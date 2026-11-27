defmodule Muro.IR.Share do
  @moduledoc """
  Share repeated pure calls in a `Muro.IR` image.

  Every run is pure and total, so a `{:call, f, args}` with the same
  arguments has the same value wherever both are in scope. Two steps:

  1. Inline. A call to a run that folds (or calls one that does), whose
     own body holds no fold, stream, or `uncons`, is replaced by that
     body under fresh names, with one `let` per parameter, when the
     expansion holds a call in the caller's names that the fully
     inlined caller makes more than once. A `let` of a variable of the
     same layout is substituted away. Arguments were already evaluated
     once at the call, and they still are, so no work moves. Every run
     is still emitted; only bodies change.
  2. Hoist. A call that every path through a term evaluates, and that
     appears there more than once, is bound once with `let` at the top
     of that term and each occurrence becomes the variable. A call that
     only some paths evaluate is never hoisted above the branch, so no
     path does work it did not do before. An arm that aborts is a path:
     it evaluates what it binds before `abort` and nothing else, so a
     call the other arms make is not hoisted above a match with such an
     arm. Arms, binder bodies, and the value a hoist binds are shared
     the same way, inside their own scope.

  Inlining is bounded twice: a callee's inlined body is at most
  `inline_max` nodes, and inlining grows the whole image by at most
  `grow_max` nodes (by default twice the size of the image, so
  inlining at most triples it). The budget counts inlining only, before
  any hoist, so it also bounds the image after hoisting up to one node
  per hoist: a hoist adds one `let` per shared call and removes every
  other occurrence. Counted before hoisting, an inlined body still holds
  every copy a hoist later removes, which is why the default is twice
  the image and not once. Runs draw on it smallest growth first, then by name, so
  which runs inline does not depend on the order of the list; a run
  whose inlining would pass what is left is shared as elaborated. A run
  that fits keeps its inlined body only when a hoist took place in it,
  or the body shrank, and its worst path does no more heavy work
  (folds, streams, and `uncons`, followed through calls) than its
  elaborated body shared without inlining; otherwise it keeps that one
  and draws nothing. Inlined bodies do not depend on that order
  either. A generated fold or stream step is never inlined into and
  draws nothing on the budget; it is still shared.

  Size decides a copy that does not change the work. The size is the
  body after the calls inside it that this pass would inline, so a thin
  wrapper of a large run counts as that run. A body of at most
  `dup_max` nodes is inlined when its expansion holds a repeated call
  in the caller's names, or known arguments shrink it below the call.
  A body bigger than `dup_max` nodes, exported or not, stays a call
  when copying it does not lower the caller's worst-path heavy work,
  and is inlined at every such site when the copy does. That work is
  each fold, stream, and `uncons` on the body this pass emits, with
  no floor: a walk of zero stays zero. An erased let makes a run
  heavy for the small-inline set, and it adds nothing to this count,
  so it cannot justify the copy. A repeated call that does not fold,
  stream, or uncons does not by itself justify it either. Runs that
  call one another are one component. Each is charged the folds of
  the whole component, the same number whichever of them is asked
  first, so the choice does not depend on the order the runs are
  listed. Copying one of them is not a saving while the copy still
  calls another. A run that only shares a fold with itself is not
  copied into its callers: the callee already hoists that fold, and
  the call costs the same as the copy. The folds are the work this
  measure can see; call overhead and the size of the body in the
  instruction cache are not. The copy is
  still bounded by `inline_max` and by `grow_max`. A comparison that
  only returns a constructor, at most `inline_small` nodes, is inlined
  at a match scrutinee when that match commutes onto the comparison.

  Known values. A match whose scrutinee is already a constructor, a
  word, or a comparison fixed by an enclosing arm keeps the arm that
  can run. The fact holds in that arm, through a binding that does not
  reuse the name or a name the fact mentions, and not in a sibling
  arm. A match on a known pair substitutes every field at once, so a
  permuted arm reads the field it names. An arm that aborts stays
  until the scrutinee rules it out. `cost: false` is the previous
  inlining. `spec: false` keeps every arm.

  The emitted program computes the same value as the checked term. A
  word operation, a constructor, and a byte literal are not shared:
  only `:call`. `Muro.IR.elaborate/2` is unchanged and still mirrors
  `agda/Muro/IR.agda`. This pass runs after it, for C, Rust and Zig. `stop/2` reads the early-exit test of a fold step for C.
  """

  @inline_max 1500
  @inline_small 48
  @dup_max 160

  @doc """
  The options of `funs/2` in `opts`, for an emitter to pass through.
  """
  def opts(opts) when is_list(opts),
    do:
      Keyword.take(opts, [
        :share,
        :inline,
        :inline_max,
        :grow_max,
        :cost,
        :spec,
        :dup_max,
        :inline_small
      ])

  @doc """
  Rewrite `funs` (the list `Muro.IR.elaborate/1` returns). Order,
  names, parameters, and layouts are kept. `opts` may set `inline: false`
  (hoisting only), `share: false` (return `funs` unchanged),
  `inline_max:` (nodes per inlined callee), `grow_max:` (nodes the
  whole image may grow by inlining, smallest growth first),
  `cost: false` (the previous inlining), `spec: false` (keep every
  match arm), `dup_max:` (nodes of the inlined body; a larger run stays
  a call unless inlining it lowers the caller's worst-path heavy work),
  or `inline_small:` (nodes; a comparison of that size may be inlined
  at a match scrutinee).
  """
  def funs(funs, opts \\ []) when is_list(funs) do
    funs = Enum.map(funs, &Muro.IR.normalize_fun/1)

    if Keyword.get(opts, :share, true) do
      inline? = Keyword.get(opts, :inline, true)
      # A generated fold or stream step is never called by name, and its
      # name (`stepN`) may also be a source run's name.
      by_name = for f <- funs, not Map.get(f, :generated, false), into: %{}, do: {f.name, f}
      {scc_of, scc_members} = components(by_name)
      counter = :counters.new(1, [])
      hoists = :counters.new(1, [])
      taken = taken_names(funs)
      heavy = heavy_set(by_name)
      known = for f <- funs, known?(f.body), do: f

      grow =
        Keyword.get_lazy(opts, :grow_max, fn ->
          2 * Enum.reduce(known, 0, &(&2 + size(&1.body)))
        end)

      budget = :counters.new(1, [])
      :counters.put(budget, 1, grow)

      ctx = %{
        hoists: hoists,
        fresh: :ets.new(:share_fresh, [:set, :private]),
        heavy: heavy,
        max: Keyword.get(opts, :inline_max, @inline_max),
        budget: budget,
        reach: reach_map(by_name),
        by_name: by_name,
        counter: counter,
        taken: taken,
        memo: :ets.new(:share, [:set, :private]),
        work: :ets.new(:share_work, [:set, :private]),
        chosen: :ets.new(:share_chosen, [:set, :private]),
        costs: :ets.new(:share_cost, [:set, :private]),
        scc_lock: :ets.new(:share_scc, [:set, :private]),
        scc_of: scc_of,
        scc_members: scc_members,
        did_save: :ets.new(:share_save, [:bag, :private]),
        gens: :counters.new(1, []),
        save_gen: 0,
        save: false,
        save_block: MapSet.new(),
        cost: Keyword.get(opts, :cost, true),
        spec: Keyword.get(opts, :spec, true),
        dup_max: Keyword.get(opts, :dup_max, @dup_max),
        small: Keyword.get(opts, :inline_small, @inline_small)
      }

      try do
        out = optimize_all(funs, ctx, inline?)

        Enum.map(Enum.with_index(funs), fn {fun, i} ->
          relax_fun(Map.get(out, i, fun))
        end)
      after
        :ets.delete(ctx.memo)
        :ets.delete(ctx.fresh)
        :ets.delete(ctx.work)
        :ets.delete(ctx.chosen)
        :ets.delete(ctx.costs)
        :ets.delete(ctx.scc_lock)
        :ets.delete(ctx.did_save)
      end
    else
      Enum.map(funs, &relax_fun/1)
    end
  end

  @doc """
  Worst-path heavy work of `t` under the non-generated runs in `funs`.

  This is the measure the keep rule uses (`work/2`): each fold,
  stream, and `uncons`, followed through calls, with the `:busy -> 1`
  cycle break and the `max(body, 1)` floor on a heavy run. Both sides
  of that comparison use the floor, including a heavy run whose walk
  has no fold, so the number stays the one the keep rule locks. A
  large copy does not use it. That count has no floor, an erased let
  adds nothing, and a mutual component is charged once.
  """
  def path_work(funs, t) when is_list(funs) do
    funs = Enum.map(funs, &Muro.IR.normalize_fun/1)
    t = Muro.IR.normalize_term(t)
    by_name = for f <- funs, not Map.get(f, :generated, false), into: %{}, do: {f.name, f}
    tab = :ets.new(:share_work, [:set, :private])

    try do
      work(t, %{by_name: by_name, heavy: heavy_set(by_name), work: tab})
    after
      :ets.delete(tab)
    end
  end

  @doc """
  The test a fold may make before each octet to stop early, or `:none`.

  `step` is a generated fold step (`fold: true`); its last parameter is
  the accumulator. A step that is, or calls a run that is,
  `match acc | c fields => match g | k => acc | ...`, with `g` reading
  only those fields, returns the accumulator unchanged on every octet
  once `g` takes the arm `k`. The rest of the fold is then the
  identity. Returns `{:ok, acc, test}`: `test` reads only `acc` and is
  `1` (a `:u64`) exactly when that arm is taken.
  """
  def stop(%{params: params, body: body}, by_name) when params != [] do
    {acc, _lay, _} = List.last(params)

    with {:ok, v, t} <- stop_target(body, acc, by_name),
         {:ok, test} <- stop_test(t, v, MapSet.new()) do
      {:ok, v, test}
    else
      _ -> :none
    end
  end

  def stop(_step, _by_name), do: :none

  defp stop_target({:call, f, args}, acc, by_name) do
    with %{params: ps, body: body} <- Map.get(by_name, f),
         i when is_integer(i) <- Enum.find_index(args, &(&1 == {:var, acc})),
         true <- length(ps) == length(args) do
      {p, _, _} = Enum.at(ps, i)
      {:ok, p, body}
    else
      _ -> :none
    end
  end

  defp stop_target(body, acc, _by_name), do: {:ok, acc, body}

  defp stop_test({:match, {:var, v}, [{:arm, c, fields, inner}]}, v, ok) do
    if v in fields do
      :none
    else
      with {:ok, test} <- stop_test(inner, v, MapSet.union(ok, MapSet.new(fields))) do
        {:ok, {:match, {:var, v}, [{:arm, c, fields, test}]}}
      end
    end
  end

  defp stop_test({:match, g, arms}, v, ok) when is_list(arms) do
    keep = Enum.find(arms, &match?({:arm, _, [], {:var, ^v}}, &1))

    if keep != nil and known?(g) and MapSet.subset?(free_vars(g), MapSet.put(ok, v)) and
         not MapSet.member?(ok, v) do
      {:arm, k, [], _} = keep

      {:ok,
       {:match, g,
        Enum.map(arms, fn {:arm, a, ns, _} ->
          {:arm, a, ns, {:wrd, :u64, {:lit, :u64, if(a == k, do: 1, else: 0)}, []}}
        end)}}
    else
      :none
    end
  end

  # A let the test does not read is skipped: its value is pure, and the
  # test cannot name it.
  defp stop_test({:let, x, _lay, _g, _val, body}, v, ok) do
    if x == v or MapSet.member?(ok, x), do: :none, else: stop_test(body, v, ok)
  end

  defp stop_test(_t, _v, _ok), do: :none

  # ---------------------------------------------------------------- driver

  # A run with nothing to share and nothing to prune keeps its
  # elaborated body. A call is inlined only when its expansion holds a
  # call, in this run's own names, that the fully inlined run evaluates
  # more than once, or a known argument makes the body smaller than the
  # call, or the call is the scrutinee of a match and the body is a
  # small comparison. A per-octet step is never inlined into and is not
  # specialised: `stop/2` reads its shape.
  # Growth is the inlined body minus the elaborated body, after
  # specialisation and before any hoist. Runs draw smallest growth
  # first, then by name. A run that fits keeps the candidate when a
  # hoist took place, or the body shrank, and its worst path does no
  # more heavy work than the elaborated body shared without inlining.
  # A body larger than `dup_max` is a candidate only when the copy
  # lowers that work against the callee after this same pass.
  defp optimize_all(funs, ctx, inline?) do
    plans =
      for {fun, i} <- Enum.with_index(funs), known?(fun.body) do
        # A generated fold or stream step is never inlined into: it runs
        # once per octet or element, so it keeps calling its run, and it
        # draws nothing on the budget. It is still shared. It is not
        # specialised, so the early-exit test keeps its shape.
        gen = Map.get(fun, :generated, false)
        inline_here? = inline? and not gen

        body =
          cond do
            inline_here? -> inline_run(fun, ctx)
            ctx.spec and not gen -> spec_only(fun, ctx)
            true -> fun.body
          end

        {i, fun, body, size(body) - size(fun.body)}
      end

    plans
    |> Enum.sort_by(fn {i, fun, body, grow} ->
      {body != fun.body, grow, fun.name, Map.get(fun, :generated, false), i}
    end)
    |> Enum.reduce(%{}, fn {i, fun, body, grow}, acc ->
      res = judge(fun, body, grow, ctx)

      case res do
        {:ok, out} -> Map.put(acc, i, %{fun | body: out})
        :skip -> acc
      end
    end)
  end

  # `body == fun.body` is the elaborated term: share it and draw
  # nothing. A candidate that grows past the budget is dropped; a
  # specialisation of the elaborated body can still replace it, and
  # that draws nothing. Otherwise keep the candidate when its worst
  # path is no heavier and either a hoist took place or the term got
  # strictly smaller or lighter.
  defp judge(fun, body, grow, ctx) do
    cond do
      body == fun.body ->
        shared(fun.body, ctx)

      grow > :counters.get(ctx.budget, 1) ->
        fallback(fun, ctx)

      true ->
        plain = shared(fun.body, ctx)
        cand = shared(body, ctx)
        pb = shared_body(plain, fun.body)
        cb = shared_body(cand, body)
        wp = work(pb, ctx)
        wc = work(cb, ctx)
        hoist? = match?({:ok, _}, cand)
        better? = wc < wp or size(cb) < size(pb)

        if wc <= wp and (hoist? or better?) do
          :counters.sub(ctx.budget, 1, max(grow, 0))
          if hoist?, do: cand, else: {:ok, cb}
        else
          plain
        end
    end
  end

  # Inlining did not fit. A specialisation that shrinks the elaborated
  # body still replaces it, and draws nothing on the budget.
  defp fallback(fun, ctx) do
    spec =
      if ctx.spec and not Map.get(fun, :generated, false),
        do: spec_only(fun, ctx),
        else: fun.body

    if spec == fun.body or size(spec) >= size(fun.body) do
      shared(fun.body, ctx)
    else
      plain = shared(fun.body, ctx)
      cand = shared(spec, ctx)
      pb = shared_body(plain, fun.body)
      cb = shared_body(cand, spec)

      if work(cb, ctx) <= work(pb, ctx) do
        if match?({:ok, _}, cand), do: cand, else: {:ok, cb}
      else
        plain
      end
    end
  end

  # `:skip` means the hoist left the term as it was given. The caller
  # passes that term, so a specialisation that shares nothing is kept.
  defp shared_body({:ok, out}, _input), do: out
  defp shared_body(:skip, input), do: input

  # Heavy work on the worst path through `t`: each fold, stream, or
  # `uncons` it evaluates, and each call of a run, counted through that
  # run's elaborated body. A match takes its scrutinee and its costliest
  # arm. A variable costs nothing, so a shared call is counted once.
  defp work({:call, name, args}, ctx) do
    own =
      case Map.get(ctx.by_name, name) do
        %{body: b} -> if MapSet.member?(ctx.heavy, name), do: run_work(name, b, ctx), else: 0
        nil -> 0
      end

    own + Enum.reduce(args, 0, &(&2 + work(&1, ctx)))
  end

  defp work({:match, s, arms}, ctx) do
    worst = arms |> Enum.map(fn {:arm, _, _, tm} -> work(tm, ctx) end) |> Enum.max(fn -> 0 end)
    work(s, ctx) + worst
  end

  defp work(t, ctx) do
    own =
      case t do
        {:bfold, _, _, _, _} -> 1
        {:stream, _, _, _} -> 1
        {:uncons, _} -> 1
        _ -> 0
      end

    own + Enum.reduce(children(t), 0, &(&2 + work(&1, ctx)))
  end

  # The keep rule's cycle break and floor. Both sides of that comparison
  # use this table. A heavy run whose walk has no fold is one, so
  # `path_work/2` stays the number the keep rule locks. A large copy
  # does not read this table: `chosen_cost/2` is zero when the only
  # weight would have been this floor or an erased let.
  # This undercounts mutually recursive SCCs: it is a finite heuristic,
  # not a bound on recursive runtime.
  defp run_work(name, body, ctx) do
    case :ets.lookup(ctx.work, name) do
      [{_, :busy}] ->
        1

      [{_, n}] ->
        n

      [] ->
        :ets.insert(ctx.work, {name, :busy})
        n = if known?(body), do: max(work(body, ctx), 1), else: 1
        :ets.insert(ctx.work, {name, n})
        n
    end
  end

  # `work/2` charged at the body this pass emits for the callee, without
  # the keep rule's floor. A body that does not fold, stream, or uncons
  # costs nothing here, erased let included.
  defp work_at({:call, name, args}, ctx) do
    own =
      case Map.get(ctx.by_name, name) do
        %{} -> if MapSet.member?(ctx.heavy, name), do: chosen_cost(name, ctx), else: 0
        nil -> 0
      end

    own + Enum.reduce(args, 0, &(&2 + work_at(&1, ctx)))
  end

  defp work_at({:match, s, arms}, ctx) do
    worst =
      arms |> Enum.map(fn {:arm, _, _, tm} -> work_at(tm, ctx) end) |> Enum.max(fn -> 0 end)

    work_at(s, ctx) + worst
  end

  defp work_at(t, ctx) do
    own =
      case t do
        {:bfold, _, _, _, _} -> 1
        {:stream, _, _, _} -> 1
        {:uncons, _} -> 1
        _ -> 0
      end

    own + Enum.reduce(children(t), 0, &(&2 + work_at(&1, ctx)))
  end

  # Folds, streams, and `uncons` on the body this pass emits. No floor:
  # a walk of zero stays zero, so an erased let cannot buy a large copy.
  # A self-call while that body is being measured is zero, which cuts
  # the cycle without charging a fold that is not there. Runs that call
  # one another are measured once, with those calls at zero, and every
  # member stores that same total.
  defp chosen_cost(name, ctx) do
    case :ets.lookup(ctx.costs, name) do
      [{_, n}] when is_integer(n) ->
        n

      [{_, :busy}] ->
        0

      [{_, :open}] ->
        0

      [] ->
        members = component_members(name, ctx)

        if length(members) > 1 do
          resolve_component(members, ctx)

          case :ets.lookup(ctx.costs, name) do
            [{_, n}] when is_integer(n) -> n
            _ -> 0
          end
        else
          case :ets.lookup(ctx.chosen, name) do
            [{_, :busy}] -> 0
            _ -> trivial_cost(name, ctx)
          end
        end
    end
  end

  defp trivial_cost(name, ctx) do
    :ets.insert(ctx.costs, {name, :busy})

    n =
      case Map.get(ctx.by_name, name) do
        %{body: b} = fun ->
          shared = share(inline_run(fun, ctx), ctx)
          if known?(b), do: work_at(shared, ctx), else: 0

        nil ->
          0
      end

    :ets.insert(ctx.costs, {name, n})
    n
  end

  defp component_members(name, ctx) do
    case Map.get(ctx.scc_of, name) do
      nil -> []
      id -> Map.fetch!(ctx.scc_members, id)
    end
  end

  # Ask every member, in name order, before any of them is on the
  # `chosen` stack. Cross-calls stay `:open` and cost nothing, so the
  # total is the folds of the component and does not follow visit order.
  defp resolve_component(members, ctx) do
    id = Map.fetch!(ctx.scc_of, hd(members))

    if :ets.insert_new(ctx.scc_lock, {id}) do
      try do
        Enum.each(members, &:ets.insert(ctx.costs, {&1, :open}))
        Enum.each(members, &inline_run(Map.fetch!(ctx.by_name, &1), ctx))

        sum =
          Enum.reduce(members, 0, fn name, acc ->
            fun = Map.fetch!(ctx.by_name, name)
            acc + work_at(share(inline_run(fun, ctx), ctx), ctx)
          end)

        Enum.each(members, &:ets.insert(ctx.costs, {&1, sum}))
      after
        :ets.delete(ctx.scc_lock, id)
      end
    end
  end

  defp ensure_component(%{name: name}, ctx) do
    members = component_members(name, ctx)

    if length(members) > 1 and not component_resolved?(members, ctx) do
      resolve_component(members, ctx)
    end
  end

  defp component_resolved?(members, ctx) do
    Enum.all?(members, fn name ->
      case :ets.lookup(ctx.costs, name) do
        [{_, n}] when is_integer(n) -> true
        _ -> false
      end
    end)
  end

  defp shared(body, ctx) do
    before = :counters.get(ctx.hoists, 1)
    out = share(body, ctx)
    if :counters.get(ctx.hoists, 1) > before, do: {:ok, out}, else: :skip
  end

  defp inline_run(fun, ctx) do
    case :ets.lookup(ctx.chosen, fun.name) do
      [{_, :busy}] ->
        fun.body

      [{_, body}] ->
        body

      [] ->
        # Before `:busy`, so a mutual component is not measured from
        # inside one member's walk. That walk would price the others
        # at the cycle cut and the total would follow the list order.
        ensure_component(fun, ctx)

        case :ets.lookup(ctx.chosen, fun.name) do
          [{_, :busy}] ->
            fun.body

          [{_, body}] ->
            body

          [] ->
            :ets.insert(ctx.chosen, {fun.name, :busy})
            body = inline_run1(fun, ctx)
            :ets.insert(ctx.chosen, {fun.name, body})
            body
        end
    end
  end

  defp inline_run1(fun, ctx) do
    scope = stable_names(fun)
    lays = Muro.IR.param_lays(fun.params)
    full = propagate(inlined_body(fun, ctx, MapSet.new()), lays, ctx)
    wanted = repeated_keys(full, scope, ctx)
    want = %{scope: scope, wanted: wanted, sites: site_counts(fun.body)}

    if ctx.cost do
      choose_inline(fun, lays, want, ctx)
    else
      body =
        if MapSet.size(wanted) == 0,
          do: fun.body,
          else: selective(fun.body, lays, want, ctx, MapSet.new([fun.name]))

      if ctx.spec, do: spec_only_tm(body, lays, ctx), else: body
    end
  end

  # A callee above `dup_max` is copied only when that copy lowers the
  # worst-path count of folds, streams, and `uncons`. The call is
  # charged after the callee's own pass, with no floor, so a fold the
  # callee already hoists is not a saving and neither is an erased let.
  # Small callees take one pass.
  defp choose_inline(fun, lays, want, ctx) do
    if may_save?(fun.body, ctx, MapSet.new([fun.name])) do
      choose_save(fun, lays, want, ctx)
    else
      {body, _} = run_pass(fun, lays, want, %{ctx | save: false, save_block: MapSet.new()})
      body
    end
  end

  defp choose_save(fun, lays, want, ctx) do
    off = %{ctx | save: false, save_block: MapSet.new()}
    {capped, _} = run_pass(fun, lays, want, off)
    cw = emitted(capped, ctx)
    {saved, gen} = run_pass(fun, lays, want, %{ctx | save: true, save_block: MapSet.new()})
    names = save_names(ctx, gen)
    sw = if names == [], do: cw, else: emitted(saved, ctx)

    if names != [] and sw < cw do
      tighten(fun, lays, want, ctx, names, saved, sw, cw, capped)
    else
      capped
    end
  end

  # Drop a large copy that the joint inline does not need. Refusing it
  # must not raise the worst path, and on a tie it must not grow the
  # body. Names are sorted so the choice does not follow book order.
  # The capped pass has already filled the cost table, so a trial does
  # not choose a callee's body again.
  defp tighten(fun, lays, want, ctx, names, saved, sw, cw, capped) do
    {block, _bw, _} =
      Enum.reduce(Enum.sort(names), {MapSet.new(), sw, size(saved)}, fn name, {block, bw, bs} ->
        trial_block = MapSet.put(block, name)

        {trial, _} =
          run_pass(fun, lays, want, %{ctx | save: true, save_block: trial_block})

        tw = emitted(trial, ctx)
        ts = size(trial)

        if tw < bw or (tw == bw and ts <= bs) do
          {trial_block, tw, ts}
        else
          {block, bw, bs}
        end
      end)

    cond do
      MapSet.size(block) == 0 ->
        saved

      true ->
        {body, _} = run_pass(fun, lays, want, %{ctx | save: true, save_block: block})
        if emitted(body, ctx) < cw, do: body, else: capped
    end
  end

  defp run_pass(fun, lays, want, ctx) do
    gen = next_gen(ctx)

    body =
      pass(
        fun.body,
        lays,
        %{},
        want,
        %{ctx | save_gen: gen},
        MapSet.new([fun.name]),
        true
      )

    {body, gen}
  end

  defp next_gen(ctx) do
    :counters.add(ctx.gens, 1, 1)
    :counters.get(ctx.gens, 1)
  end

  defp save_names(ctx, gen) do
    ctx.did_save
    |> :ets.lookup(gen)
    |> Enum.map(fn {_gen, name} -> name end)
    |> Enum.uniq()
  end

  defp may_save?(t, ctx, seen) do
    case t do
      {:call, name, args} ->
        large_callee?(name, ctx, seen) or Enum.any?(args, &may_save?(&1, ctx, seen))

      other ->
        Enum.any?(children(other), &may_save?(&1, ctx, seen))
    end
  end

  defp large_callee?(name, ctx, seen) do
    case Map.get(ctx.by_name, name) do
      %{} = callee ->
        not MapSet.member?(seen, name) and expanded_size(callee, ctx, seen) > ctx.dup_max

      _ ->
        false
    end
  end

  # Worst-path heavy work of the term this pass will emit. A call costs
  # the callee's body after the callee's own inlines and hoist, not the
  # elaborated body: that one still holds the folds the callee shares
  # with itself.
  defp emitted(t, ctx) do
    t
    |> share(ctx)
    |> work_at(ctx)
  end

  defp spec_only(fun, ctx) do
    spec_only_tm(fun.body, Muro.IR.param_lays(fun.params), ctx)
  end

  defp spec_only_tm(body, lays, ctx) do
    want = %{scope: MapSet.new(), wanted: MapSet.new(), sites: %{}}
    pass(body, lays, %{}, want, ctx, MapSet.new(), false)
  end

  # The caller's names whose meaning is one binding: a parameter no
  # binder of the body reuses, or a binder the body binds exactly once
  # and that is no parameter. A call over these names has one value
  # wherever it appears, so counting it twice means it is repeated.
  defp stable_names(fun) do
    counts = binder_counts(fun.body, %{})
    params = MapSet.new(fun.params, &elem(&1, 0))

    ps = for p <- params, not Map.has_key?(counts, p), into: MapSet.new(), do: p
    bs = for {b, 1} <- counts, not MapSet.member?(params, b), into: MapSet.new(), do: b
    MapSet.union(ps, bs)
  end

  defp binder_counts(t, acc) do
    own =
      case t do
        {:let, x, _, _, _, _} -> [x]
        {:letp, a, b, _, _} -> [a, b]
        {:match, _, arms} -> Enum.flat_map(arms, fn {:arm, _, ns, _} -> ns end)
        _ -> []
      end

    acc = Enum.reduce(own, acc, fn x, a -> Map.update(a, x, 1, &(&1 + 1)) end)
    Enum.reduce(children(t), acc, &binder_counts/2)
  end

  # Calls to a folding run, in `scope` names, that `t` makes twice or more.
  defp repeated_keys(t, scope, ctx) do
    t
    |> heavy_keys(scope, ctx, %{})
    |> Enum.filter(fn {_k, n} -> n >= 2 end)
    |> MapSet.new(fn {k, _} -> k end)
  end

  # `scope` is `stable_names/1` of the caller: each name in it has one
  # binding in the caller, and an inlined body binds only fresh names,
  # so equal keys over it have one value.
  defp heavy_keys({:call, name, args} = t, scope, ctx, acc) do
    acc =
      if MapSet.member?(ctx.heavy, name) and MapSet.subset?(free_vars(t), scope),
        do: Map.update(acc, t, 1, &(&1 + 1)),
        else: acc

    Enum.reduce(args, acc, &heavy_keys(&1, scope, ctx, &2))
  end

  defp heavy_keys(t, scope, ctx, acc),
    do: Enum.reduce(children(t), acc, &heavy_keys(&1, scope, ctx, &2))

  defp selective({:call, name, args}, lays, want, ctx, seen) do
    args = Enum.map(args, &selective(&1, lays, want, ctx, seen))

    with {:ok, callee, _full} <- inline_target(name, args, ctx, seen),
         full = propagate(expand(callee, inlined_body(callee, ctx, seen), args, ctx), lays, ctx),
         false <-
           MapSet.disjoint?(
             MapSet.new(Map.keys(heavy_keys(full, want.scope, ctx, %{}))),
             want.wanted
           ) do
      callee
      |> expand(callee.body, args, ctx)
      |> propagate(lays, ctx)
      |> selective(lays, want, ctx, MapSet.put(seen, name))
    else
      _ -> {:call, name, args}
    end
  end

  defp selective({:let, x, lay, g, v, b}, lays, want, ctx, seen),
    do:
      {:let, x, lay, g, selective(v, lays, want, ctx, seen),
       selective(b, Map.put(lays, x, lay), want, ctx, seen)}

  defp selective({:letp, a, b, e, body}, lays, want, ctx, seen),
    do:
      {:letp, a, b, selective(e, lays, want, ctx, seen),
       selective(body, lays |> Map.delete(a) |> Map.delete(b), want, ctx, seen)}

  defp selective({:match, scrut, arms}, lays, want, ctx, seen) do
    {:match, selective(scrut, lays, want, ctx, seen),
     Enum.map(arms, fn {:arm, c, names, tm} ->
       {:arm, c, names, selective(tm, Map.drop(lays, names), want, ctx, seen)}
     end)}
  end

  defp selective(t, lays, want, ctx, seen),
    do: map_children(t, &selective(&1, lays, want, ctx, seen))

  # The body of `fun` with every inlinable call inside it inlined.
  # The result depends on which runs `seen` already holds, since those
  # stay calls, so the memo is keyed by the part of `seen` that `fun`
  # can reach.
  defp inlined_body(fun, ctx, seen) do
    if MapSet.member?(seen, fun.name) do
      fun.body
    else
      key = memo_key(fun, seen, ctx)

      case :ets.lookup(ctx.memo, key) do
        [{_, body}] ->
          body

        [] ->
          body = inline(fun.body, ctx, MapSet.put(seen, fun.name))
          :ets.insert(ctx.memo, {key, body})
          body
      end
    end
  end

  defp memo_key(fun, seen, ctx) do
    generated = Map.get(fun, :generated, false)
    reach = if generated, do: MapSet.new(), else: Map.get(ctx.reach, fun.name, MapSet.new())
    {generated, fun.name, MapSet.intersection(seen, reach)}
  end

  # Runs each source run calls, directly or not.
  defp reach_map(by_name) do
    calls =
      Map.new(by_name, fn {n, f} ->
        {n, if(known?(f.body), do: called(f.body), else: MapSet.new())}
      end)

    Map.new(calls, fn {n, _} -> {n, close(calls, Map.get(calls, n), MapSet.new())} end)
  end

  defp close(calls, todo, acc) do
    new = MapSet.difference(todo, acc)

    if MapSet.size(new) == 0 do
      acc
    else
      acc = MapSet.union(acc, new)
      next = Enum.reduce(new, MapSet.new(), &MapSet.union(&2, Map.get(calls, &1, MapSet.new())))
      close(calls, next, acc)
    end
  end

  # ---------------------------------------------------------------- inline

  defp inline({:call, name, args}, ctx, seen) do
    args = Enum.map(args, &inline(&1, ctx, seen))

    case inline_target(name, args, ctx, seen) do
      {:ok, callee, body} -> expand(callee, body, args, ctx)
      :no -> {:call, name, args}
    end
  end

  defp inline(t, ctx, seen), do: map_children(t, &inline(&1, ctx, seen))

  # A call worth inlining: a folding run, an argument that is not
  # closed, plain layouts, and a fully inlined body without a fold of
  # its own and at most `inline_max` nodes.
  defp inline_target(name, args, ctx, seen) do
    with %{} = callee <- Map.get(ctx.by_name, name),
         true <- MapSet.member?(ctx.heavy, name),
         true <- Enum.any?(args, &(MapSet.size(free_vars(&1)) > 0)),
         true <- inlinable_sig?(callee, args),
         false <- MapSet.member?(seen, name),
         true <- known?(callee.body),
         body = inlined_body(callee, ctx, seen),
         true <- known?(body) and inlinable_body?(body) and size(body) <= ctx.max do
      {:ok, callee, body}
    else
      _ -> :no
    end
  end

  # `body` under fresh names, one let per parameter.
  defp expand(callee, body, args, ctx) do
    {renamed, map} = rename(body, callee.params, ctx)

    Enum.zip(callee.params, args)
    |> Enum.reverse()
    |> Enum.reduce(renamed, fn {{p, lay, g}, arg}, acc ->
      {:let, Map.fetch!(map, {:param, p}), lay, g, arg, acc}
    end)
  end

  # Runs that fold, stream, or call one that does. Only these are
  # inlined: a call to anything else has nothing worth sharing inside.
  defp heavy_set(by_name) do
    direct =
      for {n, f} <- by_name,
          known?(f.body),
          not inlinable_body?(f.body),
          into: MapSet.new(),
          do: n

    calls =
      Map.new(by_name, fn {n, f} ->
        {n, if(known?(f.body), do: called(f.body), else: MapSet.new())}
      end)

    grow_heavy(direct, calls)
  end

  defp grow_heavy(set, calls) do
    more =
      for {n, cs} <- calls,
          not MapSet.member?(set, n),
          not MapSet.disjoint?(cs, set),
          into: set,
          do: n

    if MapSet.size(more) == MapSet.size(set), do: set, else: grow_heavy(more, calls)
  end

  defp called({:call, n, args}),
    do: Enum.reduce(args, MapSet.new([n]), &MapSet.union(&2, called(&1)))

  defp called(t), do: Enum.reduce(children(t), MapSet.new(), &MapSet.union(&2, called(&1)))

  # Strongly connected components of the call graph, Kosaraju. A
  # self-call is a component of one. Members are sorted, so a later
  # walk of the component does not follow the list the book used.
  # The finish list is built by an explicit stack: a protocol book
  # can chain more calls than the process stack would hold.
  defp components(by_name) do
    names = MapSet.new(Map.keys(by_name))

    graph =
      Map.new(by_name, fn {n, f} ->
        callees = if known?(f.body), do: called(f.body), else: MapSet.new()
        {n, MapSet.intersection(callees, names)}
      end)

    graph
    |> Map.keys()
    |> Enum.sort()
    |> finish_order(graph)
    |> assign_components(transpose(graph))
  end

  defp finish_order(nodes, graph) do
    nodes
    |> Enum.map(&{:enter, &1})
    |> dfs_finish(graph, [], MapSet.new())
  end

  defp dfs_finish([], _graph, order, _seen), do: order

  defp dfs_finish([{:exit, n} | rest], graph, order, seen),
    do: dfs_finish(rest, graph, [n | order], seen)

  defp dfs_finish([{:enter, n} | rest], graph, order, seen) do
    if MapSet.member?(seen, n) do
      dfs_finish(rest, graph, order, seen)
    else
      kids =
        graph
        |> Map.get(n, MapSet.new())
        |> Enum.sort()
        |> Enum.map(&{:enter, &1})

      dfs_finish(kids ++ [{:exit, n} | rest], graph, order, MapSet.put(seen, n))
    end
  end

  defp transpose(graph) do
    Enum.reduce(graph, %{}, fn {n, ms}, acc ->
      acc = Map.put_new(acc, n, MapSet.new())

      Enum.reduce(ms, acc, fn m, acc ->
        Map.update(acc, m, MapSet.new([n]), &MapSet.put(&1, n))
      end)
    end)
  end

  # `order` starts with the last finished node, which is the order the
  # second pass wants. Do not reverse it.
  defp assign_components(order, rev) do
    {sof, mem, _, _} =
      Enum.reduce(order, {%{}, %{}, MapSet.new(), 0}, fn n, {sof, mem, seen, id} ->
        if MapSet.member?(seen, n) do
          {sof, mem, seen, id}
        else
          {comp, seen} = collect_component([{:enter, n}], rev, [], seen)
          comp = Enum.sort(comp)
          sof = Enum.reduce(comp, sof, &Map.put(&2, &1, id))
          {sof, Map.put(mem, id, comp), seen, id + 1}
        end
      end)

    {sof, mem}
  end

  defp collect_component([], _rev, comp, seen), do: {comp, seen}

  defp collect_component([{:exit, n} | rest], rev, comp, seen),
    do: collect_component(rest, rev, [n | comp], seen)

  defp collect_component([{:enter, n} | rest], rev, comp, seen) do
    if MapSet.member?(seen, n) do
      collect_component(rest, rev, comp, seen)
    else
      kids =
        rev
        |> Map.get(n, MapSet.new())
        |> Enum.sort()
        |> Enum.map(&{:enter, &1})

      collect_component(kids ++ [{:exit, n} | rest], rev, comp, MapSet.put(seen, n))
    end
  end

  defp inlinable_sig?(callee, args) do
    not Map.get(callee, :generated, false) and length(callee.params) == length(args) and
      Enum.all?([callee.ret | Enum.map(callee.params, &elem(&1, 1))], &plain_lay?/1)
  end

  # A layout the emitters bind and return without a conversion.
  defp plain_lay?(:opaque), do: false
  defp plain_lay?(:erased), do: false
  defp plain_lay?(:string), do: false
  defp plain_lay?({:opt, a}), do: plain_lay?(a)
  defp plain_lay?({:pair, a, b}), do: plain_lay?(a) and plain_lay?(b)
  defp plain_lay?({:stream, _}), do: false
  defp plain_lay?({:fn, _, _}), do: false
  defp plain_lay?(_), do: true

  # An erased let keeps the run out of the small-inline set. It is not
  # a fold, and the large-copy count does not charge it.
  defp inlinable_body?(t) do
    not contains?(t, fn
      {:bfold, _, _, _, _} -> true
      {:stream, _, _, _} -> true
      {:uncons, _} -> true
      {:let, _, :erased, _, _, _} -> true
      _ -> false
    end)
  end

  # Fresh names for every binder of a callee body, parameters included.
  defp rename(body, params, ctx) do
    {map, env} =
      Enum.reduce(params, {%{}, %{}}, fn {p, _lay, _g}, {map, env} ->
        f = fresh(p, ctx)
        {Map.put(map, {:param, p}, f), Map.put(env, p, f)}
      end)

    {rename_tm(body, env, ctx), map}
  end

  defp rename_tm({:var, x}, env, _ctx), do: {:var, Map.get(env, x, x)}

  defp rename_tm({:let, x, lay, g, v, b}, env, ctx) do
    f = fresh(x, ctx)
    {:let, f, lay, g, rename_tm(v, env, ctx), rename_tm(b, Map.put(env, x, f), ctx)}
  end

  defp rename_tm({:letp, a, b, e, body}, env, ctx) do
    fa = fresh(a, ctx)
    fb = fresh(b, ctx)
    env1 = env |> Map.put(a, fa) |> Map.put(b, fb)
    {:letp, fa, fb, rename_tm(e, env, ctx), rename_tm(body, env1, ctx)}
  end

  defp rename_tm({:match, scrut, arms}, env, ctx) do
    arms =
      Enum.map(arms, fn {:arm, c, names, tm} ->
        fs = Enum.map(names, &fresh(&1, ctx))
        env1 = Enum.zip(names, fs) |> Enum.reduce(env, fn {n, f}, e -> Map.put(e, n, f) end)
        {:arm, c, fs, rename_tm(tm, env1, ctx)}
      end)

    {:match, rename_tm(scrut, env, ctx), arms}
  end

  defp rename_tm({:match, scrut, lay, arms}, env, ctx)
       when is_list(arms) and not is_list(lay) do
    arms =
      Enum.map(arms, fn {:arm, c, names, tm} ->
        fs = Enum.map(names, &fresh(&1, ctx))
        env1 = Enum.zip(names, fs) |> Enum.reduce(env, fn {n, f}, e -> Map.put(e, n, f) end)
        {:arm, c, fs, rename_tm(tm, env1, ctx)}
      end)

    {:match, rename_tm(scrut, env, ctx), lay, arms}
  end

  defp rename_tm({:lam, name, lay, g, body}, env, ctx) when is_binary(name) do
    f = fresh(name, ctx)
    {:lam, f, lay, g, rename_tm(body, Map.put(env, name, f), ctx)}
  end

  defp rename_tm(t, env, ctx), do: map_children(t, &rename_tm(&1, env, ctx))

  defp fresh(base, ctx) do
    :counters.add(ctx.counter, 1, 1)
    n = :counters.get(ctx.counter, 1)
    name = "#{base}_s#{n}"

    if MapSet.member?(ctx.taken, name) do
      fresh(base, ctx)
    else
      :ets.insert(ctx.fresh, {name})
      name
    end
  end

  # ------------------------------------------------------- copy propagation

  # `let x = y`, x a parameter an inlined body was given and y of the
  # same layout: use y. x is fresh, so nothing captures y. A let the
  # source wrote stays.
  defp propagate({:let, x, lay, g, {:var, y}, b}, lays, ctx) do
    if :ets.member(ctx.fresh, x) and lay != :erased and Map.get(lays, y) == lay and
         not rebinds?(b, y) do
      propagate(subst_var(b, x, y), lays, ctx)
    else
      {:let, x, lay, g, {:var, y}, propagate(b, Map.put(lays, x, lay), ctx)}
    end
  end

  defp propagate({:let, x, lay, g, v, b}, lays, ctx),
    do: {:let, x, lay, g, propagate(v, lays, ctx), propagate(b, Map.put(lays, x, lay), ctx)}

  defp propagate({:letp, a, b, e, body}, lays, ctx),
    do:
      {:letp, a, b, propagate(e, lays, ctx),
       propagate(body, lays |> Map.delete(a) |> Map.delete(b), ctx)}

  defp propagate({:match, scrut, arms}, lays, ctx) do
    {:match, propagate(scrut, lays, ctx),
     Enum.map(arms, fn {:arm, c, names, tm} ->
       {:arm, c, names, propagate(tm, Map.drop(lays, names), ctx)}
     end)}
  end

  defp propagate(t, lays, ctx), do: map_children(t, &propagate(&1, lays, ctx))

  defp rebinds?(t, y), do: MapSet.member?(binders(t), y)

  defp subst_var({:var, x}, x, y), do: {:var, y}

  defp subst_var({:let, z, lay, g, v, b}, x, y) do
    v = subst_var(v, x, y)
    if z == x, do: {:let, z, lay, g, v, b}, else: {:let, z, lay, g, v, subst_var(b, x, y)}
  end

  defp subst_var({:letp, a, b, e, body}, x, y) do
    e = subst_var(e, x, y)
    if x in [a, b], do: {:letp, a, b, e, body}, else: {:letp, a, b, e, subst_var(body, x, y)}
  end

  defp subst_var({:match, scrut, arms}, x, y) do
    {:match, subst_var(scrut, x, y),
     Enum.map(arms, fn {:arm, c, names, tm} = arm ->
       if x in names, do: arm, else: {:arm, c, names, subst_var(tm, x, y)}
     end)}
  end

  defp subst_var(t, x, y), do: map_children(t, &subst_var(&1, x, y))

  # ------------------------------------------------- cost and specialise

  # One left-to-right walk. `inl` is false when only specialisation
  # runs. A small comparison is inlined at a match scrutinee by
  # `commute_scrut/8`, which asks `scrut_small?/4` itself.
  defp pass(t, lays, facts, want, ctx, seen, inl) do
    case t do
      {:call, name, args} ->
        pass_call(name, args, lays, facts, want, ctx, seen, inl)

      {:let, x, lay, g, v, b} ->
        pass_let(x, lay, g, v, b, lays, facts, want, ctx, seen, inl)

      {:letp, a, b, e, body} ->
        pass_letp(a, b, e, body, lays, facts, want, ctx, seen, inl)

      {:match, scrut, arms} ->
        pass_match(scrut, arms, lays, facts, want, ctx, seen, inl)

      _ ->
        pass_node(t, lays, facts, want, ctx, seen, inl)
    end
  end

  defp pass_call(name, args, lays, facts, want, ctx, seen, inl) do
    args = pass_list(args, lays, facts, want, ctx, seen, inl)
    call = {:call, name, args}

    if not inl do
      call
    else
      case decide(name, args, lays, facts, want, ctx, seen) do
        :no -> call
        mode -> splice(mode, name, args, lays, facts, want, ctx, seen)
      end
    end
  end

  defp decide(name, args, lays, facts, want, ctx, seen) do
    callee = Map.get(ctx.by_name, name)

    cond do
      heavy_here?(name, args, lays, want, ctx, seen) -> :heavy
      shrink_here?(callee, args, facts, ctx, seen) -> :shrink
      save_here?(name, args, lays, want, ctx, seen) -> :save
      true -> :no
    end
  end

  # A match scrutinee whose body is itself a small match. The outer
  # match inlines it only when that match commutes onto the comparison,
  # and leaves the call when it does not. The caller is `scrut_expand/7`,
  # which only runs for a scrutinee.
  defp scrut_small?(nil, _args, _ctx, _seen), do: false

  defp scrut_small?(callee, args, ctx, seen) do
    ctx.spec and size(callee.body) <= ctx.small and match_body?(callee.body) and
      light?(callee, args, ctx, seen)
  end

  # The copy is the inlined body, not the source body. A wrapper whose
  # source is one call still counts as the run it pulls in.
  defp heavy_here?(name, args, lays, want, ctx, seen) do
    case Map.get(ctx.by_name, name) do
      %{} = callee ->
        expanded_size(callee, ctx, seen) <= ctx.dup_max and
          wanted_hit?(name, args, lays, want, ctx, seen)

      _ ->
        false
    end
  end

  defp shrink_here?(nil, _args, _facts, _ctx, _seen), do: false

  defp shrink_here?(callee, args, facts, ctx, seen) do
    ctx.spec and expanded_size(callee, ctx, seen) <= ctx.dup_max and
      light?(callee, args, ctx, seen) and
      (map_size(facts) > 0 or Enum.any?(args, &known_arg?(&1, facts)))
  end

  # Above `dup_max` the copy has to pay for itself in worst-path work.
  # `choose_save/4` is what checks the saving; this only admits the splice
  # on the pass that is allowed to try it. A member of the caller's own
  # mutual component is not admitted: the copy still calls the other
  # member, and while the component is being measured those calls cost
  # nothing, which would look like a saving that is not one.
  defp save_here?(name, args, lays, want, ctx, seen) do
    ctx.save and not MapSet.member?(ctx.save_block, name) and not mutual_copy?(name, seen, ctx) and
      case Map.get(ctx.by_name, name) do
        %{} = callee ->
          expanded_size(callee, ctx, seen) > ctx.dup_max and
            wanted_hit?(name, args, lays, want, ctx, seen)

        _ ->
          false
      end
  end

  defp mutual_copy?(name, seen, ctx) do
    case Map.get(ctx.scc_of, name) do
      nil ->
        false

      id ->
        length(Map.get(ctx.scc_members, id, [])) > 1 and
          Enum.any?(seen, &(Map.get(ctx.scc_of, &1) == id))
    end
  end

  defp wanted_hit?(name, args, lays, want, ctx, seen) do
    if MapSet.size(want.wanted) == 0 do
      false
    else
      with {:ok, callee, _} <- inline_target(name, args, ctx, seen),
           full =
             propagate(expand(callee, inlined_body(callee, ctx, seen), args, ctx), lays, ctx),
           keys = MapSet.new(Map.keys(heavy_keys(full, want.scope, ctx, %{}))),
           false <- MapSet.disjoint?(keys, want.wanted) do
        true
      else
        _ -> false
      end
    end
  end

  defp light?(callee, args, ctx, seen) do
    not MapSet.member?(seen, callee.name) and inlinable_sig?(callee, args) and
      known?(callee.body) and inlinable_body?(callee.body) and size(callee.body) <= ctx.max
  end

  defp match_body?(t) do
    case peel_lets(t) do
      {:match, _, _} -> true
      _ -> false
    end
  end

  defp expanded_size(callee, ctx, seen), do: size(inlined_body(callee, ctx, seen))

  defp known_arg?({:wrd, _, {:lit, _, n}, []}, _facts) when is_integer(n), do: true
  defp known_arg?(:ze, _facts), do: true
  defp known_arg?({:su, {:var, _}}, _facts), do: true
  defp known_arg?({:con, _, _, []}, _facts), do: true
  defp known_arg?({:wrd, _, b, []}, _facts) when b in [true, false], do: true
  defp known_arg?({:var, x}, facts), do: Map.has_key?(facts, x)
  defp known_arg?(_, _), do: false

  defp splice(mode, name, args, lays, facts, want, ctx, seen) do
    callee = Map.fetch!(ctx.by_name, name)
    seen2 = MapSet.put(seen, name)
    body = propagate(expand(callee, callee.body, args, ctx), lays, ctx)
    out = pass(body, lays, facts, want, ctx, seen2, true)
    call = {:call, name, args}

    case mode do
      :shrink ->
        if size(out) < size(call), do: out, else: call

      :save ->
        :ets.insert(ctx.did_save, {ctx.save_gen, name})
        out

      :heavy ->
        out
    end
  end

  defp pass_let(x, lay, g, v, b, lays, facts, want, ctx, seen, inl) do
    v = pass(v, lays, facts, want, ctx, seen, inl)
    # The value was checked in the outer scope. `lays` stays that scope.
    facts1 = scrub(facts, [x])
    lays1 = Map.put(lays, x, lay)
    facts1 = learn_value(x, v, lay, facts1, lays)
    b = pass(b, lays1, facts1, want, ctx, seen, inl)

    cond do
      fresh_var?(x, lay, v, b, lays, ctx) ->
        {:var, y} = v
        subst_var(b, x, y)

      :ets.member(ctx.fresh, x) and pure_value?(v) and not MapSet.member?(free_vars(b), x) ->
        b

      :ets.member(ctx.fresh, x) and b == {:var, x} and pure_value?(v) ->
        v

      true ->
        {:let, x, lay, relax_grade(g, x, b), v, b}
    end
  end

  defp fresh_var?(x, lay, {:var, y}, b, lays, ctx) do
    :ets.member(ctx.fresh, x) and lay != :erased and Map.get(lays, y) == lay and
      not rebinds?(b, y)
  end

  defp fresh_var?(_, _, _, _, _, _), do: false

  defp pass_letp(a, b, e, body, lays, facts, want, ctx, seen, inl) do
    e = pass(e, lays, facts, want, ctx, seen, inl)
    lays1 = lays |> Map.delete(a) |> Map.delete(b)
    facts1 = scrub(facts, [a, b])
    body = pass(body, lays1, facts1, want, ctx, seen, inl)
    {:letp, a, b, e, body}
  end

  # Inline a small comparison only when the outer match commutes onto
  # it. A scrutinee that does not commute stays a call, so the larger
  # match is not copied in.
  defp commute_scrut(scrut, arms, lays, facts, want, ctx, seen, inl) do
    case scrut_expand(scrut, lays, facts, want, ctx, seen, inl) do
      {:ok, expanded} ->
        case fuse_match(expanded, arms, ctx) do
          {:ok, inner, as, lets} -> {:ok, inner, as, lets}
          :no -> fuse_or_no(scrut, arms, ctx)
        end

      :no ->
        fuse_or_no(scrut, arms, ctx)
    end
  end

  defp fuse_or_no(scrut, arms, ctx) do
    case fuse_match(scrut, arms, ctx) do
      {:ok, inner, as, lets} -> {:ok, inner, as, lets}
      :no -> :no
    end
  end

  defp scrut_expand({:call, name, args} = call, lays, facts, want, ctx, seen, inl) do
    callee = Map.get(ctx.by_name, name)

    if scrut_small?(callee, args, ctx, seen) do
      seen2 = MapSet.put(seen, name)
      body = propagate(expand(callee, callee.body, args, ctx), lays, ctx)
      out = pass(body, lays, facts, want, ctx, seen2, inl)
      if out != call, do: {:ok, out}, else: :no
    else
      :no
    end
  end

  defp scrut_expand(_, _, _, _, _, _, _), do: :no

  defp pass_match(scrut, arms, lays, facts, want, ctx, seen, inl) do
    scrut = pass(scrut, lays, facts, want, ctx, seen, inl)
    plain = finish_match(scrut, arms, [], lays, facts, want, ctx, seen, inl, ctx.spec)

    if ctx.spec do
      # A commute that is dropped must not consume fresh names. The
      # counter is global, so a rejected copy would rename a later binder.
      mark = :counters.get(ctx.counter, 1)

      case commute_scrut(scrut, arms, lays, facts, want, ctx, seen, inl) do
        {:ok, inner, as, lets} ->
          term = finish_match(inner, as, lets, lays, facts, want, ctx, seen, inl, true)

          # A commute that does not shrink the match is dropped. Both
          # arms of a comparison that is not yet known stay as the call.
          if size(term) < size(plain) do
            term
          else
            :counters.put(ctx.counter, 1, mark)
            plain
          end

        :no ->
          :counters.put(ctx.counter, 1, mark)
          plain
      end
    else
      plain
    end
  end

  defp finish_match(scrut, arms, lets, lays, facts, want, ctx, seen, inl, spec?) do
    term =
      if spec? do
        case reduce_match(scrut, arms, lays, facts, ctx) do
          {:done, tag, names, body} ->
            # The arm was substituted away. Its binders are not in scope,
            # so a fact learned here keeps the outer names.
            facts2 = arm_facts(scrut, tag, names, facts, lays, :reduced)
            pass(body, Map.drop(lays, names), facts2, want, ctx, seen, inl)

          :keep ->
            arms = kill_dead(scrut, arms, lays, facts)
            pass_arms(scrut, arms, lays, facts, want, ctx, seen, inl)
        end
      else
        pass_arms(scrut, arms, lays, facts, want, ctx, seen, inl)
      end

    rewrap(lets, term)
  end

  defp pass_arms(scrut, arms, lays, facts, want, ctx, seen, inl) do
    arms =
      Enum.map(arms, fn {:arm, c, names, tm} ->
        lays2 = Map.drop(lays, names)
        facts2 = arm_facts(scrut, c, names, facts, lays, :enter)
        tm = pass(tm, lays2, facts2, want, ctx, seen, inl)
        {:arm, c, names, tm}
      end)

    {:match, scrut, arms}
  end

  defp pass_list(ts, lays, facts, want, ctx, seen, inl) do
    Enum.map(ts, &pass(&1, lays, facts, want, ctx, seen, inl))
  end

  defp pass_node(t, lays, facts, want, ctx, seen, inl) do
    put_children(t, pass_list(children(t), lays, facts, want, ctx, seen, inl))
  end

  # ---- facts

  # A fact names the binders in scope when it was learned. A new binder
  # shadows every one of those names, so the fact is dropped with the
  # key. `let`, `letp`, and a match arm that is kept all do this. The
  # parameter lets an inlined run is given are ordinary lets, so they
  # do too. A fold or a stream step is a separate function and is not
  # specialised, so its binders never see these facts.
  defp scrub(facts, names) do
    drop = MapSet.new(names)

    facts
    |> Map.drop(names)
    |> Map.filter(fn {_k, fact} -> not fact_mentions?(fact, drop) end)
  end

  defp fact_mentions?({:ne_var, y}, drop), do: MapSet.member?(drop, y)
  defp fact_mentions?({:nat, :suc, p}, drop), do: MapSet.member?(drop, p)

  defp fact_mentions?({:ctor, _, fields}, drop),
    do: Enum.any?(fields, &MapSet.member?(drop, &1))

  defp fact_mentions?(_, _), do: false

  # `:enter` is an arm that stays. Its binders shadow, so facts that
  # name them go, and the scrutinee is recorded against these binders.
  # `:reduced` is an arm that was substituted away. Those names are not
  # introduced. The fact keeps the outer binders: retargeting it at the
  # eliminated ones would point it out of scope.
  defp arm_facts(scrut, tag, names, facts, lays, :enter) do
    facts = scrub(facts, names)
    learn_scrut(scrut, tag, names, facts, lays, :refresh)
  end

  defp arm_facts(scrut, tag, names, facts, lays, :reduced) do
    learn_scrut(scrut, tag, names, facts, lays, :keep)
  end

  defp learn_scrut({:var, x}, tag, names, facts, lays, mode) do
    if x in names, do: facts, else: learn_tag(x, tag, names, facts, lays, mode)
  end

  defp learn_scrut({:wrd, _, :eq, [a, b]}, tag, _names, facts, _lays, _mode) do
    cond do
      false_tag?(tag) -> learn_ne(a, b, facts)
      true_tag?(tag) -> learn_eq(a, b, facts)
      true -> facts
    end
  end

  defp learn_scrut(_, _, _, facts, _, _), do: facts

  defp learn_tag(x, "zero", _names, facts, lays, mode) do
    if Map.get(lays, x) == :nat,
      do: put_fact(facts, x, {:nat, :zero}, mode),
      else: put_ctor(facts, x, "zero", [], mode)
  end

  defp learn_tag(x, "suc", [p], facts, lays, mode) do
    if Map.get(lays, x) == :nat,
      do: put_fact(facts, x, {:nat, :suc, p}, mode),
      else: put_ctor(facts, x, "suc", [p], mode)
  end

  defp learn_tag(x, "wtrue", _, facts, lays, mode) do
    if Map.get(lays, x) == :wbool,
      do: put_fact(facts, x, {:wbool, true}, mode),
      else: put_ctor(facts, x, "wtrue", [], mode)
  end

  defp learn_tag(x, "wfalse", _, facts, lays, mode) do
    if Map.get(lays, x) == :wbool,
      do: put_fact(facts, x, {:wbool, false}, mode),
      else: put_ctor(facts, x, "wfalse", [], mode)
  end

  defp learn_tag(x, tag, names, facts, _lays, mode),
    do: put_ctor(facts, x, tag, names, mode)

  defp put_ctor(facts, x, tag, names, mode),
    do: put_fact(facts, x, {:ctor, tag, names}, mode)

  # The value is in the outer scope. A fact built from it that names
  # the new binder is about that outer name, so it does not belong to
  # the binding.
  defp learn_value(x, v, lay, facts, lays) do
    facts = learn_bound(x, v, lay, facts, lays)

    case Map.get(facts, x) do
      nil ->
        facts

      fact ->
        if fact_mentions?(fact, MapSet.new([x])), do: Map.delete(facts, x), else: facts
    end
  end

  defp learn_bound(x, {:var, y}, lay, facts, lays) do
    if Map.get(lays, y) == lay do
      case Map.get(facts, y) do
        nil -> facts
        f -> put_fact(facts, x, f)
      end
    else
      facts
    end
  end

  defp learn_bound(x, {:wrd, _, {:lit, _, n}, []}, _lay, facts, _lays) when is_integer(n),
    do: put_fact(facts, x, {:wlit, n})

  defp learn_bound(x, :ze, :nat, facts, _lays), do: put_fact(facts, x, {:nat, :zero})

  defp learn_bound(x, {:su, {:var, p}}, :nat, facts, _lays),
    do: put_fact(facts, x, {:nat, :suc, p})

  defp learn_bound(x, {:con, _, tag, args}, _lay, facts, _lays) do
    if Enum.all?(args, &match?({:var, _}, &1)) do
      put_ctor(facts, x, tag, Enum.map(args, fn {:var, v} -> v end), :keep)
    else
      facts
    end
  end

  defp learn_bound(x, {:wrd, _, b, []}, _lay, facts, _lays) when b in [true, false],
    do: put_fact(facts, x, {:wbool, b})

  defp learn_bound(_x, _v, _lay, facts, _lays), do: facts

  # `:refresh` is the arm that is kept: its binders are the fields now,
  # even when a fact for this scrutinee already named the outer ones.
  # `:keep` is everywhere else. A word literal, a constructor, and a
  # nat are not replaced by a weaker comparison.
  defp put_fact(facts, x, fact, mode \\ :keep)

  defp put_fact(facts, x, fact, :refresh), do: Map.put(facts, x, fact)

  defp put_fact(facts, x, fact, :keep) do
    case Map.get(facts, x) do
      nil -> Map.put(facts, x, fact)
      ^fact -> facts
      {:wlit, _} -> facts
      {:nat, _} -> facts
      {:nat, _, _} -> facts
      {:ctor, _, _} -> facts
      {:wbool, _} -> facts
      _ -> Map.put(facts, x, fact)
    end
  end

  defp learn_eq(a, b, facts) do
    facts
    |> eq_side(a, b)
    |> eq_side(b, a)
  end

  defp eq_side(facts, {:var, x}, {:wrd, _, {:lit, _, n}, []}) when is_integer(n),
    do: put_fact(facts, x, {:wlit, n})

  defp eq_side(facts, {:var, x}, {:var, y}) do
    case Map.get(facts, y) do
      nil -> facts
      f -> put_fact(facts, x, f)
    end
  end

  defp eq_side(facts, _, _), do: facts

  defp learn_ne(a, b, facts) do
    facts
    |> ne_side(a, b)
    |> ne_side(b, a)
  end

  defp ne_side(facts, {:var, x}, other) do
    case lit_of(other, facts) do
      {:ok, n} when is_integer(n) ->
        put_fact(facts, x, {:ne_word, n})

      _ ->
        case other do
          {:var, y} -> put_fact(facts, x, {:ne_var, y})
          _ -> facts
        end
    end
  end

  defp ne_side(facts, _, _), do: facts

  defp true_tag?(tag), do: tag in ["wtrue", "true"]
  defp false_tag?(tag), do: tag in ["wfalse", "false"]

  # ---- reduce

  # Commute `match (match s | k => ctor) | ctor => body` when every
  # inner arm is a constructor with no fields, so each outer body is
  # placed once under the arm that returns it. A let the outer bodies
  # do not name stays wrapped around the match.
  defp fuse_match(scrut, outers, ctx) do
    case peel_safe(scrut, outers) do
      {lets, {:match, inner, iarms}} ->
        if fuse_ok?(outers, iarms, ctx) do
          arms =
            Enum.map(iarms, fn {:arm, c, [], val} ->
              {:ok, tag} = ctor_tag(val)
              {:arm, _, _, body} = Enum.find(outers, &match?({:arm, ^tag, _, _}, &1))
              {:arm, c, [], body}
            end)

          {:ok, inner, arms, lets}
        else
          :no
        end

      _ ->
        :no
    end
  end

  defp fuse_ok?(outers, iarms, ctx) do
    tags =
      Enum.map(iarms, fn
        {:arm, _, [], val} -> ctor_tag(val)
        _ -> :no
      end)

    known = Enum.all?(tags, &match?({:ok, _}, &1))

    uses =
      Enum.reduce(tags, %{}, fn
        {:ok, tag}, acc -> Map.update(acc, tag, 1, &(&1 + 1))
        _, acc -> acc
      end)

    known and
      Enum.all?(tags, fn {:ok, tag} -> Enum.any?(outers, &match?({:arm, ^tag, _, _}, &1)) end) and
      Enum.all?(outers, fn {:arm, tag, _, body} ->
        Map.get(uses, tag, 0) <= 1 or size(body) <= ctx.small
      end)
  end

  defp peel_safe({:let, x, lay, g, v, b}, outers) do
    if Enum.any?(outers, fn {:arm, _, _, body} -> MapSet.member?(free_vars(body), x) end) do
      {[], {:let, x, lay, g, v, b}}
    else
      {lets, inner} = peel_safe(b, outers)
      {[{x, lay, g, v} | lets], inner}
    end
  end

  defp peel_safe(t, _outers), do: {[], t}

  defp peel_lets({:let, _, _, _, _, b}), do: peel_lets(b)
  defp peel_lets(t), do: t

  defp rewrap([], inner), do: inner
  defp rewrap([{x, lay, g, v} | lets], inner), do: {:let, x, lay, g, v, rewrap(lets, inner)}

  defp ctor_tag({:con, _, tag, []}), do: {:ok, tag}
  defp ctor_tag({:wrd, _, true, []}), do: {:ok, "wtrue"}
  defp ctor_tag({:wrd, _, false, []}), do: {:ok, "wfalse"}
  defp ctor_tag(:ze), do: {:ok, "zero"}
  defp ctor_tag(:tt), do: {:ok, "tt"}
  defp ctor_tag(_), do: :no

  # The live arm, when the scrutinee is a pure value and every field
  # the arm binds is a variable. Anything else keeps the match, so a
  # call in the scrutinee still runs.
  defp reduce_match(scrut, arms, lays, facts, ctx) do
    if pure_value?(scrut) do
      case which_arm(scrut, arms, lays, facts) do
        {:ok, {:arm, tag, names, body}, fields} ->
          case bind_fields(names, fields) do
            {:ok, substs} -> {:done, tag, names, apply_substs(body, substs, ctx)}
            :no -> :keep
          end

        :no ->
          :keep
      end
    else
      :keep
    end
  end

  defp which_arm(scrut, arms, lays, facts) do
    case which_tag(scrut, arms, lays, facts) do
      {:ok, tag, fields} ->
        case Enum.find(arms, &match?({:arm, ^tag, _, _}, &1)) do
          nil -> :no
          arm -> {:ok, arm, fields}
        end

      :no ->
        :no
    end
  end

  defp which_tag(scrut, arms, lays, facts) do
    found =
      cond do
        match?({:ok, true}, cmp_result(scrut, facts)) ->
          {:ok, pick_tag(arms, ["wtrue", "true"]), []}

        match?({:ok, false}, cmp_result(scrut, facts)) ->
          {:ok, pick_tag(arms, ["wfalse", "false"]), []}

        true ->
          value_tag(scrut, lays, facts)
      end

    case normalize_tag(found) do
      # `zero` / `suc` are also ordinary constructors. A nat arm is
      # taken only from a nat fact or from `ze` / `su` themselves.
      {:ok, tag, _} = ok ->
        if tag in ["zero", "suc"] and nat_arms?(arms) and not nat_scrut?(scrut, lays, facts),
          do: :no,
          else: ok

      :no ->
        :no
    end
  end

  defp nat_arms?(arms) do
    Enum.map(arms, fn {:arm, c, _, _} -> c end) |> Enum.sort() == ["suc", "zero"]
  end

  defp nat_scrut?(:ze, _, _), do: true
  defp nat_scrut?({:su, _}, _, _), do: true

  defp nat_scrut?({:var, x}, lays, facts),
    do: Map.get(lays, x) == :nat or nat_fact?(Map.get(facts, x))

  defp nat_scrut?(_, _, _), do: false

  # `{:nat, :suc, p}` is the fact `learn_eq` copies onto a word when the
  # other side is a successor. `{:nat, _}` is the zero fact and a nat
  # literal. A data constructor named suc is not either of these.
  defp nat_fact?({:nat, :suc, p}) when is_binary(p), do: true
  defp nat_fact?({:nat, _}), do: true
  defp nat_fact?(_), do: false

  defp normalize_tag({:ok, :no, _}), do: :no
  defp normalize_tag({:ok, tag, fields}) when is_binary(tag), do: {:ok, tag, fields}
  defp normalize_tag(:no), do: :no

  defp pick_tag(arms, prefs) do
    Enum.find(prefs, :no, fn t -> Enum.any?(arms, &match?({:arm, ^t, _, _}, &1)) end)
  end

  defp value_tag(:ze, _lays, _facts), do: {:ok, "zero", []}
  defp value_tag({:su, {:var, p}}, _lays, _facts), do: {:ok, "suc", [{:var, p}]}
  defp value_tag({:wrd, _, true, []}, _lays, _facts), do: {:ok, "wtrue", []}
  defp value_tag({:wrd, _, false, []}, _lays, _facts), do: {:ok, "wfalse", []}
  defp value_tag({:con, _, tag, args}, _lays, _facts), do: {:ok, tag, args}

  defp value_tag({:var, x}, lays, facts) do
    case Map.get(facts, x) do
      {:nat, :zero} -> {:ok, "zero", []}
      {:nat, :suc, p} when is_binary(p) -> {:ok, "suc", [{:var, p}]}
      {:wbool, true} -> {:ok, "wtrue", []}
      {:wbool, false} -> {:ok, "wfalse", []}
      {:wlit, 0} -> if(Map.get(lays, x) == :nat, do: {:ok, "zero", []}, else: :no)
      {:ctor, tag, fields} -> {:ok, tag, Enum.map(fields, &{:var, &1})}
      _ -> :no
    end
  end

  defp value_tag(_, _, _), do: :no

  defp bind_fields(names, fields) when length(names) == length(fields) do
    if Enum.all?(fields, &match?({:var, _}, &1)) do
      {:ok, Enum.zip(names, Enum.map(fields, fn {:var, v} -> v end))}
    else
      :no
    end
  end

  defp bind_fields(_, _), do: :no

  # Every field at once. A sequential walk of `pair y x => y` with
  # `y` bound to `x` and `x` bound to `y` would read `y` back.
  # A binder that is itself a target is renamed first, so
  # `let x = z in y` does not capture the `x` just substituted for `y`.
  defp apply_substs(body, substs, ctx) do
    subst_sim(body, Map.new(substs), ctx)
  end

  defp subst_sim(tm, map, _ctx) when map_size(map) == 0, do: tm

  defp subst_sim({:var, x}, map, _ctx) do
    case Map.get(map, x) do
      nil -> {:var, x}
      y -> {:var, y}
    end
  end

  defp subst_sim({:let, x, lay, g, v, b}, map, ctx) do
    v = subst_sim(v, map, ctx)
    map = Map.delete(map, x)
    {x, b, map} = avoid_capture(x, b, map, ctx)
    {:let, x, lay, g, v, subst_sim(b, map, ctx)}
  end

  defp subst_sim({:letp, a, b, e, body}, map, ctx) do
    e = subst_sim(e, map, ctx)
    map = map |> Map.delete(a) |> Map.delete(b)
    {a, body, map} = avoid_capture(a, body, map, ctx)
    {b, body, map} = avoid_capture(b, body, map, ctx)
    {:letp, a, b, e, subst_sim(body, map, ctx)}
  end

  defp subst_sim({:match, scrut, arms}, map, ctx) do
    scrut = subst_sim(scrut, map, ctx)

    arms =
      Enum.map(arms, fn {:arm, c, names, tm} ->
        inner = Enum.reduce(names, map, &Map.delete(&2, &1))

        {names, tm} =
          Enum.map_reduce(names, tm, fn name, tm ->
            {name2, tm, _map} = avoid_capture(name, tm, inner, ctx)
            {name2, tm}
          end)

        {:arm, c, names, subst_sim(tm, inner, ctx)}
      end)

    {:match, scrut, arms}
  end

  defp subst_sim(tm, map, ctx), do: map_children(tm, &subst_sim(&1, map, ctx))

  defp avoid_capture(z, body, map, ctx) do
    if Enum.any?(map, fn {_from, to} -> to == z end) do
      z2 = fresh(z, ctx)
      {z2, subst_var(body, z, z2), map}
    else
      {z, body, map}
    end
  end

  # An arm the scrutinee cannot take becomes `abort`. The arm stays, so
  # the emitters still see every constructor. A tag that is not one of
  # the arms aborts nothing.
  defp kill_dead(scrut, arms, lays, facts) do
    case which_tag(scrut, arms, lays, facts) do
      {:ok, tag, _} ->
        if Enum.any?(arms, &match?({:arm, ^tag, _, _}, &1)) do
          Enum.map(arms, fn {:arm, c, ns, _tm} = arm ->
            if c == tag, do: arm, else: {:arm, c, ns, :abort}
          end)
        else
          arms
        end

      :no ->
        arms
    end
  end

  defp cmp_result({:wrd, k, op, [a, b]}, facts) when op in [:eq, :lt, :le] do
    case {lit_of(a, facts), lit_of(b, facts)} do
      {{:ok, n}, {:ok, m}} ->
        if op == :eq or k != :i64, do: {:ok, apply_cmp(op, n, m)}, else: :unknown

      _ ->
        cond do
          op == :eq and ne?(a, b, facts) -> {:ok, false}
          op == :eq and same?(a, b, facts) -> {:ok, true}
          true -> :unknown
        end
    end
  end

  defp cmp_result(_, _), do: :unknown

  defp apply_cmp(:eq, n, m), do: n == m
  defp apply_cmp(:lt, n, m), do: n < m
  defp apply_cmp(:le, n, m), do: n <= m

  defp lit_of({:wrd, _, {:lit, _, n}, []}, _facts) when is_integer(n), do: {:ok, n}
  defp lit_of({:var, x}, facts), do: lit_fact(Map.get(facts, x))
  defp lit_of(_, _), do: :no

  defp lit_fact({:wlit, n}) when is_integer(n), do: {:ok, n}
  defp lit_fact(_), do: :no

  defp ne?(a, b, facts) do
    ne_pair?(a, b, facts) or ne_pair?(b, a, facts)
  end

  defp ne_pair?({:var, x}, other, facts) do
    case Map.get(facts, x) do
      {:ne_word, n} -> match?({:ok, ^n}, lit_of(other, facts))
      {:ne_var, y} -> other == {:var, y}
      _ -> false
    end
  end

  defp ne_pair?(_, _, _), do: false

  defp same?({:var, x}, {:var, x}, _facts), do: true

  defp same?(a, b, facts) do
    case {lit_of(a, facts), lit_of(b, facts)} do
      {{:ok, n}, {:ok, n}} -> true
      _ -> false
    end
  end

  defp pure_value?({:var, _}), do: true
  defp pure_value?(:ze), do: true
  defp pure_value?(:tt), do: true
  defp pure_value?({:su, u}), do: pure_value?(u)
  defp pure_value?({:con, _, _, args}), do: Enum.all?(args, &pure_value?/1)
  defp pure_value?({:wrd, _, {:lit, _, n}, []}) when is_integer(n), do: true
  defp pure_value?({:wrd, _, b, []}) when b in [true, false], do: true

  defp pure_value?({:wrd, _, op, args}) when op in [:eq, :lt, :le],
    do: Enum.all?(args, &pure_value?/1)

  defp pure_value?(_), do: false

  defp site_counts(t), do: sites(t, %{})

  defp sites({:call, n, args}, acc) do
    acc = Map.update(acc, n, 1, &(&1 + 1))
    Enum.reduce(args, acc, &sites/2)
  end

  defp sites(t, acc), do: Enum.reduce(children(t), acc, &sites/2)

  defp put_children(t, kids) do
    case t do
      {:su, _} ->
        [u] = kids
        {:su, u}

      {:call, n, _} ->
        {:call, n, kids}

      {:con, d, c, _} ->
        {:con, d, c, kids}

      {:wrd, k, op, _} ->
        {:wrd, k, op, kids}

      {:pair, _, _} ->
        [a, b] = kids
        {:pair, a, b}

      {:uncons, _} ->
        [e] = kids
        {:uncons, e}

      {:stream, _, caps, s} ->
        [seed | cap_ts] = kids
        {:stream, seed, zip_caps(caps, cap_ts), s}

      {:bfold, s, caps, _, _} ->
        {cap_ts, [z, x]} = Enum.split(kids, length(caps))
        {:bfold, s, zip_caps(caps, cap_ts), z, x}

      {:bcat, _, _} ->
        [a, b] = kids
        {:bcat, a, b}

      {:blen, _} ->
        [a] = kids
        {:blen, a}

      {:beq, _, _} ->
        [a, b] = kids
        {:beq, a, b}

      {:bsub, _, _, _} ->
        [s, o, n] = kids
        {:bsub, s, o, n}

      {:bget, _, _} ->
        [s, i] = kids
        {:bget, s, i}

      {:btil, _, _} ->
        [s, b] = kids
        {:btil, s, b}

      {:baft, _, _} ->
        [s, b] = kids
        {:baft, s, b}

      {:sbytes, _} ->
        [s] = kids
        {:sbytes, s}

      {:bunc, _} ->
        [s] = kids
        {:bunc, s}

      {:scat, _, _} ->
        [a, b] = kids
        {:scat, a, b}

      {:slen, _} ->
        [a] = kids
        {:slen, a}

      {:seq, _, _} ->
        [a, b] = kids
        {:seq, a, b}

      _ ->
        t
    end
  end

  defp zip_caps(caps, ts), do: Enum.zip(Enum.map(caps, &elem(&1, 0)), ts)

  # ------------------------------------------------------------------ share

  defp share(t, ctx) do
    t = hoist(t, ctx)
    share_inside(t, ctx)
  end

  # Children that open a scope or a branch are shared on their own.
  # A let's value is evaluated exactly when the let is, so every call
  # strict in it is strict in the let and was already hoisted above it;
  # `share/2` on the value finds the rest: calls it repeats under its own
  # binders and arms. That includes the value a hoist bound, so a call
  # repeated inside it is hoisted in turn.
  defp share_inside({:let, x, lay, g, v, b}, ctx),
    do: {:let, x, lay, g, share(v, ctx), share(b, ctx)}

  # A pair's value is evaluated exactly when the letp is, as a let's
  # value is, so it takes the same `share/2`.
  defp share_inside({:letp, a, b, e, body}, ctx),
    do: {:letp, a, b, share(e, ctx), share(body, ctx)}

  defp share_inside({:match, scrut, arms}, ctx) do
    {:match, share_inside(scrut, ctx),
     Enum.map(arms, fn {:arm, c, names, tm} -> {:arm, c, names, share(tm, ctx)} end)}
  end

  defp share_inside(t, ctx), do: map_children(t, &share_inside(&1, ctx))

  defp hoist(t, ctx) do
    counts = occurrences(t)
    strict = strict(t)

    best =
      counts
      |> Enum.filter(fn {k, n} ->
        n >= 2 and MapSet.member?(strict, k) and ret_lay(k, ctx) != nil
      end)
      |> Enum.max_by(fn {k, _} -> size(k) end, fn -> nil end)

    case best do
      nil ->
        t

      {key, _} ->
        v = fresh("sh", ctx)
        lay = ret_lay(key, ctx)
        :counters.add(ctx.hoists, 1, 1)
        body = replace(t, key, v, free_vars(key))
        hoist({:let, v, lay, :reuse, key, body}, ctx)
    end
  end

  defp ret_lay({:call, name, _}, ctx) do
    case Map.get(ctx.by_name, name) do
      %{ret: lay} -> if plain_lay?(lay), do: lay, else: nil
      _ -> nil
    end
  end

  # Calls in `t` whose free variables are all bound outside `t`, with
  # how often each appears.
  defp occurrences(t), do: occ(t, MapSet.new(), %{})

  defp occ(t, bound, acc) do
    acc =
      case t do
        {:call, _, _} ->
          if disjoint?(free_vars(t), bound), do: Map.update(acc, t, 1, &(&1 + 1)), else: acc

        _ ->
          acc
      end

    fold_scoped(t, bound, acc, &occ/3)
  end

  # Calls every evaluation of `t` performs, free variables bound outside.
  defp strict(t), do: strict(t, MapSet.new())

  defp strict({:call, _, args} = t, bound) do
    own = if disjoint?(free_vars(t), bound), do: MapSet.new([t]), else: MapSet.new()
    Enum.reduce(args, own, &MapSet.union(&2, strict(&1, bound)))
  end

  defp strict({:let, x, _lay, _g, v, b}, bound),
    do: MapSet.union(strict(v, bound), strict(b, MapSet.put(bound, x)))

  defp strict({:letp, a, b, e, body}, bound),
    do: MapSet.union(strict(e, bound), strict(body, bound |> MapSet.put(a) |> MapSet.put(b)))

  # Every arm is a path, an arm that aborts included: it evaluates what
  # it binds before `abort`, and nothing after. A call the arms share is
  # strict only when each arm, that one too, evaluates it. The scrutinee
  # is evaluated on every path.
  defp strict({:match, scrut, arms}, bound) do
    per_arm =
      Enum.map(arms, fn {:arm, _, names, tm} ->
        strict(tm, MapSet.union(bound, MapSet.new(names)))
      end)

    arms_strict =
      case per_arm do
        [] -> MapSet.new()
        [s | ss] -> Enum.reduce(ss, s, &MapSet.intersection/2)
      end

    MapSet.union(strict(scrut, bound), arms_strict)
  end

  defp strict(t, bound) do
    t
    |> children()
    |> Enum.reduce(MapSet.new(), &MapSet.union(&2, strict(&1, bound)))
  end

  # Replace `key` by `{:var, v}` wherever its free variables still mean
  # what they mean at the top of `t`.
  defp replace(key, key, v, _fv), do: {:var, v}

  defp replace({:let, x, lay, g, val, b}, key, v, fv) do
    val = replace(val, key, v, fv)

    if MapSet.member?(fv, x),
      do: {:let, x, lay, g, val, b},
      else: {:let, x, lay, g, val, replace(b, key, v, fv)}
  end

  defp replace({:letp, a, b, e, body}, key, v, fv) do
    e = replace(e, key, v, fv)

    if MapSet.member?(fv, a) or MapSet.member?(fv, b),
      do: {:letp, a, b, e, body},
      else: {:letp, a, b, e, replace(body, key, v, fv)}
  end

  defp replace({:match, scrut, arms}, key, v, fv) do
    {:match, replace(scrut, key, v, fv),
     Enum.map(arms, fn {:arm, c, names, tm} = arm ->
       if Enum.any?(names, &MapSet.member?(fv, &1)),
         do: arm,
         else: {:arm, c, names, replace(tm, key, v, fv)}
     end)}
  end

  defp replace(t, key, v, fv), do: map_children(t, &replace(&1, key, v, fv))

  # A `:linear` binder unused after pruning or inlining is `:affine`,
  # including a parameter whose only use was a dropped fresh let.
  # Check then agrees with a valid Share rewrite.
  defp relax_fun(fun) do
    body = relax_tm(fun.body)

    params =
      Enum.map(fun.params, fn
        {n, lay, :linear} ->
          {n, lay, relax_grade(:linear, n, body)}

        p ->
          p
      end)

    %{fun | params: params, body: body}
  end

  defp relax_tm({:let, x, lay, g, v, b}) do
    v = relax_tm(v)
    b = relax_tm(b)
    {:let, x, lay, relax_grade(g, x, b), v, b}
  end

  defp relax_tm({:letp, a, b, e, body}), do: {:letp, a, b, relax_tm(e), relax_tm(body)}

  defp relax_tm({:match, s, arms}) when is_list(arms) do
    {:match, relax_tm(s), Enum.map(arms, fn {:arm, c, ns, tm} -> {:arm, c, ns, relax_tm(tm)} end)}
  end

  defp relax_tm({:match, s, lay, arms}) when is_list(arms) do
    {:match, relax_tm(s), lay,
     Enum.map(arms, fn {:arm, c, ns, tm} -> {:arm, c, ns, relax_tm(tm)} end)}
  end

  defp relax_tm({:lam, name, lay, g, body})
       when is_binary(name) and g in [:linear, :affine, :reuse] do
    body = relax_tm(body)
    {:lam, name, lay, relax_grade(g, name, body), body}
  end

  defp relax_tm(t), do: map_children(t, &relax_tm/1)

  defp relax_grade(:linear, x, b) do
    if MapSet.member?(free_vars(b), x), do: :linear, else: :affine
  end

  defp relax_grade(g, _x, _b), do: g

  # --------------------------------------------------------------- generic

  # Every node this pass understands. Anything else keeps the run as
  # elaborated.
  defp known?(t) do
    try do
      walk(t)
      true
    catch
      :unknown -> false
    end
  end

  defp walk(t) do
    case t do
      {:let, _, _, _, v, b} ->
        walk(v) && walk(b)

      {:letp, _, _, e, b} ->
        walk(e) && walk(b)

      {:match, s, arms} when is_list(arms) ->
        walk(s) && Enum.all?(arms, fn {:arm, _, _, tm} -> walk(tm) end)

      _ ->
        Enum.all?(children(t), &walk/1)
    end
  end

  # Term children of a node without binders, in evaluation order.
  defp children(t) do
    case t do
      :ze ->
        []

      :tt ->
        []

      :abort ->
        []

      {:nat, _} ->
        []

      {:var, _} ->
        []

      {:byt, _} ->
        []

      {:str, _} ->
        []

      {:su, u} ->
        [u]

      {:call, _, args} ->
        args

      {:con, _, _, args} ->
        args

      {:wrd, _, _, args} ->
        args

      {:pair, a, b} ->
        [a, b]

      {:uncons, e} ->
        [e]

      {:stream, seed, caps, _} ->
        [seed | Enum.map(caps, &elem(&1, 1))]

      {:bfold, _, caps, z, s} ->
        Enum.map(caps, &elem(&1, 1)) ++ [z, s]

      {:bcat, a, b} ->
        [a, b]

      {:blen, a} ->
        [a]

      {:beq, a, b} ->
        [a, b]

      {:bsub, s, o, n} ->
        [s, o, n]

      {:bget, s, i} ->
        [s, i]

      {:btil, s, b} ->
        [s, b]

      {:baft, s, b} ->
        [s, b]

      {:sbytes, s} ->
        [s]

      {:bunc, s} ->
        [s]

      {:scat, a, b} ->
        [a, b]

      {:slen, a} ->
        [a]

      {:seq, a, b} ->
        [a, b]

      {:let, _, _, _, v, b} ->
        [v, b]

      {:letp, _, _, e, b} ->
        [e, b]

      {:match, s, arms} ->
        [s | Enum.map(arms, fn {:arm, _, _, tm} -> tm end)]

      {:match, s, lay, arms} when not is_list(lay) and is_list(arms) ->
        [s | Enum.map(arms, fn {:arm, _, _, tm} -> tm end)]

      {:lam, name, _, g, body}
      when is_binary(name) and g in [:linear, :affine, :reuse] ->
        [body]

      {:appv, f, a} ->
        [f, a]

      {:data, _, args} when is_list(args) ->
        args

      _ ->
        throw(:unknown)
    end
  end

  defp map_children(t, f) do
    case t do
      {:su, u} ->
        {:su, f.(u)}

      {:call, n, args} ->
        {:call, n, Enum.map(args, f)}

      {:con, d, c, args} ->
        {:con, d, c, Enum.map(args, f)}

      {:wrd, k, op, args} ->
        {:wrd, k, op, Enum.map(args, f)}

      {:pair, a, b} ->
        {:pair, f.(a), f.(b)}

      {:uncons, e} ->
        {:uncons, f.(e)}

      {:stream, seed, caps, s} ->
        {:stream, f.(seed), map_caps(caps, f), s}

      {:bfold, s, caps, z, x} ->
        {:bfold, s, map_caps(caps, f), f.(z), f.(x)}

      {:bcat, a, b} ->
        {:bcat, f.(a), f.(b)}

      {:blen, a} ->
        {:blen, f.(a)}

      {:beq, a, b} ->
        {:beq, f.(a), f.(b)}

      {:bsub, s, o, n} ->
        {:bsub, f.(s), f.(o), f.(n)}

      {:bget, s, i} ->
        {:bget, f.(s), f.(i)}

      {:btil, s, b} ->
        {:btil, f.(s), f.(b)}

      {:baft, s, b} ->
        {:baft, f.(s), f.(b)}

      {:sbytes, s} ->
        {:sbytes, f.(s)}

      {:bunc, s} ->
        {:bunc, f.(s)}

      {:scat, a, b} ->
        {:scat, f.(a), f.(b)}

      {:slen, a} ->
        {:slen, f.(a)}

      {:seq, a, b} ->
        {:seq, f.(a), f.(b)}

      {:let, x, lay, g, v, b} ->
        {:let, x, lay, g, f.(v), f.(b)}

      {:letp, a, b, e, body} ->
        {:letp, a, b, f.(e), f.(body)}

      {:match, s, arms} ->
        {:match, f.(s), Enum.map(arms, fn {:arm, c, ns, tm} -> {:arm, c, ns, f.(tm)} end)}

      {:match, s, lay, arms} when not is_list(lay) and is_list(arms) ->
        {:match, f.(s), lay, Enum.map(arms, fn {:arm, c, ns, tm} -> {:arm, c, ns, f.(tm)} end)}

      {:lam, name, lay, g, body} when is_binary(name) ->
        {:lam, name, lay, g, f.(body)}

      {:appv, fun, a} ->
        {:appv, f.(fun), f.(a)}

      {:data, n, args} when is_list(args) ->
        {:data, n, Enum.map(args, f)}

      _ ->
        t
    end
  end

  defp map_caps(caps, f), do: Enum.map(caps, fn {n, tm} -> {n, f.(tm)} end)

  defp fold_scoped(t, bound, acc, f) do
    case t do
      {:let, x, _, _, v, b} ->
        acc = f.(v, bound, acc)
        f.(b, MapSet.put(bound, x), acc)

      {:letp, a, b, e, body} ->
        acc = f.(e, bound, acc)
        f.(body, bound |> MapSet.put(a) |> MapSet.put(b), acc)

      {:match, s, arms} ->
        acc = f.(s, bound, acc)

        Enum.reduce(arms, acc, fn {:arm, _, names, tm}, acc ->
          f.(tm, MapSet.union(bound, MapSet.new(names)), acc)
        end)

      {:match, s, _lay, arms} when is_list(arms) ->
        acc = f.(s, bound, acc)

        Enum.reduce(arms, acc, fn {:arm, _, names, tm}, acc ->
          f.(tm, MapSet.union(bound, MapSet.new(names)), acc)
        end)

      {:lam, name, _, _, body} when is_binary(name) ->
        f.(body, MapSet.put(bound, name), acc)

      _ ->
        Enum.reduce(children(t), acc, fn c, acc -> f.(c, bound, acc) end)
    end
  end

  defp free_vars(t), do: fv(t, MapSet.new())

  defp fv({:var, x}, bound),
    do: if(MapSet.member?(bound, x), do: MapSet.new(), else: MapSet.new([x]))

  defp fv({:let, x, _, _, v, b}, bound),
    do: MapSet.union(fv(v, bound), fv(b, MapSet.put(bound, x)))

  defp fv({:letp, a, b, e, body}, bound),
    do: MapSet.union(fv(e, bound), fv(body, bound |> MapSet.put(a) |> MapSet.put(b)))

  defp fv({:match, s, arms}, bound) do
    Enum.reduce(arms, fv(s, bound), fn {:arm, _, names, tm}, acc ->
      MapSet.union(acc, fv(tm, MapSet.union(bound, MapSet.new(names))))
    end)
  end

  defp fv({:match, s, _lay, arms}, bound) when is_list(arms) do
    Enum.reduce(arms, fv(s, bound), fn {:arm, _, names, tm}, acc ->
      MapSet.union(acc, fv(tm, MapSet.union(bound, MapSet.new(names))))
    end)
  end

  defp fv({:lam, name, _, _, body}, bound) when is_binary(name),
    do: fv(body, MapSet.put(bound, name))

  defp fv(t, bound), do: Enum.reduce(children(t), MapSet.new(), &MapSet.union(&2, fv(&1, bound)))

  defp binders(t) do
    own =
      case t do
        {:let, x, _, _, _, _} ->
          [x]

        {:letp, a, b, _, _} ->
          [a, b]

        {:match, _, arms} ->
          Enum.flat_map(arms, fn {:arm, _, ns, _} -> ns end)

        {:match, _, _, arms} when is_list(arms) ->
          Enum.flat_map(arms, fn {:arm, _, ns, _} -> ns end)

        {:lam, name, _, _, _} when is_binary(name) ->
          [name]

        _ ->
          []
      end

    Enum.reduce(children(t), MapSet.new(own), &MapSet.union(&2, binders(&1)))
  end

  defp contains?(t, pred), do: pred.(t) or Enum.any?(children(t), &contains?(&1, pred))

  defp disjoint?(a, b), do: MapSet.disjoint?(a, b)

  @doc """
  Nodes in an image term, the measure `inline_max:` and `grow_max:` count.
  """
  def size(t), do: 1 + Enum.reduce(children(t), 0, &(&2 + size(&1)))

  defp taken_names(funs) do
    Enum.reduce(funs, MapSet.new(), fn fun, acc ->
      acc = Enum.reduce(fun.params, acc, fn {p, _, _}, a -> MapSet.put(a, p) end)

      if known?(fun.body),
        do: MapSet.union(acc, binders(fun.body)) |> MapSet.union(free_vars(fun.body)),
        else: acc
    end)
  end
end

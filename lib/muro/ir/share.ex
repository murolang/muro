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
  that fits keeps its inlined body only when a hoist took place in it
  and its worst path does no more heavy work than its elaborated body
  shared without inlining;
  otherwise it keeps that one and draws nothing. Inlined bodies do not depend on that order
  either. A generated fold or stream step is never inlined into and
  draws nothing on the budget; it is still shared.

  The emitted program computes the same value as the checked term. A
  word operation, a constructor, and a byte literal are not shared:
  only `:call`. `Muro.IR.elaborate/2` is unchanged and still mirrors
  `agda/Muro/IR.agda`. This pass runs after it, for C, Rust and Zig. `stop/2` reads the early-exit test of a fold step for C.
  """

  @inline_max 1500

  @doc """
  The options of `funs/2` in `opts`, for an emitter to pass through.
  """
  def opts(opts) when is_list(opts),
    do: Keyword.take(opts, [:share, :inline, :inline_max, :grow_max])

  @doc """
  Rewrite `funs` (the list `Muro.IR.elaborate/1` returns). Order,
  names, parameters, and layouts are kept. `opts` may set `inline: false`
  (hoisting only), `share: false` (return `funs` unchanged),
  `inline_max:` (nodes per inlined callee), or `grow_max:` (nodes the
  whole image may grow by inlining, smallest growth first).
  """
  def funs(funs, opts \\ []) when is_list(funs) do
    if Keyword.get(opts, :share, true) do
      inline? = Keyword.get(opts, :inline, true)
      # A generated fold or stream step is never called by name, and its
      # name (`stepN`) may also be a source run's name.
      by_name = for f <- funs, not Map.get(f, :generated, false), into: %{}, do: {f.name, f}
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
        work: :ets.new(:share_work, [:set, :private])
      }

      try do
        out = optimize_all(funs, ctx, inline?)
        Enum.map(Enum.with_index(funs), fn {fun, i} -> Map.get(out, i, fun) end)
      after
        :ets.delete(ctx.memo)
        :ets.delete(ctx.fresh)
        :ets.delete(ctx.work)
      end
    else
      funs
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
    {acc, _lay} = List.last(params)

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
      {p, _} = Enum.at(ps, i)
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
  defp stop_test({:let, x, _lay, _val, body}, v, ok) do
    if x == v or MapSet.member?(ok, x), do: :none, else: stop_test(body, v, ok)
  end

  defp stop_test(_t, _v, _ok), do: :none

  # ---------------------------------------------------------------- driver

  # A run with nothing to share keeps its elaborated body, so inlining
  # alone never changes what is emitted. A call is inlined only when its
  # expansion holds a call, in this run's own names, that the fully
  # inlined run evaluates more than once. A per-octet step whose callee
  # only shares inside itself keeps calling it.
  # Every run is inlined first, then shared. A run whose inlining adds
  # nodes draws that growth, counted before any hoist, on the budget.
  # Runs draw in order of that growth, smallest first, then by name, so
  # who gets the budget does not depend on the order of `funs`; a run
  # whose growth does not fit what is left is shared as elaborated, and
  # its inlined body is never shared. A run that fits is shared both
  # ways, inlined and as elaborated, and keeps the inlined body only
  # when a hoist took place in it and its worst path does no more heavy
  # work (`work/2`) than the
  # elaborated one does once shared; otherwise it keeps that one and
  # draws nothing.
  defp optimize_all(funs, ctx, inline?) do
    plans =
      for {fun, i} <- Enum.with_index(funs), known?(fun.body) do
        # A generated fold or stream step is never inlined into: it runs
        # once per octet or element, so it keeps calling its run, and it
        # draws nothing on the budget. It is still shared.
        inline_here? = inline? and not Map.get(fun, :generated, false)
        body = if inline_here?, do: inline_run(fun, ctx), else: fun.body
        {i, fun, body, size(body) - size(fun.body)}
      end

    plans
    |> Enum.sort_by(fn {i, fun, body, grow} ->
      {body != fun.body, grow, fun.name, Map.get(fun, :generated, false), i}
    end)
    |> Enum.reduce(%{}, fn {i, fun, body, grow}, acc ->
      res =
        if body != fun.body and grow <= :counters.get(ctx.budget, 1) do
          plain = shared(fun.body, ctx)

          # The inlined body is kept only when some hoist took place in
          # it and its worst-path heavy work (folds, streams, uncons) is
          # no more than the elaborated body's, shared as `inline: false`
          # shares it. Otherwise that body is kept and nothing is drawn.
          # This compares worst paths, not each individual path.
          with {:ok, out} <- shared(body, ctx),
               true <- work(out, ctx) <= work(shared_body(plain, fun), ctx) do
            :counters.sub(ctx.budget, 1, max(grow, 0))
            {:ok, out}
          else
            _ -> plain
          end
        else
          shared(fun.body, ctx)
        end

      case res do
        {:ok, out} -> Map.put(acc, i, %{fun | body: out})
        :skip -> acc
      end
    end)
  end

  defp shared_body({:ok, out}, _fun), do: out
  defp shared_body(:skip, fun), do: fun.body

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

  # A run that reaches itself counts one unit there to break the cycle.
  # This undercounts mutually recursive SCCs: it is a finite heuristic,
  # not a bound on recursive runtime. Both sides of the keep comparison
  # use the same memoized callee costs, so cycle breaking does not change
  # that comparison's meaning (worst-path work under this measure).
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

  defp shared(body, ctx) do
    before = :counters.get(ctx.hoists, 1)
    out = share(body, ctx)
    if :counters.get(ctx.hoists, 1) > before, do: {:ok, out}, else: :skip
  end

  defp inline_run(fun, ctx) do
    scope = stable_names(fun)
    lays = Map.new(fun.params)
    full = propagate(inlined_body(fun, ctx, MapSet.new()), lays, ctx)
    wanted = repeated_keys(full, scope, ctx)

    if MapSet.size(wanted) == 0,
      do: fun.body,
      else:
        selective(fun.body, lays, %{scope: scope, wanted: wanted}, ctx, MapSet.new([fun.name]))
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
        {:let, x, _, _, _} -> [x]
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

  defp selective({:let, x, lay, v, b}, lays, want, ctx, seen),
    do:
      {:let, x, lay, selective(v, lays, want, ctx, seen),
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
    |> Enum.reduce(renamed, fn {{p, lay}, arg}, acc ->
      {:let, Map.fetch!(map, {:param, p}), lay, arg, acc}
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

  defp inlinable_body?(t) do
    not contains?(t, fn
      {:bfold, _, _, _, _} -> true
      {:stream, _, _, _} -> true
      {:uncons, _} -> true
      {:let, _, :erased, _, _} -> true
      _ -> false
    end)
  end

  # Fresh names for every binder of a callee body, parameters included.
  defp rename(body, params, ctx) do
    {map, env} =
      Enum.reduce(params, {%{}, %{}}, fn {p, _lay}, {map, env} ->
        f = fresh(p, ctx)
        {Map.put(map, {:param, p}, f), Map.put(env, p, f)}
      end)

    {rename_tm(body, env, ctx), map}
  end

  defp rename_tm({:var, x}, env, _ctx), do: {:var, Map.get(env, x, x)}

  defp rename_tm({:let, x, lay, v, b}, env, ctx) do
    f = fresh(x, ctx)
    {:let, f, lay, rename_tm(v, env, ctx), rename_tm(b, Map.put(env, x, f), ctx)}
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
  defp propagate({:let, x, lay, {:var, y}, b}, lays, ctx) do
    if :ets.member(ctx.fresh, x) and lay != :erased and Map.get(lays, y) == lay and
         not rebinds?(b, y) do
      propagate(subst_var(b, x, y), lays, ctx)
    else
      {:let, x, lay, {:var, y}, propagate(b, Map.put(lays, x, lay), ctx)}
    end
  end

  defp propagate({:let, x, lay, v, b}, lays, ctx),
    do: {:let, x, lay, propagate(v, lays, ctx), propagate(b, Map.put(lays, x, lay), ctx)}

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

  defp subst_var({:let, z, lay, v, b}, x, y) do
    v = subst_var(v, x, y)
    if z == x, do: {:let, z, lay, v, b}, else: {:let, z, lay, v, subst_var(b, x, y)}
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
  defp share_inside({:let, x, lay, v, b}, ctx),
    do: {:let, x, lay, share(v, ctx), share(b, ctx)}

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
        hoist({:let, v, lay, key, body}, ctx)
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

  defp strict({:let, x, _lay, v, b}, bound),
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

  defp replace({:let, x, lay, val, b}, key, v, fv) do
    val = replace(val, key, v, fv)

    if MapSet.member?(fv, x),
      do: {:let, x, lay, val, b},
      else: {:let, x, lay, val, replace(b, key, v, fv)}
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
      {:let, _, _, v, b} ->
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
      :ze -> []
      :tt -> []
      :abort -> []
      {:nat, _} -> []
      {:var, _} -> []
      {:byt, _} -> []
      {:str, _} -> []
      {:su, u} -> [u]
      {:call, _, args} -> args
      {:con, _, _, args} -> args
      {:wrd, _, _, args} -> args
      {:pair, a, b} -> [a, b]
      {:uncons, e} -> [e]
      {:stream, seed, caps, _} -> [seed | Enum.map(caps, &elem(&1, 1))]
      {:bfold, _, caps, z, s} -> Enum.map(caps, &elem(&1, 1)) ++ [z, s]
      {:bcat, a, b} -> [a, b]
      {:blen, a} -> [a]
      {:beq, a, b} -> [a, b]
      {:bsub, s, o, n} -> [s, o, n]
      {:bget, s, i} -> [s, i]
      {:btil, s, b} -> [s, b]
      {:baft, s, b} -> [s, b]
      {:sbytes, s} -> [s]
      {:bunc, s} -> [s]
      {:scat, a, b} -> [a, b]
      {:slen, a} -> [a]
      {:seq, a, b} -> [a, b]
      {:let, _, _, v, b} -> [v, b]
      {:letp, _, _, e, b} -> [e, b]
      {:match, s, arms} -> [s | Enum.map(arms, fn {:arm, _, _, tm} -> tm end)]
      _ -> throw(:unknown)
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

      {:let, x, lay, v, b} ->
        {:let, x, lay, f.(v), f.(b)}

      {:letp, a, b, e, body} ->
        {:letp, a, b, f.(e), f.(body)}

      {:match, s, arms} ->
        {:match, f.(s), Enum.map(arms, fn {:arm, c, ns, tm} -> {:arm, c, ns, f.(tm)} end)}

      _ ->
        t
    end
  end

  defp map_caps(caps, f), do: Enum.map(caps, fn {n, tm} -> {n, f.(tm)} end)

  defp fold_scoped(t, bound, acc, f) do
    case t do
      {:let, x, _, v, b} ->
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

      _ ->
        Enum.reduce(children(t), acc, fn c, acc -> f.(c, bound, acc) end)
    end
  end

  defp free_vars(t), do: fv(t, MapSet.new())

  defp fv({:var, x}, bound),
    do: if(MapSet.member?(bound, x), do: MapSet.new(), else: MapSet.new([x]))

  defp fv({:let, x, _, v, b}, bound), do: MapSet.union(fv(v, bound), fv(b, MapSet.put(bound, x)))

  defp fv({:letp, a, b, e, body}, bound),
    do: MapSet.union(fv(e, bound), fv(body, bound |> MapSet.put(a) |> MapSet.put(b)))

  defp fv({:match, s, arms}, bound) do
    Enum.reduce(arms, fv(s, bound), fn {:arm, _, names, tm}, acc ->
      MapSet.union(acc, fv(tm, MapSet.union(bound, MapSet.new(names))))
    end)
  end

  defp fv(t, bound), do: Enum.reduce(children(t), MapSet.new(), &MapSet.union(&2, fv(&1, bound)))

  defp binders(t) do
    own =
      case t do
        {:let, x, _, _, _} -> [x]
        {:letp, a, b, _, _} -> [a, b]
        {:match, _, arms} -> Enum.flat_map(arms, fn {:arm, _, ns, _} -> ns end)
        _ -> []
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
      acc = Enum.reduce(fun.params, acc, fn {p, _}, a -> MapSet.put(a, p) end)

      if known?(fun.body),
        do: MapSet.union(acc, binders(fun.body)) |> MapSet.union(free_vars(fun.body)),
        else: acc
    end)
  end
end

defmodule Muro.Temporal do
  @moduledoc """
  Decides `always`, `eventually`, and `leads_to` on the reachable
  configurations of one buffered meeting.

  | Elixir | Agda |
  | --- | --- |
  | `reachable/1` | `Muro.Temporal.Graph.reachable` |
  | `levels/4` | the breadth-first loop inside `reachable` |
  | `decide_nostuck/2` | `Muro.Temporal.Graph.decide-nostuck` |
  | `worklist/2`, `prune/2` | `Muro.Temporal.Live.prune` (the zero out-degree queue) |
  | `lasso/3` | `Muro.Temporal.Live.loop-of` (`tour-of`, `walkC`, `cutC`) |
  | `check/5` | `Muro.Temporal.Decide.check` |
  | `holds?/3` | `Muro.Temporal.⟦_⟧` |

  The search records a parent for every configuration it enqueues, so the
  path it reports is the breadth-first one. Liveness removes every
  configuration whose surviving out-degree is zero. That set is `Z` from
  `Muro.Temporal.Live`. `lasso` takes the first successor that is still
  in `Z`. A finished configuration stutters, so it is not removed.
  """

  alias Muro.Temporal.{Compile, Elab, Graph}

  @run_msg "temporal formulas do not mention run definitions"

  @doc """
  `{:ok, count}` when the formula holds, `count` the number of reachable
  configurations. `{:error, message}` when it does not, or the meeting is
  out of scope. The message has no location and no declaration name.
  """
  def judge(book, %{meeting: meeting} = decl, fuel \\ nil) when is_list(book) do
    fuel = fuel || Muro.Check.default_fuel()

    status =
      case fetch_meet(book, meeting) do
        {:error, _} ->
          :absent

        {:ok, meet} ->
          case Muro.Check.check_def(book, meet, fuel) do
            :ok -> :ok
            {:note, _} -> :ok
            {:error, _} -> :unchecked
          end
      end

    case prepare(book, meeting, status) do
      {:ok, prep} -> judge_prepared(book, decl, {:ok, prep})
      {:error, _} = err -> err
    end
  end

  @doc false
  def prepare(_book, name, :absent), do: {:error, "unknown meeting #{name}"}

  def prepare(_book, name, :unchecked), do: {:error, "skipped because #{name} does not check"}

  # The meeting check has already been recorded. This builds that
  # meeting's configuration graph once: the reachable configurations,
  # their breadth-first parents, and the successor table.
  def prepare(book, name, :ok) do
    with {:ok, meet} <- fetch_meet(book, name),
         :ok <- needs_buffer(meet),
         {:ok, g} <- build(book, meet) do
      {cs, parents} = reachable(g)
      edges = Map.new(cs, fn conf -> {conf, Graph.edges(g, conf)} end)

      case nostuck(g, cs) do
        :ok -> {:ok, %{g: g, cs: cs, parents: parents, edges: edges}}
        {:error, _} = err -> err
      end
    end
  end

  @doc false
  def judge_prepared(book, %{formula: formula}, {:ok, prep}) do
    %{g: g, cs: cs, parents: parents, edges: edges} = prep

    case expand(book, g, formula) do
      {:ok, formulas} ->
        case Enum.find_value(formulas, fn f ->
               case check(g, parents, cs, edges, f) do
                 :yes -> nil
                 {:no, msg} -> {:no, msg}
               end
             end) do
          nil -> {:ok, length(cs)}
          {:no, msg} -> {:error, msg}
        end

      {:error, _} = err ->
        err
    end
  end

  def judge_prepared(_book, _decl, {:error, msg}), do: {:error, msg}

  @doc """
  Transcribes `decide-nostuck` over the configurations `reachable` returned.
  """
  def decide_nostuck(g, confs) do
    Enum.find_value(confs, :ok, fn conf ->
      case Graph.view(g, conf) do
        {:bad, fault} -> {:stuck, fault, conf}
        _ -> nil
      end
    end)
  end

  @doc """
  Transcribes `Live.prune`. `Z` is `prune/2` of the region's edges.
  """
  def worklist(g, region) when is_list(region) do
    succ = Map.new(region, fn conf -> {conf, Graph.edges(g, conf)} end)
    prune(region, succ)
  end

  # O(V + E), where V is `length(nodes)` and E is the number of edges in
  # `succ` that land inside `nodes`. This is `Z` from `Muro.Temporal.Live`.
  #
  # `Live` states the algorithm above `prune`: a configuration is removed
  # when it has no successor left in the region; removing it deletes every
  # edge into it; the queue is exactly the configurations whose surviving
  # successor list is empty; a finished configuration stutters, so that
  # self-edge keeps it. The measure there is the length of the surviving
  # list, and there is no fuel. The Agda function recomputes `outs` at
  # each pop, which keeps the proof free of a stored count. The set that
  # remains does not depend on that recomputation.
  #
  # The membership set, the predecessor lists, and the out-degrees are
  # built once from `succ`. A configuration starts on the queue when its
  # degree is zero, and a predecessor is queued when the last edge into a
  # removed configuration drops its degree to zero. Each configuration is
  # queued at most once and each edge decrements one degree, so the pass
  # is linear. Each pop deletes the configuration from the surviving set,
  # which is the well-founded measure. Pop order does not change `Z`: it
  # is the greatest subset in which every configuration still has a
  # successor, the greatest fixed point of deleting a zero-degree
  # configuration. That is also the set of configurations that can reach
  # a cycle in the region, so there is no separate SCC pass. `lasso`
  # reads this set, not the order of pops.
  @doc """
  The surviving subset of `nodes`, in the original order.

  `succ` maps a node to its successors. An entry is a destination or a
  `{who, dest}` edge. Destinations outside `nodes` are ignored.
  """
  def prune(nodes, succ) when is_list(nodes) and is_map(succ) do
    member = MapSet.new(nodes)

    {degree, preds} =
      Enum.reduce(nodes, {%{}, %{}}, fn node, {degree, preds} ->
        outs =
          succ
          |> Map.get(node, [])
          |> Enum.map(&dest/1)
          |> Enum.filter(&MapSet.member?(member, &1))

        degree = Map.put(degree, node, length(outs))

        preds =
          Enum.reduce(outs, preds, fn target, preds ->
            Map.update(preds, target, [node], &[node | &1])
          end)

        {degree, preds}
      end)

    queue = Enum.filter(nodes, &(Map.get(degree, &1, 0) == 0))
    alive = drop_zeros(queue, [], degree, preds, member)
    Enum.filter(nodes, &MapSet.member?(alive, &1))
  end

  defp drop_zeros([], [], _degree, _preds, alive), do: alive

  defp drop_zeros([], back, degree, preds, alive) do
    drop_zeros(:lists.reverse(back), [], degree, preds, alive)
  end

  defp drop_zeros([node | rest], back, degree, preds, alive) do
    if MapSet.member?(alive, node) do
      alive = MapSet.delete(alive, node)

      {degree, back} =
        Enum.reduce(Map.get(preds, node, []), {degree, back}, fn pred, {degree, back} ->
          if MapSet.member?(alive, pred) do
            left = Map.get(degree, pred, 0) - 1
            degree = Map.put(degree, pred, left)
            back = if left == 0, do: [pred | back], else: back
            {degree, back}
          else
            {degree, back}
          end
        end)

      drop_zeros(rest, back, degree, preds, alive)
    else
      drop_zeros(rest, back, degree, preds, alive)
    end
  end

  defp dest({:lside, dest}), do: dest
  defp dest({:rside, dest}), do: dest
  defp dest({:fin, dest}), do: dest
  defp dest(dest), do: dest

  @doc """
  Transcribes `Live.loop-of`. `{stem, loop}` are steps `{who, src, dest}`.
  `leads_to` puts the breadth-first parent trace in front of that pair.
  """
  def lasso(g, z, conf) when is_list(z) do
    edges = Map.new(z, fn c -> {c, Graph.edges(g, c)} end)
    run_lasso(edges, z, conf)
  end

  defp run_lasso(edges, z, conf) do
    walk(edges, MapSet.new(z), conf, MapSet.new(), conf, [])
  end

  @doc """
  Transcribes `Decide.check` for one elaborated formula.
  `formula` is `%{kind: :always | :eventually | :leads_to, src: ast, prop: resolved}`.
  """
  def check(g, parents, confs, _edges, %{kind: :always, src: src, prop: prop}) do
    case Enum.find(confs, fn conf -> not holds?(g, prop, conf) end) do
      nil -> :yes
      conf -> {:no, safety_msg(g, src, trace(parents, conf), conf)}
    end
  end

  def check(g, _parents, confs, edges, %{kind: :eventually, src: src, prop: prop}) do
    region = Enum.filter(confs, fn conf -> not holds?(g, prop, conf) end)
    z = prune(region, edges)
    zset = MapSet.new(z)

    if MapSet.member?(zset, Graph.init(g)) do
      {stem, loop} = run_lasso(edges, z, Graph.init(g))
      {:no, live_msg(g, {:eventually, src}, [], stem, loop)}
    else
      :yes
    end
  end

  def check(g, parents, confs, edges, %{kind: :leads_to, src: {p, q}, prop: {rp, rq}}) do
    region = Enum.filter(confs, fn conf -> not holds?(g, rq, conf) end)
    z = prune(region, edges)
    zset = MapSet.new(z)

    case Enum.find(confs, fn conf -> holds?(g, rp, conf) and MapSet.member?(zset, conf) end) do
      nil ->
        :yes

      conf ->
        {stem, loop} = run_lasso(edges, z, conf)
        {:no, live_msg(g, {:leads_to, p, q}, trace(parents, conf), stem, loop)}
    end
  end

  @doc """
  Transcribes `⟦_⟧`.
  """
  def holds?(_g, true, _conf), do: true
  def holds?(_g, false, _conf), do: false
  def holds?(g, {:not, p}, conf), do: not holds?(g, p, conf)
  def holds?(g, {:and, p, q}, conf), do: holds?(g, p, conf) and holds?(g, q, conf)
  def holds?(g, {:or, p, q}, conf), do: holds?(g, p, conf) or holds?(g, q, conf)
  def holds?(g, {:imp, p, q}, conf), do: not holds?(g, p, conf) or holds?(g, q, conf)
  def holds?(g, {:done, side}, conf), do: block_kind(g, side, conf) == :done
  def holds?(g, {:stopped, side}, conf), do: block_kind(g, side, conf) == :stop
  def holds?(_g, {:at, side, index}, conf), do: ptr(conf, side) == index

  def holds?(g, {:eq, side, slot, lit}, conf) do
    case held(env(conf, side), slot) do
      {:ok, k} -> match_lit(g, k, lit)
      :no -> false
    end
  end

  def holds?(g, {:lt, side, slot, n}, conf) do
    case nat_held(g, env(conf, side), slot) do
      {:ok, m} -> m < n
      :no -> false
    end
  end

  def holds?(g, {:le, side, slot, n}, conf) do
    case nat_held(g, env(conf, side), slot) do
      {:ok, m} -> m <= n
      :no -> false
    end
  end

  def holds?(g, {:is, side, slot, name}, conf) do
    case held(env(conf, side), slot) do
      {:ok, k} -> match?({:con, ^name}, Enum.at(g.alpha, k))
      :no -> false
    end
  end

  def holds?(_g, {:eq2, s1, i1, s2, i2}, conf) do
    case {held(env(conf, s1), i1), held(env(conf, s2), i2)} do
      {{:ok, k}, {:ok, k}} -> true
      _ -> false
    end
  end

  def holds?(_g, {:bound, side, slot}, conf) do
    match?({:ok, _}, held(env(conf, side), slot))
  end

  def holds?(_g, {:empty, side}, conf), do: inbox(conf, side) == []
  def holds?(g, {:full, side}, conf), do: length(inbox(conf, side)) >= g.cap

  def holds?(g, {:head, side, lit}, conf) do
    case inbox(conf, side) do
      [tok | _] -> match_tok(g, tok, lit)
      [] -> false
    end
  end

  # The back list is reversed. Cons is O(1), and the list is reversed
  # once when it becomes the front, so each successor is charged once.
  defp enqueue(_g, _conf, [], back, seen, parents), do: {back, seen, parents}

  defp enqueue(g, conf, [{who, dest} | rest], back, seen, parents) do
    if MapSet.member?(seen, dest) do
      enqueue(g, conf, rest, back, seen, parents)
    else
      enqueue(
        g,
        conf,
        rest,
        [dest | back],
        MapSet.put(seen, dest),
        Map.put(parents, dest, {who, conf})
      )
    end
  end

  @doc """
  One frontier of `reachable`. The queue is popped from the front and new
  configurations are appended, left successor before right.

  O(V + E). Each configuration is enqueued at most once. The two lists
  are a queue: the front is popped and successors are consed onto the
  back. That is the breadth-first order of `Muro.Temporal.Search`.
  The recursion is well-founded on the configurations not yet seen.
  """
  def levels(g, queue, seen, parents) when is_list(queue) do
    drain(g, queue, [], seen, parents, [])
  end

  def levels(g, queue, seen, parents, acc) when is_list(queue) and is_list(acc) do
    drain(g, queue, [], seen, parents, acc)
  end

  defp drain(_g, [], [], _seen, parents, acc), do: {Enum.reverse(acc), parents}

  defp drain(g, [], back, seen, parents, acc) do
    drain(g, :lists.reverse(back), [], seen, parents, acc)
  end

  defp drain(g, [conf | front], back, seen, parents, acc) do
    {back, seen, parents} = enqueue(g, conf, Graph.steps_of(g, conf), back, seen, parents)
    drain(g, front, back, seen, parents, [conf | acc])
  end

  @doc """
  Transcribes `Graph.reachable`. Returns the configurations in discovery
  order and the parent map (`child => {who, parent}`).
  """
  def reachable(g) do
    Muro.Explore.note(:graph, meeting_name(g))
    start = Graph.init(g)
    levels(g, [start], MapSet.new([start]), %{}, [])
  end

  defp meeting_name(%{meeting: name}), do: name
  defp meeting_name(_g), do: nil

  defp walk(edges, zset, conf, seen, origin, steps) do
    if MapSet.member?(seen, conf) do
      cut(conf, origin, :lists.reverse(steps))
    else
      case first_out(edges, zset, conf) do
        {who, dest} ->
          walk(edges, zset, dest, MapSet.put(seen, conf), origin, [{who, conf, dest} | steps])

        nil ->
          {[], []}
      end
    end
  end

  defp first_out(edges, zset, conf) do
    Enum.find(Map.get(edges, conf, []), fn
      {who, dest} when who in [:lside, :rside, :fin] -> MapSet.member?(zset, dest)
      _ -> false
    end)
  end

  # The edge that first arrives on the repeated configuration is the last
  # step of the stem. The steps after it are the loop. A repeat of the
  # origin is a loop with an empty stem.
  defp cut(target, origin, steps) when target == origin, do: {[], steps}
  defp cut(target, _origin, steps), do: split_at(target, steps, [])

  defp split_at(_target, [], acc), do: {Enum.reverse(acc), []}

  defp split_at(target, [{_who, _src, dest} = step | rest], acc) when dest == target do
    {Enum.reverse([step | acc]), rest}
  end

  defp split_at(target, [step | rest], acc), do: split_at(target, rest, [step | acc])

  defp trace(parents, conf), do: trace(parents, conf, [])

  defp trace(parents, conf, acc) do
    case Map.get(parents, conf) do
      nil -> acc
      {who, parent} -> trace(parents, parent, [{who, parent, conf} | acc])
    end
  end

  defp nostuck(g, confs) do
    case decide_nostuck(g, confs) do
      :ok -> :ok
      {:stuck, fault, conf} -> {:error, "#{fault_name(fault)}: #{dump(g, conf)}"}
    end
  end

  defp fault_name(:recv_l), do: "reception error"
  defp fault_name(:recv_r), do: "reception error"
  defp fault_name(:orphan), do: "orphan message"
  defp fault_name(:dead), do: "deadlock"
  defp fault_name(:unbounded), do: "unbounded recursive payload"
  defp fault_name(other), do: to_string(other)

  defp build(book, meet) do
    with {:ok, left} <- fetch_process(book, meet.left),
         {:ok, right} <- fetch_process(book, meet.right),
         {:ok, lp} <- Elab.elab(left.proc, book),
         {:ok, rp} <- Elab.elab(right.proc, book),
         {:ok, lc} <- Compile.compile(lp),
         {:ok, rc} <- Compile.compile(rp) do
      {:ok,
       %{
         code_l: lc.blocks,
         code_r: rc.blocks,
         alpha: Compile.alphabet(lc.blocks, rc.blocks),
         cap: meet.buffer,
         entry_l: lc.entry,
         entry_r: rc.entry,
         slots_l: lc.slots,
         slots_r: rc.slots,
         actions_l: lc.actions,
         actions_r: rc.actions,
         binders_l: lc.binders,
         binders_r: rc.binders,
         name_l: meet.left,
         name_r: meet.right,
         session_l: session_of(book, left),
         session_r: session_of(book, right),
         meeting: meet.name
       }}
    end
  end

  defp fetch_meet(book, name) do
    case Enum.find(book, &(Map.get(&1, :kind) == :meet and &1.name == name)) do
      nil -> {:error, "unknown meeting #{name}"}
      meet -> {:ok, meet}
    end
  end

  defp needs_buffer(%{buffer: n}) when is_integer(n), do: :ok
  defp needs_buffer(_meet), do: {:error, "temporal needs a buffered meeting"}

  defp fetch_process(book, name) do
    case Enum.find(book, &(Map.get(&1, :kind) in [:conform, :read] and &1.name == name)) do
      nil -> {:error, "unknown process #{name}"}
      proc -> {:ok, proc}
    end
  end

  defp session_of(_book, %{kind: :conform, session: session}), do: show_session(session)

  defp session_of(book, %{kind: :read, endpoint: ename}) do
    case Enum.find(book, &(Map.get(&1, :kind) == :endpoint and &1.name == ename)) do
      %{session: session} -> show_session(session)
      _ -> "?"
    end
  end

  defp session_of(_, _), do: "?"

  defp show_session(name) when is_binary(name), do: name
  defp show_session({:sess, name, _}), do: to_string(name)
  defp show_session(other), do: to_string(other)

  defp expand(book, g, {:forall, x, ty, formula}) do
    with {:ok, lits} <- quantify(book, ty) do
      Enum.reduce_while(lits, {:ok, []}, fn lit, {:ok, acc} ->
        case expand(book, g, subst(formula, x, lit)) do
          {:ok, fs} -> {:cont, {:ok, acc ++ fs}}
          {:error, _} = err -> {:halt, err}
        end
      end)
    end
  end

  defp expand(book, g, formula) do
    case resolve(book, g, formula) do
      {:ok, resolved} -> {:ok, [resolved]}
      {:error, _} = err -> err
    end
  end

  defp quantify(_book, :nat), do: {:error, "forall over Nat ranges over an open type"}

  defp quantify(_book, :bit), do: {:ok, [:b0, :b1]}

  defp quantify(book, {:dat, name, _}) do
    case Enum.find(book, &(&1[:kind] == :data and &1.name == name)) do
      %{params: params, ctors: ctors} = d ->
        if ctors != [] and Enum.all?(ctors, &nullary?(&1, d)) and params_closed?(params) do
          {:ok, Enum.map(ctors, &{:con, &1.name})}
        else
          {:error, "forall over #{name} ranges over an open type"}
        end

      _ ->
        {:error, "forall over #{name} ranges over an open type"}
    end
  end

  defp quantify(_book, ty), do: {:error, "forall over #{ty_open(ty)} ranges over an open type"}

  defp params_closed?(_params), do: true

  defp nullary?(%{type: ty}, %{params: params}) do
    nullary_after?(ty, length(params))
  end

  defp nullary_after?({:pi, _, _, _, body}, n) when n > 0, do: nullary_after?(body, n - 1)
  defp nullary_after?({:pi, _, _, _, _}, 0), do: false
  defp nullary_after?(_, 0), do: true
  defp nullary_after?(_, _), do: false

  defp ty_open(:unit), do: "Unit"
  defp ty_open({:vec, _, _}), do: "Vec"
  defp ty_open({:pair, _, _}), do: "a pair"
  defp ty_open({:rec, _}), do: "a record"
  defp ty_open(other), do: inspect(other)

  defp subst({:forall, y, ty, f}, x, lit), do: {:forall, y, ty, subst(f, x, lit)}
  defp subst({:always, p}, x, lit), do: {:always, subst_prop(p, x, lit)}
  defp subst({:eventually, p}, x, lit), do: {:eventually, subst_prop(p, x, lit)}

  defp subst({:leads_to, p, q}, x, lit),
    do: {:leads_to, subst_prop(p, x, lit), subst_prop(q, x, lit)}

  defp subst_prop({:not, p}, x, lit), do: {:not, subst_prop(p, x, lit)}
  defp subst_prop({:and, p, q}, x, lit), do: {:and, subst_prop(p, x, lit), subst_prop(q, x, lit)}
  defp subst_prop({:or, p, q}, x, lit), do: {:or, subst_prop(p, x, lit), subst_prop(q, x, lit)}
  defp subst_prop({:imp, p, q}, x, lit), do: {:imp, subst_prop(p, x, lit), subst_prop(q, x, lit)}
  defp subst_prop({:eq, role, name, val}, x, lit), do: {:eq, role, name, subst_val(val, x, lit)}
  defp subst_prop({:head, role, val}, x, lit), do: {:head, role, subst_val(val, x, lit)}
  defp subst_prop({:is, role, name, {:var, x}}, x, lit), do: is_from(role, name, lit)
  defp subst_prop(other, _x, _lit), do: other

  defp subst_val({:var, x}, x, lit), do: lit
  defp subst_val(other, _x, _lit), do: other

  defp is_from(role, name, {:con, c}), do: {:is, role, name, c}
  defp is_from(role, name, other), do: {:is, role, name, other}

  defp resolve(book, g, {:always, prop}) do
    with {:ok, p} <- resolve_prop(book, g, prop), do: {:ok, %{kind: :always, src: prop, prop: p}}
  end

  defp resolve(book, g, {:eventually, prop}) do
    with {:ok, p} <- resolve_prop(book, g, prop) do
      {:ok, %{kind: :eventually, src: prop, prop: p}}
    end
  end

  defp resolve(book, g, {:leads_to, p, q}) do
    with {:ok, rp} <- resolve_prop(book, g, p),
         {:ok, rq} <- resolve_prop(book, g, q) do
      {:ok, %{kind: :leads_to, src: {p, q}, prop: {rp, rq}}}
    end
  end

  defp resolve_prop(_book, _g, true), do: {:ok, true}
  defp resolve_prop(_book, _g, false), do: {:ok, false}

  defp resolve_prop(book, g, {:not, p}) do
    with {:ok, p} <- resolve_prop(book, g, p), do: {:ok, {:not, p}}
  end

  defp resolve_prop(book, g, {:and, p, q}) do
    with {:ok, p} <- resolve_prop(book, g, p),
         {:ok, q} <- resolve_prop(book, g, q),
         do: {:ok, {:and, p, q}}
  end

  defp resolve_prop(book, g, {:or, p, q}) do
    with {:ok, p} <- resolve_prop(book, g, p),
         {:ok, q} <- resolve_prop(book, g, q),
         do: {:ok, {:or, p, q}}
  end

  defp resolve_prop(book, g, {:imp, p, q}) do
    with {:ok, p} <- resolve_prop(book, g, p),
         {:ok, q} <- resolve_prop(book, g, q),
         do: {:ok, {:imp, p, q}}
  end

  defp resolve_prop(book, g, {:done, role}) do
    with {:ok, side} <- role_side(book, g, role), do: {:ok, {:done, side}}
  end

  defp resolve_prop(book, g, {:stopped, role}) do
    with {:ok, side} <- role_side(book, g, role), do: {:ok, {:stopped, side}}
  end

  defp resolve_prop(book, g, {:empty, role}) do
    with {:ok, side} <- role_side(book, g, role), do: {:ok, {:empty, side}}
  end

  defp resolve_prop(book, g, {:full, role}) do
    with {:ok, side} <- role_side(book, g, role), do: {:ok, {:full, side}}
  end

  defp resolve_prop(book, g, {:at, role, n, verb}) do
    with {:ok, side} <- role_side(book, g, role),
         {:ok, index} <- nth_action(g, side, verb, n) do
      {:ok, {:at, side, index}}
    end
  end

  defp resolve_prop(book, g, {:bound, role, name}) do
    with {:ok, side} <- role_side(book, g, role),
         {:ok, slot, _ty} <- binder(g, side, role, name) do
      {:ok, {:bound, side, slot}}
    end
  end

  defp resolve_prop(book, g, {:eq, role, name, val}) do
    with {:ok, side} <- role_side(book, g, role),
         {:ok, slot, ty} <- binder(g, side, role, name),
         {:ok, lit} <- slot_lit(book, val, ty) do
      {:ok, {:eq, side, slot, lit}}
    end
  end

  defp resolve_prop(book, g, {:lt, role, name, n}) do
    with {:ok, side} <- role_side(book, g, role),
         {:ok, slot, ty} <- binder(g, side, role, name),
         :ok <- nat_binder(ty) do
      {:ok, {:lt, side, slot, n}}
    end
  end

  defp resolve_prop(book, g, {:le, role, name, n}) do
    with {:ok, side} <- role_side(book, g, role),
         {:ok, slot, ty} <- binder(g, side, role, name),
         :ok <- nat_binder(ty) do
      {:ok, {:le, side, slot, n}}
    end
  end

  defp resolve_prop(book, g, {:is, role, name, ctor}) do
    with {:ok, side} <- role_side(book, g, role),
         {:ok, slot, ty} <- binder(g, side, role, name),
         :ok <- ctor_lit(book, ctor, ty) do
      {:ok, {:is, side, slot, to_string(ctor)}}
    end
  end

  defp resolve_prop(book, g, {:eq2, r1, n1, r2, n2}) do
    with {:ok, s1} <- role_side(book, g, r1),
         {:ok, i1, _} <- binder(g, s1, r1, n1),
         {:ok, s2} <- role_side(book, g, r2),
         {:ok, i2, _} <- binder(g, s2, r2, n2) do
      {:ok, {:eq2, s1, i1, s2, i2}}
    end
  end

  defp resolve_prop(book, g, {:head, role, val}) do
    with {:ok, side} <- role_side(book, g, role),
         {:ok, lit} <- head_lit(book, val) do
      {:ok, {:head, side, lit}}
    end
  end

  defp resolve_prop(_book, _g, _other), do: {:error, "nested temporal operator"}

  defp role_side(_book, g, name) when name == g.name_l, do: {:ok, :l}
  defp role_side(_book, g, name) when name == g.name_r, do: {:ok, :r}

  defp role_side(book, _g, name) do
    if run?(book, name), do: {:error, @run_msg}, else: {:error, "unknown role #{name}"}
  end

  defp binder(g, :l, role, name), do: one_binder(g.binders_l, role, name)
  defp binder(g, :r, role, name), do: one_binder(g.binders_r, role, name)

  defp one_binder(binders, role, name) do
    case Enum.filter(binders, &(&1.name == to_string(name))) do
      [b] -> {:ok, b.slot, b.type}
      [] -> {:error, "unknown binder #{name} in #{role}"}
      _ -> {:error, "ambiguous binder #{name} in #{role}"}
    end
  end

  defp nth_action(g, :l, verb, n), do: nth_action(g.actions_l, verb, n)
  defp nth_action(g, :r, verb, n), do: nth_action(g.actions_r, verb, n)

  defp nth_action(actions, verb, n) when is_list(actions) do
    case actions |> Enum.filter(&(&1.verb == verb)) |> Enum.at(n - 1) do
      nil -> {:error, "unknown step"}
      %{index: index} -> {:ok, index}
    end
  end

  defp nat_binder(:nat), do: :ok
  defp nat_binder(_), do: {:error, "ill-typed literal"}

  defp slot_lit(_book, {:nat, n}, :nat) when is_integer(n), do: {:ok, {:nat, n}}
  defp slot_lit(_book, :b0, :bit), do: {:ok, :b0}
  defp slot_lit(_book, :b1, :bit), do: {:ok, :b1}

  defp slot_lit(book, {:var, name}, {:dat, dname, _}) do
    name = to_string(name)

    cond do
      ctor_of?(book, dname, name) -> {:ok, {:con, name}}
      ctor_of?(book, name) -> {:error, "ill-typed literal"}
      run?(book, name) -> {:error, @run_msg}
      true -> {:error, "unknown constructor #{name}"}
    end
  end

  defp slot_lit(book, {:con, name}, {:dat, dname, _}) do
    slot_lit(book, {:var, name}, {:dat, dname, []})
  end

  defp slot_lit(book, {:var, name}, _ty) do
    name = to_string(name)

    cond do
      run?(book, name) -> {:error, @run_msg}
      ctor_of?(book, name) -> {:error, "ill-typed literal"}
      true -> {:error, "ill-typed literal"}
    end
  end

  defp slot_lit(_book, _val, _ty), do: {:error, "ill-typed literal"}

  defp ctor_lit(book, name, {:dat, dname, _}) do
    name = to_string(name)

    cond do
      ctor_of?(book, dname, name) -> :ok
      run?(book, name) -> {:error, @run_msg}
      ctor_of?(book, name) -> {:error, "ill-typed literal"}
      true -> {:error, "unknown constructor #{name}"}
    end
  end

  defp ctor_lit(book, name, _ty) do
    name = to_string(name)
    if run?(book, name), do: {:error, @run_msg}, else: {:error, "ill-typed literal"}
  end

  defp head_lit(_book, {:nat, n}) when is_integer(n), do: {:ok, {:nat, n}}
  defp head_lit(_book, :b0), do: {:ok, :b0}
  defp head_lit(_book, :b1), do: {:ok, :b1}
  defp head_lit(_book, :pick0), do: {:ok, :pick0}
  defp head_lit(_book, :pick1), do: {:ok, :pick1}

  defp head_lit(book, {:con, name}) do
    name = to_string(name)

    if ctor_of?(book, name),
      do: {:ok, {:con, name}},
      else: {:error, "unknown constructor #{name}"}
  end

  defp head_lit(book, {:var, name}) do
    name = to_string(name)

    cond do
      ctor_of?(book, name) -> {:ok, {:con, name}}
      run?(book, name) -> {:error, @run_msg}
      true -> {:error, "unknown constructor #{name}"}
    end
  end

  defp head_lit(_book, _val), do: {:error, "ill-typed literal"}

  defp ctor_of?(book, dname, name) do
    name = to_string(name)

    case Enum.find(book, &(&1[:kind] == :data and &1.name == dname)) do
      nil -> false
      %{ctors: ctors} -> Enum.any?(ctors, &(&1.name == name))
    end
  end

  defp ctor_of?(book, name) do
    name = to_string(name)

    Enum.any?(book, fn
      %{kind: :data, ctors: ctors} -> Enum.any?(ctors, &(&1.name == name))
      _ -> false
    end)
  end

  defp run?(book, name) do
    name = to_string(name)

    Enum.any?(book, fn d ->
      Map.get(d, :name) == name and Map.get(d, :mode) == :run and
        Map.get(d, :kind) not in [
          :data,
          :session,
          :conform,
          :place,
          :scheme,
          :move,
          :endpoint,
          :read,
          :meet,
          :talk,
          :repr,
          :seat,
          :link,
          :relay,
          :import,
          :param,
          :temporal
        ]
    end)
  end

  defp safety_msg(g, prop, steps, conf) do
    where =
      if steps == [] do
        ": #{dump(g, conf)}"
      else
        " after #{labels(g, steps)}: #{dump(g, conf)}"
      end

    "#{pp_formula({:always, prop})} fails in #{where_of(g)}#{where}"
  end

  defp live_msg(g, formula, to_c, stem, loop) do
    after_steps = if stem == [], do: to_c ++ loop, else: to_c ++ stem

    "#{pp_formula(formula)} fails in #{where_of(g)} after #{labels(g, after_steps)}; then forever: #{labels(g, loop)}"
  end

  defp where_of(g) do
    "#{g.meeting} (#{g.name_l} : #{g.session_l}, #{g.name_r} : #{g.session_r})"
  end

  defp labels(g, steps), do: Enum.map_join(steps, ", ", &step_label(g, &1))

  defp step_label(_g, {:fin, _src, _dest}), do: "the meeting has finished"

  defp step_label(g, {:lside, src, _dest}) do
    "#{g.name_l} #{act_label(g, Enum.at(g.code_l, il(src)), src, :l)}"
  end

  defp step_label(g, {:rside, src, _dest}) do
    "#{g.name_r} #{act_label(g, Enum.at(g.code_r, ir(src)), src, :r)}"
  end

  defp act_label(_g, %{k: :put, atom: atom}, _src, _side), do: "put #{atom_show(atom)}"

  defp act_label(g, %{k: :echo, slot: slot}, src, side) do
    case held(env(src, side), slot) do
      {:ok, k} -> "put #{atom_show(Enum.at(g.alpha, k))}"
      :no -> "put"
    end
  end

  defp act_label(g, %{k: :mget}, src, side) do
    case inbox(src, side) do
      [{:pay, k} | _] -> "arm #{atom_show(Enum.at(g.alpha, k))}"
      _ -> "arm"
    end
  end

  defp act_label(g, %{k: :iget}, src, side) do
    case inbox(src, side) do
      [{:pay, k} | _] ->
        case Enum.at(g.alpha, k) do
          {:bit, false} -> "arm b0"
          {:bit, true} -> "arm b1"
          _ -> "arm"
        end

      _ ->
        "arm"
    end
  end

  defp act_label(_g, %{k: :pick0}, _src, _side), do: "pick0"
  defp act_label(_g, %{k: :pick1}, _src, _side), do: "pick1"
  defp act_label(_g, %{k: :cover}, _src, _side), do: "cover"
  defp act_label(_g, %{show: show}, _src, _side), do: show
  defp act_label(_g, _, _src, _side), do: "?"

  defp dump(g, conf) do
    left = block_show(Enum.at(g.code_l, il(conf)))
    right = block_show(Enum.at(g.code_r, ir(conf)))

    "#{g.name_l}: #{left}; #{g.name_r}: #{right}; l2r: #{queue_show(g, l2r(conf))}; r2l: #{queue_show(g, r2l(conf))}"
  end

  defp block_show(%{show: show}), do: show
  defp block_show(_), do: "?"

  defp queue_show(_g, []), do: "[]"

  defp queue_show(g, toks) do
    "[#{Enum.map_join(toks, ", ", &tok_show(g, &1))}]"
  end

  defp tok_show(_g, {:lab, false}), do: "pick0"
  defp tok_show(_g, {:lab, true}), do: "pick1"
  defp tok_show(g, {:pay, k}), do: atom_show(Enum.at(g.alpha, k))

  defp atom_show({:nat, n}), do: Integer.to_string(n)
  defp atom_show({:bit, false}), do: "b0"
  defp atom_show({:bit, true}), do: "b1"
  defp atom_show({:con, name}), do: name
  defp atom_show(nil), do: "?"

  def pp_formula({:always, prop}), do: "always (#{pp_prop(prop)})"
  def pp_formula({:eventually, prop}), do: "eventually (#{pp_prop(prop)})"
  def pp_formula({:leads_to, p, q}), do: "(#{pp_prop(p)}) leads_to (#{pp_prop(q)})"

  def pp_prop(true), do: "true"
  def pp_prop(false), do: "false"
  def pp_prop({:not, p}), do: "not #{pp_prop(p)}"
  def pp_prop({:and, p, q}), do: "#{pp_prop(p)} and #{pp_prop(q)}"
  def pp_prop({:or, p, q}), do: "#{pp_prop(p)} or #{pp_prop(q)}"
  def pp_prop({:imp, p, q}), do: "#{pp_prop(p)} implies #{pp_prop(q)}"
  def pp_prop({:done, role}), do: "#{role} done"
  def pp_prop({:stopped, role}), do: "#{role} stopped"
  def pp_prop({:at, role, n, verb}), do: "#{role} at #{ordinal(n)} #{verb}"
  def pp_prop({:eq, role, name, val}), do: "#{role} has #{name} = #{pp_val(val)}"
  def pp_prop({:lt, role, name, n}), do: "#{role} has #{name} < #{n}"
  def pp_prop({:le, role, name, n}), do: "#{role} has #{name} ≤ #{n}"
  def pp_prop({:is, role, name, ctor}), do: "#{role} has #{name} is #{ctor}"
  def pp_prop({:eq2, r1, n1, r2, n2}), do: "#{r1} has #{n1} = #{r2} has #{n2}"
  def pp_prop({:bound, role, name}), do: "#{role} has #{name}"
  def pp_prop({:empty, role}), do: "inbox #{role} is empty"
  def pp_prop({:full, role}), do: "inbox #{role} is full"
  def pp_prop({:head, role, val}), do: "inbox #{role} head #{pp_val(val)}"

  defp pp_val({:nat, n}), do: Integer.to_string(n)
  defp pp_val(:b0), do: "b0"
  defp pp_val(:b1), do: "b1"
  defp pp_val(:pick0), do: "pick0"
  defp pp_val(:pick1), do: "pick1"
  defp pp_val({:con, name}), do: name
  defp pp_val({:var, name}), do: to_string(name)

  defp ordinal(1), do: "first"
  defp ordinal(2), do: "second"
  defp ordinal(3), do: "third"
  defp ordinal(n), do: "#{n}#{ord_suf(n)}"

  defp ord_suf(n) when rem(n, 100) in 11..13, do: "th"

  defp ord_suf(n) do
    case rem(n, 10) do
      1 -> "st"
      2 -> "nd"
      3 -> "rd"
      _ -> "th"
    end
  end

  defp block_kind(g, :l, conf), do: kind_of(Enum.at(g.code_l, il(conf)))
  defp block_kind(g, :r, conf), do: kind_of(Enum.at(g.code_r, ir(conf)))
  defp kind_of(%{k: k}), do: k
  defp kind_of(_), do: nil

  defp ptr(conf, :l), do: il(conf)
  defp ptr(conf, :r), do: ir(conf)
  defp il({i, _, _, _, _, _}), do: i
  defp ir({_, i, _, _, _, _}), do: i
  defp l2r({_, _, q, _, _, _}), do: q
  defp r2l({_, _, _, q, _, _}), do: q
  defp env(conf, :l), do: el(conf)
  defp env(conf, :r), do: er(conf)
  defp el({_, _, _, _, e, _}), do: e
  defp er({_, _, _, _, _, e}), do: e
  defp inbox(conf, :l), do: r2l(conf)
  defp inbox(conf, :r), do: l2r(conf)

  defp held(env, slot) do
    case Enum.at(env, slot) do
      n when is_integer(n) and n > 0 -> {:ok, n - 1}
      _ -> :no
    end
  end

  defp nat_held(g, env, slot) do
    case held(env, slot) do
      {:ok, k} ->
        case Enum.at(g.alpha, k) do
          {:nat, n} -> {:ok, n}
          _ -> :no
        end

      :no ->
        :no
    end
  end

  defp match_lit(g, k, lit) do
    case {Enum.at(g.alpha, k), lit} do
      {{:nat, n}, {:nat, n}} -> true
      {{:bit, false}, :b0} -> true
      {{:bit, true}, :b1} -> true
      {{:con, name}, {:con, name}} -> true
      _ -> false
    end
  end

  defp match_tok(_g, {:lab, false}, :pick0), do: true
  defp match_tok(_g, {:lab, true}, :pick1), do: true
  defp match_tok(g, {:pay, k}, lit), do: match_lit(g, k, lit)
  defp match_tok(_g, _tok, _lit), do: false
end

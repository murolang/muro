defmodule Muro.Temporal do
  @moduledoc """
  Decides `always`, `eventually`, and `leads_to` on the reachable
  configurations of one buffered meeting.

  | Elixir | Agda |
  | --- | --- |
  | `reachable/1` | `Muro.Temporal.Graph.reachable` |
  | `levels/4` | the breadth-first loop inside `reachable` |
  | `decide_nostuck/2` | `Muro.Temporal.Graph.decide-nostuck` |
  | `worklist/2` | `Muro.Temporal.Live.prune` (`firstZero` / `outs`) |
  | `lasso/3` | `Muro.Temporal.Live.loop-of` (`tour-of`, `walkC`, `cutC`) |
  | `check/4` | `Muro.Temporal.Decide.check` |
  | `holds?/3` | `Muro.Temporal.⟦_⟧` |

  The search records a parent for every configuration it enqueues, so the
  path it reports is the breadth-first one. Liveness pops the first
  configuration in list order whose surviving successors are empty.
  `lasso` always takes the first successor that is still in the surviving
  set. A finished configuration stutters, so it is not popped.
  """

  alias Muro.Temporal.{Compile, Elab, Graph}

  @run_msg "temporal formulas do not mention run definitions"

  @doc """
  `{:ok, count}` when the formula holds, `count` the number of reachable
  configurations. `{:error, message}` when it does not, or the meeting is
  out of scope. The message has no location and no declaration name.
  """
  def judge(book, %{meeting: meeting, formula: formula}, fuel \\ nil) when is_list(book) do
    fuel = fuel || Muro.Check.default_fuel()

    with {:ok, meet} <- fetch_meet(book, meeting),
         :ok <- meeting_checks(book, meet, fuel),
         :ok <- needs_buffer(meet),
         {:ok, g} <- build(book, meet),
         {cs, parents} = reachable(g),
         :ok <- nostuck(g, cs),
         {:ok, formulas} <- expand(book, g, formula) do
      case Enum.find_value(formulas, fn f ->
             case check(g, parents, cs, f) do
               :yes -> nil
               {:no, msg} -> {:no, msg}
             end
           end) do
        nil -> {:ok, length(cs)}
        {:no, msg} -> {:error, msg}
      end
    end
  end

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
  Transcribes `Live.prune`. The region is a list; membership is equality.
  """
  def worklist(g, region) do
    case first_zero(g, region, region) do
      nil -> region
      conf -> worklist(g, List.delete(region, conf))
    end
  end

  @doc """
  Transcribes `Live.firstZero`.
  """
  def first_zero(g, region, []), do: first_zero_end(g, region)

  def first_zero(g, region, [conf | rest]) do
    if Graph.outs(g, region, conf) == [] do
      conf
    else
      first_zero(g, region, rest)
    end
  end

  defp first_zero_end(_g, _region), do: nil

  @doc """
  Transcribes `Live.loop-of`. `{stem, loop}` are steps `{who, src, dest}`.
  `leads_to` puts the breadth-first parent trace in front of that pair.
  """
  def lasso(g, z, conf) do
    walk(g, MapSet.new(z), conf, MapSet.new(), conf, [])
  end

  @doc """
  Transcribes `Decide.check` for one elaborated formula.
  `formula` is `%{kind: :always | :eventually | :leads_to, src: ast, prop: resolved}`.
  """
  def check(g, parents, confs, %{kind: :always, src: src, prop: prop}) do
    case Enum.find(confs, fn conf -> not holds?(g, prop, conf) end) do
      nil -> :yes
      conf -> {:no, safety_msg(g, src, trace(parents, conf), conf)}
    end
  end

  def check(g, _parents, confs, %{kind: :eventually, src: src, prop: prop}) do
    region = Enum.filter(confs, fn conf -> not holds?(g, prop, conf) end)
    z = worklist(g, region)

    if Enum.member?(z, Graph.init(g)) do
      {stem, loop} = lasso(g, z, Graph.init(g))
      {:no, live_msg(g, {:eventually, src}, [], stem, loop)}
    else
      :yes
    end
  end

  def check(g, parents, confs, %{kind: :leads_to, src: {p, q}, prop: {rp, rq}}) do
    region = Enum.filter(confs, fn conf -> not holds?(g, rq, conf) end)
    z = worklist(g, region)

    case Enum.find(confs, fn conf -> holds?(g, rp, conf) and Enum.member?(z, conf) end) do
      nil ->
        :yes

      conf ->
        {stem, loop} = lasso(g, z, conf)
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

  defp enqueue(_g, _conf, [], queue, seen, parents), do: {queue, seen, parents}

  defp enqueue(g, conf, [{who, dest} | rest], queue, seen, parents) do
    if MapSet.member?(seen, dest) do
      enqueue(g, conf, rest, queue, seen, parents)
    else
      enqueue(
        g,
        conf,
        rest,
        queue ++ [dest],
        MapSet.put(seen, dest),
        Map.put(parents, dest, {who, conf})
      )
    end
  end

  @doc """
  One frontier of `reachable`. The queue is popped from the front and new
  configurations are appended, left successor before right.
  """
  def levels(g, queue, seen, parents), do: levels(g, queue, seen, parents, [])

  def levels(g, queue, seen, parents, acc) do
    case queue do
      [] ->
        {Enum.reverse(acc), parents}

      [conf | rest] ->
        {rest, seen, parents} = enqueue(g, conf, Graph.steps_of(g, conf), rest, seen, parents)
        levels(g, rest, seen, parents, [conf | acc])
    end
  end

  @doc """
  Transcribes `Graph.reachable`. Returns the configurations in discovery
  order and the parent map (`child => {who, parent}`).
  """
  def reachable(g) do
    start = Graph.init(g)
    levels(g, [start], MapSet.new([start]), %{}, [])
  end

  defp walk(g, zset, conf, seen, origin, steps) do
    if MapSet.member?(seen, conf) do
      cut(conf, origin, steps)
    else
      case Graph.outs(g, zset, conf) do
        [{who, dest} | _] ->
          walk(g, zset, dest, MapSet.put(seen, conf), origin, steps ++ [{who, conf, dest}])

        [] ->
          {[], []}
      end
    end
  end

  defp cut(target, pos, steps) when target == pos, do: {[], steps}
  defp cut(_target, _pos, []), do: {[], []}

  defp cut(target, _pos, [{_who, _src, dest} = step | rest]) do
    {stem, loop} = cut(target, dest, rest)
    {[step | stem], loop}
  end

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

  defp meeting_checks(book, meet, fuel) do
    case Muro.Check.check_def(book, meet, fuel) do
      :ok -> :ok
      {:error, _} -> {:error, "skipped because #{meet.name} does not check"}
      {:note, _} -> :ok
    end
  end

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

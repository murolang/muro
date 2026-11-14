defmodule Muro.Temporal.Graph do
  @moduledoc """
  One step of a buffered meeting over the compiled block table.

  | Elixir | Agda |
  | --- | --- |
  | `init/1` | `Muro.AsyncRec.init` |
  | `react_l/2`, `react_r/2` | `Muro.AsyncRec.reactL`, `reactR` |
  | `view/2` | `Muro.AsyncRec.view` |
  | `halted/2` | `Muro.AsyncRec.halted` |
  | `edges/2` | `Muro.Temporal.edges` |
  | `steps_of/2` | the real successors of `edges` (`Muro.Temporal.real`) |

  Left is tried before right, the order `merge` uses. The stutter edge is
  last among those three, and only at a finished configuration. `steps_of`
  drops it: the breadth-first search does not follow a configuration to
  itself.

  A meeting that marks a party `may fail` appends death and drop edges
  after that list. Death is only while that party has not halted: a
  party at `done` or `stop` has no death edge, and a party that is
  already dead has no second one. A meeting that does not mark one
  appends nothing, and this module stays the transcription of the Agda
  development, which has no failure.
  """

  @doc """
  Transcribes `AsyncRec.init`.
  """
  def init(g) do
    {g.entry_l, g.entry_r, [], [], zeros(g.slots_l), zeros(g.slots_r)}
  end

  @doc """
  Transcribes `AsyncRec.reactL`.
  """
  def react_l(g, conf) do
    if dead?(il(conf)), do: :wait, else: react(g, conf, Enum.at(g.code_l, il(conf)), :l)
  end

  @doc """
  Transcribes `AsyncRec.reactR`.
  """
  def react_r(g, conf) do
    if dead?(ir(conf)), do: :wait, else: react(g, conf, Enum.at(g.code_r, ir(conf)), :r)
  end

  @doc """
  Transcribes `AsyncRec.view`. A bad view that still has a death or a
  drop is that step: the configuration is not stuck.
  """
  def view(g, conf) do
    case merge(g, conf, react_l(g, conf), react_r(g, conf)) do
      {:bad, _} = bad ->
        case extra(g, conf) do
          [] -> bad
          [{_, dest} | rest] -> {:go, dest, Enum.map(rest, &elem(&1, 1))}
        end

      other ->
        other
    end
  end

  @doc """
  Transcribes `AsyncRec.halted`. A party that has stopped early is halted.
  """
  def halted(g, conf) do
    side_halt(g.code_l, il(conf)) and side_halt(g.code_r, ir(conf))
  end

  @doc """
  Transcribes `Muro.Temporal.edges`. Left, then right, then the stutter.
  Death and drop follow, and only when the meeting asked for them.
  """
  def edges(g, conf) do
    from(react_l(g, conf), :lside) ++
      from(react_r(g, conf), :rside) ++
      stutter(g, conf) ++
      extra(g, conf)
  end

  @doc """
  Successors the search follows. A bad view contributes none. A finished
  configuration contributes none here; `edges` keeps its stutter.
  """
  def steps_of(g, conf) do
    left = react_l(g, conf)
    right = react_r(g, conf)

    if bad?(left) or bad?(right) do
      []
    else
      from(left, :lside) ++ from(right, :rside) ++ extra(g, conf)
    end
  end

  @doc """
  Transcribes `Muro.Temporal.Live.outs`: edges whose target is still in
  the region, in edge order, duplicates kept.
  """
  def outs(g, region, conf) when is_struct(region, MapSet) do
    Enum.filter(edges(g, conf), fn {_who, dest} -> MapSet.member?(region, dest) end)
  end

  # One membership set for this call. A scan must pass the set it already
  # holds. Pruning does not call this per configuration: it keeps the set,
  # the predecessor lists, and the out-degrees (`Muro.Temporal.prune/2`).
  def outs(g, region, conf) when is_list(region) do
    outs(g, MapSet.new(region), conf)
  end

  defp react(_g, _conf, nil, _side), do: :wait
  defp react(_g, _conf, %{k: :done}, _side), do: :wait
  defp react(_g, _conf, %{k: :stop}, _side), do: :wait

  defp react(g, conf, %{k: :put, atom: atom, cont: i}, side) do
    case find_a(atom, g.alpha) do
      nil -> {:bad, :unbounded}
      k -> enq(g, conf, {:pay, k}, i, side)
    end
  end

  defp react(g, conf, %{k: :echo, slot: slot, cont: i}, side) do
    case slot_val(env(conf, side), slot) do
      nil -> :wait
      k -> enq(g, conf, {:pay, k}, i, side)
    end
  end

  defp react(g, conf, %{k: :pick0, cont: i}, side), do: enq(g, conf, {:lab, false}, i, side)
  defp react(g, conf, %{k: :pick1, cont: i}, side), do: enq(g, conf, {:lab, true}, i, side)

  defp react(g, conf, %{k: :get, tag: tag, slot: slot, cont: i} = blk, side) do
    case on_get(g, conf, tag, slot, i, side) do
      :wait -> maybe_fail(g, conf, blk, side)
      other -> other
    end
  end

  defp react(g, conf, %{k: :cover, c0: i, c1: j} = blk, side) do
    case on_cover(g, conf, i, j, side) do
      :wait -> maybe_fail(g, conf, blk, side)
      other -> other
    end
  end

  defp react(g, conf, %{k: :iget, slot: slot, c0: i, c1: j} = blk, side) do
    case on_iget(g, conf, slot, i, j, side) do
      :wait -> maybe_fail(g, conf, blk, side)
      other -> other
    end
  end

  defp react(g, conf, %{k: :mget, tag: tag, slot: slot, arms: arms} = blk, side) do
    case on_mget(g, conf, tag, slot, arms, side) do
      :wait -> maybe_fail(g, conf, blk, side)
      other -> other
    end
  end

  defp on_get(g, conf, tag, slot, i, side) do
    case inbox(conf, side) do
      [] ->
        :wait

      [{:lab, _} | _] ->
        {:bad, recv(side)}

      [{:pay, k} | rest] ->
        case Enum.at(g.alpha, k) do
          nil ->
            {:bad, recv(side)}

          atom ->
            if fits?(tag, atom) do
              {:go, jump(conf, i, rest, set_nth(slot, k + 1, env(conf, side)), side)}
            else
              {:bad, recv(side)}
            end
        end
    end
  end

  defp on_cover(_g, conf, i, j, side) do
    case inbox(conf, side) do
      [] -> :wait
      [{:pay, _} | _] -> {:bad, recv(side)}
      [{:lab, false} | rest] -> {:go, jump(conf, i, rest, env(conf, side), side)}
      [{:lab, true} | rest] -> {:go, jump(conf, j, rest, env(conf, side), side)}
    end
  end

  defp on_iget(g, conf, slot, i, j, side) do
    case inbox(conf, side) do
      [] ->
        :wait

      [{:lab, _} | _] ->
        {:bad, recv(side)}

      [{:pay, k} | rest] ->
        case Enum.at(g.alpha, k) do
          {:bit, false} ->
            {:go, jump(conf, i, rest, set_nth(slot, k + 1, env(conf, side)), side)}

          {:bit, true} ->
            {:go, jump(conf, j, rest, set_nth(slot, k + 1, env(conf, side)), side)}

          _ ->
            {:bad, recv(side)}
        end
    end
  end

  defp on_mget(g, conf, tag, slot, arms, side) do
    case inbox(conf, side) do
      [] ->
        :wait

      [{:lab, _} | _] ->
        {:bad, recv(side)}

      [{:pay, k} | rest] ->
        case Enum.at(g.alpha, k) do
          nil ->
            {:bad, recv(side)}

          atom ->
            with true <- fits?(tag, atom),
                 {:con, cname} <- atom,
                 {:ok, j} <- arm_to(cname, arms) do
              {:go, jump(conf, j, rest, set_nth(slot, k + 1, env(conf, side)), side)}
            else
              _ -> {:bad, recv(side)}
            end
        end
    end
  end

  defp merge(_g, _conf, {:bad, fault}, _right), do: {:bad, fault}
  defp merge(_g, _conf, {:go, _}, {:bad, fault}), do: {:bad, fault}
  defp merge(_g, _conf, :wait, {:bad, fault}), do: {:bad, fault}
  defp merge(_g, _conf, {:go, c1}, {:go, c2}), do: {:go, c1, [c2]}
  defp merge(_g, _conf, {:go, c1}, :wait), do: {:go, c1, []}
  defp merge(_g, _conf, :wait, {:go, c2}), do: {:go, c2, []}

  defp merge(g, conf, :wait, :wait) do
    lq = l2r(conf)
    rq = r2l(conf)

    cond do
      lq == [] and rq == [] and halted(g, conf) -> :final
      halted(g, conf) -> {:bad, :orphan}
      true -> {:bad, :dead}
    end
  end

  defp stutter(g, conf) do
    if l2r(conf) == [] and r2l(conf) == [] and halted(g, conf) do
      [{:fin, conf}]
    else
      []
    end
  end

  defp from({:go, dest}, who), do: [{who, dest}]
  defp from(_, _), do: []

  defp bad?({:bad, _}), do: true
  defp bad?(_), do: false

  # A send to a party that has already stopped is consumed and not queued.
  defp enq(g, conf, tok, i, side) do
    if dead?(ptr(conf, other(side))) do
      {:go, set_ptr(conf, i, side)}
    else
      queue = outbox(conf, side)

      if length(queue) < g.cap do
        {:go, set_ptr(set_out(conf, snoc(queue, tok), side), i, side)}
      else
        :wait
      end
    end
  end

  # The failure arm fires only once the peer has stopped and this inbox
  # is empty. A message still queued can be taken or dropped first.
  defp maybe_fail(_g, conf, blk, side) do
    fail = Map.get(blk, :fail)

    if dead?(ptr(conf, other(side))) and is_integer(fail) do
      {:go, set_ptr(conf, fail, side)}
    else
      :wait
    end
  end

  defp extra(g, conf), do: death_edges(g, conf) ++ drop_edges(g, conf)

  defp death_edges(g, conf), do: die(g, conf, :l) ++ die(g, conf, :r)

  # A marked party dies only while it has not halted. `done` and `stop`
  # stay where they are. A party that is already dead has no second death.
  defp die(g, conf, side) do
    i = ptr(conf, side)

    if may?(g, side) and not dead?(i) and not side_halt(code_of(g, side), i) do
      [{die_tag(side), set_ptr(conf, :dead, side)}]
    else
      []
    end
  end

  defp code_of(g, :l), do: g.code_l
  defp code_of(g, :r), do: g.code_r

  # The head of a queue is dropped once either end of that queue has
  # stopped. Toward the survivor that is one run beside delivery. Toward
  # the party that stopped, the message will not be read.
  defp drop_edges(_g, conf), do: drop_q(conf, :l) ++ drop_q(conf, :r)

  defp drop_q(conf, side) do
    q = outbox(conf, side)

    if q != [] and (dead?(ptr(conf, side)) or dead?(ptr(conf, other(side)))) do
      [{drop_tag(side), set_out(conf, tl(q), side)}]
    else
      []
    end
  end

  defp may?(g, :l), do: Map.get(g, :may_l, false)
  defp may?(g, :r), do: Map.get(g, :may_r, false)
  defp ptr(conf, :l), do: il(conf)
  defp ptr(conf, :r), do: ir(conf)
  defp other(:l), do: :r
  defp other(:r), do: :l
  defp die_tag(:l), do: :ldie
  defp die_tag(:r), do: :rdie
  defp drop_tag(:l), do: :ldrop
  defp drop_tag(:r), do: :rdrop
  defp dead?(:dead), do: true
  defp dead?(_), do: false

  defp side_halt(_code, :dead), do: true
  defp side_halt(code, i), do: halt?(Enum.at(code, i))

  defp jump(conf, i, rest, env, side) do
    conf
    |> set_in(rest, side)
    |> set_env(env, side)
    |> set_ptr(i, side)
  end

  defp il({i, _, _, _, _, _}), do: i
  defp ir({_, i, _, _, _, _}), do: i
  defp l2r({_, _, q, _, _, _}), do: q
  defp r2l({_, _, _, q, _, _}), do: q

  # Left reads r2l and writes l2r. Right reads l2r and writes r2l.
  defp inbox(conf, :l), do: r2l(conf)
  defp inbox(conf, :r), do: l2r(conf)
  defp outbox(conf, :l), do: l2r(conf)
  defp outbox(conf, :r), do: r2l(conf)
  defp env(conf, :l), do: el(conf)
  defp env(conf, :r), do: er(conf)
  defp el({_, _, _, _, e, _}), do: e
  defp er({_, _, _, _, _, e}), do: e

  defp set_ptr({_il, ir, l2r, r2l, el, er}, i, :l), do: {i, ir, l2r, r2l, el, er}
  defp set_ptr({il, _ir, l2r, r2l, el, er}, i, :r), do: {il, i, l2r, r2l, el, er}

  defp set_out({il, ir, _l2r, r2l, el, er}, q, :l), do: {il, ir, q, r2l, el, er}
  defp set_out({il, ir, l2r, _r2l, el, er}, q, :r), do: {il, ir, l2r, q, el, er}

  defp set_in({il, ir, l2r, _r2l, el, er}, q, :l), do: {il, ir, l2r, q, el, er}
  defp set_in({il, ir, _l2r, r2l, el, er}, q, :r), do: {il, ir, q, r2l, el, er}

  defp set_env({il, ir, l2r, r2l, _el, er}, e, :l), do: {il, ir, l2r, r2l, e, er}
  defp set_env({il, ir, l2r, r2l, el, _er}, e, :r), do: {il, ir, l2r, r2l, el, e}

  defp recv(:l), do: :recv_l
  defp recv(:r), do: :recv_r

  defp halt?(%{k: k}) when k in [:done, :stop], do: true
  defp halt?(_), do: false

  defp fits?(:nat, {:nat, _}), do: true
  defp fits?(:bit, {:bit, _}), do: true
  defp fits?({:dat, _}, {:con, _}), do: true
  defp fits?(_, _), do: false

  defp arm_to(_name, []), do: :miss
  defp arm_to(name, [{name, j} | _]), do: {:ok, j}
  defp arm_to(name, [_ | rest]), do: arm_to(name, rest)

  defp slot_val(env, slot) do
    case Enum.at(env, slot) do
      n when is_integer(n) and n > 0 -> n - 1
      _ -> nil
    end
  end

  defp set_nth(0, v, [_ | rest]), do: [v | rest]
  defp set_nth(n, v, [x | rest]) when n > 0, do: [x | set_nth(n - 1, v, rest)]
  defp set_nth(_n, _v, []), do: []

  defp snoc([], tok), do: [tok]
  defp snoc([x | xs], tok), do: [x | snoc(xs, tok)]

  defp zeros(0), do: []
  defp zeros(n) when n > 0, do: [0 | zeros(n - 1)]

  defp find_a(atom, alpha), do: find_go(0, atom, alpha)
  defp find_go(_i, _atom, []), do: nil

  defp find_go(i, atom, [x | xs]) do
    if atom_eq?(atom, x), do: i, else: find_go(i + 1, atom, xs)
  end

  defp atom_eq?({:nat, m}, {:nat, n}), do: m == n
  defp atom_eq?({:bit, a}, {:bit, b}), do: a == b
  defp atom_eq?({:con, a}, {:con, b}), do: a == b
  defp atom_eq?(_, _), do: false
end

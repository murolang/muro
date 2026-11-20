defmodule Muro.Family.Step do
  @moduledoc """
  The keyed-family step, for any number of keys and any number of instances.

  This is the executable image of `agda/Muro/Family.agda`. It is written
  against those definitions. It is not extracted from them. The names
  below are the Agda names.

  `proved_rules/0` is `holdOf` for the kind this file started with:
  `init` is `never`, `signal` is `earlier`. `hold_of/2` reads a family's
  rules. `:any` is Agda `many`: held while any other row of the key is
  open. `blocked?/3` is `earlierBlocked?`. `any_blocked?/3` is
  `anyBlocked?`. `decide/5` is `decide` for `never` and `earlier`, and
  `decideMode` when the hold is `any`. `on_key/2` is `onKey`.
  `arrive/5` is `arriveTo` and `arriveMode`. `resolve/3` is `resolveTo`
  and `resolveMode`. `withdraw/3` is `withdrawTo`: a held row leaves and
  the release is the release of `resolveMode`. `touch/2` is `touchTo`
  and `touchMode`. `rerun/2` and `meet/2` are that same transition.
  `apply` in Agda sends `Act.arrive key index kind` to `arriveTo state
  key kind index`, and `withdrawR` to `withdrawTo`.

  `no_overtake?/2` is `NoOvertake`. `bad_open?/2` is `BadOpen`. An opened
  signal is a violation when an earlier live row of its key was already
  born at the tick the signal opened (`born ≤ openedAt`). A row that
  arrives later has a greater birth tick and is not a violation.
  `held_blocked?/1` is `HeldBlocked`. It is the earlier-only fact: every
  held row has a smaller live index. A held `any` row need not.
  `least_earlier/2` is `pick` on `Earlier`. `at_most_one_any?/2` is
  `AtMostOne`. `earlier_resolved?/3` is `EarlierResolved`: an opened
  row of that key and kind has no earlier live row of the same key and
  kind whose birth is at most its open tick. The opening row is not
  earlier than itself. A row that arrives later does not refute it.
  It holds for `earlier` and for `any`. It does not hold for `never`.
  `invariant?/2` is `RulesInv`: distinct ids, distinct key-and-index
  pairs, ids below `next`, birth and open ticks below `tick`, a held
  row is `earlier` or `any`, a held `earlier` row has an earlier live
  row, a held `any` row has another open row of its key, `AtMostOne`,
  `NoOvertake`, and `ResolvedAny`.

  `script_a/0` is `script-a`: `init` at 0, `signal` at 1, `signal` at 2.
  `script_b/0` is `script-b`: `init` at 0.

  The phase `:open` is Agda `opened`. `:held` is `held`. `born` is
  `bornOf`. `opened_at` is `openedAtOf`. The dispatcher does not store
  the tick. Those fields live only here.

  `replay/2` is the family relation alone. `check_trace` also requires
  a rerun, and a resolve that has started a session, to land on `done`.
  That session condition is not `touchTo`.

  `open_all` is `openAll` / `opens?`. A held `earlier` row of the
  released key opens when `earlierBlocked?` is false. A held `any` row
  opens only when no row of the key is open, no `earlier` row of the
  key opens in that same release, and no smaller `{index, id}` `any`
  row is also free. The released list is sorted by `{index, id}`,
  which is the list the dispatcher returns. Agda `openAll` keeps list
  order. Membership is the same. On a family whose holds are `never`
  and `earlier` only, that release is every unblocked held `earlier`
  row.

  The meeting graph, one retry then give-up, `fail stop`, and the
  program that writes the dispatcher are not this module.
  """

  @doc """
  `holdOf` for the proved kind. `init` is `never`. `signal` is `earlier`.
  """
  def proved_rules, do: %{init: :never, signal: :earlier}

  @doc "Agda `empty`."
  def empty, do: %{next: 0, tick: 0, rows: []}

  @doc """
  `holdOf` read from a family's rules. An unknown kind is the
  dispatcher's `{:kind, kind}`.
  """
  def hold_of(rules, kind) do
    case Map.fetch(rules, kind) do
      {:ok, hold} when hold in [:never, :earlier, :any] -> {:ok, hold}
      _ -> {:error, {:kind, kind}}
    end
  end

  @doc """
  Agda `earlierBlocked?`. True when a live row of `key` has a creation
  index strictly below `index`. A resolved instance is not in `rows`.
  """
  def blocked?(rows, key, index) do
    Enum.any?(rows, fn row -> row.key == key and row.index < index end)
  end

  @doc """
  Agda `anyBlocked?`. True when a row of `key` other than `index` is
  open. A held row is not open, so a held subject does not block
  itself. On arrival the new row is not in `rows`.
  """
  def any_blocked?(rows, key, index) do
    Enum.any?(rows, fn row ->
      row.key == key and row.index != index and row.phase == :open
    end)
  end

  @doc """
  Agda `decide` and `decideMode`. `never` opens. `earlier` holds when
  `earlierBlocked?` is true. `any` holds when `anyBlocked?` is true.
  The phase `:open` is Agda `opened`.
  """
  def decide(rows, key, index, kind, rules) do
    {:ok, hold} = hold_of(rules, kind)
    assign(hold, rows, key, index)
  end

  @doc "Agda `onKey`."
  def on_key(rows, key), do: Enum.filter(rows, &(&1.key == key))

  @doc "Agda `fresh?`."
  def fresh?(rows, key, index) do
    not Enum.any?(rows, fn row -> row.key == key and row.index == index end)
  end

  @doc """
  Agda `arriveTo`. The new row's `born` and `opened_at` are the current
  tick, then the tick advances. `decide` reads the rows from before
  the arrival.
  """
  def arrive(state, key, kind, index, rules) do
    with :ok <- index_ok(index),
         {:ok, _hold} <- hold_of(rules, kind) do
      if fresh?(state.rows, key, index) do
        phase = decide(state.rows, key, index, kind, rules)
        id = state.next

        row = %{
          key: key,
          index: index,
          id: id,
          born: state.tick,
          opened_at: state.tick,
          kind: kind,
          phase: phase
        }

        state = %{
          state
          | next: id + 1,
            tick: state.tick + 1,
            rows: [row | state.rows]
        }

        {:ok, phase, id, state}
      else
        {:error, {:duplicate, key, index}}
      end
    end
  end

  @doc """
  Agda `resolveTo` and `resolveMode`. An opened row leaves. `openAll`
  stamps the rows that release, then the tick advances. A held id is
  `{:held, id}`. An id that is not live is `{:unknown, id}`, including
  an id that has already left.
  """
  def resolve(state, id, rules) do
    case find(state.rows, id) do
      nil ->
        {:error, {:unknown, id}}

      %{phase: :held} ->
        {:error, {:held, id}}

      %{phase: :open, key: key} ->
        release(state, id, key, rules)
    end
  end

  @doc """
  Agda `withdrawTo`. A held row leaves and `openAll` runs, the same
  release as `resolveMode`. An open id is `{:opened, id}`. An id below
  `next` that is not live has left: `{:resolved, id}`. Any other
  missing id is `{:unknown, id}`.
  """
  def withdraw(state, id, rules) do
    case find(state.rows, id) do
      %{phase: :open} ->
        {:error, {:opened, id}}

      %{phase: :held, key: key} ->
        release(state, id, key, rules)

      nil ->
        if left?(state, id), do: {:error, {:resolved, id}}, else: {:error, {:unknown, id}}
    end
  end

  @doc "Agda `touchTo`. `rerun` leaves an opened row as it is."
  def rerun(state, id), do: touch(state, id)

  @doc "Agda `touchTo`. `meet` is the same family transition as `rerun`."
  def meet(state, id), do: touch(state, id)

  @doc """
  Agda `touchTo`. The row must be opened. The state that comes back is
  the state that went in, and the released list is empty.
  """
  def touch(state, id) do
    case find(state.rows, id) do
      nil -> {:error, {:unknown, id}}
      %{phase: :held} -> {:error, {:held, id}}
      %{phase: :open} -> {:ok, [], state}
    end
  end

  @doc "The dispatcher's `live` classification. `:open` is Agda `opened`."
  def live(state, id) do
    case find(state.rows, id) do
      nil -> {:error, {:unknown, id}}
      row -> {:ok, row.phase, row.key, row.kind}
    end
  end

  @doc """
  Agda `pick` on `Earlier`: the live row of this key with the least
  creation index strictly below `row`. `nil` when none is live.
  """
  def least_earlier(rows, row) do
    case Enum.filter(rows, fn other -> other.key == row.key and other.index < row.index end) do
      [] -> nil
      earlier -> Enum.min_by(earlier, & &1.index)
    end
  end

  @doc "Rows as `{key, index, id, kind, phase}`, sorted. The tick is omitted."
  def view(rows) when is_list(rows) do
    rows
    |> Enum.map(fn row -> {row.key, row.index, row.id, row.kind, row.phase} end)
    |> Enum.sort()
  end

  def view(%{rows: rows}), do: view(rows)

  @doc "The same projection of a generated dispatcher state."
  def view_disp(%{by: by}) do
    for {key, rows} <- by,
        {index, {id, kind, phase}} <- rows do
      {key, index, id, kind, phase}
    end
    |> Enum.sort()
  end

  @doc """
  Agda `BadOpen`. An opened signal, and an earlier live row of its key
  whose birth tick is at most the signal's open tick.
  """
  def bad_open?(rows, rules) do
    Enum.any?(rows, fn opened ->
      signal?(rules, opened) and opened.phase == :open and
        Enum.any?(rows, fn earlier ->
          earlier.key == opened.key and earlier.index < opened.index and
            earlier.born <= opened.opened_at
        end)
    end)
  end

  @doc "Agda `NoOvertake` and `NoOvertakeR`, the negation of `BadOpen`."
  def no_overtake?(rows, rules), do: not bad_open?(rows, rules)

  @doc """
  Agda `AtMostOne`. At most one opened row whose hold is `any` for
  each key.
  """
  def at_most_one_any?(rows, rules) do
    rows
    |> Enum.filter(&(&1.phase == :open and any?(rules, &1)))
    |> Enum.group_by(& &1.key)
    |> Enum.all?(fn {_key, group} -> length(group) <= 1 end)
  end

  @doc """
  Agda `EarlierResolved`. For every opened row of `key` and `kind`,
  no earlier live row of that same key and kind was born at or before
  the open tick. Vacuous when nothing of that key and kind is open.
  """
  def earlier_resolved?(rows, key, kind) do
    Enum.all?(rows, fn opened ->
      opened.key != key or opened.kind != kind or opened.phase != :open or
        not Enum.any?(rows, fn earlier ->
          earlier.key == key and earlier.kind == kind and earlier.index < opened.index and
            earlier.born <= opened.opened_at
        end)
    end)
  end

  @doc """
  Agda `HeldBlocked`. Every held row has an earlier live row of its key.
  """
  def held_blocked?(rows) do
    Enum.all?(rows, fn row ->
      row.phase != :held or
        Enum.any?(rows, fn earlier -> earlier.key == row.key and earlier.index < row.index end)
    end)
  end

  @doc """
  Agda `RulesInv`. The earlier-only fields are `Invariant`. A held row
  is `earlier` or `any`. `HeldEarlier`, `HeldAny`, `AtMostOne`,
  `NoOvertake`, and `ResolvedAny` are the rest. `HeldBlocked` stays
  `held_blocked?/1` and is not required once a kind is `any`.
  """
  def invariant?(state, rules) do
    rows = state.rows

    unique_ids?(rows) and unique_index?(rows) and ids_below?(rows, state.next) and
      clock?(rows, state.tick) and held_mode?(rows, rules) and held_earlier?(rows, rules) and
      held_any?(rows, rules) and at_most_one_any?(rows, rules) and no_overtake?(rows, rules) and
      resolved_any?(rows, rules)
  end

  @doc """
  Agda `script-a`. Key `a` of the family graph: `init` at 0, `signal`
  at 1, `signal` at 2.
  """
  def script_a, do: [{:init, 0}, {:signal, 1}, {:signal, 2}]

  @doc "Agda `script-b`. Key `b` of the family graph: one `init` at 0."
  def script_b, do: [{:init, 0}]

  @doc """
  Family steps only: `arriveTo`, `resolveTo`, `withdrawTo`, and `touchTo`.

  `{:rerun, id}` succeeds here whenever the row is opened. `check_trace`
  also requires the id's sessions to be at `done`. That extra refusal
  is not this function. `{:meet, id}` is `touchTo` as well.
  """
  def replay(rules, trace, state \\ empty()) do
    Enum.reduce_while(Enum.with_index(trace), {:ok, state}, fn {act, i}, {:ok, st} ->
      case family_act(st, act, rules) do
        {:ok, st} -> {:cont, {:ok, st}}
        {:error, reason} -> {:halt, {:error, {i, reason}}}
      end
    end)
  end

  defp family_act(state, {:arrive, key, kind, index}, rules) do
    case arrive(state, key, kind, index, rules) do
      {:ok, _phase, _id, state} -> {:ok, state}
      {:error, reason} -> {:error, reason}
    end
  end

  defp family_act(state, {:resolved, id}, rules) do
    case resolve(state, id, rules) do
      {:ok, _released, state} -> {:ok, state}
      {:error, reason} -> {:error, reason}
    end
  end

  defp family_act(state, {:withdraw, id}, rules) do
    case withdraw(state, id, rules) do
      {:ok, _released, state} -> {:ok, state}
      {:error, reason} -> {:error, reason}
    end
  end

  defp family_act(state, {:rerun, id}, _rules) do
    case rerun(state, id) do
      {:ok, [], state} -> {:ok, state}
      {:error, reason} -> {:error, reason}
    end
  end

  defp family_act(state, {:meet, id}, _rules) do
    case meet(state, id) do
      {:ok, [], state} -> {:ok, state}
      {:error, reason} -> {:error, reason}
    end
  end

  defp assign(:never, _rows, _key, _index), do: :open
  defp assign(:earlier, rows, key, index), do: phase_of(blocked?(rows, key, index))
  defp assign(:any, rows, key, index), do: phase_of(any_blocked?(rows, key, index))

  defp phase_of(true), do: :held
  defp phase_of(false), do: :open

  defp index_ok(index) when is_integer(index) and index >= 0, do: :ok
  defp index_ok(index), do: {:error, {:index, index}}

  defp signal?(rules, row), do: match?({:ok, :earlier}, hold_of(rules, row.kind))
  defp any?(rules, row), do: match?({:ok, :any}, hold_of(rules, row.kind))

  defp left?(state, id), do: is_integer(id) and id >= 0 and id < state.next

  defp release(state, id, key, rules) do
    gone = remove(state.rows, id)
    {rows, released} = open_all(key, gone, state.tick, rules)
    {:ok, released, %{state | tick: state.tick + 1, rows: rows}}
  end

  # Agda `opens?`. `earlierClause` is an unblocked held `earlier` row.
  # `anyClause` is an unblocked held `any` row, and only when no
  # `earlier` row opens and no smaller `any` row is free. The list
  # `blocked` reads is the list after the removal.
  defp candidate?(key, all, row, rules) do
    row.key == key and row.phase == :held and
      cond do
        signal?(rules, row) -> not blocked?(all, row.key, row.index)
        any?(rules, row) -> not any_blocked?(all, row.key, row.index)
        true -> false
      end
  end

  # The dispatcher's `one_of_any`, which is `hasEarlierCand` and
  # `smallerAny?`. No `any` candidate: open every `earlier` candidate.
  # Only `any` candidates: open the least `{index, id}`. Both: open
  # the `earlier` candidates and leave the `any` rows held.
  defp one_of_any(candidates, rules) do
    {anys, rest} = Enum.split_with(candidates, &any?(rules, &1))

    cond do
      anys == [] -> rest
      rest == [] -> [Enum.min_by(anys, &{&1.index, &1.id})]
      true -> rest
    end
  end

  # Agda `openAll` / `stamp`. Released tuples follow `{index, id}`.
  defp open_all(key, all, tick, rules) do
    chosen = all |> Enum.filter(&candidate?(key, all, &1, rules)) |> one_of_any(rules)
    chosen_ids = MapSet.new(chosen, & &1.id)

    rows =
      Enum.map(all, fn row ->
        if MapSet.member?(chosen_ids, row.id) do
          %{row | opened_at: tick, phase: :open}
        else
          row
        end
      end)

    released =
      chosen
      |> Enum.sort_by(&{&1.index, &1.id})
      |> Enum.map(&{&1.id, &1.key, &1.kind})

    {rows, released}
  end

  defp find(rows, id), do: Enum.find(rows, &(&1.id == id))
  defp remove(rows, id), do: Enum.reject(rows, &(&1.id == id))

  defp unique_ids?(rows) do
    ids = Enum.map(rows, & &1.id)
    length(ids) == length(Enum.uniq(ids))
  end

  defp unique_index?(rows) do
    pairs = Enum.map(rows, &{&1.key, &1.index})
    length(pairs) == length(Enum.uniq(pairs))
  end

  defp ids_below?(rows, next) do
    Enum.all?(rows, fn row -> is_integer(row.id) and row.id >= 0 and row.id < next end)
  end

  defp clock?(rows, tick) do
    Enum.all?(rows, fn row ->
      is_integer(row.born) and is_integer(row.opened_at) and row.born < tick and
        row.opened_at < tick
    end)
  end

  defp held_mode?(rows, rules) do
    Enum.all?(rows, fn row ->
      row.phase != :held or signal?(rules, row) or any?(rules, row)
    end)
  end

  defp held_earlier?(rows, rules) do
    Enum.all?(rows, fn row ->
      row.phase != :held or not signal?(rules, row) or
        Enum.any?(rows, &(&1.key == row.key and &1.index < row.index))
    end)
  end

  defp held_any?(rows, rules) do
    Enum.all?(rows, fn row ->
      row.phase != :held or not any?(rules, row) or
        Enum.any?(rows, &(&1.key == row.key and &1.phase == :open))
    end)
  end

  # Agda `ResolvedAny`. An opened `any` row has no earlier live row of
  # the same kind born at or before its open tick.
  defp resolved_any?(rows, rules) do
    Enum.all?(rows, fn opened ->
      not (opened.phase == :open and any?(rules, opened)) or
        not Enum.any?(rows, fn earlier ->
          earlier.kind == opened.kind and earlier.key == opened.key and
            earlier.index < opened.index and earlier.born <= opened.opened_at
        end)
    end)
  end
end

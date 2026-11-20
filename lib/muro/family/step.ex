defmodule Muro.Family.Step do
  @moduledoc """
  The keyed-family step, for any number of keys and any number of instances.

  This is the executable image of `agda/Muro/Family.agda`. It is written
  against those definitions. It is not extracted from them. The names
  below are the Agda names.

  `hold_of/1` is `holdOf`: `init` is `never`, `signal` is `earlier`.
  A generated family whose constructor is held while an earlier instance
  is unresolved uses that same `earlier` clause. `blocked?/3` is
  `blocked?`. `decide/5` is `decide`. `on_key/2` is `onKey`. `arrive/5`
  is `arriveTo`. `resolve/3` is `resolveTo`. `touch/2` is `touchTo`, and
  `rerun/2` and `meet/2` are that same transition. `apply` in Agda sends
  `Act.arrive key index kind` to `arriveTo state key kind index`.

  `no_overtake?/2` is `NoOvertake`. `bad_open?/2` is `BadOpen`. An opened
  signal is a violation when an earlier live row of its key was already
  born at the tick the signal opened (`born ≤ openedAt`). A row that
  arrives later has a greater birth tick and is not a violation.
  `held_blocked?/1` is `HeldBlocked`. `least_earlier/2` is `pick` on
  `Earlier`. `invariant?/2` is `Invariant`: distinct ids, distinct
  key-and-index pairs, ids below `next`, birth and open ticks below
  `tick`, a held row is a signal, every held row has an earlier live
  row of its key, and `NoOvertake`.

  `script_a/0` is `script-a`: `init` at 0, `signal` at 1, `signal` at 2.
  `script_b/0` is `script-b`: `init` at 0.

  The phase `:open` is Agda `opened`. `:held` is `held`. `born` is
  `bornOf`. `opened_at` is `openedAtOf`. The dispatcher does not store
  the tick. Those fields live only here.

  `replay/2` is the family relation alone. `check_trace` also requires
  a rerun, and a resolve that has started a session, to land on `done`.
  That session condition is not `touchTo`.

  `release?` opens a held row of the resolved key when `holdOf` of its
  kind is `earlier` and `blocked?` is false on the list after the
  removal. On the proved kind, `earlier` is `signal`, which is Agda
  `isSignal`. The released list is sorted by `{index, id}`, which is
  the list the dispatcher returns. Agda `openAll` keeps list order.
  Membership is the same.

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
      {:ok, hold} when hold in [:never, :earlier] -> {:ok, hold}
      _ -> {:error, {:kind, kind}}
    end
  end

  @doc """
  Agda `blocked?`. True when a live row of `key` has a creation index
  strictly below `index`. A resolved instance is not in `rows`.
  """
  def blocked?(rows, key, index) do
    Enum.any?(rows, fn row -> row.key == key and row.index < index end)
  end

  @doc """
  Agda `decide`. `never` opens. `earlier` holds when `blocked?` is true
  and opens otherwise. The phase `:open` is Agda `opened`.
  """
  def decide(rows, key, index, kind, rules) do
    {:ok, hold} = hold_of(rules, kind)
    assign(hold, blocked?(rows, key, index))
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
  Agda `resolveTo`. An opened row leaves. Each held signal of that key
  which `release?` accepts is stamped open at the current tick, then
  the tick advances. A held id is `{:held, id}`. An unknown id is
  `{:unknown, id}`.
  """
  def resolve(state, id, rules) do
    case find(state.rows, id) do
      nil ->
        {:error, {:unknown, id}}

      %{phase: :held} ->
        {:error, {:held, id}}

      %{phase: :open, key: key} ->
        gone = remove(state.rows, id)
        {rows, released} = open_all(key, gone, state.tick, rules)
        {:ok, released, %{state | tick: state.tick + 1, rows: rows}}
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

  @doc "Agda `NoOvertake`, the negation of `BadOpen`."
  def no_overtake?(rows, rules), do: not bad_open?(rows, rules)

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
  Agda `Invariant` for this state and this family's rules. `signal` in
  the proof is a kind whose hold is `earlier`.
  """
  def invariant?(state, rules) do
    rows = state.rows

    unique_ids?(rows) and unique_index?(rows) and ids_below?(rows, state.next) and
      clock?(rows, state.tick) and held_signal?(rows, rules) and held_blocked?(rows) and
      no_overtake?(rows, rules)
  end

  @doc """
  Agda `script-a`. Key `a` of the family graph: `init` at 0, `signal`
  at 1, `signal` at 2.
  """
  def script_a, do: [{:init, 0}, {:signal, 1}, {:signal, 2}]

  @doc "Agda `script-b`. Key `b` of the family graph: one `init` at 0."
  def script_b, do: [{:init, 0}]

  @doc """
  Family steps only: `arriveTo`, `resolveTo`, and `touchTo`.

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

  defp assign(:never, _blocked), do: :open
  defp assign(:earlier, true), do: :held
  defp assign(:earlier, false), do: :open

  defp index_ok(index) when is_integer(index) and index >= 0, do: :ok
  defp index_ok(index), do: {:error, {:index, index}}

  defp signal?(rules, row), do: match?({:ok, :earlier}, hold_of(rules, row.kind))

  # Agda `release?`: same key, held, `isSignal`, and not `blocked?` on
  # the post-removal list. `isSignal` is `holdOf kd ≡ earlier`.
  defp release?(key, all, row, rules) do
    row.key == key and row.phase == :held and signal?(rules, row) and
      not blocked?(all, row.key, row.index)
  end

  # Agda `openAll` / `stamp`. The list handed to `blocked?` is the
  # pre-update list. The released tuples follow the dispatcher's
  # `{index, id}` order.
  defp open_all(key, all, tick, rules) do
    {rows, released} =
      Enum.map_reduce(all, [], fn row, acc ->
        if release?(key, all, row, rules) do
          opened = %{row | opened_at: tick, phase: :open}
          {opened, [{row.index, row.id, row.key, row.kind} | acc]}
        else
          {row, acc}
        end
      end)

    released =
      released
      |> Enum.sort_by(fn {index, id, _key, _kind} -> {index, id} end)
      |> Enum.map(fn {_index, id, key, kind} -> {id, key, kind} end)

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

  defp held_signal?(rows, rules) do
    Enum.all?(rows, fn row -> row.phase != :held or signal?(rules, row) end)
  end
end

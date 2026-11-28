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
  `anyBlocked?`. Elixir takes `(rows, key, index)` and skips same-index
  rows; Agda takes `(rs, k)` and counts `opened` rows. They agree under
  `NoDupIx` and held subjects on release, not off-invariant. `decide/5`
  is `decide` for `never` and `earlier`, and `decideMode` when the hold
  is `any`. `on_key/2` is `onKey`. `arrive/5` is `arriveTo` and
  `arriveMode`, and it refuses a creation index that has departed.
  That refusal is not `arriveTo`: Agda `fresh?` reads the live rows.
  The departed prefix and gap set remember host creation indices.
  `floor` is one integer, initially -1. `skip_below/2` raises it.
  An index at or below the floor has departed for every key, including
  a first arrival. The record above the floor is exact. While the
  floor stays -1, memory is O(departed instances) per key in general,
  and O(keys + permanent gaps) only when indices are dense per key or
  holes are skipped. After `skip_below`, memory is O(keys with a
  departure above the floor + gap entries above the floor). The floor
  and the departed record are not fields of the Agda state. `resolve/3`
  is `resolveTo`
  and `resolveMode`.
  `withdraw/3` is `withdrawTo` on the successful path: a held row leaves
  and the release is the release of `resolveMode`. Elixir returns
  `:resolved`, `:unknown`, and `:opened`; Agda returns `nothing`.
  `touch/2` is `touchTo` and `touchMode`. `rerun/2` and `meet/2` are
  that same transition. `apply` in Agda sends `Act.arrive key index
  kind` to `arriveTo state key kind index`, and `withdrawR` to
  `withdrawTo`.

  `no_overtake?/2` is `NoOvertake` and `NoOvertakeR`. `bad_open?/2` is
  `BadOpen`. Both check the `mearlier` shape only. The two-open-`many`
  case of `BadFamily` is `at_most_one_any?/2` (`AtMostOne`) and
  `ResolvedAny`. An opened signal is a violation when an earlier live
  row of its key was already born at the tick the signal opened
  (`born ≤ openedAt`). A row that arrives later has a greater birth
  tick and is not a violation.
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
  row is `earlier`, `any`, or a named kind, a held `earlier` row has an
  earlier live row, a held `any` row has another open row of its key,
  `AtMostOne`, `NoOvertake`, `ResolvedAny`, and `named_safe?`. An opened
  named row saw no live `while` row of its key born at or before it
  opened, and every `until` kind of that key has resolved at least once.
  A held named row is blocked by the rows and facts that are here now.

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

  A named rule is `{:named, %{while: kinds, until: kinds}}`. `while` holds
  while an arrived row of a listed kind and the same key is open or held.
  None arrived is not a hold. `until` holds until each listed kind has
  resolved at least once for that key. One resolution is enough. The fact
  stays after that row leaves. `withdraw` does not record it. `drop_key/2`
  deletes that key's facts when the state has a `:kinds` field, and it
  does not add the field. `skip/3` does not clear facts. `skip_below/2`
  does not clear facts unless `may revert` prunes the last resolved row
  of that key and kind.
  `empty/0` has no `:kinds` field. `waiting_on/3` names the kinds and ids
  still blocking a held id. The generated child spells that query
  `waiting_on/2`, because the child closes over its rules.

  `may revert` is the rules entry `{{:mark, :revert}, true}`. It is not
  a kind. Without it, `resolve` removes the row and `revert/3` is
  `{:error, {:unmarked, :revert}}` before it reads the state. With it,
  `resolve` of an open row keeps that row at phase `:resolved` and does
  not record a departure. `revert/3` puts the row back to `:open` and
  keeps `born` and `opened_at`, so the hold is not decided again. The
  tick advances. A same-key row that is open or resolved blocks that
  revert when its rule was held behind the target: a later creation
  index for `earlier` and for `any`, or a named rule whose `while` or
  `until` lists the target kind. The refusal is `{:error, {:held_by, ids}}`,
  ids sorted by creation index then id. A held row does not block, and
  a revert does not open or hold any other row. When no resolved row of
  that key and kind remains, the kind leaves `:kinds`. `withdraw` of a
  held row still removes it. The id stays in `:withdrawn` until
  `drop_key` of its key or `skip_below` covers its index, and `revert`
  of it is `{:error, {:withdrawn, id}}`. After that prune it is
  `{:error, {:unknown, id}}`, the same as a resolved row `drop_key` or
  `skip_below` removed. `drop_key` still refuses an open or held row.
  Resolved rows of that key are removed with the departed record and
  the facts. `skip_below` removes resolved rows at or below the new
  floor and drops a fact that no remaining resolved row supports.

  The meeting graph, one retry then give-up, `fail stop`, and the
  program that writes the dispatcher are not this module. `NamedHold` in
  `agda/Muro/Family.agda` is the named-kind argument. It does not replace
  the theorems above it.
  """

  @doc """
  `holdOf` for the proved kind. `init` is `never`. `signal` is `earlier`.
  """
  def proved_rules, do: %{init: :never, signal: :earlier}

  @doc "Agda `empty`."
  def empty, do: %{next: 0, tick: 0, rows: [], departed: %{}, floor: -1}

  @doc """
  `holdOf` read from a family's rules. An unknown kind is the
  dispatcher's `{:kind, kind}`.
  """
  def hold_of(rules, kind) do
    case Map.fetch(rules, kind) do
      {:ok, hold} when hold in [:never, :earlier, :any] ->
        {:ok, hold}

      {:ok, {:named, %{while: while, until: until}} = hold}
      when is_list(while) and is_list(until) ->
        {:ok, hold}

      _ ->
        {:error, {:kind, kind}}
    end
  end

  @doc """
  Agda `earlierBlocked?`. True when a live row of `key` has a creation
  index strictly below `index`. A row at phase `:resolved` does not
  count. A family that does not keep resolved rows has none in `rows`.
  """
  def blocked?(rows, key, index) do
    Enum.any?(rows, fn row ->
      row.key == key and row.index < index and row.phase != :resolved
    end)
  end

  @doc """
  Agda `anyBlocked?`. True when a row of `key` other than `index` is
  open. A held row is not open, so a held subject does not block
  itself. On arrival the new row is not in `rows`. Elixir takes
  `(rows, key, index)` and skips same-index rows; Agda takes `(rs, k)`
  and counts `opened` rows. They agree under `NoDupIx` and held
  subjects on release, not off-invariant.
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
    decide(rows, key, index, kind, rules, %{})
  end

  @doc """
  `decide/5` with the per-key fact map of kinds that have resolved at
  least once. `decide/5` passes an empty map, so a `held until` kind
  with no fact in that argument stays held.
  """
  def decide(rows, key, index, kind, rules, facts) when is_map(facts) do
    {:ok, hold} = hold_of(rules, kind)
    assign(hold, rows, key, index, facts)
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
  the arrival. An index that has departed is `{:departed, key, index}`.
  Agda `fresh?` does not refuse that index: it reads the live rows.
  """
  def arrive(state, key, kind, index, rules) do
    with :ok <- index_ok(index),
         {:ok, _hold} <- hold_of(rules, kind),
         {:ok, _floor} <- take_floor(state) do
      cond do
        not fresh?(state.rows, key, index) ->
          {:error, {:duplicate, key, index}}

        departed?(state, key, index) ->
          {:error, {:departed, key, index}}

        true ->
          phase = decide(state.rows, key, index, kind, rules, kind_facts(state, key))
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
      end
    end
  end

  @doc """
  True when creation index `index` of `key` has departed.

  `floor` starts at -1. Every index `i` with `i <= floor` has departed,
  for every key. `P` starts at -1, before the first valid index. Every
  index `i` with `i <= P` has departed. The gap map holds departed
  indices strictly above `P`. A key with no record has departed nothing
  above the floor. This predicate is not Agda `fresh?`.

  A missing `floor` is -1, as on `empty/0`. A present `floor` that is
  not an integer at least -1 does not match. The call fails the way a
  departed record that is not `{P, S}` fails, and it does not read that
  floor as -1. An error tuple does not fit: callers use the result as
  a boolean. `arrive`, `resolve`, `withdraw`, and `skip_below` are the
  host boundary. They return `{:error, {:state, state}}` for that floor
  and do not raise.
  """
  def departed?(state, key, index) when is_integer(index) do
    {prefix, gaps} = departed_record(state, key)
    index <= floor_value(state) or index <= prefix or Map.has_key?(gaps, index)
  end

  @doc """
  Host promise: nothing at or below `index` arrives again, for any key.

  `floor` starts at -1. A call with `index <= floor` returns the same
  state and does not read or validate the departed records. A malformed
  record is reported by the next call that reads it. The argument is a
  non-negative integer, the same check as a creation index. Gap entries
  at or below the new floor are dropped. A prefix below the floor is
  raised to the floor, then `P` advances while
  `P + 1` is in the gap map. A key that then holds nothing strictly above
  the floor loses its record. A live row is left in place. A call
  above the floor walks every key's departed record, O(keys), so a host
  calls it periodically, not on every event. A missing
  `floor` is -1, as a missing `departed` map is empty. A present `floor`
  that is not an integer at least -1 is `{:state, state}`.
  """
  def skip_below(state, index) do
    with :ok <- index_ok(index),
         {:ok, floor} <- take_floor(state) do
      if index <= floor do
        {:ok, state}
      else
        case compact_departed(state, index) do
          {:ok, departed} ->
            # `|` cannot add `floor` when the key is missing. A missing
            # floor is -1, and this call stores the new one.
            state = state |> Map.put(:departed, departed) |> Map.put(:floor, index)

            with {:ok, state} <- prune_withdrawn_floor(state, index) do
              {:ok, prune_resolved_floor(state, index)}
            end

          {:error, reason} ->
            {:error, reason}
        end
      end
    end
  end

  @doc """
  Host promise: creation index `index` of `key` does not arrive.

  A live row of that index is `{:duplicate, key, index}`. An index at or
  below the floor returns the same state and does not read the departed
  record. The kinds record is left in place. A bad departed record fails
  the way `departed?/3` fails.
  """
  def skip(state, key, index) when is_map(state) do
    with :ok <- index_ok(index),
         {:ok, floor} <- take_floor(state),
         rows when is_list(rows) <- Map.get(state, :rows) do
      cond do
        not fresh?(rows, key, index) ->
          {:error, {:duplicate, key, index}}

        index <= floor ->
          {:ok, state}

        true ->
          {:ok, note_departed(state, key, index)}
      end
    else
      {:error, reason} -> {:error, reason}
      _ -> {:error, {:state, state}}
    end
  end

  def skip(state, _key, _index), do: {:error, {:state, state}}

  @doc """
  Forget one key's departed record when that key has no live row.

  The floor stays. When `:kinds` is a map, that key's facts are deleted
  with the departed record. A state with no `:kinds` field does not grow
  one. After this call a new `until` row of the key waits again.
  """
  def drop_key(state, key) when is_map(state) do
    with {:ok, _floor} <- take_floor(state),
         rows when is_list(rows) <- Map.get(state, :rows) do
      if live_key?(rows, key) do
        {:error, {:live, key}}
      else
        with {:ok, state} <- clear_key(state, key),
             {:ok, state} <- drop_withdrawn_key(state, key) do
          {:ok, drop_resolved_key(state, key)}
        end
      end
    else
      {:error, reason} -> {:error, reason}
      _ -> {:error, {:state, state}}
    end
  end

  def drop_key(state, _key), do: {:error, {:state, state}}

  @doc """
  Agda `resolveTo` and `resolveMode`. An opened row leaves. `openAll`
  stamps the rows that release, then the tick advances. A held id is
  `{:held, id}`. An id that is not live is `{:unknown, id}`, including
  an id that has already left.
  """
  def resolve(state, id, rules) do
    with {:ok, _floor} <- take_floor(state) do
      case find(state.rows, id) do
        nil ->
          {:error, {:unknown, id}}

        %{phase: :held} ->
          {:error, {:held, id}}

        %{phase: :resolved} ->
          {:error, {:resolved, id}}

        %{phase: :open, key: key} ->
          release(state, id, key, rules, true)

        _ ->
          {:error, {:state, state}}
      end
    end
  end

  @doc """
  Agda `withdrawTo`. A held row leaves and `openAll` runs, the same
  release as `resolveMode`. The successful path matches `withdrawTo`.
  Elixir returns richer error atoms: an open id is `{:opened, id}`;
  an id below `next` that is not live has left, `{:resolved, id}`;
  any other missing id is `{:unknown, id}`. Agda returns `nothing` in
  each of those cases.
  """
  def withdraw(state, id, rules) do
    with {:ok, _floor} <- take_floor(state) do
      case find(state.rows, id) do
        %{phase: :open} ->
          {:error, {:opened, id}}

        %{phase: :resolved} ->
          {:error, {:resolved, id}}

        %{phase: :held, key: key} ->
          release(state, id, key, rules, false)

        nil ->
          if left?(state, id), do: {:error, {:resolved, id}}, else: {:error, {:unknown, id}}

        _ ->
          {:error, {:state, state}}
      end
    end
  end

  @doc """
  Why a held id is held.

  `{:ok, %{kinds: kinds, ids: ids}}` names the kinds still blocking it
  and the ids of the arrived unresolved rows that block it. Kinds follow
  the rule: `while`, then `until`, each name once. An `until` kind with
  no arrival yet is in `kinds` and contributes no id. `earlier` and `any`
  list the kinds of the blocking rows in creation-index order. Ids are
  sorted by creation index, then id. `{:error, {:opened, id}}` when the
  row is open. `{:error, {:unknown, id}}` when the id is not live,
  including one that has left. `{:error, {:state, state}}` when `state`
  is not a step state, a held row has no blocker this function can
  name, a row of that key has an index or id that is not a non-negative
  integer, or, on a family with an `until` clause, that key's kinds
  entry is not a map. The call does not raise.
  """
  def waiting_on(state, id, rules) when is_map(state) and is_map(rules) do
    with {:ok, _floor} <- take_floor(state),
         rows when is_list(rows) <- Map.get(state, :rows) do
      case safe_find(rows, id) do
        nil ->
          {:error, {:unknown, id}}

        %{phase: :open} ->
          {:error, {:opened, id}}

        %{phase: :resolved} ->
          {:error, {:unknown, id}}

        %{phase: :held} = row ->
          explain_held(state, rows, row, rules)

        _ ->
          {:error, {:state, state}}
      end
    else
      {:error, reason} -> {:error, reason}
      _ -> {:error, {:state, state}}
    end
  end

  def waiting_on(state, _id, _rules), do: {:error, {:state, state}}

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
      %{phase: :resolved} -> {:error, {:resolved, id}}
      %{phase: :open} -> {:ok, [], state}
      _ -> {:error, {:state, state}}
    end
  end

  @doc """
  Put a resolved row back to `:open`.

  The rules map carries `{{:mark, :revert}, true}` when the family is
  marked. Without that entry the result is `{:error, {:unmarked, :revert}}`
  and the state is not read. With it, an open id is `{:error, {:opened, id}}`,
  a held id is `{:error, {:held, id}}`, and a resolved id that a same-key
  open or resolved row was held behind is `{:error, {:held_by, ids}}`.
  Ids are sorted by creation index, then id. A withdrawn id that has not
  been pruned is `{:error, {:withdrawn, id}}`. An id this step never
  minted, or one `drop_key` or `skip_below` has pruned, is
  `{:error, {:unknown, id}}`. A bad state is `{:error, {:state, state}}`.
  The call does not raise.

  Success keeps `born` and `opened_at` and advances `tick`. No other
  row changes phase. The kind's fact is removed when no resolved row of
  that key and kind remains. `:kinds` is not added when the state has
  no such field.
  """
  def revert(_state, _id, rules) when not is_map(rules), do: {:error, {:unmarked, :revert}}

  def revert(state, id, rules) do
    cond do
      not revert?(rules) ->
        {:error, {:unmarked, :revert}}

      not is_map(state) ->
        {:error, {:state, state}}

      true ->
        revert_marked(state, id, rules)
    end
  end

  @doc "The dispatcher's `live` classification. `:open` is Agda `opened`."
  def live(state, id) do
    case find(state.rows, id) do
      nil ->
        {:error, {:unknown, id}}

      %{phase: :resolved} ->
        {:error, {:resolved, id}}

      %{phase: phase, key: key, kind: kind} when phase in [:open, :held] ->
        {:ok, phase, key, kind}

      _ ->
        {:error, {:state, state}}
    end
  end

  @doc """
  Agda `pick` on `Earlier`: the live row of this key with the least
  creation index strictly below `row`. `nil` when none is live.
  """
  def least_earlier(rows, row) do
    case Enum.filter(rows, fn other ->
           other.key == row.key and other.index < row.index and other.phase != :resolved
         end) do
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
  Agda `BadOpen`. The `mearlier` shape only: an opened signal, and an
  earlier live row of its key whose birth tick is at most the signal's
  open tick. The two-open-`many` case of `BadFamily` is
  `at_most_one_any?/2` (`AtMostOne`) and `ResolvedAny`.
  """
  def bad_open?(rows, rules) do
    Enum.any?(rows, fn opened ->
      signal?(rules, opened) and opened.phase == :open and
        Enum.any?(rows, fn earlier ->
          earlier.key == opened.key and earlier.index < opened.index and
            earlier.phase != :resolved and earlier.born <= opened.opened_at
        end)
    end)
  end

  @doc """
  Agda `NoOvertake` and `NoOvertakeR`, the negation of `BadOpen`.
  The `mearlier` shape only. The two-open-`many` case of `BadFamily`
  is `at_most_one_any?/2` (`AtMostOne`) and `ResolvedAny`.
  """
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
            earlier.phase != :resolved and earlier.born <= opened.opened_at
        end)
    end)
  end

  @doc """
  Agda `HeldBlocked`. Every held row has an earlier live row of its key.
  """
  def held_blocked?(rows) do
    Enum.all?(rows, fn row ->
      row.phase != :held or
        Enum.any?(rows, fn earlier ->
          earlier.key == row.key and earlier.index < row.index and earlier.phase != :resolved
        end)
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
      resolved_any?(rows, rules) and named_safe?(state, rules)
  end

  @doc """
  Agda `script-a`. Key `a` of the family graph: `init` at 0, `signal`
  at 1, `signal` at 2.
  """
  def script_a, do: [{:init, 0}, {:signal, 1}, {:signal, 2}]

  @doc "Agda `script-b`. Key `b` of the family graph: one `init` at 0."
  def script_b, do: [{:init, 0}]

  @doc """
  Family steps: `arriveTo`, `resolveTo`, `withdrawTo`, `touchTo`,
  `revert`, `skip`, `drop_key`, and `skip_below`.

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

  defp family_act(state, {:revert, id}, rules) do
    case revert(state, id, rules) do
      {:ok, state} -> {:ok, state}
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

  defp family_act(state, {:skip, key, index}, _rules) do
    case skip(state, key, index) do
      {:ok, state} -> {:ok, state}
      {:error, reason} -> {:error, reason}
    end
  end

  defp family_act(state, {:drop, key}, _rules) do
    case drop_key(state, key) do
      {:ok, state} -> {:ok, state}
      {:error, reason} -> {:error, reason}
    end
  end

  defp family_act(state, {:skip_below, index}, _rules) do
    case skip_below(state, index) do
      {:ok, state} -> {:ok, state}
      {:error, reason} -> {:error, reason}
    end
  end

  defp assign(:never, _rows, _key, _index, _facts), do: :open
  defp assign(:earlier, rows, key, index, _facts), do: phase_of(blocked?(rows, key, index))
  defp assign(:any, rows, key, index, _facts), do: phase_of(any_blocked?(rows, key, index))

  defp assign({:named, spec}, rows, key, _index, facts) do
    phase_of(named_blocked?(spec, rows, key, facts))
  end

  defp phase_of(true), do: :held
  defp phase_of(false), do: :open

  defp index_ok(index) when is_integer(index) and index >= 0, do: :ok
  defp index_ok(index), do: {:error, {:index, index}}

  # A missing floor is -1, as a missing `departed` map is empty. The
  # generated dispatcher rejects a missing floor. A present bad floor
  # is `{:error, {:state, state}}` from the host calls.
  defp take_floor(state) do
    case Map.fetch(state, :floor) do
      :error ->
        {:ok, -1}

      {:ok, floor} when is_integer(floor) and floor >= -1 ->
        {:ok, floor}

      {:ok, _} ->
        {:error, {:state, state}}
    end
  end

  # A missing floor is -1. A present bad floor does not match, as
  # `departed_record` does not match a record that is not `{P, S}`.
  # This reader does not turn that floor into -1. `departed?` uses it
  # because a boolean predicate cannot return `{:state, state}`.
  defp floor_value(state) do
    case take_floor(state) do
      {:ok, floor} -> floor
    end
  end

  defp signal?(rules, row), do: match?({:ok, :earlier}, hold_of(rules, row.kind))
  defp any?(rules, row), do: match?({:ok, :any}, hold_of(rules, row.kind))

  defp left?(state, id), do: is_integer(id) and id >= 0 and id < state.next

  defp release(state, id, key, rules, record?) do
    row = find(state.rows, id)

    # A marked resolve keeps the row. Every other release removes it and
    # records the departure. `withdraw` on a marked family also remembers
    # the id, so a later `revert` can tell it from a pruned row.
    {base, depart?} =
      if record? and revert?(rules) do
        {set_phase(state.rows, id, :resolved), false}
      else
        {remove(state.rows, id), true}
      end

    state = if record?, do: note_resolved(state, key, row.kind, rules), else: state
    facts = kind_facts(state, key)
    {rows, released} = open_all(key, base, state.tick, rules, facts)
    state = %{state | tick: state.tick + 1, rows: rows}

    state =
      if depart? do
        state = note_departed(state, key, row.index)
        if not record? and revert?(rules), do: note_withdrawn(state, row), else: state
      else
        state
      end

    {:ok, released, state}
  end

  defp revert?(rules), do: Map.get(rules, {:mark, :revert}) == true

  defp revert_marked(state, id, rules) do
    with {:ok, _floor} <- take_floor(state),
         rows when is_list(rows) <- Map.get(state, :rows),
         :ok <- kinds_shape(state) do
      case safe_find(rows, id) do
        nil ->
          revert_missing(state, id)

        %{phase: :open} ->
          {:error, {:opened, id}}

        %{phase: :held} ->
          {:error, {:held, id}}

        %{phase: :resolved} = row ->
          case blockers(rows, row, rules) do
            :bad ->
              {:error, {:state, state}}

            [] ->
              do_revert(state, row)

            ids ->
              {:error, {:held_by, ids}}
          end

        _ ->
          {:error, {:state, state}}
      end
    else
      {:error, reason} -> {:error, reason}
      _ -> {:error, {:state, state}}
    end
  end

  defp kinds_shape(state) do
    case Map.fetch(state, :kinds) do
      :error -> :ok
      {:ok, kinds} when is_map(kinds) -> :ok
      {:ok, _} -> {:error, {:state, state}}
    end
  end

  defp revert_missing(state, id) do
    cond do
      not left?(state, id) ->
        {:error, {:unknown, id}}

      withdrawn?(state, id) ->
        {:error, {:withdrawn, id}}

      true ->
        {:error, {:unknown, id}}
    end
  end

  defp withdrawn?(state, id) do
    case Map.get(state, :withdrawn) do
      %{^id => {_key, index}} when is_integer(index) -> true
      _ -> false
    end
  end

  defp do_revert(%{tick: tick} = state, row) when is_integer(tick) do
    rows = set_phase(state.rows, row.id, :open)
    state = %{state | rows: rows, tick: tick + 1}
    {:ok, drop_fact(state, row.key, row.kind)}
  end

  defp do_revert(state, _row), do: {:error, {:state, state}}

  defp set_phase(rows, id, phase) do
    Enum.map(rows, fn
      %{id: ^id} = row -> %{row | phase: phase}
      row -> row
    end)
  end

  defp note_withdrawn(state, row) do
    case Map.get(state, :withdrawn, %{}) do
      withdrawn when is_map(withdrawn) ->
        Map.put(state, :withdrawn, Map.put(withdrawn, row.id, {row.key, row.index}))

      _ ->
        Map.put(state, :withdrawn, %{row.id => {row.key, row.index}})
    end
  end

  # A later `earlier` or `any` row, or a named row whose `while` or
  # `until` lists this kind. Held rows are not in the way: they never
  # ran. `any` has no kind, so the order is the creation index, and the
  # later row is the one that was held behind.
  defp blockers(rows, target, rules) do
    case Enum.reduce_while(rows, [], fn other, acc ->
           case behind(target, other, rules) do
             :bad -> {:halt, :bad}
             :yes -> {:cont, [{other.index, other.id} | acc]}
             :no -> {:cont, acc}
           end
         end) do
      :bad ->
        :bad

      hits ->
        hits |> Enum.sort() |> Enum.map(fn {_index, id} -> id end)
    end
  end

  defp behind(target, other, rules) do
    cond do
      not row_shape?(other) ->
        :bad

      other.key != target.key or other.id == target.id ->
        :no

      other.phase not in [:open, :resolved] ->
        :no

      true ->
        case hold_of(rules, other.kind) do
          {:ok, :never} ->
            :no

          {:ok, :earlier} ->
            if other.index > target.index, do: :yes, else: :no

          {:ok, :any} ->
            if other.index > target.index, do: :yes, else: :no

          {:ok, {:named, %{while: while, until: until}}} ->
            if target.kind in while or target.kind in until, do: :yes, else: :no

          _ ->
            :bad
        end
    end
  end

  defp drop_fact(state, key, kind) do
    case Map.fetch(state, :kinds) do
      :error ->
        state

      {:ok, kinds} when is_map(kinds) ->
        if resolved_kind?(state.rows, key, kind) do
          state
        else
          %{state | kinds: delete_kind(kinds, key, kind)}
        end

      {:ok, _} ->
        state
    end
  end

  defp resolved_kind?(rows, key, kind) do
    Enum.any?(rows, fn
      %{key: ^key, kind: ^kind, phase: :resolved} -> true
      _ -> false
    end)
  end

  defp delete_kind(kinds, key, kind) do
    case Map.get(kinds, key) do
      inner when is_map(inner) ->
        inner = Map.delete(inner, kind)
        if inner == %{}, do: Map.delete(kinds, key), else: Map.put(kinds, key, inner)

      _ ->
        Map.delete(kinds, key)
    end
  end

  defp live_key?(rows, key) do
    Enum.any?(rows, fn
      %{key: ^key, phase: :resolved} -> false
      %{key: ^key} -> true
      _ -> false
    end)
  end

  defp drop_resolved_key(state, key) do
    if resolved_key?(state.rows, key) do
      %{state | rows: Enum.reject(state.rows, &match?(%{key: ^key, phase: :resolved}, &1))}
    else
      state
    end
  end

  defp resolved_key?(rows, key) do
    Enum.any?(rows, &match?(%{key: ^key, phase: :resolved}, &1))
  end

  defp drop_withdrawn_key(state, key) do
    case Map.fetch(state, :withdrawn) do
      :error ->
        {:ok, state}

      {:ok, withdrawn} when is_map(withdrawn) ->
        kept = Map.reject(withdrawn, fn {_id, pair} -> match?({^key, _}, pair) end)
        {:ok, put_withdrawn(state, withdrawn, kept)}

      {:ok, _} ->
        {:error, {:state, state}}
    end
  end

  defp prune_resolved_floor(%{rows: rows} = state, floor) when is_list(rows) do
    {drop, keep} =
      Enum.split_with(rows, fn
        %{phase: :resolved, index: ix} when is_integer(ix) and ix <= floor -> true
        _ -> false
      end)

    if drop == [] do
      state
    else
      state = %{state | rows: keep}
      Enum.reduce(drop, state, fn row, state -> drop_fact(state, row.key, row.kind) end)
    end
  end

  defp prune_resolved_floor(state, _floor), do: state

  defp prune_withdrawn_floor(state, floor) do
    case Map.fetch(state, :withdrawn) do
      :error ->
        {:ok, state}

      {:ok, withdrawn} when is_map(withdrawn) ->
        kept =
          Map.reject(withdrawn, fn
            {_id, {_key, ix}} when is_integer(ix) and ix <= floor -> true
            _ -> false
          end)

        {:ok, put_withdrawn(state, withdrawn, kept)}

      {:ok, _} ->
        {:error, {:state, state}}
    end
  end

  defp put_withdrawn(state, withdrawn, kept) do
    if map_size(kept) == map_size(withdrawn), do: state, else: %{state | withdrawn: kept}
  end

  # Host creation indices. `P` is -1 until a departure folds up to it.
  # A gap stays in the map until `P + 1` is that gap. An index at or
  # below `floor` writes nothing: the floor already covers it. A later
  # departure above the floor folds from `max(P, floor)`. Not an Agda field.
  defp note_departed(state, key, index) do
    floor = floor_value(state)

    if index <= floor do
      state
    else
      departed = Map.get(state, :departed, %{})
      {prefix, gaps} = departed_record(state, key)

      case store_departure(departed, key, prefix, gaps, floor, index) do
        :already -> state
        {:ok, departed} -> %{state | departed: departed}
      end
    end
  end

  defp compact_departed(state, floor) do
    departed = Map.get(state, :departed, %{})

    Enum.reduce_while(departed, {:ok, %{}}, fn {key, rec}, {:ok, acc} ->
      case squash_record(rec, floor, state) do
        {:error, reason} -> {:halt, {:error, reason}}
        :drop -> {:cont, {:ok, acc}}
        {:keep, kept} -> {:cont, {:ok, Map.put(acc, key, kept)}}
      end
    end)
  end

  defp squash_record({prefix, gaps}, floor, state)
       when is_integer(prefix) and prefix >= -1 and is_map(gaps) do
    if gaps_ok?(prefix, gaps) do
      case pack(prefix, gaps, floor) do
        :drop -> :drop
        kept -> {:keep, kept}
      end
    else
      {:error, {:state, state}}
    end
  end

  defp squash_record(_rec, _floor, state), do: {:error, {:state, state}}

  # Raise a prefix below the floor up to the floor, drop gaps at or
  # below that prefix, then fold. Nothing strictly above the floor
  # means the key's record is dropped.
  defp pack(prefix, gaps, floor) do
    prefix = if prefix < floor, do: floor, else: prefix
    gaps = Map.filter(gaps, fn {ix, _} -> ix > prefix end)
    {prefix, gaps} = fold_prefix(prefix, gaps)

    if prefix <= floor and map_size(gaps) == 0 do
      :drop
    else
      {prefix, gaps}
    end
  end

  defp store_departure(departed, key, prefix, gaps, floor, index) do
    case pack(prefix, gaps, floor) do
      :drop ->
        {prefix, gaps} = fold_prefix(floor, %{index => true})
        {:ok, Map.put(departed, key, {prefix, gaps})}

      {prefix, gaps} ->
        if index <= prefix or Map.has_key?(gaps, index) do
          :already
        else
          {prefix, gaps} = fold_prefix(prefix, Map.put(gaps, index, true))
          {:ok, Map.put(departed, key, {prefix, gaps})}
        end
    end
  end

  defp gaps_ok?(prefix, gaps) do
    Enum.all?(gaps, fn
      {ix, _} when is_integer(ix) and ix > prefix -> true
      _ -> false
    end)
  end

  defp departed_record(state, key) do
    case Map.fetch(Map.get(state, :departed, %{}), key) do
      {:ok, {prefix, gaps}} when is_integer(prefix) and is_map(gaps) -> {prefix, gaps}
      :error -> {-1, %{}}
    end
  end

  defp fold_prefix(prefix, gaps) do
    next = prefix + 1

    if Map.has_key?(gaps, next) do
      fold_prefix(next, Map.delete(gaps, next))
    else
      {prefix, gaps}
    end
  end

  # Agda `opens?`. `earlierClause` is an unblocked held `earlier` row.
  # `anyClause` is an unblocked held `any` row, and only when no
  # `earlier` row opens and no smaller `any` row is free. The list
  # `blocked` reads is the list after the removal.
  defp candidate?(key, all, row, rules, facts) do
    row.key == key and row.phase == :held and
      cond do
        signal?(rules, row) -> not blocked?(all, row.key, row.index)
        any?(rules, row) -> not any_blocked?(all, row.key, row.index)
        named?(rules, row) -> not named_blocked?(named_spec(rules, row), all, key, facts)
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
  defp open_all(key, all, tick, rules, facts) do
    chosen = all |> Enum.filter(&candidate?(key, all, &1, rules, facts)) |> one_of_any(rules)
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
      row.phase != :held or signal?(rules, row) or any?(rules, row) or named?(rules, row)
    end)
  end

  defp held_earlier?(rows, rules) do
    Enum.all?(rows, fn row ->
      row.phase != :held or not signal?(rules, row) or
        Enum.any?(rows, fn earlier ->
          earlier.key == row.key and earlier.index < row.index and earlier.phase != :resolved
        end)
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
  # An opened named row saw no live `while` row of its key born at or
  # before it opened, and every `until` kind has a fact. A held named
  # row is blocked by the rows and facts that are here now. A family
  # with no named rule makes this true.
  defp named_safe?(state, rules) do
    Enum.all?(state.rows, fn row ->
      not named?(rules, row) or
        case row.phase do
          phase when phase in [:open, :resolved] ->
            spec = named_spec(rules, row)
            while_known?(state.rows, row, spec) and until_ok?(state, row, spec)

          :held ->
            named_blocked?(
              named_spec(rules, row),
              state.rows,
              row.key,
              kind_facts(state, row.key)
            )
        end
    end)
  end

  defp while_known?(rows, opened, %{while: while}) do
    Enum.all?(while, fn kind ->
      not Enum.any?(rows, fn other ->
        other.key == opened.key and other.kind == kind and other.phase != :resolved and
          other.born <= opened.opened_at
      end)
    end)
  end

  defp until_ok?(state, opened, %{until: until}) do
    facts = kind_facts(state, opened.key)
    Enum.all?(until, &Map.has_key?(facts, &1))
  end

  defp named_blocked?(%{while: while, until: until}, rows, key, facts) do
    Enum.any?(while, &kind_live?(rows, key, &1)) or
      Enum.any?(until, &(not Map.has_key?(facts, &1)))
  end

  defp kind_live?(rows, key, kind) do
    Enum.any?(rows, fn row ->
      row.key == key and row.kind == kind and row.phase in [:open, :held]
    end)
  end

  defp kind_facts(state, key) do
    case Map.get(state, :kinds) do
      kinds when is_map(kinds) ->
        case Map.get(kinds, key) do
          got when is_map(got) -> got
          _ -> %{}
        end

      _ ->
        %{}
    end
  end

  # The fact is stored only when some rule's `until` list names the kind.
  # A family with no such rule does not grow a `:kinds` field.
  defp note_resolved(state, key, kind, rules) do
    if records_kind?(rules, kind) do
      kinds = Map.get(state, :kinds, %{})
      inner = Map.get(kinds, key, %{})
      inner = if is_map(inner), do: inner, else: %{}
      # `empty/0` has no `:kinds` key. `|` cannot add one.
      Map.put(state, :kinds, Map.put(kinds, key, Map.put(inner, kind, true)))
    else
      state
    end
  end

  defp records_kind?(rules, kind) do
    Enum.any?(rules, fn
      {_ctor, {:named, %{until: until}}} -> kind in until
      _ -> false
    end)
  end

  defp named?(rules, row), do: match?({:ok, {:named, _}}, hold_of(rules, row.kind))

  defp named_spec(rules, row) do
    {:ok, {:named, spec}} = hold_of(rules, row.kind)
    spec
  end

  defp safe_find(rows, id) do
    Enum.find(rows, fn
      %{id: ^id} -> true
      _ -> false
    end)
  end

  # A row of this key that is not a live open or held row, or whose
  # index or id is not a non-negative integer, is the dispatcher's
  # `:bad`. Another key is not scanned. A row that is not a row at all
  # is a bad step state.
  defp explain_held(state, rows, row, rules) do
    if wait_row?(row) do
      case hold_of(rules, row.kind) do
        {:ok, :earlier} ->
          pack_hits(state, classic_hits(rows, row, :earlier))

        {:ok, :any} ->
          pack_hits(state, classic_hits(rows, row, :any))

        {:ok, {:named, spec}} ->
          pack_hits(state, named_hits(state, rows, row, spec, rules))

        _ ->
          {:error, {:state, state}}
      end
    else
      {:error, {:state, state}}
    end
  end

  defp pack_hits(state, :bad), do: {:error, {:state, state}}

  defp pack_hits(state, {kinds, ids}) do
    if kinds == [] and ids == [] do
      {:error, {:state, state}}
    else
      {:ok, %{kinds: kinds, ids: ids}}
    end
  end

  defp classic_hits(rows, %{key: key, index: index}, mode) do
    case scan_key(rows, key) do
      :bad ->
        :bad

      {:ok, key_rows} ->
        hits =
          Enum.flat_map(key_rows, fn row ->
            if blocks_classic?(row, index, mode),
              do: [{row.index, row.id, row.kind}],
              else: []
          end)

        hits = Enum.sort_by(hits, fn {ix, id, _kind} -> {ix, id} end)
        kinds = hits |> Enum.map(fn {_ix, _id, kind} -> kind end) |> Enum.uniq()
        ids = Enum.map(hits, fn {_ix, id, _kind} -> id end)
        {kinds, ids}
    end
  end

  defp blocks_classic?(%{index: ix, phase: phase}, index, :earlier)
       when is_integer(ix) and is_integer(index) do
    ix < index and phase in [:open, :held]
  end

  defp blocks_classic?(%{index: ix, phase: phase}, index, :any)
       when is_integer(ix) and is_integer(index) do
    ix != index and phase == :open
  end

  defp blocks_classic?(_row, _index, _mode), do: false

  defp wait_row?(row), do: row_phase?(row, [:open, :held])

  # A retained resolved row of this key is not a wait hit and is not
  # `:bad`. The marked dispatcher continues past it the same way.
  defp scan_row?(row), do: row_phase?(row, [:open, :held, :resolved])

  defp row_phase?(%{index: ix, id: id, kind: kind, phase: phase}, phases)
       when is_integer(ix) and ix >= 0 and is_integer(id) and id >= 0 and is_atom(kind),
       do: phase in phases

  defp row_phase?(_row, _phases), do: false

  # Halt on a row that is not a row, and on a same-key row the
  # dispatcher would refuse. A retained `:resolved` row continues.
  # Another key stays out of the comparison.
  defp scan_key(rows, key) do
    case Enum.reduce_while(rows, [], fn row, acc ->
           cond do
             not row_shape?(row) ->
               {:halt, :bad}

             row.key == key and not scan_row?(row) ->
               {:halt, :bad}

             row.key == key ->
               {:cont, [row | acc]}

             true ->
               {:cont, acc}
           end
         end) do
      :bad -> :bad
      acc -> {:ok, acc}
    end
  end

  defp clear_key(state, key) do
    departed =
      cond do
        not Map.has_key?(state, :departed) ->
          {:ok, state}

        is_map(state.departed) ->
          {:ok, %{state | departed: Map.delete(state.departed, key)}}

        true ->
          :bad
      end

    case departed do
      :bad ->
        {:error, {:state, state}}

      {:ok, state} ->
        case Map.fetch(state, :kinds) do
          :error ->
            {:ok, state}

          {:ok, kinds} when is_map(kinds) ->
            {:ok, %{state | kinds: Map.delete(kinds, key)}}

          {:ok, _} ->
            {:error, {:state, state}}
        end
    end
  end

  # While kinds, then until kinds. A kind named in both lists appears
  # once, from the while pass. A family with no `until` clause does not
  # read `:kinds`. One with an `until` clause reads it even when this
  # row's until list is empty. A missing `:kinds` key is no facts. A
  # kinds value that is not a map, or a key whose entry is not a map,
  # is the dispatcher's `:bad`.
  defp named_hits(state, rows, row, %{while: while, until: until}, rules) do
    case scan_key(rows, row.key) do
      :bad ->
        :bad

      {:ok, key_rows} ->
        {kinds, pairs} = gather_while(key_rows, while)

        if until_family?(rules) do
          add_until_hits(state, row.key, key_rows, until, kinds, pairs)
        else
          pack_named(kinds, pairs)
        end
    end
  end

  defp gather_while(rows, kinds) do
    Enum.reduce(kinds, {[], []}, fn kind, {acc, pairs} ->
      case live_pairs(rows, kind) do
        [] -> {acc, pairs}
        hits -> {acc ++ [kind], pairs ++ hits}
      end
    end)
  end

  defp live_pairs(rows, want) do
    rows
    |> Enum.flat_map(fn
      %{kind: ^want, phase: phase, index: ix, id: id} when phase in [:open, :held] ->
        [{ix, id}]

      _ ->
        []
    end)
    |> Enum.sort()
  end

  defp add_until_hits(state, key, rows, until, kinds, pairs) do
    case kinds_entry(state, key) do
      :bad ->
        :bad

      {:ok, facts} ->
        {kinds, pairs} =
          Enum.reduce(until, {kinds, pairs}, fn kind, {kinds, pairs} ->
            if Map.has_key?(facts, kind) or kind in kinds do
              {kinds, pairs}
            else
              {kinds ++ [kind], pairs ++ live_pairs(rows, kind)}
            end
          end)

        pack_named(kinds, pairs)
    end
  end

  defp pack_named(kinds, pairs) do
    ids =
      pairs
      |> Enum.uniq()
      |> Enum.sort()
      |> Enum.map(fn {_ix, id} -> id end)

    {kinds, ids}
  end

  # The emitted `kinds_entry`. Missing `:kinds` is `%{}`. A non-map is
  # `:bad`, and so is a non-map entry for this key. `kind_facts/2` is
  # the invariant path and still treats a bad entry as no facts.
  defp kinds_entry(state, key) do
    case Map.fetch(state, :kinds) do
      :error ->
        {:ok, %{}}

      {:ok, kinds} when is_map(kinds) ->
        case Map.get(kinds, key, %{}) do
          got when is_map(got) -> {:ok, got}
          _ -> :bad
        end

      _ ->
        :bad
    end
  end

  defp until_family?(rules) do
    Enum.any?(rules, fn
      {_ctor, {:named, %{until: [_ | _]}}} -> true
      _ -> false
    end)
  end

  defp row_shape?(%{key: _, index: _, id: _, kind: _, phase: _}), do: true
  defp row_shape?(_), do: false

  defp resolved_any?(rows, rules) do
    Enum.all?(rows, fn opened ->
      not (opened.phase == :open and any?(rules, opened)) or
        not Enum.any?(rows, fn earlier ->
          earlier.kind == opened.kind and earlier.key == opened.key and
            earlier.index < opened.index and earlier.phase != :resolved and
            earlier.born <= opened.opened_at
        end)
    end)
  end
end

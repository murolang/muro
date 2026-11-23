defmodule Muro.FsmFamilyTest do
  use ExUnit.Case, async: false

  alias Muro.Family.Graph

  @moduletag timeout: 180_000

  @path "examples/keyed-slots.muro"

  setup_all do
    {disp, parent, src} = compile!(@path)
    on_exit(&purge_fam/0)
    [disp: disp, parent: parent, src: src]
  end

  test "the production trace holds, opens, and releases", %{disp: disp, parent: parent} do
    search = search!()
    assert length(search.states) == 171_649
    assert search.transitions == 729_184

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)
    assert {:open, 2, state} = disp.arrive(state, "b", :init, 0)
    assert {:ok, [{1, "a", :signal}], state} = disp.resolved(state, 0)
    assert {:ok, [], state} = disp.resolved(state, 1)
    assert {:ok, [], _state} = disp.resolved(state, 2)

    trace = [
      {:arrive, "a", :init, 0},
      {:arrive, "a", :signal, 1},
      {:arrive, "b", :init, 0},
      {:resolved, 0},
      {:resolved, 1},
      {:resolved, 2}
    ]

    assert :ok = disp.check_trace(trace)

    lockstep!(search, [
      {:arrive, "a", :init, 0, :open, 0},
      {:arrive, "a", :signal, 1, :held, 1},
      {:arrive, "b", :init, 0, :open, 2},
      {:resolved, 0, [{1, "a", :signal}]},
      {:resolved, 1, []},
      {:resolved, 2, []}
    ])

    server = Module.concat(parent, ServerWait)
    task = Module.concat(parent, TaskWork)
    assert function_exported?(server, :init, 0)
    assert function_exported?(server, :down, 1)
    assert function_exported?(task, :send, 2)
    refute function_exported?(disp, :send, 2)
    assert {:recv, {:data, "Report", []}} = server.expected(server.init())
  end

  test "resolved of an unknown id is an error and does not raise", %{disp: disp} do
    state = disp.new()

    assert {:error, {:unknown, 0}} = disp.resolved(state, 0)
    assert {:error, {:unknown, 99}} = disp.resolved(state, 99)
    assert {:error, {0, {:unknown, 4}}} = disp.check_trace([{:resolved, 4}])
    assert {:error, {:state, :nope}} = disp.resolved(:nope, 0)
    assert {:error, {:state, :nope}} = disp.arrive(:nope, "a", :init, 0)
    assert {:error, {:trace, :nope}} = disp.check_trace(:nope)

    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)
    assert {:error, {:held, 1}} = disp.resolved(state, 1)
    assert {:error, {:kind, :nope}} = disp.arrive(state, "a", :nope, 3)
    assert {:error, {:kind, "init"}} = disp.arrive(state, "a", "init", 3)
    assert {:error, {:index, -1}} = disp.arrive(state, "a", :signal, -1)
    assert {:error, {:duplicate, "a", 0}} = disp.arrive(state, "a", :signal, 0)
    assert {:ok, [{1, "a", :signal}], state} = disp.resolved(state, 0)
    assert {:error, {:unknown, 0}} = disp.resolved(state, 0)
    assert {:error, {:departed, "a", 0}} = disp.arrive(state, "a", :init, 0)
    assert {:error, {:duplicate, "a", 1}} = disp.arrive(state, "a", :signal, 1)

    assert {:error, {2, {:unknown, 0}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:resolved, 0},
               {:resolved, 0}
             ])

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :signal, 5)
    assert {:ok, [], state} = disp.resolved(state, 0)
    assert {:open, 1, state} = disp.arrive(state, "a", :signal, 3)
    assert {:error, {:departed, "a", 5}} = disp.arrive(state, "a", :signal, 5)
  end

  test "a departed creation index is refused and a gap still folds", %{disp: disp, parent: parent} do
    server = Module.concat(parent, ServerWait)

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)
    assert {:ok, [{1, "a", :signal}], done} = disp.finish(state, 0, server.init(), :down)
    assert {:error, {:departed, "a", 0}} = disp.arrive(done, "a", :init, 0)
    assert {:error, {:unknown, 0}} = disp.resolved(done, 0)
    assert done.departed["a"] == {0, %{}}

    assert {:error, {2, {:departed, "a", 0}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:resolved, 0},
               {:arrive, "a", :init, 0}
             ])

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)
    assert {:ok, [], withdrawn} = disp.withdraw(state, 1)
    assert withdrawn.departed["a"] == {-1, %{1 => true}}
    assert {:error, {:departed, "a", 1}} = disp.arrive(withdrawn, "a", :signal, 1)
    assert {:error, {:resolved, 1}} = disp.withdraw(withdrawn, 1)
    assert {:error, {:unknown, 9}} = disp.withdraw(withdrawn, 9)
    assert {:error, {:unknown, 9}} = disp.withdraw(disp.new(), 9)
    assert {:error, {:duplicate, "a", 0}} = disp.arrive(withdrawn, "a", :init, 0)
    assert {:held, 2, later} = disp.arrive(withdrawn, "a", :signal, 2)
    assert {:held, _} = hold_of(disp, later, 2)

    assert {:error, {3, {:departed, "a", 1}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:arrive, "a", :signal, 1},
               {:withdraw, 1},
               {:arrive, "a", :signal, 1}
             ])

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :signal, 4)
    assert {:ok, [], left} = disp.resolved(state, 0)
    assert {:error, {:departed, "a", 4}} = disp.arrive(left, "a", :signal, 4)

    assert {:error, {2, {:departed, "a", 4}}} =
             disp.check_trace([
               {:arrive, "a", :signal, 4},
               {:resolved, 0},
               {:arrive, "a", :signal, 4}
             ])

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :signal, 2)
    assert {:ok, [], state} = disp.resolved(state, 0)
    assert state.departed["a"] == {-1, %{2 => true}}
    assert {:open, 1, state} = disp.arrive(state, "a", :init, 0)
    assert {:ok, [], state} = disp.resolved(state, 1)
    assert state.departed["a"] == {0, %{2 => true}}
    assert {:error, {:departed, "a", 0}} = disp.arrive(state, "a", :init, 0)
    assert {:error, {:departed, "a", 2}} = disp.arrive(state, "a", :signal, 2)
    assert {:open, 2, state} = disp.arrive(state, "a", :signal, 1)
    assert {:ok, [], state} = disp.resolved(state, 2)
    assert state.departed["a"] == {2, %{}}
    assert map_size(elem(state.departed["a"], 1)) == 0
    assert {:error, {:departed, "a", 0}} = disp.arrive(state, "a", :init, 0)
    assert {:error, {:departed, "a", 1}} = disp.arrive(state, "a", :signal, 1)
    assert {:error, {:departed, "a", 2}} = disp.arrive(state, "a", :signal, 2)
    assert {:open, 3, state} = disp.arrive(state, "a", :init, 3)
    assert {:open, 4, other} = disp.arrive(state, "b", :init, 0)
    assert other.departed["a"] == {2, %{}}
    refute Map.has_key?(other.departed, "b")
    assert {:error, {:departed, "a", 0}} = disp.arrive(other, "a", :init, 0)

    assert {:error, {6, {:departed, "a", 1}}} =
             disp.check_trace([
               {:arrive, "a", :signal, 2},
               {:resolved, 0},
               {:arrive, "a", :init, 0},
               {:resolved, 1},
               {:arrive, "a", :signal, 1},
               {:resolved, 2},
               {:arrive, "a", :signal, 1}
             ])

    assert :ok =
             disp.check_trace([
               {:arrive, "a", :signal, 5},
               {:resolved, 0},
               {:arrive, "a", :signal, 3},
               {:resolved, 1},
               {:arrive, "b", :init, 0},
               {:resolved, 2},
               {:arrive, "a", :init, 6},
               {:resolved, 3}
             ])

    assert {:error, {8, {:departed, "a", 5}}} =
             disp.check_trace([
               {:arrive, "a", :signal, 5},
               {:resolved, 0},
               {:arrive, "a", :signal, 3},
               {:resolved, 1},
               {:arrive, "a", :init, 0},
               {:resolved, 2},
               {:arrive, "a", :signal, 4},
               {:resolved, 3},
               {:arrive, "a", :signal, 5}
             ])

    state = disp.new()
    assert {:ok, skipped} = disp.skip(state, "a", 0)
    assert skipped.departed["a"] == {0, %{}}
    assert {:ok, ^skipped} = disp.skip(skipped, "a", 0)
    assert {:error, {:departed, "a", 0}} = disp.arrive(skipped, "a", :init, 0)
    assert {:error, {:index, -1}} = disp.skip(skipped, "a", -1)
    assert {:open, 0, live} = disp.arrive(skipped, "a", :signal, 2)
    assert {:error, {:duplicate, "a", 2}} = disp.skip(live, "a", 2)
    assert {:ok, folded} = disp.skip(live, "a", 1)
    assert folded.departed["a"] == {1, %{}}
    assert folded.by["a"][2] == {0, :signal, :open}
    assert {:ok, [], cleared} = disp.resolved(folded, 0)
    assert cleared.departed["a"] == {2, %{}}

    assert :ok =
             disp.check_trace([
               {:skip, "a", 0},
               {:arrive, "a", :init, 2},
               {:resolved, 0},
               {:skip, "a", 1}
             ])

    assert {:error, {4, {:departed, "a", 2}}} =
             disp.check_trace([
               {:skip, "a", 0},
               {:arrive, "a", :init, 2},
               {:resolved, 0},
               {:skip, "a", 1},
               {:arrive, "a", :init, 2}
             ])

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:error, {:live, "a"}} = disp.drop_key(state, "a")
    assert {:ok, [], gone} = disp.resolved(state, 0)
    assert gone.departed["a"] == {0, %{}}
    assert {:ok, dropped} = disp.drop_key(gone, "a")
    refute Map.has_key?(dropped.departed, "a")
    assert {:open, 1, _restarted} = disp.arrive(dropped, "a", :init, 0)
    assert {:ok, fresh} = disp.drop_key(disp.new(), "missing")
    assert fresh == disp.new()

    assert :ok =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:resolved, 0},
               {:drop, "a"},
               {:arrive, "a", :init, 0},
               {:resolved, 1}
             ])

    assert {:error, {1, {:live, "a"}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:drop, "a"}
             ])

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "b", :init, 0)
    poison = put_in(state, [:departed, "a"], :bad)
    assert {:open, 1, _} = disp.arrive(poison, "b", :init, 1)
    assert {:error, {:state, _}} = disp.arrive(poison, "a", :init, 0)

    old = %{n: 0, by: %{}, id: %{}}
    assert {:error, {:state, ^old}} = disp.arrive(old, "a", :init, 0)

    below = %{disp.new() | departed: %{"a" => {-2, %{}}}}
    assert {:error, {:state, _}} = disp.arrive(below, "a", :init, 0)

    overlap = %{disp.new() | departed: %{"a" => {1, %{1 => true}}}}
    assert {:error, {:state, _}} = disp.arrive(overlap, "a", :init, 3)
  end

  test "skip_below is a monotonic floor over every key", %{disp: disp} do
    state = disp.new()
    assert state.floor == -1
    assert {:ok, once} = disp.skip_below(state, 4)
    assert once.floor == 4
    assert once.departed == %{}
    assert once.by == state.by and once.id == state.id and once.n == state.n
    assert {:ok, ^once} = disp.skip_below(once, 4)
    assert {:ok, ^once} = disp.skip_below(once, 2)
    assert {:ok, ^once} = disp.skip_below(once, 0)
    assert {:error, {:index, -1}} = disp.skip_below(once, -1)
    assert {:error, {:index, 1.5}} = disp.skip_below(once, 1.5)
    assert {:error, {:index, :nope}} = disp.skip_below(once, :nope)

    assert {:error, {:departed, "a", 0}} = disp.arrive(once, "a", :init, 0)
    assert {:error, {:departed, "a", 4}} = disp.arrive(once, "a", :signal, 4)
    assert {:error, {:departed, "b", 4}} = disp.arrive(once, "b", :init, 4)
    assert {:error, {:departed, "b", 1}} = disp.arrive(once, "b", :signal, 1)
    assert {:open, 0, above} = disp.arrive(once, "a", :init, 5)
    assert {:held, 1, above} = disp.arrive(above, "a", :signal, 6)
    assert above.floor == 4
    assert above.by["a"][5] == {0, :init, :open}
    assert above.by["a"][6] == {1, :signal, :held}

    # A restart lost the record. The persisted cursor is the floor.
    assert {:ok, restarted} = disp.skip_below(disp.new(), 10)
    assert restarted.departed == %{}
    assert {:error, {:departed, "a", 10}} = disp.arrive(restarted, "a", :init, 10)
    assert {:error, {:departed, "b", 0}} = disp.arrive(restarted, "b", :signal, 0)
    assert {:open, 0, _} = disp.arrive(restarted, "a", :init, 11)

    stale = %{n: 0, by: %{}, id: %{}, departed: %{}}
    assert {:error, {:state, ^stale}} = disp.skip_below(stale, 0)
    assert {:error, {:state, ^stale}} = disp.arrive(stale, "a", :init, 0)
    bad = %{disp.new() | floor: -2}
    assert {:error, {:state, ^bad}} = disp.skip_below(bad, 0)
    assert {:error, {:state, ^bad}} = disp.arrive(bad, "a", :init, 0)
  end

  test "skip_below compacts departed records and leaves live rows", %{disp: disp} do
    state = disp.new()
    assert {:ok, state} = disp.skip(state, "a", 0)
    assert {:ok, state} = disp.skip(state, "a", 1)
    assert state.departed["a"] == {1, %{}}
    assert {:ok, state} = disp.skip(state, "b", 8)
    assert {:ok, state} = disp.skip(state, "b", 3)
    assert state.departed["b"] == {-1, %{3 => true, 8 => true}}
    assert {:ok, state} = disp.skip(state, "c", 4)
    assert {:open, 0, state} = disp.arrive(state, "d", :init, 2)
    assert {:held, 1, state} = disp.arrive(state, "d", :signal, 4)
    assert {:open, 2, state} = disp.arrive(state, "e", :init, 9)

    assert {:ok, floored} = disp.skip_below(state, 5)
    assert floored.floor == 5
    refute Map.has_key?(floored.departed, "a")
    refute Map.has_key?(floored.departed, "c")
    assert floored.departed["b"] == {5, %{8 => true}}
    assert floored.by["d"][2] == {0, :init, :open}
    assert floored.by["d"][4] == {1, :signal, :held}
    assert floored.by["e"][9] == {2, :init, :open}
    assert floored.id == state.id
    assert {:error, {:duplicate, "d", 2}} = disp.arrive(floored, "d", :init, 2)
    assert {:error, {:duplicate, "d", 4}} = disp.arrive(floored, "d", :signal, 4)
    assert {:error, {:duplicate, "d", 2}} = disp.skip(floored, "d", 2)
    assert {:ok, ^floored} = disp.skip(floored, "d", 1)
    assert {:ok, ^floored} = disp.skip(floored, "a", 5)
    assert {:error, {:departed, "a", 1}} = disp.arrive(floored, "a", :init, 1)
    assert {:error, {:departed, "b", 8}} = disp.arrive(floored, "b", :signal, 8)
    assert {:error, {:departed, "z", 5}} = disp.arrive(floored, "z", :init, 5)
    assert {:open, 3, above} = disp.arrive(floored, "a", :signal, 6)
    assert above.departed["b"] == {5, %{8 => true}}

    assert {:ok, marked} = disp.skip(floored, "a", 7)
    assert marked.departed["a"] == {5, %{7 => true}}
    assert marked.by == floored.by
    assert {:error, {:departed, "a", 7}} = disp.arrive(marked, "a", :signal, 7)

    assert {:ok, [{1, "d", :signal}], released} = disp.resolved(floored, 0)
    assert {:ok, [{1, "d", :signal}], plain} = disp.resolved(state, 0)
    assert released.by == plain.by
    assert released.id == plain.id
    refute Map.has_key?(released.departed, "d")
    assert plain.departed["d"] == {-1, %{2 => true}}
    assert released.by["d"][4] == {1, :signal, :open}
    assert {:ok, [], released} = disp.resolved(released, 1)
    refute Map.has_key?(released.departed, "d")
    assert {:error, {:departed, "d", 2}} = disp.arrive(released, "d", :init, 2)
    assert {:error, {:departed, "d", 4}} = disp.arrive(released, "d", :signal, 4)

    held = floored
    assert {:ok, [], held} = disp.withdraw(held, 1)
    assert held.by["d"][2] == {0, :init, :open}
    refute Map.has_key?(held.by["d"], 4)
    refute Map.has_key?(held.departed, "d")
    assert {:ok, [], held} = disp.resolved(held, 0)
    refute Map.has_key?(held.departed, "d")
    assert held.floor == 5

    assert {:error, {:live, "e"}} = disp.drop_key(floored, "e")
    assert {:ok, [], gone} = disp.resolved(floored, 2)
    assert gone.departed["e"] == {5, %{9 => true}}
    assert {:ok, dropped} = disp.drop_key(gone, "e")
    refute Map.has_key?(dropped.departed, "e")
    assert dropped.floor == 5
    assert {:open, _, _} = disp.arrive(dropped, "e", :init, 9)
    assert {:error, {:departed, "e", 4}} = disp.arrive(dropped, "e", :signal, 4)

    poison = put_in(floored, [:departed, "a"], :bad)
    assert {:ok, ^poison} = disp.skip_below(poison, 5)
    assert {:ok, ^poison} = disp.skip_below(poison, 3)
    assert {:ok, ^poison} = disp.skip(poison, "a", 1)
    assert {:error, {:state, _}} = disp.skip_below(poison, 6)
    assert {:error, {:state, _}} = disp.skip(poison, "a", 8)
  end

  test "a departure above the floor stays exact and folds from the floor", %{disp: disp} do
    state = disp.new()
    assert {:ok, state} = disp.skip(state, "a", 1)
    assert {:ok, state} = disp.skip(state, "a", 4)
    assert state.departed["a"] == {-1, %{1 => true, 4 => true}}
    assert {:ok, state} = disp.skip_below(state, 2)
    assert state.departed["a"] == {2, %{4 => true}}
    assert {:error, {:departed, "a", 1}} = disp.arrive(state, "a", :init, 1)
    assert {:error, {:departed, "a", 2}} = disp.arrive(state, "a", :init, 2)
    assert {:error, {:departed, "b", 2}} = disp.arrive(state, "b", :signal, 2)
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 3)
    assert {:error, {:departed, "a", 4}} = disp.arrive(state, "a", :signal, 4)
    assert {:ok, [], state} = disp.resolved(state, 0)
    assert state.departed["a"] == {4, %{}}
    assert {:error, {:departed, "a", 4}} = disp.arrive(state, "a", :init, 4)
    assert {:open, 1, _} = disp.arrive(state, "a", :init, 5)

    dense = disp.new()
    assert {:ok, dense} = disp.skip_below(dense, 5)
    assert {:open, 0, dense} = disp.arrive(dense, "a", :init, 6)
    assert {:ok, [], dense} = disp.resolved(dense, 0)
    assert dense.departed["a"] == {6, %{}}
    refute Map.has_key?(elem(dense.departed["a"], 1), 6)
    assert {:open, 1, dense} = disp.arrive(dense, "a", :init, 7)
    assert {:ok, [], dense} = disp.resolved(dense, 1)
    assert dense.departed["a"] == {7, %{}}
    assert {:ok, dense} = disp.skip(dense, "a", 9)
    assert dense.departed["a"] == {7, %{9 => true}}
    assert {:error, {:departed, "a", 6}} = disp.arrive(dense, "a", :init, 6)
    assert {:open, 2, _} = disp.arrive(dense, "a", :init, 8)

    covered = disp.new()
    assert {:ok, covered} = disp.skip(covered, "a", 0)
    assert {:ok, covered} = disp.skip(covered, "a", 1)
    assert {:ok, covered} = disp.skip(covered, "a", 2)
    assert covered.departed["a"] == {2, %{}}
    assert {:ok, kept} = disp.skip_below(covered, 0)
    assert kept.departed["a"] == {2, %{}}
    assert {:ok, cleared} = disp.skip_below(kept, 2)
    refute Map.has_key?(cleared.departed, "a")
    assert {:error, {:departed, "a", 2}} = disp.arrive(cleared, "a", :init, 2)
    assert {:open, 0, _} = disp.arrive(cleared, "a", :init, 3)
  end

  test "check_trace replays skip_below", %{disp: disp} do
    assert :ok =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:resolved, 0},
               {:skip_below, 0},
               {:arrive, "b", :init, 1},
               {:resolved, 1}
             ])

    assert {:error, {4, {:departed, "a", 0}}} =
             disp.check_trace([
               {:skip_below, 4},
               {:arrive, "b", :signal, 5},
               {:resolved, 0},
               {:skip_below, 1},
               {:arrive, "a", :init, 0}
             ])

    assert {:error, {0, {:index, -1}}} = disp.check_trace([{:skip_below, -1}])

    assert {:error, {1, {:index, :nope}}} =
             disp.check_trace([{:skip_below, 3}, {:skip_below, :nope}])

    assert :ok =
             disp.check_trace([
               {:skip_below, 3},
               {:skip_below, 3},
               {:skip_below, 1},
               {:arrive, "a", :init, 4},
               {:resolved, 0}
             ])
  end

  test "periodic skip_below bounds a global creation sequence", %{disp: disp} do
    keys = ~w(a b c d)
    live_cap = 4
    span_limit = 6

    {plain, _popen, floored, _fopen, max_weight, plain_gaps} =
      Enum.reduce(0..239, {disp.new(), [], disp.new(), [], 0, 0}, fn i, acc ->
        {plain, popen, floored, fopen, max_w, gaps} = acc
        key = Enum.at(keys, rem(i, length(keys)))
        {:open, id, plain} = disp.arrive(plain, key, :init, i)
        {:open, ^id, floored} = disp.arrive(floored, key, :init, i)
        popen = [{i, id} | popen]
        fopen = [{i, id} | fopen]
        {plain, popen} = drain_global(disp, plain, popen, live_cap, span_limit)
        {floored, fopen} = drain_global(disp, floored, fopen, live_cap, span_limit)
        floored = raise_low_water(disp, floored, fopen, i)
        weight = departed_weight(floored)
        assert weight <= 16
        assert_above_floor(floored)
        {plain, popen, floored, fopen, max(max_w, weight), max(gaps, gap_count(plain))}
      end)

    assert plain.floor == -1
    assert max_weight <= 16
    assert plain_gaps >= 100
    assert plain_gaps > max_weight
    assert floored.floor > 0
    assert {:error, {:departed, "a", 0}} = disp.arrive(floored, "a", :init, 0)
    assert {:open, _, _} = disp.arrive(floored, "z", :init, floored.floor + 1_000)
  end

  test "a later signal opens before its init arrives, and an earlier signal blocks the next",
       %{disp: disp} do
    search = search!()
    g = search.g

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :signal, 1)
    assert {:open, 1, _state} = disp.arrive(state, "a", :init, 0)

    {_assigned, gst} =
      lockstep!(search, [
        {:arrive, "a", :signal, 1, :open, 0},
        {:arrive, "a", :init, 0, :open, 1}
      ])

    signal = Enum.find(g.instances, &(&1.key == "a" and &1.kind == "signal" and &1.index == 1))
    init = Enum.find(g.instances, &(&1.key == "a" and &1.kind == "init"))
    assert match?({:run, _, _, _}, Graph.phase(gst, signal.id))
    assert match?({:run, _, _, _}, Graph.phase(gst, init.id))
    refute Graph.known_at_open?(gst, signal.id, init.id)

    assert Graph.holds?(
             g,
             {:imp, {:opened, "a", "signal"}, {:resolved, "a", "init"}},
             gst
           )

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)
    assert {:held, 2, state} = disp.arrive(state, "a", :signal, 2)
    assert {:ok, [{1, "a", :signal}], state} = disp.resolved(state, 0)
    assert {:held, _} = hold_of(disp, state, 2)
    assert {:ok, [{2, "a", :signal}], _state} = disp.resolved(state, 1)

    lockstep!(search, [
      {:arrive, "a", :init, 0, :open, 0},
      {:arrive, "a", :signal, 1, :held, 1},
      {:arrive, "a", :signal, 2, :held, 2},
      {:resolved, 0, [{1, "a", :signal}]},
      {:resolved, 1, [{2, "a", :signal}]}
    ])
  end

  test "a second init opens at once and the signal waits for both", %{disp: disp} do
    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:open, 1, state} = disp.arrive(state, "a", :init, 1)
    assert {:held, 2, state} = disp.arrive(state, "a", :signal, 2)
    assert {:ok, [], state} = disp.resolved(state, 0)
    assert {:held, _} = hold_of(disp, state, 2)
    assert {:ok, [{2, "a", :signal}], _state} = disp.resolved(state, 1)

    search = search!(two_inits())

    lockstep!(search, [
      {:arrive, "a", :init, 0, :open, 0},
      {:arrive, "a", :init, 1, :open, 1},
      {:arrive, "a", :signal, 2, :held, 2},
      {:resolved, 0, []},
      {:resolved, 1, [{2, "a", :signal}]}
    ])
  end

  test "every dispatcher-accepted sequence over the script is a run of the family graph",
       %{disp: disp} do
    search = search!()
    assert length(search.states) == 171_649
    assert search.transitions == 729_184

    n =
      walk(
        disp,
        search,
        disp.new(),
        search.g.start,
        search.g.instances,
        %{},
        MapSet.new(),
        []
      )

    assert n > 1
  end

  test "the state keeps only the live instances", %{disp: disp} do
    state = disp.new()
    assert {:open, _, state} = disp.arrive(state, "stay", :init, 0)
    live = %{by: state.by, id: state.id}
    n0 = state.n

    state =
      Enum.reduce(1..40, state, fn n, state ->
        assert {:open, id, state} = disp.arrive(state, "a", :init, n)
        assert {:held, sig, state} = disp.arrive(state, "a", :signal, n + 1_000)
        assert {:open, other, state} = disp.arrive(state, "b", :init, n)
        assert {:ok, [{^sig, "a", :signal}], state} = disp.resolved(state, id)
        assert {:ok, [], state} = disp.resolved(state, sig)
        assert {:ok, [], state} = disp.resolved(state, other)
        assert map_size(state.id) == 1
        assert map_size(state.by) == 1
        assert %{by: state.by, id: state.id} == live
        rows = state.by |> Map.values() |> Enum.map(&map_size/1) |> Enum.sum()
        assert map_size(state.id) == rows
        state
      end)

    assert state.n == n0 + 120
    assert state.by["stay"][0] == {0, :init, :open}
    refute inspect(state.by) =~ ":resolved"
    refute inspect(state.id) =~ ":resolved"
  end

  test "a call reads only the key it names", %{disp: disp} do
    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "b", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "b", :signal, 1)

    poisoned =
      state
      |> Map.update!(:by, &Map.put(&1, "a", :poison))
      |> Map.update!(:id, &Map.put(&1, 99, :poison))

    assert {:open, 2, next} = disp.arrive(poisoned, "b", :init, 2)
    assert next.by["a"] == :poison
    assert next.id[99] == :poison
    assert next.by["b"][0] == {0, :init, :open}
    assert next.by["b"][2] == {2, :init, :open}

    assert {:ok, [{1, "b", :signal}], back} = disp.resolved(next, 0)
    assert back.by["a"] == :poison
    assert back.id[99] == :poison
    refute Map.has_key?(back.id, 0)
    assert back.by["b"][1] == {1, :signal, :open}
    assert back.by["b"][2] == {2, :init, :open}

    assert {:error, {:state, _}} = disp.arrive(poisoned, "a", :init, 0)
    assert {:error, {:state, _}} = disp.resolved(poisoned, 99)
    assert {:error, {:held, 1}} = disp.resolved(poisoned, 1)

    dirty = put_in(state, [:by, "b", 9], :poison)
    assert {:open, _, kept} = disp.arrive(dirty, "b", :init, 3)
    assert kept.by["b"][9] == :poison
    assert {:error, {:held, 1}} = disp.resolved(dirty, 1)
    assert {:error, {:state, _}} = disp.resolved(dirty, 0)
    assert {:error, {:state, _}} = disp.arrive(dirty, "b", :signal, 4)
  end

  test "finish resolves the instance on the session's end", %{
    disp: disp,
    parent: parent,
    src: src
  } do
    assert src =~ "def new, do: %{n: 0, by: %{}, id: %{}, departed: %{}, floor: -1}"
    assert src =~ "def skip(state, key, index)"
    assert src =~ "def drop_key(state, key)"
    assert src =~ "def skip_below(state, index)"
    assert src =~ "def withdraw(state, id)"
    assert src =~ "def finish(session_state, family_state, id)"
    assert src =~ "def finish(session_state, step, family_state, id)"
    assert src =~ "defp party(:server)"
    assert src =~ "{:error, {:resolved, id}}"

    server = Module.concat(parent, ServerWait)
    task = Module.concat(parent, TaskWork)
    assert function_exported?(server, :finish, 3)
    assert function_exported?(server, :finish, 4)
    assert function_exported?(task, :finish, 3)
    assert function_exported?(task, :finish, 4)

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)

    assert {:ok, [{1, "a", :signal}], done} = server.finish(server.init(), :down, state, 0)
    assert {:error, {:unknown, 0}} = disp.resolved(done, 0)
    assert {:ok, [], _} = disp.resolved(done, 1)

    assert {:ok, [{1, "a", :signal}], _} = server.finish(server.init(), {:recv, :ok}, state, 0)
    {:ok, reported} = server.recv(server.init(), :ok)
    assert server.done?(reported)
    assert {:ok, [{1, "a", :signal}], _} = server.finish(reported, state, 0)

    assert {:error, _} = server.finish(server.init(), {:send, :ok}, state, 0)
    assert {:error, _} = server.finish(server.init(), {:recv, :nope}, state, 0)
    assert {:error, {:step, :nope}} = server.finish(server.init(), :nope, state, 0)
    assert {:error, _} = server.finish(:nope, state, 0)
    assert {:error, _} = server.finish(:nope, :down, state, 0)
    assert {:error, {:held, 1}} = server.finish(server.init(), :down, state, 1)
    assert {:error, {:unknown, 9}} = server.finish(server.init(), :down, state, 9)
    assert {:ok, [{1, "a", :signal}], _} = disp.resolved(state, 0)

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:ok, [], freed} = task.finish(task.init(), {:send, :ok}, state, 0)
    assert {:error, {:unknown, 0}} = disp.resolved(freed, 0)
    assert {:error, _} = task.finish(task.init(), :down, state, 0)
    assert {:ok, [], _} = disp.resolved(state, 0)
  end

  test "check_trace names an instance whose session finished without resolved", %{disp: disp} do
    trace = [
      {:arrive, "a", :init, 0},
      {:arrive, "a", :signal, 1},
      {:arrive, "b", :init, 0},
      {:server, 0, :down},
      {:resolved, 0},
      {:task, 1, {:send, :ok}},
      {:resolved, 1},
      {:server, 2, {:recv, :ok}},
      {:resolved, 2}
    ]

    assert :ok = disp.check_trace(trace)

    leaked = [
      {:arrive, "a", :init, 0},
      {:arrive, "a", :signal, 1},
      {:arrive, "b", :init, 0},
      {:server, 0, :down}
    ]

    assert {:error, {:unresolved, 0, "a", :init}} = disp.check_trace(leaked)

    assert {:error, {:unresolved, 0, "a", :init}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:task, 0, {:send, :ok}}
             ])

    assert {:error, {0, {:unknown, 4}}} = disp.check_trace([{:server, 4, :down}])

    assert {:error, {2, {:held, 1}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:arrive, "a", :signal, 1},
               {:server, 1, {:recv, :ok}}
             ])

    assert {:error, {1, {:party, :nope}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:nope, 0, :down}
             ])
  end

  test "down into stop is not a resolved instance" do
    {disp, parent, _src} =
      compile_src!("""
      data Event : Type where
        init : Event

      data Report : Type where
        ok : Report

      session task-work := send Report end
      session server-wait := recv Report end

      conform task : task-work := put ok done

      conform server : server-wait :=
        get (r : Report) done
        fail
          stop

      meet hold : server with task may fail buffer 1

      family slots : hold per key of Event
        init never held
      """)

    server = Module.concat(parent, ServerWait)
    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:error, {:unfinished, :stop}} = server.finish(server.init(), :down, state, 0)
    assert {:ok, [], _} = disp.resolved(state, 0)

    assert {:error, {2, {:unfinished, 0}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:server, 0, :down},
               {:resolved, 0}
             ])

    assert :ok =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:server, 0, :down}
             ])
  end

  test "a send then a death resolves only when the trace says so" do
    {disp, parent, _src} =
      compile_src!("""
      data Event : Type where
        init : Event

      data Report : Type where
        ok : Report

      session task-work := recv Nat (send Report end)
      session server-work := send Nat (recv Report end)

      conform task : task-work :=
        get (n : Nat) (put ok done)

      conform server : server-work :=
        put 0 (get (r : Report) done fail done)

      meet wire : server with task may fail buffer 1

      family slots : wire per key of Event
        init never held
      """)

    server = Module.concat(parent, ServerWork)
    opened = [{:arrive, "a", :init, 0}, {:server, 0, {:send, 0}}]

    assert {:error, {2, {:unfinished, 0}}} = disp.check_trace(opened ++ [{:resolved, 0}])

    assert {:error, {:unresolved, 0, "a", :init}} =
             disp.check_trace(opened ++ [{:server, 0, {:recv, :ok}}])

    assert :ok = disp.check_trace(opened ++ [{:server, 0, :down}, {:resolved, 0}])
    assert :ok = disp.check_trace(opened ++ [{:server, 0, {:recv, :ok}}, {:resolved, 0}])

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:error, {:unfinished, _}} = server.finish(server.init(), {:send, 0}, state, 0)
    assert {:ok, [], _} = disp.resolved(state, 0)
    {:ok, mid} = server.send(server.init(), 0)
    assert {:ok, [], freed} = server.finish(mid, :down, state, 0)
    assert {:error, {:unknown, 0}} = disp.resolved(freed, 0)
    assert {:ok, [], _} = server.finish(mid, {:recv, :ok}, state, 0)
  end

  test "a meeting still in progress is not unresolved" do
    {disp, _parent, _src} =
      compile_src!("""
      data Event : Type where
        init : Event

      data Report : Type where
        ok : Report

      session task-work := recv Nat (send Report end)
      session server-work := send Nat (recv Report end)

      conform task : task-work :=
        get (n : Nat) (put ok done)

      conform server : server-work :=
        put 0 (get (r : Report) done fail done)

      meet wire : server with task may fail buffer 1

      family slots : wire per key of Event
        init never held
      """)

    # The server has reached done. The task has received and has not sent.
    open = [
      {:arrive, "a", :init, 0},
      {:server, 0, {:send, 0}},
      {:task, 0, {:recv, 0}},
      {:server, 0, {:recv, :ok}}
    ]

    assert :ok = disp.check_trace(open)
    assert {:error, {4, {:unfinished, 0}}} = disp.check_trace(open ++ [{:resolved, 0}])

    done = open ++ [{:task, 0, {:send, :ok}}]
    assert {:error, {:unresolved, 0, "a", :init}} = disp.check_trace(done)
    assert :ok = disp.check_trace(done ++ [{:resolved, 0}])
  end

  test "finish refuses an end two families share and does not resolve" do
    {disp, parent, src} =
      compile_src!("""
      data Event : Type where
        init : Event

      data Report : Type where
        ok : Report

      session server-wait := recv Report end
      session task-work := send Report end
      session peer-work := send Report end

      conform server : server-wait :=
        get (r : Report) done
        fail
          done

      conform other : server-wait :=
        get (r : Report) done
        fail
          done

      conform task : task-work := put ok done

      conform peer : peer-work := put ok done

      meet slot : server with task may fail buffer 1

      meet side : other with peer may fail buffer 1

      family slots : slot per key of Event
        init never held

      family spare : side per key of Event
        init never held
      """)

    form = "finish(family_state, id, session_state, step)"
    assert src =~ "{:error, {:family, [:Slots, :Spare], #{inspect(form)}}}"

    server = Module.concat(parent, ServerWait)
    task = Module.concat(parent, TaskWork)
    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)

    assert {:error, {:family, [:Slots, :Spare], ^form}} =
             server.finish(server.init(), {:recv, :ok}, state, 0)

    assert {:ok, [], _} = disp.resolved(state, 0)

    {:ok, done} = server.recv(server.init(), :ok)
    assert server.done?(done)
    assert {:error, {:family, [:Slots, :Spare], ^form}} = server.finish(done, state, 0)
    assert {:error, {:family, [:Slots, :Spare], ^form}} = server.finish(done, state, 0, :rerun)
    assert {:ok, [], _} = disp.resolved(state, 0)

    assert {:ok, [], freed} = task.finish(task.init(), {:send, :ok}, state, 0)
    assert {:error, {:unknown, 0}} = disp.resolved(freed, 0)
  end

  test "two families on one session finish apart" do
    {_disp, parent, _src} =
      compile_parent!("""
      data Event : Type where
        init : Event
        signal : Event

      data Command : Type where
        pause : Command
        resume : Command

      data Report : Type where
        ok : Report

      session task-work := send Report end
      session server-wait := recv Report end

      conform task : task-work := put ok done

      conform server : server-wait :=
        get (r : Report) done
        fail
          done

      meet slot : server with task may fail buffer 1

      family events : slot per key of Event
        init never held
        signal held while earlier unresolved

      family commands : slot per key of Command
        pause held while earlier unresolved
        resume held while earlier unresolved
      """)

    events = Module.concat(parent, Events)
    commands = Module.concat(parent, Commands)
    server = Module.concat(parent, ServerWait)
    form = "finish(family_state, id, session_state, step)"

    es = events.new()
    cs = commands.new()
    assert {:open, 0, es} = events.arrive(es, "wf", :init, 0)
    assert {:held, 1, es} = events.arrive(es, "wf", :signal, 1)
    assert {:open, 0, cs} = commands.arrive(cs, "wf", :pause, 0)
    assert {:held, 1, cs} = commands.arrive(cs, "wf", :resume, 1)

    assert {:error, {:family, [:Events, :Commands], ^form}} =
             server.finish(server.init(), :down, es, 0)

    assert {:error, {:family, [:Events, :Commands], ^form}} =
             server.finish(server.init(), :down, es, 0, :rerun)

    assert {:error, {:held, 1}} = events.resolved(es, 1)
    assert {:error, {:held, 1}} = commands.resolved(cs, 1)

    assert {:ok, [{1, "wf", :signal}], es} = events.finish(es, 0, server.init(), :down)
    assert {:error, {:unknown, 0}} = events.resolved(es, 0)
    assert {:ok, [], _} = events.resolved(es, 1)
    assert {:error, {:held, 1}} = commands.resolved(cs, 1)
    assert cs.by["wf"][0] == {0, :pause, :open}
    assert cs.by["wf"][1] == {1, :resume, :held}

    assert {:ok, [{1, "wf", :resume}], cs} = commands.finish(cs, 0, server.init(), :down)
    assert {:error, {:unknown, 0}} = commands.resolved(cs, 0)
    assert {:ok, [], _} = commands.resolved(cs, 1)
    assert es.by["wf"][1] == {1, :signal, :open}
  end

  test "a rerun keeps the row and the signal opens only when the init resolves", %{
    disp: disp,
    parent: parent
  } do
    server = Module.concat(parent, ServerWait)
    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)
    assert function_exported?(disp, :finish, 3)
    assert function_exported?(disp, :finish, 4)
    assert function_exported?(disp, :finish, 5)

    assert {:error, {:unfinished, _}} = disp.finish(state, 0, server.init(), :rerun)
    assert {:error, {:duplicate, "a", 0}} = disp.arrive(state, "a", :init, 0)
    assert {:error, {:unknown, 9}} = disp.finish(state, 9, server.init(), :down, :rerun)
    assert {:error, {:unknown, 9}} = server.finish(server.init(), :down, state, 9, :rerun)
    assert {:error, {:held, 1}} = disp.finish(state, 1, server.init(), :down, :rerun)

    assert {:ok, [], rerun} = disp.finish(state, 0, server.init(), :down, :rerun)
    assert rerun.by == state.by
    assert rerun.id == state.id
    assert rerun.departed == state.departed
    assert {:error, {:duplicate, "a", 0}} = disp.arrive(rerun, "a", :init, 0)
    assert {:error, {:held, 1}} = disp.resolved(rerun, 1)
    assert {:ok, [], again} = server.finish(server.init(), :down, rerun, 0, :rerun)
    assert again.by["a"][0] == {0, :init, :open}
    assert again.by["a"][1] == {1, :signal, :held}

    assert {:ok, [{1, "a", :signal}], opened} = disp.finish(again, 0, server.init(), {:recv, :ok})
    assert {:error, {:unknown, 0}} = disp.resolved(opened, 0)
    assert {:ok, [], _} = disp.resolved(opened, 1)

    death_rerun_success = [
      {:arrive, "a", :init, 0},
      {:arrive, "a", :signal, 1},
      {:server, 0, :down},
      {:rerun, 0},
      {:server, 0, {:recv, :ok}},
      {:resolved, 0},
      {:server, 1, {:recv, :ok}},
      {:resolved, 1}
    ]

    assert :ok = disp.check_trace(death_rerun_success)

    assert {:error, {4, {:held, 1}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:arrive, "a", :signal, 1},
               {:server, 0, :down},
               {:rerun, 0},
               {:server, 1, {:recv, :ok}}
             ])

    assert {:error, {:unresolved, 0, "a", :init}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:arrive, "a", :signal, 1},
               {:server, 0, :down},
               {:rerun, 0},
               {:server, 0, :down}
             ])

    assert :ok =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:server, 0, :down},
               {:rerun, 0},
               {:server, 0, :down},
               {:rerun, 0},
               {:server, 0, {:recv, :ok}},
               {:resolved, 0}
             ])

    assert {:error, {1, {:unfinished, 0}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:rerun, 0}
             ])

    assert {:error, {2, {:held, 1}}} =
             disp.check_trace([
               {:arrive, "a", :init, 0},
               {:arrive, "a", :signal, 1},
               {:rerun, 1}
             ])

    assert {:error, {0, {:unknown, 4}}} = disp.check_trace([{:rerun, 4}])
  end

  test "finish/3 and finish/4 with :rerun take a session that is already at done", %{
    disp: disp,
    parent: parent
  } do
    server = Module.concat(parent, ServerWait)
    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :signal, 1)
    {:ok, done} = server.recv(server.init(), :ok)
    assert server.done?(done)

    assert {:ok, [], kept} = disp.finish(state, 0, done, :rerun)
    assert kept.by["a"][0] == {0, :init, :open}
    assert kept.by["a"][1] == {1, :signal, :held}
    assert {:error, {:held, 1}} = disp.resolved(kept, 1)

    assert {:ok, [{1, "a", :signal}], opened} = disp.finish(kept, 0, done)
    assert {:error, {:unknown, 0}} = disp.resolved(opened, 0)
    assert {:ok, [], _} = disp.resolved(opened, 1)
  end

  test "a bad outcome is refused on the family and on the session", %{
    disp: disp,
    parent: parent
  } do
    server = Module.concat(parent, ServerWait)
    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    session = server.init()

    assert {:error, {:outcome, :nope}} = disp.finish(state, 0, session, :nope)
    assert {:error, {:outcome, :nope}} = disp.finish(state, 0, session, :down, :nope)
    assert {:error, {:outcome, :nope}} = server.finish(session, state, 0, :nope)
    assert {:error, {:outcome, :nope}} = server.finish(session, :down, state, 0, :nope)
    assert state.by["a"][0] == {0, :init, :open}
  end

  defp hold_of(disp, state, id) do
    case disp.resolved(state, id) do
      {:error, {:held, ^id}} -> {:held, id}
      other -> flunk("expected the instance to stay held, got #{inspect(other)}")
    end
  end

  defp walk(disp, search, dst, gst, remaining, assigned, resolved, trace) do
    assert {:error, {:unknown, _}} = disp.resolved(dst, -1)

    arrived =
      Enum.reduce(remaining, 0, fn inst, acc ->
        kind = String.to_atom(inst.kind)

        case disp.arrive(dst, inst.key, kind, inst.index) do
          {phase, id, dst2} when phase in [:open, :held] ->
            tag = if phase == :open, do: {:open, inst.id}, else: {:hold, inst.id}

            case step_to(search, gst, tag) do
              {:ok, gst2} ->
                left = Enum.reject(remaining, &(&1.id == inst.id))
                step = {:arrive, inst.key, kind, inst.index, phase}

                acc +
                  walk(
                    disp,
                    search,
                    dst2,
                    gst2,
                    left,
                    Map.put(assigned, id, inst),
                    resolved,
                    [step | trace]
                  )

              {:error, tags} ->
                flunk(mismatch(trace, tag, tags))
            end

          other ->
            flunk("dispatcher refused #{inspect(inst)} after #{show(trace)}: #{inspect(other)}")
        end
      end)

    finished =
      Enum.reduce(assigned, 0, fn {id, inst}, acc ->
        if MapSet.member?(resolved, id) do
          acc
        else
          case disp.resolved(dst, id) do
            {:error, _} ->
              case Graph.phase(gst, inst.id) do
                :held ->
                  acc

                other ->
                  flunk(
                    "dispatcher refused a running #{who(inst)} after #{show(trace)}, graph phase #{inspect(other)}"
                  )
              end

            {:ok, released, dst2} ->
              case realize(search, gst, inst.id) do
                {:ok, gst2, opened} ->
                  got = MapSet.new(released, &graph_id(assigned, &1))

                  if got == MapSet.new(opened) do
                    step = {:resolved, id, released}

                    acc +
                      walk(
                        disp,
                        search,
                        dst2,
                        gst2,
                        remaining,
                        assigned,
                        MapSet.put(resolved, id),
                        [step | trace]
                      )
                  else
                    flunk(
                      "release mismatch after #{show(trace)}: dispatcher #{inspect(released)} graph #{inspect(opened)}"
                    )
                  end

                :error ->
                  flunk(
                    "accepted resolve of #{who(inst)} is not a graph run after #{show(trace)}"
                  )
              end
          end
        end
      end)

    if arrived + finished == 0, do: 1, else: arrived + finished
  end

  defp lockstep!(search, trace) do
    Enum.reduce(trace, {%{}, search.g.start}, fn step, {assigned, gst} ->
      case step do
        {:arrive, key, kind, index, phase, id} ->
          inst = find_inst!(search.g, key, kind, index)
          tag = if phase == :open, do: {:open, inst.id}, else: {:hold, inst.id}

          case step_to(search, gst, tag) do
            {:ok, gst} -> {Map.put(assigned, id, inst), gst}
            {:error, tags} -> flunk(mismatch(trace, tag, tags))
          end

        {:resolved, id, released} ->
          inst = Map.fetch!(assigned, id)

          case realize(search, gst, inst.id) do
            {:ok, gst, opened} ->
              got = MapSet.new(released, &graph_id(assigned, &1))

              assert MapSet.new(opened) == got,
                     "release mismatch: dispatcher #{inspect(released)} graph #{inspect(opened)}"

              {assigned, gst}

            :error ->
              flunk("resolve of #{who(inst)} is not a graph run")
          end
      end
    end)
  end

  defp find_inst!(g, key, kind, index) do
    kind = Atom.to_string(kind)

    Enum.find(g.instances, &(&1.key == key and &1.kind == kind and &1.index == index)) ||
      flunk("script has no #{key} #{kind} #{index}")
  end

  defp graph_id(assigned, {id, key, kind}) do
    inst = Map.fetch!(assigned, id)
    assert inst.key == key
    assert inst.kind == Atom.to_string(kind)
    inst.id
  end

  defp realize(search, state, gid) do
    case bfs(search, gid, MapSet.new(), [state]) do
      nil ->
        :error

      resolved ->
        ids = held_opens(search, resolved)

        case apply_opens(search, resolved, Enum.sort(ids)) do
          {:ok, dest} -> {:ok, dest, ids}
          :error -> :error
        end
    end
  end

  defp bfs(_search, _gid, _seen, []), do: nil

  defp bfs(search, gid, seen, [state | rest]) do
    if MapSet.member?(seen, state) do
      bfs(search, gid, seen, rest)
    else
      steps = steps_of(search, state)

      case resolving(steps, gid) do
        {_tag, dest} ->
          dest

        nil ->
          more =
            for {tag, dest} <- steps,
                match?({:meet, ^gid, _}, tag) or tag == {:retry, gid},
                do: dest

          bfs(search, gid, MapSet.put(seen, state), rest ++ more)
      end
    end
  end

  defp resolving(steps, gid) do
    Enum.find(steps, fn {tag, _} -> tag == {:resolve, gid} end) ||
      Enum.find(steps, fn {tag, _} -> tag == {:give_up, gid} end)
  end

  defp held_opens(search, state) do
    steps = steps_of(search, state)

    for inst <- search.g.instances,
        Graph.phase(state, inst.id) == :held,
        Enum.any?(steps, fn {tag, _} -> tag == {:open, inst.id} end),
        do: inst.id
  end

  defp apply_opens(_search, state, []), do: {:ok, state}

  defp apply_opens(search, state, [id | rest]) do
    case step_to(search, state, {:open, id}) do
      {:ok, state} -> apply_opens(search, state, rest)
      {:error, _} -> :error
    end
  end

  defp step_to(search, state, tag) do
    case Enum.find(steps_of(search, state), fn {t, _} -> t == tag end) do
      {_, dest} -> {:ok, dest}
      nil -> {:error, steps_of(search, state) |> Enum.map(&elem(&1, 0))}
    end
  end

  defp steps_of(search, state) do
    case Map.fetch(search.edges, state) do
      {:ok, steps} -> steps
      :error -> Graph.edges(search.g, state)
    end
  end

  defp mismatch(trace, tag, tags) do
    "graph has no #{inspect(tag)} after #{show(trace)}; edges #{inspect(tags)}"
  end

  defp show(trace) when is_list(trace), do: inspect(Enum.reverse(trace))

  defp who(inst), do: "#{inst.key} #{inst.kind} #{inst.index}"

  defp drain_global(disp, state, opens, live_cap, span_limit) do
    span = open_span(opens)

    cond do
      length(opens) <= live_cap and span < span_limit ->
        {state, opens}

      span >= span_limit and opens != [] ->
        {{_index, id}, rest} = pop_oldest(opens)
        assert {:ok, [], state} = disp.resolved(state, id)
        drain_global(disp, state, rest, live_cap, span_limit)

      length(opens) > live_cap ->
        {{_index, id}, rest} = pop_newest(opens)
        assert {:ok, [], state} = disp.resolved(state, id)
        drain_global(disp, state, rest, live_cap, span_limit)

      true ->
        {state, opens}
    end
  end

  defp raise_low_water(disp, state, [], arrived) do
    assert {:ok, state} = disp.skip_below(state, arrived)
    state
  end

  defp raise_low_water(disp, state, opens, _arrived) do
    floor_ix = Enum.min(Enum.map(opens, &elem(&1, 0))) - 1

    if floor_ix >= 0 do
      assert {:ok, state} = disp.skip_below(state, floor_ix)
      state
    else
      state
    end
  end

  defp open_span([]), do: 0

  defp open_span(opens) do
    idxs = Enum.map(opens, &elem(&1, 0))
    Enum.max(idxs) - Enum.min(idxs)
  end

  defp pop_oldest(opens) do
    oldest = Enum.min_by(opens, &elem(&1, 0))
    {oldest, List.delete(opens, oldest)}
  end

  defp pop_newest(opens) do
    newest = Enum.max_by(opens, &elem(&1, 0))
    {newest, List.delete(opens, newest)}
  end

  defp departed_weight(state) do
    Enum.reduce(state.departed, 0, fn {_key, {_prefix, gaps}}, acc ->
      acc + 1 + map_size(gaps)
    end)
  end

  defp gap_count(state) do
    Enum.reduce(state.departed, 0, fn {_key, {_prefix, gaps}}, acc ->
      acc + map_size(gaps)
    end)
  end

  defp assert_above_floor(state) do
    for {_key, {prefix, gaps}} <- state.departed do
      assert prefix >= state.floor
      assert prefix > state.floor or map_size(gaps) > 0

      Enum.each(gaps, fn {ix, _} ->
        assert ix > state.floor
        assert ix > prefix
      end)
    end
  end

  defp two_inits do
    [
      %{id: 0, key: "a", kind: "init", index: 0},
      %{id: 1, key: "a", kind: "init", index: 1},
      %{id: 2, key: "a", kind: "signal", index: 2}
    ]
  end

  defp search!(instances \\ nil) do
    src = File.read!(@path)
    assert {:ok, book} = Muro.Parser.parse(src)
    family = Enum.find(book, &(&1.kind == :family))
    opts = if instances, do: [instances: instances], else: []
    assert {:ok, search} = Graph.prepare(book, family, opts)
    search
  end

  defp compile!(path) do
    {disp, parent, src} = compile_parent_path!(path, Slots)
    assert src =~ "defmodule Slots do"
    {disp, parent, src}
  end

  defp compile_src!(src) do
    {disp, parent, src} = compile_parent!(src, Slots)
    assert src =~ "defmodule Slots do"
    {disp, parent, src}
  end

  defp compile_parent!(src, family \\ nil) do
    dir = System.tmp_dir!() |> Path.join("muro-fsm-fam-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "book.muro")
    File.write!(path, src)
    compile_parent_path!(path, family)
  end

  defp compile_parent_path!(path, family) do
    parent = Module.concat(["FsmFam#{System.unique_integer([:positive])}"])
    assert {:ok, src} = Muro.emit_fsm(path, parent)
    assert src =~ "def new"
    assert src =~ "def arrive"
    assert src =~ "def resolved"
    assert src =~ "def check_trace"
    refute src =~ "GenServer"
    refute src =~ "Muro."
    {mods, diags} = Code.with_diagnostics(fn -> Code.compile_string(src) end)

    warnings =
      Enum.filter(diags, &(match?(%{severity: :warning}, &1) or match?({:warning, _}, &1)))

    assert warnings == [], inspect(warnings, limit: 20)
    assert parent in Enum.map(mods, &elem(&1, 0))
    disp = if family, do: Module.concat(parent, family), else: nil
    {disp, parent, src}
  end

  defp purge_fam do
    for {mod, _} <- :code.all_loaded(),
        name = Atom.to_string(mod),
        String.starts_with?(name, "Elixir.FsmFam") do
      :code.purge(mod)
      :code.delete(mod)
    end
  end
end

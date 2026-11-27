defmodule Muro.FamilyRevertTest do
  use ExUnit.Case, async: false

  alias Muro.{Check, Parser}
  alias Muro.Family.{Graph, Step}

  @moduletag timeout: 180_000

  @rollback "examples/keyed-rollback.muro"
  @release "examples/keyed-release.muro"

  @meet """
  data Report : Type where
    ok : Report
  session task-work := send Report end
  session server-wait := recv Report end
  conform task : task-work := put ok done
  conform server : server-wait :=
    get (r : Report) done
  meet slot : server with task buffer 1
  """

  @front %{
    {:mark, :revert} => true,
    front: :never,
    worker: {:named, %{while: [], until: [:front]}}
  }

  @earlier %{
    {:mark, :revert} => true,
    init: :never,
    signal: :earlier
  }

  @any %{
    {:mark, :revert} => true,
    slot: :any
  }

  test "may revert is a family mark, either order, and nowhere else" do
    both = fn marks ->
      src =
        kinds(~w(front worker)) <>
          @meet <>
          """
          family rollout : slot per key of Step #{marks}
            front never held
            worker held until front resolved
          """

      assert {:ok, book} = Parser.parse(src)
      family = Enum.find(book, &(&1.kind == :family))
      assert family.revert
      assert family.redeliver

      assert Muro.Family.line(family) ==
               "family rollout: slot per key of Step may redeliver may revert"
    end

    both.("may revert may redeliver")
    both.("may redeliver may revert")

    only =
      kinds(~w(front)) <>
        @meet <>
        """
        family rollout : slot per key of Step may revert
          front never held
        """

    assert {:ok, book} = Parser.parse(only)
    family = Enum.find(book, &(&1.kind == :family))
    assert family.revert
    refute family.redeliver

    assert parse_error("may revert\n") =~ "may revert is only a mark on a family"

    assert parse_error(
             kinds(~w(front)) <>
               @meet <>
               """
               family rollout : slot per key of Step
                 front never held
               may revert
               """
           ) =~ "may revert is only a mark on a family"

    assert parse_error(
             kinds(~w(front)) <>
               @meet <>
               """
               family rollout : slot per key of Step may revert may revert
                 front never held
               """
           ) =~ "duplicate family mark may revert"

    assert parse_error(
             kinds(~w(front)) <>
               @meet <>
               """
               family rollout : slot per key of Step may revert skip
                 front never held
               """
           ) =~ "skip is a mark on a contract entry, not on may revert"

    assert parse_error(
             kinds(~w(front)) <>
               @meet <>
               """
               family rollout : slot per key of Step
                 front never held
               contract rollout : may revert
               """
           ) =~ "may revert is a mark on a family, not a contract entry"

    assert parse_error(
             kinds(~w(front)) <>
               @meet <>
               """
               family rollout : slot per key of Step
                 front never held
               temporal t : rollout := always true relies may revert
               """
           ) =~ "may revert is a mark, not a contract a formula relies on"

    assert {:ok, _} = Parser.parse("def revert : run Nat := 0\n")
  end

  test "Step.revert keeps the row open and refuses every other phase" do
    assert Step.empty() == %{next: 0, tick: 0, rows: [], departed: %{}, floor: -1}
    refute Map.has_key?(Step.empty(), :kinds)
    refute Map.has_key?(Step.empty(), :withdrawn)

    assert {:error, {:unmarked, :revert}} = Step.revert(:bad, 0, %{front: :never})
    assert {:error, {:unmarked, :revert}} = Step.revert(Step.empty(), 0, :no)
    assert {:error, {:state, :bad}} = Step.revert(:bad, 0, @front)
    assert {:error, {:state, %{floor: :x}}} = Step.revert(%{floor: :x, rows: []}, 0, @front)
    assert {:error, {:unknown, -1}} = Step.revert(Step.empty(), -1, @front)
    assert {:error, {:unknown, 0}} = Step.revert(Step.empty(), 0, @front)
    assert {:error, {:unknown, "no"}} = Step.revert(Step.empty(), "no", @front)

    st = Step.empty()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :front, 0, @front)
    opened = Enum.find(st.rows, &(&1.id == 0))
    assert {:error, {:opened, 0}} = Step.revert(st, 0, @front)
    assert {:ok, [], st} = Step.resolve(st, 0, @front)
    assert Step.view(st) == [{"a", 0, 0, :front, :resolved}]
    assert st.kinds == %{"a" => %{front: true}}
    assert st.departed == %{}
    assert {:error, {:resolved, 0}} = Step.resolve(st, 0, @front)
    assert {:error, {:resolved, 0}} = Step.touch(st, 0)
    assert {:error, {:unknown, 0}} = Step.waiting_on(st, 0, @front)
    assert {:error, {:duplicate, "a", 0}} = Step.skip(st, "a", 0)

    assert {:ok, st} = Step.revert(st, 0, @front)
    [row] = st.rows
    assert row.phase == :open
    assert row.id == 0
    assert row.born == opened.born
    assert row.opened_at == opened.opened_at
    assert st.kinds == %{}
    assert {:ok, [], st} = Step.resolve(st, 0, @front)
    assert st.kinds == %{"a" => %{front: true}}
  end

  test "an open or resolved dependent blocks revert, and a held one does not" do
    st = Step.empty()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :front, 0, @front)
    assert {:ok, :held, 1, st} = Step.arrive(st, "a", :worker, 1, @front)
    assert {:ok, [{1, "a", :worker}], st} = Step.resolve(st, 0, @front)
    assert {:ok, [], st} = Step.resolve(st, 1, @front)
    assert {:error, {:held_by, [1]}} = Step.revert(st, 0, @front)
    assert {:ok, st} = Step.revert(st, 1, @front)
    assert Step.view(st) == [{"a", 0, 0, :front, :resolved}, {"a", 1, 1, :worker, :open}]
    assert {:error, {:held_by, [1]}} = Step.revert(st, 0, @front)

    st = Step.empty()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :front, 0, @front)
    assert {:ok, [], st} = Step.resolve(st, 0, @front)
    assert {:ok, st} = Step.revert(st, 0, @front)
    assert st.kinds == %{}
    assert {:ok, :held, 1, st} = Step.arrive(st, "a", :worker, 1, @front)
    assert {:ok, %{kinds: [:front], ids: [0]}} = Step.waiting_on(st, 1, @front)
    assert {:error, {:opened, 0}} = Step.revert(st, 0, @front)
    assert Step.view(st) == [{"a", 0, 0, :front, :open}, {"a", 1, 1, :worker, :held}]
    assert {:ok, [{1, "a", :worker}], _} = Step.resolve(st, 0, @front)

    st = Step.empty()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :front, 0, @front)
    assert {:ok, :open, 1, st} = Step.arrive(st, "a", :front, 1, @front)
    assert {:ok, [], st} = Step.resolve(st, 0, @front)
    assert {:ok, [], st} = Step.resolve(st, 1, @front)
    assert {:ok, st} = Step.revert(st, 0, @front)
    assert st.kinds == %{"a" => %{front: true}}
    assert {:ok, st} = Step.revert(st, 1, @front)
    assert st.kinds == %{}
  end

  test "earlier and any block only from a later open or resolved row" do
    st = Step.empty()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :init, 0, @earlier)
    assert {:ok, [], st} = Step.resolve(st, 0, @earlier)
    assert {:ok, :open, 1, st} = Step.arrive(st, "a", :signal, 1, @earlier)
    assert {:ok, [], st} = Step.resolve(st, 1, @earlier)
    assert {:error, {:held_by, [1]}} = Step.revert(st, 0, @earlier)
    assert {:ok, st} = Step.revert(st, 1, @earlier)
    assert {:error, {:held_by, [1]}} = Step.revert(st, 0, @earlier)

    held_behind = %{
      {:mark, :revert} => true,
      front: :never,
      schema: :never,
      worker: {:named, %{while: [], until: [:front, :schema]}}
    }

    st = Step.empty()
    assert {:ok, :held, 0, st} = Step.arrive(st, "a", :worker, 0, held_behind)
    assert {:ok, :open, 1, st} = Step.arrive(st, "a", :front, 1, held_behind)
    assert {:ok, [], st} = Step.resolve(st, 1, held_behind)
    assert Step.view(st) == [{"a", 0, 0, :worker, :held}, {"a", 1, 1, :front, :resolved}]
    assert {:ok, st} = Step.revert(st, 1, held_behind)
    assert Step.view(st) == [{"a", 0, 0, :worker, :held}, {"a", 1, 1, :front, :open}]
    assert st.kinds == %{}

    st = Step.empty()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :slot, 0, @any)
    assert {:ok, :held, 1, st} = Step.arrive(st, "a", :slot, 1, @any)
    assert {:ok, [{1, "a", :slot}], st} = Step.resolve(st, 0, @any)
    assert {:ok, [], st} = Step.resolve(st, 1, @any)
    assert {:error, {:held_by, [1]}} = Step.revert(st, 0, @any)
    assert {:ok, st} = Step.revert(st, 1, @any)
    assert {:error, {:held_by, [1]}} = Step.revert(st, 0, @any)
    assert {:error, {:opened, 1}} = Step.revert(st, 1, @any)
  end

  test "withdraw is remembered until drop_key or skip_below prunes it" do
    st = Step.empty()
    assert {:ok, :held, 0, st} = Step.arrive(st, "a", :worker, 0, @front)
    assert {:ok, [], st} = Step.withdraw(st, 0, @front)
    assert {:error, {:withdrawn, 0}} = Step.revert(st, 0, @front)
    assert {:error, {:resolved, 0}} = Step.withdraw(st, 0, @front)
    assert {:error, {:live, "a"}} = Step.drop_key(open_front(), "a")

    assert {:ok, st} = Step.drop_key(st, "a")
    assert st.rows == []
    assert Map.get(st, :withdrawn, %{}) == %{}
    assert {:error, {:unknown, 0}} = Step.revert(st, 0, @front)

    st = Step.empty()
    assert {:ok, :held, 0, st} = Step.arrive(st, "a", :worker, 4, @front)
    assert {:ok, [], st} = Step.withdraw(st, 0, @front)
    assert {:ok, :open, 1, st} = Step.arrive(st, "a", :front, 0, @front)
    assert {:ok, [], st} = Step.resolve(st, 1, @front)
    assert {:ok, st} = Step.skip_below(st, 3)
    assert {:error, {:withdrawn, 0}} = Step.revert(st, 0, @front)
    assert {:ok, st} = Step.skip_below(st, 4)
    assert {:error, {:unknown, 0}} = Step.revert(st, 0, @front)
    assert Step.view(st) == []
    assert st.kinds == %{}

    st = Step.empty()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :front, 0, @front)
    assert {:ok, :held, 1, st} = Step.arrive(st, "a", :worker, 1, @front)
    assert {:ok, kept} = Step.skip_below(st, 0)
    assert Step.view(kept) == Step.view(st)
  end

  test "the dispatcher revert agrees with Step, including facts and withdrawn ids" do
    {disp, _parent, emitted} = compile!(release_book("may revert"), Rollout)
    assert emitted =~ "def revert(state, id)"
    assert emitted =~ "phase in [:open, :held, :resolved]"

    assert {:error, {:state, :bad}} = disp.revert(:bad, 0)
    assert {:error, {:state, %{}}} = disp.revert(%{}, 0)
    assert {:error, {:unknown, 0}} = disp.revert(disp.new(), 0)
    assert {:error, {:unknown, -1}} = disp.revert(disp.new(), -1)
    assert {:error, {:unknown, "no"}} = disp.revert(disp.new(), "no")

    st = Step.empty()
    dst = disp.new()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :front, 0, @front)
    assert {:open, 0, dst} = disp.arrive(dst, "a", :front, 0)
    assert {:error, {:opened, 0}} = disp.revert(dst, 0)
    assert {:ok, [], st} = Step.resolve(st, 0, @front)
    assert {:ok, [], dst} = disp.resolved(dst, 0)
    assert dst.by["a"][0] == {0, :front, :resolved}
    assert Map.has_key?(dst.id, 0)
    assert {:ok, st} = Step.revert(st, 0, @front)
    assert {:ok, dst} = disp.revert(dst, 0)
    assert dst.by["a"][0] == {0, :front, :open}
    assert Map.get(st, :kinds, %{}) == Map.get(dst, :kinds, %{})

    trace = [
      {:arrive, "a", :front, 0},
      {:resolved, 0},
      {:revert, 0},
      {:arrive, "a", :worker, 1},
      {:resolved, 0},
      {:resolved, 1},
      {:revert, 1}
    ]

    drive(disp, @front, trace)
    assert {:ok, _} = Step.replay(@front, trace)
    assert disp.check_trace(trace) == :ok

    blocked = [
      {:arrive, "a", :front, 0},
      {:resolved, 0},
      {:arrive, "a", :worker, 1},
      {:resolved, 0},
      {:resolved, 1},
      {:revert, 0}
    ]

    assert drive(disp, @front, blocked) == :error

    :rand.seed(:exsss, {311, 22, 41})

    for _ <- 1..20 do
      sample = for _ <- 1..10, do: random_act()
      drive(disp, @front, sample)

      case Step.replay(@front, sample) do
        {:ok, _} -> assert disp.check_trace(sample) == :ok
        {:error, reason} -> assert disp.check_trace(sample) == {:error, reason}
      end
    end
  end

  test "an unmarked family has no revert, and its dispatcher does not grow one" do
    src = release_book("")
    assert {:ok, emitted} = emit(src)
    refute emitted =~ "def revert("
    refute emitted =~ "held_by"
    refute emitted =~ "phase in [:open, :held, :resolved]"

    assert emitted =~
             "def new, do: %{n: 0, by: %{}, id: %{}, departed: %{}, floor: -1, kinds: %{}}"

    {disp, _parent, _emitted} = compile!(src, Rollout)
    assert {:error, {0, {:step, {:revert, 0}}}} = disp.check_trace([{:revert, 0}])
    assert {:error, {:unmarked, :revert}} = Step.revert(Step.empty(), 0, %{front: :never})

    assert Step.replay(%{front: :never, worker: {:named, %{while: [], until: [:front]}}}, [
             {:revert, 0}
           ]) == {:error, {0, {:unmarked, :revert}}}

    assert {:ok, release} = Muro.emit_fsm(@release, :ReleasePin)
    refute release =~ "def revert("
    refute release =~ "held_by"

    assert release =~
             "def new, do: %{n: 0, by: %{}, id: %{}, departed: %{}, floor: -1, kinds: %{}}"

    plain =
      kinds(~w(front)) <>
        @meet <>
        """
        family rollout : slot per key of Step
          front never held
        """

    assert {:ok, plain} = emit(plain)
    assert plain =~ "def new, do: %{n: 0, by: %{}, id: %{}, departed: %{}, floor: -1}"
    refute plain =~ "kinds:"
    refute plain =~ "def revert("
    _ = disp
  end

  test "in order does not move the waterline across a retained resolved row" do
    src =
      kinds(~w(front schema worker)) <>
        @meet <>
        """
        family rollout : slot per key of Step may revert
          front never held
          schema never held
          worker held until schema resolved
        contract rollout : in order
        """

    {disp, _parent, emitted} = compile!(src, Rollout)
    assert emitted =~ "phase in [:open, :held, :resolved] ->"

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :front, 0)
    assert {:ok, [], state} = disp.resolved(state, 0)
    assert state.by["a"][0] == {0, :front, :resolved}
    assert state.departed["a"] == {0, -1}
    assert {:held, 1, state} = disp.arrive(state, "a", :worker, 1)
    assert {:ok, [], state} = disp.withdraw(state, 1)
    assert state.departed["a"] == {1, -1}
    assert state.by["a"][0] == {0, :front, :resolved}
  end

  test "idempotent init still names a repeat of a retained init" do
    src =
      kinds(~w(init signal)) <>
        @meet <>
        """
        family rollout : slot per key of Step may revert
          init never held
          signal held while earlier unresolved
        contract rollout : idempotent init
        """

    {disp, _parent, _src} = compile!(src, Rollout)
    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :init, 0)
    assert {:ok, [], state} = disp.resolved(state, 0)
    assert {:error, {:contract, :idempotent_init, "a", 0}} = disp.arrive(state, "a", :init, 0)
    assert {:error, {:duplicate, "a", 0}} = disp.arrive(state, "a", :signal, 0)
  end

  test "keyed-rollback holds, and an unrestricted revert is the counterexample" do
    assert Muro.check_file(@rollback) == :ok

    assert Check.temporal_lines() == [
             "family rollout: slot per key of Step may revert",
             "temporal front-before-worker: holds in 247 reachable states, 557 transitions",
             "temporal some-front-before-worker: holds in 247 reachable states, 557 transitions"
           ]

    assert {:ok, book} = Parser.parse(File.read!(@rollback))
    family = Enum.find(book, &(&1.kind == :family))
    assert {:ok, mirror} = Graph.prepare(book, family)
    assert length(mirror.states) == 247
    assert mirror.transitions == 557
    assert mirror.g.revert == :mirror

    assert Enum.map(mirror.g.instances, &{&1.key, &1.kind, &1.index, &1.id}) == [
             {"a", "front", 0, 0},
             {"a", "worker", 1, 1},
             {"b", "front", 0, 2}
           ]

    assert Enum.all?(mirror.states, &Graph.respects?(mirror.g, &1))
    assert bad_front_edges(mirror) == 0

    vacuous =
      String.replace(File.read!(@rollback), "some_resolved k worker", "resolved k worker",
        global: false
      )

    assert {:error, msg} = check(vacuous)
    assert msg =~ "a front 0: running"
    assert msg =~ "a worker 1: absent"

    assert {:ok, free} = Graph.prepare(book, family, revert: :free)
    assert length(free.states) == 535
    assert free.transitions == 1489
    assert free.g.revert == :free
    assert bad_front_edges(free) > 0

    formula =
      Enum.find(book, &(&1.kind == :temporal and &1.name == "front-before-worker")).formula

    assert {:error, msg} = Graph.decide(free, formula)
    assert msg =~ "a front 0 reverts"
    assert msg =~ "a worker 1: resolved"
    assert msg =~ "a front 0: running"

    wanted = [
      {:open, 0},
      {:meet, 0, :rside},
      {:meet, 0, :lside},
      {:resolve, 0},
      {:open, 1},
      {:meet, 1, :rside},
      {:meet, 1, :lside},
      {:resolve, 1},
      {:revert, 0}
    ]

    assert Enum.any?(bad_front_edges(free, :pairs), fn {src, dest} ->
             Graph.phase(src, 0) == :resolved and Graph.phase(src, 1) == :resolved and
               Graph.phase(dest, 1) == :resolved and
               path_tags(free.parents, src) ++ [{:revert, 0}] == wanted
           end)

    release = File.read!(@release)
    assert {:ok, book} = Parser.parse(release)
    family = Enum.find(book, &(&1.kind == :family))
    assert {:ok, search} = Graph.prepare(book, family)
    assert search.g.revert == false
    assert length(search.states) == 8906
    assert search.transitions == 26423
  end

  defp bad_front_edges(search, shape \\ :count) do
    pairs =
      for {src, steps} <- search.edges,
          {{:revert, 0}, dest} <- steps,
          Graph.phase(src, 0) == :resolved and Graph.phase(src, 1) == :resolved,
          do: {src, dest}

    if shape == :count, do: length(pairs), else: pairs
  end

  defp path_tags(parents, state, acc \\ []) do
    case Map.get(parents, state) do
      nil -> acc
      {tag, parent} -> path_tags(parents, parent, [tag | acc])
    end
  end

  defp open_front do
    st = Step.empty()
    assert {:ok, :open, 0, st} = Step.arrive(st, "a", :front, 0, @front)
    st
  end

  defp drive(disp, rules, trace) do
    Enum.reduce_while(trace, {Step.empty(), disp.new()}, fn act, {st, dst} ->
      {st2, s} = step_act(st, act, rules)
      {dst2, d} = disp_act(disp, dst, act)
      assert s == d, "#{inspect(act)}\nstep #{inspect(s)}\ndisp #{inspect(d)}"

      case s do
        {:error, _} ->
          {:halt, :error}

        _ ->
          assert Step.view(st2) == Step.view_disp(dst2)
          assert Map.get(st2, :kinds, %{}) == Map.get(dst2, :kinds, %{})
          assert Map.get(st2, :withdrawn, %{}) == Map.get(dst2, :withdrawn, %{})

          for id <- Enum.map(st2.rows, & &1.id) do
            assert Step.waiting_on(st2, id, rules) == disp.waiting_on(dst2, id)
          end

          {:cont, {st2, dst2}}
      end
    end)
  end

  defp step_act(st, {:arrive, key, kind, index}, rules) do
    case Step.arrive(st, key, kind, index, rules) do
      {:ok, phase, id, st} -> {st, {phase, id}}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp step_act(st, {:resolved, id}, rules) do
    case Step.resolve(st, id, rules) do
      {:ok, rel, st} -> {st, {:ok, rel}}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp step_act(st, {:withdraw, id}, rules) do
    case Step.withdraw(st, id, rules) do
      {:ok, rel, st} -> {st, {:ok, rel}}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp step_act(st, {:revert, id}, rules) do
    case Step.revert(st, id, rules) do
      {:ok, st} -> {st, :ok}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp step_act(st, {:skip, key, index}, _rules) do
    case Step.skip(st, key, index) do
      {:ok, st} -> {st, :ok}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp step_act(st, {:drop, key}, _rules) do
    case Step.drop_key(st, key) do
      {:ok, st} -> {st, :ok}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp step_act(st, {:skip_below, index}, _rules) do
    case Step.skip_below(st, index) do
      {:ok, st} -> {st, :ok}
      {:error, reason} -> {st, {:error, reason}}
    end
  end

  defp disp_act(disp, dst, {:arrive, key, kind, index}) do
    case disp.arrive(dst, key, kind, index) do
      {phase, id, dst} when phase in [:open, :held] -> {dst, {phase, id}}
      {:error, reason} -> {dst, {:error, reason}}
    end
  end

  defp disp_act(disp, dst, {:resolved, id}) do
    case disp.resolved(dst, id) do
      {:ok, rel, dst} -> {dst, {:ok, rel}}
      {:error, reason} -> {dst, {:error, reason}}
    end
  end

  defp disp_act(disp, dst, {:withdraw, id}) do
    case disp.withdraw(dst, id) do
      {:ok, rel, dst} -> {dst, {:ok, rel}}
      {:error, reason} -> {dst, {:error, reason}}
    end
  end

  defp disp_act(disp, dst, {:revert, id}) do
    case disp.revert(dst, id) do
      {:ok, dst} -> {dst, :ok}
      {:error, reason} -> {dst, {:error, reason}}
    end
  end

  defp disp_act(disp, dst, {:skip, key, index}) do
    case disp.skip(dst, key, index) do
      {:ok, dst} -> {dst, :ok}
      {:error, reason} -> {dst, {:error, reason}}
    end
  end

  defp disp_act(disp, dst, {:drop, key}) do
    case disp.drop_key(dst, key) do
      {:ok, dst} -> {dst, :ok}
      {:error, reason} -> {dst, {:error, reason}}
    end
  end

  defp disp_act(disp, dst, {:skip_below, index}) do
    case disp.skip_below(dst, index) do
      {:ok, dst} -> {dst, :ok}
      {:error, reason} -> {dst, {:error, reason}}
    end
  end

  defp random_act do
    key = Enum.random(["a", "b"])
    kind = Enum.random([:front, :worker])
    index = :rand.uniform(4) - 1
    id = :rand.uniform(6) - 1

    Enum.random([
      {:arrive, key, kind, index},
      {:resolved, id},
      {:withdraw, id},
      {:revert, id},
      {:skip, key, index},
      {:drop, key},
      {:skip_below, index}
    ])
  end

  defp kinds(names) do
    ctors = Enum.map_join(names, "\n", &"  #{&1} : Step")

    """
    data Step : Type where
    #{ctors}
    """
  end

  defp release_book(marks) do
    kinds(~w(front worker)) <>
      @meet <>
      """
      family rollout : slot per key of Step #{marks}
        front never held
        worker held until front resolved
      """
  end

  defp parse_error(src) do
    assert {:error, msg} = Parser.parse(src)
    msg
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end

  defp emit(src) do
    dir = System.tmp_dir!() |> Path.join("muro-revert-src-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "book.muro")
    File.write!(path, src)
    Muro.emit_fsm(path, Module.concat(["RevertSrc#{System.unique_integer([:positive])}"]))
  end

  defp compile!(src, family) do
    dir = System.tmp_dir!() |> Path.join("muro-revert-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "book.muro")
    File.write!(path, src)
    parent = Module.concat(["RevertFam#{System.unique_integer([:positive])}"])
    assert {:ok, emitted} = Muro.emit_fsm(path, parent)
    {mods, diags} = Code.with_diagnostics(fn -> Code.compile_string(emitted) end)

    warnings =
      Enum.filter(diags, &(match?(%{severity: :warning}, &1) or match?({:warning, _}, &1)))

    assert warnings == [], inspect(warnings, limit: 20)
    disp = Module.concat(parent, family)
    assert disp in Enum.map(mods, &elem(&1, 0))
    {disp, parent, emitted}
  end
end

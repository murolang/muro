defmodule Muro.Family.StepTest do
  use ExUnit.Case, async: false

  alias Muro.Family.Step

  # Generated Events, Commands, Orders, and Mixes, checked against
  # `Muro.Family.Step`. Those names are the Agda names in
  # `agda/Muro/Family.agda`: `holdOf`, `blocked?`, `anyBlocked?`,
  # `decide`, `decideMode`, `onKey`, `arriveTo`, `arriveMode`,
  # `resolveTo`, `resolveMode`, `withdrawTo`, `touchTo`, `touchMode`,
  # `NoOvertake`, `NoOvertakeR`, `HeldBlocked`, `BadOpen`, `AtMostOne`,
  # `EarlierResolved`, `RulesInv`, `script-a`, `script-b`. This file
  # does not build the family graph.

  @book """
  data Event : Type where
    init : Event
    signal : Event

  data Command : Type where
    command : Command

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

  session command-work := send Report end
  session command-wait := recv Report end

  conform worker : command-work := put ok done

  conform waiter : command-wait :=
    get (r : Report) done
    fail
      done

  meet command-slot : waiter with worker may fail buffer 1

  family events : slot per key of Event
    init never held
    signal held while earlier unresolved

  family commands : command-slot per key of Command
    command held while earlier unresolved

  data Order : Type where
    order : Order

  data Mix : Type where
    early : Mix
    wide : Mix

  family orders : slot per key of Order
    order held while any unresolved

  family mixes : slot per key of Mix
    early held while earlier unresolved
    wide held while any unresolved
  """

  @events Step.proved_rules()
  @commands %{command: :earlier}
  @orders %{order: :any}
  @mixes %{early: :earlier, wide: :any}
  @keys ~w(k0 k1 k2 k3)
  @event_parties %{server: {"server-wait", 0}, task: {"task-work", 0}}
  @command_parties %{waiter: {"command-wait", 0}, worker: {"command-work", 0}}

  setup_all do
    {parent, events, commands, orders, mixes} = compile!()
    on_exit(&purge/0)
    [parent: parent, events: events, commands: commands, orders: orders, mixes: mixes]
  end

  test "an opened signal carries the rows that had already arrived", %{events: events} do
    assert {:ok, :never} = Step.hold_of(@events, :init)
    assert {:ok, :earlier} = Step.hold_of(@events, :signal)

    state = events.new()
    assert {:open, 0, state} = events.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = events.arrive(state, "a", :signal, 1)
    assert {:open, 2, state} = events.arrive(state, "b", :init, 0)
    assert {:ok, [{1, "a", :signal}], state} = events.resolved(state, 0)

    ref = Step.empty()
    assert {:ok, :open, 0, ref} = Step.arrive(ref, "a", :init, 0, @events)
    assert {:ok, :held, 1, ref} = Step.arrive(ref, "a", :signal, 1, @events)
    assert {:ok, :open, 2, ref} = Step.arrive(ref, "b", :init, 0, @events)
    assert {:ok, [{1, "a", :signal}], ref} = Step.resolve(ref, 0, @events)
    assert Step.view(ref) == Step.view_disp(state)
    assert ref.next == state.n
    assert Step.invariant?(ref, @events)
    assert Step.no_overtake?(ref.rows, @events)

    trace = [
      {:arrive, "a", :init, 0},
      {:arrive, "a", :signal, 1},
      {:arrive, "b", :init, 0},
      {:resolved, 0},
      {:resolved, 1},
      {:resolved, 2}
    ]

    assert {:ok, done} = Step.replay(@events, trace)
    assert done.rows == []
    assert :ok = events.check_trace(trace)
  end

  test "a later arrival is not an earlier instance", %{events: events} do
    ref = Step.empty()
    assert {:ok, :open, 0, ref} = Step.arrive(ref, "a", :signal, 1, @events)
    assert {:ok, :open, 1, ref} = Step.arrive(ref, "a", :init, 0, @events)
    assert Step.invariant?(ref, @events)
    assert Step.no_overtake?(ref.rows, @events)

    signal = Enum.find(ref.rows, &(&1.kind == :signal))
    init = Enum.find(ref.rows, &(&1.kind == :init))
    assert init.born > signal.opened_at
    assert Step.fresh?(ref.rows, "b", 0)
    refute Step.fresh?(ref.rows, "a", 0)

    state = events.new()
    assert {:open, 0, state} = events.arrive(state, "a", :signal, 1)
    assert {:open, 1, state} = events.arrive(state, "a", :init, 0)
    assert Step.view(ref) == Step.view_disp(state)
    assert :ok = events.check_trace([{:arrive, "a", :signal, 1}, {:arrive, "a", :init, 0}])
  end

  test "a held signal opens when its last earlier row resolves", %{events: events} do
    ref = Step.empty()
    assert {:ok, :open, 0, ref} = Step.arrive(ref, "a", :init, 0, @events)
    assert {:ok, :open, 1, ref} = Step.arrive(ref, "a", :init, 1, @events)
    assert {:ok, :held, 2, ref} = Step.arrive(ref, "a", :signal, 2, @events)
    assert {:ok, :held, 3, ref} = Step.arrive(ref, "a", :signal, 3, @events)
    assert Step.invariant?(ref, @events)

    signal = Enum.find(ref.rows, &(&1.id == 2))
    least = Step.least_earlier(ref.rows, signal)
    assert least.id == 0
    assert least.phase == :open
    assert least.index < signal.index

    assert {:ok, [], ref} = Step.resolve(ref, 0, @events)
    assert {:held, 2} = held(ref, 2)
    assert Step.held_blocked?(ref.rows)

    next = Step.least_earlier(ref.rows, Enum.find(ref.rows, &(&1.id == 2)))
    assert next.phase == :open
    assert {:ok, [{2, "a", :signal}], ref} = Step.resolve(ref, next.id, @events)
    assert Enum.find(ref.rows, &(&1.id == 2)).phase == :open
    assert Enum.find(ref.rows, &(&1.id == 3)).phase == :held
    assert {:ok, [{3, "a", :signal}], ref} = Step.resolve(ref, 2, @events)
    assert Enum.find(ref.rows, &(&1.id == 3)).phase == :open
    assert Step.invariant?(ref, @events)

    state = events.new()
    assert {:open, 0, state} = events.arrive(state, "a", :init, 0)
    assert {:open, 1, state} = events.arrive(state, "a", :init, 1)
    assert {:held, 2, state} = events.arrive(state, "a", :signal, 2)
    assert {:held, 3, state} = events.arrive(state, "a", :signal, 3)
    assert {:ok, [], state} = events.resolved(state, 0)
    assert {:ok, [{2, "a", :signal}], state} = events.resolved(state, 1)
    assert {:ok, [{3, "a", :signal}], state} = events.resolved(state, 2)
    assert Step.view(ref) == Step.view_disp(state)
  end

  test "holding a signal reads only its own key", %{events: events} do
    ref = Step.empty()
    assert {:ok, :open, 0, ref} = Step.arrive(ref, "k0", :init, 0, @events)
    assert {:ok, :held, 1, ref} = Step.arrive(ref, "k0", :signal, 1, @events)
    before = Step.on_key(ref.rows, "k0")
    assert {:ok, :open, 2, ref} = Step.arrive(ref, "k1", :signal, 1, @events)
    assert Step.on_key(ref.rows, "k0") == before

    assert Step.decide(ref.rows, "k1", 1, :signal, @events) == :open

    assert Step.decide(ref.rows, "k1", 1, :signal, @events) ==
             Step.decide(Step.on_key(ref.rows, "k1"), "k1", 1, :signal, @events)

    assert Step.blocked?(ref.rows, "k1", 1) ==
             Step.blocked?(Step.on_key(ref.rows, "k1"), "k1", 1)

    state = events.new()
    assert {:open, 0, state} = events.arrive(state, "k0", :init, 0)
    assert {:held, 1, state} = events.arrive(state, "k0", :signal, 1)
    assert {:open, 2, state} = events.arrive(state, "k1", :signal, 1)
    assert Step.view(ref) == Step.view_disp(state)
  end

  test "rerun and meet leave the opened row, and a bare rerun is unfinished", %{
    events: events,
    parent: parent
  } do
    ref = Step.empty()
    assert {:ok, :open, 0, ref} = Step.arrive(ref, "a", :init, 0, @events)
    assert {:ok, :held, 1, ref} = Step.arrive(ref, "a", :signal, 1, @events)
    assert {:ok, [], kept} = Step.rerun(ref, 0)
    assert kept == ref
    assert {:ok, [], met} = Step.meet(ref, 0)
    assert met == ref
    assert {:ok, [], touched} = Step.touch(ref, 0)
    assert touched == ref
    assert {:error, {:held, 1}} = Step.rerun(ref, 1)
    assert Step.invariant?(ref, @events)

    state = events.new()
    assert {:open, 0, state} = events.arrive(state, "a", :init, 0)
    assert {:held, 1, state} = events.arrive(state, "a", :signal, 1)
    assert {:ok, [], ^state} = events.retain(state, 0)
    assert {:error, {:held, 1}} = events.retain(state, 1)

    # `touchTo` accepts this rerun. `check_trace` asks for a done session.
    assert {:ok, _} = Step.replay(@events, [{:arrive, "a", :init, 0}, {:rerun, 0}])

    bare = [{:arrive, "a", :init, 0}, {:rerun, 0}]
    assert {:error, {1, {:unfinished, 0}}} = events.check_trace(bare)
    assert events.check_trace(bare) == reference_trace(parent, @event_parties, @events, bare)

    trace = [
      {:arrive, "a", :init, 0},
      {:arrive, "a", :signal, 1},
      {:server, 0, :down},
      {:rerun, 0},
      {:server, 0, {:recv, :ok}},
      {:resolved, 0},
      {:resolved, 1}
    ]

    assert :ok = events.check_trace(trace)
    assert :ok = reference_trace(parent, @event_parties, @events, trace)
  end

  test "check_trace accepts a trace exactly when the step and the done-session condition do",
       %{
         events: events,
         commands: commands,
         parent: parent
       } do
    :rand.seed(:exsss, {22, 6, 248})

    Enum.each(1..30, fn _trial ->
      agree(events, parent, @event_parties, @events, [:init, :signal])
      agree(commands, parent, @command_parties, @commands, [:command])
    end)

    assert {:error, {:trace, :nope}} = events.check_trace(:nope)
  end

  test "random arrivals, resolves, and reruns match the generated dispatchers", %{
    events: events,
    commands: commands
  } do
    :rand.seed(:exsss, {22, 6, 1})

    stats =
      Enum.reduce(1..40, empty_stats(), fn _trial, stats ->
        stats = random_family(events, @events, [:init, :signal], stats)
        random_family(commands, @commands, [:command], stats)
      end)

    assert stats.held > 0
    assert stats.opened > 0
    assert MapSet.size(stats.keys) > 1
  end

  test "a hand-built overtake is BadOpen and sits on script-a" do
    assert Step.script_a() == [{:init, 0}, {:signal, 1}, {:signal, 2}]
    assert Step.script_b() == [{:init, 0}]
    refute Enum.any?(Step.script_b(), fn {kind, _index} -> kind == :signal end)

    init_before = [
      row("a", 1, 1, 0, 1, :signal, :open),
      row("a", 0, 0, 0, 0, :init, :open)
    ]

    signal_before = [
      row("a", 2, 1, 0, 1, :signal, :open),
      row("a", 1, 0, 0, 0, :signal, :open)
    ]

    assert Step.bad_open?(init_before, @events)
    assert Step.bad_open?(signal_before, @events)
    refute Step.no_overtake?(init_before, @events)
    refute Step.invariant?(%{next: 2, tick: 2, rows: init_before}, @events)
    assert {:init, 0} in Step.script_a()
    assert {:signal, 1} in Step.script_a()
    assert {:signal, 2} in Step.script_a()

    late = [
      row("a", 1, 0, 0, 0, :signal, :open),
      row("a", 0, 1, 1, 1, :init, :open)
    ]

    refute Step.bad_open?(late, @events)
    assert Step.no_overtake?(late, @events)
  end

  test "a command is the earlier clause, on its own keys", %{commands: commands} do
    ref = Step.empty()
    assert {:ok, :open, 0, ref} = Step.arrive(ref, "wf", :command, 0, @commands)
    assert {:ok, :held, 1, ref} = Step.arrive(ref, "wf", :command, 1, @commands)
    assert {:ok, :open, 2, ref} = Step.arrive(ref, "other", :command, 0, @commands)
    assert Step.invariant?(ref, @commands)
    assert {:error, {:kind, :init}} = Step.arrive(ref, "wf", :init, 2, @commands)

    state = commands.new()
    assert {:open, 0, state} = commands.arrive(state, "wf", :command, 0)
    assert {:held, 1, state} = commands.arrive(state, "wf", :command, 1)
    assert {:open, 2, state} = commands.arrive(state, "other", :command, 0)
    assert {:error, {:kind, :init}} = commands.arrive(state, "wf", :init, 2)
    assert Step.view(ref) == Step.view_disp(state)
    assert {:ok, [{1, "wf", :command}], _} = commands.resolved(state, 0)
    assert Step.earlier_resolved?(ref.rows, "wf", :command)
  end

  test "one any of a key is open, and release opens the least index", %{orders: orders} do
    ref = Step.empty()
    assert {:ok, :open, 0, ref} = Step.arrive(ref, "a", :order, 5, @orders)
    assert {:ok, :held, 1, ref} = Step.arrive(ref, "a", :order, 1, @orders)
    assert {:ok, :held, 2, ref} = Step.arrive(ref, "a", :order, 0, @orders)
    assert Step.at_most_one_any?(ref.rows, @orders)
    assert Step.invariant?(ref, @orders)
    assert Step.earlier_resolved?(ref.rows, "a", :order)
    refute Step.held_blocked?(ref.rows)

    assert {:ok, [{2, "a", :order}], ref} = Step.resolve(ref, 0, @orders)
    assert Enum.find(ref.rows, &(&1.id == 2)).phase == :open
    assert Enum.find(ref.rows, &(&1.id == 1)).phase == :held
    assert Step.invariant?(ref, @orders)
    assert Step.earlier_resolved?(ref.rows, "a", :order)

    state = orders.new()
    assert {:open, 0, state} = orders.arrive(state, "a", :order, 5)
    assert {:held, 1, state} = orders.arrive(state, "a", :order, 1)
    assert {:held, 2, state} = orders.arrive(state, "a", :order, 0)
    assert {:ok, [{2, "a", :order}], state} = orders.resolved(state, 0)
    assert Step.view(ref) == Step.view_disp(state)
    assert ref.next == state.n
  end

  test "a mixed family opens the any and leaves the earlier row held", %{mixes: mixes} do
    ref = Step.empty()
    assert {:ok, :open, 0, ref} = Step.arrive(ref, "a", :early, 2, @mixes)
    assert {:ok, :held, 1, ref} = Step.arrive(ref, "a", :wide, 0, @mixes)
    assert {:ok, :held, 2, ref} = Step.arrive(ref, "a", :early, 1, @mixes)
    assert Step.invariant?(ref, @mixes)
    assert Step.earlier_resolved?(ref.rows, "a", :early)
    assert Step.earlier_resolved?(ref.rows, "a", :wide)

    early = Enum.find(ref.rows, &(&1.id == 2))
    least = Step.least_earlier(ref.rows, early)
    assert least.id == 1
    assert least.phase == :held

    assert {:ok, [{1, "a", :wide}], ref} = Step.resolve(ref, 0, @mixes)
    assert Enum.find(ref.rows, &(&1.id == 1)).phase == :open
    assert Enum.find(ref.rows, &(&1.id == 2)).phase == :held
    assert Step.invariant?(ref, @mixes)
    assert Step.earlier_resolved?(ref.rows, "a", :early)
    assert Step.earlier_resolved?(ref.rows, "a", :wide)

    state = mixes.new()
    assert {:open, 0, state} = mixes.arrive(state, "a", :early, 2)
    assert {:held, 1, state} = mixes.arrive(state, "a", :wide, 0)
    assert {:held, 2, state} = mixes.arrive(state, "a", :early, 1)
    assert {:ok, [{1, "a", :wide}], state} = mixes.resolved(state, 0)
    assert Step.view(ref) == Step.view_disp(state)
  end

  test "withdraw drops a held instance and does not block a later one", %{mixes: mixes} do
    ref = Step.empty()
    assert {:ok, :open, 0, ref} = Step.arrive(ref, "a", :early, 2, @mixes)
    assert {:ok, :held, 1, ref} = Step.arrive(ref, "a", :wide, 0, @mixes)
    assert {:ok, :held, 2, ref} = Step.arrive(ref, "a", :early, 1, @mixes)
    assert {:error, {:opened, 0}} = Step.withdraw(ref, 0, @mixes)

    assert {:ok, [{2, "a", :early}], ref} = Step.withdraw(ref, 1, @mixes)
    assert {:error, {:unknown, 1}} = Step.live(ref, 1)
    assert Enum.find(ref.rows, &(&1.id == 2)).phase == :open
    assert Enum.find(ref.rows, &(&1.id == 0)).phase == :open
    assert {:error, {:resolved, 1}} = Step.withdraw(ref, 1, @mixes)
    assert {:error, {:unknown, 1}} = Step.resolve(ref, 1, @mixes)
    assert {:error, {:unknown, 9}} = Step.withdraw(ref, 9, @mixes)

    assert Step.fresh?(ref.rows, "a", 0)
    assert Step.departed?(ref, "a", 0)
    assert ref.departed["a"] == {0, %{}}
    assert {:error, {:departed, "a", 0}} = Step.arrive(ref, "a", :wide, 0, @mixes)
    assert {:ok, :held, 3, ref} = Step.arrive(ref, "a", :wide, 3, @mixes)
    assert {:error, {:resolved, 1}} = Step.withdraw(ref, 1, @mixes)
    assert Step.invariant?(ref, @mixes)
    assert Step.earlier_resolved?(ref.rows, "a", :early)
    assert Step.earlier_resolved?(ref.rows, "a", :wide)

    state = mixes.new()
    assert {:open, 0, state} = mixes.arrive(state, "a", :early, 2)
    assert {:held, 1, state} = mixes.arrive(state, "a", :wide, 0)
    assert {:held, 2, state} = mixes.arrive(state, "a", :early, 1)
    assert {:error, {:opened, 0}} = mixes.withdraw(state, 0)
    assert {:ok, [{2, "a", :early}], state} = mixes.withdraw(state, 1)
    assert {:error, {:resolved, 1}} = mixes.withdraw(state, 1)
    assert {:error, {:unknown, 1}} = mixes.resolved(state, 1)
    assert {:error, {:unknown, 9}} = mixes.withdraw(state, 9)
    assert {:error, {:departed, "a", 0}} = mixes.arrive(state, "a", :wide, 0)
    assert {:held, 3, state} = mixes.arrive(state, "a", :wide, 3)
    assert Step.view(ref) == Step.view_disp(state)
  end

  test "an opened never can break earlier_resolved while the invariant holds" do
    beside = [
      row("a", 1, 1, 0, 0, :init, :open),
      row("a", 0, 0, 0, 0, :init, :open)
    ]

    assert Step.invariant?(%{next: 2, tick: 1, rows: beside}, @events)
    refute Step.earlier_resolved?(beside, "a", :init)

    both = [
      row("a", 0, 0, 0, 0, :order, :open),
      row("a", 1, 1, 0, 0, :order, :open)
    ]

    refute Step.at_most_one_any?(both, @orders)
    refute Step.invariant?(%{next: 2, tick: 1, rows: both}, @orders)

    stamped = [
      row("a", 1, 1, 0, 0, :order, :open),
      row("a", 0, 0, 0, 0, :order, :held)
    ]

    refute Step.earlier_resolved?(stamped, "a", :order)
    refute Step.invariant?(%{next: 2, tick: 1, rows: stamped}, @orders)
  end

  test "holding an any reads only its own key", %{orders: orders} do
    ref = Step.empty()
    assert {:ok, :open, 0, ref} = Step.arrive(ref, "k0", :order, 0, @orders)
    assert {:ok, :held, 1, ref} = Step.arrive(ref, "k0", :order, 1, @orders)
    before = Step.on_key(ref.rows, "k0")
    assert {:ok, :open, 2, ref} = Step.arrive(ref, "k1", :order, 1, @orders)
    assert Step.on_key(ref.rows, "k0") == before
    assert Step.decide(ref.rows, "k1", 1, :order, @orders) == :open

    assert Step.decide(ref.rows, "k1", 1, :order, @orders) ==
             Step.decide(Step.on_key(ref.rows, "k1"), "k1", 1, :order, @orders)

    assert Step.any_blocked?(ref.rows, "k1", 1) ==
             Step.any_blocked?(Step.on_key(ref.rows, "k1"), "k1", 1)

    refute Step.any_blocked?(ref.rows, "k1", 1)
    assert Step.any_blocked?(ref.rows, "k0", 1)

    state = orders.new()
    assert {:open, 0, state} = orders.arrive(state, "k0", :order, 0)
    assert {:held, 1, state} = orders.arrive(state, "k0", :order, 1)
    assert {:open, 2, state} = orders.arrive(state, "k1", :order, 1)
    assert Step.view(ref) == Step.view_disp(state)
  end

  test "check_trace accepts withdraw on any and on a mixed family", %{
    orders: orders,
    mixes: mixes,
    parent: parent
  } do
    :rand.seed(:exsss, {22, 6, 270})

    Enum.each(1..20, fn _trial ->
      agree_withdraw(orders, parent, @event_parties, @orders, [:order])
      agree_withdraw(mixes, parent, @event_parties, @mixes, [:early, :wide])
    end)
  end

  test "skip_below matches the generated dispatcher", %{events: events, parent: parent} do
    script = [
      {:arrive, "a", :init, 0},
      {:arrive, "a", :signal, 1},
      {:arrive, "b", :init, 3},
      {:skip_below, 0},
      {:withdraw, 1},
      {:resolved, 0},
      {:arrive, "a", :init, 2},
      {:resolved, 3},
      {:skip_below, 2},
      {:arrive, "b", :signal, 4},
      {:skip_below, 1},
      {:arrive, "c", :init, 1},
      {:arrive, "c", :init, 5},
      {:skip_below, -1}
    ]

    {dstate, ref} =
      Enum.reduce(script, {events.new(), Step.empty()}, fn act, {dstate, ref} ->
        {dstate, dres} = disp_act(events, dstate, act)
        {ref, rres} = ref_act(ref, @events, act)

        assert dres == rres,
               "act #{inspect(act)} dispatcher #{inspect(dres)} reference #{inspect(rres)}"

        assert Step.view(ref) == Step.view_disp(dstate)
        assert ref.floor == dstate.floor
        assert ref.departed == dstate.departed
        assert ref.next == dstate.n
        {dstate, ref}
      end)

    assert dstate.floor == 2
    assert dstate.departed == %{}
    assert dstate.by["b"][3] == {2, :init, :open}
    assert dstate.by["b"][4] == {4, :signal, :held}
    assert dstate.by["c"][5] == {5, :init, :open}
    assert {:error, {:departed, "c", 1}} = events.arrive(dstate, "c", :init, 1)
    assert {:error, {:departed, "c", 1}} = Step.arrive(ref, "c", :init, 1, @events)
    assert Step.departed?(ref, "z", 2)
    refute Step.departed?(ref, "z", 3)

    trace = [
      {:arrive, "a", :init, 0},
      {:resolved, 0},
      {:skip_below, 0},
      {:arrive, "b", :init, 1},
      {:arrive, "a", :init, 0}
    ]

    assert reference_trace(parent, @event_parties, @events, trace) == events.check_trace(trace)

    assert {:error, {0, {:index, -1}}} = events.check_trace([{:skip_below, -1}])

    assert reference_trace(parent, @event_parties, @events, [{:skip_below, -1}]) ==
             events.check_trace([{:skip_below, -1}])
  end

  test "random any and mixed steps match the generated dispatchers", %{
    orders: orders,
    mixes: mixes
  } do
    :rand.seed(:exsss, {22, 6, 271})

    stats =
      Enum.reduce(1..20, empty_stats(), fn _trial, stats ->
        stats = random_wide(orders, @orders, [:order], stats)
        random_wide(mixes, @mixes, [:early, :wide], stats)
      end)

    assert stats.held > 0
    assert stats.opened > 0
    assert MapSet.size(stats.keys) > 1
  end

  defp agree(disp, parent, parties, rules, kinds) do
    {trace, _ref} = legal_trace(parent, parties, rules, kinds, 25)
    assert reference_trace(parent, parties, rules, trace) == disp.check_trace(trace)

    illegal = trace ++ [Enum.random([{:resolved, 99}, {:rerun, 99}, {:arrive, "k0", :nope, 0}])]
    assert reference_trace(parent, parties, rules, illegal) == disp.check_trace(illegal)
  end

  defp agree_withdraw(disp, parent, parties, rules, kinds) do
    {trace, _ref} = legal_trace(parent, parties, rules, kinds, 25, :withdraw)
    assert reference_trace(parent, parties, rules, trace) == disp.check_trace(trace)

    illegal = trace ++ [Enum.random([{:withdraw, 99}, {:resolved, 99}])]
    assert reference_trace(parent, parties, rules, illegal) == disp.check_trace(illegal)
  end

  defp legal_trace(parent, parties, rules, kinds, n, extra \\ :none) do
    Enum.reduce(1..n, {[], Step.empty(), %{}}, fn _, {trace, ref, seen} ->
      act = legal_act(parent, ref, seen, kinds, parties, extra)

      {:ok, ref, seen} =
        case oracle_step(parent, parties, rules, ref, seen, act) do
          {:ok, _, _} = ok ->
            ok

          {:error, reason} ->
            flunk("legal act #{inspect(act)} refused: #{inspect(reason)}")
        end

      {trace ++ [act], ref, seen}
    end)
    |> then(fn {trace, ref, _seen} -> {trace, ref} end)
  end

  defp legal_act(parent, ref, seen, kinds, parties, extra) do
    options =
      Enum.filter(
        [
          arrival(ref, kinds),
          resolve_ready(parent, ref, seen),
          rerun_ready(parent, ref, seen),
          session_ready(ref, seen, parties),
          if(extra == :withdraw, do: withdraw_ready(ref))
        ],
        &is_tuple/1
      )

    case options do
      [] ->
        index =
          Enum.find(0..64, fn index ->
            Step.fresh?(ref.rows, "k0", index) and not Step.departed?(ref, "k0", index)
          end)

        {:arrive, "k0", hd(kinds), index}

      _ ->
        Enum.random(options)
    end
  end

  defp arrival(ref, kinds) do
    key = Enum.random(@keys)

    case Enum.find(0..8, fn index ->
           Step.fresh?(ref.rows, key, index) and not Step.departed?(ref, key, index)
         end) do
      nil -> nil
      index -> {:arrive, key, Enum.random(kinds), index}
    end
  end

  defp resolve_ready(parent, ref, seen) do
    case open_ids(parent, ref, seen, [:none, :done]) do
      [] -> nil
      ids -> {:resolved, Enum.random(ids)}
    end
  end

  defp rerun_ready(parent, ref, seen) do
    case open_ids(parent, ref, seen, [:done]) do
      [] -> nil
      ids -> {:rerun, Enum.random(ids)}
    end
  end

  defp withdraw_ready(ref) do
    case Enum.filter(ref.rows, &(&1.phase == :held)) do
      [] -> nil
      rows -> {:withdraw, Enum.random(rows).id}
    end
  end

  defp session_ready(ref, seen, parties) do
    case open_ids(nil, ref, seen, [:none]) do
      [] ->
        nil

      ids ->
        id = Enum.random(ids)
        party = Enum.random(Map.keys(parties))
        {party, id, completing(party)}
    end
  end

  defp open_ids(parent, ref, seen, allowed) do
    ref.rows
    |> Enum.filter(&(&1.phase == :open))
    |> Enum.filter(fn row -> status(parent, seen, row.id) in allowed end)
    |> Enum.map(& &1.id)
  end

  defp completing(party) when party in [:server, :waiter], do: :down
  defp completing(party) when party in [:task, :worker], do: {:send, :ok}

  defp empty_stats, do: %{held: 0, opened: 0, keys: MapSet.new()}

  defp random_family(disp, rules, kinds, stats) do
    Enum.reduce(1..40, {disp.new(), Step.empty(), stats}, fn _step, {dstate, ref, stats} ->
      act = wild_act(rules, kinds)
      {dstate, ref, stats} = step_family(disp, dstate, ref, rules, act, stats)
      {dstate, ref, stats}
    end)
    |> elem(2)
  end

  defp random_wide(disp, rules, kinds, stats) do
    Enum.reduce(1..40, {disp.new(), Step.empty(), stats}, fn _step, {dstate, ref, stats} ->
      act = wide_act(rules, kinds)
      {dstate, ref, stats} = step_family(disp, dstate, ref, rules, act, stats)
      {dstate, ref, stats}
    end)
    |> elem(2)
  end

  defp wild_act(rules, kinds) do
    key = Enum.random(@keys)
    kind = Enum.random(kinds)
    index = :rand.uniform(9) - 1

    case :rand.uniform(10) do
      n when n <= 4 -> {:arrive, key, kind, index}
      n when n <= 6 -> {:resolved, :rand.uniform(16) - 1}
      7 -> {:rerun, :rand.uniform(16) - 1}
      8 -> {:arrive, key, :nope, index}
      9 -> {:arrive, key, kind, -1}
      10 -> {:arrive, key, Enum.random(Map.keys(rules)), index}
    end
  end

  # `wild_act` keeps its 1–10 split. Withdraw is an extra draw, used
  # only by the any and mixed walk.
  defp wide_act(rules, kinds) do
    case :rand.uniform(12) do
      n when n <= 10 -> wild_act(rules, kinds)
      _ -> {:withdraw, :rand.uniform(16) - 1}
    end
  end

  defp step_family(disp, dstate, ref, rules, act, stats) do
    {dstate2, dres} = disp_act(disp, dstate, act)
    {ref2, rres} = ref_act(ref, rules, act)

    assert dres == rres,
           "act #{inspect(act)} dispatcher #{inspect(dres)} reference #{inspect(rres)}"

    case rres do
      {:error, _} ->
        assert dstate2 == dstate
        assert ref2 == ref
        {dstate, ref, stats}

      _ ->
        assert Step.view(ref2) == Step.view_disp(dstate2)
        assert ref2.next == dstate2.n
        assert Step.invariant?(ref2, rules)
        assert_local(ref2, rules)
        assert_progress(ref2, rules)
        {dstate2, ref2, observe(stats, ref, ref2)}
    end
  end

  defp observe(stats, before, later) do
    keys = Enum.reduce(later.rows, stats.keys, fn row, acc -> MapSet.put(acc, row.key) end)
    held = stats.held + Enum.count(later.rows, &(&1.phase == :held))

    opened =
      stats.opened +
        Enum.count(before.rows, fn row ->
          row.phase == :held and
            match?(%{phase: :open}, Enum.find(later.rows, &(&1.id == row.id)))
        end)

    %{held: held, opened: opened, keys: keys}
  end

  defp disp_act(disp, state, {:skip_below, index}) do
    case disp.skip_below(state, index) do
      {:error, reason} -> {state, {:error, reason}}
      {:ok, state} -> {state, :ok}
    end
  end

  defp disp_act(disp, state, {:arrive, key, kind, index}) do
    case disp.arrive(state, key, kind, index) do
      {:error, reason} -> {state, {:error, reason}}
      {phase, id, state} -> {state, {:ok, phase, id}}
    end
  end

  defp disp_act(disp, state, {:resolved, id}) do
    case disp.resolved(state, id) do
      {:error, reason} -> {state, {:error, reason}}
      {:ok, released, state} -> {state, {:ok, released}}
    end
  end

  defp disp_act(disp, state, {:withdraw, id}) do
    case disp.withdraw(state, id) do
      {:error, reason} -> {state, {:error, reason}}
      {:ok, released, state} -> {state, {:ok, released}}
    end
  end

  defp disp_act(disp, state, {:rerun, id}) do
    case disp.retain(state, id) do
      {:error, reason} -> {state, {:error, reason}}
      {:ok, [], state} -> {state, :ok}
    end
  end

  defp ref_act(state, _rules, {:skip_below, index}) do
    case Step.skip_below(state, index) do
      {:error, reason} -> {state, {:error, reason}}
      {:ok, state} -> {state, :ok}
    end
  end

  defp ref_act(state, rules, {:arrive, key, kind, index}) do
    case Step.arrive(state, key, kind, index, rules) do
      {:error, reason} -> {state, {:error, reason}}
      {:ok, phase, id, state} -> {state, {:ok, phase, id}}
    end
  end

  defp ref_act(state, rules, {:resolved, id}) do
    case Step.resolve(state, id, rules) do
      {:error, reason} -> {state, {:error, reason}}
      {:ok, released, state} -> {state, {:ok, released}}
    end
  end

  defp ref_act(state, rules, {:withdraw, id}) do
    case Step.withdraw(state, id, rules) do
      {:error, reason} -> {state, {:error, reason}}
      {:ok, released, state} -> {state, {:ok, released}}
    end
  end

  defp ref_act(state, _rules, {:rerun, id}) do
    case Step.rerun(state, id) do
      {:error, reason} -> {state, {:error, reason}}
      {:ok, [], state} -> {state, :ok}
    end
  end

  defp assert_local(ref, rules) do
    for row <- ref.rows do
      refute Step.fresh?(ref.rows, row.key, row.index)

      assert Step.decide(ref.rows, row.key, row.index, row.kind, rules) ==
               Step.decide(Step.on_key(ref.rows, row.key), row.key, row.index, row.kind, rules)

      assert Step.blocked?(ref.rows, row.key, row.index) ==
               Step.blocked?(Step.on_key(ref.rows, row.key), row.key, row.index)

      assert Step.any_blocked?(ref.rows, row.key, row.index) ==
               Step.any_blocked?(Step.on_key(ref.rows, row.key), row.key, row.index)
    end
  end

  # `noStarve`. A held row has some opened row of its key. When the key
  # has no `any` row, `onlyEarlier-open` still says the least earlier
  # row is opened. `HeldBlocked` is that earlier-only fact.
  defp assert_progress(ref, rules) do
    for row <- ref.rows, row.phase == :held do
      assert Enum.any?(ref.rows, &(&1.key == row.key and &1.phase == :open))
    end

    for row <- ref.rows,
        hold(rules, row) != :any,
        not Step.blocked?(ref.rows, row.key, row.index) do
      assert row.phase == :open
    end

    for row <- ref.rows, row.phase == :held, hold(rules, row) == :earlier do
      any_on_key? = Enum.any?(ref.rows, &(&1.key == row.key and hold(rules, &1) == :any))

      if not any_on_key? do
        least = Step.least_earlier(ref.rows, row)
        assert least
        assert least.phase == :open
        assert least.index < row.index
        assert Step.blocked?(ref.rows, row.key, row.index)
      end
    end

    if not Enum.any?(ref.rows, &(hold(rules, &1) == :any)) do
      assert Step.held_blocked?(ref.rows)
    end

    for {kind, mode} <- rules, mode in [:earlier, :any], key <- keys_of(ref) do
      assert Step.earlier_resolved?(ref.rows, key, kind)
    end

    assert Step.at_most_one_any?(ref.rows, rules)
  end

  defp hold(rules, row) do
    case Step.hold_of(rules, row.kind) do
      {:ok, mode} -> mode
      {:error, _} -> :unknown
    end
  end

  defp keys_of(ref), do: ref.rows |> Enum.map(& &1.key) |> Enum.uniq()

  # `check_trace` agrees with this walk. A family step is `arriveTo`,
  # `resolveTo`, `withdrawTo`, or `touchTo`. A session step is `meet`
  # (`touchTo`) plus the generated session machine. `{:rerun, id}` and
  # a resolve that has started a session also require every session of
  # that id to be at `done`. That requirement is the dispatcher's. It
  # is not Agda `touchTo`. `{:withdraw, id}` does not read the session
  # map. `replay/2` is the family relation without the session condition.
  defp reference_trace(parent, parties, rules, trace) do
    walked =
      Enum.reduce_while(Enum.with_index(trace), {:ok, Step.empty(), %{}}, fn {act, i},
                                                                             {:ok, ref, seen} ->
        assert Step.invariant?(ref, rules)

        case oracle_step(parent, parties, rules, ref, seen, act) do
          {:ok, ref, seen} -> {:cont, {:ok, ref, seen}}
          {:error, reason} -> {:halt, {:error, {i, reason}}}
        end
      end)

    case walked do
      {:error, _} = error ->
        error

      {:ok, ref, seen} ->
        assert Step.invariant?(ref, rules)
        leak(parent, ref, seen)
    end
  end

  defp oracle_step(_parent, _parties, _rules, ref, seen, {:skip_below, index}) do
    case Step.skip_below(ref, index) do
      {:ok, ref} -> {:ok, ref, seen}
      {:error, reason} -> {:error, reason}
    end
  end

  defp oracle_step(_parent, _parties, rules, ref, seen, {:arrive, key, kind, index}) do
    case Step.arrive(ref, key, kind, index, rules) do
      {:error, reason} -> {:error, reason}
      {:ok, _phase, _id, ref} -> {:ok, ref, seen}
    end
  end

  defp oracle_step(parent, _parties, rules, ref, seen, {:resolved, id}) do
    cond do
      sessions_of(seen, id) == [] ->
        commit(rules, ref, seen, id)

      settled?(parent, seen, id) ->
        commit(rules, ref, drop_id(seen, id), id)

      true ->
        {:error, {:unfinished, id}}
    end
  end

  defp oracle_step(_parent, _parties, rules, ref, seen, {:withdraw, id}) do
    case Step.withdraw(ref, id, rules) do
      {:ok, _released, ref} -> {:ok, ref, seen}
      {:error, reason} -> {:error, reason}
    end
  end

  defp oracle_step(parent, _parties, _rules, ref, seen, {:rerun, id}) do
    case Step.rerun(ref, id) do
      {:ok, [], ^ref} ->
        if settled?(parent, seen, id) do
          {:ok, ref, drop_id(seen, id)}
        else
          {:error, {:unfinished, id}}
        end

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp oracle_step(parent, parties, _rules, ref, seen, {party, id, action}) when is_atom(party) do
    case Step.live(ref, id) do
      {:error, reason} ->
        {:error, reason}

      {:ok, :held, _key, _kind} ->
        {:error, {:held, id}}

      {:ok, :open, _key, _kind} ->
        case step_end(parent, parties, seen, party, id, action) do
          {:ok, sess} -> {:ok, ref, Map.put(seen, {id, party}, sess)}
          {:error, reason} -> {:error, reason}
        end
    end
  end

  defp oracle_step(_parent, _parties, _rules, _ref, _seen, other) do
    {:error, {:step, other}}
  end

  defp commit(rules, ref, seen, id) do
    case Step.resolve(ref, id, rules) do
      {:ok, _released, ref} -> {:ok, ref, seen}
      {:error, reason} -> {:error, reason}
    end
  end

  defp step_end(parent, parties, seen, party, id, action) do
    case Map.fetch(parties, party) do
      :error ->
        {:error, {:party, party}}

      {:ok, {session, arity}} ->
        prev = Map.get(seen, {id, party})

        cond do
          is_nil(prev) and arity != 0 ->
            {:error, {:session_args, party}}

          true ->
            stored =
              case prev do
                nil -> parent.muro_fsm_init(session, [])
                {_session, stored} -> stored
              end

            case apply_end(parent, session, stored, action) do
              {:ok, next} -> {:ok, {session, next}}
              {:error, reason} -> {:error, reason}
            end
        end
    end
  end

  defp apply_end(parent, session, state, {:send, value}) do
    stepped(parent.muro_fsm_step(session, :send, state, value))
  end

  defp apply_end(parent, session, state, {:recv, value}) do
    stepped(parent.muro_fsm_step(session, :recv, state, value))
  end

  defp apply_end(parent, session, state, :down) do
    stepped(parent.muro_fsm_down(session, state, nil))
  end

  defp apply_end(parent, session, state, {:down, reason}) do
    stepped(parent.muro_fsm_down(session, state, {:reason, reason}))
  end

  defp apply_end(_parent, _session, _state, other), do: {:error, {:step, other}}

  defp stepped({:ok, next}), do: {:ok, next}
  defp stepped({:error, reason}), do: {:error, reason}
  defp stepped(other), do: {:error, {:session, other}}

  defp sessions_of(seen, id) do
    for {{^id, _party}, sess} <- seen, do: sess
  end

  defp settled?(parent, seen, id) do
    case sessions_of(seen, id) do
      [] ->
        false

      sessions ->
        Enum.all?(sessions, fn {session, state} -> parent.muro_fsm_done?(session, state) end)
    end
  end

  defp status(parent, seen, id) when is_nil(parent) do
    if sessions_of(seen, id) == [], do: :none, else: :pending
  end

  defp status(parent, seen, id) do
    case sessions_of(seen, id) do
      [] -> :none
      _sessions -> if settled?(parent, seen, id), do: :done, else: :pending
    end
  end

  defp drop_id(seen, id) do
    Map.reject(seen, fn {{i, _party}, _sess} -> i == id end)
  end

  defp leak(parent, ref, seen) do
    ids =
      seen
      |> Enum.map(fn {{id, _party}, _sess} -> id end)
      |> Enum.uniq()
      |> Enum.filter(fn id ->
        settled?(parent, seen, id) and match?({:ok, _phase, _key, _kind}, Step.live(ref, id))
      end)
      |> Enum.sort()

    case ids do
      [] ->
        :ok

      [id | _] ->
        {:ok, _phase, key, kind} = Step.live(ref, id)
        {:error, {:unresolved, id, key, kind}}
    end
  end

  defp row(key, index, id, born, opened_at, kind, phase) do
    %{
      key: key,
      index: index,
      id: id,
      born: born,
      opened_at: opened_at,
      kind: kind,
      phase: phase
    }
  end

  defp held(ref, id) do
    case Enum.find(ref.rows, &(&1.id == id)) do
      %{phase: :held} -> {:held, id}
      other -> flunk("expected #{id} held, got #{inspect(other)}")
    end
  end

  defp compile! do
    dir = System.tmp_dir!() |> Path.join("muro-fam-step-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "book.muro")
    File.write!(path, @book)
    parent = Module.concat(["FamStep#{System.unique_integer([:positive])}"])
    assert {:ok, src} = Muro.emit_fsm(path, parent)
    {mods, diags} = Code.with_diagnostics(fn -> Code.compile_string(src) end)

    warnings =
      Enum.filter(diags, &(match?(%{severity: :warning}, &1) or match?({:warning, _}, &1)))

    assert warnings == [], inspect(warnings, limit: 20)
    assert parent in Enum.map(mods, &elem(&1, 0))

    {parent, Module.concat(parent, Events), Module.concat(parent, Commands),
     Module.concat(parent, Orders), Module.concat(parent, Mixes)}
  end

  defp purge do
    for {mod, _} <- :code.all_loaded(),
        name = Atom.to_string(mod),
        String.starts_with?(name, "Elixir.FamStep") do
      :code.purge(mod)
      :code.delete(mod)
    end
  end
end

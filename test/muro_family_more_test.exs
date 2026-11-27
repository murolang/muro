defmodule Muro.FamilyMoreTest do
  use ExUnit.Case, async: false

  alias Muro.{Check, Parser}
  alias Muro.Family.Graph

  @commands File.read!("examples/keyed-commands.muro")

  @earlier_first """
  temporal earlier-first : commands :=
    forall (k : key). always ((opened k command) implies (earlier_resolved k command))
  """

  test "earlier-first names the instances created earlier" do
    assert Muro.check_file("examples/keyed-commands.muro") == :ok

    assert Check.temporal_lines() == [
             "family commands: slot per key of Command",
             "temporal earlier-first: holds in 370 reachable states, 835 transitions"
           ]
  end

  test "resolved counts the command that is opening, so the same property is refused" do
    src = String.replace(@commands, "earlier_resolved k command", "resolved k command")
    assert {:error, msg} = check(src)
    assert msg =~ "earlier-first:"
    assert msg =~ "fails"
    refute msg =~ "holds in"
  end

  test "never held refuses earlier_resolved when an earlier command is still open" do
    src = String.replace(@commands, "command held while earlier unresolved", "command never held")
    assert {:error, msg} = check(src)
    assert msg =~ "earlier-first:"
    assert msg =~ "fails"
    refute msg =~ "holds in"
  end

  test "a family formula names the four atoms, and earlier_resolved is a family atom" do
    src =
      String.replace(
        @commands,
        @earlier_first,
        "temporal bad : commands := always (server done)\n"
      )

    assert {:error, msg} = check(src)

    assert msg =~
             "bad: a family formula names opened, held, resolved, earlier_resolved, or some_resolved"

    refute msg =~ "holds in"

    meet = """
    session ping := send Nat end
    session pong := recv Nat end
    conform a : ping := put 0 done
    conform b : pong := get (n : Nat) done
    meet wire : a with b buffer 1
    temporal inst : wire := always (earlier_resolved k command)
    """

    assert {:error, msg} = check(meet)
    assert msg =~ "inst: earlier_resolved names an instance of a family"

    one = String.replace(meet, "earlier_resolved k command", "some_resolved k command")
    assert {:error, msg} = check(one)
    assert msg =~ "inst: some_resolved names an instance of a family"
  end

  test "the hold rule and the atom parse, and a missing kind is refused" do
    assert {:ok, book} = Parser.parse(command_book("held while any unresolved"))
    family = Enum.find(book, &(&1.kind == :family))
    assert [%{ctor: "command", hold: :any}] = family.rules

    assert {:error, msg} =
             Parser.parse("""
             family commands : slot per key of Command
               command held forever
             """)

    assert msg =~
             "expected never held, held while earlier unresolved, held while any unresolved, held while <kind> unresolved, or held until <kind> resolved"

    assert {:error, msg} =
             Parser.parse("""
             temporal gap : commands := always (earlier_resolved k)
             """)

    assert msg =~ "expected a key and a kind"
  end

  test "earlier_resolved is the instances known at the opening, and the opener is not one of them" do
    {:ok, search} = prepare(@commands)
    g = search.g
    assert Graph.decide(search, one_formula(:earlier_resolved)) == {:ok, 370, 835}
    assert Enum.all?(search.states, &Graph.respects?(g, &1))

    run = fn _id, mask -> {:run, g.init, 0, mask} end
    prop = {:earlier_resolved, "a", "command"}

    # The command that just opened is running. It is not earlier than itself.
    assert Graph.holds?(g, prop, {run.(0, 1), :absent, :absent})
    refute Graph.holds?(g, {:resolved, "a", "command"}, {run.(0, 1), :absent, :absent})

    # An earlier command known at this opening, still running, refutes the atom.
    refute Graph.holds?(g, prop, {run.(0, 1), run.(1, 3), :absent})
    # The same earlier command, not yet known, does not.
    assert Graph.holds?(g, prop, {run.(0, 1), run.(1, 2), :absent})
    # Giving up counts as resolved. Nothing running holds vacuously.
    assert Graph.holds?(g, prop, {:gave_up, run.(1, 3), :absent})
    assert Graph.holds?(g, prop, {:absent, :absent, :absent})
    assert Graph.holds?(g, prop, {:held, :held, :absent})
  end

  test "withdraw drops a held instance without opening it, and is not a counted step" do
    instances = [
      %{id: 0, key: "a", kind: "command", index: 0},
      %{id: 1, key: "a", kind: "command", index: 1},
      %{id: 2, key: "a", kind: "command", index: 2}
    ]

    {:ok, search} = prepare(@commands, instances)
    g = search.g
    assert {:ok, _states, _transitions} = Graph.decide(search, one_formula(:earlier_resolved))

    refute Enum.any?(search.edges, fn {_state, steps} ->
             Enum.any?(steps, fn {tag, _} -> match?({:withdraw, _}, tag) end)
           end)

    running = {{:run, g.init, 0, 1}, :held, :held}
    refute 2 in Graph.openable(g, running)
    assert {:error, {:opened, 0}} = Graph.withdraw(g, running, 0)

    blocked = {:resolved, :held, :held}
    assert Graph.openable(g, blocked) == [1]
    assert {:ok, dropped} = Graph.withdraw(g, blocked, 1)
    assert Graph.phase(dropped, 1) == :withdrawn
    assert Graph.phase(dropped, 2) == :held

    held_only = {:held, :absent, :absent}
    assert {:ok, gone} = Graph.withdraw(g, held_only, 0)
    assert Graph.phase(gone, 0) == :withdrawn
    refute Graph.holds?(g, {:some_resolved, "a", "command"}, gone)
    refute Graph.holds?(g, {:resolved, "a", "command"}, gone)
    assert Graph.openable(g, dropped) == [2]
    assert {:error, {:resolved, 1}} = Graph.withdraw(g, dropped, 1)

    # A withdrawn earlier row stops blocking and is not resolved.
    run = fn mask -> {:run, g.init, 0, mask} end
    prop = {:earlier_resolved, "a", "command"}
    refute Graph.holds?(g, prop, {:withdrawn, run.(3), :absent})
    assert Graph.holds?(g, prop, {:resolved, run.(3), :absent})
    refute Graph.holds?(g, {:resolved, "a", "command"}, {:withdrawn, :absent, :absent})
    assert Graph.holds?(g, {:resolved, "a", "command"}, {:gave_up, :absent, :absent})
    refute Graph.holds?(g, {:some_resolved, "a", "command"}, {:withdrawn, :absent, :absent})
    assert Graph.holds?(g, {:some_resolved, "a", "command"}, {:gave_up, :absent, :absent})

    assert {:error, {:unknown, 0}} = Graph.withdraw(g, {:absent, :absent, :absent}, 0)
    assert {:error, {:unknown, 9}} = Graph.withdraw(g, {:absent, :absent, :absent}, 9)
    assert {:error, {:unknown, :no}} = Graph.withdraw(g, {:absent, :absent, :absent}, :no)
    assert {:error, {:resolved, 0}} = Graph.withdraw(g, {:gave_up, :held, :held}, 0)
  end

  test "held while any unresolved keeps two commands of one key from running together" do
    any = command_book("held while any unresolved", formula: true)
    earlier = command_book("held while earlier unresolved", formula: true)

    {:ok, any_search} = prepare(any)
    {:ok, earlier_search} = prepare(earlier)

    assert Enum.all?(any_search.states, &Graph.respects?(any_search.g, &1))
    assert Enum.all?(earlier_search.states, &Graph.respects?(earlier_search.g, &1))

    refute Enum.any?(any_search.states, &both_running?/1)
    assert Enum.any?(any_search.states, &older_held_while_newer_runs?/1)

    assert Enum.any?(earlier_search.states, &both_running?/1)
    refute Enum.any?(earlier_search.states, &older_held_while_newer_runs?/1)

    # A held instance does not hold another. The instance does not hold itself.
    any_g = any_search.g

    assert Enum.any?(
             Graph.edges(any_g, {:absent, :absent, :absent}),
             &match?({{:open, 0}, _}, &1)
           )

    assert Enum.any?(Graph.edges(any_g, {:held, :absent, :absent}), &match?({{:open, 1}, _}, &1))
    refute Enum.any?(Graph.edges(any_g, {:held, :absent, :absent}), &match?({{:hold, 1}, _}, &1))

    earlier_g = earlier_search.g

    assert Enum.any?(
             Graph.edges(earlier_g, {:held, :absent, :absent}),
             &match?({{:hold, 1}, _}, &1)
           )

    refute Enum.any?(
             Graph.edges(earlier_g, {:held, :absent, :absent}),
             &match?({{:open, 1}, _}, &1)
           )

    # A later command can open while an earlier one is held. That earlier
    # command is known, and it is not resolved, so earlier_resolved fails.
    # The same three instances under the earlier rule keep the atom.
    three = [
      %{id: 0, key: "a", kind: "command", index: 0},
      %{id: 1, key: "a", kind: "command", index: 1},
      %{id: 2, key: "a", kind: "command", index: 2}
    ]

    {:ok, any_three} = prepare(command_book("held while any unresolved"), three)
    assert {:error, msg} = Graph.decide(any_three, one_formula(:earlier_resolved))
    assert msg =~ "fails"

    {:ok, earlier_three} = prepare(@commands, three)
    assert {:ok, _, _} = Graph.decide(earlier_three, one_formula(:earlier_resolved))
  end

  test "the dispatcher withdraws a held command and then releases the later one" do
    {disp, _parent, src} = compile!(@commands, Commands)
    assert src =~ "def withdraw(state, id)"
    assert src =~ "def new, do: %{n: 0, by: %{}, id: %{}, departed: %{}, floor: -1}"

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :command, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :command, 1)
    assert {:held, 2, state} = disp.arrive(state, "a", :command, 2)

    assert {:ok, [], withdrawn} = disp.withdraw(state, 1)
    assert withdrawn.by["a"][0] == {0, :command, :open}
    assert withdrawn.by["a"][2] == {2, :command, :held}
    refute Map.has_key?(withdrawn.by["a"], 1)
    refute Map.has_key?(withdrawn.id, 1)
    # The id map drops an id that has left. The counter tells it apart.
    # The creation index stays above this key's prefix.
    assert Map.keys(withdrawn) |> Enum.sort() == [:by, :departed, :floor, :id, :n]
    assert withdrawn.n == 3
    assert withdrawn.departed["a"] == {-1, %{1 => true}}
    assert {:error, {:departed, "a", 1}} = disp.arrive(withdrawn, "a", :command, 1)
    refute inspect(withdrawn.by) =~ ":resolved"
    refute inspect(withdrawn.id) =~ ":resolved"

    assert {:ok, [{2, "a", :command}], released} = disp.resolved(withdrawn, 0)
    assert released.by["a"][2] == {2, :command, :open}
    assert released.departed["a"] == {1, %{}}
    assert {:error, {:unknown, 1}} = disp.resolved(released, 1)
    assert {:error, {:resolved, 1}} = disp.withdraw(released, 1)
    assert {:error, {:departed, "a", 0}} = disp.arrive(released, "a", :command, 0)
    assert {:error, {:departed, "a", 1}} = disp.arrive(released, "a", :command, 1)

    fresh = disp.new()
    assert {:open, 0, fresh} = disp.arrive(fresh, "a", :command, 0)
    assert {:held, 1, fresh} = disp.arrive(fresh, "a", :command, 1)
    assert {:held, 2, fresh} = disp.arrive(fresh, "a", :command, 2)
    assert {:ok, [{1, "a", :command}], kept} = disp.resolved(fresh, 0)
    assert kept.by["a"][2] == {2, :command, :held}

    assert {:error, {:opened, 0}} = disp.withdraw(fresh, 0)
    assert {:error, {:unknown, 9}} = disp.withdraw(disp.new(), 9)
    assert {:error, {:unknown, 0}} = disp.withdraw(disp.new(), 0)

    dirty = put_in(state, [:by, "a", 9], :poison)
    assert {:error, {:state, _}} = disp.withdraw(dirty, 1)
    assert {:ok, [], _} = disp.withdraw(state, 1)

    assert :ok =
             disp.check_trace([
               {:arrive, "a", :command, 0},
               {:arrive, "a", :command, 1},
               {:arrive, "a", :command, 2},
               {:withdraw, 1},
               {:resolved, 0},
               {:resolved, 2}
             ])

    assert {:error, {1, {:opened, 0}}} =
             disp.check_trace([
               {:arrive, "a", :command, 0},
               {:withdraw, 0}
             ])

    assert {:error, {0, {:unknown, 4}}} = disp.check_trace([{:withdraw, 4}])

    assert {:error, {3, {:resolved, 1}}} =
             disp.check_trace([
               {:arrive, "a", :command, 0},
               {:arrive, "a", :command, 1},
               {:withdraw, 1},
               {:withdraw, 1}
             ])

    assert {:error, {3, {:unknown, 1}}} =
             disp.check_trace([
               {:arrive, "a", :command, 0},
               {:arrive, "a", :command, 1},
               {:withdraw, 1},
               {:task, 1, {:send, :ok}}
             ])

    assert {:error, {:unresolved, 0, "a", :command}} =
             disp.check_trace([
               {:arrive, "a", :command, 0},
               {:arrive, "a", :command, 1},
               {:task, 0, {:send, :ok}},
               {:server, 0, {:recv, :ok}},
               {:withdraw, 1}
             ])
  end

  test "an older command read late stays held while a newer one is open" do
    {any, _, _} = compile!(command_book("held while any unresolved"), Commands)
    {earlier, _, _} = compile!(command_book("held while earlier unresolved"), Commands)

    any_state = any.new()
    assert {:open, 0, any_state} = any.arrive(any_state, "a", :command, 1)
    assert {:held, 1, any_state} = any.arrive(any_state, "a", :command, 0)
    assert any_state.by["a"][1] == {0, :command, :open}
    assert any_state.by["a"][0] == {1, :command, :held}

    assert {:held, 2, any_state} = any.arrive(any_state, "a", :command, 2)
    assert {:ok, [{1, "a", :command}], any_state} = any.resolved(any_state, 0)
    assert any_state.by["a"][0] == {1, :command, :open}
    assert any_state.by["a"][2] == {2, :command, :held}

    # A held row does not block a later arrival. The instance does not hold itself.
    lone = %{
      n: 1,
      by: %{"a" => %{0 => {0, :command, :held}}},
      id: %{0 => {"a", 0}},
      departed: %{},
      floor: -1
    }

    assert {:open, 1, opened} = any.arrive(lone, "a", :command, 1)
    assert opened.by["a"][0] == {0, :command, :held}
    assert opened.by["a"][1] == {1, :command, :open}
    assert {:open, 0, _} = any.arrive(any.new(), "a", :command, 0)

    old = earlier.new()
    assert {:open, 0, old} = earlier.arrive(old, "a", :command, 1)
    assert {:open, 1, old} = earlier.arrive(old, "a", :command, 0)
    assert old.by["a"][1] == {0, :command, :open}
    assert old.by["a"][0] == {1, :command, :open}

    assert :ok = any.check_trace([{:arrive, "a", :command, 1}, {:arrive, "a", :command, 0}])
    assert :ok = earlier.check_trace([{:arrive, "a", :command, 1}, {:arrive, "a", :command, 0}])
  end

  test "a release that also opens another kind leaves the any instance held" do
    src = """
    data Kind : Type where
      early : Kind
      wide : Kind
    data Report : Type where
      ok : Report
    session task-work := send Report end
    session server-wait := recv Report end
    conform task : task-work := put ok done
    conform server : server-wait :=
      get (r : Report) done
    meet slot : server with task buffer 1
    family both : slot per key of Kind
      early held while earlier unresolved
      wide held while any unresolved
    """

    {disp, _, _} = compile!(src, Both)

    state = %{
      n: 3,
      by: %{
        "a" => %{
          0 => {0, :early, :held},
          1 => {1, :wide, :held},
          3 => {2, :early, :held}
        }
      },
      id: %{0 => {"a", 0}, 1 => {"a", 1}, 2 => {"a", 3}},
      departed: %{},
      floor: -1
    }

    assert {:ok, [{0, "a", :early}], next} = disp.withdraw(state, 2)
    assert next.by["a"][0] == {0, :early, :open}
    assert next.by["a"][1] == {1, :wide, :held}
    refute Map.has_key?(next.by["a"], 3)
  end

  test "every hold compiles, including a family that never holds" do
    for rule <- [
          "never held",
          "held while earlier unresolved",
          "held while any unresolved"
        ] do
      {disp, _parent, _src} = compile!(command_book(rule), Commands)
      assert {:open, 0, _} = disp.arrive(disp.new(), "a", :command, 0)
    end
  end

  test "an id that has left: withdraw says resolved, resolved and finish say unknown" do
    {disp, parent, _src} = compile!(@commands, Commands)
    server = Module.concat(parent, ServerWait)

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :command, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :command, 1)
    assert {:ok, [], state} = disp.withdraw(state, 1)
    assert {:ok, [], state} = disp.resolved(state, 0)
    assert state.by == %{} and state.id == %{} and state.n == 2

    for id <- [0, 1] do
      assert {:error, {:resolved, ^id}} = disp.withdraw(state, id)
      assert {:error, {:unknown, ^id}} = disp.resolved(state, id)
      assert {:error, {:unknown, ^id}} = disp.finish(state, id, server.init(), {:recv, :ok})
    end

    # The counter is the only record: an id at or past it, or not an
    # integer, was never returned.
    for id <- [2, 9, -1, :no] do
      assert {:error, {:unknown, ^id}} = disp.withdraw(state, id)
      assert {:error, {:unknown, ^id}} = disp.resolved(state, id)
    end
  end

  test "finish with rerun keeps the open row, so a withdraw does not release the next one" do
    {disp, parent, _src} = compile!(@commands, Commands)
    server = Module.concat(parent, ServerWait)

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :command, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :command, 1)
    assert {:held, 2, state} = disp.arrive(state, "a", :command, 2)

    assert {:ok, [], rerun} = disp.finish(state, 0, server.init(), {:recv, :ok}, :rerun)
    assert rerun == state
    assert {:error, {:opened, 0}} = disp.withdraw(rerun, 0)

    assert {:ok, [], dropped} = disp.withdraw(rerun, 1)
    assert dropped.by["a"][0] == {0, :command, :open}
    assert dropped.by["a"][2] == {2, :command, :held}
    assert {:error, {:unknown, 1}} = disp.finish(dropped, 1, server.init(), {:recv, :ok}, :rerun)

    assert {:ok, [], again} = disp.finish(dropped, 0, server.init(), {:recv, :ok}, :rerun)
    assert again == dropped
    assert {:ok, [{2, "a", :command}], done} = disp.finish(again, 0, server.init(), {:recv, :ok})
    assert {:error, {:resolved, 0}} = disp.withdraw(done, 0)
    assert {:error, {:opened, 2}} = disp.withdraw(done, 2)

    assert :ok =
             disp.check_trace([
               {:arrive, "a", :command, 0},
               {:arrive, "a", :command, 1},
               {:arrive, "a", :command, 2},
               {:server, 0, {:recv, :ok}},
               {:rerun, 0},
               {:withdraw, 1},
               {:server, 0, {:recv, :ok}},
               {:resolved, 0},
               {:resolved, 2}
             ])

    assert {:error, {4, {:unknown, 1}}} =
             disp.check_trace([
               {:arrive, "a", :command, 0},
               {:arrive, "a", :command, 1},
               {:withdraw, 1},
               {:server, 0, {:recv, :ok}},
               {:rerun, 1}
             ])

    assert {:error, {4, {:opened, 0}}} =
             disp.check_trace([
               {:arrive, "a", :command, 0},
               {:arrive, "a", :command, 1},
               {:server, 0, {:recv, :ok}},
               {:rerun, 0},
               {:withdraw, 0}
             ])
  end

  test "under held while any unresolved a held command is never resolved and leads to opening" do
    held = "forall (k : key). always ((held k command) implies (not (resolved k command)))"
    opens = "forall (k : key). (held k command) leads_to (opened k command)"

    for {rule, count} <- [
          {"held while any unresolved", "273 reachable states, 550 transitions"},
          {"held while earlier unresolved", "370 reachable states, 835 transitions"}
        ] do
      src =
        command_book(rule, formula: true) <>
          "temporal held-waits : commands :=\n  #{held}\n" <>
          "temporal held-opens : commands :=\n  #{opens}\n"

      assert :ok = check(src)

      assert Check.temporal_lines() == [
               "family commands: slot per key of Command",
               "temporal earlier-first: holds in #{count}",
               "temporal held-waits: holds in #{count}",
               "temporal held-opens: holds in #{count}"
             ]
    end
  end

  test "earlier_resolved of one kind is read when another kind opens" do
    wide_after_early =
      "forall (k : key). always ((opened k wide) implies (earlier_resolved k early))"

    early_after_wide =
      "forall (k : key). always ((opened k early) implies (earlier_resolved k wide))"

    both_earlier = ["early held while earlier unresolved", "wide held while earlier unresolved"]
    mixed = ["early held while earlier unresolved", "wide held while any unresolved"]

    assert :ok = check(two_kinds(both_earlier, early_after_wide))

    assert Check.temporal_lines() == [
             "family fam: slot per key of Kind",
             "temporal p: holds in 40072 reachable states, 134652 transitions"
           ]

    assert :ok = check(two_kinds(mixed, wide_after_early))

    assert Check.temporal_lines() == [
             "family fam: slot per key of Kind",
             "temporal p: holds in 34341 reachable states, 107914 transitions"
           ]

    # A later wide opens while an earlier wide is held. That wide is known
    # at the opening of the next early, and it is not resolved.
    assert {:error, msg} = check(two_kinds(mixed, early_after_wide))
    assert msg =~ "p: always ((opened a early) implies (earlier_resolved a wide)) fails"
    assert msg =~ "a wide 2: held"

    # An early that never holds may open before a wide created after it is
    # resolved, and a wide that never holds opens beside a running early.
    assert {:error, msg} =
             check(two_kinds(["early never held", "wide never held"], wide_after_early))

    assert msg =~ "fails"
  end

  test "every dispatcher step on held while any unresolved is a run of the family graph" do
    instances = [
      %{id: 0, key: "a", kind: "command", index: 0},
      %{id: 1, key: "a", kind: "command", index: 1},
      %{id: 2, key: "a", kind: "command", index: 2},
      %{id: 3, key: "b", kind: "command", index: 0}
    ]

    src = command_book("held while any unresolved")
    {disp, _parent, _src} = compile!(src, Commands)
    {:ok, search} = prepare(src, instances)

    assert lock_walk(disp, search, disp.new(), search.g.start, instances, %{}, []) > 100
  end

  test "every dispatcher step on mixed earlier and any holds is a run of the family graph" do
    instances = [
      %{id: 0, key: "a", kind: "early", index: 0},
      %{id: 1, key: "a", kind: "wide", index: 1},
      %{id: 2, key: "a", kind: "early", index: 2},
      %{id: 3, key: "a", kind: "wide", index: 3}
    ]

    src =
      two_kinds(
        ["early held while earlier unresolved", "wide held while any unresolved"],
        nil
      )

    {disp, _parent, _src} = compile!(src, Fam)
    {:ok, search} = prepare(src, instances)

    assert lock_walk(disp, search, disp.new(), search.g.start, instances, %{}, []) > 100
  end

  # One dispatcher step at a time, matched on the graph. An arrival is the
  # graph's open or hold. A resolution is the graph's meeting run to its
  # resolve, then the dispatcher's releases as graph opens. A withdrawal is
  # Graph.withdraw, then those releases. After each release the graph has
  # no held instance left that could open: the dispatcher opens one of the
  # graph's choices, and where the graph has several `any` instances to
  # choose from the dispatcher takes the least index. Refusals match too.
  defp lock_walk(disp, search, dst, gst, remaining, live, trace) do
    g = search.g

    arrived =
      Enum.reduce(remaining, 0, fn inst, acc ->
        kind = String.to_atom(inst.kind)
        assert {phase, id, dst2} = disp.arrive(dst, inst.key, kind, inst.index)
        tag = if phase == :open, do: {:open, inst.id}, else: {:hold, inst.id}
        gst2 = step!(search, gst, tag, trace)
        left = Enum.reject(remaining, &(&1.id == inst.id))
        step = {:arrive, inst.key, kind, inst.index, phase}
        acc + lock_walk(disp, search, dst2, gst2, left, Map.put(live, id, inst), [step | trace])
      end)

    finished =
      Enum.reduce(live, 0, fn {id, inst}, acc ->
        {op, dst2, released, gst1} =
          case Graph.phase(gst, inst.id) do
            :held ->
              assert {:error, {:held, ^id}} = disp.resolved(dst, id)
              assert {:ok, released, dst2} = disp.withdraw(dst, id)
              assert {:ok, gst1} = Graph.withdraw(g, gst, inst.id)
              {:withdraw, dst2, released, gst1}

            {:run, _, _, _} ->
              assert {:error, {:opened, ^id}} = disp.withdraw(dst, id)
              assert {:error, {:opened, _}} = Graph.withdraw(g, gst, inst.id)
              assert {:ok, released, dst2} = disp.resolved(dst, id)
              {:resolved, dst2, released, resolve!(search, gst, inst.id, trace)}
          end

        trace = [{op, id, released} | trace]
        gst2 = release!(search, gst1, released, live, trace)
        assert {:error, {:resolved, ^id}} = disp.withdraw(dst2, id)
        assert {:error, {:resolved, _}} = Graph.withdraw(g, gst2, inst.id)
        acc + lock_walk(disp, search, dst2, gst2, remaining, Map.delete(live, id), trace)
      end)

    max(arrived + finished, 1)
  end

  defp release!(search, gst, released, live, trace) do
    ids =
      Enum.map(released, fn {id, key, kind} ->
        inst = Map.fetch!(live, id)
        assert {inst.key, inst.kind} == {key, Atom.to_string(kind)}
        inst
      end)

    opened =
      ids
      |> Enum.sort_by(& &1.index)
      |> Enum.reduce(gst, fn inst, st ->
        assert inst.id in Graph.openable(search.g, st),
               "dispatcher opened #{inspect(inst)} the graph holds after #{inspect(Enum.reverse(trace))}"

        step!(search, st, {:open, inst.id}, trace)
      end)

    assert Graph.openable(search.g, opened) == [],
           "graph can still open #{inspect(Graph.openable(search.g, opened))} after #{inspect(Enum.reverse(trace))}"

    opened
  end

  defp resolve!(search, gst, gid, trace) do
    resolve_bfs(search, gid, MapSet.new(), [gst]) ||
      flunk("resolve of #{gid} is not a graph run after #{inspect(Enum.reverse(trace))}")
  end

  defp resolve_bfs(_search, _gid, _seen, []), do: nil

  defp resolve_bfs(search, gid, seen, [state | rest]) do
    if MapSet.member?(seen, state) do
      resolve_bfs(search, gid, seen, rest)
    else
      steps = graph_steps(search, state)

      case Enum.find(steps, fn {tag, _} -> tag in [{:resolve, gid}, {:give_up, gid}] end) do
        {_tag, dest} ->
          dest

        nil ->
          more =
            for {tag, dest} <- steps,
                match?({:meet, ^gid, _}, tag) or tag == {:retry, gid},
                do: dest

          resolve_bfs(search, gid, MapSet.put(seen, state), rest ++ more)
      end
    end
  end

  defp step!(search, state, tag, trace) do
    steps = graph_steps(search, state)

    case Enum.find(steps, fn {t, _} -> t == tag end) do
      {_, dest} ->
        dest

      nil ->
        flunk(
          "graph has no #{inspect(tag)} after #{inspect(Enum.reverse(trace))}; edges #{inspect(Enum.map(steps, &elem(&1, 0)))}"
        )
    end
  end

  defp graph_steps(search, state) do
    case Map.fetch(search.edges, state) do
      {:ok, steps} -> steps
      :error -> Graph.edges(search.g, state)
    end
  end

  defp two_kinds(rules, formula) do
    temporal = if formula, do: "temporal p : fam :=\n  #{formula}\n", else: ""

    """
    data Kind : Type where
      early : Kind
      wide : Kind
    data Report : Type where
      ok : Report
    session task-work := send Report end
    session server-wait := recv Report end
    conform task : task-work := put ok done
    conform server : server-wait :=
      get (r : Report) done
    meet slot : server with task buffer 1
    family fam : slot per key of Kind
    #{Enum.map_join(rules, "\n", &"  #{&1}")}
    #{temporal}
    """
  end

  defp one_formula(atom) do
    {:forall, "k", {:dat, "key", []},
     {:always, {:imp, {:opened, "k", "command"}, {atom, "k", "command"}}}}
  end

  defp both_running?(state) do
    match?({:run, _, _, _}, Graph.phase(state, 0)) and
      match?({:run, _, _, _}, Graph.phase(state, 1))
  end

  defp older_held_while_newer_runs?(state) do
    Graph.phase(state, 0) == :held and match?({:run, _, _, _}, Graph.phase(state, 1))
  end

  defp command_book(rule, opts \\ []) do
    formula =
      if Keyword.get(opts, :formula, false) do
        @earlier_first
      else
        ""
      end

    """
    data Command : Type where
      command : Command
    data Report : Type where
      ok : Report
    session task-work := send Report end
    session server-wait := recv Report end
    conform task : task-work := put ok done
    conform server : server-wait :=
      get (r : Report) done
    meet slot : server with task buffer 1
    family commands : slot per key of Command
      command #{rule}
    #{formula}
    """
  end

  defp prepare(src, instances \\ nil) do
    assert {:ok, book} = Parser.parse(src)
    family = Enum.find(book, &(&1.kind == :family))
    opts = if instances, do: [instances: instances], else: []
    assert {:ok, search} = Graph.prepare(book, family, opts)
    {:ok, search}
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end

  defp compile!(src, family) do
    dir = System.tmp_dir!() |> Path.join("muro-fam-more-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "book.muro")
    File.write!(path, src)
    parent = Module.concat(["FamMore#{System.unique_integer([:positive])}"])
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

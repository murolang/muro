defmodule Muro.FamilyMoreTest do
  use ExUnit.Case, async: false

  alias Muro.{Check, Parser}
  alias Muro.Family.Graph

  @commands File.read!("examples/keyed-commands.muro")

  @one_at_a_time """
  temporal one-at-a-time : commands :=
    forall (k : key). always ((opened k command) implies (earlier_resolved k command))
  """

  test "one command at a time names the instances created earlier" do
    assert Muro.check_file("examples/keyed-commands.muro") == :ok

    assert Check.temporal_lines() == [
             "family commands: slot per key of Command",
             "temporal one-at-a-time: holds in 370 reachable states, 835 transitions"
           ]
  end

  test "resolved counts the command that is opening, so the same property is refused" do
    src = String.replace(@commands, "earlier_resolved k command", "resolved k command")
    assert {:error, msg} = check(src)
    assert msg =~ "one-at-a-time:"
    assert msg =~ "fails"
    refute msg =~ "holds in"
  end

  test "never held refuses earlier_resolved when an earlier command is still open" do
    src = String.replace(@commands, "command held while earlier unresolved", "command never held")
    assert {:error, msg} = check(src)
    assert msg =~ "one-at-a-time:"
    assert msg =~ "fails"
    refute msg =~ "holds in"
  end

  test "a family formula names the four atoms, and earlier_resolved is a family atom" do
    src =
      String.replace(
        @commands,
        @one_at_a_time,
        "temporal bad : commands := always (server done)\n"
      )

    assert {:error, msg} = check(src)
    assert msg =~ "bad: a family formula names opened, held, resolved, or earlier_resolved"
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
             "expected never held, held while earlier unresolved, or held while any unresolved"

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

  test "withdraw resolves a held instance without opening it, and is not a counted step" do
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
    assert Graph.phase(dropped, 1) == :resolved
    assert Graph.phase(dropped, 2) == :held
    assert Graph.openable(g, dropped) == [2]
    assert {:error, {:resolved, 1}} = Graph.withdraw(g, dropped, 1)

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
    assert src =~ "def new, do: %{n: 0, by: %{}, id: %{}, done: %{}}"

    state = disp.new()
    assert {:open, 0, state} = disp.arrive(state, "a", :command, 0)
    assert {:held, 1, state} = disp.arrive(state, "a", :command, 1)
    assert {:held, 2, state} = disp.arrive(state, "a", :command, 2)

    assert {:ok, [], withdrawn} = disp.withdraw(state, 1)
    assert withdrawn.by["a"][0] == {0, :command, :open}
    assert withdrawn.by["a"][2] == {2, :command, :held}
    refute Map.has_key?(withdrawn.by["a"], 1)
    refute Map.has_key?(withdrawn.id, 1)
    assert withdrawn.done[1] == true
    refute inspect(withdrawn.by) =~ ":resolved"
    refute inspect(withdrawn.id) =~ ":resolved"

    assert {:ok, [{2, "a", :command}], released} = disp.resolved(withdrawn, 0)
    assert released.by["a"][2] == {2, :command, :open}
    assert {:error, {:unknown, 1}} = disp.resolved(released, 1)
    assert {:error, {:resolved, 1}} = disp.withdraw(released, 1)

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
    lone = %{n: 1, by: %{"a" => %{0 => {0, :command, :held}}}, id: %{0 => {"a", 0}}, done: %{}}
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
      done: %{}
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
        @one_at_a_time
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

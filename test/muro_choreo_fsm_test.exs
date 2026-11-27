defmodule Muro.ChoreoFsmTest do
  use ExUnit.Case, async: false

  alias Muro.{Check, Choreo, Parser}

  @moduletag timeout: 120_000

  @plan """
  choreography plan
    roles release, front, worker
    release -> front : deploy
    front -> release : deployed
    release -> worker : deploy
    worker -> release : deployed

  session rf := seen release with front in plan
  session rw := seen release with worker in plan

  def kept : run Nat := 0
  """

  @order """
  data Reply : Type where
    written : Reply
    invalid : Reply

  choreography order
    roles client, shop, bank
    client -> shop : buy Nat
    shop -> bank : charge Nat
    bank chooses
      paid: bank -> shop : ok Reply
            shop -> client : done
      refused: bank -> shop : no
               shop -> client : sorry

  def kept : run Nat := 0
  """

  setup do
    on_exit(fn ->
      for {mod, _} <- :code.all_loaded(),
          String.starts_with?(Atom.to_string(mod), "Elixir.ChoreoFsmT") do
        :code.purge(mod)
        :code.delete(mod)
      end
    end)

    :ok
  end

  describe "the #308 release" do
    test "the monitor takes the written order and refuses the worker before the front" do
      {parent, _src} = emit_text!("plan.muro", @plan)
      plan = Module.concat(parent, Plan)

      s0 = plan.init()
      refute plan.done?(s0)
      assert plan.expected(s0) == {:message, :release, :front, :deploy, :unit}

      assert {:ok, s1} = plan.step(s0, :release, :front, :deploy)
      assert plan.expected(s1) == {:message, :front, :release, :deployed, :unit}

      assert plan.step(s1, :release, :worker, :deploy) ==
               {:error,
                {:unexpected, "plan.muro:1 choreography plan: second front -> release : deployed",
                 {:message, :front, :release, :deployed, :unit}, {:release, :worker, :deploy}}}

      assert {:ok, s2} = plan.step(s1, :front, :release, :deployed)
      assert {:ok, s3} = plan.step(s2, :release, :worker, :deploy, :tt)
      assert {:ok, s4} = plan.step(s3, :worker, :release, :deployed)
      assert plan.done?(s4)
      assert plan.expected(s4) == :done

      assert plan.step(s4, :release, :front, :deploy) ==
               {:error,
                {:unexpected, "plan.muro:1 choreography plan: end", :done,
                 {:release, :front, :deploy}}}

      # The state is plain data, and the same events give the same state.
      assert {:ok, ^s1} = plan.step(plan.init(), :release, :front, :deploy)
    end

    test "check_trace accepts a prefix, and complete: true asks for the end" do
      {parent, _src} = emit_text!("plan.muro", @plan)
      plan = Module.concat(parent, Plan)

      front = [{:release, :front, :deploy}, {:front, :release, :deployed}]
      worker = [{:release, :worker, :deploy}, {:worker, :release, :deployed}]

      assert plan.check_trace([]) == :ok
      assert plan.check_trace(front) == :ok
      assert plan.check_trace(front ++ worker, complete: true) == :ok
      assert plan.check_trace(front ++ worker, complete: false) == :ok

      assert plan.check_trace(front, complete: true) ==
               {:error,
                {2,
                 {:incomplete, "plan.muro:1 choreography plan: third release -> worker : deploy",
                  {:message, :release, :worker, :deploy, :unit}}}}

      assert plan.check_trace(worker ++ front) ==
               {:error,
                {0,
                 {:unexpected, "plan.muro:1 choreography plan: first release -> front : deploy",
                  {:message, :release, :front, :deploy, :unit}, {:release, :worker, :deploy}}}}

      # `release` talks to `worker` first: each projection is still a
      # legal prefix of its own session, and the monitor refuses it.
      early = [{:release, :front, :deploy}, {:release, :worker, :deploy}]

      assert {:error, {1, {:unexpected, _, _, {:release, :worker, :deploy}}}} =
               plan.check_trace(early)

      assert plan.check_trace(:nope) == {:error, {:trace, :nope}}
      assert plan.check_trace(:nope, complete: true) == {:error, {:trace, :nope}}
    end

    test "the projections emit as session state machines" do
      {parent, src} = emit_text!("plan.muro", @plan)
      rf = Module.concat(parent, Rf)
      rw = Module.concat(parent, Rw)

      refute src =~ "seen is not a state machine"

      s = rf.init()
      assert rf.expected(s) == {:send, :unit}
      assert {:ok, s} = rf.send(s, :tt)
      assert rf.expected(s) == {:recv, :unit}

      assert rf.send(s, :tt) ==
               {:error,
                {:unexpected, "plan.muro:8 session rf: first recv Unit", {:recv, :unit}, :tt}}

      assert {:ok, s} = rf.recv(s, :tt)
      assert rf.done?(s)

      assert rw.check_trace([{:send, :tt}, {:recv, :tt}], complete: true) == :ok
      assert rf.check_trace([{:send, :tt}]) == :ok

      assert {:error,
              {1, {:incomplete, "plan.muro:9 session rw: first recv Unit", {:recv, :unit}}}} =
               rw.check_trace([{:send, :tt}], complete: true)
    end

    test "the example book checks and emits" do
      assert Muro.check_file("examples/release-plan.muro") == :ok
      assert {:ok, src} = Muro.emit_fsm("examples/release-plan.muro", ReleasePlanFsm)
      assert src =~ "examples/release-plan.muro:"
      assert src =~ "choreography plan: first release -> front : deploy"
      assert src =~ "defmodule Plan do"
      assert src =~ "defmodule Rf do"
      assert src =~ "defmodule Rw do"
    end
  end

  describe "payloads and choices" do
    test "a payload is checked on its wire form, and a choice names its labels" do
      {parent, _src} = emit_text!("order.muro", @order)
      order = Module.concat(parent, Order)

      s = order.init()
      assert order.expected(s) == {:message, :client, :shop, :buy, :nat}

      # A payload that is not Unit is step/5. step/4 is the value `:tt`.
      assert {:error, {:unexpected, step, {:message, :client, :shop, :buy, :nat}, ev}} =
               order.step(s, :client, :shop, :buy)

      assert step == "order.muro:5 choreography order: first client -> shop : buy Nat"
      assert ev == {:client, :shop, :buy}

      assert {:error, {:unexpected, ^step, _, {:client, :shop, :buy, -1}}} =
               order.step(s, :client, :shop, :buy, -1)

      assert {:error, {:unexpected, ^step, _, {:client, :shop, :buy, "3"}}} =
               order.step(s, :client, :shop, :buy, "3")

      assert {:ok, s} = order.step(s, :client, :shop, :buy, 3)
      assert {:ok, s} = order.step(s, :shop, :bank, :charge, 2)

      assert order.expected(s) == {:choose, :bank, [:paid, :refused]}

      assert order.choose(s, :bank, :maybe) ==
               {:error,
                {:unexpected, "order.muro:5 choreography order: first bank chooses",
                 {:choose, :bank, [:paid, :refused]}, {:bank, :maybe}}}

      assert {:error, {:unexpected, _, _, {:shop, :paid}}} = order.choose(s, :shop, :paid)

      assert {:error, {:unexpected, _, _, {:bank, :shop, :ok, :written}}} =
               order.step(s, :bank, :shop, :ok, :written)

      assert {:ok, paid} = order.choose(s, :bank, :paid)
      assert order.expected(paid) == {:message, :bank, :shop, :ok, {:data, "Reply", []}}

      assert {:error,
              {:unexpected, "order.muro:5 choreography order: third bank -> shop : ok Reply", _,
               {:bank, :shop, :ok, :bogus}}} = order.step(paid, :bank, :shop, :ok, :bogus)

      assert {:ok, paid} = order.step(paid, :bank, :shop, :ok, :written)
      assert {:ok, paid} = order.step(paid, :shop, :client, :done)
      assert order.done?(paid)

      assert {:ok, refused} = order.choose(s, :bank, :refused)
      assert order.expected(refused) == {:message, :bank, :shop, :no, :unit}
    end

    test "check_trace takes a choice as {role, label}" do
      {parent, _src} = emit_text!("order.muro", @order)
      order = Module.concat(parent, Order)

      run = [
        {:client, :shop, :buy, 1},
        {:shop, :bank, :charge, 1},
        {:bank, :refused},
        {:bank, :shop, :no},
        {:shop, :client, :sorry}
      ]

      assert order.check_trace(run, complete: true) == :ok

      assert order.check_trace(Enum.take(run, 2), complete: true) ==
               {:error,
                {2,
                 {:incomplete, "order.muro:5 choreography order: first bank chooses",
                  {:choose, :bank, [:paid, :refused]}}}}

      assert {:error,
              {3,
               {:unexpected, _, {:message, :bank, :shop, :no, :unit},
                {:bank, :shop, :ok, :written}}}} =
               order.check_trace(Enum.take(run, 3) ++ [{:bank, :shop, :ok, :written}])

      assert {:error, {0, {:unexpected, _, _, :junk}}} = order.check_trace([:junk])
    end

    test "a value that is not a state is unexpected and nothing raises" do
      {parent, _src} = emit_text!("order.muro", @order)
      order = Module.concat(parent, Order)
      end_step = "order.muro:5 choreography order: end"

      for bad <- [nil, %{}, :done, %{k: "order", g: :nope}, %{k: "other", g: {:end, "x"}}] do
        assert order.step(bad, :client, :shop, :buy, 1) ==
                 {:error, {:unexpected, end_step, :done, {:client, :shop, :buy, 1}}}

        assert order.choose(bad, :bank, :paid) ==
                 {:error, {:unexpected, end_step, :done, {:bank, :paid}}}

        refute order.done?(bad)
        assert order.expected(bad) == :done
      end
    end
  end

  describe "the module" do
    test "a book with a choreography and no session is accepted" do
      {parent, src} = emit_text!("order.muro", @order)
      assert src =~ "defmodule Order do"
      refute src =~ "has no session"
      assert Code.ensure_loaded?(Module.concat(parent, Order))

      assert Muro.emit_fsm("examples/pair.muro", PairFsm) ==
               {:error, "examples/pair.muro has no session to emit"}
    end

    test "a book with no choreography emits no monitor" do
      {:ok, src} = Muro.emit_fsm("examples/meet.muro", MeetFsm)
      refute src =~ "muro_fsm_g_"
      refute src =~ "choreography"
    end

    test "a choreography child claims a name after the sessions" do
      text = """
      choreography go-now
        roles a, b
        a -> b : go

      session go_now := seen a with b in go-now

      def kept : run Nat := 0
      """

      assert Muro.Emit.elixir_alias("go-now") == Muro.Emit.elixir_alias("go_now")

      {parent, src} = emit_text!("clash.muro", text)
      assert src =~ "defmodule GoNow do"
      assert src =~ "defmodule GoNow_2 do"
      session = Module.concat(parent, GoNow)
      monitor = Module.concat(parent, GoNow_2)

      assert {:ok, _} = session.send(session.init(), :tt)
      assert {:ok, m} = monitor.step(monitor.init(), :a, :b, :go)
      assert monitor.done?(m)
    end

    test "a name with a hyphen is the atom spelling of the book" do
      text = """
      choreography two-step
        roles left-side, right
        left-side -> right : go-now

      def kept : run Nat := 0
      """

      {parent, src} = emit_text!("hyphen.muro", text)
      monitor = Module.concat(parent, Muro.Emit.elixir_alias("two-step"))
      assert src =~ "choreography two-step: first left-side -> right : go-now"

      left = String.to_atom(Muro.Emit.elixir_atom_name("left-side"))
      go = String.to_atom(Muro.Emit.elixir_atom_name("go-now"))
      assert monitor.expected(monitor.init()) == {:message, left, :right, go, :unit}
      assert {:ok, s} = monitor.step(monitor.init(), left, :right, go)
      assert monitor.done?(s)
    end

    test "two-phase commit emits a monitor and its six projections" do
      {:ok, src} = Muro.emit_fsm("examples/two-phase-commit.muro", TwoPhaseCommitFsmProbe)
      parent = ChoreoFsmTTwoPhase
      {:ok, src2} = Muro.emit_fsm("examples/two-phase-commit.muro", parent)
      compile!(src2)
      assert src =~ "choreography two-phase-commit: first coordinator chooses"

      monitor = Module.concat(parent, Muro.Emit.elixir_alias("two-phase-commit"))
      ca = Module.concat(parent, Ca)
      ab = Module.concat(parent, Ab)

      run = [
        {:coordinator, :alice, :prepare},
        {:coordinator, :bob, :prepare},
        {:alice, :coordinator, :vote},
        {:bob, :coordinator, :vote},
        {:coordinator, :commit},
        {:coordinator, :alice, :commit},
        {:coordinator, :bob, :commit}
      ]

      assert monitor.check_trace(run, complete: true) == :ok

      # Two messages that share no role still keep the written order.
      swapped = [{:coordinator, :bob, :prepare}, {:coordinator, :alice, :prepare}]
      assert {:error, {0, {:unexpected, _, _, _}}} = monitor.check_trace(swapped)

      assert ca.check_trace([{:send, :tt}, {:recv, :tt}, {:send, {:pick, :b0}}, {:send, :tt}],
               complete: true
             ) == :ok

      assert ab.done?(ab.init())
    end

    test "the outline names the monitor and its clauses" do
      {:ok, book} = Muro.Load.file("examples/release-plan.muro")
      book = Muro.Prelude.for_emit(book)
      assert {:ok, outline} = Muro.Emit.outline(:fsm, book, "examples/release-plan.muro")
      assert "Plan" in outline.names
      assert "def step(state, from, to, label, value)" in outline.clauses
      assert "def choose(state, role, label)" in outline.clauses
    end
  end

  describe "prefix of a choreography" do
    @book """
    choreography plan
      roles release, front, worker
      release -> front : deploy
      front -> release : deployed
      release -> worker : deploy Nat
      worker -> release : deployed
      release chooses
        keep: release -> front : done
              release -> worker : done
        undo: release -> front : undo
              release -> worker : undo
    """

    test "the empty list, a partial list, and the whole run are legal prefixes" do
      assert check(@book <> "\nprefix none : plan :=\n") == :ok

      assert check(
               @book <>
                 """

                 prefix front-first : plan :=
                   release -> front : deploy
                   front -> release : deployed
                 """
             ) == :ok

      assert check(
               @book <>
                 """

                 prefix whole : plan at start :=
                   release -> front : deploy
                   front -> release : deployed
                   release -> worker : deploy Nat
                   worker -> release : deployed
                   release chooses undo
                   release -> front : undo
                   release -> worker : undo
                 """
             ) == :ok
    end

    test "a choice prefix may stop after the label" do
      assert check(
               @book <>
                 """

                 prefix chosen : plan :=
                   release -> front : deploy
                   front -> release : deployed
                   release -> worker : deploy Nat
                   worker -> release : deployed
                   release chooses keep
                 """
             ) == :ok
    end

    test "an interaction out of the written order is refused" do
      assert check(
               @book <>
                 """

                 prefix early : plan :=
                   release -> front : deploy
                   release -> worker : deploy Nat
                 """
             ) ==
               {:error,
                "15:3: early: move 2 is not a legal continuation of plan at start: not enabled at start, expected front -> release : deployed, wrote release -> worker : deploy Nat"}

      assert check(
               @book <>
                 """

                 prefix first : plan :=
                   release -> worker : deploy Nat
                 """
             ) ==
               {:error,
                "14:3: first: not enabled at start, expected release -> front : deploy, wrote release -> worker : deploy Nat"}
    end

    test "a wrong label, a wrong payload, and an unknown role are refused" do
      assert {:error, msg} =
               check(@book <> "\nprefix label : plan :=\n  release -> front : ship\n")

      assert msg =~
               "label: not enabled at start, expected release -> front : deploy, wrote release -> front : ship"

      assert {:error, msg} =
               check(
                 @book <>
                   """

                   prefix pay : plan :=
                     release -> front : deploy
                     front -> release : deployed
                     release -> worker : deploy
                   """
               )

      assert msg =~ "move 3 is not a legal continuation of plan at start"
      assert msg =~ "expected release -> worker : deploy Nat, wrote release -> worker : deploy"

      assert check(@book <> "\nprefix who : plan :=\n  release -> zed : deploy\n") ==
               {:error, "14:3: who: unknown role zed"}
    end

    test "a wrong choice and a move past the end are refused" do
      run = """
        release -> front : deploy
        front -> release : deployed
        release -> worker : deploy Nat
        worker -> release : deployed
      """

      assert {:error, msg} =
               check(@book <> "\nprefix pick : plan :=\n" <> run <> "  release chooses maybe\n")

      assert msg =~ "move 5 is not a legal continuation of plan at start"
      assert msg =~ "expected release chooses keep or undo, wrote release chooses maybe"

      assert {:error, msg} =
               check(@book <> "\nprefix who : plan :=\n" <> run <> "  front chooses keep\n")

      assert msg =~ "expected release chooses keep or undo, wrote front chooses keep"

      past =
        run <>
          "  release chooses keep\n  release -> front : done\n  release -> worker : done\n  release -> front : deploy\n"

      assert {:error, msg} = check(@book <> "\nprefix past : plan :=\n" <> past)

      assert msg =~
               "move 8 is not a legal continuation of plan at start: not enabled at start, expected end, wrote release -> front : deploy"
    end

    test "a session move, a position, and a session use are refused" do
      assert {:error, msg} = check(@book <> "\nprefix sess : plan :=\n  send 1\n")
      assert msg =~ "sess: not enabled at start, expected release -> front : deploy, wrote send 1"

      assert check(@book <> "\nprefix mid : plan at 3 :=\n  release -> front : deploy\n") ==
               {:error, "13:1: mid: at 3 is not a position of plan"}

      session =
        "\nsession ab := send Nat end\n\nprefix mixed : ab :=\n  release -> front : deploy\n"

      assert {:error, msg} = check(@book <> session)
      assert msg =~ "mixed: ab is not a choreography"
    end

    test "the judgment is the written order" do
      g = {:comm, "a", "b", "x", :unit, {:comm, "c", "d", "y", :unit, :end}}
      assert Choreo.prefix(["a", "b", "c", "d"], g, [{:msg, "a", "b", "x", :unit}]) == :ok

      assert Choreo.prefix(["a", "b", "c", "d"], g, [{:msg, "c", "d", "y", :unit}]) ==
               {:error, 1, {:not_enabled, "a -> b : x", {:msg, "c", "d", "y", :unit}}}

      assert Choreo.advance(g, {:msg, "a", "b", "x", :unit}) ==
               {:ok, {:comm, "c", "d", "y", :unit, :end}}

      assert Choreo.expected_text(:end) == "end"
    end

    test "the example book's prefix checks" do
      assert File.read!("examples/release-plan.muro") =~ "prefix front-first : plan :="
      assert Muro.check_file("examples/release-plan.muro") == :ok
    end
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end

  defp emit_text!(name, text) do
    dir = Path.join(System.tmp_dir!(), "muro_choreo_fsm_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf(dir) end)
    path = Path.join(dir, name)
    File.write!(path, text)
    assert Muro.check_file(path) == :ok
    parent = Module.concat(["ChoreoFsmT#{System.unique_integer([:positive])}"])
    {:ok, src} = Muro.emit_fsm(path, parent, book: name)
    compile!(src)
    {parent, src}
  end

  defp compile!(src) do
    {mods, diags} = Code.with_diagnostics(fn -> Code.compile_string(src) end)
    warnings = Enum.filter(diags, &(&1.severity == :warning))
    assert warnings == [], inspect(warnings, limit: 30)
    mods
  end
end

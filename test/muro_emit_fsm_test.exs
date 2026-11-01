defmodule Muro.EmitFsmTest do
  use ExUnit.Case, async: false

  alias Muro.{Emit, Parser, Session}

  @moduletag timeout: 120_000

  @trace_books [
    "examples/meet.muro",
    "examples/indexed.muro",
    "examples/recursive.muro",
    "examples/computed.muro",
    "examples/field-bindings.muro",
    "examples/pair-bindings.muro",
    "examples/async-meetings.muro",
    "examples/session-calls.muro",
    "examples/value-protocols.muro",
    "examples/field-choice.muro"
  ]

  @required [
    "examples/meet.muro",
    "examples/indexed.muro",
    "examples/recursive.muro"
  ]

  @pool [-1, 1.5, "x", [], %{}, {}, {:nope}, :nope]
  @cut 12

  setup do
    on_exit(fn ->
      for {mod, _} <- :code.all_loaded(),
          name = Atom.to_string(mod),
          String.starts_with?(name, "Elixir.FsmT") or String.starts_with?(name, "Elixir.FsmRun") do
        :code.purge(mod)
        :code.delete(mod)
      end
    end)

    :ok
  end

  test "fsm_module is the stem plus Fsm" do
    assert Emit.fsm_module("examples/meet.muro") == MeetFsm
    assert Emit.fsm_module("examples/field-choice.muro") == FieldChoiceFsm
    assert Emit.fsm_module("examples/session-calls.muro") == SessionCallsFsm
  end

  test "meet, indexed, and recursive emit, compile, and stay pure" do
    for path <- @required do
      {parent, src} = emit!(path)
      assert src == emit_src(path, parent)
      assert_pure(src)
      mods = children(parent, load!(path))

      cond do
        path == "examples/meet.muro" ->
          assert mods["ping"] == Module.concat(parent, Ping)
          assert mods["back"] == Module.concat(parent, Back)
          assert mods["grant-end"] == Module.concat(parent, Emit.elixir_alias("grant-end"))
          assert byte_index(src, "defmodule Ping do") < byte_index(src, "defmodule Back do")

        path == "examples/indexed.muro" ->
          assert mods["route"] == Module.concat(parent, Route)
          assert mods["echo-bit"] == Module.concat(parent, Emit.elixir_alias("echo-bit"))

        true ->
          assert mods["loop"] == Module.concat(parent, Loop)
          assert mods["echo"] == Module.concat(parent, Echo)
      end
    end
  end

  test "the same book emits the same text from two directories" do
    {:ok, once} = Muro.emit_fsm("examples/meet.muro", MeetFsm)
    {:ok, twice} = Muro.emit_fsm("examples/meet.muro", MeetFsm)
    assert once == twice
    assert once =~ "examples/meet.muro:4 session ping: first recv Nat"
    refute once =~ File.cwd!()

    abs = Path.expand("examples/meet.muro")

    one =
      File.cd!(System.tmp_dir!(), fn ->
        {:ok, src} = Muro.emit_fsm(abs, MeetFsm)
        src
      end)

    other =
      File.cd!(Path.join(System.tmp_dir!(), ".."), fn ->
        {:ok, src} = Muro.emit_fsm(abs, MeetFsm)
        src
      end)

    assert one == other
    assert one =~ "meet.muro:4 session ping:"
    refute one =~ "/Users/"
    refute one =~ File.cwd!()
  end

  test "a book with no session is refused, and seen is refused" do
    assert Muro.emit_fsm("examples/pair.muro", PairFsm) ==
             {:error, "examples/pair.muro has no session to emit"}

    assert Muro.emit_fsm("examples/talk.muro", TalkFsm) ==
             {:error, "examples/talk.muro:6 session ping: seen is not a state machine"}

    assert Muro.emit_fsm("examples/seated.muro", SeatedFsm) ==
             {:error, "examples/seated.muro:35 session ping: seen is not a state machine"}
  end

  test "constructs the machine cannot represent are refused whole" do
    assert render_src("rec", "session bad := rec X. X\n") ==
             {:error, "rec.muro:1 session bad: unguarded rec"}

    assert render_src("self", "session loop := loop\n") ==
             {:error, "self.muro:1 session loop: unguarded session call"}

    assert render_src("later", "session a := b\nsession b := end\n") ==
             {:error, "later.muro:1 session a: session declared later"}

    assert render_src("arity", "session a := end\nsession b := a 1\n") ==
             {:error, "arity.muro:2 session b: wrong number of session arguments"}

    assert render_src("miss", "session a := dual missing\n") ==
             {:error, "miss.muro: session missing: unknown session missing"}

    assert render_src("boundvar", "session s := send (d : Nat) {d ≤ w} end\n") ==
             {:error, "boundvar.muro:1 session s: cannot evaluate bound w"}

    assert render_src("veclen", "session s := send (Vec Nat k) end\n") ==
             {:error, "veclen.muro:1 session s: cannot evaluate vector length k"}

    assert render_src("args", "session s (k : Nat) := end\nsession t := s mystery\n") ==
             {:error, "args.muro:2 session t: cannot evaluate argument mystery"}

    assert {:error, cycle} =
             render_src("cycle", "session a := dual b\nsession b := dual a\n")

    assert cycle =~ "dual cycle"

    natrun = """
    def id : run Π (n : Nat) → Nat :=
      λ (n : Nat) → n
    session s := recv (n : Nat) (case (id n) | true => end | false => end)
    """

    assert {:error, run_msg} = render_src("natrun", natrun)
    assert run_msg =~ "session s: cannot call run id"

    assert {:ok, _} = render_src("guarded", "session s := rec X. choose X end\n")

    book = [
      %{kind: :session, name: "s", params: [], proto: {:nope, 1}, loc: {1, 1}}
    ]

    assert Emit.Fsm.render(book, "ill.muro", IllFsm) ==
             {:error, "ill.muro:1 session s: ill-formed protocol"}
  end

  test "mix muro.emit --backend fsm prints the module and refuses node and imports" do
    {:ok, src} = Muro.emit_fsm("examples/meet.muro", MeetFsm)
    out = capture_emit(["examples/meet.muro", "--backend", "fsm"])
    assert String.trim_trailing(out) == String.trim_trailing(src)
    assert String.starts_with?(String.trim_leading(out), "defmodule MeetFsm do\n")

    assert_raise Mix.Error, ~r/--node writes the placement calls/, fn ->
      Mix.Tasks.Muro.Emit.run(["examples/meet.muro", "--backend", "fsm", "--node", "a"])
    end

    assert_raise Mix.Error, ~r/--imports is only valid with --backend exunit/, fn ->
      Mix.Tasks.Muro.Emit.run(["examples/meet.muro", "--backend", "fsm", "--imports"])
    end
  end

  test "ping and back walk send, recv, done, expected, and check_trace" do
    {parent, _} = emit!("examples/meet.muro")
    ping = child(parent, "ping")
    back = child(parent, "back")
    step1 = "examples/meet.muro:4 session ping: first recv Nat"
    step2 = "examples/meet.muro:4 session ping: first send Nat"
    ended = "examples/meet.muro:4 session ping: end"

    st = ping.init()
    assert ping.done?(st) == false
    assert ping.expected(st) == {:recv, :nat}
    assert {:error, {:unexpected, ^step1, {:recv, :nat}, -1}} = ping.recv(st, -1)
    assert {:error, {:unexpected, ^step1, {:recv, :nat}, :b0}} = ping.send(st, :b0)

    assert {:ok, st} = ping.recv(st, 0)
    assert ping.expected(st) == {:send, :nat}
    assert {:ok, st} = ping.send(st, 1)
    assert ping.done?(st)
    assert ping.expected(st) == :done
    assert {:error, {:unexpected, ^ended, :done, 0}} = ping.recv(st, 0)

    assert :ok = ping.check_trace([])
    assert :ok = ping.check_trace([{:recv, 0}])
    assert :ok = ping.check_trace([{:recv, 0}, {:send, 1}], complete: true)

    assert {:error, {1, {:incomplete, ^step2, {:send, :nat}}}} =
             ping.check_trace([{:recv, 0}], complete: true)

    assert {:error, {1, {:unexpected, ^step2, {:send, :nat}, :b0}}} =
             ping.check_trace([{:recv, 0}, {:recv, :b0}])

    assert {:error, {:unexpected, ^ended, :done, 1}} = ping.send(:nope, 1)
    assert ping.done?(:nope) == false
    assert ping.expected(:nope) == :done
    assert {:error, {:unexpected, ^ended, :done, 1}} = ping.send(back.init(), 1)
    assert_raise FunctionClauseError, fn -> ping.check_trace(:nope) end

    bst = back.init()
    assert back.expected(bst) == {:send, :nat}
    assert {:ok, bst} = back.send(bst, 1)
    assert back.expected(bst) == {:recv, :nat}
    assert {:ok, bst} = back.recv(bst, 1)
    assert back.done?(bst)
    assert :ok = back.check_trace([{:send, 1}, {:recv, 1}], complete: true)
  end

  test "ordinals name the source step in a branch, a loop, and after end" do
    {parent, _} =
      emit_text!("ord.muro", """
      session line := recv Nat (recv Nat (recv Nat end))
      session fork := recv (b : Bit) on (recv Nat end) (recv Nat (recv Nat end))
      session pick := choose (recv Nat end) (recv Nat (recv Nat end))
      session loop := rec X. recv Nat (send Nat X)
      """)

    line = child(parent, "line")
    fork = child(parent, "fork")
    pick = child(parent, "pick")
    loop = child(parent, "loop")
    file = "ord.muro"
    first_recv = file <> ":1 session line: first recv Nat"
    ended = file <> ":1 session line: end"

    assert line.expected(line.init()) == {:recv, :nat}

    assert {:error, {:unexpected, ^first_recv, _, _}} = line.send(line.init(), 0)

    {:ok, st} = line.recv(line.init(), 0)
    assert step_of(line, st) =~ "second recv Nat"
    {:ok, st} = line.recv(st, 0)
    assert step_of(line, st) =~ "third recv Nat"
    {:ok, st} = line.recv(st, 0)
    assert line.done?(st)
    assert {:error, {:unexpected, ^ended, :done, 0}} = line.send(st, 0)

    assert fork.expected(fork.init()) == {:recv, :bit}
    {:ok, b0} = fork.recv(fork.init(), :b0)
    assert step_of(fork, b0) =~ "second recv Nat"
    {:ok, b1} = fork.recv(fork.init(), :b1)
    assert step_of(fork, b1) =~ "third recv Nat"
    {:ok, b1} = fork.recv(b1, 0)
    assert step_of(fork, b1) =~ "4th recv Nat"

    assert pick.expected(pick.init()) == {:send_pick, [:b0, :b1]}
    {:ok, arm} = pick.send(pick.init(), {:pick, :b1})
    assert step_of(pick, arm) =~ "second recv Nat"
    {:ok, arm} = pick.recv(arm, 0)
    assert step_of(pick, arm) =~ "third recv Nat"

    assert {:error, {:unexpected, step, {:send_pick, [:b0, :b1]}, :b0}} =
             pick.send(pick.init(), :b0)

    assert step =~ "first choose"

    st = loop.init()
    assert loop.done?(st) == false
    first = step_of(loop, st)
    assert first =~ "first recv Nat"
    {:ok, st} = loop.recv(st, 1)
    assert step_of(loop, st) =~ "first send Nat"
    {:ok, st} = loop.send(st, 1)
    assert step_of(loop, st) == first
    {:ok, st} = loop.recv(st, 2)
    {:ok, st} = loop.send(st, 2)
    assert step_of(loop, st) == first
    assert loop.done?(st) == false
    assert :ok = loop.check_trace([{:recv, 1}, {:send, 1}, {:recv, 2}])

    assert {:error, {4, {:incomplete, ^first, {:recv, :nat}}}} =
             loop.check_trace([{:recv, 1}, {:send, 1}, {:recv, 2}, {:send, 2}], complete: true)
  end

  test "payloads, evidence, indices, cases, runs, and parameters" do
    {meet, _} = emit!("examples/meet.muro")
    box = child(meet, "box")
    sized = child(meet, "sized")
    window = child(meet, "window")
    grant = child(meet, "grant-end")
    choice = child(meet, "choice")
    offered = child(meet, "offered")

    assert box.expected(box.init()) ==
             {:send, {:pair, :bit, {:record, [{"x", :nat}, {"y", :nat}]}}}

    assert {:ok, st} = box.send(box.init(), {:b0, %{"x" => 0, "y" => 0}})
    assert box.done?(st)

    assert {:error, {:unexpected, _, {:send, {:pair, :bit, {:record, _}}}, %{}}} =
             box.send(box.init(), %{})

    assert {:ok, st} = sized.recv(sized.init(), 2)
    assert sized.expected(st) == {:send, {:vec, :nat, 2}}
    assert step_of(sized, sized.init()) =~ "first recv (n : Nat)"
    assert step_of(sized, st) =~ "first send (Vec Nat n)"
    assert {:ok, st} = sized.send(st, [0, 0])
    assert sized.done?(st)

    assert {:error, {:unexpected, _, {:send, {:vec, :nat, 2}}, [0]}} =
             sized.send(sized.recv(sized.init(), 2) |> elem(1), [0])

    assert window.expected(window.init()) == {:recv, :nat}
    assert {:ok, st} = window.recv(window.init(), 8)
    assert window.expected(st) == {:send, {:nat_at_most, 8}}
    assert step_of(window, st) =~ "first send (d : Nat) {d ≤ w}"
    assert {:error, {:unexpected, _, {:send, {:nat_at_most, 8}}, 9}} = window.send(st, 9)
    assert {:ok, st} = window.send(st, 8)
    assert window.done?(st)

    assert {:ok, st} = grant.send(grant.init(), 8)
    assert grant.expected(st) == {:recv, {:nat_at_most, 8}}
    assert step_of(grant, st) =~ "session grant-end: first recv (d : Nat) {d ≤ w}"
    assert {:error, {:unexpected, _, {:recv, {:nat_at_most, 8}}, 9}} = grant.recv(st, 9)
    assert {:ok, _} = grant.recv(st, 0)

    assert choice.expected(choice.init()) == {:send_pick, [:b0, :b1]}
    assert {:ok, st} = choice.send(choice.init(), {:pick, :b0})
    assert choice.done?(st)
    assert {:ok, st} = choice.send(choice.init(), {:pick, :b1})
    assert choice.expected(st) == {:send, :nat}

    assert offered.expected(offered.init()) == {:recv_pick, [:b0, :b1]}
    assert {:ok, st} = offered.recv(offered.init(), {:pick, :b1})
    assert offered.expected(st) == {:recv, :nat}

    {indexed, _} = emit!("examples/indexed.muro")
    route = child(indexed, "route")
    assert route.expected(route.init()) == {:recv, :bit}
    assert {:ok, st} = route.recv(route.init(), :b0)
    assert route.expected(st) == {:send, :nat}
    assert {:ok, st} = route.recv(route.init(), :b1)
    assert route.expected(st) == {:recv, :nat}

    assert {:error, {:unexpected, _, {:recv, :bit}, {:pick, :b0}}} =
             route.recv(route.init(), {:pick, :b0})

    {calls, _} = emit!("examples/session-calls.muro")
    nums = child(calls, "nums")
    stream = child(calls, "stream")
    three = child(calls, "three")
    assert three.expected(three.init()) == {:send, {:vec, :nat, 3}}
    assert {:ok, _} = three.send(three.init(), [0, 0, 0])
    assert_raise UndefinedFunctionError, fn -> nums.init() end
    assert_raise ArgumentError, ~r/session nums: argument 1 is not a nat/, fn -> nums.init(-1) end
    assert nums.expected(nums.init(1)) == {:send, :nat}
    assert :ok = nums.check_trace([{:send, 4}], args: [1], complete: true)
    assert_raise UndefinedFunctionError, fn -> nums.check_trace([{:send, 4}]) end

    assert_raise ArgumentError, ~r/session nums: check_trace requires args/, fn ->
      nums.check_trace([{:send, 4}], complete: true)
    end

    assert_raise ArgumentError, ~r/session stream: argument 1 is not a nat/, fn ->
      stream.init(:b0)
    end

    st = stream.init(0)
    assert stream.expected(st) == {:send, {:nat_at_most, 0}}
    assert {:error, {:unexpected, _, {:send, {:nat_at_most, 0}}, 1}} = stream.send(st, 1)
    assert {:ok, st} = stream.send(st, 0)
    assert stream.expected(st) == {:send, {:nat_at_most, 1}}
    assert {:ok, st} = stream.send(st, 1)
    assert stream.expected(st) == {:send, {:nat_at_most, 2}}
    assert stream.done?(st) == false

    {data, _} = emit!("examples/value-protocols.muro")
    server = child(data, "server")
    assert server.expected(server.init()) == {:recv, {:data, "Frame", []}}
    assert {:ok, st} = server.recv(server.init(), :bytes)
    assert server.expected(st) == {:send, {:data, "Ctl", []}}
    assert {:ok, st} = server.send(st, :rst)
    assert server.done?(st)
    assert {:ok, st} = server.recv(server.init(), :headers)
    assert server.expected(st) == {:recv, {:data, "Body", []}}

    gate = child(data, "gate")
    assert {:ok, st} = gate.recv(gate.init(), :bytes)
    assert gate.expected(st) == {:send, {:data, "Ctl", []}}
    assert {:ok, st} = gate.recv(gate.init(), :headers)
    assert gate.expected(st) == {:send, {:data, "Goaway", []}}

    {fields, _} = emit!("examples/field-choice.muro")
    fgate = child(fields, "gate")
    assert {:ok, st} = fgate.recv(fgate.init(), {:just, true})
    assert fgate.expected(st) == {:send, {:data, "Ctl", []}}
    assert {:ok, st} = fgate.recv(fgate.init(), {:just, false})
    assert fgate.done?(st)
    assert {:ok, st} = fgate.recv(fgate.init(), :nothing)
    assert fgate.done?(st)

    {computed, _} = emit!("examples/computed.muro")
    flag = child(computed, "flag")
    assert {:ok, st} = flag.recv(flag.init(), true)
    assert flag.expected(st) == {:send_pick, [:b0, :b1]}
    assert {:ok, st} = flag.recv(flag.init(), false)
    assert flag.expected(st) == {:send_pick, [:b0, :b1]}

    {recursive, _} = emit!("examples/recursive.muro")
    loop = child(recursive, "loop")
    first = step_of(loop, loop.init())
    {:ok, st} = loop.recv(loop.init(), 1)
    {:ok, st} = loop.send(st, 1)
    assert step_of(loop, st) == first
    assert loop.done?(st) == false
  end

  test "a nat above the run cap is refused before a Peano term is built" do
    {parent, src} =
      emit_text!("cap.muro", """
      data Bool : Type where
        true : Bool
        false : Bool
      data Box : Type where
        box : Nat → Box
      def big : run Π (b : Box) → Bool :=
        λ (b : Box) → true
      session s := recv (b : Box) (case (big b) | true => end | false => end)
      """)

    assert_pure(src)
    sess = child(parent, "s")
    over = {:box, 100_001}

    assert {:error, {:unexpected, step, {:nat_at_most, 100_000}, ^over}} =
             sess.recv(sess.init(), over)

    assert step =~ "first recv (b : Box)"
    assert {:ok, st} = sess.recv(sess.init(), {:box, 3})
    assert sess.done?(st)
  end

  test "repr payloads are host values, and the same payload without repr stays on the wire" do
    body = """
    data Bool : Type where
      true : Bool
      false : Bool
    data Box : Type where
      box : Nat → Box
    """

    repr = """
    #{body}
    repr Nat := integer
    repr Bool := boolean
    repr Box := map { "n" => integer }
    session give := recv Box end
    session bits := recv Bool end
    session num := recv Nat end
    """

    {with_repr, src} = emit_text!("reprs.muro", repr)
    assert_pure(src)
    assert src =~ "muro_fsm_from_host"
    give = child(with_repr, "give")
    bits = child(with_repr, "bits")
    num = child(with_repr, "num")
    assert give.expected(give.init()) == {:recv, {:repr, {:data, "Box", []}, "Box"}}
    assert {:ok, st} = give.recv(give.init(), %{"n" => 3})
    assert give.done?(st)

    assert {:error, {:unexpected, _, {:recv, {:repr, {:data, "Box", []}, "Box"}}, %{"n" => -1}}} =
             give.recv(give.init(), %{"n" => -1})

    assert {:error, {:unexpected, _, {:recv, {:repr, {:data, "Box", []}, "Box"}}, {:box, 3}}} =
             give.recv(give.init(), {:box, 3})

    assert {:ok, _} = bits.recv(bits.init(), true)
    assert bits.expected(bits.init()) == {:recv, {:repr, {:data, "Bool", []}, "Bool"}}
    assert {:ok, _} = num.recv(num.init(), 4)
    assert num.expected(num.init()) == {:recv, {:repr, :nat, "Nat"}}

    {plain, plain_src} =
      emit_text!(
        "plain.muro",
        body <>
          """
          session give := recv Box end
          """
      )

    assert_pure(plain_src)
    give = child(plain, "give")
    assert give.expected(give.init()) == {:recv, {:data, "Box", []}}
    assert {:ok, _} = give.recv(give.init(), {:box, 3})

    assert {:error, {:unexpected, _, {:recv, {:data, "Box", []}}, %{"n" => 3}}} =
             give.recv(give.init(), %{"n" => 3})
  end

  @tag timeout: 300_000
  @tag :traces
  test "meeting traces are accepted and every single-step mutation agrees" do
    old = Process.flag(:trap_exit, true)

    try do
      {report, stats} =
        Enum.reduce(@trace_books, {[], empty_stats()}, fn path, {report, stats} ->
          {rows, stats} = trace_book(path, stats)
          {report ++ rows, stats}
        end)

      File.write!(
        "/tmp/fsm_report.txt",
        inspect(%{report: report, stats: stats}, limit: :infinity)
      )

      for path <- @required do
        assert Enum.any?(report, fn row -> row.path == path and row.status != :skip end),
               "no trace for #{path}: #{inspect(report)}"

        assert Enum.all?(report, fn
                 %{path: ^path, oracle: :conforms} -> true
                 %{path: ^path, status: :skip} -> false
                 %{path: ^path} -> false
                 _ -> true
               end),
               "a required trace left the conformance oracle: #{inspect(report)}"
      end

      message = stats_message(stats)
      assert stats.traces > 0, message
      assert stats.mutants > 0, message
      assert stats.legal > 0, message

      for kind <- [:drop, :swap, :flip, :retype, :near, :dup, :append, :relabel] do
        bucket = Map.fetch!(stats.kinds, kind)
        if bucket.total > 0, do: assert(bucket.refused > 0, message)
      end
    after
      Process.flag(:trap_exit, old)
      flush_msgs()
    end
  end

  defp emit!(path) do
    parent = parent_mod()
    {:ok, src} = Muro.emit_fsm(path, parent)
    compile_fsm!(src)
    {parent, src}
  end

  defp emit_src(path, parent) do
    {:ok, src} = Muro.emit_fsm(path, parent)
    src
  end

  defp emit_text!(name, text) do
    dir = Path.join(System.tmp_dir!(), "muro_fsm_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf(dir) end)
    path = Path.join(dir, name)
    File.write!(path, text)
    parent = parent_mod()
    {:ok, src} = Muro.emit_fsm(path, parent, book: name)
    compile_fsm!(src)
    {parent, src}
  end

  defp parent_mod, do: Module.concat(["FsmT#{System.unique_integer([:positive])}"])

  defp compile_fsm!(src) do
    {mods, diags} = Code.with_diagnostics(fn -> Code.compile_string(src) end)
    warnings = Enum.filter(diags, &warning?/1)
    assert warnings == [], inspect(warnings, limit: 30)
    mods
  end

  defp warning?(%{severity: :warning}), do: true
  defp warning?({:warning, _}), do: true
  defp warning?(_), do: false

  defp assert_pure(src) do
    for needle <- ["GenServer", "spawn", "Process.", "receive", "send(", "Muro."] do
      refute src =~ needle, needle
    end

    assert src =~ "unquote(:send)"
  end

  defp load!(path) do
    {:ok, book} = Muro.Load.file(path)
    Muro.Prelude.for_emit(book)
  end

  defp children(parent, book) do
    names =
      book
      |> Enum.filter(&(Map.get(&1, :kind) == :session))
      |> Enum.map(& &1.name)

    names
    |> Muro.Emit.elixir_modules()
    |> Map.new(fn {name, camel} -> {name, Module.concat(parent, camel)} end)
  end

  defp child(parent, name), do: Module.concat(parent, Muro.Emit.elixir_alias(name))

  defp byte_index(src, needle) do
    {pos, _} = :binary.match(src, needle)
    pos
  end

  defp step_of(mod, state) do
    assert {:error, {:unexpected, step, _, _}} = mod.send(state, make_ref())
    step
  end

  defp render_src(name, src) do
    assert {:ok, book} = Parser.parse(src)
    Emit.Fsm.render(book, name <> ".muro", FsmProbe)
  end

  defp capture_emit(args) do
    ExUnit.CaptureIO.capture_io(fn -> Mix.Tasks.Muro.Emit.run(args) end)
    |> String.replace(~r/^==> \S+\n/m, "")
  end

  defp trace_book(path, stats) do
    book = load!(path)

    case Muro.emit_fsm(path, parent_mod()) do
      {:error, reason} ->
        {[%{path: path, meet: nil, status: :skip, why: reason, oracle: nil}], stats}

      {:ok, src} ->
        parent = module_of(src)
        compile_fsm!(src)
        mods = children(parent, book)
        stem = "FsmRun#{System.unique_integer([:positive])}"
        {:ok, otp} = Emit.Otp.render(book, stem)

        {otp_mod, _} =
          Enum.find(Code.compile_string(otp), fn {mod, _} ->
            Atom.to_string(mod) |> String.ends_with?("Otp")
          end)

        meets = Enum.filter(book, &(Map.get(&1, :kind) == :meet))

        Enum.reduce(meets, {[], stats}, fn meet, {rows, stats} ->
          case trace_meet(book, mods, otp_mod, meet) do
            {:skip, why} ->
              {rows ++ [%{path: path, meet: meet.name, status: :skip, why: why, oracle: nil}],
               stats}

            {:ok, ends, status} ->
              {stats, oracle} = check_ends(path, meet.name, ends, status, stats)
              row = %{path: path, meet: meet.name, status: status, why: nil, oracle: oracle}
              {rows ++ [row], stats}
          end
        end)
    end
  end

  defp module_of(src) do
    [_, name] = Regex.run(~r/defmodule ([A-Za-z0-9_.]+) do/, src)
    Module.concat([name])
  end

  defp trace_meet(book, mods, otp_mod, meet) do
    with {:ok, left} <- endpoint(book, mods, meet.left),
         {:ok, right} <- endpoint(book, mods, meet.right) do
      run_pair(otp_mod, left, right)
    else
      :skip -> {:skip, "not a conform"}
    end
  end

  defp endpoint(book, mods, proc_name) do
    case Enum.find(book, &(Map.get(&1, :kind) == :conform and &1.name == proc_name)) do
      nil ->
        :skip

      %{session: session, proc: proc} ->
        {name, args} = session_args(book, session)
        proto = opened_proto(book, name, args)
        env = param_env(book, name, args)

        %{
          mod: Map.fetch!(mods, name),
          args: nat_args(book, args),
          proto: proto,
          env: env,
          book: book,
          skel: Session.carry(proc, book),
          session: name
        }
        |> then(&{:ok, &1})
    end
  end

  defp session_args(_book, name) when is_binary(name), do: {name, []}
  defp session_args(_book, {:sess, name, args}), do: {name, args}

  defp nat_args(book, args), do: Enum.map(args, &nat_of(&1, book))

  defp nat_of({:lit, n}, _book) when is_integer(n), do: n
  defp nat_of({:suc, inner}, book), do: nat_of(inner, book) + 1

  defp nat_of({:var, name}, book) do
    case Session.eval_run(Atom.to_string(name), [], book) do
      n when is_integer(n) and n >= 0 -> n
      other -> raise "session argument #{name} is #{inspect(other)}"
    end
  end

  defp nat_of({:con, name, args}, book) do
    vals = Enum.map(args, &nat_of(&1, book))

    case Session.eval_run(name, vals, book) do
      n when is_integer(n) and n >= 0 -> n
      other -> raise "session argument #{name} is #{inspect(other)}"
    end
  end

  defp param_env(book, name, args) do
    sess = session_decl(book, name)
    Map.new(Enum.zip(Map.get(sess, :params, []), nat_args(book, args)))
  end

  defp opened_proto(book, name, []) do
    sess = session_decl(book, name)
    {:ok, proto} = Session.elaborate(sess, book)
    proto
  end

  defp opened_proto(book, name, args) do
    {:ok, sess} = Session.open_applied(book, name, args)
    sess.proto
  end

  defp session_decl(book, name) do
    Enum.find(book, &(Map.get(&1, :kind) == :session and &1.name == name))
  end

  # The live meeting records each end's sends. A GenServer mailbox queues a
  # payload before that process performs the receive, so the :receive trace
  # is not the protocol order. Replaying each skeleton against the other's
  # sends, and delivering the next payload only once the process is waiting,
  # is the order that process performs.
  defp run_pair(otp_mod, left, right) do
    case exchange(otp_mod, left, right) do
      {:skip, _} = skip ->
        skip

      {:ok, lsends, rsends, status} ->
        ltrace = replay(otp_mod, left, rsends)
        rtrace = replay(otp_mod, right, lsends)

        if status == :done do
          assert sends_of(ltrace) == lsends, "left sends diverged"
          assert sends_of(rtrace) == rsends, "right sends diverged"
        end

        {:ok, [{left, ltrace}, {right, rtrace}], status}
    end
  end

  defp sends_of(trace) do
    for {:send, value} <- trace, do: {:send, value}
  end

  defp exchange(otp_mod, left, right) do
    {:ok, lpid} = GenServer.start(otp_mod, {left.skel, :open})
    {:ok, rpid} = GenServer.start(otp_mod, {right.skel, :open})
    _ = Process.monitor(lpid)
    _ = Process.monitor(rpid)

    try do
      :ok = GenServer.call(lpid, {:muro_peer, rpid})
      :ok = GenServer.call(rpid, {:muro_peer, lpid})
      :erlang.trace(lpid, true, [:send, {:tracer, self()}])
      :erlang.trace(rpid, true, [:send, {:tracer, self()}])
      send(lpid, :muro_go)
      send(rpid, :muro_go)
      {lt, rt, status, reasons} = collect(lpid, rpid, [], [], nil, nil)

      cond do
        status == :quiet and lt == [] and rt == [] ->
          {:skip, "no messages"}

        status == :crash ->
          {:skip, "otp stopped #{inspect(reasons)}"}

        true ->
          {:ok, lt, rt, finish_status(status, reasons)}
      end
    after
      for pid <- [lpid, rpid], Process.alive?(pid), do: Process.exit(pid, :kill)
      flush_msgs()
    end
  end

  defp replay(otp_mod, info, incoming) do
    {:ok, pid} = GenServer.start(otp_mod, {info.skel, :open})
    _ = Process.monitor(pid)

    try do
      :ok = GenServer.call(pid, {:muro_peer, self()})
      :erlang.trace(pid, true, [:send, {:tracer, self()}])
      send(pid, :muro_go)
      {trace, _reason} = replay_loop(pid, incoming, [])
      trace
    after
      if Process.alive?(pid), do: Process.exit(pid, :kill)
      flush_msgs()
    end
  end

  defp replay_loop(pid, incoming, trace) do
    cond do
      length(trace) >= @cut ->
        {trace, :cut}

      true ->
        receive do
          {:trace, ^pid, :send, msg, _to} ->
            replay_loop(pid, incoming, note(:send, msg, trace))

          {:muro, ^pid, _} ->
            replay_loop(pid, incoming, trace)

          {:muro_pick, ^pid, _} ->
            replay_loop(pid, incoming, trace)

          {:DOWN, _, :process, ^pid, reason} ->
            {trace, reason}

          {:EXIT, ^pid, reason} ->
            {trace, reason}
        after
          30 ->
            cond do
              not Process.alive?(pid) ->
                {trace, :dead}

              parked?(pid) and incoming != [] ->
                {value, rest} = List.pop_at(incoming, 0)
                deliver(pid, value)
                replay_loop(pid, rest, trace ++ [{:recv, elem(value, 1)}])

              true ->
                {trace, :waiting}
            end
        end
    end
  end

  defp parked?(pid) do
    case Process.info(pid, [:status, :message_queue_len]) do
      [status: status, message_queue_len: 0] when status in [:waiting, :suspended] -> true
      _ -> false
    end
  end

  defp deliver(pid, {:send, {:pick, bit}}), do: send(pid, {:muro_pick, self(), bit})
  defp deliver(pid, {:send, value}), do: send(pid, {:muro, self(), value})

  defp finish_status(:done, [:normal, :normal]), do: :done

  defp finish_status(:done, reasons) do
    if Enum.all?(reasons, &(&1 == {:shutdown, :abandon})), do: :stop, else: :cut
  end

  defp finish_status(_status, _reasons), do: :cut

  defp collect(lpid, rpid, lt, rt, lr, rr) do
    cond do
      length(lt) >= @cut or length(rt) >= @cut ->
        {lt, rt, :cut, [lr, rr]}

      lr != nil and rr != nil ->
        {lt, rt, :done, [lr, rr]}

      true ->
        receive do
          {:trace, ^lpid, kind, msg, _to} ->
            collect(lpid, rpid, note(kind, msg, lt), rt, lr, rr)

          {:trace, ^lpid, kind, msg} ->
            collect(lpid, rpid, note(kind, msg, lt), rt, lr, rr)

          {:trace, ^rpid, kind, msg, _to} ->
            collect(lpid, rpid, lt, note(kind, msg, rt), lr, rr)

          {:trace, ^rpid, kind, msg} ->
            collect(lpid, rpid, lt, note(kind, msg, rt), lr, rr)

          {:DOWN, _, :process, ^lpid, reason} ->
            collect(lpid, rpid, lt, rt, reason, rr)

          {:DOWN, _, :process, ^rpid, reason} ->
            collect(lpid, rpid, lt, rt, lr, reason)

          {:EXIT, pid, reason} when pid in [lpid, rpid] ->
            {lr, rr} = if pid == lpid, do: {reason, rr}, else: {lr, reason}
            collect(lpid, rpid, lt, rt, lr, rr)
        after
          500 ->
            {lt, rt, :quiet, [lr, rr]}
        end
    end
  end

  defp note(:send, {:muro, _, value}, acc), do: acc ++ [{:send, value}]
  defp note(:send, {:muro_pick, _, bit}, acc), do: acc ++ [{:send, {:pick, bit}}]
  defp note(:receive, {:muro, _, value}, acc), do: acc ++ [{:recv, value}]
  defp note(:receive, {:muro_pick, _, bit}, acc), do: acc ++ [{:recv, {:pick, bit}}]
  defp note(_, _, acc), do: acc

  defp check_ends(path, meet, ends, status, stats) do
    Enum.reduce(ends, {stats, :conforms}, fn {info, trace}, {stats, oracle} ->
      assert_trace(info, trace, status)
      {mode, verdict} = classify_original(trace, info)

      if path in @required do
        assert mode == :both and verdict == :ok,
               "#{path} #{meet} #{info.session} used #{mode} #{inspect(verdict)}"
      end

      stats = Map.update!(stats, :traces, &(&1 + 1))

      stats =
        if mode == :walker, do: Map.update!(stats, :walker_traces, &(&1 + 1)), else: stats

      stats = mutate_all(info, trace, stats, mode)
      {stats, if(mode == :walker, do: :walker, else: oracle)}
    end)
  end

  defp assert_trace(info, trace, status) do
    st = start_state(info)

    walked =
      Enum.reduce(trace, st, fn {dir, value}, st ->
        assert {:ok, st} = apply(info.mod, dir, [st, value])
        st
      end)

    assert check(info, trace, false) == :ok

    if status == :done do
      assert apply(info.mod, :done?, [walked])
      assert apply(info.mod, :expected, [walked]) == :done
      assert check(info, trace, true) == :ok
    end
  end

  defp start_state(%{mod: mod, args: []}), do: mod.init()
  defp start_state(%{mod: mod, args: args}), do: apply(mod, :init, args)

  defp check(%{mod: mod, args: []}, trace, false), do: mod.check_trace(trace)
  defp check(%{mod: mod, args: []}, trace, true), do: mod.check_trace(trace, complete: true)

  defp check(%{mod: mod, args: args}, trace, complete?) do
    opts = if complete?, do: [args: args, complete: true], else: [args: args]
    mod.check_trace(trace, opts)
  end

  # A nested field split has no flat process term. When the original trace
  # is legal for the walker and the conformance builder cannot say the same,
  # every mutant of that trace is judged by the walker.
  defp classify_original(trace, info) do
    walked = walk(trace, initial(info))

    cond do
      alien_trace?(trace) ->
        {:walker, walked}

      true ->
        case conform_index(trace, info.proto, info.env, info.book) do
          :unencoded -> {:walker, walked}
          ^walked -> {:both, walked}
          _other when walked == :ok -> {:walker, walked}
          other -> flunk(disagree(info, trace, walked, other))
        end
    end
  end

  defp judge(trace, info, :walker), do: {:walker, walk(trace, initial(info))}

  defp judge(trace, info, :strict) do
    walked = walk(trace, initial(info))

    cond do
      alien_trace?(trace) ->
        {:walker, walked}

      true ->
        case conform_index(trace, info.proto, info.env, info.book) do
          :unencoded -> {:walker, walked}
          ^walked -> {:both, walked}
          other -> flunk(disagree(info, trace, walked, other))
        end
    end
  end

  defp disagree(info, trace, walked, other) do
    """
    oracle disagreement on #{info.session}
    walker #{inspect(walked)} conforms #{inspect(other)}
    trace #{inspect(trace, limit: 40)}
    """
  end

  defp mutate_all(info, trace, stats, mode) do
    pid = self()
    ref = make_ref()
    pool = @pool ++ [ref, pid]
    how = if mode == :walker, do: :walker, else: :strict

    trace
    |> mutants(pool)
    |> Enum.reduce(stats, fn {kind, mutated}, stats ->
      {_mode, verdict} = judge(mutated, info, how)
      got = check(info, mutated, false)
      stats = bump_stat(stats, kind, verdict)
      assert_mutant(info, kind, mutated, verdict, got)
      stats
    end)
  end

  defp assert_mutant(info, kind, trace, verdict, got) do
    case {verdict, got} do
      {:ok, :ok} ->
        :ok

      {{:fail, i}, {:error, {i, {:unexpected, step, _, _}}}} when is_binary(step) ->
        assert step =~ "session ", "#{info.session} #{kind} #{step}"

      other ->
        flunk("""
        #{info.session} #{kind}
        oracle #{inspect(verdict)} fsm #{inspect(got)} pair #{inspect(other)}
        trace #{inspect(trace, limit: 30)}
        """)
    end
  end

  defp mutants(trace, pool) do
    n = length(trace)

    drops =
      for i <- step_range(n) do
        {:drop, List.delete_at(trace, i)}
      end

    swaps =
      for i <- pair_range(n) do
        {:swap, swap_at(trace, i)}
      end

    flips =
      for i <- step_range(n) do
        {:flip, List.update_at(trace, i, &flip_dir/1)}
      end

    retypes =
      for i <- step_range(n), alien <- pool do
        {:retype, replace_value(trace, i, alien)}
      end

    nears =
      for i <- step_range(n), near <- neighbours(elem(Enum.at(trace, i), 1)) do
        {:near, replace_value(trace, i, near)}
      end

    dups =
      for i <- step_range(n) do
        {:dup, dup_at(trace, i)}
      end

    appended =
      for extra <- [{:send, -1}, {:recv, :nope}, {:send, {:pick, :b0}}] do
        {:append, trace ++ [extra]}
      end

    relabels =
      for i <- step_range(n),
          {dir, {:pick, bit}} <- [Enum.at(trace, i)],
          bit in [:b0, :b1] do
        {:relabel, List.replace_at(trace, i, {dir, {:pick, other_bit(bit)}})}
      end

    drops ++ swaps ++ flips ++ retypes ++ nears ++ dups ++ appended ++ relabels
  end

  defp step_range(n) when n > 0, do: 0..(n - 1)//1
  defp step_range(_n), do: []

  defp pair_range(n) when n > 1, do: 0..(n - 2)//1
  defp pair_range(_n), do: []

  defp swap_at(trace, i) do
    a = Enum.at(trace, i)
    b = Enum.at(trace, i + 1)
    trace |> List.replace_at(i, b) |> List.replace_at(i + 1, a)
  end

  defp flip_dir({:send, v}), do: {:recv, v}
  defp flip_dir({:recv, v}), do: {:send, v}

  defp replace_value(trace, i, value) do
    {dir, _} = Enum.at(trace, i)
    List.replace_at(trace, i, {dir, value})
  end

  defp dup_at(trace, i) do
    {head, tail} = Enum.split(trace, i + 1)
    head ++ [Enum.at(trace, i) | tail]
  end

  defp neighbours(n) when is_integer(n) and n >= 0, do: [n + 1]
  defp neighbours(:b0), do: [:b1]
  defp neighbours(:b1), do: [:b0]
  defp neighbours({:pick, bit}) when bit in [:b0, :b1], do: []
  defp neighbours(value), do: other_ctors(value)

  defp other_bit(:b0), do: :b1
  defp other_bit(:b1), do: :b0

  defp other_ctors(value) when is_atom(value) do
    case Atom.to_string(value) do
      "true" -> [false]
      "false" -> [true]
      "bytes" -> [:trailers]
      "trailers" -> [:bytes]
      "headers" -> [:bytes]
      "nothing" -> [{:just, true}]
      "rst" -> [:goaway]
      "goaway" -> [:rst]
      "chunk" -> []
      _ -> []
    end
  end

  defp other_ctors({:just, true}), do: [:nothing]
  defp other_ctors({:just, false}), do: [:nothing]
  defp other_ctors(_), do: []

  defp alien_trace?(trace) do
    Enum.any?(trace, fn
      {_dir, value} -> alien?(value)
      _ -> false
    end)
  end

  defp alien?(value) do
    cond do
      is_integer(value) and value < 0 -> true
      is_float(value) -> true
      is_binary(value) -> true
      is_reference(value) -> true
      is_pid(value) -> true
      value == {} -> true
      value == {:nope} -> true
      value == :nope -> true
      true -> false
    end
  end

  defp empty_stats do
    kinds =
      Map.new([:drop, :swap, :flip, :retype, :near, :dup, :append, :relabel], fn kind ->
        {kind, %{total: 0, refused: 0, legal: 0}}
      end)

    %{traces: 0, walker_traces: 0, mutants: 0, legal: 0, refused: 0, kinds: kinds}
  end

  defp bump_stat(stats, kind, verdict) do
    legal? = verdict == :ok
    stats = Map.update!(stats, :mutants, &(&1 + 1))

    stats =
      if legal?,
        do: Map.update!(stats, :legal, &(&1 + 1)),
        else: Map.update!(stats, :refused, &(&1 + 1))

    Map.update!(stats, :kinds, fn kinds ->
      Map.update!(kinds, kind, fn bucket ->
        bucket
        |> Map.update!(:total, &(&1 + 1))
        |> Map.update!(if(legal?, do: :legal, else: :refused), &(&1 + 1))
      end)
    end)
  end

  defp stats_message(stats) do
    kinds =
      Enum.map_join(stats.kinds, " ", fn {kind, bucket} ->
        "#{kind} refused=#{bucket.refused} legal=#{bucket.legal}"
      end)

    "traces=#{stats.traces} walker=#{stats.walker_traces} mutants=#{stats.mutants} legal=#{stats.legal} refused=#{stats.refused} #{kinds}"
  end

  defp flush_msgs do
    receive do
      _ -> flush_msgs()
    after
      0 -> :ok
    end
  end

  # The walker is a reference model of the elaborated protocol. It is not
  # the emitted machine. `conforms/3` is asked as well. A value the process
  # language cannot write (a foreign term, a vector that is not `rep`, a
  # nat strictly between 0 and a variable evidence bound) is `:unencoded`,
  # and the walker decides that mutant.

  defp initial(info) do
    %{
      p: info.proto,
      e: info.env,
      r: %{},
      idx: %{},
      book: info.book,
      decls: Session.payload_decls(info.book),
      fresh: 0
    }
  end

  defp walk(trace, st), do: walk1(trace, expose(st, []), 0)
  defp walk1([], _st, _i), do: :ok

  defp walk1([{:send, value} | rest], st, i), do: walked(:send, value, rest, st, i)
  defp walk1([{:recv, value} | rest], st, i), do: walked(:recv, value, rest, st, i)
  defp walk1([_ | _], _st, i), do: {:fail, i}

  defp walked(dir, value, rest, st, i) do
    case take(dir, value, st) do
      {:ok, st} -> walk1(rest, expose(st, []), i + 1)
      :error -> {:fail, i}
    end
  end

  defp take(dir, value, %{p: proto} = st) do
    case {dir, proto} do
      {:send, {:send, ty, cont}} -> payload(st, ty, cont, value, nil)
      {:recv, {:recv, ty, cont}} -> payload(st, ty, cont, value, nil)
      {:send, {:dsend, name, ty, cont}} -> payload(st, ty, cont, value, name)
      {:recv, {:drecv, name, ty, cont}} -> payload(st, ty, cont, value, name)
      {:send, {:esend, name, bound, cont}} -> evidence(st, name, bound, cont, value)
      {:recv, {:erecv, name, bound, cont}} -> evidence(st, name, bound, cont, value)
      {:send, {:isend, name, left, right}} -> index(st, name, left, right, value)
      {:recv, {:irecv, name, left, right}} -> index(st, name, left, right, value)
      {:send, {:choose, left, right}} -> pick(st, left, right, value)
      {:recv, {:branch, left, right}} -> pick(st, left, right, value)
      _ -> :error
    end
  end

  defp payload(st, ty, cont, value, name) do
    if member?(ty, value, st) do
      st = if is_nil(name), do: st, else: %{st | e: Map.put(st.e, name, value)}
      continue(%{st | p: cont}, name, value, ty)
    else
      :error
    end
  end

  defp continue(st, name, value, ty) do
    case quiet(st, []) do
      %{p: {:case, scrut, arms}} = st2 -> arm(st2, name, value, ty, scrut, arms)
      st2 -> {:ok, st2}
    end
  end

  defp arm(st, name, value, ty, scrut, arms) do
    scrut_name =
      case scrut do
        {:name, n} -> n
        {:run, _, n} -> n
        _ -> nil
      end

    cond do
      scrut_name != name ->
        :error

      huge?(value) ->
        :error

      true ->
        case to_check(ty, value, st) do
          {:ok, checker} ->
            case Session.chosen_arm(scrut, checker, arms, st.book) do
              {:ok, proto} -> {:ok, %{st | p: proto}}
              _ -> :error
            end

          :error ->
            :error
        end
    end
  end

  defp evidence(st, name, bound, cont, value) do
    case ix(bound, st.e) do
      {:ok, max} when is_integer(value) and value >= 0 and value <= max ->
        {:ok, %{st | e: Map.put(st.e, name, value), p: cont}}

      _ ->
        :error
    end
  end

  defp index(st, name, left, _right, :b0), do: {:ok, %{st | e: Map.put(st.e, name, :b0), p: left}}

  defp index(st, name, _left, right, :b1),
    do: {:ok, %{st | e: Map.put(st.e, name, :b1), p: right}}

  defp index(_st, _name, _left, _right, _), do: :error

  defp pick(st, left, _right, {:pick, :b0}), do: {:ok, %{st | p: left}}
  defp pick(st, _left, right, {:pick, :b1}), do: {:ok, %{st | p: right}}
  defp pick(_st, _left, _right, _), do: :error

  defp huge?(value) when is_integer(value) and value > 10_000, do: true
  defp huge?({:pick, _}), do: false
  defp huge?(value) when is_tuple(value), do: value |> Tuple.to_list() |> Enum.any?(&huge?/1)
  defp huge?(value) when is_list(value), do: Enum.any?(value, &huge?/1)
  defp huge?(value) when is_map(value), do: Enum.any?(Map.values(value), &huge?/1)
  defp huge?(_), do: false

  defp expose(%{p: {:rec, name, body}} = st, seen) do
    expose(%{st | p: body, r: Map.put(st.r, name, body)}, seen)
  end

  defp expose(%{p: {:svar, name}} = st, seen) do
    mark = {:svar, name}

    cond do
      mark in seen ->
        %{st | p: :stuck}

      true ->
        case Map.get(st.r, name) do
          nil -> %{st | p: :stuck}
          body -> expose(%{st | p: body}, [mark | seen])
        end
    end
  end

  defp expose(%{p: {:sjump, target, args}} = st, seen) do
    mark = {:jump, target, args}

    cond do
      mark in seen ->
        %{st | p: :stuck}

      true ->
        case enter(target, args, st) do
          {:ok, proto, env} -> expose(%{st | p: proto, e: env, r: %{}, idx: %{}}, [mark | seen])
          :error -> %{st | p: :stuck}
        end
    end
  end

  defp expose(%{p: {:case, _, _}} = st, _seen), do: %{st | p: :stuck}
  defp expose(st, _seen), do: st

  defp quiet(%{p: {:rec, name, body}} = st, seen) do
    quiet(%{st | p: body, r: Map.put(st.r, name, body)}, seen)
  end

  defp quiet(%{p: {:svar, name}} = st, seen) do
    mark = {:svar, name}

    cond do
      mark in seen ->
        %{st | p: :stuck}

      true ->
        case Map.get(st.r, name) do
          nil -> %{st | p: :stuck}
          body -> quiet(%{st | p: body}, [mark | seen])
        end
    end
  end

  defp quiet(%{p: {:sjump, target, args}} = st, seen) do
    mark = {:jump, target, args}

    cond do
      mark in seen ->
        %{st | p: :stuck}

      true ->
        case enter(target, args, st) do
          {:ok, proto, env} -> quiet(%{st | p: proto, e: env, r: %{}, idx: %{}}, [mark | seen])
          :error -> %{st | p: :stuck}
        end
    end
  end

  defp quiet(st, _seen), do: st

  defp enter(name, args, st) when is_binary(name), do: open_named(name, args, st)

  defp enter({:dual, name}, args, st) when is_binary(name) do
    case open_named(name, args, st) do
      {:ok, proto, env} -> {:ok, Session.dual(proto), env}
      :error -> :error
    end
  end

  defp enter(_, _, _), do: :error

  defp open_named(name, args, st) do
    with {:ok, vals} <- ix_list(args, st.e),
         sess when not is_nil(sess) <- session_decl(st.book, name),
         lits = Enum.map(vals, &{:lit, &1}),
         {:ok, opened} <- Session.open_applied(st.book, name, lits) do
      params = Map.get(sess, :params, [])

      if length(params) == length(vals) do
        {:ok, opened.proto, Map.new(Enum.zip(params, vals))}
      else
        :error
      end
    else
      _ -> :error
    end
  end

  defp ix_list(args, env) do
    Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, acc} ->
      case ix(arg, env) do
        {:ok, n} -> {:cont, {:ok, acc ++ [n]}}
        :error -> {:halt, :error}
      end
    end)
  end

  defp ix({:lit, n}, _env) when is_integer(n) and n >= 0, do: {:ok, n}

  defp ix({:var, name}, env) do
    case Map.get(env, name) do
      n when is_integer(n) and n >= 0 -> {:ok, n}
      _ -> :error
    end
  end

  defp ix({:suc, inner}, env) do
    case ix(inner, env) do
      {:ok, n} -> {:ok, n + 1}
      :error -> :error
    end
  end

  defp ix(_, _), do: :error

  defp member?(ty, value, st) do
    member_ty?(subst_ty(ty, st.e), value, st)
  end

  defp member_ty?(:nat, n, _st), do: is_integer(n) and n >= 0
  defp member_ty?(:bit, bit, _st), do: bit in [:b0, :b1]
  defp member_ty?(:unit, :tt, _st), do: true
  defp member_ty?({:pair, a, b}, {x, y}, st), do: member_ty?(a, x, st) and member_ty?(b, y, st)

  defp member_ty?({:rec, fields}, map, st) when is_list(fields) and is_map(map) do
    names = Enum.map(fields, fn {name, _} -> name end)

    Enum.sort(Map.keys(map)) == Enum.sort(names) and
      Enum.all?(fields, fn {name, ty} -> member_ty?(ty, Map.get(map, name), st) end)
  end

  defp member_ty?({:vec, elem, {:lit, n}}, list, st)
       when is_list(list) and is_integer(n) and n >= 0 do
    length(list) == n and Enum.all?(list, &member_ty?(elem, &1, st))
  end

  defp member_ty?({:dat, name, args}, value, st) when is_list(args) do
    case Map.get(st.decls, name) do
      %{np: n, ctors: ctors} when length(args) == n -> dat_member?(ctors, name, args, value, st)
      _ -> false
    end
  end

  defp member_ty?(_, _, _), do: false

  defp dat_member?(ctors, _name, _args, value, _st) when is_atom(value) do
    Map.get(ctors, Atom.to_string(value)) == []
  end

  defp dat_member?(ctors, dname, args, value, st)
       when is_tuple(value) and tuple_size(value) >= 1 do
    [tag | fields] = Tuple.to_list(value)

    if is_atom(tag) do
      case Map.get(ctors, Atom.to_string(tag)) do
        tmpl when is_list(tmpl) and length(tmpl) == length(fields) ->
          Enum.zip(tmpl, fields)
          |> Enum.all?(fn {field, got} -> member_ty?(inst(field, dname, args), got, st) end)

        _ ->
          false
      end
    else
      false
    end
  end

  defp dat_member?(_, _, _, _, _), do: false

  defp inst({:par, i}, _name, args), do: Enum.at(args, i)
  defp inst({:pair, a, b}, name, args), do: {:pair, inst(a, name, args), inst(b, name, args)}
  defp inst({:self, ts}, name, args), do: {:dat, name, Enum.map(ts, &inst(&1, name, args))}
  defp inst({:dat, name, ts}, dname, args), do: {:dat, name, Enum.map(ts, &inst(&1, dname, args))}
  defp inst(ty, _name, _args), do: ty

  defp subst_ty(ty, _env) when ty in [:nat, :bit, :unit], do: ty
  defp subst_ty({:pair, a, b}, env), do: {:pair, subst_ty(a, env), subst_ty(b, env)}

  defp subst_ty({:rec, fields}, env) when is_list(fields) do
    {:rec, Enum.map(fields, fn {name, ty} -> {name, subst_ty(ty, env)} end)}
  end

  defp subst_ty({:vec, elem, e}, env), do: {:vec, subst_ty(elem, env), subst_ix(e, env)}
  defp subst_ty({:dat, name, args}, env), do: {:dat, name, Enum.map(args, &subst_ty(&1, env))}
  defp subst_ty(ty, _env), do: ty

  defp subst_ix({:lit, n}, _env), do: {:lit, n}

  defp subst_ix({:var, name}, env) do
    case Map.get(env, name) do
      n when is_integer(n) and n >= 0 -> {:lit, n}
      _ -> {:var, name}
    end
  end

  defp subst_ix({:suc, inner}, env) do
    case subst_ix(inner, env) do
      {:lit, n} -> {:lit, n + 1}
      other -> other
    end
  end

  defp subst_ix(e, _env), do: e

  defp to_check(ty, value, st), do: to_check(subst_ty(ty, st.e), value, st, :go)

  defp to_check(:nat, n, _st, _tag) when is_integer(n) and n >= 0, do: {:ok, {:nat, n}}
  defp to_check(:bit, bit, _st, _tag) when bit in [:b0, :b1], do: {:ok, bit}
  defp to_check(:unit, :tt, _st, _tag), do: {:ok, :tt}

  defp to_check({:pair, a, b}, {x, y}, st, _tag) do
    with {:ok, cx} <- to_check(a, x, st, :go),
         {:ok, cy} <- to_check(b, y, st, :go) do
      {:ok, {:tup, cx, cy}}
    end
  end

  defp to_check({:rec, fields}, map, st, _tag) when is_map(map) do
    Enum.reduce_while(fields, {:ok, []}, fn {name, ty}, {:ok, acc} ->
      case to_check(ty, Map.get(map, name), st, :go) do
        {:ok, val} -> {:cont, {:ok, acc ++ [{name, val}]}}
        :error -> {:halt, :error}
      end
    end)
    |> case do
      {:ok, vals} -> {:ok, {:rec, vals}}
      :error -> :error
    end
  end

  defp to_check({:vec, elem, {:lit, n}}, list, st, _tag)
       when is_list(list) and is_integer(n) and length(list) == n do
    case uniform(elem, list, st) do
      {:ok, one} -> {:ok, {:rep, {:nat, n}, one}}
      :error -> :error
    end
  end

  defp to_check({:vec, elem, {:var, name}}, list, st, _tag)
       when is_list(list) and is_atom(name) do
    case uniform(elem, list, st) do
      {:ok, one} -> {:ok, {:rep, {:var, name}, one}}
      :error -> :error
    end
  end

  defp to_check({:dat, name, args}, value, st, _tag) do
    to_con(name, args, value, st)
  end

  defp to_check(_, _, _, _), do: :error

  defp uniform(_elem, [], _st), do: :error

  defp uniform(elem, [head | tail], st) do
    with {:ok, one} <- to_check(elem, head, st, :go) do
      if Enum.all?(tail, &(to_check(elem, &1, st, :go) == {:ok, one})),
        do: {:ok, one},
        else: :error
    end
  end

  defp to_con(dname, _args, value, st) when is_atom(value) do
    case ctor_fields(st.decls, dname, Atom.to_string(value)) do
      {:ok, []} -> {:ok, {:con, Atom.to_string(value), []}}
      _ -> :error
    end
  end

  defp to_con(dname, args, value, st) when is_tuple(value) and tuple_size(value) >= 1 do
    [tag | fields] = Tuple.to_list(value)

    if is_atom(tag) do
      case ctor_fields(st.decls, dname, Atom.to_string(tag)) do
        {:ok, tmpl} when length(tmpl) == length(fields) ->
          conv =
            Enum.reduce_while(Enum.zip(tmpl, fields), {:ok, []}, fn {field, got}, {:ok, acc} ->
              case to_check(inst(field, dname, args), got, st, :go) do
                {:ok, val} -> {:cont, {:ok, acc ++ [val]}}
                :error -> {:halt, :error}
              end
            end)

          case conv do
            {:ok, args} -> {:ok, {:con, Atom.to_string(tag), args}}
            :error -> :error
          end

        _ ->
          :error
      end
    else
      :error
    end
  end

  defp to_con(_, _, _, _), do: :error

  defp ctor_fields(decls, dname, ctor) do
    case Map.get(decls, dname) do
      %{ctors: ctors} ->
        case Map.fetch(ctors, ctor) do
          {:ok, fields} -> {:ok, fields}
          :error -> :error
        end

      _ ->
        :error
    end
  end

  defp conform_index(trace, proto, env, book) do
    case conform_ok?(trace, proto, env, book) do
      :ok ->
        :ok

      :unencoded ->
        :unencoded

      :no ->
        Enum.reduce_while(0..(length(trace) - 1), :ok, fn i, _ ->
          case conform_ok?(Enum.take(trace, i + 1), proto, env, book) do
            :ok -> {:cont, :ok}
            :unencoded -> {:halt, :unencoded}
            :no -> {:halt, {:fail, i}}
          end
        end)
    end
  end

  defp conform_ok?(trace, proto, env, book) do
    st = %{
      p: proto,
      e: env,
      r: %{},
      idx: %{},
      book: book,
      decls: Session.payload_decls(book),
      fresh: 0
    }

    with {:ok, proc} <- build(trace, st),
         {:ok, mirror} <- build(flip(trace), %{st | p: Session.dual(proto)}) do
      if Session.conforms(proc, proto, book) == :ok and
           Session.conforms(mirror, Session.dual(proto), book) == :ok do
        :ok
      else
        :no
      end
    else
      :unencoded -> :unencoded
    end
  end

  defp flip(trace) do
    Enum.map(trace, fn
      {:send, value} -> {:recv, value}
      {:recv, value} -> {:send, value}
    end)
  end

  defp build(trace, st), do: build1(trace, expose(st, []))
  defp build1([], _st), do: {:ok, :stop}

  defp build1([{dir, value} | rest], st) do
    case place(dir, value, st) do
      {:cont, st2, wrap} ->
        case build1(rest, expose(st2, [])) do
          {:ok, cont} -> {:ok, wrap.(cont)}
          other -> other
        end

      {:stop, proc} ->
        {:ok, proc}

      :gap ->
        :unencoded
    end
  end

  defp place(dir, value, %{p: proto} = st) do
    case {dir, proto} do
      {:send, {:send, ty, cont}} -> place_payload(st, ty, cont, value, nil, :send)
      {:recv, {:recv, ty, cont}} -> place_payload(st, ty, cont, value, nil, :recv)
      {:send, {:dsend, name, ty, cont}} -> place_payload(st, ty, cont, value, name, :send)
      {:recv, {:drecv, name, ty, cont}} -> place_payload(st, ty, cont, value, name, :recv)
      {:send, {:esend, name, bound, cont}} -> place_evidence(st, name, bound, cont, value, :send)
      {:recv, {:erecv, name, bound, cont}} -> place_evidence(st, name, bound, cont, value, :recv)
      {:send, {:isend, name, left, right}} -> place_index(st, name, left, right, value, :send)
      {:recv, {:irecv, name, left, right}} -> place_index(st, name, left, right, value, :recv)
      {:send, {:choose, left, right}} -> place_pick(st, left, right, value, :send)
      {:recv, {:branch, left, right}} -> place_pick(st, left, right, value, :recv)
      _ -> {:stop, mismatch(dir)}
    end
  end

  # A send is a put and a recv is a get. The opposite encoding conforms
  # to the action the trace got wrong, so the checker would accept it.
  defp mismatch(:send), do: {:put, :nat, {:nat, 0}, :stop}
  defp mismatch(:recv), do: {:get, :nat, :v, :stop}

  defp place_payload(st, ty, cont, value, name, dir) do
    applied = apply_idx(ty, st.idx)

    cond do
      not member?(ty, value, st) ->
        {:stop, bad_node(dir, applied)}

      true ->
        case encode(applied, value, st) do
          :gap ->
            :gap

          {:ok, checker} ->
            {st, pname} = bind_idx(st, name, dir, applied, checker, value)
            st = %{st | p: cont}
            finish_payload(st, dir, applied, checker, pname, value)
        end
    end
  end

  defp finish_payload(st, dir, applied, checker, pname, value) do
    case quiet(st, []) do
      %{p: {:case, scrut, arms}} = st2 ->
        place_arm(st2, dir, applied, checker, pname, value, scrut, arms)

      st2 ->
        wrap =
          if dir == :send do
            fn cont -> {:put, applied, checker, cont} end
          else
            fn cont -> {:get, applied, pname, cont} end
          end

        {:cont, st2, wrap}
    end
  end

  defp place_arm(st, dir, applied, checker, pname, value, scrut, arms) do
    scrut_name =
      case scrut do
        {:name, n} -> n
        {:run, _, n} -> n
        _ -> nil
      end

    cond do
      scrut_name != pname or huge?(value) ->
        {:stop, bad_node(dir, applied)}

      true ->
        case Session.chosen_arm(scrut, checker, arms, st.book) do
          {:ok, proto} ->
            labels = arm_order(scrut, applied, arms, st)

            wrap = fn cont ->
              if dir == :send do
                {:put, applied, checker, cont}
              else
                {:get, applied, pname, {:match, pname, match_arms(labels, tag_of(checker), cont)}}
              end
            end

            {:cont, %{st | p: proto}, wrap}

          _ ->
            {:stop, bad_node(dir, applied)}
        end
    end
  end

  defp arm_order({:run, _, _}, ty, _arms, st), do: input_ctors(ty, st)
  defp arm_order(_, _ty, arms, _st), do: Enum.map(arms, fn {tag, _} -> tag end)

  defp input_ctors(:bit, _st), do: ["b0", "b1"]

  defp input_ctors({:dat, name, _}, st) do
    case Map.get(st.decls, name) do
      %{order: order} -> order
      _ -> []
    end
  end

  defp input_ctors(_, _), do: []

  defp match_arms(labels, tag, cont) do
    Enum.map(labels, fn label ->
      if label == tag, do: cont, else: :stop
    end)
  end

  defp tag_of(:b0), do: "b0"
  defp tag_of(:b1), do: "b1"
  defp tag_of({:con, name, _}), do: name
  defp tag_of(_), do: nil

  defp bind_idx(st, nil, _dir, _ty, _checker, _value), do: {st, fresh(st)}

  defp bind_idx(st, name, :recv, _ty, _checker, value) do
    st = %{st | e: Map.put(st.e, name, value), idx: rename_idx(st.idx, name)}
    {st, name}
  end

  defp bind_idx(st, name, :send, ty, checker, value) do
    st = %{st | e: Map.put(st.e, name, value), idx: ext_idx(st.idx, name, ty, checker)}
    {st, name}
  end

  defp fresh(_st), do: :v

  defp rename_idx(idx, name), do: Map.put(Map.delete(idx, name), name, {:var, name})

  defp ext_idx(idx, name, :nat, {:nat, n}), do: Map.put(idx, name, {:lit, n})
  defp ext_idx(idx, name, :nat, {:var, v}), do: Map.put(idx, name, {:var, v})
  defp ext_idx(idx, name, _ty, _checker), do: Map.delete(idx, name)

  defp place_evidence(st, name, bound, cont, value, dir) do
    case evidence_term(bound, value, st) do
      :gap ->
        :gap

      :bad ->
        {:stop, bad_node(dir, :nat)}

      {:ok, checker} ->
        wrap = fn next ->
          if dir == :send, do: {:put, :unknown, checker, next}, else: {:get, :nat, name, next}
        end

        st =
          if is_integer(value) do
            %{st | e: Map.put(st.e, name, value), p: cont}
          else
            %{st | p: cont}
          end

        {:cont, st, wrap}
    end
  end

  defp evidence_term(bound, value, st) do
    cond do
      not (is_integer(value) and value >= 0) ->
        :bad

      true ->
        case ix(bound, st.e) do
          {:ok, max} when value > max ->
            {:ok, {:nat, value}}

          {:ok, _max} ->
            case bound do
              {:lit, _} ->
                {:ok, {:nat, value}}

              {:var, bname} ->
                cond do
                  value == 0 -> {:ok, {:nat, 0}}
                  value == Map.get(st.e, bname) -> {:ok, {:var, bname}}
                  true -> :gap
                end

              _ ->
                :gap
            end

          :error ->
            :bad
        end
    end
  end

  defp place_index(st, name, left, right, bit, :send) when bit in [:b0, :b1] do
    cont = if bit == :b0, do: left, else: right
    wrap = fn next -> {:put, :bit, bit, next} end
    {:cont, %{st | e: Map.put(st.e, name, bit), p: cont}, wrap}
  end

  defp place_index(st, name, left, right, bit, :recv) when bit in [:b0, :b1] do
    cont = if bit == :b0, do: left, else: right

    wrap = fn next ->
      if bit == :b0, do: {:iget, name, next, :stop}, else: {:iget, name, :stop, next}
    end

    {:cont, %{st | e: Map.put(st.e, name, bit), p: cont}, wrap}
  end

  defp place_index(_st, _name, _left, _right, _value, dir), do: {:stop, mismatch(dir)}

  defp place_pick(st, left, right, {:pick, bit}, dir) when bit in [:b0, :b1] do
    cont = if bit == :b0, do: left, else: right

    wrap = fn next ->
      case {dir, bit} do
        {:send, :b0} -> {:pick0, next}
        {:send, :b1} -> {:pick1, next}
        {:recv, :b0} -> {:cover, next, :stop}
        {:recv, :b1} -> {:cover, :stop, next}
      end
    end

    {:cont, %{st | p: cont}, wrap}
  end

  defp place_pick(_st, _left, _right, _value, dir), do: {:stop, mismatch(dir)}

  defp bad_node(:send, :nat), do: {:put, :unit, :tt, :stop}
  defp bad_node(:send, _ty), do: {:put, :nat, {:nat, 0}, :stop}
  defp bad_node(:recv, :nat), do: {:get, :unit, :v, :stop}
  defp bad_node(:recv, _ty), do: {:get, :nat, :v, :stop}

  defp encode(ty, value, st) do
    case to_check(ty, value, %{st | e: %{}}) do
      {:ok, checker} -> {:ok, checker}
      :error -> :gap
    end
  end

  defp apply_idx(ty, _idx) when ty in [:nat, :bit, :unit, :unknown], do: ty
  defp apply_idx({:pair, a, b}, idx), do: {:pair, apply_idx(a, idx), apply_idx(b, idx)}

  defp apply_idx({:rec, fields}, idx) when is_list(fields) do
    {:rec, Enum.map(fields, fn {name, ty} -> {name, apply_idx(ty, idx)} end)}
  end

  defp apply_idx({:vec, elem, e}, idx), do: {:vec, apply_idx(elem, idx), apply_nexp(e, idx)}
  defp apply_idx({:dat, name, args}, idx), do: {:dat, name, Enum.map(args, &apply_idx(&1, idx))}
  defp apply_idx(ty, _idx), do: ty

  defp apply_nexp({:lit, n}, _idx), do: {:lit, n}

  defp apply_nexp({:var, name}, idx) do
    case Map.get(idx, name) do
      nil -> {:var, name}
      e -> e
    end
  end

  defp apply_nexp(e, _idx), do: e
end

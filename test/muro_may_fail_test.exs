defmodule Muro.MayFailTest do
  use ExUnit.Case, async: false

  alias Muro.{Ast, Check, Fail, Parser, Session, Temporal}
  alias Muro.Temporal.Graph

  @refuse "c:mayfail\nmay fail is checked and not emitted"

  @missing "examples/may-fail-missing.muro:15:1: miss: server: get (r : Report) does not handle failure of task"

  @held "examples/may-fail-hold.muro:20:1: held: (server at first get) leads_to (server done) fails in hold (server : server-wait, task : task-work) after task died, server fail; then forever: the meeting has finished"

  test "may fail prints on the party it marks, and buffer stays last" do
    assert {:ok, book} =
             Parser.parse("""
             meet wire : server with task may fail buffer 1
             meet left : server may fail with task
             meet both : server may fail with task may fail buffer 2
             meet plain : server with task
             meet down : server with down
             def may : run Π (n : Nat) → Nat := λ (n : Nat) → n
             def fail : run Nat := 0
             def use : run Nat := may fail
             """)

    meets = for %{kind: :meet} = meet <- book, do: Fail.show_meet(meet)

    assert meets == [
             "meet wire : server with task may fail buffer 1",
             "meet left : server may fail with task",
             "meet both : server may fail with task may fail buffer 2",
             "meet plain : server with task",
             "meet down : server with down"
           ]

    by_name = Map.new(book, fn d -> {d.name, d} end)
    assert by_name["may"].mode == :run
    assert by_name["fail"].mode == :run
    assert by_name["use"].mode == :run
    assert {:app, {:var, "may"}, {:var, "fail"}} = by_name["use"].body
  end

  test "fail is an arm only after a receive, and a bare fail stays a call" do
    assert show("""
           session s := recv Nat end
           conform server : s := get Nat fail
           """) == "get Nat fail"

    assert show("""
           session s := recv Nat end
           conform server : s := get Nat done fail done
           """) == "get Nat done fail done"

    assert show("""
           session s := recv Nat end
           conform server : s := get (r : Nat) done fail (e : Reason) done
           """) == "get (r : Nat) done fail (e : Reason) done"

    assert show("""
           session s := recv Nat (recv Nat end)
           conform server : s := get Nat (get Nat done fail done) fail done
           """) == "get Nat (get Nat done fail done) fail done"

    assert show("""
           session s := recv Nat end
           conform server : s := get Nat done fail (done)
           """) == "get Nat done fail done"

    assert show("""
           session s := end
           conform down : s := done
           """) == "done"
  end

  test "may fail outside a two-party meet is refused" do
    only = Fail.only_message()

    for src <- [
          "may fail\n",
          "session s := may fail end\n",
          "session s := end\nconform p : s := may fail done\n",
          "talk ping := may fail over\n",
          "choreography c\n  roles a, b\n  may fail\n",
          "seat home : may fail pong at home in talk\n",
          "link go : may fail cross a with b in talk\n",
          "endpoint home := may fail ping at local\n",
          "meet wire : server may with task\n",
          "meet wire : server with task may\n",
          """
          session ping := end
          def f : (s : ping) ⊸ ping := may fail
          """
        ] do
      assert {:error, msg} = Parser.parse(src)
      assert msg =~ only
    end
  end

  test "a missing failure arm is refused at the receive" do
    assert {:error, @missing} = Muro.check_file("examples/may-fail-missing.muro")
  end

  test "a failure arm that does not release the slot fails leads_to" do
    assert {:error, @held} = Muro.check_file("examples/may-fail-hold.muro")
  end

  test "a failure arm that releases the slot holds" do
    assert Muro.check_file("examples/may-fail-free.muro") == :ok

    assert Check.temporal_lines() == [
             "temporal freed: holds in 5 reachable states, 6 transitions"
           ]
  end

  test "a meeting that does not mark a party keeps the report path" do
    assert Muro.check_file("examples/may-fail-control.muro") == :ok

    assert Check.temporal_lines() == [
             "temporal released: holds in 3 reachable states, 3 transitions"
           ]
  end

  test "a send needs no failure arm" do
    assert Muro.check_file("examples/may-fail-send.muro") == :ok

    assert Check.temporal_lines() == [
             "temporal freed: holds in 12 reachable states, 16 transitions"
           ]
  end

  test "a failure arm on a party that may not fail is refused" do
    assert {:error, msg} =
             check("""
             data Report : Type where
               ok : Report
             session task-work := send Report end
             session server-wait := recv Report end
             conform task : task-work := put ok done
             conform server : server-wait :=
               get (r : Report) done
               fail
                 done
             meet wire : server with task buffer 1
             """)

    assert msg =~ "wire: server: get (r : Report) has a failure arm, and task may not fail"
  end

  test "both parties may fail, and each receive needs an arm" do
    assert check("""
           data Report : Type where
             ok : Report
           session left-s := send Report (recv Report end)
           session right-s := recv Report (send Report end)
           conform left : left-s := put ok (get (r : Report) done fail done)
           conform right : right-s := get (r : Report) (put ok done) fail done
           meet both : left may fail with right may fail buffer 1
           """) == :ok

    assert {:error, msg} =
             check("""
             data Report : Type where
               ok : Report
             session left-s := send Report (recv Report end)
             session right-s := recv Report (send Report end)
             conform left : left-s := put ok (get (r : Report) done)
             conform right : right-s := get (r : Report) (put ok done) fail done
             meet both : left may fail with right may fail buffer 1
             """)

    assert msg =~ "left: get (r : Report) does not handle failure of right"
  end

  test "a reason is a payload the book names" do
    assert check("""
           data Report : Type where
             ok : Report
           session task-work := send Report end
           session server-wait := recv Report end
           conform task : task-work := put ok done
           conform server : server-wait :=
             get (r : Report) done
             fail (e : Report)
               done
           meet wire : server with task may fail buffer 1
           """) == :ok

    assert {:error, msg} =
             check("""
             data Report : Type where
               ok : Report
             session task-work := send Report end
             session server-wait := recv Report end
             conform task : task-work := put ok done
             conform server : server-wait :=
               get (r : Report) done
               fail (e : Missing)
                 done
             meet wire : server with task may fail buffer 1
             """)

    assert msg =~ "unknown payload Missing"
  end

  test "session %1 refuses a failure arm that stops" do
    assert {:error, msg} =
             check("""
             data Report : Type where
               ok : Report
             session %1 server-wait := recv Report end
             session task-work := send Report end
             conform server : server-wait :=
               get (r : Report) done
               fail
                 stop
             conform task : task-work := put ok done
             meet wire : server with task may fail buffer 1
             """)

    assert msg =~ "linear channel abandoned"

    assert check("""
           data Report : Type where
             ok : Report
           session %1 server-wait := recv Report end
           session task-work := send Report end
           conform server : server-wait :=
             get (r : Report) done
             fail
               done
           conform task : task-work := put ok done
           meet wire : server with task may fail buffer 1
           """) == :ok
  end

  test "a rendezvous meeting may mark a party" do
    assert check("""
           data Report : Type where
             ok : Report
           session task-work := send Report end
           session server-wait := dual task-work
           conform task : task-work := put ok done
           conform server : server-wait :=
             get (r : Report) done
             fail
               done
           meet wire : server with task may fail
           """) == :ok
  end

  test "every backend refuses may fail, and a meeting without the mark still emits" do
    assert {:ok, src} = Muro.emit_file("examples/may-fail-control.muro", MayFailControl)
    refute src =~ "c:mayfail"

    dir =
      System.tmp_dir!()
      |> Path.join("muro-mayfail-emit-#{System.unique_integer([:positive])}")

    File.mkdir_p!(dir)
    path = Path.join(dir, "free.muro")
    File.cp!("examples/may-fail-free.muro", path)
    on_exit(fn -> File.rm_rf(dir) end)

    assert {:error, @refuse} = Muro.emit_file(path, MayFail)
    assert {:error, @refuse} = Muro.emit_exunit(path, MayFailEmitTest)
    assert {:error, @refuse} = Muro.emit_c(path, nif: false)
    assert {:error, @refuse} = Muro.emit_rust(path)
    assert {:error, @refuse} = Muro.emit_zig(path)
    assert {:error, @refuse} = Muro.emit_js(path)
    assert {:error, @refuse} = Muro.emit_asm(path)
    assert {:error, @refuse} = Muro.emit_node(path, :a)

    assert {:ok, fsm} = Muro.emit_fsm(path, MayFail)
    assert fsm =~ "def down(state)"
    assert fsm =~ "def down(state, reason)"
    refute fsm =~ "c:mayfail"
    refute fsm =~ "GenServer"
    refute fsm =~ "Process."

    assert {:ok, [otp]} = Muro.emit_otp(path)
    otp_src = File.read!(otp)
    assert otp_src =~ "fail_at"
    assert otp_src =~ "Process.monitor"
    refute otp_src =~ "c:mayfail"

    assert Enum.sort(File.ls!(dir)) == ["free.muro", "free_otp.ex"]
  end

  test "a positional match stops before a bare fail" do
    assert show("""
           session s := recv Bit end
           conform server : s := get (b : Bit) match b done done fail done
           """) == "get (b : Bit) (match b done done) fail done"

    assert show("""
           session s := recv Bit end
           conform server : s :=
             get (b : Bit) match b
               | b0 => done
               | b1 => done
               fail done
           """) == "get (b : Bit) (match b | b0 => done | b1 => done) fail done"

    assert show("""
           session s := recv Bit end
           conform server : s := get (b : Bit) (match b done done) fail done
           """) == "get (b : Bit) (match b done done) fail done"

    assert show("""
           session s := recv Bit end
           conform server : s := get (b : Bit) done fail (e : Bit) done
           """) == "get (b : Bit) done fail (e : Bit) done"

    assert {:error, msg} =
             Parser.parse("""
             session s := recv Bit end
             conform server : s := get (b : Bit) match b fail done
             """)

    assert msg =~ "expected a process"

    assert {:ok, book} =
             Parser.parse("""
             session s := recv Bit end
             conform server : s := get (b : Bit) match b (fail) done fail done
             """)

    assert {:on_fail, {:get, :bit, :b, {:match, :b, [{:call, :fail}, :done]}}, nil, :done} =
             conform_proc(book)
  end

  test "a positional match failure arm checks, and a named arm still does" do
    assert check("""
           session choice := recv Bit end
           session offer := send Bit end
           conform server : choice := get (b : Bit) match b done done fail done
           conform task : offer := put b0 done
           meet wire : server with task may fail buffer 1
           """) == :ok

    assert check("""
           session choice := recv Bit end
           session offer := send Bit end
           conform server : choice :=
             get (b : Bit) match b
               | b0 => done
               | b1 => done
               fail done
           conform task : offer := put b0 done
           meet wire : server with task may fail buffer 1
           """) == :ok

    assert check("""
           session choice := recv Bit end
           session offer := send Bit end
           conform server : choice := get (b : Bit) (match b done done) fail done
           conform task : offer := put b0 done
           meet wire : server with task may fail buffer 1
           """) == :ok
  end

  test "a party at done or stop has no death step" do
    %{g: g, cs: cs, edges: edges} = prep_file!("examples/may-fail-free.muro", "free")

    done = Enum.filter(cs, &Temporal.holds?(g, {:done, :r}, &1))
    assert done != []

    for conf <- done do
      assert Temporal.holds?(g, {:done, :r}, conf)
      refute Temporal.holds?(g, {:dead, :r}, conf)
      assert deaths(edges, conf, :rdie) == []
    end

    assert Enum.any?(cs, fn conf ->
             Temporal.holds?(g, {:dead, :r}, conf) and
               not Temporal.holds?(g, {:done, :r}, conf)
           end)

    assert Enum.any?(cs, fn conf ->
             not Temporal.holds?(g, {:done, :r}, conf) and
               not Temporal.holds?(g, {:dead, :r}, conf) and
               deaths(edges, conf, :rdie) != []
           end)

    %{g: g, cs: cs, edges: edges} =
      prep!(
        """
        data Report : Type where
          ok : Report
        session task-work := send Report end
        session server-wait := recv Report end
        conform task : task-work := put ok stop
        conform server : server-wait :=
          get (r : Report) done
          fail done
        meet halt : server with task may fail buffer 1
        """,
        "halt"
      )

    stopped = Enum.filter(cs, &Temporal.holds?(g, {:stopped, :r}, &1))
    assert stopped != []

    for conf <- stopped do
      assert Temporal.holds?(g, {:stopped, :r}, conf)
      refute Temporal.holds?(g, {:dead, :r}, conf)
      assert deaths(edges, conf, :rdie) == []
      assert deaths(edges, conf, :ldie) == []
    end
  end

  test "role dead is the crash, and a halt is not dead" do
    free = File.read!("examples/may-fail-free.muro")

    assert check("""
           #{free}
           temporal crashed : free := (task dead) leads_to (server done)
           """) == :ok

    assert Check.temporal_lines() == [
             "temporal freed: holds in 5 reachable states, 6 transitions",
             "temporal crashed: holds in 5 reachable states, 6 transitions"
           ]

    assert {:error, msg} =
             check("""
             #{free}
             temporal early : free := always ((task dead) implies (server done))
             """)

    assert msg =~ "task dead"

    plain = File.read!("examples/may-fail-control.muro")

    assert check("""
           #{plain}
           temporal quiet : plain := always (not (task dead))
           """) == :ok

    assert Check.temporal_lines() == [
             "temporal released: holds in 3 reachable states, 3 transitions",
             "temporal quiet: holds in 3 reachable states, 3 transitions"
           ]

    assert {:error, msg} =
             check("""
             #{plain}
             temporal quiet : plain := eventually (task dead)
             """)

    assert msg =~ "task dead"

    assert check("""
           data Report : Type where
             ok : Report
           session task-work := send Report end
           session server-wait := recv Report end
           conform task : task-work := put ok done
           conform server : server-wait :=
             get (r : Report) done
             fail done
           meet free : server with task may fail buffer 1
           temporal stayed : free := always ((task done) implies (not (task dead)))
           temporal crashed : free := always ((task dead) implies (not (task done)))
           """) == :ok

    assert check("""
           data Report : Type where
             ok : Report
           session task-work := send Report end
           session server-wait := recv Report end
           conform task : task-work := put ok stop
           conform server : server-wait :=
             get (r : Report) done
             fail done
           meet halt : server with task may fail buffer 1
           temporal stayed : halt := always ((task stopped) implies (not (task dead)))
           """) == :ok

    assert {:ok, book} =
             Parser.parse("""
             def dead : run Nat := 0
             session s := end
             conform go : s := dead
             temporal t : wire := always (task dead)
             """)

    by_name = Map.new(book, &{&1.name, &1})
    assert by_name["dead"].mode == :run
    assert by_name["go"].proc == {:call, :dead}
    assert by_name["t"].formula == {:always, {:dead, "task"}}
    assert Temporal.pp_prop({:dead, "task"}) == "task dead"
  end

  test "buffer 2 keeps a drop and a delivery of the queued messages" do
    src = """
    data Note : Type where
      a : Note
      b : Note
    session out := send Note (send Note (send Note end))
    session inn := recv Note (recv Note (recv Note end))
    conform task : out := put a (put b (put a done))
    conform server : inn :=
      get (x : Note) (
        get (y : Note) (
          get (z : Note) done
          fail done
        )
        fail done
      )
      fail done
    meet buf : server with task may fail buffer 2
    """

    assert check(src) == :ok
    %{g: g, cs: cs, edges: edges} = prep!(src, "buf")

    queued =
      Enum.filter(cs, fn conf ->
        length(r2l(conf)) >= 2 and ir(conf) != :dead and
          block_k(g.code_r, ir(conf)) not in [:done, :stop] and
          deaths(edges, conf, :rdie) != []
      end)

    assert queued != []

    for conf <- queued do
      [dead] = deaths(edges, conf, :rdie)
      assert length(r2l(dead)) == length(r2l(conf))
      assert ir(dead) == :dead

      drops = deaths(edges, dead, :rdrop)
      delivers = deaths(edges, dead, :lside)
      assert drops != []
      assert delivers != []
      assert Enum.all?(drops, &(length(r2l(&1)) == length(r2l(dead)) - 1))
      assert Enum.all?(delivers, &(length(r2l(&1)) == length(r2l(dead)) - 1))
    end
  end

  test "a crash while the survivor is blocked consumes the waiting put" do
    src = """
    data Report : Type where
      ok : Report
    session server-s := send Nat (send Nat (recv Report end))
    session task-s := recv Nat (recv Nat (send Report end))
    conform server : server-s :=
      put 0 (
        put 1 (
          get (r : Report) done
          fail done
        )
      )
    conform task : task-s :=
      get (n : Nat) (
        get (m : Nat) (put ok done)
      )
    meet full : server with task may fail buffer 1
    """

    assert check(src) == :ok
    %{g: g, cs: cs, edges: edges} = prep!(src, "full")

    waiting =
      Enum.filter(cs, fn conf ->
        length(l2r(conf)) == 1 and block_k(g.code_l, il(conf)) == :put and
          ir(conf) != :dead and deaths(edges, conf, :lside) == [] and
          deaths(edges, conf, :rdie) != []
      end)

    assert waiting != []

    for conf <- waiting do
      [dead] = deaths(edges, conf, :rdie)
      assert l2r(dead) == l2r(conf)
      assert il(dead) == il(conf)
      assert ir(dead) == :dead

      [gone] = deaths(edges, dead, :lside)
      assert l2r(gone) == l2r(dead)
      assert il(gone) != il(dead)
      assert block_k(g.code_l, il(gone)) == :get
    end
  end

  test "cover and get on need a failure arm, and so does a receive in a match" do
    assert check("""
           session offered := branch end end
           session choosing := choose end end
           conform server : offered := cover done done fail done
           conform task : choosing := pick0 done
           meet wire : server with task may fail buffer 1
           """) == :ok

    assert {:error, msg} =
             check("""
             session offered := branch end end
             session choosing := choose end end
             conform server : offered := cover done done
             conform task : choosing := pick0 done
             meet wire : server with task may fail buffer 1
             """)

    assert msg =~ "server: cover does not handle failure of task"

    assert check("""
           session route := recv (b : Bit) on end end
           session sendb := send (b : Bit) on end end
           conform server : route := get (b : Bit) on done done fail done
           conform task : sendb := put b0 done
           meet wire : server with task may fail buffer 1
           """) == :ok

    assert {:error, msg} =
             check("""
             session route := recv (b : Bit) on end end
             session sendb := send (b : Bit) on end end
             conform server : route := get (b : Bit) on done done
             conform task : sendb := put b0 done
             meet wire : server with task may fail buffer 1
             """)

    assert msg =~ "server: get (b : Bit) does not handle failure of task"

    assert check("""
           data Ans : Type where
             yes : Ans
             no : Ans
           session server-s := recv Ans (recv Nat end)
           session task-s := send Ans (send Nat end)
           conform server : server-s :=
             get (a : Ans) (
               match a
                 (get (n : Nat) done fail done)
                 (get (n : Nat) done fail done)
             )
             fail done
           conform task : task-s := put yes (put 0 done)
           meet wire : server with task may fail buffer 1
           """) == :ok

    assert {:error, msg} =
             check("""
             data Ans : Type where
               yes : Ans
               no : Ans
             session server-s := recv Ans (recv Nat end)
             session task-s := send Ans (send Nat end)
             conform server : server-s :=
               get (a : Ans) (
                 match a
                   (get (n : Nat) done)
                   (get (n : Nat) done fail done)
               )
               fail done
             conform task : task-s := put yes (put 0 done)
             meet wire : server with task may fail buffer 1
             """)

    assert msg =~ "server: get (n : Nat) does not handle failure of task"
  end

  test "a bad react still offers the crash, and an unmarked meeting offers nothing" do
    g = %{
      code_l: [
        %{k: :get, tag: :nat, slot: 0, cont: 1, show: "get (n : Nat)", at: 0}
      ],
      code_r: [
        %{k: :put, atom: {:nat, 0}, cont: 1, show: "put 0", at: 0},
        %{k: :done, show: "done", at: 1}
      ],
      alpha: [{:nat, 0}, {:con, "ok"}],
      cap: 2,
      may_l: false,
      may_r: true
    }

    conf = {0, 0, [], [{:pay, 1}], [0], []}
    assert [{:rdie, dest}] = Graph.steps_of(g, conf)
    assert dest == {0, :dead, [], [{:pay, 1}], [0], []}

    edges = Graph.edges(g, conf)
    assert Enum.any?(edges, &match?({:rside, _}, &1))
    assert Enum.any?(edges, &match?({:rdie, _}, &1))

    unmarked = %{g | may_r: false}
    assert Graph.steps_of(unmarked, conf) == []

    %{edges: plain} = prep_file!("examples/may-fail-control.muro", "plain")

    tags =
      plain
      |> Map.values()
      |> List.flatten()
      |> Enum.map(&elem(&1, 0))

    refute :ldie in tags
    refute :rdie in tags
    refute :ldrop in tags
    refute :rdrop in tags
  end

  test "the failure arm runs when the task is killed, and the report still finishes" do
    path = copy!("examples/may-fail-free.muro")
    mod = compile_otp!(path)
    assert {:ok, left, right, lref, rref} = mod.free()
    assert_down(lref, left, :normal)
    assert_down(rref, right, :normal)

    assert kill_before_go(mod, skel!(path, "server"), 1, :kill) == :normal
  end

  test "a meeting without the mark still abandons, and down is not a step" do
    path = copy!("examples/may-fail-control.muro")
    mod = compile_otp!(path)
    assert {:ok, left, right, lref, rref} = mod.plain()
    assert_down(lref, left, :normal)
    assert_down(rref, right, :normal)
    assert kill_before_go(mod, skel!(path, "server"), 1, :kill) == {:shutdown, :abandon}
    refute inspect(skel!(path, "server")) =~ "fail_at"

    fsm = compile_fsm!(path, MayFailControlFsm)
    child = child(fsm, "server-wait")
    assert {:error, {:unexpected, _, {:recv, _}, :down}} = child.down(child.init())
  end

  test "fsm down takes the failure arm, and recv takes the report" do
    path = copy!("examples/may-fail-free.muro")
    fsm = compile_fsm!(path, MayFailFreeFsm)
    server = child(fsm, "server-wait")
    st = server.init()
    assert {:ok, failed} = server.down(st)
    assert server.done?(failed)
    assert server.expected(failed) == :done

    assert {:ok, reported} = server.recv(server.init(), :ok)
    assert server.done?(reported)

    task = child(fsm, "task-work")
    assert {:error, {:unexpected, _, {:send, _}, :down}} = task.down(task.init())
  end

  test "a bound reason is the DOWN reason, and down checks the one the host supplies" do
    src = """
    session task-work := send Bit end
    session server-wait := recv Bit end
    conform task : task-work := put b0 done
    conform server : server-wait :=
      get (b : Bit) done
      fail (e : Bit)
        match e
          | b0 => done
          | b1 => stop
    meet wire : server with task may fail
    """

    path = write_book!("reason", src)
    mod = compile_otp!(path)
    assert kill_before_go(mod, skel!(path, "server"), nil, :b0) == :normal
    assert kill_before_go(mod, skel!(path, "server"), nil, :b1) == {:shutdown, :abandon}

    fsm = compile_fsm!(path, MayFailReasonFsm)
    server = child(fsm, "server-wait")
    st = server.init()
    assert {:error, {:unexpected, _, {:down, :bit}, :down}} = server.down(st)
    assert {:error, {:unexpected, _, {:down, :bit}, 1}} = server.down(st, 1)
    assert {:ok, yes} = server.down(st, :b0)
    assert server.done?(yes)
    assert {:ok, no} = server.down(st, :b1)
    refute server.done?(no)
    assert server.expected(no) == :stop
  end

  test "a put to a stopped task is consumed, and down is not a send" do
    path = copy!("examples/may-fail-send.muro")
    mod = compile_otp!(path)
    skel = skel!(path, "server")
    assert match?({:say, 0, {:fail_at, _, _, _}}, skel)
    assert kill_before_go(mod, skel, 1, :kill) == :normal

    fsm = compile_fsm!(path, MayFailSendFsm)
    server = child(fsm, "server-work")
    assert {:error, {:unexpected, _, {:send, _}, :down}} = server.down(server.init())
    assert {:ok, st} = server.send(server.init(), 0)
    assert {:ok, failed} = server.down(st)
    assert server.done?(failed)
  end

  test "an arm that stops does not release the slot" do
    src = """
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
    """

    path = write_book!("hold", src)
    mod = compile_otp!(path)
    assert kill_before_go(mod, skel!(path, "server"), 1, :kill) == {:shutdown, :abandon}

    fsm = compile_fsm!(path, MayFailHoldFsm)
    server = child(fsm, "server-wait")
    assert {:ok, st} = server.down(server.init())
    refute server.done?(st)
    assert server.expected(st) == :stop
  end

  test "a protocol stop is a halt, and the failure arm does not run" do
    path = copy!("examples/may-fail-free.muro")
    mod = compile_otp!(path)
    server_skel = skel!(path, "server")
    {:ok, server} = GenServer.start(mod, {server_skel, :open, 1})
    {:ok, peer} = GenServer.start(mod, {:leave, :open, 1})
    :ok = GenServer.call(server, {:muro_peer, peer})
    :ok = GenServer.call(peer, {:muro_peer, server})
    ref = Process.monitor(server)
    true = :erlang.suspend_process(server)
    send(peer, :muro_go)

    await_mailbox(server, fn msgs ->
      Enum.any?(msgs, &match?({:muro_halt, _}, &1)) and
        Enum.any?(msgs, &match?({:DOWN, _, :process, ^peer, _}, &1))
    end)

    send(server, :muro_go)
    :erlang.resume_process(server)
    assert_down(ref, server, {:shutdown, :abandon})
  end

  test "left, right, both, and an unbounded meeting emit" do
    right = copy!("examples/may-fail-free.muro")
    assert {:ok, _} = Muro.emit_otp(right)
    assert {:ok, _} = Muro.emit_fsm(right, MayFailRightFsm)

    left =
      write_book!("left", """
      data Report : Type where
        ok : Report
      session task-work := recv Report end
      session server-wait := send Report end
      conform server : server-wait := put ok done
      conform task : task-work :=
        get (r : Report) done
        fail
          done
      meet left : server may fail with task buffer 1
      """)

    mod = compile_otp!(left)
    assert kill_before_go(mod, skel!(left, "task"), 1, :kill) == :normal
    fsm = compile_fsm!(left, MayFailLeftFsm)
    task = child(fsm, "task-work")
    assert {:ok, st} = task.down(task.init())
    assert task.done?(st)

    both =
      write_book!("both", """
      session server-wait := recv Bit (send Bit end)
      session task-work := send Bit (recv Bit end)
      conform server : server-wait :=
        get (b : Bit) (put b0 done)
        fail
          done
      conform task : task-work :=
        put b0 (get (c : Bit) done fail done)
      meet both : server may fail with task may fail buffer 1
      """)

    assert {:ok, _} = Muro.emit_otp(both)
    assert {:ok, src} = Muro.emit_fsm(both, MayFailBothFsm)
    assert src =~ "def down(state)"

    open =
      write_book!("open", """
      data Report : Type where
        ok : Report
      session task-work := send Report end
      session server-wait := recv Report end
      conform task : task-work := put ok done
      conform server : server-wait :=
        get (r : Report) done
        fail
          done
      meet wire : server with task may fail
      """)

    mod = compile_otp!(open)
    assert kill_before_go(mod, skel!(open, "server"), nil, :kill) == :normal
    assert {:ok, _} = Muro.emit_fsm(open, MayFailOpenFsm)
  end

  defp copy!(example) do
    dir = tmp!()
    path = Path.join(dir, Path.basename(example))
    File.cp!(example, path)
    path
  end

  defp write_book!(name, src) do
    path = Path.join(tmp!(), name <> ".muro")
    File.write!(path, src)
    path
  end

  defp tmp! do
    dir = Path.join(System.tmp_dir!(), "muro-mayfail-otp-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf(dir) end)
    dir
  end

  defp compile_otp!(path) do
    assert {:ok, [file]} = Muro.emit_otp(path)
    mods = Code.compile_string(File.read!(file))
    on_exit(fn -> purge(mods) end)
    stem = path |> Path.basename(".muro") |> String.replace("-", "_") |> Macro.camelize()
    Module.concat([stem <> "Otp"])
  end

  defp compile_fsm!(path, mod) do
    assert {:ok, src} = Muro.emit_fsm(path, mod)
    mods = Code.compile_string(src)
    on_exit(fn -> purge(mods) end)
    mod
  end

  defp purge(mods) do
    for {mod, _} <- mods do
      :code.purge(mod)
      :code.delete(mod)
    end
  end

  defp child(parent, name), do: Module.concat(parent, Muro.Emit.elixir_alias(name))

  defp skel!(path, name) do
    assert {:ok, book} = Muro.Load.file(path)
    book = Muro.Prelude.for_emit(book)
    %{proc: proc} = Enum.find(book, &(&1.kind == :conform and &1.name == name))
    Session.carry_fail(proc, book)
  end

  defp kill_before_go(mod, skel, cap, reason) do
    dummy = spawn(fn -> receive do: (:x -> :ok) end)
    arg = if is_integer(cap), do: {skel, :open, cap}, else: {skel, :open}
    {:ok, pid} = GenServer.start(mod, arg)
    :ok = GenServer.call(pid, {:muro_peer, dummy})
    ref = Process.monitor(pid)
    true = :erlang.suspend_process(pid)
    Process.exit(dummy, reason)

    await_mailbox(pid, fn msgs ->
      Enum.any?(msgs, &match?({:DOWN, _, :process, ^dummy, _}, &1))
    end)

    send(pid, :muro_go)
    :erlang.resume_process(pid)
    reason = await_down(ref, pid)
    if Process.alive?(pid), do: GenServer.stop(pid)
    if Process.alive?(dummy), do: Process.exit(dummy, :kill)
    reason
  end

  defp await_mailbox(pid, pred) do
    deadline = System.monotonic_time(:millisecond) + 2_000

    Stream.repeatedly(fn ->
      cond do
        not Process.alive?(pid) ->
          :dead

        true ->
          {:messages, msgs} = Process.info(pid, :messages)
          if pred.(msgs), do: :hit, else: Process.sleep(10)
      end
    end)
    |> Enum.find(fn
      :hit -> true
      :dead -> true
      _ -> System.monotonic_time(:millisecond) > deadline
    end)
  end

  defp await_down(ref, pid) do
    receive do
      {:DOWN, ^ref, :process, ^pid, reason} -> reason
    after
      2_000 -> flunk("timed out waiting for #{inspect(pid)}")
    end
  end

  defp assert_down(ref, pid, reason) do
    assert await_down(ref, pid) == reason
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book, [])
  end

  defp show(src) do
    assert {:ok, book} = Parser.parse(src)
    Session.show_proc(conform_proc(book))
  end

  defp conform_proc(book) do
    %{proc: proc} = Enum.find(book, &match?(%{kind: :conform}, &1))
    proc
  end

  defp prep!(src, meeting) do
    assert {:ok, named} = Parser.parse(src)
    assert {:ok, book} = Ast.book_to_db(named)
    assert {:ok, prep} = Temporal.prepare(book, meeting, :ok)
    prep
  end

  defp prep_file!(path, meeting), do: prep!(File.read!(path), meeting)

  defp il({i, _, _, _, _, _}), do: i
  defp ir({_, i, _, _, _, _}), do: i
  defp l2r({_, _, q, _, _, _}), do: q
  defp r2l({_, _, _, q, _, _}), do: q

  defp block_k(_code, :dead), do: :dead
  defp block_k(code, i) when is_integer(i), do: Map.fetch!(Enum.at(code, i), :k)

  defp deaths(edges, conf, tag) do
    for {^tag, dest} <- Map.get(edges, conf, []), do: dest
  end
end

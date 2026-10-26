defmodule Muro.SessionTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, Emit, IR, Parser, Session}

  test "ping.muro checks, and emit keeps no session" do
    path = "examples/ping.muro"
    src = File.read!(path)
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    assert Muro.check_file(path) == :ok

    assert {:ok, out} = Muro.emit_file(path, Ping)
    refute out =~ "pong"
    refute out =~ "put"
    refute out =~ "session"

    assert {:ok, []} = IR.elaborate_file(path)
  end

  test "a conform may name a session declared later" do
    assert check("""
           conform pong : ping := get Nat (put 1 done)
           session ping := recv Nat (send Nat end)
           """) == :ok
  end

  test "a session follows a data declaration" do
    assert check("""
           data Flag : Type where
             yes : Flag

           session closed := end
           conform finished : closed := done
           """) == :ok
  end

  test "end and send stay identifiers outside a session" do
    assert check("""
           def end : run Nat := 0
           def send : run Nat := 0
           def Bit : run Nat := 0
           """) == :ok
  end

  test "a tuple wrapping a fixed map conforms, and so does another value of that type" do
    assert check("""
           session box := send (Bit * {x : Nat, y : Nat}) end
           conform here : box := put (b0, {x = 0, y = 0}) done
           conform there : box := put (b1, {x = 1, y = 2}) done
           session take := dual box
           conform recv : take := get (Bit * {x : Nat, y : Nat}) done
           """) == :ok
  end

  test "a repeated field is refused, and an undeclared payload name is refused" do
    assert {:error, msg} = Parser.parse("session box := send {x : Nat, x : Bit} end\n")
    assert msg =~ "duplicate field x"

    assert {:error, msg} = check("session box := send String end\n")
    assert msg =~ "ill-formed payload"
  end

  test "a data argument stops before a pair" do
    assert {:ok, [box]} = Parser.parse("session box := send Maybe Nat * Bit end\n")
    assert box.proto == {:send, {:pair, {:dat, "Maybe", [:nat]}, :bit}, :end}
  end

  test "a run beside a session is what emit keeps" do
    src = """
    session ping := recv Nat (send Nat end)
    conform pong : ping := get Nat (put 1 done)
    def z : run Nat := 0
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    out = Emit.emit_module(PingRun, book)
    assert out =~ ~r/\bdef z\b/
    refute out =~ "pong"
    refute out =~ "put"
  end

  test "a value of the wrong type is refused" do
    assert {:error, msg} =
             check("""
             session ping := recv Nat (send Nat end)
             conform early-send : ping := get Bit (put b0 done)
             """)

    assert msg =~ "get Bit (put b0 done) does not conform to recv Nat (send Nat end)"
  end

  test "two sends where the continuation is end are refused" do
    assert {:error, msg} =
             check("""
             session once := send Nat end
             conform twice : once := put 0 (put 1 done)
             """)

    assert msg =~ "put 1 done does not conform to end"
  end

  test "a send where the protocol says receive is refused" do
    assert {:error, msg} =
             check("""
             session ping := recv Nat end
             conform swapped : ping := put 0 done
             """)

    assert msg =~ "put 0 done does not conform to recv Nat end"
  end

  test "an unknown session is refused" do
    assert {:error, msg} =
             check("""
             conform pong : gone := done
             """)

    assert msg =~ "unknown session gone"
  end

  test "a session name is not a definition" do
    assert {:error, msg} =
             check("""
             session ping := end
             def z : run Nat := ping
             """)

    assert msg =~ "ping is a session, not a definition"
  end

  test "finishes when every leaf is done" do
    assert Session.finishes(:done) == :yes
    assert Session.finishes(:stop) == :no
    assert Session.finishes({:put, :nat, {:nat, 0}, :stop}) == :no
    assert Session.finishes({:get, :nat, :k, {:put, :nat, {:nat, 0}, :done}}) == :yes
    assert Session.finishes({:pick0, :done}) == :yes
    assert Session.finishes({:pick1, :stop}) == :no
    assert Session.finishes({:cover, :done, :stop}) == :no
    assert Session.finishes({:cover, :done, {:put, :nat, {:nat, 0}, :done}}) == :yes
  end

  test "a session records its mark" do
    assert {:ok, book} =
             Parser.parse("""
             session ping := end
             session %0 open := end
             session %1 closed := end
             """)

    mults = Map.new(book, &{&1.name, &1.mult})
    assert mults["ping"] == :affine
    assert mults["open"] == :affine
    assert mults["closed"] == :linear
  end

  test "%1 is a whole token" do
    assert {:error, msg} = Parser.parse("session %10 once := end\n")
    assert msg =~ "expected %0 or %1"
  end

  test "a finishing linear session checks" do
    assert check("""
           session %1 ping-done := recv Nat (send Nat end)
           conform pong-done : ping-done := get Nat (put 1 done)
           session %1 arms := branch end (send Nat end)
           conform both : arms := cover done (put 0 done)
           """) == :ok
  end

  test "%0 still allows abandonment" do
    assert check("""
           session %0 once := send Nat end
           conform left : once := put 0 stop
           conform none : once := stop
           """) == :ok
  end

  test "a linear session refuses an abandoned channel" do
    assert {:error, msg} =
             check("""
             session %1 once := send Nat end
             conform left : once := put 0 stop
             """)

    assert msg =~ "linear channel abandoned"
    refute msg =~ "does not conform"
  end

  test "one abandoned arm of a linear branch is refused" do
    assert {:error, msg} =
             check("""
             session %1 arms := branch end end
             conform half : arms := cover done stop
             """)

    assert msg =~ "linear channel abandoned"
  end

  test "a linear session still reports a protocol mismatch" do
    assert {:error, msg} =
             check("""
             session %1 once := end
             conform bad : once := put 0 done
             """)

    assert msg =~ "put 0 done does not conform to end"
    refute msg =~ "abandoned"
  end

  test "a session name is declared once" do
    assert {:error, msg} =
             check("""
             session ping := end
             def ping : run Nat := 0
             """)

    assert msg =~ "duplicate name ping"
  end

  test "value binding: echo conforms" do
    assert check("""
           session ping := recv Nat (send Nat end)
           conform echo : ping := get (k : Nat) (put k done)
           """) == :ok
  end

  test "value binding: a bound value need not be used" do
    assert check("""
           session box := recv (Nat * Nat) (send Nat end)
           conform use-first : box := get (p : (Nat * Nat)) (put 0 done)
           """) == :ok
  end

  test "value binding: unbound variable is refused" do
    assert {:error, msg} =
             check("""
             session ping := recv Nat (send Nat end)
             conform bad : ping := get (k : Nat) (put m done)
             """)

    assert msg =~ "unbound variable m"
  end

  test "value binding: variable from outer scope" do
    assert check("""
           session nested := recv Nat (recv Nat (send Nat end))
           conform outer : nested := get (k : Nat) (get (m : Nat) (put k done))
           """) == :ok
  end

  test "value binding: a bound value is sent at its own type" do
    assert check("""
           session pair-echo := recv (Nat * Nat) (send (Nat * Nat) end)
           conform swap : pair-echo := get (p : (Nat * Nat)) (put p done)
           """) == :ok
  end

  test "value binding: a bound value sent at another type is refused" do
    assert {:error, msg} =
             check("""
             session mixed := recv Bit (send Nat end)
             conform mix : mixed := get (v : Bit) (put v done)
             """)

    assert msg =~ "put v done does not conform to send Nat end"
  end

  test "value binding: a rebound name refers to the inner binding" do
    assert check("""
           session inner := recv Nat (recv Bit (send Bit end))
           conform latest : inner := get (v : Nat) (get (v : Bit) (put v done))
           """) == :ok

    assert {:error, msg} =
             check("""
             session outer := recv Nat (recv Bit (send Nat end))
             conform stale : outer := get (v : Nat) (get (v : Bit) (put v done))
             """)

    assert msg =~ "put v done does not conform to send Nat end"
  end

  test "a continuation may mention a received nat as a vector length" do
    src = """
    session sized := recv (n : Nat) (send (Vec Nat n) end)
    session back := dual sized
    conform server : sized := get (n : Nat) (put (rep n 0) done)
    conform client : back := put 2 (get (Vec Nat 2) done)
    """

    assert {:ok, book} = Parser.parse(src)
    sized = Enum.find(book, &(&1.name == "sized"))
    assert sized.proto == {:drecv, :n, :nat, {:send, {:vec, :nat, {:var, :n}}, :end}}

    assert Session.dual(sized.proto) ==
             {:dsend, :n, :nat, {:recv, {:vec, :nat, {:var, :n}}, :end}}

    assert Session.dual(Session.dual(sized.proto)) == sized.proto
    assert Session.proto_ok(sized.proto) == :ok
    assert Session.show_proto(sized.proto) == "recv (n : Nat) (send (Vec Nat n) end)"

    assert Session.show_proto(Session.dual(sized.proto)) ==
             "send (n : Nat) (recv (Vec Nat n) end)"

    assert Check.check_sig(book) == :ok
  end

  test "a vector length that is not that nat is refused" do
    assert {:error, msg} =
             check("""
             session bits := recv (b : Bit) (send (Vec Nat b) end)
             """)

    assert msg =~ "vector length is not a nat"

    assert {:error, msg} =
             check("""
             session open := send (Vec Nat n) end
             """)

    assert msg =~ "unbound length"

    assert {:error, msg} = Parser.parse("session bare := send (Vec Nat) end\n")
    assert msg =~ "expected a vector length"
  end

  test "a vector of another length does not conform" do
    assert {:error, msg} =
             check("""
             session sized := recv (n : Nat) (send (Vec Nat n) end)
             session back := dual sized
             conform bad : back := put 2 (get (Vec Nat 3) done)
             """)

    assert msg =~ "does not conform"
  end

  test "an evidence payload sends a nat at most a bound" do
    src = """
    session window := recv (w : Nat) (send (d : Nat) {d ≤ w} end)
    session grant-end := dual window
    conform full : window := get (w : Nat) (put w done)
    conform empty : window := get (w : Nat) (put 0 done)
    conform grant : grant-end := put 8 (get (d : Nat) done)
    """

    assert {:ok, book} = Parser.parse(src)
    window = Enum.find(book, &(&1.name == "window"))
    assert window.proto == {:drecv, :w, :nat, {:esend, :d, {:var, :w}, :end}}
    assert Session.dual(window.proto) == {:dsend, :w, :nat, {:erecv, :d, {:var, :w}, :end}}
    assert Session.dual(Session.dual(window.proto)) == window.proto
    assert Session.proto_ok(window.proto) == :ok
    assert Session.show_proto(window.proto) == "recv (w : Nat) (send (d : Nat) {d ≤ w} end)"

    assert Session.show_proto(Session.dual(window.proto)) ==
             "send (w : Nat) (recv (d : Nat) {d ≤ w} end)"

    assert Check.check_sig(book) == :ok

    assert {:ok, [ascii]} = Parser.parse("session frame := send (d : Nat) {d <= 16384} end\n")
    assert ascii.proto == {:esend, :d, {:lit, 16384}, :end}
  end

  test "a numeral within a numeral bound conforms, and one past it does not" do
    assert check("""
           session granted := send (w : Nat) (send (d : Nat) {d ≤ w} end)
           conform within : granted := put 8 (put 5 done)
           conform edge : granted := put 8 (put 8 done)
           session frame := send (d : Nat) {d ≤ 16384} end
           conform small : frame := put 16384 done
           """) == :ok

    # d > w: nine is not at most eight.
    assert {:error, msg} =
             check("""
             session granted := send (w : Nat) (send (d : Nat) {d ≤ w} end)
             conform over : granted := put 8 (put 9 done)
             """)

    assert msg =~ "put 9 done does not conform to send (d : Nat) {d ≤ w} end"

    assert {:error, msg} =
             check("""
             session frame := send (d : Nat) {d ≤ 16384} end
             conform big : frame := put 16385 done
             """)

    assert msg =~ "does not conform"
  end

  test "a numeral against a received window has no evidence" do
    assert {:error, msg} =
             check("""
             session window := recv (w : Nat) (send (d : Nat) {d ≤ w} end)
             conform guess : window := get (w : Nat) (put 2 done)
             """)

    assert msg =~ "put 2 done does not conform to send (d : Nat) {d ≤ w} end"

    # Zero is at most any window, named or not.
    assert check("""
           session window := recv (w : Nat) (send (d : Nat) {d ≤ w} end)
           conform anon : window := get Nat (put 0 done)
           """) == :ok
  end

  test "a window name bound twice is no evidence" do
    assert {:error, msg} =
             check("""
             session stale := recv (w : Nat) (recv Nat (send (d : Nat) {d ≤ w} end))
             conform s : stale := get (w : Nat) (get (w : Nat) (put w done))
             """)

    assert msg =~ "put w done does not conform"

    assert check("""
           session stale := recv (w : Nat) (recv Nat (send (d : Nat) {d ≤ w} end))
           conform s : stale := get (w : Nat) (get (u : Nat) (put w done))
           """) == :ok

    # The window is a nat. Sending another received nat is no evidence.
    assert {:error, _} =
             check("""
             session two := recv (w : Nat) (recv Nat (send (d : Nat) {d ≤ w} end))
             conform s : two := get (w : Nat) (get (u : Nat) (put u done))
             """)
  end

  test "an ill-formed evidence payload is refused" do
    assert {:error, msg} = check("session open := send (d : Nat) {d ≤ w} end\n")
    assert msg =~ "unbound bound name"

    assert {:error, msg} =
             check("session bits := recv (b : Bit) (send (d : Nat) {d ≤ b} end)\n")

    assert msg =~ "bound is not a nat"

    assert {:error, msg} = Parser.parse("session other := send (d : Nat) {e ≤ 3} end\n")
    assert msg =~ "the bound names the nat that is sent"

    assert {:error, msg} = Parser.parse("session bit := send (d : Bit) {d ≤ 3} end\n")
    assert msg =~ "an evidence payload is a nat"

    # The name is in scope in its bound only.
    assert {:error, msg} =
             check("session later := send (d : Nat) {d ≤ 4} (send (Vec Nat d) end)\n")

    assert msg =~ "unbound length"
  end

  test "the receiver of an evidence payload gets a nat" do
    assert {:error, msg} =
             check("""
             session window := recv (w : Nat) (send (d : Nat) {d ≤ w} end)
             session grant-end := dual window
             conform g : grant-end := put 8 (get Bit done)
             """)

    assert msg =~ "get Bit done does not conform to recv (d : Nat) {d ≤ w} end"
  end

  test "a received bit selects one of two arms" do
    src = """
    session route := recv (b : Bit) on (send Nat end) (recv Nat end)
    session route-back := dual route
    conform server : route := get (b : Bit) on (put 1 done) (get (n : Nat) done)
    conform client : route-back := put b0 (get (m : Nat) done)
    conform client-one : route-back := put b1 (put 0 done)
    session echo-bit := recv (b : Bit) on (send Bit end) (send Bit end)
    conform echo : echo-bit := get (b : Bit) on (put b done) (put b done)
    """

    assert {:ok, book} = Parser.parse(src)
    route = Enum.find(book, &(&1.name == "route"))

    assert route.proto ==
             {:irecv, :b, {:send, :nat, :end}, {:recv, :nat, :end}}

    assert Session.dual(route.proto) ==
             {:isend, :b, {:recv, :nat, :end}, {:send, :nat, :end}}

    assert Session.dual(Session.dual(route.proto)) == route.proto
    assert Session.proto_ok(route.proto) == :ok

    assert Session.show_proto(route.proto) ==
             "recv (b : Bit) on (send Nat end) (recv Nat end)"

    assert Session.show_proto(Session.dual(route.proto)) ==
             "send (b : Bit) on (recv Nat end) (send Nat end)"

    server = Enum.find(book, &(&1.name == "server"))

    assert Session.show_proc(server.proc) ==
             "get (b : Bit) on (put 1 done) (get (n : Nat) done)"

    assert Session.skel(server.proc) ==
             {:index, :b, {:say, 1, :finish}, {:hear, :nat, :n, :finish}}

    assert Session.finishes(server.proc) == :yes
    assert Check.check_sig(book) == :ok

    # A length received outside the index stays a length. The bit shadows its own name.
    assert check("""
           session sized := recv (n : Nat) (recv (b : Bit) on (send (Vec Nat n) end) (recv (Vec Nat n) end))
           session back := dual sized
           conform server : sized := get (n : Nat) (get (b : Bit) on (put (rep n 0) done) (get (Vec Nat n) done))
           conform client : back := put 2 (put b0 (get (Vec Nat 2) done))
           """) == :ok
  end

  test "a bit index is not a vector length, and a nat does not choose an arm" do
    assert {:error, msg} =
             check("session bits := recv (b : Bit) on (send (Vec Nat b) end) end\n")

    assert msg =~ "vector length is not a nat"

    assert {:error, msg} = Parser.parse("session n := recv (n : Nat) on end end\n")
    assert msg =~ "a next action is chosen by a bit"

    assert {:error, msg} = Parser.parse("conform n : s := get (n : Nat) on done done\n")
    assert msg =~ "a next action is chosen by a bit"

    assert {:error, msg} = Parser.parse("conform n : s := get Bit on done done\n")
    assert msg =~ "a bit index is bound"
  end

  test "a variable bit does not select an arm, and one arm is not an index" do
    assert {:error, msg} =
             check("""
             session fwd := recv (b : Bit) (send (c : Bit) on end (send Nat end))
             conform bad : fwd := get (b : Bit) (put b done)
             """)

    assert msg =~ "put b done does not conform to send (c : Bit) on end (send Nat end)"

    assert check("""
           session fwd := recv (b : Bit) (send (c : Bit) on end (send Nat end))
           conform lit : fwd := get (b : Bit) (put b0 done)
           """) == :ok

    assert {:error, msg} =
             check("""
             session route := recv (b : Bit) on (send Nat end) (recv Nat end)
             conform one : route := get (b : Bit) (put 1 done)
             """)

    assert msg =~
             "get (b : Bit) (put 1 done) does not conform to recv (b : Bit) on (send Nat end) (recv Nat end)"

    assert {:error, msg} =
             check("""
             session route := recv (b : Bit) on (send Nat end) (recv Nat end)
             session back := dual route
             conform bad : back := put b0 (put 1 done)
             """)

    assert msg =~ "put 1 done does not conform to recv Nat end"
  end

  test "a linear index finishes on both arms" do
    assert {:error, msg} =
             check("""
             session %1 route := recv (b : Bit) on end (send Nat end)
             conform open : route := get (b : Bit) on done stop
             """)

    assert msg =~ "linear channel abandoned"

    assert check("""
           session %1 route := recv (b : Bit) on end (send Nat end)
           conform shut : route := get (b : Bit) on done (put 1 done)
           """) == :ok
  end

  test "on stays an identifier outside a session" do
    assert check("""
           def on : run Nat := 0
           """) == :ok
  end

  test "computed.muro checks, and emit keeps the runs" do
    path = "examples/computed.muro"
    assert Muro.check_file(path) == :ok

    assert {:ok, out} = Muro.emit_file(path, ComputedRun)
    assert out =~ ~r/\bdef effective\b/
    assert out =~ ~r/\bdef kept\b/
    refute out =~ "reply"
    refute out =~ "taker"
    refute out =~ "pass"
    refute out =~ "⊸"

    assert {:ok, funs} = IR.elaborate_file(path)
    assert Enum.map(funs, & &1.name) == ["mark", "effective", "kept"]
  end

  test "indexed.muro checks, and emit keeps the runs" do
    path = "examples/indexed.muro"
    assert {:ok, book} = Parser.parse(File.read!(path))
    assert Check.check_sig(book) == :ok
    assert Muro.check_file(path) == :ok

    assert {:ok, out} = Muro.emit_file(path, IndexedRun)
    assert out =~ ~r/\bdef on\b/
    assert out =~ ~r/\bdef kept\b/
    refute out =~ "wire"
    refute out =~ "GenServer"

    assert {:ok, funs} = IR.elaborate_file(path)
    assert Enum.map(funs, & &1.name) == ["on", "kept"]
  end

  test "the evidence is not in the skeleton" do
    assert {:ok, book} =
             Parser.parse("""
             session window := recv (w : Nat) (send (d : Nat) {d ≤ w} end)
             conform full : window := get (w : Nat) (put w done)
             """)

    full = Enum.find(book, &(&1.name == "full"))
    assert Session.skel(full.proc) == {:hear, :nat, :w, {:say, {:var, :w}, :finish}}
  end

  test "value binding: parse get with binder" do
    src =
      "conform test : ping := get (k : Nat) (put k done)\nsession ping := recv Nat (send Nat end)\n"

    assert {:ok, book} = Parser.parse(src)
    [conform | _] = book
    assert conform.kind == :conform
    assert {:get, :nat, :k, _} = conform.proc
  end

  test "a protocol may repeat, and the variable is the same protocol" do
    assert check("""
           session loop := rec X. recv Nat (send Nat X)
           session back := dual loop
           conform forever : loop := rec X. get (n : Nat) (put n X)
           conform sender : back := rec Y. put 1 (get (m : Nat) Y)
           meet endless : forever with sender
           session echo := rec X. recv (b : Bit) on (recv Nat (send Nat X)) end
           session echo-back := dual echo
           conform server : echo := rec X. get (b : Bit) on (get (n : Nat) (put n X)) done
           conform client : echo-back := put b0 (put 1 (get (m : Nat) (put b1 done)))
           meet wire : server with client
           def kept : run Nat := 0
           """) == :ok

    assert {:ok, book} = Parser.parse("session loop := rec X. recv Nat (send Nat X)\n")
    loop = Enum.find(book, &(&1.name == "loop"))

    assert Session.show_proto(loop.proto) == "rec X. recv Nat (send Nat X)"

    assert Session.show_proto(Session.dual(loop.proto)) ==
             "rec X. send Nat (recv Nat X)"

    assert Session.dual(Session.dual(loop.proto)) == loop.proto
  end

  test "a recursion variable guarded by a later action is one loop" do
    assert check("""
           session flat := rec X. rec Y. send Nat X
           conform once : flat := rec X. rec Y. put 1 X
           session nest := rec X. send Nat (rec Y. recv Nat X)
           session back := dual nest
           conform reply : nest := rec X. put 1 (rec Y. get Nat X)
           conform ask : back := rec A. get Nat (rec B. put 0 A)
           meet w : reply with ask
           session sized := rec X. recv (n : Nat) (send (Vec Nat n) X)
           conform give : sized := rec X. get (n : Nat) (put (rep n 0) X)
           session outer := recv (n : Nat) (rec X. send (Vec Nat n) X)
           conform hold : outer := get (n : Nat) (rec X. put (rep n 0) X)
           """) == :ok
  end

  test "an unused rec is the body, and a jump is not a finished leaf" do
    assert check("""
           session closed := rec X. end
           conform finished : closed := rec X. done
           session %1 closed-lin := rec X. end
           conform finished-lin : closed-lin := done
           """) == :ok

    assert {:error, msg} =
             check("""
             session %1 loop := rec X. recv Nat (send Nat X)
             conform spins : loop := rec X. get (n : Nat) (put n X)
             """)

    assert msg =~ "linear channel abandoned"
    refute msg =~ "does not conform"
    refute msg =~ "unguarded"
  end

  test "unguarded recursion, an unknown session, and a free process variable are refused" do
    assert {:error, msg} = check("session bad := rec X. X\n")
    assert msg =~ "unguarded recursion"

    assert {:error, msg} = check("session bad := rec X. rec Y. X\n")
    assert msg =~ "unguarded recursion"

    assert {:error, msg} = check("session bad := rec X. rec Y. Y\n")
    assert msg =~ "unguarded recursion"

    assert {:error, msg} = check("session bad := X\n")
    assert msg =~ "unknown session X"

    assert {:error, msg} = check("session bad := rec X. send Nat Y\n")
    assert msg =~ "unknown session Y"

    assert {:error, msg} =
             check("""
             session ping := rec X. end
             conform bad : ping := rec X. X
             """)

    assert msg =~ "unguarded recursion"

    assert {:error, msg} =
             check("""
             session ping := end
             conform bad : ping := X
             """)

    assert msg =~ "free session variable X"

    assert {:error, msg} =
             check("""
             session loop := rec X. recv Nat (send Nat X)
             conform bad : loop := rec X. get (n : Nat) (put X X)
             """)

    assert msg =~ "unbound variable X"
  end

  test "rec stays an identifier outside a session" do
    assert check("""
           def rec : run Nat := 0
           def end : run Nat := 0
           def send : run Nat := 0
           """) == :ok
  end

  test "a declared data type is a payload, and so is its dual" do
    src = """
    data Bool : Type where
      true : Bool
      false : Bool

    data Maybe (A : Type) : Type where
      nothing : Maybe A
      just : A → Maybe A

    data List (A : Type) : Type where
      nil : List A
      cons : A → List A → List A

    data Either (A : Type) (B : Type) : Type where
      left : A → Either A B
      right : B → Either A B

    data Tree : Type where
      leaf : Tree
      node : Tree → Tree → Tree

    session flag := send Bool end
    session flag-back := dual flag
    conform up : flag := put true done
    conform down : flag-back := get Bool done
    meet flag-wire : up with down

    session opt := send (Maybe Nat) end
    session opt-back := dual opt
    conform some : opt := put (just 0) done
    conform none-p : opt := put nothing done
    conform take : opt-back := get (Maybe Nat) done
    meet opt-wire : some with take

    session nums := send (List Nat) end
    conform empty : nums := put nil done
    conform grown : nums := put (cons 0 (cons 0 nil)) done

    session sum := send (Either Nat Bit) end
    conform on-left : sum := put (left 0) done
    conform on-right : sum := put (right b0) done

    session trees := send Tree end
    conform twig : trees := put (node leaf leaf) done

    session echo := recv Bool (send Bool end)
    conform echoer : echo := get (k : Bool) (put k done)
    conform shadow : echo := get (true : Bool) (put true done)
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    flag = Enum.find(book, &(&1.name == "flag"))
    assert flag.proto == {:send, {:dat, "Bool", []}, :end}
    assert Session.dual(flag.proto) == {:recv, {:dat, "Bool", []}, :end}
    assert Session.proto_ok(flag.proto, book) == :ok
    assert Session.proto_ok(Session.dual(flag.proto), book) == :ok

    opt = Enum.find(book, &(&1.name == "opt"))
    assert opt.proto == {:send, {:dat, "Maybe", [:nat]}, :end}
    assert Session.proto_ok(opt.proto, book) == :ok
    assert Session.proto_ok(Session.dual(opt.proto), book) == :ok

    up = Enum.find(book, &(&1.name == "up"))
    down = Enum.find(book, &(&1.name == "down"))
    some = Enum.find(book, &(&1.name == "some"))
    assert Session.skel(up.proc) == {:say, {:var, true}, :finish}
    assert Session.carry(up.proc, book) == {:say, true, :finish}
    assert Session.carry(some.proc, book) == {:say, {:just, 0}, :finish}

    assert Session.carry(Enum.find(book, &(&1.name == "grown")).proc, book) ==
             {:say, {:cons, 0, {:cons, 0, nil}}, :finish}

    assert Muro.Meet.meets(up.proc, down.proc, book) == :ok
    assert Muro.Meet.meets(some.proc, Enum.find(book, &(&1.name == "take")).proc, book) == :ok
  end

  test "a constructor that does not inhabit the payload is refused" do
    src = """
    data Bool : Type where
      true : Bool
      false : Bool

    data Maybe (A : Type) : Type where
      nothing : Maybe A
      just : A → Maybe A

    data Either (A : Type) (B : Type) : Type where
      left : A → Either A B
      right : B → Either A B

    session flag := send Bool end
    session flag-back := dual flag
    conform up : flag := put true done
    conform down : flag-back := get Bool done
    conform miss : flag := put (just 0) done
    conform wrong-atom : flag := put nothing done
    session opt := send (Maybe Nat) end
    conform bad-maybe : opt := put (just b0) done
    conform bad-right : sum := put (right 0) done
    session sum := send (Either Nat Bit) end
    """

    assert {:error, msg} = check(src)
    assert msg =~ "put (just 0) done does not conform to send Bool end"
    assert msg =~ "put nothing done does not conform to send Bool end"
    assert msg =~ "put (just b0) done does not conform to send (Maybe Nat) end"
    assert msg =~ "put (right 0) done does not conform to send (Either Nat Bit) end"

    assert {:ok, book} = Parser.parse(src)
    down = Enum.find(book, &(&1.name == "down"))
    miss = Enum.find(book, &(&1.name == "miss"))
    assert {:error, meet} = Muro.Meet.meets(miss.proc, down.proc, book)
    assert meet =~ "diverged: left: put (just 0); right: get Bool"
  end

  test "an indexed declaration, an atom, and a computed put stay refused" do
    assert {:error, msg} =
             check("""
             session atom := send Atom end
             """)

    assert msg =~ "ill-formed payload"

    assert {:error, msg} =
             check("""
             data Fin : Nat → Type where
               fzero : Π (n : Nat) → Fin suc(n)
               fsuc : Π (n : Nat) → Fin n → Fin suc(n)

             session fin := send Fin end
             """)

    assert msg =~ "ill-formed payload"

    assert {:error, msg} =
             check("""
             data Count (n : Nat) : Type where
               counted : Count n

             session count := send Count end
             """)

    assert msg =~ "ill-formed payload"

    assert {:error, msg} =
             check("""
             data Fun : Type where
               wrap : (Nat → Nat) → Fun

             session fun := send Fun end
             """)

    assert msg =~ "ill-formed payload"

    assert {:error, msg} =
             check("""
             data Hide : Type where
               pack : Π (- n : Nat) → Hide

             session hidden := send Hide end
             """)

    assert msg =~ "ill-formed payload"

    assert {:error, msg} =
             check("""
             session nums := send Nat end
             conform computed : nums := put (suc 0) done
             conform added : nums := put (plus 0 0) done
             """)

    assert msg =~ "unbound variable suc"
    assert msg =~ "unbound variable plus"

    assert {:error, msg} =
             Parser.parse("""
             data Bool : Type where
               true : Bool
               false : Bool

             session route := recv (b : Bool) on end end
             """)

    assert msg =~ "a next action is chosen by a bit"
  end

  test "a declared data payload inside rec checks, dualises, and meets" do
    src = """
    data Bool : Type where
      true : Bool
      false : Bool

    data Maybe (A : Type) : Type where
      nothing : Maybe A
      just : A → Maybe A

    session flags := rec X. send Bool X
    session flags-back := dual flags
    conform up : flags := rec X. put true X
    conform down : flags-back := rec Y. get Bool Y
    meet flag-loop : up with down
    """

    assert check(src) == :ok
    assert {:ok, book} = Parser.parse(src)
    flags = Enum.find(book, &(&1.name == "flags"))
    assert Session.show_proto(flags.proto) == "rec X. send Bool X"
    assert Session.show_proto(Session.dual(flags.proto)) == "rec X. recv Bool X"
    assert Session.dual(Session.dual(flags.proto)) == flags.proto
    assert Session.proto_ok(flags.proto, book) == :ok
    assert Session.proto_ok(Session.dual(flags.proto), book) == :ok

    up = Enum.find(book, &(&1.name == "up"))
    down = Enum.find(book, &(&1.name == "down"))
    assert Session.carry(up.proc, book) == {:loop, :X, {:say, true, {:jump, :X}}}
    assert Muro.Meet.meets(up.proc, down.proc, book) == :ok

    assert {:error, msg} =
             check("""
             data Bool : Type where
               true : Bool
               false : Bool

             data Maybe (A : Type) : Type where
               nothing : Maybe A
               just : A → Maybe A

             session flags := rec X. send Bool X
             conform bad : flags := rec X. put (just 0) X
             """)

    assert msg =~ "put (just 0) X does not conform to send Bool X"

    assert {:ok, bad_book} =
             Parser.parse("""
             data Bool : Type where
               true : Bool
               false : Bool

             data Maybe (A : Type) : Type where
               nothing : Maybe A
               just : A → Maybe A

             session flags := rec X. send Bool X
             session flags-back := dual flags
             conform bad : flags := rec X. put (just 0) X
             conform down : flags-back := rec Y. get Bool Y
             """)

    bad = Enum.find(bad_book, &(&1.name == "bad"))
    down = Enum.find(bad_book, &(&1.name == "down"))
    assert {:error, meet} = Muro.Meet.meets(bad.proc, down.proc, bad_book)
    assert meet =~ "diverged: left: put (just 0); right: get Bool"
  end

  test "a computed put and a match on the received value check, dualise, and meet" do
    src = """
    data Item : Type where
      self : Item
      other : Item

    data Bool : Type where
      true : Bool
      false : Bool

    data Maybe (A : Type) : Type where
      nothing : Maybe A
      just : A → Maybe A

    def mark : run Π (f : Item) → Bool :=
      λ (f : Item) →
        match f motive (λ _ → Bool)
          | self => true
          | other => false

    def effective : run Π (+ f : Item) → Maybe Bool :=
      λ (+ f : Item) →
        match f motive (λ _ → Maybe Bool)
          | self => just (mark f)
          | other => nothing

    def id : run Π (n : Nat) → Nat :=
      λ (n : Nat) → n

    def bump : run Π (n : Nat) → Nat :=
      λ (n : Nat) → suc (id n)

    def count : run Nat := suc 0

    def size : run Π (f : Item) → Nat :=
      λ (f : Item) →
        match f motive (λ _ → Nat)
          | self => 0
          | other => suc (suc 0)

    def eq : evidence {0 ≡ 0 : Nat} := refl

    def bad : run Π (f : Item) → Bool :=
      λ (f : Item) → true

    session answer := send (Maybe Bool) end
    session answer-back := dual answer
    conform reply : answer := put (effective self) done
    conform other-reply : answer := put (effective other) done
    conform hear : answer-back := get (Maybe Bool) done
    meet reply-wire : reply with hear
    meet other-wire : other-reply with hear

    session nums := send Nat end
    session nums-back := dual nums
    conform counted : nums := put count done
    conform bumped : nums := put (bump 0) done
    conform hear-num : nums-back := get Nat done

    session cap := send (d : Nat) {d ≤ 1} end
    session cap-back := dual cap
    conform under : cap := put (size self) done
    conform hear-cap : cap-back := get (d : Nat) done
    meet cap-wire : under with hear-cap

    session flags := rec X. send (Maybe Bool) X
    session flags-back := dual flags
    conform loop : flags := rec X. put (effective self) X
    conform loop-back : flags-back := rec Y. get (m : Maybe Bool) Y
    meet loop-wire : loop with loop-back

    session choice := recv Bit (choose end (send Nat end))
    session offered := dual choice
    conform taker : choice := get (b : Bit) (match b pick0 done pick1 (put 0 done))
    conform giver : offered := put b0 (cover done (get Nat done))
    conform giver-one : offered := put b1 (cover done (get Nat done))
    meet arm0 : taker with giver
    meet arm1 : taker with giver-one

    session flag := recv Bool (choose end (send Nat end))
    session flag-back := dual flag
    conform flag-taker : flag := get (b : Bool) (match b pick0 done pick1 (put 1 done))
    conform flag-yes : flag-back := put true (cover done (get Nat done))
    conform flag-no : flag-back := put false (cover done (get Nat done))
    meet flag-yes-wire : flag-taker with flag-yes
    meet flag-no-wire : flag-taker with flag-no

    session opt := recv (Maybe Nat) end
    session opt-back := dual opt
    conform opt-taker : opt := get (m : Maybe Nat) (match m stop done)
    conform opt-none : opt-back := put nothing stop
    conform opt-some : opt-back := put (just 0) done
    meet opt-none-wire : opt-taker with opt-none
    meet opt-some-wire : opt-taker with opt-some

    session %1 closed := send (Maybe Bool) end
    conform finished : closed := put (effective self) done
    session %1 choice-done := recv Bit (choose end end)
    conform both-done : choice-done := get (b : Bit) (match b pick0 done pick1 done)

    def pass : (s : answer) ⊸ answer := λ¹ (s : answer) → s
    """

    assert check(src) == :ok
    assert {:ok, book} = Parser.parse(src)

    answer = Enum.find(book, &(&1.name == "answer"))
    assert Session.show_proto(Session.dual(answer.proto)) == "recv (Maybe Bool) end"
    assert Session.dual(Session.dual(answer.proto)) == answer.proto

    reply = Enum.find(book, &(&1.name == "reply"))
    other_reply = Enum.find(book, &(&1.name == "other-reply"))
    hear = Enum.find(book, &(&1.name == "hear"))
    assert Session.carry(reply.proc, book) == {:say, {:just, true}, :finish}
    assert Session.carry(other_reply.proc, book) == {:say, :nothing, :finish}
    assert Muro.Meet.meets(reply.proc, hear.proc, book) == :ok
    assert Muro.Meet.meets(hear.proc, reply.proc, book) == :ok
    assert Muro.Meet.meets(other_reply.proc, hear.proc, book) == :ok
    assert Muro.Meet.meets(hear.proc, other_reply.proc, book) == :ok
    assert Muro.Meet.meet_mult(:lin, reply.proc, hear.proc, book) == :ok

    counted = Enum.find(book, &(&1.name == "counted"))
    bumped = Enum.find(book, &(&1.name == "bumped"))
    hear_num = Enum.find(book, &(&1.name == "hear-num"))
    under = Enum.find(book, &(&1.name == "under"))
    hear_cap = Enum.find(book, &(&1.name == "hear-cap"))
    assert Session.carry(counted.proc, book) == {:say, 1, :finish}
    assert Session.carry(bumped.proc, book) == {:say, 1, :finish}
    assert Session.carry(under.proc, book) == {:say, 0, :finish}
    assert Muro.Meet.meets(counted.proc, hear_num.proc, book) == :ok
    assert Muro.Meet.meets(bumped.proc, hear_num.proc, book) == :ok
    assert Muro.Meet.meets(hear_num.proc, bumped.proc, book) == :ok
    assert Muro.Meet.meets(under.proc, hear_cap.proc, book) == :ok
    assert Muro.Meet.meets(hear_cap.proc, under.proc, book) == :ok

    flags = Enum.find(book, &(&1.name == "flags"))
    assert Session.show_proto(Session.dual(flags.proto)) == "rec X. recv (Maybe Bool) X"
    loop = Enum.find(book, &(&1.name == "loop"))
    loop_back = Enum.find(book, &(&1.name == "loop-back"))
    assert Session.carry(loop.proc, book) == {:loop, :X, {:say, {:just, true}, {:jump, :X}}}
    assert Muro.Meet.meets(loop.proc, loop_back.proc, book) == :ok
    assert Muro.Meet.meets(loop_back.proc, loop.proc, book) == :ok

    choice = Enum.find(book, &(&1.name == "choice"))
    assert Session.show_proto(choice.proto) == "recv Bit (choose end (send Nat end))"

    assert Session.show_proto(Session.dual(choice.proto)) ==
             "send Bit (branch end (recv Nat end))"

    taker = Enum.find(book, &(&1.name == "taker"))
    giver = Enum.find(book, &(&1.name == "giver"))
    giver_one = Enum.find(book, &(&1.name == "giver-one"))
    assert Muro.Meet.meets(taker.proc, giver.proc, book) == :ok
    assert Muro.Meet.meets(giver.proc, taker.proc, book) == :ok
    assert Muro.Meet.meets(taker.proc, giver_one.proc, book) == :ok
    assert Muro.Meet.meets(giver_one.proc, taker.proc, book) == :ok
    assert Muro.Meet.meet_mult(:lin, taker.proc, giver.proc, book) == :ok

    flag_taker = Enum.find(book, &(&1.name == "flag-taker"))
    flag_yes = Enum.find(book, &(&1.name == "flag-yes"))
    flag_no = Enum.find(book, &(&1.name == "flag-no"))
    assert Muro.Meet.meets(flag_taker.proc, flag_yes.proc, book) == :ok
    assert Muro.Meet.meets(flag_yes.proc, flag_taker.proc, book) == :ok
    assert Muro.Meet.meets(flag_taker.proc, flag_no.proc, book) == :ok
    assert Muro.Meet.meets(flag_no.proc, flag_taker.proc, book) == :ok

    opt_taker = Enum.find(book, &(&1.name == "opt-taker"))
    opt_none = Enum.find(book, &(&1.name == "opt-none"))
    opt_some = Enum.find(book, &(&1.name == "opt-some"))
    assert Muro.Meet.meets(opt_taker.proc, opt_none.proc, book) == :ok
    assert Muro.Meet.meets(opt_none.proc, opt_taker.proc, book) == :ok
    assert Muro.Meet.meets(opt_taker.proc, opt_some.proc, book) == :ok
    assert Muro.Meet.meets(opt_some.proc, opt_taker.proc, book) == :ok

    # b0 takes done, which meets done. The abandoned arm is still consumed.
    stopped = {:get, :bit, :b, {:match, :b, [:done, :stop]}}
    sent0 = {:put, :bit, :b0, :done}
    assert Muro.Meet.meets(stopped, sent0, book) == :ok
    assert {:error, lin} = Muro.Meet.meet_mult(:lin, stopped, sent0, book)
    assert lin =~ "linear endpoint not consumed: left"

    # The value that was computed does not inhabit the payload.
    assert {:error, msg} =
             check("""
             data Item : Type where
               self : Item

             data Bool : Type where
               true : Bool
               false : Bool

             data Maybe (A : Type) : Type where
               nothing : Maybe A
               just : A → Maybe A

             def bad : run Π (f : Item) → Bool :=
               λ (f : Item) → true

             def wrong : run Π (f : Item) → Maybe Bool :=
               λ (f : Item) → nothing

             def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
               λ (n : Nat) → λ (m : Nat) → n

             def eq : evidence {0 ≡ 0 : Nat} := refl
             def ghost : spec Type := Nat

             session answer := send (Maybe Bool) end
             conform miss : answer := put (bad self) done
             session flag := send Bool end
             conform miss-bool : flag := put (wrong self) done
             session nums := send Nat end
             conform open : nums := put (plus n 0) done
             conform bare : nums := put plus done
             conform proof : nums := put eq done
             conform applied : nums := put (eq 0) done
             conform specced : nums := put ghost done
             conform successor : nums := put (suc 0) done
             """)

    assert msg =~ "put (bad self) done does not conform to send (Maybe Bool) end"
    assert msg =~ "put (wrong self) done does not conform to send Bool end"
    assert msg =~ "unbound variable n"
    assert msg =~ "put plus done does not conform to send Nat end"
    assert msg =~ "proof: evidence is not a value"
    assert msg =~ "applied: evidence is not a value"
    assert msg =~ "ghost is not a run definition"
    assert msg =~ "unbound variable suc"

    assert {:ok, miss_book} =
             Parser.parse("""
             data Item : Type where
               self : Item

             data Bool : Type where
               true : Bool
               false : Bool

             data Maybe (A : Type) : Type where
               nothing : Maybe A
               just : A → Maybe A

             def bad : run Π (f : Item) → Bool :=
               λ (f : Item) → true

             session answer := send (Maybe Bool) end
             session answer-back := dual answer
             conform miss : answer := put (bad self) done
             conform hear : answer-back := get (Maybe Bool) done
             """)

    miss = Enum.find(miss_book, &(&1.name == "miss"))
    hear = Enum.find(miss_book, &(&1.name == "hear"))
    assert {:error, meet} = Muro.Meet.meets(miss.proc, hear.proc, miss_book)

    assert meet =~
             "diverged: left: put (bad self); right: get (Maybe Bool): computed value true does not inhabit Maybe Bool"

    assert {:error, meet} = Muro.Meet.meets(hear.proc, miss.proc, miss_book)
    assert meet =~ "diverged: left: get (Maybe Bool); right: put (bad self)"

    # An argument that is not a value is not computed.
    assert {:error, msg} =
             check("""
             def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
               λ (n : Nat) → λ (m : Nat) →
                 match n motive (λ _ → Nat)
                   | 0 => m
                   | suc np => suc(plus np m)

             session echo := recv Nat (send Nat end)
             conform open : echo := get (n : Nat) (put (plus n 0) done)
             """)

    assert msg =~ "put (plus n 0) done does not conform to send Nat end"

    # A definition that calls itself is refused on every argument, including
    # the arm that does not take the call. A call of a later definition is
    # the same refusal. A `let` and a partial application are outside the
    # fragment the meeting evaluates.
    assert {:error, msg} =
             check("""
             def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
               λ (n : Nat) → λ (m : Nat) →
                 match n motive (λ _ → Nat)
                   | 0 => m
                   | suc np => suc (plus np m)

             def early : run Nat := late

             def late : run Nat := 0

             def hop : run Π (n : Nat) → Π (m : Nat) → Nat :=
               λ (n : Nat) → λ (m : Nat) → n

             def dropped : run Nat := let (a, b) = (0, 0) in a

             session nums := send Nat end
             conform zero : nums := put (plus 0 0) done
             conform one : nums := put (plus 1 0) done
             conform fwd : nums := put early done
             conform partial : nums := put (hop 0) done
             conform letbound : nums := put dropped done
             """)

    assert msg =~
             "zero: put (plus 0 0) done does not conform to send Nat end: run definition calls itself"

    assert msg =~
             "one: put (plus 1 0) done does not conform to send Nat end: run definition calls itself"

    assert msg =~
             "fwd: put early done does not conform to send Nat end: run definition declared later"

    assert msg =~ "put (hop 0) done does not conform to send Nat end"
    assert msg =~ "put dropped done does not conform to send Nat end"

    # `size other` computes 2, and 2 is not at most 1.
    assert {:error, msg} =
             check("""
             data Item : Type where
               self : Item
               other : Item

             def size : run Π (f : Item) → Nat :=
               λ (f : Item) →
                 match f motive (λ _ → Nat)
                   | self => 0
                   | other => suc (suc 0)

             session cap := send (d : Nat) {d ≤ 1} end
             conform over : cap := put (size other) done
             """)

    assert msg =~ "put (size other) done does not conform to send (d : Nat) {d ≤ 1} end"

    # The match covers the value the get just bound, one arm per constructor.
    assert {:error, msg} =
             check("""
             data Bool : Type where
               true : Bool
               false : Bool

             data Maybe (A : Type) : Type where
               nothing : Maybe A
               just : A → Maybe A

             session choice := recv Bit (choose end end)
             conform short : choice := get (b : Bit) (match b pick0 done)
             conform third : choice := get (b : Bit) (match b pick0 done pick1 done done)
             conform other : choice := get (b : Bit) (match c pick0 done pick1 done)
             conform later : choice := get (b : Bit) (put b (match b done done))
             conform stray : choice := match b done done
             session nums := recv Nat end
             conform natty : nums := get (n : Nat) (match n done done)
             session box := recv (Nat * Nat) end
             conform paired : box := get (p : Nat * Nat) (match p done done)
             session unit := recv Unit end
             conform united : unit := get (u : Unit) (match u done)
             session row := recv {x : Nat} end
             conform recorded : row := get (r : {x : Nat}) (match r done)
             session vecs := recv (Vec Nat 2) end
             conform vectored : vecs := get (v : Vec Nat 2) (match v done)
             session flag := recv Bool end
             conform short-bool : flag := get (b : Bool) (match b done)
             session opt := recv (Maybe Nat) end
             conform third-opt : opt := get (m : Maybe Nat) (match m done done done)
             session %1 open := recv Bit end
             conform abandoned : open := get (b : Bit) (match b done stop)
             """)

    assert msg =~ "match does not cover the received value"
    assert msg =~ "put b (match b done done) does not conform to choose end end"
    assert msg =~ "linear channel abandoned"

    # A variable selects no arm. The other party does not cover both arms.
    assert {:ok, var_book} =
             Parser.parse("""
             session relay := recv Bit (send Bit (choose end end))
             session relay-back := dual relay
             conform forward : relay := get (c : Bit) (put c (cover done done))
             conform taker : relay-back := put b0 (get (b : Bit) (match b pick0 done pick1 done))
             """)

    forward = Enum.find(var_book, &(&1.name == "forward"))
    var_taker = Enum.find(var_book, &(&1.name == "taker"))
    assert {:error, meet} = Muro.Meet.meets(forward.proc, var_taker.proc, var_book)
    assert meet =~ "the value c does not select an arm"

    # A nat computed where a Bool is received does not inhabit that payload.
    assert {:ok, count_book} =
             Parser.parse("""
             data Bool : Type where
               true : Bool
               false : Bool

             def count : run Nat := 0

             session flag := recv Bool end
             session flag-back := dual flag
             conform taker : flag := get (b : Bool) (match b done done)
             conform counted : flag-back := put count done
             """)

    counted = Enum.find(count_book, &(&1.name == "counted"))
    taker = Enum.find(count_book, &(&1.name == "taker"))
    assert {:error, meet} = Muro.Meet.meets(counted.proc, taker.proc, count_book)

    assert meet ==
             "diverged: left: put count; right: get (b : Bool): computed value 0 does not inhabit Bool"

    assert {:error, meet} = Muro.Meet.meets(taker.proc, counted.proc, count_book)

    assert meet ==
             "diverged: left: get (b : Bool); right: put count: computed value 0 does not inhabit Bool"

    # The crossed arms do not meet: b0 takes the first process.
    assert {:ok, cross_book} =
             Parser.parse("""
             session choice := recv Bit end
             session offered := dual choice
             conform taker : choice := get (b : Bit) (match b done stop)
             conform giver : offered := put b0 stop
             """)

    taker = Enum.find(cross_book, &(&1.name == "taker"))
    giver = Enum.find(cross_book, &(&1.name == "giver"))
    assert {:error, meet} = Muro.Meet.meets(taker.proc, giver.proc, cross_book)
    assert meet =~ "diverged after get b, arm b0: left: done; right: stop"
  end

  test "session-calls.muro checks, and emit keeps the runs" do
    path = "examples/session-calls.muro"
    src = File.read!(path)
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    assert Muro.check_file(path) == :ok

    assert {:ok, out} = Muro.emit_file(path, Calls)
    assert out =~ "kept"
    refute out =~ "session"
    refute out =~ "stream"
  end

  test "a session call opens as its body, and a guarded self-call is a jump" do
    assert {:ok, book} =
             Parser.parse("""
             session ack := send Bit end
             session req := send Nat ack
             session stream (n : Nat) := send (d : Nat) {d ≤ n} (stream (suc n))
             session spin := choose (send Nat spin) end
             session again := rec X. send Nat again
             """)

    assert {:ok, db} = Muro.Ast.book_to_db(book)
    req = Enum.find(db, &(&1.name == "req"))
    assert {:ok, proto} = Session.elaborate(req, db)
    assert proto == {:send, :nat, {:send, :bit, :end}}
    assert Session.dual(proto) == {:recv, :nat, {:recv, :bit, :end}}

    assert {:ok, %{proto: stream}} = Session.open_applied(db, "stream", [{:lit, 0}])

    assert stream == {:esend, :d, {:lit, 0}, {:sjump, "stream", [{:lit, 1}]}}

    assert Session.dual(stream) ==
             {:erecv, :d, {:lit, 0}, {:sjump, {:dual, "stream"}, [{:lit, 1}]}}

    assert check("""
           session ack := send Bit end
           session req := send Nat ack
           session choice := choose ack end
           session route := recv (b : Bit) on ack end
           session loop := rec X. recv Nat (send Nat ack)
           session spin := choose (send Nat spin) end
           conform looped : spin := rec X. pick0 (put 0 X)
           session again := rec X. send Nat again
           conform hops : again := rec Y. put 1 Y
           def pass : (s : req) ⊸ req := λ¹ (s : req) → s
           """) == :ok
  end

  test "a parameterised session, a computed argument, and a data payload check" do
    assert check("""
           def id : run Π (n : Nat) → Nat :=
             λ (n : Nat) → n

           def bump : run Π (n : Nat) → Nat :=
             λ (n : Nat) → suc (id n)

           data Bool : Type where
             true : Bool
             false : Bool

           session flag (k : Nat) := send Bool end
           session flag1 := flag 1
           conform yes : flag1 := put true done
           session frames (k : Nat) := send (Vec Nat k) end
           session three := frames 3
           session counted := frames (bump 0)
           conform send1 : counted := put (rep 1 0) done
           session nums (k : Nat) := send Nat end
           conform bumped : nums (bump 0) := put (bump 0) done
           session rest (n : Nat) := send (Vec Nat n) end
           session sized := recv (n : Nat) (rest n)
           conform server : sized := get (n : Nat) (put (rep n 0) done)
           def pass : (s : three) ⊸ three := λ¹ (s : three) → s
           place home := ambient
           scheme local := fixed home
           endpoint three-home := three at local
           """) == :ok
  end

  test "an unguarded call, a forward call, an unknown name, and a bad argument are refused" do
    assert {:error, msg} = check("session s := s\n")
    assert msg =~ "unguarded session call"

    assert {:error, msg} =
             check("""
             session a := send Nat b
             session b := end
             """)

    assert msg =~ "session declared later"

    assert {:error, msg} = check("session q := no-such\n")
    assert msg =~ "unknown session no-such"

    assert {:error, msg} =
             check("""
             session frames (k : Nat) := send (Vec Nat k) end
             session bad := frames
             session two := frames 1 2
             """)

    assert msg =~ "wrong number of session arguments"

    assert {:error, msg} =
             check("""
             def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
               λ (n : Nat) → λ (m : Nat) → plus n m

             def early : run Nat := late

             def late : run Nat := 0

             session frames (k : Nat) := end
             session bad-plus := frames (plus 0 0)
             session bad-early := frames early
             session bad-name := frames nope
             """)

    assert msg =~ "argument (plus 0 0): run definition calls itself"
    assert msg =~ "argument early: run definition declared later"
    assert msg =~ "argument nope is not a nat"

    assert {:error, msg} = Parser.parse("session bad (b : Bit) := end\n")
    assert msg =~ "a session parameter is a nat"

    assert {:error, msg} =
             check("""
             session w (n : Nat) := send (d : Nat) {d ≤ n} end
             conform over : w 0 := put 1 done
             """)

    assert msg =~ "put 1 done does not conform to send (d : Nat) {d ≤ 0} end"

    assert {:error, msg} =
             check("""
             session shrink (n : Nat) := send (d : Nat) {d ≤ n} (shrink 0)
             conform shrinks : shrink 5 := rec X. put 5 X
             """)

    assert msg =~ "d ≤ 0"

    assert {:error, msg} =
             check("""
             session grow (n : Nat) := send (Vec Nat n) (grow (suc n))
             conform grows : grow 0 := rec X. put (rep 0 0) X
             """)

    assert msg =~ "send (Vec Nat 1)"

    assert {:error, msg} =
             check("""
             session stream (n : Nat) := send (d : Nat) {d ≤ n} (stream (suc n))
             session stream0 := stream 0
             session mirror := rec X. recv (d : Nat) X
             conform up : stream0 := rec X. put 0 X
             conform down : mirror := rec Y. get (d : Nat) Y
             meet bad : up with down
             """)

    assert msg =~ "diverged"

    assert {:error, _} = Parser.parse("session c := choose ack (frames 3)\n")

    assert check("""
           session ack := send Bit end
           session frames (k : Nat) := end
           session c := choose (ack) (frames 3)
           """) == :ok
  end

  test "value-protocols.muro checks, and a case dualises arm by arm" do
    path = "examples/value-protocols.muro"
    src = File.read!(path)
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    assert Muro.check_file(path) == :ok

    assert {:ok, db} = Muro.Ast.book_to_db(book)
    srv = Enum.find(db, &(&1.name == "srv"))
    assert {:ok, proto} = Session.elaborate(srv, db)

    assert proto ==
             {:drecv, :f, {:dat, "Frame", []},
              {:case, {:name, :f},
               [
                 {"bytes", {:send, :bit, :end}},
                 {"trailers", :end},
                 {"headers", :end}
               ]}}

    assert Session.dual(Session.dual(proto)) == proto

    assert Session.dual(proto) ==
             {:dsend, :f, {:dat, "Frame", []},
              {:case, {:name, :f},
               [
                 {"bytes", {:recv, :bit, :end}},
                 {"trailers", :end},
                 {"headers", :end}
               ]}}

    gate = Enum.find(db, &(&1.name == "gate"))
    assert {:ok, late} = Session.elaborate(gate, db)

    assert late ==
             {:drecv, :f, {:dat, "Frame", []},
              {:case, {:run, "late", :f},
               [
                 {"true", {:send, {:dat, "Ctl", []}, :end}},
                 {"false", {:send, {:dat, "Goaway", []}, :end}}
               ]}}

    assert Session.dual(Session.dual(late)) == late
  end

  test "a receiver may abandon a case, and a concrete sender follows one arm" do
    assert check("""
           data Frame : Type where
             bytes : Frame
             trailers : Frame
             headers : Frame

           data Ctl : Type where
             rst : Ctl

           session server :=
             recv (f : Frame) (case f
               | bytes => send Ctl end
               | trailers => end
               | headers => end)
           conform leave : server := get (f : Frame) stop
           conform one : server := get (f : Frame) (match f (put rst done) done done)
           """) == :ok
  end

  test "a run that reads a field accepts the protocol and a concrete sender" do
    assert check("""
           data Bool : Type where
             true : Bool
             false : Bool

           data Maybe (A : Type) : Type where
             nothing : Maybe A
             just : A → Maybe A

           def onJust : run Π (m : Maybe Bool) → Bool :=
             λ (m : Maybe Bool) →
               match m motive (λ _ → Bool)
                 | nothing => false
                 | just b => true

           session peek :=
             recv (m : Maybe Bool) (case (onJust m)
               | true => end
               | false => send Bool end)
           session peek-back := dual peek
           conform none : peek-back := put nothing (get Bool done)
           conform some : peek-back := put (just true) done
           """) == :ok
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

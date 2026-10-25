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

  test "unguarded recursion and a free session variable are refused" do
    assert {:error, msg} = check("session bad := rec X. X\n")
    assert msg =~ "unguarded recursion"

    assert {:error, msg} = check("session bad := rec X. rec Y. X\n")
    assert msg =~ "unguarded recursion"

    assert {:error, msg} = check("session bad := rec X. rec Y. Y\n")
    assert msg =~ "unguarded recursion"

    assert {:error, msg} = check("session bad := X\n")
    assert msg =~ "free session variable X"

    assert {:error, msg} = check("session bad := rec X. send Nat Y\n")
    assert msg =~ "free session variable Y"

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
    assert meet =~ "put (just 0) done does not meet get Bool done"
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
    assert meet =~ "put (just 0) X does not meet get Bool Y"
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

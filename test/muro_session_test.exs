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

  test "a repeated field and a payload that is not a type are refused" do
    assert {:error, msg} = Parser.parse("session box := send {x : Nat, x : Bit} end\n")
    assert msg =~ "duplicate field x"

    assert {:error, msg} = Parser.parse("session box := send String end\n")
    assert msg =~ "expected a payload"
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

  test "value binding: parse get with binder" do
    src =
      "conform test : ping := get (k : Nat) (put k done)\nsession ping := recv Nat (send Nat end)\n"

    assert {:ok, book} = Parser.parse(src)
    [conform | _] = book
    assert conform.kind == :conform
    assert {:get, :nat, :k, _} = conform.proc
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

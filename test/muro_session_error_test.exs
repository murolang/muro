defmodule Muro.SessionErrorTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, Meet, Parser, Print}

  test "a conform refusal points at the put, not the definition" do
    assert {:error, msg} =
             check("""
             session ping := recv Nat end
             conform bad : ping :=
               put b0 done
             """)

    assert msg == "3:3: bad: put b0 done does not conform to recv Nat end"
  end

  test "a put inside rec points at that put" do
    assert {:error, msg} =
             check("""
             session nums := rec X. send Nat X
             conform bad : nums :=
               rec X. put b0 X
             """)

    assert msg == "3:10: bad: put b0 X does not conform to send Nat X"
  end

  test "a put after a session call points at that put" do
    assert {:error, msg} =
             check("""
             session ack := send Bit end
             session req := send Nat ack
             conform bad : req :=
               put 1 (put 1 done)
             """)

    assert msg == "4:10: bad: put 1 done does not conform to send Bit end"
  end

  test "a parameterised session names the instantiated bound" do
    assert {:error, msg} =
             check("""
             session w (n : Nat) := send (d : Nat) {d ≤ n} end
             conform over : w 0 :=
               put 1 done
             """)

    assert msg ==
             "3:3: over: put 1 done does not conform to send (d : Nat) {d ≤ 0} end: value 1 misses bound ≤ 0"
  end

  test "a computed value that misses a bound names both" do
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
             conform over : cap :=
               put (size other) done
             """)

    assert msg ==
             "13:3: over: put (size other) done does not conform to send (d : Nat) {d ≤ 1} end: computed value 2 misses bound ≤ 1"
  end

  test "a computed value that does not inhabit names the value and the type" do
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

             session answer := send (Maybe Bool) end
             conform miss : answer :=
               put (bad self) done
             """)

    assert msg ==
             "17:3: miss: put (bad self) done does not conform to send (Maybe Bool) end: computed value true does not inhabit Maybe Bool"
  end

  test "a run that calls itself is not an unbound name" do
    assert {:error, msg} =
             check("""
             def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
               λ (n : Nat) → λ (m : Nat) →
                 match n motive (λ _ → Nat)
                   | 0 => m
                   | suc np => suc (plus np m)

             session nums := send Nat end
             conform zero : nums :=
               put (plus 0 0) done
             """)

    assert msg ==
             "9:3: zero: put (plus 0 0) done does not conform to send Nat end: run definition calls itself"

    refute msg =~ "unbound variable"
  end

  test "a run declared later is not a self-call" do
    assert {:error, msg} =
             check("""
             def early : run Nat := late

             def late : run Nat := 0

             session nums := send Nat end
             conform fwd : nums :=
               put early done
             """)

    assert msg ==
             "7:3: fwd: put early done does not conform to send Nat end: run definition declared later"
  end

  test "partial application, let, a remaining λ, a record, and a vector say which fragment" do
    assert {:error, msg} =
             check("""
             def hop : run Π (n : Nat) → Π (m : Nat) → Nat :=
               λ (n : Nat) → λ (m : Nat) → n

             def dropped : run Nat := let (a, b) = (0, 0) in a

             def apply : run Π (n : Nat) → Nat :=
               λ (n : Nat) → (λ (x : Nat) → x) n

             def idn : run Π (n : Nat) → Nat :=
               λ (n : Nat) → n

             session nums := send Nat end
             conform partial : nums :=
               put (hop 0) done
             conform letbound : nums :=
               put dropped done
             conform lam : nums :=
               put (apply 0) done
             conform recorded : nums :=
               put (idn {x = 0}) done
             conform vectored : nums :=
               put (idn (rep 1 0)) done
             """)

    assert msg =~
             "partial: put (hop 0) done does not conform to send Nat end: outside the computed fragment: partial application"

    assert msg =~
             "letbound: put dropped done does not conform to send Nat end: outside the computed fragment: let"

    assert msg =~
             "lam: put (apply 0) done does not conform to send Nat end: outside the computed fragment: λ"

    assert msg =~
             "recorded: put (idn {x = 0}) done does not conform to send Nat end: outside the computed fragment: record"

    assert msg =~
             "vectored: put (idn rep 1 0) done does not conform to send Nat end: outside the computed fragment: vector"
  end

  test "an open argument is not a value, and evidence is not a value" do
    assert {:error, msg} =
             check("""
             def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
               λ (n : Nat) → λ (m : Nat) → n

             def eq : evidence {0 ≡ 0 : Nat} := refl

             session echo := recv Nat (send Nat end)
             conform open : echo :=
               get (n : Nat) (put (plus n 0) done)
             session nums := send Nat end
             conform proof : nums :=
               put eq done
             """)

    assert msg =~
             "open: put (plus n 0) done does not conform to send Nat end: argument is not a value"

    assert msg =~ "proof: evidence is not a value"
    refute msg =~ "unbound variable"
  end

  test "only a missing name is an unbound variable, at the put" do
    assert {:error, msg} =
             check("""
             session nums := send Nat end
             conform bad : nums :=
               put m done
             """)

    assert msg == "3:3: bad: unbound variable m"
  end

  test "a value-chosen match diverges on the arm the value selects" do
    assert {:error, msg} =
             check("""
             session choice := recv Bit end
             session offered := dual choice
             conform taker : choice :=
               get (b : Bit) (match b done stop)
             conform giver : offered :=
               put b0 stop
             meet arm : taker with giver
             """)

    assert msg =~
             "arm: diverged after get b, arm b0: left: done; right: stop; protocol: end"

    refute msg =~ "does not conform"
  end

  test "a choice label mismatch names the two arms" do
    assert {:error, msg} = Meet.meets({:pick0, :done}, {:pick1, :done})
    assert msg == "diverged: left: pick0; right: pick1"

    assert {:error, msg} =
             check("""
             session choice := choose end (send Nat end)
             session offered := dual choice
             conform taker : choice :=
               pick1 stop
             conform giver : offered :=
               cover done (get Nat done)
             meet arm : taker with giver
             """)

    assert msg =~
             "arm: diverged after arm pick1: left: stop; right: get Nat; protocol: send Nat end"

    refute msg =~ "does not conform"
  end

  test "done against a pending action is the meeting, and a failed conform is skipped" do
    assert {:error, msg} =
             check("""
             session ping := recv Nat (send Nat end)
             session back := dual ping
             conform pong : ping :=
               get Nat (put 1 done)
             conform early : back :=
               put 0 stop
             meet wire : pong with early
             """)

    assert msg =~ "wire: diverged after put 0: left: put 1; right: stop; protocol: send Nat end"

    assert {:error, msg} =
             check("""
             session ping := recv Nat end
             session back := dual ping
             conform bad : ping :=
               put b0 done
             conform good : back :=
               put 0 done
             meet wire : bad with good
             """)

    assert msg =~ "4:3: bad: put b0 done does not conform to recv Nat end"
    assert msg =~ "wire: skipped because bad does not conform"
    refute msg =~ "diverged"
  end

  test "a linear endpoint that is not consumed names the side" do
    assert {:error, msg} = Meet.meet_mult(:lin, :stop, :stop)
    assert msg == "linear endpoint not consumed: left"
    assert {:error, msg} = Meet.meet_mult(:lin, :done, :stop)
    assert msg == "diverged: left: done; right: stop"
  end

  test "a put and a get of different payloads diverge, and a failed conform is not met again" do
    assert {:error, msg} =
             check("""
             session ping := recv Nat (send Bit end)
             session back := dual ping
             conform pong : ping :=
               get Nat (put b0 done)
             conform peer : back :=
               put 0 (get Nat done)
             meet wire : pong with peer
             """)

    assert msg =~ "6:10: peer: get Nat done does not conform to recv Bit end"
    assert msg =~ "wire: skipped because peer does not conform"
    refute msg =~ "diverged"

    assert {:error, msg} = Meet.meets({:put, :bit, :b0, :done}, {:get, :nat, :_, :done})
    assert msg == "diverged: left: put b0; right: get Nat"
  end

  test "the end of a file is the last line" do
    src = "session ping := recv\n"
    assert {:error, msg} = Parser.parse(src)
    assert msg =~ "unexpected end of file, expected"
    {line, col} = Print.offset_to_loc(src, byte_size(src))
    assert {line, col} == {1, 21}
    assert msg =~ "#{line}:#{col}: "

    src = "session ping :=\nrecv Nat\n"
    assert {:error, msg} = Parser.parse(src)
    assert msg =~ "2:"
    refute msg =~ "3:"
    assert msg =~ "unexpected end of file, expected"
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

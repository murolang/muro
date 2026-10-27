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

  test "an in-flight frame that sends goaway is refused, and the meeting is skipped" do
    assert {:error, msg} =
             check("""
             data Frame : Type where
               bytes : Frame
               trailers : Frame
               headers : Frame

             data Ctl : Type where
               rst : Ctl

             data Goaway : Type where
               goaway : Goaway

             data Body : Type where
               chunk : Body

             data Bool : Type where
               true : Bool
               false : Bool

             def late : run Π (f : Frame) → Bool :=
               λ (f : Frame) →
                 match f motive (λ _ → Bool)
                   | bytes => true
                   | trailers => true
                   | headers => false

             session server :=
               recv (f : Frame) (case f
                 | bytes => send Ctl end
                 | trailers => send Ctl end
                 | headers => recv Body end)
             session client := dual server
             conform inflight-bad : client :=
               put bytes (put goaway done)
             conform stream : server :=
               get (f : Frame) (match f (get Ctl done) (get Ctl done) (get (b : Body) done))
             meet wire : inflight-bad with stream
             """)

    assert msg =~ "inflight-bad: put goaway done does not conform to recv Ctl end"
    assert msg =~ "wire: skipped because inflight-bad does not conform"
    refute msg =~ "diverged"

    assert {:error, msg} =
             check("""
             data Frame : Type where
               bytes : Frame
               trailers : Frame
               headers : Frame

             data Ctl : Type where
               rst : Ctl

             data Goaway : Type where
               goaway : Goaway

             data Bool : Type where
               true : Bool
               false : Bool

             def late : run Π (f : Frame) → Bool :=
               λ (f : Frame) →
                 match f motive (λ _ → Bool)
                   | bytes => true
                   | trailers => true
                   | headers => false

             session gate :=
               recv (f : Frame) (case (late f)
                 | true => send Ctl end
                 | false => send Goaway end)
             conform late-bad : gate :=
               get (f : Frame) (match f (put goaway done) (put rst done) (put goaway done))
             """)

    assert msg =~ "late-bad: put goaway done does not conform to send Ctl end"
  end

  test "a case meeting names the value and the arm" do
    assert {:error, msg} =
             check("""
             data Frame : Type where
               bytes : Frame
               trailers : Frame
               headers : Frame

             data Body : Type where
               chunk : Body

             session server :=
               recv (f : Frame) (case f
                 | bytes => end
                 | trailers => end
                 | headers => recv Body end)
             session client := dual server
             conform stream : server :=
               get (f : Frame) (match f done done (get (b : Body) stop))
             conform open : client :=
               put headers (put chunk done)
             meet wire : stream with open
             meet swap : open with stream
             """)

    assert msg =~
             "wire: diverged after get f, arm headers, put chunk: left: stop; right: done; protocol: end"

    assert msg =~
             "swap: diverged after get f, arm headers, put chunk: left: done; right: stop; protocol: end"

    assert {:error, msg} =
             check("""
             data Frame : Type where
               bytes : Frame
               trailers : Frame
               headers : Frame

             data Ctl : Type where
               rst : Ctl

             session left :=
               recv (f : Frame) (case f
                 | bytes => send Ctl end
                 | trailers => end
                 | headers => end)
             session right :=
               send (f : Frame) (case f
                 | bytes => send Ctl end
                 | trailers => end
                 | headers => end)
             conform a : left :=
               get (f : Frame) (match f (put rst done) done done)
             conform b : right :=
               put bytes (put rst done)
             meet bad : a with b
             """)

    assert msg =~ "arm bytes"
    assert msg =~ "bad: diverged after recv (f : Frame), arm bytes"
  end

  test "a case is refused on the wrong type, the wrong name, and the wrong arms" do
    assert {:error, msg} =
             check("""
             data Frame : Type where
               bytes : Frame
               trailers : Frame
               headers : Frame

             session natty := recv (n : Nat) (case n | bytes => end)
             session paired := recv (p : Nat * Nat) (case p | bytes => end)
             session recorded := recv (r : {x : Nat}) (case r | bytes => end)
             session vectored := recv (v : Vec Nat 2) (case v | bytes => end)
             session united := recv (u : Unit) (case u | bytes => end)
             session early :=
               recv (g : Frame) (recv (f : Frame) (case g
                 | bytes => end
                 | trailers => end
                 | headers => end))
             session bare := case f | bytes => end
             session loose := recv Frame (case f | bytes => end | trailers => end | headers => end)
             session short :=
               recv (f : Frame) (case f
                 | bytes => end
                 | trailers => end)
             session extra :=
               recv (f : Frame) (case f
                 | bytes => end
                 | trailers => end
                 | headers => end
                 | extra => end)
             session order :=
               recv (f : Frame) (case f
                 | headers => end
                 | bytes => end
                 | trailers => end)
             """)

    for name <- ~w(natty paired recorded vectored united) do
      assert msg =~ "#{name}: a case is on a bit or a declared data type"
    end

    assert msg =~ "early: a case is on the name just bound"
    assert msg =~ "bare: a case follows the value just exchanged"
    assert msg =~ "loose: a case follows the value just exchanged"
    assert msg =~ "short: case arms do not match the constructors"
    assert msg =~ "extra: case arms do not match the constructors"
    assert msg =~ "order: case arms do not match the constructors"
  end

  test "a run case is refused when the run is recursive, later, or outside the fragment" do
    assert {:error, msg} =
             check("""
             data Nest : Type where
               tip : Nest
               nest : Nest → Nest

             data Bool : Type where
               true : Bool
               false : Bool

             def walk : run Π (t : Nest) → Bool :=
               λ (t : Nest) →
                 match t motive (λ _ → Bool)
                   | tip => true
                   | nest u => walk u

             session looped :=
               recv (t : Nest) (case (walk t)
                 | true => end
                 | false => end)
             """)

    assert msg =~ "looped: run definition calls itself"

    assert {:error, msg} =
             check("""
             data Frame : Type where
               bytes : Frame
               trailers : Frame
               headers : Frame

             data Bool : Type where
               true : Bool
               false : Bool

             def early : run Π (f : Frame) → Bool :=
               λ (f : Frame) → later

             def later : run Bool := true

             session forwarded :=
               recv (f : Frame) (case (early f)
                 | true => end
                 | false => end)
             """)

    assert msg =~ "forwarded: run definition declared later"

    assert {:error, msg} =
             check("""
             data Frame : Type where
               bytes : Frame
               trailers : Frame
               headers : Frame

             data Bool : Type where
               true : Bool
               false : Bool

             def dropped : run Π (f : Frame) → Bool :=
               λ (f : Frame) → let (a, b) = (true, false) in a

             session letcase :=
               recv (f : Frame) (case (dropped f)
                 | true => end
                 | false => end)
             """)

    assert msg =~ "letcase: outside the computed fragment: let"

    assert {:error, msg} =
             check("""
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
                 | false => end)
             conform bad : peek :=
               get (m : Maybe Bool) (match m done done)
             """)

    assert msg =~
             "bad: get (m : (Maybe Bool)) (match m done done) does not conform to recv (m : Maybe Bool) (case (onJust m) | true => end | false => end): the run does not decide an arm"

    refute msg =~ "peek:"
  end

  test "an unknown sender is refused unless every arm agrees, and the meeting stays refused" do
    assert {:error, msg} =
             check("""
             data Frame : Type where
               bytes : Frame
               trailers : Frame
               headers : Frame

             data Ctl : Type where
               rst : Ctl

             session split :=
               recv (g : Frame) (send (f : Frame) (case f
                 | bytes => send Ctl end
                 | trailers => end
                 | headers => end))
             conform bad : split :=
               get (g : Frame) (put g done)
             """)

    assert msg =~
             "bad: put g done does not conform to send (f : Frame) (case f | bytes => send Ctl end | trailers => end | headers => end): the value g does not select an arm"

    assert {:error, msg} =
             check("""
             data Frame : Type where
               bytes : Frame
               trailers : Frame
               headers : Frame

             session relay :=
               recv (g : Frame) (send (f : Frame) (case f
                 | bytes => end
                 | trailers => end
                 | headers => end))
             session back := dual relay
             conform relayed : relay :=
               get (g : Frame) (put g done)
             conform hear : back :=
               put headers (get (f : Frame) (match f done done done))
             meet wire : relayed with hear
             """)

    assert msg =~ "the value g does not select an arm"
    refute msg =~ "relayed: "
    refute msg =~ "hear: "

    assert {:error, msg} =
             check("""
             data Frame : Type where
               bytes : Frame
               trailers : Frame
               headers : Frame

             session server :=
               recv (f : Frame) (case f
                 | bytes => end
                 | trailers => end
                 | headers => end)
             conform short : server :=
               get (f : Frame) (match f done done)
             conform other : server :=
               get (f : Frame) (match g done done done)
             conform closed : server :=
               get (f : Frame) done
             session %1 once :=
               recv (f : Frame) (case f
                 | bytes => end
                 | trailers => end
                 | headers => end)
             conform abandoned : once :=
               get (f : Frame) (match f stop done done)
             """)

    assert msg =~
             "short: get (f : Frame) (match f done done) does not conform to recv (f : Frame) (case f | bytes => end | trailers => end | headers => end): match does not cover the received value"

    assert msg =~ "other: match does not cover the received value"
    assert msg =~ "closed: done does not conform to case f"
    assert msg =~ "abandoned: linear channel abandoned"

    assert {:error, msg} =
             Parser.parse("""
             data Bool : Type where
               true : Bool
               false : Bool
             session bad := recv (b : Bool) on end end
             """)

    assert msg =~ "a next action is chosen by a bit"
  end

  test "a field binding is refused when the arm, the name, or the put is wrong" do
    prelude = """
    data Bool : Type where
      true : Bool
      false : Bool

    data Maybe (A : Type) : Type where
      nothing : Maybe A
      just : A → Maybe A

    def grant : run Π (b : Bool) → Bool :=
      λ (b : Bool) →
        match b motive (λ _ → Bool)
          | true => true
          | false => false

    session ask := recv (Maybe Bool) (send Bool end)
    """

    assert {:error, msg} =
             check("""
             #{prelude}
             conform short : ask :=
               get (m : Maybe Bool)
                 (match m
                   | nothing => put false done
                   | just => put false done)
             """)

    assert msg =~ "wrong arity"

    assert {:error, msg} =
             check("""
             #{prelude}
             conform extra : ask :=
               get (m : Maybe Bool)
                 (match m
                   | nothing x => put false done
                   | just b => put b done)
             """)

    assert msg =~ "wrong arity"

    assert {:error, msg} =
             check("""
             #{prelude}
             conform loose : ask :=
               get (m : Maybe Bool)
                 (match m
                   | nothing => put false done
                   | just b => put c done)
             """)

    assert msg =~ "unbound variable c"

    assert {:error, msg} =
             check("""
             #{prelude}
             conform wrapped : ask :=
               get (m : Maybe Bool)
                 (match m
                   | nothing => put false done
                   | just b => put (just b) done)
             """)

    assert msg =~ "outside the computed fragment"
    refute msg =~ "outside the computed fragment:"

    assert {:error, msg} =
             check("""
             #{prelude}
             conform nested : ask :=
               get (m : Maybe Bool)
                 (match m
                   | nothing => put false done
                   | just b => put (grant (just b)) done)
             """)

    assert msg =~ "argument is not a value"

    assert {:error, msg} =
             check("""
             #{prelude}
             conform swapped : ask :=
               get (m : Maybe Bool)
                 (match m
                   | just b => put b done
                   | nothing => put false done)
             """)

    assert msg =~ "match does not cover the received value"

    assert {:error, msg} =
             check("""
             #{prelude}
             session nest := recv Bool (recv (Maybe Bool) end)
             conform other : nest :=
               get (k : Bool)
                 (get (m : Maybe Bool)
                   (match k
                     | true => done
                     | false => done))
             """)

    assert msg =~ "match does not cover the received value"

    assert {:error, msg} =
             check("""
             #{prelude}
             session nums := recv (Maybe Bool) (send Nat end)
             conform bad : nums :=
               get (m : Maybe Bool)
                 (match m
                   | nothing => put 0 done
                   | just b => put b done)
             """)

    assert msg =~ "put b done does not conform to send Nat end"
    refute msg =~ "does not inhabit"

    assert {:error, msg} =
             check("""
             #{prelude}
             session nums := recv (Maybe Bool) (send Nat end)
             conform bad : nums :=
               get (m : Maybe Bool)
                 (match m
                   | nothing => put 0 done
                   | just b => put (grant b) done)
             """)

    assert msg =~ "computed value (grant b) does not inhabit Nat"

    assert {:error, msg} =
             check("""
             #{prelude}
             def onJust : run Π (m : Maybe Bool) → Bool :=
               λ (m : Maybe Bool) →
                 match m motive (λ _ → Bool)
                   | nothing => false
                   | just b => true

             session peek :=
               recv (m : Maybe Bool) (case (onJust m)
                 | true => end
                 | false => end)
             conform bad : peek :=
               get (m : Maybe Bool)
                 (match m
                   | nothing => done
                   | just b => done)
             """)

    assert msg =~ "the run does not decide an arm"

    assert {:error, msg} =
             check("""
             data Box : Type where
               box : Π (n : Nat) →
                 Box

             session owed := recv Box (send (d : Nat) {d ≤ 1} end)
             conform over : owed :=
               get (x : Box)
                 (match x
                   | box n => put n done)
             """)

    assert msg =~ "misses bound"
  end

  test "a product arm is refused when it does not bind the received value" do
    assert {:error, msg} = Muro.check_file("examples/bad_pair_bindings.muro")
    assert msg =~ "short: wrong arity"
    assert msg =~ "extra-binders: wrong arity"
    assert msg =~ "ctor-pair: constructor arm on a pair"
    assert msg =~ "ctor-rec: constructor arm on a record"
    assert msg =~ "missing: missing field"
    assert msg =~ "extra-field: extra field"
    assert msg =~ "duplicate: duplicate field"
    assert msg =~ "order: field out of order"
    assert msg =~ "wrong-type: put b done does not conform to send Nat end"
    assert msg =~ "natty: match does not cover the received value"
    assert msg =~ "united: match does not cover the received value"
    assert msg =~ "vectored: match does not cover the received value"
    assert msg =~ "on-pair: a case is on a bit or a declared data type"
    assert msg =~ "on-rec: a case is on a bit or a declared data type"
    assert msg =~ "on-comp: a case is on the name just bound"
    assert msg =~ "peek: the run does not decide an arm"
    assert msg =~ "other: match does not cover the received value"
    assert msg =~ "abandoned: linear channel abandoned"

    assert {:error, nest} =
             Parser.parse("conform x : p := get (p : Nat) (match p | (q, (a, b)) => done)\n")

    assert nest =~ "a pattern is one level"

    assert {:error, nest} =
             Parser.parse("conform x : p := get (r : Nat) (match r | { x = (a, b) } => done)\n")

    assert nest =~ "a pattern is one level"
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

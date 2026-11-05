defmodule Muro.BoundedFieldsTest do
  use ExUnit.Case, async: true

  alias Muro.{Async, Check, Meet, Parser}

  test "bounded-fields.muro checks, and both meeting orders follow the split" do
    path = "examples/bounded-fields.muro"
    assert Muro.check_file(path) == :ok

    assert {:ok, book} = Parser.parse(File.read!(path))
    assert Check.check_sig(book) == :ok

    pairs = [
      {"ask-server", "ask-send"},
      {"tri-server", "tri-send"},
      {"two-server", "two-send"}
    ]

    for {left, right} <- pairs do
      l = Enum.find(book, &(&1.name == left))
      r = Enum.find(book, &(&1.name == right))
      assert Meet.meets(l.proc, r.proc, book) == :ok
      assert Meet.meets(r.proc, l.proc, book) == :ok
      assert Async.meets(l.proc, r.proc, book, 1) == :ok
      assert Async.meets(r.proc, l.proc, book, 1) == :ok
    end
  end

  test "a numeral field bound is required to build the value" do
    assert {:error, msg} =
             check("""
             data Req : Type where
               req : (slot : Nat) {slot ≤ 1} → Req

             def two : run Nat := suc (suc 0)

             session give := send Req end

             conform over : give := put (req 2) done
             conform computed : give := put (req two) done
             conform named : give :=
               get (k : Nat) (put (req k) done)
             """)

    assert msg =~ "over:"
    assert msg =~ "misses bound"
    assert msg =~ "computed:"
    assert msg =~ "misses bound"
    assert msg =~ "named:"
    assert msg =~ "misses bound"
  end

  test "a field bound that is not a numeral, or not on a nat, is refused" do
    assert {:error, msg} =
             Parser.parse("data Req : Type where req : (slot : Nat) {slot ≤ n} → Req\n")

    assert msg =~ "a field bound is a numeral"

    assert {:error, msg} =
             Parser.parse("data Req : Type where req : (slot : Nat) {other ≤ 1} → Req\n")

    assert msg =~ "a field bound is a numeral"

    assert {:error, msg} =
             Parser.parse("data Req : Type where req : (slot : Nat) {slot ≤ suc 0} → Req\n")

    assert msg =~ "a field bound is a numeral"

    assert {:error, msg} =
             Parser.parse("data Req : Type where req : (slot : Nat) {slot ≤ 00} → Req\n")

    assert msg =~ "a field bound is a numeral"

    assert {:error, msg} =
             Parser.parse("""
             data Bool : Type where
               true : Bool
               false : Bool
             data Req : Type where
               req : (b : Bool) {b ≤ 1} → Req
             """)

    assert msg =~ "a field bound is on a nat"
  end

  test "an unbounded nat, a pair, a record, a vector, and a wildcard stay refused" do
    assert {:error, msg} =
             check("""
             data Bool : Type where
               true : Bool
               false : Bool

             data Box : Type where
               box : (n : Nat) → Box

             data Maybe (A : Type) : Type where
               nothing : Maybe A
               just : A → Maybe A

             data Pair : Type where
               pair : (p : Bool × Bool) → Pair

             def ignore : run Π (q : Bool × Bool) → Bool :=
               λ (q : Bool × Bool) → true

             def on-nat : run Π (b : Box) → Bool :=
               λ (b : Box) →
                 match b motive (λ _ → Bool)
                   | box n =>
                       match n motive (λ _ → Bool)
                         | 0 => true
                         | suc _ => false

             def on-pair : run Π (p : Pair) → Bool :=
               λ (p : Pair) →
                 match p motive (λ _ → Bool)
                   | pair q => ignore q

             def wild : run Π (m : Maybe Bool) → Bool :=
               λ (m : Maybe Bool) →
                 match m motive (λ _ → Bool)
                   | _ => false
                   | just b => b

             session natty :=
               recv (b : Box) (case (on-nat b)
                 | true => end
                 | false => end)

             session paired :=
               recv (p : Pair) (case (on-pair p)
                 | true => end
                 | false => end)

             session recorded :=
               recv (r : { x : Bool }) (case r
                 | true => end
                 | false => end)

             session vectored :=
               recv (v : Vec Bool 1) (case v
                 | true => end
                 | false => end)

             conform natty-server : natty :=
               get (b : Box) (match b | box n => done)

             conform pair-server : paired :=
               get (p : Pair) (match p | pair q => done)
             """)

    assert msg =~ "wild body: expected constructor nothing, got _"
    assert msg =~ "natty-server:"
    assert msg =~ "the run does not decide an arm"
    assert msg =~ "pair-server:"
    assert msg =~ "the run does not decide an arm"
    assert msg =~ "recorded: a case is on a bit or a declared data type"
    assert msg =~ "vectored: a case is on a bit or a declared data type"
  end

  test "a recursive field read by the run does not decide an arm" do
    assert {:error, msg} =
             check("""
             data Bool : Type where
               true : Bool
               false : Bool

             data Nest : Type where
               tip : Nest
               nest : Nest → Nest

             def peek : run Π (t : Nest) → Bool :=
               λ (t : Nest) →
                 match t motive (λ _ → Bool)
                   | tip => true
                   | nest u =>
                       match u motive (λ _ → Bool)
                         | tip => false
                         | nest _ => true

             session nested :=
               recv (t : Nest) (case (peek t)
                 | true => end
                 | false => end)

             conform nested-server : nested :=
               get (t : Nest) (match t | tip => done | nest u => done)
             """)

    assert msg =~ "nested-server:"
    assert msg =~ "the run does not decide an arm"
    refute msg =~ "run definition calls itself"
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

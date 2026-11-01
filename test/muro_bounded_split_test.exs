defmodule Muro.BoundedSplitTest do
  use ExUnit.Case, async: true

  alias Muro.{Async, Check, Meet, Parser}

  test "bounded-split.muro checks, and both meeting orders follow the numeral" do
    path = "examples/bounded-split.muro"
    assert Muro.check_file(path) == :ok
    assert {:ok, book} = Parser.parse(File.read!(path))
    assert Check.check_sig(book) == :ok

    pairs = [
      {"direct-server", "direct-0"},
      {"direct-server", "direct-1"},
      {"direct-server", "direct-2"},
      {"gated-server", "gated-0"},
      {"gated-server", "gated-1"},
      {"gated-server", "gated-two"},
      {"mixed-server", "mix-t0"},
      {"mixed-server", "mix-t1"},
      {"mixed-server", "mix-f0"},
      {"mixed-server", "mix-f1"}
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

  test "a missing numeral in a product column does not conform" do
    assert {:error, msg} =
             check("""
             data Bool : Type where
               true : Bool
               false : Bool

             def mix : run Π (d : Nat) → Π (b : Bool) → Bool :=
               λ (d : Nat) → λ (b : Bool) →
                 match b motive (λ _ → Bool)
                   | true =>
                       match d motive (λ _ → Bool)
                         | 0 => true
                         | suc _ => false
                   | false => false

             session mixed :=
               recv (d : Nat) {d ≤ 1} (
                 recv (b : Bool) (case (mix d b)
                   | true => send Nat end
                   | false => end))

             conform short : mixed :=
               get (d : Nat) (
                 get (b : Bool) (
                   match b
                     | true => (match d
                         | 0 => put 0 done)
                     | false => done))
             """)

    assert msg =~ "match does not cover the received value"
  end

  test "an unbounded nat, a name bound, and a wildcard stay refused" do
    assert {:error, msg} =
             check("""
             session plain :=
               recv (n : Nat) (case n
                 | 0 => end)

             session named :=
               recv (w : Nat) (recv (d : Nat) {d ≤ w} (case d
                 | 0 => end))

             session wild :=
               recv (d : Nat) {d ≤ 0} (case d
                 | _ => end)

             session padded :=
               recv (d : Nat) {d ≤ 0} (case d
                 | 00 => end)

             session order :=
               recv (d : Nat) {d ≤ 1} (case d
                 | 1 => end
                 | 0 => end)
             """)

    assert msg =~ "plain: a case is on a bit or a declared data type"
    assert msg =~ "named: a case is on a bit or a declared data type"
    assert msg =~ "wild: case arms do not match the constructors"
    assert msg =~ "padded: case arms do not match the constructors"
    assert msg =~ "order: case arms do not match the constructors"
  end

  test "a pair, a record, a vector, and unit stay refused as the split" do
    assert {:error, msg} =
             check("""
             session paired :=
               recv (p : Nat × Nat) (case p
                 | 0 => end)

             session recorded :=
               recv (r : { x : Nat }) (case r
                 | 0 => end)

             session vectored :=
               recv (v : Vec Nat 1) (case v
                 | 0 => end)

             session united :=
               recv (u : Unit) (case u
                 | tt => end)
             """)

    assert msg =~ "paired: a case is on a bit or a declared data type"
    assert msg =~ "recorded: a case is on a bit or a declared data type"
    assert msg =~ "vectored: a case is on a bit or a declared data type"
    assert msg =~ "united: a case is on a bit or a declared data type"
  end

  test "a run of more than the nat and one payload does not decide an arm" do
    assert {:error, msg} =
             check("""
             data Bool : Type where
               true : Bool
               false : Bool

             def both : run Π (d : Nat) → Π (e : Nat) → Bool :=
               λ (d : Nat) → λ (e : Nat) → true

             def three : run Π (d : Nat) → Π (b : Bool) → Π (c : Bool) → Bool :=
               λ (d : Nat) → λ (b : Bool) → λ (c : Bool) → true

             def gate : run Π (n : Nat) → Bool :=
               λ (n : Nat) → true

             session two-nats :=
               recv (d : Nat) {d ≤ 1} (
                 recv (e : Nat) {e ≤ 1} (case (both d e)
                   | true => end
                   | false => end))

             session tri :=
               recv (d : Nat) {d ≤ 1} (
                 recv (b : Bool) (
                   recv (c : Bool) (case (three d b c)
                     | true => end
                     | false => end)))

             session early :=
               recv (d : Nat) {d ≤ 1} (
                 recv (b : Bool) (case d
                   | 0 => end
                   | 1 => end))

             session unbounded-run :=
               recv (n : Nat) (case (gate n)
                 | true => end
                 | false => end)
             """)

    assert msg =~ "two-nats: the run does not decide an arm"
    assert msg =~ "tri: the run does not decide an arm"
    assert msg =~ "early: a case is on the name just bound"
    assert msg =~ "unbounded-run: a case is on a bit or a declared data type"
  end

  test "a numeral past the bound misses it" do
    assert {:error, msg} =
             check("""
             session direct :=
               recv (d : Nat) {d ≤ 2} (case d
                 | 0 => end
                 | 1 => end
                 | 2 => end)

             session direct-back := dual direct

             conform over : direct-back := put 3 done
             """)

    assert msg =~ "misses bound"
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

defmodule Muro.ArrowTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, Parser}

  test "arrow.muro checks, and a %1 argument is passed once" do
    path = "examples/arrow.muro"
    assert Muro.check_file(path) == :ok

    assert {:ok, out} = Muro.emit_file(path, Arrow)
    assert out =~ ~r/\bdef keep\b/
    assert out =~ ~r/\bdef use\b/
    assert out =~ "keep(0)"
  end

  test "%1 is a whole token on a binder" do
    assert {:error, msg} =
             Parser.parse("def f : run Π (%10 x : Nat) → Nat := λ (%1 x : Nat) → x\n")

    assert msg =~ "expected %0 or %1"
  end

  test "a %1 binder that is never used is refused" do
    assert {:error, msg} =
             check("""
             def drop : run Π (%1 x : Nat) → Nat :=
               λ (%1 x : Nat) → 0
             """)

    assert msg =~ "linear variable unused"
  end

  test "an unmarked binder and %0 may be dropped" do
    assert check("""
           def plain : run Π (x : Nat) → Nat := λ (x : Nat) → 0
           def loose : run Π (%0 x : Nat) → Nat := λ (%0 x : Nat) → 0
           """) == :ok
  end

  test "the λ mark and the Π mark must agree" do
    assert {:error, msg} =
             check("""
             def bad : run Π (%1 x : Nat) → Nat := λ (x : Nat) → x
             """)

    assert msg =~ "λ/Π multiplicity mismatch"

    assert {:error, msg} =
             check("""
             def bad : run Π (x : Nat) → Nat := λ (%1 x : Nat) → x
             """)

    assert msg =~ "λ/Π multiplicity mismatch"
  end

  test "a second use of a %1 binder is the affine refusal" do
    assert {:error, msg} =
             check("""
             def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
               λ (n : Nat) → λ (m : Nat) → n
             def twice : run Π (%1 x : Nat) → Nat :=
               λ (%1 x : Nat) → plus x x
             """)

    assert msg =~ "affine variable used twice"
  end

  test "evidence refuses an unused %1 binder, and spec forgets the use" do
    assert {:error, msg} =
             check("""
             def ignore : evidence Π (%1 n : Nat) → Nat :=
               λ (%1 n : Nat) → 0
             """)

    assert msg =~ "linear variable unused"

    assert check("""
           def box : spec Type := Π (%1 x : Nat) → Nat
           """) == :ok
  end

  test "a %1 field of a constructor must be used" do
    assert check("""
           data Box : Type where
             box : Π (%1 n : Nat) → Box

           def get : run Π (b : Box) → Nat :=
             λ (b : Box) →
               match b motive (λ _ → Nat)
                 | box n => n
           """) == :ok

    assert {:error, msg} =
             check("""
             data Box : Type where
               box : Π (%1 n : Nat) → Box

             def lose : run Π (b : Box) → Nat :=
               λ (b : Box) →
                 match b motive (λ _ → Nat)
                   | box n => 0
             """)

    assert msg =~ "linear variable unused"
  end

  test "a session mark and a binder mark parse in one book" do
    assert check("""
           session %1 done-s := end
           conform finished : done-s := done
           def keep : run Π (%1 x : Nat) → Nat := λ (%1 x : Nat) → x
           """) == :ok
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

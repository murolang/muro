defmodule Muro.GradeTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, Emit, Parser, Prelude}

  @plus """
  def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
    λ (n : Nat) → λ (m : Nat) → n
  """

  test "grades.muro checks, and emit erases the pairs" do
    path = "examples/grades.muro"
    assert Muro.check_file(path) == :ok

    assert {:ok, graded} = Muro.emit_file(path, Grades)

    stripped = """
    def once : run Π (n : Nat) → Nat :=
      λ (n : Nat) → n

    def many : run Π (n : Nat) → Nat :=
      λ (n : Nat) → plus n n
    """

    assert {:ok, book} = Parser.parse(stripped)
    assert graded == Emit.emit_module(Grades, Prelude.for_emit(book))
    refute graded =~ "ω"
    refute graded =~ "(1, 0)"
    refute graded =~ "(ω, 0)"
  end

  test "grade 1 that is never used is refused" do
    assert {:error, msg} =
             check("""
             def drop : run Π (n : (1, 0) Nat) → Nat :=
               λ (n : (1, 0) Nat) → 0
             """)

    assert msg =~ "linear variable unused"
  end

  test "a second use of grade 1 is the affine refusal" do
    assert {:error, msg} =
             check("""
             #{@plus}
             def twice : run Π (n : (1, 0) Nat) → Nat :=
               λ (n : (1, 0) Nat) → plus n n
             """)

    assert msg =~ "affine variable used twice"
  end

  test "exact grade 2 used once is refused, and used twice checks" do
    assert {:error, msg} =
             check("""
             def once : run Π (n : (2, 0) Nat) → Nat :=
               λ (n : (2, 0) Nat) → n
             """)

    assert msg =~ "grade 2 does not allow 1 uses"

    assert check("""
           #{@plus}
           def twice : run Π (n : (2, 0) Nat) → Nat :=
             λ (n : (2, 0) Nat) → plus n n
           """) == :ok
  end

  test "ω may be unused or used twice" do
    assert check("""
           #{@plus}
           def none : run Π (n : (ω, 0) Nat) → Nat :=
             λ (n : (ω, 0) Nat) → 0
           def twice : run Π (n : (omega, 0) Nat) → Nat :=
             λ (n : (omega, 0) Nat) → plus n n
           """) == :ok
  end

  test "an interval [0, 1] may drop and may not be used twice" do
    assert check("""
           def drop : run Π (n : ([0, 1], 0) Nat) → Nat :=
             λ (n : ([0, 1], 0) Nat) → 0
           """) == :ok

    assert {:error, msg} =
             check("""
             #{@plus}
             def twice : run Π (n : ([0, 1], 0) Nat) → Nat :=
               λ (n : ([0, 1], 0) Nat) → plus n n
             """)

    assert msg =~ "affine variable used twice"
  end

  test "a type grade of 0 refuses a mention in the type" do
    assert {:error, msg} =
             check("""
             def bad : spec Π (n : (ω, 0) Nat) → {n ≡ n : Nat} :=
               λ (n : (ω, 0) Nat) → refl
             """)

    assert msg =~ "type grade 0 does not allow 2 uses"
  end

  test "spec forgets the computational grade, and an exact type grade counts mentions" do
    assert check("""
           def box : spec Type := Π (n : (1, 0) Nat) → Nat
           def named : spec Type := Π (n : (0, 2) Nat) → {n ≡ n : Nat}
           """) == :ok
  end

  test "the λ grade and the Π grade must agree" do
    assert {:error, msg} =
             check("""
             def bad : run Π (n : (1, 0) Nat) → Nat :=
               λ (n : (ω, 0) Nat) → n
             """)

    assert msg =~ "λ/Π quantity mismatch"
  end

  test "an unused predecessor of grade 1 is refused" do
    assert {:error, msg} =
             check("""
             def lose : run Π (n : (1, 0) Nat) → Nat :=
               λ (n : (1, 0) Nat) →
                 match n motive (λ _ → Nat)
                   | 0 => 0
                   | suc k => 0
             """)

    assert msg =~ "linear variable unused"
  end

  test "(x : (0, 1)) is still a pair" do
    assert {:ok, book} =
             Parser.parse("""
             def p : run Π (x : (0, 1)) → Nat := λ (x : (0, 1)) → 0
             """)

    [%{type: {:pi, :affine, {:pair, :ze, {:nat, 1}}, _, _}} | _] = book
  end

  test "a mark and a grade pair are refused" do
    assert {:error, msg} =
             Parser.parse("""
             def f : run Π (+ n : (ω, 0) Nat) → Nat := λ (n : (ω, 0) Nat) → n
             """)

    assert msg =~ "a grade pair is written on an unmarked binder"

    assert {:error, msg} =
             Parser.parse("""
             def f : run Π (%1 n : (1, 0) Nat) → Nat := λ (n : (1, 0) Nat) → n
             """)

    assert msg =~ "a grade pair is written on an unmarked binder"
  end

  test "an empty grade interval is refused" do
    assert {:error, msg} =
             Parser.parse("""
             def f : run Π (n : ([2, 1], 0) Nat) → Nat := λ (n : ([2, 1], 0) Nat) → n
             """)

    assert msg =~ "a grade interval is empty"
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

defmodule Muro.IndexedStreamTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, Parser}

  @streams ~S"""
  ν Stream (A : Type) : Type where
    uncons : Stream A → A × Stream A

  def zeros : run Stream Nat :=
    unfold 0 (λ (_ : Nat) → (0, 0))

  def natsFrom : run Π (n : Nat) → Stream Nat :=
    λ (n : Nat) → unfold n (λ (+ k : Nat) → (k, suc k))

  def zb : evidence zeros ~ zeros :=
    unfold tt (λ (_ : Unit) → (refl, zb))
  """

  defp check(src) do
    assert {:ok, book} = Parser.parse(@streams <> "\n" <> src)
    Check.check_sig(book)
  end

  test "bisim proofs compose in products" do
    assert check(~S"""
           def packaged : evidence (zeros ~ zeros) × Unit := (zb, tt)
           """) == :ok
  end

  test "bisim proofs can be theorem arguments" do
    assert check(~S"""
           def useB : evidence Π (p : zeros ~ zeros) → Unit :=
             λ (p : zeros ~ zeros) → tt
           def used : evidence Unit := useB zb
           """) == :ok
  end

  test "bisim proofs can use a spec alias" do
    assert check(~S"""
           def ZZ : spec Type := zeros ~ zeros
           def alias-proof : evidence ZZ :=
             unfold tt (λ (_ : Unit) → (refl, alias-proof))
           """) == :ok
  end

  test "bisim conversion compares indices under binders" do
    assert check(~S"""
           def pass : evidence Π (-A : Type) → Π (-s : Stream A) →
               Π (p : s ~ s) → (((λ (-t : Stream A) → t) s) ~ s) × Unit :=
             λ (-A : Type) → λ (-s : Stream A) → λ (p : s ~ s) → (p, tt)
           """) == :ok
  end

  test "bisim conversion does not erase different indices" do
    assert {:error, msg} =
             check(~S"""
             def useB : evidence Π (p : natsFrom 0 ~ zeros) → Unit :=
               λ (p : natsFrom 0 ~ zeros) → tt
             def wrong : evidence Unit := useB zb
             """)

    assert msg =~ "wrong body: cannot convert"
  end

  test "bisim proofs can be data constructor arguments" do
    assert check(~S"""
           data Box (A : Type) : Type where
             box : A → Box A
           def packaged : evidence Box (zeros ~ zeros) := box zb
           """) == :ok
  end

  test "bisim aliases can mention bound streams" do
    assert check(~S"""
           def Same : spec Π (-A : Type) → Π (-s : Stream A) → Type :=
             λ (-A : Type) → λ (-s : Stream A) → s ~ s
           def packaged : evidence Π (-A : Type) → Π (-s : Stream A) →
               Π (p : Same A s) → (s ~ s) × Unit :=
             λ (-A : Type) → λ (-s : Stream A) → λ (p : Same A s) → (p, tt)
           def alias-proof : evidence Same Nat zeros :=
             unfold tt (λ (_ : Unit) → (refl, alias-proof))
           """) == :ok
  end

  test "head-only and wrong-tail bisim proofs still fail" do
    for tail <- ["tt", "bad"] do
      assert {:error, msg} =
               check("""
               def bad : evidence natsFrom 0 ~ zeros :=
                 unfold tt (λ (_ : Unit) → (refl, #{tail}))
               """)

      assert msg =~ "bad body: cannot convert"
    end
  end

  test "unfold still checks stream types and both indices" do
    for relation <- ["zeros ~ tt", "zeros ~ unit-stream"] do
      assert {:error, msg} =
               check("""
               def unit-stream : run Stream Unit :=
                 unfold tt (λ (_ : Unit) → (tt, tt))
               def bad : evidence #{relation} :=
                 unfold tt (λ (_ : Unit) → (refl, bad))
               """)

      assert msg =~ "bad type: cannot convert"
    end
  end

  test "the indexed proof cannot become a run" do
    assert {:error, msg} =
             check(~S"""
             def leaked : run {0 ≡ 0 : Nat} := head zb
             """)

    assert msg =~ "no promotion"
  end

  test "bisim formation rejects F32 identity in a binder domain" do
    assert {:error, msg} =
             check(~S"""
             def invalid : evidence Π (-s : Stream F32) → Π (p : s ~ s) → Unit :=
               λ (-s : Stream F32) → λ (p : s ~ s) → tt
             """)

    assert msg =~ "invalid type: kernel identity is not defined on F32"
  end
end

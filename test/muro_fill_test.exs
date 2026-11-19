defmodule Muro.FillTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  @add1 "examples/fill/add1.muro"
  @golden "examples/fill/add1.filled.muro"

  test "mix muro.fill writes the successor and the book checks" do
    dir = tmp_dir()
    path = Path.join(dir, "add1.muro")
    File.cp!(@add1, path)

    out =
      capture_io(fn ->
        assert Mix.Tasks.Muro.Fill.run([path, "--def", "add1"]) == :ok
      end)

    assert out =~ "filled add1\n"
    assert File.read!(path) == File.read!(@golden)
    assert Muro.check_file(path) == :ok
  end

  test "closed equations reject a type-correct constant and the identity" do
    dir = tmp_dir()
    path = Path.join(dir, "add1.muro")
    before = File.read!(@add1)
    File.write!(path, before)

    assert_raise Mix.Error,
                 ~r/bound 2 reached: tried 2 candidates, 2 type-checked but failed the closed equations/,
                 fn ->
                   Mix.Tasks.Muro.Fill.run([path, "--def", "add1", "--bound", "2"])
                 end

    assert File.read!(path) == before
    refute Enum.any?(File.ls!(dir), &String.contains?(&1, ".muro-fill-"))
  end

  test "identity equations fill the bound variable" do
    src = """
    def idn : run Π (n : Nat) → Nat :=
      ?

    def idn-0 : evidence {idn 0 ≡ 0 : Nat} :=
      refl

    def idn-1 : evidence {idn suc(0) ≡ suc(0) : Nat} :=
      refl
    """

    dir = tmp_dir()
    path = Path.join(dir, "idn.muro")
    File.write!(path, src)

    capture_io(fn ->
      assert Mix.Tasks.Muro.Fill.run([path, "--def", "idn"]) == :ok
    end)

    assert File.read!(path) == String.replace(src, "?", "λ (n : Nat) → n")
    assert Muro.check_file(path) == :ok
  end

  test "evidence is filled from its type" do
    src = """
    def unit_ok : evidence {0 ≡ 0 : Nat} :=
      ?
    """

    dir = tmp_dir()
    path = Path.join(dir, "unit_ok.muro")
    File.write!(path, src)

    capture_io(fn ->
      assert Mix.Tasks.Muro.Fill.run([path, "--def", "unit_ok"]) == :ok
    end)

    assert File.read!(path) == String.replace(src, "?", "refl")
    assert Muro.check_file(path) == :ok
  end

  test "the same book and bound produce the same body" do
    dir = tmp_dir()
    left = Path.join(dir, "left.muro")
    right = Path.join(dir, "right.muro")
    File.cp!(@add1, left)
    File.cp!(@add1, right)

    capture_io(fn ->
      assert Mix.Tasks.Muro.Fill.run([left, "--def", "add1", "--bound", "8"]) == :ok
      assert Mix.Tasks.Muro.Fill.run([right, "--def", "add1", "--bound", "8"]) == :ok
    end)

    assert File.read!(left) == File.read!(right)
    assert File.read!(left) == File.read!(@golden)
  end

  test "a candidate does not call the definition being filled" do
    src = File.read!(@add1)
    assert {:ok, terms} = Muro.Fill.candidates(src, "add1", 5)

    assert Enum.take(terms, 2) == [
             {:lam, :affine, :nat, "n", :ze},
             {:lam, :affine, :nat, "n", {:var, "n"}}
           ]

    refute Enum.any?(terms, &Muro.Fill.refers?(&1, "add1"))
    assert Enum.any?(terms, &match?({:lam, _, _, _, {:mnat, _, _, _, _, _, _}}, &1))
    assert length(terms) == 60
  end

  test "a function in scope is applied, and a constant does not close the hole" do
    src = """
    def apply : run Π (f : Nat → Nat) → Π (n : Nat) → Nat :=
      ?

    def apply-id0 : evidence {apply (λ (k : Nat) → k) 0 ≡ 0 : Nat} :=
      refl

    def apply-suc : evidence {apply (λ (k : Nat) → suc(k)) suc(0) ≡ suc(suc(0)) : Nat} :=
      refl

    def apply-const : evidence {apply (λ (k : Nat) → 0) suc(0) ≡ 0 : Nat} :=
      refl
    """

    dir = tmp_dir()
    path = Path.join(dir, "apply.muro")
    File.write!(path, src)

    capture_io(fn ->
      assert Mix.Tasks.Muro.Fill.run([path, "--def", "apply"]) == :ok
    end)

    expected =
      String.replace(
        src,
        "?",
        "λ (f : Π (_ : Nat) → Nat) → λ (n : Nat) → (f n)"
      )

    assert File.read!(path) == expected
    assert Muro.check_file(path) == :ok
  end

  test "a redex inside a data match is one normal form" do
    src = """
    data Bool : Type where
      true : Bool
      false : Bool

    def k : run Π (b : Bool) → Nat :=
      ?
    """

    assert {:ok, terms} = Muro.Fill.candidates(src, "k", 6)
    pred0 = {:app, {:var, "pred"}, :ze}
    zero = match_term(:ze, :ze)
    redex = match_term(:ze, pred0)

    assert zero in terms
    assert redex in terms
    assert zero != redex
    assert {:ok, 1} = Muro.Fill.distinct_count(src, "k", [zero, redex])

    dir = tmp_dir()
    path = Path.join(dir, "k.muro")

    refused = """
    data Bool : Type where
      true : Bool
      false : Bool

    def k : run Π (b : Bool) → Nat :=
      ?

    def k-no : evidence {k true ≡ suc(suc(suc(suc(suc(0))))) : Nat} :=
      refl
    """

    File.write!(path, refused)

    assert {:error, {:bound, info}} = Muro.Fill.fill(path, name: "k", bound: 6)
    assert {:ok, candidates} = Muro.Fill.candidates(refused, "k", 6)
    assert {:ok, distinct} = Muro.Fill.distinct_count(refused, "k", candidates)
    assert distinct == info.tried
    assert File.read!(path) == refused
  end

  test "a match candidate is parsed and checked before it is written" do
    src = """
    data Bool : Type where
      true : Bool
      false : Bool

    def bitNat : run Π (b : Bool) → Nat :=
      ?

    def bitNat-t : evidence {bitNat true ≡ 0 : Nat} :=
      refl

    def bitNat-f : evidence {bitNat false ≡ suc(0) : Nat} :=
      refl
    """

    dir = tmp_dir()
    path = Path.join(dir, "bitNat.muro")
    File.write!(path, src)

    capture_io(fn ->
      assert Mix.Tasks.Muro.Fill.run([path, "--def", "bitNat"]) == :ok
    end)

    expected =
      String.replace(
        src,
        "?",
        "λ (b : Bool) → (match b motive (λ _ → Nat) | true => 0 | false => suc(0))"
      )

    assert File.read!(path) == expected
    assert Muro.check_file(path) == :ok
    refute Enum.any?(File.ls!(dir), &String.contains?(&1, ".muro-fill-"))
  end

  test "a spec is kept when its type checks" do
    src = """
    def carrier : spec Type :=
      ?
    """

    dir = tmp_dir()
    path = Path.join(dir, "carrier.muro")
    File.write!(path, src)

    capture_io(fn ->
      assert Mix.Tasks.Muro.Fill.run([path, "--def", "carrier"]) == :ok
    end)

    assert File.read!(path) == String.replace(src, "?", "Nat")
    assert Muro.check_file(path) == :ok
  end

  test "an import is refused" do
    src = """
    import "std:bool.muro"

    def k : run Nat :=
      ?
    """

    assert_unchanged(src, "k", "fill reads one file and the prelude")
  end

  test "a param is refused" do
    src = """
    param A : spec Type

    def k : run Nat :=
      ?
    """

    assert_unchanged(src, "k", "fill reads one file and the prelude")
  end

  test "a body that is not ? is refused" do
    concrete = """
    def k : run Nat :=
      0
    """

    assert_unchanged(concrete, "k", "k: the body is not ?")

    nested = """
    def k : run Π (n : Nat) → Nat :=
      λ (n : Nat) → ?
    """

    assert_unchanged(nested, "k", "k: the body is not ?")
  end

  test "an unknown definition is refused" do
    src = """
    def k : run Nat :=
      ?
    """

    assert_unchanged(src, "missing", "unknown definition missing")
  end

  test "a missing --def is refused" do
    dir = tmp_dir()
    path = Path.join(dir, "k.muro")

    src = """
    def k : run Nat :=
      ?
    """

    File.write!(path, src)
    assert {:error, "missing --def"} = Muro.Fill.fill(path, [])

    assert_raise Mix.Error, "missing --def", fn ->
      Mix.Tasks.Muro.Fill.run([path])
    end

    assert File.read!(path) == src
  end

  test "another hole is not reported as a closed-equation failure" do
    src = """
    def other : run Nat :=
      ?

    def k : run Nat :=
      ?
    """

    message = assert_unchanged(src, "k", "the book has another hole")
    refute message =~ "closed equations"
  end

  test "a book check is not a closed-equation failure" do
    src = """
    def bad : run Nat :=
      tt

    def k : run Nat :=
      ?
    """

    dir = tmp_dir()
    path = Path.join(dir, "bad.muro")
    File.write!(path, src)

    assert {:error, {:bound, info}} = Muro.Fill.fill(path, name: "k", bound: 1)
    assert info.equations_failed == 0
    assert info.book_failed > 0
    refute Muro.Fill.bound_message(info) =~ "closed equations"
    assert File.read!(path) == src
  end

  test "too-low fuel is not acceptance" do
    dir = tmp_dir()
    path = Path.join(dir, "add1.muro")
    before = File.read!(@add1)
    File.write!(path, before)

    assert {:error, {:bound, info}} =
             Muro.Fill.fill(path, name: "add1", bound: 8, fuel: 1)

    assert File.read!(path) == before
    assert info.fuel_failed > 0
    assert info.equations_failed == 0
    message = Muro.Fill.bound_message(info)
    refute message =~ "closed equations"
    assert message =~ "ran out of fuel"
  end

  defp match_term(left, right) do
    {:lam, :affine, {:var, "Bool"}, "b",
     {:mdata, {:var, "b"}, "_", :nat,
      [
        {"true", [], left},
        {"false", [], right}
      ]}}
  end

  defp assert_unchanged(src, name, message) do
    dir = tmp_dir()
    path = Path.join(dir, "book.muro")
    File.write!(path, src)

    assert {:error, ^message} = Muro.Fill.fill(path, name: name, bound: 4)
    assert File.read!(path) == src
    message
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_fill_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end

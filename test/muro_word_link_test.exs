defmodule Muro.WordLinkTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, Parser}

  @val_u8 """
  Π (a : U8) → Π (b : U8) → Π (c : U8) →
  Π (h : {addc a b ≡ wsome c : Opt U8}) →
  {toNat c ≡ plus (toNat a) (toNat b) : Nat}
  """

  test "std:word.muro checks, including the closed bounds and the centidollar sum" do
    assert Muro.check_file("lib/muro/std/word.muro") == :ok
  end

  test "a book imports the unsigned lemmas and cites one" do
    src = """
    import "std:word.muro"
    def use : evidence #{@val_u8} :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) →
      λ (h : {addc a b ≡ wsome c : Opt U8}) →
        addc-val-u8 a b c h
    """

    assert check_src(src) == :ok
  end

  test "I64 is not a word-to-Nat lemma" do
    src = """
    def bad : evidence
        Π (a : I64) → Π (b : I64) → Π (c : I64) →
        Π (h : {addc a b ≡ wsome c : Opt I64}) →
        {toNat c ≡ plus (toNat a) (toNat b) : Nat} :=
      λ (a : I64) → λ (b : I64) → λ (c : I64) →
      λ (h : {addc a b ≡ wsome c : Opt I64}) →
        wlink h
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "word-to-Nat lemmas are unsigned"
  end

  test "a bound at another width is refused" do
    src = """
    import "std:le.muro"
    def bad : evidence
        Π (a : U8) → Π (b : U8) →
        Π (h : Le (suc (plus (toNat a) (toNat b))) 4294967296) →
        {addc a b ≡ wsome (toU8 (plus (toNat a) (toNat b))) : Opt U8} :=
      λ (a : U8) → λ (b : U8) →
      λ (h : Le (suc (plus (toNat a) (toNat b))) 4294967296) →
        wlink h
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "wlink width does not match"
  end

  test "a hypothesis that is not the equation is refused" do
    src = """
    def bad : evidence
        Π (a : U8) → Π (b : U8) → Π (c : U8) →
        {toNat c ≡ plus (toNat a) (toNat b) : Nat} :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) →
        wlink tt
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "wlink does not prove this type"
  end

  test "subc does not prove the plus equation" do
    src = """
    def bad : evidence
        Π (a : U8) → Π (b : U8) → Π (c : U8) →
        Π (h : {subc a b ≡ wsome c : Opt U8}) →
        {toNat c ≡ plus (toNat a) (toNat b) : Nat} :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) →
      λ (h : {subc a b ≡ wsome c : Opt U8}) →
        wlink h
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "wlink operation does not match"
  end

  test "wrapping addition is not a checked operation" do
    src = """
    def bad : evidence
        Π (a : U8) → Π (b : U8) → Π (c : U8) →
        Π (h : {addi a b ≡ c : U8}) →
        {toNat c ≡ plus (toNat a) (toNat b) : Nat} :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) →
      λ (h : {addi a b ≡ c : U8}) →
        wlink h
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "wlink expected a checked unsigned operation"
  end

  test "wlink is refused in run mode" do
    src = """
    def bad : run U8 := wlink (toU8 0)
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "no promotion: wlink in run mode"
  end

  test "wlink has no inferred type" do
    src = """
    def bad : evidence Nat := wlink tt 0
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "wlink requires an expected type"
  end

  test "wlink takes one proof" do
    assert {:ok, [d]} = Parser.parse("def bad : evidence {0 ≡ 0 : Nat} := refl")
    book = [Map.put(d, :body, {:word, :link, []})]
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "wlink takes one proof"
  end

  test "evidence wlink is erased and the run image is unchanged" do
    bare = "def n : run Nat := 0\n"

    linked = """
    def n : run Nat := 0
    def addc-val-u8 : evidence #{@val_u8} :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) →
      λ (h : {addc a b ≡ wsome c : Opt U8}) →
        wlink h
    """

    for backend <- [:elixir, :c, :rust, :zig, :js, :asm, :mbi] do
      left = emit!(bare, backend)
      right = emit!(linked, backend)
      assert left == right, inspect(backend)
      assert left =~ "n"
      refute left =~ "wlink"
      refute left =~ "addc-val-u8"
    end
  end

  test "Le defined as Unit is refused" do
    src = """
    def Le : spec Π (m : Nat) → Π (n : Nat) → Type :=
      λ (m : Nat) → λ (n : Nat) → Unit

    def bad : evidence
        Π (a : U8) → Π (b : U8) → Π (c : U8) →
        Π (h : {addc a b ≡ wsome c : Opt U8}) →
        Le (suc (plus (toNat a) (toNat b))) 256 :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) →
      λ (h : {addc a b ≡ wsome c : Opt U8}) →
        wlink h
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "wlink expected the standard definition of Le"
  end

  test "times defined as plus is refused" do
    src = """
    def times : run Π (n : Nat) → Π (m : Nat) → Nat := plus

    def bad : evidence #{@val_u8 |> String.replace("addc", "mulc") |> String.replace("plus", "times")} :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) →
      λ (h : {mulc a b ≡ wsome c : Opt U8}) →
        wlink h
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "wlink expected the standard definition of times"
  end

  test "a redefined minus is refused" do
    src = """
    def minus : run Π (m : Nat) → Π (n : Nat) → Nat :=
      λ (m : Nat) → λ (n : Nat) → m

    def bad : evidence
        Π (a : U8) → Π (b : U8) → Π (c : U8) →
        Π (h : {subc a b ≡ wsome c : Opt U8}) →
        {toNat c ≡ minus (toNat a) (toNat b) : Nat} :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) →
      λ (h : {subc a b ≡ wsome c : Opt U8}) →
        wlink h
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "wlink expected the standard definition of minus"
  end

  test "a redefined plus is refused" do
    src = """
    def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
      λ (n : Nat) → λ (m : Nat) → 0

    def bad : evidence #{@val_u8} :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) →
      λ (h : {addc a b ≡ wsome c : Opt U8}) →
        wlink h
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "wlink expected the standard definition of plus"
  end

  test "a swapped subc fit is refused" do
    src = """
    import "std:le.muro"
    def bad : evidence
        Π (a : U8) → Π (b : U8) → Π (c : U8) →
        Π (h : {subc a b ≡ wsome c : Opt U8}) →
        Le (toNat a) (toNat b) :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) →
      λ (h : {subc a b ≡ wsome c : Opt U8}) →
        wlink h
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "wlink does not prove this type"
  end

  test "mulc's wsome hypothesis does not prove the plus equation" do
    src = """
    def bad : evidence #{@val_u8 |> String.replace("addc", "mulc")} :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) →
      λ (h : {mulc a b ≡ wsome c : Opt U8}) →
        wlink h
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "wlink operation does not match"
  end

  test "a wsome hypothesis does not prove the mulc some equation" do
    src = """
    import "std:word.muro"
    def bad : evidence
        Π (a : U8) → Π (b : U8) → Π (c : U8) →
        Π (h : {mulc a b ≡ wsome c : Opt U8}) →
        {mulc a b ≡ wsome (toU8 (times (toNat a) (toNat b))) : Opt U8} :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) →
      λ (h : {mulc a b ≡ wsome c : Opt U8}) →
        wlink h
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "wlink does not prove this type"
  end

  test "a wsome hypothesis does not prove the subc some equation" do
    src = """
    import "std:le.muro"
    def bad : evidence
        Π (a : U8) → Π (b : U8) → Π (c : U8) →
        Π (h : {subc a b ≡ wsome c : Opt U8}) →
        {subc a b ≡ wsome (toU8 (minus (toNat a) (toNat b))) : Opt U8} :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) →
      λ (h : {subc a b ≡ wsome c : Opt U8}) →
        wlink h
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "wlink does not prove this type"
  end

  test "a bound that is not a modulus is a shape error" do
    src = """
    import "std:le.muro"
    def bad : evidence
        Π (a : U8) → Π (b : U8) →
        Π (h : Le (suc (plus (toNat a) (toNat b))) 100) →
        {addc a b ≡ wsome (toU8 (plus (toNat a) (toNat b))) : Opt U8} :=
      λ (a : U8) → λ (b : U8) →
      λ (h : Le (suc (plus (toNat a) (toNat b))) 100) →
        wlink h
    """

    assert {:error, msg} = check_src(src)
    assert msg =~ "wlink does not prove this type"
    refute msg =~ "wlink width does not match"
  end

  test "nested operands are accepted and a different nesting is refused" do
    ok = """
    def nested : evidence
        Π (a : U8) → Π (b : U8) → Π (c : U8) → Π (d : U8) →
        Π (h : {addc (addi a b) c ≡ wsome d : Opt U8}) →
        {toNat d ≡ plus (toNat (addi a b)) (toNat c) : Nat} :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) → λ (d : U8) →
      λ (h : {addc (addi a b) c ≡ wsome d : Opt U8}) →
        wlink h
    """

    assert check_src(ok) == :ok

    bad = """
    def bad : evidence
        Π (a : U8) → Π (b : U8) → Π (c : U8) → Π (d : U8) →
        Π (h : {addc (addi a b) c ≡ wsome d : Opt U8}) →
        {toNat d ≡ plus (toNat a) (toNat c) : Nat} :=
      λ (a : U8) → λ (b : U8) → λ (c : U8) → λ (d : U8) →
      λ (h : {addc (addi a b) c ≡ wsome d : Opt U8}) →
        wlink h
    """

    assert {:error, msg} = check_src(bad)
    assert msg =~ "wlink does not prove this type"
  end

  test "a run-mode wlink is a type error before emit" do
    src = "def bad : run U8 := wlink (toU8 0)\n"

    assert {:error, msg} = emit_result(src, :elixir)
    assert msg =~ "no promotion: wlink in run mode"

    assert {:error, msg} = emit_result(src, :mbi)
    assert msg =~ "no promotion: wlink in run mode"
  end

  defp check_src(src) do
    dir = tmp("check")
    path = Path.join(dir, "book.muro")
    File.write!(path, src)
    Muro.check_file(path)
  end

  defp emit!(src, backend) do
    assert {:ok, out} = emit_result(src, backend)
    out
  end

  defp emit_result(src, backend) do
    dir = tmp(Atom.to_string(backend))
    path = Path.join(dir, "same.muro")
    File.write!(path, src)

    case backend do
      :elixir ->
        Muro.emit_file(path, Same)

      :c ->
        with {:ok, files} <- Muro.emit_c(path, nif: false) do
          {:ok, files |> Enum.sort() |> Enum.map_join("\n", &File.read!/1)}
        end

      :rust ->
        with {:ok, files} <- Muro.emit_rust(path) do
          {:ok, files |> Enum.map_join("\n", &File.read!/1)}
        end

      :zig ->
        with {:ok, files} <- Muro.emit_zig(path) do
          {:ok, files |> Enum.map_join("\n", &File.read!/1)}
        end

      :js ->
        with {:ok, files} <- Muro.emit_js(path) do
          {:ok, files |> Enum.sort() |> Enum.map_join("\n", &File.read!/1)}
        end

      :asm ->
        with {:ok, files} <- Muro.emit_asm(path) do
          {:ok, files |> Enum.map_join("\n", &File.read!/1)}
        end

      :mbi ->
        with {:ok, files} <- Muro.emit_mbi(path) do
          {:ok, files |> Enum.map_join(&File.read!/1)}
        end
    end
  end

  defp tmp(kind) do
    dir = Path.join(System.tmp_dir!(), "muro_wlink_#{kind}_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end

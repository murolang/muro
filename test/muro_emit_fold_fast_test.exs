defmodule Muro.EmitFoldFastTest do
  use ExUnit.Case, async: true

  @moduletag timeout: 120_000

  test "a border automaton becomes :binary.match and agrees with the byte loop" do
    src = emit!("crlf", crlf_book(), ProbeCrlfFast)
    assert src =~ ":binary.match"
    refute fun_src(src, "crlfFold") =~ "recur.("
    [{ProbeCrlfFast, _}] = Code.compile_string(src)

    samples = [
      "",
      "\r\n\r\n",
      "\r\n\r\n\r\n",
      "abc\r\n\r\nxyz",
      "\r\n\r\r\n\r\n",
      "\r\r\n\r\n",
      :binary.copy("a", 80) <> "\r\n\r\n" <> :binary.copy("b", 40),
      :binary.copy("a", 200),
      "\r\n\r",
      "\n\n",
      <<13, 10, 13, 13, 10, 13, 10>>,
      :binary.copy(<<13>>, 12),
      <<0, 255, 10, 13>>
    ]

    for bin <- samples do
      assert call(ProbeCrlfFast, :crlfFold, [bin]) == crlf_oracle(bin)
    end

    big = :binary.copy("a", 16_384)
    assert call(ProbeCrlfFast, :crlfFold, [big]) == crlf_oracle(big)
    assert reductions(fn -> call(ProbeCrlfFast, :crlfFold, [big]) end) < 1_000
  end

  test "a step that is the identity off one byte skips to that byte" do
    src = emit!("count", count_book(), ProbeCountFast)
    assert fun_src(src, "countLf") =~ ":binary.match"
    refute fun_src(src, "countLf") =~ "muro__r"
    [{ProbeCountFast, _}] = Code.compile_string(src)

    body = :binary.copy("a", 1000) <> "\n" <> :binary.copy("b", 1000) <> "\n\n"
    assert call(ProbeCountFast, :countLf, [body]) == 3
    assert call(ProbeCountFast, :countLf, [:binary.copy("a", 50)]) == 0
    assert call(ProbeCountFast, :countStop, [:binary.copy(<<10>>, 500)]) == 3

    assert reductions(fn -> call(ProbeCountFast, :countStop, [:binary.copy(<<10>>, 4_000)]) end) <
             1_000
  end

  test "a string step gated on one index stays a byte loop" do
    src = emit!("gated", gated_book(), ProbeGatedFast)
    refute src =~ ":binary.match"
    assert fun_src(src, "gatedFold") =~ "<<b, rest::binary>>"
    [{ProbeGatedFast, _}] = Code.compile_string(src)

    for bin <- ["", "\n\n", "\n", "aaaaa\n\n", "xxxx\n\n", "\n\n\n\n\n\n\n", "aaaaa\naaaaa\n\n"] do
      assert call(ProbeGatedFast, :gatedFold, [bin]) == gated_oracle(bin)
    end
  end

  # The probe module is compiled from emitted source at runtime.
  defp call(mod, fun, args), do: apply(mod, fun, args)

  defp emit!(stem, book, mod) do
    dir = Path.join(System.tmp_dir!(), "muro-fold-fast-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, stem <> ".muro")
    File.write!(path, book)

    case Muro.emit_file(path, mod) do
      {:ok, src} -> src
      other -> flunk("emit failed: #{inspect(other)}")
    end
  end

  defp fun_src(src, name) do
    src |> String.split("def #{name}(") |> Enum.at(1) |> String.split("\n  def ") |> hd()
  end

  defp reductions(fun) do
    parent = self()
    ref = make_ref()

    spawn(fn ->
      before = :erlang.process_info(self(), :reductions) |> elem(1)
      fun.()
      afterr = :erlang.process_info(self(), :reductions) |> elem(1)
      send(parent, {ref, afterr - before})
    end)

    receive do
      {^ref, n} -> n
    after
      5_000 -> flunk("timed out")
    end
  end

  defp crlf_oracle(bin) do
    Enum.reduce(:binary.bin_to_list(bin), 0, fn b, a ->
      st = Bitwise.band(a, 7)
      ix = Bitwise.bsr(a, 3)

      cond do
        st == 4 -> a
        b == 13 and st == 2 -> pack(3, ix + 1)
        b == 13 -> pack(1, ix + 1)
        b == 10 and st == 1 -> pack(2, ix + 1)
        b == 10 and st == 3 -> pack(4, ix + 1)
        true -> pack(0, ix + 1)
      end
    end)
  end

  defp gated_oracle(bin) do
    Enum.reduce(:binary.bin_to_list(bin), 0, fn b, a ->
      ix = div(a, 8)
      st = Bitwise.band(a, 7)

      cond do
        ix == 5 and st == 2 -> a
        ix == 5 and b == 10 and st == 1 -> pack(2, ix + 1)
        ix == 5 and b == 10 -> pack(1, ix + 1)
        ix == 5 -> pack(0, ix + 1)
        true -> pack(0, ix + 1)
      end
    end)
  end

  defp pack(st, ix), do: Bitwise.bor(st, Bitwise.bsl(ix, 3))

  defp crlf_book do
    """
    import "std:bool.muro"

    def u8eq : run Π (x : U8) → Π (y : U8) → Bool :=
      λ (x : U8) → λ (y : U8) →
        match (eqi x y) motive (λ _ → Bool)
          | wtrue => true
          | wfalse => false

    def u64eq : run Π (x : U64) → Π (y : U64) → Bool :=
      λ (x : U64) → λ (y : U64) →
        match (eqi x y) motive (λ _ → Bool)
          | wtrue => true
          | wfalse => false

    def packEnd : run Π (st : U64) → Π (i : U64) → U64 :=
      λ (st : U64) → λ (i : U64) →
        ori (andi st (toU64 7)) (muli i (toU64 8))

    def endSt : run Π (a : U64) → U64 :=
      λ (a : U64) → andi a (toU64 7)

    def endIx : run Π (a : U64) → U64 :=
      λ (a : U64) →
        match (divi a (toU64 8)) motive (λ _ → U64)
          | wsome q => q
          | wnone => toU64 0

    def crlfByte : run Π (+ b : U8) → Π (+ a : U64) → U64 :=
      λ (+ b : U8) → λ (+ a : U64) →
        match (u64eq (endSt a) (toU64 4)) motive (λ _ → U64)
          | true => a
          | false =>
              (match (u8eq b (toU8 13)) motive (λ _ → U64)
                | true =>
                    (match (u64eq (endSt a) (toU64 2)) motive (λ _ → U64)
                      | true => packEnd (toU64 3) (addi (endIx a) (toU64 1))
                      | false => packEnd (toU64 1) (addi (endIx a) (toU64 1)))
                | false =>
                    (match (u8eq b (toU8 10)) motive (λ _ → U64)
                      | true =>
                          (match (u64eq (endSt a) (toU64 1)) motive (λ _ → U64)
                            | true => packEnd (toU64 2) (addi (endIx a) (toU64 1))
                            | false =>
                                (match (u64eq (endSt a) (toU64 3)) motive (λ _ → U64)
                                  | true => packEnd (toU64 4) (addi (endIx a) (toU64 1))
                                  | false => packEnd (toU64 0) (addi (endIx a) (toU64 1))))
                      | false => packEnd (toU64 0) (addi (endIx a) (toU64 1))))

    def crlfFold : run Π (+ s : Slice) → U64 :=
      λ (+ s : Slice) →
        sliceFold U64 (packEnd (toU64 0) (toU64 0))
          (λ (b : U8) → λ (_r : Slice) → λ (a : U64) → crlfByte b a)
          s
    """
  end

  defp count_book do
    """
    import "std:bool.muro"

    def u8eq : run Π (x : U8) → Π (y : U8) → Bool :=
      λ (x : U8) → λ (y : U8) →
        match (eqi x y) motive (λ _ → Bool)
          | wtrue => true
          | wfalse => false

    def u64eq : run Π (x : U64) → Π (y : U64) → Bool :=
      λ (x : U64) → λ (y : U64) →
        match (eqi x y) motive (λ _ → Bool)
          | wtrue => true
          | wfalse => false

    def see : run Π (+ b : U8) → Π (+ n : U64) → U64 :=
      λ (+ b : U8) → λ (+ n : U64) →
        match (u8eq b (toU8 10)) motive (λ _ → U64)
          | true => addi n (toU64 1)
          | false => n

    def countLf : run Π (+ s : Slice) → U64 :=
      λ (+ s : Slice) →
        sliceFold U64 (toU64 0)
          (λ (b : U8) → λ (_r : Slice) → λ (n : U64) → see b n)
          s

    def seeStop : run Π (+ b : U8) → Π (+ n : U64) → U64 :=
      λ (+ b : U8) → λ (+ n : U64) →
        match (u64eq n (toU64 3)) motive (λ _ → U64)
          | true => n
          | false =>
              (match (u8eq b (toU8 10)) motive (λ _ → U64)
                | true => addi n (toU64 1)
                | false => n)

    def countStop : run Π (+ s : Slice) → U64 :=
      λ (+ s : Slice) →
        sliceFold U64 (toU64 0)
          (λ (b : U8) → λ (_r : Slice) → λ (n : U64) → seeStop b n)
          s
    """
  end

  defp gated_book do
    """
    import "std:bool.muro"

    def u8eq : run Π (x : U8) → Π (y : U8) → Bool :=
      λ (x : U8) → λ (y : U8) →
        match (eqi x y) motive (λ _ → Bool)
          | wtrue => true
          | wfalse => false

    def u64eq : run Π (x : U64) → Π (y : U64) → Bool :=
      λ (x : U64) → λ (y : U64) →
        match (eqi x y) motive (λ _ → Bool)
          | wtrue => true
          | wfalse => false

    def packEnd : run Π (st : U64) → Π (i : U64) → U64 :=
      λ (st : U64) → λ (i : U64) →
        ori (andi st (toU64 7)) (muli i (toU64 8))

    def endSt : run Π (a : U64) → U64 :=
      λ (a : U64) → andi a (toU64 7)

    def endIx : run Π (a : U64) → U64 :=
      λ (a : U64) →
        match (divi a (toU64 8)) motive (λ _ → U64)
          | wsome q => q
          | wnone => toU64 0

    def gatedByte : run Π (+ b : U8) → Π (+ a : U64) → U64 :=
      λ (+ b : U8) → λ (+ a : U64) →
        match (u64eq (endIx a) (toU64 5)) motive (λ _ → U64)
          | true =>
              (match (u64eq (endSt a) (toU64 2)) motive (λ _ → U64)
                | true => a
                | false =>
                    (match (u8eq b (toU8 10)) motive (λ _ → U64)
                      | true =>
                          (match (u64eq (endSt a) (toU64 1)) motive (λ _ → U64)
                            | true => packEnd (toU64 2) (addi (endIx a) (toU64 1))
                            | false => packEnd (toU64 1) (addi (endIx a) (toU64 1)))
                      | false => packEnd (toU64 0) (addi (endIx a) (toU64 1))))
          | false => packEnd (toU64 0) (addi (endIx a) (toU64 1))

    def gatedFold : run Π (+ s : Slice) → U64 :=
      λ (+ s : Slice) →
        sliceFold U64 (packEnd (toU64 0) (toU64 0))
          (λ (b : U8) → λ (_r : Slice) → λ (a : U64) → gatedByte b a)
          s
    """
  end
end

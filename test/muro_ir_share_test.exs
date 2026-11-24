defmodule Muro.IRShareTest do
  use ExUnit.Case, async: true

  # count folds the slice. wrap only calls it. twice and viaWrap
  # compute count s twice on every path. both computes it in each arm,
  # so on every path. nested computes it twice, only in the no arm.
  # branchy computes it only on some paths, once per pickCount, so
  # nothing there may be hoisted above the match.
  @book """
  data Pick : Type where
    yes : Pick
    no : Pick

  def count : run Π (+ s : Slice) → U64 :=
    λ (+ s : Slice) →
      sliceFold U64 (toU64 0)
        (λ (_b : U8) → λ (_r : Slice) → λ (acc : U64) → addi acc (toU64 1))
        s

  def wrap : run Π (+ s : Slice) → U64 :=
    λ (+ s : Slice) → count s

  def twice : run Π (+ s : Slice) → U64 :=
    λ (+ s : Slice) → addi (count s) (count s)

  def viaWrap : run Π (+ s : Slice) → U64 :=
    λ (+ s : Slice) → addi (wrap s) (muli (count s) (toU64 10))

  def both : run Π (+ p : Pick) → Π (+ s : Slice) → U64 :=
    λ (+ p : Pick) → λ (+ s : Slice) →
      match p motive (λ _ → U64)
        | yes => addi (count s) (toU64 100)
        | no => muli (count s) (count s)

  def nested : run Π (+ p : Pick) → Π (+ s : Slice) → U64 :=
    λ (+ p : Pick) → λ (+ s : Slice) →
      match p motive (λ _ → U64)
        | yes => toU64 100
        | no => muli (count s) (count s)

  def pickCount : run Π (+ p : Pick) → Π (+ s : Slice) → U64 :=
    λ (+ p : Pick) → λ (+ s : Slice) →
      match p motive (λ _ → U64)
        | yes => count s
        | no => toU64 7

  def branchy : run Π (+ p : Pick) → Π (+ s : Slice) → U64 :=
    λ (+ p : Pick) → λ (+ s : Slice) →
      addi (pickCount p s) (pickCount p s)

  -- seen stays 1 once it has seen an x, so hasX may stop there.
  -- tally reads the octet before it keeps acc, so it may not stop.
  def seen : run Π (b : U8) → Π (+ acc : U64) → U64 :=
    λ (b : U8) → λ (+ acc : U64) →
      match (eqi acc (toU64 0)) motive (λ _ → U64)
        | wtrue =>
            (match (eqi b (toU8 120)) motive (λ _ → U64)
              | wtrue => toU64 1
              | wfalse => toU64 0)
        | wfalse => acc

  def hasX : run Π (+ s : Slice) → U64 :=
    λ (+ s : Slice) →
      sliceFold U64 (toU64 0)
        (λ (b : U8) → λ (_r : Slice) → λ (acc : U64) → seen b acc)
        s

  def tally : run Π (+ s : Slice) → U64 :=
    λ (+ s : Slice) →
      sliceFold U64 (toU64 0)
        (λ (b : U8) → λ (_r : Slice) → λ (acc : U64) →
          match (eqi b (toU8 120)) motive (λ _ → U64)
            | wtrue => acc
            | wfalse => addi acc (toU64 1))
        s

  def twice-ok : evidence {twice b"abc" ≡ toU64 6 : U64} := refl
  def via-ok : evidence {viaWrap b"abc" ≡ toU64 33 : U64} := refl
  def branchy-ok : evidence {branchy no b"abc" ≡ toU64 14 : U64} := refl
  """

  setup_all do
    dir = Path.join(System.tmp_dir!(), "muro_share_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    path = Path.join(dir, "shared.muro")
    File.write!(path, @book)
    {:ok, book} = Muro.Load.file(path)
    book = Muro.Prelude.for_emit(book)
    {:ok, funs} = Muro.IR.elaborate(book)
    {:ok, dir: dir, book: book, funs: funs}
  end

  defp body(funs, name), do: Enum.find(funs, &(&1.name == name)).body

  defp calls(t, name) do
    own = if match?({:call, ^name, _}, t), do: 1, else: 0

    sub =
      cond do
        is_tuple(t) -> t |> Tuple.to_list() |> Enum.map(&calls(&1, name)) |> Enum.sum()
        is_list(t) -> t |> Enum.map(&calls(&1, name)) |> Enum.sum()
        true -> 0
      end

    own + sub
  end

  # Text of one emitted C function, from its signature to the closing brace.
  defp c_fun(src, name) do
    [_, rest] = String.split(src, ~r/\n[^\n;]*\b#{name}\([^;\n]*\)\s*\{/, parts: 2)
    [text | _] = String.split(rest, "\n}\n", parts: 2)
    text
  end

  test "a repeated pure call is bound once", %{funs: funs} do
    shared = Muro.IR.Share.funs(funs)
    assert calls(body(funs, "twice"), "count") == 2
    assert calls(body(shared, "twice"), "count") == 1
    assert {:let, _, :u64, {:call, "count", [var: "s"]}, _} = body(shared, "twice")
  end

  test "a wrapper is inlined so its call is shared with the caller's", %{funs: funs} do
    shared = Muro.IR.Share.funs(funs)
    assert calls(body(funs, "viaWrap"), "count") == 1
    assert calls(body(funs, "viaWrap"), "wrap") == 1
    assert calls(body(shared, "viaWrap"), "wrap") == 0
    assert calls(body(shared, "viaWrap"), "count") == 1
  end

  test "a call every arm makes is bound once above the match", %{funs: funs} do
    shared = Muro.IR.Share.funs(funs)

    assert {:let, _, :u64, {:call, "count", [var: "s"]}, {:match, {:var, "p"}, _}} =
             body(shared, "both")

    assert calls(body(shared, "both"), "count") == 1
  end

  test "a call is shared inside the arm that repeats it", %{funs: funs} do
    shared = Muro.IR.Share.funs(funs)

    assert {:match, {:var, "p"}, [{:arm, "yes", [], yes}, {:arm, "no", [], no}]} =
             body(shared, "nested")

    assert calls(yes, "count") == 0
    assert {:let, _, :u64, {:call, "count", _}, _} = no
    assert calls(no, "count") == 1
  end

  test "a call only some paths make is not hoisted above the branch", %{funs: funs} do
    shared = Muro.IR.Share.funs(funs)
    # Inlining both pickCounts would expose two count calls, each under
    # its own yes arm. Neither is on every path, so nothing is shared
    # and branchy keeps its elaborated body.
    assert body(shared, "branchy") == body(funs, "branchy")
    assert body(shared, "pickCount") == body(funs, "pickCount")
  end

  test "share: false and inline: false", %{funs: funs} do
    assert Muro.IR.Share.funs(funs, share: false) == funs
    hoisted = Muro.IR.Share.funs(funs, inline: false)
    assert calls(body(hoisted, "twice"), "count") == 1
    assert calls(body(hoisted, "viaWrap"), "wrap") == 1
  end

  test "the C emitter calls the fold once in twice and viaWrap", %{book: book} do
    {:ok, {_h, src}} = Muro.Emit.C.render(book, "shared")
    {:ok, {_h, plain}} = Muro.Emit.C.render(book, "shared", share: false)
    assert length(Regex.scan(~r/\bcount\(/, c_fun(plain, "twice"))) == 2
    assert length(Regex.scan(~r/\bcount\(/, c_fun(src, "twice"))) == 1
    assert length(Regex.scan(~r/\bcount\(/, c_fun(src, "viaWrap"))) == 1
    refute c_fun(src, "viaWrap") =~ ~r/\bwrap\(/
    assert c_fun(src, "branchy") == c_fun(plain, "branchy")
  end

  test "the Rust emitter calls the fold once in twice", %{book: book} do
    {:ok, src} = Muro.Emit.Rust.render(book, "shared")
    [_, rest] = String.split(src, ~r/fn twice\(/, parts: 2)
    [text | _] = String.split(rest, "\n}\n", parts: 2)
    assert length(Regex.scan(~r/\bcount\(/, text)) == 1
  end

  test "the Zig emitter calls the fold once in twice", %{book: book} do
    {:ok, src} = Muro.Emit.Zig.render(book, "shared")
    [_, rest] = String.split(src, ~r/fn twice\(/, parts: 2)
    [text | _] = String.split(rest, "\n}\n", parts: 2)
    assert length(Regex.scan(~r/\bcount\(/, text)) == 1
  end

  test "a fold whose step keeps its accumulator stops early in C", %{book: book, funs: funs} do
    by_name = for f <- funs, not Map.get(f, :generated, false), into: %{}, do: {f.name, f}
    steps = Enum.filter(funs, &Map.get(&1, :fold, false))
    assert Enum.count(steps, &match?({:ok, _, _}, Muro.IR.Share.stop(&1, by_name))) == 1

    {:ok, {_h, src}} = Muro.Emit.C.render(book, "shared")
    assert c_fun(src, "hasX") =~ ~r/if \(\w+\) break;/
    refute c_fun(src, "tally") =~ ~r/if \(\w+\) break;/
    refute c_fun(src, "count") =~ ~r/if \(\w+\) break;/
  end

  # Same answers with and without sharing, from the compiled C.
  test "shared and plain C agree", %{book: book, dir: dir} do
    inputs = ["a", "abc", "abxcd", "x", "hello, world", String.duplicate("x", 300)]

    outs =
      for {tag, opts} <- [{"on", []}, {"off", [share: false]}] do
        sub = Path.join(dir, tag)
        File.mkdir_p!(sub)
        {:ok, {h, c}} = Muro.Emit.C.render(book, "shared", opts)
        File.write!(Path.join(sub, "shared.h"), h)
        File.write!(Path.join(sub, "shared.c"), c)
        File.write!(Path.join(sub, "main.c"), main_c(inputs))
        cc!(sub, ~w(shared.c main.c -o main_bin))
        {out, 0} = System.cmd(Path.join(sub, "main_bin"), [], stderr_to_stdout: true)
        out
      end

    assert [on, off] = outs
    assert on == off
    assert on =~ "twice 6\n"
    assert on =~ "viaWrap 33\n"
    assert on =~ "branchy-no 14\n"
    assert on =~ "hasX 0\n"
    assert on =~ "n5 1 4 "
    assert on =~ "n300 1 0 "
  end

  defp main_c(inputs) do
    cases =
      Enum.map_join(inputs, "\n", fn s ->
        lit = s |> :binary.bin_to_list() |> Enum.map_join(", ", &Integer.to_string/1)
        n = byte_size(s)

        """
          {
            static const uint8_t b[] = {#{lit}};
            muro__slice s = {b, #{n}};
            printf("n%d %llu %llu %llu %llu %llu %llu %llu %llu %llu %llu\\n", #{n},
              (unsigned long long)hasX(s), (unsigned long long)tally(s),
              (unsigned long long)twice(s), (unsigned long long)viaWrap(s),
              (unsigned long long)both(&yes, s), (unsigned long long)both(&no, s),
              (unsigned long long)nested(&yes, s), (unsigned long long)nested(&no, s),
              (unsigned long long)branchy(&yes, s), (unsigned long long)branchy(&no, s));
          }
        """
      end)

    """
    #include <stdio.h>
    #include "shared.h"
    int main(void) {
      Pick yes = {.muro__field_tag = muro__tag_Pick_yes};
      Pick no = {.muro__field_tag = muro__tag_Pick_no};
      {
        static const uint8_t b[] = {97, 98, 99};
        muro__slice s = {b, 3};
        printf("twice %llu\\n", (unsigned long long)twice(s));
        printf("viaWrap %llu\\n", (unsigned long long)viaWrap(s));
        printf("branchy-no %llu\\n", (unsigned long long)branchy(&no, s));
        printf("hasX %llu\\n", (unsigned long long)hasX(s));
      }
    #{cases}
      return 0;
    }
    """
  end

  defp cc!(dir, args) do
    {out, status} =
      System.cmd("cc", ~w(-Wall -Wextra -Werror -std=c11) ++ args,
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, out
  end
end

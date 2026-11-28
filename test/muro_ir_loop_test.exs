defmodule Muro.IRLoopTest do
  # `Muro.IR.Loop` (Phase 1a): byte folds as loops, the early exit, and
  # in-place calls. The differential loop over the corpus and the HTTP
  # step book runs the loop image too (`:loop` in test/ir_diff_helper.exs);
  # this module holds the pass to `Muro.IR.Check`, to `Muro.IR.Eval`, and
  # to the C it emits.
  use ExUnit.Case, async: true

  Code.require_file("ir_diff_helper.exs", __DIR__)

  alias Muro.IR
  alias Muro.IR.{Anf, Check, Eval, Loop, Share}

  @moduletag timeout: 600_000

  @corpus [
    "examples/**/*.muro",
    "test/fixtures/**/*.muro",
    "lib/muro/std/*.muro",
    "test/http_step/*.muro"
  ]

  @book """
  unboxed data Acc : Type where
    acc : Π (+ n : U64) → Π (+ marks : U64) → Π (+ view : Slice) → Acc

  data Cell : Type where
    cell : Π (+ n : U64) → Cell

  def bump : run Π (s : Slice) → Π (b : U8) → Π (st : Acc) → Acc :=
    λ (s : Slice) → λ (b : U8) → λ (st : Acc) →
      match st motive (λ _ → Acc)
        | acc n marks view =>
            (match (eqi b (toU8 10)) motive (λ _ → Acc)
              | wtrue => acc (addi n (toU64 1)) (addi marks (toU64 1)) (sliceUntil s (toU8 10))
              | wfalse => acc (addi n (toU64 1)) marks view)

  def scan : run Π (+ s : Slice) → Acc :=
    λ (+ s : Slice) →
      sliceFold Acc (acc (toU64 0) (toU64 0) s)
        (λ (b : U8) → λ (_rest : Slice) → λ (st : Acc) → bump s b st) s

  def upto : run Π (+ b : U8) → Π (+ st : Acc) → Acc :=
    λ (+ b : U8) → λ (+ st : Acc) →
      match st motive (λ _ → Acc)
        | acc n marks view =>
            (match (eqi marks (toU64 0)) motive (λ _ → Acc)
              | wtrue =>
                  (match (eqi b (toU8 10)) motive (λ _ → Acc)
                    | wtrue => acc n (toU64 1) view
                    | wfalse => acc (addi n (toU64 1)) marks view)
              | wfalse => st)

  def firstLine : run Π (+ s : Slice) → Acc :=
    λ (+ s : Slice) →
      sliceFold Acc (acc (toU64 0) (toU64 0) s)
        (λ (b : U8) → λ (_rest : Slice) → λ (st : Acc) → upto b st) s

  def nested : run Π (+ s : Slice) → U64 :=
    λ (+ s : Slice) →
      sliceFold U64 (toU64 0)
        (λ (b : U8) → λ (rest : Slice) → λ (k : U64) →
          addi k (sliceFold U64 (toU64 0)
            (λ (c : U8) → λ (_r : Slice) → λ (m : U64) → addi m (asU64 (xori b c))) rest))
        s

  def tally : run Π (+ s : Slice) → Cell :=
    λ (+ s : Slice) →
      sliceFold Cell (cell (toU64 0))
        (λ (_b : U8) → λ (_rest : Slice) → λ (c : Cell) →
          match c motive (λ _ → Cell) | cell n => cell (addi n (toU64 1))) s

  def nOf : run Π (st : Acc) → U64 :=
    λ (st : Acc) → match st motive (λ _ → U64) | acc n _ _ => n

  def marksOf : run Π (st : Acc) → U64 :=
    λ (st : Acc) → match st motive (λ _ → U64) | acc _ marks _ => marks

  def viewLen : run Π (st : Acc) → U64 :=
    λ (st : Acc) → match st motive (λ _ → U64) | acc _ _ view => sliceLen view

  def cellOf : run Π (c : Cell) → U64 :=
    λ (c : Cell) → match c motive (λ _ → U64) | cell n => n
  """

  @inputs ["", "a", "ab", "ab\n", "ab\ncd", "ab\ncd\nef", "\n\n", <<0, 255, 10, 13>>]

  setup_all do
    dir = Path.join(System.tmp_dir!(), "muro_ir_loop_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    path = Path.join(dir, "loop_book.muro")
    File.write!(path, @book)
    {:ok, book} = Muro.Load.file(path)
    emit = Muro.Prelude.for_emit(book)
    {:ok, plain} = IR.elaborate(emit)
    shared = Share.funs(plain)
    {:ok, dir: dir, emit: emit, plain: plain, shared: shared, loop: Loop.funs(shared, book: emit)}
  end

  defp fun(funs, name), do: Enum.find(funs, &(&1.name == name))
  defp body(funs, name), do: fun(funs, name).body

  # -- lowering ------------------------------------------------------------

  test "every fold is a loop and its step is gone", %{shared: shared, loop: loop} do
    assert Enum.any?(shared, &Map.get(&1, :fold, false))
    refute Enum.any?(loop, &Map.get(&1, :fold, false))
    refute Loop.bfold?(Enum.map(loop, & &1.body))
    assert Loop.loops(Enum.map(loop, & &1.body)) == 5
  end

  test "the step body is inlined with its captures bound once", %{loop: loop} do
    assert {:loop, [{"s", :slice, _, {:var, "s"}}], {"b", :u8, _}, {"_rest", :slice, _},
            {"st", {:data, "Acc"}, :affine}, {:con, "Acc", "acc", _}, {:var, "s"}, :none,
            {:inout, "bump", [var: "s", var: "b", var: "st"]}} = body(loop, "scan")
  end

  test "a step that keeps its accumulator is a loop exit", %{loop: loop} do
    assert {:loop, [], _, _, {"st", _, _}, _, _, {"st", {:match, {:var, "st"}, _}}, _} =
             body(loop, "firstLine")

    for name <- ["scan", "nested", "tally"] do
      assert elem(body(loop, name), 7) == :none
    end
  end

  test "a nested fold is a loop inside the body of a loop", %{loop: loop} do
    assert {:loop, [], {"b", :u8, _}, {"rest", :slice, _}, {"k", :u64, _}, _, _, :none,
            {:wrd, :u64, :add,
             [
               {:var, "k"},
               {:loop, [{"b", :u8, :reuse, {:var, "b"}}], {"c", :u8, _}, _, {"m", :u64, _}, _,
                {:var, "rest"}, :none, _}
             ]}} = body(loop, "nested")
  end

  test "a by-value accumulator updated by a run is in place", %{loop: loop} do
    assert fun(loop, "bump").inout == "st"
    assert fun(loop, "upto").inout == "st"
    refute Map.has_key?(fun(loop, "nOf"), :inout)
  end

  test "a boxed accumulator is not in place", %{loop: loop} do
    refute inout?(body(loop, "tally"))
  end

  test "no book, no in-place call", %{shared: shared} do
    out = Loop.funs(shared)
    refute Enum.any?(out, &Map.has_key?(&1, :inout))
    refute inout?(Enum.map(out, & &1.body))
    assert Check.check(out) == :ok
  end

  test "a :reuse accumulator, a doubled one, or a rebound one stays a call", %{
    emit: emit,
    shared: shared
  } do
    scan = fun(shared, "scan")
    {:bfold, step, caps, z, s} = scan.body
    st = fun(shared, step)
    {cap_ps, [o, r, {a, lay, _}]} = Enum.split(st.params, length(caps))

    variants = [
      # The accumulator is :reuse, so a copy of the old value may live on.
      {%{st | params: cap_ps ++ [o, r, {a, lay, :reuse}]}, st.body},
      # The accumulator name is rebound before the call.
      {st,
       {:let, a, lay, :affine, {:con, "Acc", "acc", [lit(0), lit(0), {:var, "s"}]},
        {:call, "bump", [{:var, "s"}, {:var, "b"}, {:var, a}]}}}
    ]

    for {step_fun, step_body} <- variants do
      funs =
        Enum.map(shared, fn
          %{name: ^step} -> %{step_fun | body: step_body}
          f -> f
        end)

      out = Loop.funs(funs, book: emit)
      assert {:loop, _, _, _, _, ^z, ^s, _, b} = body(out, "scan")
      refute inout?(b)
    end
  end

  test "the accumulator is passed once and mentioned nowhere else" do
    assert Loop.acc_slot([{:var, "x"}, {:var, "a"}], "a") == {:ok, 1}
    assert Loop.acc_slot([{:var, "a"}, {:var, "a"}], "a") == :error
    assert Loop.acc_slot([{:su, {:var, "a"}}, {:var, "a"}], "a") == :error
    assert Loop.acc_slot([{:var, "x"}], "a") == :error
  end

  defp lit(n), do: {:wrd, :u64, {:lit, :u64, n}, []}

  defp inout?({:inout, _, _}), do: true
  defp inout?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&inout?/1)
  defp inout?(t) when is_list(t), do: Enum.any?(t, &inout?/1)
  defp inout?(_), do: false

  # -- Check ---------------------------------------------------------------

  test "Check accepts the loop image, with and without the book", %{emit: emit, loop: loop} do
    assert Check.check(loop, book: emit) == :ok
    assert Check.check(loop) == :ok
  end

  test "Check rejects malformed loops", %{emit: emit, loop: loop} do
    scan = body(loop, "scan")
    {:loop, caps, o, r, a, z, s, stop, b} = scan

    bad = [
      {{:loop, caps, o, r, a, z, s, stop, {:var, "outer"}}, "free variable outer"},
      {{:loop, caps, o, {"b", :slice, :affine}, a, z, s, stop, b}, "not distinct"},
      {{:loop, caps, {"b", :u64, :affine}, r, a, z, s, stop, b}, "octet must be :u8"},
      {{:loop, caps, o, r, a, lit(0), s, stop, b}, "loop start"},
      {{:loop, caps, o, r, a, z, lit(0), stop, b}, "loop input"},
      {{:loop, caps, o, r, a, z, s, stop, lit(0)}, "loop body"},
      {{:loop, caps, o, r, a, z, s, {"st", {:wrd, :wbool, true, []}}, b}, "loop stop"},
      {{:loop, caps, o, r, a, z, s, :sometimes, b}, "malformed loop stop"},
      {{:loop, caps, o, r, {"st", {:data, "Acc"}, :reuse}, z, s, stop, b},
       "updates the :reuse accumulator"},
      {{:inout, "bump", [{:var, "s"}, lit(0), z]}, "outside the tail of a loop body"},
      {{:loop, caps, o, r, a, z, s, stop, {:call, "bump", [{:var, "s"}, {:var, "b"}, b]}},
       "outside the tail of a loop body"},
      {{:loop, caps, o, r, a, z, s, stop, {:inout, "bump", [{:var, "s"}, {:var, "b"}, z]}},
       "does not pass the accumulator st once"}
    ]

    for {t, msg} <- bad do
      funs = Enum.map(loop, &if(&1.name == "scan", do: %{&1 | body: t}, else: &1))
      assert {:error, errs} = Check.check(funs, book: emit), msg
      assert Enum.any?(errs, &String.contains?(&1, msg)), "#{msg}: #{inspect(errs)}"
    end
  end

  test "Check rejects in-place metadata that does not hold", %{emit: emit, loop: loop} do
    bad = [
      {"bump", Map.put(fun(loop, "bump"), :inout, "s"), "does not have the return layout"},
      {"bump", Map.put(fun(loop, "bump"), :inout, "zz"), "is not a parameter"},
      {"bump", Map.delete(fun(loop, "bump"), :inout), "which has no inout parameter"},
      {"cellOf",
       %{fun(loop, "cellOf") | ret: {:data, "Cell"}, body: {:var, "c"}} |> Map.put(:inout, "c"),
       "is not a by-value struct"}
    ]

    for {name, f, msg} <- bad do
      funs = Enum.map(loop, &if(&1.name == name, do: f, else: &1))
      assert {:error, errs} = Check.check(funs, book: emit), msg
      assert Enum.any?(errs, &String.contains?(&1, msg)), "#{msg}: #{inspect(errs)}"
    end
  end

  test "Check accepts Loop of every corpus image, Share and A-normal too" do
    results =
      @corpus
      |> Enum.flat_map(&Path.wildcard/1)
      |> Enum.sort()
      |> Task.async_stream(&corpus_book/1, timeout: :infinity)
      |> Enum.flat_map(fn {:ok, r} -> r end)

    assert for({p, k, r, _} <- results, r != :ok, do: {p, k, r}) == []
    assert length(results) >= 3 * 70

    # The HTTP step book alone has a dozen folds in each image.
    assert Enum.sum(for {_, :shared, _, n} <- results, do: n) >= 30
  end

  defp corpus_book(path) do
    with {:ok, book} <- Muro.Load.file(path),
         emit = Muro.Prelude.for_emit(book),
         {:ok, plain} <- IR.elaborate(emit) do
      shared = Share.funs(plain)

      for {k, img} <- [plain: plain, shared: shared, anf: Anf.funs(shared, book: emit)] do
        out = Loop.funs(img, book: emit)
        bodies = Enum.map(out, & &1.body)

        r =
          cond do
            Loop.bfold?(bodies) -> {:bfold_left, path}
            Check.check(img, book: emit) != :ok -> :ok
            true -> Check.check(out, book: emit)
          end

        {path, k, r, Loop.loops(bodies)}
      end
    else
      _ -> []
    end
  end

  # -- Eval ----------------------------------------------------------------

  test "Eval agrees on every image and the reference", %{plain: plain, shared: shared, loop: loop} do
    for name <- ["scan", "firstLine", "nested", "tally"], input <- @inputs do
      want = Eval.call(plain, name, [{:bytes, input}])
      assert {:ok, _} = want
      assert Eval.call(shared, name, [{:bytes, input}]) == want, name
      assert Eval.call(loop, name, [{:bytes, input}]) == want, name
    end
  end

  test "the loop exit spends less fuel than the walk", %{plain: plain, loop: loop} do
    input = "a\n" <> String.duplicate("x", 200)
    want = Eval.call(plain, "firstLine", [{:bytes, input}])
    assert Eval.call(loop, "firstLine", [{:bytes, input}], fuel: 50) == want
    assert Eval.call(plain, "firstLine", [{:bytes, input}], fuel: 50) == {:error, :out_of_fuel}
  end

  test "the differential harness runs the loop image" do
    assert :loop in Muro.IRDiff.image_keys()
    {:ok, ctx} = Muro.IRDiff.load("examples/unboxed.muro")
    assert Loop.loops(Enum.map(ctx.loop, & &1.body)) > 0
    cases = Muro.IRDiff.check_run(ctx, "scan", 6)
    assert cases != []
    assert Enum.all?(cases, &match?({:agree, _}, &1)), inspect(cases)
  end

  # -- C -------------------------------------------------------------------

  test "C inlines the step, exits early, and updates the struct in place", %{dir: dir, emit: emit} do
    {:ok, {h, c}} = Muro.Emit.C.render(Muro.Grade.erase_book(emit), "loop_book")
    refute c =~ ~r/muro__step_\d+/
    assert c_fun(c, "Acc scan(") =~ ~r/muro__io_\d+\(\w+, \w+, &\w+\);/
    assert c_fun(c, "Acc firstLine(") =~ ~r/if \(\w+\) break;/
    assert c_fun(c, "Acc firstLine(") =~ ~r/muro__io_\d+\(\w+, &\w+\);/
    assert length(Regex.scan(~r/while \(/, c_fun(c, "uint64_t nested("))) == 2
    refute c_fun(c, "Cell *tally(") =~ "muro__io_"

    File.write!(Path.join(dir, "loop_book.h"), h)
    File.write!(Path.join(dir, "loop_book.c"), c)
    File.write!(Path.join(dir, "main.c"), main_c())

    {out, status} =
      System.cmd(
        "cc",
        ~w(-Wall -Wextra -Werror -std=c11 -O2 loop_book.c main.c -o main),
        cd: dir,
        stderr_to_stdout: true
      )

    assert status == 0, out
    {got, 0} = System.cmd(Path.join(dir, "main"), [])
    assert got == expected(emit)
  end

  test "the HTTP step book no longer passes its state by value per octet" do
    {:ok, book} = Muro.Load.file("test/http_step/request.muro")
    emit = book |> Muro.Prelude.for_emit() |> Muro.Grade.erase_book()
    {:ok, {_h, c}} = Muro.Emit.C.render(emit, "request")
    refute c =~ ~r/muro__step_\d+/
    refute c =~ ~r/HSt \w+\(muro__slice \w+, uint8_t \w+, muro__slice/

    assert c_fun(c, "HSt scan(") =~
             ~r/muro__io_\d+\(\w+, \w+, muro__inl_byteIndex\(\w+, \w+\), &\w+\);/

    assert c =~ ~r/static void muro__io_\d+\(muro__slice buf, uint8_t b, uint64_t i, HSt \*st\)/
  end

  defp c_fun(src, head) do
    [_, rest] = String.split(src, "\n" <> head, parts: 2)
    [text | _] = String.split(rest, "\n}\n", parts: 2)
    text
  end

  defp main_c do
    cases =
      @inputs
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {input, i} ->
        bytes = input |> :binary.bin_to_list() |> Enum.map_join(", ", &Integer.to_string/1)

        decl =
          if input == "",
            do: "static const uint8_t b#{i}[1] = {0};",
            else: "static const uint8_t b#{i}[] = {#{bytes}};"

        """
          {
            #{decl}
            muro__slice s = {b#{i}, #{byte_size(input)}};
            Acc a = scan(s);
            Acc f = firstLine(s);
            printf("%llu %llu %llu %llu %llu %llu %llu %llu\\n",
              (unsigned long long)nOf(a), (unsigned long long)marksOf(a),
              (unsigned long long)viewLen(a), (unsigned long long)nOf(f),
              (unsigned long long)marksOf(f), (unsigned long long)viewLen(f),
              (unsigned long long)nested(s), (unsigned long long)cellOf(tally(s)));
          }
        """
      end)

    """
    #include <stdio.h>
    #include "loop_book.h"
    int main(void) {
    #{cases}
      return 0;
    }
    """
  end

  # The same lines from `Muro.IR.Eval` on the elaborated image.
  defp expected(emit) do
    {:ok, plain} = IR.elaborate(emit)

    Enum.map_join(@inputs, "", fn input ->
      s = [{:bytes, input}]
      {:ok, a} = Eval.call(plain, "scan", s)
      {:ok, f} = Eval.call(plain, "firstLine", s)
      {:ok, n} = Eval.call(plain, "nested", s)
      {:ok, t} = Eval.call(plain, "tally", s)

      vals =
        [
          {"nOf", a},
          {"marksOf", a},
          {"viewLen", a},
          {"nOf", f},
          {"marksOf", f},
          {"viewLen", f}
        ]
        |> Enum.map(fn {g, v} ->
          {:ok, {:word, :u64, x}} = Eval.call(plain, g, [v])
          x
        end)

      {:ok, {:word, :u64, c}} = Eval.call(plain, "cellOf", [t])
      {:word, :u64, nv} = n
      Enum.join(vals ++ [nv, c], " ") <> "\n"
    end)
  end
end

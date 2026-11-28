defmodule Muro.IRDiffTest do
  # Differential tests of `Muro.IR.Eval` against `Muro.Check.normalize/3`.
  # See test/ir_diff_helper.exs for what is compared and how inputs are
  # generated. The HTTP step book is test/muro_ir_http_diff_test.exs.
  use ExUnit.Case, async: true

  Code.require_file("ir_diff_helper.exs", __DIR__)

  alias Muro.IRDiff

  @moduletag timeout: 600_000

  # Every book under examples, test/fixtures, and lib/muro/std (the
  # standard library). The HTTP step book (test/http_step) has its own module.
  @corpus ["examples/**/*.muro", "test/fixtures/**/*.muro", "lib/muro/std/*.muro"]

  # Books that do not check on their own: negative examples, library
  # fragments that are only imported, and books with unsupplied params.
  @not_books ~w(
    examples/bad_alias.muro examples/bad_cons.muro examples/bad_dup.muro
    examples/bad_field_choice.muro examples/bad_pair_bindings.muro
    examples/bad_positive.muro examples/bad_second_field.muro
    examples/bad_shared.muro examples/bad_stuck.muro examples/bad_wrap.muro
    examples/cshrl/lib/agent.muro examples/cshrl/lib/core.muro
    examples/cshrl/lib/finder.muro examples/cshrl/lib/placement.muro
    examples/cshrl/lib/successor.muro examples/cshrl/lib/successor_sum.muro
    examples/cshrl/lib/synth.muro examples/cycle_empty.muro
    examples/fill/add1.muro examples/may-fail-hold.muro
    examples/may-fail-missing.muro test/fixtures/choreo_untold.muro
  )

  # Books with no run either image elaborates: sessions, families,
  # temporal and may-fail books, and books whose runs are all evidence.
  @no_runs ~w(
    examples/async-meetings.muro examples/cshrl/std/bool.muro
    examples/even_dec.muro examples/keyed-commands.muro
    examples/keyed-release.muro examples/keyed-slots.muro
    examples/may-fail-control.muro
    examples/may-fail-free.muro examples/may-fail-send.muro
    examples/ping.muro examples/prefix.muro examples/temporal.muro
    lib/muro/std/classical.muro test/fixtures/reason_match.muro
  )

  # Runs whose generated inputs never reach a value under normalize:
  # `lookup` takes a `Fin n` and a `Vec A n`, and the generator does not
  # tie the two indices, so the reference is stuck on every input.
  @untied [{"examples/vec.muro", "lookup"}]

  @cases 4

  defp corpus do
    @corpus
    |> Enum.flat_map(&Path.wildcard/1)
    |> Enum.sort()
  end

  defp check_file(path) do
    case IRDiff.load(path) do
      {:ok, ctx} ->
        runs =
          for name <- IRDiff.all_runs(ctx) do
            {name, IRDiff.check_run(ctx, name, @cases)}
          end

        {path, {:ok, runs}}

      {:skip, reason} ->
        {path, {:skip, reason}}
    end
  end

  defp agreed_on?({_, _, {:agree, ks}}, image), do: image in ks
  defp agreed_on?(_, _), do: false

  test "every run of the corpus agrees with normalize on generated inputs" do
    results =
      corpus()
      |> Task.async_stream(&check_file/1, timeout: :infinity, ordered: true)
      |> Enum.map(fn {:ok, r} -> r end)

    skipped = for {path, {:skip, reason}} <- results, do: {path, reason}

    assert Enum.sort(for {p, :does_not_check} <- skipped, do: p) == Enum.sort(@not_books)
    assert Enum.sort(for {p, {:no_image, _}} <- skipped, do: p) == Enum.sort(@no_runs)

    cases = for {path, {:ok, runs}} <- results, {name, cs} <- runs, c <- cs, do: {path, name, c}
    mismatches = for {path, name, {:mismatch, d}} <- cases, do: {path, name, d}
    assert mismatches == []

    # Every run is compared on at least one input. A skip is an input the
    # reference does not reduce to a first-order value (an ill-typed
    # generated index, for example) or that exhausts Eval's fuel.
    runs = cases |> Enum.group_by(fn {p, n, _} -> {p, n} end)

    never =
      for {key, cs} <- runs, not Enum.any?(cs, &match?({_, _, {:agree, _}}, &1)), do: key

    assert Enum.sort(never) == Enum.sort(@untied)
    assert map_size(runs) >= 1000

    agreed = Enum.count(cases, &match?({_, _, {:agree, _}}, &1))
    assert agreed >= 0.95 * length(cases)

    # The closure image is compared too: on runs only it elaborates
    # (higher-order runs), and beside the default image everywhere else.
    clos = Enum.count(cases, &agreed_on?(&1, :closures))
    plain = Enum.count(cases, &agreed_on?(&1, :shared))
    assert clos > 1000
    assert plain > 1000

    # Every image in A-normal form agrees wherever its source image does.
    # So does the loop image C emits (`Muro.IR.Loop`), beside the shared
    # image it lowers.
    for {img, src} <- [anf: :plain, anf_shared: :shared, anf_closures: :closures, loop: :shared] do
      assert Enum.count(cases, &agreed_on?(&1, img)) == Enum.count(cases, &agreed_on?(&1, src))
    end
  end

  test "every word, string, and bytes operation agrees on its edge values" do
    path = "test/fixtures/ir_eval_ops.muro"
    {:ok, ctx} = IRDiff.load(path)
    assert ctx.refused == %{plain: %{}, closures: %{}}

    names =
      for n <- IRDiff.all_runs(ctx),
          String.ends_with?(IRDiff.find_def(ctx.book, n).file, "ir_eval_ops.muro"),
          do: n

    # 4 kinds × 23 operations, then 16 string, bytes, opt, and pair runs.
    assert length(names) == 4 * 23 + 16

    cases =
      names
      |> Task.async_stream(&{&1, IRDiff.check_edges(ctx, &1)}, timeout: :infinity)
      |> Enum.flat_map(fn {:ok, {n, cs}} -> Enum.map(cs, &{n, &1}) end)

    assert for({n, {:mismatch, d}} <- cases, do: {n, d}) == []
    assert for({n, {:skip, r}} <- cases, do: {n, r}) == []
    assert Enum.all?(cases, fn {_, {:agree, ks}} -> ks == IRDiff.image_keys() end)
    assert length(cases) > 8000
  end

  describe "verdict" do
    @oom {:error, :out_of_fuel}
    defp no_ref, do: fn -> flunk("the reference was asked") end

    test "a wrong image beside a later out-of-fuel image is a mismatch" do
      got = [plain: {:ok, {:nat, 0}}, shared: {:ok, {:nat, 5}}, closures: @oom]
      assert {:mismatch, %{got: ^got}} = IRDiff.verdict("plus", [], got, no_ref())

      # Both stopping images agree with each other but not with normalize.
      got = [plain: {:ok, {:nat, 0}}, shared: {:ok, {:nat, 0}}, closures: @oom]
      ref = fn -> {:ok, {:nat, 5}} end
      assert {:mismatch, %{ref: {:nat, 5}}} = IRDiff.verdict("plus", [], got, ref)
    end

    test "out of fuel skips only when every stopping image agrees" do
      assert {:skip, :eval_out_of_fuel} =
               IRDiff.verdict("f", [], [plain: @oom, shared: @oom, closures: @oom], no_ref())

      got = [plain: {:ok, {:nat, 5}}, shared: {:ok, {:nat, 5}}, closures: @oom]
      ref = fn -> {:ok, {:nat, 5}} end
      assert {:skip, :eval_out_of_fuel} = IRDiff.verdict("f", [], got, ref)
      assert {:skip, :ref_timeout} = IRDiff.verdict("f", [], got, fn -> {:skip, :ref_timeout} end)

      all = [plain: {:ok, {:nat, 5}}, shared: {:ok, {:nat, 5}}, closures: {:ok, {:nat, 5}}]
      assert {:agree, [:plain, :shared, :closures]} = IRDiff.verdict("f", [], all, ref)
      assert {:mismatch, %{got: :no_image}} = IRDiff.verdict("f", [], [], no_ref())
    end

    test "compare observes every image before it skips" do
      {:ok, ctx} = IRDiff.load("examples/half_ok.muro")

      body = fn funs, b ->
        Enum.map(funs, &if(&1.name == "plus", do: %{&1 | body: b}, else: &1))
      end

      [{n, _, _}, {m, _, _}] = Enum.find(ctx.plain, &(&1.name == "plus")).params
      loop = {:call, "plus", [{:var, n}, {:var, m}]}

      # The A-normal images follow the images they come from.
      ctx =
        IRDiff.with_anf(%{
          ctx
          | plain: body.(ctx.plain, :ze),
            closures: body.(ctx.closures, loop)
        })

      ctx = Map.put(ctx, :eval_fuel, 1000)
      args = for v <- [{:nat, 2}, {:nat, 3}], do: {IRDiff.term!(ctx, v), v}

      assert {:mismatch, %{got: got}} = IRDiff.compare(ctx, "plus", args)

      assert got == [
               plain: {:ok, {:nat, 0}},
               shared: {:ok, {:nat, 5}},
               closures: {:error, :out_of_fuel},
               anf: {:ok, {:nat, 0}},
               anf_shared: {:ok, {:nat, 5}},
               anf_closures: {:error, :out_of_fuel},
               loop: {:ok, {:nat, 5}}
             ]
    end
  end

  test "edge values skip erased parameters" do
    dir = Path.join(System.tmp_dir!(), "muro_ir_diff_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    path = Path.join(dir, "erased.muro")

    File.write!(path, """
    def keep : run Π (- n : Nat) → Π (x : U8) → U8 := λ (- n : Nat) → λ (x : U8) → x
    """)

    {:ok, ctx} = IRDiff.load(path)
    d = IRDiff.find_def(ctx.book, "keep")
    assert [[{_filler, :gone}], live] = IRDiff.edge_lists(ctx, d.type, d.body)
    assert length(live) == length(IRDiff.word_edges(:u8))

    cases = IRDiff.check_edges(ctx, "keep")
    assert length(cases) == length(live)
    keys = IRDiff.image_keys()
    assert Enum.all?(cases, &match?({:agree, ^keys}, &1))
  end

  test "generated bytes keep every octet" do
    {:ok, ctx} = IRDiff.load("test/fixtures/ir_eval_ops.muro")
    d = IRDiff.find_def(ctx.book, "blen")
    st = IRDiff.seed({ctx.path, "blen"})

    {lens, _} =
      Enum.map_reduce(20..400, st, fn i, st ->
        {:ok, [{_t, {:bytes, b}}], st} = IRDiff.gen_args(ctx, d, i, st)
        {byte_size(b), st}
      end)

    lens = MapSet.new(lens)

    assert lens == MapSet.new(0..12)
  end

  test "generated inputs are the same on every run" do
    {:ok, ctx} = IRDiff.load("examples/tree.muro")
    d = IRDiff.find_def(ctx.book, "size")
    st = IRDiff.seed({ctx.path, "size"})
    assert IRDiff.gen_args(ctx, d, 5, st) == IRDiff.gen_args(ctx, d, 5, st)
  end
end

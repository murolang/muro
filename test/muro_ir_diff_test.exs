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
    examples/keyed-slots.muro examples/may-fail-control.muro
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
    assert Enum.all?(cases, fn {_, {:agree, ks}} -> ks == [:plain, :shared, :closures] end)
    assert length(cases) > 8000
  end

  test "generated inputs are the same on every run" do
    {:ok, ctx} = IRDiff.load("examples/tree.muro")
    d = IRDiff.find_def(ctx.book, "size")
    st = IRDiff.seed({ctx.path, "size"})
    assert IRDiff.gen_args(ctx, d, 5, st) == IRDiff.gen_args(ctx, d, 5, st)
  end
end

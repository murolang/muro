defmodule Muro.CLI.Mutate do
  @moduledoc false

  @switches [
    only: :keep,
    json: :boolean,
    fuel: :integer,
    max_mutants_per_def: :integer,
    max_survivors: :integer
  ]

  @doc false
  def run(args) do
    {opts, paths, invalid} = OptionParser.parse(args, strict: @switches)

    cond do
      invalid != [] ->
        {:raise, "", "unknown option: #{inspect(invalid)}"}

      length(paths) != 1 ->
        {:raise, "", "expected one path"}

      Keyword.get(opts, :fuel, Muro.Check.default_fuel()) <= 0 ->
        {:raise, "", "--fuel must be a positive integer"}

      Keyword.get(opts, :max_mutants_per_def, Muro.Mutate.default_max_mutants()) < 0 ->
        {:raise, "", "--max-mutants-per-def must be a non-negative integer"}

      survivor_negative?(Keyword.get(opts, :max_survivors)) ->
        {:raise, "", "--max-survivors must be a non-negative integer"}

      true ->
        report(hd(paths), opts)
    end
  end

  defp survivor_negative?(value) when is_integer(value), do: value < 0
  defp survivor_negative?(_value), do: false

  defp report(path, opts) do
    fuel = Keyword.get(opts, :fuel, Muro.Check.default_fuel())
    max_m = Keyword.get(opts, :max_mutants_per_def, Muro.Mutate.default_max_mutants())
    max_s = Keyword.get(opts, :max_survivors)

    report_opts = [
      only: Keyword.get_values(opts, :only),
      fuel: fuel,
      max_mutants_per_def: max_m,
      max_survivors: max_s,
      # During classification, before the report, so the Mix task and the
      # executable print the same progress line.
      on_mutant: &progress/1
    ]

    case Muro.Mutate.report(path, report_opts) do
      {:ok, report} ->
        {:ok, render(report, opts), ""}

      {:error, :survivors, report} ->
        {:exit, 1, render(report, opts), [survivor_line(report, max_s)]}

      {:error, :book, message} ->
        {:exit, 2, "Muro v#{Mix.Tasks.Muro.version()}\n",
         [message, "refusing to mutate a book that does not check"]}

      {:error, :only, message} ->
        {:raise, "", message}
    end
  end

  defp render(report, opts) do
    text =
      if Keyword.get(opts, :json, false) do
        Muro.Mutate.render_json(report)
      else
        Muro.Mutate.render(report)
      end

    String.trim_trailing(text, "\n") <> "\n"
  end

  defp survivor_line(report, max_s) do
    "#{report.summary.surviving} survivors exceed --max-survivors #{max_s}"
  end

  defp progress(mutant) do
    IO.puts(:stderr, "#{mutant.id} #{mutant.operator} #{mutant.outcome}")
  end
end

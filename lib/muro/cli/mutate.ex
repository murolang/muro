defmodule Muro.CLI.Mutate do
  @moduledoc false

  @doc false
  def switches, do: Enum.map(options(), &{&1.name, &1.type})

  @doc false
  def options do
    fuel = Integer.to_string(Muro.Check.default_fuel())
    cap = Integer.to_string(Muro.Mutate.default_max_mutants())

    [
      %{
        name: :only,
        type: :keep,
        value: "NAME",
        default: "every run definition in the file",
        doc:
          "Mutate this run definition. Repeat the flag for more than one. A name that is not a run definition in the file is an error. The report stays in file order."
      },
      %{
        name: :json,
        type: :boolean,
        default: "false",
        doc:
          "Print one JSON object instead of the text report. The progress lines on standard error are unchanged. A book that does not check is still refused as text, not as JSON."
      },
      %{
        name: :fuel,
        type: :integer,
        value: "N",
        default: fuel,
        doc:
          "The checker's fuel for the original check and for every re-check. The equivalence probe uses a quarter of N, at least 1, and less than N when N is greater than 1. out of fuel is not acceptance."
      },
      %{
        name: :max_mutants_per_def,
        type: :integer,
        value: "N",
        default: cap,
        doc:
          "Stop after N candidates of each definition. 0 prints the header and no mutants. A candidate whose body is the original body is not counted."
      },
      %{
        name: :max_survivors,
        type: :integer,
        value: "N",
        default: "omitted, and survivors do not change the exit code",
        doc:
          "After the report, exit 1 when more than N mutants survive. The report is printed first. The error line names both counts."
      }
    ]
  end

  @doc false
  def help do
    Muro.CLI.Text.page([
      Muro.CLI.Text.prose("""
      muro mutate reads one .muro file and changes each run definition in small, type-preserving ways, then checks the book again. Evidence, spec, data, and the prelude are left as written. A killed mutant names the evidence that now fails. A surviving mutant type-checks, does not convert with the original body, and leaves every re-checked definition checking. A survivor means the evidence does not rule the change out. It is not acceptance of the original program. Each classified mutant prints "<id> <operator> <outcome>" on standard error as it is classified. The report follows on standard output. out of fuel is counted on its own. It is not acceptance.
      """),
      Muro.CLI.Text.section(
        "USAGE",
        Muro.CLI.Text.pre([
          "muro mutate path.muro [--only NAME] [--json] [--fuel N]",
          "    [--max-mutants-per-def N] [--max-survivors N]"
        ])
      ),
      Muro.CLI.Text.section(
        "ARGUMENTS",
        Muro.CLI.Text.arguments([
          {"path.muro", "Required. The book to mutate. Exactly one path."}
        ])
      ),
      Muro.CLI.Text.section("OPTIONS", Muro.CLI.Text.options(options())),
      Muro.CLI.Text.section(
        "EXAMPLES",
        Muro.CLI.Text.examples(
          [
            {"muro mutate book.muro --only one --max-mutants-per-def 1",
             "Classify one candidate of the definition one."},
            {"muro mutate book.muro --only one --max-mutants-per-def 0 --json",
             "Print the JSON summary and no mutants."},
            {"muro mutate book.muro --only one --max-mutants-per-def 0 --max-survivors 0",
             "Exits 0 when nothing survives."}
          ],
          "\n\n"
        )
      ),
      Muro.CLI.Text.section(
        "EXIT CODES",
        Muro.CLI.Text.exits([
          {"0",
           "The book checked, and survivors are within --max-survivors when that flag is set."},
          {"1",
           "Survivors exceed --max-survivors, or a flag, the path, or an --only name is refused."},
          {"2", "The book does not check. It is not mutated."}
        ])
      ),
      Muro.CLI.Text.section(
        "LEARN MORE",
        Muro.CLI.Text.pre(["https://muro-lang.dev/docs/mutate"])
      )
    ])
  end

  @doc false
  def run(args) do
    {opts, paths, invalid} = OptionParser.parse(args, strict: switches())

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

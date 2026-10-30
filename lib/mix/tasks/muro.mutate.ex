defmodule Mix.Tasks.Muro.Mutate do
  use Mix.Task

  @shortdoc "Report which theorems constrain each run definition"

  @moduledoc """
  Mutate each `run` definition and report which evidence fails.

      mix muro.mutate path.muro
      mix muro.mutate path.muro --only half
      mix muro.mutate path.muro --only half --json
      mix muro.mutate path.muro --max-survivors 0
      mix muro.mutate path.muro --fuel 2000 --max-mutants-per-def 100

  The book is checked first. A book that does not check is refused
  (exit 2) and is not mutated. `--only` may be repeated. A name that is
  not a `run` definition in the file is an error. `--max-mutants-per-def`
  caps candidates per definition (default
  `Muro.Mutate.default_max_mutants/0`, and `0` reports none).
  `--max-survivors N` exits 1 when more than `N` mutants survive.
  Omitting it does not limit survivors. `--fuel` is the checker's fuel
  for the original check and for every re-check. The equivalence probe
  uses a quarter of it (at least 1, and less than `--fuel` when `--fuel`
  is greater than 1). `--json` prints the report as one JSON object.
  Each classified mutant prints `<id> <operator> <outcome>` on standard
  error as it is classified. A run with no mutants prints none.

  Outcomes are `killed`, `surviving`, `equivalent`, `out_of_fuel`, and
  `discarded`. A mutant that converts with the original body is
  `equivalent`. Running out of fuel is `out_of_fuel`. The manual page
  is `manual/mutate.md`.
  """

  @switches [
    only: :keep,
    json: :boolean,
    fuel: :integer,
    max_mutants_per_def: :integer,
    max_survivors: :integer
  ]

  def run(args) do
    Mix.Tasks.Muro.ensure_started()
    {opts, paths, invalid} = OptionParser.parse(args, strict: @switches)

    if invalid != [] do
      Mix.raise("unknown option: #{inspect(invalid)}")
    end

    path =
      case paths do
        [path] -> path
        _ -> Mix.raise("expected one path")
      end

    fuel = Keyword.get(opts, :fuel, Muro.Check.default_fuel())

    if fuel <= 0 do
      Mix.raise("--fuel must be a positive integer")
    end

    max_m = Keyword.get(opts, :max_mutants_per_def, Muro.Mutate.default_max_mutants())

    if max_m < 0 do
      Mix.raise("--max-mutants-per-def must be a non-negative integer")
    end

    max_s = Keyword.get(opts, :max_survivors)

    if is_integer(max_s) and max_s < 0 do
      Mix.raise("--max-survivors must be a non-negative integer")
    end

    report_opts = [
      only: Keyword.get_values(opts, :only),
      fuel: fuel,
      max_mutants_per_def: max_m,
      max_survivors: max_s,
      on_mutant: fn m ->
        IO.puts(:stderr, "#{m.id} #{m.operator} #{m.outcome}")
      end
    ]

    case Muro.Mutate.report(path, report_opts) do
      {:ok, report} ->
        emit(report, opts)

      {:error, :survivors, report} ->
        emit(report, opts)
        Mix.shell().error(survivor_line(report, max_s))
        exit({:shutdown, 1})

      {:error, :book, msg} ->
        Mix.shell().info("Muro v#{Mix.Tasks.Muro.version()}")
        Mix.shell().error(msg)
        Mix.shell().error("refusing to mutate a book that does not check")
        exit({:shutdown, 2})

      {:error, :only, msg} ->
        Mix.raise(msg)
    end
  end

  defp emit(report, opts) do
    text =
      if Keyword.get(opts, :json, false) do
        Muro.Mutate.render_json(report)
      else
        Muro.Mutate.render(report)
      end

    text
    |> String.trim_trailing("\n")
    |> Mix.shell().info()
  end

  defp survivor_line(report, max_s) do
    "#{report.summary.surviving} survivors exceed --max-survivors #{max_s}"
  end
end

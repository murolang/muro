defmodule Mix.Tasks.Muro.Check do
  use Mix.Task

  @shortdoc "Type-check a .muro file or the built-in half_ok book"

  @moduledoc """
  Type-check a `.muro` file, or the built-in `half_ok` book when no path is
  given.

      mix muro.check
      mix muro.check path.muro
      mix muro.check --fuel 10000 path.muro

  `--fuel` bounds how far the checker reduces (default
  `Muro.Check.default_fuel/0`). Running out is reported as an error, not
  as a type error; raise the fuel and check again. Every definition is
  checked, and every error is reported, in book order.

  The first line is the version that checked the book (`Muro v` and the
  version from the application spec). On success the next line is
  `All terms check. Evidence never becomes a run.` When the book imports
  packages, one `conforms to <name> <version> (sha256 <hash>)` line
  follows for each package it loaded. A book that imports no package,
  and the built-in check with no path, print only those two lines.
  A refusal prints the errors after the version line.
  """

  @switches [fuel: :integer]

  def run(args) do
    Mix.Tasks.Muro.ensure_started()
    Mix.shell().info("Muro v#{Mix.Tasks.Muro.version()}")

    {opts, paths, invalid} = OptionParser.parse(args, strict: @switches)

    if invalid != [] do
      Mix.raise("unknown option: #{inspect(invalid)}")
    end

    fuel = Keyword.get(opts, :fuel, Muro.Check.default_fuel())

    if fuel <= 0 do
      Mix.raise("--fuel must be a positive integer")
    end

    result =
      case paths do
        [] -> Muro.Check.check_sig(Muro.Example.book(), fuel: fuel)
        [path] -> Muro.conforms(path, fuel: fuel)
        _ -> Mix.raise("expected at most one path")
      end

    case result do
      :ok ->
        Mix.shell().info("All terms check. Evidence never becomes a run.")

      {:ok, lines} ->
        Mix.shell().info("All terms check. Evidence never becomes a run.")
        Enum.each(lines, fn line -> Mix.shell().info(line) end)

      {:error, e} ->
        Mix.raise(e)
    end
  end
end

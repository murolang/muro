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

  def run(args) do
    Mix.Tasks.Muro.ensure_started()
    Muro.CLI.Output.mix(Muro.CLI.Check.run(args))
  end
end

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
  Omitting it does not limit survivors. `--fuel` is the checker's fuel,
  the same bound `mix muro.check` uses, and it applies to the original
  check. `--json` prints the report as one JSON object.

  Outcomes are `killed`, `surviving`, `equivalent`, `out_of_fuel`, and
  `discarded`. A mutant that converts with the original body is
  `equivalent`. Running out of fuel is `out_of_fuel`. The manual page
  is `manual/mutate.md`.
  """

  def run(args) do
    Mix.Tasks.Muro.ensure_started()
    Muro.CLI.Output.mix(Muro.CLI.Mutate.run(args))
  end
end

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

  def run(args) do
    Mix.Tasks.Muro.ensure_started()
    Muro.CLI.Output.mix(Muro.CLI.Mutate.run(args))
  end
end

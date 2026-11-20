defmodule Mix.Tasks.Muro.Synth do
  use Mix.Task

  @shortdoc "Search a version space of predicate programs"

  @moduledoc """
  Search a version space against a checked environment.

      mix muro.synth path.muro
      mix muro.synth path.muro --on traces
      mix muro.synth path.muro --oracle trace
      mix muro.synth path.muro --oracle successor --depth 0
      mix muro.synth path.muro --out out.muro --fuel 2000

  `--on` names the procedure. `traces` is the version-space search
  on the book's `step` and the observations that `step` supports.
  It is the only accepted value. A book that defines `step` selects
  `traces` when `--on` is omitted. A book with no `step` has no
  observations to synthesize against. The command refuses it, and
  the message does not name a flag. An unknown `--on` value is
  refused, and the message lists the accepted values.

  The book is checked first. A book that does not check is refused
  (exit 2) and is not searched. The search calls that book's emitted
  `step`. `--oracle` is `trace` (the default), `successor`, or
  `coind-homo`. `--depth` is the initial predicate depth. An empty
  version space is searched one depth further. `--out` writes the
  policy book and must not already exist. Without it, the book is
  printed on standard output and the report on standard error.

  The smallest program that matches every observation is the policy
  the book deploys, and `eval` runs it. A score does not decide who
  survives. Exit 0 is a checked homomorphism for that ranking, on
  the same `step`. This task exits 1 when it reports a policy whose
  environment does not define the homomorphism, an empty space, a
  counterexample, a homomorphism that is not derivable, a silent
  oracle, or features that cannot separate two carriers. `--json`
  prints that report as one JSON object.
  The manual page is `manual/synth.md`.
  """

  def run(args) do
    Mix.Tasks.Muro.ensure_started()
    Muro.CLI.Output.mix(Muro.CLI.Synth.run(args))
  end
end

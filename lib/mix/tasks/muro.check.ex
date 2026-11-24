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

  `import "std:file.muro"` loads a book of the ordinary library compiled
  into this copy of muro. The same bytes are used from a Hex install,
  from the self-contained executable, and from a checkout. A missing
  name lists the books. A path that leaves the library is refused.
  `import "pkg:name/file.muro"` loads a package file. A relative path
  is relative to the importing file. A file reached twice joins once.

  The first line is the version that checked the book (`Muro v` and the
  version from the application spec). Each keyed family then prints
  `family <name>: <meeting> per key of <kind>`, and each temporal
  declaration that holds prints `temporal <name>: holds in <n> reachable
  states`. A family marked `may redeliver` prints that mark on the same
  line. A formula that says `relies idempotent init`, and holds, prints
  `<name>: depends on contract idempotent init` on the next line.
  `may redeliver` is not that line. Those lines are in book order. Each choreography then prints
  one `choreography <name>: <role> with <role> = <session>` line per
  ordered pair of roles. Each definition the entry file reaches that
  depends on an axiom and is not a `run` then prints
  `<name>: depends on <File.axiom>`. The entry file reaches every
  definition it declares, and every definition mentioned from one it
  reaches. An imported definition that chain does not mention is not
  printed. Several axioms on one line are separated by `, `, in the
  order the axioms are declared. On success the next line is
  `All terms check. Evidence never becomes a run.` A book with no
  family, no temporal declaration, no choreography, and no reached
  definition that depends on an axiom prints that line immediately
  after the version. When the book imports packages, one
  `conforms to <name> <version> (sha256 <hash>)` line follows for each
  package it loaded. A book that imports no package, and the built-in
  check with no path, print only those two lines. A refusal prints the
  errors after the version line. A `run` that depends on an axiom is
  one of those errors, including a `run` in an imported book, and it
  is not emitted. A `spec` or `evidence` definition that is reached
  and depends on an axiom is a line, not an error.
  """

  def run(args) do
    Mix.Tasks.Muro.ensure_started()
    Muro.CLI.Output.mix(Muro.CLI.Check.run(args))
  end
end

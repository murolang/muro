defmodule Mix.Tasks.Muro.Gen do
  use Mix.Task

  @shortdoc "Write committed modules from the muro manifest"

  @moduledoc """
  Write the modules listed in the project manifest, or check that the
  committed files still match their books.

      mix muro.gen
      mix muro.gen --check

  The manifest is `muro.exs` at the project root, or a `:muro` key in
  `mix.exs`. If both exist, the task stops and names both. `muro:` is
  the version the books are checked with. It must equal the running
  Muro version. A mismatch is an error and names both versions.
  `fuel:` is optional. `modules:` lists `{book, module, target}` or
  `{book, module, target, opts}`. A 3-tuple emits Elixir. `opts` may
  set `kind: :exunit`, `kind: :fsm`, `kind: :c`, `kind: :rust`,
  `kind: :zig`, or `kind: :asm`, and for `:exunit`, `impl: An.Adapter` and
  `imports: true`. A `:c`, `:rust`, `:zig`, or `:asm` entry may omit the
  module (`{book, target, [kind: :c]}`). `:c` also writes the `.h`
  beside the `.c`. `imports:` is a boolean, default `false`, and is
  valid only for `:exunit`. `imports: true` also collects the closed
  equations of the files that book imports directly. An ExUnit target
  is usually `test/<name>_test.exs`. After the `written` or
  `unchanged` line, one `skipped <target>: …` line is printed per
  equation the suite cannot express. `--check` does not print those
  lines. A `kind: :exunit` entry checks a library of unsupplied
  `param`s. A `kind: :elixir` entry still refuses it.

  `muro_deps:` lists packages `import "pkg:..."` may load. `mix muro.gen`
  does not fetch them. A book that imports a package carries one
  `# Conforms to` header line per package, and the book hash includes
  the package files under `muro_deps/`.

  `mix muro.gen` checks every listed book with that fuel before it
  writes. If any book fails, it prints each failure and writes
  nothing. Otherwise it formats each module with the project's
  `.formatter.exs` when that file exists, adds the header, and writes
  the target, creating directories. One line per target says `written`
  or `unchanged`. A package-using target then prints each
  `conforms to` line indented by two spaces. An ExUnit target then lists
  each skipped equation. An unchanged file is not rewritten.

  `mix muro.gen --check` writes nothing. It exits non-zero and lists
  every problem: a book that does not check, a missing target, a stale
  target (the book changed), a hand-edited target (the book is
  unchanged and the body hash does not match), a target that differs
  from what its book emits, and a header that names a different Muro
  version. Each line names the target and the book. When every target
  matches, the task prints `ok`.

  The header, the hashes, and the manifest are documented in
  `Muro.Gen` and `Muro.Manifest`.
  """

  def run(args) do
    Mix.Tasks.Muro.ensure_started()
    Muro.CLI.Output.mix(Muro.CLI.Gen.run(args))
  end
end

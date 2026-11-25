defmodule Mix.Tasks.Muro.Gen do
  use Mix.Task

  @shortdoc "Write committed modules from the muro manifest"

  @moduledoc """
  Write the modules listed in the project manifest, or check that the
  committed files still match their books.

      mix muro.gen
      mix muro.gen --check
      mix muro.gen --skip-check

  The manifest is `muro.exs` at the project root, or a `:muro` key in
  `mix.exs`. If both exist, the task stops and names both. `muro:` is
  the version the books are checked with. It must equal the running
  Muro version. A mismatch is an error and names both versions.
  `fuel:` is optional. `modules:` lists `{book, module, target}` or
  `{book, module, target, opts}`. A 3-tuple emits Elixir. `opts` may
  set `kind: :exunit`, `kind: :pytest`, `kind: :rust_test`, `kind: :fsm`,
  `kind: :c`, `kind: :rust`, `kind: :zig`, `kind: :asm`, `kind: :otp`,
  `kind: :js`, or `kind: :mbi`.
  For `:exunit`, `impl: An.Adapter` and `imports: true`. For `:pytest`,
  `impl:` is a Python module name. For `:rust_test`, `impl:` is a Rust
  path. A `:c`, `:rust`, `:zig`, `:asm`, `:otp`, `:js`, `:mbi`,
  `:pytest`, or `:rust_test` entry may omit the module
  (`{book, target, [kind: :c]}`). `:c` also writes the `.h`
  beside the `.c`. `:js` also writes the `.d.ts` beside the `.mjs`.
  An `:otp` target ends with `.ex` and is formatted the same way as
  an Elixir target. An `:mbi` target ends with `.mbi` and is written
  without a gen header. Formatting is left alone for `:c`, `:rust`,
  `:zig`, `:asm`, `:js`, `:pytest`, `:rust_test`, and `:mbi`. A pytest
  target ends with `.py`. A Rust test target ends with `.rs`.
  `imports:` is
  a boolean, default `false`, and is valid for `:exunit`, `:pytest`,
  and `:rust_test`. `imports: true` also collects the closed equations
  of the files that book imports directly. An ExUnit target is usually
  `test/<name>_test.exs`. After the `written` or `unchanged` line,
  one `skipped <target>: …` line is printed per equation the suite
  cannot express. `--check` does not print those lines. A
  `kind: :exunit`, `kind: :pytest`, or `kind: :rust_test` entry checks
  a library of unsupplied `param`s. A `kind: :elixir` entry still
  refuses it.

  `muro_deps:` lists packages `import "pkg:..."` may load. `mix muro.gen`
  does not fetch them. A book that imports a package carries one
  `# Conforms to` header line per package, and the book hash includes
  the package files under `muro_deps/`.

  `mix muro.gen` type-checks each book once, with that fuel, then
  emits every target of that book from that copy. A C target's `.c`
  and `.h` come from the same copy, and so do a JavaScript target's
  `.mjs` and `.d.ts`. If any book fails, it prints each failure and
  writes nothing. A book that checks, and that the backend then
  refuses, is reported as refused by that backend, and nothing is
  written. When every book is emitted, it formats an Elixir, ExUnit,
  FSM, or OTP target with the project's `.formatter.exs` when that
  file exists, adds the header except on an `:mbi` image, and writes
  the target, creating directories. One line per
  target says `written` or `unchanged`. A package-using target then
  prints each `conforms to` line indented by two spaces. An ExUnit
  target then lists each skipped equation. An unchanged file is not
  rewritten.

  `mix muro.gen --check` writes nothing. It type-checks each book
  once and compares every committed file with the bytes that copy
  emits. It exits non-zero and lists every problem: a book that does
  not check, a missing target, a stale target (the book changed), a
  hand-edited target (the book is unchanged and the body hash does
  not match), a target that differs from what its book emits, a
  header that names a different Muro version, and, when that header
  is older than the Elixir spelling rule, the host names that
  changed. Each line names the target and the book. When every
  target matches, the task prints `ok`.

  `--skip-check` does not type-check. The caller has already checked
  the books. The files are still loaded, and a book that does not
  parse still fails. `mix muro.gen --check --skip-check` still
  compares bytes and still fails when a committed file is not what
  the book emits. The default, without the flag, type-checks.

  The header, the hashes, and the manifest are documented in
  `Muro.Gen` and `Muro.Manifest`.
  """

  def run(args) do
    Mix.Tasks.Muro.ensure_started()
    Muro.CLI.Output.mix(Muro.CLI.Gen.run(args))
  end
end

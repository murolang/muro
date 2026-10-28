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
  `fuel:` is optional. `modules:` lists `{book, module, target}`.

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
  `conforms to` line indented by two spaces. An unchanged file is not
  rewritten.

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

  @switches [check: :boolean]

  def run(args) do
    Mix.Tasks.Muro.ensure_started()

    {opts, rest, invalid} = OptionParser.parse(args, strict: @switches)

    if invalid != [] do
      Mix.raise("unknown option: #{inspect(invalid)}")
    end

    if rest != [] do
      Mix.raise("usage: mix muro.gen [--check]")
    end

    root = Muro.Manifest.root()

    manifest =
      case Muro.Manifest.load(root) do
        {:ok, manifest} -> manifest
        {:error, message} -> Mix.raise(message)
      end

    running = Mix.Tasks.Muro.version()

    case Muro.Manifest.version_pin(manifest.version, running) do
      :ok -> :ok
      {:error, message} -> Mix.raise(message)
    end

    if opts[:check] do
      run_check(manifest, root, running)
    else
      run_generate(manifest, root, running)
    end
  end

  defp run_check(manifest, root, running) do
    case Muro.Gen.check(manifest, root, running) do
      :ok -> Mix.shell().info("ok")
      {:error, message} -> Mix.raise(message)
    end
  end

  defp run_generate(manifest, root, running) do
    case Muro.Gen.generate(manifest, root, running) do
      {:ok, lines} -> Enum.each(lines, fn line -> Mix.shell().info(line) end)
      {:error, message} -> Mix.raise(message)
    end
  end
end

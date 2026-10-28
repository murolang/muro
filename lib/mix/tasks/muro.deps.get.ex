defmodule Mix.Tasks.Muro.Deps.Get do
  use Mix.Task

  @shortdoc "Fetch muro_deps and write muro.lock"

  @moduledoc """
  Fetch every package in `muro_deps:` and write `muro.lock`.

      mix muro.deps.get

  The manifest is `muro.exs` at the project root, or a `:muro` key in
  `mix.exs`. If both exist, the task stops and names both. Other keys
  are ignored, so a project that only checks books can list
  `muro_deps:` without `muro:` or `modules:`.

  Git packages are cloned with the `git` CLI. Hex packages are
  downloaded from the public repository. There are no arguments: every
  package is resolved again. A tag, a ref, or a requirement that moved
  shows up as a lock diff.

  Packages are fetched into a temporary directory and checked before
  `muro_deps/` or `muro.lock` changes. A failure leaves both as they
  were. One block per package says `fetched <name> <version> (<n>
  files)` and then `added`, `changed`, or `removed` for each file
  whose hash differs from the previous lock. The last line is
  `wrote muro.lock` or `muro.lock unchanged`.

  With no `muro_deps:` the task fetches nothing. Packages the previous
  lock named, and that the manifest no longer names, are removed.
  Directories under `muro_deps/` that the lock did not name are left
  in place.

  `mix muro.check` and `mix muro.gen` do not run this task and do not
  use the network.
  """

  def run(args) do
    Mix.Tasks.Muro.ensure_started()

    {_opts, rest, invalid} = OptionParser.parse(args, strict: [])

    if invalid != [] or rest != [] do
      Mix.raise("usage: mix muro.deps.get")
    end

    case Muro.Deps.get(Muro.Manifest.root()) do
      {:ok, lines} -> Enum.each(lines, fn line -> Mix.shell().info(line) end)
      {:error, message} -> Mix.raise(message)
    end
  end
end

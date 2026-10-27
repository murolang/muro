defmodule Mix.Tasks.Muro.Init do
  use Mix.Task

  @shortdoc "Create a muro manifest and priv/muro"

  @moduledoc """
  Create `muro.exs` and `priv/muro/`.

      mix muro.init
      mix muro.init --ci github

  `muro.exs` pins `muro:` to the running version and starts with an
  empty `modules:` list, plus a commented example entry. The task
  refuses to overwrite `muro.exs` or a `:muro` key already in
  `mix.exs`.

  `--ci github` also writes `.github/workflows/muro.yml`. The job
  sets up Elixir and OTP, installs the archive at the pinned version
  (`mix archive.install github murolang/muro ref v<version> --force`),
  and runs `mix muro.gen --check`. An existing workflow file is left
  in place.

  The task prints a note to paste into the project's agent
  instructions (AGENTS.md or similar): generated files are not edited
  by hand, the `.muro` file is the source, and `mix muro.gen` is how
  the module is updated. It does not write that file.

  The manifest and the workflow are documented in `Muro.Init`.
  """

  @switches [ci: :string]

  def run(args) do
    Mix.Tasks.Muro.ensure_started()

    {opts, rest, invalid} = OptionParser.parse(args, strict: @switches)

    if invalid != [] do
      Mix.raise("unknown option: #{inspect(invalid)}")
    end

    if rest != [] do
      Mix.raise("usage: mix muro.init [--ci github]")
    end

    ci =
      case Keyword.get(opts, :ci) do
        nil -> nil
        "github" -> :github
        other -> Mix.raise("unknown --ci #{other}; expected github")
      end

    case Muro.Init.write(Muro.Manifest.root(), Mix.Tasks.Muro.version(), ci) do
      {:ok, lines, note} ->
        Enum.each(lines, fn line -> Mix.shell().info(line) end)
        Mix.shell().info(String.trim_trailing(note))

      {:error, message} ->
        Mix.raise(message)
    end
  end
end

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
  (`mix archive.install hex muro <version> --force`),
  and runs `mix muro.gen --check`. An existing workflow file is left
  in place.

  The task prints a note. `muro skills add` writes the commands for
  this project into `AGENTS.md`. The task does not write that file.

  The manifest and the workflow are documented in `Muro.Init`.
  """

  def run(args) do
    Mix.Tasks.Muro.ensure_started()
    Muro.CLI.Output.mix(Muro.CLI.Init.run_mix(args))
  end
end

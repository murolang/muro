defmodule Muro.Init do
  @moduledoc """
  Create `muro.exs` and `priv/muro/` for `mix muro.init`.

  The manifest pins `muro:` to the running version and leaves
  `modules:` empty, with one commented example entry. An existing
  `muro.exs`, or a `:muro` key already in `mix.exs`, is left untouched.

  `ci: :github` also writes `.github/workflows/muro.yml`. The job sets
  up Elixir and OTP, installs this version of the archive from Hex, and
  runs `mix muro.gen --check`. The install line is

      mix archive.install hex muro <version> --force

  The version is the one in the manifest. `--force` skips the install
  question.

  Init prints a note for the project's agent instructions. It does
  not write that file.
  """

  @elixir "1.20.4"
  @otp "29.1"

  @doc """
  Write the manifest under `root`.

  `ci` is `nil` or `:github`. Returns `{:ok, lines, note}` or
  `{:error, message}`. `lines` names each file that was created.
  """
  def write(root, version, ci \\ nil)

  def write(root, version, ci)
      when is_binary(root) and is_binary(version) and ci in [nil, :github] do
    root = Path.expand(root)
    exs = Path.join(root, "muro.exs")
    workflow = Path.join(root, ".github/workflows/muro.yml")
    has_exs = File.regular?(exs)
    has_mix = match?({:ok, _value}, Muro.Manifest.mix_config(root))

    cond do
      has_exs and has_mix ->
        {:error,
         "refusing to overwrite an existing manifest: muro.exs and the :muro key in mix.exs"}

      has_exs ->
        {:error, "refusing to overwrite an existing manifest: muro.exs"}

      has_mix ->
        {:error, "refusing to overwrite an existing manifest: the :muro key in mix.exs"}

      ci == :github and File.regular?(workflow) ->
        {:error, "refusing to overwrite .github/workflows/muro.yml"}

      true ->
        File.mkdir_p!(Path.join(root, "priv/muro"))
        File.write!(exs, manifest_source(version))

        lines = ["created muro.exs", "created priv/muro/"]

        lines =
          if ci == :github do
            File.mkdir_p!(Path.dirname(workflow))
            File.write!(workflow, workflow(version))
            lines ++ ["created .github/workflows/muro.yml"]
          else
            lines
          end

        {:ok, lines, note()}
    end
  end

  @doc "The `muro.exs` init writes, pinned to `version`."
  def manifest_source(version) when is_binary(version) do
    """
    [
      muro: "#{version}",
      modules: [
        # {"priv/muro/rounding.muro", MyApp.Billing.Rounding, "lib/my_app/billing/rounding.ex"}
      ]
    ]
    """
  end

  @doc """
  The GitHub Actions workflow `mix muro.init --ci github` writes.

  Elixir #{@elixir} and OTP #{@otp} match this repository's `mise.toml`.
  """
  def workflow(version) when is_binary(version) do
    """
    name: muro

    on:
      push:
      pull_request:

    permissions:
      contents: read

    jobs:
      check:
        name: mix muro.gen --check
        runs-on: ubuntu-latest
        steps:
          - uses: actions/checkout@v5

          - uses: erlef/setup-beam@v1
            with:
              elixir-version: "#{@elixir}"
              otp-version: "#{@otp}"

          - name: Install the muro archive
            run: mix archive.install hex muro #{version} --force

          - name: Check generated modules
            run: mix muro.gen --check
    """
  end

  @doc """
  The note init prints. The caller pastes it into the project's
  agent instructions. Init does not write that file.
  """
  def note do
    """
    Add this to the project's agent instructions (AGENTS.md or similar):
    Generated files are not edited by hand. The .muro file is the source. Run mix muro.gen after changing it.
    """
  end
end

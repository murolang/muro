defmodule Muro.CLI.Init do
  @moduledoc false

  @doc false
  def switches, do: Enum.map(options(), &{&1.name, &1.type})

  @doc false
  def options do
    [
      %{
        name: :ci,
        type: :string,
        value: "github",
        default: "none",
        doc:
          "Also write .github/workflows/muro.yml when that file is absent. The only value is github. The job installs this version of the executable and runs muro gen --check. An existing workflow file is left in place. When the manifest is new and the workflow file exists, init exits 1 and names the file."
      },
      %{
        name: :backend,
        type: :string,
        value: "NAME",
        default: "the backend this directory selects",
        doc:
          "Store this backend on the manifest. It does not change which file is written. The value is elixir, c, rust, asm, fsm, or exunit. Without the flag, a Mix project omits the key."
      },
      %{
        name: :cargo_metadata,
        type: :boolean,
        default: "false",
        doc:
          "On a directory with Cargo.toml, append [package.metadata.muro] and write muro/. It does not write muro.toml. Without a Cargo.toml it exits 1 and writes nothing."
      }
    ]
  end

  @doc false
  def help do
    Muro.CLI.Text.page([
      Muro.CLI.Text.prose("""
      muro init looks at the working directory and writes one manifest, pinned to the running version, plus one commented example entry. mix.exs gets muro.exs and priv/muro/. Cargo.toml gets muro.toml and muro/, with Rust as the backend. A CMakeLists.txt, meson.build, or Makefile, and neither mix.exs nor Cargo.toml, gets muro.toml and muro/ for C. Anything else gets muro.toml with modules = [] and muro/. An existing manifest at muro.exs, muro.toml, or [package.metadata.muro] is left in place. Init prints a diff of that file and exits 0. It does not write a second manifest, and it does not write AGENTS.md. It prints a note that points at muro skills add.
      """),
      Muro.CLI.Text.section(
        "USAGE",
        Muro.CLI.Text.pre(["muro init [--ci github] [--backend NAME] [--cargo-metadata]"])
      ),
      Muro.CLI.Text.section(
        "ARGUMENTS",
        Muro.CLI.Text.arguments([
          {"none", "init reads the working directory. It takes no path."}
        ])
      ),
      Muro.CLI.Text.section("OPTIONS", Muro.CLI.Text.options(options())),
      Muro.CLI.Text.section(
        "EXAMPLES",
        Muro.CLI.Text.examples(
          [
            {"muro init", "In a Cargo project, write muro.toml and muro/."},
            {"muro init --backend asm", "Store asm as the manifest backend."},
            {"muro init --cargo-metadata", "Append [package.metadata.muro] to Cargo.toml."},
            {"muro init --ci github", "Also write .github/workflows/muro.yml."}
          ],
          "\n\n"
        )
      ),
      Muro.CLI.Text.section(
        "EXIT CODES",
        Muro.CLI.Text.exits([
          {"0",
           "The manifest was created, or an existing manifest was left in place and a diff was printed."},
          {"1",
           "The flag value is unknown, --cargo-metadata has no Cargo.toml, or the workflow file already exists while the manifest is new."}
        ])
      ),
      Muro.CLI.Text.section(
        "LEARN MORE",
        Muro.CLI.Text.pre(["https://muro-lang.dev/docs/binary"])
      )
    ])
  end

  @doc false
  def run_mix(args) do
    {opts, rest, invalid} = OptionParser.parse(args, strict: [ci: :string])

    cond do
      invalid != [] ->
        {:raise, "", "unknown option: #{inspect(invalid)}"}

      rest != [] ->
        {:raise, "", "usage: mix muro.init [--ci github]"}

      true ->
        case ci_value(Keyword.get(opts, :ci)) do
          {:ok, ci} ->
            case Muro.Init.write(Muro.Manifest.root(), Mix.Tasks.Muro.version(), ci) do
              {:ok, lines, note} -> {:ok, created(lines, note), ""}
              {:error, message} -> {:raise, "", message}
            end

          {:error, message} ->
            {:raise, "", message}
        end
    end
  end

  @doc false
  def run(args) do
    {opts, rest, invalid} = OptionParser.parse(args, strict: switches())

    cond do
      invalid != [] ->
        {:raise, "", "unknown option: #{inspect(invalid)}"}

      rest != [] ->
        {:raise, "", "usage: muro init [--ci github] [--backend NAME] [--cargo-metadata]"}

      true ->
        with {:ok, ci} <- ci_value(Keyword.get(opts, :ci)),
             {:ok, backend} <- backend_value(Keyword.get(opts, :backend)) do
          scaffold(ci, backend, Keyword.get(opts, :cargo_metadata, false))
        else
          {:error, message} -> {:raise, "", message}
        end
    end
  end

  defp scaffold(ci, backend, cargo?) do
    opts = [ci: ci, backend: backend, cargo_metadata: cargo?]

    case Muro.Init.scaffold(Muro.Manifest.root(), Mix.Tasks.Muro.version(), opts) do
      {:ok, lines, note} -> {:ok, created(lines, note), ""}
      {:diff, text} -> {:ok, text, ""}
      {:error, message} -> {:raise, "", message}
    end
  end

  defp created(lines, note) do
    Muro.CLI.join_lines(lines ++ [String.trim_trailing(note)])
  end

  defp ci_value(nil), do: {:ok, nil}
  defp ci_value("github"), do: {:ok, :github}
  defp ci_value(other), do: {:error, "unknown --ci #{other}; expected github"}

  defp backend_value(nil), do: {:ok, nil}

  defp backend_value(name) when name in ~w(elixir c rust asm fsm exunit) do
    {:ok, String.to_atom(name)}
  end

  defp backend_value(other), do: {:error, "unknown backend: #{other}"}
end

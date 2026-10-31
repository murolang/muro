defmodule Muro.CLI.Deps do
  @moduledoc false

  @doc false
  def switches, do: []

  @doc false
  def help do
    Muro.CLI.Text.page([
      Muro.CLI.Text.prose("""
      muro deps.get reads muro_deps from the manifest and fetches each package into muro_deps/<name>/. It writes muro.lock. It takes no package names: every package is resolved again. Git packages are cloned with git. Hex packages are downloaded over HTTPS. With no packages it prints "nothing to fetch" and removes packages the previous lock named. A failure leaves muro.lock and muro_deps/ as they were. muro check and muro gen do not fetch and do not use the network. A project with no manifest has nothing to fetch.
      """),
      Muro.CLI.Text.section("USAGE", Muro.CLI.Text.pre(["muro deps.get"])),
      Muro.CLI.Text.section(
        "ARGUMENTS",
        Muro.CLI.Text.arguments([
          {"none", "Every package in the manifest is fetched. There is no package argument."}
        ])
      ),
      Muro.CLI.Text.section(
        "OPTIONS",
        Muro.CLI.Text.prose("None. deps.get takes no flags.", 4)
      ),
      Muro.CLI.Text.section(
        "EXAMPLES",
        Muro.CLI.Text.examples(
          [
            {"muro deps.get", "Nothing to fetch when the manifest names no packages."},
            {"muro deps.get", "Fetch again. A lock that already matches is left unchanged."}
          ],
          "\n\n"
        )
      ),
      Muro.CLI.Text.section(
        "EXIT CODES",
        Muro.CLI.Text.exits([
          {"0", "The packages were fetched, or there was nothing to fetch."},
          {"1", "The manifest cannot be read, a package fails, or an argument or flag was given."}
        ])
      ),
      Muro.CLI.Text.section(
        "LEARN MORE",
        Muro.CLI.Text.pre(["https://muro-lang.dev/docs/packages"])
      )
    ])
  end

  @doc false
  def run(args) do
    {_opts, rest, invalid} = OptionParser.parse(args, strict: switches())

    if invalid != [] or rest != [] do
      {:raise, "", "usage: mix muro.deps.get"}
    else
      case Muro.Deps.get(Muro.Manifest.root()) do
        {:ok, lines} -> {:ok, Muro.CLI.join_lines(lines), ""}
        {:error, message} -> {:raise, "", message}
      end
    end
  end
end

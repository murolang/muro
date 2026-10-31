defmodule Muro.CLI.Skills do
  @moduledoc false

  @doc false
  def switches, do: []

  @doc false
  def help do
    Muro.CLI.Text.page([
      Muro.CLI.Text.prose("""
      muro skills add writes the agent block into AGENTS.md, and creates that file when it is missing. It also updates CLAUDE.md when that file already exists. It never creates CLAUDE.md. The block is delimited by the whole lines <!-- muro:begin --> and <!-- muro:end -->. A rerun replaces the lines between the markers and leaves every other byte in place, including the file's line endings. The wording is the guidance from the For agents page: two jobs, the wall, the commands for this project, and a pointer to an example. Copy syntax from the examples. Do not write it from memory. out of fuel is not acceptance. The command touches nothing outside its block.
      """),
      Muro.CLI.Text.section("USAGE", Muro.CLI.Text.pre(["muro skills add"])),
      Muro.CLI.Text.section(
        "ARGUMENTS",
        Muro.CLI.Text.arguments([
          {"add", "Required. The only subcommand. It writes the block described above."}
        ])
      ),
      Muro.CLI.Text.section(
        "OPTIONS",
        Muro.CLI.Text.prose("None. skills add takes no flags.", 4)
      ),
      Muro.CLI.Text.section(
        "EXAMPLES",
        Muro.CLI.Text.examples(
          [
            {"muro skills add", "Create AGENTS.md when it is missing."},
            {"muro skills add",
             "Run again. The block is replaced and the rest of the file stays."}
          ],
          "\n\n"
        )
      ),
      Muro.CLI.Text.section(
        "EXIT CODES",
        Muro.CLI.Text.exits([
          {"0", "The block was written."},
          {"1", "The subcommand is not add, a flag was given, or a marker is unbalanced."}
        ])
      ),
      Muro.CLI.Text.section(
        "LEARN MORE",
        Muro.CLI.Text.pre([
          "https://muro-lang.dev/docs/binary",
          "https://muro-lang.dev/docs/for-agents"
        ])
      )
    ])
  end

  @doc false
  def run(["add"]) do
    case Muro.Skills.add(Muro.Manifest.root()) do
      {:ok, lines} -> {:ok, Muro.CLI.join_lines(lines), ""}
      {:error, message} -> {:raise, "", message}
    end
  end

  def run(_args) do
    {:raise, "", "usage: muro skills add"}
  end
end

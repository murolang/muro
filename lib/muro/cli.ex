defmodule Muro.CLI do
  @moduledoc false

  @usage_line "usage: muro [--version] <check|emit|gen|init|skills|deps.get|mutate> ..."

  @doc """
  Entry point for the self-contained executable.

  Returns the process status. It does not halt.
  """
  def main(args) when is_list(args) do
    args = Enum.map(args, &to_string/1)
    previous = unicode_on()

    try do
      args |> dispatch() |> named() |> present()
    rescue
      error in Mix.Error ->
        IO.write(:stderr, ensure_nl(executable_names(error.message)))
        1
    after
      unicode_restore(previous)
    end
  end

  @doc false
  def join_lines(lines) when is_list(lines) do
    IO.iodata_to_binary(Enum.map(lines, &[to_string(&1), ?\n]))
  end

  @doc false
  def ensure_nl(text) when is_binary(text) do
    if String.ends_with?(text, "\n"), do: text, else: text <> "\n"
  end

  @doc false
  def usage_line, do: @usage_line

  @doc false
  def usage_text do
    version = Mix.Tasks.Muro.version()

    Muro.CLI.Text.page([
      "muro #{version}, an explicit affine dependent type theory\n\n" <>
        Muro.CLI.Text.prose("""
        muro checks a book of definitions, then emits verified code to Elixir/OTP, C, Rust, Zig, or Cortex-M assembly from one source. A spec never becomes evidence, and evidence never becomes a run \u{2014} only run terms are emitted. The executable carries its own Erlang runtime and does not compile or start a host application.
        """),
      Muro.CLI.Text.section(
        "USAGE",
        Muro.CLI.Text.pre([
          "muro <command> [options]",
          "muro help <command>"
        ])
      ),
      Muro.CLI.Text.section(
        "COMMANDS",
        Muro.CLI.Text.stack([
          {"check [path.muro] [--fuel N]",
           "Type-check a book, or the built-in book when the path is omitted."},
          {"emit path.muro [--backend NAME] [--node NAME] [--imports]",
           "Emit run code: elixir, c, rust, zig, asm, otp, fsm, or exunit."},
          {"gen [--check]", "Write the modules the manifest names. --check only compares."},
          {"init [--ci github] [--backend NAME] [--cargo-metadata]",
           "Write the one manifest this directory calls for."},
          {"skills add", "Write the agent guidance into AGENTS.md."},
          {"deps.get", "Fetch muro_deps and write muro.lock."},
          {[
             "mutate path.muro [--only NAME] [--json] [--fuel N]",
             "    [--max-mutants-per-def N] [--max-survivors N]"
           ], "Change run definitions and report which evidence still holds."}
        ])
      ),
      Muro.CLI.Text.section(
        "GETTING STARTED",
        Muro.CLI.Text.pre([
          "muro init writes the manifest. Copy a .muro file from the examples.",
          "muro check book.muro",
          "muro gen writes the module. muro gen --check compares it in CI.",
          "muro skills add records the commands in AGENTS.md."
        ])
      ),
      Muro.CLI.Text.section(
        "EXAMPLES",
        Muro.CLI.Text.examples([
          {"muro check book.muro", "Check one file."},
          {"muro emit book.muro --backend rust", "Emit Rust beside the book."},
          {"muro init", "In a Cargo project, write muro.toml and muro/."},
          {"muro gen", "Write the targets the manifest names."},
          {"muro gen --check", "Exits 0 when those targets match. Writes nothing."},
          {"muro skills add", "Write the guidance into AGENTS.md."}
        ])
      ),
      Muro.CLI.Text.section(
        "MANIFEST",
        Muro.CLI.Text.prose("""
        The manifest is muro.toml at the project root, or [package.metadata.muro] in Cargo.toml. It pins the muro version and lists each book, its backend, and its target. A Mix project uses muro.exs. Loading more than one manifest is an error.
        """)
      ),
      Muro.CLI.Text.section(
        "GLOBAL OPTIONS",
        Muro.CLI.Text.kv([
          {"-h, --help", "Show this text and exit 0."},
          {"-v, --version", "Print the version, then exit 0."}
        ])
      ),
      Muro.CLI.Text.section(
        "IF YOU ARE AN AGENT",
        Muro.CLI.Text.pre([
          "Read https://muro-lang.dev/docs/for-agents first, or run",
          "muro skills add to write that guidance into AGENTS.md.",
          "Copy syntax from https://muro-lang.dev/docs/examples",
          "rather than writing it from memory. out of fuel is not acceptance."
        ])
      ),
      Muro.CLI.Text.section(
        "LEARN MORE",
        Muro.CLI.Text.pre([
          "https://muro-lang.dev",
          "https://muro-lang.dev/docs",
          "https://muro-lang.dev/llms.txt",
          "https://muro-lang.dev/docs/wall",
          "https://muro-lang.dev/docs/binary",
          "muro help <command>"
        ])
      )
    ])
  end

  @doc false
  def help_pages do
    [
      usage_text(),
      Muro.CLI.Check.help(),
      Muro.CLI.Emit.help(),
      Muro.CLI.Gen.help(),
      Muro.CLI.Init.help(),
      Muro.CLI.Skills.help(),
      Muro.CLI.Deps.help(),
      Muro.CLI.Mutate.help()
    ]
  end

  defp dispatch(["--version"]), do: version_result()
  defp dispatch(["-v"]), do: version_result()
  defp dispatch(["--help" | _rest]), do: shown(usage_text())
  defp dispatch(["-h" | _rest]), do: shown(usage_text())
  defp dispatch(["help"]), do: shown(usage_text())
  defp dispatch(["help" | rest]), do: help_command(rest)
  defp dispatch([]), do: shown(usage_text())
  defp dispatch(["check" | rest]), do: command(rest, Muro.CLI.Check)
  defp dispatch(["emit" | rest]), do: command(rest, Muro.CLI.Emit)
  defp dispatch(["gen" | rest]), do: command(rest, Muro.CLI.Gen)
  defp dispatch(["init" | rest]), do: command(rest, Muro.CLI.Init)
  defp dispatch(["skills" | rest]), do: command(rest, Muro.CLI.Skills)
  defp dispatch(["deps.get" | rest]), do: command(rest, Muro.CLI.Deps)
  defp dispatch(["mutate" | rest]), do: command(rest, Muro.CLI.Mutate)

  defp dispatch([unknown | _rest]) do
    label =
      if String.starts_with?(unknown, "-") do
        "unknown option: #{unknown}"
      else
        "unknown command: #{unknown}"
      end

    {:raise, "", hint(label)}
  end

  defp help_command(["skills"]), do: shown(Muro.CLI.Skills.help())
  defp help_command(["skills", "add"]), do: shown(Muro.CLI.Skills.help())

  defp help_command([name]) when name in ["check", "emit", "gen", "init", "deps.get", "mutate"] do
    shown(module(name).help())
  end

  defp help_command(rest) do
    {:raise, "", hint("unknown command: #{Enum.join(rest, " ")}")}
  end

  defp module("check"), do: Muro.CLI.Check
  defp module("emit"), do: Muro.CLI.Emit
  defp module("gen"), do: Muro.CLI.Gen
  defp module("init"), do: Muro.CLI.Init
  defp module("deps.get"), do: Muro.CLI.Deps
  defp module("mutate"), do: Muro.CLI.Mutate

  defp command(args, module) do
    cond do
      help_flag?(args) ->
        shown(module.help())

      bad_flag?(args, module) ->
        {:raise, "", hint("unknown option: #{flag_names(args, module)}")}

      true ->
        module.run(args)
    end
  end

  defp shown(text), do: {:ok, Muro.CLI.Text.paint(text, Muro.CLI.Text.color?()), ""}

  defp help_flag?(args), do: "--help" in args or "-h" in args

  defp bad_flag?(args, module) do
    {_, _, invalid} = OptionParser.parse(args, strict: module.switches())
    invalid != []
  end

  defp flag_names(args, module) do
    {_, _, invalid} = OptionParser.parse(args, strict: module.switches())
    Enum.map_join(invalid, ", ", &flag_name/1)
  end

  defp flag_name({name, _value}) when is_binary(name), do: name
  defp flag_name(name) when is_binary(name), do: name

  defp named({:raise, stdout, message}), do: {:raise, stdout, executable_names(message)}
  defp named(result), do: result

  @doc false
  def executable_names(message) do
    Regex.replace(~r/\bmix muro\.(deps\.get|gen|init|check|emit|mutate)\b/, message, "muro \\1")
  end

  defp hint(label), do: label <> "\n" <> @usage_line <> "\nrun muro --help"

  defp version_result, do: {:ok, "Muro v#{Mix.Tasks.Muro.version()}\n", ""}

  defp present({:ok, stdout, stderr}) do
    IO.write(stdout)
    IO.write(:stderr, stderr)
    0
  end

  defp present({:raise, stdout, message}) do
    IO.write(stdout)
    IO.write(:stderr, ensure_nl(message))
    1
  end

  defp present({:exit, code, stdout, lines}) when is_list(lines) do
    IO.write(stdout)
    Enum.each(lines, &IO.puts(:stderr, &1))
    code
  end

  # A pipe's device is latin1, so a codepoint above 255 is printed as an
  # escape. Unicode encoding writes the character.
  defp unicode_on do
    previous = %{
      standard_io: encoding(:standard_io),
      standard_error: encoding(:standard_error)
    }

    _ = :io.setopts(:standard_io, [{:encoding, :unicode}])
    _ = :io.setopts(:standard_error, [{:encoding, :unicode}])
    previous
  end

  defp unicode_restore(previous) do
    restore(:standard_io, previous.standard_io)
    restore(:standard_error, previous.standard_error)
  end

  defp restore(_device, nil), do: :ok

  defp restore(device, encoding) do
    _ = :io.setopts(device, [{:encoding, encoding}])
    :ok
  end

  defp encoding(device) do
    case :io.getopts(device) do
      opts when is_list(opts) -> Keyword.get(opts, :encoding)
      _other -> nil
    end
  end
end

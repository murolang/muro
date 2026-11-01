defmodule Muro.CliHelpTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  @modules [
    Muro.CLI.Check,
    Muro.CLI.Emit,
    Muro.CLI.Gen,
    Muro.CLI.Init,
    Muro.CLI.Skills,
    Muro.CLI.Deps,
    Muro.CLI.Mutate
  ]

  @commands ["check", "emit", "gen", "init", "skills", "deps.get", "mutate"]

  @doc_urls [
    "https://muro-lang.dev",
    "https://muro-lang.dev/docs",
    "https://muro-lang.dev/docs/start",
    "https://muro-lang.dev/docs/for-agents",
    "https://muro-lang.dev/docs/binary",
    "https://muro-lang.dev/docs/language",
    "https://muro-lang.dev/docs/grammar",
    "https://muro-lang.dev/docs/wall",
    "https://muro-lang.dev/docs/emit",
    "https://muro-lang.dev/docs/gen",
    "https://muro-lang.dev/docs/mutate",
    "https://muro-lang.dev/docs/packages",
    "https://muro-lang.dev/docs/library",
    "https://muro-lang.dev/docs/examples",
    "https://muro-lang.dev/llms.txt"
  ]

  @book "def one : run Nat := 0\n"

  test "no arguments, --help, -h, and help print one usage on stdout" do
    version = Mix.Tasks.Muro.version()
    pages = Enum.map([[], ["--help"], ["-h"], ["help"]], &cli/1)

    assert Enum.all?(pages, fn {out, err, code} -> code == 0 and err == "" and out != "" end)
    [first | rest] = Enum.map(pages, fn {out, _, _} -> out end)
    assert Enum.all?(rest, &(&1 == first))
    assert first == Muro.CLI.usage_text()
    assert first =~ "muro #{version}, an explicit affine dependent type theory\n"
    assert first =~ "\u{2014}"
    refute first =~ "\\x{"
    refute first =~ "\e["

    lines = first |> String.trim_trailing("\n") |> String.split("\n")
    assert length(lines) in 50..70

    for line <- lines do
      assert String.length(line) <= 80, "usage line longer than 80: #{line}"
    end
  end

  test "help names the commands, the manifest, and where to read next" do
    text = Muro.CLI.usage_text()

    for command <- ["check", "emit", "gen", "init", "skills add", "deps.get", "mutate"] do
      assert text =~ command
    end

    for flag <- [
          "--fuel",
          "--backend",
          "--node",
          "--imports",
          "--check",
          "--ci",
          "--backend",
          "--cargo-metadata",
          "--only",
          "--json",
          "--max-mutants-per-def",
          "--max-survivors",
          "--help",
          "--version"
        ] do
      assert text =~ flag
    end

    for backend <- ["elixir", "c", "rust", "asm", "otp", "fsm", "exunit"] do
      assert text =~ backend
    end

    assert text =~ "muro.toml"
    assert text =~ "[package.metadata.muro]"
    assert text =~ "Cargo.toml"
    assert text =~ "https://muro-lang.dev/docs/binary"
    assert text =~ "https://muro-lang.dev"
    assert text =~ "https://muro-lang.dev/docs/for-agents"
    assert text =~ "https://muro-lang.dev/docs/examples"
    assert text =~ "https://muro-lang.dev/llms.txt"
    assert text =~ "muro help <command>"
    assert text =~ "out of fuel is not acceptance"
    assert text =~ "muro skills add"
    assert text =~ "IF YOU ARE AN AGENT"
    assert text =~ "GETTING STARTED"
    assert text =~ "EXAMPLES"
  end

  test "muro help <command> and <command> --help agree and do not run the command" do
    for command <- @commands do
      forms =
        case command do
          "skills" ->
            [
              ["help", "skills"],
              ["help", "skills", "add"],
              ["skills", "--help"],
              ["skills", "-h"],
              ["skills", "add", "--help"]
            ]

          other ->
            [["help", other], [other, "--help"], [other, "-h"]]
        end

      pages = Enum.map(forms, &cli/1)
      assert Enum.all?(pages, fn {out, err, code} -> code == 0 and err == "" end)
      [first | rest] = Enum.map(pages, fn {out, _, _} -> out end)
      assert Enum.all?(rest, &(&1 == first))
      assert first =~ "USAGE\n"
      assert first =~ "EXAMPLES\n"
      assert first =~ "EXIT CODES\n"
      assert first =~ "https://muro-lang.dev/docs/"
      refute first =~ "expected one path"
      refute first =~ "no manifest:"
      refute first =~ "\e["
    end
  end

  test "every help page stays within 80 columns and uses a real em dash only in the overview" do
    for text <- Muro.CLI.help_pages() do
      lines = text |> String.trim_trailing("\n") |> String.split("\n")

      for line <- lines do
        assert String.length(line) <= 80, "longer than 80: #{line}"
      end

      refute text =~ "\\x{"
    end

    assert Muro.CLI.usage_text() =~ "\u{2014}"
  end

  test "every URL in the help is on the known list" do
    urls =
      Muro.CLI.help_pages()
      |> Enum.flat_map(&Regex.scan(~r/https:\/\/[^\s)>\]]+/, &1))
      |> Enum.map(fn [url] -> String.trim_trailing(url, ".,") end)
      |> Enum.uniq()

    assert urls != []

    for url <- urls do
      assert url in @doc_urls, "unexpected URL #{url}"
    end
  end

  test "every switch OptionParser accepts appears in that command's help" do
    for module <- @modules do
      help = module.help()

      for {name, _type} <- module.switches() do
        flag = "--" <> (name |> to_string() |> String.replace("_", "-"))
        assert help =~ flag, "#{inspect(module)} omits #{flag}"
      end
    end
  end

  test "each command help states defaults, exit codes, and its manual page" do
    assert Muro.CLI.Check.help() =~ "Default: #{Muro.Check.default_fuel()}."
    assert Muro.CLI.Check.help() =~ "https://muro-lang.dev/docs/start"
    assert Muro.CLI.Check.help() =~ "https://muro-lang.dev/docs/language"
    assert Muro.CLI.Check.help() =~ "std:"
    assert Muro.CLI.Check.help() =~ "https://muro-lang.dev/docs/library"
    assert Muro.CLI.Deps.help() =~ "std:"

    emit = Muro.CLI.Emit.help()
    assert emit =~ "Default: elixir."
    assert emit =~ "https://muro-lang.dev/docs/emit"

    for backend <- ["elixir", "c", "rust", "asm", "otp", "fsm", "exunit"] do
      assert emit =~ backend
    end

    gen = Muro.CLI.Gen.help()
    assert gen =~ "--check"
    assert gen =~ "https://muro-lang.dev/docs/gen"
    assert gen =~ "book hash" or gen =~ "body hash" or gen =~ "header"

    assert Muro.CLI.Init.help() =~ "https://muro-lang.dev/docs/binary"
    assert Muro.CLI.Skills.help() =~ "https://muro-lang.dev/docs/binary"
    assert Muro.CLI.Deps.help() =~ "https://muro-lang.dev/docs/packages"
    mutate = Muro.CLI.Mutate.help()
    assert mutate =~ "https://muro-lang.dev/docs/mutate"
    assert mutate =~ "surviv"
    assert mutate =~ "Default: #{Muro.Mutate.default_max_mutants()}."
    assert mutate =~ "Default: #{Muro.Check.default_fuel()}."
  end

  test "an unknown command or a bad flag names itself on stderr" do
    {out, err, code} = cli(["bogus"])
    assert code == 1
    assert out == ""
    assert err == usage_error("unknown command: bogus")

    {out, err, code} = cli(["--bogus"])
    assert code == 1
    assert out == ""
    assert err == usage_error("unknown option: --bogus")

    for {args, name} <- [
          {["check", "--nope"], "--nope"},
          {["emit", "--nope"], "--nope"},
          {["gen", "--nope"], "--nope"},
          {["init", "--nope"], "--nope"},
          {["skills", "--nope"], "--nope"},
          {["deps.get", "--nope"], "--nope"},
          {["mutate", "--nope"], "--nope"},
          {["check", "--fuel"], "--fuel"}
        ] do
      {out, err, code} = cli(args)
      assert code == 1
      assert out == ""
      assert err == usage_error("unknown option: #{name}")
    end
  end

  test "a usage error from the executable names the executable" do
    for {args, usage} <- [
          {["init", "extra"],
           "usage: muro init [--ci github] [--backend NAME] [--cargo-metadata]"},
          {["gen", "extra"], "usage: muro gen [--check]"},
          {["deps.get", "extra"], "usage: muro deps.get"}
        ] do
      {out, err, code} = cli(args)
      assert code == 1
      assert out == ""
      assert err =~ usage
      refute err =~ "mix muro"
    end
  end

  test "messages that name a Mix task name the executable command instead" do
    assert Muro.CLI.executable_names("no muro.lock; run mix muro.deps.get") ==
             "no muro.lock; run muro deps.get"

    assert Muro.CLI.executable_names("run mix muro.gen.") == "run muro gen."
    assert Muro.CLI.executable_names("mix muro --help") == "mix muro --help"
  end

  test "mix muro --help does not print the executable usage" do
    assert_raise Mix.Error, ~r/usage: mix muro \[--version\]/, fn ->
      Mix.Tasks.Muro.run(["--help"])
    end
  end

  test "color is used only for a tty when NO_COLOR is unset" do
    previous = System.get_env("NO_COLOR")

    on_exit(fn ->
      if previous, do: System.put_env("NO_COLOR", previous), else: System.delete_env("NO_COLOR")
    end)

    System.delete_env("NO_COLOR")
    assert Muro.CLI.Text.color?(true)
    refute Muro.CLI.Text.color?(false)

    System.put_env("NO_COLOR", "")
    refute Muro.CLI.Text.color?(true)

    plain = Muro.CLI.usage_text()
    painted = Muro.CLI.Text.paint(plain, true)
    assert painted =~ IO.ANSI.bright()
    assert painted =~ IO.ANSI.cyan()
    assert painted =~ IO.ANSI.green()
    assert Muro.CLI.Text.paint(plain, false) == plain
    assert strip_ansi(painted) == plain
  end

  test "CLI sources do not contain a literal unicode escape" do
    paths = Path.wildcard("lib/muro/cli.ex") ++ Path.wildcard("lib/muro/cli/*.ex")

    for path <- paths do
      refute File.read!(path) =~ ~r/\\x\{[0-9A-Fa-f]+\}/, path
    end
  end

  test "every example command runs in a temp project" do
    examples =
      Muro.CLI.help_pages()
      |> Enum.flat_map(&example_commands/1)

    assert length(examples) >= 4

    for {command, comment} <- examples do
      argv = command |> String.split(" ") |> tl()
      expected = expected_exit(comment)
      dir = tmp_dir()
      prepare(dir, argv)
      {out, err, code} = run_in(dir, argv)

      assert code == expected, """
      #{command}
      expected exit #{expected}, got #{code}
      comment: #{comment}
      stdout: #{out}
      stderr: #{err}
      """
    end
  end

  defp usage_error(label) do
    label <> "\n" <> Muro.CLI.usage_line() <> "\nrun muro --help\n"
  end

  defp expected_exit(comment) do
    case Regex.run(~r/[Ee]xits (\d+)/, comment) do
      [_, code] -> String.to_integer(code)
      _other -> 0
    end
  end

  defp example_commands(text) do
    Regex.scan(~r/^EXAMPLES\n(.*?)(?=^[A-Z][A-Z ]+$|\z)/ms, text)
    |> Enum.flat_map(fn [_, body] -> parse_examples(body) end)
  end

  defp parse_examples(body) do
    body
    |> String.split("\n")
    |> Enum.reduce({[], nil, []}, fn line, {acc, command, comments} ->
      cond do
        command_line?(line) ->
          {flush(acc, command, comments), String.trim(line), []}

        command && String.trim(line) != "" ->
          {acc, command, comments ++ [String.trim(line)]}

        command && String.trim(line) == "" ->
          {flush(acc, command, comments), nil, []}

        true ->
          {acc, command, comments}
      end
    end)
    |> then(fn {acc, command, comments} -> flush(acc, command, comments) end)
  end

  defp command_line?(line) do
    String.trim(line) =~ ~r/\Amuro( [A-Za-z0-9._=\/-]+)+\z/
  end

  defp flush(acc, nil, _comments), do: acc

  defp flush(acc, command, comments) do
    acc ++ [{command, Enum.join(comments, " ")}]
  end

  defp prepare(dir, ["init" | _rest]) do
    File.write!(Path.join(dir, "Cargo.toml"), """
    [package]
    name = "demo"
    version = "0.1.0"
    edition = "2021"
    """)
  end

  defp prepare(dir, ["gen" | rest]) do
    write_gen_project(dir)

    if "--check" in rest do
      {out, err, code} = run_in(dir, ["gen"])
      assert code == 0, "preparing gen --check failed\n#{out}\n#{err}"
    end
  end

  defp prepare(dir, argv) do
    for path <- argv, String.ends_with?(path, ".muro") do
      dest = Path.join(dir, path)
      File.mkdir_p!(Path.dirname(dest))
      File.write!(dest, @book)
    end
  end

  defp write_gen_project(dir) do
    version = Mix.Tasks.Muro.version()
    File.write!(Path.join(dir, "book.muro"), @book)

    File.write!(Path.join(dir, "muro.toml"), """
    muro = "#{version}"
    backend = "rust"

    [[modules]]
    book = "book.muro"
    target = "book.rs"
    """)
  end

  defp run_in(dir, argv) do
    File.cd!(dir, fn -> cli(argv) end)
  end

  defp cli(argv) do
    parent = self()

    stdout =
      capture_io(fn ->
        stderr =
          capture_io(:stderr, fn ->
            send(parent, {:code, Muro.CLI.main(argv)})
          end)

        send(parent, {:stderr, stderr})
      end)

    assert_received {:stderr, stderr}
    assert_received {:code, code}
    {stdout, stderr, code}
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_help_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end

  defp strip_ansi(text), do: String.replace(text, ~r/\e\[[0-9;]*m/, "")
end

defmodule Muro.CLI.Check do
  @moduledoc false

  @doc false
  def switches, do: Enum.map(options(), &{&1.name, &1.type})

  @doc false
  def options do
    [
      %{
        name: :fuel,
        type: :integer,
        value: "N",
        default: Integer.to_string(Muro.Check.default_fuel()),
        doc:
          "How far the checker reduces, for each definition. Running out is reported as out of fuel. That is not acceptance and it is not a type error. Raise N and check again. A cannot convert failure is definite at every fuel."
      }
    ]
  end

  @doc false
  def help do
    Muro.CLI.Text.page([
      Muro.CLI.Text.prose("""
      muro check type-checks one .muro file, or the built-in book when no path is given. It reads that file and the prelude. It writes nothing. On success it prints the version, then "All terms check. Evidence never becomes a run." A book that imports packages then prints one "conforms to" line per package. A refusal prints the version and every failing definition, in book order. out of fuel means the checker stopped reducing. It is not acceptance. Copy syntax from the examples rather than writing it from memory.
      """),
      Muro.CLI.Text.section(
        "USAGE",
        Muro.CLI.Text.pre(["muro check [path.muro] [--fuel N]"])
      ),
      Muro.CLI.Text.section(
        "ARGUMENTS",
        Muro.CLI.Text.arguments([
          {"path.muro", "Optional. One book. When it is omitted, the built-in book is checked."}
        ])
      ),
      Muro.CLI.Text.section("OPTIONS", Muro.CLI.Text.options(options())),
      Muro.CLI.Text.section(
        "EXAMPLES",
        Muro.CLI.Text.examples(
          [
            {"muro check", "Check the built-in book."},
            {"muro check book.muro", "Check one file."},
            {"muro check book.muro --fuel 4000", "Give the checker a larger bound."}
          ],
          "\n\n"
        )
      ),
      Muro.CLI.Text.section(
        "EXIT CODES",
        Muro.CLI.Text.exits([
          {"0", "The book checks."},
          {"1",
           "The book does not check, --fuel is not a positive integer, more than one path was given, or a flag is unknown."}
        ])
      ),
      Muro.CLI.Text.section(
        "LEARN MORE",
        Muro.CLI.Text.pre([
          "https://muro-lang.dev/docs/start",
          "https://muro-lang.dev/docs/language",
          "https://muro-lang.dev/docs/grammar"
        ])
      )
    ])
  end

  @doc false
  def run(args) do
    version = "Muro v#{Mix.Tasks.Muro.version()}\n"
    {opts, paths, invalid} = OptionParser.parse(args, strict: switches())

    cond do
      invalid != [] ->
        {:raise, version, "unknown option: #{inspect(invalid)}"}

      Keyword.get(opts, :fuel, Muro.Check.default_fuel()) <= 0 ->
        {:raise, version, "--fuel must be a positive integer"}

      true ->
        fuel = Keyword.get(opts, :fuel, Muro.Check.default_fuel())
        check(paths, fuel, version)
    end
  end

  defp check([], fuel, version) do
    finish(Muro.Check.check_sig(Muro.Example.book(), fuel: fuel), version)
  end

  defp check([path], fuel, version) do
    finish(Muro.conforms(path, fuel: fuel), version)
  end

  defp check(_paths, _fuel, version) do
    {:raise, version, "expected at most one path"}
  end

  defp finish(:ok, version) do
    {:ok, version <> success(), ""}
  end

  defp finish({:ok, lines}, version) do
    {:ok, version <> success() <> Muro.CLI.join_lines(lines), ""}
  end

  defp finish({:error, message}, version) do
    {:raise, version, message}
  end

  defp success, do: "All terms check. Evidence never becomes a run.\n"
end

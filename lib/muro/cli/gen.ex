defmodule Muro.CLI.Gen do
  @moduledoc false

  @doc false
  def switches, do: Enum.map(options(), &{&1.name, &1.type})

  @doc false
  def options do
    [
      %{
        name: :check,
        type: :boolean,
        default: "false",
        doc:
          "Write nothing. Compare each committed file with the bytes muro gen would leave in place. The book hash, the body hash, and the Muro version in the header must agree. Success prints ok. A missing target, a stale book, a hand edit, a body that differs, or a header that names another version is an error and names the target and the book. When the header is older than the Elixir spelling rule, the error also lists host names that changed. The .h beside a C target is checked the same way. Each book is type-checked once, and every target of that book is compared from that copy."
      },
      %{
        name: :skip_check,
        type: :boolean,
        default: "false",
        doc:
          "Do not type-check. The caller has already checked the book in this process. The books are still loaded, and a book that does not parse still fails. With --check, the byte comparison is unchanged: a committed file that is not what the book emits is still an error. The default type-checks."
      }
    ]
  end

  @doc false
  def help do
    Muro.CLI.Text.page([
      Muro.CLI.Text.prose("""
      muro gen reads the manifest and writes the modules it names. The manifest is muro.toml, [package.metadata.muro] in Cargo.toml, or muro.exs. It pins muro to a version, which must equal the running version, and lists modules. Each entry names a book and a target. elixir, fsm, and exunit also name a module. c, rust, zig, and asm name a target ending in .c, .rs, .zig, or .s. An optional fuel is the checker's bound. An optional backend is the kind of every entry that omits one. gen type-checks each book once, then emits every target of that book from that copy, including both files of a C target. If one book fails, it writes nothing. A target that already matches is left untouched. Do not edit a generated file. Change the .muro file and run muro gen. --skip-check does not type-check; the caller has already checked. --check --skip-check still compares bytes.
      """),
      Muro.CLI.Text.section(
        "USAGE",
        Muro.CLI.Text.pre(["muro gen [--check] [--skip-check]"])
      ),
      Muro.CLI.Text.section(
        "ARGUMENTS",
        Muro.CLI.Text.arguments([
          {"none", "gen reads the manifest in the working directory. It takes no path."}
        ])
      ),
      Muro.CLI.Text.section("OPTIONS", Muro.CLI.Text.options(options())),
      Muro.CLI.Text.section(
        "EXAMPLES",
        Muro.CLI.Text.examples(
          [
            {"muro gen", "Write every target the manifest names."},
            {"muro gen --check", "Exits 0 when those targets match. Writes nothing."},
            {"muro gen --skip-check",
             "Write every target without type-checking. The caller has already checked."}
          ],
          "\n\n"
        )
      ),
      Muro.CLI.Text.section(
        "EXIT CODES",
        Muro.CLI.Text.exits([
          {"0", "The targets were written, or --check found no difference and printed ok."},
          {"1",
           "A book fails, the version pin differs, a target disagrees, the manifest is missing, or an argument or flag is not accepted."}
        ])
      ),
      Muro.CLI.Text.section(
        "LEARN MORE",
        Muro.CLI.Text.pre(["https://muro-lang.dev/docs/gen"])
      )
    ])
  end

  @doc false
  def run(args) do
    {opts, rest, invalid} = OptionParser.parse(args, strict: switches())

    cond do
      invalid != [] ->
        {:raise, "", "unknown option: #{inspect(invalid)}"}

      rest != [] ->
        {:raise, "", "usage: mix muro.gen [--check] [--skip-check]"}

      true ->
        go(opts[:check] || false, opts[:skip_check] || false)
    end
  end

  defp go(check?, skip?) do
    root = Muro.Manifest.root()
    opts = [skip_check: skip?]

    with {:ok, manifest} <- load(root),
         :ok <- pin(manifest) do
      running = Mix.Tasks.Muro.version()

      if check? do
        case Muro.Gen.check(manifest, root, running, opts) do
          :ok -> {:ok, "ok\n", ""}
          {:error, message} -> {:raise, "", message}
        end
      else
        case Muro.Gen.generate(manifest, root, running, opts) do
          {:ok, lines} -> {:ok, Muro.CLI.join_lines(lines), ""}
          {:error, message} -> {:raise, "", message}
        end
      end
    end
  end

  defp load(root) do
    case Muro.Manifest.load(root) do
      {:ok, manifest} -> {:ok, manifest}
      {:error, message} -> {:raise, "", message}
    end
  end

  defp pin(manifest) do
    case Muro.Manifest.version_pin(manifest.version, Mix.Tasks.Muro.version()) do
      :ok -> :ok
      {:error, message} -> {:raise, "", message}
    end
  end
end

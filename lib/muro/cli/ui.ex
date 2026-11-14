defmodule Muro.CLI.Ui do
  @moduledoc false

  @doc false
  def switches, do: []

  @doc false
  def help do
    Muro.CLI.Text.page([
      Muro.CLI.Text.prose("""
      muro ui prints how to install muro_visor and open one book. The compiler does not start the explorer. muro_visor is its own package. mix muro.ui path.muro, from that package, starts the explorer and opens the book. It prints the URL of the address it binds and opens it. IPv4 loopback is http://127.0.0.1:4017/. An IPv6 address is http://[::1]:4017/. A hostname is http://localhost:4017/. The explorer is read-only: it does not emit code and it does not change the wall.
      """),
      Muro.CLI.Text.section("USAGE", Muro.CLI.Text.pre(["muro ui path.muro"])),
      Muro.CLI.Text.section(
        "ARGUMENTS",
        Muro.CLI.Text.arguments([
          {"path.muro", "Required. The book the explorer opens."}
        ])
      ),
      Muro.CLI.Text.section(
        "EXAMPLES",
        Muro.CLI.Text.examples([
          {"muro ui book.muro", "Print the install steps for this book."}
        ])
      ),
      Muro.CLI.Text.section(
        "EXIT CODES",
        Muro.CLI.Text.exits([
          {"0", "The install steps were printed."},
          {"1", "The path was omitted, more than one path was given, or a flag is unknown."}
        ])
      ),
      Muro.CLI.Text.section(
        "LEARN MORE",
        Muro.CLI.Text.pre(["https://muro-lang.dev/docs/explorer"])
      )
    ])
  end

  @doc false
  def run(args) do
    {_opts, paths, invalid} = OptionParser.parse(args, strict: switches())

    cond do
      invalid != [] ->
        {:raise, "", "unknown option: #{inspect(invalid)}"}

      length(paths) != 1 ->
        {:raise, "", "usage: muro ui path.muro"}

      true ->
        {:ok, instructions(hd(paths)), ""}
    end
  end

  defp instructions(path) do
    quoted = shell_quote(path)
    checkout = shell_quote(Path.expand(path))

    Muro.CLI.Text.page([
      Muro.CLI.Text.prose("""
      muro_visor draws this book. This command does not start the explorer. Add muro_visor to a Mix project, then open the book with its Mix task. That task prints the URL of the address it binds and opens it. IPv4 loopback is http://127.0.0.1:4017/. An IPv6 address is http://[::1]:4017/. A hostname is http://localhost:4017/.
      """),
      Muro.CLI.Text.section(
        "INSTALL",
        Muro.CLI.Text.pre(["{:muro_visor, \"~> 0.3.1\"}", "mix deps.get"])
      ),
      Muro.CLI.Text.section("OPEN", Muro.CLI.Text.pre(["mix muro.ui #{quoted}"])),
      Muro.CLI.Text.section(
        "FROM A CHECKOUT",
        Muro.CLI.Text.pre(["cd ui && mix deps.get && mix muro.ui #{checkout}"])
      ),
      Muro.CLI.Text.section(
        "LEARN MORE",
        Muro.CLI.Text.pre(["https://muro-lang.dev/docs/explorer"])
      )
    ])
  end

  defp shell_quote(path) do
    "'" <> String.replace(path, "'", "'\\''") <> "'"
  end
end

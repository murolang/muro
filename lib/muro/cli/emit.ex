defmodule Muro.CLI.Emit do
  @moduledoc false

  @doc false
  def switches, do: Enum.map(options(), &{&1.name, &1.type})

  @doc false
  def options do
    [
      %{
        name: :backend,
        type: :string,
        value: "NAME",
        default: "elixir",
        doc:
          "Which emitter to run. Spec and evidence are omitted. The executable writes no NIF: c is the header and the source only.",
        lines: [
          "elixir  one module on standard output",
          "c       <stem>.h and <stem>.c beside the book",
          "rust    <stem>.rs beside the book",
          "asm     <stem>.s, Thumb for Cortex-M0",
          "otp     <stem>_otp.ex, a GenServer per process",
          "fsm     one state-machine module on standard output",
          "exunit  one ExUnit module for the closed equations"
        ]
      },
      %{
        name: :node,
        type: :string,
        value: "NAME",
        default: "none",
        doc:
          "With the elixir backend, write <stem>_node.ex beside the book: one call for each cross, registered on that node. A stay emits no call. Other backends refuse the flag."
      },
      %{
        name: :imports,
        type: :boolean,
        default: "false",
        doc:
          "With --backend exunit, also collect the closed equations of the files this book imports directly. It is an error with any other backend. Absent, the suite is this file only."
      }
    ]
  end

  @doc false
  def help do
    Muro.CLI.Text.page([
      Muro.CLI.Text.prose("""
      muro emit reads one .muro file, checks it, and emits run definitions. Spec and evidence are omitted. elixir, the default, prints one module on standard output and writes no file. c, rust, and asm write a file beside the book and print that path. The executable does not load a Mix project, so c writes the .h and the .c only and does not build a NIF. otp writes a GenServer for each conforming process. fsm prints a state machine and leaves the transport with the host. exunit prints one ExUnit module for the book's closed equations. Nothing here is a proof that the host translation is the book. The proof stops at the run image.
      """),
      Muro.CLI.Text.section(
        "USAGE",
        Muro.CLI.Text.pre(["muro emit path.muro [--backend NAME] [--node NAME] [--imports]"])
      ),
      Muro.CLI.Text.section(
        "ARGUMENTS",
        Muro.CLI.Text.arguments([
          {"path.muro", "Required. The book to emit."}
        ])
      ),
      Muro.CLI.Text.section("OPTIONS", Muro.CLI.Text.options(options())),
      Muro.CLI.Text.section(
        "EXAMPLES",
        Muro.CLI.Text.examples(
          [
            {"muro emit book.muro", "Print the Elixir module."},
            {"muro emit book.muro --backend rust", "Write book.rs beside the book."},
            {"muro emit book.muro --backend c", "Write book.h and book.c. No NIF."},
            {"muro emit book.muro --backend exunit", "Print an ExUnit module."}
          ],
          "\n\n"
        )
      ),
      Muro.CLI.Text.section(
        "EXIT CODES",
        Muro.CLI.Text.exits([
          {"0", "The module or the files were emitted."},
          {"1",
           "The book does not check, the backend is unknown, the path is missing or not exactly one, or a flag does not apply."}
        ])
      ),
      Muro.CLI.Text.section(
        "LEARN MORE",
        Muro.CLI.Text.pre(["https://muro-lang.dev/docs/emit"])
      )
    ])
  end

  @doc false
  def run(args, opts \\ []) do
    nif = Keyword.get(opts, :nif, :auto)
    {parsed, paths, invalid} = OptionParser.parse(args, strict: switches())

    cond do
      invalid != [] ->
        {:raise, "", "unknown option: #{inspect(invalid)}"}

      true ->
        backend = Keyword.get(parsed, :backend, "elixir")
        node = Keyword.get(parsed, :node)
        imports? = Keyword.get(parsed, :imports, false)

        case paths do
          [path] -> emit(path, backend, node, imports?, nif)
          _other -> {:raise, "", "expected one path"}
        end
    end
  end

  defp emit(path, backend, node, imports?, nif) do
    cond do
      imports? and backend != "exunit" ->
        {:raise, "", "--imports is only valid with --backend exunit"}

      backend == "exunit" and is_nil(node) ->
        emit_exunit(path, imports?)

      true ->
        dispatch(path, backend, node, nif)
    end
  end

  defp emit_exunit(path, imports?) do
    opts = if imports?, do: [imports: true], else: []

    case Muro.emit_exunit(path, Muro.Emit.exunit_module(path), opts) do
      {:ok, %{source: src, skips: skips, tests: n}} ->
        stderr =
          Enum.map_join(skips, fn skip ->
            "skipped #{skip.name} (#{skip.file}:#{skip.line}): #{skip.reason}\n"
          end) <> "#{n} tests, #{length(skips)} skipped\n"

        {:ok, src <> "\n", stderr}

      {:error, message} ->
        {:raise, "", message}
    end
  end

  defp dispatch(path, "elixir", node, _nif) when is_binary(node) do
    case node_atom(node) do
      {:ok, atom} ->
        case Muro.emit_node(path, atom) do
          {:ok, files} -> {:ok, Muro.CLI.join_lines(files), ""}
          {:error, message} -> {:raise, "", message}
        end

      {:error, message} ->
        {:raise, "", message}
    end
  end

  defp dispatch(_path, _backend, node, _nif) when not is_nil(node) do
    {:raise, "", "--node writes the placement calls"}
  end

  defp dispatch(path, "elixir", nil, _nif) do
    case Muro.emit_file(path, Muro.Emit.elixir_module(path)) do
      {:ok, src} -> {:ok, src <> "\n", ""}
      {:error, message} -> {:raise, "", message}
    end
  end

  defp dispatch(path, "c", nil, nif) do
    case Muro.emit_c(path, nif: nif?(nif)) do
      {:ok, files} -> {:ok, Muro.CLI.join_lines(files), ""}
      {:error, message} -> {:raise, "", message}
    end
  end

  defp dispatch(path, "rust", nil, _nif) do
    files(Muro.emit_rust(path))
  end

  defp dispatch(path, "asm", nil, _nif) do
    files(Muro.emit_asm(path))
  end

  defp dispatch(path, "otp", nil, _nif) do
    files(Muro.emit_otp(path))
  end

  defp dispatch(path, "fsm", nil, _nif) do
    case Muro.emit_fsm(path, Muro.Emit.fsm_module(path)) do
      {:ok, src} -> {:ok, src <> "\n", ""}
      {:error, message} -> {:raise, "", message}
    end
  end

  defp dispatch(_path, other, nil, _nif) do
    {:raise, "", "unknown backend: #{other}"}
  end

  defp files({:ok, paths}), do: {:ok, Muro.CLI.join_lines(paths), ""}
  defp files({:error, message}), do: {:raise, "", message}

  defp nif?(:force), do: true
  defp nif?(:auto), do: mix_project_cwd?()

  # The executable does not load a host project, so this is false there
  # and `--backend c` writes only the `.h` and the `.c`. Inside `mix`,
  # the loaded project contains the working directory and the NIF is built.
  defp mix_project_cwd? do
    case Mix.Project.get() do
      nil ->
        false

      _project ->
        cwd = Path.expand(File.cwd!())
        root = Mix.Project.project_file() |> Path.dirname() |> Path.expand()
        cwd == root or String.starts_with?(cwd, root <> "/")
    end
  end

  defp node_atom(name) do
    if name =~ ~r/^[A-Za-z_][A-Za-z0-9_@.-]*$/ do
      {:ok, String.to_atom(name)}
    else
      {:error, "expected a node name"}
    end
  end
end

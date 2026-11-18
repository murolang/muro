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
          "zig     <stem>.zig beside the book",
          "js      <stem>.mjs and <stem>.d.ts beside the book",
          "asm     <stem>.s, Thumb for Cortex-M0",
          "otp     <stem>_otp.ex, a GenServer per process",
          "fsm     one state-machine module on standard output",
          "exunit  one ExUnit module for the closed equations",
          "mbi     <stem>.mbi beside the book, exactly one graded run"
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
      },
      %{
        name: :prefix,
        type: :string,
        value: "TEXT",
        default: "",
        doc:
          "With --backend c, prepend TEXT to every run the host calls and to that book's session entry points. TEXT is a C identifier, and it includes the separator, as in admit_. Other backends refuse the flag. Absent, the C names are unchanged."
      }
    ]
  end

  @doc false
  def help do
    Muro.CLI.Text.page([
      Muro.CLI.Text.prose("""
      muro emit reads one .muro file, checks it, and emits run definitions. Spec and evidence are omitted. elixir, the default, prints one module on standard output and writes no file. c, rust, zig, and asm write a file beside the book and print that path. js writes <stem>.mjs and <stem>.d.ts beside the book and prints both paths. The executable does not load a Mix project, so c writes the .h and the .c only and does not build a NIF. otp writes a GenServer for each conforming process. fsm prints a state machine and leaves the transport with the host. exunit prints one ExUnit module for the book's closed equations. mbi writes <stem>.mbi beside the book only when exactly one exported run erases, and prints that path. The binder grades stay. A refusal writes nothing and prints no path. An image already beside the book stays byte for byte, including when the book has no exported run and when it has more than one. muro-beam loads that file. It is not Erlang BEAM bytecode. Data, a pair, a word, or a stream is refused. A run the entry calls is a definition in the image. A name that is not a run, and two definitions that call each other, are refused. Zero exported runs, and more than one, are refused. muro-beam checks the image again. Writing the file is not that check. Nothing here is a proof that the host translation is the book. The proof stops at the run image.
      """),
      Muro.CLI.Text.section(
        "USAGE",
        Muro.CLI.Text.pre([
          "muro emit path.muro [--backend NAME] [--node NAME] [--imports]",
          "    [--prefix TEXT]"
        ])
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
            {"muro emit book.muro --backend zig", "Write book.zig beside the book."},
            {"muro emit book.muro --backend js", "Write book.mjs and book.d.ts."},
            {"muro emit book.muro --backend c", "Write book.h and book.c. No NIF."},
            {"muro emit book.muro --backend exunit", "Print an ExUnit module."},
            {"muro emit book.muro --backend mbi", "Write book.mbi beside the book."}
          ],
          "\n\n"
        )
      ),
      Muro.CLI.Text.section(
        "EXIT CODES",
        Muro.CLI.Text.exits([
          {"0",
           "The module was printed, or the files were written. mbi writes one .mbi and prints its path. Writing it is not acceptance."},
          {"1",
           "The book does not check, an .mbi image refuses a run, the backend is unknown, the path is missing or not exactly one, or a flag does not apply."}
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
        prefix = Keyword.get(parsed, :prefix)

        case paths do
          [path] -> emit(path, backend, node, imports?, nif, prefix)
          _other -> {:raise, "", "expected one path"}
        end
    end
  end

  defp emit(path, backend, node, imports?, nif, prefix) do
    cond do
      backend == "beam" ->
        {:raise, "",
         "--backend beam is refused. Use --backend mbi. The file is the .mbi image muro-beam loads, not Erlang BEAM bytecode."}

      imports? and backend != "exunit" ->
        {:raise, "", "--imports is only valid with --backend exunit"}

      prefix not in [nil, ""] and backend != "c" ->
        {:raise, "", "--prefix is only valid with --backend c"}

      backend == "exunit" and is_nil(node) ->
        emit_exunit(path, imports?)

      backend == "c" and is_nil(node) ->
        emit_c(path, nif, prefix)

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

  defp dispatch(path, "rust", nil, _nif) do
    files(Muro.emit_rust(path))
  end

  defp dispatch(path, "zig", nil, _nif) do
    files(Muro.emit_zig(path))
  end

  defp dispatch(path, "js", nil, _nif) do
    files(Muro.emit_js(path))
  end

  defp dispatch(path, "asm", nil, _nif) do
    files(Muro.emit_asm(path))
  end

  defp dispatch(path, "otp", nil, _nif) do
    files(Muro.emit_otp(path))
  end

  # The image is written only when exactly one exported run erases.
  # Exit 0 prints that path. A refusal writes nothing and leaves a file
  # already beside the book byte for byte, so stdout stays empty.
  defp dispatch(path, "mbi", nil, _nif) do
    case Muro.emit_mbi(path) do
      {:ok, paths} ->
        {:ok, Muro.CLI.join_lines(paths), ""}

      {:error, message} ->
        {:raise, "", message}
    end
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

  defp emit_c(path, nif, prefix) do
    opts = [nif: nif?(nif)]
    opts = if prefix in [nil, ""], do: opts, else: Keyword.put(opts, :c_prefix, prefix)

    case Muro.emit_c(path, opts) do
      {:ok, files} -> {:ok, Muro.CLI.join_lines(files), ""}
      {:error, message} -> {:raise, "", message}
    end
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

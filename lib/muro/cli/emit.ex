defmodule Muro.CLI.Emit do
  @moduledoc false

  @switches [backend: :string, node: :string, imports: :boolean]

  @doc false
  def run(args, opts \\ []) do
    nif = Keyword.get(opts, :nif, :auto)
    {parsed, paths, invalid} = OptionParser.parse(args, strict: @switches)

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

defmodule Muro.Load do
  @moduledoc """
  Resolve `import` for a file.

  The string is the file. The path is relative to the importing file.
  There is no load path. The imported file is checked, and its data,
  constructors, and definitions join the importer. Evidence stays in that
  book; emit drops it, as it drops any evidence.
  """

  alias Muro.{Check, Parser, Prelude}

  @doc """
  The importer's own entries, then each imported book, with `import`
  lines removed. `{:error, msg}` names a missing file, a cycle, or a
  name declared on both sides.
  """
  def file(path, opts \\ []) when is_binary(path) do
    resolve(Path.expand(path), [], opts)
  end

  defp resolve(path, stack, opts) do
    cond do
      path in stack ->
        {:error, cycle(stack, path)}

      not File.regular?(path) ->
        {:error, "missing file #{display(path)}"}

      true ->
        with {:ok, src} <- read(path),
             {:ok, parsed} <- parse(src, path),
             {:ok, flat} <- inline(parsed, path, stack, opts),
             :ok <- check(flat, path, opts) do
          {:ok, flat}
        end
    end
  end

  defp read(path) do
    case File.read(path) do
      {:ok, src} -> {:ok, src}
      {:error, _} -> {:error, "missing file #{display(path)}"}
    end
  end

  defp parse(src, path) do
    case Parser.parse(src) do
      {:ok, book} -> {:ok, book}
      {:error, msg} -> {:error, prefix_locs(msg, path)}
    end
  end

  defp check(book, path, opts) do
    case Check.check_sig(Prelude.for_check(book), opts) do
      :ok -> :ok
      {:error, msg} -> {:error, prefix_locs(msg, path)}
    end
  end

  defp inline(entries, path, stack, opts) do
    entries = Enum.map(entries, &Map.put(&1, :file, path))
    {own, imps} = Enum.split_with(entries, &(Map.get(&1, :kind) != :import))

    with {:ok, loaded} <- load_all(imps, [path | stack], opts),
         :ok <- clashes(own, loaded) do
      {:ok, own ++ Enum.concat(loaded)}
    end
  end

  defp load_all(imps, stack, opts) do
    Enum.reduce_while(imps, {:ok, []}, fn imp, {:ok, acc} ->
      full = imp.path |> Path.expand(Path.dirname(imp.file))

      case resolve(full, stack, opts) do
        {:ok, book} -> {:cont, {:ok, acc ++ [book]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp clashes(own, loaded) do
    seen = index(own)

    Enum.reduce_while(loaded, {:ok, seen}, fn book, {:ok, seen} ->
      case clash_book(seen, book) do
        {:ok, seen1} -> {:cont, {:ok, seen1}}
        {:error, _} = err -> {:halt, err}
      end
    end)
    |> case do
      {:ok, _} -> :ok
      {:error, _} = err -> err
    end
  end

  defp index(entries) do
    Enum.reduce(entries, %{}, fn d, seen ->
      Enum.reduce(decl_names(d), seen, fn name, seen -> Map.put_new(seen, name, d) end)
    end)
  end

  defp clash_book(seen, entries) do
    Enum.reduce_while(entries, {:ok, seen}, fn d, {:ok, seen} ->
      case clash_names(seen, d, decl_names(d)) do
        {:ok, seen1} -> {:cont, {:ok, seen1}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp clash_names(seen, _d, []), do: {:ok, seen}

  defp clash_names(seen, d, [name | names]) do
    case Map.fetch(seen, name) do
      {:ok, prev} ->
        {:error, "#{site(prev)}duplicate name #{name}\n#{site(d)}duplicate name #{name}"}

      :error ->
        clash_names(Map.put(seen, name, d), d, names)
    end
  end

  defp decl_names(%{kind: :data, name: name, ctors: ctors}) do
    [name | Enum.map(ctors, & &1.name)]
  end

  defp decl_names(%{kind: :import}), do: []
  defp decl_names(%{name: name}), do: [name]

  defp site(d) do
    loc =
      case Map.get(d, :loc) do
        {line, col} -> "#{line}:#{col}: "
        _ -> ""
      end

    case Map.get(d, :file) do
      nil -> loc
      path -> "#{display(path)}:#{loc}"
    end
  end

  defp cycle(stack, path) do
    files =
      stack
      |> Enum.reverse()
      |> Enum.concat([path])
      |> Enum.map_join("\n", &display/1)

    "import cycle\n#{files}"
  end

  defp prefix_locs(msg, path) do
    file = display(path)
    Regex.replace(~r/^(\d+:\d+:)/m, msg, "#{file}:\\1")
  end

  defp display(path) do
    case Path.relative_to_cwd(path) do
      ^path -> path
      rel -> rel
    end
  end
end

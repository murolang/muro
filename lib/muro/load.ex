defmodule Muro.Load do
  @moduledoc """
  Resolve `import` for a file.

  The string is the file. The path is relative to the importing file.
  There is no load path. The imported file is checked, and its data,
  constructors, and definitions join the importer, once each when the
  file is reached by more than one import. Evidence stays in that
  book; emit drops it, as it drops any evidence.

  A `param` is supplied by the declaration of the same name in the book
  that imports its file, with the same tag and a type that converts.
  A book with a param nobody supplied yet is checked where it is
  imported, and its params pass upward until one is supplied.
  """

  alias Muro.{Check, Parser, Prelude}

  @doc """
  The importer's own entries, then each imported book, with `import`
  lines removed. `{:error, msg}` names a missing file, a cycle, or a
  name declared on both sides.
  """
  def file(path, opts \\ []) when is_binary(path) do
    with {:ok, flat} <- resolve(Path.expand(path), [], opts),
         :ok <- all_supplied(flat) do
      {:ok, flat}
    end
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
             {:ok, {flat, checks}} <- supply(flat),
             :ok <- check_supplied(flat, checks, path, opts) do
          {:ok, flat}
        end
    end
  end

  # A book with a param nobody supplied yet is checked where it is
  # imported, once its params are definitions.
  defp check_supplied(flat, checks, path, opts) do
    if Enum.any?(flat, &param?/1), do: :ok, else: check(flat ++ checks, path, opts)
  end

  defp param?(d), do: Map.get(d, :kind) == :param

  # A param is supplied by the declaration of the same name in the book
  # that imports it. Its type is checked by a definition of that type
  # whose body is the name; the definition is checked, never returned.
  defp supply(flat) do
    {params, rest} = Enum.split_with(flat, &param?/1)
    decls = index(rest)

    Enum.reduce_while(params, {:ok, {rest, []}}, fn p, {:ok, {book, checks}} ->
      case Map.fetch(decls, p.name) do
        :error ->
          {:cont, {:ok, {book ++ [p], checks}}}

        {:ok, d} ->
          cond do
            Map.get(d, :file) == Map.get(p, :file) ->
              {:halt,
               {:error, "#{site(p)}duplicate name #{p.name}\n#{site(d)}duplicate name #{p.name}"}}

            decl_mode(d) != p.mode ->
              {:halt,
               {:error,
                "#{site(d)}#{p.name} is #{decl_mode(d)}; the param it supplies is #{p.mode}\n" <>
                  "#{site(p)}param #{p.name} : #{p.mode}"}}

            true ->
              {:cont, {:ok, {book, checks ++ [param_check(p)]}}}
          end
      end
    end)
  end

  defp decl_mode(%{kind: :data}), do: :spec
  defp decl_mode(d), do: Map.get(d, :mode)

  defp param_check(p) do
    p
    |> Map.take([:mode, :export, :type, :loc, :file])
    |> Map.merge(%{name: "#{p.name} (param)", body: {:var, p.name}})
  end

  defp all_supplied(flat) do
    case Enum.filter(flat, &param?/1) do
      [] ->
        :ok

      ps ->
        {:error,
         Enum.map_join(ps, "\n", fn p ->
           "#{site(p)}param #{p.name} is supplied by a file that imports this one"
         end)}
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
    book = Enum.map(book, &relocate(&1, path))

    case Check.check_sig(Prelude.for_check(book), opts) do
      :ok -> :ok
      {:error, msg} -> {:error, prefix_locs(msg, path)}
    end
  end

  # An entry from another file reports at its own file.
  defp relocate(%{file: file, loc: {line, col}} = d, path) when file != path,
    do: %{d | loc: {display(file), line, col}}

  defp relocate(d, _path), do: d

  defp inline(entries, path, stack, opts) do
    entries = Enum.map(entries, &Map.put(&1, :file, path))
    {own, imps} = Enum.split_with(entries, &(Map.get(&1, :kind) != :import))

    with {:ok, loaded} <- load_all(imps, [path | stack], opts),
         :ok <- clashes(own, loaded) do
      {:ok, own ++ Enum.uniq_by(Enum.concat(loaded), &origin/1)}
    end
  end

  # A file reached by two imports brings the same entries twice.
  defp origin(d), do: {Map.get(d, :file), Map.get(d, :loc)}

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
        if origin(prev) == origin(d) do
          clash_names(seen, d, names)
        else
          {:error, "#{site(prev)}duplicate name #{name}\n#{site(d)}duplicate name #{name}"}
        end

      :error ->
        clash_names(Map.put(seen, name, d), d, names)
    end
  end

  defp decl_names(%{kind: :data, name: name, ctors: ctors}) do
    [name | Enum.map(ctors, & &1.name)]
  end

  defp decl_names(%{kind: :import}), do: []
  defp decl_names(%{kind: :param}), do: []
  defp decl_names(%{kind: :move}), do: []
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

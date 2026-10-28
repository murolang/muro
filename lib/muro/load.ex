defmodule Muro.Load do
  @moduledoc """
  Resolve `import` for a file.

  The string is the file. A relative path is relative to the importing
  file. There is no load path. The imported file is checked, and its
  data, constructors, and definitions join the importer, once each when
  the file is reached by more than one import. Evidence stays in that
  book; emit drops it, as it drops any evidence.

  `import "pkg:name/file.muro"` loads `<root>/muro_deps/name/file.muro`.
  The root is the `root:` option, or the nearest ancestor of the entry
  book that contains `muro.exs` or `mix.exs`. The file's bytes are
  hashed once and must match `muro.lock`. This module does not fetch
  and does not run git.

  A `param` is supplied by the declaration of the same name in the book
  that imports its file, with the same tag and a type that converts.
  A book with a param nobody supplied yet is checked where it is
  imported, and its params pass upward until one is supplied.

  `params: :open` checks that book anyway. Each remaining param is an
  assumption: it has a type and does not reduce. The default, and every
  caller except the exunit entry points, is `params: :closed`, which
  refuses a param nobody supplied. The message is
  `param <name> is supplied by a file that imports this one`.
  """

  alias Muro.{Check, Parser, Prelude}

  @dep_name ~r/\A[a-z][a-z0-9_]*\z/

  @doc """
  The importer's own entries, then each imported book, with `import`
  lines removed. `{:error, msg}` names a missing file, a cycle, a
  package whose bytes differ from `muro.lock`, or a name declared on
  both sides.
  """
  def file(path, opts \\ []) when is_binary(path) do
    case open(path, opts) do
      {:ok, flat, _lines} -> {:ok, flat}
      {:error, _} = err -> err
    end
  end

  @doc """
  `file/2`, and the `conforms to` lines for the packages the book
  loaded. `lines` is empty when the book imports no package.

  `params: :open` allows a book whose params are still unsupplied and
  checks them as assumptions. The default refuses that book.
  """
  def open(path, opts \\ []) when is_binary(path) do
    path = Path.expand(path)
    ctx = new_ctx(opts, path)

    case resolve(path, [], opts, ctx) do
      {:ok, flat, ctx} ->
        case all_supplied(flat, path, opts, ctx) do
          :ok -> {:ok, flat, conform_lines(ctx)}
          {:error, msg} -> {:error, note_packages(msg)}
        end

      {:error, msg} ->
        {:error, note_packages(msg)}
    end
  end

  @doc """
  Absolute paths of the files `path` imports directly, in declaration
  order.

  A path is listed once, the first time it appears. The book's own path
  is not listed. Imports of those files are not followed. `{:error, msg}`
  when `path` does not parse. This does not check the book.
  """
  def direct_imports(path, opts \\ []) when is_binary(path) do
    path = Path.expand(path)
    ctx = new_ctx(opts, path)

    with {:ok, src} <- read(path, ctx),
         {:ok, parsed} <- parse(src, path, ctx) do
      paths =
        parsed
        |> Enum.filter(&(Map.get(&1, :kind) == :import))
        |> Enum.map(&Map.put(&1, :file, path))
        |> Enum.reduce([], fn imp, acc ->
          case import_target(imp, ctx) do
            {:ok, target} ->
              target = Path.expand(target)
              if target in acc, do: acc, else: acc ++ [target]

            {:error, _} ->
              acc
          end
        end)

      {:ok, paths}
    end
  end

  @doc false
  def classify_import("pkg:" <> rest), do: classify_pkg(rest)
  def classify_import(path) when is_binary(path), do: :relative

  defp new_ctx(opts, path) do
    looked = if File.dir?(path), do: path, else: Path.dirname(path)

    root =
      case Keyword.get(opts, :root) do
        r when is_binary(r) -> Muro.Manifest.canonical(r)
        _ -> Muro.Manifest.find_root(path)
      end

    %{root: root, looked: looked, deps: :unset, lock: :unset, manifest: nil, packages: %{}}
  end

  defp resolve(path, stack, opts, ctx) do
    if path in stack do
      {:error, cycle(stack, path, ctx)}
    else
      case maybe_package(path, ctx) do
        {:package, name, rel, ctx} -> resolve_package(path, name, rel, stack, opts, ctx)
        {:ordinary, ctx} -> resolve_ordinary(path, stack, opts, ctx)
        {:error, _} = err -> err
      end
    end
  end

  defp resolve_ordinary(path, stack, opts, ctx) do
    if File.regular?(path) do
      with {:ok, src} <- read(path, ctx),
           {:ok, parsed} <- parse(src, path, ctx),
           {:ok, flat, ctx} <- inline(parsed, path, stack, opts, ctx),
           {:ok, {flat, checks}, ctx} <- supply(flat, ctx),
           :ok <- check_supplied(flat, checks, path, opts, ctx) do
        {:ok, flat, ctx}
      end
    else
      {:error, "missing file #{display(path, ctx)}"}
    end
  end

  defp resolve_package(path, name, rel, stack, opts, ctx) do
    with {:ok, ctx} <- ensure_lock(ctx),
         :ok <- require_source(ctx, name),
         {:ok, expected} <- require_locked(ctx, name, rel),
         {:ok, bytes} <- read_locked(path, name, rel),
         :ok <- require_hash(name, rel, bytes, expected),
         {:ok, parsed} <- parse(bytes, path, ctx),
         {:ok, flat, ctx} <- inline(parsed, path, stack, opts, ctx),
         {:ok, {flat, checks}, ctx} <- supply(flat, ctx),
         :ok <- check_supplied(flat, checks, path, opts, ctx) do
      {:ok, flat, remember(ctx, path, name, rel, bytes)}
    end
  end

  defp maybe_package(path, ctx) do
    case package_identity(path, ctx) do
      :no ->
        {:ordinary, ctx}

      {name, rel} ->
        with {:ok, ctx} <- ensure_deps(ctx) do
          if dep?(ctx, name) do
            {:package, name, rel, ctx}
          else
            {:ordinary, ctx}
          end
        end
    end
  end

  defp package_identity(_path, %{root: nil}), do: :no

  defp package_identity(path, %{root: root}) do
    if String.contains?(path, "/muro_deps/") do
      package_under(path, root)
    else
      :no
    end
  end

  defp package_under(path, root) do
    base = Muro.Manifest.canonical(Path.join(root, "muro_deps"))
    full = Muro.Manifest.canonical(path)
    prefix = base <> "/"

    if String.starts_with?(full, prefix) do
      rest = String.replace_prefix(full, prefix, "")

      case String.split(rest, "/", parts: 2) do
        [name, rel] ->
          if name_ok?(name) and rel != "" do
            {name, rel}
          else
            :no
          end

        _other ->
          :no
      end
    else
      :no
    end
  end

  # A book with a param nobody supplied yet is checked where it is
  # imported, once its params are definitions.
  defp check_supplied(flat, checks, path, opts, ctx) do
    if Enum.any?(flat, &param?/1), do: :ok, else: check(flat ++ checks, path, opts, ctx)
  end

  defp param?(d), do: Map.get(d, :kind) == :param

  # A param is supplied by the declaration of the same name in the book
  # that imports it. Its type is checked by a definition of that type
  # whose body is the name; the definition is checked, never returned.
  defp supply(flat, ctx) do
    {params, rest} = Enum.split_with(flat, &param?/1)
    decls = index(rest)

    result =
      Enum.reduce_while(params, {:ok, {rest, []}}, fn p, {:ok, {book, checks}} ->
        case Map.fetch(decls, p.name) do
          :error ->
            {:cont, {:ok, {book ++ [p], checks}}}

          {:ok, d} ->
            cond do
              Map.get(d, :file) == Map.get(p, :file) ->
                {:halt,
                 {:error,
                  "#{site(p, ctx)}duplicate name #{p.name}\n#{site(d, ctx)}duplicate name #{p.name}"}}

              decl_mode(d) != p.mode ->
                {:halt,
                 {:error,
                  "#{site(d, ctx)}#{p.name} is #{decl_mode(d)}; the param it supplies is #{p.mode}\n" <>
                    "#{site(p, ctx)}param #{p.name} : #{p.mode}"}}

              true ->
                {:cont, {:ok, {book, checks ++ [param_check(p)]}}}
            end
        end
      end)

    case result do
      {:ok, pair} -> {:ok, pair, ctx}
      {:error, _} = err -> err
    end
  end

  defp decl_mode(%{kind: :data}), do: :spec
  defp decl_mode(d), do: Map.get(d, :mode)

  defp param_check(p) do
    p
    |> Map.take([:mode, :export, :type, :loc, :file])
    |> Map.merge(%{name: "#{p.name} (param)", body: {:var, p.name}})
  end

  # `params: :open` checks the book with the remaining params as
  # assumptions. Every other caller still refuses them, with the same
  # message as before.
  defp all_supplied(flat, path, opts, ctx) do
    case Enum.filter(flat, &param?/1) do
      [] ->
        :ok

      ps ->
        if Keyword.get(opts, :params) == :open do
          check(flat, path, opts, ctx)
        else
          {:error,
           Enum.map_join(ps, "\n", fn p ->
             "#{site(p, ctx)}param #{p.name} is supplied by a file that imports this one"
           end)}
        end
    end
  end

  defp import_target(imp, ctx) do
    case classify_import(imp.path) do
      {:pkg, name, rel} ->
        if ctx.root == nil do
          {:error, :no_root}
        else
          {:ok, Path.join([ctx.root, "muro_deps", name | String.split(rel, "/")])}
        end

      :relative ->
        {:ok, Path.expand(imp.path, Path.dirname(imp.file))}

      :bad ->
        {:error, :bad}
    end
  end

  defp read(path, ctx) do
    case File.read(path) do
      {:ok, src} -> {:ok, src}
      {:error, _} -> {:error, "missing file #{display(path, ctx)}"}
    end
  end

  defp read_locked(path, name, rel) do
    case File.read(path) do
      {:ok, bytes} -> {:ok, bytes}
      {:error, _} -> {:error, "#{pkg_display(name, rel)} is missing; run mix muro.deps.get"}
    end
  end

  defp parse(src, path, ctx) do
    case Parser.parse(src) do
      {:ok, book} -> {:ok, book}
      {:error, msg} -> {:error, prefix_locs(msg, path, ctx)}
    end
  end

  defp check(book, path, opts, ctx) do
    book = Enum.map(book, &relocate(&1, path, ctx))

    case Check.check_sig(Prelude.for_check(book), opts) do
      :ok -> :ok
      {:error, msg} -> {:error, prefix_locs(msg, path, ctx)}
    end
  end

  # An entry from another file reports at its own file.
  defp relocate(%{file: file, loc: {line, col}} = d, path, ctx) when file != path,
    do: %{d | loc: {display(file, ctx), line, col}}

  defp relocate(d, _path, _ctx), do: d

  defp inline(entries, path, stack, opts, ctx) do
    entries = Enum.map(entries, &Map.put(&1, :file, path))
    {own, imps} = Enum.split_with(entries, &(Map.get(&1, :kind) != :import))

    with {:ok, loaded, ctx} <- load_all(imps, [path | stack], opts, ctx),
         :ok <- clashes(own, loaded, ctx) do
      {:ok, own ++ Enum.uniq_by(Enum.concat(loaded), &origin/1), ctx}
    end
  end

  # A file reached by two imports brings the same entries twice.
  defp origin(d), do: {Map.get(d, :file), Map.get(d, :loc)}

  defp load_all(imps, stack, opts, ctx) do
    Enum.reduce_while(imps, {:ok, [], ctx}, fn imp, {:ok, acc, ctx} ->
      case resolve_import(imp, stack, opts, ctx) do
        {:ok, book, ctx} -> {:cont, {:ok, acc ++ [book], ctx}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp resolve_import(imp, stack, opts, ctx) do
    case classify_import(imp.path) do
      {:pkg, name, rel} ->
        resolve_pkg(imp, name, rel, stack, opts, ctx)

      :bad ->
        {:error, "#{site(imp, ctx)}bad package import \"#{imp.path}\""}

      :relative ->
        full = Path.expand(imp.path, Path.dirname(imp.file))

        case stays_in_package(imp, full, ctx) do
          :ok -> resolve(full, stack, opts, ctx)
          {:error, _} = err -> err
        end
    end
  end

  defp resolve_pkg(imp, name, rel, stack, opts, ctx) do
    if ctx.root == nil do
      {:error, no_manifest(imp, ctx)}
    else
      with {:ok, ctx} <- ensure_deps(ctx) do
        if dep?(ctx, name) do
          path = Path.join([ctx.root, "muro_deps", name | String.split(rel, "/")])
          resolve(path, stack, opts, ctx)
        else
          {:error, unknown_dep(imp, name, ctx)}
        end
      end
    end
  end

  defp stays_in_package(imp, full, ctx) do
    case package_identity(imp.file, ctx) do
      :no ->
        :ok

      {name, _rel} ->
        root = Muro.Manifest.canonical(Path.join([ctx.root, "muro_deps", name]))
        full_c = Muro.Manifest.canonical(full)

        if String.starts_with?(full_c, root <> "/") do
          :ok
        else
          {:error,
           "#{site(imp, ctx)}import \"#{imp.path}\" in package #{name} (#{display(imp.file, ctx)}) leaves the package for #{display(full, ctx)}"}
        end
    end
  end

  defp no_manifest(imp, ctx) do
    "#{site(imp, ctx)}no manifest found for package import \"#{imp.path}\" " <>
      "(looked for muro.exs or mix.exs from #{ctx.looked} upward)"
  end

  defp unknown_dep(imp, name, ctx) do
    file = ctx.manifest || "missing"
    "#{site(imp, ctx)}package #{name} is not in muro_deps: (manifest #{file})"
  end

  defp clashes(own, loaded, ctx) do
    seen = index(own)

    Enum.reduce_while(loaded, {:ok, seen}, fn book, {:ok, seen} ->
      case clash_book(seen, book, ctx) do
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

  defp clash_book(seen, entries, ctx) do
    Enum.reduce_while(entries, {:ok, seen}, fn d, {:ok, seen} ->
      case clash_names(seen, d, decl_names(d), ctx) do
        {:ok, seen1} -> {:cont, {:ok, seen1}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp clash_names(seen, _d, [], _ctx), do: {:ok, seen}

  defp clash_names(seen, d, [name | names], ctx) do
    case Map.fetch(seen, name) do
      {:ok, prev} ->
        if origin(prev) == origin(d) do
          clash_names(seen, d, names, ctx)
        else
          {:error,
           "#{site(prev, ctx)}duplicate name #{name}\n#{site(d, ctx)}duplicate name #{name}"}
        end

      :error ->
        clash_names(Map.put(seen, name, d), d, names, ctx)
    end
  end

  defp decl_names(%{kind: :data, name: name, ctors: ctors}) do
    [name | Enum.map(ctors, & &1.name)]
  end

  defp decl_names(%{kind: :import}), do: []
  defp decl_names(%{kind: :param}), do: []
  defp decl_names(%{kind: :move}), do: []
  # Same name as the data type. Duplicate reprs are the checker's refusal.
  defp decl_names(%{kind: :repr}), do: []
  defp decl_names(%{name: name}), do: [name]

  defp ensure_deps(%{deps: {:ok, _deps}} = ctx), do: {:ok, ctx}

  defp ensure_deps(%{deps: :unset, root: root} = ctx) do
    case Muro.Manifest.load_deps(root) do
      {:ok, deps} ->
        {:ok, %{ctx | deps: {:ok, deps}, manifest: Muro.Manifest.manifest_name(root)}}

      {:error, _} = err ->
        err
    end
  end

  defp ensure_lock(%{lock: {:ok, _map}} = ctx), do: {:ok, ctx}
  defp ensure_lock(%{lock: :missing} = ctx), do: {:ok, ctx}

  defp ensure_lock(%{lock: :unset, root: root} = ctx) when is_binary(root) do
    case File.read(Path.join(root, "muro.lock")) do
      {:error, :enoent} ->
        {:ok, %{ctx | lock: :missing}}

      {:ok, text} ->
        case Muro.Lock.decode(text) do
          {:ok, map} -> {:ok, %{ctx | lock: {:ok, map}}}
          {:error, _} = err -> err
        end

      {:error, reason} ->
        {:error, "muro.lock could not be read (#{inspect(reason)}); run mix muro.deps.get"}
    end
  end

  defp ensure_lock(ctx), do: {:ok, %{ctx | lock: :missing}}

  defp dep?(%{deps: {:ok, deps}}, name), do: Enum.any?(deps, &(&1.name == name))

  defp find_dep(%{deps: {:ok, deps}}, name), do: Enum.find(deps, &(&1.name == name))

  defp require_source(ctx, name) do
    case lock_entry(ctx, name) do
      {:ok, entry} ->
        dep = find_dep(ctx, name)

        if entry.source == dep.source do
          :ok
        else
          {:error,
           "muro.lock is out of date for #{name}: manifest says #{Muro.Lock.show(dep.source)}, " <>
             "lock has #{Muro.Lock.show(entry.source)}; run mix muro.deps.get"}
        end

      _other ->
        :ok
    end
  end

  defp require_locked(ctx, name, rel) do
    shown = pkg_display(name, rel)

    case ctx.lock do
      :missing ->
        {:error, "no muro.lock for package #{name} (#{shown}); run mix muro.deps.get"}

      {:ok, map} ->
        case Map.fetch(map, name) do
          :error ->
            {:error, "package #{name} (#{shown}) is not in muro.lock; run mix muro.deps.get"}

          {:ok, entry} ->
            case Map.fetch(entry.files, rel) do
              {:ok, hash} ->
                {:ok, hash}

              :error ->
                {:error, "#{shown} is not in muro.lock; run mix muro.deps.get"}
            end
        end
    end
  end

  defp lock_entry(%{lock: {:ok, map}}, name), do: Map.fetch(map, name)
  defp lock_entry(_ctx, _name), do: :error

  defp require_hash(name, rel, bytes, expected) do
    actual = Muro.Hash.sha256(bytes)

    if actual == expected do
      :ok
    else
      {:error,
       "#{pkg_display(name, rel)} changed since muro.lock (expected sha256 #{expected}, " <>
         "found sha256 #{actual}; run mix muro.deps.get to fetch it again)"}
    end
  end

  defp remember(ctx, path, name, rel, bytes) do
    {:ok, entry} = lock_entry(ctx, name)
    key = Muro.Manifest.canonical(path)

    packages =
      Map.put(ctx.packages, key, %{name: name, rel: rel, bytes: bytes, version: entry.version})

    %{ctx | packages: packages}
  end

  defp conform_lines(ctx) do
    ctx.packages
    |> Map.values()
    |> Enum.group_by(& &1.name)
    |> Enum.sort_by(fn {name, _files} -> name end)
    |> Enum.map(fn {name, files} ->
      [%{version: version} | _] = files
      payload = Enum.map(files, fn file -> {name <> "/" <> file.rel, file.bytes} end)
      "conforms to #{name} #{version} (sha256 #{Muro.Hash.files(payload)})"
    end)
  end

  defp classify_pkg(rest) do
    case String.split(rest, "/", parts: 2) do
      [name, path] ->
        if name_ok?(name) and pkg_path?(path) do
          {:pkg, name, path}
        else
          :bad
        end

      _other ->
        :bad
    end
  end

  defp name_ok?(name), do: Regex.match?(@dep_name, name)

  defp pkg_path?(path) do
    String.ends_with?(path, ".muro") and not String.contains?(path, "\\") and
      not String.contains?(path, "\n") and not String.starts_with?(path, "/") and
      segments_ok?(path)
  end

  defp segments_ok?(path) do
    segs = String.split(path, "/")
    segs != [] and Enum.all?(segs, fn seg -> seg not in ["", ".", ".."] end)
  end

  defp pkg_display(name, rel), do: "muro_deps/" <> name <> "/" <> rel

  defp note_packages(msg) do
    case Regex.run(~r/muro_deps\/([a-z][a-z0-9_]*)\/[^\s:]*\.muro:\d+:\d+:/, msg, return: :index) do
      [{start, _len}, {nstart, nlen}] ->
        name = binary_part(msg, nstart, nlen)
        prefix = binary_part(msg, 0, start)

        if String.contains?(prefix, "in package " <> name) do
          msg
        else
          prefix <>
            "in package " <> name <> "\n" <> binary_part(msg, start, byte_size(msg) - start)
        end

      _other ->
        msg
    end
  end

  defp site(d, ctx) do
    loc =
      case Map.get(d, :loc) do
        {line, col} -> "#{line}:#{col}: "
        _ -> ""
      end

    case Map.get(d, :file) do
      nil -> loc
      path -> "#{display(path, ctx)}:#{loc}"
    end
  end

  defp cycle(stack, path, ctx) do
    files =
      stack
      |> Enum.reverse()
      |> Enum.concat([path])
      |> Enum.map_join("\n", &display(&1, ctx))

    "import cycle\n#{files}"
  end

  defp prefix_locs(msg, path, ctx) do
    file = display(path, ctx)
    Regex.replace(~r/^(\d+:\d+:)/m, msg, "#{file}:\\1")
  end

  defp display(path, ctx) do
    case package_identity(path, ctx) do
      {name, rel} -> pkg_display(name, rel)
      :no -> cwd_display(path)
    end
  end

  defp cwd_display(path) do
    case Path.relative_to_cwd(path) do
      ^path -> path
      rel -> rel
    end
  end
end

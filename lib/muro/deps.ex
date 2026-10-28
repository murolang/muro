defmodule Muro.Deps do
  @moduledoc """
  Resolve `muro_deps:` and write `muro_deps/` and `muro.lock`.

  Every package is fetched into a temporary directory and checked
  before `muro_deps/` or `muro.lock` is changed. A failure leaves
  both as they were. Directories under `muro_deps/` are removed
  only when the previous lock named them and the manifest no longer
  does.

  `mix muro.check` and `mix muro.gen` do not call this module.
  """

  @doc """
  Fetch every package in the manifest at `root`.

  `{:ok, lines}` is the report. `{:error, message}` names the
  package that failed and says the lock and `muro_deps/` are
  unchanged.
  """
  def get(root) when is_binary(root) do
    root = Muro.Manifest.canonical(root)

    with {:ok, deps} <- Muro.Manifest.load_deps(root),
         {:ok, old, old_bytes} <- read_lock(root) do
      if deps == [] do
        clear(root, old)
      else
        case fetch_all(deps) do
          {:ok, fetched} -> commit(root, old, old_bytes, fetched)
          {:error, msg} -> {:error, annotate(msg)}
        end
      end
    else
      {:error, msg} -> {:error, annotate(msg)}
    end
  end

  defp fetch_all(deps) do
    Enum.reduce_while(deps, {:ok, []}, fn dep, {:ok, acc} ->
      case fetch_one(dep) do
        {:ok, result} -> {:cont, {:ok, acc ++ [{dep, result}]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp fetch_one(%{kind: :git} = dep), do: Muro.Deps.Git.fetch(dep)
  defp fetch_one(%{kind: :hex} = dep), do: Muro.Deps.Hex.fetch(dep)

  defp commit(root, old, old_bytes, fetched) do
    keep = Enum.map(fetched, fn {dep, _result} -> dep.name end)
    lock = lock_map(fetched)
    encoded = Muro.Lock.encode(lock)

    drop_locked(root, old, keep)

    Enum.each(fetched, fn {dep, result} ->
      replace_tree(root, dep.name, result.files)
    end)

    lock_path = Path.join(root, "muro.lock")

    if old_bytes == encoded do
      :ok
    else
      File.write!(lock_path, encoded)
    end

    {:ok, report(old, fetched, old_bytes, encoded)}
  end

  defp clear(root, old) do
    drop_locked(root, old, [])
    lock_path = Path.join(root, "muro.lock")
    had_lock = File.regular?(lock_path)
    if had_lock, do: File.rm!(lock_path)

    removed = Enum.map(Enum.sort(Map.keys(old)), fn name -> "removed #{name}" end)
    lines = ["nothing to fetch" | removed]
    lines = if had_lock, do: lines ++ ["removed muro.lock"], else: lines
    {:ok, lines}
  end

  defp drop_locked(root, old, keep) do
    Enum.each(Map.keys(old), fn name ->
      unless name in keep do
        File.rm_rf(Path.join([root, "muro_deps", name]))
      end
    end)
  end

  defp replace_tree(root, name, files) do
    base = Path.join(root, "muro_deps")
    File.mkdir_p!(base)
    dest = Path.join(base, name)
    stage = Path.join(base, name <> ".fetching")
    File.rm_rf(stage)
    write_tree(stage, files)
    File.rm_rf(dest)
    File.rename!(stage, dest)
  end

  defp write_tree(dir, files) do
    Enum.each(files, fn {rel, bytes} ->
      path = Path.join([dir | String.split(rel, "/")])
      File.mkdir_p!(Path.dirname(path))
      File.write!(path, bytes)
    end)
  end

  defp lock_map(fetched) do
    Map.new(fetched, fn {dep, result} ->
      files = Map.new(result.files, fn {path, bytes} -> {path, Muro.Hash.sha256(bytes)} end)

      {dep.name,
       %{
         files: files,
         resolved: result.resolved,
         source: dep.source,
         version: result.version
       }}
    end)
  end

  defp report(old, fetched, old_bytes, encoded) do
    dropped =
      old
      |> Map.keys()
      |> Enum.reject(fn name -> Enum.any?(fetched, fn {dep, _} -> dep.name == name end) end)
      |> Enum.sort()
      |> Enum.map(fn name -> "removed #{name}" end)

    blocks = Enum.flat_map(fetched, fn {dep, result} -> block(dep, result, old) end)
    lock_line = if old_bytes == encoded, do: "muro.lock unchanged", else: "wrote muro.lock"
    dropped ++ blocks ++ [lock_line]
  end

  defp block(dep, result, old) do
    new_files = Map.new(result.files, fn {path, bytes} -> {path, Muro.Hash.sha256(bytes)} end)
    old_files = old_files(old, dep.name)
    n = map_size(new_files)
    noun = if n == 1, do: "file", else: "files"
    ["fetched #{dep.name} #{result.version} (#{n} #{noun})" | change_lines(old_files, new_files)]
  end

  defp old_files(old, name) do
    case Map.fetch(old, name) do
      {:ok, %{files: files}} -> files
      :error -> %{}
    end
  end

  defp change_lines(old, new) do
    (Map.keys(old) ++ Map.keys(new))
    |> Enum.uniq()
    |> Enum.sort()
    |> Enum.flat_map(fn path ->
      case {Map.get(old, path), Map.get(new, path)} do
        {nil, _now} -> ["  added #{path}"]
        {_was, nil} -> ["  removed #{path}"]
        {same, same} -> []
        {was, now} -> ["  changed #{path} (sha256 #{was} -> #{now})"]
      end
    end)
  end

  defp read_lock(root) do
    path = Path.join(root, "muro.lock")

    if File.regular?(path) do
      case File.read(path) do
        {:ok, content} ->
          case Muro.Lock.decode(content) do
            {:ok, lock} -> {:ok, lock, content}
            {:error, msg} -> {:error, msg}
          end

        {:error, reason} ->
          {:error, "muro.lock could not be read (#{inspect(reason)}); run mix muro.deps.get"}
      end
    else
      {:ok, %{}, nil}
    end
  end

  defp annotate(msg) do
    if String.contains?(msg, "unchanged") do
      msg
    else
      msg <> "\nmuro.lock and muro_deps/ are unchanged"
    end
  end
end

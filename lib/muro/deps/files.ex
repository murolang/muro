defmodule Muro.Deps.Files do
  @moduledoc false

  @doc """
  `.muro` files under `dir`, keyed by a `/` path relative to `dir`.

  Symlinks, other non-regular files, and paths with `..` or an
  absolute segment are errors. A `.git` directory is skipped. An
  empty result is not an error here; the caller refuses a package
  that ships no `.muro` file.
  """
  def collect(dir) do
    case File.lstat(dir) do
      {:ok, %{type: :directory}} -> walk(dir, "")
      {:ok, %{type: :symlink}} -> {:error, "package root is a symlink"}
      {:ok, _stat} -> {:error, "package root is not a directory"}
      {:error, _reason} -> {:error, "package root is missing"}
    end
  end

  defp walk(dir, prefix) do
    case File.ls(dir) do
      {:ok, names} ->
        Enum.reduce_while(Enum.sort(names), {:ok, %{}}, fn name, {:ok, acc} ->
          rel = if prefix == "", do: name, else: prefix <> "/" <> name

          if name == ".git" do
            {:cont, {:ok, acc}}
          else
            case one(Path.join(dir, name), rel, acc) do
              {:ok, acc} -> {:cont, {:ok, acc}}
              {:error, _} = err -> {:halt, err}
            end
          end
        end)

      {:error, reason} ->
        {:error, "could not read #{label(prefix)} (#{inspect(reason)})"}
    end
  end

  defp one(path, rel, acc) do
    case File.lstat(path) do
      {:ok, %{type: :symlink}} ->
        {:error, "symlink #{rel}"}

      {:ok, %{type: :directory}} ->
        case walk(path, rel) do
          {:ok, nested} -> {:ok, Map.merge(acc, nested)}
          {:error, _} = err -> err
        end

      {:ok, %{type: :regular}} ->
        cond do
          unsafe?(rel) ->
            {:error, "unsafe path #{rel}"}

          String.ends_with?(rel, ".muro") ->
            case File.read(path) do
              {:ok, bytes} -> {:ok, Map.put(acc, rel, bytes)}
              {:error, reason} -> {:error, "could not read #{rel} (#{inspect(reason)})"}
            end

          true ->
            {:ok, acc}
        end

      {:ok, %{type: type}} ->
        {:error, "non-regular file #{rel} (#{type})"}

      {:error, reason} ->
        {:error, "could not stat #{rel} (#{inspect(reason)})"}
    end
  end

  defp unsafe?(rel) do
    String.starts_with?(rel, "/") or String.contains?(rel, "\\") or
      Enum.any?(String.split(rel, "/"), fn seg -> seg in ["", ".", ".."] end)
  end

  defp label(""), do: "the package root"
  defp label(prefix), do: prefix
end

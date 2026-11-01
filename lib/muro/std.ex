defmodule Muro.Std do
  @moduledoc """
  The ordinary library embedded in the compiler.

  `import "std:list.muro"` loads that book from here, the way
  `Muro.Prelude` loads `prelude.muro`. The bytes are the same in the
  Hex package, a Burrito binary, and a checkout of the repo. A change
  to a book under `lib/muro/std/` recompiles this module.

  A name is one of `names/0`. `..`, a leading `/`, a backslash, a
  newline, or a NUL byte leaves the library and is refused. `.`
  segments collapse. A relative import whose importer is a `std:` book
  is resolved with `relative/2`, so it stays inside the library.
  """

  @books ~w(bool.muro le.muro list.muro maybe.muro ord.muro)

  for name <- @books do
    @external_resource Path.join([__DIR__, "std", name])
  end

  @sources Map.new(@books, fn name ->
             {name, File.read!(Path.join([__DIR__, "std", name]))}
           end)

  @doc "Book names, sorted."
  def names, do: @books

  @doc "The virtual file id of a library book."
  def id(name) when is_binary(name), do: "std:" <> name

  @doc "True when `path` is a library id, not a filesystem path."
  def std_id?("std:" <> _), do: true
  def std_id?(_path), do: false

  @doc "The embedded source of `name`, or `:error` when it is not a book."
  def source(name) when is_binary(name) do
    case Map.fetch(@sources, name) do
      {:ok, bytes} -> {:ok, bytes}
      :error -> :error
    end
  end

  @doc """
  Classify the text after `std:`.

  `{:ok, name}` is a library-shaped name, whether or not that book
  exists. `:escape` means the path leaves the library.
  """
  def classify(rest) when is_binary(rest) do
    if escape?(rest) do
      :escape
    else
      {:ok, collapse(rest)}
    end
  end

  @doc """
  Resolve `rel` from a library book id.

  `{:ok, name}` stays in the library. `:escape` leaves it.
  """
  def relative("std:" <> from, rel) when is_binary(rel) do
    dir = Path.dirname(from)
    joined = if dir == ".", do: rel, else: dir <> "/" <> rel
    classify(joined)
  end

  defp escape?(rest) do
    String.starts_with?(rest, "/") or String.contains?(rest, "\\") or
      String.contains?(rest, "\n") or String.contains?(rest, <<0>>) or
      Enum.any?(segments(rest), &(&1 == ".."))
  end

  defp collapse(rest) do
    rest
    |> segments()
    |> Enum.reject(&(&1 in [".", ""]))
    |> Enum.join("/")
  end

  defp segments(rest), do: String.split(rest, "/")
end

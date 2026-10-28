defmodule Muro.Hash do
  @moduledoc """
  One sha256 for file bytes, the book hash, and the conforms-to line.

  `sha256/1` is the lowercase hex digest of the bytes. `files/1` is the
  digest of a list of `{relative_path, bytes}` pairs: the pairs are
  sorted by path, and each contributes the path, a zero byte, the
  bytes, and a zero byte. `Muro.Gen` uses that layout for the book
  hash. The lock stores `sha256/1` of each package file. The conforms-to
  line uses `files/1` over the package files a book actually loaded,
  with the path `<name>/<file>`.
  """

  @doc "Lowercase hex sha256 of `iodata`."
  def sha256(iodata) do
    :crypto.hash(:sha256, IO.iodata_to_binary(iodata))
    |> Base.encode16(case: :lower)
  end

  @doc """
  Lowercase hex sha256 of `{relative_path, bytes}` pairs.

  Paths are compared as binaries. Each pair contributes the path, a
  zero byte, the file bytes, and a zero byte.
  """
  def files(entries) when is_list(entries) do
    entries
    |> Enum.sort()
    |> Enum.map(fn {rel, bytes} -> [rel, 0, bytes, 0] end)
    |> sha256()
  end
end

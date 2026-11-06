defmodule MuroVisor.Book do
  @moduledoc false

  @key {__MODULE__, :open}

  @doc """
  Load one book with `Muro.Load.file/1` and remember it.

  The stamp is fixed here. A later backend switch reads this book and
  does not load it again.
  """
  def open(path) when is_binary(path) do
    path = Path.expand(path)

    cond do
      not File.regular?(path) ->
        remember_error("no such book: #{path}")

      true ->
        case Muro.Load.file(path) do
          {:ok, book} -> remember(book, path)
          {:error, msg} -> remember_error(msg)
        end
    end
  end

  @doc false
  def remember(book, path) when is_list(book) and is_binary(path) do
    stamp = System.unique_integer([:positive])
    :persistent_term.put(@key, %{book: book, path: path, stamp: stamp})
    {:ok, stamp}
  end

  @doc "The book `open/1` stored, or an error when none is open."
  def current do
    case :persistent_term.get(@key, nil) do
      nil -> {:error, "no book is open"}
      {:error, msg} when is_binary(msg) -> {:error, msg}
      open -> {:ok, open}
    end
  end

  defp remember_error(msg) do
    :persistent_term.put(@key, {:error, msg})
    {:error, msg}
  end
end

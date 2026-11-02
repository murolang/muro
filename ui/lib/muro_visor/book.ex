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
        {:error, "no such book: #{path}"}

      true ->
        case Muro.Load.file(path) do
          {:ok, book} ->
            stamp = System.unique_integer([:positive])
            :persistent_term.put(@key, %{book: book, path: path, stamp: stamp})
            {:ok, stamp}

          {:error, msg} ->
            {:error, msg}
        end
    end
  end

  @doc "The book `open/1` stored, or an error when none is open."
  def current do
    case :persistent_term.get(@key, nil) do
      nil -> {:error, "no book is open"}
      open -> {:ok, open}
    end
  end
end

defmodule Mix.Tasks.Muro.Ui do
  use Mix.Task

  @shortdoc "Open a book in the muro visor"

  @moduledoc """
  Start the explorer and open one book.

      mix muro.ui path.muro

  The book is loaded before the server listens. The page is read-only.
  """

  @impl Mix.Task
  def run([path]) do
    case MuroVisor.open(path) do
      {:ok, url} ->
        listen!()
        Mix.Task.run("app.start")
        Mix.shell().info(url)
        MuroVisor.Browser.open(url)
        Process.sleep(:infinity)

      {:error, msg} ->
        Mix.raise(msg)
    end
  end

  def run(_args) do
    Mix.raise("usage: mix muro.ui path.muro")
  end

  defp listen! do
    config = Application.fetch_env!(:muro_visor, MuroVisor.Endpoint)
    Application.put_env(:muro_visor, MuroVisor.Endpoint, Keyword.put(config, :server, true))
  end
end

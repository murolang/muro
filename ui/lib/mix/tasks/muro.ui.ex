defmodule Mix.Tasks.Muro.Ui do
  use Mix.Task

  @shortdoc "Open a book in the muro visor"

  @moduledoc """
  Start the explorer and open one book.

      mix muro.ui path.muro

  The book is loaded before the server listens. The page is read-only.
  """

  @impl Mix.Task
  def run(args) do
    case boot(args) do
      {:ok, url} ->
        Mix.shell().info(url)
        MuroVisor.Browser.open(url)
        hold()

      {:error, msg} ->
        Mix.raise(msg)
    end
  end

  @doc false
  def boot([path]) when is_binary(path) do
    with {:ok, url} <- MuroVisor.open(path) do
      start!()
      {:ok, url}
    end
  end

  def boot(_args), do: {:error, "usage: mix muro.ui path.muro"}

  defp start! do
    config = Application.fetch_env!(:muro_visor, MuroVisor.Endpoint)
    Application.put_env(:muro_visor, MuroVisor.Endpoint, Keyword.put(config, :server, true))

    if Process.whereis(MuroVisor.Endpoint) do
      :ok = Supervisor.terminate_child(MuroVisor.Supervisor, MuroVisor.Endpoint)

      case Supervisor.restart_child(MuroVisor.Supervisor, MuroVisor.Endpoint) do
        {:ok, _pid} -> :ok
        {:error, reason} -> Mix.raise("explorer did not listen: #{inspect(reason)}")
      end
    else
      Mix.Task.run("app.start")
    end
  end

  # The command blocks so the endpoint stays up. Tests set `:ui_hold`
  # to false and stop the endpoint themselves.
  defp hold do
    if Application.get_env(:muro_visor, :ui_hold, true) do
      Process.sleep(:infinity)
    else
      :ok
    end
  end
end

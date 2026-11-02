defmodule MuroVisor do
  @moduledoc """
  Open one checked book in the explorer.

  `open/1` loads the book and returns the local URL. It does not listen.
  `Mix.Tasks.Muro.Ui` is what starts the server.
  """

  @doc """
  Load `path` and return the URL the explorer will serve.

  `{:error, message}` when the file is missing or the book does not load.
  """
  def open(path) when is_binary(path) do
    case MuroVisor.Book.open(path) do
      {:ok, _stamp} -> {:ok, url()}
      {:error, _} = err -> err
    end
  end

  @doc "The URL of the endpoint's http port."
  def url do
    port =
      :muro_visor
      |> Application.fetch_env!(MuroVisor.Endpoint)
      |> Keyword.fetch!(:http)
      |> Keyword.fetch!(:port)

    "http://127.0.0.1:#{port}/"
  end
end

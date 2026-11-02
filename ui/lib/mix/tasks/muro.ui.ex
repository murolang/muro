defmodule Mix.Tasks.Muro.Ui do
  use Mix.Task

  @shortdoc "Open a book in the muro visor"

  @moduledoc """
  Start the explorer and open one book.

      mix muro.ui path.muro

  The book is loaded before the server listens. The page is read-only.
  In a Mix project, add `{:muro_visor, "~> 0.1.0"}` and run `mix deps.get`
  first. Outside a project, the task installs that package and starts it.
  """

  @defaults [
    url: [host: "127.0.0.1"],
    adapter: Bandit.PhoenixAdapter,
    http: [ip: {127, 0, 0, 1}, port: 4017],
    secret_key_base: String.duplicate("v", 64),
    render_errors: [formats: [html: MuroVisor.ErrorHTML], layout: false],
    pubsub_server: MuroVisor.PubSub,
    live_view: [signing_salt: "visorsalt"],
    check_origin: ["//127.0.0.1", "//localhost"],
    server: false
  ]

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
    with :ok <- ensure_runtime!(),
         :ok <- ensure_config!(),
         {:ok, url} <- MuroVisor.open(path) do
      start!()
      {:ok, url}
    end
  end

  def boot(_args), do: {:error, "usage: mix muro.ui path.muro"}

  @doc false
  def ensure_config! do
    current = Application.get_env(:muro_visor, MuroVisor.Endpoint, [])
    Application.put_env(:muro_visor, MuroVisor.Endpoint, Keyword.merge(@defaults, current))
    :ok
  end

  defp ensure_runtime! do
    cond do
      runtime_ready?() ->
        :ok

      Mix.Project.get() == nil ->
        Mix.install([{:muro_visor, "~> 0.1.0"}])
        :ok

      true ->
        Mix.raise("""
        muro_visor is not running in this project. Add it to mix.exs:

            {:muro_visor, "~> 0.1.0"}

        Then fetch it and open the book:

            mix deps.get
            mix muro.ui path.muro
        """)
    end
  end

  defp runtime_ready? do
    Code.ensure_loaded?(MuroVisor) and Code.ensure_loaded?(Phoenix) and Code.ensure_loaded?(Muro)
  end

  defp start! do
    config = Application.fetch_env!(:muro_visor, MuroVisor.Endpoint)
    Application.put_env(:muro_visor, MuroVisor.Endpoint, Keyword.put(config, :server, true))

    case Application.ensure_all_started(:muro_visor) do
      {:ok, _} ->
        :ok

      {:error, reason} ->
        Mix.raise("explorer did not start: #{inspect(reason)}")
    end

    cond do
      not is_pid(Process.whereis(MuroVisor.Endpoint)) ->
        Mix.raise("explorer did not listen: endpoint missing")

      true ->
        :ok = Supervisor.terminate_child(MuroVisor.Supervisor, MuroVisor.Endpoint)

        case Supervisor.restart_child(MuroVisor.Supervisor, MuroVisor.Endpoint) do
          {:ok, _pid} -> :ok
          {:error, reason} -> Mix.raise("explorer did not listen: #{inspect(reason)}")
        end
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

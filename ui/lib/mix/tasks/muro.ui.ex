defmodule Mix.Tasks.Muro.Ui do
  use Mix.Task

  @shortdoc "Open a book in the muro visor"

  @moduledoc """
  Start the explorer and open one book.

      mix muro.ui path.muro

  The book is loaded before the server listens. The page is read-only.
  It opens on the meetings. `?view=all` draws every definition.
  `?view=all&grades=on` fades erased grades. `?view=synth` draws an
  environment's states. `?trace=` reads a `mix muro.synth --json` report.
  The task prints the URL of the address it binds and opens it.
  IPv4 loopback is `http://127.0.0.1:4017/`. An IPv6 address is
  `http://[::1]:4017/`. A hostname is `http://localhost:4017/`.
  In a Mix project, add `{:muro_visor, "~> 0.3.0"}` and run `mix deps.get`
  first. Outside a project, the task installs that package and starts it.
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
    with :ok <- ensure_runtime!(),
         :ok <- ensure_config!(),
         {:ok, url} <- MuroVisor.open(path) do
      start!()
      {:ok, url}
    end
  end

  def boot(_args), do: {:error, "usage: mix muro.ui path.muro"}

  @doc false
  def ensure_config!, do: MuroVisor.install_endpoint!()

  defp ensure_runtime! do
    cond do
      runtime_ready?() ->
        :ok

      Mix.Project.get() == nil ->
        Mix.install([{:muro_visor, "~> 0.3.0"}])
        :ok

      true ->
        Mix.raise("""
        muro_visor is not running in this project. Add it to mix.exs:

            {:muro_visor, "~> 0.3.0"}

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
    previous = Application.fetch_env!(:muro_visor, MuroVisor.Endpoint)
    Application.put_env(:muro_visor, MuroVisor.Endpoint, Keyword.put(previous, :server, true))

    case Application.ensure_all_started(:muro_visor) do
      {:ok, _} ->
        :ok

      {:error, reason} ->
        Application.put_env(:muro_visor, MuroVisor.Endpoint, previous)
        Mix.raise("explorer did not start: #{inspect(reason)}")
    end

    if not is_pid(Process.whereis(MuroVisor.Endpoint)) do
      Mix.raise("explorer did not listen: endpoint missing")
    end

    restart_listener!(previous)
  end

  # Drop the running child and start it with the config `start!/0` just
  # wrote. A failed bind puts the previous child back. Tests share this
  # endpoint, and a terminated child fails later LiveView tests.
  defp restart_listener!(previous) do
    :ok = Supervisor.terminate_child(MuroVisor.Supervisor, MuroVisor.Endpoint)

    case Supervisor.restart_child(MuroVisor.Supervisor, MuroVisor.Endpoint) do
      {:ok, _pid} ->
        :ok

      {:error, reason} ->
        Application.put_env(:muro_visor, MuroVisor.Endpoint, previous)
        restore_listener!(reason)
    end
  end

  defp restore_listener!(reason) do
    case Supervisor.restart_child(MuroVisor.Supervisor, MuroVisor.Endpoint) do
      {:ok, _pid} ->
        Mix.raise("explorer did not listen: #{inspect(reason)}")

      {:error, restore} ->
        Mix.raise(
          "explorer did not listen: #{inspect(reason)}; endpoint was not restored: #{inspect(restore)}"
        )
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

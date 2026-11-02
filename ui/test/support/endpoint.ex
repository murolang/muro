defmodule MuroVisor.TestEndpoint do
  @moduledoc false

  @doc """
  Leave the shared endpoint running and not listening.

  A failed bind terminates the child. Later LiveView tests call this
  process, so it has to be running again, with `server: false`.
  """
  def quiet! do
    config =
      case Application.fetch_env(:muro_visor, MuroVisor.Endpoint) do
        {:ok, config} -> config
        :error -> MuroVisor.merge_endpoint([])
      end

    Application.put_env(:muro_visor, MuroVisor.Endpoint, Keyword.put(config, :server, false))
    ensure!()
  end

  @doc """
  Start the shared endpoint from the current application env.

  Restarts the child when the supervisor is up. Starts the application
  when the supervisor itself is gone.
  """
  def ensure! do
    case Process.whereis(MuroVisor.Supervisor) do
      sup when is_pid(sup) ->
        _ = Supervisor.terminate_child(sup, MuroVisor.Endpoint)
        start_existing!(sup)

      _ ->
        revive!()
    end
  end

  defp start_existing!(sup) do
    case Supervisor.restart_child(sup, MuroVisor.Endpoint) do
      {:ok, _} ->
        :ok

      {:error, :running} ->
        :ok

      {:error, {:already_started, _pid}} ->
        :ok

      {:error, _} ->
        revive!()
    end
  end

  defp revive! do
    _ = Application.stop(:muro_visor)
    {:ok, _} = Application.ensure_all_started(:muro_visor)
    :ok
  end
end

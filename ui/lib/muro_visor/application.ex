defmodule MuroVisor.Application do
  @moduledoc false

  use Application

  @impl true
  def start(_type, _args) do
    # Config files and an installed package merge :http shallowly. Restore
    # the loopback address before the endpoint binds.
    MuroVisor.install_endpoint!()

    children = [
      {Phoenix.PubSub, name: MuroVisor.PubSub},
      MuroVisor.Endpoint
    ]

    Supervisor.start_link(children, strategy: :one_for_one, name: MuroVisor.Supervisor)
  end

  @impl true
  def config_change(changed, _new, removed) do
    MuroVisor.Endpoint.config_change(changed, removed)
    :ok
  end
end

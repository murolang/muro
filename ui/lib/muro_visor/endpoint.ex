defmodule MuroVisor.Endpoint do
  @moduledoc false

  use Phoenix.Endpoint, otp_app: :muro_visor

  @session_options [
    store: :cookie,
    key: "_muro_visor_key",
    signing_salt: "visorsign",
    same_site: "Lax"
  ]

  socket "/live", Phoenix.LiveView.Socket, websocket: [connect_info: [session: @session_options]]

  plug Plug.Static,
    at: "/assets",
    from: {:phoenix, "priv/static"},
    gzip: false,
    only: ~w(phoenix.min.js phoenix.js)

  plug Plug.Static,
    at: "/assets",
    from: {:phoenix_live_view, "priv/static"},
    gzip: false,
    only: ~w(phoenix_live_view.min.js)

  plug Plug.RequestId
  plug Plug.Telemetry, event_prefix: [:phoenix, :endpoint]

  plug Plug.Parsers,
    parsers: [:urlencoded, :multipart, :json],
    pass: ["*/*"],
    json_decoder: Phoenix.json_library()

  plug Plug.MethodOverride
  plug Plug.Head
  plug Plug.Session, @session_options
  plug MuroVisor.Router
end

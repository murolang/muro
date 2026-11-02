import Config

config :phoenix, :json_library, Jason

config :muro_visor, MuroVisor.Endpoint,
  url: [host: "127.0.0.1"],
  adapter: Bandit.PhoenixAdapter,
  http: [ip: {127, 0, 0, 1}, port: 4017],
  secret_key_base: String.duplicate("v", 64),
  render_errors: [formats: [html: MuroVisor.ErrorHTML], layout: false],
  pubsub_server: MuroVisor.PubSub,
  live_view: [signing_salt: "visorsalt"],
  check_origin: ["//127.0.0.1", "//localhost"],
  server: false

import_config "#{config_env()}.exs"

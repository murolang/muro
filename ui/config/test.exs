import Config

# Port 0 is ephemeral. A test that listens reads the bound port back.
# 4017 stays the user-facing default, and it is often already taken.
config :muro_visor, MuroVisor.Endpoint,
  http: [ip: {127, 0, 0, 1}, port: 0],
  secret_key_base: String.duplicate("t", 64),
  server: false

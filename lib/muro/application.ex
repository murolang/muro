defmodule Muro.Application do
  @moduledoc false

  use Application

  @impl true
  def start(_type, _args) do
    register_makeup_lexer()
    Supervisor.start_link([], strategy: :one_for_one, name: Muro.Supervisor)
  end

  @doc false
  def register_makeup_lexer(loaded? \\ Code.ensure_loaded?(Makeup.Registry)) do
    if loaded? do
      Makeup.Registry.register_lexer(Muro.MakeupLexer,
        names: ["muro"],
        extensions: ["muro"]
      )

      :registered
    else
      :skipped
    end
  end
end

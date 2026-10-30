defmodule Muro.Application do
  @moduledoc false

  use Application

  @impl true
  def start(_type, _args) do
    if System.get_env("__BURRITO") == "1" do
      # Mix is in the release as `:load`, so its servers are not up.
      # `Mix.Project.get/0` calls `Mix.ProjectStack`. Starting these
      # servers does not load `mix.exs`, does not compile a host, and
      # does not append `~/.mix` archives. `Mix.Project.get/0` stays nil.
      ensure_mix_servers()
      args = Enum.map(:init.get_plain_arguments(), &to_string/1)
      System.halt(Muro.CLI.main(args))
    else
      register_makeup_lexer()
      Supervisor.start_link([], strategy: :one_for_one, name: Muro.Supervisor)
    end
  end

  @doc false
  def ensure_mix_servers do
    for mod <- [Mix.Sync.PubSub, Mix.State, Mix.TasksServer, Mix.ProjectStack] do
      case Process.whereis(mod) do
        nil -> {:ok, _pid} = mod.start_link([])
        _pid -> :ok
      end
    end

    :ok
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

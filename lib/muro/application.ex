defmodule Muro.Application do
  @moduledoc false

  use Application

  @impl true
  def start(_type, _args) do
    if release_cli?() do
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

  # `__BURRITO` is set for every Burrito executable. A host that
  # depends on muro would run this CLI and halt, or fail to start
  # Mix if that release omits Mix. The marker is written only into
  # the sys.config of the muro release.
  @doc false
  def release_cli? do
    Application.get_env(:muro, :release_cli) == true
  end

  @doc false
  def write_release_marker(path) when is_binary(path) do
    case :file.consult(String.to_charlist(path)) do
      {:ok, [config]} when is_list(config) ->
        header =
          path
          |> File.stream!()
          |> Enum.take_while(&String.starts_with?(&1, "%"))
          |> Enum.join()

        marked =
          Keyword.update(config, :muro, [release_cli: true], fn muro ->
            Keyword.put(muro, :release_cli, true)
          end)

        body = IO.iodata_to_binary(:io_lib.format("~tw.~n", [marked]))
        File.write!(path, [header, body])
        :ok

      other ->
        Mix.raise("muro release sys.config could not be read: #{inspect(other)}")
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

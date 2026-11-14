defmodule MuroVisor.MixProject do
  use Mix.Project

  def project do
    discard_stale_checkout()

    [
      app: :muro_visor,
      version: "0.3.0",
      elixir: "~> 1.15",
      elixirc_paths: elixirc_paths(Mix.env()),
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      description: "A read-only visual explorer for a muro book",
      source_url: "https://github.com/murolang/muro",
      homepage_url: "https://muro-lang.dev/docs/explorer",
      package: package()
    ]
  end

  def application do
    [
      extra_applications: [:logger],
      mod: {MuroVisor.Application, []}
    ]
  end

  defp elixirc_paths(:test), do: ["lib", "test/support"]
  defp elixirc_paths(_), do: ["lib"]

  defp deps do
    [
      muro_dependency(
        System.argv(),
        File.regular?(Path.expand("../lib/muro.ex", __DIR__)),
        System.get_env("MURO_PATH")
      ),
      {:phoenix, "~> 1.7.14"},
      {:phoenix_live_view, "~> 1.0.0"},
      {:phoenix_html, "~> 4.1"},
      {:makeup, "~> 1.2"},
      {:makeup_elixir, "~> 1.0"},
      {:makeup_rust, "~> 0.3"},
      {:bandit, "~> 1.5"},
      {:jason, "~> 1.4"},
      {:floki, ">= 0.30.0", only: :test},
      {:mint, "~> 1.6", only: :test},
      {:mint_web_socket, "~> 1.0", only: :test}
    ]
  end

  # A path build whose muro.app version is not this checkout's mix.exs
  # version makes Mix stop before it recompiles. Drop that build so the
  # next command compiles the sources that are on disk.
  @doc false
  def discard_stale_muro_build(build_root, version)
      when is_binary(build_root) and is_binary(version) do
    build_root
    |> Path.join("*/lib/muro")
    |> Path.wildcard()
    |> Enum.each(fn dir ->
      app = Path.join(dir, "ebin/muro.app")

      case app_vsn(app) do
        vsn when is_binary(vsn) and vsn != version -> File.rm_rf!(dir)
        _ -> :ok
      end
    end)

    :ok
  end

  defp discard_stale_checkout do
    checkout = File.regular?(Path.expand("../lib/muro.ex", __DIR__))

    if checkout and not publishing?(System.argv()) do
      case parent_version() do
        version when is_binary(version) ->
          root = System.get_env("MIX_BUILD_PATH") || Path.expand("_build", __DIR__)
          discard_stale_muro_build(root, version)

        _ ->
          :ok
      end
    else
      :ok
    end
  end

  defp parent_version do
    case File.read(Path.expand("../mix.exs", __DIR__)) do
      {:ok, src} ->
        case Regex.run(~r/version:\s*"([^"]+)"/, src) do
          [_, version] -> version
          _ -> nil
        end

      _ ->
        nil
    end
  end

  defp app_vsn(path) do
    case File.read(path) do
      {:ok, src} ->
        case Regex.run(~r/\{vsn,\s*"([^"]+)"\}/, src) do
          [_, vsn] -> vsn
          _ -> nil
        end

      _ ->
        nil
    end
  end

  @doc false
  def muro_dependency(argv, checkout_exists, muro_path) do
    cond do
      publishing?(argv) ->
        {:muro, "~> 0.21.0"}

      is_binary(muro_path) and muro_path != "" ->
        {:muro, "~> 0.21.0", path: muro_path, override: true}

      checkout_exists ->
        {:muro, "~> 0.21.0", path: Path.expand("..", __DIR__), override: true}

      true ->
        {:muro, "~> 0.21.0"}
    end
  end

  defp publishing?(argv) do
    Enum.any?(argv, &(&1 in ["hex.publish", "hex.build"]))
  end

  defp package do
    [
      licenses: ["MIT"],
      links: %{
        "GitHub" => "https://github.com/murolang/muro",
        "Explorer" => "https://muro-lang.dev/docs/explorer"
      },
      files: ~w(lib config .formatter.exs mix.exs README.md CHANGELOG.md LICENSE)
    ]
  end
end

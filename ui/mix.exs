defmodule MuroVisor.MixProject do
  use Mix.Project

  def project do
    [
      app: :muro_visor,
      version: "0.1.0",
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
      {:bandit, "~> 1.5"},
      {:jason, "~> 1.4"},
      {:floki, ">= 0.30.0", only: :test},
      {:mint, "~> 1.6", only: :test},
      {:mint_web_socket, "~> 1.0", only: :test}
    ]
  end

  @doc false
  def muro_dependency(argv, checkout_exists, muro_path) do
    cond do
      publishing?(argv) ->
        {:muro, "~> 0.20.5"}

      is_binary(muro_path) and muro_path != "" ->
        {:muro, "~> 0.20.5", path: muro_path, override: true}

      checkout_exists ->
        {:muro, "~> 0.20.5", path: Path.expand("..", __DIR__), override: true}

      true ->
        {:muro, "~> 0.20.5"}
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

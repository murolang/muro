defmodule Muro.MixProject do
  use Mix.Project

  def project do
    [
      app: :muro,
      version: "0.16.13",
      elixir: "~> 1.15",
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      elixirc_paths: elixirc_paths(Mix.env()),
      description: "An explicit affine dependent type theory",
      source_url: "https://github.com/murolang/muro",
      homepage_url: "https://muro-lang.dev",
      package: package()
    ]
  end

  def application do
    [
      extra_applications: [:logger],
      mod: {Muro.Application, []}
    ]
  end

  defp elixirc_paths(_), do: ["lib"]

  defp deps do
    [
      {:nx, "~> 0.9"},
      {:makeup, "~> 1.2"}
    ]
  end

  defp package do
    [
      licenses: ["MIT"],
      links: %{
        "GitHub" => "https://github.com/murolang/muro",
        "Site" => "https://muro-lang.dev"
      },
      files: ~w(lib stdlib .formatter.exs mix.exs README.md LICENSE CHANGELOG.md)
    ]
  end
end

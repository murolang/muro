defmodule Muro.MixProject do
  use Mix.Project

  def project do
    [
      app: :muro,
      version: "0.19.6",
      elixir: "~> 1.15",
      start_permanent: Mix.env() in [:prod, :burrito],
      deps: deps(),
      releases: releases(),
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
      {:nx, "~> 0.9", optional: true},
      {:makeup, "~> 1.2", optional: true},
      {:elixir_make, "~> 0.10", optional: true, runtime: false},
      {:burrito, "1.5.0", only: :burrito, runtime: false}
    ]
  end

  # Burrito is loaded only while building the self-contained executable.
  # `only: :burrito` keeps it out of the Hex package. The wrap step runs
  # at release time, so this module can load when Burrito is absent.
  defp releases do
    if Mix.env() == :burrito do
      [
        muro: [
          include_executables_for: [:unix],
          # Mix is loaded, not started. Starting it would append ~/.mix
          # archives. Muro.Application starts Mix's servers in the
          # executable so Mix.Project.get/0 can run. No host project is
          # loaded, so that call stays nil.
          applications: [mix: :load],
          steps: [:assemble, &burrito_wrap/1],
          burrito: [
            targets: [
              macos_aarch64: [os: :darwin, cpu: :aarch64],
              macos_x86_64: [os: :darwin, cpu: :x86_64],
              linux_x86_64: [os: :linux, cpu: :x86_64],
              linux_aarch64: [os: :linux, cpu: :aarch64]
            ]
          ]
        ]
      ]
    else
      []
    end
  end

  defp burrito_wrap(release) do
    Burrito.wrap(release)
  end

  defp package do
    [
      licenses: ["MIT"],
      links: %{
        "GitHub" => "https://github.com/murolang/muro",
        "Site" => "https://muro-lang.dev"
      },
      files: ~w(lib .formatter.exs mix.exs README.md LICENSE CHANGELOG.md)
    ]
  end
end

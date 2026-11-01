defmodule Muro.MixProject do
  use Mix.Project

  def project do
    [
      app: :muro,
      version: "0.20.4",
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
          #
          # The fetcher starts :public_key, :ssl, and :inets. They are
          # loaded here, with :crypto and :asn1, so `muro deps.get` can
          # start them on a machine with no Erlang. They are not started
          # with the release, they are not extra applications of :muro,
          # and they are not dependencies of the Hex package.
          applications: [
            mix: :load,
            asn1: :load,
            crypto: :load,
            public_key: :load,
            ssl: :load,
            inets: :load
          ],
          # The CLI starts only when this release's sys.config sets
          # `:release_cli`. `__BURRITO` is every Burrito executable.
          steps: [:assemble, &mark_muro_release/1, &burrito_wrap/1],
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

  defp mark_muro_release(release) do
    release.version_path
    |> Path.join("sys.config")
    |> Muro.Application.write_release_marker()

    release
  end

  defp burrito_wrap(release) do
    force_prod_wrap()
    Burrito.wrap(release)
  end

  # Burrito compiles is_prod/1 against Mix.env(), which is :burrito
  # while this release is built, so the wrapper stays a debug build and
  # prints "Unpacked File" on every run. Recompile that step in memory.
  # A target marked debug stays debug. deps/burrito is not modified.
  defp force_prod_wrap do
    path = Path.join(__DIR__, "deps/burrito/lib/steps/build/pack_and_build.ex")
    source = File.read!(path)

    needle =
      """
        defp is_prod(%Target{debug?: debug?}) do
          cond do
            debug? -> "0"
            Mix.env() == :prod -> "1"
            true -> "0"
          end
        end
      """
      |> String.trim_trailing("\n")

    replacement =
      """
        defp is_prod(%Target{debug?: debug?}) do
          if debug?, do: "0", else: "1"
        end
      """
      |> String.trim_trailing("\n")

    unless String.contains?(source, needle) do
      Mix.raise("Burrito's is_prod/1 changed; the prod wrap could not be applied")
    end

    Code.ensure_loaded!(Burrito.Builder.Step)
    Code.ensure_loaded!(Burrito.Builder.Target)
    Code.ensure_loaded!(Burrito.Builder.Context)
    Code.ensure_loaded!(Burrito.Builder.Log)

    previous = Code.get_compiler_option(:ignore_module_conflict)
    Code.put_compiler_option(:ignore_module_conflict, true)

    try do
      Code.compile_string(String.replace(source, needle, replacement), path)
    after
      Code.put_compiler_option(:ignore_module_conflict, previous)
    end

    :ok
  end

  defp package do
    [
      licenses: ["MIT"],
      links: %{
        "GitHub" => "https://github.com/murolang/muro",
        "Site" => "https://muro-lang.dev"
      },
      files: ~w(lib .formatter.exs mix.exs README.md LICENSE CHANGELOG.md manual/for-agents.md)
    ]
  end
end

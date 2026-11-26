defmodule Muro.GenExecutableFormatTest do
  # The executable runs `muro gen` with no Mix project loaded. These
  # tests run the CLI in a fresh `elixir` with the test build's beams
  # and no `mix.exs`, which is that state, and compare it with
  # `mix muro.gen` in the same directory (#297).
  use ExUnit.Case, async: false

  @round """
  def round : run Π (n : Nat) → Nat :=
    λ (n : Nat) → n

  def round-ok : evidence {round (suc 0) ≡ suc 0 : Nat} :=
    refl
  """

  @target "test/rounding_test.exs"

  test "the executable resolves import_deps from deps/ and writes the mix muro.gen bytes" do
    dir = project(~s|[import_deps: [:ecto], inputs: ["{lib,test}/**/*.{ex,exs}"]]\n|)
    dep(dir, "deps/ecto", "[export: [locals_without_parens: [field: 2, schema: 2]]]\n")

    assert {out, 0} = executable(dir, ["gen"])
    assert out =~ "written #{@target}\n"
    written = File.read!(Path.join(dir, @target))
    assert written =~ "defmodule Repro.RoundingTest do\n"

    assert {out, 0} = executable(dir, ["gen", "--check"])
    refute out =~ "differs"

    # The same directory as a Mix project with that dependency: mix
    # muro.gen writes the same bytes, so --check agrees across routes.
    File.rm!(Path.join(dir, @target))
    host_mix(dir)

    assert {out, 0} = mix_route(dir)
    assert out =~ "written #{@target}\n"

    assert File.read!(Path.join(dir, @target)) == written
  end

  test "the executable names the cause when an import_deps dependency is not in deps/" do
    dir = project(~s|[import_deps: [:ecto], inputs: ["{lib,test}/**/*.{ex,exs}"]]\n|)

    assert {out, 1} = executable(dir, ["gen"])
    assert out =~ "#{@target}: .formatter.exs could not be loaded without mix.exs\n"
    assert out =~ "Unknown dependency :ecto given to :import_deps"
    assert out =~ "It reads import_deps from deps/<dep>/.formatter.exs"
    assert out =~ "or use the Mix archive: mix muro.gen loads the project.\n"
    refute File.exists?(Path.join(dir, @target))
  end

  test "the executable keeps the archive's task name and renames the others" do
    assert Muro.CLI.executable_names("run mix muro.gen --check") == "run muro gen --check"

    assert Muro.CLI.executable_names("the Mix archive: mix muro.gen") ==
             "the Mix archive: mix muro.gen"
  end

  test "the executable honours MIX_DEPS_PATH" do
    dir = project(~s|[import_deps: [:ecto]]\n|)
    dep(dir, "vendored/ecto", "[export: [locals_without_parens: [field: 2]]]\n")

    assert {_out, 1} = executable(dir, ["gen"])
    assert {out, 0} = executable(dir, ["gen"], [{"MIX_DEPS_PATH", "vendored"}])
    assert out =~ "written #{@target}\n"
  end

  test "the executable loads a formatter plugin from _build/<env>/lib" do
    plugin = :"Elixir.Muro297Plugin#{System.unique_integer([:positive])}"
    dir = project("[plugins: [#{inspect(plugin)}]]\n")

    {:module, _, beam, _} =
      Module.create(
        plugin,
        quote do
          @behaviour Mix.Tasks.Format
          def features(_opts), do: [extensions: [".exs"]]

          def format(source, opts) do
            formatted =
              source
              |> Code.format_string!(Keyword.drop(opts, [:extension, :file]))
              |> IO.iodata_to_binary()
              |> String.replace(~r/\n*# plugged\z/, "")

            formatted <> "\n# plugged\n"
          end
        end,
        Macro.Env.location(__ENV__)
      )

    n = System.unique_integer([:positive])
    helper = :"Elixir.Muro297Helper#{n}"
    shared = :"Elixir.Muro297Shared#{n}"
    helper_beam = beam(helper)
    shared_beam = beam(shared)

    assert {out, 1} = executable(dir, ["gen"])
    assert out =~ "Formatter plugin #{inspect(plugin)} cannot be found"
    assert out =~ "_build/dev/lib/*/ebin"

    # The plugin's application lists a second built application. The
    # executable is a release in embedded mode, which does not load a
    # module when it is first called, so both are loaded whole even
    # though nothing here calls the helper or the shared module.
    app(dir, "plug297", [plugin: beam, helper: helper_beam], [
      :kernel,
      :stdlib,
      :elixir,
      :shared297
    ])

    app(dir, "shared297", [shared: shared_beam], [:kernel, :stdlib, :elixir])

    loaded =
      "IO.puts(inspect(Enum.map([#{inspect(helper)}, #{inspect(shared)}], &:code.is_loaded/1)))"

    assert {out, 0} = executable(dir, ["gen"], [], loaded)
    assert out =~ "written #{@target}\n"
    assert out =~ ~r{^\[file: ~c".+/plug297/ebin/.+", file: ~c".+/shared297/ebin/.+"\]$}m
    assert File.read!(Path.join(dir, @target)) =~ ~r/\n# plugged\n\z/
    assert {_out, 0} = executable(dir, ["gen", "--check"])
  end

  defp beam(module) do
    {:module, _, beam, _} =
      Module.create(module, quote(do: def(ok, do: :ok)), Macro.Env.location(__ENV__))

    :code.purge(module)
    :code.delete(module)
    beam
  end

  defp app(dir, name, beams, applications) do
    ebin = Path.join(dir, "_build/dev/lib/#{name}/ebin")
    File.mkdir_p!(ebin)

    modules =
      for {_, beam} <- beams do
        {:ok, {module, _}} = :beam_lib.chunks(beam, [])
        File.write!(Path.join(ebin, "#{module}.beam"), beam)
        module
      end

    spec = {:application, String.to_atom(name), [modules: modules, applications: applications]}
    File.write!(Path.join(ebin, "#{name}.app"), :io_lib.format(~c"~tp.~n", [spec]))
  end

  defp project(formatter) do
    dir = Path.join(System.tmp_dir!(), "muro_exe_fmt_#{System.unique_integer([:positive])}")
    File.mkdir_p!(Path.join(dir, "priv/muro"))
    on_exit(fn -> File.rm_rf!(dir) end)

    File.write!(Path.join(dir, "priv/muro/rounding.muro"), @round)
    File.write!(Path.join(dir, ".formatter.exs"), formatter)

    File.write!(Path.join(dir, "muro.toml"), """
    muro = "#{Mix.Tasks.Muro.version()}"

    [[modules]]
    book = "priv/muro/rounding.muro"
    target = "#{@target}"
    module = "Repro.RoundingTest"
    backend = "exunit"
    """)

    dir
  end

  defp dep(dir, path, formatter) do
    File.mkdir_p!(Path.join(dir, path))
    File.write!(Path.join([dir, path, ".formatter.exs"]), formatter)
  end

  # A path dependency under deps/ is in Mix.Project.deps_paths/0 without
  # fetching. muro.toml moves aside so mix muro.gen reads mix.exs.
  # in_project in the test VM would sit on top of muro's own project and
  # read muro's dependencies, so mix muro.gen runs in its own VM.
  defp host_mix(dir) do
    File.write!(Path.join([dir, "deps/ecto/mix.exs"]), """
    defmodule Ecto297.MixProject do
      use Mix.Project
      def project, do: [app: :ecto, version: "0.1.0"]
    end
    """)

    File.rm!(Path.join(dir, "muro.toml"))

    File.write!(Path.join(dir, "mix.exs"), """
    defmodule Repro297.MixProject do
      use Mix.Project

      def project do
        [
          app: :repro297,
          version: "0.1.0",
          prune_code_paths: false,
          deps: [{:ecto, path: "deps/ecto"}],
          muro: [
            muro: "#{Mix.Tasks.Muro.version()}",
            modules: [
              {"priv/muro/rounding.muro", Repro.RoundingTest, "#{@target}", kind: :exunit}
            ]
          ]
        ]
      end
    end
    """)
  end

  defp mix_route(dir) do
    vm(
      dir,
      "Muro.Application.ensure_mix_servers(); " <>
        "Mix.Project.in_project(:repro297, \".\", fn _ -> Mix.Tasks.Muro.Gen.run([]) end)",
      [],
      []
    )
  end

  defp executable(dir, args, env \\ [], after_gen \\ "nil") do
    script =
      "Muro.Application.ensure_mix_servers(); " <>
        "nil = Mix.Project.get(); " <>
        "code = Muro.CLI.main(System.argv()); #{after_gen}; System.halt(code)"

    vm(dir, script, args, env)
  end

  defp vm(dir, script, args, env) do
    paths =
      Mix.Project.build_path()
      |> Path.join("lib/*/ebin")
      |> Path.wildcard()
      |> Enum.flat_map(&["-pa", &1])

    env = [{"MIX_ENV", nil}, {"MIX_BUILD_PATH", nil}, {"MIX_DEPS_PATH", nil} | env]

    System.cmd("elixir", paths ++ ["-e", script, "--" | args],
      cd: dir,
      env: Enum.uniq_by(Enum.reverse(env), &elem(&1, 0)),
      stderr_to_stdout: true
    )
  end
end

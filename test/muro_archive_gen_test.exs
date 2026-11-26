defmodule Muro.ArchiveGenTest do
  # `mix muro.gen` from the Mix archive, in a project whose deps are not
  # compiled yet and whose `.formatter.exs` names a plugin (#301).
  # Loading the plugin compiles the deps, which prunes the code path to
  # the project's deps. The test build's muro ebin is installed as an
  # archive in a fresh MIX_ARCHIVES, and the plugin is a local path
  # dep, so nothing is fetched.
  use ExUnit.Case, async: false

  @round """
  def round : run Π (n : Nat) → Nat :=
    λ (n : Nat) → n

  def round-ok : evidence {round (suc 0) ≡ suc 0 : Nat} :=
    refl
  """

  @target "test/muro/rounding_test.exs"

  test "mix muro.gen and --check finish when loading the formatter plugin compiles the deps" do
    archives = archives()
    dir = project()

    {out, status} = mix(dir, archives, ["muro.gen"])
    assert status == 0, out
    assert out =~ "Generated fmt_plugin app"
    assert out =~ "written #{@target}\n"
    refute out =~ "UndefinedFunctionError"
    assert File.read!(Path.join(dir, @target)) =~ "defmodule Repro.Muro.RoundingTest do\n"

    # A fresh checkout again: no _build, so --check compiles the plugin too.
    File.rm_rf!(Path.join(dir, "_build"))

    {out, status} = mix(dir, archives, ["muro.gen", "--check"])
    assert status == 0, out
    assert out =~ "Generated fmt_plugin app"
    assert out =~ "ok\n"
    refute out =~ "UndefinedFunctionError"

    # With the deps compiled, the run compiles nothing and still passes.
    {out, status} = mix(dir, archives, ["muro.gen", "--check"])
    assert status == 0, out
    refute out =~ "Generated fmt_plugin app"
    assert out =~ "ok\n"
  end

  defp archives do
    version = Mix.Tasks.Muro.version()
    dir = tmp("archives")
    name = "muro-#{version}"
    ebin = Path.join([dir, name, name, "ebin"])
    File.mkdir_p!(Path.dirname(ebin))
    File.cp_r!(Path.dirname(List.to_string(:code.which(Muro.Gen))), ebin)
    dir
  end

  defp project do
    dir = tmp("project")
    version = Mix.Tasks.Muro.version()

    write(dir, "mix.exs", """
    defmodule Repro.MixProject do
      use Mix.Project

      def project do
        [app: :repro, version: "0.1.0", deps: [{:fmt_plugin, path: "fmt_plugin"}]]
      end
    end
    """)

    write(dir, "fmt_plugin/mix.exs", """
    defmodule FmtPlugin.MixProject do
      use Mix.Project

      def project, do: [app: :fmt_plugin, version: "0.1.0"]
    end
    """)

    write(dir, "fmt_plugin/lib/fmt_plugin.ex", """
    defmodule FmtPlugin do
      @behaviour Mix.Tasks.Format

      def features(_opts), do: [extensions: [".heex"]]
      def format(contents, _opts), do: contents
    end
    """)

    write(dir, ".formatter.exs", """
    [plugins: [FmtPlugin], inputs: ["{mix,.formatter}.exs", "{lib,test}/**/*.{ex,exs}"]]
    """)

    write(dir, "priv/muro/rounding.muro", @round)

    write(dir, "muro.exs", """
    [
      muro: "#{version}",
      modules: [
        {"priv/muro/rounding.muro", Repro.Muro.RoundingTest, "#{@target}",
         [kind: :exunit, impl: Repro.Muro.Rounding]}
      ]
    ]
    """)

    dir
  end

  defp mix(dir, archives, args) do
    env =
      for name <-
            ~w(MIX_ENV MIX_TARGET MIX_BUILD_PATH MIX_BUILD_ROOT MIX_DEPS_PATH MIX_PATH MIX_EXS MIX_LOCKFILE),
          do: {name, nil}

    System.cmd("mix", args,
      cd: dir,
      env: [{"MIX_ARCHIVES", archives} | env],
      stderr_to_stdout: true
    )
  end

  defp write(dir, rel, text) do
    path = Path.join(dir, rel)
    File.mkdir_p!(Path.dirname(path))
    File.write!(path, text)
  end

  defp tmp(label) do
    dir =
      Path.join(
        System.tmp_dir!(),
        "muro_archive_gen_#{label}_#{System.unique_integer([:positive])}"
      )

    File.rm_rf!(dir)
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end

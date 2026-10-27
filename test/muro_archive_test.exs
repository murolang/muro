defmodule Muro.ArchiveTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  test "mix muro --version prints the application spec" do
    version = Mix.Tasks.Muro.version()
    assert version =~ ~r/^\d+\.\d+\.\d+$/

    out = capture_io(fn -> Mix.Tasks.Muro.run(["--version"]) end)
    assert String.trim(out) == "Muro v#{version}"

    out = capture_io(fn -> Mix.Tasks.Muro.run(["-v"]) end)
    assert String.trim(out) == "Muro v#{version}"
  end

  test "mix muro lists the tasks on one line" do
    version = Mix.Tasks.Muro.version()
    out = capture_io(fn -> Mix.Tasks.Muro.run([]) end)
    assert out == "Muro v#{version}\nmix muro.check  mix muro.emit\n"
  end

  test "mix muro rejects unknown arguments" do
    assert_raise Mix.Error, ~r/usage: mix muro/, fn ->
      Mix.Tasks.Muro.run(["--nope"])
    end
  end

  test "mix muro.check prints the version, then the success sentence" do
    version = Mix.Tasks.Muro.version()
    dir = tmp_dir()
    path = Path.join(dir, "z.muro")
    File.write!(path, "def z : run Nat := 0\n")

    out = capture_io(fn -> assert Mix.Tasks.Muro.Check.run([path]) == :ok end)

    assert out =~ "Muro v#{version}\nAll terms check. Evidence never becomes a run.\n"
  end

  test "mix muro.check prints the version when the book is refused" do
    version = Mix.Tasks.Muro.version()

    out =
      capture_io(fn ->
        assert_raise Mix.Error, ~r/duplicate name Foo/, fn ->
          Mix.Tasks.Muro.Check.run(["examples/bad_dup.muro"])
        end
      end)

    assert out =~ "Muro v#{version}"
  end

  test "uses_muro? is true for this application and for a declared muro dep" do
    assert Mix.Tasks.Muro.uses_muro?(app: :muro)
    assert Mix.Tasks.Muro.uses_muro?(app: :muro, deps: [{:nx, "~> 0.9", optional: true}])

    assert Mix.Tasks.Muro.uses_muro?(app: :host, deps: [{:muro, "~> 0.16"}])
    assert Mix.Tasks.Muro.uses_muro?(app: :host, deps: [{:muro, path: "../muro"}])

    assert Mix.Tasks.Muro.uses_muro?(
             app: :host,
             deps: [{:muro, git: "https://github.com/murolang/muro.git", tag: "v0.16.74"}]
           )

    assert Mix.Tasks.Muro.uses_muro?(app: :host, deps: [{:muro, "~> 0.16", only: :dev}])

    assert Mix.Tasks.Muro.uses_muro?(
             app: :host,
             deps: [{:nx, "~> 0.9"}, {:muro, "~> 0.16", optional: true}]
           )
  end

  test "uses_muro? is false when the project does not declare muro" do
    refute Mix.Tasks.Muro.uses_muro?([])
    refute Mix.Tasks.Muro.uses_muro?(app: :host)
    refute Mix.Tasks.Muro.uses_muro?(app: :host, deps: [])
    refute Mix.Tasks.Muro.uses_muro?(app: :host, deps: nil)
    refute Mix.Tasks.Muro.uses_muro?(app: :host, deps: [{:nx, "~> 0.9"}])
    refute Mix.Tasks.Muro.uses_muro?(app: :host, deps: [{:nx, "~> 0.9", only: :dev}])
    refute Mix.Tasks.Muro.uses_muro?(app: :host, deps: [{:nx, path: "../nx"}])
  end

  test "the makeup lexer is registered only when Makeup is loaded" do
    assert Muro.Application.register_makeup_lexer(false) == :skipped
    assert Muro.Application.register_makeup_lexer(true) == :registered
    assert {:ok, {Muro.MakeupLexer, []}} = Makeup.Registry.fetch_lexer_by_name("muro")
  end

  test "a NIF is refused when elixir_make is absent" do
    assert Muro.Emit.Nif.elixir_make_available?()
    assert Muro.Emit.Nif.require_elixir_make!() == :ok
    assert Muro.Emit.Nif.ensure_make!([], false) == :ok

    err =
      assert_raise Mix.Error, fn ->
        Muro.Emit.Nif.require_elixir_make!(false)
      end

    assert err.message =~ "{:elixir_make, \"~> 0.10\", runtime: false}"
    assert err.message =~ "project deps"
    assert err.message =~ "project that depends on muro"

    dir = tmp_dir()
    sig = %{export: true, name: "half", ret: "muro_nat *", params: []}

    assert_raise Mix.Error, ~r/elixir_make/, fn ->
      Muro.Emit.Nif.ensure_make!([sig], false)
    end

    assert_raise Mix.Error, ~r/elixir_make/, fn ->
      Muro.Emit.Nif.build(dir, "half", [sig], false)
    end

    refute File.exists?(Path.join(dir, "half.ex"))
    refute File.exists?(Path.join(dir, "half_nif.c"))
    assert Muro.Emit.Nif.build(dir, "half", [], false) == []
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_archive_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end

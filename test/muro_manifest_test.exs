defmodule Muro.ManifestTest do
  use ExUnit.Case, async: false

  @one "def one : run Nat := suc 0\n"

  test "loads muro.exs and defaults fuel" do
    dir = tmp_dir()
    write_book(dir, "priv/muro/one.muro")

    File.write!(Path.join(dir, "muro.exs"), """
    [
      muro: "0.16.74",
      modules: [
        {"priv/muro/one.muro", MyApp.Billing.Rounding, "lib/my_app/billing/rounding.ex"}
      ]
    ]
    """)

    assert {:ok, manifest} = Muro.Manifest.load(dir)
    assert manifest.version == "0.16.74"
    assert manifest.fuel == Muro.Check.default_fuel()
    assert manifest.source == :muro_exs

    assert manifest.modules == [
             %{
               book: "priv/muro/one.muro",
               module: MyApp.Billing.Rounding,
               target: "lib/my_app/billing/rounding.ex"
             }
           ]
  end

  test "loads a :muro key from the Mix project at the root" do
    dir = tmp_dir()
    version = Mix.Tasks.Muro.version()

    File.write!(Path.join(dir, "mix.exs"), mix_project(:sample_key, version, []))

    Mix.Project.in_project(:sample_key, dir, fn _module ->
      assert {:ok, manifest} = Muro.Manifest.load(dir)
      assert manifest.source == :mix
      assert manifest.version == version
      assert manifest.modules == []
    end)
  end

  test "refuses muro.exs and a :muro key together" do
    dir = tmp_dir()
    version = Mix.Tasks.Muro.version()
    File.write!(Path.join(dir, "muro.exs"), "[\n  muro: \"#{version}\",\n  modules: []\n]\n")
    File.write!(Path.join(dir, "mix.exs"), mix_project(:sample_both, version, []))

    message =
      Mix.Project.in_project(:sample_both, dir, fn _module ->
        assert {:error, message} = Muro.Manifest.load(dir)
        message
      end)

    assert message =~ "muro.exs"
    assert message =~ ":muro key in mix.exs"
  end

  test "reports a missing manifest" do
    dir = tmp_dir()

    assert {:error, message} = Muro.Manifest.load(dir)
    assert message =~ "muro.exs"
    assert message =~ ":muro"
  end

  test "reports a muro.exs that fails to evaluate" do
    dir = tmp_dir()
    File.write!(Path.join(dir, "muro.exs"), "[\n")

    assert {:error, message} = Muro.Manifest.load(dir)
    assert message =~ "muro.exs failed to evaluate"
  end

  test "reports a manifest that is not a keyword list" do
    dir = tmp_dir()
    assert {:error, message} = Muro.Manifest.validate(1, dir)
    assert message =~ "keyword list"
  end

  test "reports missing keys, a bad fuel, and unknown keys together" do
    dir = tmp_dir()

    assert {:error, message} =
             Muro.Manifest.validate([fuel: 0, fuelx: 1, muro: "1", muro: "1"], dir)

    assert message =~ "missing modules:"
    assert message =~ "fuel: must be a positive integer"
    assert message =~ "unknown keys: [:fuelx]"
    assert message =~ "repeats :muro"
  end

  test "reports a muro value that is not a version string" do
    dir = tmp_dir()

    assert {:error, message} = Muro.Manifest.validate([muro: "", modules: []], dir)
    assert message =~ "muro: must be a version string"

    assert {:error, message} = Muro.Manifest.validate([muro: 1, modules: []], dir)
    assert message =~ "muro: must be a version string"
  end

  test "reports a modules value that is not a list of entries" do
    dir = tmp_dir()

    assert {:error, message} = Muro.Manifest.validate([muro: "1.0.0", modules: :no], dir)
    assert message =~ "modules: must be a list"

    assert {:error, message} =
             Muro.Manifest.validate([muro: "1.0.0", modules: [{"only"}]], dir)

    assert message =~ "modules entry 1 is not {book, module, target}"
  end

  test "reports a missing book, a bad module, an outside target, and a duplicate" do
    dir = tmp_dir()
    write_book(dir, "priv/muro/one.muro")

    assert {:error, message} =
             Muro.Manifest.validate(
               [
                 muro: "1.0.0",
                 modules: [
                   {"priv/muro/missing.muro", :not_alias, "../out.ex"},
                   {"/tmp/outside.muro", "Rounding", "lib/a.ex"},
                   {"priv/muro/one.muro", MyApp.Rounding, "lib/./a.ex"},
                   {"priv/muro/one.muro", MyApp.Rounding, "lib/a.ex"}
                 ]
               ],
               dir
             )

    assert message =~ "modules entry 1: missing book priv/muro/missing.muro"
    assert message =~ "modules entry 1: module is not an alias atom, got: :not_alias"
    assert message =~ "modules entry 1: target is outside the project: \"../out.ex\""
    assert message =~ "modules entry 2: book is outside the project:"
    assert message =~ "modules entry 2: module is not an alias atom, got: \"Rounding\""
    assert message =~ "duplicate target lib/a.ex (modules entries 2 and 3)"
    assert message =~ "duplicate target lib/a.ex (modules entries 2 and 4)"
  end

  test "normalizes a duplicate target written two ways" do
    dir = tmp_dir()
    write_book(dir, "ok.muro")

    assert {:error, message} =
             Muro.Manifest.validate(
               [
                 muro: "1.0.0",
                 modules: [
                   {"ok.muro", One, "lib/nested/../one.ex"},
                   {"ok.muro", Two, "lib/one.ex"}
                 ]
               ],
               dir
             )

    assert message =~ "duplicate target lib/one.ex (modules entries 1 and 2)"
  end

  test "rejects a module atom that is not an alias" do
    dir = tmp_dir()
    write_book(dir, "ok.muro")

    assert {:error, message} =
             Muro.Manifest.validate(
               [muro: "1.0.0", modules: [{"ok.muro", :"Foo.bar", "lib/one.ex"}]],
               dir
             )

    assert message =~ "module is not an alias atom"
  end

  test "version pin names both versions" do
    assert Muro.Manifest.version_pin("0.16.74", "0.16.74") == :ok

    assert {:error, message} = Muro.Manifest.version_pin("0.16.72", "0.16.74")
    assert message =~ "manifest says 0.16.72"
    assert message =~ "running 0.16.74"
  end

  test "root follows the working directory outside a Mix project" do
    project = Path.expand(File.cwd!())
    assert Muro.Manifest.root() == project

    parent = Path.dirname(project)

    File.cd!(parent, fn ->
      assert Muro.Manifest.root() == parent
    end)

    File.cd!(Path.join(project, "lib"), fn ->
      assert Muro.Manifest.root() == project
    end)
  end

  defp mix_project(app, version, modules) do
    entries =
      Enum.map_join(modules, "\n", fn {book, module, target} ->
        "        {#{inspect(book)}, #{inspect(module)}, #{inspect(target)}},"
      end)

    module = Module.concat([Macro.camelize(Atom.to_string(app)), MixProject])

    """
    defmodule #{inspect(module)} do
      use Mix.Project

      def project do
        [
          app: #{inspect(app)},
          version: "0.1.0",
          muro: [
            muro: "#{version}",
            modules: [
    #{entries}
            ]
          ]
        ]
      end
    end
    """
  end

  defp write_book(dir, rel) do
    path = Path.join(dir, rel)
    File.mkdir_p!(Path.dirname(path))
    File.write!(path, @one)
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_manifest_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end

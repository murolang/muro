defmodule Muro.ManifestTest do
  use ExUnit.Case, async: false

  @one "def one : run Nat := suc 0\n"

  test "loads muro.exs and defaults fuel" do
    dir = tmp_dir()
    write_book(dir, "priv/muro/one.muro")

    File.write!(Path.join(dir, "muro.exs"), """
    [
      muro: "0.18.0",
      modules: [
        {"priv/muro/one.muro", MyApp.Billing.Rounding, "lib/my_app/billing/rounding.ex"}
      ]
    ]
    """)

    assert {:ok, manifest} = Muro.Manifest.load(dir)
    assert manifest.version == "0.18.0"
    assert manifest.fuel == Muro.Check.default_fuel()
    assert manifest.source == :muro_exs

    assert manifest.modules == [
             %{
               book: "priv/muro/one.muro",
               module: MyApp.Billing.Rounding,
               target: "lib/my_app/billing/rounding.ex",
               kind: :elixir,
               impl: nil,
               imports: false
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

  test "accepts an exunit entry and its implementation module" do
    dir = tmp_dir()
    write_book(dir, "priv/muro/round.muro")

    assert {:ok, manifest} =
             Muro.Manifest.validate(
               [
                 muro: "1.0.0",
                 modules: [
                   {"priv/muro/round.muro", MyApp.Round, "lib/round.ex"},
                   {"priv/muro/round.muro", MyApp.RoundTest, "test/round_test.exs",
                    [kind: :exunit, impl: MyApp.Rounding]}
                 ]
               ],
               dir
             )

    assert manifest.modules == [
             %{
               book: "priv/muro/round.muro",
               module: MyApp.Round,
               target: "lib/round.ex",
               kind: :elixir,
               impl: nil,
               imports: false
             },
             %{
               book: "priv/muro/round.muro",
               module: MyApp.RoundTest,
               target: "test/round_test.exs",
               kind: :exunit,
               impl: MyApp.Rounding,
               imports: false
             }
           ]
  end

  test "rejects unknown entry options, an unknown kind, and impl on elixir" do
    dir = tmp_dir()
    write_book(dir, "ok.muro")

    assert {:error, unknown} =
             Muro.Manifest.validate(
               [muro: "1.0.0", modules: [{"ok.muro", One, "lib/one.ex", [colour: :blue]}]],
               dir
             )

    assert unknown =~ "modules entry 1: unknown options [:colour]"

    assert {:error, kind} =
             Muro.Manifest.validate(
               [muro: "1.0.0", modules: [{"ok.muro", One, "lib/one.ex", [kind: :haskell]}]],
               dir
             )

    assert kind =~ "modules entry 1: unknown kind :haskell"

    assert {:error, impl_kind} =
             Muro.Manifest.validate(
               [
                 muro: "1.0.0",
                 modules: [{"ok.muro", One, "lib/one.ex", [kind: :elixir, impl: One]}]
               ],
               dir
             )

    assert impl_kind =~ "modules entry 1: impl: is only valid for kind: :exunit"

    assert {:error, impl_atom} =
             Muro.Manifest.validate(
               [
                 muro: "1.0.0",
                 modules: [{"ok.muro", One, "lib/one.ex", [kind: :exunit, impl: :round]}]
               ],
               dir
             )

    assert impl_atom =~ "modules entry 1: impl is not an alias atom"

    assert {:error, not_opts} =
             Muro.Manifest.validate(
               [muro: "1.0.0", modules: [{"ok.muro", One, "lib/one.ex", :exunit}]],
               dir
             )

    assert not_opts =~ "modules entry 1 is not {book, module, target}"

    assert {:error, on_elixir} =
             Muro.Manifest.validate(
               [
                 muro: "1.0.0",
                 modules: [{"ok.muro", One, "lib/one.ex", [kind: :elixir, imports: true]}]
               ],
               dir
             )

    assert on_elixir =~ "modules entry 1: imports: is only valid for kind: :exunit"

    assert {:error, bad_bool} =
             Muro.Manifest.validate(
               [
                 muro: "1.0.0",
                 modules: [{"ok.muro", One, "lib/one.ex", [kind: :exunit, imports: :yes]}]
               ],
               dir
             )

    assert bad_bool =~ "modules entry 1: imports: must be a boolean, got: :yes"
  end

  test "imports: true is stored only on an exunit entry" do
    dir = tmp_dir()
    write_book(dir, "ok.muro")

    assert {:ok, manifest} =
             Muro.Manifest.validate(
               [
                 muro: "1.0.0",
                 modules: [
                   {"ok.muro", OneTest, "test/one_test.exs", [kind: :exunit, imports: true]}
                 ]
               ],
               dir
             )

    assert manifest.modules == [
             %{
               book: "ok.muro",
               module: OneTest,
               target: "test/one_test.exs",
               kind: :exunit,
               impl: nil,
               imports: true
             }
           ]
  end

  test "load_deps reads only muro_deps and returns an empty list when it is absent" do
    dir = tmp_dir()

    assert Muro.Manifest.load_deps(dir) == {:ok, []}

    File.write!(Path.join(dir, "muro.exs"), "[\n  fuel: 3\n]\n")
    assert Muro.Manifest.load_deps(dir) == {:ok, []}

    File.write!(Path.join(dir, "muro.exs"), """
    [
      muro_deps: [
        pricing: {:hex, "pricing_rules", "~> 2.0"},
        shared_wire: {:git, "https://github.com/acme/shared-wire", tag: "v1.2.0", root: "priv/muro"}
      ]
    ]
    """)

    assert {:ok, [pricing, shared]} = Muro.Manifest.load_deps(dir)
    assert pricing.name == "pricing"
    assert pricing.kind == :hex
    assert pricing.root == "priv/muro"
    assert pricing.source == {:hex, "pricing_rules", "~> 2.0"}
    assert shared.name == "shared_wire"
    assert shared.pin == {:tag, "v1.2.0"}
    assert shared.root == "priv/muro"

    assert shared.source ==
             {:git, "https://github.com/acme/shared-wire", [tag: "v1.2.0", root: "priv/muro"]}
  end

  test "load validates muro_deps and still requires muro and modules" do
    dir = tmp_dir()
    write_book(dir, "priv/muro/one.muro")

    assert {:error, message} =
             Muro.Manifest.validate([muro_deps: [shared: {:path, "x"}]], dir)

    assert message =~ "muro_deps entry shared: unknown source"
    assert message =~ "missing muro:"
    assert message =~ "missing modules:"
  end

  test "muro_deps names the entry when the spec is refused" do
    dir = tmp_dir()

    refused = [
      {[shared: {:git, "https://example.com/a", tag: "v1", ref: "main"}],
       "tag and ref are both set"},
      {[shared: {:git, "https://example.com/a", branch: "main"}], "unknown option"},
      {[shared: {:git, "https://example.com/a", []}], "expected one of tag: or ref:"},
      {[Shared: {:git, "https://example.com/a", tag: "v1"}], "name must match"},
      {[shared: {:hex, "pricing_rules", "not a req"}], "requirement"},
      {[shared: {:hex, "Pricing", "~> 1.0"}], "package"},
      {[shared: {:git, "-https://example.com/a", tag: "v1"}], "url"},
      {[shared: {:git, "https://example.com/a", tag: "v1", root: "../x"}], "root"},
      {[
         shared: {:git, "https://example.com/a", tag: "v1"},
         shared: {:hex, "pricing_rules", "~> 1.0"}
       ], "duplicate name"}
    ]

    Enum.each(refused, fn {deps, fragment} ->
      assert {:error, message} = Muro.Manifest.validate([muro_deps: deps], dir)
      assert message =~ "muro_deps entry"
      assert message =~ fragment
    end)
  end

  test "load_deps refuses muro.exs and a :muro key together" do
    dir = tmp_dir()
    version = Mix.Tasks.Muro.version()
    File.write!(Path.join(dir, "muro.exs"), "[\n  muro_deps: []\n]\n")
    File.write!(Path.join(dir, "mix.exs"), mix_project(:sample_deps_both, version, []))

    message =
      Mix.Project.in_project(:sample_deps_both, dir, fn _module ->
        assert {:error, message} = Muro.Manifest.load_deps(dir)
        message
      end)

    assert message =~ "muro.exs"
    assert message =~ ":muro key in mix.exs"
  end

  test "version pin names both versions" do
    assert Muro.Manifest.version_pin("0.18.0", "0.18.0") == :ok

    assert {:error, message} = Muro.Manifest.version_pin("0.16.72", "0.18.0")
    assert message =~ "manifest says 0.16.72"
    assert message =~ "running 0.18.0"
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

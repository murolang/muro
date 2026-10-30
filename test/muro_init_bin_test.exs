defmodule Muro.InitBinTest do
  use ExUnit.Case, async: false

  test "init writes one manifest for each kind of directory" do
    version = Mix.Tasks.Muro.version()

    mix = tmp()
    File.write!(Path.join(mix, "mix.exs"), mix_exs())
    assert cli(mix, ["init"]) == created_exs()
    assert File.read!(Path.join(mix, "muro.exs")) == Muro.Init.manifest_source(version)
    assert File.dir?(Path.join(mix, "priv/muro"))
    refute File.exists?(Path.join(mix, "muro.toml"))

    cargo = tmp()
    File.write!(Path.join(cargo, "Cargo.toml"), cargo_toml())
    assert cli(cargo, ["init"]) =~ "created muro.toml\n"
    assert cli_status(cargo, ["init"]) == 0
    toml = File.read!(Path.join(cargo, "muro.toml"))
    assert toml =~ ~s(muro = "#{version}")
    assert toml =~ ~s(backend = "rust")
    assert toml =~ ~s(target = "src/rounding.rs")
    assert File.dir?(Path.join(cargo, "muro"))
    original = toml

    File.write!(Path.join(cargo, "muro.toml"), String.replace(toml, "rust", "rust # edited"))
    edited = File.read!(Path.join(cargo, "muro.toml"))
    diff = cli(cargo, ["init"])
    assert diff =~ "--- a/muro.toml\n"
    assert diff =~ "+++ b/muro.toml\n"
    assert File.read!(Path.join(cargo, "muro.toml")) == edited
    assert edited != original

    meta = tmp()
    File.write!(Path.join(meta, "Cargo.toml"), cargo_toml())
    assert cli(meta, ["init", "--cargo-metadata"]) =~ "updated Cargo.toml\n"
    cargo_text = File.read!(Path.join(meta, "Cargo.toml"))
    assert cargo_text =~ "[package.metadata.muro]"
    assert cargo_text =~ ~s(backend = "rust")
    refute File.exists?(Path.join(meta, "muro.toml"))
    assert {:ok, manifest} = Muro.Manifest.load(meta)
    assert manifest.source == :cargo

    before = cargo_text
    File.write!(Path.join(meta, "Cargo.toml"), cargo_text <> "\n# hand\n")
    hand = File.read!(Path.join(meta, "Cargo.toml"))
    again = cli(meta, ["init", "--cargo-metadata"])
    assert again =~ "--- a/Cargo.toml\n"
    assert File.read!(Path.join(meta, "Cargo.toml")) == hand
    assert hand != before

    cmake = tmp()
    File.write!(Path.join(cmake, "CMakeLists.txt"), "cmake_minimum_required(VERSION 3.16)\n")
    assert cli(cmake, ["init"]) =~ "created muro.toml\n"
    assert File.read!(Path.join(cmake, "muro.toml")) =~ ~s(backend = "c")

    meson = tmp()
    File.write!(Path.join(meson, "meson.build"), "project('demo', 'c')\n")
    assert File.read!(write_init(meson)) =~ ~s(backend = "c")

    make = tmp()
    File.write!(Path.join(make, "Makefile"), "all:\n")
    assert File.read!(write_init(make)) =~ ~s(backend = "c")

    bare = tmp()
    assert cli(bare, ["init"]) =~ "created muro.toml\n"
    bare_toml = File.read!(Path.join(bare, "muro.toml"))
    assert bare_toml =~ "modules = []"
    refute bare_toml =~ ~s(backend =)
    assert File.dir?(Path.join(bare, "muro"))

    asm = tmp()
    assert cli(asm, ["init", "--backend", "asm"]) =~ "created muro.toml\n"
    asm_toml = File.read!(Path.join(asm, "muro.toml"))
    assert asm_toml =~ ~s(backend = "asm")
    assert asm_toml =~ ~s(target = "src/rounding.s")

    forced = tmp()
    File.write!(Path.join(forced, "mix.exs"), mix_exs())
    assert cli(forced, ["init", "--backend", "asm"]) =~ "created muro.exs\n"
    refute File.exists?(Path.join(forced, "muro.toml"))
    assert File.read!(Path.join(forced, "muro.exs")) =~ "kind: :asm"
  end

  test "init --ci github writes the binary workflow and refuses to replace one" do
    dir = tmp()
    version = Mix.Tasks.Muro.version()
    assert cli(dir, ["init", "--ci", "github"]) =~ "created .github/workflows/muro.yml\n"
    workflow = Path.join(dir, ".github/workflows/muro.yml")
    assert File.read!(workflow) == Muro.Init.binary_workflow(version)
    assert File.read!(workflow) =~ "muro-#{version}-linux-x86_64"
    assert File.read!(workflow) =~ "muro gen --check"
    refute File.read!(workflow) =~ "setup-beam"

    assert cli(dir, ["init", "--ci", "github"]) =~ "--- a/muro.toml\n"
    assert File.read!(workflow) == Muro.Init.binary_workflow(version)
  end

  test "--cargo-metadata outside a Cargo project is an error" do
    dir = tmp()
    assert cli_status(dir, ["init", "--cargo-metadata"]) == 1
    refute File.exists?(Path.join(dir, "muro.toml"))
  end

  defp write_init(dir) do
    assert cli_status(dir, ["init"]) == 0
    Path.join(dir, "muro.toml")
  end

  defp created_exs do
    note = String.trim_trailing(Muro.Init.note())

    """
    created muro.exs
    created priv/muro/
    #{note}
    """
  end

  defp cli(dir, args) do
    {out, code} = run(dir, args)
    assert code == 0, out
    out
  end

  defp cli_status(dir, args) do
    {_out, code} = run(dir, args)
    code
  end

  defp run(dir, args) do
    parent = self()

    out =
      File.cd!(dir, fn ->
        ExUnit.CaptureIO.capture_io(fn ->
          ExUnit.CaptureIO.capture_io(:stderr, fn ->
            send(parent, {:code, Muro.CLI.main(args)})
          end)
        end)
      end)

    assert_received {:code, code}
    {out, code}
  end

  defp mix_exs do
    """
    defmodule Tmp.MixProject do
      use Mix.Project
      def project, do: [app: :tmp, version: "0.0.1"]
    end
    """
  end

  defp cargo_toml do
    """
    [package]
    name = "demo"
    version = "0.1.0"
    """
  end

  defp tmp do
    dir = Path.join(System.tmp_dir!(), "muro_init_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end

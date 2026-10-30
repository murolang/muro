defmodule Muro.TomlTest do
  use ExUnit.Case, async: false

  test "muro.toml loads the same manifest shape as muro.exs" do
    dir = tmp()
    version = Mix.Tasks.Muro.version()
    write_book(dir, "muro/rounding.muro")

    File.write!(Path.join(dir, "muro.toml"), """
    muro = "#{version}"
    fuel = 2000 # rounds
    backend = "rust"

    [[modules]]
    book = "muro/rounding.muro"
    target = "src/rounding.rs"

    [muro_deps.rounding]
    git = "https://example.com/rounding.git"
    tag = "v1"
    """)

    assert {:ok, manifest} = Muro.Manifest.load(dir)
    assert manifest.source == :muro_toml
    assert manifest.version == version
    assert manifest.fuel == 2000
    assert manifest.backend == :rust

    assert [%{book: "muro/rounding.muro", target: "src/rounding.rs", module: nil, kind: :rust}] =
             manifest.modules

    assert [dep] = manifest.deps
    assert dep.name == "rounding"
    assert dep.kind == :git
    assert dep.pin == {:tag, "v1"}
    assert dep.source == {:git, "https://example.com/rounding.git", [tag: "v1"]}
  end

  test "an elixir entry takes an alias string and a native entry omits module" do
    dir = tmp()
    version = Mix.Tasks.Muro.version()
    write_book(dir, "muro/rounding.muro")

    File.write!(Path.join(dir, "muro.toml"), """
    muro = "#{version}"

    [[modules]]
    book = "muro/rounding.muro"
    target = "lib/rounding.ex"
    backend = "elixir"
    module = "MyApp.Billing.Rounding"
    """)

    assert {:ok, manifest} = Muro.Manifest.load(dir)
    assert hd(manifest.modules).module == MyApp.Billing.Rounding
    assert hd(manifest.modules).kind == :elixir
  end

  test "a missing backend, a bad extension, and a duplicate header name the entry" do
    dir = tmp()
    version = Mix.Tasks.Muro.version()
    write_book(dir, "muro/a.muro")
    write_book(dir, "muro/b.muro")

    assert {:error, missing} =
             load(dir, """
             muro = "#{version}"

             [[modules]]
             book = "muro/a.muro"
             target = "src/a.rs"
             """)

    assert missing =~ "muro.toml:"
    assert missing =~ "modules entry 1: missing backend"

    assert {:error, ext} =
             load(dir, """
             muro = "#{version}"
             backend = "rust"

             [[modules]]
             book = "muro/a.muro"
             target = "src/a.c"
             """)

    assert ext =~ "modules entry 1: target for kind :rust must end with .rs"

    assert {:error, dup} =
             load(dir, """
             muro = "#{version}"

             [[modules]]
             book = "muro/a.muro"
             target = "src/a.h"
             backend = "elixir"
             module = "A"

             [[modules]]
             book = "muro/b.muro"
             target = "src/a.c"
             backend = "c"
             """)

    assert dup =~ "duplicate target src/a.h (modules entries 1 and 2)"
  end

  test "paths outside the project and a book that is missing are refused" do
    dir = tmp()
    version = Mix.Tasks.Muro.version()

    assert {:error, outside} =
             load(dir, """
             muro = "#{version}"
             backend = "c"

             [[modules]]
             book = "../outside.muro"
             target = "src/a.c"
             """)

    assert outside =~ "modules entry 1: book is outside the project"

    assert {:error, missing} =
             load(dir, """
             muro = "#{version}"
             backend = "c"

             [[modules]]
             book = "muro/missing.muro"
             target = "src/a.c"
             """)

    assert missing =~ "modules entry 1: missing book muro/missing.muro"
  end

  test "the subset refuses what it does not understand and names the line" do
    dir = tmp()

    assert {:error, message} =
             load(dir, """
             muro = "0.0.1"
             fuel = 1.5
             modules = []
             """)

    assert message =~ "muro.toml:2:"

    assert {:error, dotted} =
             load(dir, """
             muro = "0.0.1"
             a.b = 1
             modules = []
             """)

    assert dotted =~ "muro.toml:2:"

    assert {:error, inline} =
             load(dir, """
             muro = "0.0.1"
             modules = []
             point = { x = 1 }
             """)

    assert inline =~ "muro.toml:3:"
  end

  test "Cargo.toml metadata loads, and both files together name both" do
    dir = tmp()
    version = Mix.Tasks.Muro.version()
    write_book(dir, "muro/rounding.muro")

    File.write!(Path.join(dir, "Cargo.toml"), """
    [package]
    name = "demo"
    version = "0.1.0"
    description = "keep [package.metadata.muro] inside this string"

    [package.metadata.muro]
    muro = "#{version}"
    backend = "rust"
    modules = []

    [dependencies]
    serde = "1"
    """)

    assert {:ok, manifest} = Muro.Manifest.load(dir)
    assert manifest.source == :cargo
    assert manifest.backend == :rust
    assert manifest.modules == []

    File.write!(Path.join(dir, "muro.toml"), """
    muro = "#{version}"
    modules = []
    """)

    assert {:error, both} = Muro.Manifest.load(dir)
    assert both =~ "muro.toml"
    assert both =~ "[package.metadata.muro] in Cargo.toml"
    assert both =~ "both define a manifest"

    File.write!(Path.join(dir, "muro.exs"), """
    [
      muro: "#{version}",
      modules: []
    ]
    """)

    assert {:error, three} = Muro.Manifest.load(dir)
    assert three =~ "muro.exs"
    assert three =~ "muro.toml"
    assert three =~ "[package.metadata.muro] in Cargo.toml"
    assert three =~ "all define a manifest"
  end

  test "quoted Cargo headers and their multiline values are skipped" do
    dir = tmp()
    version = Mix.Tasks.Muro.version()

    text = """
    [package]
    name = "demo"
    version = "0.1.0"

    [target.'cfg(unix)'.dependencies]
    libc = "0.2"
    note = '''
    [package.metadata.muro]
    muro = "not-this"
    '''
    flags = [
      "[also not a header]",
      "one",
    [package.metadata.muro]
    muro = "not-this"
    modules = []
    ]

    [target."x86_64-pc-windows-msvc".dependencies]
    windows-sys = { version = "0.52", features = [
      "Win32_Foundation",
    ] }

    [package.metadata.muro]
    muro = "#{version}"
    backend = "rust"
    modules = []
    """

    File.write!(Path.join(dir, "Cargo.toml"), text)
    assert Muro.Toml.cargo_metadata?(text)
    assert {:ok, manifest} = Muro.Manifest.load(dir)
    assert manifest.source == :cargo
    assert manifest.backend == :rust
    assert manifest.modules == []
  end

  test "the muro table still refuses a literal string and a quoted header" do
    dir = tmp()

    assert {:error, literal} =
             load(dir, """
             muro = "0.0.1"
             name = 'nope'
             modules = []
             """)

    assert literal =~ "literal strings are not supported"

    assert {:error, header} =
             load(dir, """
             muro = "0.0.1"
             modules = []

             ['quoted']
             """)

    assert header =~ "expected a table name"

    cargo = tmp()
    version = Mix.Tasks.Muro.version()

    File.write!(Path.join(cargo, "Cargo.toml"), """
    [package.metadata.muro]
    muro = "#{version}"
    modules = []

    [package.metadata.muro.'child']
    x = 1
    """)

    assert {:error, child} = Muro.Manifest.load(cargo)
    assert child =~ "expected a table name"
  end

  test "a Cargo.toml without the muro table is not a manifest root" do
    dir = tmp()

    File.write!(Path.join(dir, "Cargo.toml"), """
    [package]
    name = "demo"
    version = "0.1.0"
    """)

    assert Muro.Manifest.manifest_name(dir) == nil
    assert {:error, message} = Muro.Manifest.load(dir)
    assert message =~ "muro.exs"
    assert message =~ "muro.toml"
    assert message =~ ":muro"
  end

  test "find_root climbs to muro.toml" do
    dir = tmp()
    File.mkdir_p!(Path.join(dir, "src"))

    File.write!(Path.join(dir, "muro.toml"), """
    muro = "0.0.1"
    modules = []
    """)

    assert Muro.Manifest.find_root(Path.join(dir, "src/a.rs")) == Muro.Manifest.canonical(dir)
  end

  defp load(dir, text) do
    File.write!(Path.join(dir, "muro.toml"), text)
    Muro.Manifest.load(dir)
  end

  defp write_book(dir, rel) do
    path = Path.join(dir, rel)
    File.mkdir_p!(Path.dirname(path))
    File.write!(path, "def one : run Nat := 0\n")
  end

  defp tmp do
    dir = Path.join(System.tmp_dir!(), "muro_toml_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end

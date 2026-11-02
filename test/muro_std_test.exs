defmodule Muro.StdTest do
  use ExUnit.Case, async: true

  test "every standard library book checks on disk" do
    for name <- Muro.Std.names() do
      assert Muro.check_file(Path.join("lib/muro/std", name)) == :ok
    end
  end

  test "std: resolves from a directory outside the repo" do
    dir = tmp()

    use = Path.join(dir, "use.muro")

    File.write!(use, """
    import "std:bool.muro"
    import "std:list.muro"
    def n : run Bool := not false
    def len0 : run Nat := length Nat nil
    """)

    assert Muro.check_file(use) == :ok
    assert {:ok, ["std:bool.muro", "std:list.muro"]} = Muro.Load.direct_imports(use)

    assert {:ok, book} = Muro.Load.file(use)
    assert Enum.count(book, &(&1.name == "fromMaybe")) == 1
    assert Enum.any?(book, &(&1.name == "fromMaybe" and &1.file == "std:maybe.muro"))
  end

  test "a std book imported twice joins once" do
    dir = tmp()
    path = Path.join(dir, "twice.muro")

    File.write!(path, """
    import "std:bool.muro"
    import "std:bool.muro"
    def n : run Bool := not false
    """)

    assert {:ok, book} = Muro.Load.file(path)
    assert Enum.count(book, &(&1.name == "not")) == 1
    assert Enum.count(book, &(&1.name == "Bool")) == 1
  end

  test "an unknown book and a path that leaves the library are refused" do
    dir = tmp()
    missing = Path.join(dir, "missing.muro")

    File.write!(missing, """
    import "std:nope.muro"
    def n : run Nat := 0
    """)

    assert {:error, msg} = Muro.check_file(missing)
    assert msg =~ "unknown standard library book \"nope.muro\""
    assert msg =~ "available books: bool.muro, le.muro, list.muro, maybe.muro, ord.muro"
    assert msg =~ "missing.muro:1:1:"

    escape = Path.join(dir, "escape.muro")

    File.write!(escape, """
    import "std:../le.muro"
    def n : run Nat := 0
    """)

    assert {:error, msg} = Muro.check_file(escape)
    assert msg =~ "import \"std:../le.muro\" leaves the standard library"

    nested = Path.join(dir, "nested.muro")

    File.write!(nested, """
    import "std:foo/../../le.muro"
    def n : run Nat := 0
    """)

    assert {:error, msg} = Muro.check_file(nested)
    assert msg =~ "leaves the standard library"

    slash = Path.join(dir, "slash.muro")

    File.write!(slash, """
    import "std:le.muro\\x"
    def n : run Nat := 0
    """)

    assert {:error, msg} = Muro.check_file(slash)
    assert msg =~ "leaves the standard library"

    assert Muro.Std.relative("std:ord.muro", "../le.muro") == :escape
    assert Muro.Std.relative("std:ord.muro", "le.muro") == {:ok, "le.muro"}
    assert Muro.Std.classify("./bool.muro") == {:ok, "bool.muro"}
  end

  test "an imported std book is hashed as std/<file> and a missing one is omitted" do
    dir = tmp()
    use = "import \"std:bool.muro\"\ndef n : run Bool := not false\n"
    write = Path.join(dir, "use.muro")
    File.write!(write, use)
    {:ok, bool} = Muro.Std.source("bool.muro")

    assert Muro.Gen.book_hash(dir, "use.muro") ==
             Muro.Hash.files([{"std/bool.muro", bool}, {"use.muro", use}])

    files = Muro.Gen.book_files(write)
    assert "std:bool.muro" in files
    refute Enum.any?(files, &String.ends_with?(&1, "/std:bool.muro"))

    missing = "import \"std:nope.muro\"\ndef n : run Nat := 0\n"
    File.write!(Path.join(dir, "miss.muro"), missing)

    assert Muro.Gen.book_hash(dir, "miss.muro") == Muro.Hash.files([{"miss.muro", missing}])
  end

  test "examples that import the standard library check" do
    for name <- ~w(list.muro maybe.muro sort.muro higher_order.muro second_field.muro) do
      assert Muro.check_file(Path.join("examples", name)) == :ok
    end
  end

  defp tmp do
    dir = Path.join(System.tmp_dir!(), "muro_std_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end

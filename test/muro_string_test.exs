defmodule Muro.StringTest do
  use ExUnit.Case, async: false

  import ExUnit.CaptureIO

  alias Muro.{Lexer, Parser, Print}

  test "a core literal keeps the escapes and rejects a surrogate" do
    assert {:ok, [defn]} = Parser.parse("def hello : run String := \"hello\"\n")
    assert defn.body == {:slit, "hello"}

    assert {:ok, [wave]} = Parser.parse("def wave : run String := \"\\u{1F44B}\"\n")
    assert wave.body == {:slit, "👋"}
    assert Print.scalar_count(wave.body |> elem(1)) == 1

    assert {:ok, [accent]} = Parser.parse("def accent : run String := \"é\"\n")
    assert accent.body == {:slit, <<195, 169>>}
    assert Print.scalar_count(<<195, 169>>) == 1

    assert {:ok, [two]} = Parser.parse("def two : run String := \"e\\u{0301}\"\n")
    assert two.body == {:slit, <<101, 204, 129>>}
    assert Print.scalar_count(<<101, 204, 129>>) == 2

    assert {:ok, [nul]} = Parser.parse("def nul : run String := \"\\u{0}\"\n")
    assert nul.body == {:slit, <<0>>}

    assert {:ok, [letter]} = Parser.parse("def letter : run String := \"\\u{41}\"\n")
    assert letter.body == {:slit, "A"}

    assert {:ok, [max]} = Parser.parse("def max : run String := \"\\u{10FFFF}\"\n")
    assert Print.scalar_count(elem(max.body, 1)) == 1

    assert {:ok, [past]} = Parser.parse("def past : run String := \"\\u{E000}\"\n")
    assert Print.scalar_count(elem(past.body, 1)) == 1

    assert {:ok, [nl]} = Parser.parse("def nl : run String := \"a\\nb\"\n")
    assert nl.body == {:slit, "a\nb"}

    assert {:ok, [quoted]} = Parser.parse("def quoted : run String := \"a\\\"b\"\n")
    assert quoted.body == {:slit, "a\"b"}

    assert {:ok, [slash]} = Parser.parse("def slash : run String := \"a\\\\b\"\n")
    assert slash.body == {:slit, "a\\b"}

    assert {:ok, [cat]} = Parser.parse("def parts : run String := strCat \"hel\" \"lo\"\n")
    assert cat.body == {:scat, {:slit, "hel"}, {:slit, "lo"}}

    assert {:ok, [len]} = Parser.parse("def n : run Nat := strLen \"é\"\n")
    assert len.body == {:slen, {:slit, <<195, 169>>}}

    assert {:ok, [eq]} = Parser.parse("def yes : run WBool := strEq \"a\" \"a\"\n")
    assert eq.body == {:seq, {:slit, "a"}, {:slit, "a"}}

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\t\"\n")
    assert msg =~ "bad escape"

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\u\"\n")
    assert msg =~ "bad escape"

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\u{D800}\"\n")
    assert msg =~ "bad unicode scalar"

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\u{dfff}\"\n")
    assert msg =~ "bad unicode scalar"

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\u{}\"\n")
    assert msg =~ "bad unicode scalar"

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\u{110000}\"\n")
    assert msg =~ "bad unicode scalar"

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\u{0000041}\"\n")
    assert msg =~ "bad unicode scalar"

    assert {:error, msg} = Parser.parse("def bad : run String := \"\\u{41\"\n")
    assert msg =~ "unclosed unicode escape"

    assert {:error, msg} = Parser.parse("def bad : run String := \"a\nb\"\n")
    assert msg =~ "unclosed string"
  end

  test "an escaped quote is one string token" do
    src = "\"a\\\"b\""
    assert [{:string, 0, stop}] = Lexer.tokenize(src)
    assert stop == byte_size(src)

    slash = "\"a\\\\b\""
    assert [{:string, 0, stop}] = Lexer.tokenize(slash)
    assert stop == byte_size(slash)
  end

  test "a repr string and an import path keep a raw backslash" do
    assert {:ok, [imp, defn, repr]} =
             Parser.parse("""
             import "a\\\\b.muro"
             def core : run String := "a\\\\b"
             repr Box := map { "a\\\\b" => integer }
             """)

    assert imp.path == "a\\\\b.muro"
    assert defn.body == {:slit, "a\\b"}
    assert {:map, false, [{"a\\\\b", {:integer}}]} = repr.body
  end

  test "the worked book checks, and a string is not an atom" do
    assert Muro.check_file("examples/string.muro") == :ok

    assert {:error, msg} = check("def bad : run String := :hello\n")
    assert msg =~ "cannot convert Atom ≁ String"

    assert {:error, msg} = check("def bad : run Atom := \"hello\"\n")
    assert msg =~ "cannot convert String ≁ Atom"

    assert {:error, msg} = check("def bad : run String := String\n")
    assert msg =~ "no promotion: String is an erased term"

    assert {:error, msg} = check("def bad : run WBool := strEq :hello \"hello\"\n")
    assert msg =~ "cannot convert Atom ≁ String"

    assert {:error, msg} =
             check("""
             def bad : run Π (s : String) → String :=
               λ (s : String) → strCat s s
             """)

    assert msg =~ "affine variable used twice"

    assert check("def S : spec Type := String\n") == :ok

    assert {:error, msg} = check("session s := send String end\n")
    assert msg =~ "ill-formed payload"

    assert {:error, msg} = check("session s := send \"hello\" end\n")
    assert msg =~ "expected a payload"
  end

  test "Elixir emits a binary, and canon quotes it" do
    dir = tmp_dir()
    path = Path.join(dir, "strings.muro")
    File.cp!("examples/string.muro", path)

    mod = Module.concat(Muro.StringProbe, "M#{System.unique_integer([:positive])}")
    assert {:ok, src} = Muro.emit_file(path, mod)
    assert src =~ ":erlang.length(:unicode.characters_to_list("
    assert src =~ "<>"
    refute src =~ "String.length"

    [{^mod, _bin}] = Code.compile_string(src)

    on_exit(fn ->
      :code.delete(mod)
      :code.purge(mod)
    end)

    assert apply(mod, :hello, []) == "hello"
    assert apply(mod, :tag, []) == :hello
    assert apply(mod, :n, []) == 1
    assert apply(mod, :two, []) == 2
    assert apply(mod, :wave_n, []) == 1
    assert apply(mod, :nul_n, []) == 1
    assert apply(mod, :empty_n, []) == 0
    assert apply(mod, :yes, []) == true
    assert apply(mod, :no, []) == false
    assert apply(mod, :parts, []) == "hello"
    assert apply(mod, :nl, []) == "a\nb"
    assert apply(mod, :quoted, []) == "a\"b"
    assert apply(mod, :slash, []) == "a\\b"
    assert apply(mod, :nul, []) == <<0>>
    assert apply(mod, :accent, []) == "é"
    assert apply(mod, :twice, ["ab"]) == "abab"
    assert apply(mod, :twice, ["é"]) == "éé"
    assert Print.scalar_count(apply(mod, :wave, [])) == 1

    assert Print.quote_string("hello") == "\"hello\""
    assert Print.quote_string("a\nb") == "\"a\\nb\""
    assert Print.quote_string("a\"b") == "\"a\\\"b\""
    assert Print.quote_string("a\\b") == "\"a\\\\b\""
    assert Print.quote_string(<<0>>) == "\"\\u{0}\""
    assert Print.quote_string("hello") != "hello"
  end

  test "JavaScript boxes a string and leaves an atom as a string" do
    dir = tmp_dir()
    path = Path.join(dir, "string.muro")
    File.cp!("examples/string.muro", path)

    assert {:ok, [mjs, dts]} = Muro.emit_js(path)
    source = File.read!(mjs)
    types = File.read!(dts)

    assert source =~ "{ string: \"hello\" }"
    assert source =~ "return (\"hello\")"
    assert source =~ "Array.from(a.string)"
    assert source =~ "typeof v.string === \"string\""
    refute source =~ "c:string"

    assert types =~ "export type Atom = string;"
    assert types =~ "export type String = { readonly string: string };"
    assert types =~ "export function twice(s: String): String;"
    assert types =~ "export function tag(): Atom;"
    assert types =~ "export function hello(): String;"
  end

  test "C, Rust, Zig, and assembly refuse a string and keep evidence" do
    dir = tmp_dir()
    path = Path.join(dir, "string.muro")
    File.cp!("examples/string.muro", path)

    for backend <- ~w(c rust zig asm) do
      assert_raise Mix.Error, ~r/\Ac:string\z/, fn ->
        Mix.Tasks.Muro.Emit.run([path, "--backend", backend])
      end
    end

    evidence = Path.join(dir, "kept.muro")

    File.write!(evidence, """
    def n : run Nat := 0
    def accent_ok : evidence {strLen "é" ≡ suc 0 : Nat} := refl
    """)

    capture_io(fn -> Mix.Tasks.Muro.Emit.run([evidence, "--backend", "c"]) end)
    assert File.regular?(Path.join(dir, "kept.c"))

    body = Path.join(dir, "len.muro")
    File.write!(body, "def n : run Nat := strLen \"é\"\n")

    assert_raise Mix.Error, ~r/\Ac:string\z/, fn ->
      Mix.Tasks.Muro.Emit.run([body, "--backend", "c"])
    end
  end

  defp check(src) do
    path =
      Path.join(System.tmp_dir!(), "muro_string_#{System.unique_integer([:positive])}.muro")

    File.write!(path, src)
    on_exit(fn -> File.rm(path) end)
    Muro.check_file(path)
  end

  defp tmp_dir do
    dir = Path.join(System.tmp_dir!(), "muro_string_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end

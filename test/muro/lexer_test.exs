defmodule Muro.LexerTest do
  use ExUnit.Case, async: true

  alias Muro.{Lexer, MakeupLexer, Parser, Words}

  test "a book covers the source and keeps parser tokens" do
    src = File.read!("examples/half_ok.muro")
    tokens = Lexer.tokenize(src)

    assert cover(src, tokens) == src
    assert {:ok, _} = Parser.parse(src)
    assert [:declaration] = kinds(src, tokens, "def") |> Enum.uniq()
    assert [:type] = kinds(src, tokens, "run") |> Enum.uniq()
    assert [:type] = kinds(src, tokens, "spec") |> Enum.uniq()
    assert [:type] = kinds(src, tokens, "evidence") |> Enum.uniq()
    assert :type in Enum.map(tokens, &elem(&1, 0))
    assert :comment in Enum.map(tokens, &elem(&1, 0))
    refute :text in Enum.map(tokens, &elem(&1, 0))
  end

  test "a fragment that is not a book still yields spans" do
    src = "(+ n : Nat) →"
    assert {:error, _} = Parser.parse(src)

    tokens = Lexer.tokenize(src)
    assert cover(src, tokens) == src

    assert tokens == [
             {:punctuation, 0, 1},
             {:operator, 1, 2},
             {:whitespace, 2, 3},
             {:name, 3, 4},
             {:whitespace, 4, 5},
             {:punctuation, 5, 6},
             {:whitespace, 6, 7},
             {:type, 7, 10},
             {:punctuation, 10, 11},
             {:whitespace, 11, 12},
             {:operator, 12, byte_size(src)}
           ]
  end

  test "keywords are not prefixes of names" do
    src = "default runtime internal inc matchEmpty"
    tokens = Lexer.tokenize(src)

    assert Enum.map(tokens, fn {kind, a, b} -> {kind, binary_part(src, a, b - a)} end) == [
             {:name, "default"},
             {:whitespace, " "},
             {:name, "runtime"},
             {:whitespace, " "},
             {:type, "internal"},
             {:whitespace, " "},
             {:name, "inc"},
             {:whitespace, " "},
             {:keyword, "matchEmpty"}
           ]
  end

  test "operators and comments follow the parser" do
    src = "n := 0 -- a comment\n-> => :: == ~"
    tokens = Lexer.tokenize(src)

    assert Enum.map(tokens, fn {kind, a, b} -> {kind, binary_part(src, a, b - a)} end) == [
             {:name, "n"},
             {:whitespace, " "},
             {:operator, ":="},
             {:whitespace, " "},
             {:number, "0"},
             {:whitespace, " "},
             {:comment, "-- a comment"},
             {:whitespace, "\n"},
             {:operator, "->"},
             {:whitespace, " "},
             {:operator, "=>"},
             {:whitespace, " "},
             {:operator, "::"},
             {:whitespace, " "},
             {:operator, "=="},
             {:whitespace, " "},
             {:operator, "~"}
           ]
  end

  test "unicode binders and an unknown codepoint are covered" do
    src = "λ (n : Nat) → @@"
    tokens = Lexer.tokenize(src)
    assert cover(src, tokens) == src
    lam = byte_size("λ")
    assert {:operator, 0, ^lam} = hd(tokens)

    {kind, start, stop} = List.last(tokens)
    assert kind == :text
    assert binary_part(src, start, stop - start) == "@"
  end

  test "an apostrophe stays inside a name" do
    src = "n'"
    assert Lexer.tokenize(src) == [{:name, 0, 2}]
  end

  test "nil is one keyword" do
    assert Lexer.tokenize("[]") == [{:keyword, 0, 2}]
  end

  test "? is punctuation" do
    assert Lexer.tokenize("?") == [{:punctuation, 0, 1}]
  end

  test "a string is one token and stops at a newline" do
    assert Lexer.tokenize(~s("ab")) == [{:string, 0, 4}]

    tokens = Lexer.tokenize("\"ab\n")
    assert Enum.map(tokens, &elem(&1, 0)) == [:string, :whitespace]
    refute :text in Enum.map(tokens, &elem(&1, 0))
  end

  test "%0 and %1 are whole tokens" do
    assert Lexer.tokenize("%0") == [{:operator, 0, 2}]
    assert Lexer.tokenize("%1") == [{:operator, 0, 2}]

    assert Enum.map(Lexer.tokenize("%10"), fn {kind, a, b} ->
             {kind, binary_part("%10", a, b - a)}
           end) == [
             {:punctuation, "%"},
             {:number, "10"}
           ]
  end

  test "an arrow does not continue a name" do
    src = "Nat->Nat"

    assert Enum.map(Lexer.tokenize(src), fn {kind, a, b} -> {kind, binary_part(src, a, b - a)} end) ==
             [
               {:type, "Nat"},
               {:operator, "->"},
               {:type, "Nat"}
             ]
  end

  test "the name after a declaration is a defined name" do
    src = "def plus"

    assert Enum.map(Lexer.tokenize(src), fn {kind, a, b} -> {kind, binary_part(src, a, b - a)} end) ==
             [
               {:declaration, "def"},
               {:whitespace, " "},
               {:function, "plus"}
             ]
  end

  test "every lexicon word and every operator has its kind" do
    for {word, kind} <- Words.lexicon() do
      assert [{^kind, 0, _}] = Lexer.tokenize(word), word
    end

    for op <- Words.operators() do
      assert [{:operator, 0, _}] = Lexer.tokenize(op), op
    end

    assert [{:keyword, 0, 2}] = Lexer.tokenize(Words.nil_token())

    for mult <- Words.mult_tokens() do
      assert [{:operator, 0, 2}] = Lexer.tokenize(mult), mult
    end
  end

  test "parser words are the lexicon, aside from numerals and operators" do
    src = File.read!("lib/muro/parser.ex")

    words =
      Regex.scan(~r/(?<![\w.])(?:word_kw\?|kw)\([^,\n]*,\s*"([^"]*)"/, src)
      |> Enum.map(fn [_, word] -> word end)
      |> Enum.uniq()

    known =
      MapSet.new(Enum.map(Words.lexicon(), &elem(&1, 0)))
      |> MapSet.union(MapSet.new(Words.operators()))
      |> MapSet.put(Words.nil_token())

    missing = Enum.reject(words, &(&1 == "0" or MapSet.member?(known, &1)))
    assert missing == []
  end

  test "examples and the prelude lex without an error token" do
    files =
      Path.wildcard("examples/**/*.muro") ++
        Path.wildcard("lib/muro/std/**/*.muro") ++
        ["lib/muro/prelude.muro"]

    assert files != []

    for path <- files do
      src = File.read!(path)
      tokens = Lexer.tokenize(src)
      assert cover(src, tokens) == src, path
      refute Enum.any?(tokens, &(elem(&1, 0) == :text)), path

      tagged = MakeupLexer.lex(src)

      assert Enum.map_join(tagged, fn {_tag, _meta, text} -> IO.iodata_to_binary(text) end) ==
               src

      refute Enum.any?(tagged, fn {tag, _, _} -> tag == :error end), path
    end
  end

  test "a definition records the bytes the parser consumed" do
    src = File.read!("examples/value-protocols.muro")
    assert {:ok, book} = Parser.parse(src)
    late = Enum.find(book, &(&1[:name] == "late"))
    assert {a, b} = late.extent
    slice = binary_part(src, a, b - a)
    assert String.starts_with?(slice, "def late")
    assert slice =~ "headers => false"
    refute slice =~ "def as-bytes"
  end

  test "makeup tags are the slices of the source" do
    src = "def plus : run Nat := 0"
    tagged = MakeupLexer.lex(src)

    assert Enum.map_join(tagged, fn {_tag, _meta, text} -> text end) == src

    assert Enum.map(tagged, fn {tag, _meta, text} -> {tag, IO.iodata_to_binary(text)} end) == [
             {:keyword_declaration, "def"},
             {:whitespace, " "},
             {:name_function, "plus"},
             {:whitespace, " "},
             {:punctuation, ":"},
             {:whitespace, " "},
             {:keyword_type, "run"},
             {:whitespace, " "},
             {:keyword_type, "Nat"},
             {:whitespace, " "},
             {:operator, ":="},
             {:whitespace, " "},
             {:number_integer, "0"}
           ]
  end

  test "muro is registered with Makeup" do
    assert {:ok, {Muro.MakeupLexer, []}} = Makeup.Registry.fetch_lexer_by_name("muro")
    assert {:ok, {Muro.MakeupLexer, []}} = Makeup.Registry.fetch_lexer_by_extension("muro")

    html = Makeup.highlight_inner_html("def plus : run", lexer: "muro")
    assert html =~ ~s(<span class="kd">def</span>)
    assert html =~ ~s(<span class="kt">run</span>)
    assert html =~ ~s(<span class="nf">plus</span>)
  end

  defp cover(src, tokens) do
    Enum.map_join(tokens, fn {_kind, start, stop} -> binary_part(src, start, stop - start) end)
  end

  defp kinds(src, tokens, text) do
    for {kind, start, stop} <- tokens, binary_part(src, start, stop - start) == text, do: kind
  end
end

defmodule Muro.Lexer do
  @moduledoc """
  Fragment lexer for highlighting.

  `Muro.Parser.parse/1` accepts a whole book and records `line:col` on
  definitions and holes. A manual
  snippet is often not a book, so highlighting cannot call it. This lexer
  uses the same lexical rules as the parser (whitespace, `--` comments,
  word-bounded keywords, identifiers) and always returns a cover of the
  source. Joining the slices gives the input back.

  Offsets are UTF-8 byte offsets, half-open: `{kind, start, stop}`.
  """

  @type kind ::
          :whitespace
          | :comment
          | :keyword
          | :tag
          | :builtin
          | :operator
          | :punctuation
          | :name
          | :number
          | :text

  @type token :: {kind, non_neg_integer, non_neg_integer}

  # Longest first. `match` is a prefix of `matchEmpty`; `in` is a prefix of
  # `internal`, and the word boundary keeps them apart.
  @keywords [
    "matchEmpty",
    "rewrite",
    "unfold",
    "motive",
    "where",
    "match",
    "data",
    "lam",
    "let",
    "def",
    "Pi",
    "nu",
    "in"
  ]

  @sigils ["λ", "Π", "ν"]

  @tags ["evidence", "internal", "spec", "run"]

  @builtins [
    "uncons",
    "Tensor",
    "Always",
    "Stream",
    "Empty",
    "packI",
    "toI64",
    "Unit",
    "Type",
    "bisim",
    "addi",
    "muli",
    "addt",
    "head",
    "tail",
    "refl",
    "Atom",
    "Nat",
    "I64",
    "F32",
    "fst",
    "snd",
    "suc",
    "tt"
  ]

  @operators [":=", "->", "=>", "::", "==", "→", "×", "⊎", "≡"]

  @spec tokenize(String.t()) :: [token]
  def tokenize(source) when is_binary(source) do
    tokenize(source, 0, [])
  end

  defp tokenize(<<>>, _offset, acc), do: Enum.reverse(acc)

  defp tokenize(rest, offset, acc) do
    {kind, len} = next(rest)

    tokenize(:binary.part(rest, len, byte_size(rest) - len), offset + len, [
      {kind, offset, offset + len} | acc
    ])
  end

  defp next(src) do
    cond do
      tok = take_ws(src) -> tok
      tok = take_comment(src) -> tok
      tok = take_nil(src) -> tok
      tok = match_prefix(src, @operators, :operator) -> tok
      tok = match_prefix(src, @sigils, :keyword) -> tok
      tok = match_word(src, @keywords, :keyword) -> tok
      tok = match_word(src, @tags, :tag) -> tok
      tok = match_word(src, @builtins, :builtin) -> tok
      tok = take_ident(src) -> tok
      tok = take_number(src) -> tok
      tok = take_mark(src) -> tok
      true -> take_text(src)
    end
  end

  defp take_ws(src), do: take_ws(src, 0)

  defp take_ws(<<c, rest::binary>>, n) when c in [?\s, ?\n, ?\t, ?\r], do: take_ws(rest, n + 1)
  defp take_ws(_, 0), do: nil
  defp take_ws(_, n), do: {:whitespace, n}

  defp take_comment(<<"--", rest::binary>>), do: {:comment, 2 + comment_rest(rest)}
  defp take_comment(_), do: nil

  defp comment_rest(<<"\n", _::binary>>), do: 0
  defp comment_rest(<<_, rest::binary>>), do: 1 + comment_rest(rest)
  defp comment_rest(<<>>), do: 0

  defp take_nil("[]" <> _), do: {:builtin, 2}
  defp take_nil(_), do: nil

  defp match_prefix(src, [word | words], kind) do
    if String.starts_with?(src, word) do
      {kind, byte_size(word)}
    else
      match_prefix(src, words, kind)
    end
  end

  defp match_prefix(_src, [], _kind), do: nil

  defp match_word(src, [word | words], kind) do
    if bounded?(src, word) do
      {kind, byte_size(word)}
    else
      match_word(src, words, kind)
    end
  end

  defp match_word(_src, [], _kind), do: nil

  defp bounded?(src, word) do
    n = byte_size(word)

    case src do
      <<^word::binary-size(^n), rest::binary>> -> not continues?(rest)
      _ -> false
    end
  end

  defp continues?(<<c, _::binary>>)
       when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ or c == ?- or c == ?',
       do: true

  defp continues?(_), do: false

  defp take_ident(<<c, rest::binary>>) when c in ?a..?z or c in ?A..?Z or c == ?_ do
    {:name, 1 + ident_rest(rest)}
  end

  defp take_ident(_), do: nil

  defp ident_rest(<<c, rest::binary>>)
       when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ or c == ?- or c == ?' do
    1 + ident_rest(rest)
  end

  defp ident_rest(_), do: 0

  defp take_number(<<c, rest::binary>>) when c in ?0..?9, do: {:number, 1 + digits(rest)}
  defp take_number(_), do: nil

  defp digits(<<c, rest::binary>>) when c in ?0..?9, do: 1 + digits(rest)
  defp digits(_), do: 0

  defp take_mark(<<c, _::binary>>) when c in ~c"(){}[]|,:+-*=~?", do: mark_kind(c)
  defp take_mark(_), do: nil

  defp mark_kind(c) when c in ~c"+-*=~", do: {:operator, 1}
  defp mark_kind(_c), do: {:punctuation, 1}

  defp take_text(src) do
    {cp, _} = String.next_codepoint(src)
    {:text, byte_size(cp)}
  end
end

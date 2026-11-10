defmodule Muro.Lexer do
  @moduledoc """
  Fragment lexer for highlighting.

  `Muro.Parser.parse/1` accepts a whole book and records `line:col` on
  definitions and holes. A manual snippet is often not a book, so
  highlighting cannot call it. This lexer uses the same lexical rules
  as the parser (whitespace, `--` comments, strings, word-bounded
  keywords from `Muro.Words`, identifiers) and always returns a cover
  of the source. Joining the slices gives the input back.

  A keyword is classified in every position. The parser still decides
  where that word is actually reserved. Offsets are UTF-8 byte offsets,
  half-open: `{kind, start, stop}`. Whitespace is its own token.
  """

  @type kind ::
          :whitespace
          | :comment
          | :string
          | :declaration
          | :keyword
          | :type
          | :operator
          | :punctuation
          | :name
          | :function
          | :number
          | :text

  @type token :: {kind, non_neg_integer, non_neg_integer}

  @words Muro.Words.lexicon() |> Enum.sort_by(fn {word, _kind} -> byte_size(word) end, :desc)
  @operators Muro.Words.symbolic_operators()
  @nil_token Muro.Words.nil_token()

  @spec tokenize(String.t()) :: [token]
  def tokenize(source) when is_binary(source) do
    source
    |> scan(0, [])
    |> name_defined(source, false)
  end

  defp scan(<<>>, _offset, acc), do: Enum.reverse(acc)

  defp scan(rest, offset, acc) do
    {kind, len} = next(rest)

    scan(:binary.part(rest, len, byte_size(rest) - len), offset + len, [
      {kind, offset, offset + len} | acc
    ])
  end

  defp next(src) do
    cond do
      tok = take_ws(src) -> tok
      tok = take_comment(src) -> tok
      tok = take_string(src) -> tok
      tok = take_nil(src) -> tok
      tok = take_mult(src) -> tok
      tok = match_prefix(src, @operators, :operator) -> tok
      tok = match_word(src, @words) -> tok
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

  defp take_string(<<"\"", rest::binary>>), do: {:string, 1 + string_rest(rest)}
  defp take_string(_), do: nil

  defp string_rest(<<"\\\"", rest::binary>>), do: 2 + string_rest(rest)
  defp string_rest(<<"\\\\", rest::binary>>), do: 2 + string_rest(rest)
  defp string_rest(<<"\"", _::binary>>), do: 1
  defp string_rest(<<"\n", _::binary>>), do: 0
  defp string_rest(<<>>), do: 0
  defp string_rest(<<_, rest::binary>>), do: 1 + string_rest(rest)

  defp take_nil(src) do
    token = @nil_token
    n = byte_size(token)
    if byte_size(src) >= n and binary_part(src, 0, n) == token, do: {:keyword, n}
  end

  defp take_mult(<<"%0", rest::binary>>) do
    if continues?(rest), do: nil, else: {:operator, 2}
  end

  defp take_mult(<<"%1", rest::binary>>) do
    if continues?(rest), do: nil, else: {:operator, 2}
  end

  defp take_mult(_), do: nil

  defp match_prefix(src, [word | words], kind) do
    n = byte_size(word)

    if byte_size(src) >= n and binary_part(src, 0, n) == word do
      {kind, n}
    else
      match_prefix(src, words, kind)
    end
  end

  defp match_prefix(_src, [], _kind), do: nil

  defp match_word(src, [{word, kind} | words]) do
    if bounded?(src, word) do
      {kind, byte_size(word)}
    else
      match_word(src, words)
    end
  end

  defp match_word(_src, []), do: nil

  defp bounded?(src, word) do
    n = byte_size(word)

    byte_size(src) >= n and binary_part(src, 0, n) == word and
      not continues?(binary_part(src, n, byte_size(src) - n))
  end

  # `->` closes a word. `Nat->Nat` is Nat, ->, Nat. A hyphen otherwise
  # stays inside the word, matching `Muro.Parser`.
  defp continues?(<<"->", _::binary>>), do: false

  defp continues?(<<c, _::binary>>)
       when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ or c == ?- or c == ?',
       do: true

  defp continues?(_), do: false

  defp take_ident(<<c, rest::binary>>) when c in ?a..?z or c in ?A..?Z or c == ?_ do
    {:name, 1 + ident_rest(rest)}
  end

  defp take_ident(_), do: nil

  defp ident_rest(<<"->", _::binary>>), do: 0

  defp ident_rest(<<c, rest::binary>>)
       when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ or c == ?- or c == ?' do
    1 + ident_rest(rest)
  end

  defp ident_rest(_), do: 0

  defp take_number(<<c, rest::binary>>) when c in ?0..?9, do: {:number, 1 + digits(rest)}
  defp take_number(_), do: nil

  defp digits(<<c, rest::binary>>) when c in ?0..?9, do: 1 + digits(rest)
  defp digits(_), do: 0

  defp take_mark(<<c, _::binary>>) when c in ~c"(){}[]|,.:?%", do: {:punctuation, 1}
  defp take_mark(<<c, _::binary>>) when c in ~c"+-*=~", do: {:operator, 1}
  defp take_mark(_), do: nil

  defp take_text(src) do
    {cp, _} = String.next_codepoint(src)
    {:text, byte_size(cp)}
  end

  defp name_defined([], _src, _armed), do: []

  defp name_defined([{:whitespace, _, _} = tok | rest], src, armed) do
    [tok | name_defined(rest, src, armed)]
  end

  defp name_defined([{:declaration, a, b} = tok | rest], src, _armed) do
    word = binary_part(src, a, b - a)
    [tok | name_defined(rest, src, Muro.Words.naming?(word))]
  end

  defp name_defined([{:name, a, b} | rest], src, true) do
    [{:function, a, b} | name_defined(rest, src, false)]
  end

  defp name_defined([tok | rest], src, _armed) do
    [tok | name_defined(rest, src, false)]
  end
end

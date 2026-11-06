defmodule Muro.Deps.Hex.JSON do
  @moduledoc """
  A small JSON decoder for the Hex release list.

  Elixir's `JSON` module is absent before 1.18. `Muro.Deps.Hex.Http`
  uses `JSON` when it is loaded and this decoder otherwise. The
  decoder accepts objects, arrays, strings, numbers, `true`, `false`,
  and `null`.
  """

  @doc "`{:ok, term}` or `{:error, message}`."
  def decode(bin) when is_binary(bin) do
    case value(skip(bin)) do
      {:ok, term, rest} ->
        if skip(rest) == "" do
          {:ok, term}
        else
          {:error, "trailing JSON"}
        end

      {:error, message} ->
        {:error, message}
    end
  end

  defp value("null" <> rest), do: {:ok, nil, rest}
  defp value("true" <> rest), do: {:ok, true, rest}
  defp value("false" <> rest), do: {:ok, false, rest}
  defp value("{" <> rest), do: object(skip(rest))
  defp value("[" <> rest), do: array(skip(rest))
  defp value("\"" <> rest), do: string(rest, "")

  defp value(<<char, _rest::binary>> = bin) when char == ?- or (char >= ?0 and char <= ?9) do
    number(bin)
  end

  defp value(_other), do: {:error, "invalid JSON"}

  defp object("}" <> rest), do: {:ok, %{}, rest}
  defp object(bin), do: pairs(bin, %{})

  defp pairs(bin, acc) do
    case key_and_value(bin) do
      {:ok, key, val, rest} ->
        acc = Map.put(acc, key, val)

        case skip(rest) do
          "," <> rest -> pairs(skip(rest), acc)
          "}" <> rest -> {:ok, acc, rest}
          _other -> {:error, "bad JSON object"}
        end

      {:error, message} ->
        {:error, message}
    end
  end

  defp key_and_value(bin) do
    case value(skip(bin)) do
      {:ok, key, rest} when is_binary(key) ->
        case skip(rest) do
          ":" <> rest ->
            case value(skip(rest)) do
              {:ok, val, rest} -> {:ok, key, val, rest}
              {:error, message} -> {:error, message}
            end

          _other ->
            {:error, "bad JSON object"}
        end

      {:ok, _key, _rest} ->
        {:error, "JSON object key is not a string"}

      {:error, message} ->
        {:error, message}
    end
  end

  defp array("]" <> rest), do: {:ok, [], rest}
  defp array(bin), do: elements(bin, [])

  defp elements(bin, acc) do
    case value(skip(bin)) do
      {:ok, el, rest} ->
        acc = acc ++ [el]

        case skip(rest) do
          "," <> rest -> elements(skip(rest), acc)
          "]" <> rest -> {:ok, acc, rest}
          _other -> {:error, "bad JSON array"}
        end

      {:error, message} ->
        {:error, message}
    end
  end

  defp string("\"" <> rest, acc), do: {:ok, acc, rest}
  defp string("\\" <> rest, acc), do: escape(rest, acc)

  defp string(<<char::utf8, rest::binary>>, acc) when char >= 0x20 do
    string(rest, acc <> <<char::utf8>>)
  end

  defp string(_other, _acc), do: {:error, "bad JSON string"}

  defp escape("\"" <> rest, acc), do: string(rest, acc <> "\"")
  defp escape("\\" <> rest, acc), do: string(rest, acc <> "\\")
  defp escape("/" <> rest, acc), do: string(rest, acc <> "/")
  defp escape("b" <> rest, acc), do: string(rest, acc <> "\b")
  defp escape("f" <> rest, acc), do: string(rest, acc <> "\f")
  defp escape("n" <> rest, acc), do: string(rest, acc <> "\n")
  defp escape("r" <> rest, acc), do: string(rest, acc <> "\r")
  defp escape("t" <> rest, acc), do: string(rest, acc <> "\t")

  defp escape(<<"u", hex::binary-size(4), rest::binary>>, acc) do
    case Integer.parse(hex, 16) do
      {code, ""} when code < 0xD800 or code > 0xDFFF ->
        string(rest, acc <> <<code::utf8>>)

      _other ->
        {:error, "bad JSON string"}
    end
  end

  defp escape(_other, _acc), do: {:error, "bad JSON string"}

  defp number(bin) do
    {text, rest} = take_number(bin, "")

    cond do
      text == "" or text == "-" ->
        {:error, "bad JSON number"}

      String.contains?(text, ".") or String.contains?(text, "e") or String.contains?(text, "E") ->
        case Float.parse(text) do
          {n, ""} -> {:ok, n, rest}
          _other -> {:error, "bad JSON number"}
        end

      true ->
        case Integer.parse(text) do
          {n, ""} -> {:ok, n, rest}
          _other -> {:error, "bad JSON number"}
        end
    end
  end

  defp take_number(<<char, rest::binary>>, acc)
       when char in ~c"-+.eE0123456789" do
    take_number(rest, acc <> <<char>>)
  end

  defp take_number(rest, acc), do: {acc, rest}

  defp skip(<<char, rest::binary>>) when char in [?\s, ?\n, ?\r, ?\t], do: skip(rest)
  defp skip(rest), do: rest
end

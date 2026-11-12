defmodule Muro.Bytes do
  @moduledoc """
  Operations on a raw octet sequence.

  A `Bytes` value and a `Slice` view are the same binary while the
  checker is reducing a closed term. A backend emits that binary as a
  pointer and a length. These functions are the reductions the checker
  and the Elixir backend share.
  """

  @doc "Octet length."
  def len(bin) when is_binary(bin), do: byte_size(bin)

  @doc "Octet-wise equality."
  def eq(a, b) when is_binary(a) and is_binary(b), do: a == b

  @doc "Concatenate. The result is one binary of the combined length."
  def cat(a, b) when is_binary(a) and is_binary(b), do: a <> b

  @doc """
  The `len` octets at `off`. Out of range, including a negative, is empty.
  An empty in-range view is empty and is not a copy of the whole binary.
  """
  def sub(bin, off, len) when is_binary(bin) and is_integer(off) and is_integer(len) do
    n = byte_size(bin)

    if off < 0 or len < 0 or off > n or len > n - off do
      ""
    else
      binary_part(bin, off, len)
    end
  end

  @doc "The octet at `i`, or `:none`."
  def get(bin, i) when is_binary(bin) and is_integer(i) do
    if i >= 0 and i < byte_size(bin), do: {:some, :binary.at(bin, i)}, else: :none
  end

  @doc "The first octet and the leftover view, or `:nothing`."
  def uncons(<<>>), do: :nothing
  def uncons(<<b, rest::binary>>), do: {:just, b, rest}

  @doc "The prefix before the first `byte`, or the whole binary when it is absent."
  def until(bin, byte) when is_binary(bin) and is_integer(byte) and byte >= 0 and byte <= 255 do
    case :binary.match(bin, <<byte>>) do
      :nomatch -> bin
      {pos, _} -> binary_part(bin, 0, pos)
    end
  end

  @doc "The suffix strictly after the first `byte`, or empty when it is absent."
  def aft(bin, byte) when is_binary(bin) and is_integer(byte) and byte >= 0 and byte <= 255 do
    case :binary.match(bin, <<byte>>) do
      :nomatch -> ""
      {pos, 1} -> binary_part(bin, pos + 1, byte_size(bin) - pos - 1)
    end
  end

  @doc "A closed `U64` literal, or `:open`."
  def u64_of({:word, {:lit, :u64, n}, []}) when is_integer(n) and n >= 0, do: {:ok, n}
  def u64_of(_), do: :open

  @doc "A closed `U8` literal, or `:open`."
  def u8_of({:word, {:lit, :u8, n}, []}) when is_integer(n) and n >= 0 and n <= 255, do: {:ok, n}
  def u8_of(_), do: :open

  @doc """
  A bytes literal. Printable ASCII is itself. `\\\\`, `\\\"`, `\\n`,
  `\\r`, and `\\t` are escaped. Every other octet, including DEL and
  any byte at least `80₁₆`, is `\\xHH`.
  """
  def quote_bytes(bin) when is_binary(bin) do
    body = for <<b <- bin>>, into: "", do: quote_byte(b)
    "b\"" <> body <> "\""
  end

  defp quote_byte(?\\), do: "\\\\"
  defp quote_byte(?"), do: "\\\""
  defp quote_byte(?\n), do: "\\n"
  defp quote_byte(?\r), do: "\\r"
  defp quote_byte(?\t), do: "\\t"
  defp quote_byte(b) when b >= 0x20 and b <= 0x7E, do: <<b>>

  defp quote_byte(b) do
    "\\x" <> String.pad_leading(Integer.to_string(b, 16) |> String.downcase(), 2, "0")
  end
end

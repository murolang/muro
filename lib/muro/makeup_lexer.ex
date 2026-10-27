defmodule Muro.MakeupLexer do
  @moduledoc """
  Makeup adapter for `Muro.Lexer`.

  The lexer owns the spans. This module only maps a kind onto a Makeup tag
  and slices the source. It does not emit HTML. Callers that want color
  (the landing site, ExDoc) style the tags.

  Registered as the language name `"muro"` and the extension `"muro"` when
  the Muro application starts and Makeup is loaded.
  """

  if Code.ensure_loaded?(Makeup.Lexer) do
    @behaviour Makeup.Lexer
  end

  @spec lex(String.t(), list()) :: [{atom(), map(), iodata()}]
  def lex(source, opts \\ []) when is_binary(source) do
    source
    |> tokens()
    |> postprocess(opts)
    |> match_groups(opts[:group_prefix] || "")
  end

  def root(source) when is_binary(source) do
    {:ok, lex(source, []), "", %{}, {1, 1}, byte_size(source)}
  end

  def root_element(source) when is_binary(source) do
    case Muro.Lexer.tokenize(source) do
      [] ->
        {:error, "empty", source, %{}, {1, 1}, 0}

      [{kind, start, stop} | _] ->
        text = :binary.part(source, start, stop - start)
        rest = :binary.part(source, stop, byte_size(source) - stop)
        {:ok, [{tag(kind), %{}, text}], rest, %{}, {1, 1}, stop}
    end
  end

  def postprocess(tokens, _opts), do: tokens

  def match_groups(tokens, _group_prefix), do: tokens

  defp tokens(source) do
    Enum.map(Muro.Lexer.tokenize(source), fn {kind, start, stop} ->
      {tag(kind), %{}, :binary.part(source, start, stop - start)}
    end)
  end

  defp tag(:whitespace), do: :whitespace
  defp tag(:comment), do: :comment
  defp tag(:keyword), do: :keyword
  defp tag(:tag), do: :keyword_type
  defp tag(:builtin), do: :name_builtin
  defp tag(:operator), do: :operator
  defp tag(:punctuation), do: :punctuation
  defp tag(:name), do: :name
  defp tag(:number), do: :number_integer
  defp tag(:text), do: :error
end

defmodule Muro.Diff do
  @moduledoc false

  @context 3

  @doc "Unified diff of two texts. `path` is the label, not a file read."
  def unified(path, old, new) when is_binary(path) and is_binary(old) and is_binary(new) do
    old_lines = lines(old)
    new_lines = lines(new)
    ops = script(old_lines, new_lines)
    "--- a/#{path}\n+++ b/#{path}\n" <> hunks(ops)
  end

  defp lines(text) do
    case String.split(text, "\n") do
      [""] ->
        []

      parts ->
        if String.ends_with?(text, "\n"), do: Enum.drop(parts, -1), else: parts
    end
  end

  defp script(old, new) do
    a = List.to_tuple(old)
    b = List.to_tuple(new)
    m = tuple_size(a)
    n = tuple_size(b)
    dp = fill(a, b, m, n, %{})
    edits(dp, a, b, m, n, [])
  end

  defp edits(_dp, _a, _b, 0, 0, acc), do: acc

  defp edits(dp, a, b, i, j, acc) when i > 0 and j > 0 and elem(a, i - 1) == elem(b, j - 1) do
    edits(dp, a, b, i - 1, j - 1, [{:eq, elem(a, i - 1)} | acc])
  end

  defp edits(dp, a, b, i, j, acc) when i > 0 do
    if j == 0 or Map.get(dp, {i - 1, j}) >= Map.get(dp, {i, j - 1}) do
      edits(dp, a, b, i - 1, j, [{:del, elem(a, i - 1)} | acc])
    else
      edits(dp, a, b, i, j - 1, [{:ins, elem(b, j - 1)} | acc])
    end
  end

  defp edits(dp, a, b, i, j, acc) when j > 0 do
    edits(dp, a, b, i, j - 1, [{:ins, elem(b, j - 1)} | acc])
  end

  defp fill(a, b, m, n, _dp) do
    Enum.reduce(0..m, %{}, fn i, dp ->
      Enum.reduce(0..n, dp, fn j, dp ->
        cond do
          i == 0 or j == 0 ->
            Map.put(dp, {i, j}, 0)

          elem(a, i - 1) == elem(b, j - 1) ->
            Map.put(dp, {i, j}, Map.get(dp, {i - 1, j - 1}) + 1)

          true ->
            Map.put(dp, {i, j}, max(Map.get(dp, {i - 1, j}), Map.get(dp, {i, j - 1})))
        end
      end)
    end)
  end

  defp hunks(ops) do
    ops
    |> change_ranges()
    |> Enum.map_join(fn {from, to} -> format_range(ops, from, to) end)
  end

  defp change_ranges(ops) do
    last = length(ops) - 1

    ops
    |> Enum.with_index()
    |> Enum.flat_map(fn
      {{:eq, _line}, _index} -> []
      {_op, index} -> [index]
    end)
    |> Enum.map(fn index -> {max(index - @context, 0), min(index + @context, last)} end)
    |> merge_ranges([])
  end

  defp merge_ranges([], acc), do: Enum.reverse(acc)

  defp merge_ranges([{from, to} | rest], []), do: merge_ranges(rest, [{from, to}])

  defp merge_ranges([{from, to} | rest], [{prev_from, prev_to} | acc]) do
    if from <= prev_to + 1 do
      merge_ranges(rest, [{prev_from, max(prev_to, to)} | acc])
    else
      merge_ranges(rest, [{from, to}, {prev_from, prev_to} | acc])
    end
  end

  defp format_range(ops, from, to) do
    slice = Enum.slice(ops, from, to - from + 1)
    before = Enum.take(ops, from)
    old_count = count(slice, [:eq, :del])
    new_count = count(slice, [:eq, :ins])
    old_start = if(old_count == 0, do: 0, else: count(before, [:eq, :del]) + 1)
    new_start = if(new_count == 0, do: 0, else: count(before, [:eq, :ins]) + 1)

    header = "@@ -#{range(old_start, old_count)} +#{range(new_start, new_count)} @@\n"

    body =
      Enum.map_join(slice, fn
        {:eq, line} -> " " <> line <> "\n"
        {:del, line} -> "-" <> line <> "\n"
        {:ins, line} -> "+" <> line <> "\n"
      end)

    header <> body
  end

  defp count(ops, kinds) do
    Enum.count(ops, fn {op, _line} -> op in kinds end)
  end

  defp range(_start, 0), do: "0,0"
  defp range(start, 1), do: Integer.to_string(start)
  defp range(start, count), do: "#{start},#{count}"
end

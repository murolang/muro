defmodule MuroVisor.Detail do
  @moduledoc false

  def empty, do: %{title: "", loc: "", kind: ""}

  @doc """
  Source location for a node, a configuration, or an edge.

  An edge is re-checked with `Muro.Explore.out_of_order/2`. The kind is
  that refusal. A use that cannot be moved says `no refusal`. A node
  has no refusal.
  """
  def lookup(%{nodes: nodes, edges: edges}, book, id) when is_binary(id) do
    cond do
      node = Enum.find(nodes, &(&1.id == id)) ->
        %{title: node.name, loc: show_at(node.file, node.loc), kind: ""}

      edge = Enum.find(edges, &(&1.id == id)) ->
        refusal = Muro.Explore.out_of_order(book, edge)

        %{
          title: title(edge),
          loc: show_at(file_of(nodes, edge.from), Map.get(refusal, :loc) || edge.loc),
          kind: refusal_kind(refusal)
        }

      child = find_child(nodes, id) ->
        %{title: child.meeting, loc: show(child.loc), kind: ""}

      true ->
        empty()
    end
  end

  defp find_child(nodes, id) do
    Enum.find_value(nodes, fn node ->
      Enum.find(node.children, &(&1.id == id))
    end)
  end

  defp file_of(nodes, id) do
    case Enum.find(nodes, &(&1.id == id)) do
      %{file: file} when is_binary(file) -> file
      _ -> nil
    end
  end

  defp title(%{use: :step, step: step, proc: proc}) when is_integer(step),
    do: "step #{step} #{proc}"

  defp title(%{use: :step, step: step, proc: proc}), do: "step #{inspect(step)} #{proc}"
  defp title(%{use: use}), do: to_string(use)

  defp refusal_kind(%{kind: :not_a_step}), do: "no refusal"

  defp refusal_kind(%{kind: :refused, proc: proc, proto: proto} = refusal)
       when not is_nil(proc) and not is_nil(proto) do
    text =
      "refused: #{Muro.Session.show_proc(proc)} does not conform to #{Muro.Session.show_proto(proto)}"

    case Map.get(refusal, :reason) do
      reason when is_binary(reason) and reason != "" -> text <> ": #{reason}"
      _ -> text
    end
  end

  defp refusal_kind(%{kind: kind, reason: reason}) when is_binary(reason) and reason != "",
    do: "#{kind}: #{reason}"

  defp refusal_kind(%{kind: kind}), do: to_string(kind)

  defp show_at(file, {line, col}) when is_integer(line) and is_integer(col) do
    case file do
      f when is_binary(f) -> "#{f}:#{line}:#{col}"
      _ -> "#{line}:#{col}"
    end
  end

  defp show_at(_file, {file, line, col})
       when is_binary(file) and is_integer(line) and is_integer(col),
       do: "#{file}:#{line}:#{col}"

  defp show_at(file, %{at: at}), do: show_at(file, at)
  defp show_at(_file, other), do: show(other)

  def show(nil), do: ""
  def show({line, col}) when is_integer(line) and is_integer(col), do: "#{line}:#{col}"

  def show({file, line, col}) when is_binary(file) and is_integer(line) and is_integer(col),
    do: "#{file}:#{line}:#{col}"

  def show(%{left: left, right: right}), do: "left #{show(left)} right #{show(right)}"
  def show(%{at: at}), do: show(at)
  def show(other), do: inspect(other)
end

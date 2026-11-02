defmodule MuroVisor.Detail do
  @moduledoc false

  def empty, do: %{title: "", loc: "", kind: ""}

  @doc """
  Source location for a node, a configuration, or an edge.

  An edge is re-checked with `Muro.Explore.out_of_order/2`. The kind is
  that refusal. A node has no refusal.
  """
  def lookup(%{nodes: nodes, edges: edges}, book, id) when is_binary(id) do
    cond do
      node = Enum.find(nodes, &(&1.id == id)) ->
        %{title: node.name, loc: show(node.loc), kind: ""}

      edge = Enum.find(edges, &(&1.id == id)) ->
        refusal = Muro.Explore.out_of_order(book, edge)

        %{
          title: title(edge),
          loc: show(Map.get(refusal, :loc) || edge.loc),
          kind: to_string(refusal.kind)
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

  defp title(%{use: :step, step: step, proc: proc}), do: "step #{step} #{proc}"
  defp title(%{use: use}), do: to_string(use)

  def show(nil), do: ""
  def show({line, col}) when is_integer(line) and is_integer(col), do: "#{line}:#{col}"

  def show({file, line, col}) when is_binary(file) and is_integer(line) and is_integer(col),
    do: "#{file}:#{line}:#{col}"

  def show(%{left: left, right: right}), do: "left #{show(left)} right #{show(right)}"
  def show(%{at: at}), do: show(at)
  def show(other), do: inspect(other)
end

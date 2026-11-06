defmodule MuroVisor.Detail do
  @moduledoc false

  def empty, do: %{title: "", loc: "", kind: "", excerpts: []}

  @kinds [:configuration, :transition, :node, :edge]

  @doc """
  DOM id and selection value for one control.

  The kind is part of the value. `Name.encode("e0")` is `"e0"`, and the
  first use edge is also `"e0"`, so the raw ids collide.
  """
  def dom_id(kind, id) when kind in @kinds and is_binary(id) do
    Atom.to_string(kind) <> "-" <> id
  end

  @doc """
  Source location for one namespaced control id.

  The prefix selects the list. A node, an edge, a configuration, and a
  transition are never looked up in each other's lists.

  An edge is re-checked with `Muro.Explore.out_of_order/2`. The kind is
  that refusal. A use that cannot be moved says `no refusal`. A node
  has no refusal.
  """
  def lookup(%{nodes: nodes, edges: edges}, book, id) when is_binary(id) do
    case split(id) do
      {:node, raw} ->
        node_detail(nodes, book, raw)

      {:edge, raw} ->
        edge_detail(nodes, edges, book, raw)

      {:configuration, raw} ->
        configuration_detail(nodes, book, raw)

      {:transition, raw} ->
        transition_detail(nodes, book, raw)

      :error ->
        empty()
    end
  end

  defp split(id) do
    Enum.find_value(@kinds, fn kind ->
      prefix = Atom.to_string(kind) <> "-"

      if String.starts_with?(id, prefix) do
        {kind, String.replace_prefix(id, prefix, "")}
      end
    end) || :error
  end

  defp node_detail(nodes, book, id) do
    case Enum.find(nodes, &(&1.id == id)) do
      nil ->
        empty()

      node ->
        %{
          title: node.name,
          loc: show_at(node.file, node.loc),
          kind: "",
          excerpts: MuroVisor.Code.excerpts(book, node.file, node.loc)
        }
    end
  end

  defp edge_detail(nodes, edges, book, id) do
    case Enum.find(edges, &(&1.id == id)) do
      nil ->
        empty()

      edge ->
        refusal = Muro.Explore.out_of_order(book, edge)
        file = file_of(nodes, edge.from)
        at = Map.get(refusal, :loc) || edge.loc

        %{
          title: title(edge),
          loc: show_at(file, at),
          kind: refusal_kind(refusal),
          excerpts: MuroVisor.Code.excerpts(book, file, at)
        }
    end
  end

  defp configuration_detail(nodes, book, id) do
    case find_child(nodes, id) do
      nil ->
        empty()

      child ->
        %{
          title: child.meeting,
          loc: show(child.loc),
          kind: "",
          excerpts: MuroVisor.Code.excerpts(book, nil, child.loc)
        }
    end
  end

  defp transition_detail(nodes, book, id) do
    case find_transition(nodes, id) do
      nil ->
        empty()

      t ->
        at = Map.get(t, :loc)

        %{
          title: transition_title(t),
          loc: show(at),
          kind: "",
          excerpts: MuroVisor.Code.excerpts(book, nil, at)
        }
    end
  end

  defp find_child(nodes, id) do
    Enum.find_value(nodes, fn node ->
      Enum.find(node.children, &(&1.id == id))
    end)
  end

  defp find_transition(nodes, id) do
    Enum.find_value(nodes, fn node ->
      Enum.find(Map.get(node, :transitions, []), &(&1.id == id))
    end)
  end

  defp transition_title(%{label: label}) when is_list(label), do: Enum.join(label, " ")
  defp transition_title(%{label: label}) when is_binary(label), do: label
  defp transition_title(%{meeting: meeting}) when is_binary(meeting), do: meeting
  defp transition_title(_other), do: ""

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

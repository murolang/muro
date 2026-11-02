defmodule MuroVisor.Draw do
  @moduledoc false

  alias Muro.Emit.Name

  @pad 16
  @width 320
  @row 48
  @child 30
  @head 22
  @gap 16

  @doc """
  Column positions for the book graph.

  A session with proved configurations is taller. Each meeting is a
  compound box of those configurations, and the transitions between
  them are drawn on that box.
  """
  def layout(%{nodes: nodes, edges: edges}) do
    {placed, bottom} =
      Enum.reduce(nodes, {[], @pad}, fn node, {acc, y} ->
        meetings = meetings(node, y + 28)
        h = height(meetings)

        box = %{
          id: node.id,
          name: "#{node.mode} #{node.name}",
          kind: to_string(node.kind),
          mode: to_string(node.mode),
          class: css(meetings),
          x: @pad,
          y: y,
          w: @width,
          h: h,
          meetings: meetings
        }

        {[box | acc], y + h + @gap}
      end)

    placed = Enum.reverse(placed)
    index = Map.new(placed, &{&1.id, &1})

    drawn =
      Enum.flat_map(edges, fn edge ->
        case {Map.get(index, edge.from), Map.get(index, edge.to)} do
          {nil, _} ->
            []

          {_, nil} ->
            []

          {from, to} ->
            [
              %{
                id: edge.id,
                use: to_string(edge.use),
                from: edge.from,
                to: edge.to,
                x1: from.x + div(from.w, 2),
                y1: from.y + div(from.h, 2),
                x2: to.x + div(to.w, 2),
                y2: to.y + div(to.h, 2)
              }
            ]
        end
      end)

    %{width: @width + @pad * 2, height: max(bottom, @pad + @row), nodes: placed, edges: drawn}
  end

  defp css([]), do: "node"
  defp css(_meetings), do: "node compound"

  defp height([]), do: @row

  defp height(meetings) do
    extra = Enum.reduce(meetings, 0, fn meet, n -> n + @head + length(meet.children) * @child end)
    28 + extra
  end

  defp meetings(%{children: kids} = node, top) when is_list(kids) and kids != [] do
    order = kids |> Enum.map(& &1.meeting) |> Enum.uniq()
    trans = Map.get(node, :transitions, [])

    {groups, _} =
      Enum.reduce(order, {[], top}, fn meet, {acc, y} ->
        children = kids |> Enum.filter(&(&1.meeting == meet)) |> place_children(y + @head)
        group_h = @head + length(children) * @child

        group = %{
          id: "m-" <> Name.encode(node.name) <> "-" <> Name.encode(meet),
          name: meet,
          x: @pad + 8,
          y: y,
          w: @width - 16,
          h: group_h - 2,
          children: children,
          transitions: place_transitions(trans, meet, children)
        }

        {[group | acc], y + group_h}
      end)

    Enum.reverse(groups)
  end

  defp meetings(_, _), do: []

  defp place_children(children, top) do
    Enum.with_index(children, fn child, i ->
      %{
        id: child.id,
        label: "#{child.meeting} #{state_id(child)}",
        state: state_id(child),
        x: @pad + 16,
        y: top + i * @child,
        w: @width - 32,
        h: @child - 4
      }
    end)
  end

  defp state_id(child) do
    child.id |> String.split("-") |> List.last()
  end

  defp place_transitions(trans, meet, placed) do
    by_id = Map.new(placed, &{&1.id, &1})

    trans
    |> Enum.filter(&(&1.meeting == meet))
    |> Enum.with_index()
    |> Enum.flat_map(fn {t, i} ->
      case {Map.get(by_id, t.from), Map.get(by_id, t.to)} do
        {%{} = from, %{} = to} -> [transition(t, from, to, i)]
        _ -> []
      end
    end)
  end

  defp transition(t, from, to, i) do
    {d, lx, ly} = path(from, to)

    %{
      id: "#{i}-#{from.id}-#{to.id}",
      from: t.from,
      to: t.to,
      label: label(t.label),
      d: d,
      lx: lx,
      ly: ly
    }
  end

  defp label(list) when is_list(list), do: Enum.join(list, " ")
  defp label(other), do: to_string(other)

  defp path(%{id: id} = box, %{id: id}) do
    x = box.x + box.w - 8
    y = box.y + div(box.h, 2)
    {"M #{x} #{y} C #{x + 26} #{y - 12} #{x + 26} #{y + 12} #{x} #{y}", x + 28, y + 4}
  end

  defp path(from, to) do
    x1 = from.x + from.w - 8
    y1 = from.y + div(from.h, 2)
    x2 = to.x + to.w - 8
    y2 = to.y + div(to.h, 2)
    {"M #{x1} #{y1} L #{x2} #{y2}", div(x1 + x2, 2) + 4, div(y1 + y2, 2)}
  end
end

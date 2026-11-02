defmodule MuroVisor.Draw do
  @moduledoc false

  @pad 16
  @width 280
  @row 48
  @child 30
  @gap 16

  @doc """
  Column positions for the book graph.

  A session with configurations is taller and holds those children.
  """
  def layout(%{nodes: nodes, edges: edges}) do
    {placed, bottom} =
      Enum.reduce(nodes, {[], @pad}, fn node, {acc, y} ->
        h = height(node)
        kids = place_children(node.children, y + 28)

        box = %{
          id: node.id,
          name: "#{node.mode} #{node.name}",
          class: css(node),
          x: @pad,
          y: y,
          w: @width,
          h: h,
          children: kids
        }

        {[box | acc], y + h + @gap}
      end)

    placed = Enum.reverse(placed)
    index = index(placed)

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
                use: edge.use,
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

  defp height(%{children: kids}) when is_list(kids) and kids != [], do: 36 + length(kids) * @child
  defp height(_node), do: @row

  defp css(%{children: kids}) when is_list(kids) and kids != [], do: "node compound"
  defp css(_node), do: "node"

  defp place_children(children, top) when is_list(children) do
    Enum.with_index(children, fn child, i ->
      %{
        id: child.id,
        label: "#{child.meeting} #{i}",
        x: @pad + 12,
        y: top + i * @child,
        w: @width - 24,
        h: @child - 4
      }
    end)
  end

  defp index(placed) do
    Enum.reduce(placed, %{}, fn box, acc ->
      Map.put(acc, box.id, box)
    end)
  end
end

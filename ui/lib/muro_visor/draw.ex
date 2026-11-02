defmodule MuroVisor.Draw do
  @moduledoc false

  alias Muro.Emit.Name

  @pad 16
  @node_gap 32
  @rank_gap 88
  @grid_gap 64
  @channel 14
  @pitch 16
  @inset 6
  @loop 22
  @loop_band 36
  @header 22
  @char 7
  @label_h 14
  @sweeps 4

  @doc """
  Layered positions for the book graph.

  Nodes sit in ranks along use edges. A rank is a column, and a book
  with no use edges wraps into a wide grid. Each edge has its own
  path. The same book always yields the same coordinates.
  """
  def layout(%{nodes: nodes, edges: edges}) do
    prepared = Enum.map(nodes, &prepare/1)
    picture = place(prepared, book_edges(edges))
    nodes = Enum.map(picture.nodes, &mount_meetings/1)
    %{picture | nodes: nodes}
  end

  defp prepare(node) do
    meetings = build_meetings(node)
    label = "#{node.mode} #{node.name}"
    inner_w = meetings |> Enum.map(& &1.w) |> Enum.max(fn -> 0 end)

    inner_h =
      case meetings do
        [] -> 36
        ms -> @header + Enum.sum(Enum.map(ms, & &1.h)) + 8 * length(ms)
      end

    %{
      id: node.id,
      name: label,
      kind: to_string(node.kind),
      mode: to_string(node.mode),
      class: if(meetings == [], do: "node", else: "node compound"),
      w: max(text_w(label) + 24, max(inner_w + 16, 96)),
      h: max(inner_h, 36),
      x: 0,
      y: 0,
      meetings: meetings
    }
  end

  defp build_meetings(%{children: kids} = node) when is_list(kids) and kids != [] do
    order = kids |> Enum.map(& &1.meeting) |> Enum.uniq()
    trans = Map.get(node, :transitions, [])

    Enum.map(order, fn meet ->
      children = Enum.filter(kids, &(&1.meeting == meet))
      transitions = Enum.filter(trans, &(&1.meeting == meet))
      layout_meeting(node.name, meet, children, transitions)
    end)
  end

  defp build_meetings(_node), do: []

  defp layout_meeting(session, meet, children, transitions) do
    nodes =
      Enum.map(children, fn child ->
        label = "#{child.meeting} #{state_id(child)}"

        %{
          id: child.id,
          label: label,
          state: state_id(child),
          w: max(text_w(label) + 20, 72),
          h: 28,
          x: 0,
          y: 0,
          meetings: []
        }
      end)

    edges =
      Enum.map(Enum.with_index(transitions), fn {t, i} ->
        %{
          id: "#{i}-#{t.from}-#{t.to}",
          from: t.from,
          to: t.to,
          label: text_label(t.label),
          use: "trans",
          d: "",
          lx: 0,
          ly: 0
        }
      end)

    picture = place(nodes, edges)
    picture = shift_picture(picture, 0, @header)

    %{
      id: "m-" <> Name.encode(session) <> "-" <> Name.encode(meet),
      name: meet,
      x: 0,
      y: 0,
      w: max(picture.width, text_w(meet) + 16),
      h: picture.height,
      children:
        Enum.map(picture.nodes, fn n ->
          %{id: n.id, label: n.label, state: n.state, x: n.x, y: n.y, w: n.w, h: n.h}
        end),
      transitions:
        Enum.map(picture.edges, fn e ->
          %{id: e.id, from: e.from, to: e.to, label: e.label, d: e.d, lx: e.lx, ly: e.ly}
        end)
    }
  end

  defp mount_meetings(node) do
    {meetings, _} =
      Enum.map_reduce(node.meetings, node.y + @header, fn meet, y ->
        {shift_meeting(meet, node.x + 8 - meet.x, y - meet.y), y + meet.h + 8}
      end)

    %{node | meetings: meetings}
  end

  defp book_edges(edges) do
    Enum.map(edges, fn edge ->
      %{
        id: edge.id,
        from: edge.from,
        to: edge.to,
        label: to_string(edge.use),
        use: to_string(edge.use),
        d: "",
        lx: 0,
        ly: 0
      }
    end)
  end

  defp place([], _edges), do: %{width: @pad * 2, height: @pad * 2, nodes: [], edges: []}

  defp place(nodes, edges) do
    known = MapSet.new(nodes, & &1.id)

    edges =
      Enum.filter(edges, fn e -> MapSet.member?(known, e.from) and MapSet.member?(known, e.to) end)

    ids = Enum.map(nodes, & &1.id)

    pairs =
      edges |> Enum.reject(&(&1.from == &1.to)) |> Enum.map(&{&1.from, &1.to}) |> Enum.uniq()

    rank = rank_map(ids, pairs)

    picture =
      if one_rank?(rank) and Enum.all?(edges, &(&1.from == &1.to)) do
        grid(nodes, edges, rank)
      else
        columns(nodes, edges, rank)
      end

    lift(picture)
  end

  defp one_rank?(rank) do
    case Map.values(rank) |> Enum.uniq() do
      [] -> true
      [_] -> true
      _ -> false
    end
  end

  defp grid(nodes, edges, rank) do
    ports = port_lists(edges, rank)
    nodes = Enum.map(nodes, &grow(&1, ports_of(ports, &1.id)))
    ordered = Enum.sort_by(nodes, & &1.id)
    cols = min(6, max(1, ceil(:math.sqrt(length(ordered)))))
    col_w = ordered |> Enum.map(& &1.w) |> Enum.max()
    rows = Enum.chunk_every(ordered, cols)

    {positions, _y} =
      Enum.reduce(rows, {%{}, @pad}, fn row, {acc, y} ->
        row_h =
          row
          |> Enum.map(fn node -> node.h + loop_count(node.id, edges) * @loop_band end)
          |> Enum.max()

        acc =
          Enum.reduce(Enum.with_index(row), acc, fn {node, c}, acc ->
            loops = loop_count(node.id, edges) * @loop_band
            x = @pad + c * (col_w + @grid_gap)

            Map.put(acc, node.id, %{node | x: x, y: y + loops})
          end)

        {acc, y + row_h + @node_gap}
      end)

    placed = Enum.map(nodes, &Map.fetch!(positions, &1.id))
    by_id = Map.new(placed, &{&1.id, &1})
    routed = Enum.map(edges, &route_self(&1, by_id, ports))
    routed = separate_labels(routed)
    Map.merge(bounds(placed, routed), %{nodes: placed, edges: routed})
  end

  defp columns(nodes, edges, rank) do
    ports = port_lists(edges, rank)
    nodes = Enum.map(nodes, &grow(&1, ports_of(ports, &1.id)))
    by_rank = order_ranks(nodes, edges, rank)
    demand = channel_demand(edges, rank)
    {placed, gaps} = assign_columns(by_rank, demand, edges)
    by_id = Map.new(placed, &{&1.id, &1})
    gutter = gutter_top(placed)

    routed =
      edges
      |> Enum.map_reduce({gaps, 0}, fn edge, {gaps, gi} ->
        {drawn, gaps, gi} = route(edge, by_id, rank, ports, gaps, gutter, gi)
        {drawn, {gaps, gi}}
      end)
      |> elem(0)

    routed = separate_labels(routed)
    order = Map.new(Enum.with_index(nodes), fn {node, i} -> {node.id, i} end)
    placed = Enum.sort_by(placed, &Map.fetch!(order, &1.id))
    Map.merge(bounds(placed, routed), %{nodes: placed, edges: routed})
  end

  defp assign_columns(by_rank, demand, edges) do
    ranks = by_rank |> Map.keys() |> Enum.sort()

    Enum.reduce(ranks, {[], %{}, @pad}, fn r, {acc, gaps, x} ->
      col = Map.fetch!(by_rank, r)
      width = col |> Enum.map(& &1.w) |> Enum.max()
      labels = labels_for(edges, r)
      gap_w = gap_width(Map.get(demand, r, {0, 0}), labels)

      {col_nodes, _} =
        Enum.map_reduce(col, @pad, fn node, y ->
          loops = loop_count(node.id, edges) * @loop_band
          y = y + loops
          {%{node | x: x, y: y}, y + node.h + @node_gap}
        end)

      gaps = Map.put(gaps, r, %{x0: x + width, next_left: 0, next_right: 0, w: gap_w})
      {acc ++ col_nodes, gaps, x + width + gap_w}
    end)
    |> then(fn {placed, gaps, _x} -> {placed, gaps} end)
  end

  defp route(edge, by_id, rank, ports, gaps, gutter, gi) do
    case orient(edge, rank) do
      :self ->
        {route_self(edge, by_id, ports), gaps, gi}

      :forward ->
        forward(edge, by_id, rank, ports, gaps, gutter, gi)

      :back ->
        backward(edge, by_id, rank, ports, gaps, gutter, gi)

      :same ->
        same_rank(edge, by_id, rank, ports, gaps, gi)
    end
  end

  defp route_self(edge, by_id, ports) do
    node = Map.fetch!(by_id, edge.from)
    {x1, y1} = port_at(node, ports, :top, edge.id, 0)
    {x2, y2} = port_at(node, ports, :top, edge.id, 1)
    k = loop_index(ports, node.id, edge.id)
    h = @loop + k * 14
    cy = y1 - h

    %{
      edge
      | d: "M #{x1} #{y1} C #{x1} #{cy} #{x2} #{cy} #{x2} #{y2}",
        lx: min(x1, x2) + 4,
        ly: max(cy + 12, 12)
    }
  end

  defp forward(edge, by_id, rank, ports, gaps, gutter, gi) do
    from = Map.fetch!(by_id, edge.from)
    to = Map.fetch!(by_id, edge.to)
    r1 = Map.fetch!(rank, edge.from)
    r2 = Map.fetch!(rank, edge.to)
    {sx, sy} = port_at(from, ports, :right, edge.id, 0)
    {tx, ty} = port_at(to, ports, :left, edge.id, 0)

    # Stubs stay on opposite sides of the gap. The crossbar is a private
    # lane below the nodes, so two edges never share a horizontal.
    gy = gutter + gi * (@label_h + 6)

    {c1, c2, gaps} =
      if r2 == r1 + 1 do
        {c1, gaps} = take_left(gaps, r1)
        {c2, gaps} = take_right(gaps, r1)
        {c1, c2, gaps}
      else
        {c1, gaps} = take_left(gaps, r1)
        {c2, gaps} = take_right(gaps, r2 - 1)
        {c1, c2, gaps}
      end

    drawn =
      polyline(edge, [sx, sy, c1, sy, c1, gy, c2, gy, c2, ty, tx, ty], min(c1, c2) + 4, gy - 2)

    {drawn, gaps, gi + 1}
  end

  defp backward(edge, by_id, rank, ports, gaps, gutter, gi) do
    from = Map.fetch!(by_id, edge.from)
    to = Map.fetch!(by_id, edge.to)
    r1 = Map.fetch!(rank, edge.from)
    r2 = Map.fetch!(rank, edge.to)
    {sx, sy} = port_at(from, ports, :left, edge.id, 0)
    {tx, ty} = port_at(to, ports, :right, edge.id, 0)
    gy = gutter + gi * (@label_h + 6)

    {c1, c2, gaps} =
      if r1 == r2 + 1 do
        {c1, gaps} = take_right(gaps, r2)
        {c2, gaps} = take_left(gaps, r2)
        {c1, c2, gaps}
      else
        {c1, gaps} = take_right(gaps, r1 - 1)
        {c2, gaps} = take_left(gaps, r2)
        {c1, c2, gaps}
      end

    drawn =
      polyline(edge, [sx, sy, c1, sy, c1, gy, c2, gy, c2, ty, tx, ty], min(c1, c2) + 4, gy - 2)

    {drawn, gaps, gi + 1}
  end

  defp same_rank(edge, by_id, rank, ports, gaps, gi) do
    from = Map.fetch!(by_id, edge.from)
    to = Map.fetch!(by_id, edge.to)
    r = Map.fetch!(rank, edge.from)
    {sx, sy} = port_at(from, ports, :right, edge.id, 0)
    {tx, ty} = port_at(to, ports, :right, edge.id, 0)
    {cx, gaps} = take_left(gaps, r)
    drawn = polyline(edge, [sx, sy, cx, sy, cx, ty, tx, ty], cx + 4, mid(sy, ty))
    {drawn, gaps, gi}
  end

  defp polyline(edge, points, lx, ly) do
    [x, y | rest] = points
    legs = rest |> Enum.chunk_every(2) |> Enum.map_join(fn [px, py] -> " L #{px} #{py}" end)
    d = "M #{x} #{y}" <> legs

    %{edge | d: d, lx: lx, ly: max(ly, 12)}
  end

  # Left channels sit beside the source column. Right channels sit beside
  # the destination column. The two zones do not meet.
  defp take_left(gaps, r) do
    g = Map.fetch!(gaps, r)
    x = g.x0 + 8 + g.next_left * @channel
    {x, put_in(gaps[r].next_left, g.next_left + 1)}
  end

  defp take_right(gaps, r) do
    g = Map.fetch!(gaps, r)
    x = g.x0 + g.w - 8 - g.next_right * @channel
    {x, put_in(gaps[r].next_right, g.next_right + 1)}
  end

  defp port_at(node, ports, side, edge_id, nth) do
    list = Map.get(ports_of(ports, node.id), side, [])
    indexes = for {id, i} <- Enum.with_index(list), id == edge_id, do: i
    side_point(node, side, Enum.at(indexes, nth), max(length(list), 1))
  end

  defp side_point(node, :right, i, n), do: {node.x + node.w, node.y + slot(node.h, i, n)}
  defp side_point(node, :left, i, n), do: {node.x, node.y + slot(node.h, i, n)}
  defp side_point(node, :top, i, n), do: {node.x + slot(node.w, i, n), node.y}
  defp side_point(node, :bottom, i, n), do: {node.x + slot(node.w, i, n), node.y + node.h}

  defp slot(len, i, n) do
    cond do
      n <= 1 -> div(len, 2)
      true -> @inset + i * max(div(len - 2 * @inset, n - 1), 1)
    end
  end

  defp port_lists(edges, rank) do
    Enum.reduce(edges, %{}, fn edge, acc ->
      case orient(edge, rank) do
        :self ->
          acc |> push_port(edge.from, :top, edge.id) |> push_port(edge.from, :top, edge.id)

        :forward ->
          acc |> push_port(edge.from, :right, edge.id) |> push_port(edge.to, :left, edge.id)

        :back ->
          acc |> push_port(edge.from, :left, edge.id) |> push_port(edge.to, :right, edge.id)

        :same ->
          acc |> push_port(edge.from, :right, edge.id) |> push_port(edge.to, :right, edge.id)
      end
    end)
  end

  defp push_port(acc, id, side, edge_id) do
    acc
    |> Map.put_new(id, empty_ports())
    |> update_in([id, side], &(&1 ++ [edge_id]))
  end

  defp empty_ports, do: %{top: [], right: [], bottom: [], left: []}
  defp ports_of(ports, id), do: Map.get(ports, id, empty_ports())

  defp grow(node, ports) do
    side = max(length(ports.left), length(ports.right))
    top = length(ports.top)

    h =
      if side <= 1,
        do: node.h,
        else: max(node.h, 2 * @inset + (side - 1) * @pitch)

    w =
      if top <= 1,
        do: node.w,
        else: max(node.w, 2 * @inset + (top - 1) * @pitch)

    %{node | w: w, h: h}
  end

  defp bump(map, key, :left) do
    Map.update(map, key, {1, 0}, fn {left, right} -> {left + 1, right} end)
  end

  defp bump(map, key, :right) do
    Map.update(map, key, {0, 1}, fn {left, right} -> {left, right + 1} end)
  end

  defp channel_demand(edges, rank) do
    Enum.reduce(edges, %{}, fn edge, acc ->
      case orient(edge, rank) do
        :self ->
          acc

        :forward ->
          r1 = Map.fetch!(rank, edge.from)
          r2 = Map.fetch!(rank, edge.to)

          if r2 == r1 + 1 do
            acc |> bump(r1, :left) |> bump(r1, :right)
          else
            acc |> bump(r1, :left) |> bump(r2 - 1, :right)
          end

        :back ->
          r1 = Map.fetch!(rank, edge.from)
          r2 = Map.fetch!(rank, edge.to)

          if r1 == r2 + 1 do
            acc |> bump(r2, :right) |> bump(r2, :left)
          else
            acc |> bump(r1 - 1, :right) |> bump(r2, :left)
          end

        :same ->
          bump(acc, Map.fetch!(rank, edge.from), :left)
      end
    end)
  end

  defp labels_for(edges, gap) do
    # Every non-self edge can put its label in a gap. Size every gap for
    # the longest label so a late channel still has room.
    edges
    |> Enum.reject(&(&1.from == &1.to))
    |> Enum.map(& &1.label)
    |> then(fn labels -> if gap < 0, do: [], else: labels end)
  end

  defp gap_width({0, 0}, _labels), do: @pad

  defp gap_width({left, right}, labels) do
    label_w = labels |> Enum.map(&text_w/1) |> Enum.max(fn -> 0 end)
    max(@rank_gap, 24 + (left + right) * @channel + label_w)
  end

  defp order_ranks(nodes, edges, rank) do
    grouped = Enum.group_by(nodes, &Map.fetch!(rank, &1.id))

    ids =
      Map.new(grouped, fn {r, ns} ->
        {r, ns |> Enum.sort_by(& &1.id) |> Enum.map(& &1.id)}
      end)

    dag = adjacent_dag(edges, rank)
    ordered = bary_sweeps(ids, dag)

    Map.new(ordered, fn {r, layer} ->
      by_id = Map.new(grouped[r], &{&1.id, &1})
      {r, Enum.map(layer, &Map.fetch!(by_id, &1))}
    end)
  end

  defp adjacent_dag(edges, rank) do
    pairs =
      edges |> Enum.reject(&(&1.from == &1.to)) |> Enum.map(&{&1.from, &1.to}) |> Enum.uniq()

    {_seen, rev} =
      walk(Enum.map(pairs, &elem(&1, 0)) ++ Enum.map(pairs, &elem(&1, 1)), adj(pairs))

    Enum.flat_map(pairs, fn {a, b} = edge ->
      {s, t} = if MapSet.member?(rev, edge), do: {b, a}, else: {a, b}

      if Map.get(rank, t) == Map.get(rank, s) + 1 do
        [{s, t}]
      else
        []
      end
    end)
  end

  defp bary_sweeps(order, dag) do
    max_r = order |> Map.keys() |> Enum.max(fn -> 0 end)
    preds = Enum.group_by(dag, &elem(&1, 1), &elem(&1, 0))
    succs = Enum.group_by(dag, &elem(&1, 0), &elem(&1, 1))

    Enum.reduce(1..@sweeps, order, fn _, order ->
      order =
        Enum.reduce(1..max_r, order, fn r, order ->
          Map.put(order, r, sort_layer(order[r], index_map(order[r - 1]), preds))
        end)

      Enum.reduce((max_r - 1)..0//-1, order, fn r, order ->
        Map.put(order, r, sort_layer(order[r], index_map(order[r + 1] || []), succs))
      end)
    end)
  end

  defp sort_layer(nil, _index, _rel), do: []

  defp sort_layer(ids, neighbor, rel) do
    self = index_map(ids)

    Enum.sort_by(ids, fn id ->
      ns =
        rel
        |> Map.get(id, [])
        |> Enum.map(&Map.get(neighbor, &1))
        |> Enum.reject(&is_nil/1)

      key = if ns == [], do: self[id] * 1000, else: div(Enum.sum(ns) * 1000, length(ns))
      {key, id}
    end)
  end

  defp index_map(ids), do: Map.new(Enum.with_index(ids))

  defp rank_map(ids, pairs) do
    {_seen, rev} = walk(ids, adj(pairs))

    dag =
      Enum.map(pairs, fn {a, b} = edge ->
        if MapSet.member?(rev, edge), do: {b, a}, else: {a, b}
      end)

    incoming = Enum.group_by(dag, &elem(&1, 1), &elem(&1, 0))

    Enum.reduce(Enum.sort(ids), %{}, fn id, memo ->
      {memo, _r} = rank_of(id, incoming, memo, MapSet.new())
      memo
    end)
  end

  defp rank_of(id, incoming, memo, stack) do
    cond do
      Map.has_key?(memo, id) ->
        {memo, Map.fetch!(memo, id)}

      MapSet.member?(stack, id) ->
        {memo, 0}

      true ->
        stack = MapSet.put(stack, id)

        {memo, best} =
          Enum.reduce(Map.get(incoming, id, []), {memo, -1}, fn pred, {memo, best} ->
            {memo, r} = rank_of(pred, incoming, memo, stack)
            {memo, max(best, r)}
          end)

        r = best + 1
        {Map.put(memo, id, r), r}
    end
  end

  defp walk(ids, adj) do
    Enum.reduce(Enum.sort(ids), {MapSet.new(), MapSet.new()}, fn id, {seen, rev} ->
      {seen, _stack, rev} = dfs(id, adj, seen, MapSet.new(), rev)
      {seen, rev}
    end)
  end

  defp dfs(id, adj, seen, stack, rev) do
    if MapSet.member?(seen, id) do
      {seen, stack, rev}
    else
      seen = MapSet.put(seen, id)
      stack = MapSet.put(stack, id)

      {seen, stack, rev} =
        Enum.reduce(Map.get(adj, id, []), {seen, stack, rev}, fn nxt, {seen, stack, rev} ->
          cond do
            MapSet.member?(stack, nxt) ->
              {seen, stack, MapSet.put(rev, {id, nxt})}

            MapSet.member?(seen, nxt) ->
              {seen, stack, rev}

            true ->
              dfs(nxt, adj, seen, stack, rev)
          end
        end)

      {seen, MapSet.delete(stack, id), rev}
    end
  end

  defp adj(pairs) do
    pairs
    |> Enum.group_by(&elem(&1, 0), &elem(&1, 1))
    |> Map.new(fn {k, vs} -> {k, Enum.sort(Enum.uniq(vs))} end)
  end

  defp orient(%{from: id, to: id}, _rank), do: :self

  defp orient(edge, rank) do
    r1 = Map.fetch!(rank, edge.from)
    r2 = Map.fetch!(rank, edge.to)

    cond do
      r1 < r2 -> :forward
      r1 > r2 -> :back
      true -> :same
    end
  end

  defp loop_count(id, edges) do
    Enum.count(edges, &(&1.from == id and &1.to == id))
  end

  defp loop_index(ports, id, edge_id) do
    ports
    |> ports_of(id)
    |> Map.fetch!(:top)
    |> Enum.chunk_every(2)
    |> Enum.find_index(fn [a, _b] -> a == edge_id end)
    |> Kernel.||(0)
  end

  defp gutter_top(nodes) do
    nodes |> Enum.map(fn n -> n.y + n.h end) |> Enum.max(fn -> @pad end) |> Kernel.+(@pad)
  end

  defp separate_labels(edges) do
    Enum.reduce(edges, [], fn edge, placed ->
      placed ++ [nudge(edge, placed, 0)]
    end)
  end

  defp nudge(edge, _placed, n) when n > 100, do: %{edge | lx: edge.lx + 8}

  defp nudge(edge, placed, n) do
    box = label_box(edge)

    clash =
      edge.label != "" and
        Enum.any?(placed, fn other ->
          other.label != "" and boxes_overlap?(label_box(other), box)
        end)

    if clash do
      nudge(%{edge | ly: edge.ly + @label_h + 2}, placed, n + 1)
    else
      edge
    end
  end

  defp label_box(%{label: label, lx: lx, ly: ly}) do
    %{x: lx, y: ly - 12, w: text_w(label), h: @label_h}
  end

  defp boxes_overlap?(a, b) do
    a.x < b.x + b.w and b.x < a.x + a.w and a.y < b.y + b.h and b.y < a.y + a.h
  end

  defp bounds(nodes, edges) do
    boxes =
      Enum.flat_map(nodes, fn n ->
        [{n.x, n.y}, {n.x + n.w, n.y + n.h}]
      end) ++
        Enum.flat_map(edges, fn e ->
          b = label_box(e)
          path_pairs(e.d) ++ [{b.x, b.y}, {b.x + b.w, b.y + b.h}]
        end)

    max_x = boxes |> Enum.map(&elem(&1, 0)) |> Enum.max(fn -> @pad end)
    max_y = boxes |> Enum.map(&elem(&1, 1)) |> Enum.max(fn -> @pad end)
    %{width: max(max_x + @pad, @pad * 2), height: max(max_y + @pad, @pad * 2)}
  end

  defp lift(picture) do
    pts =
      Enum.flat_map(picture.nodes, fn n ->
        [{n.x, n.y}, {n.x + n.w, n.y + n.h}]
      end) ++
        Enum.flat_map(picture.edges, fn e ->
          b = label_box(e)
          path_pairs(e.d) ++ [{b.x, b.y}]
        end)

    min_x = pts |> Enum.map(&elem(&1, 0)) |> Enum.min(fn -> @pad end)
    min_y = pts |> Enum.map(&elem(&1, 1)) |> Enum.min(fn -> @pad end)
    dx = max(0, @pad - min_x)
    dy = max(0, @pad - min_y)

    if dx == 0 and dy == 0 do
      picture
    else
      picture = shift_picture(picture, dx, dy)
      Map.merge(picture, bounds(picture.nodes, picture.edges))
    end
  end

  defp shift_picture(picture, dx, dy) do
    %{
      picture
      | width: picture.width + dx,
        height: picture.height + dy,
        nodes: Enum.map(picture.nodes, &shift_node(&1, dx, dy)),
        edges: Enum.map(picture.edges, &shift_edge(&1, dx, dy))
    }
  end

  defp shift_node(node, dx, dy), do: %{node | x: node.x + dx, y: node.y + dy}

  defp shift_edge(edge, dx, dy) do
    %{edge | d: shift_path(edge.d, dx, dy), lx: edge.lx + dx, ly: edge.ly + dy}
  end

  defp shift_meeting(meet, dx, dy) do
    %{
      meet
      | x: meet.x + dx,
        y: meet.y + dy,
        children: Enum.map(meet.children, &shift_node(&1, dx, dy)),
        transitions: Enum.map(meet.transitions, &shift_edge(&1, dx, dy))
    }
  end

  defp shift_path(d, dx, dy) do
    {iodata, _axis} =
      Regex.split(~r/-?\d+/, d, include_captures: true)
      |> Enum.reduce({[], :x}, fn token, {acc, axis} ->
        case Integer.parse(token) do
          {n, ""} ->
            add = if axis == :x, do: dx, else: dy
            {[Integer.to_string(n + add) | acc], if(axis == :x, do: :y, else: :x)}

          _ ->
            {[token | acc], axis}
        end
      end)

    iodata |> Enum.reverse() |> IO.iodata_to_binary()
  end

  defp path_pairs(d) do
    Regex.scan(~r/-?\d+/, d)
    |> Enum.map(fn [n] -> String.to_integer(n) end)
    |> Enum.chunk_every(2)
    |> Enum.flat_map(fn
      [x, y] -> [{x, y}]
      _ -> []
    end)
  end

  defp mid(a, b), do: div(a + b, 2) + 4

  defp text_w(text), do: max(String.length(to_string(text)), 1) * @char

  defp text_label(list) when is_list(list), do: Enum.join(list, " ")
  defp text_label(other), do: to_string(other)

  defp state_id(child) do
    child.id |> String.split("-") |> List.last()
  end
end

defmodule MuroVisor.Draw do
  @moduledoc false

  alias Muro.Emit.Name

  @pad 16
  @node_gap 32
  @rank_gap 88
  @grid_gap 64
  @channel 14
  @bend 4
  @pitch 16
  @inset 6
  @loop 22
  @loop_band 36
  @header 22
  @char 7
  @label_h 14
  @sweeps 8

  @doc """
  Layered positions for the book graph.

  Nodes sit in ranks along use edges. A rank is a column, and a book
  with no use edges wraps into a wide grid. A long edge bends once in
  each rank it crosses, and each hop stays in the gap between two
  adjacent columns. The same book always yields the same coordinates.
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
    routed = separate_labels(routed, placed)
    Map.merge(bounds(placed, routed), %{nodes: placed, edges: routed})
  end

  defp columns(nodes, edges, rank) do
    hops = expand_hops(edges, rank)
    rank = put_bends(rank, hops)
    ports = port_lists(hop_edges(hops) ++ Enum.filter(edges, &(&1.from == &1.to)), rank)
    nodes = Enum.map(nodes, &grow(&1, ports_of(ports, &1.id)))
    order = order_layers(nodes, hops, rank)
    {placed, cols, ys} = place_columns(order, Map.new(nodes, &{&1.id, &1}), hops, edges)
    routed = route_edges(edges, hops, Map.new(placed, &{&1.id, &1}), ports, cols, ys)
    routed = separate_labels(routed, placed)
    index = Map.new(Enum.with_index(nodes), fn {node, i} -> {node.id, i} end)
    placed = Enum.sort_by(placed, &Map.fetch!(index, &1.id))
    Map.merge(bounds(placed, routed), %{nodes: placed, edges: routed})
  end

  # One hop per adjacent pair of ranks. A rank in between is a bend, not
  # a drawn node. The bend takes its own row in that column, so two long
  # edges never share the line they use to cross it.
  defp expand_hops(edges, rank) do
    Enum.flat_map(edges, fn edge ->
      case orient(edge, rank) do
        :self ->
          []

        _ ->
          r1 = Map.fetch!(rank, edge.from)
          r2 = Map.fetch!(rank, edge.to)

          if r1 == r2 do
            [%{id: edge.id, seq: 0, from: edge.from, to: edge.to, fr: r1, tr: r2}]
          else
            step = if r1 < r2, do: 1, else: -1
            ranks = Enum.to_list(r1..r2//step)
            mids = ranks |> tl() |> Enum.drop(-1)
            points = [edge.from | Enum.map(mids, &{:bend, edge.id, &1})] ++ [edge.to]

            points
            |> Enum.zip(tl(points))
            |> Enum.zip(Enum.zip(ranks, tl(ranks)))
            |> Enum.with_index()
            |> Enum.map(fn {{{a, b}, {ra, rb}}, i} ->
              %{id: edge.id, seq: i, from: a, to: b, fr: ra, tr: rb}
            end)
          end
      end
    end)
  end

  defp hop_edges(hops), do: Enum.map(hops, &%{id: &1.id, from: &1.from, to: &1.to})

  defp put_bends(rank, hops) do
    Enum.reduce(hops, rank, fn hop, rank ->
      rank |> maybe_bend(hop.from) |> maybe_bend(hop.to)
    end)
  end

  defp maybe_bend(rank, {:bend, _, r} = id), do: Map.put(rank, id, r)
  defp maybe_bend(rank, _), do: rank

  defp order_layers(nodes, hops, rank) do
    ids =
      nodes
      |> Enum.group_by(&Map.fetch!(rank, &1.id))
      |> Map.new(fn {r, ns} -> {r, ns |> Enum.map(& &1.id) |> Enum.sort()} end)

    bends =
      hops
      |> Enum.flat_map(fn hop -> [hop.from, hop.to] end)
      |> Enum.filter(&bend?/1)
      |> Enum.uniq()

    ids =
      Enum.reduce(bends, ids, fn {:bend, _, r} = id, ids ->
        Map.update(ids, r, [id], fn list ->
          if id in list, do: list, else: list ++ [id]
        end)
      end)

    dag = hop_dag(hops)
    preds = Enum.group_by(dag, &elem(&1, 1), &elem(&1, 0))

    seeded =
      Map.new(ids, fn {r, list} ->
        {reals, bends} = Enum.split_with(list, &(not bend?(&1)))
        {r, seed_ids(Enum.sort(reals), Enum.sort(bends), preds)}
      end)

    bary_sweeps(seeded, dag)
  end

  defp seed_ids(reals, bends, preds) do
    Enum.reduce(bends, reals, fn id, acc ->
      pred = preds |> Map.get(id, []) |> Enum.find(&(&1 in acc))

      case pred && Enum.find_index(acc, &(&1 == pred)) do
        i when is_integer(i) -> List.insert_at(acc, i + 1, id)
        _ -> acc ++ [id]
      end
    end)
  end

  defp hop_dag(hops) do
    hops
    |> Enum.flat_map(fn hop ->
      cond do
        hop.fr + 1 == hop.tr -> [{hop.from, hop.to}]
        hop.tr + 1 == hop.fr -> [{hop.to, hop.from}]
        true -> []
      end
    end)
    |> Enum.uniq()
  end

  defp bend?({:bend, _, _}), do: true
  defp bend?(_), do: false

  defp place_columns(order, by_id, hops, edges) do
    lanes = gap_lanes(hops)
    same = same_counts(hops)
    ranks = order |> Map.keys() |> Enum.sort()

    Enum.reduce(ranks, {[], %{}, %{}, @pad}, fn r, {acc, cols, ys, x} ->
      ids = Map.fetch!(order, r)
      reals = Enum.reject(ids, &bend?/1)
      width = reals |> Enum.map(&Map.fetch!(by_id, &1).w) |> Enum.max(fn -> 1 end)
      {col_nodes, ys, bottom} = stack_column(reals, bend_gaps(ids), by_id, edges, ys, x)

      # Same-rank channels sit on the left of the gap. Each cross-rank hop
      # then takes a private jog on both sides, so the gap has to hold all
      # three strips or later hops would share a vertical.
      ncross = Map.get(lanes, r, 0)
      nsame = Map.get(same, r, 0)
      gap = max(@rank_gap, 12 + (nsame + 2 * ncross) * @channel)
      cols = Map.put(cols, r, %{left: x, right: x + width, bottom: bottom})
      {acc ++ col_nodes, cols, ys, x + width + gap}
    end)
    |> then(fn {placed, cols, ys, _x} -> {placed, cols, ys} end)
  end

  # Bends that the ordering puts above the first node, or below the last,
  # move into the nearest gap between nodes. Their rows then sit inside
  # the column's node box, and each bend still has its own y.
  defp bend_gaps(ids) do
    {gaps, n} =
      Enum.reduce(ids, {%{}, 0}, fn id, {gaps, gi} ->
        if bend?(id) do
          {Map.update(gaps, gi, [id], &(&1 ++ [id])), gi}
        else
          {gaps, gi + 1}
        end
      end)

    tuck_bends(gaps, n)
  end

  defp tuck_bends(gaps, n) when n >= 2 do
    lead = Map.get(gaps, 0, [])
    trail = Map.get(gaps, n, [])

    gaps
    |> Map.delete(0)
    |> Map.delete(n)
    |> Map.update(1, lead, &(lead ++ &1))
    |> Map.update(n - 1, trail, &(&1 ++ trail))
  end

  defp tuck_bends(gaps, _n), do: gaps

  defp stack_column(reals, gaps, by_id, edges, ys, x) do
    {ys, y} = drop_bends(Map.get(gaps, 0, []), ys, @pad)

    {nodes, ys, y} =
      reals
      |> Enum.with_index()
      |> Enum.reduce({[], ys, y}, fn {id, i}, {nodes, ys, y} ->
        node = Map.fetch!(by_id, id)
        y = y + loop_count(node.id, edges) * @loop_band
        node = %{node | x: x, y: y}
        y = y + node.h
        gap_y = y + div(@node_gap, 2)
        {ys, y} = drop_bends(Map.get(gaps, i + 1, []), ys, gap_y)
        {[node | nodes], ys, max(y, node.y + node.h + @node_gap)}
      end)

    {Enum.reverse(nodes), ys, y}
  end

  defp drop_bends(ids, ys, y) do
    Enum.reduce(ids, {ys, y}, fn id, {ys, y} ->
      {Map.put(ys, id, y), y + @bend}
    end)
  end

  defp gap_lanes(hops) do
    hops
    |> Enum.filter(&(&1.fr != &1.tr))
    |> Enum.reduce(%{}, fn hop, acc ->
      Map.update(acc, min(hop.fr, hop.tr), 1, &(&1 + 1))
    end)
  end

  defp same_counts(hops) do
    hops
    |> Enum.filter(&(&1.fr == &1.tr))
    |> Enum.reduce(%{}, fn hop, acc -> Map.update(acc, hop.fr, 1, &(&1 + 1)) end)
  end

  defp route_edges(edges, hops, by_id, ports, cols, ys) do
    grouped = Enum.group_by(hops, & &1.id)
    lanes = lane_index(hops)
    sames = same_index(hops)
    rails = assign_rails(hops, by_id, ports, cols, ys)
    same_n = same_counts(hops)

    Enum.map(edges, fn edge ->
      case Map.get(grouped, edge.id) do
        nil ->
          route_self(edge, by_id, ports)

        hs ->
          points =
            hs
            |> Enum.sort_by(& &1.seq)
            |> Enum.flat_map(&hop_points(&1, by_id, ports, cols, ys, lanes, sames, rails, same_n))
            |> drop_dupes()

          polyline(edge, points, 0, 0)
      end
    end)
  end

  # One vertical lane per cross-rank hop in a gap. Same-rank hops get their
  # own lanes so a fan-out beside one column does not push a long edge aside.
  defp lane_index(hops) do
    hops
    |> Enum.filter(&(&1.fr != &1.tr))
    |> Enum.group_by(fn hop -> min(hop.fr, hop.tr) end)
    |> Enum.flat_map(fn {_gap, group} -> index_group(group) end)
    |> Map.new()
  end

  defp same_index(hops) do
    hops
    |> Enum.filter(&(&1.fr == &1.tr))
    |> Enum.group_by(& &1.fr)
    |> Enum.flat_map(fn {_rank, group} -> index_group(group) end)
    |> Map.new()
  end

  defp index_group(group) do
    group
    |> Enum.sort_by(&{&1.id, &1.seq})
    |> Enum.with_index()
    |> Enum.map(fn {hop, i} -> {{hop.id, hop.seq}, i} end)
  end

  # The crossing of a hop runs at its own y. That y is not a port y in the
  # same gap, so a stub that leaves a node cannot lie on another edge's rail.
  defp assign_rails(hops, by_id, ports, cols, ys) do
    hops
    |> Enum.group_by(fn hop -> min(hop.fr, hop.tr) end)
    |> Enum.flat_map(fn {_gap, group} ->
      used =
        group
        |> Enum.flat_map(fn hop ->
          {sy, ty} = hop_ys(hop, by_id, ports, cols, ys)
          [sy, ty]
        end)
        |> MapSet.new()

      group
      |> Enum.filter(&(&1.fr != &1.tr))
      |> Enum.sort_by(&{&1.id, &1.seq})
      |> Enum.reduce({%{}, used}, fn hop, {acc, used} ->
        {sy, ty} = hop_ys(hop, by_id, ports, cols, ys)
        y = free_rail(div(sy + ty, 2), used)
        {Map.put(acc, {hop.id, hop.seq}, y), MapSet.put(used, y)}
      end)
      |> elem(0)
      |> Map.to_list()
    end)
    |> Map.new()
  end

  defp hop_ys(hop, by_id, ports, cols, ys) do
    if hop.fr == hop.tr do
      from = Map.fetch!(by_id, hop.from)
      to = Map.fetch!(by_id, hop.to)
      {_, sy} = port_at(from, ports, :right, hop.id, 0)
      {_, ty} = port_at(to, ports, :right, hop.id, 0)
      {sy, ty}
    else
      {_, sy} = start_point(hop, by_id, ports, cols, ys)
      {_, ty, _} = stop_point(hop, by_id, ports, cols, ys)
      {sy, ty}
    end
  end

  # `used` is finite, so some offset is free. The search steps outward by one.
  defp free_rail(mid, used) do
    0
    |> Stream.iterate(&(&1 + 1))
    |> Enum.find_value(fn n ->
      y = mid + rail_offset(n)
      if MapSet.member?(used, y), do: nil, else: y
    end)
  end

  defp rail_offset(0), do: 0

  defp rail_offset(n) do
    k = div(n + 1, 2)
    if rem(n, 2) == 1, do: k, else: -k
  end

  defp hop_points(hop, by_id, ports, cols, ys, lanes, sames, rails, same_n) do
    if hop.fr == hop.tr do
      from = Map.fetch!(by_id, hop.from)
      to = Map.fetch!(by_id, hop.to)
      {sx, sy} = port_at(from, ports, :right, hop.id, 0)
      {tx, ty} = port_at(to, ports, :right, hop.id, 0)
      lane = Map.get(sames, {hop.id, hop.seq}, 0)
      cx = cols[hop.fr].right + 4 + lane * @channel
      [sx, sy, cx, sy, cx, ty, tx, ty]
    else
      {sx, sy} = start_point(hop, by_id, ports, cols, ys)
      {tx, ty, extra} = stop_point(hop, by_id, ports, cols, ys)
      lane = Map.get(lanes, {hop.id, hop.seq}, 0)
      rail = Map.fetch!(rails, {hop.id, hop.seq})
      {jx1, jx2} = jog_xs(hop, cols, lane, Map.get(same_n, min(hop.fr, hop.tr), 0))
      [sx, sy, jx1, sy, jx1, rail, jx2, rail, jx2, ty, tx, ty] ++ extra
    end
  end

  # Left jog clears any same-rank channel. Right jog mirrors it, so the two
  # verticals of one hop never share an x with another hop in the gap.
  defp jog_xs(hop, cols, lane, same_count) do
    gap_l = cols[min(hop.fr, hop.tr)].right
    gap_r = cols[max(hop.fr, hop.tr)].left
    near = gap_l + 4 + same_count * @channel + lane * @channel
    far = gap_r - 4 - lane * @channel
    if hop.fr < hop.tr, do: {near, far}, else: {far, near}
  end

  defp start_point(hop, by_id, ports, cols, ys) do
    cond do
      bend?(hop.from) and hop.fr < hop.tr ->
        {cols[hop.fr].right, Map.fetch!(ys, hop.from)}

      bend?(hop.from) ->
        {cols[hop.fr].left, Map.fetch!(ys, hop.from)}

      hop.fr < hop.tr ->
        port_at(Map.fetch!(by_id, hop.from), ports, :right, hop.id, 0)

      true ->
        port_at(Map.fetch!(by_id, hop.from), ports, :left, hop.id, 0)
    end
  end

  defp stop_point(hop, by_id, ports, cols, ys) do
    cond do
      bend?(hop.to) and hop.fr < hop.tr ->
        y = Map.fetch!(ys, hop.to)
        col = cols[hop.tr]
        {col.left, y, [col.right, y]}

      bend?(hop.to) ->
        y = Map.fetch!(ys, hop.to)
        col = cols[hop.tr]
        {col.right, y, [col.left, y]}

      hop.fr < hop.tr ->
        {x, y} = port_at(Map.fetch!(by_id, hop.to), ports, :left, hop.id, 0)
        {x, y, []}

      true ->
        {x, y} = port_at(Map.fetch!(by_id, hop.to), ports, :right, hop.id, 0)
        {x, y, []}
    end
  end

  defp drop_dupes([x, y | rest]), do: drop_dupes(rest, x, y, [y, x])
  defp drop_dupes([], _x, _y, acc), do: Enum.reverse(acc)
  defp drop_dupes([x, y | rest], x, y, acc), do: drop_dupes(rest, x, y, acc)
  defp drop_dupes([x, y | rest], _px, _py, acc), do: drop_dupes(rest, x, y, [y, x | acc])

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

  defp polyline(edge, points, lx, ly) do
    [x, y | rest] = points
    legs = rest |> Enum.chunk_every(2) |> Enum.map_join(fn [px, py] -> " L #{px} #{py}" end)
    d = "M #{x} #{y}" <> legs

    %{edge | d: d, lx: lx, ly: max(ly, 12)}
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

  defp separate_labels(edges, nodes) do
    Enum.reduce(edges, [], fn edge, placed ->
      placed ++ [seat_label(edge, nodes, placed)]
    end)
  end

  defp seat_label(edge, nodes, placed) do
    {x, y} = label_anchor(edge)
    nudge_label(edge, x, y, nodes, placed, 0)
  end

  defp label_anchor(%{d: d, lx: lx, ly: ly}) do
    if String.contains?(d, " C "), do: {lx, ly}, else: path_midpoint(d)
  end

  defp nudge_label(edge, x, y, _nodes, _placed, n) when n > 48 do
    %{edge | lx: x, ly: max(y, 12)}
  end

  defp nudge_label(edge, x, y, nodes, placed, n) do
    {dx, dy} = spiral_at(n)
    candidate = %{edge | lx: x + dx, ly: max(y + dy, 12)}

    if label_clash?(candidate, nodes, placed) do
      nudge_label(edge, x, y, nodes, placed, n + 1)
    else
      candidate
    end
  end

  defp label_clash?(%{label: ""}, _nodes, _placed), do: false

  defp label_clash?(edge, nodes, placed) do
    box = label_box(edge)

    Enum.any?(placed, fn other ->
      other.label != "" and boxes_overlap?(label_box(other), box)
    end) or Enum.any?(nodes, &boxes_overlap?(box, &1))
  end

  defp spiral_at(0), do: {0, 0}

  defp spiral_at(n) do
    ring = div(n - 1, 8) + 1

    {dx, dy} =
      Enum.at(
        [{1, 0}, {1, 1}, {0, 1}, {-1, 1}, {-1, 0}, {-1, -1}, {0, -1}, {1, -1}],
        rem(n - 1, 8)
      )

    {dx * ring * 8, dy * ring * 8}
  end

  defp path_midpoint(d) do
    pts = path_pairs(d)

    case pts do
      [] ->
        {0, 0}

      [p] ->
        p

      _ ->
        segs = Enum.zip(pts, tl(pts))
        total = Enum.reduce(segs, 0, fn {a, b}, n -> n + manhattan(a, b) end)
        walk_mid(segs, div(total, 2))
    end
  end

  defp walk_mid([], {x, y}), do: {x, y}

  defp walk_mid([{{x1, y1}, {x2, y2}} | rest], left) do
    d = manhattan({x1, y1}, {x2, y2})

    cond do
      d == 0 and rest == [] ->
        {x2, y2}

      d == 0 ->
        walk_mid(rest, left)

      left <= d or rest == [] ->
        if x1 == x2 do
          {x1, y1 + div((y2 - y1) * left, d)}
        else
          {x1 + div((x2 - x1) * left, d), y1}
        end

      true ->
        walk_mid(rest, left - d)
    end
  end

  defp manhattan({x1, y1}, {x2, y2}), do: abs(x2 - x1) + abs(y2 - y1)

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

  defp text_w(text), do: max(String.length(to_string(text)), 1) * @char

  defp text_label(list) when is_list(list), do: Enum.join(list, " ")
  defp text_label(other), do: to_string(other)

  defp state_id(child) do
    child.id |> String.split("-") |> List.last()
  end
end

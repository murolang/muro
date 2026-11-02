defmodule MuroVisor.Draw do
  @moduledoc false

  alias Muro.Emit.Name

  @pad 16
  @node_gap 32
  @rank_gap 88
  @grid_gap 64
  @track 16
  @gutter 12
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
  with no use edges wraps into a wide grid. Each edge takes one track
  in the channel between two ranks, spread so edges into one node do
  not cross. A long edge bends at a dummy in every rank it crosses, and
  that dummy keeps the row the ordering gave it. The same book always
  yields the same coordinates.
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
    {segments, rank} = span_edges(edges, rank)
    counted = rough_ports(segments, edges)
    grown = Enum.map(nodes, &grow(&1, ports_of(counted, &1.id)))
    order = order_layers(grown, segments, rank)
    gaps = gap_counts(segments)
    {stacked, cols, ys} = stack_ranks(order, Map.new(grown, &{&1.id, &1}), edges, gaps)
    placed = %{nodes: stacked, cols: cols, ys: ys}
    shifts = rank_shifts(order, placed, counted)
    placed = apply_rank_shifts(placed, shifts, order)
    ports = ordered_ports(segments, edges, placed)
    routed = route_all(edges, segments, placed, ports, gaps, order)
    routed = separate_labels(routed, placed.nodes)
    index = Map.new(Enum.with_index(nodes), fn {node, i} -> {node.id, i} end)
    stacked = Enum.sort_by(placed.nodes, &Map.fetch!(index, &1.id))
    Map.merge(bounds(stacked, routed), %{nodes: stacked, edges: routed})
  end

  # A long edge is one segment per pair of adjacent ranks. The intermediate
  # point is a dummy that the barycenter orders with the nodes of that rank.
  defp span_edges(edges, rank) do
    Enum.flat_map_reduce(edges, rank, fn edge, rank ->
      if edge.from == edge.to do
        {[], rank}
      else
        segment_chain(edge, Map.fetch!(rank, edge.from), Map.fetch!(rank, edge.to), rank)
      end
    end)
  end

  defp segment_chain(edge, r, r, rank) do
    {[%{id: edge.id, seq: 0, kind: :same, a: edge.from, b: edge.to, rank: r}], rank}
  end

  defp segment_chain(edge, r1, r2, rank) do
    step = if r1 < r2, do: 1, else: -1
    between = r1..r2//step |> Enum.to_list() |> tl() |> Enum.drop(-1)

    {dummies, rank} =
      Enum.map_reduce(between, rank, fn r, rank ->
        id = {:bend, edge.id, r}
        {id, Map.put(rank, id, r)}
      end)

    verts = [edge.from | dummies] ++ [edge.to]

    segs =
      verts
      |> Enum.zip(tl(verts))
      |> Enum.with_index()
      |> Enum.map(fn {{u, v}, i} ->
        ru = Map.fetch!(rank, u)
        rv = Map.fetch!(rank, v)

        if ru < rv do
          %{id: edge.id, seq: i, kind: :cross, left: u, right: v, lr: ru, rr: rv, dir: :fwd}
        else
          %{id: edge.id, seq: i, kind: :cross, left: v, right: u, lr: rv, rr: ru, dir: :back}
        end
      end)

    {segs, rank}
  end

  defp rough_ports(segments, edges) do
    acc =
      Enum.reduce(segments, %{}, fn
        %{kind: :same, id: id, a: a, b: b}, acc ->
          acc |> push_port(a, :right, id) |> push_port(b, :right, id)

        %{kind: :cross, id: id, left: left, right: right}, acc ->
          acc |> maybe_push(left, :right, id) |> maybe_push(right, :left, id)
      end)

    Enum.reduce(edges, acc, fn edge, acc ->
      if edge.from == edge.to do
        acc |> push_port(edge.from, :top, edge.id) |> push_port(edge.from, :top, edge.id)
      else
        acc
      end
    end)
  end

  defp maybe_push(acc, {:bend, _, _}, _side, _edge), do: acc
  defp maybe_push(acc, id, side, edge), do: push_port(acc, id, side, edge)

  defp order_layers(nodes, segments, rank) do
    ids =
      nodes
      |> Enum.group_by(&Map.fetch!(rank, &1.id))
      |> Map.new(fn {r, ns} -> {r, ns |> Enum.map(& &1.id) |> Enum.sort()} end)

    dummies =
      segments
      |> Enum.flat_map(fn
        %{kind: :cross, left: left, right: right} -> [left, right]
        _ -> []
      end)
      |> Enum.filter(&bend?/1)
      |> Enum.uniq()

    ids =
      Enum.reduce(dummies, ids, fn {:bend, _, r} = id, ids ->
        Map.update(ids, r, [id], fn list ->
          if id in list, do: list, else: list ++ [id]
        end)
      end)

    dag =
      segments
      |> Enum.flat_map(fn
        %{kind: :cross, left: left, right: right} -> [{left, right}]
        _ -> []
      end)
      |> Enum.uniq()

    bary_sweeps(ids, dag)
  end

  defp bend?({:bend, _, _}), do: true
  defp bend?(_), do: false

  defp gap_counts(segments) do
    Enum.reduce(segments, %{same: %{}, cross: %{}}, fn
      %{kind: :same, rank: r}, acc ->
        %{acc | same: Map.update(acc.same, r, 1, &(&1 + 1))}

      %{kind: :cross, lr: r}, acc ->
        %{acc | cross: Map.update(acc.cross, r, 1, &(&1 + 1))}
    end)
  end

  defp stack_ranks(order, by_id, edges, gaps) do
    ranks = order |> Map.keys() |> Enum.sort()
    last = List.last(ranks)

    Enum.reduce(ranks, {[], %{}, %{}, @pad}, fn r, {nodes, cols, ys, x} ->
      ids = Map.get(order, r, [])
      width = column_width(ids, by_id)
      {col_nodes, ys, bottom} = stack_ids(ids, by_id, edges, ys, x)
      gap = gap_width(gaps, r, r != last)
      col = %{left: x, right: x + width, bottom: bottom}
      {nodes ++ col_nodes, Map.put(cols, r, col), ys, x + width + gap}
    end)
    |> then(fn {nodes, cols, ys, _x} -> {nodes, cols, ys} end)
  end

  defp column_width(ids, by_id) do
    ids
    |> Enum.reject(&bend?/1)
    |> Enum.map(&Map.fetch!(by_id, &1).w)
    |> Enum.max(fn -> 1 end)
  end

  # Dummies keep the crossing-reduction order. Ones the ordering places
  # past the first or last node move into the nearest gap, still in that
  # order, so a long edge crosses the column beside the nodes.
  defp stack_ids(ids, by_id, edges, ys, x) do
    {gaps, reals} = bucket_dummies(ids)
    n = length(reals)
    gaps = if n >= 2, do: tuck_outside(gaps, n), else: gaps

    {nodes, ys, y} =
      Enum.reduce(Enum.with_index(reals), {[], ys, @pad}, fn {id, i}, {nodes, ys, y} ->
        above = if i == 0, do: Map.get(gaps, 0, []), else: []
        {ys, used} = occupy(above, ys, y, :compact)
        y = y + used + if(above == [], do: 0, else: 4)

        node = Map.fetch!(by_id, id)
        y = y + loop_count(id, edges) * @loop_band
        node = %{node | x: x, y: y}
        bottom = y + node.h
        below = Map.get(gaps, i + 1, [])
        mode = if n < 2, do: :compact, else: :spread
        {ys, used} = occupy(below, ys, bottom + 4, mode)
        advance = if below == [], do: @node_gap, else: max(@node_gap, used + 8)
        {[node | nodes], ys, bottom + advance}
      end)

    {Enum.reverse(nodes), ys, y}
  end

  defp bucket_dummies(ids) do
    {gaps, reals, _gi} =
      Enum.reduce(ids, {%{}, [], 0}, fn id, {gaps, reals, gi} ->
        if bend?(id) do
          {Map.update(gaps, gi, [id], &(&1 ++ [id])), reals, gi}
        else
          {gaps, reals ++ [id], gi + 1}
        end
      end)

    {gaps, reals}
  end

  defp tuck_outside(gaps, n) do
    lead = Map.get(gaps, 0, [])
    trail = Map.get(gaps, n, [])

    gaps
    |> Map.delete(0)
    |> Map.delete(n)
    |> Map.update(1, lead, &(lead ++ &1))
    |> Map.update(n - 1, trail, &(&1 ++ trail))
  end

  defp occupy([], ys, _y, _mode), do: {ys, 0}

  defp occupy(ids, ys, y, mode) do
    step = dummy_step(mode, length(ids))

    ys =
      Enum.reduce(Enum.with_index(ids), ys, fn {id, i}, ys ->
        Map.put(ys, id, y + i * step)
      end)

    {ys, length(ids) * step}
  end

  defp dummy_step(:spread, _n), do: @track
  defp dummy_step(:compact, n) when n <= 1, do: @track
  defp dummy_step(:compact, n), do: max(min(@track, div(140, n)), 1)

  # The strip beside a rank holds same-rank edges. The rest of the gap is
  # the channel, wide enough for one track per edge that crosses it.
  defp gap_width(gaps, r, has_next) do
    same_n = Map.get(gaps.same, r, 0)
    cross_n = Map.get(gaps.cross, r, 0)

    strip_width(same_n) +
      cond do
        cross_n > 0 -> channel_width(cross_n)
        has_next -> @rank_gap
        true -> 0
      end
  end

  defp strip_width(0), do: 0
  defp strip_width(n), do: channel_width(n)
  defp channel_width(n) when n <= 1, do: @rank_gap
  defp channel_width(n), do: max(@rank_gap, 2 * @gutter + (n - 1) * @track)

  defp ordered_ports(segments, edges, placed) do
    attachments =
      Enum.flat_map(segments, fn
        %{kind: :same, id: id, a: a, b: b} ->
          [{a, :right, id, vertex_pos(b, placed)}, {b, :right, id, vertex_pos(a, placed)}]

        %{kind: :cross, id: id, left: left, right: right} ->
          port_ends(left, :right, right, id, placed) ++ port_ends(right, :left, left, id, placed)
      end)

    loops =
      for edge <- edges, edge.from == edge.to do
        {edge.from, :top, edge.id, {0, edge.id}}
      end

    (attachments ++ loops ++ loops)
    |> Enum.group_by(fn {node, side, _id, _key} -> {node, side} end)
    |> Enum.reduce(%{}, fn {{node, side}, group}, acc ->
      ids =
        group
        |> Enum.sort_by(fn {_node, _side, id, key} -> {key, id} end)
        |> Enum.map(fn {_node, _side, id, _key} -> id end)

      acc
      |> Map.put_new(node, empty_ports())
      |> put_in([node, side], ids)
    end)
  end

  defp port_ends({:bend, _, _}, _side, _other, _id, _placed), do: []

  defp port_ends(node, side, other, id, placed) do
    [{node, side, id, vertex_pos(other, placed)}]
  end

  defp vertex_pos({:bend, _, _} = id, placed) do
    {Map.fetch!(placed.ys, id), vertex_sort_key(id)}
  end

  defp vertex_pos(id, placed) do
    node = Enum.find(placed.nodes, &(&1.id == id))
    {node.y + div(node.h, 2), vertex_sort_key(id)}
  end

  defp vertex_sort_key({:bend, edge, r}), do: {:bend, edge, r}
  defp vertex_sort_key(id), do: {:node, id}

  # Port rows in a rank are at least a track apart, so a small shift makes
  # the horizontal stubs of two adjacent ranks miss each other.
  defp rank_shifts(order, placed, ports) do
    ranks = order |> Map.keys() |> Enum.sort()

    ranks
    |> Enum.reduce({%{}, MapSet.new()}, fn r, {shifts, prev} ->
      ys = rank_ys(r, order, placed, ports)
      k = disjoint_shift(ys, prev)
      {Map.put(shifts, r, k), MapSet.new(Enum.map(ys, &(&1 + k)))}
    end)
    |> elem(0)
  end

  defp rank_ys(r, order, placed, ports) do
    by_id = Map.new(placed.nodes, &{&1.id, &1})

    Enum.flat_map(Map.get(order, r, []), fn
      {:bend, _, _} = id ->
        [Map.fetch!(placed.ys, id)]

      id ->
        node = Map.fetch!(by_id, id)

        for {side, list} <- ports_of(ports, id), i <- 0..(length(list) - 1)//1 do
          {_x, y} = side_point(node, side, i, length(list))
          y
        end
    end)
    |> Enum.uniq()
  end

  defp disjoint_shift(_ys, prev) when prev == %MapSet{}, do: 0
  defp disjoint_shift([], _prev), do: 0

  defp disjoint_shift(ys, prev) do
    limit = max(Enum.max(prev) - Enum.min(ys) + 1, 0)

    Enum.find(0..limit, limit, fn k ->
      Enum.all?(ys, &(not MapSet.member?(prev, &1 + k)))
    end)
  end

  defp apply_rank_shifts(placed, shifts, order) do
    rank_of =
      Enum.reduce(order, %{}, fn {r, ids}, acc ->
        Enum.reduce(ids, acc, &Map.put(&2, &1, r))
      end)

    nodes =
      Enum.map(placed.nodes, fn node ->
        %{node | y: node.y + Map.fetch!(shifts, Map.fetch!(rank_of, node.id))}
      end)

    ys =
      Map.new(placed.ys, fn {id, y} ->
        {id, y + Map.fetch!(shifts, Map.fetch!(rank_of, id))}
      end)

    %{placed | nodes: nodes, ys: ys}
  end

  defp route_all(edges, segments, placed, ports, gaps, order) do
    by_id = Map.new(placed.nodes, &{&1.id, &1})
    grouped = Enum.group_by(segments, & &1.id)
    tracks = track_table(segments, placed, gaps, order)

    Enum.map(edges, fn edge ->
      if edge.from == edge.to do
        route_self(edge, by_id, ports)
      else
        points =
          grouped
          |> Map.get(edge.id, [])
          |> Enum.sort_by(& &1.seq)
          |> Enum.map(&segment_points(&1, by_id, placed, ports, tracks))
          |> stitch()

        polyline(edge, flatten_points(points), 0, 0)
      end
    end)
  end

  # Tracks run across the channel in source order, then target order.
  # Edges that enter one node therefore meet it without crossing.
  defp track_table(segments, placed, gaps, order) do
    index = Map.new(order, fn {r, ids} -> {r, index_map(ids)} end)

    cross =
      segments
      |> Enum.filter(&(&1.kind == :cross))
      |> Enum.group_by(& &1.lr)
      |> Enum.flat_map(fn {lr, group} ->
        xs = cross_xs(placed.cols[lr], Map.get(gaps.same, lr, 0), length(group))

        group
        |> Enum.sort_by(fn seg ->
          {index[seg.lr][seg.left], index[seg.rr][seg.right], seg.id, seg.seq}
        end)
        |> Enum.with_index()
        |> Enum.map(fn {seg, i} -> {{seg.id, seg.seq}, Enum.at(xs, i)} end)
      end)

    same =
      segments
      |> Enum.filter(&(&1.kind == :same))
      |> Enum.group_by(& &1.rank)
      |> Enum.flat_map(fn {r, group} ->
        xs = same_xs(placed.cols[r], length(group))
        idx = Map.fetch!(index, r)

        group
        |> Enum.sort_by(fn seg ->
          {min(idx[seg.a], idx[seg.b]), max(idx[seg.a], idx[seg.b]), seg.id}
        end)
        |> Enum.with_index()
        |> Enum.map(fn {seg, i} -> {{seg.id, seg.seq}, Enum.at(xs, i)} end)
      end)

    Map.new(cross ++ same)
  end

  defp cross_xs(col, same_n, cross_n) do
    spread(col.right + strip_width(same_n), channel_width(cross_n), cross_n)
  end

  defp same_xs(col, same_n), do: spread(col.right, strip_width(same_n), same_n)

  defp spread(_left, _width, 0), do: []
  defp spread(left, width, 1), do: [left + div(width, 2)]

  defp spread(left, width, n) do
    inner = max(width - 2 * @gutter, n - 1)

    Enum.map(0..(n - 1), fn i ->
      left + @gutter + div(i * inner, n - 1)
    end)
  end

  defp segment_points(%{kind: :same} = seg, by_id, _placed, ports, tracks) do
    {ax, ay} = port_at(Map.fetch!(by_id, seg.a), ports, :right, seg.id, 0)
    {bx, by} = port_at(Map.fetch!(by_id, seg.b), ports, :right, seg.id, 0)
    x = Map.fetch!(tracks, {seg.id, seg.seq})
    [{ax, ay}, {x, ay}, {x, by}, {bx, by}]
  end

  defp segment_points(%{kind: :cross} = seg, by_id, placed, ports, tracks) do
    {lx, ly} = anchor(seg.left, :right, seg.id, by_id, placed, ports)
    {rx, ry} = anchor(seg.right, :left, seg.id, by_id, placed, ports)
    x = Map.fetch!(tracks, {seg.id, seg.seq})
    points = [{lx, ly}, {x, ly}, {x, ry}, {rx, ry}]
    if seg.dir == :back, do: Enum.reverse(points), else: points
  end

  defp anchor({:bend, _, r} = id, side, _edge, _by_id, placed, _ports) do
    col = Map.fetch!(placed.cols, r)
    y = Map.fetch!(placed.ys, id)
    x = if side == :left, do: col.left, else: col.right
    {x, y}
  end

  defp anchor(id, side, edge, by_id, _placed, ports) do
    port_at(Map.fetch!(by_id, id), ports, side, edge, 0)
  end

  defp stitch([]), do: []

  defp stitch([first | rest]) do
    Enum.reduce(rest, first, fn chunk, acc -> join_points(acc, chunk) end)
  end

  defp join_points(acc, [first | rest]) do
    acc = if List.last(acc) == first, do: acc, else: acc ++ [first]
    acc ++ rest
  end

  defp flatten_points(points), do: Enum.flat_map(points, fn {x, y} -> [x, y] end)

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

  defp slot(len, _i, n) when n <= 1, do: div(len, 2)

  defp slot(len, i, n) do
    span = max(len - 2 * @inset, n - 1)
    @inset + div(i * span, n - 1)
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

  defp bary_sweeps(order, _dag) when map_size(order) <= 1, do: order

  defp bary_sweeps(order, dag) do
    max_r = order |> Map.keys() |> Enum.max()
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
      {key, vertex_sort_key(id)}
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

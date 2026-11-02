defmodule MuroVisor.Pack do
  @moduledoc false

  # One cluster per base session, then a grid that fills a wide pane.
  # Session nodes sit on the left. Everything else in the cluster is one
  # column on the right, so a step or a dual is a short line inside the
  # cluster instead of a run across the book.

  @pad 8
  @gap 4
  @track 8
  @simple_h 24
  @channel 16
  @grid_gap 12
  @grid_pad 12

  def assign(nodes, edges) do
    duals = MapSet.new(for edge <- edges, edge.use == :dual, do: edge.from)

    bases =
      Enum.filter(nodes, fn node ->
        node.kind == "session" and not MapSet.member?(duals, node.id)
      end)

    {groups, assigned} =
      Enum.map_reduce(bases, MapSet.new(), fn base, assigned ->
        members = members(base, nodes, edges, assigned)
        ids = MapSet.new(members, & &1.id)
        {%{name: base.bare, nodes: members, ids: ids}, MapSet.union(assigned, ids)}
      end)

    rest = Enum.reject(nodes, &MapSet.member?(assigned, &1.id))

    if rest == [] do
      groups
    else
      groups ++
        [%{name: "other", nodes: rest, ids: MapSet.new(rest, & &1.id)}]
    end
  end

  def cluster(%{name: name, nodes: nodes, edges: edges}) do
    {left, right} = Enum.split_with(nodes, &(&1.kind == "session"))
    left = order_left(left, name)
    right = order_right(right)
    nodes = place(left, right, edges)
    by_id = Map.new(nodes, &{&1.id, &1})
    drawn = route(edges, by_id)
    frame(nodes, drawn) |> Map.put(:name, name)
  end

  def arrange([], _cross, _score), do: {[], [], @grid_pad * 2, @grid_pad * 2}

  def arrange(pictures, cross, score) do
    {_score, placed, width, height} =
      1..length(pictures)
      |> Enum.reduce(nil, fn cols, best ->
        {placed, w, h} = grid(pictures, cols)
        candidate = {score.(w, h), placed, w, h}

        case best do
          nil -> candidate
          {s0, _, _, _} when elem(candidate, 0) > s0 -> candidate
          _ -> best
        end
      end)

    nodes =
      Enum.flat_map(placed, fn {picture, dx, dy} ->
        Enum.map(picture.nodes, fn node ->
          node |> shift_node(dx, dy) |> Map.put(:cluster, picture.name)
        end)
      end)

    edges =
      Enum.flat_map(placed, fn {picture, dx, dy} ->
        Enum.map(picture.edges, &shift_edge(&1, dx, dy))
      end)

    by_id = Map.new(nodes, &{&1.id, &1})

    foreign =
      Enum.filter(cross, fn edge ->
        Map.has_key?(by_id, edge.from) and Map.has_key?(by_id, edge.to)
      end)

    {nodes, edges ++ route_cross(foreign, by_id, occupied(edges)), width, height}
  end

  defp members(base, nodes, edges, assigned) do
    duals =
      for edge <- edges,
          edge.use == :dual,
          edge.to == base.id,
          not MapSet.member?(assigned, edge.from),
          do: edge.from

    sessions = [base.id | duals]

    conforms =
      for edge <- edges,
          edge.use == :step,
          edge.to in sessions,
          not MapSet.member?(assigned, edge.from),
          do: edge.from

    chosen = MapSet.new(sessions ++ conforms)

    meetings =
      for edge <- edges,
          edge.use == :meet,
          MapSet.member?(chosen, edge.to) or MapSet.member?(chosen, edge.from) do
        if MapSet.member?(chosen, edge.to), do: edge.from, else: edge.to
      end

    ids =
      [base.id | duals ++ conforms ++ meetings]
      |> Enum.reject(&MapSet.member?(assigned, &1))
      |> Enum.uniq()

    Enum.filter(nodes, &(&1.id in ids))
  end

  defp order_left(nodes, name) do
    {base, rest} = Enum.split_with(nodes, &(&1.bare == name))
    base ++ Enum.sort_by(rest, & &1.bare)
  end

  defp order_right(nodes), do: nodes

  defp place(left, right, edges) do
    left = Enum.map(left, &prepare_side(&1, :left, edges, left, right))
    right = Enum.map(right, &prepare_side(&1, :right, edges, left, right))
    left_w = column_w(left)
    {right, _y} = place_column(right, @pad + left_w + @channel, @pad, @gap)
    right_h = stack_span(right)
    left = fit_left(left, right_h)
    {left, _} = place_column(left, @pad, @pad, @gap)
    extra = channel_extra(left ++ right, edges)
    right = Enum.map(right, fn node -> %{node | x: node.x + extra} end)
    left ++ right
  end

  defp prepare_side(node, side, edges, left, right) do
    node = if node.meetings == [], do: %{node | h: @simple_h}, else: node
    same = if side == :left, do: left, else: right
    counts = side_counts(node, edges, same, side)
    node = reserve(node, counts)
    Map.put(node, :side, side)
  end

  defp side_counts(node, edges, same, side) do
    ids = Enum.map(same, & &1.id)
    index = Map.new(Enum.with_index(ids), fn {id, i} -> {id, i} end)
    mine = Map.get(index, node.id)

    Enum.reduce(edges, %{left: 0, right: 0, top: 0, bottom: 0}, fn edge, acc ->
      other = other_end(edge, node.id)

      cond do
        other == nil or other == node.id ->
          acc

        Map.has_key?(index, other) ->
          gap = abs(Map.fetch!(index, other) - mine)
          key = if gap <= 1, do: vertical_side(index[other], mine), else: outer_side(side)
          Map.update!(acc, key, &(&1 + 1))

        true ->
          key = if side == :left, do: :right, else: :left
          Map.update!(acc, key, &(&1 + 1))
      end
    end)
  end

  defp other_end(%{from: id, to: other}, id), do: other
  defp other_end(%{from: other, to: id}, id), do: other
  defp other_end(_edge, _id), do: nil

  defp vertical_side(other_i, mine) when other_i < mine, do: :top
  defp vertical_side(_other_i, _mine), do: :bottom

  defp outer_side(:left), do: :left
  defp outer_side(:right), do: :right

  defp reserve(node, counts) do
    %{
      node
      | h: max(node.h, side_need(max(counts.left, counts.right))),
        w: max(node.w, side_need(max(counts.top, counts.bottom)))
    }
  end

  defp side_need(n) when n <= 1, do: 0
  defp side_need(n), do: 12 + (n - 1) * @track

  defp column_w([]), do: 0

  defp column_w(nodes) do
    nodes |> Enum.map(& &1.w) |> Enum.max()
  end

  defp place_column(nodes, x, y, gap) do
    Enum.map_reduce(nodes, y, fn node, y ->
      {%{node | x: x, y: y}, y + node.h + gap}
    end)
  end

  defp stack_span([]), do: 0

  defp stack_span(nodes) do
    top = Enum.min(Enum.map(nodes, & &1.y))
    bottom = Enum.max(Enum.map(nodes, &(&1.y + &1.h)))
    bottom - top
  end

  # The base session grows so the right column's ports land on it.
  defp fit_left([], _right_h), do: []

  defp fit_left([base | rest], right_h) do
    rest_h =
      Enum.reduce(rest, 0, fn node, h ->
        h + @gap + node.h
      end)

    base_h = max(base.h, right_h - rest_h)
    [%{base | h: max(base_h, base.h)} | rest]
  end

  defp channel_extra(nodes, edges) do
    by_id = Map.new(nodes, &{&1.id, &1})
    elbows = Enum.count(edges, &elbow?(&1, by_id))
    need = if elbows <= 1, do: @channel, else: 8 + elbows * @track
    max(need - @channel, 0)
  end

  defp elbow?(edge, by_id) do
    a = Map.get(by_id, edge.from)
    b = Map.get(by_id, edge.to)

    a != nil and b != nil and a.id != b.id and a.side != b.side and
      not straight?(a, b)
  end

  defp straight?(a, b) do
    {right, left} = if a.side == :right, do: {a, b}, else: {b, a}
    y = right.y + div(right.h, 2)
    y >= left.y and y <= left.y + left.h
  end

  defp draw_edge(edge, by_id, groups) do
    a = Map.fetch!(by_id, edge.from)
    b = Map.fetch!(by_id, edge.to)

    cond do
      a.id == b.id ->
        loop_edge(edge, a, groups)

      a.side != b.side ->
        across_edge(edge, a, b, groups, by_id)

      true ->
        column_edge(edge, a, b, groups, by_id)
    end
  end

  defp loop_edge(edge, node, groups) do
    k = Enum.find_index(Map.get(groups, {:loop, node.id}, [edge.id]), &(&1 == edge.id)) || 0
    x1 = node.x + slot(node.w, 0, 2)
    x2 = node.x + slot(node.w, 1, 2)
    y = node.y
    cy = y - 16 - k * 12

    %{
      edge
      | d: "M #{x1} #{y} C #{x1} #{cy} #{x2} #{cy} #{x2} #{y}",
        lx: x1,
        ly: max(cy + 12, 12)
    }
  end

  defp across_edge(edge, a, b, groups, by_id) do
    if straight?(a, b) do
      {right, left} = if a.side == :right, do: {a, b}, else: {b, a}
      y = right.y + div(right.h, 2)
      x_r = right.x
      x_l = left.x + left.w
      {x1, x2} = if a.side == :right, do: {x_r, x_l}, else: {x_l, x_r}
      segment(edge, x1, y, x2, y)
    else
      elbow(edge, a, b, groups, by_id)
    end
  end

  defp elbow(edge, a, b, groups, by_id) do
    ids = Map.get(groups, :elbow, []) |> Enum.reverse()
    i = Enum.find_index(ids, &(&1 == edge.id)) || 0
    {right, left} = if a.side == :right, do: {a, b}, else: {b, a}
    y1 = right.y + div(right.h, 2)
    y2 = left.y + port_y(left, edge.id, :right, groups)
    track = column_right(by_id, :left) + 4 + i * @track
    x_l = left.x + left.w
    x_r = right.x

    points =
      if a.side == :right do
        [{x_r, y1}, {track, y1}, {track, y2}, {x_l, y2}]
      else
        [{x_l, y2}, {track, y2}, {track, y1}, {x_r, y1}]
      end

    polyline(edge, points)
  end

  defp column_edge(edge, a, b, groups, by_id) do
    {upper, lower} = if a.y <= b.y, do: {a, b}, else: {b, a}
    adjacent = lower.y <= upper.y + upper.h + @gap + 1

    if adjacent do
      x = shared_x(upper, lower, edge.id, groups)
      points = [{x, upper.y + upper.h}, {x, lower.y}]
      points = if a.y <= b.y, do: points, else: Enum.reverse(points)
      polyline(edge, points)
    else
      skip_curve(edge, a, b, upper, groups, by_id)
    end
  end

  # A jump past another node bows out as a curve. The curve has no straight
  # run, so it does not need a channel wider than the layer test allows.
  defp skip_curve(edge, a, b, upper, groups, by_id) do
    i = Map.get(groups, {:track, edge.id}, 0)
    margin = if upper.side == :right, do: 1, else: -1
    bow = outer_x(column_right(by_id, upper.side), upper.x, margin, i)
    side = side_of(margin)
    y1 = a.y + port_y(a, edge.id, side, groups)
    y2 = b.y + port_y(b, edge.id, side, groups)
    x1 = if margin > 0, do: a.x + a.w, else: a.x
    x2 = if margin > 0, do: b.x + b.w, else: b.x

    %{
      edge
      | d: "M #{x1} #{y1} C #{bow} #{y1} #{bow} #{y2} #{x2} #{y2}",
        lx: bow,
        ly: max(div(y1 + y2, 2), 12)
    }
  end

  defp side_of(1), do: :right
  defp side_of(_), do: :left

  defp column_right(by_id, side) do
    by_id
    |> Map.values()
    |> Enum.filter(&(&1.side == side))
    |> Enum.map(&(&1.x + &1.w))
    |> Enum.max(fn -> 0 end)
  end

  defp outer_x(right_edge, _left_x, 1, i), do: right_edge + 4 + i * @track
  defp outer_x(_right_edge, left_x, _, i), do: left_x - 4 - i * @track

  defp port_y(node, edge_id, side, groups) do
    ids = ports_on(node, side, groups)
    i = Enum.find_index(ids, &(&1 == edge_id)) || 0
    slot(node.h, i, max(length(ids), 1))
  end

  defp shared_x(upper, lower, edge_id, groups) do
    left = max(upper.x, lower.x)
    right = min(upper.x + upper.w, lower.x + lower.w)
    ids = ports_on(upper, :bottom, groups)
    i = Enum.find_index(ids, &(&1 == edge_id)) || 0
    left + slot(max(right - left, 1), i, max(length(ids), 1))
  end

  defp ports_on(node, side, groups) do
    Map.get(groups, {node.id, side}, [node.id])
    |> Enum.reverse()
    |> Enum.uniq()
  end

  # The group map built above does not record per-node ports. Record them
  # by walking the same decisions, so two edges never share a point.
  defp route(edges, by_id) do
    groups = edges |> port_groups(by_id) |> put_skip_tracks(edges, by_id)

    Enum.map(edges, fn edge ->
      draw_edge(edge, by_id, groups)
    end)
  end

  # Skip edges share an outside track when their vertical spans miss.
  # One pass over the finite skip list; a new track is opened only when
  # every earlier track is busy.
  defp put_skip_tracks(groups, edges, by_id) do
    by_edge = Map.new(edges, &{&1.id, &1})

    Enum.reduce([:left, :right], groups, fn side, groups ->
      ids = Map.get(groups, {:skip, side}, []) |> Enum.reverse()

      spans =
        Enum.map(ids, fn id ->
          edge = Map.fetch!(by_edge, id)
          a = Map.fetch!(by_id, edge.from)
          b = Map.fetch!(by_id, edge.to)
          {upper, lower} = if a.y <= b.y, do: {a, b}, else: {b, a}
          margin = if side == :right, do: 1, else: -1
          y1 = upper.y + port_y(upper, id, side_of(margin), groups)
          y2 = lower.y + port_y(lower, id, side_of(margin), groups)
          {id, min(y1, y2), max(y1, y2)}
        end)

      Enum.reduce(assign_tracks(spans), groups, fn {id, i}, groups ->
        Map.put(groups, {:track, id}, i)
      end)
    end)
  end

  defp assign_tracks(spans) do
    {assigned, _tracks} =
      Enum.map_reduce(spans, [], fn {id, y1, y2}, tracks ->
        free =
          Enum.find_index(tracks, fn used ->
            Enum.all?(used, fn {a, b} -> y2 < a or b < y1 end)
          end)

        i = free || length(tracks)

        tracks =
          if free == nil do
            tracks ++ [[{y1, y2}]]
          else
            List.update_at(tracks, i, &[{y1, y2} | &1])
          end

        {{id, i}, tracks}
      end)

    assigned
  end

  defp port_groups(edges, by_id) do
    Enum.reduce(edges, %{}, fn edge, acc ->
      a = Map.get(by_id, edge.from)
      b = Map.get(by_id, edge.to)

      cond do
        a == nil or b == nil ->
          acc

        a.id == b.id ->
          Map.update(acc, {:loop, a.id}, [edge.id], &[edge.id | &1])

        a.side != b.side ->
          {right, left} = if a.side == :right, do: {a, b}, else: {b, a}

          acc =
            acc
            |> push_port(right.id, :left, edge.id)
            |> push_port(left.id, :right, edge.id)

          if straight?(a, b), do: acc, else: Map.update(acc, :elbow, [edge.id], &[edge.id | &1])

        true ->
          {upper, lower} = if a.y <= b.y, do: {a, b}, else: {b, a}
          adjacent = lower.y <= upper.y + upper.h + @gap + 1

          if adjacent do
            acc
            |> push_port(upper.id, :bottom, edge.id)
            |> push_port(lower.id, :top, edge.id)
          else
            side = if upper.side == :right, do: :right, else: :left

            acc
            |> Map.update({:skip, upper.side}, [edge.id], &[edge.id | &1])
            |> push_port(upper.id, side, edge.id)
            |> push_port(lower.id, side, edge.id)
          end
      end
    end)
  end

  defp push_port(acc, id, side, edge_id) do
    Map.update(acc, {id, side}, [edge_id], &[edge_id | &1])
  end

  defp slot(len, _i, n) when n <= 1, do: div(len, 2)

  defp slot(len, i, n) do
    inset = min(6, div(max(len, 1), 4))
    room = max(len - 2 * inset, 0)
    span = min(max(room, n - 1), max((n - 1) * @track, n - 1))
    pos = inset + div(i * span, n - 1)
    min(max(pos, 0), max(len, 1) - 1)
  end

  defp segment(edge, x1, y1, x2, y2) do
    polyline(edge, [{x1, y1}, {x2, y2}])
  end

  defp polyline(edge, points) do
    [{x, y} | rest] = points

    d =
      "M #{x} #{y}" <>
        Enum.map_join(rest, "", fn {px, py} -> " L #{px} #{py}" end)

    %{edge | d: d, lx: x, ly: max(y, 12)}
  end

  defp frame(nodes, edges) do
    pts =
      Enum.flat_map(nodes, fn node ->
        [{node.x, node.y}, {node.x + node.w, node.y + node.h}]
      end) ++ Enum.flat_map(edges, &path_points(&1.d))

    min_x = pts |> Enum.map(&elem(&1, 0)) |> Enum.min(fn -> 0 end)
    min_y = pts |> Enum.map(&elem(&1, 1)) |> Enum.min(fn -> 0 end)
    max_x = pts |> Enum.map(&elem(&1, 0)) |> Enum.max(fn -> @pad end)
    max_y = pts |> Enum.map(&elem(&1, 1)) |> Enum.max(fn -> @pad end)
    dx = max(0, @pad - min_x)
    dy = max(0, @pad - min_y)
    nodes = Enum.map(nodes, &shift_node(&1, dx, dy))
    edges = Enum.map(edges, &shift_edge(&1, dx, dy))

    %{
      width: max(max_x + dx + @pad, @pad * 2),
      height: max(max_y + dy + @pad, @pad * 2),
      nodes: nodes,
      edges: edges
    }
  end

  defp grid(pictures, cols) do
    rows = Enum.chunk_every(pictures, cols)
    widths = column_widths(rows, cols)
    heights = Enum.map(rows, fn row -> row |> Enum.map(& &1.height) |> Enum.max() end)
    xs = offsets(widths, @grid_pad, @grid_gap)
    ys = offsets(heights, @grid_pad, @grid_gap)

    placed =
      Enum.flat_map(Enum.with_index(rows), fn {row, r} ->
        Enum.map(Enum.with_index(row), fn {picture, c} ->
          {picture, Enum.at(xs, c), Enum.at(ys, r)}
        end)
      end)

    w = @grid_pad + Enum.sum(widths) + @grid_gap * max(length(widths) - 1, 0) + @grid_pad
    h = @grid_pad + Enum.sum(heights) + @grid_gap * max(length(heights) - 1, 0) + @grid_pad
    {placed, w, h}
  end

  defp column_widths(rows, cols) do
    Enum.map(0..(cols - 1), fn c ->
      rows
      |> Enum.map(&Enum.at(&1, c))
      |> Enum.reject(&is_nil/1)
      |> Enum.map(& &1.width)
      |> Enum.max()
    end)
  end

  defp offsets(sizes, pad, gap) do
    Enum.reduce(sizes, {[], pad}, fn size, {acc, cursor} ->
      {acc ++ [cursor], cursor + size + gap}
    end)
    |> elem(0)
  end

  defp route_cross(edges, by_id, used) do
    {routed, _used} =
      Enum.map_reduce(Enum.with_index(edges), used, fn {edge, i}, used ->
        a = Map.fetch!(by_id, edge.from)
        b = Map.fetch!(by_id, edge.to)
        {p1, used} = take_port(a, b, used)
        {p2, used} = take_port(b, a, used)
        {curve(edge, p1, p2, i), used}
      end)

    routed
  end

  defp take_port(node, other, used) do
    cx = node.x + div(node.w, 2)
    cy = node.y + div(node.h, 2)
    ox = other.x + div(other.w, 2)
    oy = other.y + div(other.h, 2)

    first =
      if abs(ox - cx) >= abs(oy - cy) do
        if ox >= cx, do: :right, else: :left
      else
        if oy >= cy, do: :bottom, else: :top
      end

    sides = [first, :right, :left, :bottom, :top]

    Enum.find_value(sides, fn side ->
      case free_point(node, side, used) do
        nil -> nil
        pt -> {pt, MapSet.put(used, {node.id, pt})}
      end
    end) || {{node.x + node.w, node.y + div(node.h, 2)}, used}
  end

  defp free_point(node, side, used) do
    len = if side in [:left, :right], do: node.h, else: node.w

    positions =
      if len <= @track do
        [div(len, 2)]
      else
        Enum.to_list(@track..(len - @track)//@track)
      end

    Enum.find_value(positions, fn p ->
      pt = point_at(node, side, p)
      if MapSet.member?(used, {node.id, pt}), do: nil, else: pt
    end)
  end

  defp point_at(node, :right, p), do: {node.x + node.w, node.y + p}
  defp point_at(node, :left, p), do: {node.x, node.y + p}
  defp point_at(node, :top, p), do: {node.x + p, node.y}
  defp point_at(node, :bottom, p), do: {node.x + p, node.y + node.h}

  defp curve(edge, {x1, y1}, {x2, y2}, i) do
    bend = 16 + i * @track
    c1x = x1 + div(x2 - x1, 3)
    c1y = y1 + div(y2 - y1, 3) - bend
    c2x = x1 + div(2 * (x2 - x1), 3)
    c2y = y1 + div(2 * (y2 - y1), 3) - bend
    mx = div(x1 + x2, 2)
    my = div(y1 + y2, 2)

    %{
      edge
      | d: "M #{x1} #{y1} C #{c1x} #{c1y} #{c2x} #{c2y} #{x2} #{y2}",
        lx: mx,
        ly: max(my, 12)
    }
  end

  defp occupied(edges) do
    Enum.reduce(edges, MapSet.new(), fn edge, acc ->
      case path_points(edge.d) do
        [{x1, y1} | rest] ->
          {x2, y2} = List.last(rest) || {x1, y1}

          acc
          |> MapSet.put({edge.from, {x1, y1}})
          |> MapSet.put({edge.to, {x2, y2}})

        _ ->
          acc
      end
    end)
  end

  defp path_points(d) do
    Regex.scan(~r/-?\d+/, d)
    |> Enum.map(fn [n] -> String.to_integer(n) end)
    |> Enum.chunk_every(2)
    |> Enum.flat_map(fn
      [x, y] -> [{x, y}]
      _ -> []
    end)
  end

  defp shift_node(node, dx, dy), do: %{node | x: node.x + dx, y: node.y + dy}

  defp shift_edge(edge, dx, dy) do
    edge = %{edge | d: shift_path(edge.d, dx, dy), lx: edge.lx + dx, ly: edge.ly + dy}

    if Map.has_key?(edge, :bx) do
      %{edge | bx: edge.bx + dx, by: edge.by + dy, tx: edge.tx + dx, ty: edge.ty + dy}
    else
      edge
    end
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
end

defmodule MuroVisor.Draw do
  @moduledoc false

  alias Muro.Emit.Name
  alias MuroVisor.Pack

  @pad 16
  @node_gap 32
  @rank_gap 88
  @grid_gap 64
  @track 16
  @min_track 6
  @gutter 12
  @pitch 16
  @inset 6
  @loop 22
  @loop_band 36
  @header 22
  @char 7
  @label_h 14
  @sweeps 8
  @label_px 12
  @min_label_px 11
  @fit_margin 12
  @pane_w 1070
  @pane_h 760
  # A chain of configurations is one row. The port sits low enough that the
  # label box (baseline minus 12) stays inside the row, above the stroke.
  @meet_head 20
  @state_h 32
  @state_port 24
  @meet_gap 4
  # Room for the cluster title above its nodes, inside the frame.
  @title_band 16

  @doc """
  Positions for the book graph.

  A book of sessions is one cluster per base session, packed into a grid.
  Each cluster is a framed region titled with the session name. Other books
  keep a layered layout. The same book always yields the same coordinates.
  Fit scales that picture to the pane, and stops at the scale where a
  #{@label_px}px label is still #{@min_label_px}px.
  """
  def layout(%{nodes: nodes, edges: edges}) do
    edges = fold_steps(edges)
    prepared = Enum.map(nodes, &prepare/1)
    legend = legend(edges)
    groups = Pack.assign(prepared, edges)

    picture =
      if Enum.any?(groups, &(&1.name != "other")) do
        pack_groups(groups, edges, legend)
      else
        place(prepared, book_edges(edges, legend))
      end

    picture = finish(picture)
    nodes = Enum.map(picture.nodes, &mount_meetings/1)

    picture
    |> Map.put(:nodes, nodes)
    |> Map.put(:legend, legend)
  end

  @doc """
  Scale that fits `width` by `height` into a pane, keeping labels readable.

  The result is uniform. When the fitted scale would draw a #{@label_px}px
  label below #{@min_label_px}px, the scale stays at #{@min_label_px}/#{@label_px}
  and the pane scrolls.
  """
  def fit_scale(width, height, pane_w, pane_h)
      when width > 0 and height > 0 and pane_w > 0 and pane_h > 0 do
    raw = raw_scale(width, height, pane_w, pane_h)

    if raw * @label_px + 1.0e-9 >= @min_label_px do
      raw
    else
      @min_label_px / @label_px
    end
  end

  @doc false
  def raw_scale(width, height, pane_w, pane_h) do
    avail_w = pane_w - 2 * @fit_margin
    avail_h = pane_h - 2 * @fit_margin
    min(avail_w / width, avail_h / height)
  end

  @doc """
  Clusters the book graph would draw, in source order, plus `"other"`.
  """
  def clusters(%{nodes: nodes, edges: edges}) do
    edges = fold_steps(edges)
    Pack.assign(Enum.map(nodes, &prepare/1), edges)
  end

  defp pack_groups(groups, edges, legend) do
    drawn = book_edges(edges, legend)

    owner =
      Enum.reduce(groups, %{}, fn group, acc ->
        Enum.reduce(group.nodes, acc, &Map.put(&2, &1.id, group.name))
      end)

    {locals, cross} =
      Enum.split_with(drawn, fn edge ->
        from = Map.get(owner, edge.from)
        from != nil and from == Map.get(owner, edge.to)
      end)

    pictures =
      Enum.map(groups, fn group ->
        local = Enum.filter(locals, &(Map.get(owner, &1.from) == group.name))

        picture =
          if group.name == "other" do
            place(group.nodes, local)
          else
            Pack.cluster(%{name: group.name, nodes: group.nodes, edges: local})
          end

        picture
        |> Map.put(:name, group.name)
        |> frame_cluster()
      end)

    {nodes, edges, clusters, width, height} =
      Pack.arrange(pictures, cross, &raw_scale(&1, &2, @pane_w, @pane_h))

    %{width: width, height: height, nodes: nodes, edges: edges, clusters: clusters}
  end

  # The title occupies a band inside the frame, clear of the nodes.
  defp frame_cluster(picture) do
    height = picture.height + @title_band

    picture
    |> Map.put(:nodes, Enum.map(picture.nodes, &shift_node(&1, 0, @title_band)))
    |> Map.put(:edges, Enum.map(picture.edges, &shift_edge(&1, 0, @title_band)))
    |> Map.put(:height, height)
    |> Map.put(:frame, %{
      name: picture.name || "other",
      x: 0,
      y: 0,
      w: picture.width,
      h: height
    })
  end

  defp finish(picture) do
    clusters = Map.get(picture, :clusters, [])
    edges = seat_badges(picture.edges, picture.nodes, clusters)
    picture = Map.put(picture, :clusters, clusters)
    lift(%{picture | edges: edges})
  end

  # One step edge per conform and session, however many spine steps use it.
  # The kept id is the first in book order, so a click still resolves.
  defp fold_steps(edges) do
    {order, map} =
      Enum.reduce(edges, {[], %{}}, fn edge, {order, map} ->
        if edge.use == :step do
          key = {edge.from, edge.to}

          if Map.has_key?(map, key) do
            {order, Map.update!(map, key, &%{&1 | count: &1.count + 1})}
          else
            {[key | order], Map.put(map, key, Map.put(edge, :count, 1))}
          end
        else
          key = {:keep, edge.id}
          {[key | order], Map.put(map, key, Map.put(edge, :count, 1))}
        end
      end)

    order |> Enum.reverse() |> Enum.map(&Map.fetch!(map, &1))
  end

  defp legend(edges) do
    present = edges |> Enum.map(&to_string(&1.use)) |> Enum.uniq()
    preferred = ["meet", "step", "dual", "def"]
    Enum.filter(preferred, &(&1 in present)) ++ Enum.reject(present, &(&1 in preferred))
  end

  defp prepare(node) do
    meetings = build_meetings(node)
    label = "#{node.mode} #{node.name}"
    inner_w = meetings |> Enum.map(& &1.w) |> Enum.max(fn -> 0 end)

    inner_h =
      case meetings do
        [] -> 36
        ms -> @header + Enum.sum(Enum.map(ms, & &1.h)) + @meet_gap * length(ms)
      end

    %{
      id: node.id,
      name: label,
      bare: node.name,
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
        label = state_id(child)

        %{
          id: child.id,
          label: label,
          state: state_id(child),
          w: max(text_w(label) + 16, 36),
          h: @state_h,
          x: 0,
          y: 0,
          meetings: []
        }
      end)

    edges =
      Enum.map(Enum.with_index(transitions), fn {t, i} ->
        %{
          id: transition_id(t, i),
          from: t.from,
          to: t.to,
          label: text_label(t.label),
          use: "trans",
          count: 1,
          d: "",
          lx: 0,
          ly: 0
        }
      end)

    picture =
      if chain_row?(nodes, edges) do
        row_meeting(nodes, edges)
      else
        with_profile(meeting_profile(), fn ->
          place(nodes, edges)
        end)
      end

    picture = picture |> reseat_meeting() |> shift_picture(0, @meet_head)
    label_w = edges |> Enum.map(&text_w(&1.label)) |> Enum.max(fn -> 0 end)

    %{
      id: "m-" <> Name.encode(session) <> "-" <> Name.encode(meet),
      name: meet,
      x: 0,
      y: 0,
      w: max(picture.width, max(text_w(meet) + 16, label_w + 16)),
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
        {shift_meeting(meet, node.x + 8 - meet.x, y - meet.y), y + meet.h + @meet_gap}
      end)

    %{node | meetings: meetings}
  end

  defp book_edges(edges, _legend) do
    Enum.map(edges, fn edge ->
      %{
        id: edge.id,
        from: edge.from,
        to: edge.to,
        label: "",
        use: to_string(edge.use),
        count: Map.get(edge, :count, 1),
        d: "",
        lx: 0,
        ly: 0
      }
    end)
  end

  defp meeting_profile do
    %{rank_gap: 18, node_gap: 8, grid_gap: 12, track: 8, gutter: 6, pad: 6, pitch: 8}
  end

  defp with_profile(profile, fun) do
    previous = Process.get(:muro_draw_profile)
    Process.put(:muro_draw_profile, profile)

    try do
      fun.()
    after
      if previous == nil do
        Process.delete(:muro_draw_profile)
      else
        Process.put(:muro_draw_profile, previous)
      end
    end
  end

  defp prof(key, default) do
    case Process.get(:muro_draw_profile) do
      profile when is_map(profile) -> Map.get(profile, key, default)
      _ -> default
    end
  end

  defp place([], _edges) do
    pad = prof(:pad, @pad)
    %{width: pad * 2, height: pad * 2, nodes: [], edges: [], name: nil}
  end

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

    pad = prof(:pad, @pad)

    {positions, _y} =
      Enum.reduce(rows, {%{}, pad}, fn row, {acc, y} ->
        row_h =
          row
          |> Enum.map(fn node -> node.h + loop_count(node.id, edges) * @loop_band end)
          |> Enum.max()

        acc =
          Enum.reduce(Enum.with_index(row), acc, fn {node, c}, acc ->
            loops = loop_count(node.id, edges) * @loop_band
            x = pad + c * (col_w + prof(:grid_gap, @grid_gap))

            Map.put(acc, node.id, %{node | x: x, y: y + loops})
          end)

        {acc, y + row_h + prof(:node_gap, @node_gap)}
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

    Enum.reduce(ranks, {[], %{}, %{}, prof(:pad, @pad)}, fn r, {nodes, cols, ys, x} ->
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
      Enum.reduce(Enum.with_index(reals), {[], ys, prof(:pad, @pad)}, fn {id, i},
                                                                         {nodes, ys, y} ->
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
        gap = prof(:node_gap, @node_gap)
        advance = if below == [], do: gap, else: max(gap, used + 8)
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

  defp dummy_step(:spread, _n), do: prof(:track, @track)
  defp dummy_step(:compact, n) when n <= 1, do: prof(:track, @track)
  defp dummy_step(:compact, n), do: max(min(prof(:track, @track), div(140, n)), @min_track)

  # The strip beside a rank holds same-rank edges. The rest of the gap is
  # the channel, wide enough for one track per edge that crosses it.
  defp gap_width(gaps, r, has_next) do
    same_n = Map.get(gaps.same, r, 0)
    cross_n = Map.get(gaps.cross, r, 0)

    strip_width(same_n) +
      cond do
        cross_n > 0 -> channel_width(cross_n)
        has_next -> prof(:rank_gap, @rank_gap)
        true -> 0
      end
  end

  defp strip_width(0), do: 0
  defp strip_width(n), do: channel_width(n)
  defp channel_width(n) when n <= 1, do: prof(:rank_gap, @rank_gap)

  defp channel_width(n) do
    max(prof(:rank_gap, @rank_gap), 2 * prof(:gutter, @gutter) + (n - 1) * prof(:track, @track))
  end

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
    limit =
      max(Enum.max(prev) - Enum.min(ys) + @min_track * max(MapSet.size(prev), 1), @min_track)

    Enum.find(0..limit, limit, fn k ->
      Enum.all?(ys, &clear?(&1 + k, prev))
    end)
  end

  defp clear?(y, prev) do
    not Enum.any?(prev, fn p -> abs(p - y) < @min_track end)
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
    gutter = prof(:gutter, @gutter)
    inner = max(width - 2 * gutter, n - 1)

    Enum.map(0..(n - 1), fn i ->
      left + gutter + div(i * inner, n - 1)
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

    pitch = prof(:pitch, @pitch)

    h =
      if side <= 1,
        do: node.h,
        else: max(node.h, 2 * @inset + (side - 1) * pitch)

    w =
      if top <= 1,
        do: node.w,
        else: max(node.w, 2 * @inset + (top - 1) * pitch)

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
      placed ++ [seat_label(edge, nodes, placed, edges)]
    end)
  end

  defp seat_label(edge, nodes, placed, edges) do
    {x, y} = label_anchor(edge)
    nudge_label(edge, x, y, nodes, placed, edges, 0)
  end

  # The label sits on this edge's own track, beside the stroke, not on
  # the midpoint where another edge crosses.
  defp label_anchor(%{d: d, lx: lx, ly: ly}) do
    if String.contains?(d, " C "), do: {lx, ly}, else: track_point(d)
  end

  defp track_point(d) do
    segs =
      d
      |> path_pairs()
      |> then(fn pts -> Enum.zip(pts, tl(pts)) end)
      |> Enum.reject(fn {a, b} -> a == b end)

    vertical = Enum.filter(segs, fn {{x1, _y1}, {x2, _y2}} -> x1 == x2 end)

    chosen =
      cond do
        vertical != [] -> Enum.max_by(vertical, fn {a, b} -> manhattan(a, b) end)
        segs != [] -> Enum.max_by(segs, fn {a, b} -> manhattan(a, b) end)
        true -> nil
      end

    case chosen do
      nil ->
        path_midpoint(d)

      {{x, y1}, {x, y2}} ->
        {x + 8, div(y1 + y2, 2)}

      {{x1, y1}, {x2, y2}} ->
        {div(x1 + x2, 2), min(y1, y2) - 10}
    end
  end

  defp nudge_label(edge, x, y, _nodes, _placed, _edges, n) when n > 48 do
    %{edge | lx: x, ly: max(y, 12)}
  end

  defp nudge_label(edge, x, y, nodes, placed, edges, n) do
    {dx, dy} = spiral_at(n)
    candidate = %{edge | lx: x + dx, ly: max(y + dy, 12)}

    if label_clash?(candidate, nodes, placed, edges) do
      nudge_label(edge, x, y, nodes, placed, edges, n + 1)
    else
      candidate
    end
  end

  defp label_clash?(%{label: ""}, _nodes, _placed, _edges), do: false

  defp label_clash?(edge, nodes, placed, edges) do
    box = label_box(edge)

    Enum.any?(placed, fn other ->
      other.label != "" and boxes_overlap?(label_box(other), box)
    end) or Enum.any?(nodes, &boxes_overlap?(box, &1)) or hits_other?(box, edge, edges)
  end

  defp hits_other?(box, edge, edges) do
    Enum.any?(edges, fn other ->
      other.id != edge.id and hits_box?(box, other.d)
    end)
  end

  defp hits_box?(box, d) do
    d
    |> path_pairs()
    |> then(fn pts -> Enum.zip(pts, tl(pts)) end)
    |> Enum.any?(fn {{x1, y1}, {x2, y2}} ->
      cond do
        x1 == x2 ->
          x1 >= box.x and x1 <= box.x + box.w and
            ranges_overlap?(min(y1, y2), max(y1, y2), box.y, box.y + box.h)

        y1 == y2 ->
          y1 >= box.y and y1 <= box.y + box.h and
            ranges_overlap?(min(x1, x2), max(x1, x2), box.x, box.x + box.w)

        true ->
          false
      end
    end)
  end

  defp ranges_overlap?(a1, a2, b1, b2), do: max(a1, b1) < min(a2, b2)

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
    pad = prof(:pad, @pad)
    boxes = extent_points(nodes, edges)
    max_x = boxes |> Enum.map(&elem(&1, 0)) |> Enum.max(fn -> pad end)
    max_y = boxes |> Enum.map(&elem(&1, 1)) |> Enum.max(fn -> pad end)
    %{width: max(max_x + pad, pad * 2), height: max(max_y + pad, pad * 2)}
  end

  defp lift(picture) do
    pad = prof(:pad, @pad)
    pts = picture_points(picture)
    min_x = pts |> Enum.map(&elem(&1, 0)) |> Enum.min(fn -> pad end)
    min_y = pts |> Enum.map(&elem(&1, 1)) |> Enum.min(fn -> pad end)
    dx = max(0, pad - min_x)
    dy = max(0, pad - min_y)

    picture =
      if dx == 0 and dy == 0 do
        picture
      else
        shift_picture(picture, dx, dy)
      end

    Map.merge(picture, size_of(picture))
  end

  defp size_of(picture) do
    pad = prof(:pad, @pad)
    pts = picture_points(picture)
    max_x = pts |> Enum.map(&elem(&1, 0)) |> Enum.max(fn -> pad end)
    max_y = pts |> Enum.map(&elem(&1, 1)) |> Enum.max(fn -> pad end)
    %{width: max(max_x + pad, pad * 2), height: max(max_y + pad, pad * 2)}
  end

  defp picture_points(picture) do
    extent_points(picture.nodes, picture.edges) ++
      frame_points(Map.get(picture, :clusters, []))
  end

  defp frame_points(clusters) do
    Enum.flat_map(clusters, fn cluster ->
      [{cluster.x, cluster.y}, {cluster.x + cluster.w, cluster.y + cluster.h}]
    end)
  end

  defp extent_points(nodes, edges) do
    Enum.flat_map(nodes, fn n ->
      [{n.x, n.y}, {n.x + n.w, n.y + n.h}]
    end) ++ Enum.flat_map(edges, &edge_points/1)
  end

  defp edge_points(edge) do
    box = label_box(edge)

    badge =
      if Map.has_key?(edge, :bw) do
        [{edge.bx, edge.by}, {edge.bx + edge.bw, edge.by + edge.bh}]
      else
        []
      end

    path_pairs(edge.d) ++ [{box.x, box.y}, {box.x + box.w, box.y + box.h}] ++ badge
  end

  defp reseat_meeting(picture) do
    edges = seat_config_labels(picture.edges, picture.nodes)
    pad_meeting(%{picture | edges: edges}, 6)
  end

  # Source order is already the order the checker walked. A meeting whose
  # edges only join neighbours (or loop) is one row, with the label in the
  # gap, so the compound stays short enough to fit the pane.
  defp chain_row?(nodes, edges) do
    index = Map.new(Enum.with_index(nodes), fn {node, i} -> {node.id, i} end)

    Enum.all?(edges, fn edge ->
      a = Map.get(index, edge.from)
      b = Map.get(index, edge.to)
      a != nil and b != nil and (a == b or abs(a - b) == 1)
    end) and length(Enum.uniq(Enum.map(edges, &{&1.from, &1.to}))) == length(edges)
  end

  defp row_meeting(nodes, edges) do
    gaps = row_gaps(nodes, edges)

    {placed, _} =
      Enum.map_reduce(Enum.with_index(nodes), 0, fn {node, i}, x ->
        node = %{node | x: x, y: 0, h: @state_h}
        {node, x + node.w + Enum.at(gaps, i, 0)}
      end)

    by_id = Map.new(placed, &{&1.id, &1})
    drawn = Enum.map(edges, &route_row(&1, by_id))
    %{nodes: placed, edges: drawn, width: 0, height: 0}
  end

  defp row_gaps(nodes, edges) do
    Enum.map(Enum.with_index(nodes), fn {node, i} ->
      nxt = Enum.at(nodes, i + 1)

      if nxt == nil do
        0
      else
        labels =
          for edge <- edges,
              MapSet.new([edge.from, edge.to]) == MapSet.new([node.id, nxt.id]),
              do: text_w(edge.label)

        max(Enum.max(labels, fn -> 0 end) + 8, 16)
      end
    end)
  end

  defp route_row(%{from: id, to: id} = edge, by_id) do
    node = Map.fetch!(by_id, id)
    x1 = node.x + slot(node.w, 0, 2)
    x2 = node.x + slot(node.w, 1, 2)
    y = node.y
    cy = y - 16

    %{
      edge
      | d: "M #{x1} #{y} C #{x1} #{cy} #{x2} #{cy} #{x2} #{y}",
        lx: x1,
        ly: max(cy + 12, 12)
    }
  end

  defp route_row(edge, by_id) do
    a = Map.fetch!(by_id, edge.from)
    b = Map.fetch!(by_id, edge.to)
    forward = a.x <= b.x
    y = if forward, do: a.y + @state_port, else: a.y + a.h
    x1 = if forward, do: a.x + a.w, else: a.x
    x2 = if forward, do: b.x, else: b.x + b.w
    polyline(edge, [x1, y, x2, y], 0, 0)
  end

  defp seat_config_labels(edges, nodes) do
    Enum.reduce(edges, [], fn edge, placed ->
      edge = place_config_label(edge)
      edge = clear_label(edge, placed, nodes)
      placed ++ [edge]
    end)
  end

  defp place_config_label(%{label: label} = edge) when label in [nil, ""], do: edge

  defp place_config_label(edge) do
    w = text_w(edge.label)

    case longest_horizontal(edge.d) do
      {x1, y, x2} ->
        %{edge | lx: div(x1 + x2, 2) - div(w, 2), ly: y - 12}

      nil ->
        pts = path_pairs(edge.d)
        top = pts |> Enum.map(&elem(&1, 1)) |> Enum.min()
        left = pts |> Enum.map(&elem(&1, 0)) |> Enum.min()
        right = pts |> Enum.map(&elem(&1, 0)) |> Enum.max()
        %{edge | lx: div(left + right, 2) - div(w, 2), ly: top - 14}
    end
  end

  defp longest_horizontal(d) do
    d
    |> path_pairs()
    |> then(fn pts -> Enum.zip(pts, tl(pts)) end)
    |> Enum.filter(fn {{_x1, y1}, {_x2, y2}} -> y1 == y2 end)
    |> Enum.reject(fn {a, b} -> a == b end)
    |> case do
      [] ->
        nil

      segs ->
        {{x1, y}, {x2, _}} = Enum.max_by(segs, fn {a, b} -> abs(elem(b, 0) - elem(a, 0)) end)
        {min(x1, x2), y, max(x1, x2)}
    end
  end

  defp clear_label(%{label: label} = edge, _placed, _nodes) when label in [nil, ""], do: edge

  defp clear_label(edge, placed, nodes) do
    obstacles =
      Enum.flat_map(placed, fn other ->
        if other.label in [nil, ""], do: [], else: [label_box(other)]
      end) ++ Enum.map(nodes, fn node -> %{x: node.x, y: node.y, w: node.w, h: node.h} end)

    rise(edge, obstacles)
  end

  defp rise(edge, obstacles) do
    box = label_box(edge)

    case Enum.filter(obstacles, &boxes_overlap?(box, &1)) do
      [] ->
        edge

      hits ->
        top = Enum.min(Enum.map(hits, & &1.y))
        above = Enum.filter(obstacles, &(&1.y < top))
        rise(%{edge | ly: top - 6}, above)
    end
  end

  defp pad_meeting(picture, margin) do
    pts = extent_points(picture.nodes, picture.edges)
    min_x = pts |> Enum.map(&elem(&1, 0)) |> Enum.min(fn -> 0 end)
    min_y = pts |> Enum.map(&elem(&1, 1)) |> Enum.min(fn -> 0 end)
    max_x = pts |> Enum.map(&elem(&1, 0)) |> Enum.max(fn -> margin end)
    max_y = pts |> Enum.map(&elem(&1, 1)) |> Enum.max(fn -> margin end)
    dx = max(0, margin - min_x)
    dy = max(0, margin - min_y)
    nodes = Enum.map(picture.nodes, &shift_node(&1, dx, dy))
    edges = Enum.map(picture.edges, &shift_edge(&1, dx, dy))

    %{
      picture
      | nodes: nodes,
        edges: edges,
        width: max_x + dx + margin,
        height: max_y + dy + margin
    }
  end

  # A count sits beside the middle of its edge. If that pill would touch a
  # node, a title, or another count, it walks along the edge until it is clear.
  defp seat_badges(edges, nodes, clusters) do
    base =
      Enum.map(nodes, fn node -> %{x: node.x, y: node.y, w: node.w, h: node.h} end) ++
        Enum.map(clusters, &title_obstacle/1)

    {edges, _placed} =
      Enum.map_reduce(edges, [], fn edge, placed ->
        if Map.get(edge, :count, 1) > 1 do
          edge = put_badge(edge, base ++ placed)
          {edge, [badge_rect(edge) | placed]}
        else
          {edge, placed}
        end
      end)

    edges
  end

  defp title_obstacle(%{name: name, x: x, y: y}) do
    %{x: x + 8, y: y + 1, w: text_w(name), h: 14}
  end

  defp put_badge(edge, obstacles) do
    text = Integer.to_string(edge.count)
    w = text_w(text) + 8
    h = 16

    box =
      Enum.find_value(badge_spots(edge.d), fn {x, y, nx, ny} ->
        rect = %{x: x + nx - div(w, 2), y: y + ny - div(h, 2), w: w, h: h}
        if badge_clear?(rect, obstacles), do: rect
      end) || badge_fallback(edge, w, h)

    Map.merge(edge, %{
      bx: box.x,
      by: box.y,
      bw: box.w,
      bh: box.h,
      tx: box.x + div(box.w, 2),
      ty: box.y + 12
    })
  end

  defp badge_rect(edge), do: %{x: edge.bx, y: edge.by, w: edge.bw, h: edge.bh}

  defp badge_fallback(edge, w, h) do
    {x, y} = path_midpoint(edge.d)
    %{x: x - div(w, 2), y: y - h - 6, w: w, h: h}
  end

  # Two pixels of air, so a pill that only touches a box still counts as a hit.
  defp badge_clear?(rect, obstacles) do
    Enum.all?(obstacles, &(not near?(rect, &1)))
  end

  defp near?(a, b) do
    a.x < b.x + b.w + 2 and b.x < a.x + a.w + 2 and a.y < b.y + b.h + 2 and
      b.y < a.y + a.h + 2
  end

  defp badge_spots(d) do
    samples = path_samples(d, 4)

    ordered =
      case samples do
        [] ->
          []

        _ ->
          mid = div(List.last(samples).dist, 2)

          Enum.sort_by(samples, fn sample ->
            {abs(sample.dist - mid), sample.dist}
          end)
      end

    Enum.flat_map(ordered, fn sample ->
      Enum.map([12, -12, 20, -20, 28, -28], fn off ->
        {nx, ny} = perp_offset(sample.dx, sample.dy, off)
        {sample.x, sample.y, nx, ny}
      end)
    end)
  end

  defp perp_offset(dx, dy, off) do
    len = :math.sqrt(dx * dx + dy * dy)
    len = if len < 1.0e-6, do: 1.0, else: len
    {round(-dy / len * off), round(dx / len * off)}
  end

  defp path_samples(d, step) do
    case flatten_path(d) do
      [] ->
        []

      [point] ->
        [%{x: elem(point, 0), y: elem(point, 1), dist: 0, dx: 1.0, dy: 0.0}]

      points ->
        walk_samples(points, step)
    end
  end

  defp walk_samples(points, step) do
    {_prev, _dist, acc} =
      Enum.reduce(tl(points), {hd(points), 0.0, []}, fn nxt, {{x1, y1}, dist, acc} ->
        {x2, y2} = nxt
        len = :math.sqrt((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1))
        dx = if len < 1.0e-6, do: 1.0, else: (x2 - x1) / len
        dy = if len < 1.0e-6, do: 0.0, else: (y2 - y1) / len
        count = max(trunc(len / step), 1)

        samples =
          Enum.map(0..count, fn i ->
            t = min(i * step, len)

            %{
              x: round(x1 + dx * t),
              y: round(y1 + dy * t),
              dist: round(dist + t),
              dx: dx,
              dy: dy
            }
          end)

        {nxt, dist + len, acc ++ samples}
      end)

    Enum.uniq_by(acc, fn sample -> {sample.x, sample.y} end)
  end

  defp flatten_path(d) do
    tokens = Regex.scan(~r/[MLC]|-?\d+/, d) |> Enum.map(&hd/1)
    decode_path(tokens, [])
  end

  defp decode_path([], acc), do: Enum.reverse(acc)
  defp decode_path(["M", x, y | rest], acc), do: decode_path(rest, [{num(x), num(y)} | acc])
  defp decode_path(["L", x, y | rest], acc), do: decode_path(rest, [{num(x), num(y)} | acc])

  defp decode_path(["C", x1, y1, x2, y2, x, y | rest], [p0 | _] = acc) do
    p1 = {num(x1), num(y1)}
    p2 = {num(x2), num(y2)}
    p3 = {num(x), num(y)}

    extra =
      1..4
      |> Enum.map(fn i -> cubic(p0, p1, p2, p3, i / 4) end)
      |> Enum.reverse()

    decode_path(rest, extra ++ acc)
  end

  defp decode_path([_token | rest], acc), do: decode_path(rest, acc)

  defp cubic({x0, y0}, {x1, y1}, {x2, y2}, {x3, y3}, t) do
    u = 1 - t

    x = u * u * u * x0 + 3 * u * u * t * x1 + 3 * u * t * t * x2 + t * t * t * x3
    y = u * u * u * y0 + 3 * u * u * t * y1 + 3 * u * t * t * y2 + t * t * t * y3
    {round(x), round(y)}
  end

  defp num(token), do: String.to_integer(token)

  defp shift_picture(picture, dx, dy) do
    picture
    |> Map.update!(:width, &(&1 + dx))
    |> Map.update!(:height, &(&1 + dy))
    |> Map.update!(:nodes, fn nodes -> Enum.map(nodes, &shift_node(&1, dx, dy)) end)
    |> Map.update!(:edges, fn edges -> Enum.map(edges, &shift_edge(&1, dx, dy)) end)
    |> Map.update(:clusters, [], fn clusters ->
      Enum.map(clusters, &shift_cluster(&1, dx, dy))
    end)
  end

  defp shift_cluster(cluster, dx, dy), do: %{cluster | x: cluster.x + dx, y: cluster.y + dy}

  defp shift_node(node, dx, dy), do: %{node | x: node.x + dx, y: node.y + dy}

  defp shift_edge(edge, dx, dy) do
    edge = %{edge | d: shift_path(edge.d, dx, dy), lx: edge.lx + dx, ly: edge.ly + dy}

    if Map.has_key?(edge, :bx) do
      %{edge | bx: edge.bx + dx, by: edge.by + dy, tx: edge.tx + dx, ty: edge.ty + dy}
    else
      edge
    end
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

  defp transition_id(%{id: id}, _index) when is_binary(id), do: id
  defp transition_id(t, index), do: "#{index}-#{t.from}-#{t.to}"

  defp state_id(child) do
    child.id |> String.split("-") |> List.last()
  end
end

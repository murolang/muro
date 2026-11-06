defmodule MuroVisor.ClusterTest do
  use MuroVisor.ConnCase, async: false

  test "meet.muro puts each base session in its own cluster" do
    groups = MuroVisor.Draw.clusters(meet())

    assert Enum.map(groups, & &1.name) ==
             ~w(ping choice open box sized window other)

    names =
      Map.new(groups, fn group ->
        {group.name, group.nodes |> Enum.map(& &1.bare) |> Enum.sort()}
      end)

    assert names["ping"] ==
             ~w(back echo echo-wire peer peer-echo ping pong wire)

    assert names["choice"] == ~w(arm choice giver offered taker)
    assert names["open"] == ~w(closed drop left open right)
    assert names["box"] == ~w(box boxed far far-wrap here there wrapped)
    assert names["sized"] == ~w(sized sized-back sized-client sized-server sized-wire)
    assert names["window"] == ~w(grant-end window window-client window-server window-wire)
    assert names["other"] == ["kept"]
  end

  test "a conform has one step edge and a meeting has two" do
    graph = meet()
    drawn = MuroVisor.Draw.layout(graph).edges
    steps = Enum.filter(drawn, &(&1.use == "step"))
    pairs = Enum.map(steps, &{&1.from, &1.to})

    assert steps != []
    assert length(steps) == length(Enum.uniq(pairs))
    assert length(steps) < Enum.count(graph.edges, &(&1.use == :step))

    pong = Muro.Emit.Name.encode("pong")
    ping = Muro.Emit.Name.encode("ping")
    assert Enum.find(steps, &(&1.from == pong and &1.to == ping)).count == 3

    meets = Enum.filter(drawn, &(&1.use == "meet"))

    for {_from, group} <- Enum.group_by(meets, & &1.from) do
      assert length(group) == 2
    end

    assert length(meets) == 2 * map_size(Enum.group_by(meets, & &1.from))
  end

  test "fit keeps meet.muro labels readable and a large book scrolls" do
    picture = MuroVisor.Draw.layout(meet())
    scale = MuroVisor.Draw.fit_scale(picture.width, picture.height, 1070, 760)

    assert scale * 12 >= 11
    assert picture.width * scale <= 1070 - 24 + 1.0e-6
    assert picture.height * scale <= 760 - 24 + 1.0e-6

    wide = MuroVisor.Draw.layout(chain(60))
    fallback = MuroVisor.Draw.fit_scale(wide.width, wide.height, 1070, 760)
    assert fallback == 11 / 12
    assert wide.width * fallback > 1070 or wide.height * fallback > 760
  end

  test "configuration labels sit above the stroke and inside the meeting" do
    picture = MuroVisor.Draw.layout(meet())

    labelled =
      for node <- picture.nodes,
          meet <- node.meetings,
          edge <- meet.transitions,
          edge.label != "",
          y = segment_y(edge.d),
          y != nil do
        assert y >= edge.ly + 6, edge.label
        w = max(String.length(edge.label), 1) * 7

        assert edge.lx >= meet.x + 4
        assert edge.ly - 12 >= meet.y + 4
        assert edge.lx + w <= meet.x + meet.w - 4
        assert edge.ly - 12 + 14 <= meet.y + meet.h - 4
        edge.label
      end

    assert "put rep n 0" in labelled
    assert "put (b0, {x = 0, y = 0})" in labelled
  end

  test "the page draws one step edge per conform and a line for each kind", %{conn: conn} do
    view = open_book(conn, example("meet.muro"))
    html = render(view)
    picture = MuroVisor.Draw.layout(Muro.Explore.graph(book()))
    dom = use_edges(html)
    steps = Enum.filter(dom, &(&1.use == "step"))

    assert length(steps) == Enum.count(picture.edges, &(&1.use == "step"))
    assert length(steps) == length(Enum.uniq(Enum.map(steps, &{&1.from, &1.to})))

    pong = Muro.Emit.Name.encode("pong")
    [pong_edge] = Enum.filter(steps, &(&1.from == pong))
    assert Floki.attribute(parse(html), "##{pong_edge.id}", "data-count") == ["3"]

    meets = Enum.filter(dom, &(&1.use == "meet"))

    for {_from, group} <- Enum.group_by(meets, & &1.from) do
      assert length(group) == 2
    end

    html = render(view)
    frames = html |> parse() |> Floki.find("rect.cluster-frame")
    titles = html |> parse() |> Floki.find("text.cluster-title") |> Enum.map(&Floki.text/1)
    assert length(frames) == 7
    assert titles == ~w(ping choice open box sized window other)

    for kind <- ~w(meet step dual) do
      [class] =
        Floki.attribute(parse(html), ~s(#edge-legend li[data-kind="#{kind}"] line), "class")

      assert class == "edge edge-#{kind}"

      [x2] = Floki.attribute(parse(html), ~s(#edge-legend li[data-kind="#{kind}"] line), "x2")
      assert String.to_integer(x2) >= 24
    end
  end

  test "counts stay clear, columns are even, and meet and dual edges stay visible" do
    picture = MuroVisor.Draw.layout(meet())

    assert Enum.map(picture.clusters, & &1.name) ==
             ~w(ping choice open box sized window other)

    for cluster <- picture.clusters do
      assert cluster.x >= 0
      assert cluster.y >= 0
      assert cluster.x + cluster.w <= picture.width
      assert cluster.y + cluster.h <= picture.height

      members = Enum.filter(picture.nodes, &(&1.cluster == cluster.name))
      assert members != []

      for node <- members do
        assert node.x >= cluster.x
        assert node.y >= cluster.y + 16
        assert node.x + node.w <= cluster.x + cluster.w
        assert node.y + node.h <= cluster.y + cluster.h
      end

      if cluster.name != "other" do
        members
        |> Enum.group_by(& &1.x)
        |> Enum.each(fn {x, col} ->
          assert [_width] = Enum.uniq(Enum.map(col, & &1.w)),
                 "#{cluster.name} column at #{x} has uneven widths"
        end)
      end
    end

    nodes = Enum.map(picture.nodes, &%{x: &1.x, y: &1.y, w: &1.w, h: &1.h, id: &1.id})

    badges =
      for edge <- picture.edges, Map.has_key?(edge, :bw) do
        %{x: edge.bx, y: edge.by, w: edge.bw, h: edge.bh, id: edge.id}
      end

    assert badges != []

    for badge <- badges do
      assert badge.x >= 0
      assert badge.y >= 0
      assert badge.x + badge.w <= picture.width
      assert badge.y + badge.h <= picture.height

      for node <- nodes do
        refute box_hit?(badge, node), "badge #{badge.id} overlaps #{node.id}"
      end
    end

    for {a, i} <- Enum.with_index(badges), {b, j} <- Enum.with_index(badges), i < j do
      refute box_hit?(a, b), "badges #{a.id} and #{b.id} overlap"
    end

    sessions = Enum.filter(picture.nodes, &(&1.kind == "session"))

    for edge <- picture.edges, edge.use in ["meet", "dual"] do
      assert path_length(edge.d) + 1.0e-6 >= 24,
             "#{edge.use} #{edge.id} is #{path_length(edge.d)}"
    end

    for edge <- picture.edges, edge.use == "step", node <- sessions do
      for seg <- line_segments(edge.d) do
        case side_gap(seg, node) do
          nil -> :ok
          gap -> assert gap >= 8, "#{edge.id} runs #{gap}px from #{node.name}"
        end
      end
    end

    for edge <- picture.edges, {x, y} <- interior_points(edge.d), node <- picture.nodes do
      refute strictly_inside?(x, y, node), "#{edge.id} crosses #{node.name}"
    end
  end

  defp box_hit?(a, b) do
    a.x < b.x + b.w + 1 and b.x < a.x + a.w + 1 and a.y < b.y + b.h + 1 and b.y < a.y + a.h + 1
  end

  defp side_gap({{x1, y1}, {x2, y2}}, node) do
    cond do
      y1 == y2 and span_overlap?(x1, x2, node.x, node.x + node.w) ->
        axis_gap(y1, node.y, node.y + node.h)

      x1 == x2 and span_overlap?(y1, y2, node.y, node.y + node.h) ->
        axis_gap(x1, node.x, node.x + node.w)

      true ->
        nil
    end
  end

  defp axis_gap(v, a, b) do
    cond do
      v >= a and v <= b -> 0
      v < a -> a - v
      true -> v - b
    end
  end

  defp span_overlap?(a1, a2, b1, b2) do
    max(min(a1, a2), b1) < min(max(a1, a2), b2)
  end

  defp strictly_inside?(x, y, node) do
    x > node.x and x < node.x + node.w and y > node.y and y < node.y + node.h
  end

  defp interior_points(d) do
    tokens = Regex.scan(~r/[MLC]|-?\d+/, d) |> Enum.map(&hd/1)
    walk_interior(tokens, nil, [])
  end

  defp walk_interior([], _cur, acc), do: acc
  defp walk_interior(["M", x, y | rest], _cur, acc), do: walk_interior(rest, {n(x), n(y)}, acc)

  defp walk_interior(["L", x, y | rest], {px, py}, acc) do
    nxt = {n(x), n(y)}
    acc = if nxt == {px, py}, do: acc, else: [midpoint({px, py}, nxt) | acc]
    walk_interior(rest, nxt, acc)
  end

  defp walk_interior(["C", x1, y1, x2, y2, x, y | rest], p0, acc) do
    p1 = {n(x1), n(y1)}
    p2 = {n(x2), n(y2)}
    p3 = {n(x), n(y)}

    samples =
      Enum.map([0.25, 0.5, 0.75], fn t ->
        cubic_point(p0, p1, p2, p3, t)
      end)

    walk_interior(rest, p3, samples ++ acc)
  end

  defp midpoint({x1, y1}, {x2, y2}), do: {div(x1 + x2, 2), div(y1 + y2, 2)}

  defp cubic_point({x0, y0}, {x1, y1}, {x2, y2}, {x3, y3}, t) do
    u = 1 - t
    x = u * u * u * x0 + 3 * u * u * t * x1 + 3 * u * t * t * x2 + t * t * t * x3
    y = u * u * u * y0 + 3 * u * u * t * y1 + 3 * u * t * t * y2 + t * t * t * y3
    {round(x), round(y)}
  end

  defp line_segments(d) do
    tokens = Regex.scan(~r/[MLC]|-?\d+/, d) |> Enum.map(&hd/1)
    walk_lines(tokens, nil, [])
  end

  defp walk_lines([], _cur, acc), do: acc
  defp walk_lines(["M", x, y | rest], _cur, acc), do: walk_lines(rest, {n(x), n(y)}, acc)

  defp walk_lines(["L", x, y | rest], {px, py}, acc) do
    nxt = {n(x), n(y)}
    acc = if nxt == {px, py}, do: acc, else: [{{px, py}, nxt} | acc]
    walk_lines(rest, nxt, acc)
  end

  defp walk_lines(["C", _a, _b, _c, _d, x, y | rest], _cur, acc) do
    walk_lines(rest, {n(x), n(y)}, acc)
  end

  defp path_length(d) do
    tokens = Regex.scan(~r/[MLC]|-?\d+/, d) |> Enum.map(&hd/1)
    measure(tokens, nil, 0.0)
  end

  defp measure([], _cur, acc), do: acc
  defp measure(["M", x, y | rest], _cur, acc), do: measure(rest, {n(x), n(y)}, acc)

  defp measure(["L", x, y | rest], {px, py}, acc) do
    nxt = {n(x), n(y)}
    measure(rest, nxt, acc + hypot(px - elem(nxt, 0), py - elem(nxt, 1)))
  end

  defp measure(["C", x1, y1, x2, y2, x, y | rest], p0, acc) do
    p1 = {n(x1), n(y1)}
    p2 = {n(x2), n(y2)}
    p3 = {n(x), n(y)}
    measure(rest, p3, acc + curve_length(p0, p1, p2, p3))
  end

  defp curve_length(p0, p1, p2, p3) do
    Enum.reduce(1..16, {0.0, p0}, fn i, {acc, prev} ->
      point = cubic_point(p0, p1, p2, p3, i / 16)
      {acc + hypot(elem(prev, 0) - elem(point, 0), elem(prev, 1) - elem(point, 1)), point}
    end)
    |> elem(0)
  end

  defp hypot(dx, dy), do: :math.sqrt(dx * dx + dy * dy)
  defp n(token), do: String.to_integer(token)

  defp meet do
    assert {:ok, book} = Muro.Load.file(example("meet.muro"))
    Muro.Explore.graph(book)
  end

  defp chain(n) do
    nodes =
      Enum.map(1..n, fn i ->
        %{id: "n#{i}", name: "n#{i}", mode: :run, kind: :def, children: [], transitions: []}
      end)

    edges =
      Enum.map(1..(n - 1), fn i ->
        %{id: "e#{i}", from: "n#{i}", to: "n#{i + 1}", use: :def}
      end)

    %{nodes: nodes, edges: edges}
  end

  defp segment_y(d) do
    d
    |> String.split(~r/[MLC]/, trim: true)
    |> Enum.map(fn chunk ->
      chunk
      |> String.split(~r/\s+/, trim: true)
      |> Enum.map(&String.to_integer/1)
    end)
    |> Enum.chunk_every(2, 1, :discard)
    |> Enum.find_value(fn [a, b] ->
      if length(a) >= 2 and length(b) >= 2 and Enum.at(a, 1) == Enum.at(b, 1) and
           Enum.at(a, 0) != Enum.at(b, 0) do
        Enum.at(a, 1)
      end
    end)
  end
end

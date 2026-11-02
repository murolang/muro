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

    for kind <- ~w(meet step dual) do
      [class] =
        Floki.attribute(parse(html), ~s(#edge-legend li[data-kind="#{kind}"] line), "class")

      assert class == "edge edge-#{kind}"

      [x2] = Floki.attribute(parse(html), ~s(#edge-legend li[data-kind="#{kind}"] line), "x2")
      assert String.to_integer(x2) >= 24
    end
  end

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

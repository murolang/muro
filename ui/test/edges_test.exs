defmodule MuroVisor.EdgesTest do
  use MuroVisor.ConnCase, async: false

  test "meet.muro draws one edge per use, toward the definition", %{conn: conn} do
    view = open_book(conn, example("meet.muro"))
    book = book()
    assert_edges(render(view), Muro.Explore.graph(book))

    kept = Muro.Emit.Name.encode("kept")
    there = Muro.Emit.Name.encode("there")
    wrapped = Muro.Emit.Name.encode("wrapped")
    far = Muro.Emit.Name.encode("far-wrap")
    dom = use_edges(render(view))

    refute Enum.any?(dom, &(&1.from == kept or &1.to == kept))

    incoming =
      for edge <- dom, edge.to == there, edge.use == "meet" do
        edge.from
      end

    assert Enum.sort(incoming) == Enum.sort([wrapped, far])
  end

  test "half_ok.muro and result.muro draw the uses of the checked book", %{conn: conn} do
    for name <- ["half_ok.muro", "result.muro"] do
      view = open_book(conn, example(name))
      html = render(view)
      assert_edges(html, Muro.Explore.graph(book()))

      if name == "result.muro" do
        or_zero = Muro.Emit.Name.encode("orZero")
        refute Enum.any?(use_edges(html), &(&1.from == or_zero or &1.to == or_zero))
      end
    end
  end

  test "a sent definition is one edge per occurrence", %{conn: conn} do
    path =
      write_book("""
      def kept : run Nat := 0

      def idle : run Nat := 0

      session nums := send Nat (send Nat end)

      session back := dual nums

      conform sender : nums := put kept (put kept done)

      conform recv : back := get (kept : Nat) (get (m : Nat) done)

      meet wire : sender with recv
      """)

    view = open_book(conn, path)
    graph = Muro.Explore.graph(book())
    html = render(view)
    assert_edges(html, graph)

    sender = Muro.Emit.Name.encode("sender")
    kept = Muro.Emit.Name.encode("kept")
    idle = Muro.Emit.Name.encode("idle")
    recv = Muro.Emit.Name.encode("recv")
    dom = use_edges(html)

    uses = Enum.filter(dom, &(&1.from == sender and &1.to == kept and &1.use == "def"))
    assert length(uses) == 2
    refute Enum.any?(dom, &(&1.from == kept and &1.to == sender))
    refute Enum.any?(dom, &(&1.from == idle or &1.to == idle))
    refute Enum.any?(dom, &(&1.from == recv and &1.to == kept))
  end

  defp assert_edges(html, graph) do
    dom = use_edges(html)

    assert Enum.map(dom, & &1.id) == Enum.map(graph.edges, &("edge-" <> &1.id))

    for edge <- graph.edges do
      drawn = Enum.find(dom, &(&1.id == "edge-#{edge.id}"))
      assert drawn.from == edge.from
      assert drawn.to == edge.to
      assert drawn.use == to_string(edge.use)
    end
  end
end

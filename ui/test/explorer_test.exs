defmodule MuroVisor.ExplorerTest do
  use MuroVisor.ConnCase, async: false

  test "meet.muro draws the book, keeps the stamp, and shows a refusal", %{conn: conn} do
    path = book!("meet.muro")
    assert {:ok, stamp} = MuroVisor.Book.open(path)
    {:ok, view, _html} = live(conn, "/")

    graph = Muro.Explore.graph(elem(MuroVisor.Book.current(), 1).book)

    for node <- graph.nodes do
      assert has_element?(view, "#node-#{node.id}")
    end

    for edge <- graph.edges do
      assert has_element?(view, "#edge-#{edge.id}")
    end

    ping = Enum.find(graph.nodes, &(&1.name == "ping"))
    assert ping.children != []
    child = hd(ping.children)
    session = view |> element("#node-#{ping.id}") |> render()
    assert session =~ "compound"
    assert session =~ "node-#{child.id}"
    assert has_element?(view, "#node-#{child.id}")

    assert view |> element("#book-stamp") |> render() =~ to_string(stamp)
    otp = view |> element("#outline") |> render()
    assert otp =~ "backend: otp"
    assert otp =~ "handle_info"

    view |> element("#backend-c") |> render_click()
    c_outline = view |> element("#outline") |> render()
    assert c_outline =~ "backend: c"
    refute c_outline =~ "handle_info"
    assert view |> element("#book-stamp") |> render() =~ to_string(stamp)

    step = Enum.find(graph.edges, &(&1.use == :step and &1.proc == "pong" and &1.step == 1))
    view |> element("#edge-#{step.id}") |> render_click()
    assert view |> element("#detail-loc") |> render() =~ ":"
    assert view |> element("#detail-refusal-kind") |> render() =~ "refused"
  end

  test "half_ok shows a C signature, an FSM error, and a node location", %{conn: conn} do
    path = book!("half_ok.muro")
    assert {:ok, _stamp} = MuroVisor.Book.open(path)
    {:ok, view, _html} = live(conn, "/")

    graph = Muro.Explore.graph(elem(MuroVisor.Book.current(), 1).book)
    assert graph.nodes != []
    node = hd(graph.nodes)
    assert has_element?(view, "#node-#{node.id}")

    for edge <- graph.edges do
      assert has_element?(view, "#edge-#{edge.id}")
    end

    view |> element("#backend-c") |> render_click()
    c_outline = view |> element("#outline") |> render()
    assert c_outline =~ "backend: c"
    assert c_outline =~ "half"

    view |> element("#backend-fsm") |> render_click()
    assert view |> element("#outline") |> render() =~ "no session"

    for name <- ["rust", "zig", "otp"] do
      view |> element("#backend-#{name}") |> render_click()
      assert view |> element("#outline") |> render() =~ "backend: #{name}"
    end

    view |> element("#node-#{node.id}") |> render_click()
    loc = view |> element("#detail-loc") |> render()
    assert loc =~ ":"
    refute view |> element("#detail-refusal-kind") |> render() =~ "refused"
  end

  test "a missing book is an error and the opener does not listen" do
    assert {:error, msg} = MuroVisor.open("/tmp/no-such-muro-book.muro")
    assert msg =~ "no such book"
  end

  defp book!(name) do
    path = Path.expand("../../examples/#{name}", __DIR__)
    assert File.regular?(path)
    path
  end
end

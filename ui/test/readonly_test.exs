defmodule MuroVisor.ReadonlyTest do
  use MuroVisor.ConnCase, async: false

  test "clicks and backend switches leave the book byte-identical", %{conn: conn} do
    path = example("meet.muro")
    dir = Path.dirname(path)
    before_file = File.read!(path)
    before_dir = digest(dir)

    view = open_book(conn, path)
    loaded = book()
    graph = Muro.Explore.graph(loaded)

    for node <- graph.nodes do
      view |> element("#node-#{node.id}") |> render_click()
    end

    for edge <- graph.edges do
      view |> element("#edge-#{edge.id}") |> render_click()
    end

    for node <- graph.nodes, child <- node.children do
      view |> element("#configuration-#{child.id}") |> render_click()
    end

    for backend <- ~w(fsm c rust zig otp c fsm zig rust otp) do
      view |> element("#backend-#{backend}") |> render_click()
    end

    assert File.read!(path) == before_file
    assert digest(dir) == before_dir
    assert book() == loaded
  end
end

defmodule MuroVisor.DetailTest do
  use MuroVisor.ConnCase, async: false

  test "clicking a node shows the parser's file, line, and column", %{conn: conn} do
    view = open_book(conn, example("half_ok.muro"))

    for defn <- reported(book()) do
      assert_node(view, defn)
    end

    view = open_book(conn, example("meet.muro"))
    loaded = book()

    for name <- ["pong", "peer-echo", "wire", "kept"] do
      assert_node(view, Enum.find(loaded, &(&1.name == name)))
    end

    view = open_book(conn, example("maybe.muro"))
    from = Enum.find(book(), &(&1.name == "fromMaybe"))
    assert_node(view, from)

    std = Path.expand("../../lib/muro/std/maybe.muro", __DIR__)
    {line, col} = from.loc
    source = std |> File.read!() |> String.split("\n") |> Enum.at(line - 1)
    assert source =~ "fromMaybe"
    assert String.length(source) >= col
  end

  test "clicking an edge shows the checker's refusal and its location", %{conn: conn} do
    view = open_book(conn, example("meet.muro"))
    loaded = book()
    graph = Muro.Explore.graph(loaded)

    refused = Enum.find(graph.edges, &(&1.use == :step and &1.proc == "pong" and &1.step == 1))
    assert_edge(view, graph, loaded, refused)
    assert shown_kind(Muro.Explore.out_of_order(loaded, refused)) == "refused"

    stuck = Enum.find(graph.edges, &(&1.use == :step and &1.proc == "pong" and &1.step == 0))
    assert_edge(view, graph, loaded, stuck)
    assert shown_kind(Muro.Explore.out_of_order(loaded, stuck)) == "immovable"

    for use <- [:meet, :dual] do
      edge = Enum.find(graph.edges, &(&1.use == use))
      assert edge
      assert_edge(view, graph, loaded, edge)
      assert text_of(render(view), "#detail-refusal-kind") == "no refusal"
    end

    view = open_book(conn, example("half_ok.muro"))
    loaded = book()
    graph = Muro.Explore.graph(loaded)
    edge = Enum.find(graph.edges, &(&1.use == :def))
    assert edge
    assert_edge(view, graph, loaded, edge)
    assert text_of(render(view), "#detail-refusal-kind") == "no refusal"
  end

  defp assert_node(view, defn) do
    {line, col} = defn.loc
    id = Muro.Emit.Name.encode(defn.name)
    view |> element("#node-#{id}") |> render_click()
    html = render(view)
    shown = "#{defn.file}:#{line}:#{col}"
    assert text_of(html, "#detail-title") == defn.name
    assert text_of(html, "#detail-loc") == shown
    assert text_of(html, "#detail-refusal-kind") == ""
    assert_in_source(defn.file, line, col, defn.name)
  end

  defp assert_edge(view, graph, loaded, edge) do
    refusal = Muro.Explore.out_of_order(loaded, edge)
    from = Enum.find(graph.nodes, &(&1.id == edge.from))
    view |> element("#edge-#{edge.id}") |> render_click()
    html = render(view)

    assert text_of(html, "#detail-refusal-kind") == shown_kind(refusal)

    assert text_of(html, "#detail-loc") ==
             shown_loc(from.file, Map.get(refusal, :loc) || edge.loc)

    assert text_of(html, "#detail-title") == edge_title(edge)

    case text_of(html, "#detail-loc") do
      "" -> :ok
      shown -> assert_points_at_file(shown)
    end
  end

  defp edge_title(%{use: :step, step: step, proc: proc}), do: "step #{step} #{proc}"
  defp edge_title(%{use: use}), do: to_string(use)

  defp shown_kind(%{kind: :not_a_step}), do: "no refusal"

  defp shown_kind(%{kind: kind, reason: reason}) when is_binary(reason) and reason != "",
    do: "#{kind}: #{reason}"

  defp shown_kind(%{kind: kind}), do: to_string(kind)

  defp shown_loc(file, {line, col}) when is_binary(file) and is_integer(line) and is_integer(col),
    do: "#{file}:#{line}:#{col}"

  defp shown_loc(_file, {path, line, col})
       when is_binary(path) and is_integer(line) and is_integer(col),
       do: "#{path}:#{line}:#{col}"

  defp shown_loc(_file, nil), do: ""

  defp assert_in_source(file, line, col, name) do
    if File.regular?(file) do
      source = file |> File.read!() |> String.split("\n") |> Enum.at(line - 1)
      assert source =~ name
      assert String.length(source) >= col
    end
  end

  defp assert_points_at_file(shown) do
    assert [_, file, line, col] = Regex.run(~r/^(.*):(\d+):(\d+)$/s, shown)

    if File.regular?(file) do
      source = file |> File.read!() |> String.split("\n") |> Enum.at(String.to_integer(line) - 1)
      assert source != nil
      assert String.length(source) >= String.to_integer(col)
    end
  end
end

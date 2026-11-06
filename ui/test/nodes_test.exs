defmodule MuroVisor.NodesTest do
  use MuroVisor.ConnCase, async: false

  test "meet.muro draws each reported definition once", %{conn: conn} do
    assert_reported(conn, "meet.muro")
  end

  test "half_ok.muro draws each reported definition once", %{conn: conn} do
    assert_reported(conn, "half_ok.muro")
  end

  test "result.muro draws the functions and not the Result data", %{conn: conn} do
    html = assert_reported(conn, "result.muro")
    names = source_names(html)
    refute "Result" in names
    assert "pred" in names
    assert "orZero" in names
  end

  test "maybe.muro draws the imported runs and not the data", %{conn: conn} do
    html = assert_reported(conn, "maybe.muro")
    names = source_names(html)
    assert "fromMaybe" in names
    refute "Maybe" in names
    refute "Bool" in names

    from = Enum.find(book(), &(&1.name == "fromMaybe"))
    assert from.file == "std:maybe.muro"
    assert from.mode == :run
  end

  defp assert_reported(conn, name) do
    view = open_book(conn, example(name))
    html = render(view)
    book = book()
    reported = reported(book)
    dom = definition_nodes(html)

    assert Enum.sort(Enum.map(dom, & &1.id)) ==
             Enum.sort(Enum.map(reported, &("node-" <> Muro.Emit.Name.encode(&1.name))))

    for defn <- reported do
      id = "node-" <> Muro.Emit.Name.encode(defn.name)
      node = Enum.find(dom, &(&1.id == id))
      label = "#{defn.mode} #{defn.name}"
      assert node.kind == to_string(Map.get(defn, :kind, :def))
      assert node.mode == to_string(defn.mode)
      assert node.name == label
      assert node.text == label
      assert Enum.count(dom, &(&1.id == id)) == 1
    end

    html
  end

  defp source_names(html) do
    Enum.map(definition_nodes(html), fn node ->
      node.name |> String.split(" ", parts: 2) |> List.last()
    end)
  end
end

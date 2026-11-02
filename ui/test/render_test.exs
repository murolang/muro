defmodule MuroVisor.RenderTest do
  use MuroVisor.ConnCase, async: false

  @unicode "λ<muro__名>"

  test "the svg is well-formed and stable, and ids come from the source names", %{conn: conn} do
    for name <- ["meet.muro", "half_ok.muro", "names.muro"] do
      path = if name == "names.muro", do: fixture(), else: example(name)
      view = open_book(conn, path)
      html = render(view)
      svg = svg_source(html)
      assert well_formed!(svg)
      assert svg_source(render(view)) == svg

      {:ok, again, _} = live(build_conn(), "/?view=all")
      assert svg_source(render(again)) == svg
      assert_ids(html, book())
    end
  end

  test "hyphen, apostrophe, and muro__ names render and click", %{conn: conn} do
    view = open_book(conn, fixture())
    html = render(view)

    for name <- ["peer-echo", "it's", "muro__look", "muro__a-b"] do
      id = Muro.Emit.Name.encode(name)
      refute id =~ "__"
      refute id =~ "-"
      node = Enum.find(definition_nodes(html), &(&1.id == "node-#{id}"))
      assert node.text == "run #{name}"
      assert Enum.count(definition_nodes(html), &(&1.id == "node-#{id}")) == 1

      view |> element("#node-#{id}") |> render_click()
      clicked = render(view)
      defn = Enum.find(book(), &(&1.name == name))
      {line, col} = defn.loc
      assert text_of(clicked, "#detail-title") == name
      assert text_of(clicked, "#detail-loc") == "#{defn.file}:#{line}:#{col}"
    end

    assert well_formed!(svg_source(render(view)))
  end

  test "a unicode name that has to be escaped renders and clicks", %{conn: conn} do
    path = fixture()
    assert {:ok, loaded} = Muro.Load.file(path)

    extra = %{
      name: @unicode,
      mode: :run,
      kind: :def,
      loc: {2, 3},
      file: path
    }

    assert {:ok, _stamp} = MuroVisor.Book.remember(loaded ++ [extra], path)
    {:ok, view, _html} = live(conn, "/?view=all")
    html = render(view)
    id = Muro.Emit.Name.encode(@unicode)
    assert id == "zn0003bbzn00003cmurozuzuzn00540dzn00003e"
    refute id =~ "__"

    node = Enum.find(definition_nodes(html), &(&1.id == "node-#{id}"))
    assert node.text == "run #{@unicode}"
    refute html =~ "λ<muro__"
    assert html =~ "λ&lt;muro__名"
    assert well_formed!(svg_source(html))
    assert svg_source(render(view)) == svg_source(html)

    view |> element("#node-#{id}") |> render_click()
    clicked = render(view)
    assert text_of(clicked, "#detail-title") == @unicode
    assert text_of(clicked, "#detail-loc") == "#{path}:2:3"
    assert well_formed!(svg_source(clicked))
  end

  defp fixture, do: Path.expand("fixtures/names.muro", __DIR__)

  defp assert_ids(html, book) do
    dom = definition_nodes(html)

    for defn <- reported(book) do
      id = "node-" <> Muro.Emit.Name.encode(defn.name)
      assert Enum.count(dom, &(&1.id == id)) == 1
    end
  end
end

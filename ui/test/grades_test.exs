defmodule MuroVisor.GradesTest do
  use MuroVisor.ConnCase, async: false

  test "checker grades mark erased binders and leave an unmarked book alone", %{conn: conn} do
    path = fixture("grades_overlay.muro")
    assert {:ok, book} = Muro.Load.file(path)
    surveyed = MuroVisor.Grades.survey(book)

    assert kernel(book, "gone", "n") == :erased
    assert surveyed["gone"].grade == "erased"
    assert binder(surveyed["gone"], "n").qty == "erased"

    assert kernel(book, "erased-pair", "n") == :erased
    assert surveyed["erased-pair"].grade == "erased"
    assert binder(surveyed["erased-pair"], "n").c == "0"
    assert binder(surveyed["erased-pair"], "n").t == "0"

    assert kernel(book, "erased-proof", "n") == :erased
    assert surveyed["erased-proof"].grade == "erased"

    assert kernel(book, "kept", "n") == :linear
    assert surveyed["kept"].grade == "runtime"
    assert binder(surveyed["kept"], "n").qty == "linear"

    assert kernel(book, "once", "n") == :linear
    assert surveyed["once"].grade == "runtime"
    assert binder(surveyed["once"], "n").c == "1"

    assert kernel(book, "many", "n") == :reuse
    assert binder(surveyed["many"], "n").c == "ω"
    assert surveyed["copied"].grade == "runtime"
    assert binder(surveyed["copied"], "n").qty == "reuse"

    assert surveyed["mixed"].grade == "runtime"
    assert binder(surveyed["mixed"], "p").qty == "erased"
    assert binder(surveyed["mixed"], "n").qty == "linear"

    assert surveyed["plain"].grade == nil
    assert surveyed["plain"].binders == []
    assert surveyed["holds"].grade == nil
    assert surveyed["plain-fn"].grade == nil
    assert surveyed["plain-fn"].binders == []

    view = open_book(conn, path)
    off = render(view)
    refute off =~ "opacity=\"0.35\""
    refute off =~ "grade-erased"
    refute off =~ "id=\"grade-legend\""
    assert node_grade(off, "gone") == "erased"
    assert node_grade(off, "kept") == "runtime"
    assert node_grade(off, "plain") == nil

    view |> element("#grade-toggle") |> render_click()
    assert_patch(view, "/?view=all&grades=on")
    on = render(view)
    assert on =~ "id=\"grade-legend\""
    assert on =~ "runtime, full opacity"
    assert on =~ "erased, grade 0, faded"
    assert on =~ "linear, used once"
    assert on =~ "reuse, may be copied"
    assert opacity(on, "gone") == "0.35"
    assert opacity(on, "kept") == "1"
    assert opacity(on, "plain") == nil
    assert on =~ "class=\"binder grade-erased\""
    assert binder_row(on, "gone", "n") =~ "data-qty=\"erased\""
    assert binder_row(on, "plain-fn", "n") == nil

    view |> element("#grade-toggle") |> render_click()
    assert_patch(view, "/?view=all")
    again = render(view)
    refute again =~ "opacity=\"0.35\""
    refute again =~ "grade-erased"
  end

  test "a book with no grades does not invent faded nodes", %{conn: conn} do
    path = fixture("plain.muro")
    assert {:ok, book} = Muro.Load.file(path)
    surveyed = MuroVisor.Grades.survey(book)
    assert Enum.all?(surveyed, fn {_name, info} -> info.grade == nil and info.binders == [] end)

    assert {:ok, _stamp} = MuroVisor.Book.open(path)
    {:ok, view, _html} = live(conn, "/?view=all&grades=on")
    html = render(view)
    assert html =~ "id=\"grade-legend\""

    html
    |> parse()
    |> Floki.find("#book-graph g[data-kind]")
    |> Enum.each(fn node ->
      assert Floki.attribute(node, "data-grade") == []
      assert Floki.attribute(node, "opacity") == []
      refute attr(node, "class") =~ "grade-"
    end)

    assert Floki.find(parse(html), "#book-graph [data-qty]") == []
  end

  defp fixture(name), do: Path.expand("fixtures/#{name}", __DIR__)

  defp kernel(book, defn, binder) do
    book
    |> Enum.find(&(&1.name == defn))
    |> qty(binder)
    |> Muro.Grade.kernel_qty()
  end

  defp qty(defn, name),
    do: find_qty(Map.get(defn, :type), name) || find_qty(Map.get(defn, :body), name)

  defp find_qty({:pi, q, _, name, _}, name), do: q
  defp find_qty({:lam, q, _, name, _}, name), do: q

  defp find_qty(tuple, name) when is_tuple(tuple) do
    Enum.find_value(Tuple.to_list(tuple), &find_qty(&1, name))
  end

  defp find_qty(list, name) when is_list(list), do: Enum.find_value(list, &find_qty(&1, name))
  defp find_qty(_term, _name), do: nil

  defp binder(info, name), do: Enum.find(info.binders, &(&1.name == name))

  defp node_grade(html, name), do: html |> graph_node(name) |> attr("data-grade")

  defp opacity(html, name), do: html |> graph_node(name) |> attr("opacity")

  defp graph_node(html, name) do
    html
    |> parse()
    |> Floki.find("#book-graph g[data-kind]")
    |> Enum.find(fn node ->
      attr(node, "data-name") in ["run #{name}", "evidence #{name}", "spec #{name}"]
    end)
  end

  defp binder_row(html, defn, name) do
    html
    |> parse()
    |> Floki.find("#grade-binders li[data-def=\"#{defn}\"][data-binder=\"#{name}\"]")
    |> case do
      [] -> nil
      nodes -> Floki.raw_html(nodes)
    end
  end

  defp attr(nil, _name), do: nil

  defp attr(node, name) do
    case Floki.attribute(node, name) do
      [value | _] -> value
      [] -> nil
    end
  end
end

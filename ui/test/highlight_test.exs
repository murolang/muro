defmodule MuroVisor.HighlightTest do
  use MuroVisor.ConnCase, async: false

  test "a spec and its dual keep the printer's text and wear lexer classes", %{conn: conn} do
    path = example("meet.muro")
    assert {:ok, _} = MuroVisor.Book.open(path)
    meet = meeting(path, "wire")
    {:ok, _view, html} = live(conn, "/?meet=wire")

    assert text_of(html, "#context-spec") == meet.spec
    assert text_of(html, "#context-dual") == meet.dual
    assert meet.spec =~ "recv Nat (send Nat end)"
    refute meet.spec =~ "\n"

    assert saw?(html, "#context-spec span.k", "recv")
    assert saw?(html, "#context-spec span.kt", "Nat")
    assert saw?(html, "#context-dual span.k", "send")
    assert saw?(html, "#context-dual span.kt", "Nat")
    assert class_text(html, "#lane-left tspan.n") != []
    assert class_text(html, "#sequence text.step-no tspan") == []

    {:ok, _view, picker} = live(conn, "/")
    assert text_of(picker, ~s(section[data-session="ping"] code)) == meet.spec
    assert saw?(picker, ~s(section[data-session="ping"] code span.k), "recv")
    assert saw?(picker, ~s(section[data-session="ping"] code span.kt), "Nat")
  end

  test "a numeral is a literal, and a long spec wraps onto the same tokens", %{conn: conn} do
    {_path, meet} = digit_meet()
    {:ok, _view, html} = live(conn, "/?meet=#{URI.encode_www_form(meet.name)}")
    assert text_of(html, "#context-spec") == meet.spec
    assert class_text(html, "#context-spec span.mi") != []
    assert class_text(html, "#context-spec span.kt") != []

    assert {:ok, _} = MuroVisor.Book.open(example("value-protocols.muro"))
    book = book()
    assert {:ok, %{proto: proto}} = Muro.Check.open_session(book, "server")
    flat = Muro.Session.show_proto(proto)
    laid = MuroVisor.Code.protocol(proto)
    assert String.length(flat) > MuroVisor.Code.width()
    assert laid =~ "\n"
    assert sigils(laid) == sigils(flat)

    for line <- String.split(laid, "\n") do
      assert String.length(line) <= MuroVisor.Code.width(), line
    end

    {:ok, _view, html} = live(conn, "/?meet=headers-wire")
    shown = text_of(html, "#context-spec")
    assert shown =~ "\n"
    assert sigils(shown) == sigils(flat)
    assert saw?(html, "#context-spec span.k", "case")
    assert saw?(html, "#context-spec span.n", "Frame")
    assert class_text(html, "#context-spec span.p") != []
    assert class_text(html, "#context-spec span.o") != []
    dual = MuroVisor.Code.protocol(Muro.Session.dual(proto))
    assert text_of(html, "#context-dual") == dual
    assert sigils(dual) == sigils(Muro.Session.show_proto(Muro.Session.dual(proto)))
  end

  test "opened sessions lay out to the printer's tokens" do
    for file <- ["meet.muro", "value-protocols.muro", "session-calls.muro"] do
      assert {:ok, _} = MuroVisor.Book.open(example(file))

      for %{kind: :session, name: name} <- book(), is_binary(name) do
        case Muro.Check.open_session(book(), name) do
          {:ok, %{proto: proto}} ->
            flat = Muro.Session.show_proto(proto)
            laid = MuroVisor.Code.protocol(proto)
            assert sigils(flat) == sigils(laid), "#{file} #{name}\n#{laid}"

          _ ->
            :ok
        end
      end
    end
  end

  test "the outline keeps its text and marks keywords, names, and literals", %{conn: conn} do
    path = example("session-calls.muro")
    assert {:ok, _} = MuroVisor.Book.open(path)
    {:ok, view, html} = live(conn, "/")
    outline = MuroVisor.Outline.render(book(), path, :otp)

    assert pre_text(html, "#outline-names") == "names: #{outline.names}"
    assert pre_text(html, "#outline-signatures") == outline.signatures
    assert pre_text(html, "#outline-layouts") == "layouts:\n#{outline.layouts}"
    assert pre_text(html, "#outline-clauses") == outline.clauses

    assert saw?(html, "#outline-clauses span.k", "def") or
             saw?(html, "#outline-clauses span.kd", "def")

    assert class_text(html, "#outline span.n") != []

    view |> element("#backend-c") |> render_click()
    html = render(view)
    c_outline = MuroVisor.Outline.render(book(), path, :c)
    assert pre_text(html, "#outline-layouts") == "layouts:\n#{c_outline.layouts}"
    assert class_text(html, "#outline span.mi") != []
  end

  test "detail shows the definition from its own line, with the column marked", %{conn: conn} do
    path = example("meet.muro")
    view = open_book(conn, path)
    kept = Enum.find(book(), &(&1.name == "kept"))
    {line, col} = kept.loc
    assert line > 1

    view |> element("#node-#{Muro.Emit.Name.encode("kept")}") |> render_click()
    html = render(view)
    assert text_of(html, "#detail-loc") == "#{kept.file}:#{line}:#{col}"
    assert text_of(html, "#detail-title") == "kept"

    rows = html |> parse() |> Floki.find("#detail-source .row")
    assert rows != []
    assert Floki.text(Floki.find(hd(rows), ".ln")) == Integer.to_string(line)

    source = source_lines(kept.file)

    for row <- rows do
      [n] = Floki.attribute(row, "data-line")
      assert Floki.text(Floki.find(row, "code")) == Enum.at(source, String.to_integer(n) - 1)
    end

    marked = Enum.filter(rows, &(Floki.attribute(&1, "class") |> List.first() =~ "marked"))
    assert [only] = marked
    assert Floki.attribute(only, "data-line") == [Integer.to_string(line)]
    assert saw?(html, "#detail-source span.kd", "def")
    assert saw?(html, "#detail-source span.nf", "kept")
    assert saw?(html, "#detail-source span.kt", "run")
    assert saw?(html, "#detail-source span.kt", "Nat")
    assert saw?(html, "#detail-source span.mi", "0")
    here = Floki.find(parse(html), "#detail-source .row.marked .here")
    assert here != []
    assert Enum.at(source, line - 1) =~ Floki.text(hd(here))

    id = "node-#{Muro.Emit.Name.encode("kept")}"
    node = Enum.find(definition_nodes(html), &(&1.id == id))
    assert node.text == "run kept"
    assert saw?(html, "##{id} tspan.kt", "run")
    assert saw?(html, "##{id} tspan.n", "kept")
  end

  test "detail shows a whole multi-line definition", %{conn: conn} do
    path = example("value-protocols.muro")
    view = open_book(conn, path)
    late = Enum.find(book(), &(&1.name == "late"))
    {line, col} = late.loc
    {start, stop} = late.extent
    {:ok, src} = File.read(late.file)
    slice = binary_part(src, start, stop - start)
    lines = String.split(String.trim_trailing(slice, "\n"), "\n")
    assert length(lines) > 1

    view |> element("#node-#{Muro.Emit.Name.encode("late")}") |> render_click()
    html = render(view)
    rows = html |> parse() |> Floki.find("#detail-source .row")
    assert length(rows) == length(lines)
    assert Floki.text(Floki.find(hd(rows), ".ln")) == Integer.to_string(line)

    for {row, text} <- Enum.zip(rows, lines) do
      assert Floki.text(Floki.find(row, "code")) == text
    end

    assert saw?(html, "#detail-source span.k", "match")
    assert saw?(html, "#detail-source span.kt", "run")
    assert saw?(html, "#detail-source span.n", "Bool")
    assert saw?(html, "#detail-source span.o", "→")

    marked = Enum.filter(rows, &(Floki.attribute(&1, "class") |> List.first() =~ "marked"))
    assert [only] = marked
    assert Floki.attribute(only, "data-line") == [Integer.to_string(line)]
    assert Floki.find(parse(html), "#detail-source .here") != []
    assert col >= 1
  end

  test "a definition longer than forty lines folds the tail" do
    rows = for n <- 1..45, do: %{n: n, marked: false, html: Integer.to_string(n)}
    {:safe, iodata} = MuroVisor.Code.source_block(%{id: "detail-source", label: nil, rows: rows})
    html = IO.iodata_to_binary(iodata)
    parsed = Floki.parse_fragment!(html)
    assert Floki.find(parsed, "details.more") != []
    assert Floki.attribute(hd(Floki.find(parsed, "details.more")), "open") == []
    assert length(Floki.find(parsed, "#detail-source .row")) == 45

    marked = List.update_at(rows, 41, &%{&1 | marked: true})

    {:safe, iodata} =
      MuroVisor.Code.source_block(%{id: "detail-source", label: nil, rows: marked})

    open = IO.iodata_to_binary(iodata) |> Floki.parse_fragment!() |> Floki.find("details.more")
    assert Floki.attribute(hd(open), "open") == ["open"]
  end

  test "a refused edge and a configuration mark the checker's locations", %{conn: conn} do
    path = example("meet.muro")
    view = open_book(conn, path)
    loaded = book()
    graph = Muro.Explore.graph(loaded)

    edge =
      Enum.find(graph.edges, &(&1.use == :step and &1.proc == "pong" and &1.step == 0))

    view |> element("#edge-#{edge.id}") |> render_click()
    html = render(view)
    assert text_of(html, "#detail-refusal-kind") != ""
    assert_marked_loc(html, "#detail-source")

    child =
      graph.nodes
      |> Enum.find(&(&1.children != []))
      |> Map.fetch!(:children)
      |> hd()

    view |> element("#configuration-#{child.id}") |> render_click()
    html = render(view)
    assert text_of(html, "#detail-loc") =~ "left "
    assert_marked_loc(html, "#detail-source-left")
    assert_marked_loc(html, "#detail-source-right")
  end

  test "sequence code is highlighted and the notes stay plain", %{conn: conn} do
    assert {:ok, _} = MuroVisor.Book.open(example("meet.muro"))
    {:ok, _view, html} = live(conn, "/?meet=window-wire")
    assert text_of(html, "#sequence .evidence-badge") == "w ⊢ d ≤ w"
    assert class_text(html, "#sequence .evidence-badge tspan") != []
    assert saw?(html, "#sequence .evidence-badge tspan.o", "⊢")
    assert saw?(html, "#sequence .evidence-badge tspan.o", "≤")
    assert class_text(html, "#sequence text.arrow-label tspan") != []
    assert class_text(html, "#sequence text.step-no tspan") == []

    {:ok, _view, html} = live(conn, "/?meet=arm")
    assert text_of(html, "#sequence text.choice-note") =~ "chooses branch"
    assert class_text(html, "#sequence text.choice-note tspan") == []
    assert class_text(html, "#sequence text.loop-note tspan") == []

    {:ok, _view, html} = live(conn, "/")
    assert text_of(html, ~s(.meet-row[data-meet="window-wire"] .evidence)) == "{d ≤ w}"
    assert class_text(html, ~s(.meet-row[data-meet="window-wire"] .evidence span)) != []
  end

  defp meeting(path, name) do
    catalog = MuroVisor.Meetings.catalog(book(), Muro.Explore.graph(book()), path)
    Enum.find(catalog.meetings, &(&1.name == name))
  end

  defp digit_meet do
    Enum.find_value(
      ["session-calls.muro", "value-protocols.muro", "async-meetings.muro"],
      fn file ->
        path = example(file)
        assert {:ok, _} = MuroVisor.Book.open(path)
        catalog = MuroVisor.Meetings.catalog(book(), Muro.Explore.graph(book()), path)

        case Enum.find(catalog.meetings, &(&1.spec =~ ~r/\d/)) do
          nil -> nil
          meet -> {path, meet}
        end
      end
    ) || flunk("no session spec contains a numeral")
  end

  defp class_text(html, selector) do
    html |> parse() |> Floki.find(selector) |> Enum.map(&Floki.text/1)
  end

  defp saw?(html, selector, text) do
    Enum.any?(class_text(html, selector), &(String.trim(&1) == text))
  end

  defp pre_text(html, selector) do
    html |> parse() |> Floki.find("#{selector} pre") |> Floki.text()
  end

  defp source_lines(file) do
    {:ok, src} = File.read(file)
    lines = String.split(src, "\n")

    if lines != [] and List.last(lines) == "" and String.ends_with?(src, "\n") do
      List.delete_at(lines, -1)
    else
      lines
    end
  end

  defp assert_marked_loc(html, id) do
    loc = text_of(html, "#detail-loc")

    line =
      cond do
        String.ends_with?(id, "-left") -> side_line(loc, "left")
        String.ends_with?(id, "-right") -> side_line(loc, "right")
        true -> trailing_line(loc)
      end

    rows = html |> parse() |> Floki.find("#{id} .row.marked")
    assert rows != []
    assert Enum.all?(rows, &(Floki.attribute(&1, "data-line") == [line]))
    assert Floki.find(parse(html), "#{id} .here") != []
  end

  defp side_line(loc, side) do
    assert [_, line, _col] = Regex.run(~r/#{side} \S+:(\d+):(\d+)/, loc)
    line
  end

  defp trailing_line(loc) do
    assert [_, line, _col] = Regex.run(~r/:(\d+):(\d+)\s*$/, loc)
    line
  end

  defp sigils(src) do
    src
    |> Muro.Lexer.tokenize()
    |> Enum.flat_map(fn
      {:whitespace, _, _} -> []
      {kind, a, b} -> [{kind, :binary.part(src, a, b - a)}]
    end)
  end
end

defmodule MuroVisor.MeetingViewTest do
  use MuroVisor.ConnCase, async: false

  test "the picker lists every meeting in meet.muro", %{conn: conn} do
    assert {:ok, _stamp} = MuroVisor.Book.open(example("meet.muro"))
    {:ok, _view, html} = live(conn, "/")
    refute html =~ "id=\"book-graph\""
    assert html =~ "id=\"meeting-picker\""

    names = attr_list(html, "#meeting-picker a", "data-meet")

    assert names ==
             ~w(wire echo-wire arm drop wrapped far-wrap sized-wire window-wire)

    assert length(names) == 8

    groups = attr_list(html, "#meeting-picker section", "data-session")
    assert groups == ~w(ping choice open box sized window)

    wire = row(html, "wire")
    assert wire["data-left"] == "pong"
    assert wire["data-right"] == "peer"
    assert wire["data-base"] == "ping"
    assert wire["data-steps"] == "2"
    assert wire["data-evidence"] == ""
    assert row_text(html, "wire") =~ "pong ⇄ peer"
    assert text_of(html, ~s(section[data-session="ping"] code)) =~ "recv Nat (send Nat end)"

    window = row(html, "window-wire")
    assert window["data-steps"] == "2"
    assert window["data-evidence"] == "{d ≤ w}"
    assert row_text(html, "window-wire") =~ "{d ≤ w}"
  end

  test "picking a meeting patches its sequence, and the url opens it", %{conn: conn} do
    assert {:ok, _} = MuroVisor.Book.open(example("meet.muro"))
    {:ok, view, html} = live(conn, "/")
    assert html =~ "href=\"/?meet=wire\""
    assert html =~ "href=\"/?meet=echo-wire\""

    view |> element(~s(a[data-meet="wire"])) |> render_click()
    assert_patch(view, "/?meet=wire")
    assert steps(render(view)) == wire_steps()

    {:ok, echo, html} = live(conn, "/?meet=echo-wire")
    assert steps(html) == echo_steps()
    assert text_of(html, "#lane-left") =~ "echo"
    assert text_of(html, "#lane-left") =~ "ping"
    assert text_of(html, "#lane-right") =~ "peer-echo"
    assert text_of(html, "#lane-right") =~ "dual ping"

    {:ok, arm, html} = live(conn, "/?meet=arm")
    assert steps(html) == arm_steps()
    assert text_of(html, "#sequence") =~ "chooses branch 0 of 2"
    assert text_of(html, "#sequence") =~ "0"
    assert html =~ ~s(data-arity="2")
    assert_on_lifelines(html)

    {:ok, window, html} = live(conn, "/?meet=window-wire")
    assert steps(html) == window_steps()
    assert text_of(html, "#sequence .evidence-badge") == "w ⊢ d ≤ w"
    assert html =~ "evidence-pill"
    fills = html |> parse() |> Floki.attribute("#sequence text.step-no", "fill")
    assert fills != []
    assert Enum.uniq(fills) == ["#1c1917"]
    assert_on_lifelines(html)

    for view <- [echo, arm, window] do
      assert render(view) =~ "id=\"sequence\""
      refute render(view) =~ "id=\"book-graph\""
    end
  end

  test "the context panel shows the session, its dual, and the conforms", %{conn: conn} do
    assert {:ok, _} = MuroVisor.Book.open(example("meet.muro"))
    {:ok, view, html} = live(conn, "/?meet=wire")

    assert text_of(html, "#meeting-checked") == "checked"
    assert text_of(html, "#context-session") == "ping"
    assert text_of(html, "#context-spec") =~ "recv Nat (send Nat end)"
    assert text_of(html, "#context-dual-name") == "back"
    assert text_of(html, "#context-dual") =~ "send Nat (recv Nat end)"
    assert text_of(html, "#lane-left") =~ "pong"
    assert text_of(html, "#lane-right") =~ "dual ping"

    pong = Enum.find(book(), &(&1.name == "pong"))
    {line, col} = pong.loc
    refute html =~ "<h2>Detail</h2>"
    assert text_of(html, "#conform-pong") == "pongmeet.muro:#{line}:#{col}"
    refute text_of(html, "#conform-pong") =~ pong.file

    view |> element("#conform-pong") |> render_click()
    clicked = render(view)
    assert text_of(clicked, "#detail-title") == "pong"
    assert text_of(clicked, "#detail-loc") == "#{pong.file}:#{line}:#{col}"
    assert clicked =~ "id=\"sequence\""
    assert steps(clicked) == wire_steps()

    view |> element("#conform-peer") |> render_click()
    peer = render(view)
    assert text_of(peer, "#detail-title") == "peer"
  end

  test "the backend switch redraws the host outline and keeps the meeting", %{conn: conn} do
    path = example("meet.muro")
    assert {:ok, stamp} = MuroVisor.Book.open(path)
    counter = count_checks()
    {:ok, view, html} = live(conn, "/?meet=wire")
    assert text_of(html, "#outline-backend") == "otp"
    refute text_of(html, "#outline") =~ "backend:"
    assert text_of(html, "#outline-for") == "meeting: wire"
    assert text_of(html, "#book-stamp") =~ to_string(stamp)
    assert checks(counter) == 0
    otp = text_of(html, "#outline")

    seen =
      Enum.reduce([:rust, :fsm, :c, :zig, :otp], %{otp: otp}, fn backend, seen ->
        view |> element("#backend-#{backend}") |> render_click()
        html = render(view)
        text = text_of(html, "#outline")
        assert text_of(html, "#outline-backend") == "#{backend}"
        refute text =~ "backend:"
        assert text_of(html, "#outline-for") == "meeting: wire"
        assert text_of(html, "#book-stamp") =~ to_string(stamp)
        assert steps(html) == wire_steps()
        assert checks(counter) == 0
        assert book() |> Enum.find(&(&1.name == "wire"))

        case Map.fetch(seen, backend) do
          {:ok, earlier} -> assert text == earlier
          :error -> :ok
        end

        Map.put(seen, backend, text)
      end)

    refute seen.rust == seen.otp
    refute seen.fsm == seen.otp
    assert seen.otp =~ "handle_info"
    refute seen.rust =~ "handle_info"
  end

  test "all definitions is the book graph, and the sequence fits the pane", %{conn: conn} do
    assert {:ok, _} = MuroVisor.Book.open(example("meet.muro"))
    {:ok, view, _html} = live(conn, "/")
    view |> element("#view-all") |> render_click()
    assert_patch(view, "/?view=all")
    html = render(view)
    assert html =~ "id=\"book-graph\""
    refute html =~ "id=\"sequence\""
    assert definition_nodes(html) != []

    view |> element("#view-meetings") |> render_click()
    assert_patch(view, "/")
    assert render(view) =~ "id=\"meeting-picker\""

    page = html_response(get(conn, "/?meet=sized-wire"), 200)

    assert page =~
             ".meeting-pane, .sequence-wrap, .picker { max-width: 100%; overflow-x: hidden; }"

    assert page =~ "overflow-wrap: anywhere"
    refute page =~ "overflow-wrap: normal"
    assert page =~ "minmax(0, 1fr)"
    assert page =~ "font-size: 14px"
    assert page =~ "justify-content: center"
    refute page =~ "id=\"book-graph\""
    assert text_of(page, "#sequence") =~ "rep n 0"
    refute page =~ ~r/\bwidth="\d{4,}"/
    assert_on_lifelines(page)
  end

  test "other books that meet render a sequence", %{conn: conn} do
    for {file, meet} <- [
          {"async-meetings.muro", "stream-sync"},
          {"session-calls.muro", "choice-wire"},
          {"computed.muro", "arm1"},
          {"temporal.muro", "inflight"},
          {"value-protocols.muro", "headers-wire"}
        ] do
      assert {:ok, _} = MuroVisor.Book.open(example(file))
      {:ok, _view, html} = live(conn, "/?meet=#{meet}")
      assert html =~ "id=\"sequence\""
      assert html =~ "id=\"lane-left\""
      assert html =~ "id=\"lane-right\""
      assert text_of(html, "#meeting-checked") == "checked"
      assert text_of(html, "#outline-backend") == "otp"

      rows = steps(html)

      assert Enum.all?(rows, fn {kind, from, to, label, _branch} ->
               kind in ["send", "choice", "terminal"] and label not in [nil, ""] and
                 (kind == "terminal" or (is_binary(from) and is_binary(to)))
             end)

      assert rows != []
    end
  end

  defp wire_steps do
    [
      {"send", "peer", "pong", "1", nil},
      {"send", "pong", "peer", "1", nil},
      {"terminal", nil, nil, "done", nil}
    ]
  end

  defp echo_steps do
    [
      {"send", "peer-echo", "echo", "2", nil},
      {"send", "echo", "peer-echo", "k", nil},
      {"terminal", nil, nil, "done", nil}
    ]
  end

  defp arm_steps do
    [
      {"choice", "taker", "giver", "pick0", "0"},
      {"terminal", nil, nil, "done", nil}
    ]
  end

  defp window_steps do
    [
      {"send", "window-client", "window-server", "8", nil},
      {"send", "window-server", "window-client", "w", nil},
      {"terminal", nil, nil, "done", nil}
    ]
  end

  defp steps(html) do
    html
    |> parse()
    |> Floki.find("#sequence .seq-row")
    |> Enum.map(fn row ->
      {
        attr(row, "data-kind"),
        attr(row, "data-from"),
        attr(row, "data-to"),
        attr(row, "data-label"),
        attr(row, "data-branch")
      }
    end)
  end

  defp assert_on_lifelines(html) do
    doc = parse(html)
    [left, right] = Floki.find(doc, "#sequence line.lifeline")
    lx = attr(left, "x1")
    rx = attr(right, "x1")
    assert attr(left, "x2") == lx
    assert attr(right, "x2") == rx
    assert attr(left, "y2") == attr(right, "y2")
    assert String.to_integer(attr(left, "y2")) > String.to_integer(attr(left, "y1"))
    assert abs(String.to_integer(rx) - String.to_integer(lx)) == 420
    assert html =~ ~r/markerunits="strokeWidth"/i

    arrows = Floki.find(doc, "#sequence line.arrow")
    assert arrows != []
    ends = Enum.sort([lx, rx])

    for arrow <- arrows do
      assert Enum.sort([attr(arrow, "x1"), attr(arrow, "x2")]) == ends
      assert attr(arrow, "y1") == attr(arrow, "y2")
      assert attr(arrow, "marker-end") == "url(#seq-arrow)"
    end

    mid = Integer.to_string(div(String.to_integer(lx) + String.to_integer(rx), 2))

    for label <- Floki.find(doc, "#sequence text.arrow-label") do
      assert attr(label, "text-anchor") == "middle"
      assert attr(label, "x") == mid
    end

    numbers = doc |> Floki.find("#sequence text.step-no") |> Enum.map(&Floki.text/1)
    assert numbers == Enum.map(1..length(numbers), &Integer.to_string/1)

    life_bot = attr(left, "y2")
    boxes = Floki.find(doc, "#sequence g.lane-box rect")
    assert length(boxes) == 4
    assert Enum.count(boxes, &(attr(&1, "y") == life_bot)) == 2

    for term <- Floki.find(doc, "#sequence g.terminal") do
      marks = Floki.find(term, "rect.term-mark")
      assert length(marks) == 2

      centres =
        Enum.map(marks, fn mark ->
          String.to_integer(attr(mark, "x")) + div(String.to_integer(attr(mark, "width")), 2)
        end)

      assert Enum.sort(centres) == Enum.sort([String.to_integer(lx), String.to_integer(rx)])
    end
  end

  defp row(html, name) do
    [node] = html |> parse() |> Floki.find(~s(#meeting-picker a[data-meet="#{name}"]))

    Map.new(~w(data-left data-right data-base data-steps data-evidence), fn key ->
      {key, attr(node, key)}
    end)
  end

  defp row_text(html, name) do
    html |> parse() |> Floki.find(~s(a[data-meet="#{name}"])) |> Floki.text()
  end

  defp attr_list(html, selector, name) do
    html
    |> parse()
    |> Floki.find(selector)
    |> Enum.map(&attr(&1, name))
  end

  defp attr(node, name) do
    case Floki.attribute(node, name) do
      [value | _] -> value
      [] -> nil
    end
  end

  defp count_checks do
    {:ok, agent} = Agent.start_link(fn -> 0 end)
    :ok = Muro.Check.check_hook(fn -> Agent.update(agent, &(&1 + 1)) end)

    on_exit(fn ->
      Muro.Check.check_hook(nil)
      if Process.alive?(agent), do: Agent.stop(agent)
    end)

    agent
  end

  defp checks(agent), do: Agent.get(agent, & &1)
end

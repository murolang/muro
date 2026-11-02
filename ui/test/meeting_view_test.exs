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
    assert row_text(html, "wire") =~ "pong with peer"

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
    assert text_of(html, "#sequence") =~ "pick0"
    assert text_of(html, "#sequence") =~ "0"

    {:ok, window, html} = live(conn, "/?meet=window-wire")
    assert steps(html) == window_steps()

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
    assert text_of(html, "#conform-pong") =~ "pong"
    assert text_of(html, "#conform-pong") =~ "#{pong.file}:#{line}:#{col}"

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
    assert text_of(html, "#outline") =~ "backend: otp\n"
    assert text_of(html, "#outline-for") == "meeting: wire"
    assert text_of(html, "#book-stamp") =~ to_string(stamp)
    assert checks(counter) == 0
    otp = text_of(html, "#outline")

    seen =
      Enum.reduce([:rust, :fsm, :c, :zig, :otp], %{otp: otp}, fn backend, seen ->
        view |> element("#backend-#{backend}") |> render_click()
        html = render(view)
        text = text_of(html, "#outline")
        assert text =~ "backend: #{backend}\n"
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
    assert page =~ ".meeting-pane, .sequence, .picker { max-width: 100%; overflow-x: hidden; }"
    assert page =~ "overflow-wrap: anywhere"
    assert page =~ "minmax(0, 1fr)"
    refute page =~ "id=\"book-graph\""
    assert page =~ "rep n 0"
    refute page =~ ~r/\bwidth="\d{4,}"/
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
      assert text_of(html, "#outline") =~ "backend: otp"

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

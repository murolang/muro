defmodule MuroVisor.SessionTest do
  use MuroVisor.ConnCase, async: false

  test "a branching meeting draws the configurations the checker walked", %{conn: conn} do
    view = open_book(conn, example("meet.muro"))
    book = book()
    assert_meetings(view, book)

    arm = Enum.find(book, &(&1.kind == :meet and &1.name == "arm"))
    walked = walked(book, arm)
    assert Enum.any?(walked.transitions, &(Enum.join(&1.label, " ") =~ "pick0"))

    group = meeting(render(view), "choice", "arm")
    assert group.class =~ "compound"
    assert Enum.any?(group.transitions, &(&1.label =~ "pick0"))
    assert_transition_paths(group)
  end

  test "a recursive meeting draws its loop", %{conn: conn} do
    view = open_book(conn, example("async-meetings.muro"))
    book = book()
    assert_meetings(view, book)

    sync = Enum.find(book, &(&1.kind == :meet and &1.name == "stream-sync"))
    walked = walked(book, sync)
    assert Enum.any?(walked.transitions, &(&1.from == &1.to))

    session = session_name(book, sync.left)
    group = meeting(render(view), session, "stream-sync")
    assert group.class =~ "compound"
    assert Enum.any?(group.transitions, &(&1.from == &1.to and &1.label =~ "put 0"))
    assert_transition_paths(group)

    loop = Enum.find(group.transitions, &(&1.from == &1.to))
    assert loop.d =~ " C "
  end

  test "a meeting that fails to check is that error and has no configurations", %{conn: conn} do
    path =
      write_book("""
      session choice := choose end (send Nat end)
      session offered := dual choice
      conform taker : choice :=
        pick1 stop
      conform giver : offered :=
        cover done (get Nat done)
      meet arm : taker with giver
      """)

    assert {:error, msg} = Muro.Load.file(path)
    assert {:error, ^msg} = MuroVisor.Book.open(path)
    assert msg =~ "arm:"
    assert msg =~ "diverged"

    {:ok, view, _html} = live(conn, "/")
    html = render(view)
    assert text_of(html, "#book-error") == msg
    assert definition_nodes(html) == []
    assert meeting_groups(html) == []
    refute html =~ "cfg-"

    view |> element("#backend-fsm") |> render_click()
    html = render(view)
    assert text_of(html, "#book-error") == msg
    assert meeting_groups(html) == []
    assert text_of(html, "#outline") == ""
  end

  defp assert_meetings(view, book) do
    html = render(view)
    groups = meeting_groups(html)
    meetings = Enum.filter(book, &(Map.get(&1, :kind) == :meet))

    assert Enum.sort(Enum.map(groups, & &1.id)) ==
             Enum.sort(
               Enum.map(meetings, fn meet ->
                 session = session_name(book, meet.left)
                 "meeting-m-#{Muro.Emit.Name.encode(session)}-#{Muro.Emit.Name.encode(meet.name)}"
               end)
             )

    for meet <- meetings do
      session = session_name(book, meet.left)
      group = meeting(html, session, meet.name)
      walked = walked(book, meet)
      prefix = "cfg-#{Muro.Emit.Name.encode(session)}-#{Muro.Emit.Name.encode(meet.name)}"

      assert group.children |> Enum.map(& &1.id) ==
               Enum.map(walked.states, &"node-#{prefix}-#{&1.id}")

      assert group.children |> Enum.map(& &1.state) ==
               Enum.map(walked.states, &Integer.to_string(&1.id))

      assert group.transitions |> Enum.map(&{&1.from, &1.to, &1.label}) ==
               Enum.map(walked.transitions, fn t ->
                 {"#{prefix}-#{t.from}", "#{prefix}-#{t.to}", Enum.join(t.label, " ")}
               end)

      session_html = view |> element("#node-#{Muro.Emit.Name.encode(session)}") |> render()
      assert session_html =~ "compound"
      assert session_html =~ group.id
    end
  end

  defp meeting(html, session, meet) do
    id = "meeting-m-#{Muro.Emit.Name.encode(session)}-#{Muro.Emit.Name.encode(meet)}"
    Enum.find(meeting_groups(html), &(&1.id == id))
  end

  defp assert_transition_paths(group) do
    for t <- group.transitions do
      assert is_binary(t.d) and t.d != ""

      if t.from == t.to do
        assert t.d =~ " C "
      else
        assert t.d =~ " L "
      end
    end
  end
end

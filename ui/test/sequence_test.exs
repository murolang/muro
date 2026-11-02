defmodule MuroVisor.SequenceTest do
  use ExUnit.Case, async: true

  setup do
    {:ok, catalog: catalog("meet.muro")}
  end

  test "meet.muro lists every meeting under its base session, in source order", %{
    catalog: catalog
  } do
    assert Enum.map(catalog.meetings, & &1.name) ==
             ~w(wire echo-wire arm drop wrapped far-wrap sized-wire window-wire)

    assert length(catalog.meetings) == 8

    assert Enum.map(catalog.groups, fn group ->
             {group.base, Enum.map(group.meetings, & &1.name)}
           end) == [
             {"ping", ["wire", "echo-wire"]},
             {"choice", ["arm"]},
             {"open", ["drop"]},
             {"box", ["wrapped", "far-wrap"]},
             {"sized", ["sized-wire"]},
             {"window", ["window-wire"]}
           ]
  end

  test "wire, echo-wire, arm, and window-wire are the configuration steps", %{catalog: catalog} do
    wire = meeting(catalog, "wire")
    assert wire.steps == 2
    assert wire.left == "pong"
    assert wire.right == "peer"
    assert wire.base == "ping"
    assert wire.left_session == "ping"
    assert wire.right_session == "dual ping"
    assert wire.evidence == ""
    assert wire.href == "/?meet=wire"

    assert steps(wire) == [
             {:send, "peer", "pong", "1", nil, false},
             {:send, "pong", "peer", "1", nil, false},
             {:terminal, nil, nil, "done", nil, false}
           ]

    echo = meeting(catalog, "echo-wire")

    assert steps(echo) == [
             {:send, "peer-echo", "echo", "2", nil, false},
             {:send, "echo", "peer-echo", "k", nil, false},
             {:terminal, nil, nil, "done", nil, false}
           ]

    arm = meeting(catalog, "arm")
    assert arm.steps == 1
    assert hd(arm.rows).arity == 2

    assert steps(arm) == [
             {:choice, "taker", "giver", "pick0", "0", false},
             {:terminal, nil, nil, "done", nil, false}
           ]

    window = meeting(catalog, "window-wire")
    assert window.steps == 2
    assert window.evidence == "{d ≤ w}"
    assert window.spec =~ "{d ≤ w}"

    assert steps(window) == [
             {:send, "window-client", "window-server", "8", nil, false},
             {:send, "window-server", "window-client", "w", nil, false},
             {:terminal, nil, nil, "done", nil, false}
           ]

    assert Enum.at(window.rows, 0).evidence == nil
    assert Enum.at(window.rows, 1).evidence == "w ⊢ d ≤ w"

    assert Enum.at(meeting(catalog, "sized-wire").rows, 1).label == "rep n 0"
    assert hd(meeting(catalog, "wrapped").rows).label == "(b0, {x = 0, y = 0})"
    assert List.last(meeting(catalog, "drop").rows).label == "stop"
    assert hd(meeting(catalog, "far-wrap").rows).label == "(b1, {x = 1, y = 2})"
  end

  test "a loop is one row, and a buffered step still names the sender" do
    catalog = catalog("async-meetings.muro")
    sync = meeting(catalog, "stream-sync")
    assert sync.steps == 1
    assert [%{kind: :send, label: "0", loop: true, from: "up", to: "down"}] = sync.rows
    assert sync.evidence =~ "≤"

    echo = meeting(catalog, "echo-wire")
    assert echo.buffer == 1
    assert hd(echo.rows).from == "echo-a"
    assert hd(echo.rows).to == "echo-b"
    assert hd(echo.rows).label == "0"

    calls = catalog("session-calls.muro")
    choice = meeting(calls, "choice-wire")

    assert steps(choice) == [
             {:choice, "taker", "giver", "pick0", "0", false},
             {:send, "taker", "giver", "b1", nil, false},
             {:terminal, nil, nil, "done", nil, false}
           ]

    computed = catalog("computed.muro")
    arm1 = meeting(computed, "arm1")
    assert Enum.at(arm1.rows, 0).label == "b1"
    assert Enum.at(arm1.rows, 1).label == "pick1"
    assert Enum.at(arm1.rows, 1).branch == "1"
    assert Enum.at(arm1.rows, 1).arity == 2
  end

  test "arrows share the two lifelines and a choice names its arity", %{catalog: catalog} do
    for name <- ~w(wire echo-wire arm drop wrapped far-wrap sized-wire window-wire) do
      drawn = MuroVisor.Sequence.diagram(meeting(catalog, name))
      assert drawn.right_x - drawn.left_x == 420
      assert drawn.right_x - drawn.left_x <= 420

      for step <- drawn.steps, step.kind != :terminal do
        assert Enum.sort([step.x1, step.x2]) == Enum.sort([drawn.left_x, drawn.right_x])
        assert step.y1 == step.y2
        assert step.label_x == div(drawn.left_x + drawn.right_x, 2)
      end
    end

    arm = MuroVisor.Sequence.diagram(meeting(catalog, "arm"))
    choice = Enum.find(arm.steps, &(&1.kind == :choice))
    assert choice.choice.text == "chooses branch 0 of 2"
    assert choice.arrow_label == "0"
    assert choice.number == 1

    window = MuroVisor.Sequence.diagram(meeting(catalog, "window-wire"))
    discharged = Enum.find(window.steps, &(&1.evidence == "w ⊢ d ≤ w"))
    assert discharged.label == "w"
    assert discharged.number == 2
  end

  defp catalog(name) do
    path = Path.expand("../../examples/#{name}", __DIR__)
    assert {:ok, book} = Muro.Load.file(path)
    MuroVisor.Meetings.catalog(book, Muro.Explore.graph(book))
  end

  defp meeting(catalog, name), do: Enum.find(catalog.meetings, &(&1.name == name))

  defp steps(meet) do
    Enum.map(meet.rows, &{&1.kind, &1.from, &1.to, &1.label, &1.branch, &1.loop})
  end
end

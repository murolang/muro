defmodule Muro.ExploreTest do
  use ExUnit.Case, async: true

  alias Muro.{Async, Explore, Load, Meet}

  setup do
    path = Path.expand("examples/meet.muro", File.cwd!())
    assert {:ok, book} = Load.file(path)
    {:ok, book: book}
  end

  test "a meeting's configurations are the ones the checker walked", %{book: book} do
    pong = proc(book, "pong")
    peer = proc(book, "peer")
    assert Meet.meets(pong, peer, book) == :ok

    assert {:ok, graph} =
             Meet.graph(pong, peer, book, nil, {steps(book, "pong"), steps(book, "peer")})

    assert graph.states != []

    assert Enum.all?(
             graph.states,
             &match?(%{id: id, loc: %{left: _, right: _}} when is_integer(id), &1)
           )

    assert Enum.all?(graph.transitions, fn t ->
             is_integer(t.from) and is_integer(t.to) and is_list(t.label) and is_map(t.loc)
           end)

    assert hd(graph.transitions).loc.left != nil or hd(graph.transitions).loc.right != nil
  end

  test "the explored book draws definitions, uses, and the session's configurations", %{
    book: book
  } do
    g = Explore.graph(book)
    ping = find_node(g, "ping")
    assert ping.kind == :session
    assert ping.mode == :spec
    assert Enum.any?(ping.children, &(&1.meeting == "wire"))
    assert Enum.any?(ping.transitions, &(&1.meeting == "wire"))

    wire = find_node(g, "wire")
    assert wire.kind == :meet
    assert Enum.any?(g.edges, &(&1.use == :meet and &1.from == wire.id))
    assert Enum.any?(g.edges, &(&1.use == :dual and &1.to == ping.id))

    pong = find_node(g, "pong")
    steps = Enum.filter(g.edges, &(&1.use == :step and &1.proc == "pong" and &1.from == pong.id))
    assert Enum.any?(steps, &(&1.step == 0))
    assert Enum.any?(steps, &(&1.step == 1))
    assert Enum.all?(steps, &is_tuple(&1.loc))
  end

  test "moving one step earlier is a refusal with its source location", %{book: book} do
    assert %{kind: :immovable, index: 0} = Explore.out_of_order(book, "pong", 0)

    refused = Explore.out_of_order(book, "pong", 1)
    assert refused.kind == :refused
    assert is_tuple(refused.loc)
    assert {:put, _, _, _} = refused.proc
    assert refused.proto != nil

    step =
      Explore.graph(book).edges
      |> Enum.find(&(&1.use == :step and &1.proc == "pong" and &1.step == 1))

    assert Explore.out_of_order(book, step).kind == :refused
    assert Explore.out_of_order(book, %{use: :meet, loc: {1, 1}, step: nil}).kind == :not_a_step
  end

  test "a buffered meeting records the same search" do
    path = Path.expand("examples/async-meetings.muro", File.cwd!())
    assert {:ok, book} = Load.file(path)
    left = proc(book, "client")
    right = proc(book, "server")
    assert Meet.meets(left, right, book) == :ok or Async.meets(left, right, book, 1) == :ok

    graph =
      Async.graph(
        left,
        right,
        book,
        1,
        "client",
        "server",
        {steps(book, "client"), steps(book, "server")}
      )

    assert length(graph.states) >= 2
    assert graph.transitions != []
  end

  defp proc(book, name), do: Enum.find(book, &(&1.name == name)).proc
  defp steps(book, name), do: Enum.find(book, &(&1.name == name)).steps
  defp find_node(g, name), do: Enum.find(g.nodes, &(&1.name == name))
end

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
    assert %{kind: :not_a_step} = Explore.out_of_order(book, "missing", 1)
    assert %{kind: :immovable, loc: nil} = Explore.out_of_order(book, "pong", 9)
  end

  test "node ids are the source names spelled by Muro.Emit.Name", %{book: book} do
    g = Explore.graph(book)

    for node <- g.nodes do
      assert node.id == Muro.Emit.Name.encode(node.name)
    end

    assert find_node(g, "peer-echo").id == "peerzdecho"
    assert find_node(g, "kept")
  end

  test "a definition with no uses has no edge, and one used twice has two", %{book: book} do
    g = Explore.graph(book)
    kept = find_node(g, "kept").id
    refute Enum.any?(g.edges, &(&1.from == kept or &1.to == kept))

    there = find_node(g, "there").id

    incoming =
      for edge <- g.edges, edge.to == there, edge.use == :meet do
        edge.from
      end

    assert Enum.sort(incoming) ==
             Enum.sort([find_node(g, "wrapped").id, find_node(g, "far-wrap").id])
  end

  test "data is not a node, and a std import's definitions are" do
    {:ok, result} = Load.file(Path.expand("examples/result.muro", File.cwd!()))
    g = Explore.graph(result)
    reported = reported(result)
    assert Enum.map(g.nodes, & &1.name) == Enum.map(reported, & &1.name)
    refute Enum.any?(g.nodes, &(&1.name == "Result"))

    for node <- g.nodes do
      defn = Enum.find(reported, &(&1.name == node.name))
      assert node.kind == Map.get(defn, :kind, :def)
      assert node.mode == defn.mode
    end

    {:ok, maybe} = Load.file(Path.expand("examples/maybe.muro", File.cwd!()))
    g = Explore.graph(maybe)
    assert Enum.map(g.nodes, & &1.name) == Enum.map(reported(maybe), & &1.name)
    from = find_node(g, "fromMaybe")
    assert from.file == "std:maybe.muro"
    assert from.mode == :run
    refute Enum.any?(g.nodes, &(&1.name in ["Maybe", "Bool"]))
  end

  test "a sent definition is one use per occurrence, and a bound name is not" do
    book =
      load_src("""
      def kept : run Nat := 0

      def idle : run Nat := 0

      session nums := send Nat (send Nat end)

      session back := dual nums

      conform sender : nums := put kept (put kept done)

      conform recv : back := get (kept : Nat) (get (m : Nat) done)

      meet wire : sender with recv
      """)

    g = Explore.graph(book)
    sender = find_node(g, "sender")
    kept = find_node(g, "kept")
    idle = find_node(g, "idle")
    uses = Enum.filter(g.edges, &(&1.from == sender.id and &1.to == kept.id and &1.use == :def))
    assert length(uses) == 2
    assert Enum.all?(uses, &is_tuple(&1.loc))
    refute Enum.any?(g.edges, &(&1.from == idle.id or &1.to == idle.id))
    recv = find_node(g, "recv")
    refute Enum.any?(g.edges, &(&1.from == recv.id and &1.to == kept.id))
  end

  test "swapping two sends that still conform reports still_conforms" do
    book =
      load_src("""
      session nums := send Nat (send Nat end)
      session back := dual nums
      conform a : nums := put 1 (put 2 done)
      conform b : back := get Nat (get Nat done)
      meet wire : a with b
      """)

    assert %{kind: :still_conforms, index: 1, loc: loc} = Explore.out_of_order(book, "a", 1)
    assert is_tuple(loc)
    assert %{kind: :immovable} = Explore.out_of_order(book, "a", 0)
  end

  test "a branching meeting and a loop are the configurations the checker walked" do
    {:ok, meet} = Load.file(Path.expand("examples/meet.muro", File.cwd!()))
    arm = meeting(meet, "arm")
    walked = walked(meet, arm)
    assert Enum.any?(walked.transitions, fn t -> Enum.join(t.label, " ") =~ "pick0" end)

    g = Explore.graph(meet)
    choice = find_node(g, "choice")
    kids = Enum.filter(choice.children, &(&1.meeting == "arm"))
    trans = Enum.filter(choice.transitions, &(&1.meeting == "arm"))
    assert_graph(kids, trans, walked, "choice", "arm")

    {:ok, async} = Load.file(Path.expand("examples/async-meetings.muro", File.cwd!()))
    sync = meeting(async, "stream-sync")
    walked = walked(async, sync)
    assert Enum.any?(walked.transitions, &(&1.from == &1.to))
    g = Explore.graph(async)
    session = find_node(g, session_name(async, sync.left))
    kids = Enum.filter(session.children, &(&1.meeting == "stream-sync"))
    trans = Enum.filter(session.transitions, &(&1.meeting == "stream-sync"))
    assert_graph(kids, trans, walked, session.name, "stream-sync")
    assert Enum.any?(trans, fn t -> t.from == t.to end)
  end

  test "the check hook counts check_sig and an outline does not check" do
    parent = self()

    # One persistent term for the whole VM. Other tests check at the same
    # time, on their own processes. Only this process is watching.
    assert :ok =
             Muro.Check.check_hook(fn ->
               if Process.get(:muro_check_watch), do: send(parent, :checked)
             end)

    on_exit(fn -> Muro.Check.check_hook(nil) end)

    path = Path.expand("examples/half_ok.muro", File.cwd!())
    Process.put(:muro_check_watch, true)
    assert {:ok, book} = Load.file(path)
    assert_receive :checked

    emit = Muro.Prelude.for_emit(book)
    assert {:ok, _} = Muro.Emit.outline(:c, emit, "half_ok")
    assert {:error, msg} = Muro.Emit.outline(:fsm, emit, path)
    assert msg =~ "no session"
    refute_receive :checked, 0
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

  defp reported(book) do
    Enum.filter(book, fn d ->
      is_map(d) and is_binary(Map.get(d, :name)) and Map.get(d, :mode) in [:spec, :evidence, :run]
    end)
  end

  defp meeting(book, name), do: Enum.find(book, &(&1.name == name and &1.kind == :meet))

  defp session_name(book, party) do
    case Enum.find(book, &(&1.name == party)).session do
      name when is_binary(name) -> name
      {:sess, name, _} -> name
    end
  end

  defp walked(book, meet) do
    left = Enum.find(book, &(&1.name == meet.left))
    right = Enum.find(book, &(&1.name == meet.right))
    spans = {Map.get(left, :steps), Map.get(right, :steps)}

    case Map.get(meet, :buffer) do
      n when is_integer(n) ->
        Async.graph(left.proc, right.proc, book, n, meet.left, meet.right, spans)

      _ ->
        {_verdict, graph} = Meet.graph(left.proc, right.proc, book, nil, spans)
        graph
    end
  end

  defp assert_graph(kids, trans, walked, session, meet) do
    prefix = "cfg-" <> Muro.Emit.Name.encode(session) <> "-" <> Muro.Emit.Name.encode(meet)
    assert Enum.map(kids, & &1.id) == Enum.map(walked.states, &"#{prefix}-#{&1.id}")

    assert Enum.map(trans, &{&1.from, &1.to, &1.label}) ==
             Enum.map(walked.transitions, fn t ->
               {"#{prefix}-#{t.from}", "#{prefix}-#{t.to}", t.label}
             end)
  end

  defp load_src(src) do
    path = Path.join(System.tmp_dir!(), "muro-explore-#{System.unique_integer([:positive])}.muro")
    File.write!(path, src)
    on_exit(fn -> File.rm(path) end)
    assert {:ok, book} = Load.file(path)
    book
  end
end

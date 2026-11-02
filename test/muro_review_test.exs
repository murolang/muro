defmodule Muro.ReviewTest do
  use ExUnit.Case, async: true

  alias Muro.{Explore, Load, Session}

  test "a type reference keeps the parser's span" do
    book =
      load("""
      def carrier : spec Type := Nat
      def f : spec Π (_ : carrier) → Nat := λ (_ : carrier) → 0
      """)

    g = Explore.graph(book)
    id = Enum.find(g.nodes, &(&1.name == "f"))
    d = Enum.find(g.nodes, &(&1.name == "carrier"))
    uses = Enum.filter(g.edges, &(&1.from == id.id and &1.to == d.id and &1.use == :def))
    assert length(uses) >= 2
    assert Enum.all?(uses, &match?({_line, _col}, &1.loc))
    cols = Enum.map(uses, fn %{loc: {_line, col}} -> col end)
    assert length(Enum.uniq(cols)) >= 2
  end

  test "a branching spine tail is one edge" do
    {:ok, book} = Load.file(Path.expand("examples/meet.muro", File.cwd!()))
    giver = Enum.find(book, &(&1.name == "giver"))
    [cover | _] = Session.spine(giver.proc, giver.steps)
    loc = Session.step_at(elem(cover, 2))

    edges =
      Explore.graph(book).edges
      |> Enum.filter(&(&1.proc == "giver" and &1.use == :step and &1.loc == loc))

    assert length(edges) == 1
    assert is_integer(hd(edges).step)

    nested = Enum.filter(Explore.graph(book).edges, &(&1.proc == "giver" and &1.use == :step))
    assert Enum.any?(nested, &match?({:down, 0, [1, 0]}, &1.step))
  end

  test "a nested action is a real out-of-order query" do
    {:ok, book} = Load.file(Path.expand("examples/async-meetings.muro", File.cwd!()))
    edges = Explore.graph(book).edges

    put =
      Enum.find(edges, fn e ->
        e.proc == "server" and e.use == :step and match?({:down, _, [0, 0]}, e.step)
      end)

    get =
      Enum.find(edges, fn e ->
        e.proc == "server" and e.use == :step and match?({:down, _, [0, 1]}, e.step)
      end)

    assert put && get
    assert Explore.out_of_order(book, put).kind == :immovable
    assert Explore.out_of_order(book, get).kind != :not_a_step
  end

  test "a conforming loop keeps its rec when two sends swap" do
    book =
      load("""
      session nums := rec X. send Nat (send Nat X)
      conform loop : nums := rec X. put 0 (put 1 X)
      """)

    moved = Explore.out_of_order(book, "loop", 1)
    assert moved.kind == :still_conforms
    refute moved.reason == "free session variable X"
  end

  test "a seen session is the checker's protocol" do
    {:ok, book} = Load.file(Path.expand("examples/talk.muro", File.cwd!()))
    moved = Explore.out_of_order(book, "pong", 1)
    assert moved.kind in [:refused, :still_conforms, :immovable]
    refute to_string(moved.reason) =~ "ill-formed"
  end

  test "a reading uses its endpoint's session" do
    {:ok, book} = Load.file(Path.expand("examples/located.muro", File.cwd!()))
    g = Explore.graph(book)
    pong = Enum.find(g.nodes, &(&1.name == "pong"))
    ping = Enum.find(g.nodes, &(&1.name == "ping"))

    assert Enum.any?(g.edges, fn e ->
             e.use == :step and e.from == pong.id and e.to == ping.id
           end)
  end

  test "a checked meeting keeps the graph the checker recorded" do
    {:ok, book} = Load.file(Path.expand("examples/meet.muro", File.cwd!()))
    wire = Enum.find(book, &(&1.kind == :meet and &1.name == "wire"))
    assert %{states: states} = wire.graph
    assert states != []

    g = Explore.graph(book)
    ping = Enum.find(g.nodes, &(&1.name == "ping"))
    assert Enum.any?(ping.children, &(&1.meeting == "wire"))

    stripped =
      Enum.map(book, fn
        %{kind: :meet} = meet -> %{meet | left: "missing-left", right: "missing-right"}
        other -> other
      end)

    again = Explore.graph(stripped)
    ping = Enum.find(again.nodes, &(&1.name == "ping"))
    assert Enum.any?(ping.children, &(&1.meeting == "wire"))
  end

  test "the selected arm is the source path, not an equal body" do
    book =
      load("""
      session bits := send Bit end
      session take := dual bits
      conform sender : bits := put b1 done
      conform recv : take := get (b : Bit) (match b done done)
      meet wire : sender with recv
      """)

    wire = Enum.find(book, &(&1.kind == :meet and &1.name == "wire"))
    [jump] = Enum.filter(wire.graph.transitions, &(Enum.join(&1.label, " ") =~ "arm"))
    landed = Enum.find(wire.graph.states, &(&1.id == jump.to))
    recv = Enum.find(book, &(&1.name == "recv"))
    assert landed.loc.right == second_done(recv)

    book =
      load("""
      data D : Type where
        A : D
        B : Nat → D
      session box := recv (d : D) (case d | A => end | B => send Nat end)
      session take := dual box
      conform recv : box :=
        get (d : D) (match d
          | A => done
          | B n => put n done)
      conform sender : take := put (B 1) (get (k : Nat) done)
      meet wire : sender with recv
      """)

    wire = Enum.find(book, &(&1.kind == :meet and &1.name == "wire"))
    [jump] = Enum.filter(wire.graph.transitions, &(Enum.join(&1.label, " ") =~ "arm"))
    landed = Enum.find(wire.graph.states, &(&1.id == jump.to))
    recv = Enum.find(book, &(&1.name == "recv"))
    assert landed.loc.right == put_loc(recv)
    refute landed.loc.right == done_after_put(recv)
  end

  test "closed data layouts name each constructor's tag and fields" do
    one =
      outline_layouts("""
      data D : Type where
        A : D
        B : Nat → D
      def id : run Π (x : D) → D := λ (x : D) → x
      """)

    two =
      outline_layouts("""
      data D : Type where
        A : Nat → Nat → D
      def id : run Π (x : D) → D := λ (x : D) → x
      """)

    sig = Enum.find(one, &(not Map.has_key?(&1, :constructors)))
    assert sig.layout == {:data, "D"}

    [left] = Enum.filter(one, &Map.has_key?(&1, :constructors))
    [right] = Enum.filter(two, &Map.has_key?(&1, :constructors))
    assert left.constructors != right.constructors
    assert Enum.any?(left.constructors, &(&1.name == "B" and &1.tag == 1 and &1.fields == [:nat]))
    assert Enum.any?(right.constructors, &(&1.name == "A" and &1.fields == [:nat, :nat]))
  end

  defp load(src) do
    path = Path.join(System.tmp_dir!(), "muro-review-#{System.unique_integer([:positive])}.muro")
    File.write!(path, src)
    on_exit(fn -> File.rm(path) end)
    assert {:ok, book} = Load.file(path)
    book
  end

  defp outline_layouts(src) do
    book = load(src)
    emit = Muro.Prelude.for_emit(book)

    layouts =
      for backend <- [:c, :rust, :zig] do
        assert {:ok, outline} = Muro.Emit.outline(backend, emit, "d")
        outline.layouts
      end

    [first | rest] = layouts
    assert Enum.all?(rest, &(&1 == first))
    first
  end

  defp second_done(%{steps: %{down: [match]}}) do
    %{down: [_b0, b1]} = match
    Session.step_at(b1)
  end

  defp put_loc(%{steps: %{down: [match]}}) do
    %{down: [_a, put]} = match
    Session.step_at(put)
  end

  defp done_after_put(%{steps: %{down: [match]}}) do
    %{down: [_a, put]} = match
    %{down: [done]} = put
    Session.step_at(done)
  end
end

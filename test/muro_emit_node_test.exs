defmodule Muro.EmitNodeTest do
  use ExUnit.Case, async: false

  alias Muro.Emit

  setup do
    on_exit(fn ->
      stop(:local)
      purge(PlaceNode)
      purge(StayNode)
      purge(TwiceNode)
      purge(LocatedNode)
      purge(ReadStayNode)
    end)

    :ok
  end

  test "a cross is one call and a stay is none" do
    dir = tmp!()
    path = Path.join(dir, "place.muro")
    File.cp!("examples/place.muro", path)

    assert {:ok, [file]} = Muro.emit_node(path, :a)
    assert Path.basename(file) == "place_node.ex"

    src = File.read!(file)
    assert String.contains?(src, "defmodule PlaceNode do")
    assert String.contains?(src, "@node :a")
    assert String.contains?(src, "def cross_local_at_away(timeout \\\\ 5000)")
    assert String.contains?(src, "dest = {:local, @node}")
    assert String.contains?(src, ":erlang.monitor(:process, dest)")
    assert String.contains?(src, "GenServer.call(dest, {:muro_read, \"local\"}, timeout)")
    assert String.contains?(src, "The proof stops at the move.")
    refute String.contains?(src, "def cross_local_at_home")
    refute String.contains?(src, "def cross_poly")
    refute String.contains?(src, "def kept")
    refute String.contains?(src, ":b0")
    refute String.contains?(src, ":b1")
    assert call_count(src) == 1

    assert {:ok, elixir} = Muro.emit_file("examples/place.muro", PlaceRun)
    assert elixir =~ ~r/\bdef kept\b/
    refute elixir =~ "GenServer"
  end

  test "a book of stays emits no call" do
    dir = tmp!()
    path = Path.join(dir, "stay.muro")

    File.write!(path, """
    place home := ambient
    scheme local := fixed home
    move stay local : home
    def kept : run Nat := 0
    """)

    assert {:ok, [file]} = Muro.emit_node(path, :a)
    src = File.read!(file)
    assert String.contains?(src, "defmodule StayNode do")
    assert String.contains?(src, "def node, do: @node")
    assert call_count(src) == 0
    refute src =~ "def kept"
  end

  test "two crosses are two calls" do
    dir = tmp!()
    path = Path.join(dir, "twice.muro")

    File.write!(path, """
    place home := ambient
    place away := node a
    scheme local := fixed home
    move cross local : away
    move cross local : away
    """)

    assert {:ok, src} = Emit.Node.render(checked!(path), "twice", :a)
    assert String.contains?(src, "def cross_local_at_away(")
    assert String.contains?(src, "def cross_local_at_away2(")
    assert call_count(src) == 2
  end

  test "a wrong mark is not emitted" do
    dir = tmp!()
    path = Path.join(dir, "bad.muro")

    File.write!(path, """
    place home := ambient
    place away := node a
    scheme local := fixed home
    move stay local : away
    """)

    assert {:error, msg} = Muro.emit_node(path, :a)
    assert msg =~ "expected cross"
    refute File.exists?(Path.join(dir, "bad_node.ex"))
  end

  test "the call reaches the registered name on this node" do
    node = node()
    dir = tmp!()
    path = Path.join(dir, "place.muro")
    File.cp!("examples/place.muro", path)

    assert {:ok, [file]} = Muro.emit_node(path, node)
    [{PlaceNode, _}] = Code.compile_string(File.read!(file))
    assert apply(PlaceNode, :node, []) == node

    assert apply(PlaceNode, :cross_local_at_away, [200]) == {:error, :noproc}

    {:ok, pid} = GenServer.start(ReadServer, nil, name: :local)
    assert apply(PlaceNode, :cross_local_at_away, [200]) == :ok

    ref = Process.monitor(pid)
    Process.exit(pid, :kill)
    assert_receive {:DOWN, ^ref, :process, ^pid, :killed}
    assert apply(PlaceNode, :cross_local_at_away, [200]) == {:error, :noproc}
  end

  test "a cross reading is one call and a stay reading is none" do
    dir = tmp!()
    path = Path.join(dir, "located.muro")
    File.cp!("examples/located.muro", path)

    assert {:ok, [file]} = Muro.emit_node(path, :a)
    assert Path.basename(file) == "located_node.ex"

    src = File.read!(file)
    assert String.contains?(src, "defmodule LocatedNode do")
    assert String.contains?(src, "def cross_local_at_away(timeout \\\\ 5000)")
    assert String.contains?(src, "def cross_local_at_away2(")
    assert String.contains?(src, "def cross_local_at_away3(")
    assert String.contains?(src, "dest = {:local, @node}")
    assert String.contains?(src, "GenServer.call(dest, {:muro_read, \"local\"}, timeout)")
    assert String.contains?(src, "The bits stay on the session.")
    refute String.contains?(src, "def cross_local_at_home")
    refute String.contains?(src, "def cross_poly")
    refute String.contains?(src, "def kept")
    refute String.contains?(src, "def pong")
    refute String.contains?(src, ":b0")
    refute String.contains?(src, ":b1")
    assert call_count(src) == 3

    assert {:ok, elixir} = Muro.emit_file("examples/located.muro", LocatedRun)
    assert elixir =~ ~r/\bdef kept\b/
    refute elixir =~ "GenServer"
  end

  test "a book of stay readings emits no call" do
    dir = tmp!()
    path = Path.join(dir, "read_stay.muro")

    File.write!(path, """
    place home := ambient
    place away := node a
    scheme local := fixed home
    scheme poly := any
    session ping := recv end (send end end)
    endpoint ping-home := ping at local
    endpoint ping-poly := ping at poly
    read stay pong : ping-home at home := get b1 (put b0 done)
    read stay pong-poly : ping-poly at away := get b1 (put b0 done)
    def kept : run Nat := 0
    """)

    assert {:ok, [file]} = Muro.emit_node(path, :a)
    src = File.read!(file)
    assert String.contains?(src, "defmodule ReadStayNode do")
    assert String.contains?(src, "def node, do: @node")
    assert call_count(src) == 0
    refute src =~ "def kept"
    refute src =~ ":b0"
  end

  test "a move and a reading of the same scheme are two calls" do
    dir = tmp!()
    path = Path.join(dir, "both.muro")

    File.write!(path, """
    place home := ambient
    place away := node a
    scheme local := fixed home
    session ping := recv end (send end end)
    endpoint ping-home := ping at local
    move cross local : away
    read cross pong : ping-home at away := get b1 (put b0 done)
    """)

    assert {:ok, src} = Emit.Node.render(checked!(path), "both", :a)
    assert String.contains?(src, "def cross_local_at_away(")
    assert String.contains?(src, "def cross_local_at_away2(")
    assert call_count(src) == 2
  end

  test "a reading may name an endpoint declared later" do
    dir = tmp!()
    path = Path.join(dir, "later.muro")

    File.write!(path, """
    read cross pong : ping-home at away := get b1 (put b0 done)
    endpoint ping-home := ping at local
    session ping := recv end (send end end)
    scheme local := fixed home
    place home := ambient
    place away := node a
    """)

    assert {:ok, src} = Emit.Node.render(checked!(path), "later", :a)
    assert String.contains?(src, "def cross_local_at_away(")
    assert call_count(src) == 1
  end

  test "a refused reading is not emitted" do
    dir = tmp!()
    path = Path.join(dir, "bad_read.muro")

    File.write!(path, """
    place home := ambient
    place away := node a
    scheme local := fixed home
    session ping := recv end (send end end)
    endpoint ping-home := ping at local
    read stay pong : ping-home at away := get b1 (put b0 done)
    """)

    assert {:error, msg} = Muro.emit_node(path, :a)
    assert msg =~ "expected cross"
    refute File.exists?(Path.join(dir, "bad_read_node.ex"))
  end

  test "the reading's call reaches the registered scheme" do
    node = node()
    dir = tmp!()
    path = Path.join(dir, "located.muro")
    File.cp!("examples/located.muro", path)

    assert {:ok, [file]} = Muro.emit_node(path, node)
    [{LocatedNode, _}] = Code.compile_string(File.read!(file))
    assert apply(LocatedNode, :node, []) == node

    assert apply(LocatedNode, :cross_local_at_away, [200]) == {:error, :noproc}

    {:ok, pid} = GenServer.start(ReadServer, nil, name: :local)
    assert apply(LocatedNode, :cross_local_at_away, [200]) == :ok
    assert apply(LocatedNode, :cross_local_at_away2, [200]) == :ok
    assert apply(LocatedNode, :cross_local_at_away3, [200]) == :ok

    ref = Process.monitor(pid)
    Process.exit(pid, :kill)
    assert_receive {:DOWN, ^ref, :process, ^pid, :killed}
    assert apply(LocatedNode, :cross_local_at_away, [200]) == {:error, :noproc}
  end

  test "mix muro.emit --node prints the path" do
    dir = tmp!()
    path = Path.join(dir, "place.muro")
    File.cp!("examples/place.muro", path)

    assert ExUnit.CaptureIO.capture_io(fn ->
             Mix.Task.rerun("muro.emit", [path, "--node", "a"])
           end) =~ "place_node.ex"
  end

  defp call_count(src) do
    src |> String.split("GenServer.call") |> length() |> Kernel.-(1)
  end

  defp checked!(path) do
    {:ok, book} = Muro.Load.file(path)
    Muro.Prelude.for_emit(book)
  end

  defp stop(name) do
    case Process.whereis(name) do
      nil -> :ok
      pid -> GenServer.stop(pid, :normal, 200)
    end
  end

  defp purge(mod) do
    :code.purge(mod)
    :code.delete(mod)
  end

  defp tmp! do
    dir = Path.join(System.tmp_dir!(), "muro_node_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end

defmodule ReadServer do
  use GenServer

  @impl true
  def init(_), do: {:ok, nil}

  @impl true
  def handle_call({:muro_read, "local"}, _from, state), do: {:reply, :ok, state}
end

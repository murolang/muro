defmodule Muro.EmitOtpTest do
  use ExUnit.Case, async: false

  alias Muro.{Emit, Parser, Session}

  setup do
    on_exit(fn ->
      for name <- [:Pong, :LeftOpen, :Untouched, :Chosen, :Both, ""] do
        mod = if name == "", do: Module.concat(["PingOtp"]), else: Module.concat("PingOtp", name)
        :code.purge(mod)
        :code.delete(mod)
      end
    end)

    :ok
  end

  test "skel follows the Agda actions" do
    assert {:ok, book} = Parser.parse(File.read!("examples/ping.muro"))
    proc = Map.new(book, &{&1.name, Map.get(&1, :proc)})

    assert Session.skel(proc["pong"]) == {:hear, :b1, {:say, :b0, :finish}}
    assert Session.skel(proc["left-open"]) == {:say, :b0, :leave}
    assert Session.skel(proc["untouched"]) == :leave
    assert Session.skel(proc["chosen"]) == {:choose, :b0, :finish}
    assert Session.skel(proc["both"]) == {:offer, :finish, {:say, :b0, :finish}}
  end

  test "otp emit writes the servers and leaves run emit alone" do
    dir = tmp!()
    path = Path.join(dir, "ping.muro")
    File.cp!("examples/ping.muro", path)

    assert {:ok, [file]} = Muro.emit_otp(path)
    assert Path.basename(file) == "ping_otp.ex"

    src = File.read!(file)
    assert src =~ "defmodule PingOtp do"
    assert src =~ "defmodule Pong do"
    assert src =~ "{:hear, :b1, {:say, :b0, :finish}}"
    assert src =~ "The proof stops at the conformance derivation."
    refute src =~ "def z"

    assert {:ok, elixir} = Muro.emit_file("examples/ping.muro", Ping)
    refute elixir =~ "Pong"
    refute elixir =~ "GenServer"
  end

  test "a process that does not conform is not emitted" do
    dir = tmp!()
    path = Path.join(dir, "bad.muro")

    File.write!(path, """
    session ping := end
    conform bad : ping := put b0 done
    """)

    assert {:error, msg} = Muro.emit_otp(path)
    assert msg =~ "does not conform"
    refute File.exists?(Path.join(dir, "bad_otp.ex"))
  end

  test "a run beside a session is not in the OTP file" do
    dir = tmp!()
    path = Path.join(dir, "mixed.muro")

    File.write!(path, """
    session ping := end
    conform done-it : ping := done
    def z : run Nat := 0
    """)

    assert {:ok, [file]} = Muro.emit_otp(path)
    src = File.read!(file)
    assert src =~ "defmodule DoneIt do"
    refute src =~ "def z"
  end

  test "the servers speak the session" do
    assert {:ok, src} = Emit.Otp.render(checked!("examples/ping.muro"), "ping")
    Code.compile_string(src)

    pong_roundtrip()
    pong_unexpected()
    pong_peer_dies()
    left_open()
    untouched()
    chosen()
    both_arms()
  end

  defp pong_roundtrip do
    {:ok, pid, ref} = start(:Pong)
    send(pid, {:muro, self(), :b1})
    assert_receive {:muro, ^pid, :b0}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
  end

  defp pong_unexpected do
    {:ok, pid, ref} = start(:Pong)
    send(pid, {:muro, self(), :b0})
    assert_receive {:DOWN, ^ref, :process, ^pid, {:shutdown, {:unexpected, :b0}}}
  end

  defp pong_peer_dies do
    peer =
      spawn(fn ->
        receive do
          :go -> :ok
        end
      end)

    {:ok, pid, ref} = start(:Pong, peer)
    Process.exit(peer, :kill)
    assert_receive {:DOWN, ^ref, :process, ^pid, {:shutdown, :abandon}}
  end

  defp left_open do
    {:ok, pid, ref} = start(:LeftOpen)
    assert_receive {:muro, ^pid, :b0}
    assert_receive {:DOWN, ^ref, :process, ^pid, {:shutdown, :abandon}}
  end

  defp untouched do
    {:ok, pid, ref} = start(:Untouched)
    assert_receive {:DOWN, ^ref, :process, ^pid, {:shutdown, :abandon}}
    refute_received {:muro, ^pid, _}
  end

  defp chosen do
    {:ok, pid, ref} = start(:Chosen)
    assert_receive {:muro_pick, ^pid, :b0}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
  end

  defp both_arms do
    {:ok, left, left_ref} = start(:Both)
    send(left, {:muro_pick, self(), :b0})
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    refute_received {:muro, ^left, _}

    {:ok, right, right_ref} = start(:Both)
    send(right, {:muro_pick, self(), :b1})
    assert_receive {:muro, ^right, :b0}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}
  end

  defp start(name, peer \\ self()) do
    apply(Module.concat("PingOtp", name), :start, [peer])
  end

  defp tmp! do
    dir = Path.join(System.tmp_dir!(), "muro_otp_#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end

  defp checked!(path) do
    {:ok, book} = Muro.Load.file(path)
    Muro.Prelude.for_emit(book)
  end
end

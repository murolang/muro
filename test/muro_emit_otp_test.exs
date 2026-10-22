defmodule Muro.EmitOtpTest do
  use ExUnit.Case, async: false

  alias Muro.{Emit, Parser, Session}

  setup do
    on_exit(fn ->
      for {parent, names} <- [
            {"PingOtp", [:Pong, :LeftOpen, :Untouched, :Chosen, :Both, :PongDone, :OpenStop, ""]},
            {"LocatedOtp",
             [:Pong, :PongAway, :PongPoly, :PongPolyAway, :PongDone, :LeftOpen, ""]},
            {"BothOtp", [:Pong, :PongHome, ""]},
            {"MeetOtp", [:Pong, :Peer, :Taker, :Giver, :Left, :Right, :Here, :There, :Far, ""]}
          ] do
        for name <- names do
          mod = if name == "", do: Module.concat([parent]), else: Module.concat(parent, name)
          :code.purge(mod)
          :code.delete(mod)
        end
      end
    end)

    :ok
  end

  test "skel follows the Agda actions" do
    assert {:ok, book} = Parser.parse(File.read!("examples/ping.muro"))
    proc = Map.new(book, &{&1.name, Map.get(&1, :proc)})

    assert Session.skel(proc["pong"]) == {:hear, :nat, {:say, 1, :finish}}
    assert Session.skel(proc["left-open"]) == {:say, 0, :leave}
    assert Session.skel(proc["untouched"]) == :leave
    assert Session.skel(proc["chosen"]) == {:choose, :b0, :finish}
    assert Session.skel(proc["both"]) == {:offer, :finish, {:say, 0, :finish}}
    assert Session.skel(proc["pong-done"]) == {:hear, :nat, {:say, 1, :finish}}
    assert Session.skel(proc["open-stop"]) == :leave
    assert Session.finishes(proc["pong-done"]) == :yes
    assert Session.finishes(proc["open-stop"]) == :no
    assert Session.finishes(proc["left-open"]) == :no
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
    assert src =~ "{:hear, :nat, {:say, 1, :finish}}"
    assert src =~ "The proof stops at the conformance derivation."
    refute src =~ "def z"
    refute src =~ "muro_peer"

    assert {:ok, elixir} = Muro.emit_file("examples/ping.muro", Ping)
    refute elixir =~ "Pong"
    refute elixir =~ "GenServer"
  end

  test "a process that does not conform is not emitted" do
    dir = tmp!()
    path = Path.join(dir, "bad.muro")

    File.write!(path, """
    session ping := end
    conform bad : ping := put 0 done
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

  test "a reading is the same server" do
    dir = tmp!()
    path = Path.join(dir, "located.muro")
    File.cp!("examples/located.muro", path)

    assert {:ok, [file]} = Muro.emit_otp(path)
    assert Path.basename(file) == "located_otp.ex"

    src = File.read!(file)
    assert src =~ "defmodule LocatedOtp do"
    assert src =~ "defmodule Pong do"
    assert src =~ "defmodule PongAway do"
    assert src =~ "defmodule PongPoly do"
    assert src =~ "defmodule PongPolyAway do"
    assert src =~ "defmodule PongDone do"
    assert src =~ "defmodule LeftOpen do"
    assert src =~ "{:hear, :nat, {:say, 1, :finish}}"
    assert src =~ "{:say, 0, :leave}"
    assert src =~ "The server talks to one peer."
    refute src =~ "def kept"
    refute src =~ "GenServer.call"
    refute src =~ "@node"

    assert {:ok, elixir} = Muro.emit_file("examples/located.muro", LocatedRun)
    assert elixir =~ ~r/\bdef kept\b/
    refute elixir =~ "GenServer"
  end

  test "a meeting starts the two processes as peers" do
    assert {:ok, src} = Emit.Otp.render(checked!("examples/meet.muro"), "meet")
    assert src =~ "A meeting starts the two processes as each other's peer."
    assert src =~ "def wire do"
    assert src =~ "def arm do"
    assert src =~ "def drop do"
    assert src =~ "defmodule Pong do"
    refute src =~ "def kept"
    refute src =~ "{:muro_read"

    Code.compile_string(src)

    {:ok, left, right, left_ref, right_ref} = meet(:wire)
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}

    {:ok, here, there, here_ref, there_ref} = meet(:wrapped)
    assert_receive {:DOWN, ^here_ref, :process, ^here, :normal}
    assert_receive {:DOWN, ^there_ref, :process, ^there, :normal}

    {:ok, taker, giver, taker_ref, giver_ref} = meet(:arm)
    assert_receive {:DOWN, ^taker_ref, :process, ^taker, :normal}
    assert_receive {:DOWN, ^giver_ref, :process, ^giver, :normal}

    {:ok, opened, closed, opened_ref, closed_ref} = meet(:drop)
    assert_receive {:DOWN, ^opened_ref, :process, ^opened, {:shutdown, :abandon}}
    assert_receive {:DOWN, ^closed_ref, :process, ^closed, {:shutdown, :abandon}}

    {:ok, pid, ref} = meet_one(:Pong)
    send(pid, {:muro, self(), 0})
    assert_receive {:muro, ^pid, 1}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
  end

  test "a meeting of a reading uses that process" do
    dir = tmp!()
    path = Path.join(dir, "read_meet.muro")

    File.write!(path, """
    session ping := recv Nat (send Nat end)
    session back := dual ping
    place home := ambient
    scheme local := fixed home
    endpoint there := back at local
    read stay peer : there at home := put 1 (get Nat done)
    conform pong : ping := get Nat (put 1 done)
    meet wire : pong with peer
    meet a-b : peer with pong
    meet a_b : pong with peer
    meet end : pong with peer
    """)

    assert {:ok, src} = Emit.Otp.render(checked!(path), "read-meet")
    assert src =~ "def wire do"
    assert src =~ "def a_b do"
    assert src =~ "def a_b2 do"
    assert src =~ "def muro_end do"
    assert src =~ "{:hear, :nat, {:say, 1, :finish}}"
    assert src =~ "{:say, 1, {:hear, :nat, :finish}}"
  end

  test "a conform and a reading are two servers" do
    dir = tmp!()
    path = Path.join(dir, "both.muro")

    File.write!(path, """
    session ping := recv Nat (send Nat end)
    conform pong : ping := get Nat (put 1 done)
    place home := ambient
    scheme local := fixed home
    endpoint ping-home := ping at local
    read stay pong-home : ping-home at home := get Nat (put 1 done)
    """)

    assert {:ok, src} = Emit.Otp.render(checked!(path), "both")
    assert src =~ "defmodule Pong do"
    assert src =~ "defmodule PongHome do"
    assert length(String.split(src, "{:hear, :nat, {:say, 1, :finish}}")) == 3
  end

  test "a refused reading is not emitted" do
    dir = tmp!()
    path = Path.join(dir, "bad_read.muro")

    File.write!(path, """
    session ping := recv Nat (send Nat end)
    place home := ambient
    place away := node a
    scheme local := fixed home
    endpoint ping-home := ping at local
    read cross early : ping-home at away := get Bit (put b0 done)
    """)

    assert {:error, msg} = Muro.emit_otp(path)
    assert msg =~ "does not conform"
    refute File.exists?(Path.join(dir, "bad_read_otp.ex"))
  end

  test "the reading's server speaks the session" do
    assert {:ok, src} = Emit.Otp.render(checked!("examples/located.muro"), "located")
    Code.compile_string(src)

    {:ok, pid, ref} = located(:Pong)
    send(pid, {:muro, self(), 0})
    assert_receive {:muro, ^pid, 1}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, away, away_ref} = located(:PongAway)
    send(away, {:muro, self(), 0})
    assert_receive {:muro, ^away, 1}
    assert_receive {:DOWN, ^away_ref, :process, ^away, :normal}

    {:ok, open, open_ref} = located(:LeftOpen)
    assert_receive {:muro, ^open, 0}
    assert_receive {:DOWN, ^open_ref, :process, ^open, {:shutdown, :abandon}}
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
    pong_done()
    open_stop()
  end

  defp pong_roundtrip do
    {:ok, pid, ref} = start(:Pong)
    send(pid, {:muro, self(), 0})
    assert_receive {:muro, ^pid, 1}
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
    assert_receive {:muro, ^pid, 0}
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

  defp pong_done do
    {:ok, pid, ref} = start(:PongDone)
    send(pid, {:muro, self(), 0})
    assert_receive {:muro, ^pid, 1}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
  end

  defp open_stop do
    {:ok, pid, ref} = start(:OpenStop)
    assert_receive {:DOWN, ^ref, :process, ^pid, {:shutdown, :abandon}}
    refute_received {:muro, ^pid, _}
  end

  defp both_arms do
    {:ok, left, left_ref} = start(:Both)
    send(left, {:muro_pick, self(), :b0})
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    refute_received {:muro, ^left, _}

    {:ok, right, right_ref} = start(:Both)
    send(right, {:muro_pick, self(), :b1})
    assert_receive {:muro, ^right, 0}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}
  end

  defp start(name, peer \\ self()) do
    apply(Module.concat("PingOtp", name), :start, [peer])
  end

  defp meet(fun) do
    apply(Module.concat(["MeetOtp"]), fun, [])
  end

  defp meet_one(name) do
    apply(Module.concat("MeetOtp", name), :start, [self()])
  end

  defp located(name, peer \\ self()) do
    apply(Module.concat("LocatedOtp", name), :start, [peer])
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

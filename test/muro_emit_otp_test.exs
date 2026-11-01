defmodule Muro.EmitOtpTest do
  use ExUnit.Case, async: false

  alias Muro.{Emit, Parser, Session}

  setup do
    on_exit(fn ->
      for {parent, names} <- [
            {"PingOtp", ~w(pong left-open untouched chosen both pong-done open-stop) ++ [""]},
            {"LocatedOtp",
             ~w(pong pong-away pong-poly pong-poly-away pong-done left-open) ++ [""]},
            {"BothOtp", ~w(pong pong-home) ++ [""]},
            {"MeetOtp",
             ~w(pong peer taker giver left right here there far sized-server sized-client echo peer-echo window-server window-client) ++
               [""]},
            {"IndexedOtp", ~w(server client client-one echo ask) ++ [""]},
            {"RecursiveOtp", ~w(forever sender server client) ++ [""]},
            {"DataOtp", ~w(up down some take echoer ask shadow) ++ [""]},
            {"FieldBindingsOtp", ~w(reply asker pass passer rest rest-peer) ++ [""]},
            {"FieldChoiceOtp",
             ~w(gate-server put-true put-false put-none hdr-server hdr-bytes hdr-trailers wrap-server wrap-bytes loop-server loop-client called-server called-client sized-server sized-client counted-server counted-client once-server) ++
               [""]}
          ] do
        for name <- names do
          mod =
            if name == "" do
              Module.concat([parent])
            else
              Module.concat(parent, Emit.elixir_alias(name))
            end

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

    assert Session.skel(proc["pong"]) == {:hear, :nat, :_, {:say, 1, :finish}}
    assert Session.skel(proc["left-open"]) == {:say, 0, :leave}
    assert Session.skel(proc["untouched"]) == :leave
    assert Session.skel(proc["chosen"]) == {:choose, :b0, :finish}
    assert Session.skel(proc["both"]) == {:offer, :finish, {:say, 0, :finish}}
    assert Session.skel(proc["pong-done"]) == {:hear, :nat, :_, {:say, 1, :finish}}
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
    assert src =~ "{:hear, :nat, :_, {:say, 1, :finish}}"
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

  test "a run beside a session is named, and its body is not a function" do
    dir = tmp!()
    path = Path.join(dir, "mixed.muro")

    File.write!(path, """
    session ping := end
    conform done-it : ping := done
    def z : run Nat := 0
    """)

    assert {:ok, [file]} = Muro.emit_otp(path)
    src = File.read!(file)
    assert src =~ "defmodule #{Emit.elixir_alias("done-it")} do"
    assert src =~ ~s|defp muro_host("z"), do: :z|
    refute src =~ "def z do"
    refute src =~ "def z("
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
    assert src =~ "defmodule #{Emit.elixir_alias("pong-away")} do"
    assert src =~ "defmodule #{Emit.elixir_alias("pong-poly")} do"
    assert src =~ "defmodule #{Emit.elixir_alias("pong-poly-away")} do"
    assert src =~ "defmodule #{Emit.elixir_alias("pong-done")} do"
    assert src =~ "defmodule #{Emit.elixir_alias("left-open")} do"
    assert src =~ "{:hear, :nat, :_, {:say, 1, :finish}}"
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

    {:ok, server, client, server_ref, client_ref} = meet(host_fun("sized-wire"))
    assert_receive {:DOWN, ^server_ref, :process, ^server, :normal}
    assert_receive {:DOWN, ^client_ref, :process, ^client, :normal}

    {:ok, server, client, server_ref, client_ref} = meet(host_fun("window-wire"))
    assert_receive {:DOWN, ^server_ref, :process, ^server, :normal}
    assert_receive {:DOWN, ^client_ref, :process, ^client, :normal}
  end

  test "an evidence payload carries the nat alone" do
    assert {:ok, src} = Emit.Otp.render(checked!("examples/meet.muro"), "meet")
    assert src =~ "def #{Emit.elixir_base("window-wire")} do"
    assert src =~ "{:hear, :nat, :w, {:say, {:var, :w}, :finish}}"
    assert src =~ "{:say, 8, {:hear, :nat, :d, :finish}}"
    refute src =~ "esend"
    refute src =~ "erecv"
    refute src =~ "≤"

    Code.compile_string(src)

    # The window arrives as a nat, and the data goes back as that nat.
    {:ok, pid, ref} = meet_one(host_mod("window-server"))
    send(pid, {:muro, self(), 8})
    assert_receive {:muro, ^pid, 8}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    # The client sends the window and receives the data as one nat.
    {:ok, pid, ref} = meet_one(host_mod("window-client"))
    assert_receive {:muro, ^pid, 8}
    send(pid, {:muro, self(), 5})
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
  end

  test "a bit index carries the bit alone" do
    assert {:ok, src} = Emit.Otp.render(checked!("examples/indexed.muro"), "indexed")
    assert src =~ "def wire do"
    assert src =~ "def #{Emit.elixir_base("wire-one")} do"
    assert src =~ "def #{Emit.elixir_base("echo-wire")} do"
    assert src =~ "{:index, :b, {:say, 1, :finish}, {:hear, :nat, :n, :finish}}"
    assert src =~ "{:say, :b0, {:hear, :nat, :m, :finish}}"
    assert src =~ "{:say, :b1, {:say, 0, :finish}}"
    assert src =~ "{:index, :b, {:say, {:var, :b}, :finish}, {:say, {:var, :b}, :finish}}"
    assert src =~ "{:say, :b1, {:hear, :bit, :c, :finish}}"
    refute src =~ "def kept"
    refute src =~ "def on"

    Code.compile_string(src)

    {:ok, server, client, server_ref, client_ref} = indexed(:wire)
    assert_receive {:DOWN, ^server_ref, :process, ^server, :normal}
    assert_receive {:DOWN, ^client_ref, :process, ^client, :normal}

    {:ok, server, client, server_ref, client_ref} = indexed(host_fun("wire-one"))
    assert_receive {:DOWN, ^server_ref, :process, ^server, :normal}
    assert_receive {:DOWN, ^client_ref, :process, ^client, :normal}

    {:ok, echo, ask, echo_ref, ask_ref} = indexed(host_fun("echo-wire"))
    assert_receive {:DOWN, ^echo_ref, :process, ^echo, :normal}
    assert_receive {:DOWN, ^ask_ref, :process, ^ask, :normal}

    # b0 takes the arm that sends 1.
    {:ok, pid, ref} = indexed_one(:Server)
    send(pid, {:muro, self(), :b0})
    assert_receive {:muro, ^pid, 1}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    # b1 takes the arm that receives a nat.
    {:ok, pid, ref} = indexed_one(:Server)
    send(pid, {:muro, self(), :b1})
    send(pid, {:muro, self(), 0})
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
    refute_received {:muro, ^pid, _}

    # A nat is not an index.
    {:ok, pid, ref} = indexed_one(:Server)
    send(pid, {:muro, self(), 0})
    assert_receive {:DOWN, ^ref, :process, ^pid, {:shutdown, {:unexpected, 0}}}

    # A choice label is not an index.
    {:ok, pid, ref} = indexed_one(:Server)
    send(pid, {:muro_pick, self(), :b0})
    assert_receive {:DOWN, ^ref, :process, ^pid, {:shutdown, {:unexpected, :b0}}}

    # The arm sends the bit it received.
    {:ok, pid, ref} = indexed_one(:Echo)
    send(pid, {:muro, self(), :b1})
    assert_receive {:muro, ^pid, :b1}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = indexed_one(:Echo)
    send(pid, {:muro, self(), :b0})
    assert_receive {:muro, ^pid, :b0}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
  end

  test "a recursive protocol is a tail call on the BEAM" do
    assert {:ok, src} = Emit.Otp.render(checked!("examples/recursive.muro"), "recursive")
    assert src =~ "def wire do"
    assert src =~ "{:loop, :X, {:hear, :nat, :n, {:say, {:var, :n}, {:jump, :X}}}}"

    assert src =~
             "{:loop, :X, {:index, :b, {:hear, :nat, :n, {:say, {:var, :n}, {:jump, :X}}}, :finish}}"

    assert src =~ "loops: %{}"
    refute src =~ "def kept"

    Code.compile_string(src)

    {:ok, server, client, server_ref, client_ref} = recursive(:wire)
    assert_receive {:DOWN, ^server_ref, :process, ^server, :normal}
    assert_receive {:DOWN, ^client_ref, :process, ^client, :normal}

    {:ok, pid, ref} = recursive_one(:Forever)
    send(pid, {:muro, self(), 1})
    assert_receive {:muro, ^pid, 1}
    send(pid, {:muro, self(), 2})
    assert_receive {:muro, ^pid, 2}
    GenServer.stop(pid)
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
    assert src =~ "def #{Emit.elixir_base("a-b")} do"
    assert src =~ "def a_b do"
    refute src =~ "def a_b_2 do"
    refute src =~ "def a_b2 do"
    assert src =~ "def #{Emit.elixir_base("end")} do"
    assert src =~ "{:hear, :nat, :_, {:say, 1, :finish}}"
    assert src =~ "{:say, 1, {:hear, :nat, :_, :finish}}"
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
    assert src =~ "defmodule #{Emit.elixir_alias("pong-home")} do"
    assert length(String.split(src, "{:hear, :nat, :_, {:say, 1, :finish}}")) == 3
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

    {:ok, away, away_ref} = located(host_mod("pong-away"))
    send(away, {:muro, self(), 0})
    assert_receive {:muro, ^away, 1}
    assert_receive {:DOWN, ^away_ref, :process, ^away, :normal}

    {:ok, open, open_ref} = located(host_mod("left-open"))
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
    {:ok, pid, ref} = start(host_mod("left-open"))
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
    {:ok, pid, ref} = start(host_mod("pong-done"))
    send(pid, {:muro, self(), 0})
    assert_receive {:muro, ^pid, 1}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
  end

  defp open_stop do
    {:ok, pid, ref} = start(host_mod("open-stop"))
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

  test "a declared data value is the OTP message" do
    src = """
    data Bool : Type where
      true : Bool
      false : Bool

    data Maybe (A : Type) : Type where
      nothing : Maybe A
      just : A → Maybe A

    session flag := send Bool end
    session flag-back := dual flag
    conform up : flag := put true done
    conform down : flag-back := get Bool done
    meet flag-wire : up with down

    session opt := send (Maybe Nat) end
    session opt-back := dual opt
    conform some : opt := put (just 0) done
    conform take : opt-back := get (Maybe Nat) done
    meet opt-wire : some with take

    session echo := recv Bool (send Bool end)
    session echo-back := dual echo
    conform echoer : echo := get (k : Bool) (put k done)
    conform ask : echo-back := put false (get (m : Bool) done)
    meet echo-wire : echoer with ask

    conform shadow : echo := get (true : Bool) (put true done)
    """

    assert {:ok, book} = Parser.parse(src)
    assert Muro.Check.check_sig(book) == :ok
    emit = Muro.Prelude.for_emit(book)
    assert {:ok, otp} = Emit.Otp.render(emit, "data")
    assert otp =~ "{:say, true, :finish}"
    assert otp =~ "{:hear, {:dat, \"Bool\", []}, :_, :finish}"
    assert otp =~ "{:say, {:just, 0}, :finish}"
    assert otp =~ "{:hear, {:dat, \"Bool\", []}, :k, {:say, {:var, :k}, :finish}}"
    assert otp =~ "{:hear, {:dat, \"Bool\", []}, true, {:say, {:var, true}, :finish}}"
    refute otp =~ "esend"
    refute otp =~ "≤"

    Code.compile_string(otp)

    {:ok, left, right, left_ref, right_ref} = data(host_fun("flag-wire"))
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}

    {:ok, left, right, left_ref, right_ref} = data(host_fun("opt-wire"))
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}

    {:ok, pid, ref} = data_one(:Down)
    send(pid, {:muro, self(), true})
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = data_one(:Down)
    send(pid, {:muro, self(), :nothing})
    assert_receive {:DOWN, ^ref, :process, ^pid, {:shutdown, {:unexpected, :nothing}}}

    {:ok, pid, ref} = data_one(:Take)
    send(pid, {:muro, self(), {:just, 0}})
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = data_one(:Take)
    send(pid, {:muro, self(), true})
    assert_receive {:DOWN, ^ref, :process, ^pid, {:shutdown, {:unexpected, true}}}

    {:ok, pid, ref} = data_one(:Echoer)
    send(pid, {:muro, self(), false})
    assert_receive {:muro, ^pid, false}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = data_one(:Shadow)
    send(pid, {:muro, self(), false})
    assert_receive {:muro, ^pid, false}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
  end

  test "a computed put and a value match are the OTP message" do
    assert {:ok, src} = Emit.Otp.render(checked!("examples/computed.muro"), "computed")
    assert src =~ "{:say, {:just, true}, :finish}"
    assert src =~ "{:loop, :X, {:say, {:just, true}, {:jump, :X}}}"
    assert src =~ "{:pick, ["
    refute src =~ ~s/{:run, "effective"/
    refute src =~ "def effective"
    refute src =~ "esend"

    Code.compile_string(src)

    {:ok, left, right, left_ref, right_ref} = computed(host_fun("reply-wire"))
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}

    {:ok, left, right, left_ref, right_ref} = computed(:arm0)
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}
    refute_received {:muro, _, 0}

    {:ok, left, right, left_ref, right_ref} = computed(:arm1)
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}

    {:ok, pid, ref} = computed_one(:Taker)
    send(pid, {:muro, self(), :b0})
    assert_receive {:muro_pick, ^pid, :b0}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
    refute_received {:muro, ^pid, 0}

    {:ok, pid, ref} = computed_one(:Taker)
    send(pid, {:muro, self(), :b1})
    assert_receive {:muro_pick, ^pid, :b1}
    assert_receive {:muro, ^pid, 0}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = computed_one(host_mod("flag-taker"))
    send(pid, {:muro, self(), true})
    assert_receive {:muro_pick, ^pid, :b0}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
    refute_received {:muro, ^pid, _}

    {:ok, pid, ref} = computed_one(host_mod("flag-taker"))
    send(pid, {:muro, self(), false})
    assert_receive {:muro_pick, ^pid, :b1}
    assert_receive {:muro, ^pid, 1}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = computed_one(host_mod("flag-taker"))
    send(pid, {:muro, self(), :nothing})
    assert_receive {:DOWN, ^ref, :process, ^pid, {:shutdown, {:unexpected, :nothing}}}

    {:ok, pid, ref} = computed_one(host_mod("opt-taker"))
    send(pid, {:muro, self(), :nothing})
    assert_receive {:DOWN, ^ref, :process, ^pid, {:shutdown, :abandon}}

    {:ok, pid, ref} = computed_one(host_mod("opt-taker"))
    send(pid, {:muro, self(), {:just, 0}})
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = computed_one(host_mod("opt-taker"))
    send(pid, {:muro, self(), true})
    assert_receive {:DOWN, ^ref, :process, ^pid, {:shutdown, {:unexpected, true}}}
  end

  test "a value case picks the process arm, and evidence stays off the message" do
    assert {:ok, src} =
             Emit.Otp.render(checked!("examples/value-protocols.muro"), "value-protocols")

    assert src =~
             "{:hear, {:dat, \"Frame\", []}, :f, {:pick, [{:say, :rst, :finish}, {:say, :rst, :finish}, {:hear, {:dat, \"Body\", []}, :b, :finish}]}}"

    assert src =~
             "{:hear, {:dat, \"Frame\", []}, :f, {:pick, [{:say, :rst, :finish}, {:say, :rst, :finish}, {:say, :goaway, :finish}]}}"

    assert src =~
             "{:hear, {:dat, \"Frame\", []}, :f, {:pick, [{:say, 0, :finish}, :finish, :finish]}}"

    assert src =~ "{:say, :headers, {:say, :chunk, :finish}}"
    refute src =~ "≤"
    refute src =~ ~s/{:run, "late"/
    refute src =~ "def late"

    Code.compile_string(src)
  end

  test "a field binding is the OTP receive, and the run is evaluated there" do
    assert {:ok, src} =
             Emit.Otp.render(checked!("examples/field-bindings.muro"), "field-bindings")

    assert src =~ "{:arm, \"just\", [:b], {:say, {:run, \"grant\", [var: :b]}, :finish}}"
    assert src =~ "{:arm, \"nothing\", [], {:say, false, :finish}}"
    assert src =~ "{:arm, \"cons\", [:n, :ys], {:say, {:var, :ys}, :finish}}"
    assert src =~ "{:say, {:var, :b}, :finish}"
    refute src =~ "effective"

    Code.compile_string(src)

    {:ok, left, right, left_ref, right_ref} = field(host_fun("reply-wire"))
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}

    {:ok, left, right, left_ref, right_ref} = field(host_fun("pass-wire"))
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}

    {:ok, left, right, left_ref, right_ref} = field(host_fun("tail-wire"))
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}

    {:ok, pid, ref} = field_one(:Reply)
    send(pid, {:muro, self(), {:just, true}})
    assert_receive {:muro, ^pid, true}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = field_one(:Reply)
    send(pid, {:muro, self(), {:just, false}})
    assert_receive {:muro, ^pid, false}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = field_one(:Reply)
    send(pid, {:muro, self(), :nothing})
    assert_receive {:muro, ^pid, false}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = field_one(:Pass)
    send(pid, {:muro, self(), {:just, false}})
    assert_receive {:muro, ^pid, false}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = field_one(:Rest)
    send(pid, {:muro, self(), {:cons, 0, nil}})
    assert_receive {:muro, ^pid, nil}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = field_one(:Rest)
    send(pid, {:muro, self(), nil})
    assert_receive {:muro, ^pid, nil}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
  end

  test "a product arm is the OTP receive, and the run is evaluated there" do
    assert {:ok, src} = Emit.Otp.render(checked!("examples/pair-bindings.muro"), "pair-bindings")

    assert src =~ "{:prod, {:pair, [:n, :b]}, {:say, {:var, :n}, :finish}}"
    assert src =~ "{:prod, {:pair, [:a, :b]}, {:say, {:run, \"grant\", [var: :a]}, :finish}}"
    assert src =~ "{:prod, {:rec, [{\"x\", :a}, {\"y\", :c}]}, {:say, {:var, :c}, :finish}}"
    assert src =~ "defp pick_arm({:pair, _, _}, {a, b}, [{:prod, {:pair, [x, y]}, next}])"
    assert src =~ "defp pick_arm({:rec, fields}, map, [{:prod, {:rec, bs}, next}])"
    refute src =~ "≤"

    Code.compile_string(src)

    for name <- ~w(pair-wire grant-wire rec-wire lin-wire shade-wire wrap-wire box-wire) do
      {:ok, left, right, left_ref, right_ref} = pair(host_fun(name))
      assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
      assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}
    end

    {:ok, pid, ref} = pair_one(host_mod("pair-reply"))
    send(pid, {:muro, self(), {1, :b1}})
    assert_receive {:muro, ^pid, 1}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = pair_one(host_mod("grant-reply"))
    send(pid, {:muro, self(), {true, :b0}})
    assert_receive {:muro, ^pid, true}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = pair_one(host_mod("rec-reply"))
    send(pid, {:muro, self(), %{"x" => 1, "y" => :b0}})
    assert_receive {:muro, ^pid, :b0}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = pair_one(host_mod("lin-reply"))
    send(pid, {:muro, self(), {2, :b1}})
    assert_receive {:muro, ^pid, 2}
    assert_receive {:muro, ^pid, 2}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = pair_one(host_mod("shade-reply"))
    send(pid, {:muro, self(), {0, :b0}})
    assert_receive {:muro, ^pid, :b0}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = pair_one(host_mod("wrap-reply"))
    send(pid, {:muro, self(), {{1, :b1}, :b0}})
    assert_receive {:muro, ^pid, {1, :b1}}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = pair_one(host_mod("box-reply"))
    send(pid, {:muro, self(), %{"x" => {1, :b1}, "y" => :b0}})
    assert_receive {:muro, ^pid, {1, :b1}}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
  end

  test "a field the run reads is the OTP split, and the value is already on the message" do
    assert {:ok, src} = Emit.Otp.render(checked!("examples/field-choice.muro"), "field-choice")

    assert src =~
             "{:arm, \"just\", [:b], {:split, :b, [{:arm, \"true\", [], {:say, :rst, :finish}}, {:arm, \"false\", [], :finish}]}}"

    assert src =~
             "{:arm, \"hdr\", [:f], {:split, :f, [{:arm, \"bytes\", [], {:say, :rst, :finish}}, {:arm, \"trailers\", [], :finish}, {:arm, \"headers\", [], :finish}]}}"

    assert src =~ "{:pick, ["
    refute src =~ "esend"
    refute src =~ "≤"

    Code.compile_string(src)

    {:ok, left, right, left_ref, right_ref} = choice(host_fun("gate-true"))
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}

    {:ok, left, right, left_ref, right_ref} = choice(host_fun("gate-true-swap"))
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}

    {:ok, left, right, left_ref, right_ref} = choice(host_fun("gate-false"))
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}

    {:ok, left, right, left_ref, right_ref} = choice(host_fun("gate-none"))
    assert_receive {:DOWN, ^left_ref, :process, ^left, :normal}
    assert_receive {:DOWN, ^right_ref, :process, ^right, :normal}

    {:ok, pid, ref} = choice_one(host_mod("gate-server"))
    send(pid, {:muro, self(), {:just, true}})
    assert_receive {:muro, ^pid, :rst}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = choice_one(host_mod("gate-server"))
    send(pid, {:muro, self(), {:just, false}})
    refute_receive {:muro, ^pid, _}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = choice_one(host_mod("gate-server"))
    send(pid, {:muro, self(), :nothing})
    refute_receive {:muro, ^pid, _}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = choice_one(host_mod("hdr-server"))
    send(pid, {:muro, self(), {:hdr, :bytes}})
    assert_receive {:muro, ^pid, :rst}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = choice_one(host_mod("wrap-server"))
    send(pid, {:muro, self(), {:wrap, {:hdr, :bytes}}})
    assert_receive {:muro, ^pid, :rst}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}

    {:ok, pid, ref} = choice_one(host_mod("wrap-server"))
    send(pid, {:muro, self(), {:wrap, {:hdr, :trailers}}})
    refute_receive {:muro, ^pid, _}
    assert_receive {:DOWN, ^ref, :process, ^pid, :normal}
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

  defp choice(fun) do
    apply(Module.concat(["FieldChoiceOtp"]), fun, [])
  end

  defp choice_one(name) do
    apply(Module.concat("FieldChoiceOtp", name), :start, [self()])
  end

  defp field(fun) do
    apply(Module.concat(["FieldBindingsOtp"]), fun, [])
  end

  defp field_one(name) do
    apply(Module.concat("FieldBindingsOtp", name), :start, [self()])
  end

  defp pair(fun) do
    apply(Module.concat(["PairBindingsOtp"]), fun, [])
  end

  defp pair_one(name) do
    apply(Module.concat("PairBindingsOtp", name), :start, [self()])
  end

  defp computed(fun) do
    apply(Module.concat(["ComputedOtp"]), fun, [])
  end

  defp computed_one(name) do
    apply(Module.concat("ComputedOtp", name), :start, [self()])
  end

  defp data(fun) do
    apply(Module.concat(["DataOtp"]), fun, [])
  end

  defp data_one(name) do
    apply(Module.concat("DataOtp", name), :start, [self()])
  end

  defp indexed(fun) do
    apply(Module.concat(["IndexedOtp"]), fun, [])
  end

  defp indexed_one(name) do
    apply(Module.concat("IndexedOtp", name), :start, [self()])
  end

  defp recursive(fun) do
    apply(Module.concat(["RecursiveOtp"]), fun, [])
  end

  defp recursive_one(name) do
    apply(Module.concat("RecursiveOtp", name), :start, [self()])
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

  defp host_fun(name), do: String.to_atom(Emit.elixir_base(name))
  defp host_mod(name), do: String.to_atom(Emit.elixir_alias(name))
end

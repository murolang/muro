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
    meet end : pong with peer
    """)

    assert {:ok, src} = Emit.Otp.render(checked!(path), "read-meet")
    assert src =~ "def wire do"
    assert Emit.elixir_base("a-b") == "a_b"
    assert src =~ "def a_b do"
    refute src =~ "def a_b_2 do"
    refute src =~ "def a_b2 do"
    refute src =~ "def muro__azdbar do"
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

  test "an integer buffer caps pending protocol tokens, then the meeting finishes" do
    async = compile_otp!("examples/async-meetings.muro", "buf-async")
    bound = compile_book!(buffer_book(), "buf-bound")

    # Shipped inflight, buffer 1. The receiver is suspended before it runs.
    # The sender's unacked set is the account: one send, id 0. The mailbox
    # is what arrived under this schedule. Both finish :normal after resume.
    {client, server, cref, sref, st, pending} = hold(async.mod, :inflight)
    assert pending == [:headers]
    assert st.cap == 1
    assert st.credit == 0
    assert st.unacked == MapSet.new([0])
    assert MapSet.size(st.unacked) <= st.cap
    assert match?({:say, :trailers, _}, st.send_wait)
    release_and_finish(client, server, cref, sref)

    # Buffer 2 allows both frames. This client has only two puts, so the
    # held mailbox is those two and the unacked set is ids 0 and 1.
    {client, server, cref, sref, st, pending} = hold(async.mod, :inflight_two)
    assert pending == [:headers, :trailers]
    assert st.cap == 2
    assert st.credit == 0
    assert st.unacked == MapSet.new([0, 1])
    assert MapSet.size(st.unacked) <= st.cap
    assert st.send_wait == nil
    release_and_finish(client, server, cref, sref)

    # Three data sends. Cap 1 holds the second and third. Cap 2 holds the third.
    {left, right, lref, rref, st, pending} = hold(bound.mod, :nats1)
    assert pending == [0]
    assert st.credit == 0 and st.unacked == MapSet.new([0])
    assert MapSet.size(st.unacked) <= st.cap
    assert match?({:say, 1, _}, st.send_wait)
    release_and_finish(left, right, lref, rref)

    {left, right, lref, rref, st, pending} = hold(bound.mod, :nats2)
    assert pending == [0, 1]
    assert st.cap == 2 and st.credit == 0 and st.unacked == MapSet.new([0, 1])
    assert MapSet.size(st.unacked) <= st.cap
    assert match?({:say, 2, _}, st.send_wait)
    release_and_finish(left, right, lref, rref)

    # A choice and the following payload share one credit.
    {left, right, lref, rref, st, pending} = hold(bound.mod, :pick1)
    assert pending == [:b0]
    assert st.credit == 0 and st.unacked == MapSet.new([0])
    assert MapSet.size(st.unacked) <= st.cap
    assert match?({:say, 4, _}, st.send_wait)
    release_and_finish(left, right, lref, rref)

    # Meetings that already complete keep completing, buffered and not.
    finish_public(async.mod, :crossed)
    finish_public(async.mod, :line_wire)
    finish_public(async.mod, :inflight)

    nilbuf = compile_otp!("examples/meet.muro", "buf-nil")
    finish_public(nilbuf.mod, :wire)
    assert nilbuf.src =~ "muro_open_pair(left_skel, right_skel, nil)"
    refute exchange_clause(nilbuf.book, nilbuf.src, "wire") =~ ~r/, \d+\)\z/
    assert exchange_clause(async.book, async.src, "inflight") =~ ~r/, 1\)\z/
    assert exchange_clause(async.book, async.src, "inflight-two") =~ ~r/, 2\)\z/
  end

  test "credit returns at consumption, not at enqueue, and start/2 is unbounded" do
    %{mod: mod, book: book} = compile_book!(buffer_book(), "buf-ack")
    hear = carry(book, "hear2")

    {:ok, pid} = GenServer.start(mod, {hear, :open, 1})
    ref = Process.monitor(pid)

    try do
      :ok = GenServer.call(pid, {:muro_peer, self()})
      send(pid, {:muro, self(), 0, 0})
      send(pid, {:muro, self(), 1, 1})
      st = :sys.get_state(pid, 5_000)
      assert st.queue == [{{:muro, self(), 0}, 0}, {{:muro, self(), 1}, 1}]
      refute_received {:muro_ack, _, _}
      refute_received {:muro_ack, _}

      send(pid, :muro_go)
      assert_receive {:muro_ack, ^pid, 0}, 5_000
      assert_receive {:muro_ack, ^pid, 1}, 5_000
      certify(pid, ref)
    after
      stop(pid)
    end

    %{mod: meet} = compile_otp!("examples/meet.muro", "buf-start")
    {:ok, pid, ref} = apply(Module.concat(meet, Pong), :start, [self()])

    try do
      st = :sys.get_state(pid, 5_000)
      assert st.cap == nil and st.credit == nil and st.unacked == MapSet.new()
      send(pid, {:muro, self(), 0})
      assert_receive {:muro, ^pid, 1}, 5_000
      refute_received {:muro_ack, _, _}
      refute_received {:muro_ack, _}
      assert_down(ref, pid, :normal)
    after
      stop(pid)
    end
  end

  test "a replayed ack does not free a newer outstanding send" do
    %{mod: mod, book: book} = compile_book!(buffer_book(), "buf-replay")
    quad = carry(book, "quad-a")

    # Cap 1. ACK(A) resumes B before the duplicate ACK(A) is handled.
    # The duplicate must not free B. A real ACK(B) then releases C.
    {:ok, pid} = GenServer.start(mod, {quad, :open, 1})
    ref = Process.monitor(pid)

    other =
      spawn(fn ->
        receive do
          :done -> :ok
        end
      end)

    try do
      :ok = GenServer.call(pid, {:muro_peer, self()})
      send(pid, :muro_go)
      assert_receive {:muro, ^pid, 0, 0}, 5_000
      st = :sys.get_state(pid, 5_000)
      assert st.credit == 0
      assert st.unacked == MapSet.new([0])
      assert MapSet.size(st.unacked) <= st.cap
      assert st.next_send == 1
      assert match?({:say, 1, _}, st.send_wait)

      send(pid, {:muro_ack, self(), 0})
      send(pid, {:muro_ack, self(), 0})
      assert_receive {:muro, ^pid, 1, 1}, 5_000
      st = :sys.get_state(pid, 5_000)
      assert st.credit == 0
      assert st.unacked == MapSet.new([1])
      assert MapSet.size(st.unacked) <= st.cap
      assert st.next_send == 2
      assert match?({:say, 2, _}, st.send_wait)
      refute_protocol(pid)

      send(pid, {:muro_ack, other, 1})
      send(pid, {:muro_ack, self(), 99})
      send(pid, {:muro_ack, self()})
      held = :sys.get_state(pid, 5_000)
      assert held.credit == st.credit
      assert held.unacked == st.unacked
      assert held.next_send == st.next_send
      assert held.send_wait == st.send_wait
      refute_protocol(pid)

      send(pid, {:muro_ack, self(), 1})
      assert_receive {:muro, ^pid, 2, 2}, 5_000
      st = :sys.get_state(pid, 5_000)
      assert st.credit == 0
      assert st.unacked == MapSet.new([2])
      assert MapSet.size(st.unacked) <= st.cap
      refute_protocol(pid)

      send(pid, {:muro_ack, self(), 2})
      assert_receive {:muro, ^pid, 3, 3}, 5_000
      send(pid, {:muro_ack, self(), 3})
      certify(pid, ref)
    after
      Process.exit(other, :kill)
      stop(pid)
    end

    # Cap 2. A and B are outstanding. ACK(A) releases C. A replay of ACK(A)
    # must leave B outstanding and must not send D. ACK(B) then sends D.
    {:ok, pid} = GenServer.start(mod, {quad, :open, 2})
    ref = Process.monitor(pid)

    other =
      spawn(fn ->
        receive do
          :done -> :ok
        end
      end)

    try do
      :ok = GenServer.call(pid, {:muro_peer, self()})
      send(pid, :muro_go)
      assert_receive {:muro, ^pid, 0, 0}, 5_000
      assert_receive {:muro, ^pid, 1, 1}, 5_000
      st = :sys.get_state(pid, 5_000)
      assert st.credit == 0
      assert st.unacked == MapSet.new([0, 1])
      assert MapSet.size(st.unacked) <= st.cap
      assert st.next_send == 2
      assert match?({:say, 2, _}, st.send_wait)
      refute_protocol(pid)

      send(pid, {:muro_ack, self(), 0})
      assert_receive {:muro, ^pid, 2, 2}, 5_000
      st = :sys.get_state(pid, 5_000)
      assert st.credit == 0
      assert st.unacked == MapSet.new([1, 2])
      assert MapSet.size(st.unacked) <= st.cap
      assert st.next_send == 3
      refute_protocol(pid)

      send(pid, {:muro_ack, self(), 0})
      send(pid, {:muro_ack, other, 1})
      send(pid, {:muro_ack, self(), 99})
      send(pid, {:muro_ack, self()})
      held = :sys.get_state(pid, 5_000)
      assert held.credit == 0
      assert held.unacked == MapSet.new([1, 2])
      assert MapSet.size(held.unacked) <= held.cap
      assert held.next_send == st.next_send
      refute_protocol(pid)

      send(pid, {:muro_ack, self(), 1})
      assert_receive {:muro, ^pid, 3, 3}, 5_000
      send(pid, {:muro_ack, self(), 2})
      send(pid, {:muro_ack, self(), 3})
      certify(pid, ref)
    after
      Process.exit(other, :kill)
      stop(pid)
    end
  end

  test "a peer crash while credit is exhausted abandons the waiting sender" do
    %{mod: mod} = compile_book!(buffer_book(), "buf-down")
    {left, right, lref, rref, st, pending} = hold(mod, :nats1)

    try do
      assert pending == [0]
      assert st.credit == 0 and st.send_wait != nil
      Process.exit(right, :kill)
      assert_down(rref, right, :killed)
      assert_down(lref, left, {:shutdown, :abandon})
    after
      stop(left)
      stop(right)
    end
  end

  test "buffer 0 blocks every send and is not a rendezvous" do
    # The checker rejects `meet ... buffer 0` as deadlock, matching the
    # source. This drives the emitted integer-cap init at 0.
    %{mod: mod, book: book} = compile_book!(buffer_book(), "buf-cap0")
    {left, right, lref, rref} = open_pair(mod, carry(book, "burst-a"), carry(book, "sink-b"), 0)

    try do
      send(left, :muro_go)
      send(right, :muro_go)
      refute_receive {:DOWN, ^lref, :process, ^left, _}, 200
      refute_receive {:DOWN, ^rref, :process, ^right, _}, 200
      st = :sys.get_state(left, 5_000)
      rst = :sys.get_state(right, 5_000)
      assert st.cap == 0 and st.credit == 0 and st.phase == :run
      assert st.unacked == MapSet.new()
      assert match?({:say, 0, _}, st.send_wait)
      assert protocol_mailbox(right) == []
      assert rst.phase == :run and rst.queue == []
      assert Process.alive?(left) and Process.alive?(right)
    after
      stop(left)
      stop(right)
    end
  end

  test "finite prefixes of infinite meetings keep the unacked set within N" do
    %{mod: mod, book: book} = compile_otp!("examples/async-meetings.muro", "buf-spin")
    spin = carry(book, "spin-client")
    echo = carry(book, "echo-a")

    {pid, ref} = paired_sender(mod, spin, 1)

    try do
      send(pid, :muro_go)

      Enum.each(0..15, fn i ->
        assert_receive {:muro, ^pid, ^i, :bytes}, 5_000
        st = :sys.get_state(pid, 5_000)
        assert st.phase == :run
        assert st.unacked == MapSet.new([i])
        assert MapSet.size(st.unacked) <= st.cap
        assert st.next_send == i + 1
        send(pid, {:muro_ack, self(), i})
      end)

      assert_receive {:muro, ^pid, 16, :bytes}, 5_000
      st = :sys.get_state(pid, 5_000)
      assert st.unacked == MapSet.new([16])
      assert st.next_send == 17
      assert MapSet.size(st.unacked) <= st.cap
      assert Process.alive?(pid)
    after
      stop(pid)
      _ = Process.demonitor(ref, [:flush])
    end

    {pid, ref} = paired_sender(mod, echo, 1)

    try do
      send(pid, :muro_go)
      assert_receive {:muro, ^pid, 0, 0}, 5_000

      Enum.each(0..3, fn i ->
        next = i + 1
        send(pid, {:muro_ack, self(), i})
        send(pid, {:muro, self(), i, 0})
        assert_receive {:muro_ack, ^pid, ^i}, 5_000
        assert_receive {:muro, ^pid, ^next, 0}, 5_000
        st = :sys.get_state(pid, 5_000)
        assert st.phase == :run
        assert st.unacked == MapSet.new([next])
        assert MapSet.size(st.unacked) <= st.cap
        assert st.next_send == next + 1
      end)
    after
      stop(pid)
      _ = Process.demonitor(ref, [:flush])
    end
  end

  test "concurrent and repeated meetings do not accept a foreign ack" do
    %{mod: mod, book: book} = compile_book!(buffer_book(), "buf-iso")
    quad = carry(book, "quad-a")
    {a, aref} = paired_sender(mod, quad, 1)
    {b, bref} = paired_sender(mod, quad, 1)

    try do
      send(a, :muro_go)
      send(b, :muro_go)
      assert_receive {:muro, ^a, 0, 0}, 5_000
      assert_receive {:muro, ^b, 0, 0}, 5_000
      send(b, {:muro_ack, a, 0})
      stb = :sys.get_state(b, 5_000)
      assert stb.credit == 0 and stb.unacked == MapSet.new([0])
      refute_protocol(b)
      send(a, {:muro_ack, self(), 0})
      assert_receive {:muro, ^a, 1, 1}, 5_000
      stb = :sys.get_state(b, 5_000)
      assert stb.credit == 0 and stb.unacked == MapSet.new([0])
      refute_protocol(b)
    after
      stop(a)
      stop(b)
      _ = Process.demonitor(aref, [:flush])
      _ = Process.demonitor(bref, [:flush])
    end

    {old, old_ref} = paired_sender(mod, quad, 1)

    try do
      send(old, :muro_go)
      assert_receive {:muro, ^old, 0, 0}, 5_000
    after
      stop(old)
    end

    assert_down(old_ref, old, :killed)
    {pid, ref} = paired_sender(mod, quad, 1)

    try do
      send(pid, :muro_go)
      assert_receive {:muro, ^pid, 0, 0}, 5_000
      send(pid, {:muro_ack, old, 0})
      st = :sys.get_state(pid, 5_000)
      assert st.credit == 0 and st.unacked == MapSet.new([0])
      assert st.next_send == 1
      refute_protocol(pid)
    after
      stop(pid)
      _ = Process.demonitor(ref, [:flush])
    end
  end

  test "a source-finished sender stays up until the receiver consumes" do
    %{mod: mod, book: book} = compile_book!(buffer_book(), "buf-life")

    # Scheduler block and suspend are a deterministic stand-in for the
    # old interpreter breakpoint before the receiver's go. This does not
    # claim that native preemption reproduced that race.
    {left, right, lref, rref, st, pending} = hold(mod, :nats3)
    assert pending == [0, 1, 2]
    assert st.phase == :settled and st.paired
    assert st.unacked == MapSet.new([0, 1, 2])
    assert MapSet.size(st.unacked) <= st.cap
    assert Process.alive?(left) and Process.alive?(right)
    refute_received {:DOWN, ^lref, :process, ^left, _}
    release_and_finish(left, right, lref, rref)

    burst = carry(book, "burst-a")
    sink = carry(book, "sink-b")
    {left, right, lref, rref} = open_pair(mod, burst, sink, 3)

    try do
      send(left, :muro_go)
      st = :sys.get_state(left, 5_000)
      rst = :sys.get_state(right, 5_000)
      assert st.phase == :settled
      assert st.unacked == MapSet.new([0, 1, 2])
      assert rst.phase == :run and rst.skel != nil

      assert Enum.map(rst.queue, fn {{:muro, _, value}, id} -> {id, value} end) == [
               {0, 0},
               {1, 1},
               {2, 2}
             ]

      assert Process.alive?(left)
      refute_received {:DOWN, ^lref, :process, ^left, _}
      send(right, :muro_go)
      assert_down(lref, left, :normal)
      assert_down(rref, right, :normal)
    after
      stop(left)
      stop(right)
    end
  end

  test "a crash while lifecycle is parked abandons the finished sender" do
    %{mod: mod, book: book} = compile_book!(buffer_book(), "buf-parked")
    burst = carry(book, "burst-a")
    sink = carry(book, "sink-b")
    {left, right, lref, rref} = open_pair(mod, burst, sink, 3)

    try do
      send(left, :muro_go)
      st = :sys.get_state(left, 5_000)
      assert st.phase == :settled and MapSet.size(st.unacked) == 3
      Process.exit(right, :kill)
      assert_down(rref, right, :killed)
      assert_down(lref, left, {:shutdown, :abandon})
    after
      stop(left)
      stop(right)
    end
  end

  test "an unexpected payload stops with an explicit reason" do
    %{mod: mod, book: book} = compile_book!(buffer_book(), "buf-bad")
    hear = carry(book, "hear2")
    {:ok, pid} = GenServer.start(mod, {hear, :open, 1})
    ref = Process.monitor(pid)

    try do
      :ok = GenServer.call(pid, {:muro_peer, self()})
      send(pid, :muro_go)
      send(pid, {:muro, self(), 0, :not_nat})
      assert_down(ref, pid, {:shutdown, {:unexpected, :not_nat}})
    after
      stop(pid)
    end
  end

  defp buffer_book do
    """
    session burst := send Nat (send Nat (send Nat end))
    session sink := recv Nat (recv Nat (recv Nat end))
    conform burst-a : burst := put 0 (put 1 (put 2 done))
    conform sink-b : sink := get (a : Nat) (get (b : Nat) (get (c : Nat) done))
    meet nats1 : burst-a with sink-b buffer 1
    meet nats2 : burst-a with sink-b buffer 2
    meet nats3 : burst-a with sink-b buffer 3

    session pick := choose (send Nat end) (end)
    session picked := dual pick
    conform picker : pick := pick0 (put 4 done)
    conform coverer : picked := cover (get (n : Nat) done) done
    meet pick1 : picker with coverer buffer 1

    session two := recv Nat (recv Nat end)
    conform hear2 : two := get (a : Nat) (get (b : Nat) done)
    session quad := send Nat (send Nat (send Nat (send Nat end)))
    conform quad-a : quad := put 0 (put 1 (put 2 (put 3 done)))
    """
  end

  defp compile_otp!(path, stem) do
    compile_book!(checked!(path), stem)
  end

  defp compile_book!(book, stem) when is_list(book) do
    compile_rendered!(book, stem)
  end

  defp compile_book!(src, stem) when is_binary(src) do
    dir = tmp!()
    path = Path.join(dir, stem <> ".muro")
    File.write!(path, src)
    compile_rendered!(checked!(path), stem)
  end

  defp compile_rendered!(book, stem) do
    assert {:ok, src} = Emit.Otp.render(book, stem)
    parent = Module.concat([module_name(stem)])
    mods = Code.compile_string(src)
    assert Enum.any?(mods, fn {compiled, _} -> compiled == parent end)
    mod = parent

    on_exit(fn ->
      :code.purge(mod)
      :code.delete(mod)

      for name <- ~w(burst-a sink-b picker coverer hear2 quad-a pong spin-client echo-a) do
        child = Module.concat(mod, Emit.elixir_alias(name))
        :code.purge(child)
        :code.delete(child)
      end
    end)

    %{book: book, src: src, mod: mod}
  end

  defp module_name(stem) do
    stem |> String.replace("-", "_") |> Macro.camelize() |> Kernel.<>("Otp")
  end

  defp certify(pid, ref) do
    assert_receive {:muro_settled, ^pid}, 5_000
    send(pid, {:muro_settled, self()})
    assert_down(ref, pid, :normal)
  end

  defp paired_sender(mod, skel, cap) do
    {:ok, pid} = GenServer.start(mod, {skel, :open, cap})
    ref = Process.monitor(pid)
    :ok = GenServer.call(pid, {:muro_peer, self()})
    {pid, ref}
  end

  defp open_pair(mod, left_skel, right_skel, cap) do
    {:ok, left} = GenServer.start(mod, {left_skel, :open, cap})
    {:ok, right} = GenServer.start(mod, {right_skel, :open, cap})
    lref = Process.monitor(left)
    rref = Process.monitor(right)
    :ok = GenServer.call(left, {:muro_peer, right})
    :ok = GenServer.call(right, {:muro_peer, left})
    {left, right, lref, rref}
  end

  defp hold(mod, fun) do
    # One scheduler, so the receiver cannot run between the two go sends
    # and the suspend. `unblock` restores the previous schedulers.
    previous = :erlang.system_flag(:multi_scheduling, :block)

    try do
      {:ok, left, right, lref, rref} = apply(mod, fun, [])

      on_exit(fn ->
        stop(left)
        stop(right)
      end)

      true = :erlang.suspend_process(right)
      state = :sys.get_state(left, 5_000)
      {left, right, lref, rref, state, protocol_mailbox(right)}
    after
      if previous == :enabled, do: :erlang.system_flag(:multi_scheduling, :unblock)
    end
  end

  defp release_and_finish(left, right, lref, rref) do
    try do
      if Process.alive?(right), do: :erlang.resume_process(right)
      assert_down(lref, left, :normal)
      assert_down(rref, right, :normal)
    after
      stop(left)
      stop(right)
    end
  end

  defp finish_public(mod, fun) do
    {:ok, left, right, lref, rref} = apply(mod, fun, [])

    try do
      assert_down(lref, left, :normal)
      assert_down(rref, right, :normal)
    after
      stop(left)
      stop(right)
    end
  end

  defp protocol_mailbox(pid) do
    {:messages, msgs} = Process.info(pid, :messages)

    for msg <- msgs, {:ok, value} <- [protocol_payload(msg)], do: value
  end

  defp protocol_payload({:muro, _, _, value}), do: {:ok, value}
  defp protocol_payload({:muro_pick, _, _, bit}), do: {:ok, bit}
  defp protocol_payload({:muro, _, value}), do: {:ok, value}
  defp protocol_payload({:muro_pick, _, bit}), do: {:ok, bit}
  defp protocol_payload(_msg), do: :error

  defp refute_protocol(pid) do
    refute_received {:muro, ^pid, _, _}
    refute_received {:muro_pick, ^pid, _, _}
    refute_received {:muro, ^pid, _}
    refute_received {:muro_pick, ^pid, _}
  end

  defp exchange_clause(book, src, name) do
    {:ok, outline} = Emit.Otp.outline(book, "clause")
    clause = Enum.find(outline.clauses, &String.starts_with?(&1, "def #{host_fun(name)} do"))
    # The next outline clause is the exchange call, stored beside the def.
    idx = Enum.find_index(outline.clauses, &(&1 == clause))
    call = Enum.at(outline.clauses, idx + 1)
    assert src =~ call
    call
  end

  defp carry(book, name) do
    %{proc: proc} =
      Enum.find(book, fn
        %{kind: kind, name: ^name, proc: proc}
        when kind in [:conform, :read] and not is_nil(proc) ->
          true

        _ ->
          false
      end)

    Session.carry(proc, book)
  end

  defp assert_down(ref, pid, reason) do
    assert_receive {:DOWN, ^ref, :process, ^pid, got}, 5_000
    assert got == reason
  end

  defp stop(pid) when is_pid(pid) do
    if Process.alive?(pid) and Process.info(pid, :status) == {:status, :suspended} do
      :erlang.resume_process(pid)
    end

    if Process.alive?(pid), do: Process.exit(pid, :kill)
  end

  defp stop(_), do: :ok

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

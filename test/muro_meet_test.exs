defmodule Muro.MeetTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, IR, Meet, Parser}

  test "a send meets a receive of the same type" do
    pong = {:get, :nat, :_, {:put, :nat, {:nat, 1}, :done}}
    peer = {:put, :nat, {:nat, 0}, {:get, :nat, :_, :done}}
    other = {:put, :nat, {:nat, 2}, {:get, :nat, :_, :done}}
    assert Meet.meets(pong, peer) == :ok
    assert Meet.meets(pong, other) == :ok
    assert Meet.meets(peer, pong) == :ok

    box = {:pair, :bit, {:rec, [{"x", :nat}, {"y", :nat}]}}
    here = {:tup, :b0, {:rec, [{"x", {:nat, 0}}, {"y", {:nat, 0}}]}}
    there = {:tup, :b1, {:rec, [{"x", {:nat, 1}}, {"y", {:nat, 2}}]}}
    assert Meet.meets({:put, box, here, :done}, {:get, box, :_, :done}) == :ok
    assert Meet.meets({:put, box, there, :done}, {:get, box, :_, :done}) == :ok

    assert Meet.meets({:put, :nat, {:nat, 0}, :stop}, {:get, :nat, :_, :stop}) == :ok
    assert Meet.meets({:pick0, :done}, {:cover, :done, {:get, :nat, :_, :done}}) == :ok
    assert Meet.meets(:done, :done) == :ok
    assert Meet.meets(:stop, :stop) == :ok
  end

  test "a type they do not share has no derivation" do
    assert {:error, msg} = Meet.meets({:get, :bit, :_, :done}, {:put, :nat, {:nat, 0}, :done})
    assert msg == "diverged: left: get Bit; right: put 0"

    swapped = {:rec, [{"y", :nat}, {"x", :nat}]}
    point = {:rec, [{"x", :nat}, {"y", :nat}]}

    assert {:error, msg} =
             Meet.meets(
               {:put, point, {:rec, [{"x", {:nat, 0}}, {"y", {:nat, 1}}]}, :done},
               {:get, swapped, :_, :done}
             )

    assert msg =~ "diverged"

    assert {:error, msg} =
             Meet.meets({:put, :nat, {:nat, 0}, :done}, {:put, :nat, {:nat, 0}, :done})

    assert msg == "diverged: left: put 0; right: put 0"

    assert {:error, msg} = Meet.meets({:put, :nat, {:nat, 0}, :stop}, {:get, :nat, :_, :done})
    assert msg == "diverged after put 0: left: stop; right: done"

    assert {:error, msg} =
             Meet.meets({:pick0, :done}, {:cover, :stop, {:get, :nat, :_, :done}})

    assert msg == "diverged after arm pick0: left: done; right: stop"
  end

  test "a bound name meets a receive of the type it was bound" do
    echo = {:get, :nat, :k, {:put, :unknown, {:var, :k}, :done}}
    peer = {:put, :nat, {:nat, 1}, {:get, :nat, :_, :done}}
    assert Meet.meets(echo, peer) == :ok
    assert Meet.meets(peer, echo) == :ok

    twice =
      {:get, :nat, :k, {:put, :unknown, {:var, :k}, {:put, :unknown, {:var, :k}, :done}}}

    again = {:put, :nat, {:nat, 1}, {:get, :nat, :_, {:get, :nat, :_, :done}}}
    assert Meet.meets(twice, again) == :ok

    point = {:rec, [{"x", :nat}, {"y", :nat}]}
    sent = {:rec, [{"x", {:nat, 0}}, {"y", {:nat, 1}}]}
    record = {:get, point, :p, {:put, :unknown, {:var, :p}, :done}}
    assert Meet.meets(record, {:put, point, sent, {:get, point, :_, :done}}) == :ok

    inner = {:get, :nat, :v, {:get, :bit, :v, {:put, :unknown, {:var, :v}, :done}}}
    bits = {:put, :nat, {:nat, 0}, {:put, :bit, :b0, {:get, :bit, :_, :done}}}
    assert Meet.meets(inner, bits) == :ok
    assert Meet.meets(bits, inner) == :ok

    chosen = {:pick0, {:get, :nat, :k, {:put, :unknown, {:var, :k}, :done}}}
    offered = {:cover, {:put, :nat, {:nat, 1}, {:get, :nat, :_, :done}}, :done}
    assert Meet.meets(chosen, offered) == :ok
  end

  test "a bound name does not meet a receive of another type" do
    echo = {:get, :nat, :k, {:put, :unknown, {:var, :k}, :done}}
    bit = {:put, :nat, {:nat, 0}, {:get, :bit, :_, :done}}
    assert {:error, msg} = Meet.meets(echo, bit)
    assert msg == "diverged after put 0: left: put k; right: get Bit"
    assert {:error, msg} = Meet.meets(bit, echo)
    assert msg == "diverged after put 0: left: get Bit; right: put k"

    assert {:error, msg} =
             Meet.meets({:put, :unknown, {:var, :k}, :done}, {:get, :nat, :_, :done})

    assert msg == "diverged: left: put k; right: get Nat"

    inner = {:get, :nat, :v, {:get, :bit, :v, {:put, :unknown, {:var, :v}, :done}}}
    nats = {:put, :nat, {:nat, 0}, {:put, :bit, :b0, {:get, :nat, :_, :done}}}
    assert {:error, msg} = Meet.meets(inner, nats)
    assert msg == "diverged after put 0, put b0: left: put v; right: get Nat"

    point = {:rec, [{"x", :nat}, {"y", :nat}]}
    swapped = {:rec, [{"y", :nat}, {"x", :nat}]}
    sent = {:rec, [{"x", {:nat, 0}}, {"y", {:nat, 1}}]}
    record = {:get, point, :p, {:put, :unknown, {:var, :p}, :done}}

    assert {:error, msg} =
             Meet.meets(record, {:put, point, sent, {:get, swapped, :_, :done}})

    assert msg ==
             "diverged after put {x = 0, y = 1}: left: put p; right: get {y : Nat, x : Nat}"
  end

  test "a received nat is the length of the vector that meets it" do
    vec = fn e -> {:vec, :nat, e} end
    server = {:get, :nat, :n, {:put, vec.({:var, :n}), {:rep, {:var, :n}, {:nat, 0}}, :done}}
    client = {:put, :nat, {:nat, 2}, {:get, vec.({:lit, 2}), :_, :done}}
    assert Meet.meets(server, client) == :ok
    assert Meet.meets(client, server) == :ok

    short = {:put, :nat, {:nat, 2}, {:get, vec.({:lit, 3}), :_, :done}}
    assert {:error, msg} = Meet.meets(server, short)
    assert msg == "diverged after put 2: left: put rep n 0; right: get (Vec Nat 3)"
    assert {:error, msg} = Meet.meets(short, server)
    assert msg == "diverged after put 2: left: get (Vec Nat 3); right: put rep n 0"

    assert check("""
           session sized := recv (n : Nat) (send (Vec Nat n) end)
           session back := dual sized
           conform server : sized := get (n : Nat) (put (rep n 0) done)
           conform client : back := put 2 (get (Vec Nat 2) done)
           meet wire : server with client
           """) == :ok

    assert {:error, msg} =
             check("""
             session sized := recv (n : Nat) (send (Vec Nat n) end)
             session back := dual sized
             conform server : sized := get (n : Nat) (put (rep n 0) done)
             conform bad : back := put 2 (get (Vec Nat 3) done)
             meet wire : server with bad
             """)

    assert msg =~ "does not conform"
    assert msg =~ "skipped because bad does not conform"
    refute msg =~ "diverged"
  end

  test "an evidence payload meets as a nat" do
    server = {:get, :nat, :w, {:put, :unknown, {:var, :w}, :done}}
    client = {:put, :nat, {:nat, 8}, {:get, :nat, :d, :done}}
    assert Meet.meets(server, client) == :ok
    assert Meet.meets(client, server) == :ok

    assert check("""
           session window := recv (w : Nat) (send (d : Nat) {d ≤ w} end)
           session grant-end := dual window
           conform server : window := get (w : Nat) (put w done)
           conform client : grant-end := put 8 (get (d : Nat) done)
           meet wire : server with client
           """) == :ok
  end

  test "a guess meets the grant but has no conformance" do
    # The meeting compares nats. The evidence is the conformance.
    guess = {:get, :nat, :w, {:put, :nat, {:nat, 9}, :done}}
    client = {:put, :nat, {:nat, 8}, {:get, :nat, :d, :done}}
    assert Meet.meets(guess, client) == :ok

    assert {:error, msg} =
             check("""
             session window := recv (w : Nat) (send (d : Nat) {d ≤ w} end)
             session grant-end := dual window
             conform guess : window := get (w : Nat) (put 9 done)
             conform client : grant-end := put 8 (get (d : Nat) done)
             meet wire : guess with client
             """)

    assert msg =~ "put 9 done does not conform to send (d : Nat) {d ≤ w} end"

    # The receiver gets a nat. A bit does not meet it.
    assert {:no, _, _} = Meet.go(guess, {:put, :nat, {:nat, 8}, {:get, :bit, :d, :done}})
  end

  test "a claimed length does not meet the length of the received nat" do
    # The sender sends 3 and then a vector of length 2.
    # The receiver expects a vector whose length is that nat.
    vec2 = {:rep, {:nat, 2}, {:nat, 0}}

    assert {:no, {:put, {:vec, :nat, {:lit, 2}}, ^vec2, :done},
            {:get, {:vec, :nat, {:var, :n}}, :_, :done}} =
             Meet.go(
               {:put, :nat, {:nat, 3}, {:put, {:vec, :nat, {:lit, 2}}, vec2, :done}},
               {:get, :nat, :n, {:get, {:vec, :nat, {:var, :n}}, :_, :done}}
             )
  end

  test "a variable does not meet a length the other side has not received" do
    # `v` is bound at `Vec Nat n` before this side receives `n`.
    # The send is `:unknown`. Receiving `n` instantiates that length to 2.
    # The other side still expects the name. Meet refuses.
    vec = {:vec, :nat, {:var, :n}}

    sender =
      {:get, vec, :v, {:get, :nat, :n, {:put, :unknown, {:var, :v}, :done}}}

    receiver =
      {:put, vec, {:rep, {:var, :n}, {:nat, 0}}, {:put, :nat, {:nat, 2}, {:get, vec, :_, :done}}}

    assert {:error, _} = Meet.meets(sender, receiver)
    assert {:error, _} = Meet.meets(receiver, sender)
  end

  test "a bit index meets the arm of that bit" do
    server =
      {:iget, :b, {:put, :nat, {:nat, 1}, :done}, {:get, :nat, :n, :done}}

    zero = {:put, :bit, :b0, {:get, :nat, :m, :done}}
    one = {:put, :bit, :b1, {:put, :nat, {:nat, 0}, :done}}
    assert Meet.meets(server, zero) == :ok
    assert Meet.meets(zero, server) == :ok
    assert Meet.meets(server, one) == :ok
    assert Meet.meets(one, server) == :ok

    # b0's arm sends a nat. A client that also sends on that arm has no meeting.
    miss = {:put, :bit, :b0, {:put, :nat, {:nat, 1}, :done}}
    assert {:error, msg} = Meet.meets(server, miss)
    assert msg == "diverged after get b, arm b0: left: put 1; right: put 1"

    assert {:error, _} = Meet.meets(server, {:put, :unknown, {:var, :b}, :done})
    assert {:error, _} = Meet.meets(server, {:put, :nat, {:nat, 0}, :done})
    assert {:error, _} = Meet.meets(server, {:iget, :c, :done, :done})

    echo =
      {:iget, :b, {:put, :unknown, {:var, :b}, :done}, {:put, :unknown, {:var, :b}, :done}}

    ask = {:put, :bit, :b1, {:get, :bit, :c, :done}}
    assert Meet.meets(echo, ask) == :ok
    assert Meet.meets(ask, echo) == :ok

    assert {:error, msg} = Meet.meets(echo, {:put, :bit, :b1, {:get, :nat, :c, :done}})
    assert msg == "diverged after get b, arm b1: left: put b; right: get (c : Nat)"

    assert check("""
           session route := recv (b : Bit) on (send Nat end) (recv Nat end)
           session back := dual route
           conform server : route := get (b : Bit) on (put 1 done) (get (n : Nat) done)
           conform client : back := put b0 (get (m : Nat) done)
           conform client-one : back := put b1 (put 0 done)
           meet wire : server with client
           meet wire-one : server with client-one
           session echo-bit := recv (b : Bit) on (send Bit end) (send Bit end)
           session echo-back := dual echo-bit
           conform echo : echo-bit := get (b : Bit) on (put b done) (put b done)
           conform ask : echo-back := put b1 (get (c : Bit) done)
           meet echo-wire : echo with ask
           """) == :ok
  end

  test "arms that are not dualised pointwise are not the other end" do
    assert {:error, msg} =
             check("""
             session route := recv (b : Bit) on (send Nat end) (recv Nat end)
             session crossed := send (b : Bit) on (send Nat end) (recv Nat end)
             conform server : route := get (b : Bit) on (put 1 done) (get (n : Nat) done)
             conform client : crossed := put b0 (put 1 done)
             meet wire : server with client
             """)

    assert msg =~ "diverged"
    refute msg =~ "does not meet"
  end

  test "a meeting reports a bound name sent at another type" do
    assert {:error, msg} =
             check("""
             session ping := recv Nat (send Nat end)
             session back := dual ping
             conform echo : ping := get (k : Nat) (put k done)
             conform bad : back := put 0 (get Bit done)
             meet wire : echo with bad
             """)

    assert msg =~ "skipped because bad does not conform"
    refute msg =~ "diverged"
  end

  test "meet.muro checks, and emit keeps the run" do
    path = "examples/meet.muro"
    src = File.read!(path)
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    assert Muro.check_file(path) == :ok

    assert {:ok, out} = Muro.emit_file(path, MeetRun)
    assert out =~ ~r/\bdef kept\b/
    refute out =~ "wire"
    refute out =~ "GenServer"

    assert {:ok, funs} = IR.elaborate_file(path)
    assert Enum.map(funs, & &1.name) == ["kept"]
  end

  test "a meeting may name a process declared later" do
    assert check("""
           meet wire : pong with peer
           conform peer : back := put 1 (get Nat done)
           session back := dual ping
           conform pong : ping := get Nat (put 1 done)
           session ping := recv Nat (send Nat end)
           """) == :ok
  end

  test "the other end of the other end meets" do
    assert check("""
           session ping := recv Nat (send Nat end)
           session back := dual ping
           session forth := dual back
           conform again : forth := get Nat (put 1 done)
           conform peer : back := put 1 (get Nat done)
           meet wire : again with peer
           """) == :ok

    assert check("""
           session ping := recv Nat (send Nat end)
           session back := dual ping
           conform pong : ping := get Nat (put 1 done)
           conform peer : back := put 1 (get Nat done)
           meet wire : peer with pong
           """) == :ok
  end

  test "two done processes meet on end" do
    assert check("""
           session quiet := end
           conform a : quiet := done
           conform b : quiet := done
           meet close : a with b
           """) == :ok
  end

  test "a reading meets a conformance" do
    assert check("""
           session ping := recv Nat (send Nat end)
           session back := dual ping
           place home := ambient
           scheme local := fixed home
           endpoint there := back at local
           read stay peer : there at home := put 1 (get Nat done)
           conform pong : ping := get Nat (put 1 done)
           meet wire : pong with peer
           """) == :ok

    assert check("""
           session ping := recv Nat (send Nat end)
           session back := dual ping
           place home := ambient
           scheme local := fixed home
           endpoint here := ping at local
           endpoint there := back at local
           read stay pong : here at home := get Nat (put 1 done)
           read stay peer : there at home := put 1 (get Nat done)
           meet wire : pong with peer
           """) == :ok
  end

  test "protocols that are not the other end are refused before the bits" do
    assert {:error, msg} =
             check("""
             session a := send Nat end
             session b := recv Nat (send Nat end)
             conform left : a := put 0 done
             conform right : b := get Nat (put 0 done)
             meet wire : left with right
             """)

    assert msg =~ "diverged"
    refute msg =~ "does not meet"
  end

  test "one end finishing and the other abandoning is refused" do
    assert {:error, msg} =
             check("""
             session ping := recv Nat (send Nat end)
             session back := dual ping
             conform pong : ping := get Nat (put 1 done)
             conform early : back := put 0 stop
             meet wire : pong with early
             """)

    assert msg =~ "diverged after put 0: left: put 1; right: stop; protocol: send Nat end"
    refute msg =~ "expected the other end"
  end

  test "the wrong arm of an offer is refused" do
    assert {:error, msg} =
             check("""
             session choice := choose end (send Nat end)
             session offered := dual choice
             conform taker : choice := pick0 done
             conform giver : offered := cover stop (get Nat done)
             meet arm : taker with giver
             """)

    assert msg =~ "diverged after arm pick0: left: done; right: stop; protocol: end"
    refute msg =~ "expected the other end"

    assert {:error, msg} =
             check("""
             session open := send Nat end
             session closed := dual open
             conform left : open := put 0 stop
             conform right : closed := get Nat done
             meet drop : left with right
             """)

    assert msg =~ "diverged after put 0: left: stop; right: done; protocol: end"
  end

  test "a session is not a process" do
    assert {:error, msg} =
             check("""
             session ping := end
             meet wire : ping with ping
             """)

    assert msg =~ "unknown process ping"

    assert {:error, msg} =
             check("""
             session ping := end
             place home := ambient
             scheme local := fixed home
             endpoint e := ping at local
             meet wire : e with e
             """)

    assert msg =~ "unknown process e"
  end

  test "an unknown session and a dual cycle surface on the meeting" do
    assert {:error, msg} =
             check("""
             conform pong : gone := done
             meet wire : pong with pong
             """)

    assert msg =~ "unknown session gone"

    assert {:error, msg} =
             check("""
             session a := dual b
             session b := dual a
             conform left : a := done
             conform right : b := done
             meet wire : left with right
             """)

    assert msg =~ "dual cycle"
  end

  test "a meeting is not a definition" do
    assert {:error, msg} =
             check("""
             session ping := recv Nat (send Nat end)
             session back := dual ping
             conform pong : ping := get Nat (put 1 done)
             conform peer : back := put 1 (get Nat done)
             meet wire : pong with peer
             def use : run Nat := wire
             """)

    assert msg =~ "wire is a meeting, not a definition"
  end

  test "meet and with stay identifiers outside a meeting" do
    assert check("""
           def meet : run Nat := 0
           """) == :ok

    assert check("""
           def with : run Nat := 0
           """) == :ok

    assert check("""
           data Box : Type where
             meet : Box

           def z : run Box := meet
           """) == :ok
  end

  test "a meeting follows a constructor type" do
    src = """
    data Box : Type where
      c : Π (n : Nat) →
        Box

    meet wire : pong with peer
    conform pong : ping := get Nat (put 1 done)
    conform peer : back := put 1 (get Nat done)
    session back := dual ping
    session ping := recv Nat (send Nat end)
    """

    assert {:ok, book} = Parser.parse(src)
    assert Enum.any?(book, &match?(%{kind: :meet, name: "wire"}, &1))
    assert Check.check_sig(book) == :ok
  end

  test "a received field meets in both orders" do
    assert {:ok, book} = Parser.parse(File.read!("examples/field-bindings.muro"))

    for {left, right} <- [{"reply", "asker"}, {"pass", "passer"}, {"rest", "rest-peer"}] do
      l = Enum.find(book, &(&1.name == left))
      r = Enum.find(book, &(&1.name == right))
      assert Meet.meets(l.proc, r.proc, book) == :ok
      assert Meet.meets(r.proc, l.proc, book) == :ok
    end
  end

  test "a received pair or record meets in both orders" do
    assert {:ok, book} = Parser.parse(File.read!("examples/pair-bindings.muro"))

    for {left, right} <- [
          {"pair-reply", "pair-ask"},
          {"grant-reply", "grant-ask"},
          {"rec-reply", "rec-ask"}
        ] do
      l = Enum.find(book, &(&1.name == left))
      r = Enum.find(book, &(&1.name == right))
      assert Meet.meets(l.proc, r.proc, book) == :ok
      assert Meet.meets(r.proc, l.proc, book) == :ok
    end
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

defmodule Muro.MeetTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, IR, Meet, Parser}

  test "a send meets a receive of the same bit" do
    pong = {:get, :b1, {:put, :b0, :done}}
    peer = {:put, :b1, {:get, :b0, :done}}
    assert Meet.meets(pong, peer) == :ok
    assert Meet.meets(peer, pong) == :ok

    assert Meet.meets({:put, :b0, :stop}, {:get, :b0, :stop}) == :ok
    assert Meet.meets({:pick0, :done}, {:cover, :done, {:get, :b0, :done}}) == :ok
    assert Meet.meets(:done, :done) == :ok
    assert Meet.meets(:stop, :stop) == :ok
  end

  test "a bit they do not share has no derivation" do
    assert {:error, msg} = Meet.meets({:get, :b1, :done}, {:put, :b0, :done})
    assert msg == "get b1 done does not meet put b0 done"

    assert {:error, msg} = Meet.meets({:put, :b0, :done}, {:put, :b0, :done})
    assert msg == "put b0 done does not meet put b0 done"

    assert {:error, msg} = Meet.meets({:put, :b0, :stop}, {:get, :b0, :done})
    assert msg == "stop does not meet done"

    assert {:error, msg} =
             Meet.meets({:pick0, :done}, {:cover, :stop, {:get, :b0, :done}})

    assert msg == "done does not meet stop"
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
           conform peer : back := put b1 (get b0 done)
           session back := dual ping
           conform pong : ping := get b1 (put b0 done)
           session ping := recv end (send end end)
           """) == :ok
  end

  test "the other end of the other end meets" do
    assert check("""
           session ping := recv end (send end end)
           session back := dual ping
           session forth := dual back
           conform again : forth := get b1 (put b0 done)
           conform peer : back := put b1 (get b0 done)
           meet wire : again with peer
           """) == :ok

    assert check("""
           session ping := recv end (send end end)
           session back := dual ping
           conform pong : ping := get b1 (put b0 done)
           conform peer : back := put b1 (get b0 done)
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
           session ping := recv end (send end end)
           session back := dual ping
           place home := ambient
           scheme local := fixed home
           endpoint there := back at local
           read stay peer : there at home := put b1 (get b0 done)
           conform pong : ping := get b1 (put b0 done)
           meet wire : pong with peer
           """) == :ok

    assert check("""
           session ping := recv end (send end end)
           session back := dual ping
           place home := ambient
           scheme local := fixed home
           endpoint here := ping at local
           endpoint there := back at local
           read stay pong : here at home := get b1 (put b0 done)
           read stay peer : there at home := put b1 (get b0 done)
           meet wire : pong with peer
           """) == :ok
  end

  test "protocols that are not the other end are refused before the bits" do
    assert {:error, msg} =
             check("""
             session a := send end end
             session b := recv end (send end end)
             conform left : a := put b0 done
             conform right : b := get b0 done
             meet wire : left with right
             """)

    assert msg =~ "expected the other end"
    refute msg =~ "does not meet"
  end

  test "a bit the two processes do not share is refused" do
    assert {:error, msg} =
             check("""
             session ping := recv end (send end end)
             session back := dual ping
             conform pong : ping := get b1 (put b0 done)
             conform early : back := put b0 done
             meet wire : pong with early
             """)

    assert msg =~ "get b1 (put b0 done) does not meet put b0 done"
    refute msg =~ "expected the other end"
  end

  test "the wrong arm of an offer is refused" do
    assert {:error, msg} =
             check("""
             session choice := choose end (send end end)
             session offered := dual choice
             conform taker : choice := pick0 done
             conform giver : offered := cover stop (get b0 done)
             meet arm : taker with giver
             """)

    assert msg =~ "done does not meet stop"
    refute msg =~ "expected the other end"

    assert {:error, msg} =
             check("""
             session open := send end end
             session closed := dual open
             conform left : open := put b0 stop
             conform right : closed := get b0 done
             meet drop : left with right
             """)

    assert msg =~ "stop does not meet done"
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
             session ping := recv end (send end end)
             session back := dual ping
             conform pong : ping := get b1 (put b0 done)
             conform peer : back := put b1 (get b0 done)
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
    conform pong : ping := get b1 (put b0 done)
    conform peer : back := put b1 (get b0 done)
    session back := dual ping
    session ping := recv end (send end end)
    """

    assert {:ok, book} = Parser.parse(src)
    assert Enum.any?(book, &match?(%{kind: :meet, name: "wire"}, &1))
    assert Check.check_sig(book) == :ok
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

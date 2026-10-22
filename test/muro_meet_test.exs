defmodule Muro.MeetTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, IR, Meet, Parser}

  test "a send meets a receive of the same type" do
    pong = {:get, :nat, {:put, :nat, {:nat, 1}, :done}}
    peer = {:put, :nat, {:nat, 0}, {:get, :nat, :done}}
    other = {:put, :nat, {:nat, 2}, {:get, :nat, :done}}
    assert Meet.meets(pong, peer) == :ok
    assert Meet.meets(pong, other) == :ok
    assert Meet.meets(peer, pong) == :ok

    box = {:pair, :bit, {:rec, [{"x", :nat}, {"y", :nat}]}}
    here = {:tup, :b0, {:rec, [{"x", {:nat, 0}}, {"y", {:nat, 0}}]}}
    there = {:tup, :b1, {:rec, [{"x", {:nat, 1}}, {"y", {:nat, 2}}]}}
    assert Meet.meets({:put, box, here, :done}, {:get, box, :done}) == :ok
    assert Meet.meets({:put, box, there, :done}, {:get, box, :done}) == :ok

    assert Meet.meets({:put, :nat, {:nat, 0}, :stop}, {:get, :nat, :stop}) == :ok
    assert Meet.meets({:pick0, :done}, {:cover, :done, {:get, :nat, :done}}) == :ok
    assert Meet.meets(:done, :done) == :ok
    assert Meet.meets(:stop, :stop) == :ok
  end

  test "a type they do not share has no derivation" do
    assert {:error, msg} = Meet.meets({:get, :bit, :done}, {:put, :nat, {:nat, 0}, :done})
    assert msg == "get Bit done does not meet put 0 done"

    swapped = {:rec, [{"y", :nat}, {"x", :nat}]}
    point = {:rec, [{"x", :nat}, {"y", :nat}]}

    assert {:error, msg} =
             Meet.meets(
               {:put, point, {:rec, [{"x", {:nat, 0}}, {"y", {:nat, 1}}]}, :done},
               {:get, swapped, :done}
             )

    assert msg =~ "does not meet"

    assert {:error, msg} =
             Meet.meets({:put, :nat, {:nat, 0}, :done}, {:put, :nat, {:nat, 0}, :done})

    assert msg == "put 0 done does not meet put 0 done"

    assert {:error, msg} = Meet.meets({:put, :nat, {:nat, 0}, :stop}, {:get, :nat, :done})
    assert msg == "stop does not meet done"

    assert {:error, msg} =
             Meet.meets({:pick0, :done}, {:cover, :stop, {:get, :nat, :done}})

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

    assert msg =~ "expected the other end"
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

    assert msg =~ "put 1 done does not meet stop"
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

    assert msg =~ "done does not meet stop"
    refute msg =~ "expected the other end"

    assert {:error, msg} =
             check("""
             session open := send Nat end
             session closed := dual open
             conform left : open := put 0 stop
             conform right : closed := get Nat done
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

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

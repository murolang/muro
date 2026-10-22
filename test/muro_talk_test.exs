defmodule Muro.TalkTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, IR, Parser, Session, Talk}

  test "the sender's session is send, and the receiver's is recv" do
    ping = {:say, "peer", "pong", :over, {:say, "pong", "peer", :over, :over}}

    assert Talk.seen("pong", "peer", ping) == {:ok, {:recv, :end, {:send, :end, :end}}}
    assert Talk.seen("peer", "pong", ping) == {:ok, {:send, :end, {:recv, :end, :end}}}

    {:ok, there} = Talk.seen("pong", "peer", ping)
    {:ok, here} = Talk.seen("peer", "pong", ping)
    assert Session.dual(there) == here

    assert Talk.seen("log", "peer", ping) == {:error, "log has no session with peer"}
  end

  test "equal continuations give an outsider that session" do
    arm = {:say, "b", "c", :over, :over}
    both = {:say, "a", "b", arm, arm}

    assert Talk.seen("a", "b", both) == {:ok, {:send, :end, :end}}
    assert Talk.seen("b", "c", both) == {:ok, {:send, :end, :end}}
    assert Talk.seen("a", "c", both) == {:ok, :end}
  end

  test "an outsider of two different continuations has no session" do
    one = {:say, "a", "b", :over, {:say, "b", "c", :over, :over}}

    assert Talk.seen("a", "b", one) == {:ok, {:send, :end, :end}}
    assert Talk.seen("b", "c", one) == {:error, "b has no session with c"}
  end

  test "an offer is choose for the party who chooses, and branch for the other" do
    arm = {:offer, "a", "b", :over, {:say, "a", "b", :over, :over}}

    assert Talk.seen("a", "b", arm) == {:ok, {:choose, :end, {:send, :end, :end}}}
    assert Talk.seen("b", "a", arm) == {:ok, {:branch, :end, {:recv, :end, :end}}}
    assert Talk.seen("log", "a", arm) == {:error, "log has no session with a"}
  end

  test "a party does not have a session with itself on a send" do
    self = {:say, "a", "a", :over, :over}
    assert Talk.seen("a", "b", self) == {:error, "a has no session with b"}
    assert Talk.seen("a", "a", :over) == {:ok, :end}
  end

  test "talk.muro checks, and emit keeps the run" do
    path = "examples/talk.muro"
    src = File.read!(path)
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    assert Muro.check_file(path) == :ok

    assert {:ok, out} = Muro.emit_file(path, TalkRun)
    assert out =~ ~r/\bdef kept\b/
    refute out =~ "ping-exchange"
    refute out =~ "both-arms"
    refute out =~ "GenServer"

    assert {:ok, funs} = IR.elaborate_file(path)
    assert Enum.map(funs, & &1.name) == ["kept"]
  end

  test "a session and a talk may be declared later" do
    assert check("""
           conform pong : ping := get b1 (put b0 done)
           session ping := seen pong with peer in ping-exchange
           talk ping-exchange := say peer pong over (say pong peer over over)
           """) == :ok

    assert check("""
           talk outer := say a b inner inner
           session bc := seen b with c in outer
           conform relay : bc := put b0 done
           talk inner := say b c over over
           """) == :ok
  end

  test "two names of one description are the same description" do
    assert check("""
           talk left := say b c over over
           talk right := say b c over over
           talk outer := say a b left right
           session bc := seen b with c in outer
           session same := seen b with c in left
           conform relay : bc := put b0 done
           conform again : same := put b1 done
           """) == :ok
  end

  test "the other end of a seen session is that session's dual" do
    assert check("""
           talk ping-exchange := say peer pong over (say pong peer over over)
           session ping := seen pong with peer in ping-exchange
           session back := dual ping
           conform peer : back := put b1 (get b0 done)
           conform pong : ping := get b1 (put b0 done)
           meet wire : pong with peer
           """) == :ok
  end

  test "a %1 session from a description must finish, and the mark stays" do
    assert check("""
           talk ping-exchange := say peer pong over (say pong peer over over)
           session %1 ping := seen pong with peer in ping-exchange
           conform pong : ping := get b1 (put b0 done)
           session back := dual ping
           conform peer : back := put b1 (get b0 done)
           """) == :ok

    assert {:error, msg} =
             check("""
             talk ping-exchange := say peer pong over (say pong peer over over)
             session %1 ping := seen pong with peer in ping-exchange
             conform pong : ping := get b1 (put b0 stop)
             """)

    assert msg =~ "linear channel abandoned"

    assert {:error, msg} =
             check("""
             talk ping-exchange := say peer pong over (say pong peer over over)
             session %1 ping := seen pong with peer in ping-exchange
             session %0 back := dual ping
             """)

    assert msg =~ "expected %1"
  end

  test "an unknown talk is reported before a missing session" do
    assert {:error, msg} =
             check("""
             session ping := seen pong with peer in gone
             """)

    assert msg =~ "unknown talk gone"
    refute msg =~ "has no session"
  end

  test "a talk that refers to itself is a cycle" do
    assert {:error, msg} =
             check("""
             talk loop := loop
             session s := seen a with b in loop
             """)

    assert msg =~ "talk cycle"
    refute msg =~ "has no session"
    refute msg =~ "unknown talk"

    assert {:error, msg} =
             check("""
             talk a := b
             talk b := a
             """)

    assert msg =~ "talk cycle"
  end

  test "a third party on the exchange has no session, and the description checks" do
    assert check("""
           talk ping-exchange := say peer pong over (say pong peer over over)
           def kept : run Nat := 0
           """) == :ok

    assert {:error, msg} =
             check("""
             talk ping-exchange := say peer pong over (say pong peer over over)
             session log := seen log with peer in ping-exchange
             """)

    assert msg =~ "log has no session with peer"
    refute msg =~ "unknown talk"
    refute msg =~ "talk cycle"
  end

  test "one arm that differs gives the inner parties no session" do
    assert {:error, msg} =
             check("""
             talk one-arm := say a b over (say b c over over)
             session bc := seen b with c in one-arm
             """)

    assert msg =~ "b has no session with c"

    assert check("""
           talk one-arm := say a b over (say b c over over)
           session ab := seen a with b in one-arm
           conform sender : ab := put b0 done
           """) == :ok
  end

  test "a self-send is a description, and that view has no session" do
    assert check("""
           talk self := say a a over over
           def kept : run Nat := 0
           """) == :ok

    assert {:error, msg} =
             check("""
             talk self := say a a over over
             session s := seen a with b in self
             """)

    assert msg =~ "a has no session with b"
  end

  test "a talk is not a definition" do
    assert {:error, msg} =
             check("""
             talk ping-exchange := over
             def use : run Nat := ping-exchange
             """)

    assert msg =~ "ping-exchange is a talk, not a definition"
  end

  test "talk, seen, say, over, and offer stay identifiers outside the form" do
    assert check("""
           def talk : run Nat := 0
           """) == :ok

    assert check("""
           def seen : run Nat := 0
           """) == :ok

    assert check("""
           def say : run Nat := 0
           """) == :ok

    assert check("""
           def over : run Nat := 0
           """) == :ok

    assert check("""
           def offer : run Nat := 0
           """) == :ok

    assert check("""
           def with : run Nat := 0
           """) == :ok

    assert check("""
           data Box : Type where
             talk : Box

           def z : run Box := talk
           """) == :ok
  end

  test "over, say, and offer are not party names" do
    assert {:error, msg} = Parser.parse("talk bad := say over pong over over\n")
    assert msg =~ "expected a party"

    assert {:error, msg} = Parser.parse("talk bad := say peer say over over\n")
    assert msg =~ "expected a party"

    assert {:error, msg} = Parser.parse("talk bad := offer offer b over over\n")
    assert msg =~ "expected a party"
  end

  test "a talk follows a constructor type" do
    src = """
    data Box : Type where
      c : Π (n : Nat) →
        Box

    talk ping-exchange := say peer pong over (say pong peer over over)
    session ping := seen pong with peer in ping-exchange
    conform pong : ping := get b1 (put b0 done)
    """

    assert {:ok, book} = Parser.parse(src)
    assert Enum.any?(book, &match?(%{kind: :talk, name: "ping-exchange"}, &1))
    assert Check.check_sig(book) == :ok
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

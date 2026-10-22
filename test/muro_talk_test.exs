defmodule Muro.TalkTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, IR, Parser, Session, Talk}

  test "the sender's session is send, and the receiver's is recv" do
    ping = {:say, "peer", "pong", :nat, {:say, "pong", "peer", :nat, :over}}

    assert Talk.seen("pong", "peer", ping) == {:ok, {:recv, :nat, {:send, :nat, :end}}}
    assert Talk.seen("peer", "pong", ping) == {:ok, {:send, :nat, {:recv, :nat, :end}}}

    {:ok, there} = Talk.seen("pong", "peer", ping)
    {:ok, here} = Talk.seen("peer", "pong", ping)
    assert Session.dual(there) == here

    assert Talk.seen("log", "peer", ping) == {:ok, :end}
  end

  test "equal arms of an offer give an outsider that session" do
    arm = {:say, "b", "c", :nat, :over}
    both = {:offer, "a", "b", arm, arm}

    assert Talk.seen("a", "b", both) == {:ok, {:choose, :end, :end}}
    assert Talk.seen("b", "c", both) == {:ok, {:send, :nat, :end}}
    assert Talk.seen("a", "c", both) == {:ok, :end}
  end

  test "an outsider of two different arms has no session" do
    one = {:offer, "a", "b", :over, {:say, "b", "c", :nat, :over}}

    assert Talk.seen("a", "b", one) == {:ok, {:choose, :end, :end}}
    assert Talk.seen("b", "c", one) == {:error, "b has no session with c"}
  end

  test "an offer is choose for the party who chooses, and branch for the other" do
    arm = {:offer, "a", "b", :over, {:say, "a", "b", :nat, :over}}

    assert Talk.seen("a", "b", arm) == {:ok, {:choose, :end, {:send, :nat, :end}}}
    assert Talk.seen("b", "a", arm) == {:ok, {:branch, :end, {:recv, :nat, :end}}}
    assert Talk.seen("log", "a", arm) == {:error, "log has no session with a"}
  end

  test "a party does not have a session with itself on a send" do
    self = {:say, "a", "a", :nat, :over}
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
           conform pong : ping := get Nat (put 1 done)
           session ping := seen pong with peer in ping-exchange
           talk ping-exchange := say peer pong Nat (say pong peer Nat over)
           """) == :ok

    assert check("""
           talk outer := say a b Nat inner
           session bc := seen b with c in outer
           conform relay : bc := put 0 done
           talk inner := say b c Nat over
           """) == :ok
  end

  test "two names of one description are the same description" do
    assert check("""
           talk left := say b c Nat over
           talk right := say b c Nat over
           talk outer := offer a b left right
           session bc := seen b with c in outer
           session same := seen b with c in left
           conform relay : bc := put 0 done
           conform again : same := put 1 done
           """) == :ok
  end

  test "the other end of a seen session is that session's dual" do
    assert check("""
           talk ping-exchange := say peer pong Nat (say pong peer Nat over)
           session ping := seen pong with peer in ping-exchange
           session back := dual ping
           conform peer : back := put 1 (get Nat done)
           conform pong : ping := get Nat (put 1 done)
           meet wire : pong with peer
           """) == :ok
  end

  test "a %1 session from a description must finish, and the mark stays" do
    assert check("""
           talk ping-exchange := say peer pong Nat (say pong peer Nat over)
           session %1 ping := seen pong with peer in ping-exchange
           conform pong : ping := get Nat (put 1 done)
           session back := dual ping
           conform peer : back := put 1 (get Nat done)
           """) == :ok

    assert {:error, msg} =
             check("""
             talk ping-exchange := say peer pong Nat (say pong peer Nat over)
             session %1 ping := seen pong with peer in ping-exchange
             conform pong : ping := get Nat (put 0 stop)
             """)

    assert msg =~ "linear channel abandoned"

    assert {:error, msg} =
             check("""
             talk ping-exchange := say peer pong Nat (say pong peer Nat over)
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

  test "a party off a say has the continuation, which here is end" do
    assert check("""
           talk ping-exchange := say peer pong Nat (say pong peer Nat over)
           session log := seen log with peer in ping-exchange
           conform quiet : log := done
           """) == :ok
  end

  test "a party off an offer whose arms differ has no session" do
    assert {:error, msg} =
             check("""
             talk split := offer peer pong over (say pong peer Nat over)
             session log := seen log with peer in split
             """)

    assert msg =~ "log has no session with peer"
    refute msg =~ "unknown talk"
    refute msg =~ "talk cycle"
  end

  test "one arm that differs gives the inner parties no session" do
    assert {:error, msg} =
             check("""
             talk one-arm := offer a b over (say b c Nat over)
             session bc := seen b with c in one-arm
             """)

    assert msg =~ "b has no session with c"

    assert check("""
           talk one-arm := offer a b over (say b c Nat over)
           session ab := seen a with b in one-arm
           conform sender : ab := pick0 done
           """) == :ok
  end

  test "a self-send is a description, and that view has no session" do
    assert check("""
           talk self := say a a Nat over
           def kept : run Nat := 0
           """) == :ok

    assert {:error, msg} =
             check("""
             talk self := say a a Nat over
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

    talk ping-exchange := say peer pong Nat (say pong peer Nat over)
    session ping := seen pong with peer in ping-exchange
    conform pong : ping := get Nat (put 1 done)
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

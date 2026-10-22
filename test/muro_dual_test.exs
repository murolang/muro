defmodule Muro.DualTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, IR, Parser, Session}

  test "dual swaps send with recv and choose with branch" do
    ping = {:recv, :end, {:send, :end, :end}}
    assert Session.dual(ping) == {:send, :end, {:recv, :end, :end}}
    assert Session.dual(Session.dual(ping)) == ping

    choice = {:choose, :end, {:send, :end, :end}}
    assert Session.dual(choice) == {:branch, :end, {:recv, :end, :end}}
    assert Session.dual(Session.dual(choice)) == choice
  end

  test "dual.muro checks, and emit keeps the run" do
    path = "examples/dual.muro"
    src = File.read!(path)
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    assert Muro.check_file(path) == :ok

    assert {:ok, out} = Muro.emit_file(path, DualRun)
    assert out =~ ~r/\bdef kept\b/
    refute out =~ "peer"
    refute out =~ "dual"
    refute out =~ "GenServer"

    assert {:ok, funs} = IR.elaborate_file(path)
    assert Enum.map(funs, & &1.name) == ["kept"]
  end

  test "a dual may name a session declared later" do
    assert check("""
           conform peer : back := put b1 (get b0 done)
           session back := dual ping
           session ping := recv end (send end end)
           """) == :ok
  end

  test "the other end of the other end is the same session" do
    assert check("""
           session ping := recv end (send end end)
           session back := dual ping
           session forth := dual back
           conform again : forth := get b1 (put b0 done)
           """) == :ok
  end

  test "an omitted mark is the named session's mark" do
    assert check("""
           session %1 ping := recv end (send end end)
           session back := dual ping
           conform peer : back := put b1 (get b0 done)
           """) == :ok

    assert {:error, msg} =
             check("""
             session %1 ping := recv end (send end end)
             session back := dual ping
             conform stopped : back := stop
             """)

    assert msg =~ "linear channel abandoned"
  end

  test "a written mark agrees with the named session" do
    assert check("""
           session %1 ping := recv end (send end end)
           session %1 back := dual ping
           conform peer : back := put b1 (get b0 done)
           """) == :ok

    assert {:error, msg} =
             check("""
             session ping := recv end (send end end)
             session %1 back := dual ping
             """)

    assert msg =~ "expected %0"

    assert {:error, msg} =
             check("""
             session %1 ping := recv end (send end end)
             session %0 back := dual ping
             """)

    assert msg =~ "expected %1"
  end

  test "a bit the other end does not name is refused" do
    assert {:error, msg} =
             check("""
             session ping := recv end (send end end)
             session back := dual ping
             conform early : back := put b1 done
             """)

    assert msg =~ "does not conform"
  end

  test "choosing swaps with offering" do
    assert check("""
           session choice := choose end (send end end)
           session offered := dual choice
           conform either : offered := cover done (get b0 done)
           """) == :ok

    assert {:error, msg} =
             check("""
             session choice := choose end (send end end)
             session offered := dual choice
             conform early : offered := pick0 done
             """)

    assert msg =~ "does not conform"
  end

  test "a reading takes the other end's protocol and mark" do
    assert check("""
           session %1 ping := recv end (send end end)
           session back := dual ping
           place home := ambient
           scheme local := fixed home
           endpoint e := back at local
           read stay peer : e at home := put b1 (get b0 done)
           """) == :ok

    assert {:error, msg} =
             check("""
             session %1 ping := recv end (send end end)
             session back := dual ping
             place home := ambient
             scheme local := fixed home
             endpoint e := back at local
             read stay stopped : e at home := stop
             """)

    assert msg =~ "linear channel abandoned"
  end

  test "an unknown session and a dual cycle are refused" do
    assert {:error, msg} =
             check("""
             session back := dual gone
             """)

    assert msg =~ "unknown session gone"

    assert {:error, msg} =
             check("""
             session a := dual b
             session b := dual a
             """)

    assert msg =~ "dual cycle"

    assert {:error, msg} =
             check("""
             session a := dual a
             """)

    assert msg =~ "dual cycle"
  end

  test "dual stays an identifier outside a session" do
    assert check("""
           def dual : run Nat := 0
           """) == :ok

    assert check("""
           data Box : Type where
             dual : Box

           def z : run Box := dual
           """) == :ok
  end

  test "a dual session follows a constructor type" do
    assert check("""
           data Box : Type where
             c : Π (n : Nat) →
               Box

           session back := dual ping
           session ping := recv end (send end end)
           """) == :ok
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

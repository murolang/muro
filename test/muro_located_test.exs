defmodule Muro.LocatedTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, IR, Parser}

  test "located.muro checks, and emit keeps the run" do
    path = "examples/located.muro"
    src = File.read!(path)
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    assert Muro.check_file(path) == :ok

    assert {:ok, out} = Muro.emit_file(path, LocatedRun)
    assert out =~ ~r/\bdef kept\b/
    refute out =~ "pong"
    refute out =~ "endpoint"
    refute out =~ "GenServer"

    assert {:ok, funs} = IR.elaborate_file(path)
    assert Enum.map(funs, & &1.name) == ["kept"]
  end

  test "a reading may name an endpoint declared later" do
    assert check("""
           read stay pong : ping-home at home := get Nat (put 1 done)
           endpoint ping-home := ping at local
           session ping := recv Nat (send Nat end)
           scheme local := fixed home
           place home := ambient
           """) == :ok
  end

  test "an endpoint follows a constructor type" do
    assert check("""
           data Box : Type where
             c : Π (n : Nat) →
               Box

           session ping := recv Nat (send Nat end)
           place home := ambient
           scheme local := fixed home
           endpoint ping-home := ping at local
           read stay pong : ping-home at home := get Nat (put 1 done)
           """) == :ok
  end

  test "endpoint, read, and at stay identifiers" do
    assert check("""
           def endpoint : run Nat := 0
           def read : run Nat := 0
           def at : run Nat := 0
           """) == :ok
  end

  test "a constructor may be named endpoint" do
    assert check("""
           data Box : Type where
             endpoint : Box

           def z : run Box := endpoint
           """) == :ok
  end

  test "a polymorphic session stays, and a fixed one crosses once" do
    assert check("""
           #{base()}
           read stay pong : ping-home at home := get Nat (put 1 done)
           read cross pong-away : ping-home at away := get Nat (put 1 done)
           read stay here : ping-poly at away := get Nat (put 1 done)
           """) == :ok
  end

  test "a session that must finish may finish at another place" do
    assert check("""
           #{base()}
           session %1 ping-done := recv Nat (send Nat end)
           endpoint done-home := ping-done at local
           read cross pong-done : done-home at away := get Nat (put 1 done)
           """) == :ok
  end

  test "abandonment is allowed for an unmarked session, and the reading still crosses" do
    assert check("""
           #{base()}
           session send-then-send := send Nat (send Nat end)
           endpoint open-home := send-then-send at local
           read cross left-open : open-home at away := put 0 stop
           """) == :ok
  end

  test "a stay where the reading crosses is refused" do
    assert {:error, msg} =
             check("""
             #{base()}
             read stay pong : ping-home at away := get Nat (put 1 done)
             """)

    assert msg =~ "expected cross"
  end

  test "a cross where the reading stays is refused" do
    assert {:error, msg} =
             check("""
             #{base()}
             read cross pong : ping-home at home := get Nat (put 1 done)
             """)

    assert msg =~ "expected stay"
  end

  test "a cross of a polymorphic session is refused" do
    assert {:error, msg} =
             check("""
             #{base()}
             read cross pong : ping-poly at away := get Nat (put 1 done)
             """)

    assert msg =~ "expected stay"
  end

  test "a wrong bit is refused at the far place" do
    assert {:error, msg} =
             check("""
             #{base()}
             read cross early : ping-home at away := get Bit (put b0 done)
             """)

    assert msg =~ "does not conform"
    refute msg =~ "expected"
  end

  test "a session that must finish refuses abandonment at home and away" do
    src = """
    #{base()}
    session %1 ping-done := recv Nat (send Nat end)
    endpoint done-home := ping-done at local
    """

    assert {:error, home} =
             check("""
             #{src}
             read stay stopped : done-home at home := stop
             """)

    assert {:error, away} =
             check("""
             #{src}
             read cross stopped : done-home at away := stop
             """)

    assert home =~ "linear channel abandoned"
    assert away =~ "linear channel abandoned"
  end

  test "an unknown endpoint is refused" do
    assert {:error, msg} =
             check("""
             #{base()}
             read stay pong : gone at home := get Nat (put 1 done)
             """)

    assert msg =~ "unknown endpoint gone"
  end

  test "an endpoint names a session and a scheme" do
    assert {:error, session} =
             check("""
             #{base()}
             endpoint gone := missing at local
             """)

    assert {:error, scheme} =
             check("""
             #{base()}
             endpoint gone := ping at missing
             """)

    assert session =~ "unknown session missing"
    assert scheme =~ "unknown scheme missing"
  end

  test "an endpoint name is not a definition" do
    assert {:error, msg} =
             check("""
             #{base()}
             def z : run Nat := ping-home
             """)

    assert msg =~ "ping-home is an endpoint, not a definition"
  end

  test "a reading name is not a definition" do
    assert {:error, msg} =
             check("""
             #{base()}
             read stay pong : ping-home at home := get Nat (put 1 done)
             def z : run Nat := pong
             """)

    assert msg =~ "pong is a reading, not a definition"
  end

  test "an endpoint name is declared once" do
    assert {:error, msg} =
             check("""
             #{base()}
             endpoint ping-home := ping at local
             def ping-home : run Nat := 0
             """)

    assert msg =~ "duplicate name ping-home"
  end

  defp base do
    """
    session ping := recv Nat (send Nat end)
    place home := ambient
    place away := node a
    scheme local := fixed home
    scheme poly := any
    endpoint ping-home := ping at local
    endpoint ping-poly := ping at poly
    """
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

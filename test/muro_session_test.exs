defmodule Muro.SessionTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, Emit, IR, Parser}

  test "ping.muro checks, and emit keeps no session" do
    path = "examples/ping.muro"
    src = File.read!(path)
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    assert Muro.check_file(path) == :ok

    assert {:ok, out} = Muro.emit_file(path, Ping)
    refute out =~ "pong"
    refute out =~ "put"
    refute out =~ "session"

    assert {:ok, []} = IR.elaborate_file(path)
  end

  test "a conform may name a session declared later" do
    assert check("""
           conform pong : ping := get b1 (put b0 done)
           session ping := recv end (send end end)
           """) == :ok
  end

  test "a session follows a data declaration" do
    assert check("""
           data Flag : Type where
             yes : Flag

           session closed := end
           conform finished : closed := done
           """) == :ok
  end

  test "end and send stay identifiers outside a session" do
    assert check("""
           def end : run Nat := 0
           def send : run Nat := 0
           """) == :ok
  end

  test "a run beside a session is what emit keeps" do
    src = """
    session ping := recv end (send end end)
    conform pong : ping := get b1 (put b0 done)
    def z : run Nat := 0
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    out = Emit.emit_module(PingRun, book)
    assert out =~ ~r/\bdef z\b/
    refute out =~ "pong"
    refute out =~ "put"
  end

  test "a second send is refused" do
    assert {:error, msg} =
             check("""
             session ping := recv end (send end end)
             conform early-send : ping := get b0 (put b0 done)
             """)

    assert msg =~ "put b0 done does not conform to end"
  end

  test "two sends where the continuation is end are refused" do
    assert {:error, msg} =
             check("""
             session once := send end end
             conform twice : once := put b0 (put b1 done)
             """)

    assert msg =~ "put b1 done does not conform to end"
  end

  test "a send where the protocol says receive is refused" do
    assert {:error, msg} =
             check("""
             session ping := recv end end
             conform swapped : ping := put b0 done
             """)

    assert msg =~ "put b0 done does not conform to recv end end"
  end

  test "an unknown session is refused" do
    assert {:error, msg} =
             check("""
             conform pong : gone := done
             """)

    assert msg =~ "unknown session gone"
  end

  test "a session name is not a definition" do
    assert {:error, msg} =
             check("""
             session ping := end
             def z : run Nat := ping
             """)

    assert msg =~ "ping is a session, not a definition"
  end

  test "a session name is declared once" do
    assert {:error, msg} =
             check("""
             session ping := end
             def ping : run Nat := 0
             """)

    assert msg =~ "duplicate name ping"
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

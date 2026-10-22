defmodule Muro.SeatedTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, IR, Parser}

  test "seated.muro checks, and emit keeps the run" do
    path = "examples/seated.muro"
    src = File.read!(path)
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    assert Muro.check_file(path) == :ok

    assert {:ok, out} = Muro.emit_file(path, SeatedRun)
    assert out =~ ~r/\bdef kept\b/
    refute out =~ "pong-home"
    refute out =~ "stay-here"
    refute out =~ "GenServer"
    refute out =~ "b0"
    refute out =~ "b1"

    assert {:ok, funs} = IR.elaborate_file(path)
    assert Enum.map(funs, & &1.name) == ["kept"]
  end

  test "a seat and a link may be declared later" do
    assert check("""
           link stay-here : stay pong-home with peer-home in ping-exchange
           seat peer-home : peer at home in ping-exchange
           seat pong-home : pong at home in ping-exchange
           talk ping-exchange := say peer pong over (say pong peer over over)
           place home := node a
           """) == :ok
  end

  test "the same node name is the same place" do
    assert check("""
           place home := node a
           place also := node a
           talk ping-exchange := say peer pong over (say pong peer over over)
           seat pong-home : pong at home in ping-exchange
           seat peer-also : peer at also in ping-exchange
           link stay-here : stay pong-home with peer-also in ping-exchange
           """) == :ok
  end

  test "ambient stays, and ambient to a node crosses once" do
    assert check("""
           #{base()}
           place here := ambient
           seat pong-here : pong at here in ping-exchange
           seat peer-here : peer at here in ping-exchange
           link local : stay pong-here with peer-here in ping-exchange
           link out : cross pong-here with peer-away in ping-exchange
           """) == :ok
  end

  test "a party with no session may sit, and the link has no boundary" do
    assert check("""
           #{base()}
           seat log-home : log at home in ping-exchange
           def kept : run Nat := 0
           """) == :ok

    assert {:error, msg} =
             check("""
             #{base()}
             seat log-home : log at home in ping-exchange
             link go : cross log-home with peer-away in ping-exchange
             """)

    assert msg =~ "log has no session with peer"
    refute msg =~ "expected cross"
    refute msg =~ "expected stay"
  end

  test "a stated mark that disagrees is refused after the session" do
    assert {:error, msg} =
             check("""
             #{base()}
             link bad : cross pong-home with peer-home in ping-exchange
             """)

    assert msg =~ "expected stay"
    refute msg =~ "has no session"

    assert {:error, msg} =
             check("""
             #{base()}
             link bad : stay pong-home with peer-away in ping-exchange
             """)

    assert msg =~ "expected cross"
    refute msg =~ "has no session"
  end

  test "two descriptions are refused before the session" do
    assert {:error, msg} =
             check("""
             #{base()}
             talk quiet := over
             seat pong-quiet : pong at home in quiet
             link bad : stay pong-home with pong-quiet in ping-exchange
             """)

    assert msg =~ "expected one description"
    refute msg =~ "has no session"
    refute msg =~ "expected stay"
  end

  test "the empty description seats any two parties at end" do
    assert check("""
           place home := ambient
           talk quiet := over
           seat a-home : a at home in quiet
           seat b-home : b at home in quiet
           link close : stay a-home with b-home in quiet
           """) == :ok
  end

  test "an unknown talk is reported before an unknown place" do
    assert {:error, msg} =
             check("""
             seat pong-home : pong at gone in missing
             """)

    assert msg =~ "unknown talk missing"
    refute msg =~ "unknown place"
  end

  test "a talk that refers to itself is a cycle on the seat" do
    assert {:error, msg} =
             check("""
             place home := node a
             talk loop := loop
             seat pong-home : pong at home in loop
             link bad : stay pong-home with pong-home in loop
             """)

    assert msg =~ "talk cycle"
    refute msg =~ "has no session"
  end

  test "one arm that differs gives the inner parties no boundary" do
    assert {:error, msg} =
             check("""
             place home := node a
             talk one-arm := say a b over (say b c over over)
             seat b-home : b at home in one-arm
             seat c-home : c at home in one-arm
             link bad : stay b-home with c-home in one-arm
             """)

    assert msg =~ "b has no session with c"

    assert check("""
           place home := node a
           talk one-arm := say a b over (say b c over over)
           seat a-home : a at home in one-arm
           seat b-home : b at home in one-arm
           link ok : stay a-home with b-home in one-arm
           """) == :ok
  end

  test "a seat and a link are not definitions" do
    assert {:error, msg} =
             check("""
             #{base()}
             def use : run Nat := pong-home
             """)

    assert msg =~ "pong-home is a seat, not a definition"

    assert {:error, msg} =
             check("""
             #{base()}
             def use : run Nat := stay-here
             """)

    assert msg =~ "stay-here is a link, not a definition"
  end

  test "seat, link, and at stay identifiers outside the form" do
    assert check("""
           def seat : run Nat := 0
           """) == :ok

    assert check("""
           def link : run Nat := 0
           """) == :ok

    assert check("""
           def at : run Nat := 0
           """) == :ok

    assert check("""
           data Box : Type where
             seat : Box
             link : Box

           def z : run Box := seat
           def w : run Box := link
           """) == :ok
  end

  test "over, say, and offer are not party names" do
    assert {:error, msg} = Parser.parse("seat bad : over at home in t\n")
    assert msg =~ "expected a party"

    assert {:error, msg} = Parser.parse("seat bad : say at home in t\n")
    assert msg =~ "expected a party"

    assert {:error, msg} = Parser.parse("seat bad : offer at home in t\n")
    assert msg =~ "expected a party"
  end

  test "a seat follows a constructor type" do
    src = """
    data Box : Type where
      c : Π (n : Nat) →
        Box

    place home := node a
    talk ping-exchange := say peer pong over (say pong peer over over)
    seat pong-home : pong at home in ping-exchange
    seat peer-home : peer at home in ping-exchange
    link stay-here : stay pong-home with peer-home in ping-exchange
    """

    assert {:ok, book} = Parser.parse(src)
    assert Enum.any?(book, &match?(%{kind: :seat, name: "pong-home"}, &1))
    assert Enum.any?(book, &match?(%{kind: :link, name: "stay-here"}, &1))
    assert Check.check_sig(book) == :ok
  end

  defp base do
    """
    place home := node a
    place away := node b
    talk ping-exchange := say peer pong over (say pong peer over over)
    seat pong-home : pong at home in ping-exchange
    seat peer-home : peer at home in ping-exchange
    seat peer-away : peer at away in ping-exchange
    link stay-here : stay pong-home with peer-home in ping-exchange
    """
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

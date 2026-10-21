defmodule Muro.PlaceTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, Emit, IR, Parser, Place}

  test "place.muro checks, and emit keeps the run" do
    path = "examples/place.muro"
    src = File.read!(path)
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    assert Muro.check_file(path) == :ok

    assert {:ok, out} = Muro.emit_file(path, PlaceRun)
    assert out =~ ~r/\bdef kept\b/
    refute out =~ "ambient"
    refute out =~ "cross"
    refute out =~ "home"

    assert {:ok, funs} = IR.elaborate_file(path)
    assert Enum.map(funs, & &1.name) == ["kept"]
  end

  test "decide stays at one place and crosses once to another" do
    assert Place.decide(:ambient, :ambient) == :stay
    assert Place.decide({:node, "a"}, {:node, "a"}) == :stay
    assert Place.decide(:ambient, {:node, "a"}) == :cross
    assert Place.bounds(Place.decide({:node, "a"}, {:node, "b"})) == :one
    assert Place.conform(:any, {:node, "a"}) == :stay
    assert Place.bounds(Place.conform(:any, :ambient)) == :none
    assert Place.conform({:fixed, :ambient}, :ambient) == :stay
    assert Place.bounds(Place.conform({:fixed, :ambient}, {:node, "a"})) == :one
    assert Place.ground(:any, {:node, "a"}) == {:node, "a"}
    assert Place.ground({:fixed, :ambient}, {:node, "a"}) == :ambient
  end

  test "a move may name a place declared later" do
    assert check("""
           move stay local : home
           scheme local := fixed home
           place home := ambient
           """) == :ok
  end

  test "a place follows a constructor type" do
    assert check("""
           data Box : Type where
             c : Π (n : Nat) →
               Box

           place home := ambient
           scheme local := fixed home
           move stay local : home
           """) == :ok
  end

  test "place, scheme, move, and the marks stay identifiers" do
    assert check("""
           def place : run Nat := 0
           def scheme : run Nat := 0
           def move : run Nat := 0
           def ambient : run Nat := 0
           def node : run Nat := 0
           def any : run Nat := 0
           def fixed : run Nat := 0
           def stay : run Nat := 0
           def cross : run Nat := 0
           """) == :ok
  end

  test "a constructor may be named place" do
    assert check("""
           data Box : Type where
             place : Box

           def z : run Box := place
           """) == :ok
  end

  test "a fixed place stays at itself and crosses once away" do
    assert check("""
           place home := ambient
           place away := node a
           scheme local := fixed home
           move stay local : home
           move cross local : away
           """) == :ok
  end

  test "a polymorphic scheme stays where it is read" do
    assert check("""
           place home := ambient
           place away := node a
           scheme poly := any
           move stay poly : home
           move stay poly : away
           """) == :ok
  end

  test "the same node read under two names stays" do
    assert check("""
           place left := node a
           place right := node a
           scheme from := fixed left
           move stay from : right
           """) == :ok
  end

  test "two ambient names are one place" do
    assert check("""
           place home := ambient
           place here := ambient
           scheme local := fixed home
           move stay local : here
           """) == :ok
  end

  test "a node name is a string" do
    assert check("""
           place home := ambient
           place away := node home
           scheme local := fixed home
           move cross local : away
           """) == :ok
  end

  test "stay is refused when the reading crosses" do
    assert {:error, msg} =
             check("""
             place home := ambient
             place away := node a
             scheme local := fixed home
             move stay local : away
             """)

    assert msg =~ "expected cross"
  end

  test "cross is refused when the reading stays" do
    assert {:error, msg} =
             check("""
             place home := ambient
             scheme local := fixed home
             move cross local : home
             """)

    assert msg =~ "expected stay"
  end

  test "cross is refused for a polymorphic scheme" do
    assert {:error, msg} =
             check("""
             place away := node a
             scheme poly := any
             move cross poly : away
             """)

    assert msg =~ "expected stay"
  end

  test "an unknown place is refused" do
    assert {:error, msg} =
             check("""
             scheme local := fixed gone
             """)

    assert msg =~ "unknown place gone"
  end

  test "an unknown scheme is refused" do
    assert {:error, msg} =
             check("""
             place home := ambient
             move stay gone : home
             """)

    assert msg =~ "unknown scheme gone"
  end

  test "a place name is not a definition" do
    assert {:error, msg} =
             check("""
             place home := ambient
             def z : run Nat := home
             """)

    assert msg =~ "home is a place, not a definition"
  end

  test "a scheme name is not a definition" do
    assert {:error, msg} =
             check("""
             place home := ambient
             scheme local := fixed home
             def z : run Nat := local
             """)

    assert msg =~ "local is a scheme, not a definition"
  end

  test "a place name is declared once" do
    assert {:error, msg} =
             check("""
             place home := ambient
             def home : run Nat := 0
             """)

    assert msg =~ "duplicate name home"
  end

  test "a place expects ambient or node" do
    assert {:error, msg} = Parser.parse("place home := here\n")
    assert msg =~ "expected ambient or node"
  end

  test "a scheme expects any or fixed" do
    assert {:error, msg} = Parser.parse("scheme local := home\n")
    assert msg =~ "expected any or fixed"
  end

  test "a move expects stay or cross" do
    assert {:error, msg} = Parser.parse("move local : home\n")
    assert msg =~ "expected stay or cross"
  end

  test "emit walks a book that holds a move" do
    src = """
    place home := ambient
    scheme local := fixed home
    move stay local : home
    def id : run Π (n : Nat) → Nat :=
      λ (n : Nat) → n
    def z : run Nat := id 0
    """

    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok
    out = Emit.emit_module(Placed, book)
    assert out =~ ~r/\bdef z\b/
    assert out =~ ~r/\bdef id\b/
    refute out =~ "ambient"
    refute out =~ "cross"
  end

  defp check(src) do
    assert {:ok, book} = Parser.parse(src)
    Check.check_sig(book)
  end
end

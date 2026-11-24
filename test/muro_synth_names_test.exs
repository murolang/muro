defmodule Muro.Synth.NamesTest do
  use ExUnit.Case, async: true

  alias Muro.Synth.Names

  test "fresh keeps the preferred spelling when it is free" do
    assert Names.fresh("c", MapSet.new()) == "c"
  end

  test "fresh skips a reserved name and a prefix-sharing suffix" do
    taken = Names.take(MapSet.new(), ["c", "c-2"])
    assert Names.fresh("c", taken) == "c-3"
  end

  test "fresh does not emit a reserved word" do
    assert Names.fresh("suc", MapSet.new()) == "suc-2"
    assert Names.fresh("plus", MapSet.new()) == "plus-2"
    assert Names.fresh("match", MapSet.new()) == "match-2"
  end

  test "table allocates distinct binders against a reserved set" do
    taken = Names.take(MapSet.new(), ["c", "x", "y", "z", "s", "t"])
    {binders, taken} = Names.table(taken)
    assert binders["c"] == "c-2"
    assert binders["x"] == "x-2"
    assert binders["y"] == "y-2"
    assert binders["z"] == "z-2"
    assert binders["s"] == "s-2"
    assert binders["t"] == "t-2"
    assert Names.free?(binders) == false
    assert MapSet.member?(taken, "c-2")
  end

  test "reserved collects constructors of a loaded book" do
    book = [
      %{kind: :data, name: "Action", ctors: [%{name: "c"}, %{name: "x"}]},
      %{kind: :data, name: "State", ctors: [%{name: "s"}]},
      %{name: "step"}
    ]

    taken = Names.reserved(book)
    assert Names.occupied?("c", taken)
    assert Names.occupied?("x", taken)
    assert Names.occupied?("s", taken)
    assert Names.occupied?("step", taken)
    refute Names.occupied?("go", taken)
  end

  test "current keeps a table entry and freshens an unknown reserved base" do
    taken = Names.take(MapSet.new(), ["c", "ha"])
    {binders, taken} = Names.table(taken)

    Names.with_binders(binders, taken, fn ->
      assert Names.current("c") == "c-2"
      assert Names.current("ha") == "ha-2"
      assert Names.current("ha") == "ha-2"
    end)
  end

  test "standard bases include the list-equality binders i and u" do
    assert "i" in Names.standard_bases()
    assert "u" in Names.standard_bases()
  end

  test "table freshens i and u when they are reserved" do
    taken = Names.take(MapSet.new(), ["i", "u"])
    {binders, taken} = Names.table(taken)
    assert binders["i"] == "i-2"
    assert binders["u"] == "u-2"
    assert Names.free?(binders) == false
    assert MapSet.member?(taken, "i-2")
  end

  test "current freshens nested k0 and rk0 against the reserved set" do
    taken = Names.take(MapSet.new(), ["k0", "rk0", "k0-2"])
    {binders, taken} = Names.table(taken)

    Names.with_binders(binders, taken, fn ->
      assert Names.current("k0") == "k0-3"
      assert Names.current("rk0") == "rk0-2"
      assert Names.current("k0") == "k0-3"
    end)
  end

  test "with_binders/2 is refused when the reserved set is absent" do
    assert_raise ArgumentError, ~r/with_binders\/2/, fn ->
      Names.with_binders(%{"c" => "c"}, fn -> Names.current("c") end)
    end
  end
end

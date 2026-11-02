defmodule Muro.EmitNameTest do
  use ExUnit.Case, async: true

  alias Muro.Emit.Name

  @forbidden MapSet.new(~w(
    type fn match if else true false bool int void return struct enum
    read write close malloc free error std
  ))

  @sources ~w(
    a-b a_b a_b_2 a'b a__b muro_step muro-step muro_step_2 muro__step_0
    muro__zero muro__to_u64 type Type true false u8 u64 std n a0 fst step
    Nat nat foo Foo foo_bar foo-bar zz zu z Z _ _x read and fn bool
    muro_env_0 muro_blk0 step0 step2
  )

  test "spell then claim is injective, and the two spaces stay apart" do
    for names <- [@sources, Enum.reverse(@sources)] do
      {claimed, _} =
        Enum.reduce(names, {%{}, MapSet.new()}, fn name, {map, used} ->
          {spelled, used} = Name.claim(Name.spell(name, @forbidden, &width?/1), used)
          {Map.put(map, name, spelled), used}
        end)

      assert map_size(claimed) == length(names)
      assert length(Enum.uniq(Map.values(claimed))) == length(names)

      Enum.each(Map.values(claimed), fn spelled ->
        refute Name.generated?(spelled)
        refute String.contains?(spelled, "__")
      end)
    end

    assert Name.spell("a-b", @forbidden) == "azdb"
    assert Name.spell("a_b", @forbidden) == "azub"
    assert Name.spell("a_b_2", @forbidden) == "azubzu2"
    assert Name.spell("muro_step", @forbidden) == "murozustep"
    assert Name.spell("muro-step", @forbidden) == "murozdstep"
    assert Name.spell("muro__step_0", @forbidden) == "murozuzustepzu0"
    assert Name.spell("u64", @forbidden, &width?/1) == "u64_k"
    assert Name.spell("type", @forbidden) == "type_k"

    generated =
      ["zero", "step", "to_u64", "Nat", "a", "f", "allocator", "field_fst"]
      |> Enum.map(&Name.gen/1)

    generated = generated ++ [Name.gen("step", 0), Name.gen("step", 2), Name.gen("env", 0)]

    Enum.each(generated, fn name ->
      assert Name.generated?(name)
      assert String.contains?(name, "__")
    end)

    {suffixed, _} =
      Enum.reduce(generated, {[], MapSet.new(generated)}, fn name, {acc, used} ->
        {next, used} = Name.claim(name, used)
        {[next | acc], used}
      end)

    Enum.each(suffixed, fn name ->
      assert Name.generated?(name)
      refute name in @sources
    end)

    source_ids = Enum.map(@sources, fn name -> Name.spell(name, @forbidden, &width?/1) end)
    assert MapSet.disjoint?(MapSet.new(source_ids), MapSet.new(generated))
    assert "muro__step_2" in generated
    refute "muro__step_2" in source_ids
  end

  test "a binder is claimed against every visible name, including types" do
    scope = Name.open(MapSet.new(["Box", "mk"]))
    {param, scope} = Name.bind("Box", scope)
    assert param == "Box_2"
    {again, scope} = Name.bind("Box", scope)
    assert again == "Box_3"
    {local, scope} = Name.bind_n("mk", 0, scope)
    assert local == "mk_0"
    {fresh, _} = Name.bind("n", scope)
    assert fresh == "n"

    seen = Name.see(Name.open(MapSet.new()), "muro__ep")
    assert Name.bind("muro__ep", seen) |> elem(0) == "muro__ep_2"
  end

  test "decode inverts encode, including escapes" do
    samples = [
      "is-on",
      "hold-it",
      "muro__iszdon",
      "a_b_2",
      "foo-bar",
      "n'",
      "λ",
      "?",
      "Bit",
      "and",
      "end",
      "true",
      "foo?",
      "1foo",
      "zz",
      "Z",
      "_",
      "a__b",
      ""
    ]

    for name <- samples do
      assert Name.decode(Name.encode(name)) == {:ok, name}
    end

    assert Name.decode("z") == :error
    assert Name.decode("Z") == :error
    assert Name.decode("zn12") == :error
    assert Name.decode("znXXXX") == :error
    assert Name.decode("zn03bb") == :error
    assert Name.decode("zz") == {:ok, "z"}
    assert Name.decode("zu") == {:ok, "_"}
    assert Name.decode("zd") == {:ok, "-"}
    assert Name.decode("zq") == {:ok, "'"}
    assert Name.decode("zn0003bb") == {:ok, "λ"}
    assert Name.decode("zn0003BB") == {:ok, "λ"}
  end

  test "a scalar escape is six digits, and decode is its inverse" do
    ffff = <<0xFFFF::utf8>>
    one = <<0x10000::utf8>>
    ten = <<0x10FFFF::utf8>>
    thousand = <<0x1000::utf8>>

    assert Name.encode(ffff) == "zn00ffff"
    assert Name.encode(one) == "zn010000"
    assert Name.encode(ten) == "zn10ffff"
    assert Name.encode("λ") == "zn0003bb"
    assert Name.encode(one) != Name.encode(thousand <> "0")
    assert Name.encode("zn010000") == "zzn010000"
    assert Name.encode("zn010000") != Name.encode(one)

    for name <- ["", "muro__iszdon", "zn", "zn1234", "zn010000", ffff, one, ten, "λ0", "λ" <> "0"] do
      assert Name.decode(Name.encode(name)) == {:ok, name}
      assert Name.encode(elem(Name.decode(Name.encode(name)), 1)) == Name.encode(name)
    end

    assert Name.decode("zn00d800") == :error
    assert Name.decode("zn00DFFF") == :error
    assert Name.decode("zn110000") == :error
    assert Name.decode("zn0003bb0") == {:ok, "λ0"}
  end

  test "encode is injective on short strings drawn from the escape alphabet" do
    wide = ["a", "z", "Z", "n", "u", "d", "q", "0", "f", "_", "-", "'", "λ", <<0x10000::utf8>>]
    narrow = ["z", "n", "0", "u", "d", "q", "Z", "_"]
    strings = Enum.uniq(sweep(wide, 2) ++ sweep(narrow, 3))

    encoded = Map.new(strings, &{&1, Name.encode(&1)})
    assert map_size(encoded) == length(strings)
    assert length(Enum.uniq(Map.values(encoded))) == length(strings)

    for name <- strings do
      assert Name.decode(Name.encode(name)) == {:ok, name}
    end
  end

  defp sweep(alphabet, max) do
    Enum.reduce(1..max, [""], fn _, acc ->
      acc ++ for prefix <- acc, char <- alphabet, do: prefix <> char
    end)
  end

  defp width?(encoded), do: String.match?(encoded, ~r/^[iu][0-9]+$/)
end

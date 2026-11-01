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

  defp width?(encoded), do: String.match?(encoded, ~r/^[iu][0-9]+$/)
end

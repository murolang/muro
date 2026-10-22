defmodule Muro.Environments.LamTest do
  use ExUnit.Case, async: true

  alias Muro.Environments.Lam
  alias Muro.Policies.Seek
  alias Muro.Reducers.Lam, as: Reducer

  setup_all do
    {:ok, episodes: Lam.episodes()}
  end

  test "the readings are fields of the call, and the search acts in the environment", %{
    episodes: episodes
  } do
    assert Lam.observe(episodes["copy2"]) == %{
             mark: :reuse,
             uses: 2,
             arg_head: :call,
             arg_apps: 1,
             arg_size: Lam.observe(episodes["copy2"]).arg_size
           }

    assert Lam.observe(episodes["discard"]).uses == 0
    assert Lam.observe(episodes["discard"]).mark == :affine
    assert Lam.observe(episodes["copy_discard"]) == %{
             Lam.observe(episodes["discard"])
             | mark: :reuse
           }

    ready = Lam.observe(episodes["copy_ready"])
    assert ready.mark == :reuse
    assert ready.uses == 2
    assert ready.arg_head == :fun
    assert ready.arg_apps == 0

    assert {:ok, %{chain: chain, features: features, rounds: rounds}} =
             Seek.run(Map.values(episodes))

    assert rounds == 1

    assert chain == [
             {{:and, {:feat, {:gt1, :uses}}, {:not, {:feat, {:eq0, :arg_apps}}}}, :arg}
           ]
    assert Enum.any?(features, &match?({:gt0, _field}, &1))
    assert Enum.any?(features, &match?({:square_gt1, _field}, &1))
    assert Enum.any?(features, &match?({:is, _field, _tag}, &1))

    choose = fn term -> Seek.choose(chain, term) end
    spine = fn _term -> :spine end

    counts =
      Map.new(episodes, fn {name, term} ->
        assert {:ok, whnf} = Reducer.follow(term, spine)
        assert {:ok, agent} = Reducer.follow(term, choose)
        {name, %{whnf: whnf, agent: agent}}
      end)

    assert counts["affine"].agent == counts["affine"].whnf
    assert counts["discard"].agent == counts["discard"].whnf
    assert counts["copy_discard"].agent == counts["copy_discard"].whnf
    assert counts["copy_ready"].agent == counts["copy_ready"].whnf
    assert counts["copy2"].agent < counts["copy2"].whnf
    assert counts["copy4"].agent < counts["copy4"].whnf
    assert counts["copy8"].agent < counts["copy8"].whnf

    src = Lam.book(chain, features)

    path =
      Path.join(System.tmp_dir!(), "muro_lam_env_#{System.unique_integer([:positive])}.muro")

    File.write!(path, src)
    assert Muro.check_file(path) == :ok
    assert {:ok, out} = Muro.emit_file(path, Muro.LamEnvPolicy)
    Code.eval_string(out)

    for {name, term} <- episodes do
      obs = Lam.observe(term)

      assert apply(Muro.LamEnvPolicy, :policy, [
               obs.mark,
               peano(obs.uses),
               peano(obs.arg_apps),
               peano(obs.arg_size),
               obs.arg_head
             ]) == choose.(term),
             name
    end
  end

  defp peano(0), do: 0
  defp peano(n) when n > 0, do: {:suc, peano(n - 1)}
end

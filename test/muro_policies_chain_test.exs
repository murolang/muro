defmodule Muro.Policies.ChainTest do
  use ExUnit.Case, async: true

  alias Muro.Policies.Chain

  # The bit is the only feature. true fires, false is the default.
  defp bit(_feature, state), do: state

  defp oracle(_pred, state), do: state

  defp traj(_pred), do: [true, false]

  defp feats(_states), do: [:bit]

  defp score({:feat, _}), do: 1
  defp score(_), do: 0

  test "a chain fires one action" do
    chain = [{{:feat, :bit}, :go}]
    assert Chain.eval_chain(chain, :stay, &bit/2, true) == :go
    assert Chain.eval_chain(chain, :stay, &bit/2, false) == :stay
  end

  test "depth 0 returns the feature test that matches the oracle" do
    assert Chain.run(&score/1, &oracle/2, &traj/1, &feats/1, &bit/2, 0) ==
             {:converged, {:feat, :bit}}
  end

  test "a predicate that matches an observation stays, and the space shrinks" do
    vs = Chain.enumerate([:bit], 0)
    kept = Chain.refine(vs, {true, true}, &bit/2)
    assert {:feat, :bit} in kept
    assert false not in kept
    assert length(kept) < length(vs)

    both = Chain.refine_all(vs, [{true, true}, {false, false}], &bit/2)
    assert {:feat, :bit} in both
    assert true not in both
  end

  test "states that agree on the features a predicate reads agree on its value" do
    pred = {:and, {:feat, :bit}, {:not, {:feat, :other}}}

    feat = fn
      :bit, state -> state.bit
      :other, state -> state.other
    end

    left = %{bit: true, other: false, tag: 1}
    right = %{bit: true, other: false, tag: 2}
    assert Chain.reads(pred) == [:bit, :other]
    assert Chain.eval(pred, feat, left) == Chain.eval(pred, feat, right)
  end

  test "fewer steps is the better action, and a stop ties them" do
    step = fn
      :far, :short -> :done
      :far, :long -> :mid
      :mid, _ -> :done
      other, _ -> other
    end

    stop? = fn state -> state == :done end
    pi = fn _ -> :short end

    assert Chain.fewer?(:far, :short, :long, step, stop?, pi, 4)
    refute Chain.fewer?(:far, :long, :short, step, stop?, pi, 4)
    assert Chain.rollout(:done, :short, step, stop?, pi, 4) == 0
    assert Chain.rollout(:done, :long, step, stop?, pi, 4) == 0
  end

  test "the synthesized policy checks and runs" do
    assert {:converged, pred} =
             Chain.run(&score/1, &oracle/2, &traj/1, &feats/1, &bit/2, 0)

    spell = fn :bit -> "s" end
    src = Chain.policy([{pred, :go}], :stay, spell)

    path =
      Path.join(System.tmp_dir!(), "muro_synth_policy_#{System.unique_integer([:positive])}.muro")

    File.write!(path, src)

    assert Muro.check_file(path) == :ok
    assert {:ok, out} = Muro.emit_file(path, Muro.SynthBitPolicy)
    Code.eval_string(out)
    assert apply(Muro.SynthBitPolicy, :policy, [true]) == :go
    assert apply(Muro.SynthBitPolicy, :policy, [false]) == :stay

    assert {:converged, negated} =
             Chain.deepen(0, 0, &neg_score/1, &neg_oracle/2, &traj/1, &feats/1, &bit/2)

    neg = Chain.policy([{negated, :go}], :stay, spell)

    neg_path =
      Path.join(System.tmp_dir!(), "muro_synth_neg_#{System.unique_integer([:positive])}.muro")

    File.write!(neg_path, neg)
    assert Muro.check_file(neg_path) == :ok
    assert {:ok, neg_out} = Muro.emit_file(neg_path, Muro.SynthNegPolicy)
    Code.eval_string(neg_out)
    assert apply(Muro.SynthNegPolicy, :policy, [true]) == :stay
    assert apply(Muro.SynthNegPolicy, :policy, [false]) == :go
  end

  defp neg_score({:not, {:feat, _}}), do: 1
  defp neg_score(_), do: 0

  defp neg_oracle(_pred, state), do: not state

  test "a miss at depth 0 deepens once and finds the negation" do
    # The oracle wants the bit off. Depth 0 has the positive test, not
    # its negation. One deepening builds {:not, {:feat, :bit}}.
    score = fn
      {:not, {:feat, _}} -> 1
      _ -> 0
    end

    oracle = fn _pred, state -> not state end

    assert Chain.deepen(0, 0, score, oracle, &traj/1, &feats/1, &bit/2) ==
             {:converged, {:not, {:feat, :bit}}}
  end
end

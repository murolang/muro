defmodule Muro.SynthTest do
  use ExUnit.Case, async: true

  alias Muro.Synth

  # The bit is the only feature. true fires, false is the default.
  defp bit(_feature, state), do: state

  defp oracle(_pred, state), do: state

  defp traj(_pred), do: [true, false]

  defp feats(_states), do: [:bit]

  defp score({:feat, _}), do: 1
  defp score(_), do: 0

  test "a chain fires one action" do
    chain = [{{:feat, :bit}, :go}]
    assert Synth.eval_chain(chain, :stay, &bit/2, true) == :go
    assert Synth.eval_chain(chain, :stay, &bit/2, false) == :stay
  end

  test "depth 0 returns the feature test that matches the oracle" do
    assert Synth.run(&score/1, &oracle/2, &traj/1, &feats/1, &bit/2, 0) ==
             {:converged, {:feat, :bit}}
  end

  test "a predicate that matches an observation stays, and the space shrinks" do
    vs = Synth.enumerate([:bit], 0)
    kept = Synth.refine(vs, {true, true}, &bit/2)
    assert {:feat, :bit} in kept
    assert false not in kept
    assert length(kept) < length(vs)

    both = Synth.refine_all(vs, [{true, true}, {false, false}], &bit/2)
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
    assert Synth.reads(pred) == [:bit, :other]
    assert Synth.eval(pred, feat, left) == Synth.eval(pred, feat, right)
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

    assert Synth.fewer?(:far, :short, :long, step, stop?, pi, 4)
    refute Synth.fewer?(:far, :long, :short, step, stop?, pi, 4)
    assert Synth.rollout(:done, :short, step, stop?, pi, 4) == 0
    assert Synth.rollout(:done, :long, step, stop?, pi, 4) == 0
  end

  test "a miss at depth 0 deepens once and finds the negation" do
    # The oracle wants the bit off. Depth 0 has the positive test, not
    # its negation. One deepening builds {:not, {:feat, :bit}}.
    score = fn
      {:not, {:feat, _}} -> 1
      _ -> 0
    end

    oracle = fn _pred, state -> not state end

    assert Synth.cegar(0, 0, score, oracle, &traj/1, &feats/1, &bit/2) ==
             {:converged, {:not, {:feat, :bit}}}
  end
end

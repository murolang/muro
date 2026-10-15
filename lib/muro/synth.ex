defmodule Muro.Synth do
  @moduledoc """
  Discrete predicate synthesis. One state, one action.

  A predicate is a Boolean combination of feature tests. A chain fires
  the action of the first predicate that holds, or the default. The
  search enumerates predicates to a depth and keeps the highest-scoring
  one that agrees with an oracle on a trajectory. Score zero is dropped.

  `fewer?/7` compares two actions by how soon a stop is reached. One
  call of `step` is one action. A state that has already stopped ties
  them.

  The checker is not involved. A candidate is a predicate, not a reduct.
  """

  @doc """
  Evaluate `pred` at `state`. `feat.(feature, state)` is one test.
  """
  def eval(true, _feat, _state), do: true
  def eval(false, _feat, _state), do: false
  def eval({:feat, feature}, feat, state), do: feat.(feature, state)
  def eval({:and, p, q}, feat, state), do: eval(p, feat, state) and eval(q, feat, state)
  def eval({:or, p, q}, feat, state), do: eval(p, feat, state) or eval(q, feat, state)
  def eval({:not, p}, feat, state), do: not eval(p, feat, state)

  @doc """
  The first pair whose predicate holds supplies the action.
  """
  def eval_chain([], default, _feat, _state), do: default

  def eval_chain([{pred, action} | rest], default, feat, state) do
    if eval(pred, feat, state),
      do: action,
      else: eval_chain(rest, default, feat, state)
  end

  @doc """
  Features this predicate reads, in the order they occur.
  """
  def reads(true), do: []
  def reads(false), do: []
  def reads({:feat, feature}), do: [feature]
  def reads({:and, p, q}), do: reads(p) ++ reads(q)
  def reads({:or, p, q}), do: reads(p) ++ reads(q)
  def reads({:not, p}), do: reads(p)

  @doc """
  Every predicate built from `features` at this depth. Depth 0 is the
  constants and the feature tests.
  """
  def enumerate(features, 0), do: atoms(features)

  def enumerate(features, depth) when is_integer(depth) and depth > 0,
    do: extend(enumerate(features, depth - 1))

  @doc """
  Predicates in `vs` that match the observation `{state, bit}`.
  """
  def refine(vs, ob, feat), do: Enum.filter(vs, &consistent?(&1, ob, feat))

  @doc """
  Refine by each observation, in order.
  """
  def refine_all(vs, [], _feat), do: vs
  def refine_all(vs, [ob | obs], feat), do: refine_all(refine(vs, ob, feat), obs, feat)

  @doc """
  `pred` agrees with `oracle.(pred, state)` at every state in `traj`.
  """
  def agrees?(pred, oracle, traj, feat) do
    Enum.all?(traj, fn state -> eval(pred, feat, state) == oracle.(pred, state) end)
  end

  @doc """
  `{:converged, pred}` is the best positive-scoring predicate that
  agrees with the oracle. `{:cegar, pred}` is the best candidate when
  none agreed.
  """
  def solve(cands, score, oracle, traj, feat) do
    case Enum.filter(cands, &viable?(&1, score, oracle, traj, feat)) do
      [] -> {:cegar, best(cands, score)}
      viable -> {:converged, best(viable, score)}
    end
  end

  @doc """
  Search at `depth`. Features come from the trajectories of the
  constant predicates `true` and `false`. `feat.(feature, state)`
  reads a test. `feats.(states)` lists the features those states offer.
  """
  def run(score, oracle, traj, feats, feat, depth) do
    run_from(true, score, oracle, traj, feats, feat, depth)
  end

  @doc """
  Same search, with `seed` added to the states the features are drawn from.
  """
  def run_from(seed, score, oracle, traj, feats, feat, depth) do
    states = traj.(true) ++ traj.(false) ++ traj.(seed)
    solve(enumerate(feats.(states), depth), score, oracle, traj, feat)
  end

  @doc """
  On `{:cegar, pred}`, try `pred` at the next depth. `budget` is how
  many further deepenings follow that try. `{:converged, _}` stops.
  """
  def cegar(budget, depth, score, oracle, traj, feats, feat) do
    step(
      budget,
      depth,
      run(score, oracle, traj, feats, feat, depth),
      score,
      oracle,
      traj,
      feats,
      feat
    )
  end

  @doc """
  Steps until `stop?.(state)`, taking `action` first and then `pi`.
  Fuel `0` counts nothing.
  """
  def rollout(_state, _action, _step, _stop?, _pi, 0), do: 0

  def rollout(state, action, step, stop?, pi, fuel) when is_integer(fuel) and fuel > 0 do
    if stop?.(state) do
      0
    else
      next = step.(state, action)
      1 + rollout(next, pi.(next), step, stop?, pi, fuel - 1)
    end
  end

  @doc """
  `a1` reaches the stop in no more steps than `a2`.
  """
  def fewer?(state, a1, a2, step, stop?, pi, fuel) do
    rollout(state, a1, step, stop?, pi, fuel) <= rollout(state, a2, step, stop?, pi, fuel)
  end

  defp step(_budget, _depth, {:converged, pred}, _score, _oracle, _traj, _feats, _feat),
    do: {:converged, pred}

  defp step(budget, depth, {:cegar, pred}, score, oracle, traj, feats, feat)
       when budget == 0 or budget > 0 do
    next = run_from(pred, score, oracle, traj, feats, feat, depth + 1)

    if budget == 0 do
      next
    else
      step(budget - 1, depth + 1, next, score, oracle, traj, feats, feat)
    end
  end

  defp atoms(features), do: [true, false | Enum.map(features, &{:feat, &1})]

  defp extend(prev) do
    neg = Enum.map(prev, &{:not, &1})

    prev ++
      neg ++
      pairs(prev, prev, :and) ++
      pairs(prev, prev, :or) ++
      pairs(prev, neg, :and) ++
      pairs(prev, neg, :or)
  end

  defp pairs(left, right, op) do
    Enum.flat_map(left, fn p -> Enum.map(right, &{op, p, &1}) end)
  end

  defp consistent?(pred, {state, bit}, feat), do: eval(pred, feat, state) == bit

  defp viable?(pred, score, oracle, traj, feat) do
    score.(pred) > 0 and agrees?(pred, oracle, traj.(pred), feat)
  end

  # Earlier candidates win a tie. A later one replaces the leader only
  # on a strictly higher score.
  defp best([], _score), do: true

  defp best([pred | rest], score) do
    Enum.reduce(rest, pred, fn cand, leader ->
      if score.(cand) > score.(leader), do: cand, else: leader
    end)
  end
end

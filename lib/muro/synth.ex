defmodule Muro.Synth do
  @moduledoc """
  Discrete predicate synthesis.

  A predicate is a Boolean combination of feature tests. `eval/3` is the
  same reading as `eval` in `examples/cshrl/lib/synth.muro`: a feature
  test, a conjunction, a disjunction, a negation, or a constant. The
  checker sees that program, deployed as a `run` policy. It does not see
  the search that built it.

  Version space, not scores, decides who survives. `solve/5` keeps every
  predicate that matches the observations. `pick/2` chooses the smallest
  of those. The size of a program is the number of predicate
  constructors: a constant or a feature test is one, a negation is one
  plus its body, and a conjunction or a disjunction is one plus both
  parts. The feature's name is not a constructor. A score breaks a tie
  between programs of equal size, and an earlier program wins a
  remaining tie. A score does not put a program that missed an
  observation back into the space.

  `cegis_loop/2` is the closed search. It enumerates, refines by
  observations taken from the environment's emitted `step`, deepens
  while the space is empty and the depth bound allows it, and, when a
  check of the surviving program fails, drops that candidate and checks
  the next one. A candidate the checker refused is not selected again.
  When the refusal removes every survivor and a greater depth is still
  allowed, the search continues there. The fuel bound and the round
  bound are operational. They stop a loop that is not shrinking. They
  are not `sufficient-cegis`. A sweep of one trajectory is not that
  theorem.

  `deepen/7` is the depth step. A miss at the current depth searches
  the next depth. `budget` is how many further deepenings follow that
  try. Budget 0 deepens once.
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
  Predicate constructors in `pred`. A feature name adds nothing.
  """
  def size(true), do: 1
  def size(false), do: 1
  def size({:feat, _feature}), do: 1
  def size({:not, pred}), do: 1 + size(pred)
  def size({:and, p, q}), do: 1 + size(p) + size(q)
  def size({:or, p, q}), do: 1 + size(p) + size(q)

  @doc """
  The Muro term for `pred`, using `truep`, `falsep`, `feat`, `andp`,
  `orp`, and `notp`.
  """
  def render(true), do: "truep"
  def render(false), do: "falsep"
  def render({:feat, feature}), do: "(feat #{feature})"
  def render({:not, pred}), do: "(notp #{render(pred)})"
  def render({:and, p, q}), do: "(andp #{render(p)} #{render(q)})"
  def render({:or, p, q}), do: "(orp #{render(p)} #{render(q)})"

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
  Every predicate in `cands` that agrees with `oracle` on `traj.(pred)`.

  `score` does not filter and does not order the result. `{:survivors,
  preds}` keeps every match, in enumeration order. `{:empty, []}` is an
  empty version space. `pick/2` chooses among the survivors.
  """
  def solve(cands, score, oracle, traj, feat) when is_function(score, 1) do
    case Enum.filter(cands, &agrees?(&1, oracle, traj.(&1), feat)) do
      [] -> {:empty, []}
      preds -> {:survivors, preds}
    end
  end

  @doc """
  The smallest predicate in `preds`. A higher `score` wins among equal
  sizes. An earlier predicate wins a remaining tie.
  """
  def pick([pred | rest], score) when is_function(score, 1) do
    Enum.reduce(rest, pred, fn cand, leader ->
      cond do
        size(cand) < size(leader) -> cand
        size(cand) > size(leader) -> leader
        score.(cand) > score.(leader) -> cand
        true -> leader
      end
    end)
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
  On an empty version space, search at the next depth. `budget` is how
  many further deepenings follow that try. `{:survivors, _}` stops.
  Budget 0 deepens once and returns that space, empty or not.
  """
  def deepen(budget, depth, score, oracle, traj, feats, feat) do
    go(budget, depth, score, oracle, traj, feats, feat)
  end

  @doc """
  Closed search over a checked environment.

  `path` is a book that already checks and defines `step`. Observations
  come from that emitted `step` and the named oracle (`trace`,
  `successor`, or `coind-homo`). See `Muro.Synth.Loop`.
  """
  def cegis_loop(path, opts \\ []) when is_binary(path) and is_list(opts) do
    Muro.Synth.Loop.run(path, opts)
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

  @doc """
  A `.muro` book whose `policy` is this chain.

  `s` is a reusable `Bool`. `spell.(feature)` is the `Bool` term for one
  test, written in scope of `s`. Each action and the default are
  constructors of `Action`. The book typechecks when those spellings do.
  """
  def policy(chain, default, spell) when is_list(chain) and is_function(spell, 1) do
    actions =
      chain
      |> Enum.map(fn {_pred, action} -> muro_name(action) end)
      |> Enum.concat([muro_name(default)])
      |> Enum.uniq()

    ctors = Enum.map_join(actions, "\n", &"  #{&1} : Action")

    """
    data Bool : Type where
      true : Bool
      false : Bool

    data Action : Type where
    #{ctors}

    def policy : run Π (+ s : Bool) → Action :=
      λ (+ s : Bool) →
        #{chain_term(chain, default, spell)}
    """
  end

  defp go(budget, depth, score, oracle, traj, feats, feat) do
    case run(score, oracle, traj, feats, feat, depth) do
      {:survivors, _preds} = hit -> hit
      {:empty, []} -> deepen_more(budget, depth, score, oracle, traj, feats, feat)
    end
  end

  defp deepen_more(0, depth, score, oracle, traj, feats, feat) do
    run(score, oracle, traj, feats, feat, depth + 1)
  end

  defp deepen_more(budget, depth, score, oracle, traj, feats, feat) when budget > 0 do
    go(budget - 1, depth + 1, score, oracle, traj, feats, feat)
  end

  defp chain_term([], default, _spell), do: muro_name(default)

  defp chain_term([{pred, action} | rest], default, spell) do
    "(match #{bool_term(pred, spell)} motive (λ _ → Action) | true => #{muro_name(action)} | false => #{chain_term(rest, default, spell)})"
  end

  defp bool_term(true, _spell), do: "true"
  defp bool_term(false, _spell), do: "false"
  defp bool_term({:feat, feature}, spell), do: "(#{spell.(feature)})"

  defp bool_term({:not, pred}, spell) do
    "(match #{bool_term(pred, spell)} motive (λ _ → Bool) | true => false | false => true)"
  end

  defp bool_term({:and, p, q}, spell) do
    "(match #{bool_term(p, spell)} motive (λ _ → Bool) | true => #{bool_term(q, spell)} | false => false)"
  end

  defp bool_term({:or, p, q}, spell) do
    "(match #{bool_term(p, spell)} motive (λ _ → Bool) | true => true | false => #{bool_term(q, spell)})"
  end

  defp muro_name(name) when is_atom(name) do
    text = Atom.to_string(name)

    if String.match?(text, ~r/^[A-Za-z_][A-Za-z0-9_-]*$/) do
      text
    else
      raise ArgumentError, "not a Muro name: #{inspect(name)}"
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
end

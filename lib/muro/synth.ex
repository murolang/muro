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

  `enumerate_sized/6` is the search after `reaches-pos` is installed.
  It builds programs by size, up to `pred_size_bound/0`: the atoms, their
  negations, a conjunction or a disjunction of two atoms, the same with
  the right atom negated, and a left-associated conjunction or
  disjunction of feature tests. One further layer negates such a
  disjunction or conjunction and joins it with an atom. An
  action-indexed family adds two atoms per action: `self` is that
  action's feature, and `other` is the disjunction of the same stem at
  every other action. Each is one constructor. The list of actions is
  not counted again. Those atoms combine by the same negation and
  pairing rules. The subset chains stay feature tests, because a
  quantifier is already one constructor for the whole action set. One
  observation signature keeps the smallest program. A later program of
  the same signature is kept only when it is smaller.

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

  The book that checks is the surviving predicate. `rank` reads it:
  `Unit` when the predicate prefers the action, `Empty` when it does
  not. On a finite state type, the book also carries the homomorphism
  of that ranking when every successor has a constant `solve`, checked
  on the same `step`. A state that pays less now still has that
  ranking: the tail comparison rewrites the successors' constants.
  That checked homomorphism is the success. A policy whose environment
  does not define the homomorphism is reported and is not success.

  `deepen/7` is the depth step. A miss at the current depth searches
  the next depth. `budget` is how many further deepenings follow that
  try. Budget 0 deepens once.
  """

  @doc """
  Evaluate `pred` at `state`. `feat.(feature, state)` is one test.
  """
  def eval(pred, feat, state) do
    {:ok, value, :infinity} = eval(pred, feat, state, :infinity)
    value
  end

  @doc """
  Evaluate `pred` at `state` under a fuel bound.

  One unit of fuel is one predicate constructor this walk visits, in
  `eval/3`'s order, including the short-circuit of `and` and `or`. An
  `other` spends one unit for its constructor and one unit for each
  column it reads.

  `fuel` is a non-negative integer, or `:infinity` for an unbounded
  walk. The result is `{:ok, value, fuel_left}` when the walk finishes,
  and `:out_of_fuel` when a constructor is needed and no fuel remains.
  `:infinity` never returns `:out_of_fuel`.
  """
  def eval(true, _feat, _state, fuel) do
    case charge(fuel) do
      {:ok, left} -> {:ok, true, left}
      :out_of_fuel -> :out_of_fuel
    end
  end

  def eval(false, _feat, _state, fuel) do
    case charge(fuel) do
      {:ok, left} -> {:ok, false, left}
      :out_of_fuel -> :out_of_fuel
    end
  end

  def eval({:feat, feature}, feat, state, fuel) do
    case charge(fuel) do
      {:ok, left} -> {:ok, feat.(feature, state), left}
      :out_of_fuel -> :out_of_fuel
    end
  end

  def eval({:not, pred}, feat, state, fuel) do
    case charge(fuel) do
      :out_of_fuel ->
        :out_of_fuel

      {:ok, left} ->
        case eval(pred, feat, state, left) do
          {:ok, value, rest} -> {:ok, not value, rest}
          :out_of_fuel -> :out_of_fuel
        end
    end
  end

  def eval({:and, p, q}, feat, state, fuel) do
    case charge(fuel) do
      :out_of_fuel ->
        :out_of_fuel

      {:ok, left} ->
        case eval(p, feat, state, left) do
          {:ok, false, rest} -> {:ok, false, rest}
          {:ok, true, rest} -> eval(q, feat, state, rest)
          :out_of_fuel -> :out_of_fuel
        end
    end
  end

  def eval({:or, p, q}, feat, state, fuel) do
    case charge(fuel) do
      :out_of_fuel ->
        :out_of_fuel

      {:ok, left} ->
        case eval(p, feat, state, left) do
          {:ok, true, rest} -> {:ok, true, rest}
          {:ok, false, rest} -> eval(q, feat, state, rest)
          :out_of_fuel -> :out_of_fuel
        end
    end
  end

  def eval({:self, _stem, _action, nil}, _feat, _state, fuel) do
    case charge(fuel) do
      {:ok, left} -> {:ok, false, left}
      :out_of_fuel -> :out_of_fuel
    end
  end

  def eval({:self, _stem, _action, feature}, feat, state, fuel) do
    eval({:feat, feature}, feat, state, fuel)
  end

  def eval({:other, _stem, _action, features}, feat, state, fuel) when is_list(features) do
    case charge(fuel) do
      :out_of_fuel -> :out_of_fuel
      {:ok, left} -> any_column(features, feat, state, left)
    end
  end

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
  def reads({:self, _stem, _action, nil}), do: []
  def reads({:self, _stem, _action, feature}), do: [feature]
  def reads({:other, _stem, _action, features}) when is_list(features), do: features

  @doc """
  Predicate constructors in `pred`. A feature name adds nothing.

  A constant or a feature test is 1. A negation is 1 plus its body. A
  conjunction or a disjunction is 1 plus both parts. `{:self, stem,
  action, feature}`, rendered `selfp`, is 1: it reads that action's
  column of the stem. `{:other, stem, action, features}`, rendered
  `otherp`, is also 1: it is the disjunction of the stem at every other
  action, and the list of those columns is not counted again, so the
  size does not grow with the number of actions. An `other` with no
  other column is false and still size 1.
  """
  def size(true), do: 1
  def size(false), do: 1
  def size({:feat, _feature}), do: 1
  def size({:not, pred}), do: 1 + size(pred)
  def size({:and, p, q}), do: 1 + size(p) + size(q)
  def size({:or, p, q}), do: 1 + size(p) + size(q)
  def size({:self, _stem, _action, _feature}), do: 1
  def size({:other, _stem, _action, features}) when is_list(features), do: 1

  @doc """
  The Muro term for `pred`, using `truep`, `falsep`, `feat`, `andp`,
  `orp`, `notp`, `selfp`, and `otherp`. `selfp stem a` and `otherp stem
  a` name the stem and the action. The columns they read are not
  written: the policy book's `stem-at` and `other-at` supply them.
  """
  def render(true), do: "truep"
  def render(false), do: "falsep"
  def render({:feat, feature}), do: "(feat #{feature})"
  def render({:not, pred}), do: "(notp #{render(pred)})"
  def render({:and, p, q}), do: "(andp #{render(p)} #{render(q)})"
  def render({:or, p, q}), do: "(orp #{render(p)} #{render(q)})"

  def render({:self, stem, action, _feature}), do: "(selfp #{stem} #{action})"

  def render({:other, stem, action, _features}), do: "(otherp #{stem} #{action})"

  @doc """
  Every predicate built from `features` at this depth. Depth 0 is the
  constants and the feature tests.
  """
  def enumerate(features, 0), do: atoms(features)

  def enumerate(features, depth) when is_integer(depth) and depth > 0,
    do: extend(enumerate(features, depth - 1))

  @pred_size_bound 18
  # C(36, 9) is 94143280 and C(40, 8) is 76904685. C(40, 9) is
  # 273438880, so a cover of forty features still shrinks the widest
  # subset, and the report names this budget. A cover of 76 features
  # shrinks to five, because C(76, 6) is 218618940.
  @subset_budget 100_000_000
  # Four queens considers 8138 programs and stops at size 4. One
  # million remains the stop for a walk that has not met every
  # signature. An earlier eight-queens size walk, made before these
  # atoms, had considered 3766542 programs by the end of size 7.
  @considered_budget 1_000_000
  # Soft bound on current growth, sampled in `sized_insert` before each
  # candidate is inserted. This process's memory (`Process.info(self(),
  # :memory)`) minus the total at the start of the walk. Not a hard cap
  # on the peak: the candidate just inserted can pass the bound before
  # the next sample, and a later sample reads the total after
  # collection, not the high-water mark. Other processes in the same VM
  # do not count. 512 MiB.
  @memory_budget 512 * 1_048_576

  @doc """
  The size `enumerate_sized/6` searches up to.
  """
  def pred_size_bound, do: @pred_size_bound

  @doc """
  A subset whose binomial coefficient is above this is not enumerated.

  The budget admits a subset of nine features out of thirty-six, which
  is the widest subset a size of 18 builds, and a subset of eight
  features out of forty. A cover of seventy-six features shrinks to a
  subset of five. A wider subset is still skipped, and the report
  names the budget.
  """
  def subset_budget, do: @subset_budget

  @doc """
  Programs `enumerate_sized/6` considers before it stops, unless a call
  passes `considered_budget:`.

  The walk stops once it has considered this many programs. The report
  names `considered budget` and does not deploy a predicate. The walk
  reads the bound once, at the start. `Muro.Synth.Loop.run/2` takes the
  same option.
  """
  def considered_budget, do: @considered_budget

  @doc """
  Bytes of current growth `enumerate_sized/6` may observe before it
  stops, unless a call passes `memory_budget:`.

  The bound is a soft sample of current growth of this process, not a
  hard cap on the peak and not the size of the VM. Before each candidate
  is inserted, the walk reads `Process.info(self(), :memory)` minus the
  process total recorded when the walk started. Concurrent work in other
  processes does not count. The candidate just inserted can take that
  total past the bound; the next sample is what stops the walk. A later
  sample reads the total after collection, not the high-water mark.
  The report names `memory budget`. A negative bound stops before the
  first candidate. `Muro.Synth.Loop.run/2` takes the same option, and
  the walk reads it once, at the start.
  """
  def memory_budget, do: @memory_budget

  @doc """
  Pack `pred` on `states` into an integer. The first state is the high bit.
  """
  def signature(pred, states, feat) when is_function(feat, 2) and is_list(states) do
    states
    |> Enum.map(&eval(pred, feat, &1))
    |> pack_bits()
  end

  @doc """
  Pack booleans into an integer. The first boolean is the high bit.
  """
  def pack_bits(bits) when is_list(bits) do
    Enum.reduce(bits, 0, fn bit, acc ->
      Bitwise.bor(Bitwise.bsl(acc, 1), if(bit, do: 1, else: 0))
    end)
  end

  @doc """
  Programs from `features` up to `max_size`, one per observation signature.

  `sig_fun.(pred)` is that signature. `width` is the number of states the
  signature packs, and it is the mask a negation flips. `index` maps a
  signature to `{program, size, order}`. `meta` counts the programs
  considered, the distinct signatures, the new signatures at each size,
  and whether a subset was skipped because its binomial coefficient
  passed `subset_budget/0`.

  `wanted` is a set of signatures to retain. Counts still include every
  new signature. `nil` retains every signature. The bank keeps a program
  only for a wanted signature. `seen` still records every signature, so
  a later smaller program of a wanted signature replaces the one kept,
  and a repeated signature is not counted twice.

  `opts` may set `families:`, the action-indexed stems from
  `Muro.Synth.Feature.families/2`. Omitted, the grammar is the feature
  tests alone. A family contributes `self` and `other` atoms. Their
  signatures are the feature column and the pointwise disjunction of
  the other actions. The subset walk does not take those atoms: a
  quantifier is already the whole action set.

  `{:ok, index, meta}` is a finished walk. `{:empty, reason, meta}` is
  a stop: `reason` is `considered budget` or `memory budget`. `meta`
  counts only the programs considered before that stop. `size` is the
  last size at which a program was counted, and it is 0 when the walk
  stops before counting one. It advances only after that count, so a
  budget that lands on the last program of a size names that size.
  `sizes` lists each size that added a new signature. When the last
  counted size added one, it is the last row of `sizes`. `size` is
  that enumeration progress on a finished walk and on a stop. It is
  not the size of a survivor. A partial bank is not returned.

  `opts` may set `considered_budget:` and `memory_budget:`. Omitted, the
  bounds are `considered_budget/0` and `memory_budget/0`. The walk reads
  them once, at the start. Each bound must be an integer.
  """
  def enumerate_sized(features, max_size, sig_fun, width, wanted \\ nil, opts \\ [])
      when is_list(features) and is_integer(max_size) and max_size >= 1 and
             is_function(sig_fun, 1) and is_integer(width) and width >= 0 and
             (is_nil(wanted) or is_struct(wanted, MapSet)) and is_list(opts) do
    started = System.monotonic_time(:millisecond)
    considered_budget = budget_opt!(opts, :considered_budget, @considered_budget)
    memory_budget = budget_opt!(opts, :memory_budget, @memory_budget)
    families = Keyword.get(opts, :families, [])
    mask = Bitwise.bsl(1, width) - 1
    feat_atoms = Enum.map(features, &{:feat, &1})
    atoms = [true, false | feat_atoms]
    n = length(features)
    k_or = div(max_size + 1, 2)
    k_wrap = if max_size >= 4, do: div(max_size - 2, 2), else: 0
    k_ideal = min(n, max(k_or, k_wrap))
    k_cap = shrink_k(n, k_ideal)
    trace_open(n, max_size, k_cap, k_ideal)

    sigs =
      Map.new(atoms, fn
        true -> {true, mask}
        false -> {false, 0}
        atom -> {atom, sig_fun.(atom)}
      end)

    sigs = family_column_sigs(sigs, families, sig_fun)
    {quant_atoms, quant_sigs} = quantifier_atoms(families, sigs)
    atoms = atoms ++ quant_atoms
    sigs = Map.merge(sigs, quant_sigs)

    st = %{
      max_size: max_size,
      mask: mask,
      sigs: sigs,
      atoms: atoms,
      feat_atoms: feat_atoms,
      k_cap: k_cap,
      wanted: wanted,
      seen: %{},
      bank: %{},
      counts: %{},
      considered: 0,
      distinct: 0,
      ord: 0,
      trace: trace?(),
      started: started,
      stop: nil,
      size: 0,
      considered_budget: considered_budget,
      memory_budget: memory_budget,
      base_mem: walk_memory()
    }

    # `after_base:` is a zero-arity hook for tests. It runs after
    # `base_mem` is recorded and before the first candidate is inserted,
    # so a test can grow memory in another process and then continue.
    case Keyword.get(opts, :after_base) do
      hook when is_function(hook, 0) -> hook.()
      _other -> :ok
    end

    # `size` advances in `insert_counted`, after a program at that
    # size is counted. Assigning it here would name the next size when
    # the budget lands on the last program of this one.
    st =
      Enum.reduce_while(1..max_size, st, fn size, st ->
        if stopped?(st) do
          {:halt, st}
        else
          trace_begin(st, size)
          st = add_size(st, size)
          trace_size(st, size, started)

          cond do
            stopped?(st) ->
              {:halt, st}

            wanted != nil and Enum.all?(wanted, &Map.has_key?(st.seen, &1)) ->
              {:halt, st}

            true ->
              {:cont, st}
          end
        end
      end)

    meta = sized_meta(st, k_ideal, k_cap, started)

    if stopped?(st) do
      {:empty, st.stop, meta}
    else
      {:ok, st.bank, meta}
    end
  end

  defp sized_meta(st, k_ideal, k_cap, started) do
    sizes =
      st.counts
      |> Enum.reject(fn {_size, count} -> count <= 0 end)
      |> Enum.sort_by(&elem(&1, 0))
      |> Enum.map(fn {size, count} -> [size, count] end)

    %{
      considered: st.considered,
      distinct: st.distinct,
      truncated: k_ideal >= 2 and k_cap < k_ideal,
      sizes: sizes,
      size: st.size,
      enum_ms: System.monotonic_time(:millisecond) - started
    }
  end

  defp budget_opt!(opts, key, default) do
    case Keyword.get(opts, key, default) do
      n when is_integer(n) ->
        n

      other ->
        raise ArgumentError, "#{key} must be an integer, got: #{inspect(other)}"
    end
  end

  defp stopped?(%{stop: stop}) when is_binary(stop), do: true
  defp stopped?(_st), do: false

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

  defp bool_term({:self, _stem, _action, nil}, _spell), do: "false"
  defp bool_term({:self, _stem, _action, feature}, spell), do: "(#{spell.(feature)})"

  # The first column is the outermost test, in the order of `features`.
  defp bool_term({:other, _stem, _action, features}, spell) do
    List.foldr(features, "false", fn feature, acc ->
      "(match #{bool_term({:self, nil, nil, feature}, spell)} motive (λ _ → Bool) | true => true | false => #{acc})"
    end)
  end

  defp muro_name(name) when is_atom(name) do
    text = Atom.to_string(name)

    if String.match?(text, ~r/^[A-Za-z_][A-Za-z0-9_-]*$/) do
      text
    else
      raise ArgumentError, "not a Muro name: #{inspect(name)}"
    end
  end

  defp add_size(st, 1) do
    reduce_stop(st.atoms, st, fn atom, st ->
      sized_insert(st, fn -> atom end, 1, Map.fetch!(st.sigs, atom))
    end)
  end

  defp add_size(st, 2) do
    reduce_stop(st.atoms, st, fn atom, st ->
      sig = negate_sig(Map.fetch!(st.sigs, atom), st.mask)
      sized_insert(st, fn -> {:not, atom} end, 2, sig)
    end)
  end

  defp add_size(st, 3) do
    st
    |> add_atom_pairs(:and, 3, false)
    |> add_atom_pairs(:or, 3, false)
  end

  defp add_size(st, 4) do
    st
    |> add_atom_pairs(:and, 4, true)
    |> add_atom_pairs(:or, 4, true)
    |> add_not_nary(4)
  end

  defp add_size(st, size) do
    st
    |> add_bare_nary(size)
    |> add_not_nary(size)
    |> add_wraps(size)
  end

  defp reduce_stop(enum, acc, fun) do
    Enum.reduce_while(enum, acc, fn item, acc ->
      if stopped?(acc) do
        {:halt, acc}
      else
        {:cont, fun.(item, acc)}
      end
    end)
  end

  defp add_atom_pairs(st, _op, _size, _negated?) when is_binary(st.stop), do: st

  defp add_atom_pairs(st, op, size, negated?) do
    reduce_stop(st.atoms, st, fn left, st ->
      left_sig = Map.fetch!(st.sigs, left)

      reduce_stop(st.atoms, st, fn right, st ->
        right_sig =
          if negated?,
            do: negate_sig(Map.fetch!(st.sigs, right), st.mask),
            else: Map.fetch!(st.sigs, right)

        prog = fn ->
          if negated?, do: {op, left, {:not, right}}, else: {op, left, right}
        end

        sized_insert(st, prog, size, combine_sig(op, left_sig, right_sig))
      end)
    end)
  end

  defp add_bare_nary(st, _size) when is_binary(st.stop), do: st

  defp add_bare_nary(st, size) do
    k = div(size + 1, 2)

    if k >= 3 and k <= st.k_cap and 2 * k - 1 == size do
      add_subsets(st, k, fn chosen, st ->
        st
        |> sized_insert(fn -> fold_prog(chosen, :or) end, size, fold_sig(chosen, st.sigs, :or))
        |> sized_insert(fn -> fold_prog(chosen, :and) end, size, fold_sig(chosen, st.sigs, :and))
      end)
    else
      st
    end
  end

  defp add_not_nary(st, _size) when is_binary(st.stop), do: st

  defp add_not_nary(st, size) do
    body = size - 1
    k = div(body + 1, 2)

    if k >= 2 and k <= st.k_cap and 2 * k - 1 == body do
      add_subsets(st, k, fn chosen, st ->
        or_sig = fold_sig(chosen, st.sigs, :or)
        and_sig = fold_sig(chosen, st.sigs, :and)

        st
        |> sized_insert(
          fn -> {:not, fold_prog(chosen, :or)} end,
          size,
          negate_sig(or_sig, st.mask)
        )
        |> sized_insert(
          fn -> {:not, fold_prog(chosen, :and)} end,
          size,
          negate_sig(and_sig, st.mask)
        )
      end)
    else
      st
    end
  end

  defp add_wraps(st, _size) when is_binary(st.stop), do: st

  defp add_wraps(st, size) do
    k = div(size - 2, 2)

    if k >= 2 and k <= st.k_cap and 2 * k + 2 == size do
      add_subsets(st, k, fn chosen, st ->
        or_prog = fn -> {:not, fold_prog(chosen, :or)} end
        and_prog = fn -> {:not, fold_prog(chosen, :and)} end
        or_sig = negate_sig(fold_sig(chosen, st.sigs, :or), st.mask)
        and_sig = negate_sig(fold_sig(chosen, st.sigs, :and), st.mask)

        reduce_stop(st.atoms, st, fn atom, st ->
          atom_sig = Map.fetch!(st.sigs, atom)

          st
          |> sized_insert(
            fn -> {:or, atom, or_prog.()} end,
            size,
            combine_sig(:or, atom_sig, or_sig)
          )
          |> sized_insert(
            fn -> {:and, atom, or_prog.()} end,
            size,
            combine_sig(:and, atom_sig, or_sig)
          )
          |> sized_insert(
            fn -> {:or, atom, and_prog.()} end,
            size,
            combine_sig(:or, atom_sig, and_sig)
          )
          |> sized_insert(
            fn -> {:and, atom, and_prog.()} end,
            size,
            combine_sig(:and, atom_sig, and_sig)
          )
        end)
      end)
    else
      st
    end
  end

  defp add_subsets(st, _k, _fun) when is_binary(st.stop), do: st

  defp add_subsets(st, k, fun) do
    combine(st.feat_atoms, k, [], fun, st)
  end

  defp combine(_list, _k, _chosen, _fun, %{stop: stop} = acc) when is_binary(stop), do: acc
  defp combine(_list, 0, chosen, fun, acc), do: fun.(Enum.reverse(chosen), acc)
  defp combine([], _k, _chosen, _fun, acc), do: acc

  defp combine([head | tail], k, chosen, fun, acc) do
    acc = combine(tail, k - 1, [head | chosen], fun, acc)
    combine(tail, k, chosen, fun, acc)
  end

  defp fold_prog([first | rest], op) do
    Enum.reduce(rest, first, fn atom, prog -> {op, prog, atom} end)
  end

  defp fold_sig([first | rest], sigs, op) do
    Enum.reduce(rest, Map.fetch!(sigs, first), fn atom, sig ->
      combine_sig(op, sig, Map.fetch!(sigs, atom))
    end)
  end

  defp combine_sig(:or, left, right), do: Bitwise.bor(left, right)
  defp combine_sig(:and, left, right), do: Bitwise.band(left, right)
  defp negate_sig(sig, mask), do: Bitwise.bxor(sig, mask)

  # One choke point for both bounds. A program past either bound is not
  # inserted. `seen` still records every signature that was inserted, so
  # the counts stay the counts of the programs actually considered.
  #
  # The memory sample is the current process total, not a peak and not
  # the VM. It runs before this candidate is inserted, so the previous
  # candidate can already have taken the process total past the bound.
  defp sized_insert(%{stop: stop} = st, _prog_fun, _size, _sig) when is_binary(stop), do: st

  defp sized_insert(st, _prog_fun, _size, _sig) when st.considered >= st.considered_budget do
    %{st | stop: "considered budget"}
  end

  defp sized_insert(st, _prog_fun, _size, _sig) when st.memory_budget < 0 do
    %{st | stop: "memory budget"}
  end

  defp sized_insert(st, prog_fun, size, sig) do
    if over_memory?(st) do
      %{st | stop: "memory budget"}
    else
      st = insert_counted(st, prog_fun, size, sig)
      heartbeat(st)
    end
  end

  # Current growth of this process since `base_mem`, not the high-water
  # mark and not `:erlang.memory(:total)`. Collection between samples
  # lowers the total the next candidate sees.
  defp over_memory?(st) do
    walk_memory() - st.base_mem > st.memory_budget
  end

  defp walk_memory do
    {:memory, mem} = Process.info(self(), :memory)
    mem
  end

  defp insert_counted(st, _prog_fun, size, _sig) when size > st.max_size, do: st

  defp insert_counted(st, prog_fun, size, sig) do
    considered = st.considered + 1

    case Map.fetch(st.seen, sig) do
      {:ok, old} when old <= size ->
        %{st | considered: considered, size: size}

      {:ok, old} ->
        %{
          st
          | considered: considered,
            size: size,
            seen: Map.put(st.seen, sig, size),
            counts: move_count(st.counts, old, size),
            bank: replace_bank(st, sig, prog_fun, size)
        }

      :error ->
        bank =
          if st.wanted == nil or MapSet.member?(st.wanted, sig) do
            Map.put(st.bank, sig, {prog_fun.(), size, st.ord})
          else
            st.bank
          end

        %{
          st
          | considered: considered,
            size: size,
            seen: Map.put(st.seen, sig, size),
            counts: Map.update(st.counts, size, 1, &(&1 + 1)),
            bank: bank,
            ord: st.ord + 1,
            distinct: st.distinct + 1
        }
    end
  end

  defp heartbeat(%{trace: true, considered: considered} = st)
       when rem(considered, 1_000_000) == 0 do
    elapsed = System.monotonic_time(:millisecond) - st.started
    heap = div(walk_memory(), 1_048_576)

    IO.puts(
      :stderr,
      "muro synth: considered #{considered} distinct #{st.distinct} #{elapsed} ms heap #{heap} MB"
    )

    st
  end

  defp heartbeat(st), do: st

  defp replace_bank(st, sig, prog_fun, size) do
    if Map.has_key?(st.bank, sig) do
      Map.put(st.bank, sig, {prog_fun.(), size, st.ord})
    else
      st.bank
    end
  end

  defp move_count(counts, old, size) do
    counts
    |> Map.update!(old, &(&1 - 1))
    |> Map.update(size, 1, &(&1 + 1))
  end

  defp trace_begin(%{trace: true} = st, size) do
    elapsed = System.monotonic_time(:millisecond) - st.started

    IO.puts(
      :stderr,
      "muro synth: size #{size} begin considered #{st.considered} distinct #{st.distinct} #{elapsed} ms"
    )
  end

  defp trace_begin(_st, _size), do: :ok

  defp trace_open(n, max_size, k_cap, k_ideal) do
    if trace?() do
      IO.puts(
        :stderr,
        "muro synth: enumerate features #{n} size bound #{max_size} k cap #{k_cap} k ideal #{k_ideal}"
      )
    end
  end

  defp trace_size(st, size, started) do
    if trace?() do
      elapsed = System.monotonic_time(:millisecond) - started
      new = Map.get(st.counts, size, 0)
      heap = div(walk_memory(), 1_048_576)

      IO.puts(
        :stderr,
        "muro synth: size #{size} new #{new} considered #{st.considered} distinct #{st.distinct} #{elapsed} ms heap #{heap} MB"
      )
    end
  end

  defp trace? do
    System.get_env("MURO_SYNTH_TRACE") in ["1", "true"]
  end

  defp shrink_k(_n, k) when not is_integer(k) or k < 2, do: 0

  defp shrink_k(n, k) do
    if binom(n, k) > @subset_budget, do: shrink_k(n, k - 1), else: k
  end

  defp binom(_n, 0), do: 1
  defp binom(n, k) when k < 0 or n < 0 or k > n, do: 0

  defp binom(n, k) do
    k = min(k, n - k)

    if k == 0 do
      1
    else
      Enum.reduce(1..k, 1, fn i, acc -> div(acc * (n - k + i), i) end)
    end
  end

  # A stem column that is not a feat atom still needs a signature:
  # `self` and `other` read it, and a missing signature is refused
  # rather than treated as false.
  defp family_column_sigs(sigs, families, sig_fun) do
    Enum.reduce(families, sigs, fn family, sigs ->
      Enum.reduce(family.actions, sigs, fn action, sigs ->
        feature = family_column!(family, family.by_action, action)
        key = {:feat, feature}

        if Map.has_key?(sigs, key) do
          sigs
        else
          Map.put(sigs, key, sig_fun.(key))
        end
      end)
    end)
  end

  # `self` reads the action's own column. `other` is the pointwise
  # disjunction of the other actions in the family. The feature list is
  # the action set, not a nest of constructors, so both atoms have size 1.
  # Every column of a family must have a signature. A column without one
  # is not dropped: dropping it would change what `other` means at every
  # sibling action, so the walk refuses the family instead.
  defp quantifier_atoms(families, sigs) do
    pairs =
      Enum.flat_map(families, fn family ->
        actions = family.actions
        by = family.by_action
        columns = Enum.map(actions, &family_column!(family, by, &1))

        case Enum.reject(columns, &Map.has_key?(sigs, {:feat, &1})) do
          [] ->
            :ok

          missing ->
            raise ArgumentError,
                  "action family #{family.stem} has columns with no signature: " <>
                    Enum.join(missing, ", ")
        end

        Enum.flat_map(actions, fn action ->
          feature = Map.fetch!(by, action)
          others = for other <- actions, other != action, do: Map.fetch!(by, other)
          self = {:self, family.stem, action, feature}
          other = {:other, family.stem, action, others}
          self_sig = Map.fetch!(sigs, {:feat, feature})

          other_sig =
            Enum.reduce(others, 0, fn name, acc ->
              Bitwise.bor(acc, Map.fetch!(sigs, {:feat, name}))
            end)

          [{self, self_sig}, {other, other_sig}]
        end)
      end)

    {Enum.map(pairs, &elem(&1, 0)), Map.new(pairs)}
  end

  defp family_column!(family, by, action) do
    case Map.fetch(by, action) do
      {:ok, feature} ->
        feature

      :error ->
        raise ArgumentError,
              "action family #{family.stem} lists #{action} with no column"
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

  defp any_column([], _feat, _state, fuel), do: {:ok, false, fuel}

  defp any_column([feature | rest], feat, state, fuel) do
    case charge(fuel) do
      :out_of_fuel ->
        :out_of_fuel

      {:ok, left} ->
        if feat.(feature, state) do
          {:ok, true, left}
        else
          any_column(rest, feat, state, left)
        end
    end
  end

  defp charge(:infinity), do: {:ok, :infinity}
  defp charge(fuel) when is_integer(fuel) and fuel > 0, do: {:ok, fuel - 1}
  defp charge(fuel) when is_integer(fuel) and fuel <= 0, do: :out_of_fuel
end

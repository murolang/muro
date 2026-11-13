defmodule Muro.Synth.Cert do
  @moduledoc false

  # The ranking and its homomorphism, checked on the surviving predicate
  # against the environment's `step`. `solve s n` is the best immediate
  # reward among states reached in n steps. On a finite `State` each
  # component is one of a finite set of closed Nat rewards, so the
  # vector repeats. A transient of 0 and a period of 1 is a constant at
  # every state. Any other shape is a finite prefix and then a constant
  # or a repeating tail. The tail comparison rewrites that closed form.
  # `rank` is Unit when the predicate prefers the action and Empty when
  # it does not. The evidence is the case split. The walk that finds the
  # period is the pigeonhole on that finite set. It is not a fuel bound.
  # The evidence inducts on `n`.

  def target("successor"), do: "CoinductiveHomomorphism"
  def target(_oracle), do: "CoindHomo"

  @doc """
  The certificate text, or a reason it was not generated.

  `{:ok, text, obligations}` appends a ranking the checker can accept.
  `{:skip, reason}` leaves the policy book without a ranking.
  """
  def render(host, arms, oracle, bound) do
    needed = [target(oracle) | support(oracle)]

    case missing(host, needed) do
      [name | _] ->
        {:skip, "the environment does not define #{name}"}

      [] ->
        case vocabulary(host) do
          {:error, reason} ->
            {:skip, reason}

          {:ok, vocab} ->
            case classify(host) do
              {:error, reason} ->
                {:skip, reason}

              {:constant, values, settled} ->
                build(host, arms, oracle, vocab, values, settled, bound)

              {:periodic, orbit} ->
                build_periodic(host, arms, oracle, vocab, orbit, bound)
            end
        end
    end
  end

  defp support("successor") do
    ["successor-value", "value", "solve", "dom-refl", "tabulate-dom", "le-refl"]
  end

  defp support(_oracle) do
    ["action-value", "action-at", "value", "solve", "dom-refl", "tabulate-dom", "le-refl"]
  end

  defp missing(host, names) do
    Enum.reject(names, &defined?(host, &1))
  end

  defp defined?(host, name), do: Enum.any?(host.book, &(Map.get(&1, :name) == name))

  defp vocabulary(host) do
    with {:ok, max_name} <- spell_body(body(host, "max")),
         {:ok, bottom} <- spell_body(body(host, "bottom")),
         {:ok, reward} <- spell_body(body(host, "Reward")) do
      {:ok, %{max: max_name, bottom: bottom, reward: reward}}
    else
      :error -> {:error, "max, bottom, or Reward does not unfold to a name"}
    end
  end

  defp body(host, name) do
    case Enum.find(host.book, &(Map.get(&1, :name) == name)) do
      %{body: body} -> body
      _ -> nil
    end
  end

  defp spell_body(:ze), do: {:ok, "0"}
  defp spell_body(:nat), do: {:ok, "Nat"}
  defp spell_body({:var, name}), do: {:ok, name}
  defp spell_body(_body), do: :error

  # The first repeated vector is `seq` at `i`. `seq` stores indices
  # `0 .. transient + period - 1` and does not store the duplicate.
  # A transient of 0 and a period of 1 is the constant certificate.
  defp classify(host) do
    states = constructors(host, "State")
    actions = host.actions

    with {:ok, now} <- vector(host, states, actions, &reward(host, &1, &2)) do
      if Enum.all?(Map.values(now), &closed_nat?/1) do
        walk(host, states, actions, [now], %{key(now, states) => 0})
      else
        {:error, "reward is not a closed Nat"}
      end
    end
  end

  defp walk(host, states, actions, seq, seen) do
    last = List.last(seq)

    case vector(host, states, actions, fn state, action ->
           last[next(host, state, action)]
         end) do
      {:error, reason} ->
        {:error, reason}

      {:ok, nxt} ->
        case Map.fetch(seen, key(nxt, states)) do
          {:ok, i} ->
            transient = i
            period = length(seq) - i

            if transient == 0 and period == 1 do
              {:constant, hd(seq), MapSet.new(states)}
            else
              {:periodic, %{transient: transient, period: period, seq: seq, states: states}}
            end

          :error ->
            walk(
              host,
              states,
              actions,
              seq ++ [nxt],
              Map.put(seen, key(nxt, states), length(seq))
            )
        end
    end
  end

  defp key(vector, states), do: Enum.map(states, &nat_int(vector[&1]))

  defp at(%{transient: t, period: p, seq: seq}, n) do
    idx = if n < t, do: n, else: t + rem(n - t, p)
    Enum.at(seq, idx)
  end

  # Earliest index at or before the transient from which one step of the
  # period no longer changes this component. The transient itself always
  # qualifies: the range above it is empty.
  defp onset(orbit, state) do
    t = orbit.transient
    p = orbit.period

    Enum.find(0..t, fn start ->
      Enum.all?(start..(t - 1)//1, fn n ->
        nat_int(at(orbit, n + p)[state]) == nat_int(at(orbit, n)[state])
      end)
    end)
  end

  defp vector(host, states, actions, fun) do
    Enum.reduce_while(states, {:ok, %{}}, fn state, {:ok, acc} ->
      case maximum(host, Enum.map(actions, &fun.(state, &1))) do
        {:ok, value} -> {:cont, {:ok, Map.put(acc, state, value)}}
        :unordered -> {:halt, {:error, "the rewards at #{state} have no maximum"}}
      end
    end)
  end

  defp maximum(host, rewards) do
    case Muro.Synth.Oracle.maximum_reward(host.leb, rewards) do
      :unordered -> :unordered
      value -> {:ok, value}
    end
  end

  defp reward(host, state, action), do: elem(host.step.(state, action), 1)
  defp next(host, state, action), do: elem(host.step.(state, action), 0)

  defp constructors(host, data) do
    %{ctors: ctors} = Enum.find(host.book, &(Map.get(&1, :kind) == :data and &1.name == data))
    Enum.map(ctors, & &1.name)
  end

  defp build(host, arms, oracle, vocab, values, settled, bound) do
    states = constructors(host, "State")
    actions = constructors(host, "Action")
    taken = bound.taken
    {rank, taken} = Muro.Synth.Book.reserve("rank", taken)
    {solves, taken} = solve_names(states, taken)
    primary = primary(oracle)
    extra? = extra_homo?(host, oracle, states, actions, arms, values)

    {below, taken, below_obs, below_names} =
      below_lemmas(host, arms, states, actions, vocab, values, solves, primary, taken)

    {more_below, taken, more_below_obs, more_below_names} =
      if extra? do
        below_lemmas(host, arms, states, actions, vocab, values, solves, :action, taken)
      else
        {[], taken, [], %{}}
      end

    {leaves, taken, leaf_obs, leaf_names} =
      leaf_lemmas(host, arms, states, actions, rank, primary, below_names, taken)

    {more_leaves, taken, more_leaf_obs, more_leaf_names} =
      if extra? do
        leaf_lemmas(host, arms, states, actions, rank, :action, more_below_names, taken)
      else
        {[], taken, [], %{}}
      end

    {preserves, taken} = Muro.Synth.Book.reserve("preserves", taken)

    {extra_preserves, _taken} =
      if extra?,
        do: Muro.Synth.Book.reserve("preserves-coind", taken),
        else: {nil, taken}

    text =
      [
        solves_text(host, states, vocab, values, solves, settled),
        below,
        more_below,
        rank_text(bound, arms, actions, rank),
        leaves,
        more_leaves,
        preserves_text(
          preserves,
          certificate_name(primary),
          states,
          actions,
          rank,
          primary,
          leaf_names
        ),
        if extra? do
          preserves_text(
            extra_preserves,
            "CoindHomo",
            states,
            actions,
            rank,
            :action,
            more_leaf_names
          )
        else
          []
        end
      ]
      |> IO.iodata_to_binary()

    {:ok,
     %{
       text: text,
       obligations: below_obs ++ more_below_obs ++ leaf_obs ++ more_leaf_obs,
       certificate: certificate_name(primary),
       also: if(extra?, do: "CoindHomo")
     }}
  end

  defp primary("successor"), do: :successor
  defp primary(_oracle), do: :action

  defp certificate_name(:successor), do: "CoinductiveHomomorphism"
  defp certificate_name(:action), do: "CoindHomo"

  # A successor certificate claims CoindHomo only when the immediate
  # rewards respect the same ranking. BinarySacrifice does not.
  defp extra_homo?(host, "successor", states, actions, arms, values) do
    defined?(host, "CoindHomo") and defined?(host, "action-value") and
      defined?(host, "action-at") and
      Enum.all?(states, fn state ->
        winner = chosen(host, arms, state)

        Enum.all?(actions, fn left ->
          Enum.all?(actions, fn right ->
            not prefers?(winner, left, right) or head_and_tail?(host, values, state, left, right)
          end)
        end)
      end)
  end

  defp extra_homo?(_host, _oracle, _states, _actions, _arms, _values), do: false

  defp head_and_tail?(host, values, state, left, right) do
    host.leb.(reward(host, state, left), reward(host, state, right)) and
      host.leb.(values[next(host, state, left)], values[next(host, state, right)])
  end

  defp solve_names(states, taken) do
    {pairs, taken} =
      Enum.map_reduce(states, taken, fn state, taken ->
        {name, taken} = Muro.Synth.Book.reserve("cert-solve-#{state}", taken)
        {{state, name}, taken}
      end)

    {Map.new(pairs), taken}
  end

  defp solves_text(host, states, vocab, values, solves, settled) do
    states
    |> Enum.filter(&MapSet.member?(settled, &1))
    |> Enum.map(fn state ->
      name = Map.fetch!(solves, state)
      const = spell_nat(values[state])
      steps = Enum.map(host.actions, &next(host, state, &1))

      """
      def #{name} : evidence Π (n : Nat) → {solve #{state} n ≡ #{const} : #{vocab.reward}} :=
        λ (n : Nat) →
          match n motive (λ (k : Nat) → {solve #{state} k ≡ #{const} : #{vocab.reward}})
            | 0 => refl
            | suc m =>
                #{rewrite_chain(steps, solves, const, vocab, &spell_nat(values[&1]), &"solve #{&1} m")}
      """
    end)
  end

  # One rewrite per distinct successor, outer first in action order.
  # An earlier successor is its right-hand side inside a later rewrite,
  # because that outer rewrite is read at its right-hand side. The current
  # successor is `z` everywhere it occurs. A later one is still `solve`.
  defp rewrite_chain(steps, solves, rhs, vocab, shown, fresh) do
    order = Enum.uniq(steps)
    last = length(order) - 1

    Enum.reduce(last..0//-1, "refl", fn index, acc ->
      state = Enum.at(order, index)
      args = Enum.map(steps, &rewrite_slot(&1, state, index, order, shown, fresh))
      nest = max_nest(args, vocab.max, vocab.bottom)
      lemma = Map.fetch!(solves, state)

      """
      rewrite #{lemma} m motive (λ z → {#{nest} ≡ #{rhs} : #{vocab.reward}}) in
      #{acc}\
      """
      |> String.trim_trailing()
    end)
  end

  defp rewrite_slot(state, current, index, order, shown, fresh) do
    cond do
      state == current -> "z"
      Enum.find_index(order, &(&1 == state)) < index -> shown.(state)
      true -> fresh.(state)
    end
  end

  defp max_nest(args, max_name, bottom) do
    Enum.reduce(Enum.reverse(args), bottom, fn arg, acc ->
      "#{max_name} #{paren(arg)} #{paren(acc)}"
    end)
  end

  defp below_lemmas(host, arms, states, actions, vocab, values, solves, kind, taken) do
    pairs = proof_pairs(host, arms, states, actions, kind)

    Enum.reduce(pairs, {[], taken, [], %{}}, fn {state, left, right}, {text, taken, obs, names} ->
      base = "cert-below-#{kind}-#{state}-#{left}-#{right}"
      {name, taken} = Muro.Synth.Book.reserve(base, taken)
      arm = deciding(host, arms, state)
      bit = bit_at(host, arm, state)

      body =
        case kind do
          :action -> action_below(host, state, left, right, solves, values)
          :successor -> successor_below(host, state, left, right, solves, values, vocab)
        end

      lemma = """
      def #{name} : evidence #{below_type(host, kind, state, left, right)} :=
        #{body}
      """

      ob = obligation(name, state, left, right, arm.name, bit)
      {text ++ [lemma], taken, obs ++ [ob], Map.put(names, {state, left, right}, name)}
    end)
  end

  defp below_type(_host, :action, state, left, right) do
    "Π (n : Nat) → le (action-at #{state} #{left} n) (action-at #{state} #{right} n)"
  end

  defp below_type(host, :successor, state, left, right) do
    left_state = next(host, state, left)
    right_state = next(host, state, right)
    "Π (n : Nat) → le (solve #{left_state} n) (solve #{right_state} n)"
  end

  defp proof_pairs(host, arms, states, actions, kind) do
    for state <- states,
        left <- actions,
        right <- actions,
        winner = chosen(host, arms, state),
        prefers?(winner, left, right),
        needs_below?(host, kind, state, left, right),
        do: {state, left, right}
  end

  # Equal actions are `dom-refl`. A successor pair with one next state
  # is `dom-refl` of that value. Everything else is a pointwise lemma.
  defp needs_below?(_host, _kind, _state, action, action), do: false

  defp needs_below?(host, :successor, state, left, right) do
    next(host, state, left) != next(host, state, right)
  end

  defp needs_below?(_host, :action, _state, _left, _right), do: true

  defp action_below(host, state, left, right, solves, values) do
    tail =
      if next(host, state, left) == next(host, state, right) do
        "le-refl (solve #{next(host, state, left)} m)"
      else
        left_state = next(host, state, left)
        right_state = next(host, state, right)
        const = spell_nat(values[left_state])

        """
        rewrite #{solves[left_state]} m motive (λ z → le z (solve #{right_state} m)) in
        rewrite #{solves[right_state]} m motive (λ z → le #{paren(const)} z) in tt\
        """
      end

    """
    λ (n : Nat) →
      match n motive (λ (k : Nat) → le (action-at #{state} #{left} k) (action-at #{state} #{right} k))
        | 0 => tt
        | suc m =>
            #{tail}\
    """
  end

  defp successor_below(host, state, left, right, solves, values, _vocab) do
    left_state = next(host, state, left)
    right_state = next(host, state, right)
    const = spell_nat(values[left_state])

    """
    λ (n : Nat) →
      rewrite #{solves[left_state]} n motive (λ z → le z (solve #{right_state} n)) in
      rewrite #{solves[right_state]} n motive (λ z → le #{paren(const)} z) in tt\
    """
  end

  defp leaf_lemmas(host, arms, states, actions, rank, kind, below, taken) do
    cells =
      for state <- states, left <- actions, right <- actions do
        {state, left, right}
      end

    Enum.reduce(cells, {[], taken, [], %{}}, fn {state, left, right}, {text, taken, obs, names} ->
      base = "cert-leaf-#{kind}-#{state}-#{left}-#{right}"
      {name, taken} = Muro.Synth.Book.reserve(base, taken)
      arm = deciding(host, arms, state)
      bit = bit_at(host, arm, state)
      winner = chosen(host, arms, state)
      body = leaf_body(host, kind, state, left, right, winner, below)

      lemma = """
      def #{name} : evidence #{leaf_type(kind, rank, state, left, right)} :=
        #{body}
      """

      ob = obligation(name, state, left, right, arm.name, bit)
      {text ++ [lemma], taken, obs ++ [ob], Map.put(names, {state, left, right}, name)}
    end)
  end

  defp leaf_type(kind, rank, state, left, right) do
    fun = stream_fun(kind)

    "Π (r : #{rank} #{state} #{left} #{right}) → Dom Reward le (#{fun} #{state} #{left}) (#{fun} #{state} #{right})"
  end

  defp leaf_body(host, kind, state, left, right, winner, below) do
    cond do
      not unit?(winner, left, right) ->
        empty_body(kind, state, left, right)

      not needs_below?(host, kind, state, left, right) ->
        dom_refl(kind, host, state, left)

      true ->
        tabulate(kind, host, state, left, right, Map.fetch!(below, {state, left, right}))
    end
  end

  defp unit?(winner, left, right), do: left == right or prefers?(winner, left, right)

  defp empty_body(kind, state, left, right) do
    "λ (r : Empty) → matchEmpty r motive (λ _ → Dom Reward le (#{stream(kind, state, left)}) (#{stream(kind, state, right)}))"
  end

  defp dom_refl(:action, _host, state, action) do
    "λ (r : Unit) → dom-refl Reward le le-refl (action-value #{state} #{action})"
  end

  defp dom_refl(:successor, host, state, action) do
    "λ (r : Unit) → dom-refl Reward le le-refl (value #{next(host, state, action)})"
  end

  defp tabulate(:action, _host, state, left, right, lemma) do
    "λ (r : Unit) → tabulate-dom Reward le (λ (n : Nat) → action-at #{state} #{left} n) (λ (n : Nat) → action-at #{state} #{right} n) #{lemma} 0"
  end

  defp tabulate(:successor, host, state, left, right, lemma) do
    left_state = next(host, state, left)
    right_state = next(host, state, right)

    "λ (r : Unit) → tabulate-dom Reward le (λ (n : Nat) → solve #{left_state} n) (λ (n : Nat) → solve #{right_state} n) #{lemma} 0"
  end

  defp stream(kind, state, action), do: "#{stream_fun(kind)} #{state} #{action}"
  defp stream_fun(:action), do: "action-value"
  defp stream_fun(:successor), do: "successor-value"

  defp obligation(name, state, left, right, arm, bit) do
    %{
      name: name,
      carrier: state,
      oracle: bit,
      pair: {left, right},
      claimed: bit,
      kind: :certificate,
      arm: arm
    }
  end

  defp chosen(host, arms, state) do
    case Enum.find(arms, &bit_at(host, &1, state)) do
      nil -> List.last(arms).else
      arm -> arm.action
    end
  end

  defp deciding(host, arms, state) do
    Enum.find(arms, List.last(arms), &bit_at(host, &1, state))
  end

  defp bit_at(host, arm, state) do
    case Enum.find(arm.observations, &(elem(&1, 0) == state)) do
      {_state, bit} -> bit
      nil -> Muro.Synth.eval(arm.pred, &host.eval_feature.(&1, &2), state)
    end
  end

  # `right` is at least as preferred as `left`, and the two differ.
  # Equals are not a dominance obligation.
  defp prefers?(winner, left, right) do
    left != right and right == winner
  end

  defp closed_nat?(0), do: true
  defp closed_nat?({:suc, n}), do: closed_nat?(n)
  defp closed_nat?(n) when is_integer(n) and n >= 0, do: true
  defp closed_nat?(_value), do: false

  defp spell_nat(0), do: "0"
  defp spell_nat({:suc, n}), do: spell_nat(nat_int({:suc, n}))

  defp spell_nat(n) when is_integer(n) and n > 0 do
    rest = spell_nat(n - 1)
    if rest == "0", do: "suc 0", else: "suc (" <> rest <> ")"
  end

  defp nat_int(0), do: 0
  defp nat_int({:suc, n}), do: 1 + nat_int(n)
  defp nat_int(n) when is_integer(n) and n >= 0, do: n

  defp paren(term) do
    if String.contains?(term, " ") or String.contains?(term, "("), do: "(#{term})", else: term
  end

  defp rank_text(bound, arms, actions, rank) do
    """
    def #{rank} : spec Π (s : State) → Π (a : Action) → Π (b : Action) → Type :=
      λ (s : State) → λ (a : Action) → λ (b : Action) →
        #{rank_match(bound, arms, actions)}
    """
  end

  defp rank_match(bound, [arm], actions) do
    decl = Map.fetch!(bound.decl, arm.name)

    """
    (match #{bound.names.eval} #{decl} s motive (λ _ → Type)
      | true =>
          #{prefer(actions, arm.action)}
      | false =>
          #{prefer(actions, arm.else)})
    """
  end

  defp rank_match(bound, [arm | rest], actions) do
    decl = Map.fetch!(bound.decl, arm.name)

    """
    (match #{bound.names.eval} #{decl} s motive (λ _ → Type)
      | true =>
          #{prefer(actions, arm.action)}
      | false =>
          #{rank_match(bound, rest, actions)})
    """
  end

  defp prefer(actions, winner) do
    branches =
      Enum.map_join(actions, "\n", fn left ->
        rights =
          Enum.map_join(actions, "\n", fn right ->
            cell = if unit?(winner, left, right), do: "Unit", else: "Empty"
            "        | #{right} => #{cell}"
          end)

        """
        | #{left} =>
            (match b motive (λ _ → Type)
        #{rights})
        """
      end)

    """
    (match a motive (λ _ → Type)
    #{branches})
    """
  end

  defp preserves_text(name, target, states, actions, rank, kind, leaves) do
    fun = stream_fun(kind)

    """
    def #{name} : evidence #{target} #{rank} :=
      λ (a : Action) → λ (b : Action) → λ (s : State) →
        match s motive (λ (x : State) → Π (r : #{rank} x a b) → Dom Reward le (#{fun} x a) (#{fun} x b))
    #{Enum.map_join(states, "\n", &state_branch(&1, actions, rank, kind, leaves))}
    """
  end

  defp state_branch(state, actions, rank, kind, leaves) do
    fun = stream_fun(kind)

    arms =
      Enum.map_join(actions, "\n", fn left ->
        rights =
          Enum.map_join(actions, "\n", fn right ->
            "            | #{right} => #{Map.fetch!(leaves, {state, left, right})}"
          end)

        """
        | #{left} =>
            (match b motive (λ (z : Action) → Π (r : #{rank} #{state} #{left} z) → Dom Reward le (#{fun} #{state} #{left}) (#{fun} #{state} z))
        #{rights})
        """
      end)

    """
    | #{state} =>
        (match a motive (λ (y : Action) → Π (r : #{rank} #{state} y b) → Dom Reward le (#{fun} #{state} y) (#{fun} #{state} b))
    #{arms})
    """
  end

  # A transient of 0 and a period of 1 is `build/7`. Every other finite
  # orbit is a closed form. The lemmas are general: the state names are
  # the environment's constructors.
  defp build_periodic(host, arms, oracle, vocab, orbit, bound) do
    states = orbit.states
    actions = constructors(host, "Action")
    taken = bound.taken
    {rank, taken} = Muro.Synth.Book.reserve("rank", taken)
    {forms, solves, taken} = form_text(host, vocab, orbit, taken)
    primary = primary(oracle)
    extra? = extra_periodic?(host, oracle, states, actions, arms, orbit)

    {below, taken, below_obs, below_names} =
      below_periodic(host, arms, states, actions, orbit, solves, primary, taken)

    {more_below, taken, more_below_obs, more_below_names} =
      if extra? do
        below_periodic(host, arms, states, actions, orbit, solves, :action, taken)
      else
        {[], taken, [], %{}}
      end

    {leaves, taken, leaf_obs, leaf_names} =
      leaf_lemmas(host, arms, states, actions, rank, primary, below_names, taken)

    {more_leaves, taken, more_leaf_obs, more_leaf_names} =
      if extra? do
        leaf_lemmas(host, arms, states, actions, rank, :action, more_below_names, taken)
      else
        {[], taken, [], %{}}
      end

    {preserves, taken} = Muro.Synth.Book.reserve("preserves", taken)

    {extra_preserves, _taken} =
      if extra?,
        do: Muro.Synth.Book.reserve("preserves-coind", taken),
        else: {nil, taken}

    text =
      [
        forms,
        below,
        more_below,
        rank_text(bound, arms, actions, rank),
        leaves,
        more_leaves,
        preserves_text(
          preserves,
          certificate_name(primary),
          states,
          actions,
          rank,
          primary,
          leaf_names
        ),
        if extra? do
          preserves_text(
            extra_preserves,
            "CoindHomo",
            states,
            actions,
            rank,
            :action,
            more_leaf_names
          )
        else
          []
        end
      ]
      |> IO.iodata_to_binary()

    {:ok,
     %{
       text: text,
       obligations: below_obs ++ more_below_obs ++ leaf_obs ++ more_leaf_obs,
       certificate: certificate_name(primary),
       also: if(extra?, do: "CoindHomo")
     }}
  end

  # Whole action-value streams, not the value at step 0. A successor
  # ranking claims CoindHomo only when those streams respect it.
  defp extra_periodic?(host, "successor", states, actions, arms, orbit) do
    defined?(host, "CoindHomo") and defined?(host, "action-value") and
      defined?(host, "action-at") and
      Enum.all?(states, fn state ->
        winner = chosen(host, arms, state)

        Enum.all?(actions, fn left ->
          Enum.all?(actions, fn right ->
            not prefers?(winner, left, right) or
              streams_ordered?(host, orbit, state, left, right)
          end)
        end)
      end)
  end

  defp extra_periodic?(_host, _oracle, _states, _actions, _arms, _orbit), do: false

  defp streams_ordered?(host, orbit, state, left, right) do
    host.leb.(reward(host, state, left), reward(host, state, right)) and
      Enum.all?(0..(orbit.transient + orbit.period - 1), fn n ->
        left_state = next(host, state, left)
        right_state = next(host, state, right)
        host.leb.(at(orbit, n)[left_state], at(orbit, n)[right_state])
      end)
  end

  defp form_text(host, vocab, orbit, taken) do
    {plans, taken} =
      Enum.map_reduce(orbit.states, taken, fn state, taken ->
        plan_state(orbit, state, taken)
      end)

    solves = Map.new(plans, &{&1.state, &1.lemma})

    lemmas =
      if orbit.period == 1 do
        Enum.map(plans, &aligned_text(host, &1, vocab, orbit, solves))
      else
        Enum.map(plans, &repeat_text(host, &1, vocab, orbit, solves))
      end

    text =
      Enum.map(plans, &prefix_text(&1, vocab)) ++
        lemmas ++ Enum.map(plans, &wrapper_text(&1, vocab, orbit.transient))

    {text, solves, taken}
  end

  defp plan_state(orbit, state, taken) do
    t = orbit.transient
    p = orbit.period

    if p == 1 do
      start = onset(orbit, state)
      base = if start == t, do: "cert-solve-#{state}", else: "cert-solve-#{state}-tail"

      {lemma, taken} = Muro.Synth.Book.reserve(base, taken)

      {wrapper, taken} =
        cond do
          start == t -> {nil, taken}
          start == 0 -> Muro.Synth.Book.reserve("cert-solve-#{state}", taken)
          true -> Muro.Synth.Book.reserve("cert-solve-#{state}-from", taken)
        end

      {prefixes, taken} = prefix_names(state, 0..(start - 1)//1, orbit, taken)

      plan = %{
        state: state,
        onset: start,
        lemma: lemma,
        wrapper: wrapper,
        prefixes: prefixes,
        const: at(orbit, t)[state]
      }

      {plan, taken}
    else
      {lemma, taken} = Muro.Synth.Book.reserve("cert-solve-#{state}-rep", taken)
      {prefixes, taken} = prefix_names(state, 0..(t + p - 1), orbit, taken)

      plan = %{
        state: state,
        onset: nil,
        lemma: lemma,
        wrapper: nil,
        prefixes: prefixes,
        const: nil
      }

      {plan, taken}
    end
  end

  defp prefix_names(state, range, orbit, taken) do
    Enum.map_reduce(range, taken, fn k, taken ->
      {name, taken} = Muro.Synth.Book.reserve("cert-solve-#{state}-#{k}", taken)
      {{name, k, at(orbit, k)[state]}, taken}
    end)
  end

  defp prefix_text(plan, vocab) do
    Enum.map(plan.prefixes, fn {name, k, value} ->
      evidence_def(
        name,
        "{solve #{plan.state} #{nat_arg(k)} ≡ #{spell_nat(value)} : #{vocab.reward}}",
        "refl"
      )
    end)
  end

  defp aligned_text(host, plan, vocab, orbit, solves) do
    const = spell_nat(plan.const)
    t = orbit.transient

    type =
      "Π (n : Nat) → {solve #{plan.state} #{shift_term("n", t)} ≡ #{const} : #{vocab.reward}}"

    evidence_def(plan.lemma, type, aligned_body(host, plan.state, vocab, orbit, solves, const))
  end

  defp aligned_body(host, state, vocab, orbit, solves, const) do
    t = orbit.transient
    steps = Enum.map(host.actions, &next(host, state, &1))
    rhs = const
    shown = fn succ -> spell_nat(at(orbit, t)[succ]) end
    fresh = fn succ -> "solve #{succ} #{shift_term("m", t)}" end
    chain = rewrite_chain(steps, solves, rhs, vocab, shown, fresh)
    goal = fn var -> "solve #{state} #{shift_term(var, t)} ≡ #{const} : #{vocab.reward}" end

    """
    λ (n : Nat) →
      match n motive (λ (k : Nat) → {#{goal.("k")}})
        | 0 => refl
        | suc m =>
            #{chain}
    """
  end

  defp repeat_text(host, plan, vocab, orbit, solves) do
    t = orbit.transient
    p = orbit.period
    left = "solve #{plan.state} #{shift_term("n", t + p)}"
    right = "solve #{plan.state} #{shift_term("n", t)}"
    type = "Π (n : Nat) → {#{left} ≡ #{right} : #{vocab.reward}}"
    evidence_def(plan.lemma, type, repeat_body(host, plan.state, vocab, orbit, solves))
  end

  defp repeat_body(host, state, vocab, orbit, solves) do
    t = orbit.transient
    p = orbit.period
    steps = Enum.map(host.actions, &next(host, state, &1))
    rhs = "solve #{state} #{shift_term("m", t + 1)}"
    shown = fn succ -> "solve #{succ} #{shift_term("m", t)}" end
    fresh = fn succ -> "solve #{succ} #{shift_term("m", t + p)}" end
    chain = rewrite_chain(steps, solves, rhs, vocab, shown, fresh)

    eq = fn var ->
      "solve #{state} #{shift_term(var, t + p)} ≡ solve #{state} #{shift_term(var, t)} : #{vocab.reward}"
    end

    """
    λ (n : Nat) →
      match n motive (λ (k : Nat) → {#{eq.("k")}})
        | 0 => refl
        | suc m =>
            #{chain}
    """
  end

  defp wrapper_text(%{wrapper: nil}, _vocab, _t), do: []

  defp wrapper_text(plan, vocab, t) do
    const = spell_nat(plan.const)

    type =
      "Π (n : Nat) → {solve #{plan.state} #{shift_term("n", plan.onset)} ≡ #{const} : #{vocab.reward}}"

    body = """
    λ (n : Nat) →
      #{peel(plan.state, plan.lemma, const, vocab.reward, plan.onset, t, "n")}
    """

    evidence_def(plan.wrapper, type, body)
  end

  defp peel(_state, lemma, _const, _reward, onset, t, var) when onset >= t do
    "#{lemma} #{var}"
  end

  defp peel(state, lemma, const, reward, onset, t, var) do
    nxt = "m#{onset}"
    idx = shift_term("k", onset)

    """
    (match #{var} motive (λ (k : Nat) → {solve #{state} #{idx} ≡ #{const} : #{reward}})
      | 0 => refl
      | suc #{nxt} =>
          #{peel(state, lemma, const, reward, onset + 1, t, nxt)})
    """
  end

  defp below_periodic(host, arms, states, actions, orbit, solves, kind, taken) do
    pairs = proof_pairs(host, arms, states, actions, kind)

    Enum.reduce(pairs, {[], taken, [], %{}}, fn {state, left, right}, {text, taken, obs, names} ->
      base = "cert-below-#{kind}-#{state}-#{left}-#{right}"
      {name, taken} = Muro.Synth.Book.reserve(base, taken)
      arm = deciding(host, arms, state)
      ob = obligation(name, state, left, right, arm.name, bit_at(host, arm, state))

      {prelude, body, taken, more} =
        form_below(host, kind, state, left, right, orbit, solves, name, taken, ob)

      lemma = evidence_def(name, below_type(host, kind, state, left, right), body)
      {text ++ prelude ++ [lemma], taken, obs ++ more, Map.put(names, {state, left, right}, name)}
    end)
  end

  defp form_below(host, :action, state, left, right, orbit, solves, _name, taken, ob) do
    if next(host, state, left) == next(host, state, right) do
      {[], action_form_body(host, state, left, right, nil), taken, [ob]}
    else
      tag = "action-#{state}-#{left}-#{right}"
      {le_name, taken} = Muro.Synth.Book.reserve("cert-le-#{tag}", taken)
      le_ob = %{ob | name: le_name}
      next_l = next(host, state, left)
      next_r = next(host, state, right)

      {prelude, le_body, taken, le_obs} =
        compare_of(le_name, next_l, next_r, orbit, solves, taken, le_ob, tag)

      le_ty = "Π (n : Nat) → le (solve #{next_l} n) (solve #{next_r} n)"
      defs = prelude ++ [evidence_def(le_name, le_ty, le_body)]
      {defs, action_form_body(host, state, left, right, le_name), taken, le_obs ++ [ob]}
    end
  end

  defp form_below(host, :successor, state, left, right, orbit, solves, name, taken, ob) do
    tag = "successor-#{state}-#{left}-#{right}"
    next_l = next(host, state, left)
    next_r = next(host, state, right)
    compare_of(name, next_l, next_r, orbit, solves, taken, ob, tag)
  end

  defp action_form_body(host, state, left, right, call) do
    tail =
      if call == nil do
        "le-refl (solve #{next(host, state, left)} m)"
      else
        "#{call} m"
      end

    """
    λ (n : Nat) →
      match n motive (λ (k : Nat) → le (action-at #{state} #{left} k) (action-at #{state} #{right} k))
        | 0 => tt
        | suc m =>
            #{tail}
    """
  end

  # `name` is the definition whose body this returns. A period greater
  # than 1 with a transient emits the repeating tail first and calls it
  # after the prefix has been matched away.
  defp compare_of(name, left, right, orbit, solves, taken, ob, tag) do
    t = orbit.transient
    p = orbit.period

    cond do
      p == 1 ->
        body = """
        λ (n : Nat) →
          #{const_nest(left, right, solves, at(orbit, t)[left], t, "n", 0)}
        """

        {[], body, taken, [ob]}

      t == 0 ->
        body = """
        λ (n : Nat) →
          #{cycle_nest(left, right, solves, 0, p, name, "n", 0)}
        """

        {[], body, taken, [ob]}

      true ->
        {cycle, taken} = Muro.Synth.Book.reserve("cert-cycle-#{tag}", taken)

        cycle_ty =
          "Π (n : Nat) → le (solve #{left} #{shift_term("n", t)}) (solve #{right} #{shift_term("n", t)})"

        cycle_body = """
        λ (n : Nat) →
          #{cycle_nest(left, right, solves, t, p, cycle, "n", 0)}
        """

        outer = """
        λ (n : Nat) →
          #{transient_nest(left, right, t, cycle, "n", 0)}
        """

        {[evidence_def(cycle, cycle_ty, cycle_body)], outer, taken, [%{ob | name: cycle}, ob]}
    end
  end

  defp const_nest(left, right, solves, const_left, t, var, depth) when depth == t do
    idx = shift_term(var, t)
    shown = spell_nat(const_left)

    """
    rewrite #{solves[left]} #{var} motive (λ z → le z (solve #{right} #{idx})) in
    rewrite #{solves[right]} #{var} motive (λ z → le #{paren(shown)} z) in tt\
    """
    |> String.trim_trailing()
  end

  defp const_nest(left, right, solves, const_left, t, var, depth) do
    nxt = if depth == t - 1, do: "m", else: "k#{depth}"
    idx = shift_term("k", depth)

    """
    (match #{var} motive (λ (k : Nat) → le (solve #{left} #{idx}) (solve #{right} #{idx}))
      | 0 => tt
      | suc #{nxt} =>
          #{const_nest(left, right, solves, const_left, t, nxt, depth + 1)})
    """
  end

  defp cycle_nest(left, right, solves, t, p, self_name, var, depth) when depth == p do
    big = shift_term(var, t + p)
    small = shift_term(var, t)

    """
    rewrite #{solves[left]} #{var} motive (λ z → le z (solve #{right} #{big})) in
    rewrite #{solves[right]} #{var} motive (λ z → le (solve #{left} #{small}) z) in
    #{self_name} #{var}\
    """
    |> String.trim_trailing()
  end

  defp cycle_nest(left, right, solves, t, p, self_name, var, depth) do
    nxt = if depth == p - 1, do: "m", else: "k#{depth}"
    idx = shift_term("k", t + depth)

    """
    (match #{var} motive (λ (k : Nat) → le (solve #{left} #{idx}) (solve #{right} #{idx}))
      | 0 => tt
      | suc #{nxt} =>
          #{cycle_nest(left, right, solves, t, p, self_name, nxt, depth + 1)})
    """
  end

  defp transient_nest(_left, _right, t, cycle, var, depth) when depth == t, do: "#{cycle} #{var}"

  defp transient_nest(left, right, t, cycle, var, depth) do
    nxt = if depth == t - 1, do: "m", else: "k#{depth}"
    idx = shift_term("k", depth)

    """
    (match #{var} motive (λ (k : Nat) → le (solve #{left} #{idx}) (solve #{right} #{idx}))
      | 0 => tt
      | suc #{nxt} =>
          #{transient_nest(left, right, t, cycle, nxt, depth + 1)})
    """
  end

  defp evidence_def(name, type, body) do
    """
    def #{name} : evidence #{type} :=
      #{body}
    """
  end

  defp shift_term(var, 0), do: var
  defp shift_term(var, n) when n > 0, do: "(" <> shift_raw(var, n) <> ")"
  defp shift_raw(var, 1), do: "suc " <> var
  defp shift_raw(var, n) when n > 1, do: "suc " <> shift_term(var, n - 1)

  defp nat_arg(n) do
    term = spell_nat(n)
    if term == "0", do: "0", else: paren(term)
  end
end

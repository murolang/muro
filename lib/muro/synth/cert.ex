defmodule Muro.Synth.Cert do
  @moduledoc false

  # The ranking and its homomorphism, for a finite state type whose
  # `solve` is constant. `rank` reads the surviving predicate: Unit when
  # that predicate prefers the action, Empty when it does not. The
  # evidence is the case split over states and actions. It is checked
  # on the environment's `step`, the same function the search called.

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
            case constants(host) do
              {:error, reason} -> {:skip, reason}
              {:ok, values} -> build(host, arms, oracle, vocab, values, bound)
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

  # `solve s n` is the best immediate reward among states reached in n
  # steps. On these environments that reward does not depend on n: the
  # vector of immediate maxima is a fixed point of stepping.
  defp constants(host) do
    states = constructors(host, "State")
    actions = host.actions

    with {:ok, now} <- vector(host, states, actions, &reward(host, &1, &2)) do
      if Enum.all?(Map.values(now), &closed_nat?/1) do
        later =
          vector(host, states, actions, fn state, action ->
            now[next(host, state, action)]
          end)

        case later do
          {:ok, ^now} ->
            {:ok, now}

          {:ok, other} ->
            state = Enum.find(states, &(now[&1] != other[&1]))
            {:error, "solve at #{state} is not constant"}

          {:error, reason} ->
            {:error, reason}
        end
      else
        {:error, "reward is not a closed Nat"}
      end
    end
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

  defp build(host, arms, oracle, vocab, values, bound) do
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
        solves_text(host, states, vocab, values, solves),
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

  defp solves_text(host, states, vocab, values, solves) do
    Enum.map(states, fn state ->
      name = Map.fetch!(solves, state)
      const = spell_nat(values[state])
      steps = Enum.map(host.actions, &next(host, state, &1))

      """
      def #{name} : evidence Π (n : Nat) → {solve #{state} n ≡ #{const} : #{vocab.reward}} :=
        λ (n : Nat) →
          match n motive (λ (k : Nat) → {solve #{state} k ≡ #{const} : #{vocab.reward}})
            | 0 => refl
            | suc m =>
                #{rewrite_chain(steps, solves, values, const, vocab)}
      """
    end)
  end

  # One rewrite per distinct successor, outer first in action order.
  # An earlier successor is its constant inside a later rewrite, because
  # that outer rewrite is read at its right-hand side. The current
  # successor is `z` everywhere it occurs. A later one is still `solve`.
  defp rewrite_chain(steps, solves, values, const, vocab) do
    order = Enum.uniq(steps)
    last = length(order) - 1

    Enum.reduce(last..0//-1, "refl", fn index, acc ->
      state = Enum.at(order, index)
      args = Enum.map(steps, &rewrite_arg(&1, state, index, order, values))
      nest = max_nest(args, vocab.max, vocab.bottom)
      lemma = Map.fetch!(solves, state)

      """
      rewrite #{lemma} m motive (λ z → {#{nest} ≡ #{const} : #{vocab.reward}}) in
      #{acc}\
      """
      |> String.trim_trailing()
    end)
  end

  defp rewrite_arg(state, current, index, order, values) do
    cond do
      state == current -> "z"
      Enum.find_index(order, &(&1 == state)) < index -> spell_nat(values[state])
      true -> "solve #{state} m"
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
end

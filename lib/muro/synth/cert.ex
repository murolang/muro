defmodule Muro.Synth.Cert do
  alias Muro.Synth.Names
  @moduledoc false

  alias Muro.Synth.Term

  # The ranking and its homomorphism, checked on the surviving predicate
  # against the environment's `step`. `solve s n` is the best immediate
  # reward among states reached in n steps. On a finite `State`, or on
  # a finite `all-states` that `step` does not leave, each component is
  # one of a finite set of closed Nat rewards, so the vector repeats. A
  # transient of 0 and a period of 1 is a constant at every state of
  # that set. Any other shape is a finite prefix and then a constant or
  # a repeating tail. The tail comparison rewrites that closed form.
  # `rank` is Unit when the predicate prefers the action and Empty when
  # it does not. Off a declared cover it is Empty: the homomorphism
  # does not order a state the cover does not name. The evidence is the
  # case split. The walk that finds the period is the pigeonhole on
  # that finite set. It is not a fuel bound. The evidence inducts on `n`.

  def target("successor"), do: "CoinductiveHomomorphism"
  def target(_oracle), do: "CoindHomo"

  # queens4 is 18 × 4 × 4 = 288 and stays on the per-leaf book.
  # A placement state is ClassCert, including queens8, and is not this.
  @wide_cells 1500

  @doc false
  def wide_host?(host) do
    not placement_state?(host) and cell_count(host) > @wide_cells
  end

  defp placement_state?(host) do
    case Enum.find(host.book, &(Map.get(&1, :kind) == :data and &1.name == "State")) do
      %{ctors: ctors} -> Enum.map(ctors, & &1.name) == ["ongoing", "dead", "solved"]
      _ -> false
    end
  end

  defp cell_count(host) do
    actions = length(host.actions || [])

    n =
      cond do
        is_list(host[:inhabitants]) and host.inhabitants != [] ->
          length(host.inhabitants)

        is_list(host[:all_states]) and host.all_states != [] ->
          length(host.all_states)

        true ->
          case Enum.find(host.book, &(Map.get(&1, :kind) == :data and &1.name == "State")) do
            %{ctors: ctors} -> length(ctors)
            _ -> 0
          end
      end

    n * actions * actions
  end

  defp wide?(states, actions) do
    Process.get(:muro_synth_wide) == true and
      length(states) * length(actions) * length(actions) > @wide_cells
  end

  @doc """
  The certificate text, or a reason it was not generated.

  `{:ok, text, obligations}` appends a ranking the checker can accept.
  `{:skip, reason}` leaves the policy book without a ranking.
  """
  def render(host, arms, oracle, bound) do
    case Muro.Synth.ClassCert.render(host, arms, oracle, bound) do
      :fallthrough -> render_cover(host, arms, oracle, bound)
      other -> other
    end
  end

  @doc false
  def cascade(bound, arms, actions), do: rank_match(bound, arms, actions)

  # Same term as `prefer/2`, with the two action variables named.
  @doc false
  def preference(actions, winner, left \\ nil, right \\ nil) do
    prefer(actions, winner, left || Names.current("a"), right || Names.current("b"))
  end

  defp render_cover(host, arms, oracle, bound) do
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
    case cert_states(host) do
      :open ->
        {:error, "State is not a finite enumeration"}

      {:error, reason} ->
        {:error, reason}

      {:ok, states} ->
        actions = host.actions

        with {:ok, now} <- vector(host, states, actions, &reward(host, &1, &2)) do
          if Enum.all?(Map.values(now), &closed_nat?/1) do
            walk(host, states, actions, [now], %{key(now, states) => 0})
          else
            {:error, "reward is not a closed Nat"}
          end
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

  defp key(vector, states), do: Enum.map(states, &vector[&1])

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
        at(orbit, n + p)[state] == at(orbit, n)[state]
      end)
    end)
  end

  defp vector(host, states, actions, fun) do
    Enum.reduce_while(states, {:ok, %{}}, fn state, {:ok, acc} ->
      case maximum(host, Enum.map(actions, &fun.(state, &1))) do
        {:ok, value} -> {:cont, {:ok, Map.put(acc, state, value)}}
        :unordered -> {:halt, {:error, "the rewards at #{Term.spell(state)} have no maximum"}}
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

  # The raw successor. Closure looks at this, so a state outside the
  # pool is visible. `next/3` then replaces it with the pool element of
  # the same value, and the walk's keys are that element.
  defp raw_next(host, state, action), do: elem(host.step.(state, action), 0)

  defp next(host, state, action) do
    canon_state(state_pool(host), raw_next(host, state, action))
  end

  defp state_key(%Term{value: value}), do: value
  defp state_key(other), do: other

  defp state_pool(host) do
    cond do
      not host[:structured] -> nil
      is_list(host[:inhabitants]) and host.inhabitants != [] -> host.inhabitants
      is_list(host[:all_states]) and host.all_states != [] -> host.all_states
      true -> nil
    end
  end

  defp canon_state(nil, raw), do: raw

  defp canon_state(pool, raw) do
    key = state_key(raw)
    Enum.find(pool, raw, &(state_key(&1) == key))
  end

  defp constructors(host, data) do
    %{ctors: ctors} = Enum.find(host.book, &(Map.get(&1, :kind) == :data and &1.name == data))
    Enum.map(ctors, & &1.name)
  end

  # Nullary `State` is its constructors, in declaration order. A finite
  # structured `State` is every inhabitant, so the match is exhaustive.
  # An open term with a finite non-empty `all-states` is that cover,
  # when `step` of every action stays inside it. Extending the cover
  # would rank states the search did not observe. An empty cover is
  # not a ranking. Anything else is not that split. The walk is the
  # pigeonhole on this finite set.
  defp cert_states(host) do
    cond do
      not host[:structured] ->
        {:ok, constructors(host, "State")}

      is_list(host[:inhabitants]) and host.inhabitants != [] ->
        {:ok, host.inhabitants}

      host[:all_states] == [] ->
        {:error, "all-states is empty"}

      cover_only?(host) ->
        cover_states(host)

      true ->
        :open
    end
  end

  defp cover_states(host) do
    cond do
      is_binary(msg = Term.cert_refusal(host.schema)) ->
        {:error, msg}

      not closed_cover?(host, host.all_states, host.actions) ->
        {:error, "all-states is not closed under step"}

      not cover_splittable?(host) ->
        {:error, "the cover cannot be split"}

      true ->
        {:ok, host.all_states}
    end
  end

  # A finite cover is split by peeling the terms themselves. Equality
  # of the schema is a different question: a back-edge under a product
  # has no equality run, and the cover can still be ranked.
  defp cover_splittable?(host) do
    miss = fn _src -> "Empty" end
    body = fn _spell -> "Unit" end
    type = fn _src -> "Type" end

    case Term.cover_match(host.schema, Names.current("s"), host.all_states, type, body, miss) do
      {:ok, _text} -> true
      :open -> false
    end
  end

  # Inhabitants of at most 32 stay on the exhaustive match. The cover
  # is only the open, or wider, state.
  defp cover_only?(host) do
    host[:structured] and
      not (is_list(host[:inhabitants]) and host.inhabitants != []) and
      is_list(host[:all_states]) and host.all_states != []
  end

  defp closed_cover?(host, states, actions) do
    Enum.all?(states, fn state ->
      Enum.all?(actions, fn action ->
        raw = raw_next(host, state, action)
        Enum.any?(states, &(state_key(&1) == state_key(raw)))
      end)
    end)
  end

  defp build(host, arms, oracle, vocab, values, settled, bound) do
    {:ok, states} = cert_states(host)
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

    {extra_preserves, taken} =
      if extra?,
        do: Muro.Synth.Book.reserve("preserves-coind", taken),
        else: {nil, taken}

    proofs =
      proof_entries(
        extra?,
        preserves,
        extra_preserves,
        primary,
        leaf_names,
        more_leaf_names,
        leaves,
        more_leaves
      )

    case seal(host, bound, arms, actions, rank, states, proofs, taken) do
      {:skip, reason} ->
        {:skip, reason}

      {:ok, tail} ->
        text =
          [
            solves_text(host, states, vocab, values, solves, settled),
            below,
            more_below,
            tail
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
        {name, taken} = Muro.Synth.Book.reserve("cert-solve-#{Term.label(state)}", taken)
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
      def #{name} : evidence Π (#{Names.current("n")} : Nat) → {solve #{Term.spell(state)} #{Names.current("n")} ≡ #{const} : #{vocab.reward}} :=
        λ (#{Names.current("n")} : Nat) →
          match #{Names.current("n")} motive (λ (#{Names.current("k")} : Nat) → {solve #{Term.spell(state)} #{Names.current("k")} ≡ #{const} : #{vocab.reward}})
            | 0 => refl
            | suc #{Names.current("m")} =>
                #{rewrite_chain(steps, solves, const, vocab, &spell_nat(values[&1]), &"solve #{Term.spell(&1)} #{Names.current("m")}")}
      """
    end)
  end

  # One rewrite per distinct successor, outer first in action order.
  # An earlier successor is its right-hand side inside a later rewrite,
  # because that outer rewrite is read at its right-hand side. The current
  # successor is `z` everywhere it occurs. A later one is still `solve`.
  defp rewrite_chain(steps, solves, rhs, vocab, shown, fresh, spell_apply \\ nil) do
    spell_apply = spell_apply || fn lemma -> "#{lemma} #{Names.current("m")}" end
    order = Enum.uniq(steps)
    last = length(order) - 1

    Enum.reduce(last..0//-1, "refl", fn index, acc ->
      state = Enum.at(order, index)
      args = Enum.map(steps, &rewrite_slot(&1, state, index, order, shown, fresh))
      nest = max_nest(args, vocab.max, vocab.bottom)
      lemma = Map.fetch!(solves, state)

      """
      rewrite #{spell_apply.(lemma)} motive (λ #{Names.current("z")} → {#{nest} ≡ #{rhs} : #{vocab.reward}}) in
      #{acc}\
      """
      |> String.trim_trailing()
    end)
  end

  defp rewrite_slot(state, current, index, order, shown, fresh) do
    cond do
      state == current -> Names.current("z")
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
      base = "cert-below-#{kind}-#{Term.label(state)}-#{Term.spell(left)}-#{Term.spell(right)}"
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
    "Π (#{Names.current("n")} : Nat) → le (action-at #{Term.spell(state)} #{Term.spell(left)} #{Names.current("n")}) (action-at #{Term.spell(state)} #{Term.spell(right)} #{Names.current("n")})"
  end

  defp below_type(host, :successor, state, left, right) do
    left_state = next(host, state, left)
    right_state = next(host, state, right)

    "Π (#{Names.current("n")} : Nat) → le (solve #{Term.spell(left_state)} #{Names.current("n")}) (solve #{Term.spell(right_state)} #{Names.current("n")})"
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
        "le-refl (solve #{Term.spell(next(host, state, left))} #{Names.current("m")})"
      else
        left_state = next(host, state, left)
        right_state = next(host, state, right)
        const = spell_nat(values[left_state])

        """
        rewrite #{solves[left_state]} #{Names.current("m")} motive (λ #{Names.current("z")} → le #{Names.current("z")} (solve #{Term.spell(right_state)} #{Names.current("m")})) in
        rewrite #{solves[right_state]} #{Names.current("m")} motive (λ #{Names.current("z")} → le #{paren(const)} #{Names.current("z")}) in tt\
        """
      end

    """
    λ (#{Names.current("n")} : Nat) →
      match #{Names.current("n")} motive (λ (#{Names.current("k")} : Nat) → le (action-at #{Term.spell(state)} #{Term.spell(left)} #{Names.current("k")}) (action-at #{Term.spell(state)} #{Term.spell(right)} #{Names.current("k")}))
        | 0 => tt
        | suc #{Names.current("m")} =>
            #{tail}\
    """
  end

  defp successor_below(host, state, left, right, solves, values, _vocab) do
    left_state = next(host, state, left)
    right_state = next(host, state, right)
    const = spell_nat(values[left_state])

    """
    λ (#{Names.current("n")} : Nat) →
      rewrite #{solves[left_state]} #{Names.current("n")} motive (λ #{Names.current("z")} → le #{Names.current("z")} (solve #{Term.spell(right_state)} #{Names.current("n")})) in
      rewrite #{solves[right_state]} #{Names.current("n")} motive (λ #{Names.current("z")} → le #{paren(const)} #{Names.current("z")}) in tt\
    """
  end

  defp leaf_lemmas(host, arms, states, actions, rank, kind, below, taken) do
    if wide?(states, actions) do
      wide_leaves(host, arms, states, actions, rank, kind, below, taken)
    else
      leaf_defs(host, arms, states, actions, rank, kind, below, taken)
    end
  end

  defp leaf_defs(host, arms, states, actions, rank, kind, below, taken) do
    cells =
      for state <- states, left <- actions, right <- actions do
        {state, left, right}
      end

    Enum.reduce(cells, {[], taken, [], %{}}, fn {state, left, right}, {text, taken, obs, names} ->
      base = "cert-leaf-#{kind}-#{Term.label(state)}-#{Term.spell(left)}-#{Term.spell(right)}"
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

  # The pointwise lemmas stay. The |A|×|A| split is one arm per winning
  # action, so the cell map is not copied onto every state.
  defp wide_leaves(_host, _arms, _states, _actions, _rank, kind, below, taken) do
    {miss, taken} = Muro.Synth.Book.reserve("cert-miss-#{kind}", taken)
    {same, taken} = Muro.Synth.Book.reserve("cert-same-#{kind}", taken)
    ctx = %{below: below, miss: miss, same: same, kind: kind}
    {["-- wide cover\n", wide_helpers(kind, miss, same)], taken, [], ctx}
  end

  defp wide_helpers(kind, miss, same) do
    fun = stream_fun(kind)
    s = Names.current("s")
    a = Names.current("a")
    b = Names.current("b")
    r = Names.current("r")

    """
    def #{miss} : evidence Π (+ #{s} : State) → Π (+ #{a} : Action) → Π (+ #{b} : Action) → Π (#{r} : Empty) → Dom Reward le (#{fun} #{s} #{a}) (#{fun} #{s} #{b}) :=
      λ (+ #{s} : State) → λ (+ #{a} : Action) → λ (+ #{b} : Action) → λ (#{r} : Empty) →
        matchEmpty #{r} motive (λ _ → Dom Reward le (#{fun} #{s} #{a}) (#{fun} #{s} #{b}))
    def #{same} : evidence Π (+ #{s} : State) → Π (+ #{a} : Action) → Π (#{r} : Unit) → Dom Reward le (#{fun} #{s} #{a}) (#{fun} #{s} #{a}) :=
      λ (+ #{s} : State) → λ (+ #{a} : Action) → λ (#{r} : Unit) →
        dom-refl Reward le le-refl (#{fun} #{s} #{a})
    """
  end

  defp leaf_type(kind, rank, state, left, right) do
    fun = stream_fun(kind)

    "Π (#{Names.current("r")} : #{rank} #{Term.spell(state)} #{Term.spell(left)} #{Term.spell(right)}) → Dom Reward le (#{fun} #{Term.spell(state)} #{Term.spell(left)}) (#{fun} #{Term.spell(state)} #{Term.spell(right)})"
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
    "λ (#{Names.current("r")} : Empty) → matchEmpty #{Names.current("r")} motive (λ _ → Dom Reward le (#{stream(kind, state, left)}) (#{stream(kind, state, right)}))"
  end

  defp dom_refl(:action, _host, state, action) do
    "λ (#{Names.current("r")} : Unit) → dom-refl Reward le le-refl (action-value #{Term.spell(state)} #{action})"
  end

  defp dom_refl(:successor, host, state, action) do
    "λ (#{Names.current("r")} : Unit) → dom-refl Reward le le-refl (value #{Term.spell(next(host, state, action))})"
  end

  defp tabulate(:action, _host, state, left, right, lemma) do
    "λ (#{Names.current("r")} : Unit) → tabulate-dom Reward le (λ (#{Names.current("n")} : Nat) → action-at #{Term.spell(state)} #{Term.spell(left)} #{Names.current("n")}) (λ (#{Names.current("n")} : Nat) → action-at #{Term.spell(state)} #{Term.spell(right)} #{Names.current("n")}) #{lemma} 0"
  end

  defp tabulate(:successor, host, state, left, right, lemma) do
    left_state = next(host, state, left)
    right_state = next(host, state, right)

    "λ (#{Names.current("r")} : Unit) → tabulate-dom Reward le (λ (#{Names.current("n")} : Nat) → solve #{Term.spell(left_state)} #{Names.current("n")}) (λ (#{Names.current("n")} : Nat) → solve #{Term.spell(right_state)} #{Names.current("n")}) #{lemma} 0"
  end

  defp stream(kind, state, action), do: "#{stream_fun(kind)} #{Term.spell(state)} #{action}"
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

  defp closed_nat?(n) when is_integer(n) and n >= 0, do: true
  defp closed_nat?(_value), do: false

  defp spell_nat(0), do: "0"
  # A closed numeral, not a tower of successors. Small numerals stay
  # written as successors so an existing certificate is unchanged.
  defp spell_nat(n) when is_integer(n) and n >= 10, do: Integer.to_string(n)

  defp spell_nat(n) when is_integer(n) and n > 0 do
    rest = spell_nat(n - 1)
    if rest == "0", do: "suc 0", else: "suc (" <> rest <> ")"
  end

  defp paren(term) do
    if String.contains?(term, " ") or String.contains?(term, "("), do: "(#{term})", else: term
  end

  # `{name, target, kind, leaf names, leaf text}`. Leaf text comes before
  # every preserves, as it did when the split was exhaustive.
  defp proof_entries(
         extra?,
         preserves,
         extra_preserves,
         primary,
         leaf_names,
         more_leaf_names,
         leaves,
         more_leaves
       ) do
    primary_proof = {preserves, certificate_name(primary), primary, leaf_names, leaves}

    if extra? do
      [primary_proof, {extra_preserves, "CoindHomo", :action, more_leaf_names, more_leaves}]
    else
      [primary_proof]
    end
  end

  defp seal(host, bound, arms, actions, rank, states, proofs, taken) do
    {preface, taken} = wide_preface(host, bound, arms, actions, states, taken)

    sealed =
      if cover_only?(host) do
        seal_cover(host, bound, arms, actions, rank, states, proofs, taken)
      else
        {:ok, seal_closed(host, bound, arms, actions, rank, states, proofs, taken)}
      end

    case sealed do
      {:ok, tail} -> {:ok, [preface | tail]}
      other -> other
    end
  end

  # Named preferences, one chain of `eval`, and one `refl` per state that
  # the deployed policy selects the winner. The arm reads the names.
  defp wide_preface(host, bound, arms, actions, states, taken) do
    if wide?(states, actions) do
      {prefers, prefer_text, taken} = prefer_block(arms, actions, taken)
      Process.put(:muro_synth_prefers, prefers)
      Process.put(:muro_synth_choice, Map.new(states, &{&1, chosen(host, arms, &1)}))

      {step_text, taken} =
        if cover_only?(host) do
          {name, taken} = Muro.Synth.Book.reserve("rank-step", taken)
          Process.put(:muro_synth_rank_step, name)
          {rank_step_def(name, bound, arms, prefers), taken}
        else
          Process.delete(:muro_synth_rank_step)
          {"", taken}
        end

      {picks, taken} = policy_picks(bound, states, taken)
      {[prefer_text, step_text, picks], taken}
    else
      Process.delete(:muro_synth_prefers)
      Process.delete(:muro_synth_choice)
      Process.delete(:muro_synth_rank_step)
      {"", taken}
    end
  end

  defp prefer_block(arms, actions, taken) do
    named =
      arms
      |> Enum.flat_map(&[&1.action, &1.else])
      |> Enum.reject(&is_nil/1)
      |> Enum.uniq_by(&action_key/1)

    {rows, taken} =
      Enum.map_reduce(named, taken, fn action, taken ->
        {name, taken} = Muro.Synth.Book.reserve("prefer-#{Term.label(action)}", taken)

        defn = """
        def #{name} : spec Π (#{Names.current("a")} : Action) → Π (#{Names.current("b")} : Action) → Type :=
          λ (#{Names.current("a")} : Action) → λ (#{Names.current("b")} : Action) →
            #{prefer(actions, action)}
        """

        {{action_key(action), name, defn}, taken}
      end)

    {Map.new(rows, fn {key, name, _} -> {key, name} end), Enum.map(rows, &elem(&1, 2)), taken}
  end

  defp rank_step_def(name, bound, arms, prefers) do
    s = Names.current("s")
    a = Names.current("a")
    b = Names.current("b")

    """
    def #{name} : spec Π (#{s} : State) → Π (#{a} : Action) → Π (#{b} : Action) → Type :=
      λ (#{s} : State) → λ (#{a} : Action) → λ (#{b} : Action) →
        #{rank_match_named(bound, arms, prefers)}
    """
  end

  defp policy_picks(bound, states, taken) do
    choice = Process.get(:muro_synth_choice)

    Enum.map_reduce(states, taken, fn state, taken ->
      winner = Map.fetch!(choice, state)
      {name, taken} = Muro.Synth.Book.reserve("cert-picks-#{Term.label(state)}", taken)
      spell = atom_src(Term.spell(state))
      win = Term.spell(winner)

      defn = """
      def #{name} : evidence {#{bound.policy} #{spell} ≡ #{win} : Action} :=
        refl
      """

      {defn, taken}
    end)
  end

  defp action_key(action), do: Term.spell(action)

  defp seal_closed(host, bound, arms, actions, rank, states, proofs, taken) do
    texts = Enum.map(proofs, fn {_name, _target, _kind, _leaves, text} -> text end)

    {bodies, _taken} =
      Enum.map_reduce(proofs, taken, fn {name, target, kind, leaves, _text}, taken ->
        preserves_text(host, name, target, states, actions, rank, kind, leaves, taken)
      end)

    [rank_text(bound, arms, actions, rank) | texts] ++ bodies
  end

  defp seal_cover(host, bound, arms, actions, rank, states, proofs, taken) do
    with {:ok, rank_def} <- rank_cover(host, bound, arms, actions, rank, states),
         {:ok, bodies} <- cover_proofs(host, states, actions, rank, proofs, taken) do
      texts = Enum.map(proofs, fn {_name, _target, _kind, _leaves, text} -> text end)
      {:ok, [rank_def | texts] ++ bodies}
    else
      :open -> {:skip, "the cover cannot be split"}
    end
  end

  defp cover_proofs(host, states, actions, rank, proofs, taken) do
    Enum.reduce_while(proofs, {:ok, [], taken}, fn proof, {:ok, acc, taken} ->
      {name, target, kind, leaves, _text} = proof
      {miss, taken} = Muro.Synth.Book.reserve("cert-cover-miss", taken)

      case preserves_cover(host, name, target, states, actions, rank, kind, leaves, miss, taken) do
        :open -> {:halt, :open}
        {:ok, body, taken} -> {:cont, {:ok, acc ++ [cover_miss(miss, kind), body], taken}}
      end
    end)
    |> case do
      :open -> :open
      {:ok, parts, _taken} -> {:ok, parts}
    end
  end

  # On the cover, `rank` is `eval` of the survivor. Off it, `rank` is
  # Empty, so the universal homomorphism does not order that state.
  defp rank_cover(host, bound, arms, actions, rank, states) do
    body_of =
      if wide?(states, actions) do
        step = Process.get(:muro_synth_rank_step)

        fn spell ->
          "#{step} #{atom_src(spell)} #{Names.current("a")} #{Names.current("b")}"
        end
      else
        fn _spell -> rank_match(bound, arms, actions) end
      end

    case Term.cover_match(
           host.schema,
           Names.current("s"),
           states,
           fn _src -> "Type" end,
           body_of,
           fn _src -> "Empty" end
         ) do
      :open ->
        :open

      {:ok, body} ->
        {:ok,
         """
         def #{rank} : spec Π (#{Names.current("s")} : State) → Π (#{Names.current("a")} : Action) → Π (#{Names.current("b")} : Action) → Type :=
           λ (#{Names.current("s")} : State) → λ (#{Names.current("a")} : Action) → λ (#{Names.current("b")} : Action) →
             #{body}
         """}
    end
  end

  defp preserves_cover(host, name, target, states, actions, rank, kind, leaves, miss_name, taken) do
    if wide?(states, actions) do
      wide_preserves_cover(
        host,
        name,
        target,
        states,
        actions,
        rank,
        kind,
        leaves,
        miss_name,
        taken
      )
    else
      preserves_cover_cells(
        host,
        name,
        target,
        states,
        actions,
        rank,
        kind,
        leaves,
        miss_name,
        taken
      )
    end
  end

  defp preserves_cover_cells(
         host,
         name,
         target,
         states,
         actions,
         rank,
         kind,
         leaves,
         miss_name,
         taken
       ) do
    fun = stream_fun(kind)
    by_spell = Map.new(states, &{Term.spell(&1), &1})

    typed = fn src ->
      safe = atom_src(src)

      "Π (#{Names.current("r")} : #{rank} #{safe} #{Names.current("a")} #{Names.current("b")}) → Dom Reward le (#{fun} #{safe} #{Names.current("a")}) (#{fun} #{safe} #{Names.current("b")})"
    end

    case Term.cover_match(
           host.schema,
           Names.current("s"),
           states,
           typed,
           fn spell -> action_nest(Map.fetch!(by_spell, spell), actions, rank, kind, leaves) end,
           fn src ->
             "#{miss_name} #{atom_src(src)} #{Names.current("a")} #{Names.current("b")}"
           end
         ) do
      :open ->
        :open

      {:ok, body} ->
        {:ok,
         """
         def #{name} : evidence #{target} #{rank} :=
           λ (#{Names.current("a")} : Action) → λ (#{Names.current("b")} : Action) → λ (#{Names.current("s")} : State) →
             #{body}
         """, taken}
    end
  end

  defp wide_preserves_cover(
         host,
         name,
         target,
         states,
         actions,
         rank,
         kind,
         leaves,
         miss_name,
         taken
       ) do
    fun = stream_fun(kind)
    by_spell = Map.new(states, &{Term.spell(&1), &1})
    {arm_text, calls, taken} = wide_arm_bundle(states, actions, rank, kind, leaves, taken)

    typed = fn src ->
      safe = atom_src(src)

      "Π (#{Names.current("r")} : #{rank} #{safe} #{Names.current("a")} #{Names.current("b")}) → Dom Reward le (#{fun} #{safe} #{Names.current("a")}) (#{fun} #{safe} #{Names.current("b")})"
    end

    case Term.cover_match(
           host.schema,
           Names.current("s"),
           states,
           typed,
           fn spell -> Map.fetch!(calls, Map.fetch!(by_spell, spell)) end,
           fn src ->
             "#{miss_name} #{atom_src(src)} #{Names.current("a")} #{Names.current("b")}"
           end
         ) do
      :open ->
        :open

      {:ok, body} ->
        {:ok, arm_text ++ [preserves_def(name, target, rank, body)], taken}
    end
  end

  defp preserves_def(name, target, rank, body) do
    """
    def #{name} : evidence #{target} #{rank} :=
      λ (#{Names.current("a")} : Action) → λ (#{Names.current("b")} : Action) → λ (#{Names.current("s")} : State) →
        #{body}
    """
  end

  # The branch is this helper applied to the state term. The state
  # binder of `CoindHomo` is affine, and a motive that named both
  # streams would use it twice. The helper's own argument is reusable.
  defp cover_miss(name, kind) do
    fun = stream_fun(kind)

    """
    def #{name} : evidence Π (+ #{Names.current("s")} : State) → Π (+ #{Names.current("a")} : Action) → Π (+ #{Names.current("b")} : Action) → Π (#{Names.current("r")} : Empty) → Dom Reward le (#{fun} #{Names.current("s")} #{Names.current("a")}) (#{fun} #{Names.current("s")} #{Names.current("b")}) :=
      λ (+ #{Names.current("s")} : State) → λ (+ #{Names.current("a")} : Action) → λ (+ #{Names.current("b")} : Action) → λ (#{Names.current("r")} : Empty) →
        matchEmpty #{Names.current("r")} motive (λ _ → Dom Reward le (#{fun} #{Names.current("s")} #{Names.current("a")}) (#{fun} #{Names.current("s")} #{Names.current("b")}))
    """
  end

  defp atom_src(src) do
    cond do
      String.starts_with?(src, "(") -> src
      String.contains?(src, " ") -> "(#{src})"
      true -> src
    end
  end

  defp rank_text(bound, arms, actions, rank) do
    body =
      case Process.get(:muro_synth_prefers) do
        %{} = prefers -> rank_match_named(bound, arms, prefers)
        _ -> rank_match(bound, arms, actions)
      end

    """
    def #{rank} : spec Π (#{Names.current("s")} : State) → Π (#{Names.current("a")} : Action) → Π (#{Names.current("b")} : Action) → Type :=
      λ (#{Names.current("s")} : State) → λ (#{Names.current("a")} : Action) → λ (#{Names.current("b")} : Action) →
        #{body}
    """
  end

  defp rank_match_named(bound, [arm], prefers) do
    decl = Map.fetch!(bound.decl, arm.name)
    s = Names.current("s")

    """
    (match #{bound.names.eval} #{decl} #{s} motive (λ _ → Type)
      | true =>
          #{prefer_ref(prefers, arm.action)}
      | false =>
          #{prefer_ref(prefers, arm.else)})
    """
  end

  defp rank_match_named(bound, [arm | rest], prefers) do
    decl = Map.fetch!(bound.decl, arm.name)
    s = Names.current("s")

    """
    (match #{bound.names.eval} #{decl} #{s} motive (λ _ → Type)
      | true =>
          #{prefer_ref(prefers, arm.action)}
      | false =>
          #{rank_match_named(bound, rest, prefers)})
    """
  end

  defp prefer_ref(prefers, action) do
    name = Map.fetch!(prefers, action_key(action))
    "#{name} #{Names.current("a")} #{Names.current("b")}"
  end

  defp rank_match(bound, [arm], actions) do
    decl = Map.fetch!(bound.decl, arm.name)

    """
    (match #{bound.names.eval} #{decl} #{Names.current("s")} motive (λ _ → Type)
      | true =>
          #{prefer(actions, arm.action)}
      | false =>
          #{prefer(actions, arm.else)})
    """
  end

  defp rank_match(bound, [arm | rest], actions) do
    decl = Map.fetch!(bound.decl, arm.name)

    """
    (match #{bound.names.eval} #{decl} #{Names.current("s")} motive (λ _ → Type)
      | true =>
          #{prefer(actions, arm.action)}
      | false =>
          #{rank_match(bound, rest, actions)})
    """
  end

  defp prefer(actions, winner),
    do: prefer(actions, winner, Names.current("a"), Names.current("b"))

  defp prefer(actions, winner, left_var, right_var) do
    branches =
      Enum.map_join(actions, "\n", fn left ->
        rights =
          Enum.map_join(actions, "\n", fn right ->
            cell = if unit?(winner, left, right), do: "Unit", else: "Empty"
            "        | #{Term.spell(right)} => #{cell}"
          end)

        """
        | #{Term.spell(left)} =>
            (match #{right_var} motive (λ _ → Type)
        #{rights})
        """
      end)

    """
    (match #{left_var} motive (λ _ → Type)
    #{branches})
    """
  end

  defp preserves_text(host, name, target, states, actions, rank, kind, leaves, taken) do
    if wide?(states, actions) do
      wide_preserves_split(host, name, target, states, actions, rank, kind, leaves, taken)
    else
      text =
        if Enum.any?(states, &match?(%Term{}, &1)) do
          preserves_structured(host, name, target, states, actions, rank, kind, leaves)
        else
          preserves_closed(name, target, states, actions, rank, kind, leaves)
        end

      {text, taken}
    end
  end

  defp wide_preserves_split(host, name, target, states, actions, rank, kind, leaves, taken) do
    {arm_text, calls, taken} = wide_arm_bundle(states, actions, rank, kind, leaves, taken)
    fun = stream_fun(kind)

    text =
      if Enum.any?(states, &match?(%Term{}, &1)) do
        by_spell = Map.new(states, &{&1.spell, &1})

        body =
          Term.exhaust(
            host.schema,
            Names.current("s"),
            fn src ->
              "Π (#{Names.current("r")} : #{rank} #{src} #{Names.current("a")} #{Names.current("b")}) → Dom Reward le (#{fun} #{src} #{Names.current("a")}) (#{fun} #{src} #{Names.current("b")})"
            end,
            fn spell -> Map.fetch!(calls, Map.fetch!(by_spell, spell)) end,
            bound_binders()
          )

        arm_text ++ [preserves_def(name, target, rank, body)]
      else
        branches =
          Enum.map_join(states, "\n", fn state ->
            "| #{Term.spell(state)} => #{Map.fetch!(calls, state)}"
          end)

        arm_text ++
          [
            """
            def #{name} : evidence #{target} #{rank} :=
              λ (#{Names.current("a")} : Action) → λ (#{Names.current("b")} : Action) → λ (#{Names.current("s")} : State) →
                match #{Names.current("s")} motive (λ (#{Names.current("x")} : State) → Π (#{Names.current("r")} : #{rank} #{Names.current("x")} #{Names.current("a")} #{Names.current("b")}) → Dom Reward le (#{fun} #{Names.current("x")} #{Names.current("a")}) (#{fun} #{Names.current("x")} #{Names.current("b")}))
            #{branches}
            """
          ]
      end

    {text, taken}
  end

  # One `under` per state and one arm per winning action. The arm's
  # ranking is the named preference, which `rank` reduces to.
  defp wide_arm_bundle(states, actions, _rank, kind, ctx, taken) do
    fun = stream_fun(kind)
    choice = Process.get(:muro_synth_choice)
    prefers = Process.get(:muro_synth_prefers)
    a = Names.current("a")
    b = Names.current("b")

    {under_rows, taken} =
      Enum.map_reduce(states, taken, fn state, taken ->
        winner = Map.fetch!(choice, state)
        {uname, taken} = Muro.Synth.Book.reserve("cert-under-#{kind}-#{Term.label(state)}", taken)
        {{state, uname, under_def(uname, state, actions, winner, kind, ctx)}, taken}
      end)

    winners =
      states
      |> Enum.map(&Map.fetch!(choice, &1))
      |> Enum.uniq_by(&action_key/1)

    {arm_rows, taken} =
      Enum.map_reduce(winners, taken, fn winner, taken ->
        {aname, taken} = Muro.Synth.Book.reserve("cert-arm-#{kind}-#{Term.label(winner)}", taken)
        prefer = Map.fetch!(prefers, action_key(winner))

        {{action_key(winner), aname,
          shared_arm_def(aname, actions, winner, kind, fun, prefer, ctx)}, taken}
      end)

    arm_by = Map.new(arm_rows, fn {key, name, _} -> {key, name} end)
    under_by = Map.new(under_rows, fn {state, name, _} -> {state, name} end)

    calls =
      Map.new(states, fn state ->
        winner = Map.fetch!(choice, state)
        arm = Map.fetch!(arm_by, action_key(winner))
        under = Map.fetch!(under_by, state)
        {state, "#{arm} #{atom_src(Term.spell(state))} #{under} #{a} #{b}"}
      end)

    text = Enum.map(under_rows, &elem(&1, 2)) ++ Enum.map(arm_rows, &elem(&1, 2))
    {text, calls, taken}
  end

  defp under_def(name, state, actions, winner, kind, ctx) do
    a = Names.current("a")
    n = Names.current("n")
    y = Names.current("y")
    spell = atom_src(Term.spell(state))
    win = atom_src(Term.spell(winner))
    motive = "le (#{pointwise(kind, spell, y, n)}) (#{pointwise(kind, spell, win, n)})"

    branches =
      Enum.map_join(actions, "\n", fn action ->
        body =
          if action_key(action) == action_key(winner) do
            "le-refl (#{pointwise(kind, spell, win, n)})"
          else
            case Map.fetch(ctx.below, {state, action, winner}) do
              {:ok, lemma} -> "#{lemma} #{n}"
              :error -> "le-refl (#{pointwise(kind, spell, atom_src(Term.spell(action)), n)})"
            end
          end

        "| #{Term.spell(action)} => #{body}"
      end)

    evidence_def(
      name,
      "Π (#{a} : Action) → Π (#{n} : Nat) → le (#{pointwise(kind, spell, a, n)}) (#{pointwise(kind, spell, win, n)})",
      """
      λ (#{a} : Action) → λ (#{n} : Nat) →
        match #{a} motive (λ (#{y} : Action) → #{motive})
      #{branches}
      """
    )
  end

  defp shared_arm_def(name, actions, winner, kind, fun, prefer, ctx) do
    s = Names.current("s")
    a = Names.current("a")
    b = Names.current("b")
    u = Names.current("u")
    r = Names.current("r")
    y = Names.current("y")
    z = Names.current("z")
    n = Names.current("n")
    j = Names.current("j")
    win = atom_src(Term.spell(winner))

    under_ty =
      "Π (#{j} : Action) → Π (#{n} : Nat) → le (#{pointwise(kind, s, j, n)}) (#{pointwise(kind, s, win, n)})"

    arms =
      Enum.map_join(actions, "\n", fn left ->
        left_s = atom_src(Term.spell(left))

        rights =
          Enum.map_join(actions, "\n", fn right ->
            right_s = atom_src(Term.spell(right))

            "        | #{Term.spell(right)} => #{arm_cell(kind, fun, s, u, r, n, left_s, right_s, win, ctx)}"
          end)

        """
        | #{Term.spell(left)} =>
            (match #{b} motive (λ (#{z} : Action) → Π (#{r} : #{prefer} #{left_s} #{z}) → Dom Reward le (#{fun} #{s} #{left_s}) (#{fun} #{s} #{z}))
        #{rights})
        """
      end)

    evidence_def(
      name,
      "Π (+ #{s} : State) → Π (#{u} : #{under_ty}) → Π (+ #{a} : Action) → Π (#{b} : Action) → Π (#{r} : #{prefer} #{a} #{b}) → Dom Reward le (#{fun} #{s} #{a}) (#{fun} #{s} #{b})",
      """
      λ (+ #{s} : State) → λ (#{u} : #{under_ty}) → λ (+ #{a} : Action) → λ (#{b} : Action) →
        (match #{a} motive (λ (#{y} : Action) → Π (#{r} : #{prefer} #{y} #{b}) → Dom Reward le (#{fun} #{s} #{y}) (#{fun} #{s} #{b}))
      #{arms})
      """
    )
  end

  defp arm_cell(_kind, _fun, s, u, r, n, left, right, winner, ctx) do
    cond do
      left == right ->
        "#{ctx.same} #{s} #{left}"

      right == winner ->
        "λ (#{r} : Unit) → tabulate-dom Reward le (λ (#{n} : Nat) → #{pointwise_kind(ctx.kind, s, left, n)}) (λ (#{n} : Nat) → #{pointwise_kind(ctx.kind, s, winner, n)}) (#{u} #{left}) 0"

      true ->
        "#{ctx.miss} #{s} #{left} #{right}"
    end
  end

  defp pointwise(kind, state, action, n), do: pointwise_kind(kind, state, action, n)

  defp pointwise_kind(:action, state, action, n), do: "action-at #{state} #{action} #{n}"

  defp pointwise_kind(:successor, state, action, n),
    do: "solve (fst (step #{state} #{action})) #{n}"

  defp preserves_closed(name, target, states, actions, rank, kind, leaves) do
    fun = stream_fun(kind)

    """
    def #{name} : evidence #{target} #{rank} :=
      λ (#{Names.current("a")} : Action) → λ (#{Names.current("b")} : Action) → λ (#{Names.current("s")} : State) →
        match #{Names.current("s")} motive (λ (#{Names.current("x")} : State) → Π (#{Names.current("r")} : #{rank} #{Names.current("x")} #{Names.current("a")} #{Names.current("b")}) → Dom Reward le (#{fun} #{Names.current("x")} #{Names.current("a")}) (#{fun} #{Names.current("x")} #{Names.current("b")}))
    #{Enum.map_join(states, "\n", &state_branch(&1, actions, rank, kind, leaves))}
    """
  end

  # The scrutinee is the state term. Each arm is one inhabitant, and the
  # body is the action split at that closed term. A constructor pattern
  # would not cover a field.
  defp preserves_structured(host, name, target, states, actions, rank, kind, leaves) do
    fun = stream_fun(kind)
    by_spell = Map.new(states, &{&1.spell, &1})

    body =
      Term.exhaust(
        host.schema,
        Names.current("s"),
        fn src ->
          "Π (#{Names.current("r")} : #{rank} #{src} #{Names.current("a")} #{Names.current("b")}) → Dom Reward le (#{fun} #{src} #{Names.current("a")}) (#{fun} #{src} #{Names.current("b")})"
        end,
        fn spell ->
          action_nest(Map.fetch!(by_spell, spell), actions, rank, kind, leaves)
        end,
        bound_binders()
      )

    """
    def #{name} : evidence #{target} #{rank} :=
      λ (#{Names.current("a")} : Action) → λ (#{Names.current("b")} : Action) → λ (#{Names.current("s")} : State) →
        #{body}
    """
  end

  defp action_nest(state, actions, rank, kind, leaves) do
    fun = stream_fun(kind)

    arms =
      Enum.map_join(actions, "\n", fn left ->
        rights =
          Enum.map_join(actions, "\n", fn right ->
            "            | #{Term.spell(right)} => #{Map.fetch!(leaves, {state, left, right})}"
          end)

        """
        | #{Term.spell(left)} =>
            (match #{Names.current("b")} motive (λ (#{Names.current("z")} : Action) → Π (#{Names.current("r")} : #{rank} #{Term.spell(state)} #{Term.spell(left)} #{Names.current("z")}) → Dom Reward le (#{fun} #{Term.spell(state)} #{Term.spell(left)}) (#{fun} #{Term.spell(state)} #{Names.current("z")}))
        #{rights})
        """
      end)

    """
    (match #{Names.current("a")} motive (λ (#{Names.current("y")} : Action) → Π (#{Names.current("r")} : #{rank} #{Term.spell(state)} #{Names.current("y")} #{Names.current("b")}) → Dom Reward le (#{fun} #{Term.spell(state)} #{Names.current("y")}) (#{fun} #{Term.spell(state)} #{Names.current("b")}))
    #{arms})
    """
  end

  defp state_branch(state, actions, rank, kind, leaves) do
    fun = stream_fun(kind)

    arms =
      Enum.map_join(actions, "\n", fn left ->
        rights =
          Enum.map_join(actions, "\n", fn right ->
            "            | #{Term.spell(right)} => #{Map.fetch!(leaves, {state, left, right})}"
          end)

        """
        | #{Term.spell(left)} =>
            (match #{Names.current("b")} motive (λ (#{Names.current("z")} : Action) → Π (#{Names.current("r")} : #{rank} #{Term.spell(state)} #{Term.spell(left)} #{Names.current("z")}) → Dom Reward le (#{fun} #{Term.spell(state)} #{Term.spell(left)}) (#{fun} #{Term.spell(state)} #{Names.current("z")}))
        #{rights})
        """
      end)

    """
    | #{Term.spell(state)} =>
        (match #{Names.current("a")} motive (λ (#{Names.current("y")} : Action) → Π (#{Names.current("r")} : #{rank} #{Term.spell(state)} #{Names.current("y")} #{Names.current("b")}) → Dom Reward le (#{fun} #{Term.spell(state)} #{Names.current("y")}) (#{fun} #{Term.spell(state)} #{Names.current("b")}))
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
      below_periodic(host, arms, states, actions, orbit, solves, vocab, primary, taken)

    {more_below, taken, more_below_obs, more_below_names} =
      if extra? do
        below_periodic(host, arms, states, actions, orbit, solves, vocab, :action, taken)
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

    {extra_preserves, taken} =
      if extra?,
        do: Muro.Synth.Book.reserve("preserves-coind", taken),
        else: {nil, taken}

    proofs =
      proof_entries(
        extra?,
        preserves,
        extra_preserves,
        primary,
        leaf_names,
        more_leaf_names,
        leaves,
        more_leaves
      )

    case seal(host, bound, arms, actions, rank, states, proofs, taken) do
      {:skip, reason} ->
        {:skip, reason}

      {:ok, tail} ->
        text =
          [forms, below, more_below, tail]
          |> IO.iodata_to_binary()

        {:ok,
         %{
           text: text,
           obligations: below_obs ++ more_below_obs ++ leaf_obs ++ more_leaf_obs,
           certificate: certificate_name(primary),
           also: if(extra?, do: "CoindHomo")
         }}
    end
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
    if wide?(orbit.states, host.actions) and orbit.period == 1 do
      shallow_form(host, vocab, orbit, taken)
    else
      form_text_orbit(host, vocab, orbit, taken)
    end
  end

  # One closed equation per state per depth up to the transient.
  # Depth 0 is `refl`. A later depth unfolds `solve` once, then rewrites
  # one successor at a time. The motive names a single `max`, and the
  # remaining actions stay a `max-list`, so conversion does not unfold a
  # wide nest of `solve`. The tail inducts on `n` the same way and calls
  # each successor's tail at the predecessor, so a cycle still descends.
  defp shallow_form(host, vocab, orbit, taken) do
    t = orbit.transient
    states = orbit.states
    {suc_eq, taken} = Muro.Synth.Book.reserve("solve-suc-eq", taken)
    {pack, taken} = squeeze_names(taken)

    {levels, by_k, taken} =
      Enum.reduce(0..t, {[], %{}, taken}, fn k, {texts, by_k, taken} ->
        prev_names =
          if k == 0 do
            %{}
          else
            Map.new(by_k[k - 1], fn {state, {name, _value}} -> {state, name} end)
          end

        {rows, taken} =
          Enum.map_reduce(states, taken, fn state, taken ->
            {name, taken} =
              Muro.Synth.Book.reserve("cert-solve-#{Term.label(state)}-#{k}", taken)

            value = at(orbit, k)[state]

            body =
              if k == 0 do
                "refl"
              else
                step_peel(
                  host,
                  state,
                  k - 1,
                  prev_names,
                  spell_nat(value),
                  vocab,
                  suc_eq,
                  pack,
                  fn succ ->
                    at(orbit, k - 1)[succ]
                  end
                )
              end

            defn =
              evidence_def(
                name,
                "{solve #{Term.spell(state)} #{nat_arg(k)} ≡ #{spell_nat(value)} : #{vocab.reward}}",
                body
              )

            {{state, name, value, defn}, taken}
          end)

        named = Map.new(rows, fn {state, name, value, _defn} -> {state, {name, value}} end)
        {texts ++ Enum.map(rows, &elem(&1, 3)), Map.put(by_k, k, named), taken}
      end)

    Process.put(
      :muro_synth_concrete,
      Map.new(states, fn state ->
        {state, Map.new(0..t, fn k -> {k, Map.fetch!(by_k[k], state)} end)}
      end)
    )

    named_at = fn state, k -> elem(Map.fetch!(by_k[k], state), 0) end

    {tails, taken} =
      Enum.map_reduce(states, taken, fn state, taken ->
        {name, taken} = Muro.Synth.Book.reserve("cert-solve-#{Term.label(state)}", taken)
        {{state, name}, taken}
      end)

    solves = Map.new(tails)

    tail_text =
      Enum.map(states, fn state ->
        const = spell_nat(at(orbit, t)[state])
        n = Names.current("n")
        m = Names.current("m")

        rows =
          Enum.map(host.actions, fn action ->
            succ = next(host, state, action)
            {"#{solves[succ]} #{m}", spell_nat(at(orbit, t)[succ]), action}
          end)

        chain = finish_peel(state, shift_term(m, t), const, vocab, suc_eq, rows, pack)

        goal = fn var ->
          "solve #{Term.spell(state)} #{shift_term(var, t)} ≡ #{const} : #{vocab.reward}"
        end

        evidence_def(
          solves[state],
          "Π (+ #{n} : Nat) → {#{goal.(n)}}",
          """
          λ (+ #{n} : Nat) →
            match #{n} motive (λ (#{Names.current("k")} : Nat) → {#{goal.(Names.current("k"))}})
              | 0 => #{named_at.(state, t)}
              | suc #{m} =>
                  #{chain}
          """
        )
      end)

    text = [solve_suc_def(suc_eq, vocab), squeeze_defs(pack, vocab) | levels] ++ tail_text
    {text, solves, taken}
  end

  defp squeeze_names(taken) do
    {max_same, taken} = Muro.Synth.Book.reserve("max-same", taken)
    {max_bot, taken} = Muro.Synth.Book.reserve("max-bot", taken)
    {rest_eq, taken} = Muro.Synth.Book.reserve("rest-eq", taken)
    {squeeze, taken} = Muro.Synth.Book.reserve("squeeze", taken)
    {%{max_same: max_same, max_bot: max_bot, rest_eq: rest_eq, squeeze: squeeze}, taken}
  end

  # `{solve s (suc k) ≡ max-list (map (solve ∘ step) all-actions)}` by the
  # clause of `solve`. One unfold, then `peel_rows` rewrites each action.
  defp solve_suc_def(name, vocab) do
    s = Names.current("s")
    k = Names.current("k")
    a = Names.current("a")

    evidence_def(
      name,
      "Π (+ #{s} : State) → Π (#{k} : Nat) → {solve #{s} (suc #{k}) ≡ max-list (map Action Reward (λ (#{a} : Action) → solve (fst (step #{s} #{a})) #{k}) all-actions) : #{vocab.reward}}",
      "λ (+ #{s} : State) → λ (#{k} : Nat) → refl"
    )
  end

  defp step_peel(host, state, prev, lemmas, goal, vocab, suc_eq, pack, value_of) do
    rows =
      Enum.map(host.actions, fn action ->
        succ = next(host, state, action)
        {Map.fetch!(lemmas, succ), spell_nat(value_of.(succ)), action}
      end)

    finish_peel(state, nat_arg(prev), goal, vocab, suc_eq, rows, pack)
  end

  # Every successor carries the same constant, so one rewrite of the
  # first action and a list induction (`squeeze`) finish the max.
  # A mixed constant still peels one action at a time; that chain is a
  # closed numeral, which reduces.
  defp finish_peel(state, k, goal, vocab, suc_eq, rows, pack) do
    uniform? = rows != [] and Enum.all?(rows, fn {_eq, const, _action} -> const == goal end)

    if uniform? do
      squeeze_peel(state, k, goal, vocab, suc_eq, rows, pack)
    else
      unfold_peel(state, k, goal, vocab, suc_eq, rows)
    end
  end

  defp squeeze_peel(state, k, goal, vocab, suc_eq, [{head_eq, _const, _action} | rest], pack) do
    spell = atom_src(Term.spell(state))
    z = Names.current("z")
    goal_p = paren(goal)

    {after_head, rest_term} =
      case rest do
        [] ->
          {"#{pack.max_bot} #{goal_p}", vocab.bottom}

        _ ->
          actions = Enum.map(rest, &elem(&1, 2))
          tuple = proof_tuple(Enum.map(rest, &elem(&1, 0)))

          {"#{pack.squeeze} (#{cons_list(actions)}) #{spell} #{k} #{goal_p} #{tuple}",
           max_list_of(actions, spell, k)}
      end

    """
    rewrite #{suc_eq} #{spell} #{k} motive (λ w → {w ≡ #{goal} : #{vocab.reward}}) in
    rewrite #{head_eq} motive (λ #{z} → {#{vocab.max} #{z} #{paren(rest_term)} ≡ #{goal} : #{vocab.reward}}) in
    #{after_head}
    """
    |> String.trim_trailing()
  end

  defp proof_tuple([]), do: "tt"

  defp proof_tuple([eq | rest]) do
    inner = proof_tuple(rest)
    if inner == "tt", do: "(#{eq}, tt)", else: "(#{eq}, #{inner})"
  end

  defp squeeze_defs(pack, vocab) do
    n = Names.current("n")
    p = Names.current("p")
    s = Names.current("s")
    k = Names.current("k")
    c = Names.current("c")
    xs = Names.current("xs")
    h = Names.current("h")
    rest = Names.current("r")
    e = Names.current("e")
    max = vocab.max
    reward = vocab.reward
    same = pack.max_same
    bot = pack.max_bot
    req = pack.rest_eq
    sq = pack.squeeze

    """
    def #{same} : evidence Π (#{n} : Nat) → {#{max} #{n} #{n} ≡ #{n} : #{reward}} :=
      λ (#{n} : Nat) →
        match #{n} motive (λ (x : Nat) → {#{max} x x ≡ x : #{reward}})
          | 0 => refl
          | suc #{p} => rewrite #{same} #{p} motive (λ z → {suc z ≡ suc #{p} : #{reward}}) in refl
    def #{bot} : evidence Π (#{n} : Nat) → {#{max} #{n} 0 ≡ #{n} : #{reward}} :=
      λ (#{n} : Nat) →
        match #{n} motive (λ (x : Nat) → {#{max} x 0 ≡ x : #{reward}})
          | 0 => refl
          | suc u => refl
    def #{req} : spec Π (+ #{s} : State) → Π (+ #{k} : Nat) → Π (#{c} : Nat) → Π (#{xs} : List Action) → Type :=
      λ (+ #{s} : State) → λ (+ #{k} : Nat) → λ (#{c} : Nat) → λ (#{xs} : List Action) →
        match #{xs} motive (λ _ → Type)
          | nil => Unit
          | cons #{h} #{rest} => {solve (fst (step #{s} #{h})) #{k} ≡ #{c} : #{reward}} × #{req} #{s} #{k} #{c} #{rest}
    def #{sq} : evidence Π (#{xs} : List Action) → Π (+ #{s} : State) → Π (+ #{k} : Nat) → Π (#{c} : Nat) → Π (#{e} : #{req} #{s} #{k} #{c} #{xs}) → {#{max} #{c} (max-list (map Action Reward (λ (a : Action) → solve (fst (step #{s} a)) #{k}) #{xs})) ≡ #{c} : #{reward}} :=
      λ (#{xs} : List Action) →
        match #{xs} motive (λ (ys : List Action) → Π (+ #{s} : State) → Π (+ #{k} : Nat) → Π (#{c} : Nat) → Π (q : #{req} #{s} #{k} #{c} ys) → {#{max} #{c} (max-list (map Action Reward (λ (a : Action) → solve (fst (step #{s} a)) #{k}) ys)) ≡ #{c} : #{reward}})
          | nil => λ (+ #{s} : State) → λ (+ #{k} : Nat) → λ (#{c} : Nat) → λ (u : Unit) → #{bot} #{c}
          | cons #{h} #{rest} => λ (+ #{s} : State) → λ (+ #{k} : Nat) → λ (#{c} : Nat) → λ (q : {solve (fst (step #{s} #{h})) #{k} ≡ #{c} : #{reward}} × #{req} #{s} #{k} #{c} #{rest}) →
              let (hh, hr) = q in
              rewrite hh motive (λ z → {#{max} #{c} (#{max} z (max-list (map Action Reward (λ (a : Action) → solve (fst (step #{s} a)) #{k}) #{rest}))) ≡ #{c} : #{reward}}) in
              rewrite #{sq} #{rest} #{s} #{k} #{c} hr motive (λ z → {#{max} #{c} z ≡ #{c} : #{reward}}) in
              #{same} #{c}
    """
  end

  defp unfold_peel(state, k, goal, vocab, suc_eq, rows) do
    spell = atom_src(Term.spell(state))
    chain = peel_rows(rows, spell, k, goal, vocab, [])

    """
    rewrite #{suc_eq} #{spell} #{k} motive (λ w → {w ≡ #{goal} : #{vocab.reward}}) in
    #{chain}
    """
    |> String.trim_trailing()
  end

  defp peel_rows([], _spell, _k, _goal, _vocab, _prefix), do: "refl"

  defp peel_rows([{eq, const, _action} | rest], spell, k, goal, vocab, prefix) do
    inner = peel_rows(rest, spell, k, goal, vocab, prefix ++ [const])

    rest_term =
      case rest do
        [] -> vocab.bottom
        _ -> max_list_of(Enum.map(rest, &elem(&1, 2)), spell, k)
      end

    z = Names.current("z")

    nest =
      Enum.reduce(Enum.reverse(prefix), "#{vocab.max} #{z} #{paren(rest_term)}", fn n, acc ->
        "#{vocab.max} #{paren(n)} #{paren(acc)}"
      end)

    """
    rewrite #{eq} motive (λ #{z} → {#{nest} ≡ #{goal} : #{vocab.reward}}) in
    #{inner}
    """
    |> String.trim_trailing()
  end

  defp max_list_of(actions, state_spell, k) do
    "max-list (map Action Reward (λ (a : Action) → solve (fst (step #{state_spell} a)) #{k}) (#{cons_list(actions)}))"
  end

  defp cons_list(actions) do
    Enum.reduce(Enum.reverse(actions), "nil", fn action, acc ->
      term = Term.spell(action)

      if acc == "nil" do
        "cons #{term} nil"
      else
        "cons #{term} (#{acc})"
      end
    end)
  end

  defp form_text_orbit(host, vocab, orbit, taken) do
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

      base =
        if start == t,
          do: "cert-solve-#{Term.label(state)}",
          else: "cert-solve-#{Term.label(state)}-tail"

      {lemma, taken} = Muro.Synth.Book.reserve(base, taken)

      {wrapper, taken} =
        cond do
          start == t -> {nil, taken}
          start == 0 -> Muro.Synth.Book.reserve("cert-solve-#{Term.label(state)}", taken)
          true -> Muro.Synth.Book.reserve("cert-solve-#{Term.label(state)}-from", taken)
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
      {lemma, taken} = Muro.Synth.Book.reserve("cert-solve-#{Term.label(state)}-rep", taken)
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
      {name, taken} = Muro.Synth.Book.reserve("cert-solve-#{Term.label(state)}-#{k}", taken)
      {{name, k, at(orbit, k)[state]}, taken}
    end)
  end

  defp prefix_text(plan, vocab) do
    Enum.map(plan.prefixes, fn {name, k, value} ->
      evidence_def(
        name,
        "{solve #{Term.spell(plan.state)} #{nat_arg(k)} ≡ #{spell_nat(value)} : #{vocab.reward}}",
        "refl"
      )
    end)
  end

  defp aligned_text(host, plan, vocab, orbit, solves) do
    const = spell_nat(plan.const)
    t = orbit.transient

    type =
      "Π (#{Names.current("n")} : Nat) → {solve #{Term.spell(plan.state)} #{shift_term(Names.current("n"), t)} ≡ #{const} : #{vocab.reward}}"

    evidence_def(plan.lemma, type, aligned_body(host, plan.state, vocab, orbit, solves, const))
  end

  defp aligned_body(host, state, vocab, orbit, solves, const) do
    t = orbit.transient
    steps = Enum.map(host.actions, &next(host, state, &1))
    rhs = const
    shown = fn succ -> spell_nat(at(orbit, t)[succ]) end
    fresh = fn succ -> "solve #{Term.spell(succ)} #{shift_term(Names.current("m"), t)}" end
    chain = rewrite_chain(steps, solves, rhs, vocab, shown, fresh)

    goal = fn var ->
      "solve #{Term.spell(state)} #{shift_term(var, t)} ≡ #{const} : #{vocab.reward}"
    end

    """
    λ (#{Names.current("n")} : Nat) →
      match #{Names.current("n")} motive (λ (#{Names.current("k")} : Nat) → {#{goal.(Names.current("k"))}})
        | 0 => refl
        | suc #{Names.current("m")} =>
            #{chain}
    """
  end

  defp repeat_text(host, plan, vocab, orbit, solves) do
    t = orbit.transient
    p = orbit.period
    left = "solve #{Term.spell(plan.state)} #{shift_term(Names.current("n"), t + p)}"
    right = "solve #{Term.spell(plan.state)} #{shift_term(Names.current("n"), t)}"
    type = "Π (#{Names.current("n")} : Nat) → {#{left} ≡ #{right} : #{vocab.reward}}"
    evidence_def(plan.lemma, type, repeat_body(host, plan.state, vocab, orbit, solves))
  end

  defp repeat_body(host, state, vocab, orbit, solves) do
    t = orbit.transient
    p = orbit.period
    steps = Enum.map(host.actions, &next(host, state, &1))
    rhs = "solve #{Term.spell(state)} #{shift_term(Names.current("m"), t + 1)}"
    shown = fn succ -> "solve #{Term.spell(succ)} #{shift_term(Names.current("m"), t)}" end
    fresh = fn succ -> "solve #{Term.spell(succ)} #{shift_term(Names.current("m"), t + p)}" end
    chain = rewrite_chain(steps, solves, rhs, vocab, shown, fresh)

    eq = fn var ->
      "solve #{Term.spell(state)} #{shift_term(var, t + p)} ≡ solve #{Term.spell(state)} #{shift_term(var, t)} : #{vocab.reward}"
    end

    """
    λ (#{Names.current("n")} : Nat) →
      match #{Names.current("n")} motive (λ (#{Names.current("k")} : Nat) → {#{eq.(Names.current("k"))}})
        | 0 => refl
        | suc #{Names.current("m")} =>
            #{chain}
    """
  end

  defp wrapper_text(%{wrapper: nil}, _vocab, _t), do: []

  defp wrapper_text(plan, vocab, t) do
    const = spell_nat(plan.const)

    type =
      "Π (#{Names.current("n")} : Nat) → {solve #{Term.spell(plan.state)} #{shift_term(Names.current("n"), plan.onset)} ≡ #{const} : #{vocab.reward}}"

    body = """
    λ (#{Names.current("n")} : Nat) →
      #{peel(plan.state, plan.lemma, const, vocab.reward, plan.onset, t, Names.current("n"))}
    """

    evidence_def(plan.wrapper, type, body)
  end

  defp peel(_state, lemma, _const, _reward, onset, t, var) when onset >= t do
    "#{lemma} #{var}"
  end

  defp peel(state, lemma, const, reward, onset, t, var) do
    nxt = fresh_local("m#{onset}")
    idx = shift_term(Names.current("k"), onset)

    """
    (match #{var} motive (λ (#{Names.current("k")} : Nat) → {solve #{Term.spell(state)} #{idx} ≡ #{const} : #{reward}})
      | 0 => refl
      | suc #{nxt} =>
          #{peel(state, lemma, const, reward, onset + 1, t, nxt)})
    """
  end

  defp below_periodic(host, arms, states, actions, orbit, solves, vocab, kind, taken) do
    pairs = proof_pairs(host, arms, states, actions, kind)
    {stream_text, stream, taken} = le_stream_setup(kind, orbit, vocab, taken)

    {text, taken, obs, names} =
      Enum.reduce(pairs, {[], taken, [], %{}}, fn {state, left, right},
                                                  {text, taken, obs, names} ->
        base = "cert-below-#{kind}-#{Term.label(state)}-#{Term.spell(left)}-#{Term.spell(right)}"
        {name, taken} = Muro.Synth.Book.reserve(base, taken)
        arm = deciding(host, arms, state)
        ob = obligation(name, state, left, right, arm.name, bit_at(host, arm, state))

        {prelude, body, taken, more} =
          form_below(host, kind, state, left, right, orbit, solves, stream, name, taken, ob)

        lemma = evidence_def(name, below_type(host, kind, state, left, right), body)

        {text ++ prelude ++ [lemma], taken, obs ++ more,
         Map.put(names, {state, left, right}, name)}
      end)

    {stream_text ++ text, taken, obs, names}
  end

  # One lemma for `le` of two solve streams. Each pair calls it. The
  # per-pair nest would repeat the same rewrites once per cell.
  defp le_stream_setup(:action, orbit, vocab, taken) do
    if orbit.period == 1 and is_map(Process.get(:muro_synth_concrete)) do
      {name, taken} = Muro.Synth.Book.reserve("le-stream", taken)
      {[le_stream_def(name, vocab, orbit.transient)], name, taken}
    else
      {[], nil, taken}
    end
  end

  defp le_stream_setup(_kind, _orbit, _vocab, taken), do: {[], nil, taken}

  defp le_stream_def(name, vocab, t) do
    s = Names.current("s")
    r = Names.current("r")
    n = Names.current("n")
    reward = vocab.reward
    groups = stream_groups(t, s, r, reward)
    pis = Enum.map_join(groups, " → ", & &1.pi)
    lams = Enum.map_join(groups, " → ", & &1.lam)

    type =
      "Π (+ #{s} : State) → Π (+ #{r} : State) → #{pis} → Π (#{n} : Nat) → le (solve #{s} #{n}) (solve #{r} #{n})"

    body = """
    λ (+ #{s} : State) → λ (+ #{r} : State) → #{lams} → λ (#{n} : Nat) →
      #{stream_nest(groups, s, r, n, 0)}
    """

    evidence_def(name, type, body)
  end

  defp stream_groups(t, s, r, reward) do
    prefix =
      Enum.map(0..(t - 1), fn k ->
        c = Names.current("c#{k}")
        d = Names.current("d#{k}")
        p = Names.current("p#{k}")
        q = Names.current("q#{k}")
        o = Names.current("o#{k}")
        idx = nat_arg(k)
        eq_l = "{solve #{s} #{idx} ≡ #{c} : #{reward}}"
        eq_r = "{solve #{r} #{idx} ≡ #{d} : #{reward}}"

        %{
          tail: false,
          c: c,
          p: p,
          q: q,
          o: o,
          idx: idx,
          pi:
            "Π (+ #{c} : #{reward}) → Π (+ #{d} : #{reward}) → Π (#{p} : #{eq_l}) → Π (#{q} : #{eq_r}) → Π (#{o} : le #{c} #{d})",
          lam:
            "λ (+ #{c} : #{reward}) → λ (+ #{d} : #{reward}) → λ (#{p} : #{eq_l}) → λ (#{q} : #{eq_r}) → λ (#{o} : le #{c} #{d})"
        }
      end)

    c = Names.current("ct")
    d = Names.current("dt")
    p = Names.current("pt")
    q = Names.current("qt")
    o = Names.current("ot")
    j = Names.current("j")
    shifted = shift_term(j, t)
    tail_l = "Π (+ #{j} : Nat) → {solve #{s} #{shifted} ≡ #{c} : #{reward}}"
    tail_r = "Π (+ #{j} : Nat) → {solve #{r} #{shifted} ≡ #{d} : #{reward}}"

    prefix ++
      [
        %{
          tail: true,
          c: c,
          p: p,
          q: q,
          o: o,
          pi:
            "Π (+ #{c} : #{reward}) → Π (+ #{d} : #{reward}) → Π (#{p} : #{tail_l}) → Π (#{q} : #{tail_r}) → Π (#{o} : le #{c} #{d})",
          lam:
            "λ (+ #{c} : #{reward}) → λ (+ #{d} : #{reward}) → λ (#{p} : #{tail_l}) → λ (#{q} : #{tail_r}) → λ (#{o} : le #{c} #{d})"
        }
      ]
  end

  defp stream_nest(groups, s, r, var, depth) do
    last = length(groups) - 1
    group = Enum.at(groups, depth)

    if depth == last do
      idx = shift_term(var, last)
      z = Names.current("z")

      """
      rewrite (#{group.p} #{var}) motive (λ #{z} → le #{z} (solve #{r} #{idx})) in
      rewrite (#{group.q} #{var}) motive (λ #{z} → le #{group.c} #{z}) in #{group.o}\
      """
      |> String.trim_trailing()
    else
      nxt = if depth == last - 1, do: Names.current("m"), else: fresh_local("k#{depth}")
      k = Names.current("k")
      idx = shift_term(k, depth)
      z = Names.current("z")

      """
      (match #{var} motive (λ (#{k} : Nat) → le (solve #{s} #{idx}) (solve #{r} #{idx}))
        | 0 => rewrite #{group.p} motive (λ #{z} → le #{z} (solve #{r} #{group.idx})) in
      rewrite #{group.q} motive (λ #{z} → le #{group.c} #{z}) in #{group.o}
        | suc #{nxt} =>
            #{stream_nest(groups, s, r, nxt, depth + 1)})
      """
    end
  end

  defp le_stream_call(name, left, right, orbit, solves) do
    t = orbit.transient

    prefix =
      Enum.flat_map(0..(t - 1), fn k ->
        {lname, lval} = concrete_cell(Process.get(:muro_synth_concrete), left, k)
        {rname, rval} = concrete_cell(Process.get(:muro_synth_concrete), right, k)
        [spell_nat(lval), spell_nat(rval), lname, rname, "tt"]
      end)

    tail = [
      spell_nat(at(orbit, t)[left]),
      spell_nat(at(orbit, t)[right]),
      solve_name(solves, left),
      solve_name(solves, right),
      "tt"
    ]

    args = [Term.spell(left), Term.spell(right)] ++ prefix ++ tail
    Enum.join([name | Enum.map(args, &paren_arg/1)], " ")
  end

  defp solve_name(solves, state) do
    case Map.fetch(solves, state) do
      {:ok, name} ->
        name

      :error ->
        spell = Term.spell(state)
        {_key, name} = Enum.find(solves, fn {key, _} -> Term.spell(key) == spell end)
        name
    end
  end

  defp paren_arg(arg) do
    if String.contains?(arg, " ") and not String.starts_with?(arg, "("), do: "(#{arg})", else: arg
  end

  defp form_below(host, :action, state, left, right, orbit, solves, stream, _name, taken, ob) do
    if next(host, state, left) == next(host, state, right) do
      {[], action_form_body(host, state, left, right, nil), taken, [ob]}
    else
      next_l = next(host, state, left)
      next_r = next(host, state, right)

      if is_binary(stream) do
        call = le_stream_call(stream, next_l, next_r, orbit, solves)
        {[], action_form_body(host, state, left, right, call), taken, [ob]}
      else
        tag = "action-#{Term.label(state)}-#{Term.spell(left)}-#{Term.spell(right)}"
        {le_name, taken} = Muro.Synth.Book.reserve("cert-le-#{tag}", taken)
        le_ob = %{ob | name: le_name}

        {prelude, le_body, taken, le_obs} =
          compare_of(le_name, next_l, next_r, orbit, solves, taken, le_ob, tag)

        le_ty =
          "Π (#{Names.current("n")} : Nat) → le (solve #{Term.spell(next_l)} #{Names.current("n")}) (solve #{Term.spell(next_r)} #{Names.current("n")})"

        defs = prelude ++ [evidence_def(le_name, le_ty, le_body)]
        {defs, action_form_body(host, state, left, right, le_name), taken, le_obs ++ [ob]}
      end
    end
  end

  defp form_below(host, :successor, state, left, right, orbit, solves, _stream, name, taken, ob) do
    tag = "successor-#{Term.label(state)}-#{Term.spell(left)}-#{Term.spell(right)}"
    next_l = next(host, state, left)
    next_r = next(host, state, right)
    compare_of(name, next_l, next_r, orbit, solves, taken, ob, tag)
  end

  defp action_form_body(host, state, left, right, call) do
    tail =
      if call == nil do
        "le-refl (solve #{Term.spell(next(host, state, left))} #{Names.current("m")})"
      else
        "#{call} #{Names.current("m")}"
      end

    """
    λ (#{Names.current("n")} : Nat) →
      match #{Names.current("n")} motive (λ (#{Names.current("k")} : Nat) → le (action-at #{Term.spell(state)} #{Term.spell(left)} #{Names.current("k")}) (action-at #{Term.spell(state)} #{Term.spell(right)} #{Names.current("k")}))
        | 0 => tt
        | suc #{Names.current("m")} =>
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
        λ (#{Names.current("n")} : Nat) →
          #{const_nest(left, right, solves, at(orbit, t)[left], t, Names.current("n"), 0)}
        """

        {[], body, taken, [ob]}

      t == 0 ->
        body = """
        λ (#{Names.current("n")} : Nat) →
          #{cycle_nest(left, right, solves, 0, p, name, Names.current("n"), 0)}
        """

        {[], body, taken, [ob]}

      true ->
        {cycle, taken} = Muro.Synth.Book.reserve("cert-cycle-#{tag}", taken)

        cycle_ty =
          "Π (#{Names.current("n")} : Nat) → le (solve #{Term.spell(left)} #{shift_term(Names.current("n"), t)}) (solve #{Term.spell(right)} #{shift_term(Names.current("n"), t)})"

        cycle_body = """
        λ (#{Names.current("n")} : Nat) →
          #{cycle_nest(left, right, solves, t, p, cycle, Names.current("n"), 0)}
        """

        outer = """
        λ (#{Names.current("n")} : Nat) →
          #{transient_nest(left, right, t, cycle, Names.current("n"), 0)}
        """

        {[evidence_def(cycle, cycle_ty, cycle_body)], outer, taken, [%{ob | name: cycle}, ob]}
    end
  end

  defp const_zero(left, right, depth) do
    case Process.get(:muro_synth_concrete) do
      table when is_map(table) ->
        {lname, lval} = concrete_cell(table, left, depth)
        {rname, _rval} = concrete_cell(table, right, depth)
        shown = spell_nat(lval)
        idx = nat_arg(depth)

        """
        rewrite #{lname} motive (λ #{Names.current("z")} → le #{Names.current("z")} (solve #{Term.spell(right)} #{idx})) in
        rewrite #{rname} motive (λ #{Names.current("z")} → le #{paren(shown)} #{Names.current("z")}) in tt\
        """
        |> String.trim_trailing()

      _ ->
        "tt"
    end
  end

  defp concrete_cell(table, state, depth) do
    row =
      case Map.fetch(table, state) do
        {:ok, row} ->
          row

        :error ->
          spell = Term.spell(state)
          {_key, row} = Enum.find(table, fn {key, _row} -> Term.spell(key) == spell end)
          row
      end

    Map.fetch!(row, depth)
  end

  defp const_nest(left, right, solves, const_left, t, var, depth) when depth == t do
    idx = shift_term(var, t)
    shown = spell_nat(const_left)

    """
    rewrite #{solves[left]} #{var} motive (λ #{Names.current("z")} → le #{Names.current("z")} (solve #{Term.spell(right)} #{idx})) in
    rewrite #{solves[right]} #{var} motive (λ #{Names.current("z")} → le #{paren(shown)} #{Names.current("z")}) in tt\
    """
    |> String.trim_trailing()
  end

  defp const_nest(left, right, solves, const_left, t, var, depth) do
    nxt = if depth == t - 1, do: Names.current("m"), else: fresh_local("k#{depth}")
    idx = shift_term(Names.current("k"), depth)

    """
    (match #{var} motive (λ (#{Names.current("k")} : Nat) → le (solve #{Term.spell(left)} #{idx}) (solve #{Term.spell(right)} #{idx}))
      | 0 => #{const_zero(left, right, depth)}
      | suc #{nxt} =>
          #{const_nest(left, right, solves, const_left, t, nxt, depth + 1)})
    """
  end

  defp cycle_nest(left, right, solves, t, p, self_name, var, depth) when depth == p do
    big = shift_term(var, t + p)
    small = shift_term(var, t)

    """
    rewrite #{solves[left]} #{var} motive (λ #{Names.current("z")} → le #{Names.current("z")} (solve #{Term.spell(right)} #{big})) in
    rewrite #{solves[right]} #{var} motive (λ #{Names.current("z")} → le (solve #{Term.spell(left)} #{small}) #{Names.current("z")}) in
    #{self_name} #{var}\
    """
    |> String.trim_trailing()
  end

  defp cycle_nest(left, right, solves, t, p, self_name, var, depth) do
    nxt = if depth == p - 1, do: Names.current("m"), else: fresh_local("k#{depth}")
    idx = shift_term(Names.current("k"), t + depth)

    """
    (match #{var} motive (λ (#{Names.current("k")} : Nat) → le (solve #{Term.spell(left)} #{idx}) (solve #{Term.spell(right)} #{idx}))
      | 0 => tt
      | suc #{nxt} =>
          #{cycle_nest(left, right, solves, t, p, self_name, nxt, depth + 1)})
    """
  end

  defp transient_nest(_left, _right, t, cycle, var, depth) when depth == t, do: "#{cycle} #{var}"

  defp transient_nest(left, right, t, cycle, var, depth) do
    nxt = if depth == t - 1, do: Names.current("m"), else: fresh_local("k#{depth}")
    idx = shift_term(Names.current("k"), depth)

    """
    (match #{var} motive (λ (#{Names.current("k")} : Nat) → le (solve #{Term.spell(left)} #{idx}) (solve #{Term.spell(right)} #{idx}))
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

  defp bound_binders do
    Process.get(:muro_synth_binders) || %{}
  end

  defp fresh_local(base), do: Names.current(base)
end

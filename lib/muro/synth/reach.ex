defmodule Muro.Synth.Reach do
  @moduledoc """
  The reachability runs in a policy book.

  `dyn-best-pos s k` is false at horizon 0, and otherwise the best
  action from `s` pays a positive reward inside `k` steps.
  `dyn-one` is one action. `dyn-any` is some action. `reaches-pos`
  reads `dyn-one` at the environment's horizon.

  When the cover is finite, closed under `step`, and `cover_match`
  can split it, the book tabulates `dyn-best-pos` for every cover
  state and every horizon up to the environment's. The table is a
  match in the book. The checker does not trust the fill. `dyn-any`
  reads that table. `dyn-one`, the run `eval` calls, is the
  recurrence, so a proof can induct on the horizon. The table is
  not that recurrence.

  Soundness inside the table is an inductive family of `refl`s.
  `dyn-best-pos s 0` agrees with `false`. `dyn-best-pos s (j + 1)`
  agrees with one step of `dyn-any s j`, and that step reads the
  table at horizon `j`. The chain ends at the zero arm. Each cell is
  its own evidence, named `dyn-reach-holds` with the state and the
  horizon. A wrong cell fails that evidence. The table is not shown
  to be sound by comparing it, in one shot, with the recurrence
  unfolded out to the horizon.

  A horizon past the reachability table, and a state off the cover,
  fall back to the `*-rec` recurrence. `dyn-known` calls
  `dyn-any-rec` in both cases. That block is `dyn-best-rec`,
  `dyn-one-rec`, and `dyn-any-rec`. It does not call the table. The
  call is legal because it is not inside the block.

  A cover that is not closed, that the match cannot split, or that
  is larger than `@domain_cap` states, keeps the three recursive
  runs and emits no table. The search's own memo of the same
  recursion is not this table, and the checker never reads it.
  """

  alias Muro.Synth.Book
  alias Muro.Synth.Term

  @domain_cap 100_000

  @doc """
  The reachability text, and the names it reserved.

  `best`, `one`, and `any` are the runs `eval` calls.
  """
  def sources(host, best, one, any, pos, taken, rec \\ nil) do
    actions = actions_of(host)
    states = cover(host)

    # A class proof on a large cover inducts on the recurrence. The
    # per-state table is not part of that certificate.
    if Process.get(:muro_synth_class_recur) != true and tabulate?(host, states, actions) do
      case prepare(host, states) do
        :recur ->
          {recursive(best, one, any, pos, actions), taken}

        {:ok, bits} ->
          tabulated(host, states, bits, best, one, any, pos, actions, taken, rec)
      end
    else
      {recursive(best, one, any, pos, actions), taken}
    end
  end

  defp tabulated(host, states, bits, best, one, any, pos, actions, taken, rec) do
    saved = taken
    {known, taken} = Book.reserve("dyn-known", taken)
    {best_rec, taken} = pick_rec(rec, :best, "dyn-best-rec", taken)
    {one_rec, taken} = pick_rec(rec, :one, "dyn-one-rec", taken)
    {any_rec, taken} = pick_rec(rec, :any, "dyn-any-rec", taken)
    {one_tab, taken} = Book.reserve("dyn-one-tab", taken)

    case known_match(host, states, bits, any_rec) do
      :open ->
        {recursive(best, one, any, pos, actions), saved}

      {:ok, known_text} ->
        {evidence, taken} = evidence(host, states, best, any, taken)

        text =
          Enum.join(
            [
              recursive(best_rec, one_rec, any_rec, pos, actions),
              front(best, known, one, one_tab, any, pos, actions, known_text, best_rec),
              evidence
            ],
            "\n"
          )

        {text, taken}
    end
  end

  # The caller reserved the recurrence names when it needs to mention
  # them. Otherwise this block reserves them, as it always did.
  defp pick_rec(nil, _key, base, taken), do: Book.reserve(base, taken)

  defp pick_rec(rec, key, _base, taken) when is_map(rec) do
    {Map.fetch!(rec, key), taken}
  end

  defp known_match(host, states, bits, any_rec) do
    by_spell = Map.new(states, fn state -> {Term.spell(state), bits_of(bits, state)} end)

    body_of = fn spell ->
      horizon_body(any_rec, paren(spell), Map.fetch!(by_spell, spell), host.horizon)
    end

    miss = fn src -> "#{any_rec} #{paren(src)} j" end

    Term.cover_match(host.schema, "s", states, fn _src -> "Bool" end, body_of, miss)
  end

  # `bits` is `best_pos` at horizons 1..horizon. The last `suc` is
  # every larger horizon, and it calls the recurrence.
  defp horizon_body(any_rec, spell, [], _horizon) do
    "#{any_rec} #{spell} j"
  end

  defp horizon_body(any_rec, spell, bits, horizon) do
    nest(any_rec, spell, bits, horizon, "j", 0)
  end

  defp nest(any_rec, spell, [bit], horizon, var, index) do
    nxt = "rk#{index}"

    """
    (match #{var} motive (λ _ → Bool)
      | 0 => #{word(bit)}
      | suc #{nxt} => #{any_rec} #{spell} #{paren(apply_sucs(nxt, horizon))})
    """
  end

  defp nest(any_rec, spell, [bit | rest], horizon, var, index) do
    nxt = "rk#{index}"

    """
    (match #{var} motive (λ _ → Bool)
      | 0 => #{word(bit)}
      | suc #{nxt} => #{nest(any_rec, spell, rest, horizon, nxt, index + 1)})
    """
  end

  defp apply_sucs(var, 0), do: var
  defp apply_sucs(var, 1), do: "suc #{var}"
  defp apply_sucs(var, n) when n > 1, do: "suc (" <> apply_sucs(var, n - 1) <> ")"

  # `one` is the recurrence `eval` calls. `one_tab` is the same
  # match reading the table, and `any` calls that, so the agreement
  # stays a chain of closed bits.
  defp front(best, known, one, one_tab, any, pos, actions, known_text, best_rec) do
    """
    def #{best} : run Π (+ s : State) → Π (+ k : Nat) → Bool :=
      λ (+ s : State) → λ (+ k : Nat) →
        match k motive (λ _ → Bool)
          | 0 => false
          | suc j => #{known} s j

    def #{known} : run Π (+ s : State) → Π (+ j : Nat) → Bool :=
      λ (+ s : State) → λ (+ j : Nat) →
        #{known_text}

    def #{one} : run Π (+ s : State) → Π (+ a : Action) → Π (+ k : Nat) → Bool :=
      λ (+ s : State) → λ (+ a : Action) → λ (+ k : Nat) →
        (match (#{pos} (snd (step s a))) motive (λ _ → Bool)
          | true => true
          | false => #{best_rec} (fst (step s a)) k)

    def #{one_tab} : run Π (+ s : State) → Π (+ a : Action) → Π (+ k : Nat) → Bool :=
      λ (+ s : State) → λ (+ a : Action) → λ (+ k : Nat) →
        (match (#{pos} (snd (step s a))) motive (λ _ → Bool)
          | true => true
          | false => #{best} (fst (step s a)) k)

    def #{any} : run Π (+ s : State) → Π (+ j : Nat) → Bool :=
      λ (+ s : State) → λ (+ j : Nat) →
        #{any_body(one_tab, actions)}
    """
  end

  # The block descends on the horizon. `best` is first. `one` passes
  # that same horizon to it. `any` passes its horizon to `one`. The
  # call from `suc j` is the smaller argument, and `any` is later in
  # the block.
  defp recursive(best, one, any, pos, actions) do
    """
    def #{best} : run Π (+ s : State) → Π (+ k : Nat) → Bool :=
      λ (+ s : State) → λ (+ k : Nat) →
        match k motive (λ _ → Bool)
          | 0 => false
          | suc j => #{any} s j

    def #{one} : run Π (+ s : State) → Π (+ a : Action) → Π (+ k : Nat) → Bool :=
      λ (+ s : State) → λ (+ a : Action) → λ (+ k : Nat) →
        (match (#{pos} (snd (step s a))) motive (λ _ → Bool)
          | true => true
          | false => #{best} (fst (step s a)) k)

    def #{any} : run Π (+ s : State) → Π (+ j : Nat) → Bool :=
      λ (+ s : State) → λ (+ j : Nat) →
        #{any_body(one, actions)}
    """
  end

  # The last action is the false-to-false match, the same term a
  # fold over the action list reduces to. A bare call is the same
  # bool and is not that term.
  defp any_body(one, [action]) do
    """
    (match (#{one} s #{action} j) motive (λ _ → Bool)
      | true => true
      | false => false)
    """
  end

  defp any_body(one, [action | rest]) do
    """
    (match (#{one} s #{action} j) motive (λ _ → Bool)
      | true => true
      | false => #{any_body(one, rest)})
    """
  end

  # One evidence per cell. The name carries the state and the horizon,
  # so a wrong cell is that definition. Horizon 0 agrees with `false`.
  # Horizon `j + 1` agrees with one step of `dyn-any` at `j`.
  defp evidence(host, states, best, any, taken) do
    {blocks, taken} =
      Enum.flat_map_reduce(states, taken, fn state, taken ->
        spell = Term.spell(state)
        shown = paren(spell)

        Enum.map_reduce(cell_equations(best, any, shown, host.horizon), taken, fn
          {horizon, equation}, taken ->
            {name, taken} = Book.reserve(cell_name(spell, horizon), taken)
            {"def #{name} : evidence {#{equation}} := refl\n", taken}
        end)
      end)

    {Enum.join(blocks, "\n"), taken}
  end

  defp cell_equations(best, any, spell, horizon) do
    steps =
      if horizon <= 0 do
        []
      else
        Enum.map(0..(horizon - 1), fn j ->
          {j + 1, "#{best} #{spell} #{j + 1} ≡ #{any} #{spell} #{j} : Bool"}
        end)
      end

    [{0, "#{best} #{spell} 0 ≡ false : Bool"} | steps]
  end

  defp cell_name(spell, horizon) do
    tag =
      spell
      |> String.replace(~r/[^A-Za-z0-9]+/u, "-")
      |> String.trim("-")

    tag = if tag == "", do: "cell", else: tag
    "dyn-reach-holds-#{tag}-#{horizon}"
  end

  defp prepare(host, states) do
    steps = step_table(host, states)

    if closed?(states, steps) do
      {:ok, bits(host, states, steps)}
    else
      :recur
    end
  end

  defp step_table(host, states) do
    Map.new(states, fn state ->
      row =
        Enum.map(host.actions, fn action ->
          {next, reward} = host.step.(state, action)
          {next, reward}
        end)

      {key(state), row}
    end)
  end

  defp closed?(states, steps) do
    known = MapSet.new(states, &key/1)

    Enum.all?(steps, fn {_key, row} ->
      Enum.all?(row, fn {next, _reward} -> MapSet.member?(known, key(next)) end)
    end)
  end

  # `rows[k]` is `best_pos(s, k + 1)`: some action pays now, or the
  # successor's bit at the previous horizon is set. Horizon 0 is the
  # false base and is not stored.
  defp bits(host, states, steps) do
    keys = Enum.map(states, &key/1)

    if host.horizon == 0 do
      Map.new(keys, &{&1, []})
    else
      prev = Map.new(keys, &{&1, false})

      {rows, _prev} =
        Enum.reduce(1..host.horizon, {Map.new(keys, &{&1, []}), prev}, fn _k, {rows, prev} ->
          layer =
            Map.new(keys, fn kstate ->
              bit =
                Enum.any?(Map.fetch!(steps, kstate), fn {next, reward} ->
                  positive?(reward) or Map.fetch!(prev, key(next))
                end)

              {kstate, bit}
            end)

          rows =
            Map.new(keys, fn kstate ->
              {kstate, Map.fetch!(rows, kstate) ++ [Map.fetch!(layer, kstate)]}
            end)

          {rows, layer}
        end)

      rows
    end
  end

  defp bits_of(bits, state), do: Map.fetch!(bits, key(state))

  defp positive?(0), do: false
  defp positive?(n) when is_integer(n), do: n > 0
  defp positive?(_reward), do: false

  defp cover(host) do
    case Muro.Synth.Oracle.cover(host) do
      states when is_list(states) -> Enum.uniq_by(states, &key/1)
      _ -> []
    end
  end

  defp tabulate?(host, states, actions) do
    is_integer(host[:horizon]) and host.horizon >= 0 and host[:schema] != nil and
      states != [] and length(states) <= @domain_cap and actions != []
  end

  defp actions_of(host) do
    if is_list(host[:actions]), do: host.actions, else: []
  end

  defp key(%Term{value: value}), do: value
  defp key(other), do: other

  defp word(true), do: "true"
  defp word(false), do: "false"

  defp paren(spell) do
    cond do
      String.starts_with?(spell, "(") -> spell
      String.contains?(spell, " ") or String.contains?(spell, "\n") -> "(#{spell})"
      true -> spell
    end
  end
end

defmodule Muro.Synth.Feature do
  @moduledoc false

  # Dynamics feature discovery for a finite environment.
  #
  # The templates follow CSHRL.Synthesis.DynFeatureTemplate
  # (`has-pos-reward`, `is-self-loop`) and the dynamics half of
  # CSHRL.Synthesis.AutoFeatureNat (`leads-terminal`). The pipeline is
  # the one in literate/CSHRLSynthesis.lagda.tex §Feature Discovery
  # (`sec:ftl`): enumerate, drop trivial features, drop redundant ones.
  # CSHRL.Synthesis.CSHRLLoop raises depth on `cegar-needed`; the loop
  # already does that when the version space is empty.
  #
  # This module is outside the certificate. `eval-feature` in the policy
  # book is a `run` over the environment's `step`, and the checker sees
  # that term. The search that chose the template is not evidence.
  #
  # A state constructor is not a feature. `state-is`, factorization, and
  # thresholds from AutoFeatureNat are not instantiated: those templates
  # read a numeric state index. Structural templates (`vals-eq`,
  # `spread-eq`, `pair-any`, `len-is` in FeatureTemplate.agda) are not
  # instantiated either. The states this host sees are atomic
  # constructors, and there is no term to walk.

  @doc """
  Features for `host`, hints first-filtered with the dynamics templates.

  `hints` are the nullary `Feature` constructors the book declared.
  A book that declares none passes `[]`.
  """
  def discover(host, hints) when is_list(hints) do
    states = Muro.Synth.Oracle.cover(host)
    taken = taken_names(host.book)
    candidates = enumerate(host, states, hints, taken)
    eval = fn spec, state -> eval_spec(host, &host.eval_feature.(&1, &2), spec, state) end

    candidates
    |> filter_nontrivial(states, eval)
    |> drop_subsumed()
    |> drop_equivalent(states, eval)
  end

  @doc """
  The bit of `spec` at `state`. `hint_eval.(name, state)` reads a declared feature.
  """
  def eval_spec(_host, hint_eval, %{kind: :hint, name: name}, state)
      when is_function(hint_eval, 2) do
    hint_eval.(name, state)
  end

  def eval_spec(host, _hint_eval, %{kind: :has_pos_reward, action: action}, state) do
    {_next, reward} = host.step.(state, action)
    positive?(reward)
  end

  def eval_spec(host, _hint_eval, %{kind: :is_self_loop, action: action}, state) do
    {next, _reward} = host.step.(state, action)
    next == state
  end

  def eval_spec(host, _hint_eval, %{kind: :leads_terminal, action: action}, state) do
    {next, _reward} = host.step.(state, action)
    terminal?(host, next)
  end

  # A state is terminal when every action stays there. That is the
  # absorbing state of the step function. It is not a label on a
  # constructor.
  def terminal?(host, state) do
    Enum.all?(host.actions, fn action ->
      {next, _reward} = host.step.(state, action)
      next == state
    end)
  end

  defp enumerate(host, states, hints, taken) do
    {dyn, _taken} = enumerate_dyn(host, states, taken)

    Enum.reduce(hints, dyn, fn name, specs ->
      specs ++ [%{name: name, kind: :hint, action: nil}]
    end)
  end

  defp enumerate_dyn(host, states, taken) do
    actions = host.actions

    {reward_specs, taken} =
      if nat_rewards?(host, states) do
        add_all(taken, actions, "has-pos-reward", :has_pos_reward)
      else
        {[], taken}
      end

    {loops, taken} = add_all(taken, actions, "is-self-loop", :is_self_loop)
    {leads, taken} = add_all(taken, actions, "leads-terminal", :leads_terminal)
    {reward_specs ++ loops ++ leads, taken}
  end

  defp add_all(taken, actions, prefix, kind) do
    Enum.map_reduce(actions, taken, fn action, taken ->
      name = fresh("#{prefix}-#{action}", taken)
      {%{name: name, kind: kind, action: action}, take(taken, name)}
    end)
  end

  defp nat_rewards?(host, states) do
    Enum.all?(states, fn state ->
      Enum.all?(host.actions, fn action ->
        {_next, reward} = host.step.(state, action)
        closed_nat?(reward)
      end)
    end)
  end

  defp positive?(0), do: false
  defp positive?({:suc, _n}), do: true
  defp positive?(n) when is_integer(n), do: n > 0
  defp positive?(_reward), do: false

  defp closed_nat?(0), do: true
  defp closed_nat?({:suc, n}), do: closed_nat?(n)
  defp closed_nat?(n) when is_integer(n) and n >= 0, do: true
  defp closed_nat?(_reward), do: false

  defp filter_nontrivial(specs, states, eval) do
    Enum.filter(specs, fn spec ->
      values = Enum.map(states, &eval.(spec, &1))
      not all_true?(values) and not all_false?(values)
    end)
  end

  # Agda `all-true-list []` and `all-false-list []` are both true, so a
  # feature on an empty cover is trivial. `Enum.all?/2` is true on `[]`.
  defp all_true?(values), do: Enum.all?(values, &(&1 == true))

  defp all_false?(values), do: Enum.all?(values, &(&1 == false))

  # FeatureTemplate.eliminate-redundant: `pair-any i j` subsumes
  # `vals-eq i j` and `spread-eq i j`. No dynamics template has that
  # shape. The clause is here so a later structural spec drops the same
  # way. Dynamics redundancy is the equivalence pass below.
  defp drop_subsumed(specs) do
    Enum.filter(specs, fn spec ->
      not Enum.any?(specs, &subsumes?(&1, spec))
    end)
  end

  defp subsumes?(%{kind: :pair_any, i: i, j: j}, %{kind: kind, i: i, j: j})
       when kind in [:vals_eq, :spread_eq],
       do: true

  defp subsumes?(_other, _spec), do: false

  # Two features with one truth vector on the cover define the same
  # atom of the version space. Keep the earlier one.
  defp drop_equivalent(specs, states, eval) do
    Enum.reduce(specs, [], fn spec, kept ->
      vector = Enum.map(states, &eval.(spec, &1))

      if Enum.any?(kept, fn other -> Enum.map(states, &eval.(other, &1)) == vector end) do
        kept
      else
        kept ++ [spec]
      end
    end)
  end

  defp taken_names(book) when is_list(book) do
    Enum.reduce(book, MapSet.new(), fn entry, acc ->
      Enum.reduce(entry_names(entry), acc, &take(&2, &1))
    end)
  end

  defp taken_names(_book), do: MapSet.new()

  defp entry_names(%{kind: :data, name: name, ctors: ctors}),
    do: [name | Enum.map(ctors, & &1.name)]

  defp entry_names(%{kind: :import}), do: []
  defp entry_names(%{name: name}), do: [name]
  defp entry_names(_entry), do: []

  defp fresh(base, taken) do
    if occupied?(base, taken) do
      n = Enum.find(2..10_000, &(not occupied?("#{base}-#{&1}", taken)))
      "#{base}-#{n}"
    else
      base
    end
  end

  defp occupied?(name, taken) do
    MapSet.member?(taken, name) or
      MapSet.member?(taken, {:elixir, Muro.Emit.elixir_base(name)})
  end

  defp take(taken, name) do
    taken
    |> MapSet.put(name)
    |> MapSet.put({:elixir, Muro.Emit.elixir_base(name)})
  end
end

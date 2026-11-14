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
  # a threshold on a raw state index are not instantiated.
  #
  # When `State` has a field, structural templates are read off that
  # term: the constructor, equality of two fields, a field equal to a
  # closed Nat, and on a list (or on the fields of one constructor)
  # `vals-eq`, `spread-eq`, `pair-any`, and `len-is`. The first pass
  # opens one field. A later pass opens more, up to `Term.path_bound/0`.
  # An atomic `State` is not walked. A bare Nat state is not a template.

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

    reduce(candidates, states, eval)
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

  def eval_spec(host, _hint_eval, %{kind: kind} = spec, state)
      when kind in [:ctor_is, :vals_eq, :spread_eq, :pair_any, :len_is, :nat_is] do
    Muro.Synth.Term.eval_spec(host.schema, spec, state)
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
    {dyn, taken} = enumerate_dyn(host, states, taken)
    {structural, _taken} = enumerate_structural(host, states, taken)

    Enum.reduce(hints, dyn ++ structural, fn name, specs ->
      specs ++ [%{name: name, kind: :hint, action: nil}]
    end)
  end

  defp enumerate_structural(host, states, taken) do
    if host[:structured] && host[:structural] != false && host[:schema] do
      Muro.Synth.Term.templates(host.schema, states, taken, Muro.Synth.Term.first_path_depth())
    else
      {[], taken}
    end
  end

  @doc """
  Further structural tests that separate `earlier` from `later`.

  The result is the filtered union, or `[]` when the two carriers still
  agree. Depth is not involved.
  """
  def invent(host, earlier, later) do
    cond do
      not structural_host?(host) ->
        []

      true ->
        taken = taken_names(host.book)

        taken =
          Enum.reduce(host.feature_specs, taken, fn spec, taken ->
            take(taken, spec.name)
          end)

        {added, _taken} =
          Muro.Synth.Term.invent(host.schema, earlier, later, host.feature_specs, taken)

        if added == [] do
          []
        else
          specs = host.feature_specs ++ added
          states = Muro.Synth.Oracle.cover(host)
          hint_eval = host.hint_eval
          eval = fn spec, state -> eval_spec(host, hint_eval, spec, state) end

          reduced = reduce(specs, states, eval)

          if separates?(reduced, earlier, later, eval), do: reduced, else: []
        end
    end
  end

  defp separates?(specs, earlier, later, eval) do
    Enum.map(specs, &eval.(&1, earlier)) != Enum.map(specs, &eval.(&1, later))
  end

  defp structural_host?(host) do
    host[:structured] == true and host[:structural] != false and host[:schema] != nil
  end

  @doc """
  Re-enumerate structural tests one field deeper, up to the path bound.

  `{:ok, specs, depth}` separates `earlier` from `later`. `{:stop, specs,
  depth}` has reached the bound, or this host has no structural walk.
  `specs` is `nil` when nothing was re-enumerated. The caller filters
  nothing further: the specs here are already reduced.
  """
  def deepen(host, earlier, later) do
    depth = Map.get(host, :path_depth, Muro.Synth.Term.first_path_depth())

    cond do
      not structural_host?(host) ->
        {:stop, nil, depth}

      depth >= Muro.Synth.Term.path_bound() ->
        {:stop, nil, depth}

      true ->
        climb(host, depth, earlier, later)
    end
  end

  defp climb(host, depth, earlier, later) do
    next = depth + 1
    specs = enumerate_at(host, next)
    hint_eval = Map.get(host, :hint_eval, host.eval_feature)
    eval = fn spec, state -> eval_spec(host, hint_eval, spec, state) end

    cond do
      separates?(specs, earlier, later, eval) ->
        {:ok, specs, next}

      next >= Muro.Synth.Term.path_bound() ->
        {:stop, specs, next}

      true ->
        host = host |> Map.put(:feature_specs, specs) |> Map.put(:path_depth, next)
        climb(host, next, earlier, later)
    end
  end

  defp enumerate_at(host, depth) do
    states = Muro.Synth.Oracle.cover(host)
    {dyn, hints} = partition_specs(host.feature_specs || [])
    taken = taken_names(host.book)

    taken =
      Enum.reduce(dyn ++ hints, taken, fn spec, taken ->
        take(taken, spec.name)
      end)

    {structural, _taken} = Muro.Synth.Term.templates(host.schema, states, taken, depth)
    hint_eval = Map.get(host, :hint_eval, host.eval_feature)
    eval = fn spec, state -> eval_spec(host, hint_eval, spec, state) end
    reduce(dyn ++ structural ++ hints, states, eval)
  end

  defp partition_specs(specs) do
    dyn =
      Enum.filter(specs, fn spec ->
        spec.kind in [:has_pos_reward, :is_self_loop, :leads_terminal]
      end)

    hints = Enum.filter(specs, &(&1.kind == :hint))
    {dyn, hints}
  end

  defp reduce(specs, states, eval) do
    specs
    |> filter_nontrivial(states, eval)
    |> drop_subsumed()
    |> drop_equivalent(states, eval)
  end

  defp enumerate_dyn(host, states, taken) do
    actions = host.actions

    {reward_specs, taken} =
      if nat_rewards?(host, states) do
        add_all(taken, actions, "has-pos-reward", :has_pos_reward)
      else
        {[], taken}
      end

    {loops, leads, taken} =
      if state_comparable?(host) do
        {loops, taken} = add_all(taken, actions, "is-self-loop", :is_self_loop)
        {leads, taken} = add_all(taken, actions, "leads-terminal", :leads_terminal)
        {loops, leads, taken}
      else
        {[], [], taken}
      end

    {reward_specs ++ loops ++ leads, taken}
  end

  # A finite inhabitant list is an exhaustive match. An open structured
  # state is a run over its schema. A direct inductive back-edge is
  # that run. A function, a mutual family, a linear field, an erased
  # constructor argument, or a back-edge under a list or a product has
  # neither test. A nullary state stays.
  defp state_comparable?(host) do
    cond do
      host[:structured] != true ->
        true

      is_list(host[:inhabitants]) and host.inhabitants != [] ->
        true

      true ->
        Muro.Synth.Term.equatable?(host[:schema])
    end
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
  # `vals-eq i j` and `spread-eq i j` on the same path. Dynamics
  # templates have no such pair. Two atoms with one truth vector still
  # collapse below, whichever template produced them.
  defp drop_subsumed(specs) do
    Enum.filter(specs, fn spec ->
      not Enum.any?(specs, &subsumes?(&1, spec))
    end)
  end

  defp subsumes?(%{kind: :pair_any, i: i, j: j} = pair, %{kind: kind, i: i, j: j} = spec)
       when kind in [:vals_eq, :spread_eq] do
    same_site?(pair, spec)
  end

  defp subsumes?(_other, _spec), do: false

  defp same_site?(left, right) do
    Map.get(left, :path, []) == Map.get(right, :path, []) and
      Map.get(left, :view) == Map.get(right, :view) and
      Map.get(left, :ctor) == Map.get(right, :ctor) and
      Map.get(left, :guards) == Map.get(right, :guards)
  end

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

defmodule Muro.Policies.Seek do
  @moduledoc """
  Search for a chain by acting in an environment.

  The chain is asked at every state. `step` returns the next state and
  a reward. A counterexample is a visited state where another action
  has a higher return: the reward of taking it once, then following the
  chain. The predicate for that action is a conjunction grown one
  feature function at a time. A test is kept when it rules out a state
  where the action is no better, and still holds on a state where it is.
  The episode is rolled again until the chain agrees with every visited
  state.
  """

  alias Muro.Policies.{Chain, Library}
  alias Muro.Environments.Lam

  @doc """
  Act in `Muro.Environments.Lam` from `starts` until the chain agrees
  with the states it visits, or the round limit is hit.
  """
  def run(starts, fuel \\ 64) when is_list(starts) do
    seek(starts, [], fuel, 0, [])
  end

  @doc """
  The action the chain takes at `term`. The default is `:spine`.
  """
  def choose(chain, term) do
    Chain.eval_chain(chain, Lam.default(), &holds?/2, term)
  end

  @doc """
  Sum of rewards from `term` following `choose`, until the episode ends.
  """
  def returns(term, choose, fuel \\ 64) do
    follow(term, choose, fuel, 0)
  end

  defp seek(_starts, chain, _fuel, round, _seen) when round > 6 do
    {:rounds, chain}
  end

  defp seek(starts, chain, fuel, round, seen) do
    choose = fn term -> choose(chain, term) end
    labeled = labels(starts, choose, fuel)

    cex =
      Enum.filter(labeled, fn {term, action} -> choose.(term) != action end)

    if cex == [] do
      observations = Enum.map(labeled, fn {term, _} -> Lam.observe(term) end)
      {:ok, %{chain: chain, features: Library.offered(observations), rounds: round}}
    else
      case learn(labeled) do
        {:ok, next} ->
          if next in seen do
            {:cycle, next}
          else
            seek(starts, next, fuel, round + 1, [next | seen])
          end

        other ->
          other
      end
    end
  end

  defp labels(starts, choose, fuel) do
    starts
    |> Enum.flat_map(&visit(&1, choose, fuel, []))
    |> Enum.uniq()
    |> Enum.map(fn term -> {term, best_action(term, choose, fuel)} end)
  end

  defp visit(term, choose, fuel, acc) do
    cond do
      Lam.stop?(term) ->
        Enum.reverse(acc)

      fuel == 0 ->
        Enum.reverse(acc)

      true ->
        case Lam.step(term, choose.(term)) do
          {:ok, next, _reward} -> visit(next, choose, fuel - 1, [term | acc])
          :error -> Enum.reverse([term | acc])
        end
    end
  end

  defp best_action(term, choose, fuel) do
    scored =
      for action <- Lam.actions(),
          return = deviate(term, action, choose, fuel),
          return != :illegal,
          do: {action, return}

    {action, _return} =
      Enum.max_by(scored, fn {action, return} ->
        {return, action == Lam.default()}
      end)

    action
  end

  defp deviate(term, action, choose, fuel) do
    case Lam.step(term, action) do
      {:ok, next, reward} -> reward + follow(next, choose, fuel - 1, 0)
      :error -> :illegal
    end
  end

  defp follow(term, choose, fuel, acc) do
    cond do
      Lam.stop?(term) -> acc
      fuel == 0 -> acc
      true ->
        case Lam.step(term, choose.(term)) do
          {:ok, next, reward} -> follow(next, choose, fuel - 1, acc + reward)
          :error -> acc - 1_000
        end
    end
  end

  defp learn(labeled) do
    pos = for {term, :arg} <- labeled, do: term
    neg = for {term, action} <- labeled, action != :arg, do: term
    observations = Enum.map(labeled, fn {term, _} -> Lam.observe(term) end)

    case clauses(pos, neg, Library.offered(observations)) do
      {:ok, preds} -> {:ok, Enum.map(preds, &{&1, :arg})}
      other -> other
    end
  end

  defp clauses([], _neg, _features), do: {:ok, []}

  defp clauses(pos, neg, features) do
    case one_clause(pos, neg, features, true, 5) do
      {:ok, clause} ->
        covered = Enum.filter(pos, &holds_pred?(clause, &1))
        rest = pos -- covered

        if covered == [] do
          {:unseparated, length(pos)}
        else
          case clauses(rest, neg, features) do
            {:ok, more} -> {:ok, [clause | more]}
            other -> other
          end
        end

      other ->
        other
    end
  end

  defp one_clause(pos, neg, features, clause, fuel) do
    good = Enum.filter(pos, &holds_pred?(clause, &1))
    bad = Enum.filter(neg, &holds_pred?(clause, &1))
    used = Chain.reads(clause)

    cond do
      good == [] -> :empty
      bad == [] -> {:ok, clause}
      fuel == 0 -> :fuel
      true ->
        case best_literal(good, bad, features -- used) do
          nil -> :stuck
          lit -> one_clause(pos, neg, features, conj(clause, lit), fuel - 1)
        end
    end
  end

  defp best_literal(good, bad, features) do
    scored =
      for feature <- features,
          lit <- [{:feat, feature}, {:not, {:feat, feature}}],
          kept = Enum.count(good, &holds_pred?(lit, &1)),
          kept > 0,
          dropped = Enum.count(bad, &(not holds_pred?(lit, &1))),
          dropped > 0,
          do: {dropped, kept, lit}

    case Enum.sort_by(scored, fn {dropped, kept, _lit} -> {-dropped, -kept} end) do
      [{_dropped, _kept, lit} | _] -> lit
      [] -> nil
    end
  end

  defp conj(true, lit), do: lit
  defp conj(clause, lit), do: {:and, clause, lit}

  defp holds_pred?(pred, term) do
    Chain.eval(pred, &holds?/2, term)
  end

  defp holds?(feature, term), do: Library.apply(feature, Lam.observe(term))
end

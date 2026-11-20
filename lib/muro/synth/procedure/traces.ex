defmodule Muro.Synth.Procedure.Traces do
  @moduledoc """
  The version-space search, as a procedure.

  `run/2` is that search: `Muro.Synth.cegis_loop/2`. The candidates,
  their order, and the book are the ones that search already produces.
  `generate/1`, `evaluate/2`, and `rank/1` expose the same version
  space, the same predicate reading, and the same size order. They do
  not replace the loop.
  """

  @behaviour Muro.Synth.Procedure

  alias Muro.Synth

  @doc """
  Run the version-space search on `path`.

  `opts` are the options `Muro.Synth.cegis_loop/2` takes. The result
  is that function's result.
  """
  def run(path, opts \\ []) when is_binary(path) and is_list(opts) do
    Synth.cegis_loop(path, opts)
  end

  @doc """
  The version space at `:depth`, as a stream.

  `:features` is the list `Muro.Synth.enumerate/2` takes. `:depth`
  defaults to 0. The stream yields that enumeration in its order, one
  depth at a time. Pulling a candidate at depth n builds depth n and
  does not build depth n + 1. Taking the first candidates of depth 0
  does not build a later depth.
  """
  @impl true
  def generate(%{features: features} = context) when is_list(features) do
    depth = Map.get(context, :depth, 0)

    unless is_integer(depth) and depth >= 0 do
      raise ArgumentError, "depth must be a non-negative integer"
    end

    0..depth
    |> Stream.flat_map(fn level ->
      programs = Synth.enumerate(features, level)

      if level == 0 do
        programs
      else
        earlier = Synth.enumerate(features, level - 1)
        Enum.drop(programs, length(earlier))
      end
    end)
  end

  @doc """
  Read `candidate` against `:observations` with `:fuel` steps.

  `:feat` is `feat.(feature, state)` and is required when
  `:observations` is not empty. `:observations` is a list of
  `{state, bit}` and defaults to `[]`. `:fuel` defaults to
  `Muro.Check.default_fuel/0`. `:score` is `score.(candidate)` and
  defaults to 0.

  One step is one predicate constructor `Muro.Synth.eval/3` visits.
  `and` and `or` stop early, as `eval/3` does. An `other` spends one
  step for its constructor and one step for each column it reads.
  Fuel 0, or a budget that runs out before the observations are
  read, returns `{:out_of_fuel, %{candidate: candidate}}`.

  A finished walk returns `{:ok, detail}` with `:candidate`,
  `:agrees`, `:score`, and `:fuel_left`. `:agrees` is true when every
  observation matches, and an empty observation list agrees without
  spending fuel. The version-space search does not call `evaluate/2`.
  Its default fuel does not change that search.
  """
  @impl true
  def evaluate(candidate, context) when is_map(context) do
    fuel = Map.get(context, :fuel, Muro.Check.default_fuel())
    observations = Map.get(context, :observations, [])
    feat = Map.get(context, :feat)
    score = Map.get(context, :score, fn _candidate -> 0 end)

    cond do
      not (is_integer(fuel) and fuel >= 0) ->
        raise ArgumentError, "fuel must be a non-negative integer"

      not is_list(observations) ->
        raise ArgumentError, "observations must be a list"

      observations != [] and not is_function(feat, 2) ->
        raise ArgumentError, "feat is the feature test"

      not is_function(score, 1) ->
        raise ArgumentError, "score must be a function of the candidate"

      true ->
        case walk(candidate, observations, feat, fuel) do
          :out_of_fuel ->
            {:out_of_fuel, %{candidate: candidate}}

          {:ok, agrees, left} ->
            {:ok,
             %{
               candidate: candidate,
               agrees: agrees,
               score: score.(candidate),
               fuel_left: left
             }}
        end
    end
  end

  @doc """
  Order finished evaluations as `Muro.Synth.pick/2` orders predicates.

  Smaller `Muro.Synth.size/1` comes first. A higher `:score` wins
  among equal sizes. An earlier input wins a remaining tie. An
  `{:out_of_fuel, _}` result is omitted. A miss is not omitted.
  """
  @impl true
  def rank(evaluated) when is_list(evaluated) do
    evaluated
    |> Enum.with_index()
    |> Enum.flat_map(fn
      {{:ok, detail}, index} when is_map(detail) -> [{detail, index}]
      {_other, _index} -> []
    end)
    |> Enum.sort_by(fn {detail, index} ->
      {Synth.size(detail.candidate), -number_score(detail), index}
    end)
    |> Enum.map(fn {detail, _index} -> {:ok, detail} end)
  end

  defp number_score(%{score: score}) when is_number(score), do: score
  defp number_score(_detail), do: 0

  defp walk(candidate, observations, feat, fuel) do
    Enum.reduce_while(observations, {:ok, true, fuel}, fn {state, bit}, {:ok, true, left} ->
      case eval_step(candidate, feat, state, left) do
        :out_of_fuel ->
          {:halt, :out_of_fuel}

        {:ok, value, rest} ->
          if value == bit do
            {:cont, {:ok, true, rest}}
          else
            {:halt, {:ok, false, rest}}
          end
      end
    end)
  end

  defp eval_step(pred, feat, state, fuel) do
    case pred do
      true ->
        Synth.eval(pred, feat, state, fuel)

      false ->
        Synth.eval(pred, feat, state, fuel)

      {:feat, _} ->
        Synth.eval(pred, feat, state, fuel)

      {:not, _} ->
        Synth.eval(pred, feat, state, fuel)

      {:and, _, _} ->
        Synth.eval(pred, feat, state, fuel)

      {:or, _, _} ->
        Synth.eval(pred, feat, state, fuel)

      {:self, _, _, _} ->
        Synth.eval(pred, feat, state, fuel)

      {:other, _, _, features} when is_list(features) ->
        Synth.eval(pred, feat, state, fuel)

      other ->
        raise ArgumentError, "not a predicate: #{inspect(other)}"
    end
  end
end

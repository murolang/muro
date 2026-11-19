defmodule Muro.Synth.Procedure do
  @moduledoc """
  One search `mix muro.synth` can run.

  The tool selects a procedure and runs it. The checker is still the
  only acceptance gate: a candidate is written into the book and kept
  only when that book checks.

  A procedure offers candidates, judges one candidate, and orders the
  candidates that finished. `generate/1` is lazy. `evaluate/2` takes a
  fuel bound and stops with an out-of-fuel result when the bound is
  spent, so a walk over a candidate cannot run without a budget.
  `rank/1` orders the candidates that finished.

  `traces` is the version-space search on a book's `step` and the
  observations that `step` supports. It is the only procedure.
  """

  @type context :: map()
  @type evaluation :: {:ok, map()} | {:out_of_fuel, map()}

  @procedures %{"traces" => Muro.Synth.Procedure.Traces}

  @doc """
  Yield candidates.

  `context` is a map. The procedure reads the keys it needs. `traces`
  reads `:features`, the list `Muro.Synth.enumerate/2` takes, and
  `:depth`, a non-negative integer that defaults to 0.

  The result is an `Enumerable`, and it is a stream, not a list.
  Elements are produced when a consumer pulls them. A consumer that
  stops does not force the candidates it did not pull, and a later
  depth is not built until the consumer reaches it.

  `generate/1` does not judge a candidate and does not spend fuel.
  """
  @callback generate(context()) :: Enumerable.t()

  @doc """
  Judge one candidate under a fuel bound.

  `context` is a map. `:fuel` is a non-negative integer, the number of
  steps this call may take. When `:fuel` is omitted the bound is
  `Muro.Check.default_fuel/0`. A step is one unit of the walk the
  procedure already uses to read a candidate. `traces` spends one step
  for each predicate constructor `Muro.Synth.eval/3` visits, in that
  function's order, including the short-circuit of `and` and `or`.

  The walk stops when a step is needed and the remaining fuel is 0.
  The result is then `{:out_of_fuel, detail}`, `detail` names the
  candidate, and no further step is taken. That outcome is not
  agreement and it is not a miss. A walk that finishes inside the
  budget returns `{:ok, detail}`.

  Fuel 0 cannot take a step. A candidate that needs a step at fuel 0
  is out of fuel. The default fuel is the checker's fuel. For `traces`
  it bounds that same predicate reading. The version-space search does
  not call `evaluate/2`, so this default does not change the candidates,
  the order, or the book that search already writes.
  """
  @callback evaluate(candidate :: term(), context()) :: evaluation()

  @doc """
  Order the candidates that finished.

  `evaluated` is a list of `evaluate/2` results. An `{:ok, detail}`
  result is a candidate that was judged. An `{:out_of_fuel, _}` result
  was not judged to the end, and it is not placed among the ordered
  candidates.

  The ordered list is those `{:ok, detail}` results. `traces` orders
  them as `Muro.Synth.pick/2` orders predicates: smaller size, then
  higher `:score`, then the earlier input. A candidate that missed an
  observation is still ordered. The version space drops a miss before
  it ranks. `rank/1` does not spend fuel and does not build candidates.
  """
  @callback rank(evaluated :: [evaluation()]) :: [evaluation()]

  @doc false
  def procedures, do: @procedures

  @doc """
  The `--on` values this tool accepts, in alphabetical order.
  """
  def accepted, do: @procedures |> Map.keys() |> Enum.sort()

  @doc false
  def fetch(name) when is_binary(name) do
    case Map.fetch(@procedures, name) do
      {:ok, module} -> {:ok, module}
      :error -> {:error, unknown_on(name)}
    end
  end

  @doc false
  def unknown_on(name) when is_binary(name) do
    "unknown --on #{name}; accepted: " <> Enum.join(accepted(), ", ")
  end

  @doc false
  def no_step_message do
    "the book has no step and observations to synthesize against"
  end

  @doc """
  `traces` when `path` defines `step` after it checks.

  A book that does not check is `{:error, :book, message}`. A book
  that checks and does not define `step` has no observations for
  `traces`, and the message does not name a flag.
  """
  def select(path, fuel) when is_binary(path) and is_integer(fuel) and fuel > 0 do
    case Muro.Load.file(path, fuel: fuel) do
      {:error, message} ->
        {:error, :book, message}

      {:ok, book} ->
        if defines_step?(book) do
          {:ok, Muro.Synth.Procedure.Traces}
        else
          {:error, :usage, no_step_message()}
        end
    end
  end

  defp defines_step?(book) when is_list(book) do
    Enum.any?(book, &(Map.get(&1, :name) == "step"))
  end
end

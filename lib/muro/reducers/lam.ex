defmodule Muro.Reducers.Lam do
  @moduledoc """
  The `lam` clause of reduction.

  A candidate is an application whose function is a λ. The step is
  `Muro.Subst.inst` of the body with the argument. A path that is not
  such an application is refused. The head has stopped when no such
  application sits on the function spine. Later steps, after the one
  being compared, take that spine application.

  `Muro.Check` is unchanged. Its `whnf` also calls `inst` for a `suc`
  branch, `uncons`, and `let`. This reducer is only the λ case.
  """

  alias Muro.Subst

  @doc """
  Paths of the candidates in `term`, left to right. A path is `:fun`,
  `:arg`, and `:body` from the root. The domain of a λ is not searched.
  """
  def candidates(term), do: walk(term, [])

  @doc """
  The candidate on the function spine, or `:error` when the head has stopped.
  """
  def head_path(term), do: spine(term, [])

  @doc """
  The head has stopped.
  """
  def stopped?(term), do: head_path(term) == :error

  @doc """
  Substitute the argument at `path` into the λ body. `:error` when
  that subterm is not an application of a λ.
  """
  def reduce(term, path) when is_list(path) do
    with {:ok, {:app, {:lam, _, _, _, body}, arg}} <- fetch(term, path) do
      put(term, path, Subst.inst(body, arg))
    else
      _ -> :error
    end
  end

  @doc """
  Take one step. `:spine` is the application on the function spine.
  `:arg` is the λ application in that argument. `:other` is the first
  candidate off the spine, or the first candidate when the head has
  already stopped.
  """
  def act(term, :spine) do
    with {:ok, path} <- head_path(term), do: reduce(term, path)
  end

  def act(term, :arg) do
    with {:ok, path, {:app, {:lam, _, _, _, _}, arg}} <- head_app(term),
         {:ok, rel} <- head_path(arg) do
      reduce(term, path ++ [:arg | rel])
    else
      _ -> :error
    end
  end

  def act(term, :other) do
    head =
      case head_path(term),
        do: (
          {:ok, path} -> path
          :error -> nil
        )

    case Enum.find(candidates(term), &(&1 != head)) do
      nil -> :error
      path -> reduce(term, path)
    end
  end

  @doc """
  How many contractions from `action`, then `:spine`, until the
  head stops. Fuel `0` counts nothing.
  """
  def steps(term, action, fuel \\ 8) do
    Muro.Policies.Chain.rollout(term, action, &step/2, &stopped?/1, &cont/1, fuel)
  end

  @doc """
  `a1` reaches a stopped head in no more steps than `a2`.
  """
  def fewer?(term, a1, a2, fuel \\ 8) do
    Muro.Policies.Chain.fewer?(term, a1, a2, &step/2, &stopped?/1, &cont/1, fuel)
  end

  @doc """
  Substitutions until the head stops. `choose.(term)` is the action at
  that term. `{:fuel, n}` is a stop that did not arrive.
  """
  def follow(term, choose, fuel \\ 64) when is_function(choose, 1) do
    go(term, choose, fuel, 0)
  end

  @doc """
  The application on the function spine, with the path to it.
  """
  def head_app(term) do
    with {:ok, path} <- head_path(term),
         {:ok, {:app, _, _} = app} <- fetch(term, path) do
      {:ok, path, app}
    else
      _ -> :error
    end
  end

  defp go(term, choose, fuel, n) do
    cond do
      stopped?(term) ->
        {:ok, n}

      fuel == 0 ->
        {:fuel, n}

      true ->
        case act(term, choose.(term)) do
          {:ok, next} -> go(next, choose, fuel - 1, n + 1)
          :error -> {:stuck, n, choose.(term)}
        end
    end
  end

  defp cont(_term), do: :spine

  defp step(term, action) do
    {:ok, next} = act(term, action)
    next
  end

  defp walk({:app, f, a}, rev) do
    here = if match?({:lam, _, _, _, _}, f), do: [Enum.reverse(rev)], else: []
    here ++ walk(f, [:fun | rev]) ++ walk(a, [:arg | rev])
  end

  defp walk({:lam, _, _, _, body}, rev), do: walk(body, [:body | rev])
  defp walk(_, _), do: []

  defp spine({:app, {:lam, _, _, _, _}, _}, rev), do: {:ok, Enum.reverse(rev)}
  defp spine({:app, f, _}, rev), do: spine(f, [:fun | rev])
  defp spine(_, _), do: :error

  defp fetch(term, []), do: {:ok, term}
  defp fetch({:app, f, _}, [:fun | rest]), do: fetch(f, rest)
  defp fetch({:app, _, a}, [:arg | rest]), do: fetch(a, rest)
  defp fetch({:lam, _, _, _, body}, [:body | rest]), do: fetch(body, rest)
  defp fetch(_, _), do: :error

  defp put(_term, [], next), do: {:ok, next}

  defp put({:app, f, a}, [:fun | rest], next) do
    with {:ok, f1} <- put(f, rest, next), do: {:ok, {:app, f1, a}}
  end

  defp put({:app, f, a}, [:arg | rest], next) do
    with {:ok, a1} <- put(a, rest, next), do: {:ok, {:app, f, a1}}
  end

  defp put({:lam, q, ty, x, body}, [:body | rest], next) do
    with {:ok, body1} <- put(body, rest, next), do: {:ok, {:lam, q, ty, x, body1}}
  end

  defp put(_, _, _), do: :error
end

defmodule Muro.Meet do
  @moduledoc """
  The Elixir mirror of `decide` in `agda/Muro/Meet.agda`.

  A send meets a receive of the same payload type, and the
  continuations meet. The values need not be the same term. A variable
  is sent at the type of its innermost binding, and that is the type
  the other process receives. A choice meets the arm that was offered.
  Both ends close, or both abandon. `meets/2` is `:ok` when `decide`
  returns `yes`. Otherwise the pair where it returns `no`.
  """

  @doc """
  `:ok` when the two processes meet. Otherwise the pair where `decide` returns `no`.
  """
  def meets(p, q) do
    case go(p, q, %{}, %{}) do
      :ok ->
        :ok

      {:no, a, b} ->
        {:error, "#{Muro.Session.show_proc(a)} does not meet #{Muro.Session.show_proc(b)}"}
    end
  end

  # `done-done` and `stop-stop`.
  defp go(:done, :done, _lp, _rq), do: :ok
  defp go(:stop, :stop, _lp, _rq), do: :ok

  # `same-put`. The payload types agree. A `get` binds that type for its continuation.
  defp go({:put, ty, _, p}, {:get, ty, name, q}, lp, rq) do
    keep(go(p, q, lp, bind(rq, name, ty)))
  end

  # `same-get`.
  defp go({:get, ty, name, p}, {:put, ty, _, q}, lp, rq) do
    keep(go(p, q, bind(lp, name, ty), rq))
  end

  # A variable has no type of its own. `var-ok` reads the innermost binding,
  # and `same-put` compares that type with the receive.
  defp go({:put, :unknown, {:var, name} = val, p}, {:get, ty, gname, q}, lp, rq) do
    if bound?(lp, name, ty) do
      keep(go(p, q, lp, bind(rq, gname, ty)))
    else
      {:no, {:put, :unknown, val, p}, {:get, ty, gname, q}}
    end
  end

  # `same-get` for a variable on the right.
  defp go({:get, ty, gname, p}, {:put, :unknown, {:var, name} = val, q}, lp, rq) do
    if bound?(rq, name, ty) do
      keep(go(p, q, bind(lp, gname, ty), rq))
    else
      {:no, {:get, ty, gname, p}, {:put, :unknown, val, q}}
    end
  end

  # `pick0-cover`, `pick1-cover`, `cover-pick0`, `cover-pick1`.
  defp go({:pick0, p}, {:cover, q, _}, lp, rq), do: keep(go(p, q, lp, rq))
  defp go({:pick1, p}, {:cover, _, r}, lp, rq), do: keep(go(p, r, lp, rq))
  defp go({:cover, p, _}, {:pick0, r}, lp, rq), do: keep(go(p, r, lp, rq))
  defp go({:cover, _, q}, {:pick1, r}, lp, rq), do: keep(go(q, r, lp, rq))

  defp go(p, q, _lp, _rq), do: {:no, p, q}

  defp keep(:ok), do: :ok
  defp keep({:no, _, _} = no), do: no

  # `_` is an unnamed `get` and adds no binding. A later binding of the same name wins.
  defp bind(ctx, :_, _ty), do: ctx
  defp bind(ctx, name, ty), do: Map.put(ctx, name, ty)

  defp bound?(ctx, name, ty) do
    case Map.get(ctx, name) do
      ^ty -> true
      _ -> false
    end
  end
end

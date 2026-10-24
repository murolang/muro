defmodule Muro.Meet do
  @moduledoc """
  The Elixir mirror of `decide` in `agda/Muro/Meet.agda`.

  A send meets a receive of the same payload type, and the
  continuations meet. The values need not be the same term. A nat
  sent for a dependent receive instantiates vector lengths that name
  it on the receiver's side. A variable is sent at the type of its
  innermost binding, after a nat received on that side has instantiated
  the lengths in that type. That is the type the other process receives.
  An evidence payload meets as a nat. The evidence is in each
  conformance, not in the meeting, so this module has no case for it.
  A choice meets the arm that was offered.
  Both ends close, or both abandon. `meets/2` is `:ok` when `decide`
  returns `yes`. Otherwise the pair where it returns `no`.
  """

  @doc """
  `:ok` when the two processes meet. Otherwise the pair where `decide` returns `no`.
  """
  def meets(p, q) do
    case go(p, q, %{}, %{}, %{}, %{}) do
      :ok ->
        :ok

      {:no, a, b} ->
        {:error, "#{Muro.Session.show_proc(a)} does not meet #{Muro.Session.show_proc(b)}"}
    end
  end

  @doc false
  def go(p, q), do: go(p, q, %{}, %{}, %{}, %{})

  # `done-done` and `stop-stop`.
  defp go(:done, :done, _lp, _rq, _li, _ri), do: :ok
  defp go(:stop, :stop, _lp, _rq, _li, _ri), do: :ok

  # A variable has no type of its own. Its innermost binding is read
  # after this side's lengths are instantiated, and that type is
  # compared with the receive. `:unknown` is not a payload type, so
  # this clause stays ahead of the concrete one.
  defp go({:put, :unknown, {:var, name} = val, p}, {:get, gty, gname, q}, lp, rq, li, ri) do
    ty = apply_ty(ri, gty)

    if held(lp, li, name) == ty do
      keep(go(p, q, lp, bind(rq, gname, ty), li, ext(ri, gname, val, ty)))
    else
      {:no, {:put, :unknown, val, p}, {:get, gty, gname, q}}
    end
  end

  defp go({:get, gty, gname, p}, {:put, :unknown, {:var, name} = val, q}, lp, rq, li, ri) do
    ty = apply_ty(li, gty)

    if held(rq, ri, name) == ty do
      keep(go(p, q, bind(lp, gname, ty), rq, ext(li, gname, val, ty), ri))
    else
      {:no, {:get, gty, gname, p}, {:put, :unknown, val, q}}
    end
  end

  # The payload types agree after a received nat instantiates lengths.
  # A variable is the type of its innermost binding, as in `conforms`.
  # A `get` binds that type for its continuation.
  defp go({:put, ty, val, p}, {:get, gty, name, q}, lp, rq, li, ri) when ty != :unknown do
    left = apply_ty(li, ty)
    right = apply_ty(ri, gty)

    if left == right and inhabits?(val, left, li, lp) do
      keep(go(p, q, lp, bind(rq, name, right), li, ext(ri, name, val, right)))
    else
      {:no, {:put, ty, val, p}, {:get, gty, name, q}}
    end
  end

  defp go({:get, gty, name, p}, {:put, ty, val, q}, lp, rq, li, ri) when ty != :unknown do
    left = apply_ty(li, gty)
    right = apply_ty(ri, ty)

    if left == right and inhabits?(val, right, ri, rq) do
      keep(go(p, q, bind(lp, name, left), rq, ext(li, name, val, left), ri))
    else
      {:no, {:get, gty, name, p}, {:put, ty, val, q}}
    end
  end

  # `pick0-cover`, `pick1-cover`, `cover-pick0`, `cover-pick1`.
  defp go({:pick0, p}, {:cover, q, _}, lp, rq, li, ri), do: keep(go(p, q, lp, rq, li, ri))
  defp go({:pick1, p}, {:cover, _, r}, lp, rq, li, ri), do: keep(go(p, r, lp, rq, li, ri))
  defp go({:cover, p, _}, {:pick0, r}, lp, rq, li, ri), do: keep(go(p, r, lp, rq, li, ri))
  defp go({:cover, _, q}, {:pick1, r}, lp, rq, li, ri), do: keep(go(q, r, lp, rq, li, ri))

  defp go(p, q, _lp, _rq, _li, _ri), do: {:no, p, q}

  defp keep(:ok), do: :ok
  defp keep({:no, _, _} = no), do: no

  # `_` is an unnamed `get` and adds no binding. A later binding of the same name wins.
  defp bind(ctx, :_, _ty), do: ctx
  defp bind(ctx, name, ty), do: Map.put(ctx, name, ty)

  # The innermost binding, with this side's lengths instantiated.
  # An unbound name has no type.
  defp held(ctx, idx, name) do
    case Map.get(ctx, name) do
      nil -> nil
      stored -> apply_ty(idx, stored)
    end
  end

  # A literal inhabits the type written on the send. A name inhabits its
  # instantiated binding, and an unbound or mistyped name does not.
  defp inhabits?({:var, name}, ty, idx, ctx), do: held(ctx, idx, name) == ty
  defp inhabits?(_val, _ty, _idx, _ctx), do: true

  # A nat received under a name instantiates lengths on that side.
  # Another payload shadows the name. `_` binds nothing.
  defp ext(idx, :_, _val, _ty), do: idx

  defp ext(idx, name, val, :nat) do
    case nexp(val) do
      nil -> Map.delete(idx, name)
      e -> Map.put(idx, name, e)
    end
  end

  defp ext(idx, name, _val, _ty), do: Map.delete(idx, name)

  defp nexp({:nat, n}) when is_integer(n) and n >= 0, do: {:lit, n}
  defp nexp({:var, name}), do: {:var, name}
  defp nexp(_), do: nil

  defp apply_ty(_idx, ty) when ty in [:nat, :bit, :unit, :unknown], do: ty
  defp apply_ty(idx, {:pair, a, b}), do: {:pair, apply_ty(idx, a), apply_ty(idx, b)}

  defp apply_ty(idx, {:rec, fields}) when is_list(fields) do
    {:rec, Enum.map(fields, fn {name, ty} -> {name, apply_ty(idx, ty)} end)}
  end

  defp apply_ty(idx, {:vec, elem, e}), do: {:vec, apply_ty(idx, elem), apply_ix(idx, e)}

  defp apply_ix(_idx, {:lit, _} = e), do: e

  defp apply_ix(idx, {:var, name}) do
    case Map.get(idx, name) do
      nil -> {:var, name}
      e -> e
    end
  end
end

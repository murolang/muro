defmodule Muro.Meet do
  @moduledoc """
  The Elixir mirror of `decide` in `agda/Muro/Meet.agda`.

  A send meets a receive of the same payload type, and the
  continuations meet. The sent value inhabits that type. A constructor
  inhabits the declaration's type, or it does not. The values need not
  be the same term. A nat sent for a dependent receive instantiates
  vector lengths that name it on the receiver's side. A variable is sent
  at the type of its innermost binding, after a nat received on that
  side has instantiated the lengths in that type. That is the type the
  other process receives. An evidence payload meets as a nat. The
  evidence is in each conformance, not in the meeting, so this module
  has no case for it. A bit index meets the arm of that same bit. `b0`
  meets the first arm and `b1` meets the second. A variable bit selects
  neither. A choice meets the arm that was offered.
  Both ends close, or both abandon. A repeated head is the same pair
  of processes again, and that pair meets. `meets/2` is `:ok` when
  `decide` returns `yes`. Otherwise the pair where it returns `no`.
  """

  @doc """
  `:ok` when the two processes meet. Otherwise the pair where `decide` returns `no`.
  """
  def meets(p, q, book \\ []) do
    case go(p, q, book) do
      :ok ->
        :ok

      {:no, a, b} ->
        {:error, "#{Muro.Session.show_proc(a)} does not meet #{Muro.Session.show_proc(b)}"}

      {:error, msg} ->
        {:error, msg}
    end
  end

  @doc false
  def go(p, q), do: go(p, q, [])

  @meet_fuel 10_000

  @doc false
  def go(p, q, book) when is_list(book) do
    advance(p, q, %{}, %{}, %{}, %{}, %{}, %{}, MapSet.new(), @meet_fuel, book)
  end

  # The value indices stay inside one pass. They are not part of the
  # pair, so a nat bound in the loop does not have to be the same nat
  # on the next arrival at the head.
  defp advance(p, q, lp, rq, li, ri, penv, qenv, seen, fuel, book) do
    if fuel <= 0 do
      {:error, "out of fuel"}
    else
      with {:ok, p, penv} <- Muro.Session.unwind_proc(p, penv),
           {:ok, q, qenv} <- Muro.Session.unwind_proc(q, qenv),
           {:ok, pk} <- Muro.Session.project_proc(penv, p),
           {:ok, qk} <- Muro.Session.project_proc(qenv, q) do
        key = {p, pk, q, qk}

        if MapSet.member?(seen, key) do
          :ok
        else
          step(p, q, lp, rq, li, ri, penv, qenv, MapSet.put(seen, key), fuel, book)
        end
      end
    end
  end

  # `done-done` and `stop-stop`.
  defp step(:done, :done, _lp, _rq, _li, _ri, _penv, _qenv, _seen, _fuel, _book), do: :ok
  defp step(:stop, :stop, _lp, _rq, _li, _ri, _penv, _qenv, _seen, _fuel, _book), do: :ok

  # A variable has no type of its own. Its innermost binding is read
  # after this side's lengths are instantiated, and that type is
  # compared with the receive. An unbound name is a constructor when
  # the declaration says so. `:unknown` is not a payload type, so
  # this clause stays ahead of the concrete one.
  defp step(
         {:put, :unknown, val, p},
         {:get, gty, gname, q},
         lp,
         rq,
         li,
         ri,
         penv,
         qenv,
         seen,
         fuel,
         book
       ) do
    ty = apply_ty(ri, gty)

    if sends?(val, ty, lp, li, book) do
      keep(
        advance(
          p,
          q,
          lp,
          bind(rq, gname, ty),
          li,
          ext(ri, gname, val, ty),
          penv,
          qenv,
          seen,
          fuel - 1,
          book
        )
      )
    else
      {:no, {:put, :unknown, val, p}, {:get, gty, gname, q}}
    end
  end

  defp step(
         {:get, gty, gname, p},
         {:put, :unknown, val, q},
         lp,
         rq,
         li,
         ri,
         penv,
         qenv,
         seen,
         fuel,
         book
       ) do
    ty = apply_ty(li, gty)

    if sends?(val, ty, rq, ri, book) do
      keep(
        advance(
          p,
          q,
          bind(lp, gname, ty),
          rq,
          ext(li, gname, val, ty),
          ri,
          penv,
          qenv,
          seen,
          fuel - 1,
          book
        )
      )
    else
      {:no, {:get, gty, gname, p}, {:put, :unknown, val, q}}
    end
  end

  # The payload types agree after a received nat instantiates lengths.
  # A variable is the type of its innermost binding, as in `conforms`.
  # A `get` binds that type for its continuation.
  defp step(
         {:put, ty, val, p},
         {:get, gty, name, q},
         lp,
         rq,
         li,
         ri,
         penv,
         qenv,
         seen,
         fuel,
         book
       )
       when ty != :unknown do
    left = apply_ty(li, ty)
    right = apply_ty(ri, gty)

    if left == right and inhabits?(val, left, li, lp, book) do
      keep(
        advance(
          p,
          q,
          lp,
          bind(rq, name, right),
          li,
          ext(ri, name, val, right),
          penv,
          qenv,
          seen,
          fuel - 1,
          book
        )
      )
    else
      {:no, {:put, ty, val, p}, {:get, gty, name, q}}
    end
  end

  defp step(
         {:get, gty, name, p},
         {:put, ty, val, q},
         lp,
         rq,
         li,
         ri,
         penv,
         qenv,
         seen,
         fuel,
         book
       )
       when ty != :unknown do
    left = apply_ty(li, gty)
    right = apply_ty(ri, ty)

    if left == right and inhabits?(val, right, ri, rq, book) do
      keep(
        advance(
          p,
          q,
          bind(lp, name, left),
          rq,
          ext(li, name, val, left),
          ri,
          penv,
          qenv,
          seen,
          fuel - 1,
          book
        )
      )
    else
      {:no, {:get, gty, name, p}, {:put, ty, val, q}}
    end
  end

  # `iget-b0`, `iget-b1`, `b0-iget`, `b1-iget`. The literal selects the
  # arm. The bit is bound on the receiver and does not instantiate a length.
  defp step(
         {:iget, name, p, _q},
         {:put, :bit, :b0, r},
         lp,
         rq,
         li,
         ri,
         penv,
         qenv,
         seen,
         fuel,
         book
       ) do
    keep(
      advance(
        p,
        r,
        bind(lp, name, :bit),
        rq,
        ext(li, name, :b0, :bit),
        ri,
        penv,
        qenv,
        seen,
        fuel - 1,
        book
      )
    )
  end

  defp step(
         {:iget, name, _p, q},
         {:put, :bit, :b1, r},
         lp,
         rq,
         li,
         ri,
         penv,
         qenv,
         seen,
         fuel,
         book
       ) do
    keep(
      advance(
        q,
        r,
        bind(lp, name, :bit),
        rq,
        ext(li, name, :b1, :bit),
        ri,
        penv,
        qenv,
        seen,
        fuel - 1,
        book
      )
    )
  end

  defp step(
         {:put, :bit, :b0, p},
         {:iget, name, q, _r},
         lp,
         rq,
         li,
         ri,
         penv,
         qenv,
         seen,
         fuel,
         book
       ) do
    keep(
      advance(
        p,
        q,
        lp,
        bind(rq, name, :bit),
        li,
        ext(ri, name, :b0, :bit),
        penv,
        qenv,
        seen,
        fuel - 1,
        book
      )
    )
  end

  defp step(
         {:put, :bit, :b1, p},
         {:iget, name, _q, r},
         lp,
         rq,
         li,
         ri,
         penv,
         qenv,
         seen,
         fuel,
         book
       ) do
    keep(
      advance(
        p,
        r,
        lp,
        bind(rq, name, :bit),
        li,
        ext(ri, name, :b1, :bit),
        penv,
        qenv,
        seen,
        fuel - 1,
        book
      )
    )
  end

  # `pick0-cover`, `pick1-cover`, `cover-pick0`, `cover-pick1`.
  defp step({:pick0, p}, {:cover, q, _}, lp, rq, li, ri, penv, qenv, seen, fuel, book) do
    keep(advance(p, q, lp, rq, li, ri, penv, qenv, seen, fuel - 1, book))
  end

  defp step({:pick1, p}, {:cover, _, r}, lp, rq, li, ri, penv, qenv, seen, fuel, book) do
    keep(advance(p, r, lp, rq, li, ri, penv, qenv, seen, fuel - 1, book))
  end

  defp step({:cover, p, _}, {:pick0, r}, lp, rq, li, ri, penv, qenv, seen, fuel, book) do
    keep(advance(p, r, lp, rq, li, ri, penv, qenv, seen, fuel - 1, book))
  end

  defp step({:cover, _, q}, {:pick1, r}, lp, rq, li, ri, penv, qenv, seen, fuel, book) do
    keep(advance(q, r, lp, rq, li, ri, penv, qenv, seen, fuel - 1, book))
  end

  defp step(p, q, _lp, _rq, _li, _ri, _penv, _qenv, _seen, _fuel, _book), do: {:no, p, q}

  defp keep(:ok), do: :ok
  defp keep({:no, _, _} = no), do: no
  defp keep({:error, _} = err), do: err

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
  # A constructor inhabits the declaration's type, or it does not.
  defp sends?({:var, name} = val, ty, ctx, idx, book) do
    case held(ctx, idx, name) do
      nil -> Muro.Session.inhabits?(val, ty, %{}, book)
      got -> got == ty
    end
  end

  defp sends?(val, ty, ctx, idx, book), do: inhabits?(val, ty, idx, ctx, book)

  defp inhabits?({:var, name}, ty, idx, ctx, _book), do: held(ctx, idx, name) == ty

  defp inhabits?({:con, _, _} = val, ty, idx, ctx, book) do
    Muro.Session.inhabits?(val, ty, ground(ctx, idx), book)
  end

  defp inhabits?(_val, _ty, _idx, _ctx, _book), do: true

  defp ground(ctx, idx), do: Map.new(ctx, fn {name, ty} -> {name, apply_ty(idx, ty)} end)

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

  defp apply_ty(idx, {:dat, name, args}) do
    {:dat, name, Enum.map(args, &apply_ty(idx, &1))}
  end

  defp apply_ix(_idx, {:lit, _} = e), do: e

  defp apply_ix(idx, {:var, name}) do
    case Map.get(idx, name) do
      nil -> {:var, name}
      e -> e
    end
  end
end

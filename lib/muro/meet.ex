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
  @path_key {__MODULE__, :path}
  @proto_key {__MODULE__, :proto}
  @why_key {__MODULE__, :why}

  def meets(p, q, book \\ [], proto \\ nil) do
    Process.put(@path_key, [])
    Process.put(@proto_key, proto)
    Process.delete(@why_key)

    try do
      case go(p, q, book) do
        :ok ->
          :ok

        {:no, a, b} ->
          {:error, diverged(a, b)}

        {:error, msg} ->
          {:error, msg}
      end
    after
      Process.delete(@path_key)
      Process.delete(@proto_key)
      Process.delete(@why_key)
    end
  end

  defp diverged(a, b) do
    path = Process.get(@path_key, [])
    where = if path == [], do: "", else: " after " <> Enum.join(path, ", ")

    msg =
      "diverged#{where}: left: #{Muro.Session.step_proc(a)}; right: #{Muro.Session.step_proc(b)}"

    msg =
      case Process.get(@why_key) do
        nil -> msg
        reason -> msg <> ": #{reason}"
      end

    case Process.get(@proto_key) do
      proto when proto in [nil, :unset] -> msg
      proto -> msg <> "; protocol: #{Muro.Session.show_proto(proto)}"
    end
  end

  defp took(labels, proto_step) do
    Process.put(@path_key, Process.get(@path_key, []) ++ List.wrap(labels))
    Process.put(@proto_key, advance_proto(Process.get(@proto_key), proto_step))
  end

  defp why(nil), do: :ok
  defp why(reason) when is_binary(reason), do: Process.put(@why_key, reason)

  defp advance_proto(nil, _), do: nil
  defp advance_proto(proto, step), do: advance_head(proto, step)

  defp advance_head({:rec, _, body}, step), do: advance_head(body, step)
  defp advance_head({:send, _, s}, :put), do: s
  defp advance_head({:dsend, _, _, s}, :put), do: s
  defp advance_head({:esend, _, _, s}, :put), do: s
  defp advance_head({:isend, _, s, _}, {:put, :b0}), do: s
  defp advance_head({:isend, _, _, t}, {:put, :b1}), do: t
  defp advance_head({:recv, _, s}, :get), do: s
  defp advance_head({:drecv, _, _, s}, :get), do: s
  defp advance_head({:erecv, _, _, s}, :get), do: s
  defp advance_head({:irecv, _, s, _}, {:get, :b0}), do: s
  defp advance_head({:irecv, _, _, t}, {:get, :b1}), do: t
  defp advance_head({:choose, s, _}, :pick0), do: s
  defp advance_head({:choose, _, t}, :pick1), do: t
  defp advance_head({:branch, s, _}, :cover0), do: s
  defp advance_head({:branch, _, t}, :cover1), do: t
  defp advance_head(proto, _), do: proto

  @doc """
  `meets/2`, then the multiplicity. Affine abandonment stays.
  A linear endpoint that is not consumed once is refused.
  """
  def meet_mult(mult, p, q, book \\ []) when mult in [:aff, :lin] and is_list(book) do
    with :ok <- meets(p, q, book), do: Muro.Linear.meet_proc(mult, p, q)
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

  # A computed value meets the arm the match selects. The other
  # orientation is the same pair of premises.
  defp step(
         {:put, ty, val, cont},
         {:get, gty, gname, {:match, scrut, arms}} = getp,
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
    match_meet(
      {:put, ty, val, cont},
      getp,
      ty,
      val,
      cont,
      gty,
      gname,
      scrut,
      arms,
      lp,
      rq,
      li,
      ri,
      :put_first,
      penv,
      qenv,
      seen,
      fuel,
      book
    )
  end

  defp step(
         {:get, gty, gname, {:match, scrut, arms}} = getp,
         {:put, ty, val, cont},
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
    match_meet(
      getp,
      {:put, ty, val, cont},
      ty,
      val,
      cont,
      gty,
      gname,
      scrut,
      arms,
      rq,
      lp,
      ri,
      li,
      :get_first,
      penv,
      qenv,
      seen,
      fuel,
      book
    )
  end

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

    case sends?(val, ty, lp, li, book) do
      :yes ->
        took(put_label(val), :put)

        keep(
          advance(
            p,
            q,
            lp,
            bind(rq, gname, ty),
            li,
            ext(ri, gname, sent_of(val, lp, li, book), ty),
            penv,
            qenv,
            seen,
            fuel - 1,
            book
          )
        )

      :no ->
        why(Muro.Session.explain_put(val, ty, ground(lp, li), book))
        {:no, {:put, :unknown, val, p}, {:get, gty, gname, q}}

      {:error, _} = err ->
        err
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

    case sends?(val, ty, rq, ri, book) do
      :yes ->
        took(put_label(val), :get)

        keep(
          advance(
            p,
            q,
            bind(lp, gname, ty),
            rq,
            ext(li, gname, sent_of(val, rq, ri, book), ty),
            ri,
            penv,
            qenv,
            seen,
            fuel - 1,
            book
          )
        )

      :no ->
        why(Muro.Session.explain_put(val, ty, ground(rq, ri), book))
        {:no, {:get, gty, gname, p}, {:put, :unknown, val, q}}

      {:error, _} = err ->
        err
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

    case {left == right, inhabits?(val, left, li, lp, book)} do
      {true, :yes} ->
        took(put_label(val), :put)

        keep(
          advance(
            p,
            q,
            lp,
            bind(rq, name, right),
            li,
            ext(ri, name, sent_of(val, lp, li, book), right),
            penv,
            qenv,
            seen,
            fuel - 1,
            book
          )
        )

      {_, {:error, msg}} ->
        why(msg)
        {:no, {:put, ty, val, p}, {:get, gty, name, q}}

      _ ->
        why(Muro.Session.explain_put(val, left, ground(lp, li), book))
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

    case {left == right, inhabits?(val, right, ri, rq, book)} do
      {true, :yes} ->
        took(put_label(val), :get)

        keep(
          advance(
            p,
            q,
            bind(lp, name, left),
            rq,
            ext(li, name, sent_of(val, rq, ri, book), left),
            ri,
            penv,
            qenv,
            seen,
            fuel - 1,
            book
          )
        )

      {_, {:error, msg}} ->
        why(msg)
        {:no, {:get, gty, name, p}, {:put, ty, val, q}}

      _ ->
        why(Muro.Session.explain_put(val, right, ground(rq, ri), book))
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
    took(["get #{name}", "arm b0"], {:get, :b0})

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
    took(["get #{name}", "arm b1"], {:get, :b1})

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
    took(["get #{name}", "arm b0"], {:put, :b0})

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
    took(["get #{name}", "arm b1"], {:put, :b1})

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
    took("arm pick0", :pick0)
    keep(advance(p, q, lp, rq, li, ri, penv, qenv, seen, fuel - 1, book))
  end

  defp step({:pick1, p}, {:cover, _, r}, lp, rq, li, ri, penv, qenv, seen, fuel, book) do
    took("arm pick1", :pick1)
    keep(advance(p, r, lp, rq, li, ri, penv, qenv, seen, fuel - 1, book))
  end

  defp step({:cover, p, _}, {:pick0, r}, lp, rq, li, ri, penv, qenv, seen, fuel, book) do
    took("arm pick0", :cover0)
    keep(advance(p, r, lp, rq, li, ri, penv, qenv, seen, fuel - 1, book))
  end

  defp step({:cover, _, q}, {:pick1, r}, lp, rq, li, ri, penv, qenv, seen, fuel, book) do
    took("arm pick1", :cover1)
    keep(advance(q, r, lp, rq, li, ri, penv, qenv, seen, fuel - 1, book))
  end

  defp step(p, q, _lp, _rq, _li, _ri, _penv, _qenv, _seen, _fuel, _book), do: {:no, p, q}

  defp keep(:ok), do: :ok
  defp keep({:no, _, _} = no), do: no
  defp keep({:error, _} = err), do: err

  defp put_label(val), do: "put #{Muro.Session.show_value(val)}"

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
      nil -> Muro.Session.answer(val, ty, %{}, book)
      got -> if got == ty, do: :yes, else: :no
    end
  end

  defp sends?(val, ty, ctx, idx, book), do: inhabits?(val, ty, idx, ctx, book)

  defp inhabits?({:var, name}, ty, idx, ctx, _book) do
    if held(ctx, idx, name) == ty, do: :yes, else: :no
  end

  defp inhabits?({:con, _, _} = val, ty, idx, ctx, book) do
    Muro.Session.answer(val, ty, ground(ctx, idx), book)
  end

  defp inhabits?(_val, _ty, _idx, _ctx, _book), do: :yes

  defp sent_of(val, ctx, idx, book) do
    case Muro.Session.form(val, ground(ctx, idx), book) do
      {:ok, v} -> v
      _ -> val
    end
  end

  @cover "match does not cover the received value"

  # `orient` says which process is the put. The receiver's context is
  # extended with the value that was computed, and the selected arm is
  # the continuation that meets the sender's continuation.
  defp match_meet(
         left,
         right,
         ty,
         val,
         cont,
         gty,
         gname,
         scrut,
         arms,
         sctx,
         rctx,
         sidx,
         ridx,
         orient,
         penv,
         qenv,
         seen,
         fuel,
         book
       ) do
    if scrut != gname do
      {:error, @cover}
    else
      recv_ty = apply_ty(ridx, gty)
      send_ty = if ty == :unknown, do: recv_ty, else: apply_ty(sidx, ty)

      if send_ty != recv_ty do
        {:no, left, right}
      else
        case Muro.Session.form(val, ground(sctx, sidx), book) do
          {:error, msg} ->
            why(msg)
            {:no, left, right}

          {:ok, {:var, name}} ->
            why("the value #{name} does not select an arm")
            {:no, left, right}

          {:ok, :miss} ->
            {:no, left, right}

          {:ok, v} ->
            case Muro.Session.answer(v, send_ty, ground(sctx, sidx), book) do
              :yes ->
                case Muro.Session.arm(send_ty, v, arms, book) do
                  {:ok, arm} ->
                    took(["get #{gname}", "arm #{arm_name(v)}"], :get)

                    advance_arm(
                      orient,
                      cont,
                      arm,
                      gname,
                      v,
                      send_ty,
                      sctx,
                      rctx,
                      sidx,
                      ridx,
                      penv,
                      qenv,
                      seen,
                      fuel,
                      book
                    )

                  :error ->
                    why("the value #{Muro.Session.show_value(v)} does not select an arm")
                    {:no, left, right}
                end

              :no ->
                why(Muro.Session.explain_put(val, send_ty, ground(sctx, sidx), book))
                {:no, left, right}

              {:error, msg} ->
                why(msg)
                {:no, left, right}
            end
        end
      end
    end
  end

  defp arm_name(:b0), do: "b0"
  defp arm_name(:b1), do: "b1"
  defp arm_name({:con, name, _}), do: name
  defp arm_name(other), do: Muro.Session.show_value(other)

  defp advance_arm(
         :put_first,
         cont,
         arm,
         gname,
         val,
         ty,
         sctx,
         rctx,
         sidx,
         ridx,
         penv,
         qenv,
         seen,
         fuel,
         book
       ) do
    keep(
      advance(
        cont,
        arm,
        sctx,
        bind(rctx, gname, ty),
        sidx,
        ext(ridx, gname, val, ty),
        penv,
        qenv,
        seen,
        fuel - 1,
        book
      )
    )
  end

  defp advance_arm(
         :get_first,
         cont,
         arm,
         gname,
         val,
         ty,
         sctx,
         rctx,
         sidx,
         ridx,
         penv,
         qenv,
         seen,
         fuel,
         book
       ) do
    # The call site swapped the contexts so the sender is `sctx`, but
    # the processes were not swapped: the get is still the left process.
    keep(
      advance(
        arm,
        cont,
        bind(rctx, gname, ty),
        sctx,
        ext(ridx, gname, val, ty),
        sidx,
        penv,
        qenv,
        seen,
        fuel - 1,
        book
      )
    )
  end

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

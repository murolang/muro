defmodule Muro.Session do
  @moduledoc """
  The Elixir mirror of `decide` and `finishes` in `agda/Muro/Session.agda`.

  A communication carries a payload type and one continuation. The
  payload is a nat, a bit, unit, a pair, a record of named fields, or a
  vector whose length is a numeral or a nat received earlier. A pair is
  a tuple. A record is a fixed map: the names, in the order written,
  are the type. A vector is a list of that length. `put` sends a value
  of that type. `get` binds the received value to a named variable that
  can be used in the continuation. A dependent receive binds a name the
  continuation's payload may mention as a vector length. An evidence
  payload sends a nat at most a bound, a numeral or a nat bound
  earlier. The sender owes that evidence, and the checker decides it as
  `decide` does. The process puts the nat alone. `isend` and `irecv`
  send or receive a bit whose two arms are the index. `b0` takes the
  first arm and `b1` takes the second. The sender writes the literal.
  A variable bit does not select an arm. `iget` offers both arms and
  binds the bit. `choose` and `branch` select an arm by a label.
  `rec X. S` is that protocol again where `X` stands. The variable
  must sit under an action. `rec X. X` is not a protocol, and a name
  with no `rec` is not one. A process repeats the same way. A jump
  does not finish, so `%1` still refuses a loop. `stop` conforms to
  every protocol. `finishes/1` is `:yes` when every leaf is `done`.
  `skel/1` carries the value on `say` and the type on `hear`, and both
  arms of an indexed receive. A loop is one action and a jump is the
  name. `dual/1` swaps direction and keeps the payload type, the index,
  and the recursion variable.
  """

  @doc """
  The other end of a protocol. Mirrors `dual` in `agda/Muro/Dual.agda`.

  `send` swaps with `recv`. `choose` swaps with `branch`. The payload
  type stays. The continuation dualises. `rec` stays `rec` and a
  variable stays.
  """
  def dual(:end), do: :end
  def dual({:send, a, s}), do: {:recv, a, dual(s)}
  def dual({:recv, a, s}), do: {:send, a, dual(s)}
  def dual({:dsend, x, a, s}), do: {:drecv, x, a, dual(s)}
  def dual({:drecv, x, a, s}), do: {:dsend, x, a, dual(s)}
  def dual({:esend, x, e, s}), do: {:erecv, x, e, dual(s)}
  def dual({:erecv, x, e, s}), do: {:esend, x, e, dual(s)}
  def dual({:isend, x, s, t}), do: {:irecv, x, dual(s), dual(t)}
  def dual({:irecv, x, s, t}), do: {:isend, x, dual(s), dual(t)}
  def dual({:choose, s, t}), do: {:branch, dual(s), dual(t)}
  def dual({:branch, s, t}), do: {:choose, dual(s), dual(t)}
  def dual({:rec, x, s}), do: {:rec, x, dual(s)}
  def dual({:svar, x}), do: {:svar, x}

  @doc """
  The actions of a process. Mirrors `skel` in `agda/Muro/Session.agda`.

  `say` carries the value a peer receives. `hear` carries the type.
  """
  def skel(proc), do: skel_go(proc)

  defp skel_go(:done), do: :finish
  defp skel_go(:stop), do: :leave
  defp skel_go({:put, _ty, val, p}), do: {:say, runtime(val), skel_go(p)}
  defp skel_go({:get, ty, name, p}), do: {:hear, ty, name, skel_go(p)}
  defp skel_go({:pick0, p}), do: {:choose, :b0, skel_go(p)}
  defp skel_go({:pick1, p}), do: {:choose, :b1, skel_go(p)}
  defp skel_go({:cover, p, q}), do: {:offer, skel_go(p), skel_go(q)}
  defp skel_go({:iget, name, p, q}), do: {:index, name, skel_go(p), skel_go(q)}
  defp skel_go({:rec, name, body}), do: {:loop, name, skel_go(body)}
  defp skel_go({:call, name}), do: {:jump, name}

  @doc """
  The value as the OTP message carries it. A nat is an integer. A
  pair is a two-element tuple. A record is a map whose keys are the
  field names.
  """
  def runtime({:nat, n}) when is_integer(n) and n >= 0, do: n
  def runtime(bit) when bit in [:b0, :b1], do: bit
  def runtime(:tt), do: :tt
  def runtime({:var, name}), do: {:var, name}
  def runtime({:tup, a, b}), do: {runtime(a), runtime(b)}

  def runtime({:rec, fields}) when is_list(fields) do
    Map.new(fields, fn {name, val} -> {name, runtime(val)} end)
  end

  def runtime({:rep, {:nat, n}, val}) when is_integer(n) and n >= 0 do
    List.duplicate(runtime(val), n)
  end

  def runtime({:rep, {:var, name}, val}), do: {:rep, {:var, name}, runtime(val)}

  @doc """
  Whether a message value is of the payload type. A record matches by
  field name. The order of the names is the type, and it is compared
  with the protocol before this check.
  """
  def fits?(:nat, n) when is_integer(n) and n >= 0, do: true
  def fits?(:bit, bit) when bit in [:b0, :b1], do: true
  def fits?(:unit, :tt), do: true
  def fits?({:pair, a, b}, {x, y}), do: fits?(a, x) and fits?(b, y)

  def fits?({:rec, fields}, map) when is_list(fields) and is_map(map) do
    names = Enum.map(fields, fn {name, _} -> name end)

    Enum.sort(Map.keys(map)) == Enum.sort(names) and
      Enum.all?(fields, fn {name, ty} -> fits?(ty, Map.get(map, name)) end)
  end

  def fits?({:vec, elem, {:lit, n}}, list) when is_list(list) and is_integer(n) and n >= 0 do
    length(list) == n and Enum.all?(list, &fits?(elem, &1))
  end

  def fits?(_, _), do: false

  @doc """
  `:yes` when `finishes` returns `ends`. `stop` is `:no`.
  Mirrors `finishes` in `agda/Muro/Session.agda`.
  """
  def finishes(proc), do: finishes_go(proc)

  defp finishes_go(:done), do: :yes
  defp finishes_go(:stop), do: :no
  defp finishes_go({:put, _, _, p}), do: finishes_go(p)
  defp finishes_go({:get, _, _, p}), do: finishes_go(p)
  defp finishes_go({:pick0, p}), do: finishes_go(p)
  defp finishes_go({:pick1, p}), do: finishes_go(p)

  defp finishes_go({:cover, p, q}) do
    case finishes_go(p) do
      :yes -> finishes_go(q)
      :no -> :no
    end
  end

  defp finishes_go({:iget, _, p, q}) do
    case finishes_go(p) do
      :yes -> finishes_go(q)
      :no -> :no
    end
  end

  # A jump has no derivation. `rec X. done` does not jump.
  defp finishes_go({:rec, _, body}), do: finishes_go(body)
  defp finishes_go({:call, _}), do: :no

  @doc """
  `:ok` when `decide` returns `yes`. Otherwise the pair where it returns `no`.

  A repeated head is the same process and the same protocol again.
  That pair conforms. The value context is not part of the pair:
  one pass of a regular protocol is the whole check.
  """
  @conform_fuel 10_000

  def conforms(proc, proto) do
    case go(proc, proto, %{}, %{}, %{}, %{}, MapSet.new(), @conform_fuel) do
      :ok ->
        :ok

      {:no, p, s} ->
        {:error, "#{show_proc(p)} does not conform to #{show_proto(s)}"}

      {:error, msg} ->
        {:error, msg}
    end
  end

  @doc """
  `:ok` when every vector length is a numeral or a nat in scope.
  A dependent action extends that scope with its binder.
  """
  def proto_ok(proto), do: proto_ok(proto, %{})

  @doc """
  `:ok` when every recursion variable of a process sits under an action
  of its own `rec`. A free name is not a process.
  """
  def proc_ok(proc), do: proc_ok(proc, %{})

  # Leading `rec` and a jump unwind before the step. A cycle with no
  # action between is unguarded. Seeing the same head again conforms.
  defp go(proc, proto, ctx, idx, penv, senv, seen, fuel) do
    if fuel <= 0 do
      {:error, "out of fuel"}
    else
      with {:ok, proc, penv} <- unwind_proc(proc, penv),
           {:ok, proto, senv} <- unwind_proto(proto, senv),
           {:ok, pkey} <- project(penv, free_proc(proc)),
           {:ok, skey} <- project(senv, free_proto(proto)) do
        key = {proc, pkey, proto, skey}

        if MapSet.member?(seen, key) do
          :ok
        else
          step(proc, proto, ctx, idx, penv, senv, MapSet.put(seen, key), fuel)
        end
      end
    end
  end

  defp step(:done, :end, _ctx, _idx, _penv, _senv, _seen, _fuel), do: :ok
  defp step(:stop, _, _ctx, _idx, _penv, _senv, _seen, _fuel), do: :ok

  defp step({:put, ty, val, p} = proc, {:send, sty, s} = proto, ctx, idx, penv, senv, seen, fuel) do
    expected = apply_ty(idx, sty)

    if put_ok?(ty, val, expected, ctx) do
      keep(go(p, s, ctx, idx, penv, senv, seen, fuel - 1))
    else
      {:no, proc, proto}
    end
  end

  defp step(
         {:put, ty, val, p} = proc,
         {:dsend, y, sty, s} = proto,
         ctx,
         idx,
         penv,
         senv,
         seen,
         fuel
       ) do
    expected = apply_ty(idx, sty)

    if put_ok?(ty, val, expected, ctx) do
      keep(go(p, s, ctx, ext(idx, y, val, expected), penv, senv, seen, fuel - 1))
    else
      {:no, proc, proto}
    end
  end

  defp step({:get, ty, name, p} = proc, {:recv, sty, s} = proto, ctx, idx, penv, senv, seen, fuel) do
    expected = apply_ty(idx, sty)

    if ty == expected do
      keep(go(p, s, bind_ctx(ctx, name, expected), idx, penv, senv, seen, fuel - 1))
    else
      {:no, proc, proto}
    end
  end

  defp step(
         {:get, ty, name, p} = proc,
         {:drecv, y, sty, s} = proto,
         ctx,
         idx,
         penv,
         senv,
         seen,
         fuel
       ) do
    expected = apply_ty(idx, sty)

    if ty == expected do
      keep(
        go(
          p,
          s,
          bind_ctx(ctx, name, expected),
          rename_idx(idx, y, name),
          penv,
          senv,
          seen,
          fuel - 1
        )
      )
    else
      {:no, proc, proto}
    end
  end

  # `eput-ok`. The nat is a numeral or a name bound at Nat, and it owes
  # the bound the substitution resolves.
  defp step(
         {:put, ty, val, p} = proc,
         {:esend, _y, e, s} = proto,
         ctx,
         idx,
         penv,
         senv,
         seen,
         fuel
       ) do
    if put_ok?(ty, val, :nat, ctx) and owed?(val, resolve(idx, e), ctx) do
      keep(go(p, s, ctx, idx, penv, senv, seen, fuel - 1))
    else
      {:no, proc, proto}
    end
  end

  # `eget-ok`. The receiver binds a nat and owes nothing.
  defp step({:get, :nat, name, p}, {:erecv, _y, _e, s}, ctx, idx, penv, senv, seen, fuel) do
    keep(go(p, s, bind_ctx(ctx, name, :nat), idx, penv, senv, seen, fuel - 1))
  end

  # `iput0-ok` and `iput1-ok`. The literal selects the arm. A variable
  # bit does not. The name is shadowed so it does not instantiate a length.
  defp step(
         {:put, ty, val, p} = proc,
         {:isend, y, s, t} = proto,
         ctx,
         idx,
         penv,
         senv,
         seen,
         fuel
       ) do
    cond do
      val == :b0 and put_ok?(ty, val, :bit, ctx) ->
        keep(go(p, s, ctx, Map.delete(idx, y), penv, senv, seen, fuel - 1))

      val == :b1 and put_ok?(ty, val, :bit, ctx) ->
        keep(go(p, t, ctx, Map.delete(idx, y), penv, senv, seen, fuel - 1))

      true ->
        {:no, proc, proto}
    end
  end

  # `iget-ok`. Both arms are checked with the bit bound. It is not a length.
  defp step({:iget, name, p, q}, {:irecv, y, s, t}, ctx, idx, penv, senv, seen, fuel) do
    ctx1 = bind_ctx(ctx, name, :bit)
    idx1 = Map.delete(idx, y)

    case go(p, s, ctx1, idx1, penv, senv, seen, fuel - 1) do
      :ok -> keep(go(q, t, ctx1, idx1, penv, senv, seen, fuel - 1))
      no -> no
    end
  end

  defp step({:pick0, p}, {:choose, s, _}, ctx, idx, penv, senv, seen, fuel) do
    keep(go(p, s, ctx, idx, penv, senv, seen, fuel - 1))
  end

  defp step({:pick1, p}, {:choose, _, t}, ctx, idx, penv, senv, seen, fuel) do
    keep(go(p, t, ctx, idx, penv, senv, seen, fuel - 1))
  end

  defp step({:cover, p, q}, {:branch, s, t}, ctx, idx, penv, senv, seen, fuel) do
    case go(p, s, ctx, idx, penv, senv, seen, fuel - 1) do
      :ok -> keep(go(q, t, ctx, idx, penv, senv, seen, fuel - 1))
      no -> no
    end
  end

  defp step(p, s, _ctx, _idx, _penv, _senv, _seen, _fuel), do: {:no, p, s}

  # The binding is the `rec` term. A jump unfolds that term. The stack
  # is only the unwind, so a cycle here has no action under it.
  @doc false
  def unwind_proc(proc, env \\ %{}) do
    unwind_p(proc, env, MapSet.new())
  end

  defp unwind_p({:rec, name, body} = term, env, stack) do
    if MapSet.member?(stack, term) do
      {:error, "unguarded recursion"}
    else
      unwind_p(body, Map.put(env, name, term), MapSet.put(stack, term))
    end
  end

  defp unwind_p({:call, name}, env, stack) do
    case Map.get(env, name) do
      nil ->
        {:error, "free session variable #{name}"}

      term ->
        if MapSet.member?(stack, term) do
          {:error, "unguarded recursion"}
        else
          unwind_p(term, env, stack)
        end
    end
  end

  defp unwind_p(proc, env, _stack), do: {:ok, proc, env}

  defp unwind_proto(proto, env), do: unwind_s(proto, env, MapSet.new())

  defp unwind_s({:rec, name, body} = term, env, stack) do
    if MapSet.member?(stack, term) do
      {:error, "unguarded recursion"}
    else
      unwind_s(body, Map.put(env, name, term), MapSet.put(stack, term))
    end
  end

  defp unwind_s({:svar, name}, env, stack) do
    case Map.get(env, name) do
      nil ->
        {:error, "free session variable #{name}"}

      term ->
        if MapSet.member?(stack, term) do
          {:error, "unguarded recursion"}
        else
          unwind_s(term, env, stack)
        end
    end
  end

  defp unwind_s(proto, env, _stack), do: {:ok, proto, env}

  @doc false
  def project_proc(env, proc), do: project(env, free_proc(proc))

  defp project(env, names) do
    Enum.reduce_while(names, {:ok, %{}}, fn name, {:ok, acc} ->
      case Map.fetch(env, name) do
        {:ok, term} -> {:cont, {:ok, Map.put(acc, name, term)}}
        :error -> {:halt, {:error, "free session variable #{name}"}}
      end
    end)
  end

  defp free_proc(:done), do: MapSet.new()
  defp free_proc(:stop), do: MapSet.new()
  defp free_proc({:put, _, _, p}), do: free_proc(p)
  defp free_proc({:get, _, _, p}), do: free_proc(p)
  defp free_proc({:pick0, p}), do: free_proc(p)
  defp free_proc({:pick1, p}), do: free_proc(p)
  defp free_proc({:cover, p, q}), do: MapSet.union(free_proc(p), free_proc(q))
  defp free_proc({:iget, _, p, q}), do: MapSet.union(free_proc(p), free_proc(q))
  defp free_proc({:call, name}), do: MapSet.new([name])
  defp free_proc({:rec, name, body}), do: MapSet.delete(free_proc(body), name)

  defp free_proto(:end), do: MapSet.new()
  defp free_proto({:send, _, s}), do: free_proto(s)
  defp free_proto({:recv, _, s}), do: free_proto(s)
  defp free_proto({:dsend, _, _, s}), do: free_proto(s)
  defp free_proto({:drecv, _, _, s}), do: free_proto(s)
  defp free_proto({:esend, _, _, s}), do: free_proto(s)
  defp free_proto({:erecv, _, _, s}), do: free_proto(s)
  defp free_proto({:isend, _, s, t}), do: MapSet.union(free_proto(s), free_proto(t))
  defp free_proto({:irecv, _, s, t}), do: MapSet.union(free_proto(s), free_proto(t))
  defp free_proto({:choose, s, t}), do: MapSet.union(free_proto(s), free_proto(t))
  defp free_proto({:branch, s, t}), do: MapSet.union(free_proto(s), free_proto(t))
  defp free_proto({:svar, name}), do: MapSet.new([name])
  defp free_proto({:rec, name, body}), do: MapSet.delete(free_proto(body), name)

  defp put_ok?(:unknown, val, expected, ctx), do: value?(val, expected, ctx)
  defp put_ok?(ty, val, expected, ctx), do: ty == expected and value?(val, ty, ctx)

  # The count under `{:bound, name}` is how often the name was bound.
  # `Once` reads it.
  defp bind_ctx(ctx, :_, _ty), do: ctx

  defp bind_ctx(ctx, name, ty) do
    ctx
    |> Map.put(name, ty)
    |> Map.update({:bound, name}, 1, &(&1 + 1))
  end

  # `resolve`. A numeral is its own bound. A name is what the
  # substitution holds for it, and an unresolved name has no bound.
  defp resolve(_idx, {:lit, n}), do: {:lit, n}
  defp resolve(idx, {:var, name}), do: Map.get(idx, name)

  # `owed?` and `le?`. A numeral is at most a numeral by `≤`. Zero is
  # at most a name. A name is at most itself when it was bound once.
  defp owed?(_val, nil, _ctx), do: false
  defp owed?({:nat, m}, {:lit, n}, _ctx), do: m <= n
  defp owed?({:nat, 0}, {:var, _}, _ctx), do: true
  defp owed?({:var, x}, {:var, x}, ctx), do: Map.get(ctx, {:bound, x}) == 1
  defp owed?(_val, _e, _ctx), do: false

  # A nat instantiates the lengths that name it. Another payload
  # shadows the name and does not instantiate a length. `_` binds nothing.
  defp ext(idx, :_, _val, _ty), do: idx

  defp ext(idx, name, val, :nat) do
    case nexp_of(val) do
      nil -> Map.delete(idx, name)
      e -> Map.put(idx, name, e)
    end
  end

  defp ext(idx, name, _val, _ty), do: Map.delete(idx, name)

  # The protocol binder is the process binder in the continuation.
  defp rename_idx(idx, y, :_), do: Map.put(Map.delete(idx, y), y, {:var, :_})
  defp rename_idx(idx, y, name), do: Map.put(Map.delete(idx, y), y, {:var, name})

  defp nexp_of({:nat, n}) when is_integer(n) and n >= 0, do: {:lit, n}
  defp nexp_of({:var, name}), do: {:var, name}
  defp nexp_of(_), do: nil

  defp apply_ty(_idx, ty) when ty in [:nat, :bit, :unit, :unknown], do: ty
  defp apply_ty(idx, {:pair, a, b}), do: {:pair, apply_ty(idx, a), apply_ty(idx, b)}

  defp apply_ty(idx, {:rec, fields}) when is_list(fields) do
    {:rec, Enum.map(fields, fn {name, ty} -> {name, apply_ty(idx, ty)} end)}
  end

  defp apply_ty(idx, {:vec, elem, e}), do: {:vec, apply_ty(idx, elem), apply_nexp(idx, e)}

  defp apply_nexp(_idx, {:lit, _n} = e), do: e

  defp apply_nexp(idx, {:var, name}) do
    case Map.get(idx, name) do
      nil -> {:var, name}
      e -> e
    end
  end

  defp proto_ok(:end, _ctx), do: :ok
  defp proto_ok({:send, ty, s}, ctx), do: with_ty(ty_ok(ty, ctx), proto_ok(s, guard(ctx)))
  defp proto_ok({:recv, ty, s}, ctx), do: with_ty(ty_ok(ty, ctx), proto_ok(s, guard(ctx)))

  defp proto_ok({:dsend, name, ty, s}, ctx) do
    with_ty(ty_ok(ty, ctx), proto_ok(s, guard(Map.put(ctx, name, ty))))
  end

  defp proto_ok({:drecv, name, ty, s}, ctx) do
    with_ty(ty_ok(ty, ctx), proto_ok(s, guard(Map.put(ctx, name, ty))))
  end

  # The name of an evidence payload is in scope in its bound only.
  defp proto_ok({:esend, _name, e, s}, ctx),
    do: with_ty(bound_ok(e, ctx), proto_ok(s, guard(ctx)))

  defp proto_ok({:erecv, _name, e, s}, ctx),
    do: with_ty(bound_ok(e, ctx), proto_ok(s, guard(ctx)))

  defp proto_ok({:isend, name, s, t}, ctx) do
    ctx1 = guard(Map.put(ctx, name, :bit))
    with_ty(proto_ok(s, ctx1), proto_ok(t, ctx1))
  end

  defp proto_ok({:irecv, name, s, t}, ctx) do
    ctx1 = guard(Map.put(ctx, name, :bit))
    with_ty(proto_ok(s, ctx1), proto_ok(t, ctx1))
  end

  defp proto_ok({:choose, s, t}, ctx) do
    ctx1 = guard(ctx)
    with_ty(proto_ok(s, ctx1), proto_ok(t, ctx1))
  end

  defp proto_ok({:branch, s, t}, ctx) do
    ctx1 = guard(ctx)
    with_ty(proto_ok(s, ctx1), proto_ok(t, ctx1))
  end

  # `rec` binds the name unguarded. An action, not another `rec`, guards it.
  defp proto_ok({:rec, name, body}, ctx) do
    proto_ok(body, Map.put(ctx, {:sess, name}, :unguarded))
  end

  defp proto_ok({:svar, name}, ctx) do
    case Map.get(ctx, {:sess, name}) do
      :guarded -> :ok
      :unguarded -> {:error, "unguarded recursion"}
      nil -> {:error, "free session variable #{name}"}
    end
  end

  defp proto_ok(_, _ctx), do: {:error, "ill-formed protocol"}

  defp guard(ctx) do
    Map.new(ctx, fn
      {{:sess, name}, _} -> {{:sess, name}, :guarded}
      pair -> pair
    end)
  end

  defp proc_ok(:done, _ctx), do: :ok
  defp proc_ok(:stop, _ctx), do: :ok
  defp proc_ok({:put, _, _, p}, ctx), do: proc_ok(p, guard_proc(ctx))
  defp proc_ok({:get, _, _, p}, ctx), do: proc_ok(p, guard_proc(ctx))
  defp proc_ok({:pick0, p}, ctx), do: proc_ok(p, guard_proc(ctx))
  defp proc_ok({:pick1, p}, ctx), do: proc_ok(p, guard_proc(ctx))

  defp proc_ok({:cover, p, q}, ctx) do
    ctx1 = guard_proc(ctx)
    with_ty(proc_ok(p, ctx1), proc_ok(q, ctx1))
  end

  defp proc_ok({:iget, _, p, q}, ctx) do
    ctx1 = guard_proc(ctx)
    with_ty(proc_ok(p, ctx1), proc_ok(q, ctx1))
  end

  defp proc_ok({:rec, name, body}, ctx), do: proc_ok(body, Map.put(ctx, name, :unguarded))

  defp proc_ok({:call, name}, ctx) do
    case Map.get(ctx, name) do
      :guarded -> :ok
      :unguarded -> {:error, "unguarded recursion"}
      nil -> {:error, "free session variable #{name}"}
    end
  end

  defp proc_ok(_, _ctx), do: {:error, "ill-formed process"}

  defp guard_proc(ctx), do: Map.new(ctx, fn {name, _} -> {name, :guarded} end)

  defp with_ty(:ok, rest), do: rest
  defp with_ty({:error, _} = err, _rest), do: err

  defp bound_ok({:lit, n}, _ctx) when is_integer(n) and n >= 0, do: :ok

  defp bound_ok({:var, name}, ctx) do
    case Map.get(ctx, name) do
      nil -> {:error, "unbound bound name"}
      :nat -> :ok
      _ -> {:error, "bound is not a nat"}
    end
  end

  defp bound_ok(_, _ctx), do: {:error, "bound is not a nat"}

  defp ty_ok(ty, _ctx) when ty in [:nat, :bit, :unit], do: :ok
  defp ty_ok({:pair, a, b}, ctx), do: with_ty(ty_ok(a, ctx), ty_ok(b, ctx))

  defp ty_ok({:rec, fields}, ctx) when is_list(fields) do
    Enum.reduce_while(fields, :ok, fn {_name, ty}, :ok ->
      case ty_ok(ty, ctx) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
  end

  defp ty_ok({:vec, elem, {:lit, n}}, ctx) when is_integer(n) and n >= 0, do: ty_ok(elem, ctx)

  defp ty_ok({:vec, elem, {:var, name}}, ctx) do
    case Map.get(ctx, name) do
      nil -> {:error, "unbound length"}
      :nat -> ty_ok(elem, ctx)
      _ -> {:error, "vector length is not a nat"}
    end
  end

  defp ty_ok({:vec, _, _}, _ctx), do: {:error, "vector length is not a nat"}
  defp ty_ok(_, _ctx), do: {:error, "ill-formed payload"}

  defp keep(:ok), do: :ok
  defp keep({:no, _, _} = no), do: no
  defp keep({:error, _} = err), do: err

  defp value?({:nat, n}, :nat, _ctx) when is_integer(n) and n >= 0, do: true
  defp value?(bit, :bit, _ctx) when bit in [:b0, :b1], do: true
  defp value?(:tt, :unit, _ctx), do: true
  defp value?({:tup, a, b}, {:pair, ta, tb}, ctx), do: value?(a, ta, ctx) and value?(b, tb, ctx)

  defp value?({:rec, vals}, {:rec, fields}, ctx) when is_list(vals) and is_list(fields) do
    length(vals) == length(fields) and
      Enum.all?(fields, fn {name, ty} ->
        case List.keyfind(vals, name, 0) do
          {^name, val} -> value?(val, ty, ctx)
          _ -> false
        end
      end)
  end

  defp value?({:rep, ix, elem}, {:vec, ety, e}, ctx) do
    nexp_of(ix) == e and value?(elem, ety, ctx)
  end

  # Check that a variable has the expected type in the context
  defp value?({:var, name}, expected_ty, ctx) do
    case Map.get(ctx, name) do
      ^expected_ty -> true
      _ -> false
    end
  end

  defp value?(_, _, _ctx), do: false

  def show_proc(:done), do: "done"
  def show_proc(:stop), do: "stop"
  def show_proc({:put, _ty, val, p}), do: "put #{show_val(val)} #{paren_proc(p)}"
  def show_proc({:get, ty, :_, p}), do: "get #{show_pay_atom(ty)} #{paren_proc(p)}"
  def show_proc({:get, ty, name, p}), do: "get (#{name} : #{show_pay_atom(ty)}) #{paren_proc(p)}"
  def show_proc({:pick0, p}), do: "pick0 #{paren_proc(p)}"
  def show_proc({:pick1, p}), do: "pick1 #{paren_proc(p)}"
  def show_proc({:cover, p, q}), do: "cover #{paren_proc(p)} #{paren_proc(q)}"

  def show_proc({:iget, name, p, q}) do
    "get (#{name} : Bit) on #{paren_proc(p)} #{paren_proc(q)}"
  end

  def show_proc({:rec, name, body}), do: "rec #{name}. #{show_proc(body)}"
  def show_proc({:call, name}), do: "#{name}"

  defp show_val({:var, name}), do: "#{name}"
  defp show_val({:nat, n}), do: "#{n}"
  defp show_val(:b0), do: "b0"
  defp show_val(:b1), do: "b1"
  defp show_val(:tt), do: "tt"
  defp show_val({:tup, a, b}), do: "(#{show_val(a)}, #{show_val(b)})"
  defp show_val({:rep, ix, elem}), do: "rep #{show_val(ix)} #{show_val(elem)}"

  defp show_val({:rec, []}) do
    "{}"
  end

  defp show_val({:rec, fields}) when is_list(fields) do
    inner = Enum.map_join(fields, ", ", fn {name, val} -> "#{name} = #{show_val(val)}" end)
    "{#{inner}}"
  end

  def show_proto(:end), do: "end"
  def show_proto({:send, ty, s}), do: "send #{show_pay_atom(ty)} #{paren_proto(s)}"
  def show_proto({:recv, ty, s}), do: "recv #{show_pay_atom(ty)} #{paren_proto(s)}"

  def show_proto({:dsend, name, ty, s}) do
    "send (#{name} : #{show_pay(ty)}) #{paren_proto(s)}"
  end

  def show_proto({:drecv, name, ty, s}) do
    "recv (#{name} : #{show_pay(ty)}) #{paren_proto(s)}"
  end

  def show_proto({:esend, name, e, s}) do
    "send (#{name} : Nat) {#{name} ≤ #{show_ix(e)}} #{paren_proto(s)}"
  end

  def show_proto({:erecv, name, e, s}) do
    "recv (#{name} : Nat) {#{name} ≤ #{show_ix(e)}} #{paren_proto(s)}"
  end

  def show_proto({:isend, name, s, t}) do
    "send (#{name} : Bit) on #{paren_proto(s)} #{paren_proto(t)}"
  end

  def show_proto({:irecv, name, s, t}) do
    "recv (#{name} : Bit) on #{paren_proto(s)} #{paren_proto(t)}"
  end

  def show_proto({:choose, s, t}), do: "choose #{paren_proto(s)} #{paren_proto(t)}"
  def show_proto({:branch, s, t}), do: "branch #{paren_proto(s)} #{paren_proto(t)}"
  def show_proto({:rec, name, body}), do: "rec #{name}. #{show_proto(body)}"
  def show_proto({:svar, name}), do: "#{name}"

  defp show_pay(:nat), do: "Nat"
  defp show_pay(:bit), do: "Bit"
  defp show_pay(:unit), do: "Unit"
  defp show_pay({:pair, a, b}), do: "#{show_pay_atom(a)} * #{show_pay_atom(b)}"
  defp show_pay({:rec, []}), do: "{}"

  defp show_pay({:rec, fields}) do
    inner = Enum.map_join(fields, ", ", fn {name, ty} -> "#{name} : #{show_pay(ty)}" end)
    "{#{inner}}"
  end

  defp show_pay({:vec, elem, e}), do: "Vec #{show_pay_atom(elem)} #{show_ix(e)}"

  defp show_ix({:lit, n}), do: "#{n}"
  defp show_ix({:var, name}), do: "#{name}"

  defp show_pay_atom({:pair, _, _} = ty), do: "(#{show_pay(ty)})"
  defp show_pay_atom({:vec, _, _} = ty), do: "(#{show_pay(ty)})"
  defp show_pay_atom(ty), do: show_pay(ty)

  defp paren_proc(p) when is_atom(p), do: show_proc(p)
  defp paren_proc({:call, _} = p), do: show_proc(p)
  defp paren_proc(p), do: "(#{show_proc(p)})"

  defp paren_proto(:end), do: "end"
  defp paren_proto({:svar, _} = s), do: show_proto(s)
  defp paren_proto(s), do: "(#{show_proto(s)})"
end

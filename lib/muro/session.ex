defmodule Muro.Session do
  @moduledoc """
  The Elixir mirror of `decide` and `finishes` in `agda/Muro/Session.agda`.

  A communication carries a payload type and one continuation. The
  payload is a nat, a bit, unit, a pair, a record of named fields, a
  vector whose length is a numeral or a nat received earlier, or a
  non-indexed declared data type applied to payload arguments. The
  constructors are the ones that declaration has. A pair is a tuple. A
  record is a fixed map: the names, in the order written, are the type.
  A vector is a list of that length. `put` sends a value
  of that type: a literal, a name bound by `get`, or the value an
  in-scope `run` definition computes from its arguments. The body is a
  first-order term, and a definition may call only a definition declared
  before it. A definition that calls itself or a later definition is
  refused. `get` binds the received value to
  a named variable. `get (b : Bit) (match b P Q)` matches on that value.
  Each arm conforms to the one continuation, and the processes may differ:
  the received value chooses which process runs. A declared data type has
  one arm per constructor, in declaration order. A dependent receive binds a name the
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

  @doc """
  The skeleton an OTP image runs. `skel/1` leaves a constructor name as
  a variable. `carry/2` resolves an unbound constructor to the value the
  message carries: a nullary constructor is an atom, and a constructor
  with fields is a tagged tuple. A bound name stays a variable.
  """
  def carry(proc, book), do: carry_go(proc, prepare(book), %{})

  @doc false
  def inhabits?(val, ty, ctx, book) when is_map(ctx) and is_list(book) do
    answer(val, ty, ctx, prepare(book)) == :yes
  end

  @doc false
  def answer(val, ty, ctx, book) when is_list(book), do: answer(val, ty, ctx, prepare(book))

  def answer(val, ty, ctx, %{decls: _, runs: _} = book) do
    case reduce(val, ctx, book) do
      {:error, _} = err -> err
      {:ok, v} -> fits(v, ty, ctx, book)
    end
  end

  @doc false
  def form(val, ctx, book) when is_list(book), do: form(val, ctx, prepare(book))

  def form(val, ctx, %{decls: _, runs: _} = book) do
    case reduce(val, ctx, book) do
      {:ok, v} -> {:ok, canon(v, book)}
      other -> other
    end
  end

  @doc false
  def covered?(ty, arms, book) when is_list(book), do: covered?(ty, arms, prepare(book))
  def covered?(:bit, arms, _book) when length(arms) == 2, do: :ok

  def covered?({:dat, name, _}, arms, book) do
    names = ctor_names(book, name)
    if names != [] and length(names) == length(arms), do: :ok, else: :error
  end

  def covered?(_, _, _), do: :error

  @doc false
  def arm(ty, val, arms, book) when is_list(book), do: arm(ty, val, arms, prepare(book))

  def arm(ty, val, arms, book) do
    val = canon(val, book)

    case {ty, val, arms} do
      {:bit, :b0, [p, _]} ->
        {:ok, p}

      {:bit, :b1, [_, q]} ->
        {:ok, q}

      {{:dat, dname, _}, {:con, c, _}, _} ->
        case Enum.find_index(ctor_names(book, dname), &(&1 == cname(c))) do
          i when is_integer(i) ->
            case Enum.at(arms, i) do
              nil -> :error
              p -> {:ok, p}
            end

          _ ->
            :error
        end

      _ ->
        :error
    end
  end

  @doc """
  Constructor field templates for the declarations that are payloads.
  A nullary constructor's template is `[]`. `{:par, i}` is a parameter.
  `{:self, args}` is this declaration. `{:dat, name, args}` is another.
  """
  def payload_decls(book) when is_list(book) do
    book
    |> data_entries()
    |> Enum.flat_map(fn d ->
      case decl_templates(d) do
        {:ok, entry} -> [entry]
        :error -> []
      end
    end)
    |> Map.new()
  end

  defp skel_go(:done), do: :finish
  defp skel_go(:stop), do: :leave
  defp skel_go({:put, _ty, val, p}), do: {:say, runtime(val), skel_go(p)}
  defp skel_go({:get, ty, name, p}), do: {:hear, ty, name, skel_go(p)}
  defp skel_go({:pick0, p}), do: {:choose, :b0, skel_go(p)}
  defp skel_go({:pick1, p}), do: {:choose, :b1, skel_go(p)}
  defp skel_go({:cover, p, q}), do: {:offer, skel_go(p), skel_go(q)}
  defp skel_go({:iget, name, p, q}), do: {:index, name, skel_go(p), skel_go(q)}
  defp skel_go({:match, _name, arms}), do: {:pick, Enum.map(arms, &skel_go/1)}
  defp skel_go({:rec, name, body}), do: {:loop, name, skel_go(body)}
  defp skel_go({:call, name}), do: {:jump, name}

  defp carry_go(:done, _book, _ctx), do: :finish
  defp carry_go(:stop, _book, _ctx), do: :leave

  defp carry_go({:put, _ty, val, p}, book, ctx) do
    {:say, runtime(resolve_val(val, book, ctx)), carry_go(p, book, ctx)}
  end

  defp carry_go({:get, ty, name, p}, book, ctx) do
    {:hear, ty, name, carry_go(p, book, carry_bind(ctx, name))}
  end

  defp carry_go({:pick0, p}, book, ctx), do: {:choose, :b0, carry_go(p, book, ctx)}
  defp carry_go({:pick1, p}, book, ctx), do: {:choose, :b1, carry_go(p, book, ctx)}

  defp carry_go({:cover, p, q}, book, ctx) do
    {:offer, carry_go(p, book, ctx), carry_go(q, book, ctx)}
  end

  defp carry_go({:iget, name, p, q}, book, ctx) do
    ctx1 = carry_bind(ctx, name)
    {:index, name, carry_go(p, book, ctx1), carry_go(q, book, ctx1)}
  end

  defp carry_go({:match, _name, arms}, book, ctx) do
    {:pick, Enum.map(arms, &carry_go(&1, book, ctx))}
  end

  defp carry_go({:rec, name, body}, book, ctx), do: {:loop, name, carry_go(body, book, ctx)}
  defp carry_go({:call, name}, _book, _ctx), do: {:jump, name}

  defp carry_bind(ctx, :_), do: ctx
  defp carry_bind(ctx, name), do: Map.put(ctx, name, true)

  defp resolve_val({:var, name} = val, book, ctx) do
    cond do
      Map.has_key?(ctx, name) ->
        val

      nullary_name?(book, name) ->
        {:con, cname(name), []}

      run?(book, cname(name)) ->
        case eval_call(cname(name), [], book) do
          {:ok, v} when v != :miss -> v
          _ -> val
        end

      true ->
        val
    end
  end

  defp resolve_val({:con, name, args}, book, ctx) do
    args = Enum.map(args, &resolve_val(&1, book, ctx))

    if run?(book, name) and Enum.all?(args, &closed?(&1, ctx, book)) do
      case eval_call(name, args, book) do
        {:ok, v} when v != :miss -> v
        _ -> {:con, cname(name), args}
      end
    else
      {:con, cname(name), args}
    end
  end

  defp resolve_val({:tup, a, b}, book, ctx) do
    {:tup, resolve_val(a, book, ctx), resolve_val(b, book, ctx)}
  end

  defp resolve_val({:rec, fields}, book, ctx) when is_list(fields) do
    {:rec, Enum.map(fields, fn {name, val} -> {name, resolve_val(val, book, ctx)} end)}
  end

  defp resolve_val({:rep, ix, elem}, book, ctx) do
    {:rep, resolve_val(ix, book, ctx), resolve_val(elem, book, ctx)}
  end

  defp resolve_val(val, _book, _ctx), do: val

  @doc """
  The value as the OTP message carries it. A nat is an integer. A
  pair is a two-element tuple. A record is a map whose keys are the
  field names. A constructor with no fields is an atom. A constructor
  with fields is a tagged tuple.
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

  def runtime({:con, name, []}) when is_binary(name), do: String.to_atom(name)

  def runtime({:con, name, args}) when is_binary(name) and is_list(args) do
    List.to_tuple([String.to_atom(name) | Enum.map(args, &runtime/1)])
  end

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

  defp finishes_go({:match, _, arms}), do: finishes_all(arms)

  # A jump has no derivation. `rec X. done` does not jump.
  defp finishes_go({:rec, _, body}), do: finishes_go(body)
  defp finishes_go({:call, _}), do: :no

  defp finishes_all([]), do: :yes

  defp finishes_all([p | ps]) do
    case finishes_go(p) do
      :yes -> finishes_all(ps)
      :no -> :no
    end
  end

  @doc """
  `:ok` when `decide` returns `yes`. Otherwise the pair where it returns `no`.

  A repeated head is the same process and the same protocol again.
  That pair conforms. The value context is not part of the pair:
  one pass of a regular protocol is the whole check.
  """
  @conform_fuel 10_000

  def conforms(proc, proto, book \\ []) do
    case go(proc, proto, %{}, %{}, %{}, %{}, MapSet.new(), @conform_fuel, prepare(book)) do
      :ok ->
        :ok

      {:no, p, s} ->
        {:error, "#{show_proc(p)} does not conform to #{show_proto(s)}"}

      {:error, msg} ->
        {:error, msg}
    end
  end

  @doc """
  `:ok` when every payload is a nat, a bit, unit, a pair, a record, a
  vector whose length is in scope, or a non-indexed declared data type
  whose constructor fields are payloads, and every recursion variable
  sits under an action of its own `rec`. A dependent action extends
  that scope with its binder. A free name is not a protocol.
  """
  def proto_ok(proto, book \\ []), do: proto_at(proto, %{}, data_entries(book))

  @doc """
  `:ok` when every recursion variable of a process sits under an action
  of its own `rec`. A free name is not a process.
  """
  def proc_ok(proc), do: proc_ok(proc, %{})

  # Leading `rec` and a jump unwind before the step. A cycle with no
  # action between is unguarded. Seeing the same head again conforms.
  defp go(proc, proto, ctx, idx, penv, senv, seen, fuel, book) do
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
          step(proc, proto, ctx, idx, penv, senv, MapSet.put(seen, key), fuel, book)
        end
      end
    end
  end

  defp step(:done, :end, _ctx, _idx, _penv, _senv, _seen, _fuel, _book), do: :ok
  defp step(:stop, _, _ctx, _idx, _penv, _senv, _seen, _fuel, _book), do: :ok

  defp step(
         {:put, ty, val, p} = proc,
         {:send, sty, s} = proto,
         ctx,
         idx,
         penv,
         senv,
         seen,
         fuel,
         book
       ) do
    expected = apply_ty(idx, sty)

    case put_ok?(ty, val, expected, ctx, book) do
      :yes -> keep(go(p, s, ctx, idx, penv, senv, seen, fuel - 1, book))
      :no -> {:no, proc, proto}
      {:error, _} = err -> err
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
         fuel,
         book
       ) do
    expected = apply_ty(idx, sty)

    case put_ok?(ty, val, expected, ctx, book) do
      :yes ->
        keep(
          go(
            p,
            s,
            ctx,
            ext(idx, y, sent_val(val, ctx, book), expected),
            penv,
            senv,
            seen,
            fuel - 1,
            book
          )
        )

      :no ->
        {:no, proc, proto}

      {:error, _} = err ->
        err
    end
  end

  defp step(
         {:get, ty, name, p} = proc,
         {:recv, sty, s} = proto,
         ctx,
         idx,
         penv,
         senv,
         seen,
         fuel,
         book
       ) do
    expected = apply_ty(idx, sty)

    if ty == expected do
      keep(cont(p, s, name, expected, ctx, idx, penv, senv, seen, fuel, book))
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
         fuel,
         book
       ) do
    expected = apply_ty(idx, sty)

    if ty == expected do
      keep(
        cont(
          p,
          s,
          name,
          expected,
          ctx,
          rename_idx(idx, y, name),
          penv,
          senv,
          seen,
          fuel,
          book
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
         fuel,
         book
       ) do
    case put_ok?(ty, val, :nat, ctx, book) do
      :yes ->
        case reduce(val, ctx, book) do
          {:ok, got} ->
            if owed?(got, resolve(idx, e), ctx) do
              keep(go(p, s, ctx, idx, penv, senv, seen, fuel - 1, book))
            else
              {:no, proc, proto}
            end

          {:error, _} = err ->
            err
        end

      :no ->
        {:no, proc, proto}

      {:error, _} = err ->
        err
    end
  end

  # `eget-ok`. The receiver binds a nat and owes nothing.
  defp step({:get, :nat, name, p}, {:erecv, _y, _e, s}, ctx, idx, penv, senv, seen, fuel, book) do
    keep(cont(p, s, name, :nat, ctx, idx, penv, senv, seen, fuel, book))
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
         fuel,
         book
       ) do
    case put_ok?(ty, val, :bit, ctx, book) do
      :yes when val == :b0 ->
        keep(go(p, s, ctx, Map.delete(idx, y), penv, senv, seen, fuel - 1, book))

      :yes when val == :b1 ->
        keep(go(p, t, ctx, Map.delete(idx, y), penv, senv, seen, fuel - 1, book))

      :no ->
        {:no, proc, proto}

      :yes ->
        {:no, proc, proto}

      {:error, _} = err ->
        err
    end
  end

  # `iget-ok`. Both arms are checked with the bit bound. It is not a length.
  defp step({:iget, name, p, q}, {:irecv, y, s, t}, ctx, idx, penv, senv, seen, fuel, book) do
    ctx1 = bind_ctx(ctx, name, :bit)
    idx1 = Map.delete(idx, y)

    case go(p, s, ctx1, idx1, penv, senv, seen, fuel - 1, book) do
      :ok -> keep(go(q, t, ctx1, idx1, penv, senv, seen, fuel - 1, book))
      no -> no
    end
  end

  defp step({:pick0, p}, {:choose, s, _}, ctx, idx, penv, senv, seen, fuel, book) do
    keep(go(p, s, ctx, idx, penv, senv, seen, fuel - 1, book))
  end

  defp step({:pick1, p}, {:choose, _, t}, ctx, idx, penv, senv, seen, fuel, book) do
    keep(go(p, t, ctx, idx, penv, senv, seen, fuel - 1, book))
  end

  defp step({:cover, p, q}, {:branch, s, t}, ctx, idx, penv, senv, seen, fuel, book) do
    case go(p, s, ctx, idx, penv, senv, seen, fuel - 1, book) do
      :ok -> keep(go(q, t, ctx, idx, penv, senv, seen, fuel - 1, book))
      no -> no
    end
  end

  defp step(p, s, _ctx, _idx, _penv, _senv, _seen, _fuel, _book), do: {:no, p, s}

  # A match is the continuation of the `get` just taken. Each arm conforms
  # to that one protocol. The processes may differ: the received value
  # chooses which process runs, and it does not choose another protocol.
  # The scrutinee is the received name. A nat, a pair, a record, a vector,
  # or unit has no covering.
  @cover "match does not cover the received value"

  defp cont({:match, scrut, arms}, proto, name, ty, ctx, idx, penv, senv, seen, fuel, book) do
    cond do
      scrut != name ->
        {:error, @cover}

      covered?(ty, arms, book) != :ok ->
        {:error, @cover}

      true ->
        arms_go(arms, proto, bind_ctx(ctx, name, ty), idx, penv, senv, seen, fuel, book)
    end
  end

  defp cont(p, proto, name, ty, ctx, idx, penv, senv, seen, fuel, book) do
    go(p, proto, bind_ctx(ctx, name, ty), idx, penv, senv, seen, fuel - 1, book)
  end

  defp arms_go([], _proto, _ctx, _idx, _penv, _senv, _seen, _fuel, _book), do: :ok

  defp arms_go([p | ps], proto, ctx, idx, penv, senv, seen, fuel, book) do
    case go(p, proto, ctx, idx, penv, senv, seen, fuel - 1, book) do
      :ok -> arms_go(ps, proto, ctx, idx, penv, senv, seen, fuel, book)
      other -> other
    end
  end

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

  defp free_proc({:match, _, arms}),
    do: Enum.reduce(arms, MapSet.new(), &MapSet.union(free_proc(&1), &2))

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

  defp put_ok?(:unknown, val, expected, ctx, book), do: answer(val, expected, ctx, book)

  defp put_ok?(ty, val, expected, ctx, book) do
    if ty == expected, do: answer(val, expected, ctx, book), else: :no
  end

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

  defp apply_ty(idx, {:dat, name, args}) do
    {:dat, name, Enum.map(args, &apply_ty(idx, &1))}
  end

  defp apply_nexp(_idx, {:lit, _n} = e), do: e

  defp apply_nexp(idx, {:var, name}) do
    case Map.get(idx, name) do
      nil -> {:var, name}
      e -> e
    end
  end

  defp proto_at(:end, _ctx, _book), do: :ok

  defp proto_at({:send, ty, s}, ctx, book),
    do: with_ty(ty_ok(ty, ctx, book), proto_at(s, guard(ctx), book))

  defp proto_at({:recv, ty, s}, ctx, book),
    do: with_ty(ty_ok(ty, ctx, book), proto_at(s, guard(ctx), book))

  defp proto_at({:dsend, name, ty, s}, ctx, book) do
    with_ty(ty_ok(ty, ctx, book), proto_at(s, guard(Map.put(ctx, name, ty)), book))
  end

  defp proto_at({:drecv, name, ty, s}, ctx, book) do
    with_ty(ty_ok(ty, ctx, book), proto_at(s, guard(Map.put(ctx, name, ty)), book))
  end

  # The name of an evidence payload is in scope in its bound only.
  defp proto_at({:esend, _name, e, s}, ctx, book),
    do: with_ty(bound_ok(e, ctx), proto_at(s, guard(ctx), book))

  defp proto_at({:erecv, _name, e, s}, ctx, book),
    do: with_ty(bound_ok(e, ctx), proto_at(s, guard(ctx), book))

  defp proto_at({:isend, name, s, t}, ctx, book) do
    ctx1 = guard(Map.put(ctx, name, :bit))
    with_ty(proto_at(s, ctx1, book), proto_at(t, ctx1, book))
  end

  defp proto_at({:irecv, name, s, t}, ctx, book) do
    ctx1 = guard(Map.put(ctx, name, :bit))
    with_ty(proto_at(s, ctx1, book), proto_at(t, ctx1, book))
  end

  defp proto_at({:choose, s, t}, ctx, book) do
    ctx1 = guard(ctx)
    with_ty(proto_at(s, ctx1, book), proto_at(t, ctx1, book))
  end

  defp proto_at({:branch, s, t}, ctx, book) do
    ctx1 = guard(ctx)
    with_ty(proto_at(s, ctx1, book), proto_at(t, ctx1, book))
  end

  # `rec` binds the name unguarded. An action, not another `rec`, guards it.
  defp proto_at({:rec, name, body}, ctx, book) do
    proto_at(body, Map.put(ctx, {:sess, name}, :unguarded), book)
  end

  defp proto_at({:svar, name}, ctx, _book) do
    case Map.get(ctx, {:sess, name}) do
      :guarded -> :ok
      :unguarded -> {:error, "unguarded recursion"}
      nil -> {:error, "free session variable #{name}"}
    end
  end

  defp proto_at(_, _ctx, _book), do: {:error, "ill-formed protocol"}

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

  defp proc_ok({:match, _, arms}, ctx) do
    Enum.reduce_while(arms, :ok, fn p, :ok ->
      case proc_ok(p, ctx) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
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

  defp ty_ok(ty, ctx, book), do: ty_ok(ty, ctx, book, MapSet.new())

  defp ty_ok(ty, _ctx, _book, _seen) when ty in [:nat, :bit, :unit], do: :ok

  defp ty_ok({:pair, a, b}, ctx, book, seen) do
    with_ty(ty_ok(a, ctx, book, seen), ty_ok(b, ctx, book, seen))
  end

  defp ty_ok({:rec, fields}, ctx, book, seen) when is_list(fields) do
    Enum.reduce_while(fields, :ok, fn {_name, ty}, :ok ->
      case ty_ok(ty, ctx, book, seen) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
  end

  defp ty_ok({:vec, elem, {:lit, n}}, ctx, book, seen) when is_integer(n) and n >= 0 do
    ty_ok(elem, ctx, book, seen)
  end

  defp ty_ok({:vec, elem, {:var, name}}, ctx, book, seen) do
    case Map.get(ctx, name) do
      nil -> {:error, "unbound length"}
      :nat -> ty_ok(elem, ctx, book, seen)
      _ -> {:error, "vector length is not a nat"}
    end
  end

  defp ty_ok({:vec, _, _}, _ctx, _book, _seen), do: {:error, "vector length is not a nat"}

  # A declared data type. An inductive occurrence of the same application
  # is the declaration already being checked. An index, a parameter that
  # is not `Type`, or a field that is not a payload, is ill-formed.
  defp ty_ok({:dat, name, args}, ctx, book, seen), do: ty_dat(name, args, ctx, book, seen)

  defp ty_ok(_, _ctx, _book, _seen), do: {:error, "ill-formed payload"}

  defp keep(:ok), do: :ok
  defp keep({:no, _, _} = no), do: no
  defp keep({:error, _} = err), do: err

  defp fits({:nat, n}, :nat, _ctx, _book) when is_integer(n) and n >= 0, do: :yes
  defp fits(bit, :bit, _ctx, _book) when bit in [:b0, :b1], do: :yes
  defp fits(:tt, :unit, _ctx, _book), do: :yes

  defp fits({:tup, a, b}, {:pair, ta, tb}, ctx, book) do
    both(answer(a, ta, ctx, book), fn -> answer(b, tb, ctx, book) end)
  end

  defp fits({:rec, vals}, {:rec, fields}, ctx, book) when is_list(vals) and is_list(fields) do
    if length(vals) == length(fields) do
      Enum.reduce_while(fields, :yes, fn {name, ty}, :yes ->
        case List.keyfind(vals, name, 0) do
          {^name, val} ->
            case answer(val, ty, ctx, book) do
              :yes -> {:cont, :yes}
              other -> {:halt, other}
            end

          _ ->
            {:halt, :no}
        end
      end)
    else
      :no
    end
  end

  defp fits({:rep, ix, elem}, {:vec, ety, e}, ctx, book) do
    if nexp_of(ix) == e, do: answer(elem, ety, ctx, book), else: :no
  end

  defp fits({:con, name, args}, {:dat, _, _} = ty, ctx, book) do
    con_fits(name, args, ty, ctx, book)
  end

  # A bound name inhabits its binding. An unbound name inhabits a data
  # type when it is a nullary constructor of that type. The binding wins.
  defp fits({:var, name}, expected, ctx, book) do
    case Map.get(ctx, name) do
      ^expected -> :yes
      nil -> if nullary_ctor?(book, expected, name), do: :yes, else: :no
      _ -> :no
    end
  end

  defp fits(_, _, _ctx, _book), do: :no

  defp both(:yes, rest), do: rest.()
  defp both({:error, _} = err, _rest), do: err
  defp both(_, _rest), do: :no

  defp ty_dat(name, args, ctx, book, seen) do
    key = {name, args}

    cond do
      MapSet.member?(seen, key) ->
        :ok

      true ->
        case find_decl(book, name) do
          nil ->
            {:error, "ill-formed payload"}

          d ->
            case decl_templates(d) do
              {:ok, {_name, %{np: n, ctors: ctors}}} when n == length(args) ->
                seen = MapSet.put(seen, key)

                with :ok <- each_ty(args, ctx, book, seen) do
                  each_ctor(ctors, name, args, ctx, book, seen)
                end

              _ ->
                {:error, "ill-formed payload"}
            end
        end
    end
  end

  defp each_ty(args, ctx, book, seen) do
    Enum.reduce_while(args, :ok, fn ty, :ok ->
      case ty_ok(ty, ctx, book, seen) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
  end

  defp each_ctor(ctors, dname, args, ctx, book, seen) do
    Enum.reduce_while(ctors, :ok, fn {_cname, fields}, :ok ->
      case each_ty(Enum.map(fields, &inst_field(&1, dname, args)), ctx, book, seen) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
  end

  defp con_fits(name, args, {:dat, dname, targs}, ctx, book) do
    case find_decl(book, dname) do
      nil ->
        :no

      d ->
        case ctor_fields(d, cname(name)) do
          {:ok, fields} when length(fields) == length(args) ->
            Enum.reduce_while(Enum.zip(fields, args), :yes, fn {field, arg}, :yes ->
              case answer(arg, inst_field(field, dname, targs), ctx, book) do
                :yes -> {:cont, :yes}
                other -> {:halt, other}
              end
            end)

          _ ->
            :no
        end
    end
  end

  defp nullary_ctor?(book, {:dat, dname, _}, name) do
    case find_decl(book, dname) do
      nil -> false
      d -> ctor_fields(d, cname(name)) == {:ok, []}
    end
  end

  defp nullary_ctor?(_book, _ty, _name), do: false

  defp nullary_name?(book, name) do
    label = cname(name)
    Enum.any?(decls(book), fn d -> ctor_fields(d, label) == {:ok, []} end)
  end

  defp cname(name) when is_atom(name), do: Atom.to_string(name)
  defp cname(name) when is_binary(name), do: name

  defp find_decl(book, name) do
    Enum.find(decls(book), &(Map.get(&1, :kind) == :data and &1.name == name))
  end

  # De Bruijn data declarations. A named book is converted once.
  defp data_entries(book) do
    Enum.flat_map(book, fn
      %{kind: :data} = d ->
        case ensure_db(d) do
          {:ok, db} -> [db]
          _ -> []
        end

      _ ->
        []
    end)
  end

  defp ensure_db(d) do
    if named_decl?(d), do: Muro.Ast.data_to_db(d), else: {:ok, d}
  end

  defp named_decl?(%{params: params, ctors: ctors} = d) do
    indices = Map.get(d, :indices, [])

    Enum.any?(params ++ indices, fn {_q, _x, a} -> named_term?(a) end) or
      Enum.any?(ctors, fn %{type: ty} -> named_term?(ty) end)
  end

  defp named_term?({:var, v}) when is_binary(v), do: true
  defp named_term?({:var, v}) when is_integer(v), do: false
  defp named_term?({:mnat, _, _, _, _, _, _}), do: true
  defp named_term?({:mdata, _, _, _, _}), do: true
  defp named_term?({:munit, _, _, _, _}), do: true
  defp named_term?({:memp, _, _, _}), do: true
  defp named_term?({:letp, _, _, _, _}), do: true
  defp named_term?({:rwt, _, _, _, _}), do: true
  defp named_term?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&named_term?/1)
  defp named_term?(t) when is_list(t), do: Enum.any?(t, &named_term?/1)
  defp named_term?(_), do: false

  # A payload declaration has no indices, and every parameter is `Type`.
  # Each constructor field is a payload template.
  defp decl_templates(%{name: name, params: params, ctors: ctors} = d) do
    indices = Map.get(d, :indices, [])

    cond do
      indices != [] ->
        :error

      not Enum.all?(params, fn {_q, _x, a} -> a == :typ end) ->
        :error

      true ->
        order = Enum.map(ctors, & &1.name)

        Enum.reduce_while(ctors, {:ok, %{}}, fn c, {:ok, acc} ->
          case fields_of(d, c) do
            {:ok, fields} -> {:cont, {:ok, Map.put(acc, c.name, fields)}}
            :error -> {:halt, :error}
          end
        end)
        |> case do
          {:ok, ctors} -> {:ok, {name, %{np: length(params), order: order, ctors: ctors}}}
          :error -> :error
        end
    end
  end

  defp ctor_fields(d, name) do
    case decl_templates(d) do
      {:ok, {_n, %{ctors: ctors}}} ->
        case Map.fetch(ctors, name) do
          {:ok, fields} -> {:ok, fields}
          :error -> :error
        end

      :error ->
        :error
    end
  end

  # Drop the parameter binders. The remaining domains are the fields.
  # `0` after that drop is the last parameter. A field that mentions a
  # previous field, a function, or an erased argument is not a payload.
  defp fields_of(d, %{type: ty}) do
    n = length(d.params)

    case drop_params(ty, n) do
      {:ok, body} -> read_fields(body, d.name, n, 0)
      :error -> :error
    end
  end

  defp drop_params(ty, 0), do: {:ok, ty}
  defp drop_params({:pi, _q, _a, _x, b}, n) when n > 0, do: drop_params(b, n - 1)
  defp drop_params(_, _), do: :error

  defp read_fields({:pi, q, a, _x, b}, dname, n, depth) do
    if q == :erased do
      :error
    else
      with {:ok, field} <- field_template(a, dname, n, depth),
           {:ok, rest} <- read_fields(b, dname, n, depth + 1) do
        {:ok, [field | rest]}
      end
    end
  end

  defp read_fields(_result, _dname, _n, _depth), do: {:ok, []}

  defp field_template(:nat, _dname, _n, _depth), do: {:ok, :nat}
  defp field_template(:unit, _dname, _n, _depth), do: {:ok, :unit}
  defp field_template(:bit, _dname, _n, _depth), do: {:ok, :bit}

  defp field_template({:prod, a, b}, dname, n, depth) do
    with {:ok, ta} <- field_template(a, dname, n, depth),
         {:ok, tb} <- field_template(b, dname, n, depth) do
      {:ok, {:pair, ta, tb}}
    end
  end

  defp field_template({:var, i}, _dname, n, depth) when is_integer(i) do
    cond do
      i < depth ->
        :error

      true ->
        k = i - depth
        idx = n - 1 - k
        if idx >= 0 and idx < n, do: {:ok, {:par, idx}}, else: :error
    end
  end

  defp field_template({:pi, _, _, _, _}, _dname, _n, _depth), do: :error

  defp field_template(t, dname, n, depth) do
    case unspine(t, []) do
      {:ok, name, args} ->
        templates =
          Enum.reduce_while(args, {:ok, []}, fn a, {:ok, acc} ->
            case field_template(a, dname, n, depth) do
              {:ok, tmpl} -> {:cont, {:ok, acc ++ [tmpl]}}
              :error -> {:halt, :error}
            end
          end)

        case templates do
          {:ok, ts} when name == dname -> {:ok, {:self, ts}}
          {:ok, ts} -> {:ok, {:dat, name, ts}}
          :error -> :error
        end

      :error ->
        :error
    end
  end

  defp unspine({:app, f, a}, acc), do: unspine(f, [a | acc])
  defp unspine({:def, name}, acc), do: {:ok, name, acc}
  defp unspine(_, _), do: :error

  defp inst_field(:nat, _dname, _args), do: :nat
  defp inst_field(:bit, _dname, _args), do: :bit
  defp inst_field(:unit, _dname, _args), do: :unit
  defp inst_field({:par, i}, _dname, args), do: Enum.at(args, i)

  defp inst_field({:pair, a, b}, dname, args),
    do: {:pair, inst_field(a, dname, args), inst_field(b, dname, args)}

  defp inst_field({:self, ts}, dname, args),
    do: {:dat, dname, Enum.map(ts, &inst_field(&1, dname, args))}

  defp inst_field({:dat, name, ts}, dname, args),
    do: {:dat, name, Enum.map(ts, &inst_field(&1, dname, args))}

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

  def show_proc({:match, name, arms}) do
    "match #{name} #{Enum.map_join(arms, " ", &paren_proc/1)}"
  end

  def show_proc({:rec, name, body}), do: "rec #{name}. #{show_proc(body)}"
  def show_proc({:call, name}), do: "#{name}"

  defp show_val({:var, name}), do: "#{name}"
  defp show_val({:con, name, []}), do: "#{name}"

  defp show_val({:con, name, args}) do
    "(#{name} #{Enum.map_join(args, " ", &show_val/1)})"
  end

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
  defp show_pay({:dat, name, []}), do: name

  defp show_pay({:dat, name, args}) do
    "#{name} #{Enum.map_join(args, " ", &show_pay_atom/1)}"
  end

  defp show_ix({:lit, n}), do: "#{n}"
  defp show_ix({:var, name}), do: "#{name}"

  defp show_pay_atom({:pair, _, _} = ty), do: "(#{show_pay(ty)})"
  defp show_pay_atom({:vec, _, _} = ty), do: "(#{show_pay(ty)})"
  defp show_pay_atom({:dat, _, [_ | _]} = ty), do: "(#{show_pay(ty)})"
  defp show_pay_atom(ty), do: show_pay(ty)

  defp paren_proc(p) when is_atom(p), do: show_proc(p)
  defp paren_proc({:call, _} = p), do: show_proc(p)
  defp paren_proc(p), do: "(#{show_proc(p)})"

  defp paren_proto(:end), do: "end"
  defp paren_proto({:svar, _} = s), do: show_proto(s)
  defp paren_proto(s), do: "(#{show_proto(s)})"

  # The value a dependent send instantiates. A run application is the
  # nat it computes. A name stays a name.
  defp sent_val(val, ctx, book) do
    case reduce(val, ctx, book) do
      {:ok, v} when v != :miss -> v
      _ -> val
    end
  end

  # Data declarations for payload templates, and `run` definitions for
  # the first-order evaluator. A named book is converted once. A de Bruijn
  # book is kept: converting it again would rewrite `{:var, 0}`.
  defp prepare(book) when is_list(book) do
    %{decls: data_entries(book), runs: eval_book(book)}
  end

  defp decls(%{decls: decls}), do: decls
  defp decls(book) when is_list(book), do: book

  defp runs(%{runs: runs}), do: runs
  defp runs(_), do: []

  defp eval_book(book) do
    Enum.flat_map(book, fn d ->
      cond do
        Map.get(d, :kind) == :data ->
          case ensure_db(d) do
            {:ok, db} -> [db]
            _ -> []
          end

        run_entry?(d) ->
          case ensure_run(d) do
            {:ok, db} -> [db]
            _ -> []
          end

        true ->
          []
      end
    end)
  end

  defp run_entry?(%{mode: :run, name: _, body: _, type: _} = d), do: termish?(d)
  defp run_entry?(_), do: false

  defp termish?(%{kind: kind})
       when kind in [
              :data,
              :session,
              :conform,
              :place,
              :scheme,
              :move,
              :endpoint,
              :read,
              :meet,
              :talk,
              :seat,
              :link,
              :relay,
              :import,
              :param
            ],
       do: false

  defp termish?(_), do: true

  defp ensure_run(%{type: ty, body: body} = d) do
    if named_term?(ty) or named_term?(body), do: Muro.Ast.def_to_db(d), else: {:ok, d}
  end

  defp run?(book, name) do
    Enum.any?(runs(book), &(&1.name == name and &1.mode == :run))
  end

  defp ctor?(book, name) do
    label = cname(name)

    Enum.any?(decls(book), fn d ->
      match?({:ok, _}, ctor_fields(d, label))
    end)
  end

  defp ctor_names(book, dname) do
    case find_decl(book, dname) do
      %{ctors: ctors} -> Enum.map(ctors, & &1.name)
      _ -> []
    end
  end

  defp canon({:var, name} = val, book) do
    if nullary_name?(book, name), do: {:con, cname(name), []}, else: val
  end

  defp canon({:con, name, args}, book) do
    {:con, cname(name), Enum.map(args, &canon(&1, book))}
  end

  defp canon({:tup, a, b}, book), do: {:tup, canon(a, book), canon(b, book)}
  defp canon(val, _book), do: val

  # A run application is evaluated in the first-order fragment. A
  # definition may call only a definition declared before it.
  defp reduce({:con, name, args}, ctx, book) do
    with {:ok, args} <- reduce_list(args, ctx, book) do
      if run?(book, name) and Enum.all?(args, &closed?(&1, ctx, book)) do
        eval_call(name, args, book)
      else
        {:ok, {:con, cname(name), args}}
      end
    end
  end

  defp reduce({:tup, a, b}, ctx, book) do
    with {:ok, a} <- reduce(a, ctx, book),
         {:ok, b} <- reduce(b, ctx, book) do
      {:ok, {:tup, a, b}}
    end
  end

  defp reduce({:rec, fields}, ctx, book) when is_list(fields) do
    Enum.reduce_while(fields, {:ok, []}, fn {name, val}, {:ok, acc} ->
      case reduce(val, ctx, book) do
        {:ok, v} -> {:cont, {:ok, acc ++ [{name, v}]}}
        err -> {:halt, err}
      end
    end)
    |> case do
      {:ok, fields} -> {:ok, {:rec, fields}}
      err -> err
    end
  end

  defp reduce({:rep, ix, elem}, ctx, book) do
    with {:ok, ix} <- reduce(ix, ctx, book),
         {:ok, elem} <- reduce(elem, ctx, book) do
      {:ok, {:rep, ix, elem}}
    end
  end

  # A bare name is a nullary run when it is not bound and not a constructor.
  # The binding wins, and so does a constructor.
  defp reduce({:var, name} = val, ctx, book) do
    cond do
      Map.has_key?(ctx, name) or nullary_name?(book, name) ->
        {:ok, val}

      run?(book, cname(name)) ->
        eval_call(cname(name), [], book)

      true ->
        {:ok, val}
    end
  end

  defp reduce(val, _ctx, _book), do: {:ok, val}

  defp reduce_list(args, ctx, book) do
    Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, acc} ->
      case reduce(arg, ctx, book) do
        {:ok, v} -> {:cont, {:ok, acc ++ [v]}}
        err -> {:halt, err}
      end
    end)
  end

  defp closed?({:nat, n}, _ctx, _book) when is_integer(n) and n >= 0, do: true
  defp closed?(bit, _ctx, _book) when bit in [:b0, :b1], do: true
  defp closed?(:tt, _ctx, _book), do: true
  defp closed?({:tup, a, b}, ctx, book), do: closed?(a, ctx, book) and closed?(b, ctx, book)

  defp closed?({:rec, fields}, ctx, book) when is_list(fields) do
    Enum.all?(fields, fn {_name, val} -> closed?(val, ctx, book) end)
  end

  defp closed?({:rep, ix, elem}, ctx, book) do
    closed?(ix, ctx, book) and closed?(elem, ctx, book)
  end

  defp closed?({:con, name, args}, ctx, book) do
    ctor?(book, name) and Enum.all?(args, &closed?(&1, ctx, book))
  end

  defp closed?({:var, name}, ctx, book) do
    not Map.has_key?(ctx, name) and nullary_name?(book, name)
  end

  defp closed?(_, _, _), do: false

  defp eval_call(name, args, book) do
    defs = run_defs(book)
    args = Enum.map(args, &canon_arg(&1, book))

    case Enum.find_index(defs, &(&1.name == name)) do
      nil ->
        {:ok, :miss}

      i ->
        eval_def(Enum.at(defs, i), args, Enum.take(defs, i), defs, book)
    end
  end

  defp run_defs(book) do
    Enum.filter(runs(book), &(&1[:mode] == :run))
  end

  defp canon_arg({:var, name}, book) do
    if nullary_name?(book, name), do: {:con, cname(name), []}, else: {:var, name}
  end

  defp canon_arg({:con, name, args}, book) do
    {:con, cname(name), Enum.map(args, &canon_arg(&1, book))}
  end

  defp canon_arg({:tup, a, b}, book), do: {:tup, canon_arg(a, book), canon_arg(b, book)}
  defp canon_arg(val, _book), do: val

  defp eval_def(%{body: body}, args, prefix, defs, book) do
    case drop_lams(body, length(args)) do
      {:ok, core} ->
        if calls_out?(core, prefix, defs) do
          {:error, "recursive run definition"}
        else
          ev(core, Enum.reverse(args), prefix, defs, book)
        end

      :error ->
        {:ok, :miss}
    end
  end

  defp drop_lams(body, 0), do: {:ok, body}
  defp drop_lams({:lam, _, _, _, body}, n) when n > 0, do: drop_lams(body, n - 1)
  defp drop_lams(_, _), do: :error

  defp ev(:ze, _env, _prefix, _defs, _book), do: {:ok, {:nat, 0}}
  defp ev(:one, _env, _prefix, _defs, _book), do: {:ok, :tt}
  defp ev({:ann, t, _}, env, prefix, defs, book), do: ev(t, env, prefix, defs, book)

  defp ev({:su, t}, env, prefix, defs, book) do
    case ev(t, env, prefix, defs, book) do
      {:ok, {:nat, n}} -> {:ok, {:nat, n + 1}}
      {:ok, _} -> {:ok, :miss}
      other -> other
    end
  end

  defp ev({:pair, a, b}, env, prefix, defs, book) do
    with {:ok, a} <- ev(a, env, prefix, defs, book),
         {:ok, b} <- ev(b, env, prefix, defs, book) do
      if a == :miss or b == :miss, do: {:ok, :miss}, else: {:ok, {:tup, a, b}}
    end
  end

  defp ev({:var, i}, env, _prefix, _defs, _book) when is_integer(i) do
    case Enum.at(env, i) do
      nil -> {:ok, :miss}
      val -> {:ok, val}
    end
  end

  defp ev({:mnat, e, _motive, z, s}, env, prefix, defs, book) do
    case ev(e, env, prefix, defs, book) do
      {:ok, {:nat, 0}} ->
        ev(z, env, prefix, defs, book)

      {:ok, {:nat, n}} when n > 0 ->
        ev(s, [{:nat, n - 1} | env], prefix, defs, book)

      {:ok, _} ->
        {:ok, :miss}

      other ->
        other
    end
  end

  defp ev({:mdata, e, _motive, branches}, env, prefix, defs, book) do
    case ev(e, env, prefix, defs, book) do
      {:ok, val} ->
        case tagged(val) do
          {:con, name, fields} ->
            case find_branch(branches, name) do
              {_, arity, body} when length(fields) == arity ->
                ev(body, Enum.reverse(fields) ++ env, prefix, defs, book)

              _ ->
                {:ok, :miss}
            end

          _ ->
            {:ok, :miss}
        end

      other ->
        other
    end
  end

  defp ev({:app, _, _} = term, env, prefix, defs, book) do
    case spine_term(term, []) do
      {:ok, name, args} -> apply_head(name, args, env, prefix, defs, book)
      :error -> {:ok, :miss}
    end
  end

  defp ev({:def, name}, env, prefix, defs, book) do
    apply_head(name, [], env, prefix, defs, book)
  end

  defp ev(_, _, _, _, _), do: {:ok, :miss}

  defp tagged(:b0), do: {:con, "b0", []}
  defp tagged(:b1), do: {:con, "b1", []}
  defp tagged({:con, name, fields}), do: {:con, cname(name), fields}
  defp tagged(_), do: :no

  defp find_branch(branches, name) do
    Enum.find_value(branches, fn branch ->
      case branch_shape(branch) do
        {n, arity, body} -> if cname(n) == cname(name), do: {n, arity, body}
        _ -> nil
      end
    end)
  end

  defp branch_shape({name, binders, body}) when is_list(binders) do
    {name, length(binders), body}
  end

  defp branch_shape({name, arity, body}) when is_integer(arity), do: {name, arity, body}
  defp branch_shape(_), do: :no

  defp spine_term({:app, f, a}, acc), do: spine_term(f, [a | acc])
  defp spine_term({:def, name}, acc), do: {:ok, name, acc}
  defp spine_term(_, _), do: :error

  defp apply_head(name, args, env, prefix, defs, book) do
    with {:ok, vals} <- evs(args, env, prefix, defs, book) do
      if Enum.any?(vals, &(&1 == :miss)) do
        {:ok, :miss}
      else
        dispatch(name, vals, prefix, defs, book)
      end
    end
  end

  defp evs(ts, env, prefix, defs, book) do
    Enum.reduce_while(ts, {:ok, []}, fn t, {:ok, acc} ->
      case ev(t, env, prefix, defs, book) do
        {:ok, v} -> {:cont, {:ok, acc ++ [v]}}
        other -> {:halt, other}
      end
    end)
  end

  defp dispatch(name, vals, prefix, defs, book) do
    case Enum.find_index(prefix, &(&1.name == name)) do
      i when is_integer(i) ->
        eval_def(Enum.at(prefix, i), vals, Enum.take(prefix, i), defs, book)

      nil ->
        cond do
          Enum.any?(defs, &(&1.name == name)) ->
            {:error, "recursive run definition"}

          ctor?(book, name) ->
            {:ok, {:con, cname(name), vals}}

          true ->
            {:ok, :miss}
        end
    end
  end

  # The whole body, including an arm this argument does not take. A call
  # of this definition or of one declared later is a recursive run.
  defp calls_out?(term, prefix, defs) do
    case term do
      {:su, t} ->
        calls_out?(t, prefix, defs)

      {:ann, t, _} ->
        calls_out?(t, prefix, defs)

      {:pair, a, b} ->
        calls_out?(a, prefix, defs) or calls_out?(b, prefix, defs)

      {:mnat, e, _motive, z, s} ->
        calls_out?(e, prefix, defs) or calls_out?(z, prefix, defs) or
          calls_out?(s, prefix, defs)

      {:mnat, e, _x, _motive, z, _y, s} ->
        calls_out?(e, prefix, defs) or calls_out?(z, prefix, defs) or
          calls_out?(s, prefix, defs)

      {:mdata, e, motive, branches} when is_list(branches) ->
        calls_out?(e, prefix, defs) or calls_out?(motive, prefix, defs) or
          Enum.any?(branches, &branch_out?(&1, prefix, defs))

      {:mdata, e, _x, motive, branches} when is_list(branches) ->
        calls_out?(e, prefix, defs) or calls_out?(motive, prefix, defs) or
          Enum.any?(branches, &branch_out?(&1, prefix, defs))

      {:app, _, _} ->
        case spine_term(term, []) do
          {:ok, name, args} ->
            out_of_prefix?(name, prefix, defs) or
              Enum.any?(args, &calls_out?(&1, prefix, defs))

          :error ->
            false
        end

      {:def, name} ->
        out_of_prefix?(name, prefix, defs)

      _ ->
        false
    end
  end

  defp branch_out?(branch, prefix, defs) do
    case branch_shape(branch) do
      {_, _, body} -> calls_out?(body, prefix, defs)
      _ -> false
    end
  end

  defp out_of_prefix?(name, prefix, defs) do
    Enum.any?(defs, &(&1.name == name)) and not Enum.any?(prefix, &(&1.name == name))
  end
end

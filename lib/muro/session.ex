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
  the received value chooses which process runs. A received pair has one
  arm `| (a, b) =>`, and a received record has one arm naming every field
  in type order. A component is payload data, the same way a bound
  constructor field is. A `case` on that value
  gives each constructor its own continuation. A `case` on a `run` of
  the value gives each constructor the continuation of the run's result.
  A declared data type has
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
  must sit under an action. `rec X. X` is not a protocol. A name with
  no `rec` is a call of a session declared earlier. A call of the
  session itself sits under an action. A process repeats the same way. A jump
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
  type stays. The continuation dualises. A `case` stays a `case` and
  each arm dualises. `rec` stays `rec` and a variable stays.
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
  def dual({:sjump, target, args}), do: {:sjump, flip_jump(target), args}

  def dual({:case, scrut, arms}) do
    {:case, scrut, Enum.map(arms, fn {c, s} -> {c, dual(s)} end)}
  end

  defp flip_jump({:dual, name}), do: name
  defp flip_jump(name), do: {:dual, name}

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
    cond do
      # A run applied to a bound field is checked by the declared type.
      # The field is not known until the meeting. A constructor of the
      # value a `get` bound, such as `box n`, stays on the path below.
      match?({:con, _, _}, val) and run_apply(val, book) != nil and mentions_field?(val, ctx) ->
        typed_call(val, ty, ctx, book)

      # A bound field sent as itself is the value-binding check below.
      # A constructor of that field is not a value of the fragment.
      mentions_field?(val, ctx) and not match?({:var, _}, val) ->
        {:error, "outside the computed fragment"}

      true ->
        case reduce(val, ctx, book) do
          {:error, _} = err -> err
          {:ok, v} -> fits(v, ty, ctx, book)
        end
    end
  end

  # `call-ty`. The run is in scope and earlier than this check, its body
  # stays in the computed fragment, the codomain is the payload, and each
  # argument is a literal or a bound name of the parameter's type.
  defp typed_call({:con, name, args} = val, ty, ctx, book) do
    defs = run_defs(book)

    case Enum.find_index(defs, &(&1.name == cname(name))) do
      nil ->
        {:error, "outside the computed fragment"}

      i ->
        defn = Enum.at(defs, i)
        prefix = Enum.take(defs, i)
        {doms, cod} = pi_chain(defn.type, [])

        cond do
          length(doms) != length(args) ->
            {:error, "outside the computed fragment: partial application"}

          true ->
            case drop_lams(defn.body, length(args)) do
              :error ->
                {:error, "outside the computed fragment: partial application"}

              {:ok, core} ->
                cond do
                  calls_out?(core, prefix, defs) ->
                    {:error, run_cycle(cname(name), core)}

                  head = outside_fragment(core) ->
                    {:error, "outside the computed fragment: #{head}"}

                  true ->
                    case result_ty(cod, book) do
                      {:ok, ^ty} ->
                        args_typed(args, doms, ctx, book)

                      _ ->
                        {:error, inhabit(val, ty)}
                    end
                end
            end
        end
    end
  end

  defp args_typed([], [], _ctx, _book), do: :yes

  defp args_typed([arg | args], [dom | doms], ctx, book) do
    case result_ty(dom, book) do
      {:ok, expected} ->
        case decide_arg(arg, expected, ctx, book) do
          :ok -> args_typed(args, doms, ctx, book)
          {:error, _} = err -> err
        end

      :error ->
        {:error, "outside the computed fragment"}
    end
  end

  defp decide_arg({:var, name}, expected, ctx, book) do
    case Map.fetch(ctx, name) do
      {:ok, ^expected} ->
        :ok

      {:ok, _} ->
        {:error, inhabit({:var, name}, expected)}

      :error ->
        if literal_arg?({:var, name}, ctx, book) do
          literal_decided({:var, name}, expected, ctx, book)
        else
          if run?(book, cname(name)) do
            {:error, "argument is not a value"}
          else
            {:error, "unbound variable #{name}"}
          end
        end
    end
  end

  defp decide_arg(arg, expected, ctx, book) do
    if literal_arg?(arg, ctx, book) do
      literal_decided(arg, expected, ctx, book)
    else
      {:error, "argument is not a value"}
    end
  end

  defp literal_decided(arg, expected, ctx, book) do
    case answer(arg, expected, ctx, book) do
      :yes -> :ok
      :no -> {:error, inhabit(arg, expected)}
      {:error, msg} -> {:error, msg}
    end
  end

  defp literal_arg?({:nat, n}, _ctx, _book) when is_integer(n) and n >= 0, do: true
  defp literal_arg?(bit, _ctx, _book) when bit in [:b0, :b1, :tt], do: true

  defp literal_arg?({:tup, a, b}, ctx, book),
    do: literal_arg?(a, ctx, book) and literal_arg?(b, ctx, book)

  defp literal_arg?({:rec, fields}, ctx, book) when is_list(fields) do
    Enum.all?(fields, fn {_name, val} -> literal_arg?(val, ctx, book) end)
  end

  defp literal_arg?({:rep, ix, elem}, ctx, book) do
    literal_arg?(ix, ctx, book) and literal_arg?(elem, ctx, book)
  end

  defp literal_arg?({:con, name, args}, ctx, book) do
    not run?(book, name) and Enum.all?(args, &literal_arg?(&1, ctx, book))
  end

  defp literal_arg?({:var, name}, ctx, book) do
    not Map.has_key?(ctx, name) and nullary_name?(book, name)
  end

  defp literal_arg?(_, _, _), do: false

  # A field mark is the name a received constructor bound. A `get` clears it.
  defp mentions_field?({:var, name}, ctx), do: Map.get(ctx, {:field, name}) == true
  defp mentions_field?({:con, _, args}, ctx), do: Enum.any?(args, &mentions_field?(&1, ctx))
  defp mentions_field?({:tup, a, b}, ctx), do: mentions_field?(a, ctx) or mentions_field?(b, ctx)

  defp mentions_field?({:rec, fields}, ctx) when is_list(fields) do
    Enum.any?(fields, fn {_name, val} -> mentions_field?(val, ctx) end)
  end

  defp mentions_field?({:rep, ix, elem}, ctx) do
    mentions_field?(ix, ctx) or mentions_field?(elem, ctx)
  end

  defp mentions_field?(_, _), do: false

  defp inhabit(val, ty), do: "computed value #{show_val(val)} does not inhabit #{show_pay(ty)}"

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

  # One product arm. The field check is `product_cover`.
  def covered?({:pair, _, _}, [{:prod, {:pair, [x, y]}, _}], _book)
      when is_atom(x) and is_atom(y),
      do: :ok

  def covered?({:rec, fields}, [{:prod, {:rec, bs}, _}], _book)
      when is_list(fields) and is_list(bs),
      do: :ok

  def covered?(_, _, _), do: :error

  @doc false
  def arm(ty, val, arms, book) when is_list(book), do: arm(ty, val, arms, prepare(book))

  # A positional arm is that process. A named arm is that process after
  # the value's fields replace its binders. A bare arm is not arity-checked.
  # A product arm is that process after the tuple or the record replaces
  # its binders. The last binder wins.
  def arm(ty, val, arms, book) do
    val = canon(val, book)

    case {ty, val, arms} do
      {:bit, :b0, _} ->
        take_indexed(arms, 0, "b0", [], [], book)

      {:bit, :b1, _} ->
        take_indexed(arms, 1, "b1", [], [], book)

      {{:dat, dname, _} = dty, {:con, c, fields}, _} ->
        case Enum.find_index(ctor_names(book, dname), &(&1 == cname(c))) do
          i when is_integer(i) ->
            ftys =
              case fields_of_ctor(dty, cname(c), book) do
                {:ok, ts} -> ts
                :error -> []
              end

            take_indexed(arms, i, cname(c), fields, ftys, book)

          _ ->
            :error
        end

      {{:pair, _, _}, {:tup, a, b}, [{:prod, {:pair, [x, y]}, body}]}
      when is_atom(x) and is_atom(y) ->
        {:ok, subst_fields([x, y], [a, b], body)}

      {{:rec, fields}, {:rec, vals}, [{:prod, {:rec, bs}, body}]}
      when is_list(fields) and is_list(vals) and is_list(bs) ->
        fill_rec(fields, vals, bs, body)

      _ ->
        :error
    end
  end

  @doc false
  def arm_body({:arm, _, _, p}), do: p
  def arm_body({:prod, _, p}), do: p
  def arm_body(p), do: p

  @doc false
  def arm_binders({:arm, _, xs, _}) when is_list(xs), do: xs
  def arm_binders({:prod, pat, _}), do: pat_binders(pat)
  def arm_binders(_), do: []

  defp take_indexed(arms, i, expected, fields, ftys, book) do
    case Enum.at(arms, i) do
      nil -> :error
      arm -> take_arm(arm, expected, fields, ftys, book)
    end
  end

  # A match on a bound field follows the value of that field. The leaf
  # is the continuation. The other fields of this constructor stay in
  # the leaf, and so does the field that was cased on.
  defp take_arm({:arm, ctor, binders, {:match, name, inner}}, expected, fields, ftys, book)
       when is_binary(ctor) and is_list(binders) and is_list(fields) and is_list(inner) do
    cond do
      ctor != expected ->
        :error

      length(binders) != length(fields) ->
        :error

      name not in binders ->
        {:ok, subst_fields(binders, fields, {:match, name, inner})}

      true ->
        i = Enum.find_index(binders, &(&1 == name))

        case arm(Enum.at(ftys, i), Enum.at(fields, i), inner, book) do
          {:ok, leaf} -> {:ok, subst_fields(binders, fields, leaf)}
          :error -> :error
        end
    end
  end

  defp take_arm({:arm, ctor, binders, body}, expected, fields, _ftys, _book)
       when is_binary(ctor) and is_list(binders) and is_list(fields) do
    cond do
      ctor != expected -> :error
      length(binders) != length(fields) -> :error
      true -> {:ok, subst_fields(binders, fields, body)}
    end
  end

  defp take_arm({:prod, _, _}, _expected, _fields, _ftys, _book), do: :error
  defp take_arm(proc, _expected, _fields, _ftys, _book), do: {:ok, proc}

  # The record's fields, in type order. A missing key does not open the arm.
  defp fill_rec(fields, vals, bs, body) do
    case rec_fit(fields, bs) do
      :ok ->
        pairs =
          Enum.map(bs, fn {field, binder} ->
            case List.keyfind(vals, field, 0) do
              {_, val} -> {binder, val}
              nil -> nil
            end
          end)

        if Enum.any?(pairs, &is_nil/1) do
          :error
        else
          {:ok, subst_p(body, Map.new(pairs))}
        end

      _ ->
        :error
    end
  end

  defp pat_binders({:pair, names}) when is_list(names), do: names
  defp pat_binders({:rec, bs}) when is_list(bs), do: Enum.map(bs, fn {_, binder} -> binder end)
  defp pat_binders(_), do: []

  # Last binder wins, as with a nested `get`.
  defp subst_fields(binders, fields, body) do
    subst_p(body, Map.new(Enum.zip(binders, fields)))
  end

  defp subst_p({:put, ty, val, p}, env), do: {:put, ty, subst_v(val, env), subst_p(p, env)}

  defp subst_p({:get, ty, name, p}, env) do
    {:get, ty, name, subst_p(p, Map.delete(env, name))}
  end

  defp subst_p({:pick0, p}, env), do: {:pick0, subst_p(p, env)}
  defp subst_p({:pick1, p}, env), do: {:pick1, subst_p(p, env)}
  defp subst_p({:cover, p, q}, env), do: {:cover, subst_p(p, env), subst_p(q, env)}

  defp subst_p({:iget, name, p, q}, env) do
    env1 = Map.delete(env, name)
    {:iget, name, subst_p(p, env1), subst_p(q, env1)}
  end

  defp subst_p({:match, name, arms}, env) do
    env1 = Map.delete(env, name)
    {:match, name, Enum.map(arms, &subst_arm(&1, env1))}
  end

  defp subst_p({:rec, name, body}, env), do: {:rec, name, subst_p(body, env)}
  defp subst_p({:call, name}, _env), do: {:call, name}
  defp subst_p(:done, _env), do: :done
  defp subst_p(:stop, _env), do: :stop

  defp subst_arm({:arm, c, xs, p}, env) do
    env1 = Enum.reduce(xs, env, &Map.delete(&2, &1))
    {:arm, c, xs, subst_p(p, env1)}
  end

  defp subst_arm({:prod, pat, p}, env) do
    env1 = Enum.reduce(pat_binders(pat), env, &Map.delete(&2, &1))
    {:prod, pat, subst_p(p, env1)}
  end

  defp subst_arm(p, env), do: subst_p(p, env)

  defp subst_v({:var, name}, env) do
    case Map.fetch(env, name) do
      {:ok, val} -> val
      :error -> {:var, name}
    end
  end

  defp subst_v({:con, name, args}, env), do: {:con, name, Enum.map(args, &subst_v(&1, env))}
  defp subst_v({:tup, a, b}, env), do: {:tup, subst_v(a, env), subst_v(b, env)}

  defp subst_v({:rec, fields}, env) when is_list(fields) do
    {:rec, Enum.map(fields, fn {name, val} -> {name, subst_v(val, env)} end)}
  end

  defp subst_v({:rep, ix, elem}, env), do: {:rep, subst_v(ix, env), subst_v(elem, env)}
  defp subst_v(val, _env), do: val

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
  defp skel_go({:match, _name, arms}), do: {:pick, Enum.map(arms, &skel_arm/1)}
  defp skel_go({:rec, name, body}), do: {:loop, name, skel_go(body)}
  defp skel_go({:call, name}), do: {:jump, name}

  defp skel_arm({:arm, c, xs, {:match, name, inner}})
       when is_list(xs) and is_list(inner) do
    if name in xs do
      {:arm, c, xs, {:split, name, Enum.map(inner, &skel_arm/1)}}
    else
      {:arm, c, xs, {:pick, Enum.map(inner, &skel_arm/1)}}
    end
  end

  defp skel_arm({:arm, c, xs, p}), do: {:arm, c, xs, skel_go(p)}
  defp skel_arm({:prod, pat, p}), do: {:prod, pat, skel_go(p)}
  defp skel_arm(p), do: skel_go(p)

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
    {:pick, Enum.map(arms, &carry_arm(&1, book, ctx))}
  end

  defp carry_go({:rec, name, body}, book, ctx), do: {:loop, name, carry_go(body, book, ctx)}
  defp carry_go({:call, name}, _book, _ctx), do: {:jump, name}

  defp carry_arm({:arm, c, xs, {:match, name, inner}}, book, ctx)
       when is_list(xs) and is_list(inner) do
    ctx1 = Enum.reduce(xs, ctx, &carry_bind(&2, &1))

    body =
      if name in xs do
        {:split, name, Enum.map(inner, &carry_arm(&1, book, ctx1))}
      else
        {:pick, Enum.map(inner, &carry_arm(&1, book, ctx1))}
      end

    {:arm, c, xs, body}
  end

  defp carry_arm({:arm, c, xs, p}, book, ctx) do
    ctx1 = Enum.reduce(xs, ctx, &carry_bind(&2, &1))
    {:arm, c, xs, carry_go(p, book, ctx1)}
  end

  defp carry_arm({:prod, pat, p}, book, ctx) do
    ctx1 = Enum.reduce(pat_binders(pat), ctx, &carry_bind(&2, &1))
    {:prod, pat, carry_go(p, book, ctx1)}
  end

  defp carry_arm(p, book, ctx), do: carry_go(p, book, ctx)

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

    cond do
      run?(book, name) and Enum.all?(args, &closed?(&1, ctx, book)) ->
        case eval_call(name, args, book) do
          {:ok, v} when v != :miss -> v
          _ -> {:con, cname(name), args}
        end

      # An open field stays a variable. The server binds it on receive.
      run?(book, name) and Enum.any?(args, &has_var?/1) ->
        {:run, cname(name), args}

      true ->
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

  defp has_var?({:var, _}), do: true
  defp has_var?({:run, _, _}), do: true
  defp has_var?({:con, _, args}), do: Enum.any?(args, &has_var?/1)
  defp has_var?({:tup, a, b}), do: has_var?(a) or has_var?(b)

  defp has_var?({:rec, fields}) when is_list(fields) do
    Enum.any?(fields, fn {_name, val} -> has_var?(val) end)
  end

  defp has_var?({:rep, ix, elem}), do: has_var?(ix) or has_var?(elem)
  defp has_var?(_), do: false

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

  def runtime({:run, name, args}) when is_binary(name) and is_list(args) do
    {:run, name, Enum.map(args, &runtime/1)}
  end

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
    case finishes_go(arm_body(p)) do
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
  @span_key {__MODULE__, :span}
  @pspans_key {__MODULE__, :pspans}
  @run_key {__MODULE__, :run}

  def conforms(proc, proto, book \\ []) do
    case conform_at(proc, proto, book, nil) do
      :ok -> :ok
      {:error, _at, msg} -> {:error, msg}
    end
  end

  @doc false
  def conform_at(proc, proto, book, steps) do
    Process.put(@span_key, steps)
    Process.put(@pspans_key, %{})

    try do
      case go(proc, proto, %{}, %{}, %{}, %{}, MapSet.new(), @conform_fuel, prepare(book)) do
        :ok ->
          :ok

        {:no, p, s} ->
          {:error, nil, blame(p, s, nil)}

        {:no, p, s, reason, at} ->
          {:error, at, blame(p, s, reason)}

        {:error, msg} ->
          {:error, nil, msg}

        {:error, at, msg} ->
          {:error, at, msg}
      end
    after
      Process.delete(@span_key)
      Process.delete(@pspans_key)
    end
  end

  defp blame(p, s, nil), do: "#{show_proc(p)} does not conform to #{show_proto(s)}"
  defp blame(p, s, reason), do: "#{show_proc(p)} does not conform to #{show_proto(s)}: #{reason}"

  @doc """
  `:ok` when every payload is a nat, a bit, unit, a pair, a record, a
  vector whose length is in scope, or a non-indexed declared data type
  whose constructor fields are payloads, and every recursion variable
  sits under an action of its own `rec`. A dependent action extends
  that scope with its binder. A free name is not a protocol.
  """
  def proto_ok(proto, book \\ []) do
    proto_at(proto, %{{:__book__, :book} => book}, data_entries(book))
  end

  @doc """
  The declaration is well formed. A call of an earlier session checks
  its arguments. A call of this session must sit under an action.
  A later session, an unknown name, and the wrong number of arguments
  are refused here, before a meeting.
  """
  def decl_ok(session, book) when is_list(book) do
    params = Map.get(session, :params, [])

    ctx =
      params
      |> Map.new(&{&1, :nat})
      |> Map.put({:self, session.name}, :unguarded)
      |> Map.put({:__book__, :book}, book)
      |> Map.put({:__self__, :index}, session_index(book, session.name))

    case session.proto do
      {:dual, _} -> :ok
      {:seen, _, _, _} -> :ok
      proto -> proto_at(proto, ctx, data_entries(book))
    end
  end

  @doc """
  Open a nullary session body. Earlier calls are inlined. A guarded
  self-call is a jump that carries the next arguments.
  """
  def elaborate(session, book) when is_list(book) do
    elab(session.proto, elab_state(session.name, session_index(book, session.name), book, %{}))
  end

  @doc """
  Open `name` applied to `args`. The arguments are evaluated before the
  body is opened. The result is that session with a concrete protocol.
  """
  def open_applied(book, name, args) when is_list(book) and is_list(args) do
    case locate_session(book, name) do
      nil ->
        {:error, "unknown session #{name}"}

      {i, sess} ->
        st = elab_state(nil, nil, book, %{})

        with {:ok, exps} <- eval_arg_list(args, st),
             :ok <- arity_ok(sess, exps) do
          subst = Map.new(Enum.zip(Map.get(sess, :params, []), exps))

          case elab(sess.proto, %{elab_state(name, i, book, subst) | guarded: false}) do
            {:ok, proto} -> {:ok, %{sess | proto: proto, params: []}}
            {:error, _} = err -> err
          end
        end
    end
  end

  @doc """
  `:ok` when every recursion variable of a process sits under an action
  of its own `rec`. A free name is not a process.
  """
  def proc_ok(proc), do: proc_ok(proc, %{})

  # Leading `rec` and a jump unwind before the step. Opening a jump may
  # return another `rec`, so the head is exposed again. A cycle with no
  # action between is unguarded. Seeing the same head again conforms.
  defp go(proc, proto, ctx, idx, penv, senv, seen, fuel, book) do
    if fuel <= 0 do
      {:error, "out of fuel"}
    else
      span0 = Process.get(@span_key)
      pspans0 = Process.get(@pspans_key) || %{}
      orig = proc

      with {:ok, proc, proto, penv, senv} <- open_head(orig, proto, penv, senv, book) do
        {span, pspans} = placed(orig, span0, pspans0)
        Process.put(@span_key, span)
        Process.put(@pspans_key, pspans)

        try do
          with {:ok, pkey} <- project(penv, free_proc(proc)),
               {:ok, skey} <- project(senv, free_proto(proto)) do
            key = {proc, pkey, proto, skey}

            cond do
              MapSet.member?(seen, key) -> :ok
              absorb_loop?(seen, proc, pkey, proto) -> :ok
              true -> step(proc, proto, ctx, idx, penv, senv, MapSet.put(seen, key), fuel, book)
            end
          end
        after
          Process.put(@span_key, span0)
          Process.put(@pspans_key, pspans0)
        end
      end
    end
  end

  # The span of the head `unwind_proc` exposes. A cycle here is the
  # unguarded recursion `unwind_proc` already refused, so a miss is no location.
  defp placed(proc, span, pspans) do
    case place_span(proc, span, pspans, MapSet.new()) do
      {:ok, span, pspans} -> {span, pspans}
      _ -> {nil, pspans}
    end
  end

  defp place_span({:rec, name, body} = term, span, pspans, stack) do
    if MapSet.member?(stack, term) do
      :error
    else
      place_span(
        body,
        step_down(span, 0),
        Map.put(pspans, name, {span, body}),
        MapSet.put(stack, term)
      )
    end
  end

  defp place_span({:call, name}, _span, pspans, stack) do
    case Map.get(pspans, name) do
      {rec_span, body} ->
        term = {:rec, name, body}

        if MapSet.member?(stack, term) do
          :error
        else
          place_span(body, step_down(rec_span, 0), pspans, MapSet.put(stack, term))
        end

      _ ->
        {:ok, nil, pspans}
    end
  end

  defp place_span(_proc, span, pspans, _stack), do: {:ok, span, pspans}

  defp descend(p, proto, ctx, idx, penv, senv, seen, fuel, book, span) do
    span0 = Process.get(@span_key)
    pspans0 = Process.get(@pspans_key)
    Process.put(@span_key, span)

    try do
      go(p, proto, ctx, idx, penv, senv, seen, fuel, book)
    after
      Process.put(@span_key, span0)
      Process.put(@pspans_key, pspans0)
    end
  end

  defp refuse(proc, proto, reason \\ nil) do
    {:no, proc, proto, reason, step_at(Process.get(@span_key))}
  end

  defp open_head(proc, proto, penv, senv, book) do
    open_head(proc, proto, penv, senv, book, MapSet.new())
  end

  defp open_head(proc, proto, penv, senv, book, seen) do
    with {:ok, proc, penv} <- unwind_proc(proc, penv),
         {:ok, proto, senv} <- unwind_proto(proto, senv),
         {:ok, proto} <- expand_head(proto, book) do
      if head_again?(proto) do
        if MapSet.member?(seen, proto) do
          {:error, "unguarded session call"}
        else
          open_head(proc, proto, penv, senv, book, MapSet.put(seen, proto))
        end
      else
        {:ok, proc, proto, penv, senv}
      end
    end
  end

  defp head_again?({:rec, _, _}), do: true
  defp head_again?({:svar, _}), do: true
  defp head_again?(_), do: false

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
      :yes ->
        keep(descend(p, s, ctx, idx, penv, senv, seen, fuel - 1, book, step_down(here_span(), 0)))

      :no ->
        refuse(proc, proto, explain_no(ty, val, expected, ctx, book))

      {:error, msg} ->
        refuse(proc, proto, rewrite_run(msg))
    end
  end

  # `dput-arm`. The value selects one protocol arm. A variable continues
  # only when every arm is that same protocol.
  defp step(
         {:put, ty, val, p} = proc,
         {:dsend, y, sty, {:case, scrut, arms}} = proto,
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
        case select_sender(scrut, y, val, arms, ctx, book) do
          {:ok, chosen} ->
            keep(
              descend(
                p,
                chosen,
                ctx,
                ext(idx, y, sent_val(val, ctx, book), expected),
                penv,
                senv,
                seen,
                fuel - 1,
                book,
                step_down(here_span(), 0)
              )
            )

          {:error, msg} ->
            refuse(proc, proto, msg)
        end

      :no ->
        refuse(proc, proto, explain_no(ty, val, expected, ctx, book))

      {:error, msg} ->
        refuse(proc, proto, rewrite_run(msg))
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
          descend(
            p,
            s,
            ctx,
            ext(idx, y, sent_val(val, ctx, book), expected),
            penv,
            senv,
            seen,
            fuel - 1,
            book,
            step_down(here_span(), 0)
          )
        )

      :no ->
        refuse(proc, proto, explain_no(ty, val, expected, ctx, book))

      {:error, msg} ->
        refuse(proc, proto, rewrite_run(msg))
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
      keep(
        cont(
          p,
          s,
          name,
          expected,
          ctx,
          idx,
          penv,
          senv,
          seen,
          fuel,
          book,
          step_down(here_span(), 0)
        )
      )
    else
      refuse(proc, proto)
    end
  end

  # `mget-val` and `mget-run`. The process covers every constructor.
  # Each arm conforms to the protocol that constructor selects.
  defp step(
         {:get, ty, name, {:match, mscrut, ps}} = proc,
         {:drecv, y, sty, {:case, scrut, arms}} = proto,
         ctx,
         idx,
         penv,
         senv,
         seen,
         fuel,
         book
       ) do
    expected = apply_ty(idx, sty)

    cond do
      ty != expected ->
        refuse(proc, proto)

      mscrut != name ->
        {:error, step_at(step_down(here_span(), 0)), "match does not cover the received value"}

      scrut_binder(scrut) != y ->
        refuse(proc, proto, "a case is on the name just bound")

      true ->
        case zip_arms(scrut, expected, arms, ps, book) do
          {:ok, pairs} ->
            case arms_paired(
                   pairs,
                   bind_ctx(ctx, name, expected),
                   rename_idx(idx, y, name),
                   penv,
                   senv,
                   seen,
                   fuel,
                   book,
                   step_down(here_span(), 0),
                   0,
                   expected
                 ) do
              {:shape} -> refuse(proc, proto)
              other -> keep(other)
            end

          {:error, msg} ->
            refuse(proc, proto, msg)
        end
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
          book,
          step_down(here_span(), 0)
        )
      )
    else
      refuse(proc, proto)
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
            bound = resolve(idx, e)

            if owed?(got, bound, ctx) do
              keep(
                descend(
                  p,
                  s,
                  ctx,
                  idx,
                  penv,
                  senv,
                  seen,
                  fuel - 1,
                  book,
                  step_down(here_span(), 0)
                )
              )
            else
              refuse(proc, proto, bound_reason(val, got, bound, book))
            end

          {:error, msg} ->
            refuse(proc, proto, rewrite_run(msg))
        end

      :no ->
        refuse(proc, proto, explain_no(ty, val, :nat, ctx, book))

      {:error, msg} ->
        refuse(proc, proto, rewrite_run(msg))
    end
  end

  # `eget-ok`. The receiver binds a nat and owes nothing.
  defp step({:get, :nat, name, p}, {:erecv, _y, _e, s}, ctx, idx, penv, senv, seen, fuel, book) do
    keep(
      cont(p, s, name, :nat, ctx, idx, penv, senv, seen, fuel, book, step_down(here_span(), 0))
    )
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
        keep(
          descend(
            p,
            s,
            ctx,
            Map.delete(idx, y),
            penv,
            senv,
            seen,
            fuel - 1,
            book,
            step_down(here_span(), 0)
          )
        )

      :yes when val == :b1 ->
        keep(
          descend(
            p,
            t,
            ctx,
            Map.delete(idx, y),
            penv,
            senv,
            seen,
            fuel - 1,
            book,
            step_down(here_span(), 0)
          )
        )

      :no ->
        refuse(proc, proto, explain_no(ty, val, :bit, ctx, book))

      :yes ->
        refuse(proc, proto)

      {:error, msg} ->
        refuse(proc, proto, rewrite_run(msg))
    end
  end

  # `iget-ok`. Both arms are checked with the bit bound. It is not a length.
  defp step({:iget, name, p, q}, {:irecv, y, s, t}, ctx, idx, penv, senv, seen, fuel, book) do
    ctx1 = bind_ctx(ctx, name, :bit)
    idx1 = Map.delete(idx, y)
    span = here_span()

    case descend(p, s, ctx1, idx1, penv, senv, seen, fuel - 1, book, step_down(span, 0)) do
      :ok -> keep(descend(q, t, ctx1, idx1, penv, senv, seen, fuel - 1, book, step_down(span, 1)))
      no -> no
    end
  end

  defp step({:pick0, p}, {:choose, s, _}, ctx, idx, penv, senv, seen, fuel, book) do
    keep(descend(p, s, ctx, idx, penv, senv, seen, fuel - 1, book, step_down(here_span(), 0)))
  end

  defp step({:pick1, p}, {:choose, _, t}, ctx, idx, penv, senv, seen, fuel, book) do
    keep(descend(p, t, ctx, idx, penv, senv, seen, fuel - 1, book, step_down(here_span(), 0)))
  end

  defp step({:cover, p, q}, {:branch, s, t}, ctx, idx, penv, senv, seen, fuel, book) do
    span = here_span()

    case descend(p, s, ctx, idx, penv, senv, seen, fuel - 1, book, step_down(span, 0)) do
      :ok -> keep(descend(q, t, ctx, idx, penv, senv, seen, fuel - 1, book, step_down(span, 1)))
      no -> no
    end
  end

  defp step(p, s, _ctx, _idx, _penv, _senv, _seen, _fuel, _book), do: refuse(p, s)

  defp here_span, do: Process.get(@span_key)

  # A match is the continuation of the `get` just taken. Each arm conforms
  # to that one protocol. The processes may differ: the received value
  # chooses which process runs, and it does not choose another protocol.
  # A `case` protocol is the step above: each arm conforms to the protocol
  # that constructor selects. The scrutinee is the received name. A
  # received pair or record has one product arm. A nat, a vector, or
  # unit has no covering.
  @cover "match does not cover the received value"

  defp cont({:match, scrut, arms}, proto, name, ty, ctx, idx, penv, senv, seen, fuel, book, span) do
    if scrut != name do
      {:error, step_at(span), @cover}
    else
      case explain_cover(ty, arms, book) do
        :ok ->
          arms_go(
            arms,
            proto,
            bind_ctx(ctx, name, ty),
            ty,
            idx,
            penv,
            senv,
            seen,
            fuel,
            book,
            span,
            0
          )

        {:error, msg} ->
          {:error, step_at(span), msg}
      end
    end
  end

  defp cont(p, proto, name, ty, ctx, idx, penv, senv, seen, fuel, book, span) do
    descend(p, proto, bind_ctx(ctx, name, ty), idx, penv, senv, seen, fuel - 1, book, span)
  end

  defp arms_go([], _proto, _ctx, _ty, _idx, _penv, _senv, _seen, _fuel, _book, _span, _i),
    do: :ok

  defp arms_go([arm | ps], proto, ctx, ty, idx, penv, senv, seen, fuel, book, span, i) do
    case open_arm(arm, ctx, ty, i, book) do
      {:ok, p, ctx1} ->
        case descend(p, proto, ctx1, idx, penv, senv, seen, fuel - 1, book, step_down(span, i)) do
          :ok ->
            arms_go(ps, proto, ctx, ty, idx, penv, senv, seen, fuel, book, span, i + 1)

          other ->
            other
        end

      {:error, msg} ->
        {:error, step_at(step_down(span, i)), msg}
    end
  end

  # `:pass` is a bit or declared data, checked by `covered?`. A pair or a
  # record has one product arm, and the refusal names the mismatch.
  defp explain_cover(ty, arms, book) do
    case product_cover(ty, arms) do
      :pass -> if covered?(ty, arms, book) == :ok, do: :ok, else: {:error, @cover}
      other -> other
    end
  end

  defp product_cover({:pair, _, _}, arms), do: pair_cover(arms)
  defp product_cover({:rec, fields}, arms), do: rec_cover(fields, arms)
  defp product_cover(_, _), do: :pass

  defp pair_cover([{:prod, {:pair, [x, y]}, _}]) when is_atom(x) and is_atom(y), do: :ok
  defp pair_cover([{:prod, {:pair, _}, _}]), do: {:error, "wrong arity"}
  defp pair_cover([{:arm, _, _, _}]), do: {:error, "constructor arm on a pair"}
  defp pair_cover(_), do: {:error, @cover}

  defp rec_cover(fields, [{:prod, {:rec, bs}, _}]) when is_list(bs) do
    case rec_fit(fields, bs) do
      :ok -> :ok
      {:error, msg} -> {:error, msg}
    end
  end

  defp rec_cover(_fields, [{:arm, _, _, _}]), do: {:error, "constructor arm on a record"}
  defp rec_cover(_fields, _), do: {:error, @cover}

  # Duplicate fields first. Then the names, lockstep with the type.
  defp rec_fit(fields, bs) when is_list(fields) and is_list(bs) do
    type_names = Enum.map(fields, fn {name, _} -> name end)
    pat_names = Enum.map(bs, fn {name, _} -> name end)

    if dup_name?(pat_names) do
      {:error, "duplicate field"}
    else
      walk_fields(type_names, pat_names, type_names, pat_names)
    end
  end

  defp rec_fit(_, _), do: {:error, @cover}

  defp dup_name?(names) do
    Enum.reduce_while(names, MapSet.new(), fn name, seen ->
      if MapSet.member?(seen, name), do: {:halt, true}, else: {:cont, MapSet.put(seen, name)}
    end) == true
  end

  defp walk_fields([], [], _all_t, _all_p), do: :ok
  defp walk_fields([], [_ | _], _all_t, _all_p), do: {:error, "extra field"}
  defp walk_fields([_ | _], [], _all_t, _all_p), do: {:error, "missing field"}

  defp walk_fields([t | ts], [p | ps], all_t, all_p) do
    cond do
      t == p -> walk_fields(ts, ps, all_t, all_p)
      p not in all_t -> {:error, "extra field"}
      t not in all_p -> {:error, "missing field"}
      true -> {:error, "field out of order"}
    end
  end

  # A positional arm keeps the received name. A named arm binds the fields
  # of the constructor at this index, innermost last, over that name.
  # A product arm binds the components, last binder innermost.
  defp open_arm({:prod, {:pair, [x, y]}, body}, ctx, {:pair, a, b}, _i, _book)
       when is_atom(x) and is_atom(y) do
    {:ok, body, bind_fields(ctx, [x, y], [a, b])}
  end

  defp open_arm({:prod, {:pair, _}, _body}, _ctx, {:pair, _, _}, _i, _book),
    do: {:error, "wrong arity"}

  defp open_arm({:prod, {:rec, bs}, body}, ctx, {:rec, fields}, _i, _book) when is_list(bs) do
    case rec_fit(fields, bs) do
      :ok ->
        binders = Enum.map(bs, fn {_, binder} -> binder end)
        tys = Enum.map(fields, fn {_, ty} -> ty end)
        {:ok, body, bind_fields(ctx, binders, tys)}

      {:error, msg} ->
        {:error, msg}
    end
  end

  defp open_arm({:prod, _, _}, _ctx, _ty, _i, _book), do: {:error, @cover}

  defp open_arm({:arm, ctor, binders, body}, ctx, ty, i, book)
       when is_binary(ctor) and is_list(binders) do
    case field_tys(ty, i, book) do
      {:ok, expected, fields} ->
        cond do
          ctor != expected -> {:error, @cover}
          length(binders) != length(fields) -> {:error, "wrong arity"}
          true -> {:ok, body, bind_fields(ctx, binders, fields)}
        end

      :error ->
        {:error, @cover}
    end
  end

  defp open_arm(proc, ctx, _ty, _i, _book), do: {:ok, proc, ctx}

  defp bind_fields(ctx, binders, tys) do
    Enum.reduce(Enum.zip(binders, tys), ctx, fn {name, fty}, acc ->
      bind_field(acc, name, fty)
    end)
  end

  # The field mark is what `answer` reads. A later `get` of the same name
  # clears it, so the innermost binding wins and a received nat stays a nat.
  defp bind_field(ctx, name, ty) do
    ctx
    |> bind_ctx(name, ty)
    |> Map.put({:field, name}, true)
  end

  defp field_tys(:bit, 0, _book), do: {:ok, "b0", []}
  defp field_tys(:bit, 1, _book), do: {:ok, "b1", []}

  defp field_tys({:dat, dname, _args} = ty, i, book) do
    case Enum.at(ctor_names(book, dname), i) do
      nil ->
        :error

      ctor ->
        case fields_of_ctor(ty, ctor, book) do
          {:ok, fields} -> {:ok, ctor, fields}
          :error -> :error
        end
    end
  end

  defp field_tys(_, _, _), do: :error

  defp fields_of_ctor(:bit, "b0", _book), do: {:ok, []}
  defp fields_of_ctor(:bit, "b1", _book), do: {:ok, []}

  defp fields_of_ctor({:dat, dname, args}, ctor, book) do
    case find_decl(book, dname) do
      nil ->
        :error

      d ->
        case ctor_fields(d, ctor) do
          {:ok, tmpls} -> {:ok, Enum.map(tmpls, &inst_field(&1, dname, args))}
          :error -> :error
        end
    end
  end

  defp fields_of_ctor(_, _, _), do: :error

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
    do: Enum.reduce(arms, MapSet.new(), &MapSet.union(free_proc(arm_body(&1)), &2))

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
  defp free_proto({:sjump, _, _}), do: MapSet.new()
  defp free_proto({:sess, _, _}), do: MapSet.new()

  defp free_proto({:case, _, arms}) do
    Enum.reduce(arms, MapSet.new(), fn {_, s}, acc -> MapSet.union(acc, free_proto(s)) end)
  end

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
    |> Map.delete({:field, name})
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

  defp proto_at({:dsend, name, ty, {:case, scrut, arms}}, ctx, book) do
    with_ty(ty_ok(ty, ctx, book), case_ok(name, ty, scrut, arms, ctx, book))
  end

  defp proto_at({:drecv, name, ty, {:case, scrut, arms}}, ctx, book) do
    with_ty(ty_ok(ty, ctx, book), case_ok(name, ty, scrut, arms, ctx, book))
  end

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

  defp proto_at({:sjump, _, _}, _ctx, _book), do: :ok

  defp proto_at({:sess, name, args}, ctx, book) when is_binary(name) and is_list(args) do
    with :ok <- args_ok(args, ctx, book) do
      # The self name is the key that `decl_ok` stored. A guarded call
      # of that name is the loop. It is not opened again here.
      self = self_of(ctx)

      cond do
        name == self and Map.get(ctx, {:self, name}) == :unguarded ->
          {:error, "unguarded session call"}

        name == self ->
          :ok

        true ->
          call_known(name, args, ctx)
      end
    end
  end

  defp proto_at({:case, _, _}, _ctx, _book),
    do: {:error, "a case follows the value just exchanged"}

  defp proto_at(_, _ctx, _book), do: {:error, "ill-formed protocol"}

  # A case is the continuation of the binder just written. Direct arms
  # are that payload's constructors. A run's arms are the result's
  # constructors. The payload itself is still a bit or declared data.
  # A run that reads a splittable field is split on the values it reads.
  defp case_ok(name, ty, scrut, arms, ctx, book) do
    ctx1 = guard(Map.put(ctx, name, ty))

    case scrut do
      {:name, ^name} ->
        val_case(ty, arms, ctx1, book)

      {:run, fname, ^name} ->
        run_case(fname, ty, arms, ctx, ctx1, book)

      {:name, _} ->
        {:error, "a case is on the name just bound"}

      {:run, _, _} ->
        {:error, "a case is on the name just bound"}

      _ ->
        {:error, "a case follows the value just exchanged"}
    end
  end

  defp val_case(ty, arms, ctx, book) do
    case arm_labels(ty, book) do
      {:ok, labels} ->
        if labels == Enum.map(arms, fn {c, _} -> c end) do
          arms_ok(arms, ctx, book)
        else
          {:error, "case arms do not match the constructors"}
        end

      :error ->
        {:error, "a case is on a bit or a declared data type"}
    end
  end

  defp run_case(fname, ty, arms, ctx, ctx1, book) do
    source = Map.get(ctx, {:__book__, :book}, [])
    prepared = prepare(source)

    case run_view(fname, ty, prepared, book) do
      {:ok, labels} ->
        cond do
          labels != Enum.map(arms, fn {c, _} -> c end) ->
            {:error, "case arms do not match the constructors"}

          arm_labels(ty, book) == :error ->
            {:error, "a case is on a bit or a declared data type"}

          true ->
            arms_ok(arms, ctx1, book)
        end

      {:error, msg} ->
        {:error, msg}
    end
  end

  defp arms_ok([], _ctx, _book), do: :ok

  defp arms_ok([{_, s} | rest], ctx, book) do
    with_ty(proto_at(s, ctx, book), arms_ok(rest, ctx, book))
  end

  # One argument, the payload's type, a result that has constructors,
  # a body in the computed fragment, and no call of this definition or
  # of one declared later.
  defp run_view(fname, payload, prepared, data_book) do
    defs = run_defs(prepared)

    case Enum.find_index(defs, &(&1.name == fname)) do
      nil ->
        {:error, "the run does not decide an arm"}

      i ->
        defn = Enum.at(defs, i)
        prefix = Enum.take(defs, i)

        case one_arg(defn) do
          {:ok, domain, codomain, body} ->
            cond do
              not type_matches?(payload, domain, data_book) ->
                {:error, "the run does not decide an arm"}

              calls_out?(body, prefix, defs) ->
                {:error, run_cycle(fname, body)}

              head = outside_fragment(body) ->
                {:error, "outside the computed fragment: #{head}"}

              true ->
                case result_ty(codomain, data_book) do
                  {:ok, rty} ->
                    case arm_labels(rty, data_book) do
                      {:ok, labels} -> {:ok, labels}
                      :error -> {:error, "a case is on a bit or a declared data type"}
                    end

                  :error ->
                    {:error, "a case is on a bit or a declared data type"}
                end
            end

          :error ->
            {:error, "the run does not decide an arm"}
        end
    end
  end

  defp one_arg(%{type: {:pi, _, domain, _, codomain}, body: {:lam, _, _, _, body}}) do
    if match?({:pi, _, _, _, _}, codomain) do
      :error
    else
      {:ok, domain, codomain, body}
    end
  end

  defp one_arg(_), do: :error

  # Parameter types, outermost first, then the codomain.
  defp pi_chain({:pi, _, domain, _, cod}, acc), do: pi_chain(cod, acc ++ [domain])
  defp pi_chain(cod, acc), do: {acc, cod}

  defp run_cycle(fname, body) do
    if call_of?(body, fname),
      do: "run definition calls itself",
      else: "run definition declared later"
  end

  defp outside_fragment(:ze), do: nil
  defp outside_fragment(:one), do: nil
  defp outside_fragment({:var, i}) when is_integer(i), do: nil
  defp outside_fragment({:def, name}) when is_binary(name), do: nil
  defp outside_fragment({:su, t}), do: outside_fragment(t)
  defp outside_fragment({:ann, t, _}), do: outside_fragment(t)
  defp outside_fragment({:pair, a, b}), do: outside_fragment(a) || outside_fragment(b)
  defp outside_fragment({:app, f, a}), do: outside_fragment(f) || outside_fragment(a)

  defp outside_fragment({:mnat, e, _, z, s}) do
    outside_fragment(e) || outside_fragment(z) || outside_fragment(s)
  end

  defp outside_fragment({:mdata, e, _, branches}) when is_list(branches) do
    outside_fragment(e) || branch_fragment(branches)
  end

  defp outside_fragment(other), do: fragment_head(other)

  defp branch_fragment(branches) do
    Enum.find_value(branches, fn branch ->
      case branch_shape(branch) do
        {_, _, body} -> outside_fragment(body)
        _ -> "match"
      end
    end)
  end

  defp fragment_head({:lam, _, _, _, _}), do: "λ"
  defp fragment_head({:let, _, _, _, _}), do: "let"
  defp fragment_head({:letp, _, _, _, _}), do: "let"
  defp fragment_head(other) when is_atom(other), do: Atom.to_string(other)
  defp fragment_head(other) when is_tuple(other), do: other |> elem(0) |> to_string()
  defp fragment_head(_), do: "term"

  defp type_matches?(:nat, :nat, _), do: true
  defp type_matches?(:unit, :unit, _), do: true
  defp type_matches?(:bit, {:def, "Bit"}, book), do: find_decl(book, "Bit") == nil
  defp type_matches?(:unit, {:def, "Unit"}, book), do: find_decl(book, "Unit") == nil

  defp type_matches?({:dat, name, args}, term, book) do
    case type_spine(term, []) do
      {:ok, ^name, targs} when length(args) == length(targs) ->
        find_decl(book, name) != nil and
          Enum.all?(Enum.zip(args, targs), fn {a, b} -> type_matches?(a, b, book) end)

      _ ->
        false
    end
  end

  defp type_matches?(_, _, _), do: false

  defp type_spine({:app, f, a}, acc), do: type_spine(f, [a | acc])
  defp type_spine({:def, name}, acc) when is_binary(name), do: {:ok, name, acc}
  defp type_spine(_, _), do: :error

  defp result_ty(:nat, _), do: {:ok, :nat}
  defp result_ty(:unit, _), do: {:ok, :unit}

  defp result_ty({:def, "Bit"}, book) do
    if find_decl(book, "Bit"), do: {:ok, {:dat, "Bit", []}}, else: {:ok, :bit}
  end

  defp result_ty({:def, "Unit"}, book) do
    if find_decl(book, "Unit"), do: {:ok, {:dat, "Unit", []}}, else: {:ok, :unit}
  end

  defp result_ty({:def, name}, book) when is_binary(name) do
    if find_decl(book, name), do: {:ok, {:dat, name, []}}, else: :error
  end

  defp result_ty({:app, _, _} = term, book) do
    case type_spine(term, []) do
      {:ok, name, args} ->
        if find_decl(book, name) do
          case result_list(args, book) do
            {:ok, as} -> {:ok, {:dat, name, as}}
            :error -> :error
          end
        else
          :error
        end

      _ ->
        :error
    end
  end

  defp result_ty(_, _), do: :error

  defp result_list(args, book) do
    Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, acc} ->
      case result_ty(arg, book) do
        {:ok, ty} -> {:cont, {:ok, acc ++ [ty]}}
        :error -> {:halt, :error}
      end
    end)
  end

  defp arm_labels(:bit, _book), do: {:ok, ["b0", "b1"]}

  defp arm_labels({:dat, name, _}, book) do
    case ctor_names(book, name) do
      [] -> :error
      names -> {:ok, names}
    end
  end

  defp arm_labels(_, _), do: :error

  defp scrut_binder({:name, n}), do: n
  defp scrut_binder({:run, _, n}), do: n
  defp scrut_binder(_), do: nil

  defp show_scrut({:name, n}), do: "#{n}"
  defp show_scrut({:run, f, n}), do: "(#{f} #{n})"
  defp show_scrut(_), do: "?"

  @doc false
  def chosen_arm(scrut, val, arms, book) do
    book = if is_list(book), do: prepare(book), else: book
    choose_arm(scrut, val, arms, book)
  end

  defp select_sender(scrut, binder, val, arms, ctx, book) do
    if scrut_binder(scrut) != binder do
      {:error, "a case is on the name just bound"}
    else
      case known_payload(val, ctx, book) do
        {:ok, v} -> choose_arm(scrut, v, arms, book)
        :unknown -> agree_arms(val, arms)
        {:error, msg} -> {:error, rewrite_run(msg)}
      end
    end
  end

  defp known_payload(val, ctx, book) do
    case reduce(val, ctx, book) do
      {:error, msg} ->
        {:error, msg}

      {:ok, :miss} ->
        :unknown

      {:ok, v} ->
        case canon(v, book) do
          {:var, _} -> :unknown
          other -> {:ok, other}
        end
    end
  end

  defp agree_arms(val, [{_, proto} | rest]) do
    if Enum.all?(rest, fn {_, other} -> other == proto end) do
      {:ok, proto}
    else
      {:error, "the value #{show_val(val)} does not select an arm"}
    end
  end

  defp agree_arms(val, _) do
    {:error, "the value #{show_val(val)} does not select an arm"}
  end

  defp choose_arm({:name, _}, val, arms, _book) do
    case ctor_tag(val) do
      nil -> {:error, "the value #{show_val(val)} does not select an arm"}
      tag -> fetch_arm(tag, arms, "the value #{tag} does not select an arm")
    end
  end

  defp choose_arm({:run, fname, _}, val, arms, book) do
    case apply_run(fname, [val], book) do
      {:ok, :miss} ->
        {:error, "the run does not decide an arm"}

      {:ok, result} ->
        case ctor_tag(result) do
          nil -> {:error, "the run does not decide an arm"}
          tag -> fetch_arm(tag, arms, "the run does not decide an arm")
        end

      {:error, msg} ->
        {:error, rewrite_run(msg)}
    end
  end

  defp choose_arm(_, _, _, _), do: {:error, "a case follows the value just exchanged"}

  defp fetch_arm(tag, arms, missing) do
    case Enum.find(arms, fn {c, _} -> c == tag end) do
      {_, proto} -> {:ok, proto}
      nil -> {:error, missing}
    end
  end

  defp apply_run(name, args, book), do: eval_call(name, args, book)

  defp ctor_tag(:b0), do: "b0"
  defp ctor_tag(:b1), do: "b1"
  defp ctor_tag({:con, name, _}), do: cname(name)
  defp ctor_tag(_), do: nil

  defp zip_arms({:name, _}, ty, arms, ps, book) do
    case arm_labels(ty, book) do
      {:ok, labels} ->
        got = Enum.map(arms, fn {c, _} -> c end)

        cond do
          labels != got ->
            {:error, "case arms do not match the constructors"}

          length(ps) != length(arms) ->
            {:error, "match does not cover the received value"}

          true ->
            {:ok, Enum.map(Enum.zip(ps, arms), fn {p, {c, s}} -> {p, c, s} end)}
        end

      :error ->
        {:error, "a case is on a bit or a declared data type"}
    end
  end

  defp zip_arms({:run, fname, _}, ty, arms, ps, book) do
    case arm_labels(ty, book) do
      {:ok, ctors} when length(ctors) == length(ps) ->
        zip_run(fname, ty, ctors, arms, ps, book, [])

      {:ok, _} ->
        {:error, "match does not cover the received value"}

      :error ->
        {:error, "a case is on a bit or a declared data type"}
    end
  end

  defp zip_arms(_, _, _, _, _), do: {:error, "a case follows the value just exchanged"}

  defp zip_run(_fname, _ty, [], _arms, [], _book, acc), do: {:ok, Enum.reverse(acc)}

  defp zip_run(fname, ty, [c | cs], arms, [p | ps], book, acc) do
    case split_of(fname, ty, c, arms, book) do
      {:ok, {:flat, proto}} ->
        zip_run(fname, ty, cs, arms, ps, book, [{:flat, p, c, proto} | acc])

      {:ok, {:node, index, ch}} ->
        zip_run(fname, ty, cs, arms, ps, book, [{:node, p, c, index, ch} | acc])

      :no ->
        {:error, "the run does not decide an arm"}

      {:error, msg} ->
        {:error, rewrite_run(msg)}
    end
  end

  defp zip_run(_, _, _, _, _, _, _), do: {:error, "match does not cover the received value"}

  defp probe_of(:bit, "b0"), do: :b0
  defp probe_of(:bit, "b1"), do: :b1
  defp probe_of(_, c), do: {:con, c, []}

  # A field is splittable when it is a bit or a declared data type.
  # The split follows the run. A field the run binds and does not read
  # is a dummy, and it is not a node. A nat, a vector, a pair, or a
  # record is not a finite split.
  defp splittable?(:bit), do: true
  defp splittable?({:dat, _, _}), do: true
  defp splittable?(_), do: false

  defp pay_ctors(:bit, _book), do: ["b0", "b1"]

  defp pay_ctors({:dat, name, _}, book) do
    case ctor_names(book, name) do
      [] -> nil
      names -> names
    end
  end

  defp pay_ctors(_, _), do: nil

  defp any_var(p, {:var, i}) when is_integer(i), do: p.(i)
  defp any_var(p, {:su, t}), do: any_var(p, t)
  defp any_var(p, {:ann, t, _}), do: any_var(p, t)
  defp any_var(p, {:pair, a, b}), do: any_var(p, a) or any_var(p, b)
  defp any_var(p, {:app, f, a}), do: any_var(p, f) or any_var(p, a)
  defp any_var(p, {:mnat, e, _, z, s}), do: any_var(p, e) or any_var(p, z) or any_var(p, s)

  defp any_var(p, {:mnat, e, _, _, z, _, s}),
    do: any_var(p, e) or any_var(p, z) or any_var(p, s)

  defp any_var(p, {:mdata, e, _, branches}) when is_list(branches),
    do: any_var(p, e) or any_arms(p, branches)

  defp any_var(p, {:mdata, e, _, _, branches}) when is_list(branches),
    do: any_var(p, e) or any_arms(p, branches)

  defp any_var(_, _), do: false

  defp any_arms(p, branches) do
    Enum.any?(branches, fn branch ->
      case branch_shape(branch) do
        {_, _, body} -> any_var(p, body)
        _ -> false
      end
    end)
  end

  defp in_range?(lo, hi, j), do: lo <= j and j < hi

  defp occurs_between(lo, hi, term), do: any_var(&in_range?(lo, hi, &1), term)

  defp read_idxs(tys, term), do: read_go(0, tys, term)

  defp read_go(_i, [], _term), do: {:ok, []}

  defp read_go(i, [a | ts], term) do
    if any_var(&(&1 == length(ts)), term) do
      if splittable?(a) do
        case read_go(i + 1, ts, term) do
          {:ok, is} -> {:ok, [i | is]}
          :no -> :no
        end
      else
        :no
      end
    else
      read_go(i + 1, ts, term)
    end
  end

  defp others(tys, i, term), do: others_go(0, tys, i, term)

  defp others_go(_j, [], _i, _term), do: false
  defp others_go(j, [_a | ts], i, term) when j == i, do: others_go(j + 1, ts, i, term)

  defp others_go(j, [_a | ts], i, term) do
    if any_var(&(&1 == length(ts)), term), do: true, else: others_go(j + 1, ts, i, term)
  end

  defp lookup_field(tys, k), do: look_field(0, tys, k)

  defp look_field(_i, [], _k), do: nil

  defp look_field(i, [a | ts], k) do
    if length(ts) == k, do: {i, a}, else: look_field(i + 1, ts, k)
  end

  defp mk_val(:bit, "b0", _ftys, _book), do: :b0
  defp mk_val(:bit, "b1", _ftys, _book), do: :b1
  defp mk_val(:bit, _, _ftys, _book), do: :b0
  defp mk_val(_ty, c, ftys, _book), do: {:con, c, Enum.map(ftys, &dummy_field/1)}

  defp dummy_field(:nat), do: {:nat, 0}
  defp dummy_field(:bit), do: :b0
  defp dummy_field(:unit), do: :tt
  defp dummy_field({:pair, a, b}), do: {:tup, dummy_field(a), dummy_field(b)}

  defp dummy_field({:rec, fields}) when is_list(fields) do
    {:rec, Enum.map(fields, fn {name, ty} -> {name, dummy_field(ty)} end)}
  end

  defp dummy_field({:vec, _, _}), do: []
  defp dummy_field(_), do: {:con, "•", []}

  defp set_field({:con, c, rs}, i, r) when is_list(rs), do: {:con, c, List.replace_at(rs, i, r)}
  defp set_field(v, _i, _r), do: v

  defp poke(host, [], i, r), do: set_field(host, i, r)

  defp poke(host, [j | js], i, r) do
    case field_at(host, j) do
      nil -> host
      inner -> set_field(host, j, poke(inner, js, i, r))
    end
  end

  defp field_at({:con, _, rs}, i) when is_list(rs), do: Enum.at(rs, i)
  defp field_at(_, _), do: nil

  defp opened({:mdata, {:var, 0}, _, branches}, c) when is_list(branches) do
    case find_branch(branches, c) do
      {_, _, body} -> body
      _ -> nil
    end
  end

  defp opened({:mdata, {:var, 0}, _, _, branches}, c) when is_list(branches) do
    opened({:mdata, {:var, 0}, nil, branches}, c)
  end

  defp opened(_, _), do: nil

  defp split_of(fname, ty, ctor, arms, book) do
    defs = run_defs(book)

    case Enum.find_index(defs, &(&1.name == fname)) do
      nil ->
        :no

      i ->
        case one_arg(Enum.at(defs, i)) do
          {:ok, _domain, _codomain, body} ->
            case fields_of_ctor(ty, ctor, book) do
              :error ->
                :no

              {:ok, ftys} ->
                case opened(body, ctor) do
                  nil -> plain_probe(fname, ty, ctor, arms, book)
                  b -> guard(fname, arms, ftys, [], 0, 0, mk_val(ty, ctor, ftys, book), b, book)
                end
            end

          :error ->
            :no
        end
    end
  end

  defp plain_probe(fname, ty, ctor, arms, book) do
    case apply_run(fname, [probe_of(ty, ctor)], book) do
      {:ok, :miss} -> :no
      {:ok, result} -> flat_result(result, arms)
      {:error, msg} -> {:error, msg}
    end
  end

  defp flat_result(result, arms) do
    case ctor_tag(result) do
      nil ->
        :no

      tag ->
        case fetch_arm(tag, arms, "the run does not decide an arm") do
          {:ok, proto} -> {:ok, {:flat, proto}}
          {:error, _} -> :no
        end
    end
  end

  defp proto_at(fname, host, arms, book) do
    case apply_run(fname, [host], book) do
      {:ok, :miss} ->
        :no

      {:ok, result} ->
        case ctor_tag(result) do
          nil ->
            :no

          tag ->
            case fetch_arm(tag, arms, "the run does not decide an arm") do
              {:ok, proto} -> {:ok, proto}
              {:error, _} -> :no
            end
        end

      {:error, msg} ->
        {:error, msg}
    end
  end

  defp guard(fname, arms, tys, path, lo, hi, host, {:mdata, {:var, k}, _, branches} = term, book)
       when is_integer(k) and is_list(branches) do
    guard_at(fname, arms, tys, path, lo, hi, host, term, {:field, k, branches}, book)
  end

  defp guard(
         fname,
         arms,
         tys,
         path,
         lo,
         hi,
         host,
         {:mdata, {:var, k}, _, _, branches} = term,
         book
       )
       when is_integer(k) and is_list(branches) do
    guard_at(fname, arms, tys, path, lo, hi, host, term, {:field, k, branches}, book)
  end

  defp guard(fname, arms, tys, path, lo, hi, host, term, book) do
    guard_at(fname, arms, tys, path, lo, hi, host, term, :term, book)
  end

  defp guard_at(fname, arms, tys, path, lo, hi, host, term, how, book) do
    cond do
      occurs_between(lo, hi, term) ->
        :no

      true ->
        case read_idxs(tys, term) do
          :no ->
            :no

          {:ok, is} ->
            case how do
              {:field, k, branches} ->
                on_field(lookup_field(tys, k), fname, arms, tys, path, host, branches, is, book)

              :term ->
                enum_or(fname, arms, tys, host, is, book)
            end
        end
    end
  end

  defp on_field(nil, fname, arms, tys, _path, host, _branches, is, book) do
    enum_or(fname, arms, tys, host, is, book)
  end

  defp on_field({i, a}, fname, arms, tys, path, host, branches, _is, book) do
    if splittable?(a) do
      case pay_ctors(a, book) do
        nil ->
          :no

        cs ->
          case kids(fname, arms, tys, path, host, i, a, cs, branches, book) do
            {:ok, ch} -> {:ok, collapse(i, ch)}
            other -> other
          end
      end
    else
      :no
    end
  end

  defp kids(_fname, _arms, _tys, _path, _host, _i, _a, [], [], _book), do: {:ok, []}

  defp kids(fname, arms, tys, path, host, i, a, [c | cs], [branch | as], book) do
    case branch_shape(branch) do
      {d, _, b} ->
        if cname(d) == c do
          case fields_of_ctor(a, c, book) do
            {:ok, ts} ->
              case descend(fname, arms, tys, path, host, i, a, c, ts, b, book) do
                {:ok, s} ->
                  case kids(fname, arms, tys, path, host, i, a, cs, as, book) do
                    {:ok, ch} -> {:ok, [{c, s} | ch]}
                    other -> other
                  end

                other ->
                  other
              end

            :error ->
              :no
          end
        else
          :no
        end

      _ ->
        :no
    end
  end

  defp kids(_, _, _, _, _, _, _, _, _, _), do: :no

  defp descend(fname, arms, tys, path, host, i, a, c, [], b, book) do
    if others(tys, i, b) do
      :no
    else
      guard(fname, arms, [], path, 0, 0, poke(host, path, i, mk_val(a, c, [], book)), b, book)
    end
  end

  defp descend(fname, arms, tys, path, host, i, a, c, ts, b, book) do
    guard(
      fname,
      arms,
      ts,
      path ++ [i],
      length(ts),
      length(ts) + length(tys),
      poke(host, path, i, mk_val(a, c, ts, book)),
      b,
      book
    )
  end

  defp enum_or(fname, arms, _tys, host, [], book) do
    case proto_at(fname, host, arms, book) do
      {:ok, proto} -> {:ok, {:flat, proto}}
      other -> other
    end
  end

  defp enum_or(fname, arms, tys, host, [i | is], book) do
    case Enum.at(tys, i) do
      nil ->
        :no

      a ->
        case pay_ctors(a, book) do
          nil ->
            :no

          cs ->
            case enum_cs(fname, arms, tys, host, i, is, a, cs, book) do
              {:ok, ch} -> {:ok, collapse(i, ch)}
              other -> other
            end
        end
    end
  end

  defp enum_cs(_fname, _arms, _tys, _host, _i, _is, _a, [], _book), do: {:ok, []}

  defp enum_cs(fname, arms, tys, host, i, is, a, [c | cs], book) do
    case fields_of_ctor(a, c, book) do
      {:ok, ts} ->
        host1 = set_field(host, i, mk_val(a, c, ts, book))

        case enum_or(fname, arms, tys, host1, is, book) do
          {:ok, s} ->
            case enum_cs(fname, arms, tys, host, i, is, a, cs, book) do
              {:ok, ch} -> {:ok, [{c, s} | ch]}
              other -> other
            end

          other ->
            other
        end

      :error ->
        :no
    end
  end

  defp collapse(i, [{_c, {:flat, s}} | rest] = ch) do
    case agree_split(s, rest) do
      {:ok, _} -> {:flat, s}
      :no -> {:node, i, ch}
    end
  end

  defp collapse(i, ch), do: {:node, i, ch}

  defp agree_split(s, []), do: {:ok, s}
  defp agree_split(s, [{_, {:flat, t}} | ch]) when s == t, do: agree_split(s, ch)
  defp agree_split(_s, [{_, {:flat, _t}} | _ch]), do: :no
  defp agree_split(_s, [{_, {:node, _, _}} | _]), do: :no

  defp arms_paired([], _ctx, _idx, _penv, _senv, _seen, _fuel, _book, _span, _i, _ty),
    do: :ok

  defp arms_paired(
         [{:flat, p, ctor, proto} | pairs],
         ctx,
         idx,
         penv,
         senv,
         seen,
         fuel,
         book,
         span,
         i,
         ty
       ) do
    case open_named(p, ctor, ty, ctx, book) do
      {:ok, body, ctx1} ->
        case descend(body, proto, ctx1, idx, penv, senv, seen, fuel - 1, book, step_down(span, i)) do
          :ok ->
            arms_paired(pairs, ctx, idx, penv, senv, seen, fuel, book, span, i + 1, ty)

          other ->
            other
        end

      {:error, msg} ->
        {:error, step_at(step_down(span, i)), msg}
    end
  end

  defp arms_paired(
         [{:node, p, ctor, index, children} | pairs],
         ctx,
         idx,
         penv,
         senv,
         seen,
         fuel,
         book,
         span,
         i,
         ty
       ) do
    case cover_node(p, ctor, index, children, ty, ctx, book) do
      {:ok, jobs} ->
        case check_jobs(jobs, idx, penv, senv, seen, fuel, book, span, i) do
          :ok ->
            arms_paired(pairs, ctx, idx, penv, senv, seen, fuel, book, span, i + 1, ty)

          other ->
            other
        end

      {:shape} ->
        {:shape}

      {:error, msg} ->
        {:error, step_at(step_down(span, i)), msg}
    end
  end

  # A direct case is one protocol per constructor. It is the flat split.
  defp arms_paired(
         [{p, ctor, proto} | pairs],
         ctx,
         idx,
         penv,
         senv,
         seen,
         fuel,
         book,
         span,
         i,
         ty
       )
       when is_binary(ctor) do
    arms_paired(
      [{:flat, p, ctor, proto} | pairs],
      ctx,
      idx,
      penv,
      senv,
      seen,
      fuel,
      book,
      span,
      i,
      ty
    )
  end

  defp check_jobs([], _idx, _penv, _senv, _seen, _fuel, _book, _span, _i), do: :ok

  defp check_jobs(
         [{:check, body, proto, ctx1} | rest],
         idx,
         penv,
         senv,
         seen,
         fuel,
         book,
         span,
         i
       ) do
    case descend(body, proto, ctx1, idx, penv, senv, seen, fuel - 1, book, step_down(span, i)) do
      :ok -> check_jobs(rest, idx, penv, senv, seen, fuel, book, span, i)
      other -> other
    end
  end

  # A node is a case on the field the run reads. A flat child is one
  # process. A nested node is a case on the field that child binds.
  defp cover_node({:arm, ctor, binders, {:match, y, inner}}, expected, i, children, ty, ctx, book)
       when is_binary(ctor) and is_list(binders) and is_list(inner) do
    cond do
      ctor != expected ->
        {:error, @cover}

      true ->
        case fields_of_ctor(ty, expected, book) do
          {:ok, ftys} ->
            cond do
              length(binders) != length(ftys) ->
                {:error, "wrong arity"}

              Enum.at(binders, i) != y ->
                {:shape}

              true ->
                case Enum.at(ftys, i) do
                  fty when not is_nil(fty) ->
                    if splittable?(fty) do
                      pair_fork(children, inner, fty, bind_fields(ctx, binders, ftys), book)
                    else
                      {:shape}
                    end

                  _ ->
                    {:shape}
                end
            end

          :error ->
            {:error, @cover}
        end
    end
  end

  defp cover_node({:arm, ctor, _, _}, expected, _, _, _, _, _)
       when is_binary(ctor) and ctor != expected,
       do: {:error, @cover}

  defp cover_node(_, _, _, _, _, _, _), do: {:shape}

  defp pair_fork([], [], _fty, _ctx, _book), do: {:ok, []}
  defp pair_fork([], [_ | _], _fty, _ctx, _book), do: {:error, @cover}
  defp pair_fork([_ | _], [], _fty, _ctx, _book), do: {:error, @cover}

  defp pair_fork([{cname, {:flat, proto}} | ch], [p | ps], fty, ctx, book) do
    case open_named(p, cname, fty, ctx, book) do
      {:ok, body, ctx1} ->
        case pair_fork(ch, ps, fty, ctx, book) do
          {:ok, rest} -> {:ok, [{:check, body, proto, ctx1} | rest]}
          other -> other
        end

      {:error, msg} ->
        {:error, msg}
    end
  end

  defp pair_fork([{cname, {:node, j, ch2}} | ch], [arm | ps], fty, ctx, book) do
    case arm do
      {:arm, c, xs, {:match, y, inner}}
      when is_binary(c) and is_list(xs) and is_list(inner) ->
        cond do
          c != cname ->
            {:error, @cover}

          Enum.at(xs, j) != y ->
            {:shape}

          true ->
            case fields_of_ctor(fty, cname, book) do
              {:ok, ftys} ->
                if length(xs) == length(ftys) do
                  case Enum.at(ftys, j) do
                    inner_ty when not is_nil(inner_ty) ->
                      if splittable?(inner_ty) do
                        ctx1 = bind_fields(ctx, xs, ftys)

                        with {:ok, nested} <- pair_fork(ch2, inner, inner_ty, ctx1, book),
                             {:ok, rest} <- pair_fork(ch, ps, fty, ctx, book) do
                          {:ok, nested ++ rest}
                        end
                      else
                        {:shape}
                      end

                    _ ->
                      {:shape}
                  end
                else
                  {:error, "wrong arity"}
                end

              :error ->
                {:error, @cover}
            end
        end

      _ ->
        {:shape}
    end
  end

  defp pair_fork(_, _, _, _, _), do: {:shape}

  # Fields come from the payload constructor. The protocol arm is the
  # one the run selects for this constructor, or for the field it reads.
  defp open_named({:arm, ctor, binders, body}, expected, ty, ctx, book)
       when is_binary(ctor) and is_list(binders) do
    cond do
      ctor != expected ->
        {:error, @cover}

      true ->
        case fields_of_ctor(ty, expected, book) do
          {:ok, fields} ->
            if length(binders) == length(fields) do
              {:ok, body, bind_fields(ctx, binders, fields)}
            else
              {:error, "wrong arity"}
            end

          :error ->
            {:error, @cover}
        end
    end
  end

  defp open_named(proc, _expected, _ty, ctx, _book), do: {:ok, proc, ctx}

  defp self_of(ctx) do
    Enum.find_value(ctx, fn
      {{:self, name}, _} when is_binary(name) -> name
      _ -> nil
    end)
  end

  defp call_known(name, args, ctx) do
    book = Map.get(ctx, {:__book__, :book}, [])

    case locate_session(book, name) do
      nil ->
        {:error, "unknown session #{name}"}

      {i, sess} ->
        idx = Map.get(ctx, {:__self__, :index})

        cond do
          is_integer(idx) and i > idx ->
            {:error, "session declared later"}

          length(Map.get(sess, :params, [])) != length(args) ->
            {:error, "wrong number of session arguments"}

          true ->
            :ok
        end
    end
  end

  defp args_ok(args, ctx, book) do
    Enum.reduce_while(args, :ok, fn arg, :ok ->
      case arg_ok(arg, ctx, book) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
  end

  defp arg_ok({:lit, n}, _ctx, _book) when is_integer(n) and n >= 0, do: :ok
  defp arg_ok({:lit, n}, _ctx, _book), do: {:error, "argument #{n} is not a nat"}

  defp arg_ok({:var, name}, ctx, _book) do
    source = Map.get(ctx, {:__book__, :book}, [])

    cond do
      Map.get(ctx, name) == :nat -> :ok
      run?(prepare(source), cname(name)) -> :ok
      true -> {:error, "argument #{name} is not a nat"}
    end
  end

  defp arg_ok({:suc, a}, ctx, book), do: arg_ok(a, ctx, book)

  defp arg_ok({:con, _, inner} = arg, ctx, book) do
    with :ok <- args_ok(inner, ctx, book) do
      if symbolic_arg?(arg, ctx) do
        :ok
      else
        st = elab_state(nil, nil, Map.get(ctx, {:__book__, :book}, []), %{})

        case eval_arg_exp(arg, st) do
          {:ok, {:lit, _}} -> :ok
          {:error, msg} -> {:error, msg}
          _ -> {:error, "argument #{show_arg(arg)} is not a nat"}
        end
      end
    end
  end

  defp arg_ok(other, _ctx, _book), do: {:error, "argument #{show_arg(other)} is not a nat"}

  defp symbolic_arg?({:var, name}, ctx), do: Map.get(ctx, name) == :nat
  defp symbolic_arg?({:suc, a}, ctx), do: symbolic_arg?(a, ctx)
  defp symbolic_arg?({:con, _, args}, ctx), do: Enum.any?(args, &symbolic_arg?(&1, ctx))
  defp symbolic_arg?(_, _), do: false

  defp guard(ctx) do
    Map.new(ctx, fn
      {{:sess, name}, _} -> {{:sess, name}, :guarded}
      {{:self, name}, _} -> {{:self, name}, :guarded}
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
    Enum.reduce_while(arms, :ok, fn arm, :ok ->
      case proc_ok(arm_body(arm), ctx) do
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
  defp keep({:no, _, _, _, _} = no), do: no
  defp keep({:error, _} = err), do: err
  defp keep({:error, _, _} = err), do: err

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
    if Enum.any?(arms, &(match?({:arm, _, _, _}, &1) or match?({:prod, _, _}, &1))) do
      "match #{name} #{Enum.map_join(arms, " ", &show_arm/1)}"
    else
      "match #{name} #{Enum.map_join(arms, " ", &paren_proc/1)}"
    end
  end

  def show_proc({:rec, name, body}), do: "rec #{name}. #{show_proc(body)}"
  def show_proc({:call, name}), do: "#{name}"

  defp show_arm({:arm, c, [], p}), do: "| #{c} => #{paren_proc(p)}"

  defp show_arm({:arm, c, xs, p}) do
    "| #{c} #{Enum.map_join(xs, " ", &to_string/1)} => #{paren_proc(p)}"
  end

  defp show_arm({:prod, {:pair, names}, p}) do
    "| (#{Enum.map_join(names, ", ", &to_string/1)}) => #{paren_proc(p)}"
  end

  defp show_arm({:prod, {:rec, bs}, p}) do
    inner = Enum.map_join(bs, ", ", fn {field, binder} -> "#{field} = #{binder}" end)
    "| {#{inner}} => #{paren_proc(p)}"
  end

  defp show_arm(p), do: paren_proc(p)

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

  def show_proto({:sjump, target, args}) do
    name =
      case target do
        {:dual, n} -> n
        n -> n
      end

    case args do
      [] -> "#{name}"
      _ -> "#{name} #{Enum.map_join(args, " ", &show_ix/1)}"
    end
  end

  def show_proto({:case, scrut, arms}) do
    body = Enum.map_join(arms, " ", fn {c, s} -> "| #{c} => #{show_proto(s)}" end)
    "case #{show_scrut(scrut)} #{body}"
  end

  def show_proto({:sess, name, args}) do
    case args do
      [] -> name
      _ -> "#{name} #{Enum.map_join(args, " ", &show_arg/1)}"
    end
  end

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
  defp paren_proto({:sjump, _, _} = s), do: show_proto(s)
  defp paren_proto({:sess, _, _} = s), do: show_proto(s)
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
    %{decls: data_entries(book), runs: eval_book(book), entries: book}
  end

  @doc false
  def run_fragment(book, names) when is_list(names) do
    prepared = if is_list(book), do: prepare(book), else: book
    defs = run_defs(prepared)
    keep = close_names(names, defs, MapSet.new())
    runs = Enum.filter(defs, &MapSet.member?(keep, &1.name))
    decls = if runs == [], do: [], else: decls(prepared)
    %{decls: decls, runs: runs}
  end

  defp close_names([], _defs, acc), do: acc

  defp close_names([name | rest], defs, acc) do
    if MapSet.member?(acc, name) do
      close_names(rest, defs, acc)
    else
      case Enum.find_index(defs, &(&1.name == name)) do
        nil ->
          close_names(rest, defs, acc)

        i ->
          defn = Enum.at(defs, i)
          prefix = defs |> Enum.take(i) |> MapSet.new(& &1.name)

          more =
            defn.body
            |> called_defs()
            |> Enum.filter(&MapSet.member?(prefix, &1))

          close_names(more ++ rest, defs, MapSet.put(acc, name))
      end
    end
  end

  defp called_defs({:def, name}) when is_binary(name), do: [name]

  defp called_defs({:app, _, _} = term) do
    case spine_term(term, []) do
      {:ok, name, args} -> [name | Enum.flat_map(args, &called_defs/1)]
      :error -> []
    end
  end

  defp called_defs(term) when is_tuple(term),
    do: term |> Tuple.to_list() |> Enum.flat_map(&called_defs/1)

  defp called_defs(term) when is_list(term), do: Enum.flat_map(term, &called_defs/1)
  defp called_defs(_), do: []

  defp decls(%{decls: decls}), do: decls
  defp decls(book) when is_list(book), do: book

  defp runs(%{runs: runs}), do: runs
  defp runs(_), do: []

  # A jump at the head is one unfolding of that session. The body is
  # the declaration, opened at these arguments. A jump that opens to a
  # jump has no action under it.
  defp expand_head({:sjump, target, args}, book) do
    case reopen(target, args, book) do
      {:ok, {:sjump, _, _}} -> {:error, "unguarded session call"}
      other -> other
    end
  end

  defp expand_head(proto, _book), do: {:ok, proto}

  defp reopen(name, args, book) when is_binary(name) do
    open_jump(name, args, source_entries(book))
  end

  defp reopen({:dual, name}, args, book) when is_binary(name) do
    case open_jump(name, args, source_entries(book)) do
      {:ok, proto} -> {:ok, dual(proto)}
      err -> err
    end
  end

  defp reopen(_, _, _), do: {:error, "unknown session"}

  defp open_jump(name, args, book) do
    case locate_session(book, name) do
      nil ->
        {:error, "unknown session #{name}"}

      {i, sess} ->
        params = Map.get(sess, :params, [])

        if length(params) != length(args) do
          {:error, "wrong number of session arguments"}
        else
          subst = Map.new(Enum.zip(params, args))
          elab(sess.proto, elab_state(name, i, book, subst))
        end
    end
  end

  defp source_entries(%{entries: entries}) when is_list(entries), do: entries
  defp source_entries(book) when is_list(book), do: book
  defp source_entries(_), do: []

  # The same process, and a protocol of the same shape, whose evidence
  # bounds and jump arguments have not decreased. A vector length is
  # part of the shape, so a changed length is a different protocol.
  defp absorb_loop?(seen, proc, pkey, proto) do
    case shape_lits(proto) do
      {:ok, shape, lits} ->
        Enum.any?(seen, fn
          {^proc, ^pkey, old, _} ->
            case shape_lits(old) do
              {:ok, ^shape, prev} ->
                length(prev) == length(lits) and
                  Enum.all?(Enum.zip(prev, lits), fn {a, b} -> b >= a end)

              _ ->
                false
            end

          _ ->
            false
        end)

      _ ->
        false
    end
  end

  defp shape_lits(proto) do
    case shape_go(proto, []) do
      {:ok, shape, lits} -> {:ok, shape, Enum.reverse(lits)}
      :error -> :error
    end
  end

  defp shape_go(:end, lits), do: {:ok, :end, lits}

  defp shape_go({:send, ty, s}, lits) do
    with {:ok, s, lits} <- shape_go(s, lits), do: {:ok, {:send, ty, s}, lits}
  end

  defp shape_go({:recv, ty, s}, lits) do
    with {:ok, s, lits} <- shape_go(s, lits), do: {:ok, {:recv, ty, s}, lits}
  end

  defp shape_go({:dsend, name, ty, s}, lits) do
    with {:ok, s, lits} <- shape_go(s, lits), do: {:ok, {:dsend, name, ty, s}, lits}
  end

  defp shape_go({:drecv, name, ty, s}, lits) do
    with {:ok, s, lits} <- shape_go(s, lits), do: {:ok, {:drecv, name, ty, s}, lits}
  end

  defp shape_go({:esend, name, {:lit, n}, s}, lits) when is_integer(n) do
    with {:ok, s, lits} <- shape_go(s, [n | lits]), do: {:ok, {:esend, name, :hole, s}, lits}
  end

  defp shape_go({:esend, name, e, s}, lits) do
    with {:ok, s, lits} <- shape_go(s, lits), do: {:ok, {:esend, name, e, s}, lits}
  end

  defp shape_go({:erecv, name, {:lit, n}, s}, lits) when is_integer(n) do
    with {:ok, s, lits} <- shape_go(s, [n | lits]), do: {:ok, {:erecv, name, :hole, s}, lits}
  end

  defp shape_go({:erecv, name, e, s}, lits) do
    with {:ok, s, lits} <- shape_go(s, lits), do: {:ok, {:erecv, name, e, s}, lits}
  end

  defp shape_go({:isend, name, s, t}, lits) do
    with {:ok, s, lits} <- shape_go(s, lits),
         {:ok, t, lits} <- shape_go(t, lits) do
      {:ok, {:isend, name, s, t}, lits}
    end
  end

  defp shape_go({:irecv, name, s, t}, lits) do
    with {:ok, s, lits} <- shape_go(s, lits),
         {:ok, t, lits} <- shape_go(t, lits) do
      {:ok, {:irecv, name, s, t}, lits}
    end
  end

  defp shape_go({:choose, s, t}, lits) do
    with {:ok, s, lits} <- shape_go(s, lits),
         {:ok, t, lits} <- shape_go(t, lits) do
      {:ok, {:choose, s, t}, lits}
    end
  end

  defp shape_go({:branch, s, t}, lits) do
    with {:ok, s, lits} <- shape_go(s, lits),
         {:ok, t, lits} <- shape_go(t, lits) do
      {:ok, {:branch, s, t}, lits}
    end
  end

  defp shape_go({:rec, name, body}, lits) do
    with {:ok, body, lits} <- shape_go(body, lits), do: {:ok, {:rec, name, body}, lits}
  end

  defp shape_go({:svar, name}, lits), do: {:ok, {:svar, name}, lits}

  defp shape_go({:sjump, target, args}, lits) do
    {holes, nums} = hole_jump_args(args)
    {:ok, {:sjump, target, holes}, nums ++ lits}
  end

  defp shape_go({:case, scrut, arms}, lits) do
    Enum.reduce_while(arms, {:ok, [], lits}, fn {c, s}, {:ok, acc, lits} ->
      case shape_go(s, lits) do
        {:ok, shaped, lits} -> {:cont, {:ok, acc ++ [{c, shaped}], lits}}
        :error -> {:halt, :error}
      end
    end)
    |> case do
      {:ok, shaped, lits} -> {:ok, {:case, scrut, shaped}, lits}
      :error -> :error
    end
  end

  defp shape_go(_, _), do: :error

  defp hole_jump_args(args) do
    Enum.map_reduce(args, [], fn
      {:lit, n}, nums when is_integer(n) -> {:hole, nums ++ [n]}
      other, nums -> {other, nums}
    end)
  end

  defp locate_session(book, name) when is_list(book) do
    case Enum.find_index(book, &(Map.get(&1, :kind) == :session and &1.name == name)) do
      nil -> nil
      i -> {i, Enum.at(book, i)}
    end
  end

  defp locate_session(_, _), do: nil

  defp session_index(book, name) do
    case locate_session(book, name) do
      {i, _} -> i
      nil -> nil
    end
  end

  defp elab_state(self, index, book, subst) do
    %{
      book: book,
      self: self,
      index: index,
      guarded: false,
      subst: subst,
      prepared: prepare(book)
    }
  end

  defp arity_ok(sess, exps) do
    if length(Map.get(sess, :params, [])) == length(exps) do
      :ok
    else
      {:error, "wrong number of session arguments"}
    end
  end

  defp elab(:end, _st), do: {:ok, :end}

  defp elab({:send, ty, s}, st) do
    with {:ok, s} <- elab(s, %{st | guarded: true}) do
      {:ok, {:send, subst_ty(ty, st.subst), s}}
    end
  end

  defp elab({:recv, ty, s}, st) do
    with {:ok, s} <- elab(s, %{st | guarded: true}) do
      {:ok, {:recv, subst_ty(ty, st.subst), s}}
    end
  end

  defp elab({:dsend, name, ty, s}, st) do
    ty = subst_ty(ty, st.subst)

    with {:ok, s} <- elab(s, %{bind_st(st, name, ty) | guarded: true}) do
      {:ok, {:dsend, name, ty, s}}
    end
  end

  defp elab({:drecv, name, ty, s}, st) do
    ty = subst_ty(ty, st.subst)

    with {:ok, s} <- elab(s, %{bind_st(st, name, ty) | guarded: true}) do
      {:ok, {:drecv, name, ty, s}}
    end
  end

  defp elab({:esend, name, e, s}, st) do
    with {:ok, s} <- elab(s, %{st | guarded: true}) do
      {:ok, {:esend, name, subst_ix(e, st.subst), s}}
    end
  end

  defp elab({:erecv, name, e, s}, st) do
    with {:ok, s} <- elab(s, %{st | guarded: true}) do
      {:ok, {:erecv, name, subst_ix(e, st.subst), s}}
    end
  end

  defp elab({:isend, name, s, t}, st) do
    st1 = %{shadow_st(st, name) | guarded: true}

    with {:ok, s} <- elab(s, st1),
         {:ok, t} <- elab(t, st1) do
      {:ok, {:isend, name, s, t}}
    end
  end

  defp elab({:irecv, name, s, t}, st) do
    st1 = %{shadow_st(st, name) | guarded: true}

    with {:ok, s} <- elab(s, st1),
         {:ok, t} <- elab(t, st1) do
      {:ok, {:irecv, name, s, t}}
    end
  end

  defp elab({:choose, s, t}, st) do
    st1 = %{st | guarded: true}

    with {:ok, s} <- elab(s, st1),
         {:ok, t} <- elab(t, st1) do
      {:ok, {:choose, s, t}}
    end
  end

  defp elab({:branch, s, t}, st) do
    st1 = %{st | guarded: true}

    with {:ok, s} <- elab(s, st1),
         {:ok, t} <- elab(t, st1) do
      {:ok, {:branch, s, t}}
    end
  end

  # `rec` does not guard a session call, and it does not clear a guard
  # an action outside it already gave.
  defp elab({:rec, name, body}, st) do
    with {:ok, body} <- elab(body, st) do
      {:ok, {:rec, name, body}}
    end
  end

  defp elab({:svar, name}, _st), do: {:ok, {:svar, name}}
  defp elab({:sjump, _, _} = jump, _st), do: {:ok, jump}

  defp elab({:sess, name, args}, st) when is_binary(name) do
    elab_sess(name, args, st)
  end

  defp elab({:dual, ref}, st) do
    elab_dual(ref, st)
  end

  defp elab({:case, scrut, arms}, st) do
    Enum.reduce_while(arms, {:ok, []}, fn {c, s}, {:ok, acc} ->
      case elab(s, st) do
        {:ok, body} -> {:cont, {:ok, acc ++ [{c, body}]}}
        err -> {:halt, err}
      end
    end)
    |> case do
      {:ok, arms} -> {:ok, {:case, scrut, arms}}
      err -> err
    end
  end

  defp elab(_, _), do: {:error, "ill-formed protocol"}

  defp elab_dual(name, st) when is_binary(name) do
    case locate_session(st.book, name) do
      nil ->
        {:error, "unknown session #{name}"}

      {i, sess} ->
        with {:ok, proto} <- elab(sess.proto, elab_state(name, i, st.book, %{})) do
          {:ok, dual(proto)}
        end
    end
  end

  defp elab_dual({:sess, name, args}, st) do
    case open_applied(st.book, name, subst_args(args, st.subst)) do
      {:ok, %{proto: proto}} -> {:ok, dual(proto)}
      {:error, _} = err -> err
    end
  end

  defp elab_dual(_, _), do: {:error, "unknown session"}

  defp elab_sess(name, args, st) do
    with {:ok, exps} <- eval_arg_list(args, st) do
      cond do
        name == st.self and not st.guarded ->
          {:error, "unguarded session call"}

        name == st.self ->
          {:ok, {:sjump, name, exps}}

        true ->
          case locate_session(st.book, name) do
            nil ->
              {:error, "unknown session #{name}"}

            {i, _} when is_integer(st.index) and i > st.index ->
              {:error, "session declared later"}

            {i, sess} ->
              with :ok <- arity_ok(sess, exps) do
                subst = Map.new(Enum.zip(Map.get(sess, :params, []), exps))
                elab(sess.proto, elab_state(sess.name, i, st.book, subst))
              end
          end
      end
    end
  end

  defp bind_st(st, name, :nat), do: %{st | subst: Map.put(st.subst, name, {:var, name})}
  defp bind_st(st, name, _), do: shadow_st(st, name)
  defp shadow_st(st, name), do: %{st | subst: Map.delete(st.subst, name)}

  defp subst_args(args, subst) do
    Enum.map(args, fn
      {:var, name} -> Map.get(subst, name, {:var, name})
      {:suc, a} -> {:suc, subst_one(a, subst)}
      {:con, name, inner} -> {:con, name, subst_args(inner, subst)}
      other -> other
    end)
  end

  defp subst_one(arg, subst), do: hd(subst_args([arg], subst))

  defp subst_ty(ty, _subst) when ty in [:nat, :bit, :unit], do: ty
  defp subst_ty({:pair, a, b}, subst), do: {:pair, subst_ty(a, subst), subst_ty(b, subst)}

  defp subst_ty({:rec, fields}, subst) when is_list(fields) do
    {:rec, Enum.map(fields, fn {name, ty} -> {name, subst_ty(ty, subst)} end)}
  end

  defp subst_ty({:vec, elem, e}, subst), do: {:vec, subst_ty(elem, subst), subst_ix(e, subst)}

  defp subst_ty({:dat, name, args}, subst) do
    {:dat, name, Enum.map(args, &subst_ty(&1, subst))}
  end

  defp subst_ty(ty, _subst), do: ty

  defp subst_ix({:lit, n}, _subst), do: {:lit, n}

  defp subst_ix({:var, name}, subst) do
    case Map.get(subst, name) do
      nil -> {:var, name}
      exp -> exp
    end
  end

  defp subst_ix(e, _subst), do: e

  defp eval_arg_list(args, st) do
    Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, acc} ->
      case eval_arg_exp(arg, st) do
        {:ok, exp} -> {:cont, {:ok, acc ++ [exp]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp eval_arg_exp({:lit, n}, _st) when is_integer(n) and n >= 0, do: {:ok, {:lit, n}}
  defp eval_arg_exp({:lit, n}, _st), do: {:error, "argument #{n} is not a nat"}

  defp eval_arg_exp({:var, name}, st) do
    case Map.get(st.subst, name) do
      {:lit, n} ->
        {:ok, {:lit, n}}

      {:var, v} ->
        {:ok, {:var, v}}

      nil ->
        case reduce({:var, name}, %{}, st.prepared) do
          {:ok, {:nat, n}} when is_integer(n) and n >= 0 -> {:ok, {:lit, n}}
          {:error, msg} -> {:error, "argument #{name}: #{msg}"}
          _ -> {:error, "argument #{name} is not a nat"}
        end
    end
  end

  defp eval_arg_exp({:suc, a} = arg, st) do
    case eval_arg_exp(a, st) do
      {:ok, {:lit, n}} -> {:ok, {:lit, n + 1}}
      {:ok, _} -> {:error, "argument #{show_arg(arg)} is not a nat"}
      {:error, _} = err -> err
    end
  end

  defp eval_arg_exp({:con, name, args} = arg, st) do
    with {:ok, exps} <- eval_arg_list(args, st) do
      if Enum.all?(exps, &match?({:lit, _}, &1)) do
        term = {:con, cname(name), Enum.map(exps, fn {:lit, n} -> {:nat, n} end)}

        case reduce(term, %{}, st.prepared) do
          {:ok, {:nat, n}} when is_integer(n) and n >= 0 ->
            {:ok, {:lit, n}}

          {:error, msg} ->
            {:error, "argument #{show_arg(arg)}: #{msg}"}

          _ ->
            {:error, "argument #{show_arg(arg)} is not a nat"}
        end
      else
        {:error, "argument #{show_arg(arg)} is not a nat"}
      end
    end
  end

  defp eval_arg_exp(other, _st), do: {:error, "argument #{show_arg(other)} is not a nat"}

  defp show_arg({:lit, n}), do: "#{n}"
  defp show_arg({:var, name}), do: "#{name}"
  defp show_arg({:suc, a}), do: "(suc #{show_arg(a)})"
  defp show_arg({:con, name, []}), do: "#{name}"

  defp show_arg({:con, name, args}) do
    "(#{name} #{Enum.map_join(args, " ", &show_arg/1)})"
  end

  defp show_arg(other), do: "#{other}"

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
              :repr,
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

  @doc false
  def run_name?(book, name) when is_list(book), do: run_name?(prepare(book), name)
  def run_name?(%{decls: _, runs: _} = book, name), do: run?(book, cname(name))

  @doc false
  def nullary_ctor_name?(book, name) when is_list(book),
    do: nullary_ctor_name?(prepare(book), name)

  def nullary_ctor_name?(%{decls: _, runs: _} = book, name), do: nullary_name?(book, name)

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

  @doc false
  def eval_run(name, runtime_args, book) when is_list(book) do
    eval_run(name, runtime_args, prepare(book))
  end

  def eval_run(name, runtime_args, %{decls: _, runs: _} = book) when is_list(runtime_args) do
    defs = run_defs(book)

    case Enum.find_index(defs, &(&1.name == name)) do
      nil ->
        {:run, name, runtime_args}

      i ->
        {doms, _cod} = pi_chain(Enum.at(defs, i).type, [])

        if length(doms) != length(runtime_args) do
          {:run, name, runtime_args}
        else
          case read_args(doms, runtime_args, book) do
            {:ok, args} ->
              case eval_call(name, args, book) do
                {:ok, v} when v != :miss -> runtime(v)
                _ -> {:run, name, runtime_args}
              end

            :error ->
              {:run, name, runtime_args}
          end
        end
    end
  end

  defp read_args(doms, values, book) do
    Enum.reduce_while(Enum.zip(doms, values), {:ok, []}, fn {dom, value}, {:ok, acc} ->
      case result_ty(dom, book) do
        {:ok, ty} ->
          case read_pay(ty, value, book) do
            {:ok, arg} -> {:cont, {:ok, acc ++ [arg]}}
            :error -> {:halt, :error}
          end

        :error ->
          {:halt, :error}
      end
    end)
  end

  # The parameter type chooses the reading. A two-element tuple is a pair
  # or a one-field constructor, and those are different types.
  defp read_pay(:nat, n, _book) when is_integer(n) and n >= 0, do: {:ok, {:nat, n}}
  defp read_pay(:bit, bit, _book) when bit in [:b0, :b1], do: {:ok, bit}
  defp read_pay(:unit, :tt, _book), do: {:ok, :tt}

  defp read_pay({:pair, a, b}, {x, y}, book) do
    with {:ok, x} <- read_pay(a, x, book),
         {:ok, y} <- read_pay(b, y, book) do
      {:ok, {:tup, x, y}}
    end
  end

  defp read_pay({:dat, dname, _args}, value, book) when is_atom(value) do
    case find_decl(book, dname) do
      nil ->
        :error

      d ->
        case ctor_fields(d, Atom.to_string(value)) do
          {:ok, []} -> {:ok, {:con, Atom.to_string(value), []}}
          _ -> :error
        end
    end
  end

  defp read_pay({:dat, dname, args}, value, book)
       when is_tuple(value) and tuple_size(value) >= 1 do
    [tag | fields] = Tuple.to_list(value)

    if is_atom(tag) do
      label = Atom.to_string(tag)

      case find_decl(book, dname) do
        nil ->
          :error

        d ->
          case ctor_fields(d, label) do
            {:ok, tmpls} when length(tmpls) == length(fields) ->
              read_ctor_fields(label, tmpls, fields, dname, args, book, [])

            _ ->
              :error
          end
      end
    else
      :error
    end
  end

  defp read_pay(_, _, _), do: :error

  defp read_ctor_fields(tag, [], [], _dname, _args, _book, acc), do: {:ok, {:con, tag, acc}}

  defp read_ctor_fields(tag, [tmpl | tmpls], [value | values], dname, args, book, acc) do
    case read_pay(inst_field(tmpl, dname, args), value, book) do
      {:ok, field} -> read_ctor_fields(tag, tmpls, values, dname, args, book, acc ++ [field])
      :error -> :error
    end
  end

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

  defp eval_def(%{name: name, body: body}, args, prefix, defs, book) do
    push_self(name)

    try do
      case drop_lams(body, length(args)) do
        {:ok, core} ->
          if calls_out?(core, prefix, defs) do
            {:error, cycle_reason(name, core)}
          else
            ev(core, Enum.reverse(args), prefix, defs, book)
          end

        :error ->
          {:ok, :miss}
      end
    after
      pop_self()
    end
  end

  defp push_self(name), do: Process.put(@run_key, [name | Process.get(@run_key, [])])

  defp pop_self do
    case Process.get(@run_key, []) do
      [_ | rest] -> Process.put(@run_key, rest)
      _ -> Process.delete(@run_key)
    end
  end

  defp current_self do
    case Process.get(@run_key, []) do
      [name | _] -> name
      _ -> nil
    end
  end

  defp cycle_reason(self, core) do
    if call_of?(core, self),
      do: "run definition calls itself",
      else: "run definition declared later"
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
            {:error,
             if(name == current_self(),
               do: "run definition calls itself",
               else: "run definition declared later"
             )}

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

  defp call_of?(term, name) do
    case term do
      {:su, t} ->
        call_of?(t, name)

      {:ann, t, _} ->
        call_of?(t, name)

      {:pair, a, b} ->
        call_of?(a, name) or call_of?(b, name)

      {:mnat, e, _motive, z, s} ->
        call_of?(e, name) or call_of?(z, name) or call_of?(s, name)

      {:mnat, e, _x, _motive, z, _y, s} ->
        call_of?(e, name) or call_of?(z, name) or call_of?(s, name)

      {:mdata, e, motive, branches} when is_list(branches) ->
        call_of?(e, name) or call_of?(motive, name) or
          Enum.any?(branches, &branch_call?(&1, name))

      {:mdata, e, _x, motive, branches} when is_list(branches) ->
        call_of?(e, name) or call_of?(motive, name) or
          Enum.any?(branches, &branch_call?(&1, name))

      {:app, _, _} ->
        case spine_term(term, []) do
          {:ok, n, args} -> n == name or Enum.any?(args, &call_of?(&1, name))
          :error -> false
        end

      {:def, n} ->
        n == name

      _ ->
        false
    end
  end

  defp branch_call?(branch, name) do
    case branch_shape(branch) do
      {_, _, body} -> call_of?(body, name)
      _ -> false
    end
  end

  @doc false
  def step_at(nil), do: nil
  def step_at(%{at: at}), do: at
  def step_at(_), do: nil

  @doc false
  def step_down(nil, _), do: nil
  def step_down(%{down: ds}, i) when is_list(ds), do: Enum.at(ds, i)
  def step_down(_, _), do: nil

  @doc false
  def step_proc(:done), do: "done"
  def step_proc(:stop), do: "stop"
  def step_proc({:put, _ty, val, _}), do: "put #{show_val(val)}"
  def step_proc({:get, ty, :_, _}), do: "get #{show_pay_atom(ty)}"
  def step_proc({:get, ty, name, _}), do: "get (#{name} : #{show_pay_atom(ty)})"
  def step_proc({:pick0, _}), do: "pick0"
  def step_proc({:pick1, _}), do: "pick1"
  def step_proc({:cover, _, _}), do: "cover"
  def step_proc({:iget, name, _, _}), do: "get (#{name} : Bit)"
  def step_proc({:match, name, _}), do: "match #{name}"
  def step_proc({:rec, name, _}), do: "rec #{name}"
  def step_proc({:call, name}), do: "#{name}"
  def step_proc(other), do: inspect(other)

  @doc false
  def step_proto(:end), do: "end"
  def step_proto({:send, ty, _}), do: "send #{show_pay_atom(ty)}"
  def step_proto({:recv, ty, _}), do: "recv #{show_pay_atom(ty)}"
  def step_proto({:dsend, name, ty, _}), do: "send (#{name} : #{show_pay(ty)})"
  def step_proto({:drecv, name, ty, _}), do: "recv (#{name} : #{show_pay(ty)})"
  def step_proto({:esend, name, e, _}), do: "send (#{name} : Nat) {#{name} ≤ #{show_ix(e)}}"
  def step_proto({:erecv, name, e, _}), do: "recv (#{name} : Nat) {#{name} ≤ #{show_ix(e)}}"
  def step_proto({:isend, name, _, _}), do: "send (#{name} : Bit)"
  def step_proto({:irecv, name, _, _}), do: "recv (#{name} : Bit)"
  def step_proto({:choose, _, _}), do: "choose"
  def step_proto({:branch, _, _}), do: "branch"
  def step_proto({:rec, name, _}), do: "rec #{name}"
  def step_proto({:svar, name}), do: "#{name}"
  def step_proto({:sjump, _, _} = p), do: show_proto(p)
  def step_proto({:sess, _, _} = p), do: show_proto(p)
  def step_proto({:case, {:name, n}, _}), do: "case #{n}"
  def step_proto({:case, {:run, f, n}, _}), do: "case (#{f} #{n})"
  def step_proto({:case, _, _}), do: "case"
  def step_proto(other), do: inspect(other)

  @doc false
  def show_value(val), do: show_val(val)

  @doc false
  def explain_put(val, ty, ctx, book) when is_list(book),
    do: explain_put(val, ty, ctx, prepare(book))

  def explain_put(val, ty, ctx, %{decls: _, runs: _} = book) do
    explain_no(:unknown, val, ty, ctx, book)
  end

  defp explain_no(ty, val, expected, ctx, book) do
    if ty == :unknown or ty == expected do
      explain_val(val, expected, ctx, book)
    else
      nil
    end
  end

  defp explain_val(val, expected, ctx, book) do
    cond do
      open_run_arg?(val, ctx, book) ->
        "argument is not a value"

      true ->
        case reduce(val, ctx, book) do
          {:error, msg} ->
            rewrite_run(msg)

          {:ok, v} ->
            cond do
              reason = fragment_reason(val, v, book) ->
                reason

              v != :miss and computed_send?(val, ctx, book) and
                  fits(v, expected, ctx, book) == :no ->
                "computed value #{show_val(v)} does not inhabit #{show_pay(expected)}"

              true ->
                nil
            end
        end
    end
  end

  defp rewrite_run("recursive run definition"), do: "run definition calls itself"
  defp rewrite_run(msg), do: msg

  defp bound_reason(val, got, bound, book) do
    shown = if got == :miss, do: show_val(val), else: show_val(got)
    kind = if computed_send?(val, %{}, book), do: "computed value", else: "value"
    "#{kind} #{shown} misses bound #{show_bound(bound)}"
  end

  defp show_bound(nil), do: "≤ ?"
  defp show_bound(e), do: "≤ #{show_ix(e)}"

  defp open_run_arg?({:con, name, args}, ctx, book) do
    run?(book, name) and not Enum.all?(args, &closed?(&1, ctx, book))
  end

  defp open_run_arg?(_, _, _), do: false

  defp computed_send?({:con, name, _}, ctx, book) do
    run?(book, name) and not Map.has_key?(ctx, name)
  end

  defp computed_send?({:var, name}, ctx, book) do
    not Map.has_key?(ctx, name) and not nullary_name?(book, name) and run?(book, cname(name))
  end

  defp computed_send?(_, _, _), do: false

  defp fragment_reason(val, v, book) do
    case run_apply(val, book) do
      nil ->
        nil

      {name, args} ->
        case find_run(book, name) do
          nil ->
            nil

          %{body: body} ->
            case drop_lams(body, length(args)) do
              :error ->
                "outside the computed fragment: partial application"

              {:ok, core} ->
                frag = if v == :miss, do: fragment_term(core), else: nil

                cond do
                  match?({:lam, _, _, _, _}, core) ->
                    "outside the computed fragment: partial application"

                  frag == :let ->
                    "outside the computed fragment: let"

                  frag == :lam ->
                    "outside the computed fragment: λ"

                  record_arg?(args) and (v == :miss or match?({:rec, _}, v)) ->
                    "outside the computed fragment: record"

                  vector_arg?(args) and (v == :miss or match?({:rep, _, _}, v)) ->
                    "outside the computed fragment: vector"

                  true ->
                    nil
                end
            end
        end
    end
  end

  defp run_apply({:con, name, args}, book) do
    if run?(book, name), do: {cname(name), args}, else: nil
  end

  defp run_apply({:var, name}, book) do
    if run?(book, cname(name)) and not nullary_name?(book, name), do: {cname(name), []}, else: nil
  end

  defp run_apply(_, _), do: nil

  defp find_run(book, name) do
    Enum.find(run_defs(book), &(&1.name == name))
  end

  defp record_arg?(args), do: Enum.any?(args, &match?({:rec, _}, &1))
  defp vector_arg?(args), do: Enum.any?(args, &match?({:rep, _, _}, &1))

  defp fragment_term({:letp, _, _}), do: :let
  defp fragment_term({:lam, _, _, _, _}), do: :lam
  defp fragment_term({:ann, t, _}), do: fragment_term(t)
  defp fragment_term({:su, t}), do: fragment_term(t)
  defp fragment_term({:pair, a, b}), do: fragment_term(a) || fragment_term(b)

  defp fragment_term({:app, f, a}) do
    fragment_term(f) || fragment_term(a)
  end

  defp fragment_term({:mnat, e, _, z, s}) do
    fragment_term(e) || fragment_term(z) || fragment_term(s)
  end

  defp fragment_term({:mnat, e, _, _, z, _, s}) do
    fragment_term(e) || fragment_term(z) || fragment_term(s)
  end

  defp fragment_term({:mdata, e, motive, branches}) when is_list(branches) do
    fragment_term(e) || fragment_term(motive) ||
      Enum.find_value(branches, fn b ->
        case branch_shape(b) do
          {_, _, body} -> fragment_term(body)
          _ -> nil
        end
      end)
  end

  defp fragment_term(_), do: nil
end

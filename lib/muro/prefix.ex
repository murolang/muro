defmodule Muro.Prefix do
  @moduledoc false

  # The Elixir mirror of `Leg` and `accept` in `agda/Muro/Prefix.agda`
  # for `end`, `send`, `recv`, `choose`, and `branch`. Recursion, a
  # named continuation, a dependent payload, an evidence bound, an
  # indexed bit, a `case` on the constructor just exchanged, and the
  # numeric `at` of the C stepper are decided here. They are not that
  # theorem. A `case` on a run is refused.

  alias Muro.{Check, Print, Session}
  alias Muro.Emit.C.Session, as: Stepper

  @doc false
  def judge(book, %{name: name, session: use, at: at, moves: moves, loc: loc} = d)
      when is_list(book) do
    case global_use(book, use) do
      %{} = chor ->
        judge_global(book, chor, d)

      nil ->
        case Enum.find(moves, &match?({:global, _, _, _}, &1)) do
          nil -> judge_session(book, name, use, at, moves, loc)
          move -> {:error, blamed(move_loc(move), name, "#{show_use(use)} is not a choreography")}
        end
    end
  end

  # A name that is a session stays a session. A name that is only a
  # choreography is the global type.
  defp global_use(book, use) when is_binary(use) do
    if decl(book, use) do
      nil
    else
      Enum.find(book, &match?(%{kind: :choreography, name: ^use}, &1))
    end
  end

  defp global_use(_book, _use), do: nil

  # A choreography prefix is the written order (`Muro.Choreo.prefix/3`).
  # It starts at the start. A session move is not an interaction.
  defp judge_global(book, chor, %{name: name, at: at, moves: moves, loc: loc}) do
    st = %{
      name: name,
      session: chor.name,
      origin: "start",
      here: "start",
      n: 1,
      decl_loc: loc,
      move_loc: loc
    }

    if at in [:start, {:name, "start"}] do
      case Muro.Choreo.check_decl(chor, book) do
        {:error, msg} -> {:error, blamed(loc, name, "#{chor.name}: #{msg}")}
        {:ok, _lines} -> judge_global_moves(chor, moves, st)
      end
    else
      {:error, blamed(loc, name, "at #{show_at(at)} is not a position of #{chor.name}")}
    end
  end

  defp judge_global_moves(chor, moves, st) do
    case Muro.Choreo.prefix(chor.roles, chor.body, Enum.map(moves, &global_move/1)) do
      :ok ->
        :ok

      {:error, n, reason} ->
        move = Enum.at(moves, n - 1)
        blame(%{st | n: n, move_loc: move_loc(move)}, global_reason(reason, move, st))
    end
  end

  defp global_move({:global, :msg, {a, b, label, ty}, _}), do: {:msg, a, b, label, ty}
  defp global_move({:global, :pick, {p, label}, _}), do: {:pick, p, label}
  defp global_move(other), do: {:session, other}

  defp global_reason({:unknown_role, role}, _move, _st), do: "unknown role #{role}"

  defp global_reason({:not_enabled, expected, _}, move, st) do
    "not enabled at #{st.here}, expected #{expected}, wrote #{show_move(move)}"
  end

  defp show_at({:name, pos}), do: pos
  defp show_at({:num, n}), do: Integer.to_string(n)
  defp show_at(other), do: inspect(other)

  defp judge_session(book, name, use, at, moves, loc) do
    with {:ok, opened, source} <- open_prefix(book, use),
         {:ok, proto, recs, origin} <- position(book, use, opened, source, at) do
      walk(proto, recs, moves, %{
        book: book,
        name: name,
        session: show_use(use),
        origin: origin,
        here: origin,
        n: 1,
        decl_loc: loc,
        move_loc: loc,
        ctx: %{}
      })
    else
      {:error, msg} -> {:error, blamed(loc, name, msg)}
    end
  end

  defp open_prefix(book, use) do
    with {:ok, session} <- open_use(book, use),
         {:ok, source} <- source_proto(book, use) do
      {:ok, session, source}
    end
  end

  defp open_use(book, name) when is_binary(name), do: Check.open_session(book, name)

  defp open_use(book, {:sess, _, _} = use), do: Check.open_session(book, use)

  defp open_use(book, {:dual, ref}) do
    with {:ok, base} <- open_use(book, ref) do
      {:ok, %{base | proto: Session.dual(base.proto)}}
    end
  end

  defp open_use(_book, _), do: {:error, "unknown session"}

  defp source_proto(book, name) when is_binary(name) do
    case decl(book, name) do
      %{proto: proto} -> {:ok, proto}
      nil -> {:error, "unknown session #{name}"}
    end
  end

  defp source_proto(book, {:sess, name, _}) do
    case decl(book, name) do
      %{proto: proto} -> {:ok, proto}
      nil -> {:error, "unknown session #{name}"}
    end
  end

  # The declaration still names a continuation as `{:sess, _, _}`.
  # Dualising that text crashes. The position search opens the
  # continuation and dualises that. `open_use` has already refused
  # every other shape, so a missing declaration is the `nil` branch.
  defp source_proto(_book, {:dual, ref}), do: {:ok, {:dual, ref}}

  defp decl(book, name) when is_binary(name) do
    Enum.find(book, &(Map.get(&1, :kind) == :session and &1.name == name))
  end

  defp position(book, use, opened, source, at) do
    case at do
      :start ->
        {:ok, opened.proto, %{}, "start"}

      {:name, "start"} ->
        {:ok, opened.proto, %{}, "start"}

      {:name, pos} ->
        named(book, use, opened.proto, source, pos)

      {:num, n} ->
        numeric(book, use, n)
    end
  end

  defp named(book, use, elaborated, source, pos) do
    case find_rec(elaborated, pos) do
      {:ok, rec} ->
        {:ok, rec, %{}, pos}

      :no ->
        case find_call_pos(book, source, pos, MapSet.new()) do
          {:ok, proto} -> {:ok, proto, %{}, pos}
          :no -> {:error, "at #{pos} is not a position of #{show_use(use)}"}
          {:error, _} = err -> err
        end
    end
  end

  defp numeric(_book, use, n) when not is_integer(n) or n < 1 do
    {:error, "at #{n} is not a position of #{show_use(use)}"}
  end

  defp numeric(book, use, n) do
    label = show_use(use)

    case owner_of(use) do
      owner when is_binary(owner) ->
        case Stepper.positions(book) do
          {:ok, %{nodes: nodes}} ->
            case Map.get(nodes, n) do
              %{session: ^owner, proto: proto, recs: recs} ->
                {:ok, proto, recs, Integer.to_string(n)}

              _ ->
                {:error, "at #{n} is not a position of #{label}"}
            end

          {:error, _} ->
            {:error, "at #{n} is not a position of #{label}"}
        end

      _ ->
        {:error, "at #{n} is not a position of #{label}"}
    end
  end

  defp owner_of(name) when is_binary(name), do: name
  defp owner_of({:sess, name, _}) when is_binary(name), do: name
  defp owner_of(_), do: nil

  defp walk(proto, recs, moves, st) do
    case expose(bare(proto), bare_recs(recs), [], st.book, 10_000) do
      {:error, msg} ->
        {:error, blamed(st.decl_loc, st.name, msg)}

      {:ok, head, recs} ->
        case moves do
          [] ->
            :ok

          [move | rest] ->
            take(head, recs, move, rest, %{st | move_loc: move_loc(move)})
        end
    end
  end

  defp take(head, recs, move, rest, st) do
    {mdir, mshape, _, _} = move

    cond do
      dir_of(head) != nil and dir_of(head) != mdir ->
        blame(st, wrong_dir(st, head, move))

      dir_of(head) != nil and shape_of(head) != mshape ->
        blame(st, not_enabled(st, head, move))

      true ->
        step_head(head, recs, move, rest, st)
    end
  end

  defp step_head({:choose, left, _}, recs, {:send, :pick, :b0, _}, rest, st),
    do: continue(left, recs, rest, st.ctx, st)

  defp step_head({:choose, _, right}, recs, {:send, :pick, :b1, _}, rest, st),
    do: continue(right, recs, rest, st.ctx, st)

  defp step_head({:branch, left, _}, recs, {:recv, :pick, :b0, _}, rest, st),
    do: continue(left, recs, rest, st.ctx, st)

  defp step_head({:branch, _, right}, recs, {:recv, :pick, :b1, _}, rest, st),
    do: continue(right, recs, rest, st.ctx, st)

  defp step_head({:isend, _, left, _}, recs, {:send, :data, :b0, _}, rest, st),
    do: continue(left, recs, rest, st.ctx, st)

  defp step_head({:isend, _, _, right}, recs, {:send, :data, :b1, _}, rest, st),
    do: continue(right, recs, rest, st.ctx, st)

  defp step_head({:isend, _, _, _} = head, _recs, move, _rest, st),
    do: blame(st, not_enabled(st, head, move))

  defp step_head({:irecv, name, left, _}, recs, {:recv, :data, :b0, _}, rest, st),
    do: continue(left, recs, rest, bind(st.ctx, name, :bit), st)

  defp step_head({:irecv, name, _, right}, recs, {:recv, :data, :b1, _}, rest, st),
    do: continue(right, recs, rest, bind(st.ctx, name, :bit), st)

  defp step_head({:irecv, _, _, _} = head, _recs, move, _rest, st),
    do: blame(st, not_enabled(st, head, move))

  defp step_head({:send, ty, cont}, recs, {:send, :data, val, _} = move, rest, st) do
    payload(ty, val, nil, cont, recs, rest, move, {:send, ty, :end}, st)
  end

  defp step_head({:recv, ty, cont}, recs, {:recv, :data, val, _} = move, rest, st) do
    payload(ty, val, nil, cont, recs, rest, move, {:recv, ty, :end}, st)
  end

  defp step_head({:dsend, name, ty, cont}, recs, {:send, :data, val, _} = move, rest, st) do
    payload(ty, val, name, cont, recs, rest, move, {:dsend, name, ty, :end}, st)
  end

  defp step_head({:drecv, name, ty, cont}, recs, {:recv, :data, val, _} = move, rest, st) do
    payload(ty, val, name, cont, recs, rest, move, {:drecv, name, ty, :end}, st)
  end

  defp step_head(
         {:esend, name, bound, cont} = head,
         recs,
         {:send, :data, val, _} = move,
         rest,
         st
       ) do
    evidence(head, name, bound, cont, val, recs, rest, move, st)
  end

  defp step_head(
         {:erecv, name, bound, cont} = head,
         recs,
         {:recv, :data, val, _} = move,
         rest,
         st
       ) do
    evidence(head, name, bound, cont, val, recs, rest, move, st)
  end

  defp step_head(head, _recs, move, _rest, st), do: blame(st, not_enabled(st, head, move))

  defp payload(ty, val, name, cont, recs, rest, move, shown, st) do
    case unknown_ctor(val, ty, st.book) do
      {:error, msg} ->
        blame(st, msg)

      :ok ->
        if Session.inhabits?(val, ty, st.ctx, st.book) do
          after_payload(cont, name, val, ty, recs, rest, %{st | ctx: bind(st.ctx, name, ty)})
        else
          blame(st, not_enabled(st, shown, move))
        end
    end
  end

  defp evidence(head, name, bound, cont, val, recs, rest, move, st) do
    case bound_ok(bound, val) do
      :ok ->
        after_payload(cont, name, val, :nat, recs, rest, %{st | ctx: bind(st.ctx, name, :nat)})

      :miss ->
        blame(st, not_enabled(st, head, move))

      {:unknown, spell} ->
        blame(st, "bound #{spell} is not known at #{st.here}")
    end
  end

  defp after_payload(_cont, _name, _val, _ty, _recs, [], _st), do: :ok

  defp after_payload(cont, name, val, _ty, recs, rest, st) do
    case bare(cont) do
      {:case, {:run, fname, arg}, _} ->
        blame(next_st(st, rest), "case (#{fname} #{arg}) is not a prefix step")

      {:case, {:run, fname, arg, earlier}, _} when is_list(earlier) ->
        args = Enum.map_join(earlier ++ [arg], " ", &to_string/1)
        blame(next_st(st, rest), "case (#{fname} #{args}) is not a prefix step")

      {:case, {:name, scrut}, arms} ->
        if scrut == name do
          select_arm(arms, val, recs, rest, st)
        else
          blame(next_st(st, rest), "case #{scrut} is not a prefix step")
        end

      _ ->
        continue(cont, recs, rest, st.ctx, st)
    end
  end

  defp select_arm(arms, val, recs, rest, st) do
    label = ctor_spell(val)

    case Enum.find(arms, fn {ctor, _} -> ctor == label end) do
      {_, body} -> continue(body, recs, rest, st.ctx, st)
      nil -> blame(next_st(st, rest), "#{label} does not select an arm")
    end
  end

  defp continue(proto, recs, moves, ctx, st) do
    walk(proto, recs, moves, %{st | n: st.n + 1, ctx: ctx})
  end

  defp next_st(st, [move | _]) do
    %{st | n: st.n + 1, move_loc: move_loc(move)}
  end

  defp bind(ctx, name, ty) when is_atom(name), do: Map.put(ctx, name, ty)
  defp bind(ctx, _name, _ty), do: ctx

  defp bound_ok(bound, val) do
    case numeral(bound) do
      {:ok, w} ->
        case val do
          {:nat, n} when is_integer(n) and n >= 0 and n <= w -> :ok
          _ -> :miss
        end

      :no ->
        {:unknown, show_bound(bound)}
    end
  end

  defp numeral({:lit, n}) when is_integer(n) and n >= 0, do: {:ok, n}
  defp numeral(_), do: :no

  defp show_bound({:var, name}), do: to_string(name)
  defp show_bound({:lit, n}), do: to_string(n)
  defp show_bound(other), do: inspect(other)

  defp unknown_ctor(val, {:dat, dname, _} = ty, book) do
    case ctor_spell(val) do
      nil ->
        :ok

      name ->
        if ctor_of?(book, dname, name) do
          :ok
        else
          {:error, "unknown constructor #{name} of #{show_ty(ty)}"}
        end
    end
  end

  defp unknown_ctor(_val, _ty, _book), do: :ok

  defp ctor_of?(book, dname, name) do
    case Enum.find(book, &(Map.get(&1, :kind) == :data and &1.name == dname)) do
      %{ctors: ctors} -> Enum.any?(ctors, &(&1.name == name))
      nil -> false
    end
  end

  defp ctor_spell({:var, name}), do: to_string(name)
  defp ctor_spell({:con, name, _}), do: to_string(name)
  defp ctor_spell(_), do: nil

  defp dir_of({:choose, _, _}), do: :send
  defp dir_of({:branch, _, _}), do: :recv
  defp dir_of({:send, _, _}), do: :send
  defp dir_of({:recv, _, _}), do: :recv
  defp dir_of({:dsend, _, _, _}), do: :send
  defp dir_of({:drecv, _, _, _}), do: :recv
  defp dir_of({:esend, _, _, _}), do: :send
  defp dir_of({:erecv, _, _, _}), do: :recv
  defp dir_of({:isend, _, _, _}), do: :send
  defp dir_of({:irecv, _, _, _}), do: :recv
  defp dir_of(_), do: nil

  defp shape_of({:choose, _, _}), do: :pick
  defp shape_of({:branch, _, _}), do: :pick
  defp shape_of(head), do: if(dir_of(head) == nil, do: nil, else: :data)

  defp action({:choose, _, _}), do: "send pick"
  defp action({:branch, _, _}), do: "recv pick"
  defp action({:isend, _, _, _}), do: "send Bit"
  defp action({:irecv, _, _, _}), do: "recv Bit"
  defp action(:end), do: "end"
  defp action(head), do: Session.step_proto(head)

  defp wrong_dir(st, head, move) do
    "move #{st.n} has the wrong direction: expected #{action(head)}, wrote #{show_move(move)}"
  end

  defp not_enabled(st, head, move) do
    "not enabled at #{st.here}, expected #{action(head)}, wrote #{show_move(move)}"
  end

  defp show_move({:global, :msg, {a, b, label, ty}, _}),
    do: Muro.Choreo.show_message(a, b, label, ty)

  defp show_move({:global, :pick, {p, label}, _}), do: "#{p} chooses #{label}"
  defp show_move({dir, :pick, bit, _}), do: "#{dir} pick #{bit}"
  defp show_move({dir, :data, val, _}), do: "#{dir} #{Session.show_value(val)}"

  defp show_ty({:dat, name, []}), do: name

  defp show_ty({:dat, name, args}) when is_list(args) do
    name <> " " <> Enum.map_join(args, " ", &show_bound/1)
  end

  defp show_ty(ty) do
    Session.step_proto({:send, ty, :end}) |> String.replace_prefix("send ", "")
  end

  defp blame(st, detail) do
    body =
      if st.n > 1 do
        inner = String.replace_prefix(detail, "move #{st.n} ", "")
        "move #{st.n} is not a legal continuation of #{st.session} at #{st.origin}: #{inner}"
      else
        detail
      end

    {:error, blamed(st.move_loc, st.name, body)}
  end

  defp blamed(loc, name, msg), do: "#{Print.loc_prefix(loc)}#{name}: #{msg}"

  defp move_loc({_, _, _, loc}), do: loc
  defp move_loc(_), do: nil

  defp show_use(name) when is_binary(name), do: name
  defp show_use({:sess, name, []}), do: name

  defp show_use({:sess, name, args}) do
    "#{name} " <> Enum.map_join(args, " ", &show_bound/1)
  end

  defp show_use({:dual, ref}), do: "dual #{show_use(ref)}"
  defp show_use(other), do: inspect(other)

  # -- head exposure: rec, svar, and a session jump are not moves ------

  defp expose(_proto, _recs, _seen, _book, n) when n <= 0, do: {:error, "out of fuel"}

  defp expose(proto, recs, seen, book, n) do
    case bare(proto) do
      {:rec, name, body} ->
        mark = {:rec, name}

        if mark in seen do
          {:error, "unguarded rec"}
        else
          expose(body, Map.put(recs, name, body), [mark | seen], book, n - 1)
        end

      {:svar, name} ->
        mark = {:svar, name}

        cond do
          mark in seen ->
            {:error, "unguarded rec"}

          true ->
            case Map.get(recs, name) do
              nil ->
                {:error, "unknown continuation #{name}"}

              body ->
                expose(body, recs, [mark | seen], book, n - 1)
            end
        end

      {:sjump, target, args} ->
        jump(book, target, args, seen, n)

      {:sess, target, args} ->
        jump(book, target, args, seen, n)

      head ->
        {:ok, head, recs}
    end
  end

  defp jump(book, target, args, seen, n) do
    mark = {:jump, target, args}

    if mark in seen do
      {:error, "unguarded rec"}
    else
      case open_jump(book, target, args) do
        {:ok, proto} -> expose(proto, %{}, [mark | seen], book, n - 1)
        {:error, _} = err -> err
      end
    end
  end

  defp open_jump(book, target, args) do
    name = to_string(target)
    ref = if args == [], do: name, else: {:sess, name, args}

    case Check.open_session(book, ref) do
      {:ok, %{proto: proto}} -> {:ok, proto}
      {:error, _} = err -> err
    end
  end

  defp find_call_pos(book, {:dual, ref}, name, seen) do
    case reveal(book, ref, seen, 1) do
      {:ok, proto, flips} -> take_call(book, proto, name, flips)
      {:error, _} = err -> err
    end
  end

  defp find_call_pos(book, source, name, _seen) do
    take_call(book, source, name, 0)
  end

  defp take_call(book, proto, name, flips) do
    case find_call(proto, name) do
      {:ok, target, args} ->
        with {:ok, opened} <- open_jump(book, target, args) do
          {:ok, flip_opened(opened, flips)}
        end

      :no ->
        :no
    end
  end

  defp flip_opened(proto, flips) when rem(flips, 2) == 1, do: Session.dual(proto)
  defp flip_opened(proto, _flips), do: proto

  # Each `dual` flips. `dual` of a session declared `dual` cancels.
  defp reveal(book, {:dual, ref}, seen, flips) do
    reveal(book, ref, seen, flips + 1)
  end

  defp reveal(book, {:sess, name, _}, seen, flips) do
    reveal(book, name, seen, flips)
  end

  defp reveal(book, name, seen, flips) when is_binary(name) do
    if MapSet.member?(seen, name) do
      {:error, "dual cycle"}
    else
      case decl(book, name) do
        %{proto: proto} -> reveal_body(book, proto, MapSet.put(seen, name), flips)
        nil -> {:error, "unknown session #{name}"}
      end
    end
  end

  defp reveal(_book, _other, _seen, _flips), do: {:error, "unknown session"}

  defp reveal_body(book, {:dual, ref}, seen, flips) do
    reveal(book, ref, seen, flips + 1)
  end

  defp reveal_body(_book, proto, _seen, flips), do: {:ok, proto, flips}

  defp find_rec(proto, name), do: find_rec(bare(proto), to_string(name), MapSet.new())

  defp find_rec({:rec, n, body} = node, name, seen) do
    if to_string(n) == name do
      {:ok, node}
    else
      mark = {:rec, n}

      if mark in seen do
        :no
      else
        find_rec(body, name, MapSet.put(seen, mark))
      end
    end
  end

  defp find_rec({:svar, _}, _name, _seen), do: :no
  defp find_rec(:end, _name, _seen), do: :no
  defp find_rec({:send, _, cont}, name, seen), do: find_rec(cont, name, seen)
  defp find_rec({:recv, _, cont}, name, seen), do: find_rec(cont, name, seen)
  defp find_rec({:dsend, _, _, cont}, name, seen), do: find_rec(cont, name, seen)
  defp find_rec({:drecv, _, _, cont}, name, seen), do: find_rec(cont, name, seen)
  defp find_rec({:esend, _, _, cont}, name, seen), do: find_rec(cont, name, seen)
  defp find_rec({:erecv, _, _, cont}, name, seen), do: find_rec(cont, name, seen)
  defp find_rec({:isend, _, left, right}, name, seen), do: find_either(left, right, name, seen)
  defp find_rec({:irecv, _, left, right}, name, seen), do: find_either(left, right, name, seen)
  defp find_rec({:choose, left, right}, name, seen), do: find_either(left, right, name, seen)
  defp find_rec({:branch, left, right}, name, seen), do: find_either(left, right, name, seen)
  defp find_rec({:sjump, _, _}, _name, _seen), do: :no
  defp find_rec({:sess, _, _}, _name, _seen), do: :no

  defp find_rec({:case, _, arms}, name, seen) when is_list(arms) do
    Enum.find_value(arms, :no, fn {_, proto} ->
      case find_rec(proto, name, seen) do
        :no -> nil
        found -> found
      end
    end)
  end

  defp find_rec(_other, _name, _seen), do: :no

  defp find_either(left, right, name, seen) do
    case find_rec(left, name, seen) do
      :no -> find_rec(right, name, seen)
      found -> found
    end
  end

  defp find_call(proto, name), do: find_call(bare(proto), to_string(name), MapSet.new())

  defp find_call({:sess, n, args}, name, _seen) do
    if to_string(n) == name, do: {:ok, n, args}, else: :no
  end

  defp find_call({:sjump, n, args}, name, _seen) do
    if to_string(n) == name, do: {:ok, n, args}, else: :no
  end

  defp find_call({:rec, n, body}, name, seen) do
    mark = {:rec, n}

    if mark in seen do
      :no
    else
      find_call(body, name, MapSet.put(seen, mark))
    end
  end

  defp find_call({:svar, _}, _name, _seen), do: :no
  defp find_call(:end, _name, _seen), do: :no
  defp find_call({:send, _, cont}, name, seen), do: find_call(cont, name, seen)
  defp find_call({:recv, _, cont}, name, seen), do: find_call(cont, name, seen)
  defp find_call({:dsend, _, _, cont}, name, seen), do: find_call(cont, name, seen)
  defp find_call({:drecv, _, _, cont}, name, seen), do: find_call(cont, name, seen)
  defp find_call({:esend, _, _, cont}, name, seen), do: find_call(cont, name, seen)
  defp find_call({:erecv, _, _, cont}, name, seen), do: find_call(cont, name, seen)

  defp find_call({:isend, _, left, right}, name, seen),
    do: find_call_either(left, right, name, seen)

  defp find_call({:irecv, _, left, right}, name, seen),
    do: find_call_either(left, right, name, seen)

  defp find_call({:choose, left, right}, name, seen),
    do: find_call_either(left, right, name, seen)

  defp find_call({:branch, left, right}, name, seen),
    do: find_call_either(left, right, name, seen)

  defp find_call({:case, _, arms}, name, seen) when is_list(arms) do
    Enum.find_value(arms, :no, fn {_, proto} ->
      case find_call(proto, name, seen) do
        :no -> nil
        found -> found
      end
    end)
  end

  defp find_call(_other, _name, _seen), do: :no

  defp find_call_either(left, right, name, seen) do
    case find_call(left, name, seen) do
      :no -> find_call(right, name, seen)
      found -> found
    end
  end

  # The state machine inserts a step string. The checker walks the
  # protocol underneath it. A parser tuple has no step string.
  defp bare({:end, step}) when is_binary(step), do: :end
  defp bare({:send, step, ty, cont}) when is_binary(step), do: {:send, ty, bare(cont)}
  defp bare({:recv, step, ty, cont}) when is_binary(step), do: {:recv, ty, bare(cont)}

  defp bare({:dsend, step, name, ty, cont}) when is_binary(step),
    do: {:dsend, name, ty, bare(cont)}

  defp bare({:drecv, step, name, ty, cont}) when is_binary(step),
    do: {:drecv, name, ty, bare(cont)}

  defp bare({:esend, step, name, bound, cont}) when is_binary(step),
    do: {:esend, name, bound, bare(cont)}

  defp bare({:erecv, step, name, bound, cont}) when is_binary(step),
    do: {:erecv, name, bound, bare(cont)}

  defp bare({:isend, step, name, left, right}) when is_binary(step),
    do: {:isend, name, bare(left), bare(right)}

  defp bare({:irecv, step, name, left, right}) when is_binary(step),
    do: {:irecv, name, bare(left), bare(right)}

  defp bare({:choose, step, left, right}) when is_binary(step),
    do: {:choose, bare(left), bare(right)}

  defp bare({:branch, step, left, right}) when is_binary(step),
    do: {:branch, bare(left), bare(right)}

  defp bare({:rec, name, body}), do: {:rec, name, bare(body)}

  defp bare({:case, scrut, arms}) when is_list(arms) do
    {:case, scrut, Enum.map(arms, fn {ctor, proto} -> {ctor, bare(proto)} end)}
  end

  defp bare(other), do: other

  defp bare_recs(recs) when is_map(recs) do
    Map.new(recs, fn {key, proto} -> {key, bare(proto)} end)
  end

  defp bare_recs(_), do: %{}
end

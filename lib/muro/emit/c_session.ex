defmodule Muro.Emit.C.Session do
  @moduledoc """
  A session stepper for the C backend.

  The states, events, and refusals are the ones `Muro.Emit.Fsm.image/3`
  steps. The host passes a state and an event. The function returns the
  next state and the action, or refuses an event the protocol does not
  allow. It does not loop the protocol and it does not speak on a socket.
  """

  alias Muro.Emit
  alias Muro.Emit.{C, Fsm, Name}

  @cap 100_000
  @err "c:session\n"

  @doc false
  def positions(book, path \\ "prefix.muro") when is_list(book) and is_binary(path) do
    case Fsm.image(book, path, []) do
      {:ok, image} ->
        nm = %{ctors: %{}, structs: %{}, atoms: %{}, taken: MapSet.new()}
        st = plan(image, book, nm, [], [])

        if st.error do
          {:error, st.error}
        else
          {:ok, %{nodes: st.positions}}
        end

      {:error, _} = err ->
        err
    end
  end

  @doc false
  def fragments(book, path, nm, sigs, opts \\ []) when is_list(book) and is_binary(path) do
    if Enum.any?(book, &(Map.get(&1, :kind) == :session)) do
      case Fsm.image(book, path, []) do
        {:error, reason} -> {:error, @err <> reason}
        {:ok, image} -> compile(image, book, nm, sigs, opts)
      end
    else
      {:ok, "", ""}
    end
  end

  defp compile(image, book, nm, sigs, opts) do
    with :ok <- refuse_repr(image),
         :ok <- refuse_unboxed(image, book) do
      st = plan(image, book, nm, sigs, opts)
      if st.error, do: {:error, st.error}, else: {:ok, header(st), source(st)}
    end
  end

  defp refuse_repr(%{sessions: sessions, duals: duals, reprs: reprs, decls: decls}) do
    hit =
      Enum.find_value(sessions, fn sess ->
        walk_repr(sess.proto, reprs, decls, MapSet.new()) && sess
      end) ||
        Enum.find_value(duals, fn {name, {_params, proto}} ->
          if walk_repr(proto, reprs, decls, MapSet.new()) do
            Enum.find(sessions, &(&1.name == name)) ||
              %{name: name, file: "session", line: 0}
          end
        end)

    case hit do
      nil ->
        :ok

      sess ->
        type = walk_repr(sess.proto, reprs, decls, MapSet.new()) || "payload"

        {:error,
         @err <> "#{sess.file}:#{sess.line} session #{sess.name}: repr #{type} is not a C payload"}
    end
  end

  # A dual whose name is not one of the opened sessions still names the
  # type the walk found. Re-walking the session proto would drop it.
  @doc false
  def refuse_unboxed(%{sessions: sessions, duals: duals, decls: decls}, book) do
    hit =
      Enum.find_value(sessions, fn sess ->
        case walk_unboxed(sess.proto, decls, book, MapSet.new()) do
          nil -> nil
          type -> {sess, type}
        end
      end) ||
        Enum.find_value(duals, fn {name, {_params, proto}} ->
          case walk_unboxed(proto, decls, book, MapSet.new()) do
            nil ->
              nil

            type ->
              sess =
                Enum.find(sessions, &(&1.name == name)) ||
                  %{name: name, file: "session", line: 0}

              {sess, type}
          end
        end)

    case hit do
      nil ->
        :ok

      {sess, type} ->
        {:error,
         @err <>
           "#{sess.file}:#{sess.line} session #{sess.name}: unboxed #{type} is not a C payload"}
    end
  end

  defp walk_repr(proto, reprs, decls, seen) do
    case proto do
      {tag, _step, ty, cont} when tag in [:send, :recv] ->
        walk_ty(ty, reprs, decls, seen) || walk_repr(cont, reprs, decls, seen)

      {tag, _step, _name, ty, cont} when tag in [:dsend, :drecv] ->
        walk_ty(ty, reprs, decls, seen) || walk_repr(cont, reprs, decls, seen)

      {tag, _step, _name, _bound, cont} when tag in [:esend, :erecv] ->
        nat_repr(reprs) || walk_repr(cont, reprs, decls, seen)

      {tag, _step, _name, left, right} when tag in [:isend, :irecv] ->
        walk_repr(left, reprs, decls, seen) || walk_repr(right, reprs, decls, seen)

      {tag, _step, left, right} when tag in [:choose, :branch] ->
        walk_repr(left, reprs, decls, seen) || walk_repr(right, reprs, decls, seen)

      {:rec, _, body} ->
        walk_repr(body, reprs, decls, seen)

      {:case, _, arms} ->
        Enum.find_value(arms, fn {_tag, arm} -> walk_repr(arm, reprs, decls, seen) end)

      {:sjump, _, _} ->
        nil

      {:svar, _} ->
        nil

      {:end, _} ->
        nil

      _ ->
        nil
    end
  end

  defp nat_repr(reprs) do
    if "Nat" in reprs, do: "Nat"
  end

  defp walk_ty(:nat, reprs, _decls, _seen), do: nat_repr(reprs)
  defp walk_ty(:bit, _, _, _), do: nil
  defp walk_ty(:unit, _, _, _), do: nil

  defp walk_ty({:pair, a, b}, reprs, decls, seen) do
    walk_ty(a, reprs, decls, seen) || walk_ty(b, reprs, decls, seen)
  end

  defp walk_ty({:rec, fields}, reprs, decls, seen) when is_list(fields) do
    Enum.find_value(fields, fn {_n, ty} -> walk_ty(ty, reprs, decls, seen) end)
  end

  defp walk_ty({:vec, elem, _ix}, reprs, decls, seen), do: walk_ty(elem, reprs, decls, seen)

  defp walk_ty({:dat, name, args}, reprs, decls, seen) when is_binary(name) and is_list(args) do
    cond do
      name in reprs ->
        name

      true ->
        Enum.find_value(args, &walk_ty(&1, reprs, decls, seen)) ||
          walk_decl(name, reprs, decls, seen)
    end
  end

  defp walk_ty(_, _, _, _), do: nil

  defp walk_decl(name, reprs, decls, seen) do
    if MapSet.member?(seen, name) do
      nil
    else
      case Map.get(decls, name) do
        %{ctors: ctors} ->
          seen = MapSet.put(seen, name)

          Enum.find_value(ctors, fn {_tag, fields} ->
            Enum.find_value(fields, &walk_field(&1, name, reprs, decls, seen))
          end)

        _ ->
          nil
      end
    end
  end

  defp walk_field(:nat, _name, reprs, _decls, _seen), do: nat_repr(reprs)
  defp walk_field(:bit, _, _, _, _), do: nil
  defp walk_field(:unit, _, _, _, _), do: nil
  defp walk_field({:par, _}, _, _, _, _), do: nil
  defp walk_field({:bnat, _}, _, reprs, _, _), do: nat_repr(reprs)

  defp walk_field({:pair, a, b}, name, reprs, decls, seen) do
    walk_field(a, name, reprs, decls, seen) || walk_field(b, name, reprs, decls, seen)
  end

  defp walk_field({:rec, fields}, name, reprs, decls, seen) when is_list(fields) do
    Enum.find_value(fields, fn {_f, ty} -> walk_field(ty, name, reprs, decls, seen) end)
  end

  defp walk_field({:vec, elem, _}, name, reprs, decls, seen) do
    walk_field(elem, name, reprs, decls, seen)
  end

  defp walk_field({:self, ts}, name, reprs, decls, seen) when is_list(ts) do
    Enum.find_value(ts, &walk_field(&1, name, reprs, decls, seen))
  end

  defp walk_field({:dat, name, ts}, _dname, reprs, decls, seen)
       when is_binary(name) and is_list(ts) do
    cond do
      name in reprs ->
        name

      true ->
        Enum.find_value(ts, &walk_field(&1, name, reprs, decls, seen)) ||
          walk_decl(name, reprs, decls, seen)
    end
  end

  defp walk_field(_, _, _, _, _), do: nil

  defp walk_unboxed(proto, decls, book, seen) do
    case proto do
      {tag, _step, ty, cont} when tag in [:send, :recv] ->
        unboxed_ty(ty, decls, book, seen) || walk_unboxed(cont, decls, book, seen)

      {tag, _step, _name, ty, cont} when tag in [:dsend, :drecv] ->
        unboxed_ty(ty, decls, book, seen) || walk_unboxed(cont, decls, book, seen)

      {tag, _step, _name, _b, cont} when tag in [:esend, :erecv] ->
        walk_unboxed(cont, decls, book, seen)

      {tag, _step, _name, l, r} when tag in [:isend, :irecv] ->
        walk_unboxed(l, decls, book, seen) || walk_unboxed(r, decls, book, seen)

      {tag, _step, l, r} when tag in [:choose, :branch] ->
        walk_unboxed(l, decls, book, seen) || walk_unboxed(r, decls, book, seen)

      {:rec, _, body} ->
        walk_unboxed(body, decls, book, seen)

      {:case, _, arms} ->
        Enum.find_value(arms, fn {_t, arm} -> walk_unboxed(arm, decls, book, seen) end)

      _ ->
        nil
    end
  end

  defp unboxed_ty({:pair, a, b}, decls, book, seen) do
    unboxed_ty(a, decls, book, seen) || unboxed_ty(b, decls, book, seen)
  end

  defp unboxed_ty({:rec, fields}, decls, book, seen) when is_list(fields) do
    Enum.find_value(fields, fn {_n, ty} -> unboxed_ty(ty, decls, book, seen) end)
  end

  defp unboxed_ty({:vec, elem, _}, decls, book, seen), do: unboxed_ty(elem, decls, book, seen)

  defp unboxed_ty({:dat, name, args}, decls, book, seen) when is_binary(name) do
    cond do
      unboxed_data?(book, name) ->
        name

      true ->
        Enum.find_value(args, &unboxed_ty(&1, decls, book, seen)) ||
          unboxed_decl(name, decls, book, seen)
    end
  end

  defp unboxed_ty(_, _, _, _), do: nil

  defp unboxed_decl(name, decls, book, seen) do
    if MapSet.member?(seen, name) do
      nil
    else
      case Map.get(decls, name) do
        %{ctors: ctors} ->
          seen = MapSet.put(seen, name)

          Enum.find_value(ctors, fn {_tag, fields} ->
            Enum.find_value(fields, &unboxed_field(&1, name, decls, book, seen))
          end)

        _ ->
          nil
      end
    end
  end

  defp unboxed_field({:dat, name, ts}, _d, decls, book, seen)
       when is_binary(name) and is_list(ts) do
    cond do
      unboxed_data?(book, name) ->
        name

      true ->
        Enum.find_value(ts, &unboxed_field(&1, name, decls, book, seen)) ||
          unboxed_decl(name, decls, book, seen)
    end
  end

  defp unboxed_field({:self, ts}, name, decls, book, seen) do
    Enum.find_value(ts, &unboxed_field(&1, name, decls, book, seen))
  end

  defp unboxed_field({:pair, a, b}, name, decls, book, seen) do
    unboxed_field(a, name, decls, book, seen) || unboxed_field(b, name, decls, book, seen)
  end

  defp unboxed_field({:rec, fields}, name, decls, book, seen) when is_list(fields) do
    Enum.find_value(fields, fn {_f, ty} -> unboxed_field(ty, name, decls, book, seen) end)
  end

  defp unboxed_field({:vec, elem, _}, name, decls, book, seen) do
    unboxed_field(elem, name, decls, book, seen)
  end

  defp unboxed_field(_, _, _, _, _), do: nil

  defp unboxed_data?(book, name) do
    Enum.any?(book, fn
      %{kind: :data, name: ^name, unboxed: true} -> true
      _ -> false
    end)
  end

  defp plan(image, book, nm, sigs, opts) do
    templates = templates(image)
    datas = data_map(book)

    st = %{
      templates: templates,
      sessions: image.sessions,
      decls: image.decls,
      datas: datas,
      nm: nm,
      sigs: sigs,
      book: book,
      prefix: Keyword.get(opts, :c_prefix, ""),
      stem: Keyword.get(opts, :stem, "book"),
      keys: %{},
      nodes: %{},
      owners: %{},
      next: 1,
      slots: %{},
      slot_n: 0,
      inits: %{},
      checks: %{},
      check_ord: [],
      builds: %{},
      build_ord: [],
      ixs: %{},
      ix_ord: [],
      srcs: MapSet.new(),
      nat_of: false,
      putu: false,
      positions: %{},
      error: nil
    }

    st = pre_slots(st)

    Enum.reduce(image.sessions, st, fn sess, st ->
      ctx = %{
        mode: :expose,
        recs: %{},
        seen: [],
        template: {:sess, sess.name},
        bound: nil,
        live: true,
        ty: nil,
        owner: sess.name
      }

      {prog, st} = walk(sess.proto, ctx, st)
      %{st | inits: Map.put(st.inits, sess.name, prog)}
    end)
  end

  defp templates(image) do
    sessions =
      Map.new(image.sessions, fn sess ->
        {{:sess, sess.name},
         %{
           params: sess.params,
           proto: sess.proto,
           end_step: sess.end_step,
           file: sess.file,
           line: sess.line,
           name: sess.name
         }}
      end)

    duals =
      Map.new(image.duals, fn {name, {params, proto}} ->
        base =
          Map.get(sessions, {:sess, name}, %{file: "session", line: 0, name: name, end_step: ""})

        {{:dual, name},
         %{
           params: params,
           proto: proto,
           end_step: base.end_step,
           file: base.file,
           line: base.line,
           name: name
         }}
      end)

    Map.merge(sessions, duals)
  end

  defp data_map(book) do
    book
    |> Enum.filter(&(Map.get(&1, :kind) == :data))
    |> Map.new(fn d -> {d.name, d} end)
  end

  defp pre_slots(st) do
    Enum.reduce(st.templates, st, fn {key, %{params: params}}, st ->
      Enum.reduce(params, st, fn p, st ->
        {_i, st} = slot_for(st, key, p)
        st
      end)
    end)
  end

  defp slot_for(st, template, name) do
    k = {template, nm(name)}

    case Map.fetch(st.slots, k) do
      {:ok, i} ->
        {i, st}

      :error ->
        i = st.slot_n
        {i, %{st | slot_n: i + 1, slots: Map.put(st.slots, k, i)}}
    end
  end

  defp walk(proto, ctx, %{error: reason} = st) when not is_nil(reason) do
    _ = {proto, ctx}
    {{:stuck}, st}
  end

  defp walk(proto, ctx, st), do: walk1(proto, ctx, st)

  defp walk1({:rec, name, body}, ctx, st) do
    walk(body, %{ctx | recs: Map.put(ctx.recs, name, body)}, st)
  end

  defp walk1({:svar, name}, ctx, st) do
    mark = {:svar, name}

    cond do
      mark in ctx.seen ->
        {{:stuck}, st}

      true ->
        case Map.get(ctx.recs, name) do
          nil -> {{:stuck}, st}
          body -> walk(body, %{ctx | seen: [mark | ctx.seen]}, st)
        end
    end
  end

  defp walk1({:sjump, target, args}, ctx, st) do
    mark = {:jump, target, args}

    cond do
      mark in ctx.seen ->
        {{:stuck}, st}

      true ->
        key = jump_key(target)

        case Map.get(st.templates, key) do
          nil ->
            {{:stuck}, st}

          %{params: params, proto: proto} ->
            folded = Enum.map(args, &fold_ix/1)

            if length(params) != length(folded) or Enum.any?(folded, &(&1 == :overflow)) do
              {{:stuck}, st}
            else
              # Jump arguments are read in the caller's environment.
              {ixs, st} =
                Enum.map_reduce(folded, st, fn
                  {:lit, n}, st -> {{:lit, n}, st}
                  expr, st -> ix_for(st, ctx.template, expr)
                end)

              inner_ctx = %{
                ctx
                | template: key,
                  recs: %{},
                  seen: [mark | ctx.seen],
                  live: false
              }

              {inner, st} = walk(proto, inner_ctx, st)
              slots = Enum.map(params, fn p -> Map.fetch!(st.slots, {key, nm(p)}) end)
              {{:jump, slots, ixs, inner}, st}
            end
        end
    end
  end

  defp walk1({:case, scrut, arms}, %{mode: :expose}, st) do
    _ = {scrut, arms}
    {{:stuck}, st}
  end

  defp walk1({:case, scrut, arms}, ctx, st) do
    cond do
      not ctx.live ->
        {{:fail}, st}

      true ->
        case scrut do
          {:run, _fname, _n, earlier} when is_list(earlier) ->
            {_, st} = ill(st, ctx.template, "cannot call run")
            {{:fail}, st}

          {:run, fname, n} ->
            if nm(n) == nm(ctx.bound) do
              run_case(fname, ctx, arms, st)
            else
              {{:fail}, st}
            end

          {:name, n} ->
            if nm(n) == nm(ctx.bound) and matchable?(ctx.ty) do
              name_case(ctx, arms, st)
            else
              {{:fail}, st}
            end

          _ ->
            {{:fail}, st}
        end
    end
  end

  defp walk1({:send, step, ty, cont} = proto, ctx, st),
    do: comm(:send, step, nil, ty, cont, proto, ctx, st)

  defp walk1({:recv, step, ty, cont} = proto, ctx, st),
    do: comm(:recv, step, nil, ty, cont, proto, ctx, st)

  defp walk1({:dsend, step, name, ty, cont} = proto, ctx, st),
    do: comm(:dsend, step, name, ty, cont, proto, ctx, st)

  defp walk1({:drecv, step, name, ty, cont} = proto, ctx, st),
    do: comm(:drecv, step, name, ty, cont, proto, ctx, st)

  defp walk1({:esend, step, name, bound, cont} = proto, ctx, st) do
    evidence(:esend, step, name, bound, cont, proto, ctx, st)
  end

  defp walk1({:erecv, step, name, bound, cont} = proto, ctx, st) do
    evidence(:erecv, step, name, bound, cont, proto, ctx, st)
  end

  defp walk1({:isend, step, name, left, right} = proto, ctx, st) do
    split(:isend, step, name, left, right, proto, ctx, st)
  end

  defp walk1({:irecv, step, name, left, right} = proto, ctx, st) do
    split(:irecv, step, name, left, right, proto, ctx, st)
  end

  defp walk1({:choose, step, left, right} = proto, ctx, st),
    do: split(:choose, step, nil, left, right, proto, ctx, st)

  defp walk1({:branch, step, left, right} = proto, ctx, st),
    do: split(:branch, step, nil, left, right, proto, ctx, st)

  defp walk1({:end, step} = proto, ctx, st), do: finish(proto, step, ctx, st)

  defp walk1(_other, ctx, st) do
    {_ok, st} = ill(st, ctx.template, "ill-formed protocol")
    {{:stuck}, st}
  end

  defp comm(kind, step, name, ty, cont, proto, ctx, st) do
    open_node(ctx.template, step, ctx.owner, proto, ctx.recs, st, fn id, st ->
      {slot, st} = if ty == :nat and name, do: slot_for(st, ctx.template, name), else: {nil, st}
      st = ensure_check(st, ctx.template, ty)

      cont_ctx = %{
        ctx
        | mode: :quiet,
          seen: [],
          bound: name,
          live: true,
          ty: ty
      }

      {prog, st} = walk(cont, cont_ctx, st)

      node = %{
        id: id,
        template: ctx.template,
        kind: kind,
        step: step,
        ty: ty,
        name: name,
        slot: slot,
        bound: nil,
        prog: prog,
        left: nil,
        right: nil
      }

      {node, st}
    end)
  end

  defp evidence(kind, step, name, bound, cont, proto, ctx, st) do
    open_node(ctx.template, step, ctx.owner, proto, ctx.recs, st, fn id, st ->
      {slot, st} = slot_for(st, ctx.template, name)
      {ix, st} = ix_of_bound(st, ctx.template, bound)

      cont_ctx = %{ctx | mode: :expose, seen: [], bound: nil, live: true, ty: nil}
      {prog, st} = walk(cont, cont_ctx, st)

      node = %{
        id: id,
        template: ctx.template,
        kind: kind,
        step: step,
        ty: :nat,
        name: name,
        slot: slot,
        bound: ix,
        prog: prog,
        left: nil,
        right: nil
      }

      {node, st}
    end)
  end

  defp split(kind, step, name, left, right, proto, ctx, st) do
    _ = name

    open_node(ctx.template, step, ctx.owner, proto, ctx.recs, st, fn id, st ->
      arm = %{ctx | mode: :expose, seen: [], bound: nil, live: true, ty: nil}
      {lprog, st} = walk(left, arm, st)
      {rprog, st} = walk(right, arm, st)

      node = %{
        id: id,
        template: ctx.template,
        kind: kind,
        step: step,
        ty: :bit,
        name: name,
        slot: nil,
        bound: nil,
        prog: nil,
        left: lprog,
        right: rprog
      }

      {node, st}
    end)
  end

  defp finish(proto, step, ctx, st) do
    open_node(ctx.template, step, ctx.owner, proto, ctx.recs, st, fn id, st ->
      node = %{
        id: id,
        template: ctx.template,
        kind: :end,
        step: step,
        ty: nil,
        name: nil,
        slot: nil,
        bound: nil,
        prog: nil,
        left: nil,
        right: nil
      }

      {node, st}
    end)
  end

  defp open_node(template, step, owner, proto, recs, st, build) do
    if st.error do
      {{:stuck}, st}
    else
      key = {template, step}

      case Map.get(st.keys, key) do
        id when is_integer(id) ->
          {{:land, id}, add_owner(st, id, owner)}

        nil ->
          id = st.next

          st =
            if id > 65_535 do
              err(st, "too many session states")
            else
              %{
                st
                | next: id + 1,
                  keys: Map.put(st.keys, key, id),
                  owners: Map.put(st.owners, id, MapSet.new([owner])),
                  positions:
                    Map.put(st.positions, id, %{
                      session: owner,
                      template: template,
                      proto: proto,
                      recs: recs,
                      step: step
                    })
              }
            end

          if st.error do
            {{:stuck}, st}
          else
            {node, st} = build.(id, st)
            {{:land, id}, %{st | nodes: Map.put(st.nodes, id, node)}}
          end
      end
    end
  end

  defp add_owner(st, id, owner) do
    owners =
      Map.update(st.owners, id, MapSet.new([owner]), fn set -> MapSet.put(set, owner) end)

    %{st | owners: owners}
  end

  defp name_case(ctx, arms, st) do
    st = ensure_src(st, case_data(ctx.ty))

    {arms, st} =
      Enum.map_reduce(arms, st, fn {tag, proto}, st ->
        arm = %{ctx | mode: :expose, seen: [], bound: nil, live: true, ty: nil}
        {prog, st} = walk(proto, arm, st)
        {{nm(tag), prog}, st}
      end)

    {{:name_case, case_kind(ctx.ty), arms}, st}
  end

  defp run_case(fname, ctx, arms, st) do
    case prepare_run(st, fname, ctx.ty, ctx.template) do
      {:error, st} ->
        {{:fail}, st}

      {:ok, info, st} ->
        {arms, st} =
          Enum.map_reduce(arms, st, fn {tag, proto}, st ->
            arm = %{ctx | mode: :expose, seen: [], bound: nil, live: true, ty: nil}
            {prog, st} = walk(proto, arm, st)
            {{nm(tag), prog}, st}
          end)

        {{:run_case, info, ctx.ty, arms}, st}
    end
  end

  defp prepare_run(st, fname, ty, template) do
    sig = Enum.find(st.sigs, &(&1.source == fname))
    ret = sig && String.trim(sig.ret)

    data =
      sig &&
        Enum.find(Map.values(st.datas), fn d ->
          spell = C.data_struct(d.name, st.prefix)

          cond do
            ret == spell <> " *" -> true
            ret == spell -> C.enum_type?(st.book, d.name) and not unboxed_data?(st.book, d.name)
            true -> false
          end
        end)

    param = sig && param_ty(sig)

    cond do
      is_nil(sig) or is_nil(data) ->
        {:error, blame(st, template, "#{fname}: result is not a C payload tag")}

      not arg_ok?(ty, param, st) ->
        {:error, blame(st, template, "#{fname}: argument is not a C payload")}

      build_blocked?(ty, st) ->
        {:error, blame(st, template, "#{fname}: argument is not a C payload")}

      true ->
        ctors = Enum.map(data.ctors, & &1.name)

        info = %{
          fname: fname,
          cname: sig.name,
          ret: data.name,
          ctors: ctors,
          spell: C.data_struct(data.name, st.prefix),
          arg: build_ptr(ty, st)
        }

        {id, st} = build_for(st, ty)
        {:ok, Map.put(info, :build, id), st}
    end
  end

  defp param_ty(%{params: [{ty, _}]}), do: String.trim(ty)
  defp param_ty(_), do: nil

  defp arg_ok?(:nat, "muro__nat *", _st), do: true

  defp arg_ok?({:dat, name, _}, param, st) when is_binary(param) do
    spell = C.data_struct(name, st.prefix)

    param == spell <> " *" or
      (param == spell and C.enum_type?(st.book, name) and not unboxed_data?(st.book, name))
  end

  defp arg_ok?(_, _, _), do: false

  defp build_blocked?(ty, st), do: build_blocked?(ty, st, MapSet.new())
  defp build_blocked?(:nat, _st, _seen), do: false
  defp build_blocked?(:unit, _st, _seen), do: false
  defp build_blocked?(:bit, _st, _seen), do: true

  defp build_blocked?({:pair, a, b}, st, seen),
    do: build_blocked?(a, st, seen) or build_blocked?(b, st, seen)

  defp build_blocked?({:vec, elem, _}, st, seen), do: build_blocked?(elem, st, seen)

  defp build_blocked?({:rec, fields}, st, seen) when is_list(fields) do
    Enum.any?(fields, fn {_n, ty} -> build_blocked?(ty, st, seen) end)
  end

  defp build_blocked?({:dat, name, args} = ty, st, seen) when is_binary(name) and is_list(args) do
    cond do
      MapSet.member?(seen, ty) ->
        false

      Enum.any?(args, &build_blocked?(&1, st, seen)) ->
        true

      true ->
        seen = MapSet.put(seen, ty)

        case Map.get(st.decls, name) do
          %{ctors: ctors} ->
            Enum.any?(ctors, fn {_c, fields} ->
              Enum.any?(fields, fn field ->
                build_blocked?(inst_field(field, name, args), st, seen)
              end)
            end)

          _ ->
            true
        end
    end
  end

  defp build_blocked?(_, _st, _seen), do: true

  defp case_data({:dat, name, _}), do: name
  defp case_data(_), do: nil

  defp case_kind({:dat, name, args}), do: {:dat, name, args}
  defp case_kind(:bit), do: :bit
  defp case_kind(_), do: :other

  defp matchable?(:bit), do: true
  defp matchable?({:dat, name, args}) when is_binary(name) and is_list(args), do: true
  defp matchable?(_), do: false

  defp ensure_src(st, nil), do: st
  defp ensure_src(st, name), do: %{st | srcs: MapSet.put(st.srcs, name)}

  defp ensure_check(st, template, ty) do
    st = note_ix(st, template, ty)
    key = {template, ty}

    if Map.has_key?(st.checks, key) do
      st
    else
      id = length(st.check_ord)
      %{st | checks: Map.put(st.checks, key, id), check_ord: st.check_ord ++ [key]}
    end
  end

  # A vector length is read from the environment at the check, so the
  # index function has to exist before the checker is emitted.
  defp note_ix(st, template, ty), do: note_ix(st, template, ty, MapSet.new())

  defp note_ix(st, template, {:vec, elem, ix}, seen) do
    st =
      case fold_ix(ix) do
        {:lit, _} -> st
        :overflow -> st
        expr -> elem(ix_for(st, template, expr), 1)
      end

    note_ix(st, template, elem, seen)
  end

  defp note_ix(st, template, {:pair, a, b}, seen) do
    st |> note_ix(template, a, seen) |> note_ix(template, b, seen)
  end

  defp note_ix(st, template, {:rec, fields}, seen) when is_list(fields) do
    Enum.reduce(fields, st, fn {_n, ty}, st -> note_ix(st, template, ty, seen) end)
  end

  defp note_ix(st, template, {:dat, name, args} = ty, seen) when is_list(args) do
    if MapSet.member?(seen, ty) do
      st
    else
      seen = MapSet.put(seen, ty)

      Enum.reduce(args, st, fn arg, st -> note_ix(st, template, arg, seen) end)
      |> then(fn st ->
        case Map.get(st.decls, name) do
          %{ctors: ctors} ->
            Enum.reduce(ctors, st, fn {_c, fields}, st ->
              Enum.reduce(fields, st, fn field, st ->
                note_ix(st, template, inst_field(field, name, args), seen)
              end)
            end)

          _ ->
            st
        end
      end)
    end
  end

  defp note_ix(st, _template, _ty, _seen), do: st

  defp build_for(st, ty) do
    key = build_key(ty)

    case Map.fetch(st.builds, key) do
      {:ok, id} ->
        {id, flag_nat(st, ty)}

      :error ->
        id = length(st.build_ord)
        st = %{st | builds: Map.put(st.builds, key, id), build_ord: st.build_ord ++ [{key, ty}]}
        {id, flag_nat(st, ty)}
    end
  end

  defp flag_nat(st, ty) do
    if has_nat?(ty), do: %{st | nat_of: true}, else: st
  end

  defp has_nat?(:nat), do: true
  defp has_nat?({:pair, a, b}), do: has_nat?(a) or has_nat?(b)
  defp has_nat?({:vec, e, _}), do: has_nat?(e)
  defp has_nat?({:rec, fs}) when is_list(fs), do: Enum.any?(fs, fn {_, t} -> has_nat?(t) end)
  defp has_nat?({:dat, _, args}), do: Enum.any?(args, &has_nat?/1)
  defp has_nat?(_), do: false

  defp build_key(ty), do: ty

  defp ix_of_bound(st, template, expr) do
    case fold_ix(expr) do
      {:lit, n} -> {{:lit, n}, st}
      :overflow -> {{:overflow}, st}
      other -> ix_for(st, template, other)
    end
  end

  defp ix_for(st, template, expr) do
    key = {template, expr}

    case Map.fetch(st.ixs, key) do
      {:ok, id} ->
        {{:ix, id}, st}

      :error ->
        id = length(st.ix_ord)
        st = %{st | ixs: Map.put(st.ixs, key, id), ix_ord: st.ix_ord ++ [{id, template, expr}]}
        {{:ix, id}, %{st | putu: true}}
    end
  end

  defp fold_ix({:lit, n}) when is_integer(n) and n >= 0, do: {:lit, n}
  defp fold_ix({:var, name}), do: {:var, name}

  defp fold_ix({:suc, inner}) do
    case fold_ix(inner) do
      {:lit, n} when n < 18_446_744_073_709_551_615 -> {:lit, n + 1}
      {:lit, _} -> :overflow
      :overflow -> :overflow
      other -> {:suc, other}
    end
  end

  defp fold_ix(_), do: :overflow

  defp ill(st, template, reason), do: {:error, blame(st, template, reason)}

  defp blame(st, template, reason) do
    %{file: file, line: line, name: name} = Map.fetch!(st.templates, template)
    err(st, "#{file}:#{line} session #{name}: #{reason}")
  end

  defp err(st, reason), do: %{st | error: st.error || @err <> reason}

  defp nm(name) when is_atom(name), do: Atom.to_string(name)
  defp nm(name) when is_binary(name), do: name
  defp nm(name), do: to_string(name)

  defp jump_key(name) when is_binary(name), do: {:sess, name}
  defp jump_key(name) when is_atom(name), do: {:sess, Atom.to_string(name)}
  defp jump_key({:dual, name}) when is_binary(name), do: {:dual, name}
  defp jump_key({:dual, name}) when is_atom(name), do: {:dual, Atom.to_string(name)}
  defp jump_key(_), do: nil

  # --- C text ---

  defp header(st) do
    n = max(st.slot_n, 1)

    """
    #include <stddef.h>
    #include <stdint.h>

    #ifndef MURO__SESS_ABI
    #define MURO__SESS_ABI
    typedef enum muro__sess_status {
      MURO_SESS_OK = 0,
      MURO_SESS_UNEXPECTED = 1,
      MURO_SESS_BAD = 2,
      MURO_SESS_INIT = 3
    } muro__sess_status;

    typedef enum muro__sess_dir {
      MURO_SESS_SEND = 1,
      MURO_SESS_RECV = 2
    } muro__sess_dir;

    typedef enum muro__sess_tag {
      MURO_SESS_NAT = 1,
      MURO_SESS_BIT = 2,
      MURO_SESS_UNIT = 3,
      MURO_SESS_PICK = 4,
      MURO_SESS_PAIR = 5,
      MURO_SESS_REC = 6,
      MURO_SESS_VEC = 7,
      MURO_SESS_DATA = 8
    } muro__sess_tag;

    typedef struct muro__sess_val {
      uint8_t tag;
      uint8_t bit;
      uint64_t nat;
      uint64_t n;
      const char *ctor;
      const char *const *names;
      const struct muro__sess_val *a;
      const struct muro__sess_val *b;
    } muro__sess_val;
    #endif

    #ifndef MURO__SESS_ST
    #define MURO__SESS_ST
    #define MURO__SESS_SLOTS #{n}
    typedef struct muro__sess_st {
      uint16_t key;
      uint16_t at;
      uint8_t stuck;
      uint64_t nat[#{n}];
      uint8_t set[#{n}];
    } muro__sess_st;

    typedef struct muro__sess_res {
      int status;
      muro__sess_st state;
      const char *step;
      char expected[1024];
      int done;
    } muro__sess_res;
    #elif MURO__SESS_SLOTS != #{n}
    #error muro session state slot count differs between headers
    #endif

    #{prototypes(st)}
    """
    |> String.trim()
  end

  defp prototypes(st) do
    gens = generic_protos(st)

    guarded =
      if st.prefix == "" do
        """
        #ifndef MURO__SESS_API
        #define MURO__SESS_API
        #{gens}
        #endif
        """
      else
        gens
      end

    pers =
      Enum.map(st.sessions, fn sess ->
        fun = sess_fun(st, sess.name)

        """
        muro__sess_res #{fun}_init(#{init_params(sess)});
        muro__sess_res #{fun}_step(muro__sess_st st, int dir, const muro__sess_val *value);
        muro__sess_res #{fun}_step_word(muro__sess_st st, int dir, int tag, uint64_t word);
        int #{fun}_done(muro__sess_st st);
        const char *#{fun}_at(muro__sess_st st);
        void #{fun}_expected(muro__sess_st st, char *buf, size_t n);
        """
      end)

    ([String.trim(guarded)] ++ pers) |> Enum.join("\n") |> String.trim()
  end

  defp generic_protos(st) do
    i = api(st, "init")
    s = api(st, "step")
    w = api(st, "step_word")
    d = api(st, "done")
    a = api(st, "at")
    e = api(st, "expected")

    """
    muro__sess_res #{i}(const char *name, const uint64_t *args, size_t n);
    muro__sess_res #{s}(const char *name, muro__sess_st st, int dir, const muro__sess_val *value);
    muro__sess_res #{w}(const char *name, muro__sess_st st, int dir, int tag, uint64_t word);
    int #{d}(const char *name, muro__sess_st st);
    const char *#{a}(const char *name, muro__sess_st st);
    void #{e}(const char *name, muro__sess_st st, char *buf, size_t n);
    """
    |> String.trim()
  end

  defp api(st, tail), do: st.prefix <> "muro__sess_" <> tail

  defp init_params(%{params: []}), do: "void"

  defp init_params(%{params: params}) do
    params
    |> Enum.with_index()
    |> Enum.map_join(", ", fn {_p, i} -> "uint64_t a#{i}" end)
  end

  defp sess_fun(st, name), do: api(st, C.source_id(name))

  defp source(st) do
    st =
      st
      |> expand_checks()
      |> note_srcs()
      |> expand_builds()
      |> flag_builds()

    source_emit(st)
  end

  defp puts_src do
    """
    static void muro__sess_puts(char *buf, size_t n, size_t *i, const char *s) {
      if (!s) return;
      while (*s && *i + 1 < n) buf[(*i)++] = *s++;
      if (*i < n) buf[*i] = 0;
    }

    static void muro__sess_lit(char *buf, size_t n, const char *s) {
      size_t i = 0;
      if (n) buf[0] = 0;
      muro__sess_puts(buf, n, &i, s);
    }
    """
    |> String.trim()
  end

  defp putu_src do
    """
    static void muro__sess_putu(char *buf, size_t n, size_t *i, uint64_t x) {
      char tmp[32];
      int k = 0;
      if (x == 0) {
        muro__sess_puts(buf, n, i, "0");
        return;
      }
      while (x > 0 && k < 32) {
        tmp[k++] = (char)('0' + (x % 10));
        x /= 10;
      }
      while (k > 0) {
        char one[2];
        one[0] = tmp[--k];
        one[1] = 0;
        muro__sess_puts(buf, n, i, one);
      }
    }
    """
    |> String.trim()
  end

  defp nat_of_src do
    nat = Name.gen("nat")
    zero = Name.gen("zero")
    suc = Name.gen("suc")

    """
    static #{nat} *muro__sess_nat_of(uint64_t n) {
      #{nat} *p;
      if (n > #{@cap}ull) return 0;
      p = #{zero}();
      while (n > 0) {
        p = #{suc}(p);
        n--;
      }
      return p;
    }
    """
    |> String.trim()
  end

  defp ix_src(st) do
    Enum.map_join(st.ix_ord, "\n\n", fn {id, template, expr} ->
      body = ix_body(expr, template, st)

      """
      static int muro__sess_ix_#{id}(const muro__sess_st *st, uint64_t *out) {
      #{indent(body, 2)}
      }
      """
      |> String.trim()
    end)
  end

  defp ix_body({:var, name}, template, st) do
    slot = Map.fetch!(st.slots, {template, nm(name)})

    """
    if (!st->set[#{slot}]) return 0;
    *out = st->nat[#{slot}];
    return 1;
    """
    |> String.trim()
  end

  defp ix_body({:suc, inner}, template, st) do
    {core, k} = suc_depth(inner, 0)
    inner_body = ix_body(core, template, st) |> String.replace("return 1;", "x = *out;")

    """
    uint64_t x;
    #{inner_body}
    if (x > UINT64_MAX - #{k}ull) return 0;
    *out = x + #{k}ull;
    return 1;
    """
    |> String.trim()
  end

  defp ix_body(_, _, _) do
    "return 0;"
  end

  defp suc_depth({:suc, inner}, k), do: suc_depth(inner, k + 1)
  defp suc_depth(other, k), do: {other, k + 1}

  defp src_src(st) do
    Enum.map_join(st.srcs, "\n\n", fn name ->
      decl = Map.get(st.decls, name)
      order = if decl, do: decl.order, else: []
      spell = C.source_id(name)
      safes = safe_pairs(order)
      lines = src_lines(safes, order)

      """
      static const char *muro__sess_src_#{spell}(const char *got) {
        if (!got) return 0;
      #{lines}
        return 0;
      }
      """
      |> String.trim()
    end)
  end

  defp safe_pairs(order) do
    Enum.flat_map(order, fn ctor ->
      safe = Emit.elixir_atom_name(ctor)
      if safe == ctor, do: [], else: [{safe, ctor}]
    end)
  end

  defp src_lines(safes, order) do
    checks =
      Enum.map(safes, fn {safe, ctor} ->
        "  if (strcmp(got, #{c_str(safe)}) == 0) return #{c_str(ctor)};"
      end) ++
        Enum.map(order, fn ctor ->
          "  if (strcmp(got, #{c_str(ctor)}) == 0) return #{c_str(ctor)};"
        end)

    Enum.join(checks, "\n")
  end

  defp check_src(st) do
    proto =
      Enum.map_join(st.check_ord, "\n", fn key ->
        id = Map.fetch!(st.checks, key)
        "static int muro__sess_pay_#{id}(const muro__sess_val *v, const muro__sess_st *st);"
      end)

    bodies =
      Enum.map_join(st.check_ord, "\n\n", fn {template, ty} = key ->
        id = Map.fetch!(st.checks, key)
        body = check_body(ty, template, st, "v")

        """
        static int muro__sess_pay_#{id}(const muro__sess_val *v, const muro__sess_st *st) {
          (void)st;
        #{indent(body, 2)}
        }
        """
        |> String.trim()
      end)

    [proto, bodies] |> Enum.reject(&(&1 == "")) |> Enum.join("\n\n")
  end

  defp check_body(:nat, _template, _st, v) do
    "return #{v} && #{v}->tag == MURO_SESS_NAT;"
  end

  defp check_body(:bit, _template, _st, v) do
    "return #{v} && #{v}->tag == MURO_SESS_BIT && #{v}->bit <= 1;"
  end

  defp check_body(:unit, _template, _st, v) do
    "return #{v} && #{v}->tag == MURO_SESS_UNIT;"
  end

  defp check_body({:bnat, _}, _template, _st, _v) do
    "return 0;"
  end

  defp check_body({:pair, a, b}, template, st, v) do
    """
    if (!#{v} || #{v}->tag != MURO_SESS_PAIR || !#{v}->a || !#{v}->b) return 0;
    if (!#{check_call(a, template, st, "#{v}->a")}) return 0;
    return #{check_call(b, template, st, "#{v}->b")};
    """
    |> String.trim()
  end

  defp check_body({:rec, fields}, template, st, v) when is_list(fields) do
    n = length(fields)

    cond do
      n == 0 ->
        "return #{v} && #{v}->tag == MURO_SESS_REC && #{v}->n == 0;"

      true ->
        names =
          Enum.with_index(fields, fn {name, ty}, i ->
            {nm(name), ty, i}
          end)

        tests =
          Enum.map_join(names, "\n", fn {name, _ty, i} ->
            "    else if (strcmp(nm, #{c_str(name)}) == 0) hit = #{i};"
          end)
          |> String.replace_prefix("    else ", "    ")

        field_checks =
          Enum.map_join(names, "\n", fn {_name, ty, i} ->
            call = check_call(ty, template, st, "&" <> v <> "->a[i]")

            """
            if (hit == #{i}) {
              if (seen[#{i}]) return 0;
              seen[#{i}] = 1;
              if (!#{call}) return 0;
            }
            """
            |> String.trim()
          end)

        """
        if (!#{v} || #{v}->tag != MURO_SESS_REC || #{v}->n != #{n} || !#{v}->a || !#{v}->names) return 0;
        {
          uint8_t seen[#{n}] = {0};
          uint64_t i;
          for (i = 0; i < #{v}->n; i++) {
            const char *nm = #{v}->names[i];
            int hit = -1;
            if (!nm) return 0;
        #{tests}
            else return 0;
        #{indent(field_checks, 4)}
          }
        }
        return 1;
        """
        |> String.trim()
    end
  end

  defp check_body({:vec, elem, ix}, template, st, v) do
    len = length_code(ix, template, st)

    """
    {
      uint64_t len = 0;
      uint64_t i;
      #{len}
      if (!#{v} || #{v}->tag != MURO_SESS_VEC || #{v}->n != len) return 0;
      if (len && !#{v}->a) return 0;
      for (i = 0; i < len; i++) {
        if (!#{check_call(elem, template, st, "&#{v}->a[i]")}) return 0;
      }
      return 1;
    }
    """
    |> String.trim()
  end

  defp check_body({:dat, name, args}, template, st, v) do
    decl = Map.get(st.decls, name)

    if is_nil(decl) do
      "return 0;"
    else
      st = ensure_src(st, name)
      _ = st
      spell = C.source_id(name)

      arms =
        Enum.map_join(decl.order, "\n", fn ctor ->
          fields = Map.get(decl.ctors, ctor, [])
          inst = Enum.map(fields, &inst_field(&1, name, args))
          n = length(inst)

          checks =
            inst
            |> Enum.with_index()
            |> Enum.map_join("\n", fn {ty, i} ->
              "if (!#{check_call(ty, template, st, "&#{v}->a[#{i}]")}) return 0;"
            end)

          """
          if (strcmp(tag, #{c_str(ctor)}) == 0) {
            if (#{v}->n != #{n}) return 0;
            if (#{n} && !#{v}->a) return 0;
          #{indent(checks, 2)}
            return 1;
          }
          """
          |> String.trim()
        end)

      """
      {
        const char *tag;
        if (!#{v} || #{v}->tag != MURO_SESS_DATA) return 0;
        tag = muro__sess_src_#{spell}(#{v}->ctor);
        if (!tag) return 0;
      #{indent(arms, 2)}
        return 0;
      }
      """
      |> String.trim()
    end
  end

  defp check_body(_, _, _, _), do: "return 0;"

  defp check_call(ty, template, st, expr) do
    id = Map.fetch!(st.checks, {template, ty})
    "muro__sess_pay_#{id}(#{expr}, st)"
  end

  defp length_code(ix, template, st) do
    case fold_ix(ix) do
      {:lit, n} ->
        "len = #{n}ull;"

      :overflow ->
        "return 0;"

      expr ->
        {{:ix, id}, _} = ix_for_lookup(st, template, expr)
        "if (!muro__sess_ix_#{id}(st, &len)) return 0;"
    end
  end

  defp ix_for_lookup(st, template, expr) do
    id = Map.fetch!(st.ixs, {template, expr})
    {{:ix, id}, st}
  end

  defp inst_field({:par, i}, _name, args), do: Enum.at(args, i) || :ill

  defp inst_field({:pair, a, b}, name, args) do
    {:pair, inst_field(a, name, args), inst_field(b, name, args)}
  end

  defp inst_field({:rec, fields}, name, args) when is_list(fields) do
    {:rec, Enum.map(fields, fn {f, ty} -> {f, inst_field(ty, name, args)} end)}
  end

  defp inst_field({:vec, elem, ix}, name, args) do
    {:vec, inst_field(elem, name, args), ix}
  end

  defp inst_field({:self, ts}, name, args) do
    {:dat, name, Enum.map(ts, &inst_field(&1, name, args))}
  end

  defp inst_field({:dat, dname, ts}, name, args) do
    {:dat, dname, Enum.map(ts, &inst_field(&1, name, args))}
  end

  defp inst_field(ty, _name, _args), do: ty

  defp expand_checks(st) do
    extra = Enum.flat_map(st.check_ord, fn {template, ty} -> nested_types(ty, template, st) end)
    grow(st, extra)
  end

  defp grow(st, []), do: st

  defp grow(st, types) do
    st2 = Enum.reduce(types, st, fn {template, ty}, st -> ensure_check(st, template, ty) end)

    if length(st2.check_ord) == length(st.check_ord) do
      st
    else
      expand_checks(st2)
    end
  end

  defp nested_types(ty, template, st) do
    case ty do
      {:pair, a, b} ->
        [{template, a}, {template, b}]

      {:rec, fields} when is_list(fields) ->
        Enum.map(fields, fn {_n, t} -> {template, t} end)

      {:vec, elem, _} ->
        [{template, elem}]

      {:dat, name, args} ->
        case Map.get(st.decls, name) do
          %{ctors: ctors} ->
            Enum.flat_map(ctors, fn {_c, fields} ->
              Enum.map(fields, fn field -> {template, inst_field(field, name, args)} end)
            end)

          _ ->
            []
        end

      _ ->
        []
    end
  end

  defp source_emit(st) do
    parts = [
      drop_macro(),
      "#include <string.h>",
      puts_src(),
      if(st.putu, do: putu_src(), else: ""),
      if(st.nat_of, do: nat_of_src(), else: ""),
      ix_src(st),
      src_src(st),
      check_src(st),
      build_src(st),
      label_src(st),
      word_name_src(st),
      Enum.map_join(st.sessions, "\n\n", &session_src(&1, st)),
      generic_src(st)
    ]

    parts
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n\n")
    |> Kernel.<>("\n")
  end

  defp note_srcs(st) do
    from_checks =
      Enum.reduce(st.check_ord, st, fn
        {_template, {:dat, name, _}}, st when is_binary(name) -> ensure_src(st, name)
        _, st -> st
      end)

    Enum.reduce(st.srcs, from_checks, &ensure_src(&2, &1))
  end

  defp expand_builds(st) do
    n = length(st.build_ord)

    st =
      Enum.reduce(st.build_ord, st, fn {_key, ty}, st ->
        add_builds(st, ty, MapSet.new())
      end)

    if length(st.build_ord) == n, do: st, else: expand_builds(st)
  end

  defp add_builds(st, {:dat, name, args} = ty, seen) do
    if MapSet.member?(seen, ty) do
      st
    else
      seen = MapSet.put(seen, ty)

      case Map.get(st.decls, name) do
        %{ctors: ctors} ->
          Enum.reduce(ctors, st, fn {_c, fields}, st ->
            Enum.reduce(fields, st, fn field, st ->
              ity = inst_field(field, name, args)
              {_id, st} = build_for(st, ity)
              add_builds(st, ity, seen)
            end)
          end)

        _ ->
          st
      end
    end
  end

  defp add_builds(st, {:pair, a, b}, seen), do: st |> add_builds(a, seen) |> add_builds(b, seen)
  defp add_builds(st, {:vec, elem, _}, seen), do: add_builds(st, elem, seen)

  defp add_builds(st, {:rec, fields}, seen) when is_list(fields) do
    Enum.reduce(fields, st, fn {_n, ty}, st -> add_builds(st, ty, seen) end)
  end

  defp add_builds(st, _ty, _seen), do: st

  defp flag_builds(st) do
    needs =
      Enum.any?(st.build_ord, fn {_key, ty} ->
        build_needs_nat?(ty, st, MapSet.new())
      end)

    if needs, do: %{st | nat_of: true}, else: st
  end

  defp build_needs_nat?(:nat, _st, _seen), do: true

  defp build_needs_nat?({:dat, name, args} = ty, st, seen) do
    cond do
      MapSet.member?(seen, ty) ->
        false

      true ->
        seen = MapSet.put(seen, ty)

        case Map.get(st.decls, name) do
          %{ctors: ctors} ->
            Enum.any?(ctors, fn {_c, fields} ->
              Enum.any?(fields, fn field ->
                build_needs_nat?(inst_field(field, name, args), st, seen)
              end)
            end)

          _ ->
            false
        end
    end
  end

  defp build_needs_nat?({:pair, a, b}, st, seen) do
    build_needs_nat?(a, st, seen) or build_needs_nat?(b, st, seen)
  end

  defp build_needs_nat?({:vec, elem, _}, st, seen), do: build_needs_nat?(elem, st, seen)

  defp build_needs_nat?({:rec, fields}, st, seen) when is_list(fields) do
    Enum.any?(fields, fn {_n, ty} -> build_needs_nat?(ty, st, seen) end)
  end

  defp build_needs_nat?(_, _, _), do: false

  defp drop_macro do
    """
    #ifndef muro__DROP
    #define muro__DROP(p) free(p)
    #endif
    """
    |> String.trim()
  end

  defp build_src(%{build_ord: []}), do: ""

  defp build_src(st) do
    entries =
      Enum.map(st.build_ord, fn {key, ty} ->
        {Map.fetch!(st.builds, key), ty}
      end)

    build_proto =
      Enum.map_join(entries, "\n", fn {id, ty} ->
        "static int muro__sess_build_#{id}(const muro__sess_val *v, const muro__sess_st *st, #{build_ptr(ty, st)} *out);"
      end)

    free_proto =
      Enum.map_join(entries, "\n", fn {id, ty} ->
        "static void muro__sess_free_#{id}(#{build_ptr(ty, st)}p);"
      end)

    free_body = Enum.map_join(entries, "\n\n", fn {id, ty} -> free_body(ty, id, st) end)

    built =
      Enum.map_join(entries, "\n\n", fn {id, ty} ->
        ptr = build_ptr(ty, st)

        """
        static int muro__sess_build_#{id}(const muro__sess_val *v, const muro__sess_st *st, #{ptr} *out) {
          (void)st;
        #{indent(build_body(ty, st), 2)}
        }
        """
        |> String.trim()
      end)

    [build_proto, free_proto, free_body, built]
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n\n")
  end

  defp free_body(:nat, id, _st) do
    nat = Name.gen("nat")
    tag = Name.gen("field_tag")
    suc = Name.gen("field_suc")

    """
    static void muro__sess_free_#{id}(#{nat} *p) {
      #{nat} *next;
      while (p) {
        next = p->#{tag} ? p->#{suc} : 0;
        muro__DROP(p);
        p = next;
      }
    }
    """
    |> String.trim()
  end

  defp free_body(:unit, id, _st) do
    unit = Name.gen("unit")

    """
    static void muro__sess_free_#{id}(#{unit} *p) {
      (void)p;
    }
    """
    |> String.trim()
  end

  defp free_body({:dat, name, args}, id, st) do
    if C.enum_type?(st.book, name) do
      ptr = build_ptr({:dat, name, args}, st)

      """
      static void muro__sess_free_#{id}(#{ptr}p) {
        (void)p;
      }
      """
      |> String.trim()
    else
      free_body_boxed_data(name, args, id, st)
    end
  end

  defp free_body(_ty, id, _st) do
    """
    static void muro__sess_free_#{id}(void *p) {
      (void)p;
    }
    """
    |> String.trim()
  end

  defp free_body_boxed_data(name, args, id, st) do
    data = Map.get(st.datas, name)
    decl = Map.get(st.decls, name)
    ptr = build_ptr({:dat, name, args}, st)
    tagf = Name.gen("field_tag")
    asf = Name.gen("as")

    arms =
      if is_nil(data) or is_nil(decl) do
        ""
      else
        data.ctors
        |> Enum.with_index()
        |> Enum.map_join("\n", fn {ctor, tag} ->
          free_ctor(name, ctor.name, tag, args, decl, st, asf)
        end)
      end

    """
    static void muro__sess_free_#{id}(#{ptr}p) {
      if (!p) return;
      switch (p->#{tagf}) {
    #{indent(arms, 4)}
        default: return;
      }
    }
    """
    |> String.trim()
  end

  defp free_ctor(dname, ctor, tag, args, decl, st, asf) do
    fields = Map.get(decl.ctors, ctor, [])
    inst = Enum.map(fields, &inst_field(&1, dname, args))
    member = C.source_id(ctor)

    if inst == [] do
      "case #{tag}: return;"
    else
      {_fun, ctypes} = ctor_info(st, dname, ctor)

      frees =
        inst
        |> Enum.with_index()
        |> Enum.map_join("\n", fn {ty, k} ->
          fid = Map.fetch!(st.builds, ty)
          field = "p->#{asf}.#{member}.#{Name.gen("f", k)}"
          ctype = Enum.at(ctypes, k) || "void *"
          "muro__sess_free_#{fid}(#{pay_load(field, ty, ctype, st)});"
        end)

      """
      case #{tag}: {
      #{indent(frees, 2)}
        muro__DROP(p);
        return;
      }
      """
      |> String.trim()
    end
  end

  defp build_ptr(:nat, _st), do: Name.gen("nat") <> " *"
  defp build_ptr(:unit, _st), do: Name.gen("unit") <> " *"

  defp build_ptr({:dat, name, _}, st) do
    spell = C.data_struct(name, st.prefix)

    if C.enum_type?(st.book, name) do
      spell <> " "
    else
      spell <> " *"
    end
  end

  defp build_ptr(_, _st), do: "void *"

  # A polymorphic field is `void *`. An enum scalar packed in that word
  # goes through `uintptr_t` both ways. A field whose slot is already
  # the enum type is stored and loaded as that type, with no pack.
  defp enum_pay?({:dat, name, _}, st), do: C.enum_type?(st.book, name)
  defp enum_pay?(_, _), do: false

  defp pay_store(ex, ty, ctype, st) do
    want = String.trim(ctype)

    if enum_pay?(ty, st) and want == "void *" do
      "(void *)(uintptr_t)(#{ex})"
    else
      "(#{want})#{ex}"
    end
  end

  defp pay_load(ex, ty, ctype, st) do
    want = String.trim(ctype)

    if enum_pay?(ty, st) and want == "void *" do
      "(#{String.trim(build_ptr(ty, st))})(uintptr_t)(#{ex})"
    else
      ex
    end
  end

  defp build_body(:nat, _st) do
    """
    #{Name.gen("nat")} *p;
    if (!v || v->tag != MURO_SESS_NAT || !out) return 2;
    p = muro__sess_nat_of(v->nat);
    if (!p) return 1;
    *out = p;
    return 0;
    """
    |> String.trim()
  end

  defp build_body(:unit, _st) do
    """
    if (!v || v->tag != MURO_SESS_UNIT || !out) return 2;
    *out = #{Name.gen("tt")}();
    return 0;
    """
    |> String.trim()
  end

  defp build_body({:dat, name, args}, st) do
    decl = Map.get(st.decls, name)
    spell = C.source_id(name)

    if is_nil(decl) do
      "return 2;"
    else
      arms =
        Enum.map_join(decl.order, "\n", fn ctor ->
          build_ctor(name, ctor, args, decl, st)
        end)

      """
      {
        const char *tag;
        if (!v || v->tag != MURO_SESS_DATA || !out) return 2;
        tag = muro__sess_src_#{spell}(v->ctor);
        if (!tag) return 2;
      #{indent(arms, 2)}
        return 2;
      }
      """
      |> String.trim()
    end
  end

  defp build_body(_, _st), do: "return 2;"

  defp build_ctor(dname, ctor, args, decl, st) do
    fields = Map.get(decl.ctors, ctor, [])
    inst = Enum.map(fields, &inst_field(&1, dname, args))
    {fun, ctypes} = ctor_info(st, dname, ctor)

    if length(ctypes) != length(inst) do
      """
      if (strcmp(tag, #{c_str(ctor)}) == 0) return 2;
      """
      |> String.trim()
    else
      n = length(inst)

      decls =
        inst
        |> Enum.with_index()
        |> Enum.map_join("\n", fn {ty, i} ->
          "#{build_ptr(ty, st)}f#{i} = 0;"
        end)

      built =
        inst
        |> Enum.with_index()
        |> Enum.map_join("\n", fn {ty, i} ->
          id = Map.fetch!(st.builds, ty)

          prior =
            inst
            |> Enum.take(i + 1)
            |> Enum.with_index()
            |> Enum.map_join("\n", fn {pty, j} ->
              "muro__sess_free_#{Map.fetch!(st.builds, pty)}(f#{j});"
            end)

          """
          {
            int rc = muro__sess_build_#{id}(&v->a[#{i}], st, &f#{i});
            if (rc) {
          #{indent(prior, 4)}
              return rc;
            }
          }
          """
          |> String.trim()
        end)

      call_args =
        inst
        |> Enum.with_index()
        |> Enum.map_join(", ", fn {ty, i} ->
          ctype = Enum.at(ctypes, i) |> String.trim()
          pay_store("f#{i}", ty, ctype, st)
        end)

      call = if n == 0, do: "#{fun}()", else: "#{fun}(#{call_args})"

      """
      if (strcmp(tag, #{c_str(ctor)}) == 0) {
        if (!out) return 2;
        if (v->n != #{n}) return 2;
        if (#{n} && !v->a) return 2;
      #{indent(decls, 2)}
      #{indent(built, 2)}
        *out = #{call};
        return 0;
      }
      """
      |> String.trim()
    end
  end

  defp ctor_info(st, dname, cname) do
    data = Map.fetch!(st.datas, dname)
    ctor = Enum.find(data.ctors, &(&1.name == cname))
    fun = Map.fetch!(st.nm.ctors, {dname, cname})
    {fun, live_field_ctypes(ctor.type, st)}
  end

  defp live_field_ctypes(ty, st) do
    ty
    |> telescope([])
    |> Enum.flat_map(fn
      {:erased, _, _} -> []
      {_, dom, _} -> [pay_ctype(dom, st)]
    end)
  end

  defp telescope({:pi, q, a, _x, b}, acc), do: telescope(b, [{q, a, nil} | acc])
  defp telescope(_ty, acc), do: Enum.reverse(acc)

  defp pay_ctype(:nat, _st), do: Name.gen("nat") <> " *"
  defp pay_ctype(:unit, _st), do: Name.gen("unit") <> " *"
  defp pay_ctype({:var, name}, st), do: ptr_or_void(name, st)
  defp pay_ctype({:def, name}, st), do: ptr_or_void(name, st)
  defp pay_ctype({:app, f, _a}, st), do: pay_ctype(f, st)
  defp pay_ctype({:data, name}, st), do: ptr_or_void(name, st)
  defp pay_ctype(_, _st), do: "void *"

  defp ptr_or_void(name, st) do
    if Enum.any?(st.book, &(Map.get(&1, :kind) == :data and &1.name == name)) do
      build_ptr({:dat, name, []}, st)
    else
      "void *"
    end
  end

  defp label_src(st) do
    [end_of_src(st), label_fn(st), done_fn(st), exp_fn(st), fill_fn()]
    |> Enum.join("\n\n")
  end

  defp end_of_src(st) do
    arms =
      st.sessions
      |> Enum.with_index(1)
      |> Enum.map_join("\n", fn {sess, key} ->
        "    case #{key}: return #{c_str(sess.end_step)};"
      end)

    """
    static const char *muro__sess_end_of(uint16_t key) {
      switch (key) {
    #{arms}
        default: return "";
      }
    }
    """
    |> String.trim()
  end

  defp label_fn(st) do
    arms =
      st.nodes
      |> Map.values()
      |> Enum.sort_by(& &1.id)
      |> Enum.map_join("\n", fn node ->
        "    case #{node.id}: return #{c_str(node.step)};"
      end)

    """
    static const char *muro__sess_label(uint16_t key, uint16_t at) {
      if (at == 0) return muro__sess_end_of(key);
      switch (at) {
    #{arms}
        default: return muro__sess_end_of(key);
      }
    }
    """
    |> String.trim()
  end

  defp done_fn(st) do
    arms =
      st.nodes
      |> Map.values()
      |> Enum.filter(&(&1.kind == :end))
      |> Enum.sort_by(& &1.id)
      |> Enum.map_join("\n", fn node ->
        "    case #{node.id}: return #{owner_test(st, node.id)};"
      end)

    """
    static int muro__sess_is_done(uint16_t key, uint16_t at, uint8_t stuck) {
      (void)key;
      if (stuck || at == 0) return 0;
      switch (at) {
    #{arms}
        default: return 0;
      }
    }
    """
    |> String.trim()
  end

  defp owner_test(st, id) do
    names = st.owners |> Map.get(id, MapSet.new()) |> MapSet.to_list()

    case names do
      [] ->
        "0"

      _ ->
        Enum.map_join(names, " || ", fn name -> "key == #{key_of(st, name)}" end)
    end
  end

  defp exp_fn(st) do
    arms =
      st.nodes
      |> Map.values()
      |> Enum.sort_by(& &1.id)
      |> Enum.map_join("\n", fn node ->
        body = seg_stmt(node_segs(node, st))

        """
        case #{node.id}:
        #{indent(body, 2)}
          break;
        """
        |> String.trim()
      end)

    """
    static void muro__sess_exp_at(uint16_t at, const muro__sess_st *st, char *buf, size_t n) {
      size_t i = 0;
      (void)st;
      if (!buf || n == 0) return;
      buf[0] = 0;
      switch (at) {
    #{indent(arms, 4)}
        default:
          muro__sess_puts(buf, n, &i, "done");
          break;
      }
    }
    """
    |> String.trim()
  end

  defp fill_fn do
    """
    static void muro__sess_fill(muro__sess_res *res) {
      res->done = muro__sess_is_done(res->state.key, res->state.at, res->state.stuck);
      if (res->state.stuck || res->state.at == 0) {
        muro__sess_lit(res->expected, sizeof res->expected, "done");
        return;
      }
      muro__sess_exp_at(res->state.at, &res->state, res->expected, sizeof res->expected);
    }
    """
    |> String.trim()
  end

  defp session_src(sess, st) do
    fun = sess_fun(st, sess.name)
    key = key_of(st, sess.name)
    nodes = owned_nodes(st, sess.name)
    init = Map.get(st.inits, sess.name, {:stuck})
    slots = param_slots(st, sess.name)

    [
      init_src(fun, key, sess, slots, init, st),
      step_src(fun, key, sess.end_step, nodes, st),
      step_word_src(fun),
      query_src(fun, key, sess.end_step)
    ]
    |> Enum.join("\n\n")
  end

  defp init_src(fun, key, sess, slots, prog, st) do
    binds =
      slots
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {slot, i} ->
        """
        res->state.nat[#{slot}] = a#{i};
        res->state.set[#{slot}] = 1;
        """
        |> String.trim()
      end)

    """
    muro__sess_res #{fun}_init(#{init_params(sess)}) {
      muro__sess_res out;
      muro__sess_res *res = &out;
      int fail = 0;
      int cap = 0;
      memset(res, 0, sizeof *res);
      res->status = MURO_SESS_OK;
      res->state.key = #{key};
    #{indent(binds, 2)}
    #{indent(prog_c(prog, st), 2)}
      (void)fail;
      (void)cap;
      if (res->state.stuck || res->state.at == 0) {
        res->state.stuck = 1;
        res->state.at = 0;
        res->state.key = #{key};
      }
      res->step = muro__sess_label(res->state.key, res->state.at);
      muro__sess_fill(res);
      return out;
    }
    """
    |> String.trim()
  end

  defp step_src(fun, key, end_step, nodes, st) do
    arms =
      Enum.map_join(nodes, "\n", fn node ->
        """
        case #{node.id}: {
        #{indent(node_body(node, st), 2)}
          break;
        }
        """
        |> String.trim()
      end)

    """
    muro__sess_res #{fun}_step(muro__sess_st st, int dir, const muro__sess_val *value) {
      muro__sess_res out;
      muro__sess_res *res = &out;
      const muro__sess_st *saved = &st;
      (void)dir;
      (void)value;
      memset(res, 0, sizeof *res);
      res->state = st;
      if (dir != MURO_SESS_SEND && dir != MURO_SESS_RECV) {
        res->status = MURO_SESS_UNEXPECTED;
        res->step = #{c_str(end_step)};
        muro__sess_lit(res->expected, sizeof res->expected, "done");
        res->done = st.key == #{key} ? muro__sess_is_done(st.key, st.at, st.stuck) : 0;
        return out;
      }
      if (st.key != #{key}) {
        res->status = MURO_SESS_UNEXPECTED;
        res->step = #{c_str(end_step)};
        muro__sess_lit(res->expected, sizeof res->expected, "done");
        return out;
      }
      if (st.stuck) {
        res->status = MURO_SESS_UNEXPECTED;
        res->step = muro__sess_label(st.key, st.at);
        muro__sess_lit(res->expected, sizeof res->expected, "done");
        return out;
      }
      switch (st.at) {
    #{indent(arms, 4)}
        default:
          res->status = MURO_SESS_UNEXPECTED;
          res->step = #{c_str(end_step)};
          muro__sess_lit(res->expected, sizeof res->expected, "done");
          break;
      }
      return out;
    }
    """
    |> String.trim()
  end

  defp query_src(fun, key, end_step) do
    """
    int #{fun}_done(muro__sess_st st) {
      if (st.key != #{key}) return 0;
      return muro__sess_is_done(st.key, st.at, st.stuck);
    }

    const char *#{fun}_at(muro__sess_st st) {
      if (st.key != #{key}) return #{c_str(end_step)};
      return muro__sess_label(st.key, st.at);
    }

    void #{fun}_expected(muro__sess_st st, char *buf, size_t n) {
      if (!buf || n == 0) return;
      if (st.key != #{key} || st.stuck || st.at == 0) {
        muro__sess_lit(buf, n, "done");
        return;
      }
      muro__sess_exp_at(st.at, &st, buf, n);
    }
    """
    |> String.trim()
  end

  defp node_body(%{kind: :end} = node, _st) do
    """
    res->status = MURO_SESS_UNEXPECTED;
    res->state = *saved;
    res->step = #{c_str(node.step)};
    muro__sess_lit(res->expected, sizeof res->expected, "done");
    res->done = muro__sess_is_done(saved->key, saved->at, saved->stuck);
    """
    |> String.trim()
  end

  defp node_body(%{kind: kind} = node, st) when kind in [:send, :recv, :dsend, :drecv] do
    id = Map.fetch!(st.checks, {node.template, node.ty})
    dir = dir_const(kind_dir(kind))

    """
    if (dir != #{dir} || !muro__sess_pay_#{id}(value, saved)) {
    #{indent(refuse_node(node), 2)}
    } else {
      int fail = 0;
      int cap = 0;
    #{indent(bind_slot(node.slot), 2)}
    #{indent(prog_c(node.prog, st), 2)}
    #{indent(conclude(node), 2)}
    }
    """
    |> String.trim()
  end

  defp node_body(%{kind: kind} = node, st) when kind in [:esend, :erecv] do
    dir = dir_const(kind_dir(kind))

    """
    {
      int within = 0;
      if (value && value->tag == MURO_SESS_NAT) {
        uint64_t max = 0;
        int have = 0;
    #{indent(bound_have(node.bound), 4)}
        if (have && value->nat <= max) within = 1;
      }
      if (dir != #{dir} || !within) {
    #{indent(refuse_node(node), 4)}
      } else {
        int fail = 0;
        int cap = 0;
    #{indent(bind_slot(node.slot), 4)}
    #{indent(prog_c(node.prog, st), 4)}
    #{indent(conclude(node), 4)}
      }
    }
    """
    |> String.trim()
  end

  defp node_body(%{kind: kind} = node, st) when kind in [:isend, :irecv, :choose, :branch] do
    dir = dir_const(kind_dir(kind))
    tag = if kind in [:choose, :branch], do: "MURO_SESS_PICK", else: "MURO_SESS_BIT"

    """
    {
      int arm = -1;
      if (value && value->tag == #{tag} && value->bit <= 1) arm = (int)value->bit;
      if (dir != #{dir} || arm < 0) {
    #{indent(refuse_node(node), 4)}
      } else {
        int fail = 0;
        int cap = 0;
        if (arm == 0) {
    #{indent(prog_c(node.left, st), 6)}
        } else {
    #{indent(prog_c(node.right, st), 6)}
        }
    #{indent(conclude(node), 4)}
      }
    }
    """
    |> String.trim()
  end

  defp node_body(node, _st) do
    refuse_node(node)
  end

  defp refuse_node(node) do
    """
    res->status = MURO_SESS_UNEXPECTED;
    res->state = *saved;
    res->step = #{c_str(node.step)};
    muro__sess_exp_at(#{node.id}, saved, res->expected, sizeof res->expected);
    res->done = muro__sess_is_done(saved->key, saved->at, saved->stuck);
    """
    |> String.trim()
  end

  defp conclude(node) do
    step = c_str(node.step)

    """
    if (cap) {
      res->state = *saved;
      res->status = MURO_SESS_UNEXPECTED;
      res->step = #{step};
      muro__sess_lit(res->expected, sizeof res->expected, "nat_at_most #{@cap}");
      res->done = muro__sess_is_done(saved->key, saved->at, saved->stuck);
    } else if (fail) {
      muro__sess_exp_at(#{node.id}, saved, res->expected, sizeof res->expected);
      res->state = *saved;
      res->status = MURO_SESS_UNEXPECTED;
      res->step = #{step};
      res->done = muro__sess_is_done(saved->key, saved->at, saved->stuck);
    } else {
      res->status = MURO_SESS_OK;
      res->step = #{step};
      muro__sess_fill(res);
    }
    """
    |> String.trim()
  end

  defp bind_slot(nil), do: ""

  defp bind_slot(slot) when is_integer(slot) do
    """
    if (value && value->tag == MURO_SESS_NAT) {
      res->state.nat[#{slot}] = value->nat;
      res->state.set[#{slot}] = 1;
    }
    """
    |> String.trim()
  end

  defp bound_have({:lit, n}) do
    """
    max = #{n}ull;
    have = 1;
    """
    |> String.trim()
  end

  defp bound_have({:overflow}) do
    "have = 0;"
  end

  defp bound_have({:ix, id}) do
    "have = muro__sess_ix_#{id}(saved, &max);"
  end

  defp prog_c({:land, id}, _st) do
    """
    res->state.at = #{id};
    res->state.stuck = 0;
    """
    |> String.trim()
  end

  defp prog_c({:stuck}, _st), do: "res->state.stuck = 1;"
  defp prog_c({:fail}, _st), do: "fail = 1;"

  defp prog_c({:jump, slots, ixs, inner}, st) do
    n = length(ixs)

    evals =
      ixs
      |> Enum.with_index()
      |> Enum.map_join("\n", fn
        {{:lit, k}, i} ->
          "jv[#{i}] = #{k}ull;"

        {{:ix, id}, i} ->
          "if (jok && !muro__sess_ix_#{id}(&res->state, &jv[#{i}])) jok = 0;"

        {_, i} ->
          "jv[#{i}] = 0; jok = 0;"
      end)

    writes =
      slots
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {slot, i} ->
        """
        res->state.nat[#{slot}] = jv[#{i}];
        res->state.set[#{slot}] = 1;
        """
        |> String.trim()
      end)

    decl = if n == 0, do: "(void)0;", else: "uint64_t jv[#{n}];"

    """
    {
      int jok = 1;
    #{indent(decl, 2)}
    #{indent(evals, 2)}
      if (!jok) {
        res->state.stuck = 1;
      } else {
        memset(res->state.set, 0, sizeof res->state.set);
    #{indent(writes, 4)}
    #{indent(prog_c(inner, st), 4)}
      }
    }
    """
    |> String.trim()
  end

  defp prog_c({:name_case, :bit, arms}, st) do
    branches = arm_branches(arms, st)

    """
    {
      const char *tag = 0;
      if (value && value->tag == MURO_SESS_BIT && value->bit == 0) tag = "b0";
      else if (value && value->tag == MURO_SESS_BIT && value->bit == 1) tag = "b1";
      if (!tag) fail = 1;
    #{indent(branches, 2)}
      else fail = 1;
    }
    """
    |> String.trim()
  end

  defp prog_c({:name_case, {:dat, name, _}, arms}, st) do
    spell = C.source_id(name)
    branches = arm_branches(arms, st)

    """
    {
      const char *tag = 0;
      if (value && value->tag == MURO_SESS_DATA)
        tag = muro__sess_src_#{spell}(value->ctor);
      if (!tag) fail = 1;
    #{indent(branches, 2)}
      else fail = 1;
    }
    """
    |> String.trim()
  end

  defp prog_c({:name_case, _, _}, _st), do: "fail = 1;"

  defp prog_c({:run_case, info, _ty, arms}, st) do
    tagf = Name.gen("field_tag")
    ret = info.spell
    arm_map = Map.new(arms)
    enum? = C.enum_type?(st.book, info.ret)
    miss = if String.ends_with?(String.trim(info.arg), "*"), do: " || !built", else: ""

    branches =
      info.ctors
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {ctor, idx} ->
        case Map.get(arm_map, ctor) do
          nil ->
            "case #{idx}: fail = 1; break;"

          prog ->
            """
            case #{idx}: {
            #{indent(prog_c(prog, st), 2)}
              break;
            }
            """
            |> String.trim()
        end
      end)

    got_line =
      if enum? do
        "#{ret} got = #{info.cname}(built);"
      else
        "#{ret} *got = #{info.cname}(built);"
      end

    tag_line = if enum?, do: "tag = (int)got;", else: "tag = (int)got->#{tagf};"

    inner =
      if enum? do
        """
        #{got_line}
        int tag = -1;
        #{tag_line}
        muro__sess_free_#{info.build}(built);
        switch (tag) {
        #{indent(branches, 8)}
          default: fail = 1; break;
        }
        """
      else
        """
        #{got_line}
        int tag = -1;
        if (!got) {
          muro__sess_free_#{info.build}(built);
          fail = 1;
        } else {
          #{tag_line}
          muro__sess_free_#{info.build}(built);
          switch (tag) {
        #{indent(branches, 10)}
            default: fail = 1; break;
          }
        }
        """
      end

    """
    {
      #{info.arg} built = 0;
      int rc = muro__sess_build_#{info.build}(value, &res->state, &built);
      if (rc == 1) {
        cap = 1;
      } else if (rc != 0#{miss}) {
        muro__sess_free_#{info.build}(built);
        fail = 1;
      } else {
    #{indent(String.trim(inner), 4)}
      }
    }
    """
    |> String.trim()
  end

  defp prog_c(_, _st), do: "fail = 1;"

  defp arm_branches(arms, st) do
    Enum.map_join(arms, "\n", fn {tag, prog} ->
      """
      else if (tag && strcmp(tag, #{c_str(tag)}) == 0) {
      #{indent(prog_c(prog, st), 2)}
      }
      """
      |> String.trim()
    end)
  end

  # One copy per book. Each session's step_word is the call. The tag is
  # written only after the kind matches, so an out-of-range int is not
  # stored in the uint8_t field.
  defp step_word_src(fun) do
    """
    muro__sess_res #{fun}_step_word(muro__sess_st st, int dir, int tag, uint64_t word) {
      return muro__sess_word_step(st, dir, tag, word, #{fun}_step);
    }
    """
    |> String.trim()
  end

  defp word_name_src(st) do
    rows = C.ctor_words(st.book, st.stem, st.prefix)

    body =
      if rows == [] do
        "(void)word;\nreturn 0;"
      else
        arms =
          Enum.map_join(rows, "\n", fn row ->
            "case #{row.word}: return #{c_str(row.ctor)};"
          end)

        """
        switch (word) {
        #{arms}
          default: return 0;
        }
        """
        |> String.trim()
      end

    """
    static muro__sess_res muro__sess_word_bad(muro__sess_st st) {
      muro__sess_res bad;
      memset(&bad, 0, sizeof bad);
      bad.status = MURO_SESS_UNEXPECTED;
      bad.state = st;
      bad.step = "";
      muro__sess_lit(bad.expected, sizeof bad.expected, "word");
      return bad;
    }

    static const char *muro__sess_word_name(uint64_t word) {
    #{indent(body, 2)}
    }

    static muro__sess_res muro__sess_word_step(
        muro__sess_st st, int dir, int tag, uint64_t word,
        muro__sess_res (*step)(muro__sess_st, int, const muro__sess_val *)) {
      muro__sess_val value;
      memset(&value, 0, sizeof value);
      if (tag == MURO_SESS_NAT) {
        value.tag = MURO_SESS_NAT;
        value.nat = word;
        return step(st, dir, &value);
      }
      if (tag == MURO_SESS_BIT || tag == MURO_SESS_PICK) {
        if (word > 1) return muro__sess_word_bad(st);
        value.tag = tag == MURO_SESS_BIT ? (uint8_t)MURO_SESS_BIT : (uint8_t)MURO_SESS_PICK;
        value.bit = (uint8_t)word;
        return step(st, dir, &value);
      }
      if (tag == MURO_SESS_UNIT) {
        value.tag = MURO_SESS_UNIT;
        return step(st, dir, &value);
      }
      if (tag == MURO_SESS_DATA) {
        const char *ctor = muro__sess_word_name(word);
        if (!ctor) return muro__sess_word_bad(st);
        value.tag = MURO_SESS_DATA;
        value.ctor = ctor;
        return step(st, dir, &value);
      }
      return muro__sess_word_bad(st);
    }
    """
    |> String.trim()
  end

  defp generic_src(st) do
    inits =
      Enum.map_join(st.sessions, "\n", fn sess ->
        fun = sess_fun(st, sess.name)
        n = length(sess.params)
        args = if n == 0, do: "", else: Enum.map_join(0..(n - 1), ", ", &"args[#{&1}]")

        """
        if (strcmp(name, #{c_str(sess.name)}) == 0 && n == #{n}#{if n == 0, do: "", else: " && args"}) {
          return #{fun}_init(#{args});
        }
        """
        |> String.trim()
      end)

    steps =
      Enum.map_join(st.sessions, "\n", fn sess ->
        fun = sess_fun(st, sess.name)

        """
        if (strcmp(name, #{c_str(sess.name)}) == 0) return #{fun}_step(st, dir, value);
        """
        |> String.trim()
      end)

    words =
      Enum.map_join(st.sessions, "\n", fn sess ->
        fun = sess_fun(st, sess.name)

        """
        if (strcmp(name, #{c_str(sess.name)}) == 0) return #{fun}_step_word(st, dir, tag, word);
        """
        |> String.trim()
      end)

    dones =
      Enum.map_join(st.sessions, "\n", fn sess ->
        fun = sess_fun(st, sess.name)
        "  if (name && strcmp(name, #{c_str(sess.name)}) == 0) return #{fun}_done(st);"
      end)

    ats =
      Enum.map_join(st.sessions, "\n", fn sess ->
        fun = sess_fun(st, sess.name)
        "  if (name && strcmp(name, #{c_str(sess.name)}) == 0) return #{fun}_at(st);"
      end)

    exps =
      Enum.map_join(st.sessions, "\n", fn sess ->
        fun = sess_fun(st, sess.name)

        """
        if (name && strcmp(name, #{c_str(sess.name)}) == 0) {
          #{fun}_expected(st, buf, n);
          return;
        }
        """
        |> String.trim()
      end)

    init_f = api(st, "init")
    step_f = api(st, "step")
    word_f = api(st, "step_word")
    done_f = api(st, "done")
    at_f = api(st, "at")
    exp_f = api(st, "expected")

    """
    muro__sess_res #{init_f}(const char *name, const uint64_t *args, size_t n) {
      muro__sess_res res;
      memset(&res, 0, sizeof res);
      res.status = MURO_SESS_INIT;
      res.step = "";
      muro__sess_lit(res.expected, sizeof res.expected, "done");
      (void)args;
      if (!name) return res;
    #{indent(inits, 2)}
      return res;
    }

    muro__sess_res #{step_f}(const char *name, muro__sess_st st, int dir, const muro__sess_val *value) {
      muro__sess_res res;
      memset(&res, 0, sizeof res);
      res.status = MURO_SESS_UNEXPECTED;
      res.state = st;
      res.step = "";
      muro__sess_lit(res.expected, sizeof res.expected, "done");
      if (!name) return res;
    #{indent(steps, 2)}
      return res;
    }

    muro__sess_res #{word_f}(const char *name, muro__sess_st st, int dir, int tag, uint64_t word) {
      muro__sess_res res;
      memset(&res, 0, sizeof res);
      res.status = MURO_SESS_UNEXPECTED;
      res.state = st;
      res.step = "";
      muro__sess_lit(res.expected, sizeof res.expected, "done");
      (void)dir;
      (void)tag;
      (void)word;
      if (!name) return res;
    #{indent(words, 2)}
      return res;
    }

    int #{done_f}(const char *name, muro__sess_st st) {
    #{dones}
      return 0;
    }

    const char *#{at_f}(const char *name, muro__sess_st st) {
    #{ats}
      return "";
    }

    void #{exp_f}(const char *name, muro__sess_st st, char *buf, size_t n) {
      if (!buf || n == 0) return;
      muro__sess_lit(buf, n, "done");
    #{indent(exps, 2)}
    }
    """
    |> String.trim()
  end

  defp key_of(st, name) do
    Enum.find_index(st.sessions, &(&1.name == name)) + 1
  end

  defp owned_nodes(st, name) do
    st.nodes
    |> Map.values()
    |> Enum.filter(fn node ->
      MapSet.member?(Map.get(st.owners, node.id, MapSet.new()), name)
    end)
    |> Enum.sort_by(& &1.id)
  end

  defp param_slots(st, name) do
    %{params: params} = Map.fetch!(st.templates, {:sess, name})

    Enum.map(params, fn p ->
      Map.fetch!(st.slots, {{:sess, name}, nm(p)})
    end)
  end

  defp kind_dir(kind) when kind in [:send, :dsend, :esend, :isend, :choose], do: :send
  defp kind_dir(_kind), do: :recv
  defp dir_const(:send), do: "MURO_SESS_SEND"
  defp dir_const(:recv), do: "MURO_SESS_RECV"

  defp node_segs(%{kind: :end}, _st), do: [{:s, "done"}]
  defp node_segs(%{kind: :choose}, _st), do: [{:s, "send_pick"}]
  defp node_segs(%{kind: :branch}, _st), do: [{:s, "recv_pick"}]

  defp node_segs(%{kind: kind, bound: bound}, _st) when kind in [:esend, :erecv] do
    dir_segs(kind_dir(kind), bound_segs(bound))
  end

  defp node_segs(%{kind: kind, ty: ty, template: template}, st)
       when kind in [:send, :recv, :dsend, :drecv, :isend, :irecv] do
    dir_segs(kind_dir(kind), ty_segs(ty, template, st))
  end

  defp node_segs(_, _st), do: [{:s, "done"}]

  defp bound_segs(bound), do: [{:s, "nat_at_most "}, num_seg(bound)]
  defp num_seg({:lit, n}), do: {:s, Integer.to_string(n)}
  defp num_seg({:overflow}), do: {:s, "0"}
  defp num_seg({:ix, id}), do: {:u, id}

  defp ty_segs(:nat, _template, _st), do: [{:s, "nat"}]
  defp ty_segs(:bit, _template, _st), do: [{:s, "bit"}]
  defp ty_segs(:unit, _template, _st), do: [{:s, "unit"}]

  defp ty_segs({:pair, a, b}, template, st) do
    [{:s, "pair "}] ++
      wrap_segs(ty_segs(a, template, st)) ++
      [{:s, " "}] ++ wrap_segs(ty_segs(b, template, st))
  end

  defp ty_segs({:rec, fields}, template, st) when is_list(fields) do
    [{:s, "record"}] ++
      Enum.flat_map(fields, fn {name, ty} ->
        [{:s, " " <> nm(name) <> " "}] ++ wrap_segs(ty_segs(ty, template, st))
      end)
  end

  defp ty_segs({:vec, elem, ix}, template, st) do
    [{:s, "vec "}] ++
      wrap_segs(ty_segs(elem, template, st)) ++ [{:s, " "}, len_seg(ix, template, st)]
  end

  defp ty_segs({:dat, name, args}, template, st) when is_binary(name) and is_list(args) do
    [{:s, "data " <> name}] ++
      Enum.flat_map(args, fn arg ->
        [{:s, " "}] ++ wrap_segs(ty_segs(arg, template, st))
      end)
  end

  defp ty_segs(_, _template, _st), do: [{:s, "nat"}]

  defp len_seg(ix, template, st) do
    case fold_ix(ix) do
      {:lit, n} ->
        {:s, Integer.to_string(n)}

      :overflow ->
        {:s, "0"}

      expr ->
        {:u, Map.fetch!(st.ixs, {template, expr})}
    end
  end

  defp dir_segs(dir, segs) do
    word = if dir == :send, do: "send ", else: "recv "
    inner = if bare?(flatten_segs(segs)), do: flatten_segs(segs), else: wrap_segs(segs)
    [{:s, word} | inner]
  end

  defp wrap_segs(segs) do
    segs = flatten_segs(segs)
    if bare?(segs), do: segs, else: [{:s, "("} | segs] ++ [{:s, ")"}]
  end

  defp bare?([{:s, s}]) when s in ["nat", "bit", "unit"], do: true
  defp bare?(_), do: false

  defp flatten_segs(segs) do
    segs
    |> Enum.reduce([], fn
      {:s, s}, [{:s, prev} | rest] -> [{:s, prev <> s} | rest]
      other, acc -> [other | acc]
    end)
    |> Enum.reverse()
  end

  defp seg_stmt(segs) do
    segs
    |> flatten_segs()
    |> Enum.map_join("\n", fn
      {:s, s} ->
        "muro__sess_puts(buf, n, &i, #{c_str(s)});"

      {:u, id} ->
        """
        {
          uint64_t num = 0;
          if (!muro__sess_ix_#{id}(st, &num)) num = 0;
          muro__sess_putu(buf, n, &i, num);
        }
        """
        |> String.trim()
    end)
  end

  defp c_str(text) do
    escaped =
      text
      |> to_string()
      |> String.replace("\\", "\\\\")
      |> String.replace("\"", "\\\"")
      |> String.replace("\n", "\\n")

    "\"#{escaped}\""
  end

  defp indent(text, n) do
    pad = String.duplicate(" ", n)

    text
    |> to_string()
    |> String.trim_trailing()
    |> String.split("\n")
    |> Enum.map_join("\n", fn
      "" -> ""
      line -> pad <> line
    end)
  end
end

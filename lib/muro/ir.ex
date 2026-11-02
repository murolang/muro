defmodule Muro.IR do
  @moduledoc """
  Closed `run` image of a checked book.

  This is the Elixir spelling of `agda/Muro/IR.agda`. Spec, evidence, motives,
  rewrite, and annotation are dropped. Erased λ-arguments are not elaborated.
  An atom is `{:con, "Atom", name, []}` over the names `Muro.Ast.atoms/1`
  collected, in that order. Nothing here builds an atom from a string.

  The named book keeps source binder names. Agda's de Bruijn `Tm` has lost
  them, so the same arm there is `b` plus the context length.

  Layouts: `:nat`, `:unit`, `:opaque`, `{:pair, a, b}`, `{:stream, a}`,
  `{:data, name}`. `{:data, name}` is `dataL`.
  """

  alias Muro.{Ast, Load, Prelude}

  @doc """
  Elaborate every `run` definition in `book`, which is a checked named book
  (`Muro.Load.file/1`, then `Muro.Prelude.for_emit/1`).

  Returns `{:ok, funs}` or `{:error, reason}` where `reason` is one of
  `c:lambda`, `c:machine`, `c:stream`, `c:erased`, `c:unsupported`.
  """
  def elaborate(book) when is_list(book) do
    st = %{book: book, atoms: Ast.atoms(book)}
    elab_runs(st, book, 0)
  end

  @doc """
  Check `path` and elaborate its run image.
  """
  def elaborate_file(path) when is_binary(path) do
    with {:ok, book} <- Load.file(path) do
      elaborate(Prelude.for_emit(book))
    end
  end

  defp elab_runs(_st, [], _k), do: {:ok, []}

  defp elab_runs(st, [d | ds], k) do
    cond do
      Map.get(d, :kind) == :data ->
        elab_runs(st, ds, k)

      Map.get(d, :mode) != :run ->
        elab_runs(st, ds, k)

      true ->
        with {:ok, {fun, steps, k1}} <- elab_fun(st, d, k),
             {:ok, rest} <- elab_runs(st, ds, k1) do
          {:ok, [fun | steps ++ rest]}
        end
    end
  end

  # One λ per Π. An erased Π or an erased λ drops that parameter.
  # Fewer λs than Πs is c:unsupported. A λ left over is elaborated, and a
  # value λ is c:lambda.
  defp elab_fun(st, %{name: name, type: ty, body: body} = d, k) do
    with {:ok, {params, ctx, inner, ret}} <- peel(st, [], [], ty, body),
         {:ok, e} <- elab(st, inner, ctx, k) do
      fun = %{
        name: name,
        export: Map.get(d, :export, true),
        params: params,
        ret: ret,
        body: e.tm
      }

      {:ok, {fun, e.steps, e.k}}
    end
  end

  defp peel(st, ctx, acc, {:pi, q, a, _x, b}, {:lam, q2, _dom, name, body}) do
    if q == :erased or q2 == :erased do
      peel(st, [{:gone, name} | ctx], acc, b, body)
    else
      with {:ok, lay} <- layout_of(st, a) do
        peel(st, [{:live, name, lay} | ctx], acc ++ [{name, lay}], b, body)
      end
    end
  end

  defp peel(_st, _ctx, _acc, {:pi, _, _, _, _}, _body), do: {:error, "c:unsupported"}

  defp peel(st, ctx, acc, ty, body) do
    with {:ok, lay} <- layout_of(st, ty) do
      {:ok, {acc, ctx, body, lay}}
    end
  end

  defp elab(st, t, ctx, k), do: apply(st, t, [], ctx, k)

  # A spine argument keeps the context it was written in. A λ consumes one
  # argument and elaborates its body in the extended context; arguments
  # already on the spine stay in the context they carry.
  defp apply(st, {:app, f, a}, args, ctx, k) do
    apply(st, f, [{a, ctx} | args], ctx, k)
  end

  defp apply(st, {:ann, e, _}, args, ctx, k), do: apply(st, e, args, ctx, k)
  defp apply(st, {:rwt, _, _, _, t}, args, ctx, k), do: apply(st, t, args, ctx, k)
  defp apply(st, {:rwt, _, _, t}, args, ctx, k), do: apply(st, t, args, ctx, k)

  defp apply(st, {:lam, :erased, _dom, name, body}, [_arg | rest], ctx, k) do
    apply(st, body, rest, [{:gone, name} | ctx], k)
  end

  defp apply(st, {:lam, _q, dom, name, body}, [{arg, actx} | rest], ctx, k) do
    with {:ok, lay} <- layout_of(st, dom),
         {:ok, ae} <- elab(st, arg, actx, k) do
      # A spec alias is opaque here. The argument keeps its own layout,
      # so a zero is a Nat and not the erased-field placeholder.
      blay = bind_layout(lay, ae.lay)

      with {:ok, be} <- apply(st, body, rest, [{:live, name, blay} | ctx], ae.k) do
        {:ok,
         %{
           tm: {:let, name, blay, ae.tm, be.tm},
           lay: be.lay,
           steps: ae.steps ++ be.steps,
           k: be.k
         }}
      end
    end
  end

  defp apply(st, {:var, name}, args, ctx, k), do: apply_name(st, name, args, ctx, k)
  defp apply(st, {:def, name}, args, ctx, k), do: apply_name(st, name, args, ctx, k)
  defp apply(st, {:atom, name}, args, _ctx, k), do: elab_atom(st, name, args, k)

  defp apply(st, t, [], ctx, k), do: elab_form(st, t, ctx, k)

  defp apply(_st, t, _args, _ctx, _k) do
    case bad_head(t) do
      nil -> {:error, "c:lambda"}
      reason -> {:error, reason}
    end
  end

  defp bind_layout(:opaque, lay), do: lay
  defp bind_layout(lay, _arg), do: lay

  defp apply_name(st, name, [], ctx, k) do
    case lookup(ctx, name) do
      {:live, lay} -> ok({:var, name}, lay, [], k)
      :gone -> {:error, "c:erased"}
      :miss -> global(st, name, [], k)
    end
  end

  defp apply_name(st, name, args, ctx, k) do
    case lookup(ctx, name) do
      :miss -> global(st, name, args, k)
      _ -> {:error, "c:lambda"}
    end
  end

  defp global(st, name, args, k) do
    cond do
      data = data_of_ctor(st.book, name) ->
        ctor = Enum.find(data.ctors, &(&1.name == name))
        finish_ctor(st, data, ctor, args, k)

      d = find_def(st.book, name) ->
        finish_def(st, d, args, k)

      true ->
        {:error, "c:unsupported"}
    end
  end

  defp finish_def(st, %{mode: :run, name: name, type: ty}, args, k) do
    with {:ok, {ts, steps, k1, lay}} <- zip_live(st, ty, args, k) do
      ok({:call, name, ts}, lay, steps, k1)
    end
  end

  defp finish_def(_st, _d, _args, _k), do: {:error, "c:unsupported"}

  defp finish_ctor(st, data, ctor, args, k) do
    with {:ok, {ts, steps, k1, _lay}} <- zip_live(st, ctor.type, args, k) do
      ok({:con, data.name, ctor.name, ts}, {:data, data.name}, steps, k1)
    end
  end

  # An unknown atom is refused before the arity check. A known atom with
  # an argument is an extra constructor argument.
  defp elab_atom(st, name, args, k) do
    cond do
      name not in st.atoms -> {:error, "c:unsupported"}
      args != [] -> {:error, "c:lambda"}
      true -> ok({:con, "Atom", name, []}, {:data, "Atom"}, [], k)
    end
  end

  defp zip_live(st, {:pi, :erased, _, _, b}, [_arg | rest], k) do
    zip_live(st, b, rest, k)
  end

  defp zip_live(st, {:pi, _q, _, _, b}, [{arg, actx} | rest], k) do
    with {:ok, e} <- elab(st, arg, actx, k),
         {:ok, {ts, steps, k1, lay}} <- zip_live(st, b, rest, e.k) do
      {:ok, {[e.tm | ts], e.steps ++ steps, k1, lay}}
    end
  end

  defp zip_live(_st, {:pi, _, _, _, _}, [], _k), do: {:error, "c:lambda"}

  defp zip_live(st, ty, [], k) do
    with {:ok, lay} <- layout_of(st, ty) do
      {:ok, {[], [], k, lay}}
    end
  end

  defp zip_live(_st, _ty, _args, _k), do: {:error, "c:lambda"}

  defp elab_form(_st, :ze, _ctx, k), do: ok(:ze, :nat, [], k)
  defp elab_form(_st, :one, _ctx, k), do: ok(:tt, :unit, [], k)

  defp elab_form(st, {:su, u}, ctx, k) do
    with {:ok, e} <- elab(st, u, ctx, k) do
      ok({:su, e.tm}, :nat, e.steps, e.k)
    end
  end

  defp elab_form(st, {:pair, a, b}, ctx, k) do
    with {:ok, ea} <- elab(st, a, ctx, k),
         {:ok, eb} <- elab(st, b, ctx, ea.k) do
      ok({:pair, ea.tm, eb.tm}, {:pair, ea.lay, eb.lay}, ea.steps ++ eb.steps, eb.k)
    end
  end

  defp elab_form(st, {:letp, e, a, b, body}, ctx, k) do
    with {:ok, ee} <- elab(st, e, ctx, k) do
      {la, lb} = pair_halves(ee.lay)
      bctx = [{:live, b, lb}, {:live, a, la} | ctx]

      with {:ok, be} <- elab(st, body, bctx, ee.k) do
        ok({:letp, a, b, ee.tm, be.tm}, be.lay, ee.steps ++ be.steps, be.k)
      end
    end
  end

  defp elab_form(st, {:ucons, s}, ctx, k) do
    with {:ok, e} <- elab(st, s, ctx, k) do
      ok({:uncons, e.tm}, uncons_lay(e.lay), e.steps, e.k)
    end
  end

  # The suc arm is already open. `y` is the predecessor.
  defp elab_form(st, {:mnat, e, mx, mot, z, y, s}, ctx, k) do
    with {:ok, ee} <- elab(st, e, ctx, k),
         {:ok, ze} <- elab(st, z, ctx, ee.k),
         {:ok, se} <- elab(st, s, [{:live, y, :nat} | ctx], ze.k),
         {:ok, rlay} <- motive_lay(st, mot, ee.lay, mx) do
      arms = [
        {:arm, "zero", [], ze.tm},
        {:arm, "suc", [y], se.tm}
      ]

      ok({:match, ee.tm, arms}, rlay, ee.steps ++ ze.steps ++ se.steps, se.k)
    end
  end

  defp elab_form(st, {:mdata, e, mx, mot, bs}, ctx, k) do
    with {:ok, ee} <- elab(st, e, ctx, k),
         {:ok, dname} <- data_key(ee.lay),
         {:ok, data} <- find_data(st.book, dname),
         :ok <- branch_count(data.ctors, bs),
         {:ok, {arms, steps, k1}} <- elab_arms(st, data.ctors, bs, ctx, ee.k),
         {:ok, rlay} <- motive_lay(st, mot, ee.lay, mx) do
      ok({:match, ee.tm, arms}, rlay, ee.steps ++ steps, k1)
    end
  end

  defp elab_form(st, {:matom, e, mx, mot, bs}, ctx, k) do
    with {:ok, ee} <- elab(st, e, ctx, k),
         :ok <- atom_key(ee.lay),
         :ok <- atom_cover(st.atoms, bs),
         {:ok, {arms, steps, k1}} <- elab_atom_arms(st, st.atoms, bs, ctx, ee.k),
         {:ok, rlay} <- motive_lay(st, mot, ee.lay, mx) do
      ok({:match, ee.tm, arms}, rlay, ee.steps ++ steps, k1)
    end
  end

  defp elab_form(st, {:memp, e, mx, mot}, ctx, k) do
    with {:ok, ee} <- elab(st, e, ctx, k),
         {:ok, rlay} <- motive_lay(st, mot, ee.lay, mx) do
      ok({:let, fresh(ctx), ee.lay, ee.tm, :abort}, rlay, ee.steps, ee.k)
    end
  end

  defp elab_form(st, {:munit, e, _mx, _mot, u}, ctx, k) do
    with {:ok, ee} <- elab(st, e, ctx, k),
         {:ok, ue} <- elab(st, u, ctx, ee.k) do
      ok({:let, fresh(ctx), :unit, ee.tm, ue.tm}, ue.lay, ee.steps ++ ue.steps, ue.k)
    end
  end

  defp elab_form(st, {:unf, seed, {:lam, q, dom, name, body}}, ctx, k) do
    with {:ok, ee} <- elab(st, seed, ctx, k),
         {:ok, dlay} <- layout_of(st, dom) do
      caps = captures(body, name, ctx)
      id = ee.k

      with {:ok, be} <- elab(st, body, seed_ctx(q, name, dlay, ctx), id + 1) do
        # `generated` is provenance. The name `stepN` is not: a source
        # run may be called `stepN` and take the same binders.
        step = %{
          name: "step#{id}",
          export: false,
          generated: true,
          params: cap_params(caps) ++ seed_param(q, name, dlay),
          ret: be.lay,
          body: be.tm
        }

        ok(
          {:stream, ee.tm, cap_terms(caps), "step#{id}"},
          {:stream, dlay},
          ee.steps ++ be.steps ++ [step],
          be.k
        )
      end
    end
  end

  defp elab_form(_st, {:unf, _, _}, _ctx, _k), do: {:error, "c:lambda"}
  defp elab_form(_st, {:lam, _, _, _, _}, _ctx, _k), do: {:error, "c:lambda"}

  defp elab_form(_st, t, _ctx, _k) do
    case bad_head(t) do
      nil -> {:error, "c:unsupported"}
      reason -> {:error, reason}
    end
  end

  defp elab_arms(_st, [], [], _ctx, k), do: {:ok, {[], [], k}}

  defp elab_arms(st, [c | cs], [{cname, binders, body} | bs], ctx, k) do
    if c.name != cname do
      {:error, "c:unsupported"}
    else
      with {:ok, {bctx, wraps}} <- open_ctor(st, c.type, binders, ctx),
           {:ok, e} <- elab(st, body, bctx, k),
           {:ok, {arms, steps, k1}} <- elab_arms(st, cs, bs, ctx, e.k) do
        {names, tm} = wrap(wraps, e.tm)
        {:ok, {[{:arm, cname, names, tm} | arms], e.steps ++ steps, k1}}
      end
    end
  end

  defp elab_arms(_st, _cs, _bs, _ctx, _k), do: {:error, "c:unsupported"}

  defp elab_atom_arms(_st, [], _bs, _ctx, k), do: {:ok, {[], [], k}}

  defp elab_atom_arms(st, [name | names], bs, ctx, k) do
    case Enum.find(bs, fn {n, _} -> n == name end) do
      nil ->
        {:error, "c:unsupported"}

      {^name, body} ->
        with {:ok, e} <- elab(st, body, ctx, k),
             {:ok, {arms, steps, k1}} <- elab_atom_arms(st, names, bs, ctx, e.k) do
          {:ok, {[{:arm, name, [], e.tm} | arms], e.steps ++ steps, k1}}
        end
    end
  end

  # An erased constructor field is omitted from the arm and wrapped as
  # `Let x opaque Ze`, so a use is `Var`.
  defp open_ctor(st, ty, binders, ctx) do
    pis = telescope(ty)

    if length(pis) != length(binders) do
      {:error, "c:unsupported"}
    else
      open_fields(st, Enum.zip(pis, binders), ctx, [])
    end
  end

  defp open_fields(_st, [], ctx, wraps), do: {:ok, {ctx, wraps}}

  defp open_fields(st, [{{:erased, _, _}, bname} | rest], ctx, wraps) do
    open_fields(st, rest, [{:live, bname, :opaque} | ctx], wraps ++ [{:gone, bname}])
  end

  defp open_fields(st, [{{_q, a, _}, bname} | rest], ctx, wraps) do
    with {:ok, lay} <- layout_of(st, a) do
      open_fields(st, rest, [{:live, bname, lay} | ctx], wraps ++ [{:live, bname}])
    end
  end

  defp wrap([], tm), do: {[], tm}

  defp wrap([{:live, x} | ws], tm) do
    {names, inner} = wrap(ws, tm)
    {[x | names], inner}
  end

  defp wrap([{:gone, x} | ws], tm) do
    {names, inner} = wrap(ws, tm)
    {names, {:let, x, :opaque, :ze, inner}}
  end

  defp telescope(t), do: telescope(t, [])
  defp telescope({:pi, q, a, x, b}, acc), do: telescope(b, [{q, a, x} | acc])
  defp telescope(_t, acc), do: Enum.reverse(acc)

  defp branch_count(ctors, bs) do
    cond do
      ctors == [] -> {:error, "c:unsupported"}
      length(ctors) != length(bs) -> {:error, "c:unsupported"}
      true -> :ok
    end
  end

  defp atom_cover([], _bs), do: {:error, "c:unsupported"}

  defp atom_cover(atoms, bs) do
    got = Enum.map(bs, fn {n, _} -> n end)

    cond do
      length(got) != length(Enum.uniq(got)) -> {:error, "c:unsupported"}
      Enum.sort(got) != Enum.sort(atoms) -> {:error, "c:unsupported"}
      true -> :ok
    end
  end

  defp atom_key({:data, "Atom"}), do: :ok
  defp atom_key(_), do: {:error, "c:unsupported"}

  # `var` of the motive binder is the scrutinee. `{:stream, A}` is the
  # named spelling of `ν X. A × X`.
  defp layout_of(_st, :nat), do: {:ok, :nat}
  defp layout_of(_st, :unit), do: {:ok, :unit}
  defp layout_of(_st, :typ), do: {:ok, :opaque}
  defp layout_of(_st, {:pi, _, _, _, _}), do: {:ok, :opaque}
  defp layout_of(_st, :empty), do: {:ok, :opaque}
  defp layout_of(_st, {:idt, _, _, _}), do: {:ok, :opaque}
  defp layout_of(_st, :atom), do: {:ok, {:data, "Atom"}}

  defp layout_of(st, {:var, name}) do
    if data?(st.book, name), do: {:ok, {:data, name}}, else: {:ok, :opaque}
  end

  defp layout_of(st, {:def, name}), do: layout_of(st, {:var, name})
  defp layout_of(st, {:app, f, _}), do: layout_of(st, f)
  defp layout_of(st, {:ann, e, _}), do: layout_of(st, e)
  defp layout_of(st, {:rwt, _, _, _, t}), do: layout_of(st, t)
  defp layout_of(st, {:rwt, _, _, t}), do: layout_of(st, t)

  defp layout_of(st, {:prod, a, b}) do
    with {:ok, la} <- layout_of(st, a),
         {:ok, lb} <- layout_of(st, b) do
      {:ok, {:pair, la, lb}}
    end
  end

  defp layout_of(st, {:stream, a}) do
    with {:ok, lay} <- layout_of(st, a) do
      {:ok, {:stream, lay}}
    end
  end

  defp layout_of(st, {:nu, x, {:prod, a, {:var, x}}}) do
    with {:ok, lay} <- layout_of(st, a) do
      {:ok, {:stream, lay}}
    end
  end

  defp layout_of(_st, {:nu, _, _}), do: {:error, "c:stream"}
  defp layout_of(_st, {:nu, _}), do: {:error, "c:stream"}
  defp layout_of(_st, t), do: head_refusal(t)

  defp motive_lay(st, {:lam, _, _, x, body}, scr, _binder), do: motive_lay(st, body, scr, x)
  defp motive_lay(_st, {:var, x}, scr, x), do: {:ok, scr}
  defp motive_lay(st, t, _scr, _binder), do: layout_of(st, t)

  defp head_refusal(t) do
    case bad_head(t) do
      nil -> {:error, "c:unsupported"}
      reason -> {:error, reason}
    end
  end

  defp bad_head(:i64), do: "c:machine"
  defp bad_head(:f32ty), do: "c:machine"
  defp bad_head({:tensor, _, _}), do: "c:machine"
  defp bad_head({:addi, _, _}), do: "c:machine"
  defp bad_head({:muli, _, _}), do: "c:machine"
  defp bad_head({:addt, _, _}), do: "c:machine"
  defp bad_head({:toi64, _}), do: "c:machine"
  defp bad_head({:packi, _, _}), do: "c:machine"
  defp bad_head({:nu, _}), do: "c:stream"
  defp bad_head({:nu, _, _}), do: "c:stream"
  defp bad_head({:always, _, _, _}), do: "c:stream"
  defp bad_head({:always, _, _}), do: "c:stream"
  defp bad_head({:bisim, _, _}), do: "c:stream"
  defp bad_head(_), do: nil

  defp pair_halves({:pair, a, b}), do: {a, b}
  defp pair_halves(_), do: {:opaque, :opaque}

  defp uncons_lay({:stream, s}), do: {:pair, :opaque, {:stream, s}}
  defp uncons_lay(_), do: {:pair, :opaque, :opaque}

  defp data_key({:data, name}), do: {:ok, name}
  defp data_key(_), do: {:error, "c:unsupported"}

  defp find_data(book, name) do
    case Enum.find(book, &(Map.get(&1, :kind) == :data and &1.name == name)) do
      nil -> {:error, "c:unsupported"}
      d -> {:ok, d}
    end
  end

  defp data?(book, name) do
    Enum.any?(book, &(Map.get(&1, :kind) == :data and &1.name == name))
  end

  defp data_of_ctor(book, name) do
    Enum.find(book, fn
      %{kind: :data, ctors: cs} -> Enum.any?(cs, &(&1.name == name))
      _ -> false
    end)
  end

  defp find_def(book, name) do
    Enum.find(book, fn d ->
      Map.get(d, :kind, :def) not in [:data, :relay, :repr] and Map.get(d, :name) == name and
        Map.has_key?(d, :type)
    end)
  end

  defp seed_ctx(:erased, name, _lay, ctx), do: [{:gone, name} | ctx]
  defp seed_ctx(_q, name, lay, ctx), do: [{:live, name, lay} | ctx]

  defp seed_param(:erased, _name, _lay), do: []
  defp seed_param(_q, name, lay), do: [{name, lay}]

  defp cap_params(caps), do: Enum.map(caps, fn {name, lay, _} -> {name, lay} end)
  defp cap_terms(caps), do: Enum.map(caps, fn {name, _, tm} -> {name, tm} end)

  defp captures(body, binder, ctx) do
    body
    |> free_names(MapSet.new([binder]))
    |> uniq()
    |> Enum.flat_map(fn name ->
      case lookup(ctx, name) do
        {:live, lay} -> [{name, lay, {:var, name}}]
        _ -> []
      end
    end)
  end

  defp free_names({:var, name}, bound) do
    if MapSet.member?(bound, name), do: [], else: [name]
  end

  defp free_names({:lam, _, a, x, t}, bound) do
    free_names(a, bound) ++ free_names(t, MapSet.put(bound, x))
  end

  defp free_names({:pi, _, a, x, b}, bound) do
    free_names(a, bound) ++ free_names(b, MapSet.put(bound, x))
  end

  defp free_names({:letp, e, a, b, t}, bound) do
    free_names(e, bound) ++ free_names(t, bound |> MapSet.put(a) |> MapSet.put(b))
  end

  defp free_names({:mnat, e, x, p, z, y, s}, bound) do
    free_names(e, bound) ++
      free_names(p, MapSet.put(bound, x)) ++
      free_names(z, bound) ++ free_names(s, MapSet.put(bound, y))
  end

  defp free_names({:matom, e, x, p, bs}, bound) do
    free_names(e, bound) ++
      free_names(p, MapSet.put(bound, x)) ++
      Enum.flat_map(bs, fn {_n, body} -> free_names(body, bound) end)
  end

  defp free_names({:mdata, e, x, p, bs}, bound) do
    free_names(e, bound) ++
      free_names(p, MapSet.put(bound, x)) ++
      Enum.flat_map(bs, fn {_c, binders, body} ->
        free_names(body, Enum.reduce(binders, bound, &MapSet.put(&2, &1)))
      end)
  end

  defp free_names({:memp, e, x, p}, bound) do
    free_names(e, bound) ++ free_names(p, MapSet.put(bound, x))
  end

  defp free_names({:munit, e, x, p, u}, bound) do
    free_names(e, bound) ++ free_names(p, MapSet.put(bound, x)) ++ free_names(u, bound)
  end

  defp free_names({:rwt, e, x, p, t}, bound) do
    free_names(e, bound) ++ free_names(p, MapSet.put(bound, x)) ++ free_names(t, bound)
  end

  defp free_names({:unf, s, {:lam, _, a, x, t}}, bound) do
    free_names(s, bound) ++ free_names(a, bound) ++ free_names(t, MapSet.put(bound, x))
  end

  defp free_names(t, bound) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.flat_map(&free_names(&1, bound))
  end

  defp free_names(t, bound) when is_list(t), do: Enum.flat_map(t, &free_names(&1, bound))
  defp free_names(_t, _bound), do: []

  defp uniq(xs), do: uniq(xs, MapSet.new(), [])
  defp uniq([], _seen, acc), do: Enum.reverse(acc)

  defp uniq([x | xs], seen, acc) do
    if MapSet.member?(seen, x) do
      uniq(xs, seen, acc)
    else
      uniq(xs, MapSet.put(seen, x), [x | acc])
    end
  end

  defp lookup([{:live, name, lay} | _], name), do: {:live, lay}
  defp lookup([{:gone, name} | _], name), do: :gone
  defp lookup([_ | rest], name), do: lookup(rest, name)
  defp lookup([], _name), do: :miss

  defp fresh(ctx), do: fresh("b#{length(ctx)}", ctx)

  defp fresh(name, ctx) do
    if Enum.any?(ctx, fn
         {:live, ^name, _} -> true
         {:gone, ^name} -> true
         _ -> false
       end) do
      fresh(name <> "_", ctx)
    else
      name
    end
  end

  defp ok(tm, lay, steps, k), do: {:ok, %{tm: tm, lay: lay, steps: steps, k: k}}
end

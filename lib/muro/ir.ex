defmodule Muro.IR do
  @moduledoc """
  Closed `run` image of a checked book.

  This is the Elixir spelling of `agda/Muro/IR.agda`. Spec, evidence, motives,
  rewrite, and annotation are dropped. Erased λ-arguments are not elaborated.
  An atom is `{:con, "Atom", name, []}` over the names `Muro.Ast.atoms/1`
  collected, in that order. Nothing here builds an atom from a string.

  The named book keeps source binder names. Agda's de Bruijn `Tm` has lost
  them, so the same arm there is `b` plus the context length.

  Layouts: `:nat`, `:unit`, `:opaque`, `:erased`, `{:pair, a, b}`,
  `{:stream, a}`, `{:data, name}`, `:u8`, `:u32`, `:u64`, `:i64`, `:wbool`,
  `{:opt, payload}`, `:string`, `:slice`. `{:data, name}` is `dataL`. `:erased` marks the let of
  an erased constructor field (`{:let, x, :erased, :ze, body}`). Emitters
  match that layout and ignore the payload. The field stays live at
  `:opaque`, so a use is `Var`. A word term is `{:wrd, kind, op, args}`.
  `closures: true` also uses `{:fn, arg, ret}`, `{:lam, name, lay, body}`,
  `{:appv, fun, arg}`, and `{:data, name, args}`. The default image does not.
  """

  alias Muro.{Ast, Load, Prelude}

  @doc """
  Elaborate every `run` definition in `book`, which is a checked named book
  (`Muro.Load.file/1`, then `Muro.Prelude.for_emit/1`).

  Returns `{:ok, funs}` or `{:error, reason}`. `reason` is `c:lambda`,
  `c:machine`, `c:stream`, `c:string`, `c:erased`, or `c:unsupported`. With
  `closures: true` a refusal is `{:named, reason, def_name}` instead.
  That path may also record `{:data, name, args}`. The default image
  keeps the bare reason and `{:data, name}`.

  `opts` may set `closures: true`. That path elaborates a lambda as a
  closure instead of `c:lambda`, and a definition with fewer λs than Πs
  is applied to the missing parameters. It also elaborates a string as
  `{:str, utf8}`, `{:scat, a, b}`, `{:slen, a}`, or `{:seq, a, b}`.
  The default, `closures: false`, is the image C, Rust, and Zig emit.
  That image refuses a string. A `Bytes` or a `Slice` is `:slice` on every
  image: `{:byt, binary}`, `{:bcat, a, b}`, `{:blen, a}`, `{:beq, a, b}`,
  `{:bsub, s, off, len}`, `{:bget, s, i}`, `{:bunc, s}`, `{:btil, s, b}`,
  `{:baft, s, b}`, `{:bfold, step, caps, z, s}`. `strBytes` of a closed
  string is `{:byt, utf8}`. An open string on the default image is `c:string`.
  """
  def elaborate(book, opts \\ []) when is_list(book) and is_list(opts) do
    st = %{
      book: book,
      atoms: Ast.atoms(book),
      closures: Keyword.get(opts, :closures, false)
    }

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
        case elab_fun(st, d, k) do
          {:ok, {fun, steps, k1}} ->
            with {:ok, rest} <- elab_runs(st, ds, k1) do
              {:ok, [fun | steps ++ rest]}
            end

          {:error, reason} ->
            {:error, named_closure(st, d, reason)}
        end
    end
  end

  # A later definition's tagged error passes through `with` above.
  # Wrapping only this definition's bare reason keeps the failing name.
  defp named_closure(%{closures: true}, %{name: name}, reason)
       when is_binary(reason) and is_binary(name),
       do: {:named, reason, name}

  defp named_closure(_st, _d, reason), do: reason

  # One λ per Π. An erased Π or an erased λ drops that parameter.
  # Fewer λs than Πs is c:unsupported, unless `closures: true`, which
  # makes those Πs parameters and applies the body to them. A λ left
  # over is elaborated, and a value λ is c:lambda on the default path.
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

  defp peel(%{closures: true} = st, ctx, acc, {:pi, :erased, _, name, b}, body) do
    peel(st, [{:gone, name} | ctx], acc, b, {:app, body, {:var, name}})
  end

  defp peel(%{closures: true} = st, ctx, acc, {:pi, _q, a, name, b}, body) do
    with {:ok, lay} <- layout_of(st, a) do
      peel(st, [{:live, name, lay} | ctx], acc ++ [{name, lay}], b, {:app, body, {:var, name}})
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

  defp apply(%{closures: true} = st, t, args, ctx, k) when args != [] do
    case bad_head(t) do
      nil ->
        with {:ok, e} <- elab_form(st, t, ctx, k),
             {:ok, be} <- apply_value(st, e.tm, e.lay, args, e.k) do
          {:ok, %{be | steps: e.steps ++ be.steps}}
        end

      reason ->
        {:error, reason}
    end
  end

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

  defp apply_name(%{closures: true} = st, name, args, ctx, k) when args != [] do
    case lookup(ctx, name) do
      :miss -> global(st, name, args, k)
      :gone -> {:error, "c:erased"}
      {:live, lay} -> apply_value(st, {:var, name}, lay, args, k)
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

  defp finish_def(%{closures: true} = st, %{mode: :run, name: name, type: ty}, args, k) do
    finish_closure(st, ty, args, k, fn ts, lay -> {{:call, name, ts}, lay} end)
  end

  defp finish_def(st, %{mode: :run, name: name, type: ty}, args, k) do
    with {:ok, {ts, steps, k1, lay}} <- zip_live(st, ty, args, k) do
      ok({:call, name, ts}, lay, steps, k1)
    end
  end

  defp finish_def(_st, _d, _args, _k), do: {:error, "c:unsupported"}

  defp finish_ctor(%{closures: true} = st, data, ctor, args, k) do
    finish_closure(st, ctor.type, args, k, fn ts, _lay ->
      {{:con, data.name, ctor.name, ts}, {:data, data.name}}
    end)
  end

  defp finish_ctor(st, data, ctor, args, k) do
    with {:ok, {ts, steps, k1, _lay}} <- zip_live(st, ctor.type, args, k) do
      ok({:con, data.name, ctor.name, ts}, {:data, data.name}, steps, k1)
    end
  end

  # A saturated call stays `{:call, ...}` or `{:con, ...}`. Fewer live
  # arguments become nested `{:lam, ...}` whose body is that call. Extra
  # arguments apply the result. `consume` already stores arguments in
  # source order. A binder is freshened when it would capture a name
  # already stored in the argument list.
  defp finish_closure(st, ty, args, k, pack) do
    with {:ok, consumed} <- consume(st, ty, args, k) do
      case consumed do
        {:done, ts, steps, k1, lay} ->
          {tm, lay} = pack.(ts, lay)
          ok(tm, lay, steps, k1)

        {:partial, ts, steps, k1, rest} ->
          with {:ok, {tm, lay}} <- wrap_inner(st, ts, rest, pack) do
            ok(tm, lay, steps, k1)
          end

        {:over, ts, steps, k1, lay, extra} ->
          {tm, lay} = pack.(ts, lay)

          with {:ok, be} <- apply_value(st, tm, lay, extra, k1) do
            {:ok, %{be | steps: steps ++ be.steps}}
          end
      end
    end
  end

  defp consume(st, {:pi, :erased, _, _, b}, [_arg | rest], k) do
    consume(st, b, rest, k)
  end

  defp consume(st, {:pi, _q, _, _, b}, [{arg, actx} | rest], k) do
    with {:ok, e} <- elab(st, arg, actx, k),
         {:ok, consumed} <- consume(st, b, rest, e.k) do
      {:ok, push_arg(consumed, e.tm, e.steps)}
    end
  end

  defp consume(_st, {:pi, _, _, _, _} = ty, [], k), do: {:ok, {:partial, [], [], k, ty}}

  defp consume(st, ty, [], k) do
    with {:ok, lay} <- layout_of(st, ty) do
      {:ok, {:done, [], [], k, lay}}
    end
  end

  defp consume(st, ty, args, k) when args != [] do
    with {:ok, lay} <- layout_of(st, ty) do
      {:ok, {:over, [], [], k, lay, args}}
    end
  end

  defp push_arg({:done, ts, steps, k, lay}, tm, more),
    do: {:done, [tm | ts], more ++ steps, k, lay}

  defp push_arg({:partial, ts, steps, k, rest}, tm, more),
    do: {:partial, [tm | ts], more ++ steps, k, rest}

  defp push_arg({:over, ts, steps, k, lay, extra}, tm, more),
    do: {:over, [tm | ts], more ++ steps, k, lay, extra}

  defp wrap_inner(st, ts, {:pi, :erased, _, _, b}, pack) do
    wrap_inner(st, ts, b, pack)
  end

  defp wrap_inner(st, ts, {:pi, _q, a, name, b}, pack) do
    with {:ok, lay} <- layout_of(st, a) do
      fresh = freshen(name, ts)

      with {:ok, {body, ret}} <- wrap_inner(st, ts ++ [{:var, fresh}], b, pack) do
        {:ok, {{:lam, fresh, lay, body}, {:fn, lay, ret}}}
      end
    end
  end

  defp wrap_inner(st, ts, ty, pack) do
    with {:ok, lay} <- layout_of(st, ty) do
      {tm, lay} = pack.(ts, lay)
      {:ok, {tm, lay}}
    end
  end

  defp freshen(name, ts) do
    if occurs_name?(name, ts), do: freshen(name <> "_", ts), else: name
  end

  defp occurs_name?(name, t) when is_tuple(t), do: occurs_name?(name, Tuple.to_list(t))
  defp occurs_name?(name, t) when is_list(t), do: Enum.any?(t, &occurs_name?(name, &1))
  defp occurs_name?(name, name), do: true
  defp occurs_name?(_name, _t), do: false

  defp apply_value(_st, fun, lay, [], k), do: ok(fun, lay, [], k)

  defp apply_value(st, fun, {:fn, _arg, ret}, [{arg, actx} | rest], k) do
    with {:ok, ae} <- elab(st, arg, actx, k),
         {:ok, be} <- apply_value(st, {:appv, fun, ae.tm}, ret, rest, ae.k) do
      {:ok, %{be | steps: ae.steps ++ be.steps}}
    end
  end

  defp apply_value(st, fun, :opaque, [{arg, actx} | rest], k) do
    with {:ok, ae} <- elab(st, arg, actx, k),
         {:ok, be} <- apply_value(st, {:appv, fun, ae.tm}, :opaque, rest, ae.k) do
      {:ok, %{be | steps: ae.steps ++ be.steps}}
    end
  end

  defp apply_value(_st, _fun, _lay, _args, _k), do: {:error, "c:lambda"}

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

      ok(match_tm(st, ee.tm, :nat, arms), rlay, ee.steps ++ ze.steps ++ se.steps, se.k)
    end
  end

  defp elab_form(st, {:mdata, e, mx, mot, bs}, ctx, k) do
    with {:ok, ee} <- elab(st, e, ctx, k),
         {:ok, dname} <- data_key(ee.lay),
         {:ok, data} <- find_data(st.book, dname),
         :ok <- branch_count(data.ctors, bs),
         {:ok, {arms, steps, k1}} <-
           elab_arms(st, data.ctors, bs, ctx, ee.k, field_subst(st, data, ee.lay)),
         {:ok, rlay} <- motive_lay(st, mot, ee.lay, mx) do
      ok(match_tm(st, ee.tm, {:data, dname}, arms), rlay, ee.steps ++ steps, k1)
    end
  end

  defp elab_form(st, {:matom, e, mx, mot, bs}, ctx, k) do
    with {:ok, ee} <- elab(st, e, ctx, k),
         :ok <- atom_key(ee.lay),
         :ok <- atom_cover(st.atoms, bs),
         {:ok, {arms, steps, k1}} <- elab_atom_arms(st, st.atoms, bs, ctx, ee.k),
         {:ok, rlay} <- motive_lay(st, mot, ee.lay, mx) do
      ok(match_tm(st, ee.tm, :atom, arms), rlay, ee.steps ++ steps, k1)
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

  # Match on WBool. The image is the word the backends already use.
  defp elab_form(st, {:mwbool, e, mx, mot, bs}, ctx, k) do
    with {:ok, ee} <- elab(st, e, ctx, k),
         :ok <- wbool_arms(bs),
         {:ok, {arms, steps, k1}} <- elab_wbool_arms(st, bs, ctx, ee.k),
         {:ok, rlay} <- motive_lay(st, mot, ee.lay, mx) do
      ok(match_tm(st, ee.tm, :wbool, arms), rlay, ee.steps ++ steps, k1)
    end
  end

  # Match on Opt. The payload is by value. wnone carries no binder.
  defp elab_form(st, {:mopt, e, mx, mot, bs}, ctx, k) do
    with {:ok, ee} <- elab(st, e, ctx, k),
         :ok <- opt_arms(bs),
         pay = opt_payload_lay(ee.lay),
         {:ok, {arms, steps, k1}} <- elab_opt_arms(st, bs, pay, ctx, ee.k),
         {:ok, rlay} <- motive_lay(st, mot, ee.lay, mx) do
      ok(match_tm(st, ee.tm, {:opt, pay}, arms), rlay, ee.steps ++ steps, k1)
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

  defp elab_form(%{closures: true} = st, {:lam, :erased, _dom, name, body}, ctx, k) do
    elab(st, body, [{:gone, name} | ctx], k)
  end

  defp elab_form(%{closures: true} = st, {:lam, _q, dom, name, body}, ctx, k) do
    with {:ok, lay} <- layout_of(st, dom),
         {:ok, be} <- elab(st, body, [{:live, name, lay} | ctx], k) do
      ok({:lam, name, lay, be.tm}, {:fn, lay, be.lay}, be.steps, be.k)
    end
  end

  defp elab_form(_st, {:lam, _, _, _, _}, _ctx, _k), do: {:error, "c:lambda"}

  defp elab_form(st, {:word, op, args}, ctx, k) do
    # A closed numeral converts in one step. Emitting it as a chain of
    # successors would allocate one cell per unit, which a Slice view
    # must not do.
    case Muro.Word.step(op, args) do
      {:ok, reduced} ->
        elab_form(st, reduced, ctx, k)

      :stuck ->
        with {:ok, {tms, lays, steps, k1}} <- elab_words(st, args, ctx, k) do
          case word_retry(op, tms) do
            {:ok, reduced} ->
              with {:ok, e} <- elab_form(st, reduced, ctx, k1) do
                {:ok, %{e | steps: steps ++ e.steps}}
              end

            :stuck ->
              case word_image(op, tms, lays) do
                {:ok, {tm, lay}} -> ok(tm, lay, steps, k1)
                {:error, _} = err -> err
              end
          end
        end
    end
  end

  defp elab_form(%{closures: true}, {:slit, bin}, _ctx, k) when is_binary(bin) do
    ok({:str, bin}, :string, [], k)
  end

  defp elab_form(%{closures: true} = st, {:scat, a, b}, ctx, k) do
    with {:ok, ea} <- elab(st, a, ctx, k),
         {:ok, eb} <- elab(st, b, ctx, ea.k) do
      ok({:scat, ea.tm, eb.tm}, :string, ea.steps ++ eb.steps, eb.k)
    end
  end

  defp elab_form(%{closures: true} = st, {:slen, a}, ctx, k) do
    with {:ok, ea} <- elab(st, a, ctx, k) do
      ok({:slen, ea.tm}, :nat, ea.steps, ea.k)
    end
  end

  defp elab_form(%{closures: true} = st, {:seq, a, b}, ctx, k) do
    with {:ok, ea} <- elab(st, a, ctx, k),
         {:ok, eb} <- elab(st, b, ctx, ea.k) do
      ok({:seq, ea.tm, eb.tm}, :wbool, ea.steps ++ eb.steps, eb.k)
    end
  end

  defp elab_form(_st, {:blit, bin}, _ctx, k) when is_binary(bin) do
    ok({:byt, bin}, :slice, [], k)
  end

  defp elab_form(st, {:bcat, a, b}, ctx, k) do
    with {:ok, ea} <- elab(st, a, ctx, k),
         {:ok, eb} <- elab(st, b, ctx, ea.k) do
      ok({:bcat, ea.tm, eb.tm}, :slice, ea.steps ++ eb.steps, eb.k)
    end
  end

  defp elab_form(st, {tag, a}, ctx, k) when tag in [:blen, :xlen] do
    with {:ok, ea} <- elab(st, a, ctx, k) do
      ok({:blen, ea.tm}, :u64, ea.steps, ea.k)
    end
  end

  defp elab_form(st, {tag, a, b}, ctx, k) when tag in [:beq, :xeq] do
    with {:ok, ea} <- elab(st, a, ctx, k),
         {:ok, eb} <- elab(st, b, ctx, ea.k) do
      ok({:beq, ea.tm, eb.tm}, :wbool, ea.steps ++ eb.steps, eb.k)
    end
  end

  defp elab_form(st, {:bsub, s, off, len}, ctx, k) do
    with {:ok, es} <- elab(st, s, ctx, k),
         {:ok, eo} <- elab(st, off, ctx, es.k),
         {:ok, en} <- elab(st, len, ctx, eo.k) do
      ok({:bsub, es.tm, eo.tm, en.tm}, :slice, es.steps ++ eo.steps ++ en.steps, en.k)
    end
  end

  defp elab_form(st, {tag, s, i}, ctx, k) when tag in [:bget, :aget] do
    with {:ok, es} <- elab(st, s, ctx, k),
         {:ok, ei} <- elab(st, i, ctx, es.k) do
      ok({:bget, es.tm, ei.tm}, {:opt, :u8}, es.steps ++ ei.steps, ei.k)
    end
  end

  defp elab_form(st, {:bunc, s}, ctx, k) do
    with {:ok, es} <- elab(st, s, ctx, k) do
      ok({:bunc, es.tm}, {:data, "Maybe"}, es.steps, es.k)
    end
  end

  defp elab_form(st, {:btil, s, b}, ctx, k) do
    with {:ok, es} <- elab(st, s, ctx, k),
         {:ok, eb} <- elab(st, b, ctx, es.k) do
      ok({:btil, es.tm, eb.tm}, :slice, es.steps ++ eb.steps, eb.k)
    end
  end

  defp elab_form(st, {:baft, s, b}, ctx, k) do
    with {:ok, es} <- elab(st, s, ctx, k),
         {:ok, eb} <- elab(st, b, ctx, es.k) do
      ok({:baft, es.tm, eb.tm}, :slice, es.steps ++ eb.steps, eb.k)
    end
  end

  defp elab_form(st, {:sbytes, s}, ctx, k) do
    case closed_utf8(s) do
      {:ok, bin} ->
        ok({:byt, bin}, :slice, [], k)

      :open ->
        if st.closures do
          with {:ok, es} <- elab(st, s, ctx, k) do
            ok({:sbytes, es.tm}, :slice, es.steps, es.k)
          end
        else
          {:error, "c:string"}
        end
    end
  end

  defp elab_form(st, {tag, _ty, z, f, s}, ctx, k) when tag in [:bfold, :afold] do
    case peel_fold(f) do
      {:ok, bname, rname, aname, body} ->
        with {:ok, ez} <- elab(st, z, ctx, k),
             {:ok, es} <- elab(st, s, ctx, ez.k) do
          caps = fold_captures(body, [bname, rname, aname], ctx)
          id = es.k

          body_ctx = [
            {:live, bname, :u8},
            {:live, rname, :slice},
            {:live, aname, ez.lay} | ctx
          ]

          with {:ok, be} <- elab(st, body, body_ctx, id + 1) do
            step = %{
              name: "step#{id}",
              export: false,
              generated: true,
              fold: true,
              params: cap_params(caps) ++ [{bname, :u8}, {rname, :slice}, {aname, ez.lay}],
              ret: ez.lay,
              body: be.tm
            }

            ok(
              {:bfold, "step#{id}", cap_terms(caps), ez.tm, es.tm},
              ez.lay,
              ez.steps ++ es.steps ++ be.steps ++ [step],
              be.k
            )
          end
        end

      :error ->
        {:error, "c:lambda"}
    end
  end

  defp elab_form(_st, t, _ctx, _k) do
    case bad_head(t) do
      nil -> {:error, "c:unsupported"}
      reason -> {:error, reason}
    end
  end

  defp elab_arms(_st, [], [], _ctx, k, _subst), do: {:ok, {[], [], k}}

  defp elab_arms(st, [c | cs], [{cname, binders, body} | bs], ctx, k, subst) do
    if c.name != cname do
      {:error, "c:unsupported"}
    else
      with {:ok, {bctx, wraps}} <- open_ctor(st, c.type, binders, ctx, subst),
           {:ok, e} <- elab(st, body, bctx, k),
           {:ok, {arms, steps, k1}} <- elab_arms(st, cs, bs, ctx, e.k, subst) do
        {names, tm} = wrap(wraps, e.tm)
        {:ok, {[{:arm, cname, names, tm} | arms], e.steps ++ steps, k1}}
      end
    end
  end

  defp elab_arms(_st, _cs, _bs, _ctx, _k, _subst), do: {:error, "c:unsupported"}

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
  # `Let x erased Ze`. The layout is the mark. Emitters ignore the
  # payload. The field stays live at `:opaque`, so a use is `Var`.
  # A zero passed under a spec alias is bound by `bind_layout` at the
  # argument's layout, so that let is not this one.
  defp open_ctor(st, ty, binders, ctx, subst) do
    pis = telescope(ty)

    if length(pis) != length(binders) do
      {:error, "c:unsupported"}
    else
      open_fields(st, Enum.zip(pis, binders), ctx, [], subst)
    end
  end

  defp open_fields(_st, [], ctx, wraps, _subst), do: {:ok, {ctx, wraps}}

  defp open_fields(st, [{{:erased, _, _}, bname} | rest], ctx, wraps, subst) do
    open_fields(st, rest, [{:live, bname, :opaque} | ctx], wraps ++ [{:gone, bname}], subst)
  end

  defp open_fields(st, [{{_q, a, _}, bname} | rest], ctx, wraps, subst) do
    with {:ok, lay} <- layout_of(Map.put(st, :subst, subst), a) do
      open_fields(st, rest, [{:live, bname, lay} | ctx], wraps ++ [{:live, bname}], subst)
    end
  end

  # Indices are not parameters. `Enum.zip` drops a trailing index, so a
  # field that shares an index's name stays the field.
  defp field_subst(%{closures: true}, data, {:data, _, arg_lays}) when is_list(arg_lays) do
    data
    |> Map.get(:params, [])
    |> Enum.flat_map(fn
      {_q, x, _a} when is_binary(x) -> [x]
      _ -> []
    end)
    |> Enum.zip(arg_lays)
    |> Map.new()
  end

  defp field_subst(_st, _data, _lay), do: %{}

  defp wrap([], tm), do: {[], tm}

  defp wrap([{:live, x} | ws], tm) do
    {names, inner} = wrap(ws, tm)
    {[x | names], inner}
  end

  defp wrap([{:gone, x} | ws], tm) do
    {names, inner} = wrap(ws, tm)
    {names, {:let, x, :erased, :ze, inner}}
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

  defp layout_of(%{closures: true} = st, {:pi, :erased, _, _, b}), do: layout_of(st, b)

  defp layout_of(%{closures: true} = st, {:pi, _q, a, _, b}) do
    with {:ok, la} <- layout_of(st, a),
         {:ok, lb} <- layout_of(st, b) do
      {:ok, {:fn, la, lb}}
    end
  end

  defp layout_of(_st, {:pi, _, _, _, _}), do: {:ok, :opaque}
  defp layout_of(_st, :empty), do: {:ok, :opaque}
  defp layout_of(_st, {:idt, _, _, _}), do: {:ok, :opaque}
  defp layout_of(_st, :atom), do: {:ok, {:data, "Atom"}}
  defp layout_of(%{closures: true}, :string), do: {:ok, :string}
  defp layout_of(_st, :string), do: {:error, "c:string"}
  defp layout_of(_st, :bytes), do: {:ok, :slice}
  defp layout_of(_st, :slice), do: {:ok, :slice}

  defp layout_of(st, {:var, name}) do
    case Map.get(Map.get(st, :subst, %{}), name) do
      nil ->
        if data?(st.book, name), do: {:ok, {:data, name}}, else: {:ok, :opaque}

      lay ->
        {:ok, lay}
    end
  end

  defp layout_of(st, {:def, name}), do: layout_of(st, {:var, name})

  # A field type names the data parameter (`A`), not the argument the
  # scrutinee was built at (`Bool2`). The closure image substitutes that
  # parameter so a match on the element is a data match. An argument
  # with no layout (`suc m`) stays opaque and does not refuse the
  # application. The default image still drops the arguments.
  defp layout_of(%{closures: true} = st, {:app, _, _} = t) do
    {head, args} = app_spine(t, [])

    with {:ok, hl} <- layout_of(st, head) do
      case hl do
        {:data, name} when is_binary(name) ->
          {:ok, {:data, name, Enum.map(args, &arg_lay(st, &1))}}

        other ->
          {:ok, other}
      end
    end
  end

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
  defp layout_of(_st, :i64), do: {:ok, :i64}
  defp layout_of(_st, {:word, {:ty, :u8}, []}), do: {:ok, :u8}
  defp layout_of(_st, {:word, {:ty, :u32}, []}), do: {:ok, :u32}
  defp layout_of(_st, {:word, {:ty, :u64}, []}), do: {:ok, :u64}
  defp layout_of(_st, {:word, :bool, []}), do: {:ok, :wbool}
  defp layout_of(_st, {:word, {:optk, k}, []}), do: {:ok, {:opt, word_lay(k)}}

  defp layout_of(st, {:word, :opt, [a]}) do
    with {:ok, lay} <- layout_of(st, a) do
      {:ok, {:opt, lay}}
    end
  end

  defp layout_of(_st, {:word, _, _}), do: {:error, "c:unsupported"}
  defp layout_of(_st, t), do: head_refusal(t)

  defp app_spine({:app, f, a}, acc), do: app_spine(f, [a | acc])
  defp app_spine(head, acc), do: {head, acc}

  defp arg_lay(st, t) do
    case layout_of(st, t) do
      {:ok, lay} -> lay
      {:error, _} -> :opaque
    end
  end

  defp motive_lay(st, {:lam, _, _, x, body}, scr, _binder), do: motive_lay(st, body, scr, x)
  defp motive_lay(_st, {:var, x}, scr, x), do: {:ok, scr}
  defp motive_lay(st, t, _scr, _binder), do: layout_of(st, t)

  defp head_refusal(t) do
    case bad_head(t) do
      nil -> {:error, "c:unsupported"}
      reason -> {:error, reason}
    end
  end

  defp bad_head(:string), do: "c:string"
  defp bad_head({:slit, _}), do: "c:string"
  defp bad_head({:scat, _, _}), do: "c:string"
  defp bad_head({:slen, _}), do: "c:string"
  defp bad_head({:seq, _, _}), do: "c:string"
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

  defp elab_words(_st, [], _ctx, k), do: {:ok, {[], [], [], k}}

  defp elab_words(st, [t | ts], ctx, k) do
    with {:ok, e} <- elab(st, t, ctx, k),
         {:ok, {tms, lays, steps, k1}} <- elab_words(st, ts, ctx, e.k) do
      {:ok, {[e.tm | tms], [e.lay | lays], e.steps ++ steps, k1}}
    end
  end

  defp word_lay(:u8), do: :u8
  defp word_lay(:u32), do: :u32
  defp word_lay(:u64), do: :u64
  defp word_lay(:i64), do: :i64

  defp lay_kind(:u8), do: :u8
  defp lay_kind(:u32), do: :u32
  defp lay_kind(:u64), do: :u64
  defp lay_kind(:i64), do: :i64
  defp lay_kind(_), do: nil

  defp same_kind(lx, ly) do
    case {lay_kind(lx), lay_kind(ly)} do
      {k, k} when k != nil -> k
      _ -> nil
    end
  end

  defp bin_w(ret, op, [x, y], [lx, ly]) do
    case same_kind(lx, ly) do
      nil -> {:error, "c:unsupported"}
      k -> {:ok, {{:wrd, k, op, [x, y]}, ret.(k)}}
    end
  end

  defp bin_w(_ret, _op, _ts, _ls), do: {:error, "c:unsupported"}

  # wnone has no payload kind. {:opt, :opaque} is a placeholder; the
  # function return layout still comes from the declared type.
  # Arguments that were closed numerals are literals by the time they
  # are elaborated. Compare them here so a constant `u8` test is a
  # boolean, not a comparison rustc rejects as useless.
  defp word_retry(:ton, _tms), do: :stuck
  defp word_retry(:opt, _tms), do: :stuck

  defp word_retry(op, tms) do
    args = Enum.map(tms, &word_value/1)

    if Enum.any?(args, &is_nil/1) do
      :stuck
    else
      Muro.Word.step(op, args)
    end
  end

  defp word_value({:wrd, _k, {:lit, k, n}, []}) when is_integer(n), do: {:word, {:lit, k, n}, []}
  defp word_value({:wrd, _, true, []}), do: {:word, true, []}
  defp word_value({:wrd, _, false, []}), do: {:word, false, []}
  defp word_value(_), do: nil

  defp word_image({:lit, k, n}, [], []), do: {:ok, {{:wrd, k, {:lit, k, n}, []}, word_lay(k)}}
  defp word_image({:of, k}, [t], [:nat]), do: {:ok, {{:wrd, k, {:of, k}, [t]}, word_lay(k)}}

  defp word_image(:ton, [t], [lay]) do
    case lay_kind(lay) do
      nil -> {:error, "c:unsupported"}
      k -> {:ok, {{:wrd, k, :ton, [t]}, :nat}}
    end
  end

  defp word_image(:add, ts, ls), do: bin_w(&word_lay/1, :add, ts, ls)
  defp word_image(:sub, ts, ls), do: bin_w(&word_lay/1, :sub, ts, ls)
  defp word_image(:mul, ts, ls), do: bin_w(&word_lay/1, :mul, ts, ls)
  defp word_image(:and, ts, ls), do: bin_w(&word_lay/1, :and, ts, ls)
  defp word_image(:or, ts, ls), do: bin_w(&word_lay/1, :or, ts, ls)
  defp word_image(:xor, ts, ls), do: bin_w(&word_lay/1, :xor, ts, ls)

  defp word_image(op, ts, ls) when op in [:cadd, :csub, :cmul, :div, :rem] do
    bin_w(fn k -> {:opt, word_lay(k)} end, op, ts, ls)
  end

  defp word_image(op, ts, ls) when op in [:eq, :lt, :le] do
    bin_w(fn _k -> :wbool end, op, ts, ls)
  end

  defp word_image(:not, [t], [lay]) do
    case lay_kind(lay) do
      nil -> {:error, "c:unsupported"}
      k -> {:ok, {{:wrd, k, :not, [t]}, word_lay(k)}}
    end
  end

  defp word_image(op, [x, a], [lx, :nat]) when op in [:shl, :shr] do
    case lay_kind(lx) do
      nil -> {:error, "c:unsupported"}
      k -> {:ok, {{:wrd, k, op, [x, a]}, word_lay(k)}}
    end
  end

  defp word_image({:cast, k}, [t], [lay]) do
    case lay_kind(lay) do
      nil -> {:error, "c:unsupported"}
      _ -> {:ok, {{:wrd, k, {:cast, k}, [t]}, word_lay(k)}}
    end
  end

  defp word_image(true, [], []), do: {:ok, {{:wrd, :u8, true, []}, :wbool}}
  defp word_image(false, [], []), do: {:ok, {{:wrd, :u8, false, []}, :wbool}}

  # A machine payload keeps the word kind. Ordinary data is that
  # value: the option's payload is the data pointer. Unboxed data
  # still fails later, as c:unboxed.
  defp word_image(:some, [t], [lay]) do
    case lay_kind(lay) do
      nil ->
        case lay do
          {:data, name} when is_binary(name) ->
            {:ok, {{:wrd, lay, :some, [t]}, {:opt, lay}}}

          _ ->
            {:error, "c:unsupported"}
        end

      k ->
        {:ok, {{:wrd, k, :some, [t]}, {:opt, word_lay(k)}}}
    end
  end

  defp word_image(:none, [], []), do: {:ok, {{:wrd, :u8, :none, []}, {:opt, :opaque}}}
  defp word_image(_op, _ts, _ls), do: {:error, "c:unsupported"}

  defp pair_halves({:pair, a, b}), do: {a, b}
  defp pair_halves(_), do: {:opaque, :opaque}

  defp uncons_lay({:stream, s}), do: {:pair, :opaque, {:stream, s}}
  defp uncons_lay(_), do: {:pair, :opaque, :opaque}

  defp data_key({:data, name}), do: {:ok, name}
  defp data_key({:data, name, _args}), do: {:ok, name}
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

  defp peel_fold({:lam, q, _, b, {:lam, q2, _, r, {:lam, q3, _, a, body}}})
       when q != :erased and q2 != :erased and q3 != :erased,
       do: {:ok, b, r, a, body}

  defp peel_fold(_), do: :error

  defp fold_captures(body, binders, ctx) do
    body
    |> free_names(MapSet.new(binders))
    |> uniq()
    |> Enum.flat_map(fn name ->
      case lookup(ctx, name) do
        {:live, lay} -> [{name, lay, {:var, name}}]
        _ -> []
      end
    end)
  end

  defp closed_utf8({:slit, bin}) when is_binary(bin), do: {:ok, bin}

  defp closed_utf8({:scat, a, b}) do
    case {closed_utf8(a), closed_utf8(b)} do
      {{:ok, x}, {:ok, y}} -> {:ok, x <> y}
      _ -> :open
    end
  end

  defp closed_utf8(_), do: :open

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

  defp free_names({tag, e, x, p, bs}, bound) when tag in [:mwbool, :mopt] do
    free_names(e, bound) ++
      free_names(p, MapSet.put(bound, x)) ++
      Enum.flat_map(bs, fn {_c, binders, body} ->
        free_names(body, Enum.reduce(binders, bound, &MapSet.put(&2, &1)))
      end)
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

  # The kind is only on the closure image. C, Rust, and Zig match
  # `{:match, scrut, arms}` and must keep seeing that tuple.
  defp match_tm(%{closures: true}, scrut, kind, arms), do: {:match, scrut, kind, arms}
  defp match_tm(_st, scrut, _kind, arms), do: {:match, scrut, arms}

  defp wbool_arms([{"wtrue", [], _}, {"wfalse", [], _}]), do: :ok
  defp wbool_arms(_), do: {:error, "c:unsupported"}

  defp opt_arms([{"wsome", [_], _}, {"wnone", [], _}]), do: :ok
  defp opt_arms(_), do: {:error, "c:unsupported"}

  defp opt_payload_lay({:opt, pay}), do: pay
  defp opt_payload_lay(_), do: :opaque

  defp elab_wbool_arms(st, [{"wtrue", [], t}, {"wfalse", [], f}], ctx, k) do
    with {:ok, te} <- elab(st, t, ctx, k),
         {:ok, fe} <- elab(st, f, ctx, te.k) do
      arms = [{:arm, "wtrue", [], te.tm}, {:arm, "wfalse", [], fe.tm}]
      {:ok, {arms, te.steps ++ fe.steps, fe.k}}
    end
  end

  defp elab_opt_arms(st, [{"wsome", [y], s}, {"wnone", [], n}], pay, ctx, k) do
    with {:ok, se} <- elab(st, s, [{:live, y, pay} | ctx], k),
         {:ok, ne} <- elab(st, n, ctx, se.k) do
      arms = [{:arm, "wsome", [y], se.tm}, {:arm, "wnone", [], ne.tm}]
      {:ok, {arms, se.steps ++ ne.steps, ne.k}}
    end
  end

  defp ok(tm, lay, steps, k), do: {:ok, %{tm: tm, lay: lay, steps: steps, k: k}}
end

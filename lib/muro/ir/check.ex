defmodule Muro.IR.Check do
  @moduledoc """
  Validates a `Muro.IR` image.

  `check/1` and `check/2` walk every function after `Muro.IR.elaborate/2`
  or `Muro.IR.Share`. They report well-scopedness, layout and arity
  agreement, the absence of erased survivors in live positions, grade
  accounting along paths, arm exhaustiveness when a book is given, and
  that closure forms appear only in the closures image.

  Grades are `:linear` (used once on every path), `:affine` (used at
  most once on any path), and `:reuse` (unrestricted). Compiler-introduced
  CSE lets are `:reuse`. After Share prunes a path, an unused `:linear`
  binder is `:affine`, so a valid rewrite still checks.
  """

  alias Muro.IR

  @live_grades [:linear, :affine, :reuse]

  @doc """
  Check a list of IR functions.

  Options:

    * `:book` — the named book, used for constructor fields and
      exhaustiveness. Without it those checks are skipped.
    * `:closures` — `true` when the image was elaborated with
      `closures: true`. When omitted, it is inferred from the image.
  """
  def check(funs, opts \\ []) when is_list(funs) do
    funs = Enum.map(funs, &IR.normalize_fun/1)
    closures? = Keyword.get(opts, :closures, closures_image?(funs))

    ctx = %{
      by_name: Map.new(funs, &{&1.name, &1}),
      book: Keyword.get(opts, :book),
      closures: closures?
    }

    errors =
      funs
      |> Enum.flat_map(&check_fun(&1, ctx))
      |> Enum.uniq()

    case errors do
      [] -> :ok
      list -> {:error, list}
    end
  end

  defp closures_image?(funs) do
    Enum.any?(funs, fn fun ->
      Enum.any?(fun.params, fn p -> fn_lay?(IR.param_lay(p)) end) or
        fn_lay?(fun.ret) or has_closure_form?(fun.body)
    end)
  end

  defp fn_lay?({:fn, _, _}), do: true
  defp fn_lay?({:pair, a, b}), do: fn_lay?(a) or fn_lay?(b)
  defp fn_lay?({:stream, a}), do: fn_lay?(a)
  defp fn_lay?({:opt, a}), do: fn_lay?(a)
  defp fn_lay?(_), do: false

  defp has_closure_form?({:lam, name, _, g, _})
       when is_binary(name) and g in @live_grades,
       do: true

  defp has_closure_form?({:appv, _, _}), do: true
  defp has_closure_form?({:data, _, args}) when is_list(args), do: true
  defp has_closure_form?({:match, _, lay, arms}) when not is_list(lay) and is_list(arms), do: true

  defp has_closure_form?(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.any?(&has_closure_form?/1)

  defp has_closure_form?(t) when is_list(t), do: Enum.any?(t, &has_closure_form?/1)
  defp has_closure_form?(_), do: false

  defp check_fun(fun, ctx) do
    names = Enum.map(fun.params, &IR.param_name/1)

    param_errors =
      fun.params
      |> Enum.with_index()
      |> Enum.flat_map(fn {p, i} ->
        n = IR.param_name(p)
        lay = IR.param_lay(p)
        g = IR.param_grade(p)

        cond do
          g not in @live_grades ->
            ["#{fun.name}: parameter #{n} has invalid grade #{inspect(g)}"]

          lay == :erased ->
            ["#{fun.name}: parameter #{n} has erased layout"]

          not ctx.closures and fn_lay?(lay) ->
            ["#{fun.name}: closure layout on parameter #{n} outside the closures image"]

          n in Enum.take(names, i) ->
            ["#{fun.name}: duplicate parameter #{n}"]

          true ->
            []
        end
      end)

    ret_errors =
      if not ctx.closures and fn_lay?(fun.ret) do
        ["#{fun.name}: closure return layout outside the closures image"]
      else
        []
      end

    env =
      Map.new(fun.params, fn p ->
        {IR.param_name(p), %{grade: IR.param_grade(p), lay: IR.param_lay(p)}}
      end)

    {paths, body_errors} = check_tm(fun.body, env, fun, ctx)

    grade_errors =
      Enum.flat_map(paths, fn path ->
        Enum.flat_map(fun.params, fn p ->
          n = IR.param_name(p)
          grade_error(fun.name, n, IR.param_grade(p), Map.get(path, n, 0))
        end)
      end)

    param_errors ++ ret_errors ++ body_errors ++ grade_errors
  end

  defp grade_error(_fun, _name, :linear, 1), do: []

  defp grade_error(fun, name, :linear, n),
    do: ["#{fun}: linear binder #{name} used #{n} time(s) on a path"]

  defp grade_error(fun, name, :affine, n) when n > 1,
    do: ["#{fun}: affine binder #{name} used #{n} times on a path"]

  defp grade_error(_fun, _name, _g, _n), do: []

  # -- term walk --------------------------------------------------------

  defp check_tm({:var, x}, env, fun, _ctx) do
    case env do
      %{^x => %{lay: :erased}} ->
        {[%{}], ["#{fun.name}: erased variable #{x} used in a live position"]}

      %{^x => _} ->
        {[%{x => 1}], []}

      _ ->
        {[%{}], ["#{fun.name}: free variable #{x}"]}
    end
  end

  defp check_tm({:let, x, :erased, g, val, body}, env, fun, ctx) do
    errors =
      cond do
        g not in @live_grades ->
          ["#{fun.name}: let #{x} has invalid grade #{inspect(g)}"]

        val != :ze ->
          ["#{fun.name}: erased let #{x} does not bind Ze"]

        true ->
          []
      end

    env1 = Map.put(env, x, %{grade: g, lay: :erased})
    {bpaths, berr} = check_tm(body, env1, fun, ctx)

    used =
      Enum.flat_map(bpaths, fn p ->
        if Map.get(p, x, 0) > 0,
          do: ["#{fun.name}: erased variable #{x} used in a live position"],
          else: []
      end)

    {Enum.map(bpaths, &Map.delete(&1, x)), errors ++ berr ++ used}
  end

  defp check_tm({:let, x, lay, g, val, body}, env, fun, ctx) do
    errors =
      if g in @live_grades,
        do: [],
        else: ["#{fun.name}: let #{x} has invalid grade #{inspect(g)}"]

    {vpaths, verr} = check_tm(val, env, fun, ctx)
    errors = errors ++ verr ++ layout_agree(fun, "let #{x}", infer(val, env, ctx), lay)

    env1 = Map.put(env, x, %{grade: g, lay: lay})
    {bpaths, berr} = check_tm(body, env1, fun, ctx)

    gerr =
      Enum.flat_map(bpaths, fn p ->
        grade_error(fun.name, x, g, Map.get(p, x, 0))
      end)

    {seq(vpaths, Enum.map(bpaths, &Map.delete(&1, x))), errors ++ berr ++ gerr}
  end

  defp check_tm({:letp, a, b, e, body}, env, fun, ctx) do
    {epaths, eerr} = check_tm(e, env, fun, ctx)
    elay = infer(e, env, ctx)

    {alay, blay} =
      case elay do
        {:pair, x, y} -> {x, y}
        _ -> {:unknown, :unknown}
      end

    env1 =
      env
      |> Map.put(a, %{grade: :reuse, lay: alay})
      |> Map.put(b, %{grade: :reuse, lay: blay})

    {bpaths, berr} = check_tm(body, env1, fun, ctx)
    {seq(epaths, Enum.map(bpaths, &Map.drop(&1, [a, b]))), eerr ++ berr}
  end

  defp check_tm({:lam, name, lay, g, body}, env, fun, ctx) when is_binary(name) do
    errors =
      cond do
        not ctx.closures ->
          ["#{fun.name}: λ outside the closures image"]

        g not in @live_grades ->
          ["#{fun.name}: λ #{name} has invalid grade #{inspect(g)}"]

        true ->
          []
      end

    env1 = Map.put(env, name, %{grade: g, lay: lay})
    {bpaths, berr} = check_tm(body, env1, fun, ctx)

    gerr =
      Enum.flat_map(bpaths, fn p ->
        grade_error(fun.name, name, g, Map.get(p, name, 0))
      end)

    {Enum.map(bpaths, &Map.delete(&1, name)), errors ++ berr ++ gerr}
  end

  defp check_tm({:appv, f, a}, env, fun, ctx) do
    errors =
      if ctx.closures, do: [], else: ["#{fun.name}: application outside the closures image"]

    {p1, e1} = check_tm(f, env, fun, ctx)
    {p2, e2} = check_tm(a, env, fun, ctx)
    {seq(p1, p2), errors ++ e1 ++ e2}
  end

  defp check_tm({:data, _name, args}, env, fun, ctx) when is_list(args) do
    errors =
      if ctx.closures, do: [], else: ["#{fun.name}: data value outside the closures image"]

    {ps, es} = check_seq(args, env, fun, ctx)
    {ps, errors ++ es}
  end

  defp check_tm({:match, s, lay, arms}, env, fun, ctx) when is_list(arms) and not is_list(lay) do
    errors =
      if ctx.closures, do: [], else: ["#{fun.name}: typed match outside the closures image"]

    {ps, es} = check_match(s, arms, env, fun, ctx, lay)
    {ps, errors ++ es}
  end

  defp check_tm({:match, s, arms}, env, fun, ctx) when is_list(arms) do
    check_match(s, arms, env, fun, ctx, infer(s, env, ctx))
  end

  defp check_tm({:call, name, args}, env, fun, ctx) when is_list(args) do
    {ps, es} = check_seq(args, env, fun, ctx)

    case Map.fetch(ctx.by_name, name) do
      :error ->
        {ps, es ++ ["#{fun.name}: unknown call #{name}"]}

      {:ok, callee} ->
        {ps, es ++ call_errors(fun, name, args, callee, env, ctx)}
    end
  end

  defp check_tm({:con, d, c, args}, env, fun, ctx) when is_list(args) do
    {ps, es} = check_seq(args, env, fun, ctx)
    {ps, es ++ ctor_errors(fun, d, c, args, env, ctx)}
  end

  defp check_tm({:stream, seed, caps, step}, env, fun, ctx) do
    tms = [seed | Enum.map(caps, fn {_n, tm} -> tm end)]
    {ps, es} = check_seq(tms, env, fun, ctx)

    step_err =
      if Map.has_key?(ctx.by_name, step),
        do: [],
        else: ["#{fun.name}: unknown stream step #{step}"]

    {ps, es ++ step_err}
  end

  defp check_tm({:bfold, step, caps, z, s}, env, fun, ctx) do
    tms = Enum.map(caps, fn {_n, tm} -> tm end) ++ [z, s]
    {ps, es} = check_seq(tms, env, fun, ctx)

    step_err =
      if Map.has_key?(ctx.by_name, step),
        do: [],
        else: ["#{fun.name}: unknown fold step #{step}"]

    {ps, es ++ step_err}
  end

  defp check_tm(t, env, fun, ctx) when is_tuple(t) do
    check_seq(tuple_children(t), env, fun, ctx)
  end

  defp check_tm(t, env, fun, ctx) when is_list(t), do: check_seq(t, env, fun, ctx)
  defp check_tm(_t, _env, _fun, _ctx), do: {[%{}], []}

  defp check_match(s, arms, env, fun, ctx, scrut_lay) do
    {spaths, serr} = check_tm(s, env, fun, ctx)
    {apaths, aerr} = arm_paths(arms, scrut_lay, env, fun, ctx)
    ex = exhaust_errors(fun, scrut_lay, arms, ctx)
    {seq(spaths, apaths), serr ++ aerr ++ ex}
  end

  defp arm_paths(arms, scrut_lay, env, fun, ctx) do
    walked =
      Enum.map(arms, fn {:arm, tag, names, tm} ->
        lays = arm_field_lays(scrut_lay, tag, names, ctx)

        env1 =
          Enum.zip(names, lays)
          |> Enum.reduce(env, fn {n, lay}, env ->
            Map.put(env, n, %{grade: :reuse, lay: lay})
          end)

        {paths, errors} = check_tm(tm, env1, fun, ctx)
        {Enum.map(paths, &Map.drop(&1, names)), errors}
      end)

    case walked do
      [] ->
        {[%{}], []}

      list ->
        paths = Enum.flat_map(list, &elem(&1, 0))
        errors = Enum.flat_map(list, &elem(&1, 1))
        {paths, errors}
    end
  end

  defp arm_field_lays(scrut_lay, tag, names, ctx) do
    case {scrut_lay, tag} do
      {:nat, "suc"} ->
        pad_lays([:nat], names)

      {{:opt, pay}, "wsome"} ->
        pad_lays([pay], names)

      {{:data, d}, _} ->
        case ctor_field_lays(ctx.book, d, tag) do
          :unknown -> Enum.map(names, fn _ -> :unknown end)
          lays -> pad_lays(lays, names)
        end

      _ ->
        Enum.map(names, fn _ -> :unknown end)
    end
  end

  defp pad_lays(lays, names) do
    n = length(names)
    lays ++ List.duplicate(:unknown, max(n - length(lays), 0))
  end

  defp exhaust_errors(_fun, _lay, _arms, %{book: nil}), do: []

  defp exhaust_errors(fun, lay, arms, ctx) do
    case expected_tags(lay, ctx.book) do
      nil ->
        []

      expected ->
        have = Enum.map(arms, fn {:arm, tag, _, _} -> tag end) |> Enum.uniq()
        missing = expected -- have
        extra = have -- expected

        miss =
          if missing == [],
            do: [],
            else: ["#{fun.name}: match is missing arm(s) #{Enum.join(missing, ", ")}"]

        ext =
          if extra == [],
            do: [],
            else: ["#{fun.name}: match has unknown arm(s) #{Enum.join(extra, ", ")}"]

        miss ++ ext
    end
  end

  defp expected_tags(:nat, _book), do: ["zero", "suc"]
  defp expected_tags(:wbool, _book), do: ["wtrue", "wfalse"]
  defp expected_tags({:opt, _}, _book), do: ["wsome", "wnone"]

  defp expected_tags({:data, "Atom"}, book) do
    case Muro.Ast.atoms(book) do
      [] -> nil
      atoms -> atoms
    end
  end

  defp expected_tags({:data, name}, book) do
    case find_data(book, name) do
      nil -> nil
      d -> Enum.map(d.ctors, & &1.name)
    end
  end

  defp expected_tags(_, _), do: nil

  # -- calls and constructors ------------------------------------------

  defp call_errors(fun, name, args, callee, env, ctx) do
    arity =
      if length(args) == length(callee.params) do
        []
      else
        [
          "#{fun.name}: call #{name} has #{length(args)} argument(s), expected #{length(callee.params)}"
        ]
      end

    lays =
      args
      |> Enum.zip(callee.params)
      |> Enum.flat_map(fn {arg, p} ->
        layout_agree(
          fun,
          "argument of #{name}",
          infer(arg, env, ctx),
          IR.param_lay(p)
        )
      end)

    arity ++ lays
  end

  defp ctor_errors(fun, d, c, args, env, ctx) do
    case {ctx.book, ctor_field_lays(ctx.book, d, c)} do
      {nil, _} ->
        []

      {_, :unknown} ->
        []

      {_, lays} ->
        arity =
          if length(args) == length(lays) do
            []
          else
            [
              "#{fun.name}: constructor #{c} has #{length(args)} field(s), expected #{length(lays)}"
            ]
          end

        agrees =
          args
          |> Enum.zip(lays)
          |> Enum.flat_map(fn {arg, lay} ->
            layout_agree(fun, "field of #{c}", infer(arg, env, ctx), lay)
          end)

        arity ++ agrees
    end
  end

  defp ctor_field_lays(nil, _d, _c), do: :unknown

  defp ctor_field_lays(book, dname, cname) do
    with d when d != nil <- find_data(book, dname),
         ctor when ctor != nil <- Enum.find(d.ctors, &(&1.name == cname)) do
      live_field_lays(book, ctor.type)
    else
      _ -> :unknown
    end
  end

  defp live_field_lays(book, ty), do: live_field_lays(book, ty, [])

  defp live_field_lays(book, {:pi, q, a, _n, b}, acc) do
    if Muro.Grade.kernel_qty(q) == :erased do
      live_field_lays(book, b, acc)
    else
      live_field_lays(book, b, acc ++ [type_lay(book, a)])
    end
  end

  defp live_field_lays(_book, _ty, acc), do: acc

  defp type_lay(_book, :nat), do: :nat
  defp type_lay(_book, :unit), do: :unit
  defp type_lay(_book, :u8), do: :u8
  defp type_lay(_book, :u32), do: :u32
  defp type_lay(_book, :u64), do: :u64
  defp type_lay(_book, :i64), do: :i64
  defp type_lay(_book, :wbool), do: :wbool
  defp type_lay(_book, :string), do: :string
  defp type_lay(_book, :slice), do: :slice
  defp type_lay(_book, {:data, name}), do: {:data, name}

  defp type_lay(book, {:const, name}) do
    case Enum.find(book, &(Map.get(&1, :name) == name)) do
      %{kind: :data} -> {:data, name}
      _ -> :unknown
    end
  end

  defp type_lay(book, name) when is_binary(name) do
    case Enum.find(book, &(Map.get(&1, :name) == name)) do
      %{kind: :data} -> {:data, name}
      _ -> :unknown
    end
  end

  defp type_lay(_, _), do: :unknown

  defp find_data(nil, _name), do: nil

  defp find_data(book, name) do
    Enum.find(book, fn
      %{kind: :data, name: ^name} -> true
      _ -> false
    end)
  end

  # -- layouts ----------------------------------------------------------

  defp layout_agree(_fun, _where, got, expect)
       when got in [:unknown, :opaque] or expect in [:unknown, :opaque] or got == expect,
       do: []

  defp layout_agree(fun, where, got, expect),
    do: ["#{fun.name}: #{where} has layout #{inspect(got)}, expected #{inspect(expect)}"]

  defp infer({:var, x}, env, _ctx) do
    case env do
      %{^x => %{lay: lay}} -> lay
      _ -> :unknown
    end
  end

  defp infer(:ze, _env, _ctx), do: :nat
  defp infer({:su, _}, _env, _ctx), do: :nat
  defp infer({:nat, n}, _env, _ctx) when is_integer(n), do: :nat
  defp infer(:tt, _env, _ctx), do: :unit
  defp infer(:abort, _env, _ctx), do: :opaque
  defp infer({:byt, _}, _env, _ctx), do: :slice
  defp infer({:str, _}, _env, _ctx), do: :string
  defp infer({:pair, a, b}, env, ctx), do: {:pair, infer(a, env, ctx), infer(b, env, ctx)}
  defp infer({:call, name, _}, _env, ctx), do: call_ret(ctx, name)
  defp infer({:con, d, _, _}, _env, _ctx), do: {:data, d}
  defp infer({:wrd, lay, _, _}, _env, _ctx), do: lay
  defp infer({:let, _, _, _, _, b}, env, ctx), do: infer(b, env, ctx)
  defp infer({:letp, _, _, _, b}, env, ctx), do: infer(b, env, ctx)
  defp infer({:uncons, e}, env, ctx), do: uncons_lay(infer(e, env, ctx))
  defp infer({:stream, seed, _, _}, env, ctx), do: {:stream, infer(seed, env, ctx)}
  defp infer({:blen, _}, _env, _ctx), do: :u64
  defp infer({:slen, _}, _env, _ctx), do: :nat
  defp infer({:beq, _, _}, _env, _ctx), do: :wbool
  defp infer({:seq, _, _}, _env, _ctx), do: :wbool
  defp infer({:bcat, _, _}, _env, _ctx), do: :slice
  defp infer({:scat, _, _}, _env, _ctx), do: :string
  defp infer({:bsub, _, _, _}, _env, _ctx), do: :slice
  defp infer({:bget, _, _}, _env, _ctx), do: {:opt, :u8}
  defp infer({:btil, _, _}, _env, _ctx), do: :slice
  defp infer({:baft, _, _}, _env, _ctx), do: :slice
  defp infer({:sbytes, _}, _env, _ctx), do: :slice
  defp infer({:bunc, _}, _env, _ctx), do: :slice
  defp infer({:lam, _, lay, _, body}, env, ctx), do: {:fn, lay, infer(body, env, ctx)}
  defp infer({:appv, f, _}, env, ctx), do: ret_of_fn(infer(f, env, ctx))
  defp infer({:data, name, _}, _env, _ctx), do: {:data, name}

  defp infer({:match, _, arms}, env, ctx) when is_list(arms) and arms != [] do
    {:arm, _, _, tm} = hd(arms)
    infer(tm, env, ctx)
  end

  defp infer({:match, _, _, arms}, env, ctx) when is_list(arms) and arms != [] do
    {:arm, _, _, tm} = hd(arms)
    infer(tm, env, ctx)
  end

  defp infer({:bfold, _, _, z, _}, env, ctx), do: infer(z, env, ctx)
  defp infer(_, _, _), do: :unknown

  defp call_ret(ctx, name) do
    case Map.fetch(ctx.by_name, name) do
      {:ok, fun} -> fun.ret
      :error -> :unknown
    end
  end

  defp uncons_lay({:stream, a}), do: {:pair, a, {:stream, a}}
  defp uncons_lay(_), do: :unknown

  defp ret_of_fn({:fn, _, ret}), do: ret
  defp ret_of_fn(_), do: :unknown

  # -- paths ------------------------------------------------------------

  defp check_seq(tms, env, fun, ctx) do
    Enum.reduce(tms, {[%{}], []}, fn tm, {paths, errors} ->
      {ps, es} = check_tm(tm, env, fun, ctx)
      {seq(paths, ps), errors ++ es}
    end)
  end

  defp seq(ps, qs) do
    for p <- ps, q <- qs, do: add_uses(p, q)
  end

  defp add_uses(a, b) do
    Map.merge(a, b, fn _k, x, y -> x + y end)
  end

  defp tuple_children(t) do
    case t do
      :ze ->
        []

      :tt ->
        []

      :abort ->
        []

      {:nat, _} ->
        []

      {:var, _} ->
        []

      {:byt, _} ->
        []

      {:str, _} ->
        []

      {:su, u} ->
        [u]

      {:call, _, args} ->
        args

      {:con, _, _, args} ->
        args

      {:wrd, _, _, args} ->
        args

      {:pair, a, b} ->
        [a, b]

      {:uncons, e} ->
        [e]

      {:stream, seed, caps, _} ->
        [seed | Enum.map(caps, &elem(&1, 1))]

      {:bfold, _, caps, z, s} ->
        Enum.map(caps, &elem(&1, 1)) ++ [z, s]

      {:bcat, a, b} ->
        [a, b]

      {:blen, a} ->
        [a]

      {:beq, a, b} ->
        [a, b]

      {:bsub, s, o, n} ->
        [s, o, n]

      {:bget, s, i} ->
        [s, i]

      {:btil, s, b} ->
        [s, b]

      {:baft, s, b} ->
        [s, b]

      {:sbytes, s} ->
        [s]

      {:bunc, s} ->
        [s]

      {:scat, a, b} ->
        [a, b]

      {:slen, a} ->
        [a]

      {:seq, a, b} ->
        [a, b]

      {:js, _} ->
        []

      other ->
        other
        |> Tuple.to_list()
        |> Enum.filter(&(is_tuple(&1) or is_list(&1)))
    end
  end
end

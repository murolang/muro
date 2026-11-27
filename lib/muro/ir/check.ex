defmodule Muro.IR.Check do
  @moduledoc """
  Validates a `Muro.IR` image.

  `check/1` and `check/2` walk every function after `Muro.IR.elaborate/2`
  or `Muro.IR.Share`. They report well-scopedness, layout and arity
  agreement, the absence of erased survivors in live positions, grade
  accounting along paths, arm exhaustiveness when a book is given, and
  that closure forms appear only in the closures image.

  Grades are `:linear` (used once on every live path), `:affine` (used at
  most once on any path), and `:reuse` (unrestricted). An `:abort` path
  is bottom: it does not require leftover linear binders, but uses that
  already happened still count. If every arm is `:abort`, the match is
  unreachable. Compiler-introduced CSE lets are `:reuse`. After Share
  prunes a path, an unused `:linear` binder — a body let, or a
  parameter whose only use was dropped — is downgraded to `:affine`
  (`relax_fun/1`).

  Captures under `{:lam, ...}` are charged at formation, as in
  `Muro.Grade` and `agda/Muro/Grade.agda` (`rest` after `pop`). A
  `:reuse` binding, argument, or constructor field that mentions a
  `:linear` or `:affine` variable is refused, because copying that value
  would copy the capture.

  `letp` binders are `:affine`, as in `Muro.Check` (⇐-letp). The
  predecessor of `suc` or `wsome` takes `pred_qty` from the scrutinee:
  `:reuse` under a `:reuse` variable, `:linear` under `%1`, and
  `:affine` otherwise. Constructor field grades and binder counts are
  taken from the book; without a book they are not guessed (a missing
  book does not default those fields to `:reuse`).
  """

  alias Muro.IR

  @live_grades [:linear, :affine, :reuse]

  @doc """
  Check a list of IR functions.

  Options:

    * `:book` — the named book, used for constructor fields, field
      grades, and exhaustiveness. Without it those checks are skipped
      rather than defaulted to `:reuse`. An unknown constructor or a
      wrong binder count is an error when a book is given.
    * `:closures` — `true` when the image was elaborated with
      `closures: true`. When omitted, it is inferred from the image.
  """
  def check(funs, opts \\ []) when is_list(funs) do
    missing = Enum.flat_map(funs, &ungraded_errors/1)
    funs = Enum.map(funs, &IR.normalize_fun/1)
    closures? = Keyword.get(opts, :closures, closures_image?(funs))

    ctx = %{
      by_name: Map.new(funs, &{&1.name, &1}),
      book: Keyword.get(opts, :book),
      closures: closures?
    }

    errors =
      (missing ++ Enum.flat_map(funs, &check_fun(&1, ctx)))
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
      Enum.flat_map(fun.params, fn p ->
        n = IR.param_name(p)
        path_grade_errors(fun.name, n, IR.param_grade(p), paths)
      end)

    ret_agree = layout_agree(fun, "return", infer(fun.body, env, ctx), fun.ret)

    param_errors ++ ret_errors ++ body_errors ++ grade_errors ++ ret_agree
  end

  defp path_grade_errors(fun, name, grade, paths) do
    Enum.flat_map(paths, fn path ->
      n = Map.get(uses_of(path), name, 0)

      cond do
        dead?(path) and n <= 1 ->
          []

        true ->
          grade_error(fun, name, grade, n)
      end
    end)
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
        {[{:live, %{}}], ["#{fun.name}: erased variable #{x} used in a live position"]}

      %{^x => _} ->
        {[{:live, %{x => 1}}], []}

      _ ->
        {[{:live, %{}}], ["#{fun.name}: free variable #{x}"]}
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
        if Map.get(uses_of(p), x, 0) > 0,
          do: ["#{fun.name}: erased variable #{x} used in a live position"],
          else: []
      end)

    {Enum.map(bpaths, &drop_binder(&1, x)), errors ++ berr ++ used}
  end

  defp check_tm({:let, x, lay, g, val, body}, env, fun, ctx) do
    errors =
      if g in @live_grades,
        do: [],
        else: ["#{fun.name}: let #{x} has invalid grade #{inspect(g)}"]

    {vpaths, verr} = check_tm(val, env, fun, ctx)
    errors = errors ++ verr ++ layout_agree(fun, "let #{x}", infer(val, env, ctx), lay)
    errors = errors ++ reuse_capture_errors(fun, "let #{x}", g, val, env, lay)

    env1 = Map.put(env, x, %{grade: g, lay: lay})
    {bpaths, berr} = check_tm(body, env1, fun, ctx)
    gerr = path_grade_errors(fun.name, x, g, bpaths)

    {seq(vpaths, Enum.map(bpaths, &drop_binder(&1, x))), errors ++ berr ++ gerr}
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
      |> Map.put(a, %{grade: :affine, lay: alay})
      |> Map.put(b, %{grade: :affine, lay: blay})

    {bpaths, berr} = check_tm(body, env1, fun, ctx)

    gerr =
      path_grade_errors(fun.name, a, :affine, bpaths) ++
        path_grade_errors(fun.name, b, :affine, bpaths)

    {seq(epaths, Enum.map(bpaths, &drop_binders(&1, [a, b]))), eerr ++ berr ++ gerr}
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

    gerr = path_grade_errors(fun.name, name, g, bpaths)

    {Enum.map(bpaths, &drop_binder(&1, name)), errors ++ berr ++ gerr}
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

  defp check_tm(:abort, _env, _fun, _ctx), do: {[{:dead, %{}}], []}

  defp check_tm(t, env, fun, ctx) when is_tuple(t) do
    check_seq(tuple_children(t), env, fun, ctx)
  end

  defp check_tm(t, env, fun, ctx) when is_list(t), do: check_seq(t, env, fun, ctx)
  defp check_tm(_t, _env, _fun, _ctx), do: {[{:live, %{}}], []}

  defp check_match(s, arms, env, fun, ctx, scrut_lay) do
    {spaths, serr} = check_tm(s, env, fun, ctx)
    {apaths, aerr} = arm_paths(s, arms, scrut_lay, env, fun, ctx)
    ex = exhaust_errors(fun, scrut_lay, arms, ctx)
    {seq(spaths, apaths), serr ++ aerr ++ ex}
  end

  defp arm_paths(scrut, arms, scrut_lay, env, fun, ctx) do
    walked =
      Enum.map(arms, fn {:arm, tag, names, tm} ->
        arity = arm_arity_errors(fun, scrut_lay, tag, names, ctx)
        lays = arm_field_lays(scrut_lay, tag, names, ctx)
        grades = arm_field_grades(scrut, scrut_lay, tag, names, env, ctx)

        env1 =
          case grades do
            {:ok, gs} ->
              names
              |> Enum.zip(lays)
              |> Enum.zip(gs)
              |> Enum.reduce(env, fn {{n, lay}, g}, env ->
                Map.put(env, n, %{grade: g, lay: lay})
              end)

            :unknown ->
              Enum.zip(names, lays)
              |> Enum.reduce(env, fn {n, lay}, env ->
                Map.put(env, n, %{grade: :unknown, lay: lay})
              end)
          end

        {paths, errors} = check_tm(tm, env1, fun, ctx)

        gerr =
          case grades do
            {:ok, gs} ->
              names
              |> Enum.zip(gs)
              |> Enum.flat_map(fn {n, g} -> path_grade_errors(fun.name, n, g, paths) end)

            :unknown ->
              []
          end

        {Enum.map(paths, &drop_binders(&1, names)), arity ++ errors ++ gerr}
      end)

    case walked do
      [] ->
        {[{:dead, %{}}], []}

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

  # `Env.predQty`: reusable under a reusable scrutinee variable,
  # linear under `%1`, affine otherwise (including a non-variable).
  defp pred_qty({:var, x}, env) do
    case env do
      %{^x => %{grade: :reuse}} -> :reuse
      %{^x => %{grade: :linear}} -> :linear
      _ -> :affine
    end
  end

  defp pred_qty(_scrut, _env), do: :affine

  defp arm_field_grades(scrut, scrut_lay, tag, _names, env, ctx) do
    case {scrut_lay, tag} do
      {:nat, "suc"} ->
        {:ok, [pred_qty(scrut, env)]}

      {:nat, "zero"} ->
        {:ok, []}

      {{:opt, _}, "wsome"} ->
        {:ok, [pred_qty(scrut, env)]}

      {{:opt, _}, "wnone"} ->
        {:ok, []}

      {{:data, d}, _} ->
        case ctor_field_grades(ctx.book, d, tag) do
          :unknown -> :unknown
          gs -> {:ok, gs}
        end

      _ ->
        :unknown
    end
  end

  defp arm_arity_errors(fun, scrut_lay, tag, names, ctx) do
    case known_field_count(scrut_lay, tag, ctx) do
      n when is_integer(n) and n != length(names) ->
        ["#{fun.name}: arm #{tag} has #{length(names)} binder(s), expected #{n}"]

      _ ->
        []
    end
  end

  defp known_field_count(:nat, "suc", _ctx), do: 1
  defp known_field_count(:nat, "zero", _ctx), do: 0
  defp known_field_count({:opt, _}, "wsome", _ctx), do: 1
  defp known_field_count({:opt, _}, "wnone", _ctx), do: 0

  defp known_field_count({:data, d}, tag, ctx) do
    case ctor_field_lays(ctx.book, d, tag) do
      :unknown -> nil
      lays -> length(lays)
    end
  end

  defp known_field_count(_lay, _tag, _ctx), do: nil

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

    caps =
      args
      |> Enum.zip(callee.params)
      |> Enum.flat_map(fn {arg, p} ->
        reuse_capture_errors(
          fun,
          "argument of #{name}",
          IR.param_grade(p),
          arg,
          env,
          IR.param_lay(p)
        )
      end)

    arity ++ lays ++ caps
  end

  defp ctor_errors(fun, d, c, args, env, ctx) do
    case {ctx.book, ctor_field_lays(ctx.book, d, c), ctor_field_grades(ctx.book, d, c)} do
      {nil, _, _} ->
        []

      {_, :unknown, _} when d == "Atom" ->
        if args == [] do
          []
        else
          ["#{fun.name}: constructor #{c} has #{length(args)} field(s), expected 0"]
        end

      {_, :unknown, _} ->
        ["#{fun.name}: unknown constructor #{c}"]

      {_, lays, grades} ->
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

        caps =
          case grades do
            :unknown ->
              []

            gs ->
              args
              |> Enum.zip(lays)
              |> Enum.zip(gs)
              |> Enum.flat_map(fn {{arg, lay}, g} ->
                reuse_capture_errors(fun, "field of #{c}", g, arg, env, lay)
              end)
          end

        arity ++ agrees ++ caps
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

  defp ctor_field_grades(nil, _d, _c), do: :unknown

  defp ctor_field_grades(book, dname, cname) do
    with d when d != nil <- find_data(book, dname),
         ctor when ctor != nil <- Enum.find(d.ctors, &(&1.name == cname)) do
      live_field_grades(ctor.type)
    else
      _ -> :unknown
    end
  end

  defp live_field_grades(ty), do: live_field_grades(ty, [])

  defp live_field_grades({:pi, q, _a, _n, b}, acc) do
    if Muro.Grade.kernel_qty(q) == :erased do
      live_field_grades(b, acc)
    else
      live_field_grades(b, acc ++ [IR.live_grade(q)])
    end
  end

  defp live_field_grades(_ty, acc), do: acc

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
  defp type_lay(_book, {:word, {:ty, k}, []}) when k in [:u8, :u32, :u64], do: k
  defp type_lay(_book, {:word, :bool, []}), do: :wbool
  defp type_lay(_book, {:word, {:optk, k}, []}) when k in [:u8, :u32, :u64, :i64], do: {:opt, k}
  defp type_lay(book, {:word, :opt, [a]}), do: {:opt, type_lay(book, a)}
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

  # The default image stores a datatype as `{:data, name}`. The closures
  # image may add argument layouts. The name is the same layout.
  defp layout_agree(_fun, _where, {:data, n}, {:data, n, _}), do: []
  defp layout_agree(_fun, _where, {:data, n, _}, {:data, n}), do: []
  defp layout_agree(_fun, _where, {:data, n, a}, {:data, n, b}) when a == b, do: []

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

  defp infer({:let, x, lay, _g, _v, b}, env, ctx) do
    infer(b, Map.put(env, x, %{grade: :reuse, lay: lay}), ctx)
  end

  defp infer({:letp, a, b, e, body}, env, ctx) do
    {alay, blay} =
      case infer(e, env, ctx) do
        {:pair, x, y} -> {x, y}
        _ -> {:unknown, :unknown}
      end

    env1 =
      env
      |> Map.put(a, %{grade: :reuse, lay: alay})
      |> Map.put(b, %{grade: :reuse, lay: blay})

    infer(body, env1, ctx)
  end

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
  defp infer({:bunc, _}, _env, _ctx), do: {:data, "Maybe"}

  defp infer({:lam, name, lay, _g, body}, env, ctx) when is_binary(name) do
    {:fn, lay, infer(body, Map.put(env, name, %{grade: :reuse, lay: lay}), ctx)}
  end

  defp infer({:appv, f, _}, env, ctx), do: ret_of_fn(infer(f, env, ctx))
  defp infer({:data, name, _}, _env, _ctx), do: {:data, name}

  defp infer({:match, s, arms}, env, ctx) when is_list(arms) and arms != [] do
    infer_arm(hd(arms), infer(s, env, ctx), env, ctx)
  end

  defp infer({:match, s, _lay, arms}, env, ctx) when is_list(arms) and arms != [] do
    infer_arm(hd(arms), infer(s, env, ctx), env, ctx)
  end

  defp infer({:bfold, _, _, z, _}, env, ctx), do: infer(z, env, ctx)
  defp infer(_, _, _), do: :unknown

  defp infer_arm({:arm, tag, names, tm}, scrut_lay, env, ctx) do
    lays = arm_field_lays(scrut_lay, tag, names, ctx)

    env1 =
      Enum.zip(names, lays)
      |> Enum.reduce(env, fn {n, lay}, env ->
        Map.put(env, n, %{grade: :reuse, lay: lay})
      end)

    infer(tm, env1, ctx)
  end

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
    Enum.reduce(tms, {[{:live, %{}}], []}, fn tm, {paths, errors} ->
      {ps, es} = check_tm(tm, env, fun, ctx)
      {seq(paths, ps), errors ++ es}
    end)
  end

  defp seq(ps, qs) do
    Enum.flat_map(ps, fn p -> Enum.flat_map(qs, &seq_one(p, &1)) end)
  end

  defp seq_one({:dead, u}, _q), do: [{:dead, u}]
  defp seq_one({:live, u}, {:dead, v}), do: [{:dead, add_uses(u, v)}]
  defp seq_one({:live, u}, {:live, v}), do: [{:live, add_uses(u, v)}]

  defp add_uses(a, b) do
    Map.merge(a, b, fn _k, x, y -> x + y end)
  end

  defp uses_of({:live, u}), do: u
  defp uses_of({:dead, u}), do: u
  defp dead?({:dead, _}), do: true
  defp dead?({:live, _}), do: false

  defp drop_binder({:live, u}, x), do: {:live, Map.delete(u, x)}
  defp drop_binder({:dead, u}, x), do: {:dead, Map.delete(u, x)}
  defp drop_binders(path, names), do: Enum.reduce(names, path, &drop_binder(&2, &1))

  # A `:reuse` binding or argument may not mention a linear or affine
  # variable. `Muro.Grade` charges λ-captures at formation; copying the
  # value would copy those captures (`affine variable used as reusable`).
  # A + position whose type is Data copies by value, so an affine or
  # linear variable may be moved there once (as in `Muro.Check.reuse_arg_uses/4`).
  # A function (or other non-Data) type would scale those uses to ω.
  defp reuse_capture_errors(_fun, _where, g, _tm, _env, _lay) when g != :reuse, do: []

  defp reuse_capture_errors(fun, where, :reuse, tm, env, lay) do
    if data_lay?(lay) do
      []
    else
      names = tm |> restricted_free(env, MapSet.new()) |> Enum.uniq()

      case names do
        [] ->
          []

        ns ->
          ["#{fun.name}: #{where} uses #{Enum.join(ns, ", ")} as reusable"]
      end
    end
  end

  # `Muro.Check.is_data/3`: a + argument of a Data type copies by value.
  defp data_lay?(:nat), do: true
  defp data_lay?(:unit), do: true
  defp data_lay?(:string), do: true
  defp data_lay?(:slice), do: true
  defp data_lay?(:u8), do: true
  defp data_lay?(:u32), do: true
  defp data_lay?(:u64), do: true
  defp data_lay?(:i64), do: true
  defp data_lay?(:wbool), do: true
  defp data_lay?({:data, _}), do: true
  defp data_lay?({:data, _, _}), do: true
  defp data_lay?({:opt, a}), do: data_lay?(a)
  defp data_lay?({:pair, a, b}), do: data_lay?(a) and data_lay?(b)
  defp data_lay?(_), do: false

  defp restricted_free({:var, x}, env, bound) do
    if MapSet.member?(bound, x) do
      []
    else
      case env do
        %{^x => %{grade: g}} when g in [:linear, :affine] -> [x]
        _ -> []
      end
    end
  end

  defp restricted_free({:let, x, _, _, v, b}, env, bound) do
    restricted_free(v, env, bound) ++ restricted_free(b, env, MapSet.put(bound, x))
  end

  defp restricted_free({:lam, name, _, _, body}, env, bound) when is_binary(name),
    do: restricted_free(body, env, MapSet.put(bound, name))

  defp restricted_free({:letp, a, b, e, body}, env, bound) do
    restricted_free(e, env, bound) ++
      restricted_free(body, env, bound |> MapSet.put(a) |> MapSet.put(b))
  end

  defp restricted_free({:match, s, arms}, env, bound) when is_list(arms) do
    restricted_free(s, env, bound) ++ restricted_free_arms(arms, env, bound)
  end

  defp restricted_free({:match, s, _lay, arms}, env, bound) when is_list(arms) do
    restricted_free(s, env, bound) ++ restricted_free_arms(arms, env, bound)
  end

  defp restricted_free(t, env, bound) when is_tuple(t) do
    Enum.flat_map(tuple_children(t), &restricted_free(&1, env, bound))
  end

  defp restricted_free(t, env, bound) when is_list(t),
    do: Enum.flat_map(t, &restricted_free(&1, env, bound))

  defp restricted_free(_t, _env, _bound), do: []

  defp restricted_free_arms(arms, env, bound) do
    Enum.flat_map(arms, fn {:arm, _, names, tm} ->
      restricted_free(tm, env, MapSet.union(bound, MapSet.new(names)))
    end)
  end

  defp ungraded_errors(fun) do
    params =
      Enum.flat_map(fun.params, fn
        {n, _lay} when is_binary(n) ->
          ["#{fun.name}: parameter #{n} is missing a grade"]

        _ ->
          []
      end)

    params ++ ungraded_tm(fun.name, fun.body)
  end

  defp ungraded_tm(fun, {:let, x, _lay, _v, b} = t) when tuple_size(t) == 5 do
    ["#{fun}: let #{x} is missing a grade"] ++ ungraded_tm(fun, b)
  end

  defp ungraded_tm(fun, {:lam, name, _lay, body} = t)
       when is_binary(name) and tuple_size(t) == 4 do
    ["#{fun}: λ #{name} is missing a grade"] ++ ungraded_tm(fun, body)
  end

  defp ungraded_tm(fun, t) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.flat_map(&ungraded_tm(fun, &1))
  end

  defp ungraded_tm(fun, t) when is_list(t), do: Enum.flat_map(t, &ungraded_tm(fun, &1))
  defp ungraded_tm(_fun, _t), do: []

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

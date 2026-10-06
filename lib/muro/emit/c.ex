defmodule Muro.Emit.C do
  @moduledoc """
  Emit a closed run book to C. Specs and evidence are omitted.

  `Nat` is a tagged struct. User data, indexed data included, is a tag
  plus fields. `match` is a `switch`. Erased arguments are dropped.
  `run internal` is `static`.

  A `run` stream is a struct: the seed, an environment for values the
  step closes over, and a function pointer for the step. `uncons` calls
  that function and builds a new struct for the tail. `Always`, `~`,
  and a raw `ν` in a run are refused (`c:stream`). `I64`, `F32`, and
  `Tensor` are refused (`c:machine`). A lambda that is not an unfold
  step is `c:lambda`.
  """

  alias Muro.{Ast, Emit}

  @c_keywords ~w(
    auto break case char const continue default do double else enum extern
    float for goto if inline int long register restrict return short signed
    sizeof static struct switch typedef union unsigned void volatile while
  ) |> MapSet.new()

  @reserved ~w(
    muro_nat muro_unit muro_pair muro_zero muro_suc muro_tt muro_nat_new muro_mk_pair
    muro_stream muro_stream_new muro_envp muro_seedp muro_ep
  ) |> MapSet.new()

  @doc """
  Render `book` as `{header, source}` for a file stem such as `half_ok`.
  """
  def render(book, stem) when is_list(book) and is_binary(stem) do
    runs = Emit.run_defs(book)

    case reject(runs) do
      nil ->
        case compile_runs(runs, book) do
          {:ok, sigs, funs, extras} ->
            {:ok, {header(book, sigs, stem), source(book, runs, sigs, funs, extras, stem)}}

          {:error, _} = err ->
            err
        end

      err ->
        {:error, err}
    end
  end

  defp reject(runs) do
    Enum.find_value(runs, fn d ->
      case forbid(d.type) || forbid(d.body) do
        nil -> nil
        kind -> "c:#{kind}"
      end
    end)
  end

  defp forbid(t) do
    case classify(t) do
      nil -> forbid_children(t)
      kind -> kind
    end
  end

  defp forbid_children(t) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.find_value(&forbid/1)
  end

  defp forbid_children(t) when is_list(t), do: Enum.find_value(t, &forbid/1)
  defp forbid_children(_), do: nil

  defp classify({:nu, _, _}), do: :stream
  defp classify({:always, _, _, _}), do: :stream
  defp classify({:bisim, _, _}), do: :stream
  defp classify(:i64), do: :machine
  defp classify(:f32ty), do: :machine
  defp classify({:tensor, _, _}), do: :machine
  defp classify({:addi, _, _}), do: :machine
  defp classify({:muli, _, _}), do: :machine
  defp classify({:addt, _, _}), do: :machine
  defp classify({:toi64, _}), do: :machine
  defp classify({:packi, _, _}), do: :machine
  defp classify(_), do: nil

  defp compile_runs(runs, book) do
    Enum.reduce_while(runs, {:ok, [], [], [], 0}, fn d, {:ok, sigs, funs, extras, k} ->
      case compile_def(d, book, k) do
        {:ok, sig, fun, extra, k1} ->
          {:cont, {:ok, sigs ++ [sig], funs ++ [fun], extras ++ extra, k1}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
    |> case do
      {:ok, sigs, funs, extras, _k} -> {:ok, sigs, funs, extras}
      err -> err
    end
  end

  defp compile_def(d, book, k) do
    with {:ok, sig} <- signature(d, book),
         {:ok, {pre, expr, st}} <-
           emit(sig.inner, sig.env, book, %{t: 0, s: 0, k: k, steps: [], envs: []}, sig.ret) do
      body =
        if pre == "" do
          "  return #{expr};"
        else
          indent(pre, 2) <> "\n  return #{expr};"
        end

      {:ok, sig, "#{decl(sig)} {\n#{body}\n}", st.envs ++ st.steps, st.k}
    end
  end

  defp signature(d, book) do
    {pis, ret} = telescope(d.type)

    case peel_lams(d.body, length(pis)) do
      {:ok, lams, inner} ->
        bound =
          Enum.zip(pis, lams)
          |> Enum.map(fn {{q, a, _x}, {lq, lname}} ->
            {lname, ctype(a, book), q == :erased or lq == :erased}
          end)

        {named, _used} =
          Enum.map_reduce(bound, MapSet.new(), fn {muro, ty, erased}, used ->
            {c, used} = fresh(c_name(muro), used)
            {{muro, c, ty, erased}, used}
          end)

        params = for {_muro, c, ty, false} <- named, do: {ty, c}

        env =
          Enum.reduce(named, [], fn {muro, c, _ty, erased}, env ->
            [{muro, c, if(erased, do: :erased, else: :live)} | env]
          end)

        {:ok,
         %{
           name: c_name(d.name),
           export: Map.get(d, :export, true),
           params: params,
           ret: ctype(ret, book),
           env: env,
           inner: inner
         }}

      {:error, _} = err ->
        err
    end
  end

  defp peel_lams(t, 0), do: {:ok, [], t}

  defp peel_lams({:lam, q, _a, x, t}, n) when n > 0 do
    case peel_lams(t, n - 1) do
      {:ok, rest, inner} -> {:ok, [{q, x} | rest], inner}
      err -> err
    end
  end

  defp peel_lams(_, _), do: {:error, "c:unsupported"}

  defp telescope(t), do: telescope(t, [])
  defp telescope({:pi, q, a, x, b}, acc), do: telescope(b, [{q, a, x} | acc])
  defp telescope(ret, acc), do: {Enum.reverse(acc), ret}

  defp decl(sig) do
    args =
      case sig.params do
        [] -> "void"
        ps -> Enum.map_join(ps, ", ", fn {ty, name} -> "#{ty}#{name}" end)
      end

    kw = if sig.export, do: "", else: "static "
    "#{kw}#{sig.ret}#{sig.name}(#{args})"
  end

  defp emit({:var, name}, env, book, st, _expect) do
    case lookup(env, name) do
      nil -> emit_global(name, [], env, book, st)
      {:erased, _} -> {:error, "c:erased"}
      {:live, c} -> {:ok, {"", c, st}}
    end
  end

  defp emit({:def, name}, env, book, st, expect), do: emit({:var, name}, env, book, st, expect)
  defp emit(:ze, _env, _book, st, _expect), do: {:ok, {"", "muro_zero()", st}}
  defp emit(:one, _env, _book, st, _expect), do: {:ok, {"", "muro_tt()", st}}

  defp emit({:su, u}, env, book, st, _expect) do
    with {:ok, {pre, ex, st}} <- emit(u, env, book, st, "muro_nat *") do
      {:ok, {pre, "muro_suc(#{ex})", st}}
    end
  end

  defp emit({:ann, e, _a}, env, book, st, expect), do: emit(e, env, book, st, expect)
  defp emit({:rwt, _eq, _x, _p, t}, env, book, st, expect), do: emit(t, env, book, st, expect)

  defp emit({:app, _, _} = t, env, book, st, _expect) do
    case spine(t, []) do
      {{:var, name}, args} ->
        if lookup(env, name) == nil do
          emit_global(name, args, env, book, st)
        else
          {:error, "c:lambda"}
        end

      _ ->
        {:error, "c:lambda"}
    end
  end

  defp emit({:mnat, e, _x, _p, z, y, s}, env, book, st, expect) do
    with {:ok, {pre, scrut, st}} <- emit(e, env, book, st, "muro_nat *") do
      {sname, st} = news(st)
      {tname, st} = newt(st)

      with {:ok, {zpre, zex, st}} <- emit(z, env, book, st, expect) do
        {yname, env1} = bind_one(y, env)

        with {:ok, {spre, sex, st}} <- emit(s, env1, book, st, expect) do
          stmt =
            squash([
              pre,
              "#{expect}#{tname} = 0;",
              "{",
              "muro_nat *#{sname} = #{scrut};",
              "switch (#{sname}->tag) {",
              "case 0: {",
              zpre,
              "#{tname} = #{zex};",
              "break;",
              "}",
              "case 1: {",
              "muro_nat *#{yname} = #{sname}->suc;",
              spre,
              "#{tname} = #{sex};",
              "break;",
              "}",
              "default: {",
              "/* unreachable */",
              "abort();",
              "}",
              "}",
              "}"
            ])

          {:ok, {stmt, tname, st}}
        end
      end
    end
  end

  defp emit({:mdata, _e, _x, _p, []}, _env, _book, _st, _expect), do: {:error, "c:unsupported"}

  defp emit({:mdata, e, _x, _p, [{cname, _, _} | _] = branches}, env, book, st, expect) do
    case data_of_ctor(book, cname) do
      nil ->
        {:error, "c:unsupported"}

      data ->
        ptr = struct_ptr(data.name)

        with {:ok, {pre, scrut, st}} <- emit(e, env, book, st, ptr) do
          {sname, st} = news(st)
          {tname, st} = newt(st)

          case emit_cases(branches, data, sname, tname, env, book, st, expect) do
            {:ok, {cases, st}} ->
              stmt =
                squash([
                  pre,
                  "#{expect}#{tname} = 0;",
                  "{",
                  "#{ptr}#{sname} = #{scrut};",
                  "switch (#{sname}->tag) {",
                  cases,
                  "default: {",
                  "/* unreachable */",
                  "abort();",
                  "}",
                  "}",
                  "}"
                ])

              {:ok, {stmt, tname, st}}

            {:error, _} = err ->
              err
          end
        end
    end
  end

  defp emit({:munit, e, _x, _p, u}, env, book, st, expect) do
    with {:ok, {pre, ex, st}} <- emit(e, env, book, st, "muro_unit *") do
      {sname, st} = news(st)

      with {:ok, {pre2, ex2, st}} <- emit(u, env, book, st, expect) do
        stmt =
          squash([
            pre,
            "muro_unit *#{sname} = #{ex};",
            "(void)#{sname};",
            pre2
          ])

        {:ok, {stmt, ex2, st}}
      end
    end
  end

  defp emit({:memp, e, _x, _p}, env, book, st, _expect) do
    with {:ok, {pre, ex, st}} <- emit(e, env, book, st, "void *") do
      stmt = squash([pre, "(void)(#{ex});", "/* unreachable */", "abort();"])
      {:ok, {stmt, "0", st}}
    end
  end

  defp emit({:pair, a, b}, env, book, st, _expect) do
    with {:ok, {pre, ea, st}} <- emit(a, env, book, st, "void *"),
         {:ok, {pre2, eb, st}} <- emit(b, env, book, st, "void *") do
      {:ok, {squash([pre, pre2]), "muro_mk_pair(#{ea}, #{eb})", st}}
    end
  end

  defp emit({:letp, e, a, b, t}, env, book, st, expect) do
    with {:ok, {pre, ex, st}} <- emit(e, env, book, st, "muro_pair *") do
      {sname, st} = news(st)
      {ca, used} = fresh(c_name(a), MapSet.new())
      {cb, _} = fresh(c_name(b), used)
      env1 = [{b, cb, :live}, {a, ca, :live} | env]

      with {:ok, {pre2, ex2, st}} <- emit(t, env1, book, st, expect) do
        stmt =
          squash([
            pre,
            "muro_pair *#{sname} = #{ex};",
            "void *#{ca} = #{sname}->fst;",
            "void *#{cb} = #{sname}->snd;",
            pre2
          ])

        {:ok, {stmt, ex2, st}}
      end
    end
  end

  defp emit({:unf, seed, {:lam, q, dom, x, body}}, env, book, st, _expect) do
    seed_ty = ctype(dom, book)

    with {:ok, {pre, seed_ex, st}} <- emit(seed, env, book, st, seed_ty) do
      id = st.k
      st = %{st | k: id + 1}
      caps = capture_fields(body, x, env)
      {env_ty, env_pre, env_ex, st} = alloc_env(caps, id, st)
      step = "muro_step_#{id}"

      with {:ok, {src, st}} <-
             emit_step(step, q, x, seed_ty, body, caps, env_ty, env, book, st) do
        expr = "muro_stream_new(#{seed_ex}, #{env_ex}, #{step})"
        {:ok, {squash([pre, env_pre]), expr, %{st | steps: st.steps ++ [src]}}}
      end
    end
  end

  defp emit({:unf, _, _}, _env, _book, _st, _expect), do: {:error, "c:lambda"}

  defp emit({:ucons, s}, env, book, st, _expect) do
    with {:ok, {pre, ex, st}} <- emit(s, env, book, st, "muro_stream *") do
      {sname, st} = news(st)
      {pname, st} = news(st)
      {hname, st} = news(st)
      {nname, st} = news(st)
      {tname, st} = news(st)

      stmt =
        squash([
          "#{stream_ptr()}#{sname} = #{ex};",
          "muro_pair *#{pname} = #{sname}->step(#{sname}->env, #{sname}->seed);",
          "void *#{hname} = #{pname}->fst;",
          "void *#{nname} = #{pname}->snd;",
          "#{stream_ptr()}#{tname} = muro_stream_new(#{nname}, #{sname}->env, #{sname}->step);"
        ])

      {:ok, {squash([pre, stmt]), "muro_mk_pair(#{hname}, #{tname})", st}}
    end
  end

  defp emit({:lam, _, _, _, _}, _env, _book, _st, _expect), do: {:error, "c:lambda"}

  defp emit({:atom, name}, _env, _book, st, _expect), do: {:ok, {"", atom_c(name), st}}

  defp emit({:matom, e, _x, _p, bs}, env, book, st, expect) do
    with {:ok, {pre, scrut, st}} <- emit(e, env, book, st, "muro_atom ") do
      {sname, st} = news(st)
      {tname, st} = newt(st)

      case emit_atom_cases(bs, tname, env, book, st, expect) do
        {:ok, {cases, st}} ->
          stmt =
            squash([
              pre,
              "#{expect}#{tname} = 0;",
              "{",
              "muro_atom #{sname} = #{scrut};",
              "switch (#{sname}) {",
              cases,
              "default: {",
              "abort();",
              "}",
              "}",
              "}"
            ])

          {:ok, {stmt, tname, st}}

        {:error, _} = err ->
          err
      end
    end
  end

  defp emit(_other, _env, _book, _st, _expect), do: {:error, "c:unsupported"}

  defp emit_step(step, q, x, seed_ty, body, caps, env_ty, env, book, st) do
    cap_env =
      Enum.reduce(Enum.reverse(caps), env, fn {name, field, _outer}, env ->
        [{name, "muro_ep->#{field}", :live} | env]
      end)

    {seed_local, seed_env} =
      case q do
        :erased ->
          {nil, [{x, "muro_seedp", :erased} | cap_env]}

        _ ->
          used = MapSet.new(["muro_ep", "muro_envp", "muro_seedp" | Enum.map(caps, &elem(&1, 1))])
          {local, _} = fresh(c_name(x), used)
          {local, [{x, local, :live} | cap_env]}
      end

    with {:ok, {pre, expr, st}} <- emit(body, seed_env, book, st, "muro_pair *") do
      prelude =
        cond do
          pre == "" -> "  return #{expr};"
          true -> indent(pre, 2) <> "\n  return #{expr};"
        end

      src = """
      static muro_pair *#{step}(void *muro_envp, void *muro_seedp) {
      #{step_bind(q, seed_ty, seed_local, caps, env_ty)}
      #{prelude}
      }
      """

      {:ok, {String.trim(src), st}}
    end
  end

  defp step_bind(q, seed_ty, seed_local, caps, env_ty) do
    env_line =
      if caps == [] do
        "  (void)muro_envp;"
      else
        "  #{env_ty} *muro_ep = muro_envp;"
      end

    seed_line =
      if q == :erased or seed_local == nil do
        "  (void)muro_seedp;"
      else
        "  #{seed_ty}#{seed_local} = muro_seedp;"
      end

    env_line <> "\n" <> seed_line
  end

  defp alloc_env([], _id, st), do: {nil, "", "0", st}

  defp alloc_env(caps, id, st) do
    env_ty = "muro_env_#{id}"
    var = "muro_ep#{id}"

    fields = Enum.map_join(caps, "\n", fn {_name, field, _outer} -> "  void *#{field};" end)

    typedef = """
    typedef struct {
    #{fields}
    } #{env_ty};
    """

    assigns =
      Enum.map_join(caps, "\n", fn {_name, field, outer} ->
        "#{var}->#{field} = #{outer};"
      end)

    pre = """
    #{env_ty} *#{var} = malloc(sizeof *#{var});
    if (#{var} == 0) abort();
    #{assigns}
    """

    {env_ty, String.trim(pre), var, %{st | envs: st.envs ++ [String.trim(typedef)]}}
  end

  defp capture_fields(body, binder, env) do
    body
    |> free_names(MapSet.new([binder]))
    |> Enum.uniq()
    |> Enum.flat_map(fn name ->
      case lookup(env, name) do
        {:live, c} -> [{name, c}]
        _ -> []
      end
    end)
    |> then(fn caps ->
      {named, _} =
        Enum.map_reduce(caps, MapSet.new(), fn {name, outer}, used ->
          {field, used} = fresh(c_name(name), used)
          {{name, field, outer}, used}
        end)

      named
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
        bound1 = Enum.reduce(binders, bound, &MapSet.put(&2, &1))
        free_names(body, bound1)
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

  defp free_names(t, bound) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.flat_map(&free_names(&1, bound))
  end

  defp free_names(t, bound) when is_list(t), do: Enum.flat_map(t, &free_names(&1, bound))
  defp free_names(_, _), do: []

  defp emit_atom_cases(bs, tname, env, book, st, expect) do
    Enum.reduce_while(bs, {:ok, {[], st}}, fn {name, body}, {:ok, {acc, st}} ->
      case emit(body, env, book, st, expect) do
        {:ok, {bpre, bex, st}} ->
          text =
            squash([
              "case #{atom_c(name)}: {",
              bpre,
              "#{tname} = #{bex};",
              "break;",
              "}"
            ])

          {:cont, {:ok, {acc ++ [text], st}}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
    |> case do
      {:ok, {cases, st}} -> {:ok, {Enum.join(cases, "\n"), st}}
      err -> err
    end
  end

  defp emit_cases(branches, data, sname, tname, env, book, st, expect) do
    Enum.reduce_while(branches, {:ok, {[], st}}, fn {cname, binders, body}, {:ok, {acc, st}} ->
      case branch_case(cname, binders, body, data, sname, tname, env, book, st, expect) do
        {:ok, {text, st}} -> {:cont, {:ok, {acc ++ [text], st}}}
        {:error, _} = err -> {:halt, err}
      end
    end)
    |> case do
      {:ok, {cases, st}} -> {:ok, {Enum.join(cases, "\n"), st}}
      err -> err
    end
  end

  defp branch_case(cname, binders, body, data, sname, tname, env, book, st, expect) do
    ctor = Enum.find(data.ctors, &(&1.name == cname))
    tag = Enum.find_index(data.ctors, &(&1.name == cname))

    if ctor == nil or tag == nil do
      {:error, "c:unsupported"}
    else
      case open_branch(binders, ctor, sname, env, book) do
        {:ok, {decls, env1}} ->
          with {:ok, {pre, ex, st}} <- emit(body, env1, book, st, expect) do
            text =
              squash([
                "case #{tag}: {",
                decls,
                pre,
                "#{tname} = #{ex};",
                "break;",
                "}"
              ])

            {:ok, {text, st}}
          end

        {:error, _} = err ->
          err
      end
    end
  end

  defp open_branch(binders, ctor, sname, env, book) do
    {pis, _} = telescope(ctor.type)

    if length(binders) != length(pis) do
      {:error, "c:unsupported"}
    else
      member = c_name(ctor.name)

      {decls, env1, _used, _k} =
        Enum.reduce(Enum.zip(binders, pis), {[], env, MapSet.new(), 0}, fn
          {bname, {:erased, _a, _x}}, {decls, env, used, k} ->
            {c, used} = fresh(c_name(bname), used)
            decl = "void *#{c} = 0;"
            {decls ++ [decl], [{bname, c, :live} | env], used, k}

          {bname, {_q, a, _x}}, {decls, env, used, k} ->
            {c, used} = fresh(c_name(bname), used)
            ty = ctype(a, book)
            decl = "#{ty}#{c} = #{sname}->as.#{member}.f#{k};"
            {decls ++ [decl], [{bname, c, :live} | env], used, k + 1}
        end)

      {:ok, {Enum.join(decls, "\n"), env1}}
    end
  end

  defp emit_global(name, args, env, book, st) do
    specs = live_args(book, name, args)
    need = live_count(book, name)

    cond do
      need != :unknown and length(specs) != need ->
        {:error, "c:lambda"}

      true ->
        with {:ok, {pres, exprs, st}} <- emit_specs(specs, env, book, st) do
          {:ok, {squash(pres), "#{c_name(name)}(#{Enum.join(exprs, ", ")})", st}}
        end
    end
  end

  defp emit_specs(specs, env, book, st) do
    Enum.reduce_while(specs, {:ok, {[], [], st}}, fn {a, ty}, {:ok, {pres, exprs, st}} ->
      case emit(a, env, book, st, ty) do
        {:ok, {pre, ex, st}} -> {:cont, {:ok, {pres ++ [pre], exprs ++ [ex], st}}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp live_args(book, name, args) do
    qtys = quantities(book, name)
    extra = max(length(args) - length(qtys), 0)
    padded = qtys ++ List.duplicate({:live, "void *"}, extra)

    args
    |> Enum.zip(padded)
    |> Enum.flat_map(fn
      {_a, :erased} -> []
      {a, {:live, ty}} -> [{a, ty}]
    end)
  end

  defp live_count(book, name) do
    case quantities(book, name) do
      [] ->
        if find_ctor(book, name) == nil and find_def(book, name) == nil, do: :unknown, else: 0

      qtys ->
        Enum.count(qtys, &(&1 != :erased))
    end
  end

  defp quantities(book, name) do
    type =
      cond do
        ctor = find_ctor(book, name) -> ctor.type
        defn = find_def(book, name) -> defn.type
        true -> nil
      end

    case type do
      nil ->
        []

      ty ->
        {pis, _} = telescope(ty)

        Enum.map(pis, fn
          {:erased, _, _} -> :erased
          {_, a, _} -> {:live, ctype(a, book)}
        end)
    end
  end

  defp find_ctor(book, name) do
    Enum.find_value(book, fn
      %{kind: :data, ctors: cs} -> Enum.find(cs, &(&1.name == name))
      _ -> nil
    end)
  end

  defp find_def(book, name) do
    Enum.find(book, &(Map.get(&1, :kind, :def) != :data and &1.name == name))
  end

  defp data_of_ctor(book, name) do
    Enum.find(book, fn
      %{kind: :data, ctors: cs} -> Enum.any?(cs, &(&1.name == name))
      _ -> false
    end)
  end

  defp lookup(env, name) do
    Enum.find_value(env, fn
      {^name, c, kind} -> {kind, c}
      _ -> nil
    end)
  end

  defp bind_one(name, env) do
    c = c_name(name)
    {c, [{name, c, :live} | env]}
  end

  defp news(st), do: {"muro_s#{st.s}", %{st | s: st.s + 1}}
  defp newt(st), do: {"muro_t#{st.t}", %{st | t: st.t + 1}}

  defp spine({:app, f, a}, acc), do: spine(f, [a | acc])
  defp spine(h, acc), do: {h, acc}

  defp ctype(:atom, _book), do: "muro_atom "
  defp ctype(:nat, _book), do: "muro_nat *"
  defp ctype(:unit, _book), do: "muro_unit *"
  defp ctype({:stream, _}, _book), do: "muro_stream *"

  defp ctype({:var, name}, book) do
    if data?(book, name), do: struct_ptr(name), else: "void *"
  end

  defp ctype({:app, f, _a}, book), do: ctype(f, book)
  defp ctype(_, _book), do: "void *"

  defp data?(book, name) do
    Enum.any?(book, &(Map.get(&1, :kind) == :data and &1.name == name))
  end

  defp struct_ptr(name), do: struct_name(name) <> " *"

  defp struct_name(name) do
    base = "muro_" <> (safe(name) |> String.downcase())

    if base in ~w(muro_nat muro_unit muro_pair) do
      "muro_ty_" <> String.downcase(safe(name))
    else
      base
    end
  end

  defp c_name(name) do
    n = safe(name)

    cond do
      n == "" or n == "_" -> "x"
      String.match?(n, ~r/^[0-9]/) -> "muro_" <> n
      MapSet.member?(@c_keywords, n) -> "muro_" <> n
      MapSet.member?(@reserved, n) -> "muro_" <> n
      String.starts_with?(n, "_") -> "muro_" <> n
      String.match?(n, ~r/^muro_[st][0-9]+$/) -> "muro_" <> n
      true -> n
    end
  end

  defp safe(name) do
    name
    |> String.replace("-", "_")
    |> String.replace("'", "_")
  end

  defp fresh(base, used) do
    name = if MapSet.member?(used, base), do: bump(base, 2, used), else: base
    {name, MapSet.put(used, name)}
  end

  defp bump(base, i, used) do
    n = "#{base}_#{i}"
    if MapSet.member?(used, n), do: bump(base, i + 1, used), else: n
  end

  defp squash(parts) do
    parts
    |> Enum.flat_map(fn
      nil -> []
      "" -> []
      s when is_binary(s) -> String.split(s, "\n")
    end)
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n")
  end

  defp indent(s, n) do
    pad = String.duplicate(" ", n)
    s |> String.split("\n") |> Enum.map_join("\n", &(pad <> &1))
  end

  defp header(book, sigs, stem) do
    g = guard(stem)

    parts = [
      "/* generated by muro — do not edit */",
      "#ifndef #{g}",
      "#define #{g}",
      "#include <stdint.h>",
      nat_struct(),
      unit_struct(),
      atom_enum(book),
      stream_typedef(sigs),
      data_structs(book),
      prototypes(sigs),
      "#endif"
    ]

    join_parts(parts)
  end

  defp source(book, runs, sigs, funs, extras, stem) do
    internals =
      sigs
      |> Enum.reject(& &1.export)
      |> Enum.map_join("\n", &"#{decl(&1)};")

    parts = [
      "/* generated by muro — do not edit */",
      "#include \"#{stem}.h\"",
      "#include <stdlib.h>",
      nat_helpers(),
      unit_helpers(),
      pair_helpers(runs),
      stream_helpers(runs, exports_stream?(sigs)),
      data_ctors(book),
      internals,
      Enum.join(extras, "\n\n"),
      Enum.join(funs, "\n\n")
    ]

    join_parts(parts)
  end

  defp join_parts(parts) do
    parts
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n")
    |> Kernel.<>("\n")
  end

  defp prototypes(sigs) do
    sigs
    |> Enum.filter(& &1.export)
    |> Enum.map_join("\n", &"#{decl(&1)};")
  end

  defp guard(stem) do
    body =
      stem
      |> String.upcase()
      |> String.replace(~r/[^A-Z0-9]/, "_")

    "MURO_#{body}_H"
  end

  defp atom_enum(book) do
    case Ast.atoms(book) do
      [] ->
        ""

      names ->
        consts = Enum.map_join(names, ",\n  ", &atom_c/1)

        """
        typedef enum {
          #{consts}
        } muro_atom;
        """
        |> String.trim()
    end
  end

  defp atom_c(name) do
    "MURO_" <> (name |> safe() |> String.upcase())
  end

  defp nat_struct do
    """
    typedef struct muro_nat muro_nat;
    struct muro_nat { uint8_t tag; muro_nat *suc; }; /* 0 = zero, 1 = suc */
    """
    |> String.trim()
  end

  defp unit_struct do
    """
    typedef struct muro_unit muro_unit;
    struct muro_unit { uint8_t tag; };
    """
    |> String.trim()
  end

  defp nat_helpers do
    """
    static muro_nat *muro_nat_new(uint8_t tag, muro_nat *suc) {
      muro_nat *p = malloc(sizeof *p);
      if (p == 0) abort();
      p->tag = tag;
      p->suc = suc;
      return p;
    }

    static muro_nat *muro_zero(void) { return muro_nat_new(0, 0); }

    static muro_nat *muro_suc(muro_nat *n) { return muro_nat_new(1, n); }
    """
    |> String.trim()
  end

  defp unit_helpers do
    """
    static muro_unit muro_tt_obj = {0};

    static muro_unit *muro_tt(void) { return &muro_tt_obj; }
    """
    |> String.trim()
  end

  defp pair_helpers(runs) do
    if mentions?(runs, &pair_form?/1) or mentions?(runs, &stream_form?/1) do
      """
      typedef struct muro_pair_s { void *fst; void *snd; } muro_pair;

      static muro_pair *muro_mk_pair(void *fst, void *snd) {
        muro_pair *p = malloc(sizeof *p);
        if (p == 0) abort();
        p->fst = fst;
        p->snd = snd;
        return p;
      }
      """
      |> String.trim()
    else
      ""
    end
  end

  defp pair_form?({:pair, _, _}), do: true
  defp pair_form?({:letp, _, _, _, _}), do: true
  defp pair_form?(_), do: false

  defp stream_form?({:stream, _}), do: true
  defp stream_form?({:unf, _, _}), do: true
  defp stream_form?({:ucons, _}), do: true
  defp stream_form?(_), do: false

  defp stream_ptr, do: "muro_stream *"

  defp exports_stream?(sigs) do
    Enum.any?(sigs, fn sig ->
      sig.export and
        (stream_ty?(sig.ret) or Enum.any?(sig.params, fn {ty, _} -> stream_ty?(ty) end))
    end)
  end

  defp stream_ty?(ty), do: String.starts_with?(ty, "muro_stream ")

  defp stream_typedef(sigs) do
    if exports_stream?(sigs), do: "typedef struct muro_stream muro_stream;", else: ""
  end

  defp stream_helpers(runs, exported?) do
    if mentions?(runs, &stream_form?/1) do
      decl = if exported?, do: "", else: "typedef struct muro_stream muro_stream;"

      """
      #{decl}
      struct muro_stream {
        void *seed;
        void *env;
        muro_pair *(*step)(void *env, void *seed);
      };

      static muro_stream *muro_stream_new(void *seed, void *env, muro_pair *(*step)(void *env, void *seed)) {
        muro_stream *p = malloc(sizeof *p);
        if (p == 0) abort();
        p->seed = seed;
        p->env = env;
        p->step = step;
        return p;
      }
      """
      |> String.trim()
    else
      ""
    end
  end

  defp mentions?(runs, pred) do
    Enum.any?(runs, fn d -> walk?(d.type, pred) or walk?(d.body, pred) end)
  end

  defp walk?(t, pred) do
    pred.(t) or walk_children?(t, pred)
  end

  defp walk_children?(t, pred) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.any?(&walk?(&1, pred))
  end

  defp walk_children?(t, pred) when is_list(t), do: Enum.any?(t, &walk?(&1, pred))
  defp walk_children?(_, _), do: false

  defp data_structs(book) do
    datas = data_defs(book)

    if datas == [],
      do: "",
      else: typedefs(datas) <> "\n" <> Enum.map_join(datas, "\n", &struct_src(&1, book))
  end

  defp typedefs(datas) do
    Enum.map_join(datas, "\n", fn d ->
      n = struct_name(d.name)
      "typedef struct #{n} #{n};"
    end)
  end

  defp struct_src(d, book) do
    name = struct_name(d.name)

    members =
      d.ctors
      |> Enum.with_index()
      |> Enum.map(fn {ctor, tag} ->
        {pis, _} = telescope(ctor.type)

        fs =
          pis
          |> Enum.reject(fn {q, _, _} -> q == :erased end)
          |> Enum.with_index()
          |> Enum.map(fn {{_, a, _}, k} -> "    #{ctype(a, book)}f#{k};" end)

        {tag, ctor.name, fs}
      end)

    comment = Enum.map_join(members, ", ", fn {tag, cname, _} -> "#{cname} = #{tag}" end)

    union_members =
      Enum.flat_map(members, fn {_tag, cname, fs} ->
        if fs == [] do
          []
        else
          ["    struct {\n#{Enum.join(fs, "\n")}\n    } #{c_name(cname)};"]
        end
      end)

    union_body = Enum.join(["    char unused;" | union_members], "\n")

    """
    struct #{name} {
      uint8_t tag; /* #{comment} */
      union {
    #{union_body}
      } as;
    };
    """
    |> String.trim()
  end

  defp data_ctors(book) do
    book
    |> data_defs()
    |> Enum.flat_map(fn d ->
      d.ctors
      |> Enum.with_index()
      |> Enum.map(fn {ctor, tag} -> ctor_fun(d, ctor, tag, book) end)
    end)
    |> Enum.join("\n\n")
  end

  defp ctor_fun(d, ctor, tag, book) do
    {pis, _} = telescope(ctor.type)

    fields =
      pis
      |> Enum.reject(fn {q, _, _} -> q == :erased end)
      |> Enum.with_index()
      |> Enum.map(fn {{_, a, x}, k} -> {ctype(a, book), x, k} end)

    {params, _} =
      Enum.map_reduce(fields, MapSet.new(), fn {ty, x, k}, used ->
        base = if x == "_", do: "f#{k}", else: c_name(x)
        {cname, used} = fresh(base, used)
        {{ty, cname, k}, used}
      end)

    ptr = struct_ptr(d.name)
    member = c_name(ctor.name)

    assigns =
      Enum.map_join(params, "\n", fn {_ty, cname, k} ->
        "  p->as.#{member}.f#{k} = #{cname};"
      end)

    args =
      case params do
        [] -> "void"
        ps -> Enum.map_join(ps, ", ", fn {ty, n, _} -> "#{ty}#{n}" end)
      end

    body =
      if assigns == "" do
        """
        static #{ptr}#{c_name(ctor.name)}(#{args}) {
          #{ptr}p = malloc(sizeof *p);
          if (p == 0) abort();
          p->tag = #{tag};
          return p;
        }
        """
      else
        """
        static #{ptr}#{c_name(ctor.name)}(#{args}) {
          #{ptr}p = malloc(sizeof *p);
          if (p == 0) abort();
          p->tag = #{tag};
        #{assigns}
          return p;
        }
        """
      end

    String.trim(body)
  end

  defp data_defs(book) do
    Enum.filter(book, &(Map.get(&1, :kind) == :data))
  end
end

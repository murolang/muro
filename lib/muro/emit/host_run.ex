defmodule Muro.Emit.HostRun do
  @moduledoc false

  # Clauses of `muro_eval_run/3` for the runs a skeleton still names.
  # Each clause returns `{:ok, host}` or `:error`. `:error` is the
  # sentinel `Session.eval_run/3` wraps as `{:run, name, args}`.
  # A call of this definition, or of one declared later, is `:error`
  # for the whole clause when `calls_out?` sees it, and `:error` for
  # the arm when only that arm is taken.

  alias Muro.Emit

  @doc false
  def clauses(%{runs: runs, decls: decls}) when is_list(runs) and is_list(decls) do
    runs = Enum.filter(runs, &(Map.get(&1, :mode) == :run))

    {texts, oks} =
      Enum.map_reduce(runs, %{}, fn defn, oks ->
        {text, ok} = one_clause(defn, runs, decls, oks)
        {text, Map.put(oks, defn.name, ok)}
      end)

    %{text: Enum.join(texts, "\n\n"), ok: Enum.any?(oks, fn {_name, ok} -> ok end)}
  end

  def clauses(_), do: %{text: "", ok: false}

  defp one_clause(defn, runs, decls, oks) do
    i = Enum.find_index(runs, &(&1.name == defn.name))
    prefix = runs |> Enum.take(i) |> MapSet.new(& &1.name)
    defs = MapSet.new(runs, & &1.name)
    doms = pi_chain(defn.type, [])
    n = length(doms)
    args = if n == 0, do: [], else: Enum.map(0..(n - 1), &"a#{&1}")
    head = "defp muro_eval_run(#{inspect(defn.name)}, [#{Enum.join(args, ", ")}], :raw)"

    {body, ok} =
      cond do
        Enum.any?(doms, &(result_ty(&1, decls) == :error)) ->
          {":error", false}

        drop_lams(defn.body, n) == :error ->
          {":error", false}

        true ->
          {:ok, core} = drop_lams(defn.body, n)

          if calls_out?(core, prefix, defs) do
            {":error", false}
          else
            ctx = %{
              prefix: prefix,
              defs: defs,
              decls: decls,
              ctors: ctor_set(decls),
              oks: oks,
              n: 0
            }

            env = initial_env(args, doms, decls)

            case compile(core, env, ctx) do
              {:miss, _} ->
                {":error", false}

              {compiled, _} ->
                rendered = render_compiled(compiled)

                {wrap_payload(payload_checks(args, doms, decls), rendered), returns_ok?(compiled)}
            end
          end
      end

    text =
      if String.contains?(body, "\n") do
        "#{head} do\n#{indent(body, 2)}\nend"
      else
        "#{head}, do: #{body}"
      end

    {text, ok}
  end

  defp initial_env(args, doms, decls) do
    args
    |> Enum.zip(doms)
    |> Enum.map(fn {arg, dom} ->
      case result_ty(dom, decls) do
        {:ok, :nat} -> {:nat, arg}
        _ -> {:code, arg}
      end
    end)
    |> Enum.reverse()
  end

  defp payload_checks(args, doms, decls) do
    Enum.zip(args, doms)
    |> Enum.map(fn {arg, dom} ->
      {:ok, ty} = result_ty(dom, decls)
      "payload?(#{inspect(ty, limit: :infinity, charlists: :as_lists)}, #{arg})"
    end)
  end

  defp wrap_payload([], body), do: body

  defp wrap_payload(checks, body) do
    """
    if #{Enum.join(checks, " and ")} do
    #{indent(body, 2)}
    else
      :error
    end
    """
    |> String.trim()
  end

  defp compile(:ze, _env, ctx), do: {{:pure, {:lit, 0}}, ctx}
  defp compile({:nat, n}, _env, ctx) when is_integer(n) and n >= 0, do: {{:pure, {:lit, n}}, ctx}
  defp compile(:one, _env, ctx), do: {{:pure, {:atom, :tt}}, ctx}
  defp compile({:ann, t, _}, env, ctx), do: compile(t, env, ctx)

  defp compile({:var, i}, env, ctx) when is_integer(i) do
    case Enum.at(env, i) do
      nil -> {:miss, ctx}
      host -> {{:pure, host}, ctx}
    end
  end

  defp compile({:su, t}, env, ctx) do
    case compile(t, env, ctx) do
      {:miss, ctx} -> {:miss, ctx}
      {{:pure, {:lit, n}}, ctx} -> {{:pure, {:lit, n + 1}}, ctx}
      {{:pure, {:nat, src}}, ctx} -> {{:pure, {:nat, nat_add(src)}}, ctx}
      {{:pure, {:code, src}}, ctx} -> suc_code(src, ctx)
      {{:pure, _}, ctx} -> {:miss, ctx}
      {{:check, src, ok}, ctx} -> suc_check(src, ok, ctx)
    end
  end

  defp compile({:pair, a, b}, env, ctx) do
    {ca, ctx} = compile(a, env, ctx)
    {cb, ctx} = compile(b, env, ctx)
    seq([ca, cb], fn [ha, hb], ctx -> {{:pure, {:tup, [ha, hb]}}, ctx} end, ctx)
  end

  defp compile({:mnat, e, _motive, z, s}, env, ctx), do: compile_nat(e, z, s, env, ctx)

  defp compile({:mnat, e, _x, _motive, z, _y, s}, env, ctx), do: compile_nat(e, z, s, env, ctx)

  defp compile({:mdata, e, _motive, branches}, env, ctx) when is_list(branches) do
    compile_data(e, branches, env, ctx)
  end

  defp compile({:mdata, e, _x, _motive, branches}, env, ctx) when is_list(branches) do
    compile_data(e, branches, env, ctx)
  end

  defp compile({:mwbool, e, _motive, branches}, env, ctx) when is_list(branches) do
    compile_word(e, branches, env, ctx, :bool)
  end

  defp compile({:mwbool, e, _x, _motive, branches}, env, ctx) when is_list(branches) do
    compile_word(e, branches, env, ctx, :bool)
  end

  defp compile({:mopt, e, _motive, branches}, env, ctx) when is_list(branches) do
    compile_word(e, branches, env, ctx, :opt)
  end

  defp compile({:mopt, e, _x, _motive, branches}, env, ctx) when is_list(branches) do
    compile_word(e, branches, env, ctx, :opt)
  end

  defp compile({:app, _, _} = term, env, ctx) do
    case spine(term, []) do
      {:ok, name, args} -> compile_call(name, args, env, ctx)
      :error -> {:miss, ctx}
    end
  end

  defp compile({:def, name}, env, ctx), do: compile_call(name, [], env, ctx)
  defp compile(_, _env, ctx), do: {:miss, ctx}

  defp compile_nat(e, z, s, env, ctx) do
    case compile(e, env, ctx) do
      {:miss, ctx} ->
        {:miss, ctx}

      {{:pure, {:lit, 0}}, ctx} ->
        compile(z, env, ctx)

      {{:pure, {:lit, n}}, ctx} when n > 0 ->
        compile(s, [{:lit, n - 1} | env], ctx)

      {{:pure, {:nat, src}}, ctx} ->
        nat_case(src, z, s, env, ctx)

      {{:pure, {:code, src}}, ctx} ->
        nat_case(src, z, s, env, ctx)

      {{:pure, _}, ctx} ->
        {:miss, ctx}

      {{:check, src, true}, ctx} ->
        {var, ctx} = fresh(ctx, "muro_v")
        {inner, ctx} = nat_case(var, z, s, env, ctx)
        wrap_check(src, var, inner, ctx)

      {{:check, _src, false}, ctx} ->
        {:miss, ctx}
    end
  end

  defp nat_case(src, z, s, env, ctx) do
    {zr, ctx} = compile(z, env, ctx)
    {var, ctx} = fresh(ctx, "muro_n")
    {sr, ctx} = compile(s, [{:nat, "#{var} - 1"} | env], ctx)

    text = """
    case #{scrut(src)} do
      0 ->
    #{indent(render_compiled(zr), 4)}
      #{var} when is_integer(#{var}) and #{var} > 0 ->
    #{indent(render_compiled(sr), 4)}
      _ ->
        :error
    end
    """

    {{:check, text, returns_ok?(zr) or returns_ok?(sr)}, ctx}
  end

  defp compile_data(e, branches, env, ctx) do
    case compile(e, env, ctx) do
      {:miss, ctx} ->
        {:miss, ctx}

      {{:pure, {:con, name, fields}}, ctx} ->
        fold_con(name, fields, branches, env, ctx)

      {{:pure, {:atom, atom}}, ctx} ->
        fold_atom(atom, branches, env, ctx)

      {{:pure, {:code, src}}, ctx} ->
        open_data(src, branches, env, ctx)

      {{:pure, _}, ctx} ->
        {:miss, ctx}

      {{:check, src, true}, ctx} ->
        {var, ctx} = fresh(ctx, "muro_v")
        {inner, ctx} = open_data(var, branches, env, ctx)
        wrap_check(src, var, inner, ctx)

      {{:check, _src, false}, ctx} ->
        {:miss, ctx}
    end
  end

  defp fold_con(name, fields, branches, env, ctx) do
    case find_branch(branches, name, length(fields)) do
      nil -> {:miss, ctx}
      body -> compile(body, Enum.reverse(fields) ++ env, ctx)
    end
  end

  defp fold_atom(atom, branches, env, ctx) do
    label = Atom.to_string(atom)

    picked =
      Enum.find_value(shaped(branches), fn {name, arity, body} ->
        if arity == 0 and Emit.elixir_atom_name(name) == label, do: body
      end) ||
        Enum.find_value(shaped(branches), fn {name, arity, body} ->
          if arity == 0 and name == label, do: body
        end)

    case picked do
      nil -> {:miss, ctx}
      body -> compile(body, env, ctx)
    end
  end

  defp open_data(src, branches, env, ctx) do
    arms = shaped(branches)
    names = Enum.map(arms, fn {name, _, _} -> name end)

    {pairs, ctx} =
      arms
      |> Enum.group_by(fn {_, arity, _} -> arity end)
      |> Enum.sort_by(fn {arity, _} -> arity end)
      |> Enum.map_reduce(ctx, fn {arity, group}, ctx ->
        {clause, ok, ctx} = arity_clause(arity, group, names, env, ctx)
        {{clause, ok}, ctx}
      end)

    clauses = Enum.map(pairs, &elem(&1, 0))
    ok = Enum.any?(pairs, &elem(&1, 1))

    text =
      if clauses == [] do
        ":error"
      else
        """
        case #{scrut(src)} do
        #{indent(Enum.join(clauses, "\n"), 2)}
          _ ->
            :error
        end
        """
      end

    {{:check, String.trim(text), ok}, ctx}
  end

  defp arity_clause(0, group, names, env, ctx) do
    {inners, ctx} =
      Enum.map_reduce(group, ctx, fn {name, 0, body}, ctx ->
        {compiled, ctx} = compile(body, env, ctx)

        {{arrow("{:ok, #{inspect(name)}}", render_compiled(compiled)), returns_ok?(compiled)},
         ctx}
      end)

    clause = """
    tag when is_atom(tag) ->
      case muro_source_ctor(#{inspect(names)}, Atom.to_string(tag)) do
    #{indent(Enum.map_join(inners, "\n", &elem(&1, 0)), 4)}
        _ ->
          :error
      end
    """

    {String.trim(clause), Enum.any?(inners, &elem(&1, 1)), ctx}
  end

  defp arity_clause(arity, group, names, env, ctx) do
    {vars, ctx} = fresh_fields(arity, ctx)
    field_env = Enum.reverse(Enum.map(vars, &{:code, &1})) ++ env

    {inners, ctx} =
      Enum.map_reduce(group, ctx, fn {name, ^arity, body}, ctx ->
        {compiled, ctx} = compile(body, field_env, ctx)

        {{arrow("{:ok, #{inspect(name)}}", render_compiled(compiled)), returns_ok?(compiled)},
         ctx}
      end)

    texts = Enum.map(inners, &elem(&1, 0))
    used = Enum.join(texts, "\n")

    pats =
      Enum.map_join(vars, ", ", fn var ->
        if referenced?(used, var), do: var, else: "_"
      end)

    clause = """
    {tag, #{pats}} when is_atom(tag) ->
      case muro_source_ctor(#{inspect(names)}, Atom.to_string(tag)) do
    #{indent(Enum.join(texts, "\n"), 4)}
        _ ->
          :error
      end
    """

    {String.trim(clause), Enum.any?(inners, &elem(&1, 1)), ctx}
  end

  defp compile_word(e, branches, env, ctx, kind) do
    case compile(e, env, ctx) do
      {:miss, ctx} ->
        {:miss, ctx}

      {{:pure, {:atom, true}}, ctx} when kind == :bool ->
        take_arm(branches, "wtrue", [], env, ctx)

      {{:pure, {:atom, false}}, ctx} when kind == :bool ->
        take_arm(branches, "wfalse", [], env, ctx)

      {{:pure, {:atom, :none}}, ctx} when kind == :opt ->
        take_arm(branches, "wnone", [], env, ctx)

      {{:pure, {:code, src}}, ctx} ->
        word_case(src, branches, env, ctx, kind)

      {{:pure, _}, ctx} ->
        {:miss, ctx}

      {{:check, src, true}, ctx} ->
        {var, ctx} = fresh(ctx, "muro_v")
        {inner, ctx} = word_case(var, branches, env, ctx, kind)
        wrap_check(src, var, inner, ctx)

      {{:check, _src, false}, ctx} ->
        {:miss, ctx}
    end
  end

  defp word_case(src, branches, env, ctx, :bool) do
    {tb, tb_ok, ctx} = arm_text(branches, "wtrue", [], env, ctx)
    {fb, fb_ok, ctx} = arm_text(branches, "wfalse", [], env, ctx)

    text = """
    case #{scrut(src)} do
    #{indent(arrow("true", tb), 2)}
    #{indent(arrow("false", fb), 2)}
    #{indent(arrow("{:word, true, []}", tb), 2)}
    #{indent(arrow("{:word, false, []}", fb), 2)}
      _ ->
        :error
    end
    """

    {{:check, String.trim(text), tb_ok or fb_ok}, ctx}
  end

  defp word_case(src, branches, env, ctx, :opt) do
    {var, ctx} = fresh(ctx, "muro_f")
    {none, none_ok, ctx} = arm_text(branches, "wnone", [], env, ctx)
    {some, some_ok, ctx} = arm_text(branches, "wsome", [{:code, var}], env, ctx)
    field = if referenced?(some, var), do: var, else: "_"

    text = """
    case #{scrut(src)} do
    #{indent(arrow(":none", none), 2)}
    #{indent(arrow("{:some, #{field}}", some), 2)}
    #{indent(arrow("{:word, :none, []}", none), 2)}
    #{indent(arrow("{:word, :some, [#{field}]}", some), 2)}
      _ ->
        :error
    end
    """

    {{:check, String.trim(text), none_ok or some_ok}, ctx}
  end

  defp take_arm(branches, name, fields, env, ctx) do
    case find_branch(branches, name, length(fields)) do
      nil -> {:miss, ctx}
      body -> compile(body, Enum.reverse(fields) ++ env, ctx)
    end
  end

  defp arm_text(branches, name, fields, env, ctx) do
    case take_arm(branches, name, fields, env, ctx) do
      {:miss, ctx} -> {":error", false, ctx}
      {compiled, ctx} -> {render_compiled(compiled), returns_ok?(compiled), ctx}
    end
  end

  defp compile_call(name, args, env, ctx) do
    {parts, ctx} = map_compile(args, env, ctx)
    seq(parts, fn hosts, ctx -> dispatch(to_name(name), hosts, ctx) end, ctx)
  end

  defp map_compile([], _env, ctx), do: {[], ctx}

  defp map_compile([t | ts], env, ctx) do
    {c, ctx} = compile(t, env, ctx)
    {cs, ctx} = map_compile(ts, env, ctx)
    {[c | cs], ctx}
  end

  defp dispatch(name, hosts, ctx) do
    cond do
      MapSet.member?(ctx.prefix, name) ->
        args = Enum.map_join(hosts, ", ", &render_nest/1)

        {{:check, "muro_eval_run(#{inspect(name)}, [#{args}], :raw)",
          Map.get(ctx.oks, name, false)}, ctx}

      MapSet.member?(ctx.defs, name) ->
        {:miss, ctx}

      MapSet.member?(ctx.ctors, name) ->
        {{:pure, {:con, name, hosts}}, ctx}

      true ->
        {:miss, ctx}
    end
  end

  defp seq([], fun, ctx), do: fun.([], ctx)
  defp seq([:miss | _], _fun, ctx), do: {:miss, ctx}

  defp seq([{:pure, h} | rest], fun, ctx) do
    seq(rest, fn hs, ctx -> fun.([h | hs], ctx) end, ctx)
  end

  defp seq([{:check, _src, false} | _], _fun, ctx), do: {:miss, ctx}

  defp seq([{:check, src, true} | rest], fun, ctx) do
    {var, ctx} = fresh(ctx, "muro_v")

    case seq(rest, fn hs, ctx -> fun.([{:code, var} | hs], ctx) end, ctx) do
      {:miss, ctx} -> {:miss, ctx}
      {inner, ctx} -> wrap_check(src, var, inner, ctx)
    end
  end

  defp wrap_check(_src, _var, :miss, ctx), do: {:miss, ctx}

  defp wrap_check(src, var, inner, ctx) do
    text = """
    case #{scrut(src)} do
      {:ok, #{var}} ->
    #{indent(render_compiled(inner), 4)}
      :error ->
        :error
    end
    """

    {{:check, String.trim(text), returns_ok?(inner)}, ctx}
  end

  defp suc_code(src, ctx) do
    text = """
    case #{scrut(src)} do
      n when is_integer(n) and n >= 0 -> {:ok, n + 1}
      _ -> :error
    end
    """

    {{:check, String.trim(text), true}, ctx}
  end

  defp suc_check(_src, false, ctx), do: {:miss, ctx}

  defp suc_check(src, true, ctx) do
    {var, ctx} = fresh(ctx, "muro_v")

    inner = """
    case #{var} do
      n when is_integer(n) and n >= 0 -> {:ok, n + 1}
      _ -> :error
    end
    """

    wrap_check(src, var, {:check, String.trim(inner), true}, ctx)
  end

  defp nat_add(src) do
    if simple?(src), do: "#{src} + 1", else: "(#{src}) + 1"
  end

  defp find_branch(branches, name, arity) do
    name = to_name(name)

    Enum.find_value(shaped(branches), fn {n, a, body} ->
      if n == name and a == arity, do: body
    end)
  end

  defp shaped(branches) do
    Enum.flat_map(branches, fn branch ->
      case branch_shape(branch) do
        {name, arity, body} -> [{to_name(name), arity, body}]
        :no -> []
      end
    end)
  end

  defp branch_shape({name, binders, body}) when is_list(binders) do
    {name, length(binders), body}
  end

  defp branch_shape({name, arity, body}) when is_integer(arity), do: {name, arity, body}
  defp branch_shape(_), do: :no

  defp ctor_set(decls) do
    Enum.reduce(decls, MapSet.new(), fn
      %{kind: :data, ctors: ctors} = d, acc ->
        if payload_decl?(d) do
          Enum.reduce(ctors, acc, fn %{name: name}, acc -> MapSet.put(acc, to_name(name)) end)
        else
          acc
        end

      _, acc ->
        acc
    end)
  end

  defp payload_decl?(d) do
    indices = Map.get(d, :indices, [])
    params = Map.get(d, :params, [])

    indices == [] and
      Enum.all?(params, fn
        {_q, _x, :typ} -> true
        _ -> false
      end)
  end

  defp fresh_fields(n, ctx) do
    Enum.map_reduce(1..n, ctx, fn _, ctx -> fresh(ctx, "muro_f") end)
  end

  defp fresh(ctx, prefix) do
    {"#{prefix}#{ctx.n}", %{ctx | n: ctx.n + 1}}
  end

  defp render_compiled(:miss), do: ":error"
  defp render_compiled({:pure, host}), do: "{:ok, #{render_nest(host)}}"
  defp render_compiled({:check, src, _ok}), do: src

  defp returns_ok?({:pure, _}), do: true
  defp returns_ok?(:miss), do: false
  defp returns_ok?({:check, _src, ok}), do: ok

  defp render_nest({:lit, n}), do: Integer.to_string(n)
  defp render_nest({:nat, src}), do: paren_code(src)
  defp render_nest({:atom, atom}), do: inspect(atom)
  defp render_nest({:code, src}), do: paren_code(src)

  defp render_nest({:con, name, []}) do
    inspect(String.to_atom(Emit.elixir_atom_name(name)))
  end

  defp render_nest({:con, name, fields}) do
    tag = inspect(String.to_atom(Emit.elixir_atom_name(name)))
    "{" <> Enum.map_join([tag | Enum.map(fields, &render_nest/1)], ", ") <> "}"
  end

  defp render_nest({:tup, hosts}) do
    "{" <> Enum.map_join(hosts, ", ", &render_nest/1) <> "}"
  end

  defp paren_code(src) do
    if simple?(src), do: src, else: "(#{src})"
  end

  defp scrut(src) do
    if simple?(src), do: src, else: "(#{src})"
  end

  defp simple?(src), do: String.match?(src, ~r/^[a-z_][A-Za-z0-9_]*$/)

  defp arrow(head, body) do
    body = String.trim(body)

    if String.contains?(body, "\n") do
      head <> " ->\n" <> indent(body, 2)
    else
      head <> " -> " <> body
    end
  end

  defp referenced?(src, name) do
    Regex.match?(~r/(?<![A-Za-z0-9_])#{Regex.escape(name)}(?![A-Za-z0-9_])/, src)
  end

  defp indent(code, n) do
    pad = String.duplicate(" ", n)

    code
    |> String.trim_trailing()
    |> String.split("\n")
    |> Enum.map_join("\n", fn
      "" -> ""
      line -> pad <> line
    end)
  end

  defp to_name(name) when is_atom(name), do: Atom.to_string(name)
  defp to_name(name) when is_binary(name), do: name

  defp drop_lams(body, 0), do: {:ok, body}
  defp drop_lams({:lam, _, _, _, body}, n) when n > 0, do: drop_lams(body, n - 1)
  defp drop_lams(_, _), do: :error

  defp pi_chain({:pi, _, domain, _, cod}, acc), do: pi_chain(cod, [domain | acc])
  defp pi_chain(_, acc), do: Enum.reverse(acc)

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
        case spine(term, []) do
          {:ok, name, args} ->
            out?(name, prefix, defs) or Enum.any?(args, &calls_out?(&1, prefix, defs))

          :error ->
            false
        end

      {:def, name} ->
        out?(to_name(name), prefix, defs)

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

  defp out?(name, prefix, defs) do
    name = to_name(name)
    MapSet.member?(defs, name) and not MapSet.member?(prefix, name)
  end

  defp spine({:app, f, a}, acc), do: spine(f, [a | acc])
  defp spine({:def, name}, acc), do: {:ok, name, acc}
  defp spine(_, _), do: :error

  defp result_ty(:nat, _), do: {:ok, :nat}
  defp result_ty(:unit, _), do: {:ok, :unit}

  defp result_ty({:def, "Bit"}, decls) do
    if find_decl(decls, "Bit"), do: {:ok, {:dat, "Bit", []}}, else: {:ok, :bit}
  end

  defp result_ty({:def, "Unit"}, decls) do
    if find_decl(decls, "Unit"), do: {:ok, {:dat, "Unit", []}}, else: {:ok, :unit}
  end

  defp result_ty({:def, name}, decls) when is_binary(name) do
    if find_decl(decls, name), do: {:ok, {:dat, name, []}}, else: :error
  end

  defp result_ty({:app, _, _} = term, decls) do
    case type_spine(term, []) do
      {:ok, name, args} ->
        if find_decl(decls, name) do
          case result_list(args, decls) do
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

  defp result_list(args, decls) do
    Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, acc} ->
      case result_ty(arg, decls) do
        {:ok, ty} -> {:cont, {:ok, acc ++ [ty]}}
        :error -> {:halt, :error}
      end
    end)
  end

  defp type_spine({:app, f, a}, acc), do: type_spine(f, [a | acc])
  defp type_spine({:def, name}, acc) when is_binary(name), do: {:ok, name, acc}
  defp type_spine(_, _), do: :error

  defp find_decl(decls, name) do
    Enum.find(decls, &(Map.get(&1, :kind) == :data and &1.name == name))
  end
end

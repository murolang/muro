defmodule Muro.Emit.Zig do
  @moduledoc """
  Emit a closed run book to Zig 0.15. Specs and evidence are omitted.
  Run bodies are the image from `Muro.IR`.

  The text is what `zig` translates. A refusal is the elaboration's:
  `c:lambda`, `c:machine`, `c:stream`, `c:string`, `c:erased`,
  `c:unsupported`.

  Every run takes an allocator first and returns an error union. A caller
  can pass a `muro__std.heap.ArenaAllocator` and reset it. `Nat` and user
  data are tagged unions. A fieldless constructor is one static value. A
  stream is a seed, an environment, and a step.

  Identifiers come from `Muro.Emit.Name`. A source name is spelled there.
  A helper, a step, a constructor argument, and a temporary are generated
  there. The two spellings share no identifier. A binder is claimed there
  against every name visible in its scope, including type names.
  """

  alias Muro.{Ast, Emit, IR}
  alias Muro.Emit.Name

  # Zig 0.15 keywords (`std.zig.tokenizer`). `true` and `false` are
  # primitives, not keywords. A keyword as a name is a parse error.
  @keywords ~w(
    addrspace align allowzero and anyframe anytype asm break callconv catch
    comptime const continue defer else enum errdefer error export extern fn
    for if inline noalias noinline nosuspend opaque or orelse packed pub
    resume return linksection struct suspend switch test threadlocal try
    union unreachable var volatile while
  )
            |> MapSet.new()

  # `std.zig.primitives`, plus `u8` / `i32` via the pattern below.
  # A function with one of these names shadows the primitive.
  @primitives ~w(
    anyerror anyframe anyopaque bool c_int c_long c_longdouble c_longlong
    c_char c_short c_uint c_ulong c_ulonglong c_ushort comptime_float
    comptime_int f16 f32 f64 f80 f128 false isize noreturn null true type
    undefined usize void
  )
              |> MapSet.new()

  @forbidden MapSet.union(@keywords, @primitives)

  @doc false
  def source_id(name) when is_binary(name), do: spell(name)

  @doc false
  def generated_samples do
    tags = ~w(
      std Nat Unit Pair Stream Atom Step
      zero suc tt from_u64 to_u64 erase reveal pair stream_new no_env
      allocator env seed
      field_fst field_snd field_step field_seed field_env
      tag_zero tag_suc tag_tt
      n p k i cur T e s t blk
    )

    Enum.map(tags, &Name.gen/1) ++
      [
        Name.gen("step", 0),
        Name.gen("env", 0),
        Name.gen("a", 0),
        Name.gen("f", 0),
        Name.gen("s", 0),
        Name.gen("blk", 0),
        Name.gen("val_Nat_zero"),
        Name.gen("val_Unit_tt")
      ]
  end

  defp spell(name), do: Name.spell(name, @forbidden, &zig_width?/1)

  defp zig_width?(encoded), do: String.match?(encoded, ~r/^[iu][0-9]+$/)

  defp g(tag), do: Name.gen(tag)
  defp g(tag, n), do: Name.gen(tag, n)

  defp al, do: g("allocator")
  defp stdn, do: g("std")
  defp alloc_ty, do: "#{stdn()}.mem.Allocator"

  defp claim(base, used), do: Name.claim(base, used)

  @doc """
  Render `book` as one Zig source file for a stem such as `half_ok`.
  """
  def render(book, stem) when is_list(book) and is_binary(stem) do
    case IR.elaborate(book) do
      {:ok, funs} -> compile(book, funs, stem)
      {:error, reason} -> {:error, reason}
    end
  end

  @doc """
  Names, signatures, layouts, and clause heads of the Zig file
  `render/2` writes. A run's head is the one `run_open/2` places in
  front of its body. A generated step's head is `step_head/2`. No
  source is written.
  """
  def outline(book, _stem) when is_list(book) do
    case IR.elaborate(book) do
      {:ok, funs} ->
        with {:ok, st, groups, _scan, _flags, steps, _step_info} <- image(book, funs) do
          user = Enum.map(groups, fn {fun, _} -> fun end)
          step_funs = Enum.flat_map(groups, fn {_fun, ss} -> ss end)

          signatures =
            Enum.map(user, fn fun ->
              {head, _env, st1, params} = run_open(fun, st)

              %{
                source: fun.name,
                name: Map.fetch!(st.names, fun.name),
                layout: fun.ret,
                param_layouts: Enum.map(fun.params, fn {_n, lay} -> lay end),
                params: Enum.map(params, fn {_src, rn, _lay} -> rn end),
                ret: "!" <> pty(fun.ret, st1),
                export: fun.export,
                head: head
              }
            end)

          step_clauses =
            step_funs
            |> Enum.reject(&(Map.get(&1, :fold) == true))
            |> Enum.map(&step_head(&1, st))

          _ = steps

          {:ok,
           %{
             names:
               signatures |> Enum.flat_map(fn sig -> [sig.name | sig.params] end) |> Enum.uniq(),
             elixir: Emit.elixir_names(book),
             signatures: Enum.map(signatures, &Map.delete(&1, :head)),
             layouts:
               Enum.map(
                 signatures,
                 &%{name: &1.source, layout: &1.layout, params: &1.param_layouts}
               ) ++ data_layouts(book),
             clauses: Enum.map(signatures, & &1.head) ++ step_clauses
           }}
        end

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp compile(book, funs, _stem) do
    with {:ok, st, _groups, scan, flags, steps, step_info} <- image(book, funs),
         {:ok, fns} <- emit_funs(funs, st) do
      atoms = st.atoms
      atom_vals = st.atom_vals

      parts = [
        "// generated by muro — do not edit",
        "const #{stdn()} = @import(\"std\");",
        runtime(flags),
        atom_enum(atoms),
        atom_values(scan.atoms, atoms, atom_vals),
        data_items(book, st, scan.ctors),
        env_structs(steps, st),
        if(needs_no_env?(step_info), do: "const #{g("no_env")}: u8 = 0;", else: ""),
        Enum.join(fns, "\n\n")
      ]

      {:ok, join(parts)}
    end
  end

  defp image(book, funs) do
    with {:ok, groups, step_map} <- Emit.partition_funs(funs, Emit.run_defs(book)) do
      user_funs = Enum.map(groups, fn {fun, _} -> fun end)
      steps = Enum.flat_map(groups, fn {_fun, ss} -> ss end)
      scan = scan_funs(funs)
      flags = runtime_flags(scan, funs, book)
      spell = &spell/1
      {types, taken} = type_names(book, MapSet.new(), spell)
      {ctor_fns, taken} = ctor_fn_names(book, taken, spell)
      variants = variant_names(book)
      atoms = atom_variants(book)
      {atom_vals, taken} = atom_statics(scan.atoms, atoms, taken)
      {val_names, taken} = fieldless_statics(scan.ctors, book, types, variants, taken)
      stream_steps = Enum.reject(steps, &(Map.get(&1, :fold) == true))
      {step_info, taken} = step_infos(stream_steps, scan.steps, taken)
      {names, taken} = names_of(book, taken, spell)
      {step_names, globals} = name_steps(steps, taken, spell)

      st = %{
        book: book,
        names: names,
        step_names: step_names,
        funs: Map.new(user_funs, &{&1.name, &1}),
        steps: step_map,
        step_ids: MapSet.new(steps),
        types: types,
        ctor_fns: ctor_fns,
        variants: variants,
        atoms: atoms,
        atom_vals: atom_vals,
        val_names: val_names,
        step_info: step_info,
        globals: globals
      }

      {:ok, st, groups, scan, flags, steps, step_info}
    end
  end

  defp emit_funs(funs, st) do
    Enum.reduce_while(funs, {:ok, []}, fn fun, {:ok, acc} ->
      case emit_fun(fun, st) do
        {:ok, text} -> {:cont, {:ok, acc ++ [text]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp emit_fun(fun, st) do
    cond do
      Map.get(fun, :fold) == true -> emit_fold_fun(fun, st)
      MapSet.member?(st.step_ids, fun) -> emit_step(fun, st)
      true -> emit_run(fun, st)
    end
  end

  defp emit_fold_fun(fun, st0) do
    {head, env, st, params} = fold_open(fun, st0)

    with {:ok, {lines, ex, lay, eff, _st}} <- emit_tm(fun.body, env, st) do
      discards =
        []
        |> alloc_discard(fun.body, st, lines, ex)
        |> param_discards(params, fun.body)

      body = fn_body(discards ++ lines, coerce(force(ex, eff), lay, fun.ret, st))
      {:ok, "#{head} {\n#{body}\n}"}
    end
  end

  defp fold_open(fun, st0) do
    scope0 = st0.globals |> Name.open() |> Name.see(al())

    {params, scope} =
      Enum.reduce(fun.params, {[], scope0}, fn {pname, lay}, {acc, scope} ->
        {rn, scope} = Name.bind(spell(pname), scope)
        {acc ++ [{pname, rn, lay}], scope}
      end)

    env = Enum.reduce(params, [], fn {src, rn, lay}, env -> [{src, rn, lay} | env] end)
    st = Map.merge(st0, %{n: 0, blk: 0, scope: scope})

    args =
      ["#{al()}: #{alloc_ty()}"] ++
        Enum.map(params, fn {_src, rn, lay} -> "#{rn}: #{pty(lay, st)}" end)

    ret = "!" <> pty(fun.ret, st)
    name = Map.fetch!(st.step_names, fun.name)
    {"fn #{name}(#{Enum.join(args, ", ")}) #{ret}", env, st, params}
  end

  defp emit_run(fun, st0) do
    {head, env, st, params} = run_open(fun, st0)

    with {:ok, {lines, ex, lay, eff, _st}} <- emit_tm(fun.body, env, st) do
      discards =
        []
        |> alloc_discard(fun.body, st, lines, ex)
        |> param_discards(params, fun.body)

      body = fn_body(discards ++ lines, coerce(force(ex, eff), lay, fun.ret, st))
      {:ok, "#{head} {\n#{body}\n}"}
    end
  end

  defp run_open(fun, st0) do
    scope0 = st0.globals |> Name.open() |> Name.see(al())

    {params, scope} =
      Enum.reduce(fun.params, {[], scope0}, fn {pname, lay}, {acc, scope} ->
        {rn, scope} = Name.bind(spell(pname), scope)
        {acc ++ [{pname, rn, lay}], scope}
      end)

    env = Enum.reduce(params, [], fn {src, rn, lay}, env -> [{src, rn, lay} | env] end)
    st = Map.merge(st0, %{n: 0, blk: 0, scope: scope})

    args =
      ["#{al()}: #{alloc_ty()}"] ++
        Enum.map(params, fn {_src, rn, lay} -> "#{rn}: #{pty(lay, st)}" end)

    vis = if fun.export, do: "pub ", else: ""
    ret = "!" <> pty(fun.ret, st)
    name = Map.fetch!(st.names, fun.name)
    {"#{vis}fn #{name}(#{Enum.join(args, ", ")}) #{ret}", env, st, params}
  end

  defp step_head(fun, st) do
    name = Map.fetch!(st.step_names, fun.name)

    "fn #{name}(#{al()}: #{alloc_ty()}, #{g("env")}: *const anyopaque, #{g("seed")}: *const anyopaque) anyerror!*const #{g("Pair")}"
  end

  defp emit_step(fun, st0) do
    info = Map.fetch!(st0.step_info, fun.name)
    caps = Enum.take(fun.params, info.cap_count)
    seed_params = Enum.drop(fun.params, info.cap_count)

    if length(seed_params) > 1 do
      {:error, "c:unsupported"}
    else
      scope0 =
        st0.globals
        |> Name.open()
        |> Name.see(al())
        |> Name.see(g("env"))
        |> Name.see(g("seed"))

      st = Map.merge(st0, %{n: 0, blk: 0, scope: scope0})
      {pro, env, st} = step_prologue(fun.body, caps, seed_params, info, st)

      with {:ok, {lines, ex, lay, eff, st}} <- emit_tm(fun.body, env, st) do
        target = pair_target(lay)
        expr = coerce(force(ex, eff), lay, target, st)
        discards = alloc_discard([], fun.body, st, lines, ex)
        body = fn_body(discards ++ pro ++ lines, expr)
        {:ok, "#{step_head(fun, st)} {\n#{body}\n}"}
      end
    end
  end

  defp step_prologue(body, caps, seed_params, info, st) do
    {cap_lines, cap_env, st} = bind_caps(body, caps, seed_params, info, st)
    {seed_lines, seed_env, st} = bind_seed(body, seed_params, st)
    {cap_lines ++ seed_lines, seed_env ++ cap_env, st}
  end

  defp bind_caps(_body, [], _later, _info, st), do: {["_ = #{g("env")};"], [], st}

  defp bind_caps(body, caps, later, info, st) do
    used? =
      Enum.with_index(caps, fn {name, _lay}, i ->
        binder_used?(body, name, Enum.drop(caps, i + 1) ++ later)
      end)

    if Enum.any?(used?) do
      {e, st} = local(st, g("e"))
      reveal = "const #{e} = #{g("reveal")}(#{info.env}, #{g("env")});"

      {consts, env, st} =
        [caps, used?]
        |> Enum.zip()
        |> Enum.with_index()
        |> Enum.reduce({[], [], st}, fn
          {{{name, lay}, true}, i}, {consts, env, st} ->
            {rn, st} = local(st, spell(name))
            {consts ++ ["const #{rn} = #{e}.#{g("f", i)};"], [{name, rn, lay} | env], st}

          {{{_name, _lay}, false}, _i}, acc ->
            acc
        end)

      {[reveal | consts], env, st}
    else
      {["_ = #{g("env")};"], [], st}
    end
  end

  defp bind_seed(_body, [], st), do: {["_ = #{g("seed")};"], [], st}

  defp bind_seed(body, [{name, lay} | rest], st) do
    if binder_used?(body, name, rest) do
      {rn, st} = local(st, spell(name))

      line =
        if lay == :opaque do
          "const #{rn} = #{g("seed")};"
        else
          "const #{rn} = #{g("reveal")}(#{zty(lay, st)}, #{g("seed")});"
        end

      {[line], [{name, rn, lay}], st}
    else
      {["_ = #{g("seed")};"], [], st}
    end
  end

  defp emit_tm({:var, name}, env, st) do
    case lookup(env, name) do
      {rn, lay} -> {:ok, {[], rn, lay, :pure, st}}
      nil -> {:error, "c:unsupported"}
    end
  end

  defp emit_tm(:ze, _env, st), do: {:ok, {[], "#{g("zero")}()", :nat, :pure, st}}
  defp emit_tm(:tt, _env, st), do: {:ok, {[], "#{g("tt")}()", :unit, :pure, st}}
  defp emit_tm(:abort, _env, st), do: {:ok, {[], "#{stdn()}.posix.abort()", :never, :pure, st}}

  defp emit_tm({:su, u}, env, st) do
    with {:ok, {lines, ex, lay, eff, st}} <- emit_tm(u, env, st) do
      {lines, ex, eff, st} = materialize(lines, ex, eff, st)
      arg = coerce(force(ex, eff), lay, :nat, st)
      {:ok, {lines, "#{g("suc")}(#{al()}, #{arg})", :nat, :fail, st}}
    end
  end

  defp emit_tm({:call, name, args}, env, st) do
    case Map.fetch(st.funs, name) do
      :error ->
        {:error, "c:unsupported"}

      {:ok, fun} ->
        with {:ok, {lines, exprs, lays, effs, st}} <- emit_list(args, env, st) do
          params = Enum.map(fun.params, fn {_n, lay} -> lay end)

          if length(params) != length(exprs) do
            {:error, "c:unsupported"}
          else
            coerced =
              [exprs, lays, effs, params]
              |> Enum.zip()
              |> Enum.map(fn {ex, from, eff, to} -> coerce(force(ex, eff), from, to, st) end)

            call = "#{Map.fetch!(st.names, name)}(#{Enum.join([al() | coerced], ", ")})"
            {:ok, {lines, call, fun.ret, :fail, st}}
          end
        end
    end
  end

  defp emit_tm({:con, "Atom", name, []}, _env, st) do
    case Map.fetch(st.atom_vals, name) do
      {:ok, val} -> {:ok, {[], "&#{val}", {:data, "Atom"}, :pure, st}}
      :error -> {:error, "c:unsupported"}
    end
  end

  defp emit_tm({:con, dname, cname, args}, env, st) do
    with {:ok, {lines, exprs, lays, effs, st}} <- emit_list(args, env, st) do
      fn_name = Map.get(st.ctor_fns, {dname, cname})

      case ctor_fields(st.book, dname, cname) do
        :error ->
          {:error, "c:unsupported"}

        {:ok, fields} ->
          cond do
            fn_name == nil or length(fields) != length(exprs) ->
              {:error, "c:unsupported"}

            fields == [] ->
              {:ok, {lines, "#{fn_name}()", {:data, dname}, :pure, st}}

            true ->
              coerced =
                [exprs, lays, effs, fields]
                |> Enum.zip()
                |> Enum.map(fn {ex, from, eff, to} -> coerce(force(ex, eff), from, to, st) end)

              call = "#{fn_name}(#{Enum.join([al() | coerced], ", ")})"
              {:ok, {lines, call, {:data, dname}, :fail, st}}
          end
      end
    end
  end

  # An erased constructor field, marked `:erased`. The placeholder is
  # unit, and the payload is ignored. A zero passed under a spec alias
  # is bound at the argument's layout, so this clause does not see it.
  defp emit_tm({:let, name, :erased, _val, body}, env, st) do
    if uses?(body, name) do
      {rn, st} = local(st, spell(name))

      with {:ok, {lines, ex, lay, eff, st}} <- emit_tm(body, [{name, rn, :opaque} | env], st) do
        {:ok, {["const #{rn} = #{g("erase")}(#{g("tt")}());" | lines], ex, lay, eff, st}}
      end
    else
      emit_tm(body, env, st)
    end
  end

  defp emit_tm({:let, _name, _lay, val, :abort}, env, st) do
    with {:ok, {lines, ex, _lay, eff, st}} <- emit_tm(val, env, st) do
      {lines, ex, eff, st} = materialize(lines, ex, eff, st)
      {rn, st} = local(st, g("s"))
      more = ["const #{rn} = #{force(ex, eff)};", "_ = #{rn};"]
      {:ok, {lines ++ more, "#{stdn()}.posix.abort()", :never, :pure, st}}
    end
  end

  defp emit_tm({:let, name, lay, val, body}, env, st) do
    with {:ok, {vlines, vex, vlay, veff, st}} <- emit_tm(val, env, st) do
      {vlines, vex, veff, st} = materialize(vlines, vex, veff, st)
      {rn, st} = local(st, spell(name))
      bound = coerce(force(vex, veff), vlay, lay, st)
      discard = if uses?(body, name), do: [], else: ["_ = #{rn};"]

      with {:ok, {blines, bex, blay, beff, st}} <- emit_tm(body, [{name, rn, lay} | env], st) do
        {:ok, {vlines ++ ["const #{rn} = #{bound};"] ++ discard ++ blines, bex, blay, beff, st}}
      end
    end
  end

  defp emit_tm({:pair, a, b}, env, st) do
    with {:ok, {al, ae, alay, aeff, st}} <- emit_tm(a, env, st),
         {:ok, {bl, be, blay, beff, st}} <- emit_tm(b, env, st) do
      {al, ae, aeff, st} = materialize(al, ae, aeff, st)
      {bl, be, beff, st} = materialize(bl, be, beff, st)

      expr =
        "#{g("pair")}(#{al()}, #{coerce(force(ae, aeff), alay, :opaque, st)}, #{coerce(force(be, beff), blay, :opaque, st)})"

      {:ok, {al ++ bl, expr, {:pair, alay, blay}, :fail, st}}
    end
  end

  defp emit_tm({:letp, a, b, e, body}, env, st) do
    with {:ok, {elines, eex, elay, eeff, st}} <- emit_tm(e, env, st) do
      {elines, eex, eeff, st} = materialize(elines, eex, eeff, st)
      {s, st} = local(st, g("p"))
      {ra, st} = local(st, spell(a))
      {rb, st} = local(st, spell(b))
      {la, lb} = pair_halves(elay)
      env1 = [{b, rb, lb}, {a, ra, la} | env]

      with {:ok, {blines, bex, blay, beff, st}} <- emit_tm(body, env1, st) do
        shown = coerce(force(eex, eeff), elay, pair_view(elay), st)

        binds =
          ["const #{s} = #{shown};"] ++
            maybe_bind(a, ra, "#{s}.#{g("field_fst")}", la, body, [b], st) ++
            maybe_bind(b, rb, "#{s}.#{g("field_snd")}", lb, body, [], st)

        {:ok, {elines ++ binds ++ blines, bex, blay, beff, st}}
      end
    end
  end

  defp emit_tm({:uncons, e}, env, st) do
    with {:ok, {lines, ex, elay, eff, st}} <- emit_tm(e, env, st) do
      {lines, ex, eff, st} = materialize(lines, ex, eff, st)
      {s, st} = local(st, g("s"))
      {p, st} = local(st, g("p"))
      {t, st} = local(st, g("t"))

      shown = coerce(force(ex, eff), elay, stream_view(elay), st)

      more = [
        "const #{s} = #{shown};",
        "const #{p} = try #{s}.#{g("field_step")}(#{al()}, #{s}.#{g("field_env")}, #{s}.#{g("field_seed")});",
        "const #{t} = try #{g("stream_new")}(#{al()}, #{p}.#{g("field_snd")}, #{s}.#{g("field_env")}, #{s}.#{g("field_step")});"
      ]

      expr = "#{g("pair")}(#{al()}, #{p}.#{g("field_fst")}, #{g("erase")}(#{t}))"
      {:ok, {lines ++ more, expr, uncons_lay(elay), :fail, st}}
    end
  end

  defp emit_tm({:stream, seed, caps, step_name}, env, st) do
    case Map.fetch(st.steps, step_name) do
      :error ->
        {:error, "c:unsupported"}

      {:ok, step} ->
        info = Map.get(st.step_info, step_name)

        with true <- is_map(info) and length(caps) == info.cap_count,
             {:ok, {slines, sex, slay, seff, st}} <- emit_tm(seed, env, st),
             {:ok, {clines, cexs, clays, ceffs, st}} <- emit_caps(caps, env, st) do
          {slines, sex, seff, st} = materialize(slines, sex, seff, st)
          cap_lays = step.params |> Enum.take(length(caps)) |> Enum.map(&elem(&1, 1))
          seed_lays = step.params |> Enum.drop(length(caps)) |> Enum.map(&elem(&1, 1))

          if length(cap_lays) != length(cexs) do
            {:error, "c:unsupported"}
          else
            {elines, env_ex, st} =
              env_expr(cexs, clays, ceffs, cap_lays, info, st)

            seed_ex = coerce(force(sex, seff), slay, :opaque, st)
            fname = Map.fetch!(st.step_names, step_name)
            expr = "#{g("stream_new")}(#{al()}, #{seed_ex}, #{env_ex}, #{fname})"

            lay =
              case seed_lays do
                [dlay] -> {:stream, dlay}
                _ -> {:stream, slay}
              end

            {:ok, {slines ++ clines ++ elines, expr, lay, :fail, st}}
          end
        else
          _ -> {:error, "c:unsupported"}
        end
    end
  end

  defp emit_tm({:match, scrut, arms}, env, st) do
    with {:ok, {lines, ex, lay, eff, st}} <- emit_tm(scrut, env, st) do
      {lines, ex, st} = as_name(lines, ex, eff, st)
      kind = match_kind(lay, arms, st.book)
      ex = shown_scrut(ex, lay, kind, st)

      with {:ok, expr, rlay, st} <- emit_match(scrut_lay(kind), ex, arms, env, st) do
        {:ok, {lines, expr, rlay, :pure, st}}
      end
    end
  end

  defp emit_tm({:wrd, k, op, args}, env, st) do
    with {:ok, {lines, exprs, lays, effs, st}} <- emit_list(args, env, st) do
      forced =
        exprs
        |> Enum.zip(effs)
        |> Enum.map(fn {ex, eff} -> force(ex, eff) end)

      case word_zig(k, op, forced, lays, st) do
        {:ok, {more, expr, lay, eff, st}} ->
          {:ok, {lines ++ more, expr, lay, eff, st}}

        {:error, _} = err ->
          err
      end
    end
  end

  defp emit_tm({:byt, bin}, _env, st) when is_binary(bin) do
    if bin == "" do
      {:ok, {[], "#{g("slice_empty")}()", :slice, :pure, st}}
    else
      {tmp, st} = local(st, g("lit"))
      bytes = bin |> :binary.bin_to_list() |> Enum.map_join(", ", &Integer.to_string/1)

      lines = [
        "const #{tmp} = struct { const data = [_]u8{#{bytes}}; };"
      ]

      expr =
        ".{ .p = @as([*]const u8, @ptrCast(&#{tmp}.data)), .n = #{tmp}.data.len }"

      {:ok, {lines, expr, :slice, :pure, st}}
    end
  end

  defp emit_tm({:bcat, a, b}, env, st) do
    with {:ok, {la, ea, _, eaeff, st}} <- emit_tm(a, env, st),
         {:ok, {lb, eb, _, ebeff, st}} <- emit_tm(b, env, st) do
      expr = "#{g("bytes_cat")}(#{al()}, #{force(ea, eaeff)}, #{force(eb, ebeff)})"
      {:ok, {la ++ lb, expr, :slice, :fail, st}}
    end
  end

  defp emit_tm({:blen, a}, env, st) do
    with {:ok, {ls, ex, _, eff, st}} <- emit_tm(a, env, st) do
      {:ok, {ls, "@as(u64, #{force(ex, eff)}.n)", :u64, :pure, st}}
    end
  end

  defp emit_tm({:beq, a, b}, env, st) do
    with {:ok, {la, ea, _, eaeff, st}} <- emit_tm(a, env, st),
         {:ok, {lb, eb, _, ebeff, st}} <- emit_tm(b, env, st) do
      expr = "#{g("slice_eq")}(#{force(ea, eaeff)}, #{force(eb, ebeff)})"
      {:ok, {la ++ lb, expr, :wbool, :pure, st}}
    end
  end

  defp emit_tm({:bsub, s, off, len}, env, st) do
    with {:ok, {ls, es, _, eseff, st}} <- emit_tm(s, env, st),
         {:ok, {lo, eo, _, eoeff, st}} <- emit_tm(off, env, st),
         {:ok, {ln, en, _, eneff, st}} <- emit_tm(len, env, st) do
      expr = "#{g("slice_sub")}(#{force(es, eseff)}, #{force(eo, eoeff)}, #{force(en, eneff)})"
      {:ok, {ls ++ lo ++ ln, expr, :slice, :pure, st}}
    end
  end

  defp emit_tm({:bget, s, i}, env, st) do
    with {:ok, {ls, es, _, eseff, st}} <- emit_tm(s, env, st),
         {:ok, {li, ei, _, eieff, st}} <- emit_tm(i, env, st) do
      expr = "#{g("slice_get")}(#{force(es, eseff)}, #{force(ei, eieff)})"
      {:ok, {ls ++ li, expr, {:opt, :u8}, :pure, st}}
    end
  end

  defp emit_tm({:btil, s, b}, env, st) do
    with {:ok, {ls, es, _, eseff, st}} <- emit_tm(s, env, st),
         {:ok, {lb, eb, _, ebeff, st}} <- emit_tm(b, env, st) do
      expr = "#{g("slice_until")}(#{force(es, eseff)}, #{force(eb, ebeff)})"
      {:ok, {ls ++ lb, expr, :slice, :pure, st}}
    end
  end

  defp emit_tm({:baft, s, b}, env, st) do
    with {:ok, {ls, es, _, eseff, st}} <- emit_tm(s, env, st),
         {:ok, {lb, eb, _, ebeff, st}} <- emit_tm(b, env, st) do
      expr = "#{g("slice_after")}(#{force(es, eseff)}, #{force(eb, ebeff)})"
      {:ok, {ls ++ lb, expr, :slice, :pure, st}}
    end
  end

  defp emit_tm({:sbytes, _}, _env, _st), do: {:error, "c:string"}

  defp emit_tm({:bunc, s}, env, st) do
    nothing = Map.get(st.ctor_fns, {"Maybe", "nothing"})
    just = Map.get(st.ctor_fns, {"Maybe", "just"})

    if nothing == nil or just == nil do
      {:error, "c:unsupported"}
    else
      with {:ok, {lines, ex, _, eff, st}} <- emit_tm(s, env, st) do
        {cur, st} = local(st, nil)
        {byte, st} = local(st, nil)
        {rest, st} = local(st, nil)
        {bp, st} = local(st, nil)
        {sp, st} = local(st, nil)
        {pp, st} = local(st, nil)
        sl = g("slice")
        pair = g("Pair")
        erase = g("erase")
        ally = al()
        lines = lines ++ ["const #{cur} = #{force(ex, eff)};"]

        expr = """
        if (#{cur}.n == 0) #{nothing}() else blk: {
            const #{byte}: u8 = #{cur}.p[0];
            const #{rest}: #{sl} = .{ .p = #{cur}.p + 1, .n = #{cur}.n - 1 };
            const #{bp} = try #{ally}.create(u8);
            #{bp}.* = #{byte};
            const #{sp} = try #{ally}.create(#{sl});
            #{sp}.* = #{rest};
            const #{pp} = try #{ally}.create(#{pair});
            #{pp}.* = .{ .#{g("field_fst")} = #{erase}(#{bp}), .#{g("field_snd")} = #{erase}(#{sp}) };
            break :blk try #{just}(#{ally}, #{erase}(#{pp}));
        }
        """

        {:ok, {lines, String.trim(expr), {:data, "Maybe"}, :pure, st}}
      end
    end
  end

  defp emit_tm({:bfold, step, caps, z, s}, env, st) do
    with {:ok, {cl, ces, _, ceffs, st}} <- emit_list(caps, env, st),
         {:ok, {zl, ze, zlay, zeff, st}} <- emit_tm(z, env, st),
         {:ok, {sl, se, _, seff, st}} <- emit_tm(s, env, st) do
      {acc, st} = local(st, nil)
      {cur, st} = local(st, nil)
      {byte, st} = local(st, nil)
      {rest, st} = local(st, nil)
      fname = Map.fetch!(st.step_names, step)
      cap_args = Enum.map(Enum.zip(ces, ceffs), fn {ex, eff} -> force(ex, eff) end)
      args = Enum.join([al() | cap_args] ++ [byte, rest, acc], ", ")
      slice = g("slice")

      more = [
        "var #{acc}: #{pty(zlay, st)} = #{force(ze, zeff)};",
        "var #{cur}: #{slice} = #{force(se, seff)};",
        "while (#{cur}.n > 0) {",
        "    const #{byte}: u8 = #{cur}.p[0];",
        "    const #{rest}: #{slice} = .{ .p = #{cur}.p + 1, .n = #{cur}.n - 1 };",
        "    #{acc} = try #{fname}(#{args});",
        "    #{cur} = #{rest};",
        "}"
      ]

      {:ok, {cl ++ zl ++ sl ++ more, acc, zlay, :pure, st}}
    end
  end

  defp emit_tm({:str, _}, _env, _st), do: {:error, "c:string"}
  defp emit_tm({:scat, _, _}, _env, _st), do: {:error, "c:string"}
  defp emit_tm({:slen, _}, _env, _st), do: {:error, "c:string"}
  defp emit_tm({:seq, _, _}, _env, _st), do: {:error, "c:string"}
  defp emit_tm(_other, _env, _st), do: {:error, "c:unsupported"}

  defp emit_list(ts, env, st) do
    Enum.reduce_while(ts, {:ok, [], [], [], [], st}, fn t, {:ok, lines, exprs, lays, effs, st} ->
      case emit_tm(t, env, st) do
        {:ok, {ls, ex, lay, eff, st}} ->
          {ls, ex, eff, st} = materialize(ls, ex, eff, st)
          {:cont, {:ok, lines ++ ls, exprs ++ [ex], lays ++ [lay], effs ++ [eff], st}}

        {:error, _} = err ->
          {:halt, err}
      end
    end)
    |> case do
      {:ok, lines, exprs, lays, effs, st} -> {:ok, {lines, exprs, lays, effs, st}}
      err -> err
    end
  end

  defp emit_caps(caps, env, st) do
    emit_list(Enum.map(caps, fn {_name, tm} -> tm end), env, st)
  end

  defp env_expr(_cexs, _clays, _ceffs, [], _info, st) do
    {[], "#{g("erase")}(&#{g("no_env")})", st}
  end

  defp env_expr(cexs, clays, ceffs, cap_lays, info, st) do
    {e, st} = local(st, g("e"))

    fields =
      [cexs, clays, ceffs, cap_lays]
      |> Enum.zip()
      |> Enum.with_index()
      |> Enum.map_join(", ", fn {{ex, from, eff, to}, i} ->
        ".#{g("f", i)} = #{coerce(force(ex, eff), from, to, st)}"
      end)

    lines = [
      "const #{e} = try #{al()}.create(#{info.env});",
      "#{e}.* = .{ #{fields} };"
    ]

    {lines, "#{g("erase")}(#{e})", st}
  end

  defp emit_match(:nat, ex, [{:arm, "zero", [], z}, {:arm, "suc", [y], s}], env, st) do
    with {:ok, zpat, zlines, zenv, st} <- {:ok, ".#{g("tag_zero")} => ", [], env, st},
         {:ok, spat, slines, senv, st} <- suc_pattern(y, s, env, st),
         {:ok, zarm, zlay, st} <- arm_text(z, zlines, zenv, st),
         {:ok, sarm, slay, st} <- arm_text(s, slines, senv, st) do
      {expr, lay, st} =
        finish_match(ex, [{"#{zpat}", zarm, zlay}, {"#{spat}", sarm, slay}], st)

      {:ok, expr, lay, st}
    end
  end

  defp emit_match({:data, "Atom"}, ex, arms, env, st) do
    with {:ok, rendered, st} <-
           reduce_arms(arms, st, fn {:arm, name, _binders, body}, st ->
             case Map.fetch(st.atoms, name) do
               {:ok, variant} ->
                 with {:ok, arm, lay, st} <- arm_text(body, [], env, st) do
                   {:ok, {".#{variant} => ", arm, lay}, st}
                 end

               :error ->
                 {:error, "c:unsupported"}
             end
           end) do
      {expr, lay, st} = finish_match(ex, rendered, st)
      {:ok, expr, lay, st}
    end
  end

  defp emit_match({:data, dname}, ex, arms, env, st) do
    with {:ok, rendered, st} <-
           reduce_arms(arms, st, fn {:arm, cname, binders, body}, st ->
             variant = Map.get(st.variants, {dname, cname})

             case ctor_fields(st.book, dname, cname) do
               {:ok, fields}
               when variant != nil and length(fields) == length(binders) ->
                 {pat, pre, env1, st} = arm_pattern(variant, fields, binders, body, env, st)

                 with {:ok, arm, lay, st} <- arm_text(body, pre, env1, st) do
                   {:ok, {pat, arm, lay}, st}
                 end

               _ ->
                 {:error, "c:unsupported"}
             end
           end) do
      {expr, lay, st} = finish_match(ex, rendered, st)
      {:ok, expr, lay, st}
    end
  end

  # WBool is a u8. 0 is wfalse. The test does not allocate.
  defp emit_match(:wbool, ex, [{:arm, "wtrue", [], t}, {:arm, "wfalse", [], f}], env, st) do
    with {:ok, tarm, tlay, st} <- arm_text(t, [], env, st),
         {:ok, farm, flay, st} <- arm_text(f, [], env, st) do
      target = join_lay([tlay, flay])
      {ttext, st} = render_arm(elem(tarm, 0), elem(tarm, 1), elem(tarm, 2), tlay, target, st)
      {ftext, st} = render_arm(elem(farm, 0), elem(farm, 1), elem(farm, 2), flay, target, st)
      {:ok, "if ((#{ex}) == 0) #{ftext} else #{ttext}", target, st}
    end
  end

  # Opt is `?T`. The payload is the captured value. null is wnone.
  defp emit_match({:opt, pay}, ex, [{:arm, "wsome", [y], s}, {:arm, "wnone", [], n}], env, st) do
    {pat, env1, st} =
      if binder_used?(s, y, []) do
        {rn, st} = local(st, spell(y))
        {"|#{rn}|", [{y, rn, pay} | env], st}
      else
        {"|_|", env, st}
      end

    with {:ok, sarm, slay, st} <- arm_text(s, [], env1, st),
         {:ok, narm, nlay, st} <- arm_text(n, [], env, st) do
      target = join_lay([slay, nlay])
      {stext, st} = render_arm(elem(sarm, 0), elem(sarm, 1), elem(sarm, 2), slay, target, st)
      {ntext, st} = render_arm(elem(narm, 0), elem(narm, 1), elem(narm, 2), nlay, target, st)
      {:ok, "if (#{ex}) #{pat} #{stext} else #{ntext}", target, st}
    end
  end

  defp emit_match(_lay, _ex, _arms, _env, _st), do: {:error, "c:unsupported"}

  # An alias is :opaque. The arms still say Nat, Atom, or a data type,
  # the same way the C emitter's match_kind does. Reveal before the switch.
  defp match_kind(:nat, _arms, _book), do: :nat
  defp match_kind(:wbool, _arms, _book), do: :wbool
  defp match_kind({:opt, pay}, _arms, _book), do: {:opt, pay}
  defp match_kind({:data, "Atom"}, _arms, _book), do: :atom
  defp match_kind({:data, name}, _arms, _book), do: {:data, name}
  defp match_kind(_lay, [{:arm, "zero", [], _}, {:arm, "suc", [_], _}], _book), do: :nat
  defp match_kind(_lay, [{:arm, "wtrue", [], _}, {:arm, "wfalse", [], _}], _book), do: :wbool

  defp match_kind(_lay, [{:arm, "wsome", [_], _}, {:arm, "wnone", [], _}], _book),
    do: {:opt, :opaque}

  defp match_kind(_lay, arms, book) do
    cond do
      atom_arms?(arms, book) -> :atom
      name = ctor_data(arms, book) -> {:data, name}
      true -> :unknown
    end
  end

  defp atom_arms?(arms, book) do
    atoms = Ast.atoms(book)

    atoms != [] and
      Enum.all?(arms, fn
        {:arm, name, [], _} -> name in atoms
        _ -> false
      end)
  end

  defp ctor_data([{:arm, cname, _, _} | _], book) do
    case data_of_ctor(book, cname) do
      %{name: name} -> name
      _ -> nil
    end
  end

  defp ctor_data(_, _), do: nil

  defp data_of_ctor(book, name) do
    Enum.find(book, fn
      %{kind: :data, ctors: cs} -> Enum.any?(cs, &(&1.name == name))
      _ -> false
    end)
  end

  defp scrut_lay(:nat), do: :nat
  defp scrut_lay(:wbool), do: :wbool
  defp scrut_lay({:opt, pay}), do: {:opt, pay}
  defp scrut_lay(:atom), do: {:data, "Atom"}
  defp scrut_lay({:data, _} = lay), do: lay
  defp scrut_lay(:unknown), do: :unknown

  defp shown_scrut(ex, _lay, :unknown, _st), do: ex
  defp shown_scrut(ex, lay, kind, st), do: coerce(ex, lay, scrut_lay(kind), st)

  defp suc_pattern(y, body, env, st) do
    if binder_used?(body, y, []) do
      {rn, st} = local(st, spell(y))
      {:ok, ".#{g("tag_suc")} => |#{rn}| ", [], [{y, rn, :nat} | env], st}
    else
      {:ok, ".#{g("tag_suc")} => |_| ", [], env, st}
    end
  end

  defp arm_pattern(variant, [], _binders, _body, env, st) do
    {".#{variant} => ", [], env, st}
  end

  defp arm_pattern(variant, [lay], [bname], body, env, st) do
    if binder_used?(body, bname, []) do
      {rn, st} = local(st, spell(bname))
      {".#{variant} => |#{rn}| ", [], [{bname, rn, lay} | env], st}
    else
      {".#{variant} => |_| ", [], env, st}
    end
  end

  defp arm_pattern(variant, fields, binders, body, env, st) do
    used? =
      Enum.with_index(binders, fn bname, i ->
        binder_used?(body, bname, Enum.drop(binders, i + 1))
      end)

    if Enum.any?(used?) do
      {pay, st} = local(st, g("p"))

      {consts, env, st} =
        [binders, fields, used?]
        |> Enum.zip()
        |> Enum.with_index()
        |> Enum.reduce({[], env, st}, fn
          {{bname, lay, true}, i}, {consts, env, st} ->
            {rn, st} = local(st, spell(bname))
            {consts ++ ["const #{rn} = #{pay}.#{g("f", i)};"], [{bname, rn, lay} | env], st}

          {{_bname, _lay, false}, _i}, acc ->
            acc
        end)

      {".#{variant} => |#{pay}| ", consts, env, st}
    else
      {".#{variant} => |_| ", [], env, st}
    end
  end

  defp arm_text(body, pre, env, st) do
    with {:ok, {lines, expr, lay, eff, st}} <- emit_tm(body, env, st) do
      {:ok, {pre ++ lines, expr, eff}, lay, st}
    end
  end

  defp finish_match(scrut, arms, st) do
    target = join_lay(Enum.map(arms, fn {_pat, {_lines, _ex, _eff}, lay} -> lay end))

    {rendered, st} =
      Enum.map_reduce(arms, st, fn {pat, {lines, expr, eff}, lay}, st ->
        {text, st} = render_arm(lines, expr, eff, lay, target, st)
        {{pat, text}, st}
      end)

    body = Enum.map_join(rendered, "\n", fn {pat, text} -> place_arm(pat, text) end)
    {"switch (#{scrut}.*) {\n#{body}\n}", target, st}
  end

  defp render_arm(lines, expr, eff, lay, target, st) do
    coerced = coerce(force(expr, eff), lay, target, st)

    if lines == [] do
      {coerced, st}
    else
      {lab, st} = fresh_label(st)
      inner = indent(Enum.join(lines ++ ["break :#{lab} (#{coerced});"], "\n"), 4)
      {"#{lab}: {\n#{inner}\n}", st}
    end
  end

  defp place_arm(pat, arm) do
    if String.contains?(arm, "\n") do
      [first | rest] = String.split(arm, "\n")
      rest = Enum.map_join(rest, "\n", &("    " <> &1))
      "    #{pat}#{first}\n#{rest},"
    else
      "    #{pat}#{arm},"
    end
  end

  defp join_lay(lays) do
    case Enum.uniq(Enum.reject(lays, &(&1 == :never))) do
      [] -> :never
      [one] -> one
      _many -> :opaque
    end
  end

  defp reduce_arms(arms, st, fun) do
    Enum.reduce_while(arms, {:ok, [], st}, fn arm, {:ok, acc, st} ->
      case fun.(arm, st) do
        {:ok, text, st} -> {:cont, {:ok, acc ++ [text], st}}
        {:error, _} = err -> {:halt, err}
      end
    end)
    |> case do
      {:ok, acc, st} -> {:ok, acc, st}
      err -> err
    end
  end

  defp maybe_bind(src, rn, slot, lay, body, later, st) do
    line = "const #{rn} = #{bind_half(slot, lay, st)};"
    if binder_used?(body, src, later), do: [line], else: [line, "_ = #{rn};"]
  end

  defp bind_half(slot, :opaque, _st), do: slot
  defp bind_half(slot, lay, st), do: "#{g("reveal")}(#{zty(lay, st)}, #{slot})"

  defp coerce(ex, :never, _to, _st), do: ex
  defp coerce(ex, from, to, _st) when from == to, do: ex
  defp coerce("null", {:opt, _}, {:opt, _} = to, st), do: "@as(#{zty(to, st)}, null)"

  defp coerce(ex, from, to, st) do
    cond do
      pty(from, st) == pty(to, st) -> ex
      to == :opaque -> "#{g("erase")}(#{ex})"
      from == :opaque -> "#{g("reveal")}(#{zty(to, st)}, #{ex})"
      true -> "#{g("reveal")}(#{zty(to, st)}, #{g("erase")}(#{ex}))"
    end
  end

  defp pair_halves({:pair, a, b}), do: {a, b}
  defp pair_halves(_), do: {:opaque, :opaque}

  defp pair_view({:pair, _, _} = lay), do: lay
  defp pair_view(_), do: {:pair, :opaque, :opaque}

  defp stream_view({:stream, _} = lay), do: lay
  defp stream_view(_), do: {:stream, :opaque}

  defp uncons_lay({:stream, s}), do: {:pair, :opaque, {:stream, s}}
  defp uncons_lay(_), do: {:pair, :opaque, :opaque}

  defp pair_target({:pair, _, _} = lay), do: lay
  defp pair_target(_), do: {:pair, :opaque, :opaque}

  # Words are passed by value. Wrapping uses +%/-%/*%. Shifts and
  # division are guarded so an out-of-range count or a zero divisor is
  # never evaluated. Signed division also refuses INT64_MIN / −1.
  defp word_zig(k, {:lit, k, n}, [], _lays, st) do
    {:ok, {[], z_lit(k, n), k, :pure, st}}
  end

  defp word_zig(_k, true, [], _lays, st), do: {:ok, {[], "@as(u8, 1)", :wbool, :pure, st}}
  defp word_zig(_k, false, [], _lays, st), do: {:ok, {[], "@as(u8, 0)", :wbool, :pure, st}}
  defp word_zig(_k, :none, [], _lays, st), do: {:ok, {[], "null", {:opt, :opaque}, :pure, st}}

  defp word_zig(k, {:of, k}, [nat], _lays, st) do
    acc = "#{g("to_u64")}(#{nat})"

    expr =
      case k do
        :u8 -> "@as(u8, @truncate(#{acc}))"
        :u32 -> "@as(u32, @truncate(#{acc}))"
        :u64 -> acc
        :i64 -> "@as(i64, @bitCast(#{acc}))"
      end

    {:ok, {[], expr, k, :pure, st}}
  end

  defp word_zig(k, :ton, [x], _lays, st) do
    bits = if k == :i64, do: "@as(u64, @bitCast(#{x}))", else: "@as(u64, #{x})"
    {:ok, {[], "#{g("from_u64")}(#{al()}, #{bits})", :nat, :fail, st}}
  end

  defp word_zig(k, op, [x, y], _lays, st) when op in [:add, :sub, :mul] do
    sym = %{add: "+%", sub: "-%", mul: "*%"}
    {:ok, {[], "(#{x}) #{sym[op]} (#{y})", k, :pure, st}}
  end

  defp word_zig(k, op, [x, y], _lays, st) when op in [:and, :or, :xor] do
    {:ok, {[], z_bit(op, k, x, y), k, :pure, st}}
  end

  defp word_zig(k, :not, [x], _lays, st), do: {:ok, {[], z_not(k, x), k, :pure, st}}

  defp word_zig(_k, op, [x, y], _lays, st) when op in [:eq, :lt, :le] do
    sym = %{eq: "==", lt: "<", le: "<="}
    {:ok, {[], "@as(u8, @intFromBool((#{x}) #{sym[op]} (#{y})))", :wbool, :pure, st}}
  end

  defp word_zig(k, op, [x, y], _lays, st) when op in [:cadd, :csub, :cmul] do
    z_checked(k, op, x, y, st)
  end

  defp word_zig(k, op, [x, y], _lays, st) when op in [:div, :rem] do
    z_divrem(k, op, x, y, st)
  end

  defp word_zig(k, op, [x, amt], _lays, st) when op in [:shl, :shr] do
    z_shift(k, op, x, amt, st)
  end

  defp word_zig(k, {:cast, k}, [x], [src | _], st) do
    {:ok, {[], z_cast(k, src, x), k, :pure, st}}
  end

  defp word_zig(k, :some, [x], _lays, st) do
    {:ok, {[], "@as(?#{zty(k, st)}, #{x})", {:opt, k}, :pure, st}}
  end

  defp word_zig(_k, _op, _args, _lays, _st), do: {:error, "c:unsupported"}

  defp z_lit(:i64, n) do
    n = rem(n, 18_446_744_073_709_551_616)

    if n >= 9_223_372_036_854_775_808,
      do: "@as(i64, @bitCast(@as(u64, #{n})))",
      else: "@as(i64, #{n})"
  end

  defp z_lit(k, n) do
    mod =
      case k do
        :u8 -> 256
        :u32 -> 4_294_967_296
        _ -> 18_446_744_073_709_551_616
      end

    "@as(#{k}, #{rem(n, mod)})"
  end

  defp z_bit(op, :i64, x, y) do
    sym = %{and: "&", or: "|", xor: "^"}
    "@as(i64, @bitCast(@as(u64, @bitCast(#{x})) #{sym[op]} @as(u64, @bitCast(#{y}))))"
  end

  defp z_bit(op, _k, x, y) do
    sym = %{and: "&", or: "|", xor: "^"}
    "(#{x}) #{sym[op]} (#{y})"
  end

  defp z_not(:i64, x), do: "@as(i64, @bitCast(~@as(u64, @bitCast(#{x}))))"
  defp z_not(_k, x), do: "~(#{x})"

  defp z_checked(k, op, x, y, st) do
    {ov, st} = local(st, g("s"))
    {out, st} = local(st, g("t"))
    builtin = %{cadd: "@addWithOverflow", csub: "@subWithOverflow", cmul: "@mulWithOverflow"}

    lines = [
      "const #{ov} = #{builtin[op]}(#{x}, #{y});",
      "const #{out}: ?#{zty(k, st)} = if (#{ov}[1] == 0) #{ov}[0] else null;"
    ]

    {:ok, {lines, out, {:opt, k}, :pure, st}}
  end

  defp z_divrem(k, op, x, y, st) do
    {out, st} = local(st, g("t"))
    fnm = if op == :div, do: "@divTrunc", else: "@rem"

    lines = [
      "const #{out}: ?#{zty(k, st)} = if (#{z_div_guard(k, x, y)}) null else #{fnm}(#{x}, #{y});"
    ]

    {:ok, {lines, out, {:opt, k}, :pure, st}}
  end

  defp z_div_guard(:i64, x, y) do
    "#{y} == 0 or (@as(u64, @bitCast(#{x})) == (@as(u64, 1) << 63) and @as(u64, @bitCast(#{y})) == ~@as(u64, 0))"
  end

  defp z_div_guard(_k, _x, y), do: "#{y} == 0"

  defp z_shift(k, op, x, amt, st) do
    {sh, st} = local(st, g("s"))
    {p, st} = local(st, g("p"))
    {out, st} = local(st, g("t"))
    {lab, st} = fresh_label(st)
    w = z_width(k)
    zero = g("tag_zero")
    suc = g("tag_suc")
    nxt = g("n")

    lines = [
      "var #{sh}: u32 = 0;",
      "var #{p} = #{amt};",
      "#{lab}: while (#{sh} + 1 < #{w}) {",
      "    switch (#{p}.*) {",
      "        .#{zero} => break :#{lab},",
      "        .#{suc} => |#{nxt}| { #{sh} += 1; #{p} = #{nxt}; },",
      "    }",
      "}",
      "const #{out}: #{zty(k, st)} = if (switch (#{p}.*) { .#{zero} => false, .#{suc} => true, }) #{z_shift_oob(k, op, x)} else #{z_shift_in(k, op, x, sh)};"
    ]

    {:ok, {lines, out, k, :pure, st}}
  end

  defp z_width(:u8), do: 8
  defp z_width(:u32), do: 32
  defp z_width(_), do: 64

  defp z_shamt(:u8), do: "u3"
  defp z_shamt(:u32), do: "u5"
  defp z_shamt(_), do: "u6"

  defp z_shift_oob(_k, :shl, _x), do: "0"
  defp z_shift_oob(k, :shr, _x) when k != :i64, do: "0"

  defp z_shift_oob(:i64, :shr, x) do
    "if (@as(u64, @bitCast(#{x})) >= (@as(u64, 1) << 63)) @as(i64, -1) else @as(i64, 0)"
  end

  defp z_shift_in(k, :shl, x, sh) when k != :i64 do
    "#{x} << @as(#{z_shamt(k)}, @intCast(#{sh}))"
  end

  defp z_shift_in(:i64, :shl, x, sh) do
    "@as(i64, @bitCast(@as(u64, @bitCast(#{x})) << @as(u6, @intCast(#{sh}))))"
  end

  defp z_shift_in(k, :shr, x, sh) when k != :i64 do
    "#{x} >> @as(#{z_shamt(k)}, @intCast(#{sh}))"
  end

  defp z_shift_in(:i64, :shr, x, sh) do
    "#{x} >> @as(u6, @intCast(#{sh}))"
  end

  defp z_cast(k, src, x), do: z_from_u64(k, z_as_u64(src, x))

  defp z_as_u64(:i64, x), do: "@as(u64, @bitCast(#{x}))"
  defp z_as_u64(:u64, x), do: "(#{x})"
  defp z_as_u64(_src, x), do: "@as(u64, #{x})"

  defp z_from_u64(:u8, bits), do: "@as(u8, @truncate(#{bits}))"
  defp z_from_u64(:u32, bits), do: "@as(u32, @truncate(#{bits}))"
  defp z_from_u64(:u64, bits), do: "(#{bits})"
  defp z_from_u64(:i64, bits), do: "@as(i64, @bitCast(#{bits}))"

  defp pty(lay, st) when lay in [:u8, :u32, :u64, :i64, :wbool, :slice], do: zty(lay, st)
  defp pty({:opt, _} = lay, st), do: zty(lay, st)
  defp pty(lay, st), do: "*const " <> zty(lay, st)

  defp zty(:slice, _st), do: g("slice")
  defp zty(:u8, _st), do: "u8"
  defp zty(:u32, _st), do: "u32"
  defp zty(:u64, _st), do: "u64"
  defp zty(:i64, _st), do: "i64"
  defp zty(:wbool, _st), do: "u8"
  defp zty({:opt, pay}, st), do: "?" <> pty(pay, st)
  defp zty(:nat, _st), do: g("Nat")
  defp zty(:unit, _st), do: g("Unit")
  defp zty(:opaque, _st), do: "anyopaque"
  defp zty(:never, _st), do: "anyopaque"
  defp zty({:pair, _, _}, _st), do: g("Pair")
  defp zty({:stream, _}, _st), do: g("Stream")
  defp zty({:data, "Atom"}, _st), do: g("Atom")
  defp zty({:data, name}, st), do: Map.fetch!(st.types, name)

  defp data_layouts(book) do
    book
    |> Enum.filter(&(Map.get(&1, :kind) == :data))
    |> Enum.map(fn d ->
      ctors =
        d.ctors
        |> Enum.with_index()
        |> Enum.map(fn {ctor, tag} ->
          fields =
            case ctor_fields(book, d.name, ctor.name) do
              {:ok, fs} -> fs
              :error -> []
            end

          %{name: ctor.name, tag: tag, fields: fields}
        end)

      %{name: d.name, layout: {:data, d.name}, constructors: ctors}
    end)
  end

  defp ctor_fields(book, dname, cname) do
    case find_data(book, dname) do
      nil ->
        :error

      data ->
        case Enum.find(data.ctors, &(&1.name == cname)) do
          nil ->
            :error

          ctor ->
            fields =
              telescope(ctor.type)
              |> Enum.flat_map(fn
                {:erased, _, _} -> []
                {_, a, _} -> [type_layout(book, a)]
              end)

            {:ok, fields}
        end
    end
  end

  defp type_layout(_book, :nat), do: :nat
  defp type_layout(_book, :unit), do: :unit
  defp type_layout(_book, :atom), do: {:data, "Atom"}
  defp type_layout(book, {:stream, a}), do: {:stream, type_layout(book, a)}

  defp type_layout(book, {:var, name}) do
    if data?(book, name), do: {:data, name}, else: :opaque
  end

  defp type_layout(book, {:def, name}), do: type_layout(book, {:var, name})
  defp type_layout(book, {:app, f, _}), do: type_layout(book, f)

  defp type_layout(book, {:prod, a, b}) do
    {:pair, type_layout(book, a), type_layout(book, b)}
  end

  defp type_layout(book, {:ann, e, _}), do: type_layout(book, e)
  defp type_layout(_book, :i64), do: :i64
  defp type_layout(_book, {:word, {:ty, :u8}, []}), do: :u8
  defp type_layout(_book, {:word, {:ty, :u32}, []}), do: :u32
  defp type_layout(_book, {:word, {:ty, :u64}, []}), do: :u64
  defp type_layout(_book, {:word, :bool, []}), do: :wbool
  defp type_layout(_book, {:word, {:optk, :u8}, []}), do: {:opt, :u8}
  defp type_layout(_book, {:word, {:optk, :u32}, []}), do: {:opt, :u32}
  defp type_layout(_book, {:word, {:optk, :u64}, []}), do: {:opt, :u64}
  defp type_layout(_book, {:word, {:optk, :i64}, []}), do: {:opt, :i64}
  defp type_layout(book, {:word, :opt, [a]}), do: {:opt, type_layout(book, a)}
  defp type_layout(_book, :bytes), do: :slice
  defp type_layout(_book, :slice), do: :slice
  defp type_layout(_book, _), do: :opaque

  defp telescope(t), do: telescope(t, [])
  defp telescope({:pi, q, a, x, b}, acc), do: telescope(b, [{q, a, x} | acc])
  defp telescope(_t, acc), do: Enum.reverse(acc)

  defp find_data(book, name) do
    Enum.find(book, &(Map.get(&1, :kind) == :data and &1.name == name))
  end

  defp data?(book, name) do
    Enum.any?(book, &(Map.get(&1, :kind) == :data and &1.name == name))
  end

  defp lookup(env, name) do
    Enum.find_value(env, fn
      {^name, rn, lay} -> {rn, lay}
      _ -> nil
    end)
  end

  defp materialize(lines, expr, eff, st) do
    if lines != [] or String.contains?(expr, "\n") do
      {rn, st} = local(st, g("s"))
      {lines ++ ["const #{rn} = #{force(expr, eff)};"], rn, :pure, st}
    else
      {lines, expr, eff, st}
    end
  end

  defp as_name(lines, expr, eff, st) do
    if lines == [] and eff == :pure and identifier?(expr) do
      {lines, expr, st}
    else
      {rn, st} = local(st, g("s"))
      {lines ++ ["const #{rn} = #{force(expr, eff)};"], rn, st}
    end
  end

  defp identifier?(ex), do: String.match?(ex, ~r/^[A-Za-z_][A-Za-z0-9_]*$/)

  defp force(ex, :fail), do: "try #{ex}"
  defp force(ex, :pure), do: ex

  defp local(st, base) do
    base = if base in [nil, ""], do: g("s"), else: base
    {name, scope} = Name.bind_n(base, st.n, st.scope)
    {name, %{st | n: st.n + 1, scope: scope}}
  end

  defp fresh_label(st) do
    {name, scope} = Name.bind(g("blk", st.blk), st.scope)
    {name, %{st | blk: st.blk + 1, scope: scope}}
  end

  # ofNat and toNat name the allocator in the emitted text. Discarding a
  # parameter that text also names is an error, so the scan sees the
  # statements and the result expression, not only the source term.
  defp alloc_discard(prefix, body, st, lines, expr) do
    name = al()

    used =
      mentions_alloc?(body, st) or
        Enum.any?(lines, &String.contains?(&1, name)) or
        String.contains?(expr, name)

    if used, do: prefix, else: prefix ++ ["_ = #{name};"]
  end

  defp param_discards(lines, params, body) do
    params
    |> Enum.with_index()
    |> Enum.reduce(lines, fn {{src, rn, _lay}, i}, lines ->
      if binder_used?(body, src, Enum.drop(params, i + 1)),
        do: lines,
        else: lines ++ ["_ = #{rn};"]
    end)
  end

  # A later binder of the same source name hides this one. `later` holds
  # the names still to come, as binaries or `{name, ...}` tuples.
  defp binder_used?(body, name, later) do
    not Enum.any?(later, &same_binder?(&1, name)) and uses?(body, name)
  end

  defp same_binder?(n, name) when is_binary(n), do: n == name
  defp same_binder?({n, _, _}, name), do: n == name
  defp same_binder?({n, _}, name), do: n == name
  defp same_binder?(_, _), do: false

  defp mentions_alloc?(tm, st) do
    case tm do
      {:call, _, _} ->
        true

      {:su, _} ->
        true

      {:pair, _, _} ->
        true

      {:uncons, _} ->
        true

      {:stream, _, _, _} ->
        true

      {:con, "Atom", _, _} ->
        false

      {:con, d, c, args} ->
        case ctor_fields(st.book, d, c) do
          {:ok, []} -> Enum.any?(args, &mentions_alloc?(&1, st))
          {:ok, _fields} -> true
          :error -> true
        end

      {:let, _, _, v, b} ->
        mentions_alloc?(v, st) or mentions_alloc?(b, st)

      {:letp, _, _, e, b} ->
        mentions_alloc?(e, st) or mentions_alloc?(b, st)

      {:match, s, arms} ->
        mentions_alloc?(s, st) or
          Enum.any?(arms, fn {:arm, _, _, body} -> mentions_alloc?(body, st) end)

      t when is_tuple(t) ->
        t |> Tuple.to_list() |> Enum.any?(&mentions_alloc?(&1, st))

      t when is_list(t) ->
        Enum.any?(t, &mentions_alloc?(&1, st))

      _ ->
        false
    end
  end

  defp uses?(tm, name), do: uses?(tm, name, MapSet.new())

  defp uses?({:var, n}, name, bound), do: n == name and not MapSet.member?(bound, name)

  defp uses?({:let, n, _, v, b}, name, bound) do
    uses?(v, name, bound) or uses?(b, name, MapSet.put(bound, n))
  end

  defp uses?({:letp, a, b, e, body}, name, bound) do
    uses?(e, name, bound) or uses?(body, name, bound |> MapSet.put(a) |> MapSet.put(b))
  end

  defp uses?({:match, s, arms}, name, bound) do
    uses?(s, name, bound) or
      Enum.any?(arms, fn {:arm, _, binders, body} ->
        inner = Enum.reduce(binders, bound, &MapSet.put(&2, &1))
        uses?(body, name, inner)
      end)
  end

  defp uses?({:stream, seed, caps, _name}, name, bound) do
    uses?(seed, name, bound) or Enum.any?(caps, fn {_n, tm} -> uses?(tm, name, bound) end)
  end

  defp uses?(tm, name, bound) when is_tuple(tm) do
    tm |> Tuple.to_list() |> Enum.any?(&uses?(&1, name, bound))
  end

  defp uses?(tm, name, bound) when is_list(tm), do: Enum.any?(tm, &uses?(&1, name, bound))
  defp uses?(_tm, _name, _bound), do: false

  defp fn_body(lines, expr) do
    indent(Enum.join(lines ++ ["return #{expr};"], "\n"), 4)
  end

  defp indent(s, n) do
    pad = String.duplicate(" ", n)
    s |> String.split("\n") |> Enum.map_join("\n", &(pad <> &1))
  end

  defp join(parts) do
    parts
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n\n")
    |> Kernel.<>("\n")
  end

  defp names_of(book, taken, spell) do
    names = Emit.def_names(book, spell, taken)
    {names, MapSet.union(taken, MapSet.new(Map.values(names)))}
  end

  # A step symbol is generated, so a source spelling cannot be one.
  defp name_steps(steps, taken, _spell) do
    Enum.reduce(steps, {%{}, taken}, fn fun, {map, used} ->
      {rn, used} = claim(step_symbol(fun.name), used)
      {Map.put(map, fun.name, rn), used}
    end)
  end

  defp step_symbol("step" <> n) do
    if String.match?(n, ~r/^[0-9]+$/), do: g("step", String.to_integer(n)), else: g("step")
  end

  defp ctor_fn_names(book, taken, spell) do
    Enum.reduce(data_decls(book), {%{}, taken}, fn d, {map, used} ->
      Enum.reduce(d.ctors, {map, used}, fn c, {map, used} ->
        {rn, used} = claim(spell.(c.name), used)
        {Map.put(map, {d.name, c.name}, rn), used}
      end)
    end)
  end

  defp type_names(book, taken, spell) do
    Enum.reduce(data_decls(book), {%{}, taken}, fn d, {map, used} ->
      {rn, used} = claim(spell.(d.name), used)
      {Map.put(map, d.name, rn), used}
    end)
  end

  defp variant_names(book) do
    Enum.reduce(data_decls(book), %{}, fn d, map ->
      {inner, _} =
        Enum.reduce(d.ctors, {%{}, MapSet.new()}, fn c, {acc, used} ->
          {rn, used} = claim(spell(c.name), used)
          {Map.put(acc, {d.name, c.name}, rn), used}
        end)

      Map.merge(map, inner)
    end)
  end

  defp atom_variants(book) do
    {map, _} =
      Enum.reduce(Ast.atoms(book), {%{}, MapSet.new()}, fn name, {map, used} ->
        {rn, used} = claim(spell(name), used)
        {Map.put(map, name, rn), used}
      end)

    map
  end

  defp atom_statics(used, atoms, taken) do
    Enum.reduce(used, {%{}, taken}, fn name, {map, taken} ->
      case Map.fetch(atoms, name) do
        {:ok, variant} ->
          {sn, taken} = claim(g("atom_" <> variant), taken)
          {Map.put(map, name, sn), taken}

        :error ->
          {map, taken}
      end
    end)
  end

  defp fieldless_statics(used, book, types, variants, taken) do
    Enum.reduce(used, {%{}, taken}, fn {dname, cname}, {map, taken} ->
      case ctor_fields(book, dname, cname) do
        {:ok, []} ->
          type = Map.fetch!(types, dname)
          variant = Map.fetch!(variants, {dname, cname})
          {sn, taken} = claim(g("val_" <> type <> "_" <> variant), taken)
          {Map.put(map, {dname, cname}, sn), taken}

        _ ->
          {map, taken}
      end
    end)
  end

  defp step_infos(steps, caps, taken) do
    Enum.reduce(steps, {%{}, taken}, fn fun, {map, taken} ->
      case Map.fetch(caps, fun.name) do
        {:ok, n} when n > 0 ->
          {env, taken} = claim(g("env", map_size(map)), taken)
          {Map.put(map, fun.name, %{cap_count: n, env: env}), taken}

        {:ok, n} ->
          {Map.put(map, fun.name, %{cap_count: n, env: nil}), taken}

        :error ->
          {Map.put(map, fun.name, %{cap_count: 0, env: nil}), taken}
      end
    end)
  end

  defp data_decls(book) do
    Enum.filter(book, &(Map.get(&1, :kind) == :data))
  end

  defp data_items(book, st, used) do
    book
    |> data_decls()
    |> Enum.map_join("\n\n", &data_item(&1, st, used))
  end

  defp data_item(d, st, used) do
    type = Map.fetch!(st.types, d.name)

    variants =
      Enum.map_join(d.ctors, "\n", fn c ->
        v = Map.fetch!(st.variants, {d.name, c.name})
        {:ok, fields} = ctor_fields(st.book, d.name, c.name)
        variant_decl(v, fields, st)
      end)

    ctors =
      d.ctors
      |> Enum.filter(&MapSet.member?(used, {d.name, &1.name}))
      |> Enum.map_join("\n\n", &ctor_fn(&1, d.name, type, st))

    [
      """
      pub const #{type} = union(enum) {
      #{variants}
      };
      """
      |> String.trim(),
      ctors
    ]
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n\n")
  end

  defp variant_decl(name, [], _st), do: "    #{name},"

  defp variant_decl(name, [lay], st), do: "    #{name}: #{pty(lay, st)},"

  defp variant_decl(name, fields, st) do
    inner =
      fields
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {lay, i} -> "        #{g("f", i)}: #{pty(lay, st)}," end)

    """
        #{name}: struct {
    #{inner}
        },\
    """
  end

  defp ctor_fn(c, dname, type, st) do
    fn_name = Map.fetch!(st.ctor_fns, {dname, c.name})
    v = Map.fetch!(st.variants, {dname, c.name})
    {:ok, fields} = ctor_fields(st.book, dname, c.name)

    if fields == [] do
      val = Map.fetch!(st.val_names, {dname, c.name})

      """
      const #{val}: #{type} = .#{v};

      fn #{fn_name}() *const #{type} {
          return &#{val};
      }
      """
      |> String.trim()
    else
      scope = Name.open(st.globals) |> Name.see(al())

      {bound, _} =
        Enum.map_reduce(Enum.with_index(fields), scope, fn {lay, i}, scope ->
          {rn, scope} = Name.bind(g("a", i), scope)
          {{rn, lay}, scope}
        end)

      args =
        ["#{al()}: #{alloc_ty()}"] ++
          Enum.map(bound, fn {rn, lay} -> "#{rn}: #{pty(lay, st)}" end)

      build =
        case bound do
          [{rn, _lay}] ->
            ".#{v} = #{rn}"

          _ ->
            inner =
              bound
              |> Enum.with_index()
              |> Enum.map_join(", ", fn {{rn, _lay}, i} -> ".#{g("f", i)} = #{rn}" end)

            ".#{v} = .{ #{inner} }"
        end

      """
      fn #{fn_name}(#{Enum.join(args, ", ")}) !*const #{type} {
          const #{g("p")} = try #{al()}.create(#{type});
          #{g("p")}.* = .{ #{build} };
          return #{g("p")};
      }
      """
      |> String.trim()
    end
  end

  defp atom_enum(atoms) when map_size(atoms) == 0, do: ""

  defp atom_enum(atoms) do
    vars = Enum.map_join(atoms, "\n", fn {_name, v} -> "    #{v}," end)

    """
    pub const #{g("Atom")} = union(enum) {
    #{vars}
    };
    """
    |> String.trim()
  end

  defp atom_values(used, atoms, vals) do
    used
    |> Enum.map(fn name ->
      v = Map.fetch!(atoms, name)
      val = Map.fetch!(vals, name)
      "const #{val}: #{g("Atom")} = .#{v};"
    end)
    |> Enum.join("\n")
  end

  defp env_structs(funs, st) do
    funs
    |> Enum.map(fn fun ->
      case Map.fetch(st.step_info, fun.name) do
        {:ok, %{cap_count: n, env: env}} when n > 0 ->
          fields =
            fun.params
            |> Enum.take(n)
            |> Enum.with_index()
            |> Enum.map_join("\n", fn {{_name, lay}, i} ->
              "    #{g("f", i)}: #{pty(lay, st)},"
            end)

          "const #{env} = struct {\n#{fields}\n};"

        _ ->
          ""
      end
    end)
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n\n")
  end

  defp needs_no_env?(step_info) do
    Enum.any?(step_info, fn {_name, info} -> info.cap_count == 0 end)
  end

  # Every data declaration is emitted, so a field of `Nat × Nat` or a
  # stream needs the pair and stream runtimes even when no run mentions them.
  defp runtime_flags(scan, funs, book) do
    fields = data_field_lays(book)
    stream? = scan.stream or lays?(funs, &has_stream?/1) or Enum.any?(fields, &has_stream?/1)
    pair? = stream? or scan.pair or lays?(funs, &has_pair?/1) or Enum.any?(fields, &has_pair?/1)

    bytes? =
      lays?(funs, &(&1 == :slice)) or Enum.any?(fields, &(&1 == :slice)) or
        Enum.any?(funs, &zig_bytes?(&1.body))

    %{pair: pair?, stream: stream?, bytes: bytes?}
  end

  defp runtime(flags) do
    parts = [
      nat_runtime(),
      unit_runtime(),
      erase_runtime(),
      if(flags.pair, do: pair_runtime(), else: ""),
      if(flags.stream, do: stream_runtime(), else: ""),
      if(flags.bytes, do: bytes_runtime(), else: "")
    ]

    parts |> Enum.reject(&(&1 == "")) |> Enum.join("\n\n")
  end

  defp data_field_lays(book) do
    book
    |> data_decls()
    |> Enum.flat_map(fn d ->
      Enum.flat_map(d.ctors, fn c ->
        case ctor_fields(book, d.name, c.name) do
          {:ok, fields} -> fields
          :error -> []
        end
      end)
    end)
  end

  defp lays?(funs, pred) do
    Enum.any?(funs, fn fun ->
      pred.(fun.ret) or Enum.any?(fun.params, fn {_n, lay} -> pred.(lay) end)
    end)
  end

  defp has_pair?({:pair, _, _}), do: true
  defp has_pair?({:stream, a}), do: has_pair?(a)
  defp has_pair?(_), do: false

  defp has_stream?({:stream, _}), do: true
  defp has_stream?({:pair, a, b}), do: has_stream?(a) or has_stream?(b)
  defp has_stream?(_), do: false

  defp nat_runtime do
    nat = g("Nat")
    zero = g("tag_zero")
    suc = g("tag_suc")
    val = g("val_Nat_zero")
    n = g("n")
    p = g("p")
    k = g("k")
    i = g("i")
    cur = g("cur")

    """
    pub const #{nat} = union(enum) {
        #{zero},
        #{suc}: *const #{nat},
    };

    const #{val}: #{nat} = .#{zero};

    pub fn #{g("zero")}() *const #{nat} {
        return &#{val};
    }

    pub fn #{g("suc")}(#{al()}: #{alloc_ty()}, #{n}: *const #{nat}) !*const #{nat} {
        const #{p} = try #{al()}.create(#{nat});
        #{p}.* = .{ .#{suc} = #{n} };
        return #{p};
    }

    pub fn #{g("from_u64")}(#{al()}: #{alloc_ty()}, #{k}: u64) !*const #{nat} {
        var #{n} = #{g("zero")}();
        var #{i}: u64 = #{k};
        while (#{i} > 0) {
            #{n} = try #{g("suc")}(#{al()}, #{n});
            #{i} -= 1;
        }
        return #{n};
    }

    pub fn #{g("to_u64")}(#{n}: *const #{nat}) u64 {
        var #{k}: u64 = 0;
        var #{cur} = #{n};
        while (true) {
            switch (#{cur}.*) {
                .#{zero} => return #{k},
                .#{suc} => |#{p}| {
                    #{k} += 1;
                    #{cur} = #{p};
                },
            }
        }
    }
    """
    |> String.trim()
  end

  defp unit_runtime do
    unit = g("Unit")
    tt = g("tag_tt")
    val = g("val_Unit_tt")

    """
    pub const #{unit} = union(enum) { #{tt} };

    const #{val}: #{unit} = .#{tt};

    pub fn #{g("tt")}() *const #{unit} {
        return &#{val};
    }
    """
    |> String.trim()
  end

  defp erase_runtime do
    p = g("p")
    t = g("T")

    """
    pub fn #{g("erase")}(#{p}: anytype) *const anyopaque {
        return @ptrCast(#{p});
    }

    pub fn #{g("reveal")}(comptime #{t}: type, #{p}: *const anyopaque) *const #{t} {
        return @ptrCast(@alignCast(#{p}));
    }
    """
    |> String.trim()
  end

  defp pair_runtime do
    pair = g("Pair")
    fst = g("field_fst")
    snd = g("field_snd")
    p = g("p")

    """
    pub const #{pair} = struct {
        #{fst}: *const anyopaque,
        #{snd}: *const anyopaque,
    };

    pub fn #{g("pair")}(#{al()}: #{alloc_ty()}, #{fst}: *const anyopaque, #{snd}: *const anyopaque) !*const #{pair} {
        const #{p} = try #{al()}.create(#{pair});
        #{p}.* = .{ .#{fst} = #{fst}, .#{snd} = #{snd} };
        return #{p};
    }
    """
    |> String.trim()
  end

  defp stream_runtime do
    step_ty = g("Step")
    stream = g("Stream")
    pair = g("Pair")
    seed_f = g("field_seed")
    env_f = g("field_env")
    step_f = g("field_step")
    p = g("p")

    """
    pub const #{step_ty} = *const fn (#{al()}: #{alloc_ty()}, #{g("env")}: *const anyopaque, #{g("seed")}: *const anyopaque) anyerror!*const #{pair};

    pub const #{stream} = struct {
        #{seed_f}: *const anyopaque,
        #{env_f}: *const anyopaque,
        #{step_f}: #{step_ty},
    };

    pub fn #{g("stream_new")}(#{al()}: #{alloc_ty()}, #{g("seed")}: *const anyopaque, #{g("env")}: *const anyopaque, #{step_f}: #{step_ty}) !*const #{stream} {
        const #{p} = try #{al()}.create(#{stream});
        #{p}.* = .{ .#{seed_f} = #{g("seed")}, .#{env_f} = #{g("env")}, .#{step_f} = #{step_f} };
        return #{p};
    }
    """
    |> String.trim()
  end

  defp scan_funs(funs) do
    Enum.reduce(
      funs,
      %{ctors: MapSet.new(), atoms: MapSet.new(), steps: %{}, pair: false, stream: false},
      fn fun, acc ->
        scan_tm(fun.body, acc)
      end
    )
  end

  defp scan_tm({:pair, a, b}, acc), do: scan_tm(b, scan_tm(a, %{acc | pair: true}))

  defp scan_tm({:uncons, e}, acc), do: scan_tm(e, %{acc | pair: true, stream: true})

  defp scan_tm({:letp, _a, _b, e, body}, acc) do
    scan_tm(body, scan_tm(e, %{acc | pair: true}))
  end

  defp scan_tm({:stream, seed, caps, name}, acc) do
    acc = %{acc | stream: true, pair: true}
    acc = note_step(acc, name, length(caps))
    acc = scan_tm(seed, acc)
    Enum.reduce(caps, acc, fn {_n, tm}, acc -> scan_tm(tm, acc) end)
  end

  defp scan_tm({:con, "Atom", name, []}, acc) do
    %{acc | atoms: MapSet.put(acc.atoms, name)}
  end

  defp scan_tm({:con, d, c, args}, acc) do
    acc = %{acc | ctors: MapSet.put(acc.ctors, {d, c})}
    Enum.reduce(args, acc, &scan_tm/2)
  end

  defp scan_tm({:match, s, arms}, acc) do
    acc = scan_tm(s, acc)

    Enum.reduce(arms, acc, fn {:arm, _, _, body}, acc -> scan_tm(body, acc) end)
  end

  defp scan_tm(tm, acc) when is_tuple(tm) do
    tm |> Tuple.to_list() |> Enum.reduce(acc, &scan_tm/2)
  end

  defp scan_tm(tm, acc) when is_list(tm), do: Enum.reduce(tm, acc, &scan_tm/2)
  defp scan_tm(_tm, acc), do: acc

  defp note_step(acc, name, n) do
    case Map.fetch(acc.steps, name) do
      :error -> %{acc | steps: Map.put(acc.steps, name, n)}
      {:ok, ^n} -> acc
      {:ok, _} -> acc
    end
  end

  defp zig_bytes?(t) when is_tuple(t) do
    case t do
      {:byt, _} -> true
      {:bcat, _, _} -> true
      {:blen, _} -> true
      {:beq, _, _} -> true
      {:bsub, _, _, _} -> true
      {:bget, _, _} -> true
      {:bunc, _} -> true
      {:btil, _, _} -> true
      {:baft, _, _} -> true
      {:bfold, _, _, _, _} -> true
      {:sbytes, _} -> true
      other -> other |> Tuple.to_list() |> Enum.any?(&zig_bytes?/1)
    end
  end

  defp zig_bytes?(t) when is_list(t), do: Enum.any?(t, &zig_bytes?/1)
  defp zig_bytes?(:slice), do: true
  defp zig_bytes?(_), do: false

  defp bytes_runtime do
    sl = g("slice")
    empty = g("empty_bytes")
    emp = g("slice_empty")
    wrap = g("slice_of")
    sub = g("slice_sub")
    eq = g("slice_eq")
    cat = g("bytes_cat")
    get = g("slice_get")
    til = g("slice_until")
    aft = g("slice_after")
    stdlib = stdn()

    """
    pub const #{sl} = extern struct { p: [*]const u8, n: usize };

    const #{empty} = [_]u8{0};

    fn #{emp}() #{sl} {
        return .{ .p = @as([*]const u8, @ptrCast(&#{empty})), .n = 0 };
    }

    pub fn #{wrap}(p: [*c]const u8, n: usize) #{sl} {
        if (n == 0 or p == null) return #{emp}();
        return .{ .p = p, .n = n };
    }

    fn #{sub}(s: #{sl}, off: u64, len: u64) #{sl} {
        const sn: u64 = s.n;
        if (off > sn or len > sn - off) return #{emp}();
        return .{ .p = s.p + @as(usize, @intCast(off)), .n = @as(usize, @intCast(len)) };
    }

    fn #{eq}(a: #{sl}, b: #{sl}) u8 {
        if (a.n != b.n) return 0;
        if (a.n == 0) return 1;
        if (#{stdlib}.mem.eql(u8, a.p[0..a.n], b.p[0..b.n])) return 1;
        return 0;
    }

    fn #{cat}(#{al()}: #{alloc_ty()}, a: #{sl}, b: #{sl}) !#{sl} {
        const ov = @addWithOverflow(a.n, b.n);
        if (ov[1] != 0) return error.Overflow;
        const n = ov[0];
        if (n == 0) return #{emp}();
        const buf = try #{al()}.alloc(u8, n);
        if (a.n != 0) @memcpy(buf[0..a.n], a.p[0..a.n]);
        if (b.n != 0) @memcpy(buf[a.n..n], b.p[0..b.n]);
        return .{ .p = buf.ptr, .n = n };
    }

    fn #{get}(s: #{sl}, i: u64) ?u8 {
        if (i >= @as(u64, s.n)) return null;
        return s.p[@as(usize, @intCast(i))];
    }

    fn #{til}(s: #{sl}, b: u8) #{sl} {
        var i: usize = 0;
        while (i < s.n) {
            if (s.p[i] == b) return .{ .p = s.p, .n = i };
            i += 1;
        }
        return s;
    }

    fn #{aft}(s: #{sl}, b: u8) #{sl} {
        var i: usize = 0;
        while (i < s.n) {
            if (s.p[i] == b) return .{ .p = s.p + i + 1, .n = s.n - i - 1 };
            i += 1;
        }
        return #{emp}();
    }
    """
    |> String.trim()
  end
end

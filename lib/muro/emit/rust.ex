defmodule Muro.Emit.Rust do
  @moduledoc """
  Emit a closed run book to Rust. Specs and evidence are omitted.
  Run bodies are the image from `Muro.IR`.

  The text is what `rustc` translates. A refusal is the elaboration's:
  `c:lambda`, `c:machine`, `c:stream`, `c:erased`,
  `c:unboxed`, `c:unsupported`. A string is `muro__str`, a `#[repr(C)]`
  pointer and octet length. An `unboxed data` value is the enum.
  It is not wrapped in `Rc`. An `Opt` of that value is `c:unboxed`.

  Identifiers come from `Muro.Emit.Name`. A source name is spelled there.
  A helper, a step, a constructor argument, and a temporary are generated
  there. The two spellings share no identifier. A binder is claimed there
  against every name visible in its scope, including type names.
  """

  alias Muro.{Ast, Emit, IR}
  alias Muro.Emit.Name

  @rust_keywords ~w(
    as async await break const continue crate dyn else enum extern false
    fn for if impl in let loop match mod move mut pub ref return self Self
    static struct super trait true type unsafe use where while abstract
    become box do final macro override priv typeof unsized virtual yield try
    gen
  ) |> MapSet.new()

  # Primitive types. A `struct` of one of these names shadows the primitive
  # in the type namespace, which is where `muro__from_u64` reads `u64`.
  @primitives ~w(
    bool char str
    i8 i16 i32 i64 i128 isize
    u8 u16 u32 u64 u128 usize
    f16 f32 f64 f128
  ) |> MapSet.new()

  # Prelude names the runtime spells. Derives and `dyn Fn` are written
  # with a full path; reserving the name keeps a source struct off them.
  @prelude ~w(Clone Copy PartialEq Eq Fn) |> MapSet.new()

  @forbidden @rust_keywords |> MapSet.union(@primitives) |> MapSet.union(@prelude)

  @doc false
  def source_id(name) when is_binary(name), do: spell(name)

  @doc false
  def generated_samples do
    tags = ~w(
      Nat NatNode Unit Erased Pair Stream Atom
      zero suc erase reveal from_u64 to_u64
      field_seed field_step tag_zero tag_suc
      seed n p k s t c x e rc v
    )

    Enum.map(tags, &Name.gen/1) ++ [Name.gen("step", 0), Name.gen("a", 0), Name.gen("node_List")]
  end

  defp spell(name), do: Name.spell(name, @forbidden)
  defp g(tag), do: Name.gen(tag)
  defp g(tag, n), do: Name.gen(tag, n)
  defp claim(base, used), do: Name.claim(base, used)

  @doc """
  Render `book` as one Rust source file for a stem such as `half_ok`.
  """
  def render(book, stem) when is_list(book) and is_binary(stem) do
    case IR.elaborate(book) do
      {:ok, funs} ->
        with :ok <- Emit.refuse_may_fail(book),
             :ok <- Emit.refuse_unboxed_opt(book, funs) do
          compile(book, funs, stem)
        end

      {:error, reason} ->
        {:error, reason}
    end
  end

  @doc """
  Names, signatures, layouts, and clause heads of the Rust file
  `render/2` writes. Each head is the one `fun_open/2` places in front
  of that run's body. No source is written.
  """
  def outline(book, _stem) when is_list(book) do
    case IR.elaborate(book) do
      {:ok, funs} ->
        with :ok <- Emit.refuse_may_fail(book),
             :ok <- Emit.refuse_unboxed_opt(book, funs),
             {:ok, st0, groups} <- image(book, funs) do
          user = Enum.map(groups, fn {fun, _} -> fun end)

          signatures =
            Enum.map(user, fn fun ->
              {head, _env, st, params} = fun_open(fun, st0)

              %{
                source: fun.name,
                name: emitted_name(fun, st),
                layout: fun.ret,
                param_layouts: Enum.map(fun.params, fn {_n, lay} -> lay end),
                params: Enum.map(params, fn {_src, rn, _lay} -> rn end),
                ret: rty(fun.ret, st),
                export: fun.export,
                head: head
              }
            end)

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
             clauses: Enum.map(signatures, & &1.head)
           }}
        end

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp compile(book, funs, _stem) do
    with {:ok, st0, _groups} <- image(book, funs) do
      compile_book(book, funs, st0)
    end
  end

  defp image(book, funs) do
    with {:ok, groups, step_map} <- Emit.partition_funs(funs, Emit.run_defs(book)) do
      user_funs = Enum.map(groups, fn {fun, _} -> fun end)
      steps = Enum.flat_map(groups, fn {_fun, ss} -> ss end)
      spell = &spell/1
      {types, taken} = type_names(book, MapSet.new(), spell)
      {ctor_fns, taken} = ctor_fn_names(book, taken, spell)
      variants = variant_names(book)
      atoms = atom_variants(book)
      {names, taken} = names_of(book, taken, spell)
      {step_names, taken} = name_steps(steps, taken)
      file_scope = Name.open(taken)

      st0 = %{
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
        file_scope: file_scope
      }

      {:ok, st0, groups}
    end
  end

  defp compile_book(book, funs, st0) do
    types = st0.types
    variants = st0.variants
    ctor_fns = st0.ctor_fns
    atoms = st0.atoms
    file_scope = st0.file_scope

    with {:ok, fns} <- emit_funs(funs, st0) do
      parts = [
        "// generated by muro — do not edit",
        "#![allow(dead_code, unused_variables, non_snake_case, non_camel_case_types, unused_parens)]",
        runtime(),
        bytes_runtime(book, funs),
        string_runtime(book, funs),
        atom_enum(atoms),
        data_items(book, types, variants, ctor_fns, file_scope),
        Enum.join(fns, "\n\n")
      ]

      {:ok, join(parts)}
    end
  end

  defp emit_funs(funs, st0) do
    Enum.reduce_while(funs, {:ok, []}, fn fun, {:ok, acc} ->
      case emit_fun(fun, st0) do
        {:ok, text} -> {:cont, {:ok, acc ++ [text]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp emit_fun(fun, st0) do
    {head, env, st, _params} = fun_open(fun, st0)

    with {:ok, {lines, expr, lay, _st}} <- emit_tm(fun.body, env, st) do
      body = fn_body(lines, coerce(expr, lay, fun.ret, st))
      {:ok, "#{head} {\n#{body}\n}"}
    end
  end

  defp fun_open(fun, st0) do
    {params, scope} =
      Enum.reduce(fun.params, {[], st0.file_scope}, fn {pname, lay}, {acc, scope} ->
        {rn, scope} = Name.bind(spell(pname), scope)
        {acc ++ [{pname, rn, lay}], scope}
      end)

    env = Enum.reduce(params, [], fn {src, rn, lay}, env -> [{src, rn, lay} | env] end)
    st = Map.merge(st0, %{n: 0, scope: scope})
    args = Enum.map_join(params, ", ", fn {_src, rn, lay} -> "#{rn}: #{rty(lay, st)}" end)
    vis = if fun.export, do: "pub ", else: ""
    ret = rty(fun.ret, st)
    name = emitted_name(fun, st)
    {"#{vis}fn #{name}(#{args}) -> #{ret}", env, st, params}
  end

  defp emitted_name(fun, st) do
    map = if MapSet.member?(st.step_ids, fun), do: st.step_names, else: st.names
    Map.fetch!(map, fun.name)
  end

  defp emit_tm({:var, name}, env, st) do
    case lookup(env, name) do
      {rn, lay} -> {:ok, {[], "#{rn}.clone()", lay, st}}
      nil -> {:error, "c:unsupported"}
    end
  end

  defp emit_tm(:ze, _env, st), do: {:ok, {[], "#{g("zero")}()", :nat, st}}
  defp emit_tm(:tt, _env, st), do: {:ok, {[], g("Unit"), :unit, st}}
  defp emit_tm(:abort, _env, st), do: {:ok, {[], "::std::process::abort()", :never, st}}

  defp emit_tm({:su, u}, env, st) do
    with {:ok, {lines, ex, lay, st}} <- emit_tm(u, env, st) do
      {:ok, {lines, "#{g("suc")}(#{coerce(ex, lay, :nat, st)})", :nat, st}}
    end
  end

  defp emit_tm({:call, name, args}, env, st) do
    case Map.fetch(st.funs, name) do
      :error ->
        {:error, "c:unsupported"}

      {:ok, fun} ->
        with {:ok, {lines, exprs, lays, st}} <- emit_list(args, env, st) do
          params = Enum.map(fun.params, fn {_n, lay} -> lay end)

          if length(params) != length(exprs) do
            {:error, "c:unsupported"}
          else
            coerced =
              Enum.map(Enum.zip([exprs, lays, params]), fn {ex, from, to} ->
                coerce(ex, from, to, st)
              end)

            call = "#{Map.fetch!(st.names, name)}(#{Enum.join(coerced, ", ")})"
            {:ok, {lines, call, fun.ret, st}}
          end
        end
    end
  end

  defp emit_tm({:con, "Atom", name, []}, _env, st) do
    case Map.fetch(st.atoms, name) do
      {:ok, variant} -> {:ok, {[], "#{g("Atom")}::#{variant}", {:data, "Atom"}, st}}
      :error -> {:error, "c:unsupported"}
    end
  end

  defp emit_tm({:con, dname, cname, args}, env, st) do
    with {:ok, {lines, exprs, lays, st}} <- emit_list(args, env, st) do
      fields = ctor_fields(st.book, cname)
      fn_name = Map.get(st.ctor_fns, {dname, cname})

      cond do
        fn_name == nil ->
          {:error, "c:unsupported"}

        length(fields) != length(exprs) ->
          {:error, "c:unsupported"}

        true ->
          coerced =
            Enum.map(Enum.zip([exprs, lays, fields]), fn {ex, from, to} ->
              coerce(ex, from, to, st)
            end)

          {:ok, {lines, "#{fn_name}(#{Enum.join(coerced, ", ")})", {:data, dname}, st}}
      end
    end
  end

  # An erased constructor field, marked `:erased`. The placeholder is
  # unit, and the payload is ignored. A zero passed under a spec alias
  # is bound at the argument's layout, so this clause does not see it.
  defp emit_tm({:let, name, :erased, _val, body}, env, st) do
    {rn, st} = local(st, spell(name))

    with {:ok, {lines, ex, lay, st}} <- emit_tm(body, [{name, rn, :opaque} | env], st) do
      {:ok, {["let #{rn} = #{g("erase")}(());" | lines], ex, lay, st}}
    end
  end

  defp emit_tm({:let, _name, _lay, val, :abort}, env, st) do
    with {:ok, {lines, ex, _lay, st}} <- emit_tm(val, env, st) do
      {:ok, {lines ++ ["let _ = #{ex};"], "::std::process::abort()", :never, st}}
    end
  end

  defp emit_tm({:let, name, lay, val, body}, env, st) do
    with {:ok, {vlines, vex, vlay, st}} <- emit_tm(val, env, st) do
      {rn, st} = local(st, spell(name))
      bound = coerce(vex, vlay, lay, st)

      with {:ok, {blines, bex, blay, st}} <- emit_tm(body, [{name, rn, lay} | env], st) do
        {:ok, {vlines ++ ["let #{rn} = #{bound};"] ++ blines, bex, blay, st}}
      end
    end
  end

  defp emit_tm({:pair, a, b}, env, st) do
    with {:ok, {al, ae, alay, st}} <- emit_tm(a, env, st),
         {:ok, {bl, be, blay, st}} <- emit_tm(b, env, st) do
      if unboxed_lay?(st.book, alay) or unboxed_lay?(st.book, blay) do
        {:error, "c:unboxed"}
      else
        expr = "#{g("Pair")}(#{coerce(ae, alay, :opaque, st)}, #{coerce(be, blay, :opaque, st)})"
        {:ok, {al ++ bl, expr, {:pair, alay, blay}, st}}
      end
    end
  end

  defp emit_tm({:letp, a, b, e, body}, env, st) do
    with {:ok, {elines, eex, elay, st}} <- emit_tm(e, env, st) do
      {s, st} = local(st, g("p"))
      {ra, st} = local(st, spell(a))
      {rb, st} = local(st, spell(b))
      {la, lb} = pair_halves(elay)
      env1 = [{b, rb, lb}, {a, ra, la} | env]

      with {:ok, {blines, bex, blay, st}} <- emit_tm(body, env1, st) do
        lines =
          elines ++
            [
              "let #{s} = #{as_pair(eex, elay, st)};",
              bind_half(ra, "#{s}.0", la, st),
              bind_half(rb, "#{s}.1", lb, st)
            ] ++ blines

        {:ok, {lines, bex, blay, st}}
      end
    end
  end

  defp emit_tm({:uncons, e}, env, st) do
    with {:ok, {lines, ex, elay, st}} <- emit_tm(e, env, st) do
      {s, st} = local(st, g("s"))
      {p, st} = local(st, g("p"))
      {t, st} = local(st, g("t"))

      more = [
        "let #{s} = #{as_stream(ex, elay, st)};",
        "let #{p} = (#{s}.#{g("field_step")})(#{s}.#{g("field_seed")}.clone());",
        "let #{t} = #{g("Stream")} { #{g("field_seed")}: #{p}.1.clone(), #{g("field_step")}: #{s}.#{g("field_step")}.clone() };"
      ]

      expr = "#{g("Pair")}(#{p}.0.clone(), #{g("erase")}(#{t}))"
      {:ok, {lines ++ more, expr, uncons_lay(elay), st}}
    end
  end

  defp emit_tm({:stream, seed, caps, step_name}, env, st) do
    case Map.fetch(st.steps, step_name) do
      :error ->
        {:error, "c:unsupported"}

      {:ok, step} ->
        with {:ok, {slines, sex, slay, st}} <- emit_tm(seed, env, st),
             {:ok, {clines, cexs, clays, st}} <- emit_caps(caps, env, st) do
          if unboxed_lay?(st.book, slay) or Enum.any?(clays, &unboxed_lay?(st.book, &1)) do
            {:error, "c:unboxed"}
          else
            {cap_lays, seed_lays} =
              Enum.split(Enum.map(step.params, &elem(&1, 1)), length(caps))

            {cap_locals, cap_binds, st} =
              Enum.reduce(cexs, {[], [], st}, fn ex, {locs, binds, st} ->
                {loc, st} = local(st, g("c"))
                {locs ++ [loc], binds ++ ["let #{loc} = #{ex};"], st}
              end)

            call = step_call(step_name, cap_locals, clays, cap_lays, seed_lays, st)
            expr = stream_expr(coerce(sex, slay, :opaque, st), call)

            lay =
              case seed_lays do
                [dlay] -> {:stream, dlay}
                _ -> {:stream, slay}
              end

            {:ok, {slines ++ clines ++ cap_binds, expr, lay, st}}
          end
        end
    end
  end

  defp emit_tm({:match, scrut, arms}, env, st) do
    with {:ok, {lines, ex, lay, st}} <- emit_tm(scrut, env, st) do
      kind = match_kind(lay, arms, st.book)
      ex = shown_scrut(ex, lay, kind, st)

      with {:ok, expr, rlay, st} <- emit_match(scrut_lay(kind), ex, arms, env, st) do
        {:ok, {lines, expr, rlay, st}}
      end
    end
  end

  defp emit_tm({:wrd, k, op, args}, env, st) do
    with {:ok, {lines, exprs, lays, st}} <- emit_list(args, env, st) do
      case word_rust(k, op, exprs, lays, st) do
        {:ok, {more, expr, lay, st}} -> {:ok, {lines ++ more, expr, lay, st}}
        {:error, _} = err -> err
      end
    end
  end

  defp emit_tm({:byt, bin}, _env, st) when is_binary(bin) do
    if bin == "" do
      {:ok, {[], "#{g("slice_empty")}()", :slice, st}}
    else
      {tmp, st} = local(st, g("lit"))
      bytes = bin |> :binary.bin_to_list() |> Enum.map_join(", ", &Integer.to_string/1)
      lines = ["let #{tmp}: &'static [u8] = &[#{bytes}];"]
      expr = "#{g("slice")} { p: #{tmp}.as_ptr(), n: #{tmp}.len() }"
      {:ok, {lines, expr, :slice, st}}
    end
  end

  defp emit_tm({:bcat, a, b}, env, st) do
    with {:ok, {la, ea, _, st}} <- emit_tm(a, env, st),
         {:ok, {lb, eb, _, st}} <- emit_tm(b, env, st) do
      {:ok, {la ++ lb, "#{g("bytes_cat")}(#{ea}, #{eb})", :slice, st}}
    end
  end

  defp emit_tm({:blen, a}, env, st) do
    with {:ok, {ls, ex, _, st}} <- emit_tm(a, env, st) do
      {:ok, {ls, "(#{ex}.n as u64)", :u64, st}}
    end
  end

  defp emit_tm({:beq, a, b}, env, st) do
    with {:ok, {la, ea, _, st}} <- emit_tm(a, env, st),
         {:ok, {lb, eb, _, st}} <- emit_tm(b, env, st) do
      {:ok, {la ++ lb, "#{g("slice_eq")}(#{ea}, #{eb})", :wbool, st}}
    end
  end

  defp emit_tm({:bsub, s, off, len}, env, st) do
    with {:ok, {ls, es, _, st}} <- emit_tm(s, env, st),
         {:ok, {lo, eo, _, st}} <- emit_tm(off, env, st),
         {:ok, {ln, en, _, st}} <- emit_tm(len, env, st) do
      {:ok, {ls ++ lo ++ ln, "#{g("slice_sub")}(#{es}, #{eo}, #{en})", :slice, st}}
    end
  end

  defp emit_tm({:bget, s, i}, env, st) do
    with {:ok, {ls, es, _, st}} <- emit_tm(s, env, st),
         {:ok, {li, ei, _, st}} <- emit_tm(i, env, st) do
      {:ok, {ls ++ li, "#{g("slice_get")}(#{es}, #{ei})", {:opt, :u8}, st}}
    end
  end

  defp emit_tm({:btil, s, b}, env, st) do
    with {:ok, {ls, es, _, st}} <- emit_tm(s, env, st),
         {:ok, {lb, eb, _, st}} <- emit_tm(b, env, st) do
      {:ok, {ls ++ lb, "#{g("slice_until")}(#{es}, #{eb})", :slice, st}}
    end
  end

  defp emit_tm({:baft, s, b}, env, st) do
    with {:ok, {ls, es, _, st}} <- emit_tm(s, env, st),
         {:ok, {lb, eb, _, st}} <- emit_tm(b, env, st) do
      {:ok, {ls ++ lb, "#{g("slice_after")}(#{es}, #{eb})", :slice, st}}
    end
  end

  defp emit_tm({:sbytes, s}, env, st) do
    with {:ok, {ls, ex, lay, st}} <- emit_tm(s, env, st) do
      {:ok, {ls, "#{g("str_bytes")}(#{as_str(ex, lay, st)})", :slice, st}}
    end
  end

  defp emit_tm({:bunc, s}, env, st) do
    nothing = Map.get(st.ctor_fns, {"Maybe", "nothing"})
    just = Map.get(st.ctor_fns, {"Maybe", "just"})

    if nothing == nil or just == nil do
      {:error, "c:unsupported"}
    else
      with {:ok, {lines, ex, _, st}} <- emit_tm(s, env, st) do
        {cur, st} = local(st, nil)
        {byte, st} = local(st, nil)
        {rest, st} = local(st, nil)
        sl = g("slice")
        pair = g("Pair")
        erase = g("erase")

        lines = lines ++ ["let #{cur} = #{ex};"]

        expr = """
        if #{cur}.n == 0 { #{nothing}() } else {
            let #{byte}: u8 = unsafe { *#{cur}.p };
            let #{rest} = #{sl} { p: unsafe { #{cur}.p.add(1) }, n: #{cur}.n - 1 };
            #{just}(#{erase}(#{pair}(#{erase}(#{byte}), #{erase}(#{rest}))))
        }
        """

        {:ok, {lines, String.trim(expr), {:data, "Maybe"}, st}}
      end
    end
  end

  defp emit_tm({:bfold, step, caps, z, s}, env, st) do
    cap_terms = Enum.map(caps, fn {_name, tm} -> tm end)

    with {:ok, {cl, ces, _, st}} <- emit_list(cap_terms, env, st),
         {:ok, {zl, ze, zlay, st}} <- emit_tm(z, env, st),
         {:ok, {sl, se, _, st}} <- emit_tm(s, env, st) do
      {acc, st} = local(st, nil)
      {cur, st} = local(st, nil)
      {byte, st} = local(st, nil)
      {rest, st} = local(st, nil)
      fname = Map.fetch!(st.step_names, step)
      args = Enum.join(ces ++ [byte, rest, acc], ", ")
      slice = g("slice")

      more = [
        "let mut #{acc} = #{ze};",
        "let mut #{cur} = #{se};",
        "while #{cur}.n > 0 {",
        "    let #{byte}: u8 = unsafe { *#{cur}.p };",
        "    let #{rest} = #{slice} { p: unsafe { #{cur}.p.add(1) }, n: #{cur}.n - 1 };",
        "    #{acc} = #{fname}(#{args});",
        "    #{cur} = #{rest};",
        "}"
      ]

      {:ok, {cl ++ zl ++ sl ++ more, acc, zlay, st}}
    end
  end

  defp emit_tm({:str, bin}, _env, st) when is_binary(bin) do
    if bin == "" do
      {:ok, {[], "#{g("str_empty")}()", :string, st}}
    else
      {tmp, st} = local(st, g("lit"))
      bytes = bin |> :binary.bin_to_list() |> Enum.map_join(", ", &Integer.to_string/1)
      lines = ["let #{tmp}: &'static [u8] = &[#{bytes}];"]
      expr = "#{g("str")} { p: #{tmp}.as_ptr(), n: #{tmp}.len() }"
      {:ok, {lines, expr, :string, st}}
    end
  end

  defp emit_tm({:scat, a, b}, env, st) do
    with {:ok, {la, ea, laya, st}} <- emit_tm(a, env, st),
         {:ok, {lb, eb, layb, st}} <- emit_tm(b, env, st) do
      expr = "#{g("str_cat")}(#{as_str(ea, laya, st)}, #{as_str(eb, layb, st)})"
      {:ok, {la ++ lb, expr, :string, st}}
    end
  end

  defp emit_tm({:slen, a}, env, st) do
    with {:ok, {ls, ex, lay, st}} <- emit_tm(a, env, st) do
      {:ok, {ls, "#{g("str_len")}(#{as_str(ex, lay, st)})", :nat, st}}
    end
  end

  defp emit_tm({:seq, a, b}, env, st) do
    with {:ok, {la, ea, laya, st}} <- emit_tm(a, env, st),
         {:ok, {lb, eb, layb, st}} <- emit_tm(b, env, st) do
      expr = "#{g("str_eq")}(#{as_str(ea, laya, st)}, #{as_str(eb, layb, st)})"
      {:ok, {la ++ lb, expr, :wbool, st}}
    end
  end

  defp emit_tm(_other, _env, _st), do: {:error, "c:unsupported"}

  defp as_str(ex, :string, _st), do: ex
  defp as_str(ex, _lay, st), do: coerce(ex, :opaque, :string, st)

  defp emit_list(ts, env, st) do
    Enum.reduce_while(ts, {:ok, [], [], [], st}, fn t, {:ok, lines, exprs, lays, st} ->
      case emit_tm(t, env, st) do
        {:ok, {ls, ex, lay, st}} -> {:cont, {:ok, lines ++ ls, exprs ++ [ex], lays ++ [lay], st}}
        {:error, _} = err -> {:halt, err}
      end
    end)
    |> case do
      {:ok, lines, exprs, lays, st} -> {:ok, {lines, exprs, lays, st}}
      err -> err
    end
  end

  defp emit_caps(caps, env, st) do
    emit_list(Enum.map(caps, fn {_name, tm} -> tm end), env, st)
  end

  defp emit_match(:nat, ex, [{:arm, "zero", [], z}, {:arm, "suc", [y], s}], env, st) do
    {yname, st} = local(st, spell(y))

    with {:ok, zarm, zlay, st} <- arm_expr(z, env, st),
         {:ok, sarm, slay, st} <- arm_expr(s, [{y, yname, :nat} | env], st) do
      {expr, lay} =
        finish_match(
          owned_node(ex),
          [
            {"#{g("NatNode")}::#{g("tag_zero")}", zarm, zlay},
            {"#{g("NatNode")}::#{g("tag_suc")}(#{yname})", sarm, slay}
          ],
          st
        )

      {:ok, expr, lay, st}
    end
  end

  defp emit_match({:data, "Atom"}, ex, arms, env, st) do
    with {:ok, rendered, st} <-
           reduce_arms(arms, st, fn {:arm, name, _binders, body}, st ->
             case Map.fetch(st.atoms, name) do
               {:ok, variant} ->
                 with {:ok, arm, lay, st} <- arm_expr(body, env, st) do
                   {:ok, {"#{g("Atom")}::#{variant}", arm, lay}, st}
                 end

               :error ->
                 {:error, "c:unsupported"}
             end
           end) do
      {expr, lay} = finish_match("(#{ex})", rendered, st)
      {:ok, expr, lay, st}
    end
  end

  defp emit_match({:data, dname}, ex, arms, env, st) do
    by_value = unboxed_name?(st.book, dname)
    node = if by_value, do: Map.fetch!(st.types, dname), else: node_name(dname, st)
    scrut = if by_value, do: "(#{ex})", else: owned_node(ex)

    with {:ok, rendered, st} <-
           reduce_arms(arms, st, fn {:arm, cname, binders, body}, st ->
             fields = ctor_fields(st.book, cname)
             variant = Map.get(st.variants, {dname, cname})

             cond do
               variant == nil or length(fields) != length(binders) ->
                 {:error, "c:unsupported"}

               true ->
                 {pats, env1, st} = bind_owned(binders, fields, env, st)

                 with {:ok, arm, lay, st} <- arm_expr(body, env1, st) do
                   pat =
                     if pats == [] do
                       "#{node}::#{variant}"
                     else
                       "#{node}::#{variant}(#{Enum.join(pats, ", ")})"
                     end

                   {:ok, {pat, arm, lay}, st}
                 end
             end
           end) do
      {expr, lay} = finish_match(scrut, rendered, st)
      {:ok, expr, lay, st}
    end
  end

  # WBool is bool. The match does not build an Rc.
  defp emit_match(:wbool, ex, [{:arm, "wtrue", [], t}, {:arm, "wfalse", [], f}], env, st) do
    with {:ok, tarm, tlay, st} <- arm_expr(t, env, st),
         {:ok, farm, flay, st} <- arm_expr(f, env, st) do
      {expr, lay} =
        finish_match("(#{ex})", [{"true", tarm, tlay}, {"false", farm, flay}], st)

      {:ok, expr, lay, st}
    end
  end

  # Opt is Option. An unused payload is `_`, which rustc does not warn on.
  defp emit_match({:opt, pay}, ex, [{:arm, "wsome", [y], s}, {:arm, "wnone", [], n}], env, st) do
    {pat, env1, st} =
      if rust_used?(s, y) do
        {rn, st} = local(st, spell(y))
        {"::std::option::Option::Some(#{rn})", [{y, rn, pay} | env], st}
      else
        {"::std::option::Option::Some(_)", env, st}
      end

    with {:ok, sarm, slay, st} <- arm_expr(s, env1, st),
         {:ok, narm, nlay, st} <- arm_expr(n, env, st) do
      {expr, lay} =
        finish_match(
          "(#{ex})",
          [{pat, sarm, slay}, {"::std::option::Option::None", narm, nlay}],
          st
        )

      {:ok, expr, lay, st}
    end
  end

  defp emit_match(_lay, _ex, _arms, _env, _st), do: {:error, "c:unsupported"}

  defp rust_used?(tm, name), do: rust_used?(tm, name, MapSet.new())
  defp rust_used?({:var, n}, name, bound), do: n == name and not MapSet.member?(bound, name)

  defp rust_used?({:let, n, _, v, b}, name, bound) do
    rust_used?(v, name, bound) or rust_used?(b, name, MapSet.put(bound, n))
  end

  defp rust_used?({:letp, a, b, e, body}, name, bound) do
    rust_used?(e, name, bound) or
      rust_used?(body, name, bound |> MapSet.put(a) |> MapSet.put(b))
  end

  defp rust_used?({:match, s, arms}, name, bound) do
    rust_used?(s, name, bound) or
      Enum.any?(arms, fn {:arm, _, binders, body} ->
        inner = Enum.reduce(binders, bound, &MapSet.put(&2, &1))
        rust_used?(body, name, inner)
      end)
  end

  defp rust_used?(tm, name, bound) when is_tuple(tm) do
    tm |> Tuple.to_list() |> Enum.any?(&rust_used?(&1, name, bound))
  end

  defp rust_used?(tm, name, bound) when is_list(tm) do
    Enum.any?(tm, &rust_used?(&1, name, bound))
  end

  defp rust_used?(_tm, _name, _bound), do: false

  # An alias is Erased. The arms still say Nat, Atom, or a data type,
  # the same way the C emitter's match_kind does. Reveal before the match.
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

  defp arm_expr(body, env, st) do
    with {:ok, {lines, expr, lay, st}} <- emit_tm(body, env, st) do
      {:ok, nest(lines, expr), lay, st}
    end
  end

  defp bind_owned(binders, lays, env, st) do
    Enum.reduce(Enum.zip(binders, lays), {[], env, st}, fn {bname, lay}, {pats, env, st} ->
      {rn, st} = local(st, spell(bname))
      {pats ++ [rn], [{bname, rn, lay} | env], st}
    end)
  end

  defp owned_node(ex), do: "(*((#{ex}).0)).clone()"

  defp finish_match(scrut, arms, st) do
    target = join_lay(Enum.map(arms, fn {_, _, lay} -> lay end))

    rendered =
      Enum.map_join(arms, ",\n", fn {pat, body, lay} ->
        "#{pat} => #{coerce(body, lay, target, st)}"
      end)

    expr =
      """
      match (#{scrut}) {
      #{indent(rendered, 4)},
      }
      """
      |> String.trim()

    {expr, target}
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

  defp step_call(step_name, cap_locals, from_lays, cap_lays, seed_lays, st) do
    fname = Map.fetch!(st.step_names, step_name)

    caps =
      [cap_locals, from_lays, cap_lays]
      |> Enum.zip()
      |> Enum.map(fn {loc, from, to} -> coerce("#{loc}.clone()", from, to, st) end)

    seed =
      case seed_lays do
        [] -> []
        [:opaque] -> [g("seed")]
        [lay] -> ["#{g("reveal")}::<#{rty(lay, st)}>(#{g("seed")})"]
      end

    "#{fname}(#{Enum.join(caps ++ seed, ", ")})"
  end

  defp stream_expr(seed_ex, call) do
    "#{g("Stream")} { #{g("field_seed")}: #{seed_ex}, #{g("field_step")}: ::std::rc::Rc::new(move |#{g("seed")}: #{g("Erased")}| -> #{g("Pair")} { #{call} }) }"
  end

  defp bind_half(rn, slot, :opaque, _st), do: "let #{rn} = #{slot}.clone();"

  defp bind_half(rn, slot, lay, st),
    do: "let #{rn} = #{g("reveal")}::<#{rty(lay, st)}>(#{slot}.clone());"

  defp coerce(ex, :never, _to, _st), do: ex
  defp coerce(ex, from, to, _st) when from == to, do: ex

  defp coerce("None", {:opt, _}, {:opt, pay}, st),
    do: "::std::option::Option::<#{rty(pay, st)}>::None"

  defp coerce(ex, _from, :opaque, _st), do: "#{g("erase")}(#{ex})"
  defp coerce(ex, :opaque, to, st), do: "#{g("reveal")}::<#{rty(to, st)}>(#{ex})"
  defp coerce(ex, _from, to, st), do: "#{g("reveal")}::<#{rty(to, st)}>(#{g("erase")}(#{ex}))"

  defp pair_halves({:pair, a, b}), do: {a, b}
  defp pair_halves(_), do: {:opaque, :opaque}

  defp as_pair(ex, {:pair, _, _}, _st), do: ex
  defp as_pair(ex, from, st), do: coerce(ex, from, {:pair, :opaque, :opaque}, st)

  defp as_stream(ex, {:stream, _}, _st), do: ex
  defp as_stream(ex, from, st), do: coerce(ex, from, {:stream, :opaque}, st)

  defp uncons_lay({:stream, s}), do: {:pair, :opaque, {:stream, s}}
  defp uncons_lay(_), do: {:pair, :opaque, :opaque}

  # Words are `Copy` and passed by value. `checked_div` / `checked_rem`
  # already return None for zero and for `i64::MIN / -1`. Shifts use the
  # operator only when the amount is below the width; `wrapping_shl`
  # would mask the count.
  defp word_rust(k, {:lit, k, n}, [], _lays, st) do
    {:ok, {[], r_lit(k, n), k, st}}
  end

  defp word_rust(_k, true, [], _lays, st), do: {:ok, {[], "true", :wbool, st}}
  defp word_rust(_k, false, [], _lays, st), do: {:ok, {[], "false", :wbool, st}}
  defp word_rust(_k, :none, [], _lays, st), do: {:ok, {[], "None", {:opt, :opaque}, st}}

  defp word_rust(k, {:of, k}, [nat], _lays, st) do
    acc = "#{g("to_u64")}(&#{nat})"

    expr =
      case k do
        :u8 -> "(#{acc} as u8)"
        :u32 -> "(#{acc} as u32)"
        :u64 -> acc
        :i64 -> "(#{acc} as i64)"
      end

    {:ok, {[], expr, k, st}}
  end

  defp word_rust(_k, :ton, [x], _lays, st) do
    {:ok, {[], "#{g("from_u64")}(#{x} as u64)", :nat, st}}
  end

  defp word_rust(k, op, [x, y], _lays, st) when op in [:add, :sub, :mul] do
    name = %{add: "wrapping_add", sub: "wrapping_sub", mul: "wrapping_mul"}
    {:ok, {[], "#{x}.#{name[op]}(#{y})", k, st}}
  end

  defp word_rust(k, op, [x, y], _lays, st) when op in [:and, :or, :xor] do
    sym = %{and: "&", or: "|", xor: "^"}
    {:ok, {[], "(#{x} #{sym[op]} #{y})", k, st}}
  end

  defp word_rust(k, :not, [x], _lays, st), do: {:ok, {[], "(!#{x})", k, st}}

  defp word_rust(_k, op, [x, y], _lays, st) when op in [:eq, :lt, :le] do
    sym = %{eq: "==", lt: "<", le: "<="}
    {:ok, {[], "(#{x} #{sym[op]} #{y})", :wbool, st}}
  end

  defp word_rust(k, op, [x, y], _lays, st) when op in [:cadd, :csub, :cmul] do
    name = %{cadd: "checked_add", csub: "checked_sub", cmul: "checked_mul"}
    {:ok, {[], "#{x}.#{name[op]}(#{y})", {:opt, k}, st}}
  end

  defp word_rust(k, :div, [x, y], _lays, st) do
    {:ok, {[], "#{x}.checked_div(#{y})", {:opt, k}, st}}
  end

  defp word_rust(k, :rem, [x, y], _lays, st) do
    {:ok, {[], "#{x}.checked_rem(#{y})", {:opt, k}, st}}
  end

  defp word_rust(k, op, [x, amt], _lays, st) when op in [:shl, :shr] do
    r_shift(k, op, x, amt, st)
  end

  defp word_rust(k, {:cast, k}, [x], [src | _], st) do
    {:ok, {[], r_cast(k, src, x), k, st}}
  end

  defp word_rust(k, :some, [x], _lays, st) do
    {:ok, {[], "::std::option::Option::Some(#{x})", {:opt, k}, st}}
  end

  defp word_rust(_k, _op, _args, _lays, _st), do: {:error, "c:unsupported"}

  defp r_lit(:i64, n) do
    n = rem(n, 18_446_744_073_709_551_616)

    if n >= 9_223_372_036_854_775_808,
      do: "(#{n}u64 as i64)",
      else: "#{n}i64"
  end

  defp r_lit(k, n) do
    mod =
      case k do
        :u8 -> 256
        :u32 -> 4_294_967_296
        _ -> 18_446_744_073_709_551_616
      end

    "#{rem(n, mod)}#{k}"
  end

  defp r_shift(k, op, x, amt, st) do
    {sh, st} = local(st, g("s"))
    {p, st} = local(st, g("p"))
    {out, st} = local(st, g("t"))
    w = r_width(k)
    node = g("NatNode")
    zero = g("tag_zero")
    suc = g("tag_suc")
    nxt = g("n")

    lines = [
      "let mut #{sh}: u32 = 0;",
      "let mut #{p} = #{amt}.clone();",
      "while #{sh} + 1 < #{w} {",
      "    match &*#{p}.0 {",
      "        #{node}::#{zero} => break,",
      "        #{node}::#{suc}(#{nxt}) => { #{sh} += 1; #{p} = #{nxt}.clone(); }",
      "    }",
      "}",
      "let #{out}: #{rty(k, st)} = if matches!(&*#{p}.0, #{node}::#{suc}(_)) { #{r_shift_oob(k, op, x)} } else { #{r_shift_in(op, x, sh)} };"
    ]

    {:ok, {lines, out, k, st}}
  end

  defp r_width(:u8), do: 8
  defp r_width(:u32), do: 32
  defp r_width(_), do: 64

  defp r_shift_oob(k, :shl, _x), do: "0#{k}"
  defp r_shift_oob(k, :shr, _x) when k != :i64, do: "0#{k}"
  defp r_shift_oob(:i64, :shr, x), do: "if #{x} < 0 { -1i64 } else { 0i64 }"

  defp r_shift_in(:shl, x, sh), do: "#{x} << #{sh}"
  defp r_shift_in(:shr, x, sh), do: "#{x} >> #{sh}"

  defp r_cast(k, src, x), do: r_from_u64(k, r_as_u64(src, x))
  defp r_as_u64(:u64, x), do: "(#{x})"
  defp r_as_u64(_src, x), do: "(#{x} as u64)"
  defp r_from_u64(:u64, bits), do: "(#{bits})"
  defp r_from_u64(k, bits), do: "(#{bits} as #{k})"

  defp rty(:u8, _st), do: "u8"
  defp rty(:u32, _st), do: "u32"
  defp rty(:u64, _st), do: "u64"
  defp rty(:i64, _st), do: "i64"
  defp rty(:wbool, _st), do: "bool"
  defp rty({:opt, pay}, st), do: "::std::option::Option<#{rty(pay, st)}>"
  defp rty(:slice, _st), do: g("slice")
  defp rty(:string, _st), do: g("str")
  defp rty(:nat, _st), do: g("Nat")
  defp rty(:unit, _st), do: g("Unit")
  defp rty(:opaque, _st), do: g("Erased")
  defp rty(:never, _st), do: "()"
  defp rty({:pair, _, _}, _st), do: g("Pair")
  defp rty({:stream, _}, _st), do: g("Stream")
  defp rty({:data, "Atom"}, _st), do: g("Atom")
  defp rty({:data, name}, st), do: Map.fetch!(st.types, name)

  defp data_layouts(book) do
    book
    |> Enum.filter(&(Map.get(&1, :kind) == :data))
    |> Enum.map(fn d ->
      ctors =
        d.ctors
        |> Enum.with_index()
        |> Enum.map(fn {ctor, tag} ->
          %{name: ctor.name, tag: tag, fields: ctor_fields(book, ctor.name)}
        end)

      %{name: d.name, layout: {:data, d.name}, constructors: ctors}
    end)
  end

  defp ctor_fields(book, cname) do
    case find_ctor(book, cname) do
      nil ->
        []

      ctor ->
        telescope(ctor.type)
        |> Enum.flat_map(fn
          {:erased, _, _} -> []
          {_, a, _} -> [type_layout(book, a)]
        end)
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
  defp type_layout(_book, :string), do: :string
  defp type_layout(_book, _), do: :opaque

  defp telescope(t), do: telescope(t, [])
  defp telescope({:pi, q, a, x, b}, acc), do: telescope(b, [{q, a, x} | acc])
  defp telescope(_t, acc), do: Enum.reverse(acc)

  defp find_ctor(book, name) do
    Enum.find_value(book, fn
      %{kind: :data, ctors: cs} -> Enum.find(cs, &(&1.name == name))
      _ -> nil
    end)
  end

  defp data?(book, name) do
    Enum.any?(book, &(Map.get(&1, :kind) == :data and &1.name == name))
  end

  defp unboxed_name?(book, name) when is_binary(name) do
    case Enum.find(book, &(Map.get(&1, :kind) == :data and &1.name == name)) do
      %{unboxed: true} -> true
      _ -> false
    end
  end

  defp unboxed_name?(_book, _name), do: false

  defp unboxed_lay?(book, {:data, name}), do: unboxed_name?(book, name)
  defp unboxed_lay?(_book, _lay), do: false

  defp lookup(env, name) do
    Enum.find_value(env, fn
      {^name, rn, lay} -> {rn, lay}
      _ -> nil
    end)
  end

  defp local(st, base) do
    base = if base in [nil, ""], do: g("s"), else: base
    {name, scope} = Name.bind_n(base, st.n, st.scope)
    {name, %{st | n: st.n + 1, scope: scope}}
  end

  defp fn_body(lines, expr) do
    indent(Enum.join(lines ++ [expr], "\n"), 4)
  end

  defp nest([], expr), do: expr

  defp nest(lines, expr) do
    "{\n#{indent(Enum.join(lines ++ [expr], "\n"), 4)}\n}"
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
  defp name_steps(steps, taken) do
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

  defp node_name(dname, st), do: g("node_" <> Map.fetch!(st.types, dname))

  defp data_items(book, types, variants, ctor_fns, file_scope) do
    Enum.map_join(data_decls(book), "\n\n", fn d ->
      if Map.get(d, :unboxed) == true do
        unboxed_data_item(d, book, types, variants, ctor_fns, file_scope)
      else
        boxed_data_item(d, book, types, variants, ctor_fns, file_scope)
      end
    end)
  end

  defp boxed_data_item(d, book, types, variants, ctor_fns, file_scope) do
    type = Map.fetch!(types, d.name)
    node = g("node_" <> type)

    variants_txt =
      Enum.map_join(d.ctors, "\n", fn c ->
        v = Map.fetch!(variants, {d.name, c.name})
        fields = ctor_fields(book, c.name)

        if fields == [] do
          "    #{v},"
        else
          tys = Enum.map_join(fields, ", ", &rty(&1, %{types: types}))
          "    #{v}(#{tys}),"
        end
      end)

    ctors =
      Enum.map_join(d.ctors, "\n\n", fn c ->
        fn_name = Map.fetch!(ctor_fns, {d.name, c.name})
        v = Map.fetch!(variants, {d.name, c.name})
        fields = ctor_fields(book, c.name)

        {bound, _} =
          fields
          |> Enum.with_index()
          |> Enum.map_reduce(file_scope, fn {lay, i}, scope ->
            {rn, scope} = Name.bind(g("a", i), scope)
            {{rn, lay}, scope}
          end)

        args =
          Enum.map_join(bound, ", ", fn {rn, lay} -> "#{rn}: #{rty(lay, %{types: types})}" end)

        build =
          if fields == [] do
            "#{node}::#{v}"
          else
            inner = Enum.map_join(bound, ", ", fn {rn, _lay} -> rn end)
            "#{node}::#{v}(#{inner})"
          end

        "fn #{fn_name}(#{args}) -> #{type} {\n    #{type}(::std::rc::Rc::new(#{build}))\n}"
      end)

    """
    #[derive(::std::clone::Clone)]
    pub struct #{type}(::std::rc::Rc<#{node}>);
    #[derive(::std::clone::Clone)]
    enum #{node} {
    #{variants_txt}
    }

    #{ctors}
    """
    |> String.trim()
  end

  # By value. Copy is derived and Eq is not: a Slice field is a raw pointer.
  defp unboxed_data_item(d, book, types, variants, ctor_fns, file_scope) do
    type = Map.fetch!(types, d.name)

    variants_txt =
      Enum.map_join(d.ctors, "\n", fn c ->
        v = Map.fetch!(variants, {d.name, c.name})
        fields = ctor_fields(book, c.name)

        if fields == [] do
          "    #{v},"
        else
          tys = Enum.map_join(fields, ", ", &rty(&1, %{types: types}))
          "    #{v}(#{tys}),"
        end
      end)

    ctors =
      Enum.map_join(d.ctors, "\n\n", fn c ->
        fn_name = Map.fetch!(ctor_fns, {d.name, c.name})
        v = Map.fetch!(variants, {d.name, c.name})
        fields = ctor_fields(book, c.name)

        {bound, _} =
          fields
          |> Enum.with_index()
          |> Enum.map_reduce(file_scope, fn {lay, i}, scope ->
            {rn, scope} = Name.bind(g("a", i), scope)
            {{rn, lay}, scope}
          end)

        args =
          Enum.map_join(bound, ", ", fn {rn, lay} -> "#{rn}: #{rty(lay, %{types: types})}" end)

        build =
          if fields == [] do
            "#{type}::#{v}"
          else
            inner = Enum.map_join(bound, ", ", fn {rn, _lay} -> rn end)
            "#{type}::#{v}(#{inner})"
          end

        "fn #{fn_name}(#{args}) -> #{type} {\n    #{build}\n}"
      end)

    """
    #[derive(::std::clone::Clone, ::std::marker::Copy)]
    pub enum #{type} {
    #{variants_txt}
    }

    #{ctors}
    """
    |> String.trim()
  end

  defp atom_enum(atoms) when map_size(atoms) == 0, do: ""

  defp atom_enum(atoms) do
    vars = Enum.map_join(atoms, "\n", fn {_name, v} -> "    #{v}," end)

    """
    #[derive(::std::clone::Clone, ::std::marker::Copy, ::std::cmp::PartialEq, ::std::cmp::Eq)]
    pub enum #{g("Atom")} {
    #{vars}
    }
    """
    |> String.trim()
  end

  defp data_decls(book) do
    Enum.filter(book, &(Map.get(&1, :kind) == :data))
  end

  defp runtime do
    erased = g("Erased")
    nat = g("Nat")
    node = g("NatNode")
    zero = g("tag_zero")
    suc = g("tag_suc")
    unit = g("Unit")
    pair = g("Pair")
    stream = g("Stream")
    x = g("x")
    e = g("e")
    rc = g("rc")
    v = g("v")
    n = g("n")
    k = g("k")
    p = g("p")

    """
    #[derive(::std::clone::Clone)]
    pub struct #{erased}(::std::rc::Rc<dyn ::std::any::Any>);

    pub fn #{g("erase")}<T: 'static>(#{x}: T) -> #{erased} {
        #{erased}(::std::rc::Rc::new(#{x}))
    }

    pub fn #{g("reveal")}<T: 'static + ::std::clone::Clone>(#{e}: #{erased}) -> T {
        match ::std::rc::Rc::downcast::<T>(#{e}.0) {
            ::std::result::Result::Ok(#{rc}) => match ::std::rc::Rc::try_unwrap(#{rc}) {
                ::std::result::Result::Ok(#{v}) => #{v},
                ::std::result::Result::Err(#{rc}) => (*#{rc}).clone(),
            },
            ::std::result::Result::Err(_) => ::std::process::abort(),
        }
    }

    #[derive(::std::clone::Clone)]
    pub struct #{nat}(::std::rc::Rc<#{node}>);
    #[derive(::std::clone::Clone)]
    enum #{node} {
        #{zero},
        #{suc}(#{nat}),
    }

    fn #{g("zero")}() -> #{nat} {
        #{nat}(::std::rc::Rc::new(#{node}::#{zero}))
    }

    fn #{g("suc")}(#{n}: #{nat}) -> #{nat} {
        #{nat}(::std::rc::Rc::new(#{node}::#{suc}(#{n})))
    }

    pub fn #{g("from_u64")}(mut #{k}: ::std::primitive::u64) -> #{nat} {
        let mut #{n} = #{g("zero")}();
        while #{k} > 0 {
            #{n} = #{g("suc")}(#{n});
            #{k} -= 1;
        }
        #{n}
    }

    pub fn #{g("to_u64")}(#{n}: &#{nat}) -> ::std::primitive::u64 {
        let mut #{k} = 0u64;
        let mut #{n} = #{n}.clone();
        loop {
            match &*#{n}.0 {
                #{node}::#{zero} => return #{k},
                #{node}::#{suc}(#{p}) => {
                    #{k} += 1;
                    #{n} = #{p}.clone();
                }
            }
        }
    }

    #[derive(::std::clone::Clone, ::std::marker::Copy)]
    pub struct #{unit};

    #[derive(::std::clone::Clone)]
    pub struct #{pair}(#{erased}, #{erased});

    #[derive(::std::clone::Clone)]
    pub struct #{stream} {
        #{g("field_seed")}: #{erased},
        #{g("field_step")}: ::std::rc::Rc<dyn ::std::ops::Fn(#{erased}) -> #{pair}>,
    }
    """
    |> String.trim()
  end

  defp bytes_runtime(book, funs) do
    if bytes_image?(book, funs), do: bytes_helpers(), else: ""
  end

  defp string_runtime(book, funs) do
    if string_image?(book, funs), do: string_helpers(bytes_image?(book, funs)), else: ""
  end

  defp bytes_image?(book, funs) do
    Enum.any?(funs, fn fun ->
      fun.ret == :slice or Enum.any?(fun.params, fn {_n, lay} -> lay == :slice end) or
        ir_bytes?(fun.body)
    end) or
      Enum.any?(data_decls(book), fn d ->
        Enum.any?(d.ctors, fn c -> Enum.any?(ctor_fields(book, c.name), &(&1 == :slice)) end)
      end)
  end

  defp ir_bytes?(t) when is_tuple(t) do
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
      other -> other |> Tuple.to_list() |> Enum.any?(&ir_bytes?/1)
    end
  end

  defp ir_bytes?(t) when is_list(t), do: Enum.any?(t, &ir_bytes?/1)
  defp ir_bytes?(:slice), do: true
  defp ir_bytes?(_), do: false

  defp bytes_helpers do
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

    """
    #[derive(::std::clone::Clone, ::std::marker::Copy)]
    #[repr(C)]
    pub struct #{sl} { pub p: *const u8, pub n: usize }

    #[allow(non_upper_case_globals)]
    static #{empty}: u8 = 0;

    fn #{emp}() -> #{sl} {
        #{sl} { p: &#{empty} as *const u8, n: 0 }
    }

    pub fn #{wrap}(p: *const u8, n: usize) -> #{sl} {
        if n == 0 || p.is_null() { #{emp}() } else { #{sl} { p: p, n: n } }
    }

    fn #{sub}(s: #{sl}, off: u64, len: u64) -> #{sl} {
        if off > s.n as u64 || len > (s.n as u64) - off {
            #{emp}()
        } else {
            #{sl} { p: unsafe { s.p.add(off as usize) }, n: len as usize }
        }
    }

    fn #{eq}(a: #{sl}, b: #{sl}) -> bool {
        if a.n != b.n { return false; }
        if a.n == 0 { return true; }
        unsafe { ::std::slice::from_raw_parts(a.p, a.n) == ::std::slice::from_raw_parts(b.p, b.n) }
    }

    fn #{cat}(a: #{sl}, b: #{sl}) -> #{sl} {
        let n = a.n + b.n;
        if n == 0 { return #{emp}(); }
        let mut buf = ::std::vec::Vec::<u8>::with_capacity(n);
        if a.n != 0 { buf.extend_from_slice(unsafe { ::std::slice::from_raw_parts(a.p, a.n) }); }
        if b.n != 0 { buf.extend_from_slice(unsafe { ::std::slice::from_raw_parts(b.p, b.n) }); }
        let p = buf.as_ptr();
        ::std::mem::forget(buf);
        #{sl} { p: p, n: n }
    }

    fn #{get}(s: #{sl}, i: u64) -> ::std::option::Option<u8> {
        if i >= s.n as u64 { ::std::option::Option::None } else { ::std::option::Option::Some(unsafe { *s.p.add(i as usize) }) }
    }

    fn #{til}(s: #{sl}, b: u8) -> #{sl} {
        let mut i = 0usize;
        while i < s.n {
            if unsafe { *s.p.add(i) } == b { return #{sl} { p: s.p, n: i }; }
            i += 1;
        }
        s
    }

    fn #{aft}(s: #{sl}, b: u8) -> #{sl} {
        let mut i = 0usize;
        while i < s.n {
            if unsafe { *s.p.add(i) } == b {
                return #{sl} { p: unsafe { s.p.add(i + 1) }, n: s.n - i - 1 };
            }
            i += 1;
        }
        #{emp}()
    }
    """
    |> String.trim()
  end

  defp string_image?(book, funs) do
    Enum.any?(funs, fn fun ->
      string_lay?(fun.ret) or Enum.any?(fun.params, fn {_n, lay} -> string_lay?(lay) end) or
        ir_string?(fun.body)
    end) or
      Enum.any?(data_decls(book), fn d ->
        Enum.any?(d.ctors, fn c -> Enum.any?(ctor_fields(book, c.name), &string_lay?/1) end)
      end)
  end

  defp string_lay?(:string), do: true
  defp string_lay?({:opt, a}), do: string_lay?(a)
  defp string_lay?({:pair, a, b}), do: string_lay?(a) or string_lay?(b)
  defp string_lay?({:stream, a}), do: string_lay?(a)
  defp string_lay?(_), do: false

  defp ir_string?(t) when is_tuple(t) do
    case t do
      {:str, _} -> true
      {:scat, _, _} -> true
      {:slen, _} -> true
      {:seq, _, _} -> true
      {:sbytes, _} -> true
      other -> other |> Tuple.to_list() |> Enum.any?(&ir_string?/1)
    end
  end

  defp ir_string?(t) when is_list(t), do: Enum.any?(t, &ir_string?/1)
  defp ir_string?(:string), do: true
  defp ir_string?(_), do: false

  defp string_helpers(bytes?) do
    ty = g("str")
    empty = g("empty_str")
    emp = g("str_empty")
    eq = g("str_eq")
    cat = g("str_cat")
    len = g("str_len")
    bytes = if bytes?, do: rust_str_bytes(), else: ""

    """
    #[derive(::std::clone::Clone, ::std::marker::Copy)]
    #[repr(C)]
    pub struct #{ty} { pub p: *const u8, pub n: usize }

    #[allow(non_upper_case_globals)]
    static #{empty}: u8 = 0;

    fn #{emp}() -> #{ty} {
        #{ty} { p: &#{empty} as *const u8, n: 0 }
    }

    fn #{eq}(a: #{ty}, b: #{ty}) -> bool {
        if a.n != b.n { return false; }
        if a.n == 0 { return true; }
        unsafe { ::std::slice::from_raw_parts(a.p, a.n) == ::std::slice::from_raw_parts(b.p, b.n) }
    }

    fn #{cat}(a: #{ty}, b: #{ty}) -> #{ty} {
        let n = a.n + b.n;
        if n == 0 { return #{emp}(); }
        let mut buf = ::std::vec::Vec::<u8>::with_capacity(n);
        if a.n != 0 { buf.extend_from_slice(unsafe { ::std::slice::from_raw_parts(a.p, a.n) }); }
        if b.n != 0 { buf.extend_from_slice(unsafe { ::std::slice::from_raw_parts(b.p, b.n) }); }
        let p = buf.as_ptr();
        ::std::mem::forget(buf);
        #{ty} { p: p, n: n }
    }

    fn #{len}(s: #{ty}) -> #{g("Nat")} {
        let mut i = 0usize;
        let mut k = 0u64;
        while i < s.n {
            let c = unsafe { *s.p.add(i) };
            let mut w = 1usize;
            if (c & 0xE0) == 0xC0 { w = 2; }
            else if (c & 0xF0) == 0xE0 { w = 3; }
            else if (c & 0xF8) == 0xF0 { w = 4; }
            if w > s.n - i { w = s.n - i; }
            i += w;
            k += 1;
        }
        #{g("from_u64")}(k)
    }
    #{bytes}
    """
    |> String.trim()
  end

  defp rust_str_bytes do
    ty = g("str")
    sl = g("slice")

    """
    fn #{g("str_bytes")}(s: #{ty}) -> #{sl} {
        #{sl} { p: s.p, n: s.n }
    }
    """
    |> String.trim()
  end
end

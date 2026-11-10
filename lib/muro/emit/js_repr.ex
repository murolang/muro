defmodule Muro.Emit.JS.Repr do
  @moduledoc false

  # JavaScript encode and decode for a `repr`. The plan is `Muro.Repr.plans/2`,
  # the same analysis the Elixir codecs use. Decode returns
  # `{ ok: { value, table } }` or `{ error: { path, reason } }`. Encode returns
  # `{ ok: wire }` or `{ error: { path, reason } }`. Neither throws.
  # `muro_repr_table_new` and `muro_repr_table_names` throw on a bad argument,
  # matching the Elixir `ArgumentError`.
  #
  # The value is the run image: a bigint nat, `{ tag, fields }`, `null` for
  # unit, a two-element array for a pair. The host wire is a JavaScript value:
  # numbers, bigints, booleans, strings, `null`, arrays, plain objects, `Map`,
  # and `muro_repr_atom` for an atom. A book with no repr emits nothing.

  alias Muro.Emit
  alias Muro.Repr

  @exported MapSet.new(~w(muro_repr_table_new muro_repr_table_names muro_repr_atom))
  @consts MapSet.new(~w(muro_repr_nat_max muro_repr_atom_sym))

  @helper_order ~w(
    muro_repr_table_new
    muro_repr_table_names
    muro_repr_table_check
    muro_repr_table_copy
    muro_repr_inspect
    muro_repr_is_ctor
    muro_repr_is_int
    muro_repr_is_atom
    muro_repr_atom
    muro_repr_is_plain
    muro_repr_is_map
    muro_repr_is_data
    muro_repr_show
    muro_repr_key_eq
    muro_repr_lit_eq
    muro_repr_lookup
    muro_repr_keys
    muro_repr_keys_have
    muro_repr_path_key
    muro_repr_has_lit
    muro_repr_fetch
    muro_repr_tag
    muro_repr_expect
    muro_repr_atom_name
    muro_repr_wire_rank
    muro_repr_wire_cmp
    muro_repr_array_cmp
    muro_repr_map_cmp
    muro_repr_entries
    muro_repr_no_extra
    muro_repr_ambiguous
    muro_repr_decode_nat
    muro_repr_encode_nat
    muro_repr_decode_bool
    muro_repr_encode_bool
    muro_repr_decode_optional
    muro_repr_put_optional
    muro_repr_decode_nullable
    muro_repr_encode_nullable
    muro_repr_list_decode
    muro_repr_list_encode
    muro_repr_decode_interned
    muro_repr_intern_index
    muro_repr_name_term
    muro_repr_name_index
    muro_repr_encode_interned
    muro_repr_bin_from
    muro_repr_bin_index
    muro_repr_term_eq
    muro_repr_map_put
    muro_repr_finish_map
    muro_repr_finish_entries
    muro_repr_map_of_decode
    muro_repr_map_of_encode
    muro_repr_path_eq
    muro_repr_seg_eq
    muro_repr_else
  )

  @doc false
  def render(book, taken, types)
      when is_list(book) and is_struct(taken, MapSet) and is_map(types) do
    case Repr.plans(book, Emit.elixir_names(book)) do
      {:ok, []} ->
        {:ok, nil}

      {:ok, plans} ->
        build(plans, taken, types)

      {:error, msg} ->
        {:error, msg}
    end
  end

  defp build(plans, taken, types) do
    by_fun = Map.new(plans, fn {d, codec} -> {Repr.snake_ident(d.name), codec} end)
    kinds = interned_kinds(plans)
    keep_nat = num_fallback?(plans)
    helpers = helper_sources(kinds, keep_nat)
    funs = Enum.map_join(plans, "\n\n", fn {d, codec} -> render_pair(d, codec, by_fun) end)

    set =
      (called(funs) ++ ["muro_repr_table_new", "muro_repr_table_names", "muro_repr_table_check"])
      |> close(helpers)
      |> add_atom()

    source =
      [emit_consts(set), emit_helpers(set, helpers), funs]
      |> Enum.reject(&(&1 == ""))
      |> Enum.join("\n\n")

    case collide(source, taken, plans) do
      :ok ->
        names = export_names(set, plans)

        {:ok,
         %{source: source, dts: dts(plans, types, set), names: names, clauses: clauses(names)}}

      {:error, _} = err ->
        err
    end
  end

  defp render_pair(d, codec, plans) do
    fun = Repr.snake_ident(d.name)
    dec = "decode_" <> fun
    enc = "encode_" <> fun

    """
    export function #{dec}(value, table) {
      const checked = muro_repr_table_check(table === undefined ? muro_repr_table_new() : table, "#{dec}");
      if (checked.error) return checked;
      return muro_repr_dec_#{fun}(value, [], checked.ok);
    }

    function muro_repr_dec_#{fun}(value, path, table) {
    #{ind(dec_stmts(codec, plans))}
    }

    export function #{enc}(value, table) {
      const checked = muro_repr_table_check(table, "#{enc}");
      if (checked.error) return checked;
      return muro_repr_enc_#{fun}(value, checked.ok);
    }

    function muro_repr_enc_#{fun}(value, table) {
    #{ind(enc_stmts(codec, enc, plans))}
    }
    """
    |> String.trim()
  end

  # -- decode ----------------------------------------------------------------

  defp dec_stmts({:bool}, _plans), do: "return muro_repr_decode_bool(value, path, table);"
  defp dec_stmts({:nat}, _plans), do: "return muro_repr_decode_nat(value, path, table);"
  defp dec_stmts({:const, lit, ctor}, _plans), do: const_dec(lit, ctor)
  defp dec_stmts({:wrap, ctor, inner}, plans), do: wrap_dec(ctor, inner, plans)
  defp dec_stmts({:unwrap, ctor, inner}, plans), do: wrap_dec(ctor, inner, plans)
  defp dec_stmts({:tuple, ctor, comps}, plans), do: tuple_dec(ctor, comps, plans)
  defp dec_stmts({:map, open?, ctor, entries}, plans), do: map_dec(open?, ctor, entries, plans)
  defp dec_stmts({:choice, arms}, plans), do: choice_dec(arms, plans)

  defp dec_stmts(codec, plans),
    do: "return " <> dec_expr(codec, "value", "path", "table", plans) <> ";"

  defp const_dec(lit, ctor) do
    """
    if (#{lit_guard(lit)}) return { ok: { value: #{nullary(ctor)}, table } };
    return { error: { path, reason: { k: "expected", literal: #{lit_shown(lit)}, value } } };
    """
    |> String.trim()
  end

  defp wrap_dec(ctor, inner, plans) do
    """
    const step = #{dec_expr(inner, "value", "path", "table", plans)};
    if (step.error) return step;
    return { ok: { value: #{data(ctor, ["step.ok.value"])}, table: step.ok.table } };
    """
    |> String.trim()
  end

  defp tuple_dec(ctor, comps, plans) do
    n = length(comps)

    {lines, _} =
      Enum.reduce(Enum.with_index(comps), {[], 0}, fn
        {{:tag, lit}, idx}, {lines, fi} ->
          line =
            "step = muro_repr_expect(value[#{idx}], path.concat([#{idx}]), #{lit_host(lit)});\nif (step.error) return step;"

          {[line | lines], fi}

        {{:field, codec}, idx}, {lines, fi} ->
          line = """
          step = #{dec_expr(codec, "value[#{idx}]", "path.concat([#{idx}])", "table", plans)};
          if (step.error) return step;
          const f#{fi} = step.ok.value;
          table = step.ok.table;
          """

          {[String.trim(line) | lines], fi + 1}
      end)

    """
    if (!Array.isArray(value)) return { error: { path, reason: { k: "not_tuple", value } } };
    if (value.length !== #{n}) return { error: { path, reason: { k: "wrong_tuple_size", size: #{n}, value } } };
    let step;
    #{lines |> Enum.reverse() |> Enum.join("\n")}
    return { ok: { value: #{data(ctor, field_refs(comps))}, table } };
    """
    |> String.trim()
  end

  defp map_dec(open?, ctor, entries, plans) do
    keys = Enum.map(entries, &entry_key/1)

    {lines, _} =
      Enum.reduce(entries, {[], 0}, fn
        {:tag, key, lit}, {lines, fi} ->
          line =
            "step = muro_repr_tag(value, path, #{key_expr(key)}, #{lit_host(lit)});\nif (step.error) return step;"

          {[line | lines], fi}

        {:field, key, codec}, {lines, fi} ->
          line = """
          step = muro_repr_fetch(value, path, #{key_expr(key)});
          if (step.error) return step;
          const g#{fi} = step.ok;
          step = #{dec_expr(codec, "g#{fi}", "muro_repr_path_key(path, #{key_expr(key)})", "table", plans)};
          if (step.error) return step;
          const f#{fi} = step.ok.value;
          table = step.ok.table;
          """

          {[String.trim(line) | lines], fi + 1}

        {:opt, key, nothing, just, codec, mode}, {lines, fi} ->
          line = """
          step = muro_repr_decode_optional(value, path, table, #{key_expr(key)}, #{dec_lambda(codec, plans)}, "#{tag(nothing)}", "#{tag(just)}", #{mode_js(mode)});
          if (step.error) return step;
          const f#{fi} = step.ok.value;
          table = step.ok.table;
          """

          {[String.trim(line) | lines], fi + 1}
      end)

    pre =
      if open? and keys != [] do
        "step = muro_repr_ambiguous(value, path, [#{Enum.map_join(keys, ", ", &key_expr/1)}]);\nif (step.error) return step;"
      else
        ""
      end

    post =
      if open? do
        ""
      else
        "step = muro_repr_no_extra(value, path, [#{Enum.map_join(keys, ", ", &key_expr/1)}]);\nif (step.error) return step;"
      end

    """
    if (!muro_repr_is_map(value)) return { error: { path, reason: { k: "not_map", value } } };
    let step;
    #{pre}
    #{lines |> Enum.reverse() |> Enum.join("\n")}
    #{post}
    return { ok: { value: #{data(ctor, field_refs(entries))}, table } };
    """
    |> String.trim()
  end

  defp choice_dec(arms, plans) do
    body =
      Enum.map_join(arms, "\n", fn arm ->
        """
        if (#{class_guard(arm, plans, MapSet.new())}) {
        #{ind(arm_dec(arm, plans))}
        }
        """
        |> String.trim()
      end)

    names = Enum.map_join(arms, ", ", fn arm -> "\"#{tag(arm_ctor(arm))}\"" end)

    """
    #{body}
    return { error: { path, reason: { k: "no_variant", names: [#{names}], value } } };
    """
    |> String.trim()
  end

  defp arm_dec({:const, lit, ctor}, _plans), do: const_dec(lit, ctor)
  defp arm_dec({:unwrap, ctor, inner}, plans), do: wrap_dec(ctor, inner, plans)
  defp arm_dec({:tuple, ctor, comps}, plans), do: tuple_dec(ctor, comps, plans)
  defp arm_dec({:map, open?, ctor, entries}, plans), do: map_dec(open?, ctor, entries, plans)

  defp dec_expr({:nat}, v, p, t, _plans), do: "muro_repr_decode_nat(#{v}, #{p}, #{t})"
  defp dec_expr({:bool}, v, p, t, _plans), do: "muro_repr_decode_bool(#{v}, #{p}, #{t})"
  defp dec_expr({:call, fun}, v, p, t, _plans), do: "muro_repr_dec_#{fun}(#{v}, #{p}, #{t})"

  defp dec_expr({:list, nil_c, cons, el}, v, p, t, plans) do
    "muro_repr_list_decode(#{v}, #{p}, #{t}, #{dec_lambda(el, plans)}, \"#{tag(nil_c)}\", \"#{tag(cons)}\")"
  end

  defp dec_expr({:nullable, nothing, just, inner}, v, p, t, plans) do
    "muro_repr_decode_nullable(#{v}, #{p}, #{t}, \"#{tag(nothing)}\", \"#{tag(just)}\", #{dec_lambda(inner, plans)})"
  end

  defp dec_expr({:interned, kind, reserved}, v, p, t, _plans) do
    "muro_repr_decode_interned(#{v}, #{p}, #{t}, #{kind_js(kind)}, #{reserved_js(reserved)})"
  end

  defp dec_expr({:map_of, key, val, mode}, v, p, t, plans) do
    {elem, nil_c, cons} = pack_js(mode)

    "muro_repr_map_of_decode(#{v}, #{p}, #{t}, #{dec_lambda(key, plans)}, #{dec_lambda(val, plans)}, #{elem}, \"#{tag(nil_c)}\", \"#{tag(cons)}\")"
  end

  defp dec_expr({:else, inner, fb}, v, p, t, plans) do
    "muro_repr_else(#{dec_expr(inner, v, p, t, plans)}, #{p}, #{t}, #{fallback_js(fb)})"
  end

  defp dec_expr({:wrap, ctor, inner}, v, p, t, plans) do
    "(() => { const step = #{dec_expr(inner, v, p, t, plans)}; if (step.error) return step; return { ok: { value: #{data(ctor, ["step.ok.value"])}, table: step.ok.table } }; })()"
  end

  defp dec_lambda(codec, plans), do: "(el, p, t) => " <> dec_expr(codec, "el", "p", "t", plans)

  # -- encode ----------------------------------------------------------------

  defp enc_stmts({:bool}, _pub, _plans), do: "return muro_repr_encode_bool(value);"
  defp enc_stmts({:nat}, _pub, _plans), do: "return muro_repr_encode_nat(value);"

  defp enc_stmts({:const, lit, ctor}, _pub, _plans) do
    """
    if (!muro_repr_is_ctor(value, "#{tag(ctor)}", 0)) return #{bad()};
    return { ok: #{lit_host(lit)} };
    """
    |> String.trim()
  end

  defp enc_stmts({:wrap, ctor, inner}, pub, plans), do: enc_wrap(ctor, inner, pub, plans)
  defp enc_stmts({:unwrap, ctor, inner}, pub, plans), do: enc_wrap(ctor, inner, pub, plans)

  defp enc_stmts({:tuple, ctor, comps}, pub, plans) do
    n = field_slots(comps)

    """
    if (!muro_repr_is_ctor(value, "#{tag(ctor)}", #{n})) return #{bad()};
    #{tuple_enc_body(comps, pub, plans)}
    """
    |> String.trim()
  end

  defp enc_stmts({:map, _open, ctor, entries}, pub, plans) do
    n = field_slots(entries)

    """
    if (!muro_repr_is_ctor(value, "#{tag(ctor)}", #{n})) return #{bad()};
    #{map_enc_body(entries, pub, plans)}
    """
    |> String.trim()
  end

  defp enc_stmts({:choice, arms}, pub, plans) do
    body =
      Enum.map_join(arms, "\n", fn arm ->
        enc_arm(arm, pub, plans)
      end)

    """
    #{body}
    return #{bad()};
    """
    |> String.trim()
  end

  defp enc_stmts(codec, pub, plans),
    do: "return " <> enc_expr(codec, "value", "table", pub, plans) <> ";"

  defp enc_wrap(ctor, inner, pub, plans) do
    """
    if (!muro_repr_is_ctor(value, "#{tag(ctor)}", 1)) return #{bad()};
    return #{enc_expr(inner, "value.fields[0]", "table", pub, plans)};
    """
    |> String.trim()
  end

  defp enc_arm({:const, lit, ctor}, _pub, _plans) do
    "if (muro_repr_is_ctor(value, \"#{tag(ctor)}\", 0)) return { ok: #{lit_host(lit)} };"
  end

  defp enc_arm({:unwrap, ctor, inner}, pub, plans) do
    "if (muro_repr_is_ctor(value, \"#{tag(ctor)}\", 1)) return #{enc_expr(inner, "value.fields[0]", "table", pub, plans)};"
  end

  defp enc_arm({:tuple, ctor, comps}, pub, plans) do
    n = field_slots(comps)

    """
    if (muro_repr_is_ctor(value, "#{tag(ctor)}", #{n})) {
    #{ind(tuple_enc_body(comps, pub, plans))}
    }
    """
    |> String.trim()
  end

  defp enc_arm({:map, _open, ctor, entries}, pub, plans) do
    n = field_slots(entries)

    """
    if (muro_repr_is_ctor(value, "#{tag(ctor)}", #{n})) {
    #{ind(map_enc_body(entries, pub, plans))}
    }
    """
    |> String.trim()
  end

  defp tuple_enc_body(comps, pub, plans) do
    {elems, lines, _} =
      Enum.reduce(comps, {[], [], 0}, fn
        {:tag, lit}, {elems, lines, fi} ->
          {elems ++ [lit_host(lit)], lines, fi}

        {:field, codec}, {elems, lines, fi} ->
          line = """
          step = #{enc_expr(codec, "value.fields[#{fi}]", "table", pub, plans)};
          if (step.error) return step;
          const w#{fi} = step.ok;
          """

          {elems ++ ["w#{fi}"], lines ++ [String.trim(line)], fi + 1}
      end)

    bind = if lines == [], do: "", else: "let step;\n"

    """
    #{bind}#{Enum.join(lines, "\n")}
    return { ok: [#{Enum.join(elems, ", ")}] };
    """
    |> String.trim()
  end

  defp map_enc_body(entries, pub, plans) do
    {lines, _} =
      Enum.reduce(entries, {[], 0}, fn
        {:tag, key, lit}, {lines, fi} ->
          {["entries.push([#{key_expr(key)}, #{lit_host(lit)}]);" | lines], fi}

        {:field, key, codec}, {lines, fi} ->
          line = """
          step = #{enc_expr(codec, "value.fields[#{fi}]", "table", pub, plans)};
          if (step.error) return step;
          entries.push([#{key_expr(key)}, step.ok]);
          """

          {[String.trim(line) | lines], fi + 1}

        {:opt, key, nothing, just, codec, _mode}, {lines, fi} ->
          line = """
          step = muro_repr_put_optional(entries, #{key_expr(key)}, "#{tag(nothing)}", "#{tag(just)}", value.fields[#{fi}], (el) => #{enc_expr(codec, "el", "table", pub, plans)});
          if (step.error) return step;
          """

          {[String.trim(line) | lines], fi + 1}
      end)

    """
    const entries = [];
    let step;
    #{lines |> Enum.reverse() |> Enum.join("\n")}
    return muro_repr_finish_entries(entries);
    """
    |> String.trim()
  end

  defp enc_expr({:nat}, v, _t, _pub, _plans), do: "muro_repr_encode_nat(#{v})"
  defp enc_expr({:bool}, v, _t, _pub, _plans), do: "muro_repr_encode_bool(#{v})"
  defp enc_expr({:call, fun}, v, t, _pub, _plans), do: "muro_repr_enc_#{fun}(#{v}, #{t})"
  defp enc_expr({:else, inner, _}, v, t, pub, plans), do: enc_expr(inner, v, t, pub, plans)

  defp enc_expr({:list, nil_c, cons, el}, v, t, pub, plans) do
    "muro_repr_list_encode(#{v}, \"#{tag(nil_c)}\", \"#{tag(cons)}\", (el) => #{enc_expr(el, "el", t, pub, plans)})"
  end

  defp enc_expr({:nullable, nothing, just, inner}, v, t, pub, plans) do
    "muro_repr_encode_nullable(\"#{tag(nothing)}\", \"#{tag(just)}\", #{v}, (el) => #{enc_expr(inner, "el", t, pub, plans)})"
  end

  defp enc_expr({:interned, kind, reserved}, v, t, pub, _plans) do
    "muro_repr_encode_interned(#{v}, #{t}, #{kind_js(kind)}, #{reserved_js(reserved)}, \"#{js(pub)}\")"
  end

  defp enc_expr({:map_of, key, val, mode}, v, t, pub, plans) do
    {split, nil_c, cons} = split_js(mode)

    "muro_repr_map_of_encode(#{v}, #{split}, \"#{tag(nil_c)}\", \"#{tag(cons)}\", (el) => #{enc_expr(key, "el", t, pub, plans)}, (el) => #{enc_expr(val, "el", t, pub, plans)}, \"#{js(pub)}\")"
  end

  defp enc_expr({:wrap, ctor, inner}, v, t, pub, plans) do
    "(() => { if (!muro_repr_is_ctor(#{v}, \"#{tag(ctor)}\", 1)) return #{bad_of(v)}; return #{enc_expr(inner, "#{v}.fields[0]", t, pub, plans)}; })()"
  end

  # -- class guards ----------------------------------------------------------

  defp class_guard({:bool}, _plans, _seen), do: "(value === true || value === false)"
  defp class_guard({:nat}, _plans, _seen), do: "muro_repr_is_int(value)"
  defp class_guard({:const, lit, _}, _plans, _seen), do: lit_guard(lit)

  defp class_guard({:interned, _, reserved}, _plans, _seen) do
    Enum.reduce(reserved, "typeof value === \"string\"", fn lit, acc ->
      acc <> " && value !== \"#{js(lit)}\""
    end)
  end

  defp class_guard({:map_of, _, _, _}, _plans, _seen), do: "muro_repr_is_map(value)"
  defp class_guard({:else, inner, _}, plans, seen), do: class_guard(inner, plans, seen)

  defp class_guard({:call, fun}, plans, seen) do
    if MapSet.member?(seen, fun) do
      "true"
    else
      class_guard(Map.fetch!(plans, fun), plans, MapSet.put(seen, fun))
    end
  end

  defp class_guard({:list, _, _, _}, _plans, _seen), do: "Array.isArray(value)"

  defp class_guard({:nullable, _, _, inner}, plans, seen) do
    "(value === null || (#{class_guard(inner, plans, seen)}))"
  end

  defp class_guard({:wrap, _, inner}, plans, seen), do: class_guard(inner, plans, seen)
  defp class_guard({:unwrap, _, inner}, plans, seen), do: class_guard(inner, plans, seen)

  defp class_guard({:tuple, _, comps}, _plans, _seen) do
    base = "Array.isArray(value) && value.length === #{length(comps)}"

    comps
    |> Enum.with_index()
    |> Enum.reduce(base, fn
      {{:tag, lit}, i}, acc -> acc <> " && " <> lit_eq("value[#{i}]", lit)
      _, acc -> acc
    end)
  end

  defp class_guard({:map, _, _, entries}, _plans, _seen) do
    Enum.reduce(entries, "muro_repr_is_map(value)", fn
      {:tag, key, lit}, acc ->
        acc <> " && muro_repr_has_lit(value, #{key_expr(key)}, #{lit_host(lit)})"

      _, acc ->
        acc
    end)
  end

  defp class_guard({:choice, arms}, plans, seen) do
    Enum.map_join(arms, " || ", fn arm -> "(" <> class_guard(arm, plans, seen) <> ")" end)
  end

  defp lit_eq(src, nil), do: "#{src} === null"
  defp lit_eq(src, lit) when is_binary(lit), do: "#{src} === \"#{js(lit)}\""

  defp lit_eq(src, lit) when is_atom(lit),
    do: "muro_repr_lit_eq(#{src}, #{lit_host(lit)})"

  # -- literals --------------------------------------------------------------

  defp lit_guard(nil), do: "value === null"
  defp lit_guard(lit) when is_binary(lit), do: "value === \"#{js(lit)}\""

  defp lit_guard(lit) when is_atom(lit),
    do: "muro_repr_is_atom(value) && value.atom === \"#{js(Atom.to_string(lit))}\""

  defp lit_host(nil), do: "null"
  defp lit_host(lit) when is_binary(lit), do: "\"#{js(lit)}\""

  defp lit_host(lit) when is_atom(lit),
    do: "muro_repr_atom(\"#{js(Atom.to_string(lit))}\")"

  defp lit_shown(nil), do: "null"
  defp lit_shown(lit) when is_binary(lit), do: "\"#{js(lit)}\""

  defp lit_shown(lit) when is_atom(lit),
    do: "{ atom: \"#{js(Atom.to_string(lit))}\" }"

  defp key_expr(nil), do: "null"
  defp key_expr(lit) when is_atom(lit), do: lit_host(lit)
  defp key_expr(lit) when is_binary(lit), do: lit_host(lit)
  defp key_expr(n) when is_integer(n), do: Integer.to_string(n)

  defp kind_js(:nat), do: "\"nat\""

  defp kind_js({:bin, z, d1, d2}) do
    "{ z: \"#{tag(z)}\", d1: \"#{tag(d1)}\", d2: \"#{tag(d2)}\" }"
  end

  defp reserved_js(list) do
    "[" <> Enum.map_join(list, ", ", fn s -> "\"#{js(s)}\"" end) <> "]"
  end

  defp pack_js({:pair, nil_c, cons}), do: {"(k, v) => [k, v]", nil_c, cons}

  defp pack_js({:record, ctor, nil_c, cons}) do
    {"(k, v) => ({ tag: \"#{tag(ctor)}\", fields: [k, v] })", nil_c, cons}
  end

  defp split_js({:pair, nil_c, cons}) do
    {"(el) => (Array.isArray(el) && el.length === 2 ? { k: el[0], v: el[1] } : { error: { path: [], reason: { k: \"bad_value\", value: el } } })",
     nil_c, cons}
  end

  defp split_js({:record, ctor, nil_c, cons}) do
    {"(el) => (muro_repr_is_ctor(el, \"#{tag(ctor)}\", 2) ? { k: el.fields[0], v: el.fields[1] } : { error: { path: [], reason: { k: \"bad_value\", value: el } } })",
     nil_c, cons}
  end

  defp fallback_js({:atom, atom}), do: nullary(atom)
  defp fallback_js({:num, n}) when is_integer(n), do: Integer.to_string(n) <> "n"

  defp mode_js(nil), do: "\"nothing\""
  defp mode_js(:drop), do: "\"error\""
  defp mode_js(:pass), do: "\"pass\""

  defp entry_key({:tag, key, _}), do: key
  defp entry_key({:field, key, _}), do: key
  defp entry_key({:opt, key, _, _, _, _}), do: key

  defp arm_ctor({:const, _, ctor}), do: ctor
  defp arm_ctor({:unwrap, ctor, _}), do: ctor
  defp arm_ctor({:tuple, ctor, _}), do: ctor
  defp arm_ctor({:map, _, ctor, _}), do: ctor

  defp field_slots(parts) do
    Enum.count(parts, fn
      {:field, _} -> true
      {:field, _, _} -> true
      {:opt, _, _, _, _, _} -> true
      _ -> false
    end)
  end

  defp field_refs(parts) do
    {names, _} =
      Enum.reduce(parts, {[], 0}, fn
        {:field, _}, {ns, i} -> {ns ++ ["f#{i}"], i + 1}
        {:field, _, _}, {ns, i} -> {ns ++ ["f#{i}"], i + 1}
        {:opt, _, _, _, _, _}, {ns, i} -> {ns ++ ["f#{i}"], i + 1}
        _, acc -> acc
      end)

    names
  end

  defp nullary(ctor), do: data(ctor, [])

  defp data(ctor, fields) do
    "{ tag: \"#{tag(ctor)}\", fields: [#{Enum.join(fields, ", ")}] }"
  end

  defp tag(atom), do: js(Atom.to_string(atom))

  defp bad, do: "{ error: { path: [], reason: { k: \"bad_value\", value } } }"
  defp bad_of(v), do: "{ error: { path: [], reason: { k: \"bad_value\", value: #{v} } } }"

  defp js(s) when is_binary(s) do
    s
    |> String.replace("\\", "\\\\")
    |> String.replace("\"", "\\\"")
    |> String.replace("\n", "\\n")
    |> String.replace("\r", "\\r")
    |> String.replace("\t", "\\t")
  end

  # -- names -----------------------------------------------------------------

  defp collide(source, taken, plans) do
    hit = Enum.find(defined(source), &MapSet.member?(taken, &1))

    if hit do
      owner =
        Enum.find(plans, fn {d, _} ->
          fun = Repr.snake_ident(d.name)

          hit in [
            "decode_" <> fun,
            "encode_" <> fun,
            "muro_repr_dec_" <> fun,
            "muro_repr_enc_" <> fun
          ]
        end)

      d = if owner, do: elem(owner, 0), else: elem(hd(plans), 0)
      {:error, blame(d, "#{hit} collides with an existing JavaScript name")}
    else
      :ok
    end
  end

  defp defined(source) do
    Regex.scan(~r/function ([A-Za-z0-9_]+)\(/, source) |> Enum.map(fn [_, name] -> name end)
  end

  defp blame(d, msg) do
    "#{Muro.Print.loc_prefix(Map.get(d, :loc))}repr #{d.name}: #{msg}"
  end

  defp export_names(set, plans) do
    codecs =
      Enum.flat_map(plans, fn {d, _} ->
        fun = Repr.snake_ident(d.name)
        ["decode_" <> fun, "encode_" <> fun]
      end)

    helpers =
      ["muro_repr_table_new", "muro_repr_table_names", "muro_repr_atom"]
      |> Enum.filter(&MapSet.member?(set, &1))

    codecs ++ helpers
  end

  defp clauses(names) do
    Enum.map(names, fn
      "muro_repr_table_new" -> "export function muro_repr_table_new(names)"
      "muro_repr_table_names" -> "export function muro_repr_table_names(table)"
      "muro_repr_atom" -> "export function muro_repr_atom(name)"
      "decode_" <> _ = name -> "export function #{name}(value, table)"
      "encode_" <> _ = name -> "export function #{name}(value, table)"
    end)
  end

  defp type_spell(name, types) do
    case Map.get(types, name) do
      %{spell: spell} -> spell
      _ -> if(name == "Nat", do: "Nat", else: "unknown")
    end
  end

  defp dts(plans, types, set) do
    sigs =
      Enum.map_join(plans, "\n", fn {d, _} ->
        fun = Repr.snake_ident(d.name)
        spell = type_spell(d.name, types)

        """
        export function decode_#{fun}(value: unknown, table?: ReprTable): ReprDecode<#{spell}>;
        export function encode_#{fun}(value: #{spell}, table: ReprTable): ReprEncode;
        """
        |> String.trim()
      end)

    helpers =
      [
        if(MapSet.member?(set, "muro_repr_table_new"),
          do: "export function muro_repr_table_new(names?: readonly string[]): ReprTable;"
        ),
        if(MapSet.member?(set, "muro_repr_table_names"),
          do: "export function muro_repr_table_names(table: ReprTable): readonly string[];"
        ),
        if(MapSet.member?(set, "muro_repr_atom"),
          do: "export function muro_repr_atom(name: string): { readonly atom: string };"
        )
      ]
      |> Enum.reject(&is_nil/1)
      |> Enum.join("\n")

    String.trim(dts_types() <> "\n\n" <> sigs <> "\n" <> helpers)
  end

  defp dts_types do
    """
    export type ReprPath = readonly (string | number | { readonly k: "key"; readonly key: unknown } | { readonly atom: string })[];
    export type ReprReason =
      | { readonly k: "not_boolean"; readonly value: unknown }
      | { readonly k: "not_integer"; readonly value: unknown }
      | { readonly k: "negative_integer"; readonly value: unknown }
      | { readonly k: "nat_too_large"; readonly value: unknown }
      | { readonly k: "not_map"; readonly value: unknown }
      | { readonly k: "missing_key"; readonly key: unknown }
      | { readonly k: "unexpected_key"; readonly key: unknown }
      | { readonly k: "nil_not_allowed"; readonly value: unknown }
      | { readonly k: "no_variant"; readonly names: readonly string[]; readonly value: unknown }
      | { readonly k: "not_list"; readonly value: unknown }
      | { readonly k: "not_tuple"; readonly value: unknown }
      | { readonly k: "wrong_tuple_size"; readonly size: number; readonly value: unknown }
      | { readonly k: "expected"; readonly literal: unknown; readonly value: unknown }
      | { readonly k: "ambiguous_key"; readonly key: unknown }
      | { readonly k: "not_string"; readonly value: unknown }
      | { readonly k: "too_many_names"; readonly max: number }
      | { readonly k: "keys_collide"; readonly a: unknown; readonly b: unknown }
      | { readonly k: "bad_table"; readonly message: string }
      | { readonly k: "bad_value"; readonly value: unknown }
      | { readonly k: "no_name"; readonly index: number; readonly message: string }
      | { readonly k: "reserved_name"; readonly name: string; readonly message: string }
      | { readonly k: "duplicate_key"; readonly key: unknown; readonly message: string };
    export type ReprTable = { readonly by_name: { readonly [name: string]: number }; readonly by_index: { readonly [index: string]: string } };
    export type ReprDecode<T> = { readonly ok: { readonly value: T; readonly table: ReprTable } } | { readonly error: { readonly path: ReprPath; readonly reason: ReprReason } };
    export type ReprEncode = { readonly ok: unknown } | { readonly error: { readonly path: ReprPath; readonly reason: ReprReason } };
    """
    |> String.trim()
  end

  # -- helper selection ------------------------------------------------------

  defp close(needed, helpers), do: Enum.reduce(needed, MapSet.new(), &pull(&1, &2, helpers))

  defp pull(name, acc, helpers) do
    if MapSet.member?(acc, name) do
      acc
    else
      acc = MapSet.put(acc, name)

      case Map.get(helpers, name) do
        nil -> acc
        src -> Enum.reduce(called(src), acc, &pull(&1, &2, helpers))
      end
    end
  end

  defp called(source) do
    Regex.scan(~r/muro_repr_[a-z0-9_]+/, source) |> Enum.map(fn [name] -> name end) |> Enum.uniq()
  end

  defp add_atom(set) do
    if MapSet.member?(set, "muro_repr_is_atom") or MapSet.member?(set, "muro_repr_atom") do
      set
      |> MapSet.put("muro_repr_is_atom")
      |> MapSet.put("muro_repr_atom")
      |> MapSet.put("muro_repr_atom_sym")
    else
      set
    end
  end

  defp emit_consts(set) do
    parts = []

    parts =
      if MapSet.member?(set, "muro_repr_nat_max"),
        do: parts ++ ["const muro_repr_nat_max = 1_000_000;"],
        else: parts

    parts =
      if MapSet.member?(set, "muro_repr_atom_sym"),
        do: parts ++ ["const muro_repr_atom_sym = Symbol.for(\"muro.repr.atom\");"],
        else: parts

    Enum.join(parts, "\n")
  end

  defp emit_helpers(set, helpers) do
    set
    |> MapSet.to_list()
    |> Enum.filter(&(Map.has_key?(helpers, &1) and not MapSet.member?(@consts, &1)))
    |> Enum.sort_by(&helper_rank/1)
    |> Enum.map_join("\n\n", fn name ->
      src = helpers |> Map.fetch!(name) |> String.trim()

      if MapSet.member?(@exported, name) do
        String.replace_prefix(src, "function ", "export function ")
      else
        src
      end
    end)
  end

  defp helper_rank(name) do
    case Enum.find_index(@helper_order, &(&1 == name)) do
      nil -> 1000
      i -> i
    end
  end

  defp interned_kinds(plans) do
    Enum.reduce(plans, MapSet.new(), fn {_, codec}, acc ->
      walk(codec, acc, fn
        {:interned, :nat, _}, a -> MapSet.put(a, :nat)
        {:interned, {:bin, _, _, _}, _}, a -> MapSet.put(a, :bin)
        _, a -> a
      end)
    end)
  end

  defp num_fallback?(plans) do
    Enum.any?(plans, fn {_, codec} ->
      walk(codec, false, fn
        {:else, _, {:num, _}}, _ -> true
        _, acc -> acc
      end)
    end)
  end

  defp walk(codec, acc, fun) do
    acc = fun.(codec, acc)

    case codec do
      {:list, _, _, el} -> walk(el, acc, fun)
      {:nullable, _, _, el} -> walk(el, acc, fun)
      {:wrap, _, el} -> walk(el, acc, fun)
      {:unwrap, _, el} -> walk(el, acc, fun)
      {:opt, _, _, _, el, _} -> walk(el, acc, fun)
      {:map_of, key, val, _} -> walk(val, walk(key, acc, fun), fun)
      {:else, inner, _} -> walk(inner, acc, fun)
      {:tuple, _, comps} -> Enum.reduce(comps, acc, &walk_part(&1, &2, fun))
      {:map, _, _, entries} -> Enum.reduce(entries, acc, &walk_part(&1, &2, fun))
      {:choice, arms} -> Enum.reduce(arms, acc, &walk(&1, &2, fun))
      _ -> acc
    end
  end

  defp walk_part({:field, codec}, acc, fun), do: walk(codec, acc, fun)
  defp walk_part({:field, _, codec}, acc, fun), do: walk(codec, acc, fun)
  defp walk_part({:opt, _, _, _, codec, _}, acc, fun), do: walk(codec, acc, fun)
  defp walk_part(_, acc, _fun), do: acc

  defp ind(text) do
    text
    |> String.trim()
    |> String.split("\n")
    |> Enum.map_join("\n", fn
      "" -> ""
      line -> "  " <> line
    end)
  end

  # -- helper sources --------------------------------------------------------

  defp helper_sources(kinds, keep_nat) do
    %{
      "muro_repr_table_new" => table_new_src(),
      "muro_repr_table_names" => table_names_src(),
      "muro_repr_table_check" => table_check_src(),
      "muro_repr_table_copy" => table_copy_src(),
      "muro_repr_inspect" => inspect_src(),
      "muro_repr_is_ctor" => is_ctor_src(),
      "muro_repr_is_int" => is_int_src(),
      "muro_repr_is_atom" => is_atom_src(),
      "muro_repr_atom" => atom_src(),
      "muro_repr_is_plain" => is_plain_src(),
      "muro_repr_is_map" => is_map_src(),
      "muro_repr_is_data" => is_data_src(),
      "muro_repr_show" => show_src(),
      "muro_repr_key_eq" => key_eq_src(),
      "muro_repr_lit_eq" => lit_eq_src(),
      "muro_repr_lookup" => lookup_src(),
      "muro_repr_keys" => keys_src(),
      "muro_repr_keys_have" => keys_have_src(),
      "muro_repr_path_key" => path_key_src(),
      "muro_repr_has_lit" => has_lit_src(),
      "muro_repr_fetch" => fetch_src(),
      "muro_repr_tag" => tag_src(),
      "muro_repr_expect" => expect_src(),
      "muro_repr_atom_name" => atom_name_src(),
      "muro_repr_wire_rank" => wire_rank_src(),
      "muro_repr_wire_cmp" => wire_cmp_src(),
      "muro_repr_array_cmp" => array_cmp_src(),
      "muro_repr_map_cmp" => map_cmp_src(),
      "muro_repr_entries" => entries_src(),
      "muro_repr_no_extra" => no_extra_src(),
      "muro_repr_ambiguous" => ambiguous_src(),
      "muro_repr_decode_nat" => decode_nat_src(),
      "muro_repr_encode_nat" => encode_nat_src(),
      "muro_repr_decode_bool" => decode_bool_src(),
      "muro_repr_encode_bool" => encode_bool_src(),
      "muro_repr_decode_optional" => optional_src(),
      "muro_repr_put_optional" => put_optional_src(),
      "muro_repr_decode_nullable" => nullable_dec_src(),
      "muro_repr_encode_nullable" => nullable_enc_src(),
      "muro_repr_list_decode" => list_dec_src(),
      "muro_repr_list_encode" => list_enc_src(),
      "muro_repr_decode_interned" => interned_dec_src(),
      "muro_repr_intern_index" => intern_index_src(),
      "muro_repr_name_term" => name_term_src(kinds),
      "muro_repr_name_index" => name_index_src(kinds),
      "muro_repr_encode_interned" => interned_enc_src(),
      "muro_repr_bin_from" => bin_from_src(),
      "muro_repr_bin_index" => bin_index_src(),
      "muro_repr_term_eq" => term_eq_src(),
      "muro_repr_map_put" => map_put_src(),
      "muro_repr_finish_map" => finish_map_src(),
      "muro_repr_finish_entries" => finish_entries_src(),
      "muro_repr_map_of_decode" => map_of_dec_src(),
      "muro_repr_map_of_encode" => map_of_enc_src(),
      "muro_repr_path_eq" => path_eq_src(),
      "muro_repr_seg_eq" => seg_eq_src(),
      "muro_repr_else" => else_src(keep_nat)
    }
  end

  defp table_new_src do
    """
    function muro_repr_table_new(names) {
      if (names === undefined) return { by_name: Object.create(null), by_index: Object.create(null) };
      if (!Array.isArray(names)) throw new Error("muro_repr_table_new expects a list of binaries, got: " + muro_repr_inspect(names));
      const by_name = Object.create(null);
      const by_index = Object.create(null);
      for (let i = 0; i < names.length; i++) {
        const name = names[i];
        if (typeof name !== "string") throw new Error("muro_repr_table_new expects a binary, got: " + muro_repr_inspect(name));
        if (Object.prototype.hasOwnProperty.call(by_name, name)) throw new Error("muro_repr_table_new duplicate name " + JSON.stringify(name));
        by_name[name] = i;
        by_index[String(i)] = name;
      }
      return { by_name, by_index };
    }
    """
  end

  defp table_names_src do
    """
    function muro_repr_table_names(table) {
      const checked = muro_repr_table_check(table, "muro_repr_table_names");
      if (checked.error) throw new Error(checked.error.reason.message);
      const by_index = checked.ok.by_index;
      const keys = Object.keys(by_index);
      keys.sort((a, b) => Number(a) - Number(b));
      return keys.map((k) => by_index[k]);
    }
    """
  end

  defp table_check_src do
    """
    function muro_repr_table_check(table, fun) {
      const message = fun + " table must be %{by_name: %{}, by_index: %{}}";
      const bad = { error: { path: [], reason: { k: "bad_table", message } } };
      if (table === null || typeof table !== "object" || Array.isArray(table) || table instanceof Map) return bad;
      if (Object.keys(table).length !== 2) return bad;
      if (!Object.prototype.hasOwnProperty.call(table, "by_name") || !Object.prototype.hasOwnProperty.call(table, "by_index")) return bad;
      const by_name = table.by_name;
      const by_index = table.by_index;
      if (by_name === null || typeof by_name !== "object" || Array.isArray(by_name) || by_name instanceof Map) return bad;
      if (by_index === null || typeof by_index !== "object" || Array.isArray(by_index) || by_index instanceof Map) return bad;
      return { ok: table };
    }
    """
  end

  defp table_copy_src do
    """
    function muro_repr_table_copy(table) {
      const by_name = Object.create(null);
      const by_index = Object.create(null);
      for (const k of Object.keys(table.by_name)) by_name[k] = table.by_name[k];
      for (const k of Object.keys(table.by_index)) by_index[k] = table.by_index[k];
      return { by_name, by_index };
    }
    """
  end

  defp inspect_src do
    """
    function muro_repr_inspect(value) {
      if (typeof value === "string") return JSON.stringify(value);
      if (typeof value === "bigint") return value.toString();
      if (typeof value === "number") return Object.is(value, -0) ? "-0" : String(value);
      if (typeof value === "boolean") return value ? "true" : "false";
      if (value === null) return "nil";
      if (value === undefined) return "undefined";
      if (Array.isArray(value)) return "[" + value.map(muro_repr_inspect).join(", ") + "]";
      if (typeof value === "function") return "#Function";
      try { return JSON.stringify(value); } catch (_e) { return Object.prototype.toString.call(value); }
    }
    """
  end

  defp is_ctor_src do
    """
    function muro_repr_is_ctor(value, tag, n) {
      return !!value && typeof value === "object" && !Array.isArray(value) && value.tag === tag && Array.isArray(value.fields) && value.fields.length === n;
    }
    """
  end

  defp is_int_src do
    """
    function muro_repr_is_int(value) {
      return typeof value === "bigint" || (typeof value === "number" && Number.isInteger(value));
    }
    """
  end

  defp is_atom_src do
    """
    function muro_repr_is_atom(value) {
      return !!value && typeof value === "object" && !Array.isArray(value) && typeof value.atom === "string" && value[muro_repr_atom_sym] === value.atom && Object.keys(value).length === 1;
    }
    """
  end

  defp atom_src do
    """
    function muro_repr_atom(name) {
      const o = { atom: name };
      o[muro_repr_atom_sym] = name;
      return o;
    }
    """
  end

  defp is_plain_src do
    """
    function muro_repr_is_plain(value) {
      return value !== null && typeof value === "object" && !Array.isArray(value) && !(value instanceof Map) && !muro_repr_is_atom(value);
    }
    """
  end

  defp is_map_src do
    """
    function muro_repr_is_map(value) {
      return value instanceof Map || muro_repr_is_plain(value);
    }
    """
  end

  defp is_data_src do
    """
    function muro_repr_is_data(value) {
      return !!value && typeof value === "object" && !Array.isArray(value) && typeof value.tag === "string" && Array.isArray(value.fields);
    }
    """
  end

  defp show_src do
    """
    function muro_repr_show(value) {
      if (muro_repr_is_atom(value)) return { atom: value.atom };
      return value;
    }
    """
  end

  defp key_eq_src do
    """
    function muro_repr_key_eq(a, b) {
      if (muro_repr_is_atom(a) || muro_repr_is_atom(b)) return muro_repr_is_atom(a) && muro_repr_is_atom(b) && a.atom === b.atom;
      if (typeof a === "number" && typeof b === "bigint") return Number.isSafeInteger(a) && BigInt(a) === b;
      if (typeof a === "bigint" && typeof b === "number") return Number.isSafeInteger(b) && a === BigInt(b);
      if (typeof a === "bigint" && typeof b === "bigint") return a === b;
      return Object.is(a, b);
    }
    """
  end

  defp lit_eq_src do
    """
    function muro_repr_lit_eq(value, literal) {
      if (muro_repr_is_atom(literal)) return muro_repr_is_atom(value) && value.atom === literal.atom;
      if (typeof literal === "number" || typeof literal === "bigint") {
        if (!muro_repr_is_int(value)) return false;
        const left = typeof value === "bigint" ? value : BigInt(value);
        const right = typeof literal === "bigint" ? literal : BigInt(literal);
        return left === right;
      }
      return Object.is(value, literal);
    }
    """
  end

  defp lookup_src do
    """
    function muro_repr_lookup(value, key) {
      if (value instanceof Map) {
        for (const [k, v] of value) if (muro_repr_key_eq(k, key)) return { found: true, value: v };
        return { found: false };
      }
      if (!muro_repr_is_plain(value) || typeof key !== "string") return { found: false };
      if (Object.prototype.hasOwnProperty.call(value, key)) return { found: true, value: value[key] };
      return { found: false };
    }
    """
  end

  defp keys_src do
    """
    function muro_repr_keys(value) {
      if (value instanceof Map) return Array.from(value.keys());
      if (muro_repr_is_plain(value)) return Object.keys(value);
      return [];
    }
    """
  end

  defp keys_have_src do
    """
    function muro_repr_keys_have(keys, key) {
      for (const k of keys) if (muro_repr_key_eq(k, key)) return true;
      return false;
    }
    """
  end

  defp path_key_src do
    """
    function muro_repr_path_key(path, key) {
      return path.concat([muro_repr_show(key)]);
    }
    """
  end

  defp has_lit_src do
    """
    function muro_repr_has_lit(value, key, literal) {
      const got = muro_repr_lookup(value, key);
      return got.found && muro_repr_lit_eq(got.value, literal);
    }
    """
  end

  defp fetch_src do
    """
    function muro_repr_fetch(value, path, key) {
      const got = muro_repr_lookup(value, key);
      if (!got.found) return { error: { path, reason: { k: "missing_key", key: muro_repr_show(key) } } };
      return { ok: got.value };
    }
    """
  end

  defp tag_src do
    """
    function muro_repr_tag(value, path, key, literal) {
      const got = muro_repr_lookup(value, key);
      if (!got.found) return { error: { path, reason: { k: "missing_key", key: muro_repr_show(key) } } };
      if (muro_repr_lit_eq(got.value, literal)) return { ok: true };
      return { error: { path: muro_repr_path_key(path, key), reason: { k: "expected", literal: muro_repr_show(literal), value: got.value } } };
    }
    """
  end

  defp expect_src do
    """
    function muro_repr_expect(value, path, literal) {
      if (muro_repr_lit_eq(value, literal)) return { ok: true };
      return { error: { path, reason: { k: "expected", literal: muro_repr_show(literal), value } } };
    }
    """
  end

  defp atom_name_src do
    """
    function muro_repr_atom_name(value) {
      if (value === null) return "nil";
      if (value === true) return "true";
      if (value === false) return "false";
      if (muro_repr_is_atom(value)) return value.atom;
      return "";
    }
    """
  end

  defp wire_rank_src do
    """
    function muro_repr_wire_rank(value) {
      if (typeof value === "number" || typeof value === "bigint") return 0;
      if (typeof value === "boolean" || value === null || muro_repr_is_atom(value)) return 1;
      if (Array.isArray(value)) return 2;
      if (muro_repr_is_map(value)) return 3;
      if (typeof value === "string") return 4;
      return 5;
    }
    """
  end

  defp wire_cmp_src do
    """
    function muro_repr_wire_cmp(a, b) {
      const ra = muro_repr_wire_rank(a);
      const rb = muro_repr_wire_rank(b);
      if (ra !== rb) return ra < rb ? -1 : 1;
      if (ra === 0) {
        if (!muro_repr_is_int(a) || !muro_repr_is_int(b)) return Object.is(a, b) ? 0 : (String(a) < String(b) ? -1 : 1);
        const da = typeof a === "bigint" ? a : BigInt(a);
        const db = typeof b === "bigint" ? b : BigInt(b);
        return da < db ? -1 : da > db ? 1 : 0;
      }
      if (ra === 1) {
        const na = muro_repr_atom_name(a);
        const nb = muro_repr_atom_name(b);
        return na < nb ? -1 : na > nb ? 1 : 0;
      }
      if (ra === 2) return muro_repr_array_cmp(a, b);
      if (ra === 3) return muro_repr_map_cmp(a, b);
      if (ra === 4) return a < b ? -1 : a > b ? 1 : 0;
      return 0;
    }
    """
  end

  defp array_cmp_src do
    """
    function muro_repr_array_cmp(a, b) {
      const n = Math.min(a.length, b.length);
      for (let i = 0; i < n; i++) {
        const c = muro_repr_wire_cmp(a[i], b[i]);
        if (c !== 0) return c;
      }
      return a.length === b.length ? 0 : a.length < b.length ? -1 : 1;
    }
    """
  end

  defp map_cmp_src do
    """
    function muro_repr_map_cmp(a, b) {
      const ae = muro_repr_entries(a).sort((x, y) => muro_repr_wire_cmp(x[0], y[0]));
      const be = muro_repr_entries(b).sort((x, y) => muro_repr_wire_cmp(x[0], y[0]));
      if (ae.length !== be.length) return ae.length < be.length ? -1 : 1;
      for (let i = 0; i < ae.length; i++) {
        const ck = muro_repr_wire_cmp(ae[i][0], be[i][0]);
        if (ck !== 0) return ck;
        const cv = muro_repr_wire_cmp(ae[i][1], be[i][1]);
        if (cv !== 0) return cv;
      }
      return 0;
    }
    """
  end

  defp entries_src do
    """
    function muro_repr_entries(value) {
      if (value instanceof Map) return Array.from(value.entries());
      const out = [];
      for (const k of Object.keys(value)) out.push([k, value[k]]);
      return out;
    }
    """
  end

  defp no_extra_src do
    """
    function muro_repr_no_extra(value, path, keys) {
      const extra = [];
      for (const key of muro_repr_keys(value)) if (!muro_repr_keys_have(keys, key)) extra.push(key);
      extra.sort(muro_repr_wire_cmp);
      if (extra.length === 0) return { ok: true };
      return { error: { path, reason: { k: "unexpected_key", key: muro_repr_show(extra[0]) } } };
    }
    """
  end

  defp ambiguous_src do
    """
    function muro_repr_ambiguous(value, path, keys) {
      const host = muro_repr_keys(value);
      const atoms = new Map();
      for (const key of host) if (muro_repr_is_atom(key)) atoms.set(key.atom, key);
      for (const key of keys) {
        if (typeof key === "string") {
          const atom = atoms.get(key);
          if (atom !== undefined && !muro_repr_keys_have(keys, atom)) return { error: { path, reason: { k: "ambiguous_key", key: muro_repr_show(atom) } } };
        } else if (muro_repr_is_atom(key)) {
          const name = key.atom;
          if (muro_repr_keys_have(host, name) && !muro_repr_keys_have(keys, name)) return { error: { path, reason: { k: "ambiguous_key", key: name } } };
        }
      }
      return { ok: true };
    }
    """
  end

  defp decode_nat_src do
    """
    function muro_repr_decode_nat(value, path, table) {
      if (!muro_repr_is_int(value)) return { error: { path, reason: { k: "not_integer", value } } };
      const n = typeof value === "bigint" ? value : BigInt(value);
      if (n < 0n) return { error: { path, reason: { k: "negative_integer", value } } };
      if (n > BigInt(muro_repr_nat_max)) return { error: { path, reason: { k: "nat_too_large", value } } };
      return { ok: { value: n, table } };
    }
    """
  end

  defp encode_nat_src do
    """
    function muro_repr_encode_nat(value) {
      if (typeof value !== "bigint" || value < 0n) return { error: { path: [], reason: { k: "bad_value", value } } };
      if (value <= BigInt(Number.MAX_SAFE_INTEGER)) return { ok: Number(value) };
      return { ok: value };
    }
    """
  end

  defp decode_bool_src do
    """
    function muro_repr_decode_bool(value, path, table) {
      if (value === true) return { ok: { value: { tag: "true", fields: [] }, table } };
      if (value === false) return { ok: { value: { tag: "false", fields: [] }, table } };
      return { error: { path, reason: { k: "not_boolean", value } } };
    }
    """
  end

  defp encode_bool_src do
    """
    function muro_repr_encode_bool(value) {
      if (muro_repr_is_ctor(value, "true", 0)) return { ok: true };
      if (muro_repr_is_ctor(value, "false", 0)) return { ok: false };
      return { error: { path: [], reason: { k: "bad_value", value } } };
    }
    """
  end

  defp optional_src do
    """
    function muro_repr_decode_optional(value, path, table, key, fun, nothing, just, mode) {
      const got = muro_repr_lookup(value, key);
      if (!got.found) return { ok: { value: { tag: nothing, fields: [] }, table } };
      if (got.value === null && mode === "nothing") return { ok: { value: { tag: nothing, fields: [] }, table } };
      if (got.value === null && mode === "error") return { error: { path: muro_repr_path_key(path, key), reason: { k: "nil_not_allowed", value: null } } };
      const step = fun(got.value, muro_repr_path_key(path, key), table);
      if (step.error) return step;
      return { ok: { value: { tag: just, fields: [step.ok.value] }, table: step.ok.table } };
    }
    """
  end

  defp put_optional_src do
    """
    function muro_repr_put_optional(entries, key, nothing, just, value, fun) {
      if (muro_repr_is_ctor(value, nothing, 0)) return { ok: entries };
      if (!muro_repr_is_ctor(value, just, 1)) return { error: { path: [], reason: { k: "bad_value", value } } };
      const step = fun(value.fields[0]);
      if (step.error) return step;
      entries.push([key, step.ok]);
      return { ok: entries };
    }
    """
  end

  defp nullable_dec_src do
    """
    function muro_repr_decode_nullable(value, path, table, nothing, just, fun) {
      if (value === null) return { ok: { value: { tag: nothing, fields: [] }, table } };
      const step = fun(value, path, table);
      if (step.error) return step;
      return { ok: { value: { tag: just, fields: [step.ok.value] }, table: step.ok.table } };
    }
    """
  end

  defp nullable_enc_src do
    """
    function muro_repr_encode_nullable(nothing, just, value, fun) {
      if (muro_repr_is_ctor(value, nothing, 0)) return { ok: null };
      if (!muro_repr_is_ctor(value, just, 1)) return { error: { path: [], reason: { k: "bad_value", value } } };
      return fun(value.fields[0]);
    }
    """
  end

  defp list_dec_src do
    """
    function muro_repr_list_decode(value, path, table, fun, nilCtor, cons) {
      if (!Array.isArray(value)) return { error: { path, reason: { k: "not_list", value } } };
      const acc = [];
      for (let i = 0; i < value.length; i++) {
        const step = fun(value[i], path.concat([i]), table);
        if (step.error) return step;
        acc.push(step.ok.value);
        table = step.ok.table;
      }
      let packed = { tag: nilCtor, fields: [] };
      for (let i = acc.length - 1; i >= 0; i--) packed = { tag: cons, fields: [acc[i], packed] };
      return { ok: { value: packed, table } };
    }
    """
  end

  defp list_enc_src do
    """
    function muro_repr_list_encode(value, nilCtor, cons, fun) {
      const out = [];
      let cur = value;
      while (true) {
        if (muro_repr_is_ctor(cur, nilCtor, 0)) return { ok: out };
        if (!muro_repr_is_ctor(cur, cons, 2)) return { error: { path: [], reason: { k: "bad_value", value } } };
        const step = fun(cur.fields[0]);
        if (step.error) return step;
        out.push(step.ok);
        cur = cur.fields[1];
      }
    }
    """
  end

  defp interned_dec_src do
    """
    function muro_repr_decode_interned(value, path, table, kind, reserved) {
      if (typeof value !== "string" || reserved.indexOf(value) !== -1) return { error: { path, reason: { k: "not_string", value } } };
      return muro_repr_intern_index(value, path, table, kind);
    }
    """
  end

  defp intern_index_src do
    """
    function muro_repr_intern_index(name, path, table, kind) {
      const by_name = table.by_name;
      if (Object.prototype.hasOwnProperty.call(by_name, name)) return { ok: { value: muro_repr_name_term(by_name[name], kind), table } };
      const i = Object.keys(by_name).length;
      if (i > muro_repr_nat_max) return { error: { path, reason: { k: "too_many_names", max: muro_repr_nat_max } } };
      const next = muro_repr_table_copy(table);
      next.by_name[name] = i;
      next.by_index[String(i)] = name;
      return { ok: { value: muro_repr_name_term(i, kind), table: next } };
    }
    """
  end

  defp name_term_src(kinds) do
    nat? = MapSet.member?(kinds, :nat)
    bin? = MapSet.member?(kinds, :bin)

    body =
      cond do
        nat? and bin? ->
          "if (kind === \"nat\") return BigInt(i);\n  return muro_repr_bin_from(i, kind);"

        nat? ->
          "return BigInt(i);"

        true ->
          "return muro_repr_bin_from(i, kind);"
      end

    """
    function muro_repr_name_term(i, kind) {
      #{body}
    }
    """
  end

  defp name_index_src(kinds) do
    nat? = MapSet.member?(kinds, :nat)
    bin? = MapSet.member?(kinds, :bin)

    nat_body = """
    if (typeof term !== "bigint" || term < 0n || term > BigInt(Number.MAX_SAFE_INTEGER)) return { error: { path: [], reason: { k: "bad_value", value: term } } };
    return { ok: Number(term) };
    """

    body =
      cond do
        nat? and bin? ->
          "if (kind === \"nat\") {\n    #{String.trim(nat_body)}\n  }\n  return muro_repr_bin_index(term, kind);"

        nat? ->
          String.trim(nat_body)

        true ->
          "return muro_repr_bin_index(term, kind);"
      end

    """
    function muro_repr_name_index(term, kind) {
      #{body}
    }
    """
  end

  defp interned_enc_src do
    """
    function muro_repr_encode_interned(term, table, kind, reserved, fun) {
      const idx = muro_repr_name_index(term, kind);
      if (idx.error) return idx;
      const key = String(idx.ok);
      if (!Object.prototype.hasOwnProperty.call(table.by_index, key)) {
        const message = fun + ": no name for index " + String(idx.ok);
        return { error: { path: [], reason: { k: "no_name", index: idx.ok, message } } };
      }
      const name = table.by_index[key];
      if (reserved.indexOf(name) !== -1) {
        const message = fun + ": name " + JSON.stringify(name) + " is reserved by a sibling constructor";
        return { error: { path: [], reason: { k: "reserved_name", name, message } } };
      }
      return { ok: name };
    }
    """
  end

  defp bin_from_src do
    """
    function muro_repr_bin_from(i, kind) {
      if (i === 0) return { tag: kind.z, fields: [] };
      const digits = [];
      let n = i;
      while (n > 0) {
        if (n % 2 === 1) { digits.push(kind.d1); n = (n - 1) / 2; }
        else { digits.push(kind.d2); n = (n - 2) / 2; }
      }
      let acc = { tag: kind.z, fields: [] };
      for (let k = digits.length - 1; k >= 0; k--) acc = { tag: digits[k], fields: [acc] };
      return acc;
    }
    """
  end

  defp bin_index_src do
    """
    function muro_repr_bin_index(term, kind) {
      const digits = [];
      let cur = term;
      while (true) {
        if (muro_repr_is_ctor(cur, kind.z, 0)) break;
        if (muro_repr_is_ctor(cur, kind.d1, 1)) { digits.push(1); cur = cur.fields[0]; continue; }
        if (muro_repr_is_ctor(cur, kind.d2, 1)) { digits.push(2); cur = cur.fields[0]; continue; }
        return { error: { path: [], reason: { k: "bad_value", value: term } } };
      }
      digits.reverse();
      let acc = 0;
      for (const d of digits) acc = acc * 2 + d;
      return { ok: acc };
    }
    """
  end

  defp term_eq_src do
    """
    function muro_repr_term_eq(a, b) {
      if (typeof a === "bigint" && typeof b === "bigint") return a === b;
      if (a === null || b === null) return a === b;
      if (typeof a !== "object" || typeof b !== "object") return Object.is(a, b);
      if (Array.isArray(a) || Array.isArray(b)) {
        if (!Array.isArray(a) || !Array.isArray(b) || a.length !== b.length) return false;
        for (let i = 0; i < a.length; i++) if (!muro_repr_term_eq(a[i], b[i])) return false;
        return true;
      }
      if (muro_repr_is_data(a) && muro_repr_is_data(b)) {
        if (a.tag !== b.tag || a.fields.length !== b.fields.length) return false;
        for (let i = 0; i < a.fields.length; i++) if (!muro_repr_term_eq(a.fields[i], b.fields[i])) return false;
        return true;
      }
      return false;
    }
    """
  end

  defp map_put_src do
    """
    function muro_repr_map_put(map, key, value, fun) {
      for (const k of map.keys()) {
        if (muro_repr_key_eq(k, key)) {
          const shown = muro_repr_is_atom(key) ? ":" + key.atom : muro_repr_inspect(key);
          const message = fun + ": duplicate map key " + shown;
          return { error: { path: [], reason: { k: "duplicate_key", key: muro_repr_show(key), message } } };
        }
      }
      map.set(key, value);
      return { ok: map };
    }
    """
  end

  defp finish_map_src do
    """
    function muro_repr_finish_map(map) {
      let strings = true;
      for (const k of map.keys()) if (typeof k !== "string") strings = false;
      if (!strings) return { ok: map };
      const o = Object.create(null);
      for (const [k, v] of map) o[k] = v;
      return { ok: o };
    }
    """
  end

  defp finish_entries_src do
    """
    function muro_repr_finish_entries(entries) {
      const map = new Map();
      for (const [k, v] of entries) map.set(k, v);
      return muro_repr_finish_map(map);
    }
    """
  end

  defp map_of_dec_src do
    """
    function muro_repr_map_of_decode(value, path, table, keyFun, valFun, elemFun, nilCtor, cons) {
      if (!muro_repr_is_map(value)) return { error: { path, reason: { k: "not_map", value } } };
      const pairs = muro_repr_entries(value);
      pairs.sort((a, b) => muro_repr_wire_cmp(a[0], b[0]));
      const acc = [];
      const seen = [];
      for (let i = 0; i < pairs.length; i++) {
        const wk = pairs[i][0];
        const wv = pairs[i][1];
        const ks = keyFun(wk, path.concat([{ k: "key", key: muro_repr_show(wk) }]), table);
        if (ks.error) return ks;
        const mk = ks.ok.value;
        table = ks.ok.table;
        let prev = null;
        for (const s of seen) if (muro_repr_term_eq(s.mk, mk)) prev = s;
        if (prev) {
          const ordered = muro_repr_wire_cmp(prev.wk, wk) <= 0 ? [prev.wk, wk] : [wk, prev.wk];
          return { error: { path, reason: { k: "keys_collide", a: muro_repr_show(ordered[0]), b: muro_repr_show(ordered[1]) } } };
        }
        const vs = valFun(wv, path.concat([muro_repr_show(wk)]), table);
        if (vs.error) return vs;
        table = vs.ok.table;
        seen.push({ mk, wk });
        acc.push(elemFun(mk, vs.ok.value));
      }
      let packed = { tag: nilCtor, fields: [] };
      for (let i = acc.length - 1; i >= 0; i--) packed = { tag: cons, fields: [acc[i], packed] };
      return { ok: { value: packed, table } };
    }
    """
  end

  defp map_of_enc_src do
    """
    function muro_repr_map_of_encode(value, split, nilCtor, cons, keyFun, valFun, fun) {
      const acc = new Map();
      let cur = value;
      while (true) {
        if (muro_repr_is_ctor(cur, nilCtor, 0)) return muro_repr_finish_map(acc);
        if (!muro_repr_is_ctor(cur, cons, 2)) return { error: { path: [], reason: { k: "bad_value", value: cur } } };
        const parts = split(cur.fields[0]);
        if (parts.error) return parts;
        const ks = keyFun(parts.k);
        if (ks.error) return ks;
        const vs = valFun(parts.v);
        if (vs.error) return vs;
        const put = muro_repr_map_put(acc, ks.ok, vs.ok, fun);
        if (put.error) return put;
        cur = cur.fields[1];
      }
    }
    """
  end

  defp path_eq_src do
    """
    function muro_repr_path_eq(a, b) {
      if (!Array.isArray(a) || !Array.isArray(b) || a.length !== b.length) return false;
      for (let i = 0; i < a.length; i++) if (!muro_repr_seg_eq(a[i], b[i])) return false;
      return true;
    }
    """
  end

  defp seg_eq_src do
    """
    function muro_repr_seg_eq(a, b) {
      if (typeof a === "number" && typeof b === "number") return Object.is(a, b);
      if (typeof a === "string" && typeof b === "string") return a === b;
      if (typeof a === "bigint" && typeof b === "bigint") return a === b;
      if (a === null || b === null || typeof a !== "object" || typeof b !== "object") return Object.is(a, b);
      if (a.k === "key" && b.k === "key") return muro_repr_seg_eq(a.key, b.key);
      if (typeof a.atom === "string" && typeof b.atom === "string" && Object.keys(a).length === 1 && Object.keys(b).length === 1) return a.atom === b.atom;
      return false;
    }
    """
  end

  defp else_src(keep_nat) do
    nat =
      if keep_nat do
        "if (reason && reason.k === \"nat_too_large\") return step;"
      else
        ""
      end

    """
    function muro_repr_else(step, at, incoming, fallback) {
      if (step.ok) return step;
      const reason = step.error && step.error.reason;
      if (reason && reason.k === "ambiguous_key") return step;
      #{nat}
      if (muro_repr_path_eq(step.error.path, at)) return { ok: { value: fallback, table: incoming } };
      return step;
    }
    """
  end
end

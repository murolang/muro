defmodule Muro.Repr do
  @moduledoc """
  Host representations.

  A `repr` is a spec-side, host-side declaration. It is not a kernel term,
  it has no Agda rule, and it never enters a run image. `check_entry/2` is
  the contract `mix muro.check` enforces. `elixir/2` emits `decode_<type>/1`
  and `encode_<type>/1` from the same analysis.

  Decode is total and strict: the result is `{:ok, value}` or
  `{:error, {path, reason}}`, and nothing the repr does not describe becomes
  a default. Encode is for a value the book already proved; a term that is
  not a value of the type raises `FunctionClauseError`.

  An ambiguous repr is refused here, at check time, and the message names
  both constructors. `integer` builds a Peano `Nat` with a tail call and
  refuses an integer above `@muro_repr_nat_max` (1_000_000).
  """

  alias Muro.{Emit, Print}

  @shape_words ~w(boolean integer nil list optional nullable tuple map open)
  @nat_max 1_000_000

  @helper_names %{
    nat: ~w(muro_repr_decode_nat muro_repr_encode_nat muro_repr_nat_from),
    bool: ~w(muro_repr_decode_bool muro_repr_encode_bool),
    fetch: ~w(muro_repr_fetch),
    tag: ~w(muro_repr_tag),
    expect: ~w(muro_repr_expect),
    extra: ~w(muro_repr_no_extra),
    optional: ~w(muro_repr_decode_optional muro_repr_put_optional),
    nullable: ~w(muro_repr_decode_nullable muro_repr_encode_nullable),
    list: ~w(muro_repr_list_decode muro_repr_list_pack muro_repr_list_encode)
  }

  @doc """
  Check one `repr` of a book (named or de Bruijn). `:ok` or `{:error, msg}`.
  The message starts with `line:col`.
  """
  def check_entry(book, %{kind: :repr, name: name} = d) when is_list(book) do
    same = Enum.filter(book, &(Map.get(&1, :kind) == :repr and &1.name == name))

    case same do
      [first, _ | _] when d == first ->
        {:error, dup_msg(same)}

      [_, _ | _] ->
        :ok

      _ ->
        case compile_repr(d, book) do
          {:ok, codec} -> collide(d, codec, book, run_names(book))
          {:error, _} = err -> err
        end
    end
  end

  @doc """
  Elixir source for every `repr` in `book`, in book order.
  `names` is `Muro.Emit.def_names/3` for the runs. `""` when the book has
  no repr. Raises when a repr does not check: emit runs after the check.
  """
  def elixir(book, names) when is_list(book) and is_map(names) do
    reprs = Enum.filter(book, &(Map.get(&1, :kind) == :repr))

    case reprs do
      [] ->
        ""

      _ ->
        case compile_all(reprs, book, names) do
          {:ok, plans} ->
            render(plans)

          {:error, msg} ->
            raise "repr emit: #{msg}"
        end
    end
  end

  defp compile_all(reprs, book, names) do
    case duplicate_group(reprs) do
      nil ->
        Enum.reduce_while(reprs, {:ok, []}, fn d, {:ok, acc} ->
          case compile_repr(d, book) do
            {:ok, codec} ->
              case collide(d, codec, book, names) do
                :ok -> {:cont, {:ok, acc ++ [{d, codec}]}}
                {:error, msg} -> {:halt, {:error, msg}}
              end

            {:error, msg} ->
              {:halt, {:error, msg}}
          end
        end)

      same ->
        {:error, dup_msg(same)}
    end
  end

  defp duplicate_group(reprs) do
    reprs
    |> Enum.group_by(& &1.name)
    |> Enum.find_value(fn {_name, group} -> if length(group) > 1, do: group end)
  end

  defp dup_msg(same) do
    Enum.map_join(same, "\n", fn d ->
      blame(d, "duplicate repr")
    end)
  end

  defp collide(d, codec, book, runs) do
    fun = snake(d.name)
    dec = "decode_" <> fun
    enc = "encode_" <> fun
    feats = features(codec, MapSet.new())

    other =
      Enum.find(book, fn e ->
        Map.get(e, :kind) == :repr and Map.get(e, :name) != d.name and
          snake(Map.get(e, :name, "")) == fun
      end)

    hit = Enum.find(runs, fn {_src, em} -> em == dec or em == enc end)
    helper = helper_hit(feats, runs)

    cond do
      other != nil ->
        {:error, blame(d, "#{dec} collides with repr #{other.name}")}

      is_tuple(hit) ->
        {src, em} = hit
        {:error, blame(d, "#{em} collides with run #{src}")}

      is_tuple(helper) ->
        {src, em} = helper
        {:error, blame(d, "#{em} collides with run #{src}")}

      true ->
        :ok
    end
  end

  defp helper_hit(feats, runs) do
    names =
      feats
      |> Enum.flat_map(fn feat -> Map.get(@helper_names, feat, []) end)
      |> MapSet.new()

    Enum.find(runs, fn {_src, em} -> MapSet.member?(names, em) end)
  end

  defp run_names(book) do
    taken =
      if Enum.any?(book, fn d -> Map.get(d, :mode) == :run and has_toi64?(Map.get(d, :body)) end),
        do: MapSet.new(["muro_nat_to_int"]),
        else: MapSet.new()

    Emit.def_names(book, &Emit.elixir_base/1, taken)
  end

  defp has_toi64?({:toi64, _}), do: true
  defp has_toi64?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&has_toi64?/1)
  defp has_toi64?(t) when is_list(t), do: Enum.any?(t, &has_toi64?/1)
  defp has_toi64?(_), do: false

  # -- compile ---------------------------------------------------------------

  defp compile_repr(d, book) do
    ctx = %{
      book: book,
      entry: d,
      form: book_form(book),
      reprs: repr_map(book),
      in_map: false,
      ctor: nil,
      data: nil
    }

    case subject(book, d.name) do
      :missing ->
        {:error, blame(d, "unknown type #{d.name}")}

      {:params, _} ->
        {:error, blame(d, "#{d.name} has parameters")}

      {:indices, _} ->
        {:error, blame(d, "#{d.name} has indices")}

      :nat ->
        if d.body == {:integer} do
          {:ok, {:nat}}
        else
          {:error, blame(d, "Nat is represented by integer")}
        end

      {:data, data} ->
        ctx = Map.put(ctx, :data, data)

        with {:ok, codec} <- compile_body(d.body, data, ctx),
             :ok <- consume_ok(d, ctx) do
          {:ok, codec}
        end
    end
  end

  # A reference cycle is fine when each step matches a host class first
  # (a map, a list, a tuple, a literal). A cycle that never does, such as
  # `repr Loop := Loop`, would decode the same term forever.
  defp consume_ok(d, ctx) do
    if consumes?(d.body, ctx, MapSet.new([d.name])) do
      :ok
    else
      {:error,
       blame(
         d,
         "decoding would not terminate; the repr must match nil, a boolean, an integer, a literal, a list, a tuple, or a map before it refers to itself"
       )}
    end
  end

  defp consumes?({:boolean}, _ctx, _seen), do: true
  defp consumes?({:integer}, _ctx, _seen), do: true
  defp consumes?({nil}, _ctx, _seen), do: true
  defp consumes?({:atom, _}, _ctx, _seen), do: true
  defp consumes?({:string, _}, _ctx, _seen), do: true
  defp consumes?({:list, _}, _ctx, _seen), do: true
  defp consumes?({:tuple, _}, _ctx, _seen), do: true
  defp consumes?({:map, _, _}, _ctx, _seen), do: true
  defp consumes?({:nullable, inner}, ctx, seen), do: consumes?(inner, ctx, seen)
  defp consumes?({:optional, inner}, ctx, seen), do: consumes?(inner, ctx, seen)

  defp consumes?({:choice, variants}, ctx, seen) do
    Enum.all?(variants, fn {_, shape} -> consumes?(shape, ctx, seen) end)
  end

  defp consumes?({:ref, "Nat"}, _ctx, _seen), do: true

  defp consumes?({:ref, name}, ctx, seen) do
    cond do
      MapSet.member?(seen, name) ->
        false

      # A missing repr is reported by the field check. Do not hide it.
      not Map.has_key?(ctx.reprs, name) ->
        true

      true ->
        consumes?(ctx.reprs[name].body, ctx, MapSet.put(seen, name))
    end
  end

  defp consumes?(_shape, _ctx, _seen), do: true

  defp compile_body({:boolean}, data, ctx) do
    if bool_data?(data, ctx) do
      {:ok, {:bool}}
    else
      {:error,
       blame(
         ctx,
         "boolean is only for a type with nullary constructors true and false; write a choice such as on => :true | off => :false"
       )}
    end
  end

  defp compile_body({:choice, variants}, data, ctx) do
    known = Map.new(data.ctors, &{&1.name, &1})
    listed = Enum.map(variants, &elem(&1, 0))

    cond do
      unknown = Enum.find(listed, &(not Map.has_key?(known, &1))) ->
        {:error, blame(ctx, "unknown constructor #{unknown}")}

      repeated = repeated_name(listed) ->
        {:error, blame(ctx, "repeated constructor #{repeated}")}

      missing = Enum.find(data.ctors, &(&1.name not in listed)) ->
        {:error, blame(ctx, "missing constructor #{missing.name}")}

      true ->
        ordered = Enum.map(data.ctors, fn c -> {c, variant_shape(variants, c.name)} end)

        with {:ok, arms} <- compile_arms(ordered, ctx),
             :ok <- disjoint_arms(ordered, ctx) do
          {:ok, {:choice, arms}}
        end
    end
  end

  defp compile_body(shape, data, ctx) do
    case data.ctors do
      [ctor] ->
        compile_single(ctor, shape, ctx)

      ctors ->
        {:error, blame(ctx, "#{data.name} has #{length(ctors)} constructors; write a choice")}
    end
  end

  defp compile_arms(ordered, ctx) do
    Enum.reduce_while(ordered, {:ok, []}, fn {ctor, shape}, {:ok, acc} ->
      case compile_ctor_shape(ctor, shape, ctx, :choice) do
        {:ok, arm} -> {:cont, {:ok, acc ++ [arm]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp variant_shape(variants, name) do
    Enum.find_value(variants, fn
      {^name, shape} -> shape
      _ -> nil
    end)
  end

  defp repeated_name(names) do
    names
    |> Enum.frequencies()
    |> Enum.find_value(fn {name, n} -> if n > 1, do: name end)
  end

  defp compile_single(ctor, shape, ctx) do
    fields = ctor_fields(ctx.data, ctor, ctx)

    cond do
      match?({:tuple, _}, shape) or match?({:map, _, _}, shape) ->
        compile_ctor_shape(ctor, shape, ctx, :single)

      fields == [] ->
        compile_const_ctor(ctor, shape, ctx)

      length(fields) == 1 and not const_shape?(shape) ->
        case compile_field(shape, hd_field(fields), 0, %{ctx | in_map: false, ctor: ctor.name}) do
          {:ok, inner} -> {:ok, {:wrap, ctor_atom(ctor.name), inner}}
          {:error, _} = err -> err
        end

      true ->
        {:error, count_msg(ctx, ctor.name, length(fields), bind_count(components_of(shape)))}
    end
  end

  defp compile_ctor_shape(ctor, shape, ctx, _where) do
    fields = ctor_fields(ctx.data, ctor, ctx)
    ctx = %{ctx | ctor: ctor.name, in_map: false}

    cond do
      fields == [] ->
        compile_const_ctor(ctor, shape, ctx)

      match?({:tuple, _}, shape) or match?({:map, _, _}, shape) ->
        compile_wrap(ctor, shape, fields, ctx)

      length(fields) == 1 and not const_shape?(shape) ->
        case compile_field(shape, hd_field(fields), 0, ctx) do
          {:ok, inner} -> {:ok, {:unwrap, ctor_atom(ctor.name), inner}}
          {:error, _} = err -> err
        end

      true ->
        {:error, count_msg(ctx, ctor.name, length(fields), bind_count(components_of(shape)))}
    end
  end

  defp compile_const_ctor(ctor, shape, ctx) do
    case shape do
      {nil} ->
        {:ok, {:const, nil, ctor_atom(ctor.name)}}

      {:atom, name} ->
        {:ok, {:const, String.to_atom(name), ctor_atom(ctor.name)}}

      {:string, text} ->
        {:ok, {:const, text, ctor_atom(ctor.name)}}

      _ ->
        {:error,
         blame(
           ctx,
           "constructor #{ctor.name} has no fields; the shape must be nil, an atom literal, or a string literal"
         )}
    end
  end

  defp compile_wrap(ctor, {:tuple, shapes}, fields, ctx) do
    case bind_components(shapes, fields, ctor.name, ctx) do
      {:ok, comps} -> {:ok, {:tuple, ctor_atom(ctor.name), comps}}
      {:error, _} = err -> err
    end
  end

  defp compile_wrap(ctor, {:map, open?, entries}, fields, ctx) do
    case bind_map(entries, fields, ctor.name, ctx) do
      {:ok, bound} -> {:ok, {:map, open?, ctor_atom(ctor.name), bound}}
      {:error, _} = err -> err
    end
  end

  defp bind_components(shapes, fields, ctor, ctx) do
    got = bind_count(shapes)

    if got != length(fields) do
      {:error, count_msg(ctx, ctor, length(fields), got)}
    else
      bind_comp(shapes, fields, 0, [], %{ctx | ctor: ctor, in_map: false})
    end
  end

  defp bind_comp([], [], _i, acc, _ctx), do: {:ok, Enum.reverse(acc)}

  defp bind_comp([shape | shapes], fields, i, acc, ctx) do
    if const_shape?(shape) do
      bind_comp(shapes, fields, i, [{:tag, const_literal(shape)} | acc], ctx)
    else
      [ty | rest] = fields

      case compile_field(shape, ty, i, ctx) do
        {:ok, codec} -> bind_comp(shapes, rest, i + 1, [{:field, codec} | acc], ctx)
        {:error, _} = err -> err
      end
    end
  end

  defp duplicate_key(entries) do
    entries
    |> Enum.map(&elem(&1, 0))
    |> Enum.frequencies()
    |> Enum.find_value(fn {key, n} -> if n > 1, do: key end)
  end

  defp bind_map(entries, fields, ctor, ctx) do
    case duplicate_key(entries) do
      nil ->
        shapes = Enum.map(entries, &elem(&1, 1))
        got = bind_count(shapes)

        if got != length(fields) do
          {:error, count_msg(ctx, ctor, length(fields), got)}
        else
          bind_map_entries(entries, fields, 0, [], %{ctx | ctor: ctor})
        end

      key ->
        {:error, blame(ctx, "duplicate map key #{inspect(key)}")}
    end
  end

  defp bind_map_entries([], [], _i, acc, _ctx), do: {:ok, Enum.reverse(acc)}

  defp bind_map_entries([{key, shape} | entries], fields, i, acc, ctx) do
    cond do
      const_shape?(shape) ->
        bind_map_entries(entries, fields, i, [{:tag, key, const_literal(shape)} | acc], ctx)

      match?({:optional, _}, shape) ->
        [ty | rest] = fields

        case compile_field(shape, ty, i, %{ctx | in_map: true}) do
          {:ok, codec} ->
            bind_map_entries(entries, rest, i + 1, [put_key(codec, key) | acc], ctx)

          {:error, _} = err ->
            err
        end

      true ->
        [ty | rest] = fields

        case compile_field(shape, ty, i, %{ctx | in_map: false}) do
          {:ok, codec} ->
            bind_map_entries(entries, rest, i + 1, [{:field, key, codec} | acc], ctx)

          {:error, _} = err ->
            err
        end
    end
  end

  # `compile_field` of an optional returns `{:opt, nothing, just, inner, mode}`
  # without the key. The map entry adds the key.
  defp put_key({:opt, nothing, just, inner, mode}, key),
    do: {:opt, key, nothing, just, inner, mode}

  defp compile_field(shape, ty, index, ctx) do
    cond do
      match?({:tuple, _}, shape) or match?({:map, _, _}, shape) or match?({:choice, _}, shape) ->
        {:error, blame(ctx, nest_msg(ctx.ctor, index, shape))}

      match?({:optional, _}, shape) and not ctx.in_map ->
        {:error, blame(ctx, "optional is only a map entry; use nullable")}

      true ->
        suit(shape, ty, index, ctx)
    end
  end

  defp suit({:integer}, :nat, _i, _ctx), do: {:ok, {:nat}}
  defp suit({:integer}, ty, i, ctx), do: outside(ctx, i, ty, "integer")

  defp suit({:boolean}, ty, i, ctx) do
    if bare_bool?(ty, ctx), do: {:ok, {:bool}}, else: outside(ctx, i, ty, "boolean")
  end

  defp suit({:ref, name}, ty, i, ctx) do
    cond do
      name in @shape_words ->
        {:error, blame(ctx, "#{name} is a shape word and cannot name a type")}

      name == "Nat" ->
        if ty == :nat, do: {:ok, {:nat}}, else: {:error, suit_msg(ctx, i, ty, "Nat")}

      not Map.has_key?(ctx.reprs, name) ->
        {:error, blame(ctx, "#{name} has no repr")}

      type_name(ty) == name and bare_type?(ty) ->
        {:ok, {:call, snake(name)}}

      true ->
        outside(ctx, i, ty, name)
    end
  end

  defp suit({:list, inner}, ty, i, ctx) do
    case list_view(ty, ctx) do
      {:ok, elem, nil_c, cons_c} ->
        case compile_field(inner, elem, i, %{ctx | in_map: false}) do
          {:ok, el} -> {:ok, {:list, nil_c, cons_c, el}}
          {:error, _} = err -> err
        end

      :no ->
        outside(ctx, i, ty, "list")
    end
  end

  defp suit({:nullable, inner}, ty, i, ctx) do
    case maybe_view(ty, ctx) do
      {:ok, elem, nothing, just} ->
        with {:ok, el} <- compile_field(inner, elem, i, %{ctx | in_map: false}),
             :ok <- nil_clash(inner, nothing_name(ty, ctx), ctx) do
          {:ok, {:nullable, nothing, just, el}}
        end

      :no ->
        outside(ctx, i, ty, "nullable")
    end
  end

  defp suit({:optional, {:nullable, inner}}, ty, i, ctx) do
    case maybe_view(ty, ctx) do
      {:ok, elem, nothing, just} ->
        with {:ok, el} <- compile_field(inner, elem, i, %{ctx | in_map: false}),
             :ok <- nil_clash(inner, nothing_name(ty, ctx), ctx) do
          {:ok, {:opt, nothing, just, el, nil}}
        end

      :no ->
        outside(ctx, i, ty, "optional")
    end
  end

  defp suit({:optional, inner}, ty, i, ctx) do
    case maybe_view(ty, ctx) do
      {:ok, elem, nothing, just} ->
        with {:ok, el} <- compile_field(inner, elem, i, %{ctx | in_map: false}),
             :ok <- nil_clash(inner, nothing_name(ty, ctx), ctx) do
          {:ok, {:opt, nothing, just, el, :drop}}
        end

      :no ->
        outside(ctx, i, ty, "optional")
    end
  end

  defp suit(shape, ty, i, ctx) do
    outside(ctx, i, ty, describe(shape, ctx, MapSet.new()))
  end

  defp outside(ctx, i, ty, what) do
    cond do
      ty == :atom ->
        {:error,
         blame(
           ctx,
           "constructor #{ctx.ctor} field #{i} has type Atom; free-form strings and interned names are not supported; model the closed set as a type and give it a repr"
         )}

      vocabulary?(ty, ctx) ->
        {:error, suit_msg(ctx, i, ty, what)}

      true ->
        {:error,
         blame(
           ctx,
           "constructor #{ctx.ctor} field #{i} has type #{show_ty(ty)}, which this version does not support"
         )}
    end
  end

  defp vocabulary?(ty, ctx) do
    ty == :nat or bare_bool?(ty, ctx) or bare_type?(ty) or list_view(ty, ctx) != :no or
      maybe_view(ty, ctx) != :no
  end

  defp suit_msg(ctx, i, ty, what) do
    blame(
      ctx,
      "constructor #{ctx.ctor} field #{i} has type #{show_ty(ty)}, which does not suit #{what}"
    )
  end

  defp nest_msg(ctor, index, {:map, _, _}),
    do: "constructor #{ctor} field #{index} nests a map; name a type with its own repr"

  defp nest_msg(ctor, index, {:tuple, _}),
    do: "constructor #{ctor} field #{index} nests a tuple; name a type with its own repr"

  defp nest_msg(ctor, index, {:choice, _}),
    do: "constructor #{ctor} field #{index} nests a choice; name a type with its own repr"

  defp count_msg(ctx, ctor, need, got) do
    blame(ctx, "constructor #{ctor} has #{need} #{fields_word(need)} but the shape binds #{got}")
  end

  defp fields_word(1), do: "field"
  defp fields_word(_), do: "fields"

  defp nothing_name(ty, ctx) do
    case maybe_view(ty, ctx) do
      {:ok, _, nothing, _} -> Atom.to_string(nothing)
      :no -> "nothing"
    end
  end

  defp nil_clash(shape, nothing, ctx) do
    if accepts_nil?(shape, ctx, MapSet.new()) do
      other = nil_witness(shape, ctx, MapSet.new())
      {:error, blame(ctx, "constructors #{nothing} and #{other} share a host shape (nil)")}
    else
      :ok
    end
  end

  defp list_view({:app, {:ty, name}, elem}, ctx) do
    case find_data(ctx.book, name) do
      nil ->
        :no

      data ->
        if list_like?(data, ctx) do
          {nil_c, cons_c} = list_ctors(data, ctx)
          {:ok, elem, nil_c, cons_c}
        else
          :no
        end
    end
  end

  defp list_view(_, _), do: :no

  defp maybe_view({:app, {:ty, name}, elem}, ctx) do
    case find_data(ctx.book, name) do
      nil ->
        :no

      data ->
        if maybe_like?(data, ctx) do
          {nothing, just} = maybe_ctors(data, ctx)
          {:ok, elem, nothing, just}
        else
          :no
        end
    end
  end

  defp maybe_view(_, _), do: :no

  defp list_like?(data, ctx) do
    case data.params do
      [{_, pname, _}] ->
        case ctor_infos(data, ctx) do
          [%{fields: []}, %{name: _, fields: [a, b]}] -> list_fields?(a, b, data.name, pname)
          [%{fields: [a, b]}, %{fields: []}] -> list_fields?(a, b, data.name, pname)
          _ -> false
        end

      _ ->
        false
    end
  end

  defp list_fields?({:param, p}, {:app, {:ty, name}, {:param, p}}, name, p), do: true
  defp list_fields?(_, _, _, _), do: false

  defp maybe_like?(data, ctx) do
    case data.params do
      [{_, pname, _}] ->
        case ctor_infos(data, ctx) do
          [%{fields: []}, %{fields: [a]}] -> a == {:param, pname}
          [%{fields: [a]}, %{fields: []}] -> a == {:param, pname}
          _ -> false
        end

      _ ->
        false
    end
  end

  defp list_ctors(data, ctx) do
    [a, b] = ctor_infos(data, ctx)

    if a.fields == [] do
      {ctor_atom(a.name), ctor_atom(b.name)}
    else
      {ctor_atom(b.name), ctor_atom(a.name)}
    end
  end

  defp maybe_ctors(data, ctx) do
    [a, b] = ctor_infos(data, ctx)

    if a.fields == [] do
      {ctor_atom(a.name), ctor_atom(b.name)}
    else
      {ctor_atom(b.name), ctor_atom(a.name)}
    end
  end

  defp ctor_infos(data, ctx) do
    Enum.map(data.ctors, fn c ->
      %{name: c.name, fields: ctor_fields(data, c, ctx)}
    end)
  end

  defp bool_data?(data, ctx) do
    names = data.ctors |> Enum.map(& &1.name) |> Enum.sort()

    data.params == [] and Map.get(data, :indices, []) == [] and names == ["false", "true"] and
      Enum.all?(data.ctors, fn c -> ctor_fields(data, c, ctx) == [] end)
  end

  defp bare_bool?(ty, ctx) do
    case ty do
      {:ty, name} ->
        case find_data(ctx.book, name) do
          nil -> false
          data -> bool_data?(data, ctx)
        end

      _ ->
        false
    end
  end

  # -- ambiguity -------------------------------------------------------------

  defp disjoint_arms(ordered, ctx) do
    case first_overlap(ordered, ctx) do
      nil ->
        :ok

      {n1, s1, n2} ->
        {:error,
         blame(
           ctx,
           "constructors #{n1} and #{n2} share a host shape (#{describe(s1, ctx, MapSet.new())})"
         )}
    end
  end

  defp first_overlap([], _ctx), do: nil
  defp first_overlap([_], _ctx), do: nil

  defp first_overlap([{c1, s1} | rest], ctx) do
    case Enum.find(rest, fn {_c2, s2} -> not disjoint?(s1, s2, ctx, MapSet.new()) end) do
      nil -> first_overlap(rest, ctx)
      {c2, _} -> {c1.name, s1, c2.name}
    end
  end

  defp disjoint?(s1, s2, ctx, seen) do
    case {alts(s1, ctx, seen), alts(s2, ctx, seen)} do
      {:unknown, _} ->
        false

      {_, :unknown} ->
        false

      {{:ok, as, seen1}, {:ok, bs, seen2}} ->
        seen = MapSet.union(seen1, seen2)
        Enum.all?(as, fn a -> Enum.all?(bs, &alt_disj?(a, &1, ctx, seen)) end)
    end
  end

  defp alt_disj?(a, b, ctx, seen) do
    case {nilish(a), nilish(b)} do
      {nil, nil} ->
        false

      {nil, _} ->
        true

      {_, nil} ->
        true

      {{:atom, x}, {:atom, y}} ->
        x != y

      {{:string, x}, {:string, y}} ->
        x != y

      {:integer, :integer} ->
        false

      {:list, :list} ->
        false

      {{:tuple, xs}, {:tuple, ys}} ->
        length(xs) != length(ys) or
          Enum.any?(Enum.zip(xs, ys), fn {x, y} -> disjoint?(x, y, ctx, seen) end)

      {{:map, true, _}, {:map, true, _}} ->
        false

      {{:map, _, r1}, {:map, _, r2}} ->
        Enum.any?(r1, fn {k, s1} ->
          case List.keyfind(r2, k, 0) do
            {_, s2} -> disjoint?(s1, s2, ctx, seen)
            nil -> false
          end
        end)

      {x, y} ->
        alt_class(x) != alt_class(y)
    end
  end

  defp nilish({:atom, "nil"}), do: nil
  defp nilish(other), do: other

  defp alt_class({:atom, _}), do: :atom
  defp alt_class({:string, _}), do: :string
  defp alt_class(:integer), do: :integer
  defp alt_class(:list), do: :list
  defp alt_class({:tuple, _}), do: :tuple
  defp alt_class({:map, _, _}), do: :map
  defp alt_class(_), do: :other

  defp alts({:boolean}, _ctx, seen), do: {:ok, [{:atom, "true"}, {:atom, "false"}], seen}
  defp alts({:integer}, _ctx, seen), do: {:ok, [:integer], seen}
  defp alts({nil}, _ctx, seen), do: {:ok, [nil], seen}
  defp alts({:atom, n}, _ctx, seen), do: {:ok, [{:atom, n}], seen}
  defp alts({:string, s}, _ctx, seen), do: {:ok, [{:string, s}], seen}
  defp alts({:list, _}, _ctx, seen), do: {:ok, [:list], seen}
  defp alts({:tuple, ss}, _ctx, seen), do: {:ok, [{:tuple, ss}], seen}

  defp alts({:map, open?, entries}, _ctx, seen) do
    reqs =
      for {key, shape} <- entries, not match?({:optional, _}, shape) do
        {key, shape}
      end

    {:ok, [{:map, open?, reqs}], seen}
  end

  defp alts({:nullable, s}, ctx, seen) do
    case alts(s, ctx, seen) do
      :unknown -> :unknown
      {:ok, as, seen1} -> {:ok, [nil | as], seen1}
    end
  end

  defp alts({:optional, s}, ctx, seen), do: alts(s, ctx, seen)

  defp alts({:choice, vs}, ctx, seen) do
    Enum.reduce_while(vs, {:ok, [], seen}, fn {_, shape}, {:ok, acc, seen1} ->
      case alts(shape, ctx, seen1) do
        :unknown -> {:halt, :unknown}
        {:ok, more, seen2} -> {:cont, {:ok, acc ++ more, seen2}}
      end
    end)
  end

  defp alts({:ref, "Nat"}, _ctx, seen), do: {:ok, [:integer], seen}

  defp alts({:ref, name}, ctx, seen) do
    cond do
      MapSet.member?(seen, name) ->
        :unknown

      not Map.has_key?(ctx.reprs, name) ->
        :unknown

      true ->
        alts(ctx.reprs[name].body, ctx, MapSet.put(seen, name))
    end
  end

  defp alts(_, _ctx, _seen), do: :unknown

  defp accepts_nil?(shape, ctx, seen) do
    case alts(shape, ctx, seen) do
      :unknown -> true
      {:ok, as, _} -> Enum.any?(as, &nil_alt?/1)
    end
  end

  defp nil_alt?(nil), do: true
  defp nil_alt?({:atom, "nil"}), do: true
  defp nil_alt?(_), do: false

  defp nil_witness({:ref, name}, ctx, seen) do
    cond do
      MapSet.member?(seen, name) or name == "Nat" or not Map.has_key?(ctx.reprs, name) ->
        "nil"

      true ->
        body = ctx.reprs[name].body
        seen = MapSet.put(seen, name)

        case body do
          {:choice, vs} ->
            Enum.find_value(vs, "nil", fn {cname, shape} ->
              if accepts_nil?(shape, ctx, seen), do: cname
            end)

          _ ->
            case find_data(ctx.book, name) do
              %{ctors: [ctor]} -> ctor.name
              _ -> nil_witness(body, ctx, seen)
            end
        end
    end
  end

  defp nil_witness({:choice, vs}, ctx, seen) do
    Enum.find_value(vs, "nil", fn {cname, shape} ->
      if accepts_nil?(shape, ctx, seen), do: cname
    end)
  end

  defp nil_witness(_, _ctx, _seen), do: "nil"

  defp describe(shape, ctx, seen) do
    case shape do
      {nil} ->
        "nil"

      {:integer} ->
        "integer"

      {:boolean} ->
        "boolean"

      {:atom, n} ->
        ":" <> n

      {:string, s} ->
        inspect(s)

      {:list, _} ->
        "list"

      {:tuple, _} ->
        "tuple"

      {:nullable, _} ->
        "nil"

      {:ref, "Nat"} ->
        "integer"

      {:ref, name} ->
        cond do
          MapSet.member?(seen, name) -> name
          not Map.has_key?(ctx.reprs, name) -> name
          true -> describe(ctx.reprs[name].body, ctx, MapSet.put(seen, name))
        end

      {:choice, [{_, shape} | _]} ->
        describe(shape, ctx, seen)

      {:map, _, entries} ->
        case Enum.find(entries, fn {_, sh} -> const_shape?(sh) end) do
          {key, sh} -> "map with #{inspect(key)} => #{describe(sh, ctx, seen)}"
          nil -> "map"
        end

      _ ->
        "shape"
    end
  end

  # -- types -----------------------------------------------------------------

  defp subject(book, "Nat") do
    case find_data(book, "Nat") do
      nil -> :nat
      data -> subject_data(data)
    end
  end

  defp subject(book, name) do
    case find_data(book, name) do
      nil -> :missing
      data -> subject_data(data)
    end
  end

  defp subject_data(data) do
    cond do
      data.params != [] -> {:params, data}
      Map.get(data, :indices, []) != [] -> {:indices, data}
      true -> {:data, data}
    end
  end

  defp find_data(book, name) do
    Enum.find(book, &(Map.get(&1, :kind) == :data and &1.name == name))
  end

  defp repr_map(book) do
    Map.new(for %{kind: :repr, name: name} = d <- book, do: {name, d})
  end

  defp book_form(book) do
    Enum.find_value(book, :named, fn
      %{kind: :data, ctors: ctors} ->
        if Enum.any?(ctors, &db_type?(&1.type)), do: :db, else: nil

      _ ->
        nil
    end)
  end

  defp db_type?(t) when is_tuple(t),
    do: db_node?(t) or t |> Tuple.to_list() |> Enum.any?(&db_type?/1)

  defp db_type?(t) when is_list(t), do: Enum.any?(t, &db_type?/1)
  defp db_type?(_), do: false

  defp db_node?({:def, name}) when is_binary(name), do: true
  defp db_node?({:var, i}) when is_integer(i), do: true
  defp db_node?(_), do: false

  defp ctor_fields(data, ctor, ctx) do
    case ctx.form do
      :db ->
        n = length(data.params)
        ty = drop_pi(ctor.type, n)
        env = data.params |> Enum.map(fn {_, x, _} -> {:param, x} end) |> Enum.reverse()
        {fields, _} = split_db(ty, env)
        fields

      :named ->
        pnames = Enum.map(data.params, fn {_, x, _} -> x end)
        {fields, _} = split_named(ctor.type, pnames)
        fields
    end
  end

  defp drop_pi(ty, 0), do: ty
  defp drop_pi({:pi, _, _, _, b}, n) when n > 0, do: drop_pi(b, n - 1)
  defp drop_pi({:ann, t, _}, n), do: drop_pi(t, n)
  defp drop_pi(ty, _), do: ty

  defp split_db({:ann, t, _}, env), do: split_db(t, env)

  defp split_db({:pi, _, a, x, b}, env) do
    a1 = norm_db(a, env)
    {fs, ret} = split_db(b, [{:binder, x} | env])
    {[a1 | fs], ret}
  end

  defp split_db(ret, env), do: {[], norm_db(ret, env)}

  defp split_named({:ann, t, _}, pnames), do: split_named(t, pnames)

  defp split_named({:pi, _, a, _, b}, pnames) do
    {fs, ret} = split_named(b, pnames)
    {[norm_named(a, pnames) | fs], ret}
  end

  defp split_named(ret, pnames), do: {[], norm_named(ret, pnames)}

  defp norm_db({:var, i}, env) when is_integer(i) do
    case Enum.at(env, i) do
      {:param, _} = p -> p
      {:binder, n} -> {:binder, n}
      nil -> {:binder, "?"}
    end
  end

  defp norm_db({:def, n}, _env), do: {:ty, n}
  defp norm_db({:app, f, a}, env), do: {:app, norm_db(f, env), norm_db(a, env)}
  defp norm_db({:prod, a, b}, env), do: {:prod, norm_db(a, env), norm_db(b, env)}
  defp norm_db({:stream, a}, env), do: {:stream, norm_db(a, env)}
  defp norm_db({:tensor, a, b}, env), do: {:tensor, norm_db(a, env), norm_db(b, env)}

  defp norm_db({:pi, q, a, x, b}, env),
    do: {:pi, q, norm_db(a, env), x, norm_db(b, [{:binder, x} | env])}

  defp norm_db({:ann, t, _}, env), do: norm_db(t, env)
  defp norm_db(other, _env), do: other

  defp norm_named({:var, n}, pnames) when is_binary(n) do
    if n in pnames, do: {:param, n}, else: {:ty, n}
  end

  defp norm_named({:app, f, a}, pnames), do: {:app, norm_named(f, pnames), norm_named(a, pnames)}

  defp norm_named({:prod, a, b}, pnames),
    do: {:prod, norm_named(a, pnames), norm_named(b, pnames)}

  defp norm_named({:stream, a}, pnames), do: {:stream, norm_named(a, pnames)}

  defp norm_named({:tensor, a, b}, pnames),
    do: {:tensor, norm_named(a, pnames), norm_named(b, pnames)}

  defp norm_named({:pi, q, a, x, b}, pnames),
    do: {:pi, q, norm_named(a, pnames), x, norm_named(b, pnames)}

  defp norm_named({:ann, t, _}, pnames), do: norm_named(t, pnames)
  defp norm_named(other, _pnames), do: other

  defp type_name({:ty, name}), do: name
  defp type_name(_), do: nil

  defp bare_type?({:ty, _}), do: true
  defp bare_type?(:nat), do: true
  defp bare_type?(_), do: false

  defp show_ty(:nat), do: "Nat"
  defp show_ty(:atom), do: "Atom"
  defp show_ty(:unit), do: "Unit"
  defp show_ty(:empty), do: "Empty"
  defp show_ty(:i64), do: "I64"
  defp show_ty(:f32ty), do: "F32"
  defp show_ty(:typ), do: "Type"
  defp show_ty({:param, n}), do: n
  defp show_ty({:ty, n}), do: n
  defp show_ty({:binder, n}), do: n
  defp show_ty({:prod, a, b}), do: "(#{show_ty(a)} × #{show_ty(b)})"
  defp show_ty({:stream, a}), do: "Stream #{show_ty(a)}"
  defp show_ty({:tensor, _, _}), do: "Tensor"
  defp show_ty({:pi, _, a, _, b}), do: "(#{show_ty(a)} → #{show_ty(b)})"

  defp show_ty({:app, f, a}) do
    arg = show_ty(a)

    arg =
      if match?({:app, _, _}, a) or match?({:prod, _, _}, a) or match?({:pi, _, _, _, _}, a),
        do: "(#{arg})",
        else: arg

    "#{show_ty(f)} #{arg}"
  end

  defp show_ty(other), do: inspect(other)

  # -- shapes ----------------------------------------------------------------

  defp const_shape?({nil}), do: true
  defp const_shape?({:atom, _}), do: true
  defp const_shape?({:string, _}), do: true
  defp const_shape?(_), do: false

  defp const_literal({nil}), do: nil
  defp const_literal({:atom, n}), do: String.to_atom(n)
  defp const_literal({:string, s}), do: s

  defp components_of(shape), do: [shape]

  defp bind_count(shapes), do: Enum.count(shapes, &(not const_shape?(&1)))

  defp hd_field([ty | _]), do: ty

  defp ctor_atom(name) do
    name
    |> String.replace("-", "_")
    |> String.replace("'", "_")
    |> String.to_atom()
  end

  defp snake(name) do
    name
    |> String.replace("-", "_")
    |> String.replace("'", "_")
    |> String.replace(~r/([a-z0-9])([A-Z])/, "\\1_\\2")
    |> String.downcase()
  end

  defp blame(%{entry: d}, msg), do: blame(d, msg)

  defp blame(d, msg) do
    "#{Print.loc_prefix(Map.get(d, :loc))}repr #{d.name}: #{msg}"
  end

  defp features(codec, acc) do
    case codec do
      {:nat} ->
        MapSet.put(acc, :nat)

      {:bool} ->
        MapSet.put(acc, :bool)

      {:const, _, _} ->
        acc

      {:call, _} ->
        acc

      {:list, _, _, el} ->
        features(el, MapSet.put(acc, :list))

      {:nullable, _, _, el} ->
        features(el, MapSet.put(acc, :nullable))

      {:wrap, _, el} ->
        features(el, acc)

      {:unwrap, _, el} ->
        features(el, acc)

      {:opt, _, _, _, el, _} ->
        features(el, MapSet.put(acc, :optional))

      {:tuple, _, comps} ->
        Enum.reduce(comps, acc, fn
          {:tag, _}, a -> MapSet.put(a, :expect)
          {:field, c}, a -> features(c, a)
        end)

      {:map, open?, _, entries} ->
        acc = if open?, do: acc, else: MapSet.put(acc, :extra)

        Enum.reduce(entries, acc, fn
          {:tag, _, _}, a -> MapSet.put(a, :tag)
          {:field, _, c}, a -> features(c, MapSet.put(a, :fetch))
          {:opt, _, _, _, c, _}, a -> features(c, MapSet.put(a, :optional))
        end)

      {:choice, arms} ->
        Enum.reduce(arms, acc, &features(&1, &2))
    end
  end

  # -- render ----------------------------------------------------------------

  defp render(plans) do
    by_fun = Map.new(plans, fn {d, codec} -> {snake(d.name), codec} end)
    funs = Enum.map_join(plans, "\n\n", fn {d, codec} -> render_pair(d, codec, by_fun) end)
    feats = Enum.reduce(plans, MapSet.new(), fn {_, codec}, acc -> features(codec, acc) end)
    helpers = render_helpers(feats)
    source = String.trim(funs <> "\n\n" <> helpers) <> "\n"
    preformat(source)
  end

  # Format the codec on its own, then drop the dummy module wrapper.
  # `emit_module/2` indents the result by two spaces. A book with no
  # repr never reaches this function, so its module text stays as it was.
  defp preformat(source) do
    wrapped = "defmodule MuroReprTmp do\n" <> indent_block(source, 2) <> "end\n"

    formatted =
      wrapped
      |> Code.format_string!()
      |> IO.iodata_to_binary()
      |> String.trim_trailing("\n")

    formatted
    |> String.split("\n")
    |> Enum.drop(1)
    |> Enum.drop(-1)
    |> Enum.map(fn
      "  " <> rest -> rest
      "" -> ""
      other -> other
    end)
    |> Enum.join("\n")
    |> Kernel.<>("\n")
  end

  defp render_pair(d, codec, plans) do
    fun = snake(d.name)
    dec = "decode_" <> fun
    enc = "encode_" <> fun

    """
    def #{dec}(value), do: #{dec}(value, [])

    #{render_decode(dec, codec, plans)}

    #{render_encode(enc, codec)}
    """
    |> String.trim()
  end

  defp render_decode(name, {:bool}, _plans) do
    "defp #{name}(value, path), do: muro_repr_decode_bool(value, path)"
  end

  defp render_decode(name, {:nat}, _plans) do
    "defp #{name}(value, path), do: muro_repr_decode_nat(value, path)"
  end

  defp render_decode(name, {:const, lit, ctor}, _plans) do
    """
    defp #{name}(#{inspect(lit)}, _path), do: {:ok, #{atom_src(ctor)}}
    defp #{name}(value, path), do: {:error, {path, {:expected, #{inspect(lit)}, value}}}
    """
    |> String.trim()
  end

  defp render_decode(name, {:wrap, ctor, inner}, plans) do
    """
    defp #{name}(value, path) do
      case #{dec_expr(inner, "value", "path", plans)} do
        {:ok, got} -> {:ok, {#{atom_src(ctor)}, got}}
        {:error, _} = err -> err
      end
    end
    """
    |> String.trim()
  end

  defp render_decode(name, {:tuple, ctor, comps}, plans) do
    n = length(comps)

    """
    defp #{name}(value, path) when is_tuple(value) and tuple_size(value) == #{n} do
      #{with_block(tuple_lines(comps, plans), ctor_term(ctor, comps))}
    end

    defp #{name}(value, path) when is_tuple(value) do
      {:error, {path, {:wrong_tuple_size, #{n}, value}}}
    end

    defp #{name}(value, path), do: {:error, {path, {:not_tuple, value}}}
    """
    |> String.trim()
  end

  defp render_decode(name, {:map, open?, ctor, entries}, plans) do
    """
    defp #{name}(value, path) when is_map(value) do
      #{with_block(map_lines(entries, open?, plans), ctor_term(ctor, entries))}
    end

    defp #{name}(value, path), do: {:error, {path, {:not_map, value}}}
    """
    |> String.trim()
  end

  defp render_decode(name, {:choice, arms}, plans) do
    clauses =
      Enum.map_join(arms, "\n\n", fn arm ->
        guard = arm_guard(arm, plans, MapSet.new())
        body = arm_body(arm, plans)
        "#{guard} ->\n#{indent_block(body, 2)}"
      end)

    names = Enum.map_join(arms, ", ", fn arm -> atom_src(arm_ctor(arm)) end)

    """
    defp #{name}(value, path) do
      cond do
        #{clauses}

        true ->
          {:error, {path, {:no_variant, [#{names}], value}}}
      end
    end
    """
    |> String.trim()
  end

  defp arm_body({:const, _lit, ctor}, _plans), do: "{:ok, #{atom_src(ctor)}}"

  defp arm_body({:unwrap, ctor, inner}, plans) do
    """
    case #{dec_expr(inner, "value", "path", plans)} do
      {:ok, got} -> {:ok, {#{atom_src(ctor)}, got}}
      {:error, _} = err -> err
    end
    """
    |> String.trim()
  end

  defp arm_body({:tuple, ctor, comps}, plans) do
    with_block(tuple_lines(comps, plans), ctor_term(ctor, comps))
  end

  defp arm_body({:map, open?, ctor, entries}, plans) do
    with_block(map_lines(entries, open?, plans), ctor_term(ctor, entries))
  end

  defp arm_guard(arm, plans, seen), do: class_guard(arm, plans, seen)

  defp class_guard(codec, plans, seen) do
    case codec do
      {:bool} ->
        "(value == true or value == false)"

      {:nat} ->
        "is_integer(value)"

      {:const, lit, _} ->
        "value == #{inspect(lit)}"

      {:call, fun} ->
        if MapSet.member?(seen, fun) do
          "true"
        else
          class_guard(Map.fetch!(plans, fun), plans, MapSet.put(seen, fun))
        end

      {:list, _, _, _} ->
        "is_list(value)"

      {:nullable, _, _, inner} ->
        # `or` is looser than `and`. Without the inner parentheses,
        # `value == nil or is_map(value) and Map.fetch(...)` fetches on nil.
        "(value == nil or (#{class_guard(inner, plans, seen)}))"

      {:wrap, _, inner} ->
        class_guard(inner, plans, seen)

      {:unwrap, _, inner} ->
        class_guard(inner, plans, seen)

      {:tuple, _, comps} ->
        tuple_guard(comps)

      {:map, _, _, entries} ->
        map_guard(entries)

      {:choice, arms} ->
        Enum.map_join(arms, " or ", fn arm -> "(" <> class_guard(arm, plans, seen) <> ")" end)
    end
  end

  defp tuple_guard(comps) do
    base = "is_tuple(value) and tuple_size(value) == #{length(comps)}"

    comps
    |> Enum.with_index()
    |> Enum.reduce(base, fn
      {{:tag, lit}, i}, acc -> acc <> " and elem(value, #{i}) == #{inspect(lit)}"
      _, acc -> acc
    end)
  end

  defp map_guard(entries) do
    Enum.reduce(entries, "is_map(value)", fn
      {:tag, key, lit}, acc ->
        acc <> " and match?({:ok, #{inspect(lit)}}, Map.fetch(value, #{inspect(key)}))"

      _, acc ->
        acc
    end)
  end

  defp tuple_lines(comps, plans) do
    {lines, _fi} =
      Enum.reduce(Enum.with_index(comps), {[], 0}, fn
        {{:tag, lit}, idx}, {lines, fi} ->
          line = ":ok <- muro_repr_expect(elem(value, #{idx}), path ++ [#{idx}], #{inspect(lit)})"
          {[line | lines], fi}

        {{:field, codec}, idx}, {lines, fi} ->
          line =
            "{:ok, f#{fi}} <- #{dec_expr(codec, "elem(value, #{idx})", "path ++ [#{idx}]", plans)}"

          {[line | lines], fi + 1}
      end)

    Enum.reverse(lines)
  end

  defp map_lines(entries, open?, plans) do
    {lines, keys, _fi} =
      Enum.reduce(entries, {[], [], 0}, fn
        {:tag, key, lit}, {lines, keys, fi} ->
          line = ":ok <- muro_repr_tag(value, path, #{inspect(key)}, #{inspect(lit)})"
          {[line | lines], [key | keys], fi}

        {:field, key, codec}, {lines, keys, fi} ->
          fetch = "{:ok, g#{fi}} <- muro_repr_fetch(value, path, #{inspect(key)})"

          dec =
            "{:ok, f#{fi}} <- #{dec_expr(codec, "g#{fi}", "path ++ [#{inspect(key)}]", plans)}"

          {[dec, fetch | lines], [key | keys], fi + 1}

        {:opt, key, nothing, just, codec, mode}, {lines, keys, fi} ->
          nil_ok = mode == nil

          line =
            "{:ok, f#{fi}} <- muro_repr_decode_optional(value, path, #{inspect(key)}, #{fun2(codec, plans)}, #{atom_src(nothing)}, #{atom_src(just)}, #{nil_ok})"

          {[line | lines], [key | keys], fi + 1}
      end)

    lines = Enum.reverse(lines)

    lines =
      if open? do
        lines
      else
        key_list = keys |> Enum.reverse() |> Enum.map_join(", ", &inspect/1)
        lines ++ [":ok <- muro_repr_no_extra(value, path, [#{key_list}])"]
      end

    lines
  end

  defp ctor_term(ctor, parts) do
    n = field_slots(parts)

    if n == 0 do
      atom_src(ctor)
    else
      vars = Enum.map_join(0..(n - 1), ", ", &"f#{&1}")
      "{#{atom_src(ctor)}, #{vars}}"
    end
  end

  defp field_slots(parts) do
    Enum.count(parts, fn
      {:field, _} -> true
      {:field, _, _} -> true
      {:opt, _, _, _, _, _} -> true
      _ -> false
    end)
  end

  defp with_block([], term), do: "{:ok, #{term}}"

  defp with_block(lines, term) do
    body = Enum.map_join(lines, ",\n", & &1)

    """
    with #{indent_rest(body)} do
      {:ok, #{term}}
    end
    """
    |> String.trim()
  end

  defp indent_rest(body) do
    lines = String.split(body, "\n")
    [h | t] = lines
    Enum.join([h | Enum.map(t, &("  " <> &1))], "\n")
  end

  defp dec_expr({:nat}, src, path, _plans), do: "muro_repr_decode_nat(#{src}, #{path})"
  defp dec_expr({:bool}, src, path, _plans), do: "muro_repr_decode_bool(#{src}, #{path})"
  defp dec_expr({:call, fun}, src, path, _plans), do: "decode_#{fun}(#{src}, #{path})"

  defp dec_expr({:list, nil_c, cons, el}, src, path, plans) do
    "muro_repr_list_decode(#{src}, #{path}, #{fun2(el, plans)}, #{atom_src(nil_c)}, #{atom_src(cons)})"
  end

  defp dec_expr({:nullable, nothing, just, inner}, src, path, plans) do
    "muro_repr_decode_nullable(#{src}, #{path}, #{atom_src(nothing)}, #{atom_src(just)}, #{fun2(inner, plans)})"
  end

  defp dec_expr({:wrap, ctor, inner}, src, path, plans) do
    "case #{dec_expr(inner, src, path, plans)} do {:ok, got} -> {:ok, {#{atom_src(ctor)}, got}}; {:error, _} = err -> err end"
  end

  defp fun2(codec, plans) do
    case codec do
      {:nat} -> "&muro_repr_decode_nat/2"
      {:bool} -> "&muro_repr_decode_bool/2"
      {:call, fun} -> "&decode_#{fun}/2"
      _ -> "fn el, p -> #{dec_expr(codec, "el", "p", plans)} end"
    end
  end

  defp render_encode(name, {:bool}), do: "def #{name}(value), do: muro_repr_encode_bool(value)"
  defp render_encode(name, {:nat}), do: "def #{name}(value), do: muro_repr_encode_nat(value)"

  defp render_encode(name, {:const, lit, ctor}) do
    "def #{name}(#{atom_src(ctor)}), do: #{inspect(lit)}"
  end

  defp render_encode(name, {:wrap, ctor, inner}) do
    "def #{name}({#{atom_src(ctor)}, f0}), do: #{enc_expr(inner, "f0")}"
  end

  defp render_encode(name, {:unwrap, ctor, inner}) do
    "def #{name}({#{atom_src(ctor)}, f0}), do: #{enc_expr(inner, "f0")}"
  end

  defp render_encode(name, {:tuple, ctor, comps}) do
    n = field_slots(comps)
    head = encode_head(ctor, n)
    body = "{" <> Enum.map_join(tuple_enc(comps), ", ", & &1) <> "}"
    "def #{name}(#{head}), do: #{body}"
  end

  defp render_encode(name, {:map, _open, ctor, entries}) do
    n = field_slots(entries)
    head = encode_head(ctor, n)
    "def #{name}(#{head}) do\n#{indent_block(map_enc(entries), 2)}\nend"
  end

  defp render_encode(name, {:choice, arms}) do
    Enum.map_join(arms, "\n\n", fn arm ->
      render_encode_arm(name, arm)
    end)
  end

  defp render_encode_arm(name, {:const, lit, ctor}) do
    "def #{name}(#{atom_src(ctor)}), do: #{inspect(lit)}"
  end

  defp render_encode_arm(name, {:unwrap, ctor, inner}) do
    "def #{name}({#{atom_src(ctor)}, f0}), do: #{enc_expr(inner, "f0")}"
  end

  defp render_encode_arm(name, {:tuple, ctor, comps}) do
    render_encode(name, {:tuple, ctor, comps})
  end

  defp render_encode_arm(name, {:map, open?, ctor, entries}) do
    render_encode(name, {:map, open?, ctor, entries})
  end

  defp encode_head(ctor, 0), do: atom_src(ctor)

  defp encode_head(ctor, n) do
    vars = Enum.map_join(0..(n - 1), ", ", &"f#{&1}")
    "{#{atom_src(ctor)}, #{vars}}"
  end

  defp tuple_enc(comps) do
    {exprs, _fi} =
      Enum.map_reduce(comps, 0, fn
        {:tag, lit}, fi -> {inspect(lit), fi}
        {:field, codec}, fi -> {enc_expr(codec, "f#{fi}"), fi + 1}
      end)

    exprs
  end

  defp map_enc(entries) do
    {base, opts, _fi} =
      Enum.reduce(entries, {[], [], 0}, fn
        {:tag, key, lit}, {base, opts, fi} ->
          {[{key, inspect(lit)} | base], opts, fi}

        {:field, key, codec}, {base, opts, fi} ->
          {[{key, enc_expr(codec, "f#{fi}")} | base], opts, fi + 1}

        {:opt, key, nothing, just, codec, _mode}, {base, opts, fi} ->
          opt = {key, nothing, just, "f#{fi}", enc_fun1(codec)}
          {base, [opt | opts], fi + 1}
      end)

    map =
      base
      |> Enum.reverse()
      |> Enum.map_join(", ", fn {k, v} -> "#{inspect(k)} => #{v}" end)

    acc = "%{#{map}}"

    case Enum.reverse(opts) do
      [] ->
        acc

      opts ->
        Enum.reduce(opts, acc, fn {key, nothing, just, var, fun}, acc ->
          "#{acc}\n|> muro_repr_put_optional(#{inspect(key)}, #{atom_src(nothing)}, #{atom_src(just)}, #{var}, #{fun})"
        end)
    end
  end

  defp enc_expr({:nat}, src), do: "muro_repr_encode_nat(#{src})"
  defp enc_expr({:bool}, src), do: "muro_repr_encode_bool(#{src})"
  defp enc_expr({:call, fun}, src), do: "encode_#{fun}(#{src})"

  defp enc_expr({:list, nil_c, cons, el}, src) do
    "muro_repr_list_encode(#{src}, #{atom_src(nil_c)}, #{atom_src(cons)}, #{enc_fun1(el)})"
  end

  defp enc_expr({:nullable, nothing, just, inner}, src) do
    "muro_repr_encode_nullable(#{atom_src(nothing)}, #{atom_src(just)}, #{src}, #{enc_fun1(inner)})"
  end

  # A field codec is a call, a nat, a bool, a list, or a nullable.
  # A nested newtype is refused before render.
  defp enc_expr({:wrap, _ctor, _inner}, _src) do
    raise "repr emit: nested newtype"
  end

  defp enc_fun1({:nat}), do: "&muro_repr_encode_nat/1"
  defp enc_fun1({:bool}), do: "&muro_repr_encode_bool/1"
  defp enc_fun1({:call, fun}), do: "&encode_#{fun}/1"
  defp enc_fun1(codec), do: "fn el -> #{enc_expr(codec, "el")} end"

  defp arm_ctor({:const, _, ctor}), do: ctor
  defp arm_ctor({:unwrap, ctor, _}), do: ctor
  defp arm_ctor({:tuple, ctor, _}), do: ctor
  defp arm_ctor({:map, _, ctor, _}), do: ctor

  defp atom_src(true), do: "true"
  defp atom_src(false), do: "false"
  defp atom_src(nil), do: "nil"

  defp atom_src(atom) when is_atom(atom) do
    name = Atom.to_string(atom)

    if name in ~w(do end catch rescue after else when and or not in fn) do
      ~s(:"#{name}")
    else
      ":" <> name
    end
  end

  defp indent_block(text, n) do
    pad = String.duplicate(" ", n)
    text |> String.split("\n") |> Enum.map_join("\n", &(pad <> &1))
  end

  defp render_helpers(feats) do
    parts =
      []
      |> maybe(:nat, feats, nat_helpers())
      |> maybe(:bool, feats, bool_helpers())
      |> maybe(:fetch, feats, fetch_helper())
      |> maybe(:tag, feats, tag_helper())
      |> maybe(:expect, feats, expect_helper())
      |> maybe(:extra, feats, extra_helper())
      |> maybe(:optional, feats, optional_helpers())
      |> maybe(:nullable, feats, nullable_helpers())
      |> maybe(:list, feats, list_helpers())

    Enum.join(parts, "\n\n")
  end

  defp maybe(acc, feat, feats, src) do
    if MapSet.member?(feats, feat), do: acc ++ [String.trim(src)], else: acc
  end

  defp nat_helpers do
    """
    @muro_repr_nat_max #{inspect(@nat_max)}

    defp muro_repr_decode_nat(value, _path)
         when is_integer(value) and value >= 0 and value <= @muro_repr_nat_max do
      {:ok, muro_repr_nat_from(value)}
    end

    defp muro_repr_decode_nat(value, path) when is_integer(value) and value < 0 do
      {:error, {path, {:negative_integer, value}}}
    end

    defp muro_repr_decode_nat(value, path) when is_integer(value) do
      {:error, {path, {:nat_too_large, value}}}
    end

    defp muro_repr_decode_nat(value, path), do: {:error, {path, {:not_integer, value}}}

    defp muro_repr_nat_from(0), do: 0

    defp muro_repr_nat_from(n) when is_integer(n) and n > 0 do
      muro_repr_nat_from(n, 0)
    end

    defp muro_repr_nat_from(0, acc), do: acc

    defp muro_repr_nat_from(n, acc) when is_integer(n) and n > 0 do
      muro_repr_nat_from(n - 1, {:suc, acc})
    end

    defp muro_repr_encode_nat(value), do: muro_repr_encode_nat(value, 0)
    defp muro_repr_encode_nat(0, acc), do: acc
    defp muro_repr_encode_nat({:suc, value}, acc), do: muro_repr_encode_nat(value, acc + 1)
    """
  end

  defp bool_helpers do
    """
    defp muro_repr_decode_bool(true, _path), do: {:ok, true}
    defp muro_repr_decode_bool(false, _path), do: {:ok, false}
    defp muro_repr_decode_bool(value, path), do: {:error, {path, {:not_boolean, value}}}

    defp muro_repr_encode_bool(true), do: true
    defp muro_repr_encode_bool(false), do: false
    """
  end

  defp fetch_helper do
    """
    defp muro_repr_fetch(value, path, key) do
      case Map.fetch(value, key) do
        {:ok, got} -> {:ok, got}
        :error -> {:error, {path, {:missing_key, key}}}
      end
    end
    """
  end

  defp tag_helper do
    """
    defp muro_repr_tag(value, path, key, literal) do
      case Map.fetch(value, key) do
        :error -> {:error, {path, {:missing_key, key}}}
        {:ok, got} when got == literal -> :ok
        {:ok, got} -> {:error, {path ++ [key], {:expected, literal, got}}}
      end
    end
    """
  end

  defp expect_helper do
    """
    defp muro_repr_expect(literal, _path, literal), do: :ok
    defp muro_repr_expect(value, path, literal), do: {:error, {path, {:expected, literal, value}}}
    """
  end

  defp extra_helper do
    """
    defp muro_repr_no_extra(value, path, keys) do
      extra = value |> Map.keys() |> Enum.reject(&(&1 in keys)) |> Enum.sort()

      case extra do
        [] -> :ok
        [key | _] -> {:error, {path, {:unexpected_key, key}}}
      end
    end
    """
  end

  defp optional_helpers do
    """
    defp muro_repr_decode_optional(value, path, key, fun, nothing, just, nil_ok) do
      case Map.fetch(value, key) do
        :error ->
          {:ok, nothing}

        {:ok, nil} ->
          if nil_ok do
            {:ok, nothing}
          else
            {:error, {path ++ [key], {:nil_not_allowed, nil}}}
          end

        {:ok, got} ->
          case fun.(got, path ++ [key]) do
            {:ok, inner} -> {:ok, {just, inner}}
            {:error, _} = err -> err
          end
      end
    end

    defp muro_repr_put_optional(map, _key, nothing, _just, nothing, _fun), do: map

    defp muro_repr_put_optional(map, key, _nothing, just, {just, inner}, fun) do
      Map.put(map, key, fun.(inner))
    end
    """
  end

  defp nullable_helpers do
    """
    defp muro_repr_decode_nullable(nil, _path, nothing, _just, _fun), do: {:ok, nothing}

    defp muro_repr_decode_nullable(value, path, _nothing, just, fun) do
      case fun.(value, path) do
        {:ok, inner} -> {:ok, {just, inner}}
        {:error, _} = err -> err
      end
    end

    defp muro_repr_encode_nullable(nothing, _just, nothing, _fun), do: nil
    defp muro_repr_encode_nullable(_nothing, just, {just, inner}, fun), do: fun.(inner)
    """
  end

  defp list_helpers do
    """
    defp muro_repr_list_decode(value, path, fun, nil_ctor, cons) do
      case muro_repr_list_walk(value, path, 0, fun, []) do
        {:ok, acc} -> {:ok, muro_repr_list_pack(acc, nil_ctor, cons)}
        :improper -> {:error, {path, {:not_list, value}}}
        {:error, _} = err -> err
      end
    end

    defp muro_repr_list_walk([], _path, _i, _fun, acc), do: {:ok, acc}

    defp muro_repr_list_walk([el | rest], path, i, fun, acc) do
      case fun.(el, path ++ [i]) do
        {:ok, got} -> muro_repr_list_walk(rest, path, i + 1, fun, [got | acc])
        {:error, _} = err -> err
      end
    end

    defp muro_repr_list_walk(_value, _path, _i, _fun, _acc), do: :improper

    defp muro_repr_list_pack(reversed, nil_ctor, cons) do
      Enum.reduce(reversed, nil_ctor, fn el, acc -> {cons, el, acc} end)
    end

    defp muro_repr_list_encode(value, nil_ctor, cons, fun) do
      muro_repr_list_encode(value, nil_ctor, cons, fun, [])
    end

    defp muro_repr_list_encode(nil_ctor, nil_ctor, _cons, _fun, acc), do: Enum.reverse(acc)

    defp muro_repr_list_encode({cons, el, rest}, nil_ctor, cons, fun, acc) do
      muro_repr_list_encode(rest, nil_ctor, cons, fun, [fun.(el) | acc])
    end
    """
  end
end

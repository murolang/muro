defmodule Muro.Synth.Term do
  @moduledoc false

  # A structured state is a term. Nullary states stay binaries, and
  # `spell/1` and `label/1` are the identity on those, so a book that
  # never leaves the nullary path is unchanged.
  #
  # `spell` is the source term. `label` is the fragment a definition
  # name may contain. The two differ when the term has fields.

  defstruct [:value, :spell, :label]

  @cap 32

  def cap, do: @cap

  def spell(%__MODULE__{spell: spell}), do: spell
  def spell(name) when is_binary(name), do: name
  def spell(nil), do: nil

  def label(%__MODULE__{label: label}), do: label
  def label(name) when is_binary(name), do: name
  def label(nil), do: nil

  def value_of(%__MODULE__{value: value}), do: value
  def value_of(value), do: value

  @doc """
  The shape of `name` after aliases.

  `{:enum, name, ctors}` is a data type whose constructors take nothing.
  `{:data, name, rows}` is a datatype with fields. A field is that
  field's schema, or `%{schema, qty, name}` when the telescope named
  a quantity. `{:rec, name}` is a back-edge to the datatype `name`
  already being read, so the Elixir term stays finite.
  `{:open, reason}` is not a finite term walk. `"mutual"` is a
  back-edge to a different datatype.
  """
  def schema(book, name) when is_list(book) and is_binary(name) do
    of_type(book, {:var, name}, MapSet.new())
  end

  def schema(_book, _name), do: {:open, "missing"}

  def finite?(schema) do
    match?({:ok, _}, inhabitants(schema))
  end

  def inhabitants(schema), do: enum_inhabitants(schema, @cap)

  def decode(raw, schema) do
    case pack(schema, raw) do
      {:ok, value, spell, label} ->
        {:ok, %__MODULE__{value: value, spell: spell, label: label}}

      :error ->
        :error
    end
  end

  def decode!(raw, schema) do
    case decode(raw, schema) do
      {:ok, term} -> term
      :error -> raise ArgumentError, "not a value of this state: #{inspect(raw)}"
    end
  end

  # Fields opened along a path. The first pass opens one. A later
  # pass opens one more, and stops at this bound. The number is not
  # a fixture's depth.
  @path_bound 3
  @first_path_depth 1

  def path_bound, do: @path_bound
  def first_path_depth, do: @first_path_depth

  @doc """
  Structural templates at paths of length at most `max_depth`.

  Depth 0 is the value itself. Each greater depth opens one field.
  Resolving a back-edge does not spend a step: the field that
  carried the name already did, and a name already opened is not
  walked past `max_depth`. A list element is not a field step.
  Invention reads that difference. A bare `Nat` at the root is not
  a template: that would be a threshold on a state index.
  """
  def templates(schema, states, taken, max_depth) do
    values = Enum.map(states, &value_of/1)
    specs = collect(schema, values, [], 0, max_depth, %{})
    name_specs(specs, taken)
  end

  @doc """
  Templates at the nodes where `earlier` and `later` differ.

  Specs already present are not returned. The caller filters the union.
  """
  def invent(schema, earlier, later, existing, taken) do
    left = value_of(earlier)
    right = value_of(later)

    specs =
      schema
      |> diffs(left, right, [], %{})
      |> Enum.flat_map(fn {path, sub, a, b} -> local(sub, [a, b], path) end)
      |> Enum.reject(fn spec -> Enum.any?(existing, &(spec_key(&1) == spec_key(spec))) end)

    name_specs(specs, taken)
  end

  def eval_spec(schema, spec, state) do
    case dig(schema, Map.get(spec, :path, []), value_of(state), Map.get(spec, :guards, [])) do
      :miss -> false
      {:ok, sub, value} -> bit(spec, sub, value)
    end
  end

  def structural?(%{kind: kind}) do
    kind in [:ctor_is, :vals_eq, :spread_eq, :pair_any, :len_is, :nat_is]
  end

  def render_helpers(specs, taken) do
    struct_specs = Enum.filter(specs, &structural?/1)

    if struct_specs == [] do
      {%{text: "", funs: %{}}, taken}
    else
      build_helpers(struct_specs, taken)
    end
  end

  def render_clause(schema, spec, ctor, helpers) do
    body = test_at(schema, "c", Map.get(spec, :path, []), spec, helpers, [])
    "      | #{ctor} => #{body}"
  end

  @doc """
  Nested match from `scrutinee` down to each inhabitant.

  `type_of.(src)` is the type of a branch at that source term.
  `body_of.(src)` is the branch once the term is concrete.
  """
  def exhaust(schema, scrutinee, type_of, body_of) when is_function(type_of, 1) do
    open(schema, scrutinee, & &1, type_of, body_of, 0)
  end

  @doc """
  Whether two values of `schema` can be compared by a run.

  A finite inhabitant list is not required. A direct back-edge to the
  datatype being compared can: the run recurses on that field. A
  function, a mutual family, a linear field, an erased constructor
  argument, or a back-edge under a list or a product cannot.
  """
  def equatable?(schema) do
    match?({:ok, _}, eq_nodes(schema, []))
  end

  @doc """
  A reason this schema cannot be ranked, or `nil`.

  The certificate peels a finite cover. A function field, a linear
  field, and an erased constructor argument are not that peeling:
  a function is not a value, a linear binder would be dropped in
  an unused arm, and an erased argument is absent from the value
  but required in the constructor's telescope. A back-edge under
  a list or a product is not this peeling either: a `let` parses,
  and `rank` of the bound pair does not convert in the evidence.
  """
  def cert_refusal(schema) do
    refusal_in(schema)
  end

  @doc """
  `name` decides whether two states are the same value.

  The comparison matches constructors and walks fields, lists, and
  Nats. It does not enumerate inhabitants. `:open` means no such run
  exists. The caller must not emit an empty match in its place.
  """
  def eq_source(name, schema, taken) when is_binary(name) do
    case eq_nodes(schema, []) do
      :open ->
        :open

      {:ok, nodes} ->
        {names, taken} =
          Enum.reduce(nodes, {%{}, taken}, fn node, {map, taken} ->
            {fun, taken} = Muro.Synth.Book.reserve(eq_base(node), taken)
            {Map.put(map, node, fun), taken}
          end)

        aux = Enum.map_join(nodes, "\n", &eq_def(&1, Map.fetch!(names, &1), names))
        {:ok, aux <> "\n" <> eq_root(name, Map.fetch!(names, schema)), taken}
    end
  end

  def same_source(name, schema, inhabitants) when is_list(inhabitants) do
    body =
      exhaust(schema, "s", fn _ -> "Bool" end, fn spell ->
        exhaust(schema, "t", fn _ -> "Bool" end, fn other ->
          if other == spell, do: "true", else: "false"
        end)
      end)

    """
    def #{name} : run Π (+ s : State) → Π (+ t : State) → Bool :=
      λ (+ s : State) → λ (+ t : State) →
        #{body}
    """
  end

  defp of_type(book, ty, seen) do
    case unfold(book, ty, MapSet.new()) do
      :nat ->
        :nat

      {:var, "Nat"} ->
        :nat

      {:var, name} ->
        of_declared(book, name, seen)

      {:app, {:var, "List"}, elem} ->
        {:list, of_type(book, elem, seen)}

      {:prod, left, right} ->
        {:prod, of_type(book, left, seen), of_type(book, right, seen)}

      {:pi, _, _, _, _} ->
        {:open, "function"}

      _ ->
        {:open, "type"}
    end
  end

  defp of_declared(book, name, seen) do
    if MapSet.member?(seen, name) do
      {:rec, name}
    else
      case Enum.find(book, &(Map.get(&1, :kind) == :data and &1.name == name)) do
        nil ->
          {:open, "missing"}

        %{params: params} when is_list(params) and params != [] ->
          {:open, "params"}

        %{indices: indices} when is_list(indices) and indices != [] ->
          {:open, "indices"}

        %{ctors: ctors} ->
          seen = MapSet.put(seen, name)
          fields = Enum.map(ctors, &ctor_fields(book, &1, seen))

          rows =
            Enum.zip(ctors, fields)
            |> Enum.map(fn {ctor, fs} ->
              %{name: ctor.name, fields: fs, erased: erased_arg?(Map.get(ctor, :type))}
            end)

          cond do
            Enum.all?(fields, &(&1 == [])) ->
              {:enum, name, Enum.map(ctors, & &1.name)}

            mutual_rows?(rows, name) ->
              {:open, "mutual"}

            true ->
              {:data, name, rows}
          end
      end
    end
  end

  defp ctor_fields(book, ctor, seen) do
    read_fields(book, Map.get(ctor, :type), seen)
  end

  # An erased argument is not in the emitted value, so it is not a field.
  # A relevant field keeps the telescope's quantity and binder. A bare
  # arrow's binder is "_", and that is not a name.
  defp read_fields(book, {:pi, :erased, _, _, cod}, seen), do: read_fields(book, cod, seen)

  defp read_fields(book, {:pi, qty, dom, name, cod}, seen) do
    field = %{schema: of_type(book, dom, seen), qty: qty, name: field_binder(name)}
    [field | read_fields(book, cod, seen)]
  end

  defp read_fields(_book, _ty, _seen), do: []

  # An erased argument is dropped from the value. A pattern that omitted
  # it would not match the constructor's telescope, so that datatype is
  # not given an equality run.
  defp erased_arg?({:pi, :erased, _, _, _}), do: true
  defp erased_arg?({:pi, _, _, _, cod}), do: erased_arg?(cod)
  defp erased_arg?(_ty), do: false

  defp field_binder(name) when is_binary(name) and name != "_", do: name
  defp field_binder(_name), do: nil

  # Older schemas, and tests, store a bare schema in `fields`.
  defp field_schema(%{schema: schema}), do: schema
  defp field_schema(schema), do: schema

  # A linear binder cannot be dropped in the unequal arm.
  defp linear_field?(%{qty: qty}), do: Muro.Grade.kernel_qty(qty) == :linear
  defp linear_field?(_field), do: false

  # A back-edge is mutual when it does not name the nearest datatype.
  # A nested datatype may refer to itself. A back-edge to an ancestor
  # is the mutual family.
  defp mutual_rows?(rows, name) do
    Enum.any?(rows, fn row ->
      Enum.any?(row.fields, &foreign_rec?(field_schema(&1), name))
    end)
  end

  defp foreign_rec?({:open, "mutual"}, _enclosing), do: true
  defp foreign_rec?({:rec, name}, name), do: false
  defp foreign_rec?({:rec, _other}, _enclosing), do: true

  defp foreign_rec?({:data, name, rows}, _enclosing) do
    Enum.any?(rows, fn row ->
      Enum.any?(row.fields, &foreign_rec?(field_schema(&1), name))
    end)
  end

  defp foreign_rec?({:list, elem}, enclosing), do: foreign_rec?(elem, enclosing)

  defp foreign_rec?({:prod, left, right}, enclosing) do
    foreign_rec?(left, enclosing) or foreign_rec?(right, enclosing)
  end

  defp foreign_rec?(_, _enclosing), do: false

  defp resolve({:rec, name}, bound) do
    case Map.fetch(bound, name) do
      {:ok, schema} -> schema
      :error -> {:rec, name}
    end
  end

  defp resolve(schema, _bound), do: schema

  defp bind_data({:data, name, _} = schema, bound), do: Map.put(bound, name, schema)
  defp bind_data(_schema, bound), do: bound

  defp enter(schema, bound) do
    schema = resolve(schema, bound)
    {schema, bind_data(schema, bound)}
  end

  defp unfold(book, {:var, name}, seen) do
    if MapSet.member?(seen, name) do
      {:var, name}
    else
      case alias_of(book, name) do
        nil -> {:var, name}
        body -> unfold(book, body, MapSet.put(seen, name))
      end
    end
  end

  defp unfold(book, {:prod, left, right}, seen) do
    {:prod, unfold(book, left, seen), unfold(book, right, seen)}
  end

  defp unfold(book, {:app, fun, arg}, seen) do
    {:app, unfold(book, fun, seen), unfold(book, arg, seen)}
  end

  defp unfold(book, {:pi, qty, dom, name, cod}, seen) do
    {:pi, qty, unfold(book, dom, seen), name, unfold(book, cod, seen)}
  end

  defp unfold(_book, ty, _seen), do: ty

  defp alias_of(book, name) do
    Enum.find_value(book, fn
      %{name: ^name, mode: :spec, type: :typ, body: body} = d ->
        if Map.get(d, :kind) == :data, do: nil, else: body

      _ ->
        nil
    end)
  end

  defp enum_inhabitants(schema, cap) do
    case grow(schema, cap) do
      :open -> :open
      :cap -> :cap
      {:ok, rows} when length(rows) <= cap -> {:ok, Enum.map(rows, &pack_row/1)}
      _ -> :cap
    end
  end

  defp grow(:nat, _cap), do: :open
  defp grow({:list, _}, _cap), do: :open
  defp grow({:open, _}, _cap), do: :open
  defp grow({:rec, _}, _cap), do: :open

  defp grow({:enum, _name, ctors}, _cap) do
    {:ok, Enum.map(ctors, &{:atom, &1})}
  end

  defp grow({:data, _name, ctors}, cap) do
    Enum.reduce_while(ctors, {:ok, []}, fn ctor, {:ok, acc} ->
      case grow_fields(ctor.fields, cap) do
        :open ->
          {:halt, :open}

        :cap ->
          {:halt, :cap}

        {:ok, rows} ->
          built = Enum.map(rows, &{:ctor, ctor.name, &1})
          joined = acc ++ built
          if length(joined) > cap, do: {:halt, :cap}, else: {:cont, {:ok, joined}}
      end
    end)
  end

  defp grow({:prod, left, right}, cap) do
    with {:ok, ls} <- grow(left, cap),
         {:ok, rs} <- grow(right, cap) do
      rows = for l <- ls, r <- rs, do: {:pair, l, r}
      if length(rows) > cap, do: :cap, else: {:ok, rows}
    end
  end

  defp grow_fields(fields, cap) do
    Enum.reduce_while(fields, {:ok, [[]]}, fn field, {:ok, acc} ->
      case grow(field_schema(field), cap) do
        :open ->
          {:halt, :open}

        :cap ->
          {:halt, :cap}

        {:ok, items} ->
          rows = for row <- acc, item <- items, do: row ++ [item]
          if length(rows) > cap, do: {:halt, :cap}, else: {:cont, {:ok, rows}}
      end
    end)
  end

  defp pack_row(row) do
    {value, spell, label} = realize(row)
    %__MODULE__{value: value, spell: spell, label: label}
  end

  defp realize({:atom, name}) do
    {atom_of(name), name, name}
  end

  defp realize({:ctor, name, field_rows}) do
    realized = Enum.map(field_rows, &realize/1)

    value =
      case realized do
        [] -> atom_of(name)
        rows -> List.to_tuple([atom_of(name) | Enum.map(rows, &elem(&1, 0))])
      end

    spell =
      case realized do
        [] -> name
        rows -> "(" <> Enum.join([name | Enum.map(rows, &arg(elem(&1, 1)))], " ") <> ")"
      end

    label =
      case realized do
        [] -> name
        rows -> Enum.join([name | Enum.map(rows, &elem(&1, 2))], "-")
      end

    {value, spell, label}
  end

  defp realize({:pair, left, right}) do
    {lv, ls, ll} = realize(left)
    {rv, rs, rl} = realize(right)
    {{lv, rv}, "(#{ls}, #{rs})", "#{ll}-#{rl}"}
  end

  defp realize({:packed, value, spell, label}), do: {value, spell, label}

  defp pack(schema, raw), do: pack(schema, raw, %{})

  defp pack(schema, raw, bound) do
    {schema, bound} = enter(schema, bound)
    pack_schema(schema, raw, bound)
  end

  defp pack_schema(:nat, raw, _bound) do
    case canon_nat(raw) do
      {:ok, n} -> {:ok, n, spell_nat(n), "n#{n}"}
      :error -> :error
    end
  end

  defp pack_schema({:enum, _name, ctors}, raw, _bound) when is_atom(raw) do
    case Enum.find(ctors, &(atom_of(&1) == raw)) do
      nil -> :error
      name -> {:ok, raw, name, name}
    end
  end

  defp pack_schema({:enum, _, _}, _, _), do: :error

  defp pack_schema({:data, _name, ctors}, raw, bound) do
    tag = tag_atom(raw)

    case Enum.find(ctors, &(atom_of(&1.name) == tag)) do
      nil ->
        :error

      ctor ->
        fields = raw_fields(raw)

        if length(fields) != length(ctor.fields) do
          :error
        else
          decoded = Enum.zip(Enum.map(ctor.fields, &field_schema/1), fields)

          case decode_fields(decoded, bound) do
            :error ->
              :error

            {:ok, rows} ->
              {value, spell, label} = realize({:ctor, ctor.name, rows_to_ast(rows)})
              {:ok, value, spell, label}
          end
        end
    end
  end

  defp pack_schema({:list, elem}, raw, bound) do
    case canon_list(raw) do
      :error ->
        :error

      {:ok, items} ->
        case decode_list_items(elem, items, bound) do
          :error ->
            :error

          {:ok, rows} ->
            value = encode_list(Enum.map(rows, &elem(&1, 0)))
            spells = Enum.map(rows, &elem(&1, 1))
            labels = Enum.map(rows, &elem(&1, 2))
            {:ok, value, list_spell(spells), list_label(labels)}
        end
    end
  end

  defp pack_schema({:prod, left, right}, {a, b}, bound) do
    with {:ok, lv, ls, ll} <- pack(left, a, bound),
         {:ok, rv, rs, rl} <- pack(right, b, bound) do
      {:ok, {lv, rv}, "(#{ls}, #{rs})", "#{ll}-#{rl}"}
    else
      _ -> :error
    end
  end

  defp pack_schema({:open, _}, _, _), do: :error
  defp pack_schema(_schema, _raw, _bound), do: :error

  defp rows_to_ast(rows) do
    Enum.map(rows, fn {value, spell, label} -> {:packed, value, spell, label} end)
  end

  defp decode_fields(pairs, bound) do
    Enum.reduce_while(pairs, {:ok, []}, fn {schema, raw}, {:ok, acc} ->
      case pack(schema, raw, bound) do
        {:ok, value, spell, label} -> {:cont, {:ok, acc ++ [{value, spell, label}]}}
        :error -> {:halt, :error}
      end
    end)
  end

  defp decode_list_items(elem, items, bound) do
    Enum.reduce_while(items, {:ok, []}, fn raw, {:ok, acc} ->
      case pack(elem, raw, bound) do
        {:ok, value, spell, label} -> {:cont, {:ok, acc ++ [{value, spell, label}]}}
        :error -> {:halt, :error}
      end
    end)
  end

  defp collect(schema, values, path, depth, max_depth, bound) do
    {schema, bound} = enter(schema, bound)
    here = local(schema, values, path)

    below =
      if depth < max_depth do
        descend(schema, values, path, depth, max_depth, bound)
      else
        []
      end

    here ++ below
  end

  defp local(schema, values, path) do
    ctor_tests(schema, path) ++
      compare_tests(schema, values, path) ++
      nat_tests(schema, values, path) ++
      len_tests(schema, values, path) ++
      binder_tests(schema, values, path)
  end

  # A relevant field records `qty` and `name`. The quantity is the
  # telescope's grade, the same at every value of that constructor, so
  # a test of it is constant or a duplicate of `ctor-is`. A use count
  # is not a reading of the value: the binder name does not occur in
  # the term. A later encoding that stores a grade or an occurrence
  # in the value fills this in.
  defp binder_tests(_schema, _values, _path), do: []

  defp ctor_tests({:enum, _, ctors}, path) when length(ctors) >= 2 do
    Enum.map(ctors, &%{kind: :ctor_is, path: path, tag: &1})
  end

  defp ctor_tests({:data, _, ctors}, path) when length(ctors) >= 2 do
    Enum.map(ctors, &%{kind: :ctor_is, path: path, tag: &1.name})
  end

  defp ctor_tests(_, _), do: []

  defp compare_tests({:data, _, ctors}, _values, path) do
    Enum.flat_map(ctors, fn ctor ->
      ctor.fields
      |> pair_indexes()
      |> Enum.flat_map(fn {i, j, elem} ->
        trio(path, :fields, i, j, elem, ctor.name)
      end)
    end)
  end

  defp compare_tests({:prod, left, right}, _values, path) do
    case same_family(left, right) do
      nil -> []
      elem -> trio(path, :fields, 0, 1, elem, nil)
    end
  end

  defp compare_tests({:list, elem}, values, path) do
    case family(elem) do
      nil ->
        []

      fam ->
        max_len = max_len(values)

        if max_len >= 2 do
          for j <- 1..(max_len - 1)//1,
              i <- 0..(j - 1)//1,
              row <- trio(path, :list, i, j, fam, nil) do
            row
          end
        else
          []
        end
    end
  end

  defp compare_tests(_, _, _), do: []

  defp nat_tests(:nat, _values, []), do: []

  defp nat_tests(:nat, values, path) do
    values
    |> Enum.flat_map(fn value ->
      case canon_nat(value) do
        {:ok, n} -> [n]
        :error -> []
      end
    end)
    |> Enum.uniq()
    |> Enum.map(&%{kind: :nat_is, path: path, n: &1})
  end

  defp nat_tests(_, _, _), do: []

  defp len_tests({:list, elem}, values, path) do
    max_len = max_len(values)

    for n <- 0..max_len//1 do
      %{kind: :len_is, path: path, n: n, elem: elem}
    end
  end

  defp len_tests(_, _, _), do: []

  defp trio(path, view, i, j, elem, ctor) do
    base = %{path: path, view: view, i: i, j: j, elem: elem, ctor: ctor}

    [
      Map.put(base, :kind, :vals_eq),
      Map.put(base, :kind, :spread_eq),
      Map.put(base, :kind, :pair_any)
    ]
  end

  defp pair_indexes(fields) do
    indexed = fields |> Enum.map(&field_schema/1) |> Enum.with_index()

    for {left, i} <- indexed,
        {right, j} <- indexed,
        i < j,
        fam = same_family(left, right),
        fam != nil do
      {i, j, fam}
    end
  end

  defp same_family(left, right) do
    case {family(left), family(right)} do
      {nil, _} -> nil
      {_, nil} -> nil
      {fam, fam} -> fam
      _ -> nil
    end
  end

  defp family(:nat), do: :nat
  defp family({:enum, name, ctors}), do: {:enum, name, ctors}
  defp family(_), do: nil

  defp descend({:data, _, [ctor]}, values, path, depth, max_depth, bound) do
    ctor.fields
    |> Enum.with_index()
    |> Enum.flat_map(fn {field, i} ->
      projected = Enum.map(values, &data_field(&1, i))
      collect(field_schema(field), projected, path ++ [i], depth + 1, max_depth, bound)
    end)
  end

  defp descend({:data, _, ctors}, values, path, depth, max_depth, bound) do
    Enum.flat_map(ctors, fn ctor ->
      subset = Enum.filter(values, &(tag_name(&1, ctors) == ctor.name))

      ctor.fields
      |> Enum.with_index()
      |> Enum.flat_map(fn {field, i} ->
        projected = Enum.map(subset, &data_field(&1, i))

        field_schema(field)
        |> collect(projected, path ++ [i], depth + 1, max_depth, bound)
        |> Enum.map(&add_guard(&1, path, ctor.name))
      end)
    end)
  end

  defp descend({:prod, left, right}, values, path, depth, max_depth, bound) do
    collect(left, Enum.map(values, &elem(&1, 0)), path ++ [0], depth + 1, max_depth, bound) ++
      collect(right, Enum.map(values, &elem(&1, 1)), path ++ [1], depth + 1, max_depth, bound)
  end

  # A list's tests are the positions and the length, at this node.
  # An element is not a field step. Invention reads a list difference.
  defp descend({:list, _}, _values, _path, _depth, _max_depth, _bound), do: []
  defp descend(_schema, _values, _path, _depth, _max_depth, _bound), do: []

  defp add_guard(spec, prefix, ctor) do
    Map.update(spec, :guards, [{prefix, ctor}], &(&1 ++ [{prefix, ctor}]))
  end

  defp diffs(schema, left, right, path, bound) do
    {schema, bound} = enter(schema, bound)

    if left == right do
      []
    else
      diff_at(schema, left, right, path, bound)
    end
  end

  defp diff_at({:enum, _, _} = schema, left, right, path, _bound),
    do: [{path, schema, left, right}]

  defp diff_at(:nat, left, right, path, _bound), do: [{path, :nat, left, right}]

  defp diff_at({:data, _, ctors} = schema, left, right, path, bound) do
    ltag = tag_name(left, ctors)
    rtag = tag_name(right, ctors)

    if ltag != rtag or ltag == nil do
      [{path, schema, left, right}]
    else
      ctor = Enum.find(ctors, &(&1.name == ltag))

      ctor.fields
      |> Enum.with_index()
      |> Enum.flat_map(fn {field, i} ->
        diffs(field_schema(field), data_field(left, i), data_field(right, i), path ++ [i], bound)
      end)
    end
  end

  defp diff_at({:prod, a, b}, {l1, r1}, {l2, r2}, path, bound) do
    diffs(a, l1, l2, path ++ [0], bound) ++ diffs(b, r1, r2, path ++ [1], bound)
  end

  defp diff_at({:list, elem} = schema, left, right, path, bound) do
    here = [{path, schema, left, right}]
    ls = list_items(left)
    rs = list_items(right)

    deeper =
      ls
      |> Enum.zip(rs)
      |> Enum.with_index()
      |> Enum.flat_map(fn {{a, b}, i} -> diffs(elem, a, b, path ++ [i], bound) end)

    here ++ deeper
  end

  defp diff_at(_, _, _, _, _), do: []

  defp name_specs(specs, taken) do
    Enum.map_reduce(specs, taken, fn spec, taken ->
      name = fresh(base_name(spec), taken)
      {Map.put(spec, :name, name), take(taken, name)}
    end)
  end

  defp base_name(%{kind: :ctor_is, path: path, tag: tag}) do
    join_name(["ctor-is", path_tag(path), guard_tag(path), tag])
  end

  defp base_name(%{kind: kind, path: path, i: i, j: j} = spec)
       when kind in [:vals_eq, :spread_eq, :pair_any] do
    join_name([kind_word(kind), path_tag(path), guard_tag(spec), "#{i}", "#{j}"])
  end

  defp base_name(%{kind: :len_is, path: path, n: n} = spec) do
    join_name(["len-is", path_tag(path), guard_tag(spec), "#{n}"])
  end

  defp base_name(%{kind: :nat_is, path: path, n: n} = spec) do
    join_name(["nat-is", path_tag(path), guard_tag(spec), "#{n}"])
  end

  defp kind_word(:vals_eq), do: "vals-eq"
  defp kind_word(:spread_eq), do: "spread-eq"
  defp kind_word(:pair_any), do: "pair-any"

  defp path_tag([]), do: nil

  defp path_tag([head | tail]) do
    Enum.join(["p#{head}" | Enum.map(tail, &Integer.to_string/1)], "-")
  end

  defp guard_tag(%{guards: [{_path, ctor} | _]}), do: ctor
  defp guard_tag(_), do: nil

  defp join_name(parts) do
    parts |> Enum.reject(&is_nil/1) |> Enum.join("-")
  end

  defp spec_key(spec) do
    {
      spec.kind,
      Map.get(spec, :path, []),
      Map.get(spec, :view),
      Map.get(spec, :i),
      Map.get(spec, :j),
      Map.get(spec, :tag),
      Map.get(spec, :n),
      Map.get(spec, :ctor),
      Map.get(spec, :guards)
    }
  end

  defp dig(schema, path, value, guards), do: dig(schema, path, value, guards, %{})

  defp dig(schema, [], value, guards, bound) do
    {schema, _bound} = enter(schema, bound)

    case require_guard(guards, [], value, schema) do
      :miss -> :miss
      :ok -> {:ok, schema, value}
    end
  end

  defp dig(schema, [index | rest], value, guards, bound) do
    {schema, bound} = enter(schema, bound)

    case require_guard(guards, [], value, schema) do
      :miss ->
        :miss

      :ok ->
        case step_field(schema, index, value) do
          :miss -> :miss
          {:ok, sub, child} -> dig_from(sub, rest, child, guards, [index], bound)
        end
    end
  end

  defp dig_from(schema, [], value, guards, walked, bound) do
    {schema, _bound} = enter(schema, bound)

    case require_guard(guards, walked, value, schema) do
      :miss -> :miss
      :ok -> {:ok, schema, value}
    end
  end

  defp dig_from(schema, [index | rest], value, guards, walked, bound) do
    {schema, bound} = enter(schema, bound)

    case require_guard(guards, walked, value, schema) do
      :miss ->
        :miss

      :ok ->
        case step_field(schema, index, value) do
          :miss -> :miss
          {:ok, sub, child} -> dig_from(sub, rest, child, guards, walked ++ [index], bound)
        end
    end
  end

  defp require_guard(guards, walked, value, schema) do
    case Enum.find(guards, fn {prefix, _} -> prefix == walked end) do
      nil ->
        :ok

      {_prefix, ctor} ->
        if tag_name(value, ctors_of(schema)) == ctor, do: :ok, else: :miss
    end
  end

  defp ctors_of({:data, _, ctors}), do: ctors
  defp ctors_of(_), do: []

  defp step_field({:data, _, ctors}, index, value) do
    case Enum.find(ctors, &(atom_of(&1.name) == tag_atom(value))) do
      nil ->
        :miss

      ctor ->
        if index < length(ctor.fields) do
          {:ok, field_schema(Enum.at(ctor.fields, index)), data_field(value, index)}
        else
          :miss
        end
    end
  end

  defp step_field({:prod, left, _}, 0, {a, _}), do: {:ok, left, a}
  defp step_field({:prod, _, right}, 1, {_, b}), do: {:ok, right, b}

  defp step_field({:list, elem}, index, value) do
    case Enum.at(list_items(value), index) do
      nil -> :miss
      item -> {:ok, elem, item}
    end
  end

  defp step_field(_, _, _), do: :miss

  defp bit(%{kind: :ctor_is, tag: tag}, schema, value) do
    tag_name(value, ctors_of(schema)) == tag or enum_name(schema, value) == tag
  end

  defp bit(%{kind: :nat_is, n: n}, :nat, value) do
    case canon_nat(value) do
      {:ok, ^n} -> true
      _ -> false
    end
  end

  defp bit(%{kind: :len_is, n: n}, {:list, _}, value), do: length(list_items(value)) == n

  defp bit(%{kind: kind, view: view, i: i, j: j, elem: elem}, schema, value)
       when kind in [:vals_eq, :spread_eq, :pair_any] do
    compare(kind, view, schema, value, i, j, elem)
  end

  defp bit(_, _, _), do: false

  defp compare(kind, :list, _schema, value, i, j, elem) do
    items = list_items(value)

    if j < length(items) do
      relate(kind, Enum.at(items, i), Enum.at(items, j), i, j, elem)
    else
      false
    end
  end

  defp compare(kind, :fields, schema, value, i, j, elem) do
    with {:ok, a} <- field_at(schema, value, i),
         {:ok, b} <- field_at(schema, value, j) do
      relate(kind, a, b, i, j, elem)
    else
      _ -> false
    end
  end

  defp compare(_, _, _, _, _, _, _), do: false

  defp relate(:vals_eq, a, b, _i, _j, elem) do
    case {number(a, elem), number(b, elem)} do
      {{:ok, n}, {:ok, n}} -> true
      _ -> false
    end
  end

  defp relate(:spread_eq, a, b, i, j, elem) do
    case {number(a, elem), number(b, elem)} do
      {{:ok, x}, {:ok, y}} -> abs(x - y) == abs(i - j)
      _ -> false
    end
  end

  defp relate(:pair_any, a, b, i, j, elem) do
    relate(:vals_eq, a, b, i, j, elem) or relate(:spread_eq, a, b, i, j, elem)
  end

  defp number(value, :nat) do
    case canon_nat(value) do
      {:ok, n} -> {:ok, n}
      :error -> :error
    end
  end

  defp number(value, {:enum, _name, ctors}) when is_atom(value) do
    case Enum.find_index(ctors, &(atom_of(&1) == value)) do
      nil -> :error
      index -> {:ok, index}
    end
  end

  defp number(_, _), do: :error

  defp field_at({:data, _, ctors}, value, index) do
    case Enum.find(ctors, &(atom_of(&1.name) == tag_atom(value))) do
      %{fields: fields} when index < length(fields) -> {:ok, data_field(value, index)}
      _ -> :error
    end
  end

  defp field_at({:prod, _, _}, {a, _}, 0), do: {:ok, a}
  defp field_at({:prod, _, _}, {_, b}, 1), do: {:ok, b}
  defp field_at(_, _, _), do: :error

  defp enum_name({:enum, _, ctors}, value) when is_atom(value) do
    Enum.find(ctors, &(atom_of(&1) == value))
  end

  defp enum_name(_, _), do: nil

  defp test_at(schema, hole, path, spec, helpers, walked) do
    test_at(schema, hole, path, spec, helpers, walked, %{})
  end

  defp test_at(schema, hole, [], spec, helpers, walked, bound) do
    {schema, _bound} = enter(schema, bound)
    leaf_test(schema, hole, spec, helpers, walked)
  end

  defp test_at(schema, hole, [index | rest], spec, helpers, walked, bound) do
    {schema, bound} = enter(schema, bound)
    test_step(schema, hole, index, rest, spec, helpers, walked, bound)
  end

  defp test_step({:data, _, ctors} = schema, hole, index, rest, spec, helpers, walked, bound) do
    wanted = guard_ctor(spec, walked)

    arms =
      Enum.map_join(ctors, "\n", fn ctor ->
        if wanted != nil and ctor.name != wanted do
          "| #{pat(ctor.name, wild(ctor))} => false"
        else
          binder = "x#{length(walked)}"
          binders = focus(ctor, index, binder)
          field = ctor.fields |> Enum.at(index) |> field_schema()
          inner = test_at(field, binder, rest, spec, helpers, walked ++ [index], bound)
          "| #{pat(ctor.name, binders)} => #{inner}"
        end
      end)

    match_bool(hole, arms, schema)
  end

  defp test_step({:prod, left, right}, hole, index, rest, spec, helpers, walked, bound) do
    binder = "x#{length(walked)}"
    {b0, b1} = if index == 0, do: {binder, "_"}, else: {"_", binder}
    field = if index == 0, do: left, else: right
    inner = test_at(field, binder, rest, spec, helpers, walked ++ [index], bound)
    let_pair(hole, b0, b1, inner)
  end

  defp test_step({:list, elem}, hole, index, rest, spec, helpers, walked, bound) do
    binder = "x#{length(walked)}"
    inner = test_at(elem, binder, rest, spec, helpers, walked ++ [index], bound)
    peel_cons(hole, index, binder, inner, type_name(elem))
  end

  defp test_step(_schema, _hole, _index, _rest, _spec, _helpers, _walked, _bound), do: "false"

  defp leaf_test({:enum, _, ctors}, hole, %{kind: :ctor_is, tag: tag}, _helpers, _walked) do
    arms =
      Enum.map_join(ctors, "\n", fn ctor ->
        bit = if ctor == tag, do: "true", else: "false"
        "| #{ctor} => #{bit}"
      end)

    match_bool(hole, arms, {:enum, "", ctors})
  end

  defp leaf_test({:data, _, ctors}, hole, %{kind: :ctor_is, tag: tag}, _helpers, _walked) do
    arms =
      Enum.map_join(ctors, "\n", fn ctor ->
        bit = if ctor.name == tag, do: "true", else: "false"
        "| #{pat(ctor.name, wild(ctor))} => #{bit}"
      end)

    match_bool(hole, arms, {:data, "", ctors})
  end

  defp leaf_test(:nat, hole, %{kind: :nat_is, n: n}, helpers, _walked) do
    "#{helpers.nat_eq} #{hole} #{spell_nat(n)}"
  end

  defp leaf_test({:list, elem}, hole, %{kind: :len_is, n: n}, helpers, _walked) do
    "#{helpers.nat_eq} (#{helpers.list_len} #{type_name(elem)} #{hole}) #{spell_nat(n)}"
  end

  defp leaf_test(schema, hole, %{view: :fields, i: i, j: j, kind: kind} = spec, helpers, _walked)
       when kind in [:vals_eq, :spread_eq, :pair_any] do
    key = {:cmp, kind, spec.elem, abs(j - i)}
    fun = Map.fetch!(helpers.funs, key)
    field_call(schema, hole, spec, i, j, fun)
  end

  defp leaf_test({:list, _elem}, hole, %{view: :list, kind: kind, i: i, j: j} = spec, helpers, _)
       when kind in [:vals_eq, :spread_eq, :pair_any] do
    key = {:list_cmp, kind, spec.elem, i, j}
    fun = Map.fetch!(helpers.funs, key)
    "#{fun} #{hole}"
  end

  defp leaf_test(_, _, _, _, _), do: "false"

  defp field_call({:data, _, ctors}, hole, spec, i, j, fun) do
    ctor = Enum.find(ctors, &(&1.name == (spec.ctor || hd(ctors).name)))
    xi = "x#{i}"
    xj = "x#{j}"
    binders = focus_two(ctor, i, xi, j, xj)

    arms =
      if length(ctors) == 1 do
        "| #{pat(ctor.name, binders)} => #{fun} #{xi} #{xj}"
      else
        Enum.map_join(ctors, "\n", fn other ->
          if other.name == ctor.name do
            "| #{pat(other.name, binders)} => #{fun} #{xi} #{xj}"
          else
            "| #{pat(other.name, wild(other))} => false"
          end
        end)
      end

    match_bool(hole, arms, {:data, "", ctors})
  end

  defp field_call({:prod, _, _}, hole, _spec, _i, _j, fun) do
    let_pair(hole, "x0", "x1", "#{fun} x0 x1")
  end

  defp field_call(_, _, _, _, _, _), do: "false"

  defp peel_cons(hole, 0, binder, inner, _elem) do
    """
    (match #{hole} motive (λ _ → Bool)
      | nil => false
      | cons #{binder} _ => #{inner})
    """
  end

  defp peel_cons(hole, index, binder, inner, _elem) do
    """
    (match #{hole} motive (λ _ → Bool)
      | nil => false
      | cons _ t => #{peel_cons("t", index - 1, binder, inner, nil)})
    """
  end

  defp match_bool(hole, arms, _schema) do
    """
    (match #{hole} motive (λ _ → Bool)
    #{arms})
    """
  end

  defp guard_ctor(spec, walked) do
    case Enum.find(Map.get(spec, :guards, []), fn {prefix, _} -> prefix == walked end) do
      nil -> nil
      {_prefix, ctor} -> ctor
    end
  end

  defp wild(ctor), do: Enum.map(ctor.fields, fn _ -> "_" end)

  defp focus(ctor, index, binder) do
    ctor.fields
    |> Enum.with_index()
    |> Enum.map(fn {_field, i} -> if i == index, do: binder, else: "_" end)
  end

  defp focus_two(ctor, i, xi, j, xj) do
    ctor.fields
    |> Enum.with_index()
    |> Enum.map(fn {_field, k} ->
      cond do
        k == i -> xi
        k == j -> xj
        true -> "_"
      end
    end)
  end

  defp pat(ctor, []), do: ctor
  defp pat(ctor, binders), do: ctor <> " " <> Enum.join(binders, " ")

  defp build_helpers(specs, taken) do
    needs = helper_needs(specs)
    {funs, taken, parts} = emit_helpers(needs, taken)
    text = parts |> Enum.reject(&(&1 == "")) |> Enum.join("\n")

    {%{
       text: text,
       funs: funs,
       nat_eq: Map.get(funs, :nat_eq),
       list_len: Map.get(funs, :list_len)
     }, taken}
  end

  defp helper_needs(specs) do
    Enum.reduce(specs, MapSet.new(), fn spec, acc ->
      case spec.kind do
        :nat_is ->
          MapSet.put(acc, :nat_eq)

        :len_is ->
          acc |> MapSet.put(:nat_eq) |> MapSet.put(:list_len)

        kind when kind in [:vals_eq, :spread_eq, :pair_any] ->
          acc
          |> MapSet.put(:nat_eq)
          |> needs_abs(kind)
          |> needs_or(kind)
          |> put_enum(spec.elem)
          |> MapSet.put({:cmp, kind, spec.elem, abs(spec.j - spec.i)})
          |> needs_list(spec, kind)

        _ ->
          acc
      end
    end)
  end

  defp needs_abs(set, kind) when kind in [:spread_eq, :pair_any], do: MapSet.put(set, :nat_abs)
  defp needs_abs(set, _), do: set
  defp put_enum(set, {:enum, _, _} = elem), do: MapSet.put(set, {:enum_fun, elem})
  defp put_enum(set, _), do: set
  defp needs_or(set, :pair_any), do: MapSet.put(set, :bit_or)
  defp needs_or(set, _), do: set

  defp needs_list(set, %{view: :list, elem: elem, i: i, j: j}, kind) do
    set
    |> MapSet.put(:list_len)
    |> MapSet.put(:list_has)
    |> MapSet.put(:list_at)
    |> MapSet.put({:list_cmp, kind, elem, i, j})
  end

  defp needs_list(set, _, _), do: set

  defp emit_helpers(needs, taken) do
    {funs, taken, parts} =
      Enum.reduce(ordered_needs(needs), {%{}, taken, []}, fn need, {funs, taken, parts} ->
        {key, base, source} = helper_def(need, funs)
        {name, taken} = Muro.Synth.Book.reserve(base, taken)
        text = source.(name)
        {Map.put(funs, key, name), taken, parts ++ [text]}
      end)

    {funs, taken, parts}
  end

  defp ordered_needs(needs) do
    keys =
      [:nat_eq, :nat_abs, :bit_or, :list_len, :list_has, :list_at] ++
        (needs |> MapSet.to_list() |> Enum.filter(&match?({:enum_fun, _}, &1))) ++
        (needs |> MapSet.to_list() |> Enum.filter(&match?({:cmp, _, _, _}, &1))) ++
        (needs |> MapSet.to_list() |> Enum.filter(&match?({:list_cmp, _, _, _, _}, &1)))

    Enum.filter(keys, &MapSet.member?(needs, &1))
  end

  defp helper_def(:nat_eq, _funs), do: {:nat_eq, "nat-eq", &nat_eq_source/1}
  defp helper_def(:nat_abs, _funs), do: {:nat_abs, "nat-abs", &nat_abs_source/1}
  defp helper_def(:bit_or, _funs), do: {:bit_or, "bit-or", &bit_or_source/1}
  defp helper_def(:list_len, _funs), do: {:list_len, "list-len", &list_len_source/1}
  defp helper_def(:list_has, _funs), do: {:list_has, "list-has", &list_has_source/1}
  defp helper_def(:list_at, _funs), do: {:list_at, "list-at", &list_at_source/1}

  defp helper_def({:enum_fun, {:enum, name, ctors}}, _funs) do
    {{:enum, name}, "nat-of-#{name}", fn def_name -> enum_nat_source(def_name, name, ctors) end}
  end

  defp helper_def({:cmp, kind, elem, gap}, funs) do
    key = {:cmp, kind, elem, gap}
    base = "cmp-#{kind_word(kind)}-#{elem_word(elem)}-#{gap}"
    {key, base, fn def_name -> cmp_source(def_name, kind, elem, gap, funs) end}
  end

  defp helper_def({:list_cmp, kind, elem, i, j}, funs) do
    key = {:list_cmp, kind, elem, i, j}
    base = "cmp-list-#{kind_word(kind)}-#{elem_word(elem)}-#{i}-#{j}"
    {key, base, fn def_name -> list_cmp_source(def_name, kind, elem, i, j, funs) end}
  end

  defp elem_word(:nat), do: "Nat"
  defp elem_word({:enum, name, _}), do: name

  defp nat_eq_source(name) do
    """
    def #{name} : run Π (+ n : Nat) → Π (+ m : Nat) → Bool :=
      λ (+ n : Nat) → λ (+ m : Nat) →
        match n motive (λ _ → Bool)
          | 0 =>
              (match m motive (λ _ → Bool)
                | 0 => true
                | suc _ => false)
          | suc n1 =>
              (match m motive (λ _ → Bool)
                | 0 => false
                | suc m1 => #{name} n1 m1)
    """
  end

  defp nat_abs_source(name) do
    monus = name <> "-monus"

    """
    def #{monus} : run Π (+ n : Nat) → Π (+ m : Nat) → Nat :=
      λ (+ n : Nat) → λ (+ m : Nat) →
        match n motive (λ _ → Nat)
          | 0 => 0
          | suc n1 =>
              (match m motive (λ _ → Nat)
                | 0 => suc n1
                | suc m1 => #{monus} n1 m1)
    def #{name} : run Π (+ n : Nat) → Π (+ m : Nat) → Nat :=
      λ (+ n : Nat) → λ (+ m : Nat) →
        plus (#{monus} n m) (#{monus} m n)
    """
  end

  defp bit_or_source(name) do
    """
    def #{name} : run Π (p : Bool) → Π (q : Bool) → Bool :=
      λ (p : Bool) → λ (q : Bool) →
        match p motive (λ _ → Bool)
          | true => true
          | false => q
    """
  end

  defp list_len_source(name) do
    """
    def #{name} : run Π (- A : Type) → Π (xs : List A) → Nat :=
      λ (- A : Type) → λ (xs : List A) →
        match xs motive (λ _ → Nat)
          | nil => 0
          | cons _ ys => suc (#{name} A ys)
    """
  end

  defp list_has_source(name) do
    """
    def #{name} : run Π (- A : Type) → Π (xs : List A) → Π (n : Nat) → Bool :=
      λ (- A : Type) → λ (xs : List A) → λ (n : Nat) →
        match n motive (λ _ → Bool)
          | 0 =>
              (match xs motive (λ _ → Bool)
                | nil => false
                | cons _ _ => true)
          | suc n1 =>
              (match xs motive (λ _ → Bool)
                | nil => false
                | cons _ ys => #{name} A ys n1)
    """
  end

  defp list_at_source(name) do
    """
    def #{name} : run Π (- A : Type) → Π (xs : List A) → Π (n : Nat) → Π (d : A) → A :=
      λ (- A : Type) → λ (xs : List A) → λ (n : Nat) → λ (d : A) →
        match n motive (λ _ → A)
          | 0 =>
              (match xs motive (λ _ → A)
                | nil => d
                | cons h _ => h)
          | suc n1 =>
              (match xs motive (λ _ → A)
                | nil => d
                | cons _ ys => #{name} A ys n1 d)
    """
  end

  defp enum_nat_source(name, type_name, ctors) do
    arms =
      ctors
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {ctor, index} ->
        "      | #{ctor} => #{spell_nat(index)}"
      end)

    """
    def #{name} : run Π (+ x : #{type_name}) → Nat :=
      λ (+ x : #{type_name}) →
        match x motive (λ _ → Nat)
    #{arms}
    """
  end

  defp cmp_source(name, kind, elem, gap, funs) do
    type_name = elem_type(elem)
    body = cmp_body(kind, elem, gap, "x", "y", funs)

    """
    def #{name} : run Π (+ x : #{type_name}) → Π (+ y : #{type_name}) → Bool :=
      λ (+ x : #{type_name}) → λ (+ y : #{type_name}) →
        #{body}
    """
  end

  defp cmp_body(kind, elem, gap, x, y, funs) do
    nx = num_expr(elem, x, funs)
    ny = num_expr(elem, y, funs)
    eq = "#{funs.nat_eq} #{nx} #{ny}"

    spread =
      "#{funs.nat_eq} (#{funs[:nat_abs]} #{nx} #{ny}) #{spell_nat(gap)}"

    case kind do
      :vals_eq -> eq
      :spread_eq -> spread
      :pair_any -> "#{funs[:bit_or]} (#{eq}) (#{spread})"
    end
  end

  defp num_expr(:nat, var, _funs), do: var

  defp num_expr({:enum, name, _}, var, funs) do
    "(#{Map.fetch!(funs, {:enum, name})} #{var})"
  end

  defp list_cmp_source(name, kind, elem, i, j, funs) do
    ty = elem_type(elem)
    default = default_of(elem)
    cmp = Map.fetch!(funs, {:cmp, kind, elem, abs(j - i)})
    has = funs.list_has
    at = funs.list_at

    """
    def #{name} : run Π (+ xs : List #{ty}) → Bool :=
      λ (+ xs : List #{ty}) →
        (match (#{has} #{ty} xs #{spell_nat(j)}) motive (λ _ → Bool)
          | true => #{cmp} (#{at} #{ty} xs #{spell_nat(i)} #{default}) (#{at} #{ty} xs #{spell_nat(j)} #{default})
          | false => false)
    """
  end

  defp elem_type(:nat), do: "Nat"
  defp elem_type({:enum, name, _}), do: name

  defp default_of(:nat), do: "0"
  defp default_of({:enum, _name, [ctor | _]}), do: ctor

  # `seen` stops a second visit to the same datatype. Exhaustive
  # equality is only emitted for a finite inhabitant list, which has
  # no back-edge; the set is the guard if one is handed in.
  defp open(schema, hole, plug, type_of, body_of, k) do
    open(schema, hole, plug, type_of, body_of, k, MapSet.new())
  end

  defp open({:data, name, ctors}, hole, plug, type_of, body_of, k, seen) do
    if MapSet.member?(seen, name) do
      body_of.(hole)
    else
      var = "k#{k}"
      motive = "(λ (#{var} : #{name}) → #{type_of.(plug.(var))})"
      seen = MapSet.put(seen, name)

      arms =
        Enum.map_join(ctors, "\n", fn ctor ->
          binders = binders(length(ctor.fields), k)
          local = app_src(ctor.name, binders)

          inner =
            open_fields(ctor.fields, binders, local, plug, type_of, body_of, k + 1, seen)

          "| #{pat(ctor.name, binders)} => #{inner}"
        end)

      """
      (match #{hole} motive #{motive}
      #{arms})
      """
    end
  end

  defp open({:enum, name, ctors}, hole, plug, type_of, body_of, k, _seen) do
    var = "k#{k}"
    motive = "(λ (#{var} : #{name}) → #{type_of.(plug.(var))})"
    arms = Enum.map_join(ctors, "\n", fn ctor -> "| #{ctor} => #{body_of.(ctor)}" end)

    """
    (match #{hole} motive #{motive}
    #{arms})
    """
  end

  defp open({:prod, left, right}, hole, plug, type_of, body_of, k, seen) do
    b0 = "f#{k}_0"
    b1 = "f#{k}_1"
    local = "(#{b0}, #{b1})"
    inner = open_fields([left, right], [b0, b1], local, plug, type_of, body_of, k + 1, seen)
    let_pair(hole, b0, b1, inner)
  end

  defp open(_schema, hole, _plug, _type_of, body_of, _k, _seen), do: body_of.(hole)

  defp open_fields([], _binders, local, _plug, _type_of, body_of, _k, _seen),
    do: body_of.(local)

  defp open_fields([field | rest], [binder | binders], local, plug, type_of, body_of, k, seen) do
    on_concrete = fn concrete ->
      open_fields(
        rest,
        binders,
        subst(local, binder, concrete),
        plug,
        type_of,
        body_of,
        k + 1,
        seen
      )
    end

    plug_src = fn src -> plug.(subst(local, binder, src)) end
    open(field_schema(field), binder, plug_src, type_of, on_concrete, k, seen)
  end

  defp binders(0, _k), do: []
  defp binders(n, k), do: Enum.map(0..(n - 1)//1, &"f#{k}_#{&1}")

  defp app_src(ctor, []), do: ctor
  defp app_src(ctor, args), do: "(" <> Enum.join([ctor | Enum.map(args, &arg/1)], " ") <> ")"

  defp subst(src, binder, repl) do
    Regex.replace(~r/(?<![A-Za-z0-9_-])#{Regex.escape(binder)}(?![A-Za-z0-9_-])/, src, fn _ ->
      repl
    end)
  end

  # A pair is opened with `let`, not a match arm. `| (a, b) =>` is not
  # a constructor pattern.
  defp let_pair(hole, a, b, inner) do
    "(let (#{a}, #{b}) = #{hole} in #{inner})"
  end

  defp type_name(:nat), do: "Nat"
  defp type_name({:enum, name, _}), do: name
  defp type_name({:data, name, _}), do: name
  defp type_name({:rec, name}), do: name
  defp type_name({:list, elem}), do: "(List #{type_name(elem)})"
  defp type_name({:prod, left, right}), do: "(#{type_name(left)} × #{type_name(right)})"
  defp type_name({:open, _}), do: "Type"

  defp fresh(base, taken) do
    if occupied?(base, taken) do
      n = Enum.find(2..10_000, &(not occupied?("#{base}-#{&1}", taken)))
      "#{base}-#{n}"
    else
      base
    end
  end

  defp occupied?(name, taken) do
    MapSet.member?(taken, name) or MapSet.member?(taken, {:elixir, Muro.Emit.elixir_base(name)})
  end

  defp take(taken, name) do
    taken
    |> MapSet.put(name)
    |> MapSet.put({:elixir, Muro.Emit.elixir_base(name)})
  end

  defp tag_atom(atom) when is_atom(atom), do: atom
  defp tag_atom(tuple) when is_tuple(tuple) and tuple_size(tuple) >= 1, do: elem(tuple, 0)

  defp raw_fields(atom) when is_atom(atom), do: []
  defp raw_fields(tuple) when is_tuple(tuple), do: Tuple.to_list(tuple) |> tl()

  defp data_field(atom, _index) when is_atom(atom), do: nil
  defp data_field(tuple, index) when is_tuple(tuple), do: elem(tuple, index + 1)

  defp tag_name(value, ctors) do
    atom = tag_atom(value)
    Enum.find_value(ctors, fn ctor -> if atom_of(ctor.name) == atom, do: ctor.name end)
  end

  defp list_items(nil), do: []
  defp list_items({:cons, head, tail}), do: [head | list_items(tail)]
  defp list_items(_), do: []

  defp max_len(values) do
    values
    |> Enum.map(&length(list_items(&1)))
    |> Enum.max(fn -> 0 end)
  end

  defp canon_list(nil), do: {:ok, []}

  defp canon_list({:cons, head, tail}) do
    case canon_list(tail) do
      {:ok, rest} -> {:ok, [head | rest]}
      :error -> :error
    end
  end

  defp canon_list(_), do: :error

  defp encode_list([]), do: nil
  defp encode_list([head | tail]), do: {:cons, head, encode_list(tail)}

  defp list_spell([]), do: "nil"

  defp list_spell(spells) do
    Enum.reduce(Enum.reverse(spells), "nil", fn spell, acc ->
      "(cons #{arg(spell)} #{arg(acc)})"
    end)
  end

  defp list_label([]), do: "nil"
  defp list_label(labels), do: "cons-" <> Enum.join(labels, "-")

  defp canon_nat(0), do: {:ok, 0}
  defp canon_nat(n) when is_integer(n) and n >= 0, do: {:ok, n}

  defp canon_nat({:suc, n}) do
    case canon_nat(n) do
      {:ok, k} -> {:ok, k + 1}
      :error -> :error
    end
  end

  defp canon_nat(_), do: :error

  def spell_nat(0), do: "0"
  def spell_nat(1), do: "suc 0"

  def spell_nat(n) when is_integer(n) and n > 1 do
    "suc (" <> spell_nat(n - 1) <> ")"
  end

  defp arg(spell) do
    cond do
      String.starts_with?(spell, "(") -> spell
      String.contains?(spell, " ") -> "(#{spell})"
      true -> spell
    end
  end

  # Dependencies before the type that uses them. A repeated schema is one
  # function. `opening` is the datatype whose equality is being built:
  # a direct back-edge to it is that same function. A back-edge under a
  # list or a product is not a run, because a field is smaller only when
  # its type is the datatype being matched. A linear field is not a run:
  # the unequal arm would drop it. A function or an empty declaration
  # is not a run.
  defp eq_nodes(schema, acc), do: eq_nodes(schema, acc, MapSet.new())

  defp eq_nodes(schema, acc, opening) do
    if schema in acc do
      {:ok, acc}
    else
      eq_fresh(schema, acc, opening)
    end
  end

  defp eq_fresh({:rec, name}, acc, opening) do
    cond do
      MapSet.member?(opening, name) -> {:ok, acc}
      Enum.any?(acc, &match?({:data, ^name, _}, &1)) -> {:ok, acc}
      true -> :open
    end
  end

  defp eq_fresh(:nat, acc, _opening), do: {:ok, acc ++ [:nat]}

  defp eq_fresh({:enum, _, ctors} = schema, acc, _opening) when ctors != [] do
    {:ok, acc ++ [schema]}
  end

  defp eq_fresh({:list, elem} = schema, acc, opening) do
    if refers_opening?(elem, opening) do
      :open
    else
      case eq_nodes(elem, acc, opening) do
        {:ok, acc} -> {:ok, acc ++ [schema]}
        :open -> :open
      end
    end
  end

  defp eq_fresh({:prod, left, right} = schema, acc, opening) do
    if refers_opening?(left, opening) or refers_opening?(right, opening) do
      :open
    else
      with {:ok, acc} <- eq_nodes(left, acc, opening),
           {:ok, acc} <- eq_nodes(right, acc, opening) do
        {:ok, acc ++ [schema]}
      end
    end
  end

  defp eq_fresh({:data, name, rows} = schema, acc, opening) when rows != [] do
    cond do
      linear_rows?(rows) or erased_rows?(rows) ->
        :open

      true ->
        opening = MapSet.put(opening, name)

        case eq_rows(rows, acc, opening) do
          {:ok, acc} -> {:ok, acc ++ [schema]}
          :open -> :open
        end
    end
  end

  defp eq_fresh(_schema, _acc, _opening), do: :open

  defp linear_rows?(rows) do
    Enum.any?(rows, fn row -> Enum.any?(row.fields, &linear_field?/1) end)
  end

  defp erased_rows?(rows) do
    Enum.any?(rows, &Map.get(&1, :erased, false))
  end

  defp refusal_in({:open, "function"}), do: "State has a function field"

  defp refusal_in({:data, name, rows}) do
    cond do
      erased_rows?(rows) ->
        "State has an erased constructor argument"

      linear_rows?(rows) ->
        "State has a linear field"

      rec_under_container?(rows, name) ->
        "State recursion under List/product cannot be certified"

      true ->
        Enum.find_value(rows, fn row ->
          Enum.find_value(row.fields, &refusal_in(field_schema(&1)))
        end)
    end
  end

  defp refusal_in({:list, elem}), do: refusal_in(elem)
  defp refusal_in({:prod, left, right}), do: refusal_in(left) || refusal_in(right)
  defp refusal_in(_schema), do: nil

  # A back-edge under a list or a product, including through a nested
  # datatype. Direct fields of the datatype being split are not this.
  defp rec_under_container?(rows, name) when is_binary(name) do
    rec_under_container?(rows, MapSet.new([name]))
  end

  defp rec_under_container?(rows, opening) when is_list(rows) do
    Enum.any?(rows, fn row ->
      Enum.any?(row.fields, &container_rec?(field_schema(&1), opening))
    end)
  end

  defp container_rec?({:list, elem}, opening), do: refers_opening?(elem, opening)

  defp container_rec?({:prod, left, right}, opening) do
    refers_opening?(left, opening) or refers_opening?(right, opening)
  end

  defp container_rec?({:data, name, rows}, opening) do
    rec_under_container?(rows, MapSet.put(opening, name))
  end

  defp container_rec?(_schema, _opening), do: false

  # A recursive occurrence of a datatype whose equality is already being
  # built. A nested datatype is walked on its own; this only sees a
  # back-edge that would have to be matched under a list or a product.
  defp refers_opening?({:rec, name}, opening), do: MapSet.member?(opening, name)
  defp refers_opening?({:list, elem}, opening), do: refers_opening?(elem, opening)

  defp refers_opening?({:prod, left, right}, opening) do
    refers_opening?(left, opening) or refers_opening?(right, opening)
  end

  defp refers_opening?({:data, _name, rows}, opening) do
    Enum.any?(rows, fn row ->
      Enum.any?(row.fields, &refers_opening?(field_schema(&1), opening))
    end)
  end

  defp refers_opening?(_schema, _opening), do: false

  defp eq_rows(rows, acc, opening) do
    Enum.reduce_while(rows, {:ok, acc}, fn row, {:ok, acc} ->
      case eq_row(row.fields, acc, opening) do
        {:ok, acc} -> {:cont, {:ok, acc}}
        :open -> {:halt, :open}
      end
    end)
  end

  defp eq_row(fields, acc, opening) do
    Enum.reduce_while(fields, {:ok, acc}, fn field, {:ok, acc} ->
      case eq_nodes(field_schema(field), acc, opening) do
        {:ok, acc} -> {:cont, {:ok, acc}}
        :open -> {:halt, :open}
      end
    end)
  end

  defp eq_base(:nat), do: "eq-nat"
  defp eq_base({:enum, name, _}), do: "eq-#{name}"
  defp eq_base({:data, name, _}), do: "eq-#{name}"
  defp eq_base({:list, elem}), do: "eq-list-#{eq_word(elem)}"
  defp eq_base({:prod, left, right}), do: "eq-pair-#{eq_word(left)}-#{eq_word(right)}"

  defp eq_word(:nat), do: "Nat"
  defp eq_word({:enum, name, _}), do: name
  defp eq_word({:data, name, _}), do: name
  defp eq_word({:list, elem}), do: "list-#{eq_word(elem)}"
  defp eq_word({:prod, left, right}), do: "#{eq_word(left)}-#{eq_word(right)}"

  defp eq_root(name, fun) do
    """
    def #{name} : run Π (+ s : State) → Π (+ t : State) → Bool :=
      λ (+ s : State) → λ (+ t : State) →
        #{fun} s t
    """
  end

  defp eq_def(schema, fun, names) do
    ty = eq_type(schema)

    """
    def #{fun} : run Π (x : #{ty}) → Π (y : #{ty}) → Bool :=
      λ (x : #{ty}) → λ (y : #{ty}) →
        #{eq_body(schema, fun, names)}
    """
  end

  defp eq_type(:nat), do: "Nat"
  defp eq_type(schema), do: type_name(schema)

  defp eq_body(:nat, fun, _names) do
    """
    (match x motive (λ _ → Bool)
      | 0 =>
          (match y motive (λ _ → Bool)
            | 0 => true
            | suc _ => false)
      | suc x1 =>
          (match y motive (λ _ → Bool)
            | 0 => false
            | suc y1 => #{fun} x1 y1))
    """
  end

  defp eq_body({:enum, _, ctors}, _fun, _names) do
    arms =
      Enum.map_join(ctors, "\n", fn ctor ->
        inner =
          Enum.map_join(ctors, "\n", fn other ->
            bit = if ctor == other, do: "true", else: "false"
            "        | #{other} => #{bit}"
          end)

        """
          | #{ctor} =>
              (match y motive (λ _ → Bool)
        #{inner})
        """
      end)

    """
    (match x motive (λ _ → Bool)
    #{arms})
    """
  end

  defp eq_body({:list, elem}, fun, names) do
    elem_eq = Map.fetch!(names, elem)

    """
    (match x motive (λ _ → Bool)
      | nil =>
          (match y motive (λ _ → Bool)
            | nil => true
            | cons _ _ => false)
      | cons h t =>
          (match y motive (λ _ → Bool)
            | nil => false
            | cons i u => #{eq_and(["#{elem_eq} h i", "#{fun} t u"])}))
    """
  end

  defp eq_body({:prod, left, right}, _fun, names) do
    inner =
      eq_and([
        "#{Map.fetch!(names, left)} a c",
        "#{Map.fetch!(names, right)} b d"
      ])

    let_pair("x", "a", "b", let_pair("y", "c", "d", inner))
  end

  defp eq_body({:data, _, rows}, _fun, names) do
    arms =
      Enum.map_join(rows, "\n", fn row ->
        xs = eq_binders("p", length(row.fields))

        inner =
          Enum.map_join(rows, "\n", fn other ->
            ys = eq_binders("q", length(other.fields))

            body =
              if other.name == row.name do
                eq_and(eq_calls(row.fields, xs, ys, names))
              else
                "false"
              end

            "        | #{pat(other.name, ys)} => #{body}"
          end)

        """
          | #{pat(row.name, xs)} =>
              (match y motive (λ _ → Bool)
        #{inner})
        """
      end)

    """
    (match x motive (λ _ → Bool)
    #{arms})
    """
  end

  defp eq_calls(fields, xs, ys, names) do
    fields
    |> Enum.map(&field_schema/1)
    |> Enum.zip(xs)
    |> Enum.zip(ys)
    |> Enum.map(fn {{field, x}, y} -> "#{eq_fun(names, field)} #{x} #{y}" end)
  end

  # A back-edge uses the function reserved for that datatype.
  defp eq_fun(names, {:rec, name}) do
    case Enum.find(names, fn
           {{:data, ^name, _}, _fun} -> true
           _ -> false
         end) do
      {_schema, fun} -> fun
      nil -> raise KeyError, key: {:rec, name}, term: names
    end
  end

  defp eq_fun(names, schema), do: Map.fetch!(names, schema)

  defp eq_and([]), do: "true"
  defp eq_and([one]), do: one

  defp eq_and([first | rest]) do
    """
    (match (#{first}) motive (λ _ → Bool)
      | true => #{eq_and(rest)}
      | false => false)
    """
  end

  defp eq_binders(_prefix, 0), do: []
  defp eq_binders(prefix, n), do: Enum.map(0..(n - 1)//1, &"#{prefix}#{&1}")

  @doc """
  A match on `scrutinee` that follows only the terms in `states`.

  `type_of.(src)` is the type of a branch whose source is `src`.
  `body_of.(spell)` is the branch at one cover element.
  `miss.(src)` is a state outside the cover, and `src` is already the
  reconstructed state. A nested split passes that same function
  through: `embed` is what places the piece. `:open` means the terms
  do not determine a split. The caller must not emit a partial match.
  The tree is finite because each step peels a constructor, a list
  cell, or one `suc` toward the largest Nat in the cover.
  """
  def cover_match(schema, scrutinee, states, type_of, body_of, miss)
      when is_binary(scrutinee) and is_list(states) and is_function(type_of, 1) and
             is_function(body_of, 1) and is_function(miss, 1) do
    cands =
      Enum.map(states, fn state ->
        %{spell: spell(state), focus: value_of(state), stack: []}
      end)

    done = fn piece, here, k -> finish_cover(piece, here, body_of, k) end

    case split(schema, scrutinee, & &1, cands, type_of, done, miss, 0, %{}) do
      {:ok, text, _k} -> {:ok, text}
      :open -> :open
    end
  end

  defp finish_cover(piece, cands, body_of, k) do
    case cands |> Enum.map(& &1.spell) |> Enum.uniq() do
      [spell] when spell == piece -> {:ok, body_of.(spell), k}
      _ -> :open
    end
  end

  defp split(_schema, hole, embed, [], _type_of, _continue, miss, k, _bound) do
    {:ok, miss.(embed.(hole)), k}
  end

  # `bound` resolves `{:rec, name}` to the datatype already being split.
  # The split still follows the value, so a finite cover stays finite.
  defp split(schema, hole, embed, cands, type_of, continue, miss, k, bound) do
    {schema, bound} = enter(schema, bound)

    case schema do
      :nat ->
        split_nat(hole, embed, cands, type_of, continue, miss, k)

      {:list, elem} ->
        split_list(elem, hole, embed, cands, type_of, continue, miss, k, bound)

      {:enum, name, ctors} ->
        split_enum(name, ctors, hole, embed, cands, type_of, continue, miss, k)

      {:data, name, rows} ->
        split_data(name, rows, hole, embed, cands, type_of, continue, miss, k, bound)

      {:prod, left, right} ->
        split_prod(left, right, hole, embed, cands, type_of, continue, miss, k, bound)

      _ ->
        :open
    end
  end

  # The zero arm is the remainder `0`. Outer successors live in
  # `prefix`, so the source at depth d is `prefix.("0")`, which is
  # `spell_nat(d)`. A missing number, and every larger `suc`, is a miss.
  defp split_nat(hole, embed, cands, type_of, continue, miss, k) do
    case nat_rank(cands) do
      :open -> :open
      {:ok, ranked} -> nat_from(hole, embed, & &1, ranked, 0, type_of, continue, miss, k)
    end
  end

  defp nat_rank(cands) do
    Enum.reduce_while(cands, {:ok, []}, fn cand, {:ok, acc} ->
      case canon_nat(cand.focus) do
        {:ok, n} -> {:cont, {:ok, [Map.put(cand, :n, n) | acc]}}
        :error -> {:halt, :open}
      end
    end)
    |> case do
      :open -> :open
      {:ok, ranked} -> {:ok, Enum.reverse(ranked)}
    end
  end

  defp nat_from(hole, embed, prefix, cands, depth, type_of, continue, miss, k) do
    var = "n#{k}_#{depth}"
    suc_var = "s#{k}_#{depth}"
    motive = "(λ (#{var} : Nat) → #{type_of.(embed.(prefix.(var)))})"
    here = Enum.filter(cands, &(&1.n == depth))
    deeper = Enum.filter(cands, &(&1.n > depth))

    with {:ok, zero_body, _} <- arm_or_miss(here, prefix.("0"), continue, miss, embed, k),
         {:ok, suc_body, _} <-
           nat_suc(deeper, suc_var, embed, prefix, depth, type_of, continue, miss, k) do
      text =
        match_arms(hole, motive, [
          "| 0 => #{zero_body}",
          "| suc #{suc_var} => #{suc_body}"
        ])

      {:ok, text, k}
    else
      :open -> :open
    end
  end

  defp nat_suc([], suc_var, embed, prefix, _depth, _type_of, _continue, miss, k) do
    {:ok, miss.(embed.(prefix.(suc_spell(suc_var)))), k}
  end

  defp nat_suc(deeper, suc_var, embed, prefix, depth, type_of, continue, miss, k) do
    inner = fn rest -> prefix.(suc_spell(rest)) end
    nat_from(suc_var, embed, inner, deeper, depth + 1, type_of, continue, miss, k)
  end

  # `spell_nat(1)` is `suc 0`. A deeper numeral parenthesises the argument.
  defp suc_spell("0"), do: "suc 0"
  defp suc_spell(rest), do: "suc " <> arg(rest)

  defp split_list(elem, hole, embed, cands, type_of, continue, miss, k, bound) do
    case list_rank(cands) do
      :open ->
        :open

      {:ok, nils, conses} ->
        var = "l#{k}"
        h = "h#{k}"
        t = "t#{k}"
        motive = "(λ (#{var} : #{type_name({:list, elem})}) → #{type_of.(embed.(var))})"

        with {:ok, nil_body, _} <- arm_or_miss(nils, "nil", continue, miss, embed, k),
             {:ok, cons_body, _} <-
               cons_arm(elem, h, t, conses, embed, type_of, continue, miss, k, bound) do
          text =
            match_arms(hole, motive, [
              "| nil => #{nil_body}",
              "| cons #{h} #{t} => #{cons_body}"
            ])

          {:ok, text, k}
        else
          :open -> :open
        end
    end
  end

  defp list_rank(cands) do
    Enum.reduce_while(cands, {:ok, [], []}, fn cand, {:ok, nils, conses} ->
      case cand.focus do
        nil -> {:cont, {:ok, [cand | nils], conses}}
        {:cons, _, _} -> {:cont, {:ok, nils, [cand | conses]}}
        _ -> {:halt, :open}
      end
    end)
    |> case do
      :open -> :open
      {:ok, nils, conses} -> {:ok, Enum.reverse(nils), Enum.reverse(conses)}
    end
  end

  defp cons_arm(_elem, h, t, [], embed, _type_of, _continue, miss, k, _bound) do
    {:ok, miss.(embed.("(cons #{h} #{t})")), k}
  end

  defp cons_arm(elem, h, t, conses, embed, type_of, continue, miss, k, bound) do
    projected =
      Enum.map(conses, fn cand ->
        {:cons, head, tail} = cand.focus
        push(%{cand | focus: head}, {:tail, tail})
      end)

    embed_head = fn src -> embed.(plug("(cons #{h} #{t})", h, src, :arg)) end

    step = fn piece, here, k_here ->
      local = plug("(cons #{h} #{t})", h, piece, :arg)

      case pop_all(here, :tail) do
        :open ->
          :open

        {:ok, pairs} ->
          tails = Enum.map(pairs, fn {tail, cand} -> %{cand | focus: tail} end)
          embed_tail = fn src -> embed.(plug(local, t, src, :arg)) end

          cont = fn tail_piece, here2, k2 ->
            continue.(plug(local, t, tail_piece, :arg), here2, k2)
          end

          split(
            {:list, elem},
            t,
            embed_tail,
            tails,
            type_of,
            cont,
            miss,
            k_here,
            bound
          )
      end
    end

    split(
      elem,
      h,
      embed_head,
      projected,
      type_of,
      step,
      miss,
      k + 1,
      bound
    )
  end

  defp split_enum(name, ctors, hole, embed, cands, type_of, continue, miss, k) do
    var = "e#{k}"
    motive = "(λ (#{var} : #{name}) → #{type_of.(embed.(var))})"
    known = MapSet.new(ctors, &atom_of/1)

    if Enum.all?(cands, &(is_atom(&1.focus) and MapSet.member?(known, &1.focus))) do
      case enum_arms(ctors, cands, embed, continue, miss, k) do
        :open -> :open
        {:ok, arms} -> {:ok, match_arms(hole, motive, arms), k}
      end
    else
      :open
    end
  end

  defp enum_arms(ctors, cands, embed, continue, miss, k) do
    gather(ctors, fn ctor ->
      group = Enum.filter(cands, &(&1.focus == atom_of(ctor)))

      case arm_or_miss(group, ctor, continue, miss, embed, k) do
        :open -> :open
        {:ok, body, _} -> {:ok, "| #{ctor} => #{body}"}
      end
    end)
  end

  defp split_data(name, rows, hole, embed, cands, type_of, continue, miss, k, bound) do
    var = "u#{k}"
    motive = "(λ (#{var} : #{name}) → #{type_of.(embed.(var))})"

    case data_arms(rows, cands, embed, type_of, continue, miss, k, bound) do
      :open -> :open
      {:ok, arms} -> {:ok, match_arms(hole, motive, arms), k}
    end
  end

  defp data_arms(rows, cands, embed, type_of, continue, miss, k, bound) do
    Enum.reduce_while(rows, {:ok, [], cands}, fn row, {:ok, arms, left} ->
      case take_row(row, left) do
        :open ->
          {:halt, :open}

        {:ok, group, rest} ->
          case row_arm(row, group, embed, type_of, continue, miss, k, bound) do
            :open -> {:halt, :open}
            {:ok, arm, _} -> {:cont, {:ok, arms ++ [arm], rest}}
          end
      end
    end)
    |> case do
      :open -> :open
      {:ok, _arms, left} when left != [] -> :open
      {:ok, arms, []} -> {:ok, arms}
    end
  end

  defp take_row(row, cands) do
    atom = atom_of(row.name)
    n = length(row.fields)

    Enum.reduce_while(cands, {:ok, [], []}, fn cand, {:ok, hit, other} ->
      cond do
        not tagged?(cand.focus) ->
          {:halt, :open}

        tag_atom(cand.focus) != atom ->
          {:cont, {:ok, hit, [cand | other]}}

        length(raw_fields(cand.focus)) != n ->
          {:halt, :open}

        true ->
          {:cont, {:ok, [cand | hit], other}}
      end
    end)
    |> case do
      :open -> :open
      {:ok, hit, other} -> {:ok, Enum.reverse(hit), Enum.reverse(other)}
    end
  end

  defp row_arm(row, [], embed, _type_of, _continue, miss, k, _bound) do
    binders = field_binders(row.fields, k)
    local = app_src(row.name, binders)
    {:ok, "| #{pat(row.name, binders)} => #{miss.(embed.(local))}", k}
  end

  defp row_arm(row, group, embed, type_of, continue, miss, k, bound) do
    binders = field_binders(row.fields, k)
    local = app_src(row.name, binders)

    seeded =
      Enum.map(group, fn cand ->
        push(cand, {:fields, raw_fields(cand.focus)})
      end)

    case split_fields(
           row.fields,
           binders,
           local,
           seeded,
           embed,
           type_of,
           continue,
           miss,
           k,
           :arg,
           bound
         ) do
      :open -> :open
      {:ok, inner, k2} -> {:ok, "| #{pat(row.name, binders)} => #{inner}", k2}
    end
  end

  defp field_binders([], _k), do: []
  defp field_binders(fields, k), do: Enum.map(0..(length(fields) - 1), &"f#{k}_#{&1}")

  defp split_fields(
         [],
         _binders,
         local,
         cands,
         _embed,
         _type_of,
         continue,
         _miss,
         k,
         _wrap,
         _bound
       ) do
    case drop_frame(cands, :fields, []) do
      :open -> :open
      {:ok, cands} -> continue.(local, cands, k)
    end
  end

  defp split_fields(
         [field | fields],
         [binder | binders],
         local,
         cands,
         embed,
         type_of,
         continue,
         miss,
         k,
         wrap,
         bound
       ) do
    case take_field(cands) do
      :open ->
        :open

      {:ok, projected} ->
        embed_one = fn src -> embed.(plug(local, binder, src, wrap)) end

        step = fn piece, here, k_here ->
          next_local = plug(local, binder, piece, wrap)

          split_fields(
            fields,
            binders,
            next_local,
            here,
            embed,
            type_of,
            continue,
            miss,
            k_here,
            wrap,
            bound
          )
        end

        split(
          field_schema(field),
          binder,
          embed_one,
          projected,
          type_of,
          step,
          miss,
          k + 1,
          bound
        )
    end
  end

  defp take_field(cands) do
    Enum.reduce_while(cands, {:ok, []}, fn cand, {:ok, acc} ->
      case pop(cand, :fields) do
        {:ok, [value | rest], cand} ->
          {:cont, {:ok, [push(%{cand | focus: value}, {:fields, rest}) | acc]}}

        _ ->
          {:halt, :open}
      end
    end)
    |> case do
      :open -> :open
      {:ok, acc} -> {:ok, Enum.reverse(acc)}
    end
  end

  defp drop_frame(cands, tag, expected) do
    Enum.reduce_while(cands, {:ok, []}, fn cand, {:ok, acc} ->
      case pop(cand, tag) do
        {:ok, ^expected, cand} -> {:cont, {:ok, [cand | acc]}}
        _ -> {:halt, :open}
      end
    end)
    |> case do
      :open -> :open
      {:ok, acc} -> {:ok, Enum.reverse(acc)}
    end
  end

  defp split_prod(left, right, hole, embed, cands, type_of, continue, miss, k, bound) do
    a = "p#{k}_0"
    b = "p#{k}_1"
    local = "(#{a}, #{b})"

    case pair_cands(cands) do
      :open ->
        :open

      {:ok, projected} ->
        embed_left = fn src -> embed.(plug(local, a, src, :raw)) end

        step = fn piece, here, k_here ->
          next_local = plug(local, a, piece, :raw)

          case pop_all(here, :side) do
            :open ->
              :open

            {:ok, pairs} ->
              rights = Enum.map(pairs, fn {value, cand} -> %{cand | focus: value} end)
              embed_right = fn src -> embed.(plug(next_local, b, src, :raw)) end

              cont = fn right_piece, here2, k2 ->
                continue.(plug(next_local, b, right_piece, :raw), here2, k2)
              end

              split(
                right,
                b,
                embed_right,
                rights,
                type_of,
                cont,
                miss,
                k_here,
                bound
              )
          end
        end

        case split(
               left,
               a,
               embed_left,
               projected,
               type_of,
               step,
               miss,
               k + 1,
               bound
             ) do
          :open -> :open
          {:ok, inner, k2} -> {:ok, let_pair(hole, a, b, inner), k2}
        end
    end
  end

  defp pair_cands(cands) do
    Enum.reduce_while(cands, {:ok, []}, fn cand, {:ok, acc} ->
      case cand.focus do
        {left, right} -> {:cont, {:ok, [push(%{cand | focus: left}, {:side, right}) | acc]}}
        _ -> {:halt, :open}
      end
    end)
    |> case do
      :open -> :open
      {:ok, acc} -> {:ok, Enum.reverse(acc)}
    end
  end

  defp arm_or_miss([], src, _continue, miss, embed, k), do: {:ok, miss.(embed.(src)), k}

  defp arm_or_miss(here, src, continue, _miss, _embed, k), do: continue.(src, here, k + 1)

  defp pop_all(cands, tag) do
    Enum.reduce_while(cands, {:ok, []}, fn cand, {:ok, acc} ->
      case pop(cand, tag) do
        {:ok, value, cand} -> {:cont, {:ok, [{value, cand} | acc]}}
        :open -> {:halt, :open}
      end
    end)
    |> case do
      :open -> :open
      {:ok, pairs} -> {:ok, Enum.reverse(pairs)}
    end
  end

  defp pop(%{stack: [{got, value} | rest]} = cand, tag) when got == tag do
    {:ok, value, %{cand | stack: rest}}
  end

  defp pop(_cand, _tag), do: :open

  defp push(%{stack: stack} = cand, frame), do: %{cand | stack: [frame | stack]}

  defp plug(local, binder, piece, :arg), do: subst(local, binder, arg(piece))
  defp plug(local, binder, piece, :raw), do: subst(local, binder, piece)

  defp tagged?(value) when is_atom(value), do: true
  defp tagged?(value) when is_tuple(value) and tuple_size(value) >= 1, do: is_atom(elem(value, 0))
  defp tagged?(_value), do: false

  defp gather(enum, fun) do
    Enum.reduce_while(enum, {:ok, []}, fn item, {:ok, acc} ->
      case fun.(item) do
        {:ok, value} -> {:cont, {:ok, acc ++ [value]}}
        :open -> {:halt, :open}
      end
    end)
  end

  defp match_arms(hole, motive, arms) do
    """
    (match #{hole} motive #{motive}
    #{Enum.join(arms, "\n")})
    """
  end

  defp atom_of(name), do: String.to_atom(Muro.Emit.elixir_atom_name(name))
end

defimpl String.Chars, for: Muro.Synth.Term do
  def to_string(term), do: term.spell
end

defmodule Muro.Mutate do
  @moduledoc """
  Mutation of `run` definitions.

  `report/2` builds type-preserving mutants of each `run` definition, in a
  fixed order, and classifies them with `Muro.Check`. A mutant the checker
  rejects is discarded. One that converts with the original body is
  `equivalent`. One that makes a depending definition fail is `killed`.
  Running out of fuel is `out_of_fuel`, never a kill. Anything else
  survives.

  The manual page is `manual/mutate.md`.
  """

  alias Muro.{Ast, Check, Load, Prelude, Print}

  @default_max 100
  @operators [
    "swap_arms",
    "replace_ctor",
    "replace_var",
    "replace_call",
    "replace_rec_arm",
    "swap_args"
  ]
  @termination [
    "recursive call does not descend on a smaller argument",
    "unguarded recursive call",
    "recursive definition must be applied to its arguments",
    "unfold body must be a pair",
    "ν value calls its own block outside an unfold",
    "not strictly positive",
    "ν body is not a product",
    "bare ν is not a stream"
  ]

  @doc "Default of `--max-mutants-per-def`."
  def default_max_mutants, do: @default_max

  @doc """
  Mutate `path`. Options:

    * `:only` — a name or a list of names. Only those `run` definitions.
    * `:max_mutants_per_def` — cap per definition (default #{@default_max}).
    * `:max_survivors` — `nil` (default) does not limit survivors.
    * `:fuel` — the checker's fuel (default `Muro.Check.default_fuel/0`).
    * `:concurrency` — how many mutants are classified at once.
    * `:root` — passed to `Muro.Load.file/2`.

  `{:ok, report}` when the book checks and survivors are within the limit.
  `{:error, :book, message}` when the book does not check.
  `{:error, :only, message}` when a name is not a `run` definition.
  `{:error, :survivors, report}` when survivors exceed `:max_survivors`.
  The report is the same shape either way.
  """
  def report(path, opts \\ []) when is_binary(path) and is_list(opts) do
    fuel = Keyword.get(opts, :fuel, Check.default_fuel())
    max_m = Keyword.get(opts, :max_mutants_per_def, @default_max)
    max_s = Keyword.get(opts, :max_survivors)
    conc = Keyword.get(opts, :concurrency, System.schedulers_online())
    only = opts |> Keyword.get_values(:only) |> List.flatten()

    with {:ok, user} <- load(path, fuel, opts),
         :ok <- check_only(user, only),
         check = Prelude.for_check(user),
         {:ok, db} <- to_db_book(check) do
      {raw, defs} =
        user
        |> run_defs(only)
        |> Enum.map_reduce([], fn d, infos ->
          {ms, info} = mutants_of(d, check, db, fuel, max_m)
          {ms, infos ++ [info]}
        end)

      judged = judge_all(List.flatten(raw), db, fuel, conc)
      report = pack(path, judged, defs)

      if is_integer(max_s) and report.summary.surviving > max_s do
        {:error, :survivors, report}
      else
        {:ok, report}
      end
    end
  end

  @doc "The text report. A trailing newline closes the last line."
  def render(report) do
    head = [
      "Muro v#{report.version}",
      report.book
      | Enum.map(report.defs, fn d ->
          "#{d.name}: re-checked #{d.rechecked} of #{d.evidence} evidence definitions"
        end)
    ]

    {type_n, term_n} = discard_split(report.mutants)

    counts = [
      "killed: #{report.summary.killed}",
      "surviving: #{report.summary.surviving}",
      "equivalent: #{report.summary.equivalent}",
      "out_of_fuel: #{report.summary.out_of_fuel}",
      "discarded: #{report.summary.discarded} (type #{type_n}, termination #{term_n})"
    ]

    ops =
      Enum.map(@operators, fn op ->
        {t, r} = discard_split(Enum.filter(report.mutants, &(&1.operator == op)))
        "#{op}: discarded type #{t}, termination #{r}"
      end)

    lines = head ++ counts ++ ops ++ Enum.flat_map(report.mutants, &mutant_lines/1)
    Enum.join(lines, "\n") <> "\n"
  end

  @doc "The JSON report, keys in the documented order, ending with a newline."
  def render_json(report) do
    json_object([
      {"book", {:str, report.book}},
      {"version", {:str, report.version}},
      {"summary",
       {:obj,
        [
          {"killed", {:int, report.summary.killed}},
          {"surviving", {:int, report.summary.surviving}},
          {"equivalent", {:int, report.summary.equivalent}},
          {"out_of_fuel", {:int, report.summary.out_of_fuel}},
          {"discarded", {:int, report.summary.discarded}}
        ]}},
      {"mutants", {:arr, Enum.map(report.mutants, &mutant_json/1)}}
    ]) <> "\n"
  end

  # -- book -------------------------------------------------------------------

  defp load(path, fuel, opts) do
    load_opts = [fuel: fuel, root: Keyword.get(opts, :root)]

    case Load.file(path, load_opts) do
      {:ok, book} -> {:ok, book}
      {:error, msg} -> {:error, :book, msg}
    end
  end

  defp to_db_book(check) do
    case Ast.book_to_db(check) do
      {:ok, db} -> {:ok, db}
      {:error, msg} -> {:error, :book, msg}
    end
  end

  defp check_only(_user, []), do: :ok

  defp check_only(user, [name | rest]) do
    case Enum.find(user, &(Map.get(&1, :name) == name)) do
      d when not is_nil(d) ->
        if run_def?(d), do: check_only(user, rest), else: {:error, :only, not_run(name)}

      nil ->
        {:error, :only, not_run(name)}
    end
  end

  defp not_run(name), do: "--only #{name} is not a run definition"

  defp run_defs(user, []), do: Enum.filter(user, &run_def?/1)

  defp run_defs(user, only) do
    wanted = MapSet.new(only)
    Enum.filter(user, fn d -> run_def?(d) and d.name in wanted end)
  end

  defp run_def?(%{mode: :run} = d), do: Map.get(d, :kind, :def) == :def
  defp run_def?(_), do: false

  defp mutants_of(d, check, db, fuel, max_m) do
    index = Enum.find_index(db, &(Map.get(&1, :name) == d.name and Map.get(&1, :mode) == :run))
    deps = dep_records(check, db, d.name)
    ev = evidence_indexes(db)

    ev_deps =
      Enum.filter(deps, fn dep ->
        Enum.at(db, dep.index) |> Map.get(:mode) == :evidence
      end)

    info = %{
      name: d.name,
      rechecked: length(ev_deps),
      evidence: length(ev),
      evidence_names: Enum.map(ev_deps, & &1.name)
    }

    st = %{
      root: d.body,
      path: [],
      env: [],
      result: true,
      under_app: false,
      expected: d.type,
      fuel: fuel,
      db: db,
      named: check,
      earlier: earlier_runs(check, d.name),
      block: mutual_block(db, d.name),
      fallback: line_col(Map.get(d, :loc)),
      file: Map.get(d, :file),
      max: max_m,
      def_name: d.name,
      index: index,
      deps: deps
    }

    {walk(d.body, Map.get(d, :body_span), st, []), info}
  end

  defp earlier_runs(check, def_name) do
    prelude =
      for d <- check, run_def?(d) and not Map.has_key?(d, :file) do
        %{name: d.name, type: d.type}
      end

    user = for d <- check, run_def?(d) and Map.has_key?(d, :file), do: d
    before = Enum.take_while(user, &(&1.name != def_name))
    prelude ++ Enum.map(before, &%{name: &1.name, type: &1.type})
  end

  # Definitions that mention `name`, then definitions that mention those, in
  # book order. `name` itself is not in the list: its mutant is checked apart.
  defp dep_records(check, db, name) do
    mentions = Enum.map(db, &collect_defs/1)
    self = self_index(db, name)
    names = Enum.map(db, &Map.get(&1, :name))
    direct = for {ms, i} <- Enum.with_index(mentions), i != self, name in ms, do: i

    direct
    |> close_deps(mentions, names, MapSet.new(direct), self)
    |> Enum.map(fn i ->
      %{index: i, name: Enum.at(names, i) || "def", location: show_loc(Enum.at(check, i))}
    end)
  end

  defp close_deps(known, mentions, names, seen, self) do
    known_names =
      names
      |> Enum.with_index()
      |> Enum.flat_map(fn {n, i} -> if i in known and n != nil, do: [n], else: [] end)
      |> MapSet.new()

    more =
      for {ms, i} <- Enum.with_index(mentions),
          i != self,
          i not in seen,
          Enum.any?(known_names, &(&1 in ms)),
          do: i

    case more do
      [] -> Enum.sort(known)
      _ -> close_deps(known ++ more, mentions, names, MapSet.union(seen, MapSet.new(more)), self)
    end
  end

  defp self_index(db, name) do
    Enum.find_index(db, &(Map.get(&1, :name) == name and Map.get(&1, :mode) == :run))
  end

  defp evidence_indexes(db) do
    for {d, i} <- Enum.with_index(db), Map.get(d, :mode) == :evidence, do: i
  end

  defp collect_defs(d), do: collect_defs(d, MapSet.new()) |> MapSet.delete(nil)

  defp collect_defs({:def, n}, acc), do: MapSet.put(acc, n)

  defp collect_defs(t, acc) when is_map(t) do
    Enum.reduce(Map.values(t), acc, &collect_defs/2)
  end

  defp collect_defs(t, acc) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.reduce(acc, &collect_defs/2)
  end

  defp collect_defs(t, acc) when is_list(t), do: Enum.reduce(t, acc, &collect_defs/2)
  defp collect_defs(_, acc), do: acc

  defp mutual_block(db, name) do
    runs =
      for %{mode: :run, name: n, body: b} <- db, into: %{} do
        {n, b |> collect_defs() |> MapSet.delete(nil)}
      end

    edges =
      Map.new(runs, fn {n, ms} -> {n, MapSet.intersection(ms, MapSet.new(Map.keys(runs)))} end)

    edges
    |> Map.keys()
    |> Enum.filter(fn j -> reaches?(edges, name, j) and reaches?(edges, j, name) end)
    |> MapSet.new()
  end

  defp reaches?(_edges, src, tgt) when src == tgt, do: true

  defp reaches?(edges, src, tgt), do: reaches?(edges, src, tgt, MapSet.new())

  defp reaches?(edges, cur, tgt, vis) do
    if cur in vis do
      false
    else
      vis = MapSet.put(vis, cur)
      edges |> Map.get(cur, MapSet.new()) |> Enum.any?(&reaches?(edges, &1, tgt, vis))
    end
  end

  # -- walk -------------------------------------------------------------------

  defp walk(_t, _span, %{max: max} = _st, acc) when length(acc) >= max, do: acc

  defp walk({:lam, _q, a, x, b}, span, st, acc) do
    spans = child_spans(span, 2)
    env = [{x, a} | st.env]
    expected = open_pi(st.expected)
    st1 = %{st | env: env, expected: expected, path: st.path ++ [1]}
    walk(b, Enum.at(spans, 1), st1, acc)
  end

  defp walk({:app, _, _} = t, span, st, acc) do
    acc =
      if st.under_app do
        acc
      else
        acc
        |> add_replace_ctor(t, span, st)
        |> add_replace_call(t, span, st)
        |> add_swap_args(t, span, st)
      end

    spans = child_spans(span, 2)
    acc = walk(elem_child(t, 0), Enum.at(spans, 0), app_child(st, 0, true), acc)
    walk(elem_child(t, 1), Enum.at(spans, 1), app_child(st, 1, false), acc)
  end

  defp walk({:su, t} = term, span, st, acc) do
    acc = add_replace_ctor(acc, term, span, st)
    spans = child_spans(span, 1)
    walk(t, Enum.at(spans, 0), plain_child(st, 0, false), acc)
  end

  defp walk(:ze = term, span, st, acc) do
    add_replace_ctor(acc, term, span, st)
  end

  defp walk({:var, _} = t, span, st, acc) do
    acc =
      if st.under_app do
        add_replace_var(acc, t, span, st)
      else
        acc
        |> add_replace_ctor(t, span, st)
        |> add_replace_var(t, span, st)
        |> add_replace_call(t, span, st)
      end

    acc
  end

  defp walk({:mnat, e, x, p, z, y, s} = t, span, st, acc) do
    acc =
      acc
      |> add_swap_arms(t, span, st)
      |> add_replace_rec(t, span, st)

    spans = child_spans(span, 4)
    acc = walk(e, Enum.at(spans, 0), plain_child(st, 0, false), acc)
    acc = walk(z, Enum.at(spans, 2), arm_child(st, 2, motive_type(p, x, :ze)), acc)
    env = [{y, :nat} | st.env]

    walk(
      s,
      Enum.at(spans, 3),
      arm_child(%{st | env: env}, 3, motive_type(p, x, {:su, {:var, y}})),
      acc
    )
  end

  defp walk({:mdata, e, x, p, bs} = t, span, st, acc) do
    acc =
      acc
      |> add_swap_arms(t, span, st)
      |> add_replace_rec(t, span, st)

    spans = child_spans(span, 2 + length(bs))
    acc = walk(e, Enum.at(spans, 0), plain_child(st, 0, false), acc)
    scrut = scrut_type(e, st.env)

    Enum.with_index(bs)
    |> Enum.reduce(acc, fn {{cname, binders, body}, i}, acc ->
      ctor = ctor_term(cname, binders)
      env = arm_env(st, cname, binders, scrut)
      expected = motive_type(p, x, ctor)
      st1 = arm_child(%{st | env: env}, i + 2, expected)
      walk(body, Enum.at(spans, i + 2), st1, acc)
    end)
  end

  defp walk({:matom, e, x, p, bs} = t, span, st, acc) do
    acc =
      acc
      |> add_swap_arms(t, span, st)
      |> add_replace_rec(t, span, st)

    spans = child_spans(span, 2 + length(bs))
    acc = walk(e, Enum.at(spans, 0), plain_child(st, 0, false), acc)

    Enum.with_index(bs)
    |> Enum.reduce(acc, fn {{name, body}, i}, acc ->
      expected = motive_type(p, x, {:atom, name})
      walk(body, Enum.at(spans, i + 2), arm_child(st, i + 2, expected), acc)
    end)
  end

  defp walk({:memp, e, _, _}, span, st, acc) do
    spans = child_spans(span, 2)
    walk(e, Enum.at(spans, 0), plain_child(st, 0, false), acc)
  end

  defp walk({:rwt, e, _, _, t}, span, st, acc) do
    spans = child_spans(span, 3)
    acc = walk(e, Enum.at(spans, 0), plain_child(st, 0, false), acc)
    walk(t, Enum.at(spans, 2), %{plain_child(st, 2, false) | result: st.result}, acc)
  end

  defp walk({:letp, e, a, b, t}, span, st, acc) do
    spans = child_spans(span, 2)
    acc = walk(e, Enum.at(spans, 0), plain_child(st, 0, false), acc)
    env = [{b, :unknown}, {a, :unknown} | st.env]

    walk(
      t,
      Enum.at(spans, 1),
      %{plain_child(%{st | env: env}, 1, false) | result: st.result},
      acc
    )
  end

  defp walk({:idt, _, a, b}, span, st, acc) do
    spans = child_spans(span, 3)
    acc = walk(a, Enum.at(spans, 1), plain_child(st, 1, false), acc)
    walk(b, Enum.at(spans, 2), plain_child(st, 2, false), acc)
  end

  defp walk({:pi, _, _, _, _}, _span, _st, acc), do: acc
  defp walk({:prod, _, _}, _span, _st, acc), do: acc
  defp walk({:stream, _}, _span, _st, acc), do: acc

  defp walk(t, span, st, acc) do
    kids = Ast.children(t)
    spans = child_spans(span, length(kids))

    Enum.with_index(kids)
    |> Enum.reduce(acc, fn {k, i}, acc ->
      walk(k, Enum.at(spans, i), plain_child(st, i, false), acc)
    end)
  end

  defp elem_child({:app, f, _}, 0), do: f
  defp elem_child({:app, _, a}, 1), do: a

  defp app_child(st, i, under) do
    %{st | path: st.path ++ [i], result: false, under_app: under}
  end

  defp plain_child(st, i, _result?) do
    %{st | path: st.path ++ [i], result: false, under_app: false}
  end

  defp arm_child(st, i, expected) do
    %{st | path: st.path ++ [i], result: true, under_app: false, expected: expected}
  end

  defp open_pi({:pi, _, _, _, b}), do: b
  defp open_pi(_), do: :unknown

  defp child_spans({_loc, kids}, n) when length(kids) == n, do: kids
  defp child_spans(_, n), do: List.duplicate(nil, n)

  # -- operators --------------------------------------------------------------

  defp add_swap_arms(acc, {:mnat, _e, x, p, z, y, s} = t, span, st) do
    swap_pairs(acc, t, span, st, x, p, [{:ze, z}, {{:su, {:var, y}}, s}])
  end

  defp add_swap_arms(acc, {:mdata, _, x, p, bs} = t, span, st) do
    arms = Enum.map(bs, fn {c, binders, body} -> {ctor_term(c, binders), body} end)
    swap_pairs(acc, t, span, st, x, p, arms)
  end

  defp add_swap_arms(acc, {:matom, _, x, p, bs} = t, span, st) do
    arms = Enum.map(bs, fn {name, body} -> {{:atom, name}, body} end)
    swap_pairs(acc, t, span, st, x, p, arms)
  end

  # Bodies move; constructor names and binders stay. A pair is emitted when
  # the motive, instantiated at each constructor, converts. Fuel on that
  # comparison skips the pair.
  defp swap_pairs(acc, term, span, st, x, p, arms) do
    Enum.reduce(pairs(length(arms)), acc, fn {i, j}, acc ->
      {ci, bi} = Enum.at(arms, i)
      {cj, bj} = Enum.at(arms, j)

      if bi == bj do
        acc
      else
        case motive_same?(p, x, ci, cj, st) do
          :yes ->
            swapped = swap_term(term, i, j)
            push(acc, st, span, "swap_arms", term, swapped, replace_at(st.root, st.path, swapped))

          _ ->
            acc
        end
      end
    end)
  end

  defp motive_same?(p, x, ci, cj, st) do
    types_conv?(subst_name(p, x, ci), subst_name(p, x, cj), st)
  end

  defp pairs(n) when n < 2, do: []

  defp pairs(n) do
    for i <- 0..(n - 2), j <- (i + 1)..(n - 1), do: {i, j}
  end

  defp swap_term({:mnat, e, x, p, z, y, s}, 0, 1), do: {:mnat, e, x, p, s, y, z}

  defp swap_term({:mdata, e, x, p, bs}, i, j) do
    {:mdata, e, x, p, swap_branch_bodies(bs, i, j)}
  end

  defp swap_term({:matom, e, x, p, bs}, i, j) do
    {:matom, e, x, p, swap_branch_bodies(bs, i, j)}
  end

  defp swap_branch_bodies(bs, i, j) do
    bi = Enum.at(bs, i)
    bj = Enum.at(bs, j)

    bs
    |> List.replace_at(i, put_body(bi, body_of(bj)))
    |> List.replace_at(j, put_body(bj, body_of(bi)))
  end

  defp body_of({_, body}), do: body
  defp body_of({_, _, body}), do: body
  defp put_body({n, _}, body), do: {n, body}
  defp put_body({n, binders, _}, body), do: {n, binders, body}

  defp add_replace_rec(acc, {:mnat, _, _, _, z, _, s} = t, span, st) do
    rec_on(acc, t, span, st, [z, s])
  end

  defp add_replace_rec(acc, {:mdata, _, _, _, bs} = t, span, st) do
    rec_on(acc, t, span, st, Enum.map(bs, fn {_, _, body} -> body end))
  end

  defp add_replace_rec(acc, {:matom, _, _, _, bs} = t, span, st) do
    rec_on(acc, t, span, st, Enum.map(bs, fn {_, body} -> body end))
  end

  defp rec_on(acc, term, span, st, bodies) do
    base = Enum.find_index(bodies, fn b -> not mentions_any?(b, st.block) end)

    if base == nil do
      acc
    else
      base_body = Enum.at(bodies, base)

      Enum.with_index(bodies)
      |> Enum.reduce(acc, fn {body, i}, acc ->
        if i != base and mentions_any?(body, st.block) and body != base_body do
          swapped = put_arm(term, i, base_body)

          push(
            acc,
            st,
            span,
            "replace_rec_arm",
            term,
            swapped,
            replace_at(st.root, st.path, swapped)
          )
        else
          acc
        end
      end)
    end
  end

  defp put_arm({:mnat, e, x, p, _z, y, s}, 0, body), do: {:mnat, e, x, p, body, y, s}
  defp put_arm({:mnat, e, x, p, z, y, _}, 1, body), do: {:mnat, e, x, p, z, y, body}

  defp put_arm({:mdata, e, x, p, bs}, i, body) do
    {:mdata, e, x, p, List.update_at(bs, i, fn {c, binders, _} -> {c, binders, body} end)}
  end

  defp put_arm({:matom, e, x, p, bs}, i, body) do
    {:matom, e, x, p, List.update_at(bs, i, fn {n, _} -> {n, body} end)}
  end

  defp add_replace_ctor(acc, term, span, st) do
    if st.result and ctor_form?(term, st) do
      term
      |> other_ctors(st)
      |> Enum.reduce(acc, fn built, acc ->
        if built == term do
          acc
        else
          push(acc, st, span, "replace_ctor", term, built, replace_at(st.root, st.path, built))
        end
      end)
    else
      acc
    end
  end

  defp ctor_form?(:ze, _st), do: true
  defp ctor_form?({:su, _}, _st), do: true

  defp ctor_form?(term, st) do
    {head, _} = named_spine(term)

    case head do
      {:var, n} -> ctor?(st.named, n) and not local?(st.env, n)
      _ -> false
    end
  end

  defp other_ctors(:ze, st), do: suc_fills(st)
  defp other_ctors({:su, _}, _st), do: [:ze]

  defp other_ctors(term, st) do
    {{:var, name}, _} = named_spine(term)

    case ctor_entry(st.named, name) do
      nil ->
        []

      {data, _} ->
        case unify_expected(data, term, st) do
          {:ok, subst} ->
            data.ctors
            |> Enum.reject(&(&1.name == name))
            |> Enum.flat_map(&fills_for(&1, subst, st))

          :no ->
            []
        end
    end
  end

  defp suc_fills(st) do
    for filler <- fillers(:nat, st), do: {:su, filler}
  end

  defp fills_for(ctor, subst, st) do
    {doms, _} = peel_pi(ctor.type)
    doms = Enum.map(doms, &apply_subst(&1, subst))

    case fill_product(doms, st) do
      [] ->
        []

      combos ->
        Enum.map(combos, &apply_ctor(ctor.name, &1))
    end
  end

  defp fill_product([], _st), do: [[]]

  defp fill_product([ty | rest], st) do
    fs = fillers(ty, st)

    if fs == [] do
      []
    else
      for f <- fs, tail <- fill_product(rest, st), do: [f | tail]
    end
  end

  defp apply_ctor(name, []), do: {:var, name}

  defp apply_ctor(name, [a | as]),
    do: Enum.reduce(as, {:app, {:var, name}, a}, fn x, f -> {:app, f, x} end)

  defp add_replace_var(acc, {:var, name} = term, span, st) do
    case lookup_ty(st.env, name) do
      :unknown ->
        acc

      nil ->
        acc

      ty ->
        alts = var_alts(name, ty, st)

        Enum.reduce(alts, acc, fn alt, acc ->
          push(acc, st, span, "replace_var", term, alt, replace_at(st.root, st.path, alt))
        end)
    end
  end

  defp var_alts(name, ty, st) do
    vars =
      st.env
      |> Enum.reverse()
      |> Enum.flat_map(fn
        {^name, _} ->
          []

        {_n, :unknown} ->
          []

        {n, nty} ->
          if types_conv?(ty, nty, st) == :yes, do: [{:var, n}], else: []
      end)

    vars ++ Enum.filter(nullaries(ty, st), &(&1 != {:var, name}))
  end

  defp add_replace_call(acc, term, span, st) do
    {head, args} = named_spine(term)

    case call_head(head, st) do
      {:def, name} ->
        case declared_type(st.named, name) do
          nil ->
            acc

          ty ->
            st.earlier
            |> Enum.reduce(acc, fn g, acc ->
              if g.name != name and types_conv?(ty, g.type, %{st | env: []}) == :yes do
                built = apply_ctor(g.name, args)

                push(
                  acc,
                  st,
                  span,
                  "replace_call",
                  term,
                  built,
                  replace_at(st.root, st.path, built)
                )
              else
                acc
              end
            end)
        end

      _ ->
        acc
    end
  end

  defp add_swap_args(acc, term, span, st) do
    {head, args} = named_spine(term)

    if length(args) < 2 or call_head(head, st) in [:ctor, :other] do
      acc
    else
      case head_type(head, st) do
        nil ->
          acc

        :fuel ->
          acc

        ty ->
          Enum.reduce(pairs(length(args)), acc, fn {i, j}, acc ->
            swap_one(acc, term, span, st, args, ty, i, j)
          end)
      end
    end
  end

  defp swap_one(acc, term, span, st, args, ty, i, j) do
    ai = Enum.at(args, i)
    aj = Enum.at(args, j)

    if ai == aj do
      acc
    else
      case {pure_domain(ty, i, st), pure_domain(ty, j, st)} do
        {{:ok, di}, {:ok, dj}} ->
          if Check.conv(st.db, di, dj, st.fuel) == :ok do
            swapped = apply_head(elem(named_spine(term), 0), swap_at(args, i, j))
            push(acc, st, span, "swap_args", term, swapped, replace_at(st.root, st.path, swapped))
          else
            acc
          end

        _ ->
          acc
      end
    end
  end

  defp swap_at(args, i, j) do
    ai = Enum.at(args, i)
    aj = Enum.at(args, j)

    args
    |> List.replace_at(i, aj)
    |> List.replace_at(j, ai)
  end

  defp apply_head(head, []), do: head

  defp apply_head(head, [a | as]),
    do: Enum.reduce(as, {:app, head, a}, fn x, f -> {:app, f, x} end)

  defp call_head({:var, n}, st) do
    cond do
      local?(st.env, n) -> {:local, n}
      ctor?(st.named, n) -> :ctor
      true -> {:def, n}
    end
  end

  defp call_head(_, _), do: :other

  defp head_type(head, st) do
    case call_head(head, st) do
      {:local, n} ->
        case lookup_ty(st.env, n) do
          nil -> nil
          :unknown -> nil
          ty -> ty
        end

      {:def, n} ->
        declared_type(st.named, n)

      _ ->
        nil
    end
  end

  # The domain of argument `index`, shifted back to the call's context.
  # A domain that mentions an earlier argument is not swappable.
  defp pure_domain(named_ty, index, st) do
    with {:ok, dbty} <- Ast.to_db(named_ty, env_names(st.env)),
         {:ok, dom} <- peel_domain(dbty, index, st.db, st.fuel) do
      if depends_on_earlier?(dom, index), do: :no, else: {:ok, shift_down(dom, index)}
    else
      {:error, msg} -> if Check.out_of_fuel?(msg), do: :fuel, else: :no
      :no -> :no
      _ -> :no
    end
  end

  defp depends_on_earlier?(_term, 0), do: false

  defp depends_on_earlier?(term, n) when n > 0 do
    try do
      Muro.Subst.ren(fn i -> if i < n, do: throw(:hit), else: i end, term)
      false
    catch
      :hit -> true
    end
  end

  defp shift_down(term, 0), do: term

  defp shift_down(term, n) when n > 0 do
    Muro.Subst.ren(fn i -> i - n end, term)
  end

  defp peel_domain(ty, 0, book, fuel) do
    case Check.reduce(book, ty, fuel) do
      {:ok, {:pi, _, a, _, _}} -> {:ok, a}
      {:ok, _} -> :no
      {:error, _} = err -> err
    end
  end

  defp peel_domain(ty, n, book, fuel) when n > 0 do
    case Check.reduce(book, ty, fuel) do
      {:ok, {:pi, _, _, _, b}} -> peel_domain(b, n - 1, book, fuel)
      {:ok, _} -> :no
      {:error, _} = err -> err
    end
  end

  # -- types, ctors, fillers --------------------------------------------------

  defp fillers(ty, st) do
    vars =
      st.env
      |> Enum.reverse()
      |> Enum.flat_map(fn
        {_n, :unknown} -> []
        {n, nty} -> if types_conv?(ty, nty, st) == :yes, do: [{:var, n}], else: []
      end)

    vars ++ nullaries(ty, st)
  end

  defp nullaries(ty, st) do
    base =
      []
      |> add_if(types_conv?(ty, :nat, st) == :yes, :ze)
      |> add_if(types_conv?(ty, :unit, st) == :yes, :one)

    ctors =
      for %{kind: :data, ctors: cs} = data <- st.named,
          c <- cs,
          {doms, result} = peel_pi(c.type),
          doms == [],
          types_conv?(ty, result, st) == :yes do
        _ = data
        {:var, c.name}
      end

    base ++ ctors
  end

  defp add_if(list, true, item), do: list ++ [item]
  defp add_if(list, false, _), do: list

  defp types_conv?(a, b, st) do
    with {:ok, da} <- Ast.to_db(a, env_names(st.env)),
         {:ok, db} <- Ast.to_db(b, env_names(st.env)) do
      case Check.conv(st.db, da, db, st.fuel) do
        :ok -> :yes
        {:error, msg} -> if Check.out_of_fuel?(msg), do: :fuel, else: :no
      end
    else
      _ -> :no
    end
  end

  defp unify_expected(data, term, st) do
    if st.expected in [:unknown, nil] do
      :no
    else
      {_, result} = peel_pi(ctor_type_of(term, data))
      unify_app(result, st.expected, %{})
    end
  end

  defp ctor_type_of(term, data) do
    {:var, name} = elem(named_spine(term), 0)
    Enum.find(data.ctors, &(&1.name == name)).type
  end

  defp unify_app(a, b, subst) do
    {h1, args1} = named_spine(a)
    {h2, args2} = named_spine(b)

    if h1 == h2 and length(args1) == length(args2) do
      Enum.reduce_while(Enum.zip(args1, args2), subst, fn {x, y}, subst ->
        case bind_arg(x, y, subst) do
          {:ok, subst} -> {:cont, subst}
          :no -> {:halt, :no}
        end
      end)
      |> case do
        :no -> :no
        subst -> {:ok, subst}
      end
    else
      :no
    end
  end

  defp bind_arg({:var, n}, y, subst) do
    case Map.fetch(subst, n) do
      {:ok, ^y} -> {:ok, subst}
      {:ok, _} -> :no
      :error -> {:ok, Map.put(subst, n, y)}
    end
  end

  defp bind_arg(x, y, subst) when x == y, do: {:ok, subst}

  defp bind_arg(x, y, subst) do
    {h1, a1} = named_spine(x)
    {h2, a2} = named_spine(y)

    if h1 == h2 and a1 != [] and length(a1) == length(a2) do
      unify_app(x, y, subst)
    else
      :no
    end
  end

  defp ctor_field_types(book, cname, scrut) do
    case ctor_entry(book, cname) do
      nil ->
        :no

      {_data, ctor} ->
        if scrut in [:unknown, nil] do
          :no
        else
          {doms, result} = peel_pi(ctor.type)

          case unify_app(result, scrut, %{}) do
            {:ok, subst} -> {:ok, Enum.map(doms, &apply_subst(&1, subst))}
            :no -> :no
          end
        end
    end
  end

  defp arm_env(st, cname, binders, scrut) do
    types =
      case ctor_field_types(st.named, cname, scrut) do
        {:ok, ts} when length(ts) == length(binders) -> ts
        _ -> List.duplicate(:unknown, length(binders))
      end

    extra = binders |> Enum.zip(types) |> Enum.reverse()
    extra ++ st.env
  end

  defp peel_pi(t), do: peel_pi(t, [])
  defp peel_pi({:pi, _, a, _, b}, acc), do: peel_pi(b, acc ++ [a])
  defp peel_pi(t, acc), do: {acc, t}

  defp apply_subst(t, subst), do: apply_subst(t, subst, MapSet.new())

  defp apply_subst({:var, n}, subst, bound) do
    if n in bound, do: {:var, n}, else: Map.get(subst, n, {:var, n})
  end

  defp apply_subst({:lam, q, a, x, b}, subst, bound) do
    {:lam, q, apply_subst(a, subst, bound), x, apply_subst(b, subst, MapSet.put(bound, x))}
  end

  defp apply_subst({:pi, q, a, x, b}, subst, bound) do
    {:pi, q, apply_subst(a, subst, bound), x, apply_subst(b, subst, MapSet.put(bound, x))}
  end

  defp apply_subst(t, subst, bound) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.map(&apply_subst(&1, subst, bound)) |> List.to_tuple()
  end

  defp apply_subst(t, subst, bound) when is_list(t),
    do: Enum.map(t, &apply_subst(&1, subst, bound))

  defp apply_subst(t, _, _), do: t

  defp motive_type(p, x, arg), do: subst_name(p, x, arg)

  defp subst_name(t, name, rep), do: subst_name(t, name, rep, MapSet.new())

  defp subst_name({:var, n}, n, rep, bound) do
    if n in bound, do: {:var, n}, else: rep
  end

  defp subst_name({:lam, q, a, x, b}, name, rep, bound) do
    {:lam, q, subst_name(a, name, rep, bound), x, subst_name(b, name, rep, MapSet.put(bound, x))}
  end

  defp subst_name({:pi, q, a, x, b}, name, rep, bound) do
    {:pi, q, subst_name(a, name, rep, bound), x, subst_name(b, name, rep, MapSet.put(bound, x))}
  end

  defp subst_name({:mnat, e, x, p, z, y, s}, name, rep, bound) do
    {:mnat, subst_name(e, name, rep, bound), x, subst_name(p, name, rep, MapSet.put(bound, x)),
     subst_name(z, name, rep, bound), y, subst_name(s, name, rep, MapSet.put(bound, y))}
  end

  defp subst_name(t, name, rep, bound) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.map(&subst_name(&1, name, rep, bound)) |> List.to_tuple()
  end

  defp subst_name(t, name, rep, bound) when is_list(t) do
    Enum.map(t, &subst_name(&1, name, rep, bound))
  end

  defp subst_name(t, _, _, _), do: t

  defp mentions_any?(term, names), do: mentions_any?(term, names, MapSet.new())

  defp mentions_any?({:var, n}, names, bound), do: n in names and n not in bound

  defp mentions_any?({:lam, _, a, x, b}, names, bound) do
    mentions_any?(a, names, bound) or mentions_any?(b, names, MapSet.put(bound, x))
  end

  defp mentions_any?({:pi, _, a, x, b}, names, bound) do
    mentions_any?(a, names, bound) or mentions_any?(b, names, MapSet.put(bound, x))
  end

  defp mentions_any?({:mnat, e, x, p, z, y, s}, names, bound) do
    mentions_any?(e, names, bound) or mentions_any?(p, names, MapSet.put(bound, x)) or
      mentions_any?(z, names, bound) or mentions_any?(s, names, MapSet.put(bound, y))
  end

  defp mentions_any?({:mdata, e, x, p, bs}, names, bound) do
    mentions_any?(e, names, bound) or mentions_any?(p, names, MapSet.put(bound, x)) or
      Enum.any?(bs, fn {_, binders, body} ->
        bound = Enum.reduce(binders, bound, &MapSet.put(&2, &1))
        mentions_any?(body, names, bound)
      end)
  end

  defp mentions_any?({:matom, e, x, p, bs}, names, bound) do
    mentions_any?(e, names, bound) or mentions_any?(p, names, MapSet.put(bound, x)) or
      Enum.any?(bs, fn {_, body} -> mentions_any?(body, names, bound) end)
  end

  defp mentions_any?(t, names, bound) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.any?(&mentions_any?(&1, names, bound))
  end

  defp mentions_any?(t, names, bound) when is_list(t) do
    Enum.any?(t, &mentions_any?(&1, names, bound))
  end

  defp mentions_any?(_, _, _), do: false

  defp local?(env, n), do: Enum.any?(env, fn {name, _} -> name == n end)

  defp lookup_ty(env, n) do
    case Enum.find(env, fn {name, _} -> name == n end) do
      {_, ty} -> ty
      nil -> nil
    end
  end

  defp declared_type(book, name) do
    case Enum.find(book, &(Map.get(&1, :name) == name and run_def?(&1))) do
      nil -> nil
      d -> d.type
    end
  end

  defp ctor?(book, name), do: ctor_entry(book, name) != nil

  defp ctor_entry(book, name) do
    Enum.find_value(book, fn
      %{kind: :data, ctors: ctors} = data ->
        case Enum.find(ctors, &(&1.name == name)) do
          nil -> nil
          c -> {data, c}
        end

      _ ->
        nil
    end)
  end

  defp ctor_term(name, []), do: {:var, name}

  defp ctor_term(name, binders) do
    Enum.reduce(binders, {:var, name}, fn b, f -> {:app, f, {:var, b}} end)
  end

  defp scrut_type({:var, n}, env) do
    case lookup_ty(env, n) do
      nil -> :unknown
      ty -> ty
    end
  end

  defp scrut_type(:ze, _), do: :nat
  defp scrut_type({:su, _}, _), do: :nat
  defp scrut_type(_, _), do: :unknown

  defp named_spine(t), do: named_spine(t, [])
  defp named_spine({:app, f, a}, acc), do: named_spine(f, [a | acc])
  defp named_spine(h, acc), do: {h, acc}

  defp env_names(env), do: Enum.map(env, &elem(&1, 0))

  # -- emit a candidate -------------------------------------------------------

  defp push(acc, %{max: max} = _st, _span, _op, _before, _after, _body) when length(acc) >= max do
    acc
  end

  defp push(acc, st, span, op, before, later, new_body) do
    if before == later or new_body == st.root do
      acc
    else
      db_body =
        case Ast.to_db(new_body) do
          {:ok, t} -> t
          _ -> :error
        end

      loc = loc_text(st.file, focus_loc(span, st.fallback))

      mutant = %{
        id: "#{st.def_name}##{length(acc) + 1}",
        def: st.def_name,
        operator: op,
        location: loc,
        before: show_term(before, st.env),
        after: show_term(later, st.env),
        db_body: db_body,
        index: st.index,
        deps: st.deps,
        discard: nil,
        killed_by: []
      }

      acc ++ [mutant]
    end
  end

  defp focus_loc({loc, _}, _fallback) when is_tuple(loc), do: line_col(loc)
  defp focus_loc(_, fallback), do: fallback

  defp show_term(named, env) do
    names = env_names(env)

    case Ast.to_db(named, names) do
      {:ok, db} -> db |> Print.term(names) |> String.replace(~r/[\r\n]+/, " ")
      _ -> "?"
    end
  end

  defp replace_at(_term, [], new), do: new

  defp replace_at(term, [i | is], new) do
    kids = Ast.children(term)
    kids = List.replace_at(kids, i, replace_at(Enum.at(kids, i), is, new))
    rebuild(term, kids)
  end

  defp rebuild({:su, _}, [a]), do: {:su, a}
  defp rebuild({:stream, _}, [a]), do: {:stream, a}
  defp rebuild({:always, _, _, _}, [a, p, s]), do: {:always, a, p, s}
  defp rebuild({:bisim, _, _}, [a, b]), do: {:bisim, a, b}
  defp rebuild({:unf, _, _}, [a, b]), do: {:unf, a, b}
  defp rebuild({:ucons, _}, [a]), do: {:ucons, a}
  defp rebuild({:pi, q, _, x, _}, [a, b]), do: {:pi, q, a, x, b}
  defp rebuild({:lam, q, _, x, _}, [a, b]), do: {:lam, q, a, x, b}
  defp rebuild({:app, _, _}, [a, b]), do: {:app, a, b}
  defp rebuild({:prod, _, _}, [a, b]), do: {:prod, a, b}
  defp rebuild({:pair, _, _}, [a, b]), do: {:pair, a, b}
  defp rebuild({:letp, _, x, y, _}, [e, b]), do: {:letp, e, x, y, b}
  defp rebuild({:idt, _, _, _}, [ty, a, b]), do: {:idt, ty, a, b}
  defp rebuild({:rwt, _, x, _, _}, [e, p, t]), do: {:rwt, e, x, p, t}
  defp rebuild({:ann, _, _}, [e, a]), do: {:ann, e, a}
  defp rebuild({:mnat, _, x, _, _, y, _}, [e, p, z, s]), do: {:mnat, e, x, p, z, y, s}
  defp rebuild({:memp, _, x, _}, [e, p]), do: {:memp, e, x, p}
  defp rebuild({:munit, _, x, _, _}, [e, p, u]), do: {:munit, e, x, p, u}

  defp rebuild({:matom, _, x, _, bs}, kids) do
    [e, p | bodies] = kids
    bs = Enum.zip(bs, bodies) |> Enum.map(fn {{n, _}, b} -> {n, b} end)
    {:matom, e, x, p, bs}
  end

  defp rebuild({:mdata, _, x, _, bs}, kids) do
    [e, p | bodies] = kids
    bs = Enum.zip(bs, bodies) |> Enum.map(fn {{c, bind, _}, b} -> {c, bind, b} end)
    {:mdata, e, x, p, bs}
  end

  defp rebuild({:tensor, _, _}, [a, b]), do: {:tensor, a, b}
  defp rebuild({:addi, _, _}, [a, b]), do: {:addi, a, b}
  defp rebuild({:muli, _, _}, [a, b]), do: {:muli, a, b}
  defp rebuild({:addt, _, _}, [a, b]), do: {:addt, a, b}
  defp rebuild({:toi64, _}, [a]), do: {:toi64, a}
  defp rebuild({:packi, _, _}, [a, b]), do: {:packi, a, b}
  defp rebuild({:nu, x, _}, [f]), do: {:nu, x, f}

  # -- classify ---------------------------------------------------------------

  defp judge_all(mutants, db, fuel, conc) do
    mutants
    |> Task.async_stream(&classify(&1, db, fuel),
      ordered: true,
      timeout: :infinity,
      max_concurrency: max(conc, 1)
    )
    |> Enum.map(fn
      {:ok, m} -> m
      {:exit, reason} -> exit(reason)
    end)
  end

  defp classify(%{db_body: :error} = m, _db, _fuel) do
    finish(m, "discarded", :type, [])
  end

  defp classify(m, db, fuel) do
    orig = Enum.at(db, m.index)
    mutant_def = %{orig | body: m.db_body}
    book = List.replace_at(db, m.index, mutant_def)

    case Check.check_def(book, mutant_def, fuel) do
      {:error, msg} ->
        cond do
          Check.out_of_fuel?(msg) -> finish(m, "out_of_fuel", nil, [])
          termination?(msg) -> finish(m, "discarded", :termination, [])
          true -> finish(m, "discarded", :type, [])
        end

      :ok ->
        if equivalent?(db, orig.body, m.db_body, fuel) do
          finish(m, "equivalent", nil, [])
        else
          recheck(m, book, fuel)
        end
    end
  end

  defp recheck(m, book, fuel) do
    fails =
      Enum.flat_map(m.deps, fn dep ->
        d = Enum.at(book, dep.index)

        case Check.check_def(book, d, fuel) do
          :ok -> []
          {:error, msg} -> [{dep, msg}]
        end
      end)

    real = Enum.reject(fails, fn {_, msg} -> Check.out_of_fuel?(msg) end)

    cond do
      real != [] ->
        killed = Enum.map(real, fn {dep, _} -> %{name: dep.name, location: dep.location} end)
        finish(m, "killed", nil, killed)

      fails != [] ->
        finish(m, "out_of_fuel", nil, [])

      true ->
        finish(m, "surviving", nil, [])
    end
  end

  # Stock conversion treats match branches by constructor position. When that
  # fails for a reason other than fuel, pair branches by constructor and ask
  # conversion again on the bodies. Fuel on the first comparison is not
  # equivalence.
  defp equivalent?(book, orig, mut, fuel) do
    case Check.conv(book, orig, mut, fuel) do
      :ok ->
        true

      {:error, msg} ->
        if Check.out_of_fuel?(msg), do: false, else: perm_eq?(book, orig, mut, fuel)
    end
  end

  defp perm_eq?(book, a, b, fuel) do
    case Check.conv(book, a, b, fuel) do
      :ok -> true
      {:error, msg} -> if Check.out_of_fuel?(msg), do: false, else: perm_struct?(book, a, b, fuel)
    end
  end

  defp perm_struct?(book, {:su, a}, {:su, b}, fuel), do: perm_eq?(book, a, b, fuel)

  defp perm_struct?(book, {:lam, q, a, _, t}, {:lam, q, a1, _, t1}, fuel) do
    perm_eq?(book, a, a1, fuel) and perm_eq?(book, t, t1, fuel)
  end

  defp perm_struct?(book, {:pi, q, a, _, t}, {:pi, q, a1, _, t1}, fuel) do
    perm_eq?(book, a, a1, fuel) and perm_eq?(book, t, t1, fuel)
  end

  defp perm_struct?(book, {:app, f, a}, {:app, g, b}, fuel) do
    perm_eq?(book, f, g, fuel) and perm_eq?(book, a, b, fuel)
  end

  defp perm_struct?(book, {:mnat, e, p, z, s}, {:mnat, e1, p1, z1, s1}, fuel) do
    perm_eq?(book, e, e1, fuel) and perm_eq?(book, p, p1, fuel) and perm_eq?(book, z, z1, fuel) and
      perm_eq?(book, s, s1, fuel)
  end

  defp perm_struct?(book, {:mdata, e, p, bs}, {:mdata, e1, p1, bs1}, fuel) do
    perm_eq?(book, e, e1, fuel) and perm_eq?(book, p, p1, fuel) and
      perm_branches?(book, bs, bs1, fuel)
  end

  defp perm_struct?(book, {:matom, e, p, bs}, {:matom, e1, p1, bs1}, fuel) do
    perm_eq?(book, e, e1, fuel) and perm_eq?(book, p, p1, fuel) and
      perm_atom_branches?(book, bs, bs1, fuel)
  end

  defp perm_struct?(book, {:pair, a, b}, {:pair, a1, b1}, fuel) do
    perm_eq?(book, a, a1, fuel) and perm_eq?(book, b, b1, fuel)
  end

  defp perm_struct?(_, _, _, _), do: false

  defp perm_branches?(book, bs, bs1, fuel) do
    length(bs) == length(bs1) and
      Enum.all?(bs, fn {n, ar, b} ->
        case Enum.find(bs1, fn {n1, ar1, _} -> n1 == n and ar1 == ar end) do
          {_, _, b1} -> perm_eq?(book, b, b1, fuel)
          nil -> false
        end
      end)
  end

  defp perm_atom_branches?(book, bs, bs1, fuel) do
    length(bs) == length(bs1) and
      Enum.all?(bs, fn {n, b} ->
        case Enum.find(bs1, fn {n1, _} -> n1 == n end) do
          {_, b1} -> perm_eq?(book, b, b1, fuel)
          nil -> false
        end
      end)
  end

  defp termination?(msg), do: Enum.any?(@termination, &String.contains?(msg, &1))

  defp finish(m, outcome, discard, killed_by) do
    m
    |> Map.put(:outcome, outcome)
    |> Map.put(:discard, discard)
    |> Map.put(:killed_by, killed_by)
    |> Map.drop([:db_body, :index, :deps])
  end

  # -- report -----------------------------------------------------------------

  defp pack(path, mutants, defs) do
    summary = %{
      killed: count(mutants, "killed"),
      surviving: count(mutants, "surviving"),
      equivalent: count(mutants, "equivalent"),
      out_of_fuel: count(mutants, "out_of_fuel"),
      discarded: count(mutants, "discarded")
    }

    %{book: path, version: app_version(), summary: summary, defs: defs, mutants: mutants}
  end

  defp count(mutants, outcome), do: Enum.count(mutants, &(&1.outcome == outcome))

  defp discard_split(mutants) do
    type_n = Enum.count(mutants, &(&1.outcome == "discarded" and &1.discard == :type))
    term_n = Enum.count(mutants, &(&1.outcome == "discarded" and &1.discard == :termination))
    {type_n, term_n}
  end

  defp mutant_lines(m) do
    tag =
      case m.discard do
        :type -> "discarded type"
        :termination -> "discarded termination"
        _ -> m.outcome
      end

    by =
      Enum.map(m.killed_by, fn k ->
        "  by #{k.name} at #{k.location}"
      end)

    ["#{m.id} #{m.operator} #{m.location} #{tag}"] ++
      by ++ ["  before: #{m.before}", "  after: #{Map.fetch!(m, :after)}"]
  end

  defp app_version do
    case Application.spec(:muro, :vsn) do
      v when is_list(v) -> List.to_string(v)
      _ -> "0.0.0"
    end
  end

  defp show_loc(d) do
    case Map.get(d, :loc) do
      {line, col} when is_integer(line) and is_integer(col) ->
        case Map.get(d, :file) do
          path when is_binary(path) -> loc_text(path, {line, col})
          _ -> "#{line}:#{col}"
        end

      {file, line, col} when is_binary(file) ->
        "#{file}:#{line}:#{col}"

      _ ->
        "1:1"
    end
  end

  defp loc_text(nil, {line, col}), do: "#{line}:#{col}"

  defp loc_text(file, {line, col}) do
    "#{cwd_rel(file)}:#{line}:#{col}"
  end

  defp line_col({line, col}) when is_integer(line) and is_integer(col), do: {line, col}
  defp line_col({_file, line, col}), do: {line, col}
  defp line_col(_), do: {1, 1}

  defp cwd_rel(path) do
    case Path.relative_to_cwd(path) do
      ^path -> path
      rel -> rel
    end
  end

  # -- json -------------------------------------------------------------------

  defp mutant_json(m) do
    {:obj,
     [
       {"id", {:str, m.id}},
       {"def", {:str, m.def}},
       {"operator", {:str, m.operator}},
       {"location", {:str, m.location}},
       {"before", {:str, m.before}},
       {"after", {:str, Map.fetch!(m, :after)}},
       {"outcome", {:str, m.outcome}},
       {"killed_by",
        {:arr,
         Enum.map(m.killed_by, fn k ->
           {:obj, [{"name", {:str, k.name}}, {"location", {:str, k.location}}]}
         end)}}
     ]}
  end

  defp json_object(pairs) do
    inner = Enum.map_join(pairs, ",", fn {k, v} -> json_string(k) <> ":" <> json_value(v) end)
    "{" <> inner <> "}"
  end

  defp json_value({:str, s}), do: json_string(s)
  defp json_value({:int, n}) when is_integer(n), do: Integer.to_string(n)
  defp json_value({:obj, pairs}), do: json_object(pairs)
  defp json_value({:arr, xs}), do: "[" <> Enum.map_join(xs, ",", &json_value/1) <> "]"

  defp json_string(s) do
    "\"" <> escape(s) <> "\""
  end

  defp escape(s) do
    s
    |> String.replace("\\", "\\\\")
    |> String.replace("\"", "\\\"")
    |> String.replace("\n", "\\n")
    |> String.replace("\r", "\\r")
    |> String.replace("\t", "\\t")
  end
end

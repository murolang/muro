defmodule Muro.Emit.JS do
  @moduledoc """
  Emit a closed run book to JavaScript. Specs and evidence are omitted.
  Run bodies are the closure image from `Muro.IR` (`closures: true`).

  The text is an ES module. `node` runs the `.mjs`. A `.d.ts` beside it
  names the host types. A self-tail call is a loop. Any other named
  recursion, including mutual recursion, is a trampoline, so a deep
  `Nat` does not grow the JavaScript stack. At the host boundary an
  `I64` is a signed bigint and an unsigned word is an unsigned bigint.
  Inside the module, word operations keep the unsigned residue.

  A refusal is `c:machine`, `c:stream`, `c:erased`, `c:session`,
  `c:host`, or `c:unsupported`. A lambda is a closure, so `c:lambda`
  is not a refusal here. A session declaration or a host placement
  refuses the book.

  This is not `Muro.Emit.Node`. That file is the BEAM `--node` backend.

  Identifiers come from `Muro.Emit.Name`. A source name is spelled there.
  A helper and a step are generated there. The two spellings share no
  identifier. A binder is claimed against the function names in the file.
  The proof stops at the run image.
  """

  alias Muro.Emit
  alias Muro.Emit.Name
  alias Muro.IR

  @js_keywords ~w(
    await break case catch class const continue debugger default delete
    do else enum export extends false finally for function if import in
    instanceof let new null return super switch this throw true try typeof
    var void while with yield implements interface package private protected
    public static eval arguments
  ) |> MapSet.new()

  @host ~w(
    undefined NaN Infinity
    Array Object Promise Map Set Symbol BigInt
    console globalThis window process module exports require
    Function Number String Boolean Date Math JSON Error Reflect Proxy
    WeakMap WeakSet parseInt parseFloat isNaN isFinite
    constructor prototype
    type namespace declare abstract keyof readonly infer asserts unique
    satisfies override accessor
  ) |> MapSet.new()

  @forbidden MapSet.union(@js_keywords, @host)

  # TypeScript rejects these as type-alias names, and they are the aliases
  # this file already exports. Matched against the encoding, like keywords.
  @ts_reserved ~w(
    string number boolean bigint symbol any unknown never object
    undefined null void this
    Nat Unit U8 U32 U64 I64 WordBool Opt Pair Stream Atom
  ) |> MapSet.new()

  @type_forbidden MapSet.union(@forbidden, @ts_reserved)

  @tags ~w(
    mod bits half abort suc pred data stream uncons canon
    res add sub mul band bnot bor bxor eq slt lt le pow2
    shl ashr shr toZ fromZ inRange some none
    cadd csub cmul badDiv negBits absBits div rem
    of ton cast scrut pair
    bounce go hole ret stack
  )

  @session_kinds ~w(
    session conform meet endpoint read choreography talk seat link relay
  )a

  @host_kinds ~w(place scheme move)a

  @unsigned_words [:u8, :u32, :u64]

  @doc """
  Render `book` as an ES module and a declaration file for `stem`.
  """
  def render(book, stem) when is_list(book) and is_binary(stem) do
    case compile(book) do
      {:ok, compiled, types} -> {:ok, mjs(stem, compiled), dts(compiled, types, book)}
      {:error, reason} -> {:error, reason}
    end
  end

  @doc """
  Names, signatures, layouts, and clause heads of the module `render/2`
  writes. No source is written.
  """
  def outline(book, _stem) when is_list(book) do
    case compile(book) do
      {:ok, compiled, _types} ->
        user = Enum.reject(compiled, &generated?/1)

        {:ok,
         %{
           names:
             compiled
             |> Enum.flat_map(fn rec -> [rec.name | param_names(rec)] end)
             |> Enum.uniq(),
           elixir: Emit.elixir_names(book),
           signatures: Enum.map(user, &signature/1),
           layouts:
             Enum.map(user, fn rec ->
               %{
                 name: rec.fun.name,
                 layout: rec.fun.ret,
                 params: Enum.map(rec.fun.params, fn {_n, lay} -> lay end)
               }
             end),
           clauses: Enum.map(compiled, & &1.head)
         }}

      {:error, reason} ->
        {:error, reason}
    end
  end

  @doc false
  def source_id(name) when is_binary(name), do: spell(name)

  defp compile(book) do
    with :ok <- refuse_book(book),
         {:ok, funs} <- IR.elaborate(book, closures: true),
         {:ok, groups, _} <- Emit.partition_funs(funs, Emit.run_defs(book)) do
      h = helper_map()
      taken = MapSet.new(Map.values(h))
      names = Emit.def_names(book, &spell/1, taken)
      steps = Enum.flat_map(groups, fn {_fun, ss} -> ss end)
      used = MapSet.union(taken, MapSet.new(Map.values(names)))

      {step_names, _used} =
        Enum.reduce(steps, {%{}, used}, fn step, {map, used} ->
          {rn, used} = Name.claim(Name.gen("step", map_size(map)), used)
          {Map.put(map, step.name, rn), used}
        end)

      visible =
        used
        |> MapSet.union(MapSet.new(Map.values(step_names)))
        |> Name.open()

      rec = recursive_names(funs)

      st = %{
        h: h,
        names: names,
        steps: step_names,
        step_funs: Map.new(steps, &{&1.name, &1}),
        file_scope: visible,
        scope: visible,
        vars: %{},
        targets: build_targets(funs, names, step_names, rec),
        rec: rec,
        k: 0,
        self: nil,
        params: []
      }

      ordered = steps ++ Enum.map(groups, fn {fun, _} -> fun end)

      with {:ok, compiled} <- emit_all(ordered, st) do
        {:ok, compiled, data_types(book)}
      end
    end
  end

  defp refuse_book(book) do
    Enum.find_value(book, :ok, fn entry ->
      kind = Map.get(entry, :kind, :def)

      cond do
        kind in @session_kinds -> {:error, "c:session"}
        kind in @host_kinds -> {:error, "c:host"}
        true -> nil
      end
    end)
  end

  defp recursive_names(funs) do
    graph = Map.new(funs, fn fun -> {fun.name, calls_of(fun.body)} end)

    Enum.reduce(Map.keys(graph), MapSet.new(), fn name, acc ->
      if reaches?(name, name, graph, MapSet.new()), do: MapSet.put(acc, name), else: acc
    end)
  end

  defp reaches?(origin, name, graph, seen) do
    Enum.any?(Map.get(graph, name, []), fn callee ->
      cond do
        callee == origin -> true
        MapSet.member?(seen, callee) -> false
        true -> reaches?(origin, callee, graph, MapSet.put(seen, callee))
      end
    end)
  end

  defp calls_of(tm), do: tm |> calls_acc([]) |> Enum.uniq()

  defp calls_acc({:call, name, args}, acc), do: Enum.reduce(args, [name | acc], &calls_acc/2)
  defp calls_acc({:lam, _, _, body}, acc), do: calls_acc(body, acc)
  defp calls_acc({:su, t}, acc), do: calls_acc(t, acc)
  defp calls_acc({:pair, a, b}, acc), do: calls_acc(b, calls_acc(a, acc))
  defp calls_acc({:con, _, _, args}, acc), do: Enum.reduce(args, acc, &calls_acc/2)
  defp calls_acc({:appv, f, a}, acc), do: calls_acc(a, calls_acc(f, acc))
  defp calls_acc({:let, _, _, val, body}, acc), do: calls_acc(body, calls_acc(val, acc))
  defp calls_acc({:letp, _, _, e, body}, acc), do: calls_acc(body, calls_acc(e, acc))
  defp calls_acc({:uncons, e}, acc), do: calls_acc(e, acc)

  defp calls_acc({:stream, seed, caps, _step}, acc) do
    Enum.reduce(caps, calls_acc(seed, acc), fn {_name, tm}, acc -> calls_acc(tm, acc) end)
  end

  defp calls_acc({:match, scrut, _, arms}, acc) do
    Enum.reduce(arms, calls_acc(scrut, acc), fn {:arm, _, _, body}, acc ->
      calls_acc(body, acc)
    end)
  end

  defp calls_acc({:wrd, _, _, args}, acc), do: Enum.reduce(args, acc, &calls_acc/2)
  defp calls_acc(_tm, acc), do: acc

  defp build_targets(funs, names, step_names, rec) do
    Map.new(funs, fn fun ->
      js = js_name(fun, names, step_names)
      recursive = MapSet.member?(rec, fun.name)
      boundary = fun.export == true and boundary?(fun)
      call = if boundary, do: js <> "__r", else: js
      worker = if recursive, do: js <> "__w", else: nil

      {fun.name,
       %{
         js: js,
         recursive: recursive,
         boundary: boundary,
         call: call,
         worker: worker,
         arity: length(fun.params)
       }}
    end)
  end

  defp js_name(fun, names, step_names) do
    if generated_fun?(fun),
      do: Map.fetch!(step_names, fun.name),
      else: Map.fetch!(names, fun.name)
  end

  defp boundary?(fun) do
    converts?(fun.ret) or Enum.any?(fun.params, fn {_name, lay} -> converts?(lay) end)
  end

  defp converts?(:i64), do: true
  defp converts?(kind) when kind in @unsigned_words, do: true
  defp converts?({:opt, inner}), do: converts?(inner)
  defp converts?({:pair, a, b}), do: converts?(a) or converts?(b)
  defp converts?(_lay), do: false

  defp emit_all(funs, st) do
    Enum.reduce_while(funs, {:ok, []}, fn fun, {:ok, acc} ->
      case emit_fun(fun, st) do
        {:ok, rec} -> {:cont, {:ok, acc ++ [rec]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp emit_fun(fun, st) do
    info = Map.fetch!(st.targets, fun.name)
    base = %{st | scope: st.file_scope, vars: %{}, k: 0, self: nil, params: []}

    cond do
      info.recursive -> emit_worker(fun, base, info)
      info.boundary -> emit_boundary(fun, base, info)
      true -> emit_plain(fun, base)
    end
  end

  defp emit_plain(fun, st) do
    {fst, name, kw, params} = open_fun(fun, st)

    with {:ok, body} <- emit_tm(fun.body, fst) do
      head = "#{kw} #{name}(#{arg_names(params)})"
      {:ok, compiled(fun, name, kw, params, head, block(head, ["return (#{body});"]))}
    end
  end

  defp emit_boundary(fun, st, info) do
    {fst, name, _kw, params} = open_fun(fun, st)

    with {:ok, body} <- emit_tm(fun.body, fst) do
      residue = block("function #{info.call}(#{arg_names(params)})", ["return (#{body});"])
      wrapper = wrapper_block(name, params, fun.ret, info, fst)
      head = "export function #{name}(#{arg_names(params)})"
      {:ok, compiled(fun, name, "export function", params, head, residue <> "\n" <> wrapper)}
    end
  end

  defp emit_worker(fun, st, info) do
    {fst, name, kw, params} = open_fun(fun, st)
    fst = %{fst | self: fun.name, params: params}

    with {:ok, lines, _fst} <- cps(fun.body, fst, true) do
      args = arg_names(params)
      worker_args = call_args(Enum.map(params, fn {_src, rn, _lay} -> rn end), fst.h.stack)

      worker =
        block(
          "function #{info.worker}(#{worker_args})",
          ["while (true) {"] ++ indent(lines) ++ ["}"]
        )

      bounce_body = [
        "return #{fst.h.bounce}((#{fst.h.stack}) => #{info.worker}(#{pass_args(params, fst.h.stack)}));"
      ]

      bounce =
        if info.boundary do
          block("function #{info.call}(#{args})", bounce_body) <>
            "\n" <> wrapper_block(name, params, fun.ret, info, fst)
        else
          block("#{kw} #{name}(#{args})", bounce_body)
        end

      head =
        if fun.export, do: "export function #{name}(#{args})", else: "function #{name}(#{args})"

      kw_out = if fun.export, do: "export function", else: "function"
      {:ok, compiled(fun, name, kw_out, params, head, worker <> "\n" <> bounce)}
    end
  end

  defp wrapper_block(host, params, ret, info, st) do
    ins = Enum.map_join(params, ", ", fn {_src, rn, lay} -> in_expr(rn, lay) end)
    retn = st.h.ret

    block("export function #{host}(#{arg_names(params)})", [
      "const #{retn} = #{info.call}(#{ins});",
      "return #{out_expr(retn, ret)};"
    ])
  end

  defp compiled(fun, name, kw, params, head, text) do
    %{fun: fun, name: name, kw: kw, params: params, head: head, text: text}
  end

  defp block(head, lines) do
    inner =
      Enum.map_join(lines, "\n", fn
        "" -> ""
        line -> "  " <> line
      end)

    head <> " {\n" <> inner <> "\n}"
  end

  defp indent(lines) do
    Enum.map(lines, fn
      "" -> ""
      line -> "  " <> line
    end)
  end

  defp arg_names(params), do: Enum.map_join(params, ", ", fn {_src, rn, _lay} -> rn end)

  defp pass_args(params, stack) do
    call_args(Enum.map(params, fn {_src, rn, _lay} -> rn end), stack)
  end

  defp call_args([], stack), do: stack
  defp call_args(es, stack), do: Enum.join(es, ", ") <> ", " <> stack

  defp cps(tm, st, tail?) do
    if contains_rec?(tm, st.rec) do
      cps_rec(tm, st, tail?)
    else
      with {:ok, expr} <- emit_tm(tm, st), do: {:ok, ["return (#{expr});"], st}
    end
  end

  defp cps_rec({:let, name, lay, val, body}, st, tail?) do
    if contains_rec?(val, st.rec) do
      cps_suspend(val, fn hole -> {:let, name, lay, hole, body} end, st)
    else
      cps_let_pure(name, lay, val, body, st, tail?)
    end
  end

  defp cps_rec({:letp, a, b, e, body}, st, tail?) do
    if contains_rec?(e, st.rec) do
      cps_suspend(e, fn hole -> {:letp, a, b, hole, body} end, st)
    else
      cps_letp_pure(a, b, e, body, st, tail?)
    end
  end

  defp cps_rec({:match, scrut, kind, arms}, st, tail?) do
    if contains_rec?(scrut, st.rec) do
      cps_suspend(scrut, fn hole -> {:match, hole, kind, arms} end, st)
    else
      cps_match(scrut, kind, arms, st, tail?)
    end
  end

  defp cps_rec({:call, name, args}, st, tail?) do
    if Enum.any?(args, &contains_rec?(&1, st.rec)) do
      cps_suspend({:call, name, args}, fn hole -> hole end, st)
    else
      cps_call(name, args, st, tail?)
    end
  end

  defp cps_rec(tm, st, _tail?), do: cps_suspend(tm, fn hole -> hole end, st)

  defp cps_let_pure(name, lay, val, body, st, tail?) do
    with {:ok, ve} <- emit_tm(val, st) do
      {rn, scope} = Name.bind(spell(name), st.scope)
      st2 = %{st | scope: scope, vars: Map.put(st.vars, name, rn)}
      rhs = if lay == :opaque and val == :ze, do: "undefined", else: ve

      with {:ok, lines, st3} <- cps(body, st2, tail?) do
        {:ok, ["const #{rn} = (#{rhs});" | lines], st3}
      end
    end
  end

  defp cps_letp_pure(a, b, e, body, st, tail?) do
    with {:ok, ee} <- emit_tm(e, st) do
      {ra, scope} = Name.bind(spell(a), st.scope)
      {rb, scope} = Name.bind(spell(b), scope)
      {pn, st1} = fresh_name(%{st | scope: scope})
      vars = st.vars |> Map.put(a, ra) |> Map.put(b, rb)
      st2 = %{st1 | vars: vars}

      with {:ok, lines, st3} <- cps(body, st2, tail?) do
        {:ok,
         [
           "const #{pn} = (#{ee});",
           "const #{ra} = #{pn}[0];",
           "const #{rb} = #{pn}[1];"
           | lines
         ], st3}
      end
    end
  end

  defp cps_match(scrut, :nat, arms, st, tail?) do
    with {:ok, se} <- emit_tm(scrut, st),
         {:arm, "zero", _, zbody} <- arm(arms, "zero"),
         {:arm, "suc", [y], sbody} <- arm(arms, "suc") do
      {scr, st1} = fresh_name(st)

      with {:ok, zlines, _} <- cps(zbody, st1, tail?),
           {:ok, slines, rn} <- cps_suc(y, sbody, st1, scr, tail?) do
        lines =
          ["const #{scr} = (#{se});", "if (#{scr} === 0n) {"] ++
            indent(zlines) ++
            ["} else {"] ++
            indent(["const #{rn} = #{st.h.pred}(#{scr});" | slines]) ++
            ["}"]

        {:ok, lines, st1}
      end
    else
      {:error, _} = err -> err
      _ -> {:error, "c:unsupported"}
    end
  end

  defp cps_match(scrut, kind, arms, st, tail?) when kind == :atom or is_tuple(kind) do
    with {:ok, se} <- emit_tm(scrut, st) do
      {scr, st1} = fresh_name(st)

      with {:ok, cases} <- cps_cases(arms, st1, kind, tail?, scr) do
        switch_on = if kind == :atom, do: scr, else: "#{scr}.tag"

        lines =
          ["const #{scr} = (#{se});", "switch (#{switch_on}) {"] ++
            cases ++
            ["  default: { return #{st.h.abort}(); }", "}"]

        {:ok, lines, st1}
      end
    end
  end

  defp cps_match(_scrut, _kind, _arms, _st, _tail?), do: {:error, "c:unsupported"}

  defp cps_suc(y, body, st, _scr, tail?) do
    {rn, scope} = Name.bind(spell(y), st.scope)
    st2 = %{st | scope: scope, vars: Map.put(st.vars, y, rn)}

    with {:ok, lines, _} <- cps(body, st2, tail?) do
      {:ok, lines, rn}
    end
  end

  defp cps_cases(arms, st, kind, tail?, scr) do
    Enum.reduce_while(arms, {:ok, []}, fn arm, {:ok, acc} ->
      case cps_one_case(arm, st, kind, tail?, scr) do
        {:ok, lines} -> {:cont, {:ok, acc ++ lines}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp cps_one_case({:arm, cname, binders, body}, st, kind, tail?, scr) do
    {names, st2} = if kind == :atom, do: {[], st}, else: bind_fields(binders, st)

    with {:ok, lines, _} <- cps(body, st2, tail?) do
      consts =
        names
        |> Enum.with_index()
        |> Enum.map(fn {rn, i} -> "const #{rn} = #{scr}.fields[#{i}];" end)

      {:ok, ["  case #{js_str(cname)}: {"] ++ indent(indent(consts ++ lines)) ++ ["  }"]}
    end
  end

  defp cps_one_case(_arm, _st, _kind, _tail?, _scr), do: {:error, "c:unsupported"}

  defp cps_call(name, args, st, tail?) do
    with {:ok, info} <- target(st, name, length(args)),
         {:ok, es} <- emit_many(args, st) do
      cond do
        tail? and name == st.self ->
          {tmps, binds, st1} = bind_temps(es, st)
          assigns = assign_params(st.params, tmps)
          {:ok, binds ++ assigns ++ ["continue;"], st1}

        info.recursive ->
          {tmps, binds, st1} = bind_temps(es, st)

          {:ok,
           binds ++ ["return #{st.h.go}(() => #{info.worker}(#{call_args(tmps, st.h.stack)}));"],
           st1}

        true ->
          {:ok, ["return #{info.call}(#{Enum.join(es, ", ")});"], st}
      end
    end
  end

  defp cps_suspend(focus, wrap, st) do
    case lift(focus, st.rec) do
      {:ok, {:call, name, args}, rebuild} ->
        with {:ok, info} <- target(st, name, length(args)),
             true <- info.recursive,
             {:ok, es} <- emit_many(args, st) do
          {hole, st1} = fresh_name(st)
          whole = wrap.(rebuild.({:js, hole}))

          with {:ok, rest, st2} <- cps(whole, st1, false) do
            lines =
              ["#{st.h.stack}.push((#{hole}) => {"] ++
                indent(rest) ++
                [
                  "});",
                  "return #{st.h.go}(() => #{info.worker}(#{call_args(es, st.h.stack)}));"
                ]

            {:ok, lines, st2}
          end
        else
          false -> {:error, "c:unsupported"}
          {:error, _} = err -> err
        end

      _ ->
        {:error, "c:unsupported"}
    end
  end

  defp target(st, name, arity) do
    case Map.fetch(st.targets, name) do
      {:ok, %{arity: ^arity} = info} -> {:ok, info}
      {:ok, _info} -> {:error, "c:unsupported"}
      :error -> {:error, "c:unsupported"}
    end
  end

  defp bind_temps(es, st) do
    {pairs, st} =
      Enum.map_reduce(es, st, fn expr, st ->
        {rn, st} = fresh_name(st)
        {{rn, "const #{rn} = (#{expr});"}, st}
      end)

    {Enum.map(pairs, &elem(&1, 0)), Enum.map(pairs, &elem(&1, 1)), st}
  end

  defp assign_params(params, tmps) do
    params
    |> Enum.zip(tmps)
    |> Enum.map(fn {{_src, rn, _lay}, tmp} -> "#{rn} = #{tmp};" end)
  end

  defp fresh_name(st) do
    {rn, scope} = Name.bind(st.h.hole <> Integer.to_string(st.k), st.scope)
    {rn, %{st | k: st.k + 1, scope: scope}}
  end

  defp contains_rec?({:call, name, args}, rec) do
    MapSet.member?(rec, name) or Enum.any?(args, &contains_rec?(&1, rec))
  end

  defp contains_rec?({:lam, _, _, _}, _rec), do: false
  defp contains_rec?({:js, _}, _rec), do: false
  defp contains_rec?({:su, t}, rec), do: contains_rec?(t, rec)
  defp contains_rec?({:pair, a, b}, rec), do: contains_rec?(a, rec) or contains_rec?(b, rec)
  defp contains_rec?({:con, _, _, args}, rec), do: Enum.any?(args, &contains_rec?(&1, rec))
  defp contains_rec?({:appv, f, a}, rec), do: contains_rec?(f, rec) or contains_rec?(a, rec)

  defp contains_rec?({:let, _, _, val, body}, rec),
    do: contains_rec?(val, rec) or contains_rec?(body, rec)

  defp contains_rec?({:letp, _, _, e, body}, rec),
    do: contains_rec?(e, rec) or contains_rec?(body, rec)

  defp contains_rec?({:uncons, e}, rec), do: contains_rec?(e, rec)

  defp contains_rec?({:stream, seed, caps, _step}, rec) do
    contains_rec?(seed, rec) or Enum.any?(caps, fn {_name, tm} -> contains_rec?(tm, rec) end)
  end

  defp contains_rec?({:match, scrut, _, arms}, rec) do
    contains_rec?(scrut, rec) or
      Enum.any?(arms, fn {:arm, _, _, body} -> contains_rec?(body, rec) end)
  end

  defp contains_rec?({:wrd, _, _, args}, rec), do: Enum.any?(args, &contains_rec?(&1, rec))
  defp contains_rec?(_tm, _rec), do: false

  defp lift({:call, name, args} = tm, rec) do
    case lift_list(args, rec) do
      {:ok, index, call, rebuild} ->
        {:ok, call, fn hole -> {:call, name, List.replace_at(args, index, rebuild.(hole))} end}

      :none ->
        if MapSet.member?(rec, name), do: {:ok, tm, fn hole -> hole end}, else: :none
    end
  end

  defp lift({:lam, _, _, _}, _rec), do: :none
  defp lift({:js, _}, _rec), do: :none
  defp lift({:su, t}, rec), do: lift_one(t, rec, fn hole -> {:su, hole} end)

  defp lift({:pair, a, b}, rec) do
    case lift(a, rec) do
      {:ok, call, rebuild} -> {:ok, call, fn hole -> {:pair, rebuild.(hole), b} end}
      :none -> lift_one(b, rec, fn hole -> {:pair, a, hole} end)
    end
  end

  defp lift({:con, data, cname, args}, rec) do
    lift_kids(args, rec, fn args -> {:con, data, cname, args} end)
  end

  defp lift({:appv, f, a}, rec) do
    case lift(f, rec) do
      {:ok, call, rebuild} -> {:ok, call, fn hole -> {:appv, rebuild.(hole), a} end}
      :none -> lift_one(a, rec, fn hole -> {:appv, f, hole} end)
    end
  end

  defp lift({:let, name, lay, val, body}, rec) do
    case lift(val, rec) do
      {:ok, call, rebuild} ->
        {:ok, call, fn hole -> {:let, name, lay, rebuild.(hole), body} end}

      :none ->
        lift_one(body, rec, fn hole -> {:let, name, lay, val, hole} end)
    end
  end

  defp lift({:letp, a, b, e, body}, rec) do
    case lift(e, rec) do
      {:ok, call, rebuild} -> {:ok, call, fn hole -> {:letp, a, b, rebuild.(hole), body} end}
      :none -> lift_one(body, rec, fn hole -> {:letp, a, b, e, hole} end)
    end
  end

  defp lift({:uncons, e}, rec), do: lift_one(e, rec, fn hole -> {:uncons, hole} end)

  defp lift({:stream, seed, caps, step}, rec) do
    case lift(seed, rec) do
      {:ok, call, rebuild} ->
        {:ok, call, fn hole -> {:stream, rebuild.(hole), caps, step} end}

      :none ->
        lift_caps(caps, rec, fn caps -> {:stream, seed, caps, step} end)
    end
  end

  defp lift({:match, scrut, kind, arms}, rec) do
    case lift(scrut, rec) do
      {:ok, call, rebuild} ->
        {:ok, call, fn hole -> {:match, rebuild.(hole), kind, arms} end}

      :none ->
        lift_arms(arms, rec, fn arms -> {:match, scrut, kind, arms} end)
    end
  end

  defp lift({:wrd, k, op, args}, rec) do
    lift_kids(args, rec, fn args -> {:wrd, k, op, args} end)
  end

  defp lift(_tm, _rec), do: :none

  defp lift_one(tm, rec, rebuild) do
    case lift(tm, rec) do
      {:ok, call, inner} -> {:ok, call, fn hole -> rebuild.(inner.(hole)) end}
      :none -> :none
    end
  end

  defp lift_kids(items, rec, rebuild) do
    case lift_list(items, rec) do
      {:ok, index, call, inner} ->
        {:ok, call, fn hole -> rebuild.(List.replace_at(items, index, inner.(hole))) end}

      :none ->
        :none
    end
  end

  defp lift_list(items, rec), do: lift_list(items, rec, 0)
  defp lift_list([], _rec, _index), do: :none

  defp lift_list([item | rest], rec, index) do
    case lift(item, rec) do
      {:ok, call, rebuild} -> {:ok, index, call, rebuild}
      :none -> lift_list(rest, rec, index + 1)
    end
  end

  defp lift_caps(caps, rec, rebuild) do
    case lift_list(Enum.map(caps, fn {_name, tm} -> tm end), rec) do
      {:ok, index, call, inner} ->
        {:ok, call,
         fn hole ->
           rebuild.(List.update_at(caps, index, fn {name, _tm} -> {name, inner.(hole)} end))
         end}

      :none ->
        :none
    end
  end

  defp lift_arms([], _rec, _rebuild), do: :none

  defp lift_arms([{:arm, cname, binders, body} | rest], rec, rebuild) do
    case lift(body, rec) do
      {:ok, call, inner} ->
        {:ok, call,
         fn hole ->
           rebuild.([{:arm, cname, binders, inner.(hole)} | rest])
         end}

      :none ->
        case lift_arms(rest, rec, fn arms -> arms end) do
          {:ok, call, inner} ->
            {:ok, call, fn hole -> rebuild.([{:arm, cname, binders, body} | inner.(hole)]) end}

          :none ->
            :none
        end
    end
  end

  defp lift_arms([_ | rest], rec, rebuild), do: lift_arms(rest, rec, rebuild)

  defp arm(arms, name) do
    case find_arm(arms, name) do
      {:arm, _, _, _} = found -> found
      _ -> {:error, "c:unsupported"}
    end
  end

  defp in_expr(js, :i64), do: "BigInt.asUintN(64, #{js})"
  defp in_expr(js, :u8), do: "BigInt.asUintN(8, #{js})"
  defp in_expr(js, :u32), do: "BigInt.asUintN(32, #{js})"
  defp in_expr(js, :u64), do: "BigInt.asUintN(64, #{js})"

  defp in_expr(js, {:opt, inner}) do
    if converts?(inner) do
      "((#{js}) && (#{js}).k === \"some\" ? { k: \"some\", v: #{in_expr("(#{js}).v", inner)} } : (#{js}))"
    else
      js
    end
  end

  defp in_expr(js, {:pair, a, b}) do
    if converts?(a) or converts?(b) do
      "[#{in_expr("(#{js})[0]", a)}, #{in_expr("(#{js})[1]", b)}]"
    else
      js
    end
  end

  defp in_expr(js, _lay), do: js

  defp out_expr(js, :i64), do: "BigInt.asIntN(64, #{js})"
  defp out_expr(js, :u8), do: "BigInt.asUintN(8, #{js})"
  defp out_expr(js, :u32), do: "BigInt.asUintN(32, #{js})"
  defp out_expr(js, :u64), do: "BigInt.asUintN(64, #{js})"

  defp out_expr(js, {:opt, inner}) do
    if converts?(inner) do
      "((#{js}) && (#{js}).k === \"some\" ? { k: \"some\", v: #{out_expr("(#{js}).v", inner)} } : (#{js}))"
    else
      js
    end
  end

  defp out_expr(js, {:pair, a, b}) do
    if converts?(a) or converts?(b) do
      "[#{out_expr("(#{js})[0]", a)}, #{out_expr("(#{js})[1]", b)}]"
    else
      js
    end
  end

  defp out_expr(js, _lay), do: js

  defp open_fun(fun, st) do
    {params, scope} =
      Enum.map_reduce(fun.params, st.scope, fn {src, lay}, scope ->
        {rn, scope} = Name.bind(spell(src), scope)
        {{src, rn, lay}, scope}
      end)

    vars = Map.new(params, fn {src, rn, _lay} -> {src, rn} end)

    name =
      if generated_fun?(fun),
        do: Map.fetch!(st.steps, fun.name),
        else: Map.fetch!(st.names, fun.name)

    kw =
      cond do
        generated_fun?(fun) -> "function"
        fun.export -> "export function"
        true -> "function"
      end

    {%{st | scope: scope, vars: vars}, name, kw, params}
  end

  defp emit_tm({:var, name}, st) do
    case Map.fetch(st.vars, name) do
      {:ok, rn} -> {:ok, rn}
      :error -> {:error, "c:unsupported"}
    end
  end

  defp emit_tm(:ze, _st), do: {:ok, "0n"}
  defp emit_tm(:tt, _st), do: {:ok, "null"}
  defp emit_tm(:abort, st), do: {:ok, st.h.abort <> "()"}

  defp emit_tm({:su, t}, st) do
    with {:ok, e} <- emit_tm(t, st), do: {:ok, "#{st.h.suc}(#{e})"}
  end

  defp emit_tm({:pair, a, b}, st) do
    with {:ok, ea} <- emit_tm(a, st),
         {:ok, eb} <- emit_tm(b, st),
         do: {:ok, "[#{ea}, #{eb}]"}
  end

  defp emit_tm({:js, rn}, _st) when is_binary(rn), do: {:ok, rn}

  defp emit_tm({:call, name, args}, st) do
    with {:ok, info} <- target(st, name, length(args)),
         {:ok, es} <- emit_many(args, st) do
      {:ok, "#{info.call}(#{Enum.join(es, ", ")})"}
    end
  end

  defp emit_tm({:con, "Atom", name, []}, _st), do: {:ok, js_str(name)}

  defp emit_tm({:con, _data, cname, args}, st) do
    with {:ok, es} <- emit_many(args, st) do
      {:ok, "#{st.h.data}(#{js_str(cname)}#{arg_tail(es)})"}
    end
  end

  defp emit_tm({:lam, name, _lay, body}, st) do
    {rn, scope} = Name.bind(spell(name), st.scope)
    st2 = %{st | scope: scope, vars: Map.put(st.vars, name, rn)}

    with {:ok, be} <- emit_tm(body, st2) do
      {:ok, "(#{rn}) => (#{be})"}
    end
  end

  defp emit_tm({:appv, f, a}, st) do
    with {:ok, fe} <- emit_tm(f, st),
         {:ok, ae} <- emit_tm(a, st) do
      {:ok, "#{callee(fe)}(#{ae})"}
    end
  end

  defp emit_tm({:let, name, lay, val, body}, st) do
    with {:ok, ve} <- emit_tm(val, st) do
      {rn, scope} = Name.bind(spell(name), st.scope)
      st2 = %{st | scope: scope, vars: Map.put(st.vars, name, rn)}

      with {:ok, be} <- emit_tm(body, st2) do
        rhs = if lay == :opaque and val == :ze, do: "undefined", else: ve
        {:ok, js_fn(["const #{rn} = (#{rhs});", "return (#{be});"])}
      end
    end
  end

  defp emit_tm({:letp, a, b, e, body}, st) do
    with {:ok, ee} <- emit_tm(e, st) do
      {ra, scope} = Name.bind(spell(a), st.scope)
      {rb, scope} = Name.bind(spell(b), scope)
      vars = st.vars |> Map.put(a, ra) |> Map.put(b, rb)
      st2 = %{st | scope: scope, vars: vars}
      p = st.h.pair

      with {:ok, be} <- emit_tm(body, st2) do
        {:ok,
         js_fn([
           "const #{p} = (#{ee});",
           "const #{ra} = #{p}[0];",
           "const #{rb} = #{p}[1];",
           "return (#{be});"
         ])}
      end
    end
  end

  defp emit_tm({:uncons, e}, st) do
    with {:ok, ee} <- emit_tm(e, st), do: {:ok, "#{st.h.uncons}(#{ee})"}
  end

  defp emit_tm({:stream, seed, caps, step}, st) do
    with {:ok, se} <- emit_tm(seed, st),
         {:ok, ces} <- emit_caps(caps, st),
         {:ok, sname} <- fetch_step(st, step) do
      step_fun = Map.fetch!(st.step_funs, step)
      n = length(caps)
      has_seed = length(step_fun.params) > n
      env_args = if n == 0, do: "", else: Enum.map_join(0..(n - 1), ", ", &"env[#{&1}]")

      call =
        cond do
          has_seed and env_args == "" -> "seed"
          has_seed -> env_args <> ", seed"
          true -> env_args
        end

      {:ok,
       "#{st.h.stream}((#{se}), [#{Enum.join(ces, ", ")}], (env, seed) => #{sname}(#{call}))"}
    end
  end

  defp emit_tm({:match, scrut, :nat, arms}, st) do
    with {:ok, se} <- emit_tm(scrut, st),
         {:arm, "zero", _, zbody} <- find_arm(arms, "zero"),
         {:arm, "suc", [y], sbody} <- find_arm(arms, "suc"),
         {:ok, ze} <- emit_tm(zbody, st) do
      {rn, scope} = Name.bind(spell(y), st.scope)
      st2 = %{st | scope: scope, vars: Map.put(st.vars, y, rn)}

      with {:ok, se_body} <- emit_tm(sbody, st2) do
        scr = st.h.scrut

        {:ok,
         js_fn([
           "const #{scr} = (#{se});",
           "if (#{scr} === 0n) {",
           "  return (#{ze});",
           "} else {",
           "  const #{rn} = #{st.h.pred}(#{scr});",
           "  return (#{se_body});",
           "}"
         ])}
      end
    else
      {:error, _} = err -> err
      _ -> {:error, "c:unsupported"}
    end
  end

  defp emit_tm({:match, scrut, {:data, _}, arms}, st) do
    with {:ok, se} <- emit_tm(scrut, st),
         {:ok, cases} <- arm_cases(arms, st, :data) do
      scr = st.h.scrut

      {:ok,
       js_fn([
         "const #{scr} = (#{se});",
         "switch (#{scr}.tag) {",
         cases,
         "  default: { return #{st.h.abort}(); }",
         "}"
       ])}
    end
  end

  defp emit_tm({:match, scrut, :atom, arms}, st) do
    with {:ok, se} <- emit_tm(scrut, st),
         {:ok, cases} <- arm_cases(arms, st, :atom) do
      scr = st.h.scrut

      {:ok,
       js_fn([
         "const #{scr} = (#{se});",
         "switch (#{scr}) {",
         cases,
         "  default: { return #{st.h.abort}(); }",
         "}"
       ])}
    end
  end

  defp emit_tm({:wrd, k, op, args}, st), do: emit_wrd(k, op, args, st)
  defp emit_tm(_tm, _st), do: {:error, "c:unsupported"}

  defp emit_wrd(k, op, args, st) do
    h = st.h
    ks = js_str(Atom.to_string(k))

    with {:ok, es} <- emit_many(args, st) do
      at = fn i -> Enum.at(es, i) end

      text =
        case op do
          {:lit, _, n} -> bigint(n)
          {:of, _} -> "#{h.of}(#{ks}, #{at.(0)})"
          :ton -> "#{h.ton}(#{ks}, #{at.(0)})"
          :add -> "#{h.add}(#{ks}, #{at.(0)}, #{at.(1)})"
          :sub -> "#{h.sub}(#{ks}, #{at.(0)}, #{at.(1)})"
          :mul -> "#{h.mul}(#{ks}, #{at.(0)}, #{at.(1)})"
          :and -> "#{h.band}(#{ks}, #{at.(0)}, #{at.(1)})"
          :or -> "#{h.bor}(#{ks}, #{at.(0)}, #{at.(1)})"
          :xor -> "#{h.bxor}(#{ks}, #{at.(0)}, #{at.(1)})"
          :not -> "#{h.bnot}(#{ks}, #{at.(0)})"
          :cadd -> "#{h.cadd}(#{ks}, #{at.(0)}, #{at.(1)})"
          :csub -> "#{h.csub}(#{ks}, #{at.(0)}, #{at.(1)})"
          :cmul -> "#{h.cmul}(#{ks}, #{at.(0)}, #{at.(1)})"
          :div -> "#{h.div}(#{ks}, #{at.(0)}, #{at.(1)})"
          :rem -> "#{h.rem}(#{ks}, #{at.(0)}, #{at.(1)})"
          :eq -> "#{h.eq}(#{ks}, #{at.(0)}, #{at.(1)})"
          :lt -> "#{h.lt}(#{ks}, #{at.(0)}, #{at.(1)})"
          :le -> "#{h.le}(#{ks}, #{at.(0)}, #{at.(1)})"
          :shl -> "#{h.shl}(#{ks}, #{at.(0)}, #{at.(1)})"
          :shr -> "#{h.shr}(#{ks}, #{at.(0)}, #{at.(1)})"
          {:cast, _} -> "#{h.cast}(#{ks}, #{at.(0)})"
          true -> "true"
          false -> "false"
          :some -> "#{h.some}(#{at.(0)})"
          :none -> "#{h.none}()"
          _ -> :bad
        end

      if text == :bad, do: {:error, "c:unsupported"}, else: {:ok, text}
    end
  end

  defp arm_cases(arms, st, kind) do
    Enum.reduce_while(arms, {:ok, []}, fn arm, {:ok, acc} ->
      case one_case(arm, st, kind) do
        {:ok, text} -> {:cont, {:ok, acc ++ [text]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
    |> case do
      {:ok, texts} -> {:ok, Enum.join(texts, "\n")}
      err -> err
    end
  end

  defp one_case({:arm, cname, binders, body}, st, kind) do
    {names, st2} = bind_fields(binders, st)

    with {:ok, be} <- emit_tm(body, st2) do
      scr = st.h.scrut

      consts =
        case kind do
          :data ->
            names
            |> Enum.with_index()
            |> Enum.map(fn {rn, i} -> "    const #{rn} = #{scr}.fields[#{i}];" end)

          :atom ->
            []
        end

      lines =
        ["  case #{js_str(cname)}: {"] ++
          consts ++
          ["    return (#{be});", "  }"]

      {:ok, Enum.join(lines, "\n")}
    end
  end

  defp bind_fields(binders, st) do
    Enum.map_reduce(binders, st, fn src, st ->
      {rn, scope} = Name.bind(spell(src), st.scope)
      {rn, %{st | scope: scope, vars: Map.put(st.vars, src, rn)}}
    end)
  end

  defp find_arm(arms, name) do
    Enum.find(arms, fn
      {:arm, ^name, _, _} -> true
      _ -> false
    end)
  end

  defp emit_many(ts, st) do
    Enum.reduce_while(ts, {:ok, []}, fn t, {:ok, acc} ->
      case emit_tm(t, st) do
        {:ok, e} -> {:cont, {:ok, acc ++ [e]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp emit_caps(caps, st) do
    emit_many(Enum.map(caps, fn {_name, tm} -> tm end), st)
  end

  defp fetch_step(st, step) do
    case Map.fetch(st.steps, step) do
      {:ok, name} -> {:ok, name}
      :error -> {:error, "c:unsupported"}
    end
  end

  defp arg_tail([]), do: ""
  defp arg_tail(es), do: ", " <> Enum.join(es, ", ")

  defp callee(fe) do
    if Regex.match?(~r/^[A-Za-z_$][A-Za-z0-9_$]*$/, fe), do: fe, else: "(#{fe})"
  end

  defp js_fn(lines) do
    body =
      Enum.map_join(lines, "\n", fn line ->
        line
        |> String.split("\n")
        |> Enum.map_join("\n", &("  " <> &1))
      end)

    "(() => {\n" <> body <> "\n})()"
  end

  defp bigint(n) when is_integer(n) and n >= 0, do: Integer.to_string(n) <> "n"
  defp bigint(n) when is_integer(n), do: "(" <> Integer.to_string(n) <> "n)"

  defp js_str(s) when is_binary(s) do
    body =
      s
      |> String.replace("\\", "\\\\")
      |> String.replace("\"", "\\\"")
      |> String.replace("\n", "\\n")
      |> String.replace("\r", "\\r")
      |> String.replace("\u2028", "\\u2028")
      |> String.replace("\u2029", "\\u2029")

    "\"" <> body <> "\""
  end

  defp spell(name), do: Name.spell(name, @forbidden)
  defp type_spell(name), do: Name.spell(name, @type_forbidden)

  defp helper_map do
    Map.new(@tags, fn tag -> {String.to_atom(tag), Name.gen(tag)} end)
  end

  defp generated?(rec), do: generated_fun?(rec.fun)
  defp generated_fun?(fun), do: Map.get(fun, :generated, false) == true

  defp param_names(rec), do: Enum.map(rec.params, fn {_src, rn, _lay} -> rn end)

  defp signature(rec) do
    %{
      source: rec.fun.name,
      name: rec.name,
      layout: rec.fun.ret,
      param_layouts: Enum.map(rec.fun.params, fn {_n, lay} -> lay end),
      params: param_names(rec),
      export: rec.fun.export,
      head: rec.head
    }
  end

  defp mjs(stem, compiled) do
    h = helper_map()

    [
      "// generated by muro — do not edit",
      "// #{stem}",
      "// The proof stops at the run image.",
      runtime(h),
      Enum.map_join(compiled, "\n\n", & &1.text),
      ""
    ]
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n\n")
  end

  defp runtime(h) do
    h = Map.new(h, fn {k, v} -> {Atom.to_string(k), v} end)

    """
    const #{h["mod"]} = { u8: 256n, u32: 4294967296n, u64: 18446744073709551616n, i64: 18446744073709551616n };
    const #{h["bits"]} = { u8: 8n, u32: 32n, u64: 64n, i64: 64n };
    const #{h["half"]} = 9223372036854775808n;

    function #{h["abort"]}() { throw new Error("Empty"); }
    function #{h["go"]}(f) { return { #{h["go"]}: f }; }
    function #{h["bounce"]}(start) {
      const stack = [];
      let v = start(stack);
      while (true) {
        if (typeof v === "object" && v !== null && typeof v.#{h["go"]} === "function") {
          v = v.#{h["go"]}();
          continue;
        }
        if (stack.length === 0) return v;
        const k = stack.pop();
        v = k(v);
      }
    }
    function #{h["suc"]}(n) { return n + 1n; }
    function #{h["pred"]}(n) { return n === 0n ? 0n : n - 1n; }
    export function #{h["data"]}(tag, ...fields) { return { tag: tag, fields: fields }; }
    function #{h["stream"]}(seed, env, step) { return { seed: seed, env: env, step: step }; }
    export function #{h["uncons"]}(s) {
      const #{h["pair"]} = s.step(s.env, s.seed);
      return [#{h["pair"]}[0], { seed: #{h["pair"]}[1], env: s.env, step: s.step }];
    }
    export function #{h["canon"]}(v) {
      if (typeof v === "bigint") return (v < 0n ? BigInt.asUintN(64, v) : v).toString();
      if (v === null) return "tt";
      if (typeof v === "boolean") return v ? "true" : "false";
      if (typeof v === "string") return v;
      if (typeof v === "function") return "fn";
      if (Array.isArray(v)) return "(" + v.map(#{h["canon"]}).join(",") + ")";
      if (v && typeof v === "object") {
        if (typeof v.tag === "string" && Array.isArray(v.fields)) {
          if (v.fields.length === 0) return v.tag;
          return v.tag + "(" + v.fields.map(#{h["canon"]}).join(",") + ")";
        }
        if (v.k === "none") return "none";
        if (v.k === "some") return "some(" + #{h["canon"]}(v.v) + ")";
        if (typeof v.step === "function") return "stream";
      }
      return "unknown";
    }
    function #{h["res"]}(k, n) {
      const m = #{h["mod"]}[k];
      let r = n % m;
      if (r < 0n) r += m;
      return r;
    }
    function #{h["add"]}(k, x, y) { return #{h["res"]}(k, #{h["res"]}(k, x) + #{h["res"]}(k, y)); }
    function #{h["sub"]}(k, x, y) {
      x = #{h["res"]}(k, x);
      y = #{h["res"]}(k, y);
      return #{h["res"]}(k, x + (#{h["mod"]}[k] - y));
    }
    function #{h["mul"]}(k, x, y) { return #{h["res"]}(k, #{h["res"]}(k, x) * #{h["res"]}(k, y)); }
    function #{h["band"]}(k, x, y) { return #{h["res"]}(k, #{h["res"]}(k, x) & #{h["res"]}(k, y)); }
    function #{h["bnot"]}(k, x) { return #{h["res"]}(k, #{h["mod"]}[k] - 1n - #{h["res"]}(k, x)); }
    function #{h["bor"]}(k, x, y) { return #{h["bnot"]}(k, #{h["band"]}(k, #{h["bnot"]}(k, x), #{h["bnot"]}(k, y))); }
    function #{h["bxor"]}(k, x, y) {
      return #{h["bor"]}(k, #{h["band"]}(k, x, #{h["bnot"]}(k, y)), #{h["band"]}(k, #{h["bnot"]}(k, x), y));
    }
    function #{h["eq"]}(k, x, y) { return #{h["res"]}(k, x) === #{h["res"]}(k, y); }
    function #{h["slt"]}(x, y) {
      const h = #{h["half"]};
      if (x < h && y < h) return x < y;
      if (x >= h && y >= h) return x < y;
      return x >= h;
    }
    function #{h["lt"]}(k, x, y) {
      x = #{h["res"]}(k, x);
      y = #{h["res"]}(k, y);
      return k === "i64" ? #{h["slt"]}(x, y) : x < y;
    }
    function #{h["le"]}(k, x, y) { return #{h["eq"]}(k, x, y) || #{h["lt"]}(k, x, y); }
    function #{h["pow2"]}(n) { return 1n << n; }
    function #{h["shl"]}(k, x, n) {
      x = #{h["res"]}(k, x);
      if (n < 0n || n >= #{h["bits"]}[k]) return 0n;
      return #{h["res"]}(k, x * #{h["pow2"]}(n));
    }
    function #{h["ashr"]}(x, n) {
      const u = #{h["mod"]}.u64;
      if (n >= 64n) return x < #{h["half"]} ? 0n : u - 1n;
      const q = x / #{h["pow2"]}(n);
      if (x < #{h["half"]}) return q;
      return (q + (u - #{h["pow2"]}(64n - n))) % u;
    }
    function #{h["shr"]}(k, x, n) {
      x = #{h["res"]}(k, x);
      if (n < 0n) return 0n;
      if (k === "i64") return #{h["ashr"]}(x, n);
      if (n >= #{h["bits"]}[k]) return 0n;
      return x / #{h["pow2"]}(n);
    }
    function #{h["toZ"]}(n) {
      n = #{h["res"]}("i64", n);
      return n < #{h["half"]} ? n : n - #{h["mod"]}.u64;
    }
    function #{h["fromZ"]}(z) { return z >= 0n ? z : z + #{h["mod"]}.u64; }
    function #{h["inRange"]}(z) { return z >= -#{h["half"]} && z <= #{h["half"]} - 1n; }
    function #{h["some"]}(v) { return { k: "some", v: v }; }
    function #{h["none"]}() { return { k: "none" }; }
    function #{h["cadd"]}(k, x, y) {
      if (k === "i64") {
        const z = #{h["toZ"]}(x) + #{h["toZ"]}(y);
        return #{h["inRange"]}(z) ? #{h["some"]}(#{h["fromZ"]}(z)) : #{h["none"]}();
      }
      const s = #{h["res"]}(k, x) + #{h["res"]}(k, y);
      return s < #{h["mod"]}[k] ? #{h["some"]}(s) : #{h["none"]}();
    }
    function #{h["csub"]}(k, x, y) {
      if (k === "i64") {
        const z = #{h["toZ"]}(x) - #{h["toZ"]}(y);
        return #{h["inRange"]}(z) ? #{h["some"]}(#{h["fromZ"]}(z)) : #{h["none"]}();
      }
      x = #{h["res"]}(k, x);
      y = #{h["res"]}(k, y);
      return y <= x ? #{h["some"]}(x - y) : #{h["none"]}();
    }
    function #{h["cmul"]}(k, x, y) {
      if (k === "i64") {
        const z = #{h["toZ"]}(x) * #{h["toZ"]}(y);
        return #{h["inRange"]}(z) ? #{h["some"]}(#{h["fromZ"]}(z)) : #{h["none"]}();
      }
      const s = #{h["res"]}(k, x) * #{h["res"]}(k, y);
      return s < #{h["mod"]}[k] ? #{h["some"]}(s) : #{h["none"]}();
    }
    function #{h["badDiv"]}(k, x, y) {
      y = #{h["res"]}(k, y);
      if (k === "i64") {
        x = #{h["res"]}(k, x);
        return y === 0n || (x === #{h["half"]} && y === #{h["mod"]}.u64 - 1n);
      }
      return y === 0n;
    }
    function #{h["negBits"]}(n) { return n === 0n ? 0n : #{h["mod"]}.u64 - n; }
    function #{h["absBits"]}(n) { return n < #{h["half"]} ? n : #{h["mod"]}.u64 - n; }
    function #{h["div"]}(k, x, y) {
      if (#{h["badDiv"]}(k, x, y)) return #{h["none"]}();
      if (k !== "i64") return #{h["some"]}(#{h["res"]}(k, x) / #{h["res"]}(k, y));
      x = #{h["res"]}(k, x);
      y = #{h["res"]}(k, y);
      const mag = #{h["absBits"]}(x) / #{h["absBits"]}(y);
      const neg = (x >= #{h["half"]}) !== (y >= #{h["half"]});
      return #{h["some"]}(neg ? #{h["negBits"]}(mag) : mag);
    }
    function #{h["rem"]}(k, x, y) {
      if (#{h["badDiv"]}(k, x, y)) return #{h["none"]}();
      if (k !== "i64") return #{h["some"]}(#{h["res"]}(k, x) % #{h["res"]}(k, y));
      x = #{h["res"]}(k, x);
      y = #{h["res"]}(k, y);
      const mag = #{h["absBits"]}(x) % #{h["absBits"]}(y);
      return #{h["some"]}(x >= #{h["half"]} ? #{h["negBits"]}(mag) : mag);
    }
    function #{h["of"]}(k, n) { return #{h["res"]}(k, n); }
    function #{h["ton"]}(k, x) { return #{h["res"]}(k, x); }
    function #{h["cast"]}(k, n) { return #{h["res"]}(k, n); }
    """
    |> String.trim()
  end

  defp dts(compiled, types, book) do
    h = helper_map()
    funs = compiled |> Enum.map(&dts_fun(&1, types)) |> Enum.reject(&is_nil/1)

    [
      "// generated by muro — do not edit",
      "// The proof stops at the run image. This is a host binding, not the book.",
      "// I64 at the host boundary is a signed bigint (BigInt.asIntN(64)).",
      "// -1n is I64 −1. The minimum is -(2n**63n).",
      "// Inside the module, word operations use the unsigned residue.",
      "// U8, U32, and U64 are unsigned (BigInt.asUintN).",
      "// Nat is a bigint. A host passes 4n, not 4.",
      dts_prelude(),
      dts_data(book, types),
      Enum.join(funs, "\n"),
      "export function #{h.data}(tag: string, ...fields: unknown[]): { readonly tag: string; readonly fields: readonly unknown[] };",
      "export function #{h.uncons}(s: Stream): readonly [unknown, Stream];",
      "export function #{h.canon}(value: unknown): string;",
      ""
    ]
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n\n")
  end

  defp dts_prelude do
    """
    export type Nat = bigint;
    export type Unit = null;
    export type U8 = bigint;
    export type U32 = bigint;
    export type U64 = bigint;
    export type I64 = bigint;
    export type WordBool = boolean;
    export type Atom = string;
    export type Opt<T> = { readonly k: "none" } | { readonly k: "some"; readonly v: T };
    export type Pair<A, B> = readonly [A, B];
    export type Stream = {
      readonly seed: unknown;
      readonly env: readonly unknown[];
      readonly step: (env: readonly unknown[], seed: unknown) => readonly [unknown, unknown];
    };
    """
    |> String.trim()
  end

  defp dts_fun(rec, types) do
    if generated?(rec) or not rec.fun.export do
      nil
    else
      params =
        Enum.map_join(rec.params, ", ", fn {_src, rn, lay} ->
          "#{rn}: #{render_lay(lay, types)}"
        end)

      "export function #{rec.name}(#{params}): #{render_lay(rec.fun.ret, types)};"
    end
  end

  defp dts_data(book, types) do
    book
    |> Enum.filter(&(Map.get(&1, :kind) == :data))
    |> Enum.map_join("\n\n", fn d ->
      name = Map.fetch!(types, d.name)

      if d.ctors == [] do
        "export type #{name} = never;"
      else
        ctors =
          Enum.map_join(d.ctors, "\n", fn c ->
            lays = field_lays(book, c.type)
            fields = Enum.map_join(lays, ", ", &render_lay(&1, types))
            "  | { readonly tag: #{js_str(c.name)}; readonly fields: readonly [#{fields}] }"
          end)

        "export type #{name} =\n#{ctors};"
      end
    end)
  end

  defp data_types(book) do
    book
    |> Enum.filter(&(Map.get(&1, :kind) == :data))
    |> Enum.reduce({%{}, MapSet.new()}, fn d, {map, used} ->
      {rn, used} = Name.claim(type_spell(d.name), used)
      {Map.put(map, d.name, rn), used}
    end)
    |> elem(0)
  end

  defp field_lays(book, ty), do: field_lays(book, ty, [])
  defp field_lays(book, {:pi, :erased, _, _, b}, acc), do: field_lays(book, b, acc)

  defp field_lays(book, {:pi, _q, a, _, b}, acc) do
    field_lays(book, b, acc ++ [rough_lay(book, a)])
  end

  defp field_lays(_book, _ty, acc), do: acc

  defp rough_lay(_book, :nat), do: :nat
  defp rough_lay(_book, :unit), do: :unit
  defp rough_lay(_book, :i64), do: :i64
  defp rough_lay(_book, :atom), do: {:data, "Atom"}
  defp rough_lay(_book, {:word, {:ty, k}, []}) when k in [:u8, :u32, :u64], do: k
  defp rough_lay(_book, {:word, :bool, []}), do: :wbool
  defp rough_lay(_book, {:word, {:optk, k}, []}), do: {:opt, rough_word(k)}
  defp rough_lay(book, {:var, name}), do: data_or_opaque(book, name)
  defp rough_lay(book, {:def, name}), do: data_or_opaque(book, name)
  defp rough_lay(book, {:app, f, _}), do: rough_lay(book, f)
  defp rough_lay(book, {:ann, e, _}), do: rough_lay(book, e)
  defp rough_lay(book, {:rwt, _, _, _, t}), do: rough_lay(book, t)
  defp rough_lay(book, {:rwt, _, _, t}), do: rough_lay(book, t)
  defp rough_lay(book, {:prod, a, b}), do: {:pair, rough_lay(book, a), rough_lay(book, b)}
  defp rough_lay(book, {:pi, :erased, _, _, b}), do: rough_lay(book, b)
  defp rough_lay(book, {:pi, _, a, _, b}), do: {:fn, rough_lay(book, a), rough_lay(book, b)}
  defp rough_lay(book, {:stream, a}), do: {:stream, rough_lay(book, a)}
  defp rough_lay(_book, _), do: :opaque

  defp data_or_opaque(book, name) do
    if Enum.any?(book, &(Map.get(&1, :kind) == :data and &1.name == name)) do
      {:data, name}
    else
      :opaque
    end
  end

  defp rough_word(k) when k in [:u8, :u32, :u64, :i64], do: k
  defp rough_word(_), do: :opaque

  defp render_lay(lay, types), do: render_lay(lay, types, false)

  defp render_lay(:nat, _types, _nested), do: "Nat"
  defp render_lay(:unit, _types, _nested), do: "Unit"
  defp render_lay(:u8, _types, _nested), do: "U8"
  defp render_lay(:u32, _types, _nested), do: "U32"
  defp render_lay(:u64, _types, _nested), do: "U64"
  defp render_lay(:i64, _types, _nested), do: "I64"
  defp render_lay(:wbool, _types, _nested), do: "WordBool"
  defp render_lay(:opaque, _types, _nested), do: "unknown"
  defp render_lay(:never, _types, _nested), do: "never"
  defp render_lay({:data, "Atom"}, _types, _nested), do: "Atom"

  defp render_lay({:data, name}, types, _nested) do
    Map.get(types, name, "unknown")
  end

  defp render_lay({:pair, a, b}, types, _nested) do
    "Pair<#{render_lay(a, types, true)}, #{render_lay(b, types, true)}>"
  end

  defp render_lay({:opt, a}, types, _nested), do: "Opt<#{render_lay(a, types, true)}>"
  defp render_lay({:stream, _}, _types, _nested), do: "Stream"

  defp render_lay({:fn, a, b}, types, nested) do
    text = "(arg: #{render_lay(a, types, true)}) => #{render_lay(b, types, true)}"
    if nested, do: "(" <> text <> ")", else: text
  end

  defp render_lay(_lay, _types, _nested), do: "unknown"
end

defmodule Muro.IRDiff do
  import Bitwise, only: [<<<: 2]
  @moduledoc false
  # The differential harness of `Muro.IR.Eval`.
  #
  # For a checked book and one of its runs, generate closed arguments
  # from the run's type, apply the run to them on both sides, and compare
  #
  #     normalize(run args) == Eval(elaborate) == Eval(Share(elaborate))
  #                         == Eval(elaborate(closures: true))
  #
  # and each of those images in A-normal form (`Muro.IR.Anf`) beside it:
  # `anf`, `anf_shared`, and `anf_closures`, and the image C emits, the
  # shared image with every byte fold a loop (`Muro.IR.Loop`): `loop`.
  #
  # `Muro.Check.normalize/3` is the reference. A reference that does not
  # reach a closed first-order value (a λ, a stuck term, an `abort`, out
  # of fuel) is not compared; every such case is counted by reason.
  # A stream result is compared on its first `@heads` heads.
  #
  # Inputs are generated from the named Π telescope, not the IR layout,
  # so a `List Bool` argument holds `Bool`s. Generation is seeded by the
  # file and the run name and draws from `:rand` with an explicit state,
  # so every run of the suite sees the same inputs.

  alias Muro.{Ast, Check, IR, Load, Prelude}
  alias Muro.IR.{Anf, Eval, Loop, Share}
  alias Muro.IR.Eval.Ref

  @heads 3
  @strings ["", "a", "hello", "é", "e\u0301", "\u{1F44B}", "a\nb", "GET", "a b:c"]

  @bytes [
    "",
    "GET / HTTP/1.1\r\nHost: a\r\n\r\n",
    "a",
    "ab\ncd",
    <<0, 255, 10, 13>>,
    "POST /x HTTP/1.1\r\nContent-Length: 3\r\n\r\nabc",
    "key: value\r\n"
  ]
  @ref_fuel 4_000
  @eval_fuel 100_000
  @ref_ms 15_000

  # -- a book ----------------------------------------------------------------

  @doc "Load `path` and build every image. `{:ok, ctx}` or `{:skip, reason}`."
  def load(path) do
    case Load.file(path) do
      {:ok, book} -> prepare(path, book)
      {:error, _} -> {:skip, :does_not_check}
    end
  end

  # Each run is elaborated with only the runs it reaches, so one run the
  # image refuses does not take the rest of its book with it. The image
  # is then every run that elaborates on its own, in one book.
  #
  # `roots:` keeps only the runs those runs reach.
  def prepare(path, book, opts \\ []) do
    emit = Prelude.for_emit(book)

    emit =
      case Keyword.get(opts, :roots) do
        nil -> emit
        roots -> restrict(emit, closure(roots, reach_map(emit), MapSet.new()))
      end

    scope = Prelude.for_check(book)

    case Ast.book_to_db(scope, params: :open) do
      {:ok, db} ->
        {plain, plain_out} = image(emit, [])
        {closures, clos_out} = image(emit, closures: true)

        if plain == nil and closures == nil do
          {:skip, {:no_image, plain_out |> Map.values() |> Enum.uniq()}}
        else
          {:ok,
           with_anf(%{
             path: path,
             book: emit,
             db: db,
             atoms: Ast.atoms(emit),
             plain: plain,
             shared: plain && Share.funs(plain),
             closures: closures,
             refused: %{plain: plain_out, closures: clos_out}
           })}
        end

      {:error, _} ->
        {:skip, :no_db}
    end
  end

  @doc "Every image of the whole book at once, for a book that elaborates whole."
  def prepare_whole(path, book) do
    emit = Prelude.for_emit(book)
    {:ok, db} = Ast.book_to_db(Prelude.for_check(book), params: :open)
    {:ok, plain} = IR.elaborate(emit)
    {:ok, closures} = IR.elaborate(emit, closures: true)

    with_anf(%{
      path: path,
      book: emit,
      db: db,
      atoms: Ast.atoms(emit),
      plain: plain,
      shared: Share.funs(plain),
      closures: closures,
      refused: %{plain: %{}, closures: %{}}
    })
  end

  # The A-normal form of each image, `nil` where the image is.
  @anf_of [anf: :plain, anf_shared: :shared, anf_closures: :closures]

  @doc "The images `compare/3` runs, in order."
  def image_keys, do: [:plain, :shared, :closures | Keyword.keys(@anf_of)] ++ [:loop]

  @doc """
  Rebuilds the A-normal images of `ctx` and the loop image from the
  images they come from.
  """
  def with_anf(ctx) do
    ctx =
      Enum.reduce(@anf_of, ctx, fn {k, src}, ctx ->
        funs = Map.fetch!(ctx, src)
        opts = [book: ctx.book, closures: src == :closures]
        Map.put(ctx, k, funs && Anf.funs(funs, opts))
      end)

    Map.put(ctx, :loop, ctx.shared && Loop.funs(ctx.shared, book: ctx.book))
  end

  def reach_map(emit) do
    names = MapSet.new(for d <- emit, run?(d), do: d.name)
    Map.new(for d <- emit, run?(d), do: {d.name, mentioned(d.body, names)})
  end

  defp image(emit, opts) do
    runs = for d <- emit, run?(d), do: d.name
    reach = reach_map(emit)

    {ok, refused} =
      Enum.reduce(runs, {[], %{}}, fn r, {ok, refused} ->
        keep = closure([r], reach, MapSet.new())

        case IR.elaborate(restrict(emit, keep), opts) do
          {:ok, _} -> {[r | ok], refused}
          {:error, reason} -> {ok, Map.put(refused, r, reason)}
        end
      end)

    keep = closure(ok, reach, MapSet.new())

    case ok do
      [] ->
        {nil, refused}

      _ ->
        {:ok, funs} = IR.elaborate(restrict(emit, keep), opts)
        {funs, refused}
    end
  end

  defp run?(d), do: Map.get(d, :kind, :def) != :data and Map.get(d, :mode) == :run

  def restrict(emit, keep), do: Enum.filter(emit, &(not run?(&1) or &1.name in keep))

  def closure([], _reach, seen), do: seen

  def closure([r | rs], reach, seen) do
    if MapSet.member?(seen, r) do
      closure(rs, reach, seen)
    else
      closure(MapSet.to_list(Map.get(reach, r, MapSet.new())) ++ rs, reach, MapSet.put(seen, r))
    end
  end

  defp mentioned({tag, n}, names) when tag in [:var, :def] and is_binary(n),
    do: if(MapSet.member?(names, n), do: MapSet.new([n]), else: MapSet.new())

  defp mentioned(t, names) when is_tuple(t), do: mentioned(Tuple.to_list(t), names)

  defp mentioned(t, names) when is_list(t),
    do: Enum.reduce(t, MapSet.new(), &MapSet.union(&2, mentioned(&1, names)))

  defp mentioned(_t, _names), do: MapSet.new()

  @doc "Every source run either image holds."
  def all_runs(ctx) do
    [ctx.plain, ctx.closures]
    |> Enum.reject(&is_nil/1)
    |> Enum.flat_map(&runs/1)
    |> Enum.uniq()
  end

  @doc "The source runs of an image: every function that is not a step."
  def runs(funs), do: for(f <- funs, not Map.get(f, :generated, false), do: f.name)

  # -- one run ---------------------------------------------------------------

  @doc """
  Compare `name` on `count` generated inputs. Returns a list of
  `{:agree, input}`, `{:skip, reason}`, or `{:mismatch, detail}`.
  """
  def check_run(ctx, name, count) do
    case find_def(ctx.book, name) do
      nil ->
        [{:skip, :no_def}]

      d ->
        st = seed({ctx.path, name})

        {cases, _} =
          Enum.map_reduce(1..count, st, fn i, st ->
            case gen_args(ctx, d, i, st) do
              {:ok, args, st} -> {compare(ctx, name, args), st}
              {:skip, reason, st} -> {{:skip, reason}, st}
            end
          end)

        cases
    end
  end

  @doc """
  Compare `name` on every combination of the edge values of its live
  parameter types. Each live parameter must have edges (`edges/2`). A Π
  the image drops (an erased quantity on the Π or its λ, or a `Type`)
  is one filler argument `{term, :gone}`, as in `gen_args/4`.
  """
  def check_edges(ctx, name) do
    d = find_def(ctx.book, name)

    ctx
    |> edge_lists(d.type, Map.get(d, :body))
    |> product()
    |> Enum.map(&compare(ctx, name, &1))
  end

  @doc "Per Π of `type`, its argument choices `[{term, value | :gone}]`."
  def edge_lists(ctx, {:pi, q, a, _x, b}, body) do
    {q2, body2} =
      case body do
        {:lam, q2, _dom, _n, inner} -> {q2, inner}
        _ -> {nil, nil}
      end

    choices =
      cond do
        a == :typ ->
          [{:nat, :gone}]

        IR.erased_qty?(q) or (q2 != nil and IR.erased_qty?(q2)) ->
          case try_gen(ctx, a, 1, seed({:edge_filler, a})) do
            {:ok, v, _st} -> [{to_term!(ctx, v), :gone}]
            :no -> [{:rfl, :gone}]
          end

        true ->
          Enum.map(edges(ctx, a), &{to_term!(ctx, &1), &1})
      end

    [choices | edge_lists(ctx, b, body2)]
  end

  def edge_lists(_ctx, _type, _body), do: []

  defp product([]), do: [[]]
  defp product([xs | rest]), do: for(x <- xs, tail <- product(rest), do: [x | tail])

  @doc "The edge values of a first-order type."
  def edges(_ctx, :nat), do: Enum.map([0, 1, 2, 7, 8, 31, 32, 63, 64, 65], &{:nat, &1})
  def edges(_ctx, :i64), do: Enum.map(word_edges(:i64), &{:word, :i64, &1})
  def edges(_ctx, {:word, {:ty, k}, []}), do: Enum.map(word_edges(k), &{:word, k, &1})
  def edges(_ctx, {:word, :bool, []}), do: [true, false]
  def edges(_ctx, :string), do: Enum.map(@strings, &{:str, &1})
  def edges(_ctx, t) when t in [:bytes, :slice], do: Enum.map(@bytes, &{:bytes, &1})

  def edges(ctx, {:word, :opt, [a]}),
    do: [:none | ctx |> edges(a) |> Enum.take(4) |> Enum.map(&{:some, &1})]

  def edges(ctx, {:word, {:optk, k}, []}), do: edges(ctx, {:word, :opt, [Muro.Word.word_ty(k)]})

  def edges(ctx, {:prod, a, b}),
    do: for(x <- Enum.take(edges(ctx, a), 4), y <- Enum.take(edges(ctx, b), 4), do: {:pair, x, y})

  @doc "Compare `name` on the given argument list `[{term, value | :gone}]`."
  def compare(ctx, name, args) do
    terms = Enum.map(args, &elem(&1, 0))
    vals = for {_t, v} <- args, v != :gone, do: v
    ast = Enum.reduce(terms, {:def, name}, &{:app, &2, &1})

    images =
      image_keys()
      |> Enum.map(&{&1, Map.get(ctx, &1)})
      |> Enum.reject(fn {_k, funs} -> funs == nil end)
      |> Enum.filter(fn {_k, funs} ->
        Enum.any?(funs, &(&1.name == name and arity_ok?(&1, vals)))
      end)

    fuel = Map.get(ctx, :eval_fuel, @eval_fuel)
    got = for {k, funs} <- images, do: {k, observe(funs, name, vals, fuel)}

    verdict(name, vals, got, fn -> reference(ctx, ast) end)
  end

  @doc """
  The verdict on the results `got` (`[{image, result}]`) of every image.
  `ref` is called for the reference only when some image did not run
  out of fuel.

  Eval spends fuel on every call and the closure image on every
  application, so one image may run out where another stops. Every image
  is observed. Results that did stop must agree with one another and
  with the reference. A closure an A-normal image returns holds the
  same code under other binder names, so closures agree by shape. An input where every image ran out of fuel is not
  compared, and the reference is not asked for it. An input where some
  did, and the rest agree, is a skip.
  """
  def verdict(name, vals, got, ref) do
    oom = {:error, :out_of_fuel}
    done = for {k, r} <- got, r != oom, do: {k, r}

    cond do
      got == [] ->
        {:mismatch, %{run: name, args: vals, got: :no_image}}

      done == [] ->
        {:skip, :eval_out_of_fuel}

      length(Enum.uniq(Enum.map(done, &erase_closures(elem(&1, 1))))) > 1 ->
        {:mismatch, %{run: name, args: vals, ref: :not_asked, got: got}}

      true ->
        case ref.() do
          {:ok, r} ->
            cond do
              Enum.any?(done, fn {_k, v} -> v != {:ok, r} end) ->
                {:mismatch, %{run: name, args: vals, ref: r, got: got}}

              length(done) < length(got) ->
                {:skip, :eval_out_of_fuel}

              true ->
                {:agree, Keyword.keys(got)}
            end

          {:skip, reason} ->
            {:skip, reason}
        end
    end
  end

  # Only the closures image and its A-normal form return a closure.
  defp erase_closures({:clo, _env, _x, _body}), do: :closure

  defp erase_closures(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.map(&erase_closures/1) |> List.to_tuple()

  defp erase_closures(t) when is_list(t), do: Enum.map(t, &erase_closures/1)
  defp erase_closures(t), do: t

  defp arity_ok?(fun, vals), do: length(fun.params) == length(vals)

  # The first-order value, or the first heads of a stream.
  def reference(ctx, ast) do
    task = Task.async(fn -> reference_now(ctx, ast) end)

    case Task.yield(task, @ref_ms) || Task.shutdown(task, :brutal_kill) do
      {:ok, r} -> r
      _ -> {:skip, :ref_timeout}
    end
  end

  defp reference_now(ctx, ast) do
    case Check.normalize(ctx.db, ast, Map.get(ctx, :ref_fuel, @ref_fuel)) do
      {:ok, {:unf, _, _} = s} -> ref_heads(ctx, s, @heads, [])
      {:ok, nf} -> ref_value(ctx, nf)
      {:error, "out of fuel" <> _} -> {:skip, :ref_out_of_fuel}
      {:error, _} -> {:skip, :ref_error}
    end
  end

  defp ref_value(ctx, nf) do
    case Ref.of_normal(ctx.book, nf) do
      {:ok, v} -> {:ok, v}
      {:error, {:not_value, _}} -> {:skip, ref_shape(nf)}
    end
  end

  defp ref_shape({:lam, _, _, _, _}), do: :ref_function
  defp ref_shape(_), do: :ref_stuck

  defp ref_heads(_ctx, _s, 0, acc), do: {:ok, {:heads, Enum.reverse(acc)}}

  defp ref_heads(ctx, s, n, acc) do
    case Check.normalize(ctx.db, {:ucons, s}, Map.get(ctx, :ref_fuel, @ref_fuel)) do
      {:ok, {:pair, h, rest}} ->
        with {:ok, hv} <- ref_value(ctx, h), do: ref_heads(ctx, rest, n - 1, [hv | acc])

      {:ok, _} ->
        {:skip, :ref_stuck}

      {:error, _} ->
        {:skip, :ref_out_of_fuel}
    end
  end

  def observe(funs, name, vals, fuel \\ @eval_fuel) do
    case Eval.call(funs, name, vals, fuel: fuel) do
      {:ok, {:stream, _, _, _} = s} ->
        case Eval.take(funs, s, @heads, fuel: fuel) do
          {:ok, hs} -> {:ok, {:heads, hs}}
          err -> err
        end

      other ->
        other
    end
  end

  # -- generated arguments ---------------------------------------------------

  def find_def(book, name) do
    Enum.find(book, fn d ->
      Map.get(d, :kind, :def) not in [:data, :relay, :repr] and Map.get(d, :name) == name and
        Map.get(d, :mode) == :run and Map.has_key?(d, :type)
    end)
  end

  @doc """
  One argument per Π of the run's type, as `{term, value}`; a Π the image
  drops is `{term, :gone}`. The first case uses small fixed values.
  """
  def gen_args(ctx, d, i, st) do
    gen_tel(ctx, d.type, Map.get(d, :body), %{}, i, st, [])
  catch
    {:no_gen, reason, st} -> {:skip, {:no_gen, reason}, st}
  end

  defp gen_tel(ctx, {:pi, q, a, x, b}, body, sub, i, st, acc) do
    {q2, body2} =
      case body do
        {:lam, q2, _dom, _n, inner} -> {q2, inner}
        _ -> {nil, nil}
      end

    a = subst(a, sub)
    gone? = IR.erased_qty?(q) or (q2 != nil and IR.erased_qty?(q2))

    {term, val, st} =
      cond do
        a == :typ ->
          {:nat, nil, st}

        gone? ->
          case try_gen(ctx, a, i, st) do
            {:ok, v, st} -> {to_term!(ctx, v), nil, st}
            :no -> {:rfl, nil, st}
          end

        true ->
          {v, st} = gen(ctx, a, 3, i, st)
          {to_term!(ctx, v), unfun(v), st}
      end

    sub = if is_binary(x), do: Map.put(sub, x, if(a == :typ, do: :nat, else: term)), else: sub
    entry = {term, if(gone?, do: :gone, else: val)}
    gen_tel(ctx, b, body2, sub, i, st, [entry | acc])
  end

  defp gen_tel(_ctx, _ty, _body, _sub, _i, st, acc), do: {:ok, Enum.reverse(acc), st}

  defp try_gen(ctx, a, i, st) do
    {v, st} = gen(ctx, a, 2, i, st)
    {:ok, v, st}
  catch
    {:no_gen, _, _} -> :no
  end

  def term!(ctx, v), do: to_term!(ctx, v)

  defp to_term!(_ctx, {:fun, name, _clo}) when is_binary(name), do: {:def, name}

  defp to_term!(_ctx, {:fun, named, _clo}) do
    {:ok, t} = Ast.to_db(named)
    t
  end

  defp to_term!(ctx, v) do
    {:ok, t} = Ref.to_term(ctx.book, v, :rfl)
    t
  end

  defp unfun({:fun, _name, clo}), do: clo
  defp unfun(v), do: v

  # Fixed values first, then random ones.
  defp gen(_ctx, :nat, _depth, i, st) do
    if i <= 3, do: {{:nat, i - 1}, st}, else: pick(st, 0..6, &{:nat, &1})
  end

  defp gen(_ctx, :unit, _d, _i, st), do: {:tt, st}
  defp gen(_ctx, :string, _d, i, st), do: gen_string(i, st)
  defp gen(_ctx, t, _d, i, st) when t in [:bytes, :slice], do: gen_bytes(i, st)
  defp gen(_ctx, :i64, _d, i, st), do: gen_word(:i64, i, st)
  defp gen(_ctx, {:word, {:ty, k}, []}, _d, i, st), do: gen_word(k, i, st)

  defp gen(_ctx, {:word, :bool, []}, _d, i, st) do
    if i <= 2, do: {i == 1, st}, else: pick(st, [true, false], & &1)
  end

  defp gen(ctx, {:word, {:optk, k}, []}, d, i, st),
    do: gen(ctx, {:word, :opt, [Muro.Word.word_ty(k)]}, d, i, st)

  defp gen(ctx, {:word, :opt, [a]}, d, i, st) do
    {n, st} = uniform(st, 4)

    if n == 1 do
      {:none, st}
    else
      {v, st} = gen(ctx, a, d, i + n, st)
      {{:some, v}, st}
    end
  end

  defp gen(ctx, {:prod, a, b}, d, i, st) do
    {va, st} = gen(ctx, a, d, i, st)
    {vb, st} = gen(ctx, b, d, i + 1, st)
    {{:pair, va, vb}, st}
  end

  defp gen(%{atoms: []}, :atom, _d, _i, st), do: throw({:no_gen, :atom, st})
  defp gen(ctx, :atom, _d, _i, st), do: pick(st, ctx.atoms, &{:con, "Atom", &1, []})

  defp gen(ctx, {:ann, t, _}, d, i, st), do: gen(ctx, t, d, i, st)

  # A function argument is a run of the book with the same type, as a
  # closure that calls it. Only the closure image takes one.
  #
  # Without one, or on every other draw, the argument is a λ written
  # here: the identity on `T → T`, `suc` on `Nat → Nat`, otherwise a
  # constant function of a generated result.
  defp gen(ctx, {:pi, _, _, _, _} = t, d, i, st) do
    if ctx.closures == nil or fn_key(t) == nil, do: throw({:no_gen, :pi, st})

    {n, st} = uniform(st, 2)

    case {fn_runs(ctx, t), n} do
      {[_ | _] = runs, 1} -> pick(st, runs, &fn_value(ctx, &1))
      _ -> gen_lam(ctx, t, d, i, st)
    end
  end

  defp gen(ctx, t, d, i, st) do
    {head, args} = spine(t, [])

    case head do
      {tag, name} when tag in [:var, :def] ->
        case {find_data(ctx.book, name), find_alias(ctx.book, name)} do
          {nil, nil} -> {{:nat, rem(i, 4)}, st}
          {nil, body} -> gen(ctx, beta(body, args), d, i, st)
          {data, _} -> gen_data(ctx, data, args, d, i, st)
        end

      _ ->
        throw({:no_gen, shape(t), st})
    end
  end

  defp fn_runs(ctx, t) do
    key = fn_key(t)

    if key == nil or ctx.closures == nil do
      []
    else
      for d <- ctx.book,
          Map.get(d, :mode) == :run,
          Map.get(d, :kind, :def) != :data,
          Map.has_key?(d, :type),
          fn_key(d.type) == key,
          Enum.any?(ctx.closures, &(&1.name == d.name and not Map.get(&1, :generated, false))),
          do: d
    end
  end

  # A non-dependent Π with no erased binder, binder names and grades
  # dropped.
  defp fn_key({:pi, q, a, _x, b}) do
    if IR.erased_qty?(q) do
      nil
    else
      with ka when ka != nil <- fn_key_dom(a), kb when kb != nil <- fn_key(b), do: {:pi, ka, kb}
    end
  end

  defp fn_key(t), do: fn_key_dom(t)

  defp fn_key_dom({:pi, _, _, _, _} = t), do: fn_key(t)
  defp fn_key_dom(t), do: t

  defp fn_value(_ctx, d) do
    names = arity_names(d.type, 0)
    vars = Enum.map(names, &{:var, &1})
    call = {:call, d.name, vars}
    [first | rest] = names
    body = Enum.reduce(Enum.reverse(rest), call, fn x, acc -> {:lam, x, :opaque, :reuse, acc} end)
    {:fun, d.name, {:clo, %{}, first, body}}
  end

  defp gen_lam(ctx, {:pi, _q, a, _x, b} = t, d, i, st) do
    x = "x#{d}"

    {body_tm, body_ir, st} =
      cond do
        a == b and a == :nat and rem(i, 2) == 0 ->
          {{:su, {:var, x}}, {:su, {:var, x}}, st}

        a == b ->
          {{:var, x}, {:var, x}, st}

        match?({:pi, _, _, _, _}, b) ->
          {inner, st} = gen_lam(ctx, b, d - 1, i, st)
          {:fun, named, {:clo, _, y, ibody}} = inner
          {:ok, tm} = {:ok, named}
          {tm, {:lam, y, :opaque, :reuse, ibody}, st}

        true ->
          {v, st} = gen(ctx, b, 1, i, st)
          if match?({:fun, _, _}, v), do: throw({:no_gen, :pi, st})
          {to_term!(ctx, v), ir_term(v), st}
      end

    _ = t
    {{:fun, {:lam, :reuse, a, x, body_tm}, {:clo, %{}, x, body_ir}}, st}
  end

  # The IR term of a first-order value.
  defp ir_term({:nat, n}), do: {:nat, n}
  defp ir_term(:tt), do: :tt
  defp ir_term({:word, k, n}), do: {:wrd, k, {:lit, k, n}, []}
  defp ir_term(b) when is_boolean(b), do: {:wrd, :u8, b, []}
  defp ir_term({:some, v}), do: {:wrd, :u8, :some, [ir_term(v)]}
  defp ir_term(:none), do: {:wrd, :u8, :none, []}
  defp ir_term({:str, b}), do: {:str, b}
  defp ir_term({:bytes, b}), do: {:byt, b}
  defp ir_term({:pair, a, b}), do: {:pair, ir_term(a), ir_term(b)}
  defp ir_term({:con, d, c, fs}), do: {:con, d, c, Enum.map(fs, &ir_term/1)}

  defp arity_names({:pi, _, _, _, b}, k), do: ["arg#{k}" | arity_names(b, k + 1)]
  defp arity_names(_, _), do: []

  defp shape(t) when is_tuple(t), do: elem(t, 0)
  defp shape(t), do: t

  defp gen_data(ctx, data, args, d, i, st) do
    params = for {_q, x, _a} <- Map.get(data, :params, []), do: x
    sub = params |> Enum.zip(args) |> Map.new()
    ctors = data.ctors

    # At depth 0, only constructors with no field of this data.
    pool =
      if d <= 0 do
        case Enum.reject(ctors, &recursive?(&1, data.name)) do
          [] -> ctors
          base -> base
        end
      else
        ctors
      end

    {c, st} = pick(st, pool, & &1)
    {fields, st} = gen_fields(ctx, c.type, sub, d - 1, i, st, [])
    {{:con, data.name, c.name, fields}, st}
  end

  defp gen_fields(ctx, {:pi, q, a, x, b}, sub, d, i, st, acc) do
    if IR.erased_qty?(q) do
      gen_fields(ctx, b, sub, d, i, st, acc)
    else
      {v, st} = gen(ctx, subst(a, sub), d, i + length(acc), st)
      if match?({:fun, _, _}, v), do: throw({:no_gen, :pi_field, st})
      sub = if is_binary(x), do: Map.put(sub, x, to_term!(ctx, v)), else: sub
      gen_fields(ctx, b, sub, d, i, st, [v | acc])
    end
  end

  defp gen_fields(_ctx, _t, _sub, _d, _i, st, acc), do: {Enum.reverse(acc), st}

  # A field of this data. The result type always names it.
  defp recursive?(c, name), do: c.type |> field_types() |> Enum.any?(&mentions?(&1, name))

  defp field_types({:pi, _q, a, _x, b}), do: [a | field_types(b)]
  defp field_types(_), do: []

  defp mentions?({:var, name}, name), do: true
  defp mentions?({:def, name}, name), do: true

  defp mentions?(t, name) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.any?(&mentions?(&1, name))

  defp mentions?(t, name) when is_list(t), do: Enum.any?(t, &mentions?(&1, name))
  defp mentions?(_t, _name), do: false

  # A type alias: a definition of a type, unfolded with its arguments.
  defp find_alias(book, name) do
    case Enum.find(book, &(Map.get(&1, :kind, :def) == :def and Map.get(&1, :name) == name)) do
      %{type: ty, body: body} -> if returns_type?(ty), do: body
      _ -> nil
    end
  end

  defp returns_type?(:typ), do: true
  defp returns_type?({:pi, _, _, _, b}), do: returns_type?(b)
  defp returns_type?(_), do: false

  defp beta({:lam, _q, _a, x, body}, [arg | rest]), do: beta(subst(body, %{x => arg}), rest)
  defp beta(body, []), do: body
  defp beta(body, args), do: Enum.reduce(args, body, &{:app, &2, &1})

  defp find_data(book, name),
    do: Enum.find(book, &(Map.get(&1, :kind) == :data and &1.name == name))

  defp spine({:app, f, a}, acc), do: spine(f, [a | acc])
  defp spine(h, acc), do: {h, acc}

  # Named substitution of type arguments. A binder that shadows a name
  # stops it.
  defp subst({:var, x} = t, sub), do: Map.get(sub, x, t)

  defp subst({tag, q, a, x, b}, sub) when tag in [:pi, :lam],
    do: {tag, q, subst(a, sub), x, subst(b, Map.delete(sub, x))}

  defp subst(t, sub) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.map(&subst(&1, sub)) |> List.to_tuple()

  defp subst(t, sub) when is_list(t), do: Enum.map(t, &subst(&1, sub))
  defp subst(t, _sub), do: t

  @word_edges %{
    u8: [0, 1, 2, 7, 10, 13, 32, 58, 127, 128, 254, 255],
    u32: [0, 1, 2, 255, 256, 65_535, 2_147_483_647, 2_147_483_648, 4_294_967_295],
    u64: [
      0,
      1,
      2,
      3,
      4,
      6,
      255,
      16_384,
      9_223_372_036_854_775_807,
      9_223_372_036_854_775_808,
      18_446_744_073_709_551_615
    ],
    i64: [
      0,
      1,
      2,
      18_446_744_073_709_551_615,
      9_223_372_036_854_775_807,
      9_223_372_036_854_775_808,
      18_446_744_073_709_551_614
    ]
  }

  def word_edges(k), do: Map.fetch!(@word_edges, k)

  defp gen_word(k, i, st) do
    edges = word_edges(k)

    cond do
      i <= 3 ->
        {{:word, k, Enum.at(edges, i - 1)}, st}

      true ->
        {n, st} = uniform(st, 3)

        case n do
          1 ->
            {w, st} = uniform(st, Muro.Word.modulus(k))
            {{:word, k, w - 1}, st}

          _ ->
            pick(st, edges, &{:word, k, &1})
        end
    end
  end

  defp gen_string(i, st) do
    if i <= length(@strings),
      do: {{:str, Enum.at(@strings, i - 1)}, st},
      else: pick(st, @strings, &{:str, &1})
  end

  defp gen_bytes(i, st) do
    if i <= length(@bytes) do
      {{:bytes, Enum.at(@bytes, i - 1)}, st}
    else
      {len, st} = uniform(st, 13)
      len = len - 1

      {bin, st} =
        Enum.reduce(List.duplicate(nil, len), {<<>>, st}, fn _, {acc, st} ->
          {b, st} = pick(st, [?a, ?\s, ?:, ?\r, ?\n, ?/, ?0, 0, 255], & &1)
          {acc <> <<b>>, st}
        end)

      {{:bytes, bin}, st}
    end
  end

  # -- seeded randomness -----------------------------------------------------

  def seed(term) do
    h = :erlang.phash2(term, 1 <<< 30)
    :rand.seed_s(:exsss, {h, h + 1, h + 2})
  end

  defp uniform(st, n) do
    {x, st} = :rand.uniform_s(n, st)
    {x, st}
  end

  defp pick(st, enum, f) do
    list = Enum.to_list(enum)
    {x, st} = :rand.uniform_s(length(list), st)
    {f.(Enum.at(list, x - 1)), st}
  end
end

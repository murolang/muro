defmodule Muro.IR.Anf do
  @moduledoc """
  A-normal form of a `Muro.IR` image.

  `funs/2` rewrites every function so that each operand is atomic: the
  arguments of a call, a constructor, a word operation, a pair, `su`,
  `uncons`, a closure application, a string or bytes primitive, the
  captures, seed, start, and input of a stream or a fold, the scrutinee
  of a `match`, and the pair of a `letp`. An atom is a variable or a
  literal: `:ze`, `:tt`, `{:nat, n}`, `{:str, s}`, `{:byt, b}`, a
  nullary word (`{:wrd, k, op, []}`), or a nullary constructor.

  A non-atomic operand is bound by a fresh `let` just before its use,
  operands left to right in the order `Muro.IR.Eval` evaluates them
  (a stream's captures before its seed; a fold's captures, then its
  start, then its input), so evaluation order, `abort`, and fuel are
  unchanged. A `let` whose value is itself a `let` or `letp` is
  flattened. A `match` in operand position is bound by a `let`, so
  the continuation is never copied into its arms.

  The grammar of the result:

      tail ::= comp | let x lay g comp tail | let x :erased g :ze tail
             | letp a b atom tail
      comp ::= atom | abort | op(atom, ...) | lam x lay g tail
             | match atom [arm(tail)]

  Every binder of a function is unique after this pass. A source binder
  keeps its name unless an earlier binder of the function has it; a
  fresh name contains `%`, which no source name does.

  Layouts and grades. A fresh `let` takes the layout
  `Muro.IR.Check` infers for its value (`:opaque` where it infers
  none), so every use reads the layout the operand had. Its grade
  follows `Muro.IR.Check`: a scrutinee (`match`, `letp`) is `:affine`,
  as a non-variable scrutinee is there, so the predecessor of `suc` and
  `wsome` keeps its grade. Any other operand is `:reuse` when its value
  mentions no `:linear` or `:affine` variable and `:linear` otherwise:
  it is used once on every path, and a `:reuse` position still refuses
  it exactly when it refused the operand.

  `Muro.IR.Check` accepts the result of an image it accepts, and
  `Muro.IR.Eval` computes the same value on it. No emitter reads this
  image yet: C, Rust, and Zig emit the image before this pass, so
  their bytes do not change. `Muro.IR.Loop` accepts it as it accepts
  any image.
  """

  alias Muro.IR
  alias Muro.IR.Check

  @doc """
  The A-normal form of every function of `funs`.

  `opts` may set `book:`, the named book, so a constructor field gets
  the grade `Muro.IR.Check` gives it, and `closures:` as there.
  """
  def funs(funs, opts \\ []) when is_list(funs) and is_list(opts) do
    funs = Enum.map(funs, &IR.normalize_fun/1)
    ctx = Check.layout_ctx(funs, opts)
    Enum.map(funs, &fun(&1, ctx))
  end

  defp fun(f, ctx) do
    names = Enum.map(f.params, &IR.param_name/1)

    chk =
      Map.new(f.params, fn p ->
        {IR.param_name(p), %{grade: IR.param_grade(p), lay: IR.param_lay(p)}}
      end)

    env = %{ren: Map.new(names, &{&1, &1}), chk: chk, ctx: ctx}
    st = %{taken: MapSet.new(names), n: 0}
    {body, _st} = tail(f.body, env, st)
    %{f | body: body}
  end

  # -- atoms ----------------------------------------------------------------

  @doc "True when `t` is an atom: a variable or a literal."
  def atom?({:var, x}) when is_binary(x), do: true
  def atom?(:ze), do: true
  def atom?(:tt), do: true
  def atom?({:nat, n}) when is_integer(n), do: true
  def atom?({:str, s}) when is_binary(s), do: true
  def atom?({:byt, b}) when is_binary(b), do: true
  def atom?({:wrd, _k, _op, []}), do: true
  def atom?({:con, _d, _c, []}), do: true
  def atom?(_), do: false

  @doc """
  The operands of an operation, in evaluation order, and a function
  that rebuilds the operation from new operands. `nil` for a binder,
  a `match`, an atom, `abort`, or a term this module does not know.
  """
  def split({:su, u}), do: {[u], fn [u] -> {:su, u} end}
  def split({:pair, a, b}), do: {[a, b], fn [a, b] -> {:pair, a, b} end}
  def split({:call, n, args}) when is_list(args), do: {args, &{:call, n, &1}}

  def split({:con, d, c, args}) when is_list(args) and args != [],
    do: {args, &{:con, d, c, &1}}

  def split({:wrd, k, op, args}) when is_list(args) and args != [],
    do: {args, &{:wrd, k, op, &1}}

  def split({:data, n, args}) when is_binary(n) and is_list(args), do: {args, &{:data, n, &1}}
  def split({:uncons, e}), do: {[e], fn [e] -> {:uncons, e} end}
  def split({:appv, f, a}), do: {[f, a], fn [f, a] -> {:appv, f, a} end}

  def split({:stream, seed, caps, step}) when is_list(caps) do
    {names, tms} = Enum.unzip(caps)

    {tms ++ [seed],
     fn xs ->
       {cs, [s]} = Enum.split(xs, length(caps))
       {:stream, s, Enum.zip(names, cs), step}
     end}
  end

  def split({:bfold, step, caps, z, s}) when is_list(caps) do
    {names, tms} = Enum.unzip(caps)

    {tms ++ [z, s],
     fn xs ->
       {cs, [z, s]} = Enum.split(xs, length(caps))
       {:bfold, step, Enum.zip(names, cs), z, s}
     end}
  end

  def split({tag, a}) when tag in [:blen, :sbytes, :bunc, :slen],
    do: {[a], fn [a] -> {tag, a} end}

  def split({tag, a, b}) when tag in [:bcat, :beq, :bget, :btil, :baft, :scat, :seq],
    do: {[a, b], fn [a, b] -> {tag, a, b} end}

  def split({:bsub, s, o, n}), do: {[s, o, n], fn [s, o, n] -> {:bsub, s, o, n} end}
  def split(_), do: nil

  @doc "The operands of `t` (`split/1`), or `[]`."
  def operands(t) do
    case split(t) do
      {ops, _} -> ops
      nil -> []
    end
  end

  # -- the pass -------------------------------------------------------------

  defp tail(t, env, st), do: norm(t, env, st, fn c, _chk, st -> {c, st} end)

  # `k` takes a comp, the binder environment after the lets placed
  # before it, and the name state, and returns `{term, st}`. Source
  # names resolve through `env.ren`, which is lexical; `chk` is keyed
  # by output names, which are unique, so it only grows.
  defp norm({:var, x}, env, st, k), do: k.({:var, Map.get(env.ren, x, x)}, env.chk, st)

  defp norm({:let, x, :erased, g, v, b}, env, st, k) when is_binary(x) do
    {x2, st} = bind(x, st)
    env1 = scope(env, env.chk, [{x, x2, %{grade: g, lay: :erased}}])
    {b2, st} = norm(b, env1, st, k)
    {{:let, x2, :erased, g, v, b2}, st}
  end

  defp norm({:let, x, lay, g, v, b}, env, st, k) when is_binary(x) do
    norm(v, env, st, fn c, chk, st ->
      {x2, st} = bind(x, st)
      env1 = scope(env, chk, [{x, x2, %{grade: g, lay: lay, arg_grade: Check.arg_grade_of(c)}}])
      {b2, st} = norm(b, env1, st, k)
      {{:let, x2, lay, g, c, b2}, st}
    end)
  end

  defp norm({:letp, a, b, e, body}, env, st, k) do
    atomize(e, :scrut, env, st, fn ae, chk, st ->
      {a2, st} = bind(a, st)
      {b2, st} = bind(b, st)

      {la, lb} =
        case Check.infer_layout(ae, chk, env.ctx) do
          {:pair, x, y} -> {x, y}
          _ -> {:unknown, :unknown}
        end

      env1 =
        scope(env, chk, [{a, a2, %{grade: :affine, lay: la}}, {b, b2, %{grade: :affine, lay: lb}}])

      {body2, st} = norm(body, env1, st, k)
      {{:letp, a2, b2, ae, body2}, st}
    end)
  end

  defp norm({:match, s, arms}, env, st, k) when is_list(arms) do
    atomize(s, :scrut, env, st, fn as, chk, st ->
      slay = Check.infer_layout(as, chk, env.ctx)
      {arms2, st} = norm_arms(arms, as, slay, %{env | chk: chk}, st)
      k.({:match, as, arms2}, chk, st)
    end)
  end

  defp norm({:match, s, lay, arms}, env, st, k) when is_list(arms) do
    atomize(s, :scrut, env, st, fn as, chk, st ->
      {arms2, st} = norm_arms(arms, as, lay, %{env | chk: chk}, st)
      k.({:match, as, lay, arms2}, chk, st)
    end)
  end

  defp norm({:lam, x, lay, g, body}, env, st, k) when is_binary(x) do
    {x2, st} = bind(x, st)
    env1 = scope(env, env.chk, [{x, x2, %{grade: g, lay: lay}}])
    {body2, st} = tail(body, env1, st)
    k.({:lam, x2, lay, g, body2}, env.chk, st)
  end

  defp norm(t, env, st, k) do
    cond do
      atom?(t) ->
        k.(t, env.chk, st)

      t == :abort ->
        k.(t, env.chk, st)

      true ->
        case split(t) do
          {ops, rebuild} ->
            atomize_list(ops, env, st, fn atoms, chk, st -> k.(rebuild.(atoms), chk, st) end)

          nil ->
            raise ArgumentError, "Muro.IR.Anf: unknown term #{inspect(t, limit: 8)}"
        end
    end
  end

  defp norm_arms(arms, scrut, slay, env, st) do
    Enum.map_reduce(arms, st, fn {:arm, tag, names, body}, st ->
      {pairs, st} =
        Enum.map_reduce(names, st, fn n, st ->
          {n2, st} = bind(n, st)
          {{n, n2}, st}
        end)

      names2 = Enum.map(pairs, &elem(&1, 1))
      chk = Check.arm_env(scrut, slay, {:arm, tag, names2, nil}, env.chk, env.ctx)
      env1 = %{env | ren: Enum.reduce(pairs, env.ren, fn {n, n2}, r -> Map.put(r, n, n2) end)}
      {body2, st} = tail(body, %{env1 | chk: chk}, st)
      {{:arm, tag, names2, body2}, st}
    end)
  end

  defp atomize_list([], env, st, k), do: k.([], env.chk, st)

  defp atomize_list([t | ts], env, st, k) do
    atomize(t, :op, env, st, fn a, chk, st ->
      atomize_list(ts, %{env | chk: chk}, st, fn as, chk, st -> k.([a | as], chk, st) end)
    end)
  end

  # An atomic operand stays where it is. Anything else is bound by a
  # fresh let. A scrutinee that was not a variable is always bound, so
  # `Muro.IR.Check` reads it as it read the non-variable.
  defp atomize(t, kind, env, st, k) do
    if atom?(t) do
      norm(t, env, st, k)
    else
      norm(t, env, st, fn c, chk, st ->
        if kind == :op and atom?(c) do
          k.(c, chk, st)
        else
          {x, st} = fresh(st)
          lay = known(Check.infer_layout(c, chk, env.ctx))
          g = grade(kind, c, chk)
          meta = %{grade: g, lay: lay, arg_grade: Check.arg_grade_of(c)}
          {body, st} = k.({:var, x}, Map.put(chk, x, meta), st)
          {{:let, x, lay, g, c, body}, st}
        end
      end)
    end
  end

  defp grade(:scrut, _c, _chk), do: :affine

  defp grade(:op, c, chk) do
    if Check.restricted_vars(c, chk) == [], do: :reuse, else: :linear
  end

  defp known(:unknown), do: :opaque

  defp known(t) when is_tuple(t),
    do: t |> Tuple.to_list() |> Enum.map(&known/1) |> List.to_tuple()

  defp known(t), do: t

  defp scope(env, chk, binds) do
    Enum.reduce(binds, %{env | chk: chk}, fn {src, out, meta}, env ->
      %{env | ren: Map.put(env.ren, src, out), chk: Map.put(env.chk, out, meta)}
    end)
  end

  defp bind(x, st) do
    if MapSet.member?(st.taken, x) do
      fresh(st, x)
    else
      {x, %{st | taken: MapSet.put(st.taken, x)}}
    end
  end

  defp fresh(st, stem \\ "a") do
    name = "#{stem}%#{st.n}"
    st = %{st | n: st.n + 1}

    if MapSet.member?(st.taken, name),
      do: fresh(st, stem),
      else: {name, %{st | taken: MapSet.put(st.taken, name)}}
  end

  # -- the invariant --------------------------------------------------------

  @doc """
  Every place `funs` is not in A-normal form, as
  `{function, term}`. `[]` for the result of `funs/2`.
  """
  def violations(funs) when is_list(funs) do
    Enum.flat_map(funs, fn f ->
      f = IR.normalize_fun(f)
      f.body |> tail_bad() |> Enum.map(&{f.name, &1})
    end)
  end

  @doc "True when every operand of every function of `funs` is atomic."
  def anf?(funs), do: violations(funs) == []

  @doc """
  True when every binder of each function of `funs` (parameters
  included) is bound once.
  """
  def unique_binders?(funs) when is_list(funs) do
    Enum.all?(funs, fn f ->
      names = Enum.map(f.params, &IR.param_name/1) ++ binders(f.body)
      length(names) == length(Enum.uniq(names))
    end)
  end

  defp binders({:let, x, _lay, _g, v, b}), do: [x | binders(v) ++ binders(b)]
  defp binders({:letp, a, b, e, body}), do: [a, b | binders(e) ++ binders(body)]
  defp binders({:lam, x, _lay, _g, body}) when is_binary(x), do: [x | binders(body)]

  defp binders({:match, s, arms}) when is_list(arms), do: binders(s) ++ arm_binders(arms)

  defp binders({:match, s, _lay, arms}) when is_list(arms),
    do: binders(s) ++ arm_binders(arms)

  defp binders(t), do: Enum.flat_map(operands(t), &binders/1)

  defp arm_binders(arms),
    do: Enum.flat_map(arms, fn {:arm, _, names, tm} -> names ++ binders(tm) end)

  defp tail_bad({:let, _x, :erased, _g, :ze, b}), do: tail_bad(b)

  defp tail_bad({:let, _x, _lay, _g, v, b} = t) do
    head =
      case v do
        {:let, _, _, _, _, _} -> [t]
        {:letp, _, _, _, _} -> [t]
        _ -> comp_bad(v)
      end

    head ++ tail_bad(b)
  end

  defp tail_bad({:letp, _a, _b, e, body} = t) do
    if(atom?(e), do: [], else: [t]) ++ tail_bad(body)
  end

  defp tail_bad(t), do: comp_bad(t)

  defp comp_bad(:abort), do: []

  defp comp_bad({:lam, x, _lay, _g, body}) when is_binary(x), do: tail_bad(body)

  defp comp_bad({:match, s, arms} = t) when is_list(arms), do: match_bad(t, s, arms)
  defp comp_bad({:match, s, _lay, arms} = t) when is_list(arms), do: match_bad(t, s, arms)

  defp comp_bad(t) do
    cond do
      atom?(t) ->
        []

      true ->
        case split(t) do
          {ops, _} -> if Enum.all?(ops, &atom?/1), do: [], else: [t]
          nil -> [t]
        end
    end
  end

  defp match_bad(t, s, arms) do
    if(atom?(s), do: [], else: [t]) ++
      Enum.flat_map(arms, fn {:arm, _, _, tm} -> tail_bad(tm) end)
  end
end

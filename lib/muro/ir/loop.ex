defmodule Muro.IR.Loop do
  @moduledoc """
  Byte folds as loops (Phase 1a of the `Muro.IR` plan).

  `Muro.IR.elaborate/2` prints a `sliceFold` as `{:bfold, step, caps,
  z, s}` and the fold body as a generated function `step`, so a back
  end that follows the image calls `step` once per octet and passes the
  accumulator to it by value and back. `funs/2` replaces every such
  fold with the loop the step describes:

      {:loop, caps, octet, rest, acc, z, s, stop, body}

    * `caps` is `[{name, layout, grade, term}]`: the step's capture
      parameters, each bound once to its term before the first octet.
    * `octet` and `rest` are the step's octet and remainder parameters,
      `{name, :u8, grade}` and `{name, :slice, grade}`.
    * `acc` is the step's accumulator parameter, `{name, layout,
      grade}`. It holds `z` before the first octet and the value of
      `body` after each one; the loop's value is its last value.
    * `s` is the input.
    * `stop` is `:none` or `{v, test}`, the early exit of
      `Muro.IR.Share.stop/2`: before each octet, `test` is evaluated
      with `v` bound to the accumulator, and the loop ends when it is
      the `:u64` `1`. `Muro.IR.Share.stop/2` only returns a test that
      holds exactly when the rest of the fold is the identity, so the
      exit does not change the value.
    * `body` is the step's body. Its free variables are the loop's
      binders and nothing else: the step was a closed function.

  A fold whose step is not a generated fold step of the image, or
  whose step does not have exactly the captures plus the three fold
  parameters, is left as it is. A generated fold step that no fold
  refers to any more is dropped from the image.

  ## In-place calls

  A loop body whose value, along a tail path (through `let`, `letp`,
  and match arms that do not rebind the accumulator), is a call
  `f(..., acc, ...)` that passes the accumulator once and nowhere else
  in its arguments becomes `{:inout, f, args}` when that argument may
  be updated in place. That is so when the accumulator is `:linear` or
  `:affine` (no copy of the old value is kept), the parameter of `f`
  in its place has the accumulator's layout, `f` returns that same
  layout, the layout is a by-value struct (`Muro.IR.Rep.value_lay?/2`,
  so `book:` must be given), `f` is a run and not a generated step,
  and the body of `f` holds no stream (a stream would need a second
  copy of its step functions). `f` gets the field `inout: name`, the
  parameter it updates. The grade of that parameter inside `f` does
  not matter: `f` reads it only before it writes its result. Each run
  updates at most one parameter: the first fold that asks for one
  decides it.

  `{:inout, f, args}` has the value of `{:call, f, args}`. A back end
  may instead pass the accumulator by reference and let `f` overwrite
  it: the call is the last thing the iteration does with the
  accumulator, so nothing reads the old value after the update, and
  `f` reads its parameter only before it writes its result.

  `Muro.IR.Check` validates both forms, and `Muro.IR.Eval` evaluates
  them, spending one unit of fuel per octet, as the step call did.
  `Muro.Emit.C` runs this pass after `Muro.IR.Share`. Rust, Zig, and
  the other back ends do not read it.
  """

  alias Muro.IR
  alias Muro.IR.{Rep, Share}

  @restricted [:linear, :affine]

  @doc """
  Lower every byte fold of `funs` to a loop.

  `opts` may set `book:`, the named book. Without it no call is marked
  `:inout`, because a by-value struct cannot be recognised.
  """
  def funs(funs, opts \\ []) when is_list(funs) and is_list(opts) do
    funs = Enum.map(funs, &IR.normalize_fun/1)
    book = Keyword.get(opts, :book)

    steps =
      for f <- funs, fold_step?(f), into: %{}, do: {f.name, f}

    runs = for f <- funs, not Map.get(f, :generated, false), into: %{}, do: {f.name, f}
    ctx = %{steps: steps, runs: runs}

    lowered = Enum.map(funs, fn f -> %{f | body: lower(f.body, ctx)} end)
    lowered |> mark_inout(book) |> drop_dead_steps()
  end

  @doc "Whether `t` holds a byte fold that `funs/2` did not lower."
  def bfold?({:bfold, _, _, _, _}), do: true
  def bfold?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&bfold?/1)
  def bfold?(t) when is_list(t), do: Enum.any?(t, &bfold?/1)
  def bfold?(_), do: false

  @doc "The number of `{:loop, ...}` forms in `t`."
  def loops({:loop, caps, _o, _r, _a, z, s, _stop, body}) do
    1 + loops(Enum.map(caps, &elem(&1, 3))) + loops(z) + loops(s) + loops(body)
  end

  def loops(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.map(&loops/1) |> Enum.sum()
  def loops(t) when is_list(t), do: t |> Enum.map(&loops/1) |> Enum.sum()
  def loops(_), do: 0

  defp fold_step?(f), do: Map.get(f, :generated, false) and Map.get(f, :fold, false)

  # -- lowering ----------------------------------------------------------

  defp lower({:bfold, step, caps, z, s} = t, ctx) when is_list(caps) do
    with %{params: params, body: body} = fun <- Map.get(ctx.steps, step),
         true <- length(params) == length(caps) + 3 do
      {cap_ps, [octet, rest, acc]} = Enum.split(params, length(caps))

      lcaps =
        Enum.zip_with(cap_ps, caps, fn {n, lay, g}, {_cn, tm} -> {n, lay, g, lower(tm, ctx)} end)

      {:loop, lcaps, octet, rest, acc, lower(z, ctx), lower(s, ctx), stop(fun, ctx),
       lower(body, ctx)}
    else
      _ -> lower_children(t, ctx)
    end
  end

  defp lower(t, ctx), do: lower_children(t, ctx)

  defp lower_children(t, ctx) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.map(&lower(&1, ctx)) |> List.to_tuple()
  end

  defp lower_children(t, ctx) when is_list(t), do: Enum.map(t, &lower(&1, ctx))
  defp lower_children(t, _ctx), do: t

  defp stop(step, ctx) do
    case Share.stop(step, ctx.runs) do
      {:ok, v, test} -> {v, test}
      :none -> :none
    end
  end

  # -- in-place calls ----------------------------------------------------

  defp mark_inout(funs, nil), do: funs

  defp mark_inout(funs, book) do
    by_name = Map.new(funs, &{&1.name, &1})

    {funs, chosen} =
      Enum.map_reduce(funs, %{}, fn f, chosen ->
        {body, chosen} = io_walk(f.body, by_name, book, chosen)
        {%{f | body: body}, chosen}
      end)

    Enum.map(funs, fn f ->
      case Map.fetch(chosen, f.name) do
        {:ok, i} -> Map.put(f, :inout, IR.param_name(Enum.at(f.params, i)))
        :error -> f
      end
    end)
  end

  # Every loop of `t`, outermost first, with its body's tail calls
  # rewritten where that is allowed.
  defp io_walk({:loop, caps, o, r, {acc, alay, ag} = a, z, s, stop, body}, by_name, book, chosen) do
    {caps, chosen} =
      Enum.map_reduce(caps, chosen, fn {n, lay, g, tm}, chosen ->
        {tm, chosen} = io_walk(tm, by_name, book, chosen)
        {{n, lay, g, tm}, chosen}
      end)

    {z, chosen} = io_walk(z, by_name, book, chosen)
    {s, chosen} = io_walk(s, by_name, book, chosen)
    {body, chosen} = io_walk(body, by_name, book, chosen)

    {body, chosen} =
      if ag in @restricted,
        do: io_tail(body, acc, alay, by_name, book, chosen),
        else: {body, chosen}

    {{:loop, caps, o, r, a, z, s, stop, body}, chosen}
  end

  defp io_walk(t, by_name, book, chosen) when is_tuple(t) do
    {xs, chosen} = io_walk(Tuple.to_list(t), by_name, book, chosen)
    {List.to_tuple(xs), chosen}
  end

  defp io_walk(t, by_name, book, chosen) when is_list(t),
    do: Enum.map_reduce(t, chosen, &io_walk(&1, by_name, book, &2))

  defp io_walk(t, _by_name, _book, chosen), do: {t, chosen}

  defp io_tail({:let, x, lay, g, v, b}, acc, alay, by_name, book, chosen) when x != acc do
    {b, chosen} = io_tail(b, acc, alay, by_name, book, chosen)
    {{:let, x, lay, g, v, b}, chosen}
  end

  defp io_tail({:letp, a, b, e, body}, acc, alay, by_name, book, chosen)
       when a != acc and b != acc do
    {body, chosen} = io_tail(body, acc, alay, by_name, book, chosen)
    {{:letp, a, b, e, body}, chosen}
  end

  defp io_tail({:match, s, arms}, acc, alay, by_name, book, chosen) when is_list(arms) do
    {arms, chosen} = io_arms(arms, acc, alay, by_name, book, chosen)
    {{:match, s, arms}, chosen}
  end

  defp io_tail({:match, s, lay, arms}, acc, alay, by_name, book, chosen) when is_list(arms) do
    {arms, chosen} = io_arms(arms, acc, alay, by_name, book, chosen)
    {{:match, s, lay, arms}, chosen}
  end

  defp io_tail({:call, f, args} = t, acc, alay, by_name, book, chosen) when is_list(args) do
    with %{} = callee <- Map.get(by_name, f),
         {:ok, i} <- acc_slot(args, acc),
         true <- io_param?(callee, i, alay, book),
         true <- Map.get(chosen, f, i) == i do
      {{:inout, f, args}, Map.put(chosen, f, i)}
    else
      _ -> {t, chosen}
    end
  end

  defp io_tail(t, _acc, _alay, _by_name, _book, chosen), do: {t, chosen}

  defp io_arms(arms, acc, alay, by_name, book, chosen) do
    Enum.map_reduce(arms, chosen, fn {:arm, c, ns, tm} = arm, chosen ->
      if acc in ns do
        {arm, chosen}
      else
        {tm, chosen} = io_tail(tm, acc, alay, by_name, book, chosen)
        {{:arm, c, ns, tm}, chosen}
      end
    end)
  end

  @doc false
  # The index of the one argument that is the accumulator, when no other
  # argument mentions it.
  def acc_slot(args, acc) do
    case Enum.filter(Enum.with_index(args), fn {a, _} -> a == {:var, acc} end) do
      [{_, i}] ->
        others = List.delete_at(args, i)
        if Enum.any?(others, &mentions?(&1, acc)), do: :error, else: {:ok, i}

      _ ->
        :error
    end
  end

  @doc false
  # Whether parameter `i` of `callee` may be updated in place by a loop
  # whose `:linear` or `:affine` accumulator has layout `alay`.
  def io_param?(callee, i, alay, book) do
    case Enum.at(callee.params, i) do
      nil ->
        false

      p ->
        IR.param_lay(p) == alay and callee.ret == alay and
          not Map.get(callee, :generated, false) and Rep.value_lay?(book, alay) and
          not stream?(callee.body)
    end
  end

  defp stream?({:stream, _, _, _}), do: true
  defp stream?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&stream?/1)
  defp stream?(t) when is_list(t), do: Enum.any?(t, &stream?/1)
  defp stream?(_), do: false

  # Syntactic, so a shadowed name still counts: that only declines.
  defp mentions?({:var, x}, x), do: true
  defp mentions?(t, x) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&mentions?(&1, x))
  defp mentions?(t, x) when is_list(t), do: Enum.any?(t, &mentions?(&1, x))
  defp mentions?(_, _), do: false

  # -- dead steps --------------------------------------------------------

  # A generated fold step stays while a remaining `bfold` names it. A
  # stream step is never dropped here.
  defp drop_dead_steps(funs) do
    live =
      funs
      |> Enum.reject(&fold_step?/1)
      |> reach(Map.new(funs, &{&1.name, &1}), MapSet.new())

    Enum.filter(funs, fn f -> not fold_step?(f) or MapSet.member?(live, f.name) end)
  end

  defp reach([], _by_name, seen), do: seen

  defp reach([f | fs], by_name, seen) do
    new =
      f.body
      |> fold_names([])
      |> Enum.reject(&MapSet.member?(seen, &1))
      |> Enum.uniq()

    seen = Enum.reduce(new, seen, &MapSet.put(&2, &1))
    more = for n <- new, g = Map.get(by_name, n), do: g
    reach(more ++ fs, by_name, seen)
  end

  defp fold_names({:bfold, step, caps, z, s}, acc),
    do: fold_names([caps, z, s], [step | acc])

  defp fold_names(t, acc) when is_tuple(t), do: fold_names(Tuple.to_list(t), acc)
  defp fold_names(t, acc) when is_list(t), do: Enum.reduce(t, acc, &fold_names/2)
  defp fold_names(_, acc), do: acc
end

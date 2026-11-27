defmodule Muro.IR.Eval do
  @moduledoc """
  Call-by-value interpreter of a `Muro.IR` image.

  `call/4` runs one function of an image on argument values. It reads
  every image `Muro.IR` produces: the default image of
  `Muro.IR.elaborate/2`, the same image after `Muro.IR.Share.funs/2`,
  the closure image of `Muro.IR.elaborate(book, closures: true)`, and
  any of those after `Muro.IR.Anf.funs/2` or `Muro.IR.Loop.funs/2`.
  No emitter reads this module. It is the reference the differential
  tests hold every image to, against `Muro.Check.normalize/3`.

  ## Values

    * `{:nat, n}` with `n >= 0`, for `:nat`.
    * `:tt`, for `:unit`.
    * `{:word, k, n}` with `k` in `:u8`, `:u32`, `:u64`, `:i64` and `n`
      the residue modulo `2^w`. I64 is the two's-complement bit
      pattern, as in `Muro.Word`.
    * `true` or `false`, for `:wbool`.
    * `{:some, v}` or `:none`, for `{:opt, _}`.
    * `{:str, utf8}`, for `:string`.
    * `{:bytes, binary}`, for `:slice` (a `Bytes` or a `Slice` view).
    * `{:pair, a, b}`.
    * `{:con, data, ctor, fields}` for `{:data, _}`. Erased fields are
      not there. An atom is `{:con, "Atom", name, []}`.
    * `{:stream, step, caps, seed}`, a stream: the generated step's
      name, the captured values in parameter order, and the seed.
    * `{:clo, env, name, body}`, a `{:lam, ...}` closure.
    * `:erased`, the value an erased constructor field binds
      (`{:let, x, :erased, _, :ze, body}`).

  ## Fuel

  Every function call, closure application, stream `uncons`, and
  octet of a `bfold` or a `loop` spends one unit of fuel. Nothing else
  loops, so a non-terminating image always ends in
  `{:error, :out_of_fuel}`.

  ## Loops

  `{:loop, caps, octet, rest, acc, z, s, stop, body}` (`Muro.IR.Loop`)
  binds the captures once, then runs `body` once per octet of `s` with
  the captures, the octet, the remaining bytes, and the accumulator
  bound, exactly as the fold step it came from was called. Before each
  octet a `{v, test}` stop is evaluated with `v` bound to the
  accumulator, and the loop ends when it is the `:u64` `1`.
  `{:inout, f, args}` is the call `{:call, f, args}`.

  ## Word operations

  A word operation is handed to `Muro.Word.step/2` on the literal terms
  of its argument values, so wrapping, signed comparison, shifts,
  checked arithmetic, division by zero, and casts are the checker's own
  reductions and not a second copy of them.
  """

  alias Muro.{Bytes, Print, Word}

  @fuel 1_000_000

  @typedoc "A value. See the module documentation."
  @type value :: term()

  @typedoc "Why evaluation stopped."
  @type reason ::
          :out_of_fuel
          | :abort
          | {:unbound, String.t()}
          | {:unknown_fun, String.t()}
          | {:arity, String.t(), non_neg_integer(), non_neg_integer()}
          | {:no_arm, value()}
          | {:type, atom(), value()}
          | {:stuck_word, term(), [value()]}
          | {:unknown_term, term()}

  @doc "The fuel `call/4` and `eval/4` start with when `fuel:` is not given."
  def default_fuel, do: @fuel

  @doc """
  Call the function `name` of `funs` on `args`, a list of values, one per
  live parameter in order.

  `opts` may set `fuel:` (default `default_fuel/0`). Returns
  `{:ok, value}` or `{:error, reason}`.
  """
  @spec call([map()], String.t(), [value()], keyword()) :: {:ok, value()} | {:error, reason()}
  def call(funs, name, args, opts \\ []) when is_list(funs) and is_list(args) do
    prog = program(funs)

    run(opts, fn fuel ->
      case Map.fetch(prog.calls, name) do
        {:ok, fun} -> invoke(prog, fun, args, fuel)
        :error -> throw({:ir_eval, {:unknown_fun, name}})
      end
    end)
  end

  @doc """
  Evaluate the term `t` of the image `funs` under `env`, a map from
  binder name to value. Same options and result as `call/4`.
  """
  @spec eval([map()], term(), map(), keyword()) :: {:ok, value()} | {:error, reason()}
  def eval(funs, t, env \\ %{}, opts \\ []) when is_list(funs) and is_map(env) do
    prog = program(funs)
    run(opts, fn fuel -> ev(prog, t, env, fuel) end)
  end

  @doc """
  The first `n` heads of a stream value of `funs`, as `{:ok, heads}`.
  Each head spends one unit of fuel.
  """
  @spec take([map()], value(), non_neg_integer(), keyword()) ::
          {:ok, [value()]} | {:error, reason()}
  def take(funs, stream, n, opts \\ []) when is_list(funs) and is_integer(n) and n >= 0 do
    prog = program(funs)
    run(opts, fn fuel -> take_go(prog, stream, n, [], fuel) end)
  end

  defp take_go(_prog, _s, 0, acc, fuel), do: {Enum.reverse(acc), fuel}

  defp take_go(prog, s, n, acc, fuel) do
    {{:pair, h, rest}, fuel} = uncons(prog, s, fuel)
    take_go(prog, rest, n - 1, [h | acc], fuel)
  end

  @doc """
  Apply a closure value to an argument value. Same result as `call/4`.
  """
  @spec apply_value([map()], value(), value(), keyword()) :: {:ok, value()} | {:error, reason()}
  def apply_value(funs, f, a, opts \\ []) when is_list(funs) do
    prog = program(funs)
    run(opts, fn fuel -> appv(prog, f, a, fuel) end)
  end

  defp run(opts, go) do
    fuel = Keyword.get(opts, :fuel, @fuel)

    try do
      {v, _fuel} = go.(fuel)
      {:ok, v}
    catch
      {:ir_eval, reason} -> {:error, reason}
    end
  end

  # A generated fold or stream step is never called by name, and its
  # name may also be a source run's name, so steps are a second table.
  defp program(funs) do
    funs = Enum.map(funs, &Muro.IR.normalize_fun/1)

    %{
      calls: for(f <- funs, not Map.get(f, :generated, false), into: %{}, do: {f.name, f}),
      steps: for(f <- funs, Map.get(f, :generated, false), into: %{}, do: {f.name, f})
    }
  end

  defp step_fun(prog, name) do
    case Map.fetch(prog.steps, name) do
      {:ok, f} ->
        f

      :error ->
        case Map.fetch(prog.calls, name) do
          {:ok, f} -> f
          :error -> throw({:ir_eval, {:unknown_fun, name}})
        end
    end
  end

  defp spend(0), do: throw({:ir_eval, :out_of_fuel})
  defp spend(fuel), do: fuel - 1

  defp invoke(prog, fun, args, fuel) do
    fuel = spend(fuel)
    params = fun.params

    if length(params) != length(args) do
      throw({:ir_eval, {:arity, fun.name, length(params), length(args)}})
    end

    env =
      params
      |> Enum.zip(args)
      |> Map.new(fn {p, v} -> {Muro.IR.param_name(p), v} end)

    ev(prog, fun.body, env, fuel)
  end

  # -- terms -------------------------------------------------------------

  defp ev(_prog, {:var, x}, env, fuel) do
    case Map.fetch(env, x) do
      {:ok, v} -> {v, fuel}
      :error -> throw({:ir_eval, {:unbound, x}})
    end
  end

  defp ev(_prog, :ze, _env, fuel), do: {{:nat, 0}, fuel}
  defp ev(_prog, :tt, _env, fuel), do: {:tt, fuel}
  defp ev(_prog, {:nat, n}, _env, fuel) when is_integer(n) and n >= 0, do: {{:nat, n}, fuel}

  defp ev(prog, {:su, t}, env, fuel) do
    {v, fuel} = ev(prog, t, env, fuel)
    {{:nat, nat!(v) + 1}, fuel}
  end

  defp ev(_prog, :abort, _env, _fuel), do: throw({:ir_eval, :abort})

  defp ev(prog, {:let, x, :erased, _g, _v, b}, env, fuel) when is_binary(x),
    do: ev(prog, b, Map.put(env, x, :erased), fuel)

  defp ev(prog, {:let, x, _lay, _g, v, b}, env, fuel) when is_binary(x) do
    {val, fuel} = ev(prog, v, env, fuel)
    ev(prog, b, Map.put(env, x, val), fuel)
  end

  defp ev(prog, {:let, x, lay, v, b}, env, fuel),
    do: ev(prog, {:let, x, lay, :reuse, v, b}, env, fuel)

  defp ev(prog, {:pair, a, b}, env, fuel) do
    {va, fuel} = ev(prog, a, env, fuel)
    {vb, fuel} = ev(prog, b, env, fuel)
    {{:pair, va, vb}, fuel}
  end

  defp ev(prog, {:letp, a, b, e, body}, env, fuel) do
    case ev(prog, e, env, fuel) do
      {{:pair, va, vb}, fuel} -> ev(prog, body, env |> Map.put(a, va) |> Map.put(b, vb), fuel)
      {v, _} -> throw({:ir_eval, {:type, :pair, v}})
    end
  end

  defp ev(prog, {:uncons, s}, env, fuel) do
    {v, fuel} = ev(prog, s, env, fuel)
    uncons(prog, v, fuel)
  end

  defp ev(prog, {:match, s, arms}, env, fuel) when is_list(arms),
    do: ev_match(prog, s, arms, env, fuel)

  defp ev(prog, {:match, s, _kind, arms}, env, fuel) when is_list(arms),
    do: ev_match(prog, s, arms, env, fuel)

  defp ev(prog, {:call, name, ts}, env, fuel) do
    {args, fuel} = ev_list(prog, ts, env, fuel)

    case Map.fetch(prog.calls, name) do
      {:ok, fun} -> invoke(prog, fun, args, fuel)
      :error -> throw({:ir_eval, {:unknown_fun, name}})
    end
  end

  defp ev(prog, {:con, data, ctor, ts}, env, fuel) do
    {vs, fuel} = ev_list(prog, ts, env, fuel)
    {{:con, data, ctor, vs}, fuel}
  end

  defp ev(prog, {:stream, seed, caps, step}, env, fuel) do
    {cvs, fuel} = ev_list(prog, Enum.map(caps, fn {_name, t} -> t end), env, fuel)
    {sv, fuel} = ev(prog, seed, env, fuel)
    {{:stream, step, cvs, sv}, fuel}
  end

  defp ev(_prog, {:lam, x, _lay, _g, body}, env, fuel) when is_binary(x),
    do: {{:clo, env, x, body}, fuel}

  defp ev(_prog, {:lam, x, _lay, body}, env, fuel) when is_binary(x),
    do: {{:clo, env, x, body}, fuel}

  defp ev(prog, {:appv, f, a}, env, fuel) do
    {fv, fuel} = ev(prog, f, env, fuel)
    {av, fuel} = ev(prog, a, env, fuel)
    appv(prog, fv, av, fuel)
  end

  defp ev(prog, {:wrd, _k, op, args}, env, fuel) do
    {vs, fuel} = ev_list(prog, args, env, fuel)
    {word(op, vs), fuel}
  end

  # -- strings -------------------------------------------------------------

  defp ev(_prog, {:str, bin}, _env, fuel) when is_binary(bin), do: {{:str, bin}, fuel}

  defp ev(prog, {:scat, a, b}, env, fuel) do
    {[x, y], fuel} = ev_list(prog, [a, b], env, fuel)
    {{:str, str!(x) <> str!(y)}, fuel}
  end

  defp ev(prog, {:slen, a}, env, fuel) do
    {x, fuel} = ev(prog, a, env, fuel)
    {{:nat, Print.scalar_count(str!(x))}, fuel}
  end

  defp ev(prog, {:seq, a, b}, env, fuel) do
    {[x, y], fuel} = ev_list(prog, [a, b], env, fuel)
    {str!(x) == str!(y), fuel}
  end

  defp ev(prog, {:sbytes, a}, env, fuel) do
    {x, fuel} = ev(prog, a, env, fuel)
    {{:bytes, str!(x)}, fuel}
  end

  # -- bytes ---------------------------------------------------------------

  defp ev(_prog, {:byt, bin}, _env, fuel) when is_binary(bin), do: {{:bytes, bin}, fuel}

  defp ev(prog, {:bcat, a, b}, env, fuel) do
    {[x, y], fuel} = ev_list(prog, [a, b], env, fuel)
    {{:bytes, Bytes.cat(bytes!(x), bytes!(y))}, fuel}
  end

  defp ev(prog, {:blen, a}, env, fuel) do
    {x, fuel} = ev(prog, a, env, fuel)
    {{:word, :u64, Bytes.len(bytes!(x))}, fuel}
  end

  defp ev(prog, {:beq, a, b}, env, fuel) do
    {[x, y], fuel} = ev_list(prog, [a, b], env, fuel)
    {Bytes.eq(bytes!(x), bytes!(y)), fuel}
  end

  defp ev(prog, {:bsub, s, off, len}, env, fuel) do
    {[x, o, n], fuel} = ev_list(prog, [s, off, len], env, fuel)
    {{:bytes, Bytes.sub(bytes!(x), word!(o, :u64), word!(n, :u64))}, fuel}
  end

  defp ev(prog, {:bget, s, i}, env, fuel) do
    {[x, iv], fuel} = ev_list(prog, [s, i], env, fuel)

    case Bytes.get(bytes!(x), word!(iv, :u64)) do
      {:some, b} -> {{:some, {:word, :u8, b}}, fuel}
      :none -> {:none, fuel}
    end
  end

  defp ev(prog, {:bunc, s}, env, fuel) do
    {x, fuel} = ev(prog, s, env, fuel)

    case Bytes.uncons(bytes!(x)) do
      :nothing ->
        {{:con, "Maybe", "nothing", []}, fuel}

      {:just, b, rest} ->
        {{:con, "Maybe", "just", [{:pair, {:word, :u8, b}, {:bytes, rest}}]}, fuel}
    end
  end

  defp ev(prog, {:btil, s, b}, env, fuel) do
    {[x, bv], fuel} = ev_list(prog, [s, b], env, fuel)
    {{:bytes, Bytes.until(bytes!(x), word!(bv, :u8))}, fuel}
  end

  defp ev(prog, {:baft, s, b}, env, fuel) do
    {[x, bv], fuel} = ev_list(prog, [s, b], env, fuel)
    {{:bytes, Bytes.aft(bytes!(x), word!(bv, :u8))}, fuel}
  end

  defp ev(prog, {:bfold, step, caps, z, s}, env, fuel) do
    {cvs, fuel} = ev_list(prog, Enum.map(caps, fn {_name, t} -> t end), env, fuel)
    {zv, fuel} = ev(prog, z, env, fuel)
    {sv, fuel} = ev(prog, s, env, fuel)
    fold(prog, step_fun(prog, step), cvs, zv, bytes!(sv), fuel)
  end

  defp ev(prog, {:loop, caps, octet, rest, acc, z, s, stop, body}, env, fuel) do
    {cvs, fuel} = ev_list(prog, Enum.map(caps, &elem(&1, 3)), env, fuel)
    {zv, fuel} = ev(prog, z, env, fuel)
    {sv, fuel} = ev(prog, s, env, fuel)

    base =
      caps
      |> Enum.map(&elem(&1, 0))
      |> Enum.zip(cvs)
      |> Map.new()

    names = {Muro.IR.param_name(octet), Muro.IR.param_name(rest), Muro.IR.param_name(acc)}
    loop(prog, {base, names, stop, body}, zv, bytes!(sv), fuel)
  end

  defp ev(prog, {:inout, name, ts}, env, fuel), do: ev(prog, {:call, name, ts}, env, fuel)

  defp ev(_prog, t, _env, _fuel), do: throw({:ir_eval, {:unknown_term, t}})

  defp ev_list(prog, ts, env, fuel) do
    {vs, fuel} =
      Enum.reduce(ts, {[], fuel}, fn t, {acc, fuel} ->
        {v, fuel} = ev(prog, t, env, fuel)
        {[v | acc], fuel}
      end)

    {Enum.reverse(vs), fuel}
  end

  defp fold(_prog, _step, _caps, acc, <<>>, fuel), do: {acc, fuel}

  defp fold(prog, step, caps, acc, <<b, rest::binary>>, fuel) do
    {acc, fuel} = invoke(prog, step, caps ++ [{:word, :u8, b}, {:bytes, rest}, acc], fuel)
    fold(prog, step, caps, acc, rest, fuel)
  end

  defp loop(_prog, _l, acc, <<>>, fuel), do: {acc, fuel}

  defp loop(prog, {base, {o, r, a}, stop, body} = l, acc, <<b, rest::binary>>, fuel) do
    case stopped(prog, stop, acc, fuel) do
      {true, fuel} ->
        {acc, fuel}

      {false, fuel} ->
        fuel = spend(fuel)
        env = base |> Map.put(o, {:word, :u8, b}) |> Map.put(r, {:bytes, rest}) |> Map.put(a, acc)
        {acc, fuel} = ev(prog, body, env, fuel)
        loop(prog, l, acc, rest, fuel)
    end
  end

  defp stopped(_prog, :none, _acc, fuel), do: {false, fuel}

  defp stopped(prog, {v, test}, acc, fuel) do
    case ev(prog, test, %{v => acc}, fuel) do
      {{:word, :u64, 1}, fuel} -> {true, fuel}
      {{:word, :u64, 0}, fuel} -> {false, fuel}
      {other, _} -> throw({:ir_eval, {:type, :u64, other}})
    end
  end

  # A stream step takes the captures, then the seed when the seed is
  # live. An erased seed is not a parameter.
  defp uncons(prog, {:stream, step, caps, seed} = s, fuel) do
    fun = step_fun(prog, step)

    args =
      if length(fun.params) == length(caps) + 1, do: caps ++ [seed], else: caps

    case invoke(prog, fun, args, fuel) do
      {{:pair, h, next}, fuel} -> {{:pair, h, {:stream, step, caps, next}}, fuel}
      {v, _} -> throw({:ir_eval, {:type, :pair, {s, v}}})
    end
  end

  defp uncons(_prog, v, _fuel), do: throw({:ir_eval, {:type, :stream, v}})

  defp appv(prog, {:clo, cenv, x, body}, a, fuel) do
    fuel = spend(fuel)
    ev(prog, body, Map.put(cenv, x, a), fuel)
  end

  defp appv(_prog, v, _a, _fuel), do: throw({:ir_eval, {:type, :fn, v}})

  # -- matches -------------------------------------------------------------

  defp ev_match(prog, s, arms, env, fuel) do
    {v, fuel} = ev(prog, s, env, fuel)
    {tag, fields} = shape(v)

    case Enum.find(arms, fn {:arm, c, _ns, _t} -> c == tag end) do
      {:arm, _c, names, body} ->
        if length(names) != length(fields) do
          throw({:ir_eval, {:arity, tag, length(names), length(fields)}})
        end

        env = names |> Enum.zip(fields) |> Enum.reduce(env, fn {n, f}, e -> Map.put(e, n, f) end)
        ev(prog, body, env, fuel)

      nil ->
        throw({:ir_eval, {:no_arm, v}})
    end
  end

  defp shape({:nat, 0}), do: {"zero", []}
  defp shape({:nat, n}) when is_integer(n) and n > 0, do: {"suc", [{:nat, n - 1}]}
  defp shape({:con, _data, ctor, fields}), do: {ctor, fields}
  defp shape(true), do: {"wtrue", []}
  defp shape(false), do: {"wfalse", []}
  defp shape({:some, v}), do: {"wsome", [v]}
  defp shape(:none), do: {"wnone", []}
  defp shape(v), do: throw({:ir_eval, {:no_arm, v}})

  # -- words ---------------------------------------------------------------

  defp word({:lit, k, n}, []) when is_integer(n), do: {:word, k, Word.residue(k, n)}
  defp word(true, []), do: true
  defp word(false, []), do: false
  defp word(:some, [v]), do: {:some, v}
  defp word(:none, []), do: :none

  defp word(op, vs) do
    case Word.step(op, Enum.map(vs, &word_term(&1, op, vs))) do
      {:ok, r} -> word_value(r, op, vs)
      :stuck -> throw({:ir_eval, {:stuck_word, op, vs}})
    end
  end

  defp word_term({:word, k, n}, _op, _vs), do: {:word, {:lit, k, n}, []}
  defp word_term({:nat, n}, _op, _vs), do: {:nat, n}
  defp word_term(_v, op, vs), do: throw({:ir_eval, {:stuck_word, op, vs}})

  defp word_value({:word, {:lit, k, n}, []}, _op, _vs), do: {:word, k, n}
  defp word_value({:word, true, []}, _op, _vs), do: true
  defp word_value({:word, false, []}, _op, _vs), do: false
  defp word_value({:word, :none, []}, _op, _vs), do: :none
  defp word_value({:word, :some, [x]}, op, vs), do: {:some, word_value(x, op, vs)}

  defp word_value(t, op, vs) do
    case Word.nat_closed(t) do
      {:ok, n} -> {:nat, n}
      :error -> throw({:ir_eval, {:stuck_word, op, vs}})
    end
  end

  # -- checks --------------------------------------------------------------

  defp nat!({:nat, n}), do: n
  defp nat!(v), do: throw({:ir_eval, {:type, :nat, v}})

  defp str!({:str, s}), do: s
  defp str!(v), do: throw({:ir_eval, {:type, :string, v}})

  defp bytes!({:bytes, b}), do: b
  defp bytes!(v), do: throw({:ir_eval, {:type, :slice, v}})

  defp word!({:word, k, n}, k), do: n
  defp word!(v, k), do: throw({:ir_eval, {:type, k, v}})
end

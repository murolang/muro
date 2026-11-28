defmodule Muro.Emit.FoldFast do
  @moduledoc """
  Fast Elixir for a byte fold the same recognizer the C backend uses can prove.

  A fold is a string scan when `index_plain?/4` holds, the transition at
  indices 0, 1, 5 and 40 is one border automaton, and `Muro.IR.Eval`
  agrees on the samples below. It is a hot-byte skip when the step is
  the identity off one, two or three constants and the same interpreter
  agrees. Either failure leaves the closure fold. The C emitter is not
  changed here.
  """

  alias Muro.IR

  @mask 0xFFFFFFFFFFFFFFFF
  @fuel 80_000

  @doc """
  Plans for the runs of `book`, keyed by source name.

  `names` is `Muro.Emit.elixir_names/1`. A book with no byte fold is
  `\%{}` and is not elaborated.
  """
  def plans(book, names) when is_list(book) and is_map(names) do
    if mentions_fold?(book) do
      case Muro.IR.elaborate(book) do
        {:ok, image} -> build(book, image, names)
        _ -> %{}
      end
    else
      %{}
    end
  end

  @doc """
  Elixir expression for `plan` applied to `args`, or nil when the
  expression cannot be printed. `args` are the live parameter names in
  order, the same names `Muro.Emit` gives the definition.
  """
  def render({:needle, plan}, args, _names) do
    case arg_src(plan.params, plan.param, args) do
      nil -> nil
      arg -> needle_src(arg, plan)
    end
  end

  def render({:hot, plan}, args, names) do
    with arg when arg != nil <- arg_src(plan.params, plan.param, args),
         {:ok, env} <- body_env(plan, args, names),
         {:ok, z} <- ex(plan.z, param_env(plan.params, args), names),
         {:ok, body} <- ex(plan.body, env, names),
         {:ok, stop} <- stop_ex(plan.stop, plan.acc, names) do
      hot_src(arg, plan.ks, z, body, stop)
    else
      _ -> nil
    end
  end

  def needle_acc(bin, bytes, delta, accept) when is_binary(bin) and is_list(bytes) do
    len = length(bytes)
    needle = IO.iodata_to_binary(bytes)
    n = byte_size(bin)

    case :binary.match(bin, needle) do
      {pos, ^len} ->
        pack(accept, pos + len)

      :nomatch ->
        start = if n > len - 1, do: n - (len - 1), else: 0
        tail_acc(bin, start, n, 0, delta, accept)
    end
  end

  defp build(book, image, names) do
    shared = Muro.IR.Share.funs(image, [])
    looped = Muro.IR.Loop.funs(shared, book: book)
    by = Map.new(looped, &{&1.name, &1})

    Enum.reduce(looped, %{}, fn fun, acc ->
      if Map.get(fun, :generated, false) do
        acc
      else
        case of_fun(by, looped, names, fun) do
          nil -> acc
          plan -> Map.put(acc, fun.name, plan)
        end
      end
    end)
  end

  defp of_fun(by, funs, names, %{body: {:loop, _, _, _, _, _, _, _, _} = loop} = fun) do
    params = Enum.map(fun.params, &IR.param_name/1)
    placeholders = Enum.with_index(params, fn _, i -> "muro__p#{i}" end)

    needle_try(by, funs, names, params, placeholders, loop) ||
      hot_try(by, funs, names, params, placeholders, loop, :keep) ||
      hot_try(by, funs, names, params, placeholders, loop, :drop)
  end

  defp of_fun(_, _, _, _), do: nil

  defp needle_try(by, funs, names, params, placeholders, loop) do
    {:loop, caps, {on, _, _}, {rn, _, _}, {an, :u64, _}, z, s, _stop, body} = loop

    with [] <- caps,
         false <- uses?(body, rn),
         {:var, param} <- s,
         {:ok, bytes, delta, accept} <- needle_table(z, body, on, an, %{funs: by}),
         plan =
           {:needle, %{bytes: bytes, delta: delta, accept: accept, param: param, params: params}},
         true <- needle_ok?(funs, loop, plan),
         src when is_binary(src) <- render(plan, placeholders, names) do
      plan
    else
      _ -> nil
    end
  rescue
    _ -> nil
  end

  defp hot_try(by, funs, names, params, placeholders, loop, stop_mode) do
    {:loop, caps, {on, _, _}, {rn, _, _}, {an, _, _}, z, s, stop, body} = loop
    stop = if stop_mode == :drop, do: :none, else: stop

    with {:var, param} <- s,
         {:ok, ks} <- hot_bytes(body, on, an, by),
         true <- hot_ok?(funs, loop, ks),
         plan =
           {:hot,
            %{
              ks: ks,
              param: param,
              params: params,
              caps: caps,
              z: z,
              body: body,
              stop: stop,
              oct: on,
              rest: rn,
              acc: an
            }},
         src when is_binary(src) <- render(plan, placeholders, names) do
      plan
    else
      _ -> nil
    end
  rescue
    _ -> nil
  end

  defp needle_ok?(
         funs,
         loop,
         {:needle, %{bytes: bytes, delta: delta, accept: accept, param: param}}
       ) do
    Enum.all?(needle_samples(bytes), fn bin ->
      case Muro.IR.Eval.eval(funs, loop, %{param => {:bytes, bin}}, fuel: @fuel) do
        {:ok, {:word, :u64, n}} -> n == needle_acc(bin, bytes, delta, accept)
        _ -> false
      end
    end)
  end

  defp hot_ok?(funs, {:loop, _, _, _, _, _, {:var, param}, _, _} = loop, ks) do
    Enum.all?(hot_samples(), fn bin ->
      full = Muro.IR.Eval.eval(funs, loop, %{param => {:bytes, bin}}, fuel: @fuel)
      sim = hot_sim(funs, loop, bin, ks)

      case {full, sim} do
        {{:ok, v}, {:ok, v}} -> true
        _ -> false
      end
    end)
  end

  defp hot_ok?(_, _, _), do: false

  defp needle_samples(bytes) do
    needle = IO.iodata_to_binary(bytes)
    len = length(bytes)
    head = IO.iodata_to_binary(Enum.take(bytes, max(len - 1, 0)))

    Enum.uniq(
      [
        "",
        needle,
        needle <> needle,
        head,
        :binary.copy(<<0>>, 40) <> needle,
        needle <> :binary.copy(<<0>>, 40),
        <<0>>,
        <<255>>,
        :binary.copy(<<hd(bytes)>>, 12)
      ] ++ for(b <- [0, 1, 9, 10, 13, 32, 58, 255], do: <<b>>)
    )
  end

  defp hot_samples do
    header = "GET /hello HTTP/1.1\r\nHost: x\r\n\r\n"

    [
      "",
      "a",
      "\n",
      ":",
      "\r\n",
      "a:b\r\n",
      "a:b\r\nc:d\r\n",
      header,
      header <> :binary.copy("a", 64),
      header <> :binary.copy("\n", 30),
      "GET /a:b HTTP/1.1\r\nHost: x\r\n\r\n",
      :binary.copy(":", 8),
      :binary.copy("\n", 8),
      <<0, 10, 58, 255>>,
      "xxxx\r\n\r\n" <> :binary.copy("y", 20)
    ]
  end

  defp hot_sim(
         funs,
         {:loop, caps, {on, _, _}, {rn, _, _}, {an, _, _}, z, {:var, param}, stop, body},
         bin,
         ks
       ) do
    env = %{param => {:bytes, bin}}

    with {:ok, cvs} <- eval_list(funs, Enum.map(caps, &elem(&1, 3)), env),
         {:ok, zv} <- ev1(funs, z, env) do
      base = caps |> Enum.map(&elem(&1, 0)) |> Enum.zip(cvs) |> Map.new()
      pat = :binary.compile_pattern(Enum.map(ks, &<<&1>>))
      walk(funs, base, on, rn, an, stop, body, zv, bin, pat, 0)
    else
      _ -> :no
    end
  end

  defp walk(_funs, _base, _on, _rn, _an, _stop, _body, acc, bin, _pat, off)
       when off >= byte_size(bin),
       do: {:ok, acc}

  defp walk(funs, base, on, rn, an, stop, body, acc, bin, pat, off) do
    n = byte_size(bin)

    if stop?(funs, stop, an, acc) do
      {:ok, acc}
    else
      case :binary.match(bin, pat, scope: {off, n - off}) do
        :nomatch ->
          {:ok, acc}

        {pos, 1} ->
          b = :binary.at(bin, pos)
          rest = :binary.part(bin, pos + 1, n - pos - 1)

          env =
            base
            |> Map.put(on, {:word, :u8, b})
            |> Map.put(rn, {:bytes, rest})
            |> Map.put(an, acc)

          case ev1(funs, body, env) do
            {:ok, acc2} -> walk(funs, base, on, rn, an, stop, body, acc2, bin, pat, pos + 1)
            :no -> :no
          end
      end
    end
  end

  defp stop?(_funs, :none, _an, _acc), do: false

  defp stop?(funs, {v, test}, _an, acc) do
    case ev1(funs, test, %{v => acc}) do
      {:ok, {:word, :u64, 1}} -> true
      {:ok, {:word, :u64, 0}} -> false
      _ -> true
    end
  end

  defp eval_list(funs, terms, env) do
    Enum.reduce_while(terms, {:ok, []}, fn t, {:ok, acc} ->
      case ev1(funs, t, env) do
        {:ok, v} -> {:cont, {:ok, [v | acc]}}
        :no -> {:halt, :no}
      end
    end)
    |> case do
      {:ok, vs} -> {:ok, Enum.reverse(vs)}
      :no -> :no
    end
  end

  defp ev1(funs, term, env) do
    case Muro.IR.Eval.eval(funs, term, env, fuel: @fuel) do
      {:ok, v} -> {:ok, v}
      _ -> :no
    end
  end

  defp tail_acc(_bin, i, n, st, _delta, _accept) when i >= n, do: pack(st, n)

  defp tail_acc(bin, i, n, st, delta, accept) do
    b = :binary.at(bin, i)
    next = Map.fetch!(delta, {st, b})

    if next == accept do
      pack(accept, i + 1)
    else
      tail_acc(bin, i + 1, n, next, delta, accept)
    end
  end

  defp pack(st, ix) do
    Bitwise.band(Bitwise.bor(Bitwise.band(st, 7), Bitwise.bsl(ix, 3)), @mask)
  end

  defp arg_src(params, param, args) do
    case Enum.find_index(params, &(&1 == param)) do
      nil ->
        nil

      i ->
        case Enum.at(args, i) do
          name when is_binary(name) and name != "_" -> name
          _ -> nil
        end
    end
  end

  defp param_env(params, args) do
    params |> Enum.zip(args) |> Map.new()
  end

  defp body_env(plan, args, names) do
    base = param_env(plan.params, args)

    Enum.reduce_while(plan.caps, {:ok, base}, fn {cname, _lay, _g, tm}, {:ok, env} ->
      case ex(tm, base, names) do
        {:ok, src} -> {:cont, {:ok, Map.put(env, cname, src)}}
        :no -> {:halt, :no}
      end
    end)
    |> case do
      {:ok, env} ->
        {:ok,
         env
         |> Map.put(plan.oct, "muro__b")
         |> Map.put(plan.rest, "muro__r")
         |> Map.put(plan.acc, "muro__acc")}

      :no ->
        :no
    end
  end

  defp stop_ex(:none, _acc, _names), do: {:ok, nil}

  defp stop_ex({v, test}, acc, names) when v == acc do
    ex(test, %{v => "muro__acc"}, names)
  end

  defp stop_ex(_, _, _), do: :no

  defp needle_src(arg, %{bytes: bytes, delta: delta, accept: accept}) do
    lit = Enum.join(bytes, ", ")
    len = length(bytes)
    tail = len - 1

    """
    (fn muro__s ->
      muro__n = byte_size(muro__s)
      case :binary.match(muro__s, <<#{lit}>>) do
        {muro__pos, #{len}} ->
          Bitwise.band(Bitwise.bor(#{accept}, Bitwise.bsl(muro__pos + #{len}, 3)), 0xFFFFFFFFFFFFFFFF)
        :nomatch ->
          muro__start = if muro__n > #{tail}, do: muro__n - #{tail}, else: 0
          muro__go = fn muro__go, muro__st, muro__i ->
            if muro__i >= muro__n do
              Bitwise.band(Bitwise.bor(muro__st, Bitwise.bsl(muro__n, 3)), 0xFFFFFFFFFFFFFFFF)
            else
              muro__b = :binary.at(muro__s, muro__i)
              muro__nx = case muro__st do
    #{trans_src(delta, accept)}
                _ -> muro__st
              end
              if muro__nx == #{accept} do
                Bitwise.band(Bitwise.bor(#{accept}, Bitwise.bsl(muro__i + 1, 3)), 0xFFFFFFFFFFFFFFFF)
              else
                muro__go.(muro__go, muro__nx, muro__i + 1)
              end
            end
          end
          muro__go.(muro__go, 0, muro__start)
      end
    end).(#{arg})
    """
    |> String.trim()
  end

  defp trans_src(delta, accept) do
    Enum.map_join(0..(accept - 1), "\n", fn s ->
      groups = Enum.group_by(0..255, fn b -> Map.fetch!(delta, {s, b}) end)
      {default, _} = Enum.max_by(groups, fn {n, bs} -> {length(bs), -n} end)

      specials =
        groups
        |> Enum.reject(fn {n, _} -> n == default end)
        |> Enum.flat_map(fn {n, bs} -> Enum.map(bs, &{&1, n}) end)
        |> Enum.sort()

      inner =
        if specials == [] do
          Integer.to_string(default)
        else
          rows = Enum.map_join(specials, "\n", fn {b, n} -> "            #{b} -> #{n}" end)

          """
          case muro__b do
          #{rows}
                    _ -> #{default}
                  end
          """
          |> String.trim()
        end

      "          #{s} -> #{inner}"
    end)
  end

  defp rest_bind(body) do
    if String.contains?(body, "muro__r") do
      "muro__r = :binary.part(muro__bin, muro__pos + 1, muro__n - muro__pos - 1)\n              "
    else
      ""
    end
  end

  defp hot_src(arg, ks, z, body, stop) do
    bins = Enum.map_join(ks, ", ", &"<<#{&1}>>")

    cond =
      if stop do
        "muro__off >= muro__n or (#{stop}) == 1"
      else
        "muro__off >= muro__n"
      end

    """
    (fn muro__bin ->
      muro__n = byte_size(muro__bin)
      muro__pat = :binary.compile_pattern([#{bins}])
      muro__go = fn muro__go, muro__acc, muro__off ->
        if #{cond} do
          muro__acc
        else
          case :binary.match(muro__bin, muro__pat, scope: {muro__off, muro__n - muro__off}) do
            :nomatch ->
              muro__acc
            {muro__pos, 1} ->
              muro__b = :binary.at(muro__bin, muro__pos)
              #{rest_bind(body)}muro__acc2 = #{body}
              muro__go.(muro__go, muro__acc2, muro__pos + 1)
          end
        end
      end
      muro__go.(muro__go, #{z}, 0)
    end).(#{arg})
    """
    |> String.trim()
  end

  defp ex({:var, x}, env, _names) do
    case Map.fetch(env, x) do
      {:ok, src} when is_binary(src) -> {:ok, src}
      _ -> :no
    end
  end

  defp ex({:call, f, args}, env, names) do
    with {:ok, xs} <- exs(args, env, names),
         {:ok, fun} <- Map.fetch(names, f) do
      {:ok, "#{fun}(#{Enum.join(xs, ", ")})"}
    else
      _ -> :no
    end
  end

  defp ex({:inout, f, args}, env, names), do: ex({:call, f, args}, env, names)

  defp ex({:wrd, _, {:lit, _, n}, []}, _env, _names) when is_integer(n) and n >= 0,
    do: {:ok, Integer.to_string(n)}

  defp ex({:con, _data, ctor, []}, _env, _names),
    do: {:ok, ":" <> Muro.Emit.elixir_atom_name(ctor)}

  defp ex({:con, _data, ctor, fields}, env, names) do
    with {:ok, xs} <- exs(fields, env, names) do
      {:ok, "{:#{Muro.Emit.elixir_atom_name(ctor)}, #{Enum.join(xs, ", ")}}"}
    end
  end

  defp ex({:match, scrut, arms}, env, names) when is_list(arms) do
    with {:ok, s} <- ex(scrut, env, names),
         {:ok, rows} <- arm_rows(arms, env, names) do
      {:ok, "case #{s} do #{rows} end"}
    end
  end

  defp ex({:match, scrut, _lay, arms}, env, names) when is_list(arms),
    do: ex({:match, scrut, arms}, env, names)

  defp ex(_, _, _), do: :no

  defp exs(args, env, names) do
    Enum.reduce_while(args, {:ok, []}, fn a, {:ok, acc} ->
      case ex(a, env, names) do
        {:ok, s} -> {:cont, {:ok, [s | acc]}}
        :no -> {:halt, :no}
      end
    end)
    |> case do
      {:ok, xs} -> {:ok, Enum.reverse(xs)}
      :no -> :no
    end
  end

  defp arm_rows(arms, env, names) do
    Enum.reduce_while(arms, {:ok, []}, fn arm, {:ok, acc} ->
      case arm_row(arm, env, names) do
        {:ok, row} -> {:cont, {:ok, [row | acc]}}
        :no -> {:halt, :no}
      end
    end)
    |> case do
      {:ok, rows} -> {:ok, rows |> Enum.reverse() |> Enum.join("; ")}
      :no -> :no
    end
  end

  defp arm_row({:arm, ctor, fields, body}, env, names) when is_list(fields) do
    env2 =
      Enum.reduce_while(fields, {:ok, env}, fn f, {:ok, e} ->
        case var_src(f) do
          nil -> {:halt, :no}
          src -> {:cont, {:ok, Map.put(e, f, src)}}
        end
      end)

    with {:ok, env2} <- env2,
         {:ok, b} <- ex(body, env2, names) do
      {:ok, "#{pat(ctor, fields, b)} -> #{b}"}
    end
  end

  defp arm_row(_, _, _), do: :no

  defp pat(ctor, [], _body), do: ":" <> Muro.Emit.elixir_atom_name(ctor)

  defp pat(ctor, fields, body) do
    names = Enum.map_join(fields, ", ", &pat_field(&1, body))
    "{:#{Muro.Emit.elixir_atom_name(ctor)}, #{names}}"
  end

  defp pat_field(f, body) do
    src = var_src(f)

    if Regex.match?(~r/(^|[^A-Za-z0-9_])#{Regex.escape(src)}([^A-Za-z0-9_]|$)/, body) do
      src
    else
      if String.starts_with?(src, "_"), do: src, else: "_" <> src
    end
  end

  defp var_src(name) do
    if String.match?(name, ~r/^[a-z_][A-Za-z0-9_]*$/), do: name, else: nil
  end

  defp mentions_fold?(term) do
    case term do
      {:bfold, _, _, _, _} ->
        true

      {:afold, _, _, _, _} ->
        true

      t when is_tuple(t) ->
        t |> Tuple.to_list() |> Enum.any?(&mentions_fold?/1)

      t when is_list(t) ->
        Enum.any?(t, &mentions_fold?/1)

      t when is_map(t) ->
        Enum.any?(Map.to_list(t), fn {k, v} -> mentions_fold?(k) or mentions_fold?(v) end)

      _ ->
        false
    end
  end

  # A loop's body sees only the loop's binders. Same walk as `Muro.Emit.C`.
  defp uses?({:loop, caps, _o, _r, _a, z, s, _stop, _body}, name),
    do: uses?([Enum.map(caps, &elem(&1, 3)), z, s], name)

  defp uses?(t, name) when is_tuple(t) do
    t == {:var, name} or t |> Tuple.to_list() |> Enum.any?(&uses?(&1, name))
  end

  defp uses?(t, name) when is_list(t), do: Enum.any?(t, &uses?(&1, name))
  defp uses?(_, _), do: false

  defp needle_table(z, body, on, an, st) do
    funs = Map.values(st.funs)

    with {:ok, {:word, :u64, 0}} <- Muro.IR.Eval.eval(funs, z, %{}, fuel: 8_000),
         true <- index_plain?(st.funs, body, on, an),
         {:ok, delta, accept} <- probe_states(funs, body, on, an),
         {:ok, bytes} <- chain_needle(delta, accept),
         true <- border_matches?(bytes, delta, accept) do
      {:ok, bytes, delta, accept}
    else
      _ -> :no
    end
  end

  defp probe_states(funs, body, on, an) do
    walk_states([0], MapSet.new(), %{}, nil, funs, body, on, an)
  end

  defp walk_states([], _seen, _delta, nil, _funs, _body, _on, _an), do: :no

  defp walk_states([], _seen, delta, accept, _funs, _body, _on, _an),
    do: {:ok, delta, accept}

  defp walk_states([s | rest], seen, delta, accept, funs, body, on, an) do
    cond do
      s > 7 or MapSet.member?(seen, s) ->
        walk_states(rest, seen, delta, accept, funs, body, on, an)

      true ->
        seen = MapSet.put(seen, s)

        case classify_state(s, funs, body, on, an) do
          :no ->
            :no

          :absorb ->
            if accept == nil do
              walk_states(rest, seen, delta, s, funs, body, on, an)
            else
              :no
            end

          {:move, map} ->
            delta = Enum.reduce(map, delta, fn {b, n}, d -> Map.put(d, {s, b}, n) end)
            more = map |> Map.values() |> Enum.uniq()
            walk_states(rest ++ more, seen, delta, accept, funs, body, on, an)
        end
    end
  end

  # One index is not enough. A step gated on that index matches the
  # border table there and nowhere else, and the scan would disagree
  # with the byte loop. The low three bits, and whether the state
  # absorbs, have to be the same at every probed index. A move advances
  # the high bits by exactly one.
  @probe_indices [0, 1, 5, 40]

  defp classify_state(s, funs, body, on, an) do
    Enum.reduce_while(@probe_indices, :start, fn ix, prev ->
      case classify_at(s, funs, body, on, an, ix) do
        :no -> {:halt, :no}
        class when prev == :start -> {:cont, class}
        ^prev -> {:cont, prev}
        _ -> {:halt, :no}
      end
    end)
    |> case do
      :start -> :no
      class -> class
    end
  end

  defp classify_at(s, funs, body, on, an, ix) do
    acc = Bitwise.bor(Bitwise.band(s, 7), Bitwise.bsl(ix, 3))

    0..255
    |> Enum.reduce_while({:same, %{}}, fn b, {mode, map} ->
      case probe_step(funs, body, on, an, b, acc) do
        {:ok, ^acc} ->
          if mode == :move, do: {:halt, :no}, else: {:cont, {:same, map}}

        {:ok, r} ->
          next = Bitwise.band(r, 7)

          if Bitwise.bsr(r, 3) == ix + 1 and mode in [:same, :move] do
            {:cont, {:move, Map.put(map, b, next)}}
          else
            {:halt, :no}
          end

        :no ->
          {:halt, :no}
      end
    end)
    |> case do
      {:same, _} -> :absorb
      {:move, map} when map_size(map) == 256 -> {:move, map}
      _ -> :no
    end
  end

  defp probe_step(funs, body, on, an, byte, acc) do
    env = %{on => {:word, :u8, byte}, an => {:word, :u64, acc}}

    case Muro.IR.Eval.eval(funs, body, env, fuel: 8_000) do
      {:ok, {:word, :u64, n}} when is_integer(n) and n >= 0 -> {:ok, n}
      _ -> :no
    end
  end

  # The high bits of the accumulator are the index. A pass-through
  # reads them only to add one and pack them back (`endIx`, `+ 1`,
  # `packEnd`), and a condition never reads them. The value packed
  # beside them depends on the low three bits, the octet, and
  # constants. Returning the accumulator unchanged is the absorbing
  # state. Anything else, including a term this walk does not know,
  # is not a pass-through.
  defp index_plain?(funs, body, on, an) when is_map(funs) do
    st = %{fuel: 8_000, depth: 0, cache: %{}}

    case abs_ev(funs, body, %{on => :byte, an => :acc}, st) do
      {:ok, v, _} -> v in [:acc, :packed, :step]
      :no -> false
    end
  end

  defp abs_ev(_funs, _tm, _env, %{fuel: fuel}) when fuel <= 0, do: :no

  defp abs_ev(funs, tm, env, st), do: abs_term(funs, tm, env, %{st | fuel: st.fuel - 1})

  defp abs_term(_funs, {:var, x}, env, st) do
    case Map.fetch(env, x) do
      {:ok, v} -> {:ok, v, st}
      :error -> :no
    end
  end

  defp abs_term(_funs, :ze, _env, st), do: {:ok, {:k, 0}, st}

  defp abs_term(_funs, {:nat, n}, _env, st) when is_integer(n) and n >= 0,
    do: {:ok, {:k, n}, st}

  defp abs_term(funs, {:su, t}, env, st) do
    case abs_ev(funs, t, env, st) do
      {:ok, {:k, n}, st} -> {:ok, {:k, n + 1}, st}
      _ -> :no
    end
  end

  defp abs_term(funs, {:let, x, _lay, _g, val, body}, env, st) when is_binary(x) do
    case abs_ev(funs, val, env, st) do
      {:ok, v, st} -> abs_ev(funs, body, Map.put(env, x, v), st)
      :no -> :no
    end
  end

  defp abs_term(funs, {:let, x, lay, val, body}, env, st) when is_binary(x),
    do: abs_term(funs, {:let, x, lay, :reuse, val, body}, env, st)

  defp abs_term(funs, {:call, name, args}, env, st) do
    with {:ok, vs, st} <- abs_list(funs, args, env, st),
         %{} = fun <- Map.get(funs, name),
         true <- st.depth < 12,
         true <- length(fun.params) == length(vs) do
      key = {name, vs}

      case Map.get(st.cache, key) do
        :pending ->
          :no

        v when v != nil ->
          {:ok, v, st}

        nil ->
          bound =
            fun.params
            |> Enum.zip(vs)
            |> Map.new(fn {p, v} -> {param_nm(p), v} end)

          inner = %{st | depth: st.depth + 1, cache: Map.put(st.cache, key, :pending)}

          case abs_ev(funs, fun.body, bound, inner) do
            {:ok, v, st3} ->
              {:ok, v, %{st3 | depth: st.depth, cache: Map.put(st3.cache, key, v)}}

            :no ->
              :no
          end
      end
    else
      _ -> :no
    end
  end

  defp abs_term(funs, {:inout, name, args}, env, st),
    do: abs_term(funs, {:call, name, args}, env, st)

  defp abs_term(funs, {:match, scrut, arms}, env, st) when is_list(arms) do
    case abs_ev(funs, scrut, env, st) do
      {:ok, v, st} -> abs_match(funs, v, arms, env, st)
      :no -> :no
    end
  end

  defp abs_term(funs, {:match, scrut, _lay, arms}, env, st) when is_list(arms),
    do: abs_term(funs, {:match, scrut, arms}, env, st)

  defp abs_term(funs, {:wrd, _k, op, args}, env, st) do
    case abs_list(funs, args, env, st) do
      {:ok, vs, st} ->
        case abs_wrd(op, vs) do
          :no -> :no
          v -> {:ok, v, st}
        end

      :no ->
        :no
    end
  end

  defp abs_term(funs, {:con, data, ctor, ts}, env, st) do
    case abs_list(funs, ts, env, st) do
      {:ok, vs, st} -> {:ok, {:con, data, ctor, vs}, st}
      :no -> :no
    end
  end

  defp abs_term(_funs, _tm, _env, _st), do: :no

  defp abs_list(funs, ts, env, st) do
    Enum.reduce_while(ts, {:ok, [], st}, fn t, {:ok, acc, st} ->
      case abs_ev(funs, t, env, st) do
        {:ok, v, st} -> {:cont, {:ok, [v | acc], st}}
        :no -> {:halt, :no}
      end
    end)
    |> case do
      {:ok, vs, st} -> {:ok, Enum.reverse(vs), st}
      :no -> :no
    end
  end

  defp param_nm({n, _, _}), do: n
  defp param_nm({n, _}), do: n

  defp abs_match(_funs, :bool_ix, _arms, _env, _st), do: :no
  defp abs_match(_funs, :taint, _arms, _env, _st), do: :no

  defp abs_match(funs, :bool_ok, arms, env, st),
    do: abs_both(funs, arms, "wtrue", "wfalse", env, st)

  defp abs_match(funs, true, arms, env, st), do: abs_arm(funs, arms, "wtrue", [], env, st)
  defp abs_match(funs, false, arms, env, st), do: abs_arm(funs, arms, "wfalse", [], env, st)

  defp abs_match(funs, {:either_con, "Bool"}, arms, env, st),
    do: abs_both(funs, arms, "true", "false", env, st)

  defp abs_match(funs, {:con, _, ctor, fields}, arms, env, st),
    do: abs_arm(funs, arms, ctor, fields, env, st)

  defp abs_match(funs, {:some, v}, arms, env, st),
    do: abs_arm(funs, arms, "wsome", [v], env, st)

  defp abs_match(funs, :none, arms, env, st),
    do: abs_arm(funs, arms, "wnone", [], env, st)

  defp abs_match(_funs, _v, _arms, _env, _st), do: :no

  defp abs_both(funs, arms, a, b, env, st) do
    with {:arm, _, [], ba} <- Enum.find(arms, fn {:arm, c, _, _} -> c == a end),
         {:arm, _, [], bb} <- Enum.find(arms, fn {:arm, c, _, _} -> c == b end),
         {:ok, va, st} <- abs_ev(funs, ba, env, st),
         {:ok, vb, st} <- abs_ev(funs, bb, env, st),
         {:ok, joined} <- abs_join(va, vb) do
      {:ok, joined, st}
    else
      _ -> :no
    end
  end

  defp abs_arm(funs, arms, ctor, fields, env, st) do
    case Enum.find(arms, fn {:arm, c, _, _} -> c == ctor end) do
      {:arm, _, names, body} when length(names) == length(fields) ->
        env =
          names
          |> Enum.zip(fields)
          |> Enum.reduce(env, fn {n, f}, e -> Map.put(e, n, f) end)

        abs_ev(funs, body, env, st)

      _ ->
        :no
    end
  end

  defp abs_join(v, v), do: {:ok, v}
  defp abs_join(:acc, :packed), do: {:ok, :step}
  defp abs_join(:packed, :acc), do: {:ok, :step}
  defp abs_join(:step, :acc), do: {:ok, :step}
  defp abs_join(:acc, :step), do: {:ok, :step}
  defp abs_join(:step, :packed), do: {:ok, :step}
  defp abs_join(:packed, :step), do: {:ok, :step}
  defp abs_join(true, false), do: {:ok, :bool_ok}
  defp abs_join(false, true), do: {:ok, :bool_ok}
  defp abs_join(:bool_ok, v) when v in [true, false, :bool_ok], do: {:ok, :bool_ok}
  defp abs_join(v, :bool_ok) when v in [true, false], do: {:ok, :bool_ok}
  defp abs_join({:k, a}, {:k, b}) when a in 0..7 and b in 0..7, do: {:ok, :low3}
  defp abs_join({:k, a}, :low3) when a in 0..7, do: {:ok, :low3}
  defp abs_join(:low3, {:k, a}) when a in 0..7, do: {:ok, :low3}
  defp abs_join({:con, d, _, []}, {:con, d, _, []}), do: {:ok, {:either_con, d}}
  defp abs_join({:either_con, d}, {:con, d, _, []}), do: {:ok, {:either_con, d}}
  defp abs_join({:con, d, _, []}, {:either_con, d}), do: {:ok, {:either_con, d}}
  defp abs_join(_, _), do: :no

  defp abs_wrd({:lit, _k, n}, []) when is_integer(n) and n >= 0, do: {:k, n}
  defp abs_wrd(true, []), do: true
  defp abs_wrd(false, []), do: false
  defp abs_wrd(:none, []), do: :none
  defp abs_wrd(:some, [v]), do: {:some, v}
  defp abs_wrd({:of, _}, [{:k, n}]), do: {:k, n}
  defp abs_wrd(:and, [a, b]), do: abs_and(a, b)
  defp abs_wrd(:or, [a, b]), do: abs_or(a, b)
  defp abs_wrd(:add, [a, b]), do: abs_add(a, b)
  defp abs_wrd(:mul, [a, b]), do: abs_mul(a, b)
  defp abs_wrd(:div, [a, b]), do: abs_div(a, b)
  defp abs_wrd(:eq, [a, b]), do: abs_cmp(a, b, :eq)
  defp abs_wrd(:lt, [a, b]), do: abs_cmp(a, b, :lt)
  defp abs_wrd(:le, [a, b]), do: abs_cmp(a, b, :le)
  defp abs_wrd(:shr, [a, n]), do: abs_shr(a, n)
  defp abs_wrd(:shl, [a, n]), do: abs_shl(a, n)
  defp abs_wrd(:not, [{:k, n}]), do: {:k, Bitwise.band(Bitwise.bnot(n), 0xFFFFFFFFFFFFFFFF)}
  defp abs_wrd(_op, _vs), do: :no

  defp abs_and({:k, a}, {:k, b}), do: {:k, Bitwise.band(a, b)}
  defp abs_and(:acc, {:k, m}) when m in 0..7, do: :low3
  defp abs_and({:k, m}, :acc) when m in 0..7, do: :low3
  defp abs_and(:low3, {:k, _}), do: :low3
  defp abs_and({:k, _}, :low3), do: :low3
  defp abs_and(:low3, :low3), do: :low3
  defp abs_and(:low3, :byte), do: :low3
  defp abs_and(:byte, :low3), do: :low3
  defp abs_and(:byte, {:k, m}) when m in 0..7, do: :low3
  defp abs_and({:k, m}, :byte) when m in 0..7, do: :low3
  defp abs_and(:pure, {:k, m}) when m in 0..7, do: :low3
  defp abs_and({:k, m}, :pure) when m in 0..7, do: :low3
  defp abs_and(:packed, {:k, m}) when m in 0..7, do: :low3
  defp abs_and({:k, m}, :packed) when m in 0..7, do: :low3
  defp abs_and(:hipack, {:k, m}) when m in 0..7, do: {:k, 0}
  defp abs_and({:k, m}, :hipack) when m in 0..7, do: {:k, 0}
  defp abs_and(_, _), do: :no

  defp abs_or({:k, a}, {:k, b}), do: {:k, Bitwise.bor(a, b)}
  defp abs_or(:low3, :hipack), do: :packed
  defp abs_or(:hipack, :low3), do: :packed
  defp abs_or({:k, n}, :hipack) when n in 0..7, do: :packed
  defp abs_or(:hipack, {:k, n}) when n in 0..7, do: :packed
  defp abs_or(:low3, :low3), do: :low3
  defp abs_or({:k, n}, :low3) when n in 0..7, do: :low3
  defp abs_or(:low3, {:k, n}) when n in 0..7, do: :low3
  defp abs_or(_, _), do: :no

  defp abs_add({:k, a}, {:k, b}), do: {:k, Bitwise.band(a + b, 0xFFFFFFFFFFFFFFFF)}
  defp abs_add(:ix, {:k, 1}), do: :ix1
  defp abs_add({:k, 1}, :ix), do: :ix1
  defp abs_add(:low3, {:k, n}) when n in 0..7, do: :pure
  defp abs_add({:k, n}, :low3) when n in 0..7, do: :pure
  defp abs_add(:pure, {:k, _}), do: :pure
  defp abs_add({:k, _}, :pure), do: :pure
  defp abs_add(:byte, {:k, _}), do: :pure
  defp abs_add({:k, _}, :byte), do: :pure
  defp abs_add(_, _), do: :no

  defp abs_mul({:k, a}, {:k, b}), do: {:k, Bitwise.band(a * b, 0xFFFFFFFFFFFFFFFF)}
  defp abs_mul(:ix1, {:k, 8}), do: :hipack
  defp abs_mul({:k, 8}, :ix1), do: :hipack
  defp abs_mul(_, _), do: :no

  defp abs_div(_a, {:k, 0}), do: :none
  defp abs_div({:k, n}, {:k, d}) when d > 0, do: {:some, {:k, div(n, d)}}
  defp abs_div(:acc, {:k, 8}), do: {:some, :ix}
  defp abs_div(:packed, {:k, 8}), do: {:some, :ix1}
  defp abs_div(:hipack, {:k, 8}), do: {:some, :ix1}
  defp abs_div(:low3, {:k, d}) when d >= 8, do: {:some, {:k, 0}}
  defp abs_div(:byte, {:k, d}) when d > 0, do: {:some, :pure}
  defp abs_div(:pure, {:k, d}) when d > 0, do: {:some, :pure}
  defp abs_div(_, _), do: :no

  defp abs_cmp({:k, a}, {:k, b}, :eq), do: a == b
  defp abs_cmp({:k, a}, {:k, b}, :lt), do: a < b
  defp abs_cmp({:k, a}, {:k, b}, :le), do: a <= b

  defp abs_cmp(a, b, _op) do
    if idx_dep?(a) or idx_dep?(b), do: :bool_ix, else: :bool_ok
  end

  defp abs_shr(:acc, {:k, 3}), do: :ix
  defp abs_shr(:packed, {:k, 3}), do: :ix1
  defp abs_shr(:hipack, {:k, 3}), do: :ix1
  defp abs_shr({:k, n}, {:k, s}) when s in 0..63, do: {:k, Bitwise.bsr(n, s)}
  defp abs_shr(_, _), do: :no

  defp abs_shl(:ix1, {:k, 3}), do: :hipack

  defp abs_shl({:k, n}, {:k, s}) when s in 0..63,
    do: {:k, Bitwise.band(Bitwise.bsl(n, s), 0xFFFFFFFFFFFFFFFF)}

  defp abs_shl(_, _), do: :no

  defp idx_dep?(v) when v in [:acc, :ix, :ix1, :hipack, :packed, :step, :taint, :bool_ix],
    do: true

  defp idx_dep?({:some, v}), do: idx_dep?(v)
  defp idx_dep?(_), do: false

  defp chain_needle(delta, accept) when is_integer(accept) and accept >= 2 and accept <= 7 do
    0..(accept - 1)
    |> Enum.reduce_while([], fn s, acc ->
      bytes = for b <- 0..255, Map.get(delta, {s, b}) == s + 1, do: b

      case bytes do
        [b] -> {:cont, acc ++ [b]}
        _ -> {:halt, :no}
      end
    end)
    |> case do
      bytes when is_list(bytes) and length(bytes) == accept -> {:ok, bytes}
      _ -> :no
    end
  end

  defp chain_needle(_delta, _accept), do: :no

  # `pi` is the border table of the needle. Every reached state has to
  # be that automaton, including a byte that is not the next octet of
  # the needle.
  defp border_matches?(bytes, delta, accept) do
    pi = prefix_borders(bytes)

    covered =
      Enum.all?(0..(accept - 1), fn s -> Enum.all?(0..255, &Map.has_key?(delta, {s, &1})) end)

    covered and
      Enum.all?(delta, fn {{s, b}, n} ->
        s <= accept and border_step(bytes, pi, s, b) == n
      end)
  end

  defp prefix_borders(bytes) do
    m = length(bytes)

    {pi, _} =
      Enum.reduce(1..max(m - 1, 0)//1, {%{0 => 0}, 0}, fn q, {pi, k} ->
        k = drop_border(bytes, pi, k, q)
        k = if Enum.at(bytes, k) == Enum.at(bytes, q), do: k + 1, else: k
        {Map.put(pi, q, k), k}
      end)

    pi
  end

  defp drop_border(bytes, pi, k, q) when k > 0 do
    if Enum.at(bytes, k) == Enum.at(bytes, q),
      do: k,
      else: drop_border(bytes, pi, Map.fetch!(pi, k - 1), q)
  end

  defp drop_border(_bytes, _pi, 0, _q), do: 0

  # The step walks borders against the octet just read. `drop_border/4`
  # walks them against a later needle index, which is how `pi` is built.
  defp fall_border(bytes, pi, k, b) when k > 0 do
    if Enum.at(bytes, k) == b,
      do: k,
      else: fall_border(bytes, pi, Map.fetch!(pi, k - 1), b)
  end

  defp fall_border(_bytes, _pi, 0, _b), do: 0

  defp border_step(bytes, pi, s, b) do
    if s == length(bytes) do
      s
    else
      s = fall_border(bytes, pi, s, b)
      if s < length(bytes) and Enum.at(bytes, s) == b, do: s + 1, else: s
    end
  end

  defp hot_bytes(body, oct, acc, funs) do
    case follow_step(body, oct, acc, funs, 0) do
      {:ok, set} ->
        ks = set |> MapSet.to_list() |> Enum.sort()

        if ks != [] and length(ks) <= 3 and Enum.all?(ks, &(&1 in 0..255)),
          do: {:ok, ks},
          else: :no

      :no ->
        :no
    end
  end

  # Follow a tail call that passes the octet and the accumulator once
  # each, into that callee, and then read the body. A `let` that binds
  # neither is substituted first. Four hops is enough for a fold that
  # names its step; past that the byte loop stays.
  defp follow_step(tm, oct, acc, funs, depth) do
    case peel_lets(tm, oct, acc) do
      :no ->
        :no

      {:ok, {:call, f, args}} ->
        descend_step(f, args, oct, acc, funs, depth)

      {:ok, {:inout, f, args}} ->
        descend_step(f, args, oct, acc, funs, depth)

      {:ok, other} ->
        walk_hot(other, oct, acc, empty_hot(), funs)
    end
  end

  defp descend_step(f, args, oct, acc, funs, depth) do
    with true <- depth < 4,
         %{} = fun <- Map.get(funs, f),
         {:ok, oct2, acc2} <- map_step_params(fun.params, args, oct, acc) do
      follow_step(fun.body, oct2, acc2, funs, depth + 1)
    else
      _ -> walk_hot({:call, f, args}, oct, acc, empty_hot(), funs)
    end
  end

  defp map_step_params(params, args, oct, acc) do
    pairs = Enum.zip(params, args)
    oct_ps = for {p, {:var, ^oct}} <- pairs, do: IR.param_name(p)
    acc_ps = for {p, {:var, ^acc}} <- pairs, do: IR.param_name(p)

    if length(oct_ps) == 1 and length(acc_ps) == 1 and hd(oct_ps) != hd(acc_ps) do
      {:ok, hd(oct_ps), hd(acc_ps)}
    else
      :no
    end
  end

  defp peel_lets({:let, x, _lay, _g, val, body}, oct, acc) do
    if x == oct or x == acc do
      :no
    else
      case peel_lets(body, oct, acc) do
        :no -> :no
        {:ok, inner} -> {:ok, subst_term(inner, x, val)}
      end
    end
  end

  defp peel_lets(tm, _oct, _acc), do: {:ok, tm}

  defp subst_term({:var, x}, x, val), do: val
  defp subst_term({:var, y}, _x, _val), do: {:var, y}

  defp subst_term({:let, z, lay, g, v, b}, x, val) do
    v = subst_term(v, x, val)
    if z == x, do: {:let, z, lay, g, v, b}, else: {:let, z, lay, g, v, subst_term(b, x, val)}
  end

  defp subst_term({:letp, a, b, e, body}, x, val) do
    e = subst_term(e, x, val)

    if x in [a, b],
      do: {:letp, a, b, e, body},
      else: {:letp, a, b, e, subst_term(body, x, val)}
  end

  defp subst_term({:match, scrut, arms}, x, val) when is_list(arms) do
    {:match, subst_term(scrut, x, val), subst_arms(arms, x, val)}
  end

  defp subst_term({:match, scrut, lay, arms}, x, val) when is_list(arms) do
    {:match, subst_term(scrut, x, val), lay, subst_arms(arms, x, val)}
  end

  defp subst_term(t, x, val) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.map(&subst_term(&1, x, val)) |> List.to_tuple()
  end

  defp subst_term(t, x, val) when is_list(t), do: Enum.map(t, &subst_term(&1, x, val))
  defp subst_term(t, _x, _val), do: t

  defp subst_arms(arms, x, val) do
    Enum.map(arms, fn
      {:arm, c, names, tm} = arm ->
        if is_list(names) and x in names, do: arm, else: {:arm, c, names, subst_term(tm, x, val)}

      other ->
        subst_term(other, x, val)
    end)
  end

  defp empty_hot, do: %{eq: nil, neq: MapSet.new(), inset: MapSet.new()}

  # `{:ok, set}` is the bytes a non-identity leaf may see. `:no` means
  # some leaf is reachable with no finite byte, so the fold is not a
  # search for a short set.
  defp walk_hot({:var, name}, _oct, acc, _c, _funs) when name == acc, do: {:ok, MapSet.new()}

  defp walk_hot({:let, x, _lay, _g, val, body}, oct, acc, c, funs) do
    if x == oct or x == acc do
      :no
    else
      walk_hot(subst_term(body, x, val), oct, acc, c, funs)
    end
  end

  defp walk_hot({:match, scrut, arms}, oct, acc, c, funs) when is_list(arms) do
    walk_match_arms(arms, classify(scrut, oct, funs), oct, acc, c, funs)
  end

  defp walk_hot({:match, scrut, _lay, arms}, oct, acc, c, funs) when is_list(arms) do
    walk_hot({:match, scrut, arms}, oct, acc, c, funs)
  end

  defp walk_hot(_tm, _oct, _acc, c, _funs), do: hot_leaf(c)

  defp walk_match_arms(arms, class, oct, acc, c, funs) do
    Enum.reduce_while(arms, {:ok, MapSet.new()}, fn arm, {:ok, accs} ->
      case arm_hot(arm, class, oct, acc, c, funs) do
        :no -> {:halt, :no}
        {:ok, s} -> {:cont, {:ok, MapSet.union(accs, s)}}
      end
    end)
  end

  defp arm_hot({:arm, ctor, binders, body}, class, oct, acc, c, funs) when is_list(binders) do
    if oct in binders or acc in binders do
      :no
    else
      case arm_constraint(class, ctor, c) do
        :dead -> {:ok, MapSet.new()}
        {:ok, c2} -> walk_hot(body, oct, acc, c2, funs)
      end
    end
  end

  defp arm_hot(_, _, _, _, _, _), do: :no

  defp arm_constraint({:bool_eq, k}, "true", c), do: put_eq(c, k)
  defp arm_constraint({:bool_eq, k}, "false", c), do: add_neq(c, k)
  defp arm_constraint({:bool_neq, k}, "true", c), do: add_neq(c, k)
  defp arm_constraint({:bool_neq, k}, "false", c), do: put_eq(c, k)
  defp arm_constraint({:and_byte, k}, "true", c), do: put_eq(c, k)
  defp arm_constraint({:and_byte, _k}, "false", c), do: {:ok, c}
  defp arm_constraint({:byte_in, ks}, "true", c), do: hot_in(c, ks)
  defp arm_constraint({:byte_in, ks}, "false", c), do: add_neq_all(c, ks)
  defp arm_constraint({:wbool_eq, k}, "wtrue", c), do: put_eq(c, k)
  defp arm_constraint({:wbool_eq, k}, "wfalse", c), do: add_neq(c, k)
  defp arm_constraint(_class, _ctor, c), do: {:ok, c}

  defp put_eq(%{eq: eq, neq: neq} = c, k) do
    cond do
      eq == k ->
        {:ok, c}

      eq == nil and not MapSet.member?(neq, k) ->
        {:ok, %{c | eq: k}}

      eq == :in and MapSet.member?(c.inset, k) and not MapSet.member?(neq, k) ->
        {:ok, %{c | eq: k}}

      true ->
        :dead
    end
  end

  defp add_neq(%{eq: k}, k) when is_integer(k), do: :dead

  defp add_neq(%{eq: :in, inset: inset, neq: neq} = c, k) do
    inset = MapSet.delete(inset, k)

    case MapSet.size(inset) do
      0 ->
        :dead

      1 ->
        {:ok, %{c | eq: hd(MapSet.to_list(inset)), inset: MapSet.new(), neq: MapSet.put(neq, k)}}

      _ ->
        {:ok, %{c | inset: inset, neq: MapSet.put(neq, k)}}
    end
  end

  defp add_neq(%{neq: neq} = c, k), do: {:ok, %{c | neq: MapSet.put(neq, k)}}

  defp add_neq_all(c, ks) do
    Enum.reduce_while(ks, {:ok, c}, fn k, {:ok, c} ->
      case add_neq(c, k) do
        :dead -> {:halt, :dead}
        {:ok, c2} -> {:cont, {:ok, c2}}
      end
    end)
  end

  defp hot_in(%{eq: eq, neq: neq, inset: inset} = c, ks) do
    ks = MapSet.difference(ks, neq)

    cond do
      is_integer(eq) and MapSet.member?(ks, eq) ->
        {:ok, c}

      is_integer(eq) ->
        :dead

      eq == :in ->
        both = MapSet.intersection(inset, ks)

        case MapSet.size(both) do
          0 -> :dead
          1 -> {:ok, %{c | eq: hd(MapSet.to_list(both))}}
          _ -> {:ok, %{c | inset: both}}
        end

      MapSet.size(ks) == 0 ->
        :dead

      MapSet.size(ks) == 1 ->
        {:ok, %{c | eq: hd(MapSet.to_list(ks))}}

      true ->
        {:ok, %{c | eq: :in, inset: ks}}
    end
  end

  defp hot_leaf(%{eq: k, neq: neq}) when is_integer(k) do
    if MapSet.member?(neq, k), do: {:ok, MapSet.new()}, else: {:ok, MapSet.new([k])}
  end

  defp hot_leaf(%{eq: :in, inset: inset, neq: neq}) do
    ks = MapSet.difference(inset, neq)
    if MapSet.size(ks) == 0, do: {:ok, MapSet.new()}, else: {:ok, ks}
  end

  defp hot_leaf(_c), do: :no

  # A scrutinee that does not mention the octet constrains the state.
  # Both arms keep the byte constraint they already had. A call the
  # known boolean forms do not match is opened once, when it passes the
  # octet through, so a named test of that octet is still a byte test.
  # Four opens is the limit; a cycle keeps the byte-by-byte loop.
  defp classify(tm, oct, funs), do: classify_at(tm, oct, funs, 0)

  defp classify_at({:let, x, _lay, _g, val, body}, oct, funs, depth) do
    if x == oct, do: :unknown, else: classify_at(subst_term(body, x, val), oct, funs, depth)
  end

  defp classify_at(tm, oct, funs, depth) do
    if uses?(tm, oct), do: classify_byte(tm, oct, funs, depth), else: :state
  end

  defp classify_byte({:call, f, args}, oct, funs, depth) do
    case Map.get(funs, f) do
      %{} = fun ->
        case classify_fun(fun, args, oct, funs, depth) do
          :unknown -> unfold_test(fun, args, oct, funs, depth)
          other -> other
        end

      _ ->
        :unknown
    end
  end

  defp classify_byte({:wrd, :u8, :eq, args}, oct, _funs, _depth) do
    case lit_pair(args, oct) do
      {:ok, k} -> {:wbool_eq, k}
      :no -> :unknown
    end
  end

  defp classify_byte({:match, {:wrd, :u8, :eq, args}, arms}, oct, _funs, _depth) do
    if u8eq_arms?(arms) do
      case lit_pair(args, oct) do
        {:ok, k} -> {:bool_eq, k}
        :no -> :unknown
      end
    else
      :unknown
    end
  end

  defp classify_byte(
         {:match, first,
          [
            {:arm, "true", [], {:con, "Bool", "false", []}},
            {:arm, "false", [], {:con, "Bool", "true", []}}
          ]},
         oct,
         funs,
         depth
       ) do
    classify_not(first, oct, funs, depth)
  end

  defp classify_byte(
         {:match, first,
          [
            {:arm, "true", [], second},
            {:arm, "false", [], {:con, "Bool", "false", []}}
          ]},
         oct,
         funs,
         depth
       ) do
    classify_and(first, second, oct, funs, depth)
  end

  defp classify_byte(
         {:match, first,
          [
            {:arm, "true", [], {:con, "Bool", "true", []}},
            {:arm, "false", [], second}
          ]},
         oct,
         funs,
         depth
       ) do
    classify_or(first, second, oct, funs, depth)
  end

  defp classify_byte(_, _, _, _), do: :unknown

  # Only a callee that takes the octet as exactly one argument, and
  # does not mention it in any other argument, is a test of that octet.
  defp unfold_test(_fun, _args, _oct, _funs, depth) when depth >= 4, do: :unknown

  defp unfold_test(fun, args, oct, funs, depth) do
    case octet_param(fun.params, args, oct) do
      {:ok, pname} -> classify_at(fun.body, pname, funs, depth + 1)
      :no -> :unknown
    end
  end

  defp octet_param(params, args, oct) do
    pairs = Enum.zip(params, args)
    named = for {p, {:var, ^oct}} <- pairs, do: IR.param_name(p)
    others = for {_p, arg} <- pairs, arg != {:var, oct}, do: arg

    if length(named) == 1 and not Enum.any?(others, &uses?(&1, oct)) do
      {:ok, hd(named)}
    else
      :no
    end
  end

  defp classify_fun(fun, args, oct, funs, depth) do
    cond do
      u8eq_fun?(fun) ->
        case lit_pair(args, oct) do
          {:ok, k} -> {:bool_eq, k}
          :no -> :unknown
        end

      and_fun?(fun) and length(args) == 2 ->
        classify_and(Enum.at(args, 0), Enum.at(args, 1), oct, funs, depth)

      or_fun?(fun) and length(args) == 2 ->
        classify_or(Enum.at(args, 0), Enum.at(args, 1), oct, funs, depth)

      not_fun?(fun) and length(args) == 1 ->
        classify_not(hd(args), oct, funs, depth)

      true ->
        :unknown
    end
  end

  defp classify_and(a, b, oct, funs, depth) do
    case {classify_at(a, oct, funs, depth), classify_at(b, oct, funs, depth)} do
      {:state, {:bool_eq, k}} -> {:and_byte, k}
      {{:bool_eq, k}, :state} -> {:and_byte, k}
      {:state, {:wbool_eq, k}} -> {:and_byte, k}
      {{:wbool_eq, k}, :state} -> {:and_byte, k}
      {:state, :state} -> :state
      _ -> :unknown
    end
  end

  defp classify_or(a, b, oct, funs, depth) do
    case {classify_at(a, oct, funs, depth), classify_at(b, oct, funs, depth)} do
      {:state, :state} ->
        :state

      {{:bool_eq, k}, {:bool_eq, m}} ->
        {:byte_in, MapSet.new([k, m])}

      {{:bool_eq, k}, {:byte_in, ks}} ->
        {:byte_in, MapSet.put(ks, k)}

      {{:byte_in, ks}, {:bool_eq, k}} ->
        {:byte_in, MapSet.put(ks, k)}

      {{:byte_in, ks}, {:byte_in, ms}} ->
        {:byte_in, MapSet.union(ks, ms)}

      _ ->
        :unknown
    end
  end

  defp classify_not(a, oct, funs, depth) do
    case classify_at(a, oct, funs, depth) do
      {:bool_eq, k} -> {:bool_neq, k}
      {:wbool_eq, k} -> {:bool_neq, k}
      :state -> :state
      _ -> :unknown
    end
  end

  defp u8eq_fun?(%{
         params: params,
         body: {:match, {:wrd, :u8, :eq, [{:var, a}, {:var, b}]}, arms}
       }) do
    names = Enum.map(params, &IR.param_name/1)
    length(names) == 2 and MapSet.new(names) == MapSet.new([a, b]) and u8eq_arms?(arms)
  end

  defp u8eq_fun?(_), do: false

  defp u8eq_arms?([
         {:arm, "wtrue", [], {:con, "Bool", "true", []}},
         {:arm, "wfalse", [], {:con, "Bool", "false", []}}
       ]),
       do: true

  defp u8eq_arms?(_), do: false

  defp and_fun?(%{
         params: [p, q],
         body:
           {:match, {:var, a},
            [
              {:arm, "true", [], {:var, b}},
              {:arm, "false", [], {:con, "Bool", "false", []}}
            ]}
       }) do
    IR.param_name(p) == a and IR.param_name(q) == b
  end

  defp and_fun?(_), do: false

  defp or_fun?(%{
         params: [p, q],
         body:
           {:match, {:var, a},
            [
              {:arm, "true", [], {:con, "Bool", "true", []}},
              {:arm, "false", [], {:var, b}}
            ]}
       }) do
    IR.param_name(p) == a and IR.param_name(q) == b
  end

  defp or_fun?(_), do: false

  defp not_fun?(%{
         params: [p],
         body:
           {:match, {:var, a},
            [
              {:arm, "true", [], {:con, "Bool", "false", []}},
              {:arm, "false", [], {:con, "Bool", "true", []}}
            ]}
       }) do
    IR.param_name(p) == a
  end

  defp not_fun?(_), do: false

  defp lit_pair([a, b], oct) do
    cond do
      a == {:var, oct} -> u8_lit(b)
      b == {:var, oct} -> u8_lit(a)
      true -> :no
    end
  end

  defp lit_pair(_, _), do: :no

  defp u8_lit({:wrd, :u8, {:lit, :u8, k}, []}) when is_integer(k) and k >= 0 and k <= 255,
    do: {:ok, k}

  defp u8_lit(_), do: :no
end

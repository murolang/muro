defmodule Muro.Emit do
  @moduledoc """
  Emit run definitions to Elixir. Specs and evidence erase.
  A spec never becomes evidence. Evidence never becomes a run.

  A checked run Stream is emitted as `Stream.unfold/2`. The pair in an
  unfold body is `{head, next_seed}`. `uncons` is two replayable views
  (`Enum.take/2` + `Stream.drop/2`); affinity was already checked.

  A `repr` is emitted as `decode_<type>/1`, `decode_<type>/2`, and
  `encode_<type>/2` by `Muro.Repr`, from the same analysis the checker
  used. Decode returns `{:ok, value, table}`. Encode takes that table.
  A book with no `repr` emits the same module text as before.
  """

  alias Muro.Ast
  alias Muro.Emit.Name

  # Words the Elixir parser rejects as function names (`syntax error before: do`).
  @elixir_reserved ~w(
    true false nil
    when and or not in
    fn do end catch rescue after else
  ) |> MapSet.new()

  @doc """
  Run definitions in book order. Data, spec, and evidence are omitted.
  A temporal declaration has mode evidence, so it is omitted here and in
  every backend that reads this list, including Zig.
  `run internal` stays in the list; its `export` flag is false.
  """
  def run_defs(book) when is_list(book) do
    Enum.filter(book, &(Map.get(&1, :kind, :def) != :data and Map.get(&1, :mode) == :run))
  end

  @doc """
  Group each elaborated run with the unfold steps it closed.

  A generated step has `generated: true`. It follows the run that
  closed it. A source name, including `step0`, and a parameter list
  that matches the step are still that run. The two are not told
  apart by spelling.
  """
  def partition_funs(funs, runs) when is_list(funs) and is_list(runs) do
    partition_funs(funs, runs, [], %{})
  end

  defp partition_funs([], [], groups, map), do: {:ok, Enum.reverse(groups), map}

  defp partition_funs([%{generated: true} | _], _runs, _groups, _map),
    do: {:error, "c:unsupported"}

  defp partition_funs([%{name: name} = fun | rest], [%{name: name} | ds], groups, map) do
    {steps, rest} = take_generated(rest)
    map = Enum.reduce(steps, map, &Map.put(&2, &1.name, &1))
    partition_funs(rest, ds, [{fun, steps} | groups], map)
  end

  defp partition_funs(_funs, _runs, _groups, _map), do: {:error, "c:unsupported"}

  defp take_generated([%{generated: true} = fun | rest]) do
    {more, rest} = take_generated(rest)
    {[fun | more], rest}
  end

  defp take_generated(funs), do: {[], funs}

  @doc """
  Source name to emitted name for each run definition, in book order.

  `spell` turns a source name into the backend's base spelling. The first
  definition to claim a spelling keeps it. A later one takes `base_2`,
  then `base_3`, and so on. `taken` is spellings already used by the
  backend (a constructor function, the Nat helper).
  """
  def def_names(book, spell, taken \\ MapSet.new()) when is_function(spell, 1) do
    {map, _} =
      Enum.reduce(run_defs(book), {%{}, taken}, fn %{name: name}, {map, used} ->
        {emitted, used} = claim(spell.(name), used)
        {Map.put(map, name, emitted), used}
      end)

    map
  end

  @doc """
  Module name `mix muro.emit` gives a file: the stem, hyphens turned
  into underscores, then camelized. `rounding.muro` is `Rounding`.
  `half_ok.muro` is `HalfOk`.
  """
  def elixir_module(path) when is_binary(path) do
    path
    |> elixir_stem()
    |> List.wrap()
    |> Module.concat()
  end

  @doc """
  Test module `mix muro.emit --backend exunit` prints for `path`.
  The stem module plus `Test`: `rounding.muro` is `RoundingTest`.
  The implementation under test stays `elixir_module/1`, so the two
  modules can be compiled together.
  """
  def exunit_module(path) when is_binary(path) do
    Module.concat([elixir_stem(path) <> "Test"])
  end

  @doc """
  Module name `mix muro.emit --backend fsm` gives a file.
  The stem plus `Fsm`: `meet.muro` is `MeetFsm`.
  """
  def fsm_module(path) when is_binary(path) do
    Module.concat([elixir_stem(path) <> "Fsm"])
  end

  @doc false
  def emit_private_runs(book, wanted) when is_list(book) and is_list(wanted) do
    names = elixir_names(book)
    want = MapSet.new(wanted)

    runs =
      book
      |> run_defs()
      |> Enum.filter(&MapSet.member?(want, &1.name))

    funs =
      runs
      |> Enum.map(&emit_def(Map.put(&1, :export, false), book, names))
      |> Enum.join("\n\n")

    except =
      case kernel_clashes(runs, names) do
        [] -> ""
        clashes -> "import Kernel, except: #{inspect(clashes)}\n"
      end

    nat = nat_helpers(runs, "")

    String.trim(except <> "\n" <> funs <> "\n" <> nat)
  end

  defp elixir_stem(path) do
    path
    |> Path.basename(".muro")
    |> String.replace("-", "_")
    |> Macro.camelize()
  end

  @doc """
  Source name to Elixir function name for every `run` definition.

  The spelling is `elixir_base/1`. Every run is claimed, in book order,
  before a backend drops internal or non-`Nat` runs. `taken` is the
  host functions that share a module with those runs: the NIF loader,
  the FSM interpreter, `muro_nat_to_int`, and the repr helpers.
  Elixir, NIF, OTP, FSM, and ExUnit all read this map.
  """
  def elixir_names(book) when is_list(book) do
    def_names(book, &elixir_base/1, Muro.Emit.Helpers.runs())
  end

  @doc """
  The outline of one backend. `:c`, `:rust`, `:zig`, `:js`, and `:otp`
  take a stem. `:fsm` takes the book path and uses `fsm_module/1`. The
  result is `{:ok, outline}` or `{:error, reason}`. An outline names the
  signatures, layouts, and clause heads that backend emits. It does not
  write source.
  """
  def outline(:otp, book, stem), do: Muro.Emit.Otp.outline(book, stem)
  def outline(:c, book, stem), do: Muro.Emit.C.outline(book, stem)
  def outline(:rust, book, stem), do: Muro.Emit.Rust.outline(book, stem)
  def outline(:zig, book, stem), do: Muro.Emit.Zig.outline(book, stem)
  def outline(:js, book, stem), do: Muro.Emit.JS.outline(book, stem)

  def outline(:fsm, book, path) when is_binary(path) do
    Muro.Emit.Fsm.outline(book, path, fsm_module(path))
  end

  @doc """
  Module alias of each source name, claimed in list order.

  `Macro.camelize/1` is not injective (`a_1b` and `a1b` both become
  `A1b`). The later name takes `_2`.
  """
  def elixir_modules(names) when is_list(names) do
    {map, _} =
      Enum.reduce(names, {%{}, MapSet.new()}, fn name, {map, used} ->
        {mod, used} = Name.claim(elixir_alias(name), used)
        {Map.put(map, name, mod), used}
      end)

    map
  end

  @doc """
  Quantities of the Π binders of a named type, outer binder first.
  `emit_module/2` drops the `:erased` ones from the Elixir arity.
  """
  def binder_qtys(type) do
    case Ast.to_db(type) do
      {:ok, ty} -> qty_spine(ty)
      {:error, _message} -> []
    end
  end

  @doc """
  Render a closed de Bruijn value as the Elixir literal `emit_module/2`
  builds: `0`, `{:suc, n}`, `:tt`, an atom, a constructor tuple, or a
  pair.

  `book` is the named book, so declared constructors are recognized.
  Returns `{:ok, source}` or `{:error, reason}` where `reason` is
  `:function`, `:stream`, `:machine`, `:open`, or `:shape`.

  Host data (`repr`, issue #131) belongs in this function. Until that
  exists, a caller compares these shapes.
  """
  def emit_closed(term, book) when is_list(book) do
    case value_kind(term, book) do
      :value -> {:ok, emit_db(term, 0, book, %{})}
      reason -> {:error, reason}
    end
  end

  def emit_module(module, book) when is_atom(module) do
    book = Muro.Grade.erase_book(book)
    runs = run_defs(book)
    names = elixir_names(book)
    funs = runs |> Enum.map(&emit_def(&1, book, names)) |> Enum.join("\n\n")

    except =
      case kernel_clashes(runs, names) do
        [] -> ""
        clashes -> "  import Kernel, except: #{inspect(clashes)}\n"
      end

    nat_helper = nat_helpers(runs, "  ")

    source = """
    defmodule #{inspect(module)} do
      # Generated by Muro. Evidence never becomes a run.
    #{except}
    #{indent(funs, 2)}
    #{nat_helper}
    end
    """

    case Muro.Repr.elixir(book, names) do
      "" ->
        source

      codec ->
        String.replace_suffix(source, "end\n", indent(codec, 2) <> "\nend\n")
    end
  end

  defp emit_def(%{name: name, type: ty, body: body} = d, book, names) do
    {:ok, ty_db} = Ast.to_db(ty)
    {:ok, body_db} = Ast.to_db(body)
    {erased, arity} = telescope(ty_db, 0, [])
    inner = eta_body(body_db, arity)
    Process.put({Muro.Emit, :word_kinds}, word_kind_spine(ty_db))

    try do
      args =
        0..(arity - 1)//1
        |> Enum.reject(&(&1 in erased))
        |> Enum.map(&bound_name(inner, arity - 1 - &1, &1, book))

      expr = emit_db(inner, arity, book, names)
      kw = if Map.get(d, :export, true), do: "def", else: "defp"
      fun = Map.fetch!(names, name)

      if args == [] do
        "#{kw} #{fun} do\n  #{expr}\nend"
      else
        "#{kw} #{fun}(#{Enum.join(args, ", ")}) do\n  #{expr}\nend"
      end
    after
      Process.delete({Muro.Emit, :word_kinds})
    end
  end

  # A run definition named like a Kernel function or macro of the same
  # arity (`max/2`, `length/1`) would be ambiguous with the import.
  defp kernel_clashes(runs, names) do
    kernel = Kernel.__info__(:functions) ++ Kernel.__info__(:macros)

    runs
    |> Enum.map(fn %{name: name, type: ty} ->
      {:ok, ty_db} = Ast.to_db(ty)
      {erased, arity} = telescope(ty_db, 0, [])
      {String.to_atom(Map.fetch!(names, name)), arity - length(erased)}
    end)
    |> Enum.filter(&(&1 in kernel))
    |> Enum.uniq()
  end

  defp telescope({:pi, :erased, _, _, b}, i, er), do: telescope(b, i + 1, [i | er])
  defp telescope({:pi, _, _, _, b}, i, er), do: telescope(b, i + 1, er)
  defp telescope(_, i, er), do: {er, i}

  defp peel_lams({:lam, _, _, _, t}, n) when n > 0, do: peel_lams(t, n - 1)
  defp peel_lams(t, _), do: t

  # The body under `arity` binders. A body with fewer λs than its type
  # has Πs (`def f : run Π (n : Nat) → Stream Nat := natsFrom`) is
  # applied to the binders it does not name.
  defp eta_body(body, arity) do
    named = count_lams(body, arity)
    missing = arity - named
    inner = peel_lams(body, named)

    if missing == 0 do
      inner
    else
      shifted = Muro.Subst.ren(&(&1 + missing), inner)
      Enum.reduce((missing - 1)..0//-1, shifted, fn i, acc -> {:app, acc, {:var, i}} end)
    end
  end

  defp count_lams({:lam, _, _, _, t}, n) when n > 0, do: 1 + count_lams(t, n - 1)
  defp count_lams(_, _), do: 0

  # de Bruijn 0 is the nearest binder = last peeled λ = x#{depth-1}.
  defp emit_db({:var, i}, depth, _book, _names), do: "x#{depth - 1 - i}"
  defp emit_db(:ze, _, _book, _names), do: "0"
  defp emit_db(:one, _, _book, _names), do: ":tt"
  defp emit_db({:su, u}, d, book, names), do: "{:suc, #{emit_db(u, d, book, names)}}"
  defp emit_db({:ann, e, _}, d, book, names), do: emit_db(e, d, book, names)
  defp emit_db(:rfl, _, _book, _names), do: ":refl"
  defp emit_db({:rwt, _, _, t}, d, book, names), do: emit_db(t, d, book, names)

  defp emit_db({:hole, _}, _, _, _), do: raise("emit: hole")

  defp emit_db({:atom, n}, _, _book, _names), do: elixir_atom(n)

  defp emit_db({:matom, e, _p, bs}, d, book, names) do
    clauses =
      Enum.map(bs, fn {name, b} ->
        "      #{elixir_atom(name)} -> #{emit_db(b, d, book, names)}"
      end)
      |> Enum.join("\n")

    """
    (case #{emit_db(e, d, book, names)} do
    #{clauses}
    end)
    """
    |> String.trim()
  end

  defp emit_db({:lam, :erased, _, _, t}, d, book, names) do
    with_kinds([nil], fn -> emit_db(t, d + 1, book, names) end)
  end

  defp emit_db({:lam, _, a, _, t}, d, book, names) do
    with_kinds([kind_of_annot(a)], fn ->
      "fn #{bound_name(t, 0, d, book)} -> #{emit_db(t, d + 1, book, names)} end"
    end)
  end

  defp emit_db({:mdata, e, _p, bs}, d, book, names) do
    clauses =
      Enum.map(bs, fn {name, ar, b} ->
        pat = emit_ctor_pat(name, ar, d, b, book)

        body =
          with_kinds(List.duplicate(nil, ar), fn -> emit_db(b, d + ar, book, names) end)

        "      #{pat} -> #{body}"
      end)
      |> Enum.join("\n")

    """
    (case #{emit_db(e, d, book, names)} do
    #{clauses}
    end)
    """
    |> String.trim()
  end

  defp emit_db({:mwbool, e, _p, bs}, d, book, names) do
    t = word_arm(bs, "wtrue")
    f = word_arm(bs, "wfalse")

    """
    (case #{emit_db(e, d, book, names)} do
      true -> #{emit_db(t, d, book, names)}
      false -> #{emit_db(f, d, book, names)}
    end)
    """
    |> String.trim()
  end

  defp emit_db({:mopt, e, _p, bs}, d, book, names) do
    {_, _, s} = Enum.find(bs, fn {n, _, _} -> n == "wsome" end)
    n = word_arm(bs, "wnone")

    pay =
      case term_kind(e, book) do
        {:opt, k} -> k
        _ -> nil
      end

    some = with_kinds([pay], fn -> emit_db(s, d + 1, book, names) end)

    """
    (case #{emit_db(e, d, book, names)} do
      {:some, #{bound_name(s, 0, d, book)}} -> #{some}
      :none -> #{emit_db(n, d, book, names)}
    end)
    """
    |> String.trim()
  end

  defp emit_db({:mnat, e, _p, z, s}, d, book, names) do
    suc = with_kinds([nil], fn -> emit_db(s, d + 1, book, names) end)

    """
    case #{emit_db(e, d, book, names)} do
      0 -> #{emit_db(z, d, book, names)}
      {:suc, #{bound_name(s, 0, d, book)}} -> #{suc}
    end
    """
    |> String.trim()
  end

  defp emit_db({:memp, _, _}, _, _book, _names), do: "raise \"Empty\""

  defp emit_db({:munit, e, _, u}, d, book, names) do
    "(#{emit_db(e, d, book, names)}; #{emit_db(u, d, book, names)})"
  end

  defp emit_db({:pair, a, b}, d, book, names),
    do: "{#{emit_db(a, d, book, names)}, #{emit_db(b, d, book, names)}}"

  # let (a, b) = e in t: a is de Bruijn 1 (x#{d}), b is de Bruijn 0 (x#{d + 1}).
  defp emit_db({:letp, e, t}, d, book, names) do
    a = bound_name(t, 1, d, book)
    b = bound_name(t, 0, d + 1, book)
    body = with_kinds([nil, nil], fn -> emit_db(t, d + 2, book, names) end)
    "({#{a}, #{b}} = #{emit_db(e, d, book, names)}; #{body})"
  end

  defp emit_db({:unf, seed, f}, d, book, names) do
    "Stream.unfold(#{emit_db(seed, d, book, names)}, #{emit_db(f, d, book, names)})"
  end

  defp emit_db({:ucons, s}, d, book, names) do
    "(fn s -> {s |> Enum.take(1) |> hd(), Stream.drop(s, 1)} end).(#{emit_db(s, d, book, names)})"
  end

  defp emit_db({:addi, x, y}, d, book, names) do
    "Nx.add(#{emit_db(x, d, book, names)}, #{emit_db(y, d, book, names)})"
  end

  defp emit_db({:muli, x, y}, d, book, names) do
    "Nx.multiply(#{emit_db(x, d, book, names)}, #{emit_db(y, d, book, names)})"
  end

  defp emit_db({:addt, t, u}, d, book, names) do
    "Nx.add(#{emit_db(t, d, book, names)}, #{emit_db(u, d, book, names)})"
  end

  defp emit_db({:toi64, t}, d, book, names) do
    "Nx.tensor(muro_nat_to_int(#{emit_db(t, d, book, names)}), type: :s64)"
  end

  defp emit_db({:packi, x, y}, d, book, names) do
    "Nx.stack([#{emit_db(x, d, book, names)}, #{emit_db(y, d, book, names)}])"
  end

  defp emit_db({:app, _, _} = t, d, book, names) do
    {h, args} = spine(t, [])

    case h do
      {:def, n} -> emit_ref(n, args, d, book, names)
      _ -> apply_rest(emit_db(h, d, book, names), args, d, book, names)
    end
  end

  defp emit_db({:def, n}, d, book, names), do: emit_ref(n, [], d, book, names)

  defp emit_db({:word, op, args}, d, book, names), do: emit_word(op, args, d, book, names)

  defp emit_db({:slit, bin}, _, _book, _names) when is_binary(bin), do: inspect(bin)

  defp emit_db({:scat, a, b}, d, book, names) do
    "(#{emit_db(a, d, book, names)}) <> (#{emit_db(b, d, book, names)})"
  end

  defp emit_db({:slen, a}, d, book, names) do
    ":erlang.length(:unicode.characters_to_list(#{emit_db(a, d, book, names)}))"
  end

  defp emit_db({:seq, a, b}, d, book, names) do
    "(#{emit_db(a, d, book, names)}) == (#{emit_db(b, d, book, names)})"
  end

  defp emit_db({:blit, bin}, _, _book, _names) when is_binary(bin), do: inspect(bin)

  defp emit_db({:bcat, a, b}, d, book, names) do
    "(#{emit_db(a, d, book, names)}) <> (#{emit_db(b, d, book, names)})"
  end

  defp emit_db({:blen, a}, d, book, names), do: byte_size_of(emit_db(a, d, book, names))
  defp emit_db({:xlen, a}, d, book, names), do: byte_size_of(emit_db(a, d, book, names))

  defp emit_db({:beq, a, b}, d, book, names),
    do: bytes_eq(emit_db(a, d, book, names), emit_db(b, d, book, names))

  defp emit_db({:xeq, a, b}, d, book, names),
    do: bytes_eq(emit_db(a, d, book, names), emit_db(b, d, book, names))

  defp emit_db({:bsub, s, off, len}, d, book, names) do
    bytes_sub(
      emit_db(s, d, book, names),
      emit_db(off, d, book, names),
      emit_db(len, d, book, names)
    )
  end

  defp emit_db({:bget, s, i}, d, book, names),
    do: bytes_get(emit_db(s, d, book, names), emit_db(i, d, book, names))

  defp emit_db({:aget, s, i}, d, book, names),
    do: bytes_get(emit_db(s, d, book, names), emit_db(i, d, book, names))

  defp emit_db({:bunc, s}, d, book, names), do: bytes_uncons(emit_db(s, d, book, names))
  defp emit_db({:sbytes, s}, d, book, names), do: emit_db(s, d, book, names)

  defp emit_db({:btil, s, b}, d, book, names),
    do: bytes_until(emit_db(s, d, book, names), emit_db(b, d, book, names))

  defp emit_db({:baft, s, b}, d, book, names),
    do: bytes_after(emit_db(s, d, book, names), emit_db(b, d, book, names))

  defp emit_db({tag, _ty, z, f, s}, d, book, names) when tag in [:bfold, :afold] do
    bytes_fold(emit_db(f, d, book, names), emit_db(z, d, book, names), emit_db(s, d, book, names))
  end

  defp emit_db(_, _, _book, _names), do: "raise \"erased term\""

  defp word_arm(bs, name) do
    {_, _, body} = Enum.find(bs, fn {n, _, _} -> n == name end)
    body
  end

  defp byte_size_of(s), do: "byte_size(#{s})"
  defp bytes_eq(a, b), do: "(#{a}) == (#{b})"

  defp bytes_sub(s, off, len) do
    "(fn s, off, len -> n = byte_size(s); if off < 0 or len < 0 or off > n or len > n - off, do: <<>>, else: :binary.part(s, off, len) end).(#{s}, #{off}, #{len})"
  end

  defp bytes_get(s, i) do
    "(fn s, i -> if i >= 0 and i < byte_size(s), do: {:some, :binary.at(s, i)}, else: :none end).(#{s}, #{i})"
  end

  defp bytes_uncons(s) do
    "(fn s -> case s do <<>> -> :nothing; <<b, rest::binary>> -> {:just, {b, rest}} end end).(#{s})"
  end

  defp bytes_until(s, b) do
    "(fn s, b -> case :binary.match(s, <<b>>) do :nomatch -> s; {pos, _} -> :binary.part(s, 0, pos) end end).(#{s}, #{b})"
  end

  defp bytes_after(s, b) do
    "(fn s, b -> case :binary.match(s, <<b>>) do :nomatch -> <<>>; {pos, 1} -> :binary.part(s, pos + 1, byte_size(s) - pos - 1) end end).(#{s}, #{b})"
  end

  defp bytes_fold(f, z, s) do
    "(fn f, z, s -> recur = fn recur, acc, cur -> case cur do <<>> -> acc; <<b, rest::binary>> -> recur.(recur, f.(b).(rest).(acc), rest) end end; recur.(recur, z, s) end).(#{f}, #{z}, #{s})"
  end

  # A definition applied to `args`. With as many arguments as its type
  # has Πs it is a direct call. With more, the result is a function value
  # and the rest are applied with `.()`. With fewer it is a curried
  # closure over the remaining live arguments, the given ones evaluated
  # once; erased binders take no argument, as for an anonymous λ. A
  # constructor is always fully applied (the checker asks for it).
  defp emit_ref(n, args, d, book, names) do
    cond do
      ctor_name?(book, n) ->
        emit_ctor(n, args, d, book, names)

      qtys = ref_qtys(book, n) ->
        emit_ref(n, qtys, args, d, book, names)

      true ->
        "#{ename(names, n)}(#{Enum.join(Enum.map(args, &emit_db(&1, d, book, names)), ", ")})"
    end
  end

  defp emit_ref(n, qtys, args, d, book, names) do
    arity = length(qtys)
    {now, rest} = Enum.split(args, arity)

    cond do
      length(args) >= arity ->
        apply_rest(full_call(n, now, d, book, names), rest, d, book, names)

      true ->
        live_given =
          for {a, q} <- Enum.zip(now, qtys), q != :erased, do: emit_db(a, d, book, names)

        missing = Enum.drop(qtys, length(now))
        as = for {_, i} <- Enum.with_index(live_given), do: "a#{d}_#{i}"
        ys = for {q, i} <- Enum.with_index(missing), q != :erased, do: "y#{d}_#{i}"
        call = "#{ename(names, n)}(#{Enum.join(as ++ ys, ", ")})"
        closure = Enum.reduce(Enum.reverse(ys), call, fn y, acc -> "fn #{y} -> #{acc} end" end)

        if as == [],
          do: closure,
          else: "(fn #{Enum.join(as, ", ")} -> #{closure} end).(#{Enum.join(live_given, ", ")})"
    end
  end

  defp full_call(n, args, d, book, names),
    do: "#{ename(names, n)}(#{Enum.join(live_args(book, n, args, d, names), ", ")})"

  defp apply_rest(head, [], _d, _book, _names), do: head

  defp apply_rest(head, args, d, book, names) do
    Enum.reduce(args, callable(head), fn a, acc -> "#{acc}.(#{emit_db(a, d, book, names)})" end)
  end

  # `case … end.(x)` does not parse; a head that is not a name or a call
  # is parenthesized before it is applied.
  defp callable(head) do
    if String.match?(head, ~r/\A[A-Za-z_][A-Za-z0-9_]*(\(.*\))?\z/s) and
         not String.contains?(head, "\n"),
       do: head,
       else: "(#{head})"
  end

  # Quantities of the Πs of a definition's type; nil for a name the book
  # does not define.
  defp ref_qtys(book, name) do
    case Enum.find(
           book,
           &(Map.get(&1, :kind, :def) not in [:data, :repr] and Map.get(&1, :name) == name)
         ) do
      nil ->
        nil

      dfn ->
        {:ok, ty} = Ast.to_db(dfn.type)
        qty_spine(ty)
    end
  end

  defp emit_ctor(name, args, d, book, names) do
    xs = Enum.map(args, &emit_db(&1, d, book, names))
    atom = elixir_atom(name)

    case xs do
      [] -> atom
      _ -> "{#{atom}, #{Enum.join(xs, ", ")}}"
    end
  end

  defp emit_ctor_pat(name, 0, _d, _body, _book), do: elixir_atom(name)

  defp emit_ctor_pat(name, ar, d, body, book) do
    vars = Enum.map(0..(ar - 1), fn i -> bound_name(body, ar - 1 - i, d + i, book) end)
    "{#{elixir_atom(name)}, #{Enum.join(vars, ", ")}}"
  end

  # A binder the emitted term never mentions is `_`, so eval does not warn.
  defp bound_name(body, idx, slot, book) do
    if emitted_occurs?(idx, body, book), do: "x#{slot}", else: "_"
  end

  defp emitted_occurs?(i, {:var, j}, _), do: i == j
  defp emitted_occurs?(i, {:lam, _, _, _, t}, book), do: emitted_occurs?(i + 1, t, book)
  defp emitted_occurs?(i, {:su, t}, book), do: emitted_occurs?(i, t, book)
  defp emitted_occurs?(i, {:ann, e, _}, book), do: emitted_occurs?(i, e, book)
  defp emitted_occurs?(i, {:rwt, _, _, t}, book), do: emitted_occurs?(i, t, book)

  defp emitted_occurs?(i, {:pair, a, b}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book)

  defp emitted_occurs?(i, {:letp, e, t}, book),
    do: emitted_occurs?(i, e, book) or emitted_occurs?(i + 2, t, book)

  defp emitted_occurs?(i, {:mnat, e, _, z, s}, book),
    do:
      emitted_occurs?(i, e, book) or emitted_occurs?(i, z, book) or
        emitted_occurs?(i + 1, s, book)

  defp emitted_occurs?(i, {:mdata, e, _, bs}, book) do
    emitted_occurs?(i, e, book) or
      Enum.any?(bs, fn {_, ar, b} -> emitted_occurs?(i + ar, b, book) end)
  end

  defp emitted_occurs?(i, {tag, e, _, bs}, book) when tag in [:mwbool, :mopt] do
    emitted_occurs?(i, e, book) or
      Enum.any?(bs, fn {_, ar, b} -> emitted_occurs?(i + ar, b, book) end)
  end

  defp emitted_occurs?(i, {:matom, e, _, bs}, book) do
    emitted_occurs?(i, e, book) or
      Enum.any?(bs, fn {_, b} -> emitted_occurs?(i, b, book) end)
  end

  defp emitted_occurs?(i, {:munit, e, _, u}, book),
    do: emitted_occurs?(i, e, book) or emitted_occurs?(i, u, book)

  defp emitted_occurs?(i, {:unf, s, f}, book),
    do: emitted_occurs?(i, s, book) or emitted_occurs?(i, f, book)

  defp emitted_occurs?(i, {:ucons, s}, book), do: emitted_occurs?(i, s, book)

  defp emitted_occurs?(i, {:addi, a, b}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book)

  defp emitted_occurs?(i, {:muli, a, b}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book)

  defp emitted_occurs?(i, {:addt, a, b}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book)

  defp emitted_occurs?(i, {:toi64, t}, book), do: emitted_occurs?(i, t, book)

  defp emitted_occurs?(i, {:packi, a, b}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book)

  defp emitted_occurs?(i, {:word, _, args}, book),
    do: Enum.any?(args, &emitted_occurs?(i, &1, book))

  defp emitted_occurs?(i, {:scat, a, b}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book)

  defp emitted_occurs?(i, {:slen, a}, book), do: emitted_occurs?(i, a, book)

  defp emitted_occurs?(i, {:seq, a, b}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book)

  defp emitted_occurs?(i, {:bcat, a, b}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book)

  defp emitted_occurs?(i, {:blen, a}, book), do: emitted_occurs?(i, a, book)
  defp emitted_occurs?(i, {:xlen, a}, book), do: emitted_occurs?(i, a, book)

  defp emitted_occurs?(i, {:beq, a, b}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book)

  defp emitted_occurs?(i, {:xeq, a, b}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book)

  defp emitted_occurs?(i, {:bget, a, b}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book)

  defp emitted_occurs?(i, {:aget, a, b}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book)

  defp emitted_occurs?(i, {:btil, a, b}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book)

  defp emitted_occurs?(i, {:baft, a, b}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book)

  defp emitted_occurs?(i, {:bunc, a}, book), do: emitted_occurs?(i, a, book)
  defp emitted_occurs?(i, {:sbytes, a}, book), do: emitted_occurs?(i, a, book)

  defp emitted_occurs?(i, {:bsub, a, b, c}, book),
    do: emitted_occurs?(i, a, book) or emitted_occurs?(i, b, book) or emitted_occurs?(i, c, book)

  defp emitted_occurs?(i, {tag, ty, z, f, s}, book) when tag in [:bfold, :afold],
    do:
      emitted_occurs?(i, ty, book) or emitted_occurs?(i, z, book) or emitted_occurs?(i, f, book) or
        emitted_occurs?(i, s, book)

  defp emitted_occurs?(i, {:app, _, _} = t, book) do
    {h, args} = spine(t, [])

    case h do
      {:def, n} ->
        if ctor_name?(book, n) do
          Enum.any?(args, &emitted_occurs?(i, &1, book))
        else
          args
          |> Enum.zip(arg_qtys(book, n, length(args)))
          |> Enum.reject(fn {_, q} -> q == :erased end)
          |> Enum.any?(fn {a, _} -> emitted_occurs?(i, a, book) end)
        end

      other ->
        emitted_occurs?(i, other, book) or Enum.any?(args, &emitted_occurs?(i, &1, book))
    end
  end

  defp emitted_occurs?(_, _, _), do: false

  defp arg_qtys(book, name, n) do
    case Enum.find(
           book,
           &(Map.get(&1, :kind, :def) not in [:data, :repr] and Map.get(&1, :name) == name)
         ) do
      nil ->
        List.duplicate(:affine, n)

      dfn ->
        {:ok, ty} = Ast.to_db(dfn.type)
        qtys = qty_spine(ty)
        qtys ++ List.duplicate(:affine, max(n - length(qtys), 0))
    end
  end

  defp ctor_name?(book, name) do
    Enum.any?(book, fn
      %{kind: :data, ctors: cs} -> Enum.any?(cs, &(&1.name == name))
      _ -> false
    end)
  end

  # A value the suite can pass to `==`. Anything else is a skip reason.
  # `repr` (#131) replaces this classification.
  defp value_kind(:ze, _book), do: :value
  defp value_kind(:one, _book), do: :value
  defp value_kind({:atom, _name}, _book), do: :value
  defp value_kind({:slit, bin}, _book) when is_binary(bin), do: :value
  defp value_kind({:blit, bin}, _book) when is_binary(bin), do: :value

  defp value_kind({:bcat, a, b}, book) do
    case value_kind(a, book) do
      :value -> value_kind(b, book)
      reason -> reason
    end
  end

  defp value_kind({:sbytes, a}, book), do: value_kind(a, book)

  defp value_kind({:scat, a, b}, book) do
    case value_kind(a, book) do
      :value -> value_kind(b, book)
      reason -> reason
    end
  end

  defp value_kind({:slen, a}, book), do: value_kind(a, book)

  defp value_kind({:seq, a, b}, book) do
    case value_kind(a, book) do
      :value -> value_kind(b, book)
      reason -> reason
    end
  end

  defp value_kind({:su, t}, book), do: value_kind(t, book)
  defp value_kind({:ann, e, _ty}, book), do: value_kind(e, book)

  defp value_kind({:pair, a, b}, book) do
    case value_kind(a, book) do
      :value -> value_kind(b, book)
      reason -> reason
    end
  end

  defp value_kind({:var, _i}, _book), do: :open

  defp value_kind({:def, name}, book) do
    if ctor_name?(book, name), do: :value, else: :open
  end

  defp value_kind({:lam, _q, _a, _x, _t}, _book), do: :function
  defp value_kind({:unf, _s, _f}, _book), do: :stream
  defp value_kind({:ucons, _s}, _book), do: :stream
  defp value_kind({:nu, _f}, _book), do: :stream
  defp value_kind({:bisim, _s, _t}, _book), do: :stream
  defp value_kind({:toi64, _t}, _book), do: :machine
  defp value_kind({:addi, _x, _y}, _book), do: :machine
  defp value_kind({:muli, _x, _y}, _book), do: :machine
  defp value_kind({:addt, _t, _u}, _book), do: :machine
  defp value_kind({:packi, _x, _y}, _book), do: :machine
  defp value_kind({:tensor, _d, _s}, _book), do: :machine
  defp value_kind(:i64, _book), do: :machine
  defp value_kind({:word, _, _}, _book), do: :machine
  defp value_kind(:f32ty, _book), do: :machine

  defp value_kind({:app, _, _} = term, book) do
    {head, args} = spine(term, [])

    case head do
      {:def, name} ->
        if ctor_name?(book, name) do
          value_args(args, book)
        else
          :shape
        end

      _other ->
        :shape
    end
  end

  defp value_kind(_other, _book), do: :shape

  defp value_args([], _book), do: :value

  defp value_args([arg | rest], book) do
    case value_kind(arg, book) do
      :value -> value_args(rest, book)
      reason -> reason
    end
  end

  defp live_args(book, name, args, d, names) do
    case Enum.find(
           book,
           &(Map.get(&1, :kind, :def) not in [:data, :repr] and Map.get(&1, :name) == name)
         ) do
      nil ->
        Enum.map(args, &emit_db(&1, d, book, names))

      dfn ->
        {:ok, ty} = Ast.to_db(dfn.type)
        qtys = qty_spine(ty)

        args
        |> Enum.zip(qtys ++ List.duplicate(:affine, length(args)))
        |> Enum.reject(fn {_, q} -> q == :erased end)
        |> Enum.map(fn {a, _} -> emit_db(a, d, book, names) end)
    end
  end

  defp qty_spine({:pi, q, _, _, b}), do: [q | qty_spine(b)]
  defp qty_spine(_), do: []

  defp spine({:app, f, a}, acc), do: spine(f, [a | acc])
  defp spine(h, acc), do: {h, acc}

  defp elixir_atom(name), do: ":" <> elixir_atom_name(name)

  # The host spelling of one source identifier. A hyphen folds to `_`.
  # If that fold is already a function name (`^[a-z_][A-Za-z0-9_]*$`, no
  # `__`, not reserved), the fold is the spelling: `golden-silence` is
  # `golden_silence`. A name that is already that shape stays itself.
  # Everything else is `muro__` plus `Name.encode/1` of the source name
  # (`Bit`, `and`, `?`, `!`, a scalar outside the alphabet). The escape
  # contains `__` only as that prefix. Two source names that reach one
  # spelling are refused by `elixir_clash/1`; within a book the map is
  # injective. `?` and `!` are not kept: a claim suffix would follow
  # them (`foo?_2`), which Elixir rejects.
  @elixir_spelling "0.20.17"

  @doc """
  Elixir function name of one source identifier.

  A hyphen folds to `_`. `foo_bar`, `fromMaybe`, `muro_and`, and
  `golden-silence` (as `golden_silence`) stay or become that fold when
  it is already a function name. An uppercase first letter, a leading
  digit, `?` or `!`, a reserved word, a fold that contains `__`, or a
  scalar outside the alphabet becomes `muro__` plus
  `Muro.Emit.Name.encode/1` of the source name.
  """
  def elixir_base(name) when is_binary(name) do
    folded = String.replace(name, "-", "_")

    if kept_function?(folded) and not MapSet.member?(@elixir_reserved, folded) do
      folded
    else
      "muro__" <> Name.encode(name)
    end
  end

  @doc """
  The Muro version that introduced the current Elixir host spelling.

  A committed module whose header names an older version may still
  carry the 0.20.4 `muro__` spelling of a hyphenated run.
  `mix muro.gen` prints the host names that changed in that case.
  """
  def elixir_spelling, do: @elixir_spelling

  @doc """
  `:ok` when every run and every meeting in `book` has a distinct
  `elixir_base/1` spelling. `{:error, message}` names both source
  names when two of them reach one Elixir function.
  """
  def elixir_clash(book) when is_list(book) do
    book
    |> elixir_host_entries()
    |> elixir_clash_seen(%{})
  end

  defp elixir_host_entries(book) do
    Enum.filter(book, fn d ->
      Map.get(d, :kind, :def) not in [:data, :repr] and
        (Map.get(d, :mode) == :run or Map.get(d, :kind) == :meet)
    end)
  end

  defp elixir_clash_seen([], _seen), do: :ok

  defp elixir_clash_seen([d | rest], seen) do
    host = elixir_base(d.name)

    case Map.fetch(seen, host) do
      {:ok, prev} ->
        {:error,
         "#{Muro.Print.loc_prefix(Map.get(prev, :loc))}#{prev.name} and #{d.name} spell one Elixir function\n" <>
           "#{Muro.Print.loc_prefix(Map.get(d, :loc))}#{prev.name} and #{d.name} spell one Elixir function"}

      :error ->
        elixir_clash_seen(rest, Map.put(seen, host, d))
    end
  end

  @doc """
  Host function names in `old_body` that this spelling rewrites.

  Each pair is `{old, new}`: a `muro__` spelling whose source folds to
  a name present in `new_body`. Used when a committed module's header
  is older than `elixir_spelling/0`.
  """
  def elixir_host_renames(old_body, new_body)
      when is_binary(old_body) and is_binary(new_body) do
    new = MapSet.new(elixir_def_names(new_body))

    old_body
    |> elixir_def_names()
    |> Enum.flat_map(fn name ->
      case elixir_source(name) do
        {:ok, source} ->
          folded = elixir_base(source)

          if folded != name and MapSet.member?(new, folded) do
            [{name, folded}]
          else
            []
          end

        :error ->
          []
      end
    end)
    |> Enum.uniq()
  end

  defp elixir_def_names(body) do
    Regex.scan(~r/^[ \t]*defp? ([A-Za-z_][A-Za-z0-9_]*)/m, body)
    |> Enum.map(fn [_all, name] -> name end)
  end

  @doc """
  Atom spelling of a source constructor or tag.

  A valid unquoted atom with no `__` stays itself, so `:true`, `:Bit`,
  `:just`, and `:nil` stay. Anything else uses `elixir_base/1`. That
  image contains `__`, which a kept atom does not, so the two branches
  are disjoint. A function still uses `elixir_base/1` only: the atom
  `:and` and the function `muro__and` are different spellings.
  """
  def elixir_atom_name(name) when is_binary(name) do
    if String.match?(name, ~r/^[A-Za-z_][A-Za-z0-9_]*[?!]?$/) and not String.contains?(name, "__") do
      name
    else
      elixir_base(name)
    end
  end

  @doc """
  Inverse of the `muro__` escape, and of a spelling that was kept.

  A spelling that begins with `muro__` is `Name.decode/1` of the rest.
  Any other spelling is itself. `Name.encode/1` writes no underscore, so
  the prefix splits in one place. A hyphenated source whose fold is a
  function name is not recovered: `elixir_source("golden_silence")` is
  `{:ok, "golden_silence"}`. `source_ctor/2` is the book-aware inverse
  for constructors.

  This is the spelling inverse, not a lookup among one declaration's
  constructors. `elixir_source("muro__iszdon")` is `{:ok, "is-on"}` even
  when a constructor is named `muro__iszdon`. `source_ctor/2` is that
  lookup, and it is the only place a host label becomes a constructor.
  """
  def elixir_source("muro__" <> rest), do: Name.decode(rest)
  def elixir_source(spelling) when is_binary(spelling), do: {:ok, spelling}

  @doc """
  Source constructor named by a host label, or `:error`.

  `names` are the source constructors of one declaration. A label equal
  to `elixir_atom_name/1` of one of them is that constructor. A label
  that is itself one of those names is that constructor. When both
  apply, the host atom wins: the label `is_on` is `is-on` when that
  declaration has `is-on`. A constructor named `muro__iszdon` stays
  that source name as a label. Callers do not decode it again.
  """
  def source_ctor(names, label) when is_binary(label) do
    set = if is_struct(names, MapSet), do: names, else: MapSet.new(names)

    case Enum.find(set, fn name -> elixir_atom_name(name) == label end) do
      name when is_binary(name) ->
        {:ok, name}

      nil ->
        if MapSet.member?(set, label), do: {:ok, label}, else: :error
    end
  end

  @doc """
  Module alias of one source name.

  A snake name matching `^[a-z][a-z0-9]*(_[a-z0-9]+)*$` is camelized, so
  `pong` is `Pong`, `foo_bar` is `FooBar`, and `grant-end` is `GrantEnd`.
  Every other spelling is `M` plus `elixir_base/1`. Camelizing an escape
  would collide: `muro__and` and `muro_and` both become `MuroAnd`, and
  `_foo` becomes `Foo`.
  """
  def elixir_alias(name) when is_binary(name) do
    base = elixir_base(name)

    if String.match?(base, ~r/^[a-z][a-z0-9]*(_[a-z0-9]+)*$/) do
      Macro.camelize(base)
    else
      "M" <> base
    end
  end

  defp kept_function?(name) do
    String.match?(name, ~r/^[a-z_][A-Za-z0-9_]*$/) and not String.contains?(name, "__")
  end

  defp ename(names, name), do: Map.fetch!(names, name)

  # Same suffix as the C, Rust, and Zig emitters. Elixir spellings are
  # not in those two spaces; only the numeric tail is shared.
  defp claim(base, used), do: Name.claim(base, used)

  defp term_has_toi64?({:toi64, _}), do: true
  defp term_has_toi64?({:word, {:of, _}, _}), do: true
  defp term_has_toi64?({:word, op, _}) when op in [:shl, :shr], do: true

  defp term_has_toi64?(t) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.any?(&term_has_toi64?/1)
  end

  defp term_has_toi64?(t) when is_list(t), do: Enum.any?(t, &term_has_toi64?/1)
  defp term_has_toi64?(_), do: false

  defp term_has_ton?({:word, :ton, _}), do: true

  defp term_has_ton?(t) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.any?(&term_has_ton?/1)
  end

  defp term_has_ton?(t) when is_list(t), do: Enum.any?(t, &term_has_ton?/1)
  defp term_has_ton?(_), do: false

  defp nat_helpers(runs, pad) do
    [
      helper(Enum.any?(runs, &term_has_toi64?(&1.body)), pad, """
      defp muro_nat_to_int(0), do: 0
      defp muro_nat_to_int({:suc, n}), do: 1 + muro_nat_to_int(n)
      """),
      helper(Enum.any?(runs, &term_has_ton?(&1.body)), pad, """
      defp muro_int_to_nat(0), do: 0
      defp muro_int_to_nat(n) when n > 0, do: {:suc, muro_int_to_nat(n - 1)}
      """)
    ]
    |> Enum.reject(&(&1 == ""))
    |> Enum.join("\n")
  end

  # The helper text is a heredoc whose lines start with `defp`, so the
  # reservation scan sees the name. `pad` is applied when the text is built.
  defp helper(false, _pad, _src), do: ""

  defp helper(true, pad, src) do
    src
    |> String.trim_trailing()
    |> String.split("\n")
    |> Enum.map_join("\n", &(pad <> &1))
  end

  # Index 0 is the innermost binder (de Bruijn 0).
  defp word_kind_spine(ty), do: word_kind_spine(ty, [])
  defp word_kind_spine({:pi, _, a, _, b}, acc), do: word_kind_spine(b, [kind_of_annot(a) | acc])
  defp word_kind_spine(_, acc), do: acc

  defp kind_of_annot(:i64), do: :i64
  defp kind_of_annot({:word, {:ty, k}, []}), do: k
  defp kind_of_annot({:word, {:optk, k}, []}), do: {:opt, k}

  defp kind_of_annot({:word, :opt, [a]}) do
    case kind_of_annot(a) do
      nil -> nil
      k -> {:opt, k}
    end
  end

  defp kind_of_annot({:word, :bool, []}), do: :bool
  defp kind_of_annot({:ann, _, a}), do: kind_of_annot(a)
  defp kind_of_annot(_), do: nil

  defp with_kinds(ks, fun) do
    push_kinds(ks)

    try do
      fun.()
    after
      pop_kinds(length(ks))
    end
  end

  defp push_kinds(ks) do
    Process.put({Muro.Emit, :word_kinds}, ks ++ (Process.get({Muro.Emit, :word_kinds}) || []))
  end

  defp pop_kinds(n) do
    Process.put(
      {Muro.Emit, :word_kinds},
      Enum.drop(Process.get({Muro.Emit, :word_kinds}) || [], n)
    )
  end

  defp emit_word({:lit, k, n}, [], _d, _book, _names) do
    Integer.to_string(Muro.Word.residue(k, n))
  end

  defp emit_word(true, [], _d, _book, _names), do: "true"
  defp emit_word(false, [], _d, _book, _names), do: "false"
  defp emit_word(:none, [], _d, _book, _names), do: ":none"

  defp emit_word({:of, k}, [{:nat, n}], _d, _book, _names) when is_integer(n) and n >= 0 do
    Integer.to_string(Muro.Word.residue(k, n))
  end

  defp emit_word({:of, k}, [t], d, book, names) do
    "Muro.Word.of(#{inspect(k)}, muro_nat_to_int(#{emit_db(t, d, book, names)}))"
  end

  defp emit_word(:ton, [t], d, book, names) do
    "muro_int_to_nat(#{emit_db(t, d, book, names)})"
  end

  defp emit_word(op, [x, y], d, book, names) when op in [:add, :sub, :mul] do
    fun = %{add: "add", sub: "sub", mul: "mul"}
    word_bin(fun[op], x, y, d, book, names)
  end

  defp emit_word(op, [x, y], d, book, names) when op in [:and, :or, :xor] do
    fun = %{and: "band", or: "bor", xor: "bxor"}
    word_bin(fun[op], x, y, d, book, names)
  end

  defp emit_word(:not, [x], d, book, names) do
    "Muro.Word.bnot(#{inspect(need_kind(x, book))}, #{emit_db(x, d, book, names)})"
  end

  defp emit_word(op, [x, y], d, book, names) when op in [:eq, :lt, :le] do
    fun = %{eq: "eq?", lt: "lt?", le: "le?"}
    word_bin(fun[op], x, y, d, book, names)
  end

  defp emit_word(op, [x, y], d, book, names) when op in [:cadd, :csub, :cmul] do
    fun = %{cadd: "checked_add", csub: "checked_sub", cmul: "checked_mul"}
    word_bin(fun[op], x, y, d, book, names)
  end

  defp emit_word(:div, [x, y], d, book, names), do: word_bin("divide", x, y, d, book, names)
  defp emit_word(:rem, [x, y], d, book, names), do: word_bin("remainder", x, y, d, book, names)

  defp emit_word(op, [x, amt], d, book, names) when op in [:shl, :shr] do
    fun = if op == :shl, do: "shl", else: "shr"

    "Muro.Word.#{fun}(#{inspect(need_kind(x, book))}, #{emit_db(x, d, book, names)}, muro_nat_to_int(#{emit_db(amt, d, book, names)}))"
  end

  defp emit_word({:cast, k}, [x], d, book, names) do
    "Muro.Word.cast(#{inspect(k)}, #{emit_db(x, d, book, names)})"
  end

  defp emit_word(:some, [x], d, book, names) do
    "{:some, #{emit_db(x, d, book, names)}}"
  end

  defp emit_word(_op, _args, _d, _book, _names), do: "raise \"erased term\""

  defp word_bin(fun, x, y, d, book, names) do
    "Muro.Word.#{fun}(#{inspect(operand_kind(x, y, book))}, #{emit_db(x, d, book, names)}, #{emit_db(y, d, book, names)})"
  end

  defp operand_kind(x, y, book) do
    case term_kind(x, book) || term_kind(y, book) do
      k when k in [:u8, :u32, :u64, :i64] -> k
      _ -> raise "word kind"
    end
  end

  defp need_kind(t, book) do
    case term_kind(t, book) do
      k when k in [:u8, :u32, :u64, :i64] -> k
      _ -> raise "word kind"
    end
  end

  defp term_kind({:var, i}, _book) do
    Enum.at(Process.get({Muro.Emit, :word_kinds}) || [], i)
  end

  defp term_kind({:ann, e, a}, book), do: term_kind(e, book) || kind_of_annot(a)
  defp term_kind({:word, {:lit, k, _}, _}, _book), do: k
  defp term_kind({:word, {:of, k}, _}, _book), do: k
  defp term_kind({:word, {:cast, k}, _}, _book), do: k
  defp term_kind({:word, true, _}, _book), do: :bool
  defp term_kind({:word, false, _}, _book), do: :bool
  defp term_kind({:word, :none, _}, _book), do: {:opt, nil}
  defp term_kind({:word, :some, [t]}, book), do: {:opt, term_kind(t, book)}
  defp term_kind({:word, op, [_x, _]}, _book) when op in [:eq, :lt, :le], do: :bool

  defp term_kind({:word, op, [x, _]}, book) when op in [:cadd, :csub, :cmul, :div, :rem],
    do: {:opt, term_kind(x, book)}

  defp term_kind({:word, op, [x, _]}, book)
       when op in [:add, :sub, :mul, :and, :or, :xor, :shl, :shr],
       do: term_kind(x, book)

  defp term_kind({:word, :not, [x]}, book), do: term_kind(x, book)
  defp term_kind({:beq, _, _}, _book), do: :bool
  defp term_kind({:xeq, _, _}, _book), do: :bool
  defp term_kind({:seq, _, _}, _book), do: :bool
  defp term_kind({:bget, _, _}, _book), do: {:opt, :u8}
  defp term_kind({:aget, _, _}, _book), do: {:opt, :u8}

  defp term_kind({:app, _, _} = t, book) do
    {h, args} = spine(t, [])

    case h do
      {:def, n} ->
        case Enum.find(book, &(Map.get(&1, :name) == n and Map.get(&1, :kind, :def) == :def)) do
          nil ->
            nil

          dfn ->
            {:ok, ty} = Ast.to_db(dfn.type)
            result_kind(ty, length(args))
        end

      _ ->
        nil
    end
  end

  defp term_kind(_, _book), do: nil

  defp result_kind(ty, 0), do: kind_of_annot(ty)
  defp result_kind({:pi, _, _, _, b}, n) when n > 0, do: result_kind(b, n - 1)
  defp result_kind(_, _), do: nil

  defp indent(s, n) do
    pad = String.duplicate(" ", n)

    s
    |> String.split("\n")
    |> Enum.map(&(pad <> &1))
    |> Enum.join("\n")
  end
end

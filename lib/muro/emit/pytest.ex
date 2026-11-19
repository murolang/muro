defmodule Muro.Emit.Pytest do
  @moduledoc """
  Emit a book's closed equations as one pytest module.

  The candidates and the structural skips are `Muro.Emit.Equations`.
  Each candidate is one test function, in book order. A skip is a
  `pytest.mark.skip` test, and it is also returned in `skips`. Nothing
  is dropped.

  The tests call a Python module. The default is the file stem, folded
  to an identifier (`rounding.muro` calls `rounding.round`). `impl:`
  bakes another module into the file. `MURO_IMPL_<STEM>` selects a
  module when the tests run, and that read is not part of the bytes.

  `print_value/2` is the one place a value becomes a Python literal.
  A later `repr` plugs in there.
  """

  alias Muro.Emit
  alias Muro.Emit.{Equations, Name}

  @i64_mod 18_446_744_073_709_551_616
  @i64_half 9_223_372_036_854_775_808

  # Hard keywords. `match` and `case` are soft keywords and stay identifiers.
  @keywords MapSet.new(~w(
    False None True and as assert async await break class continue def del
    elif else except finally for from global if import in is lambda nonlocal
    not or pass raise return try while with yield
  ))

  @doc """
  `{:ok, %{source: source, skips: skips, tests: n}}` or
  `{:error, message}` when the book does not check.

  `book` is the checked book from `Muro.Load.file/2`, without the
  prelude. `opts` accepts `:fuel`, `:root`, `:book`, `:imports`, and
  `:impl` (the default Python module). `tests` counts the equations
  that run. Skips are separate, and every candidate is one or the other.

  `Ast.book_to_db/2` is called with `params: :open`.
  """
  def render(path, book, opts \\ []) when is_binary(path) and is_list(book) and is_list(opts) do
    impl = impl_of(path, opts)

    with :ok <- impl_error(impl),
         {:ok, collected} <-
           Equations.collect(
             path,
             book,
             Keyword.merge(opts, print: &print_value/2, names: &names/1)
           ) do
      items = assign_funs(collected.items)
      {tests, skips} = partition(items)
      source = source(collected.ctx, impl, path, tests, items)
      {:ok, %{source: source, skips: skips, tests: length(tests)}}
    end
  end

  @doc """
  Print one closed normal form as a Python literal.

  `{:ok, source}` or `{:error, reason}`. `reason` is `:function`,
  `:stream`, `:machine`, `:open`, `:shape`, or `{:text, message}`.
  `book` is the named book, so declared constructors are recognized.
  """
  def print_value(term, book) when is_list(book), do: go(term, book)

  @doc """
  Python identifier of one source name.

  A hyphen folds to `_`. An identifier that is not a keyword stays.
  A keyword gains a trailing `_` (`class` is `class_`, `None` is
  `None_`, `lambda` is `lambda_`). Any other character becomes `_`.
  An empty result, or one that starts with a digit, gains the prefix
  `muro_`. `match` and `case` stay, because they are soft keywords.
  """
  def python_base(name) when is_binary(name) do
    folded = String.replace(name, "-", "_")

    cond do
      identifier?(folded) and not keyword?(folded) ->
        folded

      identifier?(folded) ->
        folded <> "_"

      true ->
        scrubbed = String.replace(folded, ~r/[^A-Za-z0-9_]/u, "_")

        scrubbed =
          cond do
            scrubbed == "" -> "muro_"
            String.match?(scrubbed, ~r/\A[0-9]/) -> "muro_" <> scrubbed
            true -> scrubbed
          end

        if keyword?(scrubbed), do: scrubbed <> "_", else: scrubbed
    end
  end

  @doc """
  Default implementation module for `path`: the stem, folded by
  `python_base/1`. `rounding.muro` is `rounding`. `word-kind.muro`
  is `word_kind`.
  """
  def python_module(path) when is_binary(path) do
    path |> Path.basename(".muro") |> python_base()
  end

  @doc """
  True when `name` is a dotted Python module: each segment is an
  identifier and not a keyword.
  """
  def module_name?(name) when is_binary(name) and name != "" do
    segs = String.split(name, ".", trim: false)

    segs != [] and not Enum.any?(segs, &(&1 == "")) and
      Enum.all?(segs, &(identifier?(&1) and not keyword?(&1)))
  end

  def module_name?(_other), do: false

  @doc """
  Environment variable that overrides the baked module.

  The stem's hyphens become `_`, every other character outside
  `[A-Za-z0-9_]` becomes `_`, and the result is uppercased.
  `rounding.muro` is `MURO_IMPL_ROUNDING`. `half_ok.muro` is
  `MURO_IMPL_HALF_OK`. `word-kind.muro` is `MURO_IMPL_WORD_KIND`.
  """
  def impl_env(path) when is_binary(path) do
    stem =
      path
      |> Path.basename(".muro")
      |> String.replace("-", "_")
      |> String.replace(~r/[^A-Za-z0-9_]/u, "_")
      |> String.upcase()

    "MURO_IMPL_" <> stem
  end

  defp names(book), do: Emit.def_names(book, &python_base/1)

  defp impl_of(path, opts) do
    case Keyword.get(opts, :impl) do
      name when is_binary(name) and name != "" -> name
      _other -> python_module(path)
    end
  end

  defp impl_error(impl) do
    if module_name?(impl) do
      :ok
    else
      {:error, "impl must be a Python module name, got: #{inspect(impl)}"}
    end
  end

  defp assign_funs(items) do
    {rev, _used} =
      Enum.reduce(items, {[], MapSet.new()}, fn {tag, row}, {acc, used} ->
        {fun, used} = Name.claim("test_" <> python_base(row.name), used)
        {[{tag, Map.put(row, :py_fun, fun)} | acc], used}
      end)

    Enum.reverse(rev)
  end

  defp partition(items) do
    Enum.reduce(items, {[], []}, fn
      {:test, test}, {tests, skips} -> {tests ++ [test], skips}
      {:skip, skip}, {tests, skips} -> {tests, skips ++ [skip]}
    end)
  end

  defp source(ctx, impl, path, tests, items) do
    body =
      [header(ctx, impl, path, tests), fixture(), tests_src(items)]
      |> Enum.reject(&(&1 == ""))
      |> Enum.join("\n\n")

    String.trim_trailing(body, "\n") <> "\n"
  end

  defp header(ctx, impl, path, tests) do
    env = impl_env(path)
    display = one_line(ctx.display)

    """
    # Closed equations of #{display} as pytest tests.
    # The implementation defaults to #{impl}.
    # #{env} selects another module when the tests run.
    # The bytes of this file do not read that variable.
    import importlib
    import inspect
    import os

    import pytest

    MURO_BOOK = #{py_str(ctx.hash)}
    _MURO_IMPL_ENV = #{py_str(env)}
    _MURO_IMPL_DEFAULT = #{py_str(impl)}
    #{calls_src(tests)}
    """
    |> String.trim_trailing("\n")
  end

  defp calls_src(tests) do
    rows =
      Enum.map(Equations.calls(tests), fn {fun, args} ->
        "    (" <> py_str(fun) <> ", " <> Integer.to_string(length(args)) <> "),"
      end)

    case rows do
      [] -> "_MURO_CALLS = ()"
      _ -> "_MURO_CALLS = (\n" <> Enum.join(rows, "\n") <> "\n)"
    end
  end

  defp fixture do
    ~S"""
    def _muro_accepts(fn, arity):
        try:
            sig = inspect.signature(fn)
        except (ValueError, TypeError):
            return True
        params = list(sig.parameters.values())
        vararg = any(p.kind == inspect.Parameter.VAR_POSITIONAL for p in params)
        positional = [
            p
            for p in params
            if p.kind
            in (
                inspect.Parameter.POSITIONAL_ONLY,
                inspect.Parameter.POSITIONAL_OR_KEYWORD,
            )
        ]
        required = sum(1 for p in positional if p.default is inspect.Parameter.empty)
        if vararg:
            return arity >= required
        return required <= arity <= len(positional)


    @pytest.fixture(scope="module")
    def muro_impl():
        name = os.environ.get(_MURO_IMPL_ENV) or _MURO_IMPL_DEFAULT
        try:
            mod = importlib.import_module(name)
        except Exception as exc:
            pytest.fail(f"implementation module {name} could not be imported: {exc}")
        missing = []
        for fun, arity in _MURO_CALLS:
            fn = getattr(mod, fun, None)
            if not callable(fn) or not _muro_accepts(fn, arity):
                missing.append(f"{fun}/{arity}")
        if missing:
            joined = ", ".join(missing)
            pytest.fail(f"implementation module {name} does not export {joined}")
        return mod
    """
    |> String.trim_trailing("\n")
  end

  defp tests_src([]), do: ""
  defp tests_src(items), do: Enum.map_join(items, "\n\n", &test_clause/1)

  defp test_clause({:test, test}) do
    {id, message} = Equations.label(test)

    """
    @pytest.mark.parametrize("_muro_id", [#{py_str(id)}], ids=[#{py_str(id)}])
    def #{test.py_fun}(_muro_id, muro_impl):
        assert #{side(test.lhs)} == #{side(test.rhs)}, #{py_str(message)}
    """
    |> String.trim_trailing("\n")
  end

  defp test_clause({:skip, skip}) do
    {id, _message} = Equations.label(skip)
    reason = "#{skip.name} (#{skip.file}:#{skip.line}): #{skip.reason}"

    """
    @pytest.mark.skip(reason=#{py_str(reason)})
    @pytest.mark.parametrize("_muro_id", [#{py_str(id)}], ids=[#{py_str(id)}])
    def #{skip.py_fun}(_muro_id):
        pass
    """
    |> String.trim_trailing("\n")
  end

  defp side({:call, fun, []}), do: "muro_impl.#{fun}()"
  defp side({:call, fun, args}), do: "muro_impl.#{fun}(#{Enum.join(args, ", ")})"
  defp side({:value, source}), do: source

  defp one_line(text) do
    text |> to_string() |> String.replace(~r/[\r\n]/, " ")
  end

  defp go(:ze, _book), do: {:ok, "0"}
  defp go({:nat, n}, _book) when is_integer(n) and n >= 0, do: {:ok, Integer.to_string(n)}

  defp go({:su, _} = term, _book) do
    case Muro.Word.nat_closed(term) do
      {:ok, n} -> {:ok, Integer.to_string(n)}
      :error -> {:error, :shape}
    end
  end

  defp go(:one, _book), do: {:ok, "None"}

  defp go({:pair, a, b}, book) do
    with {:ok, x} <- go(a, book), {:ok, y} <- go(b, book) do
      {:ok, "(" <> x <> ", " <> y <> ")"}
    end
  end

  defp go({:ann, term, _ty}, book), do: go(term, book)
  defp go({:rwt, _a, _b, term}, book), do: go(term, book)

  defp go({:word, {:lit, k, n}, []}, _book)
       when k in [:u8, :u32, :u64, :i64] and is_integer(n) do
    {:ok, word_int(k, n)}
  end

  defp go({:word, {:of, k}, [term]}, _book) when k in [:u8, :u32, :u64, :i64] do
    case Muro.Word.nat_closed(term) do
      {:ok, n} -> {:ok, word_int(k, n)}
      :error -> {:error, {:text, "normal form is a word that is not a literal"}}
    end
  end

  defp go({:word, true, []}, _book), do: {:ok, py_str("wtrue")}
  defp go({:word, false, []}, _book), do: {:ok, py_str("wfalse")}
  defp go({:word, :none, []}, _book), do: {:ok, py_str("wnone")}

  defp go({:word, :some, [payload]}, book) do
    case go(payload, book) do
      {:ok, src} -> {:ok, "(" <> py_str("wsome") <> ", " <> src <> ")"}
      {:error, _} = err -> err
    end
  end

  defp go({:word, _, _}, _book),
    do: {:error, {:text, "normal form is a word that is not a literal"}}

  defp go({:slit, bin}, _book) when is_binary(bin) do
    if String.valid?(bin) do
      {:ok, py_str(bin)}
    else
      {:error, {:text, "normal form is a string that is not valid UTF-8"}}
    end
  end

  defp go({:scat, _, _} = term, _book), do: text_literal(term)
  defp go({:sbytes, _} = term, _book), do: text_literal(term)

  defp go({:blit, bin}, _book) when is_binary(bin), do: {:ok, py_bytes(bin)}
  defp go({:bcat, _, _} = term, _book), do: bytes_literal(term)

  defp go({:lam, _, _, _, _}, _book), do: {:error, :function}
  defp go({:pi, _, _, _, _}, _book), do: {:error, :function}
  defp go({:unf, _, _}, _book), do: {:error, :stream}
  defp go({:ucons, _}, _book), do: {:error, :stream}
  defp go({:nu, _}, _book), do: {:error, :stream}
  defp go({:nu, _, _}, _book), do: {:error, :stream}
  defp go({:bisim, _, _}, _book), do: {:error, :stream}
  defp go({:var, _}, _book), do: {:error, :open}
  defp go({:toi64, _}, _book), do: {:error, :machine}
  defp go({:addi, _, _}, _book), do: {:error, :machine}
  defp go({:muli, _, _}, _book), do: {:error, :machine}
  defp go({:addt, _, _}, _book), do: {:error, :machine}
  defp go({:packi, _, _}, _book), do: {:error, :machine}
  defp go({:tensor, _, _}, _book), do: {:error, :machine}
  defp go(:i64, _book), do: {:error, :machine}
  defp go(:f32ty, _book), do: {:error, :machine}
  defp go({:atom, name}, _book) when is_binary(name), do: {:ok, py_str(name)}

  defp go({:def, name}, book) do
    if ctor?(book, name), do: {:ok, py_str(name)}, else: {:error, :open}
  end

  defp go({:app, _, _} = term, book) do
    {head, args} = spine(term, [])

    case head do
      {:def, name} ->
        if ctor?(book, name), do: print_ctor(name, args, book), else: {:error, :open}

      _other ->
        {:error, :shape}
    end
  end

  defp go(_other, _book), do: {:error, :shape}

  defp print_ctor(name, args, book) do
    case print_many(args, book) do
      {:ok, []} -> {:ok, py_str(name)}
      {:ok, srcs} -> {:ok, "(" <> Enum.join([py_str(name) | srcs], ", ") <> ")"}
      {:error, _} = err -> err
    end
  end

  defp print_many(args, book) do
    Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, acc} ->
      case go(arg, book) do
        {:ok, src} -> {:cont, {:ok, acc ++ [src]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp text_literal(term) do
    case flatten_text(term) do
      {:ok, bin} -> {:ok, py_str(bin)}
      :invalid -> {:error, {:text, "normal form is a string that is not valid UTF-8"}}
      :error -> {:error, {:text, "normal form is a string that is not a literal"}}
    end
  end

  defp bytes_literal(term) do
    case flatten_bytes(term) do
      {:ok, bin} -> {:ok, py_bytes(bin)}
      :error -> {:error, {:text, "normal form is bytes that are not a literal"}}
    end
  end

  defp flatten_text({:slit, bin}) when is_binary(bin) do
    if String.valid?(bin), do: {:ok, bin}, else: :invalid
  end

  defp flatten_text({:scat, a, b}) do
    with {:ok, x} <- flatten_text(a), {:ok, y} <- flatten_text(b), do: {:ok, x <> y}
  end

  defp flatten_text({:sbytes, term}) do
    case flatten_bytes(term) do
      {:ok, bin} -> if String.valid?(bin), do: {:ok, bin}, else: :invalid
      :error -> :error
    end
  end

  defp flatten_text(_other), do: :error

  defp flatten_bytes({:blit, bin}) when is_binary(bin), do: {:ok, bin}

  defp flatten_bytes({:bcat, a, b}) do
    with {:ok, x} <- flatten_bytes(a), {:ok, y} <- flatten_bytes(b), do: {:ok, x <> y}
  end

  defp flatten_bytes(_other), do: :error

  defp word_int(:i64, n), do: Integer.to_string(signed_i64(n))

  defp word_int(k, n) when k in [:u8, :u32, :u64] do
    Integer.to_string(Muro.Word.residue(k, n))
  end

  defp signed_i64(n) do
    n = Muro.Word.residue(:i64, n)
    if n < @i64_half, do: n, else: n - @i64_mod
  end

  defp ctor?(book, name) do
    Enum.any?(book, fn
      %{kind: :data, ctors: ctors} -> Enum.any?(ctors, &(&1.name == name))
      _other -> false
    end)
  end

  defp spine({:app, fun, arg}, acc), do: spine(fun, [arg | acc])
  defp spine(head, acc), do: {head, acc}

  defp py_str(text) when is_binary(text) do
    "\"" <> py_str_body(text) <> "\""
  end

  defp py_str_body(<<>>), do: ""

  defp py_str_body(<<char::utf8, rest::binary>>) do
    py_str_char(char) <> py_str_body(rest)
  end

  defp py_str_body(<<byte, rest::binary>>) do
    "\\x" <> hex(byte, 2) <> py_str_body(rest)
  end

  defp py_str_char(?"), do: "\\\""
  defp py_str_char(?\\), do: "\\\\"
  defp py_str_char(?\n), do: "\\n"
  defp py_str_char(?\r), do: "\\r"
  defp py_str_char(?\t), do: "\\t"
  defp py_str_char(char) when char < 32 or char == 127, do: "\\u" <> hex(char, 4)
  defp py_str_char(char) when char > 0xFFFF, do: "\\U" <> hex(char, 8)
  defp py_str_char(char) when char > 126, do: <<char::utf8>>
  defp py_str_char(char), do: <<char>>

  defp py_bytes(bin) when is_binary(bin) do
    body = for <<byte <- bin>>, into: "", do: py_byte(byte)
    "b\"" <> body <> "\""
  end

  defp py_byte(?"), do: "\\\""
  defp py_byte(?\\), do: "\\\\"
  defp py_byte(?\n), do: "\\n"
  defp py_byte(?\r), do: "\\r"
  defp py_byte(?\t), do: "\\t"
  defp py_byte(byte) when byte >= 32 and byte <= 126, do: <<byte>>
  defp py_byte(byte), do: "\\x" <> hex(byte, 2)

  defp hex(n, width) do
    n |> Integer.to_string(16) |> String.downcase() |> String.pad_leading(width, "0")
  end

  defp identifier?(name), do: String.match?(name, ~r/\A[A-Za-z_][A-Za-z0-9_]*\z/)
  defp keyword?(name), do: MapSet.member?(@keywords, name)
end

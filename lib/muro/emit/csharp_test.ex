defmodule Muro.Emit.CSharpTest do
  @moduledoc """
  Emit a book's closed equations as one C# xUnit file.

  The candidates and the structural skips are `Muro.Emit.Equations`.
  Each candidate is one `[Fact]`, in book order. A skip is a `[Fact]`
  with `Skip` set, and it is also returned in `skips`. Nothing is
  dropped.

  With no `impl:`, a fact that reduces on both sides compares the two
  normal forms, and that file compiles in a project that references
  xUnit and nothing else. A param equation, or a side that does not
  reduce to a value, still names a host type (the file stem, unless
  `impl:` names one). There is no C# image beside the file. `impl:`
  names a type and the left-hand side is a call of that type. A
  simple type name is written `global::T`, so it is not a nested
  helper. The path is fixed when the file is written. There is no
  environment override.

  The value helpers live in a nested `public static class MuroValues`.
  The name is reserved, so a constructor or a test method that would
  take it is rewritten.

  `print_value/2` is the one place a value becomes a C# expression.

  `Nat` is `System.Numerics.BigInteger`. A `Nat` is unbounded, and a
  fixed-width integer would wrap. The digits are parsed with
  `NumberStyles.None` and `CultureInfo.InvariantCulture`, so the
  literal does not depend on the host culture. Machine words are the
  matching C# integers: `byte`, `uint`, `ulong`, and `long`. `I64`
  is the signed residue. `long.MinValue` is that constant, because
  the decimal spelling of `-9223372036854775808` does not fit in a
  `long` literal.

  `WBool` is a record holding a `bool`. `Assert.Equal` on two raw
  `bool`s is the xUnit diagnostic xUnit2004, which `dotnet build
  -warnaserror` rejects. A record compares by its field, and the
  assertion is not that overload.

  A constructor is a `readonly record struct`. Equality is
  synthesized and structural, which is what `Assert.Equal` uses.
  A record that holds a `byte[]`, a `List<T>`, or an
  `ImmutableArray<T>` compares those fields by reference, so two
  equal payloads do not compare equal. Bytes are a record of a
  lowercase hex `string`. Strings and atoms are strings inside a
  record for an atom, so an atom does not equal a string of the
  same characters. A pair is a `ValueTuple`. `tt` is an empty
  `readonly record struct`, not `null`.

  A constructor type whose spelling is only lowercase ASCII letters
  gains a trailing `_`. `red` is `red_`. `dotnet build -warnaserror`
  rejects that type name (CS8981). A method keeps the spelling,
  because the warning is about types. A keyword still uses `@`,
  and `@class` is not that warning.

  A test method named `Equals`, `GetHashCode`, `GetType`,
  `ToString`, `Finalize`, or `MemberwiseClone` hides `object` and
  fails `-warnaserror`, and xUnit refuses the first four by name.
  Each gains a trailing `_`. `@` does not rename them. A C# keyword,
  reserved or contextual, is written with `@`.
  """

  alias Muro.{Ast, Check, Emit, Word}
  alias Muro.Emit.{Equations, Name}

  @i64_mod 18_446_744_073_709_551_616
  @i64_half 9_223_372_036_854_775_808
  @i64_min -9_223_372_036_854_775_808

  @used_key :muro_csharp_used

  # Reserved keywords, plus contextual keywords that are not identifiers
  # in a type or member position (`record`, `var`, `file`, `required`,
  # `field`, `extension`, `allows`). `@` in front of any of them is that
  # identifier.
  @keywords MapSet.new(~w(
    abstract as base bool break byte case catch char checked class const
    continue decimal default delegate do double else enum event explicit
    extern false finally fixed float for foreach goto if implicit in int
    interface internal is lock long namespace new null object operator out
    override params private protected public readonly ref return sbyte
    sealed short sizeof stackalloc static string struct switch this throw
    true try typeof uint ulong unchecked unsafe ushort using virtual void
    volatile while add alias allows and args async await by descending
    dynamic equals extension field file from get global group init into
    join let managed nameof nint not notnull nuint on or orderby partial
    record remove required scoped select set unmanaged value var when
    where with yield
  ))

  # Instance methods that hide `object` under `-warnaserror`, or that
  # xUnit rejects as test names. `@` is the same identifier, so the
  # suffix is a different name.
  @object_methods MapSet.new(~w(
    Equals GetHashCode GetType ToString Finalize MemberwiseClone
  ))

  # Nested in the test class. A constructor or a test method that
  # folds to one of these takes the next free spelling. The helper
  # class is `MuroValues`, not `Values`, so an impl or stem named
  # `Values` is not the helper class.
  @helper_types MapSet.new(~w(
    Unit MuroBytes MuroAtom MuroNone MuroSome MuroWBool MuroNat MuroValues
  ))

  @reserved_methods MapSet.new(["MURO_BOOK", "MuroValues"])

  @doc """
  `{:ok, %{source: source, skips: skips, tests: n}}` or
  `{:error, message}` when the book does not check, or when `impl:`
  is not a C# type name.

  `book` is the checked book from `Muro.Load.file/2`, without the
  prelude. `opts` accepts `:fuel`, `:root`, `:book`, `:imports`, and
  `:impl` (a C# type). `tests` counts the equations that run. Skips
  are separate, and every candidate is one or the other.

  `Ast.book_to_db/2` is called with `params: :open`.
  """
  def render(path, book, opts \\ []) when is_binary(path) and is_list(book) and is_list(opts) do
    {impl, explicit?} = impl_of(path, opts)

    with :ok <- impl_error(impl) do
      Process.put(@used_key, empty_used())

      try do
        render_noted(path, book, opts, impl, explicit?)
      after
        Process.delete(@used_key)
      end
    end
  end

  @doc """
  Print one closed normal form as a C# expression.

  `{:ok, source}` or `{:error, reason}`. `reason` is `:function`,
  `:stream`, `:machine`, `:open`, `:shape`, or `{:text, message}`.
  `book` is the named book, so declared constructors are recognized.
  """
  def print_value(term, book) when is_list(book) do
    gloss = glossary(book)

    case typed(peel(term), book, gloss) do
      {:ok, source, _ty} -> {:ok, source}
      {:error, _} = err -> err
    end
  end

  @doc """
  C# identifier of one source name, before a collision suffix.

  A hyphen folds to `_`. Any other character outside `[A-Za-z0-9_]`
  becomes `_`. An empty result, or one that starts with a digit, gains
  the prefix `muro_`. A name that hides `object` gains a trailing `_`.
  A keyword, reserved or contextual, is written with `@`. A method
  does not gain the trailing `_` that a lowercase type name gains,
  so `red` stays `red`.
  """
  def ident(name) when is_binary(name), do: finish_method(fold_plain(name))

  @doc """
  Type identifier of one source name, before a collision suffix.

  The fold is `ident/1`. A keyword is written with `@`. A name that
  is only lowercase ASCII letters gains a trailing `_` (`red` is
  `red_`), so a record of that name is not CS8981. A type is not an
  `object` method, so `Equals` stays `Equals` and `record` is
  `@record`.
  """
  def type_ident(name) when is_binary(name), do: finish_type(fold_plain(name))

  @doc """
  Test class for `path`. The stem is folded, then `Tests` is appended.
  `rounding.muro` is `roundingTests`. `word-kind.muro` is
  `word_kindTests`. `class.muro` is `classTests`.
  """
  def class_name(path) when is_binary(path) do
    path |> Path.basename(".muro") |> fold_plain() |> then(&finish_type(&1 <> "Tests"))
  end

  @doc """
  Default type the tests call when an equation does not reduce to a
  value. `rounding.muro` is `rounding`. `class.muro` is `@class`.
  `2nd.muro` is `muro_2nd`.
  """
  def impl_type(path) when is_binary(path) do
    path |> Path.basename(".muro") |> fold_plain() |> finish_keyword()
  end

  @doc """
  True when `name` is a C# type name. Each segment is an identifier
  that is not a keyword, or `@` plus an identifier. A bare keyword is
  refused. An empty segment is refused. `Host.Rounding` and `@class`
  are accepted. `class`, `1bad`, `.Rounding`, and `Rounding.` are not.
  """
  def type_name?(name) when is_binary(name) and name != "" do
    segs = String.split(name, ".", trim: false)
    segs != [] and Enum.all?(segs, &type_segment?/1)
  end

  def type_name?(_other), do: false

  defp render_noted(path, book, opts, impl, explicit?) do
    gloss = glossary(book)

    with {:ok, collected} <-
           Equations.collect(path, book, collect_opts(opts, gloss)) do
      items =
        if explicit?,
          do: collected.items,
          else: oracle_items(collected.items, book, collected.ctx)

      used = Process.get(@used_key) || empty_used()
      items = assign_funs(items)
      {tests, skips} = partition(items)

      source =
        source(collected.ctx, impl, explicit?, class_name(path), items, used, gloss)

      {:ok, %{source: source, skips: skips, tests: length(tests)}}
    end
  end

  defp collect_opts(opts, gloss) do
    Keyword.merge(opts,
      print: fn term, scope ->
        case typed(peel(term), scope, gloss) do
          {:ok, source, _ty} -> {:ok, source}
          {:error, _} = err -> err
        end
      end,
      names: &method_names/1
    )
  end

  defp impl_of(path, opts) do
    case Keyword.get(opts, :impl) do
      name when is_binary(name) and name != "" -> {name, true}
      _other -> {impl_type(path), false}
    end
  end

  defp impl_error(impl) do
    if type_name?(impl) do
      :ok
    else
      {:error, "impl must be a C# type name, got: #{inspect(impl)}"}
    end
  end

  # The collector's left-hand side is a call. Print the normal form of
  # the whole left-hand side when it has one, so the fact names no host
  # type. A param, or a term this printer cannot write, keeps the call.
  defp oracle_items(items, book, ctx) do
    Enum.map(items, fn
      {:test, test} = item ->
        case evidence_lhs(book, ctx, test) do
          nil ->
            item

          lhs ->
            case normalize_print(lhs, ctx) do
              {:ok, source} -> {:test, %{test | lhs: {:value, source}}}
              :error -> item
            end
        end

      other ->
        other
    end)
  end

  defp evidence_lhs(book, ctx, test) do
    Enum.find_value(book, fn d ->
      if evidence?(d) and d.name == test.name and line_of(d) == test.line and
           Equations.display_for(d, ctx) == test.file do
        case Map.get(d, :type) do
          {:idt, _ty, lhs, _rhs} -> lhs
          _other -> nil
        end
      end
    end)
  end

  defp evidence?(d) do
    Map.get(d, :kind, :def) == :def and Map.get(d, :mode) == :evidence
  end

  defp normalize_print(term, ctx) do
    with {:ok, db} <- Ast.to_db(term),
         {:ok, nf} <- Check.normalize(ctx.db, db, ctx.fuel),
         {:ok, source} <- ctx.print.(nf, ctx.scope) do
      {:ok, source}
    else
      _other -> :error
    end
  end

  defp line_of(%{loc: {line, _col}}), do: line
  defp line_of(_other), do: 0

  defp method_names(book) do
    {map, _} =
      Enum.reduce(Emit.run_defs(book), {%{}, MapSet.new()}, fn %{name: name}, {map, used} ->
        {emitted, used} = claim_method(name, used, MapSet.new())
        {Map.put(map, name, emitted), used}
      end)

    map
  end

  defp assign_funs(items) do
    {rev, _used} =
      Enum.reduce(items, {[], @reserved_methods}, fn {tag, row}, {acc, used} ->
        {fun, used} = claim_method(row.name, used, @reserved_methods)
        {[{tag, Map.put(row, :cs_fun, fun)} | acc], used}
      end)

    Enum.reverse(rev)
  end

  defp claim_method(name, used, reserved) do
    claim_free(fold_plain(name), used, &finish_method/1, reserved)
  end

  defp claim_type(name, used) do
    claim_free(fold_plain(name), used, &finish_type/1, @helper_types)
  end

  # `Name.claim` records the folded spelling. `finish_method` then
  # rewrites `Equals` to `Equals_` and `class` to `@class`. Record that
  # finished spelling, or the next evidence takes the same identifier.
  defp claim_free(base, used, finish, reserved) do
    {chosen, used} = Name.claim(base, used)
    finished = finish.(chosen)

    if MapSet.member?(reserved, finished) or
         (finished != chosen and MapSet.member?(used, finished)) do
      claim_free(base, MapSet.put(used, finished), finish, reserved)
    else
      {finished, MapSet.put(used, finished)}
    end
  end

  defp fold_plain(name) do
    folded =
      name
      |> String.replace("-", "_")
      |> String.replace(~r/[^A-Za-z0-9_]/u, "_")

    cond do
      folded == "" -> "muro_"
      String.match?(folded, ~r/\A[0-9]/) -> "muro_" <> folded
      true -> folded
    end
  end

  defp finish_method(name) do
    name = if MapSet.member?(@object_methods, name), do: name <> "_", else: name
    finish_keyword(name)
  end

  # A type we declare. `@` covers a keyword. A name of only lowercase
  # ASCII letters is CS8981 under `-warnaserror`, so it gains `_`.
  # `@class` is already not that spelling.
  defp finish_type(name) do
    name = finish_keyword(name)

    cond do
      String.starts_with?(name, "@") -> name
      lowercase_type?(name) -> name <> "_"
      true -> name
    end
  end

  defp finish_keyword(name) do
    if keyword?(name), do: "@" <> name, else: name
  end

  defp lowercase_type?(name), do: String.match?(name, ~r/\A[a-z]+\z/)

  defp keyword?(name), do: MapSet.member?(@keywords, name)

  defp type_segment?("@" <> ident), do: identifier?(ident)
  defp type_segment?(seg), do: identifier?(seg) and not keyword?(seg)

  defp identifier?(name), do: String.match?(name, ~r/\A[A-Za-z_][A-Za-z0-9_]*\z/)

  defp partition(items) do
    {tests, skips} =
      Enum.reduce(items, {[], []}, fn
        {:test, test}, {tests, skips} -> {[test | tests], skips}
        {:skip, skip}, {tests, skips} -> {tests, [skip | skips]}
      end)

    {Enum.reverse(tests), Enum.reverse(skips)}
  end

  defp source(ctx, impl, explicit?, class, items, used, gloss) do
    parts =
      [
        header(ctx, impl, explicit?),
        usings(used),
        class_src(ctx, class, impl, items, used, gloss)
      ]
      |> Enum.reject(&(&1 == ""))

    Enum.join(parts, "\n\n") <> "\n"
  end

  defp header(ctx, impl, explicit?) do
    display = one_line(ctx.display)

    call =
      if explicit? do
        "Each fact calls #{impl}."
      else
        "Each fact compares the two normal forms. A call names #{impl}."
      end

    """
    // Closed equations of #{display} as C# tests.
    // #{call}
    // A skipped fact records an equation this encoding does not write.
    """
    |> String.trim_trailing("\n")
  end

  defp usings(used) do
    rows =
      if used.nat do
        ["using System.Globalization;", "using System.Numerics;"]
      else
        []
      end

    Enum.join(rows, "\n")
  end

  defp class_src(ctx, class, impl, items, used, gloss) do
    body =
      [const_src(ctx), values_src(used, gloss), tests_src(items, impl)]
      |> Enum.reject(&(&1 == ""))
      |> Enum.join("\n\n")

    """
    public class #{class}
    {
    #{indent(body, 4)}
    }
    """
    |> String.trim_trailing("\n")
  end

  defp const_src(ctx) do
    "public const string MURO_BOOK = #{cs_str(ctx.hash)};"
  end

  defp values_src(used, gloss) do
    rows = helper_rows(used) ++ ctor_rows(used, gloss)

    if rows == [] do
      ""
    else
      body = Enum.join(rows, "\n")

      """
      public static class MuroValues
      {
      #{indent(body, 4)}
      }
      """
      |> String.trim_trailing("\n")
    end
  end

  defp helper_rows(used) do
    rows =
      []
      |> add_row(used.unit, "public readonly record struct Unit;")
      |> add_row(used.bytes, "public readonly record struct MuroBytes(string Hex);")
      |> add_row(used.atom, "public readonly record struct MuroAtom(string Name);")
      |> add_row(used.none, "public readonly record struct MuroNone;")
      |> add_row(used.some, "public readonly record struct MuroSome<T0>(T0 F0);")
      |> add_row(used.wbool, "public readonly record struct MuroWBool(bool Value);")

    rows =
      if used.nat do
        rows ++
          [
            """
            public static BigInteger MuroNat(string digits) =>
                BigInteger.Parse(digits, NumberStyles.None, CultureInfo.InvariantCulture);
            """
            |> String.trim_trailing("\n")
          ]
      else
        rows
      end

    rows
  end

  defp add_row(rows, true, row), do: rows ++ [row]
  defp add_row(rows, false, _row), do: rows

  defp ctor_rows(used, gloss) do
    gloss.order
    |> Enum.filter(&MapSet.member?(used.ctors, &1))
    |> Enum.map(fn name ->
      info = Map.fetch!(gloss.ctors, name)
      record_decl(info.cs, info.live)
    end)
  end

  defp record_decl(name, 0), do: "public readonly record struct #{name};"

  defp record_decl(name, n) when n > 0 do
    params = Enum.map_join(0..(n - 1), ", ", &"T#{&1}")
    fields = Enum.map_join(0..(n - 1), ", ", &"T#{&1} F#{&1}")
    "public readonly record struct #{name}<#{params}>(#{fields});"
  end

  defp tests_src([], _impl), do: ""
  defp tests_src(items, impl), do: Enum.map_join(items, "\n\n", &test_clause(&1, impl))

  defp test_clause({:test, test}, impl) do
    {_id, message} = Equations.label(test)

    """
    [Xunit.Fact(DisplayName = #{cs_str(message)})]
    public void #{test.cs_fun}()
    {
        Xunit.Assert.Equal(#{side(test.rhs, impl)}, #{side(test.lhs, impl)});
    }
    """
    |> String.trim_trailing("\n")
  end

  defp test_clause({:skip, skip}, _impl) do
    {_id, message} = Equations.label(skip)
    reason = "#{skip.name} (#{skip.file}:#{skip.line}): #{skip.reason}"

    """
    [Xunit.Fact(DisplayName = #{cs_str(message)}, Skip = #{cs_str(reason)})]
    public void #{skip.cs_fun}()
    {
    }
    """
    |> String.trim_trailing("\n")
  end

  # The right-hand side is the expected value. `Assert.Equal` takes
  # that argument first. A call names the implementation type. A
  # simple (non-namespaced) name is written `global::T`, so a stem
  # or `--impl` of `Values` is not the nested helper `MuroValues`,
  # and a name that matches a nested type is looked up globally.
  defp side({:call, fun, []}, impl), do: "#{qualify_impl(impl)}.#{fun}()"

  defp side({:call, fun, args}, impl),
    do: "#{qualify_impl(impl)}.#{fun}(#{Enum.join(args, ", ")})"

  defp side({:value, source}, _impl), do: source

  defp qualify_impl(impl) do
    if String.contains?(impl, "."), do: impl, else: "global::" <> impl
  end

  defp one_line(text) do
    text |> to_string() |> String.replace(~r/[\r\n]/, " ")
  end

  defp indent(text, n) do
    pad = String.duplicate(" ", n)

    text
    |> String.split("\n")
    |> Enum.map_join("\n", fn
      "" -> ""
      line -> pad <> line
    end)
  end

  defp empty_used do
    %{
      nat: false,
      bytes: false,
      atom: false,
      unit: false,
      none: false,
      some: false,
      wbool: false,
      ctors: MapSet.new()
    }
  end

  defp note(flag) when is_atom(flag) do
    case Process.get(@used_key) do
      nil -> :ok
      used -> Process.put(@used_key, Map.put(used, flag, true))
    end
  end

  defp note_ctor(name) when is_binary(name) do
    case Process.get(@used_key) do
      nil ->
        :ok

      used ->
        Process.put(@used_key, %{used | ctors: MapSet.put(used.ctors, name)})
    end
  end

  defp glossary(book) do
    {ctors, _amb, _used, order} =
      Enum.reduce(book, {%{}, MapSet.new(), @helper_types, []}, fn
        %{kind: :data, name: data, ctors: declared}, {ctors, amb, used, order} ->
          Enum.reduce(declared, {ctors, amb, used, order}, fn ctor, {ctors, amb, used, order} ->
            add_ctor(ctors, amb, used, order, ctor, data)
          end)

        _other, acc ->
          acc
      end)

    %{ctors: ctors, order: Enum.reverse(order)}
  end

  defp add_ctor(ctors, amb, used, order, ctor, data) do
    name = ctor.name

    cond do
      MapSet.member?(amb, name) ->
        {ctors, amb, used, order}

      Map.has_key?(ctors, name) ->
        {Map.delete(ctors, name), MapSet.put(amb, name), used, List.delete(order, name)}

      true ->
        qtys = qty_list(ctor.type)
        {cs, used} = claim_type(name, used)
        live = Enum.count(qtys, &(&1 != :erased))
        info = %{cs: cs, qtys: qtys, live: live, data: data}
        {Map.put(ctors, name, info), amb, used, [name | order]}
    end
  end

  defp qty_list({:pi, qty, _a, _x, b}), do: [qty | qty_list(b)]
  defp qty_list({:ann, t, _}), do: qty_list(t)
  defp qty_list(_other), do: []

  defp peel({:ann, term, _ty}), do: peel(term)
  defp peel({:rwt, _a, _b, term}), do: peel(term)
  defp peel(term), do: term

  defp typed(:ze, _book, _gloss), do: nat_src(0)

  defp typed({:nat, n}, _book, _gloss) when is_integer(n) and n >= 0, do: nat_src(n)

  defp typed({:su, _} = term, _book, _gloss) do
    case Word.nat_closed(term) do
      {:ok, n} -> nat_src(n)
      :error -> {:error, :shape}
    end
  end

  defp typed(:one, _book, _gloss) do
    note(:unit)
    {:ok, "new MuroValues.Unit()", "MuroValues.Unit"}
  end

  defp typed({:pair, a, b}, book, gloss) do
    with {:ok, x, tx} <- typed(peel(a), book, gloss),
         {:ok, y, ty} <- typed(peel(b), book, gloss) do
      {:ok, "(#{x}, #{y})", "(#{tx}, #{ty})"}
    end
  end

  defp typed({:word, {:lit, k, n}, []}, _book, _gloss)
       when k in [:u8, :u32, :u64, :i64] and is_integer(n) do
    word_src(k, n)
  end

  defp typed({:word, {:of, k}, [term]}, _book, _gloss) when k in [:u8, :u32, :u64, :i64] do
    case Word.nat_closed(term) do
      {:ok, n} -> word_src(k, n)
      :error -> {:error, {:text, "normal form is a word that is not a literal"}}
    end
  end

  defp typed({:word, true, []}, _book, _gloss), do: wbool_src(true)
  defp typed({:word, false, []}, _book, _gloss), do: wbool_src(false)

  defp typed({:word, :none, []}, _book, _gloss) do
    note(:none)
    {:ok, "new MuroValues.MuroNone()", "MuroValues.MuroNone"}
  end

  defp typed({:word, :some, [payload]}, book, gloss) do
    case typed(peel(payload), book, gloss) do
      {:ok, src, ty} ->
        note(:some)
        {:ok, "new MuroValues.MuroSome<#{ty}>(#{src})", "MuroValues.MuroSome<#{ty}>"}

      {:error, _} = err ->
        err
    end
  end

  defp typed({:word, _, _}, _book, _gloss),
    do: {:error, {:text, "normal form is a word that is not a literal"}}

  defp typed({:slit, bin}, _book, _gloss) when is_binary(bin), do: text_literal(bin)
  defp typed({:scat, _, _} = term, _book, _gloss), do: text_term(term)
  defp typed({:sbytes, _} = term, _book, _gloss), do: text_term(term)
  defp typed({:blit, bin}, _book, _gloss) when is_binary(bin), do: bytes_literal(bin)
  defp typed({:bcat, _, _} = term, _book, _gloss), do: bytes_term(term)

  defp typed({:atom, name}, _book, _gloss) when is_binary(name) do
    note(:atom)
    {:ok, "new MuroValues.MuroAtom(#{cs_str(name)})", "MuroValues.MuroAtom"}
  end

  defp typed({:lam, _, _, _, _}, _book, _gloss), do: {:error, :function}
  defp typed({:pi, _, _, _, _}, _book, _gloss), do: {:error, :function}
  defp typed({:unf, _, _}, _book, _gloss), do: {:error, :stream}
  defp typed({:ucons, _}, _book, _gloss), do: {:error, :stream}
  defp typed({:nu, _}, _book, _gloss), do: {:error, :stream}
  defp typed({:nu, _, _}, _book, _gloss), do: {:error, :stream}
  defp typed({:bisim, _, _}, _book, _gloss), do: {:error, :stream}
  defp typed({:var, _}, _book, _gloss), do: {:error, :open}
  defp typed(:erased, _book, _gloss), do: {:error, {:text, "normal form is erased"}}
  defp typed({:erased, _}, _book, _gloss), do: {:error, {:text, "normal form is erased"}}
  defp typed({:toi64, _}, _book, _gloss), do: {:error, :machine}
  defp typed({:addi, _, _}, _book, _gloss), do: {:error, :machine}
  defp typed({:muli, _, _}, _book, _gloss), do: {:error, :machine}
  defp typed({:addt, _, _}, _book, _gloss), do: {:error, :machine}
  defp typed({:packi, _, _}, _book, _gloss), do: {:error, :machine}
  defp typed({:tensor, _, _}, _book, _gloss), do: {:error, :machine}
  defp typed(:i64, _book, _gloss), do: {:error, :machine}
  defp typed(:f32ty, _book, _gloss), do: {:error, :machine}

  defp typed({:def, name}, book, gloss), do: print_ctor(name, [], book, gloss)

  defp typed({:con, _data, name, args}, book, gloss), do: print_ctor(name, args, book, gloss)

  defp typed({:app, _, _} = term, book, gloss) do
    {head, args} = spine(term, [])

    case head do
      {:def, name} -> print_ctor(name, args, book, gloss)
      {:con, _data, name, inner} -> print_ctor(name, inner ++ args, book, gloss)
      _other -> {:error, :shape}
    end
  end

  defp typed(_other, _book, _gloss), do: {:error, :shape}

  defp nat_src(n) when is_integer(n) and n >= 0 do
    note(:nat)
    {:ok, "MuroValues.MuroNat(#{cs_str(Integer.to_string(n))})", "BigInteger"}
  end

  defp wbool_src(value) when is_boolean(value) do
    note(:wbool)
    lit = if value, do: "true", else: "false"
    {:ok, "new MuroValues.MuroWBool(#{lit})", "MuroValues.MuroWBool"}
  end

  defp word_src(k, n) do
    n = Word.residue(k, n)

    case k do
      :u8 -> {:ok, "(byte)#{n}", "byte"}
      :u32 -> {:ok, "#{n}u", "uint"}
      :u64 -> {:ok, "#{n}UL", "ulong"}
      :i64 -> i64_src(signed_i64(n))
    end
  end

  defp i64_src(@i64_min), do: {:ok, "long.MinValue", "long"}
  defp i64_src(n) when is_integer(n), do: {:ok, "#{n}L", "long"}

  defp signed_i64(n) do
    n = Word.residue(:i64, n)
    if n < @i64_half, do: n, else: n - @i64_mod
  end

  defp print_ctor(name, args, book, gloss) do
    case Map.fetch(gloss.ctors, name) do
      :error ->
        {:error, :open}

      {:ok, info} ->
        case live_args(info, args) do
          {:ok, live} ->
            case print_many(live, book, gloss) do
              {:ok, srcs, tys} ->
                note_ctor(name)
                ctor_src(info.cs, srcs, tys)

              {:error, _} = err ->
                err
            end

          :partial ->
            {:error, :function}

          :error ->
            {:error, :shape}
        end
    end
  end

  defp ctor_src(name, [], []) do
    {:ok, "new MuroValues.#{name}()", "MuroValues.#{name}"}
  end

  defp ctor_src(name, srcs, tys) do
    args = Enum.join(tys, ", ")
    fields = Enum.join(srcs, ", ")
    {:ok, "new MuroValues.#{name}<#{args}>(#{fields})", "MuroValues.#{name}<#{args}>"}
  end

  defp live_args(info, args) do
    qtys = info.qtys
    live = info.live
    n = length(args)

    cond do
      qtys != [] and n == length(qtys) ->
        kept =
          args
          |> Enum.zip(qtys)
          |> Enum.reject(fn {_arg, qty} -> qty == :erased end)
          |> Enum.map(&elem(&1, 0))

        if length(kept) == live, do: {:ok, kept}, else: :error

      n == live ->
        {:ok, args}

      n < live ->
        :partial

      true ->
        :error
    end
  end

  defp print_many(args, book, gloss) do
    Enum.reduce_while(args, {:ok, [], []}, fn arg, {:ok, srcs, tys} ->
      case typed(peel(arg), book, gloss) do
        {:ok, src, ty} -> {:cont, {:ok, srcs ++ [src], tys ++ [ty]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp text_term(term) do
    case flatten_text(term) do
      {:ok, bin} -> text_literal(bin)
      :invalid -> {:error, {:text, "normal form is a string that is not valid UTF-8"}}
      :error -> {:error, {:text, "normal form is a string that is not a literal"}}
    end
  end

  defp text_literal(bin) do
    if String.valid?(bin) do
      {:ok, cs_str(bin), "string"}
    else
      {:error, {:text, "normal form is a string that is not valid UTF-8"}}
    end
  end

  defp bytes_term(term) do
    case flatten_bytes(term) do
      {:ok, bin} -> bytes_literal(bin)
      :error -> {:error, {:text, "normal form is bytes that are not a literal"}}
    end
  end

  defp bytes_literal(bin) do
    note(:bytes)
    hex = Base.encode16(bin, case: :lower)
    {:ok, "new MuroValues.MuroBytes(#{cs_str(hex)})", "MuroValues.MuroBytes"}
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

  defp spine({:app, fun, arg}, acc), do: spine(fun, [arg | acc])
  defp spine(head, acc), do: {head, acc}

  defp cs_str(text) when is_binary(text) do
    "\"" <> cs_str_body(text) <> "\""
  end

  defp cs_str_body(<<>>), do: ""

  defp cs_str_body(<<char::utf8, rest::binary>>) do
    cs_char(char) <> cs_str_body(rest)
  end

  defp cs_str_body(<<byte, rest::binary>>) do
    "\\u" <> hex4(byte) <> cs_str_body(rest)
  end

  defp cs_char(?"), do: "\\\""
  defp cs_char(?\\), do: "\\\\"
  defp cs_char(?\n), do: "\\n"
  defp cs_char(?\r), do: "\\r"
  defp cs_char(?\t), do: "\\t"
  defp cs_char(char) when char < 32 or char == 127, do: "\\u" <> hex4(char)
  defp cs_char(char), do: <<char::utf8>>

  defp hex4(n) do
    n |> Integer.to_string(16) |> String.pad_leading(4, "0") |> String.downcase()
  end
end

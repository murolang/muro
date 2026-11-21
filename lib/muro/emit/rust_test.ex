defmodule Muro.Emit.RustTest do
  @moduledoc """
  Emit a book's closed equations as one Rust test file.

  The candidates and the structural skips are `Muro.Emit.Equations`.
  Each candidate is one test function, in book order. A skip is a
  `#[test]` function marked `#[ignore = "..."]`, and it is also returned
  in `skips`. Nothing is dropped.

  The tests call a Rust path. The default is the file beside this one:
  `#[path = "<stem>.rs"] mod <ident>;`, then `<ident>::<run>(...)`.
  `rounding.muro` calls `rounding::round`. `impl:` bakes another path
  into the file. The path is fixed when the file is written. There is
  no environment override.

  `print_value/3` is the one place a value becomes a Rust expression.
  It uses the constructor spellings `Muro.Emit.Rust` gives the image.
  """

  alias Muro.{Prelude, Word}
  alias Muro.Emit.{Equations, Name, Rust}

  @u64_max 18_446_744_073_709_551_615
  # `muro__from_u64` builds one successor per unit. The same cap the C
  # session image uses before it builds a Peano nat. Above it, the test
  # is a skip instead of a chain that hangs or exhausts memory.
  @nat_build_max 100_000

  @doc """
  `{:ok, %{source: source, skips: skips, tests: n}}` or
  `{:error, message}` when the book does not check, or when `impl:`
  is not a Rust path.

  `book` is the checked book from `Muro.Load.file/2`, without the
  prelude. `opts` accepts `:fuel`, `:root`, `:book`, `:imports`, and
  `:impl` (a Rust path). `tests` counts the equations that run. Skips
  are separate, and every candidate is one or the other.

  `Ast.book_to_db/2` is called with `params: :open`.
  """
  def render(path, book, opts \\ []) when is_binary(path) and is_list(book) and is_list(opts) do
    {mod, explicit?} = impl_of(path, opts)

    with :ok <- impl_error(mod),
         {:ok, collected} <-
           Equations.collect(path, book, collect_opts(book, opts, mod_prefix(mod))) do
      reserved = reserved_names(mod, explicit?)
      items = assign_funs(collected.items, reserved)
      {tests, skips} = partition(items)
      source = source(collected.ctx, mod, path, explicit?, mod_prefix(mod), items)
      {:ok, %{source: source, skips: skips, tests: length(tests)}}
    end
  end

  @doc """
  Print one closed normal form as a Rust expression.

  `prefix` is a module path and a trailing `::`, or `""` when the
  expression is written inside the image. `{:ok, source}` or
  `{:error, reason}`. `reason` is `:function`, `:stream`, `:machine`,
  `:open`, `:shape`, or `{:text, message}`. `book` is the named book,
  so declared constructors are recognized.
  """
  def print_value(term, book, prefix \\ "") when is_list(book) and is_binary(prefix) do
    gloss = Rust.glossary(Prelude.for_emit(book))
    print_term(term, book, gloss, prefix)
  end

  @doc """
  Rust identifier of one source name, before a collision suffix.

  A hyphen folds to `_`. Any other character outside `[A-Za-z0-9_]`
  becomes `_`. An empty result, or one that starts with a digit, gains
  the prefix `muro_`. A keyword that can be raw is `r#` plus the
  identifier (`loop` is `r#loop`). `crate`, `self`, `super`, and `Self`
  cannot be raw, so each gains a trailing `_`.
  """
  def test_ident(name) when is_binary(name), do: finish_ident(fold_plain(name))

  @doc """
  Module identifier for `path`: the stem, folded by `test_ident/1`.
  `rounding.muro` is `rounding`. `word-kind.muro` is `word_kind`.
  `fn.muro` is `r#fn`. `crate.muro` is `crate_`.
  """
  def module_ident(path) when is_binary(path) do
    path |> Path.basename(".muro") |> test_ident()
  end

  @doc """
  File name the default tests include. `word-kind.muro` is
  `word-kind.rs`. The module identifier may differ.
  """
  def sibling_file(path) when is_binary(path) do
    Path.basename(path, ".muro") <> ".rs"
  end

  @doc """
  True when `name` is a Rust path. Each segment is an identifier that
  is not a keyword, a path keyword (`crate`, `self`, `super`, `Self`),
  or `r#` plus an identifier that is not one of those four. An empty
  segment is refused.
  """
  def module_path?(name) when is_binary(name) and name != "" do
    segs = String.split(name, "::", trim: false)
    segs != [] and Enum.all?(segs, &segment?/1)
  end

  def module_path?(_other), do: false

  defp collect_opts(book, opts, prefix) do
    gloss = Rust.glossary(Prelude.for_emit(book))

    Keyword.merge(opts,
      print: fn term, scope -> print_term(term, scope, gloss, prefix) end,
      names: fn _emit -> gloss.names end
    )
  end

  defp impl_of(path, opts) do
    case Keyword.get(opts, :impl) do
      name when is_binary(name) and name != "" -> {name, true}
      _other -> {module_ident(path), false}
    end
  end

  defp impl_error(mod) do
    if module_path?(mod) do
      :ok
    else
      {:error, "impl must be a Rust path, got: #{inspect(mod)}"}
    end
  end

  defp mod_prefix(mod), do: mod <> "::"

  defp reserved_names(_mod, true), do: ["MURO_BOOK"]
  defp reserved_names(mod, false), do: [mod, "MURO_BOOK"]

  defp assign_funs(items, reserved) do
    {rev, _used} =
      Enum.reduce(items, {[], MapSet.new()}, fn {tag, row}, {acc, used} ->
        {fun, used} = claim_test(row.name, used, reserved)
        {[{tag, Map.put(row, :rs_fun, fun)} | acc], used}
      end)

    Enum.reverse(rev)
  end

  defp claim_test(name, used, reserved), do: claim_free(fold_plain(name), used, reserved)

  # `Name.claim` records the folded spelling. `finish_ident` then
  # rewrites `crate` to `crate_`. Record that finished spelling too,
  # or an evidence named `crate_` is a second `fn crate_()`.
  defp claim_free(base, used, reserved) do
    {chosen, used} = Name.claim(base, used)
    finished = finish_ident(chosen)

    if finished in reserved or (finished != chosen and MapSet.member?(used, finished)) do
      claim_free(base, MapSet.put(used, finished), reserved)
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

  defp finish_ident(name) do
    cond do
      Rust.keyword?(name) and Rust.raw_forbidden?(name) -> name <> "_"
      Rust.keyword?(name) -> "r#" <> name
      true -> name
    end
  end

  defp segment?("r#" <> ident) do
    identifier?(ident) and not Rust.raw_forbidden?(ident)
  end

  defp segment?(seg) do
    cond do
      Rust.raw_forbidden?(seg) -> true
      Rust.keyword?(seg) -> false
      true -> identifier?(seg)
    end
  end

  defp identifier?(name), do: String.match?(name, ~r/\A[A-Za-z_][A-Za-z0-9_]*\z/)

  defp partition(items) do
    {tests, skips} =
      Enum.reduce(items, {[], []}, fn
        {:test, test}, {tests, skips} -> {[test | tests], skips}
        {:skip, skip}, {tests, skips} -> {tests, [skip | skips]}
      end)

    {Enum.reverse(tests), Enum.reverse(skips)}
  end

  defp source(ctx, mod, path, explicit?, prefix, items) do
    body =
      [header(ctx, mod, path, explicit?), tests_src(items, prefix)]
      |> Enum.reject(&(&1 == ""))
      |> Enum.join("\n\n")

    String.trim_trailing(body, "\n") <> "\n"
  end

  defp header(ctx, mod, path, explicit?) do
    display = one_line(ctx.display)
    file = sibling_file(path)

    call =
      if explicit? do
        "// The tests call #{mod}."
      else
        """
        // The tests call #{mod}, the module in #{file} beside this file.
        // `rustc --test` accepts the two files as siblings.
        // A Cargo `tests/` directory passes `--impl crate::module`.
        """
        |> String.trim_trailing("\n")
      end

    mod_item =
      if explicit? do
        ""
      else
        "#[path = #{rust_str(file)}]\nmod #{mod};"
      end

    """
    // Closed equations of #{display} as Rust tests.
    #{call}
    #![allow(unused, non_snake_case, non_camel_case_types)]

    const MURO_BOOK: &str = #{rust_str(ctx.hash)};
    #{mod_item}
    """
    |> String.trim_trailing()
  end

  defp tests_src([], _prefix), do: ""
  defp tests_src(items, prefix), do: Enum.map_join(items, "\n\n", &test_clause(&1, prefix))

  defp test_clause({:test, test}, prefix) do
    {_id, message} = Equations.label(test)

    """
    #[test]
    fn #{test.rs_fun}() {
        assert_eq!(#{side(prefix, test.lhs)}, #{side(prefix, test.rhs)}, #{rust_str(message)});
    }
    """
    |> String.trim_trailing("\n")
  end

  defp test_clause({:skip, skip}, _prefix) do
    reason = "#{skip.name} (#{skip.file}:#{skip.line}): #{skip.reason}"

    """
    #[test]
    #[ignore = #{rust_str(reason)}]
    fn #{skip.rs_fun}() {}
    """
    |> String.trim_trailing("\n")
  end

  # Printed values already carry the module prefix. A call does not.
  defp side(prefix, {:call, fun, []}), do: "#{prefix}#{fun}()"
  defp side(prefix, {:call, fun, args}), do: "#{prefix}#{fun}(#{Enum.join(args, ", ")})"
  defp side(_prefix, {:value, source}), do: source

  defp one_line(text) do
    text |> to_string() |> String.replace(~r/[\r\n]/, " ")
  end

  defp print_term(term, book, gloss, prefix) do
    go(peel(term), book, gloss, prefix)
  end

  defp peel({:ann, term, _ty}), do: peel(term)
  defp peel({:rwt, _a, _b, term}), do: peel(term)
  defp peel(term), do: term

  defp go(:ze, _book, _gloss, prefix), do: nat_src(0, prefix)
  defp go({:nat, n}, _book, _gloss, prefix) when is_integer(n) and n >= 0, do: nat_src(n, prefix)

  defp go({:su, _} = term, _book, _gloss, prefix) do
    case Word.nat_closed(term) do
      {:ok, n} -> nat_src(n, prefix)
      :error -> {:error, :shape}
    end
  end

  defp go(:one, _book, _gloss, prefix), do: {:ok, prefix <> Name.gen("Unit")}

  defp go({:pair, a, b}, book, gloss, prefix) do
    if unboxed_value?(book, a) or unboxed_value?(book, b) do
      {:error, {:text, "normal form is unboxed data in a pair"}}
    else
      with {:ok, x} <- go(peel(a), book, gloss, prefix),
           {:ok, y} <- go(peel(b), book, gloss, prefix) do
        {:ok, "#{prefix}#{Name.gen("pair")}(#{x}, #{y})"}
      end
    end
  end

  defp go({:word, {:lit, k, n}, []}, _book, _gloss, _prefix)
       when k in [:u8, :u32, :u64, :i64] and is_integer(n) do
    {:ok, Rust.word_lit(k, n)}
  end

  defp go({:word, {:of, k}, [term]}, _book, _gloss, _prefix) when k in [:u8, :u32, :u64, :i64] do
    case Word.nat_closed(term) do
      {:ok, n} -> {:ok, Rust.word_lit(k, n)}
      :error -> {:error, {:text, "normal form is a word that is not a literal"}}
    end
  end

  defp go({:word, true, []}, _book, _gloss, _prefix), do: {:ok, "true"}
  defp go({:word, false, []}, _book, _gloss, _prefix), do: {:ok, "false"}
  defp go({:word, :none, []}, _book, _gloss, _prefix), do: {:ok, "::std::option::Option::None"}

  defp go({:word, :some, [payload]}, book, gloss, prefix) do
    if unboxed_value?(book, payload) do
      {:error, {:text, "normal form is an unboxed Opt"}}
    else
      case go(peel(payload), book, gloss, prefix) do
        {:ok, src} -> {:ok, "::std::option::Option::Some(#{src})"}
        {:error, _} = err -> err
      end
    end
  end

  defp go({:word, _, _}, _book, _gloss, _prefix),
    do: {:error, {:text, "normal form is a word that is not a literal"}}

  defp go({:slit, bin}, _book, _gloss, prefix) when is_binary(bin), do: text_literal(bin, prefix)
  defp go({:scat, _, _} = term, _book, _gloss, prefix), do: text_term(term, prefix)
  defp go({:sbytes, _} = term, _book, _gloss, prefix), do: text_term(term, prefix)
  defp go({:blit, bin}, _book, _gloss, prefix) when is_binary(bin), do: bytes_literal(bin, prefix)
  defp go({:bcat, _, _} = term, _book, _gloss, prefix), do: bytes_term(term, prefix)

  defp go({:atom, name}, _book, gloss, prefix) when is_binary(name) do
    case Map.fetch(gloss.atoms, name) do
      {:ok, variant} -> {:ok, "#{prefix}#{Name.gen("Atom")}::#{variant}"}
      :error -> {:error, {:text, "normal form is an atom the Rust image does not declare"}}
    end
  end

  defp go({:lam, _, _, _, _}, _book, _gloss, _prefix), do: {:error, :function}
  defp go({:pi, _, _, _, _}, _book, _gloss, _prefix), do: {:error, :function}
  defp go({:unf, _, _}, _book, _gloss, _prefix), do: {:error, :stream}
  defp go({:ucons, _}, _book, _gloss, _prefix), do: {:error, :stream}
  defp go({:nu, _}, _book, _gloss, _prefix), do: {:error, :stream}
  defp go({:nu, _, _}, _book, _gloss, _prefix), do: {:error, :stream}
  defp go({:bisim, _, _}, _book, _gloss, _prefix), do: {:error, :stream}
  defp go({:var, _}, _book, _gloss, _prefix), do: {:error, :open}
  defp go(:erased, _book, _gloss, _prefix), do: {:error, {:text, "normal form is erased"}}
  defp go({:erased, _}, _book, _gloss, _prefix), do: {:error, {:text, "normal form is erased"}}
  defp go({:toi64, _}, _book, _gloss, _prefix), do: {:error, :machine}
  defp go({:addi, _, _}, _book, _gloss, _prefix), do: {:error, :machine}
  defp go({:muli, _, _}, _book, _gloss, _prefix), do: {:error, :machine}
  defp go({:addt, _, _}, _book, _gloss, _prefix), do: {:error, :machine}
  defp go({:packi, _, _}, _book, _gloss, _prefix), do: {:error, :machine}
  defp go({:tensor, _, _}, _book, _gloss, _prefix), do: {:error, :machine}
  defp go(:i64, _book, _gloss, _prefix), do: {:error, :machine}
  defp go(:f32ty, _book, _gloss, _prefix), do: {:error, :machine}

  defp go({:def, name}, book, gloss, prefix) do
    print_ctor(name, [], book, gloss, prefix)
  end

  defp go({:con, _data, name, args}, book, gloss, prefix) do
    print_ctor(name, args, book, gloss, prefix)
  end

  defp go({:app, _, _} = term, book, gloss, prefix) do
    {head, args} = spine(term, [])

    case head do
      {:def, name} -> print_ctor(name, args, book, gloss, prefix)
      _other -> {:error, :shape}
    end
  end

  defp go(_other, _book, _gloss, _prefix), do: {:error, :shape}

  defp nat_src(n, _prefix) when n > @u64_max,
    do: {:error, {:text, "normal form is a Nat that does not fit in u64"}}

  defp nat_src(n, _prefix) when is_integer(n) and n > @nat_build_max,
    do: {:error, {:text, "normal form is a Nat above #{@nat_build_max}"}}

  defp nat_src(n, prefix) when is_integer(n) and n >= 0 do
    {:ok, "#{prefix}#{Name.gen("from_u64")}(#{n})"}
  end

  defp print_ctor(name, args, book, gloss, prefix) do
    case ctor_owner(book, name) do
      :error ->
        {:error, :open}

      {:ok, data} ->
        fn_name = Map.get(gloss.ctor_fns, {data, name})

        cond do
          fn_name == nil ->
            {:error, {:text, "normal form is a constructor the Rust image does not declare"}}

          not Rust.comparable?(book, {:data, data}) ->
            {:error, {:text, "normal form is not comparable in Rust"}}

          true ->
            case live_args(book, name, args) do
              {:ok, live} ->
                case print_many(live, book, gloss, prefix) do
                  {:ok, srcs} -> {:ok, "#{prefix}#{fn_name}(#{Enum.join(srcs, ", ")})"}
                  {:error, _} = err -> err
                end

              :partial ->
                {:error, :function}

              :error ->
                {:error, :shape}
            end
        end
    end
  end

  defp live_args(book, name, args) do
    case find_ctor(book, name) do
      nil ->
        :error

      ctor ->
        qtys = qty_spine(ctor.type)
        live = Enum.count(qtys, &(&1 != :erased))

        cond do
          length(args) > length(qtys) ->
            :error

          length(args) != length(qtys) ->
            :partial

          true ->
            kept =
              args
              |> Enum.zip(qtys)
              |> Enum.reject(fn {_arg, qty} -> qty == :erased end)
              |> Enum.map(&elem(&1, 0))

            if length(kept) == live, do: {:ok, kept}, else: :error
        end
    end
  end

  defp qty_spine({:pi, qty, _a, _x, b}), do: [qty | qty_spine(b)]
  defp qty_spine({:ann, t, _}), do: qty_spine(t)
  defp qty_spine(_), do: []

  defp print_many(args, book, gloss, prefix) do
    Enum.reduce_while(args, {:ok, []}, fn arg, {:ok, acc} ->
      case go(peel(arg), book, gloss, prefix) do
        {:ok, src} -> {:cont, {:ok, acc ++ [src]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp text_term(term, prefix) do
    case flatten_text(term) do
      {:ok, bin} -> text_literal(bin, prefix)
      :invalid -> {:error, {:text, "normal form is a string that is not valid UTF-8"}}
      :error -> {:error, {:text, "normal form is a string that is not a literal"}}
    end
  end

  defp text_literal(bin, prefix) do
    if String.valid?(bin) do
      {:ok, rust_buf(bin, Name.gen("str"), prefix)}
    else
      {:error, {:text, "normal form is a string that is not valid UTF-8"}}
    end
  end

  defp bytes_term(term, prefix) do
    case flatten_bytes(term) do
      {:ok, bin} -> bytes_literal(bin, prefix)
      :error -> {:error, {:text, "normal form is bytes that are not a literal"}}
    end
  end

  defp bytes_literal(bin, prefix), do: {:ok, rust_buf(bin, Name.gen("slice"), prefix)}

  defp rust_buf(bin, ty, prefix) do
    bytes = bin |> :binary.bin_to_list() |> Enum.map_join(", ", &Integer.to_string/1)

    "{ let muro__b: &'static [u8] = &[#{bytes}]; #{prefix}#{ty} { p: muro__b.as_ptr(), n: muro__b.len() } }"
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

  defp unboxed_value?(book, term) do
    {head, _args} = spine(peel(term), [])

    case head do
      {:def, name} ->
        case ctor_owner(book, name) do
          {:ok, data} -> Rust.unboxed?(book, data)
          :error -> false
        end

      _other ->
        false
    end
  end

  defp ctor_owner(book, name) do
    hits =
      for %{kind: :data, name: data, ctors: ctors} <- book,
          Enum.any?(ctors, &(&1.name == name)),
          do: data

    case hits do
      [data] -> {:ok, data}
      _other -> :error
    end
  end

  defp find_ctor(book, name) do
    Enum.find_value(book, fn
      %{kind: :data, ctors: ctors} -> Enum.find(ctors, &(&1.name == name))
      _other -> nil
    end)
  end

  defp spine({:app, fun, arg}, acc), do: spine(fun, [arg | acc])
  defp spine(head, acc), do: {head, acc}

  defp rust_str(text) when is_binary(text) do
    "\"" <> rust_str_body(text) <> "\""
  end

  defp rust_str_body(<<>>), do: ""

  defp rust_str_body(<<char::utf8, rest::binary>>) do
    rust_char(char) <> rust_str_body(rest)
  end

  defp rust_str_body(<<byte, rest::binary>>) do
    "\\u{#{Integer.to_string(byte, 16)}}" <> rust_str_body(rest)
  end

  defp rust_char(?"), do: "\\\""
  defp rust_char(?\\), do: "\\\\"
  defp rust_char(?\n), do: "\\n"
  defp rust_char(?\r), do: "\\r"
  defp rust_char(?\t), do: "\\t"
  defp rust_char(char) when char < 32 or char == 127, do: "\\u{#{Integer.to_string(char, 16)}}"
  defp rust_char(char), do: <<char::utf8>>
end

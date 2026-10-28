defmodule Muro.Emit.ExUnitSuite do
  @moduledoc """
  Emit a book's closed equations as one ExUnit module.

  A candidate is an `evidence` definition in this file whose type is an
  equation `{f a₁ … aₙ ≡ b : T}`, and `f` is a name. Quantified evidence,
  an equation whose head is not a name (`0`, `suc`, `head`, `fst`), and
  evidence from an imported book are not candidates. Each candidate is
  one test or one skipped line. A skip is never dropped.

  The tests call an implementation module. The default is the module
  `Muro.Emit.elixir_module/1` gives the book. A host selects another with
  `Application.put_env(:muro, TestModule, Adapter)`. The key is the test
  module. The behaviour module in the same file names the callbacks.
  Values are the shapes `Muro.Emit.emit_closed/2` prints. Host data
  arrives with repr (#131).
  """

  alias Muro.{Ast, Check, Emit, Gen, Prelude}

  @doc """
  `{:ok, %{source: source, skips: skips, tests: n}}` or
  `{:error, message}` when the book does not check.

  `book` is the checked book from `Muro.Load.file/2`, without the
  prelude. `opts` accepts `:fuel`, `:root`, `:book` (the display path),
  and `:impl` (the default implementation module).
  """
  def render(path, module, book, opts \\ []) when is_atom(module) and is_list(book) do
    fuel = Keyword.get(opts, :fuel, Check.default_fuel())
    display = display_book(path, opts)
    root = Keyword.get(opts, :root, File.cwd!())
    impl = Keyword.get(opts, :impl) || Emit.elixir_module(path)
    scope = Prelude.for_check(book)
    names = Emit.elixir_names(Prelude.for_emit(book))

    with {:ok, db_book} <- Ast.book_to_db(scope) do
      ctx = %{
        fuel: fuel,
        display: display,
        scope: scope,
        names: names,
        db: db_book,
        hash: Gen.book_hash(root, display)
      }

      {tests, skips} =
        book
        |> Enum.filter(&own_equation?(&1, Path.expand(path)))
        |> Enum.map(&classify(&1, ctx))
        |> partition()

      source = source(module, impl, ctx, tests, skips)
      {:ok, %{source: source, skips: skips, tests: length(tests)}}
    end
  end

  defp display_book(path, opts) do
    case Keyword.get(opts, :book) do
      book when is_binary(book) ->
        book

      _other ->
        root = Keyword.get(opts, :root, File.cwd!())
        rel = Gen.relative_path(root, path)
        if String.starts_with?(rel, "/"), do: Path.basename(path), else: rel
    end
  end

  defp own_equation?(d, book_file) do
    Map.get(d, :kind, :def) == :def and Map.get(d, :mode) == :evidence and
      Map.get(d, :file) == book_file and equation_name?(Map.get(d, :type))
  end

  defp equation_name?({:idt, _ty, lhs, _rhs}), do: name_head?(lhs)
  defp equation_name?(_other), do: false

  defp name_head?(lhs) do
    {head, _args} = named_spine(lhs, [])
    is_binary(head_name(head))
  end

  defp head_name({:var, name}), do: name
  defp head_name({:def, name}), do: name
  defp head_name(_other), do: nil

  defp named_spine({:app, f, a}, acc), do: named_spine(f, [a | acc])
  defp named_spine(head, acc), do: {head, acc}

  defp partition(items) do
    Enum.reduce(items, {[], []}, fn
      {:test, test}, {tests, skips} -> {tests ++ [test], skips}
      {:skip, skip}, {tests, skips} -> {tests, skips ++ [skip]}
    end)
  end

  defp classify(d, ctx) do
    {:idt, _ty, lhs, rhs} = d.type
    {head, args} = named_spine(lhs, [])
    name = head_name(head)
    located = %{name: d.name, file: ctx.display, line: line_of(d)}

    case decision(name, args, rhs, ctx) do
      {:test, test} -> {:test, Map.merge(located, test)}
      {:skip, reason} -> {:skip, Map.put(located, :reason, reason)}
    end
  end

  defp line_of(%{loc: {line, _col}}), do: line
  defp line_of(_other), do: 0

  # First problem wins. The order is the order in the manual.
  defp decision(name, args, rhs, ctx) do
    fun = find_def(ctx.scope, name)

    cond do
      fun == nil or Map.get(fun, :mode) != :run ->
        {:skip, "#{name} is not a run definition"}

      not is_binary(Map.get(fun, :file)) ->
        {:skip, "#{name} is a prelude run and is not defined by the book"}

      Map.get(fun, :export, true) == false ->
        {:skip, "#{name} is run internal and is not exported"}

      true ->
        qtys = Emit.binder_qtys(fun.type)
        decide_call(name, args, qtys, rhs, ctx)
    end
  end

  defp find_def(book, name) do
    Enum.find(book, fn d ->
      Map.get(d, :kind, :def) != :data and Map.get(d, :name) == name
    end)
  end

  defp decide_call(name, args, qtys, rhs, ctx) do
    cond do
      length(args) > length(qtys) ->
        {:skip, "#{name} is applied to more arguments than its type lists"}

      Enum.any?(Enum.take(qtys, length(args)), &(&1 == :erased)) ->
        {:skip, "argument passed at an erased binder of #{name}"}

      true ->
        case normalize_call(args, rhs, ctx) do
          {:skip, reason} ->
            {:skip, reason}

          {:ok, arg_src, expected} ->
            live = Enum.count(qtys, &(&1 != :erased))

            if length(args) == live do
              {:test,
               %{fun: Map.fetch!(ctx.names, name), arity: live, args: arg_src, expected: expected}}
            else
              {:skip,
               "#{name} is applied to #{length(args)} arguments and the emitted function has arity #{live}"}
            end
        end
    end
  end

  defp normalize_call(args, rhs, ctx) do
    with {:ok, arg_src} <- normalize_args(args, 1, ctx) do
      case normalize_one(rhs, "result", ctx) do
        {:ok, expected} -> {:ok, arg_src, expected}
        {:skip, reason} -> {:skip, reason}
      end
    end
  end

  defp normalize_args([], _index, _ctx), do: {:ok, []}

  defp normalize_args([arg | rest], index, ctx) do
    with {:ok, source} <- normalize_one(arg, "argument #{index}", ctx),
         {:ok, tail} <- normalize_args(rest, index + 1, ctx) do
      {:ok, [source | tail]}
    end
  end

  defp normalize_one(term, which, ctx) do
    case Ast.to_db(term) do
      {:ok, db} ->
        case Check.normalize(ctx.db, db, ctx.fuel) do
          {:ok, nf} ->
            case Emit.emit_closed(nf, ctx.scope) do
              {:ok, source} -> {:ok, source}
              {:error, reason} -> {:skip, shape_reason(which, reason)}
            end

          {:error, "out of fuel" <> _rest} ->
            {:skip, "#{which} did not normalize within fuel"}

          {:error, _message} ->
            {:skip, "#{which} did not normalize"}
        end

      {:error, _message} ->
        {:skip, "#{which} did not normalize"}
    end
  end

  defp shape_reason(which, :function), do: "#{which} normal form is a function"
  defp shape_reason(which, :stream), do: "#{which} normal form is a stream"
  defp shape_reason(which, :machine), do: "#{which} normal form is a machine term"

  defp shape_reason(which, :open),
    do: "#{which} is not closed (free variable or unresolved param)"

  defp shape_reason(which, :shape), do: "#{which} normal form has no literal"

  defp source(module, impl, ctx, tests, skips) do
    behaviour = Module.concat(module, Behaviour)
    callbacks = callbacks(tests)

    """
    defmodule #{inspect(behaviour)} do
      @moduledoc \"\"\"
      Callbacks for the closed equations in #{ctx.display}.

      The tests call these functions on the implementation module.
      An adapter declares `@behaviour #{inspect(behaviour)}`.
      \"\"\"
    #{callback_block(callbacks)}
    end

    defmodule #{inspect(module)} do
      @moduledoc \"\"\"
      Closed equations of #{ctx.display} as ExUnit tests.

      The implementation defaults to `#{inspect(impl)}`. Select another
      without editing this file. The key is this module:

          Application.put_env(:muro, #{inspect(module)}, YourAdapter)

      Comparisons use emitted shapes (`0`, `{:suc, n}`, `:tt`, constructor
      tuples, pairs). Host data arrives with repr (#131).
      \"\"\"

    #{skip_block(skips)}
      use ExUnit.Case, async: false

      @muro_book #{inspect(ctx.hash)}
      def muro_book, do: @muro_book

      @impl_mod #{inspect(impl)}
      #{callbacks_attr(callbacks)}

      setup_all do
        impl = Application.get_env(:muro, __MODULE__, @impl_mod)

        cond do
          not is_atom(impl) or impl == nil ->
            raise "implementation module must be a module name, got: \#{inspect(impl)}. " <>
                    "The default is \#{inspect(@impl_mod)}."

          true ->
            case Code.ensure_loaded(impl) do
              {:module, ^impl} ->
                :ok

              {:error, reason} ->
                raise "implementation module \#{inspect(impl)} is not loaded (\#{inspect(reason)}). " <>
                        "The default is \#{inspect(@impl_mod)}. " <>
                        "Select one with Application.put_env(:muro, #{inspect(module)}, YourAdapter) before the tests run."
            end
        end

        missing =
          for {name, arity} <- @callbacks, not function_exported?(impl, name, arity) do
            "\#{name}/\#{arity}"
          end

        if missing != [] do
          raise "implementation module \#{inspect(impl)} does not export \#{Enum.join(missing, ", ")}"
        end

        %{impl: impl}
      end
    #{test_block(tests)}
    end
    """
  end

  defp callbacks(tests) do
    tests
    |> Enum.uniq_by(& &1.fun)
    |> Enum.map(fn test -> {String.to_atom(test.fun), test.arity} end)
  end

  defp callback_block([]), do: ""

  defp callback_block(callbacks) do
    lines =
      Enum.map(callbacks, fn {name, arity} ->
        if arity == 0 do
          "  @callback #{name}() :: term()"
        else
          args = Enum.map_join(1..arity, ", ", fn _ -> "term()" end)
          "  @callback #{name}(#{args}) :: term()"
        end
      end)

    Enum.join(lines, "\n") <> "\n"
  end

  defp callbacks_attr([]), do: "@callbacks []"

  defp callbacks_attr(callbacks) do
    inner = Enum.map_join(callbacks, ", ", fn {name, arity} -> "#{name}: #{arity}" end)
    "@callbacks [#{inner}]"
  end

  defp skip_block([]), do: "  # Skipped: none"

  defp skip_block(skips) do
    lines =
      Enum.map(skips, fn skip ->
        "  #   #{skip.name} (#{skip.file}:#{skip.line}): #{skip.reason}"
      end)

    ["  # Skipped: #{length(skips)}" | lines]
    |> Enum.join("\n")
  end

  defp test_block([]), do: ""

  defp test_block(tests) do
    "\n" <> Enum.map_join(tests, "\n\n", &test_clause/1) <> "\n"
  end

  defp test_clause(test) do
    label = "#{test.name} (#{test.file}:#{test.line})"
    call = call(test.fun, test.args)

    """
      test #{inspect(label)}, %{impl: impl} do
        assert #{call} == #{test.expected}, #{inspect(label)}
      end\
    """
  end

  defp call(fun, []), do: "impl.#{fun}()"
  defp call(fun, args), do: "impl.#{fun}(#{Enum.join(args, ", ")})"
end

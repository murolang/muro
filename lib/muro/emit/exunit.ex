defmodule Muro.Emit.ExUnitSuite do
  @moduledoc """
  Emit a book's closed equations as one ExUnit module.

  A candidate is an `evidence` definition whose type is an equation
  `{f a₁ … aₙ ≡ b : T}`, and `f` is a name. Quantified evidence and an
  equation whose head is not a name (`0`, `suc`, `head`, `fst`) are not
  candidates. By default the candidates are the definitions in this
  file. `imports: true` also takes the files this book imports directly,
  in declaration order, once each. Each candidate is one test or one
  skipped line. A skip is never dropped.

  A `run` param at the head of a side is `impl.<name>(...)`. The
  arguments are closed values. A `run` param inside a value, or reached
  by evaluating a library `run` definition, is skipped. The adapter is
  not threaded through library code. An `evidence` param is not a
  callback.

  The tests call an implementation module. The default is the module
  `Muro.Emit.elixir_module/1` gives the book. A host selects another with
  `Application.put_env(:muro, TestModule, Adapter)`. The key is the test
  module. The behaviour module in the same file names the callbacks.
  Values are the shapes `Muro.Emit.emit_closed/2` prints. Host data
  arrives with repr (#131).
  """

  alias Muro.Emit
  alias Muro.Emit.Equations

  @doc """
  `{:ok, %{source: source, skips: skips, tests: n}}` or
  `{:error, message}` when the book does not check.

  `book` is the checked book from `Muro.Load.file/2`, without the
  prelude. `opts` accepts `:fuel`, `:root`, `:book` (the display path
  of this file), `:impl` (the default implementation module), and
  `:imports` (also collect direct imports; default `false`).

  `Ast.book_to_db/2` is called with `params: :open`. A param in this
  book is an assumption. Callers other than the exunit path do not
  render a book that still has params.
  """
  def render(path, module, book, opts \\ []) when is_atom(module) and is_list(book) do
    impl = Keyword.get(opts, :impl) || Emit.elixir_module(path)

    with {:ok, %{tests: tests, skips: skips, ctx: ctx}} <- Equations.collect(path, book, opts) do
      source = source(module, impl, ctx, tests, skips)
      {:ok, %{source: source, skips: skips, tests: length(tests)}}
    end
  end

  @doc false
  def display_book(path, opts), do: Equations.display_book(path, opts)

  @doc false
  def display_for(d, ctx), do: Equations.display_for(d, ctx)

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

      Comparisons use emitted shapes (a non-negative integer for a Nat,
      `:tt`, constructor tuples, pairs). Host data arrives with repr (#131).
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
    Enum.map(Equations.calls(tests), fn {fun, args} ->
      {String.to_atom(fun), length(args)}
    end)
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

  defp callbacks_attr([]) do
    """
    @callbacks []
    """
    |> String.trim()
  end

  defp callbacks_attr(callbacks) do
    inner = Enum.map_join(callbacks, ", ", fn {name, arity} -> "#{name}: #{arity}" end)

    """
    @callbacks [#{inner}]
    """
    |> String.trim()
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
    {name, message} = label(test)

    """
      test #{inspect(name)}, %{impl: impl} do
        assert #{side_src(test.lhs)} == #{side_src(test.rhs)}, #{inspect(message)}
      end\
    """
  end

  # The test name and the assertion message. `origin` is the file today.
  # A later qualifier for the package an equation comes from is added here.
  defp label(test), do: Equations.label(test)

  defp side_src({:call, fun, []}), do: "impl.#{fun}()"
  defp side_src({:call, fun, args}), do: "impl.#{fun}(#{Enum.join(args, ", ")})"
  defp side_src({:value, source}), do: source
end

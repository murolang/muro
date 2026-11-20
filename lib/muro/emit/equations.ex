defmodule Muro.Emit.Equations do
  @moduledoc """
  Closed equations collected for a host test suite.

  ExUnit, pytest, and the Rust test file share this collector.

  A candidate is an `evidence` definition whose type is an equation
  `{f a₁ … aₙ ≡ b : T}`, and `f` is a name. Quantified evidence and an
  equation whose head is not a name are not candidates. By default the
  candidates are the definitions in this file. `imports: true` also
  takes the files this book imports directly, in declaration order,
  once each. Each candidate is one test or one skip. A skip is never
  dropped.

  The structural skips (erased arguments, arity, a run that is not
  exported, a param reached only by evaluation, fuel) are decided
  here. The value of an argument or a result is printed by `opts[:print]`,
  which defaults to `Muro.Emit.emit_closed/2`. A backend that wants
  another literal passes its own printer. That printer is the place a
  later `repr` plugs in. It returns `{:ok, source}` or
  `{:error, reason}`, and `reason` is `:function`, `:stream`,
  `:machine`, `:open`, `:shape`, or `{:text, message}`.
  """

  alias Muro.{Ast, Check, Emit, Gen, Prelude}

  @doc """
  `{:ok, %{tests: tests, skips: skips, items: items, ctx: ctx}}` or
  `{:error, message}` when the book does not check.

  `book` is the checked book from `Muro.Load.file/2`, without the
  prelude. `opts` accepts `:fuel`, `:root`, `:book` (the display path
  of this file), `:imports`, `:print` (the value printer), and
  `:names` (a function of the emit book that returns the host name
  map). The default names are `Muro.Emit.elixir_names/1`.

  `items` is every candidate in book order, each `{:test, test}` or
  `{:skip, skip}`. `tests` and `skips` are those two lists. Their
  lengths sum to the number of candidates.

  `Ast.book_to_db/2` is called with `params: :open`. A param in this
  book is an assumption.
  """
  def collect(path, book, opts \\ []) when is_binary(path) and is_list(book) and is_list(opts) do
    fuel = Keyword.get(opts, :fuel, Check.default_fuel())
    display = display_book(path, opts)
    root = Keyword.get(opts, :root, File.cwd!())
    scope = Prelude.for_check(book)
    emit_book = Prelude.for_emit(book)

    names =
      case Keyword.get(opts, :names) do
        fun when is_function(fun, 1) -> fun.(emit_book)
        _other -> Emit.elixir_names(emit_book)
      end

    print = Keyword.get(opts, :print, &Emit.emit_closed/2)

    with :ok <- Emit.refuse_may_fail(book),
         {:ok, files} <- candidate_files(path, opts),
         {:ok, db_book} <- Ast.book_to_db(scope, params: :open) do
      ctx = %{
        fuel: fuel,
        path: Path.expand(path),
        display: display,
        root: root,
        scope: scope,
        names: names,
        db: db_book,
        hash: Gen.book_hash(root, display),
        print: print
      }

      items =
        files
        |> Enum.flat_map(fn file ->
          Enum.filter(book, &own_equation?(&1, file))
        end)
        |> Enum.map(&classify(&1, ctx))

      {tests, skips} = partition(items)
      {:ok, %{tests: tests, skips: skips, items: items, ctx: ctx}}
    end
  end

  @doc """
  Calls a suite actually makes, in the order the tests first mention
  them. Each entry is `{host_name, arg_sources}`. A later call of the
  same host name is dropped.
  """
  def calls(tests) when is_list(tests) do
    tests
    |> Enum.flat_map(&test_calls/1)
    |> Enum.uniq_by(&elem(&1, 0))
  end

  @doc """
  The test name and the assertion message. The name is
  `"<file> <def-name>"`. The message is `"<file>:<line> <def-name>"`.
  """
  def label(%{name: name, line: line, origin: %{file: file}}) do
    {"#{file} #{name}", "#{file}:#{line} #{name}"}
  end

  defp candidate_files(path, opts) do
    own = Path.expand(path)

    if Keyword.get(opts, :imports, false) do
      case Muro.Load.direct_imports(path, root: Keyword.get(opts, :root)) do
        {:ok, extra} ->
          {:ok, [own | Enum.reject(extra, &same_file?(&1, own))]}

        {:error, _} = err ->
          err
      end
    else
      {:ok, [own]}
    end
  end

  @doc false
  def display_book(path, opts) do
    case Keyword.get(opts, :book) do
      book when is_binary(book) ->
        book

      _other ->
        root = Keyword.get(opts, :root, File.cwd!())
        rel = Gen.relative_path(root, path)
        if String.starts_with?(rel, "/"), do: Path.basename(path), else: rel
    end
  end

  @doc false
  def closed_equations(book, book_file) when is_list(book) and is_binary(book_file) do
    Enum.filter(book, &own_equation?(&1, book_file))
  end

  @doc false
  def equation_head(%{type: {:idt, _ty, lhs, _rhs}}) do
    {head, _args} = named_spine(lhs, [])
    head_name(head)
  end

  def equation_head(_other), do: nil

  defp own_equation?(d, book_file) do
    Map.get(d, :kind, :def) == :def and Map.get(d, :mode) == :evidence and
      is_binary(Map.get(d, :file)) and same_file?(d.file, book_file) and
      equation_name?(Map.get(d, :type))
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
    file = display_for(d, ctx)
    located = %{name: d.name, file: file, line: line_of(d), origin: %{file: file}}

    case decision(lhs, rhs, ctx) do
      {:test, test} -> {:test, Map.merge(located, test)}
      {:skip, reason} -> {:skip, Map.put(located, :reason, reason)}
    end
  end

  # The loader canonicalizes a package root (`/var` is `/private/var` on
  # macOS). Compare and display both sides the same way, so a test name
  # stays `muro_deps/name/file.muro` and never an absolute path.
  @doc false
  def display_for(d, ctx) do
    cond do
      Muro.Std.std_id?(d.file) ->
        d.file

      same_file?(d.file, ctx.path) ->
        ctx.display

      true ->
        rel = Gen.relative_path(canon(ctx.root), canon(d.file))

        if String.starts_with?(rel, "..") or String.starts_with?(rel, "/") do
          Path.basename(d.file)
        else
          rel
        end
    end
  end

  # A library id is compared as written. Expanding it would invent a
  # file named `std:le.muro` in the working directory.
  defp same_file?(a, b) do
    if Muro.Std.std_id?(a) or Muro.Std.std_id?(b), do: a == b, else: canon(a) == canon(b)
  end

  defp canon(path), do: Muro.Manifest.canonical(path)

  defp line_of(%{loc: {line, _col}}), do: line
  defp line_of(_other), do: 0

  # First problem wins. The order is the order in the manual.
  # A run param at the head of the left-hand side is an implementation
  # call. Anything else keeps the 0.16.76 decision, after a param reached
  # by evaluation has been refused.
  defp decision(lhs, rhs, ctx) do
    {head, args} = named_spine(lhs, [])
    name = head_name(head)

    cond do
      param = run_param(ctx.scope, name) ->
        decide_param(param, args, rhs, ctx)

      true ->
        case surface_inside(args, ctx) do
          {:skip, _} = skip ->
            skip

          :ok ->
            case through_param(lhs, name, ctx) do
              {:skip, _} = skip -> skip
              :ok -> decide_def(name, args, rhs, ctx)
            end
        end
    end
  end

  defp decide_def(name, args, rhs, ctx) do
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

  # A param call is the left-hand side. The right-hand side is decided
  # afterwards, so a param on the right does not re-enter this clause.
  # The right-hand side is normalized before the arity check, which is
  # the 0.16.76 order: `{round ≡ round}` skips as a function result,
  # not as an arity mismatch.
  defp decide_param(param, args, rhs, ctx) do
    case param_ready(param, args, ctx) do
      {:ok, arg_src, qtys} ->
        with {:ok, right} <- rhs_side(rhs, ctx),
             {:ok, call} <- call_or_arity(param.name, args, qtys, arg_src, ctx) do
          {:test, %{lhs: call, rhs: right}}
        end

      {:skip, _} = skip ->
        skip
    end
  end

  defp param_call(param, args, ctx) do
    case param_ready(param, args, ctx) do
      {:ok, arg_src, qtys} -> call_or_arity(param.name, args, qtys, arg_src, ctx)
      {:skip, _} = skip -> skip
    end
  end

  defp param_ready(param, args, ctx) do
    qtys = Emit.binder_qtys(param.type)

    cond do
      shape = param_shape(param, ctx) ->
        {:skip, shape}

      length(args) > length(qtys) ->
        {:skip, "#{param.name} is applied to more arguments than its type lists"}

      Enum.any?(Enum.take(qtys, length(args)), &(&1 == :erased)) ->
        {:skip, "argument passed at an erased binder of #{param.name}"}

      true ->
        case surface_inside(args, ctx) do
          {:skip, _} = skip ->
            skip

          :ok ->
            case normalize_args(args, 1, ctx) do
              {:ok, arg_src} -> {:ok, arg_src, qtys}
              {:skip, _} = skip -> skip
            end
        end
    end
  end

  defp call_or_arity(name, args, qtys, arg_src, ctx) do
    live = Enum.count(qtys, &(&1 != :erased))

    if length(args) == live do
      {:ok, {:call, Map.fetch!(ctx.names, name), arg_src}}
    else
      {:skip,
       "#{name} is applied to #{length(args)} arguments and the emitted function has arity #{live}"}
    end
  end

  defp find_def(book, name) do
    Enum.find(book, fn d ->
      Map.get(d, :kind, :def) not in [:data, :prefix] and Map.get(d, :name) == name
    end)
  end

  defp decide_call(name, args, qtys, rhs, ctx) do
    cond do
      length(args) > length(qtys) ->
        {:skip, "#{name} is applied to more arguments than its type lists"}

      Enum.any?(Enum.take(qtys, length(args)), &(&1 == :erased)) ->
        {:skip, "argument passed at an erased binder of #{name}"}

      true ->
        with {:ok, arg_src} <- normalize_args(args, 1, ctx),
             {:ok, right} <- rhs_side(rhs, ctx),
             {:ok, call} <- call_or_arity(name, args, qtys, arg_src, ctx) do
          {:test, %{lhs: call, rhs: right}}
        end
    end
  end

  defp rhs_side(rhs, ctx) do
    {head, args} = named_spine(rhs, [])
    name = head_name(head)

    cond do
      param = run_param(ctx.scope, name) ->
        param_call(param, args, ctx)

      true ->
        case find_param_named(rhs, ctx) do
          pname when is_binary(pname) ->
            {:skip, "calls param #{pname} inside a value"}

          _ ->
            if is_binary(name) and run_def?(ctx.scope, name) do
              case through_param(rhs, name, ctx) do
                {:skip, _} = skip -> skip
                :ok -> value_side(rhs, ctx)
              end
            else
              value_side(rhs, ctx)
            end
        end
    end
  end

  defp value_side(term, ctx) do
    case normalize_one(term, "result", ctx) do
      {:ok, source} -> {:ok, {:value, source}}
      {:skip, _} = skip -> skip
    end
  end

  # A `run` param. An `evidence` param is not a callback and is not a call.
  defp run_param(_scope, name) when not is_binary(name), do: nil

  defp run_param(scope, name) do
    Enum.find(scope, fn d ->
      Map.get(d, :kind) == :param and Map.get(d, :name) == name and Map.get(d, :mode) == :run
    end)
  end

  defp run_def?(scope, name) do
    case find_def(scope, name) do
      %{mode: :run} = d -> Map.get(d, :kind, :def) != :param
      _ -> false
    end
  end

  # First-order data, or a skip cause. A function, a stream, or a session
  # in an argument or in the result is named. Anything else the emitter
  # cannot render as a literal argument is `arguments are not data`.
  # A result that is not data, and is not one of those three, is named too.
  defp param_shape(param, ctx) do
    case telescope_fault(param.type, ctx) do
      nil -> nil
      cause -> "param #{param.name} #{cause}"
    end
  end

  defp telescope_fault({:pi, _q, dom, _x, cod}, ctx) do
    case class_cause(type_class(dom, ctx), :arg) do
      nil -> telescope_fault(cod, ctx)
      cause -> cause
    end
  end

  defp telescope_fault({:ann, t, _ty}, ctx), do: telescope_fault(t, ctx)

  defp telescope_fault(result, ctx), do: class_cause(type_class(result, ctx), :res)

  defp class_cause(:data, _side), do: nil
  defp class_cause(:function, :arg), do: "takes a function"
  defp class_cause(:function, :res), do: "returns a function"
  defp class_cause(:stream, :arg), do: "takes a stream"
  defp class_cause(:stream, :res), do: "returns a stream"
  defp class_cause(:session, :arg), do: "takes a session"
  defp class_cause(:session, :res), do: "returns a session"
  defp class_cause(_other, :arg), do: "arguments are not data"
  defp class_cause(_other, :res), do: "returns a value that is not data"

  defp type_class({:ann, t, _ty}, ctx), do: type_class(t, ctx)
  defp type_class({:pi, _, _, _, _}, _ctx), do: :function
  defp type_class({:lam, _, _, _, _}, _ctx), do: :function
  defp type_class({:stream, _a}, _ctx), do: :stream
  defp type_class({:nu, _, _}, _ctx), do: :stream
  defp type_class({:nu, _}, _ctx), do: :stream
  defp type_class({:sess, _, _}, _ctx), do: :session
  defp type_class(:nat, _ctx), do: :data
  defp type_class(:unit, _ctx), do: :data
  defp type_class(:atom, _ctx), do: :data
  defp type_class(:string, _ctx), do: :data
  defp type_class(:bytes, _ctx), do: :data
  defp type_class(:slice, _ctx), do: :data
  defp type_class(:empty, _ctx), do: :data

  defp type_class({:prod, a, b}, ctx) do
    join_class(type_class(a, ctx), type_class(b, ctx))
  end

  defp type_class({:var, name}, ctx), do: name_class(ctx.scope, name)

  defp type_class({:app, _, _} = term, ctx) do
    {head, args} = named_spine(term, [])

    case head do
      {:var, name} ->
        if data_name?(ctx.scope, name) do
          Enum.reduce(args, :data, fn arg, acc ->
            join_class(acc, arg_class(type_class(arg, ctx)))
          end)
        else
          name_class(ctx.scope, name)
        end

      _ ->
        :other
    end
  end

  defp type_class(:ze, _ctx), do: :index
  defp type_class({:su, _}, _ctx), do: :index
  defp type_class(:one, _ctx), do: :index
  defp type_class({:atom, _}, _ctx), do: :index
  defp type_class({:slit, _}, _ctx), do: :index
  defp type_class({:blit, _}, _ctx), do: :index
  defp type_class(_other, _ctx), do: :other

  # An index of a data type (a nat, a variable) does not make the value
  # something other than data. A function, stream, or session parameter does.
  defp arg_class(:index), do: :data
  defp arg_class(other), do: other

  # A name with no declaration is a binder (an index of a data type).
  # A declared name that is not data and not a session is not a literal.
  defp name_class(scope, name) do
    case Enum.find(scope, &(Map.get(&1, :name) == name)) do
      %{kind: :data} -> :data
      %{kind: :session} -> :session
      nil -> :index
      _declared -> :other
    end
  end

  defp data_name?(scope, name) do
    Enum.any?(scope, &(Map.get(&1, :kind) == :data and Map.get(&1, :name) == name))
  end

  defp join_class(a, b) do
    Enum.max_by([a, b], fn
      :function -> 5
      :stream -> 4
      :session -> 3
      :other -> 2
      :index -> 1
      :data -> 0
    end)
  end

  defp surface_inside(args, ctx) do
    case Enum.find_value(args, &find_param_named(&1, ctx)) do
      nil -> :ok
      pname -> {:skip, "calls param #{pname} inside a value"}
    end
  end

  defp find_param_named(term, ctx), do: find_named(term, MapSet.new(), ctx)

  defp find_named({:var, name}, bound, ctx) do
    if MapSet.member?(bound, name) or not run_param?(ctx, name), do: nil, else: name
  end

  defp find_named({:def, name}, bound, ctx) do
    if MapSet.member?(bound, name) or not run_param?(ctx, name), do: nil, else: name
  end

  defp find_named({:lam, _q, dom, x, body}, bound, ctx) do
    find_named(dom, bound, ctx) || find_named(body, MapSet.put(bound, x), ctx)
  end

  defp find_named({:pi, _q, dom, x, body}, bound, ctx) do
    find_named(dom, bound, ctx) || find_named(body, MapSet.put(bound, x), ctx)
  end

  defp find_named({:app, f, a}, bound, ctx) do
    find_named(f, bound, ctx) || find_named(a, bound, ctx)
  end

  defp find_named(term, bound, ctx) when is_tuple(term) do
    term |> Tuple.to_list() |> Enum.find_value(&find_named(&1, bound, ctx))
  end

  defp find_named(term, bound, ctx) when is_list(term) do
    Enum.find_value(term, &find_named(&1, bound, ctx))
  end

  defp find_named(_other, _bound, _ctx), do: nil

  defp run_param?(ctx, name), do: run_param(ctx.scope, name) != nil

  # The surface did not mention a param. Unfolding `through` did.
  # A normalize failure is not this reason: the later value skip reports it.
  # The normal form can name a param only when a run param is in scope.
  # With none, the normalize cannot change this answer, and it is :ok.
  defp through_param(term, through, ctx) do
    if run_param_in_scope?(ctx) do
      through_param_unfold(term, through, ctx)
    else
      :ok
    end
  end

  defp run_param_in_scope?(ctx) do
    Enum.any?(ctx.scope, fn d ->
      Map.get(d, :kind) == :param and Map.get(d, :mode) == :run
    end)
  end

  defp through_param_unfold(term, through, ctx) do
    case Ast.to_db(term) do
      {:ok, db} ->
        case Check.normalize(ctx.db, db, ctx.fuel) do
          {:ok, nf} ->
            case find_param_db(nf, ctx) do
              nil -> :ok
              pname -> {:skip, "calls param #{pname} through #{through}"}
            end

          {:error, _} ->
            :ok
        end

      {:error, _} ->
        :ok
    end
  end

  defp find_param_db({:def, name}, ctx) do
    if run_param?(ctx, name), do: name, else: nil
  end

  defp find_param_db({:app, f, a}, ctx) do
    find_param_db(f, ctx) || find_param_db(a, ctx)
  end

  defp find_param_db(term, ctx) when is_tuple(term) do
    term |> Tuple.to_list() |> Enum.find_value(&find_param_db(&1, ctx))
  end

  defp find_param_db(term, ctx) when is_list(term) do
    Enum.find_value(term, &find_param_db(&1, ctx))
  end

  defp find_param_db(_other, _ctx), do: nil

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
            case find_param_db(nf, ctx) do
              pname when is_binary(pname) ->
                {:skip, "calls param #{pname} inside a value"}

              _ ->
                case ctx.print.(nf, ctx.scope) do
                  {:ok, source} -> {:ok, source}
                  {:error, reason} -> {:skip, shape_reason(which, reason)}
                end
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
  defp shape_reason(which, {:text, msg}) when is_binary(msg), do: "#{which} #{msg}"

  defp test_calls(%{lhs: lhs, rhs: rhs}) do
    calls_of(lhs) ++ calls_of(rhs)
  end

  defp calls_of({:call, fun, args}), do: [{fun, args}]
  defp calls_of(_other), do: []
end

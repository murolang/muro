defmodule Muro.IR.Rep do
  @moduledoc """
  The machine representation of each data type of a book.

  A data type is resolved once, from its declaration, to one of

    * `{:enum, ctors}` — every constructor has no live field. The value
      is the tag. An all-nullary `unboxed data` type is this enum too.
    * `{:value, [{ctor, fields}]}` — `unboxed data` with a live field:
      a struct passed by value, tag plus fields.
    * `{:boxed, [{ctor, fields}]}` — a heap object, tag plus fields.

  A field is `{name, layout, :live | :erased}`, in telescope order.
  `layout` is the `Muro.IR` layout of the field type (`type_layout/2`).
  An erased field keeps its place and its layout so a reader sees the
  whole telescope; only a `:live` field is stored.

  The C emitter reads its struct, enum, by-value, and pointer choices
  from here. `Muro.Emit.C` does not classify a data type itself.

  ## `c:unboxed`

  A by-value struct cannot sit in a `void *` word, and its option
  struct is printed before the struct is complete. The rules are here:

    * `value_lay?/2` — a pair half, a stream seed, or a stream capture
      of this layout is `c:unboxed` (C, Rust, and Zig check it where they
      emit the pair or the stream).
    * `refuse_unboxed_opt/2` — any `Opt` of declared `unboxed data`,
      enum or not, in a run's layouts, body, or a data field, is
      `c:unboxed` (C, Rust, and Zig; `Muro.Emit.refuse_unboxed_opt/2`
      is this function).
    * `value_opt_payload?/2` — the C option typedef of a by-value struct.
    * `check/2` — all three over a whole image, without emitting.

  A field is erased when its quantity is exactly `:erased`, the
  quantity `Muro.Grade.erase_book/1` leaves on a book every emitter
  reads.
  """

  alias Muro.IR
  alias Muro.IR.Check

  @type layout :: term()
  @type field :: {String.t() | nil, layout(), :live | :erased}
  @type rep ::
          {:enum, [String.t()]}
          | {:value, [{String.t(), [field()]}]}
          | {:boxed, [{String.t(), [field()]}]}

  @doc "Every data type of `book`, by name, to its representation."
  @spec of_book(list()) :: %{String.t() => rep()}
  def of_book(book) when is_list(book) do
    book
    |> data_defs()
    |> Map.new(fn d -> {d.name, of_data(book, d)} end)
  end

  @doc "The representation of the data declaration `d` of `book`."
  @spec of_data(list(), map()) :: rep()
  def of_data(book, d) when is_list(book) and is_map(d) do
    cond do
      enum_data?(d) ->
        {:enum, Enum.map(d.ctors, & &1.name)}

      unboxed_data?(d) ->
        {:value, Enum.map(d.ctors, &{&1.name, fields(book, &1)})}

      true ->
        {:boxed, Enum.map(Map.get(d, :ctors, []), &{&1.name, fields(book, &1)})}
    end
  end

  @doc "The representation of the data type `name`, or `nil`."
  @spec data_rep(list(), term()) :: rep() | nil
  def data_rep(book, name) do
    case find_data(book, name) do
      nil -> nil
      d -> of_data(book, d)
    end
  end

  @doc "`:enum`, `:value`, or `:boxed`."
  def kind({k, _}) when k in [:enum, :value, :boxed], do: k

  @doc "The fields of a constructor, erased ones included, in order."
  @spec fields(list(), map()) :: [field()]
  def fields(book, ctor) do
    ctor.type
    |> telescope()
    |> Enum.map(fn {q, a, x} ->
      {x, type_layout(book, a), if(q == :erased, do: :erased, else: :live)}
    end)
  end

  @doc "The layouts of the live fields of a constructor, in order."
  def live_layouts(book, ctor) do
    for {_x, lay, :live} <- fields(book, ctor), do: lay
  end

  # -- classification -----------------------------------------------------

  @doc """
  True when every constructor of `d` has no live field. A type with a
  fieldful constructor is not, including when some of its constructors
  are fieldless. Only the constructor telescope is read, so the test
  cannot loop through a field of another data type.
  """
  def enum_data?(d) when is_map(d) do
    ctors = Map.get(d, :ctors, [])
    is_list(ctors) and ctors != [] and Enum.all?(ctors, &nullary_ctor?/1)
  end

  @doc "True when `d` is declared `unboxed data`."
  def unboxed_data?(%{unboxed: true}), do: true
  def unboxed_data?(_), do: false

  @doc "True when the data type `name` of `book` is `{:enum, _}`."
  def enum?(book, name) when is_list(book) and is_binary(name) do
    case find_data(book, name) do
      nil -> false
      d -> enum_data?(d)
    end
  end

  def enum?(_book, _name), do: false

  @doc "True when `lay` is `{:data, name}` of an enum type."
  def enum_lay?(book, {:data, name}), do: enum?(book, name)
  def enum_lay?(_book, _lay), do: false

  @doc "True when the data type `name` is declared `unboxed data` (enum or not)."
  def unboxed?(book, name) when is_binary(name) do
    case find_data(book, name) do
      %{unboxed: true} -> true
      _ -> false
    end
  end

  def unboxed?(_book, _name), do: false

  @doc "True when `name` is `{:value, _}`: declared unboxed and not an enum."
  def value?(book, name), do: unboxed?(book, name) and not enum?(book, name)

  @doc """
  True when `lay` is a by-value struct. Such a value cannot live in a
  pair, a stream seed, or a stream capture (`c:unboxed`).
  """
  def value_lay?(book, {:data, name}), do: value?(book, name)
  def value_lay?(_book, _lay), do: false

  @doc """
  True when the C option struct of `lay` (an `{:opt, _}`) would hold a
  by-value struct. Option structs are printed before data structs.
  """
  def value_opt_payload?(book, {:opt, {:data, name}}) when is_binary(name),
    do: value?(book, name)

  def value_opt_payload?(book, {:opt, {:opt, _} = inner}), do: value_opt_payload?(book, inner)
  def value_opt_payload?(_book, _lay), do: false

  @doc """
  The by-value data types a by-value field of `d` embeds, so their
  struct bodies come first. `d` itself is not one.
  """
  def value_deps(book, d) do
    d.ctors
    |> Enum.flat_map(fn ctor ->
      Enum.flat_map(fields(book, ctor), fn
        {_x, _lay, :erased} ->
          []

        {_x, {:data, name}, :live} ->
          if name != d.name and value?(book, name), do: [name], else: []

        _ ->
          []
      end)
    end)
    |> Enum.uniq()
  end

  # -- layouts ------------------------------------------------------------

  @doc """
  The `Muro.IR` layout of a field or parameter type, as the C emitter
  stores it. A name that is not a data type is `:opaque`.
  """
  def type_layout(_book, :bytes), do: :slice
  def type_layout(_book, :slice), do: :slice
  def type_layout(_book, :string), do: :string
  def type_layout(_book, :nat), do: :nat
  def type_layout(_book, :unit), do: :unit
  def type_layout(_book, :atom), do: {:data, "Atom"}
  def type_layout(book, {:stream, a}), do: {:stream, type_layout(book, a)}

  def type_layout(book, {:var, name}) do
    if data?(book, name), do: {:data, name}, else: :opaque
  end

  def type_layout(book, {:def, name}), do: type_layout(book, {:var, name})
  def type_layout(book, {:app, f, _}), do: type_layout(book, f)

  def type_layout(book, {:prod, a, b}) do
    {:pair, type_layout(book, a), type_layout(book, b)}
  end

  def type_layout(book, {:ann, e, _}), do: type_layout(book, e)
  def type_layout(_book, :i64), do: :i64
  def type_layout(_book, {:word, {:ty, :u8}, []}), do: :u8
  def type_layout(_book, {:word, {:ty, :u32}, []}), do: :u32
  def type_layout(_book, {:word, {:ty, :u64}, []}), do: :u64
  def type_layout(_book, {:word, :bool, []}), do: :wbool
  def type_layout(_book, {:word, {:optk, :u8}, []}), do: {:opt, :u8}
  def type_layout(_book, {:word, {:optk, :u32}, []}), do: {:opt, :u32}
  def type_layout(_book, {:word, {:optk, :u64}, []}), do: {:opt, :u64}
  def type_layout(_book, {:word, {:optk, :i64}, []}), do: {:opt, :i64}
  def type_layout(book, {:word, :opt, [a]}), do: {:opt, type_layout(book, a)}
  def type_layout(_book, _), do: :opaque

  # -- c:unboxed ------------------------------------------------------------

  @doc """
  `{:error, "c:unboxed"}` when a run or a data field carries `Opt` of
  unboxed data. The option struct is emitted before the data structs,
  so C, Rust, and Zig refuse it. Elixir and JavaScript do not call this.
  """
  def refuse_unboxed_opt(book, funs) when is_list(book) and is_list(funs) do
    if unboxed_opt_image?(book, funs), do: {:error, "c:unboxed"}, else: :ok
  end

  @doc """
  Every `c:unboxed` rule over the image `funs` of `book`, without
  emitting: an unboxed `Opt` (`refuse_unboxed_opt/2`), a by-value
  struct as a pair half, and a by-value struct as a stream seed or a
  stream capture. `:ok` or `{:error, "c:unboxed"}`. Layouts are the
  ones `Muro.IR.Check` infers.
  """
  def check(funs, book) when is_list(funs) and is_list(book) do
    funs = Enum.map(funs, &IR.normalize_fun/1)
    ctx = Check.layout_ctx(funs, book: book)

    with :ok <- refuse_unboxed_opt(book, funs) do
      if Enum.any?(funs, &fun_bad?(&1, book, ctx)), do: {:error, "c:unboxed"}, else: :ok
    end
  end

  defp fun_bad?(fun, book, ctx) do
    env =
      Map.new(fun.params, fn p ->
        {IR.param_name(p), %{grade: IR.param_grade(p), lay: IR.param_lay(p)}}
      end)

    bad?(fun.body, env, book, ctx)
  end

  defp bad?({:pair, a, b} = t, env, book, ctx) do
    value_lay?(book, Check.infer_layout(a, env, ctx)) or
      value_lay?(book, Check.infer_layout(b, env, ctx)) or
      children_bad?(t, env, book, ctx)
  end

  defp bad?({:stream, seed, caps, step} = t, env, book, ctx) do
    cap_lays =
      case Map.fetch(ctx.by_name, step) do
        {:ok, f} -> f.params |> Enum.take(length(caps)) |> Enum.map(&IR.param_lay/1)
        :error -> []
      end

    Enum.any?([Check.infer_layout(seed, env, ctx) | cap_lays], &value_lay?(book, &1)) or
      children_bad?(t, env, book, ctx)
  end

  defp bad?({:let, x, lay, g, v, b}, env, book, ctx) do
    bad?(v, env, book, ctx) or bad?(b, Map.put(env, x, %{grade: g, lay: lay}), book, ctx)
  end

  defp bad?({:letp, a, b, e, body}, env, book, ctx) do
    {la, lb} =
      case Check.infer_layout(e, env, ctx) do
        {:pair, x, y} -> {x, y}
        _ -> {:unknown, :unknown}
      end

    env1 = env |> Map.put(a, %{grade: :affine, lay: la}) |> Map.put(b, %{grade: :affine, lay: lb})
    bad?(e, env, book, ctx) or bad?(body, env1, book, ctx)
  end

  defp bad?({:lam, x, lay, g, body}, env, book, ctx) when is_binary(x),
    do: bad?(body, Map.put(env, x, %{grade: g, lay: lay}), book, ctx)

  defp bad?({:match, s, arms}, env, book, ctx) when is_list(arms),
    do: match_bad?(s, Check.infer_layout(s, env, ctx), arms, env, book, ctx)

  defp bad?({:match, s, lay, arms}, env, book, ctx) when is_list(arms),
    do: match_bad?(s, lay, arms, env, book, ctx)

  defp bad?(t, env, book, ctx) when is_tuple(t), do: children_bad?(t, env, book, ctx)
  defp bad?(_t, _env, _book, _ctx), do: false

  defp match_bad?(s, slay, arms, env, book, ctx) do
    bad?(s, env, book, ctx) or
      Enum.any?(arms, fn {:arm, _tag, _names, tm} = arm ->
        bad?(tm, Check.arm_env(s, slay, arm, env, ctx), book, ctx)
      end)
  end

  defp children_bad?(t, env, book, ctx) do
    t |> IR.Anf.operands() |> Enum.any?(&bad?(&1, env, book, ctx))
  end

  # -- helpers --------------------------------------------------------------

  defp unboxed_opt_image?(book, funs) do
    Enum.any?(funs, fn fun ->
      contains_unboxed_opt?(book, fun.ret) or contains_unboxed_opt?(book, fun.params) or
        contains_unboxed_opt?(book, fun.body)
    end) or Enum.any?(book, &unboxed_opt_fields?(book, &1))
  end

  defp unboxed_opt_fields?(book, %{kind: :data, ctors: ctors}) do
    Enum.any?(ctors, fn ctor -> unboxed_opt_type?(book, ctor.type) end)
  end

  defp unboxed_opt_fields?(_book, _decl), do: false

  defp unboxed_opt_type?(book, {:pi, :erased, _, _, b}), do: unboxed_opt_type?(book, b)

  defp unboxed_opt_type?(book, {:pi, _, a, _, b}) do
    type_is_unboxed_opt?(book, a) or unboxed_opt_type?(book, b)
  end

  defp unboxed_opt_type?(_book, _ty), do: false

  defp type_is_unboxed_opt?(book, {:word, :opt, [a]}) do
    unboxed_type_name?(book, a) or type_is_unboxed_opt?(book, a)
  end

  defp type_is_unboxed_opt?(book, {:ann, e, _}), do: type_is_unboxed_opt?(book, e)
  defp type_is_unboxed_opt?(_book, _ty), do: false

  defp unboxed_type_name?(book, {:def, name}), do: unboxed_decl?(book, name)
  defp unboxed_type_name?(book, {:var, name}) when is_binary(name), do: unboxed_decl?(book, name)
  defp unboxed_type_name?(book, {:app, f, _}), do: unboxed_type_name?(book, f)
  defp unboxed_type_name?(book, {:ann, e, _}), do: unboxed_type_name?(book, e)
  defp unboxed_type_name?(_book, _ty), do: false

  defp unboxed_decl?(book, name) do
    Enum.any?(book, fn
      %{kind: :data, name: ^name, unboxed: true} -> true
      _ -> false
    end)
  end

  defp contains_unboxed_opt?(book, {:opt, pay}) do
    unboxed_payload?(book, pay) or contains_unboxed_opt?(book, pay)
  end

  defp contains_unboxed_opt?(book, t) when is_tuple(t) do
    Enum.any?(Tuple.to_list(t), &contains_unboxed_opt?(book, &1))
  end

  defp contains_unboxed_opt?(book, t) when is_list(t) do
    Enum.any?(t, &contains_unboxed_opt?(book, &1))
  end

  defp contains_unboxed_opt?(_book, _t), do: false

  defp unboxed_payload?(book, {:data, name}) when is_binary(name), do: unboxed_decl?(book, name)
  defp unboxed_payload?(book, {:opt, pay}), do: unboxed_payload?(book, pay)
  defp unboxed_payload?(_book, _pay), do: false

  defp nullary_ctor?(ctor) do
    ctor.type |> telescope() |> Enum.all?(fn {q, _, _} -> q == :erased end)
  end

  defp telescope(t), do: telescope(t, [])
  defp telescope({:pi, q, a, x, b}, acc), do: telescope(b, [{q, a, x} | acc])
  defp telescope(_ret, acc), do: Enum.reverse(acc)

  defp data_defs(book), do: Enum.filter(book, &(Map.get(&1, :kind) == :data))

  defp find_data(book, name) when is_list(book) do
    Enum.find(book, &(Map.get(&1, :kind) == :data and &1.name == name))
  end

  defp find_data(_book, _name), do: nil

  defp data?(book, name) when is_list(book) do
    Enum.any?(book, &(Map.get(&1, :kind) == :data and &1.name == name))
  end

  defp data?(_book, _name), do: false
end

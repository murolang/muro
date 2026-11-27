defmodule Muro.IR.Eval.Ref do
  @moduledoc """
  The bridge between `Muro.Check.normalize/3` and `Muro.IR.Eval`.

  `of_normal/2` reads a closed normal form as an `Muro.IR.Eval` value.
  `to_term/2` writes a value back as a closed de Bruijn term, so the
  same argument can be applied on both sides. Both take the named book
  the image was elaborated from (`Muro.Load.file/1`), which says which
  constructor fields are erased. An erased field is dropped, as
  `Muro.IR.elaborate/2` drops it. Atoms are `{:con, "Atom", name, []}`
  on the value side and `{:atom, name}` on the term side.

  A λ, a stream, a stuck term, or anything else that is not a closed
  first-order value is `{:error, {:not_value, term}}`.
  """

  alias Muro.{IR, Word}

  @doc "Read the closed normal form `t` as an `Muro.IR.Eval` value."
  def of_normal(book, t) when is_list(book) do
    {:ok, value!(ctor_table(book), t)}
  catch
    {:not_value, bad} -> {:error, {:not_value, bad}}
  end

  @doc """
  Write the value `v` as a closed de Bruijn term. An erased constructor
  field is filled with `filler` (default `:one`), which the checker
  never reads. A closure or a stream is `{:error, {:not_term, v}}`.
  """
  def to_term(book, v, filler \\ :one) when is_list(book) do
    {:ok, term!(ctor_table(book), v, filler)}
  catch
    {:not_term, bad} -> {:error, {:not_term, bad}}
  end

  @doc """
  The constructors of `book`: name to `{data, [:live | :erased]}`, one
  mark per field in order.
  """
  def ctor_table(book) when is_list(book) do
    for %{kind: :data, name: data, ctors: cs} <- book, c <- cs, into: %{} do
      {c.name, {data, fields(c.type)}}
    end
  end

  defp fields({:pi, q, _a, _x, b}),
    do: [if(IR.erased_qty?(q), do: :erased, else: :live) | fields(b)]

  defp fields(_), do: []

  # -- normal form to value --------------------------------------------------

  defp value!(_tbl, :one), do: :tt
  defp value!(_tbl, {:slit, bin}) when is_binary(bin), do: {:str, bin}
  defp value!(_tbl, {:blit, bin}) when is_binary(bin), do: {:bytes, bin}
  defp value!(_tbl, {:atom, name}) when is_binary(name), do: {:con, "Atom", name, []}
  defp value!(tbl, {:pair, a, b}), do: {:pair, value!(tbl, a), value!(tbl, b)}
  defp value!(_tbl, {:word, {:lit, k, n}, []}) when is_integer(n), do: {:word, k, n}
  defp value!(_tbl, {:word, true, []}), do: true
  defp value!(_tbl, {:word, false, []}), do: false
  defp value!(_tbl, {:word, :none, []}), do: :none
  defp value!(tbl, {:word, :some, [x]}), do: {:some, value!(tbl, x)}

  defp value!(tbl, t) do
    case Word.nat_closed(t) do
      {:ok, n} -> {:nat, n}
      :error -> con!(tbl, t)
    end
  end

  defp con!(tbl, t) do
    {head, args} = spine(t, [])

    with {:def, c} <- head,
         {:ok, {data, marks}} <- Map.fetch(tbl, c),
         true <- length(marks) == length(args) do
      live =
        marks
        |> Enum.zip(args)
        |> Enum.flat_map(fn
          {:live, a} -> [value!(tbl, a)]
          {:erased, _} -> []
        end)

      {:con, data, c, live}
    else
      _ -> throw({:not_value, t})
    end
  end

  defp spine({:app, f, a}, acc), do: spine(f, [a | acc])
  defp spine(head, acc), do: {head, acc}

  # -- value to term ---------------------------------------------------------

  defp term!(_tbl, {:nat, n}, _f) when is_integer(n) and n >= 0, do: {:nat, n}
  defp term!(_tbl, :tt, _f), do: :one
  defp term!(_tbl, {:word, k, n}, _f), do: {:word, {:lit, k, n}, []}
  defp term!(_tbl, true, _f), do: {:word, true, []}
  defp term!(_tbl, false, _f), do: {:word, false, []}
  defp term!(_tbl, :none, _f), do: {:word, :none, []}
  defp term!(tbl, {:some, v}, f), do: {:word, :some, [term!(tbl, v, f)]}
  defp term!(_tbl, {:str, bin}, _f), do: {:slit, bin}
  defp term!(_tbl, {:bytes, bin}, _f), do: {:blit, bin}
  defp term!(tbl, {:pair, a, b}, f), do: {:pair, term!(tbl, a, f), term!(tbl, b, f)}
  defp term!(_tbl, {:con, "Atom", name, []}, _f), do: {:atom, name}

  defp term!(tbl, {:con, data, c, live} = v, f) do
    case Map.fetch(tbl, c) do
      {:ok, {^data, marks}} ->
        if Enum.count(marks, &(&1 == :live)) != length(live), do: throw({:not_term, v})

        {args, []} =
          Enum.map_reduce(marks, live, fn
            :erased, rest -> {f, rest}
            :live, [x | rest] -> {term!(tbl, x, f), rest}
          end)

        Enum.reduce(args, {:def, c}, &{:app, &2, &1})

      _ ->
        throw({:not_term, v})
    end
  end

  defp term!(_tbl, v, _f), do: throw({:not_term, v})
end

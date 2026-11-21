defmodule Muro.Axiom do
  @moduledoc """
  Declared axioms, and the run terms that must not reach them.

  An axiom is a signature entry: a name, the evidence tag, and a type.
  It has no body, and it does not reduce. A `?` is an unsolved goal,
  not an axiom.

  A definition depends on the axioms named in its type or its body,
  and on the axioms those definitions depend on. `mix muro.check`
  prints that set. A definition that depends on none is silent. A
  `run` that depends on an axiom is refused.
  """

  alias Muro.Print

  @doc """
  Dependency lines for `book`, or the refusals of its `run` definitions.

  `book` is de Bruijn. `{:ok, lines}` is in book order. Each line is
  `<name>: depends on <File.axiom>`. Several axioms are separated by
  `, `, in the order the axioms are declared. `{:error, message}` is
  one refusal per `run`, in book order, separated by a blank line.
  A book with no axiom has no lines.
  """
  def report(book) when is_list(book) do
    axioms = for %{kind: :axiom, name: name} = d <- book, is_binary(name), do: d

    case axioms do
      [] ->
        {:ok, []}

      _ ->
        direct = direct(book)
        labels = Map.new(axioms, fn d -> {d.name, label(d)} end)
        order = Enum.map(axioms, & &1.name)
        reached = closure(direct, MapSet.new(order))
        split(term_decls(book), reached, order, labels)
    end
  end

  defp split(decls, reached, order, labels) do
    {errors, lines} =
      Enum.reduce(decls, {[], []}, fn d, {errors, lines} ->
        set = Map.get(reached, d.name, MapSet.new())
        set = if axiom?(d), do: MapSet.delete(set, d.name), else: set
        names = Enum.filter(order, &MapSet.member?(set, &1))

        cond do
          names == [] ->
            {errors, lines}

          run?(d) ->
            msg =
              "#{Print.loc_prefix(Map.get(d, :loc))}#{d.name}: a run depends on #{show(names, labels)}"

            {errors ++ [msg], lines}

          true ->
            {errors, lines ++ ["#{d.name}: depends on #{show(names, labels)}"]}
        end
      end)

    case errors do
      [] -> {:ok, lines}
      msgs -> {:error, Enum.join(msgs, "\n\n")}
    end
  end

  defp show(names, labels), do: Enum.map_join(names, ", ", &Map.fetch!(labels, &1))

  defp label(%{name: name} = d) do
    case stem(Map.get(d, :file)) do
      nil -> name
      stem -> stem <> "." <> name
    end
  end

  defp stem(file) when is_binary(file) do
    file
    |> String.split("/")
    |> List.last()
    |> String.split(":")
    |> List.last()
    |> String.trim_trailing(".muro")
  end

  defp stem(_), do: nil

  defp direct(book) do
    Map.new(term_decls(book), fn d -> {d.name, refs(d)} end)
  end

  defp refs(%{type: ty, body: body}), do: mentions(body, mentions(ty, [])) |> Enum.uniq()
  defp refs(%{type: ty}), do: mentions(ty, []) |> Enum.uniq()
  defp refs(_), do: []

  # Each axiom reaches itself. A step unions the sets of the names a
  # definition mentions. A cycle stops when the sets stop growing.
  defp closure(direct, axiom_names) do
    init =
      Map.new(direct, fn {n, _} ->
        {n, if(MapSet.member?(axiom_names, n), do: MapSet.new([n]), else: MapSet.new())}
      end)

    fix(direct, init, map_size(direct) + 1)
  end

  defp fix(_direct, acc, 0), do: acc

  defp fix(direct, acc, fuel) do
    next =
      Map.new(acc, fn {n, set} ->
        set =
          Enum.reduce(Map.get(direct, n, []), set, fn r, set ->
            MapSet.union(set, Map.get(acc, r, MapSet.new()))
          end)

        {n, set}
      end)

    if next == acc, do: acc, else: fix(direct, next, fuel - 1)
  end

  defp term_decls(book), do: Enum.filter(book, &term_decl?/1)

  defp term_decl?(%{kind: :axiom, name: name}) when is_binary(name), do: true
  defp term_decl?(%{kind: :param, name: name}) when is_binary(name), do: true
  defp term_decl?(%{kind: kind}) when not is_nil(kind), do: false

  defp term_decl?(%{name: name, mode: mode, type: _})
       when is_binary(name) and mode in [:run, :evidence, :spec],
       do: true

  defp term_decl?(_), do: false

  defp axiom?(%{kind: :axiom}), do: true
  defp axiom?(_), do: false

  defp run?(%{mode: :run}), do: true
  defp run?(_), do: false

  defp mentions({:def, n}, acc) when is_binary(n), do: [n | acc]

  defp mentions(t, acc) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.reduce(acc, &mentions/2)
  end

  defp mentions(t, acc) when is_list(t), do: Enum.reduce(t, acc, &mentions/2)
  defp mentions(_, acc), do: acc
end

defmodule Muro.Axiom do
  @moduledoc """
  Declared axioms, and the run terms that must not reach them.

  An axiom is a signature entry: a name, the evidence tag, and a type.
  It has no body, and it does not reduce. A `?` is an unsolved goal,
  not an axiom.

  A definition depends on the axioms named in its type or its body,
  and on the axioms those definitions depend on.

  `mix muro.check` and `muro check` print that set for the definitions
  the entry file reaches. The entry file reaches every definition it
  declares, and every definition mentioned from one it reaches. An
  imported definition that chain does not mention is silent. A
  definition that depends on none is silent. A `run` that depends on
  an axiom is refused wherever it sits in the joined book, because
  that run is emitted.
  """

  alias Muro.Print

  @doc """
  Dependency lines for `book`, or the refusals of its `run` definitions.

  `book` is de Bruijn. `entry:` is the file the check was asked for.
  `{:ok, lines}` is in book order, and only for definitions that file
  reaches. Each line is `<name>: depends on <File.axiom>`. Several
  axioms are separated by `, `, in the order the axioms are declared.
  `{:error, message}` is one refusal per `run` that reaches an axiom,
  in book order, separated by a blank line, including a `run` the
  entry file does not mention. A book with no axiom has no lines.
  Omitting `entry:` reports every non-`run` definition, which is the
  book handed to `Muro.Check.check_sig/2` when no file was loaded.
  """
  def report(book, opts \\ []) when is_list(book) and is_list(opts) do
    axioms = for %{kind: :axiom, name: name} = d <- book, is_binary(name), do: d

    case axioms do
      [] ->
        {:ok, []}

      _ ->
        direct = direct(book)
        labels = Map.new(axioms, fn d -> {d.name, label(d)} end)
        order = Enum.map(axioms, & &1.name)
        reached = closure(direct, MapSet.new(order))
        scope = scope(book, Keyword.get(opts, :entry), direct)
        split(term_decls(book), reached, order, labels, scope)
    end
  end

  # Names the entry file reaches. No entry means the whole book.
  defp scope(book, nil, _direct) do
    MapSet.new(for d <- term_decls(book), do: d.name)
  end

  defp scope(book, entry, direct) when is_binary(entry) do
    roots = for d <- term_decls(book), Map.get(d, :file) == entry, do: d.name
    grow(MapSet.new(roots), direct)
  end

  defp grow(set, direct) do
    more =
      Enum.reduce(set, [], fn n, acc ->
        Enum.reduce(Map.get(direct, n, []), acc, fn r, acc ->
          if MapSet.member?(set, r), do: acc, else: [r | acc]
        end)
      end)

    case more do
      [] -> set
      _ -> grow(MapSet.union(set, MapSet.new(more)), direct)
    end
  end

  defp split(decls, reached, order, labels, scope) do
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

          MapSet.member?(scope, d.name) ->
            {errors, lines ++ ["#{d.name}: depends on #{show(names, labels)}"]}

          true ->
            {errors, lines}
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

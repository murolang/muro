defmodule Muro.Prelude do
  @moduledoc """
  The book `Muro.check_file/2` puts in scope behind the file.

  A name the file defines replaces the prelude definition of that name.
  A prelude definition that refers to a replaced name is dropped too, so
  `plus_suc` is not offered as a lemma about a different `plus`.

  Prelude `run` definitions are emitted only when a `run` term in the file
  calls them, and then as `defp`.
  """

  alias Muro.{Ast, Parser}

  @external_resource Path.join(__DIR__, "prelude.muro")
  @source File.read!(Path.join(__DIR__, "prelude.muro"))

  @doc "The prelude source."
  def source, do: @source

  @doc "The parsed prelude."
  def book do
    case Parser.parse(@source) do
      {:ok, book} -> book
      {:error, msg} -> raise "prelude: #{msg}"
    end
  end

  @doc "The file's book, then the prelude definitions still in scope."
  def for_check(user_book) when is_list(user_book) do
    user_book ++ visible(user_book)
  end

  @doc """
  The file's book, plus prelude `run` definitions a `run` term calls.
  Those extras are `export: false` (`defp`).
  """
  def for_emit(user_book) when is_list(user_book) do
    visible = visible(user_book)
    used = used_runs(user_book, visible)

    extras =
      for d <- visible, Map.get(d, :mode) == :run and d.name in used do
        Map.put(d, :export, false)
      end

    user_book ++ extras
  end

  defp visible(user_book) do
    prelude = book()
    hidden = hidden(prelude, names(user_book))
    Enum.reject(prelude, &(&1.name in hidden))
  end

  defp names(book), do: MapSet.new(for %{name: name} <- book, do: name)

  # User names, plus any prelude definition that refers to one of them.
  defp hidden(prelude, user_names) do
    refs = Map.new(prelude, fn d -> {d.name, def_refs(d)} end)
    grow(user_names, refs)
  end

  defp grow(hidden, refs) do
    more =
      for {name, rs} <- refs,
          name not in hidden,
          Enum.any?(rs, &(&1 in hidden)),
          do: name

    case more do
      [] -> hidden
      _ -> grow(MapSet.union(hidden, MapSet.new(more)), refs)
    end
  end

  defp used_runs(user_book, visible) do
    runs = Map.new(for d <- visible, Map.get(d, :mode) == :run, do: {d.name, d})
    run_names = MapSet.new(Map.keys(runs))

    seeds =
      user_book
      |> Enum.filter(&(Map.get(&1, :kind, :def) != :data and Map.get(&1, :mode) == :run))
      |> Enum.reduce(MapSet.new(), fn d, acc -> MapSet.union(acc, mentions(d)) end)
      |> MapSet.intersection(run_names)

    close_runs(seeds, runs, run_names)
  end

  defp close_runs(names, runs, run_names) do
    more =
      Enum.reduce(names, names, fn n, acc ->
        MapSet.union(acc, MapSet.intersection(mentions(runs[n]), run_names))
      end)

    if MapSet.equal?(more, names), do: names, else: close_runs(more, runs, run_names)
  end

  # Definition names a def refers to, not counting itself.
  defp def_refs(d), do: MapSet.delete(mentions(d), d.name)

  defp mentions(%{type: ty, body: body}) do
    {:ok, ty1} = Ast.to_db(ty)
    {:ok, body1} = Ast.to_db(body)
    MapSet.union(collect(ty1), collect(body1))
  end

  defp mentions(_), do: MapSet.new()

  defp collect({:def, n}, acc), do: MapSet.put(acc, n)

  defp collect(t, acc) when is_tuple(t) do
    t |> Tuple.to_list() |> Enum.reduce(acc, &collect/2)
  end

  defp collect(t, acc) when is_list(t), do: Enum.reduce(t, acc, &collect/2)
  defp collect(_, acc), do: acc

  defp collect(t), do: collect(t, MapSet.new())
end

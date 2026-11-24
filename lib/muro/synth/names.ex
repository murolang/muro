defmodule Muro.Synth.Names do
  @moduledoc false

  # Preferred binders used in generated synthesis books. A name the
  # environment already uses is not reused: `fresh/2` walks `base-2`,
  # `base-3`, ... until the full identifier is free, including a
  # reserved name that shares the prefix.
  @standard ~w(c f p q r a b s t x y z n k m j d h i u A xs ys n1 m1)

  # Primitives, prelude runs, and lexicon words the generated book
  # mentions as globals. They are not always present as book entries
  # (`suc` is not a constructor of a loaded `Nat`, and `plus` is a
  # prelude run), so `occupied?/2` rejects them even when `taken` is
  # only the environment's declarations.
  @blocked MapSet.new(
             Enum.map(Muro.Words.lexicon(), &elem(&1, 0)) ++
               Muro.Words.decl_words() ++
               Muro.Words.naming_words() ++
               Muro.Words.nu_words() ++
               Muro.Words.pi_words() ++
               Muro.Words.lam_words() ++
               Muro.Words.elam_words() ++
               ~w(Nat suc pred plus Bool true false List cons nil Unit Empty Type
                  tt refl fst snd)
           )

  @doc "Preferred binder spellings used in generated books."
  def standard_bases, do: @standard

  @doc """
  Declaration and constructor names of a loaded book, including the
  Elixir spelling `Muro.Load` would treat as the same run.
  """
  def reserved(book) when is_list(book) do
    Enum.reduce(book, MapSet.new(), fn entry, acc -> take(acc, entry_names(entry)) end)
  end

  def reserved(_book), do: MapSet.new()

  @doc """
  A map from each preferred spelling to a binder that does not collide
  with `taken`, and the set with those binders reserved.
  """
  def table(taken, bases \\ @standard) do
    Enum.map_reduce(bases, taken, fn base, taken ->
      {name, taken} = alloc(base, taken)
      {{base, name}, taken}
    end)
    |> then(fn {pairs, taken} -> {Map.new(pairs), taken} end)
  end

  @doc "Whether every preferred spelling in `bases` was kept as itself."
  def free?(binders, bases \\ @standard) do
    Enum.all?(bases, &(Map.fetch!(binders, &1) == &1))
  end

  @doc """
  Binders and the reserved set for one generated book.

  The process dictionary keys `:muro_synth_binders` and
  `:muro_synth_taken` are only valid inside this wrapper, which
  `Book.render/4` uses while it emits a policy book. Callers that
  already have the reserved set must pass it as `with_binders/3`.
  The arity-2 form only extends a reserved set that is already
  installed; it is refused when that set is absent, so it cannot
  silently forget environment names.
  """
  def with_binders(binders, fun) when is_map(binders) and is_function(fun, 0) do
    case Process.get(:muro_synth_taken) do
      %MapSet{} = existing ->
        with_binders(binders, Enum.reduce(Map.values(binders), existing, &take(&2, &1)), fun)

      _ ->
        raise ArgumentError,
              "Names.with_binders/2 needs :muro_synth_taken already set; pass the reserved set to with_binders/3"
    end
  end

  def with_binders(binders, taken, fun)
      when is_map(binders) and is_function(fun, 0) do
    prev_binders = Process.get(:muro_synth_binders)
    prev_taken = Process.get(:muro_synth_taken)
    Process.put(:muro_synth_binders, binders)
    Process.put(:muro_synth_taken, taken)

    try do
      fun.()
    after
      restore(:muro_synth_binders, prev_binders)
      restore(:muro_synth_taken, prev_taken)
    end
  end

  @doc """
  The reserved set installed for the book being rendered, or an empty
  set outside `with_binders/3`.
  """
  def taken do
    case Process.get(:muro_synth_taken) do
      %MapSet{} = taken -> taken
      _ -> MapSet.new()
    end
  end

  @doc "Union of `extra` with the reserved set of the current book, if any."
  def merge_taken(extra) when is_struct(extra, MapSet) do
    MapSet.union(taken(), extra)
  end

  @doc """
  A fresh binder for `base` against the current book's reserved set.

  The reserved set is updated so a later binder cannot reuse the name.
  A local `taken` is merged in when the caller is walking a nest.
  """
  def alloc_current(base, taken \\ nil) when is_binary(base) do
    taken = merge_taken(taken || MapSet.new())

    case Process.get(:muro_synth_binders) do
      %{} = binders ->
        case Map.fetch(binders, base) do
          {:ok, name} ->
            {name, take(taken, name)}

          :error ->
            {name, taken} = alloc(base, taken)
            Process.put(:muro_synth_binders, Map.put(binders, base, name))
            Process.put(:muro_synth_taken, taken)
            {name, taken}
        end

      _ ->
        alloc(base, taken)
    end
  end

  @doc "The binder for a preferred spelling in the current generated book."
  def current(base) when is_binary(base) do
    {name, _} = alloc_current(base)
    name
  end

  defp restore(key, nil), do: Process.delete(key)
  defp restore(key, value), do: Process.put(key, value)

  @doc "A fresh identifier and the set with that name reserved."
  def alloc(base, taken) do
    name = fresh(base, taken)
    {name, take(taken, name)}
  end

  @doc """
  A valid Muro identifier that is not in `taken`, is not a reserved
  word, and does not share an Elixir spelling with one that is.
  """
  def fresh(base, taken) do
    if occupied?(base, taken) do
      n = Enum.find(2..10_000, &(not occupied?("#{base}-#{&1}", taken)))
      "#{base}-#{n}"
    else
      base
    end
  end

  def occupied?(name, taken) do
    MapSet.member?(@blocked, name) or
      MapSet.member?(taken, name) or
      MapSet.member?(taken, {:elixir, Muro.Emit.elixir_base(name)})
  end

  def take(taken, names) when is_list(names) do
    Enum.reduce(names, taken, &take(&2, &1))
  end

  def take(taken, name) when is_binary(name) do
    taken
    |> MapSet.put(name)
    |> MapSet.put({:elixir, Muro.Emit.elixir_base(name)})
  end

  defp entry_names(%{kind: :data, name: name, ctors: ctors}),
    do: [name | Enum.map(ctors, &ctor_name/1)]

  defp entry_names(%{kind: :import}), do: []
  defp entry_names(%{name: name}) when is_binary(name), do: [name]
  defp entry_names(_entry), do: []

  defp ctor_name(%{name: name}), do: name
  defp ctor_name(name) when is_binary(name), do: name
end

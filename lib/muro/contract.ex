defmodule Muro.Contract do
  @moduledoc """
  A stated external contract from a closed list.

  The entries are `idempotent init`, `in order`, and `dense`. `may
  redeliver` is a mark on a family, not an entry here. `dedupe` parses
  as a name of this list and is refused: it is not in this version.
  A contract is not an axiom and not an evidence term.

  `idempotent init` is a waiver of one repeat. `in order` and `dense`
  narrow arrivals. `skip` drops the run-time check and leaves the
  narrowing in place. The family graph reads the declaration, with or
  without `skip`.
  """

  @idempotent :idempotent_init
  @narrowing [:in_order, :dense]

  @doc "The atom in `{:contract, name, key, index}` for `idempotent init`."
  def idempotent_init, do: @idempotent

  @doc """
  `:ok` when `decl` names a known family and this is the earliest
  declaration of that entry on that family. `idempotent init` also
  needs a constructor `init`. `in order` and `dense` do not.
  `{:error, message}` otherwise. The message has a location and no
  declaration name.
  """
  def check(book, %{kind: :contract, family: family, entry: entry, loc: loc} = decl)
      when is_list(book) do
    with :ok <- entry_ok(entry),
         :ok <- known_family(book, family),
         :ok <- needs_init(book, family, entry),
         :ok <- one_entry(book, decl),
         :ok <- script(book, family, entry) do
      :ok
    else
      {:error, msg} -> {:error, "#{Muro.Print.loc_prefix(loc)}#{msg}"}
    end
  end

  @doc "Whether `family` declares `entry`."
  def declared?(book, family, entry) when is_list(book) and is_binary(family) do
    Enum.any?(book, &match?(%{kind: :contract, family: ^family, entry: ^entry}, &1))
  end

  @doc """
  The waiver on `family`, or `nil` when that family declares none.
  The earliest declaration wins. `%{entry: :idempotent_init, skip: bool}`.
  """
  def waiver_of(book, family) when is_list(book) and is_binary(family) do
    entry(book, family, @idempotent)
  end

  @doc """
  The declaration of `entry` on `family`, or `nil`.
  `%{entry: atom, skip: bool}`.
  """
  def entry(book, family, entry) when is_list(book) and is_binary(family) do
    case Enum.find(book, &match?(%{kind: :contract, family: ^family, entry: ^entry}, &1)) do
      nil -> nil
      %{skip: skip} -> %{entry: entry, skip: skip == true}
    end
  end

  @doc """
  Whether `family` declares `in order` or `dense`. `skip` still counts:
  the graph narrows either way. `%{in_order: bool, dense: bool}`.
  """
  def narrowing(book, family) when is_list(book) and is_binary(family) do
    %{
      in_order: entry(book, family, :in_order) != nil,
      dense: entry(book, family, :dense) != nil
    }
  end

  @doc "The surface spelling of a closed-list entry."
  def spell(:in_order), do: "in order"
  def spell(:dense), do: "dense"
  def spell(:dedupe), do: "dedupe"
  def spell(@idempotent), do: "idempotent init"
  def spell(other), do: to_string(other)

  @doc false
  def creation(instances, entry) when entry in @narrowing and is_list(instances) do
    instances
    |> Enum.group_by(& &1.key)
    |> Enum.reduce_while(:ok, fn {_key, rows}, :ok ->
      case scan(rows, entry) do
        :ok -> {:cont, :ok}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp entry_ok(@idempotent), do: :ok
  defp entry_ok(:in_order), do: :ok
  defp entry_ok(:dense), do: :ok
  defp entry_ok(:dedupe), do: {:error, "dedupe is not in this version"}
  defp entry_ok(other), do: {:error, "unknown contract entry #{spell(other)}"}

  defp known_family(book, family) do
    case Enum.find(book, &match?(%{kind: :family, name: ^family}, &1)) do
      nil ->
        {:error, "unknown family #{family}"}

      %{key: nil} ->
        {:error, "#{family} ranges over a choreography: a contract names a family of a meeting"}

      _ ->
        :ok
    end
  end

  defp needs_init(book, family, @idempotent), do: has_init(book, family)
  defp needs_init(_book, _family, _entry), do: :ok

  defp has_init(book, family_name) do
    family = Enum.find(book, &match?(%{kind: :family, name: ^family_name}, &1))
    data = Enum.find(book, &(&1[:kind] == :data and &1[:name] == family.key))
    ctors = if data, do: Map.get(data, :ctors, []), else: []

    if Enum.any?(ctors, &(&1.name == "init")) do
      :ok
    else
      {:error, "no constructor init"}
    end
  end

  # The built-in script gives each key the indices `0, 1, …` in creation
  # order, so this passes for a family the checker accepts. A caller that
  # supplies its own instances, and a later script that does not, is
  # refused here. An empty constructor list is the family's own error.
  defp script(book, family_name, entry) when entry in @narrowing do
    family = Enum.find(book, &match?(%{kind: :family, name: ^family_name}, &1))
    data = family && Enum.find(book, &(&1[:kind] == :data and &1[:name] == family.key))
    ctors = if data, do: Map.get(data, :ctors, []), else: []

    if family && data && ctors != [] && is_list(Map.get(family, :rules)) do
      creation(Muro.Family.Graph.instances(book, family), entry)
    else
      :ok
    end
  end

  defp script(_book, _family_name, _entry), do: :ok

  defp scan(rows, :in_order), do: late_scan(rows, -1)
  defp scan(rows, :dense), do: gap_scan(rows)

  defp late_scan([], _max_seen), do: :ok

  defp late_scan([%{index: index} | rest], max_seen) when is_integer(index) do
    if index < max_seen do
      {:error, "in order creates an index late"}
    else
      late_scan(rest, max(max_seen, index))
    end
  end

  defp late_scan(_rows, _max_seen), do: {:error, "in order creates an index late"}

  defp gap_scan(rows) do
    indices = Enum.map(rows, & &1.index)

    cond do
      indices == [] ->
        :ok

      not Enum.all?(indices, &is_integer/1) ->
        {:error, "dense creates a gap"}

      indices != Enum.uniq(indices) ->
        {:error, "dense creates a gap"}

      true ->
        sorted = Enum.sort(indices)

        if sorted == Enum.to_list(0..List.last(sorted)//1) do
          :ok
        else
          {:error, "dense creates a gap"}
        end
    end
  end

  # Both declarations are checked against the whole joined book, after
  # imports have been relocated. The first `{family, entry}` in book
  # order stands. A later one is a duplicate, including when one is
  # `skip` and the other is not, and including a `{file, line, col}`
  # location from `Load.relocate/3`.
  defp one_entry(book, %{family: family, entry: entry} = decl) do
    case Enum.find(book, &match?(%{kind: :contract, family: ^family, entry: ^entry}, &1)) do
      ^decl -> :ok
      _other -> {:error, "duplicate contract #{spell(entry)}"}
    end
  end
end

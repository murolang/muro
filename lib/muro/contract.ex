defmodule Muro.Contract do
  @moduledoc """
  A stated external contract from a closed list.

  Part 1 has one waiver, `idempotent init`. `may redeliver` is a mark on
  a family, not an entry here. `in order`, `dense`, and `dedupe` parse
  as names of this list and are refused: they are not in this version.
  A contract is not an axiom and not an evidence term.
  """

  @idempotent :idempotent_init

  @doc "The atom in `{:contract, name, key, index}` for `idempotent init`."
  def idempotent_init, do: @idempotent

  @doc """
  `:ok` when `decl` names a family that has a constructor `init`, and
  this is the earliest declaration of that entry on that family.
  `{:error, message}` otherwise. The message has a location and no
  declaration name.
  """
  def check(book, %{kind: :contract, family: family, entry: entry, loc: loc} = decl)
      when is_list(book) do
    with :ok <- entry_ok(entry),
         :ok <- known_family(book, family),
         :ok <- has_init(book, family),
         :ok <- one_entry(book, decl) do
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
    case Enum.find(book, &match?(%{kind: :contract, family: ^family, entry: @idempotent}, &1)) do
      nil -> nil
      %{skip: skip} -> %{entry: @idempotent, skip: skip == true}
    end
  end

  @doc "The surface spelling of a closed-list entry."
  def spell(:in_order), do: "in order"
  def spell(:dense), do: "dense"
  def spell(:dedupe), do: "dedupe"
  def spell(@idempotent), do: "idempotent init"
  def spell(other), do: to_string(other)

  defp entry_ok(@idempotent), do: :ok
  defp entry_ok(:in_order), do: {:error, "in order is not in this version"}
  defp entry_ok(:dense), do: {:error, "dense is not in this version"}
  defp entry_ok(:dedupe), do: {:error, "dedupe is not in this version"}
  defp entry_ok(other), do: {:error, "unknown contract entry #{spell(other)}"}

  defp known_family(book, family) do
    if Enum.any?(book, &match?(%{kind: :family, name: ^family}, &1)) do
      :ok
    else
      {:error, "unknown family #{family}"}
    end
  end

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

  # Both declarations are checked against the whole book. The earliest
  # location is the one that stands. A later one is the duplicate.
  defp one_entry(book, %{family: family, entry: entry, loc: loc}) do
    earlier =
      Enum.any?(book, fn
        %{kind: :contract, family: ^family, entry: ^entry, loc: other} ->
          loc_before?(other, loc)

        _ ->
          false
      end)

    if earlier, do: {:error, "duplicate contract #{spell(entry)}"}, else: :ok
  end

  defp loc_before?({l1, c1}, {l2, c2}) when is_integer(l1) and is_integer(c1) do
    l1 < l2 or (l1 == l2 and c1 < c2)
  end

  defp loc_before?(_, _), do: false
end

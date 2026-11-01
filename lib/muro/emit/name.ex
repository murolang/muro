defmodule Muro.Emit.Name.Scope do
  @moduledoc false
  defstruct [:names]
end

defmodule Muro.Emit.Name do
  @moduledoc """
  Identifiers for the C, Rust, and Zig emitters.

  Every emitted identifier is built here, and it lands in exactly one of
  two sets.

  A source-derived name is `spell/3` of a source identifier, then
  `claim/2` or `claim_n/3` if that spelling is already taken. `encode/1`
  is injective on the source alphabet (`A-Z`, `a-z`, digits, `_`, `-`,
  `'`). It writes no underscore: `z` and `Z` are doubled, `_` is `zu`,
  `-` is `zd`, and `'` is `zq`. `spell/3` appends `_k` when the encoding
  is a keyword, a primitive, or a host name. That is underscore then `k`,
  and the encoding does not end in `_`. `claim/2` appends `_` and a
  decimal starting at 2. The base does not end in `_`, so the suffix
  does not create `__`. A source-derived name therefore contains no `__`.

  A generated name is `gen/1` or `gen/2`: the prefix `muro__` plus a tag
  the emitter chooses (a helper, a step, a constructor argument, a
  temporary). It always contains `__`. `claim/2` on a generated name
  appends `_` and a decimal, which keeps the `__`.

  The two sets are disjoint. A source-derived name has no `__`, and a
  generated name has `__`, including after either side is suffixed.
  Suffixing one space cannot enter the other.

  A binder is chosen with `bind/2` or `bind_n/3` on a scope from
  `open/1`. That scope is every identifier already visible where the
  binder is introduced, including type names. `bind/2` claims against
  the whole scope, then adds the chosen spelling. A caller does not
  pass a smaller set. `see/2` records a generated identifier that is
  already visible. The C, Rust, and Zig symbol stays in this module.
  An Elixir host name is `Muro.Emit.elixir_base/1` of the source name.
  It is not this spelling.

  `spell/3` then `claim/2` is injective on distinct source names. `encode/1`
  is injective, and `_k` sits outside its image, so `spell/3` is injective.
  A claimed suffix is `_` plus digits. No spelling is of that form: an
  encoding has no underscore, and a keyword form ends in `_k`. The base is
  what remains after stripping one trailing `_` plus digits, so different
  bases, and different suffixes of one base, are different identifiers.
  In particular `a-b`, `a_b`, and `a_b_2` spell three ways (`azdb`, `azub`,
  `azubzu2`), and none of those is a suffix of another.
  """

  @marker "__"

  @doc """
  Injective encoding of a source identifier. The result has no underscore.
  """
  def encode(name) when is_binary(name) do
    name
    |> String.to_charlist()
    |> Enum.map_join(&encode_char/1)
  end

  @doc """
  Source spelling. `forbidden` is the backend's keywords, primitives, and
  host names, matched against the encoding. `pred` is an extra shape the
  backend cannot use as an identifier, such as Zig's `u8` / `i32`.

  The result has no `__`.
  """
  def spell(name, forbidden, pred \\ fn _ -> false end)
      when is_binary(name) and (is_struct(forbidden, MapSet) or is_map(forbidden)) and
             is_function(pred, 1) do
    encoded = encode(name)
    if MapSet.member?(forbidden, encoded) or pred.(encoded), do: encoded <> "_k", else: encoded
  end

  @doc """
  A generated identifier. `tag` is `[A-Za-z][A-Za-z0-9_]*`, has no `__`,
  and does not end in `_`. The result always contains `__`.
  """
  def gen(tag) when is_binary(tag) do
    "muro" <> @marker <> check_tag(tag)
  end

  @doc """
  `gen/1` with a decimal tail: `muro__step_0`. The `__` stays.
  """
  def gen(tag, n) when is_binary(tag) and is_integer(n) and n >= 0 do
    gen(tag) <> "_" <> Integer.to_string(n)
  end

  @doc """
  First free spelling of `base`, then `base_2`, `base_3`, and so on.

  The suffix keeps a source base free of `__` and keeps a generated base's
  `__`. It does not move a name from one space to the other.
  """
  def claim(base, used) when is_binary(base) do
    name = if MapSet.member?(used, base), do: bump(base, 2, used), else: base
    {name, MapSet.put(used, name)}
  end

  @doc """
  Like `claim/2`, but the first suffix tried is `base_n` when `base` is
  taken. `n` is the emitter's local counter.
  """
  def claim_n(base, n, used) when is_binary(base) and is_integer(n) and n >= 0 do
    candidate = if MapSet.member?(used, base), do: suffix(base, n), else: base

    if MapSet.member?(used, candidate) do
      claim_n(base, n + 1, used)
    else
      {candidate, MapSet.put(used, candidate)}
    end
  end

  @doc """
  A scope of identifiers a binder must not take.

  `visible` is everything already in scope, including type names.
  """
  def open(visible) when is_struct(visible, MapSet) do
    %__MODULE__.Scope{names: visible}
  end

  @doc """
  Claim `base` against every name in `scope`, then add the spelling.

  This is the only way a binder is chosen. The type names opened into
  the scope stay visible to every later binder.
  """
  def bind(base, %__MODULE__.Scope{names: names} = scope) when is_binary(base) do
    {chosen, names} = claim(base, names)
    {chosen, %{scope | names: names}}
  end

  @doc """
  `bind/2` with `claim_n/3` as the suffix counter.
  """
  def bind_n(base, n, %__MODULE__.Scope{names: names} = scope)
      when is_binary(base) and is_integer(n) and n >= 0 do
    {chosen, names} = claim_n(base, n, names)
    {chosen, %{scope | names: names}}
  end

  @doc """
  Record an identifier that is already visible, such as a generated
  parameter the emitter chose before the binders.
  """
  def see(%__MODULE__.Scope{names: names} = scope, name) when is_binary(name) do
    %{scope | names: MapSet.put(names, name)}
  end

  @doc """
  Whether `name` is in the generated space. Generated names are exactly
  those that contain `__`.
  """
  def generated?(name) when is_binary(name), do: String.contains?(name, @marker)

  defp encode_char(?z), do: "zz"
  defp encode_char(?Z), do: "ZZ"
  defp encode_char(?_), do: "zu"
  defp encode_char(?-), do: "zd"
  defp encode_char(?'), do: "zq"

  defp encode_char(c) when c in ?0..?9 or c in ?a..?y or c in ?A..?Y, do: <<c>>

  # Outside the source alphabet. Four hex digits keep the encoding
  # prefix-free and free of underscores.
  defp encode_char(c) when is_integer(c) and c >= 0 do
    "zn" <> (c |> Integer.to_string(16) |> String.pad_leading(4, "0"))
  end

  defp check_tag(tag) do
    if String.match?(tag, ~r/^[A-Za-z][A-Za-z0-9_]*$/) and not String.contains?(tag, @marker) and
         not String.ends_with?(tag, "_") do
      tag
    else
      raise ArgumentError, "generated tag #{inspect(tag)} is not a bare identifier"
    end
  end

  defp bump(base, i, used) do
    n = suffix(base, i)
    if MapSet.member?(used, n), do: bump(base, i + 1, used), else: n
  end

  defp suffix(base, i), do: base <> "_" <> Integer.to_string(i)
end

defmodule Muro.Session do
  @moduledoc """
  The Elixir mirror of `decide` and `finishes` in `agda/Muro/Session.agda`.

  A communication carries a payload type and one continuation. The
  payload is a nat, a bit, unit, a pair, or a record of named fields.
  A pair is a tuple. A record is a fixed map: the names, in the order
  written, are the type. `put` sends a value of that type. `get` binds
  the received value to a named variable that can be used in the
  continuation. `choose` and `branch` select an arm. `stop` conforms
  to every protocol. `finishes/1` is `:yes` when every leaf is `done`.
  `skel/1` carries the value on `say` and the type on `hear`. `dual/1`
  swaps direction and keeps the payload type.
  """

  @doc """
  The other end of a protocol. Mirrors `dual` in `agda/Muro/Dual.agda`.

  `send` swaps with `recv`. `choose` swaps with `branch`. The payload
  type stays. The continuation dualises.
  """
  def dual(:end), do: :end
  def dual({:send, a, s}), do: {:recv, a, dual(s)}
  def dual({:recv, a, s}), do: {:send, a, dual(s)}
  def dual({:choose, s, t}), do: {:branch, dual(s), dual(t)}
  def dual({:branch, s, t}), do: {:choose, dual(s), dual(t)}

  @doc """
  The actions of a process. Mirrors `skel` in `agda/Muro/Session.agda`.

  `say` carries the value a peer receives. `hear` carries the type.
  """
  def skel(proc), do: skel_go(proc)

  defp skel_go(:done), do: :finish
  defp skel_go(:stop), do: :leave
  defp skel_go({:put, _ty, val, p}), do: {:say, runtime(val), skel_go(p)}
  defp skel_go({:get, ty, name, p}), do: {:hear, ty, name, skel_go(p)}
  defp skel_go({:pick0, p}), do: {:choose, :b0, skel_go(p)}
  defp skel_go({:pick1, p}), do: {:choose, :b1, skel_go(p)}
  defp skel_go({:cover, p, q}), do: {:offer, skel_go(p), skel_go(q)}

  @doc """
  The value as the OTP message carries it. A nat is an integer. A
  pair is a two-element tuple. A record is a map whose keys are the
  field names.
  """
  def runtime({:nat, n}) when is_integer(n) and n >= 0, do: n
  def runtime(bit) when bit in [:b0, :b1], do: bit
  def runtime(:tt), do: :tt
  def runtime({:var, name}), do: {:var, name}
  def runtime({:tup, a, b}), do: {runtime(a), runtime(b)}

  def runtime({:rec, fields}) when is_list(fields) do
    Map.new(fields, fn {name, val} -> {name, runtime(val)} end)
  end

  @doc """
  Whether a message value is of the payload type. A record matches by
  field name. The order of the names is the type, and it is compared
  with the protocol before this check.
  """
  def fits?(:nat, n) when is_integer(n) and n >= 0, do: true
  def fits?(:bit, bit) when bit in [:b0, :b1], do: true
  def fits?(:unit, :tt), do: true
  def fits?({:pair, a, b}, {x, y}), do: fits?(a, x) and fits?(b, y)

  def fits?({:rec, fields}, map) when is_list(fields) and is_map(map) do
    names = Enum.map(fields, fn {name, _} -> name end)

    Enum.sort(Map.keys(map)) == Enum.sort(names) and
      Enum.all?(fields, fn {name, ty} -> fits?(ty, Map.get(map, name)) end)
  end

  def fits?(_, _), do: false

  @doc """
  `:yes` when `finishes` returns `ends`. `stop` is `:no`.
  Mirrors `finishes` in `agda/Muro/Session.agda`.
  """
  def finishes(proc), do: finishes_go(proc)

  defp finishes_go(:done), do: :yes
  defp finishes_go(:stop), do: :no
  defp finishes_go({:put, _, _, p}), do: finishes_go(p)
  defp finishes_go({:get, _, _, p}), do: finishes_go(p)
  defp finishes_go({:pick0, p}), do: finishes_go(p)
  defp finishes_go({:pick1, p}), do: finishes_go(p)

  defp finishes_go({:cover, p, q}) do
    case finishes_go(p) do
      :yes -> finishes_go(q)
      :no -> :no
    end
  end

  @doc """
  `:ok` when `decide` returns `yes`. Otherwise the pair where it returns `no`.
  """
  def conforms(proc, proto) do
    case go(proc, proto, %{}) do
      :ok -> :ok
      {:no, p, s} -> {:error, "#{show_proc(p)} does not conform to #{show_proto(s)}"}
    end
  end

  defp go(:done, :end, _ctx), do: :ok
  defp go(:stop, _, _ctx), do: :ok

  # put with inferred type (when value is a literal)
  defp go({:put, ty, val, p} = proc, {:send, ty, s} = proto, ctx) do
    if value?(val, ty, ctx), do: keep(go(p, s, ctx)), else: {:no, proc, proto}
  end

  # put with unknown type (when value is a variable) - check against protocol's expected type
  defp go({:put, :unknown, val, p} = proc, {:send, expected_ty, s} = proto, ctx) do
    if value?(val, expected_ty, ctx), do: keep(go(p, s, ctx)), else: {:no, proc, proto}
  end

  defp go({:get, ty, name, p}, {:recv, ty, s}, ctx) do
    # Add variable binding to context (anonymous _ doesn't add)
    new_ctx = if name == :_, do: ctx, else: Map.put(ctx, name, ty)
    keep(go(p, s, new_ctx))
  end

  defp go({:pick0, p}, {:choose, s, _}, ctx), do: keep(go(p, s, ctx))
  defp go({:pick1, p}, {:choose, _, t}, ctx), do: keep(go(p, t, ctx))

  defp go({:cover, p, q}, {:branch, s, t}, ctx) do
    case go(p, s, ctx) do
      :ok -> keep(go(q, t, ctx))
      no -> no
    end
  end

  defp go(p, s, _ctx), do: {:no, p, s}

  defp keep(:ok), do: :ok
  defp keep({:no, _, _} = no), do: no

  defp value?({:nat, n}, :nat, _ctx) when is_integer(n) and n >= 0, do: true
  defp value?(bit, :bit, _ctx) when bit in [:b0, :b1], do: true
  defp value?(:tt, :unit, _ctx), do: true
  defp value?({:tup, a, b}, {:pair, ta, tb}, ctx), do: value?(a, ta, ctx) and value?(b, tb, ctx)

  defp value?({:rec, vals}, {:rec, fields}, ctx) when is_list(vals) and is_list(fields) do
    length(vals) == length(fields) and
      Enum.all?(fields, fn {name, ty} ->
        case List.keyfind(vals, name, 0) do
          {^name, val} -> value?(val, ty, ctx)
          _ -> false
        end
      end)
  end

  # Check that a variable has the expected type in the context
  defp value?({:var, name}, expected_ty, ctx) do
    case Map.get(ctx, name) do
      ^expected_ty -> true
      _ -> false
    end
  end

  defp value?(_, _, _ctx), do: false

  def show_proc(:done), do: "done"
  def show_proc(:stop), do: "stop"
  def show_proc({:put, _ty, val, p}), do: "put #{show_val(val)} #{paren_proc(p)}"
  def show_proc({:get, ty, :_, p}), do: "get #{show_pay_atom(ty)} #{paren_proc(p)}"
  def show_proc({:get, ty, name, p}), do: "get (#{name} : #{show_pay_atom(ty)}) #{paren_proc(p)}"
  def show_proc({:pick0, p}), do: "pick0 #{paren_proc(p)}"
  def show_proc({:pick1, p}), do: "pick1 #{paren_proc(p)}"
  def show_proc({:cover, p, q}), do: "cover #{paren_proc(p)} #{paren_proc(q)}"

  defp show_val({:var, name}), do: "#{name}"
  defp show_val({:nat, n}), do: "#{n}"
  defp show_val(:b0), do: "b0"
  defp show_val(:b1), do: "b1"
  defp show_val(:tt), do: "tt"
  defp show_val({:tup, a, b}), do: "(#{show_val(a)}, #{show_val(b)})"

  defp show_val({:rec, []}) do
    "{}"
  end

  defp show_val({:rec, fields}) when is_list(fields) do
    inner = Enum.map_join(fields, ", ", fn {name, val} -> "#{name} = #{show_val(val)}" end)
    "{#{inner}}"
  end

  def show_proto(:end), do: "end"
  def show_proto({:send, ty, s}), do: "send #{show_pay_atom(ty)} #{paren_proto(s)}"
  def show_proto({:recv, ty, s}), do: "recv #{show_pay_atom(ty)} #{paren_proto(s)}"
  def show_proto({:choose, s, t}), do: "choose #{paren_proto(s)} #{paren_proto(t)}"
  def show_proto({:branch, s, t}), do: "branch #{paren_proto(s)} #{paren_proto(t)}"

  defp show_pay(:nat), do: "Nat"
  defp show_pay(:bit), do: "Bit"
  defp show_pay(:unit), do: "Unit"
  defp show_pay({:pair, a, b}), do: "#{show_pay_atom(a)} * #{show_pay_atom(b)}"
  defp show_pay({:rec, []}), do: "{}"

  defp show_pay({:rec, fields}) do
    inner = Enum.map_join(fields, ", ", fn {name, ty} -> "#{name} : #{show_pay(ty)}" end)
    "{#{inner}}"
  end

  defp show_pay_atom({:pair, _, _} = ty), do: "(#{show_pay(ty)})"
  defp show_pay_atom(ty), do: show_pay(ty)

  defp paren_proc(p) when is_atom(p), do: show_proc(p)
  defp paren_proc(p), do: "(#{show_proc(p)})"

  defp paren_proto(:end), do: "end"
  defp paren_proto(s), do: "(#{show_proto(s)})"
end

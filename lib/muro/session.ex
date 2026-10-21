defmodule Muro.Session do
  @moduledoc """
  The Elixir mirror of `decide` and `finishes` in `agda/Muro/Session.agda`.

  A protocol is spec. A conformance derivation is evidence. `stop`
  conforms to every protocol (`abandon`). The continuation after a
  bit is that bit's branch. `finishes/1` is `:yes` when every leaf is
  `done`. `skel/1` is the process as actions. `dual/1` is the other
  end: `send` swaps with `recv`, and `choose` swaps with `branch`.
  """

  @doc """
  The other end of a protocol. Mirrors `dual` in `agda/Muro/Dual.agda`.

  `send` swaps with `recv`. `choose` swaps with `branch`. Both
  continuations dualise. The bit stays the selector.
  """
  def dual(:end), do: :end
  def dual({:send, s, t}), do: {:recv, dual(s), dual(t)}
  def dual({:recv, s, t}), do: {:send, dual(s), dual(t)}
  def dual({:choose, s, t}), do: {:branch, dual(s), dual(t)}
  def dual({:branch, s, t}), do: {:choose, dual(s), dual(t)}

  @doc """
  The actions of a process. Mirrors `skel` in `agda/Muro/Session.agda`.
  """
  def skel(proc), do: skel_go(proc)

  # skel done = finish
  defp skel_go(:done), do: :finish

  # skel stop = leave
  defp skel_go(:stop), do: :leave

  # skel (put b P) = say b (skel P)
  defp skel_go({:put, bit, p}), do: {:say, bit, skel_go(p)}

  # skel (get b P) = hear b (skel P)
  defp skel_go({:get, bit, p}), do: {:hear, bit, skel_go(p)}

  # skel (pick0 P) = choose b0 (skel P)
  defp skel_go({:pick0, p}), do: {:choose, :b0, skel_go(p)}

  # skel (pick1 P) = choose b1 (skel P)
  defp skel_go({:pick1, p}), do: {:choose, :b1, skel_go(p)}

  # skel (cover P Q) = offer (skel P) (skel Q)
  defp skel_go({:cover, p, q}), do: {:offer, skel_go(p), skel_go(q)}

  @doc """
  `:yes` when `finishes` returns `ends`. `stop` is `:no`.
  Mirrors `finishes` in `agda/Muro/Session.agda`.
  """
  def finishes(proc), do: finishes_go(proc)

  # finishes done = ends ends-done
  defp finishes_go(:done), do: :yes

  # finishes stop = leaves (λ ())
  defp finishes_go(:stop), do: :no

  # finishes (put _ P) = step-put (finishes P)
  defp finishes_go({:put, _, p}), do: finishes_go(p)

  # finishes (get _ P) = step-get (finishes P)
  defp finishes_go({:get, _, p}), do: finishes_go(p)

  # finishes (pick0 P) = step-pick0 (finishes P)
  defp finishes_go({:pick0, p}), do: finishes_go(p)

  # finishes (pick1 P) = step-pick1 (finishes P)
  defp finishes_go({:pick1, p}), do: finishes_go(p)

  # finishes (cover P Q) = step-cover (finishes P) (finishes Q)
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
    case go(proc, proto) do
      :ok -> :ok
      {:no, p, s} -> {:error, "#{show_proc(p)} does not conform to #{show_proto(s)}"}
    end
  end

  # decide done end = yes done-end
  defp go(:done, :end), do: :ok

  # decide stop _ = yes abandon
  defp go(:stop, _), do: :ok

  # decide (put b0 P) (send S _) = on0 (decide P S)
  defp go({:put, :b0, p}, {:send, s, _}), do: keep(go(p, s))

  # decide (put b1 P) (send _ T) = on1 (decide P T)
  defp go({:put, :b1, p}, {:send, _, t}), do: keep(go(p, t))

  # decide (get b0 P) (recv S _) = in0 (decide P S)
  defp go({:get, :b0, p}, {:recv, s, _}), do: keep(go(p, s))

  # decide (get b1 P) (recv _ T) = in1 (decide P T)
  defp go({:get, :b1, p}, {:recv, _, t}), do: keep(go(p, t))

  # decide (pick0 P) (choose S _) = at0 (decide P S)
  defp go({:pick0, p}, {:choose, s, _}), do: keep(go(p, s))

  # decide (pick1 P) (choose _ T) = at1 (decide P T)
  defp go({:pick1, p}, {:choose, _, t}), do: keep(go(p, t))

  # decide (cover P Q) (branch S T) = both-of (decide P S) (decide Q T)
  defp go({:cover, p, q}, {:branch, s, t}) do
    case go(p, s) do
      :ok -> keep(go(q, t))
      no -> no
    end
  end

  defp go(p, s), do: {:no, p, s}

  defp keep(:ok), do: :ok
  defp keep({:no, _, _} = no), do: no

  defp show_bit(:b0), do: "b0"
  defp show_bit(:b1), do: "b1"

  defp show_proc(:done), do: "done"
  defp show_proc(:stop), do: "stop"
  defp show_proc({:put, bit, p}), do: "put #{show_bit(bit)} #{paren_proc(p)}"
  defp show_proc({:get, bit, p}), do: "get #{show_bit(bit)} #{paren_proc(p)}"
  defp show_proc({:pick0, p}), do: "pick0 #{paren_proc(p)}"
  defp show_proc({:pick1, p}), do: "pick1 #{paren_proc(p)}"
  defp show_proc({:cover, p, q}), do: "cover #{paren_proc(p)} #{paren_proc(q)}"

  defp show_proto(:end), do: "end"
  defp show_proto({:send, s, t}), do: "send #{paren_proto(s)} #{paren_proto(t)}"
  defp show_proto({:recv, s, t}), do: "recv #{paren_proto(s)} #{paren_proto(t)}"
  defp show_proto({:choose, s, t}), do: "choose #{paren_proto(s)} #{paren_proto(t)}"
  defp show_proto({:branch, s, t}), do: "branch #{paren_proto(s)} #{paren_proto(t)}"

  defp paren_proc(p) when is_atom(p), do: show_proc(p)
  defp paren_proc(p), do: "(#{show_proc(p)})"

  defp paren_proto(:end), do: "end"
  defp paren_proto(s), do: "(#{show_proto(s)})"
end

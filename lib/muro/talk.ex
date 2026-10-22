defmodule Muro.Talk do
  @moduledoc """
  The Elixir mirror of `seen` in `agda/Muro/Talk.agda`.

  A description is already expanded: a name is the tree it stands
  for. `seen/3` is the session one party has with another. The sender's
  session is `send` or `choose`. The receiver's session is `recv` or
  `branch`. A party off that channel has a session when both
  continuations are the same description. The first continuation is
  `b0` and the second is `b1`.
  """

  @doc """
  The session `p` has with `q` in `talk`. Otherwise `p` has no session with `q`.
  """
  def seen(p, q, talk) do
    case seen_go(p, q, talk) do
      :none -> {:error, "#{p} has no session with #{q}"}
      {:ok, proto} -> {:ok, proto}
    end
  end

  # seen p q over = just end
  defp seen_go(_p, _q, :over), do: {:ok, :end}

  # seen p q (say a b t0 t1) = join said (hear p q a b) (talk≟ t0 t1) …
  defp seen_go(p, q, {:say, a, b, t0, t1}) do
    join(:said, hear(p, q, a, b), t0 == t1, seen_go(p, q, t0), seen_go(p, q, t1))
  end

  # seen p q (offer a b t0 t1) = join offered (hear p q a b) (talk≟ t0 t1) …
  defp seen_go(p, q, {:offer, a, b, t0, t1}) do
    join(:offered, hear(p, q, a, b), t0 == t1, seen_go(p, q, t0), seen_go(p, q, t1))
  end

  # a ≡ b, or the channel is a party with itself: bad.
  # The sender is out. The receiver is got. Anyone else is off.
  defp hear(p, q, a, b) do
    cond do
      a == b -> :bad
      p == q -> :bad
      p == a and q == b -> :out
      p == b and q == a -> :got
      true -> :off
    end
  end

  # join _ bad _ _ _ = nothing
  defp join(_kind, :bad, _eq, _m, _n), do: :none

  # join _ off (no _) _ _ = nothing
  defp join(_kind, :off, false, _m, _n), do: :none

  # join _ off (yes _) m _ = m
  defp join(_kind, :off, true, m, _n), do: m

  # join said out _ m n = both send m n
  defp join(:said, :out, _eq, m, n), do: both(:send, m, n)

  # join said got _ m n = both recv m n
  defp join(:said, :got, _eq, m, n), do: both(:recv, m, n)

  # join offered out _ m n = both choose m n
  defp join(:offered, :out, _eq, m, n), do: both(:choose, m, n)

  # join offered got _ m n = both branch m n
  defp join(:offered, :got, _eq, m, n), do: both(:branch, m, n)

  defp both(_ctor, :none, _n), do: :none
  defp both(_ctor, _m, :none), do: :none
  defp both(ctor, {:ok, s}, {:ok, t}), do: {:ok, {ctor, s, t}}
end

defmodule Muro.Talk do
  @moduledoc """
  The Elixir mirror of `seen` in `agda/Muro/Talk.agda`.

  A description is already expanded: a name is the tree it stands
  for. `seen/3` is the session one party has with another. `say`
  names one payload type and one continuation. The sender's session
  is `send` of that type. The receiver's session is `recv` of that
  type. A party off that `say` has the continuation's session.
  `offer` still has two arms. A party off an `offer` has a session
  when both arms are the same description. The sender's session is
  then `choose`, and the receiver's is `branch`.
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

  defp seen_go(_p, _q, :over), do: {:ok, :end}

  defp seen_go(p, q, {:say, a, b, ty, t}) do
    said(hear(p, q, a, b), ty, seen_go(p, q, t))
  end

  defp seen_go(p, q, {:offer, a, b, t0, t1}) do
    join(hear(p, q, a, b), t0 == t1, seen_go(p, q, t0), seen_go(p, q, t1))
  end

  defp hear(p, q, a, b) do
    cond do
      a == b -> :bad
      p == q -> :bad
      p == a and q == b -> :out
      p == b and q == a -> :got
      true -> :off
    end
  end

  defp said(:bad, _ty, _m), do: :none
  defp said(:off, _ty, m), do: m
  defp said(:out, _ty, :none), do: :none
  defp said(:out, ty, {:ok, s}), do: {:ok, {:send, ty, s}}
  defp said(:got, _ty, :none), do: :none
  defp said(:got, ty, {:ok, s}), do: {:ok, {:recv, ty, s}}

  defp join(:bad, _eq, _m, _n), do: :none
  defp join(:off, false, _m, _n), do: :none
  defp join(:off, true, m, _n), do: m
  defp join(:out, _eq, m, n), do: both(:choose, m, n)
  defp join(:got, _eq, m, n), do: both(:branch, m, n)

  defp both(_ctor, :none, _n), do: :none
  defp both(_ctor, _m, :none), do: :none
  defp both(ctor, {:ok, s}, {:ok, t}), do: {:ok, {ctor, s, t}}
end

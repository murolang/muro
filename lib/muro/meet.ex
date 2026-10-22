defmodule Muro.Meet do
  @moduledoc """
  The Elixir mirror of `decide` in `agda/Muro/Meet.agda`.

  A send meets a receive of the same bit, and the continuations meet.
  A choice meets the arm that was offered. Both ends close, or both
  abandon. `meets/2` is `:ok` when `decide` returns `yes`. Otherwise
  the pair where it returns `no`.
  """

  @doc """
  `:ok` when the two processes meet. Otherwise the pair where `decide` returns `no`.
  """
  def meets(p, q) do
    case go(p, q) do
      :ok -> :ok
      {:no, a, b} -> {:error, "#{show_proc(a)} does not meet #{show_proc(b)}"}
    end
  end

  # decide done done = yes done-done
  defp go(:done, :done), do: :ok

  # decide stop stop = yes stop-stop
  defp go(:stop, :stop), do: :ok

  # decide (put b P) (get b Q) = put-get-yes (decide P Q)
  defp go({:put, b, p}, {:get, b, q}), do: keep(go(p, q))

  # decide (get b P) (put b Q) = get-put-yes (decide P Q)
  defp go({:get, b, p}, {:put, b, q}), do: keep(go(p, q))

  # decide (pick0 P) (cover Q _) = pick0-yes (decide P Q)
  defp go({:pick0, p}, {:cover, q, _}), do: keep(go(p, q))

  # decide (pick1 P) (cover _ R) = pick1-yes (decide P R)
  defp go({:pick1, p}, {:cover, _, r}), do: keep(go(p, r))

  # decide (cover P _) (pick0 R) = cover0-yes (decide P R)
  defp go({:cover, p, _}, {:pick0, r}), do: keep(go(p, r))

  # decide (cover _ Q) (pick1 R) = cover1-yes (decide Q R)
  defp go({:cover, _, q}, {:pick1, r}), do: keep(go(q, r))

  defp go(p, q), do: {:no, p, q}

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

  defp paren_proc(p) when is_atom(p), do: show_proc(p)
  defp paren_proc(p), do: "(#{show_proc(p)})"
end

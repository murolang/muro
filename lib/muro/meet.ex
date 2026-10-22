defmodule Muro.Meet do
  @moduledoc """
  The Elixir mirror of `decide` in `agda/Muro/Meet.agda`.

  A send meets a receive of the same payload type, and the
  continuations meet. The values need not be the same term. A choice
  meets the arm that was offered. Both ends close, or both abandon.
  `meets/2` is `:ok` when `decide` returns `yes`. Otherwise the pair
  where it returns `no`.
  """

  @doc """
  `:ok` when the two processes meet. Otherwise the pair where `decide` returns `no`.
  """
  def meets(p, q) do
    case go(p, q) do
      :ok ->
        :ok

      {:no, a, b} ->
        {:error, "#{Muro.Session.show_proc(a)} does not meet #{Muro.Session.show_proc(b)}"}
    end
  end

  defp go(:done, :done), do: :ok
  defp go(:stop, :stop), do: :ok

  defp go({:put, ty, _, p}, {:get, ty, q}), do: keep(go(p, q))
  defp go({:get, ty, p}, {:put, ty, _, q}), do: keep(go(p, q))

  defp go({:pick0, p}, {:cover, q, _}), do: keep(go(p, q))
  defp go({:pick1, p}, {:cover, _, r}), do: keep(go(p, r))
  defp go({:cover, p, _}, {:pick0, r}), do: keep(go(p, r))
  defp go({:cover, _, q}, {:pick1, r}), do: keep(go(q, r))

  defp go(p, q), do: {:no, p, q}

  defp keep(:ok), do: :ok
  defp keep({:no, _, _} = no), do: no
end

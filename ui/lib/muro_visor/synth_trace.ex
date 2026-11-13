defmodule MuroVisor.SynthTrace do
  @moduledoc false

  @doc """
  Read one synthesis report.

  The object `mix muro.synth --json` prints is enough: `status`,
  `program`, `versions`, `cex`, `note`, and `certificate`. `versions`
  becomes one round per size. The carriers in `cex` light on the last
  round, which is the round the report names.

  A later search may add `rounds` and `states` without renaming those
  keys. `rounds` is `[%{"round" => n, "versions" => size, "cex" =>
  [state]}]`. `states` is `[%{"name" => state, "status" => "ranked" |
  "unsettled", "certificate" => name | nil}]`. When `states` is absent,
  a `certified` report ranks every state of the book under
  `certificate`, and any other status leaves those states unsettled.
  """
  def load(path) when is_binary(path) do
    case File.read(path) do
      {:ok, body} -> decode(body)
      {:error, :enoent} -> {:error, "no such trace"}
      {:error, reason} -> {:error, "trace: #{inspect(reason)}"}
    end
  end

  @doc false
  def normalize(map) when is_map(map) do
    versions = sizes(Map.get(map, "versions"))
    cex = carriers(Map.get(map, "cex"))
    rounds = rounds(Map.get(map, "rounds"), versions, cex)

    %{
      status: string_or_nil(Map.get(map, "status")),
      program: program(Map.get(map, "program")),
      certificate: string_or_nil(Map.get(map, "certificate")),
      note: string_or_nil(Map.get(map, "note")),
      versions: versions,
      rounds: rounds,
      states: states(Map.get(map, "states")),
      cex: cex
    }
  end

  defp decode(body) do
    case Jason.decode(body) do
      {:ok, map} when is_map(map) -> {:ok, normalize(map)}
      _ -> {:error, "the trace is not a JSON object"}
    end
  end

  defp rounds(list, _versions, _cex) when is_list(list) and list != [] do
    list
    |> Enum.with_index(1)
    |> Enum.map(fn {round, index} ->
      %{
        n: round_n(round, index),
        versions: round_size(round),
        cex: carriers(round_cex(round))
      }
    end)
  end

  defp rounds(_missing, versions, cex) do
    case versions do
      [] ->
        [%{n: 1, versions: nil, cex: cex}]

      sizes ->
        last = length(sizes)

        sizes
        |> Enum.with_index(1)
        |> Enum.map(fn {size, index} ->
          %{n: index, versions: size, cex: if(index == last, do: cex, else: [])}
        end)
    end
  end

  defp round_n(%{"round" => n}, _index) when is_integer(n) and n > 0, do: n
  defp round_n(_round, index), do: index

  defp round_size(%{"versions" => n}) when is_integer(n) and n >= 0, do: n
  defp round_size(_round), do: nil

  defp round_cex(%{"cex" => cex}), do: cex
  defp round_cex(_round), do: []

  defp states(list) when is_list(list) do
    Enum.flat_map(list, fn
      %{"name" => name} = state when is_binary(name) ->
        [
          %{
            name: name,
            status: state_status(Map.get(state, "status")),
            certificate: string_or_nil(Map.get(state, "certificate"))
          }
        ]

      _ ->
        []
    end)
  end

  defp states(_missing), do: nil

  defp state_status("ranked"), do: "ranked"
  defp state_status("unsettled"), do: "unsettled"
  defp state_status(_other), do: nil

  defp sizes(list) when is_list(list) do
    Enum.flat_map(list, fn
      n when is_integer(n) and n >= 0 -> [n]
      _ -> []
    end)
  end

  defp sizes(_other), do: []

  defp carriers(list) when is_list(list) do
    list
    |> Enum.flat_map(fn
      %{"carrier" => name} when is_binary(name) and name != "" -> [name]
      name when is_binary(name) and name != "" -> [name]
      _ -> []
    end)
    |> Enum.uniq()
  end

  defp carriers(_other), do: []

  defp program(nil), do: nil
  defp program(text) when is_binary(text) and text != "", do: text
  defp program(text) when is_binary(text), do: nil

  defp program(list) when is_list(list) do
    list
    |> Enum.filter(&is_binary/1)
    |> case do
      [] -> nil
      lines -> Enum.join(lines, "\n")
    end
  end

  defp program(_other), do: nil

  defp string_or_nil(text) when is_binary(text) and text != "", do: text
  defp string_or_nil(_other), do: nil
end

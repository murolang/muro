defmodule Muro.CLI.Skills do
  @moduledoc false

  @doc false
  def run(["add"]) do
    case Muro.Skills.add(Muro.Manifest.root()) do
      {:ok, lines} -> {:ok, Muro.CLI.join_lines(lines), ""}
      {:error, message} -> {:raise, "", message}
    end
  end

  def run(_args) do
    {:raise, "", "usage: muro skills add"}
  end
end

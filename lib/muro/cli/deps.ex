defmodule Muro.CLI.Deps do
  @moduledoc false

  @doc false
  def run(args) do
    {_opts, rest, invalid} = OptionParser.parse(args, strict: [])

    if invalid != [] or rest != [] do
      {:raise, "", "usage: mix muro.deps.get"}
    else
      case Muro.Deps.get(Muro.Manifest.root()) do
        {:ok, lines} -> {:ok, Muro.CLI.join_lines(lines), ""}
        {:error, message} -> {:raise, "", message}
      end
    end
  end
end

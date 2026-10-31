defmodule Muro.CLI.Gen do
  @moduledoc false

  @switches [check: :boolean]

  @doc false
  def run(args) do
    {opts, rest, invalid} = OptionParser.parse(args, strict: @switches)

    cond do
      invalid != [] ->
        {:raise, "", "unknown option: #{inspect(invalid)}"}

      rest != [] ->
        {:raise, "", "usage: mix muro.gen [--check]"}

      true ->
        go(opts[:check] || false)
    end
  end

  defp go(check?) do
    root = Muro.Manifest.root()

    with {:ok, manifest} <- load(root),
         :ok <- pin(manifest) do
      running = Mix.Tasks.Muro.version()

      if check? do
        case Muro.Gen.check(manifest, root, running) do
          :ok -> {:ok, "ok\n", ""}
          {:error, message} -> {:raise, "", message}
        end
      else
        case Muro.Gen.generate(manifest, root, running) do
          {:ok, lines} -> {:ok, Muro.CLI.join_lines(lines), ""}
          {:error, message} -> {:raise, "", message}
        end
      end
    end
  end

  defp load(root) do
    case Muro.Manifest.load(root) do
      {:ok, manifest} -> {:ok, manifest}
      {:error, message} -> {:raise, "", message}
    end
  end

  defp pin(manifest) do
    case Muro.Manifest.version_pin(manifest.version, Mix.Tasks.Muro.version()) do
      :ok -> :ok
      {:error, message} -> {:raise, "", message}
    end
  end
end

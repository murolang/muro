defmodule Muro.CLI.Init do
  @moduledoc false

  @doc false
  def run_mix(args) do
    {opts, rest, invalid} = OptionParser.parse(args, strict: [ci: :string])

    cond do
      invalid != [] ->
        {:raise, "", "unknown option: #{inspect(invalid)}"}

      rest != [] ->
        {:raise, "", "usage: mix muro.init [--ci github]"}

      true ->
        case ci_value(Keyword.get(opts, :ci)) do
          {:ok, ci} ->
            case Muro.Init.write(Muro.Manifest.root(), Mix.Tasks.Muro.version(), ci) do
              {:ok, lines, note} -> {:ok, created(lines, note), ""}
              {:error, message} -> {:raise, "", message}
            end

          {:error, message} ->
            {:raise, "", message}
        end
    end
  end

  @doc false
  def run(args) do
    switches = [ci: :string, backend: :string, cargo_metadata: :boolean]
    {opts, rest, invalid} = OptionParser.parse(args, strict: switches)

    cond do
      invalid != [] ->
        {:raise, "", "unknown option: #{inspect(invalid)}"}

      rest != [] ->
        {:raise, "", "usage: mix muro.init [--ci github]"}

      true ->
        with {:ok, ci} <- ci_value(Keyword.get(opts, :ci)),
             {:ok, backend} <- backend_value(Keyword.get(opts, :backend)) do
          scaffold(ci, backend, Keyword.get(opts, :cargo_metadata, false))
        else
          {:error, message} -> {:raise, "", message}
        end
    end
  end

  defp scaffold(ci, backend, cargo?) do
    opts = [ci: ci, backend: backend, cargo_metadata: cargo?]

    case Muro.Init.scaffold(Muro.Manifest.root(), Mix.Tasks.Muro.version(), opts) do
      {:ok, lines, note} -> {:ok, created(lines, note), ""}
      {:diff, text} -> {:ok, text, ""}
      {:error, message} -> {:raise, "", message}
    end
  end

  defp created(lines, note) do
    Muro.CLI.join_lines(lines ++ [String.trim_trailing(note)])
  end

  defp ci_value(nil), do: {:ok, nil}
  defp ci_value("github"), do: {:ok, :github}
  defp ci_value(other), do: {:error, "unknown --ci #{other}; expected github"}

  defp backend_value(nil), do: {:ok, nil}

  defp backend_value(name) when name in ~w(elixir c rust asm fsm exunit) do
    {:ok, String.to_atom(name)}
  end

  defp backend_value(other), do: {:error, "unknown backend: #{other}"}
end

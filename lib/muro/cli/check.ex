defmodule Muro.CLI.Check do
  @moduledoc false

  @switches [fuel: :integer]

  @doc false
  def run(args) do
    version = "Muro v#{Mix.Tasks.Muro.version()}\n"
    {opts, paths, invalid} = OptionParser.parse(args, strict: @switches)

    cond do
      invalid != [] ->
        {:raise, version, "unknown option: #{inspect(invalid)}"}

      Keyword.get(opts, :fuel, Muro.Check.default_fuel()) <= 0 ->
        {:raise, version, "--fuel must be a positive integer"}

      true ->
        fuel = Keyword.get(opts, :fuel, Muro.Check.default_fuel())
        check(paths, fuel, version)
    end
  end

  defp check([], fuel, version) do
    finish(Muro.Check.check_sig(Muro.Example.book(), fuel: fuel), version)
  end

  defp check([path], fuel, version) do
    finish(Muro.conforms(path, fuel: fuel), version)
  end

  defp check(_paths, _fuel, version) do
    {:raise, version, "expected at most one path"}
  end

  defp finish(:ok, version) do
    {:ok, version <> success(), ""}
  end

  defp finish({:ok, lines}, version) do
    {:ok, version <> success() <> Muro.CLI.join_lines(lines), ""}
  end

  defp finish({:error, message}, version) do
    {:raise, version, message}
  end

  defp success, do: "All terms check. Evidence never becomes a run.\n"
end

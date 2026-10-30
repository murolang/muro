defmodule Muro.CLI do
  @moduledoc false

  @commands ["check", "emit", "gen", "init", "skills add", "deps.get", "mutate"]

  @doc """
  Entry point for the self-contained executable.

  Returns the process status. It does not halt.
  """
  def main(args) when is_list(args) do
    args = Enum.map(args, &to_string/1)

    try do
      args |> dispatch() |> present()
    rescue
      error in Mix.Error ->
        IO.write(:stderr, ensure_nl(error.message))
        1
    end
  end

  @doc false
  def join_lines(lines) when is_list(lines) do
    IO.iodata_to_binary(Enum.map(lines, &[to_string(&1), ?\n]))
  end

  @doc false
  def ensure_nl(text) when is_binary(text) do
    if String.ends_with?(text, "\n"), do: text, else: text <> "\n"
  end

  defp dispatch(["--version"]), do: version_result()
  defp dispatch(["-v"]), do: version_result()
  defp dispatch(["--help"]), do: {:ok, help_text(), ""}
  defp dispatch(["-h"]), do: {:ok, help_text(), ""}
  defp dispatch(["help"]), do: {:ok, help_text(), ""}
  defp dispatch([]), do: {:ok, bare(), ""}
  defp dispatch(["check" | rest]), do: Muro.CLI.Check.run(rest)
  defp dispatch(["emit" | rest]), do: Muro.CLI.Emit.run(rest)
  defp dispatch(["gen" | rest]), do: Muro.CLI.Gen.run(rest)
  defp dispatch(["init" | rest]), do: Muro.CLI.Init.run(rest)
  defp dispatch(["skills" | rest]), do: Muro.CLI.Skills.run(rest)
  defp dispatch(["deps.get" | rest]), do: Muro.CLI.Deps.run(rest)
  defp dispatch(["mutate" | rest]), do: Muro.CLI.Mutate.run(rest)
  defp dispatch(_other), do: {:raise, "", usage()}

  defp version_result, do: {:ok, "Muro v#{Mix.Tasks.Muro.version()}\n", ""}

  defp bare do
    names = Enum.map_join(@commands, "  ", &("muro " <> &1))
    "Muro v#{Mix.Tasks.Muro.version()}\n" <> names <> "\n"
  end

  defp usage do
    "usage: muro [--version] <check|emit|gen|init|skills|deps.get|mutate> ..."
  end

  defp help_text do
    """
    muro — check, emit, and commit Muro modules

    The executable is self-contained. It carries its own Erlang runtime.
    It does not compile or start a host application.

    #{usage()}

    muro check [path.muro] [--fuel N]
    muro emit path.muro [--backend elixir|c|rust|asm|otp|fsm|exunit] [--node NAME] [--imports]
    muro gen [--check]
    muro init [--ci github] [--backend BACKEND] [--cargo-metadata]
    muro skills add
    muro deps.get
    muro mutate path.muro [--only NAME] [--json] [--fuel N]
    muro --version
    """
  end

  defp present({:ok, stdout, stderr}) do
    IO.write(stdout)
    IO.write(:stderr, stderr)
    0
  end

  defp present({:raise, stdout, message}) do
    IO.write(stdout)
    IO.write(:stderr, ensure_nl(message))
    1
  end

  defp present({:exit, code, stdout, lines}) when is_list(lines) do
    IO.write(stdout)
    Enum.each(lines, &IO.puts(:stderr, &1))
    code
  end
end

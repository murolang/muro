defmodule Muro.CLI.Output do
  @moduledoc false

  @doc """
  Present a CLI result through Mix.

  Success writes stdout once, after the application banner Mix prints
  on the first shell line. A refusal raises `Mix.Error` with the same
  message the task used to raise. `{:exit, code, _, lines}` prints each
  line with `Mix.shell().error/1` and exits with `code`.
  """
  def mix({:ok, stdout, stderr}) do
    write_stdout(stdout)
    IO.write(:stderr, stderr)
    :ok
  end

  def mix({:raise, stdout, message}) do
    write_stdout(stdout)
    Mix.raise(message)
  end

  def mix({:exit, code, stdout, lines}) when is_list(lines) do
    write_stdout(stdout)
    Enum.each(lines, fn line -> Mix.shell().error(line) end)
    exit({:shutdown, code})
  end

  defp write_stdout(""), do: :ok

  defp write_stdout(stdout) do
    Mix.Shell.IO.print_app()
    IO.write(stdout)
  end
end

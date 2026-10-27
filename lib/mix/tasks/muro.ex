defmodule Mix.Tasks.Muro do
  use Mix.Task

  @shortdoc "Print the muro version and the muro tasks"

  @moduledoc """
  Print the version of the muro that is running, and the muro tasks.

      mix muro
      mix muro --version
      mix muro -v

  The version comes from the application spec, printed as `Muro v` and
  that version. With no arguments, the same line is followed by the muro
  tasks on one line.

  Inside a Mix project, `mix muro.check` and `mix muro.emit` start that
  project's applications. Outside a project, they load and start `:muro`
  from the installed archive.

  When a project depends on muro and an archive is also installed, Mix
  uses the project's copy. This version line is the copy that ran.
  """

  @tasks [Mix.Tasks.Muro.Check, Mix.Tasks.Muro.Emit]

  def run([]), do: report()

  def run([flag]) when flag in ["--version", "-v"] do
    Mix.shell().info(version_line())
  end

  def run(_args) do
    Mix.raise("usage: mix muro [--version]")
  end

  @doc false
  def ensure_started do
    case Mix.Project.get() do
      nil -> start_archive()
      _project -> Mix.Task.run("app.start")
    end
  end

  @doc false
  def version do
    ensure_loaded!()

    case Application.spec(:muro, :vsn) do
      vsn when is_list(vsn) -> List.to_string(vsn)
      other -> Mix.raise("could not read the muro version (#{inspect(other)})")
    end
  end

  defp report do
    Mix.shell().info(version_line())
    Mix.shell().info(task_line())
  end

  defp version_line, do: "Muro v#{version()}"

  defp task_line do
    Enum.map_join(@tasks, "  ", fn module -> "mix " <> Mix.Task.task_name(module) end)
  end

  defp start_archive do
    case Application.ensure_all_started(:muro) do
      {:ok, _apps} -> :ok
      {:error, reason} -> Mix.raise("could not start :muro (#{inspect(reason)})")
    end
  end

  defp ensure_loaded! do
    case Application.load(:muro) do
      :ok -> :ok
      {:error, {:already_loaded, _app}} -> :ok
      {:error, reason} -> Mix.raise("could not load :muro (#{inspect(reason)})")
    end
  end
end

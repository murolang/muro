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

  Inside a project that depends on muro, or whose application is
  `:muro`, the tasks start that project's applications and use the
  project's copy. Inside any other project, or outside a project, they
  load and start `:muro` from the installed archive. The host is neither
  compiled nor started.

  `mix muro.check`, `mix muro.mutate`, `mix muro.emit`, `mix muro.gen`,
  `mix muro.init`, and `mix muro.deps.get` call `ensure_started/0` before
  they run.
  A task added later calls it too, and follows the same rule.
  The version line is the copy that ran.

  A script run with `mix run --no-start` does not see the archive.
  Archives are on the code path for Mix tasks.
  """

  @tasks [
    Mix.Tasks.Muro.Check,
    Mix.Tasks.Muro.Mutate,
    Mix.Tasks.Muro.Emit,
    Mix.Tasks.Muro.Gen,
    Mix.Tasks.Muro.Init,
    Mix.Tasks.Muro.Deps.Get
  ]

  def run([]), do: report()

  def run([flag]) when flag in ["--version", "-v"] do
    Mix.shell().info(version_line())
  end

  def run(_args) do
    Mix.raise("usage: mix muro [--version]")
  end

  @doc false
  def ensure_started do
    # Taken from the task that is running, before anything changes the
    # code path. `app.start` prunes paths that are not project deps.
    ebin = running_ebin()

    if project_uses_muro?() do
      Mix.Task.run("app.start")
    else
      prepend_ebin(ebin)
      start_archive()
    end
  end

  @doc false
  def uses_muro?(config) when is_list(config) do
    config[:app] == :muro or muro_dep?(config[:deps])
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

  defp project_uses_muro? do
    case Mix.Project.get() do
      nil -> false
      _project -> uses_muro?(Mix.Project.config())
    end
  end

  defp muro_dep?(deps) when is_list(deps) do
    Enum.any?(deps, &muro_dep_entry?/1)
  end

  defp muro_dep?(_deps), do: false

  defp muro_dep_entry?({:muro, _requirement}), do: true
  defp muro_dep_entry?({:muro, _requirement, _opts}), do: true
  defp muro_dep_entry?(_other), do: false

  defp start_archive do
    case Application.ensure_all_started(:muro) do
      {:ok, _apps} -> :ok
      {:error, reason} -> Mix.raise("could not start :muro (#{inspect(reason)})")
    end
  end

  defp ensure_loaded! do
    # Same ebin as ensure_started/0. `mix muro --version` loads the app
    # without starting the host, and still has to find muro.app.
    unless project_uses_muro?() do
      prepend_ebin(running_ebin())
    end

    case Application.load(:muro) do
      :ok -> :ok
      {:error, {:already_loaded, _app}} -> :ok
      {:error, reason} -> Mix.raise("could not load :muro (#{inspect(reason)})")
    end
  end

  defp running_ebin do
    case :code.which(Mix.Tasks.Muro) do
      path when is_list(path) ->
        path |> List.to_string() |> Path.dirname()

      _other ->
        nil
    end
  end

  defp prepend_ebin(ebin) when is_binary(ebin) do
    Code.prepend_path(ebin)
    :ok
  end

  defp prepend_ebin(_ebin), do: :ok
end

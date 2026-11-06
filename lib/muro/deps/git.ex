defmodule Muro.Deps.Git do
  @moduledoc """
  Fetch one git dependency with the `git` CLI.

  `tag:` and a `ref:` that names a branch use
  `git clone --depth 1 --branch <name> -- <url> <dir>`. A `ref:` that
  is a commit (7 to 40 hex digits) uses `git init`, then
  `git fetch --depth 1 -- <url> <ref>`, then
  `git checkout --detach FETCH_HEAD`. A spec with no pin uses
  `git clone --depth 1 -- <url> <dir>`, so git checks out the remote's
  default branch. The branch name is `git rev-parse --abbrev-ref HEAD`
  in that clone. A detached `HEAD` falls back to
  `git ls-remote --symref <url> HEAD`. When the remote has no default
  branch, the error is `muro_deps entry <name>: remote has no default
  branch; add tag: or ref:`. `GIT_TERMINAL_PROMPT` is `0`. Arguments
  are passed to `System.cmd/3`, not through a shell. No credentials
  are added beyond what git itself does.

  The resolved commit is `git rev-parse HEAD`. The version label for
  a tag drops one leading `v` when the rest starts with a digit.
  A ref's version is `<ref>@<7 hex chars>`, or those 7 chars when the
  ref is itself a commit. A pin-free spec uses `<branch>@<7 hex chars>`.
  Only regular `.muro` files under the package root are kept. The
  `.git` directory is not copied.
  """

  alias Muro.Deps.Files

  @doc """
  `{:ok, fetched}` or `{:error, message}`. `git` is
  `System.find_executable("git")`; tests pass `nil` to check the
  missing-git message without changing `PATH`.
  """
  def fetch(dep, git \\ System.find_executable("git"))

  def fetch(_dep, nil) do
    {:error, "git is not on PATH; muro.lock and muro_deps/ are unchanged"}
  end

  def fetch(dep, git) when is_binary(git) do
    parent =
      Path.join(
        System.tmp_dir!(),
        "muro-git-" <> Integer.to_string(System.unique_integer([:positive]))
      )

    dest = Path.join(parent, "repo")

    try do
      with :ok <- File.mkdir_p(parent),
           {:ok, dep} <- checkout(dep, dest, git),
           {:ok, commit} <- rev_parse(dest, git),
           {:ok, files} <- read_files(dep, dest) do
        {:ok,
         %{
           version: version_label(dep, commit),
           resolved: {:git, commit},
           files: files
         }}
      else
        {:error, :no_default} ->
          {:error, "muro_deps entry #{dep.name}: remote has no default branch; add tag: or ref:"}

        {:error, msg} ->
          {:error, "#{dep.name}: #{msg}"}
      end
    after
      File.rm_rf(parent)
    end
  end

  @doc false
  def version_label(%{pin: {:tag, tag}}, _commit), do: tag_version(tag)

  def version_label(%{pin: {:ref, ref}}, commit) do
    short = String.slice(commit, 0, 7)

    if commit_ref?(ref) do
      short
    else
      ref <> "@" <> short
    end
  end

  def version_label(%{pin: :head, branch: branch}, commit) when is_binary(branch) do
    branch <> "@" <> String.slice(commit, 0, 7)
  end

  @doc false
  def branch_from_symref(output) when is_binary(output) do
    output
    |> String.split(["\r", "\n"], trim: true)
    |> Enum.find_value(:error, fn line ->
      case Regex.run(~r/\Aref:\s+refs\/heads\/(\S+)\s+HEAD\z/, String.trim(line)) do
        [_, branch] -> {:ok, branch}
        _ -> nil
      end
    end)
  end

  defp checkout(%{pin: {:tag, tag}, url: url} = dep, dest, git) do
    case clone_branch(git, url, tag, dest) do
      :ok -> {:ok, dep}
      {:error, _} = err -> err
    end
  end

  defp checkout(%{pin: {:ref, ref}, url: url} = dep, dest, git) do
    result =
      if commit_ref?(ref) do
        fetch_ref(git, url, ref, dest)
      else
        clone_branch(git, url, ref, dest)
      end

    case result do
      :ok -> {:ok, dep}
      {:error, _} = err -> err
    end
  end

  defp checkout(%{pin: :head, url: url} = dep, dest, git) do
    with :ok <- clone_default(git, url, dest),
         {:ok, branch} <- default_branch(git, url, dest) do
      {:ok, Map.put(dep, :branch, branch)}
    end
  end

  defp clone_default(git, url, dest) do
    case git(git, ["clone", "--depth", "1", "--", url, dest], []) do
      {:ok, _out} -> :ok
      {:error, msg} -> {:error, msg}
    end
  end

  defp clone_branch(git, url, branch, dest) do
    case git(git, ["clone", "--depth", "1", "--branch", branch, "--", url, dest], []) do
      {:ok, _out} -> :ok
      {:error, msg} -> {:error, msg}
    end
  end

  # No checked-out commit means the remote HEAD names nothing.
  # A detached checkout has a commit but no branch; the symref is the name.
  defp default_branch(git, url, dest) do
    case rev_parse(dest, git) do
      {:ok, _commit} ->
        case abbrev_head(dest, git) do
          {:ok, "HEAD"} -> remote_head_branch(git, url)
          {:ok, branch} -> {:ok, branch}
          :error -> remote_head_branch(git, url)
        end

      {:error, _msg} ->
        {:error, :no_default}
    end
  end

  defp abbrev_head(dest, git) do
    case git(git, ["rev-parse", "--abbrev-ref", "HEAD"], cd: dest) do
      {:ok, out} ->
        case out |> String.split(["\r", "\n"], trim: true) |> List.first() do
          nil -> :error
          name -> {:ok, String.trim(name)}
        end

      {:error, _} ->
        :error
    end
  end

  defp remote_head_branch(git, url) do
    case git(git, ["ls-remote", "--symref", "--", url, "HEAD"], []) do
      {:ok, out} ->
        case branch_from_symref(out) do
          {:ok, branch} -> {:ok, branch}
          :error -> {:error, :no_default}
        end

      {:error, _} ->
        {:error, :no_default}
    end
  end

  defp fetch_ref(git, url, ref, dest) do
    with :ok <- File.mkdir_p(dest),
         {:ok, _} <- git(git, ["init"], cd: dest),
         {:ok, _} <- git(git, ["fetch", "--depth", "1", "--", url, ref], cd: dest),
         {:ok, _} <- git(git, ["checkout", "--detach", "FETCH_HEAD"], cd: dest) do
      :ok
    else
      {:error, msg} -> {:error, msg}
    end
  end

  defp rev_parse(dest, git) do
    case git(git, ["rev-parse", "HEAD"], cd: dest) do
      {:ok, sha} ->
        sha = String.downcase(String.trim(sha))

        if Regex.match?(~r/\A[0-9a-f]{40}\z/, sha) do
          {:ok, sha}
        else
          {:error, "git rev-parse HEAD returned #{inspect(sha)}"}
        end

      {:error, msg} ->
        {:error, msg}
    end
  end

  defp read_files(dep, dest) do
    root = Path.join(dest, dep.root)

    case Files.collect(root) do
      {:ok, files} when map_size(files) > 0 ->
        {:ok, files}

      {:ok, _empty} ->
        {:error, "no .muro file under #{dep.root}"}

      {:error, "package root is missing"} ->
        {:error, "root #{dep.root} is missing"}

      {:error, msg} ->
        {:error, msg}
    end
  end

  defp tag_version("v" <> rest = tag) do
    case rest do
      <<digit, _::binary>> when digit in ?0..?9 -> rest
      _other -> tag
    end
  end

  defp tag_version(tag), do: tag

  defp commit_ref?(ref), do: String.match?(ref, ~r/\A[0-9a-fA-F]{7,40}\z/)

  defp git(git, args, opts) do
    opts = Keyword.merge([stderr_to_stdout: true, env: [{"GIT_TERMINAL_PROMPT", "0"}]], opts)

    case System.cmd(git, args, opts) do
      {out, 0} -> {:ok, out}
      {out, status} -> {:error, "git failed (#{status}): #{trim_error(out)}"}
    end
  end

  defp trim_error(out) do
    out = String.trim(out)
    if out == "", do: "no output", else: out
  end
end

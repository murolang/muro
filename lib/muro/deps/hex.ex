defmodule Muro.Deps.Hex do
  @moduledoc """
  Fetch one Hex dependency without the Hex client.

  The transport is `Application.get_env(:muro, :hex_transport,
  Muro.Deps.Hex.Http)`. That key is a test seam, not a user option.
  Tests install a module that returns fixture releases and tarballs.

  The highest release matching the requirement is selected with
  `Version.match?/3` and `allow_pre: false`, so a pre-release is
  eligible only when the requirement itself contains a pre-release.
  A release whose
  `retirement` field is a JSON object is skipped when another
  matching release is not retired. When every match is retired, the
  highest retired release is used.

  The outer tarball is `VERSION`, `CHECKSUM`, `metadata.config`, and
  `contents.tar.gz`. `CHECKSUM` must be the sha256 of
  `VERSION <> metadata.config <> contents.tar.gz`, as uppercase or
  lowercase hex, or as the raw 32-byte digest. Members that are
  symlinks, absolute paths, or paths containing `..` are refused.
  Only regular files under `priv/muro/` whose names end in `.muro`
  are kept. The lock records the sha256 of the outer tarball.

  Private repositories, organizations, and auth keys are not
  supported. A 401 from the API says so.
  """

  @doc """
  `{:ok, %{version, resolved, files}}` or `{:error, message}`.
  `resolved` is `{:hex, version, tarball_sha256}`.
  """
  def fetch(%{kind: :hex, package: package, requirement: requirement, name: name}) do
    transport = Application.get_env(:muro, :hex_transport, Muro.Deps.Hex.Http)

    with {:ok, releases} <- transport.releases(package),
         {:ok, version} <- choose(releases, requirement, package),
         {:ok, tarball} <- transport.tarball(package, version),
         {:ok, files} <- unpack(tarball) do
      if map_size(files) == 0 do
        {:error, "#{name}: no .muro file under priv/muro"}
      else
        {:ok,
         %{
           version: version,
           resolved: {:hex, version, Muro.Hash.sha256(tarball)},
           files: files
         }}
      end
    else
      {:error, msg} -> {:error, prefix(name, msg)}
    end
  end

  @doc """
  The version string of the release `choose/3` selects.
  `releases` is a list of `%{version: text, retired: bool}`.
  """
  def choose(releases, requirement, package) when is_list(releases) and is_binary(requirement) do
    parsed =
      Enum.flat_map(releases, fn rel ->
        text = Map.get(rel, :version)

        case text do
          text when is_binary(text) ->
            case Version.parse(text) do
              {:ok, version} ->
                [%{version: version, text: text, retired: Map.get(rel, :retired, false) == true}]

              :error ->
                []
            end

          _other ->
            []
        end
      end)

    matching =
      Enum.filter(parsed, fn rel ->
        Version.match?(rel.version, requirement, allow_pre: false)
      end)

    pool =
      case Enum.reject(matching, & &1.retired) do
        [] -> matching
        open -> open
      end

    case Enum.sort_by(pool, fn rel -> rel.version end, {:desc, Version}) do
      [best | _rest] -> {:ok, best.text}
      [] -> {:error, "no release of #{package} matches #{requirement}"}
    end
  end

  @doc """
  `.muro` files from a Hex outer tarball, keyed by the path under
  `priv/muro/`. `{:error, message}` when the checksum or a member
  is refused.
  """
  def unpack(bin) when is_binary(bin) do
    with :ok <- screen(bin, false),
         {:ok, outer} <- extract_map(bin, false),
         {:ok, version} <- member(outer, "VERSION"),
         {:ok, checksum} <- member(outer, "CHECKSUM"),
         {:ok, metadata} <- member(outer, "metadata.config"),
         {:ok, contents} <- member(outer, "contents.tar.gz"),
         :ok <- verify_checksum(checksum, version, metadata, contents),
         :ok <- screen(contents, true),
         {:ok, inner} <- extract_map(contents, true) do
      take_muro(inner)
    end
  end

  defp prefix(name, msg) do
    if String.starts_with?(msg, name <> ":") do
      msg
    else
      name <> ": " <> msg
    end
  end

  defp verify_checksum(checksum, version, metadata, contents) do
    digest = :crypto.hash(:sha256, version <> metadata <> contents)
    hex = Base.encode16(digest, case: :upper)

    cond do
      checksum == digest ->
        :ok

      String.valid?(checksum) and String.upcase(String.trim(checksum)) == hex ->
        :ok

      true ->
        {:error, "tarball CHECKSUM does not match"}
    end
  end

  defp take_muro(files) do
    Enum.reduce_while(files, {:ok, %{}}, fn {name, bytes}, {:ok, acc} ->
      case under_muro(name) do
        {:ok, rel} -> {:cont, {:ok, Map.put(acc, rel, bytes)}}
        :skip -> {:cont, {:ok, acc}}
      end
    end)
  end

  defp under_muro(name) do
    case String.split(name, "/", parts: 3) do
      ["priv", "muro", rel] ->
        if String.ends_with?(rel, ".muro") and not String.contains?(rel, "..") do
          {:ok, rel}
        else
          :skip
        end

      _other ->
        :skip
    end
  end

  defp member(files, name) do
    case Map.fetch(files, name) do
      {:ok, bytes} -> {:ok, bytes}
      :error -> {:error, "tarball is missing #{name}"}
    end
  end

  defp screen(bin, compressed?) do
    case list_entries(bin, compressed?) do
      {:ok, rows} ->
        Enum.reduce_while(rows, :ok, fn {name, type}, :ok ->
          cond do
            type in [:symlink, :link] ->
              {:halt, {:error, "tarball has a symlink: #{name}"}}

            true ->
              case clean_name(name) do
                {:ok, _cleaned} -> {:cont, :ok}
                {:error, :absolute} -> {:halt, {:error, "tarball has an absolute path: #{name}"}}
                {:error, :escape} -> {:halt, {:error, "tarball has a path that escapes: #{name}"}}
              end
          end
        end)

      {:error, _} = err ->
        err
    end
  end

  defp extract_map(bin, compressed?) do
    case extract_entries(bin, compressed?) do
      {:ok, files} -> index_entries(files)
      {:error, _} = err -> err
    end
  end

  defp index_entries(files) do
    Enum.reduce_while(files, {:ok, %{}}, fn {name, bytes}, {:ok, acc} ->
      case clean_name(name) do
        {:ok, cleaned} -> {:cont, {:ok, Map.put(acc, cleaned, bytes)}}
        {:error, :absolute} -> {:halt, {:error, "tarball has an absolute path: #{name}"}}
        {:error, :escape} -> {:halt, {:error, "tarball has a path that escapes: #{name}"}}
      end
    end)
  end

  defp clean_name(name) do
    name = String.replace(name, "\\", "/")

    cond do
      String.starts_with?(name, "/") ->
        {:error, :absolute}

      Regex.match?(~r/\A[A-Za-z]:/, name) ->
        {:error, :absolute}

      Enum.any?(String.split(name, "/"), fn seg -> seg == ".." end) ->
        {:error, :escape}

      true ->
        segs = Enum.reject(String.split(name, "/"), fn seg -> seg in ["", "."] end)
        {:ok, Enum.join(segs, "/")}
    end
  end

  defp list_entries(bin, compressed?) do
    opts = if compressed?, do: [:verbose, :compressed], else: [:verbose]

    with_tar(bin, fn path ->
      case :erl_tar.table(path, opts) do
        {:ok, rows} -> {:ok, Enum.map(rows, &normalize_row/1)}
        {:error, reason} -> {:error, "tarball could not be read (#{inspect(reason)})"}
      end
    end)
  end

  defp extract_entries(bin, compressed?) do
    opts = if compressed?, do: [:memory, :compressed], else: [:memory]

    with_tar(bin, fn path ->
      case :erl_tar.extract(path, opts) do
        {:ok, files} ->
          {:ok, Map.new(files, fn {name, bytes} -> {entry_name(name), bytes} end)}

        {:error, reason} ->
          {:error, "tarball could not be read (#{inspect(reason)})"}
      end
    end)
  end

  defp normalize_row({name, type, _size, _mtime, _mode, _uid, _gid}) do
    {entry_name(name), type}
  end

  defp normalize_row(name), do: {entry_name(name), :regular}

  defp entry_name(name) when is_binary(name), do: name
  defp entry_name(name) when is_list(name), do: List.to_string(name)

  defp with_tar(bin, fun) do
    path =
      Path.join(
        System.tmp_dir!(),
        "muro-tar-" <> Integer.to_string(System.unique_integer([:positive]))
      )

    File.write!(path, bin)

    try do
      fun.(String.to_charlist(path))
    after
      File.rm(path)
    end
  end
end

defmodule Muro.Lock do
  @moduledoc """
  Read and write `muro.lock`.

  The file is a comment and one map, in a restricted Elixir literal
  syntax. `encode/1` prints it. `decode/1` parses it with
  `Code.string_to_quoted/2` and walks the AST. It never evaluates
  the file. A value that is not a literal map, list, 2-tuple,
  3-tuple, atom, binary, or integer is refused. The message names
  `muro.lock` and says to run `mix muro.deps.get`.

  Package names are sorted. Inside a package the keys are `files`,
  `resolved`, `source`, `version`, in that order. Each `.muro` file
  is one line, sorted by path. Indentation is two spaces. The file
  uses LF and ends with one newline.
  """

  @banner "# muro.lock: written by mix muro.deps.get. Do not edit."
  @atoms [:files, :git, :hex, :ref, :resolved, :root, :source, :tag, :version]

  @doc "The bytes of `muro.lock` for `packages`, a map of name to entry."
  def encode(packages) when is_map(packages) do
    # Mention the atoms the reader accepts so `existing_atoms_only` can see them.
    _atoms = @atoms

    entries =
      packages
      |> Enum.sort_by(fn {name, _pkg} -> name end)
      |> Enum.map(fn {name, pkg} -> package_block(name, pkg) end)

    body =
      case entries do
        [] -> "%{\n}"
        _ -> "%{\n" <> Enum.join(entries, ",\n") <> "\n}"
      end

    @banner <> "\n" <> body <> "\n"
  end

  @doc """
  `{:ok, packages}` or `{:error, message}`. `packages` maps each
  package name to `%{files, resolved, source, version}`.
  """
  def decode(content) when is_binary(content) do
    case String.split(content, "\n", parts: 2) do
      [@banner, body] ->
        decode_body(body)

      _other ->
        {:error, "muro.lock is not a muro lock; run mix muro.deps.get"}
    end
  end

  @doc "One-line literal for a manifest spec or a lock field."
  def show(term), do: format_term(term)

  defp decode_body(body) do
    case Code.string_to_quoted(body, existing_atoms_only: true) do
      {:ok, ast} ->
        case literal(ast) do
          {:ok, term} -> validate(term)
          {:error, msg} -> {:error, lock_error(msg)}
        end

      {:error, reason} ->
        {:error, lock_error(quote_reason(reason))}
    end
  end

  defp lock_error(msg), do: "muro.lock could not be read (#{msg}); run mix muro.deps.get"

  defp quote_reason({_line, err, token}) do
    inspect(err) <> " " <> inspect(token)
  end

  defp quote_reason(other), do: inspect(other)

  defp literal(atom) when is_atom(atom), do: {:ok, atom}
  defp literal(bin) when is_binary(bin), do: {:ok, bin}
  defp literal(int) when is_integer(int), do: {:ok, int}

  defp literal(list) when is_list(list) do
    Enum.reduce_while(list, {:ok, []}, fn el, {:ok, acc} ->
      case literal(el) do
        {:ok, value} -> {:cont, {:ok, acc ++ [value]}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp literal({:%{}, _meta, pairs}) when is_list(pairs) do
    Enum.reduce_while(pairs, {:ok, %{}}, fn
      {key, value}, {:ok, acc} ->
        case literal(key) do
          {:ok, decoded_key} ->
            case literal(value) do
              {:ok, decoded_value} -> {:cont, {:ok, Map.put(acc, decoded_key, decoded_value)}}
              {:error, _} = err -> {:halt, err}
            end

          {:error, _} = err ->
            {:halt, err}
        end

      _other, _acc ->
        {:halt, {:error, "a non-literal map"}}
    end)
  end

  defp literal({:{}, _meta, [left, right]}) do
    with {:ok, left} <- literal(left),
         {:ok, right} <- literal(right) do
      {:ok, {left, right}}
    end
  end

  defp literal({:{}, _meta, [a, b, c]}) do
    with {:ok, a} <- literal(a),
         {:ok, b} <- literal(b),
         {:ok, c} <- literal(c) do
      {:ok, {a, b, c}}
    end
  end

  defp literal({:{}, _meta, _elts}), do: {:error, "a tuple that is not 2 or 3 elements"}

  defp literal({left, right}) do
    with {:ok, left} <- literal(left),
         {:ok, right} <- literal(right) do
      {:ok, {left, right}}
    end
  end

  defp literal(_other), do: {:error, "a non-literal"}

  defp validate(packages) when is_map(packages) do
    Enum.reduce_while(packages, {:ok, %{}}, fn {name, entry}, {:ok, acc} ->
      case validate_entry(name, entry) do
        {:ok, normalized} -> {:cont, {:ok, Map.put(acc, name, normalized)}}
        {:error, _} = err -> {:halt, err}
      end
    end)
  end

  defp validate(_other) do
    {:error, "muro.lock could not be read (the lock is not a map); run mix muro.deps.get"}
  end

  defp validate_entry(name, entry) when is_binary(name) and is_map(entry) do
    if Regex.match?(~r/\A[a-z][a-z0-9_]*\z/, name) and
         Map.keys(entry) |> Enum.sort() == [:files, :resolved, :source, :version] do
      with {:ok, files} <- validate_files(name, entry.files),
           {:ok, resolved} <- validate_resolved(name, entry.resolved),
           {:ok, source} <- validate_source(name, entry.source),
           {:ok, version} <- validate_version(name, entry.version) do
        {:ok, %{files: files, resolved: resolved, source: source, version: version}}
      end
    else
      {:error, entry_error(name, "unexpected shape")}
    end
  end

  defp validate_entry(name, _entry), do: {:error, entry_error(name, "unexpected shape")}

  defp validate_files(name, files) when is_map(files) do
    Enum.reduce_while(files, {:ok, %{}}, fn {path, hash}, {:ok, acc} ->
      cond do
        not is_binary(path) or not pkg_path?(path) ->
          {:halt, {:error, entry_error(name, "bad file path #{inspect(path)}")}}

        not hash?(hash) ->
          {:halt, {:error, entry_error(name, "bad sha256 for #{path}")}}

        true ->
          {:cont, {:ok, Map.put(acc, path, hash)}}
      end
    end)
  end

  defp validate_files(name, _files), do: {:error, entry_error(name, "files is not a map")}

  defp validate_resolved(_name, {:git, sha}) when is_binary(sha) do
    if Regex.match?(~r/\A[0-9a-f]{40}\z/, sha) do
      {:ok, {:git, sha}}
    else
      {:error, entry_error("a package", "bad git revision #{inspect(sha)}")}
    end
  end

  defp validate_resolved(name, {:hex, version, sha})
       when is_binary(version) and is_binary(sha) do
    if hash?(sha) and version != "" do
      {:ok, {:hex, version, sha}}
    else
      {:error, entry_error(name, "bad hex resolution")}
    end
  end

  defp validate_resolved(name, _other), do: {:error, entry_error(name, "bad resolved")}

  defp validate_source(name, {:git, url, opts}) when is_binary(url) and is_list(opts) do
    case normalize_git_source(url, opts) do
      {:ok, source} -> {:ok, source}
      :error -> {:error, entry_error(name, "bad git source")}
    end
  end

  defp validate_source(name, {:hex, package, requirement})
       when is_binary(package) and is_binary(requirement) do
    if Regex.match?(~r/\A[a-z][a-z0-9_-]*\z/, package) and
         match?({:ok, _req}, Version.parse_requirement(requirement)) do
      {:ok, {:hex, package, requirement}}
    else
      {:error, entry_error(name, "bad hex source")}
    end
  end

  defp validate_source(name, _other), do: {:error, entry_error(name, "bad source")}

  defp normalize_git_source(url, opts) do
    tag = Keyword.get(opts, :tag)
    ref = Keyword.get(opts, :ref)
    root = Keyword.get(opts, :root, ".")
    keys = Enum.sort(Keyword.keys(opts))

    cond do
      url == "" or String.starts_with?(url, "-") ->
        :error

      is_binary(tag) and ref == nil and keys -- [:tag, :root] == [] and plain?(tag) and
          plain_root?(root) ->
        {:ok, {:git, url, source_opts({:tag, tag}, root)}}

      is_binary(ref) and tag == nil and keys -- [:ref, :root] == [] and plain?(ref) and
          plain_root?(root) ->
        {:ok, {:git, url, source_opts({:ref, ref}, root)}}

      tag == nil and ref == nil and keys -- [:root] == [] and plain_root?(root) ->
        {:ok, {:git, url, source_opts(:head, root)}}

      true ->
        :error
    end
  end

  defp source_opts(:head, "."), do: []
  defp source_opts(:head, root), do: [root: root]
  defp source_opts({:tag, tag}, "."), do: [tag: tag]
  defp source_opts({:tag, tag}, root), do: [tag: tag, root: root]
  defp source_opts({:ref, ref}, "."), do: [ref: ref]
  defp source_opts({:ref, ref}, root), do: [ref: ref, root: root]

  defp validate_version(_name, version) when is_binary(version) do
    if version != "" and not String.contains?(version, "\n") and
         not String.contains?(version, "\r") do
      {:ok, version}
    else
      {:error, "muro.lock could not be read (bad version); run mix muro.deps.get"}
    end
  end

  defp validate_version(name, _version), do: {:error, entry_error(name, "bad version")}

  defp pkg_path?(path) do
    String.ends_with?(path, ".muro") and not String.contains?(path, "\\") and
      not String.starts_with?(path, "/") and
      Enum.all?(String.split(path, "/"), fn seg -> seg not in ["", ".", ".."] end)
  end

  defp hash?(value), do: is_binary(value) and Regex.match?(~r/\A[0-9a-f]{64}\z/, value)

  defp plain?(value) do
    is_binary(value) and value != "" and not String.starts_with?(value, "-") and
      not String.contains?(value, "\n")
  end

  defp plain_root?("."), do: true

  defp plain_root?(root) do
    plain?(root) and Path.type(root) == :relative and not String.contains?(root, "\\") and
      Enum.all?(String.split(root, "/"), fn seg -> seg not in ["", ".", ".."] end)
  end

  defp entry_error(name, msg) when is_binary(name) do
    "muro.lock could not be read (#{name}: #{msg}); run mix muro.deps.get"
  end

  defp entry_error(name, msg), do: entry_error(inspect(name), msg)

  defp package_block(name, pkg) do
    [
      "  ",
      quote_string(name),
      " => %{\n",
      "    files: ",
      files_block(pkg.files),
      ",\n",
      "    resolved: ",
      format_term(pkg.resolved),
      ",\n",
      "    source: ",
      format_term(pkg.source),
      ",\n",
      "    version: ",
      quote_string(pkg.version),
      "\n",
      "  }"
    ]
    |> IO.iodata_to_binary()
  end

  defp files_block(files) do
    rows =
      files
      |> Enum.sort_by(fn {path, _hash} -> path end)
      |> Enum.map(fn {path, hash} ->
        "      " <> quote_string(path) <> " => " <> quote_string(hash)
      end)

    case rows do
      [] -> "%{}"
      _ -> "%{\n" <> Enum.join(rows, ",\n") <> "\n    }"
    end
  end

  defp format_term(nil), do: "nil"
  defp format_term(true), do: "true"
  defp format_term(false), do: "false"

  defp format_term(atom) when is_atom(atom) do
    body = quote_atom(atom)

    if String.starts_with?(body, ":") do
      body
    else
      ":" <> body
    end
  end

  defp format_term(bin) when is_binary(bin), do: quote_string(bin)
  defp format_term(int) when is_integer(int), do: Integer.to_string(int)

  defp format_term(list) when is_list(list) do
    if keyword_list?(list) do
      inner =
        Enum.map_join(list, ", ", fn {key, value} ->
          quote_atom(key) <> ": " <> format_term(value)
        end)

      "[" <> inner <> "]"
    else
      "[" <> Enum.map_join(list, ", ", &format_term/1) <> "]"
    end
  end

  defp format_term(tuple) when is_tuple(tuple) do
    inner = tuple |> Tuple.to_list() |> Enum.map_join(", ", &format_term/1)
    "{" <> inner <> "}"
  end

  defp format_term(map) when is_map(map) do
    inner =
      map
      |> Enum.sort()
      |> Enum.map_join(", ", fn {key, value} ->
        format_term(key) <> " => " <> format_term(value)
      end)

    "%{" <> inner <> "}"
  end

  defp keyword_list?([]), do: false

  defp keyword_list?(list) do
    Enum.all?(list, fn
      {key, _value} when is_atom(key) -> true
      _other -> false
    end)
  end

  defp quote_atom(atom) do
    text = Atom.to_string(atom)

    if Regex.match?(~r/\A[a-z_][A-Za-z0-9_]*[?!]?\z/, text) do
      text
    else
      ":" <> quote_string(text)
    end
  end

  defp quote_string(bin), do: "\"" <> escape(bin) <> "\""

  defp escape(<<>>), do: ""
  defp escape(<<"\\", rest::binary>>), do: "\\\\" <> escape(rest)
  defp escape(<<"\"", rest::binary>>), do: "\\\"" <> escape(rest)
  defp escape(<<"\n", rest::binary>>), do: "\\n" <> escape(rest)
  defp escape(<<"\r", rest::binary>>), do: "\\r" <> escape(rest)
  defp escape(<<"\t", rest::binary>>), do: "\\t" <> escape(rest)
  defp escape(<<?#, ?{, rest::binary>>), do: "\\\#{" <> escape(rest)

  defp escape(<<char::utf8, rest::binary>>) when char >= 32 and char < 127 do
    <<char>> <> escape(rest)
  end

  defp escape(<<char::utf8, rest::binary>>) do
    "\\u{#{Integer.to_string(char, 16)}}" <> escape(rest)
  end
end

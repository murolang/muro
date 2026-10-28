defmodule Muro.Manifest do
  @moduledoc """
  The project manifest for `mix muro.gen`.

  A manifest is `muro.exs` at the project root, evaluated with
  `Code.eval_file/1` as a keyword list, or a `:muro` key in the
  `mix.exs` project config when that Mix project is the root.
  If both define a manifest, loading stops and names both.

  Keys:

    * `muro:` — required version string. `mix muro.gen` runs only
      when it equals the running version.
    * `fuel:` — optional positive integer. The default is
      `Muro.Check.default_fuel/0`, the fuel `mix muro.check` uses.
    * `modules:` — required list of `{book_path, module, target_path}`.
      Paths are relative to the project root. The module is an alias
      atom (`MyApp.Billing.Rounding`).

  A book or a target that leaves the project root is refused, and so
  is a missing book, a duplicate target, or a module that is not an
  alias atom.

  `muro_deps:` is optional. It is a keyword list of package names to
  git or Hex specs. `mix muro.deps.get` fetches those packages.
  `load/1` validates it with the other keys. `load_deps/1` validates
  only that key, so a project that imports packages and does not
  generate modules can omit `muro:` and `modules:`.
  """

  defstruct [:version, :fuel, :modules, :deps, :source]

  @keys [:fuel, :modules, :muro, :muro_deps]
  @dep_name ~r/\A[a-z][a-z0-9_]*\z/
  @hex_name ~r/\A[a-z][a-z0-9_-]*\z/
  @git_opts [:ref, :root, :tag]

  @doc """
  Directory the tasks treat as the project root.

  Inside a Mix project, when the working directory is that project
  or a subdirectory, this is the directory of `mix.exs`. Otherwise
  it is the working directory, including an archive run with no
  Mix project.
  """
  def root do
    cwd = canonical(File.cwd!())

    case Mix.Project.get() do
      nil ->
        cwd

      _project ->
        project = canonical(project_dir())

        if cwd == project or inside?(cwd, project) do
          project
        else
          cwd
        end
    end
  end

  @doc """
  Load and validate the manifest at `root`.

  `{:ok, manifest}` or `{:error, message}`. The message names every
  problem found in the file.
  """
  def load(root) when is_binary(root) do
    case read_term(root) do
      {:error, _} = err ->
        err

      :none ->
        {:error, "no manifest: expected muro.exs or a :muro key in mix.exs"}

      {:ok, term, source} ->
        with {:ok, manifest} <- validate(term, root) do
          {:ok, %{manifest | source: source}}
        end
    end
  end

  @doc """
  Load `muro_deps:` from the manifest at `root`.

  Same location rules as `load/1`, including the error when `muro.exs`
  and a `:muro` key both exist. Other keys are ignored. `{:ok, []}`
  when there is no manifest or no `muro_deps:` key. The list is the
  normalized dependency maps, sorted by name.
  """
  def load_deps(root) when is_binary(root) do
    case read_term(root) do
      :none ->
        {:ok, []}

      {:error, _} = err ->
        err

      {:ok, term, _source} ->
        deps_only(term)
    end
  end

  @doc """
  Nearest ancestor of `path`, starting at its own directory, that
  contains `muro.exs` or `mix.exs`. `nil` when none does.
  """
  def find_root(path) when is_binary(path) do
    path = canonical(path)
    start = if File.dir?(path), do: path, else: Path.dirname(path)
    climb(start)
  end

  @doc """
  `muro.exs` or `mix.exs` when that file is the manifest at `root`.
  `nil` when neither file is present.
  """
  def manifest_name(root) when is_binary(root) do
    root = canonical(root)

    cond do
      File.regular?(Path.join(root, "muro.exs")) -> "muro.exs"
      File.regular?(Path.join(root, "mix.exs")) -> "mix.exs"
      true -> nil
    end
  end

  @doc false
  def canonical(path) do
    path
    |> Path.expand()
    |> Path.split()
    |> resolve_links([], 32)
    |> Enum.reverse()
    |> then(fn
      [] -> "/"
      parts -> Path.join(parts)
    end)
  end

  @doc """
  Validate a manifest term. `root` is the project root used to
  resolve book and target paths.
  """
  def validate(term, root) when is_binary(root) do
    root = canonical(root)

    if Keyword.keyword?(term) do
      errors = key_errors(term)
      {version, errors} = take_version(term, errors)
      {fuel, errors} = take_fuel(term, errors)
      {modules, errors} = take_modules(term, root, errors)
      {deps, errors} = take_deps(term, errors)

      if errors == [] do
        {:ok,
         %__MODULE__{version: version, fuel: fuel, modules: modules, deps: deps, source: nil}}
      else
        {:error, Enum.join(errors, "\n")}
      end
    else
      {:error, "manifest must be a keyword list, got: #{inspect(term)}"}
    end
  end

  @doc """
  `:ok` when `manifest_version` equals `running`. Otherwise an error
  that names both versions.
  """
  def version_pin(manifest_version, running)
      when is_binary(manifest_version) and is_binary(running) do
    if manifest_version == running do
      :ok
    else
      {:error, "muro version mismatch: manifest says #{manifest_version}, running #{running}"}
    end
  end

  @doc """
  The `:muro` value from the loaded Mix project when that project's
  directory is `root`, or `:none`.
  """
  def mix_config(root) when is_binary(root) do
    case Mix.Project.get() do
      nil ->
        :none

      _project ->
        if canonical(project_dir()) == canonical(root) do
          case Keyword.fetch(Mix.Project.config(), :muro) do
            {:ok, value} -> {:ok, value}
            :error -> :none
          end
        else
          :none
        end
    end
  end

  @doc "Absolute path of a manifest book."
  def book_path(root, %{book: book}), do: Path.expand(book, root)

  @doc "Absolute path of a manifest target."
  def target_path(root, %{target: target}), do: Path.expand(target, root)

  defp read_term(root) do
    root = canonical(root)
    exs = Path.join(root, "muro.exs")
    has_exs = File.regular?(exs)

    case mix_config(root) do
      {:ok, _value} when has_exs ->
        {:error, "muro.exs and the :muro key in mix.exs both define a manifest"}

      {:ok, value} ->
        {:ok, value, :mix}

      :none when has_exs ->
        case eval_exs(exs) do
          {:ok, term} -> {:ok, term, :muro_exs}
          {:error, _} = err -> err
        end

      :none ->
        :none
    end
  end

  defp deps_only(term) do
    if Keyword.keyword?(term) do
      case Keyword.fetch(term, :muro_deps) do
        :error ->
          {:ok, []}

        {:ok, deps} ->
          {deps, errors} = validate_deps(deps, [])

          if errors == [] do
            {:ok, deps}
          else
            {:error, Enum.join(errors, "\n")}
          end
      end
    else
      {:error, "manifest must be a keyword list, got: #{inspect(term)}"}
    end
  end

  defp climb(dir) do
    cond do
      File.regular?(Path.join(dir, "muro.exs")) ->
        dir

      File.regular?(Path.join(dir, "mix.exs")) ->
        dir

      true ->
        parent = Path.dirname(dir)
        if parent == dir, do: nil, else: climb(parent)
    end
  end

  defp eval_exs(path) do
    try do
      {term, _binding} = Code.eval_file(path)
      {:ok, term}
    rescue
      error ->
        {:error, "muro.exs failed to evaluate: #{Exception.message(error)}"}
    end
  end

  defp key_errors(term) do
    unknown = term |> Keyword.keys() |> Enum.uniq() |> Enum.reject(&(&1 in @keys)) |> Enum.sort()

    repeated =
      term
      |> Keyword.keys()
      |> Enum.frequencies()
      |> Enum.filter(fn {_key, count} -> count > 1 end)
      |> Enum.map(fn {key, _count} -> key end)
      |> Enum.sort()

    unknown_error(unknown) ++ repeated_error(repeated)
  end

  defp unknown_error([]), do: []

  defp unknown_error(keys) do
    ["manifest has unknown keys: #{inspect(keys)}"]
  end

  defp repeated_error([]), do: []

  defp repeated_error(keys) do
    ["manifest repeats #{Enum.map_join(keys, ", ", &inspect/1)}"]
  end

  defp take_version(term, errors) do
    case Keyword.fetch(term, :muro) do
      :error ->
        {nil, errors ++ ["manifest is missing muro:"]}

      {:ok, version} ->
        if version_string?(version) do
          {version, errors}
        else
          {nil, errors ++ ["manifest muro: must be a version string, got: #{inspect(version)}"]}
        end
    end
  end

  defp version_string?(version) when is_binary(version) do
    version != "" and not String.contains?(version, "\n") and not String.contains?(version, "\r")
  end

  defp version_string?(_version), do: false

  defp take_deps(term, errors) do
    case Keyword.fetch(term, :muro_deps) do
      :error -> {[], errors}
      {:ok, deps} -> validate_deps(deps, errors)
    end
  end

  defp validate_deps(deps, errors) when is_list(deps) do
    if Keyword.keyword?(deps) do
      errors = errors ++ duplicate_dep_errors(deps)

      {entries, errors} =
        Enum.reduce(deps, {[], errors}, fn {name, spec}, {entries, errors} ->
          case validate_dep(name, spec) do
            {:ok, dep} -> {entries ++ [dep], errors}
            {:error, msg} -> {entries, errors ++ [msg]}
          end
        end)

      {Enum.sort_by(entries, & &1.name), errors}
    else
      {[], errors ++ ["muro_deps must be a keyword list, got: #{inspect(deps)}"]}
    end
  end

  defp validate_deps(deps, errors) do
    {[], errors ++ ["muro_deps must be a keyword list, got: #{inspect(deps)}"]}
  end

  defp duplicate_dep_errors(deps) do
    deps
    |> Keyword.keys()
    |> Enum.frequencies()
    |> Enum.filter(fn {_name, count} -> count > 1 end)
    |> Enum.map(fn {name, _count} -> name end)
    |> Enum.sort()
    |> Enum.map(fn name -> "muro_deps entry #{dep_label(name)}: duplicate name" end)
  end

  defp validate_dep(name, spec) do
    with :ok <- validate_dep_name(name),
         {:ok, dep} <- validate_spec(name, spec) do
      {:ok, Map.put(dep, :name, Atom.to_string(name))}
    end
  end

  defp validate_dep_name(name) when is_atom(name) do
    text = Atom.to_string(name)

    if Regex.match?(@dep_name, text) do
      :ok
    else
      {:error, "muro_deps entry #{text}: name must match [a-z][a-z0-9_]*"}
    end
  end

  defp validate_dep_name(name) do
    {:error, "muro_deps entry #{inspect(name)}: name must be an atom matching [a-z][a-z0-9_]*"}
  end

  defp validate_spec(name, {:git, url, opts}) do
    label = dep_label(name)

    with :ok <- validate_url(label, url),
         {:ok, pin, root} <- validate_git_opts(label, opts) do
      {:ok, git_dep(url, pin, root)}
    end
  end

  defp validate_spec(name, {:hex, package, requirement}) do
    label = dep_label(name)

    with :ok <- validate_hex_package(label, package),
         :ok <- validate_requirement(label, requirement) do
      {:ok,
       %{
         kind: :hex,
         package: package,
         requirement: requirement,
         root: "priv/muro",
         source: {:hex, package, requirement}
       }}
    end
  end

  defp validate_spec(name, other) do
    {:error, "muro_deps entry #{dep_label(name)}: unknown source #{inspect(other)}"}
  end

  defp git_dep(url, {:tag, tag}, root) do
    %{
      kind: :git,
      url: url,
      pin: {:tag, tag},
      root: root,
      source: {:git, url, git_source_opts(tag: tag, root: root)}
    }
  end

  defp git_dep(url, {:ref, ref}, root) do
    %{
      kind: :git,
      url: url,
      pin: {:ref, ref},
      root: root,
      source: {:git, url, git_source_opts(ref: ref, root: root)}
    }
  end

  defp git_source_opts(tag: tag, root: "."), do: [tag: tag]
  defp git_source_opts(tag: tag, root: root), do: [tag: tag, root: root]
  defp git_source_opts(ref: ref, root: "."), do: [ref: ref]
  defp git_source_opts(ref: ref, root: root), do: [ref: ref, root: root]

  defp validate_git_opts(label, opts) when is_list(opts) do
    if Keyword.keyword?(opts) do
      unknown =
        opts |> Keyword.keys() |> Enum.uniq() |> Enum.reject(&(&1 in @git_opts)) |> Enum.sort()

      repeated =
        opts
        |> Keyword.keys()
        |> Enum.frequencies()
        |> Enum.filter(fn {_key, count} -> count > 1 end)
        |> Enum.map(fn {key, _count} -> key end)
        |> Enum.sort()

      cond do
        unknown != [] ->
          {:error, "muro_deps entry #{label}: unknown option #{inspect(unknown)}"}

        repeated != [] ->
          {:error,
           "muro_deps entry #{label}: repeats #{Enum.map_join(repeated, ", ", &inspect/1)}"}

        Keyword.has_key?(opts, :tag) and Keyword.has_key?(opts, :ref) ->
          {:error, "muro_deps entry #{label}: tag and ref are both set"}

        Keyword.has_key?(opts, :tag) ->
          with :ok <- validate_token(label, "tag", opts[:tag]),
               {:ok, root} <- take_root(label, opts) do
            {:ok, {:tag, opts[:tag]}, root}
          end

        Keyword.has_key?(opts, :ref) ->
          with :ok <- validate_token(label, "ref", opts[:ref]),
               {:ok, root} <- take_root(label, opts) do
            {:ok, {:ref, opts[:ref]}, root}
          end

        true ->
          {:error, "muro_deps entry #{label}: expected one of tag: or ref:"}
      end
    else
      {:error, "muro_deps entry #{label}: options must be a keyword list, got: #{inspect(opts)}"}
    end
  end

  defp validate_git_opts(label, opts) do
    {:error, "muro_deps entry #{label}: options must be a keyword list, got: #{inspect(opts)}"}
  end

  defp validate_url(label, url) do
    cond do
      not is_binary(url) ->
        {:error, "muro_deps entry #{label}: url must be a string, got: #{inspect(url)}"}

      url == "" or String.contains?(url, "\n") or String.contains?(url, "\r") ->
        {:error, "muro_deps entry #{label}: url must be a non-empty string without newlines"}

      String.starts_with?(url, "-") ->
        {:error, "muro_deps entry #{label}: url must not start with -"}

      true ->
        :ok
    end
  end

  defp validate_token(label, field, value) do
    if plain_token?(value) do
      :ok
    else
      {:error,
       "muro_deps entry #{label}: #{field} must be a non-empty string that does not start with -, got: #{inspect(value)}"}
    end
  end

  defp take_root(label, opts) do
    case Keyword.fetch(opts, :root) do
      :error ->
        {:ok, "."}

      {:ok, root} ->
        cond do
          not plain_token?(root) ->
            {:error,
             "muro_deps entry #{label}: root must be a relative directory, got: #{inspect(root)}"}

          Path.type(root) != :relative ->
            {:error,
             "muro_deps entry #{label}: root must be a relative directory, got: #{inspect(root)}"}

          bad_root?(root) ->
            {:error,
             "muro_deps entry #{label}: root must not contain .. or an empty segment, got: #{inspect(root)}"}

          true ->
            {:ok, root}
        end
    end
  end

  defp plain_token?(value) when is_binary(value) do
    value != "" and not String.contains?(value, "\n") and not String.contains?(value, "\r") and
      not String.starts_with?(value, "-")
  end

  defp plain_token?(_value), do: false

  defp bad_root?("."), do: false

  defp bad_root?(root) do
    String.contains?(root, "\\") or
      Enum.any?(String.split(root, "/"), fn seg -> seg in ["", ".", ".."] end)
  end

  defp validate_hex_package(label, package) do
    if is_binary(package) and Regex.match?(@hex_name, package) do
      :ok
    else
      {:error,
       "muro_deps entry #{label}: package name must match [a-z][a-z0-9_-]*, got: #{inspect(package)}"}
    end
  end

  defp validate_requirement(label, requirement) do
    cond do
      not is_binary(requirement) or String.contains?(requirement, "\n") or
          String.contains?(requirement, "\r") ->
        {:error, "muro_deps entry #{label}: bad requirement #{inspect(requirement)}"}

      true ->
        case Version.parse_requirement(requirement) do
          {:ok, _req} -> :ok
          :error -> {:error, "muro_deps entry #{label}: bad requirement #{inspect(requirement)}"}
        end
    end
  end

  defp dep_label(name) when is_atom(name), do: Atom.to_string(name)
  defp dep_label(name), do: inspect(name)

  defp take_fuel(term, errors) do
    case Keyword.fetch(term, :fuel) do
      :error ->
        {Muro.Check.default_fuel(), errors}

      {:ok, fuel} when is_integer(fuel) and fuel > 0 ->
        {fuel, errors}

      {:ok, fuel} ->
        {nil, errors ++ ["manifest fuel: must be a positive integer, got: #{inspect(fuel)}"]}
    end
  end

  defp take_modules(term, root, errors) do
    case Keyword.fetch(term, :modules) do
      :error ->
        {[], errors ++ ["manifest is missing modules:"]}

      {:ok, modules} when is_list(modules) ->
        validate_modules(modules, root, errors)

      {:ok, modules} ->
        {[], errors ++ ["manifest modules: must be a list, got: #{inspect(modules)}"]}
    end
  end

  defp validate_modules(modules, root, errors) do
    {entries, errors, _seen} =
      modules
      |> Enum.with_index(1)
      |> Enum.reduce({[], errors, %{}}, fn {entry, index}, {entries, errors, seen} ->
        {entry, entry_errors, seen} = validate_entry(entry, index, root, seen)
        entries = if entry == nil, do: entries, else: entries ++ [entry]
        {entries, errors ++ entry_errors, seen}
      end)

    {entries, errors}
  end

  defp validate_entry({book, module, target}, index, root, seen) do
    {book_rel, book_errors} = validate_book(book, index, root)
    {target_rel, target_errors, seen} = validate_target(target, index, root, seen)
    module_errors = validate_module(module, index)

    errors = book_errors ++ module_errors ++ target_errors

    entry =
      if book_rel && target_rel && module_errors == [] do
        %{book: book_rel, module: module, target: target_rel}
      end

    {entry, errors, seen}
  end

  defp validate_entry(other, index, _root, seen) do
    {nil, ["modules entry #{index} is not {book, module, target}: #{inspect(other)}"], seen}
  end

  defp validate_book(book, index, root) do
    case normalize_inside(root, book) do
      {:ok, rel} ->
        if File.regular?(Path.expand(rel, root)) do
          {rel, []}
        else
          {nil, ["modules entry #{index}: missing book #{rel}"]}
        end

      {:error, :outside} ->
        {nil, ["modules entry #{index}: book is outside the project: #{inspect(book)}"]}

      :bad ->
        {nil,
         [
           "modules entry #{index}: book must be a relative path inside the project, got: #{inspect(book)}"
         ]}
    end
  end

  defp validate_target(target, index, root, seen) do
    case normalize_inside(root, target) do
      {:ok, rel} ->
        abs = Path.expand(rel, root)

        cond do
          File.dir?(abs) ->
            {nil, ["modules entry #{index}: target is a directory: #{rel}"], seen}

          Map.has_key?(seen, rel) ->
            {nil, ["duplicate target #{rel} (modules entries #{seen[rel]} and #{index})"], seen}

          true ->
            {rel, [], Map.put(seen, rel, index)}
        end

      {:error, :outside} ->
        {nil, ["modules entry #{index}: target is outside the project: #{inspect(target)}"], seen}

      :bad ->
        {nil,
         [
           "modules entry #{index}: target must be a relative path inside the project, got: #{inspect(target)}"
         ], seen}
    end
  end

  defp validate_module(module, index) do
    if alias_atom?(module) do
      []
    else
      ["modules entry #{index}: module is not an alias atom, got: #{inspect(module)}"]
    end
  end

  defp alias_atom?(module) when is_atom(module) do
    Macro.classify_atom(module) == :alias and
      inspect(module) =~ ~r/\A[A-Z][A-Za-z0-9]*(\.[A-Z][A-Za-z0-9]*)*\z/
  end

  defp alias_atom?(_module), do: false

  defp normalize_inside(_root, path) when not is_binary(path), do: :bad

  defp normalize_inside(root, path) do
    cond do
      path == "" ->
        :bad

      String.contains?(path, ["\n", "\r", <<0>>]) ->
        :bad

      Path.type(path) != :relative ->
        {:error, :outside}

      true ->
        root = Path.expand(root)
        absolute = Path.expand(path, root)

        case Path.relative_to(absolute, root) do
          "." ->
            {:error, :outside}

          ^absolute ->
            {:error, :outside}

          relative ->
            slash = String.replace(relative, "\\", "/")

            if slash == "" or String.starts_with?(slash, "..") do
              {:error, :outside}
            else
              {:ok, slash}
            end
        end
    end
  end

  defp project_dir do
    Mix.Project.project_file() |> Path.dirname() |> Path.expand()
  end

  defp inside?(path, dir) do
    String.starts_with?(path, dir <> "/")
  end

  # `/var` on macOS is a symlink to `/private/var`. Mix reports the
  # project file through the resolved path, and `System.tmp_dir/0`
  # does not. Compare and join through one form so both names are
  # the same directory. `canonical/1` is that form.
  defp resolve_links([], acc, _depth), do: acc
  defp resolve_links(parts, acc, 0), do: Enum.reverse(parts) ++ acc

  defp resolve_links([part | rest], acc, depth) do
    next = [part | acc] |> Enum.reverse() |> Path.join()

    case File.read_link(next) do
      {:ok, target} ->
        target =
          if Path.type(target) == :absolute do
            target
          else
            Path.expand(target, Path.dirname(next))
          end

        resolve_links(Path.split(target) ++ rest, [], depth - 1)

      {:error, _reason} ->
        resolve_links(rest, [part | acc], depth)
    end
  end
end

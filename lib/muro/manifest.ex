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
    * `modules:` — required list of `{book_path, module, target_path}`
      or `{book_path, module, target_path, opts}`. Paths are relative
      to the project root. The module is an alias atom
      (`MyApp.Billing.Rounding`). A 3-tuple is an Elixir module.
      `opts` is a keyword list: `kind: :elixir` (the default) or
      `kind: :exunit`, and for `:exunit` an optional `impl:` alias,
      the implementation the suite tests by default.

  A book or a target that leaves the project root is refused, and so
  is a missing book, a duplicate target, a module that is not an
  alias atom, an unknown option, an unknown kind, or `impl:` on an
  `:elixir` entry.
  """

  defstruct [:version, :fuel, :modules, :source]

  @keys [:fuel, :modules, :muro]
  @entry_opts [:kind, :impl]

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
    root = canonical(root)
    exs = Path.join(root, "muro.exs")
    has_exs = File.regular?(exs)

    case mix_config(root) do
      {:ok, _value} when has_exs ->
        {:error, "muro.exs and the :muro key in mix.exs both define a manifest"}

      {:ok, value} ->
        with {:ok, manifest} <- validate(value, root) do
          {:ok, %{manifest | source: :mix}}
        end

      :none when has_exs ->
        with {:ok, term} <- eval_exs(exs),
             {:ok, manifest} <- validate(term, root) do
          {:ok, %{manifest | source: :muro_exs}}
        end

      :none ->
        {:error, "no manifest: expected muro.exs or a :muro key in mix.exs"}
    end
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

      if errors == [] do
        {:ok, %__MODULE__{version: version, fuel: fuel, modules: modules, source: nil}}
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
    finish_entry(book, module, target, [], index, root, seen)
  end

  defp validate_entry({book, module, target, opts}, index, root, seen) do
    if Keyword.keyword?(opts) do
      finish_entry(book, module, target, opts, index, root, seen)
    else
      bad_entry({book, module, target, opts}, index, seen)
    end
  end

  defp validate_entry(other, index, _root, seen) do
    bad_entry(other, index, seen)
  end

  defp bad_entry(other, index, seen) do
    {nil, ["modules entry #{index} is not {book, module, target}: #{inspect(other)}"], seen}
  end

  defp finish_entry(book, module, target, opts, index, root, seen) do
    {book_rel, book_errors} = validate_book(book, index, root)
    {target_rel, target_errors, seen} = validate_target(target, index, root, seen)
    module_errors = validate_module(module, index)
    opt_errors = option_errors(opts, index)
    {kind, kind_errors} = take_kind(opts, index)
    {impl, impl_errors} = take_impl(opts, kind, kind_errors == [], index)

    errors =
      book_errors ++ module_errors ++ target_errors ++ opt_errors ++ kind_errors ++ impl_errors

    entry =
      if book_rel && target_rel && errors == [] do
        %{book: book_rel, module: module, target: target_rel, kind: kind, impl: impl}
      end

    {entry, errors, seen}
  end

  defp option_errors(opts, index) do
    unknown =
      opts
      |> Keyword.keys()
      |> Enum.uniq()
      |> Enum.reject(&(&1 in @entry_opts))
      |> Enum.sort()

    repeated =
      opts
      |> Keyword.keys()
      |> Enum.frequencies()
      |> Enum.filter(fn {_key, count} -> count > 1 end)
      |> Enum.map(fn {key, _count} -> key end)
      |> Enum.sort()

    unknown_opts(unknown, index) ++ repeated_opts(repeated, index)
  end

  defp unknown_opts([], _index), do: []

  defp unknown_opts(keys, index) do
    ["modules entry #{index}: unknown options #{inspect(keys)}"]
  end

  defp repeated_opts([], _index), do: []

  defp repeated_opts(keys, index) do
    ["modules entry #{index}: repeated options #{inspect(keys)}"]
  end

  defp take_kind(opts, index) do
    case Keyword.fetch(opts, :kind) do
      :error ->
        {:elixir, []}

      {:ok, kind} when kind in [:elixir, :exunit] ->
        {kind, []}

      {:ok, kind} ->
        {:elixir, ["modules entry #{index}: unknown kind #{inspect(kind)}"]}
    end
  end

  defp take_impl(opts, kind, kind_ok?, index) do
    case Keyword.fetch(opts, :impl) do
      :error ->
        {nil, []}

      {:ok, impl} ->
        errors =
          []
          |> impl_kind_error(kind, kind_ok?, index)
          |> impl_alias_error(impl, index)

        if errors == [], do: {impl, []}, else: {nil, errors}
    end
  end

  defp impl_kind_error(errors, :exunit, true, _index), do: errors

  defp impl_kind_error(errors, _kind, true, index) do
    errors ++ ["modules entry #{index}: impl: is only valid for kind: :exunit"]
  end

  defp impl_kind_error(errors, _kind, false, _index), do: errors

  defp impl_alias_error(errors, impl, index) do
    if alias_atom?(impl) do
      errors
    else
      errors ++ ["modules entry #{index}: impl is not an alias atom, got: #{inspect(impl)}"]
    end
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
  # the same directory.
  defp canonical(path) do
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

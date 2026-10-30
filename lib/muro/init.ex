defmodule Muro.Init do
  @moduledoc """
  Create `muro.exs` and `priv/muro/` for `mix muro.init`.

  The manifest pins `muro:` to the running version and leaves
  `modules:` empty, with one commented example entry. An existing
  `muro.exs`, or a `:muro` key already in `mix.exs`, is left untouched.

  `ci: :github` also writes `.github/workflows/muro.yml`. The job sets
  up Elixir and OTP, installs this version of the archive from Hex, and
  runs `mix muro.gen --check`. The install line is

      mix archive.install hex muro <version> --force

  The version is the one in the manifest. `--force` skips the install
  question.

  Init prints a note for the project's agent instructions. It does
  not write that file.
  """

  @elixir "1.20.4"
  @otp "29.1"

  @doc """
  Write the manifest under `root`.

  `ci` is `nil` or `:github`. Returns `{:ok, lines, note}` or
  `{:error, message}`. `lines` names each file that was created.
  """
  def write(root, version, ci \\ nil)

  def write(root, version, ci)
      when is_binary(root) and is_binary(version) and ci in [nil, :github] do
    root = Path.expand(root)
    exs = Path.join(root, "muro.exs")
    workflow = Path.join(root, ".github/workflows/muro.yml")
    has_exs = File.regular?(exs)
    has_mix = match?({:ok, _value}, Muro.Manifest.mix_config(root))

    cond do
      has_exs and has_mix ->
        {:error,
         "refusing to overwrite an existing manifest: muro.exs and the :muro key in mix.exs"}

      has_exs ->
        {:error, "refusing to overwrite an existing manifest: muro.exs"}

      has_mix ->
        {:error, "refusing to overwrite an existing manifest: the :muro key in mix.exs"}

      ci == :github and File.regular?(workflow) ->
        {:error, "refusing to overwrite .github/workflows/muro.yml"}

      true ->
        File.mkdir_p!(Path.join(root, "priv/muro"))
        File.write!(exs, manifest_source(version))

        lines = ["created muro.exs", "created priv/muro/"]

        lines =
          if ci == :github do
            File.mkdir_p!(Path.dirname(workflow))
            File.write!(workflow, workflow(version))
            lines ++ ["created .github/workflows/muro.yml"]
          else
            lines
          end

        {:ok, lines, note()}
    end
  end

  @doc "The `muro.exs` init writes, pinned to `version`."
  def manifest_source(version) when is_binary(version) do
    """
    [
      muro: "#{version}",
      modules: [
        # {"priv/muro/rounding.muro", MyApp.Billing.Rounding, "lib/my_app/billing/rounding.ex"}
      ]
    ]
    """
  end

  @doc """
  The GitHub Actions workflow `mix muro.init --ci github` writes.

  Elixir #{@elixir} and OTP #{@otp} match this repository's `mise.toml`.
  """
  def workflow(version) when is_binary(version) do
    """
    name: muro

    on:
      push:
      pull_request:

    permissions:
      contents: read

    jobs:
      check:
        name: mix muro.gen --check
        runs-on: ubuntu-latest
        steps:
          - uses: actions/checkout@v5

          - uses: erlef/setup-beam@v1
            with:
              elixir-version: "#{@elixir}"
              otp-version: "#{@otp}"

          - name: Install the muro archive
            run: mix archive.install hex muro #{version} --force

          - name: Check generated modules
            run: mix muro.gen --check
    """
  end

  @doc """
  The note init prints. The caller pastes it into the project's
  agent instructions. Init does not write that file.
  """
  def note do
    """
    Generated files are not edited by hand. The .muro file is the source. Run mix muro.gen after changing it.
    Run `muro skills add` to write the commands for this project into AGENTS.md.
    """
  end

  @doc """
  What `muro init` writes.

  Looks at `root` and does one thing: a Mix project gets `muro.exs`
  and `priv/muro/`, a Cargo project gets `muro.toml` and `muro/`
  (or `[package.metadata.muro]` with `cargo_metadata: true`), a
  C project gets `muro.toml` and `muro/`, and anything else gets a
  minimal `muro.toml` and `muro/`. `backend` overrides the example.
  An existing manifest is left in place. The return is
  `{:ok, lines, note}`, `{:diff, text}`, or `{:error, message}`.
  """
  def scaffold(root, version, opts \\ [])

  def scaffold(root, version, opts)
      when is_binary(root) and is_binary(version) and is_list(opts) do
    root = Path.expand(root)
    ci = Keyword.get(opts, :ci)
    cargo? = Keyword.get(opts, :cargo_metadata, false)
    override = Keyword.get(opts, :backend)
    detected = detect(root)
    backend = override || detected.backend

    cond do
      cargo? and detected.kind != :cargo ->
        {:error, "--cargo-metadata applies to a directory with Cargo.toml"}

      ci not in [nil, :github] ->
        {:error, "unknown --ci #{ci}; expected github"}

      true ->
        place(root, version, detected.kind, backend, ci, cargo?)
    end
  end

  @doc "The `muro.toml` init writes, pinned to `version`."
  def toml_source(version, backend \\ nil)

  def toml_source(version, nil) when is_binary(version) do
    """
    muro = "#{version}"

    # [[modules]]
    # book = "muro/rounding.muro"
    # target = "src/rounding.rs"

    modules = []
    """
  end

  def toml_source(version, backend) when is_binary(version) and is_atom(backend) do
    {target, module} = example_paths(backend)

    module_line =
      if module do
        "# module = \"#{module}\"\n"
      else
        ""
      end

    """
    muro = "#{version}"
    backend = "#{backend}"

    # [[modules]]
    # book = "muro/rounding.muro"
    # target = "#{target}"
    #{module_line}modules = []
    """
  end

  @doc """
  The `[package.metadata.muro]` block `--cargo-metadata` appends.
  """
  def cargo_block(version, backend) when is_binary(version) do
    {target, module} = example_paths(backend || :rust)

    backend_line =
      if backend do
        "backend = \"#{backend}\"\n"
      else
        ""
      end

    module_line =
      if module do
        "# module = \"#{module}\"\n"
      else
        ""
      end

    """
    [package.metadata.muro]
    muro = "#{version}"
    #{backend_line}modules = []

    # [[package.metadata.muro.modules]]
    # book = "muro/rounding.muro"
    # target = "#{target}"
    #{module_line}
    """
  end

  @doc """
  The GitHub Actions workflow `muro init --ci github` writes.

  The job installs the self-contained `muro` binary at `version` and
  runs `muro gen --check`.
  """
  def binary_workflow(version) when is_binary(version) do
    """
    name: muro

    on:
      push:
      pull_request:

    permissions:
      contents: read

    jobs:
      check:
        name: muro gen --check
        runs-on: ubuntu-latest
        steps:
          - uses: actions/checkout@v5

          - name: Install muro #{version}
            run: |
              curl -fsSL -o muro "https://github.com/murolang/muro/releases/download/v#{version}/muro-#{version}-linux-x86_64"
              chmod +x muro
              sudo mv muro /usr/local/bin/muro

          - name: Check generated modules
            run: muro gen --check
    """
  end

  @doc "A unified diff of `current` and `proposed`, labeled `path`."
  def diff(path, current, proposed) when is_binary(path) do
    Muro.Diff.unified(path, current, proposed)
  end

  @doc "The backend `muro init` would pick for `root`, before an override."
  def detect_backend(root) when is_binary(root) do
    detect(Path.expand(root)).backend
  end

  defp place(root, version, kind, backend, ci, cargo?) do
    case existing(root, kind, cargo?) do
      nil ->
        write_new(root, version, kind, backend, ci, cargo?)

      {:file, rel, current} ->
        proposed = proposed_file(version, kind, backend, cargo?)
        {:diff, diff(rel, current, proposed)}

      {:cargo, current} ->
        proposed = proposed_cargo(current, version, backend)
        {:diff, diff("Cargo.toml", current, proposed)}
    end
  end

  defp write_new(root, version, kind, backend, ci, cargo?) do
    workflow = Path.join(root, ".github/workflows/muro.yml")

    if ci == :github and File.regular?(workflow) do
      {:error, "refusing to overwrite .github/workflows/muro.yml"}
    else
      lines = write_manifest(root, version, kind, backend, cargo?)

      lines =
        if ci == :github do
          File.mkdir_p!(Path.dirname(workflow))
          File.write!(workflow, binary_workflow(version))
          lines ++ ["created .github/workflows/muro.yml"]
        else
          lines
        end

      {:ok, lines, note()}
    end
  end

  defp write_manifest(root, version, :mix, backend, _cargo?) do
    File.mkdir_p!(Path.join(root, "priv/muro"))

    source =
      if backend in [nil, :elixir],
        do: manifest_source(version),
        else: exs_source(version, backend)

    File.write!(Path.join(root, "muro.exs"), source)
    ["created muro.exs", "created priv/muro/"]
  end

  defp write_manifest(root, version, :cargo, backend, true) do
    path = Path.join(root, "Cargo.toml")
    current = File.read!(path)
    File.write!(path, append_block(current, cargo_block(version, backend)))
    File.mkdir_p!(Path.join(root, "muro"))
    ["updated Cargo.toml", "created muro/"]
  end

  defp write_manifest(root, version, _kind, backend, _cargo?) do
    File.mkdir_p!(Path.join(root, "muro"))
    File.write!(Path.join(root, "muro.toml"), toml_source(version, backend))
    ["created muro.toml", "created muro/"]
  end

  defp proposed_file(version, :mix, backend, _cargo?) do
    if backend in [nil, :elixir], do: manifest_source(version), else: exs_source(version, backend)
  end

  defp proposed_file(version, _kind, backend, _cargo?), do: toml_source(version, backend)

  defp proposed_cargo(current, version, backend) do
    block = cargo_block(version, backend)

    if muro_header?(current) do
      replace_cargo_section(current, block)
    else
      append_block(current, block)
    end
  end

  defp existing(root, :mix, _cargo?) do
    path = Path.join(root, "muro.exs")
    if File.regular?(path), do: {:file, "muro.exs", File.read!(path)}, else: nil
  end

  defp existing(root, :cargo, true) do
    path = Path.join(root, "Cargo.toml")
    text = File.read!(path)
    if Muro.Toml.cargo_metadata?(text), do: {:cargo, text}, else: nil
  end

  defp existing(root, :cargo, false) do
    file_existing(root, "muro.toml")
  end

  defp existing(root, _kind, _cargo?), do: file_existing(root, "muro.toml")

  defp file_existing(root, rel) do
    path = Path.join(root, rel)
    if File.regular?(path), do: {:file, rel, File.read!(path)}, else: nil
  end

  defp detect(root) do
    cond do
      File.regular?(Path.join(root, "mix.exs")) ->
        %{kind: :mix, backend: :elixir}

      File.regular?(Path.join(root, "Cargo.toml")) ->
        %{kind: :cargo, backend: :rust}

      File.regular?(Path.join(root, "CMakeLists.txt")) or
        File.regular?(Path.join(root, "meson.build")) or
          File.regular?(Path.join(root, "Makefile")) ->
        %{kind: :c, backend: :c}

      true ->
        %{kind: :bare, backend: nil}
    end
  end

  defp example_paths(:elixir), do: {"lib/my_app/billing/rounding.ex", "MyApp.Billing.Rounding"}
  defp example_paths(:exunit), do: {"test/rounding_test.exs", "MyApp.Billing.RoundingTest"}

  defp example_paths(:fsm),
    do: {"lib/my_app/billing/rounding_fsm.ex", "MyApp.Billing.RoundingFsm"}

  defp example_paths(:c), do: {"src/rounding.c", nil}
  defp example_paths(:rust), do: {"src/rounding.rs", nil}
  defp example_paths(:asm), do: {"src/rounding.s", nil}
  defp example_paths(nil), do: {"src/rounding.rs", nil}

  defp exs_source(version, backend) do
    {target, module} = example_paths(backend)

    entry =
      if module do
        ~s|# {"priv/muro/rounding.muro", #{module}, "#{target}", [kind: :#{backend}]}|
      else
        ~s|# {"priv/muro/rounding.muro", "#{target}", [kind: :#{backend}]}|
      end

    """
    [
      muro: "#{version}",
      modules: [
        #{entry}
      ]
    ]
    """
  end

  defp append_block(current, block) do
    sep = if current == "" or String.ends_with?(current, "\n"), do: "", else: "\n"
    extra = if String.ends_with?(current, "\n\n") or current == "", do: "", else: "\n"
    current <> sep <> extra <> block
  end

  defp muro_header?(text) do
    text
    |> String.split("\n")
    |> Enum.any?(&muro_header_line?/1)
  end

  defp muro_header_line?(line) do
    line
    |> String.trim()
    |> String.match?(~r/^\[\[?package\.metadata\.muro(\.|\]|\])/)
  end

  defp outside_header?(line) do
    trimmed = String.trim(line)
    String.starts_with?(trimmed, "[") and not muro_header_line?(line)
  end

  defp replace_cargo_section(text, block) do
    lines = String.split(text, "\n")
    start = Enum.find_index(lines, &muro_header_line?/1)
    {prefix, rest} = Enum.split(lines, start)
    tail = Enum.drop(rest, 1)
    {section, suffix} = Enum.split_while(tail, &(not outside_header?(&1)))
    _ = section
    block_lines = block |> String.trim_trailing("\n") |> String.split("\n")
    body = prefix ++ block_lines ++ suffix
    joined = Enum.join(body, "\n")
    if String.ends_with?(text, "\n"), do: joined <> "\n", else: joined
  end
end

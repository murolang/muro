defmodule Muro do
  @moduledoc """
  Muro — a spec never becomes evidence. Evidence never becomes a run.

  An explicit affine dependent type theory: Elixir checks it, Agda specifies
  it, only run terms run.
  """

  alias Muro.{Emit, Load, Prelude}

  @doc """
  Parse and check a `.muro` file. Options: `fuel: n` (see `Muro.Check.check_sig/2`).

  The prelude is in scope behind the file. A name the file defines replaces
  the prelude's. `import "path"` loads that file, relative to this one, and
  brings its declarations into scope. `import "pkg:name/file.muro"` loads
  that file from `muro_deps/`. `root:` is the project root; when it is
  omitted, the nearest ancestor with `muro.exs` or `mix.exs` is used.
  """
  def check_file(path, opts \\ []) do
    with {:ok, _} <- Load.file(path, opts), do: :ok
  end

  @doc """
  `conforms to <package> <version> (sha256 <hash>)` for each package
  `path` loaded, in name order. The hash covers the package files this
  book loaded, not the whole package. `{:ok, []}` when the book imports
  no package. `{:error, message}` when the book does not check.
  """
  def conforms(path, opts \\ []) do
    case Load.open(path, opts) do
      {:ok, _book, lines} -> {:ok, lines}
      {:error, _} = err -> err
    end
  end

  @doc """
  Emit the `run` definitions of `path` as an Elixir module named `module`.

  `module` is the name in the source (`MyApp.Billing.Rounding` is
  `defmodule MyApp.Billing.Rounding`). It is not taken from the file
  stem. `opts` is `fuel: n`, as in `check_file/2`. A book that does
  not check returns `{:error, message}` and no module.
  Definitions imported from a package are inlined the same way as
  definitions imported from a file.
  """
  def emit_file(path, module, opts \\ []) when is_atom(module) do
    with {:ok, book} <- checked_book(path, opts) do
      {:ok, Emit.emit_module(module, book)}
    end
  end

  @doc """
  Emit the closed equations of `path` as an ExUnit module named `module`.

  `module` is the test module (`MyApp.RoundingTest`). The implementation
  under test defaults to the name `mix muro.emit` would give the book,
  unless `opts` sets `impl:`. `opts` also accepts `fuel:`, `root:`, and
  `book:` (the path printed in test names; relative, `/` separators).

  Returns `{:ok, %{source: source, skips: skips, tests: n}}`. `skips`
  are the equations the suite lists and does not run. A book that does
  not check returns `{:error, message}` and no module.

  This is the one entry point that loads with `params: :open`. A `param`
  nobody supplied is an assumption, so a library of params can be the
  suite. Every other backend still refuses that library. `imports: true`
  also collects closed equations from the files this book imports
  directly. The default is `false`.

  The bytes compare emitted shapes. Host data arrives with `repr` (#131),
  in `Muro.Emit.emit_closed/2`.
  """
  def emit_exunit(path, module, opts \\ []) when is_atom(module) do
    fuel = Keyword.get(opts, :fuel, Muro.Check.default_fuel())

    load_opts = [fuel: fuel, root: Keyword.get(opts, :root), params: :open]

    with {:ok, book} <- Load.file(path, load_opts) do
      Emit.ExUnitSuite.render(path, module, book, Keyword.put(opts, :fuel, fuel))
    end
  end

  @doc """
  Write `<name>.h` and `<name>.c` next to `path` for its run definitions.
  A `run` stream is a seed, an environment, and a step. Machine tensors
  are refused (`c:machine`).

  An exported run whose live arguments and result are `Nat` is also a NIF.
  `elixir_make` builds `priv/<name>.so`, and `<name>.ex` loads it.
  Without `elixir_make`, that NIF is refused before any file is written.
  `nif: false` writes the `.h` and the `.c` and does not build a NIF.
  The C bytes are the same either way.
  """
  def emit_c(path, opts \\ []) do
    nif? = Keyword.get(opts, :nif, true)
    stem = Path.basename(path, ".muro")
    dir = Path.dirname(path)

    with {:ok, book} <- checked_book(path, opts),
         {:ok, header, source, sigs} <- Emit.C.prepare(book, stem) do
      if nif?, do: Emit.Nif.ensure_make!(sigs), else: :ok
      h = Path.join(dir, stem <> ".h")
      c = Path.join(dir, stem <> ".c")
      File.write!(h, header)
      File.write!(c, source)
      extra = if nif?, do: Emit.Nif.build(dir, stem, sigs), else: []
      {:ok, [h, c | extra]}
    end
  end

  @doc """
  Write `<name>.rs` next to `path` for its run definitions.
  `rustc` translates that file. The proof stops at the run image.
  """
  def emit_rust(path, opts \\ []) do
    stem = Path.basename(path, ".muro")
    dir = Path.dirname(path)

    with {:ok, book} <- checked_book(path, opts),
         {:ok, source} <- Emit.Rust.render(book, stem) do
      rs = Path.join(dir, stem <> ".rs")
      File.write!(rs, source)
      {:ok, [rs]}
    end
  end

  @doc """
  Write `<name>.s` next to `path` for a closed Nat run.
  The assembler translates that file. The proof stops at the run image.
  """
  def emit_asm(path, opts \\ []) do
    stem = Path.basename(path, ".muro")
    dir = Path.dirname(path)

    with {:ok, book} <- checked_book(path, opts),
         {:ok, source} <- Emit.Asm.render(book, stem) do
      s = Path.join(dir, stem <> ".s")
      File.write!(s, source)
      {:ok, [s]}
    end
  end

  @doc """
  Elixir source for each session of `path`, as a pure state machine.

  `module` is the parent (`MeetFsm`). One child module per session is
  the API. Nothing is written next to the book: a manifest entry needs
  the source as a string. `opts` is `fuel:`, `root:`, and `book:` (the
  label printed in a step). A book that does not check returns
  `{:error, message}`. A library of unsupplied `param`s is refused,
  as for `emit_file/3`.
  """
  def emit_fsm(path, module, opts \\ []) when is_atom(module) do
    with {:ok, book} <- checked_book(path, opts) do
      Emit.Fsm.render(book, path, module, opts)
    end
  end

  @doc """
  Write `<stem>_otp.ex` next to `path`. Each conforming process is a
  GenServer that talks to one peer pid. A `read` is that same
  process. The place stays on the reading. The BEAM runs that
  server. The proof stops at the conformance derivation.
  """
  def emit_otp(path, opts \\ []) do
    stem = Path.basename(path, ".muro")
    dir = Path.dirname(path)

    with {:ok, book} <- checked_book(path, opts),
         {:ok, source} <- Emit.Otp.render(book, stem) do
      file = Path.join(dir, stem <> "_otp.ex")
      File.write!(file, source)
      {:ok, [file]}
    end
  end

  @doc """
  Write `<stem>_node.ex` next to `path`. Each `cross` is one
  `GenServer.call({name, node}, {:muro_read, scheme}, timeout)`.
  A `move cross` names the scheme. A `read cross` uses the scheme
  the endpoint names. `name` is that scheme, registered on `node`.
  The monitor of that name is installed first. A `stay` emits no
  call. The payload stays on the session. The BEAM runs the call.
  The proof stops at the move.
  """
  def emit_node(path, node, opts \\ []) when is_atom(node) do
    stem = Path.basename(path, ".muro")
    dir = Path.dirname(path)

    with {:ok, book} <- checked_book(path, opts),
         {:ok, source} <- Emit.Node.render(book, stem, node) do
      file = Path.join(dir, stem <> "_node.ex")
      File.write!(file, source)
      {:ok, [file]}
    end
  end

  defp checked_book(path, opts) do
    with {:ok, book} <- Load.file(path, opts) do
      {:ok, Prelude.for_emit(book)}
    end
  end
end

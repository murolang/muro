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
  brings its declarations into scope.
  """
  def check_file(path, opts \\ []) do
    with {:ok, _} <- Load.file(path, opts), do: :ok
  end

  def emit_file(path, module, opts \\ []) when is_atom(module) do
    with {:ok, book} <- checked_book(path, opts) do
      {:ok, Emit.emit_module(module, book)}
    end
  end

  @doc """
  Write `<name>.h` and `<name>.c` next to `path` for its run definitions.
  A `run` stream is a seed, an environment, and a step. Machine tensors
  are refused (`c:machine`).
  """
  def emit_c(path, opts \\ []) do
    stem = Path.basename(path, ".muro")
    dir = Path.dirname(path)

    with {:ok, book} <- checked_book(path, opts),
         {:ok, {header, source}} <- Emit.C.render(book, stem) do
      h = Path.join(dir, stem <> ".h")
      c = Path.join(dir, stem <> ".c")
      File.write!(h, header)
      File.write!(c, source)
      {:ok, [h, c]}
    end
  end

  defp checked_book(path, opts) do
    with {:ok, book} <- Load.file(path, opts) do
      {:ok, Prelude.for_emit(book)}
    end
  end
end

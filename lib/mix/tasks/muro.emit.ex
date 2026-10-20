defmodule Mix.Tasks.Muro.Emit do
  use Mix.Task

  @shortdoc "Emit run definitions as Elixir, C, Rust, or Cortex-M assembly"

  @moduledoc """
  Emit the `run` definitions of a `.muro` file.

      mix muro.emit path.muro
      mix muro.emit path.muro --backend elixir
      mix muro.emit path.muro --backend c
      mix muro.emit path.muro --backend rust
      mix muro.emit path.muro --backend asm

  The default backend is Elixir, the same text as `Muro.emit_file/3`.
  The module name is the file stem (`half_ok.muro` becomes `HalfOk`).

  `--backend c` writes `<name>.h` and `<name>.c` next to the file and
  prints those paths. A `run` stream is emitted. Tensors are refused.
  An exported `Nat` run is also a NIF.

  `--backend rust` writes `<name>.rs` next to the file and prints that
  path. `rustc` translates it. The proof stops at the run image.

  `--backend asm` writes `<name>.s` next to the file and prints that
  path. The text is Thumb for Cortex-M0, for a closed `Nat` run.
  The assembler translates it. The proof stops at the run image.
  """

  @switches [backend: :string]

  def run(args) do
    Mix.Task.run("app.start")

    {opts, paths, invalid} = OptionParser.parse(args, strict: @switches)

    if invalid != [] do
      Mix.raise("unknown option: #{inspect(invalid)}")
    end

    backend = Keyword.get(opts, :backend, "elixir")

    case paths do
      [path] -> emit(path, backend)
      _ -> Mix.raise("expected one path")
    end
  end

  defp emit(path, "elixir") do
    case Muro.emit_file(path, module_name(path)) do
      {:ok, src} -> Mix.shell().info(src)
      {:error, e} -> Mix.raise(e)
    end
  end

  defp emit(path, "c") do
    case Muro.emit_c(path) do
      {:ok, files} -> Enum.each(files, fn path -> Mix.shell().info(path) end)
      {:error, e} -> Mix.raise(e)
    end
  end

  defp emit(path, "rust") do
    case Muro.emit_rust(path) do
      {:ok, files} -> Enum.each(files, fn path -> Mix.shell().info(path) end)
      {:error, e} -> Mix.raise(e)
    end
  end

  defp emit(path, "asm") do
    case Muro.emit_asm(path) do
      {:ok, files} -> Enum.each(files, fn path -> Mix.shell().info(path) end)
      {:error, e} -> Mix.raise(e)
    end
  end

  defp emit(_path, other) do
    Mix.raise("unknown backend: #{other}")
  end

  defp module_name(path) do
    path
    |> Path.basename(".muro")
    |> String.replace("-", "_")
    |> Macro.camelize()
    |> List.wrap()
    |> Module.concat()
  end
end

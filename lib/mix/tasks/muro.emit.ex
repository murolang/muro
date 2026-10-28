defmodule Mix.Tasks.Muro.Emit do
  use Mix.Task

  @shortdoc "Emit run definitions as Elixir, C, Rust, or Cortex-M assembly, a session as OTP, a cross as a call, or closed equations as ExUnit"

  @moduledoc """
  Emit the `run` definitions of a `.muro` file.

      mix muro.emit path.muro
      mix muro.emit path.muro --backend elixir
      mix muro.emit path.muro --backend c
      mix muro.emit path.muro --backend rust
      mix muro.emit path.muro --backend asm
      mix muro.emit path.muro --backend otp
      mix muro.emit path.muro --backend exunit
      mix muro.emit path.muro --node a

  The default backend is Elixir, the same text as `Muro.emit_file/3`.
  The module name is the file stem (`half_ok.muro` becomes `HalfOk`).

  `--backend exunit` prints one ExUnit module for the book's closed
  equations, the same text as `Muro.emit_exunit/3`. The test module is
  the file stem plus `Test` (`rounding.muro` is `RoundingTest`). The
  implementation it calls by default is the stem module (`Rounding`).
  The suite reads `Application.get_env(:muro, TestModule, DefaultImpl)`
  in `setup_all`. The key is the test module. Skipped equations are
  listed on standard error, then a line `N tests, M skipped`. Standard
  output is only the module. `--node` with this backend is refused.

  `--backend c` writes `<name>.h` and `<name>.c` next to the file and
  prints those paths. A `run` stream is emitted. Tensors are refused.
  An exported `Nat` run is also a NIF.

  `--backend rust` writes `<name>.rs` next to the file and prints that
  path. `rustc` translates it. The proof stops at the run image.

  `--backend asm` writes `<name>.s` next to the file and prints that
  path. The text is Thumb for Cortex-M0, for a closed `Nat` run.
  The assembler translates it. The proof stops at the run image.

  `--backend otp` writes `<stem>_otp.ex` next to the file and prints
  that path. Each conforming process is a GenServer, and so is each
  reading. The server talks to one peer. The message carries the
  value. The place stays on the reading. The BEAM runs that server.
  The proof stops at the conformance derivation.

  `--node` writes `<stem>_node.ex` next to the file and prints that
  path. `place.muro` with `--node a` is `place_node.ex`. Each `cross`
  is one call to the scheme, registered on that node, after a monitor
  of the same name. A `read cross` calls the scheme its endpoint
  names. A `stay` emits no call. The payload stays on the session.
  The BEAM runs the call. The proof stops at the move.

  A NIF (`--backend c` on an exported `Nat` run) needs `elixir_make`.
  Without it, the task stops and names the dependency to add.
  """

  @switches [backend: :string, node: :string]

  def run(args) do
    Mix.Tasks.Muro.ensure_started()

    {opts, paths, invalid} = OptionParser.parse(args, strict: @switches)

    if invalid != [] do
      Mix.raise("unknown option: #{inspect(invalid)}")
    end

    backend = Keyword.get(opts, :backend, "elixir")
    node = Keyword.get(opts, :node)

    case paths do
      [path] -> emit(path, backend, node)
      _ -> Mix.raise("expected one path")
    end
  end

  defp emit(path, "elixir", node) when is_binary(node) do
    case Muro.emit_node(path, node_atom(node)) do
      {:ok, files} -> Enum.each(files, fn file -> Mix.shell().info(file) end)
      {:error, e} -> Mix.raise(e)
    end
  end

  defp emit(_path, _backend, node) when not is_nil(node) do
    Mix.raise("--node writes the placement calls")
  end

  defp emit(path, "elixir", nil) do
    case Muro.emit_file(path, module_name(path)) do
      {:ok, src} -> Mix.shell().info(src)
      {:error, e} -> Mix.raise(e)
    end
  end

  defp emit(path, "c", nil) do
    case Muro.emit_c(path) do
      {:ok, files} -> Enum.each(files, fn path -> Mix.shell().info(path) end)
      {:error, e} -> Mix.raise(e)
    end
  end

  defp emit(path, "rust", nil) do
    case Muro.emit_rust(path) do
      {:ok, files} -> Enum.each(files, fn path -> Mix.shell().info(path) end)
      {:error, e} -> Mix.raise(e)
    end
  end

  defp emit(path, "asm", nil) do
    case Muro.emit_asm(path) do
      {:ok, files} -> Enum.each(files, fn path -> Mix.shell().info(path) end)
      {:error, e} -> Mix.raise(e)
    end
  end

  defp emit(path, "otp", nil) do
    case Muro.emit_otp(path) do
      {:ok, files} -> Enum.each(files, fn path -> Mix.shell().info(path) end)
      {:error, e} -> Mix.raise(e)
    end
  end

  defp emit(path, "exunit", nil) do
    case Muro.emit_exunit(path, Muro.Emit.exunit_module(path)) do
      {:ok, %{source: src, skips: skips, tests: n}} ->
        Enum.each(skips, fn skip ->
          IO.puts(:stderr, "skipped #{skip.name} (#{skip.file}:#{skip.line}): #{skip.reason}")
        end)

        IO.puts(:stderr, "#{n} tests, #{length(skips)} skipped")
        Mix.shell().info(src)

      {:error, e} ->
        Mix.raise(e)
    end
  end

  defp emit(_path, other, nil) do
    Mix.raise("unknown backend: #{other}")
  end

  defp node_atom(name) do
    if name =~ ~r/^[A-Za-z_][A-Za-z0-9_@.-]*$/ do
      String.to_atom(name)
    else
      Mix.raise("expected a node name")
    end
  end

  defp module_name(path), do: Muro.Emit.elixir_module(path)
end

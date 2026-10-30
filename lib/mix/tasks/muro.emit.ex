defmodule Mix.Tasks.Muro.Emit do
  use Mix.Task

  @shortdoc "Emit run definitions as Elixir, C, Rust, or Cortex-M assembly, a session as OTP or a state machine, a cross as a call, or closed equations as ExUnit"

  @moduledoc """
  Emit the `run` definitions of a `.muro` file.

      mix muro.emit path.muro
      mix muro.emit path.muro --backend elixir
      mix muro.emit path.muro --backend c
      mix muro.emit path.muro --backend rust
      mix muro.emit path.muro --backend asm
      mix muro.emit path.muro --backend otp
      mix muro.emit path.muro --backend fsm
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

  A file with `param`s is refused by every backend except `exunit`.
  `--backend exunit` checks those params as assumptions and emits the
  closed equations. `--imports` with `--backend exunit` also collects
  the closed equations of the files this book imports directly. It is
  an error with any other backend. Absent, the suite is this file only.

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

  `--backend fsm` prints one module on standard output. The module
  name is the stem plus `Fsm` (`meet.muro` is `MeetFsm`). Each session
  is a child module of pure functions. The host keeps the transport.
  Nothing is written next to the book.

  `--node` writes `<stem>_node.ex` next to the file and prints that
  path. `place.muro` with `--node a` is `place_node.ex`. Each `cross`
  is one call to the scheme, registered on that node, after a monitor
  of the same name. A `read cross` calls the scheme its endpoint
  names. A `stay` emits no call. The payload stays on the session.
  The BEAM runs the call. The proof stops at the move.

  A NIF (`--backend c` on an exported `Nat` run) needs `elixir_make`.
  Without it, the task stops and names the dependency to add.
  """

  def run(args) do
    Mix.Tasks.Muro.ensure_started()
    Muro.CLI.Output.mix(Muro.CLI.Emit.run(args, nif: :force))
  end
end

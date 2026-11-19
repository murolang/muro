defmodule Mix.Tasks.Muro.Fill do
  use Mix.Task

  @shortdoc "Fill one definition body by type-directed search"

  @moduledoc """
  Fill one definition body by type-directed search.

      mix muro.fill path.muro --def name
      mix muro.fill path.muro --def name --bound 8

  The definition starts as `?`. The search tries terms in order of size.
  The checker decides. A run is kept only when the book's closed equations
  about that name still check. Evidence is kept when the type checks, and
  a spec is kept the same way. The written text is checked again, then a
  rename in the same directory puts it in place.
  Past `--bound` (default #{Muro.Fill.default_bound()}) the file is left
  unchanged and the task exits non-zero.

  This is a search. It is not `mix muro.synth`, and it certifies nothing
  beyond the checker. The manual page is `manual/fill.md`.
  """

  def run(args) do
    Mix.Tasks.Muro.ensure_started()
    Muro.CLI.Output.mix(Muro.CLI.Fill.run(args))
  end
end

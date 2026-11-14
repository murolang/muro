defmodule Muro.UnmarkedEmitTest do
  use ExUnit.Case, async: true

  @books ~w(ping meet indexed)

  for stem <- @books do
    @stem stem

    test "#{stem} otp, fsm, and elixir match a meeting with no failure mark" do
      stem = @stem
      path = "examples/#{stem}.muro"
      {:ok, book} = Muro.Load.file(path)
      book = Muro.Prelude.for_emit(book)

      assert {:ok, otp} = Muro.Emit.Otp.render(book, stem)
      assert File.read!("test/fixtures/unmarked/#{stem}.otp.ex.golden") == otp

      fsm_mod = Module.concat([Macro.camelize(stem) <> "Fsm"])
      assert {:ok, fsm} = Muro.Emit.Fsm.render(book, path, fsm_mod)
      assert File.read!("test/fixtures/unmarked/#{stem}.fsm.ex.golden") == fsm

      elixir = Muro.Emit.emit_module(Module.concat([Macro.camelize(stem)]), book)
      assert File.read!("test/fixtures/unmarked/#{stem}.ex.golden") == elixir
    end
  end
end

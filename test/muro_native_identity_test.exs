defmodule Muro.NativeIdentityTest do
  use ExUnit.Case, async: true

  @books ~w(ping bytes half_ok fnv_slice)

  for stem <- @books do
    @stem stem

    test "#{stem} emit matches the image from 0.21.0" do
      stem = @stem
      path = "examples/#{stem}.muro"
      dir = Path.join("test/fixtures/native-main", stem)
      {:ok, book} = Muro.Load.file(path)
      book = Muro.Prelude.for_emit(book)

      assert {:ok, header, source, _sigs} = Muro.Emit.C.prepare(book, stem)
      assert File.read!(Path.join(dir, stem <> ".h")) == header
      assert File.read!(Path.join(dir, stem <> ".c")) == source

      assert {:ok, rs} = Muro.Emit.Rust.render(book, stem)
      assert File.read!(Path.join(dir, stem <> ".rs")) == rs

      assert {:ok, zg} = Muro.Emit.Zig.render(book, stem)
      assert File.read!(Path.join(dir, stem <> ".zig")) == zg

      elixir = Muro.Emit.emit_module(Module.concat([Macro.camelize(stem)]), book)
      assert File.read!(Path.join(dir, stem <> ".ex.golden")) == elixir

      assert {:ok, js, dts} = Muro.Emit.JS.render(book, stem, path: path)
      assert File.read!(Path.join(dir, stem <> ".mjs")) == js
      assert File.read!(Path.join(dir, stem <> ".d.ts")) == dts

      case Muro.Emit.Asm.render(book, stem) do
        {:ok, s} ->
          assert File.read!(Path.join(dir, stem <> ".s")) == s

        {:error, "asm:scope"} ->
          refute File.regular?(Path.join(dir, stem <> ".s"))

        other ->
          flunk(inspect(other))
      end
    end
  end
end

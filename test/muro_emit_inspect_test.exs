defmodule Muro.EmitInspectTest do
  use ExUnit.Case, async: true

  # Elixir's inspect/2 defaults: printable_limit 4096, limit 50 (non-printable).
  @len 5000

  test "Elixir emits a Bytes, Slice, or String literal past inspect's limits" do
    ascii = String.duplicate("a", @len)
    raw = binary_part(:binary.copy(<<0, 1, 2, 255>>, div(@len, 4) + 1), 0, @len)

    book = """
    def ascii_bytes : run Bytes := #{Muro.Print.quote_bytes(ascii)}
    def ascii_slice : run Slice := #{Muro.Print.quote_bytes(ascii)}
    def raw_bytes : run Bytes := #{Muro.Print.quote_bytes(raw)}
    def raw_slice : run Slice := #{Muro.Print.quote_bytes(raw)}
    def ascii_string : run String := #{Muro.Print.quote_string(ascii)}
    """

    dir = tmp("inspect")
    path = Path.join(dir, "wide.muro")
    File.write!(path, book)
    assert Muro.check_file(path) == :ok

    mod = Module.concat(Muro.EmitInspectProbe, "M#{System.unique_integer([:positive])}")
    assert {:ok, src} = Muro.emit_file(path, mod)

    full = fn bin -> inspect(bin, limit: :infinity, printable_limit: :infinity) end
    clipped = fn bin -> inspect(bin) end

    assert String.contains?(clipped.(ascii), "...")
    assert String.contains?(clipped.(raw), "...")
    refute String.contains?(full.(ascii), "...")
    refute String.contains?(full.(raw), "...")

    assert src =~ full.(ascii)
    assert src =~ full.(raw)
    refute src =~ clipped.(ascii)
    refute src =~ clipped.(raw)

    [{^mod, _bin}] = Code.compile_string(src)

    on_exit(fn ->
      :code.delete(mod)
      :code.purge(mod)
    end)

    assert apply(mod, :ascii_bytes, []) == ascii
    assert apply(mod, :ascii_slice, []) == ascii
    assert apply(mod, :raw_bytes, []) == raw
    assert apply(mod, :raw_slice, []) == raw
    assert apply(mod, :ascii_string, []) == ascii
    assert byte_size(apply(mod, :ascii_bytes, [])) == @len
    assert byte_size(apply(mod, :raw_slice, [])) == @len
  end

  defp tmp(tag) do
    dir =
      Path.join(
        System.tmp_dir!(),
        "muro_emit_inspect_#{tag}_#{System.unique_integer([:positive])}"
      )

    File.mkdir_p!(dir)
    on_exit(fn -> File.rm_rf!(dir) end)
    dir
  end
end

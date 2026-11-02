defmodule Muro.OutlineTest do
  use ExUnit.Case, async: true

  alias Muro.{Emit, IR, Load, Prelude}

  test "each outline is the code that backend emits" do
    meet = book("examples/meet.muro")
    half = book("examples/half_ok.muro")

    for {label, b, stem} <- [{"meet", meet, "meet"}, {"half_ok", half, "half_ok"}] do
      for backend <- [:c, :rust, :zig] do
        assert {:ok, outline} = Emit.outline(backend, b, stem)
        src = flatten(backend, b, stem)
        assert outline.elixir == Emit.elixir_names(b)
        assert_substrings(outline, src, "#{backend} #{label}")
        assert_ir(outline, b, "#{backend} #{label}")
      end
    end

    assert {:ok, otp} = Emit.outline(:otp, meet, "meet")
    assert {:ok, otp_src} = Muro.Emit.Otp.render(meet, "meet")
    assert otp.elixir == Emit.elixir_names(meet)
    assert_substrings(otp, otp_src, "otp meet")
    assert otp.clauses |> Enum.any?(&String.contains?(&1, "handle_info"))
    assert otp.clauses |> Enum.any?(&String.contains?(&1, "handle_call"))

    path = "examples/meet.muro"
    assert {:ok, fsm} = Emit.outline(:fsm, meet, path)
    assert {:ok, fsm_src} = Muro.Emit.Fsm.render(meet, path, Emit.fsm_module(path))
    assert fsm.elixir == Emit.elixir_names(meet)
    assert_substrings(fsm, fsm_src, "fsm meet")
    assert fsm_src =~ "unquote(:send)"

    assert {:error, msg} = Emit.outline(:fsm, half, "examples/half_ok.muro")
    assert msg =~ "no session"
  end

  defp book(path) do
    assert {:ok, user} = Load.file(path)
    Prelude.for_emit(user)
  end

  defp flatten(:c, book, stem) do
    assert {:ok, {header, source}} = Muro.Emit.C.render(book, stem)
    header <> "\n" <> source
  end

  defp flatten(:rust, book, stem) do
    assert {:ok, source} = Muro.Emit.Rust.render(book, stem)
    source
  end

  defp flatten(:zig, book, stem) do
    assert {:ok, source} = Muro.Emit.Zig.render(book, stem)
    source
  end

  defp assert_substrings(outline, src, label) do
    for name <- outline.names do
      assert is_binary(name) and name != ""
      assert src =~ name, "#{label} name #{name} is not in the source"
    end

    for clause <- outline.clauses do
      assert is_binary(clause) and clause != ""
      assert src =~ clause, "#{label} clause #{clause} is not in the source"
    end
  end

  defp assert_ir(outline, book, label) do
    assert {:ok, funs} = IR.elaborate(book)
    assert {:ok, groups, _} = Emit.partition_funs(funs, Emit.run_defs(book))

    for sig <- outline.signatures do
      fun = Enum.find(groups, fn {fun, _} -> fun.name == sig.source end)
      assert {got, _} = fun
      assert sig.layout == got.ret, label
      assert sig.param_layouts == Enum.map(got.params, fn {_n, lay} -> lay end), label
    end
  end
end

defmodule Muro.Emit.NatPrim do
  @moduledoc """
  Library `Nat` runs whose Elixir body is the host integer operation.

  A `Nat` is a non-negative integer in emitted Elixir, so the checked
  recursion of `plus` would still take one call per unit. A run whose
  name, type, and body are exactly a library definition's is emitted as
  the integer operation that definition computes. A file that redefines
  the name, or a mutant of the body, is not that definition and keeps the
  emitted recursion.

  The replacement is trusted: the emitted body is not the checked term.
  `agda/Muro/NatPrim.agda` proves, under `--safe`, that each operation
  below, read over ℤ, equals a clause-for-clause transcription of its
  library definition at every natural number. The transcription is not
  checked against the `.muro` text, and Elixir integer arithmetic being
  ℤ arithmetic is assumed. The emitted function is guarded to take only
  non-negative integers. `test/muro_emit_nat_test.exs` compares each
  operation with the emitted recursion as a regression test.
  """

  alias Muro.{Ast, Grade, Parser, Prelude, Std}

  @key {__MODULE__, :library}

  # {source book, name, Elixir body over x0, x1}
  @prims [
    {:prelude, "pred", "Kernel.max(x0 - 1, 0)"},
    {:prelude, "plus", "x0 + x1"},
    {"le.muro", "max", "Kernel.max(x0, x1)"},
    {"le.muro", "min", "Kernel.min(x0, x1)"},
    {"le.muro", "minus", "Kernel.max(x0 - x1, 0)"},
    {"ord.muro", "compare", "cond do\n  x0 < x1 -> :lt\n  x0 == x1 -> :eq\n  true -> :gt\nend"}
  ]

  @doc """
  `{:ok, params, body}` when `decl` is a library definition with a host
  body, otherwise `:error`. `params` are the Elixir parameter names.
  """
  def body(%{name: name, type: ty, body: body}) do
    with {:ok, {lib_ty, lib_body, src}} <- Map.fetch(library(), name),
         {:ok, ^lib_ty} <- Ast.to_db(ty),
         {:ok, ^lib_body} <- Ast.to_db(body) do
      {:ok, params(lib_ty), src}
    else
      _ -> :error
    end
  end

  def body(_decl), do: :error

  defp params(ty), do: ty |> arity(0) |> then(&Enum.map(0..(&1 - 1)//1, fn i -> "x#{i}" end))

  defp arity({:pi, _, _, _, b}, n), do: arity(b, n + 1)
  defp arity(_, n), do: n

  defp library do
    case :persistent_term.get(@key, nil) do
      nil ->
        lib = load()
        :persistent_term.put(@key, lib)
        lib

      lib ->
        lib
    end
  end

  defp load do
    books = %{prelude: Prelude.book()}

    books =
      for {src, _, _} <- @prims, src != :prelude, reduce: books do
        acc -> Map.put_new_lazy(acc, src, fn -> parse_std(src) end)
      end

    Map.new(@prims, fn {src, name, elixir} ->
      decl = books |> Map.fetch!(src) |> Grade.erase_book() |> Enum.find(&(&1[:name] == name))
      {:ok, ty} = Ast.to_db(decl.type)
      {:ok, body} = Ast.to_db(decl.body)
      {name, {ty, body, elixir}}
    end)
  end

  defp parse_std(name) do
    {:ok, source} = Std.source(name)
    {:ok, book} = Parser.parse(source)
    book
  end
end

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
  library definition at every natural number. Each bundled definition's
  de Bruijn type and body is pinned here, so an edit of the prelude or
  standard library fails loudly and points at that transcription. Elixir
  integer arithmetic being ℤ arithmetic, and the guard that admits only
  non-negative integers, remain the trust. `test/muro_emit_nat_test.exs`
  compares each operation with the emitted recursion as a regression
  test, and checks the pins.
  """

  alias Muro.{Ast, Grade, Hash, Parser, Prelude, Std}

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

  # SHA-256 of a canonical encoding of `{type, body}` for each library
  # definition, as `Ast.to_db/1` produces it. The encoding is a tagged
  # iodata walk, not `:erlang.term_to_binary`, so the digest is stable
  # across Elixir and OTP releases and changes when the type or body
  # does. A mismatch means the bundled definition drifted from the
  # transcription in `agda/Muro/NatPrim.agda`.
  @pins %{
    "pred" => "02aee20788b297e42c824e19a7e7dcd29dee8911cafb408fd1611e92e8b0be39",
    "plus" => "ded3c010a3818d6da10d8bd182e1d6e574c68b397415849c5c7aa75c89693d6a",
    "max" => "8a84eba23fbb0c7144a0fd47320efe244795d70cb1df7b969ad9e1c059ca7ec3",
    "min" => "3e82ac2fb4c859ac4af5ccd6d79d493ac508c1d0efade3d24a09a9cedeedd4f3",
    "minus" => "b492fe129ca23272622f5e1fd1b0a3c1ff1887994bf49ea388b355eb050f3352",
    "compare" => "a5106a8860bffb32667b1d7cc278a2289fe095cc4b072b174afb7d7c1e08871e"
  }

  @pin_names @pins |> Map.keys() |> Enum.sort()
  @prim_names @prims |> Enum.map(&elem(&1, 1)) |> Enum.sort()

  if @pin_names != @prim_names do
    raise "Muro.Emit.NatPrim pins and prims disagree: #{inspect(@pin_names)} vs #{inspect(@prim_names)}"
  end

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

  @doc """
  Lowercase hex SHA-256 of a canonical encoding of the de Bruijn
  `{type, body}`.
  """
  def digest({type, body}), do: Hash.sha256(encode({type, body}))

  @doc """
  `:ok` when every pinned library definition in `lib` matches its pin,
  otherwise `{:error, message}`. The message names the drifted
  definition and points at `agda/Muro/NatPrim.agda`.

  `lib` is a map of `name => {type, body}` or
  `name => {type, body, elixir}`. `verify_pins/0` checks the bundled
  library.
  """
  def verify_pins(), do: verify_pins(library())

  def verify_pins(lib) when is_map(lib) do
    Enum.reduce_while(expected_names(), :ok, fn name, :ok ->
      case entry(lib, name) do
        {:ok, {ty, body}} ->
          if digest({ty, body}) == Map.fetch!(@pins, name) do
            {:cont, :ok}
          else
            {:halt, {:error, drift_message(name)}}
          end

        :error ->
          {:halt, {:error, drift_message(name)}}
      end
    end)
  end

  @doc """
  Raises if a bundled or supplied library definition does not match its
  pin. See `verify_pins/1`.
  """
  def verify_pins!(), do: verify_pins!(library())

  def verify_pins!(lib) when is_map(lib) do
    case verify_pins(lib) do
      :ok -> :ok
      {:error, message} -> raise ArgumentError, message
    end
  end

  @doc false
  def library_defs, do: library()

  defp entry(lib, name) do
    case Map.fetch(lib, name) do
      {:ok, {ty, body, _elixir}} -> {:ok, {ty, body}}
      {:ok, {ty, body}} -> {:ok, {ty, body}}
      :error -> :error
    end
  end

  defp expected_names, do: Enum.map(@prims, &elem(&1, 1))

  defp drift_message(name) do
    "library definition #{name} no longer matches its pin; " <>
      "update the transcription and proof in agda/Muro/NatPrim.agda together with this pin"
  end

  defp encode(atom) when is_atom(atom), do: ["A", Atom.to_string(atom), 0]
  defp encode(n) when is_integer(n), do: ["I", Integer.to_string(n), 0]
  defp encode(bin) when is_binary(bin), do: ["B", Integer.to_string(byte_size(bin)), 0, bin]

  defp encode(list) when is_list(list) do
    ["L", Integer.to_string(length(list)), 0 | Enum.map(list, &encode/1)]
  end

  defp encode(tuple) when is_tuple(tuple) do
    ["T", Integer.to_string(tuple_size(tuple)), 0 | Enum.map(Tuple.to_list(tuple), &encode/1)]
  end

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

    lib =
      Map.new(@prims, fn {src, name, elixir} ->
        decl = books |> Map.fetch!(src) |> Grade.erase_book() |> Enum.find(&(&1[:name] == name))
        {:ok, ty} = Ast.to_db(decl.type)
        {:ok, body} = Ast.to_db(decl.body)
        {name, {ty, body, elixir}}
      end)

    verify_pins!(lib)
    lib
  end

  defp parse_std(name) do
    {:ok, source} = Std.source(name)
    {:ok, book} = Parser.parse(source)
    book
  end
end

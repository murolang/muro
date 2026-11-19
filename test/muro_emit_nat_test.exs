defmodule Muro.EmitNatTest do
  use ExUnit.Case, async: true

  alias Muro.{Emit, Parser, Prelude}

  # The library runs whose Elixir body is the integer operation, with the
  # book that defines each one.
  @prims [
    {"pred", :prelude},
    {"plus", :prelude},
    {"max", "le.muro"},
    {"min", "le.muro"},
    {"minus", "le.muro"},
    {"compare", "ord.muro"}
  ]

  test "a Nat is a host integer: numerals, suc, and a match on zero and suc" do
    mod =
      compile!("""
      def three : run Nat := suc (suc (suc 0))
      def half : run Π (n : Nat) → Nat :=
        λ (n : Nat) →
          match n motive (λ _ → Nat)
            | 0 => 0
            | suc m =>
                (match m motive (λ _ → Nat)
                  | 0 => 0
                  | suc k => suc (half k))
      """)

    assert mod.three() == 3
    assert mod.half(9) == 4
    assert mod.half(2_000_001) == 1_000_000
  end

  # A host that passes something other than a Nat gets an error, not a
  # predecessor that keeps going down.
  test "a match on zero and suc refuses a negative integer and a float" do
    mod =
      compile!("""
      def half : run Π (n : Nat) → Nat :=
        λ (n : Nat) →
          match n motive (λ _ → Nat)
            | 0 => 0
            | suc m =>
                (match m motive (λ _ → Nat)
                  | 0 => 0
                  | suc k => suc (half k))
      def isZero : run Π (n : Nat) → Nat :=
        λ (n : Nat) →
          match n motive (λ _ → Nat)
            | 0 => suc 0
            | suc m => 0
      """)

    assert_raise CaseClauseError, fn -> mod.half(-1) end
    assert_raise CaseClauseError, fn -> mod.half(1.5) end
    assert_raise CaseClauseError, fn -> mod.half({:suc, 0}) end
    assert_raise CaseClauseError, fn -> mod.isZero(-3) end
    assert mod.isZero(7) == 0
  end

  test "library Nat runs are the integer operation at any size" do
    mod =
      compile!("""
      import "std:ord.muro"
      def overage : run Π (used : Nat) → Π (+ cost : Nat) → Π (limit : Nat) → Nat :=
        λ (used : Nat) → λ (+ cost : Nat) → λ (limit : Nat) →
          min cost (minus (plus used cost) limit)
      """)

    big = 10_000_000_000
    assert mod.overage(big, 3, big) == 3
    assert mod.overage(big - 2, 3, big) == 1
    assert mod.overage(5, 3, big) == 0
    assert mod.compare(big, big + 1) == :lt
    assert mod.max(big, 0) == big
  end

  # The replacement is trusted; agda/Muro/NatPrim.agda is the proof. This is
  # the regression test: each operation is compared with its own recursion,
  # emitted under another name so the replacement does not apply, on every
  # argument up to 40 and on seeded pairs up to 50_000.
  for {name, src} <- @prims do
    @name name
    @src src

    test "#{name} agrees with the recursion it replaces" do
      fast = compile!(library_source(@src))
      slow = compile!(renamed(library_source(@src), @name))
      fun = String.to_atom(Emit.elixir_base(@name))
      ref = String.to_atom(Emit.elixir_base(@name <> "-ref"))

      arity = arity(slow, ref)

      for args <- args(arity) do
        assert apply(fast, fun, args) == apply(slow, ref, args), "#{@name}#{inspect(args)}"
      end

      for bad <- [-1, 1.5, {:suc, 0}] do
        args = List.duplicate(bad, arity)
        assert_raise FunctionClauseError, fn -> apply(fast, fun, args) end
      end

      assert source!(library_source(@src)) =~
               ~r/def(p)? #{fun}\(x0(, x1)?\) when [^\n]* do\n    [^\n]*(Kernel|\+|cond)/
    end
  end

  test "a definition that only shares a library name keeps its own body" do
    source =
      source!("""
      def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
        λ (n : Nat) → λ (m : Nat) → n
      """)

    refute source =~ "x0 + x1"

    assert compile!(
             "def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=\n  λ (n : Nat) → λ (m : Nat) → n\n"
           ).plus(2, 5) == 2
  end

  test "a mutant of a library body keeps the emitted recursion" do
    {:ok, std} = Muro.Std.source("le.muro")
    mutant = String.replace(std, "| suc q => suc (min p q))", "| suc q => min p q)")
    refute mutant == std

    source = source!(mutant)
    refute source =~ "Kernel.min(x0, x1)"
    assert source =~ "Kernel.max(x0, x1)"
  end

  # Prelude runs are `run internal`; exported here so the test can call them.
  defp library_source(:prelude), do: String.replace(Prelude.source(), "run internal", "run")

  defp library_source(name) do
    {:ok, source} = Muro.Std.source(name)
    imports = if name == "ord.muro", do: elem(Muro.Std.source("le.muro"), 1), else: ""
    imports <> "\n" <> String.replace(source, ~s(import "le.muro"\n), "")
  end

  # Every whole-word use of `name` becomes `name-ref`. Muro names may
  # contain `-`, so `le-max-left` is not a use of `max`.
  defp renamed(source, name) do
    Regex.replace(~r/(?<![\w-])#{Regex.escape(name)}(?![\w-])/u, source, name <> "-ref")
  end

  defp arity(mod, fun) do
    Enum.find_value([1, 2], fn n -> if function_exported?(mod, fun, n), do: n end)
  end

  @wide 50_000

  defp args(1), do: for(a <- 0..40, do: [a]) ++ for(a <- sample(64, 1), do: [a])

  defp args(2) do
    for(a <- 0..40, b <- 0..40, do: [a, b]) ++
      Enum.zip_with(sample(64, 1), sample(64, 2), &[&1, &2]) ++
      for(a <- sample(16, 3), do: [a, a])
  end

  # Seeded, so a failure names the same pair on every run.
  defp sample(k, salt) do
    :rand.seed(:exsss, {7, 11, salt})
    for _ <- 1..k, do: :rand.uniform(@wide)
  end

  defp source!(text) do
    {:ok, book} = Parser.parse(text)
    Emit.emit_module(Muro.EmitNatProbe, Prelude.for_emit(book))
  end

  defp compile!(text) do
    dir = Path.join(System.tmp_dir!(), "muro-emit-nat-#{System.unique_integer([:positive])}")
    File.mkdir_p!(dir)
    path = Path.join(dir, "probe.muro")
    File.write!(path, text)
    assert Muro.check_file(path) == :ok
    mod = Module.concat(Muro, "EmitNat#{System.unique_integer([:positive])}")
    assert {:ok, src} = Muro.emit_file(path, mod)
    [{^mod, _}] = Code.compile_string(src)
    mod
  end
end

defmodule Muro.FoldTest do
  use ExUnit.Case, async: false

  # Eight octets, and the step uses the unrestricted field twice.
  # Without reducing constructor fields between octets, that copy
  # is re-reduced from the previous step and the check does not finish.
  @tag timeout: 30_000
  test "a fold reduces a constructor field before the next octet" do
    src = """
    unboxed data St : Type where
      st : Π (+ n : U64) → Π (+ k : U64) → St

    def widen : run Π (+ n : U64) → U64 :=
      λ (+ n : U64) →
        match (eqi n (toU64 0)) motive (λ _ → U64)
          | wtrue => toU64 1
          | wfalse =>
              (match (eqi n (toU64 1)) motive (λ _ → U64)
                | wtrue => toU64 2
                | wfalse =>
                    (match (eqi n (toU64 2)) motive (λ _ → U64)
                      | wtrue => toU64 3
                      | wfalse => addi n (toU64 1)))

    def step : run Π (+ s : St) → Π (+ b : U8) → St :=
      λ (+ s : St) → λ (+ _b : U8) →
        match s motive (λ _ → St)
          | st n _k => st (widen n) (widen (widen n))

    def go : run Π (+ s : Slice) → U64 :=
      λ (+ s : Slice) →
        match (sliceFold St (st (toU64 0) (toU64 0))
            (λ (b : U8) → λ (_r : Slice) → λ (s : St) → step s b)
            s) motive (λ _ → U64)
          | st n _k => n

    def go-ok : evidence {go b"abcdefgh" ≡ toU64 8 : U64} := refl
    """

    assert {:ok, book} = Muro.Parser.parse(src)
    assert Muro.Check.check_sig(book) == :ok
  end

  # trail reads the slice length on every octet. wrap mentions that
  # walk twice and is the identity. Five wraps, and without sharing
  # each octet rebuilds the inner wrap. Twelve octets then do not finish.
  # With sharing the length is 12 and the fold adds it 12 times.
  @tag timeout: 30_000
  test "a reusable slice is reduced once when the body mentions it twice" do
    src = """
    def trail : run Π (+ s : Slice) → U64 :=
      λ (+ s : Slice) →
        sliceFold U64 (toU64 0)
          (λ (_b : U8) → λ (r : Slice) → λ (acc : U64) →
            addi acc (addi (sliceLen s) (sliceLen r)))
          s

    def wrap : run Π (+ s : Slice) → Slice :=
      λ (+ s : Slice) →
        slice s (toU64 0)
          (addi (sliceLen s) (muli (subi (trail s) (trail s)) (toU64 0)))

    def walk : run Π (+ s : Slice) → U64 :=
      λ (+ s : Slice) →
        sliceFold U64 (toU64 0)
          (λ (_b : U8) → λ (_r : Slice) → λ (acc : U64) → addi acc (sliceLen s))
          s

    def go-ok : evidence
      {walk (wrap (wrap (wrap (wrap (wrap b"0123456789ab"))))) ≡ toU64 144 : U64} := refl
    """

    assert {:ok, book} = Muro.Parser.parse(src)
    task = Task.async(fn -> Muro.Check.check_sig(book) end)

    assert {:ok, :ok} ==
             (Task.yield(task, 10_000) || Task.shutdown(task, :brutal_kill))
  end

  # Same walk as the slice fold, over Bytes. The step still reads the
  # first field twice and ignores the second.
  @tag timeout: 30_000
  test "bytesFold reduces a constructor field the next step reads" do
    src = """
    unboxed data St : Type where
      st : Π (+ n : U64) → Π (+ k : U64) → St

    def widen : run Π (+ n : U64) → U64 :=
      λ (+ n : U64) →
        match (eqi n (toU64 0)) motive (λ _ → U64)
          | wtrue => toU64 1
          | wfalse =>
              (match (eqi n (toU64 1)) motive (λ _ → U64)
                | wtrue => toU64 2
                | wfalse =>
                    (match (eqi n (toU64 2)) motive (λ _ → U64)
                      | wtrue => toU64 3
                      | wfalse => addi n (toU64 1)))

    def step : run Π (+ s : St) → Π (+ b : U8) → St :=
      λ (+ s : St) → λ (+ _b : U8) →
        match s motive (λ _ → St)
          | st n _k => st (widen n) (widen (widen n))

    def go : run Π (+ s : Bytes) → U64 :=
      λ (+ s : Bytes) →
        match (bytesFold St (st (toU64 0) (toU64 0))
            (λ (b : U8) → λ (_r : Slice) → λ (s : St) → step s b)
            s) motive (λ _ → U64)
          | st n _k => n

    def go-ok : evidence {go b"abcdefgh" ≡ toU64 8 : U64} := refl
    """

    assert {:ok, book} = Muro.Parser.parse(src)
    assert Muro.Check.check_sig(book) == :ok
  end

  # The binder is mentioned twice, which is the sharing shape, but the
  # quantity is not reuse. `reduce` shows the argument still sitting in
  # the pair: call-by-name does not open a pair. Sharing would have
  # reduced `(λ y → 0) 0` before substitution. check refuses the affine
  # and linear books, because those quantities cannot be mentioned twice.
  test "an affine or linear argument is not reduced before the body" do
    arg = "((λ (+ y : Nat) → 0) 0)"

    for binder <- ["(x : Nat)", "(%1 x : Nat)", "(x : (1, 0) Nat)", "(x : (0, 0) Nat)"] do
      assert {:ok, {:pair, left, right}} = reduce(share_src(binder, arg))
      assert app?(left), binder
      assert left == right
    end

    assert {:ok, {:pair, :ze, :ze}} = reduce(share_src("(+ x : Nat)", arg))
  end

  # Each arm mentions x once. The sum is two and the max on one path is
  # one, so the argument stays an application under the pair.
  test "uses in different match arms are not one path" do
    src = """
    def go : run (Nat * Nat) :=
      (λ (+ x : Nat) →
        (match wtrue motive (λ _ → Nat)
           | wtrue => x
           | wfalse => x,
         0))
      ((λ (+ y : Nat) → 0) 0)
    """

    assert {:ok, {:pair, match, :ze}} = reduce(src)
    assert app?(match)
  end

  # One arm mentions x twice. That path shares, so the value is 0
  # before the pair is returned.
  test "two uses in one match arm share the argument" do
    src = """
    def go : run (Nat * Nat) :=
      (λ (+ x : Nat) →
        (match wtrue motive (λ _ → (Nat * Nat))
           | wtrue => (x, x)
           | wfalse => (0, 0),
         0))
      ((λ (+ y : Nat) → 0) 0)
    """

    assert {:ok, {:pair, {:mwbool, _, _, arms}, :ze}} = reduce(src)
    {_, _, wtrue} = Enum.find(arms, fn {name, _, _} -> name == "wtrue" end)
    assert {:pair, :ze, :ze} = wtrue
  end

  # Both mentions are in the motive. The arms do not read x. The motive
  # is still in the result because the scrutinee is an axiom, which does
  # not reduce, and the pair is already a value.
  test "a match motive does not count as a use" do
    src = """
    axiom stuck : evidence WBool

    def go : run (Nat * Nat) :=
      (λ (+ x : Nat) →
        (match stuck motive (λ _ → {x ≡ x : Nat})
           | wtrue => 0
           | wfalse => 0,
         0))
      ((λ (+ y : Nat) → 0) 0)
    """

    assert {:ok, {:pair, match, :ze}} = reduce(src)
    assert app?(match)
  end

  # `blow` is the second field. The step matches `st` and never reads it.
  # The same fuel runs out when that field is read.
  test "an unread accumulator field does not spend the fold's fuel" do
    # One `id` costs two fuel to open. Two hundred is past the budget
    # below, and the fold of one octet fits inside that budget.
    blow = Enum.reduce(1..200, "0", fn _, acc -> "id (#{acc})" end)

    assert check(field_src(blow, "st (addi n (toU64 1)) blow"), fuel: 80) == :ok

    assert {:error, msg} =
             check(field_src(blow, "st (addi n (toU64 1)) (id k)"), fuel: 80)

    assert Muro.Check.out_of_fuel?(msg)
  end

  # The payload is a word spine, not a declared constructor. The arm
  # binds it and does not read it. Reading it spends the same fuel.
  test "an unread Opt payload does not spend the fold's fuel" do
    blow = Enum.reduce(1..200, "0", fn _, acc -> "id (#{acc})" end)

    assert check(opt_src(blow, "wnone", "1"), fuel: 80) == :ok

    assert {:error, msg} = check(opt_src(blow, "wsome (id x)", "0"), fuel: 80)
    assert Muro.Check.out_of_fuel?(msg)
  end

  # The step opens the pair and reads the second component only.
  test "an unread pair component does not spend the fold's fuel" do
    blow = Enum.reduce(1..200, "0", fn _, acc -> "id (#{acc})" end)

    assert check(pair_src(blow, "(0, k)"), fuel: 80) == :ok
    assert {:error, msg} = check(pair_src(blow, "(id a, k)"), fuel: 80)
    assert Muro.Check.out_of_fuel?(msg)
  end

  defp share_src(binder, arg) do
    """
    def go : run (Nat * Nat) :=
      (λ #{binder} → (x, x))
      #{arg}
    """
  end

  defp field_src(blow, rebuild) do
    """
    data St : Type where
      st : Π (+ n : U64) → Π (+ k : Nat) → St

    def id : run Π (+ n : Nat) → Nat :=
      λ (+ n : Nat) → n

    def blow : run Nat :=
      #{blow}

    def go : run Π (+ s : Slice) → U64 :=
      λ (+ s : Slice) →
        match (sliceFold St (st (toU64 0) blow)
            (λ (_b : U8) → λ (_r : Slice) → λ (s : St) →
              match s motive (λ _ → St)
                | st n k => #{rebuild})
            s) motive (λ _ → U64)
          | st n _k => n

    def go-ok : evidence {go b"a" ≡ toU64 1 : U64} := refl
    """
  end

  defp opt_src(blow, rebuild, expect) do
    """
    def id : run Π (+ n : Nat) → Nat :=
      λ (+ n : Nat) → n

    def blow : run Nat :=
      #{blow}

    def go : run Π (+ s : Slice) → Nat :=
      λ (+ s : Slice) →
        match (sliceFold (Opt Nat) (wsome blow)
            (λ (_b : U8) → λ (_r : Slice) → λ (o : Opt Nat) →
              match o motive (λ _ → Opt Nat)
                | wsome x => #{rebuild}
                | wnone => wnone)
            s) motive (λ _ → Nat)
          | wsome _ => 0
          | wnone => 1

    def go-ok : evidence {go b"a" ≡ #{expect} : Nat} := refl
    """
  end

  defp pair_src(blow, rebuild) do
    """
    def id : run Π (+ n : Nat) → Nat :=
      λ (+ n : Nat) → n

    def blow : run Nat :=
      #{blow}

    def go : run Π (+ s : Slice) → Nat :=
      λ (+ s : Slice) →
        let (_a, k) =
          sliceFold (Nat * Nat) (blow, 0)
            (λ (_b : U8) → λ (_r : Slice) → λ (acc : Nat * Nat) →
              let (a, k) = acc in #{rebuild})
            s
        in k

    def go-ok : evidence {go b"a" ≡ 0 : Nat} := refl
    """
  end

  defp check(src, opts) do
    assert {:ok, book} = Muro.Parser.parse(src)
    Muro.Check.check_sig(book, opts)
  end

  defp reduce(src, fuel \\ 2000) do
    assert {:ok, named} = Muro.Parser.parse(src)
    assert {:ok, db} = Muro.Ast.book_to_db(named)
    defn = Enum.find(db, &(&1.name == "go"))
    Muro.Check.reduce(db, defn.body, fuel)
  end

  defp app?({:app, _, _}), do: true
  defp app?({:lam, _, _, _, t}), do: app?(t)
  defp app?(t) when is_tuple(t), do: t |> Tuple.to_list() |> Enum.any?(&app?/1)
  defp app?(t) when is_list(t), do: Enum.any?(t, &app?/1)
  defp app?(_), do: false
end

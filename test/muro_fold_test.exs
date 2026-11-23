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
end

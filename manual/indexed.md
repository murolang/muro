---
title: Indexed data
slug: indexed
order: 8
summary: Fin, Vec, index equations in motives, and lookup without a runtime bounds check.
---

# Indexed data

In brief: a branch of `match` on an indexed type is typed at its own constructor's indices, not at the scrutinee's. What the branch knows about the scrutinee's indices it learns from an equation carried by the motive, and uses with `rewrite`. A constructor whose indices are a numeral that cannot be the scrutinee's (`0` against `suc(m)`) is skipped. Motives bind the indices, then the scrutinee. If the types line up, `lookup` has no runtime bounds check.

## Fin and Vec

From `examples/vec.muro`:

```
data Fin : Nat → Type where
  fzero : Π (n : Nat) → Fin suc(n)
  fsuc  : Π (n : Nat) → Fin n → Fin suc(n)

data Vec (A : Type) : Nat → Type where
  vnil  : Vec A 0
  vcons : Π (n : Nat) → A → Vec A n → Vec A suc(n)
```

`Fin n` is a position smaller than `n`. `Vec A n` is a vector of length `n`. There are no metavariables: you write the length arguments.

## Motives with indices

The motive is a telescope: first the indices, then the scrutinee.

```
match i motive (λ (k : Nat) → λ (_ : Fin k) → Vec A k → A)
  | fzero m => …
  | fsuc m j => …
```

The `match` has type `motive n i`, the motive at the scrutinee's indices and the scrutinee. Each branch is checked against the motive at its constructor's indices and the constructor applied to its fields: the `fzero m` branch against `Vec A suc(m) → A`, the `fsuc m j` branch against `Vec A suc(m) → A`. `lookup` returns a function `Vec A k → A`, then applies it to `xs`. That is how the index `k` stays aligned with the vector you eliminate.

## Learning an index: the equation in the motive

Inside the `fzero m` branch, `ys : Vec A suc(m)` is matched again. The `vcons p a as` branch is typed at `vcons`'s own index, `suc(p)`, so `as : Vec A p`; nothing identifies `p` with `m`. To use that `ys` has length `suc(m)`, put the equation in the motive, and pass `refl` at the outside, where the indices are the scrutinee's:

```
(match ys motive (λ (k : Nat) → λ (_ : Vec A k) → {suc(m) ≡ k : Nat} → A)
  | vnil => 0
  | vcons p a as => λ (e : {suc(m) ≡ suc(p) : Nat}) → …) refl
```

The `match` has type `{suc(m) ≡ suc(m) : Nat} → A`, which `refl` fits. The `vcons` branch receives `e : {suc(m) ≡ suc(p) : Nat}` and can `rewrite` with it. `suc` is injective as evidence:

```
def pred : run Π (n : Nat) → Nat :=
  λ (n : Nat) →
    match n motive (λ _ → Nat)
      | 0 => 0
      | suc m => m

def inj-suc : evidence Π (-m : Nat) → Π (-p : Nat) →
                        Π (e : {suc(m) ≡ suc(p) : Nat}) → {m ≡ p : Nat} :=
  λ (-m : Nat) → λ (-p : Nat) → λ (e : {suc(m) ≡ suc(p) : Nat}) →
    rewrite e motive (λ z → {pred z ≡ p : Nat}) in refl
```

`rewrite e motive (λ z → {pred z ≡ p : Nat}) in refl` has type `{pred suc(m) ≡ p : Nat}` given `refl : {pred suc(p) ≡ p : Nat}`; both reduce, to `{m ≡ p : Nat}` and `{p ≡ p : Nat}`.

## lookup

```
def lookup : run Π (-A : Type) → Π (-n : Nat) → Π (i : Fin n) → Π (xs : Vec A n) → A :=
  λ (-A : Type) → λ (-n : Nat) → λ (i : Fin n) → λ (xs : Vec A n) →
    (match i motive (λ (k : Nat) → λ (_ : Fin k) → Vec A k → A)
      | fzero m =>
          λ (ys : Vec A suc(m)) →
            (match ys motive (λ (k : Nat) → λ (_ : Vec A k) → {suc(m) ≡ k : Nat} → A)
              | vnil => 0
              | vcons p a as => λ (_ : {suc(m) ≡ suc(p) : Nat}) → a) refl
      | fsuc m j =>
          λ (ys : Vec A suc(m)) →
            (match ys motive (λ (k : Nat) → λ (_ : Vec A k) → {suc(m) ≡ k : Nat} → A)
              | vnil => 0
              | vcons p a as => λ (e : {suc(m) ≡ suc(p) : Nat}) →
                  lookup A m j (rewrite inj-suc m p e motive (λ z → Vec A z) in as)) refl) xs
```

In the `fsuc m j` branch, `j : Fin m` and `as : Vec A p`. `inj-suc m p e : {m ≡ p : Nat}` and `rewrite … motive (λ z → Vec A z) in as` turns `as` into a `Vec A m`, so `lookup A m j …` is well-typed. The `rewrite` and the equation are evidence: the emitted `lookup` passes `as` on and calls itself.

`n` is erased: it only appears in types, and the emitted `lookup` does not take it. `lookup` descends on `i`: `j` (from `fsuc m j`, a field of `i`) is passed at that position. `as` is a field of `ys`, a λ-bound variable, and is not smaller: matching a variable that is not an argument, or a computed value, exposes nothing a self-call may descend on. Keeping `n` unerased also checks; the checker finds the argument to descend on.

The `vnil` branches are skipped: `vnil` has index `0` and the scrutinee has index `suc(m)`, and `0` is not `suc` of anything, so the constructor cannot occur. The surface still asks for a branch, and its body is not checked; `0` is a placeholder. The test is on numerals only: `suc` against `suc` compares the arguments, `0` against `suc(…)` is a clash, and anything else (a variable, an application) is not a clash and the branch is checked as usual.

This is the pattern of `match … in … return` in Coq, and the convoy pattern: a branch knows the constructor's indices, and the motive carries whatever else it needs to learn. Nothing is substituted into a branch behind your back, so what checks is exactly what the kernel rule (`⇒-mData`) derives.

`ones1` is a vector of length one. `lookup-ok` is `refl`:

```
def ones1 : run Vec Nat suc(0) :=
  vcons 0 (suc 0) vnil

def lookup-ok : evidence {lookup Nat suc(0) (fzero 0) ones1 ≡ suc 0 : Nat} :=
  refl
```

## Running it

```
{:ok, src} = Muro.emit_file("examples/vec.muro", Muro.Vecs)
Code.eval_string(src)
Muro.Vecs.lookup({:fzero, 0}, Muro.Vecs.ones1())
# {:suc, 0}
```

`A` was erased, so the Elixir arity starts at `n`. `n` is Peano `{:suc, 0}`. There is no bounds check in the emitted function: the index and the vector were already the same length in the type.

Next: [Streams](streams.md).

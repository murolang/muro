---
title: Reals
slug: reals
order: 16
summary: A computable Real in run, a classical CReal in evidence and spec, and an erased bridge. This is a design memo. The books are not written yet.
---

# Reals

In brief: a computable `Real` may appear in a `run` and is emitted. A classical `CReal` lives only in `evidence` and `spec`. The map between them is evidence and is erased. This page is a design memo. `std:real-comp.muro` and `std:real-class.muro` are not in the library yet. Snippets below are proposed source, not checked books. A proposed `def` includes `:= ?`: it parses, and the checker refuses it as an unsolved hole until a later stage fills it. An axiom has no body.

## The hybrid

The wall is unchanged. A `run` that reaches a classical axiom is refused, and it is not emitted. One refusal the checker emits is:

```
bad: a run depends on hidden.LEM
```

See [The wall](wall.md#axioms). Completeness and the ordered-field axioms for `CReal` will be the same kind of evidence axiom as `LEM` in [Library](library.md#classicalmuro). A computable operation does not call them.

## Computable layer

The future book is `std:real-comp.muro`.

Muro already has coinduction: `Stream` is primitive, and a declared `ν` family is a greatest fixed point ([Streams](streams.md)). A stream of approximations could be a real. This design does not use that. A stream is not copyable, so a seed of type `Stream` is affine, and `(+ t : Stream Nat)` is refused. Addition needs both arguments more than once (`x` in `x + x`). A function is copyable by closure. The representation is therefore ordinary data: a sequence and a modulus, not a `ν` type.

The ordinary library has no rational and no dyadic type. Stage 2 defines a signed dyadic type first (`Dyadic`: an integer numerator and a power-of-two denominator). Machine `I64` is a residue and is not that type.

A constructor that binds `seq` and `mod` affinely refuses a `run` that reads the sequence twice (`affine variable used twice`). Reusable fields let an operation read a sequence more than once. That is not enough for `add x x`: the caller's `x` must be reusable, and `add`, `mul`, and `neg` take reusable `Real` arguments so a body may use an argument more than once. A scratch book with a stand-in `Dyadic` checks `λ (+ x : Real) → add x x`.

```
-- proposed
data Real : Type where
  mk : Π (+ seq : Π (+ n : Nat) → Dyadic) → Π (+ mod : Π (+ k : Nat) → Nat) → Real
```

`seq n` is the approximation at index `n`. `mod k` is a point after which two approximations differ by at most `2^{-k}`: if `m` and `n` are at least `mod k`, then `|seq m - seq n| ≤ 2^{-k}`. That inequality is a `spec` on the representation, not a `run` test.

Addition, multiplication, and negation are `run`. They act on the sequences pointwise and compute a new modulus. They are total. Their `Real` arguments are reusable:

```
-- proposed
def add : run Π (+ x : Real) → Π (+ y : Real) → Real := ?
def mul : run Π (+ x : Real) → Π (+ y : Real) → Real := ?
def neg : run Π (+ x : Real) → Real := ?
```

Comparison is a `run` that takes a precision, not a decision of equality. `Ordering` in `std:ord.muro` is `lt`, `eq`, and `gt`. Close is not equality, so comparison uses its own type:

```
-- proposed
data Near : Type where
  lt : Near
  gt : Near
  close : Near

def compare : run Π (eps : Dyadic) → Π (x : Real) → Π (y : Real) → Near := ?
```

`lt` means `x` is less than `y` by more than `eps`, and `gt` means `x` is greater than `y` by more than `eps`, the same polarity as `compare` on `Nat` in `std:ord.muro` (`lt` is `suc m ≤ n`). Otherwise the result is `close`. A binder named `ε` does not parse; the precision in source is `eps`. Equality of reals is a `spec` relation. It is not decidable, and it is not a `run`.

```
-- proposed
def EqReal : spec Π (x : Real) → Π (y : Real) → Type := ?
```

`EqReal x y` says the sequences agree in the limit, using the two moduli. A square root is a `run`. Non-negativity is constructive evidence, not a classical axiom, so it may be an erased argument of that run:

```
-- proposed
def sqrt : run Π (x : Real) → Π (- nn : Nonneg x) → Real := ?
```

The result is a `Real`, so its modulus is part of that value and is computed from `x`. The type does not take a separate precision. A numeric backend that emits floating-point or arbitrary-precision arithmetic is out of scope. The representation stores a function. The kernel allows a Π in a run type. Elixir can emit it. A function argument is outside the closed run image that C, Rust, and assembly emit ([Library](library.md)).

## Classical layer

The future book is `std:real-class.muro`. It imports `std:classical.muro`. Every postulate is an evidence axiom. No `run` may depend on any of them.

Proposed axioms include a type of classical reals, the ordered-field operations and their laws, and completeness:

```
-- proposed
axiom CReal : evidence Type
axiom czero : evidence CReal
axiom cone : evidence CReal
axiom cadd : evidence Π (x : CReal) → Π (y : CReal) → CReal
axiom cmul : evidence Π (x : CReal) → Π (y : CReal) → CReal
axiom cneg : evidence Π (x : CReal) → CReal
axiom cinv : evidence Π (x : CReal) → Π (- nz : Neq x czero) → CReal
axiom cle : evidence Π (x : CReal) → Π (y : CReal) → Type
```

Plus the usual field and order laws as evidence axioms, and a least-upper-bound axiom: an inhabited, bounded-above family of `CReal` has a least upper bound. None of these is a `run`.

Existence is written in elimination form. A predicate family `Π (_ : A) → Type` is not a valid data parameter, so a polymorphic dependent pair over an arbitrary predicate cannot be declared. The checker refuses `data Sigma (A : Type) (P : A → Type)` with `Sigma pack type: cannot convert Π (_ : A) → Type ≁ Type`. A witness type on a closed domain does check, as in [the drinker example](examples.md#drinkermuro). General `Σ` over a family would be a kernel change. It is out of scope. The theorems keep the elimination form so they quantify over an arbitrary predicate.

The irrational-power theorem: there are irrationals `a` and `b` such that `a^b` is rational. Every consequence of such a pair holds:

```
-- proposed
def IrrationalPower : spec Type :=
  Π (Q : Type) →
  (Π (a : CReal) → Π (b : CReal) →
    Irrational a → Irrational b → Rational (cpow a b) → Q) →
  Q

def irrational_power : evidence IrrationalPower := ?
```

The proof may use `LEM` (the usual case split on whether `√2^{√2}` is rational). `Irrational`, `Rational`, and `cpow` are defined in the same book from the field structure. An intermediate-value statement has the same shape: every consequence of a root in the interval holds.

## The bridge

The future embedding and the agreement theorems are evidence. They are erased. They never appear in emitted code.

```
-- proposed
def embed : evidence Π (x : Real) → CReal := ?

def add-agree : evidence
  Π (x : Real) → Π (y : Real) →
  EqCReal (embed (add x y)) (cadd (embed x) (embed y)) := ?
```

The direction of the cut is this way only. `add`, `mul`, `neg`, `compare`, and `sqrt` are `run`s in the computable book. They do not mention `CReal` or its axioms. The agreement theorems are evidence *about* those runs, through `embed`. They may depend on the classical axioms. The runs themselves must not. If a `run` reached `lub` or `CReal`, the checker would refuse it with `bad: a run depends on <File.axiom>`, the same refusal as for `LEM`.

## Agda

The Agda tree is checked under `--safe`. `--safe` forbids postulates. Today's development does not postulate `LEM`: [Library](library.md#classicalmuro) records that Agda does not postulate it. Completeness and the `CReal` axioms cannot be added to that tree as postulates.

The computable layer and the bridge statements (the types of `embed` and of agreement, not a construction of `embed` from completeness) get `--safe` mirrors. `CReal` lives outside that tree: either a module that is not part of `make agda-safe`, or a module parameterized over the axioms, so the body has no postulates. That is the same discipline as `LEM`.

## Stages

This page is Stage 0. No checker, emitter, or library book is added here.

**Stage 1.** `std:real-class.muro` with the axioms, the irrational-power theorem (or IVT) as evidence, and a manual section that explains the cut. `mix muro.check` prints the depends-lines and refuses a `run` that reaches those axioms.

**Stage 2.** A dyadic (or rational) type, then `std:real-comp.muro`: the representation, `run` arithmetic with reusable `Real` arguments, `compare`, `EqReal`, and `sqrt` whose modulus is inside the returned `Real`. Evidence that the operations are correct for the representation, with no dependence on the classical axioms.

**Stage 3.** The erased embedding, the agreement theorems, and one book that uses both layers: a computable algorithm together with a classical existence proof that is erased.

Out of scope: a full constructive analysis library; transcendentals beyond the examples; a numeric backend; changing the kernel so equality of reals is decidable, or so a general `Σ` over a predicate family can be declared.

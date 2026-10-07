---
title: Either and Dec
slug: either
order: 10
summary: Disjoint union and decisions. Not LEM.
---

# Either and Dec

In brief: `A ⊎ B` is `data Either`. `Dec P` is `P ⊎ (P → Empty)`: a decision for a particular `P`, not LEM. There is no inhabitant of `Π (P : Type) → Dec P`.

## Either

Declare it in the book. The infix `⊎` desugars to `Either A B`. ASCII is the name `Either`.

```
data Either (A : Type) (B : Type) : Type where
  left  : A → Either A B
  right : B → Either A B
```

`left` and `right` are checked against an expected Either. Match has an explicit motive, same shape as other data.

A run sum (`examples/either_run.muro`):

```
def fromLeft : run Π (e : Either Nat Unit) → Nat :=
  λ (e : Either Nat Unit) →
    match e motive (λ (_ : Either Nat Unit) → Nat)
      | left n => n
      | right _ => 0
```

Emit: `{:left, n}` / `{:right, t}`.

Either is not Data. Closures `P → Empty` are not Data. No `+` on a refutation.

## Dec is a spec

```
def Dec : spec Π (P : Type) → Type :=
  λ (P : Type) → Either P (Π (_ : P) → Empty)
```

A value of `Dec P` is either a witness of `P` or a function that turns a witness into `Empty`. That is a decision for **this** `P`. It is not an axiom that every type is decidable.

There is no inhabitant of `Π (P : Type) → Dec P`.

## evenDec

`examples/even_dec.muro` decides `IsEven n` by matching on `n`.

- `0` — `left tt`. Even.
- `suc 0` — `right` of a function that `matchEmpty`s the evidence. Odd.
- `suc (suc p)` — reuse `evenDec p` and keep the same injection.

```
def evenDec : evidence Π (n : Nat) → Dec (IsEven n) :=
  λ (n : Nat) →
    match n motive (λ (x : Nat) → Dec (IsEven x))
      | 0 => left tt
      | suc n1 =>
        match n1 motive (λ (y : Nat) → Dec (IsEven suc(y)))
          | 0 => right (λ (e : IsEven suc(0)) → matchEmpty e motive (λ _ → Empty))
          | suc p =>
            match evenDec p motive (λ (d : Dec (IsEven p)) → Dec (IsEven suc(suc(p))))
              | left e  => left e
              | right c => right c
```

`evenDec` is evidence. It is not emitted. You can still check it:

```
mix muro.check examples/even_dec.muro
```

Next: [Machine numbers](machine.md).

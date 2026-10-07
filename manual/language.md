---
title: Terms
slug: language
order: 5
summary: Type, Π, λ, match, quantities, and the book.
---

# Terms

In brief: one sort `Type`. Binders are written. Application is juxtaposition. `match` takes an explicit motive. Affine is the default.

## The book

A `.muro` file is a **book**: a sequence of `ν`, `data`, and `def` entries.

```
def name : tag type := body
```

The tag is `run`, `run internal`, `spec`, or `evidence`. There is no other tag.

Forward references are allowed. The checker sees every definition when it checks any one of them.

## Prelude

`mix muro.check` and `Muro.check_file/2` put a small book in scope behind the file. These names are already defined:

| Name | Tag | What it is |
| --- | --- | --- |
| `pred` | `run internal` | The predecessor. `pred 0` is `0`. |
| `plus` | `run internal` | Addition on `Nat`. |
| `inj-suc` | `evidence` | `{suc(m) ≡ suc(p) : Nat}` gives `{m ≡ p : Nat}`. |
| `plus_suc` | `evidence` | `{plus n suc(m) ≡ suc(plus n m) : Nat}`. |
| `sym` | `evidence` | `{x ≡ y : A}` gives `{y ≡ x : A}`. |
| `cong` | `evidence` | `{x ≡ y : A}` gives `{f x ≡ f y : B}`. |

A name the file defines replaces that prelude definition. Anything in the prelude that refers to a replaced name is dropped with it: a file that defines its own `plus` does not see the prelude's `plus_suc`, because that lemma is about the prelude's `plus`.

The prelude is ordinary `.muro`. It is not a new rule. `check_sig` on a book you built yourself does not add it; `check_file` does. A prelude `run` is emitted only when a `run` term in the file calls it, and then as `defp`. Evidence in the prelude is not emitted.

`examples/using_prelude.muro` uses `sym`, `cong`, and `pred` without defining them. `examples/half_ok.muro` defines its own `plus`, so that is the `plus` the file checks and emits.

## Type

There is one sort, `Type`. It is not `Type : Type`. `Type` itself is erased: you do not compute with it.

A *small type* is a term of type `Type`: `Nat`, `Π (n : Nat) → Nat`, `Π (X : Type) → X`, `IsEven 2`. A *kind* is `Type` or `Π (x : A) → K` with `K` a kind: `Π (n : Nat) → Type` is the kind of `IsEven`. Kinds are well-formed, so they can be the type of a `def` and the type of a binder, but a kind is not a term of type `Type`. The checker refuses `Π (_ : Unit) → Type`, `Type × Unit`, and a constructor field of type `Type` where a small type is expected. Without that refusal `Type` would be a retract of a small type and the sort would be inconsistent (Girard's paradox).

`Type` is impredicative: `Π (X : Type) → X` is itself in `Type`. That is the design, not an accident, and it is why a consistency proof for the calculus cannot come from a set-theoretic model in Agda.

Primitive types you can write as atoms:

| Atom | Meaning |
| --- | --- |
| `Type` | The sort |
| `Nat` | Peano naturals |
| `Atom` | The atom literals written in this file |
| `Unit` | One constructor, `tt` |
| `Empty` | No constructors |
| `I64` / `F32` | Machine scalars; see [Machine numbers](machine.md) |
| `Stream A` | Greatest fixed point; see [Streams](streams.md) |

`Nat`, `Unit`, and `Empty` as *types* are spec formers. You infer them only in spec. Their *constructors* (`0`, `suc`, `tt`) compute in run.

## Binders and quantities

A binder is always parenthesized.

```
(n : Nat)        affine (default): at most one run/evidence use
(+ n : Nat)      reuse: only if the type WHNFs to Data
(- e : IsEven n) erased: compile-time; cannot be used computationally
```

The `+` or `-` sits immediately before the name, inside the parentheses. `(-A : Type)` and `(- A : Type)` both parse.

**Data** (after WHNF) for `+`: `Nat`, `Unit`, `Empty`, `I64`, `F32`, `Tensor`, or a user `data` type whose *parameters* are Data. Indices do not have to be Data. `List A` is Data iff `A` is. `List (Nat → Nat)` is not, so you cannot write `+xs : List (Nat → Nat)`.

`Stream` and `Either` are not Data. There is no `+` on a stream or on a refutation `P → Empty`.

In spec, uses are forgotten. You can mention an affine variable twice while building a type.

In run and evidence, using an affine variable twice is an error: `affine variable used twice`. Using an erased variable computationally is an error: `erased variable used computationally`.

## Π and λ

```
Π (n : Nat) → Nat
λ (n : Nat) → suc(n)
```

ASCII: `Pi`, `lam`, `->`.

A non-dependent arrow `A → B` is `Π (_ : A) → B` with an affine ignored binder.

Application is juxtaposition: `f a b`. `motive`, `in`, and `def` never start an argument.

## Holes

`?` is an unsolved goal, not a solution. It is allowed in any term position. The checker always refuses it, in every mode, whether it is inferring or checking:

```
1:1: gap body: 2:19: unsolved hole
expected: Nat
context:
  n : Nat
```

The prefix is `line:col`. `expected` is the type the hole must inhabit, or `(none; infer)` when the hole is the head of an inference. `context` lists the binders in scope, oldest first. A hole is not a metavariable: nothing is unified, nothing is postponed, and a book that still contains `?` does not check. Fill it.

A conversion error uses the same printer: `cannot convert Nat ≁ {n ≡ 0 : Nat}`, not `#0`.

## match

Every eliminator writes its motive. The motive is the family you return in, with the scrutinee bound.

Nat:

```
match n motive (λ x → P)
  | 0 => tz
  | suc p => ts
```

`x` is bound in `P`. `p` is bound in `ts`. `suc p` here is a pattern binder, not `suc` applied to a term.

Empty:

```
matchEmpty e motive (λ _ → P)
```

There are no constructors. If you have an inhabitant of `Empty`, you may return any `P`.

Data (one named branch per constructor):

```
match m motive (λ _ → A)
  | nothing => d
  | just a  => a
```

Motives are written in parentheses. Nested λ in the motive cover index binders (see [Indexed data](indexed.md)).

## Atoms

An atom literal is a tag written in the file, colon glued to the name: `:asc`. It is a value of type `Atom`. It is not a constructor and not a `Nat`. `Atom` is not Data, so `+` does not apply. There is no `where` block of atoms, and no function from a string to an atom.

The spellings that occur in the file are the whole type. A `match` on `Atom` is exhaustive for that set. A missing arm is an error that names the atom (`missing branch for :asc`). Elixir prints the colon form and matches with `case`. C emits an enum of those spellings (`MURO_ASC`, `MURO_DESC`) and matches with `switch`. A name the file did not write is not added. Atom is checked and emitted by this implementation; it is not in the Agda kernel.

`examples/sort.muro` is insertion sort on `List Nat`. `:asc` orders upward and `:desc` downward.

## Products

`A × B` (ASCII `*`) is a pair type. `(a, b)` is a pair. A pair is opened with `let`:

```
let (a, b) = e in t
```

`e` must have a pair type `A × B`; `t` is checked against the expected type with `a : A` and `b : B` in scope, each affine. `let (a, b) = (u, v) in t` reduces to `t` with `a := u`, `b := v`. A `let` is also inferred when its body's type does not mention `a` or `b`, so it may be the head of an application, the seed of an `unfold`, or the argument of `uncons`; a body whose type depends on a component (`Fin x` for a component `x`) is refused with `let: the body's type mentions a component of the pair`.

`let` is the way to consume an affine pair: a pair-typed variable `p` may be used once, and `plus (fst p) (snd p)` uses it twice. `let (x, y) = p in plus x y` uses it once and both components once.

`fst t` and `snd t` are sugar: `fst t` is `let (a, b) = t in a` and `snd t` is `let (a, b) = t in b`; `head s` is `fst (uncons s)` and `tail s` is `snd (uncons s)`. The kernel has one pair eliminator, `let`, and it is inside the fragment the Agda proofs cover (see [Limits](limits.md)).

## Recursion and descent

A definition in `run` or `evidence` descends on one of its non-erased arguments, the same one at every self-call. At that position a self-call must pass a smaller variable: one that came from a `match` on that argument, or on a variable already smaller (the `suc` predecessor, a constructor argument whose type is `D …`, the tail of a list, …). The other positions may hold anything. The checker finds the position: it tries the first non-erased argument, then each later one, and a definition with no self-call passes at once.

Three things are not descent. A smaller variable passed at another position (`f (suc (suc y)) xp` when `xp` came from `x`, the first argument). The fields of a `match` on a computed value or on a λ-bound variable that is not the argument (`match (f x) …`, `match ys …` under `λ ys →`): the match is fine, its fields are not smaller. The definition itself unapplied (`apply f n`): in run and evidence a self-reference must be the head of a call.

Spec does not check descent. `IsEven` may recurse on `p` after two `suc` matches because it is a spec.

A typical run recursion looks like `plus`:

```
def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
  λ (n : Nat) → λ (m : Nat) →
    match n motive (λ _ → Nat)
      | 0 => m
      | suc np => suc(plus np m)
```

`np` is smaller than `n`. `plus np m` is allowed. `plus n m` inside the `suc` branch is not.

## The half example, as a reader

`examples/half_ok.muro` puts the three modes in one file.

- `plus` — run. Adds Peano numbers.
- `IsEven` — spec. A family `Nat → Type`. `0` is even (`Unit`). `1` is odd (`Empty`). `suc(suc p)` is even iff `p` is.
- `half` — run. Drops two `suc` at a time.
- `plus_suc` — evidence. `{plus n suc(m) ≡ suc(plus n m) : Nat}`.
- `half_ok` — evidence. If `n` is even, `{plus (half n) (half n) ≡ n : Nat}`.

`half` of eight is four. The proof is `match`, `refl`, `rewrite`, and `matchEmpty`. It is not emitted.

Next: [Identity](identity.md).

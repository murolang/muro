---
title: Data
slug: data
order: 7
summary: Inductive types, positivity, Maybe, List, Tree.
---

# Data

In brief: a `data` declaration is a book entry. Binders before `:` are parameters. The telescope after `:` before `Type` is indices. Constructors must be strictly positive. Nat, Unit, Empty, and ν stay primitive.

## A declaration

```
data Maybe (A : Type) : Type where
  nothing : Maybe A
  just    : A → Maybe A
```

(`examples/maybe.muro`.)

- The type former is spec.
- Constructors compute in run and may appear in evidence.
- There is no kernel constructor named after your type. `Maybe`, `List`, `Vec`, `Fin` all use the same `dty` / `ctor` / `mData` representation.

Nat, Unit, Empty, and Stream stay primitive. Do not redeclare them.

## Parameters and indices

```
data Name params : index-telescope Type where
  ctor : telescope
```

Parameters are the binders before `:`. Indices are the telescope after `:` and before `Type`.

```
data List (A : Type) : Type where          -- one parameter, no indices
  nil  : List A
  cons : A → List A → List A

data Fin : Nat → Type where                -- no parameters, one index
  fzero : Π (n : Nat) → Fin suc(n)
  fsuc  : Π (n : Nat) → Fin n → Fin suc(n)
```

`Vec` has both; see [Indexed data](indexed.md).

## Match

One named branch per constructor. Explicit motive over the scrutinee (and its indices, when there are indices).

```
def fromMaybe : run Π (-A : Type) → Π (d : A) → Π (m : Maybe A) → A :=
  λ (-A : Type) → λ (d : A) → λ (m : Maybe A) →
    match m motive (λ _ → A)
      | nothing => d
      | just a  => a
```

`A` is erased. Emit drops that argument. `fromMaybe Nat 0 (just (suc 0))` converts to `suc 0`; `fromJust1` is `refl`.

A branch binds each field at the quantity the constructor declares. The default is affine: `a` in `just a` is used at most once in run and evidence. A constructor may declare a field `+` when its type is Data, and then every branch binds that field reusable:

```
data Seed : Type where
  at : Π (+ s : State) → Π (+ n : Nat) → Seed
```

A `match` on a `Seed` may use `s` and `n` as often as it needs. The `+` on a field is checked like the `+` on a binder: `Π (+ f : Nat → Nat) → …` is refused. A `match` on `Nat` is the one case that reads the scrutinee instead: the predecessor of a reusable variable is reusable ([Terms](language.md#match)).

## Positivity

A constructor field is strictly positive in `D` after the checker unfolds it. `D` may be absent. `D` may be the head of a spine whose arguments do not contain `D`. `D` may occur to the right of a `Π` whose domain does not contain `D`. A product is positive on both sides. `D` inside an argument of `D` is refused, including under a spec name: `Contra := Bad → Empty` is the negative arrow, and `List (Tree A)` is nested. Another data type is held to the same test: its parameters are instantiated and every one of its fields must be strictly positive in `D`. `Wrap` that stores a `Bad`, placed in a domain `(Wrap → Empty)`, is refused. `Tree` and `Forest`, each storing the other as a field, are accepted. A field that does not reduce in the fuel is refused.

This is rejected:

```
data Bad : Type where
  mk : Π (n : Nat) → (Bad n → Nat) → Bad n
```

(`Bad` is not even well-formed that way — the point is the negative occurrence.)

## Fields are small

Every constructor field (a binder after the parameters) must be a small type: a term of type `Type`. Parameters are `(A : Type)` and are exempt. A field of type `Type` is rejected:

```
data Box : Type where
  box : Π (A : Type) → Box
```

With `match … motive (λ _ → Type)` such a `Box` would project a type back out of a term of type `Type`, and `Type` would be a retract of `Box`. Parametrise instead: `data Box (A : Type) : Type`.

## Recursion

A call in run or evidence, to the definition being checked or to another run or evidence definition that reaches it, must pass a constructor argument whose type is `D …` from a `match` on the argument the block descends on. The block shares one argument position. `even` and `odd` on `Nat` are one block (`examples/even_odd.muro`). For lists, that position is the tail. For trees, either child. Fields of a `match` on a computed value are not smaller. Spec is not checked for descent.

```
def length : run Π (- A : Type) → Π (xs : List A) → Nat :=
  λ (- A : Type) → λ (xs : List A) →
    match xs motive (λ _ → Nat)
      | nil => 0
      | cons _ as => suc (length A as)
```

(`examples/list.muro`. `[]` is `nil`; `::` is `cons`.)

```
def size : run Π (t : Tree) → Nat :=
  λ (t : Tree) →
    match t motive (λ _ → Nat)
      | leaf => 0
      | node l r => suc (plus (size l) (size r))
```

(`examples/tree.muro`. Both children are smaller.)

## When is a data type Data?

`+` is allowed only if the type WHNFs to Data. For a user type, every *parameter* must be Data. Indices are not asked.

- `List Nat` is Data. `+xs : List Nat` may be reused.
- `List (Nat → Nat)` is not.
- `Maybe Unit` is Data.
- `Vec A n` is Data iff `A` is. The index `n` is Nat; it does not disqualify the type.

## Emit dialect

A 0-argument constructor is an atom: `:nil`, `:nothing`, `:leaf`.

Otherwise a tagged tuple: `{:cons, a, as}`, `{:just, a}`, `{:node, l, r}`.

`ones2()` is `{:cons, {:suc, 0}, {:cons, {:suc, 0}, :nil}}`.

```
{:ok, src} = Muro.emit_file("examples/list.muro", Muro.Lists)
Code.eval_string(src)
Muro.Lists.length(Muro.Lists.ones2())
# {:suc, {:suc, 0}}
```

Next: [Indexed data](indexed.md).

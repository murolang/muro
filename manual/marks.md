---
title: Marks
slug: marks
order: 3
summary: Π, λ, modes, data, atoms, and streams, one paragraph each.
---

# Marks

`examples/sort.muro` is a run that sorts a list. It imports the `List` it sorts ([Import](language.md#import)). The direction is an atom written in the file.

```
def sort : run Π (d : Atom) → Π (xs : List Nat) → List Nat :=
  λ (d : Atom) → λ (xs : List Nat) →
    match xs motive (λ _ → List Nat)
      | nil => nil
      | cons x xs1 =>
          match d motive (λ _ → List Nat)
            | :asc => insert :asc x (sort :asc xs1)
            | :desc => insert :desc x (sort :desc xs1)
```

`mix muro.check examples/sort.muro` succeeds. Elixir emit prints `:asc` and `:desc`.

## Π

In Muro, Π is the dependent function type. The binder is a name the result may use, so the type of the output can be a different type for each input. That is what lets lookup ask for an index that fits the vector it is given: Π (n : Nat) → Vec A n → Fin n → A. The n in Vec A n and in Fin n is the n passed in. A → B is Π (_ : A) → B, where the result does not mention the argument. The same former one level up is a kind: Π (n : Nat) → Type classifies a family such as IsEven, and it is not itself a Type.

## λ

`λ` is the function that inhabits a Π. `lam` is the ASCII spelling. The body of `sort` in `examples/sort.muro` is `λ (d : Atom) → λ (xs : List Nat) → …`, a function of the direction and then of the list. A λ is that term. The Π is the type it inhabits.

## Modes

`run` is the program and is emitted: `sort` in `examples/sort.muro`. `evidence` is a proof and is erased: `sort-two` in that file is the `:asc` result for a two-element list. `spec` is a family: `IsEven` in `examples/half_ok.muro`.

## data and match

`data` declares constructors, and `match` opens a value built with them. Constructors are the tags. `Vec A n` in `examples/vec.muro` is a list whose length is `n`. A branch binds the constructor's fields: the `vcons` arm names the length of the tail, the element, and the tail.

## Atom

`:asc` is a tag spelled in the file. In `examples/sort.muro` the spellings are `:asc` and `:desc`, and `sort` matches both. Elixir prints the colon. C prints an enum of the spellings used. A spelling the file did not write is not in that set. `:asc` is not a constructor and not a `Nat`.

## ν

A stream does not end. `unfold` builds it: `zeros` in `examples/zeros.muro` is `unfold 0 (λ (_ : Nat) → (0, 0))`. `uncons` is one step: the head, and the same stream at the tail. `Always` and `~` are that step for a proof: `zeros-always-zero` in `examples/always.muro`, and `zeros-bisim` in `examples/bisim.muro`.

The checker is Elixir.
The specification is Agda.
A proof does not become a run.

[The wall](wall.md). [Terms](language.md).

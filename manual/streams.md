---
title: Streams
slug: streams
order: 9
summary: ν, unfold, Always, bisimulation, and declared ν families.
---

# Streams

In brief: μ descends (`match` on Nat). ν is a greatest fixed point. Stream is `ν X. A × X`. Only a `run` Stream becomes an Elixir `Stream`. A non-productive unfold is rejected.

## ν Stream

Stream is primitive: its block is required for shape, then dropped. Any other name declares a ν family ([Declared families](#declared-families)).

```
ν Stream (A : Type) : Type where
  uncons : Stream A → A × Stream A
```

ASCII: `nu Stream (A : Type) : Type where uncons : Stream A -> A * Stream A`.

`uncons` splits a stream into a head and a tail. `head` and `tail` are sugar for `fst (uncons s)` and `snd (uncons s)`, that is, for a `let` on `uncons s` (see [Terms](language.md#products)).

## unfold

A ν value is built by an `unfold`.

```
unfold seed (λ (s : S) → (head, next_seed))
```

The body is a pair. Productivity: in `run` and `evidence`, no definition of the recursive block may occur in the pair’s **head**. The tail may continue the stream. Spec does not run this check.

A definition whose type is a ν need not be an `unfold` itself: `def nats : run Stream Nat := tabulate ident` checks. Such a body may not call its own block; a call into the block is productive only as the tail of an unfold step, so `def s : run Stream Nat := s` is refused.

A stream is not copyable, so a seed of type `Stream` is affine. A Nat seed may be `+`: `(+ k : Nat)` in an unfold step.

### zeros

```
def zeros : run Stream Nat :=
  unfold 0 (λ (_ : Nat) → (0, 0))
```

(`examples/zeros.muro`.) Head is `0`. The next seed is `0` again. `head-zeros` is `{head zeros ≡ 0 : Nat}` by `refl`.

### natsFrom

```
def natsFrom : run Π (n : Nat) → Stream Nat :=
  λ (n : Nat) →
    unfold n (λ (+ k : Nat) → (k, suc k))
```

(`examples/nats.muro`.) Each step reuses `k` because `Nat` is Data.

```
{:ok, src} = Muro.emit_file("examples/nats.muro", Muro.Nats)
Code.eval_string(src)
Muro.Nats.natsFrom(0) |> Stream.take(3) |> Enum.to_list()
# [0, {:suc, 0}, {:suc, {:suc, 0}}]
```

Emit of a checked run Stream is `Stream.unfold/2`. The pair is `{head, next_seed}`. `uncons` becomes two replayable views (`Enum.take/2` and `Stream.drop/2`); affinity was already checked.

## Always

`Always P s` unfolds to `P (head s) × Always P (tail s)`. The binder is a predicate at a stream, and the body instantiates it at the tail. An `unfold` returns a proof at the head and a proof of `Always P` at the tail. The tail proof is the recursive call.

```
def zeros-always-zero : evidence Always Nat (λ (_ : Nat) → {0 ≡ 0 : Nat}) zeros :=
  unfold tt (λ (_ : Unit) → (refl, zeros-always-zero))
```

The tail of `zeros` is `zeros`, so the same proof is the tail obligation. `tt` does not have that type. `Always` of `λ n → {n ≡ 0}` at `natsFrom 0` fails for the same reason: the head is `0`, and the tail asks for the predicate at `natsFrom 1`.

(`examples/always.muro`.) Surface: `Always A P s`. This is evidence. It is omitted at emit. `uncons` of an `Always` proof is `P (head s) × Always P (tail s)`. `head` of the proof is the equation.

## Bisimulation

`σ ~ τ` (ASCII `bisim σ τ`) unfolds to `{head σ ≡ head τ} × (tail σ ~ tail τ)`. After J.J.M.M. Rutten, *Elements of Stream Calculus*, ENTCS 45 (2001), Theorem 2.1.

```
def zeros-bisim : evidence zeros ~ zeros' :=
  unfold tt (λ (_ : Unit) → (refl, zeros-bisim))

def nats-tail-bisim : evidence Π (n : Nat) → tail (natsFrom n) ~ natsFrom (suc n) :=
  λ (n : Nat) →
    unfold tt (λ (_ : Unit) → (refl, nats-tail-bisim (suc n)))
```

(`examples/bisim.muro`.) `uncons` of a proof of `σ ~ τ` is `{head σ ≡ head τ} × (tail σ ~ tail τ)`. Always, `~`, and their inhabitants are evidence (or live in evidence). They are not Elixir streams.

## Declared families

A `ν` block with any name other than `Stream` declares a family over its indices. `uncons` takes the family at its indices, in order, to the body:

```
ν Dom (f : Stream Nat) (g : Stream Nat) : Type where
  uncons : Dom f g → Le (head f) (head g) × Dom (tail f) (tail g)
```

`Dom` is the spec definition `Π (f : Stream Nat) → Π (g : Stream Nat) → Type` whose body is `ν Dom. λ f g → …`: inside the body, `Dom` is the family itself, as the recursive variable is for `Always` and `~`. The body is a type in which the family occurs strictly positively, applied to all its indices; it may occur more than once. A family takes at least one index, and as many as it needs.

An `unfold` of `Dom f g` checks the body at `f` and `g`: the head obligation, and a proof of `Dom` at the tails. The proof at the tails is a call into the block, guarded as for `Always`. `uncons` of a proof reads the same pair back, so `head d : Le (head f) (head g)`.

```
def dom-refl : evidence Π (s : Stream Nat) → Dom s s :=
  λ (s : Stream Nat) →
    unfold tt (λ (_ : Unit) → (le-refl (head s), dom-refl (tail s)))

def zeros-below : evidence Π (n : Nat) → Dom zeros (natsFrom n) :=
  λ (n : Nat) →
    unfold tt (λ (_ : Unit) → (tt, zeros-below (suc n)))
```

(`examples/dominance.muro`.) A family is spec; its proofs are evidence, omitted at emit. Declared families are checked by `Muro.Check` and by the Agda checker (`agda/Muro/ExampleFamily.agda`), and they are outside ⊢, as Stream, `Always`, and `~` are ([Limits](limits.md)).

Next: [Either and Dec](either.md).

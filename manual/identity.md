---
title: Identity
slug: identity
order: 6
summary: Equations, refl, rewrite, and explicit motives.
---

# Identity

In brief: `{a ≡ b : A}` is a type. `refl` checks only when both sides convert. `rewrite` takes an explicit motive. Equations never execute.

## The type

```
{plus (half n) (half n) ≡ n : Nat}
```

ASCII: `{plus (half n) (half n) == n : Nat}`.

The sides `a`, `b` and the sort `A` are checked in spec. An identity is not a program. You cannot emit it. You cannot `+` it.

Kernel identity on `F32` and on `Tensor F32 S` is refused. Machine floats are not a setting for definitional equality. See [Machine numbers](machine.md).

## refl

`refl` checks against `{x ≡ y : A}` only when `x` and `y` convert.

Conversion, in order:

1. Syntactic equality.
2. Stuck-definition congruence, when the first argument is not constructor-headed.
3. Weak head normal form, then compare again.

Fuel bounds reduction (`@fuel 2000` in Elixir, `mix muro.check --fuel N` to change it). Infer and check recurse on the term; they do not spend that fuel. Running out is the error `out of fuel`, not a failed conversion.

So this evidence checks, after `zeros` is a productive unfold whose head is `0`:

```
def head-zeros : evidence {head zeros ≡ 0 : Nat} :=
  refl
```

(`examples/zeros.muro`.)

If the two sides do not convert, `refl` fails. You need `rewrite`, or a `match` that makes them convert in each branch.

## rewrite

```
rewrite eq motive (λ z → P) in t
```

`eq` has type `{lhs ≡ rhs : A}`. The body `t` is checked as `P` with `z` replaced by `rhs`. The whole `rewrite` has type `P` with `z` replaced by `lhs`.

You write the motive. There is no tactic that finds it.

`eq` is checked in evidence, and its uses are discarded: in a run function the equation costs nothing at runtime and is not emitted. Inside a spec term (a type, an erased argument) `eq` is checked in spec, so a type may rewrite along an erased variable: `Π (-e : {n ≡ m : Nat}) → Vec A (rewrite e motive (λ _ → Nat) in m)` is well-formed. What is evidence may be used in spec, never the other way round.

From `plus_suc` in `examples/half_ok.muro`:

```
def plus_suc : evidence Π (n : Nat) → Π (m : Nat) →
                          {plus n suc(m) ≡ suc(plus n m) : Nat} :=
  λ (n : Nat) → λ (m : Nat) →
    match n motive (λ np → {plus np suc(m) ≡ suc(plus np m) : Nat})
      | 0 => refl
      | suc np =>
        rewrite plus_suc np m motive (λ z → {suc(z) ≡ suc(suc(plus np m)) : Nat}) in
        refl
```

The `0` branch converts immediately. The `suc` branch rewrites along the inductive hypothesis, then `refl`.

`half_ok` nests two rewrites: first `plus_suc (half p) (half p)`, then `half_ok p e2`, then `refl`.

## Evidence is an ordinary term

There is no separate proof language. A theorem is a λ-term that uses `match`, `refl`, `rewrite`, and `matchEmpty`. It pays affinity and descent. Instantiating it (`half_ok p e2`) does not consume the caller’s affine resources — those arguments are checked in evidence, and their uses are discarded — but the λ-binders you write inside the theorem still do.

Emit drops the whole definition. See [Emit](emit.md).

Next: [Data](data.md).

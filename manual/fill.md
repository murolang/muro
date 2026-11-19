---
title: Fill
slug: fill
order: 28
summary: mix muro.fill writes one definition body by search. The checker decides.
---

# Fill

`mix muro.fill path.muro --def name` writes a body for one definition. The book already declares the name and the type. The body is `?`. The search tries terms the checker already accepts, in order of size, and writes the first one the checker accepts. It certifies nothing beyond that checker. It is not `mix muro.synth`.

```
mix muro.fill path.muro --def name
mix muro.fill path.muro --def name --bound 8
muro fill path.muro --def name
```

`--bound` is the largest size. The default is 8. `--fuel` is the checker's fuel for each candidate. The default is 2000. `out of fuel` is not acceptance.

## What is tried

Size counts each variable, constructor, application, lambda, and match. A match motive is fixed by the goal and is not counted. `λ (n : Nat) → 0` is size 2, so a bound of 2 on `Nat → Nat` tries the constant and the bound variable. `λ (n : Nat) → suc(n)` is size 3.

Within one size the order is fixed: `0`, `suc`, `tt`, and `refl` as the goal allows, then constructors in the order the book declares them, then other definitions in prelude order, then binders from the outside in. The same book and the same bound produce the same body. A term whose normal form was already tried is skipped. That normal form enters a lambda, an application, a successor, a match on `Nat`, and a match on a datatype, including each branch. The definition being filled is not called.

A function type is introduced as a lambda. An application of a definition or of a binder is saturated. The binder is visible and not erased, and the result of the application is the goal. A partial application is not a candidate. A match scrutinee is a binder. The checker still rejects a term that uses an affine variable twice.

## What is kept

A `run` is kept when the body type-checks and every closed equation in the book about that name still checks. Those are the same closed `refl` facts `--backend exunit` collects. A type alone barely constrains a run: `Nat → Nat` contains `λ (n : Nat) → 0`. The equations are the rest of the specification. A run with no closed equations is kept at the first term that type-checks.

Evidence is kept when the type checks. Any inhabitant is correct. A `spec` is kept the same way.

The first term that passes is parsed and checked again, then written by a rename in the same directory. The rest of the file stays as it was.

Past the bound, the file is left unchanged and the command exits non-zero. The message names the bound and how many candidates were tried. When a candidate type-checks and a closed equation does not, the message counts those failures. A failure of the rest of the book, and `out of fuel`, are counted on their own. They are not closed-equation failures.

## One file

The command reads one file and the prelude. An `import` or a `param` is refused. A body that is not exactly `?` is refused. A second `?` in the book is refused. An indexed datatype is not searched. An erased argument is not synthesized. A partial application is not a candidate. A match on `Unit`, `Empty`, a word, or an atom is not a candidate. A hole under a lambda the book already wrote is left alone.

`examples/fill/add1.muro` starts with `?`. The three equations ask for the successor. `mix muro.fill examples/fill/add1.muro --def add1` writes `λ (n : Nat) → suc(n)`. `examples/fill/add1.filled.muro` is that book.

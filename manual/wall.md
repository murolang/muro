---
title: The wall
slug: wall
order: 4
summary: spec, evidence, and run. Promotion is forbidden.
---

# The wall

In brief: every definition is tagged `spec`, `evidence`, or `run`. The checker will not let a spec become evidence, or evidence become a run. Affinity is taxed the same on theorems as on programs. Emit keeps only `run`.

This is the language, not a style guide.

## Three modes

`m ∈ {run, spec, evid}`. The surface word is `evidence`. Agda writes `evid`. Elixir stores `:evidence`.

| Tag | Meaning | Affinity and descent | Emit |
| --- | --- | --- | --- |
| `run` | A program | Yes | Elixir `def` |
| `run internal` | The same judgment as `run` | Yes | Elixir `defp` |
| `spec` | A type, family, or signature | No. Uses are forgotten | Omit |
| `evidence` | A theorem | Yes. Same tax as `run` | Omit |

`run internal` is Elixir visibility only. Agda `Def` stores the mode, not `def` vs `defp`.

See `examples/internal_ok.muro`: `step` is `run internal` (emits `defp`); `inc` is `run` (emits `def`) and calls `step`.

## Promotion is forbidden

```
spec      ↛  evidence
evidence  ↛  run
spec      ↛  run
```

Using a definition of mode `from` while checking in mode `to`:

| from \ to | run | evidence | spec |
| --- | --- | --- | --- |
| run | yes | yes | yes |
| evidence | no | yes | yes |
| spec | no | no | yes |

A program may mention other programs, and may be mentioned from evidence or spec (for example a type that talks about `half`). A theorem may be used in evidence or mentioned from spec. A spec may only be used in spec.

There is no rule that takes a spec derivation and returns an evidence derivation. The formers that live only in spec (`Nat` as a type, `Π`, identity types, …) have no constructor in a `run` or `evidence` derivation. That is proved for the core fragment in `agda/Muro/Wall.agda`.

Identity has one introduction, `refl`, and it has no `run` derivation (`no-run-rfl` in `Muro.Wall`). Run code cannot build a proof, hand one to a function, or return one, so no proof reaches emitted code. Pass a proof to a `run` function as an erased argument, `(- e : {a ≡ b : A})`: it is checked in spec and not emitted. That argument may be evidence that does not depend on an axiom. A `run` whose dependencies reach an axiom is refused, including when the axiom is reached only through an erased argument, and that run is not emitted. What that check prints is [Axioms](#axioms). An absurd branch (`matchEmpty`) may still have an identity type, since it never runs.

A `run` definition has a run type, used or not: the codomains of its Π, each side of a product, and the body of a ν are data, `Nat`, `Unit`, `Empty`, machine numbers, or names that reduce to one of those. `def e : run {0 ≡ 0 : Nat}` is refused at its type, `e type: no promotion: a run definition has a spec type`. Π domains are not read there; a run variable of a spec type is refused where it is used.

## Axioms

An axiom is a declaration with a type and no body. The tag is `evidence`. It does not reduce. Other evidence may use it, and a spec may mention it. Classical principles stay in evidence and spec. They do not sit in a `run`'s dependency cone. `std:classical.muro` declares excluded middle. See [Library](library.md#classicalmuro).

`mix muro.check` prints one line for each definition the entry file reaches that depends on an axiom, other than a `run` or a `run internal`. The entry file reaches every definition it declares, and every definition mentioned from one it reaches. An imported definition that chain does not mention is not a line. Lines are in book order. Several axioms on one line are separated by `, `, in the order those axioms are declared. Checking `lib/muro/std/classical.muro` prints `dne: depends on classical.LEM`. A reached `spec` or `evidence` is a line, and the check still succeeds.

A `run` or a `run internal` that reaches an axiom is not one of those lines. The check refuses the book, and that run is not emitted. The error names the run. One refusal the checker emits is:

```
bad: a run depends on hidden.LEM
```

That is `def bad : run internal Nat := LEM` in a file named `hidden.muro`. A `run` reached only through an erased argument is the same kind of refusal (`bad: a run depends on Classical.LEM`). A `run` in an imported book that reaches an axiom refuses the book even when the entry file does not mention that run. The checker does not print a depends-line for the run.

A contract is not an axiom and not `LEM`. It is not an evidence term. Declaring one does not emit an axiom, and a `run` that reaches an axiom is still refused when the book also declares a contract. A formula that holds and says `relies idempotent init` prints `<name>: depends on contract idempotent init`. That line is not an axiom line. The contract is [State machines](fsm.md#an-external-contract).

## What is checked in spec

Even inside a `run` or `evidence` term, some positions are spec:

- Erased Π-arguments (`(- x : A)`).
- The two sides of an identity `{a ≡ b : A}`, and the sort `A`.

Arguments at a **call site of an evidence definition** are not spec, but their uses do not count. Instantiating a theorem does not consume affine resources: inside an evidence term, the argument of an application whose head is an evidence definition is checked in `evidence` like any other argument, and its uses are then discarded. Before 0.3.0 the argument was checked in `spec`, so a spec variable could be handed to a theorem from evidence; it cannot now.

Local affine binders in an evidence λ still fail if you use them twice. Evidence pays the same affinity tax as run. It is not a free ride.

## Why the wall is the language

A type is not a proof. A proof is not a program.

If a spec could become evidence, you could treat `IsEven` as if it were a theorem. If evidence could become run, you could compile `half_ok` and run the proof. Muro refuses both. Emit’s fallback for a non-run fragment is `raise "erased term"`.

The slogan is operational:

- **Spec** is forgotten at emit.
- **Evidence** is checked, then forgotten at emit.
- **Run** is checked, then becomes Elixir.

Next: [Terms](language.md).

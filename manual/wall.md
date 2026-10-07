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

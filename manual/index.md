---
title: Manual
slug: index
order: 1
summary: What Muro is, how to read this book, and the three documentation layers.
---

# Muro

**A spec never becomes evidence. Evidence never becomes a run.**

Muro is an explicit affine dependent type theory. You write `.muro` files. Elixir parses them, checks them, and emits running code from `run` terms only. You do not need Agda to use the language.

The name is Spanish for *wall*. The wall stands between a specification, a proof, and a program. Nothing is promoted across it. Types, erased arguments, equations, and paradoxes never execute. Only `run` terms become running code.

This manual is the language book. It is written for people first. Agents can follow it too: every command is copy-pasteable, every example is a real file under `examples/`, and the [grammar](grammar.md) is what the parser implements — not a sketch.

## How to read this

If you want to write a program today, start at [Start](start.md), then [Marks](marks.md), [The wall](wall.md) and [Terms](language.md).

If you are an agent (or you are pairing with one), read [For agents](for-agents.md) first. There are two jobs. Do not mix them.

If you already write `.muro` and need a fact, use [Grammar](grammar.md) and [Examples](examples.md).

If you want to change the calculus itself, stop. That is a different job: [Extending the kernel](extending.md).

## Three layers of documentation

They are not the same book.

| Layer | Where | What it is |
| --- | --- | --- |
| **This manual** | `manual/` | The language. Modes, grammar, examples. What `muro-lang.dev` renders. |
| **Elixir docs** | `@moduledoc` / `@doc`, later `mix docs` | The implementation API: `Muro.Check`, `Muro.Parser`, `Muro.Emit`. Not this folder. |
| **Agda** | `agda/Muro/` | The rules of the calculus. A decision procedure (structural on the term, fuelled where it reduces), an inductive judgment, and the proof that the first is sound for the second on the fragment. Not a certificate that your `.muro` file is correct. |

Agda is not what `mix muro.check` runs. Elixir is. If Agda and Elixir disagree, Agda wins — you fix Elixir to match, after the Agda clause exists.

## What it is

Bidirectional. Explicit. A `?` is an unsolved goal, not a solution.

- One sort, `Type`. Not `Type : Type`, and a kind `Π (x : A) → Type` is not a term of type `Type` either.
- Every binder is written `(x : A)`, or `(+ x : A)`, or `(- x : A)`.
- Every `match` and `rewrite` writes its motive.
- No metavariables, no implicits, no unification, no tactics. `?` always fails.
- A `run` or `evidence` variable is used at most once, unless `+` on Data.
- Recursion in `run` and `evidence` must descend. Spec does not check descent.
- Emitted code is `run` only.

[half of eight is four](examples.md#half_okmuro) is the book that shows the three modes together: evenness as a spec, half as a run, the proof as evidence. Evidence is an ordinary term. It is not emitted.

## Names

| | |
| --- | --- |
| Language | Muro |
| Theory | MuroTT |
| Files | `.muro` |
| Elixir | `Muro`, `Muro.Check`, `Muro.Emit`, `Muro.Parser` |
| Agda | `Muro.*` |
| Surface word for theorems | `evidence` |
| Agda constructor | `evid` |
| Elixir atom | `:evidence` |

Continue to [Start](start.md).

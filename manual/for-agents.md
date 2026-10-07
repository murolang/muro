---
title: For agents
slug: for-agents
order: 15
summary: Two jobs. Do not mix them. Commands and file map.
---

# For agents

In brief: two jobs. Do not mix them. This page is the operational contract. Humans can read it. You must.

## Job A — write a Muro program

**Do**

- Write a `.muro` file against [Grammar](grammar.md).
- Put new programs in `examples/` unless asked otherwise.
- Check with `mix muro.check path.muro`. If the answer is `out of fuel`, the checker gave up reducing; it is not a type error. Retry with `mix muro.check --fuel 20000 path.muro`.
- Read every error. The checker reports each definition that fails, in book order, separated by a blank line. Parse and check errors start with `line:col`. Conversion prints surface types (`Fin n`, not `#0`). A `?` prints `expected` and `context`; fill it.
- Copy syntax from `examples/`, not from memory.
- Keep every binder typed. Write every motive.
- `pred`, `plus`, `inj-suc`, `plus_suc`, `sym`, and `cong` are already in scope (`lib/muro/prelude.muro`). Defining one of those names replaces it, and drops any prelude definition that refers to it.
- Use only tags `run`, `run internal`, `spec`, `evidence`.
- Leave `?` only while a term is unfinished. A hole always fails and is not in the finished book.

**Do not**

- Edit `agda/`.
- Edit `lib/muro/*.ex`.
- Edit `lib/mix/tasks/`.
- Add a fourth representation (no raw HOAS as inductive syntax).
- Invent tags, implicits, metavariables, or tactics.
- Promote a spec to evidence or evidence to run.
- Treat this manual as ExDoc. Elixir API docs are `@moduledoc` / `mix docs`.

A definition is in the book as soon as `Muro.Parser.parse/1` returns it. The checker sees the whole book. Forward references are allowed. Emit keeps `run` only.

Skeleton:

```
-- comments start with --
def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
  λ (n : Nat) → λ (m : Nat) →
    match n motive (λ _ → Nat)
      | 0 => m
      | suc np => suc(plus np m)
```

```
mix muro.check examples/your_file.muro
```

Emit (after check):

```
{:ok, src} = Muro.emit_file("examples/your_file.muro", Foo)
IO.puts(src)
```

## Job B — change the type theory

Read [Extending the kernel](extending.md). Order is mandatory: Agda syntax → subst → check → `make agda` → Elixir mirror → `mix test` and `mix muro.check`.

Users still only run Mix. If you are doing Job A, you are not doing Job B.

## Authority

| Question | Answer |
| --- | --- |
| What is the language? | This manual, especially [Grammar](grammar.md) |
| What does the parser accept? | `lib/muro/parser.ex` |
| What does the checker accept? | `lib/muro/check.ex`, specified by `agda/Muro/Check.agda` |
| If Agda and Elixir disagree? | Agda wins. Fix Elixir after the Agda clause exists. |
| Is Agda a certificate for a `.muro` file? | No. `mix muro.check` is. |
| Canonical book? | `examples/half_ok.muro` = `Muro.Example.book/0` = `agda/Muro/Example.agda` |

## File map

```
manual/                 this book (muro-lang.dev). Not ExDoc.
examples/*.muro         programs
lib/muro/parser.ex      .muro → named FOAS
lib/muro/ast.ex         named FOAS, to_db
lib/muro/print.ex       surface syntax, locations, hole messages
lib/muro/subst.ex       de Bruijn subst
lib/muro/check.ex       Elixir mirror of ⊢
lib/muro/prelude.ex     book behind every checked file
lib/muro/prelude.muro   pred, plus, inj-suc, plus_suc, sym, cong
lib/muro/emit.ex        run → Elixir source
lib/muro/example.ex     same book as Agda
lib/mix/tasks/muro.check.ex
agda/Muro.agda          public re-export
agda/Muro/Syntax.agda   Tm n (de Bruijn) and PTm V (PHOAS)
agda/Muro/Subst.agda    wk, sub, inst
agda/Muro/Unembed.agda  PHOAS → de Bruijn (TERMINATING, not --safe)
agda/Muro/SubstLemmas.agda  renaming / substitution algebra
agda/Muro/Env.agda      Sig, Ctx, uses, mode order (shared by Check and ⊢)
agda/Muro/Check.agda    the decision procedure: structural on the term, fuel only where it reduces
agda/Muro/Tag.agda      constructor tags (Check compares tags before structure)
agda/Muro/Spine.agda    application spines (constructor / dty applications), spine views
agda/Muro/Frag.agda     the ⊢ fragment as a predicate on terms, signatures, contexts
agda/Muro/Reduction.agda  parallel reduction ⇛, confluence
agda/Muro/Convert.agda  whnf strategy ⟶ and conversion ≈ for ⊢
agda/Muro/Data.agda     IsData, InstParams, BrTy: what the data rules are stated with
agda/Muro/Judgement.agda  inductive ⊢ with uses (core fragment, with data / match)
agda/Muro/Typing.agda   declarative ⊨ (no uses); substitution, preservation
agda/Muro/Wall.agda     mode wall lemmas
agda/Muro/Consistency.agda  Empty-nf, progress, preservation at Empty; Empty-evid is not proved
agda/Muro/Soundness.agda  Check says yes → ⊢ derives it, on the fragment
agda/Muro/Soundness/Conv.agda   whnf-sound, conv-sound
agda/Muro/Soundness/Views.agda  views, isData-sound, GoodSig, instParams / index clashes on a telescope
test/muro_check_test.exs
```

## Commands

```
mix deps.get
mix test
mix muro.check
mix muro.check examples/half_ok.muro
make agda          # Job B only; needs vendor/agda-stdlib v2.3
```

Success line from `mix muro.check`:

```
All terms check. Evidence never becomes a run.
```

`Muro.Check.check_sig/2` returns `:ok` on a well-typed book, or `{:error, msg}` with every definition error in book order. `check_sig(book, fuel: n)` sets the fuel for each definition. Definitions are checked concurrently; the fuel is the bound, not a wall-clock timeout.

## Representations (do not add a fourth)

| Layer | Form | Where |
| --- | --- | --- |
| Parser / pretty / emit | named FOAS | `lib/muro/{parser,ast,emit}.ex` |
| Check / subst | de Bruijn | `lib/muro/{check,subst}.ex`, `agda/Muro/{Check,Subst}.agda` |
| Examples in Agda | PHOAS `PTm V` | `agda/Muro/Syntax.agda`, `agda/Muro/Example.agda` |
| Metatheory | de Bruijn `Tm n` | `agda/Muro/Syntax.agda` |

Elixir constraints when you are in Job B: ASCII identifiers only. Do not define local `hd/1`. Guards cannot call ordinary `defp` helpers.

## What is not in the language

Type : Type, cubical, tactics, implicits, unification, metavariables (a `?` always fails; it does not unify), extra quantities, user-defined ν-predicates, `+` on Stream or Either, typing raw Elixir, emitting spec or evidence.

Full list: [Limits](limits.md).

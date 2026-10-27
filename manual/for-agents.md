---
title: For agents
slug: for-agents
order: 17
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
- Write a library for many environments with `param` entries, and check it through a file that supplies them with `def` or `data` of the same names and tags ([Params](language.md#params)). `mix muro.check` on the library itself names the params it is missing.
- Leave `?` only while a term is unfinished. A hole always fails and is not in the finished book.

**Do not**

- Edit `agda/`.
- Edit `lib/muro/*.ex`.
- Edit `lib/mix/tasks/`.
- Add a third representation (no raw HOAS as inductive syntax).
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
examples/cshrl/         CSHRL: lib/ on params, envs/ supply them
lib/muro/parser.ex      .muro → named FOAS
lib/muro/ast.ex         named FOAS, to_db
lib/muro/print.ex       surface syntax, locations, hole messages
lib/muro/subst.ex       de Bruijn subst
lib/muro/check.ex       Elixir mirror of ⊢
lib/muro/session.ex     session / conform, mirror of decide and finishes; `rec X. S` unfolds one action and a repeated head conforms
lib/muro/talk.ex        one description of an exchange, mirror of seen
lib/muro/place.ex       place / scheme / move, mirror of decide
lib/muro/prelude.ex     book behind every checked file
lib/muro/prelude.muro   pred, plus, inj-suc, plus_suc, sym, cong
lib/muro/emit.ex        run → Elixir source
lib/muro/emit/otp.ex    a conformance, and a reading, is a GenServer; a meeting starts the two processes as each other's peer; a `rec` is a tail call on `drive` (`--backend otp`)
lib/muro/emit/node.ex   a cross, and a cross reading, is one call and one monitor (`--node`)
lib/muro/example.ex     same book as Agda
lib/mix/tasks/muro.check.ex
agda/Muro.agda          public re-export
agda/Muro/Syntax.agda   Tm n (de Bruijn)
agda/Muro/Subst.agda    wk, sub, inst
agda/Muro/SubstLemmas.agda  renaming / substitution algebra
agda/Muro/Env.agda      Sig, Ctx, uses, mode order (shared by Check and ⊢)
agda/Muro/Check.agda    the decision procedure: structural on the term, fuel only where it reduces
agda/Muro/Session.agda  affine session judgment; a payload is a nat, a bit, unit, a pair, a record, a vector whose length is a received nat, a nat at most a bound the sender owes evidence for, or a non-indexed declared data type; a received bit selects one of two arms; a name is a session declared earlier, opened on the declaration prefix with no fuel; a parameter is a nat; %1 must finish; decide searches, skel is the OTP actions
agda/Muro/Rec.agda      equi-recursive `rec X. S` unfolded to a guarded coinductive protocol (`--safe --guardedness`); a guarded self-call of a parameterised session is the same coinduction (`stream`); `dual∞`, conformance, and meet are bisimulations; a declared data payload inside `rec` meets when `sent` holds; `Finishes` stays finite, so a jump is not `%1`. `agda/Muro.agda` imports it, so that file carries the same pragma
agda/Muro/Dual.agda     the other end of a session; send swaps with recv, a dependent receive swaps with a dependent send, an evidence send swaps with an evidence receive, an indexed bit keeps its index and each arm dualises, and the payload type stays; `session name := dual name` follows it
agda/Muro/Meet.agda     two processes on one channel; a send meets a receive of the same payload type and the value inhabits it; a received nat instantiates a vector length; an evidence payload meets as a nat; a literal bit meets the arm of that bit; a variable meets a receive at its innermost binding; `meet name : left with right` follows it
agda/Muro/Talk.agda     one description of an exchange; say names one payload and one continuation; `session name := seen party with party in talk` follows it
agda/Muro/Seated.agda   a party of a description sits at a place; `seat name : party at place in talk` follows it; the same place stays; two places cross once
agda/Muro/Held.agda     a meeting at the parties' places; the same place stays; two places cross once; a `.muro` file does not write it
agda/Muro/Arrow.agda    %1 on a Π binder must be used; both marks are the affine quantity
agda/Muro/Linear.agda   multiplicity on a session endpoint; λ¹ must be used once; ⊸ accepts or returns it; the protocol is `SExp`, so `rec` and a declared data payload are endpoints; `dualS` keeps both; `--safe --guardedness`; not a Tm
agda/Muro/Place.agda    placement coeffect; ambient by default; one boundary; run has no seat
agda/Muro/Located.agda  a session at a place; `endpoint` and `read` follow the sitting; `--node` follows a cross reading; `--backend otp` follows the process
agda/Muro/Tag.agda      constructor tags (Check compares tags before structure)
agda/Muro/Spine.agda    application spines (constructor / dty applications), spine views
agda/Muro/Frag.agda     the ⊢ fragment as a predicate on terms, signatures, contexts
agda/Muro/Reduction.agda  parallel reduction ⇛, confluence
agda/Muro/Convert.agda  whnf strategy ⟶ and conversion ≈ for ⊢
agda/Muro/Data.agda     IsData, InstParams, BrTy: what the data rules are stated with
agda/Muro/Judgement.agda  inductive ⊢ with uses (core fragment, with data / match / ν)
agda/Muro/Typing.agda   declarative ⊨ (no uses); substitution, preservation
agda/Muro/Wall.agda     mode wall lemmas
agda/Muro/Consistency.agda  Empty-nf, progress, preservation at Empty; Empty-evid is not proved
agda/Muro/Soundness.agda  Check says yes → ⊢ derives it, on the fragment
agda/Muro/Soundness/Conv.agda   whnf-sound, conv-sound
agda/Muro/Soundness/Views.agda  views, isData-sound, GoodSig, instParams / index clashes on a telescope
test/muro_check_test.exs
```

## Install

`mix muro.check` and `mix muro.emit` run in any directory once the archive is installed, with or without a `mix.exs`.

Once 0.16.73 is on Hex:

```
mix archive.install hex muro
```

Until that release, from a checkout of this version:

```
mix deps.get
mix archive.build
mix archive.install muro-0.16.73.ez
```

From GitHub, Mix fetches the default branch and builds the archive:

```
mix archive.install github murolang/muro
```

`--force` skips the install question.

`mix muro --version` prints `Muro v` and the version of the copy that ran. If a project depends on muro and the archive is also installed, Mix uses the project's copy. The version line names that copy.

`mix muro.emit path.muro` prints the Elixir module. `mix muro.emit path.muro > path.ex` saves it.

`--backend c` writes C. Add `{:elixir_make, "~> 0.10", runtime: false}` to the project deps, or run the task inside a project that depends on muro. Without `elixir_make`, the task stops and names that dependency. `nx` and `makeup` are optional. Checking and emitting Elixir do not load them.

## Commands

```
mix deps.get
mix test
mix muro.check
mix muro.check examples/half_ok.muro
mix muro --version
make agda          # Job B only; needs vendor/agda-stdlib v2.3
```

On success, `mix muro.check` prints the version that checked the book, then:

```
Muro v0.16.73
All terms check. Evidence never becomes a run.
```

`Muro.Check.check_sig/2` returns `:ok` on a well-typed book, or `{:error, msg}` with every definition error in book order. `check_sig(book, fuel: n)` sets the fuel for each definition. Definitions are checked concurrently; the fuel is the bound, not a wall-clock timeout.

## Representations (do not add a third)

| Layer | Form | Where |
| --- | --- | --- |
| Parser / pretty / emit | named FOAS | `lib/muro/{parser,ast,emit}.ex` |
| Check / subst | de Bruijn | `lib/muro/{check,subst}.ex`, `agda/Muro/{Check,Subst}.agda` |
| Examples and metatheory | de Bruijn `Tm n` | `agda/Muro/Syntax.agda`, `agda/Muro/Example*.agda` |

Elixir constraints when you are in Job B: ASCII identifiers only. Do not define local `hd/1`. Guards cannot call ordinary `defp` helpers.

## What is not in the language

Type : Type, cubical, tactics, implicits, unification, metavariables (a `?` always fails; it does not unify), extra quantities, `+` on Stream or Either, typing raw Elixir, emitting spec or evidence.

Full list: [Limits](limits.md).

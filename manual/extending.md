---
title: Extending the kernel
slug: extending
order: 17
summary: How to change the type theory. Agda first, then Elixir.
---

# Extending the kernel

In brief: this is Job B. If you only want a program, stop and go back to [Start](start.md). Order is mandatory. If Agda and Elixir disagree, Agda wins.

## Order

1. **Agda syntax** (`agda/Muro/Syntax.agda`) if you add a constructor — both `Tm n` and `PTm V`.
2. **Subst** (`agda/Muro/Subst.agda`): `wk`, `sub`; `toPHOAS` / `unembed` in `agda/Muro/Unembed.agda`. Pattern-lambdas passed to `sub` do not compute; use a named function (`instσ`, `motSucσ`).
3. **Check** (`agda/Muro/Check.agda`): an `infer′` / `check` clause, and the matching constructor in the documentary ⊢ at the top of the file.
4. **Judgement** (`agda/Muro/Judgement.agda`) if the constructor is in the core fragment: the same rule as an inductive constructor, with uses, and the same rule without uses in `Muro.Typing` (`⊨⁰`) with a `forget-⇒` / `forget-⇐` clause. If it reduces, a `⟶` rule in `agda/Muro/Convert.agda` and a `⇛` rule plus a `dev` clause and its `tri` case in `agda/Muro/Reduction.agda`; every new constructor needs a `⇛` congruence rule and a clause in each lemma of `Muro.Reduction` and `Muro.SubstLemmas`. Then `Muro.Wall` and `Muro.Consistency` must still check under `--safe`; a new ⇒ rule needs a `spec-⇒-uses` clause, `⊨-mode` / `⊨⁰-ren` / `⊨⁰-sub` clauses, a `pres⁰` case for each step it takes or `()` if it is rigid, and, if it is an introduction or eliminator, `Empty-intro` / `Empty-nf⊨` / `progress` clauses. A rule whose subject is a variable rather than a constructor (`t-ctor` types any constructor spine) also needs a clause wherever the term was matched with `()`: `ctor-inv` in `Muro.Typing` is the inversion for that shape.
5. `make agda` until the example twin decides (`half_ok-checks` is `refl` for the canonical book). Twins are examples of the rules, not a proof that the book is correct.
6. **Elixir mirror**, same shapes, each checker clause commented with the Agda constructor (`⇒-var-run`, `⇐-refl`, …):
   - `lib/muro/ast.ex`
   - `lib/muro/subst.ex`
   - `lib/muro/check.ex`
   - `lib/muro/parser.ex` / `lib/muro/emit.ex` if it is surface or run code
7. `mix test` and `mix muro.check`. A rule change gets a negative test: a book the old rule accepted and the new rule refuses.

Do not add a fourth representation. Do not use raw HOAS (`Tm → Tm`) as inductive syntax.

Elixir `Muro.Ast.to_db/2` sends named FOAS to de Bruijn (unbound names become `{:def, name}`).

## Rules that keep the sort honest

Some premises are there for consistency of the calculus, not for programs. Keep them when you add a former.

- `⇒-pi`: the codomain is checked against `Type`, not merely well-formed. `Π (x : A) → Type` is a kind (`type-pi`), not a term of type `Type`.
- `⇒-prod`, `⇒-nu`: components and the ν body are checked against `Type`.
- Constructor fields are checked against `Type` (`checkCtorFields`); parameters `(A : Type)` are exempt.
- `⇒-idt` is the deliberate exception: the sort in `{a ≡ b : A}` is only `wf`, so `{Nat ≡ Unit : Type} : Type`. That is the shape of Coq's `eq` in impredicative `Prop`, a singleton family indexed by a large sort with elimination allowed. `refl` has no field, so `rewrite` cannot project a type back out and no retract of `Type` arises. Keep it a singleton: an identity type with a field would need the same restriction as constructor fields.

Relaxing any of these to `wf` makes `Type` a retract of a small type, and with `match … motive (λ _ → Type)` or β that is Girard's paradox. That happened once with `⇒-pi`; the test `"a kind is not a small type"` in `test/muro_check_test.exs` guards it.

## Elixir constraints

- ASCII identifiers only. No unicode primes, no mixed-script atoms.
- Do not define local `hd/1`.
- Guards cannot call ordinary `defp` helpers.

## What Agda is

Agda holds the rules. It is not a certificate that a `.muro` file is correct. It is not what `mix muro.check` runs.

- `Muro.Env` — `Sig`, `Ctx`, uses. Shared by `Muro.Check` and ⊢.
- `Muro.Check` — the decision procedure, with a documentary ⊢ (no uses) at the top of the file. Structurally recursive on the term and `--safe`; fuel is spent only where a term is reduced (`whnf`, `conv`, `isData`, `clashIdx`), and running out is `fail outOfFuel`, never an unreduced term. A constructor spine is checked from its head (`inferCtorSpine`: the constructor's type at the parameters, then one Π per argument), a branch one λ at a time (`checkBr` / `checkBrPi`).
- `Muro.SubstLemmas` — the renaming / substitution algebra of `Tm` (`ren-ren`, `sub-sub`, `sub-inst`, `inst-wk`, …), pointwise, no function extensionality.
- `Muro.Tag` — a constructor number for each `Tm` constructor. `Check.synEq` and `Check.convN` compare tags before structure, so proofs about them case on two terms of equal tag instead of listing every off-diagonal pair.
- `Muro.Spine` — application spines `appsFrom h as` as a relation (`Spine h as e`), read back by `unspine`, unique for rigid heads, and their renaming / substitution lemmas. The spine views `Check` uses (`ctorSpine`, `dtyArgs`, `defArgs`) are characterised here.
- `Muro.Frag` — the ⊢ fragment as a predicate on terms (`Frag`), on lists, on signatures (`FragSig`), and on contexts (`FragCtx`), closed under renaming and substitution.
- `Muro.Reduction` — parallel reduction `⇛` (δ, β, ι including ι for `match` on a constructor spine, `ann`, congruent under every constructor), closed under substitution, confluent by complete developments. Rigid heads and data-headed spines are preserved along `⇛*`.
- `Muro.Convert` — the weak-head strategy `⟶` (exactly `Check.whnf`: deterministic, with normal and neutral forms `Nf` / `Ne`; constructor and `dty` spines are normal), and conversion `≈`, the equivalence generated by `⇛`. `≈` is a congruence, closed under substitution, and joinability by confluence; `≈-shape` separates rigid heads, `≈-pi-inj` / `≈-idt-inj` invert Π and ≡, `≈-dty-inj` inverts a `dty` spine (same type, convertible arguments), and a constructor spine is never convertible to a `dty` spine or to a rigid head.
- `Muro.Data` — what the data rules are stated with: `IsData` (Nat, Unit, Empty, a `dty` spine whose parameters are Data, closed under `≈`) and `ReuseOk`; `InstParams` (a constructor type instantiated at the parameters); `BrTy` (the type of a `match` branch: one Π per field, then the motive at the constructor application). Each is closed under renaming, substitution, and conversion of the telescope.
- `Muro.Judgement` — inductive ⊢ with uses for the core fragment (Π, λ, application, Nat, Unit, Empty, identity, `rewrite`, `def`, annotation, `data`, pairs with `let` in both modes; `⇒-letp` needs the body's type to be a double weakening, which `Check` decides with `Subst.strengthen₂`, a partial renaming, sound by `SubstLemmas.strengthen₂-sound`). Conversion is `≈` in spec mode, so every def unfolds, as in `Check.whnf`. Data as in `Check`: `dty` is a spec term of its declared kind (`⇒-dty`); a constructor application is checked against a `dty` type, the parameters taken from the type and the arguments checked along the instantiated telescope, an erased field in spec (`⇐-ctor`, with the constructor spine as a `Muro.Spine` view and the arguments along the telescope by the list judgment `T ▹ as ⇝ R`, built from the head outwards as `Check.inferCtorSpine` walks it: `args-[]`, `args-snoc`); `match` on a data type, indexed or not, has the motive at the scrutinee's indices and the scrutinee (`⇒-mData`: `motApp P is e`, with `MotiveOk` for the motive and `brs⟨ … ⟩` for the branches, one per constructor in declaration order, each typed at its constructor's own indices, a constructor whose numeral index clashes with the scrutinee's skipped by `brs-skip`). ⊢ does not check the declarations of σ (positivity, small fields: `Check.checkData`).
- `Muro.Typing` — the declarative judgment `⊨` the metatheory is about: ⊢ without uses, conversion at the root of every rule. Proved: ⊢ is sound for ⊨ (`forget-⇐`), mode weakening along run ≤ evid ≤ spec, renaming, substitution, and preservation (`pres`: a `⟶` step keeps the type of a derivation in any mode, given `WfSig`). For data, `t-ctor` types a whole constructor spine (there is no rule for a bare constructor, so `ctor-inv` recovers the spine's derivation), and the ι case of `pres` is `brApp`: the branch for the constructor, applied to the constructor's arguments, has the motive at the scrutinee. It needs nothing of the data declarations beyond what the derivations carry.
- `Muro.Wall` — mode wall lemmas. No promotion.
- `Muro.Consistency` — no closed normal evidence term has type Empty (for ⊢ and for ⊨), closed evidence terms make progress, preservation holds at Empty; `Empty-evid` itself is not proved (normalisation of closed evidence is the one explicit hypothesis of `Empty-evid-from`). `σ-empty` declares no data type, so constructor and `dty` spines are untyped there. ν and Tensor are still outside ⊢.
- `Muro.Soundness` (with `Muro.Soundness.Conv` and `Muro.Soundness.Views`) — the executable checker is sound for ⊢ on the fragment. `Conv`: `whnf-sound` (when `Check.whnf` returns `ok u`, `t ⟶* u` in spec and `u` is in the fragment), `synEq-sound`, `conv-sound` (`Check.conv` says yes → `≈`). `Views`: the Π / identity / data views, `isData-sound`, `GoodSig`, `instParams-sound`, `clashes-sound` (the index-clash test says clash → `Data.Clash`). `Soundness`: `infer-sound` / `check-sound` / `checkTy-sound`: over a `GoodSig` (a `FragSig` whose constructor types are telescopes ending in the data type at its parameters and indices) and a `FragCtx`, `infer k σ rs Γ m e ≡ ok (A , u)` gives a ⊢ derivation of `e` with uses `u` and a type convertible to `A`; `check` and `checkTy` likewise. `checkDef-sound` and `checkSig-sound` are the corollaries for definitions and whole signatures. The mutual proof is by structural recursion on the fragment witness of the term, following `Check` (`inferCtorSpine-sound` on the head of a spine, `checkBrPi-sound` on the λ of a branch, `checkMotive-sound` on the motive's telescope). Out of fuel is `fail`, so every lemma is about the `ok` case; the theorem holds for every fuel.

`Muro.Judgement`, `Muro.Typing`, `Muro.Wall`, `Muro.Consistency`, `Muro.Frag`, `Muro.Tag`, `Muro.Check`, the `Muro.Soundness` modules, and what they import are checked under `--safe`: no postulates, no `TERMINATING`. Only `Muro.Unembed` (PHOAS → de Bruijn, for the example twins) carries a `TERMINATING` pragma. Example twins (`Example*.agda`) are examples of those rules.

The order of the manual is what `Muro.Soundness` enforces: a clause of `Check` that ⊢ does not derive is a hole in the proof, not a feature of the checker. Three such clauses were corrected on the way to the theorem, in Agda first and then in `lib/muro/check.ex`: `checkTy` is syntax-directed (a kind is recognised by its shape, anything else must infer a type convertible to `Type`; reducing first accepted `(λ (x : Nat) → Type) 0` as a kind), the argument of an application in evidence mode is checked in evidence even when the head is an evidence definition (its uses are then discarded: `Env.appUses`), and `isData` is fuelled.

Two facts about the modes that the metatheory depends on:

- Conversion does not see the wall. `Check.whnf` unfolds every def, so ⊢ and ⊨ take `≈` in spec mode. Conversion is about types; the wall is about terms.
- Positions are monotone in the mode. Every premise of a rule is in a mode ≥ the mode of its conclusion: an erased argument is spec, a type is spec, and the equation of a `rewrite` is `evidence` in a run or evidence term and spec in a spec term (`Env.rwtMode`). This is what the substitution lemma needs (a β step substitutes a term of the λ's mode for a variable that may be used at any premise's mode), so preservation holds in every mode. Before 0.8.0 the equation was evidence in every mode and preservation was proved for run and evidence only.

## Build

Agda 2.8+ and standard library 2.3 (no `--type-in-type`):

```
git clone --depth 1 --branch v2.3 https://github.com/agda/agda-stdlib.git vendor/agda-stdlib
make agda
```

`make agda` is `agda --no-libraries -i agda -i vendor/agda-stdlib/src`, first with `--safe` on the theorem modules (`Muro.Wall`, `Muro.Consistency`, `Muro.Frag`, `Muro.Tag`, `Muro.Check`, `Muro.Soundness`, which import `Muro.Typing`, `Muro.Data`, `Muro.Convert`, `Muro.Reduction`, `Muro.Spine`, `Muro.SubstLemmas`, `Muro.Soundness.Conv`, `Muro.Soundness.Views`), then on the whole tree with the example twins (`Muro.Unembed` carries a `TERMINATING` pragma and is not `--safe`). `make agda-soundness` checks `Muro.Soundness` alone; it takes about ten minutes. The stdlib checkout ships extra `.agda-lib` files that must not be loaded.

CI runs the Elixir job and `make agda` on every push and pull request.

## Named FOAS (parser output)

```
{:var, name}
:typ | :nat | :ze | {:su, t} | :unit | :one | :empty
{:pi, qty, a, name, b}
{:lam, qty, a, name, t}
{:app, f, a}
{:mnat, e, x, p, z, y, s}
{:memp, e, x, p}
{:munit, e, x, p, u}          -- kernel only
{:idt, ty, a, b}
:rfl
{:rwt, eq, x, p, t}
{:def, name}
{:ann, e, a}                  -- kernel only
{:prod, a, b} | {:pair, a, b}
{:letp, e, a, b, t}           -- let (a, b) = e in t; fst / snd parse to it
{:stream, a} | {:unf, seed, f} | {:ucons, s}
{:sum, a, b} | {:left, t} | {:right, t}
{:msum, e, x, p, a, l, b, r}
```

`qty` is `:affine | :reuse | :erased`. A book entry:

```
%{name: "half", mode: :run, export: true, type: named, body: named}
%{name: "IsEven", mode: :spec, type: named, body: named}
%{name: "half_ok", mode: :evidence, type: named, body: named}
```

`export` is present only on `:run` (`true` → `def`, `false` → `defp`).

De Bruijn drops the name strings: `{:pi, q, a, b}`, `{:lam, q, a, t}`, `{:mnat, e, p, z, s}` with index 0 = nearest binder.

## Bidirectional rules

```
σ , Γ ⊢[ m ] e ⇒ A     infer
σ , Γ ⊢[ m ] e ⇐ A     check
```

Hard rules you must not relax without a new theory:

1. A run or evidence variable is used at most once, unless `+` on Data.
2. Run and evidence recursion descends on one non-erased argument position, the same at every self-call, with a smaller variable there; a self-reference must be applied. Spec does not check descent. (`RecSt`, `checkRec`, `selfApplied`, `checkBody` in `Check`; the proof does not depend on the recursion state.)
3. No promotion. Erased variables have no computational use.
4. Emitted code is run only.

Conversion: syntactic equality first; then stuck-def congruence when the first argument is not constructor-headed; then WHNF. Fuel is for reduction (`whnf`, conversion, `isData`, the index-clash test); infer and check are structural on the term. Out of fuel is an error, not an unreduced term: a new use of `whnf` must propagate `{:error, _}` (Elixir) / `Result` (Agda), and a new recursion that is not on a subterm must spend fuel in a clause head, as `clashIdx` does.

After you change the kernel, update this manual so `manual/` stays the language book. Do not put the change only in `@moduledoc`.

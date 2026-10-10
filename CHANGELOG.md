# Changelog

## 0.16.13

`+` accepts a copyable type: Data, a Π type, or a pair of copyable types. A Data argument at a `+` position keeps its uses, as before. A function (or a pair holding one) copies by closure, so such an argument has every use inside it counted as many: `twice (addn n) 1` with `twice : Π (+ f : Nat → Nat) → …` checks when `n` is reusable and is refused with `affine variable used as reusable` when `n` is affine. A constructor may declare a `+` field of function type under the same rule, and the `+` on a `match` branch binder is now checked by `Muro.Check` as the Agda checker always did. A pair of two Data types is Data. The refusal for a stream at `+` reads `+ requires a copyable type: Data, a pair of them, or a function`.

### Kernel

- `Data.IsCopy`, `Data.CopyOk`, `Data.d-prod`; `Env.scaleω`; `Judgement.⇒-app-copy`, `args-snoc-copy`, `CopyOk` on the λ rules and on `bt-pi`; `Typing`, `Wall`, `Consistency`; `Check.isCopy`, `Check.fieldUses`; `Soundness.Views.isCopy-sound`, `copyOk-sound`, `prodData-sound`; `Soundness`. Agda first, then `Muro.Check` (`is_copy`, `reuse_arg_uses`, `scale_omega`, `field_uses`).

### Manual

- Terms: copyable types and the scaling of a function argument at `+`.
- Data: a `+` field of function type.
- Either: a refutation is copyable.
- Limits: `P → Empty` removed from the list of refusals.

### Package

- Version 0.16.13.

## 0.16.12

One file may name another. `import "list.muro"` loads that file. The path is relative to the importing file, and the string is the whole path. The imported file is checked, and its data, constructors, and definitions come into scope. Evidence stays in scope for a proof and is erased on emit. There is no seal. A missing file is an error that prints the path. A name already declared in the importer is an error that prints both sites. A cycle of imports is an error. `examples/sort.muro` imports `list.muro` and does not declare `List`.

### Load

- `Muro.Load`. An `import` is resolved from the importing file.

### Manual

- Terms: import names a file.
- Marks: `sort.muro` imports the list it sorts.

### Package

- Version 0.16.12.

## 0.16.11

Emitted C allocates through `MURO_ALLOC`. The macro is `malloc` unless the caller defines it before the generated file is compiled. A long-running process can point it at one block and set the cursor back to the start after each call. The pointer a function returns points into that block, so the caller reads or copies it before the reset. A fieldless constructor stays a static object and is not taken from the block.

### Emit

- `Muro.Emit.C`. Allocations call `MURO_ALLOC`.

### Manual

- Emit: the macro, and resetting the block after a call.

### Package

- Version 0.16.11.

## 0.16.10

A constructor with no fields was a fresh `malloc` on every use. `nil`, `nothing`, `true`, and `false` each allocated. `tt` already returns the address of one static object. A fieldless constructor now does the same, including one whose arguments are all erased. A constructor with a field still allocates. Generated code writes fields only in that allocating constructor, so sharing the static object cannot be observed.

### Emit

- `Muro.Emit.C`. A constructor with no runtime fields is one static object.

### Manual

- Emit: a fieldless constructor is static, like `tt`.

### Package

- Version 0.16.10.

## 0.16.9

C names that are keywords or library functions stay out of the way. `true` and `false` are keywords in C23 and macros in `<stdbool.h>`, so a constructor with either spelling became `static muro_bool *true(void)` and `cc` rejected it. `read`, `write`, `delete`, and `error` clash the same way once a harness includes `<unistd.h>` or compiles as C++. The emitter already prefixed C11 keywords. That list now runs through C23, and it includes the `<stdint.h>` typedefs the header itself includes and the common functions from stdio, stdlib, string, and unistd. `half` stays `half`.

### Emit

- `Muro.Emit.C`. A reserved C name is prefixed with `muro_`.

### Manual

- Emit: which C names get the prefix.

### Package

- Version 0.16.9.

## 0.16.8

Distinct atom spellings stay distinct in C. `:A` and `:a` both became `MURO_A`, and `cc` rejected the repeated enumerator. The checker and Elixir already kept them apart. The first spelling in the file keeps its enumerator. Each later spelling that sanitizes to the same identifier is bumped, the way other C names are. `:asc` stays `MURO_ASC`.

### Emit

- `Muro.Emit.C`. Atom enumerators are unique after sanitizing case, `-`, and `'`.

### Manual

- Terms: a colliding atom spelling gets a numeric suffix.

### Package

- Version 0.16.8.

## 0.16.7

A lambda applied on the spot emits to C. `(λ (m : Nat) → suc m) n` checked, and Elixir emitted it, and the C backend refused it with `c:lambda`. The argument is evaluated once into a local and the body uses that local. An erased binder drops the argument. A chain of lambdas peels one binder at a time. An unapplied lambda, and a call of a local function, are still `c:lambda`.

### Emit

- `Muro.Emit.C`. An application whose head is a lambda is a let.

### Manual

- Emit: an applied lambda is a local.

### Package

- Version 0.16.7.

## 0.16.6

A field that mentions another data type is strictly positive only when that type's fields are. `Bad` with a field `Wrap → Empty`, and `Wrap` with a field `Bad`, each checked as positive on its own, and together they are a proof of `Empty`. The checker instantiates the other type's parameters and holds every field to the same test. `Tree` and `Forest`, each storing the other as a field, still check. Agda `absentGo` treated the other data type as opaque; both checkers now open it.

### Checker

- `Muro.Check` and `agda/Muro/Check.agda`. Positivity and absence descend into another data type's constructor fields. A type already being unfolded is the inductive occurrence.

### Manual

- `examples/bad_wrap.muro`, in `examples.md`. Data and limits: the other data type is not opaque.

### Package

- Version 0.16.6.

## 0.16.5

A name is one declaration. Two data types both named `Foo`, a definition with a constructor's name, and two definitions both named `x` were accepted. The first is a proof of `{suc 0 ≡ 0 : Nat}`, then of `Empty`: the match looks up one `Foo` and a constructor of the other, skips the branch, and never checks it. Definitions, data types, and constructors are one set of names. Agda refers to each by index, so the collision cannot be written there.

### Checker

- `Muro.Ast.book_to_db/1` refuses a name that is already declared. The error names it.

### Manual

- `examples/bad_dup.muro`, in `examples.md`. Terms: the book has one set of names.

### Package

- Version 0.16.5.

## 0.16.4

A constructor field is strictly positive only when a stuck `match` is looked through. `Bad → Empty` under `match n` on a bound `Nat` was accepted, and that acceptance is a proof of `Empty`. Agda's `absentGo` already walked every subterm of a match, a rewrite, and a tensor operation. The Elixir check now does the same. A `match` on a concrete numeral still reduces before that walk.

### Checker

- `Muro.Check`. `absent_go?` walks `match` on `Nat`, on a data type, on `Empty`, and on `Unit`, and walks `rewrite`, tensor operations, and `~`.

### Manual

- `examples/bad_stuck.muro`, in `examples.md`.

### Package

- Version 0.16.4.

## 0.16.3

A mutual block is one descent. `ping` descending on its first argument and `pong` on its second was accepted, and that acceptance is a proof of `{suc 0 ≡ 0 : Nat}`, then of `Empty`. The block is refused unless one shared argument works for every member. `even` and `odd` still share their `Nat`. Agda `pickPos` had the same fallback; both checkers refuse the block.

### Checker

- `Muro.Check` and `agda/Muro/Check.agda`. When no shared index works for a block of two or more, a member that would pass on its own index is still an error.

### Manual

- `examples/bad_shared.muro`, in `examples.md`. `examples/even_odd.muro` is the mutual recursion that checks.

### Package

- Version 0.16.3.

## 0.16.2

`Pi` and `lam` are keywords only at a word boundary. `Pickle` and `lambda` are names. `Pi (x : Nat) → Nat` and `lam (x : Nat) → x` still parse as a pi and a lambda.

### Parser

- `Π` / `Pi` and `λ` / `lam` go through the same word boundary as the other keywords. `eat_kw` refuses a match when the next character continues an identifier.

### Package

- Version 0.16.2.

## 0.16.1

A `match` on a constructor with two or more fields now reduces correctly. The checker substituted the fields one at a time without weakening the ones already in place, so every field after the first landed one variable too low, on whichever binder came next in scope. `drop1 (cons y ys)` reduced to `zs`: the true `{drop1 (cons y ys) ≡ ys}` was refused and the false `{drop1 (cons y ys) ≡ zs}` checked. Agda was right; the Elixir mirror had drifted from it.

### Checker

- `Muro.Subst.inst_n/2` substitutes all the fields at once, as Agda's `appsFrom b args` does once β-reduced.

### Manual

- `examples/second_field.muro` and `examples/bad_second_field.muro`, in `examples.md`.

### Package

- Version 0.16.1.

## 0.16.0

A constructor field is strictly positive after unfolding. A spec name is the type it unfolds to, so `Contra := Bad → Empty` does not hide a negative field, and a harmless alias of `Nat` stays positive. `D` inside an argument of `D` is refused. Run and evidence definitions that reach each other are one block and descend on one shared argument, so `even`/`odd` check and a cycle of `Empty` does not. A `match` branch binds as many variables as the constructor has fields. `uncons` of an `Always` proof or a `~` proof is the unfold step: the head fact and the same predicate at the tails.

### Checker

- `Muro.Check` and `agda/Muro/Check.agda`. Positivity unfolds, then requires the data type absent, at the head of a spine whose arguments do not contain it, or only to the right of a `Π` whose domain does not contain it.
- A recursive block is the strongly connected component of run and evidence definitions. Productivity treats a call to any member as a self-call. Spec is not in the block.
- A branch whose binder count differs from the constructor telescope is an error. An out-of-range de Bruijn index is `unbound variable`.
- `uncons` uses the same step as `unfold`, for a bare `ν` and for an applied family.

### Manual

- `data.md`, `streams.md`, `limits.md`, `examples.md`.
- `examples/even_odd.muro`. `examples/always.muro` and `examples/bisim.muro` project a proof by `uncons`.
- `examples/cycle_empty.muro`, `examples/bad_positive.muro`, `examples/bad_alias.muro`, and `examples/bad_cons.muro` are the programs `mix muro.check` refuses.

### Package

- Version 0.16.0.

## 0.15.0

`--backend c` emits a `run` stream. `unfold` is a struct holding the seed, an environment for values the step closes over, and a function pointer for the step. `uncons` calls the step and returns the head together with a new struct for the tail; the original seed stays in place. Elixir emit is still `Stream.unfold`. `I64`, `F32`, and `Tensor` stay `c:machine`. A lambda that is not an unfold step stays `c:lambda`. `Always` and `~` stay omitted.

### Elixir

- `Muro.Emit.C`.

### Manual

- `emit.md`.

### Package

- Version 0.15.0.

## 0.14.0

A proof of `σ ~ τ` keeps that type in a product, a function argument, a constructor field, and a spec alias. Conversion compares both stream indices. The unfold step still takes its head goal from the indexed family, and the tail obligation stays `tail σ ~ tail τ`. Forming `~` checks that family, including in a binder domain, so a relation on `Stream F32` is refused. A recursive call wrapped in `rewrite`, `match`, or an annotation counts as an unfold head.

### Checker

- `Muro.Check`. `~` stays `{:bisim}` in every type position. The head-occurrence walk covers `rewrite`, annotation, `match`, and identity, as in Agda.

### Package

- Version 0.14.0.

## 0.13.0

`Always P s` unfolds to `P (head s) × Always P (tail s)`, and `σ ~ τ` unfolds to `{head σ ≡ head τ} × (tail σ ~ tail τ)`. The binder is the predicate at a stream, and the recursive component of `unfold` is checked at that predicate on the tails. `tt` no longer proves `Always` of `IsZero` at `natsFrom 0`, nor `natsFrom 0 ~ zeros`. Stream is unchanged: a bare `ν` still substitutes the seed for the binder.

### Checker

- `Muro.Check` and `agda/Muro/Check.agda`. An evidence self-call in that unfold step is the coinductive step.
- `examples/always.muro`, `examples/bisim.muro`.

### Manual

- `streams.md`, `examples.md`.

### Package

- Version 0.13.0.

## 0.12.0

`mix muro.emit` writes the `run` definitions of a file. The default backend is Elixir, the same text as `Muro.emit_file/3`. `--backend c` writes `<name>.h` and `<name>.c` next to the file. C is a closed book of `Nat`, `Unit`, and user data (`match` is a `switch`, erased arguments are dropped, `run internal` is `static`). A run that mentions `Stream` or `I64` / `F32` / `Tensor` is refused (`c:stream`, `c:machine`) and still emits on the Elixir backend. There is no new tag.

### Elixir

- `Muro.Emit.C`. `Muro.Emit.run_defs/1` is the shared run filter. `Muro.emit_c/2`.
- `mix muro.emit FILE [--backend elixir|c]`.

### Manual

- `emit.md`, README.

### Package

- Version 0.12.0.

## 0.11.0

`mix muro.check` puts a small book behind the file: `pred`, `plus`, `inj-suc`, `plus_suc`, `sym`, `cong`. They are ordinary definitions, checked by the same checker. A name the file defines replaces the prelude's, and so does any prelude definition that refers to a replaced name, so `plus_suc` is not a lemma about a different `plus`. A prelude `run` is emitted as `defp` only when a `run` term in the file calls it. `check_sig` on a book passed in directly is unchanged. The Agda kernel has no prelude.

### Elixir

- `lib/muro/prelude.muro`, `Muro.Prelude`. `Muro.check_file/2` and `Muro.emit_file/3` use it.
- `examples/using_prelude.muro`.

### Manual

- `language.md`, `emit.md`, `for-agents.md`, `examples.md`, README.

### Package

- Version 0.11.0.

## 0.10.0

A book is checked one definition at a time, concurrently, and every failure comes back. `check_sig` used to stop at the first error. Each definition was already checked against the whole book with its own fuel, and `checkSig-sound` is the conjunction of those results, so running them with `Task.async_stream` is the same function. The Agda checker is unchanged: it still stops at the first `fail`.

### Elixir

- `Muro.Check.check_sig/2` checks each definition on its own process (`ordered: true`, `timeout: :infinity`). `{:error, msg}` joins the failures in book order with a blank line. Fuel remains the only bound.
- `mix muro.check` raises that combined message.

### Manual

- `for-agents.md`, README.

### Package

- Version 0.10.0.

## 0.9.0

The write / check / fix loop prints surface syntax. A conversion error says `Fin n`, not `#0`. A parse or check error starts with `line:col`. `?` is an unsolved goal: it always fails, with the expected type and the binders in scope. It is not a metavariable and it never inhabits, so it is not in ⊢ and not in the Agda kernel.

### Language

- `?` is an atom. The checker refuses it in every mode, infer or check, with `unsolved hole`, `expected: …`, and `context:`. Fill it; a book that still has a hole does not check.
- Binder names on Π and λ are kept on the de Bruijn form so printed types use the names the program wrote.
- Parse errors and definition errors are prefixed `line:col:`. A definition error names the definition and the part (`type`, `body`, `productivity`, or a constructor).

### Elixir

- `Muro.Print`: surface printer, `offset_to_loc/2`, `hole_message/4`.
- `Muro.Parser`: source is kept for the duration of a parse; `def` / `data` carry `:loc`; `?` is `{:hole, loc}`.
- `Muro.Check`: RecSt carries binder names; conversion and views print with them; holes never succeed.
- `Muro.Emit` refuses a hole.

### Manual

- `language.md` (holes), `grammar.md`, `limits.md`, `for-agents.md`, `start.md`, `index.md`.

### Package

- Version 0.9.0.

## 0.8.0

Preservation holds in every mode. The one premise that was not monotone in the mode, the equation of a `rewrite`, now is: it is checked in evidence inside a run or evidence term and in spec inside a spec term (`rwtMode`). A type may therefore rewrite along an erased equation; a run or evidence body still needs evidence.

### Language

- `rewrite eq motive P in t` inside a spec term (a type, an erased argument) checks `eq` in spec. `Π (-e : {n ≡ m : Nat}) → Vec A (rewrite e motive (λ _ → Nat) in m)` is well-formed; before, an erased variable in the equation was refused in every mode. In run and evidence terms nothing changes.

### Kernel (Agda)

- `Muro.Env`: `rwtMode` (`spec ↦ spec`, otherwise `evid`), `≤ᵐ-rwtMode`, `rwtMode-mono`.
- `Muro.Judgement` `⇒-rwt`, `Muro.Typing` `t-rwt`: the equation at `rwtMode m`.
- `Muro.Typing`: the substitution lemmas (`⊨-sub`, `wf-sub`, `▹-sub`, `ca-sub`, `brs-sub`, `mot-sub`, `⊨-inst`) no longer require the substituted terms' mode to be at most evidence; `pres` / `pres*` no longer require the derivation's mode to be at most evidence. `Muro.Consistency` follows.
- `Muro.Check` `infer′` on `rwt`, `Muro.Soundness` `infer-sound`: the equation at `rwtMode m`. `--safe`, no postulates.

### Elixir mirror

- `Muro.Check`: `rwt_mode/1`; the `{:rwt, …}` clause of `infer` uses it. A test for the accepted spec form and the refused run form.

### Manual

- `identity.md` (the mode of the equation), `limits.md`, `extending.md` (positions are monotone in the mode).

### Package

- Version 0.8.0.

## 0.7.0

`match` on an indexed data type is in ⊢, with preservation and checker soundness. A branch is typed at its constructor's own indices: the checker no longer substitutes a scrutinee index for a constructor argument in the branch (no forcing). A constructor whose numeral index clashes with the scrutinee's (`0` against `suc(…)`, under any number of matching `suc`) is skipped, as before. What a branch needs to know about the scrutinee's indices it states in the motive as an equation and uses with `rewrite`; `examples/vec.muro` does this for `lookup`, with `inj-suc` as the evidence that `suc` is injective.

### Language

- `match e motive P | c₁ … | cₙ …` on `D params indices` has type `P indices e`. The branch for `c` binds every argument of `c` and is checked against `P` at `c`'s target indices and `c` applied to its arguments. Before, a constructor-argument variable that appeared as a target index was replaced in the branch by the scrutinee's index; a program that relied on that now carries the equation in the motive (see `manual/indexed.md`). The `vnil` branch of `lookup` is still skipped as a clash.
- `examples/vec.muro`: `pred`, `inj-suc : Π (-m : Nat) → Π (-p : Nat) → {suc(m) ≡ suc(p) : Nat} → {m ≡ p : Nat}`, and `lookup` with the index equation in the inner motives.

### Kernel (Agda)

- `Muro.Subst`: `motApp P is e` (the motive at the indices and the scrutinee), `motiveTail` (the motive's kind after its first index).
- `Muro.Data`: `BrTy σ i j np T P acc X` ends at `motApp P (drop np qs) (ctor i j acc)` for a constructor telescope ending in `dty i qs`; `Clash σ np is T` (a target index is a numeral that differs from the scrutinee's); renaming, substitution, and `≈` lemmas for both; `≈L-++-split`, `drop-++`.
- `Muro.Convert`: `≈-su-inj`, `≈-su-ze`.
- `Muro.Judgement`: `⇒-mData` takes the scrutinee's type as `dty di (ps ++ is)` with `length is ≡ nidxs d`, `MotiveOk` (the motive is well-formed over the scrutinee when there are no indices, and checks against `motiveTail` otherwise), branches `brs⟨ di , ps , is , P , ci ⟩` with `brs-∷` and `brs-skip` (a `Clash`); the type is `motApp P is e`.
- `Muro.Typing`: `t-mData`, `Mot⊨`, `b-skip`; renaming and substitution of motives and branches; preservation for ι on an indexed `match` (`brApp`, `Clash-▹`: a skipped constructor cannot be the scrutinee's head). `Muro.Wall`, `Muro.Consistency` follow.
- `Muro.Check`: `forceBr`, `analyzeForces`, `forcePairs`, `matchIdx` removed. `clashes` / `clashIdx` (the clash test, `NatView`), `checkBr` / `checkBrPi` bind one λ per Π, `checkMotive` and `firstMotLam` take the data type's index telescope. Fuel is spent only in `whnf`, `conv`, `isData`, `clashIdx`.
- `Muro.Soundness.Views`: `GoodSig` covers indexed data types (`tel` at `nparams d + nidxs d`); `clashIdx-sound`, `clashIdxs-sound`, `clashes-sound`, `motApp-β`, `Frag-motiveTail`, `firstMotLam-form`. `Muro.Soundness`: `checkMotive-sound`; `checkBr-sound`, `checkBrPi-sound`, `checkBranches-sound` over indexed data, with the skipped branch as `brs-skip`. Statements otherwise unchanged; `--safe`, no postulates.
- `Muro.ExampleVec`: `pred`, `suc-inj`, `lookup` with the index equation in the inner motives; `lookup-ok` still checks.

### Elixir mirror

- `Muro.Check`: `force_br`, `analyze_forces`, `walk_forces`, `match_idx`, `forces_for` removed; `clashes` / `clash_idxs` / `clash_idx` mirror `Check.clashes`; `check_br` / `check_br_n` without a force list.

### Manual

- `indexed.md` rewritten around the motive equation and `rewrite`; `limits.md`, `extending.md`, `examples.md`, `for-agents.md`, README.

### Package

- Version 0.7.0.

## 0.6.0

The kernel has one pair eliminator. `fst` and `snd` are no longer constructors of the term language: `fst t` parses to `let (a, b) = t in a` and `snd t` to `let (a, b) = t in b`, so `head` and `tail` are a `let` on `uncons` too. To keep them usable wherever they were, `let` is now also inferred: `⇒-letp` infers the body under the two binders and requires its type not to mention the components. Every use of pairs is now inside the proved fragment.

### Language

- `let (a, b) = e in t` is inferred as well as checked. The body's type is strengthened past the two binders; `let (x, y) = p in mkFin x`, whose type `Fin suc(x)` mentions `x`, is refused in inference position with `let: the body's type mentions a component of the pair` (it still checks against an expected type).
- `fst`, `snd`, `head`, `tail` are surface sugar for `let`. Same programs check; `head (tail s)` and `tail s ~ t` go through the inferred `let`.
- Parser: an application stops before `ident :` only at the start of a line (the next constructor of a `data` block). `{0 ≡ f x : Nat}` now parses; before, `f x` was cut at `x :`.

### Kernel (Agda)

- `Muro.Syntax`: `fst`, `snd` removed, with their clauses in every module (`Tag`, `Subst`, `SubstLemmas`, `Unembed`, `Spine`, `Reduction`, `Convert`, `Check`, `Consistency`, `Soundness/*`). `Subst.fstTm` / `sndTm` build the `let` forms; `always` and `bisim` use them.
- `Muro.Subst`: `renM` (partial renaming), `strengthen₂ = renM unwk₂`. `Muro.SubstLemmas`: `renM-sound`, `strengthen₂-sound : strengthen₂ T ≡ ok C → T ≡ wk (wk C)`.
- `Muro.Judgement`: `⇒-letp`. `Muro.Typing`: `forget-⇒` case. `Muro.Wall`: `spec-⇒-uses` case. `Muro.Consistency`: `ne-untyped-⇒`, `progress-⇒` cases.
- `Muro.Frag`: `Frag-unren` (the fragment is closed under un-renaming). `Muro.Soundness`: `infer-sound` for `letp` through `strengthen₂-sound`; `checkTy-sound` on a `let` goes through `infer`. Statements unchanged; `--safe`, no postulates.
- `Muro.Check`: `infer′` has the `letp` clause; `whnf`, `synEqD`, `convND`, `hasSelf`, `occurs`, `occursD` lose the projection clauses.

### Elixir mirror

- `{:fst, _}` / `{:snd, _}` removed from `Muro.Ast`, `Muro.Subst`, `Muro.Check`, `Muro.Emit`. Parser desugars `fst`, `snd`, `head`, `tail`; `Always` and `~` build the `let` form. `Muro.Subst.strengthen2/1`. `Muro.Check`: `infer` clause for `{:letp, e, t}`.
- `examples/result.muro`: a failing `run` function returns `Result E A`; `ok` / `error` emit as `{:ok, _}` / `{:error, _}` because constructor names are the tags. Tests for it, for `fst` as `let`, for `head (tail s)`, and for the parser change.

### Manual

- `language.md` (Products), `grammar.md` (layout note), `streams.md`, `emit.md` (Failing functions), `limits.md`, `extending.md`, `examples.md`.

### Package

- Version 0.6.0.

## 0.5.0

A language addition: `let (a, b) = e in t` opens a pair. It is the eliminator an affine pair was missing. `fst p` and `snd p` each use `p`, so a pair-typed variable could never have both components used; `let` uses it once and binds both components, each affine.

### Language

- `let (a, b) = e in t`. `e` is inferred and must have type `A × B`; `t` is checked against the expected type with `a : A` and `b : B` in scope, both affine. `let (a, b) = (u, v) in t` reduces to `t[a := u, b := v]`. `let` only checks: at the head of an application it is refused with `let needs an expected type`.
- `fst` and `snd` are unchanged.

### Kernel (Agda)

- `Muro.Syntax`: `letp e t`, `t` under two binders (`a` at 1, `b` at 0); `Muro.Subst.inst₂`; renaming and substitution lemmas.
- `Muro.Reduction` / `Muro.Convert`: `ι-letp`, the `letp` congruence, `dev` / `tri` cases (confluence), `prod` and `pair` are rigid heads with shapes; `≈-prod-inj`.
- `Muro.Judgement`: `⇒-prod` (spec), `⇒-pair`, `⇐-pair`, `⇐-letp`. `Muro.Typing`: `t-prod`, `t-pair`, `t-letp`; preservation for `ι-letp`. `Muro.Wall`, `Muro.Consistency`: pairs are introduction forms; progress for `let`.
- `Muro.Frag`: `prod`, `pair`, `letp` join the fragment. `fst` and `snd` stay outside it.
- `Muro.Check`: `whnf` steps `ι-letp`; `check′` has the `letp` clause; `infer′` refuses it.
- `Muro.Soundness` (with `Conv`, `Views`): `viewProd-sound`; `infer-sound` / `check-sound` cases for `prod`, `pair`, `letp`. Statements unchanged; still `--safe`, no postulates.

### Elixir mirror

- `Muro.Ast`: named `{:letp, e, a, b, t}`, de Bruijn `{:letp, e, t}`. `Muro.Subst.inst2/3`. Lexer keyword `let`. Parser: `let ( a , b ) = e in t`. `Muro.Check`: `whnf`, conversion, occurrence checks, `check` clause, `infer` refusal. `Muro.Emit`: `({a, b} = e; t)`.
- `examples/pair.muro`; tests for the accepted and refused forms.

### Manual

- `language.md` (Products), `grammar.md`, `emit.md`, `limits.md`, `extending.md`, `examples.md`.

### Package

- Version 0.5.0.

## 0.4.2

A kernel fix to the descent check, and its redesign. A definition in `run` or `evidence` now descends on one argument position, the same at every self-call, and the checker finds that position; a self-reference must be applied. Two more ways to write a non-terminating `run` or `evidence` definition are closed, and the "first non-erased argument" rule is gone.

### Checker (`Muro.Check`)

- A self-call must pass a smaller variable *at the position of the argument it descends on*. Before, a smaller variable at any non-erased position counted, so `f (suc xp) y = f (suc (suc y)) xp` was accepted and diverges; with the `Type`-valued motive of 0.4.1 it gave an `evidence Empty`.
- The definition being checked may not occur unapplied in `run` or `evidence` (`loop n = apply loop n` was accepted; `apply` may apply it to anything). Error: `recursive definition must be applied to its arguments`. Spec is unchanged.
- The descent position is no longer fixed to the first non-erased argument. `checkBody` checks the body descending on the first non-erased position and, if that fails, on each later one; a definition with no self-call passes at once; when every attempt fails the first attempt's error is reported (the position only affects the descent check). `lookup` in `vec.muro` checks with or without its length erased.
- `RecSt` is `self`, `pos`, `nextArg`, `smaller`, `recOk`. `nextOk`/`keepNext` are replaced by `lamRec` (every leading λ, erased or not, is a position); the never-set `guarded` field is removed. `infer′` takes a Bool, "this term is the head of an application spine", passed to `checkRec` and `selfApplied`: the app case infers its head with it set, and the descent check runs only when it is not (once, on the maximal spine); the def case refuses an unapplied self-reference only when it is not. `infer` is `infer′ … false`. `checkRec` no longer needs the signature or the fuel.
- Elixir mirror: `infer/7` with `head?`, `check_rec/4`, `self_applied/4`, `arg_positions/2`, `lam_rec/1`, `infer_def/5`, `check_body/3`, `def_rec/2`.
- `Muro.Soundness`: `infer-sound` is stated for `infer′ … hd`, for every `hd`; `checkBody-sound` (whichever position succeeds, the body was checked with some recursion state); `brRec` follows `extRec`. Statements otherwise unchanged.
- Tests: the two counterexamples are refused; descent on a second argument and `lookup` with its length kept are accepted; a spec definition may still refer to itself unapplied.

### Manual

- `language.md` (Recursion and descent) rewritten for the one-position rule and the three things that are not descent; `data.md`, `indexed.md`, `start.md`, `extending.md` follow.

### Package

- Version 0.4.2.

## 0.4.1

A kernel fix. `match` on a `data` type marked every field of type `D …` as smaller, whatever the scrutinee was, so a self-call could descend on a field of a computed value (`match (f x) …`) or of a λ-bound variable that is not an argument. That accepted non-terminating `run` and `evidence` definitions, including an `evidence Empty`. `match` on `Nat` already required the scrutinee to be an argument or a smaller variable (`scrutOk`); `match` on a `data` type now does the same.

### Checker (`Muro.Check`)

- `checkBranches`, `checkBr`, `checkBrPi`, `forceBr` take the scrutinee flag `scrutOk rs e`; a field is smaller only if the flag holds and its type is `D …`. Elixir mirror: `check_branches`, `check_br`, `check_br_n`, `force_br` take `sm = scrut_ok(rs, e)`.
- `Muro.Soundness`: `brRec`, `checkBr-sound`, `checkBrPi-sound`, `checkBranches-sound` carry the flag; the statements are otherwise unchanged (⊢ has no descent rule).
- Test: a `boom`/`absurd` pair on a computed scrutinee and a λ-bound scrutinee are refused with `recursive call does not descend on a smaller argument`.

### Examples and manual

- `examples/vec.muro`, `agda/Muro/ExampleVec.agda`, `manual/indexed.md`: `lookup` erases its length `n` (`Π (-n : Nat)`), so `i : Fin n` is the argument recursion descends on and `j` from `fsuc m j` is smaller. Emitted `lookup/2` no longer takes the length.
- `manual/language.md`, `manual/data.md`: the scrutinee of the `match` that exposes a smaller variable must be the argument being descended on or a smaller variable.

### Package

- Version 0.4.1.

## 0.4.0

The checker is total and the soundness proof is `--safe`. `Muro.Check` carries no `TERMINATING` pragma: it is structurally recursive on the term, and fuel is spent only where a term is reduced. Running out of fuel is an error, never an unreduced term. All shipped examples check as before.

### Checker (`Muro.Check`, `mix muro.check`)

- Out of fuel is reported. `whnf` returns a `Result`; at fuel zero it fails with `out of fuel (the checker gave up reducing; raise the fuel)` instead of returning the term unreduced, so a term that needs more fuel is refused with that message rather than with a misleading type error (before: `cannot convert …`, `expected Π, got …`). Everything that reduces (`conv`, `isData`, the Π / identity / data / product / ν views, `instParams`, index matching, `checkUnfold`, `addT`) propagates it.
- `mix muro.check --fuel N path.muro` sets the fuel (default `2000`). `Muro.Check.check_sig/2` and `Muro.check_file/2` take `fuel: n`; `Muro.Check.default_fuel/0` is the default. There is no resumption: raise the fuel and check again.
- Fuel is spent only where a term is reduced (`whnf`, `conv`, `isData`, `matchIdx`) and where a forced index argument is substituted into a `match` branch (`forceBr`). `infer`, `check`, `checkTy`, the constructor spine, and the branches of a `match` are structural on the term.
- A constructor application is checked from the head of the spine (`inferCtorSpine`: the constructor's type at the parameters, then one Π per argument, an erased field in spec), then the residual telescope must be the expected type (`checkCtorApp`). Error texts: `constructor of another data type`, `not a constructor spine`, `too many constructor arguments`, `too few constructor arguments`.
- A run type is read syntactically after one `whnf` (`runTy`); under ν the body is read as it is, the bound variable counting as a run type (same answer as substituting `Unit`, without the substitution).
- An index clash in `match` is a value (`nothing` / `{:ok, :clash}`), not an error message that is matched by text.

### Agda (`agda/Muro`)

- `Muro.Check` is `--safe`. `whnf`, `dataWhnf`, `isData`, `isRunType`, `conv`, the views, `instParams`, `matchIdx`, `analyzeForces` return `Result`. `runTy` is structural. `checkBr` splits into `checkBr` (reduce the telescope) / `checkBrPi` (one λ against one Π) / `forceBr` (a forced argument, one unit of fuel). `checkLam`, `inferConv`, `inferArg` are named so that the case tree splits on the term.
- `Muro.Soundness` is `--safe` and split: `Muro.Soundness.Conv` (`whnf-sound`: when `whnf k σ t ≡ ok u` then `t ⟶* u` in spec and `u` is in the fragment; `synEq-sound`; `conv-sound`), `Muro.Soundness.Views` (`viewPi-sound`, `viewId-sound`, `viewData-sound`, `isData-sound`, `Tel`, `GoodSig`, `instParams-sound`, `analyzeForces-tel`), `Muro.Soundness` (`infer-sound`, `check-sound`, `checkTy-sound`, `checkAgainst-sound`, `inferConv-sound`, `inferCtorSpine-sound`, `checkCtorApp-sound`, `checkBr-sound`, `checkBrPi-sound`, `checkBranches-sound`, `checkDef-sound`, `checkSig-sound`). The proof is by structural recursion on the fragment witness `Frag e`; the depth-indexed copy `FragD` is gone. Statements are the same as in 0.3.0.
- `Muro.Judgement`: the list judgment `T ▹ as ⇝ R ⊣ u` is built from the head outwards (`args-[]`, `args-snoc`), as `Check.inferCtorSpine` walks a spine; `⇐-ctor` is unchanged. `Muro.Wall.spec-args-uses` and `Muro.Typing.forget-args` follow. `Muro.Spine.lamView` is removed.
- `Makefile`: `agda-safe` also checks `Muro.Check` and `Muro.Soundness`; `agda-soundness` and `agda-check` pass `--safe`. `agda/Muro.agda` imports the two new modules.

### Manual

- `limits.md`: what fuel bounds, what running out means, that removing the cap waits on normalisation; the soundness modules are `--safe`. `extending.md`, `for-agents.md`, `identity.md`, `index.md`, README: the module list, the fuel discipline for kernel changes, `inferCtorSpine`, `▹` from the head.

### Package

- Version 0.4.0.

## 0.3.0

The checker changes. Each change makes `Muro.Check` agree with ⊢ where they disagreed; the disagreements were found by proving the checker sound. All shipped examples check as before.

### Checker (`Muro.Check`, `mix muro.check`)

- A type is recognised by its shape. `checkTy` no longer reduces first: `Type` and `Π (x : A) → K` are kinds as written, anything else must infer a type convertible to `Type`. Refused now, accepted before: a term that merely reduces to `Type` or to a kind used as a type, such as `(λ (x : Nat) → Type) 0`. Error text: `Type has no type`.
- Arguments at a call site of an evidence definition are checked in the mode of the application. Inside an evidence term, `lem a` with `lem` an evidence definition checks `a` in `evidence` (before: in `spec`) and then discards its uses, so instantiating a theorem still consumes nothing. Refused now, accepted before: passing a spec variable to a theorem from an evidence term (`no promotion`).
- `isData` is fuelled, like every other loop over `whnf`: a recursive spec definition (`X : Type := D X`) at a `+` binder now fails with `+ requires a Data type` instead of not returning.

### Agda (`agda/Muro`)

- `Muro.Soundness`: the executable checker is sound for ⊢ on the fragment. Over a `GoodSig` (a fragment signature whose data types are non-indexed and whose constructor types are telescopes ending in the data type) and a fragment context, `infer k σ rs Γ m e ≡ ok (A , u)` gives `σ , Γ ⊢[ m ] e ⇒ A′ ⊣ u` with `A′ ≈ A` (`infer-sound`), `check … ≡ ok u` gives `⊢[ m ] e ⇐ A ⊣ u` (`check-sound`), `checkTy … ≡ ok tt` gives `⊢ A wf` (`checkTy-sound`); `checkDef-sound` and `checkSig-sound` are the corollaries for definitions and whole signatures. On the way: `whnf-sound` (`Check.whnf` is `⟶*` in spec and preserves the fragment), `synEq-sound`, `conv-sound` (`Check.conv` says yes → `≈`), `isData-sound`, `instParams-sound`, the spine views, and the `match` path (`checkBr-sound`, `checkBranches-sound`). The proof is by structural recursion on a depth-indexed fragment predicate (`FragD`). One direction only, for every fuel; the module imports `Muro.Check` and is therefore not `--safe`.
- `Muro.Frag` (the ⊢ fragment as a predicate on terms, lists, signatures, and contexts, closed under renaming and substitution) and `Muro.Tag` (constructor tags) are new and `--safe`. `Muro.Spine` gains the spine views `Check` uses (`ctorSpine`, `dtyArgs`, `defArgs`, `lamView`) with their characterisations.
- ⊢ reads types through `≈` wherever `Check` reads them through `whnf`: `type-el` (a type is a spec term whose sort is convertible to `Type`), `⇐-lam` and `⇐-refl` (the expected type is convertible to a Π / an identity type), `⇐-ctor` (constructor spine as a `Spine`, arguments along the instantiated telescope by the list judgment `T ▹ as ⇝ R`, replacing `ctor⟨ di , ps ⟩⇝`). `⇐-≈`: ⇐ is closed under conversion of the type. `⇒-app-aff` / `⇒-app-reuse` take their uses from `Env.appUses`.
- `Muro.Check`: `synEq` and `convN` compare constructor tags before structure; `defArgs`, `dtyArgs`, `ctorSpine`, `lamView` are the `Muro.Spine` views; `forcePairs`, `checkAgainst`, `checkTy` are in the form the proof follows; `infer′` takes the term before the mode (so that Agda's case tree splits on the term first). Behaviour unchanged except as listed under Checker.
- `Makefile`: `agda-safe` also checks `Muro.Frag` and `Muro.Tag`; new target `agda-soundness`.

### Manual

- `wall.md`, `identity.md`: the argument at an evidence call site is checked in evidence, its uses discarded. `limits.md`, `extending.md`, `for-agents.md`, README: what `Muro.Soundness` proves and does not, the new modules, and the three checker clauses the proof corrected.

### Package

- Version 0.3.0. `agda/Muro.agda` re-exports `Muro.Frag`, `Muro.Tag`, `Muro.Soundness`.

## 0.2.2

No checker change. Every book that checked under 0.2.1 checks under 0.2.2 with the same result. Agda and manual only.

### Agda (`agda/Muro`)

- `data` is in ⊢. `Muro.Judgement` has `⇒-dty` (a data former is a spec term of its declared kind), `⇐-ctor` (a constructor application checked against a `dty` type: parameters from the type, arguments along the instantiated telescope, an erased field in spec, as `Check.checkCtorApp`), and `⇒-mData` (`match` on a non-indexed data type: the motive at the scrutinee, one branch per constructor in declaration order, each of the type `BrTy` gives, as `Check.checkBranches`). Two auxiliary judgments carry the spine (`ctor⟨ di , ps ⟩⇝`) and the branches (`brs⟨ … ⟩`). `Muro.Env` gains `fieldMode` and `combineArg` (the mode and the uses of a constructor argument).
- Preservation covers ι for `match`. `Muro.Typing` types a constructor spine as one rule (`t-ctor`, with `ctor-inv` its inversion), `match` by `t-mData`, and proves `pres` for `ι-data`: the branch for the constructor applied to the constructor's arguments has the motive at the scrutinee (`brApp`). The proof needs nothing of the data declarations beyond what the derivations carry. Mode weakening, renaming, substitution, and `forget-⇐` extend to the new rules.
- Reduction knows `match`. `Muro.Reduction` has `⇛-ιdata` and the complete development of `mData` on a constructor spine; confluence is re-proved with it. `Muro.Convert` has `ι-data` and `mData-e` in `⟶` (exactly `Check.dataWhnf`), constructor and `dty` spines as normal forms, `≈L` on argument lists, `≈-dty-inj`, and the separation of constructor spines from `dty` spines and rigid heads.
- `Muro.Spine` (application spines as a relation, unique for rigid heads) and `Muro.Data` (`IsData`, `ReuseOk`, `InstParams`, `BrTy`, each closed under renaming, substitution, and conversion) are new. `IsData` is σ-relative and covers `dty` spines whose parameters are Data, as `Check.isData`; `reuse` binders and applications use it in ⊢ and ⊨.
- `Muro.Wall`: `no-run-dty` / `no-evid-dty`; spec derivations still carry zero uses through the new rules.
- `Muro.Consistency`: `σ-empty` declares no data type, so constructor and `dty` spines are untyped in it; `Empty-nf`, progress, and `Empty-nf⊨` cover the new normal forms. `Empty-evid-from` is unchanged: normalisation of closed evidence remains the one hypothesis.
- Still outside ⊢: `match` on an indexed data type (forced indices), ν, Tensor. ⊢ does not check `data` declarations (`Check.checkData`: positivity, small fields).

### Manual

- `extending.md`, `limits.md`, `for-agents.md`, README: the fragment now includes `data`; the new modules and what a rule whose subject is a variable costs.

### Package

- Version 0.2.2. `agda/Muro.agda` re-exports `Muro.Spine` and `Muro.Data`.

## 0.2.1

No checker change. Every book that checked under 0.2.0 checks under 0.2.1 with the same result. Agda and manual only.

### Agda (`agda/Muro`)

- Preservation is a theorem. `Muro.Typing` defines the declarative judgment `⊨` (⊢ without uses, conversion at the root of every rule) and proves: ⊢ is sound for `⊨` (`forget-⇐`), mode weakening along run ≤ evid ≤ spec, renaming, substitution (`⊨-sub`, `⊨-inst`), and `pres`: a `⟶` step, taken in any mode, keeps the type of a run- or evidence-mode derivation over a signature whose bodies have their declared types. `Muro.Consistency.Empty-evid-from` now takes only `Normalising`; `preservation` is the specialised corollary at `σ-empty`.
- Conversion is congruent. `Muro.Reduction` defines parallel reduction `⇛` (δ, β, ι, `ann`, congruent under every constructor of `Tm`), closed under substitution, confluent by complete developments (triangle property). `≈` in `Muro.Convert` is the equivalence generated by `⇛`, so it is closed under substitution and joinability comes from confluence, not from determinism of a strategy. Inversion is by rigid head (`≈-shape`) and Π / ≡ are injective up to `≈`. `Muro.SubstLemmas` holds the renaming / substitution algebra.
- `⟶` is exactly the `Check.whnf` strategy: the congruences in an application argument and under `suc` are gone (they served only the old `≈-nf` inversion).
- ⊢ takes conversion in spec mode, so every def unfolds during conversion, as `Check.whnf` does. Before, ⊢ could not check an evidence term whose type mentions a spec def although `Check` accepts it.
- `Muro.Env`: the mode order `≤ᵐ` (run ≤ evid ≤ spec) with `allowedDef` monotone.
- Recorded, not changed: the equation of a `rewrite` is checked in evidence whatever the surrounding mode is, so positions are not monotone in the mode inside spec terms and preservation is not claimed for spec derivations.

### Manual

- `extending.md`: the new modules, what each step of the order must add to them, and the two mode facts the metatheory depends on.
- `limits.md`, `for-agents.md`, README: what is proved now.

### Package

- Version 0.2.1. `agda/Muro.agda` re-exports the new modules.

## 0.2.0

The checker changes. A book that checked under 0.1.0 still checks unless it used a kind as a small type; all shipped examples are unchanged.

### Checker (`Muro.Check`, `mix muro.check`)

- Kinds are not small types. `Type` and `Π (x : A) → K` with `K` a kind are well-formed and may be the type of a `def`, a binder domain, a motive, or the sort of an identity type, but they are not terms of type `Type`. Refused now, accepted before: `Π (_ : Unit) → Type` where a term of type `Type` is expected, `Type × A`, and a `data` constructor field of type `Type` (parameters `(A : Type)` are exempt). Each of these made `Type` a retract of a small type, and with β or a `Type` motive that is Girard's paradox in `spec`. The premises that moved from well-formed to `: Type`: the codomain of `Π`, both components of `×`, the body of `ν` (kernel only; the surface ν is `Stream`), and constructor fields.
- Error text for these cases is `Type has no type (no Type : Type)`, tagged with the def or constructor.

### Agda (`agda/Muro`)

- Conversion in ⊢ is a relation. `Muro.Convert` defines deterministic weak-head reduction `⟶` (δ, β, ι for `Nat` / `Unit` / `Empty` / `rewrite`, congruence under `suc`, in the function and argument of an application, and in eliminator scrutinees) and `≈` as its equivalence closure, without fuel. `⇐-conv`, `⇐-lam`, `⇐-refl`, and the `Π` / `≡` views of `Muro.Judgement` use `≈` instead of `_≡_`. `≈` does not reduce under `λ`, `Π`, identity types, motives, or branches. `≈-nf`: distinct normal forms are not convertible.
- `Muro.Judgement`: `wf` has `type-pi`; `⇒-pi` checks the codomain against `Type`. `⇒-var-run` and `⇒-var-evid` were mis-parenthesised (two premises instead of `(qtyOf Γ x ≡ erased → ⊥)`) and no run or evidence variable was derivable; fixed.
- `Muro.Consistency`: the `Empty-evid` postulate is deleted. Proved: introduction forms never check against `Empty`; no closed normal evidence term has type `Empty`; closed neutral terms are untyped in the empty context; closed well-typed evidence terms are normal or take a `⟶` step. `Empty-evid-from : Preservation → Normalising → … → ⊥` states what remains. `Empty-evid` itself is not proved.
- `make agda` checks `Muro.Judgement`, `Muro.Wall`, `Muro.Consistency`, and their imports under `--safe`, then the whole tree. `Muro.Env` (signature, context, uses) and `Muro.Unembed` (PHOAS to de Bruijn, `TERMINATING`) are split out of `Muro.Check` and `Muro.Subst` so the theorem modules have no `TERMINATING` dependency. There are no postulates in `agda/`.
- data, ν, and Tensor are still outside ⊢.

### Manual

- `language.md`: small types versus kinds; `Type` is impredicative by design.
- `limits.md`: the refused retracts; the `⇒-pi` bug is recorded as fixed.
- `data.md`: constructor fields are small.
- `extending.md`: `Muro.Judgement` / `Muro.Convert` are a step of the order; the premises that keep the sort consistent, including why `⇒-idt` keeps a kind as its sort.
- `for-agents.md`: file map covers every Agda module and marks which are not `--safe`.

### Package

- Version 0.2.0. `CHANGELOG.md` ships in the Hex package. README points at Hex.

## 0.1.0

First release on Hex, owned by the `murolang` organization. MIT.

- `Muro.Lexer` returns byte spans for a fragment. `Muro.MakeupLexer` maps those spans to Makeup tags.

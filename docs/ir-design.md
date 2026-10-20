# Backend-agnostic IR for Muro

**Author:** placeholder · **Date:** 2026-10-20 · **Status:** Accepted

## Overview

The IR sits between a checked book and every target emitter. `Muro.emit_file/3` (`emit_module/2`, `lib/muro/emit.ex`) and `Muro.emit_c/2` (`Emit.C.render/2`, `lib/muro/emit/c.ex`, via `lib/mix/tasks/muro.emit.ex`) walk that AST today. The image is closed `run` and `run internal`. C is first; Rust, one Cortex-M assembler, and an Elixir retarget follow. The proof chain ends at the IR.

PR #20 (merged 2026-10-02, ["0.12.0: emit closed run books to C"](https://github.com/murolang/muro/pull/20)) described Stream as refused. `emit/5` on `{:unf, seed, {:lam, ...}}` now emits seed, captures, and a step pointer; `{:ucons, _}` rebuilds the struct. `examples/zeros.muro` and `examples/nats.muro` compile with `cc -c` (`test/muro_emit_c_test.exs`). The code is the contract.

## Goals

A book `Muro.check_file/2` has accepted elaborates to this IR or to `c:lambda`, `c:machine`, `c:stream`, `c:erased`, or `c:unsupported`. A backend predicate such as a Cortex-M heap rejection applies to a well-formed term and leaves it well-formed.

Linearity (`%0` / `%1`) is Phase 3. Liveness, sessions, placement, and distribution come later. `I64`, `F32`, `Tensor`, and `addi` / `muli` / `addt` / `toi64` / `packi` stay on the Elixir walk (`Nx.add`, `examples/nx_add.muro`).

## Design

```mermaid
flowchart LR
  Book[Book] --> Check["Muro.check_file"]
  Check --> Elab[elaborate]
  Elab --> IR[IR book]
  IR --> Backend["backend text"]
```

`checked_book/2` (`Prelude.for_emit/1`) is the file plus called prelude runs at `export: false`. `run_defs/1` keeps `mode: :run` and drops `kind: :data`. `run internal` is `export: false` (`lib/muro/parser.ex`). `agda/Muro/Base.agda` has `Qty` (`affine`, `reuse`, `erased`) and `Mode` (`run`, `spec`, `evid`). `allowedDef` is in `agda/Muro/Env.agda`; the wall lemmas are in `agda/Muro/Wall.agda`. Erased λ-arguments drop. Motives, `rewrite`, `ann`, and `rwt` erase to the body. Affine and reuse are already discharged. `agda/Muro/Syntax.agda` holds `Tm` and `PTm`. IR constructors are not added to `Tm` or `PTm`. The IR keeps source names; `def_names/3` and `c_name/1` print them.

### Constructs

A constructor is included when `emit/5` lowers it saturated, or for the stream encoding.

`Var` is a use of a source name bound by `Fun`, `Let`, `LetPair`, `Match`, or the stream step (seed and captures). `Var` is not a `Call`. A spine whose head `lookup` finds in that environment stays `c:lambda`. A λ-headed spine, including `{:app, {:lam, ...}, arg}`, is `Let` via `emit_lam_app/10`. The spine arm whose head is neither a λ nor a variable is `c:lambda`. In `examples/half_ok.muro`, `plus` elaborates as `Fun` with parameters `n : Nat`, `m : Nat` and body

```text
Match (Var n)
  | zero  => Var m
  | suc np => Suc (Call plus (Var np) (Var m))
```

`half`'s last arm is `Suc (Call half (Var p))`.

Layouts: `Nat`, `Unit`, `Pair` of two layouts, `Stream` of a seed layout, `Data`, and `Opaque`. `{:prod, a, b}` is `Pair` of the two field layouts. `swap` in `examples/pair.muro` is `Pair Nat Nat`. `Opaque` is the `ctype/2` fallback only after `Nat`, `Unit`, `Stream`, `Data`, and `Pair`. Today's C spelling of a `Pair` parameter as `void *` (`signature/3` through `ctype/2`) is backend printing. `ctype({:app, f, _})` peels to the head, so parameters and indices on a data type stay `Data` and are not extra slots. A constructor argument is stored unless its quantity is `:erased` (`ctor_fun`). Each `Data` layout holds the name, constructors in declaration order, and live fields (source name × layout). The backend reads that record and does not call `data_of_ctor/2`. `cons` (`examples/list.muro`) stores `A` at `Opaque` and `List A` at `Data List`. `fromMaybe` (`examples/maybe.muro`) returns `Opaque`. Affine `n` on `fzero` and `vcons` (`examples/vec.muro`) is a `Nat` field.

`Fun` is name, export, live parameters (source name × layout), return layout, body. `Muro.Emit.C.peel_lams/2` opens it (`c:unsupported` when the body is not a λ). `Muro.Emit.peel_lams/2` returns the leftover term and does not fail. `Muro.Emit.eta_body/2` stays on the Elixir walk.

- `Let` — `emit_lam_app/10`. An erased λ binder drops its argument; a use of that name is `c:erased` (the `{:var, name}` clause of `emit/5` on an `:erased` entry). `{:munit, ...}` is `Let` at `Unit`.
- `Call` — saturated global `Fun`. A short or extra application (`emit_global/5` when the live count differs), an applied local, a bare λ, or a def as a value is `c:lambda`.
- `Con` — saturated constructor, zero fields included. The static object is C printing.
- `Match` — `{:mnat, ...}` / `{:mdata, ...}`, declaration order, motive erased. Empty branches, an unknown constructor, or a binder/telescope mismatch are `c:unsupported`. An erased constructor field is omitted from `Data`. Its binder is a live dummy: `open_branch/5` sets `void * = 0`, marks the entry `:live`, and does not take a struct slot. A use is `Var`, not `c:erased`. Elaboration copies the surface arm, including a clash placeholder, and does not re-check it. `check_branches` skips the body when `clashes/5` is true (`lib/muro/check.ex`, `manual/indexed.md`); `emit/5` has no clash test. `vhead` (`examples/vec.muro`) keeps `vnil => Zero` beside `vcons p a as => Var a`.
- `Zero`, `Suc`, `Tt`, `Pair`, `LetPair`, `Uncons`, `Abort` — `:ze`, `{:su, _}`, `:one`, `{:pair, _, _}`, `{:letp, ...}`, `{:ucons, _}`, `{:memp, ...}`.
- `Stream` — seed, `capture_fields/3`, closed step to a head/next `Pair`. A non-λ step is `c:lambda`.
- Atoms are a closed `Data` layout named `Atom`: one nullary constructor for each declared atom, in declaration order. A literal is `ctor` of that declaration and elaborates as `Con`. A match on atoms is `mData` and elaborates as `Match`. In `agda/Muro/IR.agda`, `atom` and `matom` are those `Tm` forms (`ctor` and `mData`). They sit inside `Tm` and inside the verified fragment. There is no separate elaboration family and no atom-specific lemma. An index outside the enumeration is `c:unsupported`. No term builds an atom from a string. The Elixir backend prints `Con "Atom" s []` as the BEAM atom `s`, which is sound because the enumeration is closed. The C backend prints the same `Con` as the enumerator it already emits (`MURO_ASC`). Elixir's `{:atom, name}` and `{:matom, ...}` (`lib/muro/ast.ex`) are the surface spelling of this data.

Refusals, by producer. `classify/1` returns `:stream` for `{:nu, _, _}`, `{:always, _, _, _}`, and `{:bisim, _, _}`, and `:machine` for `:i64`, `:f32ty`, `{:tensor, _, _}`, `{:addi, _, _}`, `{:muli, _, _}`, `{:addt, _, _}`, `{:toi64, _}`, and `{:packi, _, _}`. Its catch-all is `nil`. `forbid/1` walks the children on `nil`. `reject/1` therefore yields only `c:stream` and `c:machine`. `c:erased` is the erased-variable clause of `emit/5`. A λ-headed application is `Let`. `c:lambda` on an application is the local-variable arm and the arm whose head is neither a λ nor a variable, plus the bare-λ clause, the non-λ `{:unf, _, _}` clause, and an arity mismatch in `emit_global/5`. `c:unsupported` is `Muro.Emit.C.peel_lams/2`, empty or unknown `{:mdata, ...}`, a branch whose binders do not match the telescope, and the catch-all of `emit/5`. `test/muro_emit_c_test.exs` asserts `c:lambda` and `c:machine`. `c:stream` is specified in `manual/emit.md` and `AGENTS.md`.

## Guarantees

Elaboration is a function of a book that `Muro.check_file/2` has accepted. The IR term is the run image: spec, evidence, erased λ-arguments, motives, and rewrite proofs are gone. Semantic faithfulness on Nat, data, atoms, pairs, and the stream-as-step encoding is observational equivalence with the Agda run semantics of `Tm`. An atom is data in that semantics: the closed enumeration, introduced by `ctor` and eliminated by `mData`. The correspondence is the elaboration of `Tm` in `agda/Muro/IR.agda`, pinned by the `refl` examples there. It is not a theorem about `cc`. A backend is a function from IR to text. Two backends that both translate a given IR term are required to agree on that observation. The exit test — C and Rust artifacts of one agent-written `run`, same results — is the empirical check of that requirement.

## Outside the boundary

`cc`, `rustc`, and the assembler are trusted only to translate the IR text. CompCert is available for the high-assurance C path and is still only a translator. The C arena contract (`MURO_ALLOC`, block reuse on the next call, `manual/emit.md`) is a backend obligation. The IR does not discharge it. Name mangling is a backend obligation. Memory safety of the generated C, NIF glue, and Rust `unsafe` blocks is outside the IR theorem. Liveness, sessions, placement, and distribution are outside this phase.

## Alternatives

**Machine nodes, Elixir-only lowering.** Phase 1 needs every IR term to have a C translation and a Rust translation. `I64` and `Tensor` nodes would miss the C half (`Emit.C` refuses them; `Muro.Emit` prints `Nx.add`). They stay on the AST walk.

**Per-backend AST walks.** Separate walks in `Muro.Emit` and `Muro.Emit.C` end the chain once per target. The chain ends at this IR.

## Key Decisions

- Post-check image of `run` and `run internal`. IR constructors are not added to `Tm` or `PTm`.
- Binder use is `Var`. `Call` is a saturated global. A local-variable head is `c:lambda`. A λ-headed spine is `Let`.
- `{:prod, a, b}` is `Pair`. `Opaque` is the `ctype/2` fallback after that. `Data` carries constructors and live fields. An erased constructor field is a dummy, not an erased λ. Clash arms are copied and not re-checked.
- Atoms are a closed `Data` enumeration inside `Tm`. A literal lowers to `Con`. A match lowers to `Match`. Dynamic creation is refused.
- Machine operators stay deferred, so every IR term has a C translation and a future Rust translation.
- Stream-as-step is included because current C emits that encoding.
- Five refusal names at elaboration. Tests lock `c:lambda` and `c:machine`. `classify/1`'s catch-all is `nil`. Further limits are predicates on well-formed IR.
- Agda elaboration of `Tm` first, then an Elixir elaborator written to match.
- Backends translate only: `cc`, `rustc`, the assembler, and CompCert.

## PR Plan

1. **Agda IR and elaboration.** Files: `agda/Muro/IR.agda`. Depends on: none. Elaborates the closed run fragment of `Tm`. Atoms are the closed enumeration (`ctor` / `mData` of a `Data` layout), inside `Tm`, with no separate family and no separate lemma. Includes `Var`, `Opaque`, and `Data` layouts. Agreement is the `refl` examples in that module. No Elixir in this PR.
2. **Elixir elaborator.** Files: `lib/muro/ir.ex`, a correspondence note in `manual/`, tests elaborating `examples/half_ok.muro`, `examples/nats.muro`, `examples/list.muro`, and `examples/sort.muro`, plus `c:machine` on `examples/nx_add.muro` and a bare-λ `c:lambda` case. Depends on: PR 1. Matches the Agda judgment, including atoms. Emitter text stays as it is.
3. **C backend on the IR.** Files: `lib/muro/emit/c.ex` and `emit_c/2` in `lib/muro.ex`. Depends on: PR 2. Behavior-preserving against `test/muro_emit_c_test.exs`.
4. **NIF from `--backend c`.** Files: an `elixir_make` NIF or Port reached from `lib/mix/tasks/muro.emit.ex`, and one closed `run` callable from Elixir. Depends on: PR 3. Refusals `c:lambda`, `c:machine`, `c:stream`, `c:erased`, and `c:unsupported` stay in force. Sequenced here. The NIF is undesigned.
5. **Trust note.** Files: `manual/emit.md`. Depends on: PR 3 only. States that `cc` and `rustc` translate only, and that CompCert is the high-assurance C translator.
6. **Rust backend.** Files: a later emitter module on the same IR. Depends on: PR 2, and on PR 3 for the exit comparison. Rust syntax belongs to that PR.

This plan ends at the Rust backend.

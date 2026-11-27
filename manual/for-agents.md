---
title: For agents
slug: for-agents
order: 19
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
- Leave `?` only while a term is unfinished. A hole always fails and is not in the finished book. A `?` is not an axiom.
- An axiom is `axiom NAME : evidence TYPE`, with no body. Only that declaration is an axiom. The type is evidence. The book and the lines the checker prints are in [The wall](wall.md#axioms) and [Library](library.md#classicalmuro).

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
lib/muro/prefix.ex      a list of directed moves is a legal prefix of a session from a position; the finite forms follow the Agda derivation; recursion, a named continuation, a dependent payload, an evidence bound, an indexed bit, a case, and the numeric position are this checker
lib/muro/fail.ex        a party of a two-party meeting may stop; a receive from that party has a failure arm; OTP and fsm emit it; other backends are `c:mayfail`
lib/muro/talk.ex        one description of an exchange, mirror of seen
lib/muro/choreo.ex      a global type projected to each role pair, mirror of project
lib/muro/place.ex       place / scheme / move, mirror of decide
lib/muro/prelude.ex     book behind every checked file
lib/muro/prelude.muro   pred, plus, inj-suc, plus_suc, sym, cong
lib/muro/load.ex        import: a relative path, pkg:, and std:
lib/muro/std.ex         the ordinary library, embedded at compile time
lib/muro/std/*.muro     bool, classical, le, list, maybe, ord, suc_bin, word
lib/muro/axiom.ex       declared axioms; lines for definitions the entry file reaches; a run that reaches one is refused
lib/muro/emit.ex        run → Elixir source
lib/muro/repr.ex        a repr: check the host shape and emit decode/1, decode/2, and encode/2. Not a kernel term.
lib/muro/emit/equations.ex closed equations shared by the ExUnit, pytest, and Rust test suites
lib/muro/emit/exunit.ex closed equations → one ExUnit module (`--backend exunit`, `kind: :exunit`)
lib/muro/emit/pytest.ex closed equations → one pytest module (`--backend pytest`, `kind: :pytest`)
lib/muro/emit/rust_test.ex closed equations → one Rust test file (`--backend rust-test`, `kind: :rust_test`)
lib/muro/emit/otp.ex    a conformance, and a reading, is a GenServer; a marked peer is monitored and a `:DOWN` that is not a halt takes the failure arm; a book with no mark emits the previous module (`--backend otp`)
lib/muro/emit/fsm.ex    a session endpoint is a state machine; a marked book has `down/1` and `down/2` for a failure arm; a book with no mark emits no `down`; a keyed family that checks is a child with `new/0`, `arrive/4`, `resolved/2` (an open instance leaves), `withdraw/2` (a held instance resolves without opening), `skip/3`, `drop_key/2`, `skip_below/2` (one floor for every key: an arrival at or below it is the departed refusal), `finish` (`:resolve` or `:rerun`), and `check_trace/1` (arrivals, resolutions, withdrawals, skips, drops, `skip_below`, reruns, and `{party, id, send|recv|down}`). A rule is `never held`, `held while earlier unresolved`, or `held while any unresolved`. `earlier_resolved k kind` names the earlier instances of that key and kind; each meeting end has `finish`, and `:rerun` when one family uses that end; two families on one end name `finish` on the family child; the transport stays with the host (`--backend fsm`). A family may be marked `may redeliver`. `contract name : idempotent init`, `contract name : in order`, and `contract name : dense`, and `skip` after an entry, are [State machines](fsm.md#an-external-contract).
lib/muro/emit/c_session.ex a session endpoint is a pure step written as C; the actions are the ones the state machine takes, init takes `uint64_t`, and `down` is not emitted (`--backend c`)
lib/muro/emit/node.ex   a cross, and a cross reading, is one call and one monitor (`--node`)
lib/muro/emit/mbi.ex    exactly one exported run as an .mbi image (`--backend mbi`, `kind: :mbi`); a run it calls is a definition in the image; muro-beam loads it
lib/muro/example.ex     same book as Agda
lib/muro/mutate.ex      mutants of run definitions (`mix muro.mutate`)
lib/muro/synth.ex       version-space search on an emitted step (`mix muro.synth`)
lib/muro/synth/procedure.ex  one search the command can run: generate, evaluate, rank
lib/muro/synth/procedure/traces.ex  the version-space search (`--on traces`)
lib/muro/fill.ex        one definition body by search (`mix muro.fill`); the checker decides
lib/mix/tasks/muro.check.ex
lib/mix/tasks/muro.mutate.ex
lib/mix/tasks/muro.synth.ex
lib/mix/tasks/muro.fill.ex
agda/Muro.agda          public re-export
agda/Muro/Syntax.agda   Tm n (de Bruijn)
agda/Muro/Subst.agda    wk, sub, inst
agda/Muro/SubstLemmas.agda  renaming / substitution algebra
agda/Muro/Env.agda      Sig, Ctx, uses, mode order (shared by Check and ⊢)
agda/Muro/Check.agda    the decision procedure: structural on the term, fuel only where it reduces
agda/Muro/Session.agda  affine session judgment; a payload is a nat, a bit, unit, a pair, a record, a vector whose length is a received nat, a nat at most a bound the sender owes evidence for, or a non-indexed declared data type; a received bit selects one of two arms; a name is a session declared earlier, opened on the declaration prefix with no fuel; a parameter is a nat; %1 must finish; decide searches, skel is the OTP actions
agda/Muro/Prefix.agda   a legal prefix of end, send, recv, choose, and branch; a derivation is the prefix; the decision procedure accepts a list only when that list has a derivation; completeness is not claimed; recursion, a named continuation, and the numeric position are not this theorem; `--safe`; not a Tm
agda/Muro/Rec.agda      equi-recursive `rec X. S` unfolded to a guarded coinductive protocol (`--safe --guardedness`); a guarded self-call of a parameterised session is the same coinduction (`stream`); `dual∞`, conformance, and meet are bisimulations; a declared data payload inside `rec` meets when `sent` holds; `Finishes` stays finite, so a jump is not `%1`. `agda/Muro.agda` imports it, so that file carries the same pragma
agda/Muro/Dual.agda     the other end of a session; send swaps with recv, a dependent receive swaps with a dependent send, an evidence send swaps with an evidence receive, an indexed bit keeps its index and each arm dualises, and the payload type stays; `session name := dual name` follows it
agda/Muro/Meet.agda     two processes on one channel; a send meets a receive of the same payload type and the value inhabits it; a received nat instantiates a vector length; an evidence payload meets as a nat; a literal bit meets the arm of that bit; a variable meets a receive at its innermost binding; `meet name : left with right` follows it
agda/Muro/Talk.agda     one description of an exchange; say names one payload and one continuation; `session name := seen party with party in talk` follows it
agda/Muro/Choreo.agda   a global type; `g ↾ r / s ≡ b` is the binary session of one role with another; `project-sound`, `project-complete`, and `pairwise-dual`; `--safe`; not a Tm
agda/Muro/Seated.agda   a party of a description sits at a place; `seat name : party at place in talk` follows it; the same place stays; two places cross once
agda/Muro/Held.agda     a meeting at the parties' places; the same place stays; two places cross once; a `.muro` file does not write it
agda/Muro/Arrow.agda    %1 on a Π binder must be used; both marks are the affine quantity
agda/Muro/Grade.agda    a grade pair `(c, t)` on a binder; `ungraded-fragment` is the affine check; not a Tm
agda/Muro/Beam.agda     erase a core term to the grade judgment; `GTm` and `decide` are unchanged; not a Tm
agda/Muro/Linear.agda   multiplicity on a session endpoint; λ¹ must be used once; ⊸ accepts or returns it; the protocol is `SExp`, so `rec` and a declared data payload are endpoints; `dualS` keeps both; `--safe --guardedness`; not a Tm
agda/Muro/Place.agda    placement coeffect; ambient by default; one boundary; run has no seat
agda/Muro/Family.agda   keyed-family hold rule, any number of keys; a signal opens against the instances of its key that had already arrived; the generator is not this proof; `--safe`; not imported by Muro.agda
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

`mix muro.check`, `mix muro.mutate`, `mix muro.synth`, `mix muro.fill`, `mix muro.emit`, `mix muro.gen`, `mix muro.init`, and `mix muro.deps.get` run in any directory once the archive is installed, with or without a `mix.exs`.

A project without Elixir uses the self-contained executable: `mise use -g github:murolang/muro@0.22.37`. If mise answers `No versions found` or a 404 from `mise-versions.jdx.dev`, run `mise settings set use_versions_host false` first. The commands are `muro check`, `muro emit`, `muro gen`, `muro init`, `muro skills add`, `muro deps.get`, `muro mutate`, `muro synth`, `muro fill`, and `muro ui`. `muro ui path.muro` prints how to install muro_visor and does not start the explorer. The page is [Visual explorer](explorer.md). The manifest is `muro.toml` or `[package.metadata.muro]` in `Cargo.toml`. The executable page is [The executable](binary.md).

Install it from Hex:

```
mix archive.install hex muro
```

Alternatively, from a checkout of this version:

```
mix deps.get
mix archive.build
mix archive.install muro-0.22.37.ez
```

From GitHub, Mix fetches the default branch and builds the archive:

```
mix archive.install github murolang/muro
```

`--force` skips the install question.

`mix muro --version` prints `Muro v` and the version of the copy that ran. Inside a project that depends on muro, the project's copy runs after `app.start`. Inside any other project, or outside a project, the archive's copy runs and the host is neither compiled nor started. The version line names the copy that ran.

A script run with `mix run --no-start` does not see the archive. Archives are on the code path only for Mix tasks. Use `mix muro.check` and `mix muro.emit`.

`mix muro.emit path.muro` prints the Elixir module. `mix muro.emit path.muro > path.ex` saves it. `mix muro.emit path.muro --backend exunit` prints one ExUnit module for the book's closed equations, including a library whose `param`s are not supplied. `mix muro.emit path.muro --backend pytest` prints one pytest module for those same equations. `mix muro.emit path.muro --backend rust-test` prints one Rust test file for those same equations. `--imports` with any of these three also collects the files the book imports directly. The pages are [Closed equations as tests](exunit.md), [Pytest](pytest.md), and [Rust tests](rust-test.md).

`--backend zig` writes `<name>.zig` next to the file. `zig` translates it. The proof stops at the run image.

`--backend mbi` writes `<stem>.mbi` next to the file only when the book has exactly one exported run and that body erases, and the binder grades stay. Any refusal, including a book with no exported run and a book with more than one, writes nothing and leaves an image already at that path byte for byte. The file is the image muro-beam loads. It is not Erlang BEAM bytecode. A run the entry calls is a closed definition in the image. A name that is not a run, data, a pair, a word, or a stream is refused. Two definitions that call each other are refused. muro-beam checks the image again. Writing the file is not that check. The page is [MBI images](mbi.md).

`--backend c` writes C. A session in the book is also a pure step, and the host keeps the transport. The Mix task builds a NIF when the working directory is the loaded Mix project. Add `{:elixir_make, "~> 0.10", runtime: false}` to the project deps, or run the task inside a project that depends on muro. Without `elixir_make`, that NIF stops and names the dependency. Outside the loaded project the task writes the `.h` and the `.c` only, and so does the executable. `nx` and `makeup` are optional. Checking and emitting Elixir do not load them.

## Committed modules

A project commits the modules `muro gen` writes. The `.muro` file is the source. Do not edit the generated file by hand. Change the `.muro` file and run `muro gen`.

`muro skills add` writes this block into `AGENTS.md`, and into `CLAUDE.md` when that file already exists, and writes the agent skills under `.agents/skills/`. It does not write `.cursor/skills` or `.claude/skills`. The command lines, the version, and the example path are filled from the project. The markers are part of the block. Each marker is a whole line. A trailing carriage return is allowed. An inline mention is left as prose. The file's line endings stay. Skill bodies are marked sections of this page, of [Committed modules](gen.md), and of [Synthesis](synth.md).

<!-- muro:begin -->
Muro has two jobs: spec and evidence. `run` is what is emitted.

The wall: a spec never becomes evidence. Evidence never becomes a run.

This project is pinned to Muro {{version}}. Commands for this project:

{{commands}}

Every binder is typed and every motive is written. Copy syntax from the bundled examples, not from memory. `out of fuel` is not acceptance; raise `--fuel` and check again. Generated files are not edited by hand.

Emit backends: {{backends}}. The emit skill names the flags (`--node`, `--imports`, `--prefix`, `--impl`). `--backend beam` is refused; use `mbi`. Mix forms (`mix muro.check`, `mix muro.emit`, `mix muro.gen`, `mix muro.synth`, `mix muro.fill`, `mix muro.mutate`, `mix muro.deps.get`) are the same commands in an Elixir project.

Success from `muro check` is a `Muro v…` line, then `All terms check. Evidence never becomes a run.`

`muro synth` exits 0 only when the output book checks and contains the homomorphism of the synthesized ranking. The synthesized PredProg is itself the certified term. It is not the Finder's ranking.

Agent skills (read these; do not invent tags, implicits, metavariables, or tactics):

- `.agents/skills/muro-book/SKILL.md` — write a book
- `.agents/skills/muro-check/SKILL.md` — check and fix refusals
- `.agents/skills/muro-emit/SKILL.md` — emit and backends
- `.agents/skills/muro-gen/SKILL.md` — manifest, gen, version pins
- `.agents/skills/muro-synth/SKILL.md` — synth, fill, mutate; the PredProg is the certificate
- `.agents/skills/muro-contracts/SKILL.md` — fsm contracts, packages, repr, params

Bundled examples: `.agents/skills/muro-book/examples/`. Nearest example: `.agents/skills/muro-book/examples/{{example}}.muro`. Docs: https://muro-lang.dev/docs and https://muro-lang.dev/docs/for-agents

The skills live under `.agents/skills/`. This command does not write `.cursor/skills` or `.claude/skills`, so a project-local editor config is left alone. Copy or symlink the `muro-*` skill folders there if your editor only loads those paths.
<!-- muro:end -->

`muro.exs` at the project root, a `:muro` key in `mix.exs`, `muro.toml`, or `[package.metadata.muro]` in `Cargo.toml` names each book and the target path. Elixir, fsm, and exunit entries also name the module. A pytest entry names a `.py` target and may omit the module. A Rust test entry names a `.rs` target and may omit the module. An `:otp` entry names a `.ex` target and may omit the module. An `:mbi` entry names a `.mbi` target and may omit the module. An entry may add `[kind: :exunit, impl: Adapter, imports: true]`, `[kind: :pytest, impl: "host.rounding"]`, `[kind: :rust_test, impl: "crate::rounding"]`, or `[kind: :c]`, `[kind: :rust]`, `[kind: :zig]`, `[kind: :asm]`, `[kind: :js]`, `[kind: :otp]`, or `[kind: :mbi]`. `imports:` is valid on an exunit entry, a pytest entry, and a Rust test entry. `muro:` is the version the books are checked with. `muro gen` and `mix muro.gen --check` refuse to run when it differs from the running version. The message names both versions. One invocation type-checks each book once and emits every target of that book from that copy, including both files of a C target. `--skip-check` does not type-check; `--check --skip-check` still compares bytes. The default type-checks.

`mix muro.init` creates `muro.exs` and `priv/muro/`. It prints a note that points at `muro skills add`. It does not write `AGENTS.md` or the skill files. `muro init --backend` stores that backend as the manifest's top-level `backend`. `muro init` writes the one manifest the directory calls for. If `muro.exs`, `muro.toml`, or `[package.metadata.muro]` is already present, it prints a diff of that file in its own format and leaves every file as it is. `mix muro.init --ci github` writes `.github/workflows/muro.yml`. The job installs the archive with `mix archive.install hex muro <version> --force`, with the version from the manifest, and runs `mix muro.gen --check`. `muro init --ci github` installs the executable and runs `muro gen --check`.

The page is [Committed modules](gen.md). Package imports (`import "pkg:..."`, `muro_deps:`, `mix muro.deps.get`, `muro.lock`) are [Packages](packages.md). The ordinary library is `import "std:file.muro"` ([Library](library.md)). It is compiled into the compiler. It is not the prelude, and it is not a package.

## Commands

```
mix deps.get
mix test
mix muro.check
mix muro.check examples/half_ok.muro
mix muro.mutate examples/half_ok.muro --only half
mix muro.synth path.muro
mix muro.synth path.muro --on traces
mix muro.fill path.muro --def name
mix muro.emit path.muro --backend exunit
mix muro.emit path.muro --backend exunit --imports
mix muro.emit path.muro --backend pytest
mix muro.emit path.muro --backend rust-test
mix muro --version
mix muro.init
mix muro.gen
mix muro.gen --check
mix muro.gen --skip-check
mix muro.deps.get  # fetch muro_deps/ and write muro.lock
make agda          # Job B only; needs vendor/agda-stdlib v2.3
```

On success, `mix muro.check` prints the version that checked the book, then one line per keyed family and one line per temporal declaration, in book order, then one line per projected pair of each choreography, then one line per definition the entry file reaches that depends on an axiom (`dne: depends on classical.LEM` when the entry file is `lib/muro/std/classical.muro`), then:

```
Muro v0.22.37
All terms check. Evidence never becomes a run.
```

A family marked `may redeliver` prints that mark on its line. A formula that says `relies idempotent init`, `relies in order`, or `relies dense`, and holds, prints `<name>: depends on contract idempotent init`, `in order`, or `dense` on the next line. `may redeliver` is not that line. A book with no keyed family, no temporal declaration, no choreography, and no reached definition that depends on an axiom prints those two lines and nothing between them. An imported definition the entry file does not reach is not a line. A `run` that reaches an axiom is a refusal, not a line. Use an axiom in evidence and spec, never in a `run`'s dependency cone. When the checker says `a run depends on`, move that classical step into evidence or remove the dependence. The refusal is in [The wall](wall.md#axioms). A book that imports packages prints `conforms to <name> <version> (sha256 <hash>)` after that sentence, one line per package it loaded. A book that imports none, and `mix muro.check` with no path, print only those two lines. With no path the task checks the built-in book (`Muro.Example.book/0`), the same book as `examples/half_ok.muro`. It does not walk `examples/`.

`Muro.Check.check_sig/2` returns `:ok` on a well-typed book, or `{:error, msg}` with every definition error in book order. `check_sig(book, fuel: n)` sets the fuel for each definition. Definitions are checked concurrently; the fuel is the bound, not a wall-clock timeout.

## Representations (do not add a third)

| Layer | Form | Where |
| --- | --- | --- |
| Parser / pretty / emit | named FOAS | `lib/muro/{parser,ast,emit}.ex` |
| Check / subst | de Bruijn | `lib/muro/{check,subst}.ex`, `agda/Muro/{Check,Subst}.agda` |
| Examples and metatheory | de Bruijn `Tm n` | `agda/Muro/Syntax.agda`, `agda/Muro/Example*.agda` |

Elixir constraints when you are in Job B: ASCII identifiers only. Do not define local `hd/1`. Guards cannot call ordinary `defp` helpers. `repr` entries are host-side declarations checked by `Muro.Repr`, not part of the Agda calculus.

## What is not in the language

Type : Type, cubical, tactics, implicits, unification, metavariables (a `?` always fails; it does not unify; `mix muro.fill` replaces a `?` that is the whole body of one definition), extra quantities, `+` on Stream or Either, typing raw Elixir, emitting spec or evidence, an axiom whose tag is not evidence, a run that depends on an axiom.

Full list: [Limits](limits.md).

## Releasing

Merging a version bump to main is the publish. Once the Elixir CI job on that commit is green, the `Hex and tag` job in CI publishes the `mix.exs` version to Hex unless that version is already there, pushes the annotated tag `vX.Y.Z` if it is missing, and then builds the self-contained binaries. A push that does not bump the version succeeds without moving an existing tag and without building the binaries. The publish does not wait for Agda or muro_visor, and the binary job does not delay the Hex publish. `muro_visor` is not published this way: Hex stages it, and it still needs 2FA.

The first publish through this workflow needs the repository secret `HEX_API_KEY`. Generate a key with `mix hex.user key generate --key-name muro-ci --permission api:write` and add it as `HEX_API_KEY` on murolang/muro. A missing secret fails the publish job with a clear error and does not print the key. The executable page is [The executable](binary.md).

## Agent skill: writing a book

<!-- muro-skill:book:begin -->
# Writing a Muro book

Muro is an explicit affine dependent type theory. You write the program together with its types, motives, and proofs. Nothing is inferred. A spec never becomes evidence. Evidence never becomes a run. Only `run` terms are emitted.

Docs: [For agents](https://muro-lang.dev/docs/for-agents), [Grammar](https://muro-lang.dev/docs/grammar), [The wall](https://muro-lang.dev/docs/wall), [Terms](https://muro-lang.dev/docs/language), [Examples](https://muro-lang.dev/docs/examples).

## Do

- Write a `.muro` file against the grammar. Put new programs where the project already keeps books, or in `examples/` in a checkout of muro itself.
- **Copy syntax from the bundled examples, not from memory.** This skill ships `examples/half_ok.muro` (the canonical book: a spec, a program, and a theorem about it), `examples/nats.muro`, and `examples/meet.muro` under `.agents/skills/muro-book/examples/`.
- Keep every binder typed. Write every motive.
- Use only the tags `run`, `run internal`, `spec`, and `evidence`.
- `pred`, `plus`, `inj-suc`, `plus_suc`, `sym`, and `cong` are already in scope (`lib/muro/prelude.muro` in a checkout; the same prelude is in the package). Defining one of those names replaces it, and drops any prelude definition that refers to it.
- The ordinary library is `import "std:<file>.muro"` ([Library](https://muro-lang.dev/docs/library)). Do not copy `List`, `Maybe`, or `Bool` into a new file, and do not add those names to the prelude. Do not copy `Either`, `left`, or `right` into a book that imports `std:classical.muro`.
- Write a library for many environments with `param` entries, and check it through a file that supplies them with `def` or `data` of the same names and tags ([Params](https://muro-lang.dev/docs/language#params)).
- Leave `?` only while a term is unfinished. A hole always fails and is not in the finished book. A `?` is not an axiom. It prints `expected` and `context`; fill it. `muro fill` replaces a `?` that is the whole body of one definition.
- An axiom is `axiom NAME : evidence TYPE`, with no body. Only that declaration is an axiom. The type is evidence. A `run` that depends on an axiom is refused and is not emitted. See [The wall](https://muro-lang.dev/docs/wall#axioms) and [Library](https://muro-lang.dev/docs/library#classicalmuro).

## Do not

- Invent tags, implicits, metavariables, or tactics.
- Promote a spec to evidence or evidence to a run.
- Treat a `?` as an axiom.
- Edit generated modules by hand. Change the `.muro` file and run `muro gen`.
- If you are only writing a book, do not edit the type theory (`agda/`, `lib/muro/*.ex`, `lib/mix/tasks/`). That is a different job; see [Extending the kernel](https://muro-lang.dev/docs/extending).

A definition is in the book as soon as it parses. The checker sees the whole book. Forward references are allowed. Emit keeps `run` only.

## Skeleton

```
-- comments start with --
def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
  λ (n : Nat) → λ (m : Nat) →
    match n motive (λ _ → Nat)
      | 0 => m
      | suc np => suc(plus np m)
```

```
muro check path.muro
```

What is not in the language: Type : Type, cubical, tactics, implicits, unification, metavariables (a `?` always fails; it does not unify), extra quantities, typing raw host code, emitting spec or evidence, an axiom whose tag is not evidence, a run that depends on an axiom. Full list: [Limits](https://muro-lang.dev/docs/limits).
<!-- muro-skill:book:end -->

## Agent skill: checking a book

<!-- muro-skill:check:begin -->
# Checking a Muro book

`muro check path.muro` type-checks a book. In an Elixir project the same command is `mix muro.check path.muro`. With no path, `mix muro.check` checks the built-in `half_ok` book.

Docs: [For agents](https://muro-lang.dev/docs/for-agents), [The wall](https://muro-lang.dev/docs/wall), [Fill](https://muro-lang.dev/docs/fill).

## Commands

```
muro check
muro check path.muro
muro check --fuel 20000 path.muro
mix muro.check path.muro
mix muro.check --fuel 20000 path.muro
```

`--fuel` is the checker's reduction bound. The default is `Muro.Check.default_fuel/0` (2000).

## Success and errors

Success is a `Muro v…` line, then `All terms check. Evidence never becomes a run.` A keyed family, a temporal declaration, a choreography, an axiom a reached definition depends on, and a package conformance may print lines between the version and that sentence, in book order. A book with none of them prints the two lines. See [State machines](https://muro-lang.dev/docs/fsm#an-external-contract) and [Packages](https://muro-lang.dev/docs/packages).

Read every error. The checker reports each definition that fails, in book order, separated by a blank line. Parse and check errors start with `line:col`. Conversion prints surface types (`Fin n`, not `#0`). A `?` prints `expected` and `context`; fill it.

`mix muro.check` on a library of unsupplied `param`s names the params it is missing. Check that library through a file that supplies them.

## Common refusals and how to fix them

- **`out of fuel` is not acceptance, and it is not a type error.** The checker gave up reducing. Raise `--fuel` and check again.
- **A multi-line `match` used as an argument needs parentheses.** Wrap the whole `match … | … => …` in `( … )`.
- **Reusing an affine variable inside a recursive `def` can be reported as `recursive call does not descend on a smaller argument`.** Before you change your recursion, check whether a non-reusable variable is used twice.
- **`match` branches must follow the order the constructors were declared in.**
- **Erased guards cannot rule out `run` branches.** An `evidence` or erased argument does not make a branch of a `run` term unreachable. Encode the invariant in a run-mode indexed type instead ([Indexed data](https://muro-lang.dev/docs/indexed)).
- **A long chain of `suc` is slow** to check. A closed numeral is a machine integer. Prefer machine words when the book allows it ([Machine numbers](https://muro-lang.dev/docs/machine)).
- **A `run` that depends on an axiom is refused** and is not emitted. An axiom is `axiom NAME : evidence TYPE` only.
- **Redefining a prelude name** (`pred`, `plus`, `inj-suc`, `plus_suc`, `sym`, `cong`) replaces it and drops any prelude definition that refers to it.

`muro fill path.muro --def name` writes a body for a definition whose body is `?`. It tries terms in order of size. A run is kept when the book's closed equations about that name still check. Evidence is kept when the type checks. It is a search. It is not `muro synth`. See [Fill](https://muro-lang.dev/docs/fill).
<!-- muro-skill:check:end -->

## Agent skill: emitting a book

<!-- muro-skill:emit:begin -->
# Emitting a Muro book

Emit only after a successful check. Spec and evidence are omitted. Erased arguments are dropped. Only `run` terms are emitted.

Docs: [Emit](https://muro-lang.dev/docs/emit), [MBI images](https://muro-lang.dev/docs/mbi), [State machines](https://muro-lang.dev/docs/fsm), [Closed equations as tests](https://muro-lang.dev/docs/exunit), [Pytest](https://muro-lang.dev/docs/pytest), [Rust tests](https://muro-lang.dev/docs/rust-test), [Host representations](https://muro-lang.dev/docs/repr).

## Backends

`muro emit path.muro` prints Elixir (the default). `--backend NAME` selects the backend. The accepted names are:

- `elixir` — Elixir module; the default. Module name from the file stem, or the name `Muro.emit_file/2` is given.
- `c` — `<name>.h` and `<name>.c`. A `Nat` run may also be a NIF when the Mix task runs inside the loaded Mix project. `--prefix TEXT` prepends a C identifier (including the separator, as in `admit_`) to every run the host calls and to that book's session entry points. Other backends refuse `--prefix`.
- `rust` — `<name>.rs`. The same image as C, translated by `rustc`. Refuses a term the C backend refuses.
- `zig` — `<name>.zig`. The same image. A function that allocates takes `muro__allocator` first and returns an error union.
- `asm` — `<name>.s`, Cortex-M0, Nat run.
- `otp` — a GenServer for a conforming process. A marked peer is monitored; a `:DOWN` that is not a halt takes the failure arm.
- `js` — `<name>.mjs` and `<name>.d.ts`; Node runs the module.
- `mbi` — `<stem>.mbi` for muro-beam, exactly one graded run. A run it calls is a closed definition. Writing the file is not acceptance; muro-beam checks the image again. `--backend beam` is refused; use `mbi`. The file is not Erlang BEAM bytecode.
- `fsm` — one state machine per session, and one dispatcher per keyed family, on stdout. The transport stays with the host.
- `exunit` — one ExUnit module for the book's closed equations, on stdout.
- `pytest` — one pytest module for those same equations, on stdout.
- `rust-test` — one Rust test file for those same equations, on stdout.

`--imports` also collects the closed equations of the files this book imports directly. It is valid only with `exunit`, `pytest`, or `rust-test`. `--impl` names the host module those tests call, and is valid only with `pytest` or `rust-test`. `--node NAME` writes one call for each `cross`, registered on that node, and is valid only with the elixir backend.

```
muro emit path.muro
muro emit path.muro --backend c
muro emit path.muro --backend rust
muro emit path.muro --backend zig
muro emit path.muro --backend asm
muro emit path.muro --backend otp
muro emit path.muro --backend js
muro emit path.muro --backend mbi
muro emit path.muro --backend fsm
muro emit path.muro --backend exunit
muro emit path.muro --backend exunit --imports
muro emit path.muro --backend pytest
muro emit path.muro --backend rust-test
muro emit path.muro --backend c --prefix TEXT
mix muro.emit path.muro --backend fsm
```

A file of unsupplied `param`s is accepted only by `exunit`, `pytest`, and `rust-test`.

## C, Rust, Zig, and assembly refusals

The C backend refuses some terms that the Elixir backend accepts. `U8`, `U32`, `U64`, and `I64` are passed by value. `F32`, `Tensor`, `addt`, and `packI` are refused as `c:machine`. Unapplied lambdas, definitions passed as values, and calls of local functions are refused as `c:lambda`, because C has no closures. A raw `ν`, `Always`, or `~` inside a `run` is refused as `c:stream`. Allocation goes through `muro__ALLOC`. The Rust, Zig, and Cortex-M backends print that same image and refuse a term the C backend refuses.

A `repr` makes emit also write `decode_<type>/1`, `decode_<type>/2`, and `encode_<type>/2`. Decode returns `{:ok, value, table}`. Encode takes that table. See [Host representations](https://muro-lang.dev/docs/repr).

For committed modules, a manifest names each book and target, and `muro gen` writes them. See the gen skill and [Committed modules](https://muro-lang.dev/docs/gen).
<!-- muro-skill:emit:end -->

## Agent skill: contracts, packages, and params

<!-- muro-skill:contracts:begin -->
# Contracts, packages, representations, and params

Docs: [State machines](https://muro-lang.dev/docs/fsm#an-external-contract), [Packages](https://muro-lang.dev/docs/packages), [Host representations](https://muro-lang.dev/docs/repr), [Params](https://muro-lang.dev/docs/language#params), [Sessions](https://muro-lang.dev/docs/sessions).

## External contracts

A keyed family that checks is a child state machine with `new/0`, `arrive/4`, `resolved/2`, `withdraw/2`, `skip/3`, `drop_key/2`, `skip_below/2`, `finish`, and `check_trace/1`. A rule is `never held`, `held while earlier unresolved`, or `held while any unresolved`. A family may be marked `may redeliver`.

External contracts are declared in the book:

- `contract name : idempotent init`
- `contract name : in order`
- `contract name : dense`

A formula that says `relies idempotent init`, `relies in order`, or `relies dense`, and holds, prints `<name>: depends on contract …` on a successful check. `may redeliver` is not that line. `skip` after an entry is part of the same contract story. See [State machines](https://muro-lang.dev/docs/fsm#an-external-contract).

The bundled example `.agents/skills/muro-book/examples/meet.muro` is the nearest session book.

## Packages

Import a book from a git or Hex package at the version `muro.lock` records.

```
muro deps.get
mix muro.deps.get
```

`muro deps.get` fetches `muro_deps/` and writes `muro.lock`. `muro check` on a book that imports packages prints one `conforms to <name> <version> (sha256 <hash>)` line per package.

## Host representations

A `repr` states the host shape of a data type. It is a host-side declaration checked by `Muro.Repr`, not a kernel term. Emit writes strict `decode_<type>/1`, `decode_<type>/2`, and `encode_<type>/2`. Decode returns `{:ok, value, table}`. Encode takes that table. See [Host representations](https://muro-lang.dev/docs/repr).

## Params

Write a library for many environments with `param` entries, and check it through a file that supplies them with `def` or `data` of the same names and tags. `muro check` on the library itself names the params it is missing. A file of unsupplied `param`s is accepted only by the `exunit`, `pytest`, and `rust-test` backends. See [Params](https://muro-lang.dev/docs/language#params).
<!-- muro-skill:contracts:end -->

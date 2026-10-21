# Changelog

## 0.16.38

A value can sit at a place. The place is ambient when it is not named. Staying there takes no boundary. Crossing to another place takes one. A polymorphic value is used where it is instantiated, and that use stays. A run term has no place.

### Manual

- Extending: placement is a coeffect. Ambient is the default. A boundary is one step.
- Limits: a `.muro` file does not write a place yet.

### Package

- Version 0.16.38.

## 0.16.37

A Π binder can require its variable to be used. `(%1 x : A)` refuses a binder that is never used. `(%0 x : A)`, and an unmarked binder, still allow that. The λ mark and the Π mark must agree. `run` is unchanged.

### Manual

- Grammar, Terms, Examples: `%0` and `%1` on a Π binder.
- Extending: a `%1` binder must be used. Both marks are the affine quantity.

### Package

- Version 0.16.37.

## 0.16.36

A session can require the process to finish. `session %1` refuses an abandoned channel. An unmarked session, and `session %0`, still allow it. `run` is unchanged.

### Manual

- Grammar, Terms, Examples: `%0` and `%1` on a session.
- Extending: a `%1` session must finish. `%0` is the affine session.

### Package

- Version 0.16.36.

## 0.16.35

`--backend otp` writes a GenServer for each process that conforms to a session. The process sends and receives bits with its peer. Abandoning the channel stops the server, and a monitor sees that stop. The BEAM runs the server. The proof stops at the conformance derivation. `run` is unchanged.

### Emit

- `Muro.Emit.Otp`, from `--backend otp`. The file is `<stem>_otp.ex`.

### Manual

- Emit: the OTP process. One peer. A bit is the payload.

### Package

- Version 0.16.35.

## 0.16.34

A `.muro` file can state an affine session protocol and a process that conforms to it. Abandoning a channel is accepted. A second send, or a send where the protocol says receive, is refused. `run` is unchanged.

### Manual

- Grammar, Terms, Examples, Limits, and For agents: `session` and `conform`. A payload is a bit.
- Extending: the checker decides the session judgment.

### Package

- Version 0.16.34.

## 0.16.33

Affine session protocols are specified in Agda. Sending a bit continues as the branch for that bit. Abandoning a channel has a conformance derivation. A second send, or a send where the protocol says receive, has none. `run` is unchanged.

### Manual

- Extending: the affine session judgment. A protocol is spec. A conformance derivation is evidence.

### Package

- Version 0.16.33.

## 0.16.32

`--backend asm` prints a Cortex-M run for `Nat`. `half(4)` is `2` and `plus(2, 3)` is `5`, the same integers the Nat NIF returns. The assembler translates that text. The proof stops at the run image.

### Emit

- `Muro.Emit.Asm`, from `--backend asm`. The file is `<stem>.s`.

### Tests

- `half(4)` is `2` and `plus(2, 3)` is `5`, the same integers the Nat NIF returns.

### Manual

- Emit: the Cortex-M file. The assembler translates. The proof stops at the run image.

### Package

- Version 0.16.32.

## 0.16.31

`--backend rust` prints the same closed run as the C backend. `half(4)` is `2` and `plus(2, 3)` is `5`, the same integers the Nat NIF returns. `rustc` translates that text. `cc` translates the C. CompCert is the high-assurance C translator. The proof stops at the run image.

### Emit

- `Muro.Emit.Rust`, from `--backend rust`. The file is `<stem>.rs`.

### Tests

- `half(4)` is `2` and `plus(2, 3)` is `5`, the same integers the Nat NIF returns.

### Manual

- Emit: the Rust file. `rustc` and `cc` translate. CompCert is the high-assurance C translator. The proof stops at the run image.

### Package

- Version 0.16.31.

## 0.16.30

An exported run whose arguments and result are `Nat` is a NIF. `half(4)` is the integer `2`, and `plus(2, 3)` is `5`. The argument and the result are non-negative integers that fit in 64 bits; anything else is a bad argument. The generated C is unchanged: `Nat` is the tagged struct, and the call allocates it through one `MURO_ALLOC` block that the next call reuses. `elixir_make` runs the makefile. A file with no such run still writes the `.h` and the `.c` only. `run internal` stays `static`.

### Emit

- `Muro.Emit.Nif`, from `--backend c`. The library is `priv/<stem>.so`. The module is the camelized stem.

### Tests

- `half(4)` is `2` and `plus(2, 3)` is `5`. A negative argument is a bad argument. `nats` writes no NIF. `inc` is an entry and `step` is not.

### Manual

- Emit: the Nat NIF and the block. `cc` translates the C. The proof stops at the run image.

### Package

- Version 0.16.30.

## 0.16.29

A checked book has a closed `run` image. `Muro.IR` keeps `mode: :run`, records `run internal` as `export: false`, and drops spec, evidence, and data declarations. An atom is a nullary constructor of one closed data declaration. An index outside that declaration is refused. Nothing in the image builds an atom from a string. The C emitter prints this image. The Elixir emitter still walks the named AST. A program the C emitter already accepted prints the same text. The refusals stay `c:lambda`, `c:machine`, `c:stream`, `c:erased`, and `c:unsupported`.

### Emit

- `Muro.IR` in Agda and `Muro.IR.elaborate/1`. `Muro.Emit.C` prints that image.

### Tests

- `half_ok`, `nats`, `list`, and `sort` elaborate. `nx_add` is `c:machine`. A bare λ is `c:lambda`. An erased argument is dropped. A raw ν is `c:stream`. A name outside the book is `c:unsupported`. An atom literal is a nullary constructor of `Atom`.

### Manual

- Extending: the image is not a source syntax. The C emitter prints it. The Elixir emitter still walks the named AST.

### Package

- Version 0.16.29.

## 0.16.28

`uncons` after unfolding a definition whose body is a family λ has a derivation. `fam-def-uncons` opens that definition onto the λ, and `uncons` of the pair instantiated at the seed reads it at the family goal, in any context. The signature hypothesis of preservation is still not the checker's acceptance of the definition. Productivity of an accepted unfold is still argued from the checker's shape.

### Manual

- Limits, CSHRL, Extending: `fam-def-uncons` opens a family-λ definition onto that λ and derives `uncons` of the pair at the seed. The productivity sentence stays.

### Package

- Version 0.16.28.

## 0.16.27

Discrete predicate synthesis, beside the checker. A predicate is a Boolean combination of feature tests. A chain fires the action of the first predicate that holds, or the default. The search keeps the highest-scoring predicate that agrees with an oracle on a trajectory, and drops a score of zero. `fewer?/7` compares two actions by how soon a stop is reached. `policy/3` writes that chain as a `run` definition over `Bool`. The checker sees the policy. It does not see the search.

### Library

- `Muro.Synth`.

### Tests

- A chain fires one action. Depth 0 returns the feature test that matches the oracle. An observation shrinks the version space. States that agree on the features a predicate reads agree on its value. Fewer steps is the better action, and a stop ties them. A miss at depth 0 deepens once and finds the negation. The policy from that search checks, emits, and runs.

### Package

- Version 0.16.27.

## 0.16.26

Two run definitions that spell the same way after `-` and `'` become `_` stay two functions, and a definition named like an Elixir reserved word still compiles. `foo-bar` and `foo_bar` used to become one `foo_bar`, so a proof about the second ran the first. `and` was emitted as `def and` and the module did not parse. The later definition takes a numeric suffix (`foo_bar_2`). A reserved word is prefixed with `muro_`. The C backend uses the same suffix when two definitions, or a definition and a constructor function, claim one spelling. `and` stays `and` in C.

### Emit

- `Muro.Emit.def_names/3`. Elixir and `Muro.Emit.C` both take definition names from it.

### Tests

- `foo-bar` and `foo_bar` emit two functions, and the call of `foo_bar` returns `suc 0`. A reserved word emits `muro_` and the module evaluates. The same pair compiles as two C functions.

### Manual

- Emit: the suffix and the `muro_` prefix.

### Package

- Version 0.16.26.

## 0.16.25

A `+` binder on an unfold step must be a copyable type, as a λ, a match branch, and a constructor field must. `unfold s (λ (+ t : Stream Nat) → ((t, t), t))` is refused. A Nat seed may still be `+`.

### Checker

- `Check` ⇐-unf for a λ step, and `Muro.Check`. The seed type is the type `isCopy` sees.

### Tests

- A reusable stream step is refused. A reusable Nat step still checks.

### Manual

- Streams: the unfold binder is the same `+` test as any other binder.

### Package

- Version 0.16.25.

## 0.16.24

A spec definition descends, as a run or evidence definition does. A spec type could name itself unapplied, and `whnf` unfolded it, so `X := Π (+ x : X) → Empty` checked and `self-app self-app` was a closed evidence term of `Empty`. The same body as `T := T`. Spec is now in the call graph: a self-reference must be applied, and a call must pass a smaller variable at the callee's position, or the caller's argument unchanged to an earlier definition. `IsEven` stays, because it recurses on a match-bound predecessor. A spec definition that reaches a run or evidence definition, and is reached by it, is in that block. The guard that lets an evidence unfold name itself does not apply to spec. Termination of an accepted block is still argued from that measure, not proved, and fuel still bounds a spec computation inside a type.

### Checker

- `Check.recMode spec` and `rec_mode?(:spec)`. `checkRec` and `selfApplied` no longer skip spec. Then `Muro.Check` (`check_rec`, `self_applied`).

### Tests

- A spec negation and a spec defined as itself are refused. A spec family that recurses on a match-bound predecessor checks, as do `examples/half_ok.muro` and `examples/even_dec.muro`.

### Manual

- Terms, Data, Start, Limits, Extending: spec descends. Limits: this removes the negation; it does not prove normalisation.

### Package

- Version 0.16.24.

## 0.16.23

ν is in ⊢. Stream, `Always`, `~`, and a declared family are rules of the judgment: `unfold` and `uncons`, the way `match` and `refl` are. An unfold of a stream is the λ, and `uncons` of that λ wraps. An unfold of a declared family is the pair instantiated at the seed, and `uncons` of that pair reads the head obligation and the proof at the tail. `uncons` of the source λ wraps, and that wrap is not the family read. The checker still refuses a self-call in the head; the judgment records the pair and does not recheck that guard, so productivity of an accepted unfold is argued from the checker's shape. Preservation covers the wrap and the pair read. It does not cover `uncons` after unfolding a definition whose body is a family λ, and the signature hypothesis of preservation is not the checker's acceptance of that definition. A checker yes is a derivation at the checker's type when the subject is that term and every premise meets its rule; a family unfold is a derivation of the pair, and a premise off its rule is not claimed. Tensor and Atom remain outside.

### Checker

- `uncons` of an unfold is the pair read, the λ wrap, or the identity on a pair seed, the same steps as `⟶`. Anything else stays stuck. The step that read a declared family off the λ is gone.

### Tests

- A declared family unfold checks, and `head (tail s)` on a unit stream is `tt`. A body that is not a product is refused. An unfold that calls itself in the head is refused. `examples/dominance.muro` still checks.

### Manual

- Limits, Streams, Extending, CSHRL, README: ν is in ⊢, with the two subjects, the guard, and what preservation does not cover.

### Package

- Version 0.16.23.

## 0.16.22

CSHRL in Muro, under `examples/cshrl/`. The artifact's parameterised modules (Core, SuccessorCore, SuccessorCoreWithArithmetic, the finite deterministic environment class with its Finder) are files whose environment is a list of `param` entries. TwoState, BinarySacrifice and SkillInvestment supply them and prove their ranking theorems: `CoindHomo ranks` for TwoState, a `CoinductiveHomomorphism` ranking the sacrifice first and the impossibility of a `CoindHomo` in either direction for BinarySacrifice, and the same at each level below master for SkillInvestment. Each environment emits an agent that plans with the Finder, or with the successor Finder, and acts: in SkillInvestment the first works for 1 forever, and the second trains three times and then earns 5.

`envs/optimal.muro` is the return theorem. One agent, the step of TwoState, and `agent-optimal`: the reward stream of `agent` dominates the reward stream of every other policy, from every state. The proof is an unfold whose tail is the same statement at both successors. A ranking's `CoindHomo` does not say this, and neither does the Finder's choice of `go`. In BinarySacrifice the two policies' streams are incomparable under `Dom`.

### Examples

- `examples/cshrl/std`: Bool, Nat order, List, Stream with `Dom`. `examples/cshrl/lib`: `core`, `successor`, `successor_sum`, `finder`, `agent`. `examples/cshrl/envs`: `two_state`, `binary_sacrifice`, `skill_investment`.

### Tests

- Each environment checks, emits without spec or evidence, and its agents' first steps are the ones above. A library file alone is refused for its unsupplied params. `envs/optimal.muro` checks.

### Manual

- CSHRL: the layout, the params, the correspondence with the artifact, the agents, the return theorem, and what is proved. Examples, For agents, README: links to it.

### Package

- Version 0.16.22.

## 0.16.21

Each member of a mutual block descends on an argument of its own, and a call may pass the caller's argument unchanged to a member defined earlier. A block shared one argument position, and every call in it passed a smaller variable there. CSHRL's Finder did not fit: `best-trace s (suc k)` calls `trace-action s a k`, and `trace-action s a k` calls `best-trace s′ k` at the same `k`, with `k` second in one and third in the other. Now every call passes, at the callee's position, a variable smaller than the caller's argument or, into an earlier definition, that argument itself, so (size, index) decreases at every call. A self-call still needs a smaller argument, and two members that pass the argument unchanged to each other are still refused. Every block accepted before is accepted now.

### Checker

- `Check.RecSt`: `poss`, a position for each member of `block`, in place of `pos`; `isArgVar`, `posOf`, `earlier`; `checkRecGo` reads the callee's position. `sharedArgs` is every assignment of non-erased positions (`choices`), and `defRec`, `checkAt`, `retryBody`, `refuseShared`, `pickPos`, `checkBodyAt` take assignments; `zeroPos` in place of index 0. `Soundness.checkBodyAt-sound` takes `zeroPos`; nothing else in the proofs reads the recursion state. Then `Muro.Check` (`poss`, `order`, `arg_var?`, `earlier?`, `choices`).

### Manual

- Terms: descent in a mutual block. Limits, Extending: the rule and what is argued, not proved. Examples: why `bad_shared.muro` is refused.

### Package

- Version 0.16.21.

## 0.16.20

A file can declare `param` entries, which a file that imports it supplies. `param step : run Π (+ s : State) → State` is a name with a tag and a type; the importing book supplies it with a `def` or `data` of the same name and tag, and the supplying type is checked against the param's. Inside the library the param is the supplied definition, so `+ s : State` is copyable when the supplied `State` is, a run param is run code that emits, and a call to an evidence param discards its arguments' uses. A library for every environment no longer passes the environment as arguments to each definition, where a spec argument could not reach evidence and an abstract type could not be `+`. A file with an unsupplied param is checked where it is imported, with its errors at its own path and line; checked alone it names each missing param.

A run definition with the name and live arity of a `Kernel` function or macro (`max/2`, `min/2`) emitted a module that did not compile; only `length/1` was excluded from `import Kernel`. Every such name is excluded now.

### Import

- `Muro.Load`: `supply`, `param_check` (a definition `name (param)` checked with the book and not returned), `all_supplied`. An entry from another file reports at its own file (`Print.loc_prefix` reads `{file, line, col}`).
- `Muro.Parser`: the `param` entry; `param` ends a term and a constructor list. `Muro.Ast.book_to_db` refuses a `param` left in a book.

### Emit

- `Muro.Emit.kernel_clashes`.

### Manual

- Terms: Params. Grammar: `param`. Limits: what is checked for a library with params. For agents: writing one. Emit: Kernel names.

### Package

- Version 0.16.20.

## 0.16.19

`refl` is not a run term. Identity has one introduction, and run code could build it: `f refl` for `f : run Π (p : {0 ≡ 0 : Nat}) → Nat`, a run pair `(n, refl)`, or `def e : run {0 ≡ 0 : Nat} := refl` all checked, and emit printed `:refl`. Proof variables were already refused at use, and evidence definitions cannot be used in run, so without `refl` no run term builds a proof and none reaches emitted code. A proof passed to a run function is an erased argument, checked in spec. An absurd branch may still have an identity type, since it never runs.

A run definition has a run type, used or not. `def e : run {0 ≡ 0 : Nat}` was accepted, and refused only where another run term used `e`. It is refused at its type now. This does not replace the `refl` rule: `def g : run Nat := f refl` has a run type.

### Checker

- `⇐-refl` in `Check` and `Judgement` takes `eqMode m run ≡ false`; `Check.check′` refuses `refl` in run with `no promotion: refl in run mode`. `Soundness.check-sound` follows the new branch, and `Wall.no-run-rfl` states that `refl` has no run derivation. Then `Muro.Check`.
- `Check.runDecl`: `checkDef` reads a run definition's type with `isRunType`, under the `type` tag. `Soundness.checkDef-sound` takes the `checkTy` part of that step. Then `Muro.Check.run_decl`.

### Examples

- `vec.muro`: `lookup` passed `refl` to the inner match at runtime (the convoy pattern). `vhead` and `vtail` match a `Vec A suc(m)` with a motive that computes from the index, `Vec A (pred k)`, and `lookup` recurses on `vtail`. `inj-suc` stays in the prelude. `agda/Muro/ExampleVec.agda` follows.

### Manual

- The wall: `refl` in run, and the type of a run definition. Indexed data: a motive that computes from the index; the equation in the motive is for proofs. Examples: `vec.muro`.

### Package

- Version 0.16.19.

## 0.16.18

A definition naming a type is that type inside a run type. The run-type test reduced the type to weak head normal form once and read the rest as written, so the codomain of `Π (r : R) → R` with `def R : spec Type := Nat` was the definition `R`, not `Nat`, and `inc : run Π (r : R) → R` was refused in run with `definition inc has a spec type`. Each Π codomain, product side, and ν body is now reduced before it is read. An identity type is still refused, under a name or not.

### Checker

- `Check.isRunType` with `isRunTypeN`, fuel-indexed like `isCopy`. Soundness reads only its verdict, and `var-run` and `⇒-def` have no run-type premise, so no proof changes. Then `Muro.Check.run_ty`.

### Manual

- Terms: the run-type rule, which the manual did not state.

### Package

- Version 0.16.18.

## 0.16.17

Conversion unfolds two calls of the same definition when their arguments differ. The congruence step compares the arguments of `f a₁ … aₙ` and `f b₁ … bₙ` when `a₁` and `b₁` are not constructor-headed; a failure there was final. A definition with a type parameter first and a `match` on a later argument (`g R n k`, matching on `n`) then never unfolded against itself: `{g Nat (suc 0) k ≡ g Nat 0 k : Nat}` was refused although both sides reduce to `k`. A failed congruence now falls back to weak head normal form, as a congruence that does not apply already did.

A file reached by two imports is loaded once. A library file that imports `nat.muro`, imported next to `nat.muro` itself, was refused with `duplicate name` for every name in `nat.muro`. Two different declarations of one name are still refused, with both sites.

`Type`, `Nat`, `Unit`, `Empty`, `refl`, `tt`, `suc`, `match`, `matchEmpty`, and `rewrite` are keywords only as whole words, as the other keywords already were. `successor`, `reflect`, `ttl`, and `Natural` are names; `successor-value` was read as `suc` applied to `cessor-value`. `->` after a keyword ends it, so `Nat->Nat` is still an arrow.

### Checker

- `Check.convStuck`: the argumentwise comparison `orElse` `convWhnf` (`_orElse_` in `Muro.Base`). `Soundness.Conv.convStuck-sound` covers the fallback with `convWhnf-sound`. Then `Muro.Check.stuck_cong`.

### Import

- `Muro.Load`: an entry from the same file and position as one already in scope is the same entry.

### Parser

- Every keyword is matched with `word_kw?`.

### Manual

- Identity: the order of conversion. Extending: the checklist line. Terms: a file reached by two imports.

### Package

- Version 0.16.17.

## 0.16.16

Elixir emit of a definition used as a value. A reference given fewer arguments than its type has Πs is a curried closure over the rest, the given arguments evaluated once and erased ones dropped: `tabulate ident` passes `fn y -> ident(y) end`, where it emitted `ident()`, and `map (plus 2) xs` passes a closure, where it emitted `plus(2)`. A reference given more arguments applies the result with `.()`. A body with fewer λs than its type has Πs (`def adder : … := plus`) is applied to the binders it does not name, where it ignored them. A head that is not a name or a call is parenthesized before it is applied. The checker is unchanged; these programs checked before and emitted code that did not compile. C emit still refuses them (`c:lambda`).

### Emit

- `Muro.Emit`: `emit_ref`, `apply_rest`, `eta_body`.

### Manual

- Emit: functions as values.
- Examples: `higher_order.muro`.

### Package

- Version 0.16.16.

## 0.16.15

A `ν` block with a name other than `Stream` declares a family over its indices: `ν Dom (f : Stream Nat) (g : Stream Nat) : Type where uncons : Dom f g → Le (head f) (head g) × Dom (tail f) (tail g)`. The family is the spec definition whose body is `ν Dom. λ f g → …`, the encoding `Always` and `~` already have. An `unfold` checks the head obligation and a proof of the same family at the tail; `uncons` reads the pair back. The body is a product, the family strictly positive in it and applied to all its indices (a body that is not a product is refused with `ν body is not a product`, in both checkers); a family takes at least one index and as many as it needs. Declared families are checked by `Muro.Check` and the Agda checker and are outside ⊢, as Stream, `Always`, and `~` are.

A definition whose type is a ν need not be an `unfold`: `def nats : run Stream Nat := tabulate ident` checks. Such a body may not call its own block. The type is reduced first, so a ν reached through a definition (`Dom s t`) is held to the same rule.

### Checker

- `Check.nuKind` takes a telescope of any length (it stopped at two). `Check.nuBodyProd` asks that a ν body be a product under its telescope. `Check.checkNu` reduces the type, accepts a family applied to any number of indices, and refuses a non-unfold body only when it calls its own block. `agda/Muro/ExampleFamily.agda` checks a three-index family and a ν-typed alias by `refl`. Then `Muro.Check` (`telescope`, `check_nu`, `nu_type?`) and the parser (`parse_nu_family`).

### Manual

- Streams: declared families; the productivity rule for a ν-typed definition; a Stream seed is affine, a Nat seed may be `+`.
- Grammar: the `ν` production.
- Limits, For agents: user-declared ν families removed from what is missing; ν families named among what ⊢ does not cover.
- Examples: `dominance.muro`.

### Package

- Version 0.16.15.

## 0.16.14

The predecessor bound by a `match` on `Nat` has the quantity of the scrutinee when the scrutinee is a variable. Under `(+ n : Nat)`, `match n` binds a reusable predecessor, and `plus p p` checks in the `suc p` branch. Under an affine variable, or a computed scrutinee, the predecessor is affine as before. A reusable number was free to copy, and so is the number under its `suc`.

### Kernel

- `Env.predQty`, `Judgement.⇒-mNat`, `Typing.t-mNat` (any quantity on the predecessor; `≤ᵐ-modeFor` for the ι step), `Check.infer′`, `Soundness`. Agda first, then `Muro.Check`.

### Manual

- Terms: the predecessor's quantity.
- Data: a `match` on `Nat` reads the scrutinee's quantity for the predecessor.

### Package

- Version 0.16.14.

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

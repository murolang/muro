---
title: Choreography
slug: choreography
order: 25
summary: A global type, projected to the binary session each pair of roles follows.
---

# Choreography

A `choreography` declaration names a set of roles and one global type for their whole interaction. Projection gives each ordered pair of roles a binary session. The choreography is spec. It adds nothing to a term, and the term emitters skip it. A local session names one of those projections, and a process conforms to that session the way it conforms to any other.

The global type also keeps the order between pairs that projection drops. A `prefix` can state that a list of interactions is a legal prefix of the choreography, and `--backend fsm` emits a monitor that checks a recorded run of the whole choreography. Both follow [the written order](#the-written-order). A family can run the choreography once per key: [A family of a choreography](#a-family-of-a-choreography).

```
choreography <name>
  roles <role> [shared], <role> [shared], ...
  <global>
```

`choreography` is a keyword only when a name follows. `def choreography : run Nat := 0` and a constructor `choreography : Box` stay definitions. `roles` and `chooses` are keywords only inside the body. `shared` is a mark only right after a role in the `roles` list. `roles a, shared` followed by `shared -> a : x` is a role named `shared`. There is no `:=` after the name. Whitespace does not structure the body.

A global type is a sequence of messages, and it may end in one choice. A choice ends the sequence: each continuation is a branch. A message is one role sending to another:

```
coordinator -> alice : prepare
coordinator -> alice : prepare Nat
```

`→` is the same arrow. The label is a name. The payload is optional and defaults to `Unit`. It is the type a `send` writes, and it does not bind a name. `prepare Nat` carries `Nat`. `prepare` carries `Unit`. A payload argument stops before a token that begins something else. The words are `def`, `data`, `session`, `conform`, `prefix`, `meet`, `place`, `scheme`, `move`, `endpoint`, `read`, `talk`, `choreography`, `seat`, `link`, `relay`, `import`, `param`, `axiom`, `where`, `nu`, `ν`, `end`, `send`, `recv`, `choose`, `branch`, `rec`, `case`, `on`, `done`, `stop`, `put`, `get`, `pick0`, `pick1`, `cover`, `over`, `say`, and `offer`. `temporal <name> :`, `family <name> :`, and `repr <name> :=` stop as well. A name followed by `->`, `→`, `chooses`, or `:` is the next interaction or a branch label, not an argument. `)` and `}` stop, and `end` closes a choice. Parentheses group a payload that would otherwise look like one (`(Reply)`, `(Maybe (List Nat))`). `Maybe Nat` is a payload. The wrong number of arguments is the session refusal `<name> takes <n> arguments, given <k>`, and one parameter is `argument`.

A choice is one role selecting a labelled branch. Two or more branches are required.

```
coordinator chooses
  commit: coordinator -> alice : commit
          coordinator -> bob : commit
  abort: coordinator -> alice : abort
         coordinator -> bob : abort
```

A nested choice that is not the last branch is closed with `end`, so the next label belongs to the outer choice. `end` written immediately after a branch's colon is the empty global type. `end ->` is a role named `end` sending, and `end:` is a branch label. Neither of those closes the choice.

```
a chooses
  go: b chooses
    left: a -> b : x
    right: b -> a : y
  end
  stop: a -> b : z
```

`examples/two-phase-commit.muro` is the worked book, and `mix muro.check` accepts it.

## Projection

Projection is pairwise. The judgment `g ↾ r / s ≡ L` is the binary session role `r` runs with role `s`. The projection of the choreography onto a role is that family of sessions, one for each other role. `L` is a session in the existing vocabulary: `end`, `send`, `recv`, `choose`, `branch`. The label selects a branch. It is not part of the session.

A message from `a` to `b` carrying `T` is `send T` on the pair `(a, b)` and `recv T` on `(b, a)`. Any other pair keeps the continuation. A role does not interact with itself.

A choice by `p` is `choose` on `p`'s side of a pair and `branch` on the other side. That choice is inserted even when every arm projects to the same session. More than two branches nest to the right: three arms `L`, `M`, `R` are `choose L (choose M R)` for the chooser and `branch L (branch M R)` for the other end.

A role that is not the chooser, and is not the other end of that choice, must project to the same session in every branch. That is plain merge. The session is that common projection. When two branches differ, projection is refused. A role that was told the choice and then behaves differently toward a third party is refused on that third pair: the merge does not keep a choice the third party was not offered.

A pair that never interacts projects to `end`.

`project` decides the judgment. It is sound and complete: the function returns a session exactly when `g ↾ r / s ≡ L` derives it (`project-sound`, `project-complete` in `agda/Muro/Choreo.agda`). For every pair of roles, when the projection of `g` onto `r` with `s` is `S`, the projection onto `s` with `r` is `dual S` (`pairwise-dual`). The pair that never interacts is the case where both sides are `end`. The module is checked under `--safe`. The Elixir checker follows that function (`lib/muro/choreo.ex`).

`session name := seen role with role in choreography` is that projection. The form is the one a talk already uses. The name may be written before the choreography. A name that is neither a talk nor a choreography is `unknown talk <name>`.

The projection is a session in the existing vocabulary, so `--backend fsm` emits it as a session child with `init`, `send`, `recv`, `expected`, `done?`, and `check_trace`, and the C and JavaScript session images step it the same way. A `seen` of a talk is still `seen is not a state machine`. See [State machines](fsm.md#a-choreography).

## two-phase commit

The coordinator asks alice and bob to prepare, collects a vote from each, and then chooses commit or abort. Both arms send one message to alice and one to bob.

```
choreography two-phase-commit
  roles coordinator, alice, bob
  coordinator -> alice : prepare
  coordinator -> bob : prepare
  alice -> coordinator : vote
  bob -> coordinator : vote
  coordinator chooses
    commit: coordinator -> alice : commit
            coordinator -> bob : commit
    abort: coordinator -> alice : abort
           coordinator -> bob : abort
```

The two arms have the same shape, and the choice stays, because the coordinator is an end of each pair:

```
choreography two-phase-commit: coordinator with alice = send Unit (recv Unit (choose (send Unit end) (send Unit end)))
choreography two-phase-commit: coordinator with bob = send Unit (recv Unit (choose (send Unit end) (send Unit end)))
choreography two-phase-commit: alice with coordinator = recv Unit (send Unit (branch (recv Unit end) (recv Unit end)))
choreography two-phase-commit: alice with bob = end
choreography two-phase-commit: bob with coordinator = recv Unit (send Unit (branch (recv Unit end) (recv Unit end)))
choreography two-phase-commit: bob with alice = end
```

Alice and bob never send to each other, so that pair is `end`. `session ca := seen coordinator with alice in two-phase-commit` is the first of those lines. The coordinator's process picks one arm (`pick0` or `pick1`). Alice's process offers both (`cover`). `kept` is the run definition in the same file. `mix muro.emit examples/two-phase-commit.muro` emits `kept`.

A label-only difference merges. `b -> c : go` and `b -> c : stop`, both carrying `Unit`, are `send Unit end` for `b` with `c`. The chooser's session with `b` is still `choose end end`.

## The written order

A choreography fixes one order: the order it is written in. The next legal interaction is the next one written. When the next thing written is a choice, the next legal event is that choice, one of its labels, taken by the chooser. After that label, the next legal interaction is the first one written in that branch. At `end` nothing is legal.

This holds even when two interactions share no role. In

```
a -> b : x
c -> d : y
```

`a -> b : x` comes first, and `c -> d : y` before it is refused. The written order is not the set of every interleaving of independent messages.

- It is exact. `expected/1` on the monitor names one next interaction, or the labels of one choice, never a set of them, and a refusal names what was expected.
- It keeps a rule between pairs that never meet. In the release of `examples/release-plan.muro`, `release` is in every message, so any order that respects each role would put `front` before `worker` there too. With `front` and `worker` deployed by two different roles, only the written order would.
- A prefix and a monitor agree on one list. The judgment and the machine are the same walk (`Muro.Choreo.prefix/3`, `accept` in `agda/Muro/ChoreoPrefix.agda`).

A book that wants two interactions in either order writes a choice, or two choreographies.

## A legal prefix

`prefix name : <choreography> :=` takes a list of interactions in the choreography's own syntax and says the list is a legal prefix of it in the written order. The declaration is evidence. The emitters omit it.

```
prefix front-first : plan :=
  release -> front : deploy
  front -> release : deployed
  release -> worker : deploy
```

A message is written as the choreography writes it: `a -> b : label`, then the payload type when it is not `Unit`. A message written without a payload is `Unit`, so `release -> worker : deploy` and `release -> worker : deploy Nat` are different moves. A choice is `p chooses label`. The empty list is a legal prefix. The position is the start: `at start` is accepted, and any other position is `at <pos> is not a position of <choreography>`. A name that is a session stays a session, and a choreography move against a session is `<session> is not a choreography`.

The judgment is `GLeg` in `agda/Muro/ChoreoPrefix.agda`. `accept` decides it, and it is sound and complete. The Elixir checker follows that function.

A refusal names the prefix and the move. The line and column are the move. From the second move on, the sentence is wrapped as on a session: `move N is not a legal continuation of <choreography> at start: …`.

```
not enabled at start, expected release -> front : deploy, wrote release -> worker : deploy
```

```
move 2 is not a legal continuation of plan at start: not enabled at start, expected front -> release : deployed, wrote release -> worker : deploy
```

```
move 5 is not a legal continuation of plan at start: not enabled at start, expected release chooses keep or undo, wrote release chooses maybe
```

A move after the end expects `end`. A role the choreography does not declare is `unknown role <name>`. A session move such as `send 1` is not enabled.

## A monitor

`--backend fsm` emits one child per choreography that checks. It is stepped with global events: `step(state, from, to, label)` for a message whose payload is `Unit`, `step(state, from, to, label, value)` for any message, and `choose(state, role, label)` for a choice. `expected/1` names the next interaction, `{:message, from, to, label, type}`, or the labels of a choice, `{:choose, role, [label, ...]}`, and it is `:done` at the end. `check_trace/1` replays a list of those events, and `check_trace(trace, complete: true)` also asks for the end. The page is [State machines](fsm.md#a-choreography).

## A family of a choreography

A family can range over a choreography. Each key runs one instance of the global type, any number of keys at once, independent of each other:

```
choreography plan
  roles registry shared, release shared, front, worker
  release -> registry : publish
  registry -> release : published
  release -> front : deploy
  front -> release : deployed
  release -> worker : deploy
  worker -> release : deployed
  release chooses
    keep: release -> front : keep
          release -> worker : keep
    undo: release -> worker : undo
          release -> front : undo

family rollout : plan per key
```

`examples/release-rollout.muro` is that book. There is no kind and no hold rule: the choreography is the plan of every key. The checker prints `family rollout: plan per key`.

A role marked `shared` is one party for every key: the registry that publishes a version once, the person running the release. The other roles are each key's own: that site's `front` and `worker`.

- **The shared preamble.** A message between two shared roles, or a choice by a shared role, written before any other step, is in the shared preamble. The preamble happens once, before any key steps. A choice in the preamble picks the branch for every key. In `plan` the preamble is `release -> registry : publish` then `registry -> release : published`.
- **Per key.** Every step after the preamble is taken per key. A message with at least one role that is not shared is a step of that key. `release -> front : deploy` is a step of each site, even though `release` is shared. A choice by a shared role after a per-key step is that key's choice: `release chooses keep or undo` is decided for each site.
- **A message between shared roles after a per-key step is refused**, on the choreography: `release -> registry : late is between shared roles after a per-key step; a message between shared roles belongs in the shared preamble`. Such a message would couple every key to every other. It belongs in the preamble.

`shared` changes nothing else. A choreography with marks and no family checks, projects, and emits its [monitor](#a-monitor) as it does without them. A choreography with no shared role has no preamble, and every key starts at once.

The family is refused when:

- the name is not a choreography and not a meeting: `unknown choreography <name>`;
- the name is a meeting: `<name> is a meeting: a family of a meeting names its kind, per key of <Kind>`;
- `per key of <Kind>` names a choreography: `<name> is a choreography: a family of a choreography is per key, with no kind and no hold rules`;
- a hold rule follows: `a family of a choreography has no hold rules`; `may redeliver` follows: `may redeliver is a mark on a family of a meeting`;
- the choreography does not check: `skipped because <name> does not check`, and the choreography's own refusal, including two roles or two labels that spell one Elixir atom, is printed on the choreography;
- every role is shared: `every role of <name> is shared, so no step runs per key`.

A contract names a family of a meeting. A contract on a family of a choreography is `<family> ranges over a choreography: a contract names a family of a meeting`.

A temporal formula may name the family, `forall (k : key)` with atoms that name an interaction or a choice label of the choreography: [Temporal](temporal.md#a-family-of-a-choreography). `--backend fsm` emits one dispatcher for the family: the monitor, replicated per key, behind the shared preamble. See [State machines](fsm.md#a-family-of-a-choreography).

## A refusal

The position is the choreography. Several failures are joined with `; `.

- A role written twice: `duplicate role <name>`.
- A name in the global type that is not a role: `unknown role <name>`.
- A message from a role to itself, or a projection of a role with itself: `self-interaction <name>`. One self-send is one error.
- A branch label written twice in one choice: `duplicate branch <label>`.
- Two roles that reach one atom spelling, `roles front-end, front_end`: `roles front-end and front_end spell one Elixir atom`. Two labels of one choice that do, `roll-out` and `roll_out`: `branches roll-out and roll_out spell one Elixir atom`. A role and a label are atoms in the [monitor](fsm.md#a-choreography), spelled as in [Emit](emit.md), and two of them on one atom would be one role, or one branch, there.
- A choice with fewer than two branches: `a choice has two branches`.
- A message between two shared roles after a per-key step: `<from> -> <to> : <label> is between shared roles after a per-key step; a message between shared roles belongs in the shared preamble`. See [A family of a choreography](#a-family-of-a-choreography).
- Plain merge fails: `<role>: branches <label> and <label> disagree`. Three or more labels are joined with commas: `branches l, m, r disagree`. The role is the one being projected. Both ends of that pair are reported.
- A payload that is not a session payload is refused with that session error. The wrong number of arguments is `<name> takes <n> arguments, given <k>`. One parameter is `argument`.

An inner choice that fails is reported at that choice. It is not rewritten as a failure of the choice wrapped around it.

`test/fixtures/choreo_untold.muro` is the refused book. The coordinator chooses, the commit arm is `alice -> bob : go`, and the abort arm is `bob -> alice : stop`. Alice and bob are not told which arm was taken, and the two arms are not the same session:

```
alice: branches commit and abort disagree
bob: branches commit and abort disagree
```

The coordinator's session with alice is `choose end end`. The chooser is an end of that pair even though both arms skip it, so the refusal does not name the coordinator.

## What is not in this declaration

- Global progress, or deadlock freedom, for more than two roles. Binary duality gives it for a tree of interactions, and that argument is not made here.
- Full merge. Plain merge demands the same session in every branch. A participant who was told the choice and then takes a different session toward someone else is refused.
- Recursion in a global type. A session may still be `rec` on its own. The choreography does not write one.
- Multiparty execution. Each projection is a binary session, and a meeting is still two processes. The monitor checks a recorded run. It does not run the roles. A family of a choreography is the same monitor per key.
- Any order of two interactions other than the written one. See [The written order](#the-written-order).
- A role's own order across its peers as a child of its own. A host checks one role's side against the monitor's events for that role.
- A temporal formula over a choreography itself. `temporal name : plan := …` names a meeting or a family, and a choreography is not one. A family of the choreography is: [Temporal](temporal.md#a-family-of-a-choreography).
- A message between shared roles in the middle of a rollout. The shared roles meet in the preamble, before any key steps.
- Fairness between keys. A run of a family steps each key to its end. Nothing here orders one key before another.
- Placing the roles of one choreography at more than one place. A seat is still a party of a talk.

## What the checker prints

After `Muro v…`, after any temporal lines, and before any axiom-dependency line and `All terms check. Evidence never becomes a run.`, one line per ordered pair of distinct roles, in the order the roles were written:

```
choreography ping: a with b = send Nat end
choreography ping: b with a = recv Nat end
```

A book with no choreography prints what it printed before.

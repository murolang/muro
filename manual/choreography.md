---
title: Choreography
slug: choreography
order: 25
summary: A global type, projected to the binary session each pair of roles follows.
---

# Choreography

A `choreography` declaration names a set of roles and one global type for their whole interaction. Projection gives each ordered pair of roles a binary session. The choreography is spec. It adds nothing to a term, and the emitters skip it. A local session names one of those projections, and a process conforms to that session the way it conforms to any other.

```
choreography <name>
  roles <role>, <role>, ...
  <global>
```

`choreography` is a keyword only when a name follows. `def choreography : run Nat := 0` and a constructor `choreography : Box` stay definitions. `roles` and `chooses` are keywords only inside the body. There is no `:=` after the name. Whitespace does not structure the body.

A global type is a sequence of messages, and it may end in one choice. A choice ends the sequence: each continuation is a branch. A message is one role sending to another:

```
coordinator -> alice : prepare
coordinator -> alice : prepare Nat
```

`→` is the same arrow. The label is a name. The payload is optional and defaults to `Unit`. It is the type a `send` writes, and it does not bind a name. `prepare Nat` carries `Nat`. `prepare` carries `Unit`. A name followed by `->`, `chooses`, `:`, or the next declaration is the next interaction, not a payload. Parentheses group a payload that would otherwise look like one. `Maybe Nat` is a payload.

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

## A refusal

The position is the choreography. Several failures are joined with `; `.

- A role written twice: `duplicate role <name>`.
- A name in the global type that is not a role: `unknown role <name>`.
- A message from a role to itself, or a projection of a role with itself: `self-interaction <name>`. One self-send is one error.
- A branch label written twice in one choice: `duplicate branch <label>`.
- A choice with fewer than two branches: `a choice has two branches`.
- Plain merge fails: `<role>: branches <label> and <label> disagree`. Three or more labels are joined with commas: `branches l, m, r disagree`. The role is the one being projected. Both ends of that pair are reported.
- A payload that is not a session payload is refused with that session error.

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
- Multiparty execution. Each projection is a binary session, and a meeting is still two processes.
- Placing the roles of one choreography at more than one place. A seat is still a party of a talk.

## What the checker prints

After `Muro v…`, after any temporal lines, and before `All terms check. Evidence never becomes a run.`, one line per ordered pair of distinct roles, in the order the roles were written:

```
choreography ping: a with b = send Nat end
choreography ping: b with a = recv Nat end
```

A book with no choreography prints what it printed before.

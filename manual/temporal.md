---
title: Temporal
slug: temporal
order: 24
summary: always, eventually, and leads_to on one buffered meeting.
---

# Temporal

A `temporal` declaration states one linear-time property of one buffered meeting. It is evidence. It adds nothing to a term, and the emitters skip it. The Zig file is the same as the C and Rust files: the declaration is not in it. The meeting stays its own entry and is checked once. The configuration graph is explored once, and every temporal declaration of that meeting reads it.

```
temporal <name> : <meeting> := <formula>
```

`temporal` is a keyword only in the form `temporal name :`. `def temporal : run Nat := 0` and a constructor `temporal : Box` stay definitions. The meeting is one written with `buffer N`. A rendezvous meeting is refused with `temporal needs a buffered meeting`.

The formulas are `always`, `eventually`, and `leads_to`. A proposition is a predicate of one configuration: the two block pointers, the two queues, and the binder slots. It does not contain a temporal operator, a term, or a `run` definition.

`examples/temporal.muro` is the worked book. Each declaration below is that file, and `mix muro.check` accepts it.

## always

`always P` holds when `P` is true in every configuration of every run, including a configuration where the meeting has finished.

```muro
temporal echo-returns-zero : echo-wire :=
  always (echo-b at first put implies echo-b has n = 0)
```

`echo-b at first put` is the first `put` in `echo-b`, counted in source order. `echo-b has n = 0` is the slot of `n` holding `0`. A slot that is not yet bound makes the atom false. The checker prints:

```
temporal echo-returns-zero: holds in 8 reachable states, 8 transitions
```

On the finite meeting, a finished client has seen `rst`:

```muro
temporal ctl-seen : inflight :=
  always (client done implies client has c is rst)
```

`client has c is rst` is the constructor case of the slot. `inflight` finishes, so every run ends at that finished configuration.

```
temporal ctl-seen: holds in 9 reachable states, 11 transitions
```

## eventually

`eventually P` holds when every run reaches a configuration where `P` is true. The first configuration counts, and so does the finished one.

```muro
temporal echo-answers : echo-wire := eventually (echo-a has m = 0)
```

```
temporal echo-answers: holds in 8 reachable states, 8 transitions
```

## leads_to

`P leads_to Q` holds when, on every run, every configuration where `P` holds is followed, then or later, by a configuration where `Q` holds. `Q` at the same configuration satisfies it.

```muro
temporal echo-answered : echo-wire :=
  (inbox echo-b head 0) leads_to (inbox echo-a head 0)
```

`inbox echo-b` is the queue of messages `echo-a` has sent and `echo-b` has not taken. `head 0` is the oldest message. The same declaration written as `always ((inbox echo-b head 0) implies eventually (inbox echo-a head 0))` is the same formula, and it is printed back as `leads_to`.

```
temporal echo-answered: holds in 8 reachable states, 8 transitions
```

`true leads_to Q` says `Q` holds infinitely often: at every position, `Q` holds then or later.

A quantifier `forall (x : T). formula` stands in front of one of these forms. `T` is `Bit` or a declared data type whose constructors are all nullary. The checker decides one formula per constructor. `forall (c : Note). always true` on `echo-wire` holds in the same 8 states and the same 8 transitions. A quantifier over `Nat`, a pair, a record, a vector, or a constructor with a field is refused.

## The state

The state is fixed by the meeting. The buffer bound is `N`. The alphabet is finite: the numerals, bits, and nullary constructors the two processes put. A slot is unbound or holds one of those literals. A configuration is two block pointers, two queues of at most `N` messages, and one slot per binder.

The size of that universe is `|codeL| · |codeR| · Q² · (|alpha| + 1)^(slotsL + slotsR)`, where `Q` is the number of queues of length at most `N` over an alphabet extended by the two labels `pick0` and `pick1`. Reachable configurations are fewer: each process has one action enabled, and the only choice is which side moves. The check walks the reachable graph once. Every declaration of that meeting reads the same graph. Growing `buffer N`, or the number of distinct literals, grows that graph exponentially. That the set is finite is why the walk ends. It is not a proof of `eventually` or `leads_to`: a finite graph still has infinite runs, and a cycle in the region that misses the goal is a run that misses the formula.

A pair, a record, a vector, a constructor with a field, and a computed `put` are `payload outside the temporal fragment`. The meeting that carries them can still check. The temporal declaration cannot.

## Runs

A step is one side moving. When both sides can move, both steps are available, left before right. A finished configuration, both blocks halted and both queues empty, steps to itself. The trace prints that stutter as `the meeting has finished`. Every run the formula talks about is infinite: a meeting that finishes stays finished, and a meeting that continues takes another step. `always` needs the proposition at the finished configuration. `eventually` accepts it there. `leads_to` needs its conclusion by that configuration. The finish step is a cycle of one transition, so a liveness refusal may be that self-loop after the path that reached it.

A meeting that does not check is not given a temporal verdict. The declaration is `skipped because <meeting> does not check`.

## A party may stop

A meeting that marks a party `may fail` adds a step on which that party stops, at every configuration where it has not halted. The party stops before `end`, and before it has halted. A party at `done` or `stop` has no later death step. A party that has already stopped has no second one. The stopped party takes no further step. A message it has not placed on the queue is lost. A message already on the queue toward the survivor may arrive, and it may be dropped. Both runs are in the graph. A `put` from the survivor to a stopped party is consumed and is not enqueued. When the survivor is at a receive, the peer has stopped, and the queue from that peer is empty, the failure arm is the step. The OTP image applies a message that reached the mailbox before `:DOWN`. It does not take the drop run. The graph still contains it.

`task dead` holds when that party's pointer is this early stop. It does not hold when the party wrote `done`, and it does not hold when the party wrote `stop`. `task done` is the `done` block. `task stopped` is the `stop` block. `dead` is a keyword only in that atom. A definition or a process named `dead` stays a name.

`always`, `eventually`, and `leads_to` are decided over those runs too. A formula that holds on the report path and fails when the peer stops is refused, and the refusal names that run.

`examples/may-fail-free.muro` releases the slot on the report and on the failure arm. `(server at first get) leads_to (server done)` holds in 5 reachable states, 6 transitions. On that same graph `(task dead) leads_to (server done)`: the crash is followed by the failure arm. `(task dead) implies (server done)` does not hold at the configuration where the task has just stopped and the server is still at the receive. `examples/may-fail-hold.muro` writes `fail stop`. The same formula fails after `task died, server fail`, and then the meeting has finished. `examples/may-fail-missing.muro` has no failure arm, so the meeting is refused and the declaration is not given a verdict. `examples/may-fail-control.muro` does not mark the task. The same formula holds in 3 reachable states, 3 transitions, on the report path alone, and `task dead` is false on every configuration. `examples/may-fail-send.muro` sends before the receive. The send has no failure arm. The formula holds in 12 reachable states, 16 transitions.

A meeting that does not mark a party keeps the graph this page has described so far. `examples/temporal.muro` keeps its counts. The development in `agda/Muro/Temporal.agda` is that graph. The crash step, the drop step, and `role dead` are decided by the Elixir checker. They are not in `agda/Muro/Temporal.agda` or `agda/Muro/AsyncRec.agda`, and this half does not port them there.

## Fairness

There is no fairness filter and no `under fair` clause. `Satisfies` quantifies over every infinite run, including a run that finishes and then stutters. A stretch of consecutive steps of one side has length at most `Φ` of that side, where `Φ` of the left at `c` is `(cap ∸ |l2r|) + |r2l|` and `Φ` of the right swaps the queues (`solo-bounded`). On a run that never finishes, the left side moves infinitely often and the right side moves infinitely often (`every-run-fair`). Those lemmas describe this graph. They are not a premise the formula may assume. The statements are in [Limits](limits.md#what-is-proved-and-what-is-not). A fairness clause would be a parse error.

## A refusal

The position is the declaration. The formula is printed in surface syntax. The meeting names the two processes and the sessions they follow. A safety refusal is the shortest path, then the configuration:

```
drained: always (inbox hear-server is empty) fails in spin-wire (spin-client : spin, hear-server : hear) after spin-client put bytes: spin-client: put bytes; hear-server: get (f : Frame); l2r: [bytes]; r2l: []
```

A liveness refusal is the path to the cycle, then the cycle after `then forever`. The cycle is not copied onto that path. When the cycle begins at the start, there is no `after` list. `spin-wire` in `examples/async-meetings.muro` sends `bytes` on every turn, so `hear-server` does not finish. The path that enters the cycle and the cycle itself name the same two steps:

```
ends: eventually (hear-server done) fails in spin-wire (spin-client : spin, hear-server : hear) after spin-client put bytes, hear-server arm bytes; then forever: spin-client put bytes, hear-server arm bytes
```

A meeting that reaches `done` and then stutters refuses `eventually false` with `then forever: the meeting has finished`. A step is `put` with its literal, `get` with its binder, or `arm` with the constructor the match took. The configuration after a safety refusal prints the block, so a match still shows `get (f : Frame)` there.

## What the checker prints

After `Muro v…`, and before `All terms check. Evidence never becomes a run.`, one line per temporal declaration, in book order:

```
temporal echo-answered: holds in 8 reachable states, 8 transitions
```

The first count is the number of distinct configurations reachable from the start of that meeting. The second is the number of entries in the successor table of that same graph: a left step, a right step, and the finish self-loop at a finished configuration. It is not the number of breadth-first parent links. Declarations of one meeting print the same pair, because the graph is built once. A refusal replaces that line. A book with no temporal declaration prints the lines it printed before this page existed. A `conforms to` line from an imported package stays after the success sentence. `--fuel` does not change a temporal verdict. The refusals listed in [Limits](limits.md) are unchanged.

Emit of a book is unchanged by appending a declaration whose meeting checks. Elixir, the state-machine backend, C, Rust, and assembly print the same programs. The ExUnit backend embeds the book hash in `@muro_book`, so that one line changes with the book bytes and the suite body does not. A committed module's header records the same hash, and `mix muro.gen --check` reports the target stale until `mix muro.gen` rewrites the header. That is the rule for any edit of a book.

On a meeting the checker has accepted, `Decide.check` accepts a fragment formula exactly when every infinite run from the start satisfies it (`Satisfies`, under `NoStuck`; `check-sound`, `check-complete`). `always` is the proposition at every position. `eventually` is some later or present position on every run. `leads_to` is that implication at every position. A refusal is `Valid × ¬ Satisfies`: the breadth-first prefix, or the recorded cycle unrolled from the start, is a run that misses the formula. The same verdict is the source meeting's when `Frag` holds of both processes, both are `echoOk` and `muOk`, `graphOf` is `gok`, and `initS` is `just` (`check-yes`, `check-no`). `cex-source` is that run read at the source. A source step is a step of the graph (`sim-fwd`). Under the cursor `Hold`, a graph step other than the stutter is the source step (`sim-bwd`), and the source configuration is final exactly when the projected configuration is (`final-iff`). `SourceShape` says every source-reachable view is `Shape`. It holds exactly when `NoStuck` does (`source-safe-iff`), and `Satisfies` holds exactly when `SourceSatisfies` does (`transfer`), for `always`, `eventually`, and `leads_to`, under those hypotheses. `SourceSafe`, final or some step, is the weaker predicate. `inj-fwd` and `inj-bwd` in `Temporal/Finite.agda` are the two directions of an embedded finite step. `inj-bwd` takes `Safe` and a step other than the stutter. `safe→nostuck` says a safe finite meeting is `NoStuck` under `graphOf ≡ gok`, `initS`, and `echoOk`. `muOk` of the injection holds whenever `Frag` does. A meeting that marks a party `may fail` adds the steps in [A party may stop](#a-party-may-stop). Those steps, and `role dead`, are decided in Elixir. They must not be ported into Agda in this half, and they must not be fixed by weakening an Agda theorem. These theorems stay the meeting that does not mark a party.

The propositions, the refusals, and the theorems are listed in [Limits](limits.md). The grammar is in [Grammar](grammar.md).

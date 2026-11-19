---
title: Temporal
slug: temporal
order: 24
summary: always, eventually, and leads_to on one buffered meeting, and a family per key of a closed kind.
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

## A keyed family

A family is spec. It names one buffered meeting and one closed kind, and one rule for each constructor of that kind. The state machine emits one dispatcher for a family that checks. `resolved` drops the instance. The family child has `finish`. `:resolve` drops the instance. `:rerun` keeps it unresolved, and a later `:resolve` drops it. There is no bound on reruns. Each end of the meeting has `finish` too. When one family uses that end, it is the same outcome. When two families share the end, that call names `finish` on the family child and does not resolve. The dispatcher's `check_trace` replays that end together with `arrive`, `resolved`, and `rerun`. Every other emitter skips the family. It adds nothing to a term. The dispatcher is [State machines](fsm.md#a-keyed-family).

```
family slots : slot per key of Event
  init never held
  signal held while earlier unresolved
```

`slots` is the family. `slot` is the meeting. `Event` is the kind. `init never held` opens that kind when the instance arrives. `signal held while earlier unresolved` opens it when no earlier arrived instance of its key is unresolved. An instance that has not arrived is not unresolved. A constructor with no rule is refused. There is no default rule.

The kind is a declared data type whose constructors are all nullary, the same restriction `forall` uses. `Bit` is refused as `unknown data type Bit`. A constructor with a field is `family over <name> is not a closed kind`.

The meeting is buffered, and it checks. An unknown meeting is `unknown meeting <name>`. A meeting that does not check is `skipped because <name> does not check`. A rendezvous is `family needs a buffered meeting`.

`family`, `per`, `key`, and `of` are keywords only in `family name :`. `never`, `while`, `earlier`, and `unresolved` are keywords only on a rule. `held` is a keyword on a rule and in the atom below. Outside that form they are identifiers, so `def family : run Nat := 0` and `def held : run Nat := 0` are definitions, and a constructor may be named `family`.

A retry is the same instance, run again, and it stays unresolved. The check allows one rerun, taken while the marked party has stopped and the server has not reached `done` or `stop`. The next such stop gives the instance up. Giving up counts as resolved for the rule and for `resolved`, and it is not delivered: the server did not reach `done`. A later `signal` then opens. `no-overtake` holds on that run, and the signal is still lost.

A server that has reached `stop`, with nothing left queued, stays in that meeting. The instance is unresolved. A `signal` held behind it stays held. The check does not retry out of that ending.

A second `init` of a key is never held. It opens at once, on the same meeting. The check does not add a report for it. A `signal` is held behind every earlier unresolved instance of its key that the family already knows. An unresolved `init` is one of those, and so is an earlier unresolved `signal`.

A `signal` with no earlier unresolved instance of its key opens at once. There is no `dropped` outcome. The signal runs the meeting the family names, and that run is its report. In `examples/keyed-slots.muro` the meeting still exchanges `ok`.

Arrival is one step, and it carries the creation index. The step opens the instance, or holds it. Instances of one key need not arrive in creation order. An earlier index can arrive after a later one has opened. The guarantee is the instances known when the signal opened.

The key in the check is the workflow, and the dispatcher uses that same key. The host compares it with `==`. That reading holds at least every instance the server holds, so a verdict on it is sound for the server. The dispatcher holds slightly more, across runs of one workflow. That is accepted. The check does not split a key by run.

A temporal declaration may name the family:

```
temporal no-overtake : slots :=
  forall (k : key). always ((opened k signal) implies (resolved k init))
temporal no-starve : slots :=
  forall (k : key). (held k signal) leads_to (opened k signal)
```

`no-overtake` says that every counting `init` of the key is resolved, and there may be none. A `signal` that opens before any `init` is known does not refute it. The hold line is the stronger guard. It does not say that an opened `signal` has an `init`, and it does not say that every earlier instance is resolved. `opened`, `held`, and `resolved` each take two names: a key, then a constructor. The constructor is a name written in the formula, not a bound variable, and there is no binder for one instance. `resolved k signal` is one atom for every `signal` of that key, including the `signal` that has just opened, and that `signal` is not resolved on the step it opens. The stronger rule is the one on the family line: a `signal` stays held while any earlier arrived instance of its key is unresolved, and an earlier `signal` is one of those instances.

An instance counts for `resolved` when it is known, unless some other running instance of the same key opened before this one was known. A late `init`, still running, does not refute `no-overtake` while that earlier `signal` is open. The graph contains that state. `resolved` there is not "delivered". A `signal` running while its `init` is still absent is in the graph too, and `resolved k init` holds there because no `init` counts.

`forall (k : key)` binds `k` as a key. That sort is `key` even when a data type of the same name is in the book. A `forall` over any other type is `forall over <name> is not a key`, including `Bit`, `Nat`, and the kind. The checker decides `always`, `eventually`, and `leads_to` on the family graph. `no-starve` is that `leads_to`. An ill-formed formula does not build the graph. A formula over a family that does not check is `skipped because <family> does not check`, and the formula is not walked. There is no fairness clause. A refusal is a lasso: the path to the cycle, then `then forever`, then the state that cycle returns to.

`opened`, `held`, and `resolved` written on a meeting are `<atom> names an instance of a family`. `forall (k : key)` on a meeting is `forall over key ranges over an open type` when no data type is named `key`. A key that is not bound is `unbound key <name>`. A constructor the kind does not have is `<name> is not a constructor of <kind>`. A proposition other than these atoms is `a family formula names opened, held, or resolved`.

`opened done` stays the role atom. The next word is `done`, `stopped`, `dead`, `at`, or `has`.

The worked book is `examples/keyed-slots.muro`. It writes `no-overtake` and `no-starve`. The failure arm is `done`, so a dying task resolves the instance and a held signal can open. `mix muro.check` prints

```
family slots: slot per key of Event
temporal no-overtake: holds in 171649 reachable states, 729184 transitions
temporal no-starve: holds in 171649 reachable states, 729184 transitions
```

That count is a model hypothesis, not data-independence. The script is fixed and a retry happens once. The checker builds the graph once for the family. That search is the cost of the check. Both lines are that same search. This is an Elixir check of the fixed script. It is not an Agda proof, and it is not data-independence.

The same script with `fail stop` refuses `no-starve`. The task dies, the server takes `fail stop`, and both signals of key `a` stay held. Key `b` opens, exchanges `ok`, and resolves while `a` is blocked. The family then stutters:

```
(held a signal) leads_to (opened a signal) fails in slots after a init 0 opens, a signal 1 held, a init 0 task died, a init 0 server fail stop, a signal 2 held, b init 0 opens, b init 0 task put ok, b init 0 server get (r : Report), b init 0 resolves; then forever: the family has finished: a init 0: running; a signal 1: held; a signal 2: held; b init 0: resolved
```

The words after the stutter are that cycle's state. `a signal` is held there, and the cycle does not open it. That run is the counterexample. It is the same Elixir check, not a proof.

The same book with `signal never held` in place of `signal held while earlier unresolved` is refused. Deleting the rule outright is `no rule for signal`. The shortest path is `a init 0 opens, a signal 1 opens`, and `a init 0` is still running. That `signal` is creation index 1.

The script is fixed. For each constructor, in declaration order, key `a` has one instance, or two when its rule is `held while earlier unresolved`. Key `b` has one instance of the first constructor. On this book key `a` is `init`, then `signal`, then `signal`, and key `b` is `init`. The creation index is the position in that key's script. Keys are interchangeable, and a rule reads only whether two instances have the same key. That this script stands for any number of keys and any number of events is a model hypothesis, not data-independence, stated in [Limits](limits.md#a-keyed-family). It is not a theorem. The script is not in the book. The check is the Elixir graph. It is not a theorem of `agda/Muro/Temporal.agda`, and those modules are unchanged.

## Fairness

`Satisfies`, `solo-bounded`, and `every-run-fair` cover meetings only. A keyed family is checked in Elixir only, and that check has no fairness filter.

There is no fairness filter and no `under fair` clause. `Satisfies` quantifies over every infinite run of a meeting, including a run that finishes and then stutters. A stretch of consecutive steps of one side has length at most `Φ` of that side, where `Φ` of the left at `c` is `(cap ∸ |l2r|) + |r2l|` and `Φ` of the right swaps the queues (`solo-bounded`). On a run that never finishes, the left side moves infinitely often and the right side moves infinitely often (`every-run-fair`). Those lemmas describe the meeting graph. They are not a premise the formula may assume. The statements are in [Limits](limits.md#what-is-proved-and-what-is-not). A fairness clause would be a parse error.

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

After `Muro v…`, and before `All terms check. Evidence never becomes a run.`, one line per keyed family and one line per temporal declaration, in book order:

```
family slots: slot per key of Event
temporal echo-answered: holds in 8 reachable states, 8 transitions
```

The family line names the meeting and the kind. It is not a count of states. A temporal line over a meeting counts that meeting: the distinct configurations reachable from its start, then the successor table, a left step, a right step, and the finish self-loop at a finished configuration. It is not the number of breadth-first parent links. Declarations of one meeting print the same pair, because the graph is built once. A temporal line over a family counts the family graph. That count is a model hypothesis, not data-independence: one retry, on the fixed script. The checker builds the graph once for the family, and that search is the cost of the check. The second count is that successor table: an arrival that opens or holds, a meeting step, a retry, a give-up, a resolve, and one self-loop when no instance can move. `always`, `eventually`, and `leads_to` declarations of one family print the same pair when they hold. A refusal replaces the counts, and the family line is not printed. A family liveness refusal appends the cycle state after the stutter. A book with no family and no temporal declaration prints the lines it printed before this page existed. A `conforms to` line from an imported package stays after the success sentence. `--fuel` does not change a temporal verdict. The meeting refusals listed in [Limits](limits.md) are unchanged. A family has its own list there.

Emit of a book is unchanged by appending a temporal declaration whose meeting checks. Elixir, the state-machine backend, C, Rust, and assembly print the same programs. The ExUnit backend embeds the book hash in `@muro_book`, so that one line changes with the book bytes and the suite body does not. A committed module's header records the same hash, and `mix muro.gen --check` reports the target stale until `mix muro.gen` rewrites the header. That is the rule for any edit of a book.

Appending a family leaves Elixir, C, Rust, Zig, JavaScript, assembly, OTP, `--node`, and ExUnit unchanged in that same way. The state machine emits a dispatcher beside the session children. See [State machines](fsm.md#a-keyed-family).

On a meeting the checker has accepted, `Decide.check` accepts a fragment formula exactly when every infinite run from the start satisfies it (`Satisfies`, under `NoStuck`; `check-sound`, `check-complete`). `always` is the proposition at every position. `eventually` is some later or present position on every run. `leads_to` is that implication at every position. A refusal is `Valid × ¬ Satisfies`: the breadth-first prefix, or the recorded cycle unrolled from the start, is a run that misses the formula. The same verdict is the source meeting's when `Frag` holds of both processes, both are `echoOk` and `muOk`, `graphOf` is `gok`, and `initS` is `just` (`check-yes`, `check-no`). `cex-source` is that run read at the source. A source step is a step of the graph (`sim-fwd`). Under the cursor `Hold`, a graph step other than the stutter is the source step (`sim-bwd`), and the source configuration is final exactly when the projected configuration is (`final-iff`). `SourceShape` says every source-reachable view is `Shape`. It holds exactly when `NoStuck` does (`source-safe-iff`), and `Satisfies` holds exactly when `SourceSatisfies` does (`transfer`), for `always`, `eventually`, and `leads_to`, under those hypotheses. `SourceSafe`, final or some step, is the weaker predicate. `inj-fwd` and `inj-bwd` in `Temporal/Finite.agda` are the two directions of an embedded finite step. `inj-bwd` takes `Safe` and a step other than the stutter. `safe→nostuck` says a safe finite meeting is `NoStuck` under `graphOf ≡ gok`, `initS`, and `echoOk`. `muOk` of the injection holds whenever `Frag` does. A meeting that marks a party `may fail` adds the steps in [A party may stop](#a-party-may-stop). Those steps, and `role dead`, are decided in Elixir. They must not be ported into Agda in this half, and they must not be fixed by weakening an Agda theorem. These theorems stay the meeting that does not mark a party.

The propositions, the refusals, and the theorems are listed in [Limits](limits.md). The grammar is in [Grammar](grammar.md).

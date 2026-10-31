---
title: Temporal
slug: temporal
order: 24
summary: always, eventually, and leads_to on one buffered meeting.
---

# Temporal

A `temporal` declaration states one linear-time property of one buffered meeting. It is evidence. It adds nothing to a term, and the emitters skip it. The meeting stays its own entry and is checked once, as it is today.

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
temporal echo-returns-zero: holds in 8 reachable states
```

On the finite meeting, a finished client has seen `rst`:

```muro
temporal ctl-seen : inflight :=
  always (client done implies client has c is rst)
```

`client has c is rst` is the constructor case of the slot. `inflight` finishes, so every run ends at that finished configuration.

```
temporal ctl-seen: holds in 9 reachable states
```

## eventually

`eventually P` holds when every run reaches a configuration where `P` is true. The first configuration counts, and so does the finished one.

```muro
temporal echo-answers : echo-wire := eventually (echo-a has m = 0)
```

```
temporal echo-answers: holds in 8 reachable states
```

## leads_to

`P leads_to Q` holds when, on every run, every configuration where `P` holds is followed, then or later, by a configuration where `Q` holds. `Q` at the same configuration satisfies it.

```muro
temporal echo-answered : echo-wire :=
  (inbox echo-b head 0) leads_to (inbox echo-a head 0)
```

`inbox echo-b` is the queue of messages `echo-a` has sent and `echo-b` has not taken. `head 0` is the oldest message. The same declaration written as `always ((inbox echo-b head 0) implies eventually (inbox echo-a head 0))` is the same formula, and it is printed back as `leads_to`.

```
temporal echo-answered: holds in 8 reachable states
```

`true leads_to Q` says `Q` holds infinitely often: at every position, `Q` holds then or later.

A quantifier `forall (x : T). formula` stands in front of one of these forms. `T` is `Bit` or a declared data type whose constructors are all nullary. The checker decides one formula per constructor. `forall (c : Note). always true` on `echo-wire` holds in the same 8 states. A quantifier over `Nat`, a pair, a record, a vector, or a constructor with a field is refused.

## The state

The state is fixed by the meeting. The buffer bound is `N`. The alphabet is the literals the two processes carry: numerals, bits, and nullary constructors. A configuration is two block pointers, two queues of at most `N` messages, and one slot per binder.

The size of that universe is `|codeL| · |codeR| · Q² · (|alpha| + 1)^(slotsL + slotsR)`, where `Q` is the number of queues of length at most `N` over an alphabet extended by the two labels `pick0` and `pick1`. Reachable configurations are fewer: each process has one action enabled, and the only choice is which side moves. The check walks the reachable graph once. Growing `buffer N`, or the number of distinct literals, grows that graph exponentially.

A pair, a record, a vector, a constructor with a field, and a computed `put` are `payload outside the temporal fragment`. The meeting that carries them can still check. The temporal declaration cannot.

## Runs

A step is one side moving. When both sides can move, both steps are available, left before right. A finished configuration, both blocks halted and both queues empty, steps to itself. The trace prints that stutter as `the meeting has finished`. Every run the formula talks about is infinite: a meeting that finishes stays finished, and a meeting that continues takes another step. `always` needs the proposition at the finished configuration. `eventually` accepts it there. `leads_to` needs its conclusion by that configuration.

A meeting that does not check is not given a temporal verdict. The declaration is `skipped because <meeting> does not check`.

## Fairness

There is no `under fair` clause. A stretch of consecutive steps of one side has length at most `Φ` of that side, where `Φ` of the left at `c` is `(cap ∸ |l2r|) + |r2l|` and `Φ` of the right swaps the queues (`solo-bounded`). On a run that never finishes, the left side moves infinitely often and the right side moves infinitely often (`every-run-fair`). The statements are in [Limits](limits.md#what-is-proved-and-what-is-not). A fairness clause would be a parse error.

## A refusal

The position is the declaration. The formula is printed in surface syntax. The meeting names the two processes and the sessions they follow. A safety refusal is the shortest path, then the configuration:

```
drained: always (inbox hear-server is empty) fails in spin-wire (spin-client : spin, hear-server : hear) after spin-client put bytes: spin-client: put bytes; hear-server: get (f : Frame); l2r: [bytes]; r2l: []
```

A liveness refusal is a stem and a loop. `spin-wire` in `examples/async-meetings.muro` sends `bytes` on every turn, so `hear-server` does not finish:

```
ends: eventually (hear-server done) fails in spin-wire (spin-client : spin, hear-server : hear) after spin-client put bytes, hear-server arm bytes; then forever: spin-client put bytes, hear-server arm bytes
```

## What the checker prints

After `Muro v…`, and before `All terms check. Evidence never becomes a run.`, one line per temporal declaration, in book order:

```
temporal echo-answered: holds in 8 reachable states
```

The count is the number of distinct configurations reachable from the start of that meeting. A refusal replaces that line. A book with no temporal declaration prints the lines it printed before this page existed. A `conforms to` line from an imported package stays after the success sentence. `--fuel` does not change a temporal verdict.

Emit of a book is unchanged by appending a declaration whose meeting checks. Elixir, the state-machine backend, C, Rust, and assembly print the same programs. The ExUnit backend embeds the book hash in `@muro_book`, so that one line changes with the book bytes and the suite body does not. A committed module's header records the same hash, and `mix muro.gen --check` reports the target stale until `mix muro.gen` rewrites the header. That is the rule for any edit of a book.

`Decide.check` accepts exactly when every infinite run from the start satisfies the formula, and a refusal is a run that misses it. A source step is a step of that graph (`sim-fwd`). A graph step on a left put whose place is already that put is that source put (`bwd-put`). Reading an arbitrary graph step back as the source step, and transferring the verdict onto the source meeting, are not theorems.

The propositions, the refusals, and the theorems are listed in [Limits](limits.md). The grammar is in [Grammar](grammar.md).

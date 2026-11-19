---
title: State machines
slug: fsm
order: 22
summary: Each session endpoint is a pure state machine, and a keyed family is one dispatcher. The transport stays with the host.
---

# State machines

`--backend fsm` prints one module for the book's sessions. A host that already has a transport (an RPC, an HTTP exchange, a queue, a websocket, a call between nodes made by other means) steps that module around the messages it sends and receives. The module does not start a process, and it does not talk to a peer. A keyed family that checks is one more child of that module. The session children are unchanged. See [A keyed family](#a-keyed-family).

This is not a replacement for `--backend otp`. The OTP image is a GenServer that owns a mailbox and monitors a marked peer. The state machine is the check that the messages a host already exchanges follow the protocol the meeting proved. A meeting marked `may fail` is accepted. `down` takes the failure arm. A meeting that does not mark a party emits no `down`. The module still starts no process.

## One end

`meet.muro` declares `session back := dual ping`. `back` sends a nat and then receives one. That is the client's end of an RPC.

```
mix muro.emit examples/meet.muro --backend fsm
```

The module is `MeetFsm`. The child is `MeetFsm.Back`. One session is one end, so the module is named for the session, not for a client/server pair the book did not declare.

```elixir
state = MeetFsm.Back.init()
# expected: {:send, :nat}
{:ok, state} = MeetFsm.Back.send(state, 1)
# reply = MyTransport.call(peer, 1)
{:ok, state} = MeetFsm.Back.recv(state, 0)
true = MeetFsm.Back.done?(state)
```

That walk prints `done: true`. Calling `recv` before the send is the error:

```elixir
{:error,
 {:unexpected, "examples/meet.muro:6 session back: first send Nat",
  {:send, :nat}, 0}}
```

`send/2` and `recv/2` return `{:ok, state}` or `{:error, {:unexpected, step, expected, value}}`. `value` is the value the host passed, unchanged. A bad value, a value after `end`, and a call in the wrong direction are that error. They do not raise.

`Muro.emit_fsm(path, module, opts \\ [])` returns `{:ok, source}` or `{:error, message}`. It does not write a file. `mix muro.gen` writes the file when the manifest says `kind: :fsm`. The default module is `Muro.Emit.fsm_module/1`: the stem plus `Fsm` (`meet.muro` is `MeetFsm`).

## The step

`step` is a binary. It names the book, the line of the `session` declaration, the session, and the action:

```
<file>:<line> session <name>: <ordinal> <action>
```

`<file>` is the book's label: relative to the project root, `/` separators, never an absolute path. A session that comes from an imported file uses that file's label. `<ordinal>` counts actions of the same kind in the written protocol, in source order: `first`, `second`, `third`, then `4th`, `5th`. Both arms of a `choose`, a `branch`, a `case`, and an `on` are counted. `<action>` is the wording of one protocol step (`recv Nat`, `send (n : Nat)`, `case (f n)`, `end`).

A step inside `rec` has the same description on every pass. The description names the source step. After `end` the step is `"<file>:<line> session <name>: end"` and `expected` is `:done`. Sending again on `ping` is:

```elixir
{:error, {:unexpected, "examples/meet.muro:4 session ping: end", :done, 9}}
```

The same book emits the same text on every run, including from two working directories.

## expected

`expected/1` is plain data:

| State | Term |
| --- | --- |
| send a payload | `{:send, type}` |
| receive a payload | `{:recv, type}` |
| this end chooses | `{:send_pick, [:b0, :b1]}` |
| the other end chooses | `{:recv_pick, [:b0, :b1]}` |
| `end` | `:done` |
| a failure arm that wrote `stop` | `:stop` |
| a failure arm the machine cannot resolve | `:stuck` |

`type` is `:nat`, `:bit`, `:unit`, `{:pair, a, b}`, `{:record, [{name, type}]}` with the field name a string, `{:vec, type, length}` with the length already a number, or `{:data, "Name", [type]}`. That term is also the third element of the error. A choice is its own step, `{:pick, :b0}` or `{:pick, :b1}`, passed to `send` by the end that chooses and to `recv` by the end that branches. A state expects a payload or a label, not both. A bit index (`on`) is the bit `:b0` or `:b1`, not a pick.

## check_trace

`check_trace/1` takes a list of `{:send, value}`, `{:recv, value}`, `:down`, and `{:down, reason}` in the order this end performed them. `:down` is a step when the book marks a party. It returns `:ok`, or `{:error, {index, reason}}` for the first bad step. `index` is zero-based. `reason` is the same `{:unexpected, step, expected, value}`. A reason `down/2` rejects names `{:down, type}` as what was expected.

A prefix is a valid trace of the emitted machine. A log may be cut short, and a `rec` protocol never reaches `end`. That test is the machine. The book judgment is `prefix`: a list of directed moves is a legal prefix of the declared session from a position. The page is [Sessions](sessions.md#a-legal-prefix). `check_trace(trace, complete: true)` also requires `done?` and otherwise returns `{:error, {length, {:incomplete, step, expected}}}`.

```elixir
:ok = MeetFsm.Ping.check_trace([{:recv, 0}, {:send, 1}], complete: true)
{:error,
 {1,
  {:incomplete, "examples/meet.muro:4 session ping: first send Nat",
   {:send, :nat}}}} = MeetFsm.Ping.check_trace([{:recv, 0}], complete: true)
```

A session with parameters has `init/n`, one nat per parameter, and `check_trace/2` with `args: [..]`. `check_trace/1` is not defined for it. A missing `args:` raises `ArgumentError`. An argument that is not a nat raises `ArgumentError` from `init/n`.

## down

A receive from a marked party has a failure arm. `down/1` takes an arm that binds no reason. `down/2` takes an arm that binds one, and the reason is the value the host supplies. The machine checks that value the way `recv` checks a payload. The OTP image does not check the `:DOWN` reason. `:kill` arrives there as `:killed`.

```elixir
{:ok, state} = ServerWait.down(state)
true = ServerWait.done?(state)
```

An arm written `done` finishes, and `expected` is `:done`. An arm written `stop` leaves `done?` false and `expected` `:stop`. An arm the machine cannot resolve leaves `done?` false and `expected` `:stuck`. `down` at a send, at `end`, or after `stop` is `{:unexpected, step, expected, value}`. A book that does not mark a party emits no `down`. `value` is `:down` for `down/1` and the reason for `down/2`. When the arm names a reason and the host calls `down/1`, `expected` is `{:down, type}`. When the arm names no reason and the host calls `down/2`, `expected` is `:down`.

`expected/1` stays the protocol step. While the end is still at the receive, that is `{:recv, type}`. `down` is an extra step beside it. A `match` on the bound reason selects the arm inside `down` and binds the constructor's fields, so `down(state, :b0)` can finish and `down(state, :b1)` can stop. The host calls `down` or `recv` again for a later receive inside the arm. A value already passed to `recv` is not dropped. The checker also counts a run that drops a message already queued. This module does not take that run.

## Wire form

A value is accepted only when the whole value is of that step's payload type, in the form the OTP image carries.

| Payload | On the wire |
| --- | --- |
| `Nat` | a non-negative integer |
| `Bit` | `:b0` or `:b1` |
| `Unit` | `:tt` |
| a pair | a two-element tuple |
| a record | a map whose keys are exactly the field names |
| `Vec` | a list of the length the type says |
| a nullary constructor | an atom (`:bytes`, and `true` / `false` for those constructors) |
| a constructor with fields | a tagged tuple (`{:just, 0}`) |

A vector length is the numeral in the type, or the nat received earlier in this protocol. The machine keeps that binding. A `rec` loop rebinds it on each pass. `sized` after `recv` of `2` expects `{:send, {:vec, :nat, 2}}` and accepts `[0, 0]`.

An evidence payload is the nat alone. The evidence is not on the wire. The machine also checks the bound that evidence stands for, a numeral or an earlier nat. `window` after receiving `8` expects `{:send, {:nat_at_most, 8}}`, and `9` is `:unexpected`. This is stricter than the OTP image, which checks only that the value is a nat. A binder erased in any other way is not on the wire.

A bit index selects the first arm on `:b0` and the second on `:b1`. A `case` on the constructor just exchanged takes that constructor's arm, in declaration order. `case (f n)` applies the emitted `run` `f` to the value just exchanged and takes the arm of the result. The run functions live in the parent module. They take the emitter's data, and a nat there is the same non-negative integer as on the wire, at any size. A library run (`plus`, `minus`, `compare`, and the others in [Emit](emit.md#how-values-look)) is one integer operation on it. A recursive run that is not one of those still takes one call per unit of the value it recurses on, so a run that walks a nat of a billion takes a billion steps. A host that passes untrusted input bounds the nat itself before it reaches the machine. The C session image builds a Peano nat for that run and refuses a nat above `100_000`. The JavaScript session image keeps nats as BigInts and refuses a nat above `100_000` passed to a run. `expected/1` still describes the protocol step.

## repr

When the book has a `repr` for a payload type (#131), that type's host form is the repr. `send` and `recv` call the book's `decode_<type>/1`. That call returns `{:ok, value, table}`. The machine checks `value` against the wire form above and drops the table. A value the codec rejects is `:unexpected`. The third element names the type and its repr, for example `{:recv, {:repr, {:data, "Box", []}, "Box"}}`. The codec's own reason is not part of the error. A type with no `repr` stays on the wire form, and `{:box, 3}` is the value of `box : Nat → Box`.

## State

State is opaque. Store it, thread it, and compare it with `==`. Do not depend on its shape. It is plain data: atoms, integers, binaries, and lists. A value that is not a state of this session is `:unexpected`, with this session's `end` step, and `done?` is false. Nothing raises.

## A keyed family

A family that checks is one child, named for the family. `examples/keyed-slots.muro` is `KeyedSlotsFsm.Slots`. The child does not run the meeting. The host calls `resolved` when that instance should stop blocking, including when the instance gives up. Giving up counts as resolved for the rule, and it is not delivered.

```elixir
state = KeyedSlotsFsm.Slots.new()
{:open, id, state} = KeyedSlotsFsm.Slots.arrive(state, "a", :init, 0)
{:held, sig, state} = KeyedSlotsFsm.Slots.arrive(state, "a", :signal, 1)
{:ok, [{sig, "a", :signal}], state} = KeyedSlotsFsm.Slots.resolved(state, id)
```

`new/0` returns the empty state.

`arrive/4` takes the state, the key, the constructor, and the creation index. The constructor is the atom of a nullary constructor of the kind (`:init`, `:signal`). The creation index is a non-negative integer. Instances of one key need not arrive in creation order. An earlier index can arrive after a later one has opened. The call returns `{:open, id, state}` or `{:held, id, state}`. `id` starts at 0 and counts arrivals.

A kind written `never held` opens on arrival. A second init of a key opens at once. A kind written `held while earlier unresolved` stays held while any earlier arrived instance of its key is unresolved. An earlier init is one of those, and so is an earlier signal. An instance that has not arrived is not unresolved. A signal with no earlier unresolved instance of its key opens at once. There is no third outcome.

`resolved/2` takes the state and an id this child returned while that instance was open. It returns `{:ok, released, state}`. `released` lists `{id, key, kind}` for the instances this resolution opens, in creation-index order, and may be empty. The resolved instance leaves the state. An id that is still held is `{:error, {:held, id}}`. A forgotten id, and an id this child never returned, are `{:error, {:unknown, id}}`. The call does not return `{:error, {:resolved, id}}`. The call does not raise. Opening one instance does not release another key.

The state keeps the live instances, open or held, and the id of each live instance records its key. One counter is the next id. A call fetches that key and does not touch the other keys. `arrive` is O(L) in that key's live rows. `resolved` is O(L²) in those rows: `take_released` calls `blocked?` once per held row, and each `blocked?` walks the rows. A value that has the shape of a state is accepted at that boundary. A bad row is reported by the call that fetches it. A held id returns `{:error, {:held, id}}` from that one row.

A repeat of a live instance, the same key and the same creation index while that instance is open or held, is `{:error, {:duplicate, key, index}}`. A repeat of a forgotten instance is not caught. The row is gone, and the dispatcher does not keep forgotten indices. An index at or below a forgotten one is not, by itself, a repeat: a later arrival may carry an earlier creation index, and that arrival is a new instance.

The key is compared with `==`. It is the workflow. A call fetches that key. Live instances of one workflow share the rule, including across runs of that workflow, and that is accepted. The guarantee is the instances that have arrived and are still live. A signal that opens before an earlier init arrives does not wait for that init. `no-overtake` is about the instances known when the signal opened.

State is opaque. Thread it and compare it with `==`. A value that is not a state of this child is `{:error, …}`.

`check_trace/1` replays a list from `new()`. A dispatcher step is `{:arrive, key, kind, index}` or `{:resolved, id}`. A session step is `{party, id, action}`. `party` is the conform atom, `:server` or `:task` on `examples/keyed-slots.muro`. `action` is `{:send, value}`, `{:recv, value}`, `:down`, or `{:down, reason}`. It returns `:ok`, or `{:error, {index, reason}}` for the first bad step. `index` is zero-based. A value that is not a list is `{:error, …}`. There is no `check_trace/2`.

`resolved` with no session step for that id is the instance giving up. It counts as resolved, and it is not delivered. `resolved` when every stepped party of that id is at `done` resolves the instance. `resolved` when a stepped party is not at `done` is `{:error, {index, {:unfinished, id}}}`, and the instance stays. At the end of the trace, an instance is `{:error, {:unresolved, id, key, kind}}` when every stepped party of that id is at `done` and the instance was never resolved. A `down` into a failure arm that ends in `done` counts as that party's `done`. One party at `done` while another stepped party is not is still the meeting, and the trace is `:ok`. The id is the smallest such id. A `down` into an arm that ends in `stop` is not that error. A session step on a held id is `{:error, {index, {:held, id}}}`. A session step on an unknown id is `{:error, {index, {:unknown, id}}}`.

Each end of the family's meeting has `finish/3` and `finish/4` on the session child. `examples/keyed-slots.muro` puts them on `ServerWait` and `TaskWork`.

```elixir
{:ok, released, state} = KeyedSlotsFsm.ServerWait.finish(session, :down, state, id)
{:ok, released, state} = KeyedSlotsFsm.ServerWait.finish(session, state, id)
```

`finish/4` takes the session state, one step, the dispatcher state, and the id. The step is `{:send, value}`, `{:recv, value}`, `:down`, or `{:down, reason}`. The step has to land on `done`: the report or the completion, or `down` into a failure arm that ends in `done`. The call then resolves that id. It returns what `resolved` returns. The host makes one call for the instance's end, including the task's `:DOWN`, and the dispatcher drops the instance in that call.

`finish/3` takes a session state that is already at `done`, the dispatcher state, and the id, and resolves it the same way.

A session that is not at an end this call can reach is `{:error, …}`. The call does not raise. A held id and a forgotten id are the errors `resolved` returns. `down` into an arm that ends in `stop` is `{:error, {:unfinished, :stop}}`, and the instance stays. Where two families share the end, the call is `{:error, {:family, names}}` and it does not resolve. The session child's own `check_trace` is that end alone. It does not resolve the family.

This child is generated code. The family graph is an Elixir check of a fixed script. The tests on `examples/keyed-slots.muro` replay one trace, refuse an unknown id, and check that every accepted sequence of `arrive` and `resolved` over that script is a run of the family graph. A sequence on some other key is outside that script. Neither check is an Agda proof. The counts stay 171649 reachable states, 729184 transitions.

A family that does not check is not emitted. A book with no family emits the same module as before. OTP, Elixir, C, Rust, Zig, JavaScript, assembly, `--node`, and ExUnit still omit the family. A meeting marked `may fail` is still refused by those backends with `c:mayfail`. The state machine accepts that meeting, as it did before, and emits this child beside the session children.

## What emit refuses

The refusal is the whole module. A book that does not check is refused by the checker, with the checker's message. A book that checks, and that the machine cannot represent, is refused with `<file>:<line> session <name>: <reason>` (a missing session name has no line).

| Reason | When |
| --- | --- |
| `<file> has no session to emit` | the book declares no session |
| `seen is not a state machine` | the protocol is a talk |
| `cannot evaluate bound <ix>` | an evidence bound is not a numeral, a name, or `suc` of one |
| `cannot evaluate vector length <ix>` | a length is not one of those |
| `cannot evaluate argument <ix>` | a jump argument is not one of those |
| `cannot call run <f>` | a `case (f n)` run is not one nat, bit, unit, pair, or declared payload, or its result has no constructors |
| `payload <type> is not supported` | a payload outside the table above |
| `ill-formed protocol` | a protocol form the opener does not know |
| `unguarded session call` | a session calls itself with no action in between |
| `unguarded rec` | `rec X. X` |
| `unknown session <name>` | `dual` of a session that is not declared |
| `session declared later` | a call of a session declared further down the book |
| `wrong number of session arguments` | the call's arity is not the declaration's |
| `dual cycle` | two sessions that are each other's dual with no body |

`examples/talk.muro` and `examples/seated.muro` are refused because the protocol is `seen`. `examples/meet.muro`, `examples/indexed.muro`, and `examples/recursive.muro` emit completely, and so do the other session examples whose protocols are the forms above. `--node` with this backend is refused (`--node writes the placement calls`). `--imports` with this backend is refused.

## Manifest

```elixir
{"priv/muro/meet.muro", Host.MeetFsm, "lib/host/meet_fsm.ex", [kind: :fsm]}
```

`impl:` and `imports:` on a `:fsm` entry are errors, and the message names the entry index. They remain valid only for `kind: :exunit`. The header, the hashes, `written` / `unchanged`, `--check`, a stale book, and a hand edit are the same as for the other kinds.

The child of `session ping` is `Host.MeetFsm.Ping`. Each child has `init`, `send`, `recv`, and `done?`. A book that marks a party also gives each child `down/1` and `down/2`. A book that does not mark a party emits no `down`. A session name whose function spelling is plain snake case (lowercase words of letters and digits joined by single underscores) camelizes: `ping` is `Ping`, `foo_bar` is `FooBar`, and `grant-end` is `GrantEnd`. Any other name is `M` plus the function spelling (`and` is `Mmuro__and`). Two sessions that camelize to the same name are `Ping` and `Ping_2`.

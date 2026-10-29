---
title: State machines
slug: fsm
order: 22
summary: Each session endpoint is a pure state machine. The transport stays with the host.
---

# State machines

`--backend fsm` prints one module for the book's sessions. A host that already has a transport (an RPC, an HTTP exchange, a queue, a websocket, a call between nodes made by other means) steps that module around the messages it sends and receives. The module does not start a process, and it does not talk to a peer.

This is not a replacement for `--backend otp`. The OTP image is a GenServer that owns a mailbox. The state machine is the check that the messages a host already exchanges follow the protocol the meeting proved. The OTP image is unchanged.

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

`type` is `:nat`, `:bit`, `:unit`, `{:pair, a, b}`, `{:record, [{name, type}]}` with the field name a string, `{:vec, type, length}` with the length already a number, or `{:data, "Name", [type]}`. That term is also the third element of the error. A choice is its own step, `{:pick, :b0}` or `{:pick, :b1}`, passed to `send` by the end that chooses and to `recv` by the end that branches. A state expects a payload or a label, not both. A bit index (`on`) is the bit `:b0` or `:b1`, not a pick.

## check_trace

`check_trace/1` takes a list of `{:send, value}` and `{:recv, value}` in the order this end performed them. It returns `:ok`, or `{:error, {index, reason}}` for the first bad step. `index` is zero-based. `reason` is the same `{:unexpected, step, expected, value}`.

A prefix is a valid trace. A log may be cut short, and a `rec` protocol never reaches `end`. `check_trace(trace, complete: true)` also requires `done?` and otherwise returns `{:error, {length, {:incomplete, step, expected}}}`.

```elixir
:ok = MeetFsm.Ping.check_trace([{:recv, 0}, {:send, 1}], complete: true)
{:error,
 {1,
  {:incomplete, "examples/meet.muro:4 session ping: first send Nat",
   {:send, :nat}}}} = MeetFsm.Ping.check_trace([{:recv, 0}], complete: true)
```

A session with parameters has `init/n`, one nat per parameter, and `check_trace/2` with `args: [..]`. `check_trace/1` is not defined for it. A missing `args:` raises `ArgumentError`. An argument that is not a nat raises `ArgumentError` from `init/n`.

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

A bit index selects the first arm on `:b0` and the second on `:b1`. A `case` on the constructor just exchanged takes that constructor's arm, in declaration order. `case (f n)` applies the emitted `run` `f` to the value just exchanged and takes the arm of the result. The run functions live in the parent module. They take the emitter's data (a nat is `0` or `{:suc, n}`), so the call converts at that boundary only. A nat above `100_000` is `:unexpected` there, with `{:nat_at_most, 100_000}`, and no Peano term is built. `expected/1` still describes the protocol step.

## repr

When the book has a `repr` for a payload type (#131), that type's host form is the repr. `send` and `recv` call the book's `decode_<type>/1`. That call returns `{:ok, value, table}`. The machine checks `value` against the wire form above and drops the table. A value the codec rejects is `:unexpected`. The third element names the type and its repr, for example `{:recv, {:repr, {:data, "Box", []}, "Box"}}`. The codec's own reason is not part of the error. A type with no `repr` stays on the wire form, and `{:box, 3}` is the value of `box : Nat → Box`.

## State

State is opaque. Store it, thread it, and compare it with `==`. Do not depend on its shape. It is plain data: atoms, integers, binaries, and lists. A value that is not a state of this session is `:unexpected`, with this session's `end` step, and `done?` is false. Nothing raises.

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

The child of `session ping` is `Host.MeetFsm.Ping`. A hyphen in the session name becomes a capital (`grant-end` is `GrantEnd`). Two sessions that camelize to the same name are `Ping` and `Ping2`.

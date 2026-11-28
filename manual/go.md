---
title: Go
slug: go
order: 31
summary: Sessions, choreography monitors, and keyed-family dispatchers as one Go file. Runs, data declarations, and repr codecs are not emitted.
---

# Go

In brief: `mix muro.emit path.muro --backend go` writes `<stem>.go` next to the book and prints that path. The file is one package. It contains the session machines, one monitor per choreography, one dispatcher per keyed family, and one per-key monitor per family of a choreography. Those are the machines `--backend fsm` prints. The Go file renders the same checked plan. It does not emit `run`. A book with neither a session nor a choreography is refused with `<file> has no session to emit`.

The file imports only the standard library (`errors`, `fmt`, and `sort` when a family or a per-key monitor needs it). It has no `init` function and no mutable package state. A refused step returns an error. It does not panic. The first line matches `^// Code generated .* DO NOT EDIT\.$`, so `go` tools treat the file as generated.

```
mix muro.emit examples/ping.muro --backend go
mix muro.emit examples/ping.muro --backend go --package host
```

`Muro.emit_go/2` writes the same file and returns `{:ok, [path]}`. `mix muro.gen` writes it when an entry sets `kind: :go`. The target ends with `.go` and names no module. The gen header sits above the generated line. Both name the book. The body is the emitter's text, and it is not formatted by Mix.

## Package and names

`--package NAME` is valid only with this backend. `NAME` matches `^[a-z][a-z0-9_]*$` and is not a Go keyword or a predeclared identifier. Anything else is `go: package name`. Absent, the package is the book stem: lowercased, a character outside `[a-z0-9_]` replaced by `_`, repeats collapsed, and a leading digit or an empty stem prefixed with `p_`. A keyword or a predeclared name gains `_k`. `keyed-slots.muro` is `package keyed_slots`. `any.muro` is `package any_k`.

An exported type is the source name in CamelCase, split on characters that are not letters or digits. An empty name is `X`. A name that starts with a digit is prefixed with `X`. A second claim of the same spelling is `Name_2`. Go keywords, predeclared identifiers, and the names this file defines (`Send`, `Recv`, `Value`, `String`, `Error`, the error types, the family phases) are claimed first, so a session named `Send` is `Send_2` and the event type stays `Send`. A constructor parameter is claimed the same way. A character outside letters, digits, and `_` becomes `_`, and the claim runs across the parameters, so `Nat` is `Nat_2`, `string` and `nil` are `string_2` and `nil_2`, and `a-b` followed by `a_b` is `a_b` then `a_b_2`.

## What the file contains

A session is a struct. `NewPing` returns the value at its first step. A session with parameters returns `(T, error)`. A negative argument is `ArgumentError`, and `errors.Is` matches `ErrArgument`. The zero value is not started: `State` is invalid, `Expected` is `"start"`, and `Step` returns an error. `Step` is a method on the pointer. On error the value is unchanged. `Done` reports the end. `Expected` names the next event (`"recv nat"`, `"send nat"`, `"send pick"`, `"done"`).

`Event` is an interface with an unexported method. Only `Send` and `Recv` implement it. Each carries a `Value`. Constructors are `Unit`, `Nat`, `Bit0`, `Bit1`, `Pick0`, `Pick1`, `Con`, `Pair`, `Record`, and `Vec`. `Record` sorts fields by name. A value that does not match the protocol is refused by `Step`, and the value stays where it was. A quiet jump is not that refusal: when an actual of a jump to this same session does not produce a nat, `Step` returns nil and the state is stuck. A book that marks a party also has `Down`. The reason is `*Value`, and nil is an arm that binds no reason. A failure arm of `finish` is done. A failure arm of `leave` is stop. Any other failure arm is refused before a file is written: `go: failure arm continues the protocol`. A book that does not mark a party emits no `Down`.

A choreography with no per-key family is one monitor value. `NewPlan` returns it. `Step(from, to, label, v)` takes the next message. A message with no payload takes `Unit()`. `Choose(role, label)` takes the next choice. `Expected` is `"message from to label"` or `"choose role a|b"`.

A family of a choreography is a pointer. `StepShared` and `ChooseShared` take the shared preamble, once. `Step` and `Choose` then take one key. A key step during the preamble is refused, and `Expected` on that error starts with `"shared "`. `SharedDone` reports the preamble. `Done(key)` reports one key. `Keys` returns the keys that have stepped, sorted.

A keyed family is a pointer from `NewSlots`. The methods are `Arrive`, `Resolved`, `Withdraw`, `WaitingOn`, `Skip`, `DropKey`, `SkipBelow`, `Revert`, `Rerun`, `Finish`, `View`, `Floor`, `Departed`, and `Live`. They are the decisions `Muro.Family.Step` runs, including `held while earlier unresolved`, `held while any unresolved`, `held while <kind> unresolved`, `held until <kind> resolved`, a comma list, and a repeated `held`. `Arrive` returns the phase and the id. On error the id is `-1` and the dispatcher is unchanged. `Resolved` and `Withdraw` return the rows that moved from held to open, sorted by creation index then id. `WaitingOn` returns the kind names and the ids that still block a held row. `SkipBelow` raises one floor for every key. An index at or below the floor has departed, including a first arrival. `Departed(key)` reports the packed prefix and the gaps. A missing key is prefix `-1`, no gaps, and false. A second arrival of a departed pair is `ErrDeparted`. `Finish(id, sessionDone, outcome)` resolves or reruns an open row after the host says the meeting session is done. It does not step that session. `sessionDone == false` is `ErrUnfinished`. `OutcomeResolve` and `OutcomeRerun` are the two outcomes.

`Revert` is always emitted. On a family marked `may revert` it puts a resolved row back to open when no open or resolved row of the same key holds it. An unmarked family returns `ErrUnmarked` and does not read the row. `may redeliver` is a comment on the type. It is not a method. `contract` declarations are not checked in this file. The state machine's external-contract lines stay on `mix muro.check`.

The kind is `type SlotsKind uint8` with one constant per constructor, in declaration order. The first constructor is iota 0. More than 255 constructors is `go: unsupported family`. Phases are `PhaseOpen`, `PhaseHeld`, and `PhaseResolved`.

## Errors

`IllegalTransitionError` has `Machine`, `State`, `Expected`, and `Event`. `Error()` describes the refusal. `Unwrap` returns `ErrIllegalTransition`, so `errors.Is` and `errors.As` both match. A nil receiver and a zero value are that same error.

`FamilyError` has `Code`, `Key`, `Index`, `ID`, `Kind`, and `IDs`. `Unwrap` returns the sentinel, and that sentinel unwraps to `ErrFamily`. `errors.Is(err, ErrDuplicate)` and `errors.Is(err, ErrFamily)` both hold. The sentinels are `ErrDuplicate`, `ErrDeparted`, `ErrUnknown`, `ErrHeld`, `ErrOpened`, `ErrResolved`, `ErrWithdrawn`, `ErrHeldBy`, `ErrLive`, `ErrKind`, `ErrBadState`, `ErrIndex`, `ErrUnmarked`, and `ErrUnfinished`. A field that does not apply is the zero of that field, and an unused id is `-1`.

## An excerpt

`examples/ping.muro` begins:

```
// Code generated by muro 0.22.52. DO NOT EDIT.

// Package ping is a session, choreography, and keyed-family image.
// Callers own each value. One session, monitor, or dispatcher is not
// safe for concurrent use: synchronize, or give each goroutine its own value.
package ping

import (
	"errors"
	"fmt"
)

// ErrIllegalTransition is the sentinel for a refused step.
var ErrIllegalTransition = errors.New("muro: illegal transition")

// IllegalTransitionError is a refused step. Unwrap returns ErrIllegalTransition.
type IllegalTransitionError struct {
	Machine  string
	State    string
	Expected string
	Event    string
}
```

The session itself:

```
// Ping is one end of session ping.
// The zero value is not started: Step and Down report an illegal transition.
// Ping is not safe for concurrent use.
type Ping struct {
	state PingState
	ready bool
	env   map[string]Value
}

// PingState is the resting position of Ping.
type PingState uint8

const (
	// PingStateInvalid is the zero Ping.
	PingStateInvalid PingState = iota
	// PingStateRecv1 is examples/ping.muro:5 session ping: first recv Nat.
	PingStateRecv1
	// PingStateSend1 is examples/ping.muro:5 session ping: first send Nat.
	PingStateSend1
	// PingStateDone is the end of the session.
	PingStateDone
	// PingStateStuck is a protocol position with no step.
	PingStateStuck
)

// NewPing starts Ping at its first step.
func NewPing() Ping {
	return Ping{state: PingStateRecv1, ready: true, env: map[string]Value{}}
}

// Step takes one send or receive. A refused step leaves the value unchanged.
func (m *Ping) Step(ev Event) error {
	if m == nil || !m.ready {
		return muroIllegal("Ping", "invalid", "start", muroEvent(ev))
	}
	switch ev := ev.(type) {
	case Send:
		return m.stepSend(ev.Value)
	case Recv:
		return m.stepRecv(ev.Value)
	default:
		return muroIllegal("Ping", m.State().String(), m.Expected(), muroEvent(ev))
	}
}
```

A host drives it:

```
m := NewPing()
if err := m.Step(Recv{Value: Nat(1)}); err != nil {
    return err
}
if err := m.Step(Send{Value: Nat(1)}); err != nil {
    return err
}
```

`m.Done()` is then true. A send at the first state returns `*IllegalTransitionError` and leaves `m` at `PingStateRecv1`.

Put the file in its own directory. The package clause is the import name.

```
go mod init example.com/ping
go vet ./...
gofmt -l .
go test ./...
```

`gofmt -l` prints nothing: the emitter writes the canonical form (tabs, aligned const blocks) and does not call `gofmt`, so two runs of the same book are the same bytes. `go test -race` needs cgo and a C compiler. The race detector is how a host checks the rule below.

## Concurrency

A session, a monitor, and a dispatcher are not safe for concurrent use. The file has no mutex. Callers synchronize, or give each goroutine its own value. Two goroutines may each call `NewSlots` and `Arrive` on the value they own. Two goroutines that share one pointer take the lock themselves. `go test -race` on the live tests covers both arrangements. The mutex in that test is in the test file, not in the generated package.

## What this backend refuses

The refusal is the whole file. Nothing is written.

| Reason | When |
| --- | --- |
| `<file> has no session to emit` | the book declares no session and no choreography |
| `go: repr payload` | a session payload type has a `repr` |
| `go: run case` | a `case` calls a `run` |
| `go: unsupported protocol` | a session jumps to a different session |
| `go: dual jump` | a jump the planner cannot place on one machine |
| `go: failure arm continues the protocol` | a `may fail` arm is neither `finish` nor `leave` |
| `go: unsupported payload` | a payload outside the values above |
| `go: unsupported family` | more than 255 constructors of the key |
| `go: package name` | `--package` is not a legal package identifier |
| the state machine's reason | a protocol the planner already refuses (`seen` of a talk, an unguarded `rec`, a bound that is not a numeral) |

A meeting marked `may fail` is emitted when every failure arm is `finish` or `leave`. This backend does not answer `c:mayfail`.

## Phase 2 is not this file

Pure functions, data declarations, and `repr` codecs are not emitted. `Muro.IR` elaborates closed runs. It does not present data declarations or `repr` codecs as a lowering a backend can consume from `elaborate/1` alone. A Go image of `run` would be a second emitter, checked by running that image against the interpreter. This release does not add it. A book that is only `run` terms is refused with `<file> has no session to emit`.

## Checks

The unit tests read the text and need no `go` binary. The live tests compile the file. They replay the same traces the Elixir machines accept and refuse: illegal transitions that do not move, payload sessions, a parameterized constructor, a choreography monitor, a per-key monitor, every family rule above, and a seeded walk of forty steps. `gofmt -l` must print nothing. `go vet` must accept the package. `go test` runs the traces. When `gcc` or `cc` is on `PATH`, `go test -race` runs them again. When `go version` does not exit 0, or does not finish, the live tests skip with `go is not available`. The race half is skipped on its own when no C compiler is present, and `go test` still runs.

Those live tests are not on the CI runners yet. Adding Go there is a follow-up, and it needs a workflow change. A runner without `go` skips the live tests and runs the rest.

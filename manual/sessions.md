---
title: Sessions
slug: sessions
order: 6
summary: A session is the protocol two processes follow.
---

# Sessions

A session is a description of the messages two processes exchange and the order they exchange them. It is not the processes. It is the protocol.

You write the protocol once:

```muro
session ping := recv Nat (send Nat end)
```

This says: the process that holds this end receives a nat, then sends a nat, then ends. The other end is the dual:

```muro
session back := dual ping
```

`back` is `send Nat (recv Nat end)`. Every send on one is a receive on the other. That is duality.

A process is evidence that it follows one end of the protocol. You write it with `conform`:

```muro
conform pong : ping := get (k : Nat) (put 1 done)
```

`get` receives. The binder `(k : Nat)` names the value. `get Nat` receives a nat and does not name it. `put` sends. `done` ends. The process `pong` follows `ping`: it receives a nat, then sends the literal `1`.

The other process follows the dual:

```muro
conform peer : back := put 1 (get (m : Nat) done)
```

It sends `1`, then receives a nat.

The meeting is the check that these two processes are the two parties of one description:

```muro
meet wire : pong with peer
```

The meeting is evidence. It is not a run term. A run definition has no seat. The OTP image is the only runtime that can produce the event of exchanging the payload and stopping `:normal` when the parties sit at different places. Other emitters do not implement the meeting.

Places are where the parties sit. When the places are the same, the meeting stays. When the places differ, the meeting crosses once. The boundary is the seating. The payload stays on the session.

```mermaid
---
config:
  theme: base
  look: classic
  themeVariables:
    darkMode: true
    background: "#050505"
    fontFamily: "IBM Plex Mono, ui-monospace, monospace"
    primaryColor: "#1a1a1a"
    primaryTextColor: "#f3f3f3"
    primaryBorderColor: "#2e2e2e"
    lineColor: "#8d8d8d"
    textColor: "#f3f3f3"
    actorBkg: "#1a1a1a"
    actorBorder: "#2e2e2e"
    actorTextColor: "#f3f3f3"
    actorLineColor: "#5e5e5e"
    signalColor: "#f3f3f3"
    signalTextColor: "#c8c8c8"
    noteBkgColor: "#1a1a1a"
    noteTextColor: "#8d8d8d"
    noteBorderColor: "#2e2e2e"
    labelBoxBkgColor: "#1a1a1a"
    labelBoxBorderColor: "#2e2e2e"
    labelTextColor: "#8d8d8d"
  sequence:
    actorFontFamily: "IBM Plex Mono, ui-monospace, monospace"
    noteFontFamily: "IBM Plex Mono, ui-monospace, monospace"
    messageFontFamily: "IBM Plex Mono, ui-monospace, monospace"
---
sequenceDiagram
  participant Pong as pong
  participant Peer as peer
  Note over Pong, Peer: same place
  Pong->>Peer: stay
  Note over Pong, Peer: places differ
  Pong->>Peer: cross
```

`examples/meet.muro`

## Value binding

Value binding is the ability to name what you received and send it later:

```muro
conform echo : ping := get (k : Nat) (put k done)
```

`k` is bound by the `get`. The `put` uses it. The innermost binding wins. The payload type is data, so the bound value can be sent more than once. The meeting requires that name to be bound at exactly the type the other process receives.

## Choice

A choice is an arm selection:

```muro
session choice := choose end (send Nat end)
session offered := dual choice
conform taker : choice := pick0 done
conform giver : offered := cover done (get Nat done)
meet arm : taker with giver
```

`pick0` takes the first arm. The other party covers both arms. The meeting checks that the chosen arm matches.

---
title: Sessions
slug: sessions
order: 6
summary: A session is the messages two processes exchange, and the order they exchange them.
---

# Sessions

Muro supports binary session types. A session is a description of the messages two processes exchange and the order they exchange them. The two parties of the session are dual: every send on one is a receive on the other. The parties sit at places. When the places are the same the meeting stays. When the places differ the meeting crosses once. The meeting is the evidence that the two processes are those parties and that the seating matches the boundary. The OTP image is the only runtime that can produce the event of exchanging the payload and stopping `:normal` when the parties sit at different places. Other emitters do not implement the meeting.

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

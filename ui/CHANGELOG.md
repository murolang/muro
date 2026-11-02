# Changelog

## 0.2.0

The page opens on the meetings in the book. They are grouped under the base session, in source order. A row names the meeting, the two conforms, the base session, the step count, and a refinement such as `{d ≤ w}` when the session carries one. Choosing a meeting patches `?meet=` onto the URL, so `http://127.0.0.1:4017/?meet=wire` opens that meeting. The focused view draws the configuration graph the checker recorded as a sequence: two lanes, one per conform, and one row per step, labelled with the value or type sent and the choice branch for `choose` and `offer`. A halted state is a terminal row (`done`, `stop`, or `end`). A context panel shows the session, its dual, the two conforms and their source locations, and a checked badge. The backend switch redraws the OTP, FSM, C, Rust, or Zig outline while that meeting stays open. All definitions, at `?view=all`, is the graph from 0.1.0.

Install it by adding `{:muro_visor, "~> 0.2.0"}` to a Mix project. A published package depends on `muro ~> 0.20.7`. A checkout builds against the repository. It does not emit code and it does not change the wall.

## 0.1.0

`mix muro.ui path.muro` opens one checked book on port 4017. It prints the URL of the address it binds and opens it: `http://127.0.0.1:4017/` for IPv4 loopback, `http://[::1]:4017/` for an IPv6 address, and `http://localhost:4017/` for a hostname. The page connects over `/live`. Nodes sit in ranks along use edges, and each edge has its own path, including a loop when a definition uses itself. A session is a compound node. Each meeting lays out its configurations inside that box, with the transitions the checker recorded drawn and labelled. The graph pane scrolls and zooms. Detail and Outline sit beside it. The outline's names, signatures, layouts, and clauses are separate sections. A backend switch redraws the OTP, FSM, C, Rust, or Zig outline without checking the book again. C, Rust, and Zig layouts include each data type's constructor tags and fields. A click or a key selects a node, an edge, or a configuration and shows the source file, line, and column. An edge also shows the out-of-order refusal, naming the process and the protocol, and a use that is not a step says there is no refusal. A meeting that fails to check is that error, with no configurations.

Install it by adding `{:muro_visor, "~> 0.1.0"}` to a Mix project. A published package depends on `muro ~> 0.20.7`. A checkout builds against the repository. It does not emit code and it does not change the wall.

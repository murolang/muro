# Changelog

## 0.1.0

`mix muro.ui path.muro` opens one checked book on port 4017. The page connects over `/live`. Nodes sit in ranks along use edges, and each edge has its own path, including a loop when a definition uses itself. A session is a compound node. Each meeting lays out its configurations inside that box, with the transitions the checker recorded drawn and labelled. The graph pane scrolls and zooms. Detail and Outline sit beside it. The outline's names, signatures, layouts, and clauses are separate sections. A backend switch redraws the OTP, FSM, C, Rust, or Zig outline without checking the book again. C, Rust, and Zig layouts include each data type's constructor tags and fields. A click or a key selects a node, an edge, or a configuration and shows the source file, line, and column. An edge also shows the out-of-order refusal, naming the process and the protocol, and a use that is not a step says there is no refusal. A meeting that fails to check is that error, with no configurations.

Install it by adding `{:muro_visor, "~> 0.1.0"}` to a Mix project. A published package depends on `muro ~> 0.20.7`. A checkout builds against the repository. It does not emit code and it does not change the wall.

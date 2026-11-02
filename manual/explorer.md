---
title: Visual explorer
slug: explorer
order: 24
summary: muro_visor draws a checked book. The compiler does not start it.
---

# Visual explorer

`muro_visor` is a read-only view of one checked book. It is its own package, with its own versions. The compiler and the release binaries do not depend on it.

`muro ui path.muro` prints how to install it. It does not start the explorer. Add muro_visor to a Mix project, fetch its dependencies, and open the book with the Mix task:

```
{:muro_visor, "~> 0.1.0"}
mix deps.get
mix muro.ui path.muro
```

From a checkout of this repository the task lives in `ui/`:

```
cd ui && mix deps.get && mix muro.ui path.muro
```

The page listens on port 4017. It draws one node for each spec, evidence, and run, and one edge for each use. Nodes sit in ranks along those edges, and each edge has its own path. A use of a definition by itself is a loop. A session is a compound node. Each meeting lays out its configurations inside that box, with the transition between configurations labelled. The positions come from the same walk the checker uses. The graph pane scrolls and zooms. Detail and Outline sit beside it.

Selecting a node, an edge, or a configuration shows the source file, line, and column. A selection can be made with a click or with the keyboard. Selecting an edge also shows the refusal the checker returns when that step is moved one place earlier: the process, the protocol, and the reason. A use that is not a step says there is no refusal.

The outline is split into names, signatures, layouts, and clauses, and each section can be collapsed. A backend switch redraws that outline for the same book: the OTP GenServer (its mailbox, and the `handle_call` and `handle_info` clauses), the pure state machine, or the C, Rust, or Zig signature and closed layout, including each data type's constructor tags and fields. The switch reads the outline that emitter already builds. It does not check the book again, and it does not write code.

The explorer does not emit, and it does not change the wall.

---
title: Visual explorer
slug: explorer
order: 24
summary: muro_visor draws a checked book. The compiler does not start it.
---

# Visual explorer

`muro_visor` is a read-only view of one checked book. It is its own package, with its own versions. The compiler and the release binaries do not depend on it.

`muro ui path.muro` prints how to install it. It does not start the explorer.

```
mix archive.install hex muro_visor
mix muro.ui path.muro
```

From a checkout of this repository the task lives in `ui/`:

```
cd ui && mix deps.get && mix muro.ui path.muro
```

The page draws one node for each spec, evidence, and run, and one edge for each use. A session is a compound node. Its children are the configurations the meeting proved, taken from the same walk the checker uses. Clicking a node or an edge shows the source location. Clicking an edge also shows the refusal the checker returns when that step is moved one place earlier.

A backend switch redraws the outline of the same book: the OTP GenServer (its mailbox, and the `handle_call` and `handle_info` clauses), the pure state machine, or the C, Rust, or Zig signature and closed layout. The switch reads the outline that emitter already builds. It does not check the book again, and it does not write code.

The explorer does not emit, and it does not change the wall.

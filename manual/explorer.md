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
{:muro_visor, "~> 0.3.0"}
mix deps.get
mix muro.ui path.muro
```

From a checkout of this repository the task lives in `ui/`:

```
cd ui && mix deps.get && mix muro.ui path.muro
```

The page listens on port 4017. `mix muro.ui` prints the URL of the address it binds and opens it: `http://127.0.0.1:4017/` for IPv4 loopback, `http://[::1]:4017/` for an IPv6 address, and `http://localhost:4017/` for a hostname. It opens on the meetings. Each meeting is listed under its base session, in source order: the name, the two conforms, the base session, the step count, and a refinement such as `{d ≤ w}` when the session carries one. Choosing a meeting patches `?meet=` onto the URL, so `http://127.0.0.1:4017/?meet=wire` opens that meeting. The focused view is a sequence diagram of the configuration graph the checker recorded. Two lanes are the two conforms, each headed by its name and its session (the base session, or `dual` of that base). Each step is a row: an arrow from the sender to the receiver, labelled with the value or type sent, and the choice branch for `choose` and `offer`. A halted state is a terminal row (`done`, `stop`, or `end`). Beside it, a context panel shows the session, its dual, the two conforms with their source locations, and a checked badge. A click on a conform opens that definition in Detail.

All definitions, at `?view=all`, is the whole book: one node for each spec, evidence, and run, and one edge for each use. Nodes sit in ranks along those edges, and each edge has its own path. A use of a definition by itself is a loop. A session is a compound node. Each meeting lays out its configurations inside that box, with the transition between configurations labelled. The positions come from the same walk the checker uses. The graph pane scrolls and zooms. Detail and Outline sit beside it.

`?view=all&grades=on` lays the checker's grades over that graph. A definition whose recorded quantities are erased is faded. A definition that still computes stays at full opacity. A binder with no grade is left as it was, and it is not treated as erased. The legend names runtime and erased, and names `%1` or reuse when a binder carries that quantity. The quantities are the ones `Muro.Grade` stored on the checked book. Turning the overlay off returns to `?view=all`.

Synthesis, at `?view=synth`, draws the state graph of an environment. The states are the constructors of `State`. An edge is a step the book writes from one of those constructors to another. Opening the view does not run a search. A report from `mix muro.synth --json`, saved and opened with `?trace=`, shows the version-space sizes, the surviving predicate, and whether the run was certified. The carriers named in `cex` are lit on the last round. A state is ranked when that report is certified, and unsettled otherwise. A report may also carry `rounds` and `states` beside the keys the command already prints. `rounds` is a list of `{round, versions, cex}`, and each round's `cex` is the states that were counterexamples on that round. `states` is a list of `{name, status, certificate}`, and `status` is `ranked` or `unsettled`. When those keys are absent the view uses the keys the command already prints. A later search can add the two keys without renaming the others. This version does not record a counterexample on each round inside the search.

Selecting a node, an edge, or a configuration shows the source file, line, and column, and the definition's source at those line numbers, with that place marked. Specs, duals, the outline, and the labels on the sequence and the definition graph are coloured by the muro lexer. A selection can be made with a click or with the keyboard. Selecting an edge also shows the refusal the checker returns when that step is moved one place earlier: the process, the protocol, and the reason. A use that is not a step says there is no refusal.

The outline is split into names, signatures, layouts, and clauses, and each section can be collapsed. A backend switch redraws that outline for the same book, including while a meeting is open: the OTP GenServer (its mailbox, and the `handle_call` and `handle_info` clauses), the pure state machine, or the C, Rust, or Zig signature and closed layout, including each data type's constructor tags and fields. The switch reads the outline that emitter already builds. It does not check the book again, and it does not write code.

The explorer does not emit, and it does not change the wall.

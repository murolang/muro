# muro_visor

A read-only visual explorer for one checked muro book. Version 0.2.0. It is its own Hex package and it depends on `muro ~> 0.20.7`.

The compiler does not start this application, and the muro release binaries do not depend on Phoenix. `muro ui path.muro` prints these install steps and links to [the explorer page](https://muro-lang.dev/docs/explorer).

Add the package to a Mix project, then open a book:

```
{:muro_visor, "~> 0.2.0"}
mix deps.get
mix muro.ui path.muro
```

A published package depends on `muro ~> 0.20.7`. This checkout, and CI, build against the repository instead. From this checkout:

```
cd ui
mix deps.get
mix muro.ui ../examples/meet.muro
```

The page listens on port 4017 and connects its LiveView over `/live`. `mix muro.ui` prints the URL of the address it binds and opens it: `http://127.0.0.1:4017/` for IPv4 loopback, `http://[::1]:4017/` for an IPv6 address, and `http://localhost:4017/` for a hostname. It opens on the meetings, grouped under the base session in source order. A row names the meeting, the two conforms, the base session, the step count, and a refinement such as `{d ≤ w}` when the session carries one. Choosing a meeting patches `?meet=` onto the URL. The focused view draws the configuration graph the checker recorded as a sequence: two lanes, one per conform, and one row per step, labelled with the value or type sent and the choice branch. A halted state is a terminal row. A context panel shows the session, its dual, the two conforms and their source locations, and a checked badge. Detail and Outline sit beside it. The outline's names, signatures, layouts, and clauses are separate sections. A backend switch (OTP, FSM, C, Rust, Zig) redraws the outline from `Muro.Emit.outline/3` and does not check the book again, including while a meeting is open. C, Rust, and Zig layouts include constructor tags and fields. All definitions, at `?view=all`, is the whole book: one node for each spec, evidence, and run, placed in ranks along the use edges, and each edge has its own path. A session is a compound node. Each meeting lays out its configurations inside that box, with a labelled transition between them. The graph pane scrolls and zooms. A click or a key selects a node, an edge, or a configuration and shows its source location. An edge also shows the refusal for taking that step out of order, including the process and the protocol.

Nothing here emits code or writes the book. Tests need only Elixir: the page is server-rendered SVG, and the LiveView client scripts are the ones Phoenix already ships. There is no Node toolchain.

```
mix format --check-formatted && mix compile --warnings-as-errors && mix test
```

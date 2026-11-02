# muro_visor

A read-only visual explorer for one checked muro book. Version 0.1.0. It is its own Hex package and it depends on `muro ~> 0.20.5`.

The compiler does not start this application, and the muro release binaries do not depend on Phoenix. `muro ui path.muro` prints these install steps and links to [the explorer page](https://muro-lang.dev/docs/explorer).

```
mix archive.install hex muro_visor
mix muro.ui path.muro
```

From this checkout the dependency is a path override of the repository root:

```
cd ui
mix deps.get
mix muro.ui ../examples/meet.muro
```

The page draws one node for each spec, evidence, and run, and one edge for each use. A session is a compound node whose children are the configurations the meeting proved. A backend switch (OTP, FSM, C, Rust, Zig) redraws the outline from `Muro.Emit.outline/3` and does not check the book again. A click shows the source location. An edge also shows the refusal for taking that step out of order.

Nothing here emits code or writes the book. Tests need only Elixir: the page is server-rendered SVG, and the LiveView client scripts are the ones Phoenix already ships. There is no Node toolchain.

```
mix format --check-formatted && mix compile --warnings-as-errors && mix test
```

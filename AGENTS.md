# AGENTS.md

Muro is an explicit affine dependent type theory built for agents to write. As the agent, you carry the formal verification: every type, motive and proof step is written out and nothing is inferred, so the checker either accepts your file or names each failing definition. A spec never becomes evidence. Evidence never becomes a run. Only `run` terms are emitted, as Elixir (BEAM), as C, as Rust, or as Cortex-M assembly, from the same source.

The canonical contract is [`manual/for-agents.md`](manual/for-agents.md). If this file and that page ever disagree, that page wins.

## Two jobs. Do not mix them.

### Job A: write a Muro program

Do:
- Write a `.muro` file against [`manual/grammar.md`](manual/grammar.md). Put it in `examples/` unless you are asked otherwise.
- **Copy syntax from `examples/`, not from memory.**
- Type every binder. Write every motive.
- Use only the tags `run`, `run internal`, `spec` and `evidence`.
- `pred`, `plus`, `inj-suc`, `plus_suc`, `sym` and `cong` are already in scope (`lib/muro/prelude.muro`). If you redefine one, your definition replaces it, and any prelude definition that refers to it is dropped.
- Use `?` only while a term is unfinished. A hole always fails, and it prints `expected` and `context` for you to fill.
- Read every error. Parse and check errors start with `line:col`, and the failing definitions are listed in book order.
- For a library with `param` entries, check it through a file that supplies the params (see [Params](manual/language.md#params)).

Do not:
- Edit `agda/`, `lib/muro/*.ex` or `lib/mix/tasks/`.
- Invent tags, implicits, metavariables or tactics.
- Promote a spec to evidence, or evidence to run.
- Add a fourth term representation.

### Job B: change the type theory

Follow [`manual/extending.md`](manual/extending.md). The order is mandatory: Agda syntax → subst → check → `make agda` → Elixir mirror → `mix test` and `mix muro.check`. If you are doing Job A, you are not doing Job B.

## Commands

```
mix deps.get
mix test
mix muro.check                              # whole book
mix muro.check path.muro                    # one file
mix muro.check --fuel 20000 path.muro       # after "out of fuel"
mix muro.mutate path.muro                   # which evidence constrains each run
mix muro.mutate path.muro --only half --json
mix muro --version                          # the copy that ran
mix muro.init                               # muro.exs and priv/muro/
mix muro.emit path.muro --backend fsm           # one state machine per session, on stdout
mix muro.emit path.muro --backend exunit       # ExUnit suite on stdout; a param library is accepted
mix muro.emit path.muro --backend exunit --imports  # also that book's direct imports
mix muro.gen                                 # write the modules the manifest names
mix muro.gen --check                         # fail when a committed module and its book disagree
mix muro.deps.get                            # fetch muro_deps/ and write muro.lock
make agda                                   # Job B only; needs vendor/agda-stdlib v2.3
```

The archive installs those tasks in any directory: `mix archive.install hex muro`. A pinned version: `mix archive.install hex muro 0.18.4`. From a checkout: `mix archive.build && mix archive.install muro-0.18.4.ez`. From GitHub: `mix archive.install github murolang/muro`. Inside a project that depends on muro, the project's copy runs after `app.start`. Inside any other project, or outside a project, the archive's copy runs and the host is neither compiled nor started. A script run with `mix run --no-start` does not see the archive; use the Mix tasks.

Success from `mix muro.check`: a `Muro v…` line, then `All terms check. Evidence never becomes a run.` A book that imports packages then prints one `conforms to <name> <version> (sha256 <hash>)` line per package. See [Packages](manual/packages.md).

## Emit

Emit only after a successful check. Spec and evidence are omitted; erased arguments are dropped.

```
mix muro.emit path.muro                     # Elixir (default); module name from the file stem
mix muro.emit path.muro --backend exunit    # ExUnit suite on stdout; test module is the stem plus Test
mix muro.emit path.muro --backend c         # <name>.h and <name>.c; a Nat run is also a NIF
mix muro.emit path.muro --backend rust      # <name>.rs
mix muro.emit path.muro --backend asm       # <name>.s, Cortex-M0, Nat run
mix muro.emit path.muro --backend fsm       # one state machine per session, on stdout
```

```elixir
{:ok, src} = Muro.emit_file("examples/your_file.muro", Foo)   # Elixir source
{:ok, files} = Muro.emit_c("examples/your_file.muro")         # .h and .c, then the Nat NIF paths
{:ok, files} = Muro.emit_rust("examples/your_file.muro")      # .rs
{:ok, files} = Muro.emit_asm("examples/your_file.muro")       # .s
```

A `repr` makes `mix muro.emit` also write `decode_<type>/1`, `decode_<type>/2`, and `encode_<type>/2`. Decode returns `{:ok, value, table}`. Encode takes that table. See [Host representations](manual/repr.md).

`--backend exunit` prints one test module for the book's closed equations. A file of unsupplied `param`s is accepted only by this backend. `--imports` also collects the files that book imports directly, and it is an error with any other backend. The tests call an implementation the host names. See [Closed equations as tests](manual/exunit.md).

The C backend refuses some terms that the Elixir backend accepts. `I64`, `F32` and `Tensor` are refused as `c:machine`. Unapplied lambdas, definitions passed as values and calls of local functions are refused as `c:lambda`, because C has no closures. A raw `ν`, `Always` or `~` inside a `run` is refused as `c:stream`. Allocation goes through `MURO_ALLOC`, which is `malloc` unless you define it. An exported run of `Nat` arguments and a `Nat` result is a NIF; that build defines `MURO_ALLOC` as one block and resets it when the call returns. The Rust backend prints the same image and refuses a term the C backend refuses. `rustc` translates that text. The Cortex-M backend prints the Nat fragment of that image. The assembler translates that text. See [Emit](manual/emit.md).

## Committed modules

`mix muro.gen` writes a module from a manifest (`muro.exs`, or a `:muro` key in `mix.exs`) into the path the manifest names. The module name is the manifest's alias, passed to `Muro.emit_file/3`. The file starts with a header that names the book, the Muro version, the book sha256, and the body sha256. Do not edit that file by hand. The `.muro` file is the source. Run `mix muro.gen` after changing it. `mix muro.gen --check` fails when the committed file and the book disagree. `muro:` must equal the running version. `mix muro.init` creates the manifest and prints a note for the project's agent instructions. It does not write that file. See [Committed modules](manual/gen.md).

## Pitfalls seen in practice

- **A multi-line `match` used as an argument needs parentheses.** Wrap the whole `match … | … => …` in `( … )`.
- **Reusing an affine variable inside a recursive `def` can be reported as `recursive call does not descend on a smaller argument`.** Before you change your recursion, check whether a non-reusable variable is used twice.
- **`match` branches must follow the order the constructors were declared in.**
- **Erased guards cannot rule out `run` branches.** An `evidence`/erased argument does not make a branch of a `run` term unreachable. Encode the invariant in a run-mode indexed type instead (see [Indexed data](manual/indexed.md)).
- **`Nat` is unary (Peano), so large constants are slow** to check and to run. Use `I64` where machine numbers fit (see [Machine numbers](manual/machine.md)).
- **`out of fuel` is not acceptance, and it is not a type error.** The checker gave up reducing. Raise `--fuel` and check again.

## Manual

[Start](manual/start.md) · [Marks](manual/marks.md) · [The wall](manual/wall.md) · [Terms](manual/language.md) · [Sessions](manual/sessions.md) · [Identity](manual/identity.md) · [Data](manual/data.md) · [Indexed data](manual/indexed.md) · [Streams](manual/streams.md) · [Either and Dec](manual/either.md) · [Machine numbers](manual/machine.md) · [Emit](manual/emit.md) · [State machines](manual/fsm.md) · [Mutation](manual/mutate.md) · [Closed equations as tests](manual/exunit.md) · [Committed modules](manual/gen.md) · [Host representations](manual/repr.md) · [Packages](manual/packages.md) · [Grammar](manual/grammar.md) · [Examples](manual/examples.md) · [CSHRL](manual/cshrl.md) · [For agents](manual/for-agents.md) · [Extending](manual/extending.md) · [Limits](manual/limits.md)

Machine-readable index: [`manual/manifest.yml`](manual/manifest.yml). Canonical book: `examples/half_ok.muro`.

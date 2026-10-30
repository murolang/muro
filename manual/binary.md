---
title: The executable
slug: binary
order: 16
summary: The self-contained muro binary, muro.toml, gen for C, Rust, and assembly, init, and muro skills add.
---

# The executable

In brief: `muro` is a self-contained executable. It carries its own Erlang runtime, so a Rust, C, or embedded project can check, emit, and commit modules with no Elixir and no Erlang installed. The checker, the emitters, and `Muro.Gen`, `Muro.Init`, and `Muro.Manifest` are the same code the Mix tasks call. The Mix tasks stay. `mix archive.install hex muro` stays the install for an Elixir project.

## Install

Release assets are one file per target, named `muro-<version>-<os>-<arch>`, with a `.sha256` file beside each:

```
muro-0.19.6-macos-aarch64
muro-0.19.6-macos-x86_64
muro-0.19.6-linux-x86_64
muro-0.19.6-linux-aarch64
```

The Linux binaries are built against musl, so one file runs on glibc and on Alpine. The asset name does not contain `musl`.

[mise](https://mise.jdx.dev/) installs the asset for the host:

```
mise use -g github:murolang/muro@0.19.6
```

`mise install muro` from the mise registry follows once the assets exist. A tag `v*` builds the four files, then smokes the Linux binary in a container with no Elixir and no Erlang. The assets are attached to the GitHub release only after that smoke succeeds. A failed smoke publishes nothing. The Hex package's dependencies are unchanged. Burrito builds the executable and is not a runtime dependency of the package.

```
muro --version
```

prints `Muro v` and the version, the same line as `mix muro --version`.

## Commands

```
muro check path.muro
muro emit path.muro [--backend elixir|c|rust|asm|otp|fsm|exunit] [--node NAME] [--imports]
muro gen
muro gen --check
muro init [--ci github] [--backend BACKEND] [--cargo-metadata]
muro skills add
muro deps.get
muro mutate path.muro [--only NAME] [--json] [--fuel N] [--max-mutants-per-def N] [--max-survivors N]
muro --version
```

Each command takes the same flags as its Mix task and prints the same lines. Where a Mix task raises, the executable prints that message on stderr and exits 1. `muro mutate` exits 1 when survivors exceed `--max-survivors` and exits 2 when the book does not check, as `mix muro.mutate` does. Each classified mutant prints `<id> <operator> <outcome>` on standard error. A run that builds no mutants prints no such line.

The executable never compiles a host application and never starts one. That holds outside a Mix project and inside one. A suite that calls an `impl:` keeps using `mix muro.*`, because that suite needs the host compiled. The executable does not load a Mix project, so a lone `:muro` key in `mix.exs` is not a manifest for it. Write `muro.exs` or `muro.toml`. `muro init` in a directory with `mix.exs` writes `muro.exs`.

`muro deps.get` fetches Hex packages over HTTPS. The executable ships `:public_key`, `:ssl`, `:inets`, `:crypto`, and `:asn1` loaded and not started. The fetcher starts them. Mix records the code path before the boot script loads those applications, so the fetcher loads the copies beside `:muro` in the release. They are not extra applications of `:muro`, and they are not dependencies of the Hex package.

## C

`muro emit path.muro --backend c` writes `<name>.h` and `<name>.c` next to the book. `<name>` is the book stem. The executable does not load the host Mix project, so those two files are the whole output. Nothing in that output mentions `elixir_make`.

`mix muro.emit path.muro --backend c` writes the same `.h` and `.c`. When the working directory is the loaded Mix project, it also writes the NIF through `elixir_make`. The C bytes are the same in both cases. A project that wants the NIF adds `{:elixir_make, "~> 0.10", runtime: false}` and runs the Mix task. See [Emit](emit.md).

`muro gen` with `kind: :c` writes the `.c` target and the `.h` beside it. The source includes that header by the target stem (`src/rounding.c` from `muro/half.muro` includes `rounding.h`). It does not build a NIF.

## muro.toml

`muro.exs` stays the Mix manifest. A project without `mix.exs` uses `muro.toml` at its root. A `Cargo.toml` may carry the same table as `[package.metadata.muro]` instead of a separate file. Loading more than one of `muro.exs`, a `:muro` key, `muro.toml`, and `[package.metadata.muro]` is an error, and the message names each of them:

```
muro.toml and [package.metadata.muro] in Cargo.toml both define a manifest
```

Three or more end with `all define a manifest`.

```toml
muro = "0.19.6"
fuel = 2000          # optional
backend = "rust"     # optional default for [[modules]]

[[modules]]
book = "muro/rounding.muro"
target = "src/rounding.rs"

[muro_deps.rounding]
git = "https://example.com/rounding.git"
tag = "v1"
```

`muro` is required. `fuel` is an optional positive integer. The default is the fuel `muro check` uses. `backend` is optional. It is `elixir`, `c`, `rust`, `asm`, `fsm`, or `exunit`, and it is the kind of every `[[modules]]` entry that omits `backend`. An entry that omits `backend` when the file omits it too is `modules entry N: missing backend`, and the message names the line.

`book` and `target` are required. Paths are relative to the project root. A book or a target outside the project is refused, a missing book is refused, and a duplicate target is refused. The errors name the entry index, as they do for `muro.exs`.

`module` is an alias string (`"MyApp.Billing.Rounding"`). It is required for `elixir`, `fsm`, and `exunit`. A `c`, `rust`, or `asm` entry omits it. The `c` target ends with `.c`, and the header is written beside it with the same stem (`src/rounding.c` also reserves `src/rounding.h`). That path is checked as a target before generation, including when it is already a directory. The error names the entry index. The `rust` target ends with `.rs`. The `asm` target ends with `.s`. A wrong suffix is `modules entry N: target for kind :rust must end with .rs`.

`muro_deps` is the same set of packages as `muro_deps:` in `muro.exs`. Each name is a table:

```toml
[muro_deps.shared_wire]
git = "https://github.com/acme/shared-wire"
tag = "v1.2.0"
root = "priv/muro"

[muro_deps.pricing]
hex = "pricing_rules"
requirement = "~> 2.0"
```

`git` takes optional `tag`, `ref`, and `root`. `hex` requires `requirement`. The rules in [Packages](packages.md) apply, including the refusal when `tag` and `ref` are both set.

`modules = []` is a valid empty list. A non-empty array is outside the subset below, so entries are `[[modules]]` tables.

## TOML subset

The reader accepts tables, arrays of tables, basic strings, integers, booleans, empty arrays, and `#` comments, including a comment after a value. Table headers may contain dots: `[muro_deps.name]`, `[[package.metadata.muro.modules]]`.

A construct outside that subset is refused. The message names the file and the line. The reader does not guess. Dotted keys in an assignment (`a.b = 1`), inline tables, literal strings, multiline strings, floats, datetimes, and non-empty arrays are refused.

In a `Cargo.toml`, tables other than `[package.metadata.muro]` and its children are skipped. A header there may quote a key with a basic or literal string, including `[target.'cfg(unix)'.dependencies]` and `[target."x86_64-pc-windows-msvc".dependencies]`. The quote form follows the header being opened, so that target table is skipped when it comes immediately after `[package.metadata.muro]`. Skipping follows strings, multi-line strings, arrays, and inline tables, so a `[` inside any of those is not a table. The muro table is read with the same subset: a literal string, a quoted header key of that form, and every other construct the subset does not include are refused there. A `Cargo.toml` with no `[package.metadata.muro]` is not a manifest.

## gen

`muro gen` and `mix muro.gen` write `elixir`, `exunit`, `fsm`, `c`, `rust`, and `asm` targets. In `muro.exs` the native entries may omit the module:

```
{"muro/rounding.muro", "src/rounding.rs", [kind: :rust]}
{"muro/rounding.muro", "src/rounding.c", [kind: :c]}
{"muro/rounding.muro", "src/rounding.s", [kind: :asm]}
```

A missing `kind:` in `muro.exs` is still `:elixir`.

The header is the same two lines and the same hashes as an Elixir target. A C source includes the header written beside the target, so `src/rounding.c` from book `muro/half.muro` includes `rounding.h`. The comment mark is `// ` for C and Rust, including the `.h`, and `@ ` for Cortex-M assembly. Formatting is left alone for these three kinds, so the body hash is the sha256 of the emitter's text. `muro gen --check` reports a missing, stale, hand-edited, or differing target, or a header that names another version, with the same messages it uses for Elixir. The `.h` beside a C target is checked the same way. See [Committed modules](gen.md).

## init

`muro init` looks at the working directory, in this order, and writes one manifest. The manifest pins `muro` to the running version and has one commented example entry for the detected backend.

| Found | Writes | Default backend |
| --- | --- | --- |
| `mix.exs` | `muro.exs` and `priv/muro/` | elixir |
| `Cargo.toml` | `muro.toml` and `muro/` | rust |
| `CMakeLists.txt`, `meson.build`, or a `Makefile`, and neither `mix.exs` nor `Cargo.toml` | `muro.toml` and `muro/` | c |
| none of these | `muro.toml` with `modules = []`, and `muro/` | none |

`--backend asm` overrides the detected backend and stores it as the manifest's top-level `backend`, so `muro skills add` and later commands use `asm`. On `muro.exs` the key is `backend: :asm`. On `muro.toml` and `[package.metadata.muro]` it is `backend = "asm"`. `--backend elixir` stores that key too. Without `--backend`, a Mix project still omits it. The flag does not change which file is written. There is no detection of embedded projects. `--backend` accepts `elixir`, `c`, `rust`, `asm`, `fsm`, or `exunit`.

`--cargo-metadata` on a directory with `Cargo.toml` appends `[package.metadata.muro]` and writes `muro/`. It does not write `muro.toml`. Without a `Cargo.toml` it exits 1 and writes nothing.

`muro init` never overwrites and never writes a second manifest. Before it writes, it looks for `muro.exs`, `muro.toml`, and `[package.metadata.muro]` in `Cargo.toml`. When any of those is already a manifest, every file stays as it is. The command prints a unified diff of that manifest in its own format, against what init would write in that same format, and exits 0. `muro init` followed by `muro init --cargo-metadata` does not append a Cargo table beside `muro.toml`. A Mix directory that already has `muro.toml` does not gain `muro.exs`.

`mix muro.init` still refuses to overwrite `muro.exs` or a `:muro` key. It prints a note. The note says generated files are not edited by hand, and it points at `muro skills add`.

It does not write `AGENTS.md`.

`--ci github` writes `.github/workflows/muro.yml` only when that file is absent. On the executable, the job installs `muro-<version>-linux-x86_64` at the pinned version and runs `muro gen --check`. On `mix muro.init --ci github`, the job installs the archive and runs `mix muro.gen --check`, as [Committed modules](gen.md) describes. An existing workflow file is left in place. When the manifest is new and the workflow file exists, init exits 1 and names `.github/workflows/muro.yml`. When the manifest already exists, init prints the diff and does not add a workflow.

## skills add

```
muro skills add
```

writes the agent section into `AGENTS.md`, and into `CLAUDE.md` when that file already exists. It creates `AGENTS.md` when `AGENTS.md` is missing. It never creates `CLAUDE.md`. It touches nothing outside its block.

The block is delimited by `<!-- muro:begin -->` and `<!-- muro:end -->`. A marker counts only as a whole line. A trailing carriage return is allowed, so a CRLF file is recognised. A mention of either marker inside a sentence is not a marker. A rerun replaces the lines between the markers and nothing else, keeps the file's line endings, and the file is byte-identical. A file with no markers gets the block appended, in those same line endings. A file with unbalanced markers is refused with `<file>:<line>: unbalanced muro marker`, and neither file is written.

The wording comes from [For agents](for-agents.md) at build time, so the executable carries it. That file is part of the Hex package, so compiling the package, or an archive built from it, reads the same source. The wording is the same for every backend. The commands and the example anchor are filled from the manifest's `backend`, or from the backend `muro init` would detect. The block states the two jobs (spec and evidence; `run` is what is emitted), the wall, the commands for this project (`muro check`, `muro emit` or `muro gen`, and `muro gen --check`), that every binder is typed and every motive is written, that generated files are not edited by hand, and a pointer to the nearest example in [Examples](examples.md).

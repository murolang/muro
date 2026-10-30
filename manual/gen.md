---
title: Committed modules
slug: gen
order: 15
summary: A manifest names each book, module, and target. mix muro.gen writes the module. mix muro.gen --check fails when the file and the book disagree.
---

# Committed modules

In brief: a project commits the Elixir a book emits. `muro.exs` names the module and the path. `mix muro.gen` checks every book, formats the module, and writes it. `mix muro.gen --check` writes nothing and fails when the committed file and the book disagree. The running Muro version must equal `muro:`.

`mix muro.emit` prints a module. It does not choose a path under `lib/`, format with the project's `.formatter.exs`, or record which book the file came from. This page is that step.

A `repr` is part of the committed module. `decode_<type>/1`, `decode_<type>/2`, and `encode_<type>/2` sit next to the run functions. Decode returns `{:ok, value, table}`. Encode takes that table. Change the repr and `mix muro.gen --check` fails, because the book hash changed. See [Host representations](repr.md).

## Manifest

`muro.exs` at the project root is a keyword list. `Code.eval_file/1` evaluates that file and nothing else. A Mix project may instead put the same keyword list under the `:muro` key in `mix.exs`. If both exist, loading stops and names both.

```
[
  muro: "0.19.1",
  fuel: 2000,
  modules: [
    {"priv/muro/rounding.muro", MyApp.Billing.Rounding, "lib/my_app/billing/rounding.ex"},
    {"priv/muro/rounding.muro", MyApp.Billing.RoundingTest, "test/rounding_test.exs",
     [kind: :exunit, impl: MyApp.Billing.Rounding]}
  ]
]
```

`muro:` is required. It is the version string the books are checked with. `fuel:` is optional. The default is the fuel `mix muro.check` uses (`Muro.Check.default_fuel/0`, 2000). `modules:` is required. It may be empty. Each entry is `{book_path, module, target_path}` or `{book_path, module, target_path, opts}`. A 3-tuple emits Elixir. `opts` is a keyword list: `kind: :elixir` (the default), `kind: :exunit`, or `kind: :fsm`, and for `:exunit` an optional `impl:` alias, the implementation the suite calls by default, and an optional `imports:` boolean. `imports: true` also collects the closed equations of the files that book imports directly. The default is `false`. `imports:` on an `:elixir` entry is an error, and a non-boolean is an error. Unknown options, an unknown kind, `impl:` on an Elixir entry, and an `impl` that is not an alias are errors, and the message names the entry index. `impl:` and `imports:` on a `:fsm` entry are the same error: both are only valid for `kind: :exunit`. The page for the suite is [Closed equations as tests](exunit.md). The page for the state machine is [State machines](fsm.md).

`muro_deps:` is optional. It names the git and Hex packages `import "pkg:..."` loads. `mix muro.deps.get` fetches them into `muro_deps/` and writes `muro.lock`. A project that only checks books can list `muro_deps:` without `muro:` or `modules:`; this task still requires those two. See [Packages](packages.md).

Paths are relative to the project root. A book or a target that leaves the project is refused, and so is a missing book, a target that is a directory, a duplicate target, or a module that is not an alias atom (`MyApp.Billing.Rounding`). `lib/./a.ex` and `lib/nested/../a.ex` are the same target. The errors name the entry.

With no Mix project, the root is the working directory. Inside a Mix project, the root is the directory of `mix.exs` when the working directory is that project or a subdirectory.

## mix muro.gen

```
mix muro.gen
```

The task checks every listed book with the manifest's fuel before it emits anything. If any book fails, it prints each failure and writes nothing. The line ends with `muro.gen wrote nothing`.

Otherwise it emits each module, formats it, adds the header, and writes the target, creating directories. One line per target:

```
written lib/my_app/billing/rounding.ex
unchanged lib/my_app/billing/rounding.ex
```

A book that loaded packages prints each `conforms to` line under that target, indented by two spaces. An ExUnit target prints one more line per skipped equation, after its `written` or `unchanged` line and after any `conforms to` lines:

```
skipped test/rounding_test.exs: step-ok (priv/muro/rounding.muro:8): step is run internal and is not exported
```

`--check` does not print those lines. The same lines are comments in the generated file, inside the body, so the body hash covers them. A book change that only alters the skipped set changes the book hash, and the stale message below reports it.

An unchanged target is not rewritten. Its modification time stays.

The module name is the manifest's alias. `Muro.emit_file/3` takes that atom as its second argument. An ExUnit entry passes the same atom to `Muro.emit_exunit/3` as the test module. The suite's default implementation is the book's file stem unless `impl:` names another. The alias itself is the name in the entry, whatever the file stem is.

Formatting uses the project's `.formatter.exs` when that file exists (`Mix.Tasks.Format.formatter_for_file/2` with `root:` set to the project). Otherwise it uses `Code.format_string!/2`. The header is comments, so the formatter leaves it on its own lines. The file ends with one newline. There is no timestamp and no absolute path. Paths in the header use `/`.

## Header

The first two lines of each target:

```
# Generated by Muro 0.19.1 from priv/muro/rounding.muro (book sha256 <hex>, body sha256 <hex>).
# Do not edit; change the .muro file and run mix muro.gen.
```

The book hash is the lowercase hex sha256 of the book together with every file it imports, including `pkg:` imports. A package file's path in the hash is `muro_deps/<name>/<path>`. The prelude is not in the hash, and neither is `muro.lock`. The version pin covers the checker, the emitter, and the prelude. The conforms line covers the package version. A file is included once. A cycle includes each file once. A file that does not parse contributes its own bytes and no further imports. A missing import is omitted. Paths are relative to the project root, with `/` separators, sorted lexicographically. An import outside the project is a `..` path from that root. Each file contributes its relative path, a zero byte, its bytes, and a zero byte.

A book that loaded packages has one line per package between the two lines above:

```
# Conforms to shared_wire 1.2.0 (sha256 <hex>).
```

A book that imports no package keeps exactly those two lines. The body is every byte after the `# Do not edit` line, including the single trailing newline. The body hash is the sha256 of that body.

The module still contains the emitter's line `# Generated by Muro. Evidence never becomes a run.` That line is part of the body.

## Version pin

`mix muro.gen` and `mix muro.gen --check` refuse to run when `muro:` differs from the running version. The process exits non-zero. The message names both versions:

```
muro version mismatch: manifest says 0.16.73, running 0.19.1
```

A mismatch is an error. A different checker can accept a different book or emit different text.

## mix muro.gen --check

```
mix muro.gen --check
```

The task writes nothing. When every book checks and every target is the bytes `mix muro.gen` would leave in place, it prints:

```
ok
```

Otherwise it exits non-zero and lists every problem. Each line names the target and the book.

A book that does not check:

```
lib/my_app/billing/rounding.ex: priv/muro/rounding.muro does not check
<the checker's error>
```

A missing target:

```
lib/my_app/billing/rounding.ex: missing target for priv/muro/rounding.muro
```

A stale target. The header's book hash differs from the current book. The book changed and nobody regenerated:

```
lib/my_app/billing/rounding.ex: stale target; priv/muro/rounding.muro changed (book sha256 <header>, current <current>)
```

A hand-edited target. The book hash matches, and the body no longer matches the body hash in the header:

```
lib/my_app/billing/rounding.ex: hand-edited target; priv/muro/rounding.muro is unchanged and the body no longer matches its recorded sha256
```

A target that differs from what the book emits now, while both recorded hashes are still consistent with the file. The header was removed, or the body matches its recorded hash and is not what the book emits:

```
lib/my_app/billing/rounding.ex: differs from what priv/muro/rounding.muro emits
```

A header that names a different Muro version:

```
lib/my_app/billing/rounding.ex: header says Muro 0.0.1, running 0.19.1, from priv/muro/rounding.muro
```

A book that fails and a target that is stale are both reported. A hand edit is reported only when the book hash matches. A version mismatch is not also reported as "differs".

## mix muro.init

```
mix muro.init
mix muro.init --ci github
```

`mix muro.init` creates `muro.exs` and `priv/muro/`. `muro:` is the running version. `modules:` is empty, with one commented example entry. An existing `muro.exs`, or a `:muro` key already in `mix.exs`, is left untouched. The message names what it refused.

`--ci github` also writes `.github/workflows/muro.yml`. An existing workflow file is left in place, and the manifest is not written either.

The job checks out the project, sets up Elixir 1.20.4 and OTP 29.1 (this repository's `mise.toml`), installs the archive, and runs `mix muro.gen --check`. The install line is:

```
mix archive.install hex muro 0.19.1 --force
```

The version is the one in the manifest, so the job installs the release that `muro:` names. `--force` skips the install question. The job does not install the checkout build or the GitHub form. `mix archive.install hex muro` without a version installs the latest release.

The task prints a note to paste into the project's agent instructions (AGENTS.md or similar):

```
Generated files are not edited by hand. The .muro file is the source. Run mix muro.gen after changing it.
```

It does not write that file.

The three tasks run from the archive, with no Mix project, and inside a project that depends on muro. When a project depends on muro and the archive is also installed, Mix uses the project's copy.

Next: [Host representations](repr.md).

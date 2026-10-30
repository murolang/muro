---
title: Packages
slug: packages
order: 15
summary: Import a book from a git or Hex package at the version muro.lock records.
---

# Packages

A path import is enough inside one repository. It is not enough when two programs have to follow one definition: a protocol both ends use, or a rule each service implements. Copying the book lets the copies drift, and a check of one copy says nothing about the other.

`import "pkg:shared_wire/wire.muro"` loads that file from a package named in the manifest, at the version `muro.lock` records. The checker refuses the book when the file's bytes differ from the lock.

## Manifest

`muro_deps:` lives in the same manifest as [`mix muro.gen`](gen.md): `muro.exs` at the project root, the `:muro` key in `mix.exs`, `muro.toml`, or `[package.metadata.muro]` in `Cargo.toml`. If more than one of these defines a manifest, loading stops and names each of them. The TOML shape is [The executable](binary.md).

A project that only checks books can list `muro_deps:` and omit `muro:` and `modules:`. `mix muro.gen` still requires those two keys.

```elixir
[
  muro_deps: [
    shared_wire: {:git, "https://github.com/acme/shared-wire", tag: "v1.2.0"},
    pricing: {:hex, "pricing_rules", "~> 2.0"}
  ]
]
```

Names are atoms matching `[a-z][a-z0-9_]*`, and they are unique.

A git spec is `{:git, url}` or `{:git, url, opts}`. `{:git, url}` means `{:git, url, []}`. `opts` may include `tag: "v1.2.0"`, `ref: "main"`, or neither, and it may include `root: "priv/muro"`. Leaving out both `tag:` and `ref:` follows the remote's default branch. `ref` is a branch, a tag, or a commit. Naming both `tag:` and `ref:` is an error. `root` is an optional relative directory inside the repository; the default is `"."`, the repository root. The url is a non-empty string with no newlines and does not start with `-`. `tag`, `ref`, and `root` do not start with `-`. `root` is relative and has no `..` or empty segment. Any other option is refused, and the message names the key.

A default branch needs no name. Either of these follows it:

```elixir
shared_wire: {:git, "https://github.com/acme/shared-wire"}
```

```elixir
shared_wire: {:git, "https://github.com/acme/shared-wire", root: "priv/muro"}
```

`{:git, url}` and `{:git, url, []}` are one dependency. The lock stores the normalized spec, so switching spelling is not a change. The spec floats with the default branch, the way a branch `ref:` floats with that branch: `mix muro.deps.get` resolves it again, and the lock pins the commit. `mix muro.check` and `mix muro.gen` do not resolve it again.

A Hex spec is `{:hex, "package_name", "~> 2.0"}`. The requirement is what `Version.parse_requirement/1` accepts. A Hex package ships its books under `priv/muro/`. That directory is the package root, and it is not configurable.

## mix muro.deps.get

```
mix muro.deps.get
```

The task fetches every package, copies regular `.muro` files into `muro_deps/<name>/`, and writes `muro.lock`. There are no package arguments. A Hex file `priv/muro/rules.muro` is `muro_deps/pricing/rules.muro`. A git dependency uses the same layout under its `root`. Symlinks and other non-regular files are refused, and so is a path that is absolute or contains `..`. A package with no `.muro` file is refused.

Fetching happens in a temporary directory. The task replaces `muro_deps/<name>/` and writes the lock only after every package has been checked. A failure leaves both as they were, and the message says so. `muro_deps/<name>/` is removed only when the previous lock named that package and the manifest no longer does. Other directories under `muro_deps/` stay.

The report is one block per package, in name order. A package the manifest dropped is a `removed <name>` line before those blocks:

```
removed old_wire
fetched shared_wire 1.2.0 (2 files)
  added wire.muro
  changed rules.muro (sha256 <old> -> <new>)
  removed gone.muro
wrote muro.lock
```

A second run that resolves the same bytes prints `muro.lock unchanged` and no file lines. With no `muro_deps:` the task prints `nothing to fetch`, removes the packages the lock named, and prints `removed muro.lock` when it deletes the file.

`mix muro.check` and `mix muro.gen` do not run this task. They do not use the network and they do not run `git`.

Git packages are cloned with the `git` CLI. A tag or a branch is `git clone --depth 1 --branch <name> -- <url> <dir>`. A commit (7 to 40 hex digits) is `git init`, then `git fetch --depth 1 -- <url> <ref>`, then `git checkout --detach FETCH_HEAD`. A spec with no `tag:` and no `ref:` is `git clone --depth 1 -- <url> <dir>`, with no `--branch`, so git checks out the remote HEAD. The branch name is `git rev-parse --abbrev-ref HEAD` in that clone. When that prints `HEAD`, the clone is detached and the name is taken from `git ls-remote --symref <url> HEAD`. A remote that has no default branch fails with `muro_deps entry <name>: remote has no default branch; add tag: or ref:`. `GIT_TERMINAL_PROMPT` is `0`. Arguments are not passed through a shell. No credentials are added beyond what git itself does. If `git` is not on `PATH`, the task stops and says `muro.lock` and `muro_deps/` are unchanged.

The version in the lock, and on the `conforms to` line, is the tag with one leading `v` removed when the rest starts with a digit (`v1.2.0` is `1.2.0`, `vlatest` stays `vlatest`). A `ref` is `<ref>@<first 7 hex chars of the commit>`, or those 7 chars when the ref is itself a commit. A pin-free spec uses the same shape as a branch ref: `<branch>@<first 7 hex chars>`, so the line reads `conforms to shared_wire main@0123abc (sha256 ...)`.

Hex packages are downloaded without the Hex client. Releases come from `HEX_API_URL` (default `https://hex.pm/api`). The tarball comes from `HEX_MIRROR` (default `https://repo.hex.pm`). The request sends `accept` and a `user-agent`. HTTPS uses `verify_peer`, `:public_key.cacerts_get/0`, and the hostname check. A redirect to another host is refused. `:inets`, `:ssl`, and `:public_key` are started by the fetcher, not listed in `:muro`'s `extra_applications`. When Mix is loaded, the fetcher calls `Mix.ensure_application!/1` for those three first, because Mix removes other OTP applications from the code path.

The highest release matching the requirement is selected with `Version.match?/3` and `allow_pre: false`. A pre-release is eligible only when the requirement itself contains a pre-release, so `~> 2.0` does not select `2.1.0-rc.1`, and `~> 2.1.0-rc` can. A release whose `retirement` field is a JSON object is skipped when another matching release is not retired. When every match is retired, the highest retired release is used.

The outer tarball holds `VERSION`, `CHECKSUM`, `metadata.config`, and `contents.tar.gz`. `CHECKSUM` must equal the sha256 of `VERSION <> metadata.config <> contents.tar.gz`, as uppercase or lowercase hex (surrounding whitespace is ignored) or as the raw 32-byte digest. Members that are symlinks, absolute paths, or paths containing `..` are refused. Only regular files under `priv/muro/` whose names end in `.muro` are kept. The lock records the lowercase hex sha256 of the outer tarball, so the pin is the exact download.

Private repositories, organizations, and auth keys are not supported. A 401 from the API says so.

`Application.get_env(:muro, :hex_transport, Muro.Deps.Hex.Http)` selects the module that lists releases and downloads tarballs. That key is a test seam, not a user option.

## muro.lock

Only `mix muro.deps.get` writes `muro.lock`. The file is one comment and one map, so a diff is stable across Elixir versions. Packages are sorted by name. Inside a package the keys are `files`, `resolved`, `source`, and `version`, in that order. Each `.muro` file is one line, sorted by path. Indentation is two spaces. The file uses LF and ends with one newline. There is no timestamp and no absolute path.

```elixir
# muro.lock: written by mix muro.deps.get. Do not edit.
%{
  "pricing" => %{
    files: %{
      "rules.muro" => "3b7e…64 hex chars…"
    },
    resolved: {:hex, "2.1.0", "sha256 of the tarball, 64 hex chars"},
    source: {:hex, "pricing_rules", "~> 2.0"},
    version: "2.1.0"
  },
  "shared_wire" => %{
    files: %{
      "wire.muro" => "9ac1…64 hex chars…"
    },
    resolved: {:git, "0123456789abcdef0123456789abcdef01234567"},
    source: {:git, "https://github.com/acme/shared-wire", [tag: "v1.2.0"]},
    version: "1.2.0"
  }
}
```

`source` is the normalized manifest spec. A pin-free git spec is stored as `{:git, url, []}`, or `{:git, url, [root: ...]}` when `root:` is set. `files` values are the lowercase hex sha256 of each file's bytes. `resolved` for git is the full commit. `resolved` for Hex is the release and the tarball sha256.

The reader parses the file with `Code.string_to_quoted/2` and walks the AST. It accepts maps, lists, 2-tuples, 3-tuples, atoms, binaries, and integers. It does not evaluate the file. Anything else is an error that names `muro.lock` and says to run `mix muro.deps.get`.

## Import

```
import "pkg:shared_wire/wire.muro"
```

The string starts with `pkg:`. The name is a manifest name. The path is relative to the package root, uses `/`, ends in `.muro`, and has no `..`, no empty segment, no leading `/`, and no backslash. Anything else is `bad package import` and shows the string and the file and line.

The project root is the `root:` option of `Muro.check_file/2` and `Muro.emit_file/3`, or the nearest ancestor of the entry book that contains `muro.exs` or `mix.exs`. `mix muro.gen` passes the manifest root. The mix tasks pass nothing and use the ancestor. With no root, the error says no manifest was found and names the directory it started from.

The manifest and the lock are read once per `Muro.check_file/2`. Before a package file is parsed, those bytes are hashed and must equal `files` in the lock. The parsed text is those bytes.

```
muro_deps/shared_wire/wire.muro changed since muro.lock (expected sha256 <lock hash>, found sha256 <actual>; run mix muro.deps.get to fetch it again)
```

The other refusals:

- `no muro.lock for package shared_wire (muro_deps/shared_wire/wire.muro); run mix muro.deps.get`
- `package shared_wire (muro_deps/shared_wire/wire.muro) is not in muro.lock; run mix muro.deps.get`
- `muro_deps/shared_wire/wire.muro is not in muro.lock; run mix muro.deps.get`
- `muro.lock is out of date for shared_wire: manifest says <spec>, lock has <spec>; run mix muro.deps.get`
- a package named in an import but not in `muro_deps:` names the package, the importing file and line, and the manifest file that was read
- `muro_deps/shared_wire/wire.muro is missing; run mix muro.deps.get`

A parse error, a check error, or a duplicate name inside a package is reported at `muro_deps/<name>/<path>:<line>:<col>:`, with `/` separators, relative to the project root. The first such error says `in package <name>`. An ordinary file still prints a path relative to the working directory.

A file inside a package may `import` another file of the same package by a relative path. A relative import that leaves `muro_deps/<name>/` is refused, and the message names both paths. A package file may import another package with `pkg:`. That resolves through the importing project's manifest and lock. Nothing is fetched for a package the consumer did not list.

The same `(package, path)` reached twice is one file: through two packages that both import `pkg:common/c.muro`, or through a relative import and a `pkg:` import of that path. Two packages that each ship their own `c.muro` are two files. A shared declaration name is `duplicate name`, as it is for two ordinary files.

A `param` in a package book works as it does across files. The importing book supplies it with the same tag and a type that converts. Two books in one project can import the same package book and supply different params; each is checked with the params it supplies. An unsupplied param is reported on the import, at the package file's line. A supply with the wrong tag is reported as it is for a file.

`mix muro.emit` inlines the package's definitions into the module, the same way it inlines a file import.

## conforms to

`mix muro.check path.muro` prints one line per package the book loaded, after `All terms check. Evidence never becomes a run.`:

```
conforms to shared_wire 1.2.0 (sha256 <hash>)
```

The version is the lock's `version`. For a pin-free git package the version is `<branch>@<sha7>`. The hash covers the package files this book loaded, not the rest of the package. Each entry is `<name>/<path>`, a zero byte, the file bytes, and a zero byte, sorted by that key, then sha256 as lowercase hex. Two projects that load the same files at the same lock print the same line. A file the book does not import does not change it. A book that imports no package, and `mix muro.check` with no path, print only the version line and the success sentence.

`Muro.conforms/2` returns `{:ok, lines}`. `Muro.check_file/2` still returns `:ok` or `{:error, message}`.

## Generated modules

The book hash used by [`mix muro.gen`](gen.md) includes each package file the book imports. The path in the hash is `muro_deps/<name>/<path>`, relative to the project root. A missing package file is omitted, as a missing import is. `muro.lock` is not in the hash. Changing a locked file and running `mix muro.deps.get` marks every dependent target stale. Editing a file under `muro_deps/` by hand makes the book not check, and `--check` prints that message.

A target whose book loaded packages has one extra header line per package, between the first line and `# Do not edit`:

```
# Conforms to shared_wire 1.2.0 (sha256 <hash>).
```

A book that imports no package keeps the two-line header. `mix muro.gen` prints each conforms line under that target's `written` or `unchanged` line, indented by two spaces. `mix muro.gen --check` still prints `ok` when the target matches. A changed conforms line, with the same body, is `differs from what <book> emits`.

## Publishing

A Hex package lists the books in `files` and keeps them under `priv/muro/`:

```elixir
def project do
  [
    app: :pricing_rules,
    version: "2.1.0",
    package: [
      files: ~w(lib priv/muro mix.exs README.md LICENSE)
    ]
  ]
end
```

`priv/muro/**/*.muro` is the tree `mix muro.deps.get` copies. Other files in the tarball are ignored.

A git package is the repository. The consumer's `root:` names the directory of the `.muro` files. Omit `root` when they sit at the repository root.

## Offline

Commit `muro_deps/` and `muro.lock`. `mix muro.check` and `mix muro.gen --check` then need no network and no `git`. `mix muro.deps.get` needs the network for a remote url, and it needs `git` on `PATH` for a git package. A `file://` url needs `git` and does not need the network.

## What this does not do

There is no registry of Muro packages. Git and Hex are the sources. Private Hex repositories, organizations, and auth keys are not supported. A package that imports another package does not fetch it: the consumer lists that package too. There is no solver across packages. Each spec is resolved on its own, again, every time `mix muro.deps.get` runs: a tag or a ref to the commit it points at now, a pin-free git spec to the current tip of the remote's default branch, a Hex requirement to the highest matching release.

Next: [Grammar](grammar.md).

---
title: Start
slug: start
order: 2
summary: Install, write a .muro file, check it, emit Elixir.
---

# Start

In brief: clone the repo, write a `.muro` file against the [grammar](grammar.md), check it with Mix. Do not change Agda or the Elixir kernel unless you are changing the type theory.

## Install

Elixir via [mise](https://mise.jdx.dev/), then:

```
git clone https://github.com/murolang/muro.git
cd muro
mise install
mix deps.get
mix test
mix muro.check
```

`mix muro.check` with no path checks the built-in book (`Muro.Example.book/0`), which must stay in sync with `examples/half_ok.muro`.

Agda is optional for writing programs. You need it only to rebuild the specification of the calculus:

```
git clone --depth 1 --branch v2.3 https://github.com/agda/agda-stdlib.git vendor/agda-stdlib
make agda
```

## A first file

Create `examples/plus.muro` (or any path). Comments start with `--`.

```
-- comments start with --
def plus : run Π (n : Nat) → Π (m : Nat) → Nat :=
  λ (n : Nat) → λ (m : Nat) →
    match n motive (λ _ → Nat)
      | 0 => m
      | suc np => suc(plus np m)
```

Check it:

```
mix muro.check examples/plus.muro
```

On success the shell prints:

```
All terms check. Evidence never becomes a run.
```

You just wrote a `run` function. `plus` will emit as an ordinary Elixir `def`. `Nat` is Peano: `0` and `suc`.

## What has to be written

Muro will not guess.

1. Every definition has a mode tag: `run`, `run internal`, `spec`, or `evidence`. See [The wall](wall.md).
2. Every binder is typed. There are no implicit arguments.
3. Every `match` writes `motive (λ x → …)` in parentheses.
4. `suc` on a term is `suc(t)` or `suc t`. `suc p` in a pattern is a binder, not an application.
5. Recursion on `run` or `evidence` must go through `match` on one argument and pass a smaller variable from the match at that argument's position. Spec does not check descent.
6. `?` is an unsolved goal. It always fails, with the expected type and the binders in scope. Fill it before the book can check.

A definition is in the book the moment `Parser.parse/1` returns it. The checker sees the whole book. Forward references are allowed.

A refused term starts with `line:col`. Conversion is printed in surface syntax: `cannot convert Nat ≁ {n ≡ 0 : Nat}`.

## Emit

Checking is not running. To see Elixir:

```
iex -S mix
```

```
{:ok, src} = Muro.emit_file("examples/plus.muro", Plus)
IO.puts(src)
```

Only `run` (and `run internal`) appear. Specs and evidence are omitted. `run` becomes `def`; `run internal` becomes `defp`. Details in [Emit](emit.md).

## Unicode and ASCII

The surface accepts both. ASCII aliases are in parentheses in the [grammar](grammar.md).

| Meaning | Unicode | ASCII |
| --- | --- | --- |
| Pi | `Π` | `Pi` |
| Lambda | `λ` | `lam` |
| Arrow | `→` | `->` |
| Identity | `≡` | `==` |
| Product | `×` | `*` |
| Sum | `⊎` | write `Either A B` |
| Stream former | `ν` | `nu` |
| Bisimulation | `~` | `bisim` |
| List nil / cons | | `[]` / `::` |

Identifiers are ASCII: `[A-Za-z_][A-Za-z0-9_-]*`.

## Two jobs

| You want to… | Do this |
| --- | --- |
| Add a Muro program | Write a `.muro` file. Check with `mix muro.check path.muro`. Do not change Agda or the Elixir kernel. |
| Change the type theory | Read [Extending the kernel](extending.md). Agda first. Then the matching Elixir clause. |

Users still only run Mix. Next: [Marks](marks.md).

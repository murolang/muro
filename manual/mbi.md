---
title: MBI images
slug: mbi
order: 27
summary: muro emit --backend mbi writes exactly one exported run, with its binder grades, as a .mbi image. Definitions that run calls are in the image. Writing the file is not acceptance. muro-beam loads the image and checks it again.
---

# MBI images

In brief: `--backend mbi` writes `<stem>.mbi` beside the book only when the book has exactly one exported `run` and that body erases. The file is the image muro-beam loads. It is not Erlang BEAM bytecode. The binder grades stay. A run the entry calls is a closed definition in the image. Data, a pair, a word, or a stream is refused. A refusal writes nothing, and an image already at that path stays byte for byte. Writing the file is not acceptance. muro-beam checks the image again. This backend is not a manifest target. `--backend beam` is refused.

```
mix muro.emit path.muro --backend mbi
muro emit path.muro --backend mbi
```

```
{:ok, files} = Muro.emit_mbi("path.muro")
```

`files` is a list of one path, the `.mbi`. That result is exactly one exported run whose body erased. The image is written only in that case. The bytes go to a temporary file in the same directory and are renamed over `<stem>.mbi`, so the path holds the previous file or the whole image. Any refusal writes nothing and leaves an image already at that path byte for byte. That includes a book that does not check, a book with no exported run (`mbi:entry`), and a book with more than one exported run.

## The file

The file is one line and a trailing newline. Version 1 is a run that calls no definition. Version 2 is a run that calls at least one definition. Boundary version 1 is the boundary the runtime checks the term against. An empty `(defs)` is not written.

```
image    ::= (muro-beam-image 1 (boundary 1) (entry <prog>))
           | (muro-beam-image 2 (boundary 1) (defs <gtm>+) (entry <prog>))
prog     ::= (seq <gtm> (done))
gtm      ::= (gvar <nat>)
           | (gtyp <nat>)
           | (glam <pair> <gtm>)
           | (gpi <pair> <gtm>)
           | (gapp <gtm> <gtm>)
           | gze
           | (gsu <gtm>)
           | (gmatch <gtm> <gtm> <gtm>)
           | (gref <nat>)
pair     ::= (<grade> <grade>)
grade    ::= <point> | (iv <point> <point>)
point    ::= <nat> | w
nat      ::= 0 | 1 | 2 | …
```

Tokens are separated by one space. There is no other whitespace. A natural is decimal, with no leading zero except `0`. `w` is ω. `(iv a b)` is the inclusive interval from `a` to `b`. A pair is the computational grade, then the type grade.

A variable is a de Bruijn index. `0` is the nearest binder. `(gvar 0)` is that variable. `(gtyp 0)` is a use of it as a type. This emitter does not write `gtyp`. The grammar names it because muro-beam's term has it.

`(glam (c t) e)` is a function. It opens one binder. `e` is under that binder, and `(gvar 0)` is the variable. The domain type is not in the image. `(gpi (c t) e)` is a Π. It opens one binder the same way. The type grade is not a second binder, and the domain type is not in the image. A Π erases as `gpi`. `(gapp f a)` is an application. `gze` is zero. `(gsu e)` is successor. A closed numeral `n` is `n` successors of `gze`, the same term as `suc` written out. `(gmatch e z s)` is a match on Nat. The motive is not in the image. `s` binds the predecessor at `(gvar 0)`, one binder.

The domain of `glam` and of `gpi` is dropped. An annotation is dropped. The motive of `gmatch` is dropped. The loader does not recover them. They stay in the book, and they are not part of the image the boundary accepts.

`(gref n)` is definition `n`. The definitions are closed terms, in order, and the entry is not one of them. Definition `i` may name itself or an earlier definition. The entry may name any definition in the section.

`(seq e (done))` is the whole program. `e` is the run. `(done)` does not use the value `e` returns. The binding that `seq` gives that value is the pair `(w 0)`.

`examples/images/once.mbi` is:

```
(muro-beam-image 1 (boundary 1) (entry (seq (glam (1 0) (gvar 0)) (done))))
```

That is `λ (n : (1, 0) Nat) → n`. An unmarked identity is `((iv 0 1) 0)`. A reusable identity is `(w 0)`. A reusable variable applied to itself is `examples/images/twice.mbi`. An erased binder whose body is `0` is `(0 0)`. `examples/images/pi.mbi` is the image of `Π (n : Nat) → n`. `examples/images/iv.mbi` is the image of `λ (n : ([0, 2], 0) Nat) → n`.

## Definitions

A run the entry reaches is a definition. That includes a `run internal` and a prelude run. Spec, evidence, and data are not. A domain, an annotation, and a match motive do not pull a definition in.

The order is the order in which each call is to itself or to an earlier definition. A run that calls itself uses its own index. The entry is a second copy of the exported run, so a recursive export is both a definition and the entry. A run that calls no definition is version 1, the same bytes as before.

Two definitions that call each other have no such order. One of them would name a later index. That is `mbi:forward-def`. Nothing is written, and an image already at that path stays byte for byte.

`examples/images/plus.mbi` is `plus 2 3`. `plus` calls itself. `examples/images/chain.mbi` is three definitions, each the successor of the one before it. `examples/images/calls.mbi` is an entry that calls two of them.

## Which definition

Success is exactly one exported `run`, and that body erases. `{:ok, files}` is that image. The file is written only in this case. The command prints the path and exits 0 only in this case. `run internal` is not exported. Spec, evidence, data, and sessions are omitted, and omitting them is not a refusal.

Zero exported runs is `mbi:entry`. No file is written. A previous image at that path stays byte for byte. A book that does not check writes nothing and leaves a previous image byte for byte.

More than one exported run is a refusal, including when one of them erases. No file is written. The command prints no path. A previous image at that path stays byte for byte. A run that also erases is `mbi:entry in <name>`. A run that does not erase is `mbi:<reason> in <name>`. An earlier failure is named the same way. The reasons are joined by newlines, in book order. The first body that erases is not among them.

When every exported run fails, no file is written. A previous image stays byte for byte. The message is those reasons. It is not `mbi:entry`.

## Grades

The computational grade and the type grade are read off the binder.

| Binder | Computational | Type |
| --- | --- | --- |
| unmarked, `%0` | `(iv 0 1)` | `0` |
| `+` | `w` | `0` |
| `-` | `0` | `0` |
| `%1` | `1` | `0` |
| `(c, t)` | `c`, as written | `t`, as written |

An unknown quantity is `mbi:grade`. A pair whose component is not a point or an interval is `mbi:grade`.

The type grade of a quantity atom is `0` because a run use charges one computational use and no type use, so an identity checks. A binder mentioned only as a type, under a Π, still erases. muro-beam's check refuses it: `type grade 0 does not allow 1 uses`. The kernel accepts that term. This emitter does not run that check.

`%1` and `(1, 0)` are the same image. The other emitters still replace a grade pair with the affine quantity. This one keeps the pair.

## Refusals

The message is `mbi:<reason> in <name>`. The reason is the first constructor, not a walk into it. `forward-def` is the book: the runs that were reached cannot be ordered.

| Reason | Term |
| --- | --- |
| `def` | a name that is not a run in the book |
| `forward-def` | definitions the run reaches that cannot be ordered so each call is to itself or an earlier definition |
| `data` | a data type, a constructor, or a match on declared data, on `WBool`, or on `Opt` |
| `pair` | a product, a pair, or `let` of a pair |
| `stream` | `ν`, `unfold`, `uncons`, `Stream`, `Always`, `~` |
| `machine` | `I64`, `F32`, `Tensor`, and their operations |
| `word` | `U8`, `U32`, `U64`, and a word operation |
| `string` | `String` and a string operation |
| `bytes` | `Bytes`, `Slice`, and an octet operation |
| `atom` | `Atom` and a match on an atom |
| `hole` | `?` |
| `typ` | `Type` |
| `nat` | the type `Nat` |
| `unit` | `Unit`, `one`, and a match on `Unit` |
| `empty` | `Empty` and a match on it |
| `id` | an equation, `refl`, or `rewrite` |
| `numeral` | a numeral that is not a natural |
| `grade` | an unknown quantity, or a grade component that is not a point or an interval |
| `term` | a term this erasure does not know |

`mbi:entry` is the book-level refusal, with no definition name.

## What muro-beam checks

Writing the file is not acceptance. A successful emit means the book had exactly one exported run and that body erased. Acceptance is `InBoundary` on the closed term, in [muro-beam Boundary v1](https://github.com/doctorcorral/muro-beam/blob/main/agda/MuroBeam/Boundary.agda) (`MuroBeam.Boundary`, `boundary-version` is 1). That module is the authority. This emitter does not call it. A term in the file can fail `InBoundary`.

The files in `examples/images/` are checked here against the grammar on this page. The check requires one line, version 1 with no `(defs)` or version 2 with a non-empty `(defs)`, a `gref` only to itself or an earlier definition, and no free `gvar` or `gtyp` in a definition or the entry. It does not call muro-beam `load`, `decideB`, or `InBoundary`. A closed term the boundary refuses still passes.

`seq` asks the term to lie inside the boundary, then runs the grade check in `run`, then checks `(done)` at grade `(w 0)`. `(done)` uses nothing. `w` and `0` accept zero uses, so `(seq e (done))` checks when `e` checks and lies inside the boundary.

A function under a live grade `1` is outside that boundary, including a function the grade check would accept. `glam` opens one binder, and a second `glam` under a grade `1` already in scope is outside the boundary. An interval is not a fourth runtime grade: the boundary reads it as ω.

Stepping the loaded program is not a single evaluation of the term. `seq` has to be stepped first. The value is the result of evaluating `e`, read before `(done)` clears it. Evaluating the loaded program as a whole does not return that value.

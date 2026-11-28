---
title: C# tests
slug: csharp-test
order: 30
summary: A book's closed equations become one C# xUnit file. Each fact compares the two normal forms, or calls the file stem or a type named with --impl. A skip is a skipped fact and is recorded.
---

# C# tests

In brief: `mix muro.emit path.muro --backend csharp-test` prints one C# xUnit file for the closed equations in that file. The equations are the ones [Closed equations as tests](exunit.md) collects, in the same order, including `--imports`. `mix muro.gen` writes the same file when an entry sets `kind: :csharp_test`. Each equation is one `[Fact]`. A skip is a `[Fact]` with `Skip` set, and it is also returned in the skip list. The count of facts plus the count of skips is the count of candidates. With no `--impl`, a fact that reduces on both sides compares the two normal forms, and that file compiles in a project that references xUnit and nothing else. A param equation, or a side that does not reduce to a value, still names a host type (the file stem, unless `--impl` names one). `--impl` names a C# type and the left-hand side is a call of that type. A file of `param`s is a suite. The same book prints the same file.

## The test

One fact per equation, in book order. The method name is the evidence definition's name, folded to a C# identifier. The `DisplayName` is `"<file>:<line> <def-name>"`. `Assert.Equal` takes the right-hand side first.

```csharp
[Xunit.Fact(DisplayName = "rounding.muro:9 round-ok")]
public void round_ok()
{
    Xunit.Assert.Equal(MuroValues.MuroNat("1"), MuroValues.MuroNat("1"));
}
```

The path is the same label the ExUnit suite uses: relative to the project root under `mix muro.gen`, relative to the current directory under `mix muro.emit`, never absolute. A hyphenated Muro name stays inside the message. The method name is only the C# identifier.

A skipped equation is still a fact. The body is empty.

```csharp
[Xunit.Fact(DisplayName = "rounding.muro:42 keep-eq", Skip = "keep-eq (rounding.muro:42): argument 1 normal form is a stream")]
public void keep_eq()
{
}
```

The reason is `"<def-name> (<file>:<line>): <reason>"`. The structural reasons are the ones on the ExUnit page: an erased argument, an arity that does not match, a `run internal`, a prelude run the book does not define, a name that is not a run, a param reached inside a value, and a value that does not normalize. A value this printer cannot write is a skip too. A function, a stream, a machine term, an open term, and a shape with no literal use the same sentences as ExUnit (`normal form is a function`, `a stream`, `a machine term`, `is not closed`, `has no literal`). A word that is not a literal, a string that is not a literal or is not valid UTF-8, and bytes that are not a literal name that fact.

The class is `public`. Each fact is a public instance method. The file does not import `Xunit`. `Xunit.Fact` and `Xunit.Assert` are written in full, so the file builds in a `dotnet new xunit` project, which already has a global `using Xunit`, and in a project that does not. A second `using Xunit` beside that global using is a warning, and `dotnet build -warnaserror` rejects it.

`mix muro.emit --backend csharp-test` prints the file on standard output. Each skip goes to standard error, then `N tests, M skipped`, including when nothing was skipped. `--node` with this backend is refused (`--node writes the placement calls`).

A book with no closed equations prints the class and `MURO_BOOK`, and no facts. The count line is `0 tests, 0 skipped`.

A meeting that marks a party that may fail is refused, as the ExUnit, pytest, and Rust suites refuse it.

## Names

A source name becomes a test method in five steps.

1. Replace each `-` with `_`. Replace each other character outside `[A-Za-z0-9_]` with `_`.
2. An empty result, or one that starts with a digit, gains the prefix `muro_`.
3. Claim that name, in book order, over every candidate, tests and skips together. A second claim of the same base is the base plus `_` and a decimal starting at 2. `round-ok` and `round_ok` are `round_ok` and `round_ok_2`.
4. A method that hides `object` gains a trailing `_`. The names are `Equals`, `GetHashCode`, `GetType`, `ToString`, `Finalize`, and `MemberwiseClone`. `@` is the same identifier, and xUnit refuses the first four as test names, so the suffix is a different name. `Equals` is `Equals_`.
5. A keyword, reserved or contextual, is written with `@`. `class` is `@class`. `record` is `@record`. `field`, `extension`, and `allows` are `@field`, `@extension`, and `@allows`.

The claim happens before `@` is added, and the finished identifier is recorded. `Equals` finishes as `Equals_`, so an evidence named `Equals_` is `Equals__2`. `class` finishes as `@class`, which is a different identifier from `class_`, so an evidence named `class_` stays `class_`. `MURO_BOOK` and `MuroValues` are reserved on the test class. An evidence named `MuroValues` is `MuroValues_2`. An evidence named `MURO_BOOK` is `MURO_BOOK_2`. An evidence named `Values` stays `Values`.

A constructor type is claimed the same way, against the helper names `Unit`, `MuroBytes`, `MuroAtom`, `MuroNone`, `MuroSome`, `MuroWBool`, `MuroNat`, and `MuroValues`. A keyword is `@`. A name that is only lowercase ASCII letters gains a trailing `_`, because `dotnet build -warnaserror` rejects that type name (CS8981). `red` is `red_`. `record` is `@record`. `field` is `@field`. A constructor named `MuroValues` is `MuroValues_2`, so it is not the helper class. A constructor named `Values` stays `Values`. A method keeps a lowercase spelling: the host call `round` stays `round`, and CS8981 names types.

The test class is the file stem, folded, with `Tests` appended, then `@` when that whole name is a keyword. `rounding.muro` is `roundingTests`. `word-kind.muro` is `word_kindTests`. `class.muro` is `classTests`. `2nd.muro` is `muro_2ndTests`.

## The implementation

With no `--impl`, each fact that reduces on both sides compares the two normal forms. A param equation, or a side that does not reduce to a value, is a call of the file stem. `rounding.muro` calls `global::rounding.round`. `class.muro` calls `global::@class`. `2nd.muro` calls `global::muro_2nd`. `Values.muro` calls `global::Values`. `MuroValues.muro` calls `global::MuroValues`, so the call is not the nested helper of the same name. A name that already contains a `.`, such as `--impl Host.Rounding`, is written as it is. There is no C# image beside the file.

`--impl` and `impl:` name a C# type. Each segment is an identifier that is not a keyword, or `@` plus an identifier. `Host.Rounding` and `@class` are accepted. `class`, `int`, `1bad`, `.Rounding`, and `Rounding.` are refused: `impl must be a C# type name`. The type is baked into the file. There is no environment override. The left-hand side is a call of that type, and the right-hand side is the normal form.

`--impl` with any backend other than `pytest`, `rust-test`, and `csharp-test` is `--impl is only valid with --backend pytest, --backend rust-test, or --backend csharp-test`.

The class defines `MURO_BOOK`, the book sha256, the same hash an ExUnit suite stores in `@muro_book`.

## Values

Arguments and the result are normalized with the checker's fuel (`Muro.Check.normalize/3`, default 2000), the same normalization the ExUnit suite uses. `Muro.Emit.CSharpTest.print_value/2` is the one printer. The helpers live in `public static class MuroValues`, nested in the test class, and a helper is written only when a fact uses it.

| Muro value | C# |
| --- | --- |
| `Nat`, including `0` and `suc` | `MuroValues.MuroNat("n")`, a `System.Numerics.BigInteger` |
| `U8` | `(byte)n` |
| `U32` | `nu` |
| `U64` | `nUL` |
| `I64` | a signed `long`, or `long.MinValue` |
| `WBool` | `new MuroValues.MuroWBool(true)` or `new MuroValues.MuroWBool(false)` |
| `wnone` | `new MuroValues.MuroNone()` |
| `wsome` | `new MuroValues.MuroSome<T>(...)` |
| constructor | `new MuroValues.red_()` or `new MuroValues.box_<BigInteger>(...)` |
| pair | `(a, b)`, a `ValueTuple` |
| `tt` | `new MuroValues.Unit()` |
| atom | `new MuroValues.MuroAtom("name")` |
| string literal | a C# string |
| bytes literal | `new MuroValues.MuroBytes("hex")` |

`Nat` is unbounded. A fixed-width integer would wrap, so the digits are a `BigInteger`. `MuroNat` parses them with `NumberStyles.None` and `CultureInfo.InvariantCulture`. A `Nat` of any size is a fact. `18446744073709551616` is `MuroValues.MuroNat("18446744073709551616")`.

`U8`, `U32`, `U64`, and `I64` are the residue of that width. `I64` is the signed residue. `subi (toI64 0) (toI64 1)` is `-1L`. The signed minimum is `long.MinValue`, because the decimal spelling of that value does not fit in a `long` literal. A word equation that ExUnit skips as a machine term is a fact here when the normal form is a literal.

`WBool` is a record holding a `bool`. `Assert.Equal` on two raw `bool`s is the xUnit diagnostic xUnit2004, which `dotnet build -warnaserror` rejects. The record compares by its field.

A constructor is a `readonly record struct`. Equality is synthesized and structural, which is what `Assert.Equal` uses. A record that holds a `byte[]`, a `List<T>`, or an `ImmutableArray<T>` compares those fields by reference, so two equal payloads do not compare equal. Bytes are a record of a lowercase hex `string`. `b"ab"` is `new MuroValues.MuroBytes("6162")`. An atom is a record of its name, so an atom does not equal a string of the same characters. A pair is a `ValueTuple`, and a pair of records compares structurally. `tt` is an empty `readonly record struct`, not `null`.

An erased field is not a field of the record. A constructor applied to fewer fields than it declares is a function. A constructor name declared twice is not given a record, and a value of that name is a skip (`is not closed`).

A string literal escapes `"`, `\`, newline, carriage return, and tab. Any other control is `\u` and four lowercase hex digits. The text is a regular string, so `$` and `{` stay as they are written.

A function, a stream, an open name, `F32`, `Tensor`, and a word operation that does not reduce to a literal are skips. An erased value is a skip (`normal form is erased`).

## Param libraries

`Muro.emit_csharp_test/2`, `mix muro.emit --backend csharp-test`, and a `kind: :csharp_test` entry check a library of unsupplied `param`s as assumptions (`params: :open`). `mix muro.check`, and every backend other than `exunit`, `pytest`, `rust-test`, and `csharp-test`, still refuse the file. A `run` param at the head of a side is a call of the entry file's type, `global::lib.p()` for `lib.muro`. An `evidence` param is not a call and not a candidate.

`--imports` collects the same files the ExUnit flag collects. Every call in that file names the entry file's type. It is an error with any backend other than `exunit`, `pytest`, `rust-test`, and `csharp-test`: `--imports is only valid with --backend exunit, --backend pytest, --backend rust-test, or --backend csharp-test`.

## Manifest

A C# test entry may omit the module. The target ends with `.cs`. `impl:` is a C# type name, not an alias and not a Python module. `imports:` is the boolean the ExUnit entry takes. The header comment is `//`, the same mark as a Rust test file. The body is not formatted. The `Skip` argument sits in the body, so `mix muro.gen --check` reports a stale target when the skipped set changes. After `written` or `unchanged`, one `skipped <target>: <name> (<file>:<line>): <reason>` line is printed per skip. `--check` does not print those lines.

```elixir
[
  muro: "0.22.53",
  modules: [
    {"priv/muro/rounding.muro", "test/rounding_test.cs",
     [kind: :csharp_test, impl: "Host.Rounding"]}
  ]
]
```

In `muro.toml` the same entry is `backend = "csharp-test"`, `impl = "Host.Rounding"`, and `target` ending in `.cs`. `module` is omitted.

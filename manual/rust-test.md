---
title: Rust tests
slug: rust-test
order: 29
summary: A book's closed equations become one Rust test file. The tests call the emitted Rust. A skip is an ignored test and is recorded.
---

# Rust tests

In brief: `mix muro.emit path.muro --backend rust-test` prints one Rust test file for the closed equations in that file. The equations are the ones [Closed equations as tests](exunit.md) collects, in the same order, including `--imports`. `mix muro.gen` writes the same file when an entry sets `kind: :rust_test`. Each equation is one test. A skip is a `#[test]` function marked `#[ignore]`, and it is also returned in the skip list. The count of tests plus the count of skips is the count of candidates. The suite calls the Rust image `--backend rust` writes. A file of `param`s is a suite.

## The test

One test per equation, in book order. The function name is the evidence definition's name, folded to a Rust identifier. The assertion message is `"<file>:<line> <def-name>"`.

```rust
#[test]
fn round_ok() {
    assert_eq!(rounding::round(rounding::muro__from_u64(1)), rounding::muro__from_u64(1), "rounding.muro:4 round-ok");
}
```

The path is the same label the ExUnit suite uses: relative to the project root under `mix muro.gen`, relative to the current directory under `mix muro.emit`, never absolute. A hyphenated Muro name stays inside the message. The function name is only the Rust identifier.

A skipped equation is still a test. The body is empty.

```rust
#[test]
#[ignore = "keep-eq (rounding.muro:42): argument 1 normal form is a stream"]
fn keep_eq() {}
```

The reason is `"<def-name> (<file>:<line>): <reason>"`. The structural reasons are the ones on the ExUnit page: an erased argument, an arity that does not match, a `run internal`, a prelude run the book does not define, a name that is not a run, a param reached inside a value, and a value that does not normalize. A value this printer cannot write is a skip too. A function, a stream, a machine term, an open term, and a shape with no literal use the same sentences as ExUnit (`normal form is a function`, `a stream`, `a machine term`, `is not closed`, `has no literal`). A word that is not a literal, a string that is not a literal or is not valid UTF-8, and bytes that are not a literal name that fact.

`mix muro.emit --backend rust-test` prints the file on standard output. Each skip goes to standard error, then `N tests, M skipped`, including when nothing was skipped. `--node` with this backend is refused (`--node writes the placement calls`).

A book with no closed equations prints the scaffold and no tests. The count line is `0 tests, 0 skipped`.

## Names

A source name becomes a test function in four steps.

1. Replace each `-` with `_`. Replace each other character outside `[A-Za-z0-9_]` with `_`.
2. An empty result, or one that starts with a digit, gains the prefix `muro_`.
3. Claim that name, in book order, over every candidate, tests and skips together. A second claim of the same base is the base plus `_` and a decimal starting at 2. `round-ok` and `round_ok` are `round_ok` and `round_ok_2`.
4. A keyword that can be raw is `r#` plus the identifier. `loop` is `r#loop`. `fn` is `r#fn`. `crate`, `self`, `super`, and `Self` cannot be raw, so each gains a trailing `_`. `crate` is `crate_`.

The claim happens before `r#` is added, and the finished identifier is recorded. `crate` finishes as `crate_`, so an evidence named `crate_` is `crate__2`. The same split holds for `self` and `self_`, `super` and `super_`, and `Self` and `Self_`. A second `fn` is `fn_2`, and the module name `r#fn` is reserved the same way, so the evidence `fn` in `fn.muro` is `fn_2`. `MURO_BOOK` is reserved. When the tests include the sibling file, the module identifier is reserved too. `--impl` does not reserve that identifier, and the finished names still do not collide.

A call uses the spelling the Rust image gives that run, not this fold. `box` is `box_k`. A run named `loop` is `loop_k`. A run named `u64` is `u64_k`. The test function `r#loop` and the run `loop_k` are different names. Every call is qualified with the module path, so a test named `round` does not hide the run `round`.

The default module is the file stem, folded the same way. `rounding.muro` calls `rounding::round`. `word-kind.muro` calls `word_kind`, and the sibling file stays `word-kind.rs`. `fn.muro` is `mod r#fn`. `crate.muro` is `mod crate_`. `2nd.muro` is `mod muro_2nd`.

## The implementation

By default the file includes the emitted image beside it:

```rust
#[path = "rounding.rs"]
mod rounding;
```

`rustc --edition 2021 --test` accepts the two files as siblings. A Cargo `tests/` directory does not reach into `src/` that way. Pass `--impl crate::module`, or `impl:` on the manifest entry, and the tests call that path. The path is baked into the file. There is no environment override.

`--impl` and `impl:` are a Rust path. Each segment is an identifier that is not a keyword, or a path keyword (`crate`, `self`, `super`, `Self`), or `r#` plus an identifier that is not one of those four. `crate::rounding`, `self::a`, and `r#fn` are accepted. `fn`, `r#crate`, `a::`, and `1bad` are refused: `impl must be a Rust path`. `--impl` with any backend other than `pytest` and `rust-test` is `--impl is only valid with --backend pytest or --backend rust-test`.

The file defines `MURO_BOOK`, the book sha256, the same hash an ExUnit suite stores in `@muro_book`. The inner attribute allows an unused module, that constant, and the names a book spells.

## Values

Arguments and the result are normalized with the checker's fuel (`Muro.Check.normalize/3`, default 2000), the same normalization the ExUnit suite uses. `Muro.Emit.RustTest.print_value/3` is the one printer. The spellings are the ones `--backend rust` writes, so a constructor in the test is the constructor in the image.

| Muro value | Rust |
| --- | --- |
| `Nat`, including `0` and `suc` | `muro__from_u64(n)` |
| `U8`, `U32`, `U64` | a suffixed residue: `5u8` |
| `I64` | a signed literal, or `(nu64 as i64)` when the residue is at least `2⁶³` |
| `WBool` | `true` or `false` |
| `wnone` | `::std::option::Option::None` |
| `wsome` | `::std::option::Option::Some(...)` |
| constructor | the image's constructor function, including a nullary call `red()` |
| pair | `muro__pair(a, b)` |
| `tt` | `muro__Unit` |
| atom | `muro__Atom::asc` |
| string literal | a `muro__str` of a static byte slice |
| bytes literal | a `muro__slice` of a static byte slice |

A `Nat` above `18446744073709551615` is a skip: `normal form is a Nat that does not fit in u64`. A `Nat` above `100000` that still fits is a skip: `normal form is a Nat above 100000`. The same sentences name the argument when that `Nat` is an argument (`argument 1 normal form is a Nat above 100000`). `muro__from_u64` builds one successor per unit. The image compares a `Nat` by walking that chain in a loop, frees the chain in a loop, and prints the count by that same walk, so `100000` compares, is freed, and a failing compare prints the failure line and the count. The test file spells that value as `muro__from_u64(100000)`. `100001` is the skip.

A word equation that ExUnit skips as a machine term is a test here when the normal form is a literal. `subi (toI64 0) (toI64 1)` prints `(18446744073709551615u64 as i64)`.

The types the tests compare implement `PartialEq` and `Debug`. Declared data that reaches itself through a boxed field frees with a heap-stack `Drop`, including two types that contain each other. When that data is comparable, `PartialEq` and `Debug` walk that cycle on a heap stack. `PartialEq` compares each field outside the cycle. `Debug` prints the number of nodes the walk visits and those fields. The text keeps the longest prefix of that print that fits in 1024 bytes and ends on a character boundary, and then `...`. A field that crosses that boundary contributes the bytes that fit. A same-length list whose payloads differ inside that prefix prints two different texts. A field past the prefix is not formatted. The count includes every node, including nodes past the prefix. A shared node is counted again each time the walk reaches it. Comparing does not record a visited set: a value the image builds is a DAG, and a clone shares a node without making a cycle. Visiting that shared node again still compares equal. A node still on the path is a cycle, and `Debug` prints `...` there. When that cycle also stores itself inside a pair, the walk enters the pair on the same heap stack. A cycle reached only through a pair keeps the derived `Drop`, `PartialEq`, and `Debug`. A cycle that goes out through a boxed field and back only through a pair does too. One type holds the other in a boxed field, and the other holds the first only inside a pair. The pair is not an edge of the boxed-ref graph, so neither type is in an SCC, and neither is walked on the heap stack. A deep value of either shape can overflow the stack. A pair prints each component. A component it cannot show prints `..`, and the other component still prints. Two hidden components print `muro__Pair(.., ..)`. A data type whose Rust image does not implement `PartialEq` and `Debug` is a skip: `normal form is not comparable in Rust`. A parameterized type whose fields are erased in that image is that skip. An `unboxed data` value is the constructor call. The same value inside a pair is a skip (`normal form is unboxed data in a pair`). An `Opt` of unboxed data is a skip (`normal form is an unboxed Opt`). An erased value is a skip (`normal form is erased`).

A string built by `strCat`, and a string built by reading bytes, prints when every piece is a literal and the text is valid UTF-8. Bytes built by concatenation print when every piece is a literal. Anything else in that family is a skip.

A function, a stream, an open name, `F32`, `Tensor`, and a word operation that does not reduce to a literal are skips.

## Param libraries

`Muro.emit_rust_test/2`, `mix muro.emit --backend rust-test`, and a `kind: :rust_test` entry check a library of unsupplied `param`s as assumptions (`params: :open`). `mix muro.check`, and every backend other than `exunit`, `pytest`, and `rust-test`, still refuse the file. A `run` param at the head of a side is a call, `lib::p()`. An `evidence` param is not a call and not a candidate.

`--imports` collects the same files the ExUnit flag collects. It is an error with any backend other than `exunit`, `pytest`, and `rust-test`: `--imports is only valid with --backend exunit, --backend pytest, or --backend rust-test`.

## Manifest

A Rust test entry may omit the module. The target ends with `.rs`. `impl:` is a Rust path, not an alias and not a Python module. `imports:` is the boolean the ExUnit entry takes. The header comment is `//`, the same mark as a Rust image. The body is not formatted. The `#[ignore]` attribute sits in the body, so `mix muro.gen --check` reports a stale target when the skipped set changes. After `written` or `unchanged`, one `skipped <target>: <name> (<file>:<line>): <reason>` line is printed per skip. `--check` does not print those lines.

```elixir
[
  muro: "0.22.21",
  modules: [
    {"priv/muro/rounding.muro", "test/rounding_test.rs",
     [kind: :rust_test, impl: "crate::rounding"]}
  ]
]
```

In `muro.toml` the same entry is `backend = "rust-test"`, `impl = "crate::rounding"`, and `target` ending in `.rs`. `module` is omitted. `kind: :rust` is the image. `kind: :rust_test` is this file. Both end in `.rs`.

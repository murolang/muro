---
title: Pytest
slug: pytest
order: 28
summary: A book's closed equations become one pytest module. The tests call a Python module the host names. A skip is a marked test and is recorded.
---

# Pytest

In brief: `mix muro.emit path.muro --backend pytest` prints one pytest module for the closed equations in that file. The equations are the ones [Closed equations as tests](exunit.md) collects, in the same order, including `--imports`. `mix muro.gen` writes the same module when an entry sets `kind: :pytest`. Each equation is one test. A skip is a `pytest.mark.skip` test, and it is also returned in the skip list. The count of tests plus the count of skips is the count of candidates. The suite calls a Python module the host names. It does not emit Muro, and it does not call an emitted module. A file of `param`s is a suite.

## The test

One test per equation. The function name is `test_` plus the evidence definition's name, folded to a Python identifier. The pytest id is `"<file> <def-name>"`. The assertion message is `"<file>:<line> <def-name>"`.

```python
@pytest.mark.parametrize("_muro_id", ["rounding.muro round-ok"], ids=["rounding.muro round-ok"])
def test_round_ok(_muro_id, muro_impl):
    assert muro_impl.round(1) == 1, "rounding.muro:4 round-ok"
```

The path is the same label the ExUnit suite uses: relative to the project root under `mix muro.gen`, relative to the current directory under `mix muro.emit`, never absolute. A hyphenated Muro name stays inside the id and the message. The function name is only the Python identifier. A failure shows the id and the assertion message, so the equation name is in the output.

A skipped equation is still a test. It does not take `muro_impl`, so a missing implementation does not hide it.

```python
@pytest.mark.skip(reason="keep-eq (rounding.muro:42): result normal form is a stream")
@pytest.mark.parametrize("_muro_id", ["rounding.muro keep-eq"], ids=["rounding.muro keep-eq"])
def test_keep_eq(_muro_id):
    pass
```

The reason is `"<def-name> (<file>:<line>): <reason>"`. The structural reasons are the ones on the ExUnit page: an erased argument, an arity that does not match, a `run internal`, a prelude run the book does not define, a name that is not a run, a param reached inside a value, and a value that does not normalize. A value this printer cannot write is a skip too. A function, a stream, a machine term, an open term, and a shape with no literal use the same sentences as ExUnit (`normal form is a function`, `a stream`, `a machine term`, `is not closed`, `has no literal`). A word that is not a literal, a string that is not a literal or is not valid UTF-8, and bytes that are not a literal name that fact (`normal form is a word that is not a literal`, and the same shape for a string or for bytes).

`mix muro.emit --backend pytest` prints the module on standard output. Each skip goes to standard error, then `N tests, M skipped`, including when nothing was skipped. `--node` with this backend is refused (`--node writes the placement calls`).

A book with no closed equations prints the fixture and no tests.

## Names

A source name becomes a Python identifier in four steps.

1. Replace each `-` with `_`.
2. If the result matches `[A-Za-z_][A-Za-z0-9_]*` and is not a keyword, use it.
3. If it is a keyword, append `_`. `class` is `class_`, `None` is `None_`, `lambda` is `lambda_`, `def` is `def_`.
4. Otherwise replace each character outside `[A-Za-z0-9_]` with `_`. Runs of `_` stay. An empty result, or one that starts with a digit, gains the prefix `muro_`. If that result is a keyword, append `_`.

`match` and `case` stay. They are soft keywords. The hard keywords are `False`, `None`, `True`, `and`, `as`, `assert`, `async`, `await`, `break`, `class`, `continue`, `def`, `del`, `elif`, `else`, `except`, `finally`, `for`, `from`, `global`, `if`, `import`, `in`, `is`, `lambda`, `nonlocal`, `not`, `or`, `pass`, `raise`, `return`, `try`, `while`, `with`, and `yield`.

The test function claims `test_` plus that fold, in book order, over every candidate, tests and skips together. A second claim of the same base is the base plus `_` and a decimal starting at 2. `round-ok` and `round_ok` are `test_round_ok` and `test_round_ok_2`. The claim is on the whole name, so a second `class` is `test_class__2`.

A call uses the same fold on the run's name, claimed across the book's definitions the way the ExUnit suite claims Elixir names, including a `param` and a `run internal`. The call is `muro_impl.<name>(args)`. The arity is the non-erased binders. Two runs that fold to one identifier are `round` and `round_2`.

The default module is the file stem, folded the same way. `rounding.muro` calls `rounding.round`. `word-kind.muro` calls `word_kind`. `2nd.muro` calls `muro_2nd`.

## The implementation

The module is chosen in three places. The file stem is the default. `--impl` on `mix muro.emit`, and `impl:` on a `kind: :pytest` entry, bake another name into the file. At run time the environment variable overrides that name, and the file's bytes do not change.

The variable is `MURO_IMPL_` plus the stem. Hyphens become `_`, every other character outside `[A-Za-z0-9_]` becomes `_`, and the result is uppercased. `rounding.muro` is `MURO_IMPL_ROUNDING`. `half_ok.muro` is `MURO_IMPL_HALF_OK`. `word-kind.muro` is `MURO_IMPL_WORD_KIND`. `2nd.muro` is `MURO_IMPL_2ND`. The stem is the file's basename, not the `muro_` prefix of a digit fold, and not the module `--impl` baked in.

The fold is not injective. `foo-bar.muro` and `foo_bar.muro` are both `MURO_IMPL_FOO_BAR`. `Foo.muro` and `foo.muro` are both `MURO_IMPL_FOO`. `a/foo-bar.muro` and `b/foo_bar.muro` fold together, because only the basename is used. `mix muro.gen` refuses a manifest whose pytest entries fold to one variable. The message names that variable and each entry.

The fixture reads `os.environ.get` of that variable, and otherwise the baked default, then `importlib.import_module`. It is module-scoped. A module that cannot be imported fails before the tests, and the message names the module: `implementation module rounding could not be imported`. A called function that is missing, or whose signature does not accept the arity, fails the same way and names `round/1`. Several missing functions are joined in that message. `inspect.signature` decides the arity. A function that raises `ValueError` or `TypeError` from `signature` is accepted. A varargs parameter accepts an arity at least the required positional count. Otherwise the arity must sit between the required positional count and the positional count. Only the functions the runnable tests call are checked. A skipped test is not in that list.

`--impl` and `impl:` are a dotted Python module. Each segment is an identifier and not a keyword. `pkg.rounding` is accepted. `class`, `my.class`, `.rounding`, and `1bad` are refused: `impl must be a Python module name`. `--impl` with any other backend is `--impl is only valid with --backend pytest`.

The module defines `MURO_BOOK`, the book sha256, the same hash an ExUnit suite stores in `@muro_book`.

## Values

Arguments and the result are normalized with the checker's fuel (`Muro.Check.normalize/3`, default 2000), the same normalization the ExUnit suite uses. `Muro.Emit.Pytest.print_value/2` is the one printer. A `repr` plugs in there.

| Muro value | Python |
| --- | --- |
| `Nat`, including `0` and `suc` | a non-negative `int` |
| `U8`, `U32`, `U64` | an `int`, the residue `0` … `2ʷ − 1` |
| `I64` | an `int`, the signed value |
| constructor with no fields | the muro name as a `str`: `"red"`, `"nil"`, `"wtrue"`, `"wfalse"`, `"wnone"` |
| constructor with fields | a tuple, the name first: `("box", 2)`, `("cons", 1, "nil")`, `("wsome", 5)` |
| pair | a 2-tuple: `(1, 2)` |
| `tt` | `None` |
| atom | the name as a `str` |
| string literal | a `str`, when the text is valid UTF-8 |
| bytes literal | a `bytes` value: `b"ab"` |

A word in the checker is a residue, `0` … `2ʷ − 1`. `U8`, `U32`, and `U64` print that residue. `I64` prints the signed value: a residue below `2⁶³` stays, and any other residue is that residue minus `2⁶⁴`. `subi (toI64 0) (toI64 1)` is the residue `2⁶⁴ − 1` and prints `-1`. The minimum `I64` prints `-9223372036854775808`. Elixir emit prints the residue, not this signed integer. Elixir prints `WBool` as `true` or `false` and `Opt` as `{:some, n}` or `:none`. This module prints the muro names `"wtrue"`, `"wfalse"`, `"wnone"`, and `("wsome", n)`.

A nullary constructor is the string. It is not a 1-tuple. A constructor is a data constructor declared in the book.

A string built by `strCat`, and a string built by reading bytes, prints when every piece is a literal and the text is valid UTF-8. Bytes built by concatenation print when every piece is a literal. Anything else in that family is a skip.

A function, a stream, an open name, `F32`, `Tensor`, and a word operation that does not reduce to a literal are skips. A word equation that ExUnit skips as a machine term is a test here when the normal form is a literal.

The encoding is not injective across types. A `String` and a nullary constructor are both a Python `str`. A `Nat` and a `U8` are both a Python `int`. A pair whose first component is a string and a unary constructor can also coincide: `("box", 2)` is that pair and it is `box` of `2`. A cross-type `==` can therefore pass when the two sides have different Muro types. Same-type literals are sound. A form this printer cannot write is a skip, and a skip is not compared.

## Param libraries

`Muro.emit_pytest/2`, `mix muro.emit --backend pytest`, and a `kind: :pytest` entry check a library of unsupplied `param`s as assumptions (`params: :open`). `mix muro.check`, and every other backend, still refuse the file. A `run` param at the head of a side is a call, `muro_impl.p()`. An `evidence` param is not a call and not a candidate.

`--imports` collects the same files the ExUnit flag collects. It is an error with any backend other than `exunit` and `pytest`: `--imports is only valid with --backend exunit or --backend pytest`.

## Manifest

A pytest entry may omit the module. The target ends with `.py`. `impl:` is a Python module name, not an alias. `imports:` is the boolean the ExUnit entry takes.

```elixir
[
  muro: "0.22.4",
  modules: [
    {"priv/muro/rounding.muro", "test/rounding_test.py",
     [kind: :pytest, impl: "host.rounding"]}
  ]
]
```

In `muro.toml` the same entry is `backend = "pytest"`, `impl = "host.rounding"`, and `target` ending in `.py`. `module` is omitted.

The header is the same two lines as any other generated file, with `#` comments. The body is not formatted. The skip decorators sit in the body, so `mix muro.gen --check` reports a stale target when the skipped set changes, and a hand edit of a skip is the hand-edited message. After `written` or `unchanged`, one `skipped <target>: <name> (<file>:<line>): <reason>` line is printed per skip. `--check` does not print those lines.

Next: [Committed modules](gen.md).

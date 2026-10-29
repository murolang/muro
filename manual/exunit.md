---
title: Closed equations as tests
slug: exunit
order: 14
summary: A book's closed equations become one ExUnit module. The tests call an implementation the host names. A skip is printed and recorded.
---

# Closed equations as tests

In brief: `mix muro.emit path.muro --backend exunit` prints one ExUnit module for the closed equations in that file. `mix muro.gen` writes the same module when an entry sets `kind: :exunit`. Each test is named `"<file> <def-name>"`. The file and line are in the assertion message. The suite calls an implementation module the host selects. It does not call the emitted module unless that module is the implementation. A file of `param`s is a suite. `--imports` also collects the equations of the files this book imports directly.

## What is collected

The book is the one `Muro.Load.file/2` checks. In book order, a candidate is an `evidence` definition in this file (kind `def`) whose type is an equation `{f a₁ … aₙ ≡ b : T}` and whose left-hand head is a name (`f`, including a nullary `f`). `T` is not used beyond that shape.

These are left out of the suite and out of the skip list. They are not closed equations of that form:

- quantified evidence, `Π (x : A) → {…}`. Property tests from those are a later change.
- an equation whose head is not a name. `0`, `suc`, a lambda, `head`, `tail`, `fst`, and `snd` are in this set. `head` and `tail` are sugar for a pair of a stream; `fst` and `snd` are sugar for a pair.
- evidence defined in an imported book, unless the command or the manifest entry asks for it. The default leaves those equations out, so a suite does not grow. [Imported equations](#imported-equations) is that collection. A `run` defined in an import may still be `f` of an equation in this file, because the emitted module includes it.
- `move`, `relay`, and `talk`.

Each candidate becomes one test or one skipped line. The count of tests plus the count of skips is the count of candidates.

Arguments and the result are normalized with the checker's fuel (`Muro.Check.normalize/3`, default 2000). A nullary `run` used as an argument or a result, such as `golden-x`, is replaced by that value. The value is then printed with the shapes in [How values look](emit.md#how-values-look): `0`, `{:suc, n}`, `:tt`, an atom for a constructor with no fields, `{:ctor, args…}`, `{a, b}`. `Muro.Emit.emit_closed/2` is that printer. A later `repr` (#131) hooks in there.

Host data arrives with repr (#131). Until then the suite compares emitted shapes. A map such as `%{"id" => 3, "enabled" => true}` is not what the assertion sees.

## The test

One test per equation:

```elixir
test "priv/muro/rounding.muro round-ok" do
  impl = ...
  assert impl.round({:suc, 0}) == {:suc, 0}, "priv/muro/rounding.muro:4 round-ok"
end
```

The name is `"<file> <def-name>"`: the book path as the suite renders it, one space, the evidence definition's name. There is no line number and no parentheses in the name. The assertion message is `"<file>:<line> <def-name>"`. An ExUnit failure shows the test name and that message. The path is relative to the project root under `mix muro.gen` (the manifest's book path, `/` separators). Under `mix muro.emit` it is relative to the current directory, or a `..` path when the file sits outside that directory. It is never absolute. An imported file that is not under that root is printed as the file's basename, so the name does not contain an absolute path. A hyphenated Muro name stays inside the string. The string is escaped as an Elixir literal.

0.16.76 named the test `"<name> (<file>:<line>)"` and used that same string as the message. The name changed in 0.17.0 so a line shift does not change a CI history, a quarantine list, or an `--only` / `--exclude` filter. Regenerate the suite with `mix muro.gen`. The line stays in the message. The skip comment and the `skipped` line keep the 0.16.76 spelling, `name (file:line): reason`. The name is built in one place from the equation's origin, which today is that file.

The function name is the spelling `Muro.Emit.def_names/3` gives the Elixir backend, with the same taken set. The arity is the number of non-erased binders of `f`. The assertion calls `impl.f(args)` or `impl.f()`. It does not call a hard-coded emitted module.

`f` from the file stem `rounding` is `round` when the Muro name is `round`. Reserved words and hyphenated names follow the Elixir backend.

## The implementation

The same file defines two modules. `MyApp.RoundingTest.Behaviour` has one `@callback` per distinct `run` the tests actually call (one per function, not per equation). Each callback is specified with `term()`:

```elixir
@callback round(term()) :: term()
```

A nullary `run` is `@callback golden() :: term()`. When every equation was skipped, the behaviour is empty. Callback names and arities match the emitted module, so that module satisfies the behaviour when it is the implementation.

`MyApp.RoundingTest` is the ExUnit case. `async` is `false`. `setup_all` reads the implementation and passes `%{impl: impl}` to the tests:

```elixir
impl = Application.get_env(:muro, __MODULE__, @impl_mod)
```

The key is the test module. The default, `@impl_mod`, is used when the key is unset. The host selects another module without editing the generated file:

```elixir
Application.put_env(:muro, MyApp.RoundingTest, MyApp.RoundingAdapter)
```

Put that line in `test/test_helper.exs`, which runs before the tests. The value is read when the tests run, so the generated bytes do not depend on the host's config. `Application.compile_env/3` would bake the config into the file, and a drift check would fail when the adapter changed.

`setup_all` raises when the value is not a module name, when `Code.ensure_loaded/1` does not return `{:module, impl}`, and when `function_exported?/3` misses a callback. The message names the module. A missing module says `is not loaded`. A missing callback says `does not export round/1`.

From `mix muro.emit`, the test module is the file stem plus `Test` (`rounding.muro` prints `RoundingTest`) and the default implementation is the stem (`Rounding`), the name the Elixir backend gives that file. Both can be compiled together. In the manifest, `module` is the test module the entry names (`MyApp.RoundingTest`). `impl:` overrides the default. When `impl:` is absent the default is still the file stem, not the test module and not the alias of a sibling Elixir entry. Set `impl:` when that alias is not the stem.

The module carries `@muro_book`, the book hash `Muro.Gen.book_hash/2` computes for the display path, and `def muro_book, do: @muro_book`.

### An adapter in the same compilation

`mix test` loads `test/**/*_test.exs`. A suite generated at `test/rounding_test.exs` is registered because `use ExUnit.Case` runs while `ExUnit.Server` is up. An adapter in `lib/` or `test/support/` is compiled before that `.exs` exists. `@behaviour MyApp.RoundingTest.Behaviour` then warns, and compilation still succeeds:

```
warning: @behaviour MyApp.RoundingTest.Behaviour does not exist (in module MyApp.RoundingAdapter)
```

The missing-callback check does not run, because the behaviour module was not part of that compilation. `setup_all` still checks `function_exported?/3` when the tests run.

To have the compiler check the adapter, generate the suite as an `.ex` on the test compilation path and compile the adapter next to it:

```elixir
# mix.exs
defp elixirc_paths(:test), do: ["lib", "test/support"]
defp elixirc_paths(_), do: ["lib"]
```

```elixir
# muro.exs
{"priv/muro/rounding.muro", MyApp.RoundingTest, "test/support/rounding_test.ex",
 [kind: :exunit, impl: MyApp.Rounding]}
```

`mix new` does not put `test/support` on `elixirc_paths`. Add it. During `mix test`, Elixir waits for `MyApp.RoundingTest.Behaviour` and then warns on a missing callback:

```
warning: function round/1 required by behaviour MyApp.RoundingTest.Behaviour is not implemented (in module IncompleteRound)
```

A complete adapter produces no such warning. The warning is a warning. It fails the build when the host compiles with `--warnings-as-errors`.

`mix test` does not load `*.ex` as tests. Register the case from `test/test_helper.exs` after `ExUnit.start()`:

```elixir
ExUnit.start()
Code.ensure_loaded!(MyApp.RoundingTest)
ExUnit.Server.add_module(MyApp.RoundingTest, MyApp.RoundingTest.__ex_unit__(:config))
Application.put_env(:muro, MyApp.RoundingTest, MyApp.RoundingAdapter)
```

`ExUnit.Server.add_module/2` is public and marked `@moduledoc false`. A project with no `*_test.exs` file makes `mix test` run the suite with the formatters removed and then print `There are no tests to run`. A `mix new` project already has one such file. Keep one.

A script that compiles the suite calls `ExUnit.start(autorun: false)` before the file is compiled.

### Hand-written module

The book:

```
def round : run Π (n : Nat) → Nat :=
  λ (n : Nat) → n

def round-ok : evidence {round (suc 0) ≡ suc 0 : Nat} :=
  refl
```

The adapter, compiled in the same run as `test/support/rounding_test.ex`:

```elixir
defmodule MyApp.Rounding do
  @behaviour MyApp.RoundingTest.Behaviour

  @impl true
  def round(n), do: n
end
```

`test/test_helper.exs` registers the case and points the suite at `MyApp.Rounding`, as above. `mix test` runs `round-ok` against that function. The arguments and the expected result are emitted shapes, `{:suc, 0}` in this equation.

### Remote service

The same behaviour. The adapter talks to the other implementation. The shapes stay the emitted ones until repr (#131).

```elixir
defmodule MyApp.RoundingAdapter do
  @behaviour MyApp.RoundingTest.Behaviour

  @impl true
  def round(n) do
    {:ok, {{_, 200, _}, _headers, body}} =
      :httpc.request(
        :post,
        {~c"https://rounding.internal/round", [], ~c"application/octet-stream", encode(n)},
        [],
        []
      )

    decode(body)
  end

  # n and the result are emitted shapes, 0 or {:suc, _}, until repr (#131).
  defp encode(0), do: ~c"0"
  defp encode({:suc, n}), do: [?s | encode(n)]

  defp decode(~c"0"), do: 0
  defp decode([?s | n]), do: {:suc, decode(n)}
end
```

```elixir
Application.put_env(:muro, MyApp.RoundingTest, MyApp.RoundingAdapter)
```

A wrong answer fails the test whose name is `priv/muro/rounding.muro round-ok`. The assertion message is `priv/muro/rounding.muro:4 round-ok`. The ExUnit header shows the test name. The message shows the name and the line in the book.

`:inets` must be started before the request. The encoding above is one encoding of the emitted `Nat` shape. The service and the adapter agree on it. The suite does not.

## Param libraries

A library states what every implementation supplies, and its closed equations are the suite those implementations run. `mix muro.emit kit.muro --backend exunit` checks the file with the params as assumptions and prints the module. `mix muro.check kit.muro`, and `mix muro.emit kit.muro` with no backend, still refuse it: `param decide is supplied by a file that imports this one`. The same message is what a `kind: :elixir` manifest entry reports. The loader option is `params: :open`. Only `Muro.emit_exunit/3`, `mix muro.emit --backend exunit`, and a `kind: :exunit` entry pass it.

```muro
data Key : Type where
  k0 : Key
  k1 : Key

data Answer : Type where
  yes : Answer
  no : Answer

def rule : run Π (k : Key) → Answer :=
  λ (k : Key) →
    match k motive (λ _ → Answer)
      | k0 => yes
      | k1 => yes

param decide : run Π (k : Key) → Answer
param decide-is : evidence Π (k : Key) → {decide k ≡ rule k : Answer}

def golden : run Key := k0

def golden-k0 : evidence {decide golden ≡ yes : Answer} :=
  rewrite (decide-is golden) motive (λ z → {z ≡ yes : Answer}) in refl

def k0-yes : evidence {decide k0 ≡ yes : Answer} :=
  rewrite (decide-is k0) motive (λ z → {z ≡ yes : Answer}) in refl

def k1-yes : evidence {decide k1 ≡ yes : Answer} :=
  rewrite (decide-is k1) motive (λ z → {z ≡ yes : Answer}) in refl

def wrap : run Π (k : Key) → Answer :=
  λ (k : Key) → decide k

def through : evidence {wrap k0 ≡ yes : Answer} :=
  rewrite (decide-is k0) motive (λ z → {z ≡ yes : Answer}) in refl
```

Emitting that file with `--backend exunit` prints three tests and one skip. `golden` is the literal `:k0`. `decide-is` is an `evidence` param, so it is not a callback and not a candidate. `through` calls `decide` by evaluating `wrap`, so it is skipped. The adapter is not threaded through `wrap`.

```elixir
@callback decide(term()) :: term()

test "kit.muro golden-k0", %{impl: impl} do
  assert impl.decide(:k0) == :yes, "kit.muro:20 golden-k0"
end

test "kit.muro k0-yes", %{impl: impl} do
  assert impl.decide(:k0) == :yes, "kit.muro:23 k0-yes"
end

test "kit.muro k1-yes", %{impl: impl} do
  assert impl.decide(:k1) == :yes, "kit.muro:26 k1-yes"
end
```

```
# Skipped: 1
#   through (kit.muro:32): calls param decide through wrap
```

A param call is `impl.<name>(...)` only when it is the head of the left-hand side or the head of the right-hand side, and the arguments normalize to closed values. Both sides may be param calls: `{decide k0 nil ≡ decide k1 nil}` is `impl.decide(:k0, :nil) == impl.decide(:k1, :nil)`. A library `run` that does not touch a param, such as `golden` or `rule`, is evaluated to a closed value the way an inlined golden is.

The callback's arity is the number of non-erased binders, the same count the Elixir backend emits for a `run` of that type. The name is the Elixir spelling of the param. A Muro implementation that supplies the param with an ordinary `run` definition is emitted with that name and arity and satisfies the behaviour. Callbacks are generated only for params that an emitted test calls. A param that appears only in a skipped equation is not a callback. The spec is `term()`, in the order the tests first call the param, left-hand side then right-hand side, the same layout as a `run` definition's callback.

These shapes are skipped, and the reason names the param:

- an argument type is a Π: `param <name> takes a function`. Each binder of the param's type is walked, so a result that is itself a Π is another argument, not `returns a function`.
- an argument or the result is `Stream`: `param <name> takes a stream` or `param <name> returns a stream`. A session name in the type does not reach this row. The book fails to check, `ping is a session, not a definition`. There is no channel type to skip.
- an argument is not data the emitter renders as a literal, such as `I64`: `param <name> arguments are not data`. A spec alias is not unfolded, so a name that stands for a function and is not written as a Π lands here, or on `returns a value that is not data`.
- a `run` param occurs in an argument or a result, not at the head of that side: `calls param <name> inside a value`.
- evaluating a library `run` reaches a `run` param: `calls param <name> through <def>`.

A head whose mode is not `run` keeps the 0.16.76 reason, `<name> is not a run definition`. A `param` and a `def` of the same name in one file are still a duplicate name. The supplier is an importing book.

A hand-written adapter is an ordinary module. This one passes the three tests:

```elixir
defmodule GoodKit do
  @behaviour KitTest.Behaviour

  def decide(:k0), do: :yes
  def decide(:k1), do: :yes
end
```

```elixir
Application.put_env(:muro, KitTest, GoodKit)
```

The key is the test module, the same key the 0.16.76 suite reads. The default, when the key is unset, is the book's emitted module (`Kit` for `kit.muro`). A module that is not loaded, or that does not export the callback, fails in `setup_all` with the same messages as before.

An implementation written in Muro supplies the params. This file checks, and `mix muro.emit impl.muro` prints the module:

```muro
import "kit.muro"

def decide : run Π (k : Key) → Answer :=
  λ (k : Key) → rule k

def decide-is : evidence Π (k : Key) → {decide k ≡ rule k : Answer} :=
  λ (k : Key) → refl
```

`mix muro.emit impl.muro --backend exunit` prints `0 tests, 0 skipped`. The equations live in `kit.muro`. The supplying `decide-is` is quantified, so it is not a candidate.

The same command with `--imports` prints four tests, all named from `kit.muro`. `through` is now a test, `impl.wrap(:k0) == :yes`, because `decide` is supplied and `wrap` reduces. The behaviour has `decide/1` and `wrap/1`. The default implementation is the emitted `Impl` module, which contains both, so the suite passes with no `Application.put_env`.

A larger library, a `decide` of a key and a list whose silence and empty cases are the wildcard `true`, emitted 14 tests and the callbacks `decide/2` and `ok/0`. Six equations were skipped: `calls param decide through f`, `calls param decide inside a value`, `param observe takes a stream`, `param hoist takes a function`, `param ticks returns a stream`, and `param widen arguments are not data`. The emitted implementation and a hand-written adapter passed all 14. An adapter that reads silence as `false` failed exactly `conformance.muro sil-k0`, `conformance.muro sil-k1`, and `conformance.muro sil-deep`. Each failure also showed `conformance.muro:<line> <name>`.

## Imported equations

`imports: true` and `--imports` add the closed equations of the files this book imports directly. The book's own equations come first, then each import in the order the `import` lines appear, and each file's equations in that file's order. A file is kept once, the first time its path appears, including a diamond and a repeated import. The book's own file is not collected twice. The imports of those files are not followed, so an equation that lives only in an indirect import is absent. The order does not depend on directory listing or on the absolute path. The printed path is relative to the project root, with `/` separators.

```elixir
[
  muro: "0.18.1",
  modules: [
    {"kit.muro", KitTest, "test/kit_test.exs", [kind: :exunit]},
    {"impl.muro", ImplTest, "test/impl_test.exs", [kind: :exunit, imports: true]}
  ]
]
```

`mix muro.emit impl.muro --backend exunit --imports` is the same collection. `--imports` with `--backend elixir`, or with `c`, `rust`, `asm`, `otp`, `fsm`, or `--node`, is an error. `imports:` on a `kind: :elixir` entry is an error and names the entry index (`modules entry 1: imports: is only valid for kind: :exunit`). A non-boolean is `imports: must be a boolean`.

A `pkg:` import is a direct import like any other. The test is named with the file under the project root, `muro_deps/shared/wire.muro wire-ok`, not with the `pkg:` spelling.

The book hash already covers every imported file. `mix muro.gen --check` reports the suite stale when one of those files changes, whether or not `imports:` is set. A hand edit of the suite is still the hand-edited message.

## Skips

The first problem wins. `mix muro.emit --backend exunit` prints the module on standard output. Each skip goes to standard error, then a summary line, including when nothing was skipped:

```
skipped step-ok (round.muro:8): step is run internal and is not exported
1 tests, 1 skipped
```

`mix muro.gen` prints, after that target's `written` or `unchanged` line:

```
skipped test/rounding_test.exs: step-ok (priv/muro/rounding.muro:8): step is run internal and is not exported
```

`--check` does not print skip lines. The generated file records them in the test module, after the moduledoc, so the body sha256 covers them:

```elixir
# Skipped: 1
#   step-ok (priv/muro/rounding.muro:8): step is run internal and is not exported
```

No skips:

```elixir
# Skipped: none
```

| Cause | Reason |
| --- | --- |
| `f` is not a `run` definition (`spec`, `evidence`, `data`, or an unknown name) | `<f> is not a run definition` |
| `f` is a prelude `run` (it has no file; it is emitted only as `defp` when a `run` calls it) | `<f> is a prelude run and is not defined by the book` |
| `f` is `run internal` | `<f> is run internal and is not exported` |
| the equation passes more arguments than `f`'s type lists | `<f> is applied to more arguments than its type lists` |
| any argument sits on an erased binder of `f` | `argument passed at an erased binder of <f>` |
| an argument or the result does not normalize within fuel | `argument N did not normalize within fuel` or `result did not normalize within fuel` |
| normalization fails for another reason | `argument N did not normalize` or `result did not normalize` |
| the normal form is a function, a stream, or a machine term (`I64`, `F32`, `Tensor`, `toi64`, and the rest of that family) | `argument N normal form is a function`, `a stream`, or `a machine term` (or `result normal form is …`) |
| the normal form has no literal the emitter prints | `argument N normal form has no literal` or `result normal form has no literal` |
| the normal form is open: a free variable, or a name that is not a constructor. Normalization unfolds `run` only, so an `evidence` or `spec` name used as a value lands here | `argument N is not closed (free variable or unresolved param)` or the same sentence for `result` |
| a `run` param is nested in an argument or a result, not at the head of that side | `calls param <name> inside a value` |
| evaluating a library `run` reaches a `run` param. The adapter is not compiled into that definition | `calls param <name> through <def>` |
| a `run` param's argument is a function, a stream, or not data, or its result is a stream or not data | `param <name> takes a function`, `takes a stream`, `returns a stream`, `arguments are not data`, or `returns a value that is not data` |
| after the values normalize, the number of arguments is not the emitted arity (a partial application whose result is a function is the function row above, and that row wins) | `<f> is applied to N arguments and the emitted function has arity A` |

`N` is the argument's position in the equation, starting at 1.

## Manifest

A 3-tuple is still an Elixir module. An ExUnit entry adds a keyword list:

```elixir
[
  muro: "0.18.1",
  modules: [
    {"priv/muro/rounding.muro", MyApp.Rounding, "lib/my_app/rounding.ex"},
    {"priv/muro/rounding.muro", MyApp.RoundingTest, "test/rounding_test.exs",
     [kind: :exunit, impl: MyApp.Rounding]},
    {"kit.muro", KitTest, "test/kit_test.exs", [kind: :exunit, imports: true]}
  ]
]
```

`kind` defaults to `:elixir`. `impl` is optional and only valid for `:exunit`. It must be an alias atom. `imports:` is optional, only valid for `:exunit`, and must be a boolean. The default is `false`. Unknown options, an unknown kind, `impl:` on an Elixir entry, `imports:` on an Elixir entry, a non-boolean `imports:`, and an `impl` that is not an alias are errors, and the message names the entry index (`modules entry 1: …`). A 4-tuple that is not a keyword list is the same error as a malformed 3-tuple: `modules entry 1 is not {book, module, target}`.

The usual target is `test/<name>_test.exs`. `test/support/<name>.ex` is the layout above, the one where `@behaviour` is checked at compile time. Formatting uses the project's `.formatter.exs`. `Mix.Tasks.Format.formatter_for_file/2` formats `.ex` and `.exs` when a formatter file exists, including a file the `inputs` list does not cover. The bytes are a fixed point of that formatting.

## Drift

The header is the same two lines as any other generated file: the Muro version, the book path, the book sha256, and the body sha256. The skip block sits in the body. `mix muro.gen --check` fails when the book gains, loses, or changes an example, including a change that only alters the skipped set: the book hash moves, and the existing message reports the target stale. A hand edit of the suite, including the skip comments, is the existing hand-edited message. There is no separate class for skips.

`.github/workflows/muro.yml` from `mix muro.init --ci github` already runs `mix muro.gen --check`. A project that commits the suite gets that check with no extra step.

## Design choices

The implementation is an application env value, read in `setup_all`, because the generated file must stay a function of the book. The key is the test module atom. Elixir 1.18 warns `passing non-atom as application env key is deprecated` for a tuple key, so `{TestModule, :impl}` is not the key. Several suites in one project stay independent: each reads its own module. The default needs no config. A missing or incomplete module fails in `setup_all` with the module name in the message, before the assertions run.

The behaviour lives in the same file as the tests so one manifest entry carries both. Two layouts are documented above because a single `.exs` is loaded by `mix test` and is not compiled before an adapter in `test/support`. Both were run on Elixir 1.18.4. The `.exs` layout runs the tests and warns that the behaviour does not exist when an adapter is compiled earlier. The `.ex` layout, with `elixirc_paths` and `ExUnit.Server.add_module/2`, warns `function round/1 required by behaviour … is not implemented` for an incomplete adapter and runs the test once a `*_test.exs` file is present.

Callbacks are `term()`. A precise `Nat` type in the callback would drift from the emitted shape and from the later `repr` hook. `emit_closed/2` is the one place that hook belongs.

A candidate is only an `evidence` equation whose left-hand head is a name. Everything else in the file is ignored, including quantified evidence and an `evidence` param. An erased argument skips the whole equation. The prelude check comes before the internal check, because a prelude `run` is not exported and is not defined by the book. The message names the prelude.

A `run` param is a callback only at the head of a side, and only for a first-order type whose arguments are data. Library `run` definitions are not rewritten to call the adapter. An equation that reaches a param through one of them is skipped on the library, and becomes an ordinary test once an importing book has supplied that param and `imports:` is on, because the param then reduces. The name is `"<file> <def-name>"` so the line can move. `imports:` follows only the `import` lines of the book being emitted.

A `run internal` the book does not call is still emitted as `defp` by the Elixir backend. The suite skips the equation and does not call that function. Compiling the emitted module then warns that the function is unused (`warning: function step/1 is unused`). A host that treats warnings as errors sees that warning from the emitted module.

Next: [Committed modules](gen.md).

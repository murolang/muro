---
title: Library
slug: library
order: 16
summary: The ordinary library, imported as std:. Bool, Le, List, Maybe, and comparison.
---

# Library

In brief: five ordinary `.muro` books ship inside the compiler. `import "std:list.muro"` loads that copy. The bytes are the same from a Hex package, from the self-contained executable, and from a checkout of this repository.

```
import "std:list.muro"
```

The name after `std:` is a file in the library: `bool.muro`, `le.muro`, `list.muro`, `maybe.muro`, or `ord.muro`. A name that is not one of those is an error at the import, and the message lists the books:

```
unknown standard library book "nope.muro"
available books: bool.muro, le.muro, list.muro, maybe.muro, ord.muro
```

`..`, a leading `/`, a backslash, or any other path that leaves the library is refused: `import "std:../le.muro" leaves the standard library`. A relative import written inside a library book stays in the library. `list.muro` imports `maybe.muro`, `maybe.muro` imports `bool.muro`, and `ord.muro` imports `le.muro`. A book reached by two imports, directly or through another book, joins once.

The id of a loaded book is `std:list.muro`, not a path on disk. An error inside a library book is reported at that id. `mix muro.gen` hashes an imported library book as `std/<file>`. The prelude is not in that hash. The version pin covers the checker, the emitter, the prelude, and this library. Changing a library book changes the hash of every book that imports it.

These books are not the prelude. The prelude stays `pred`, `plus`, `inj-suc`, `plus_suc`, `sym`, and `cong`, in scope behind every file, including a library book. None of these books defines those names. `std:` is not a package: there is no manifest entry, no lock line, and `muro deps.get` does not fetch it. See [Packages](packages.md).

`examples/cshrl` keeps its own Nat lemmas. It does not import these books.

Agda does not model `import` or file loading. What it checks is the book after the imports have been joined. See [Limits](limits.md).

A `run` in this library is first-order. A function argument is outside the closed run image that C, Rust, and assembly emit, so the library has no `map`.

## bool.muro

`Bool`, with `true` declared before `false`. `not`, `and`, and `or` are `run`. `and true b` is `b`, and `or false b` is `b`.

Evidence: `not-not`, `and-true`, `and-false`, `or-true`, `or-false`, `and-comm`, `or-comm`, and `not-and` (`not (and a b)` is `or (not a) (not b)`).

## le.muro

`Le` is ≤ on `Nat`. It is `spec`, and it computes: `Unit` when the inequality holds, `Empty` when it does not. A closed inequality is `tt`. A false one is eliminated with `matchEmpty`.

`le-refl` and `le-trans` are evidence. `max` is `run`. `le-max-left` is `m ≤ max m n`. `le-max-right` is `n ≤ max m n`. `max-mono-left` and `max-mono-right` are monotonicity in each argument.

## list.muro

`List`, with `nil` and `cons`. It imports `maybe.muro`.

`Elem` is a `spec` predicate, not an indexed family. At `nil` it is `Empty`. At `cons` it is `Or` of head-equality and tail membership. `Or` is the sum in this book, with `yes` and `no`.

`length` and `lookup` are `run`. `lookup` returns `Maybe`: `nothing` past the end, `just` the element at a numeral index. Recursion is on the list. `ones2` is two successors.

Evidence: `length-ones2`, `length-nil`, `length-cons`, `lookup-nil`, `lookup-zero`, `lookup-suc`, `elem-here`, `elem-there`, `elem-nil`, and `elem-length`. `elem-nil` is the `Empty` that `Elem` computes at `nil`. `elem-length` says a list that has an element has length at least one, by the local `spec` `Le-list`, so this book does not import `le.muro`.

## maybe.muro

`Maybe`, with `nothing` and `just`. It imports `bool.muro`.

`fromMaybe`, `isJust`, and `isNothing` are `run`. `isNothing` is `not (isJust A m)`. The type argument is erased.

Evidence: `fromMaybe-nothing`, `fromMaybe-just`, `isJust-nothing`, `isJust-just`, and `fromJust1`.

## ord.muro

`Ordering`, with `lt`, `eq`, and `gt`. It imports `le.muro`.

`compare` is `run` on `Nat`. `CompareAt m n o` says what that result means: `lt` is `Le (suc m) n`, `eq` is `{m ≡ n : Nat}`, and `gt` is `Le (suc n) m`. `compare-sound` inhabits `CompareAt m n (compare m n)`. `lift-compare` carries a result at `p` and `q` to their successors, and the `eq` arm uses `cong` from the prelude.

`compare-lex` is `run` on `Nat × Nat`. The first components are compared first. `lex-step` is `run internal`: the first ordering wins, unless it is `eq`, in which case the second decides. `LexAt` says what that pair result means, given the ordering of the first components, and `lex-sound` inhabits it. `LexSide` and `LexGt` are the two sides of that statement. Each of them matches the ordering already in hand.

## Examples

`examples/list.muro` and `examples/maybe.muro` import the library books and declare nothing of their own. `examples/sort.muro`, `examples/higher_order.muro`, and `examples/second_field.muro` import `std:list.muro`. Check a library book on disk with `mix muro.check lib/muro/std/le.muro`, or check an import from any directory:

```
import "std:bool.muro"

def n : run Bool := not false
```

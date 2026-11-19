---
title: Library
slug: library
order: 16
summary: The ordinary library, imported as std:. Bool, Le, List, Maybe, comparison, a binary successor, and unsigned word arithmetic.
---

# Library

In brief: seven ordinary `.muro` books ship inside the compiler. `import "std:list.muro"` loads that copy. The bytes are the same from a Hex package, from the self-contained executable, and from a checkout of this repository.

```
import "std:list.muro"
```

The name after `std:` is a file in the library: `bool.muro`, `le.muro`, `list.muro`, `maybe.muro`, `ord.muro`, `suc_bin.muro`, or `word.muro`. A name that is not one of those is an error at the import, and the message lists the books:

```
unknown standard library book "nope.muro"
available books: bool.muro, le.muro, list.muro, maybe.muro, ord.muro, suc_bin.muro, word.muro
```

`..`, a leading `/`, a backslash, or any other path that leaves the library is refused: `import "std:../le.muro" leaves the standard library`. A relative import written inside a library book stays in the library. `suc_bin.muro` imports `list.muro`, `list.muro` imports `maybe.muro`, `maybe.muro` imports `bool.muro`, `ord.muro` imports `le.muro`, and `word.muro` imports `le.muro`. A book reached by two imports, directly or through another book, joins once.

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

`le-refl` and `le-trans` are evidence. `max`, `min`, and `minus` are `run`. `minus m n` is truncated subtraction: `0` when `n` is larger. `le-max-left` is `m ≤ max m n`. `le-max-right` is `n ≤ max m n`. `max-mono-left` and `max-mono-right` are monotonicity in each argument. `le-min-left` is `min m n ≤ m`. `le-min-right` is `min m n ≤ n`. `minus-le-zero` is `minus m n ≡ 0` when `m ≤ n`.

In emitted Elixir, `max`, `min`, and `minus` are the integer operations they compute, and so is `compare` from `ord.muro` ([Emit](emit.md#how-values-look)).

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

`compare-lex` is `run` on `Nat × Nat`. The first components are compared first. The second components are compared only when that ordering is `eq`. `lex-step` is evidence: the first ordering wins, unless it is `eq`, in which case the second decides. `compare-lex` inlines that match, so the second comparison is not an argument of a call. `LexAt` says what that pair result means, given the ordering of the first components, and `lex-sound` inhabits it. `LexSide` and `LexGt` are the two sides of that statement. Each of them matches the ordering already in hand.

## suc_bin.muro

A binary successor beside inductive `Nat`. It imports `list.muro`. Machine integers (`U8`, `U32`, `U64`, `I64`) are fixed-width residues and do not replace this book ([Machine numbers](machine.md)).

`Bit` is `O` and `I`. A `List Bit` is a numeral, least significant bit first. Leading zeros are allowed. The empty list is zero.

`sucBit`, `sucBits`, and `sucBin` are a Mealy machine: the carry is the state, and `sucBin` starts at `I`. `fromBits` reads a bit list as a `Nat`. `toBits n` is `n` applications of `sucBin` from `nil`. `double` is `run internal`, the place-value shift `fromBits` needs. No host integer is used, and there is no fixed width.

Evidence: `sucBits-id`, `sucBin-step`, `fromBits-toBits`, `sucBin-corresp` (`fromBits (sucBin (toBits n)) ≡ suc n`), `suc-11` (the bits of 11 step to the bits of 12), `bits11-nat`, and `suc-11-nat`.

Check on disk with `mix muro.check lib/muro/std/suc_bin.muro`. Import it with `import "std:suc_bin.muro"`.

## word.muro

Unsigned checked arithmetic agrees with Nat. It imports `le.muro`, and `minus` is that book's truncated subtraction. `times` is `run internal` here. `wlink` accepts `plus`, `minus`, `times`, and `Le` only as these definitions. A different binding is refused. `I64` is outside this book: `toNat` of −1 is 2^64−1.

For `U8`, `U32`, and `U64`, and for `addc`, `subc`, and `mulc`, the book gives three lemmas. The body of each is `wlink`.

- `addc-val-u64`, and the `u8` and `u32` twins, with `subc-val-*` and `mulc-val-*`, say `toNat` of the payload is `plus`, `minus`, or `times` of the two `toNat`s.
- `addc-fit-*` and `mulc-fit-*` say that `wsome` gives `Le` of the successor of that Nat result below the modulus. `subc-fit-*` says `Le (toNat b) (toNat a)`.
- `addc-some-*` and `mulc-some-*` turn that bound into `wsome` of `toU8`, `toU32`, or `toU64` of the Nat result. `subc-some-*` turns `Le (toNat b) (toNat a)` into `wsome` of `toUk` of `minus`.

A closed equation is still `refl`. `boundary-u64` is `addc` of `toU64 4294967295` and 1, `wsome` of `toU64 4294967296`. `boundary-u32` is that pair at `U32`, and it is `wnone`. `boundary-mul` is `mulc` of `toU64 4294967296` with itself, and it is `wnone`.

`coffee`, `tip`, and `tax` are `U64` amounts, 100, 25, and 10. `line` is the checked sum of coffee and tip, and `line-nat` cites `addc-val-u64` for that Nat total. `subtotal` is the closed word 125. `bill` adds tax under the fit, and `bill-nat` cites `addc-val-u64` again.

Check on disk with `mix muro.check lib/muro/std/word.muro`. Import it with `import "std:word.muro"`. See [Machine numbers](machine.md).

## Examples

`examples/list.muro` and `examples/maybe.muro` import the library books and declare nothing of their own. `examples/sort.muro`, `examples/higher_order.muro`, and `examples/second_field.muro` import `std:list.muro`. Check a library book on disk with `mix muro.check lib/muro/std/le.muro`, or check an import from any directory:

```
import "std:bool.muro"

def n : run Bool := not false
```

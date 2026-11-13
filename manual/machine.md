---
title: Machine numbers
slug: machine
order: 12
summary: U8, U32, U64, and I64 are fixed-width residues. F32 and Tensor stay Nx. Nat stays Peano.
---

# Machine numbers

In brief: `U8`, `U32`, `U64`, and `I64` are fixed-width residues. Wrapping arithmetic stays inside the width. Checked arithmetic, division, and remainder return `Opt`. Comparisons return `WBool`. There is no implicit coercion. Nat stays Peano. `F32` and `Tensor` stay Nx.

## Residues

`U8` is ℕ modulo 256. `U32` is ℕ modulo 2^32. `U64` is ℕ modulo 2^64. `I64` is those same 64 bits read as two's complement. The bit pattern of −1 is 2^64−1. The bit pattern of the minimum is 2^63.

A value of one of these types is that residue, a machine integer. `toU8`, `toU32`, `toU64`, and `toI64` are total on `Nat` and reduce modulo the width. A closed numeral is that integer. A Peano numeral still reduces by its constructors. There is no kind-less `ofNat`. `toNat` returns the residue as a closed numeral, so `toNat` of `I64` −1 is 2^64−1, not a signed integer. A `match` still sees `0` and `suc`: it peels one successor from a closed numeral and does not expand the residue. Word operations and that numeral do not spend fuel in proportion to the value.

`asU8`, `asU32`, `asU64`, and `asI64` cast. A cast is the residue modulo the destination width. Narrowing keeps the low bits. Widening an unsigned word zero-extends. `U64` and `I64` are the same width, so each cast reinterprets the bits.

## Operations

Both arguments of a binary operation have the same width. A shift's amount is a `Nat`.

| Term | Meaning |
| --- | --- |
| `addi` `subi` `muli` | Wrap modulo 2^w. On `I64` this is the operation on the bits. `subi` of 0 and 1 is the all-ones word. |
| `addc` `subc` `mulc` | `Opt` of that width. `wsome` when the result fits, `wnone` when it does not. |
| `divi` `remi` | `Opt`. `wnone` when the divisor is 0. Signed `divi` and `remi` are also `wnone` for the minimum divided by −1. |
| `eqi` `lti` `lei` | `WBool`. |
| `andi` `ori` `xori` `noti` | Bitwise. `noti` of 0 is the all-ones word. |
| `shli` `shri` | Shift by a `Nat`. An amount at or past the width does not call a host shift. |

Unsigned `addc` and `mulc` succeed when the ℕ result is below 2^w. Unsigned `subc` succeeds when the second argument is at most the first. Signed `addc`, `subc`, and `mulc` succeed when the ℤ result lies in [−2^63, 2^63−1]. `addc` of the signed minimum with itself is `wnone`. `addc` of the signed maximum with 1 is `wnone`. `subc` of signed 0 and 1 is `wsome` of −1.

`divi` truncates toward zero. `remi` has the sign of the dividend.

Unsigned `lti` and `lei` compare the residues. Signed `lti` and `lei` compare the two's complement values, so `lti` of `I64` −1 and 0 is `wtrue`, and `lti` of `U8` 255 and 0 is `wfalse`.

`shli`, and an unsigned `shri`, yield 0 when the amount is at or past the width. A signed `shri` past the width yields 0 when the word is non-negative and the all-ones word when it is negative. A signed `shri` within the width is arithmetic: `shri` of −1 by 1 is −1.

`WBool` is `wtrue` or `wfalse`. `Opt A` is `wsome` or `wnone`. `wnone` is checked against an `Opt` type. Both are kernel types, not the library `Bool` and `Maybe`, and both are data, passed by value. `U8`, `U32`, `U64`, `I64`, `WBool`, and `Opt` of a data type are data, so `+` is allowed on them. `match` eliminates them. The arms are those constructors, in that order, with the motive written out. A closed scrutinee reduces before the arms are read.

Closed equations over these types reduce. `{addi (noti (toU8 0)) (toU8 (suc 0)) ≡ toU8 0 : U8}` is `refl`.

## What the emitters write

C uses `uint8_t`, `uint32_t`, `uint64_t`, and `int64_t`, by value. Signed wrapping is unsigned arithmetic, cast back. Checked operations use `__builtin_add_overflow`, `__builtin_sub_overflow`, and `__builtin_mul_overflow`. A shift walks the `Nat` and stops at the width, so a shift of 64 bits is not evaluated. `divi` and `remi` test the divisor, and the signed minimum over −1, before `/` or `%`. `Opt` is a struct with `tag` and `val`, tag 0 for `wnone` and tag 1 for `wsome`. `WBool` is `uint8_t`, 1 or 0. A `match` on `WBool` is a test of that word. A `match` on `Opt` is a test of `tag`, and the payload is `val`. Neither walks `Nat` and neither allocates.

Zig uses `u8`, `u32`, `u64`, and `i64`, with `+%`, `-%`, and `*%`. Checked operations use `@addWithOverflow`, `@subWithOverflow`, and `@mulWithOverflow`. Division uses `@divTrunc` and `@rem` after the same guards. `Opt` is `?T`. `WBool` is `u8`. A `match` on `WBool` tests that byte against 0. A `match` on `Opt` is `if (o) |v|`. Neither allocates.

Rust uses `wrapping_add`, `wrapping_sub`, `wrapping_mul`, `checked_add`, `checked_sub`, `checked_mul`, `checked_div`, and `checked_rem`. A shift uses `<<` or `>>` only when the amount is below the width. `Opt` is `Option`. `WBool` is `bool`. A `match` on `WBool` is `true` and `false`. A `match` on `Opt` is `Some` and `None`. Neither builds an `Rc`.

Elixir emits the residue as an integer. An `I64` value is that residue, not a negative integer. `Opt` is `{:some, n}` or `:none`. `WBool` is `true` or `false`. A `match` on `WBool` is those two booleans. A `match` on `Opt` is `{:some, n}` and `:none`. JavaScript emits the same boolean, and `Opt` as `{k: "some", v}` or `{k: "none"}`. A closed word is a function. A residue that is not a closed literal is a call to `Muro.Word`: `of`, `cast`, the wrapping and checked operations, the shifts, and the bitwise operations. Those calls run in the host. The Mix archive checks the book and emits the module, and it does not put `Muro.Word` on the host's compile path. The host project depends on muro (`{:muro, "~> 0.20.31"}`). Without that dependency, `mix compile --warnings-as-errors` reports `Muro.Word` as undefined, and calling the emitted function raises `UndefinedFunctionError`. The OTP backend does not emit `run` bodies. Assembly stays the `Nat` fragment (`asm:scope`). A `match` on `WBool` or `Opt` is outside that fragment.

`F32`, `Tensor`, `addt`, and `packI` are refused (`c:machine`).

## An example

`examples/fnv.muro` is 32-bit FNV-1a over a list of `U8`. The list is a monomorphic `ByteList`, so the byte is stored by value and each `cons` is one cell. The offset basis is 2166136261 and the prime is 16777619, each built by `shli` and `ori` of one, because `Nat` is Peano. `hashEmpty` is the basis. `hashA` hashes the byte 97 and is 3826002220. `fnv-empty` and `fnv-a` are `refl`. `examples/fnv_slice.muro` is the same hash over a kernel `Slice`. The basis and the prime there are closed `U32` literals, and the walk does not allocate a cell per octet.

## F32 and Tensor

`F32` and `Tensor D S` still wrap `%Nx.Tensor{}`. `addt` adds tensors. `packI` packs two `I64`s into a tensor whose shape is `toI64` of two. `Tensor D S` is data, so `+` is allowed on a tensor. Mix depends on `{:nx, "~> 0.9"}` only when a book uses them. Emit of those operations is `Nx.add`, `Nx.stack`, and `Nx.tensor`, not `defn`.

`examples/nx_add.muro` keeps that tensor. Its `addI` is the wrapping `I64` word, so `addI` of 3 and 4 is 7. `doubled` is still `[2, 4]` after `Nx.to_flat_list/1`. A file that mentions `addt` or `packI` is refused by C, Rust, and Zig.

There is no second index language. A tensor shape is an `I64`.

## What you cannot do

- Identity `{e₁ ≡ e₂ : F32}` or `{e₁ ≡ e₂ : Tensor F32 S}` in the kernel.
- An implicit coercion between `Nat` and `U8`, `U32`, `U64`, or `I64`. The maps are `toU8`, `toU32`, `toU64`, `toI64`, and `toNat`.
- Index a `Vec` by a word. Lengths in [indexed data](indexed.md) are Peano.
- A shift or a division that steps outside the guards above. The guards are the result, not a host exception.

The statements are `agda/Muro/Word.agda`, checked under `--safe`. `ofNat∘toNat` and `toNat∘ofNat` are the two round trips. `wrapAdd-mod`, `wrapSub-mod`, and `wrapMul-mod` are the wrapping operations modulo 2^w. `checkedAdd-iff`, `checkedSub-iff`, and `checkedMul-iff` say a checked operation returns a value exactly when the result fits. `div-iff` and `rem-iff` say division and remainder return a value exactly when the divisor is legal.

Next: [Emit](emit.md).

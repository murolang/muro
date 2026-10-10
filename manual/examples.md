---
title: Examples
slug: examples
order: 14
summary: Every file in examples/ and what it is for.
---

# Examples

In brief: every file in the sections above Refused checks with `mix muro.check path`. They are the worked book, not sketches. Prefer copying from here over inventing syntax. The files under Refused are what that command turns down.

Check one file:

```
mix muro.check examples/half_ok.muro
```

Check the built-in book (must match `half_ok.muro`):

```
mix muro.check
```

## half_ok.muro

The three modes in one book.

```
IsEven : Nat → Type                 -- spec
half   : Nat → Nat                  -- run
half_ok : (n : Nat) → IsEven n →    -- evidence
            plus (half n) (half n) ≡ n
```

Also defines `plus` (run) and `plus_suc` (evidence). Half of eight is four. Evidence is `match` + `refl` + `rewrite` + `matchEmpty`. Nothing here except `plus` and `half` is emitted.

See [The wall](wall.md), [Terms](language.md), [Identity](identity.md).

## internal_ok.muro

`run internal` helper `step` emits `defp`. `inc` is `run` and calls it. See [Emit](emit.md).

## zeros.muro

A productive `run` Stream of zeros. `head-zeros` is `{head zeros ≡ 0 : Nat}` by `refl`.

## nats.muro

`natsFrom n` is the stream `n, suc n, …`. Emit is `Stream.unfold/2`. `(+ k : Nat)` is legal because Nat is Data.

## always.muro

`Always` as evidence: every element of `zeros` is `0`. The proof is the head equation together with the same proof at the tail. `uncons` of that proof is the equation paired with the predicate at `tail zeros`.

## bisim.muro

`zeros ~ zeros'` and `tail (natsFrom n) ~ natsFrom (suc n)`. Rutten’s stream calculus, Theorem 2.1. `uncons` of `zeros ~ zeros'` is the head equation and `tail zeros ~ tail zeros'`. Evidence only.

## dominance.muro

A declared ν family, `Dom f g`: every element of `f` is at most the element of `g` at the same position. `dom-refl` proves `Dom s s`, `zeros-below` proves `Dom zeros (natsFrom n)` with the tail obligation at `natsFrom (suc n)`, and `dom-head` reads the head obligation back with `head`. Evidence only; `zeros` and `natsFrom` are emitted.

See [Streams](streams.md).

## even_dec.muro

`Dec P = P ⊎ (P → Empty)`. `evenDec` decides `IsEven n`. A decision, not LEM. Evidence; not emitted.

## either_run.muro

A `run` sum. `fromLeft` emits `{:left, _}` / `{:right, _}`.

See [Either and Dec](either.md).

## list.muro

`List A`, `nil` / `cons`, `length`, `ones2`. `List A` is Data iff `A` is. `length-ones2` is `refl`.

## maybe.muro

`Maybe`, `fromMaybe`, `fromJust1`. Erased type argument.

## even_odd.muro

`even` and `odd` call each other and descend on the same `Nat` argument. `even-two` is `refl`.

## tree.muro

Binary trees of structure (no payloads). `size` descends on both children.

## vec.muro

`Fin n`, `Vec A n`, `lookup` without a runtime bounds check. The inner `match` carries the index equation in its motive and `rewrite`s along `inj-suc` (the convoy pattern). `lookup-ok` is `refl`.

See [Data](data.md) and [Indexed data](indexed.md).

## pair.muro

`let (x, y) = p in plus x y` opens an affine pair once. `addPair`, `swap` (run); `three-ok` and `swap-ok` are `refl`. `let` emits a pattern match.

See [Terms](language.md).

## result.muro

`Result E A` with constructors `ok` and `error`: a failing `run` function returns a sum, and the constructor names are the Elixir tags `{:ok, _}` / `{:error, _}`. `pred`, `orZero` (run); `pred-two` and `pred-zero` are `refl`.

See [Emit](emit.md).

## nx_add.muro

`I64` and `Tensor`. `doubled` is `[2, 4]` after `Nx.to_flat_list/1`. Nat stays Peano.

See [Machine numbers](machine.md).

## using_prelude.muro

Uses `sym`, `cong`, and `pred` from the prelude and defines none of them. `before` is `pred (suc (suc 0))`. There is no Agda twin: the prelude is an Elixir book, not a kernel rule. See [Terms](language.md#prelude).

## Refused

`mix muro.check` fails on each of these. `even_odd.muro` is the mutual recursion that checks.

### bad_dup.muro

Two data types are both named `Foo`. `foo` builds the first at `0` and `bar` builds the second at `suc(0)`. One name for both types lets a match skip the branch it should check.

### bad_wrap.muro

`bad` takes `Wrap → Empty`, and `wrap` stores a `Bad`. Each declaration is strictly positive on its own. Together the negative occurrence is `Bad` inside `Wrap`, placed in a domain.

### cycle_empty.muro

`impossible` calls `helper` and `helper` calls `impossible`. Both inhabit `Empty`. Neither calls itself. The failure is the cycle, not a missing name.

### bad_stuck.muro

`bad` takes a function of a `Nat`. The `0` branch is `Bad → Empty`, and `n` is bound, so the match does not reduce. The field is still not strictly positive.

### bad_positive.muro

`mk : (D → Nat) → D`. `D` occurs in the domain of a field. Strict positivity refuses it.

### bad_alias.muro

`BadAlias := D → Nat`, then `mk : BadAlias → D`. The checker unfolds the alias and refuses the same negative field. The name `BadAlias` is not what fails.

### bad_cons.muro

`cons` has two fields. A branch with one binder and a branch with three both fail, naming `cons` and the count `2`. `list.muro` and `vec.muro` are the matches that check.

### bad_shared.muro

`ping` descends on its first argument and `pong` on its second. No index works for both, so the block is refused. `even_odd.muro` is the mutual recursion that checks.

### bad_second_field.muro

`drop1 (cons y ys)` is `ys`. The false equation `{drop1 (cons y ys) ≡ zs}` is refused; `second_field.muro` is the true one. A match on a constructor with several fields puts every field in place at once.

## Adding a file

1. Put it in `examples/`. Use only `run` / `run internal` / `spec` / `evidence`.
2. Every binder is `(x : A)` or `(+ x : A)` or `(- x : A)`.
3. Every `match` / `rewrite` writes `motive (λ x → …)` in parentheses.
4. Recursion on `run`/`evidence` goes through `match` and a smaller variable.
5. `mix muro.check examples/your_file.muro`.
6. If it belongs in CI, add parse/check/emit in `test/muro_check_test.exs`.

Do not edit Agda or `lib/muro/*.ex` to make a program work. If the program is allowed by the grammar and the checker refuses a term that should check, that is a kernel bug — a different job. See [For agents](for-agents.md).

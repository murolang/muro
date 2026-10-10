---
title: Library
slug: library
order: 15
summary: The .muro files under stdlib/, imported by path: the order on Nat, and the CSHRL statements.
---

# Library

In brief: `stdlib/` holds `.muro` files a program imports by path. They are ordinary books, checked like any other file, with no special status in the checker. `nat.muro` is the order on `Nat` with the maximum and its lemmas. `cshrl.muro` states the two optimality conditions of Coinductive Symmetric Homomorphism RL for an environment given as arguments, and proves that they decompose. An environment under `examples/cshrl/` imports it and supplies the proof.

## Importing

The path is relative to the importing file ([Import](language.md#import)). From `examples/cshrl/`:

```
import "../../stdlib/cshrl.muro"
```

`cshrl.muro` imports `nat.muro` itself. A file that imports `cshrl.muro` sees both.

## nat.muro

`Le` is a `spec` function, not a data type:

```
def Le : spec Π (m : Nat) → Π (n : Nat) → Type :=
  λ (m : Nat) → λ (n : Nat) →
    match m motive (λ _ → Type)
      | 0 => Unit
      | suc m1 =>
          (match n motive (λ _ → Type)
            | 0 => Empty
            | suc n1 => Le m1 n1)
```

`Le 0 n` is `Unit`, `Le suc(m) 0` is `Empty`, and `Le suc(m) suc(n)` is `Le m n`. On closed numerals it computes, so `tt : Le (suc 0) (suc (suc 0))` and a proof of `Le (suc 0) 0` is a proof of `Empty`. A lemma about `Le` is a `match` on the numbers, with no index equation to carry.

| Name | Type |
| --- | --- |
| `le-refl` | `Π (n : Nat) → Le n n` |
| `le-zero` | `Π (n : Nat) → Le 0 n` |
| `le-trans` | `Le a b → Le b c → Le a c` |
| `maxN` | `run`. The maximum of two `Nat`. |
| `maxN-le` | `Le a c → Le b c → Le (maxN a b) c` |
| `le-maxN-left` | `Le a (maxN a b)` |
| `le-maxN-right` | `Le b (maxN a b)` |
| `maxN-mono` | `Le a c → Le b d → Le (maxN a b) (maxN c d)` |

The name is `maxN` and not `max`: Elixir emit names the function after the definition, and `max/2` is in `Kernel`.

## cshrl.muro

An environment is a type of states `S`, a type of actions `A`, `next : S → A → S`, and `reward : S → A → Nat`. `solve s n` is the best reward exactly `n` steps ahead, and the value stream of a state is `solve s` tabulated over the depth. Two streams compare at every depth, so a dominance between two value streams is a `Π` over the depth:

```
def Dominates : spec Π (f : Π (_ : Nat) → Nat) → Π (g : Π (_ : Nat) → Nat) → Type :=
  λ (f : Π (_ : Nat) → Nat) → λ (g : Π (_ : Nat) → Nat) →
    Π (n : Nat) → Le (f n) (g n)
```

A ranking is `rank : S → A → A → Type`; `rank s a b` says that at `s` the action `b` is at least as good as `a`. The statements take the environment as arguments. They are `spec`, so an argument may be mentioned as often as the statement needs.

| Name | Statement |
| --- | --- |
| `ActionValue S A reward next solve s a` | The action-value stream of `a` at `s`: `reward s a` at depth `0`, `solve (next s a) m` at depth `suc m`. |
| `CoinductiveHomomorphism S A next solve rank` | `rank s a b` gives `Dominates (solve (next s a)) (solve (next s b))`. The successor condition. |
| `CoindHomo S A reward next solve rank` | `rank s a b` gives the dominance of the action-value streams. The action-value condition. |
| `HeadCompatible S A reward rank` | `rank s a b` gives `Le (reward s a) (reward s b)`. |

Two `evidence` definitions are the decomposition:

| Name | Statement |
| --- | --- |
| `coindHomo-successor` | A `CoindHomo` is a `CoinductiveHomomorphism`: take the dominance at depth `suc n`. |
| `successor-head-coindHomo` | A `CoinductiveHomomorphism` that is `HeadCompatible` is a `CoindHomo`: depth `0` is the head, depth `suc n` is the successor. |

Their environment arguments are erased (`-`). At a call they are checked in spec, so an instance passes its `spec` definitions there.

## What an instance writes

The library does not hold `solve`. A `run` function that is used on every action needs `+` on its arguments, and `+` asks for a copyable type, which an abstract `S : Type` is not. So each environment writes its own `solve`, one `match` on the depth per action, and a `spec` definition that presents it without the marks:

```
def best : spec Π (s : State) → Π (n : Nat) → Nat := λ (s : State) → λ (n : Nat) → solve s n
```

`best` is what the statements take. A dominance about `best` is a dominance about `solve`, since `best` unfolds.

The ranking is a `spec` function from the states and two actions to `Unit` or `Empty`. The proof of a condition is a `match` on the state and the actions: a `Unit` branch supplies the dominance, an `Empty` branch is `matchEmpty`. A refutation of a condition applies it to the state, the actions, `tt`, and a depth at which `Le` computes to `Empty`.

Three environments are under `examples/cshrl/`:

- `two_state.muro`: the aligned case. The successor condition and the head condition both hold, and `successor-head-coindHomo` gives the `CoindHomo`.
- `binary_sacrifice.muro`: the sacrifice pattern. The successor condition holds; the head condition fails, so no `CoindHomo` ranks the actions in that order. The file also tabulates `value` as a `run` stream and emits.
- `skill_investment.muro`: a chain of sacrifices. Three dominances in one induction on the depth, through `maxN-mono`.

See [Examples](examples.md#cshrl).

Next: [For agents](for-agents.md).

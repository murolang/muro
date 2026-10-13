---
title: CSHRL
slug: cshrl
order: 15
summary: Coinductive symmetric homomorphisms for RL, as a library on params, with three environments and their agents.
---

# CSHRL

In brief: `examples/cshrl/` is [CSHRL](https://github.com/doctorcorral/csh-rl) in Muro. The artifact's parameterised modules are files whose environment is a list of `param` entries. Each environment supplies them by declaring the names, and proves its theorems in the same file. Its run definitions are an agent that plans with the Finder and acts in the environment, emitted as an Elixir `Stream`.

## Layout

| File | Artifact |
| --- | --- |
| `lib/core.muro` | `CSHRL.Core`: `solve`, `value`, `action-value`, `CoindHomo` |
| `lib/successor.muro` | `SuccessorCore`: `CoinductiveHomomorphism`, `HeadCompatible`, both directions |
| `lib/successor_sum.muro` | `SuccessorCoreWithArithmetic`: `partial-sum`, `SubsumesSuccessorReturn`, `SuccessorArgmaxSubsumed` |
| `lib/finder.muro` | `EnvironmentClass.FiniteDeterministicMDP`: `best-trace`, `find-ranking`, `find-policy`, `ranks`, `preserves-head`; the successor Finder |
| `lib/agent.muro` | The agent: `episode` and `successor-episode` |
| `envs/two_state.muro` | `TwoState`: `CoindHomo ranks` for the Finder's ranking, policy `go` |
| `envs/optimal.muro` | The return theorem: `agent` goes, and its reward stream dominates every other policy |
| `envs/binary_sacrifice.muro` | `BinarySacrifice` |
| `envs/skill_investment.muro` | `SkillInvestment` |
| `std/` | Bool, Nat order and `maxN`, List, Stream with `Dom` |

A library file does not check on its own: `mix muro.check examples/cshrl/lib/core.muro` refuses with `param State is supplied by a file that imports this one`. Check an environment instead:

```
mix muro.check examples/cshrl/envs/skill_investment.muro
```

## The environment as params

`core.muro` opens with the artifact's module parameters, in its order:

```
param State : spec Type
param Action : spec Type
param Reward : spec Type
param step : run Π (s : State) → Π (a : Action) → State × Reward
param le : spec Π (r : Reward) → Π (q : Reward) → Type
param max : run Π (r : Reward) → Π (q : Reward) → Reward
param bottom : run Reward
param all-actions : run List Action
```

The Finder adds `leb`, `default-action` and `horizon`. `successor_sum.muro` adds `add`, `le-refl` and `add-mono` as evidence, so `partial-sum` is a ghost: it appears in statements and is never emitted. An environment declares `data State`, `def step`, and the rest. Each declaration has the mode of its param (see [Params](language.md#params)).

## Correspondence

- `Dom R le x y` is `_≤ₛ_`, a declared ν family ([Streams](streams.md#declared-families)). A proof is an `unfold` of the head obligation and a proof at the tails.
- `CoindHomo rank` is the artifact's `preserves` field, for a given `rank`. The record bundles the ranking with that field. Here the ranking is the argument, so "the Finder's ranking is a CoindHomo" is `CoindHomo ranks`.
- `action-value s a` is the tabulation of `action-at s a`. The artifact defines its head and tail by copatterns. The tail here is `value (next s a)` up to `dom-shift`, which `coindHomo-successor` uses.
- `trace-action` is written with `fst` and `snd` of `step s a`, so that `ranks` reduces to a `cons` and `preserves-head` is `fst p`, as in the artifact.
- `best-trace` and `trace-action` are mutual. `best-trace` descends on `k`, and `trace-action` passes its `k` unchanged to `best-trace`, which is defined first ([Terms](language.md#recursion-and-descent)).

## The environments

**TwoState.** From `start`, `go` reaches `goal`, whose reward is 1. `direct-preserves : CoindHomo ranks` and `test-start : find-policy start horizon ≡ go`. Optimality of that policy is `envs/optimal.muro`, below.

**BinarySacrifice.** `go-trap` earns 1 now and 0 forever. `go-paradise` earns 0 now and 1 forever. `sacrifice-homomorphism` is a `CoinductiveHomomorphism` ranking `go-paradise` above `go-trap`. `coindHomo-forward-impossible` and `coindHomo-reverse-impossible` refute every `CoindHomo` that ranks them in either direction. `paradise-subsumes` is `SuccessorArgmaxSubsumed` at start: the successor return of `go-paradise` dominates at every horizon. `finder-takes-trap` and `successor-finder-takes-paradise` hold by `refl`.

**SkillInvestment.** `train` moves from novice to apprentice to expert to master and earns 0 each time. `work` earns 1, 2 or 3 and stays put. Master earns 5. `value novice` is 1, 2, 3, 5, 5, …. `skill-homomorphism` ranks `train` above `work` below master. Three impossibilities refute a `CoindHomo` ranking `work` at or below `train` at novice, apprentice and expert. The Finder works and the successor Finder trains.

## The agents

`episode-with policy s` unfolds from `s`: at each state it asks the policy for an action, emits the action and its reward, and continues from the state it reaches. `episode` plans with `find-policy x horizon` and `successor-episode` with `find-successor-policy x horizon`. From the starting states:

| Environment | `episode` | `successor-episode` |
| --- | --- | --- |
| BinarySacrifice | `go_trap` 1, then 0 forever | `go_paradise` 0, then 1 forever |
| SkillInvestment | `work` 1 forever | `train` 0 three times, then 5 forever |

In `trap` both actions return to `trap`. The Finder's sort is stable, so the tie goes to `go_paradise`, the first action in `all-actions`.

## The return theorem

`envs/optimal.muro` is one agent and one step. `agent` goes from either state. `returns policy s` is the stream of rewards from following `policy` at `s`.

```
def agent-optimal : evidence Π (+ policy : State → Action) → Π (+ s : State) →
    Dom Nat Le (returns policy s) (returns agent s)
```

`+` is there because the policy and the state are read now and again at the successors. The proof is `dominates`, an `unfold`. The head is the reward now: `go` earns 1, and every reward this step pays is 0 or 1. The tail is `dominates` at both successors, the state `policy` reached and the state `agent` reached.

`CoindHomo ranks` is a property of a ranking of actions. `find-policy start horizon ≡ go` is the Finder's choice at `start`. `agent-optimal` is the statement that this agent's return dominates every other policy.

In BinarySacrifice the stream of `go-trap` is 1, 0, 0, … and the stream of `go-paradise` is 0, 1, 1, …. Each is strictly ahead at a position where the other is behind, so `Dom` holds in neither direction. No policy's return dominates every other policy there.

## What is proved

`agent-optimal` and the ranking theorems above are what `mix muro.check` accepts. Every statement about streams goes through `Dom`, and ν is outside the fragment of the soundness theorem ([Limits](limits.md)). The checker's ν rules, including this `unfold`, and the descent of the mutual blocks in `finder.muro`, are argued, not proved in Agda. The library has none of the artifact's appendices or stochastic environment classes.

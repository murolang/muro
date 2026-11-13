---
title: Synthesis
slug: synth
order: 26
summary: mix muro.synth searches a version space of predicate programs on a checked environment.
---

# Synthesis

`mix muro.synth path.muro` searches a version space of predicate programs against one checked environment. The search calls that book's emitted `step`. A program that misses an observation is dropped. The smallest program that matches every observation is the policy the result book deploys, and `eval` runs it. A score breaks a tie between programs of equal size. It does not decide who survives. The checker sees that policy. When the environment defines the homomorphism the oracle asks for, the same book defines `rank` from the surviving predicate and the evidence for that ranking, and the checker sees the evidence on the same `step`. It does not see the search. Exit 0 is that checked book. A policy whose environment does not define the homomorphism is not exit 0.

```
mix muro.synth path.muro
mix muro.synth path.muro --oracle trace
mix muro.synth path.muro --oracle successor --depth 0
mix muro.synth path.muro --out out.muro --fuel 2000
muro synth path.muro
```

The predicate theory is [CSHRL](cshrl.md). `examples/cshrl/envs/synth_bit.muro` is the one-bit book: `eval` of `truep` is the deployed policy.

## The environment

The book must already check. It defines `State`, `Action`, `step`, `all-actions`, `horizon`, and `leb`. `step` is the dynamics the search, the sweep, and the policy check all call. `all-states`, when the book defines it, is the cover, in the order written, and a state named twice is that state once, at its first occurrence. Otherwise the cover is the nullary constructors of `State`, closed under `step`.

Features are ordinary definitions. There is no new keyword. The search builds tests from `step`, one per action: the reward is positive, the action returns to this state, and the successor is absorbing. A state is absorbing when every action stays there. A test that is true at every state on the cover, or false at every one, is dropped. A test with the same truth vector as an earlier test is dropped. `data Feature`, when the book declares it, names hints, and `eval-feature` reads one hint at a carrier. The two declarations come together or not at all. A book that defines neither is an environment. The version space is the two constants, the tests `step` supports, and the hints that remain. `Carrier` is that state type when the book defines it. A state name is not a feature by being a constructor of `State`. Depth does not add a template. When the survivor reads a discovered test, the policy book defines that test as a run over `step`. When it reads none, and the environment declared no `Feature`, the policy book declares one constructor that is always false, under a name the environment does not already use.

The tests are `has-pos-reward` and `is-self-loop` (`CSHRL.Synthesis.DynFeatureTemplate`) and `leads-terminal` (`CSHRL.Synthesis.AutoFeatureNat`). A one-hot state, a factorization of a state index, and a threshold on that index are not tests. A state that is an atomic constructor is not walked as a term. The paper's account is §Feature Discovery (`sec:ftl`). An empty version space is still searched one depth further, as in `CSHRL.Synthesis.CSHRLLoop`.

Two actions are one predicate: prefer the first action of `all-actions`, else the second. More than two actions are one predicate per action, chained in `all-actions` order, and the last else is `default-action`. An action named twice in `all-actions` is that action once, at its first occurrence. When `default-action` is omitted, the default is the last element of the list as written. The report follows that chain. The default is the preferred action only when every arm is false. A name that exists with the wrong mode, or the wrong type, is not an environment. `step` is `Π (s : State) → Π (a : Action) → State × Reward`, `all-actions` is `List Action`, `horizon` is `Nat`, and `leb` compares that reward. Those definitions, and `all-states`, `default-action`, and `eval-feature` when the book defines them, are public `run` terms. `run internal` is refused. An argument the search passes is not erased. A `Carrier` the book defines converts to `State`.

## Oracles

`--oracle` selects the labels. The default is `trace`.

`trace` compares Finder traces out to `horizon`. Prefer the first action when the second action's trace is below it, including when the two traces are equal. When the order compares neither of the first differing rewards with the other, the pair is not ranked. `trace` asks for `CoindHomo`.

`successor` compares successor values, pointwise, on a finite prefix, and asks for `CoinductiveHomomorphism`. It claims `CoindHomo` only when the immediate rewards respect the same ranking. `coind-homo` compares action values, pointwise, on the same kind of prefix, and asks for `CoindHomo`. A first reward that is smaller does not make the rest of the stream smaller. A pair the oracle cannot order stops the run, including a pair of actions that both lose to a third. A successor value or an action value is that same refusal when the rewards at a state have no maximum. The report names the carrier and the two actions. It does not invent a ranking.

## The loop

`--depth` is the initial depth. Depth 0 is the constants and the feature tests. A negation, a conjunction, or a disjunction needs a greater depth. An empty version space is searched one depth further.

The size of a program is the number of predicate constructors. A constant or a feature test is one. A negation is one plus its body. A conjunction or a disjunction is one plus both parts. The feature's name is not a constructor. The smallest survivor is the program the book names `survivor`. `policy` is `eval` of that program:

```
def survivor : run PredProg := truep
def policy : run Π (+ s : State) → Action :=
  λ (+ s : State) →
    (match eval survivor s motive (λ _ → Action) | true => go | false => stay)
```

The equations `hold-<state>` are the observations the survivor matched. They are evidence. The emitters erase them. The policy does not case-split on the state names. `rank` reads `eval` of the survivor. It is `Unit` when the two actions are the same or the predicate prefers the second, and `Empty` otherwise. The preference is `eval` of the survivor, the same predicate the book deploys. On a finite `State`, `solve s n` is the best immediate reward among the states reached in `n` steps. Each component is one of a finite set of closed Nat rewards, so the vector of those values repeats. The book characterises `solve` at each state as a constant, or as a finite prefix and then a constant or a repeating tail. The evidence inducts on `n`. The homomorphism of the ranking rewrites those equations: `CoindHomo` for `trace` and `coind-homo`, and `CoinductiveHomomorphism` for `successor`. The evidence is a case split over the states and the actions. It is erased. A state that pays nothing now is ranked when its stream is below the stream of a state it can reach. A `successor` ranking claims `CoindHomo` only when the immediate rewards respect the same order. A set of rewards with no maximum, or a reward that is not a closed Nat, leaves the policy book without a ranking.

`examples/cshrl/envs/two_state.muro` with `trace` checks `CoindHomo`. The survivor is `truep`, and at `start` it prefers `go`. Hiding `go` from the oracle does not check a `CoindHomo` for `go`. `examples/cshrl/envs/binary_sacrifice.muro` with `successor` checks `CoinductiveHomomorphism` for a survivor that prefers `go-paradise`, and the book does not claim `CoindHomo`. The same environment with `coind-homo` reports that the oracle cannot label the pair and writes nothing. `trace` on that environment separates `start` from the sinks and does not check `CoindHomo`: the homomorphism is not derivable at `start`. A book that contains only the policy is not exit 0. `examples/cshrl/envs/maze_auto.muro` declares no `Feature`. `trace` checks `CoindHomo` for `(feat has-pos-reward-go)`, which prefers `stay` at `west` and `go` at `east`. `examples/cshrl/envs/maze_auto_e2e.muro` is the three-cell maze and declares no `Feature`. `trace` checks `CoindHomo` for `truep`, which prefers `Fwd` at `P0`, `P1`, and `P2`. `solve P0 0` is `0` and `solve P0 (suc n)` is `suc 0`. `solve P1` and `solve P2` are `suc 0` at every `n`. `examples/cshrl/envs/lam.muro` is not a validated target. It declares no `Feature`. `trace` reports that `len` agrees with `copy` on every feature.

`PredProg` and `eval` are compiled into the checker. They use the environment's `Bool`, `true`, and `false`. The policy book does not import a second `Bool` or `leb`. An environment that already declares `PredProg`, `eval`, or the Boolean helpers, when those declarations have the types the policy uses, is left as written. A name the book already uses, including one that would spell the same Elixir function, is given a fresh name. A policy book can be read again as an environment.

The fuel bound and the round bound stop a search that is not shrinking. They are operational. They are not `sufficient-cegis`. A sweep of the cover is not that theorem.

A failed check that produced a bit drops the candidate the checker refused and checks the next survivor. A failed homomorphism is that same refusal: the report names the carrier, the bit the survivor predicted, the bit the oracle required, the action pair, and how many times that carrier was fed back. That candidate is not selected again. When the refusal removes every survivor and a greater depth is still allowed, the search continues there, with the same observations. A check that produced no bit does not drop a candidate and does not deepen. The bit is the one in that obligation's diagnostic. A later obligation does not supply it, and out of fuel stays unknown. After the round bound the report names the counterexample. It does not emit a ranking that failed to check.

When two carriers on the cover agree on every discovered test and every hint, and the oracle disagrees, no program in the version space can match both. The report names the two carriers. The depth is not raised in order to invent a template.

## Flags and exit codes

| Flag | Meaning |
| --- | --- |
| `--oracle NAME` | `trace` (the default), `successor`, or `coind-homo`. |
| `--depth N` | Initial predicate depth. Default 0. An empty space is searched one depth further. |
| `--out out.muro` | Write the policy book here. The path must not already exist. A path that is present when the book is written is the same refusal, and the file is not replaced. A write that fails removes the partial file. Without this flag the book is printed on standard output and nothing is written. That book's environment import is relative to the current directory. |
| `--fuel N` | Fuel for the environment and for the policy book. Default `Muro.Check.default_fuel/0` (2000). `out of fuel` is not acceptance. |
| `--json` | Print the report as one JSON object on standard error. The object records the version-space sizes and the counterexamples. It is not a certificate. |

| Exit | Meaning |
| --- | --- |
| 0 | The output book checks and contains the homomorphism for the synthesized ranking, on the `step` the search called. `trace` and `coind-homo` check `CoindHomo`. `successor` checks `CoinductiveHomomorphism`. |
| 1 | The report names an empty version space, a counterexample, a homomorphism that is not derivable, an oracle that cannot label a pair, features that cannot separate two carriers, or a policy whose environment does not define the homomorphism. A book that typechecks and does not contain that evidence is this exit. |
| 2 | The book does not check, it does not follow the environment convention, the oracle name is unknown, `--out` already exists, or a policy book or a temporary book cannot be written. The diagnostic is the one the write returned. |

---
title: Synthesis
slug: synth
order: 26
summary: mix muro.synth searches a version space of predicate programs on a checked environment.
---

# Synthesis

`mix muro.synth path.muro` searches a version space of predicate programs against one checked environment. The search calls that book's emitted `step`. A program that misses an observation is dropped. The smallest program that matches every observation is the policy the result book deploys, and `eval` runs it. A score breaks a tie between programs of equal size. It does not decide who survives. The checker sees that policy. It does not see the search. A homomorphism for the policy is later, so this command does not exit 0.

```
mix muro.synth path.muro
mix muro.synth path.muro --oracle trace
mix muro.synth path.muro --oracle successor --depth 0
mix muro.synth path.muro --out out.muro --fuel 2000
muro synth path.muro
```

The predicate theory is [CSHRL](cshrl.md). `examples/cshrl/envs/synth_bit.muro` is the one-bit book: `eval` of `truep` is the deployed policy.

## The environment

The book must already check. It defines `State`, `Action`, `step`, `all-actions`, `horizon`, and `leb`. `step` is the dynamics the search, the sweep, and the policy check all call. `all-states`, when the book defines it, is the cover, in the order written. Otherwise the cover is the nullary constructors of `State`, closed under `step`.

Features are ordinary definitions. There is no new keyword. `data Feature` names the tests, and `eval-feature` reads one test at a carrier. `Carrier` is that state type when the book defines it. A book that defines `Feature` and not `eval-feature` is refused. A book with no `Feature` has only the two constants in the version space. A state name is not a feature by being a constructor of `State`.

Two actions are one predicate: prefer the first action of `all-actions`, else the second. More than two actions are one predicate per action, chained in `all-actions` order, and the last else is `default-action`. The report follows that chain. The default is the preferred action only when every arm is false. A name that exists with the wrong mode, or the wrong type, is not an environment. `step` is `Π (s : State) → Π (a : Action) → State × Reward`, `all-actions` is `List Action`, `horizon` is `Nat`, and `leb` compares that reward.

## Oracles

`--oracle` selects the labels. The default is `trace`.

`trace` compares Finder traces out to `horizon`. Prefer the first action when the second action's trace is below it, including when the two traces are equal. When the order compares neither of the first differing rewards with the other, the pair is not ranked.

`successor` compares successor values, pointwise, on a finite prefix. `coind-homo` compares action values, pointwise, on the same kind of prefix. A first reward that is smaller does not make the rest of the stream smaller. A pair the oracle cannot order stops the run. The report names the carrier and the two actions. It does not invent a ranking.

## The loop

`--depth` is the initial depth. Depth 0 is the constants and the feature tests. A negation, a conjunction, or a disjunction needs a greater depth. An empty version space is searched one depth further.

The size of a program is the number of predicate constructors. A constant or a feature test is one. A negation is one plus its body. A conjunction or a disjunction is one plus both parts. The feature's name is not a constructor. The smallest survivor is the program the book names `survivor`. `policy` is `eval` of that program:

```
def survivor : run PredProg := truep
def policy : run Π (+ s : State) → Action :=
  λ (+ s : State) →
    (match eval survivor s motive (λ _ → Action) | true => go | false => stay)
```

The equations `hold-<state>` are the observations the survivor matched. They are evidence. The emitters erase them. The book does not case-split on the state names. `PredProg` and `eval` are compiled into the checker. They use the environment's `Bool`, `true`, and `false`. The policy book does not import a second `Bool` or `leb`.

The fuel bound and the round bound stop a search that is not shrinking. They are operational. They are not `sufficient-cegis`. A sweep of the cover is not that theorem.

A failed check that produced a bit drops the candidate the checker refused and checks the next survivor. A check that produced no bit does not. After the round bound the report names the counterexample: the carrier, the bit the check produced or unknown, the bit the oracle required, and how many times that carrier was fed back.

When two carriers on the cover agree on every feature and the oracle disagrees, no program in the version space can match both. The report names the two carriers. The depth is not raised in order to invent a feature.

## Flags and exit codes

| Flag | Meaning |
| --- | --- |
| `--oracle NAME` | `trace` (the default), `successor`, or `coind-homo`. |
| `--depth N` | Initial predicate depth. Default 0. An empty space is searched one depth further. |
| `--out out.muro` | Write the policy book here. The path must not already exist. Without this flag the book is printed on standard output and nothing is written. |
| `--fuel N` | Fuel for the environment and for the policy book. Default `Muro.Check.default_fuel/0` (2000). `out of fuel` is not acceptance. |
| `--json` | Print the report as one JSON object on standard error. The object records the version-space sizes and the counterexamples. It is not a certificate. |

| Exit | Meaning |
| --- | --- |
| 0 | Not used. A checked homomorphism for the synthesized policy is later. |
| 1 | The report names a policy whose homomorphism is later, an empty version space, a counterexample that survived the round bound, an oracle that cannot label a pair, or features that cannot separate two carriers. |
| 2 | The book does not check, it does not follow the environment convention, the oracle name is unknown, or `--out` already exists. |

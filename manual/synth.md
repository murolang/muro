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

The book must already check. It defines `State`, `Action`, `step`, `all-actions`, `horizon`, and `leb`. `step` is the dynamics the search, the sweep, and the policy check all call. `all-states`, when the book defines it, is the cover, in the order written, and a state named twice is that state once, at its first occurrence. Otherwise the cover is the nullary constructors of `State`, closed under `step`. A `State` whose constructors take arguments is a term. When the book does not define `all-states` and that type has at most 32 inhabitants, the cover is the enumeration. More than 32 inhabitants is not that list. The book then declares `all-states`, or the environment is refused: `State has more than 32 inhabitants; declare all-states`. A constructor argument with no finite enumeration and no `all-states` is refused: `State constructors take arguments; declare all-states`. An inductive `State` may refer to itself. A finite non-empty `all-states` is then the cover, and two values are compared by matching constructors and recursing on a field of that same datatype. A family of datatypes that refer to one another is refused: `State is mutually inductive`. Wrapper recursion is that same refusal: a `Box` that holds a `State`, and a `State` that holds a `Box`, is mutually inductive, even when only one constructor of `State` mentions `Box`.

```
data Box : Type where
  box : Π (s : State) → Box

data State : Type where
  wrap : Π (b : Box) → State
```

A recursive occurrence under `List` or a product is part of the value and is not that comparison. The certificate is refused: `State recursion under List/product cannot be certified`. A field of type `List State` is also not strictly positive, and the book is refused before the environment is opened. `State has parameters` and `State has indices` are refused from the declaration. A function field is refused: `State has a function field`. An erased constructor argument is refused: `State has an erased constructor argument`. A linear field opens, and the certificate is refused: `State has a linear field`. The certificate splits on every inhabitant of a finite `State`. When `State` is not that enumeration and the book defines a finite non-empty `all-states`, the same certificate ranges over the cover, provided `step` of every action in `all-actions` stays inside it and the terms can be split. The split follows the constructors, fields, lists, and Nats of those terms, and a field whose type is the datatype being split is that datatype again. A product that does not recurse to `State` is opened with `let`. A state outside the cover has an empty ranking, so the homomorphism does not order it. A cover that `step` leaves, and an empty `all-states`, leave the policy book without a ranking.

Features are ordinary definitions. There is no new keyword. The search builds tests from `step`, one per action: the reward is positive, the action returns to this state, and the successor is absorbing. A state is absorbing when every action stays there. A test that is true at every state on the cover, or false at every one, is dropped. A test with the same truth vector as an earlier test is dropped. `data Feature`, when the book declares it, names hints, and `eval-feature` reads one hint at a carrier. The two declarations come together or not at all. A book that defines neither is an environment. The version space is the two constants, the tests `step` supports, and the hints that remain. `Carrier` is that state type when the book defines it. A state name is not a feature by being a constructor of `State`. Depth does not add a template. When the survivor reads a discovered test, the policy book defines that test as a run over `step`. On a finite list of inhabitants the comparison is an exhaustive match. Otherwise it walks constructors, fields, lists, and Nats, and a field of the datatype being compared is a recursive call of that walk. `is-self-loop` and `leads-terminal` are omitted when that comparison is not a run. When the survivor reads no discovered test, and the environment declared no `Feature`, the policy book declares one constructor that is always false, under a name the environment does not already use.

The tests from `step` are `has-pos-reward` and `is-self-loop` (`CSHRL.Synthesis.DynFeatureTemplate`) and `leads-terminal` (`CSHRL.Synthesis.AutoFeatureNat`). When `State` has a field, the same pipeline reads the term: which constructor built it, whether two fields are equal, whether a field is a closed Nat, and, on a list or on the fields of one constructor, `vals-eq`, `spread-eq`, `pair-any`, and `len-is` (`CSHRL.Synthesis.FeatureTemplate`). A `pair-any` on one pair of positions drops the `vals-eq` and the `spread-eq` of that pair. The first pass reads the value and one projection. Resolving a field that refers to the datatype already opened does not count as a further projection. An atomic constructor is not walked, so those tests are not added there. A bare Nat is not a threshold on a state index. `state-is`, a factorization, and a one-hot state are not tests. The paper's account is §Feature Discovery (`sec:ftl`). An empty version space is still searched one depth further, as in `CSHRL.Synthesis.CSHRLLoop`. A missing test of a subterm is not that deepening: when two carriers agree on every test and the two values differ, the search adds tests at the subterm where they differ and searches again.

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

The equations `hold-<state>` are the observations the survivor matched. They are evidence. The emitters erase them. The policy does not case-split on the state names. `rank` reads `eval` of the survivor. It is `Unit` when the two actions are the same or the predicate prefers the second, and `Empty` otherwise. The preference is `eval` of the survivor, the same predicate the book deploys. On a finite `State`, `solve s n` is the best immediate reward among the states reached in `n` steps. Each component is one of a finite set of closed Nat rewards, so the vector of those values repeats. The book characterises `solve` at each state as a constant, or as a finite prefix and then a constant or a repeating tail. The evidence inducts on `n`. The homomorphism of the ranking rewrites those equations: `CoindHomo` for `trace` and `coind-homo`, and `CoinductiveHomomorphism` for `successor`. The evidence is a case split over the states and the actions. It is erased. On a finite enumeration the split has one arm per inhabitant. On a declared cover the arms are the terms of the cover, and a state outside it is an empty ranking. A state that pays nothing now is ranked when its stream is below the stream of a state it can reach. A `successor` ranking claims `CoindHomo` only when the immediate rewards respect the same order. A set of rewards with no maximum, or a reward that is not a closed Nat, leaves the policy book without a ranking.

`examples/cshrl/envs/two_state.muro` with `trace` checks `CoindHomo`. The survivor is `truep`, and at `start` it prefers `go`. Hiding `go` from the oracle does not check a `CoindHomo` for `go`. `examples/cshrl/envs/binary_sacrifice.muro` with `successor` checks `CoinductiveHomomorphism` for a survivor that prefers `go-paradise`, and the book does not claim `CoindHomo`. The same environment with `coind-homo` reports that the oracle cannot label the pair and writes nothing. `trace` on that environment separates `start` from the sinks and does not check `CoindHomo`: the homomorphism is not derivable at `start`. A book that contains only the policy is not exit 0. `examples/cshrl/envs/maze_auto.muro` declares no `Feature`. `trace` checks `CoindHomo` for `(feat has-pos-reward-go)`, which prefers `stay` at `west` and `go` at `east`. `examples/cshrl/envs/maze_auto_e2e.muro` is the three-cell maze and declares no `Feature`. `trace` checks `CoindHomo` for `truep`, which prefers `Fwd` at `P0`, `P1`, and `P2`. `solve P0 0` is `0` and `solve P0 (suc n)` is `suc 0`. `solve P1` and `solve P2` are `suc 0` at every `n`. `examples/cshrl/envs/placement.muro` declares no `Feature`. The state is two rows. `trace` checks `CoindHomo` for `(feat pair-any-0-1)`, which prefers `move` when the rows are equal or adjacent and `stay` when they are two apart. The tests from `step` do not separate those boards. `examples/cshrl/envs/nested_bit.muro` declares no `Feature`. The bit sits under two constructors. The first pass does not separate the two states. A test of that bit does, and `trace` checks `CoindHomo` for `(feat ctor-is-p0-0-on)`, which prefers `move` at `on` and `stay` at `off`. `examples/cshrl/envs/list_cover.muro` declares no `Feature`. The state is a list of Nat. The cover is the empty list and the singleton `0`. `trace` checks `CoindHomo` for `(feat has-pos-reward-go)`, which prefers `stay` at the empty list and `go` at the singleton. `examples/cshrl/envs/tree_cover.muro` declares no `Feature`. The state is a binary tree of Nat. The cover is `tip 0` and `bin (tip 0) (tip 0)`. `trace` checks `CoindHomo` for `(feat has-pos-reward-go)`, which prefers `stay` at the tip and `go` at the bin.

`PredProg` and `eval` are compiled into the checker. They use the environment's `Bool`, `true`, and `false`. The policy book does not import a second `Bool` or `leb`. An environment that already declares `PredProg`, `eval`, or the Boolean helpers, when those declarations have the types the policy uses, is left as written. A name the book already uses, including one that would spell the same Elixir function, is given a fresh name. A policy book can be read again as an environment.

The fuel bound and the round bound stop a search that is not shrinking. They are operational. They are not `sufficient-cegis`. A sweep of the cover is not that theorem.

A failed check that produced a bit drops the candidate the checker refused and checks the next survivor. A failed homomorphism is that same refusal: the report names the carrier, the bit the survivor predicted, the bit the oracle required, the action pair, and how many times that carrier was fed back. That candidate is not selected again. When the refusal removes every survivor and a greater depth is still allowed, the search continues there, with the same observations. A policy book that does not check, and a check that names no obligation, drop that candidate and the search tries the next one. A check that names an obligation and produced no bit does not drop a candidate and does not deepen. The bit is the one in that obligation's diagnostic. A later obligation does not supply it, and out of fuel stays unknown. After the round bound the report names the counterexample. It does not emit a ranking that failed to check.

When two carriers on the cover agree on every discovered test and every hint, and the oracle disagrees, no program in the version space can match both. If the two values differ as terms, the search adds tests at the subterm where they differ, filters again, and searches again. Each such round separates that pair, and the number of rounds is at most the size of the cover. If the new tests still do not separate the pair, the report names the two carriers. The depth is not raised in order to invent a template.

## Paths into a term

This is the plan for a later search. This version compares a recursive term and ranks a declared cover. It does not enumerate the paths below, and it does not emit a test of a binder's quantity or of how often a variable is used.

A path starts at the root. The next step is a field of the constructor that built the value. A nested field is the same walk one step further. The bound is the number of fields opened. Resolving a name that the path has already opened does not spend a step and does not continue forever. The first pass opens one field. A later pass may open more, up to a fixed depth, and then stop.

At each path the tests generalise the structural templates the paper states for `List ℕ`. The constructor tag is `ctor-is`. On a list, `vals-eq`, `spread-eq`, `pair-any`, and `len-is` stay the tests of positions and length. On a binder, the later tests are the quantity of that field and the number of times the variable is used. A relevant field already records that quantity and that binder name. A test that is true at every state on the cover, or false at every one, is dropped. A test with the same truth vector as an earlier test is dropped. The tests are read from the schema of the environment that is open. A test does not name a fixture, a state, or one book.

When the book declares a finite non-empty `all-states` and `step` of every action in `all-actions` stays inside it, the certificate ranks that cover. A state outside the cover has an empty ranking. That is the ranking already checked for an open structured state such as a list of Nat (#231). A recursive term with such a cover uses that same certificate. What remains, when the book declares no cover, is a ranking read from the structure of the term. This version does not search that ranking. A recursive `State` with no `all-states` is still refused.

The paper's structural templates are specified for `List ℕ`. Accepting an inductive term as `State`, and comparing two values by recursion on a direct field, extends that account. A mutual family is refused, because a field is smaller only when its type is the datatype being matched. Wrapper recursion through another datatype is that refusal. A recursive occurrence under `List` or a product is stored and decoded, and it is not compared. The certificate is refused: `State recursion under List/product cannot be certified`. A `let` on the pair parses, and `rank` of the bound pair does not convert in the evidence. A field of type `List State` is not strictly positive. The comparison is not indexed by a fuel bound. Parameters, indices, a function field, and an erased constructor argument are refused when the environment is opened. A linear field is refused for the certificate and for the equality run. Two values also have no equality run when a field recurses under `List` or a product, or is linear or erased. A product that does not recurse is compared with `let`. The inhabitants of a recursive type are not listed. An erased constructor argument is omitted from the value, and that datatype is not given an equality run. The quantity of a relevant field is kept for the later tests. This version does not emit one.

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

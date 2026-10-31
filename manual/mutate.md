---
title: Mutation
slug: mutate
order: 23
summary: mix muro.mutate reports which evidence fails when a run definition changes.
---

# Mutation

`mix muro.mutate path.muro` changes each `run` definition in small, type-preserving ways and checks the book again. A killed mutant names the evidence that now fails. A survivor is a change every re-checked theorem still accepts. The page for the command is this one.

```
mix muro.mutate path.muro
mix muro.mutate path.muro --only half
mix muro.mutate path.muro --only half --only plus --json
mix muro.mutate path.muro --max-survivors 0
mix muro.mutate path.muro --fuel 2000 --max-mutants-per-def 100
```

The path is required. The book is the one `Muro.Load.file/2` checks, with the visible prelude behind it. Evidence, spec, data, and session entries are left as written. Prelude definitions are left as written. `run` and `run internal` in the file are the definitions that are mutated.

## Outcomes

Each mutant is classified with `Muro.Check`, the same checker `mix muro.check` runs.

| Outcome | Meaning |
| --- | --- |
| `killed` | A re-checked definition fails, and the failure is a real error. `killed_by` names each one, in book order, with its location. |
| `equivalent` | The mutant body and the original body convert, as closed terms, within the fuel. |
| `surviving` | The mutant type-checks, conversion with the original fails within the fuel, and every re-checked definition checks. |
| `out_of_fuel` | The checker gave up reducing. The summary counts this on its own. |
| `discarded` | The mutant is rejected. The text report splits `type` and `termination`. JSON records `discarded`. |

A type discard is a mutant `check_def` rejects for a reason other than fuel and other than the termination and structural messages below. An ill-scoped arm, an unknown name, and an affine variable used twice are type discards. A termination discard is one of: `recursive call does not descend on a smaller argument`, `unguarded recursive call`, `recursive definition must be applied to its arguments`, `unfold body must be a pair`, `ν value calls its own block outside an unfold`, `not strictly positive`, `ν body is not a product`, `bare ν is not a stream`.

Fuel exhaustion while checking the mutant itself, or while re-checking a depending definition and no depending definition has failed for another reason, is `out_of_fuel`. A real failure on any depending definition is a kill, including when another definition in the same mutant ran out of fuel.

## Equivalence by conversion

Before the book is re-checked, the two closed bodies are compared with `Muro.Check.conv/4` against the original book, so a recursive name still unfolds to the original. `:ok` is `equivalent`, and the depending definitions are not re-checked.

When that comparison runs out of fuel, the mutant stays eligible to be killed or to survive. The fallback below stays unused. When conversion fails for another reason, branches are paired by constructor name and arity, and conversion is asked again on the paired bodies, including under lambdas and applications. A body-only arm swap keeps each constructor in its original position, so the first comparison decides two arms that compute the same value (`plus 0 0` and `0`).

## What is re-checked

A mutant of `f` is checked together with every definition that mentions `f`, then every definition that mentions one of those, in book order. `f` itself is checked as the mutant. A theorem that does not mention `f`, directly or through another definition, is left unchecked.

The text report prints one line per mutated definition:

```
half: re-checked 1 of 5 evidence definitions
```

`N` is the evidence definitions in that dependency set. `M` is every evidence definition in the checked book, including the visible prelude. An equivalent mutant skips the re-check work. The line still reports the dependency count. Data and run definitions in the set are re-checked too, and they can kill the mutant. They are absent from `N` and `M`.

## Operators

Candidates are enumerated in a fixed order: file order of `run` definitions, then a pre-order walk of the body, then the operators at that node in the order below. The id is `<name>#<n>`, starting at 1 for each definition, and a discarded mutant keeps its number. The same file produces the same text and the same JSON. Mutants are classified concurrently. The order of the report is the enumeration order.

A candidate whose body is the original body is skipped. `--max-mutants-per-def` stops the enumeration at `N` candidates (default 100, and `0` is allowed). The default is `Muro.Mutate.default_max_mutants/0`.

1. `swap_arms`. Swap the bodies of two `match` arms when the motive, instantiated at each constructor, converts. Constructor names and binders stay in declaration order. Fuel on that comparison skips the pair.
2. `replace_ctor`. In result position, replace a constructor with another constructor of the same type. `0` and `suc` replace each other. A data constructor is replaced by the other constructors of its type, in declaration order. Each field is filled from in-scope variables of that field's type, outermost first, then from nullary inhabitants (`0`, `tt`, a nullary constructor). A filling equal to the original term is skipped.
3. `replace_var`. Replace a variable in a computational position (a scrutinee, an argument, a body) with another in-scope variable of the same type, outermost first, then a nullary inhabitant. Motives and binder domains are left unchanged.
4. `replace_call`. At a maximal call of a `run` definition, replace the head with another `run` definition of the same type declared earlier. Visible prelude `run` definitions count as earlier than every definition in the file, then earlier file definitions in file order. The arguments stay. Fuel on the type comparison skips the candidate.
5. `replace_rec_arm`. The first arm whose body does not mention the definition, or another definition in its mutual block, is the base. Each arm that does mention the block takes that base body.
6. `swap_args`. At a maximal call, swap two arguments when the arguments differ, their domains convert, and neither domain mentions an earlier argument.

A mutant that does not type-check as the original did is discarded and counted on that operator.

## Flags and exit codes

| Flag | Meaning |
| --- | --- |
| `--only name` | Mutate this `run` definition. Repeat the flag for more than one. The report stays in file order. |
| `--max-mutants-per-def N` | Stop after `N` candidates of each definition. Default 100. `0` prints the header and no mutants. |
| `--max-survivors N` | After the report, exit 1 when more than `N` mutants survive. Omitted, survivors do not change the exit code. |
| `--fuel N` | The checker's fuel for the original check and for every mutant. Default `Muro.Check.default_fuel/0` (2000). |
| `--json` | Print the JSON object below. The text header is omitted. |

Exit `0` means the book checked and survivors are within the limit. Exit `1` means survivors exceed `--max-survivors`. The report is printed first, and the error line is `N survivors exceed --max-survivors M`. Exit `2` means the original book does not check. The version line and the checker errors are printed, then `refusing to mutate a book that does not check`. `--json` does not change that refusal. An unknown flag, a missing path, a non-positive `--fuel`, a negative cap, or an `--only` name that is not a `run` definition in the file raises, which is exit 1 from Mix.

## JSON

`--json` prints one object. Keys stay in this order. `discarded` mutants stay in `mutants`, with `killed_by` an empty array.

```json
{
  "book": "examples/half_ok.muro",
  "version": "0.20.1",
  "summary": {
    "killed": 5,
    "surviving": 1,
    "equivalent": 0,
    "out_of_fuel": 0,
    "discarded": 11
  },
  "mutants": [
    {
      "id": "half#12",
      "def": "half",
      "operator": "replace_ctor",
      "location": "examples/half_ok.muro:25:18",
      "before": "0",
      "after": "suc(0)",
      "outcome": "surviving",
      "killed_by": []
    }
  ]
}
```

A kill fills `killed_by` with `{"name": "half_ok", "location": "examples/half_ok.muro:37:1"}` objects. `location` on a kill is the definition's location.

`book` is the path given on the command line. `version` is the application spec. `location` is `file:line:col` relative to the current directory. `before` and `after` are one line each, printed by `Muro.Print` on the de Bruijn term. The dependency counts are in the text report. They are absent from the JSON object. The printer emits the object on one line, with no space after `:` or `,`.

The text report starts with `Muro v` and the version, the book path, one re-check line per mutated definition, the five summary counts, a discard line for each operator, then one block per mutant: the id, the operator, the location, the outcome, a `by <name> at <location>` line for each kill, and the before and after lines.

---
title: Host representations
slug: repr
order: 15
summary: A repr states the host shape of a data type. Emit writes strict decode and encode.
---

# Host representations

In brief: a `repr` states how a data type looks in the host. `mix muro.emit` writes `decode_<type>/1` and `encode_<type>/1` next to the run functions. Decode is total and strict. An ambiguous repr is refused at `mix muro.check`, and the error names the two constructors.

A host calls decode, then the proved function, then encode. The translation is the statement in the book, not a function written beside it.

`repr` is host-side. It is not a kernel term, it has no Agda rule, and it never enters a run image. `Muro.Repr` checks it and emits it. The C, Rust, asm, OTP, and `--node` backends ignore it.

The book is `examples/repr.muro`.

## Syntax

`repr` is a keyword only in `repr Name :=`. A constructor `repr : Box` and `def repr : run Nat := 0` stay names. The words `boolean`, `integer`, `nil`, `list`, `optional`, `nullable`, `tuple`, `map`, and `open` are keywords only inside a repr body. A type with one of those names cannot be named in a shape.

```
repr       ::= "repr" ident ":=" (shape | variant ("|" variant)*)
variant    ::= ident "=>" shape
shape      ::= "boolean" | "integer" | "nil" | atom-lit | string-lit
             | ident
             | "list" shape | "optional" shape | "nullable" shape
             | "tuple" "{" [shape ("," shape)*] "}"
             | "map" ["open"] "{" [entry ("," entry)*] "}"
entry      ::= (string-lit | atom-lit) "=>" shape
```

`nil =>` at the start of a variant names the constructor `nil`. Anywhere else `nil` is the host nil. A string is the import string: no escapes, no newline, no `"` inside. An atom literal is `:name`.

```
repr Bool  := boolean
repr Entry := map { "id" => integer, "enabled" => optional Bool }
repr Shape := circle => map { "kind" => "circle", "r" => integer }
            | square => map { "kind" => "square", "side" => integer }
            | empty  => nil
```

The subject is a declared `data` type with no parameters and no indices, or `Nat`. One repr per type. A second one is `duplicate repr`, and the error names both lines.

## Vocabulary

| Shape | Host value | Muro value |
| --- | --- | --- |
| `boolean` | `true` / `false` | `:true` / `:false` |
| `integer` | a non-negative integer | Peano `Nat` (`0`, `{:suc, n}`) |
| `nil` | `nil` | the constructor the shape is bound to |
| `:circle` | the atom `:circle` | that constructor, or a fixed tag |
| `"circle"` | the string `"circle"` | that constructor, or a fixed tag |
| `Entry` | that type's host shape | that type's Muro value |
| `list S` | a proper list | the list-like type's own constructors |
| `nullable S` | `nil` or `S` | the maybe-like type's nullary constructor, or its one field |
| `optional S` | a missing map key, or `S` | the same, and only as a map entry |
| `tuple {…}` | a tuple of that arity | one constructor's fields |
| `map {…}` | a map with those keys | one constructor's fields |

`boolean` is valid only for a type with exactly two constructors, both nullary, named `true` and `false`. Any other pair is a choice: `on => :true | off => :false`. The refusal says so.

`integer` is valid for `Nat`: a field of type `Nat`, or `repr Nat := integer`. A bare name `Nat` in a shape means `integer`.

A bare name other than `Nat` is a type that has its own repr. A reference to a type with no repr is refused, and the error names the type. A type may refer to itself, and two types may refer to each other. Decoding terminates because the input is finite, but only after a shape has matched a host class. `repr Loop := Loop` is refused: a cycle of bare names would decode the same term forever. The message says the repr must match nil, a boolean, an integer, a literal, a list, a tuple, or a map before it refers to itself.

`list S` is valid for a field whose type is list-like, by shape rather than by name: one parameter, exactly two constructors, one nullary, one with two fields, the first of the parameter's type and the second the type applied to that parameter. The emitted code uses that type's constructor names. `S` is the element. An improper list is `{:not_list, v}`.

`optional S` and `nullable S` are valid for a field whose type is maybe-like: one parameter, exactly two constructors, one nullary, one with a single field of the parameter's type. The emitted code uses that type's constructor names. `optional` anywhere but a map entry is refused, and the message says to use `nullable`.

## Fields

A `tuple` or a `map` is the whole body of a single-constructor repr, or the shape after `ctor =>`. A constant component (`nil`, an atom literal, a string literal) is a tag: decode checks it, encode emits it, and it consumes no field. Every other component binds the constructor's fields in declaration order. The number of binding components must equal the field count. The error names the constructor and both counts.

A component must suit the field. `integer` suits `Nat`. `boolean` suits the `true` / `false` type. A type name suits a field of that type. `list`, `optional`, and `nullable` suit a list-like or maybe-like field. A mismatch names the constructor, the field index, and the type.

Do not nest a `tuple`, a `map`, or a choice inside a component. Name another type and give that type a repr.

A single-constructor type with a bare shape (not a tuple, a map, or a choice) is a newtype: exactly one field, unwrapped. In a choice, a constructor with exactly one field may also be unwrapped (`just => integer`). A `tuple` or `map` after `ctor =>` always wraps every field. A nullary constructor's shape is a constant.

A choice names every constructor of the type exactly once. A missing, unknown, or repeated constructor is refused, and the error names it.

Map keys are the string or atom literals as written. A repeated key is refused. Without `open`, a key the repr does not list is `{:unexpected_key, key}`. With `open`, extra keys are ignored. They are not kept, so `decode(encode(v))` is still `{:ok, v}`.

## Strictness

`decode_<type>/1` returns `{:ok, value}` or `{:error, {path, reason}}`. It does not raise. Anything the repr does not describe is an error, never a default. `path` is a list of the keys as written and the zero-based list or tuple indices, from the root. `[]` is the root.

The first error in a fixed order is the one returned: map keys in the order the repr lists them, then unexpected keys in Erlang term order, then list elements in order.

| Reason | When |
| --- | --- |
| `{:not_boolean, v}` | `boolean`, and `v` is not `true` or `false` |
| `{:not_integer, v}` | `integer`, and `v` is not an integer |
| `{:negative_integer, v}` | a negative integer for a `Nat` |
| `{:nat_too_large, v}` | an integer above the Nat guard |
| `{:not_map, v}` | a map shape, and `v` is not a map |
| `{:not_list, v}` | a list shape, and `v` is not a proper list |
| `{:not_tuple, v}` | a tuple shape, and `v` is not a tuple |
| `{:wrong_tuple_size, expected, v}` | a tuple of the wrong arity |
| `{:missing_key, key}` | a required key is absent; the path is the map's path |
| `{:unexpected_key, key}` | a key the repr does not list, and the map is not `open` |
| `{:nil_not_allowed, nil}` | `nil` where the shape is not nullable |
| `{:expected, literal, v}` | a constant tag did not match |
| `{:no_variant, names, v}` | no constructor of the choice matched |

A choice tries constructors in declaration order. A constructor whose host class and constant tags match is committed to. An error inside its fields is that error, with its own path, not `no_variant`. If none matches, the reason is `{:no_variant, names, v}`.

`encode_<type>/1` takes a value of the type and returns the host value. It is for a value the book already proved. A term that is not a value of the type raises `FunctionClauseError`. Decode is the guard at the boundary.

## Missing keys, nil, extra keys

| Written | Missing key | Key set to `nil` | Extra key |
| --- | --- | --- | --- |
| `S` | `{:missing_key, key}` | `{:nil_not_allowed, nil}`, unless `S` itself accepts nil | `{:unexpected_key, key}` |
| `optional S` | the nullary constructor | `{:nil_not_allowed, nil}`, unless `S` is `nullable` | `{:unexpected_key, key}` |
| `optional nullable S` | the nullary constructor | the nullary constructor; encode omits the key | `{:unexpected_key, key}` |
| `nullable S` | not a map entry by itself | the nullary constructor | — |
| `map open {…}` | as the entry says | as the entry says | ignored, not kept |

`1` is not `true`. A missing key is not `false`. Both are errors unless the repr says otherwise.

## Ambiguity

`mix muro.check` refuses a repr where two constructors can share a host value. The error names both constructors and the type:

```
3:1: repr Shape: constructors circle and square share a host shape (map with "kind" => "circle")
```

The check is conservative. A type name is replaced by the classes of that type's repr. `nullable S` adds nil. An unknown or recursive case overlaps, so it is refused.

Two shapes are disjoint when their classes differ, or both are constants of one class with different values. Two tuples are disjoint when their arities differ or some position is disjoint. Two maps are disjoint when some key is required in both and those value shapes are disjoint, as with `"kind" => "circle"` and `"kind" => "square"`. Two open maps overlap, even when a required key holds different constants. Close the map when that key is the tag. Two integers, two lists, or two nils overlap.

The same check applies inside a shape that has to pick, such as `nullable` of a type whose shape accepts nil.

## Nat

`Nat` is Peano in the emitted module: `0` and `{:suc, n}`. Decode of an integer builds that term with a tail call, one constructor per unit. Encode counts the chain with an accumulator. Both are linear in the value.

An integer above the guard is `{:nat_too_large, v}`. The guard is the module attribute `@muro_repr_nat_max`, set to `1_000_000` in the generated code, so the limit is visible and the same on every run. A negative integer is `{:negative_integer, v}`. A float, a string, or `nil` is `{:not_integer, v}`.

There is no binary `Nat` to target. A binary successor beside inductive `Nat` is issue #80, and it is open. This version does not add one. Until that exists, keep host integers inside the guard, or keep the proved function on small `Nat`s.

## In a host

`<type>` is the type name in snake case. `Entry` is `entry`. `HttpRequest` is `http_request`. `-` and `'` become `_`. The functions are public. A name that collides with a run, with another type's snake case, or with a codec helper is refused, and the error names both.

Reprs from imported books are emitted in book order, the same way runs from imports are. A book with no repr emits the same module text as before.

`mix muro.emit path.muro` prints the module. `mix muro.gen` writes it at the path the manifest names, and the codec is part of that file. `mix muro.gen --check` fails when the repr changes, because the book hash changed, and it fails when the codec is edited by hand. See [Committed modules](gen.md).

```
mix muro.check examples/repr.muro
mix muro.emit examples/repr.muro
```

## End to end

`examples/repr.muro` defines `Entry`, `toggle : run Entry → Entry`, and `describe : run Entry → Outcome`.

```elixir
{:ok, v} = Host.Repr.decode_entry(%{"id" => 3, "enabled" => true})
Host.Repr.encode_entry(Host.Repr.toggle(v))
# %{"id" => 3, "enabled" => false}

Host.Repr.encode_outcome(Host.Repr.describe(v))
# %{"status" => "on", "id" => 3}

{:ok, missing} = Host.Repr.decode_entry(%{"id" => 3})
Host.Repr.encode_outcome(Host.Repr.describe(missing))
# nil

Host.Repr.decode_entry(%{"id" => 3, "enabled" => 1})
# {:error, {["enabled"], {:not_boolean, 1}}}
```

The host terms on both ends are maps, booleans, and integers. Nothing in the call builds `{:suc, _}` or `{:just, _}`.

## Not in this version

- Free-form strings and interned names. String and atom literals are fixed tags. A field the book cannot enumerate is refused: model the closed set as a type and give it a repr.
- A parameterised or indexed type as the subject of a repr. `optional`, `nullable`, and `list` are how a field uses a parameterised type.
- Pairs (`A × B`), `Unit`, `Atom`, streams, functions, `I64`, `F32`, and tensors as fields. The error names the field.
- Parsing JSON. The codec starts from Elixir terms.
- Keeping the unknown keys of an `open` map.
- Emitting a round-trip property test for a project's own reprs.

Next: [Grammar](grammar.md).

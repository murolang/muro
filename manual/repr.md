---
title: Host representations
slug: repr
order: 15
summary: A repr states the host shape of a data type. Emit writes strict decode and encode, including interned names, maps keyed by data, and an opt-in fallback.
---

# Host representations

In brief: a `repr` states how a data type looks in the host. `mix muro.emit` writes `decode_<type>/1`, `decode_<type>/2`, and `encode_<type>/2` next to the run functions. Decode is total and strict, and it returns the value together with one name table. An ambiguous repr is refused at `mix muro.check`, and the error names the two constructors.

A host calls decode, then the proved function, then encode. The translation is the statement in the book, not a function written beside it. One decode shape covers every type, so a host does not have to know which types contain names.

`repr` is host-side. It is not a kernel term, it has no Agda rule, and it never enters a run image. `Muro.Repr` checks it and emits it. The C, Rust, asm, OTP, and `--node` backends ignore it. `else` does not change `Muro.Check` or the kernel.

The books are `examples/repr.muro` and `examples/repr_names.muro`.

## Syntax

`repr` is a keyword only in `repr Name :=`. A constructor `repr : Box` and `def repr : run Nat := 0` stay names. The words `boolean`, `integer`, `nil`, `list`, `optional`, `nullable`, `tuple`, `map`, `open`, `interned`, `map_of`, and `else` are keywords only inside a repr body. A type with one of those names cannot be named in a shape. `string` is a keyword only in `interned string`. Outside a repr body, `interned`, `map_of`, and `else` are ordinary names: `def else`, a constructor `interned`, and `data map_of` are definitions.

```
repr       ::= "repr" ident ":=" (shape | variant ("|" variant)*)
variant    ::= ident "=>" shape
shape      ::= tight ("else" fallback)*
tight      ::= "boolean" | "integer" | "nil" | atom-lit | string-lit
             | "interned" "string"
             | ident
             | "list" tight | "optional" tight | "nullable" tight
             | "map_of" tight "=>" tight
             | "tuple" "{" [shape ("," shape)*] "}"
             | "map" ["open"] "{" [entry ("," entry)*] "}"
             | "(" shape ")"
fallback   ::= numeral | ident
entry      ::= (string-lit | atom-lit) "=>" shape
```

`else` binds looser than `list`, `optional`, `nullable`, and `map_of`. `list boolean else false` is a fallback on the whole list. Write the parentheses you mean: `optional (boolean else false)`. A parenthesised shape is that shape. It adds no node.

`nil =>` at the start of a variant names the constructor `nil`. Anywhere else `nil` is the host nil. A string is the import string: no escapes, no newline, no `"` inside. An atom literal is `:name`.

```
repr Bool  := boolean
repr Entry := map { "id" => integer, "enabled" => optional Bool }
repr Key   := wild => "*" | named => interned string
repr Template := map_of Key => list Entry
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
| `interned string` | a UTF-8 binary, of any length including empty | the name's index, as `Nat` or as a binary numeral |
| `Entry` | that type's host shape | that type's Muro value |
| `list S` | a proper list | the list-like type's own constructors |
| `nullable S` | `nil` or `S` | the maybe-like type's nullary constructor, or its one field |
| `optional S` | a missing map key, or `S` | the same, and only as a map entry |
| `tuple {…}` | a tuple of that arity | one constructor's fields |
| `map {…}` | a map with those keys | one constructor's fields |
| `map_of K => V` | a map whose keys are data | a list of pairs, or of a two-field record, sorted by the wire key |
| `S else v` | `S`, or a present value `S` rejects at this position | the value `S` decoded, or the fallback |

`boolean` is valid only for a type with exactly two constructors, both nullary, named `true` and `false`. Any other pair is a choice: `on => :true | off => :false`. The refusal says so.

`integer` is valid for `Nat`: a field of type `Nat`, or `repr Nat := integer`. A bare name `Nat` in a shape means `integer`.

A bare name other than `Nat` is a type that has its own repr. A reference to a type with no repr is refused, and the error names the type. A type may refer to itself, and two types may refer to each other. Decoding terminates because the input is finite, but only after a shape has matched a host class. `repr Loop := Loop` is refused: a cycle of bare names would decode the same term forever. The message says the repr must match nil, a boolean, an integer, a literal, a list, a tuple, or a map before it refers to itself. `interned string` and `map_of` consume a host value, so they break such a cycle the way a list does.

`list S` is valid for a field whose type is list-like, by shape rather than by name: one parameter, exactly two constructors, one nullary, one with two fields, the first of the parameter's type and the second the type applied to that parameter. The emitted code uses that type's constructor names. `S` is the element. An improper list is `{:not_list, v}`.

`optional S` and `nullable S` are valid for a field whose type is maybe-like: one parameter, exactly two constructors, one nullary, one with a single field of the parameter's type. The emitted code uses that type's constructor names. `optional` anywhere but a map entry is refused, and the message says to use `nullable`.

## Fields

A `tuple` or a `map` is the whole body of a single-constructor repr, or the shape after `ctor =>`. A constant component (`nil`, an atom literal, a string literal) is a tag: decode checks it, encode emits it, and it consumes no field. Every other component binds the constructor's fields in declaration order. The number of binding components must equal the field count. The error names the constructor and both counts.

A component must suit the field. `integer` suits `Nat`. `boolean` suits the `true` / `false` type. A type name suits a field of that type. `list`, `optional`, and `nullable` suit a list-like or maybe-like field. `interned string`, `map_of`, and `else` have their own suits, below. A mismatch names the constructor, the field index, and the type.

Do not nest a `tuple`, a `map`, or a choice inside a component. Name another type and give that type a repr. `map_of K => V` compiles `K` and `V` with the same rule, so a nested tuple, map, or choice inside them is refused the same way.

A single-constructor type with a bare shape (not a tuple, a map, or a choice) is a newtype: exactly one field, unwrapped. In a choice, a constructor with exactly one field may also be unwrapped (`named => interned string`). A `tuple` or `map` after `ctor =>` always wraps every field. A nullary constructor's shape is a constant. `repr Template := map_of Key => list Entry` is that newtype rule when `Template` has one constructor whose field is such a list. It needs no special case.

A choice names every constructor of the type exactly once. A missing, unknown, or repeated constructor is refused, and the error names it.

Map keys are the string or atom literals as written. A repeated key is refused. Without `open`, a key the repr does not list is `{:unexpected_key, key}`. With `open`, extra keys are ignored. They are not kept, so `decode(encode(v), table)` is still `{:ok, v, table}`.

## Names and the table

`interned string` maps an arbitrary UTF-8 binary to an index. The wire value is a binary that `String.valid?/1` accepts, of any length including empty. Anything else, `nil` included, is `{:not_string, v}` at that path.

One table serves the whole decode, whatever the target type of each position is. A name has one index. Each position builds that index as its own target's numeral. A type that uses no names still returns the table it was given, unchanged. A failed decode returns no table.

The table hosts may rely on has exactly two keys:

```elixir
%{by_name: %{String.t() => non_neg_integer()}, by_index: %{non_neg_integer() => String.t()}}
```

Indices are dense from 0. `map_size(by_name)` equals `map_size(by_index)`, and `by_index` is the inverse of `by_name`. The table is opaque by contract. A host builds one only with the helpers every repr module exports:

| Helper | Meaning |
| --- | --- |
| `muro_repr_table_new/0` | the empty table |
| `muro_repr_table_new/1` | a list of distinct binaries; the position is the index |
| `muro_repr_table_names/1` | the names in index order |

A duplicate name, a non-binary, or a value that is not a list raises `ArgumentError` and names the cause. The helper does not require UTF-8: a host may store a binary it will not decode. A table passed to `decode_<type>/2` or `encode_<type>/2` that does not have this shape raises `ArgumentError` naming the function: `decode_bool table must be %{by_name: %{}, by_index: %{}}`.

`decode_<type>(value)` starts from the empty table. `decode_<type>(value, table)` starts from the table the host passes. Both return `{:ok, value, table}` or `{:error, {path, reason}}`. A host passes a fixed table so a name it already knows, such as its own, has a known index. Functions that compare against the caller's own name depend on that.

The table grows in first-seen order. First-seen order is the order in which decode visits `interned string` positions. That traversal is fixed by the repr, never by map iteration: fixed-key maps and tuples in the order the repr lists their entries, lists in element order, a `map_of` in sorted wire-key order and, inside one pair, the key before the value. A name already in the table, from the host's starting table or from earlier in the same decode, keeps its index. The same wire value decoded twice yields the same value and the same table. Two maps built by inserting the same pairs in opposite orders do too, including a map of more than 32 keys, where the VM's iteration order changes.

The next index is `map_size(by_name)`. An index above `@muro_repr_nat_max` (`1_000_000`) is `{:too_many_names, max}` at the position being decoded. The guard is the same one an integer uses, because a name is built as that numeral. The attribute is emitted only when the book decodes an integer or interns a name.

Encode looks the index up in `by_index`. An index the table does not have raises `ArgumentError` naming the index and the function: `encode_wrap: no name for index 1`. Encode never extends a table.

### Where a name may sit

`interned string` may sit in any component the other shapes can sit in: a field, a `list` element, an `optional` or `nullable` payload, a `map_of` key or value, and the unwrapped single field of a choice arm (`named => interned string`).

It is valid only when the field type is exactly one of these:

1. `Nat`. The name with index `i` is the Peano term of `i`, the same term `integer` builds.
2. A binary-numeral type, recognised by shape and not by name. It is a declared `data` type with no parameters and no indices and exactly three constructors: one nullary, and two that each have exactly one field of the type itself. The nullary constructor may sit in any declaration position. In declaration order the first unary constructor is `d1` and the second is `d2`. The index `i` is the bijective base-2 numeral: `i = 0` is the nullary constructor; an odd `i` is `d1` of the numeral for `(i - 1) / 2`; an even `i > 0` is `d2` of the numeral for `(i - 2) / 2`. Every index has exactly one term, and every term of the type has exactly one index, so encode is total on values of the type. The codec builds and reads the term with loops no deeper than the number of bits.

Every other type is refused at `mix muro.check`. The message names the constructor, the field index, the type, and the allowed targets:

```
constructor named field 0 has type Bool, which does not suit interned string; a name is Nat or a binary numeral type (a nullary constructor and two constructors that each take one field of the type itself)
```

`Atom`, `Unit`, `I64`, a list, a pair, and any type with parameters or indices are refused. `repr Nat := interned string` is refused with the existing message `Nat is represented by integer`. `interned string` as the whole body of a repr whose subject has more than one constructor is refused, including when that subject is itself a binary-numeral type: a repr names a type through its fields. A one-field newtype `repr Wrap := interned string` over `wrap : Nat → Wrap`, or over a binary numeral, is the ordinary newtype rule and is accepted. The target type does not need its own repr. `interned string` is the codec for the field.

### Reserved literals

A choice tries its arms in constructor declaration order. An `interned string` arm accepts every string except the string literals that sibling arms of the same choice name as their whole shape. The guard excludes those literals whatever the declaration order is. `named` declared before `wild` still sends `"*"` to `wild`:

```
repr Key := named => interned string | wild => "*"
```

`"*"` is not entered in the table. Encode of a host-supplied table that contains such a literal raises `ArgumentError`: `encode_key: name "*" is reserved by a sibling constructor`. The decoded table never contains one.

Only a direct string literal of the same choice is reserved. A literal reached through a type reference is not. `named => interned string | lit => Other` overlaps when `repr Other := "hello"`, and the check refuses it. Two `interned string` arms in one choice overlap, and the error names both constructors. An `interned string` arm and an arm whose class is not string stay disjoint.

A binary that is not valid UTF-8 still enters the interned arm, because it is a binary and it is not the reserved literal, and that arm returns `{:not_string, v}`. A non-binary that matches no arm stays `{:no_variant, names, v}`. A bare interned field, not a choice, reports `{:not_string, nil}` for `nil`.

## Maps keyed by data

`map_of K => V` is valid where the field type is list-like and the list's element is either a pair `K' × V'` or a declared single-constructor type with no parameters, no indices, and exactly two fields `K'` and `V'`. A pair element is `{k, v}`. A record element is `{ctor, k, v}`. The list is built with the list type's own constructors, as `list S` does. `K` and `V` are checked against `K'` and `V'` with the same rules as any other field shape. A list element of any other type is refused, and the message names the constructor, the field, and the type. A field that is not a list is refused the same way.

The wire value is a map. A non-map is `{:not_map, v}` at the map's path. `%{}` is the empty list, and the empty list encodes as `%{}`.

Key order is not part of the meaning. Decode produces the list sorted by the wire key in host term order: the order `Enum.sort_by(pairs, fn {k, _} -> {k, is_float(k)} end)` gives. Numbers come before atoms, then tuples, lists, and binaries. An integer sorts before the float that compares equal to it, so `1` comes before `1.0`. The order is never map iteration order. Inside one pair, decode visits the key first and then the value, and the table is threaded through both.

A failure while decoding a key has path `path ++ [{:key, wire_key}]`. A failure while decoding a value has path `path ++ [wire_key]`.

Decode of `K` must be injective on the map's keys. Two different wire keys that decode to the same Muro key, compared with `===`, are an error, never a silent merge: `{:error, {path, {:keys_collide, wire_a, wire_b}}}` at the map's path, with the two wire keys in that same host term order. This can only happen when `K` is not injective, for example a key shape with an `else` fallback. Such a shape is legal at check time and is policed at decode.

Encode turns each element into `{wire_k, wire_v}` and builds a map. A duplicate wire key, the same `K` twice or two `K` values that encode to one wire key, raises `ArgumentError` naming the function and `inspect/1` of the key: `encode_bag: duplicate map key 0`. A list that is not already sorted by wire key is not an error. Encode succeeds, and decode of that map returns the sorted list. `decode(encode(v), table)` equals `{:ok, v, table}` only for a list that was already in that order.

The ambiguity check treats `map_of` as the class of a map that accepts any keys. It overlaps another map shape unless the existing rules separate them. An unknown case is refused.

## Fallbacks

`S else v` is opt-in. Strict decoding stays the default. The fallback is visible in the book.

`else` may follow only `boolean`, `integer`, or a bare type name that has its own repr. It is refused after `list`, `optional`, `nullable`, `tuple`, `map`, `map_of`, `interned string`, a choice, or another `else`. It is refused as the whole body of a repr and as the whole shape of a choice arm (`ctor => boolean else false`). The enclosing container must already have decided the host class, so the fallback can only sit in a component: a tuple or map entry, a `list` element, an `optional` or `nullable` payload, or a `map_of` key or value. Each refusal names the constructor and the field.

The fallback value is written in the book. It is a nullary constructor of the field's type, or, for a `Nat` field, a numeral at most the Nat guard. An unknown name, a constructor that takes fields, a numeral on a non-Nat field, or a numeral above the guard is refused. The message names the type and lists its nullary constructors. `Nat`'s nullary constructor is `0`. The codec builds the value at decode time: the Peano term for a numeral, the atom for a constructor.

The fallback replaces an error whose path equals the position of that shape. It does not replace an error deeper inside, a missing map key, or an integer above the Nat guard. `{:nat_too_large, v}` is a resource limit, not data.

| Shape | Replaced by the fallback | Left as an error |
| --- | --- | --- |
| `boolean else v` | every present value that is not `true` or `false`, including `nil`, `1`, `"yes"`, and a map | — |
| `integer else v`, or `Nat else v` | a present value that is not an integer, or a negative integer | `{:nat_too_large, v}` |
| `Name else v` | a present value for which `decode_name` fails at its own root: a wrong host class, `{:no_variant, …}`, `{:expected, …}`, a missing or unexpected key of that type's map | an error whose path is deeper than that root |
| any `S else v` written as a map entry | — | the entry is absent: `{:missing_key, key}` |

`optional (S else v)` does not change the missing-key rule. An absent key is still the nullary constructor. `optional (boolean else false)` decodes a missing key to `nothing`, `true` to `just true`, and every other present value, `nil` included, to `just false`. A present `nil` is routed to the inner shape only when that inner shape is an `else`. A present `nil` under a plain `optional S` stays `{:nil_not_allowed, nil}`.

`nullable (boolean else false)` decodes `nil` to the nullary constructor first. Every other non-boolean becomes `just false`.

Encode ignores the fallback. `just false` encodes as `false`. Decode of an encoded value is the identity. Encode of a decoded fallback value is not the original wire value.

The ambiguity check and the nil clash see the inner shape, not the fallback. Encode never emits the unexpected values, so `optional (boolean else false)` is not refused for sharing nil with `nothing`.

## Strictness

`decode_<type>/1` and `decode_<type>/2` return `{:ok, value, table}` or `{:error, {path, reason}}`. Decode does not raise for a value the repr rejects. A table that is not a table raises `ArgumentError` before decode looks at the value. `path` is a list of the keys as written and the zero-based list or tuple indices, from the root. `[]` is the root. A `map_of` key failure uses `{:key, wire_key}` as the step.

The first error in a fixed order is the one returned: map keys in the order the repr lists them, then unexpected keys in Erlang term order, then list elements in order. A `map_of` walks keys in host term order.

| Reason | When |
| --- | --- |
| `{:not_boolean, v}` | `boolean`, and `v` is not `true` or `false` |
| `{:not_integer, v}` | `integer`, and `v` is not an integer |
| `{:negative_integer, v}` | a negative integer for a `Nat` |
| `{:nat_too_large, v}` | an integer above the Nat guard; a fallback does not replace it |
| `{:not_string, v}` | `interned string`, and `v` is not a valid UTF-8 binary |
| `{:too_many_names, max}` | a new name would need an index above the Nat guard |
| `{:not_map, v}` | a map or `map_of` shape, and `v` is not a map |
| `{:not_list, v}` | a list shape, and `v` is not a proper list |
| `{:not_tuple, v}` | a tuple shape, and `v` is not a tuple |
| `{:wrong_tuple_size, expected, v}` | a tuple of the wrong arity |
| `{:missing_key, key}` | a required key is absent; the path is the map's path |
| `{:unexpected_key, key}` | a key the repr does not list, and the map is not `open` |
| `{:keys_collide, a, b}` | two wire keys of a `map_of` decoded to one Muro key |
| `{:nil_not_allowed, nil}` | `nil` where the shape is not nullable and has no fallback |
| `{:expected, literal, v}` | a constant tag did not match |
| `{:no_variant, names, v}` | no constructor of the choice matched |

A choice tries constructors in declaration order. A constructor whose host class and constant tags match is committed to. An error inside its fields is that error, with its own path, not `no_variant`. If none matches, the reason is `{:no_variant, names, v}`.

There is no arity-1 `encode_<type>`. `encode_<type>(value, table)` takes the table for every type, also in a book with no names. An arity-1 encode would be unambiguous only until the book gained one `interned string`, and that gain would change what every caller writes. One arity keeps decode, then the proved function, then encode a single idiom. A type that uses no names ignores the table it is given, after checking that the table has the documented shape.

Encode returns the host value directly. It does not return an `:ok` tuple. A term that is not a value of the type raises `FunctionClauseError`. An index missing from the table, a name reserved by a sibling constructor, and a duplicate map key raise `ArgumentError` with a message that names the cause.

## Missing keys, nil, extra keys

| Written | Missing key | Key set to `nil` | Extra key |
| --- | --- | --- | --- |
| `S` | `{:missing_key, key}` | `{:nil_not_allowed, nil}`, unless `S` itself accepts nil | `{:unexpected_key, key}` |
| `S else v` | `{:missing_key, key}` | the fallback, when `nil` fails `S` at this position | `{:unexpected_key, key}` |
| `optional S` | the nullary constructor | `{:nil_not_allowed, nil}`, unless `S` is `nullable` | `{:unexpected_key, key}` |
| `optional (S else v)` | the nullary constructor | the fallback wrapped in the unary constructor | `{:unexpected_key, key}` |
| `optional nullable S` | the nullary constructor | the nullary constructor; encode omits the key | `{:unexpected_key, key}` |
| `nullable S` | not a map entry by itself | the nullary constructor | — |
| `nullable (S else v)` | not a map entry by itself | the nullary constructor; the fallback is not used | — |
| `map open {…}` | as the entry says | as the entry says | ignored, not kept |

`1` is not `true`. A missing key is not `false`. Both are errors unless the repr says otherwise.

## Ambiguity

`mix muro.check` refuses a repr where two constructors can share a host value. The error names both constructors and the type:

```
3:1: repr Shape: constructors circle and square share a host shape (map with "kind" => "circle")
```

The check is conservative. A type name is replaced by the classes of that type's repr. `nullable S` adds nil. An unknown or recursive case overlaps, so it is refused. `else` is transparent: the check sees the inner shape. `interned string` is the string class minus the string literals sibling arms of the same choice name directly. `map_of` is the class of a map that accepts any keys.

Two shapes are disjoint when their classes differ, or both are constants of one class with different values. Two tuples are disjoint when their arities differ or some position is disjoint. Two maps are disjoint when some key is required in both and those value shapes are disjoint, as with `"kind" => "circle"` and `"kind" => "square"`. Two open maps overlap, even when a required key holds different constants. Close the map when that key is the tag. Two integers, two lists, two nils, or two `interned string` arms overlap.

The same check applies inside a shape that has to pick, such as `nullable` of a type whose shape accepts nil.

## Nat

`Nat` is Peano in the emitted module: `0` and `{:suc, n}`. Decode of an integer builds that term with a tail call, one constructor per unit. Encode counts the chain with an accumulator. Both are linear in the value.

An integer above the guard is `{:nat_too_large, v}`. The guard is the module attribute `@muro_repr_nat_max`, set to `1_000_000` in the generated code, so the limit is visible and the same on every run. A negative integer is `{:negative_integer, v}`. A float, a string, or `nil` is `{:not_integer, v}`.

An interned name whose target is `Nat` builds the same Peano term, so the same guard bounds the table. A binary-numeral target, described above, is the other numeral a name may use. Its terms are as deep as the bit count, not as deep as the index. A binary successor beside inductive `Nat` is issue #80, and it is open. This version does not add one. Until that exists, keep host integers and `Nat` names inside the guard, or intern into a binary numeral.

## In a host

`<type>` is the type name in snake case. `Entry` is `entry`. `HttpRequest` is `http_request`. `-` and `'` become `_`. The functions are public. A name that collides with a run, with another type's snake case, or with a codec helper is refused, and the error names both. The table helpers (`muro_repr_table_new`, `muro_repr_table_names`, and the private helpers they use) are on that list in every repr, including a book that interns nothing.

Reprs from imported books are emitted in book order, the same way runs from imports are. A book with no repr emits the same module text as before. A feature's private helpers are emitted only when the book uses that feature, so a boolean repr does not carry the Nat guard or the name decoder.

`mix muro.emit path.muro` prints the module. `mix muro.gen` writes it at the path the manifest names, and the codec is part of that file. `mix muro.gen --check` fails when the repr changes, because the book hash changed, and it fails when the codec is edited by hand. See [Committed modules](gen.md).

```
mix muro.check examples/repr.muro
mix muro.check examples/repr_names.muro
mix muro.emit examples/repr.muro
```

## End to end

`examples/repr.muro` defines `Entry`, `toggle : run Entry → Entry`, and `describe : run Entry → Outcome`. The book has no interned name. The table is empty, and encode still takes it.

```elixir
{:ok, v, table} = Host.Repr.decode_entry(%{"id" => 3, "enabled" => true})
table
# %{by_name: %{}, by_index: %{}}

Host.Repr.encode_entry(Host.Repr.toggle(v), table)
# %{"id" => 3, "enabled" => false}

Host.Repr.encode_outcome(Host.Repr.describe(v), table)
# %{"status" => "on", "id" => 3}

{:ok, missing, table} = Host.Repr.decode_entry(%{"id" => 3})
Host.Repr.encode_outcome(Host.Repr.describe(missing), table)
# nil

Host.Repr.decode_entry(%{"id" => 3, "enabled" => 1})
# {:error, {["enabled"], {:not_boolean, 1}}}
```

The host terms on both ends are maps, booleans, and integers. Nothing in the call builds `{:suc, _}` or `{:just, _}`.

`examples/repr_names.muro` is the wire whose keys are data. `Key` is `wild` for the literal `"*"` and `named` of an interned `Nat` for every other string. `Entry` is a map. A missing `"read"` is `nothing`. Any other present value that is not a boolean, including `nil`, is `just false`. `Template` is a one-field newtype over a list of bindings, and the wire is a map from a key to a list of entries.

```elixir
wire = %{
  "*" => [%{"relation" => "*", "read" => true}],
  "auth" => [%{"relation" => "token", "read" => false}]
}

{:ok, v, table} = Host.ReprNames.decode_template(wire)
Host.ReprNames.muro_repr_table_names(table)
# ["auth", "token"]

v
# {:template,
#  {:cons,
#   {:binding, :wild, {:cons, {:entry, :wild, {:just, true}}, nil}},
#   {:cons,
#    {:binding, {:named, 0},
#     {:cons, {:entry, {:named, {:suc, 0}}, {:just, false}}, nil}},
#    nil}}}
```

`"*"` sorts before `"auth"`. `wild` takes the literal, so `"*"` is not a name. `"auth"` is seen as the map key and is index 0. `"token"` is seen as the relation and is index 1.

`reads_off` turns every `read` flag to `just false`. `count_entries` of this value is `{:suc, {:suc, 0}}`.

```elixir
Host.ReprNames.encode_template(Host.ReprNames.reads_off(v), table)
# %{
#   "*" => [%{"relation" => "*", "read" => false}],
#   "auth" => [%{"relation" => "token", "read" => false}]
# }

Host.ReprNames.count_entries(v)
# {:suc, {:suc, 0}}

Host.ReprNames.decode_template(Host.ReprNames.encode_template(v, table), table)
# {:ok, v, table}
```

A starting table keeps the indices the host already assigned. `"*"` is still `wild`.

```elixir
preset = Host.ReprNames.muro_repr_table_new(["token", "auth"])
{:ok, known, ^preset} = Host.ReprNames.decode_template(wire, preset)
# "auth" is {:named, {:suc, 0}} and "token" is {:named, 0}
Host.ReprNames.encode_template(known, preset) == wire
# true
```

`"read" => 1`, `"read" => nil`, and `"read" => "yes"` each decode as `just false`. The same entry with `optional Bool` and no fallback is `{:error, {["*", 0, "read"], {:not_boolean, 1}}}`.

## Not in this version

- `flatten`, one item per element of a `%{k => [v1, v2]}`. A book states the item type as a record of key and value, as `Binding` does, and decodes with `map_of`.
- A parameterised or indexed type as the subject of a repr. `optional`, `nullable`, and `list` are how a field uses a parameterised type.
- A field whose type is a pair, `Unit`, `Atom`, a stream, a function, `I64`, `F32`, or a tensor. The error names the field. A list of pairs, or of a two-field record, is what `map_of` decodes. An `Atom` field is refused: model the closed set as a type and give it a repr, or intern a name as `Nat` or a binary numeral.
- Parsing JSON. The codec starts from Elixir terms.
- Keeping the unknown keys of an `open` map.
- Emitting a round-trip property test for a project's own reprs.

Next: [Packages](packages.md).

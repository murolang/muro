# JavaScript backend

v1 emits a checked book's `run` terms as one ES module and one declaration file. A session endpoint in that book is a synchronous stepper in the same module. Spec and evidence are omitted. The proof stops at the run image. The host translation is not the book.

`mix muro.emit path.muro --backend js` writes `<stem>.mjs` and `<stem>.d.ts` beside the book and prints both paths, one per line. `Muro.emit_js/1` returns `{:ok, [mjs, dts]}`. `node` runs the module. A `.mjs` file is an ES module without a `package.json`.

C, Rust, and Zig keep the default closed image. JavaScript elaborates with `Muro.IR.elaborate(book, closures: true)`. That flag is the only fork. The default image still refuses an unapplied lambda, a definition passed as a value, and a call of a local function (`c:lambda`).

## Target model

The module is plain JavaScript. Exported runs are `export function` with one parameter per live argument. `run internal` is `function` and is not exported. Generated stream steps are `function` and are not exported. Function declarations are hoisted. `even` and `odd` reach each other through the trampoline.

A lambda is a native arrow function and closes over the bindings in scope. A definition is uncurried. A function value is curried, one argument at a time. The host calls `plus(2n, 3n)`. The host passes a curried function into a higher-order parameter: `map((n) => n + 1n, xs)`. At a definition boundary every leading Π becomes a parameter, including a definition whose body names fewer λs than its type has Πs. `adder := plus`, whose type is `Π (n : Nat) → Π (_ : Nat) → Nat`, is `adder(n, _)`. A second binder of that name is `_2`.

A unary wrapper that only passes its argument on is the function it calls. `tabulate ident` passes `ident`, and `measure (length Nat)` passes `length`. The same rule applies to a function value already in scope and to an internal function. `map (λ (n : Nat) → f n)` passes `f`. The contracted name is the function the wrapper called, so a word boundary stays the residue function the module already used. A partial of a function of several arguments stays an arrow. `map (plus 2)` is `(m) => plus(2n, m)`. That arrow closes over `2n`. The export `plus` takes both arguments at once, so it is not a stand-in for the arrow. `(n) => (m) => plus(n, m)` stays two arrows for the same reason. `(n) => (m) => f(n)(m)` stays two arrows as well: the wrapper applied once must not run `f`.

An immediately applied λ is still a `let`. The argument is evaluated once.

## Values

| Muro | JavaScript |
| --- | --- |
| `Nat` | bigint. `0` is `0n`. `suc` adds one. The host passes `4n`, not `4`. |
| `Unit` | `null` |
| data | `{tag, fields}`. `tag` is the source constructor name. `fields` is the live fields, in order, and is `[]` for a nullary constructor. |
| atom | a string of the source name, with no colon. `:asc` is `"asc"`. |
| pair | a two-element array |
| stream | `{seed, env, step}`. `step(env, seed)` returns `[head, nextSeed]`. |
| `U8` `U32` `U64` | unsigned bigint residues in `0 .. 2^w-1` (`BigInt.asUintN`). |
| `I64` | at the host boundary, a signed bigint (`BigInt.asIntN(64)`). `-1n` is `I64` −1. The minimum is `-(2n**63n)`. A signed input is accepted, and the unsigned residue is accepted too. Inside the module the value is that residue, so word operations match `Muro.Word`. `toNat` of `I64` −1 is `2^64−1`. A constructor field stays the residue. |
| word `Opt` | `{k: "none"}` or `{k: "some", v}`. `Unit` is already `null`, so `none` is not `null`. An exported `Opt` of a word is converted at the boundary. |
| word bool | a JavaScript boolean |
| function | a JavaScript function |
| erased field | `undefined`, only for the `let` the image wraps around an erased constructor field |

An opaque field is not boxed. `erase` and `reveal` are the identity, so a `Nat` stored in a polymorphic field stays a bigint. `fromMaybe` of a `Nat` returns a bigint.

Data constructor tags stay the source strings. Declared `Bool` stays a tagged object, `{tag: "true", fields: []}` or `{tag: "false", fields: []}`, so the canon and the Elixir backend agree: both print `true` or `false`. The declaration file types `Bool` as `{ readonly tag: "true"; readonly fields: readonly [] } | { readonly tag: "false"; readonly fields: readonly [] }`, and a TypeScript host checks `.tag`. `Bool` is not a JavaScript boolean. A word bool is a JavaScript boolean (`WordBool`). `muro__canon` prints both shapes as `true` or `false`, and a single run returns one of the two shapes.

## Words

Word operations follow `Muro.Word`. The residue, the shift guards, signed comparison, checked arithmetic, and `div` / `rem` are the same integers the Elixir backend returns.

A shift whose amount is negative or at least the width yields `0`, except a signed `shri` at or past the width: `0` when the word is below `2^63`, and `2^64−1` when it is not. `div` and `rem` are empty on division by zero, and on `I64` minimum divided by −1. Checked `I64` arithmetic succeeds only when the signed result lies in `[−2^63, 2^63−1]`. The payload inside the module is still the unsigned residue. The export wrapper is the only place that applies `BigInt.asIntN` or `BigInt.asUintN`, so a recursive `I64` function does not sign-extend on each call.

`F32`, `Tensor`, `addt`, and `packI` are `c:machine`. `addi` on a word is the word `add`, and it is emitted. `toU8`, `toU32`, `toU64`, and `toI64` are word `of`. They are emitted.

## Match and data

`match` on `Nat` tests `=== 0n` and otherwise binds the predecessor. `match` on data switches on `.tag` and binds `.fields` in order. `match` on an atom switches on the string. A branch that the image marks empty throws `Error("Empty")`. Erased constructor fields are omitted from `fields` and bound as `undefined` where the body names them.

The closure image tags a `match` with `:nat`, `{:data, name}`, or `:atom`. The default image stays `{:match, scrut, arms}`, which is what C, Rust, and Zig match on.

## Recursion

Named recursion is stack-safe. A self-tail call, the call that sits directly on the pure `match` or `let` spine of its own function, compiles to a loop: the arguments are bound, the parameters are assigned, and the loop continues. Other named recursion, including a call under `suc` and a mutual tail call, is trampolined. A trampoline step is a tagged object, `{ muro__go: f }`. A function value the book returns stays a function. Calls inside one recursive function to another function in the same set pass the trampoline stack. A call from outside that set enters through one bounce.

A host closure that recurses on itself uses the host stack. The trampoline covers the functions the book names.

A self-tail `count` of one million steps returns the same nat as the Elixir backend. On one machine, five JavaScript calls took 23 ms altogether and three Elixir calls took 80 ms, after 33 ms to build the Peano argument. Two hundred calls of `count` at one thousand took 2.2 ms in JavaScript and 1.2 ms in Elixir. Mutual `even` at twenty thousand, five times, took 2.6 ms in JavaScript and 0.2 ms in Elixir: each JavaScript step is a trampoline thunk, and the Elixir call is a tail call. The emitter before this loop overflowed the JavaScript stack on the million-step call.

`let` and `match` that contain no named recursion stay immediately invoked functions, so a branch stays an expression.

## Strings

`String` is a sequence of Unicode scalars. A literal is `"hello"`, with escapes `\\`, `\"`, `\n`, and `\u{…}`. The module boxes it as `{ string: "hello" }`. An atom stays a JavaScript string of the source name, so a host that already passes `"asc"` keeps doing that. `muro__canon` prints the box as `"hello"` and the atom as `hello`. Length is the number of scalars: `muro__slen` counts code points. `strCat` concatenates and `strEq` compares the text. A string and an atom stay distinct.

The declaration file types `String` as `{ readonly string: string }` and `Atom` as `string`. A data type the book names `String` is `String_k`, the same suffix a reserved word takes. This backend emits a string. It is not one of the refusals below.

## Host boundary

`muro__data(tag, ...fields)` builds a constructor value. `muro__uncons` forces one step and returns `[head, tail]`. `muro__canon` prints a value for tests: a bigint as decimal, a negative bigint as its unsigned 64-bit residue, `null` as `tt`, a boolean or an atom string as that text, a string box as a quoted literal, a pair as `(a,b)` with no spaces, data as `tag` or `tag(a,b)`, `none` / `some(v)`, a stream as `stream`, and a function as `fn`. An atom string prints unquoted. The canon string of `I64` −1 is `18446744073709551615`, which is what the Elixir walker prints for the residue. A host that calls the export reads `-1n`.

The host boundary is the exported function. `I64` parameters and results use `BigInt.asIntN(64)` on the way out and `BigInt.asUintN(64)` on the way in, so `-1n` and the residue `2^64−1` are the same word. `U8`, `U32`, and `U64` use `BigInt.asUintN` in both directions. An exported `Opt` or pair of those words is converted the same way, and the call result is bound once. Internal functions, workers, and stream steps see the residue.

The `.d.ts` file exports the runs the module exports, plus `muro__data`, `muro__uncons`, and `muro__canon`. Parameter names are the same spellings as the module. A function parameter whose layout is an arrow is a curried TypeScript arrow. Data is a union of `{tag, fields}`. A data type with a parameter of sort Type is generic, in the order written. `List (A : Type)` is `List<A>`. A field `A` is `A`, a field `List A` is `List<A>`, a field `List (List A)` is `List<List<A>>`, and a field `List Nat` is `List<Nat>`. An index is not a parameter: `Vec A n` is `Vec<A>`, and `Fin` stays a plain alias. A type the declaration cannot name stays `unknown`.

`Stream` carries its element. The seed and the environment stay `unknown`, because the seed is not the element. The step returns `[A, unknown]`. `muro__uncons<A>` takes `Stream<A>` and returns `[A, Stream<A>]`. An erased type parameter of an exported run is a generic of that function, and the module does not take it. `length` is `length<A>(xs: List<A>)` in the declaration and `length(xs)` in the module. `Bool` stays the tagged union of `true` and `false`. The file documents `I64` as the signed bigint the host sees. Internal runs and steps are omitted. Type names that TypeScript reserves (`string`, `String`, `Nat`, a keyword) gain the same `_k` suffix as a colliding value spelling, including a type parameter. The kernel string keeps the name `String`.

A source name folds `-` to `_`. `golden-silence` is `golden_silence`. A name that is already a JavaScript identifier stays as written: `zeros`, `a_b`, `a_b_2`, `fromMaybe`, and `Bit`. `Bit` is a legal JavaScript identifier. A strict-mode keyword, a host name (`undefined`, `Array`, `NaN`, `eval`, `arguments`), or a TypeScript word the declaration file cannot reuse gains `_k` (`function` is `function_k`, a type named `string` is `string_k`, and a type named `String` is `String_k`). A character that is not in the identifier alphabet after that fold (`?`, `!`, `'`, a leading digit, any other scalar) is an injective `$` escape. The module and the declaration file use that same spelling. A binder is claimed against the function names and the step names in the file, so a parameter `id` does not hide a function `id`. A parameter `_` stays `_`, and a second one is `_2`. A helper or a step is `muro__` plus a tag (`muro__step_0`).

Two source names that reach one identifier are refused before any file is written, and the error names both. `golden-silence` and `golden_silence` are one identifier. `a-b` and `a_b` are one identifier. A reserved-word rewrite collides the same way: `function` becomes `function_k`, so a book that also defines `function_k` is refused. C, Rust, and Zig keep the injective encoding, where `z` doubles, `_` is `zu`, and `-` is `zd`, so `a-b`, `a_b`, and `a_b_2` spell three ways (`azdb`, `azub`, `azubzu2`).

## Unsupported

A book that contains one of these is refused before any file is written. The error is the whole message. A host placement is refused before a session is planned. A session the machine cannot represent is refused before a run is elaborated.

- `c:machine`. `F32`, `Tensor`, `addt`, and `packI`, including `examples/nx_add.muro`.
- `c:stream`. A raw `ν`, `Always`, or `~` inside a `run`. A `run` whose type is `Stream` is emitted. An `evidence` `Always` or `~` is omitted with the other evidence.
- `c:erased`. A gone variable used as a value.
- `c:host`. A place, a scheme, or a move. A book that also has sessions is refused the same way, and nothing is written. `--backend fsm` may still emit those sessions.
- A session, meeting, endpoint, reading, choreography, talk, seat, link, or relay that the state machine cannot represent. The reason is the one `--backend fsm` reports (`seen is not a state machine`, an unguarded `rec`, an unknown session, and the rest of that list). Nothing is written. A conformance or a meeting on its own does not refuse the book: the endpoints are the steppers.
- A session payload whose type has a `repr`, including a field of a payload data type and a `Nat` bound when `Nat` has a `repr`. The stepper uses the run image, not a host codec. The reason names the session and the type. `--backend fsm` still accepts that book.

OTP, `--node`, fsm, and `repr` codecs are not this backend. A lambda is a closure, and this backend emits it.

## Committed modules

`mix muro.gen` and `mix muro.init` accept `backend: js`. A JavaScript entry names a target ending in `.mjs`, omits the module, and also writes the `.d.ts` beside it. That declaration path is reserved the way a C header is reserved. The files are not formatted. The comment mark is `// `. `mix muro.gen --check` compares both files with the book. A hand-edited body, a header version that is not the running Muro, a body that is not what the book emits, a book that changed under the file, or a missing file fails the check for that path.

## Out of scope

- `repr` encode and decode
- the browser DOM. The module is plain ECMAScript and does not touch it. This backend is run under Node.

## Differential testing

Tests elaborate the same book twice. Elixir comes from `Muro.emit_file/3`, compiled in the test, and walked to the canon string above. JavaScript is the emitted module, imported by a driver, and printed with `muro__canon`. Streams are compared by forcing a prefix with `Enum.take` on one side and `muro__uncons` on the other. The original seed is forced twice to check that `uncons` does not mutate it. CI installs Node and runs these differentials. When `CI` is set and `node` is missing, the file fails. When `CI` is unset and `node` is missing, the differentials are skipped.

A layout-directed Elixir walk treats `{:suc, _}` as a `Nat` before it treats an atom-headed tuple as a constructor. A pair of `Nat`s is printed as a pair. Atoms and nullary constructors print without a colon, so the atom `:b0` and the JavaScript string `"b0"` that carries it both print `b0`. A string prints as a quoted literal, so the atom `b0` and the string `"b0"` do not print the same text. `:nil` and `{tag: "nil", fields: []}` both print `nil`.

## Sessions

A session endpoint is one exported object. The name is the session's JavaScript spelling (`grant-end` is `grant_end`). A host name gains `_k`, so the session `window` is `window_k`. `done?` is the method `done`. The generated code is synchronous. It does not start a process, and it does not talk to a peer. The host sends and receives on its own transport.

```js
let state = ping.init();
ping.expected(state);                 // { k: "recv", type: "nat" }
const step = ping.recv(state, 0n);   // { ok: state } or { error }
state = step.ok;
ping.done(state);                     // true or false
ping.check_trace([{ k: "recv", value: 0n }, { k: "send", value: 1n }], { complete: true });
```

`init` returns the state. A parameterized session takes one bigint nat per parameter: `stream.init(0n)`. The wrong arity, or a nat that is not a non-negative bigint, returns `{ error: { message } }` and does not throw.

`send` and `recv` return `{ ok: state }` or `{ error: { unexpected: true, step, expected, value } }`. `value` is the host value unchanged. `step` is the same string `--backend fsm` uses: the book path, the line, the session, the ordinal, and the action.

`expected` is `"done"`, `{ k: "send", type }` or `{ k: "recv", type }`, or `{ k: "send_pick", labels: ["b0", "b1"] }` or `{ k: "recv_pick", labels: ["b0", "b1"] }`. A type is `"nat"`, `"bit"`, `"unit"`, `{ k: "pair", left, right }`, `{ k: "record", fields }`, `{ k: "vec", elem, len }`, `{ k: "data", name, args }`, or `{ k: "nat_at_most", max }`.

A payload is the run image. A nat is a bigint. A bit is `"b0"` or `"b1"`. Unit is `null`. A pair is a two-element array. A record is an object whose keys are the field names. A vector is an array. Data is `{ tag, fields }`, including declared `Bool`. A choice is `{ k: "pick", label: "b0" }` or `"b1"`, passed to `send` on a chooser and to `recv` on a brancher.

`check_trace` replays `{ k: "send", value }` and `{ k: "recv", value }`. A prefix is valid and returns `{ ok: true }`. A bad step returns `{ error: { index, unexpected: true, step, expected, value } }`. `{ complete: true }` also requires `done`, or `{ error: { index, incomplete: true, step, expected } }`. A parameterized session takes `{ args: [0n] }`. A missing or wrong-length `args` list returns `{ error: { message } }`.

A book may declare runs and sessions together. The runs stay exported functions. A state is opaque. `muro__session` is the only field the declaration file names.

The declaration file exports `SessionStepper` and one `export const` per session. `init` may return a state or `{ error: { message } }`. `send` and `recv` return `{ ok }` or `{ error }`.

An `async` wrapper that loops on `expected` and waits for the host is not emitted.

## Open questions

- Browsers, beyond Node, once the module is loaded as an ES module.

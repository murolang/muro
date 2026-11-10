# JavaScript backend

v1 emits a checked book's `run` terms as one ES module and one declaration file. Spec and evidence are omitted. The proof stops at the run image. The host translation is not the book.

`mix muro.emit path.muro --backend js` writes `<stem>.mjs` and `<stem>.d.ts` beside the book and prints both paths, one per line. `Muro.emit_js/1` returns `{:ok, [mjs, dts]}`. `node` runs the module. A `.mjs` file is an ES module without a `package.json`.

C, Rust, and Zig keep the default closed image. JavaScript elaborates with `Muro.IR.elaborate(book, closures: true)`. That flag is the only fork. The default image still refuses an unapplied lambda, a definition passed as a value, and a call of a local function (`c:lambda`).

## Target model

The module is plain JavaScript. Exported runs are `export function` with one parameter per live argument. `run internal` is `function` and is not exported. Generated stream steps are `function` and are not exported. Function declarations are hoisted, so `even` and `odd` call each other.

A lambda is a native arrow function and closes over the bindings in scope. A definition is uncurried. A function value is curried, one argument at a time. The host calls `plus(2n, 3n)`. The host passes a curried function into a higher-order parameter: `map((n) => n + 1n, xs)`. At a definition boundary every leading Π becomes a parameter, including a definition whose body names fewer λs than its type has Πs. `adder := plus`, whose type is `Π (n : Nat) → Π (_ : Nat) → Nat`, is `adder(n, zu)`.

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
| `U8` `U32` `U64` `I64` | bigint residues in `0 .. 2^w-1`. `I64` is not a signed bigint. `toNat` of `I64` −1 is `2^64−1`. |
| word `Opt` | `{k: "none"}` or `{k: "some", v}`. `Unit` is already `null`, so `none` is not `null`. |
| word bool | a JavaScript boolean |
| function | a JavaScript function |
| erased field | `undefined`, only for the `let` the image wraps around an erased constructor field |

An opaque field is not boxed. `erase` and `reveal` are the identity, so a `Nat` stored in a polymorphic field stays a bigint. `fromMaybe` of a `Nat` returns a bigint.

Data constructor tags stay the source strings. `true` and `false` from `Bool` are `"true"` and `"false"`, not booleans. A word bool is a boolean. Both print as `true` or `false` through `muro__canon`, and a single run returns one of the two shapes.

## Words

Word operations follow `Muro.Word`. The residue, the shift guards, signed comparison, checked arithmetic, and `div` / `rem` are the same integers the Elixir backend returns.

A shift whose amount is negative or at least the width yields `0`, except a signed `shri` at or past the width: `0` when the word is below `2^63`, and `2^64−1` when it is not. `div` and `rem` are empty on division by zero, and on `I64` minimum divided by −1. Checked `I64` arithmetic succeeds only when the signed result lies in `[−2^63, 2^63−1]`. The payload is still the unsigned residue.

`F32`, `Tensor`, `addt`, and `packI` are `c:machine`. `addi` on a word is the word `add`, and it is emitted. `toU8`, `toU32`, `toU64`, and `toI64` are word `of`. They are emitted.

## Match and data

`match` on `Nat` tests `=== 0n` and otherwise binds the predecessor. `match` on data switches on `.tag` and binds `.fields` in order. `match` on an atom switches on the string. A branch that the image marks empty throws `Error("Empty")`. Erased constructor fields are omitted from `fields` and bound as `undefined` where the body names them.

The closure image tags a `match` with `:nat`, `{:data, name}`, or `:atom`. The default image stays `{:match, scrut, arms}`, which is what C, Rust, and Zig match on.

## Recursion

Calls are direct. JavaScript engines do not guarantee tail-call elimination, so a recursion whose depth follows a `Nat` can overflow the stack. v1 does not trampoline. Mutual recursion is ordinary hoisted functions. `let` and `match` are immediately invoked functions, so a branch stays an expression. Those extra frames are intentional: there is no tail-call contract to keep.

## Strings

The core has no string type. Atoms are the nominal strings, represented as JavaScript strings of the source name. They do not collide with a future host string type because that type is not in this image. A host that wants a string of characters does not get one from v1.

## Host boundary

`muro__data(tag, ...fields)` builds a constructor value. `muro__uncons` forces one step and returns `[head, tail]`. `muro__canon` prints a value for tests: a bigint as decimal, `null` as `tt`, a boolean or an atom string as that text, a pair as `(a,b)` with no spaces, data as `tag` or `tag(a,b)`, `none` / `some(v)`, a stream as `stream`, and a function as `fn`.

The `.d.ts` file exports the runs the module exports, plus `muro__data`, `muro__uncons`, and `muro__canon`. Parameter names are the same spellings as the module. A function parameter whose layout is an arrow is a curried TypeScript arrow. Data is a union of `{tag, fields}`. A polymorphic field is `unknown`. `Stream` does not carry its element type. `I64` is documented as the unsigned residue. Internal runs and steps are omitted. Type names that TypeScript reserves (`string`, `Nat`, a keyword) gain the same `_k` suffix as a colliding value spelling.

Identifiers use `Muro.Emit.Name`. A source spelling contains no `__`. It gains `_k` when the encoding is a JavaScript strict-mode keyword or a host name (`undefined`, `Array`, `NaN`, `eval`, `arguments`, and the TypeScript words the declaration file cannot reuse). A binder is claimed against the function names and the step names in the file, so a parameter `id` does not hide a function `id`. A helper or a step is `muro__` plus a tag (`muro__step_0`). `a-b`, `a_b`, and `a_b_2` spell three ways.

## Sessions, later

v1 does not emit sessions, OTP processes, `--node`, or `repr` codecs. A session declaration in a book that also has runs is omitted, and the runs are emitted. A book that is only sessions emits the runtime and no session functions.

A later backend can map a session to async functions or to an explicit stepper. A meeting is two tasks and a queue, not a BEAM process. `init`, `send`, and `recv` would be the steps. Mailboxes are not threads. That mapping is not in v1, and v1 does not pretend a JavaScript `Promise` is a GenServer.

## Out of scope for v1

- `c:machine` (`F32`, `Tensor`, `addt`, `packI`) and `c:stream` (a raw `ν`, `Always`, or `~` inside a `run`)
- sessions as processes, OTP, `--node`, fsm, and host effects
- `repr` encode and decode
- `muro gen`, `muro init`, and the manifest allow-list
- a trampoline, and any promise that a deep `Nat` recursion stays under the stack limit
- a host string type, richer `.d.ts` generics (`List<A>`), and a signed view of `I64`
- the browser DOM. The module is plain ECMAScript and does not touch it. v1 is run under Node.

`c:erased` remains a refusal when a gone variable is used as a value. The checker usually rejects that term before emit.

## Differential testing

Tests elaborate the same book twice. Elixir comes from `Muro.emit_file/3`, compiled in the test, and walked to the canon string above. JavaScript is the emitted module, imported by a driver, and printed with `muro__canon`. Streams are compared by forcing a prefix with `Enum.take` on one side and `muro__uncons` on the other. The original seed is forced twice to check that `uncons` does not mutate it.

A layout-directed Elixir walk treats `{:suc, _}` as a `Nat` before it treats an atom-headed tuple as a constructor. A pair of `Nat`s is printed as a pair. Atoms and nullary constructors print without a colon, so `:b0` and the string `"b0"` agree, and `:nil` and `{tag: "nil", fields: []}` both print `nil`.

## Open questions

- A trampoline, if deep `Nat` recursion has to survive the JavaScript stack.
- Whether the host should also see `I64` as a signed bigint. The residue is what matches Elixir.
- Generics in the declaration file (`List<A>` rather than `unknown`).
- Whether `muro gen` and `muro init` should accept `backend: js`.
- A real string type, distinct from atoms.
- Session as async functions or as an `init` / `send` / `recv` stepper.
- Browsers, beyond Node, once the module is loaded as an ES module.
- Whether a saturated partial application should eta-contract to the export. v1 emits the wrapper `(m) => plus(n, m)`.

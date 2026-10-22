---
title: Examples
slug: examples
order: 14
summary: Every file in examples/ and what it is for.
---

# Examples

In brief: every file in the sections above Refused checks with `mix muro.check path`. They are the worked book, not sketches. Prefer copying from here over inventing syntax. The files under Refused are what that command turns down.

Check one file:

```
mix muro.check examples/half_ok.muro
```

Check the built-in book (must match `half_ok.muro`):

```
mix muro.check
```

## half_ok.muro

The three modes in one book.

```
IsEven : Nat → Type                 -- spec
half   : Nat → Nat                  -- run
half_ok : (n : Nat) → IsEven n →    -- evidence
            plus (half n) (half n) ≡ n
```

Also defines `plus` (run) and `plus_suc` (evidence). Half of eight is four. Evidence is `match` + `refl` + `rewrite` + `matchEmpty`. Nothing here except `plus` and `half` is emitted.

See [The wall](wall.md), [Terms](language.md), [Identity](identity.md).

## ping.muro

An affine session. The protocol is spec. The process is evidence. The Elixir, C, Rust, and assembly emitters omit it. `--backend otp` writes a GenServer for each process.

```
session ping := recv Nat (send Nat end)
conform pong : ping := get Nat (put 1 done)

session %1 ping-done := recv Nat (send Nat end)
conform pong-done : ping-done := get Nat (put 1 done)
```

`pong` receives a nat and sends `1`. `left-open` sends `0` and then abandons the channel. `untouched` abandons it before any action. `open-stop` is the same abandonment written `session %0`. `pong-done` is that protocol as `session %1`, and it finishes. `chosen` takes the first arm of an internal choice. `both` offers `done` and then `put 0 done`. A second send, a send where the protocol says receive, or an abandoned `%1` channel, is refused; those books live in `test/muro_session_test.exs`, so a program copies the form that checks.

See [Terms](language.md#session) and [Emit](emit.md#otp).

## dual.muro

The other end of a session. The protocol is spec. The process is evidence. The run emitters omit both.

```
session ping := recv Nat (send Nat end)
session back := dual ping
conform peer : back := put 1 (get Nat done)
```

`ping` receives a nat and then sends `1`. `back` is the other end, so `peer` sends `1` and then receives a nat. `forth` is `dual back`, and that is `ping` again. `reply` is the other end of `session %1 ping-done`, so it carries that mark and the process finishes. `offered` is the other end of a `choose`, and the process is a `cover`. `kept` is the run definition in the same file. `mix muro.emit examples/dual.muro` emits `kept`.

A value of a type the other end does not name, a mark other than the named session's mark, or a cycle of duals, is refused. Those books live in `test/muro_dual_test.exs`, so a program copies the form that checks.

See [Terms](language.md#session).

## meet.muro

Two processes on one session. The meeting is evidence. The run emitters omit it.

```
session ping := recv Nat (send Nat end)
session back := dual ping
conform pong : ping := get Nat (put 1 done)
conform peer : back := put 1 (get Nat done)
meet wire : pong with peer
```

`pong` receives a nat and sends `1`. `peer` is the other end, so it sends `1` and receives a nat. `wire` is the evidence that those two processes are that exchange. `arm` is a choice: `pick0 done` meets `cover done (get Nat done)`. `drop` is both ends abandoning after `0`. `box` sends a pair of a bit and a record `{x : Nat, y : Nat}`. That pair is a tuple, and the record is a map whose keys are `x` and `y`. `here` sends `(b0, {x = 0, y = 0})`. `far` sends `(b1, {x = 1, y = 2})` of that same type, and it meets `there`. `kept` is the run definition in the same file. `mix muro.emit examples/meet.muro` emits `kept`.

`mix muro.emit examples/meet.muro --backend otp` writes `meet_otp.ex`. `MeetOtp.wire/0` starts `pong` and `peer` as each other's peer. `arm` starts the choice. `drop` starts both ends abandoning after `0`. `wrapped` carries the pair. Each server talks to one peer. `Pong.start/1` still takes a peer pid supplied by the caller. See [Emit](emit.md#otp).

A process whose session is not the other end, or a payload type the two processes do not share, is refused. Those books live in `test/muro_meet_test.exs`, so a program copies the form that checks.

See [Terms](language.md#session).

## talk.muro

One description of an exchange. Each party has a session. The description is spec. The run emitters omit it.

```
talk ping-exchange := say peer pong Nat (say pong peer Nat over)
session ping := seen pong with peer in ping-exchange
session back := seen peer with pong in ping-exchange
conform pong : ping := get Nat (put 1 done)
conform peer : back := put 1 (get Nat done)
meet wire : pong with peer
```

`pong` receives a nat and then sends `1`, so `ping` is `recv Nat (send Nat end)`. `peer` has `send Nat (recv Nat end)`. `wire` is the evidence that those two processes are that exchange. `both-arms` is an offer of two sends of a nat from `b` to `c`, so `a` with `b` is `choose end end`, `b` with `c` is `send Nat end`, and `a` with `c` is `end`. `arm` is `a` offering `b` the choice of `end` or a send of a nat. `kept` is the run definition in the same file. `mix muro.emit examples/talk.muro` emits `kept`.

A party the description does not seat, or a description that refers to itself, is refused. Those books live in `test/muro_talk_test.exs`, so a program copies the form that checks.

See [Terms](language.md#session).

## seated.muro

A party of a description sits at a place. The seating is spec. The boundary is evidence. The run emitters omit both.

```
place home := node a
place away := node b
talk ping-exchange := say peer pong Nat (say pong peer Nat over)
seat pong-home : pong at home in ping-exchange
seat peer-away : peer at away in ping-exchange
link go : cross pong-home with peer-away in ping-exchange
```

`pong` sits at `home`. `peer` sits at `away`. They have a session, so the boundary crosses once. `peer` at `home` stays with `pong`. Ambient stays with itself, and ambient to a node crosses once. The other direction of a boundary is that same boundary. `ping` is still `recv Nat (send Nat end)`, and `pong` receives a nat and then sends `1`. The payload stays on the session. `kept` is the run definition in the same file. `mix muro.emit examples/seated.muro` emits `kept`.

A party with no session in the description has no boundary. A `stay` where the places differ, or a `cross` where they are the same, is refused. Those books live in `test/muro_seated_test.exs`, so a program copies the form that checks.

See [Terms](language.md#session).

## arrow.muro

A `%1` binder must be used. A `%0` binder, and an unmarked binder, may be dropped.

```
def keep : run Π (%1 x : Nat) → Nat :=
  λ (%1 x : Nat) → x

def loose : run Π (%0 x : Nat) → Nat :=
  λ (%0 x : Nat) → 0
```

`keep` returns its argument. `use` applies it to `0`. `loose` and `plain` drop the argument. A `%1` binder that is never used, a λ whose mark disagrees with the Π, or a second use of the variable, is refused; those books live in `test/muro_arrow_test.exs`.

See [Terms](language.md#binders-and-quantities).

## place.muro

A named place stays or crosses once. The place and the scheme are spec. The move is evidence. The Elixir, C, Rust, and assembly emitters omit all three. `--node` writes one call for each cross.

```
place home := ambient
place away := node a

scheme local := fixed home
scheme poly := any

move stay local : home
move cross local : away
move stay poly : home
move stay poly : away
```

`local` is fixed at `home`. Reading it there stays. Reading it at `away` crosses once. `poly` stays at `home` and at `away`. `kept` is the `run` definition in the same file.

```
mix muro.emit examples/place.muro --node a
```

That writes `place_node.ex`. The module is `PlaceNode`. The cross is `PlaceNode.cross_local_at_away/1`: a call to the process registered as `:local` on the node `:a`, with the message `{:muro_read, "local"}`. Each stay is absent from that file. `mix muro.emit examples/place.muro` emits `kept`.

A `stay` on that cross, a `cross` on a stay, or a `cross` of `poly`, is refused. Those books live in `test/muro_place_test.exs`, so a program copies the form that checks.

See [Terms](language.md#place) and [Emit](emit.md#node).

## located.muro

A session read at a place. The endpoint is spec. The reading is evidence. The Elixir, C, Rust, and assembly emitters omit both. A run definition has no seat.

```
endpoint ping-home := ping at local

read stay pong : ping-home at home := get Nat (put 1 done)
read cross pong-away : ping-home at away := get Nat (put 1 done)
```

`ping` is fixed at `home` through `local`. Reading it there stays. Reading it at `away` crosses once. `ping-poly` stays at `home` and at `away`. `pong-done` is `session %1` and finishes at `away`. `left-open` abandons an unmarked session, and that reading crosses once. `kept` is the run definition in the same file. `mix muro.emit examples/located.muro` emits `kept`.

`mix muro.emit examples/located.muro --node a` writes `located_node.ex`. `pong-away`, `pong-done`, and `left-open` are the three calls, and each one reads `local`. `pong`, `pong-poly`, and `pong-poly-away` stay, so they write no call. The payload stays on the session. See [Emit](emit.md#node).

`mix muro.emit examples/located.muro --backend otp` writes `located_otp.ex`. `Pong` and `PongAway` both receive a nat and send `1`. `LeftOpen` sends `0` and abandons the channel. The server talks to one peer. See [Emit](emit.md#otp).

A `stay` on that cross, a `cross` on a stay, a `cross` of `ping-poly`, a value of a type the protocol does not name, or an abandoned `%1` channel, is refused. Those books live in `test/muro_located_test.exs`, so a program copies the form that checks.

See [Terms](language.md#endpoint).

## internal_ok.muro

`run internal` helper `step` emits `defp`. `inc` is `run` and calls it. See [Emit](emit.md).

## zeros.muro

A productive `run` Stream of zeros. `head-zeros` is `{head zeros ≡ 0 : Nat}` by `refl`.

## nats.muro

`natsFrom n` is the stream `n, suc n, …`. Emit is `Stream.unfold/2`. `(+ k : Nat)` is legal because Nat is Data.

## always.muro

`Always` as evidence: every element of `zeros` is `0`. The proof is the head equation together with the same proof at the tail. `uncons` of that proof is the equation paired with the predicate at `tail zeros`.

## bisim.muro

`zeros ~ zeros'` and `tail (natsFrom n) ~ natsFrom (suc n)`. Rutten’s stream calculus, Theorem 2.1. `uncons` of `zeros ~ zeros'` is the head equation and `tail zeros ~ tail zeros'`. Evidence only.

## higher_order.muro

A `run` definition as a value. `map` and `tabulate` take a `+` function; `tabulate ident` passes a definition, `map (plus 2)` a partial application, and `measure (length Nat)` a partial application whose given argument is erased. The emitted code passes curried closures ([Emit](emit.md#functions-as-values)); C emit refuses it (`c:lambda`).

## dominance.muro

A declared ν family, `Dom f g`: every element of `f` is at most the element of `g` at the same position. `dom-refl` proves `Dom s s`, `zeros-below` proves `Dom zeros (natsFrom n)` with the tail obligation at `natsFrom (suc n)`, and `dom-head` reads the head obligation back with `head`. Evidence only; `zeros` and `natsFrom` are emitted.

See [Streams](streams.md).

## even_dec.muro

`Dec P = P ⊎ (P → Empty)`. `evenDec` decides `IsEven n`. A decision, not LEM. Evidence; not emitted.

## either_run.muro

A `run` sum. `fromLeft` emits `{:left, _}` / `{:right, _}`.

See [Either and Dec](either.md).

## list.muro

`List A`, `nil` / `cons`, `length`, `ones2`. `List A` is Data iff `A` is. `length-ones2` is `refl`.

## maybe.muro

`Maybe`, `fromMaybe`, `fromJust1`. Erased type argument.

## even_odd.muro

`even` and `odd` call each other and descend on the same `Nat` argument. `even-two` is `refl`.

## tree.muro

Binary trees of structure (no payloads). `size` descends on both children.

## vec.muro

`Fin n`, `Vec A n`, `lookup` without a runtime bounds check. `vhead` and `vtail` match a `Vec A suc(m)` with a motive that computes from the index (`Vec A (pred k)`), and `lookup` recurses on the tail. `lookup-ok` is `refl`.

See [Data](data.md) and [Indexed data](indexed.md).

## pair.muro

`let (x, y) = p in plus x y` opens an affine pair once. `addPair`, `swap` (run); `three-ok` and `swap-ok` are `refl`. `let` emits a pattern match.

See [Terms](language.md).

## result.muro

`Result E A` with constructors `ok` and `error`: a failing `run` function returns a sum, and the constructor names are the Elixir tags `{:ok, _}` / `{:error, _}`. `pred`, `orZero` (run); `pred-two` and `pred-zero` are `refl`.

See [Emit](emit.md).

## nx_add.muro

`I64` and `Tensor`. `doubled` is `[2, 4]` after `Nx.to_flat_list/1`. Nat stays Peano.

See [Machine numbers](machine.md).

## using_prelude.muro

Uses `sym`, `cong`, and `pred` from the prelude and defines none of them. `before` is `pred (suc (suc 0))`. There is no Agda twin: the prelude is an Elixir book, not a kernel rule. See [Terms](language.md#prelude).

## Refused

`mix muro.check` fails on each of these. `even_odd.muro` is the mutual recursion that checks.

### bad_dup.muro

Two data types are both named `Foo`. `foo` builds the first at `0` and `bar` builds the second at `suc(0)`. One name for both types lets a match skip the branch it should check.

### bad_wrap.muro

`bad` takes `Wrap → Empty`, and `wrap` stores a `Bad`. Each declaration is strictly positive on its own. Together the negative occurrence is `Bad` inside `Wrap`, placed in a domain.

### cycle_empty.muro

`impossible` calls `helper` and `helper` calls `impossible`. Both inhabit `Empty`. Neither calls itself. The failure is the cycle, not a missing name.

### bad_stuck.muro

`bad` takes a function of a `Nat`. The `0` branch is `Bad → Empty`, and `n` is bound, so the match does not reduce. The field is still not strictly positive.

### bad_positive.muro

`mk : (D → Nat) → D`. `D` occurs in the domain of a field. Strict positivity refuses it.

### bad_alias.muro

`BadAlias := D → Nat`, then `mk : BadAlias → D`. The checker unfolds the alias and refuses the same negative field. The name `BadAlias` is not what fails.

### bad_cons.muro

`cons` has two fields. A branch with one binder and a branch with three both fail, naming `cons` and the count `2`. `list.muro` and `vec.muro` are the matches that check.

### bad_shared.muro

`ping` matches on its first argument and passes `suc(p)` as `pong`'s second; `pong` matches on its second and passes `suc(q)` as `ping`'s first. Under every choice of positions some call passes a `suc`, not a smaller variable or the argument itself, so the block is refused. `even_odd.muro` is the mutual recursion that checks.

### bad_second_field.muro

`drop1 (cons y ys)` is `ys`. The false equation `{drop1 (cons y ys) ≡ zs}` is refused; `second_field.muro` is the true one. A match on a constructor with several fields puts every field in place at once.

## cshrl/

[CSHRL](cshrl.md) as a library. `lib/` holds the generic modules, written against `param` entries, and `envs/` holds three environments that supply them and run an agent. `envs/optimal.muro` is the return theorem: the go agent's reward stream dominates every other policy. Check an environment; a file under `lib/` alone is refused for its unsupplied params.

```
mix muro.check examples/cshrl/envs/binary_sacrifice.muro
```

## Adding a file

1. Put it in `examples/`. Use only `run` / `run internal` / `spec` / `evidence`.
2. Every binder is `(x : A)` or `(+ x : A)` or `(- x : A)`.
3. Every `match` / `rewrite` writes `motive (λ x → …)` in parentheses.
4. Recursion on `run`/`evidence` goes through `match` and a smaller variable.
5. `mix muro.check examples/your_file.muro`.
6. If it belongs in CI, add parse/check/emit in `test/muro_check_test.exs`.

Do not edit Agda or `lib/muro/*.ex` to make a program work. If the program is allowed by the grammar and the checker refuses a term that should check, that is a kernel bug — a different job. See [For agents](for-agents.md).

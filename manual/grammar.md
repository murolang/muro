---
title: Grammar
slug: grammar
order: 15
summary: The surface grammar lib/muro/parser.ex implements.
---

# Grammar

In brief: this is the grammar `lib/muro/parser.ex` implements. ASCII aliases are in parentheses. If this page and the parser disagree, the parser is the implementation and this page is wrong.

```
book       ::= (import | param | nu | data | talk | session | conform | place | scheme | move | endpoint | read | meet | seat | link | def)*
import     ::= "import" string             -- a path, relative to this file
param      ::= "param" ident ":" tag term  -- supplied by an importing file
nu         ::= ("ν" | "nu") ident binder+ ":" "Type" "where" "uncons" ":" term
data       ::= "data" ident binder* ":" telescope "where" (ident ":" term)+
telescope  ::= "Type" | binder ("→" | "->") telescope | term ("→" | "->") "Type"
talk       ::= "talk" ident ":=" talk-term
talk-term  ::= "over" | "(" talk-term ")" | ident
             | "say" party party pay talk-term
             | "offer" party party talk-term talk-term
party      ::= ident                  -- over, say, and offer are not parties
session    ::= "session" mult? ident sparam* ":=" (proto | "dual" sref | "seen" ident "with" ident "in" ident)
sparam     ::= "(" ident ":" "Nat" ")"
sref       ::= ident sarg*
mult       ::= "%0" | "%1"             -- default %0; %1 must finish
conform    ::= "conform" ident ":" sref ":=" proc
place      ::= "place" ident ":=" ("ambient" | "node" ident)
scheme     ::= "scheme" ident ":=" ("any" | "fixed" ident)
move       ::= "move" ("stay" | "cross") ident ":" ident
endpoint   ::= "endpoint" ident ":=" ident "at" ident
read       ::= "read" ("stay" | "cross") ident ":" ident "at" ident ":=" proc
meet       ::= "meet" ident ":" ident "with" ident ("buffer" numeral)?
seat       ::= "seat" ident ":" party "at" ident "in" ident
link       ::= "link" ident ":" ("stay" | "cross") ident "with" ident "in" ident
proto      ::= "end" | "(" proto ")"
             | ("send" | "recv") pay proto
             | ("send" | "recv") "(" ident ":" pay ")" proto
             | ("send" | "recv") "(" ident ":" "Bit" ")" "on" proto proto
             | ("choose" | "branch") proto proto
             | "rec" ident "." proto
             | "case" scrut ("|" ident "=>" proto)+
             | ident sarg*                   -- a session declared earlier; a rec variable takes no arguments
scrut      ::= ident | "(" ident ident ")"  -- the name just bound, or (run name)
sarg       ::= numeral | ident | "suc" sarg | "(" sarg ")"
proc       ::= "done" | "stop" | "(" proc ")"
             | "put" pval proc
             | "get" "(" ident ":" pay ")" proc
             | "get" "(" ident ":" "Bit" ")" "on" proc proc
             | ("pick0" | "pick1") proc
             | "cover" proc proc
             | "match" ident proc+
             | "match" ident ("|" ident ident* "=>" proc)+
             | "rec" ident "." proc
             | ident                         -- jump
pay        ::= "Nat" | "Bit" | "Unit" | pay "*" pay | "(" pay ")"
             | "{" (ident ":" pay ("," ident ":" pay)*)? "}"
             | "Vec" pay pay
             | ident pay*                    -- non-indexed declared data type
pval       ::= numeral | "tt" | "b0" | "b1" | ident | "(" pval ")"
             | "(" pval "," pval ")"
             | "{" (ident "=" pval ("," ident "=" pval)*)? "}"
numeral    ::= [0-9]+
def        ::= "def" ident ":" tag term ":=" term
             | "def" ident ":" ety ":=" etm
tag        ::= "run" "internal"? | "spec" | "evidence"
ety        ::= "(" ident ":" ident ")" earrow ety
             | "done"
             | ident
earrow     ::= "⊸" | "-o" | "→" | "->"
etm        ::= eatom eatom*
eatom      ::= ("λ¹" | "lam1" | "λ" | "lam") "(" ident ":" ident ")" earrow etm
             | "dual" eatom
             | "meet" eatom eatom
             | "(" etm ")"
             | ident

term       ::= atom atom*                  -- juxtaposition is application
             | term ("×" | "*") term
             | term "⊎" term               -- desugars to Either
             | term "::" term              -- desugars to cons
             | term ("→" | "->") term      -- non-dependent, = Π (_ : A) → B
             | term "~" term               -- bisimulation (also prefix "bisim")
atom       ::= "Type" | "Nat" | "I64" | "F32" | "Unit" | "Empty" | "refl" | "tt" | "0" | "?"
             | suc | pi | lam | let | match | matchEmpty | rewrite | idt
             | stream | unfold | uncons
             | "fst" atom | "snd" atom          -- sugar for let
             | "head" atom | "tail" atom
             | "Tensor" atom atom | "addi" atom atom | "muli" atom atom
             | "addt" atom atom | "toI64" atom | "packI" atom atom
             | "Always" atom atom atom
             | "bisim" atom atom
             | "[]"                        -- desugars to nil
             | "(" term ")" | "(" term "," term ")"
             | ident

suc        ::= "suc" "(" term ")" | "suc" atom
stream     ::= "Stream" atom
unfold     ::= "unfold" atom atom         -- seed, λ s → (head, next_seed)
uncons     ::= "uncons" atom
qty        ::= "+" | "-" | "%0" | "%1" | ε  -- ε = %0 = affine (default); %1 must be used
binder     ::= "(" qty ident ":" term ")"
pi         ::= ("Π" | "Pi") binder ("→" | "->") term
lam        ::= ("λ" | "lam") binder ("→" | "->") term
let        ::= "let" "(" ident "," ident ")" "=" term "in" term

match      ::= "match" term "motive" mot
               "|" "0" "=>" term
               "|" "suc" ident "=>" term
             | "match" term "motive" mot
               ("|" ident ident* "=>" term)+
matchEmpty ::= "matchEmpty" term "motive" mot
rewrite    ::= "rewrite" term "motive" mot "in" term
mot        ::= "(" ("λ" | "lam")? (ident | binder) ("→" | "->") term ")"
               -- nested λ in the body cover index binders (Vec / Fin)
idt        ::= "{" term ("≡" | "==") term ":" term "}"

ident      ::= [A-Za-z_][A-Za-z0-9_-]*
comment    ::= "--" through end of line
space      ::= [ \t\n\r] | comment
```

## Notes the grammar does not say loudly enough

Application is juxtaposition (`f a b`). `motive`, `in`, and `def` never start an argument. Digits start atoms, so `| 0 =>` parses.

A keyword is a whole word. `successor`, `reflect`, `ttl`, and `Natural` are identifiers; `suc`, `refl`, `tt`, and `Nat` are not. `->` ends a word, so `Nat->Nat` is an arrow.

`end`, `send`, `recv`, `choose`, `branch`, `rec`, `case`, `done`, `stop`, `put`, `get`, `pick0`, `pick1`, `cover`, `b0`, and `b1` are keywords inside a `session` or a `conform`. Outside that form they are identifiers, so `def end : run Nat := 0` is a definition. `match` is a keyword in a process, where it chooses the next action, and in a term, where it is the eliminator. Parentheses group a nested protocol or process: `recv Nat (send Nat end)`. `send` and `recv` name one payload type and one continuation. `put` writes a value of that type. `get` names the type. `choose` and `branch` still name two protocols. `dual` is a keyword in `session name := dual name` and in an endpoint function (`dual s`). Outside those forms it is an identifier, so `def dual : run Nat := 0` is a definition. The mark on a dual session is the named session's mark when it is omitted. `seen` is a keyword in `session name := seen party with party in talk`. `with` there names the other party, and `in` names the description. Outside that form `seen` is an identifier, so `def seen : run Nat := 0` is a definition. `meet` and `with` are keywords in `meet name : left with right`. `meet` is also the keyword in an endpoint function (`meet s t`). `with` is also the keyword between the two parties of a `seen` session. Outside those forms they are identifiers, so `def meet : run Nat := 0` and `def with : run Nat := 0` are definitions.

A payload type is `Nat`, `Bit`, `Unit`, a pair, a record of named fields, a vector, or a non-indexed declared data type applied to the payload types written after it (`send Bool end`, `send (Maybe Nat) end`). `Vec` is the vector form, so a data type of that name is not written there. A pair is a tuple, and `*` in a payload associates to the right, so `send Nat * Bit end` is `send (Nat * Bit) end`. A record is a map whose keys are the names written there, in that order, and that order is the type: `{x : Nat, y : Nat}` and `{y : Nat, x : Nat}` are different types. `{}` is the empty record. A repeated name is refused. A key is a name in the type. `Vec Nat n` is a vector whose length is the name `n`. `Vec Nat 2` is a vector of that numeral length. The element is one payload type, so a pair element is parenthesized: `Vec (Nat * Bit) n`. `Nat`, `Bit`, `Unit`, and `Vec` are those types only where a payload is written. Outside a payload, `Bit` is an identifier, so `def Bit : run Nat := 0` is a definition, and so is `def Vec : run Nat := 0`. A payload value is a numeral, `tt`, `b0`, `b1`, a pair `(v, w)`, a record `{ name = v }`, `rep`, a constructor (`true`, `(just 0)`, `(cons 0 nil)`), a variable bound by an enclosing `get`, or the application of an in-scope `run` definition (`(effective self)`, `(bump 0)` when `bump` calls an earlier `run`, or a bare run name). The sent value is the value that definition computes from its arguments. A `run` that calls itself or a later `run` is not a put source. `rep n 0` is a vector of the length `n` whose element is `0`. `rep` is that value only where a payload value is written. The type of a value is the type of what was written, in that order.

Value binding: `get (k : Type) continuation` receives a value of that type and binds it to `k`. The continuation can send that name at that type. `get (k : Nat) (put k done)` sends back the value it received. The innermost binding of a name is the one that is sent. Every payload type is data, so the bound value can be sent more than once. `recv (n : Nat) continuation` binds `n` for the payloads in the continuation. `recv (n : Nat) (send (Vec Nat n) end)` receives a nat and then sends a vector of that length. `send (n : Nat)` binds the same way. `recv (Nat)` and `recv (Vec Nat n)` name a type and do not bind. `send (d : Nat) {d ≤ w}` is an evidence payload: the sender owes `d ≤ w`. The left side of the bound is the name just bound, and the right side is a numeral or a nat bound earlier. `<=` is the same as `≤`. The payload is `Nat`. The name is in scope in its bound only. `recv (d : Nat) {d ≤ w}` receives that nat. `put` writes the nat alone. `recv (b : Bit) on S T` receives a bit. `b0` continues as `S` and `b1` continues as `T`. `send (b : Bit) on S T` sends that bit. `get (b : Bit) on P Q` offers both arms and binds the bit in each. The sender writes `put b0` or `put b1`. A variable does not select an arm, and neither does a computed bit. `get (b : Bit) (match b P Q)` is a process. The scrutinee is the name that `get` just bound. A bit has two arms, `b0` then `b1`. A declared data type has one arm per constructor, in declaration order. The arms are processes with no constructor names, or `|` followed by the constructor, one name per field, and `=>`. The binder count is the field count. A bit stays two processes, `b0` then `b1`, and the same two names may be written. Each arm conforms to the one continuation. The processes may differ, and the received value chooses which process runs. `match` outside a process is the term `match`. `on` is a keyword only after that bit binder. Outside that form it is an identifier, so `def on : run Nat := 0` is a definition. `case f | bytes => S | headers => T` is the continuation of the `send` or `recv` that bound `f`. The arms are constructors, in declaration order. `case (late f) | true => S | false => T` applies the `run` `late` to that name. `case` outside a protocol is an identifier, so `def case : run Nat := 0` is a definition. `recv (n : Nat) on` is refused: a next action is chosen by a bit. `get Bit on` is refused: a bit index is bound. `rec X. S` is that protocol again where `X` stands. The name is an identifier, then a dot, then the body. `X` alone is that continuation. The same form repeats a process: `rec X. P`, and `X` is the jump. A variable must sit under an action of its own `rec`. `rec X. X` is refused. A name in a process with no `rec` is refused. A name in a protocol is a call of a session declared earlier. Its arguments are nat values: a numeral, a name, `suc` of an argument, or a parenthesized application such as `(bump 0)`. A parameter is `(k : Nat)` before `:=`. `(send …)` after a name is the next protocol, not an argument, so `choose ack (send Nat end)` is `ack` and then that send. `choose (ack) (frames 3)` writes two arms when the second arm would otherwise look like an argument. `dual ping` may name a session declared later. `dual (stream 0)` is the dual of that application. `rec` is a keyword only inside a protocol or a process, so `def rec : run Nat := 0` is a definition.

`talk`, `over`, `say`, and `offer` are keywords in `talk name := …`. `over` finishes the description. `say` is one party sending one payload, then one continuation. A party off that `say` has the continuation's session. `offer` is one party choosing, and it still has two arms. A party off an `offer` has a session when both arms are the same description. A party is a name. `over`, `say`, and `offer` are not party names. A name in a description is another description. Outside that form they are identifiers, so `def talk : run Nat := 0` and `def say : run Nat := 0` are definitions. The mark on a `seen` session is the mark written there. An omitted mark is `%0`.

`ambient` and `node` are keywords on the right of a `place`. `any` and `fixed` are keywords on the right of a `scheme`. `stay` and `cross` are keywords in a `move`, and in a `link`. Outside those forms they are identifiers, so `def stay : run Nat := 0` is a definition. A `place` names `ambient` or `node` followed by a node name. A `scheme` is `any`, or `fixed` followed by a place name. A `move` states `stay` or `cross`, then a scheme name, then a place name.

`at` is a keyword in an `endpoint`, in a `read`, and in a `seat`. An `endpoint` names a session and a scheme: `endpoint name := session at scheme`. A `read` states `stay` or `cross`, then a process name, an endpoint name, `at`, a place name, and a process. A `seat` names a party, a place, and a description: `seat name : party at place in talk`. A `link` states `stay` or `cross`, then two seats, `in`, and that description: `link name : stay seat with seat in talk`. Outside those forms `endpoint`, `read`, `at`, `seat`, and `link` are identifiers, so `def seat : run Nat := 0` and `def link : run Nat := 0` are definitions. The same place stays. Two places cross once. The payload stays on the session.

`%0` and `%1` are whole tokens. `%10` is not `%1` followed by `0`. On a session, an unmarked session is `%0`, and `%1` requires the process to finish. On a Π or λ binder, an unmarked binder is `%0`, and `%1` requires the variable to be used. Both marks are the affine quantity. The λ mark and the Π mark must agree.

An endpoint function has no mode tag. Its type starts with `(`. `(s : ping) ⊸ ping` is a linear arrow (`-o` is the same arrow). `(s : ping) → ping` is affine. `λ¹` (`lam1`) binds the endpoint linearly. `λ` (`lam`) binds it affinely. The arrow after `λ` may be `→` or `⊸`; the multiplicity is the lambda's. `done` is the meeting. `dual` and `meet` are keywords in that body: `dual s`, `meet s t`. `+`, `-`, and `%` on an endpoint binder are refused. The function is evidence. The named session may repeat, and its payload may be a declared data type. `dual` keeps `rec` and that payload. A following `def`, `session`, or `meet name :` is the next entry.

Inside a `data` block each constructor declaration `ident ":" term` begins on its own line; that is how an application stops before the next constructor. On one line, `f x : Nat` inside `{ … }` is the application `f x` followed by the type. A following line that starts with `session` or `conform`, or with a `place`, `scheme`, `move`, `endpoint`, `read`, `meet`, `talk`, `seat`, or `link` entry, ends that type the same way. A constructor may be named `talk`, `place`, `scheme`, `move`, `endpoint`, `read`, `meet`, `seat`, or `link`: the entry forms are `talk name :=`, `place name :=`, `scheme name :=`, `move stay` or `move cross`, `endpoint name :=`, `read stay` or `read cross`, `meet name :`, `seat name :`, and `link name :`. `talk : Type`, `meet : Type`, `seat : Type`, and `link : Type` are constructors. `buffer` is a keyword only after the right-hand process of `meet name :`, and only with a numeral. `def buffer : run Nat := 0` is a definition.

A `ν` block has one destructor, `uncons`. `ν Stream (A : Type)` is checked for shape and dropped. Any other name declares a family: its binders are the indices, at least one, and the type of `uncons` must be the family applied to them in order, `→` the body ([Streams](streams.md#declared-families)).

`?` is an unsolved goal. It parses. It never checks. See [Terms](language.md#holes).

Not in the surface (present in the kernel AST only): `matchUnit`, annotations `{e : A}`, raw de Bruijn.

## Operator tightness (approximate)

From the Pratt parser in `lib/muro/parser.ex`:

| Construct | Binding |
| --- | --- |
| juxtaposition (app) | tightest |
| `::` | tight |
| `×` / `*` | |
| `⊎` | |
| `~` | |
| `→` / `->` | loosest among these |

## Binder quantities

```
Π (n : Nat) → …        affine (default), and the variable may be unused
Π (%0 n : Nat) → …     the same affine binder, written out
Π (%1 n : Nat) → …     affine, and the variable must be used once
Π (+ n : Nat) → …      reuse, if the type WHNFs to Data
Π (- e : IsEven n) → … erased
```

## Identity, match, rewrite

```
{plus (half n) (half n) ≡ n : Nat}

match n motive (λ x → P)
  | 0 => tz
  | suc p => ts

match m motive (λ _ → A)
  | nothing => d
  | just a  => a

matchEmpty e motive (λ _ → P)

rewrite eq motive (λ z → P) in t
```

`refl` checks against `{x ≡ y : A}` only when `x` and `y` convert.

Next: [Examples](examples.md).

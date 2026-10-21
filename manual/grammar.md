---
title: Grammar
slug: grammar
order: 13
summary: The surface grammar lib/muro/parser.ex implements.
---

# Grammar

In brief: this is the grammar `lib/muro/parser.ex` implements. ASCII aliases are in parentheses. If this page and the parser disagree, the parser is the implementation and this page is wrong.

```
book       ::= (import | param | nu | data | session | conform | place | scheme | move | endpoint | read | def)*
import     ::= "import" string             -- a path, relative to this file
param      ::= "param" ident ":" tag term  -- supplied by an importing file
nu         ::= ("ν" | "nu") ident binder+ ":" "Type" "where" "uncons" ":" term
data       ::= "data" ident binder* ":" telescope "where" (ident ":" term)+
telescope  ::= "Type" | binder ("→" | "->") telescope | term ("→" | "->") "Type"
session    ::= "session" mult? ident ":=" (proto | "dual" ident)
mult       ::= "%0" | "%1"             -- default %0; %1 must finish
conform    ::= "conform" ident ":" ident ":=" proc
place      ::= "place" ident ":=" ("ambient" | "node" ident)
scheme     ::= "scheme" ident ":=" ("any" | "fixed" ident)
move       ::= "move" ("stay" | "cross") ident ":" ident
endpoint   ::= "endpoint" ident ":=" ident "at" ident
read       ::= "read" ("stay" | "cross") ident ":" ident "at" ident ":=" proc
proto      ::= "end" | "(" proto ")"
             | ("send" | "recv" | "choose" | "branch") proto proto
proc       ::= "done" | "stop" | "(" proc ")"
             | ("put" | "get") bit proc
             | ("pick0" | "pick1") proc
             | "cover" proc proc
bit        ::= "b0" | "b1"
def        ::= "def" ident ":" tag term ":=" term
tag        ::= "run" "internal"? | "spec" | "evidence"

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

`end`, `send`, `recv`, `choose`, `branch`, `done`, `stop`, `put`, `get`, `pick0`, `pick1`, `cover`, `b0`, and `b1` are keywords inside a `session` or a `conform`. Outside that form they are identifiers, so `def end : run Nat := 0` is a definition. Parentheses group a nested protocol or process: `recv end (send end end)`. `dual` is a keyword in `session name := dual name`. Outside that form it is an identifier, so `def dual : run Nat := 0` is a definition. The mark on a dual session is the named session's mark when it is omitted.

`ambient` and `node` are keywords on the right of a `place`. `any` and `fixed` are keywords on the right of a `scheme`. `stay` and `cross` are keywords in a `move`. Outside those forms they are identifiers, so `def stay : run Nat := 0` is a definition. A `place` names `ambient` or `node` followed by a node name. A `scheme` is `any`, or `fixed` followed by a place name. A `move` states `stay` or `cross`, then a scheme name, then a place name.

`at` is a keyword in an `endpoint` and in a `read`. An `endpoint` names a session and a scheme: `endpoint name := session at scheme`. A `read` states `stay` or `cross`, then a process name, an endpoint name, `at`, a place name, and a process. Outside those forms `endpoint`, `read`, and `at` are identifiers, so `def read : run Nat := 0` is a definition.

`%0` and `%1` are whole tokens. `%10` is not `%1` followed by `0`. On a session, an unmarked session is `%0`, and `%1` requires the process to finish. On a Π or λ binder, an unmarked binder is `%0`, and `%1` requires the variable to be used. Both marks are the affine quantity. The λ mark and the Π mark must agree.

Inside a `data` block each constructor declaration `ident ":" term` begins on its own line; that is how an application stops before the next constructor. On one line, `f x : Nat` inside `{ … }` is the application `f x` followed by the type. A following line that starts with `session` or `conform`, or with a `place`, `scheme`, `move`, `endpoint`, or `read` entry, ends that type the same way. A constructor may be named `place`, `scheme`, `move`, `endpoint`, or `read`: the entry forms are `place name :=`, `scheme name :=`, `move stay` or `move cross`, `endpoint name :=`, and `read stay` or `read cross`.

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

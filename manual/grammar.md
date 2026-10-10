---
title: Grammar
slug: grammar
order: 13
summary: The surface grammar lib/muro/parser.ex implements.
---

# Grammar

In brief: this is the grammar `lib/muro/parser.ex` implements. ASCII aliases are in parentheses. If this page and the parser disagree, the parser is the implementation and this page is wrong.

```
book       ::= (import | nu | data | def)*
import     ::= "import" string             -- a path, relative to this file
nu         ::= ("ν" | "nu") "Stream" binder ":" term "where" "uncons" ":" term
data       ::= "data" ident binder* ":" telescope "where" (ident ":" term)+
telescope  ::= "Type" | binder ("→" | "->") telescope | term ("→" | "->") "Type"
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
qty        ::= "+" | "-" | ε               -- ε = affine (default)
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

Application is juxtaposition (`f a b`). `motive`, `in`, and `def` never start an argument. Digits start atoms, so `| 0 =>` parses. A keyword ends at a word boundary: `successor`, `ttl`, and `reflex` are identifiers, not `suc`, `tt`, or `refl` followed by letters.

Inside a `data` block each constructor declaration `ident ":" term` begins on its own line; that is how an application stops before the next constructor. On one line, `f x : Nat` inside `{ … }` is the application `f x` followed by the type.

The parser only accepts `ν Stream` with constructor `uncons`. Other names are an error.

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
Π (n : Nat) → …        affine (default)
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

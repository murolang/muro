------------------------------------------------------------------------
-- MuroTT v1 syntax.
--
-- de Bruijn Tm n — metatheory, the executable check, and the examples.
--
-- Raw HOAS (Tm → Tm) is not the inductive syntax.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Syntax where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.String.Base using (String; _++_)
open import Data.Unit.Base using (⊤)


open import Muro.Base

------------------------------------------------------------------------
-- Fixed-width word operators. The residue arithmetic lives in Muro.Word.
-- I64's type stays the `i64` constructor; ku64 and ki64 share 64 bits.
------------------------------------------------------------------------

data WKind : Set where
  ku8 ku32 ku64 ki64 : WKind

data WOp : Set where
  wty   : WKind → WOp                 -- U8, U32, U64 (I64's type is i64)
  wlit  : WKind → ℕ → WOp             -- bit pattern, no arguments
  wof   : WKind → WOp                 -- ofNat, one Nat argument
  wton  : WOp                         -- toNat, one word argument
  wadd  : WOp                         -- wrapping add
  wsub  : WOp
  wmul  : WOp
  wcadd : WOp                         -- checked add, result is Opt
  wcsub : WOp
  wcmul : WOp
  wdiv  : WOp                         -- truncating div, Opt (zero divisor)
  wrem  : WOp
  weq   : WOp                         -- WBool
  wlt   : WOp
  wle   : WOp
  wand  : WOp
  wor   : WOp
  wxor  : WOp
  wnot  : WOp
  wshl  : WOp                         -- shift by a Nat, total
  wshr  : WOp
  wcast : WKind → WOp                 -- explicit widening, narrowing, bitcast
  wbool : WOp
  wtrue : WOp
  wfalse : WOp
  wopt  : WOp                         -- Opt A, one type argument
  woptk : WKind → WOp                 -- Opt of a word kind, saturated
  wsome : WOp
  wnone : WOp

wk≡ᵇ : WKind → WKind → Bool
wk≡ᵇ ku8  ku8  = true
wk≡ᵇ ku32 ku32 = true
wk≡ᵇ ku64 ku64 = true
wk≡ᵇ ki64 ki64 = true
wk≡ᵇ _    _    = false

wop≡ᵇ : WOp → WOp → Bool
wop≡ᵇ (wty k)     (wty k′)     = wk≡ᵇ k k′
wop≡ᵇ (wlit k n)  (wlit k′ n′) = wk≡ᵇ k k′ ∧ (n ≡ᵇ n′)
wop≡ᵇ (wof k)     (wof k′)     = wk≡ᵇ k k′
wop≡ᵇ wton        wton         = true
wop≡ᵇ wadd        wadd         = true
wop≡ᵇ wsub        wsub         = true
wop≡ᵇ wmul        wmul         = true
wop≡ᵇ wcadd       wcadd        = true
wop≡ᵇ wcsub       wcsub        = true
wop≡ᵇ wcmul       wcmul        = true
wop≡ᵇ wdiv        wdiv         = true
wop≡ᵇ wrem        wrem         = true
wop≡ᵇ weq         weq          = true
wop≡ᵇ wlt         wlt          = true
wop≡ᵇ wle         wle          = true
wop≡ᵇ wand        wand         = true
wop≡ᵇ wor         wor          = true
wop≡ᵇ wxor        wxor         = true
wop≡ᵇ wnot        wnot         = true
wop≡ᵇ wshl        wshl         = true
wop≡ᵇ wshr        wshr         = true
wop≡ᵇ (wcast k)   (wcast k′)   = wk≡ᵇ k k′
wop≡ᵇ wbool       wbool        = true
wop≡ᵇ wtrue       wtrue        = true
wop≡ᵇ wfalse      wfalse       = true
wop≡ᵇ wopt        wopt         = true
wop≡ᵇ (woptk k)   (woptk k′)   = wk≡ᵇ k k′
wop≡ᵇ wsome       wsome        = true
wop≡ᵇ wnone       wnone        = true
wop≡ᵇ _           _            = false

showKind : WKind → String
showKind ku8  = "U8"
showKind ku32 = "U32"
showKind ku64 = "U64"
showKind ki64 = "I64"

showWOp : WOp → String
showWOp (wty k)    = showKind k
showWOp (wlit k n) = showKind k ++ "#" ++ show n
showWOp (wof k)    = "to" ++ showKind k
showWOp wton       = "toNat"
showWOp wadd       = "addi"
showWOp wsub       = "subi"
showWOp wmul       = "muli"
showWOp wcadd      = "addc"
showWOp wcsub      = "subc"
showWOp wcmul      = "mulc"
showWOp wdiv       = "divi"
showWOp wrem       = "remi"
showWOp weq        = "eqi"
showWOp wlt        = "lti"
showWOp wle        = "lei"
showWOp wand       = "andi"
showWOp wor        = "ori"
showWOp wxor       = "xori"
showWOp wnot       = "noti"
showWOp wshl       = "shli"
showWOp wshr       = "shri"
showWOp (wcast k)  = "as" ++ showKind k
showWOp wbool      = "WBool"
showWOp wtrue      = "wtrue"
showWOp wfalse     = "wfalse"
showWOp wopt       = "Opt"
showWOp (woptk k)  = "Opt " ++ showKind k
showWOp wsome      = "wsome"
showWOp wnone      = "wnone"

------------------------------------------------------------------------
-- de Bruijn terms. Index n is the number of free variables.
------------------------------------------------------------------------

data Tm (n : ℕ) : Set where
  var   : Fin n → Tm n
  typ   : Tm n                                 -- Type  (a sort; not Type : Type)
  pi    : Qty → Tm n → Tm (suc n) → Tm n       -- Π (q x : A) → B
  lam   : Qty → Tm n → Tm (suc n) → Tm n       -- λ (q x : A) → e
  app   : Tm n → Tm n → Tm n
  nat   : Tm n
  ze    : Tm n
  su    : Tm n → Tm n
  unit  : Tm n
  one   : Tm n
  empty : Tm n
  -- Data: D params indices, constructor D.j, match with a motive.
  dty   : ℕ → Tm n
  ctor  : (di ci : ℕ) → Tm n
  mData : Tm n → Tm (suc n) → List (Tm n) → Tm n
  -- match with explicit motive
  mNat  : (scrut : Tm n) (mot : Tm (suc n))
          (tz : Tm n) (ts : Tm (suc n)) → Tm n
  mEmp  : (scrut : Tm n) (mot : Tm (suc n)) → Tm n
  mUnit : (scrut : Tm n) (mot : Tm (suc n)) (tu : Tm n) → Tm n
  -- identity {e₁ ≡ e₂ : A}
  idt   : (A e₁ e₂ : Tm n) → Tm n
  rfl   : Tm n
  -- rewrite eq with explicit motive (x.P) and body : P[rhs]
  rwt   : (eq : Tm n) (mot : Tm (suc n)) (body : Tm n) → Tm n
  def   : ℕ → Tm n                             -- global definition
  ann   : Tm n → Tm n → Tm n                   -- {e : A}
  -- products: A × B, (a, b), the projections, and the tensor eliminator
  -- let (a, b) = e in t (t binds a at var 1 and b at var 0)
  prod  : Tm n → Tm n → Tm n
  pair  : Tm n → Tm n → Tm n
  letp  : Tm n → Tm (suc (suc n)) → Tm n
  -- ν X. F  (F binds X at var 0). Stream A = ν X. A × X.
  nu    : Tm (suc n) → Tm n
  unf   : Tm n → Tm n → Tm n                   -- unfold seed (λ s → (head, next))
  ucons : Tm n → Tm n
  -- Nx wrappers. Spec formers; computed values are run.
  -- Nat stays Peano. These constructors do not reduce: surface toI64,
  -- addi, and muli are the word former below.
  i64    : Tm n
  f32ty  : Tm n
  tensor : Tm n → Tm n → Tm n                  -- Tensor D S
  addi   : Tm n → Tm n → Tm n
  muli   : Tm n → Tm n → Tm n
  addt   : Tm n → Tm n → Tm n
  toi64  : Tm n → Tm n
  packi  : Tm n → Tm n → Tm n                  -- two I64s; shape is the I64 literal 2
  -- Fixed-width words. One former, so U8, U32, U64, and I64 share a
  -- residue arithmetic (Muro.Word). I64's type is still `i64`.
  word   : WOp → List (Tm n) → Tm n

------------------------------------------------------------------------
-- Global definition identifiers (closed book).
------------------------------------------------------------------------

plusId    : ℕ
plusId    = 0
isEvenId  : ℕ
isEvenId  = 1
halfId    : ℕ
halfId    = 2
plusSucId : ℕ
plusSucId = 3
halfOkId  : ℕ
halfOkId  = 4

showDef : ℕ → String
showDef 0 = "plus"
showDef 1 = "IsEven"
showDef 2 = "half"
showDef 3 = "plus_suc"
showDef 4 = "half_ok"
showDef n = "def" ++ show n

------------------------------------------------------------------------
-- Pretty-printer (debugging the decision procedure).
------------------------------------------------------------------------

mutual
  showTm : ∀ {n} → Tm n → String
  showTm (var i)      = "v" ++ show (toℕ i)
  showTm typ          = "Type"
  showTm (pi q A B)   = "Π(" ++ showQty q ++ " : " ++ showTm A ++ ") → " ++ showTm B
  showTm (lam q A t)  = "λ(" ++ showQty q ++ " : " ++ showTm A ++ ") → " ++ showTm t
  showTm (app f a)    = "(" ++ showTm f ++ " " ++ showTm a ++ ")"
  showTm nat          = "Nat"
  showTm ze           = "0"
  showTm (su t)       = "suc(" ++ showTm t ++ ")"
  showTm unit         = "Unit"
  showTm one          = "tt"
  showTm empty        = "Empty"
  showTm (dty i)      = "D" ++ show i
  showTm (ctor i j)   = "c" ++ show i ++ "." ++ show j
  showTm (mData e P _) =
    "match " ++ showTm e ++ " motive " ++ showTm P
  showTm (mNat e P z s) =
    "matchNat " ++ showTm e ++ " motive " ++ showTm P ++
    " | 0 => " ++ showTm z ++ " | suc => " ++ showTm s
  showTm (mEmp e P)   = "matchEmpty " ++ showTm e ++ " motive " ++ showTm P
  showTm (mUnit e P u) =
    "matchUnit " ++ showTm e ++ " motive " ++ showTm P ++ " | tt => " ++ showTm u
  showTm (idt A a b)  = "{" ++ showTm a ++ " ≡ " ++ showTm b ++ " : " ++ showTm A ++ "}"
  showTm rfl          = "refl"
  showTm (rwt e P t)  = "rewrite " ++ showTm e ++ " motive " ++ showTm P ++ " in " ++ showTm t
  showTm (def i)      = showDef i
  showTm (ann e A)    = "{" ++ showTm e ++ " : " ++ showTm A ++ "}"
  showTm (prod A B)   = "(" ++ showTm A ++ " × " ++ showTm B ++ ")"
  showTm (pair a b)   = "(" ++ showTm a ++ ", " ++ showTm b ++ ")"
  showTm (letp e t)   = "let (_, _) = " ++ showTm e ++ " in " ++ showTm t
  showTm (nu F)       = "ν(" ++ showTm F ++ ")"
  showTm (unf s f)    = "unfold " ++ showTm s ++ " " ++ showTm f
  showTm (ucons s)    = "uncons " ++ showTm s
  showTm i64          = "I64"
  showTm f32ty        = "F32"
  showTm (tensor d s) = "Tensor(" ++ showTm d ++ " " ++ showTm s ++ ")"
  showTm (addi x y)   = "addi(" ++ showTm x ++ " " ++ showTm y ++ ")"
  showTm (muli x y)   = "muli(" ++ showTm x ++ " " ++ showTm y ++ ")"
  showTm (addt t u)   = "addt(" ++ showTm t ++ " " ++ showTm u ++ ")"
  showTm (toi64 t)    = "toI64(" ++ showTm t ++ ")"
  showTm (packi x y)  = "packI(" ++ showTm x ++ " " ++ showTm y ++ ")"
  showTm (word op ts) = showWOp op ++ "(" ++ showArgs ts ++ ")"

  showArgs : ∀ {n} → List (Tm n) → String
  showArgs []       = ""
  showArgs (t ∷ []) = showTm t
  showArgs (t ∷ ts) = showTm t ++ " " ++ showArgs ts

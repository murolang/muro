------------------------------------------------------------------------
-- MuroTT: quantities, modes, usages, and the checker's Result type.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Base where

open import Data.Bool.Base using (Bool; true; false; _∧_; not; if_then_else_)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
open import Data.String.Base using (String; _++_)
open import Data.Unit.Base using (⊤; tt)
open import Function.Base using (case_of_)

------------------------------------------------------------------------
-- Quantities q
--   affine  — default: at most one run use
--   reuse   — +, reuse only if the type is Data
--   erased  — -, compile-time / type argument
------------------------------------------------------------------------

data Qty : Set where
  affine : Qty
  reuse  : Qty
  erased : Qty

eqQty : Qty → Qty → Bool
eqQty affine affine = true
eqQty reuse  reuse  = true
eqQty erased erased = true
eqQty _      _      = false

showQty : Qty → String
showQty affine = "₁"
showQty reuse  = "+"
showQty erased = "-"

------------------------------------------------------------------------
-- Modes m ∈ {run, spec, evid}
-- A spec never becomes evidence; evidence never becomes a run.
------------------------------------------------------------------------

data Mode : Set where
  run  : Mode
  spec : Mode
  evid : Mode

eqMode : Mode → Mode → Bool
eqMode run  run  = true
eqMode spec spec = true
eqMode evid evid = true
eqMode _    _    = false

showMode : Mode → String
showMode run  = "run"
showMode spec = "spec"
showMode evid = "evidence"

------------------------------------------------------------------------
-- Run usage of one binder.
------------------------------------------------------------------------

data Use : Set where
  U0 : Use   -- unused
  U1 : Use   -- used once
  Uω : Use   -- reusable (+)

eqUse : Use → Use → Bool
eqUse U0 U0 = true
eqUse U1 U1 = true
eqUse Uω Uω = true
eqUse _  _  = false

------------------------------------------------------------------------
-- Decision-procedure result. Errors are strings so the Elixir mirror
-- can reuse the same messages later.
------------------------------------------------------------------------

data Result (A : Set) : Set where
  ok   : A → Result A
  fail : String → Result A

return : ∀ {A : Set} → A → Result A
return = ok

_>>=_ : ∀ {A B : Set} → Result A → (A → Result B) → Result B
ok x   >>= f = f x
fail e >>= _ = fail e

_>>_ : ∀ {A B : Set} → Result A → Result B → Result B
a >> b = a >>= λ _ → b

_<$>_ : ∀ {A B : Set} → (A → B) → Result A → Result B
f <$> ok x   = ok (f x)
_ <$> fail e = fail e

_⊛_ : ∀ {A B : Set} → Result (A → B) → Result A → Result B
ok f   ⊛ ok x   = ok (f x)
fail e ⊛ _      = fail e
_      ⊛ fail e = fail e

-- The second result, when the first fails.
_orElse_ : ∀ {A : Set} → Result A → Result A → Result A
ok x   orElse _ = ok x
fail _ orElse r = r

infixl 1 _>>=_ _>>_ _orElse_
infixl 4 _<$>_ _⊛_

fromBool : String → Bool → Result ⊤
fromBool _ true  = ok tt
fromBool e false = fail e

tag : ∀ {A} → String → Result A → Result A
tag s (fail e) = fail (s ++ ": " ++ e)
tag _ r        = r

guard : String → Bool → Result ⊤
guard = fromBool

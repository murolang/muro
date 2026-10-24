------------------------------------------------------------------------
-- Always P s unfolds to P (head s) × Always P (tail s).
-- The recursive component is a proof about the tail, not Unit.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.ExampleAlways where

open import Data.List.Base using (List; []; _∷_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Check

const0≡0 : Tm 0
const0≡0 = lam affine nat (idt nat ze ze)

zerosTy : Tm 0
zerosTy = stream nat

zerosTm : Tm 0
zerosTm = unf ze (lam affine nat (pair ze ze))

-- Always (λ _ → {0 ≡ 0}) zeros
alwaysTy : Tm 0
alwaysTy = always nat const0≡0 (def 0)

-- unfold tt (λ (_ : Unit) → (refl, zeros-always-zero))
-- The tail of zeros is zeros, so the self-call is the tail proof.
alwaysTm : Tm 0
alwaysTm = unf one (lam affine unit (pair rfl (def 1)))

alwaysBook : Sig
alwaysBook = fromDefs (
  mkDef "zeros"             run  zerosTy  zerosTm  ∷
  mkDef "zeros-always-zero" evid alwaysTy alwaysTm ∷
  [])

always-checks : checkSig! alwaysBook ≡ ok tt
always-checks = refl

-- Unguarded evidence: self-call is not an unfold.
badAlways : Sig
badAlways = fromDefs (
  mkDef "zeros" run (stream nat) zerosTm ∷
  mkDef "bad" evid (always nat const0≡0 (def 0)) (def 1) ∷
  [])

------------------------------------------------------------------------
-- ν example: zeros : Stream Nat, head zeros ≡ 0.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.ExampleStream where

open import Data.List.Base using (List; []; _∷_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Check

zerosTy : Tm 0
zerosTy = stream nat

-- unfold 0 (λ (_ : Nat) → (0, 0))
zerosTm : Tm 0
zerosTm = unf ze (lam affine nat (pair ze ze))

headZerosTy : Tm 0
headZerosTy = idt nat (fstTm (ucons (def 0))) ze

headZerosTm : Tm 0
headZerosTm = rfl

zerosBook : Sig
zerosBook = fromDefs (
  mkDef "zeros"      run  zerosTy     zerosTm     ∷
  mkDef "head-zeros" evid headZerosTy headZerosTm ∷
  [])

zeros-checks : checkSig! zerosBook ≡ ok tt
zeros-checks = refl

-- Direct self-call is not an unfold.
badLoop : Sig
badLoop = fromDefs (mkDef "bad" run (stream nat) (def 0) ∷ [])

-- unfold whose λ-body is not a pair.
badUnfold : Sig
badUnfold =
  fromDefs (mkDef "bad" run (stream nat) (unf ze (lam affine nat (def 0))) ∷ [])

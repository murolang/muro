------------------------------------------------------------------------
-- Multiplicity on an affine arrow. `%0` may drop the binder. `%1`
-- must use it once. Both marks are the affine quantity. Neither is
-- a constructor of Qty, and neither is added to Tm or PTm.
--
-- An unmarked binder is `%0`. `checkArrow` is `checkBound` for that
-- quantity, then `checkMark`. For `%0` the second check accepts
-- every use, so an existing binder is unchanged. Spec forgets uses,
-- so a drop there is accepted. A second use is still the affine
-- refusal.
--
-- The Elixir checker follows `checkArrow` when a binder is written
-- `%1`. The λ mark and the Π mark must be the same mark.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Arrow where

open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (Mode; run; spec; evid; Qty; affine; Use; U0; U1; Uω; Result; ok; fail; _>>=_)
open import Muro.Env using (checkBound)

data Mark : Set where
  m0 : Mark
  m1 : Mark

-- Both marks sit on the affine arrow.
qty : Mark → Qty
qty m0 = affine
qty m1 = affine

same-qty : qty m0 ≡ qty m1
same-qty = refl

qty-affine : qty m1 ≡ affine
qty-affine = refl

-- `%0` accepts every use. `%1` refuses a drop in run and evidence.
checkMark : Mode → Mark → Use → Result ⊤
checkMark _    m0 _  = ok tt
checkMark run  m1 U0 = fail "linear variable unused"
checkMark evid m1 U0 = fail "linear variable unused"
checkMark _    m1 _  = ok tt

m0-silent : ∀ m u → checkMark m m0 u ≡ ok tt
m0-silent _ _ = refl

m1-once : checkMark run m1 U1 ≡ ok tt
m1-once = refl

m1-drop : checkMark run m1 U0 ≡ fail "linear variable unused"
m1-drop = refl

m1-evid-drop : checkMark evid m1 U0 ≡ fail "linear variable unused"
m1-evid-drop = refl

m1-spec-drop : checkMark spec m1 U0 ≡ ok tt
m1-spec-drop = refl

checkArrow : Mode → Mark → Use → Result ⊤
checkArrow m k u = checkBound m (qty k) u >>= λ _ → checkMark m k u

-- An unmarked binder is `%0`, and its check is the affine one.
arrow-m0 : ∀ m u → checkArrow m m0 u ≡ checkBound m affine u
arrow-m0 run  U0 = refl
arrow-m0 run  U1 = refl
arrow-m0 run  Uω = refl
arrow-m0 spec U0 = refl
arrow-m0 spec U1 = refl
arrow-m0 spec Uω = refl
arrow-m0 evid U0 = refl
arrow-m0 evid U1 = refl
arrow-m0 evid Uω = refl

arrow-m1-once : checkArrow run m1 U1 ≡ ok tt
arrow-m1-once = refl

arrow-m1-drop : checkArrow run m1 U0 ≡ fail "linear variable unused"
arrow-m1-drop = refl

arrow-m1-many : checkArrow run m1 Uω ≡ fail "affine variable used as reusable"
arrow-m1-many = refl

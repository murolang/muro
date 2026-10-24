------------------------------------------------------------------------
-- σ ~ τ unfolds to {head σ ≡ head τ} × (tail σ ~ tail τ).
-- The recursive component is a proof about the tails.
--
-- J.J.M.M. Rutten, Elements of Stream Calculus (An Extensive Exercise
-- in Coinduction), ENTCS 45 (2001), Theorem 2.1.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.ExampleBisim where

open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Check

zerosTy : Tm 0
zerosTy = stream nat

zerosTm : Tm 0
zerosTm = unf ze (lam affine nat (pair ze ze))

zerosBisimTy : Tm 0
zerosBisimTy = bisim nat (def 0) (def 1)

zerosBisimTm : Tm 0
zerosBisimTm = unf one (lam affine unit (pair rfl (def 2)))

zerosBook : Sig
zerosBook = fromDefs (
  mkDef "zeros"       run  zerosTy      zerosTm      ∷
  mkDef "zeros'"      run  zerosTy      zerosTm      ∷
  mkDef "zeros-bisim" evid zerosBisimTy zerosBisimTm ∷
  [])

zeros-bisim-checks : checkSig! zerosBook ≡ ok tt
zeros-bisim-checks = refl

natsFromTy : Tm 0
natsFromTy = pi affine nat (stream nat)

natsFromTm : Tm 0
natsFromTm =
  lam affine nat
    (unf (var zero) (lam reuse nat (pair (var zero) (su (var zero)))))

natsTailTy : Tm 0
natsTailTy =
  pi affine nat
    (bisim nat
      (sndTm (ucons (app (def 0) (var zero))))
      (app (def 0) (su (var zero))))

natsTailTm : Tm 0
natsTailTm =
  lam affine nat
    (unf one
      (lam affine unit
        (pair rfl (app (def 1) (su (var (suc zero)))))))

natsBook : Sig
natsBook = fromDefs (
  mkDef "natsFrom"        run  natsFromTy natsFromTm ∷
  mkDef "nats-tail-bisim" evid natsTailTy natsTailTm ∷
  [])

nats-tail-bisim-checks : checkSig! natsBook ≡ ok tt
nats-tail-bisim-checks = refl

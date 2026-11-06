------------------------------------------------------------------------
-- The v1 example: IsEven, half, plus, plus_suc, half_ok.
--
--   IsEven : Nat → Type
--   half   : Nat → Nat
--   half_ok : (n : Nat) → IsEven n → half n + half n ≡ n
--
-- Proofs are ordinary terms: match + refl + rewrite with motive.
-- Binders are de Bruijn: the innermost variable is var zero.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Example where

open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Check

-- plus : Nat → Nat → Nat
plusTy : Tm 0
plusTy =
  pi affine nat
    (pi affine nat
      nat)

plusTm : Tm 0
plusTm =
  lam affine nat
    (lam affine nat
      (mNat (var (suc zero)) nat
        (var zero)
        (su (app (app (def plusId) (var zero)) (var (suc zero))))))

-- IsEven : Nat → Type
isEvenTy : Tm 0
isEvenTy =
  pi affine nat
    typ

isEvenTm : Tm 0
isEvenTm =
  lam affine nat
    (mNat (var zero) typ
      unit
      (mNat (var zero) typ
        empty
        (app (def isEvenId) (var zero))))

-- half : Nat → Nat
halfTy : Tm 0
halfTy =
  pi affine nat
    nat

halfTm : Tm 0
halfTm =
  lam affine nat
    (mNat (var zero) nat
      ze
      (mNat (var zero) nat
        ze
        (su (app (def halfId) (var zero)))))

-- plus_suc : (n m : Nat) → plus n (suc m) ≡ suc (plus n m)
plusSucTy : Tm 0
plusSucTy =
  pi affine nat
    (pi affine nat
      (idt nat (app (app (def plusId) (var (suc zero))) (su (var zero))) (su (app (app (def plusId) (var (suc zero))) (var zero)))))

plusSucTm : Tm 0
plusSucTm =
  lam affine nat
    (lam affine nat
      (mNat (var (suc zero)) (idt nat (app (app (def plusId) (var zero)) (su (var (suc zero)))) (su (app (app (def plusId) (var zero)) (var (suc zero)))))
        rfl
        (rwt (app (app (def plusSucId) (var zero)) (var (suc zero))) (idt nat (su (var zero)) (su (su (app (app (def plusId) (var (suc zero))) (var (suc (suc zero)))))))
          rfl)))

-- half_ok : (n : Nat) → IsEven n → half n + half n ≡ n
--
-- Match n. Zero is refl. A successor matches again: the odd case is
-- empty, and the even case rewrites by plus_suc, then by half_ok.
halfOkTy : Tm 0
halfOkTy =
  pi affine nat
    (pi affine (app (def isEvenId) (var zero))
      (idt nat (app (app (def plusId) (app (def halfId) (var (suc zero)))) (app (def halfId) (var (suc zero)))) (var (suc zero))))

halfOkTm : Tm 0
halfOkTm =
  lam affine nat
    (lam affine (app (def isEvenId) (var zero))
      (app (mNat (var (suc zero)) (pi affine (app (def isEvenId) (var zero))
        (idt nat (app (app (def plusId) (app (def halfId) (var (suc zero)))) (app (def halfId) (var (suc zero)))) (var (suc zero))))
        (lam affine (app (def isEvenId) ze)
          rfl)
        (mNat (var zero) (pi affine (app (def isEvenId) (su (var zero)))
          (idt nat (app (app (def plusId) (app (def halfId) (su (var (suc zero))))) (app (def halfId) (su (var (suc zero))))) (su (var (suc zero)))))
          (lam affine (app (def isEvenId) (su ze))
            (mEmp (var zero) (idt nat (app (app (def plusId) (app (def halfId) (su ze))) (app (def halfId) (su ze))) (su ze))))
          (lam affine (app (def isEvenId) (su (su (var zero))))
            (rwt (app (app (def plusSucId) (app (def halfId) (var (suc zero)))) (app (def halfId) (var (suc zero)))) (idt nat (su (var zero)) (su (su (var (suc (suc zero))))))
              (rwt (app (app (def halfOkId) (var (suc zero))) (var zero)) (idt nat (su (su (var zero))) (su (su (var (suc (suc zero))))))
                rfl))))) (var zero)))

book : Sig
book = fromDefs (
  mkDef "plus"     run  plusTy    plusTm    ∷
  mkDef "IsEven"   spec isEvenTy  isEvenTm  ∷
  mkDef "half"     run  halfTy    halfTm    ∷
  mkDef "plus_suc" evid plusSucTy plusSucTm ∷
  mkDef "half_ok"  evid halfOkTy  halfOkTm  ∷
  [])

-- Closed computation: plus (half 2) (half 2) ≡ 2.
t2 : Tm 0
t2 = su (su ze)

plus-half-2 : Tm 0
plus-half-2 =
  app (app (def plusId) (app (def halfId) t2))
      (app (def halfId) t2)

plus-half-2-conv : conv fuel book plus-half-2 t2 ≡ ok tt
plus-half-2-conv = refl

half_ok-checks : checkSig! book ≡ ok tt
half_ok-checks = refl

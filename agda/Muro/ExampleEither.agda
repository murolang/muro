------------------------------------------------------------------------
-- Either / Dec / evenDec.
-- Dec P = P ⊎ (P → Empty). A decision, not LEM.
-- Binders are de Bruijn: the innermost variable is var zero.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.ExampleEither where

open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Check

-- IsEven is def 0, Dec is def 1, evenDec is def 2.

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
        (app (def 0) (var zero))))

leftTy : Tm 0
leftTy =
  pi affine typ
    (pi affine typ
      (pi affine (var (suc zero))
        (app (app (dty 0) (var (suc (suc zero)))) (var (suc zero)))))

rightTy : Tm 0
rightTy =
  pi affine typ
    (pi affine typ
      (pi affine (var zero)
        (app (app (dty 0) (var (suc (suc zero)))) (var (suc zero)))))

decTy : Tm 0
decTy =
  pi affine typ
    typ

decTm : Tm 0
decTm =
  lam affine typ
    (app (app (dty 0) (var zero)) (pi affine (var zero)
      empty))

evenDecTy : Tm 0
evenDecTy =
  pi affine nat
    (app (def 1) (app (def 0) (var zero)))

evenDecTm : Tm 0
evenDecTm =
  lam affine nat
    (mNat (var zero) (app (def 1) (app (def 0) (var zero)))
      (app (ctor 0 0) one)
      (mNat (var zero) (app (def 1) (app (def 0) (su (var zero))))
        (app (ctor 0 1) (lam affine (app (def 0) (su ze))
          (mEmp (var zero) empty)))
        (mData (app (def 2) (var zero)) (app (def 1) (app (def 0) (su (su (var (suc zero)))))) ((lam affine (app (def 0) (var zero))
          (app (ctor 0 0) (var zero))) ∷ (lam affine (pi affine (app (def 0) (var zero))
          empty)
          (app (ctor 0 1) (var zero))) ∷ []))))

eitherDecl : DataDecl
eitherDecl =
  mkData "Either" (affine ∷ affine ∷ []) []
    ( mkCtor "left"  leftTy  ∷
      mkCtor "right" rightTy ∷
      [] )

evenDecBook : Sig
evenDecBook =
  mkSig (eitherDecl ∷ [])
    ( mkDef "IsEven"  spec isEvenTy  isEvenTm  ∷
      mkDef "Dec"     spec decTy     decTm     ∷
      mkDef "evenDec" evid evenDecTy evenDecTm ∷
      [] )

evenDec-checks : checkSig! evenDecBook ≡ ok tt
evenDec-checks = refl

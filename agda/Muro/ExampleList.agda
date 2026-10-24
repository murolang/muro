------------------------------------------------------------------------
-- List A, length, and length (cons 1 (cons 1 nil)) ≡ 2.
-- Binders are de Bruijn: the innermost variable is var zero.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.ExampleList where

open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Check

nilTy : Tm 0
nilTy =
  pi affine typ
    (app (dty 0) (var zero))

consTy : Tm 0
consTy =
  pi affine typ
    (pi affine (var zero)
      (pi affine (app (dty 0) (var (suc zero)))
        (app (dty 0) (var (suc (suc zero))))))

lengthTy : Tm 0
lengthTy =
  pi erased typ
    (pi affine (app (dty 0) (var zero))
      nat)

lengthTm : Tm 0
lengthTm =
  lam erased typ
    (lam affine (app (dty 0) (var zero))
      (mData (var zero) nat (ze ∷ (lam affine (var (suc zero))
        (lam affine (app (dty 0) (var (suc (suc zero))))
          (su (app (app (def 0) (var (suc (suc (suc zero))))) (var zero))))) ∷ [])))

ones2Ty : Tm 0
ones2Ty = app (dty 0) nat

ones2Tm : Tm 0
ones2Tm =
  app (app (ctor 0 1) (su ze)) (app (app (ctor 0 1) (su ze)) (ctor 0 0))

lenOkTy : Tm 0
lenOkTy = idt nat (app (app (def 0) nat) (def 1)) (su (su ze))

lenOkTm : Tm 0
lenOkTm = rfl

listDecl : DataDecl
listDecl =
  mkData "List" (affine ∷ []) []
    ( mkCtor "nil"  nilTy  ∷
      mkCtor "cons" consTy ∷
      [] )

listBook : Sig
listBook =
  mkSig (listDecl ∷ [])
    ( mkDef "length"       run  lengthTy lengthTm ∷
      mkDef "ones2"        run  ones2Ty  ones2Tm  ∷
      mkDef "length-ones2" evid lenOkTy  lenOkTm  ∷
      [] )

length-ones2-checks : checkSig! listBook ≡ ok tt
length-ones2-checks = refl

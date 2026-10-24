------------------------------------------------------------------------
-- I64 / Tensor I64 n wrappers. Kernel ≡ on F32 is refused.
-- Binders are de Bruijn: the innermost variable is var zero.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.ExampleNx where

open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Check

addITy : Tm 0
addITy =
  pi affine i64
    (pi affine i64
      i64)

addITm : Tm 0
addITm =
  lam affine i64
    (lam affine i64
      (addi (var (suc zero)) (var zero)))

addTTy : Tm 0
addTTy =
  pi erased i64
    (pi reuse (tensor i64 (var zero))
      (tensor i64 (var (suc zero))))

addTTm : Tm 0
addTTm =
  lam erased i64
    (lam reuse (tensor i64 (var zero))
      (addt (var zero) (var zero)))

t1Ty : Tm 0
t1Ty = tensor i64 (toi64 (su (su ze)))

t1Tm : Tm 0
t1Tm = packi (toi64 (su ze)) (toi64 (su (su ze)))

doubledTy : Tm 0
doubledTy = tensor i64 (toi64 (su (su ze)))

doubledTm : Tm 0
doubledTm = app (app (def 1) (toi64 (su (su ze)))) (def 2)

nxBook : Sig
nxBook =
  fromDefs
    ( mkDef "addI"    run addITy    addITm    ∷
      mkDef "addT"    run addTTy    addTTm    ∷
      mkDef "t1"      run t1Ty      t1Tm      ∷
      mkDef "doubled" run doubledTy doubledTm ∷
      [] )

nx-checks : checkSig! nxBook ≡ ok tt
nx-checks = refl

-- {x ≡ y : F32} is not a type.
badFloatTy : Tm 0
badFloatTy =
  pi affine f32ty
    (pi affine f32ty
      (idt f32ty (var (suc zero)) (var zero)))

badFloatEq : Sig
badFloatEq =
  fromDefs (mkDef "bad" spec badFloatTy rfl ∷ [])

data IsFail {A : Set} : Result A → Set where
  is-fail : (e : String) → IsFail (fail e)

float-eq-rejected : IsFail (checkSig! badFloatEq)
float-eq-rejected = is-fail _

-- {x ≡ y : Tensor F32 n} is not a type.
badTenTy : Tm 0
badTenTy =
  pi affine i64
    (pi affine (tensor f32ty (var zero))
      (pi affine (tensor f32ty (var (suc zero)))
        (idt (tensor f32ty (var (suc (suc zero)))) (var (suc zero)) (var zero))))

badTenEq : Sig
badTenEq =
  fromDefs (mkDef "badT" spec badTenTy rfl ∷ [])

tensor-f32-eq-rejected : IsFail (checkSig! badTenEq)
tensor-f32-eq-rejected = is-fail _

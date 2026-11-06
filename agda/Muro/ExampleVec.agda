------------------------------------------------------------------------
-- Fin n, Vec A n, vhead and vtail by a motive that computes from the
-- index, lookup, and lookup of fzero on a singleton.
-- Binders are de Bruijn: the innermost variable is var zero.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.ExampleVec where

open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Check

-- Fin is dty 0, Vec is dty 1.
-- pred is def 0, vhead is def 1, vtail is def 2, lookup is def 3.

fzeroTy : Tm 0
fzeroTy =
  pi affine nat
    (app (dty 0) (su (var zero)))

fsucTy : Tm 0
fsucTy =
  pi affine nat
    (pi affine (app (dty 0) (var zero))
      (app (dty 0) (su (var (suc zero)))))

vnilTy : Tm 0
vnilTy =
  pi affine typ
    (app (app (dty 1) (var zero)) ze)

vconsTy : Tm 0
vconsTy =
  pi affine typ
    (pi affine nat
      (pi affine (var (suc zero))
        (pi affine (app (app (dty 1) (var (suc (suc zero)))) (var (suc zero)))
          (app (app (dty 1) (var (suc (suc (suc zero))))) (su (var (suc (suc zero))))))))

-- pred : Nat → Nat, read by vtail's motive.
predTy : Tm 0
predTy =
  pi affine nat
    nat

predTm : Tm 0
predTm =
  lam affine nat
    (mNat (var zero) nat
      ze
      (var zero))

-- vhead, vtail : (A : Type) → (m : Nat) → Vec A (su m) → …
--
-- The vcons branch is typed at its own index (su p). vtail's motive
-- Vec A (pred k) is Vec A p there, the type of as, and Vec A m at the
-- scrutinee's index su m. vnil clashes with su m and is skipped.
vheadTy : Tm 0
vheadTy =
  pi erased typ
    (pi erased nat
      (pi affine (app (app (dty 1) (var (suc zero))) (su (var zero)))
        (var (suc (suc zero)))))

vheadTm : Tm 0
vheadTm =
  lam erased typ
    (lam erased nat
      (lam affine (app (app (dty 1) (var (suc zero))) (su (var zero)))
        (mData (var zero) (lam affine (app (app (dty 1) (var (suc (suc (suc zero))))) (var zero))
          (var (suc (suc (suc (suc zero)))))) (ze ∷ (lam affine nat
          (lam affine (var (suc (suc (suc zero))))
            (lam affine (app (app (dty 1) (var (suc (suc (suc (suc zero)))))) (var (suc zero)))
              (var (suc zero))))) ∷ []))))

vtailTy : Tm 0
vtailTy =
  pi erased typ
    (pi erased nat
      (pi affine (app (app (dty 1) (var (suc zero))) (su (var zero)))
        (app (app (dty 1) (var (suc (suc zero)))) (var (suc zero)))))

vtailTm : Tm 0
vtailTm =
  lam erased typ
    (lam erased nat
      (lam affine (app (app (dty 1) (var (suc zero))) (su (var zero)))
        (mData (var zero) (lam affine (app (app (dty 1) (var (suc (suc (suc zero))))) (var zero))
          (app (app (dty 1) (var (suc (suc (suc (suc zero)))))) (app (def 0) (var (suc zero))))) (ze ∷ (lam affine nat
          (lam affine (var (suc (suc (suc zero))))
            (lam affine (app (app (dty 1) (var (suc (suc (suc (suc zero)))))) (var (suc zero)))
              (var zero)))) ∷ []))))

-- lookup : (A : Type) → (n : Nat) → Fin n → Vec A n → A
--
-- The match on i : Fin n is typed at each constructor's own index
-- (su m), and returns a function of Vec A (su m): vhead for fzero, and
-- for fsuc m j the recursive call on j and vtail.
lookupTy : Tm 0
lookupTy =
  pi erased typ
    (pi erased nat
      (pi affine (app (dty 0) (var zero))
        (pi affine (app (app (dty 1) (var (suc (suc zero)))) (var (suc zero)))
          (var (suc (suc (suc zero)))))))

lookupTm : Tm 0
lookupTm =
  lam erased typ
    (lam erased nat
      (lam affine (app (dty 0) (var zero))
        (lam affine (app (app (dty 1) (var (suc (suc zero)))) (var (suc zero)))
          (app (mData (var (suc zero)) (lam affine (app (dty 0) (var zero))
            (pi affine (app (app (dty 1) (var (suc (suc (suc (suc (suc zero))))))) (var (suc zero)))
              (var (suc (suc (suc (suc (suc (suc zero))))))))) ((lam affine nat
            (lam affine (app (app (dty 1) (var (suc (suc (suc (suc zero)))))) (su (var zero)))
              (app (app (app (def 1) (var (suc (suc (suc (suc (suc zero))))))) (var (suc zero))) (var zero)))) ∷ (lam affine nat
            (lam affine (app (dty 0) (var zero))
              (lam affine (app (app (dty 1) (var (suc (suc (suc (suc (suc zero))))))) (su (var (suc zero))))
                (app (app (app (app (def 3) (var (suc (suc (suc (suc (suc (suc zero)))))))) (var (suc (suc zero)))) (var (suc zero))) (app (app (app (def 2) (var (suc (suc (suc (suc (suc (suc zero)))))))) (var (suc (suc zero)))) (var zero)))))) ∷ [])) (var zero)))))

ones1Ty : Tm 0
ones1Ty = app (app (dty 1) nat) (su ze)

ones1Tm : Tm 0
ones1Tm = app (app (app (ctor 1 1) ze) (su ze)) (ctor 1 0)

lookOkTy : Tm 0
lookOkTy =
  idt nat
    (app (app (app (app (def 3) nat) (su ze)) (app (ctor 0 0) ze)) (def 4))
    (su ze)

lookOkTm : Tm 0
lookOkTm = rfl

finDecl : DataDecl
finDecl =
  mkData "Fin" [] ((affine , nat) ∷ [])
    ( mkCtor "fzero" fzeroTy ∷
      mkCtor "fsuc"  fsucTy  ∷
      [] )

vecDecl : DataDecl
vecDecl =
  mkData "Vec" (affine ∷ []) ((affine , nat) ∷ [])
    ( mkCtor "vnil"  vnilTy  ∷
      mkCtor "vcons" vconsTy ∷
      [] )

vecBook : Sig
vecBook =
  mkSig (finDecl ∷ vecDecl ∷ [])
    ( mkDef "pred"      run  predTy   predTm   ∷
      mkDef "vhead"     run  vheadTy  vheadTm  ∷
      mkDef "vtail"     run  vtailTy  vtailTm  ∷
      mkDef "lookup"    run  lookupTy lookupTm ∷
      mkDef "ones1"     run  ones1Ty  ones1Tm  ∷
      mkDef "lookup-ok" evid lookOkTy lookOkTm ∷
      [] )

lookup-ok-checks : checkSig! vecBook ≡ ok tt
lookup-ok-checks = refl

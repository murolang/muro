------------------------------------------------------------------------
-- List A, length, and length (cons 1 (cons 1 nil)) ≡ 2.
-- Binders are de Bruijn: the innermost variable is var zero.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.ExampleList where

open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using () renaming (zero to nzero; suc to nsuc)
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
      (mData (var zero) nat (nzero ∷ nsuc (nsuc nzero) ∷ []) (ze ∷ (lam affine (var (suc zero))
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

------------------------------------------------------------------------
-- varUses on an mData arm does not count field-binder types, matching
-- Elixir `var_uses(x + ar, b, 0)`. A is var zero at this scope:
-- the scrutinee `nil A` mentions it once; the cons field types mention
-- it again; the arm bodies do not. The count is 1, not 2.
------------------------------------------------------------------------

nilA : Tm 1
nilA = app (ctor 0 0) (var zero)

consArm₀ : Tm 1
consArm₀ =
  lam affine (var zero)
    (lam affine (app (dty 0) (var (suc zero)))
      ze)

listMatchA : Tm 1
listMatchA = mData nilA nat (nzero ∷ nsuc (nsuc nzero) ∷ []) (ze ∷ consArm₀ ∷ [])

field-types-not-counted : varUses 0 listMatchA 0 ≡ 1
field-types-not-counted = refl

-- The cons body mentions A once; that use is counted.
consArm₁ : Tm 1
consArm₁ =
  lam affine (var zero)
    (lam affine (app (dty 0) (var (suc zero)))
      (var (suc (suc zero))))

listMatchA-body : Tm 1
listMatchA-body = mData nilA typ (nzero ∷ nsuc (nsuc nzero) ∷ []) (ze ∷ consArm₁ ∷ [])

field-body-is-counted : varUses 0 listMatchA-body 0 ≡ 2
field-body-is-counted = refl

-- The nil arm's constructor arity is 0, so a body that starts with λ
-- is not a field binder: a mention of A in that λ's domain is counted.
-- The scrutinee mentions A once, the domain once, and cap 1 1 ≡ 2.
-- Skipping every leading λ would skip the domain and leave the count at 1.
nilArmBodyLam : Tm 1
nilArmBodyLam = lam affine (var zero) ze

listMatchBodyLam : Tm 1
listMatchBodyLam = mData nilA nat (nzero ∷ nsuc (nsuc nzero) ∷ []) (nilArmBodyLam ∷ consArm₀ ∷ [])

body-lam-domain-counted : varUses 0 listMatchBodyLam 0 ≡ 2
body-lam-domain-counted = refl

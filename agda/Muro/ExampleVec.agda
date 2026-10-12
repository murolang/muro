------------------------------------------------------------------------
-- Fin n, Vec A n, vhead and vtail by a motive that computes from the
-- index, lookup, and lookup of fzero on a singleton.
------------------------------------------------------------------------

module Muro.ExampleVec where

open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Unembed
open import Muro.Check

-- Fin is dty 0, Vec is dty 1.

fzeroTy : ∀ {V} → PTm V
fzeroTy = pi affine nat (λ n → app (dty 0) (su (var n)))

fsucTy : ∀ {V} → PTm V
fsucTy =
  pi affine nat (λ n →
  pi affine (app (dty 0) (var n)) (λ _ →
    app (dty 0) (su (var n))))

vnilTy : ∀ {V} → PTm V
vnilTy = pi affine typ (λ A → app (app (dty 1) (var A)) ze)

vconsTy : ∀ {V} → PTm V
vconsTy =
  pi affine typ (λ A →
  pi affine nat (λ n →
  pi affine (var A) (λ _ →
  pi affine (app (app (dty 1) (var A)) (var n)) (λ _ →
    app (app (dty 1) (var A)) (su (var n))))))

-- pred : Nat → Nat, read by vtail's motive.
predTy : ∀ {V} → PTm V
predTy = pi affine nat (λ _ → nat)

predTm : ∀ {V} → PTm V
predTm = lam affine nat (λ n → mNat (var n) (λ _ → nat) ze (λ m → var m))

-- vhead, vtail : (A : Type) → (m : Nat) → Vec A (su m) → …
--
-- The vcons branch is typed at its own index (su p). vtail's motive
-- Vec A (pred k) is Vec A p there, the type of as, and Vec A m at the
-- scrutinee's index su m. vnil clashes with su m and is skipped.
vheadTy : ∀ {V} → PTm V
vheadTy =
  pi erased typ (λ A →
  pi erased nat (λ m →
  pi affine (app (app (dty 1) (var A)) (su (var m))) (λ _ →
    var A)))

vheadTm : ∀ {V} → PTm V
vheadTm =
  lam erased typ (λ A →
  lam erased nat (λ m →
  lam affine (app (app (dty 1) (var A)) (su (var m))) (λ ys →
    mData (var ys)
      (λ k → lam affine (app (app (dty 1) (var A)) (var k)) (λ _ → var A))
      ( ze ∷
        lam affine nat (λ p →
        lam affine (var A) (λ a →
        lam affine (app (app (dty 1) (var A)) (var p)) (λ _ →
          var a))) ∷
        [] ))))

vtailTy : ∀ {V} → PTm V
vtailTy =
  pi erased typ (λ A →
  pi erased nat (λ m →
  pi affine (app (app (dty 1) (var A)) (su (var m))) (λ _ →
    app (app (dty 1) (var A)) (var m))))

vtailTm : ∀ {V} → PTm V
vtailTm =
  lam erased typ (λ A →
  lam erased nat (λ m →
  lam affine (app (app (dty 1) (var A)) (su (var m))) (λ ys →
    mData (var ys)
      (λ k →
        lam affine (app (app (dty 1) (var A)) (var k)) (λ _ →
          app (app (dty 1) (var A)) (app (def 0) (var k))))
      ( ze ∷
        lam affine nat (λ p →
        lam affine (var A) (λ _ →
        lam affine (app (app (dty 1) (var A)) (var p)) (λ as →
          var as))) ∷
        [] ))))

-- lookup : (A : Type) → (n : Nat) → Fin n → Vec A n → A
--
-- The match on i : Fin n is typed at each constructor's own index
-- (su m), and returns a function of Vec A (su m): vhead for fzero, and
-- for fsuc m j the recursive call on j and vtail.
lookupTy : ∀ {V} → PTm V
lookupTy =
  pi erased typ (λ A →
  pi erased nat (λ n →
  pi affine (app (dty 0) (var n)) (λ _ →
  pi affine (app (app (dty 1) (var A)) (var n)) (λ _ →
    var A))))

lookupTm : ∀ {V} → PTm V
lookupTm =
  lam erased typ (λ A →
  lam erased nat (λ n →
  lam affine (app (dty 0) (var n)) (λ i →
  lam affine (app (app (dty 1) (var A)) (var n)) (λ xs →
    app
      (mData (var i)
        (λ k →
          lam affine (app (dty 0) (var k)) (λ _ →
            pi affine (app (app (dty 1) (var A)) (var k)) (λ _ → var A)))
        ( lam affine nat (λ m →
            lam affine (app (app (dty 1) (var A)) (su (var m))) (λ ys →
              app (app (app (def 1) (var A)) (var m)) (var ys))) ∷
          lam affine nat (λ m →
          lam affine (app (dty 0) (var m)) (λ j →
            lam affine (app (app (dty 1) (var A)) (su (var m))) (λ ys →
              app (app (app (app (def 3) (var A)) (var m)) (var j))
                (app (app (app (def 2) (var A)) (var m)) (var ys))))) ∷
          [] ))
      (var xs)))))

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

data IsOk {A : Set} : Result A → Set where
  is-ok : (x : A) → IsOk (ok x)

out : ∀ {A} {r : Result A} → IsOk r → A
out (is-ok x) = x

fzeroTy-ok  : IsOk (unembed∀ fzeroTy)
fsucTy-ok   : IsOk (unembed∀ fsucTy)
vnilTy-ok   : IsOk (unembed∀ vnilTy)
vconsTy-ok  : IsOk (unembed∀ vconsTy)
predTy-ok   : IsOk (unembed∀ predTy)
predTm-ok   : IsOk (unembed∀ predTm)
vheadTy-ok  : IsOk (unembed∀ vheadTy)
vheadTm-ok  : IsOk (unembed∀ vheadTm)
vtailTy-ok  : IsOk (unembed∀ vtailTy)
vtailTm-ok  : IsOk (unembed∀ vtailTm)
lookupTy-ok : IsOk (unembed∀ lookupTy)
lookupTm-ok : IsOk (unembed∀ lookupTm)
fzeroTy-ok  = is-ok _
fsucTy-ok   = is-ok _
vnilTy-ok   = is-ok _
vconsTy-ok  = is-ok _
predTy-ok   = is-ok _
predTm-ok   = is-ok _
vheadTy-ok  = is-ok _
vheadTm-ok  = is-ok _
vtailTy-ok  = is-ok _
vtailTm-ok  = is-ok _
lookupTy-ok = is-ok _
lookupTm-ok = is-ok _

finDecl : DataDecl
finDecl =
  mkData "Fin" [] ((affine , nat) ∷ [])
    ( mkCtor "fzero" (out fzeroTy-ok) ∷
      mkCtor "fsuc"  (out fsucTy-ok)  ∷
      [] )

vecDecl : DataDecl
vecDecl =
  mkData "Vec" (affine ∷ []) ((affine , nat) ∷ [])
    ( mkCtor "vnil"  (out vnilTy-ok)  ∷
      mkCtor "vcons" (out vconsTy-ok) ∷
      [] )

vecBook : Sig
vecBook =
  mkSig (finDecl ∷ vecDecl ∷ [])
    ( mkDef "pred"       run  (out predTy-ok)   (out predTm-ok)   ∷
      mkDef "vhead"      run  (out vheadTy-ok)  (out vheadTm-ok)  ∷
      mkDef "vtail"      run  (out vtailTy-ok)  (out vtailTm-ok)  ∷
      mkDef "lookup"     run  (out lookupTy-ok) (out lookupTm-ok) ∷
      mkDef "ones1"      run  ones1Ty           ones1Tm           ∷
      mkDef "lookup-ok"  evid lookOkTy          lookOkTm          ∷
      [] )

lookup-ok-checks : checkSig! vecBook ≡ ok tt
lookup-ok-checks = refl

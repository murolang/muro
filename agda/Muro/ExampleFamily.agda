------------------------------------------------------------------------
-- A declared ν family is a spec definition whose body is ν F, F a
-- λ-telescope over the indices. Here three indices:
--
--   ν Three (f g h : Stream Nat) : Type where
--     uncons : Three f g h → {head f ≡ head g : Nat}
--                            × Three (tail f) (tail g) (tail h)
--
-- An unfold of Three checks the head equation and a proof of Three at
-- the tails. zeros′ is a run Stream that is not an unfold and does not
-- call its own block, so it is productive.
------------------------------------------------------------------------

module Muro.ExampleFamily where

open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Check

headTm tailTm : ∀ {n} → Tm n → Tm n
headTm s = fstTm (ucons s)
tailTm s = sndTm (ucons s)

-- Y is var 3 under the three index binders f (var 2), g (var 1), h (var 0).
threeFam : Tm 1
threeFam =
  lam affine (stream nat) (lam affine (stream nat) (lam affine (stream nat)
    (prod
      (idt nat (headTm (var (suc (suc zero)))) (headTm (var (suc zero))))
      (app (app (app (var (suc (suc (suc zero))))
        (tailTm (var (suc (suc zero)))))
        (tailTm (var (suc zero))))
        (tailTm (var zero))))))

threeKind : Tm 0
threeKind = pi affine (stream nat) (pi affine (stream nat) (pi affine (stream nat) typ))

zerosTm : Tm 0
zerosTm = unf ze (lam affine nat (pair ze ze))

threeZerosTy : Tm 0
threeZerosTy = app (app (app (def 1) (def 0)) (def 0)) (def 0)

threeZerosTm : Tm 0
threeZerosTm = unf one (lam affine unit (pair rfl (def 2)))

familyBook : Sig
familyBook = fromDefs (
  mkDef "zeros"       run  (stream nat) zerosTm      ∷
  mkDef "Three"       spec threeKind    (nu threeFam) ∷
  mkDef "three-zeros" evid threeZerosTy threeZerosTm ∷
  mkDef "zeros′"      run  (stream nat) (def 0)      ∷
  [])

family-checks : checkSig! familyBook ≡ ok tt
family-checks = refl

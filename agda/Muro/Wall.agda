------------------------------------------------------------------------
-- Mode wall: spec ↛ evid ↛ run. Lemmas on inductive ⊢. No axioms.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Wall where

open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans)

open import Muro.Base
open import Muro.Syntax
open import Muro.Env
open import Muro.Judgement

------------------------------------------------------------------------
-- combine at spec forgets uses. It does not produce run uses.
------------------------------------------------------------------------

combine-spec : ∀ {n} (u v : UseVec n) → combine spec u v ≡ ok u0s
combine-spec _ _ = refl

------------------------------------------------------------------------
-- allowedDef: spec and evid never enter run.
------------------------------------------------------------------------

allowedDef-spec-run : allowedDef spec run ≡ false
allowedDef-spec-run = refl

allowedDef-evid-run : allowedDef evid run ≡ false
allowedDef-evid-run = refl

allowedDef-spec-evid : allowedDef spec evid ≡ false
allowedDef-spec-evid = refl

------------------------------------------------------------------------
-- There is no rule
--   promote : ⊢[ spec ] e ⇒ A ⊣ u → ⊢[ evid ] e ⇒ A ⊣ u
-- Spec-only formers are indexed by spec; a run/evid derivation of
-- those terms has no constructor (inversion is λ ()).
------------------------------------------------------------------------

no-run-nat : ∀ {σ n} {Γ : Ctx n} {A u} →
  σ , Γ ⊢[ run ] nat ⇒ A ⊣ u → ⊥
no-run-nat ()

no-evid-nat : ∀ {σ n} {Γ : Ctx n} {A u} →
  σ , Γ ⊢[ evid ] nat ⇒ A ⊣ u → ⊥
no-evid-nat ()

no-run-unit : ∀ {σ n} {Γ : Ctx n} {A u} →
  σ , Γ ⊢[ run ] unit ⇒ A ⊣ u → ⊥
no-run-unit ()

no-evid-unit : ∀ {σ n} {Γ : Ctx n} {A u} →
  σ , Γ ⊢[ evid ] unit ⇒ A ⊣ u → ⊥
no-evid-unit ()

no-run-empty : ∀ {σ n} {Γ : Ctx n} {A u} →
  σ , Γ ⊢[ run ] empty ⇒ A ⊣ u → ⊥
no-run-empty ()

no-evid-empty : ∀ {σ n} {Γ : Ctx n} {A u} →
  σ , Γ ⊢[ evid ] empty ⇒ A ⊣ u → ⊥
no-evid-empty ()

no-run-pi : ∀ {σ n} {Γ : Ctx n} {q A B T u} →
  σ , Γ ⊢[ run ] pi q A B ⇒ T ⊣ u → ⊥
no-run-pi ()

no-evid-pi : ∀ {σ n} {Γ : Ctx n} {q A B T u} →
  σ , Γ ⊢[ evid ] pi q A B ⇒ T ⊣ u → ⊥
no-evid-pi ()

no-run-idt : ∀ {σ n} {Γ : Ctx n} {A a b T u} →
  σ , Γ ⊢[ run ] idt A a b ⇒ T ⊣ u → ⊥
no-run-idt ()

no-evid-idt : ∀ {σ n} {Γ : Ctx n} {A a b T u} →
  σ , Γ ⊢[ evid ] idt A a b ⇒ T ⊣ u → ⊥
no-evid-idt ()

no-run-prod : ∀ {σ n} {Γ : Ctx n} {A B T u} →
  σ , Γ ⊢[ run ] prod A B ⇒ T ⊣ u → ⊥
no-run-prod ()

no-evid-prod : ∀ {σ n} {Γ : Ctx n} {A B T u} →
  σ , Γ ⊢[ evid ] prod A B ⇒ T ⊣ u → ⊥
no-evid-prod ()

no-run-dty : ∀ {σ n} {Γ : Ctx n} {i T u} →
  σ , Γ ⊢[ run ] dty i ⇒ T ⊣ u → ⊥
no-run-dty ()

no-evid-dty : ∀ {σ n} {Γ : Ctx n} {i T u} →
  σ , Γ ⊢[ evid ] dty i ⇒ T ⊣ u → ⊥
no-evid-dty ()

------------------------------------------------------------------------
-- A spec definition is not a run (or evid) term.
------------------------------------------------------------------------

ok-inj : ∀ {A : Set} {x y : A} → ok x ≡ ok y → x ≡ y
ok-inj refl = refl

no-spec-def-in-run : ∀ {σ n} {Γ : Ctx n} {i A u d} →
  lookupDef σ i ≡ ok d →
  Def.dmode d ≡ spec →
  σ , Γ ⊢[ run ] def i ⇒ A ⊣ u → ⊥
no-spec-def-in-run lk refl (⇒-def lk′ allw) with ok-inj (trans (sym lk) lk′)
... | refl = lemma allw
  where
    lemma : allowedDef spec run ≡ true → ⊥
    lemma ()

no-spec-def-in-evid : ∀ {σ n} {Γ : Ctx n} {i A u d} →
  lookupDef σ i ≡ ok d →
  Def.dmode d ≡ spec →
  σ , Γ ⊢[ evid ] def i ⇒ A ⊣ u → ⊥
no-spec-def-in-evid lk refl (⇒-def lk′ allw) with ok-inj (trans (sym lk) lk′)
... | refl = lemma allw
  where
    lemma : allowedDef spec evid ≡ true → ⊥
    lemma ()

no-evid-def-in-run : ∀ {σ n} {Γ : Ctx n} {i A u d} →
  lookupDef σ i ≡ ok d →
  Def.dmode d ≡ evid →
  σ , Γ ⊢[ run ] def i ⇒ A ⊣ u → ⊥
no-evid-def-in-run lk refl (⇒-def lk′ allw) with ok-inj (trans (sym lk) lk′)
... | refl = lemma allw
  where
    lemma : allowedDef evid run ≡ true → ⊥
    lemma ()

------------------------------------------------------------------------
-- Spec derivations carry zero uses.
------------------------------------------------------------------------

spec-⇒-uses : ∀ {σ n} {Γ : Ctx n} {e A u} →
  σ , Γ ⊢[ spec ] e ⇒ A ⊣ u → u ≡ u0s
spec-⇐-uses : ∀ {σ n} {Γ : Ctx n} {e A u} →
  σ , Γ ⊢[ spec ] e ⇐ A ⊣ u → u ≡ u0s
spec-args-uses : ∀ {σ n} {Γ : Ctx n} {T as R u} →
  σ , Γ ⊢[ spec ] T ▹ as ⇝ R ⊣ u → u ≡ u0s
spec-brs-uses : ∀ {σ n} {Γ : Ctx n} {bs di ps is P ci cs u} →
  σ , Γ ⊢[ spec ] bs brs⟨ di , ps , is , P , ci ⟩ cs ⊣ u → u ≡ u0s

spec-⇒-uses ⇒-var-spec = refl
spec-⇒-uses ⇒-ze = refl
spec-⇒-uses (⇒-su D) = spec-⇐-uses D
spec-⇒-uses ⇒-one = refl
spec-⇒-uses ⇒-nat = refl
spec-⇒-uses ⇒-unit = refl
spec-⇒-uses ⇒-empty = refl
spec-⇒-uses (⇒-pi _ _) = refl
spec-⇒-uses (⇒-lam _ _ D _) with spec-⇒-uses D
... | refl = refl
spec-⇒-uses (⇒-app-aff _ _ _ eq) = sym (ok-inj eq)
spec-⇒-uses (⇒-app-era D _ _) = spec-⇒-uses D
spec-⇒-uses (⇒-app-reuse _ _ _ _ eq) = sym (ok-inj eq)
spec-⇒-uses (⇒-app-copy _ _ _ _ eq) = sym (ok-inj eq)
spec-⇒-uses (⇒-idt _ _ _) = refl
spec-⇒-uses (⇒-rwt _ _ _ D) = spec-⇐-uses D
spec-⇒-uses (⇒-mNat _ _ _ _ _ eq) = sym (ok-inj eq)
spec-⇒-uses (⇒-mEmp D _) = spec-⇐-uses D
spec-⇒-uses (⇒-mUnit _ _ _ eq) = sym (ok-inj eq)
spec-⇒-uses (⇒-dty _) = refl
spec-⇒-uses (⇒-mData _ _ _ _ _ _ _ eq) = sym (ok-inj eq)
spec-⇒-uses (⇒-def _ _) = refl
spec-⇒-uses (⇒-ann _ D) = spec-⇐-uses D
spec-⇒-uses (⇒-prod _ _) = refl
spec-⇒-uses (⇒-pair _ _ eq) = sym (ok-inj eq)
spec-⇒-uses (⇒-letp _ _ _ _ _ _ eq) = sym (ok-inj eq)

spec-⇐-uses (⇐-conv D _) = spec-⇒-uses D
spec-⇐-uses (⇐-lam _ _ _ _ D _) with spec-⇐-uses D
... | refl = refl
spec-⇐-uses (⇐-refl _ _) = refl
spec-⇐-uses (⇐-ctor _ _ _ _ _ _ _ Ar _) = spec-args-uses Ar
spec-⇐-uses (⇐-pair _ _ _ eq) = sym (ok-inj eq)
spec-⇐-uses (⇐-letp _ _ _ _ _ eq) = sym (ok-inj eq)

-- combineArg at spec: an erased argument gives u0s outright; the others
-- go through combine spec, which forgets.
spec-args-uses args-[] = refl
spec-args-uses (args-snoc {q = erased} _ _ _ _ eq) = sym (ok-inj eq)
spec-args-uses (args-snoc {q = affine} _ _ _ _ eq) = sym (ok-inj eq)
spec-args-uses (args-snoc {q = reuse}  _ _ _ _ eq) = sym (ok-inj eq)
spec-args-uses (args-snoc-copy _ _ _ _ eq) = sym (ok-inj eq)

spec-brs-uses brs-[] = refl
spec-brs-uses (brs-∷ _ _ _ _) = refl
spec-brs-uses (brs-skip _ _ Bs) = spec-brs-uses Bs

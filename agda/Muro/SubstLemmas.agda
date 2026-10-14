------------------------------------------------------------------------
-- The renaming / substitution algebra of Tm.
--
-- Every lemma is by induction on the term. Binder cases use the lemma
-- on the lifted map, so maps are compared pointwise (≗); there is no
-- function extensionality. The corollaries at the end are what the
-- metatheory uses: inst-wk, sub-inst, ren-inst, closed-*, inst-motSuc.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.SubstLemmas where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst

infix 4 _≗_
_≗_ : ∀ {A B : Set} → (A → B) → (A → B) → Set
f ≗ g = ∀ x → f x ≡ g x

------------------------------------------------------------------------
-- Pointwise equality is respected.
------------------------------------------------------------------------

lift-ext : ∀ {n m} {ρ ρ′ : Fin n → Fin m} → ρ ≗ ρ′ → lift ρ ≗ lift ρ′
lift-ext h zero    = refl
lift-ext h (suc i) = cong suc (h i)

lifts-ext : ∀ {n m} {σ σ′ : Fin n → Tm m} → σ ≗ σ′ → lifts σ ≗ lifts σ′
lifts-ext h zero    = refl
lifts-ext h (suc i) = cong wk (h i)

mutual
  ren-ext : ∀ {n m} {ρ ρ′ : Fin n → Fin m} → ρ ≗ ρ′ → (t : Tm n)
    → ren ρ t ≡ ren ρ′ t
  ren-ext h (var i) = cong var (h i)
  ren-ext h typ = refl
  ren-ext h (pi q A B) rewrite ren-ext h A | ren-ext (lift-ext h) B = refl
  ren-ext h (lam q A t) rewrite ren-ext h A | ren-ext (lift-ext h) t = refl
  ren-ext h (app f a) rewrite ren-ext h f | ren-ext h a = refl
  ren-ext h nat = refl
  ren-ext h ze = refl
  ren-ext h (su t) rewrite ren-ext h t = refl
  ren-ext h unit = refl
  ren-ext h one = refl
  ren-ext h empty = refl
  ren-ext h (dty i) = refl
  ren-ext h (ctor i j) = refl
  ren-ext h (mData e P bs)
    rewrite ren-ext h e | ren-ext (lift-ext h) P | renList-ext h bs = refl
  ren-ext h (mNat e P z s)
    rewrite ren-ext h e | ren-ext (lift-ext h) P | ren-ext h z
          | ren-ext (lift-ext h) s = refl
  ren-ext h (mEmp e P) rewrite ren-ext h e | ren-ext (lift-ext h) P = refl
  ren-ext h (mUnit e P u)
    rewrite ren-ext h e | ren-ext (lift-ext h) P | ren-ext h u = refl
  ren-ext h (idt A a b) rewrite ren-ext h A | ren-ext h a | ren-ext h b = refl
  ren-ext h rfl = refl
  ren-ext h (rwt e P t)
    rewrite ren-ext h e | ren-ext (lift-ext h) P | ren-ext h t = refl
  ren-ext h (def i) = refl
  ren-ext h (ann e A) rewrite ren-ext h e | ren-ext h A = refl
  ren-ext h (prod A B) rewrite ren-ext h A | ren-ext h B = refl
  ren-ext h (pair a b) rewrite ren-ext h a | ren-ext h b = refl
  ren-ext h (letp e t) rewrite ren-ext h e | ren-ext (lift-ext (lift-ext h)) t = refl
  ren-ext h (nu F) rewrite ren-ext (lift-ext h) F = refl
  ren-ext h (unf s f) rewrite ren-ext h s | ren-ext h f = refl
  ren-ext h (ucons s) rewrite ren-ext h s = refl
  ren-ext h i64 = refl
  ren-ext h f32ty = refl
  ren-ext h (tensor d s) rewrite ren-ext h d | ren-ext h s = refl
  ren-ext h (addi x y) rewrite ren-ext h x | ren-ext h y = refl
  ren-ext h (muli x y) rewrite ren-ext h x | ren-ext h y = refl
  ren-ext h (addt t u) rewrite ren-ext h t | ren-ext h u = refl
  ren-ext h (toi64 t) rewrite ren-ext h t = refl
  ren-ext h (packi x y) rewrite ren-ext h x | ren-ext h y = refl

  renList-ext : ∀ {n m} {ρ ρ′ : Fin n → Fin m} → ρ ≗ ρ′ → (ts : List (Tm n))
    → renList ρ ts ≡ renList ρ′ ts
  renList-ext h [] = refl
  renList-ext h (t ∷ ts) rewrite ren-ext h t | renList-ext h ts = refl

mutual
  sub-ext : ∀ {n m} {σ σ′ : Fin n → Tm m} → σ ≗ σ′ → (t : Tm n)
    → sub σ t ≡ sub σ′ t
  sub-ext h (var i) = h i
  sub-ext h typ = refl
  sub-ext h (pi q A B) rewrite sub-ext h A | sub-ext (lifts-ext h) B = refl
  sub-ext h (lam q A t) rewrite sub-ext h A | sub-ext (lifts-ext h) t = refl
  sub-ext h (app f a) rewrite sub-ext h f | sub-ext h a = refl
  sub-ext h nat = refl
  sub-ext h ze = refl
  sub-ext h (su t) rewrite sub-ext h t = refl
  sub-ext h unit = refl
  sub-ext h one = refl
  sub-ext h empty = refl
  sub-ext h (dty i) = refl
  sub-ext h (ctor i j) = refl
  sub-ext h (mData e P bs)
    rewrite sub-ext h e | sub-ext (lifts-ext h) P | subList-ext h bs = refl
  sub-ext h (mNat e P z s)
    rewrite sub-ext h e | sub-ext (lifts-ext h) P | sub-ext h z
          | sub-ext (lifts-ext h) s = refl
  sub-ext h (mEmp e P) rewrite sub-ext h e | sub-ext (lifts-ext h) P = refl
  sub-ext h (mUnit e P u)
    rewrite sub-ext h e | sub-ext (lifts-ext h) P | sub-ext h u = refl
  sub-ext h (idt A a b) rewrite sub-ext h A | sub-ext h a | sub-ext h b = refl
  sub-ext h rfl = refl
  sub-ext h (rwt e P t)
    rewrite sub-ext h e | sub-ext (lifts-ext h) P | sub-ext h t = refl
  sub-ext h (def i) = refl
  sub-ext h (ann e A) rewrite sub-ext h e | sub-ext h A = refl
  sub-ext h (prod A B) rewrite sub-ext h A | sub-ext h B = refl
  sub-ext h (pair a b) rewrite sub-ext h a | sub-ext h b = refl
  sub-ext h (letp e t) rewrite sub-ext h e | sub-ext (lifts-ext (lifts-ext h)) t = refl
  sub-ext h (nu F) rewrite sub-ext (lifts-ext h) F = refl
  sub-ext h (unf s f) rewrite sub-ext h s | sub-ext h f = refl
  sub-ext h (ucons s) rewrite sub-ext h s = refl
  sub-ext h i64 = refl
  sub-ext h f32ty = refl
  sub-ext h (tensor d s) rewrite sub-ext h d | sub-ext h s = refl
  sub-ext h (addi x y) rewrite sub-ext h x | sub-ext h y = refl
  sub-ext h (muli x y) rewrite sub-ext h x | sub-ext h y = refl
  sub-ext h (addt t u) rewrite sub-ext h t | sub-ext h u = refl
  sub-ext h (toi64 t) rewrite sub-ext h t = refl
  sub-ext h (packi x y) rewrite sub-ext h x | sub-ext h y = refl

  subList-ext : ∀ {n m} {σ σ′ : Fin n → Tm m} → σ ≗ σ′ → (ts : List (Tm n))
    → subList σ ts ≡ subList σ′ ts
  subList-ext h [] = refl
  subList-ext h (t ∷ ts) rewrite sub-ext h t | subList-ext h ts = refl

------------------------------------------------------------------------
-- Identity and composition.
------------------------------------------------------------------------

lift-id : ∀ {n} → lift {n} (λ x → x) ≗ (λ x → x)
lift-id zero    = refl
lift-id (suc i) = refl

mutual
  ren-id : ∀ {n} (t : Tm n) → ren (λ x → x) t ≡ t
  ren-id (var i) = refl
  ren-id typ = refl
  ren-id (pi q A B) rewrite ren-id A | ren-ext lift-id B | ren-id B = refl
  ren-id (lam q A t) rewrite ren-id A | ren-ext lift-id t | ren-id t = refl
  ren-id (app f a) rewrite ren-id f | ren-id a = refl
  ren-id nat = refl
  ren-id ze = refl
  ren-id (su t) rewrite ren-id t = refl
  ren-id unit = refl
  ren-id one = refl
  ren-id empty = refl
  ren-id (dty i) = refl
  ren-id (ctor i j) = refl
  ren-id (mData e P bs)
    rewrite ren-id e | ren-ext lift-id P | ren-id P | renList-id bs = refl
  ren-id (mNat e P z s)
    rewrite ren-id e | ren-ext lift-id P | ren-id P | ren-id z
          | ren-ext lift-id s | ren-id s = refl
  ren-id (mEmp e P) rewrite ren-id e | ren-ext lift-id P | ren-id P = refl
  ren-id (mUnit e P u)
    rewrite ren-id e | ren-ext lift-id P | ren-id P | ren-id u = refl
  ren-id (idt A a b) rewrite ren-id A | ren-id a | ren-id b = refl
  ren-id rfl = refl
  ren-id (rwt e P t)
    rewrite ren-id e | ren-ext lift-id P | ren-id P | ren-id t = refl
  ren-id (def i) = refl
  ren-id (ann e A) rewrite ren-id e | ren-id A = refl
  ren-id (prod A B) rewrite ren-id A | ren-id B = refl
  ren-id (pair a b) rewrite ren-id a | ren-id b = refl
  ren-id (letp e t)
    rewrite ren-id e | ren-ext (lift-ext lift-id) t | ren-ext lift-id t | ren-id t = refl
  ren-id (nu F) rewrite ren-ext lift-id F | ren-id F = refl
  ren-id (unf s f) rewrite ren-id s | ren-id f = refl
  ren-id (ucons s) rewrite ren-id s = refl
  ren-id i64 = refl
  ren-id f32ty = refl
  ren-id (tensor d s) rewrite ren-id d | ren-id s = refl
  ren-id (addi x y) rewrite ren-id x | ren-id y = refl
  ren-id (muli x y) rewrite ren-id x | ren-id y = refl
  ren-id (addt t u) rewrite ren-id t | ren-id u = refl
  ren-id (toi64 t) rewrite ren-id t = refl
  ren-id (packi x y) rewrite ren-id x | ren-id y = refl

  renList-id : ∀ {n} (ts : List (Tm n)) → renList (λ x → x) ts ≡ ts
  renList-id [] = refl
  renList-id (t ∷ ts) rewrite ren-id t | renList-id ts = refl

lift-∘ : ∀ {n m k} (ρ : Fin m → Fin k) (ρ′ : Fin n → Fin m)
  → (λ x → lift ρ (lift ρ′ x)) ≗ lift (λ x → ρ (ρ′ x))
lift-∘ ρ ρ′ zero    = refl
lift-∘ ρ ρ′ (suc i) = refl

mutual
  ren-ren : ∀ {n m k} (ρ : Fin m → Fin k) (ρ′ : Fin n → Fin m) (t : Tm n)
    → ren ρ (ren ρ′ t) ≡ ren (λ x → ρ (ρ′ x)) t
  ren-ren ρ ρ′ (var i) = refl
  ren-ren ρ ρ′ typ = refl
  ren-ren ρ ρ′ (pi q A B)
    rewrite ren-ren ρ ρ′ A | ren-ren (lift ρ) (lift ρ′) B
          | ren-ext (lift-∘ ρ ρ′) B = refl
  ren-ren ρ ρ′ (lam q A t)
    rewrite ren-ren ρ ρ′ A | ren-ren (lift ρ) (lift ρ′) t
          | ren-ext (lift-∘ ρ ρ′) t = refl
  ren-ren ρ ρ′ (app f a) rewrite ren-ren ρ ρ′ f | ren-ren ρ ρ′ a = refl
  ren-ren ρ ρ′ nat = refl
  ren-ren ρ ρ′ ze = refl
  ren-ren ρ ρ′ (su t) rewrite ren-ren ρ ρ′ t = refl
  ren-ren ρ ρ′ unit = refl
  ren-ren ρ ρ′ one = refl
  ren-ren ρ ρ′ empty = refl
  ren-ren ρ ρ′ (dty i) = refl
  ren-ren ρ ρ′ (ctor i j) = refl
  ren-ren ρ ρ′ (mData e P bs)
    rewrite ren-ren ρ ρ′ e | ren-ren (lift ρ) (lift ρ′) P
          | ren-ext (lift-∘ ρ ρ′) P | renList-ren ρ ρ′ bs = refl
  ren-ren ρ ρ′ (mNat e P z s)
    rewrite ren-ren ρ ρ′ e | ren-ren (lift ρ) (lift ρ′) P
          | ren-ext (lift-∘ ρ ρ′) P | ren-ren ρ ρ′ z
          | ren-ren (lift ρ) (lift ρ′) s | ren-ext (lift-∘ ρ ρ′) s = refl
  ren-ren ρ ρ′ (mEmp e P)
    rewrite ren-ren ρ ρ′ e | ren-ren (lift ρ) (lift ρ′) P
          | ren-ext (lift-∘ ρ ρ′) P = refl
  ren-ren ρ ρ′ (mUnit e P u)
    rewrite ren-ren ρ ρ′ e | ren-ren (lift ρ) (lift ρ′) P
          | ren-ext (lift-∘ ρ ρ′) P | ren-ren ρ ρ′ u = refl
  ren-ren ρ ρ′ (idt A a b)
    rewrite ren-ren ρ ρ′ A | ren-ren ρ ρ′ a | ren-ren ρ ρ′ b = refl
  ren-ren ρ ρ′ rfl = refl
  ren-ren ρ ρ′ (rwt e P t)
    rewrite ren-ren ρ ρ′ e | ren-ren (lift ρ) (lift ρ′) P
          | ren-ext (lift-∘ ρ ρ′) P | ren-ren ρ ρ′ t = refl
  ren-ren ρ ρ′ (def i) = refl
  ren-ren ρ ρ′ (ann e A) rewrite ren-ren ρ ρ′ e | ren-ren ρ ρ′ A = refl
  ren-ren ρ ρ′ (prod A B) rewrite ren-ren ρ ρ′ A | ren-ren ρ ρ′ B = refl
  ren-ren ρ ρ′ (pair a b) rewrite ren-ren ρ ρ′ a | ren-ren ρ ρ′ b = refl
  ren-ren ρ ρ′ (letp e t)
    rewrite ren-ren ρ ρ′ e | ren-ren (lift (lift ρ)) (lift (lift ρ′)) t
          | ren-ext (lift-∘ (lift ρ) (lift ρ′)) t | ren-ext (lift-ext (lift-∘ ρ ρ′)) t = refl
  ren-ren ρ ρ′ (nu F)
    rewrite ren-ren (lift ρ) (lift ρ′) F | ren-ext (lift-∘ ρ ρ′) F = refl
  ren-ren ρ ρ′ (unf s f) rewrite ren-ren ρ ρ′ s | ren-ren ρ ρ′ f = refl
  ren-ren ρ ρ′ (ucons s) rewrite ren-ren ρ ρ′ s = refl
  ren-ren ρ ρ′ i64 = refl
  ren-ren ρ ρ′ f32ty = refl
  ren-ren ρ ρ′ (tensor d s) rewrite ren-ren ρ ρ′ d | ren-ren ρ ρ′ s = refl
  ren-ren ρ ρ′ (addi x y) rewrite ren-ren ρ ρ′ x | ren-ren ρ ρ′ y = refl
  ren-ren ρ ρ′ (muli x y) rewrite ren-ren ρ ρ′ x | ren-ren ρ ρ′ y = refl
  ren-ren ρ ρ′ (addt t u) rewrite ren-ren ρ ρ′ t | ren-ren ρ ρ′ u = refl
  ren-ren ρ ρ′ (toi64 t) rewrite ren-ren ρ ρ′ t = refl
  ren-ren ρ ρ′ (packi x y) rewrite ren-ren ρ ρ′ x | ren-ren ρ ρ′ y = refl

  renList-ren : ∀ {n m k} (ρ : Fin m → Fin k) (ρ′ : Fin n → Fin m)
    (ts : List (Tm n)) → renList ρ (renList ρ′ ts) ≡ renList (λ x → ρ (ρ′ x)) ts
  renList-ren ρ ρ′ [] = refl
  renList-ren ρ ρ′ (t ∷ ts) rewrite ren-ren ρ ρ′ t | renList-ren ρ ρ′ ts = refl

lifts-lift : ∀ {n m k} (σ : Fin m → Tm k) (ρ : Fin n → Fin m)
  → (λ x → lifts σ (lift ρ x)) ≗ lifts (λ x → σ (ρ x))
lifts-lift σ ρ zero    = refl
lifts-lift σ ρ (suc i) = refl

mutual
  sub-ren : ∀ {n m k} (σ : Fin m → Tm k) (ρ : Fin n → Fin m) (t : Tm n)
    → sub σ (ren ρ t) ≡ sub (λ x → σ (ρ x)) t
  sub-ren σ ρ (var i) = refl
  sub-ren σ ρ typ = refl
  sub-ren σ ρ (pi q A B)
    rewrite sub-ren σ ρ A | sub-ren (lifts σ) (lift ρ) B
          | sub-ext (lifts-lift σ ρ) B = refl
  sub-ren σ ρ (lam q A t)
    rewrite sub-ren σ ρ A | sub-ren (lifts σ) (lift ρ) t
          | sub-ext (lifts-lift σ ρ) t = refl
  sub-ren σ ρ (app f a) rewrite sub-ren σ ρ f | sub-ren σ ρ a = refl
  sub-ren σ ρ nat = refl
  sub-ren σ ρ ze = refl
  sub-ren σ ρ (su t) rewrite sub-ren σ ρ t = refl
  sub-ren σ ρ unit = refl
  sub-ren σ ρ one = refl
  sub-ren σ ρ empty = refl
  sub-ren σ ρ (dty i) = refl
  sub-ren σ ρ (ctor i j) = refl
  sub-ren σ ρ (mData e P bs)
    rewrite sub-ren σ ρ e | sub-ren (lifts σ) (lift ρ) P
          | sub-ext (lifts-lift σ ρ) P | subList-ren σ ρ bs = refl
  sub-ren σ ρ (mNat e P z s)
    rewrite sub-ren σ ρ e | sub-ren (lifts σ) (lift ρ) P
          | sub-ext (lifts-lift σ ρ) P | sub-ren σ ρ z
          | sub-ren (lifts σ) (lift ρ) s | sub-ext (lifts-lift σ ρ) s = refl
  sub-ren σ ρ (mEmp e P)
    rewrite sub-ren σ ρ e | sub-ren (lifts σ) (lift ρ) P
          | sub-ext (lifts-lift σ ρ) P = refl
  sub-ren σ ρ (mUnit e P u)
    rewrite sub-ren σ ρ e | sub-ren (lifts σ) (lift ρ) P
          | sub-ext (lifts-lift σ ρ) P | sub-ren σ ρ u = refl
  sub-ren σ ρ (idt A a b)
    rewrite sub-ren σ ρ A | sub-ren σ ρ a | sub-ren σ ρ b = refl
  sub-ren σ ρ rfl = refl
  sub-ren σ ρ (rwt e P t)
    rewrite sub-ren σ ρ e | sub-ren (lifts σ) (lift ρ) P
          | sub-ext (lifts-lift σ ρ) P | sub-ren σ ρ t = refl
  sub-ren σ ρ (def i) = refl
  sub-ren σ ρ (ann e A) rewrite sub-ren σ ρ e | sub-ren σ ρ A = refl
  sub-ren σ ρ (prod A B) rewrite sub-ren σ ρ A | sub-ren σ ρ B = refl
  sub-ren σ ρ (pair a b) rewrite sub-ren σ ρ a | sub-ren σ ρ b = refl
  sub-ren σ ρ (letp e t)
    rewrite sub-ren σ ρ e | sub-ren (lifts (lifts σ)) (lift (lift ρ)) t
          | sub-ext (lifts-lift (lifts σ) (lift ρ)) t | sub-ext (lifts-ext (lifts-lift σ ρ)) t = refl
  sub-ren σ ρ (nu F)
    rewrite sub-ren (lifts σ) (lift ρ) F | sub-ext (lifts-lift σ ρ) F = refl
  sub-ren σ ρ (unf s f) rewrite sub-ren σ ρ s | sub-ren σ ρ f = refl
  sub-ren σ ρ (ucons s) rewrite sub-ren σ ρ s = refl
  sub-ren σ ρ i64 = refl
  sub-ren σ ρ f32ty = refl
  sub-ren σ ρ (tensor d s) rewrite sub-ren σ ρ d | sub-ren σ ρ s = refl
  sub-ren σ ρ (addi x y) rewrite sub-ren σ ρ x | sub-ren σ ρ y = refl
  sub-ren σ ρ (muli x y) rewrite sub-ren σ ρ x | sub-ren σ ρ y = refl
  sub-ren σ ρ (addt t u) rewrite sub-ren σ ρ t | sub-ren σ ρ u = refl
  sub-ren σ ρ (toi64 t) rewrite sub-ren σ ρ t = refl
  sub-ren σ ρ (packi x y) rewrite sub-ren σ ρ x | sub-ren σ ρ y = refl

  subList-ren : ∀ {n m k} (σ : Fin m → Tm k) (ρ : Fin n → Fin m)
    (ts : List (Tm n)) → subList σ (renList ρ ts) ≡ subList (λ x → σ (ρ x)) ts
  subList-ren σ ρ [] = refl
  subList-ren σ ρ (t ∷ ts) rewrite sub-ren σ ρ t | subList-ren σ ρ ts = refl

lift-lifts : ∀ {n m k} (ρ : Fin m → Fin k) (σ : Fin n → Tm m)
  → (λ x → ren (lift ρ) (lifts σ x)) ≗ lifts (λ x → ren ρ (σ x))
lift-lifts ρ σ zero    = refl
lift-lifts ρ σ (suc i) =
  trans (ren-ren (lift ρ) suc (σ i)) (sym (ren-ren suc ρ (σ i)))

mutual
  ren-sub : ∀ {n m k} (ρ : Fin m → Fin k) (σ : Fin n → Tm m) (t : Tm n)
    → ren ρ (sub σ t) ≡ sub (λ x → ren ρ (σ x)) t
  ren-sub ρ σ (var i) = refl
  ren-sub ρ σ typ = refl
  ren-sub ρ σ (pi q A B)
    rewrite ren-sub ρ σ A | ren-sub (lift ρ) (lifts σ) B
          | sub-ext (lift-lifts ρ σ) B = refl
  ren-sub ρ σ (lam q A t)
    rewrite ren-sub ρ σ A | ren-sub (lift ρ) (lifts σ) t
          | sub-ext (lift-lifts ρ σ) t = refl
  ren-sub ρ σ (app f a) rewrite ren-sub ρ σ f | ren-sub ρ σ a = refl
  ren-sub ρ σ nat = refl
  ren-sub ρ σ ze = refl
  ren-sub ρ σ (su t) rewrite ren-sub ρ σ t = refl
  ren-sub ρ σ unit = refl
  ren-sub ρ σ one = refl
  ren-sub ρ σ empty = refl
  ren-sub ρ σ (dty i) = refl
  ren-sub ρ σ (ctor i j) = refl
  ren-sub ρ σ (mData e P bs)
    rewrite ren-sub ρ σ e | ren-sub (lift ρ) (lifts σ) P
          | sub-ext (lift-lifts ρ σ) P | renList-sub ρ σ bs = refl
  ren-sub ρ σ (mNat e P z s)
    rewrite ren-sub ρ σ e | ren-sub (lift ρ) (lifts σ) P
          | sub-ext (lift-lifts ρ σ) P | ren-sub ρ σ z
          | ren-sub (lift ρ) (lifts σ) s | sub-ext (lift-lifts ρ σ) s = refl
  ren-sub ρ σ (mEmp e P)
    rewrite ren-sub ρ σ e | ren-sub (lift ρ) (lifts σ) P
          | sub-ext (lift-lifts ρ σ) P = refl
  ren-sub ρ σ (mUnit e P u)
    rewrite ren-sub ρ σ e | ren-sub (lift ρ) (lifts σ) P
          | sub-ext (lift-lifts ρ σ) P | ren-sub ρ σ u = refl
  ren-sub ρ σ (idt A a b)
    rewrite ren-sub ρ σ A | ren-sub ρ σ a | ren-sub ρ σ b = refl
  ren-sub ρ σ rfl = refl
  ren-sub ρ σ (rwt e P t)
    rewrite ren-sub ρ σ e | ren-sub (lift ρ) (lifts σ) P
          | sub-ext (lift-lifts ρ σ) P | ren-sub ρ σ t = refl
  ren-sub ρ σ (def i) = refl
  ren-sub ρ σ (ann e A) rewrite ren-sub ρ σ e | ren-sub ρ σ A = refl
  ren-sub ρ σ (prod A B) rewrite ren-sub ρ σ A | ren-sub ρ σ B = refl
  ren-sub ρ σ (pair a b) rewrite ren-sub ρ σ a | ren-sub ρ σ b = refl
  ren-sub ρ σ (letp e t)
    rewrite ren-sub ρ σ e | ren-sub (lift (lift ρ)) (lifts (lifts σ)) t
          | sub-ext (lift-lifts (lift ρ) (lifts σ)) t | sub-ext (lifts-ext (lift-lifts ρ σ)) t = refl
  ren-sub ρ σ (nu F)
    rewrite ren-sub (lift ρ) (lifts σ) F | sub-ext (lift-lifts ρ σ) F = refl
  ren-sub ρ σ (unf s f) rewrite ren-sub ρ σ s | ren-sub ρ σ f = refl
  ren-sub ρ σ (ucons s) rewrite ren-sub ρ σ s = refl
  ren-sub ρ σ i64 = refl
  ren-sub ρ σ f32ty = refl
  ren-sub ρ σ (tensor d s) rewrite ren-sub ρ σ d | ren-sub ρ σ s = refl
  ren-sub ρ σ (addi x y) rewrite ren-sub ρ σ x | ren-sub ρ σ y = refl
  ren-sub ρ σ (muli x y) rewrite ren-sub ρ σ x | ren-sub ρ σ y = refl
  ren-sub ρ σ (addt t u) rewrite ren-sub ρ σ t | ren-sub ρ σ u = refl
  ren-sub ρ σ (toi64 t) rewrite ren-sub ρ σ t = refl
  ren-sub ρ σ (packi x y) rewrite ren-sub ρ σ x | ren-sub ρ σ y = refl

  renList-sub : ∀ {n m k} (ρ : Fin m → Fin k) (σ : Fin n → Tm m)
    (ts : List (Tm n)) → renList ρ (subList σ ts) ≡ subList (λ x → ren ρ (σ x)) ts
  renList-sub ρ σ [] = refl
  renList-sub ρ σ (t ∷ ts) rewrite ren-sub ρ σ t | renList-sub ρ σ ts = refl

lifts-lifts : ∀ {n m k} (σ : Fin m → Tm k) (τ : Fin n → Tm m)
  → (λ x → sub (lifts σ) (lifts τ x)) ≗ lifts (λ x → sub σ (τ x))
lifts-lifts σ τ zero    = refl
lifts-lifts σ τ (suc i) =
  trans (sub-ren (lifts σ) suc (τ i)) (sym (ren-sub suc σ (τ i)))

mutual
  sub-sub : ∀ {n m k} (σ : Fin m → Tm k) (τ : Fin n → Tm m) (t : Tm n)
    → sub σ (sub τ t) ≡ sub (λ x → sub σ (τ x)) t
  sub-sub σ τ (var i) = refl
  sub-sub σ τ typ = refl
  sub-sub σ τ (pi q A B)
    rewrite sub-sub σ τ A | sub-sub (lifts σ) (lifts τ) B
          | sub-ext (lifts-lifts σ τ) B = refl
  sub-sub σ τ (lam q A t)
    rewrite sub-sub σ τ A | sub-sub (lifts σ) (lifts τ) t
          | sub-ext (lifts-lifts σ τ) t = refl
  sub-sub σ τ (app f a) rewrite sub-sub σ τ f | sub-sub σ τ a = refl
  sub-sub σ τ nat = refl
  sub-sub σ τ ze = refl
  sub-sub σ τ (su t) rewrite sub-sub σ τ t = refl
  sub-sub σ τ unit = refl
  sub-sub σ τ one = refl
  sub-sub σ τ empty = refl
  sub-sub σ τ (dty i) = refl
  sub-sub σ τ (ctor i j) = refl
  sub-sub σ τ (mData e P bs)
    rewrite sub-sub σ τ e | sub-sub (lifts σ) (lifts τ) P
          | sub-ext (lifts-lifts σ τ) P | subList-sub σ τ bs = refl
  sub-sub σ τ (mNat e P z s)
    rewrite sub-sub σ τ e | sub-sub (lifts σ) (lifts τ) P
          | sub-ext (lifts-lifts σ τ) P | sub-sub σ τ z
          | sub-sub (lifts σ) (lifts τ) s | sub-ext (lifts-lifts σ τ) s = refl
  sub-sub σ τ (mEmp e P)
    rewrite sub-sub σ τ e | sub-sub (lifts σ) (lifts τ) P
          | sub-ext (lifts-lifts σ τ) P = refl
  sub-sub σ τ (mUnit e P u)
    rewrite sub-sub σ τ e | sub-sub (lifts σ) (lifts τ) P
          | sub-ext (lifts-lifts σ τ) P | sub-sub σ τ u = refl
  sub-sub σ τ (idt A a b)
    rewrite sub-sub σ τ A | sub-sub σ τ a | sub-sub σ τ b = refl
  sub-sub σ τ rfl = refl
  sub-sub σ τ (rwt e P t)
    rewrite sub-sub σ τ e | sub-sub (lifts σ) (lifts τ) P
          | sub-ext (lifts-lifts σ τ) P | sub-sub σ τ t = refl
  sub-sub σ τ (def i) = refl
  sub-sub σ τ (ann e A) rewrite sub-sub σ τ e | sub-sub σ τ A = refl
  sub-sub σ τ (prod A B) rewrite sub-sub σ τ A | sub-sub σ τ B = refl
  sub-sub σ τ (pair a b) rewrite sub-sub σ τ a | sub-sub σ τ b = refl
  sub-sub σ τ (letp e t)
    rewrite sub-sub σ τ e | sub-sub (lifts (lifts σ)) (lifts (lifts τ)) t
          | sub-ext (lifts-lifts (lifts σ) (lifts τ)) t | sub-ext (lifts-ext (lifts-lifts σ τ)) t = refl
  sub-sub σ τ (nu F)
    rewrite sub-sub (lifts σ) (lifts τ) F | sub-ext (lifts-lifts σ τ) F = refl
  sub-sub σ τ (unf s f) rewrite sub-sub σ τ s | sub-sub σ τ f = refl
  sub-sub σ τ (ucons s) rewrite sub-sub σ τ s = refl
  sub-sub σ τ i64 = refl
  sub-sub σ τ f32ty = refl
  sub-sub σ τ (tensor d s) rewrite sub-sub σ τ d | sub-sub σ τ s = refl
  sub-sub σ τ (addi x y) rewrite sub-sub σ τ x | sub-sub σ τ y = refl
  sub-sub σ τ (muli x y) rewrite sub-sub σ τ x | sub-sub σ τ y = refl
  sub-sub σ τ (addt t u) rewrite sub-sub σ τ t | sub-sub σ τ u = refl
  sub-sub σ τ (toi64 t) rewrite sub-sub σ τ t = refl
  sub-sub σ τ (packi x y) rewrite sub-sub σ τ x | sub-sub σ τ y = refl

  subList-sub : ∀ {n m k} (σ : Fin m → Tm k) (τ : Fin n → Tm m)
    (ts : List (Tm n)) → subList σ (subList τ ts) ≡ subList (λ x → sub σ (τ x)) ts
  subList-sub σ τ [] = refl
  subList-sub σ τ (t ∷ ts) rewrite sub-sub σ τ t | subList-sub σ τ ts = refl

------------------------------------------------------------------------
-- Renaming is substitution by variables; substitution by variables is
-- the identity.
------------------------------------------------------------------------

lift-var : ∀ {n m} (ρ : Fin n → Fin m)
  → (λ x → var (lift ρ x)) ≗ lifts (λ x → var (ρ x))
lift-var ρ zero    = refl
lift-var ρ (suc i) = refl

mutual
  ren-is-sub : ∀ {n m} (ρ : Fin n → Fin m) (t : Tm n)
    → ren ρ t ≡ sub (λ x → var (ρ x)) t
  ren-is-sub ρ (var i) = refl
  ren-is-sub ρ typ = refl
  ren-is-sub ρ (pi q A B)
    rewrite ren-is-sub ρ A | ren-is-sub (lift ρ) B | sub-ext (lift-var ρ) B = refl
  ren-is-sub ρ (lam q A t)
    rewrite ren-is-sub ρ A | ren-is-sub (lift ρ) t | sub-ext (lift-var ρ) t = refl
  ren-is-sub ρ (app f a) rewrite ren-is-sub ρ f | ren-is-sub ρ a = refl
  ren-is-sub ρ nat = refl
  ren-is-sub ρ ze = refl
  ren-is-sub ρ (su t) rewrite ren-is-sub ρ t = refl
  ren-is-sub ρ unit = refl
  ren-is-sub ρ one = refl
  ren-is-sub ρ empty = refl
  ren-is-sub ρ (dty i) = refl
  ren-is-sub ρ (ctor i j) = refl
  ren-is-sub ρ (mData e P bs)
    rewrite ren-is-sub ρ e | ren-is-sub (lift ρ) P | sub-ext (lift-var ρ) P
          | renList-is-sub ρ bs = refl
  ren-is-sub ρ (mNat e P z s)
    rewrite ren-is-sub ρ e | ren-is-sub (lift ρ) P | sub-ext (lift-var ρ) P
          | ren-is-sub ρ z | ren-is-sub (lift ρ) s | sub-ext (lift-var ρ) s = refl
  ren-is-sub ρ (mEmp e P)
    rewrite ren-is-sub ρ e | ren-is-sub (lift ρ) P | sub-ext (lift-var ρ) P = refl
  ren-is-sub ρ (mUnit e P u)
    rewrite ren-is-sub ρ e | ren-is-sub (lift ρ) P | sub-ext (lift-var ρ) P
          | ren-is-sub ρ u = refl
  ren-is-sub ρ (idt A a b)
    rewrite ren-is-sub ρ A | ren-is-sub ρ a | ren-is-sub ρ b = refl
  ren-is-sub ρ rfl = refl
  ren-is-sub ρ (rwt e P t)
    rewrite ren-is-sub ρ e | ren-is-sub (lift ρ) P | sub-ext (lift-var ρ) P
          | ren-is-sub ρ t = refl
  ren-is-sub ρ (def i) = refl
  ren-is-sub ρ (ann e A) rewrite ren-is-sub ρ e | ren-is-sub ρ A = refl
  ren-is-sub ρ (prod A B) rewrite ren-is-sub ρ A | ren-is-sub ρ B = refl
  ren-is-sub ρ (pair a b) rewrite ren-is-sub ρ a | ren-is-sub ρ b = refl
  ren-is-sub ρ (letp e t)
    rewrite ren-is-sub ρ e | ren-is-sub (lift (lift ρ)) t
          | sub-ext (lift-var (lift ρ)) t | sub-ext (lifts-ext (lift-var ρ)) t = refl
  ren-is-sub ρ (nu F)
    rewrite ren-is-sub (lift ρ) F | sub-ext (lift-var ρ) F = refl
  ren-is-sub ρ (unf s f) rewrite ren-is-sub ρ s | ren-is-sub ρ f = refl
  ren-is-sub ρ (ucons s) rewrite ren-is-sub ρ s = refl
  ren-is-sub ρ i64 = refl
  ren-is-sub ρ f32ty = refl
  ren-is-sub ρ (tensor d s) rewrite ren-is-sub ρ d | ren-is-sub ρ s = refl
  ren-is-sub ρ (addi x y) rewrite ren-is-sub ρ x | ren-is-sub ρ y = refl
  ren-is-sub ρ (muli x y) rewrite ren-is-sub ρ x | ren-is-sub ρ y = refl
  ren-is-sub ρ (addt t u) rewrite ren-is-sub ρ t | ren-is-sub ρ u = refl
  ren-is-sub ρ (toi64 t) rewrite ren-is-sub ρ t = refl
  ren-is-sub ρ (packi x y) rewrite ren-is-sub ρ x | ren-is-sub ρ y = refl

  renList-is-sub : ∀ {n m} (ρ : Fin n → Fin m) (ts : List (Tm n))
    → renList ρ ts ≡ subList (λ x → var (ρ x)) ts
  renList-is-sub ρ [] = refl
  renList-is-sub ρ (t ∷ ts) rewrite ren-is-sub ρ t | renList-is-sub ρ ts = refl

sub-var : ∀ {n} (t : Tm n) → sub var t ≡ t
sub-var t = trans (sym (ren-is-sub (λ x → x) t)) (ren-id t)

------------------------------------------------------------------------
-- Corollaries used by the metatheory.
------------------------------------------------------------------------

-- wk then instantiate is the identity.
inst-wk : ∀ {n} (t : Tm n) (a : Tm n) → inst (wk t) a ≡ t
inst-wk t a = trans (sub-ren (instσ a) suc t) (sub-var t)

-- Substitution commutes with instantiation.
sub-inst : ∀ {n m} (σ : Fin n → Tm m) (t : Tm (suc n)) (a : Tm n)
  → sub σ (inst t a) ≡ inst (sub (lifts σ) t) (sub σ a)
sub-inst σ t a =
  trans (sub-sub σ (instσ a) t)
    (trans (sub-ext h t) (sym (sub-sub (instσ (sub σ a)) (lifts σ) t)))
  where
    h : (λ x → sub σ (instσ a x)) ≗ (λ x → sub (instσ (sub σ a)) (lifts σ x))
    h zero    = refl
    h (suc i) = sym (inst-wk (σ i) (sub σ a))

-- Renaming commutes with instantiation.
ren-inst : ∀ {n m} (ρ : Fin n → Fin m) (t : Tm (suc n)) (a : Tm n)
  → ren ρ (inst t a) ≡ inst (ren (lift ρ) t) (ren ρ a)
ren-inst ρ t a =
  trans (ren-sub ρ (instσ a) t)
    (trans (sub-ext h t) (sym (sub-ren (instσ (ren ρ a)) (lift ρ) t)))
  where
    h : (λ x → ren ρ (instσ a x)) ≗ (λ x → instσ (ren ρ a) (lift ρ x))
    h zero    = refl
    h (suc i) = refl

-- Weakening commutes with substitution and renaming under a binder.
sub-wk : ∀ {n m} (σ : Fin n → Tm m) (A : Tm n)
  → sub (lifts σ) (wk A) ≡ wk (sub σ A)
sub-wk σ A = trans (sub-ren (lifts σ) suc A) (sym (ren-sub suc σ A))

ren-wk : ∀ {n m} (ρ : Fin n → Fin m) (A : Tm n)
  → ren (lift ρ) (wk A) ≡ wk (ren ρ A)
ren-wk ρ A = trans (ren-ren (lift ρ) suc A) (sym (ren-ren suc ρ A))

-- Closed terms are fixed by renaming and substitution.
closed-ren : ∀ {n m} (ρ : Fin n → Fin m) (t : Tm 0) → ren ρ (closed t) ≡ closed t
closed-ren ρ t = trans (ren-ren ρ fromZero t) (ren-ext (λ ()) t)

closed-sub : ∀ {n m} (σ : Fin n → Tm m) (t : Tm 0) → sub σ (closed t) ≡ closed t
closed-sub σ t =
  trans (sub-ren σ fromZero t)
    (trans (sub-ext (λ ()) t) (sym (ren-is-sub fromZero t)))

inst-closed : ∀ {n} (t : Tm 0) (a : Tm n) → inst (closed t) a ≡ closed t
inst-closed t a = closed-sub (instσ a) t

wk-closed : ∀ {n} (t : Tm 0) → wk {n} (closed t) ≡ closed t
wk-closed t = closed-ren suc t

-- The successor motive.
inst-motSuc : ∀ {n} (P : Tm (suc n)) (u : Tm n) → inst (motSuc P) u ≡ inst P (su u)
inst-motSuc P u = trans (sub-sub (instσ u) motSucσ P) (sub-ext h P)
  where
    h : (λ x → sub (instσ u) (motSucσ x)) ≗ instσ (su u)
    h zero    = refl
    h (suc i) = refl

sub-motSuc : ∀ {n m} (σ : Fin n → Tm m) (P : Tm (suc n))
  → sub (lifts σ) (motSuc P) ≡ motSuc (sub (lifts σ) P)
sub-motSuc σ P =
  trans (sub-sub (lifts σ) motSucσ P)
    (trans (sub-ext h P) (sym (sub-sub motSucσ (lifts σ) P)))
  where
    h : (λ x → sub (lifts σ) (motSucσ x)) ≗ (λ x → sub motSucσ (lifts σ x))
    h zero    = refl
    h (suc i) = sym (trans (sub-ren motSucσ suc (σ i)) (sym (ren-is-sub suc (σ i))))

ren-motSuc : ∀ {n m} (ρ : Fin n → Fin m) (P : Tm (suc n))
  → ren (lift ρ) (motSuc P) ≡ motSuc (ren (lift ρ) P)
ren-motSuc ρ P =
  trans (ren-sub (lift ρ) motSucσ P)
    (trans (sub-ext h P) (sym (sub-ren motSucσ (lift ρ) P)))
  where
    h : (λ x → ren (lift ρ) (motSucσ x)) ≗ (λ x → motSucσ (lift ρ x))
    h zero    = refl
    h (suc i) = refl

-- Two binders at once (the tensor eliminator).
inst₂-wk₂ : ∀ {n} (C : Tm n) (a b : Tm n) → inst₂ (wk (wk C)) a b ≡ C
inst₂-wk₂ C a b rewrite inst-wk (wk C) (wk b) = inst-wk C a

sub-inst₂ : ∀ {n m} (σ : Fin n → Tm m) (t : Tm (suc (suc n))) (a b : Tm n)
  → sub σ (inst₂ t a b) ≡ inst₂ (sub (lifts (lifts σ)) t) (sub σ a) (sub σ b)
sub-inst₂ σ t a b
  rewrite sub-inst σ (inst t (wk b)) a | sub-inst (lifts σ) t (wk b) | sub-wk σ b = refl

ren-inst₂ : ∀ {n m} (ρ : Fin n → Fin m) (t : Tm (suc (suc n))) (a b : Tm n)
  → ren ρ (inst₂ t a b) ≡ inst₂ (ren (lift (lift ρ)) t) (ren ρ a) (ren ρ b)
ren-inst₂ ρ t a b
  rewrite ren-inst ρ (inst t (wk b)) a | ren-inst (lift ρ) t (wk b) | ren-wk ρ b = refl

------------------------------------------------------------------------
-- Partial renaming is sound: when renM ρ? t succeeds with u, and ρ is a
-- left inverse of ρ? where it is defined, ren ρ u is t again.
------------------------------------------------------------------------

Inv : ∀ {n m} → (Fin n → Result (Fin m)) → (Fin m → Fin n) → Set
Inv ρ? ρ = ∀ i j → ρ? i ≡ ok j → ρ j ≡ i

liftM-inv : ∀ {n m} (ρ? : Fin n → Result (Fin m)) (ρ : Fin m → Fin n)
  → Inv ρ? ρ → Inv (liftM ρ?) (lift ρ)
liftM-inv ρ? ρ h zero zero eq = refl
liftM-inv ρ? ρ h (suc i) j eq with ρ? i in e
liftM-inv ρ? ρ h (suc i) .(suc j′) refl | ok j′ = cong suc (h i j′ e)

mutual
  renM-sound : ∀ {n m} (ρ? : Fin n → Result (Fin m)) (ρ : Fin m → Fin n) → Inv ρ? ρ
    → (t : Tm n) {u : Tm m} → renM ρ? t ≡ ok u → ren ρ u ≡ t
  renM-sound ρ? ρ h (var i) eq with ρ? i in e
  renM-sound ρ? ρ h (var i) refl | ok j = cong var (h i j e)
  renM-sound ρ? ρ h typ refl = refl
  renM-sound ρ? ρ h (pi q A B) eq with renM ρ? A in eA | renM (liftM ρ?) B in eB
  renM-sound ρ? ρ h (pi q A B) refl | ok A′ | ok B′ = cong₂ (pi q) (renM-sound ρ? ρ h A eA) (renM-sound (liftM ρ?) (lift ρ) (liftM-inv ρ? ρ h) B eB)
  renM-sound ρ? ρ h (lam q A t) eq with renM ρ? A in eA | renM (liftM ρ?) t in et
  renM-sound ρ? ρ h (lam q A t) refl | ok A′ | ok t′ = cong₂ (lam q) (renM-sound ρ? ρ h A eA) (renM-sound (liftM ρ?) (lift ρ) (liftM-inv ρ? ρ h) t et)
  renM-sound ρ? ρ h (app f a) eq with renM ρ? f in ef | renM ρ? a in ea
  renM-sound ρ? ρ h (app f a) refl | ok f′ | ok a′ = cong₂ app (renM-sound ρ? ρ h f ef) (renM-sound ρ? ρ h a ea)
  renM-sound ρ? ρ h nat refl = refl
  renM-sound ρ? ρ h ze refl = refl
  renM-sound ρ? ρ h (su t) eq with renM ρ? t in et
  renM-sound ρ? ρ h (su t) refl | ok t′ = cong su (renM-sound ρ? ρ h t et)
  renM-sound ρ? ρ h unit refl = refl
  renM-sound ρ? ρ h one refl = refl
  renM-sound ρ? ρ h empty refl = refl
  renM-sound ρ? ρ h (dty i) refl = refl
  renM-sound ρ? ρ h (ctor i j) refl = refl
  renM-sound ρ? ρ h (mData e P bs) eq with renM ρ? e in ee | renM (liftM ρ?) P in eP | renMList ρ? bs in ebs
  renM-sound ρ? ρ h (mData e P bs) refl | ok e′ | ok P′ | ok bs′ rewrite (renM-sound ρ? ρ h e ee) | (renM-sound (liftM ρ?) (lift ρ) (liftM-inv ρ? ρ h) P eP) | (renMList-sound ρ? ρ h bs ebs) = refl
  renM-sound ρ? ρ h (mNat e P z s) eq with renM ρ? e in ee | renM (liftM ρ?) P in eP | renM ρ? z in ez | renM (liftM ρ?) s in es
  renM-sound ρ? ρ h (mNat e P z s) refl | ok e′ | ok P′ | ok z′ | ok s′ rewrite (renM-sound ρ? ρ h e ee) | (renM-sound (liftM ρ?) (lift ρ) (liftM-inv ρ? ρ h) P eP) | (renM-sound ρ? ρ h z ez) | (renM-sound (liftM ρ?) (lift ρ) (liftM-inv ρ? ρ h) s es) = refl
  renM-sound ρ? ρ h (mEmp e P) eq with renM ρ? e in ee | renM (liftM ρ?) P in eP
  renM-sound ρ? ρ h (mEmp e P) refl | ok e′ | ok P′ = cong₂ mEmp (renM-sound ρ? ρ h e ee) (renM-sound (liftM ρ?) (lift ρ) (liftM-inv ρ? ρ h) P eP)
  renM-sound ρ? ρ h (mUnit e P u) eq with renM ρ? e in ee | renM (liftM ρ?) P in eP | renM ρ? u in eu
  renM-sound ρ? ρ h (mUnit e P u) refl | ok e′ | ok P′ | ok u′ rewrite (renM-sound ρ? ρ h e ee) | (renM-sound (liftM ρ?) (lift ρ) (liftM-inv ρ? ρ h) P eP) | (renM-sound ρ? ρ h u eu) = refl
  renM-sound ρ? ρ h (idt A a b) eq with renM ρ? A in eA | renM ρ? a in ea | renM ρ? b in eb
  renM-sound ρ? ρ h (idt A a b) refl | ok A′ | ok a′ | ok b′ rewrite (renM-sound ρ? ρ h A eA) | (renM-sound ρ? ρ h a ea) | (renM-sound ρ? ρ h b eb) = refl
  renM-sound ρ? ρ h rfl refl = refl
  renM-sound ρ? ρ h (rwt e P t) eq with renM ρ? e in ee | renM (liftM ρ?) P in eP | renM ρ? t in et
  renM-sound ρ? ρ h (rwt e P t) refl | ok e′ | ok P′ | ok t′ rewrite (renM-sound ρ? ρ h e ee) | (renM-sound (liftM ρ?) (lift ρ) (liftM-inv ρ? ρ h) P eP) | (renM-sound ρ? ρ h t et) = refl
  renM-sound ρ? ρ h (def i) refl = refl
  renM-sound ρ? ρ h (ann e A) eq with renM ρ? e in ee | renM ρ? A in eA
  renM-sound ρ? ρ h (ann e A) refl | ok e′ | ok A′ = cong₂ ann (renM-sound ρ? ρ h e ee) (renM-sound ρ? ρ h A eA)
  renM-sound ρ? ρ h (prod A B) eq with renM ρ? A in eA | renM ρ? B in eB
  renM-sound ρ? ρ h (prod A B) refl | ok A′ | ok B′ = cong₂ prod (renM-sound ρ? ρ h A eA) (renM-sound ρ? ρ h B eB)
  renM-sound ρ? ρ h (pair a b) eq with renM ρ? a in ea | renM ρ? b in eb
  renM-sound ρ? ρ h (pair a b) refl | ok a′ | ok b′ = cong₂ pair (renM-sound ρ? ρ h a ea) (renM-sound ρ? ρ h b eb)
  renM-sound ρ? ρ h (letp e t) eq with renM ρ? e in ee | renM (liftM (liftM ρ?)) t in et
  renM-sound ρ? ρ h (letp e t) refl | ok e′ | ok t′ = cong₂ letp (renM-sound ρ? ρ h e ee) (renM-sound (liftM (liftM ρ?)) (lift (lift ρ)) (liftM-inv (liftM ρ?) (lift ρ) (liftM-inv ρ? ρ h)) t et)
  renM-sound ρ? ρ h (nu F) eq with renM (liftM ρ?) F in eF
  renM-sound ρ? ρ h (nu F) refl | ok F′ = cong nu (renM-sound (liftM ρ?) (lift ρ) (liftM-inv ρ? ρ h) F eF)
  renM-sound ρ? ρ h (unf s f) eq with renM ρ? s in es | renM ρ? f in ef
  renM-sound ρ? ρ h (unf s f) refl | ok s′ | ok f′ = cong₂ unf (renM-sound ρ? ρ h s es) (renM-sound ρ? ρ h f ef)
  renM-sound ρ? ρ h (ucons s) eq with renM ρ? s in es
  renM-sound ρ? ρ h (ucons s) refl | ok s′ = cong ucons (renM-sound ρ? ρ h s es)
  renM-sound ρ? ρ h i64 refl = refl
  renM-sound ρ? ρ h f32ty refl = refl
  renM-sound ρ? ρ h (tensor d s) eq with renM ρ? d in ed | renM ρ? s in es
  renM-sound ρ? ρ h (tensor d s) refl | ok d′ | ok s′ = cong₂ tensor (renM-sound ρ? ρ h d ed) (renM-sound ρ? ρ h s es)
  renM-sound ρ? ρ h (addi x y) eq with renM ρ? x in ex | renM ρ? y in ey
  renM-sound ρ? ρ h (addi x y) refl | ok x′ | ok y′ = cong₂ addi (renM-sound ρ? ρ h x ex) (renM-sound ρ? ρ h y ey)
  renM-sound ρ? ρ h (muli x y) eq with renM ρ? x in ex | renM ρ? y in ey
  renM-sound ρ? ρ h (muli x y) refl | ok x′ | ok y′ = cong₂ muli (renM-sound ρ? ρ h x ex) (renM-sound ρ? ρ h y ey)
  renM-sound ρ? ρ h (addt t u) eq with renM ρ? t in et | renM ρ? u in eu
  renM-sound ρ? ρ h (addt t u) refl | ok t′ | ok u′ = cong₂ addt (renM-sound ρ? ρ h t et) (renM-sound ρ? ρ h u eu)
  renM-sound ρ? ρ h (toi64 t) eq with renM ρ? t in et
  renM-sound ρ? ρ h (toi64 t) refl | ok t′ = cong toi64 (renM-sound ρ? ρ h t et)
  renM-sound ρ? ρ h (packi x y) eq with renM ρ? x in ex | renM ρ? y in ey
  renM-sound ρ? ρ h (packi x y) refl | ok x′ | ok y′ = cong₂ packi (renM-sound ρ? ρ h x ex) (renM-sound ρ? ρ h y ey)

  renMList-sound : ∀ {n m} (ρ? : Fin n → Result (Fin m)) (ρ : Fin m → Fin n) → Inv ρ? ρ
    → (ts : List (Tm n)) {us : List (Tm m)} → renMList ρ? ts ≡ ok us → renList ρ us ≡ ts
  renMList-sound ρ? ρ h [] refl = refl
  renMList-sound ρ? ρ h (t ∷ ts) eq with renM ρ? t in et | renMList ρ? ts in ets
  renMList-sound ρ? ρ h (t ∷ ts) refl | ok t′ | ok ts′ = cong₂ _∷_ (renM-sound ρ? ρ h t et) (renMList-sound ρ? ρ h ts ets)

unwk-inv : ∀ {n} → Inv (unwk {n}) suc
unwk-inv (suc i) j refl = refl

-- strengthen T = ok C means T is C weakened once.
strengthen-sound : ∀ {n} (T : Tm (suc n)) {C : Tm n}
  → strengthen T ≡ ok C → T ≡ wk C
strengthen-sound T eq = sym (renM-sound unwk suc unwk-inv T eq)

unwk₂-inv : ∀ {n} → Inv (unwk₂ {n}) (λ i → suc (suc i))
unwk₂-inv (suc (suc i)) j refl = refl

-- strengthen₂ T = ok C means T is C weakened twice.
strengthen₂-sound : ∀ {n} (T : Tm (suc (suc n))) {C : Tm n}
  → strengthen₂ T ≡ ok C → T ≡ wk (wk C)
strengthen₂-sound T {C} eq =
  trans (sym (renM-sound unwk₂ (λ i → suc (suc i)) unwk₂-inv T eq)) (sym (ren-ren suc suc C))

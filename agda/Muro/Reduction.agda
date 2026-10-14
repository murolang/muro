------------------------------------------------------------------------
-- Parallel reduction σ ⊢[ m ] t ⇛ u (Tait / Martin-Löf / Takahashi):
-- contract any set of the redexes present in t at once. Redexes are
--   δ    def i             ⇛ closed body      (allowedDef permits m)
--   β    app (lam q A t) a ⇛ inst t′ a′
--   ι    mNat ze / mNat (su u) / mUnit one / rwt rfl /
--        letp (pair a b) t  ⇛ inst₂ t′ a′ b′
--   ann  ann e A           ⇛ e′
-- and ⇛ is a congruence for every constructor of Tm, so it is closed
-- under substitution (⇛-sub). Confluence is by the triangle property:
-- every u with t ⇛ u satisfies u ⇛ dev t, where dev t is the complete
-- development of t. Hence ⇛* is confluent, and the conversion that ⇛
-- generates (Muro.Convert) is joinability.
--
-- Nothing here is about typing. ν and unfold have congruence rules and
-- no redex of their own. uncons of an unfold contracts when instantiating
-- the λ-body at the seed is already a pair (the body is a pair, or it is
-- the variable and the seed is a pair). That is the step uncons reads.
-- Tensor and the numeric formers have congruence rules and no redexes.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Reduction where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
import Data.Fin.Base as Fin
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; ∃; proj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.SubstLemmas
open import Muro.Env
open import Muro.Spine

infix 3 _⊢[_]_⇛_ _⊢[_]_⇛L_ _⊢[_]_⇛*_

data _⊢[_]_⇛_ (σ : Sig) (m : Mode) {n} : Tm n → Tm n → Set
data _⊢[_]_⇛L_ (σ : Sig) (m : Mode) {n} : List (Tm n) → List (Tm n) → Set

data _⊢[_]_⇛_ σ m where
  -- redexes
  ⇛-δ : ∀ {i d}
    → lookupDef σ i ≡ ok d
    → allowedDef (Def.dmode d) m ≡ true
    → σ ⊢[ m ] def i ⇛ closed (Def.dbody d)
  ⇛-β : ∀ {q A t t′ a a′}
    → σ ⊢[ m ] t ⇛ t′ → σ ⊢[ m ] a ⇛ a′
    → σ ⊢[ m ] app (lam q A t) a ⇛ inst t′ a′
  ⇛-ιz : ∀ {P z z′ s}
    → σ ⊢[ m ] z ⇛ z′
    → σ ⊢[ m ] mNat ze P z s ⇛ z′
  ⇛-ιs : ∀ {u u′ P z s s′}
    → σ ⊢[ m ] u ⇛ u′ → σ ⊢[ m ] s ⇛ s′
    → σ ⊢[ m ] mNat (su u) P z s ⇛ inst s′ u′
  ⇛-ιtt : ∀ {P u u′}
    → σ ⊢[ m ] u ⇛ u′
    → σ ⊢[ m ] mUnit one P u ⇛ u′
  ⇛-ιrfl : ∀ {P t t′}
    → σ ⊢[ m ] t ⇛ t′
    → σ ⊢[ m ] rwt rfl P t ⇛ t′
  ⇛-ann : ∀ {e e′ A}
    → σ ⊢[ m ] e ⇛ e′
    → σ ⊢[ m ] ann e A ⇛ e′
  -- let (a, b) = (a₀, b₀) in t: both binders at once
  ⇛-ιletp : ∀ {a a′ b b′ t t′}
    → σ ⊢[ m ] a ⇛ a′ → σ ⊢[ m ] b ⇛ b′ → σ ⊢[ m ] t ⇛ t′
    → σ ⊢[ m ] letp (pair a b) t ⇛ inst₂ t′ a′ b′
  -- uncons (unfold s (λ _ → (h, t))): instantiation is already the pair.
  -- The tail keeps the reduced λ, the way β keeps the reduced body.
  ⇛-ιβp : ∀ {q A A′ h h′ t t′ s s′}
    → σ ⊢[ m ] h ⇛ h′ → σ ⊢[ m ] t ⇛ t′ → σ ⊢[ m ] s ⇛ s′ → σ ⊢[ m ] A ⇛ A′
    → σ ⊢[ m ] ucons (unf s (lam q A (pair h t)))
      ⇛ pair (inst h′ s′) (unf (inst t′ s′) (lam q A′ (pair h′ t′)))
  -- uncons (unfold (a, b) (λ s → s)): the seed is the pair.
  ⇛-ιβ0 : ∀ {q A A′ a a′ b b′}
    → σ ⊢[ m ] a ⇛ a′ → σ ⊢[ m ] b ⇛ b′ → σ ⊢[ m ] A ⇛ A′
    → σ ⊢[ m ] ucons (unf (pair a b) (lam q A (var zero)))
      ⇛ pair a′ (unf b′ (lam q A′ (var zero)))
  -- uncons (unfold s (h, t)): the pair is already the step. A declared
  -- family's tail is the proof at the next indices, not a new seed.
  ⇛-ιβr : ∀ {h h′ t t′ s s′}
    → σ ⊢[ m ] h ⇛ h′ → σ ⊢[ m ] t ⇛ t′ → σ ⊢[ m ] s ⇛ s′
    → σ ⊢[ m ] ucons (unf s (pair h t)) ⇛ pair h′ t′
  -- match on a constructor application: the j-th branch applied to the
  -- constructor's arguments (Check.dataWhnf)
  ⇛-ιdata : ∀ {i j as as′ e P bs b b′}
    → Spine (ctor i j) as e
    → lookupList bs j ≡ ok b
    → σ ⊢[ m ] as ⇛L as′ → σ ⊢[ m ] b ⇛ b′
    → σ ⊢[ m ] mData e P bs ⇛ appsFrom b′ as′
  -- congruence
  ⇛-var   : ∀ {x} → σ ⊢[ m ] var x ⇛ var x
  ⇛-typ   : σ ⊢[ m ] typ ⇛ typ
  ⇛-pi    : ∀ {q A A′ B B′} → σ ⊢[ m ] A ⇛ A′ → σ ⊢[ m ] B ⇛ B′
    → σ ⊢[ m ] pi q A B ⇛ pi q A′ B′
  ⇛-lam   : ∀ {q A A′ t t′} → σ ⊢[ m ] A ⇛ A′ → σ ⊢[ m ] t ⇛ t′
    → σ ⊢[ m ] lam q A t ⇛ lam q A′ t′
  ⇛-app   : ∀ {f f′ a a′} → σ ⊢[ m ] f ⇛ f′ → σ ⊢[ m ] a ⇛ a′
    → σ ⊢[ m ] app f a ⇛ app f′ a′
  ⇛-nat   : σ ⊢[ m ] nat ⇛ nat
  ⇛-ze    : σ ⊢[ m ] ze ⇛ ze
  ⇛-su    : ∀ {t t′} → σ ⊢[ m ] t ⇛ t′ → σ ⊢[ m ] su t ⇛ su t′
  ⇛-unit  : σ ⊢[ m ] unit ⇛ unit
  ⇛-one   : σ ⊢[ m ] one ⇛ one
  ⇛-empty : σ ⊢[ m ] empty ⇛ empty
  ⇛-dty   : ∀ {i} → σ ⊢[ m ] dty i ⇛ dty i
  ⇛-ctor  : ∀ {i j} → σ ⊢[ m ] ctor i j ⇛ ctor i j
  ⇛-mData : ∀ {e e′ P P′ bs bs′}
    → σ ⊢[ m ] e ⇛ e′ → σ ⊢[ m ] P ⇛ P′ → σ ⊢[ m ] bs ⇛L bs′
    → σ ⊢[ m ] mData e P bs ⇛ mData e′ P′ bs′
  ⇛-mNat  : ∀ {e e′ P P′ z z′ s s′}
    → σ ⊢[ m ] e ⇛ e′ → σ ⊢[ m ] P ⇛ P′ → σ ⊢[ m ] z ⇛ z′ → σ ⊢[ m ] s ⇛ s′
    → σ ⊢[ m ] mNat e P z s ⇛ mNat e′ P′ z′ s′
  ⇛-mEmp  : ∀ {e e′ P P′}
    → σ ⊢[ m ] e ⇛ e′ → σ ⊢[ m ] P ⇛ P′
    → σ ⊢[ m ] mEmp e P ⇛ mEmp e′ P′
  ⇛-mUnit : ∀ {e e′ P P′ u u′}
    → σ ⊢[ m ] e ⇛ e′ → σ ⊢[ m ] P ⇛ P′ → σ ⊢[ m ] u ⇛ u′
    → σ ⊢[ m ] mUnit e P u ⇛ mUnit e′ P′ u′
  ⇛-idt   : ∀ {A A′ a a′ b b′}
    → σ ⊢[ m ] A ⇛ A′ → σ ⊢[ m ] a ⇛ a′ → σ ⊢[ m ] b ⇛ b′
    → σ ⊢[ m ] idt A a b ⇛ idt A′ a′ b′
  ⇛-rfl   : σ ⊢[ m ] rfl ⇛ rfl
  ⇛-rwt   : ∀ {e e′ P P′ t t′}
    → σ ⊢[ m ] e ⇛ e′ → σ ⊢[ m ] P ⇛ P′ → σ ⊢[ m ] t ⇛ t′
    → σ ⊢[ m ] rwt e P t ⇛ rwt e′ P′ t′
  ⇛-def   : ∀ {i} → σ ⊢[ m ] def i ⇛ def i
  ⇛-annc  : ∀ {e e′ A A′} → σ ⊢[ m ] e ⇛ e′ → σ ⊢[ m ] A ⇛ A′
    → σ ⊢[ m ] ann e A ⇛ ann e′ A′
  ⇛-prod  : ∀ {A A′ B B′} → σ ⊢[ m ] A ⇛ A′ → σ ⊢[ m ] B ⇛ B′
    → σ ⊢[ m ] prod A B ⇛ prod A′ B′
  ⇛-pair  : ∀ {a a′ b b′} → σ ⊢[ m ] a ⇛ a′ → σ ⊢[ m ] b ⇛ b′
    → σ ⊢[ m ] pair a b ⇛ pair a′ b′
  ⇛-letp  : ∀ {e e′ t t′} → σ ⊢[ m ] e ⇛ e′ → σ ⊢[ m ] t ⇛ t′
    → σ ⊢[ m ] letp e t ⇛ letp e′ t′
  ⇛-nu    : ∀ {F F′} → σ ⊢[ m ] F ⇛ F′ → σ ⊢[ m ] nu F ⇛ nu F′
  ⇛-unf   : ∀ {s s′ f f′} → σ ⊢[ m ] s ⇛ s′ → σ ⊢[ m ] f ⇛ f′
    → σ ⊢[ m ] unf s f ⇛ unf s′ f′
  ⇛-ucons : ∀ {s s′} → σ ⊢[ m ] s ⇛ s′ → σ ⊢[ m ] ucons s ⇛ ucons s′
  ⇛-i64   : σ ⊢[ m ] i64 ⇛ i64
  ⇛-f32ty : σ ⊢[ m ] f32ty ⇛ f32ty
  ⇛-tensor : ∀ {d d′ s s′} → σ ⊢[ m ] d ⇛ d′ → σ ⊢[ m ] s ⇛ s′
    → σ ⊢[ m ] tensor d s ⇛ tensor d′ s′
  ⇛-addi  : ∀ {x x′ y y′} → σ ⊢[ m ] x ⇛ x′ → σ ⊢[ m ] y ⇛ y′
    → σ ⊢[ m ] addi x y ⇛ addi x′ y′
  ⇛-muli  : ∀ {x x′ y y′} → σ ⊢[ m ] x ⇛ x′ → σ ⊢[ m ] y ⇛ y′
    → σ ⊢[ m ] muli x y ⇛ muli x′ y′
  ⇛-addt  : ∀ {t t′ u u′} → σ ⊢[ m ] t ⇛ t′ → σ ⊢[ m ] u ⇛ u′
    → σ ⊢[ m ] addt t u ⇛ addt t′ u′
  ⇛-toi64 : ∀ {t t′} → σ ⊢[ m ] t ⇛ t′ → σ ⊢[ m ] toi64 t ⇛ toi64 t′
  ⇛-packi : ∀ {x x′ y y′} → σ ⊢[ m ] x ⇛ x′ → σ ⊢[ m ] y ⇛ y′
    → σ ⊢[ m ] packi x y ⇛ packi x′ y′

data _⊢[_]_⇛L_ σ m where
  ⇛L-[] : σ ⊢[ m ] [] ⇛L []
  ⇛L-∷  : ∀ {t t′ ts ts′} → σ ⊢[ m ] t ⇛ t′ → σ ⊢[ m ] ts ⇛L ts′
    → σ ⊢[ m ] (t ∷ ts) ⇛L (t′ ∷ ts′)

------------------------------------------------------------------------
-- Reflexivity.
------------------------------------------------------------------------

mutual
  ⇛-refl : ∀ {σ m n} (t : Tm n) → σ ⊢[ m ] t ⇛ t
  ⇛-refl (var x) = ⇛-var
  ⇛-refl typ = ⇛-typ
  ⇛-refl (pi q A B) = ⇛-pi (⇛-refl A) (⇛-refl B)
  ⇛-refl (lam q A t) = ⇛-lam (⇛-refl A) (⇛-refl t)
  ⇛-refl (app f a) = ⇛-app (⇛-refl f) (⇛-refl a)
  ⇛-refl nat = ⇛-nat
  ⇛-refl ze = ⇛-ze
  ⇛-refl (su t) = ⇛-su (⇛-refl t)
  ⇛-refl unit = ⇛-unit
  ⇛-refl one = ⇛-one
  ⇛-refl empty = ⇛-empty
  ⇛-refl (dty i) = ⇛-dty
  ⇛-refl (ctor i j) = ⇛-ctor
  ⇛-refl (mData e P bs) = ⇛-mData (⇛-refl e) (⇛-refl P) (⇛L-refl bs)
  ⇛-refl (mNat e P z s) = ⇛-mNat (⇛-refl e) (⇛-refl P) (⇛-refl z) (⇛-refl s)
  ⇛-refl (mEmp e P) = ⇛-mEmp (⇛-refl e) (⇛-refl P)
  ⇛-refl (mUnit e P u) = ⇛-mUnit (⇛-refl e) (⇛-refl P) (⇛-refl u)
  ⇛-refl (idt A a b) = ⇛-idt (⇛-refl A) (⇛-refl a) (⇛-refl b)
  ⇛-refl rfl = ⇛-rfl
  ⇛-refl (rwt e P t) = ⇛-rwt (⇛-refl e) (⇛-refl P) (⇛-refl t)
  ⇛-refl (def i) = ⇛-def
  ⇛-refl (ann e A) = ⇛-annc (⇛-refl e) (⇛-refl A)
  ⇛-refl (prod A B) = ⇛-prod (⇛-refl A) (⇛-refl B)
  ⇛-refl (pair a b) = ⇛-pair (⇛-refl a) (⇛-refl b)
  ⇛-refl (letp e t) = ⇛-letp (⇛-refl e) (⇛-refl t)
  ⇛-refl (nu F) = ⇛-nu (⇛-refl F)
  ⇛-refl (unf s f) = ⇛-unf (⇛-refl s) (⇛-refl f)
  ⇛-refl (ucons s) = ⇛-ucons (⇛-refl s)
  ⇛-refl i64 = ⇛-i64
  ⇛-refl f32ty = ⇛-f32ty
  ⇛-refl (tensor d s) = ⇛-tensor (⇛-refl d) (⇛-refl s)
  ⇛-refl (addi x y) = ⇛-addi (⇛-refl x) (⇛-refl y)
  ⇛-refl (muli x y) = ⇛-muli (⇛-refl x) (⇛-refl y)
  ⇛-refl (addt t u) = ⇛-addt (⇛-refl t) (⇛-refl u)
  ⇛-refl (toi64 t) = ⇛-toi64 (⇛-refl t)
  ⇛-refl (packi x y) = ⇛-packi (⇛-refl x) (⇛-refl y)

  ⇛L-refl : ∀ {σ m n} (ts : List (Tm n)) → σ ⊢[ m ] ts ⇛L ts
  ⇛L-refl [] = ⇛L-[]
  ⇛L-refl (t ∷ ts) = ⇛L-∷ (⇛-refl t) (⇛L-refl ts)

------------------------------------------------------------------------
-- Mode monotonicity: only δ looks at the mode.
------------------------------------------------------------------------

mutual
  ⇛-mode : ∀ {σ m m′ n} {t u : Tm n} → m ≤ᵐ m′ → σ ⊢[ m ] t ⇛ u → σ ⊢[ m′ ] t ⇛ u
  ⇛-mode h (⇛-δ {d = d} lk al) = ⇛-δ lk (allowedDef-mono (Def.dmode d) h al)
  ⇛-mode h (⇛-β t a) = ⇛-β (⇛-mode h t) (⇛-mode h a)
  ⇛-mode h (⇛-ιz z) = ⇛-ιz (⇛-mode h z)
  ⇛-mode h (⇛-ιs u s) = ⇛-ιs (⇛-mode h u) (⇛-mode h s)
  ⇛-mode h (⇛-ιtt u) = ⇛-ιtt (⇛-mode h u)
  ⇛-mode h (⇛-ιrfl t) = ⇛-ιrfl (⇛-mode h t)
  ⇛-mode h (⇛-ann e) = ⇛-ann (⇛-mode h e)
  ⇛-mode h (⇛-ιletp a b t) = ⇛-ιletp (⇛-mode h a) (⇛-mode h b) (⇛-mode h t)
  ⇛-mode h (⇛-ιβp dh dt ds dA) =
    ⇛-ιβp (⇛-mode h dh) (⇛-mode h dt) (⇛-mode h ds) (⇛-mode h dA)
  ⇛-mode h (⇛-ιβ0 da db dA) = ⇛-ιβ0 (⇛-mode h da) (⇛-mode h db) (⇛-mode h dA)
  ⇛-mode h (⇛-ιβr dh dt ds) = ⇛-ιβr (⇛-mode h dh) (⇛-mode h dt) (⇛-mode h ds)
  ⇛-mode h (⇛-ιdata sp lk as b) = ⇛-ιdata sp lk (⇛L-mode h as) (⇛-mode h b)
  ⇛-mode h ⇛-var = ⇛-var
  ⇛-mode h ⇛-typ = ⇛-typ
  ⇛-mode h (⇛-pi A B) = ⇛-pi (⇛-mode h A) (⇛-mode h B)
  ⇛-mode h (⇛-lam A t) = ⇛-lam (⇛-mode h A) (⇛-mode h t)
  ⇛-mode h (⇛-app f a) = ⇛-app (⇛-mode h f) (⇛-mode h a)
  ⇛-mode h ⇛-nat = ⇛-nat
  ⇛-mode h ⇛-ze = ⇛-ze
  ⇛-mode h (⇛-su t) = ⇛-su (⇛-mode h t)
  ⇛-mode h ⇛-unit = ⇛-unit
  ⇛-mode h ⇛-one = ⇛-one
  ⇛-mode h ⇛-empty = ⇛-empty
  ⇛-mode h ⇛-dty = ⇛-dty
  ⇛-mode h ⇛-ctor = ⇛-ctor
  ⇛-mode h (⇛-mData e P bs) = ⇛-mData (⇛-mode h e) (⇛-mode h P) (⇛L-mode h bs)
  ⇛-mode h (⇛-mNat e P z s) =
    ⇛-mNat (⇛-mode h e) (⇛-mode h P) (⇛-mode h z) (⇛-mode h s)
  ⇛-mode h (⇛-mEmp e P) = ⇛-mEmp (⇛-mode h e) (⇛-mode h P)
  ⇛-mode h (⇛-mUnit e P u) = ⇛-mUnit (⇛-mode h e) (⇛-mode h P) (⇛-mode h u)
  ⇛-mode h (⇛-idt A a b) = ⇛-idt (⇛-mode h A) (⇛-mode h a) (⇛-mode h b)
  ⇛-mode h ⇛-rfl = ⇛-rfl
  ⇛-mode h (⇛-rwt e P t) = ⇛-rwt (⇛-mode h e) (⇛-mode h P) (⇛-mode h t)
  ⇛-mode h ⇛-def = ⇛-def
  ⇛-mode h (⇛-annc e A) = ⇛-annc (⇛-mode h e) (⇛-mode h A)
  ⇛-mode h (⇛-prod A B) = ⇛-prod (⇛-mode h A) (⇛-mode h B)
  ⇛-mode h (⇛-pair a b) = ⇛-pair (⇛-mode h a) (⇛-mode h b)
  ⇛-mode h (⇛-letp e t) = ⇛-letp (⇛-mode h e) (⇛-mode h t)
  ⇛-mode h (⇛-nu F) = ⇛-nu (⇛-mode h F)
  ⇛-mode h (⇛-unf s f) = ⇛-unf (⇛-mode h s) (⇛-mode h f)
  ⇛-mode h (⇛-ucons s) = ⇛-ucons (⇛-mode h s)
  ⇛-mode h ⇛-i64 = ⇛-i64
  ⇛-mode h ⇛-f32ty = ⇛-f32ty
  ⇛-mode h (⇛-tensor d s) = ⇛-tensor (⇛-mode h d) (⇛-mode h s)
  ⇛-mode h (⇛-addi x y) = ⇛-addi (⇛-mode h x) (⇛-mode h y)
  ⇛-mode h (⇛-muli x y) = ⇛-muli (⇛-mode h x) (⇛-mode h y)
  ⇛-mode h (⇛-addt t u) = ⇛-addt (⇛-mode h t) (⇛-mode h u)
  ⇛-mode h (⇛-toi64 t) = ⇛-toi64 (⇛-mode h t)
  ⇛-mode h (⇛-packi x y) = ⇛-packi (⇛-mode h x) (⇛-mode h y)

  ⇛L-mode : ∀ {σ m m′ n} {ts us : List (Tm n)} → m ≤ᵐ m′
    → σ ⊢[ m ] ts ⇛L us → σ ⊢[ m′ ] ts ⇛L us
  ⇛L-mode h ⇛L-[] = ⇛L-[]
  ⇛L-mode h (⇛L-∷ t ts) = ⇛L-∷ (⇛-mode h t) (⇛L-mode h ts)

------------------------------------------------------------------------
-- Renaming.
------------------------------------------------------------------------

mutual
  ⇛-ren : ∀ {σ m n k} (ρ : Fin n → Fin k) {t u : Tm n}
    → σ ⊢[ m ] t ⇛ u → σ ⊢[ m ] ren ρ t ⇛ ren ρ u
  ⇛-ren ρ (⇛-δ {d = d} lk al) rewrite closed-ren ρ (Def.dbody d) = ⇛-δ lk al
  ⇛-ren ρ (⇛-β {t′ = t′} {a′ = a′} t a) rewrite ren-inst ρ t′ a′ =
    ⇛-β (⇛-ren (lift ρ) t) (⇛-ren ρ a)
  ⇛-ren ρ (⇛-ιz z) = ⇛-ιz (⇛-ren ρ z)
  ⇛-ren ρ (⇛-ιs {u′ = u′} {s′ = s′} u s) rewrite ren-inst ρ s′ u′ =
    ⇛-ιs (⇛-ren ρ u) (⇛-ren (lift ρ) s)
  ⇛-ren ρ (⇛-ιtt u) = ⇛-ιtt (⇛-ren ρ u)
  ⇛-ren ρ (⇛-ιrfl t) = ⇛-ιrfl (⇛-ren ρ t)
  ⇛-ren ρ (⇛-ann e) = ⇛-ann (⇛-ren ρ e)
  ⇛-ren ρ (⇛-ιletp {a′ = a′} {b′ = b′} {t′ = t′} a b t) rewrite ren-inst₂ ρ t′ a′ b′ =
    ⇛-ιletp (⇛-ren ρ a) (⇛-ren ρ b) (⇛-ren (lift (lift ρ)) t)
  ⇛-ren ρ (⇛-ιβp {h′ = h′} {t′ = t′} {s′ = s′} dh dt ds dA)
    rewrite ren-inst ρ h′ s′ | ren-inst ρ t′ s′ =
    ⇛-ιβp (⇛-ren (lift ρ) dh) (⇛-ren (lift ρ) dt) (⇛-ren ρ ds) (⇛-ren ρ dA)
  ⇛-ren ρ (⇛-ιβ0 da db dA) = ⇛-ιβ0 (⇛-ren ρ da) (⇛-ren ρ db) (⇛-ren ρ dA)
  ⇛-ren ρ (⇛-ιβr dh dt ds) = ⇛-ιβr (⇛-ren ρ dh) (⇛-ren ρ dt) (⇛-ren ρ ds)
  ⇛-ren ρ (⇛-ιdata {as′ = as′} {bs = bs} {b′ = b′} sp lk as b)
    rewrite ren-appsFrom ρ b′ as′ =
    ⇛-ιdata (Spine-ren ρ sp) (lookupList-ren ρ bs _ lk) (⇛L-ren ρ as) (⇛-ren ρ b)
  ⇛-ren ρ ⇛-var = ⇛-var
  ⇛-ren ρ ⇛-typ = ⇛-typ
  ⇛-ren ρ (⇛-pi A B) = ⇛-pi (⇛-ren ρ A) (⇛-ren (lift ρ) B)
  ⇛-ren ρ (⇛-lam A t) = ⇛-lam (⇛-ren ρ A) (⇛-ren (lift ρ) t)
  ⇛-ren ρ (⇛-app f a) = ⇛-app (⇛-ren ρ f) (⇛-ren ρ a)
  ⇛-ren ρ ⇛-nat = ⇛-nat
  ⇛-ren ρ ⇛-ze = ⇛-ze
  ⇛-ren ρ (⇛-su t) = ⇛-su (⇛-ren ρ t)
  ⇛-ren ρ ⇛-unit = ⇛-unit
  ⇛-ren ρ ⇛-one = ⇛-one
  ⇛-ren ρ ⇛-empty = ⇛-empty
  ⇛-ren ρ ⇛-dty = ⇛-dty
  ⇛-ren ρ ⇛-ctor = ⇛-ctor
  ⇛-ren ρ (⇛-mData e P bs) =
    ⇛-mData (⇛-ren ρ e) (⇛-ren (lift ρ) P) (⇛L-ren ρ bs)
  ⇛-ren ρ (⇛-mNat e P z s) =
    ⇛-mNat (⇛-ren ρ e) (⇛-ren (lift ρ) P) (⇛-ren ρ z) (⇛-ren (lift ρ) s)
  ⇛-ren ρ (⇛-mEmp e P) = ⇛-mEmp (⇛-ren ρ e) (⇛-ren (lift ρ) P)
  ⇛-ren ρ (⇛-mUnit e P u) = ⇛-mUnit (⇛-ren ρ e) (⇛-ren (lift ρ) P) (⇛-ren ρ u)
  ⇛-ren ρ (⇛-idt A a b) = ⇛-idt (⇛-ren ρ A) (⇛-ren ρ a) (⇛-ren ρ b)
  ⇛-ren ρ ⇛-rfl = ⇛-rfl
  ⇛-ren ρ (⇛-rwt e P t) = ⇛-rwt (⇛-ren ρ e) (⇛-ren (lift ρ) P) (⇛-ren ρ t)
  ⇛-ren ρ ⇛-def = ⇛-def
  ⇛-ren ρ (⇛-annc e A) = ⇛-annc (⇛-ren ρ e) (⇛-ren ρ A)
  ⇛-ren ρ (⇛-prod A B) = ⇛-prod (⇛-ren ρ A) (⇛-ren ρ B)
  ⇛-ren ρ (⇛-pair a b) = ⇛-pair (⇛-ren ρ a) (⇛-ren ρ b)
  ⇛-ren ρ (⇛-letp e t) = ⇛-letp (⇛-ren ρ e) (⇛-ren (lift (lift ρ)) t)
  ⇛-ren ρ (⇛-nu F) = ⇛-nu (⇛-ren (lift ρ) F)
  ⇛-ren ρ (⇛-unf s f) = ⇛-unf (⇛-ren ρ s) (⇛-ren ρ f)
  ⇛-ren ρ (⇛-ucons s) = ⇛-ucons (⇛-ren ρ s)
  ⇛-ren ρ ⇛-i64 = ⇛-i64
  ⇛-ren ρ ⇛-f32ty = ⇛-f32ty
  ⇛-ren ρ (⇛-tensor d s) = ⇛-tensor (⇛-ren ρ d) (⇛-ren ρ s)
  ⇛-ren ρ (⇛-addi x y) = ⇛-addi (⇛-ren ρ x) (⇛-ren ρ y)
  ⇛-ren ρ (⇛-muli x y) = ⇛-muli (⇛-ren ρ x) (⇛-ren ρ y)
  ⇛-ren ρ (⇛-addt t u) = ⇛-addt (⇛-ren ρ t) (⇛-ren ρ u)
  ⇛-ren ρ (⇛-toi64 t) = ⇛-toi64 (⇛-ren ρ t)
  ⇛-ren ρ (⇛-packi x y) = ⇛-packi (⇛-ren ρ x) (⇛-ren ρ y)

  ⇛L-ren : ∀ {σ m n k} (ρ : Fin n → Fin k) {ts us : List (Tm n)}
    → σ ⊢[ m ] ts ⇛L us → σ ⊢[ m ] renList ρ ts ⇛L renList ρ us
  ⇛L-ren ρ ⇛L-[] = ⇛L-[]
  ⇛L-ren ρ (⇛L-∷ t ts) = ⇛L-∷ (⇛-ren ρ t) (⇛L-ren ρ ts)

------------------------------------------------------------------------
-- Substitution: both the term and the substitution may reduce.
------------------------------------------------------------------------

_⊢[_]_⇛σ_ : ∀ {n k} → Sig → Mode → (Fin n → Tm k) → (Fin n → Tm k) → Set
σ ⊢[ m ] τ ⇛σ τ′ = ∀ x → σ ⊢[ m ] τ x ⇛ τ′ x

⇛σ-lifts : ∀ {σ m n k} {τ τ′ : Fin n → Tm k}
  → σ ⊢[ m ] τ ⇛σ τ′ → σ ⊢[ m ] lifts τ ⇛σ lifts τ′
⇛σ-lifts h zero    = ⇛-var
⇛σ-lifts h (suc i) = ⇛-ren suc (h i)

mutual
  ⇛-sub : ∀ {σ m n k} {τ τ′ : Fin n → Tm k} {t u : Tm n}
    → σ ⊢[ m ] τ ⇛σ τ′ → σ ⊢[ m ] t ⇛ u → σ ⊢[ m ] sub τ t ⇛ sub τ′ u
  ⇛-sub {τ′ = τ′} h (⇛-δ {d = d} lk al) rewrite closed-sub τ′ (Def.dbody d) = ⇛-δ lk al
  ⇛-sub {τ′ = τ′} h (⇛-β {t′ = t′} {a′ = a′} t a) rewrite sub-inst τ′ t′ a′ =
    ⇛-β (⇛-sub (⇛σ-lifts h) t) (⇛-sub h a)
  ⇛-sub h (⇛-ιz z) = ⇛-ιz (⇛-sub h z)
  ⇛-sub {τ′ = τ′} h (⇛-ιs {u′ = u′} {s′ = s′} u s) rewrite sub-inst τ′ s′ u′ =
    ⇛-ιs (⇛-sub h u) (⇛-sub (⇛σ-lifts h) s)
  ⇛-sub h (⇛-ιtt u) = ⇛-ιtt (⇛-sub h u)
  ⇛-sub h (⇛-ιrfl t) = ⇛-ιrfl (⇛-sub h t)
  ⇛-sub h (⇛-ann e) = ⇛-ann (⇛-sub h e)
  ⇛-sub {τ′ = τ′} h (⇛-ιletp {a′ = a′} {b′ = b′} {t′ = t′} a b t) rewrite sub-inst₂ τ′ t′ a′ b′ =
    ⇛-ιletp (⇛-sub h a) (⇛-sub h b) (⇛-sub (⇛σ-lifts (⇛σ-lifts h)) t)
  ⇛-sub {τ′ = τ′} h (⇛-ιβp {h′ = h′} {t′ = t′} {s′ = s′} dh dt ds dA)
    rewrite sub-inst τ′ h′ s′ | sub-inst τ′ t′ s′ =
    ⇛-ιβp (⇛-sub (⇛σ-lifts h) dh) (⇛-sub (⇛σ-lifts h) dt) (⇛-sub h ds) (⇛-sub h dA)
  ⇛-sub h (⇛-ιβ0 da db dA) = ⇛-ιβ0 (⇛-sub h da) (⇛-sub h db) (⇛-sub h dA)
  ⇛-sub h (⇛-ιβr dh dt ds) = ⇛-ιβr (⇛-sub h dh) (⇛-sub h dt) (⇛-sub h ds)
  ⇛-sub {τ′ = τ′} h (⇛-ιdata {as′ = as′} {bs = bs} {b′ = b′} sp lk as b)
    rewrite sub-appsFrom τ′ b′ as′ =
    ⇛-ιdata (Spine-sub _ sp) (lookupList-sub _ bs _ lk) (⇛L-sub h as) (⇛-sub h b)
  ⇛-sub h (⇛-var {x}) = h x
  ⇛-sub h ⇛-typ = ⇛-typ
  ⇛-sub h (⇛-pi A B) = ⇛-pi (⇛-sub h A) (⇛-sub (⇛σ-lifts h) B)
  ⇛-sub h (⇛-lam A t) = ⇛-lam (⇛-sub h A) (⇛-sub (⇛σ-lifts h) t)
  ⇛-sub h (⇛-app f a) = ⇛-app (⇛-sub h f) (⇛-sub h a)
  ⇛-sub h ⇛-nat = ⇛-nat
  ⇛-sub h ⇛-ze = ⇛-ze
  ⇛-sub h (⇛-su t) = ⇛-su (⇛-sub h t)
  ⇛-sub h ⇛-unit = ⇛-unit
  ⇛-sub h ⇛-one = ⇛-one
  ⇛-sub h ⇛-empty = ⇛-empty
  ⇛-sub h ⇛-dty = ⇛-dty
  ⇛-sub h ⇛-ctor = ⇛-ctor
  ⇛-sub h (⇛-mData e P bs) =
    ⇛-mData (⇛-sub h e) (⇛-sub (⇛σ-lifts h) P) (⇛L-sub h bs)
  ⇛-sub h (⇛-mNat e P z s) =
    ⇛-mNat (⇛-sub h e) (⇛-sub (⇛σ-lifts h) P) (⇛-sub h z) (⇛-sub (⇛σ-lifts h) s)
  ⇛-sub h (⇛-mEmp e P) = ⇛-mEmp (⇛-sub h e) (⇛-sub (⇛σ-lifts h) P)
  ⇛-sub h (⇛-mUnit e P u) = ⇛-mUnit (⇛-sub h e) (⇛-sub (⇛σ-lifts h) P) (⇛-sub h u)
  ⇛-sub h (⇛-idt A a b) = ⇛-idt (⇛-sub h A) (⇛-sub h a) (⇛-sub h b)
  ⇛-sub h ⇛-rfl = ⇛-rfl
  ⇛-sub h (⇛-rwt e P t) = ⇛-rwt (⇛-sub h e) (⇛-sub (⇛σ-lifts h) P) (⇛-sub h t)
  ⇛-sub h ⇛-def = ⇛-def
  ⇛-sub h (⇛-annc e A) = ⇛-annc (⇛-sub h e) (⇛-sub h A)
  ⇛-sub h (⇛-prod A B) = ⇛-prod (⇛-sub h A) (⇛-sub h B)
  ⇛-sub h (⇛-pair a b) = ⇛-pair (⇛-sub h a) (⇛-sub h b)
  ⇛-sub h (⇛-letp e t) = ⇛-letp (⇛-sub h e) (⇛-sub (⇛σ-lifts (⇛σ-lifts h)) t)
  ⇛-sub h (⇛-nu F) = ⇛-nu (⇛-sub (⇛σ-lifts h) F)
  ⇛-sub h (⇛-unf s f) = ⇛-unf (⇛-sub h s) (⇛-sub h f)
  ⇛-sub h (⇛-ucons s) = ⇛-ucons (⇛-sub h s)
  ⇛-sub h ⇛-i64 = ⇛-i64
  ⇛-sub h ⇛-f32ty = ⇛-f32ty
  ⇛-sub h (⇛-tensor d s) = ⇛-tensor (⇛-sub h d) (⇛-sub h s)
  ⇛-sub h (⇛-addi x y) = ⇛-addi (⇛-sub h x) (⇛-sub h y)
  ⇛-sub h (⇛-muli x y) = ⇛-muli (⇛-sub h x) (⇛-sub h y)
  ⇛-sub h (⇛-addt t u) = ⇛-addt (⇛-sub h t) (⇛-sub h u)
  ⇛-sub h (⇛-toi64 t) = ⇛-toi64 (⇛-sub h t)
  ⇛-sub h (⇛-packi x y) = ⇛-packi (⇛-sub h x) (⇛-sub h y)

  ⇛L-sub : ∀ {σ m n k} {τ τ′ : Fin n → Tm k} {ts us : List (Tm n)}
    → σ ⊢[ m ] τ ⇛σ τ′ → σ ⊢[ m ] ts ⇛L us → σ ⊢[ m ] subList τ ts ⇛L subList τ′ us
  ⇛L-sub h ⇛L-[] = ⇛L-[]
  ⇛L-sub h (⇛L-∷ t ts) = ⇛L-∷ (⇛-sub h t) (⇛L-sub h ts)

⇛σ-refl : ∀ {σ m n k} (τ : Fin n → Tm k) → σ ⊢[ m ] τ ⇛σ τ
⇛σ-refl τ x = ⇛-refl (τ x)

⇛σ-inst : ∀ {σ m n} {a a′ : Tm n}
  → σ ⊢[ m ] a ⇛ a′ → σ ⊢[ m ] instσ a ⇛σ instσ a′
⇛σ-inst d zero    = d
⇛σ-inst d (suc i) = ⇛-var

⇛-inst : ∀ {σ m n} {t t′ : Tm (suc n)} {a a′ : Tm n}
  → σ ⊢[ m ] t ⇛ t′ → σ ⊢[ m ] a ⇛ a′ → σ ⊢[ m ] inst t a ⇛ inst t′ a′
⇛-inst dt da = ⇛-sub (⇛σ-inst da) dt

⇛-inst₂ : ∀ {σ m n} {t t′ : Tm (suc (suc n))} {a a′ b b′ : Tm n}
  → σ ⊢[ m ] t ⇛ t′ → σ ⊢[ m ] a ⇛ a′ → σ ⊢[ m ] b ⇛ b′
  → σ ⊢[ m ] inst₂ t a b ⇛ inst₂ t′ a′ b′
⇛-inst₂ dt da db = ⇛-inst (⇛-inst dt (⇛-ren suc db)) da

-- Reduce only the substituted terms, or only the term.
⇛-sub-l : ∀ {σ m n k} {τ τ′ : Fin n → Tm k} (t : Tm n)
  → σ ⊢[ m ] τ ⇛σ τ′ → σ ⊢[ m ] sub τ t ⇛ sub τ′ t
⇛-sub-l t h = ⇛-sub h (⇛-refl t)

⇛-sub-r : ∀ {σ m n k} (τ : Fin n → Tm k) {t u : Tm n}
  → σ ⊢[ m ] t ⇛ u → σ ⊢[ m ] sub τ t ⇛ sub τ u
⇛-sub-r τ d = ⇛-sub (⇛σ-refl τ) d

------------------------------------------------------------------------
-- Complete development: contract every redex present in t.
------------------------------------------------------------------------

devDef′ : ∀ {n} → ℕ → Def → Bool → Tm n
devDef′ i d true  = closed (Def.dbody d)
devDef′ i d false = def i

devDef : ∀ {n} → Mode → ℕ → Result Def → Tm n
devDef m i (fail _) = def i
devDef m i (ok d)   = devDef′ i d (allowedDef (Def.dmode d) m)

-- mData: the redex is contracted iff the scrutinee is a constructor
-- application with a branch. The arguments of the developed scrutinee
-- are read back with unspine (dev-Spine: they are the developed
-- arguments), and the branch is read from the developed branch list.
devData′ : ∀ {n} → List (Tm n) → Result (Tm n) → Tm n → Tm (suc n) → List (Tm n) → Tm n
devData′ as′ (ok b′)   _  _  _   = appsFrom b′ as′
devData′ as′ (fail _)  e′ P′ bs′ = mData e′ P′ bs′

devData : ∀ {n} → Tm n × List (Tm n) → Tm n → Tm (suc n) → List (Tm n) → Tm n
devData (ctor i j , _) e′ P′ bs′ =
  devData′ (proj₂ (unspine e′)) (lookupList bs′ j) e′ P′ bs′
devData _ e′ P′ bs′ = mData e′ P′ bs′

mutual
  -- The λ-body is split before the index, and the index is split by
  -- `with`, so a `suc` index reduces. A nested `var zero` pattern next
  -- to a catch-all does not.
  dev-unf-var0 : ∀ {n} → Sig → Mode → Tm n → Qty → Tm n → Tm n
  dev-unf-var0 σ m (pair a b) q A =
    pair (dev σ m a) (unf (dev σ m b) (lam q (dev σ m A) (var zero)))
  dev-unf-var0 σ m s q A =
    ucons (unf (dev σ m s) (lam q (dev σ m A) (var zero)))

  dev-unf-var : ∀ {n} → Sig → Mode → Tm n → Qty → Tm n → Fin (suc n) → Tm n
  dev-unf-var σ m s q A Fin.zero = dev-unf-var0 σ m s q A
  dev-unf-var σ m s q A (Fin.suc j) =
    ucons (unf (dev σ m s) (lam q (dev σ m A) (var (Fin.suc j))))

  dev-unf-lam : ∀ {n} → Sig → Mode → Tm n → Qty → Tm n → Tm (suc n) → Tm n
  dev-unf-lam σ m s q A (pair h t) =
    pair (inst (dev σ m h) (dev σ m s))
         (unf (inst (dev σ m t) (dev σ m s))
              (lam q (dev σ m A) (pair (dev σ m h) (dev σ m t))))
  dev-unf-lam σ m s q A (var i) = dev-unf-var σ m s q A i
  dev-unf-lam σ m s q A b =
    ucons (unf (dev σ m s) (lam q (dev σ m A) (dev σ m b)))

  dev : ∀ {n} → Sig → Mode → Tm n → Tm n
  dev σ m (var x) = var x
  dev σ m typ = typ
  dev σ m (pi q A B) = pi q (dev σ m A) (dev σ m B)
  dev σ m (lam q A t) = lam q (dev σ m A) (dev σ m t)
  dev σ m (app (lam q A t) a) = inst (dev σ m t) (dev σ m a)
  dev σ m (app f a) = app (dev σ m f) (dev σ m a)
  dev σ m nat = nat
  dev σ m ze = ze
  dev σ m (su t) = su (dev σ m t)
  dev σ m unit = unit
  dev σ m one = one
  dev σ m empty = empty
  dev σ m (dty i) = dty i
  dev σ m (ctor i j) = ctor i j
  dev σ m (mData e P bs) = devData (unspine e) (dev σ m e) (dev σ m P) (devL σ m bs)
  dev σ m (mNat ze P z s) = dev σ m z
  dev σ m (mNat (su u) P z s) = inst (dev σ m s) (dev σ m u)
  dev σ m (mNat e P z s) = mNat (dev σ m e) (dev σ m P) (dev σ m z) (dev σ m s)
  dev σ m (mEmp e P) = mEmp (dev σ m e) (dev σ m P)
  dev σ m (mUnit one P u) = dev σ m u
  dev σ m (mUnit e P u) = mUnit (dev σ m e) (dev σ m P) (dev σ m u)
  dev σ m (idt A a b) = idt (dev σ m A) (dev σ m a) (dev σ m b)
  dev σ m rfl = rfl
  dev σ m (rwt rfl P t) = dev σ m t
  dev σ m (rwt e P t) = rwt (dev σ m e) (dev σ m P) (dev σ m t)
  dev σ m (def i) = devDef m i (lookupDef σ i)
  dev σ m (ann e A) = dev σ m e
  dev σ m (prod A B) = prod (dev σ m A) (dev σ m B)
  dev σ m (pair a b) = pair (dev σ m a) (dev σ m b)
  dev σ m (letp (pair a b) t) = inst₂ (dev σ m t) (dev σ m a) (dev σ m b)
  dev σ m (letp e t) = letp (dev σ m e) (dev σ m t)
  dev σ m (nu F) = nu (dev σ m F)
  dev σ m (unf s f) = unf (dev σ m s) (dev σ m f)
  dev σ m (ucons (unf s (pair h t))) = pair (dev σ m h) (dev σ m t)
  dev σ m (ucons (unf s (lam q A b))) = dev-unf-lam σ m s q A b
  dev σ m (ucons s) = ucons (dev σ m s)
  dev σ m i64 = i64
  dev σ m f32ty = f32ty
  dev σ m (tensor d s) = tensor (dev σ m d) (dev σ m s)
  dev σ m (addi x y) = addi (dev σ m x) (dev σ m y)
  dev σ m (muli x y) = muli (dev σ m x) (dev σ m y)
  dev σ m (addt t u) = addt (dev σ m t) (dev σ m u)
  dev σ m (toi64 t) = toi64 (dev σ m t)
  dev σ m (packi x y) = packi (dev σ m x) (dev σ m y)

  devL : ∀ {n} → Sig → Mode → List (Tm n) → List (Tm n)
  devL σ m [] = []
  devL σ m (t ∷ ts) = dev σ m t ∷ devL σ m ts

-- def i reduces to its development.
dev-def : ∀ {σ m n} (i : ℕ) → σ ⊢[ m ] def {n} i ⇛ devDef m i (lookupDef σ i)
dev-def {σ} {m} i with lookupDef σ i in lk
... | fail _ = ⇛-def
... | ok d with allowedDef (Def.dmode d) m in al
...   | true  = ⇛-δ lk al
...   | false = ⇛-def

------------------------------------------------------------------------
-- Spines with a data head (ctor or dty). The head is not a λ, so a
-- spine reduces only to a spine with the same head and reduced
-- arguments; its development is the spine of developed arguments.
------------------------------------------------------------------------

data DHead {n} : Tm n → Set where
  dh-ctor : ∀ {i j} → DHead (ctor i j)
  dh-dty  : ∀ {i} → DHead (dty i)

DHead-Head : ∀ {n} {h : Tm n} → DHead h → Head h
DHead-Head dh-ctor = head-ctor
DHead-Head dh-dty = head-dty

Spine-lam : ∀ {n} {h : Tm n} {as q A t} → DHead h → Spine h as (lam q A t) → ⊥
Spine-lam () sp-[]

⇛L-++ : ∀ {σ m n} {as as′ bs bs′ : List (Tm n)}
  → σ ⊢[ m ] as ⇛L as′ → σ ⊢[ m ] bs ⇛L bs′ → σ ⊢[ m ] (as ++ bs) ⇛L (as′ ++ bs′)
⇛L-++ ⇛L-[] r = r
⇛L-++ (⇛L-∷ a as) r = ⇛L-∷ a (⇛L-++ as r)

⇛-appsFrom : ∀ {σ m n} {f f′ : Tm n} {as as′}
  → σ ⊢[ m ] f ⇛ f′ → σ ⊢[ m ] as ⇛L as′ → σ ⊢[ m ] appsFrom f as ⇛ appsFrom f′ as′
⇛-appsFrom f ⇛L-[] = f
⇛-appsFrom f (⇛L-∷ a as) = ⇛-appsFrom (⇛-app f a) as

⇛L-lookup : ∀ {σ m n} {bs bs′ : List (Tm n)} {j b}
  → σ ⊢[ m ] bs ⇛L bs′ → lookupList bs j ≡ ok b
  → ∃ λ b′ → (lookupList bs′ j ≡ ok b′) × (σ ⊢[ m ] b ⇛ b′)
⇛L-lookup {j = zero} (⇛L-∷ t ts) refl = _ , refl , t
⇛L-lookup {j = suc j} (⇛L-∷ t ts) eq = ⇛L-lookup ts eq
⇛L-lookup {j = zero} ⇛L-[] ()
⇛L-lookup {j = suc j} ⇛L-[] ()

⇛L-lookup⁻ : ∀ {σ m n} {bs cs : List (Tm n)} {j c}
  → σ ⊢[ m ] bs ⇛L cs → lookupList cs j ≡ ok c
  → ∃ λ b → (lookupList bs j ≡ ok b) × (σ ⊢[ m ] b ⇛ c)
⇛L-lookup⁻ {j = zero} (⇛L-∷ t ts) refl = _ , refl , t
⇛L-lookup⁻ {j = suc j} (⇛L-∷ t ts) eq = ⇛L-lookup⁻ ts eq
⇛L-lookup⁻ {j = zero} ⇛L-[] ()
⇛L-lookup⁻ {j = suc j} ⇛L-[] ()

Spine-⇛ : ∀ {σ m n} {h : Tm n} {as e e′} → DHead h → Spine h as e → σ ⊢[ m ] e ⇛ e′
  → ∃ λ as′ → Spine h as′ e′ × (σ ⊢[ m ] as ⇛L as′)
Spine-⇛ dh-ctor sp-[] ⇛-ctor = [] , sp-[] , ⇛L-[]
Spine-⇛ dh-dty sp-[] ⇛-dty = [] , sp-[] , ⇛L-[]
Spine-⇛ hd (sp-snoc sp) (⇛-β _ _) = ⊥-elim (Spine-lam hd sp)
Spine-⇛ hd (sp-snoc sp) (⇛-app f a) with Spine-⇛ hd sp f
... | as′ , sp′ , as⇛ = as′ ++ (_ ∷ []) , sp-snoc sp′ , ⇛L-++ as⇛ (⇛L-∷ a ⇛L-[])

devL-++ : ∀ {σ m n} (as bs : List (Tm n)) → devL σ m (as ++ bs) ≡ devL σ m as ++ devL σ m bs
devL-++ [] bs = refl
devL-++ (a ∷ as) bs = cong (_ ∷_) (devL-++ as bs)

dev-app-Spine : ∀ {σ m n} {h : Tm n} {as f} a → DHead h → Spine h as f
  → dev σ m (app f a) ≡ app (dev σ m f) (dev σ m a)
dev-app-Spine a dh-ctor sp-[] = refl
dev-app-Spine a dh-dty sp-[] = refl
dev-app-Spine a _ (sp-snoc _) = refl

dev-DHead : ∀ {σ m n} {h : Tm n} → DHead h → dev σ m h ≡ h
dev-DHead dh-ctor = refl
dev-DHead dh-dty = refl

dev-Spine : ∀ {σ m n} {h : Tm n} {as e} → DHead h → Spine h as e
  → Spine h (devL σ m as) (dev σ m e)
dev-Spine {σ} {m} hd sp-[] rewrite dev-DHead {σ} {m} hd = sp-[]
dev-Spine {σ} {m} hd (sp-snoc {as = as} {a = a} sp)
  rewrite devL-++ {σ} {m} as (a ∷ []) | dev-app-Spine {σ} {m} a hd sp =
  sp-snoc (dev-Spine hd sp)

lookupList-devL : ∀ {σ m n} (bs : List (Tm n)) j {b}
  → lookupList bs j ≡ ok b → lookupList (devL σ m bs) j ≡ ok (dev σ m b)
lookupList-devL (b ∷ bs) zero refl = refl
lookupList-devL (b ∷ bs) (suc j) eq = lookupList-devL bs j eq
lookupList-devL [] zero ()
lookupList-devL [] (suc j) ()

lookupList-devL-fail : ∀ {σ m n} (bs : List (Tm n)) j {s}
  → lookupList bs j ≡ fail s → lookupList (devL σ m bs) j ≡ fail s
lookupList-devL-fail [] zero refl = refl
lookupList-devL-fail [] (suc j) refl = refl
lookupList-devL-fail (b ∷ bs) zero ()
lookupList-devL-fail (b ∷ bs) (suc j) eq = lookupList-devL-fail bs j eq

------------------------------------------------------------------------
-- Triangle: every one-step reduct reduces to the development.
------------------------------------------------------------------------

mutual
  tri : ∀ {σ m n} {t u : Tm n} → σ ⊢[ m ] t ⇛ u → σ ⊢[ m ] u ⇛ dev σ m t
  tri (⇛-δ lk al) rewrite lk | al = ⇛-refl _
  tri (⇛-β t a) = ⇛-inst (tri t) (tri a)
  tri (⇛-ιz z) = tri z
  tri (⇛-ιs u s) = ⇛-inst (tri s) (tri u)
  tri (⇛-ιtt u) = tri u
  tri (⇛-ιrfl t) = tri t
  tri (⇛-ann e) = tri e
  tri (⇛-ιletp a b t) = ⇛-inst₂ (tri t) (tri a) (tri b)
  tri (⇛-ιβp dh dt ds dA) =
    ⇛-pair (⇛-inst (tri dh) (tri ds))
           (⇛-unf (⇛-inst (tri dt) (tri ds))
                  (⇛-lam (tri dA) (⇛-pair (tri dh) (tri dt))))
  tri (⇛-ιβ0 da db dA) =
    ⇛-pair (tri da) (⇛-unf (tri db) (⇛-lam (tri dA) ⇛-var))
  tri (⇛-ιβr dh dt _ds) = ⇛-pair (tri dh) (tri dt)
  tri (⇛-ιdata {P = P} sp lk as b) = tri-ιdata {P = P} sp lk (triL as) (tri b)
  tri ⇛-var = ⇛-var
  tri ⇛-typ = ⇛-typ
  tri (⇛-pi A B) = ⇛-pi (tri A) (tri B)
  tri (⇛-lam A t) = ⇛-lam (tri A) (tri t)
  tri (⇛-app f a) = tri-app f (tri f) (tri a)
  tri ⇛-nat = ⇛-nat
  tri ⇛-ze = ⇛-ze
  tri (⇛-su t) = ⇛-su (tri t)
  tri ⇛-unit = ⇛-unit
  tri ⇛-one = ⇛-one
  tri ⇛-empty = ⇛-empty
  tri ⇛-dty = ⇛-dty
  tri ⇛-ctor = ⇛-ctor
  tri (⇛-mData {P = P} e P⇛ bs) = tri-mData {P = P} e (tri e) (tri P⇛) (triL bs)
  tri (⇛-mNat e P z s) = tri-mNat e (tri e) (tri P) (tri z) (tri s)
  tri (⇛-mEmp e P) = ⇛-mEmp (tri e) (tri P)
  tri (⇛-mUnit e P u) = tri-mUnit e (tri e) (tri P) (tri u)
  tri (⇛-idt A a b) = ⇛-idt (tri A) (tri a) (tri b)
  tri ⇛-rfl = ⇛-rfl
  tri (⇛-rwt e P t) = tri-rwt e (tri e) (tri P) (tri t)
  tri (⇛-def {i}) = dev-def i
  tri (⇛-annc e A) = ⇛-ann (tri e)
  tri (⇛-prod A B) = ⇛-prod (tri A) (tri B)
  tri (⇛-pair a b) = ⇛-pair (tri a) (tri b)
  tri (⇛-letp e t) = tri-letp e (tri e) (tri t)
  tri (⇛-nu F) = ⇛-nu (tri F)
  tri (⇛-unf s f) = ⇛-unf (tri s) (tri f)
  tri (⇛-ucons s) = tri-ucons s (tri s)
  tri ⇛-i64 = ⇛-i64
  tri ⇛-f32ty = ⇛-f32ty
  tri (⇛-tensor d s) = ⇛-tensor (tri d) (tri s)
  tri (⇛-addi x y) = ⇛-addi (tri x) (tri y)
  tri (⇛-muli x y) = ⇛-muli (tri x) (tri y)
  tri (⇛-addt t u) = ⇛-addt (tri t) (tri u)
  tri (⇛-toi64 t) = ⇛-toi64 (tri t)
  tri (⇛-packi x y) = ⇛-packi (tri x) (tri y)

  triL : ∀ {σ m n} {ts us : List (Tm n)} → σ ⊢[ m ] ts ⇛L us → σ ⊢[ m ] us ⇛L devL σ m ts
  triL ⇛L-[] = ⇛L-[]
  triL (⇛L-∷ t ts) = ⇛L-∷ (tri t) (triL ts)

  -- mData: the development contracts the redex iff the scrutinee is a
  -- constructor application with a branch.
  tri-ιdata : ∀ {σ m n} {i j} {as as′ : List (Tm n)} {e : Tm n} {P : Tm (suc n)} {bs : List (Tm n)} {b b′}
    → Spine (ctor i j) as e → lookupList bs j ≡ ok b
    → σ ⊢[ m ] as′ ⇛L devL σ m as → σ ⊢[ m ] b′ ⇛ dev σ m b
    → σ ⊢[ m ] appsFrom b′ as′ ⇛ dev σ m (mData e P bs)
  tri-ιdata {σ} {m} {bs = bs} sp lk as* b*
    rewrite Spine→unspine head-ctor sp
          | Spine→unspine head-ctor (dev-Spine {σ} {m} dh-ctor sp)
          | lookupList-devL {σ} {m} bs _ lk = ⇛-appsFrom b* as*

  tri-mData-ctor : ∀ {σ m n} {i j} {as : List (Tm n)} {e e′ : Tm n} {P P′ : Tm (suc n)} {bs bs′ : List (Tm n)}
    → Spine (ctor i j) as e
    → σ ⊢[ m ] e ⇛ e′ → σ ⊢[ m ] e′ ⇛ dev σ m e → σ ⊢[ m ] P′ ⇛ dev σ m P
    → σ ⊢[ m ] bs′ ⇛L devL σ m bs
    → σ ⊢[ m ] mData e′ P′ bs′ ⇛
        devData′ (proj₂ (unspine (dev σ m e))) (lookupList (devL σ m bs) j)
          (dev σ m e) (dev σ m P) (devL σ m bs)
  tri-mData-ctor {σ} {m} {j = j} {bs = bs} sp e⇛ e* P* bs*
    rewrite Spine→unspine head-ctor (dev-Spine {σ} {m} dh-ctor sp)
    with lookupList bs j in lk
  ... | fail s rewrite lookupList-devL-fail {σ} {m} bs j lk = ⇛-mData e* P* bs*
  ... | ok b rewrite lookupList-devL {σ} {m} bs j lk
    with Spine-⇛ dh-ctor sp e⇛
  ...   | as′ , sp′ , _
    with Spine-⇛ dh-ctor sp′ e* | ⇛L-lookup⁻ bs* (lookupList-devL {σ} {m} bs j lk)
  ...     | as″ , sp″ , as′⇛ | b′ , lk′ , b′⇛
    with Spine-unique head-ctor head-ctor sp″ (dev-Spine {σ} {m} dh-ctor sp)
  ...       | refl , refl = ⇛-ιdata sp′ lk′ as′⇛ b′⇛

  tri-mData : ∀ {σ m n} {e e′ : Tm n} {P P′ : Tm (suc n)} {bs bs′ : List (Tm n)}
    → σ ⊢[ m ] e ⇛ e′ → σ ⊢[ m ] e′ ⇛ dev σ m e → σ ⊢[ m ] P′ ⇛ dev σ m P
    → σ ⊢[ m ] bs′ ⇛L devL σ m bs
    → σ ⊢[ m ] mData e′ P′ bs′ ⇛ dev σ m (mData e P bs)
  tri-mData {e = e} {P = P} e⇛ e* P* bs* with unspine e in eq
  ... | (ctor i j , as) = tri-mData-ctor {P = P} (unspine→Spine′ eq) e⇛ e* P* bs*
  ... | (var _ , _) = ⇛-mData e* P* bs*
  ... | (typ , _) = ⇛-mData e* P* bs*
  ... | (pi _ _ _ , _) = ⇛-mData e* P* bs*
  ... | (lam _ _ _ , _) = ⇛-mData e* P* bs*
  ... | (app _ _ , _) = ⇛-mData e* P* bs*
  ... | (nat , _) = ⇛-mData e* P* bs*
  ... | (ze , _) = ⇛-mData e* P* bs*
  ... | (su _ , _) = ⇛-mData e* P* bs*
  ... | (unit , _) = ⇛-mData e* P* bs*
  ... | (one , _) = ⇛-mData e* P* bs*
  ... | (empty , _) = ⇛-mData e* P* bs*
  ... | (dty _ , _) = ⇛-mData e* P* bs*
  ... | (mData _ _ _ , _) = ⇛-mData e* P* bs*
  ... | (mNat _ _ _ _ , _) = ⇛-mData e* P* bs*
  ... | (mEmp _ _ , _) = ⇛-mData e* P* bs*
  ... | (mUnit _ _ _ , _) = ⇛-mData e* P* bs*
  ... | (idt _ _ _ , _) = ⇛-mData e* P* bs*
  ... | (rfl , _) = ⇛-mData e* P* bs*
  ... | (rwt _ _ _ , _) = ⇛-mData e* P* bs*
  ... | (def _ , _) = ⇛-mData e* P* bs*
  ... | (ann _ _ , _) = ⇛-mData e* P* bs*
  ... | (prod _ _ , _) = ⇛-mData e* P* bs*
  ... | (pair _ _ , _) = ⇛-mData e* P* bs*
  ... | (letp _ _ , _) = ⇛-mData e* P* bs*
  ... | (nu _ , _) = ⇛-mData e* P* bs*
  ... | (unf _ _ , _) = ⇛-mData e* P* bs*
  ... | (ucons _ , _) = ⇛-mData e* P* bs*
  ... | (i64 , _) = ⇛-mData e* P* bs*
  ... | (f32ty , _) = ⇛-mData e* P* bs*
  ... | (tensor _ _ , _) = ⇛-mData e* P* bs*
  ... | (addi _ _ , _) = ⇛-mData e* P* bs*
  ... | (muli _ _ , _) = ⇛-mData e* P* bs*
  ... | (addt _ _ , _) = ⇛-mData e* P* bs*
  ... | (toi64 _ , _) = ⇛-mData e* P* bs*
  ... | (packi _ _ , _) = ⇛-mData e* P* bs*

  -- app: the development contracts the redex iff the function is a λ.
  tri-app : ∀ {σ m n} {f f′ a a′ : Tm n}
    → σ ⊢[ m ] f ⇛ f′ → σ ⊢[ m ] f′ ⇛ dev σ m f → σ ⊢[ m ] a′ ⇛ dev σ m a
    → σ ⊢[ m ] app f′ a′ ⇛ dev σ m (app f a)
  tri-app {f = lam q A t} (⇛-lam _ _) (⇛-lam _ t*) a* = ⇛-β t* a*
  tri-app {f = var x} _ f* a* = ⇛-app f* a*
  tri-app {f = typ} _ f* a* = ⇛-app f* a*
  tri-app {f = pi _ _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = app _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = nat} _ f* a* = ⇛-app f* a*
  tri-app {f = ze} _ f* a* = ⇛-app f* a*
  tri-app {f = su _} _ f* a* = ⇛-app f* a*
  tri-app {f = unit} _ f* a* = ⇛-app f* a*
  tri-app {f = one} _ f* a* = ⇛-app f* a*
  tri-app {f = empty} _ f* a* = ⇛-app f* a*
  tri-app {f = dty _} _ f* a* = ⇛-app f* a*
  tri-app {f = ctor _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = mData _ _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = mNat _ _ _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = mEmp _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = mUnit _ _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = idt _ _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = rfl} _ f* a* = ⇛-app f* a*
  tri-app {f = rwt _ _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = def _} _ f* a* = ⇛-app f* a*
  tri-app {f = ann _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = prod _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = pair _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = letp _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = nu _} _ f* a* = ⇛-app f* a*
  tri-app {f = unf _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = ucons _} _ f* a* = ⇛-app f* a*
  tri-app {f = i64} _ f* a* = ⇛-app f* a*
  tri-app {f = f32ty} _ f* a* = ⇛-app f* a*
  tri-app {f = tensor _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = addi _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = muli _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = addt _ _} _ f* a* = ⇛-app f* a*
  tri-app {f = toi64 _} _ f* a* = ⇛-app f* a*
  tri-app {f = packi _ _} _ f* a* = ⇛-app f* a*

  -- mNat: the development contracts the redex iff the scrutinee is ze or su.
  tri-mNat : ∀ {σ m n} {e e′ : Tm n} {P P′ : Tm (suc n)} {z z′ : Tm n} {s s′ : Tm (suc n)}
    → σ ⊢[ m ] e ⇛ e′ → σ ⊢[ m ] e′ ⇛ dev σ m e → σ ⊢[ m ] P′ ⇛ dev σ m P
    → σ ⊢[ m ] z′ ⇛ dev σ m z → σ ⊢[ m ] s′ ⇛ dev σ m s
    → σ ⊢[ m ] mNat e′ P′ z′ s′ ⇛ dev σ m (mNat e P z s)
  tri-mNat {e = ze} ⇛-ze _ _ z* _ = ⇛-ιz z*
  tri-mNat {e = su u} (⇛-su _) (⇛-su u*) _ _ s* = ⇛-ιs u* s*
  tri-mNat {e = var _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = typ} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = pi _ _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = lam _ _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = app _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = nat} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = unit} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = one} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = empty} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = dty _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = ctor _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = mData _ _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = mNat _ _ _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = mEmp _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = mUnit _ _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = idt _ _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = rfl} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = rwt _ _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = def _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = ann _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = prod _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = pair _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = letp _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = nu _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = unf _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = ucons _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = i64} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = f32ty} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = tensor _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = addi _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = muli _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = addt _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = toi64 _} _ e* P* z* s* = ⇛-mNat e* P* z* s*
  tri-mNat {e = packi _ _} _ e* P* z* s* = ⇛-mNat e* P* z* s*

  -- mUnit: the development contracts the redex iff the scrutinee is one.
  tri-mUnit : ∀ {σ m n} {e e′ : Tm n} {P P′ : Tm (suc n)} {u u′ : Tm n}
    → σ ⊢[ m ] e ⇛ e′ → σ ⊢[ m ] e′ ⇛ dev σ m e → σ ⊢[ m ] P′ ⇛ dev σ m P
    → σ ⊢[ m ] u′ ⇛ dev σ m u
    → σ ⊢[ m ] mUnit e′ P′ u′ ⇛ dev σ m (mUnit e P u)
  tri-mUnit {e = one} ⇛-one _ _ u* = ⇛-ιtt u*
  tri-mUnit {e = var _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = typ} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = pi _ _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = lam _ _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = app _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = nat} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = ze} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = su _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = unit} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = empty} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = dty _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = ctor _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = mData _ _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = mNat _ _ _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = mEmp _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = mUnit _ _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = idt _ _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = rfl} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = rwt _ _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = def _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = ann _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = prod _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = pair _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = letp _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = nu _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = unf _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = ucons _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = i64} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = f32ty} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = tensor _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = addi _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = muli _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = addt _ _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = toi64 _} _ e* P* u* = ⇛-mUnit e* P* u*
  tri-mUnit {e = packi _ _} _ e* P* u* = ⇛-mUnit e* P* u*

  -- letp: the development contracts the redex iff the scrutinee is a pair.
  tri-letp : ∀ {σ m n} {e e′ : Tm n} {t t′ : Tm (suc (suc n))}
    → σ ⊢[ m ] e ⇛ e′ → σ ⊢[ m ] e′ ⇛ dev σ m e → σ ⊢[ m ] t′ ⇛ dev σ m t
    → σ ⊢[ m ] letp e′ t′ ⇛ dev σ m (letp e t)
  tri-letp {e = pair a b} (⇛-pair _ _) (⇛-pair a* b*) t* = ⇛-ιletp a* b* t*
  tri-letp {e = one} _ e* t* = ⇛-letp e* t*
  tri-letp {e = var _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = typ} _ e* t* = ⇛-letp e* t*
  tri-letp {e = pi _ _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = lam _ _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = app _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = nat} _ e* t* = ⇛-letp e* t*
  tri-letp {e = ze} _ e* t* = ⇛-letp e* t*
  tri-letp {e = su _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = unit} _ e* t* = ⇛-letp e* t*
  tri-letp {e = empty} _ e* t* = ⇛-letp e* t*
  tri-letp {e = dty _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = ctor _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = mData _ _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = mNat _ _ _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = mEmp _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = mUnit _ _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = idt _ _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = rfl} _ e* t* = ⇛-letp e* t*
  tri-letp {e = rwt _ _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = def _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = ann _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = prod _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = letp _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = nu _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = unf _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = ucons _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = i64} _ e* t* = ⇛-letp e* t*
  tri-letp {e = f32ty} _ e* t* = ⇛-letp e* t*
  tri-letp {e = tensor _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = addi _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = muli _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = addt _ _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = toi64 _} _ e* t* = ⇛-letp e* t*
  tri-letp {e = packi _ _} _ e* t* = ⇛-letp e* t*

  -- rwt: the development contracts the redex iff the equation is rfl.
  tri-rwt : ∀ {σ m n} {e e′ : Tm n} {P P′ : Tm (suc n)} {t t′ : Tm n}
    → σ ⊢[ m ] e ⇛ e′ → σ ⊢[ m ] e′ ⇛ dev σ m e → σ ⊢[ m ] P′ ⇛ dev σ m P
    → σ ⊢[ m ] t′ ⇛ dev σ m t
    → σ ⊢[ m ] rwt e′ P′ t′ ⇛ dev σ m (rwt e P t)
  tri-rwt {e = rfl} ⇛-rfl _ _ t* = ⇛-ιrfl t*
  tri-rwt {e = var _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = typ} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = pi _ _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = lam _ _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = app _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = nat} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = ze} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = su _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = unit} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = one} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = empty} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = dty _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = ctor _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = mData _ _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = mNat _ _ _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = mEmp _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = mUnit _ _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = idt _ _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = rwt _ _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = def _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = ann _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = prod _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = pair _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = letp _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = nu _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = unf _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = ucons _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = i64} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = f32ty} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = tensor _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = addi _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = muli _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = addt _ _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = toi64 _} _ e* P* t* = ⇛-rwt e* P* t*
  tri-rwt {e = packi _ _} _ e* P* t* = ⇛-rwt e* P* t*

  -- uncons contracts exactly when the scrutinee is one of the two
  -- syntactic redexes. A congruence reduct of a redex is still a redex,
  -- so it takes the same step; anything else stays under uncons.
  tri-ucons : ∀ {σ m n} {e e′ : Tm n}
    → σ ⊢[ m ] e ⇛ e′ → σ ⊢[ m ] e′ ⇛ dev σ m e
    → σ ⊢[ m ] ucons e′ ⇛ dev σ m (ucons e)
  tri-ucons {e = unf _ (lam _ _ (pair _ _))}
            (⇛-unf _ (⇛-lam _ (⇛-pair _ _)))
            (⇛-unf s* (⇛-lam A* (⇛-pair h* t*))) =
    ⇛-ιβp h* t* s* A*
  tri-ucons {e = unf (pair _ _) (lam _ _ (var zero))}
            (⇛-unf (⇛-pair _ _) (⇛-lam _ ⇛-var))
            (⇛-unf (⇛-pair a* b*) (⇛-lam A* ⇛-var)) =
    ⇛-ιβ0 a* b* A*
  tri-ucons {e = var _} _ e* = ⇛-ucons e*
  tri-ucons {e = typ} _ e* = ⇛-ucons e*
  tri-ucons {e = pi _ _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = lam _ _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = app _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = nat} _ e* = ⇛-ucons e*
  tri-ucons {e = ze} _ e* = ⇛-ucons e*
  tri-ucons {e = su _} _ e* = ⇛-ucons e*
  tri-ucons {e = unit} _ e* = ⇛-ucons e*
  tri-ucons {e = one} _ e* = ⇛-ucons e*
  tri-ucons {e = empty} _ e* = ⇛-ucons e*
  tri-ucons {e = dty _} _ e* = ⇛-ucons e*
  tri-ucons {e = ctor _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = mData _ _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = mNat _ _ _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = mEmp _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = mUnit _ _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = idt _ _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = rfl} _ e* = ⇛-ucons e*
  tri-ucons {e = rwt _ _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = def _} _ e* = ⇛-ucons e*
  tri-ucons {e = ann _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = prod _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = pair _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = letp _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = nu _} _ e* = ⇛-ucons e*
  tri-ucons {e = ucons _} _ e* = ⇛-ucons e*
  tri-ucons {e = i64} _ e* = ⇛-ucons e*
  tri-ucons {e = f32ty} _ e* = ⇛-ucons e*
  tri-ucons {e = tensor _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = addi _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = muli _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = addt _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = toi64 _} _ e* = ⇛-ucons e*
  tri-ucons {e = packi _ _} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (var _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ typ} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (pi _ _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (app _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ nat} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ ze} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (su _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ unit} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ one} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ empty} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (dty _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (ctor _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (mData _ _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (mNat _ _ _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (mEmp _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (mUnit _ _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (idt _ _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ rfl} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (rwt _ _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (def _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (ann _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (prod _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (pair _ _)}
            (⇛-unf _ (⇛-pair _ _))
            (⇛-unf s* (⇛-pair h* t*)) =
    ⇛-ιβr h* t* s*
  tri-ucons {e = unf _ (letp _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (nu _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (unf _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (ucons _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ i64} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ f32ty} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (tensor _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (addi _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (muli _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (addt _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (toi64 _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (packi _ _)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (var (suc _)))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ typ)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (pi _ _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (lam _ _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (app _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ nat)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ ze)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (su _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ unit)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ one)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ empty)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (dty _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (ctor _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (mData _ _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (mNat _ _ _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (mEmp _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (mUnit _ _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (idt _ _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ rfl)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (rwt _ _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (def _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (ann _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (prod _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (letp _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (nu _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (unf _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (ucons _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ i64)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ f32ty)} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (tensor _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (addi _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (muli _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (addt _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (toi64 _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf _ (lam _ _ (packi _ _))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (var _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf typ (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (pi _ _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (lam _ _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (app _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf nat (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf ze (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (su _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf unit (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf one (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf empty (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (dty _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (ctor _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (mData _ _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (mNat _ _ _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (mEmp _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (mUnit _ _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (idt _ _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf rfl (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (rwt _ _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (def _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (ann _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (prod _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (letp _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (nu _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (unf _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (ucons _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf i64 (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf f32ty (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (tensor _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (addi _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (muli _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (addt _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (toi64 _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*
  tri-ucons {e = unf (packi _ _) (lam _ _ (var zero))} _ e* = ⇛-ucons e*

------------------------------------------------------------------------
-- Diamond, and confluence of the reflexive-transitive closure.
------------------------------------------------------------------------

diamond : ∀ {σ m n} {t u v : Tm n}
  → σ ⊢[ m ] t ⇛ u → σ ⊢[ m ] t ⇛ v
  → ∃ λ w → (σ ⊢[ m ] u ⇛ w) × (σ ⊢[ m ] v ⇛ w)
diamond {σ} {m} {t = t} d e = dev σ m t , tri d , tri e

data _⊢[_]_⇛*_ (σ : Sig) (m : Mode) {n} : Tm n → Tm n → Set where
  ⇛*-refl : ∀ {t} → σ ⊢[ m ] t ⇛* t
  ⇛*-step : ∀ {t u v} → σ ⊢[ m ] t ⇛ u → σ ⊢[ m ] u ⇛* v → σ ⊢[ m ] t ⇛* v

⇛*-one : ∀ {σ m n} {t u : Tm n} → σ ⊢[ m ] t ⇛ u → σ ⊢[ m ] t ⇛* u
⇛*-one d = ⇛*-step d ⇛*-refl

⇛*-trans : ∀ {σ m n} {t u v : Tm n}
  → σ ⊢[ m ] t ⇛* u → σ ⊢[ m ] u ⇛* v → σ ⊢[ m ] t ⇛* v
⇛*-trans ⇛*-refl r = r
⇛*-trans (⇛*-step d r) r′ = ⇛*-step d (⇛*-trans r r′)

strip : ∀ {σ m n} {t u v : Tm n}
  → σ ⊢[ m ] t ⇛ u → σ ⊢[ m ] t ⇛* v
  → ∃ λ w → (σ ⊢[ m ] u ⇛* w) × (σ ⊢[ m ] v ⇛ w)
strip d ⇛*-refl = _ , ⇛*-refl , d
strip d (⇛*-step e r) with diamond d e
... | w , uw , vw with strip vw r
...   | w′ , ww′ , vw′ = w′ , ⇛*-step uw ww′ , vw′

confluence : ∀ {σ m n} {t u v : Tm n}
  → σ ⊢[ m ] t ⇛* u → σ ⊢[ m ] t ⇛* v
  → ∃ λ w → (σ ⊢[ m ] u ⇛* w) × (σ ⊢[ m ] v ⇛* w)
confluence ⇛*-refl r = _ , r , ⇛*-refl
confluence (⇛*-step d r) r′ with strip d r′
... | w , uw , vw with confluence r uw
...   | w′ , uw′ , ww′ = w′ , uw′ , ⇛*-step vw ww′

⇛*-mode : ∀ {σ m m′ n} {t u : Tm n} → m ≤ᵐ m′ → σ ⊢[ m ] t ⇛* u → σ ⊢[ m′ ] t ⇛* u
⇛*-mode h ⇛*-refl = ⇛*-refl
⇛*-mode h (⇛*-step d r) = ⇛*-step (⇛-mode h d) (⇛*-mode h r)

⇛*-sub-r : ∀ {σ m n k} (τ : Fin n → Tm k) {t u : Tm n}
  → σ ⊢[ m ] t ⇛* u → σ ⊢[ m ] sub τ t ⇛* sub τ u
⇛*-sub-r τ ⇛*-refl = ⇛*-refl
⇛*-sub-r τ (⇛*-step d r) = ⇛*-step (⇛-sub-r τ d) (⇛*-sub-r τ r)

⇛*-ren : ∀ {σ m n k} (ρ : Fin n → Fin k) {t u : Tm n}
  → σ ⊢[ m ] t ⇛* u → σ ⊢[ m ] ren ρ t ⇛* ren ρ u
⇛*-ren ρ ⇛*-refl = ⇛*-refl
⇛*-ren ρ (⇛*-step d r) = ⇛*-step (⇛-ren ρ d) (⇛*-ren ρ r)

------------------------------------------------------------------------
-- Rigid heads are preserved: a type former or a constructor only
-- reduces to the same former with reduced arguments.
------------------------------------------------------------------------

pi-⇛* : ∀ {σ m n q} {A : Tm n} {B u}
  → σ ⊢[ m ] pi q A B ⇛* u
  → ∃ λ A′ → ∃ λ B′ → (u ≡ pi q A′ B′) × (σ ⊢[ m ] A ⇛* A′) × (σ ⊢[ m ] B ⇛* B′)
pi-⇛* ⇛*-refl = _ , _ , refl , ⇛*-refl , ⇛*-refl
pi-⇛* (⇛*-step (⇛-pi a b) r) with pi-⇛* r
... | A′ , B′ , refl , ra , rb = A′ , B′ , refl , ⇛*-step a ra , ⇛*-step b rb

idt-⇛* : ∀ {σ m n} {A a b : Tm n} {u}
  → σ ⊢[ m ] idt A a b ⇛* u
  → ∃ λ A′ → ∃ λ a′ → ∃ λ b′ → (u ≡ idt A′ a′ b′)
      × (σ ⊢[ m ] A ⇛* A′) × (σ ⊢[ m ] a ⇛* a′) × (σ ⊢[ m ] b ⇛* b′)
idt-⇛* ⇛*-refl = _ , _ , _ , refl , ⇛*-refl , ⇛*-refl , ⇛*-refl
idt-⇛* (⇛*-step (⇛-idt x y z) r) with idt-⇛* r
... | A′ , a′ , b′ , refl , rA , ra , rb =
  A′ , a′ , b′ , refl , ⇛*-step x rA , ⇛*-step y ra , ⇛*-step z rb

lam-⇛* : ∀ {σ m n q} {A : Tm n} {t u}
  → σ ⊢[ m ] lam q A t ⇛* u
  → ∃ λ A′ → ∃ λ t′ → (u ≡ lam q A′ t′) × (σ ⊢[ m ] A ⇛* A′) × (σ ⊢[ m ] t ⇛* t′)
lam-⇛* ⇛*-refl = _ , _ , refl , ⇛*-refl , ⇛*-refl
lam-⇛* (⇛*-step (⇛-lam a b) r) with lam-⇛* r
... | A′ , t′ , refl , ra , rb = A′ , t′ , refl , ⇛*-step a ra , ⇛*-step b rb

prod-⇛* : ∀ {σ m n} {A B : Tm n} {u}
  → σ ⊢[ m ] prod A B ⇛* u
  → ∃ λ A′ → ∃ λ B′ → (u ≡ prod A′ B′) × (σ ⊢[ m ] A ⇛* A′) × (σ ⊢[ m ] B ⇛* B′)
prod-⇛* ⇛*-refl = _ , _ , refl , ⇛*-refl , ⇛*-refl
prod-⇛* (⇛*-step (⇛-prod a b) r) with prod-⇛* r
... | A′ , B′ , refl , ra , rb = A′ , B′ , refl , ⇛*-step a ra , ⇛*-step b rb

pair-⇛* : ∀ {σ m n} {a b : Tm n} {u}
  → σ ⊢[ m ] pair a b ⇛* u
  → ∃ λ a′ → ∃ λ b′ → (u ≡ pair a′ b′) × (σ ⊢[ m ] a ⇛* a′) × (σ ⊢[ m ] b ⇛* b′)
pair-⇛* ⇛*-refl = _ , _ , refl , ⇛*-refl , ⇛*-refl
pair-⇛* (⇛*-step (⇛-pair a b) r) with pair-⇛* r
... | a′ , b′ , refl , ra , rb = a′ , b′ , refl , ⇛*-step a ra , ⇛*-step b rb

nu-⇛* : ∀ {σ m n} {F : Tm (suc n)} {u}
  → σ ⊢[ m ] nu F ⇛* u
  → ∃ λ F′ → (u ≡ nu F′) × (σ ⊢[ m ] F ⇛* F′)
nu-⇛* ⇛*-refl = _ , refl , ⇛*-refl
nu-⇛* (⇛*-step (⇛-nu a) r) with nu-⇛* r
... | F′ , refl , rF = F′ , refl , ⇛*-step a rF

unf-⇛* : ∀ {σ m n} {s f : Tm n} {u}
  → σ ⊢[ m ] unf s f ⇛* u
  → ∃ λ s′ → ∃ λ f′ → (u ≡ unf s′ f′) × (σ ⊢[ m ] s ⇛* s′) × (σ ⊢[ m ] f ⇛* f′)
unf-⇛* ⇛*-refl = _ , _ , refl , ⇛*-refl , ⇛*-refl
unf-⇛* (⇛*-step (⇛-unf a b) r) with unf-⇛* r
... | s′ , f′ , refl , rs , rf = s′ , f′ , refl , ⇛*-step a rs , ⇛*-step b rf

su-⇛* : ∀ {σ m n} {t : Tm n} {u}
  → σ ⊢[ m ] su t ⇛* u → ∃ λ t′ → (u ≡ su t′) × (σ ⊢[ m ] t ⇛* t′)
su-⇛* ⇛*-refl = _ , refl , ⇛*-refl
su-⇛* (⇛*-step (⇛-su a) r) with su-⇛* r
... | t′ , refl , ra = t′ , refl , ⇛*-step a ra

typ-⇛* : ∀ {σ m n} {u : Tm n} → σ ⊢[ m ] typ ⇛* u → u ≡ typ
typ-⇛* ⇛*-refl = refl
typ-⇛* (⇛*-step ⇛-typ r) = typ-⇛* r

nat-⇛* : ∀ {σ m n} {u : Tm n} → σ ⊢[ m ] nat ⇛* u → u ≡ nat
nat-⇛* ⇛*-refl = refl
nat-⇛* (⇛*-step ⇛-nat r) = nat-⇛* r

unit-⇛* : ∀ {σ m n} {u : Tm n} → σ ⊢[ m ] unit ⇛* u → u ≡ unit
unit-⇛* ⇛*-refl = refl
unit-⇛* (⇛*-step ⇛-unit r) = unit-⇛* r

empty-⇛* : ∀ {σ m n} {u : Tm n} → σ ⊢[ m ] empty ⇛* u → u ≡ empty
empty-⇛* ⇛*-refl = refl
empty-⇛* (⇛*-step ⇛-empty r) = empty-⇛* r

ze-⇛* : ∀ {σ m n} {u : Tm n} → σ ⊢[ m ] ze ⇛* u → u ≡ ze
ze-⇛* ⇛*-refl = refl
ze-⇛* (⇛*-step ⇛-ze r) = ze-⇛* r

one-⇛* : ∀ {σ m n} {u : Tm n} → σ ⊢[ m ] one ⇛* u → u ≡ one
one-⇛* ⇛*-refl = refl
one-⇛* (⇛*-step ⇛-one r) = one-⇛* r

rfl-⇛* : ∀ {σ m n} {u : Tm n} → σ ⊢[ m ] rfl ⇛* u → u ≡ rfl
rfl-⇛* ⇛*-refl = refl
rfl-⇛* (⇛*-step ⇛-rfl r) = rfl-⇛* r

------------------------------------------------------------------------
-- Spines with a data head along ⇛*: the head stays, the arguments
-- reduce pointwise.
------------------------------------------------------------------------

infix 3 _⊢[_]_⇛L*_

data _⊢[_]_⇛L*_ (σ : Sig) (m : Mode) {n} : List (Tm n) → List (Tm n) → Set where
  ⇛L*-[] : σ ⊢[ m ] [] ⇛L* []
  ⇛L*-∷  : ∀ {a a′ as as′} → σ ⊢[ m ] a ⇛* a′ → σ ⊢[ m ] as ⇛L* as′
    → σ ⊢[ m ] (a ∷ as) ⇛L* (a′ ∷ as′)

⇛L*-refl : ∀ {σ m n} (as : List (Tm n)) → σ ⊢[ m ] as ⇛L* as
⇛L*-refl [] = ⇛L*-[]
⇛L*-refl (a ∷ as) = ⇛L*-∷ ⇛*-refl (⇛L*-refl as)

⇛L-⇛L* : ∀ {σ m n} {as as₁ as′ : List (Tm n)}
  → σ ⊢[ m ] as ⇛L as₁ → σ ⊢[ m ] as₁ ⇛L* as′ → σ ⊢[ m ] as ⇛L* as′
⇛L-⇛L* ⇛L-[] ⇛L*-[] = ⇛L*-[]
⇛L-⇛L* (⇛L-∷ a as) (⇛L*-∷ a′ as′) = ⇛L*-∷ (⇛*-step a a′) (⇛L-⇛L* as as′)

Spine-⇛* : ∀ {σ m n} {h : Tm n} {as e e′} → DHead h → Spine h as e → σ ⊢[ m ] e ⇛* e′
  → ∃ λ as′ → Spine h as′ e′ × (σ ⊢[ m ] as ⇛L* as′)
Spine-⇛* hd sp ⇛*-refl = _ , sp , ⇛L*-refl _
Spine-⇛* hd sp (⇛*-step d r) with Spine-⇛ hd sp d
... | as₁ , sp₁ , as⇛ with Spine-⇛* hd sp₁ r
...   | as′ , sp′ , r′ = as′ , sp′ , ⇛L-⇛L* as⇛ r′

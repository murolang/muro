{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Soundness of the executable checker with respect to ⊢, on the ⊢
-- fragment (Muro.Frag): when Muro.Check says yes, ⊢ has a derivation.
--
-- Muro.Soundness.Conv   whnf-sound: when whnf k σ t returns ok u, t ⟶* u
--                       (spec) and u is in the fragment; synEq-sound;
--                       conv-sound: conv k σ u v ≡ ok tt → σ ⊢[ spec ] u ≈ v.
-- Muro.Soundness.Views  the views (viewPi, viewId, viewData), isData,
--                       and what the proof assumes of the signature
--                       (GoodSig), instParams and the index-clash test
--                       on a constructor telescope.
-- This module          infer-sound / check-sound / checkTy-sound, by
--                       structural recursion on the fragment witness,
--                       and checkDef-sound / checkSig-sound: every
--                       definition Check accepts is derivable in ⊢.
--
-- One direction only: nothing here says ⊢ derivations are found by
-- Check. Fuel is universally quantified: a run that stops for lack of
-- fuel proves nothing and claims nothing.
------------------------------------------------------------------------

module Muro.Soundness where

open import Data.Bool.Base using (Bool; true; false; _∧_; not; if_then_else_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length; take; drop)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_; _+_; _⊓_; _∸_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Unit.Base using (⊤; tt)
import Data.Vec.Base as Vec
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Env
open import Muro.Spine
open import Muro.Frag
open import Muro.SubstLemmas using (strengthen₂-sound; renList-id; strengthen-sound; inst-wk; renM-sound; Inv)
open import Muro.Reduction
open import Muro.Convert
open import Muro.Data hiding (subst₂)
open import Muro.Check
  using (whnf; conv; apps; viewPi; viewId; viewProd; viewData; isData; isCopy; notCopy; fieldUses; instParams; isRunType;
         infer; check; checkTy; checkAgainst; checkCtorApp; inferCtorSpine; inferConv;
         checkLam; checkBr; checkBrPi; checkBranches; checkMotive; firstMotLam; nparamsOf;
         clashes; RecSt; extRec; lamRec; scrutOk; checkRec; selfApplied;
         infer′; floatIdOk;
         isDType; checkDef; checkBody; checkBodyAt; retryBody; checkAt; argPositions; pickPos; checkDefs; checkDatas; checkSig; emptyRec; defRec; zeroPos;
         recMode; mutual?; component; sharedArgs;
         nuKind; nuKindAt; nuBodyProd; strictPos; unfStep; unfStepOf; lamForm; setGuard; checkUnfold; headTailU; skipAt;
         applyFam; unfFam; unfSpine)
open import Muro.Judgement
open import Muro.Wall using (spec-⇒-uses)
open import Muro.Typing using (typ-ext-suc; ≈-≡)
open import Muro.Soundness.Conv
open import Muro.Soundness.Views
open import Data.List.Properties using (take++drop≡id; length-take; length-drop)
open import Data.Nat.Properties using (m≤n⇒m⊓n≡m; m≤m+n; m+n∸m≡n; +-identityʳ; +-suc)

------------------------------------------------------------------------
-- Small helpers.
------------------------------------------------------------------------

var-run : ∀ {σ n} {Γ : Ctx n} {x q} → qtyOf Γ x ≡ q → (q ≡ erased → ⊥)
  → σ , Γ ⊢[ run ] var x ⇒ typOf Γ x ⊣ oneHot x (if eqQty q reuse then Uω else U1)
var-run refl ne = ⇒-var-run ne

var-evid : ∀ {σ n} {Γ : Ctx n} {x q} → qtyOf Γ x ≡ q → (q ≡ erased → ⊥)
  → σ , Γ ⊢[ evid ] var x ⇒ typOf Γ x ⊣ oneHot x (if eqQty q reuse then Uω else U1)
var-evid refl ne = ⇒-var-evid ne

eqMode-sound : ∀ m m′ → eqMode m m′ ≡ true → m ≡ m′
eqMode-sound run run _ = refl
eqMode-sound evid evid _ = refl
eqMode-sound spec spec _ = refl

-- the recursion state Check uses under a match binder (under a λ it is
-- Check.lamRec)
brRec : ∀ {n} → RecSt n → Bool → ℕ → Tm n → RecSt (suc n)
brRec rs sm di A = extRec rs (sm ∧ isDType di A) (sm ∧ isDType di A)

viewPi-≈ : ∀ k σ {n} {T : Tm n} {q A B} → FragSig σ → Frag T
  → viewPi k σ T ≡ ok (q , A , B) → σ ⊢[ spec ] T ≈ pi q A B
viewPi-≈ k σ fs FT eq = whnf-≈ k σ fs FT (viewPi-sound k σ eq)

viewPi-Frag : ∀ k σ {n} {T : Tm n} {q A B} → FragSig σ → Frag T
  → viewPi k σ T ≡ ok (q , A , B) → Frag A × Frag B
viewPi-Frag k σ fs FT eq with whnf-Frag k σ fs FT (viewPi-sound k σ eq)
... | f-pi FA FB = FA , FB

viewId-≈ : ∀ k σ {n} {T : Tm n} {A a b} → FragSig σ → Frag T
  → viewId k σ T ≡ ok (A , a , b) → σ ⊢[ spec ] T ≈ idt A a b
viewId-≈ k σ fs FT eq = whnf-≈ k σ fs FT (viewId-sound k σ eq)

viewId-Frag : ∀ k σ {n} {T : Tm n} {A a b} → FragSig σ → Frag T
  → viewId k σ T ≡ ok (A , a , b) → Frag A × Frag a × Frag b
viewId-Frag k σ fs FT eq with whnf-Frag k σ fs FT (viewId-sound k σ eq)
... | f-idt FA Fa Fb = FA , Fa , Fb

viewProd-≈ : ∀ k σ {n} {T : Tm n} {A B} → FragSig σ → Frag T
  → viewProd k σ T ≡ ok (A , B) → σ ⊢[ spec ] T ≈ prod A B
viewProd-≈ k σ fs FT eq = whnf-≈ k σ fs FT (viewProd-sound k σ eq)

viewProd-Frag : ∀ k σ {n} {T : Tm n} {A B} → FragSig σ → Frag T
  → viewProd k σ T ≡ ok (A , B) → Frag A × Frag B
viewProd-Frag k σ fs FT eq with whnf-Frag k σ fs FT (viewProd-sound k σ eq)
... | f-prod FA FB = FA , FB

------------------------------------------------------------------------
-- The checker is sound for ⊢. If infer / check / checkTy say yes on
-- fragment input over a covered signature, ⊢ has a derivation with the
-- same uses; the inferred type agrees up to ≈ (Check returns the motive
-- of a match as a β-redex). The recursion is structural on the fragment
-- witness of the term: a constructor spine is walked from its head
-- (inferCtorSpine-sound on Frag (app f a) recurses on f), a branch is
-- entered one λ at a time (checkBrPi-sound on Frag (lam q A t) recurses
-- on t); the calls that pass the witness on unchanged (check → against
-- → inferConv → infer) reach a subterm before they return.
--
-- ν is in the fragment. A stream unfold is the λ (⇐-unf). A declared
-- family is the instantiated pair (⇐-unfR): that is the term uncons
-- reads, and the wrap of the source λ is not a typed step at the family
-- goal. Where a binder's type uses that value, the derivation is at the
-- type of the pair (inf′ / chk′); it is not claimed convertible to the
-- type the checker computed from the λ.
------------------------------------------------------------------------

-- A derivation at the checker's type A, or at the type of a family
-- unfold read as a pair.
data Chk {σ n} (Γ : Ctx n) (m : Mode) (e A : Tm n) (u : UseVec n) : Set where
  chk  : σ , Γ ⊢[ m ] e ⇐ A ⊣ u → Chk Γ m e A u
  -- A derivation of a different term. A declared-family unfold is the
  -- instantiated pair, which is not the source λ.
  chk′ : ∀ {e′ A′} → σ , Γ ⊢[ m ] e′ ⇐ A′ ⊣ u → Chk Γ m e A u
  -- A premise was not at the type its rule requires.
  miss : Chk Γ m e A u

data Inf {σ n} (Γ : Ctx n) (m : Mode) (e A : Tm n) (u : UseVec n) : Set where
  inf  : ∀ {A′} → Frag A → σ , Γ ⊢[ m ] e ⇒ A′ ⊣ u → σ ⊢[ spec ] A′ ≈ A → Inf {σ} Γ m e A u
  inf′ : ∀ {e′ A′} → σ , Γ ⊢[ m ] e′ ⇒ A′ ⊣ u → Inf {σ} Γ m e A u
  miss : Inf {σ} Γ m e A u

-- inst B a′ and inst B a agree when B does not mention the last binder.
data Cod {σ : Sig} {n} : Tm n → Tm n → Set where
  cod-≈ : ∀ {A′ A} → σ ⊢[ spec ] A′ ≈ A → Cod {σ} A′ A
  cod-dep : ∀ {A′ A} → Cod {σ} A′ A

codAt : ∀ {σ n} (B : Tm (suc n)) (a a′ : Tm n) → Cod {σ} (inst B a′) (inst B a)
codAt B a a′ with strengthen B in se
... | ok C rewrite strengthen-sound B se | inst-wk C a′ | inst-wk C a = cod-≈ ≈-refl
... | fail _ = cod-dep

-- A stream codomain does not use its binder, so the instantiated product
-- is the weakening of that product.
streamBody : ∀ {σ n} {Body : Tm (suc n)} {C seed Ah S2 S}
  → strengthen Body ≡ ok C
  → σ ⊢[ spec ] inst Body seed ≈ prod Ah S2
  → σ ⊢[ spec ] S2 ≈ S
  → σ ⊢[ spec ] Body ≈ prod (wk Ah) (wk S)
streamBody {Body = Body} {C} {seed} eq cV cS rewrite strengthen-sound Body eq | inst-wk C seed =
  ≈-trans (≈-ren suc cV) (≈-prod ≈-refl (≈-ren suc cS))

-- skipAt drops the ν binder. insert puts it back, and is a left inverse
-- wherever skipAt succeeds, so a renamed kind is still in the fragment.
insert : ∀ {n} → ℕ → Fin n → Fin (suc n)
insert zero j = suc j
insert {suc _} (suc _) zero = zero
insert {suc n} (suc k) (suc j) = suc (insert {n} k j)
insert {zero} (suc _) ()

skipInv : ∀ {n} (y : ℕ) → Inv (skipAt {n} y) (insert {n} y)
skipInv zero zero _ eq = ⊥-elim (fail≢ok eq)
skipInv zero (suc i) .i refl = refl
skipInv {zero} (suc _) _ _ eq = ⊥-elim (fail≢ok eq)
skipInv {suc _} (suc _) zero .zero refl = refl
skipInv {suc n} (suc y) (suc i) j eq with skipAt {n} y i in e
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok j′ with eq
... | refl = cong suc (skipInv {n} y i j′ e)

fragSkip : ∀ {n} (y : ℕ) {A : Tm (suc n)} {A′ : Tm n} → Frag A
  → renM (skipAt y) A ≡ ok A′ → Frag A′
fragSkip y {A} {A′} FA eq =
  Frag-unren (insert y) A′
    (subst Frag (sym (renM-sound (skipAt y) (insert y) (skipInv y) A eq)) FA)

nuKindAt-Frag : ∀ {n} (y : ℕ) (F : Tm (suc n)) → Frag F → ∀ {K} → nuKindAt y F ≡ ok K → Frag K
nuKindAt-Frag y (lam q A t) (f-lam FA Ft) eq with renM (skipAt y) A in aeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok A′ with nuKindAt (suc y) t in beq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok B rewrite sym (ok-inj eq) =
  f-pi (fragSkip y FA aeq) (nuKindAt-Frag (suc y) t Ft beq)
nuKindAt-Frag _ (var _) f-var refl = f-typ
nuKindAt-Frag _ typ f-typ refl = f-typ
nuKindAt-Frag _ (pi _ _ _) (f-pi _ _) refl = f-typ
nuKindAt-Frag _ (app _ _) (f-app _ _) refl = f-typ
nuKindAt-Frag _ nat f-nat refl = f-typ
nuKindAt-Frag _ ze f-ze refl = f-typ
nuKindAt-Frag _ (su _) (f-su _) refl = f-typ
nuKindAt-Frag _ unit f-unit refl = f-typ
nuKindAt-Frag _ one f-one refl = f-typ
nuKindAt-Frag _ empty f-empty refl = f-typ
nuKindAt-Frag _ (dty _) f-dty refl = f-typ
nuKindAt-Frag _ (ctor _ _) f-ctor refl = f-typ
nuKindAt-Frag _ (mData _ _ _) (f-mData _ _ _) refl = f-typ
nuKindAt-Frag _ (mNat _ _ _ _) (f-mNat _ _ _ _) refl = f-typ
nuKindAt-Frag _ (mEmp _ _) (f-mEmp _ _) refl = f-typ
nuKindAt-Frag _ (mUnit _ _ _) (f-mUnit _ _ _) refl = f-typ
nuKindAt-Frag _ (idt _ _ _) (f-idt _ _ _) refl = f-typ
nuKindAt-Frag _ rfl f-rfl refl = f-typ
nuKindAt-Frag _ (rwt _ _ _) (f-rwt _ _ _) refl = f-typ
nuKindAt-Frag _ (def _) f-def refl = f-typ
nuKindAt-Frag _ (ann _ _) (f-ann _ _) refl = f-typ
nuKindAt-Frag _ (prod _ _) (f-prod _ _) refl = f-typ
nuKindAt-Frag _ (pair _ _) (f-pair _ _) refl = f-typ
nuKindAt-Frag _ (letp _ _) (f-letp _ _) refl = f-typ
nuKindAt-Frag _ (nu _) (f-nu _) refl = f-typ
nuKindAt-Frag _ (unf _ _) (f-unf _ _ _) refl = f-typ
nuKindAt-Frag _ (ucons _) (f-ucons _) refl = f-typ

-- lamForm is true only for ν X. Eh × X with Eh free of X.
false≢true : false ≡ true → ⊥
false≢true ()

lamForm-inv : ∀ {n} {T : Tm n} → Frag T → lamForm T ≡ true
  → ∃ λ Eh → T ≡ nu (prod (wk Eh) (var Fin.zero))
lamForm-inv (f-nu (f-prod {A = B} _ (f-var {x = zero}))) eq with strengthen B in se
... | ok Eh rewrite strengthen-sound B se = Eh , refl
... | fail _ = ⊥-elim (false≢true eq)
lamForm-inv (f-nu (f-prod _ (f-var {x = suc _}))) ()
lamForm-inv (f-var) ()
lamForm-inv f-typ ()
lamForm-inv (f-pi _ _) ()
lamForm-inv (f-lam _ _) ()
lamForm-inv (f-app _ _) ()
lamForm-inv f-nat ()
lamForm-inv f-ze ()
lamForm-inv (f-su _) ()
lamForm-inv f-unit ()
lamForm-inv f-one ()
lamForm-inv f-empty ()
lamForm-inv f-dty ()
lamForm-inv f-ctor ()
lamForm-inv (f-mData _ _ _) ()
lamForm-inv (f-mNat _ _ _ _) ()
lamForm-inv (f-mEmp _ _) ()
lamForm-inv (f-mUnit _ _ _) ()
lamForm-inv (f-idt _ _ _) ()
lamForm-inv f-rfl ()
lamForm-inv (f-rwt _ _ _) ()
lamForm-inv f-def ()
lamForm-inv (f-ann _ _) ()
lamForm-inv (f-prod _ _) ()
lamForm-inv (f-pair _ _) ()
lamForm-inv (f-letp _ _) ()
lamForm-inv (f-nu f-var) ()
lamForm-inv (f-nu f-typ) ()
lamForm-inv (f-nu (f-pi _ _)) ()
lamForm-inv (f-nu (f-lam _ _)) ()
lamForm-inv (f-nu (f-app _ _)) ()
lamForm-inv (f-nu f-nat) ()
lamForm-inv (f-nu f-ze) ()
lamForm-inv (f-nu (f-su _)) ()
lamForm-inv (f-nu f-unit) ()
lamForm-inv (f-nu f-one) ()
lamForm-inv (f-nu f-empty) ()
lamForm-inv (f-nu f-dty) ()
lamForm-inv (f-nu f-ctor) ()
lamForm-inv (f-nu (f-mData _ _ _)) ()
lamForm-inv (f-nu (f-mNat _ _ _ _)) ()
lamForm-inv (f-nu (f-mEmp _ _)) ()
lamForm-inv (f-nu (f-mUnit _ _ _)) ()
lamForm-inv (f-nu (f-idt _ _ _)) ()
lamForm-inv (f-nu f-rfl) ()
lamForm-inv (f-nu (f-rwt _ _ _)) ()
lamForm-inv (f-nu f-def) ()
lamForm-inv (f-nu (f-ann _ _)) ()
lamForm-inv (f-nu (f-pair _ _)) ()
lamForm-inv (f-nu (f-letp _ _)) ()
lamForm-inv (f-nu (f-nu _)) ()
lamForm-inv (f-nu (f-unf _ _ _)) ()
lamForm-inv (f-nu (f-ucons _)) ()
lamForm-inv (f-nu (f-prod _ f-typ)) ()
lamForm-inv (f-nu (f-prod _ (f-pi _ _))) ()
lamForm-inv (f-nu (f-prod _ (f-lam _ _))) ()
lamForm-inv (f-nu (f-prod _ (f-app _ _))) ()
lamForm-inv (f-nu (f-prod _ f-nat)) ()
lamForm-inv (f-nu (f-prod _ f-ze)) ()
lamForm-inv (f-nu (f-prod _ (f-su _))) ()
lamForm-inv (f-nu (f-prod _ f-unit)) ()
lamForm-inv (f-nu (f-prod _ f-one)) ()
lamForm-inv (f-nu (f-prod _ f-empty)) ()
lamForm-inv (f-nu (f-prod _ f-dty)) ()
lamForm-inv (f-nu (f-prod _ f-ctor)) ()
lamForm-inv (f-nu (f-prod _ (f-mData _ _ _))) ()
lamForm-inv (f-nu (f-prod _ (f-mNat _ _ _ _))) ()
lamForm-inv (f-nu (f-prod _ (f-mEmp _ _))) ()
lamForm-inv (f-nu (f-prod _ (f-mUnit _ _ _))) ()
lamForm-inv (f-nu (f-prod _ (f-idt _ _ _))) ()
lamForm-inv (f-nu (f-prod _ f-rfl)) ()
lamForm-inv (f-nu (f-prod _ (f-rwt _ _ _))) ()
lamForm-inv (f-nu (f-prod _ f-def)) ()
lamForm-inv (f-nu (f-prod _ (f-ann _ _))) ()
lamForm-inv (f-nu (f-prod _ (f-prod _ _))) ()
lamForm-inv (f-nu (f-prod _ (f-pair _ _))) ()
lamForm-inv (f-nu (f-prod _ (f-letp _ _))) ()
lamForm-inv (f-nu (f-prod _ (f-nu _))) ()
lamForm-inv (f-nu (f-prod _ (f-unf _ _ _))) ()
lamForm-inv (f-nu (f-prod _ (f-ucons _))) ()
lamForm-inv (f-unf _ _ _) ()
lamForm-inv (f-ucons _) ()

applyFam-Frag : ∀ {n} (t : Tm n) (is : List (Tm n)) → Frag t → FragL is → Frag (applyFam t is)
applyFam-Frag t [] Ft fl-[] = Ft
applyFam-Frag (lam q A b) (i ∷ is) (f-lam FA Fb) (fl-∷ Fi Fis) =
  applyFam-Frag (inst b i) is (Frag-inst Fb Fi) Fis
applyFam-Frag (var x) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (var x) i) is (f-app Ft Fi) Fis
applyFam-Frag typ (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app typ i) is (f-app Ft Fi) Fis
applyFam-Frag (pi q A B) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (pi q A B) i) is (f-app Ft Fi) Fis
applyFam-Frag (app f a) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (app f a) i) is (f-app Ft Fi) Fis
applyFam-Frag nat (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app nat i) is (f-app Ft Fi) Fis
applyFam-Frag ze (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app ze i) is (f-app Ft Fi) Fis
applyFam-Frag (su t) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (su t) i) is (f-app Ft Fi) Fis
applyFam-Frag unit (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app unit i) is (f-app Ft Fi) Fis
applyFam-Frag one (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app one i) is (f-app Ft Fi) Fis
applyFam-Frag empty (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app empty i) is (f-app Ft Fi) Fis
applyFam-Frag (dty d) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (dty d) i) is (f-app Ft Fi) Fis
applyFam-Frag (ctor d c) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (ctor d c) i) is (f-app Ft Fi) Fis
applyFam-Frag (mData e P bs) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (mData e P bs) i) is (f-app Ft Fi) Fis
applyFam-Frag (mNat e P z s) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (mNat e P z s) i) is (f-app Ft Fi) Fis
applyFam-Frag (mEmp e P) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (mEmp e P) i) is (f-app Ft Fi) Fis
applyFam-Frag (mUnit e P u) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (mUnit e P u) i) is (f-app Ft Fi) Fis
applyFam-Frag (idt A a b) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (idt A a b) i) is (f-app Ft Fi) Fis
applyFam-Frag rfl (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app rfl i) is (f-app Ft Fi) Fis
applyFam-Frag (rwt e P t) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (rwt e P t) i) is (f-app Ft Fi) Fis
applyFam-Frag (def d) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (def d) i) is (f-app Ft Fi) Fis
applyFam-Frag (ann e A) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (ann e A) i) is (f-app Ft Fi) Fis
applyFam-Frag (prod A B) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (prod A B) i) is (f-app Ft Fi) Fis
applyFam-Frag (pair a b) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (pair a b) i) is (f-app Ft Fi) Fis
applyFam-Frag (letp e t) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (letp e t) i) is (f-app Ft Fi) Fis
applyFam-Frag (nu F) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (nu F) i) is (f-app Ft Fi) Fis
applyFam-Frag (unf s f) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (unf s f) i) is (f-app Ft Fi) Fis
applyFam-Frag (ucons s) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (ucons s) i) is (f-app Ft Fi) Fis
applyFam-Frag i64 (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app i64 i) is (f-app Ft Fi) Fis
applyFam-Frag f32ty (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app f32ty i) is (f-app Ft Fi) Fis
applyFam-Frag (tensor d s) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (tensor d s) i) is (f-app Ft Fi) Fis
applyFam-Frag (addi x y) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (addi x y) i) is (f-app Ft Fi) Fis
applyFam-Frag (muli x y) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (muli x y) i) is (f-app Ft Fi) Fis
applyFam-Frag (addt x y) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (addt x y) i) is (f-app Ft Fi) Fis
applyFam-Frag (toi64 t) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (toi64 t) i) is (f-app Ft Fi) Fis
applyFam-Frag (packi x y) (i ∷ is) Ft (fl-∷ Fi Fis) = applyFam-Frag (app (packi x y) i) is (f-app Ft Fi) Fis

unfFam-Frag : ∀ {n} {S : Tm n} {F : Tm (suc n)} {as G fam} → Frag S → Frag F → FragL as
  → unfFam S F as ≡ ok (G , fam) → Frag G
unfFam-Frag FS FF fl-[] refl = Frag-inst FF FS
unfFam-Frag FS (f-lam {q = q} {A = A} {t = b} FA Fb) (fl-∷ Fi Fis) refl =
  applyFam-Frag (inst (lam q A b) (nu (lam q A b))) _
    (Frag-inst (f-lam FA Fb) (f-nu (f-lam FA Fb))) (fl-∷ Fi Fis)
unfFam-Frag _ f-var (fl-∷ _ _) ()
unfFam-Frag _ f-typ (fl-∷ _ _) ()
unfFam-Frag _ (f-pi _ _) (fl-∷ _ _) ()
unfFam-Frag _ (f-app _ _) (fl-∷ _ _) ()
unfFam-Frag _ f-nat (fl-∷ _ _) ()
unfFam-Frag _ f-ze (fl-∷ _ _) ()
unfFam-Frag _ (f-su _) (fl-∷ _ _) ()
unfFam-Frag _ f-unit (fl-∷ _ _) ()
unfFam-Frag _ f-one (fl-∷ _ _) ()
unfFam-Frag _ f-empty (fl-∷ _ _) ()
unfFam-Frag _ f-dty (fl-∷ _ _) ()
unfFam-Frag _ f-ctor (fl-∷ _ _) ()
unfFam-Frag _ (f-mData _ _ _) (fl-∷ _ _) ()
unfFam-Frag _ (f-mNat _ _ _ _) (fl-∷ _ _) ()
unfFam-Frag _ (f-mEmp _ _) (fl-∷ _ _) ()
unfFam-Frag _ (f-mUnit _ _ _) (fl-∷ _ _) ()
unfFam-Frag _ (f-idt _ _ _) (fl-∷ _ _) ()
unfFam-Frag _ f-rfl (fl-∷ _ _) ()
unfFam-Frag _ (f-rwt _ _ _) (fl-∷ _ _) ()
unfFam-Frag _ f-def (fl-∷ _ _) ()
unfFam-Frag _ (f-ann _ _) (fl-∷ _ _) ()
unfFam-Frag _ (f-prod _ _) (fl-∷ _ _) ()
unfFam-Frag _ (f-pair _ _) (fl-∷ _ _) ()
unfFam-Frag _ (f-letp _ _) (fl-∷ _ _) ()
unfFam-Frag _ (f-nu _) (fl-∷ _ _) ()
unfFam-Frag _ (f-unf _ _ _) (fl-∷ _ _) ()
unfFam-Frag _ (f-ucons _) (fl-∷ _ _) ()

unspine-go-Frag : ∀ {n} (t : Tm n) (acc : List (Tm n)) → Frag t → FragL acc
  → ∃ λ h → ∃ λ as → unspine-go t acc ≡ (h , as) × Frag h × FragL as
unspine-go-Frag (app f a) acc (f-app Ff Fa) Facc with unspine-go-Frag f (a ∷ acc) Ff (fl-∷ Fa Facc)
... | h , as , eq , Fh , Fas = h , as , eq , Fh , Fas
unspine-go-Frag (var x) acc Ft Facc = var x , acc , refl , Ft , Facc
unspine-go-Frag typ acc Ft Facc = typ , acc , refl , Ft , Facc
unspine-go-Frag (pi q A B) acc Ft Facc = pi q A B , acc , refl , Ft , Facc
unspine-go-Frag (lam q A t) acc Ft Facc = lam q A t , acc , refl , Ft , Facc
unspine-go-Frag nat acc Ft Facc = nat , acc , refl , Ft , Facc
unspine-go-Frag ze acc Ft Facc = ze , acc , refl , Ft , Facc
unspine-go-Frag (su t) acc Ft Facc = su t , acc , refl , Ft , Facc
unspine-go-Frag unit acc Ft Facc = unit , acc , refl , Ft , Facc
unspine-go-Frag one acc Ft Facc = one , acc , refl , Ft , Facc
unspine-go-Frag empty acc Ft Facc = empty , acc , refl , Ft , Facc
unspine-go-Frag (dty d) acc Ft Facc = dty d , acc , refl , Ft , Facc
unspine-go-Frag (ctor d c) acc Ft Facc = ctor d c , acc , refl , Ft , Facc
unspine-go-Frag (mData e P bs) acc Ft Facc = mData e P bs , acc , refl , Ft , Facc
unspine-go-Frag (mNat e P z s) acc Ft Facc = mNat e P z s , acc , refl , Ft , Facc
unspine-go-Frag (mEmp e P) acc Ft Facc = mEmp e P , acc , refl , Ft , Facc
unspine-go-Frag (mUnit e P u) acc Ft Facc = mUnit e P u , acc , refl , Ft , Facc
unspine-go-Frag (idt A a b) acc Ft Facc = idt A a b , acc , refl , Ft , Facc
unspine-go-Frag rfl acc Ft Facc = rfl , acc , refl , Ft , Facc
unspine-go-Frag (rwt e P t) acc Ft Facc = rwt e P t , acc , refl , Ft , Facc
unspine-go-Frag (def d) acc Ft Facc = def d , acc , refl , Ft , Facc
unspine-go-Frag (ann e A) acc Ft Facc = ann e A , acc , refl , Ft , Facc
unspine-go-Frag (prod A B) acc Ft Facc = prod A B , acc , refl , Ft , Facc
unspine-go-Frag (pair a b) acc Ft Facc = pair a b , acc , refl , Ft , Facc
unspine-go-Frag (letp e t) acc Ft Facc = letp e t , acc , refl , Ft , Facc
unspine-go-Frag (nu F) acc Ft Facc = nu F , acc , refl , Ft , Facc
unspine-go-Frag (unf s f) acc Ft Facc = unf s f , acc , refl , Ft , Facc
unspine-go-Frag (ucons s) acc Ft Facc = ucons s , acc , refl , Ft , Facc
unspine-go-Frag i64 acc Ft Facc = i64 , acc , refl , Ft , Facc
unspine-go-Frag f32ty acc Ft Facc = f32ty , acc , refl , Ft , Facc
unspine-go-Frag (tensor d s) acc Ft Facc = tensor d s , acc , refl , Ft , Facc
unspine-go-Frag (addi x y) acc Ft Facc = addi x y , acc , refl , Ft , Facc
unspine-go-Frag (muli x y) acc Ft Facc = muli x y , acc , refl , Ft , Facc
unspine-go-Frag (addt x y) acc Ft Facc = addt x y , acc , refl , Ft , Facc
unspine-go-Frag (toi64 t) acc Ft Facc = toi64 t , acc , refl , Ft , Facc
unspine-go-Frag (packi x y) acc Ft Facc = packi x y , acc , refl , Ft , Facc

unspine-Frag : ∀ {n} (t : Tm n) → Frag t
  → ∃ λ h → ∃ λ as → unspine t ≡ (h , as) × Frag h × FragL as
unspine-Frag t Ft with unspine-go-Frag t [] Ft fl-[]
... | h , as , eq , Fh , Fas = h , as , eq , Fh , Fas

unfSpine-Frag : ∀ {n} {S h : Tm n} {as G fam} → Frag S → Frag h → FragL as
  → unfSpine S (h , as) ≡ ok (G , fam) → Frag G
unfSpine-Frag FS (f-nu FF) Fas eq = unfFam-Frag FS FF Fas eq
unfSpine-Frag _ f-var _ ()
unfSpine-Frag _ f-typ _ ()
unfSpine-Frag _ (f-pi _ _) _ ()
unfSpine-Frag _ (f-lam _ _) _ ()
unfSpine-Frag _ (f-app _ _) _ ()
unfSpine-Frag _ f-nat _ ()
unfSpine-Frag _ f-ze _ ()
unfSpine-Frag _ (f-su _) _ ()
unfSpine-Frag _ f-unit _ ()
unfSpine-Frag _ f-one _ ()
unfSpine-Frag _ f-empty _ ()
unfSpine-Frag _ f-dty _ ()
unfSpine-Frag _ f-ctor _ ()
unfSpine-Frag _ (f-mData _ _ _) _ ()
unfSpine-Frag _ (f-mNat _ _ _ _) _ ()
unfSpine-Frag _ (f-mEmp _ _) _ ()
unfSpine-Frag _ (f-mUnit _ _ _) _ ()
unfSpine-Frag _ (f-idt _ _ _) _ ()
unfSpine-Frag _ f-rfl _ ()
unfSpine-Frag _ (f-rwt _ _ _) _ ()
unfSpine-Frag _ f-def _ ()
unfSpine-Frag _ (f-ann _ _) _ ()
unfSpine-Frag _ (f-prod _ _) _ ()
unfSpine-Frag _ (f-pair _ _) _ ()
unfSpine-Frag _ (f-letp _ _) _ ()
unfSpine-Frag _ (f-unf _ _ _) _ ()
unfSpine-Frag _ (f-ucons _) _ ()

unfStepOf-Frag : ∀ {n} (S T : Tm n) {G fam} → Frag S → Frag T
  → unfStepOf S T ≡ ok (G , fam) → Frag G
unfStepOf-Frag S (nu F) FS (f-nu FF) refl = Frag-inst FF FS
unfStepOf-Frag S (var x) FS Ft eq with unspine-Frag (var x) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S typ FS Ft eq with unspine-Frag typ Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (pi q A B) FS Ft eq with unspine-Frag (pi q A B) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (lam q A t) FS Ft eq with unspine-Frag (lam q A t) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (app f a) FS Ft eq with unspine-Frag (app f a) Ft
... | h , as , eq′ , Fh , Fas rewrite eq′ = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S nat FS Ft eq with unspine-Frag nat Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S ze FS Ft eq with unspine-Frag ze Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (su t) FS Ft eq with unspine-Frag (su t) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S unit FS Ft eq with unspine-Frag unit Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S one FS Ft eq with unspine-Frag one Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S empty FS Ft eq with unspine-Frag empty Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (dty d) FS Ft eq with unspine-Frag (dty d) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (ctor d c) FS Ft eq with unspine-Frag (ctor d c) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (mData e P bs) FS Ft eq with unspine-Frag (mData e P bs) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (mNat e P z s) FS Ft eq with unspine-Frag (mNat e P z s) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (mEmp e P) FS Ft eq with unspine-Frag (mEmp e P) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (mUnit e P u) FS Ft eq with unspine-Frag (mUnit e P u) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (idt A a b) FS Ft eq with unspine-Frag (idt A a b) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S rfl FS Ft eq with unspine-Frag rfl Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (rwt e P t) FS Ft eq with unspine-Frag (rwt e P t) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (def d) FS Ft eq with unspine-Frag (def d) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (ann e A) FS Ft eq with unspine-Frag (ann e A) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (prod A B) FS Ft eq with unspine-Frag (prod A B) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (pair a b) FS Ft eq with unspine-Frag (pair a b) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (letp e t) FS Ft eq with unspine-Frag (letp e t) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (unf s f) FS Ft eq with unspine-Frag (unf s f) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (ucons s) FS Ft eq with unspine-Frag (ucons s) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S i64 FS Ft eq with unspine-Frag i64 Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S f32ty FS Ft eq with unspine-Frag f32ty Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (tensor d s) FS Ft eq with unspine-Frag (tensor d s) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (addi x y) FS Ft eq with unspine-Frag (addi x y) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (muli x y) FS Ft eq with unspine-Frag (muli x y) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (addt x y) FS Ft eq with unspine-Frag (addt x y) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (toi64 t) FS Ft eq with unspine-Frag (toi64 t) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq
unfStepOf-Frag S (packi x y) FS Ft eq with unspine-Frag (packi x y) Ft
... | h , as , refl , Fh , Fas = unfSpine-Frag FS Fh Fas eq

-- hd: the term is inferred as the head of an application spine (Check
-- then skips the descent tests, which have no bearing on ⊢); infer is
-- infer′ … false.
-- The uses of a constructor argument (Check.fieldUses): a + field that
-- is Data is args-snoc, a copyable one is args-snoc-copy.
fieldUses-sound : ∀ k σ {n} {Γ : Ctx n} {m q A B a as T R au fu uses} → FragSig σ → Frag A
  → σ , Γ ⊢[ m ] T ▹ as ⇝ R ⊣ fu
  → σ ⊢[ spec ] R ≈ pi q A B
  → σ , Γ ⊢[ fieldMode q m ] a ⇐ A ⊣ au
  → fieldUses k σ q m A au fu ≡ ok uses
  → σ , Γ ⊢[ m ] T ▹ (as ++ (a ∷ [])) ⇝ inst B a ⊣ uses
fieldUses-sound k σ {q = affine} fs FA Ar c Da eq = args-snoc Ar c tt Da eq
fieldUses-sound k σ {q = erased} fs FA Ar c Da eq = args-snoc Ar c tt Da eq
fieldUses-sound k σ {q = reuse} {A = A} fs FA Ar c Da eq with isData k σ A in deq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok true = args-snoc Ar c (isData-sound k σ fs FA deq) Da eq
... | ok false with isCopy k σ A in ceq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok false = ⊥-elim (fail≢ok eq)
...   | ok true = args-snoc-copy Ar c (isCopy-sound k σ fs FA ceq) Da eq

infer-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m hd {e A u} → GoodSig σ → FragCtx Γ → Frag e
  → infer′ k σ rs Γ e m hd ≡ ok (A , u)
  → Inf {σ} Γ m e A u
check-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m {e A u} → GoodSig σ → FragCtx Γ → Frag e → Frag A
  → check k σ rs Γ m e A ≡ ok u → Chk {σ} Γ m e A u
data TyR (σ : Sig) {n} (Γ : Ctx n) (A : Tm n) : Set where
  ty : σ , Γ ⊢ A wf → TyR σ Γ A
  ty-miss : TyR σ Γ A

checkTy-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} {A} → GoodSig σ → FragCtx Γ → Frag A
  → checkTy k σ rs Γ A ≡ ok tt → TyR σ Γ A
checkTy-el : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} {A T u} → GoodSig σ → FragCtx Γ → Frag A
  → infer k σ rs Γ spec A ≡ ok (T , u) → conv k σ T typ ≡ ok tt → TyR σ Γ A
checkLam-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m {e T u} → GoodSig σ → FragCtx Γ → Frag e → Frag T
  → (r : Result (Qty × Tm n × Tm (suc n))) → viewPi k σ T ≡ r
  → checkLam k σ rs Γ m e T r ≡ ok u → Chk {σ} Γ m e T u
checkAgainst-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m {e A u} → GoodSig σ → FragCtx Γ → Frag e → Frag A
  → checkAgainst k σ rs Γ m e A (viewData k σ A) (ctorSpine e) ≡ ok u
  → Chk {σ} Γ m e A u
inferConv-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m {e A u} → GoodSig σ → FragCtx Γ → Frag e → Frag A
  → inferConv k σ rs Γ m e A ≡ ok u
  → Chk {σ} Γ m e A u
-- a constructor spine from its head: the head is a constructor of di,
-- and the arguments so far follow the constructor's telescope
inferCtorSpine-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m {di ps e R u d} → GoodSig σ → FragCtx Γ
  → Frag e → FragL ps → lookupData σ di ≡ ok d
  → inferCtorSpine k σ rs Γ m di ps e ≡ ok (R , u)
  → Maybe (∃ λ as → ∃ λ ci → ∃ λ c → ∃ λ T
    → Spine (ctor di ci) as e × (lookupCtor d ci ≡ ok c)
    × InstParams σ (closed (Ctor.ctype c)) ps T
    × (σ , Γ ⊢[ m ] T ▹ as ⇝ R ⊣ u) × Frag R × Tel di (nparams d + nidxs d) R)
checkCtorApp-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m {di ps e X u d} → GoodSig σ → FragCtx Γ
  → Frag e → FragL ps → Frag X → lookupData σ di ≡ ok d
  → checkCtorApp k σ rs Γ m di ps e X ≡ ok u
  → Maybe (∃ λ as → ∃ λ ci → ∃ λ c → ∃ λ T → ∃ λ R
    → Spine (ctor di ci) as e × (lookupCtor d ci ≡ ok c)
    × InstParams σ (closed (Ctor.ctype c)) ps T
    × (σ , Γ ⊢[ m ] T ▹ as ⇝ R ⊣ u) × (σ ⊢[ spec ] R ≈ X))
checkBr-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m di ci sm {np ar ty br q D P args u} → GoodSig σ → FragCtx Γ
  → Frag ty → Frag br → Frag D → Frag P → FragL args → Tel di ar ty → nparamsOf σ di ≡ np
  → checkBr k σ rs Γ m di ci sm ty br (lam q D P) args ≡ ok u
  → Maybe (∃ λ X → BrTy σ di ci np ty P args X × (σ , Γ ⊢[ m ] br ⇐ X ⊣ u))
checkBrPi-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m di ci sm {np ar q A B br q′ D P args u} → GoodSig σ → FragCtx Γ
  → Frag A → Frag B → Frag br → Frag D → Frag P → FragL args → Tel di ar B → nparamsOf σ di ≡ np
  → checkBrPi k σ rs Γ m di ci sm q A B br (lam q′ D P) args ≡ ok u
  → Maybe (∃ λ X → BrTy σ di ci np (pi q A B) P args X × (σ , Γ ⊢[ m ] br ⇐ X ⊣ u))
checkBranches-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m di sm {np ar params is q D P ci cs bs u} → GoodSig σ → FragCtx Γ
  → FragL params → FragL is → Frag D → Frag P → FragL bs → CtorsOk di ar cs → nparamsOf σ di ≡ np → length params ≡ np
  → checkBranches k σ rs Γ m di sm params is (lam q D P) ci cs bs ≡ ok u
  → Maybe (σ , Γ ⊢[ m ] bs brs⟨ di , params , is , P , ci ⟩ cs ⊣ u)
-- the motive: over the scrutinee when the data type has no indices,
-- otherwise over the indices and the scrutinee (Judgement.MotiveOk)
checkMotive-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} {di ixs params P} → GoodSig σ → FragCtx Γ
  → FragL params → Frag P → FragIdxs ixs
  → checkMotive k σ rs Γ di ixs params P ≡ ok tt
  → Maybe (MotiveOk σ Γ di params ixs P)

------------------------------------------------------------------------
-- inferConv: infer then convert (Check's default for ⇐).
------------------------------------------------------------------------

inferConv-sound k σ rs {Γ = Γ} m {e} {A} G FΓ Fe FA eq with infer k σ rs Γ m e in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (B , u′) with conv k σ B A in ceq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with ok-inj eq
...     | refl with infer-sound k σ rs m false G FΓ Fe ieq
...       | inf FB D c = chk (⇐-conv D (≈-trans c (conv-sound k σ (GoodSig.frag G) FB FA ceq)))
...       | inf′ D = chk′ (⇐-conv D ≈-refl)
...       | miss = miss

------------------------------------------------------------------------
-- infer
------------------------------------------------------------------------

-- var
infer-sound k σ rs {Γ = Γ} run hd G FΓ (f-var {x = x}) eq with qtyOf Γ x in qeq
... | erased = ⊥-elim (fail≢ok eq)
... | affine with isRunType k σ (typOf Γ x)
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok false = ⊥-elim (fail≢ok eq)
...   | ok true with ok-inj eq
...     | refl = inf (FΓ x) (var-run qeq (λ ())) ≈-refl
infer-sound k σ rs {Γ = Γ} run hd G FΓ (f-var {x = x}) eq | reuse with isRunType k σ (typOf Γ x)
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok false = ⊥-elim (fail≢ok eq)
...   | ok true with ok-inj eq
...     | refl = inf (FΓ x) (var-run qeq (λ ())) ≈-refl
infer-sound k σ rs {Γ = Γ} evid hd G FΓ (f-var {x = x}) eq with qtyOf Γ x in qeq
... | erased = ⊥-elim (fail≢ok eq)
... | affine with ok-inj eq
...   | refl = inf (FΓ x) (var-evid qeq (λ ())) ≈-refl
infer-sound k σ rs {Γ = Γ} evid hd G FΓ (f-var {x = x}) eq | reuse with ok-inj eq
...   | refl = inf (FΓ x) (var-evid qeq (λ ())) ≈-refl
infer-sound k σ rs spec hd G FΓ (f-var {x = x}) refl = inf (FΓ x) ⇒-var-spec ≈-refl

-- Type has no type
infer-sound k σ rs run hd G FΓ f-typ eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs evid hd G FΓ f-typ eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs spec hd G FΓ f-typ eq = ⊥-elim (fail≢ok eq)

-- Π
infer-sound k σ rs run hd G FΓ (f-pi _ _) eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs evid hd G FΓ (f-pi _ _) eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs {Γ = Γ} spec hd G FΓ (f-pi {q = q} {A = A} {B = B} FA FB) eq with checkTy k σ rs Γ A in teq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with check k σ (extRec rs false false) (ext Γ q A) spec B typ in beq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok u′ with ok-inj eq
...     | refl with checkTy-sound k σ rs G FΓ FA teq | check-sound k σ (extRec rs false false) spec G (FragCtx-ext FΓ FA) FB f-typ beq
...       | ty WA | chk DB = inf f-typ (⇒-pi WA DB) ≈-refl
...       | ty WA | chk′ _ = miss
...       | ty WA | miss = miss
...       | ty-miss | _ = miss

-- λ
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-lam {q = q} {A = A} {t = t} FA Ft) eq with checkTy k σ rs Γ A in teq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with (if eqQty q reuse then isCopy k σ A >>= guard notCopy else ok tt) in req
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with infer k σ (lamRec rs) (ext Γ q A) m t in ieq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok (B , u₀ Vec.∷ us) with checkBound m q u₀ in beq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok tt with ok-inj eq
...         | refl = lamGo Ft ieq
  where
    lamGo : Frag t → infer k σ (lamRec rs) (ext Γ q A) m t ≡ ok (B , u₀ Vec.∷ us)
      → Inf {σ} Γ m (lam q A t) (pi q A B) us
    lamGo Ft′ ieq′ with infer-sound k σ (lamRec rs) m false G (FragCtx-ext FΓ FA) Ft′ ieq′
    ... | inf FB D c = lamInf (checkTy-sound k σ rs G FΓ FA teq) FB D c
      where
        lamInf : ∀ {B′} → TyR σ Γ A → Frag B → σ , ext Γ q A ⊢[ m ] t ⇒ B′ ⊣ (u₀ Vec.∷ us)
          → σ ⊢[ spec ] B′ ≈ B → Inf {σ} Γ m (lam q A t) (pi q A B) us
        lamInf (ty WA) FB D c = inf (f-pi FA FB)
                    (⇒-lam WA (copyOk-sound k σ q (GoodSig.frag G) FA req) D beq)
                    (≈-pi ≈-refl c)
        lamInf ty-miss _ _ _ = miss
    ... | inf′ _ = miss
    ... | miss = miss

-- application: the head as a head; the descent test on the maximal
-- spine is the outermost app's and has no bearing on ⊢
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq with infer′ k σ rs Γ f m true in feq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (ft , fu) with viewPi k σ ft in peq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok (affine , A , B) with check k σ rs Γ m a A in aeq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok au with appUses σ m f fu au in ueq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok uses with checkRec m hd rs (app f a)
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok _ with ok-inj eq
...           | refl with infer-sound k σ rs m true G FΓ Ff feq
...             | inf Fft Df c with viewPi-Frag k σ (GoodSig.frag G) Fft peq
...               | FA , FB with check-sound k σ rs m G FΓ Fa FA aeq
...                 | chk Da = inf (Frag-inst FB Fa)
                      (⇒-app-aff Df (≈-trans c (viewPi-≈ k σ (GoodSig.frag G) Fft peq)) Da ueq) ≈-refl
...                 | chk′ _ = miss
...                 | miss = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq
    | ok (ft , fu) | ok (affine , A , B) | ok au | ok uses | ok _ | refl | inf′ _ = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq
    | ok (ft , fu) | ok (affine , A , B) | ok au | ok uses | ok _ | refl | miss = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq | ok (ft , fu) | ok (reuse , A , B) with isData k σ A in deq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok false with isCopy k σ A in ceq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok false = ⊥-elim (fail≢ok eq)
...       | ok true with check k σ rs Γ m a A in aeq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok au with appUses σ m f fu (scaleω au) in ueq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok uses with checkRec m hd rs (app f a)
...             | fail _ = ⊥-elim (fail≢ok eq)
...             | ok _ with ok-inj eq
...               | refl with infer-sound k σ rs m true G FΓ Ff feq
...                 | inf Fft Df c with viewPi-Frag k σ (GoodSig.frag G) Fft peq
...                   | FA , FB with check-sound k σ rs m G FΓ Fa FA aeq
...                     | chk Da = inf (Frag-inst FB Fa)
                          (⇒-app-copy Df (≈-trans c (viewPi-≈ k σ (GoodSig.frag G) Fft peq))
                            (isCopy-sound k σ (GoodSig.frag G) FA ceq) Da ueq) ≈-refl
...                     | chk′ _ = miss
...                     | miss = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq
    | ok (ft , fu) | ok (reuse , A , B) | ok false | ok true | ok au | ok uses | ok _ | refl | inf′ _ = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq
    | ok (ft , fu) | ok (reuse , A , B) | ok false | ok true | ok au | ok uses | ok _ | refl | miss = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq | ok (ft , fu) | ok (reuse , A , B) | ok true with check k σ rs Γ m a A in aeq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok au with appUses σ m f fu au in ueq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok uses with checkRec m hd rs (app f a)
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok _ with ok-inj eq
...             | refl with infer-sound k σ rs m true G FΓ Ff feq
...               | inf Fft Df c with viewPi-Frag k σ (GoodSig.frag G) Fft peq
...                 | FA , FB with check-sound k σ rs m G FΓ Fa FA aeq
...                   | chk Da = inf (Frag-inst FB Fa)
                        (⇒-app-reuse Df (≈-trans c (viewPi-≈ k σ (GoodSig.frag G) Fft peq))
                          (isData-sound k σ (GoodSig.frag G) FA deq) Da ueq) ≈-refl
...                   | chk′ _ = miss
...                   | miss = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq
    | ok (ft , fu) | ok (reuse , A , B) | ok true | ok au | ok uses | ok _ | refl | inf′ _ = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq
    | ok (ft , fu) | ok (reuse , A , B) | ok true | ok au | ok uses | ok _ | refl | miss = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq | ok (ft , fu) | ok (erased , A , B) with check k σ rs Γ spec a A in aeq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok au with eqMode m spec in meq
...       | true with eqMode-sound m spec meq
...         | refl with checkRec spec hd rs (app f a)
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok _ with ok-inj eq
...             | refl with infer-sound k σ rs spec true G FΓ Ff feq
...               | inf Fft Df c with spec-⇒-uses Df
...                 | refl with viewPi-Frag k σ (GoodSig.frag G) Fft peq
...                   | FA , FB with check-sound k σ rs spec G FΓ Fa FA aeq
...                     | chk Da = inf (Frag-inst FB Fa)
                          (⇒-app-era Df (≈-trans c (viewPi-≈ k σ (GoodSig.frag G) Fft peq)) Da) ≈-refl
...                     | chk′ _ = miss
...                     | miss = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq
    | ok (ft , fu) | ok (erased , A , B) | ok au | true | refl | ok _ | refl | inf′ _ = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq
    | ok (ft , fu) | ok (erased , A , B) | ok au | true | refl | ok _ | refl | miss = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq | ok (ft , fu) | ok (erased , A , B) | ok au | false
  with checkRec m hd rs (app f a)
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok _ with ok-inj eq
...           | refl with infer-sound k σ rs m true G FΓ Ff feq
...             | inf Fft Df c with viewPi-Frag k σ (GoodSig.frag G) Fft peq
...               | FA , FB with check-sound k σ rs spec G FΓ Fa FA aeq
...                 | chk Da = inf (Frag-inst FB Fa)
                      (⇒-app-era Df (≈-trans c (viewPi-≈ k σ (GoodSig.frag G) Fft peq)) Da) ≈-refl
...                 | chk′ _ = miss
...                 | miss = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq
    | ok (ft , fu) | ok (erased , A , B) | ok au | false | ok _ | refl | inf′ _ = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq
    | ok (ft , fu) | ok (erased , A , B) | ok au | false | ok _ | refl | miss = miss

-- Nat
infer-sound k σ rs run hd G FΓ f-nat eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs evid hd G FΓ f-nat eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs spec hd G FΓ f-nat refl = inf f-typ ⇒-nat ≈-refl
infer-sound k σ rs m hd G FΓ f-ze refl = inf f-nat ⇒-ze ≈-refl
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-su {t = t} Ft) eq with check k σ rs Γ m t nat in ceq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok u′ with ok-inj eq
...   | refl with check-sound k σ rs m G FΓ Ft f-nat ceq
...     | chk Dt = inf f-nat (⇒-su Dt) ≈-refl
...     | chk′ _ = miss
...     | miss = miss

-- Unit, Empty
infer-sound k σ rs run hd G FΓ f-unit eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs evid hd G FΓ f-unit eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs spec hd G FΓ f-unit refl = inf f-typ ⇒-unit ≈-refl
infer-sound k σ rs m hd G FΓ f-one refl = inf f-unit ⇒-one ≈-refl
infer-sound k σ rs run hd G FΓ f-empty eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs evid hd G FΓ f-empty eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs spec hd G FΓ f-empty refl = inf f-typ ⇒-empty ≈-refl

-- data former, constructor
infer-sound k σ rs run hd G FΓ f-dty eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs evid hd G FΓ f-dty eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs spec hd G FΓ (f-dty {i = i}) eq with lookupData σ i in leq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok d with ok-inj eq
...   | refl = inf (Frag-dtyType (DataDecl.pqtys d) (proj₁ (FragSig.datas (GoodSig.frag G) i d leq)))
              (⇒-dty leq) ≈-refl
infer-sound k σ rs m hd G FΓ f-ctor eq = ⊥-elim (fail≢ok eq)

-- match on data
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-mData {e = e} {P = P} {bs = bs} Fe FP Fbs) eq with infer k σ rs Γ m e in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (et , eu) with viewData k σ et in veq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok (di , params , idxs) with viewData-sound k σ veq
...     | et′ , d , args , weq , leq , sp , lenA , peq , ieq′ rewrite leq
      with checkMotive k σ rs Γ di (DataDecl.idxs d) params P in meq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok tt with infer-sound k σ rs m false G FΓ Fe ieq
...       | miss = miss
...       | inf′ _ = miss
...       | inf Fet De c
      with firstMotLam-form di params P
             (subst FragL (sym peq) (FragL-take (nparams d) (proj₂ (Frag-Spine sp (whnf-Frag k σ (GoodSig.frag G) Fet weq)))))
             (proj₁ (FragSig.datas (GoodSig.frag G) di d leq))
...       | q , D , mform , FD rewrite mform
      with checkBranches k σ rs Γ m di (scrutOk rs e) params idxs (lam q D P) 0 (DataDecl.ctors d) bs in beq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok bu with combine m eu bu in ceq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok uses with ok-inj eq
...           | refl =
  let fs = GoodSig.frag G
      Fargs = proj₂ (Frag-Spine sp (whnf-Frag k σ fs Fet weq))
      Fparams = subst FragL (sym peq) (FragL-take (nparams d) Fargs)
      Fidxs = subst FragL (sym ieq′) (FragL-drop (nparams d) Fargs)
      pieq : params ++ idxs ≡ args
      pieq = trans (cong₂ _++_ peq ieq′) (take++drop≡id (nparams d) args)
      lps : length params ≡ nparams d
      lps = trans (cong length peq)
              (trans (length-take (nparams d) args)
                (trans (cong (nparams d ⊓_) lenA) (m≤n⇒m⊓n≡m (m≤m+n (nparams d) (nidxs d)))))
      lidx : length idxs ≡ nidxs d
      lidx = trans (cong length ieq′)
               (trans (length-drop (nparams d) args)
                 (trans (cong (_∸ nparams d) lenA) (m+n∸m≡n (nparams d) (nidxs d))))
  in matchGo Fidxs fs pieq lps lidx
       (checkMotive-sound k σ rs G FΓ Fparams FP (proj₁ (FragSig.datas fs di d leq)) meq)
       (checkBranches-sound k σ rs m di (scrutOk rs e) {np = nparams d} G FΓ Fparams Fidxs FD FP Fbs
         (ctorsOk {i = di} {d = d} G leq) (nparamsOf-ok {σ} {di} {d} leq) lps beq)
  where
    matchGo : FragL idxs → FragSig σ → params ++ idxs ≡ args
      → length params ≡ nparams d → length idxs ≡ nidxs d
      → Maybe (MotiveOk σ Γ di params (DataDecl.idxs d) P)
      → Maybe (σ , Γ ⊢[ m ] bs brs⟨ di , params , idxs , P , 0 ⟩ DataDecl.ctors d ⊣ bu)
      → Inf {σ} Γ m (mData e P bs) (appsFrom (lam q D P) (idxs ++ (e ∷ []))) uses
    matchGo Fidxs fs pieq lps lidx (just mot) (just brs) =
      inf (Frag-appsFrom (f-lam FD FP) (FragL-++ Fidxs (fl-∷ Fe fl-[])))
        (⇒-mData De
          (≈-trans c (≈-trans (whnf-≈ k σ fs Fet weq)
            (≈-≡ (trans (Spine-≡ sp) (cong (appsFrom (dty di)) (sym pieq))))))
          leq lps lidx mot brs ceq)
        (≈-sym (motApp-β idxs))
    matchGo _ _ _ _ _ (just _) nothing = miss
    matchGo _ _ _ _ _ nothing _ = miss

-- match on Nat
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-mNat {e = e} {P = P} {z = z} {s = s} Fe FP Fz Fs) eq with check k σ rs Γ m e nat in eeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok eu with checkTy k σ (extRec rs false false) (ext Γ affine nat) P in peq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with check k σ rs Γ m z (inst P ze) in zeq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok zu with check k σ (extRec rs (scrutOk rs e) (scrutOk rs e)) (ext Γ (predQty Γ e) nat) m s (motSuc P) in seq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok (u₀ Vec.∷ sus) with checkBound m (predQty Γ e) u₀ in beq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok tt with combine m eu (combineAlt m zu sus) in ceq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok uses with ok-inj eq
...             | refl = natGo
                  (checkTy-sound k σ (extRec rs false false) G (FragCtx-ext FΓ f-nat) FP peq)
                  (check-sound k σ rs m G FΓ Fe f-nat eeq)
                  (check-sound k σ rs m G FΓ Fz (Frag-inst FP f-ze) zeq)
                  (check-sound k σ (extRec rs (scrutOk rs e) (scrutOk rs e)) m G (FragCtx-ext FΓ f-nat) Fs (Frag-motSuc FP) seq)
  where
    natGo : TyR σ (ext Γ affine nat) P
      → Chk {σ} Γ m e nat eu → Chk {σ} Γ m z (inst P ze) zu
      → Chk {σ} (ext Γ (predQty Γ e) nat) m s (motSuc P) (u₀ Vec.∷ sus)
      → Inf {σ} Γ m (mNat e P z s) (inst P e) uses
    natGo (ty WP) (chk De) (chk Dz) (chk Ds) = inf (Frag-inst FP Fe) (⇒-mNat De WP Dz Ds beq ceq) ≈-refl
    natGo (ty _) (chk _) (chk _) (chk′ _) = miss
    natGo (ty _) (chk _) (chk _) miss = miss
    natGo (ty _) (chk _) (chk′ _) _ = miss
    natGo (ty _) (chk _) miss _ = miss
    natGo (ty _) (chk′ _) _ _ = miss
    natGo (ty _) miss _ _ = miss
    natGo ty-miss _ _ _ = miss

-- match on Empty
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-mEmp {e = e} {P = P} Fe FP) eq with check k σ rs Γ m e empty in eeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok eu with checkTy k σ (extRec rs false false) (ext Γ affine empty) P in peq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with ok-inj eq
...     | refl with checkTy-sound k σ (extRec rs false false) G (FragCtx-ext FΓ f-empty) FP peq | check-sound k σ rs m G FΓ Fe f-empty eeq
...       | ty WP | chk De = inf (Frag-inst FP Fe) (⇒-mEmp De WP) ≈-refl
...       | ty WP | chk′ _ = miss
...       | ty WP | miss = miss
...       | ty-miss | _ = miss

-- match on Unit
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-mUnit {e = e} {P = P} {u = t} Fe FP Ft) eq with check k σ rs Γ m e unit in eeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok eu with checkTy k σ (extRec rs false false) (ext Γ affine unit) P in peq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with check k σ rs Γ m t (inst P one) in teq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok uu with combine m eu uu in ceq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok uses with ok-inj eq
...         | refl = unitGo
                  (checkTy-sound k σ (extRec rs false false) G (FragCtx-ext FΓ f-unit) FP peq)
                  (check-sound k σ rs m G FΓ Fe f-unit eeq)
                  (check-sound k σ rs m G FΓ Ft (Frag-inst FP f-one) teq)
  where
    unitGo : TyR σ (ext Γ affine unit) P
      → Chk {σ} Γ m e unit eu → Chk {σ} Γ m t (inst P one) uu
      → Inf {σ} Γ m (mUnit e P t) (inst P e) uses
    unitGo (ty WP) (chk De) (chk Du) = inf (Frag-inst FP Fe) (⇒-mUnit De WP Du ceq) ≈-refl
    unitGo (ty _) (chk _) (chk′ _) = miss
    unitGo (ty _) (chk _) miss = miss
    unitGo (ty _) (chk′ _) _ = miss
    unitGo (ty _) miss _ = miss
    unitGo ty-miss _ _ = miss

-- identity type, refl, rewrite
infer-sound k σ rs run hd G FΓ (f-idt _ _ _) eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs evid hd G FΓ (f-idt _ _ _) eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs {Γ = Γ} spec hd G FΓ (f-idt {A = A} {a = a} {b = b} FA Fa Fb) eq with checkTy k σ rs Γ A in teq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with floatIdOk k σ A
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with check k σ rs Γ spec a A in aeq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok ua with check k σ rs Γ spec b A in beq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok ub with ok-inj eq
...         | refl = idGo (checkTy-sound k σ rs G FΓ FA teq)
                     (check-sound k σ rs spec G FΓ Fa FA aeq)
                     (check-sound k σ rs spec G FΓ Fb FA beq)
  where
    idGo : ∀ {ua ub} → TyR σ Γ A → Chk {σ} Γ spec a A ua → Chk {σ} Γ spec b A ub
      → Inf {σ} Γ spec (idt A a b) typ u0s
    idGo (ty WA) (chk Da) (chk Db) = inf f-typ (⇒-idt WA Da Db) ≈-refl
    idGo (ty _) (chk _) (chk′ _) = miss
    idGo (ty _) (chk _) miss = miss
    idGo (ty _) (chk′ _) _ = miss
    idGo (ty _) miss _ = miss
    idGo ty-miss _ _ = miss
infer-sound k σ rs m hd G FΓ f-rfl eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-rwt {e = e} {P = P} {t = t} Fe FP Ft) eq with infer k σ rs Γ (rwtMode m) e in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (et , eu) with viewId k σ et in veq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok (A , l , r) with checkTy k σ (extRec rs false false) (ext Γ affine A) P in peq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok tt with check k σ rs Γ m t (inst P r) in teq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok tu with ok-inj eq
...         | refl = rwtGo Fe ieq
  where
    rwtGo : Frag e → infer k σ rs Γ (rwtMode m) e ≡ ok (et , eu)
      → Inf {σ} Γ m (rwt e P t) (inst P l) tu
    rwtGo Fe′ ieq′ with infer-sound k σ rs (rwtMode m) false G FΓ Fe′ ieq′
    ... | inf′ _ = miss
    ... | miss = miss
    ... | inf Fet De c with viewId-Frag k σ (GoodSig.frag G) Fet veq
    ... | FA , Fl , Fr
        with checkTy-sound k σ (extRec rs false false) G (FragCtx-ext FΓ FA) FP peq
           | check-sound k σ rs m G FΓ Ft (Frag-inst FP Fr) teq
    ... | ty WP | chk Dt = inf (Frag-inst FP Fl)
            (⇒-rwt De (≈-trans c (viewId-≈ k σ (GoodSig.frag G) Fet veq)) WP Dt) ≈-refl
    ... | ty _ | chk′ _ = miss
    ... | ty _ | miss = miss
    ... | ty-miss | _ = miss

-- definitions: the self-application test has no bearing on ⊢
infer-sound k σ {n} rs m hd G FΓ (f-def {i = i}) eq with selfApplied m hd rs i
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with lookupDef σ i in leq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok d with allowedDef (Def.dmode d) m in aeq
...     | false = ⊥-elim (fail≢ok eq)
...     | true with eqMode m run
...       | false with ok-inj eq
...         | refl = inf (Frag-closed (proj₁ (FragSig.defs (GoodSig.frag G) i d leq))) (⇒-def leq aeq) ≈-refl
infer-sound k σ {n} rs m hd G FΓ (f-def {i = i}) eq | ok tt | ok d | true | true with isRunType k σ (closed {n} (Def.dtype d))
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok false = ⊥-elim (fail≢ok eq)
...         | ok true with ok-inj eq
...           | refl = inf (Frag-closed (proj₁ (FragSig.defs (GoodSig.frag G) i d leq))) (⇒-def leq aeq) ≈-refl

-- annotation
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-ann {e = e} {A = A} Fe FA) eq with checkTy k σ rs Γ A in teq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with check k σ rs Γ m e A in ceq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok u′ with ok-inj eq
...     | refl with checkTy-sound k σ rs G FΓ FA teq | check-sound k σ rs m G FΓ Fe FA ceq
...       | ty WA | chk De = inf FA (⇒-ann WA De) ≈-refl
...       | ty _ | chk′ _ = miss
...       | ty _ | miss = miss
...       | ty-miss | _ = miss

-- products: A × B is spec-only; a pair infers a product of the
-- components' types
infer-sound k σ rs run hd G FΓ (f-prod _ _) eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs evid hd G FΓ (f-prod _ _) eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs {Γ = Γ} spec hd G FΓ (f-prod {A = A} {B = B} FA FB) eq with check k σ rs Γ spec A typ in aeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok _ with check k σ rs Γ spec B typ in beq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok _ with ok-inj eq
...     | refl with check-sound k σ rs spec G FΓ FA f-typ aeq
...       | chk DA with check-sound k σ rs spec G FΓ FB f-typ beq
...         | chk DB = inf f-typ (⇒-prod DA DB) ≈-refl
...         | chk′ _ = miss
...         | miss = miss
infer-sound k σ rs {Γ = Γ} spec hd G FΓ (f-prod {A = A} {B = B} FA FB) eq
    | ok _ | ok _ | refl | chk′ _ = miss
infer-sound k σ rs {Γ = Γ} spec hd G FΓ (f-prod {A = A} {B = B} FA FB) eq
    | ok _ | ok _ | refl | miss = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-pair {a = a} {b = b} Fa Fb) eq with infer k σ rs Γ m a in aeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (A , au) with infer k σ rs Γ m b in beq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok (B , bu) with combine m au bu in ceq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok uses with ok-inj eq
...       | refl with infer-sound k σ rs m false G FΓ Fa aeq | infer-sound k σ rs m false G FΓ Fb beq
...         | inf FA Da cA | inf FB Db cB = inf (f-prod FA FB) (⇒-pair Da Db ceq) (≈-prod cA cB)
...         | inf FA Da _ | inf′ Db = inf′ (⇒-pair Da Db ceq)
...         | inf′ Da | inf FB Db _ = inf′ (⇒-pair Da Db ceq)
...         | inf′ Da | inf′ Db = inf′ (⇒-pair Da Db ceq)
...         | miss | _ = miss
...         | _ | miss = miss

-- let in inference mode: the body's type is strengthened past the two
-- components; strengthen₂-sound turns success into a double weakening.
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-letp {e = e} {t = t} Fe Ft) eq with infer k σ rs Γ m e in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (E , eu) with viewProd k σ E in veq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok (A , B) with infer k σ (extRec (extRec rs false false) false false)
                             (ext (ext Γ affine A) affine (wk B)) m t in teq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok (T , ub Vec.∷ ua Vec.∷ tus) with strengthen₂ T in seq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok C with checkBound m affine ub in bb
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok tt with checkBound m affine ua in ba
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok tt with combine m eu tus in ceq
...             | fail _ = ⊥-elim (fail≢ok eq)
...             | ok us with ok-inj eq
...               | refl with infer-sound k σ rs m false G FΓ Fe ieq
...                 | inf FE De c with viewProd-Frag k σ (GoodSig.frag G) FE veq
...                   | FA , FB with infer-sound k σ (extRec (extRec rs false false) false false) m false G
                                      (FragCtx-ext (FragCtx-ext FΓ FA) (Frag-wk FB)) Ft teq
...                     | inf FT Dt cT with strengthen₂-sound T seq
...                       | refl = inf (Frag-unren suc C (Frag-unren suc (wk C) FT))
                          (⇒-letp De (≈-trans c (viewProd-≈ k σ (GoodSig.frag G) FE veq)) Dt cT bb ba ceq)
                          ≈-refl
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-letp {e = e} {t = t} Fe Ft) eq
    | ok (E , eu) | ok (A , B) | ok (T , ub Vec.∷ ua Vec.∷ tus) | ok C | ok tt | ok tt | ok us | refl
    | inf FE De c | FA , FB | inf′ _ = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-letp {e = e} {t = t} Fe Ft) eq
    | ok (E , eu) | ok (A , B) | ok (T , ub Vec.∷ ua Vec.∷ tus) | ok C | ok tt | ok tt | ok us | refl
    | inf FE De c | FA , FB | miss = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-letp {e = e} {t = t} Fe Ft) eq
    | ok (E , eu) | ok (A , B) | ok (T , ub Vec.∷ ua Vec.∷ tus) | ok C | ok tt | ok tt | ok us | refl
    | inf′ _ = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-letp {e = e} {t = t} Fe Ft) eq
    | ok (E , eu) | ok (A , B) | ok (T , ub Vec.∷ ua Vec.∷ tus) | ok C | ok tt | ok tt | ok us | refl
    | miss = miss

-- ν infers its kind. Run and evidence do not promote an erased term.
infer-sound k σ rs run hd G FΓ (f-nu _) eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs evid hd G FΓ (f-nu _) eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs {Γ = Γ} spec hd G FΓ (f-nu {F = F} FF) eq with nuKind F in keq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok K with nuBodyProd F in beq
... | false = ⊥-elim (fail≢ok eq)
... | true with check k σ (extRec rs false false) (ext Γ affine K) spec F (wk K) in ceq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok _ with strictPos F in speq
... | false = ⊥-elim (fail≢ok eq)
... | true with ok-inj eq
... | refl with check-sound k σ (extRec rs false false) spec G (FragCtx-ext FΓ (nuKindAt-Frag 0 F FF keq)) FF (Frag-wk (nuKindAt-Frag 0 F FF keq)) ceq
... | chk DB = inf (nuKindAt-Frag 0 F FF keq) (⇒-nu keq beq speq DB) ≈-refl
... | chk′ _ = miss
... | miss = miss

-- unfold infers a stream when the step's type is Stream's Π. A declared
-- family does not: its codomain is not the seed's type, so the views fail.
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-unf {s = seed} {f = pair h t} Fs (f-pair _ _) fs-step) eq
  with infer k σ rs Γ m seed
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (S , _) with infer k σ rs Γ m (pair h t)
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (ft , _) with viewPi k σ ft
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok _ = miss
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-unf {s = seed} {f = lam q A (pair h t)} Fs Ff fs-pair) eq
  with infer k σ rs Γ m seed in seq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (S , seedU) with infer k σ rs Γ m (lam q A (pair h t)) in feq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (ft , fu) with viewPi k σ ft in peq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (q′ , S′ , Body) with conv k σ S′ S in ceq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with viewProd k σ (inst Body seed) in veq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (Ah , S2) with conv k σ S2 S in s2eq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with checkUnfold k σ m rs (lam q A (pair h t))
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with combine m seedU fu in ueq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok uses with ok-inj eq
... | refl = unfGo Fs Ff seq feq
  where
    unfGo : Frag seed → Frag (lam q A (pair h t))
      → infer k σ rs Γ m seed ≡ ok (S , seedU)
      → infer k σ rs Γ m (lam q A (pair h t)) ≡ ok (ft , fu)
      → Inf {σ} Γ m (unf seed (lam q A (pair h t))) (nu (prod (wk Ah) (var Fin.zero))) uses
    unfGo Fs′ f′ seq′ feq′ with infer-sound k σ rs m false G FΓ Fs′ seq′
    ... | inf _ _ (≈-sym _) = miss
    ... | inf _ _ (≈-trans _ _) = miss
    ... | inf _ _ (≈-step _) = miss
    ... | inf′ _ = miss
    ... | miss = miss
    ... | inf FSs Ds ≈-refl with infer-sound k σ rs m false G FΓ f′ feq′
    ... | inf _ _ (≈-sym _) = miss
    ... | inf _ _ (≈-trans _ _) = miss
    ... | inf _ _ (≈-step _) = miss
    ... | inf′ _ = miss
    ... | miss = miss
    ... | inf Ftf Df ≈-refl = unfBoth Ds Df FSs Ftf
      where
        unfBoth : σ , Γ ⊢[ m ] seed ⇒ S ⊣ seedU → σ , Γ ⊢[ m ] lam q A (pair h t) ⇒ ft ⊣ fu
          → Frag S → Frag ft
          → Inf {σ} Γ m (unf seed (lam q A (pair h t))) (nu (prod (wk Ah) (var Fin.zero))) uses
        unfBoth Ds Df FSs Ftf with strengthen Body in sbeq
        ... | fail _ = miss
        ... | ok C with viewPi-Frag k σ (GoodSig.frag G) Ftf peq | viewProd-Frag k σ (GoodSig.frag G) (Frag-inst (proj₂ (viewPi-Frag k σ (GoodSig.frag G) Ftf peq)) Fs) veq
        ... | FS′ , FB | FAh , FS2 =
          inf (f-nu (f-prod (Frag-wk FAh) f-var))
            (⇒-unf Ds Df
              (≈-trans (viewPi-≈ k σ (GoodSig.frag G) Ftf peq)
                (≈-pi (conv-sound k σ (GoodSig.frag G) FS′ FSs ceq)
                  (streamBody sbeq (viewProd-≈ k σ (GoodSig.frag G) (Frag-inst FB Fs) veq)
                    (conv-sound k σ (GoodSig.frag G) FS2 FSs s2eq))))
              us-pair ueq)
            ≈-refl

-- uncons infers the pair the step returns.
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-ucons {s = s} Fs) eq with infer k σ rs Γ m s in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , u) with whnf k σ T in weq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok T′ with unfStepOf T T′ in seq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (G′ , _) with ok-inj eq
... | refl with infer-sound k σ rs m false G FΓ Fs ieq
... | inf FT Ds ≈-refl =
  inf (unfStepOf-Frag T T′ FT (whnf-Frag k σ (GoodSig.frag G) FT weq) seq)
      (⇒-ucons Ds (whnf-≈ k σ (GoodSig.frag G) FT weq) seq) ≈-refl
... | inf _ _ _ = miss
... | inf′ _ = miss
... | miss = miss

------------------------------------------------------------------------
-- check
------------------------------------------------------------------------

-- λ against a type: viewPi, or infer and convert (checkLam-sound is
-- split on the view so that the fragment witness is matched in a clause
-- head)
check-sound k σ rs m {e = lam q A t} {A = T} G FΓ Fe FT eq = checkLam-sound k σ rs m G FΓ Fe FT (viewPi k σ T) refl eq

-- refl against a type
check-sound k σ rs {Γ = Γ} m {A = T} G FΓ f-rfl FT eq with eqMode m run in req
... | true = ⊥-elim (fail≢ok eq)
... | false with viewId k σ T in veq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok (A , a , b) with floatIdOk k σ A
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok tt with conv k σ a b in ceq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok tt with ok-inj eq
...         | refl with viewId-Frag k σ (GoodSig.frag G) FT veq
...           | FA , Fa , Fb = chk (⇐-refl (viewId-≈ k σ (GoodSig.frag G) FT veq) (conv-sound k σ (GoodSig.frag G) Fa Fb ceq) req)

-- pair against a type: viewProd, then the components
check-sound k σ rs {Γ = Γ} m {A = T} G FΓ (f-pair {a = a} {b = b} Fa Fb) FT eq with viewProd k σ T in veq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (A , B) with check k σ rs Γ m a A in aeq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok au with check k σ rs Γ m b B in beq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok bu with viewProd-Frag k σ (GoodSig.frag G) FT veq
...       | FA , FB with check-sound k σ rs m G FΓ Fa FA aeq | check-sound k σ rs m G FΓ Fb FB beq
...         | chk Da | chk Db = chk (⇐-pair (viewProd-≈ k σ (GoodSig.frag G) FT veq) Da Db eq)
...         | _ | _ = miss

-- let (a, b) = e in t against a type: the scrutinee is inferred and
-- viewed as a product, the body checked under the two binders
check-sound k σ rs {Γ = Γ} m {A = T} G FΓ (f-letp {e = e} {t = t} Fe Ft) FT eq with infer k σ rs Γ m e in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (E , eu) with viewProd k σ E in veq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok (A , B) with check k σ (extRec (extRec rs false false) false false)
                             (ext (ext Γ affine A) affine (wk B)) m t (wk (wk T)) in teq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok (ub Vec.∷ ua Vec.∷ tus) with checkBound m affine ub in bb
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok tt with checkBound m affine ua in ba
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok tt with infer-sound k σ rs m false G FΓ Fe ieq
...           | inf FE De c with viewProd-Frag k σ (GoodSig.frag G) FE veq
...             | FA , FB with check-sound k σ (extRec (extRec rs false false) false false) m G
                                (FragCtx-ext (FragCtx-ext FΓ FA) (Frag-wk FB)) Ft (Frag-wk (Frag-wk FT)) teq
...               | chk Dt = chk (⇐-letp De (≈-trans c (viewProd-≈ k σ (GoodSig.frag G) FE veq)) Dt bb ba eq)
...               | chk′ _ = miss
...               | miss = miss
check-sound k σ rs {Γ = Γ} m {A = T} G FΓ (f-letp {e = e} {t = t} Fe Ft) FT eq
    | ok (E , eu) | ok (A , B) | ok (ub Vec.∷ ua Vec.∷ tus) | ok tt | ok tt | inf′ _ = miss
check-sound k σ rs {Γ = Γ} m {A = T} G FΓ (f-letp {e = e} {t = t} Fe Ft) FT eq
    | ok (E , eu) | ok (A , B) | ok (ub Vec.∷ ua Vec.∷ tus) | ok tt | ok tt | miss = miss

-- everything else: checkAgainst (the clauses match the term so that
-- the witness stays a variable and is passed on whole)
check-sound k σ rs m {e = var _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = typ} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = pi _ _ _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = app _ _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = nat} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = ze} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = su _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = unit} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = one} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = empty} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = dty _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = ctor _ _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = mData _ _ _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = mNat _ _ _ _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = mEmp _ _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = mUnit _ _ _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = idt _ _ _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = rwt _ _ _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = def _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = ann _ _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = prod _ _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = nu _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq
check-sound k σ rs m {e = ucons _} G FΓ Fe FA eq = checkAgainst-sound k σ rs m G FΓ Fe FA eq

-- A pair step is not a λ. Checking it at the step's Π fails, or the
-- stream guard fails first.
check-sound k σ rs {Γ = Γ} m {A = T} {u = uses} G FΓ (f-unf {s = seed} {f = pair h t} _ (f-pair _ _) fs-step) _ eq
  with infer k σ rs Γ m seed
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (S , seedU) with unfStep k σ T S
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (goal , fam) = stepBy fam eq
  where
    stepBy : (b : Bool)
      → ((if b then ok tt else whnf k σ T >>= λ T′ → guard "bare ν is not a stream" (lamForm T′)) >>
         check k σ (if b then setGuard rs else rs) Γ m (pair h t) (pi affine S (wk goal)) >>= λ fu →
         checkUnfold k σ m rs (pair h t) >>
         combine m seedU fu)
        ≡ ok uses
      → Chk {σ} Γ m (unf seed (pair h t)) T uses
    stepBy true eq′ with check k σ (setGuard rs) Γ m (pair h t) (pi affine S (wk goal))
    ... | fail _ = ⊥-elim (fail≢ok eq′)
    ... | ok _ = miss
    stepBy false eq′ with whnf k σ T
    ... | fail _ = ⊥-elim (fail≢ok eq′)
    ... | ok T′ with lamForm T′
    ... | false = ⊥-elim (fail≢ok eq′)
    ... | true with check k σ rs Γ m (pair h t) (pi affine S (wk goal))
    ... | fail _ = ⊥-elim (fail≢ok eq′)
    ... | ok _ = miss

-- unfold seed (λ _ → (h, t)). A stream is the λ (⇐-unf). A declared
-- family is the instantiated pair (⇐-unfR): uncons of the λ wraps, and
-- that wrap is not the family's tail.
check-sound k σ {n = n} rs {Γ = Γ} m {A = T} {u = uses} G FΓ
    (f-unf {s = seed} Fs (f-lam {q = q} {A = A} {t = pair h t} FA (f-pair Fh Ft)) fs-pair) FT eq
  with infer k σ rs Γ m seed in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (S , seedU) with conv k σ A S in aeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with unfStep k σ T S in seq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (goal , true) = unfTrue eq
  where
    unfTrue :
      ((if true then ok tt else whnf k σ T >>= λ T′ → guard "bare ν is not a stream" (lamForm T′)) >>
       (if eqQty q reuse then isCopy k σ S >>= guard notCopy else ok tt) >>
       check k σ (extRec (if true then setGuard rs else rs) false false) (ext Γ q S) m (pair h t) (wk goal) >>= λ bodyU →
       let (u₀ , us) = headTailU bodyU
       in checkBound m q u₀ >>
          checkUnfold k σ m rs (lam q A (pair h t)) >>
          combine m seedU us)
      ≡ ok uses
      → Chk {σ} Γ m (unf seed (lam q A (pair h t))) T uses
    unfTrue eq′ with (if eqQty q reuse then isCopy k σ S >>= guard notCopy else ok tt)
    ... | fail _ = ⊥-elim (fail≢ok eq′)
    ... | ok tt with check k σ (extRec (setGuard rs) false false) (ext Γ q S) m (pair h t) (wk goal) in beq
    ... | fail _ = ⊥-elim (fail≢ok eq′)
    ... | ok (u₀ Vec.∷ bus) with checkBound m q u₀ in bb
    ... | fail _ = ⊥-elim (fail≢ok eq′)
    ... | ok tt with checkUnfold k σ m rs (lam q A (pair h t))
    ... | fail _ = ⊥-elim (fail≢ok eq′)
    ... | ok tt = famYes (infer-sound k σ rs m false G FΓ Fs ieq)
      where
        famYes : Inf {σ} Γ m seed S seedU → Chk {σ} Γ m (unf seed (lam q A (pair h t))) T uses
        famYes (inf FS Ds ≈-refl) with >>=-ok seq
        ... | T′ , weq , steq with check-sound k σ (extRec (setGuard rs) false false) m G (FragCtx-ext FΓ FS)
                                  (f-pair Fh Ft) (Frag-wk (unfStepOf-Frag S T′ FS (whnf-Frag k σ (GoodSig.frag G) FT weq) steq)) beq
        ... | chk Dp = chk′ (⇐-unfR Ds (conv-sound k σ (GoodSig.frag G) FA FS aeq)
                                (whnf-≈ k σ (GoodSig.frag G) FT weq) steq refl Dp bb eq′)
        ... | chk′ _ = miss
        ... | miss = miss
        famYes (inf _ _ (≈-sym _)) = miss
        famYes (inf _ _ (≈-trans _ _)) = miss
        famYes (inf _ _ (≈-step _)) = miss
        famYes (inf′ _) = miss
        famYes miss = miss
... | ok (goal , false) = unfFalse eq
  where
    unfFalse :
      ((if false then ok tt else whnf k σ T >>= λ T′ → guard "bare ν is not a stream" (lamForm T′)) >>
       (if eqQty q reuse then isCopy k σ S >>= guard notCopy else ok tt) >>
       check k σ (extRec (if false then setGuard rs else rs) false false) (ext Γ q S) m (pair h t) (wk goal) >>= λ bodyU →
       let (u₀ , us) = headTailU bodyU
       in checkBound m q u₀ >>
          checkUnfold k σ m rs (lam q A (pair h t)) >>
          combine m seedU us)
      ≡ ok uses
      → Chk {σ} Γ m (unf seed (lam q A (pair h t))) T uses
    unfFalse eq′ = onWhnf eq′
      where
        onUnf : (T′ : Tm n) → whnf k σ T ≡ ok T′ → lamForm T′ ≡ true
          → unfStepOf S T′ ≡ ok (goal , false)
          → (u₀ : Use) (bus : UseVec n) → check k σ (extRec rs false false) (ext Γ q S) m (pair h t) (wk goal) ≡ ok (u₀ Vec.∷ bus)
          → checkBound m q u₀ ≡ ok tt
          → (checkUnfold k σ m rs (lam q A (pair h t)) >> combine m seedU bus) ≡ ok uses
          → Chk {σ} Γ m (unf seed (lam q A (pair h t))) T uses
        onUnf T′ weq leq steq u₀ bus beq bb eq′ with checkUnfold k σ m rs (lam q A (pair h t))
        ... | fail _ = ⊥-elim (fail≢ok eq′)
        ... | ok tt = streamYes (infer-sound k σ rs m false G FΓ Fs ieq)
          where
            Eh : Tm n
            Eh = proj₁ (lamForm-inv (whnf-Frag k σ (GoodSig.frag G) FT weq) leq)
            shp : T′ ≡ nu (prod (wk Eh) (var Fin.zero))
            shp = proj₂ (lamForm-inv (whnf-Frag k σ (GoodSig.frag G) FT weq) leq)
            streamYes : Inf {σ} Γ m seed S seedU → Chk {σ} Γ m (unf seed (lam q A (pair h t))) T uses
            streamYes (inf FS Ds ≈-refl) with check-sound k σ (extRec rs false false) m G (FragCtx-ext FΓ FS)
                                            (f-pair Fh Ft) (Frag-wk (unfStepOf-Frag S T′ FS (whnf-Frag k σ (GoodSig.frag G) FT weq) steq)) beq
            ... | chk Dp = chk (⇐-unf Ds (conv-sound k σ (GoodSig.frag G) FA FS aeq)
                                   (whnf-≈ k σ (GoodSig.frag G) FT weq) steq shp Dp bb eq′)
            ... | chk′ _ = miss
            ... | miss = miss
            streamYes (inf _ _ (≈-sym _)) = miss
            streamYes (inf _ _ (≈-trans _ _)) = miss
            streamYes (inf _ _ (≈-step _)) = miss
            streamYes (inf′ _) = miss
            streamYes miss = miss
        onBnd : (T′ : Tm n) → whnf k σ T ≡ ok T′ → lamForm T′ ≡ true
          → unfStepOf S T′ ≡ ok (goal , false)
          → (u₀ : Use) (bus : UseVec n) → check k σ (extRec rs false false) (ext Γ q S) m (pair h t) (wk goal) ≡ ok (u₀ Vec.∷ bus)
          → (checkBound m q u₀ >> checkUnfold k σ m rs (lam q A (pair h t)) >> combine m seedU bus) ≡ ok uses
          → Chk {σ} Γ m (unf seed (lam q A (pair h t))) T uses
        onBnd T′ weq leq steq u₀ bus beq eq′ with checkBound m q u₀ in bb
        ... | fail _ = ⊥-elim (fail≢ok eq′)
        ... | ok tt = onUnf T′ weq leq steq u₀ bus beq bb eq′
        onChk : (T′ : Tm n) → whnf k σ T ≡ ok T′ → lamForm T′ ≡ true
          → unfStepOf S T′ ≡ ok (goal , false)
          → (check k σ (extRec rs false false) (ext Γ q S) m (pair h t) (wk goal) >>= λ bodyU →
             let (u₀ , us) = headTailU bodyU in
             checkBound m q u₀ >> checkUnfold k σ m rs (lam q A (pair h t)) >> combine m seedU us)
            ≡ ok uses → Chk {σ} Γ m (unf seed (lam q A (pair h t))) T uses
        onChk T′ weq leq steq eq′ with check k σ (extRec rs false false) (ext Γ q S) m (pair h t) (wk goal) in beq
        ... | fail _ = ⊥-elim (fail≢ok eq′)
        ... | ok (u₀ Vec.∷ bus) = onBnd T′ weq leq steq u₀ bus beq eq′
        onLam : (T′ : Tm n) → whnf k σ T ≡ ok T′
          → (guard "bare ν is not a stream" (lamForm T′) >>
             (if eqQty q reuse then isCopy k σ S >>= guard notCopy else ok tt) >>
             check k σ (extRec rs false false) (ext Γ q S) m (pair h t) (wk goal) >>= λ bodyU →
             let (u₀ , us) = headTailU bodyU in
             checkBound m q u₀ >> checkUnfold k σ m rs (lam q A (pair h t)) >> combine m seedU us)
            ≡ ok uses → Chk {σ} Γ m (unf seed (lam q A (pair h t))) T uses
        onLam T′ weq eq′ with lamForm T′ in leq
        ... | false = ⊥-elim (fail≢ok eq′)
        ... | true with (if eqQty q reuse then isCopy k σ S >>= guard notCopy else ok tt)
        ... | fail _ = ⊥-elim (fail≢ok eq′)
        ... | ok tt =
          let T″ , weq2 , steq0 = >>=-ok seq
              steq = subst (λ z → unfStepOf S z ≡ ok (goal , false))
                           (sym (ok-inj (trans (sym weq) weq2))) steq0
          in onChk T′ weq leq steq eq′
        onWhnf : ((if false then ok tt else whnf k σ T >>= λ T′ → guard "bare ν is not a stream" (lamForm T′)) >>
                  (if eqQty q reuse then isCopy k σ S >>= guard notCopy else ok tt) >>
                  check k σ (extRec (if false then setGuard rs else rs) false false) (ext Γ q S) m (pair h t) (wk goal) >>= λ bodyU →
                  let (u₀ , us) = headTailU bodyU in
                  checkBound m q u₀ >> checkUnfold k σ m rs (lam q A (pair h t)) >> combine m seedU us)
                 ≡ ok uses → Chk {σ} Γ m (unf seed (lam q A (pair h t))) T uses
        onWhnf eq′ with whnf k σ T in weq
        ... | fail _ = ⊥-elim (fail≢ok eq′)
        ... | ok T′ = onLam T′ weq eq′

------------------------------------------------------------------------
-- checkLam: the λ's fragment witness is matched here, once the view of
-- the expected type is known.
------------------------------------------------------------------------

checkLam-sound k σ rs m G FΓ Fe FT (fail _) peq eq = inferConv-sound k σ rs m G FΓ Fe FT eq
checkLam-sound k σ rs {Γ = Γ} m {T = T} G FΓ (f-lam {q = q} {A = A} {t = t} FA Ft) FT (ok (q′ , A′ , B)) peq eq with eqQty q q′ in qeq
... | false = ⊥-elim (fail≢ok eq)
... | true with eqQty-sound q q′ qeq
...   | refl with checkTy k σ rs Γ A in teq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok tt with conv k σ A A′ in ceq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok tt with (if eqQty q reuse then isCopy k σ A′ >>= guard notCopy else ok tt) in req
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok tt with check k σ (lamRec rs) (ext Γ q A′) m t B in beq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok (u₀ Vec.∷ us) with checkBound m q u₀ in bq
...             | fail _ = ⊥-elim (fail≢ok eq)
...             | ok tt with ok-inj eq
...               | refl with viewPi-Frag k σ (GoodSig.frag G) FT peq | checkTy-sound k σ rs G FΓ FA teq
                       | check-sound k σ (lamRec rs) m G (FragCtx-ext FΓ (proj₁ (viewPi-Frag k σ (GoodSig.frag G) FT peq))) Ft (proj₂ (viewPi-Frag k σ (GoodSig.frag G) FT peq)) beq
...                 | FA′ , FB | ty WA | chk Dt = chk (⇐-lam WA (viewPi-≈ k σ (GoodSig.frag G) FT peq)
                      (conv-sound k σ (GoodSig.frag G) FA FA′ ceq) (copyOk-sound k σ q (GoodSig.frag G) FA′ req) Dt bq)
...                 | _ | ty _ | chk′ _ = miss
...                 | _ | ty _ | miss = miss
...                 | _ | ty-miss | _ = miss
checkLam-sound k σ rs m G FΓ f-var FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ f-typ FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-pi _ _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-app _ _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ f-nat FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ f-ze FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-su _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ f-unit FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ f-one FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ f-empty FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ f-dty FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ f-ctor FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-mData _ _ _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-mNat _ _ _ _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-mEmp _ _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-mUnit _ _ _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-idt _ _ _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ f-rfl FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-rwt _ _ _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ f-def FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-ann _ _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-prod _ _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-pair _ _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-letp _ _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-nu _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-unf _ _ _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)
checkLam-sound k σ rs m G FΓ (f-ucons _) FT (ok _) peq eq = ⊥-elim (fail≢ok eq)

------------------------------------------------------------------------
-- checkAgainst: a constructor spine against a data type, else infer.
------------------------------------------------------------------------

checkAgainst-sound k σ rs {Γ = Γ} m {e} {A} G FΓ Fe FA eq with viewData k σ A in veq | ctorSpine e
... | fail _ | _ = inferConv-sound k σ rs m G FΓ Fe FA eq
... | ok _ | nothing = inferConv-sound k σ rs m G FΓ Fe FA eq
... | ok (di , params , idxs) | just (di′ , ci , args) with di ≡ᵇ di′
...   | false = inferConv-sound k σ rs m G FΓ Fe FA eq
...   | true with viewData-sound k σ veq
...     | A′ , d , args′ , weq , leq , sp′ , lenA , peq , ieq′
      with checkCtorApp-sound k σ rs m G FΓ Fe
             (subst FragL (sym peq) (FragL-take (nparams d) (proj₂ (Frag-Spine sp′ (whnf-Frag k σ (GoodSig.frag G) FA weq)))))
             (Frag-appsFrom f-dty (FragL-++
               (subst FragL (sym peq) (FragL-take (nparams d) (proj₂ (Frag-Spine sp′ (whnf-Frag k σ (GoodSig.frag G) FA weq)))))
               (subst FragL (sym ieq′) (FragL-drop (nparams d) (proj₂ (Frag-Spine sp′ (whnf-Frag k σ (GoodSig.frag G) FA weq)))))))
             leq eq
...       | nothing = miss
...       | just (as , ci′ , c , T , R , sp , keq , ip , Ar , cR) =
  let pieq : params ++ idxs ≡ args′
      pieq = trans (cong₂ _++_ peq ieq′) (take++drop≡id (nparams d) args′)
      lps : length params ≡ nparams d
      lps = trans (cong length peq)
              (trans (length-take (nparams d) args′)
                (trans (cong (nparams d ⊓_) lenA) (m≤n⇒m⊓n≡m (m≤m+n (nparams d) (nidxs d)))))
      lidx : length idxs ≡ nidxs d
      lidx = trans (cong length ieq′)
               (trans (length-drop (nparams d) args′)
                 (trans (cong (_∸ nparams d) lenA) (m+n∸m≡n (nparams d) (nidxs d))))
  in chk (⇐-ctor sp
       (≈-trans (whnf-≈ k σ (GoodSig.frag G) FA weq)
         (≈-≡ (trans (Spine-≡ sp′) (cong (appsFrom (dty di)) (sym pieq)))))
       leq lps lidx keq ip Ar cR)

------------------------------------------------------------------------
-- inferCtorSpine / checkCtorApp: along the constructor telescope, from
-- the head of the spine.
------------------------------------------------------------------------

inferCtorSpine-sound k σ rs m {di} {ps} {d = d} G FΓ (f-ctor {i = di′} {j = ci}) Fps leq eq with di ≡ᵇ di′ in deq
... | false = ⊥-elim (fail≢ok eq)
... | true with ≡ᵇ-sound {di} {di′} deq
...   | refl rewrite leq with lookupCtor d ci in keq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok c with instParams k σ (closed (Ctor.ctype c)) ps in ipeq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok rest with ok-inj eq
...         | refl with instParams-sound k σ (GoodSig.frag G)
                          (Frag-closed (FragCtors-lookup (proj₂ (FragSig.datas (GoodSig.frag G) di d leq)) keq))
                          Fps (Tel-ren fromZero (GoodSig.tel G di d leq ci c keq)) ipeq
...           | ip , Frest , tlR = just ([] , ci , c , rest , sp-[] , keq , ip , args-[] , Frest , tlR)
inferCtorSpine-sound k σ rs {Γ = Γ} m {di} {ps} {d = d} G FΓ (f-app {f = f} {a = a} Ff Fa) Fps leq eq
  with inferCtorSpine k σ rs Γ m di ps f in feq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (tele , fu) with whnf k σ tele in weq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok ty′ with inferCtorSpine-sound k σ rs m G FΓ Ff Fps leq feq
...     | nothing = nothing
...     | just (as , ci , c , T , sp , keq , ip , Ar , Fty , tl) with Tel-whnf k σ tl weq
...       | refl with tl | Fty
...         | tel-end sp-[] _ | _ = ⊥-elim (fail≢ok eq)
...         | tel-end (sp-snoc _) _ | _ = ⊥-elim (fail≢ok eq)
...         | tel-pi {q = q} {A = A} {B = B} tl′ | f-pi FA FB with check k σ rs Γ (fieldMode q m) a A in aeq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok au with fieldUses k σ q m A au fu in ceq
...             | fail _ = ⊥-elim (fail≢ok eq)
...             | ok uses with ok-inj eq
...               | refl = fromArg (check-sound k σ rs (fieldMode q m) G FΓ Fa FA aeq)
  where
    fromArg : Chk {σ} Γ (fieldMode q m) a A au
      → Maybe (∃ λ as′ → ∃ λ ci′ → ∃ λ c′ → ∃ λ T′
        → Spine (ctor di ci′) as′ (app f a) × (lookupCtor d ci′ ≡ ok c′)
        × InstParams σ (closed (Ctor.ctype c′)) ps T′
        × (σ , Γ ⊢[ m ] T′ ▹ as′ ⇝ inst B a ⊣ uses) × Frag (inst B a) × Tel di (nparams d + nidxs d) (inst B a))
    fromArg (chk Da) = just (as ++ (a ∷ []) , ci , c , T , sp-snoc sp , keq , ip
                        , fieldUses-sound k σ (GoodSig.frag G) FA Ar ≈-refl Da ceq
                        , Frag-inst FB Fa , Tel-sub _ tl′)
    fromArg (chk′ _) = nothing
    fromArg miss = nothing
inferCtorSpine-sound k σ rs m G FΓ f-var Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ f-typ Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-pi _ _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-lam _ _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ f-nat Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ f-ze Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-su _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ f-unit Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ f-one Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ f-empty Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ f-dty Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-mData _ _ _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-mNat _ _ _ _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-mEmp _ _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-mUnit _ _ _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-idt _ _ _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ f-rfl Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-rwt _ _ _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ f-def Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-ann _ _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-prod _ _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-pair _ _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-letp _ _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-nu _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-unf _ _ _) Fps leq eq = ⊥-elim (fail≢ok eq)
inferCtorSpine-sound k σ rs m G FΓ (f-ucons _) Fps leq eq = ⊥-elim (fail≢ok eq)

checkCtorApp-sound k σ rs {Γ = Γ} m {di} {ps} {e} {X} G FΓ Fe Fps FX leq eq
  with inferCtorSpine k σ rs Γ m di ps e in seq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (R , u′) with whnf k σ R in weq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok R′ with inferCtorSpine-sound k σ rs m G FΓ Fe Fps leq seq
...     | nothing = nothing
...     | just (as , ci , c , T , sp , keq , ip , Ar , FR , tl) with Tel-whnf k σ tl weq
...       | refl with tl
...         | tel-pi _ = ⊥-elim (fail≢ok eq)
...         | tel-end sp-[] _ with conv k σ (dty di) X in ceq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok tt with ok-inj eq
...             | refl = just (as , ci , c , T , R , sp , keq , ip , Ar , conv-sound k σ (GoodSig.frag G) FR FX ceq)
checkCtorApp-sound k σ rs {Γ = Γ} m {di} {ps} {e} {X} G FΓ Fe Fps FX leq eq | ok (R , u′) | ok R′ | just (as , ci , c , T , sp , keq , ip , Ar , FR , tl) | refl | tel-end (sp-snoc {f = f} {a = a} _) _ with conv k σ (app f a) X in ceq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok tt with ok-inj eq
...             | refl = just (as , ci , c , T , R , sp , keq , ip , Ar , conv-sound k σ (GoodSig.frag G) FR FX ceq)

------------------------------------------------------------------------
-- checkBr: one branch along its constructor's telescope.
------------------------------------------------------------------------

checkBr-sound k σ rs {Γ = Γ} m di ci sm {np} {ty = brTy} {br} {q = q} {D = D} {P} {args} {u = u} G FΓ Fty Fbr FD FP Fargs tl npeq eq
  with whnf k σ brTy in weq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok ty′ with Tel-whnf k σ tl weq
...   | refl with tl | Fty
...     | tel-end {as = as} sp-[] len | _ rewrite npeq =
      brEnd (check-sound k σ rs m G FΓ Fbr
             (Frag-appsFrom (f-lam FD FP) (FragL-++ (FragL-drop np fl-[]) (fl-∷ (Frag-appsFrom f-ctor Fargs) fl-[]))) eq)
  where
    brEnd : Chk {σ} Γ m br (appsFrom (lam q D P) (drop np [] ++ (appsFrom (ctor di ci) args ∷ []))) u
      → Maybe (∃ λ X′ → BrTy σ di ci np brTy P args X′ × (σ , Γ ⊢[ m ] br ⇐ X′ ⊣ u))
    brEnd (chk Db) = just (_ , bt-end sp-[] ≈-refl , ⇐-≈ Db (motApp-β (drop np [])))
    brEnd (chk′ _) = nothing
    brEnd miss = nothing
...     | tel-end {as = as} (sp-snoc {a = a} sp) len | _
        rewrite Spine→unspine head-dty (sp-snoc {a = a} sp) | npeq =
      brEnd (check-sound k σ rs m G FΓ Fbr
             (Frag-appsFrom (f-lam FD FP)
               (FragL-++ (FragL-drop np (proj₂ (Frag-Spine (sp-snoc {a = a} sp) Fty))) (fl-∷ (Frag-appsFrom f-ctor Fargs) fl-[]))) eq)
  where
    brEnd : Chk {σ} Γ m br (appsFrom (lam q D P) (drop np as ++ (appsFrom (ctor di ci) args ∷ []))) u
      → Maybe (∃ λ X′ → BrTy σ di ci np brTy P args X′ × (σ , Γ ⊢[ m ] br ⇐ X′ ⊣ u))
    brEnd (chk Db) = just (_ , bt-end (sp-snoc sp) ≈-refl , ⇐-≈ Db (motApp-β (drop np as)))
    brEnd (chk′ _) = nothing
    brEnd miss = nothing
...     | tel-pi {q = q} {A = A} {B = B} tl′ | f-pi FA FB
        with checkBrPi-sound k σ rs m di ci sm G FΓ FA FB Fbr FD FP Fargs tl′ npeq eq
...       | just (X , bt , Dbr) = just (X , bt , Dbr)
...       | nothing = nothing

-- the branch must be a λ for the next constructor argument
checkBrPi-sound k σ rs {Γ = Γ} m di ci sm {np = np} {q = q} {A = A} {B = B} {q′ = mq} {D = D} {P = P} {args = args} G FΓ FA FB (f-lam {q = q′} {A = A′} {t = t} FA′ Ft) FD FP Fargs tl npeq eq
  with eqQty q q′ in qeq
... | false = ⊥-elim (fail≢ok eq)
... | true with eqQty-sound q q′ qeq
...   | refl with checkTy k σ rs Γ A′ in teq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok tt with conv k σ A′ A in ceq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok tt with (if eqQty q reuse then isCopy k σ A >>= guard notCopy else ok tt) in req
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok tt
          with checkBr k σ (brRec rs sm di A) (ext Γ q A) m di ci sm B t (lam mq (wk D) (ren (lift suc) P))
                 (renList suc args ++ (var zero ∷ [])) in beq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok (u₀ Vec.∷ us) with checkBound m q u₀ in bq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok tt with ok-inj eq
...             | refl = brLam (checkTy-sound k σ rs G FΓ FA′ teq)
                              (checkBr-sound k σ (brRec rs sm di A) m di ci sm G (FragCtx-ext FΓ FA) FB Ft (Frag-wk FD)
                                 (Frag-ren (lift suc) FP) (FragL-++ (FragL-ren suc Fargs) (fl-∷ f-var fl-[])) tl npeq beq)
  where
    brLam : TyR σ Γ A′
      → Maybe (∃ λ X → BrTy σ di ci np B (ren (lift suc) P) (renList suc args ++ (var zero ∷ [])) X
               × (σ , ext Γ q A ⊢[ m ] t ⇐ X ⊣ (u₀ Vec.∷ us)))
      → Maybe (∃ λ X → BrTy σ di ci np (pi q A B) P args X × (σ , Γ ⊢[ m ] lam q′ A′ t ⇐ X ⊣ us))
    brLam (ty WA) (just (X , bt , Dt)) =
      just (pi q A X
      , bt-pi ≈-refl (copyOk-sound k σ q (GoodSig.frag G) FA req) bt
      , ⇐-lam WA ≈-refl
          (conv-sound k σ (GoodSig.frag G) FA′ FA ceq)
          (copyOk-sound k σ q (GoodSig.frag G) FA req) Dt bq)
    brLam (ty _) nothing = nothing
    brLam ty-miss _ = nothing
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB f-var FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB f-typ FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-pi _ _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-app _ _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB f-nat FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB f-ze FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-su _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB f-unit FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB f-one FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB f-empty FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB f-dty FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB f-ctor FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-mData _ _ _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-mNat _ _ _ _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-mEmp _ _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-mUnit _ _ _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-idt _ _ _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB f-rfl FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-rwt _ _ _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB f-def FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-ann _ _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-prod _ _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-pair _ _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-letp _ _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-nu _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-unf _ _ _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)
checkBrPi-sound k σ rs m di ci sm G FΓ FA FB (f-ucons _) FD FP Fargs tl npeq eq = ⊥-elim (fail≢ok eq)

------------------------------------------------------------------------
-- checkBranches: one branch per constructor, in order.
------------------------------------------------------------------------

checkBranches-sound k σ rs m di sm G FΓ Fps Fis FD FP fl-[] co-[] npeq lps eq with ok-inj eq
... | refl = just brs-[]
checkBranches-sound k σ rs m di sm G FΓ Fps Fis FD FP (fl-∷ _ _) co-[] npeq lps eq = ⊥-elim (fail≢ok eq)
checkBranches-sound k σ {n} rs {Γ = Γ} m di sm {np} {params = params} {is} {D = D} {P} {ci} G FΓ Fps Fis FD FP fl-[] (co-∷ {c} {cs} Fc tlc rest) npeq lps eq
  with instParams k σ (closed (Ctor.ctype c)) params in ipeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tele with instParams-sound k σ (GoodSig.frag G) (Frag-closed Fc) Fps (Tel-ren fromZero tlc) ipeq
...   | ip , Fty , tl rewrite npeq with clashes k σ np is tele in cleq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok true = ⊥-elim (fail≢ok eq)
...     | ok false = ⊥-elim (fail≢ok eq)
checkBranches-sound k σ {n} rs {Γ = Γ} m di sm {np} {params = params} {is} {q = q} {D = D} {P} {ci} G FΓ Fps Fis FD FP (fl-∷ {t = b} {ts = bs} Fb Fbs′) (co-∷ {c} {cs} Fc tlc rest) npeq lps eq
  with instParams k σ (closed (Ctor.ctype c)) params in ipeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tele with instParams-sound k σ (GoodSig.frag G) (Frag-closed Fc) Fps (Tel-ren fromZero tlc) ipeq
...   | ip , Fty , tl rewrite npeq with clashes k σ np is tele in cleq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok true = skipRest (checkBranches-sound k σ rs m di sm G FΓ Fps Fis FD FP Fbs′ rest npeq lps eq)
  where
    skipRest : ∀ {v} → Maybe (σ , Γ ⊢[ m ] bs brs⟨ di , params , is , P , suc ci ⟩ cs ⊣ v)
      → Maybe (σ , Γ ⊢[ m ] (b ∷ bs) brs⟨ di , params , is , P , ci ⟩ (c ∷ cs) ⊣ v)
    skipRest (just rest) = just (brs-skip ip
      (subst (λ k′ → Clash σ k′ is tele) (sym lps)
        (subst (λ xs → Clash σ np xs tele) (renList-id is)
          (clashes-sound k σ (λ x → x) (GoodSig.frag G) Fis Fty tl cleq)))
      rest)
    skipRest nothing = nothing
...     | ok false with checkBr k σ rs Γ m di ci sm tele b (lam q D P) [] in beq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok u with checkBranches k σ rs Γ m di sm params is (lam q D P) (suc ci) cs bs in ceq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok v with ok-inj eq
...           | refl = consRest (checkBr-sound k σ rs m di ci sm G FΓ Fty Fb FD FP fl-[] tl npeq beq)
                               (checkBranches-sound k σ rs m di sm G FΓ Fps Fis FD FP Fbs′ rest npeq lps ceq)
  where
    consRest : ∀ {u v} → Maybe (∃ λ X → BrTy σ di ci np tele P [] X × (σ , Γ ⊢[ m ] b ⇐ X ⊣ u))
      → Maybe (σ , Γ ⊢[ m ] bs brs⟨ di , params , is , P , suc ci ⟩ cs ⊣ v)
      → Maybe (σ , Γ ⊢[ m ] (b ∷ bs) brs⟨ di , params , is , P , ci ⟩ (c ∷ cs) ⊣ combineAlt m u v)
    consRest (just (X , bt , Db)) (just rest) =
      just (brs-∷ ip (subst (λ k′ → BrTy σ di ci k′ tele P [] X) (sym lps) bt) Db rest)
    consRest (just _) nothing = nothing
    consRest nothing _ = nothing

------------------------------------------------------------------------
-- checkMotive
------------------------------------------------------------------------

checkMotive-sound k σ rs {Γ = Γ} {di} {params = params} {P} G FΓ Fps FP fi-[] eq =
  mot0 (checkTy-sound k σ (extRec rs false false) G (FragCtx-ext FΓ (Frag-appsFrom f-dty Fps)) FP eq)
  where
    mot0 : TyR σ (ext Γ affine (appsFrom (dty di) params)) P → Maybe (MotiveOk σ Γ di params [] P)
    mot0 (ty WA) = just WA
    mot0 ty-miss = nothing
checkMotive-sound k σ rs {Γ = Γ} {di} {params = params} {P} G FΓ Fps FP (fi-∷ {q = q} {T = T} {ixs = rest} FT Frest) eq
  with check k σ (extRec rs false false) (ext Γ q (closed T)) spec P
         (motiveTail di (renList suc params ++ (var zero ∷ [])) rest) in ceq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok u = motIx (check-sound k σ (extRec rs false false) spec G (FragCtx-ext FΓ (Frag-closed FT)) FP
                  (Frag-motiveTail di (FragL-++ (FragL-ren suc Fps) (fl-∷ f-var fl-[])) Frest) ceq)
  where
    motIx : Chk {σ} (ext Γ q (closed T)) spec P
              (motiveTail di (renList suc params ++ (var zero ∷ [])) rest) u
      → Maybe (MotiveOk σ Γ di params ((q , T) ∷ rest) P)
    motIx (chk Dp) = just (u , Dp)
    motIx (chk′ _) = nothing
    motIx miss = nothing

------------------------------------------------------------------------
-- checkTy: Type, a kind, or a small type (infer then conv with Type).
------------------------------------------------------------------------

checkTy-el k σ rs {A = A} G FΓ FA ieq ceq with infer-sound k σ rs spec false G FΓ FA ieq
... | inf FT D c = ty (type-el D (≈-trans c (conv-sound k σ (GoodSig.frag G) FT f-typ ceq)))
... | inf′ _ = ty-miss
... | miss = ty-miss

checkTy-sound k σ rs G FΓ f-typ eq = ty type-Type
checkTy-sound k σ rs {Γ = Γ} G FΓ (f-pi {q = q} {A = A} {B = B} FA FB) eq with checkTy k σ rs Γ A in aeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt = piDom (checkTy-sound k σ rs G FΓ FA aeq)
  where
    piDom : TyR σ Γ A → TyR σ Γ (pi q A B)
    piDom (ty WA) with checkTy-sound k σ (extRec rs false false) G (FragCtx-ext FΓ FA) FB eq
    ... | ty WB = ty (type-pi WA WB)
    ... | ty-miss = ty-miss
    piDom ty-miss = ty-miss
-- infer reduces at once
checkTy-sound k σ rs {Γ = Γ} G FΓ (f-var {x = x}) eq = ty (type-el ⇒-var-spec (conv-sound k σ (GoodSig.frag G) (FΓ x) f-typ eq))
checkTy-sound k σ rs G FΓ f-nat eq = ty (type-el ⇒-nat (conv-sound k σ (GoodSig.frag G) f-typ f-typ eq))
checkTy-sound k σ rs G FΓ f-unit eq = ty (type-el ⇒-unit (conv-sound k σ (GoodSig.frag G) f-typ f-typ eq))
checkTy-sound k σ rs G FΓ f-empty eq = ty (type-el ⇒-empty (conv-sound k σ (GoodSig.frag G) f-typ f-typ eq))
checkTy-sound k σ rs G FΓ f-ze eq = ty (type-el ⇒-ze (conv-sound k σ (GoodSig.frag G) f-nat f-typ eq))
checkTy-sound k σ rs G FΓ f-one eq = ty (type-el ⇒-one (conv-sound k σ (GoodSig.frag G) f-unit f-typ eq))
checkTy-sound k σ rs G FΓ f-ctor eq = ⊥-elim (fail≢ok eq)
checkTy-sound k σ rs G FΓ f-rfl eq = ⊥-elim (fail≢ok eq)
-- infer is stuck on a subterm. The clauses match the term, not the
-- fragment witness, which is passed on whole.
checkTy-sound k σ rs {Γ = Γ} {A = A@(lam _ _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(app _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(su _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(dty _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(mData _ _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(mNat _ _ _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(mEmp _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(mUnit _ _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(idt _ _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(rwt _ _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(def _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(ann _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(prod _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(pair _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(letp _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(nu _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(unf _ _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq
checkTy-sound k σ rs {Γ = Γ} {A = A@(ucons _)} G FΓ Fe eq with infer k σ rs Γ spec A in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (T , _) = checkTy-el k σ rs G FΓ Fe ieq eq

------------------------------------------------------------------------
-- The corollaries for a definition and for a signature.
------------------------------------------------------------------------

-- The empty context is in the fragment.
FragCtx-[] : FragCtx Vec.[]
FragCtx-[] ()

tag-ok : ∀ {A : Set} {s} {r : Result A} {x} → tag s r ≡ ok x → r ≡ ok x
tag-ok {r = ok _}   eq = eq
tag-ok {r = fail _} ()

-- What ⊢ says of a definition Check accepts: its type is well-formed
-- and its body checks against it in the declared mode, with some uses.
DefOk : Sig → Def → Set
DefOk σ d = TyR σ Vec.[] (Def.dtype d)
          × ∃ λ u → Chk {σ} Vec.[] (Def.dmode d) (Def.dbody d) (Def.dtype d) u

checkDef-sound : ∀ k σ i {d} → GoodSig σ → lookupDef σ i ≡ ok d
  → checkDef k σ i ≡ ok tt → DefOk σ d
-- checkBody tries the argument positions; whichever succeeds, the body
-- was checked with some recursion state
retryBody-sound : ∀ k σ i d msg ps {u} → retryBody k σ i d msg ps ≡ ok u
  → ∃ λ rs → check k σ rs Vec.[] (Def.dmode d) (Def.dbody d) (Def.dtype d) ≡ ok u
retryBody-sound k σ i d msg [] eq = ⊥-elim (fail≢ok eq)
retryBody-sound k σ i d msg (p ∷ ps) eq with checkAt k σ i d p in peq
... | ok u with ok-inj eq
...   | refl = defRec σ i p , peq
retryBody-sound k σ i d msg (p ∷ ps) eq | fail _ = retryBody-sound k σ i d msg ps eq

checkBodyAt-sound : ∀ k σ i d ps {u} → checkBodyAt k σ i d ps ≡ ok u
  → ∃ λ rs → check k σ rs Vec.[] (Def.dmode d) (Def.dbody d) (Def.dtype d) ≡ ok u
-- An empty assignment list checks with every member at index 0, except
-- a mutual block that has candidates and no assignment that works: that
-- path is fail, so it never arrives here with ok.
checkBodyAt-sound k σ i d [] eq with sharedArgs σ (component σ i)
... | [] = defRec σ i (zeroPos σ i) , eq
... | p ∷ _ with recMode (Def.dmode d) ∧ mutual? (component σ i)
... | false = defRec σ i (zeroPos σ i) , eq
... | true with checkAt k σ i d p
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok _   = ⊥-elim (fail≢ok eq)
checkBodyAt-sound k σ i d (p ∷ ps) eq with checkAt k σ i d p in peq
... | ok u with ok-inj eq
...   | refl = defRec σ i p , peq
checkBodyAt-sound k σ i d (p ∷ ps) eq | fail msg = retryBody-sound k σ i d msg ps eq

checkBody-sound : ∀ k σ i d {u} → checkBody k σ i d ≡ ok u
  → ∃ λ rs → check k σ rs Vec.[] (Def.dmode d) (Def.dbody d) (Def.dtype d) ≡ ok u
checkBody-sound k σ i d eq = checkBodyAt-sound k σ i d (pickPos k σ i d) eq

checkDef-sound k σ i {d} G leq eq with lookupDef σ i in leq′
... | fail _ = ⊥-elim (fail≢ok leq)
... | ok d′ with ok-inj leq
...   | refl with >>-ok₃ eq
...     | (_ , teq) , (_ , beq) , _ , _ with FragSig.defs (GoodSig.frag G) i d′ leq′
...       | FT , FB with checkBody-sound k σ i d′ (tag-ok beq)
...         | rs , ceq =
  checkTy-sound k σ emptyRec G FragCtx-[] FT
    (ok-tt (proj₂ (proj₁ (>>-ok {r = checkTy k σ emptyRec Vec.[] (Def.dtype d′)} (tag-ok teq)))))
  , _ , check-sound k σ rs (Def.dmode d′) G FragCtx-[] FB FT ceq

checkDefs-sound : ∀ k σ j ds → checkDefs k σ j ds ≡ ok tt
  → ∀ i d → lookupList ds i ≡ ok d → checkDef k σ (j + i) ≡ ok tt
checkDefs-sound k σ j [] eq i d ()
checkDefs-sound k σ j (_ ∷ ds) eq zero d leq rewrite +-identityʳ j =
  ok-tt (proj₂ (proj₁ (>>-ok {r = checkDef k σ j} eq)))
checkDefs-sound k σ j (_ ∷ ds) eq (suc i) d leq rewrite +-suc j i =
  checkDefs-sound k σ (suc j) ds (proj₂ (>>-ok {r = checkDef k σ j} eq)) i d leq

-- The theorem for a whole signature: if Check accepts σ, every
-- definition of σ is derivable in ⊢.
checkSig-sound : ∀ k σ → GoodSig σ → checkSig k σ ≡ ok tt
  → ∀ i d → lookupDef σ i ≡ ok d → DefOk σ d
checkSig-sound k σ G eq i d leq =
  checkDef-sound k σ i G leq
    (checkDefs-sound k σ 0 (Sig.defs σ) (proj₂ (>>-ok {r = checkDatas k σ} eq)) i d leq)

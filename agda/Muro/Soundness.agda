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
open import Data.Fin.Base using (Fin; zero; suc)
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
open import Muro.SubstLemmas using (strengthen₂-sound; renList-id)
open import Muro.Reduction
open import Muro.Convert
open import Muro.Data hiding (subst₂)
open import Muro.Check
  using (whnf; conv; apps; viewPi; viewId; viewProd; viewData; isData; instParams; isRunType;
         infer; check; checkTy; checkAgainst; checkCtorApp; inferCtorSpine; inferConv;
         checkLam; checkBr; checkBrPi; checkBranches; checkMotive; firstMotLam; nparamsOf;
         clashes; RecSt; extRec; lamRec; scrutOk; checkRec; selfApplied;
         infer′; floatIdOk;
         isDType; checkDef; checkBody; checkBodyAt; retryBody; checkAt; argPositions; pickPos; checkDefs; checkDatas; checkSig; emptyRec; defRec)
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
------------------------------------------------------------------------

-- hd: the term is inferred as the head of an application spine (Check
-- then skips the descent tests, which have no bearing on ⊢); infer is
-- infer′ … false.
infer-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m hd {e A u} → GoodSig σ → FragCtx Γ → Frag e
  → infer′ k σ rs Γ e m hd ≡ ok (A , u)
  → Frag A × ∃ λ A′ → (σ , Γ ⊢[ m ] e ⇒ A′ ⊣ u) × (σ ⊢[ spec ] A′ ≈ A)
check-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m {e A u} → GoodSig σ → FragCtx Γ → Frag e → Frag A
  → check k σ rs Γ m e A ≡ ok u → σ , Γ ⊢[ m ] e ⇐ A ⊣ u
checkTy-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} {A} → GoodSig σ → FragCtx Γ → Frag A
  → checkTy k σ rs Γ A ≡ ok tt → σ , Γ ⊢ A wf
checkTy-el : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} {A T u} → GoodSig σ → FragCtx Γ → Frag A
  → infer k σ rs Γ spec A ≡ ok (T , u) → conv k σ T typ ≡ ok tt → σ , Γ ⊢ A wf
checkLam-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m {e T u} → GoodSig σ → FragCtx Γ → Frag e → Frag T
  → (r : Result (Qty × Tm n × Tm (suc n))) → viewPi k σ T ≡ r
  → checkLam k σ rs Γ m e T r ≡ ok u → σ , Γ ⊢[ m ] e ⇐ T ⊣ u
checkAgainst-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m {e A u} → GoodSig σ → FragCtx Γ → Frag e → Frag A
  → checkAgainst k σ rs Γ m e A (viewData k σ A) (ctorSpine e) ≡ ok u
  → σ , Γ ⊢[ m ] e ⇐ A ⊣ u
inferConv-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m {e A u} → GoodSig σ → FragCtx Γ → Frag e → Frag A
  → inferConv k σ rs Γ m e A ≡ ok u
  → σ , Γ ⊢[ m ] e ⇐ A ⊣ u
-- a constructor spine from its head: the head is a constructor of di,
-- and the arguments so far follow the constructor's telescope
inferCtorSpine-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m {di ps e R u d} → GoodSig σ → FragCtx Γ
  → Frag e → FragL ps → lookupData σ di ≡ ok d
  → inferCtorSpine k σ rs Γ m di ps e ≡ ok (R , u)
  → ∃ λ as → ∃ λ ci → ∃ λ c → ∃ λ T
    → Spine (ctor di ci) as e × (lookupCtor d ci ≡ ok c)
    × InstParams σ (closed (Ctor.ctype c)) ps T
    × (σ , Γ ⊢[ m ] T ▹ as ⇝ R ⊣ u) × Frag R × Tel di (nparams d + nidxs d) R
checkCtorApp-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m {di ps e X u d} → GoodSig σ → FragCtx Γ
  → Frag e → FragL ps → Frag X → lookupData σ di ≡ ok d
  → checkCtorApp k σ rs Γ m di ps e X ≡ ok u
  → ∃ λ as → ∃ λ ci → ∃ λ c → ∃ λ T → ∃ λ R
    → Spine (ctor di ci) as e × (lookupCtor d ci ≡ ok c)
    × InstParams σ (closed (Ctor.ctype c)) ps T
    × (σ , Γ ⊢[ m ] T ▹ as ⇝ R ⊣ u) × (σ ⊢[ spec ] R ≈ X)
checkBr-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m di ci sm {np ar ty br q D P args u} → GoodSig σ → FragCtx Γ
  → Frag ty → Frag br → Frag D → Frag P → FragL args → Tel di ar ty → nparamsOf σ di ≡ np
  → checkBr k σ rs Γ m di ci sm ty br (lam q D P) args ≡ ok u
  → ∃ λ X → BrTy σ di ci np ty P args X × (σ , Γ ⊢[ m ] br ⇐ X ⊣ u)
checkBrPi-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m di ci sm {np ar q A B br q′ D P args u} → GoodSig σ → FragCtx Γ
  → Frag A → Frag B → Frag br → Frag D → Frag P → FragL args → Tel di ar B → nparamsOf σ di ≡ np
  → checkBrPi k σ rs Γ m di ci sm q A B br (lam q′ D P) args ≡ ok u
  → ∃ λ X → BrTy σ di ci np (pi q A B) P args X × (σ , Γ ⊢[ m ] br ⇐ X ⊣ u)
checkBranches-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} m di sm {np ar params is q D P ci cs bs u} → GoodSig σ → FragCtx Γ
  → FragL params → FragL is → Frag D → Frag P → FragL bs → CtorsOk di ar cs → nparamsOf σ di ≡ np → length params ≡ np
  → checkBranches k σ rs Γ m di sm params is (lam q D P) ci cs bs ≡ ok u
  → σ , Γ ⊢[ m ] bs brs⟨ di , params , is , P , ci ⟩ cs ⊣ u
-- the motive: over the scrutinee when the data type has no indices,
-- otherwise over the indices and the scrutinee (Judgement.MotiveOk)
checkMotive-sound : ∀ k σ {n} (rs : RecSt n) {Γ : Ctx n} {di ixs params P} → GoodSig σ → FragCtx Γ
  → FragL params → Frag P → FragIdxs ixs
  → checkMotive k σ rs Γ di ixs params P ≡ ok tt
  → MotiveOk σ Γ di params ixs P

------------------------------------------------------------------------
-- inferConv: infer then convert (Check's default for ⇐).
------------------------------------------------------------------------

inferConv-sound k σ rs {Γ = Γ} m {e} {A} G FΓ Fe FA eq with infer k σ rs Γ m e in ieq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (B , u′) with conv k σ B A in ceq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with ok-inj eq
...     | refl with infer-sound k σ rs m false G FΓ Fe ieq
...       | FB , A′ , D , c = ⇐-conv D (≈-trans c (conv-sound k σ (GoodSig.frag G) FB FA ceq))

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
...     | refl = FΓ x , _ , var-run qeq (λ ()) , ≈-refl
infer-sound k σ rs {Γ = Γ} run hd G FΓ (f-var {x = x}) eq | reuse with isRunType k σ (typOf Γ x)
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok false = ⊥-elim (fail≢ok eq)
...   | ok true with ok-inj eq
...     | refl = FΓ x , _ , var-run qeq (λ ()) , ≈-refl
infer-sound k σ rs {Γ = Γ} evid hd G FΓ (f-var {x = x}) eq with qtyOf Γ x in qeq
... | erased = ⊥-elim (fail≢ok eq)
... | affine with ok-inj eq
...   | refl = FΓ x , _ , var-evid qeq (λ ()) , ≈-refl
infer-sound k σ rs {Γ = Γ} evid hd G FΓ (f-var {x = x}) eq | reuse with ok-inj eq
...   | refl = FΓ x , _ , var-evid qeq (λ ()) , ≈-refl
infer-sound k σ rs spec hd G FΓ (f-var {x = x}) refl = FΓ x , _ , ⇒-var-spec , ≈-refl

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
...     | refl = f-typ , _
      , ⇒-pi (checkTy-sound k σ rs G FΓ FA teq)
             (check-sound k σ (extRec rs false false) spec G (FragCtx-ext FΓ FA) FB f-typ beq)
      , ≈-refl

-- λ
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-lam {q = q} {A = A} {t = t} FA Ft) eq with checkTy k σ rs Γ A in teq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with (if eqQty q reuse then isData k σ A >>= guard "+ requires a Data type" else ok tt) in req
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with infer k σ (lamRec rs) (ext Γ q A) m t in ieq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok (B , u₀ Vec.∷ us) with checkBound m q u₀ in beq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok tt with ok-inj eq
...         | refl with infer-sound k σ (lamRec rs) m false G (FragCtx-ext FΓ FA) Ft ieq
...           | FB , B′ , D , c = f-pi FA FB , _
            , ⇒-lam (checkTy-sound k σ rs G FΓ FA teq) (reuseOk-sound k σ q (GoodSig.frag G) FA req) D beq
            , ≈-pi ≈-refl c

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
...             | Fft , F′ , Df , c with viewPi-Frag k σ (GoodSig.frag G) Fft peq
...               | FA , FB = Frag-inst FB Fa , _
                , ⇒-app-aff Df (≈-trans c (viewPi-≈ k σ (GoodSig.frag G) Fft peq))
                    (check-sound k σ rs m G FΓ Fa FA aeq) ueq
                , ≈-refl
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq | ok (ft , fu) | ok (reuse , A , B) with isData k σ A in deq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok false = ⊥-elim (fail≢ok eq)
...     | ok true with check k σ rs Γ m a A in aeq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok au with appUses σ m f fu au in ueq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok uses with checkRec m hd rs (app f a)
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok _ with ok-inj eq
...             | refl with infer-sound k σ rs m true G FΓ Ff feq
...               | Fft , F′ , Df , c with viewPi-Frag k σ (GoodSig.frag G) Fft peq
...                 | FA , FB = Frag-inst FB Fa , _
                  , ⇒-app-reuse Df (≈-trans c (viewPi-≈ k σ (GoodSig.frag G) Fft peq))
                      (isData-sound k σ (GoodSig.frag G) FA deq)
                      (check-sound k σ rs m G FΓ Fa FA aeq) ueq
                  , ≈-refl
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq | ok (ft , fu) | ok (erased , A , B) with check k σ rs Γ spec a A in aeq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok au with eqMode m spec in meq
...       | true with eqMode-sound m spec meq
...         | refl with ok-inj eq
...           | refl with infer-sound k σ rs spec true G FΓ Ff feq
...             | Fft , F′ , Df , c with spec-⇒-uses Df
...               | refl with viewPi-Frag k σ (GoodSig.frag G) Fft peq
...                 | FA , FB = Frag-inst FB Fa , _
                  , ⇒-app-era Df (≈-trans c (viewPi-≈ k σ (GoodSig.frag G) Fft peq))
                      (check-sound k σ rs spec G FΓ Fa FA aeq)
                  , ≈-refl
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-app {f = f} {a = a} Ff Fa) eq | ok (ft , fu) | ok (erased , A , B) | ok au | false
  with checkRec m hd rs (app f a)
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok _ with ok-inj eq
...           | refl with infer-sound k σ rs m true G FΓ Ff feq
...             | Fft , F′ , Df , c with viewPi-Frag k σ (GoodSig.frag G) Fft peq
...               | FA , FB = Frag-inst FB Fa , _
                , ⇒-app-era Df (≈-trans c (viewPi-≈ k σ (GoodSig.frag G) Fft peq))
                    (check-sound k σ rs spec G FΓ Fa FA aeq)
                , ≈-refl

-- Nat
infer-sound k σ rs run hd G FΓ f-nat eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs evid hd G FΓ f-nat eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs spec hd G FΓ f-nat refl = f-typ , _ , ⇒-nat , ≈-refl
infer-sound k σ rs m hd G FΓ f-ze refl = f-nat , _ , ⇒-ze , ≈-refl
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-su {t = t} Ft) eq with check k σ rs Γ m t nat in ceq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok u′ with ok-inj eq
...   | refl = f-nat , _ , ⇒-su (check-sound k σ rs m G FΓ Ft f-nat ceq) , ≈-refl

-- Unit, Empty
infer-sound k σ rs run hd G FΓ f-unit eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs evid hd G FΓ f-unit eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs spec hd G FΓ f-unit refl = f-typ , _ , ⇒-unit , ≈-refl
infer-sound k σ rs m hd G FΓ f-one refl = f-unit , _ , ⇒-one , ≈-refl
infer-sound k σ rs run hd G FΓ f-empty eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs evid hd G FΓ f-empty eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs spec hd G FΓ f-empty refl = f-typ , _ , ⇒-empty , ≈-refl

-- data former, constructor
infer-sound k σ rs run hd G FΓ f-dty eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs evid hd G FΓ f-dty eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs spec hd G FΓ (f-dty {i = i}) eq with lookupData σ i in leq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok d with ok-inj eq
...   | refl = Frag-dtyType (DataDecl.pqtys d) (proj₁ (FragSig.datas (GoodSig.frag G) i d leq)) , _
            , ⇒-dty leq , ≈-refl
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
...       | Fet , E′ , De , c
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
  in Frag-appsFrom (f-lam FD FP) (FragL-++ Fidxs (fl-∷ Fe fl-[])) , _
   , ⇒-mData De
       (≈-trans c (≈-trans (whnf-≈ k σ fs Fet weq)
         (≈-≡ (trans (Spine-≡ sp) (cong (appsFrom (dty di)) (sym pieq))))))
       leq lps lidx
       (checkMotive-sound k σ rs G FΓ Fparams FP (proj₁ (FragSig.datas fs di d leq)) meq)
       (checkBranches-sound k σ rs m di (scrutOk rs e) {np = nparams d} G FΓ Fparams Fidxs FD FP Fbs
         (ctorsOk {i = di} {d = d} G leq) (nparamsOf-ok {σ} {di} {d} leq) lps beq)
       ceq
   , ≈-sym (motApp-β idxs)

-- match on Nat
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-mNat {e = e} {P = P} {z = z} {s = s} Fe FP Fz Fs) eq with check k σ rs Γ m e nat in eeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok eu with checkTy k σ (extRec rs false false) (ext Γ affine nat) P in peq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with check k σ rs Γ m z (inst P ze) in zeq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok zu with check k σ (extRec rs (scrutOk rs e) (scrutOk rs e)) (ext Γ affine nat) m s (motSuc P) in seq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok (u₀ Vec.∷ sus) with checkBound m affine u₀ in beq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok tt with combine m eu (combineAlt m zu sus) in ceq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok uses with ok-inj eq
...             | refl = Frag-inst FP Fe , _
              , ⇒-mNat (check-sound k σ rs m G FΓ Fe f-nat eeq)
                  (checkTy-sound k σ (extRec rs false false) G (FragCtx-ext FΓ f-nat) FP peq)
                  (check-sound k σ rs m G FΓ Fz (Frag-inst FP f-ze) zeq)
                  (check-sound k σ (extRec rs (scrutOk rs e) (scrutOk rs e)) m G (FragCtx-ext FΓ f-nat) Fs (Frag-motSuc FP) seq)
                  beq ceq
              , ≈-refl

-- match on Empty
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-mEmp {e = e} {P = P} Fe FP) eq with check k σ rs Γ m e empty in eeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok eu with checkTy k σ (extRec rs false false) (ext Γ affine empty) P in peq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with ok-inj eq
...     | refl = Frag-inst FP Fe , _
      , ⇒-mEmp (check-sound k σ rs m G FΓ Fe f-empty eeq)
          (checkTy-sound k σ (extRec rs false false) G (FragCtx-ext FΓ f-empty) FP peq)
      , ≈-refl

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
...         | refl = Frag-inst FP Fe , _
          , ⇒-mUnit (check-sound k σ rs m G FΓ Fe f-unit eeq)
              (checkTy-sound k σ (extRec rs false false) G (FragCtx-ext FΓ f-unit) FP peq)
              (check-sound k σ rs m G FΓ Ft (Frag-inst FP f-one) teq)
              ceq
          , ≈-refl

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
...         | refl = f-typ , _
          , ⇒-idt (checkTy-sound k σ rs G FΓ FA teq)
              (check-sound k σ rs spec G FΓ Fa FA aeq)
              (check-sound k σ rs spec G FΓ Fb FA beq)
          , ≈-refl
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
...         | refl with infer-sound k σ rs (rwtMode m) false G FΓ Fe ieq
...           | Fet , E′ , De , c with viewId-Frag k σ (GoodSig.frag G) Fet veq
...             | FA , Fl , Fr = Frag-inst FP Fl , _
              , ⇒-rwt De (≈-trans c (viewId-≈ k σ (GoodSig.frag G) Fet veq))
                  (checkTy-sound k σ (extRec rs false false) G (FragCtx-ext FΓ FA) FP peq)
                  (check-sound k σ rs m G FΓ Ft (Frag-inst FP Fr) teq)
              , ≈-refl

-- definitions: the self-application test has no bearing on ⊢
infer-sound k σ {n} rs m hd G FΓ (f-def {i = i}) eq with selfApplied m hd rs i
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with lookupDef σ i in leq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok d with allowedDef (Def.dmode d) m in aeq
...     | false = ⊥-elim (fail≢ok eq)
...     | true with eqMode m run
...       | false with ok-inj eq
...         | refl = Frag-closed (proj₁ (FragSig.defs (GoodSig.frag G) i d leq)) , _
                   , ⇒-def leq aeq , ≈-refl
infer-sound k σ {n} rs m hd G FΓ (f-def {i = i}) eq | ok tt | ok d | true | true with isRunType k σ (closed {n} (Def.dtype d))
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok false = ⊥-elim (fail≢ok eq)
...         | ok true with ok-inj eq
...           | refl = Frag-closed (proj₁ (FragSig.defs (GoodSig.frag G) i d leq)) , _
                     , ⇒-def leq aeq , ≈-refl

-- annotation
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-ann {e = e} {A = A} Fe FA) eq with checkTy k σ rs Γ A in teq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt with check k σ rs Γ m e A in ceq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok u′ with ok-inj eq
...     | refl = FA , _
      , ⇒-ann (checkTy-sound k σ rs G FΓ FA teq) (check-sound k σ rs m G FΓ Fe FA ceq)
      , ≈-refl

-- products: A × B is spec-only; a pair infers a product of the
-- components' types
infer-sound k σ rs run hd G FΓ (f-prod _ _) eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs evid hd G FΓ (f-prod _ _) eq = ⊥-elim (fail≢ok eq)
infer-sound k σ rs {Γ = Γ} spec hd G FΓ (f-prod {A = A} {B = B} FA FB) eq with check k σ rs Γ spec A typ in aeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok _ with check k σ rs Γ spec B typ in beq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok _ with ok-inj eq
...     | refl = f-typ , _
      , ⇒-prod (check-sound k σ rs spec G FΓ FA f-typ aeq) (check-sound k σ rs spec G FΓ FB f-typ beq)
      , ≈-refl
infer-sound k σ rs {Γ = Γ} m hd G FΓ (f-pair {a = a} {b = b} Fa Fb) eq with infer k σ rs Γ m a in aeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (A , au) with infer k σ rs Γ m b in beq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok (B , bu) with combine m au bu in ceq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok uses with ok-inj eq
...       | refl with infer-sound k σ rs m false G FΓ Fa aeq | infer-sound k σ rs m false G FΓ Fb beq
...         | FA , A′ , Da , cA | FB , B′ , Db , cB =
  f-prod FA FB , _ , ⇒-pair Da Db ceq , ≈-prod cA cB

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
...                 | FE , E′ , De , c with viewProd-Frag k σ (GoodSig.frag G) FE veq
...                   | FA , FB with infer-sound k σ (extRec (extRec rs false false) false false) m false G
                                      (FragCtx-ext (FragCtx-ext FΓ FA) (Frag-wk FB)) Ft teq
...                     | FT , T′ , Dt , cT with strengthen₂-sound T seq
...                       | refl =
  Frag-unren suc C (Frag-unren suc (wk C) FT) , _
  , ⇒-letp De (≈-trans c (viewProd-≈ k σ (GoodSig.frag G) FE veq)) Dt cT bb ba ceq
  , ≈-refl

------------------------------------------------------------------------
-- check
------------------------------------------------------------------------

-- λ against a type: viewPi, or infer and convert (checkLam-sound is
-- split on the view so that the fragment witness is matched in a clause
-- head)
check-sound k σ rs m {e = lam q A t} {A = T} G FΓ Fe FT eq = checkLam-sound k σ rs m G FΓ Fe FT (viewPi k σ T) refl eq

-- refl against a type
check-sound k σ rs {Γ = Γ} m {A = T} G FΓ f-rfl FT eq with viewId k σ T in veq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (A , a , b) with floatIdOk k σ A
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok tt with conv k σ a b in ceq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok tt with ok-inj eq
...       | refl with viewId-Frag k σ (GoodSig.frag G) FT veq
...         | FA , Fa , Fb = ⇐-refl (viewId-≈ k σ (GoodSig.frag G) FT veq) (conv-sound k σ (GoodSig.frag G) Fa Fb ceq)

-- pair against a type: viewProd, then the components
check-sound k σ rs {Γ = Γ} m {A = T} G FΓ (f-pair {a = a} {b = b} Fa Fb) FT eq with viewProd k σ T in veq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (A , B) with check k σ rs Γ m a A in aeq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok au with check k σ rs Γ m b B in beq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok bu with viewProd-Frag k σ (GoodSig.frag G) FT veq
...       | FA , FB =
  ⇐-pair (viewProd-≈ k σ (GoodSig.frag G) FT veq)
    (check-sound k σ rs m G FΓ Fa FA aeq) (check-sound k σ rs m G FΓ Fb FB beq) eq

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
...           | FE , E′ , De , c with viewProd-Frag k σ (GoodSig.frag G) FE veq
...             | FA , FB =
  ⇐-letp De (≈-trans c (viewProd-≈ k σ (GoodSig.frag G) FE veq))
    (check-sound k σ (extRec (extRec rs false false) false false) m G
      (FragCtx-ext (FragCtx-ext FΓ FA) (Frag-wk FB)) Ft (Frag-wk (Frag-wk FT)) teq)
    bb ba eq

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
...       | ok tt with (if eqQty q reuse then isData k σ A′ >>= guard "+ requires a Data type" else ok tt) in req
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok tt with check k σ (lamRec rs) (ext Γ q A′) m t B in beq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok (u₀ Vec.∷ us) with checkBound m q u₀ in bq
...             | fail _ = ⊥-elim (fail≢ok eq)
...             | ok tt with ok-inj eq
...               | refl with viewPi-Frag k σ (GoodSig.frag G) FT peq
...                 | FA′ , FB =
  ⇐-lam (checkTy-sound k σ rs G FΓ FA teq) (viewPi-≈ k σ (GoodSig.frag G) FT peq)
    (conv-sound k σ (GoodSig.frag G) FA FA′ ceq) (reuseOk-sound k σ q (GoodSig.frag G) FA′ req)
    (check-sound k σ (lamRec rs) m G (FragCtx-ext FΓ FA′) Ft FB beq) bq
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
...       | as , ci′ , c , T , R , sp , keq , ip , Ar , cR =
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
  in ⇐-ctor sp
       (≈-trans (whnf-≈ k σ (GoodSig.frag G) FA weq)
         (≈-≡ (trans (Spine-≡ sp′) (cong (appsFrom (dty di)) (sym pieq)))))
       leq lps lidx keq ip Ar cR

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
...           | ip , Frest , tlR = [] , ci , c , rest , sp-[] , keq , ip , args-[] , Frest , tlR
inferCtorSpine-sound k σ rs {Γ = Γ} m {di} {ps} G FΓ (f-app {f = f} {a = a} Ff Fa) Fps leq eq
  with inferCtorSpine k σ rs Γ m di ps f in feq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (ty , fu) with whnf k σ ty in weq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok ty′ with inferCtorSpine-sound k σ rs m G FΓ Ff Fps leq feq
...     | as , ci , c , T , sp , keq , ip , Ar , Fty , tl with Tel-whnf k σ tl weq
...       | refl with tl | Fty
...         | tel-end sp-[] _ | _ = ⊥-elim (fail≢ok eq)
...         | tel-end (sp-snoc _) _ | _ = ⊥-elim (fail≢ok eq)
...         | tel-pi {q = q} {A = A} {B = B} tl′ | f-pi FA FB with check k σ rs Γ (fieldMode q m) a A in aeq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok au with combineArg q m au fu in ceq
...             | fail _ = ⊥-elim (fail≢ok eq)
...             | ok uses with ok-inj eq
...               | refl = as ++ (a ∷ []) , ci , c , T , sp-snoc sp , keq , ip
                        , args-snoc Ar ≈-refl (check-sound k σ rs (fieldMode q m) G FΓ Fa FA aeq) ceq
                        , Frag-inst FB Fa , Tel-sub _ tl′
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

checkCtorApp-sound k σ rs {Γ = Γ} m {di} {ps} {e} {X} G FΓ Fe Fps FX leq eq
  with inferCtorSpine k σ rs Γ m di ps e in seq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (R , u′) with whnf k σ R in weq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok R′ with inferCtorSpine-sound k σ rs m G FΓ Fe Fps leq seq
...     | as , ci , c , T , sp , keq , ip , Ar , FR , tl with Tel-whnf k σ tl weq
...       | refl with tl
...         | tel-pi _ = ⊥-elim (fail≢ok eq)
...         | tel-end sp-[] _ with conv k σ (dty di) X in ceq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok tt with ok-inj eq
...             | refl = as , ci , c , T , R , sp , keq , ip , Ar , conv-sound k σ (GoodSig.frag G) FR FX ceq
checkCtorApp-sound k σ rs {Γ = Γ} m {di} {ps} {e} {X} G FΓ Fe Fps FX leq eq | ok (R , u′) | ok R′ | as , ci , c , T , sp , keq , ip , Ar , FR , tl | refl | tel-end (sp-snoc {f = f} {a = a} _) _ with conv k σ (app f a) X in ceq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok tt with ok-inj eq
...             | refl = as , ci , c , T , R , sp , keq , ip , Ar , conv-sound k σ (GoodSig.frag G) FR FX ceq

------------------------------------------------------------------------
-- checkBr: one branch along its constructor's telescope.
------------------------------------------------------------------------

checkBr-sound k σ rs {Γ = Γ} m di ci sm {np} {ty = ty} {br} {D = D} {P} {args} G FΓ Fty Fbr FD FP Fargs tl npeq eq
  with whnf k σ ty in weq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok ty′ with Tel-whnf k σ tl weq
...   | refl with tl | Fty
...     | tel-end {as = as} sp-[] len | _ rewrite npeq =
  _ , bt-end sp-[] ≈-refl
    , ⇐-≈ (check-sound k σ rs m G FΓ Fbr
             (Frag-appsFrom (f-lam FD FP) (FragL-++ (FragL-drop np fl-[]) (fl-∷ (Frag-appsFrom f-ctor Fargs) fl-[]))) eq)
          (motApp-β (drop np []))
...     | tel-end {as = as} (sp-snoc {a = a} sp) len | _
        rewrite Spine→unspine head-dty (sp-snoc {a = a} sp) | npeq =
  _ , bt-end (sp-snoc sp) ≈-refl
    , ⇐-≈ (check-sound k σ rs m G FΓ Fbr
             (Frag-appsFrom (f-lam FD FP)
               (FragL-++ (FragL-drop np (proj₂ (Frag-Spine (sp-snoc {a = a} sp) Fty))) (fl-∷ (Frag-appsFrom f-ctor Fargs) fl-[]))) eq)
          (motApp-β (drop np as))
...     | tel-pi {q = q} {A = A} {B = B} tl′ | f-pi FA FB
        with checkBrPi-sound k σ rs m di ci sm G FΓ FA FB Fbr FD FP Fargs tl′ npeq eq
...       | X , bt , Dbr = X , bt , Dbr

-- the branch must be a λ for the next constructor argument
checkBrPi-sound k σ rs {Γ = Γ} m di ci sm {q = q} {A = A} {B = B} {q′ = mq} {D = D} {P = P} {args = args} G FΓ FA FB (f-lam {q = q′} {A = A′} {t = t} FA′ Ft) FD FP Fargs tl npeq eq
  with eqQty q q′ in qeq
... | false = ⊥-elim (fail≢ok eq)
... | true with eqQty-sound q q′ qeq
...   | refl with checkTy k σ rs Γ A′ in teq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok tt with conv k σ A′ A in ceq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok tt with (if eqQty q reuse then isData k σ A >>= guard "+ requires a Data type" else ok tt) in req
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok tt
          with checkBr k σ (brRec rs sm di A) (ext Γ q A) m di ci sm B t (lam mq (wk D) (ren (lift suc) P))
                 (renList suc args ++ (var zero ∷ [])) in beq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok (u₀ Vec.∷ us) with checkBound m q u₀ in bq
...           | fail _ = ⊥-elim (fail≢ok eq)
...           | ok tt with ok-inj eq
...             | refl
              with checkBr-sound k σ (brRec rs sm di A) m di ci sm G (FragCtx-ext FΓ FA) FB Ft (Frag-wk FD)
                     (Frag-ren (lift suc) FP) (FragL-++ (FragL-ren suc Fargs) (fl-∷ f-var fl-[])) tl npeq beq
...               | X , bt , Dt =
  pi q A X
  , bt-pi ≈-refl (reuseOk-sound k σ q (GoodSig.frag G) FA req) bt
  , ⇐-lam (checkTy-sound k σ rs G FΓ FA′ teq) ≈-refl (conv-sound k σ (GoodSig.frag G) FA′ FA ceq)
      (reuseOk-sound k σ q (GoodSig.frag G) FA req) Dt bq
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

------------------------------------------------------------------------
-- checkBranches: one branch per constructor, in order.
------------------------------------------------------------------------

checkBranches-sound k σ rs m di sm G FΓ Fps Fis FD FP fl-[] co-[] npeq lps eq with ok-inj eq
... | refl = brs-[]
checkBranches-sound k σ rs m di sm G FΓ Fps Fis FD FP (fl-∷ _ _) co-[] npeq lps eq = ⊥-elim (fail≢ok eq)
checkBranches-sound k σ {n} rs {Γ = Γ} m di sm {np} {params = params} {is} {D = D} {P} {ci} G FΓ Fps Fis FD FP fl-[] (co-∷ {c} {cs} Fc tlc rest) npeq lps eq
  with instParams k σ (closed (Ctor.ctype c)) params in ipeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok ty with instParams-sound k σ (GoodSig.frag G) (Frag-closed Fc) Fps (Tel-ren fromZero tlc) ipeq
...   | ip , Fty , tl rewrite npeq with clashes k σ np is ty in cleq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok true = ⊥-elim (fail≢ok eq)
...     | ok false = ⊥-elim (fail≢ok eq)
checkBranches-sound k σ {n} rs {Γ = Γ} m di sm {np} {params = params} {is} {q = q} {D = D} {P} {ci} G FΓ Fps Fis FD FP (fl-∷ {t = b} {ts = bs} Fb Fbs′) (co-∷ {c} {cs} Fc tlc rest) npeq lps eq
  with instParams k σ (closed (Ctor.ctype c)) params in ipeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok ty with instParams-sound k σ (GoodSig.frag G) (Frag-closed Fc) Fps (Tel-ren fromZero tlc) ipeq
...   | ip , Fty , tl rewrite npeq with clashes k σ np is ty in cleq
...     | fail _ = ⊥-elim (fail≢ok eq)
...     | ok true =
  -- the constructor cannot produce the scrutinee's indices: skipped
  brs-skip ip
    (subst (λ k′ → Clash σ k′ is ty) (sym lps)
      (subst (λ xs → Clash σ np xs ty) (renList-id is)
        (clashes-sound k σ (λ x → x) (GoodSig.frag G) Fis Fty tl cleq)))
    (checkBranches-sound k σ rs m di sm G FΓ Fps Fis FD FP Fbs′ rest npeq lps eq)
...     | ok false with checkBr k σ rs Γ m di ci sm ty b (lam q D P) [] in beq
...       | fail _ = ⊥-elim (fail≢ok eq)
...       | ok u with checkBranches k σ rs Γ m di sm params is (lam q D P) (suc ci) cs bs in ceq
...         | fail _ = ⊥-elim (fail≢ok eq)
...         | ok v with ok-inj eq
...           | refl with checkBr-sound k σ rs m di ci sm G FΓ Fty Fb FD FP fl-[] tl npeq beq
...             | X , bt , Db =
  brs-∷ ip (subst (λ k′ → BrTy σ di ci k′ ty P [] X) (sym lps) bt) Db
    (checkBranches-sound k σ rs m di sm G FΓ Fps Fis FD FP Fbs′ rest npeq lps ceq)

------------------------------------------------------------------------
-- checkMotive
------------------------------------------------------------------------

checkMotive-sound k σ rs {Γ = Γ} {di} {params = params} {P} G FΓ Fps FP fi-[] eq =
  checkTy-sound k σ (extRec rs false false) G (FragCtx-ext FΓ (Frag-appsFrom f-dty Fps)) FP eq
checkMotive-sound k σ rs {Γ = Γ} {di} {params = params} {P} G FΓ Fps FP (fi-∷ {q = q} {T = T} {ixs = rest} FT Frest) eq
  with check k σ (extRec rs false false) (ext Γ q (closed T)) spec P
         (motiveTail di (renList suc params ++ (var zero ∷ [])) rest) in ceq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok u = u , check-sound k σ (extRec rs false false) spec G (FragCtx-ext FΓ (Frag-closed FT)) FP
                  (Frag-motiveTail di (FragL-++ (FragL-ren suc Fps) (fl-∷ f-var fl-[])) Frest) ceq

------------------------------------------------------------------------
-- checkTy: Type, a kind, or a small type (infer then conv with Type).
------------------------------------------------------------------------

checkTy-el k σ rs G FΓ FA ieq ceq with infer-sound k σ rs spec false G FΓ FA ieq
... | FT , T′ , D , c = type-el D (≈-trans c (conv-sound k σ (GoodSig.frag G) FT f-typ ceq))

checkTy-sound k σ rs G FΓ f-typ eq = type-Type
checkTy-sound k σ rs {Γ = Γ} G FΓ (f-pi {q = q} {A = A} {B = B} FA FB) eq with checkTy k σ rs Γ A in aeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok tt = type-pi (checkTy-sound k σ rs G FΓ FA aeq)
                      (checkTy-sound k σ (extRec rs false false) G (FragCtx-ext FΓ FA) FB eq)
-- infer reduces at once
checkTy-sound k σ rs {Γ = Γ} G FΓ (f-var {x = x}) eq = type-el ⇒-var-spec (conv-sound k σ (GoodSig.frag G) (FΓ x) f-typ eq)
checkTy-sound k σ rs G FΓ f-nat eq = type-el ⇒-nat (conv-sound k σ (GoodSig.frag G) f-typ f-typ eq)
checkTy-sound k σ rs G FΓ f-unit eq = type-el ⇒-unit (conv-sound k σ (GoodSig.frag G) f-typ f-typ eq)
checkTy-sound k σ rs G FΓ f-empty eq = type-el ⇒-empty (conv-sound k σ (GoodSig.frag G) f-typ f-typ eq)
checkTy-sound k σ rs G FΓ f-ze eq = type-el ⇒-ze (conv-sound k σ (GoodSig.frag G) f-nat f-typ eq)
checkTy-sound k σ rs G FΓ f-one eq = type-el ⇒-one (conv-sound k σ (GoodSig.frag G) f-unit f-typ eq)
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
DefOk σ d = (σ , Vec.[] ⊢ Def.dtype d wf)
          × ∃ λ u → σ , Vec.[] ⊢[ Def.dmode d ] Def.dbody d ⇐ Def.dtype d ⊣ u

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
checkBodyAt-sound k σ i d [] eq = defRec σ i 0 , eq
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
  checkTy-sound k σ emptyRec G FragCtx-[] FT (ok-tt (tag-ok teq))
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

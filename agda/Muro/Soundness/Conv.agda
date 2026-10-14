{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Soundness of the executable checker, part 1: weak-head normalisation
-- and conversion (Muro.Check.whnf, synEq, conv) with respect to ⟶* and
-- ≈, on the ⊢ fragment (Muro.Frag).
--
--   whnf-sound   whnf k σ t ≡ ok u → t ⟶* u in spec, and u is in the
--                fragment (running out of fuel is a failure, never a
--                result);
--   synEq-sound  synEq u v ≡ true → u ≡ v;
--   conv-sound   conv k σ u v ≡ ok tt → σ ⊢[ spec ] u ≈ v.
--
-- Fuel is universally quantified: it only decides how far the run goes.
------------------------------------------------------------------------

module Muro.Soundness.Conv where

open import Data.Bool.Base using (Bool; true; false; _∧_; not; if_then_else_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Env
open import Muro.Tag
open import Muro.Spine
open import Muro.Frag
open import Muro.Reduction
open import Muro.Convert hiding (≈-map; ≈-ucons)
open import Muro.Check
  using (whnf; uconsWhnf; dataWhnf; synEq; synEqD; synEqList; conv; convStuck; convWhnf; convN; convND;
         convArgs; eqFin; ctorHead)

------------------------------------------------------------------------
-- Results.
------------------------------------------------------------------------

fail≢ok : ∀ {A : Set} {e} {x : A} → fail e ≡ ok x → ⊥
fail≢ok ()

------------------------------------------------------------------------
-- ⟶* under evaluation contexts.
------------------------------------------------------------------------

app-f* : ∀ {σ m n} {f f′ a : Tm n} → σ ⊢[ m ] f ⟶* f′ → σ ⊢[ m ] app f a ⟶* app f′ a
app-f* ⟶*-refl = ⟶*-refl
app-f* (⟶*-step s r) = ⟶*-step (app-f s) (app-f* r)

mNat-e* : ∀ {σ m n} {e e′ : Tm n} {P z s} → σ ⊢[ m ] e ⟶* e′
  → σ ⊢[ m ] mNat e P z s ⟶* mNat e′ P z s
mNat-e* ⟶*-refl = ⟶*-refl
mNat-e* (⟶*-step s r) = ⟶*-step (mNat-e s) (mNat-e* r)

mUnit-e* : ∀ {σ m n} {e e′ : Tm n} {P u} → σ ⊢[ m ] e ⟶* e′
  → σ ⊢[ m ] mUnit e P u ⟶* mUnit e′ P u
mUnit-e* ⟶*-refl = ⟶*-refl
mUnit-e* (⟶*-step s r) = ⟶*-step (mUnit-e s) (mUnit-e* r)

mEmp-e* : ∀ {σ m n} {e e′ : Tm n} {P} → σ ⊢[ m ] e ⟶* e′
  → σ ⊢[ m ] mEmp e P ⟶* mEmp e′ P
mEmp-e* ⟶*-refl = ⟶*-refl
mEmp-e* (⟶*-step s r) = ⟶*-step (mEmp-e s) (mEmp-e* r)

mData-e* : ∀ {σ m n} {e e′ : Tm n} {P bs} → σ ⊢[ m ] e ⟶* e′
  → σ ⊢[ m ] mData e P bs ⟶* mData e′ P bs
mData-e* ⟶*-refl = ⟶*-refl
mData-e* (⟶*-step s r) = ⟶*-step (mData-e s) (mData-e* r)

letp-e* : ∀ {σ m n} {e e′ : Tm n} {t} → σ ⊢[ m ] e ⟶* e′
  → σ ⊢[ m ] letp e t ⟶* letp e′ t
letp-e* ⟶*-refl = ⟶*-refl
letp-e* (⟶*-step s r) = ⟶*-step (letp-e s) (letp-e* r)

ucons-e* : ∀ {σ m n} {e e′ : Tm n} → σ ⊢[ m ] e ⟶* e′
  → σ ⊢[ m ] ucons e ⟶* ucons e′
ucons-e* ⟶*-refl = ⟶*-refl
ucons-e* (⟶*-step s r) = ⟶*-step (ucons-e s) (ucons-e* r)

------------------------------------------------------------------------
-- whnf. On a fragment term over a fragment signature, whnf k σ t is
-- reached from t by ⟶ in spec (all defs unfold) and is again in the
-- fragment. Fuel only decides how far the run goes.
------------------------------------------------------------------------

allowedDef-spec : ∀ d → allowedDef d spec ≡ true
allowedDef-spec run = refl
allowedDef-spec evid = refl
allowedDef-spec spec = refl

-- uconsWhnf is the three uncons steps, on the nose, and stuck otherwise.
ucons-step : ∀ k σ {n} {e u : Tm n} → Frag e → uconsWhnf k σ e ≡ ok u
  → (σ ⊢[ spec ] ucons e ⟶* u) × Frag u
ucons-step k σ (f-unf {f = pair h t} _ (f-pair Fh Ft) fs-step) refl =
  ⟶*-step ι-ucons-r ⟶*-refl , f-pair Fh Ft
ucons-step k σ (f-unf {s = s} {f = lam q A (pair h t)} Fs (f-lam FA (f-pair Fh Ft)) fs-pair) refl =
  ⟶*-step ι-ucons-p ⟶*-refl
  , f-pair (Frag-inst Fh Fs)
      (f-unf (Frag-inst Ft Fs) (f-lam FA (f-pair Fh Ft)) fs-pair)
ucons-step k σ f-var refl = ⟶*-refl , f-ucons f-var
ucons-step k σ f-typ refl = ⟶*-refl , f-ucons f-typ
ucons-step k σ (f-pi FA FB) refl = ⟶*-refl , f-ucons (f-pi FA FB)
ucons-step k σ (f-lam FA Ft) refl = ⟶*-refl , f-ucons (f-lam FA Ft)
ucons-step k σ (f-app Ff Fa) refl = ⟶*-refl , f-ucons (f-app Ff Fa)
ucons-step k σ f-nat refl = ⟶*-refl , f-ucons f-nat
ucons-step k σ f-ze refl = ⟶*-refl , f-ucons f-ze
ucons-step k σ (f-su Ft) refl = ⟶*-refl , f-ucons (f-su Ft)
ucons-step k σ f-unit refl = ⟶*-refl , f-ucons f-unit
ucons-step k σ f-one refl = ⟶*-refl , f-ucons f-one
ucons-step k σ f-empty refl = ⟶*-refl , f-ucons f-empty
ucons-step k σ f-dty refl = ⟶*-refl , f-ucons f-dty
ucons-step k σ f-ctor refl = ⟶*-refl , f-ucons f-ctor
ucons-step k σ (f-mData Fe FP Fb) refl = ⟶*-refl , f-ucons (f-mData Fe FP Fb)
ucons-step k σ (f-mNat Fe FP Fz Fs) refl = ⟶*-refl , f-ucons (f-mNat Fe FP Fz Fs)
ucons-step k σ (f-mEmp Fe FP) refl = ⟶*-refl , f-ucons (f-mEmp Fe FP)
ucons-step k σ (f-mUnit Fe FP Fu) refl = ⟶*-refl , f-ucons (f-mUnit Fe FP Fu)
ucons-step k σ (f-idt FA Fa Fb) refl = ⟶*-refl , f-ucons (f-idt FA Fa Fb)
ucons-step k σ f-rfl refl = ⟶*-refl , f-ucons f-rfl
ucons-step k σ (f-rwt Fe FP Ft) refl = ⟶*-refl , f-ucons (f-rwt Fe FP Ft)
ucons-step k σ f-def refl = ⟶*-refl , f-ucons f-def
ucons-step k σ (f-ann Fe FA) refl = ⟶*-refl , f-ucons (f-ann Fe FA)
ucons-step k σ (f-prod FA FB) refl = ⟶*-refl , f-ucons (f-prod FA FB)
ucons-step k σ (f-pair Fa Fb) refl = ⟶*-refl , f-ucons (f-pair Fa Fb)
ucons-step k σ (f-letp Fe Ft) refl = ⟶*-refl , f-ucons (f-letp Fe Ft)
ucons-step k σ (f-nu F) refl = ⟶*-refl , f-ucons (f-nu F)
ucons-step k σ (f-ucons Fe) refl = ⟶*-refl , f-ucons (f-ucons Fe)

WhnfOk : Sig → ∀ {n} → Tm n → Tm n → Set
WhnfOk σ t u = (σ ⊢[ spec ] t ⟶* u) × Frag u

whnf-sound : ∀ k σ {n} {t u : Tm n} → FragSig σ → Frag t → whnf k σ t ≡ ok u → WhnfOk σ t u
whnf-sound zero σ fs Ft ()
-- app: β if the head normalises to a λ
whnf-sound (suc k) σ fs (f-app {f} {a} Ff Fa) eq with whnf k σ f in feq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (lam _ _ t) with whnf-sound k σ fs Ff feq
...   | r , f-lam _ Ft with whnf-sound k σ fs (Frag-inst Ft Fa) eq
...     | r′ , F′ = ⟶*-trans (app-f* r) (⟶*-step β r′) , F′
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (var _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok typ with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (pi _ _ _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (app _ _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok nat with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok ze with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (su _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok unit with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok one with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok empty with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (dty _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (ctor _ _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (mData _ _ _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (mNat _ _ _ _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (mEmp _ _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (mUnit _ _ _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (idt _ _ _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok rfl with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (rwt _ _ _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (def _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (ann _ _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (letp _ _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (prod _ _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (pair _ _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (nu _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (unf _ _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (ucons _) with whnf-sound k σ fs Ff feq | ok-inj eq
...   | r , F | refl = app-f* r , f-app F Fa
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok i64 with whnf-sound k σ fs Ff feq
...   | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok f32ty with whnf-sound k σ fs Ff feq
...   | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (tensor _ _) with whnf-sound k σ fs Ff feq
...   | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (addi _ _) with whnf-sound k σ fs Ff feq
...   | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (muli _ _) with whnf-sound k σ fs Ff feq
...   | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (addt _ _) with whnf-sound k σ fs Ff feq
...   | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (toi64 _) with whnf-sound k σ fs Ff feq
...   | _ , ()
whnf-sound (suc k) σ fs (f-app Ff Fa) eq | ok (packi _ _) with whnf-sound k σ fs Ff feq
...   | _ , ()
-- mNat: ι on ze / su
whnf-sound (suc k) σ fs (f-mNat {e} {P} {z} {s} Fe FP Fz Fs) eq with whnf k σ e in eeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok ze with whnf-sound k σ fs Fe eeq
...   | r , _ with whnf-sound k σ fs Fz eq
...     | r′ , F′ = ⟶*-trans (mNat-e* r) (⟶*-step ιz r′) , F′
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (su u) with whnf-sound k σ fs Fe eeq
...   | r , f-su Fu with whnf-sound k σ fs (Frag-inst Fs Fu) eq
...     | r′ , F′ = ⟶*-trans (mNat-e* r) (⟶*-step ιs r′) , F′
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (var _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok typ with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (pi _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (lam _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (app _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok nat with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok unit with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok one with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok empty with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (dty _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (ctor _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (mData _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (mNat _ _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (mEmp _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (mUnit _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (idt _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok rfl with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (rwt _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (def _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (ann _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (letp _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (prod _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (pair _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (nu _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (unf _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (ucons _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mNat-e* r , f-mNat F FP Fz Fs
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok i64 with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok f32ty with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (tensor _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (addi _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (muli _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (addt _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (toi64 _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-mNat Fe FP Fz Fs) eq | ok (packi _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
-- mUnit: ι on one
whnf-sound (suc k) σ fs (f-mUnit {e} {P} {u} Fe FP Fu) eq with whnf k σ e in eeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok one with whnf-sound k σ fs Fe eeq
...   | r , _ with whnf-sound k σ fs Fu eq
...     | r′ , F′ = ⟶*-trans (mUnit-e* r) (⟶*-step ιtt r′) , F′
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (var _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok typ with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (pi _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (lam _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (app _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok nat with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok ze with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (su _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok unit with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok empty with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (dty _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (ctor _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (mData _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (mNat _ _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (mEmp _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (mUnit _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (idt _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok rfl with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (rwt _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (def _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (ann _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (letp _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (prod _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (pair _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (nu _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (unf _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (ucons _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mUnit-e* r , f-mUnit F FP Fu
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok i64 with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok f32ty with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (tensor _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (addi _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (muli _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (addt _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (toi64 _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-mUnit Fe FP Fu) eq | ok (packi _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
-- mEmp: the scrutinee only
whnf-sound (suc k) σ fs (f-mEmp {e} Fe FP) eq with whnf k σ e in eeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok e′ with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = mEmp-e* r , f-mEmp F FP
-- mData: ι-data when the scrutinee normalises to a constructor spine
-- with a branch
whnf-sound (suc k) σ fs (f-mData {e} {P} {bs} Fe FP Fbs) eq with whnf k σ e in eeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok e′ with whnf-sound k σ fs Fe eeq
...   | r , Fe′ with ctorSpine e′ in ceq
...     | nothing with ok-inj eq
...       | refl = mData-e* r , f-mData Fe′ FP Fbs
whnf-sound (suc k) σ fs (f-mData {bs = bs} Fe FP Fbs) eq | ok e′ | r , Fe′ | just (i , ci , args) with lookupList bs ci in leq
...       | fail _ with ok-inj eq
...         | refl = mData-e* r , f-mData Fe′ FP Fbs
whnf-sound (suc k) σ fs (f-mData {bs = bs} Fe FP Fbs) eq | ok e′ | r , Fe′ | just (i , ci , args) | ok b with ctorSpine-just ceq
...         | sp with whnf-sound k σ fs (Frag-appsFrom (FragL-lookup Fbs leq) (proj₂ (Frag-Spine sp Fe′))) eq
...           | r′ , F′ = ⟶*-trans (mData-e* r) (⟶*-step (ι-data sp leq) r′) , F′
-- letp: ι when the scrutinee normalises to a pair
whnf-sound (suc k) σ fs (f-letp {e} {t} Fe Ft) eq with whnf k σ e in eeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok (pair a b) with whnf-sound k σ fs Fe eeq
...   | r , f-pair Fa Fb with whnf-sound k σ fs (Frag-inst₂ Ft Fa Fb) eq
...     | r′ , F′ = ⟶*-trans (letp-e* r) (⟶*-step ι-letp r′) , F′
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (var _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (typ) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (pi _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (lam _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (app _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (nat) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (ze) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (su _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (unit) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (one) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (empty) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (dty _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (ctor _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (mData _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (mNat _ _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (mEmp _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (mUnit _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (idt _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (rfl) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (rwt _ _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (def _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (ann _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (prod _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (letp _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (nu _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (unf _ _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (ucons _) with whnf-sound k σ fs Fe eeq | ok-inj eq
...   | r , F | refl = letp-e* r , f-letp F Ft
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (i64) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (f32ty) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (tensor _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (addi _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (muli _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (addt _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (toi64 _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
whnf-sound (suc k) σ fs (f-letp Fe Ft) eq | ok (packi _ _) with whnf-sound k σ fs Fe eeq
...   | _ , ()
-- δ: every def unfolds in spec
whnf-sound (suc k) σ fs (f-def {i}) eq with lookupDef σ i in leq
... | fail _ with ok-inj eq
...   | refl = ⟶*-refl , f-def
whnf-sound (suc k) σ fs (f-def {i}) eq | ok d with whnf-sound k σ fs (Frag-closed (proj₂ (FragSig.defs fs i d leq))) eq
...   | r , F = ⟶*-step (δ leq (allowedDef-spec _)) r , F
-- annotations are dropped
whnf-sound (suc k) σ fs (f-ann Fe FA) eq with whnf-sound k σ fs Fe eq
... | r , F = ⟶*-step ann-e r , F
-- everything else is already weak-head normal for whnf
whnf-sound (suc k) σ fs f-var refl = ⟶*-refl , f-var
whnf-sound (suc k) σ fs f-typ refl = ⟶*-refl , f-typ
whnf-sound (suc k) σ fs (f-pi FA FB) refl = ⟶*-refl , f-pi FA FB
whnf-sound (suc k) σ fs (f-lam FA Ft) refl = ⟶*-refl , f-lam FA Ft
whnf-sound (suc k) σ fs f-nat refl = ⟶*-refl , f-nat
whnf-sound (suc k) σ fs f-ze refl = ⟶*-refl , f-ze
whnf-sound (suc k) σ fs (f-su Ft) refl = ⟶*-refl , f-su Ft
whnf-sound (suc k) σ fs f-unit refl = ⟶*-refl , f-unit
whnf-sound (suc k) σ fs f-one refl = ⟶*-refl , f-one
whnf-sound (suc k) σ fs f-empty refl = ⟶*-refl , f-empty
whnf-sound (suc k) σ fs f-dty refl = ⟶*-refl , f-dty
whnf-sound (suc k) σ fs f-ctor refl = ⟶*-refl , f-ctor
whnf-sound (suc k) σ fs (f-idt FA Fa Fb) refl = ⟶*-refl , f-idt FA Fa Fb
whnf-sound (suc k) σ fs f-rfl refl = ⟶*-refl , f-rfl
whnf-sound (suc k) σ fs (f-rwt Fe FP Ft) refl = ⟶*-refl , f-rwt Fe FP Ft
whnf-sound (suc k) σ fs (f-prod FA FB) refl = ⟶*-refl , f-prod FA FB
whnf-sound (suc k) σ fs (f-pair Fa Fb) refl = ⟶*-refl , f-pair Fa Fb
whnf-sound (suc k) σ fs (f-nu F) refl = ⟶*-refl , f-nu F
whnf-sound (suc k) σ fs (f-unf Fs Ff sh) refl = ⟶*-refl , f-unf Fs Ff sh
-- uncons: read a pair step, rewrap a λ step. Both are ⟶.
whnf-sound (suc k) σ fs (f-ucons {s = e} Fe) eq with whnf k σ e in eeq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok e′ with whnf-sound k σ fs Fe eeq
...   | r , Fe′ with ucons-step k σ Fe′ eq
...     | r′ , Fu = ⟶*-trans (ucons-e* r) r′ , Fu

whnf-⟶* : ∀ k σ {n} {t u : Tm n} → FragSig σ → Frag t → whnf k σ t ≡ ok u → σ ⊢[ spec ] t ⟶* u
whnf-⟶* k σ fs Ft eq = proj₁ (whnf-sound k σ fs Ft eq)

whnf-≈ : ∀ k σ {n} {t u : Tm n} → FragSig σ → Frag t → whnf k σ t ≡ ok u → σ ⊢[ spec ] t ≈ u
whnf-≈ k σ fs Ft eq = ⟶*→≈ (whnf-⟶* k σ fs Ft eq)

whnf-Frag : ∀ k σ {n} {t u : Tm n} → FragSig σ → Frag t → whnf k σ t ≡ ok u → Frag u
whnf-Frag k σ fs Ft eq = proj₂ (whnf-sound k σ fs Ft eq)

------------------------------------------------------------------------
-- Booleans and Results.
------------------------------------------------------------------------

∧-true : ∀ {a b} → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)
∧-true {true} {true} refl = refl , refl

∧-true₃ : ∀ {a b c} → a ∧ b ∧ c ≡ true → (a ≡ true) × (b ≡ true) × (c ≡ true)
∧-true₃ eq with ∧-true eq
... | e₁ , e = e₁ , ∧-true e

∧-true₄ : ∀ {a b c d} → a ∧ b ∧ c ∧ d ≡ true
  → (a ≡ true) × (b ≡ true) × (c ≡ true) × (d ≡ true)
∧-true₄ eq with ∧-true eq
... | e₁ , e = e₁ , ∧-true₃ e

≡ᵇ-sound : ∀ {i j} → (i ≡ᵇ j) ≡ true → i ≡ j
≡ᵇ-sound {i} {j} eq = ≡ᵇ⇒≡ i j (subst T (sym eq) tt)

eqFin-sound : ∀ {n} (i j : Fin n) → eqFin i j ≡ true → i ≡ j
eqFin-sound zero zero _ = refl
eqFin-sound (suc i) (suc j) eq = cong suc (eqFin-sound i j eq)

eqQty-sound : ∀ q q′ → eqQty q q′ ≡ true → q ≡ q′
eqQty-sound affine affine _ = refl
eqQty-sound reuse reuse _ = refl
eqQty-sound erased erased _ = refl

guard-ok : ∀ {s b} → guard s b ≡ ok tt → b ≡ true
guard-ok {b = true} _ = refl

>>-ok : ∀ {A B : Set} {r : Result A} {r′ : Result B} {x}
  → (r >> r′) ≡ ok x → (∃ λ y → r ≡ ok y) × (r′ ≡ ok x)
>>-ok {r = ok y} eq = (y , refl) , eq

-- (a >> b) >> c ≡ ok, and so on, read from the left.
>>-ok₂ : ∀ {A B C : Set} {r : Result A} {r′ : Result B} {r″ : Result C} {x}
  → (r >> r′ >> r″) ≡ ok x
  → (∃ λ y → r ≡ ok y) × (∃ λ y → r′ ≡ ok y) × (r″ ≡ ok x)
>>-ok₂ eq with >>-ok eq
... | e₁₂ , e₃ with >>-ok (proj₂ e₁₂)
...   | e₁ , e₂ = e₁ , (_ , e₂) , e₃

>>-ok₃ : ∀ {A B C D : Set} {r : Result A} {r′ : Result B} {r″ : Result C} {r‴ : Result D} {x}
  → (r >> r′ >> r″ >> r‴) ≡ ok x
  → (∃ λ y → r ≡ ok y) × (∃ λ y → r′ ≡ ok y) × (∃ λ y → r″ ≡ ok y) × (r‴ ≡ ok x)
>>-ok₃ eq with >>-ok eq
... | e , e₄ with >>-ok₂ (proj₂ e)
...   | e₁ , e₂ , e₃ = e₁ , e₂ , (_ , e₃) , e₄

ok-tt : ∀ {r : Result ⊤} {y} → r ≡ ok y → r ≡ ok tt
ok-tt eq = eq

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′}
  → a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a a′ b b′ c c′ d d′}
  → a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → f a b c d ≡ f a′ b′ c′ d′
cong₄ f refl refl refl refl = refl

------------------------------------------------------------------------
-- synEq is syntactic equality.
------------------------------------------------------------------------

synEq-sound : ∀ {n} (u v : Tm n) → synEq u v ≡ true → u ≡ v
synEqL-sound : ∀ {n} (us vs : List (Tm n)) → synEqList us vs ≡ true → us ≡ vs
synEqD-sound : ∀ {n} {t} (u v : Tm n) → TmShape t u → TmShape t v → synEqD u v ≡ true → u ≡ v

synEq-sound u v eq with ∧-true eq
... | te , de = synEqD-sound u v (shape u) (subst (λ k → TmShape k v) (sym (≡ᵇ-sound te)) (shape v)) de

synEqL-sound [] [] _ = refl
synEqL-sound (u ∷ us) (v ∷ vs) eq with ∧-true eq
... | e , es = cong₂ _∷_ (synEq-sound u v e) (synEqL-sound us vs es)

synEqD-sound (var a) (var a′) sh-var sh-var eq = cong var (eqFin-sound a a′ eq)
synEqD-sound typ typ sh-typ sh-typ _ = refl
synEqD-sound (pi a b c) (pi a′ b′ c′) sh-pi sh-pi eq with ∧-true₃ eq
... | e1 , e2 , e3 = cong₃ pi (eqQty-sound a a′ e1) (synEq-sound b b′ e2) (synEq-sound c c′ e3)
synEqD-sound (lam a b c) (lam a′ b′ c′) sh-lam sh-lam eq with ∧-true₃ eq
... | e1 , e2 , e3 = cong₃ lam (eqQty-sound a a′ e1) (synEq-sound b b′ e2) (synEq-sound c c′ e3)
synEqD-sound (app a b) (app a′ b′) sh-app sh-app eq with ∧-true eq
... | e1 , e2 = cong₂ app (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound nat nat sh-nat sh-nat _ = refl
synEqD-sound ze ze sh-ze sh-ze _ = refl
synEqD-sound (su a) (su a′) sh-su sh-su eq = cong su (synEq-sound a a′ eq)
synEqD-sound unit unit sh-unit sh-unit _ = refl
synEqD-sound one one sh-one sh-one _ = refl
synEqD-sound empty empty sh-empty sh-empty _ = refl
synEqD-sound (dty a) (dty a′) sh-dty sh-dty eq = cong dty (≡ᵇ-sound eq)
synEqD-sound (ctor a b) (ctor a′ b′) sh-ctor sh-ctor eq with ∧-true eq
... | e1 , e2 = cong₂ ctor (≡ᵇ-sound e1) (≡ᵇ-sound e2)
synEqD-sound (mData a b c) (mData a′ b′ c′) sh-mData sh-mData eq with ∧-true₃ eq
... | e1 , e2 , e3 = cong₃ mData (synEq-sound a a′ e1) (synEq-sound b b′ e2) (synEqL-sound c c′ e3)
synEqD-sound (mNat a b c d) (mNat a′ b′ c′ d′) sh-mNat sh-mNat eq with ∧-true₄ eq
... | e1 , e2 , e3 , e4 = cong₄ mNat (synEq-sound a a′ e1) (synEq-sound b b′ e2) (synEq-sound c c′ e3) (synEq-sound d d′ e4)
synEqD-sound (mEmp a b) (mEmp a′ b′) sh-mEmp sh-mEmp eq with ∧-true eq
... | e1 , e2 = cong₂ mEmp (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (mUnit a b c) (mUnit a′ b′ c′) sh-mUnit sh-mUnit eq with ∧-true₃ eq
... | e1 , e2 , e3 = cong₃ mUnit (synEq-sound a a′ e1) (synEq-sound b b′ e2) (synEq-sound c c′ e3)
synEqD-sound (idt a b c) (idt a′ b′ c′) sh-idt sh-idt eq with ∧-true₃ eq
... | e1 , e2 , e3 = cong₃ idt (synEq-sound a a′ e1) (synEq-sound b b′ e2) (synEq-sound c c′ e3)
synEqD-sound rfl rfl sh-rfl sh-rfl _ = refl
synEqD-sound (rwt a b c) (rwt a′ b′ c′) sh-rwt sh-rwt eq with ∧-true₃ eq
... | e1 , e2 , e3 = cong₃ rwt (synEq-sound a a′ e1) (synEq-sound b b′ e2) (synEq-sound c c′ e3)
synEqD-sound (def a) (def a′) sh-def sh-def eq = cong def (≡ᵇ-sound eq)
synEqD-sound (ann a b) (ann a′ b′) sh-ann sh-ann eq with ∧-true eq
... | e1 , e2 = cong₂ ann (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (prod a b) (prod a′ b′) sh-prod sh-prod eq with ∧-true eq
... | e1 , e2 = cong₂ prod (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (pair a b) (pair a′ b′) sh-pair sh-pair eq with ∧-true eq
... | e1 , e2 = cong₂ pair (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (letp a b) (letp a′ b′) sh-letp sh-letp eq with ∧-true eq
... | e1 , e2 = cong₂ letp (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (nu a) (nu a′) sh-nu sh-nu eq = cong nu (synEq-sound a a′ eq)
synEqD-sound (unf a b) (unf a′ b′) sh-unf sh-unf eq with ∧-true eq
... | e1 , e2 = cong₂ unf (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (ucons a) (ucons a′) sh-ucons sh-ucons eq = cong ucons (synEq-sound a a′ eq)
synEqD-sound i64 i64 sh-i64 sh-i64 _ = refl
synEqD-sound f32ty f32ty sh-f32ty sh-f32ty _ = refl
synEqD-sound (tensor a b) (tensor a′ b′) sh-tensor sh-tensor eq with ∧-true eq
... | e1 , e2 = cong₂ tensor (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (addi a b) (addi a′ b′) sh-addi sh-addi eq with ∧-true eq
... | e1 , e2 = cong₂ addi (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (muli a b) (muli a′ b′) sh-muli sh-muli eq with ∧-true eq
... | e1 , e2 = cong₂ muli (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (addt a b) (addt a′ b′) sh-addt sh-addt eq with ∧-true eq
... | e1 , e2 = cong₂ addt (synEq-sound a a′ e1) (synEq-sound b b′ e2)
synEqD-sound (toi64 a) (toi64 a′) sh-toi64 sh-toi64 eq = cong toi64 (synEq-sound a a′ eq)
synEqD-sound (packi a b) (packi a′ b′) sh-packi sh-packi eq with ∧-true eq
... | e1 , e2 = cong₂ packi (synEq-sound a a′ e1) (synEq-sound b b′ e2)

------------------------------------------------------------------------
-- ≈ is a congruence: it is generated by ⇛, which is.
------------------------------------------------------------------------

≈-map : ∀ {σ m n k} (F : Tm n → Tm k)
  → (∀ {t u} → σ ⊢[ m ] t ⇛ u → σ ⊢[ m ] F t ⇛ F u)
  → ∀ {t u} → σ ⊢[ m ] t ≈ u → σ ⊢[ m ] F t ≈ F u
≈-map F h (≈-step s) = ≈-step (h s)
≈-map F h ≈-refl = ≈-refl
≈-map F h (≈-sym c) = ≈-sym (≈-map F h c)
≈-map F h (≈-trans c c′) = ≈-trans (≈-map F h c) (≈-map F h c′)

≈-lam : ∀ {σ m n q} {A A′ : Tm n} {t t′}
  → σ ⊢[ m ] A ≈ A′ → σ ⊢[ m ] t ≈ t′ → σ ⊢[ m ] lam q A t ≈ lam q A′ t′
≈-lam {q = q} {A′ = A′} {t = t} cA ct =
  ≈-trans (≈-map (λ x → lam q x t) (λ s → ⇛-lam s (⇛-refl _)) cA)
          (≈-map (λ x → lam q A′ x) (λ s → ⇛-lam (⇛-refl _) s) ct)

≈-app : ∀ {σ m n} {f f′ a a′ : Tm n}
  → σ ⊢[ m ] f ≈ f′ → σ ⊢[ m ] a ≈ a′ → σ ⊢[ m ] app f a ≈ app f′ a′
≈-app {f′ = f′} {a = a} cf ca =
  ≈-trans (≈-map (λ x → app x a) (λ s → ⇛-app s (⇛-refl _)) cf)
          (≈-map (λ x → app f′ x) (λ s → ⇛-app (⇛-refl _) s) ca)

≈-su : ∀ {σ m n} {a a′ : Tm n} → σ ⊢[ m ] a ≈ a′ → σ ⊢[ m ] su a ≈ su a′
≈-su = ≈-map su ⇛-su

≈-idt : ∀ {σ m n} {A A′ a a′ b b′ : Tm n}
  → σ ⊢[ m ] A ≈ A′ → σ ⊢[ m ] a ≈ a′ → σ ⊢[ m ] b ≈ b′
  → σ ⊢[ m ] idt A a b ≈ idt A′ a′ b′
≈-idt {A′ = A′} {a = a} {a′} {b} cA ca cb =
  ≈-trans (≈-map (λ x → idt x a b) (λ s → ⇛-idt s (⇛-refl _) (⇛-refl _)) cA)
  (≈-trans (≈-map (λ x → idt A′ x b) (λ s → ⇛-idt (⇛-refl _) s (⇛-refl _)) ca)
           (≈-map (λ x → idt A′ a′ x) (λ s → ⇛-idt (⇛-refl _) (⇛-refl _) s) cb))

≈-mNat : ∀ {σ m n} {e e′ : Tm n} {P P′ z z′ s s′}
  → σ ⊢[ m ] e ≈ e′ → σ ⊢[ m ] P ≈ P′ → σ ⊢[ m ] z ≈ z′ → σ ⊢[ m ] s ≈ s′
  → σ ⊢[ m ] mNat e P z s ≈ mNat e′ P′ z′ s′
≈-mNat {e′ = e′} {P} {P′} {z} {z′} {s} ce cP cz cs =
  ≈-trans (≈-map (λ x → mNat x P z s) (λ d → ⇛-mNat d (⇛-refl _) (⇛-refl _) (⇛-refl _)) ce)
  (≈-trans (≈-map (λ x → mNat e′ x z s) (λ d → ⇛-mNat (⇛-refl _) d (⇛-refl _) (⇛-refl _)) cP)
  (≈-trans (≈-map (λ x → mNat e′ P′ x s) (λ d → ⇛-mNat (⇛-refl _) (⇛-refl _) d (⇛-refl _)) cz)
           (≈-map (λ x → mNat e′ P′ z′ x) (λ d → ⇛-mNat (⇛-refl _) (⇛-refl _) (⇛-refl _) d) cs)))

≈-mEmp : ∀ {σ m n} {e e′ : Tm n} {P P′}
  → σ ⊢[ m ] e ≈ e′ → σ ⊢[ m ] P ≈ P′ → σ ⊢[ m ] mEmp e P ≈ mEmp e′ P′
≈-mEmp {e′ = e′} {P} ce cP =
  ≈-trans (≈-map (λ x → mEmp x P) (λ d → ⇛-mEmp d (⇛-refl _)) ce)
          (≈-map (λ x → mEmp e′ x) (λ d → ⇛-mEmp (⇛-refl _) d) cP)

≈-mUnit : ∀ {σ m n} {e e′ : Tm n} {P P′ u u′}
  → σ ⊢[ m ] e ≈ e′ → σ ⊢[ m ] P ≈ P′ → σ ⊢[ m ] u ≈ u′
  → σ ⊢[ m ] mUnit e P u ≈ mUnit e′ P′ u′
≈-mUnit {e′ = e′} {P} {P′} {u} ce cP cu =
  ≈-trans (≈-map (λ x → mUnit x P u) (λ d → ⇛-mUnit d (⇛-refl _) (⇛-refl _)) ce)
  (≈-trans (≈-map (λ x → mUnit e′ x u) (λ d → ⇛-mUnit (⇛-refl _) d (⇛-refl _)) cP)
           (≈-map (λ x → mUnit e′ P′ x) (λ d → ⇛-mUnit (⇛-refl _) (⇛-refl _) d) cu))

≈-rwt : ∀ {σ m n} {e e′ : Tm n} {P P′ t t′}
  → σ ⊢[ m ] e ≈ e′ → σ ⊢[ m ] P ≈ P′ → σ ⊢[ m ] t ≈ t′
  → σ ⊢[ m ] rwt e P t ≈ rwt e′ P′ t′
≈-rwt {e′ = e′} {P} {P′} {t} ce cP ct =
  ≈-trans (≈-map (λ x → rwt x P t) (λ d → ⇛-rwt d (⇛-refl _) (⇛-refl _)) ce)
  (≈-trans (≈-map (λ x → rwt e′ x t) (λ d → ⇛-rwt (⇛-refl _) d (⇛-refl _)) cP)
           (≈-map (λ x → rwt e′ P′ x) (λ d → ⇛-rwt (⇛-refl _) (⇛-refl _) d) ct))

≈-ann : ∀ {σ m n} {e e′ A A′ : Tm n}
  → σ ⊢[ m ] e ≈ e′ → σ ⊢[ m ] A ≈ A′ → σ ⊢[ m ] ann e A ≈ ann e′ A′
≈-ann {e′ = e′} {A} ce cA =
  ≈-trans (≈-map (λ x → ann x A) (λ d → ⇛-annc d (⇛-refl _)) ce)
          (≈-map (λ x → ann e′ x) (λ d → ⇛-annc (⇛-refl _) d) cA)

≈-prod : ∀ {σ m n} {A A′ B B′ : Tm n}
  → σ ⊢[ m ] A ≈ A′ → σ ⊢[ m ] B ≈ B′ → σ ⊢[ m ] prod A B ≈ prod A′ B′
≈-prod {A′ = A′} {B} cA cB =
  ≈-trans (≈-map (λ x → prod x B) (λ d → ⇛-prod d (⇛-refl _)) cA)
          (≈-map (λ x → prod A′ x) (λ d → ⇛-prod (⇛-refl _) d) cB)

≈-pair : ∀ {σ m n} {a a′ b b′ : Tm n}
  → σ ⊢[ m ] a ≈ a′ → σ ⊢[ m ] b ≈ b′ → σ ⊢[ m ] pair a b ≈ pair a′ b′
≈-pair {a′ = a′} {b} ca cb =
  ≈-trans (≈-map (λ x → pair x b) (λ d → ⇛-pair d (⇛-refl _)) ca)
          (≈-map (λ x → pair a′ x) (λ d → ⇛-pair (⇛-refl _) d) cb)

≈-letp : ∀ {σ m n} {e e′ : Tm n} {t t′}
  → σ ⊢[ m ] e ≈ e′ → σ ⊢[ m ] t ≈ t′ → σ ⊢[ m ] letp e t ≈ letp e′ t′
≈-letp {e′ = e′} {t} ce ct =
  ≈-trans (≈-map (λ x → letp x t) (λ d → ⇛-letp d (⇛-refl _)) ce)
          (≈-map (λ x → letp e′ x) (λ d → ⇛-letp (⇛-refl _) d) ct)

≈-nu : ∀ {σ m n} {F F′ : Tm (suc n)}
  → σ ⊢[ m ] F ≈ F′ → σ ⊢[ m ] nu F ≈ nu F′
≈-nu = ≈-map nu ⇛-nu

≈-unf : ∀ {σ m n} {s s′ f f′ : Tm n}
  → σ ⊢[ m ] s ≈ s′ → σ ⊢[ m ] f ≈ f′ → σ ⊢[ m ] unf s f ≈ unf s′ f′
≈-unf {s′ = s′} {f} cs cf =
  ≈-trans (≈-map (λ x → unf x f) (λ d → ⇛-unf d (⇛-refl _)) cs)
          (≈-map (λ x → unf s′ x) (λ d → ⇛-unf (⇛-refl _) d) cf)

≈-ucons : ∀ {σ m n} {s s′ : Tm n}
  → σ ⊢[ m ] s ≈ s′ → σ ⊢[ m ] ucons s ≈ ucons s′
≈-ucons = ≈-map ucons ⇛-ucons

⇛L-++ˡ : ∀ {σ m n} (pre : List (Tm n)) {xs ys}
  → σ ⊢[ m ] xs ⇛L ys → σ ⊢[ m ] pre ++ xs ⇛L pre ++ ys
⇛L-++ˡ [] d = d
⇛L-++ˡ (p ∷ pre) d = ⇛L-∷ (⇛-refl p) (⇛L-++ˡ pre d)

≈-mData-bs : ∀ {σ m n} {e : Tm n} {P} (pre : List (Tm n)) {bs bs′}
  → σ ⊢[ m ] bs ≈L bs′ → σ ⊢[ m ] mData e P (pre ++ bs) ≈ mData e P (pre ++ bs′)
≈-mData-bs pre ≈L-[] = ≈-refl
≈-mData-bs {σ} {m} {e = e} {P} pre (≈L-∷ {a} {b} {as} {bs} c cs) =
  ≈-trans
    (≈-map (λ x → mData e P (pre ++ x ∷ as))
           (λ d → ⇛-mData (⇛-refl _) (⇛-refl _) (⇛L-++ˡ pre (⇛L-∷ d (⇛L-refl as)))) c)
    (subst₂ (λ xs ys → σ ⊢[ m ] mData e P xs ≈ mData e P ys)
            (++-assoc pre (b ∷ []) as) (++-assoc pre (b ∷ []) bs)
            (≈-mData-bs (pre ++ b ∷ []) cs))

≈-mData : ∀ {σ m n} {e e′ : Tm n} {P P′ bs bs′}
  → σ ⊢[ m ] e ≈ e′ → σ ⊢[ m ] P ≈ P′ → σ ⊢[ m ] bs ≈L bs′
  → σ ⊢[ m ] mData e P bs ≈ mData e′ P′ bs′
≈-mData {e′ = e′} {P} {P′} {bs} ce cP cbs =
  ≈-trans (≈-map (λ x → mData x P bs) (λ d → ⇛-mData d (⇛-refl _) (⇛L-refl _)) ce)
  (≈-trans (≈-map (λ x → mData e′ x bs) (λ d → ⇛-mData (⇛-refl _) d (⇛L-refl _)) cP)
           (≈-mData-bs [] cbs))

------------------------------------------------------------------------
-- conv decides ≈ (soundly). Fuel only bounds the search.
------------------------------------------------------------------------

conv-sound : ∀ k σ {n} {u v : Tm n} → FragSig σ → Frag u → Frag v
  → conv k σ u v ≡ ok tt → σ ⊢[ spec ] u ≈ v
convArgs-sound : ∀ k σ {n} {us vs : List (Tm n)} → FragSig σ → FragL us → FragL vs
  → convArgs k σ us vs ≡ ok tt → σ ⊢[ spec ] us ≈L vs
convStuck-sound : ∀ k σ {n} {u v : Tm n} → FragSig σ → Frag u → Frag v
  → ∀ du dv → defArgs u ≡ du → defArgs v ≡ dv
  → convStuck k σ u v du dv ≡ ok tt → σ ⊢[ spec ] u ≈ v
convN-sound : ∀ k σ {n} {u v : Tm n} → FragSig σ → Frag u → Frag v
  → convN k σ u v ≡ ok tt → σ ⊢[ spec ] u ≈ v
convND-sound : ∀ k σ {n} {t} {u v : Tm n} → TmShape t u → TmShape t v
  → FragSig σ → Frag u → Frag v
  → convND k σ u v ≡ ok tt → σ ⊢[ spec ] u ≈ v

conv-sound (suc k) σ {u = u} {v} fs Fu Fv eq with synEq u v in seq
... | true with synEq-sound u v seq
...   | refl = ≈-refl
conv-sound (suc k) σ fs Fu Fv eq | false = convStuck-sound k σ fs Fu Fv _ _ refl refl eq

convArgs-sound k σ fs fl-[] fl-[] _ = ≈L-[]
convArgs-sound k σ fs (fl-∷ Fa Fas) (fl-∷ Fb Fbs) eq with >>-ok eq
... | (_ , ca) , cas = ≈L-∷ (conv-sound k σ fs Fa Fb ca) (convArgs-sound k σ fs Fas Fbs cas)

-- The fallback: whnf both sides and compare.
convWhnf-sound : ∀ k σ {n} {u v : Tm n} → FragSig σ → Frag u → Frag v
  → convWhnf k σ u v ≡ ok tt → σ ⊢[ spec ] u ≈ v
convWhnf-sound k σ {u = u} {v} fs Fu Fv eq with whnf k σ u in ueq
... | fail _ = ⊥-elim (fail≢ok eq)
... | ok u′ with whnf k σ v in veq
...   | fail _ = ⊥-elim (fail≢ok eq)
...   | ok v′ =
  ≈-trans (whnf-≈ k σ fs Fu ueq)
  (≈-trans (convN-sound k σ fs (whnf-Frag k σ fs Fu ueq) (whnf-Frag k σ fs Fv veq) eq)
           (≈-sym (whnf-≈ k σ fs Fv veq)))

convStuck-sound k σ {u = u} {v} fs Fu Fv (just (i , a , as)) (just (j , b , bs)) du dv eq
  with (i ≡ᵇ j) ∧ not (ctorHead a) ∧ not (ctorHead b) in ceq
... | false = convWhnf-sound k σ fs Fu Fv eq
... | true with conv k σ a b >> convArgs k σ as bs in aeq
...   | fail _ = convWhnf-sound k σ fs Fu Fv eq
...   | ok _ with ≡ᵇ-sound {i} {j} (proj₁ (∧-true {i ≡ᵇ j} ceq)) | defArgs-just du | defArgs-just dv | >>-ok aeq
...     | refl | spu | spv | (_ , ca) , cas with Frag-Spine spu Fu | Frag-Spine spv Fv
...       | _ , fl-∷ Fa Fas | _ , fl-∷ Fb Fbs =
  subst₂ (λ x y → σ ⊢[ spec ] x ≈ y) (sym (Spine-≡ spu)) (sym (Spine-≡ spv))
    (≈-appsFrom {f = def i} ≈-refl
      (≈L-∷ (conv-sound k σ fs Fa Fb ca) (convArgs-sound k σ fs Fas Fbs cas)))
convStuck-sound k σ fs Fu Fv (just _) nothing _ _ eq = convWhnf-sound k σ fs Fu Fv eq
convStuck-sound k σ fs Fu Fv nothing _ _ _ eq = convWhnf-sound k σ fs Fu Fv eq

convN-sound k σ {u = u} {v} fs Fu Fv eq with tmTag u ≡ᵇ tmTag v in teq
... | true = convND-sound k σ (shape u) (subst (λ x → TmShape x v) (sym (≡ᵇ-sound teq)) (shape v)) fs Fu Fv eq
... | false = ⊥-elim (fail≢ok eq)

convND-sound k σ (sh-var {x}) (sh-var {y}) fs _ _ eq with eqFin-sound x y (guard-ok eq)
... | refl = ≈-refl
convND-sound k σ sh-typ sh-typ fs _ _ _ = ≈-refl
convND-sound k σ (sh-pi {q}) (sh-pi {q′}) fs (f-pi FA FB) (f-pi FA′ FB′) eq with >>-ok₂ eq
... | (_ , g) , (_ , cA) , cB with eqQty-sound q q′ (guard-ok g)
...   | refl = ≈-pi (conv-sound k σ fs FA FA′ cA) (conv-sound k σ fs FB FB′ cB)
convND-sound k σ (sh-lam {q}) (sh-lam {q′}) fs (f-lam FA Ft) (f-lam FA′ Ft′) eq with >>-ok₂ eq
... | (_ , g) , (_ , cA) , ct with eqQty-sound q q′ (guard-ok g)
...   | refl = ≈-lam (conv-sound k σ fs FA FA′ cA) (conv-sound k σ fs Ft Ft′ ct)
convND-sound k σ sh-app sh-app fs (f-app Ff Fa) (f-app Fg Fb) eq with >>-ok eq
... | (_ , cf) , ca = ≈-app (conv-sound k σ fs Ff Fg cf) (conv-sound k σ fs Fa Fb ca)
convND-sound k σ sh-nat sh-nat fs _ _ _ = ≈-refl
convND-sound k σ sh-ze sh-ze fs _ _ _ = ≈-refl
convND-sound k σ sh-su sh-su fs (f-su Fa) (f-su Fb) eq = ≈-su (conv-sound k σ fs Fa Fb eq)
convND-sound k σ sh-unit sh-unit fs _ _ _ = ≈-refl
convND-sound k σ sh-one sh-one fs _ _ _ = ≈-refl
convND-sound k σ sh-empty sh-empty fs _ _ _ = ≈-refl
convND-sound k σ (sh-dty {i}) (sh-dty {j}) fs _ _ eq with ≡ᵇ-sound {i} {j} (guard-ok eq)
... | refl = ≈-refl
convND-sound k σ (sh-ctor {i} {j}) (sh-ctor {i′} {j′}) fs _ _ eq with ∧-true (guard-ok eq)
... | ei , ej with ≡ᵇ-sound {i} {i′} ei | ≡ᵇ-sound {j} {j′} ej
...   | refl | refl = ≈-refl
convND-sound k σ sh-mData sh-mData fs (f-mData Fe FP Fbs) (f-mData Fe′ FP′ Fbs′) eq with >>-ok₂ eq
... | (_ , ce) , (_ , cP) , cbs =
  ≈-mData (conv-sound k σ fs Fe Fe′ ce) (conv-sound k σ fs FP FP′ cP) (convArgs-sound k σ fs Fbs Fbs′ cbs)
convND-sound k σ sh-mNat sh-mNat fs (f-mNat Fe FP Fz Fs) (f-mNat Fe′ FP′ Fz′ Fs′) eq with >>-ok₃ eq
... | (_ , ce) , (_ , cP) , (_ , cz) , cs =
  ≈-mNat (conv-sound k σ fs Fe Fe′ ce) (conv-sound k σ fs FP FP′ cP)
         (conv-sound k σ fs Fz Fz′ cz) (conv-sound k σ fs Fs Fs′ cs)
convND-sound k σ sh-mEmp sh-mEmp fs (f-mEmp Fe FP) (f-mEmp Fe′ FP′) eq with >>-ok eq
... | (_ , ce) , cP = ≈-mEmp (conv-sound k σ fs Fe Fe′ ce) (conv-sound k σ fs FP FP′ cP)
convND-sound k σ sh-mUnit sh-mUnit fs (f-mUnit Fe FP Fu) (f-mUnit Fe′ FP′ Fu′) eq with >>-ok₂ eq
... | (_ , ce) , (_ , cP) , cu =
  ≈-mUnit (conv-sound k σ fs Fe Fe′ ce) (conv-sound k σ fs FP FP′ cP) (conv-sound k σ fs Fu Fu′ cu)
convND-sound k σ sh-idt sh-idt fs (f-idt FA Fa Fb) (f-idt FA′ Fa′ Fb′) eq with >>-ok₂ eq
... | (_ , cA) , (_ , ca) , cb =
  ≈-idt (conv-sound k σ fs FA FA′ cA) (conv-sound k σ fs Fa Fa′ ca) (conv-sound k σ fs Fb Fb′ cb)
convND-sound k σ sh-rfl sh-rfl fs _ _ _ = ≈-refl
convND-sound k σ sh-rwt sh-rwt fs (f-rwt Fe FP Ft) (f-rwt Fe′ FP′ Ft′) eq with >>-ok₂ eq
... | (_ , ce) , (_ , cP) , ct =
  ≈-rwt (conv-sound k σ fs Fe Fe′ ce) (conv-sound k σ fs FP FP′ cP) (conv-sound k σ fs Ft Ft′ ct)
convND-sound k σ (sh-def {i}) (sh-def {j}) fs _ _ eq with ≡ᵇ-sound {i} {j} (guard-ok eq)
... | refl = ≈-refl
convND-sound k σ sh-ann sh-ann fs (f-ann Fe FA) (f-ann Fe′ FA′) eq with >>-ok eq
... | (_ , ce) , cA = ≈-ann (conv-sound k σ fs Fe Fe′ ce) (conv-sound k σ fs FA FA′ cA)
convND-sound k σ sh-prod sh-prod fs (f-prod FA FB) (f-prod FA′ FB′) eq with >>-ok eq
... | (_ , cA) , cB = ≈-prod (conv-sound k σ fs FA FA′ cA) (conv-sound k σ fs FB FB′ cB)
convND-sound k σ sh-pair sh-pair fs (f-pair Fa Fb) (f-pair Fa′ Fb′) eq with >>-ok eq
... | (_ , ca) , cb = ≈-pair (conv-sound k σ fs Fa Fa′ ca) (conv-sound k σ fs Fb Fb′ cb)
convND-sound k σ sh-letp sh-letp fs (f-letp Fe Ft) (f-letp Fe′ Ft′) eq with >>-ok eq
... | (_ , ce) , ct = ≈-letp (conv-sound k σ fs Fe Fe′ ce) (conv-sound k σ fs Ft Ft′ ct)
convND-sound k σ sh-nu sh-nu fs (f-nu F) (f-nu F′) eq =
  ≈-nu (conv-sound k σ fs F F′ eq)
convND-sound k σ sh-unf sh-unf fs (f-unf Fs Ff _) (f-unf Fs′ Ff′ _) eq with >>-ok eq
... | (_ , cs) , cf = ≈-unf (conv-sound k σ fs Fs Fs′ cs) (conv-sound k σ fs Ff Ff′ cf)
convND-sound k σ sh-ucons sh-ucons fs (f-ucons Fs) (f-ucons Fs′) eq =
  ≈-ucons (conv-sound k σ fs Fs Fs′ eq)
convND-sound k σ sh-i64 sh-i64 fs () _ _
convND-sound k σ sh-f32ty sh-f32ty fs () _ _
convND-sound k σ sh-tensor sh-tensor fs () _ _
convND-sound k σ sh-addi sh-addi fs () _ _
convND-sound k σ sh-muli sh-muli fs () _ _
convND-sound k σ sh-addt sh-addt fs () _ _
convND-sound k σ sh-toi64 sh-toi64 fs () _ _
convND-sound k σ sh-packi sh-packi fs () _ _

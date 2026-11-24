------------------------------------------------------------------------
-- whnf k σ t ≡ ok v is a spec-mode reduction t ⇛* v.
--
-- The checker's whnf unfolds a definition whenever the lookup succeeds,
-- at every mode. spec permits every definition, so the witness is at
-- spec. No fragment hypothesis: a stuck numeral, float, or tensor is a
-- reflexive step, the same way a stuck variable is. A reusable beta
-- that shares its argument is still a ⇛* reduct: a ⇛* a′ gives
-- inst t a ⇛* inst t a′ (⇛*-inst).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Productive.Whnf where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (n<1+n; n≤1+n)
open import Data.Nat.Induction using (<-wellFounded; Acc; acc)
import Data.Fin.Base as Fin
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base using (Mode; run; evid; spec; ok; fail; Qty; affine; reuse; erased)
open import Muro.Syntax
open import Muro.Subst using (closed; inst; inst₂; appsFrom)
open import Muro.Env using (Sig; Def; lookupDef; lookupList; allowedDef)
open import Muro.Spine using (ctorSpine; ctorSpine-just)
open import Muro.Check using (whnf; whnfList; uconsWhnf; dataWhnf; fail≢ok; reuseWhnf; ReuseWhnf; cbn; shared)
open import Muro.Word using (wordStep)
open import Muro.Reduction

ok-inj : ∀ {A : Set} {x y : A} → ok x ≡ ok y → x ≡ y
ok-inj refl = refl

allowed-spec : ∀ m → allowedDef m spec ≡ true
allowed-spec run  = refl
allowed-spec evid = refl
allowed-spec spec = refl

app-star : ∀ {σ n} {f f′ a : Tm n}
  → σ ⊢[ spec ] f ⇛* f′ → σ ⊢[ spec ] app f a ⇛* app f′ a
app-star ⇛*-refl = ⇛*-refl
app-star {a = a} (⇛*-step d r) = ⇛*-step (⇛-app d (⇛-refl a)) (app-star r)

mNat-star : ∀ {σ n} {e e′ : Tm n} {P z s}
  → σ ⊢[ spec ] e ⇛* e′ → σ ⊢[ spec ] mNat e P z s ⇛* mNat e′ P z s
mNat-star ⇛*-refl = ⇛*-refl
mNat-star {P = P} {z = z} {s = s} (⇛*-step d r) =
  ⇛*-step (⇛-mNat d (⇛-refl P) (⇛-refl z) (⇛-refl s)) (mNat-star r)

mUnit-star : ∀ {σ n} {e e′ : Tm n} {P u}
  → σ ⊢[ spec ] e ⇛* e′ → σ ⊢[ spec ] mUnit e P u ⇛* mUnit e′ P u
mUnit-star ⇛*-refl = ⇛*-refl
mUnit-star {P = P} {u = u} (⇛*-step d r) =
  ⇛*-step (⇛-mUnit d (⇛-refl P) (⇛-refl u)) (mUnit-star r)

mEmp-star : ∀ {σ n} {e e′ : Tm n} {P}
  → σ ⊢[ spec ] e ⇛* e′ → σ ⊢[ spec ] mEmp e P ⇛* mEmp e′ P
mEmp-star ⇛*-refl = ⇛*-refl
mEmp-star {P = P} (⇛*-step d r) =
  ⇛*-step (⇛-mEmp d (⇛-refl P)) (mEmp-star r)

mData-star : ∀ {σ n} {e e′ : Tm n} {P bs}
  → σ ⊢[ spec ] e ⇛* e′ → σ ⊢[ spec ] mData e P bs ⇛* mData e′ P bs
mData-star ⇛*-refl = ⇛*-refl
mData-star {P = P} {bs = bs} (⇛*-step d r) =
  ⇛*-step (⇛-mData d (⇛-refl P) (⇛L-refl bs)) (mData-star r)

letp-star : ∀ {σ n} {e e′ : Tm n} {t}
  → σ ⊢[ spec ] e ⇛* e′ → σ ⊢[ spec ] letp e t ⇛* letp e′ t
letp-star ⇛*-refl = ⇛*-refl
letp-star {t = t} (⇛*-step d r) =
  ⇛*-step (⇛-letp d (⇛-refl t)) (letp-star r)

ucons-star : ∀ {σ n} {e e′ : Tm n}
  → σ ⊢[ spec ] e ⇛* e′ → σ ⊢[ spec ] ucons e ⇛* ucons e′
ucons-star ⇛*-refl = ⇛*-refl
ucons-star (⇛*-step d r) = ⇛*-step (⇛-ucons d) (ucons-star r)

stay : ∀ {n} (σ : Sig) (e v : Tm n)
  → ok (ucons e) ≡ ok v
  → σ ⊢[ spec ] ucons e ⇛* v
stay σ e v eq = subst (λ z → σ ⊢[ spec ] ucons e ⇛* z) (ok-inj eq) ⇛*-refl

-- The three uncons redexes, and a reflexive step on everything else.
-- The clauses are the clauses of uconsWhnf, so the equality reduces.
ucons-go : ∀ {n} k (σ : Sig) (e v : Tm n)
  → uconsWhnf k σ e ≡ ok v
  → σ ⊢[ spec ] ucons e ⇛* v
ucons-go k σ (unf s (pair h t)) v eq =
  subst (λ z → σ ⊢[ spec ] ucons (unf s (pair h t)) ⇛* z) (ok-inj eq)
    (⇛*-one (⇛-ιβr (⇛-refl h) (⇛-refl t) (⇛-refl s)))
ucons-go k σ (unf s (lam q A (pair h t))) v eq =
  subst (λ z → σ ⊢[ spec ] ucons (unf s (lam q A (pair h t))) ⇛* z) (ok-inj eq)
    (⇛*-one (⇛-ιβp (⇛-refl h) (⇛-refl t) (⇛-refl s) (⇛-refl A)))
ucons-go k σ (unf (pair a b) (lam q A (var Fin.zero))) v eq =
  subst (λ z → σ ⊢[ spec ] ucons (unf (pair a b) (lam q A (var Fin.zero))) ⇛* z)
    (ok-inj eq)
    (⇛*-one (⇛-ιβ0 (⇛-refl a) (⇛-refl b) (⇛-refl A)))

ucons-go k σ (unf (var wx) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (var wx) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (typ) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (typ) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (pi wq wA wB) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (pi wq wA wB) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (lam wq wA wt) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (lam wq wA wt) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (app wg wb) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (app wg wb) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (nat) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (nat) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (ze) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (ze) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (su wu) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (su wu) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (unit) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (unit) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (one) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (one) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (empty) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (empty) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (dty wi) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (dty wi) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (ctor wi wj) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (ctor wi wj) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (mData we wP wbs) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (mData we wP wbs) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (mNat we wP wz ws) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (mNat we wP wz ws) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (mEmp we wP) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (mEmp we wP) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (mUnit we wP wu) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (mUnit we wP wu) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (idt wA wa wb) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (idt wA wa wb) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (rfl) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (rfl) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (rwt we wP wt) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (rwt we wP wt) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (def wi) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (def wi) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (ann we wA) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (ann we wA) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (prod wA wB) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (prod wA wB) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (letp we wt) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (letp we wt) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (nu wF) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (nu wF) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (unf ws wf) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (unf ws wf) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (ucons we) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (ucons we) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (i64) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (i64) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (f32ty) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (f32ty) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (tensor wd ws) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (tensor wd ws) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (addi wx wy) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (addi wx wy) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (muli wx wy) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (muli wx wy) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (addt wt wu) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (addt wt wu) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (toi64 wt) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (toi64 wt) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (packi wx wy) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (packi wx wy) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf (word wop wts) (lam q1 A1 (var Fin.zero))) v eq = stay σ (unf (word wop wts) (lam q1 A1 (var Fin.zero))) v eq
ucons-go k σ (unf s (lam q1 A1 (var (Fin.suc y)))) v eq =
  stay σ (unf s (lam q1 A1 (var (Fin.suc y)))) v eq
ucons-go k σ (unf s (lam q1 A1 (typ))) v eq = stay σ (unf s (lam q1 A1 (typ))) v eq
ucons-go k σ (unf s (lam q1 A1 (pi wq wA wB))) v eq = stay σ (unf s (lam q1 A1 (pi wq wA wB))) v eq
ucons-go k σ (unf s (lam q1 A1 (lam wq wA wt))) v eq = stay σ (unf s (lam q1 A1 (lam wq wA wt))) v eq
ucons-go k σ (unf s (lam q1 A1 (app wg wb))) v eq = stay σ (unf s (lam q1 A1 (app wg wb))) v eq
ucons-go k σ (unf s (lam q1 A1 (nat))) v eq = stay σ (unf s (lam q1 A1 (nat))) v eq
ucons-go k σ (unf s (lam q1 A1 (ze))) v eq = stay σ (unf s (lam q1 A1 (ze))) v eq
ucons-go k σ (unf s (lam q1 A1 (su wu))) v eq = stay σ (unf s (lam q1 A1 (su wu))) v eq
ucons-go k σ (unf s (lam q1 A1 (unit))) v eq = stay σ (unf s (lam q1 A1 (unit))) v eq
ucons-go k σ (unf s (lam q1 A1 (one))) v eq = stay σ (unf s (lam q1 A1 (one))) v eq
ucons-go k σ (unf s (lam q1 A1 (empty))) v eq = stay σ (unf s (lam q1 A1 (empty))) v eq
ucons-go k σ (unf s (lam q1 A1 (dty wi))) v eq = stay σ (unf s (lam q1 A1 (dty wi))) v eq
ucons-go k σ (unf s (lam q1 A1 (ctor wi wj))) v eq = stay σ (unf s (lam q1 A1 (ctor wi wj))) v eq
ucons-go k σ (unf s (lam q1 A1 (mData we wP wbs))) v eq = stay σ (unf s (lam q1 A1 (mData we wP wbs))) v eq
ucons-go k σ (unf s (lam q1 A1 (mNat we wP wz ws))) v eq = stay σ (unf s (lam q1 A1 (mNat we wP wz ws))) v eq
ucons-go k σ (unf s (lam q1 A1 (mEmp we wP))) v eq = stay σ (unf s (lam q1 A1 (mEmp we wP))) v eq
ucons-go k σ (unf s (lam q1 A1 (mUnit we wP wu))) v eq = stay σ (unf s (lam q1 A1 (mUnit we wP wu))) v eq
ucons-go k σ (unf s (lam q1 A1 (idt wA wa wb))) v eq = stay σ (unf s (lam q1 A1 (idt wA wa wb))) v eq
ucons-go k σ (unf s (lam q1 A1 (rfl))) v eq = stay σ (unf s (lam q1 A1 (rfl))) v eq
ucons-go k σ (unf s (lam q1 A1 (rwt we wP wt))) v eq = stay σ (unf s (lam q1 A1 (rwt we wP wt))) v eq
ucons-go k σ (unf s (lam q1 A1 (def wi))) v eq = stay σ (unf s (lam q1 A1 (def wi))) v eq
ucons-go k σ (unf s (lam q1 A1 (ann we wA))) v eq = stay σ (unf s (lam q1 A1 (ann we wA))) v eq
ucons-go k σ (unf s (lam q1 A1 (prod wA wB))) v eq = stay σ (unf s (lam q1 A1 (prod wA wB))) v eq
ucons-go k σ (unf s (lam q1 A1 (letp we wt))) v eq = stay σ (unf s (lam q1 A1 (letp we wt))) v eq
ucons-go k σ (unf s (lam q1 A1 (nu wF))) v eq = stay σ (unf s (lam q1 A1 (nu wF))) v eq
ucons-go k σ (unf s (lam q1 A1 (unf ws wf))) v eq = stay σ (unf s (lam q1 A1 (unf ws wf))) v eq
ucons-go k σ (unf s (lam q1 A1 (ucons we))) v eq = stay σ (unf s (lam q1 A1 (ucons we))) v eq
ucons-go k σ (unf s (lam q1 A1 (i64))) v eq = stay σ (unf s (lam q1 A1 (i64))) v eq
ucons-go k σ (unf s (lam q1 A1 (f32ty))) v eq = stay σ (unf s (lam q1 A1 (f32ty))) v eq
ucons-go k σ (unf s (lam q1 A1 (tensor wd ws))) v eq = stay σ (unf s (lam q1 A1 (tensor wd ws))) v eq
ucons-go k σ (unf s (lam q1 A1 (addi wx wy))) v eq = stay σ (unf s (lam q1 A1 (addi wx wy))) v eq
ucons-go k σ (unf s (lam q1 A1 (muli wx wy))) v eq = stay σ (unf s (lam q1 A1 (muli wx wy))) v eq
ucons-go k σ (unf s (lam q1 A1 (addt wt wu))) v eq = stay σ (unf s (lam q1 A1 (addt wt wu))) v eq
ucons-go k σ (unf s (lam q1 A1 (toi64 wt))) v eq = stay σ (unf s (lam q1 A1 (toi64 wt))) v eq
ucons-go k σ (unf s (lam q1 A1 (packi wx wy))) v eq = stay σ (unf s (lam q1 A1 (packi wx wy))) v eq
ucons-go k σ (unf s (lam q1 A1 (word wop wts))) v eq = stay σ (unf s (lam q1 A1 (word wop wts))) v eq
ucons-go k σ (unf s (var wx)) v eq = stay σ (unf s (var wx)) v eq
ucons-go k σ (unf s (typ)) v eq = stay σ (unf s (typ)) v eq
ucons-go k σ (unf s (pi wq wA wB)) v eq = stay σ (unf s (pi wq wA wB)) v eq
ucons-go k σ (unf s (app wg wb)) v eq = stay σ (unf s (app wg wb)) v eq
ucons-go k σ (unf s (nat)) v eq = stay σ (unf s (nat)) v eq
ucons-go k σ (unf s (ze)) v eq = stay σ (unf s (ze)) v eq
ucons-go k σ (unf s (su wu)) v eq = stay σ (unf s (su wu)) v eq
ucons-go k σ (unf s (unit)) v eq = stay σ (unf s (unit)) v eq
ucons-go k σ (unf s (one)) v eq = stay σ (unf s (one)) v eq
ucons-go k σ (unf s (empty)) v eq = stay σ (unf s (empty)) v eq
ucons-go k σ (unf s (dty wi)) v eq = stay σ (unf s (dty wi)) v eq
ucons-go k σ (unf s (ctor wi wj)) v eq = stay σ (unf s (ctor wi wj)) v eq
ucons-go k σ (unf s (mData we wP wbs)) v eq = stay σ (unf s (mData we wP wbs)) v eq
ucons-go k σ (unf s (mNat we wP wz ws)) v eq = stay σ (unf s (mNat we wP wz ws)) v eq
ucons-go k σ (unf s (mEmp we wP)) v eq = stay σ (unf s (mEmp we wP)) v eq
ucons-go k σ (unf s (mUnit we wP wu)) v eq = stay σ (unf s (mUnit we wP wu)) v eq
ucons-go k σ (unf s (idt wA wa wb)) v eq = stay σ (unf s (idt wA wa wb)) v eq
ucons-go k σ (unf s (rfl)) v eq = stay σ (unf s (rfl)) v eq
ucons-go k σ (unf s (rwt we wP wt)) v eq = stay σ (unf s (rwt we wP wt)) v eq
ucons-go k σ (unf s (def wi)) v eq = stay σ (unf s (def wi)) v eq
ucons-go k σ (unf s (ann we wA)) v eq = stay σ (unf s (ann we wA)) v eq
ucons-go k σ (unf s (prod wA wB)) v eq = stay σ (unf s (prod wA wB)) v eq
ucons-go k σ (unf s (letp we wt)) v eq = stay σ (unf s (letp we wt)) v eq
ucons-go k σ (unf s (nu wF)) v eq = stay σ (unf s (nu wF)) v eq
ucons-go k σ (unf s (unf ws wf)) v eq = stay σ (unf s (unf ws wf)) v eq
ucons-go k σ (unf s (ucons we)) v eq = stay σ (unf s (ucons we)) v eq
ucons-go k σ (unf s (i64)) v eq = stay σ (unf s (i64)) v eq
ucons-go k σ (unf s (f32ty)) v eq = stay σ (unf s (f32ty)) v eq
ucons-go k σ (unf s (tensor wd ws)) v eq = stay σ (unf s (tensor wd ws)) v eq
ucons-go k σ (unf s (addi wx wy)) v eq = stay σ (unf s (addi wx wy)) v eq
ucons-go k σ (unf s (muli wx wy)) v eq = stay σ (unf s (muli wx wy)) v eq
ucons-go k σ (unf s (addt wt wu)) v eq = stay σ (unf s (addt wt wu)) v eq
ucons-go k σ (unf s (toi64 wt)) v eq = stay σ (unf s (toi64 wt)) v eq
ucons-go k σ (unf s (packi wx wy)) v eq = stay σ (unf s (packi wx wy)) v eq
ucons-go k σ (unf s (word wop wts)) v eq = stay σ (unf s (word wop wts)) v eq
ucons-go k σ (var wx) v eq = stay σ (var wx) v eq
ucons-go k σ (typ) v eq = stay σ (typ) v eq
ucons-go k σ (pi wq wA wB) v eq = stay σ (pi wq wA wB) v eq
ucons-go k σ (lam wq wA wt) v eq = stay σ (lam wq wA wt) v eq
ucons-go k σ (app wg wb) v eq = stay σ (app wg wb) v eq
ucons-go k σ (nat) v eq = stay σ (nat) v eq
ucons-go k σ (ze) v eq = stay σ (ze) v eq
ucons-go k σ (su wu) v eq = stay σ (su wu) v eq
ucons-go k σ (unit) v eq = stay σ (unit) v eq
ucons-go k σ (one) v eq = stay σ (one) v eq
ucons-go k σ (empty) v eq = stay σ (empty) v eq
ucons-go k σ (dty wi) v eq = stay σ (dty wi) v eq
ucons-go k σ (ctor wi wj) v eq = stay σ (ctor wi wj) v eq
ucons-go k σ (mData we wP wbs) v eq = stay σ (mData we wP wbs) v eq
ucons-go k σ (mNat we wP wz ws) v eq = stay σ (mNat we wP wz ws) v eq
ucons-go k σ (mEmp we wP) v eq = stay σ (mEmp we wP) v eq
ucons-go k σ (mUnit we wP wu) v eq = stay σ (mUnit we wP wu) v eq
ucons-go k σ (idt wA wa wb) v eq = stay σ (idt wA wa wb) v eq
ucons-go k σ (rfl) v eq = stay σ (rfl) v eq
ucons-go k σ (rwt we wP wt) v eq = stay σ (rwt we wP wt) v eq
ucons-go k σ (def wi) v eq = stay σ (def wi) v eq
ucons-go k σ (ann we wA) v eq = stay σ (ann we wA) v eq
ucons-go k σ (prod wA wB) v eq = stay σ (prod wA wB) v eq
ucons-go k σ (pair wa wb) v eq = stay σ (pair wa wb) v eq
ucons-go k σ (letp we wt) v eq = stay σ (letp we wt) v eq
ucons-go k σ (nu wF) v eq = stay σ (nu wF) v eq
ucons-go k σ (ucons we) v eq = stay σ (ucons we) v eq
ucons-go k σ (i64) v eq = stay σ (i64) v eq
ucons-go k σ (f32ty) v eq = stay σ (f32ty) v eq
ucons-go k σ (tensor wd ws) v eq = stay σ (tensor wd ws) v eq
ucons-go k σ (addi wx wy) v eq = stay σ (addi wx wy) v eq
ucons-go k σ (muli wx wy) v eq = stay σ (muli wx wy) v eq
ucons-go k σ (addt wt wu) v eq = stay σ (addt wt wu) v eq
ucons-go k σ (toi64 wt) v eq = stay σ (toi64 wt) v eq
ucons-go k σ (packi wx wy) v eq = stay σ (packi wx wy) v eq
ucons-go k σ (word wop wts) v eq = stay σ (word wop wts) v eq

byRefl : ∀ {n} (σ : Sig) (t v : Tm n) → ok t ≡ ok v → σ ⊢[ spec ] t ⇛* v
byRefl σ t v eq = subst (λ z → σ ⊢[ spec ] t ⇛* z) (ok-inj eq) ⇛*-refl

-- A pointwise reduction of arguments is a chain of word congruences.
-- ⇛-word is one parallel step, so each argument's ⇛* is replayed alone.
data OnlyWord {σ n} (op : WOp) : Tm n → Tm n → Set where
  ow-refl : ∀ {t} → OnlyWord {σ} op t t
  ow-step : ∀ {ts ts′ u}
    → σ ⊢[ spec ] ts ⇛L ts′
    → OnlyWord {σ} op (word op ts′) u
    → OnlyWord {σ} op (word op ts) u

ow-trans : ∀ {σ n} {op : WOp} {t u v : Tm n}
  → OnlyWord {σ} op t u → OnlyWord {σ} op u v → OnlyWord {σ} op t v
ow-trans ow-refl q = q
ow-trans (ow-step st r) q = ow-step st (ow-trans r q)

only* : ∀ {σ n} {op : WOp} {t u : Tm n}
  → OnlyWord {σ} op t u → σ ⊢[ spec ] t ⇛* u
only* ow-refl = ⇛*-refl
only* (ow-step st r) = ⇛*-step (⇛-word st) (only* r)

word-cong* : ∀ {σ n} {op : WOp} {ts ts′ : List (Tm n)}
  → σ ⊢[ spec ] ts ⇛L* ts′
  → σ ⊢[ spec ] word op ts ⇛* word op ts′
word-cong* {σ} {op = op} red = only* (go red)
  where
  pad : ∀ {ts ts′} (t : Tm _)
    → OnlyWord {σ} op (word op ts) (word op ts′)
    → OnlyWord {σ} op (word op (t ∷ ts)) (word op (t ∷ ts′))
  pad _ ow-refl = ow-refl
  pad t (ow-step st r) = ow-step (⇛L-∷ (⇛-refl t) st) (pad t r)

  headOW : ∀ {a a′} (as : List (Tm _))
    → σ ⊢[ spec ] a ⇛* a′
    → OnlyWord {σ} op (word op (a ∷ as)) (word op (a′ ∷ as))
  headOW _ ⇛*-refl = ow-refl
  headOW as (⇛*-step d r) = ow-step (⇛L-∷ d (⇛L-refl as)) (headOW as r)

  go : ∀ {ts ts′} → σ ⊢[ spec ] ts ⇛L* ts′
    → OnlyWord {σ} op (word op ts) (word op ts′)
  go ⇛L*-[] = ow-refl
  go (⇛L*-∷ {a′ = a′} {as = as} ra ras) =
    ow-trans (headOW as ra) (pad a′ (go ras))

-- Opaque outside this block so Productive does not unfold the
-- well-founded `go` proof.
abstract
  whnf-red : ∀ {n} k (σ : Sig) (t v : Tm n)
    → whnf k σ t ≡ ok v
    → σ ⊢[ spec ] t ⇛* v
  whnf-red k σ t v eq = go k (<-wellFounded k) σ t v eq
    where
    go : ∀ {n} k → Acc _<_ k → (σ : Sig) (t v : Tm n)
      → whnf k σ t ≡ ok v
      → σ ⊢[ spec ] t ⇛* v
    go zero _ σ t v ()
    go (suc k) (acc rs) σ (app f a) v eq with whnf k σ f in weq
    ... | fail _ = ⊥-elim (fail≢ok eq)
    ... | ok (lam q A t) with q
    go (suc k) (acc rs) σ (app f a) v eq | ok (lam q A t) | reuse with reuseWhnf k σ t a v eq
    go (suc k) (acc rs) σ (app f a) v eq | ok (lam q A t) | reuse | cbn eq′ =
      ⇛*-trans (app-star (go k (rs (n<1+n k)) σ f (lam reuse A t) weq))
        (⇛*-trans (⇛*-one (⇛-β (⇛-refl t) (⇛-refl a)))
                  (go k (rs (n<1+n k)) σ (inst t a) v eq′))
    go (suc k) (acc rs) σ (app f a) v eq | ok (lam q A t) | reuse | shared k′ a′ refl aeq beq =
      ⇛*-trans (app-star (go k (rs (n<1+n k)) σ f (lam reuse A t) weq))
        (⇛*-trans (⇛*-one (⇛-β (⇛-refl t) (⇛-refl a)))
          (⇛*-trans (⇛*-inst t (go (suc k′) (rs (n≤1+n (suc (suc k′)))) σ a a′ aeq))
                    (go k (rs (n<1+n k)) σ (inst t a′) v beq)))
    go (suc k) (acc rs) σ (app f a) v eq | ok (lam q A t) | affine =
      ⇛*-trans (app-star (go k (rs (n<1+n k)) σ f (lam affine A t) weq))
        (⇛*-trans (⇛*-one (⇛-β (⇛-refl t) (⇛-refl a)))
                  (go k (rs (n<1+n k)) σ (inst t a) v eq))
    go (suc k) (acc rs) σ (app f a) v eq | ok (lam q A t) | erased =
      ⇛*-trans (app-star (go k (rs (n<1+n k)) σ f (lam erased A t) weq))
        (⇛*-trans (⇛*-one (⇛-β (⇛-refl t) (⇛-refl a)))
                  (go k (rs (n<1+n k)) σ (inst t a) v eq))

    go (suc k) (acc rs) σ (app f a) v eq | ok (var wx) with go k (rs (n<1+n k)) σ f (var wx) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (typ) with go k (rs (n<1+n k)) σ f (typ) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (pi wq wA wB) with go k (rs (n<1+n k)) σ f (pi wq wA wB) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (app wg wb) with go k (rs (n<1+n k)) σ f (app wg wb) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (nat) with go k (rs (n<1+n k)) σ f (nat) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (ze) with go k (rs (n<1+n k)) σ f (ze) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (su wu) with go k (rs (n<1+n k)) σ f (su wu) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (unit) with go k (rs (n<1+n k)) σ f (unit) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (one) with go k (rs (n<1+n k)) σ f (one) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (empty) with go k (rs (n<1+n k)) σ f (empty) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (dty wi) with go k (rs (n<1+n k)) σ f (dty wi) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (ctor wi wj) with go k (rs (n<1+n k)) σ f (ctor wi wj) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (mData we wP wbs) with go k (rs (n<1+n k)) σ f (mData we wP wbs) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (mNat we wP wz ws) with go k (rs (n<1+n k)) σ f (mNat we wP wz ws) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (mEmp we wP) with go k (rs (n<1+n k)) σ f (mEmp we wP) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (mUnit we wP wu) with go k (rs (n<1+n k)) σ f (mUnit we wP wu) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (idt wA wa wb) with go k (rs (n<1+n k)) σ f (idt wA wa wb) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (rfl) with go k (rs (n<1+n k)) σ f (rfl) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (rwt we wP wt) with go k (rs (n<1+n k)) σ f (rwt we wP wt) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (def wi) with go k (rs (n<1+n k)) σ f (def wi) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (ann we wA) with go k (rs (n<1+n k)) σ f (ann we wA) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (prod wA wB) with go k (rs (n<1+n k)) σ f (prod wA wB) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (pair wa wb) with go k (rs (n<1+n k)) σ f (pair wa wb) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (letp we wt) with go k (rs (n<1+n k)) σ f (letp we wt) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (nu wF) with go k (rs (n<1+n k)) σ f (nu wF) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (unf ws wf) with go k (rs (n<1+n k)) σ f (unf ws wf) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (ucons we) with go k (rs (n<1+n k)) σ f (ucons we) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (i64) with go k (rs (n<1+n k)) σ f (i64) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (f32ty) with go k (rs (n<1+n k)) σ f (f32ty) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (tensor wd ws) with go k (rs (n<1+n k)) σ f (tensor wd ws) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (addi wx wy) with go k (rs (n<1+n k)) σ f (addi wx wy) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (muli wx wy) with go k (rs (n<1+n k)) σ f (muli wx wy) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (addt wt wu) with go k (rs (n<1+n k)) σ f (addt wt wu) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (toi64 wt) with go k (rs (n<1+n k)) σ f (toi64 wt) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (packi wx wy) with go k (rs (n<1+n k)) σ f (packi wx wy) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (app f a) v eq | ok (word wop wts) with go k (rs (n<1+n k)) σ f (word wop wts) weq | ok-inj eq
    ... | r | refl = app-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq with whnf k σ e in weq
    ... | fail _ = ⊥-elim (fail≢ok eq)
    ... | ok ze =
      ⇛*-trans (mNat-star (go k (rs (n<1+n k)) σ e ze weq))
        (⇛*-trans (⇛*-one (⇛-ιz (⇛-refl z)))
                  (go k (rs (n<1+n k)) σ z v eq))
    ... | ok (su u) =
      ⇛*-trans (mNat-star (go k (rs (n<1+n k)) σ e (su u) weq))
        (⇛*-trans (⇛*-one (⇛-ιs (⇛-refl u) (⇛-refl s)))
                  (go k (rs (n<1+n k)) σ (inst s u) v eq))

    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (var wx) with go k (rs (n<1+n k)) σ e (var wx) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (typ) with go k (rs (n<1+n k)) σ e (typ) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (pi wq wA wB) with go k (rs (n<1+n k)) σ e (pi wq wA wB) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (lam wq wA wt) with go k (rs (n<1+n k)) σ e (lam wq wA wt) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (app wg wb) with go k (rs (n<1+n k)) σ e (app wg wb) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (nat) with go k (rs (n<1+n k)) σ e (nat) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (unit) with go k (rs (n<1+n k)) σ e (unit) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (one) with go k (rs (n<1+n k)) σ e (one) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (empty) with go k (rs (n<1+n k)) σ e (empty) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (dty wi) with go k (rs (n<1+n k)) σ e (dty wi) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (ctor wi wj) with go k (rs (n<1+n k)) σ e (ctor wi wj) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (mData we wP wbs) with go k (rs (n<1+n k)) σ e (mData we wP wbs) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (mNat we wP wz ws) with go k (rs (n<1+n k)) σ e (mNat we wP wz ws) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (mEmp we wP) with go k (rs (n<1+n k)) σ e (mEmp we wP) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (mUnit we wP wu) with go k (rs (n<1+n k)) σ e (mUnit we wP wu) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (idt wA wa wb) with go k (rs (n<1+n k)) σ e (idt wA wa wb) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (rfl) with go k (rs (n<1+n k)) σ e (rfl) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (rwt we wP wt) with go k (rs (n<1+n k)) σ e (rwt we wP wt) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (def wi) with go k (rs (n<1+n k)) σ e (def wi) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (ann we wA) with go k (rs (n<1+n k)) σ e (ann we wA) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (prod wA wB) with go k (rs (n<1+n k)) σ e (prod wA wB) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (pair wa wb) with go k (rs (n<1+n k)) σ e (pair wa wb) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (letp we wt) with go k (rs (n<1+n k)) σ e (letp we wt) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (nu wF) with go k (rs (n<1+n k)) σ e (nu wF) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (unf ws wf) with go k (rs (n<1+n k)) σ e (unf ws wf) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (ucons we) with go k (rs (n<1+n k)) σ e (ucons we) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (i64) with go k (rs (n<1+n k)) σ e (i64) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (f32ty) with go k (rs (n<1+n k)) σ e (f32ty) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (tensor wd ws) with go k (rs (n<1+n k)) σ e (tensor wd ws) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (addi wx wy) with go k (rs (n<1+n k)) σ e (addi wx wy) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (muli wx wy) with go k (rs (n<1+n k)) σ e (muli wx wy) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (addt wt wu) with go k (rs (n<1+n k)) σ e (addt wt wu) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (toi64 wt) with go k (rs (n<1+n k)) σ e (toi64 wt) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (packi wx wy) with go k (rs (n<1+n k)) σ e (packi wx wy) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mNat e P z s) v eq | ok (word wop wts) with go k (rs (n<1+n k)) σ e (word wop wts) weq | ok-inj eq
    ... | r | refl = mNat-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq with whnf k σ e in weq
    ... | fail _ = ⊥-elim (fail≢ok eq)
    ... | ok one =
      ⇛*-trans (mUnit-star (go k (rs (n<1+n k)) σ e one weq))
        (⇛*-trans (⇛*-one (⇛-ιtt (⇛-refl u)))
                  (go k (rs (n<1+n k)) σ u v eq))

    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (var wx) with go k (rs (n<1+n k)) σ e (var wx) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (typ) with go k (rs (n<1+n k)) σ e (typ) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (pi wq wA wB) with go k (rs (n<1+n k)) σ e (pi wq wA wB) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (lam wq wA wt) with go k (rs (n<1+n k)) σ e (lam wq wA wt) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (app wg wb) with go k (rs (n<1+n k)) σ e (app wg wb) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (nat) with go k (rs (n<1+n k)) σ e (nat) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (ze) with go k (rs (n<1+n k)) σ e (ze) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (su wu) with go k (rs (n<1+n k)) σ e (su wu) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (unit) with go k (rs (n<1+n k)) σ e (unit) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (empty) with go k (rs (n<1+n k)) σ e (empty) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (dty wi) with go k (rs (n<1+n k)) σ e (dty wi) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (ctor wi wj) with go k (rs (n<1+n k)) σ e (ctor wi wj) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (mData we wP wbs) with go k (rs (n<1+n k)) σ e (mData we wP wbs) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (mNat we wP wz ws) with go k (rs (n<1+n k)) σ e (mNat we wP wz ws) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (mEmp we wP) with go k (rs (n<1+n k)) σ e (mEmp we wP) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (mUnit we wP wu) with go k (rs (n<1+n k)) σ e (mUnit we wP wu) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (idt wA wa wb) with go k (rs (n<1+n k)) σ e (idt wA wa wb) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (rfl) with go k (rs (n<1+n k)) σ e (rfl) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (rwt we wP wt) with go k (rs (n<1+n k)) σ e (rwt we wP wt) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (def wi) with go k (rs (n<1+n k)) σ e (def wi) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (ann we wA) with go k (rs (n<1+n k)) σ e (ann we wA) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (prod wA wB) with go k (rs (n<1+n k)) σ e (prod wA wB) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (pair wa wb) with go k (rs (n<1+n k)) σ e (pair wa wb) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (letp we wt) with go k (rs (n<1+n k)) σ e (letp we wt) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (nu wF) with go k (rs (n<1+n k)) σ e (nu wF) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (unf ws wf) with go k (rs (n<1+n k)) σ e (unf ws wf) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (ucons we) with go k (rs (n<1+n k)) σ e (ucons we) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (i64) with go k (rs (n<1+n k)) σ e (i64) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (f32ty) with go k (rs (n<1+n k)) σ e (f32ty) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (tensor wd ws) with go k (rs (n<1+n k)) σ e (tensor wd ws) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (addi wx wy) with go k (rs (n<1+n k)) σ e (addi wx wy) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (muli wx wy) with go k (rs (n<1+n k)) σ e (muli wx wy) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (addt wt wu) with go k (rs (n<1+n k)) σ e (addt wt wu) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (toi64 wt) with go k (rs (n<1+n k)) σ e (toi64 wt) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (packi wx wy) with go k (rs (n<1+n k)) σ e (packi wx wy) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mUnit e P u) v eq | ok (word wop wts) with go k (rs (n<1+n k)) σ e (word wop wts) weq | ok-inj eq
    ... | r | refl = mUnit-star r
    go (suc k) (acc rs) σ (mEmp e P) v eq with whnf k σ e in weq
    ... | fail _ = ⊥-elim (fail≢ok eq)
    ... | ok e′ with go k (rs (n<1+n k)) σ e e′ weq | ok-inj eq
    ... | r | refl = mEmp-star r
    go (suc k) (acc rs) σ (mData e P bs) v eq with whnf k σ e in weq
    ... | fail _ = ⊥-elim (fail≢ok eq)
    ... | ok e′ with go k (rs (n<1+n k)) σ e e′ weq
    ... | r with ctorSpine e′ in ceq
    ... | nothing with ok-inj eq
    ... | refl = mData-star r
    go (suc k) (acc rs) σ (mData e P bs) v eq | ok e′ | r | just (di , ci , args) with lookupList bs ci in leq
    ... | fail _ with ok-inj eq
    ... | refl = mData-star r
    go (suc k) (acc rs) σ (mData e P bs) v eq | ok e′ | r | just (di , ci , args) | ok b
      with ctorSpine-just ceq
    ... | sp =
      ⇛*-trans (mData-star r)
        (⇛*-step (⇛-ιdata sp leq (⇛L-refl args) (⇛-refl b))
                 (go k (rs (n<1+n k)) σ (appsFrom b args) v eq))
    go (suc k) (acc rs) σ (letp e t) v eq with whnf k σ e in weq
    ... | fail _ = ⊥-elim (fail≢ok eq)
    ... | ok (pair a b) =
      ⇛*-trans (letp-star (go k (rs (n<1+n k)) σ e (pair a b) weq))
        (⇛*-trans (⇛*-one (⇛-ιletp (⇛-refl a) (⇛-refl b) (⇛-refl t)))
                  (go k (rs (n<1+n k)) σ (inst₂ t a b) v eq))

    go (suc k) (acc rs) σ (letp e t) v eq | ok (var wx) with go k (rs (n<1+n k)) σ e (var wx) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (typ) with go k (rs (n<1+n k)) σ e (typ) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (pi wq wA wB) with go k (rs (n<1+n k)) σ e (pi wq wA wB) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (lam wq wA wt) with go k (rs (n<1+n k)) σ e (lam wq wA wt) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (app wg wb) with go k (rs (n<1+n k)) σ e (app wg wb) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (nat) with go k (rs (n<1+n k)) σ e (nat) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (ze) with go k (rs (n<1+n k)) σ e (ze) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (su wu) with go k (rs (n<1+n k)) σ e (su wu) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (unit) with go k (rs (n<1+n k)) σ e (unit) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (one) with go k (rs (n<1+n k)) σ e (one) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (empty) with go k (rs (n<1+n k)) σ e (empty) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (dty wi) with go k (rs (n<1+n k)) σ e (dty wi) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (ctor wi wj) with go k (rs (n<1+n k)) σ e (ctor wi wj) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (mData we wP wbs) with go k (rs (n<1+n k)) σ e (mData we wP wbs) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (mNat we wP wz ws) with go k (rs (n<1+n k)) σ e (mNat we wP wz ws) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (mEmp we wP) with go k (rs (n<1+n k)) σ e (mEmp we wP) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (mUnit we wP wu) with go k (rs (n<1+n k)) σ e (mUnit we wP wu) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (idt wA wa wb) with go k (rs (n<1+n k)) σ e (idt wA wa wb) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (rfl) with go k (rs (n<1+n k)) σ e (rfl) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (rwt we wP wt) with go k (rs (n<1+n k)) σ e (rwt we wP wt) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (def wi) with go k (rs (n<1+n k)) σ e (def wi) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (ann we wA) with go k (rs (n<1+n k)) σ e (ann we wA) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (prod wA wB) with go k (rs (n<1+n k)) σ e (prod wA wB) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (letp we wt) with go k (rs (n<1+n k)) σ e (letp we wt) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (nu wF) with go k (rs (n<1+n k)) σ e (nu wF) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (unf ws wf) with go k (rs (n<1+n k)) σ e (unf ws wf) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (ucons we) with go k (rs (n<1+n k)) σ e (ucons we) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (i64) with go k (rs (n<1+n k)) σ e (i64) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (f32ty) with go k (rs (n<1+n k)) σ e (f32ty) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (tensor wd ws) with go k (rs (n<1+n k)) σ e (tensor wd ws) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (addi wx wy) with go k (rs (n<1+n k)) σ e (addi wx wy) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (muli wx wy) with go k (rs (n<1+n k)) σ e (muli wx wy) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (addt wt wu) with go k (rs (n<1+n k)) σ e (addt wt wu) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (toi64 wt) with go k (rs (n<1+n k)) σ e (toi64 wt) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (packi wx wy) with go k (rs (n<1+n k)) σ e (packi wx wy) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (letp e t) v eq | ok (word wop wts) with go k (rs (n<1+n k)) σ e (word wop wts) weq | ok-inj eq
    ... | r | refl = letp-star r
    go (suc k) (acc rs) σ (def i) v eq with lookupDef σ i in leq
    ... | fail _ = byRefl σ (def i) v eq
    ... | ok d =
      ⇛*-step (⇛-δ leq (allowed-spec (Def.dmode d)))
              (go k (rs (n<1+n k)) σ (closed (Def.dbody d)) v eq)
    go (suc k) (acc rs) σ (ann e A) v eq =
      ⇛*-step (⇛-ann (⇛-refl e)) (go k (rs (n<1+n k)) σ e v eq)
    go (suc k) (acc rs) σ (ucons e) v eq with whnf k σ e in weq
    ... | fail _ = ⊥-elim (fail≢ok eq)
    ... | ok e′ with go k (rs (n<1+n k)) σ e e′ weq
    ... | r = ⇛*-trans (ucons-star r) (ucons-go k σ e′ v eq)

    go (suc k) (acc rs) σ (var wx) v eq = byRefl σ (var wx) v eq
    go (suc k) (acc rs) σ (typ) v eq = byRefl σ (typ) v eq
    go (suc k) (acc rs) σ (pi wq wA wB) v eq = byRefl σ (pi wq wA wB) v eq
    go (suc k) (acc rs) σ (lam wq wA wt) v eq = byRefl σ (lam wq wA wt) v eq
    go (suc k) (acc rs) σ (nat) v eq = byRefl σ (nat) v eq
    go (suc k) (acc rs) σ (ze) v eq = byRefl σ (ze) v eq
    go (suc k) (acc rs) σ (su wu) v eq = byRefl σ (su wu) v eq
    go (suc k) (acc rs) σ (unit) v eq = byRefl σ (unit) v eq
    go (suc k) (acc rs) σ (one) v eq = byRefl σ (one) v eq
    go (suc k) (acc rs) σ (empty) v eq = byRefl σ (empty) v eq
    go (suc k) (acc rs) σ (dty wi) v eq = byRefl σ (dty wi) v eq
    go (suc k) (acc rs) σ (ctor wi wj) v eq = byRefl σ (ctor wi wj) v eq
    go (suc k) (acc rs) σ (idt wA wa wb) v eq = byRefl σ (idt wA wa wb) v eq
    go (suc k) (acc rs) σ (rfl) v eq = byRefl σ (rfl) v eq
    go (suc k) (acc rs) σ (rwt we wP wt) v eq = byRefl σ (rwt we wP wt) v eq
    go (suc k) (acc rs) σ (prod wA wB) v eq = byRefl σ (prod wA wB) v eq
    go (suc k) (acc rs) σ (pair wa wb) v eq = byRefl σ (pair wa wb) v eq
    go (suc k) (acc rs) σ (nu wF) v eq = byRefl σ (nu wF) v eq
    go (suc k) (acc rs) σ (unf ws wf) v eq = byRefl σ (unf ws wf) v eq
    go (suc k) (acc rs) σ (i64) v eq = byRefl σ (i64) v eq
    go (suc k) (acc rs) σ (f32ty) v eq = byRefl σ (f32ty) v eq
    go (suc k) (acc rs) σ (tensor wd ws) v eq = byRefl σ (tensor wd ws) v eq
    go (suc k) (acc rs) σ (addi wx wy) v eq = byRefl σ (addi wx wy) v eq
    go (suc k) (acc rs) σ (muli wx wy) v eq = byRefl σ (muli wx wy) v eq
    go (suc k) (acc rs) σ (addt wt wu) v eq = byRefl σ (addt wt wu) v eq
    go (suc k) (acc rs) σ (toi64 wt) v eq = byRefl σ (toi64 wt) v eq
    go (suc k) (acc rs) σ (packi wx wy) v eq = byRefl σ (packi wx wy) v eq
    go {n} (suc k) (acc rs) σ (word op ts) v eq = word-red eq
      where
      -- whnfList shares the outer fuel, so each recursive go is on that fuel.
      listRed : ∀ {m} {us us′ : List (Tm n)}
        → Acc _<_ m
        → whnfList m σ us ≡ ok us′
        → σ ⊢[ spec ] us ⇛L* us′
      listRed {zero} {[]} {[]} _ refl = ⇛L*-[]
      listRed {zero} {_ ∷ _} _ ()
      listRed {suc m} {[]} {[]} _ refl = ⇛L*-[]
      listRed {suc m} {u ∷ us} {us′} (acc rec) eq′ with whnf m σ u in teq
      ... | fail _ = ⊥-elim (fail≢ok eq′)
      ... | ok u′ with whnfList m σ us in leq
      ... | fail _ = ⊥-elim (fail≢ok eq′)
      ... | ok tail rewrite sym (ok-inj eq′) =
          ⇛L*-∷ (go m (rec (n<1+n m)) σ u u′ teq) (listRed {m} {us} {tail} (rec (n<1+n m)) leq)

      -- eq′ stays an argument of both withs. A with abstracts its
      -- scrutinee only from the goal and from the types of arguments, so a
      -- proof closed over from an outer where would keep the unreduced case.
      word-red : whnf (suc k) σ (word op ts) ≡ ok v → σ ⊢[ spec ] word op ts ⇛* v
      word-red eq′ with whnfList k σ ts in leq
      ... | fail _ = ⊥-elim (fail≢ok eq′)
      ... | ok ts′ with wordStep op ts′ in seq
      ... | nothing =
          subst (λ z → σ ⊢[ spec ] word op ts ⇛* z) (ok-inj eq′)
            (word-cong* (listRed {k} {ts} {ts′} (rs (n<1+n k)) leq))
      ... | just r =
          ⇛*-trans (word-cong* (listRed {k} {ts} {ts′} (rs (n<1+n k)) leq))
            (⇛*-trans (⇛*-one (⇛-wred (⇛L-refl ts′) seq))
                      (go k (rs (n<1+n k)) σ r v eq′))


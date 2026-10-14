------------------------------------------------------------------------
-- The ⊢ fragment as a predicate on terms: the constructors ⊢ has rules
-- for. ν, unfold, and uncons are in it. I64 / F32 / Tensor are outside.
-- Closed under renaming and substitution, so under everything Check.whnf
-- does to a fragment term over a fragment signature.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Frag where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Env
open import Muro.Spine

-- An unfold the step can read: the function is a λ whose body is a
-- pair, or it is the identity and the seed is already a pair.
data UShape {n} : Tm n → Tm n → Set where
  us-pair : ∀ {s q A h t} → UShape s (lam q A (pair h t))
  us-id   : ∀ {a b q A} → UShape (pair a b) (lam q A (var zero))
  -- The step is already the pair uncons reads.
  us-step : ∀ {s h t} → UShape s (pair h t)

-- Fragment unfolds: the λ of a pair, whose uncons wraps, and the pair,
-- whose uncons reads. The identity λ's tail is not one of these.
data FShape {n} : Tm n → Tm n → Set where
  fs-pair : ∀ {s q A h t} → FShape s (lam q A (pair h t))
  fs-step : ∀ {s h t} → FShape s (pair h t)

data Frag {n} : Tm n → Set
data FragL {n} : List (Tm n) → Set

data Frag where
  f-var   : ∀ {x} → Frag (var x)
  f-typ   : Frag typ
  f-pi    : ∀ {q A B} → Frag A → Frag B → Frag (pi q A B)
  f-lam   : ∀ {q A t} → Frag A → Frag t → Frag (lam q A t)
  f-app   : ∀ {f a} → Frag f → Frag a → Frag (app f a)
  f-nat   : Frag nat
  f-ze    : Frag ze
  f-su    : ∀ {t} → Frag t → Frag (su t)
  f-unit  : Frag unit
  f-one   : Frag one
  f-empty : Frag empty
  f-dty   : ∀ {i} → Frag (dty i)
  f-ctor  : ∀ {i j} → Frag (ctor i j)
  f-mData : ∀ {e P bs} → Frag e → Frag P → FragL bs → Frag (mData e P bs)
  f-mNat  : ∀ {e P z s} → Frag e → Frag P → Frag z → Frag s → Frag (mNat e P z s)
  f-mEmp  : ∀ {e P} → Frag e → Frag P → Frag (mEmp e P)
  f-mUnit : ∀ {e P u} → Frag e → Frag P → Frag u → Frag (mUnit e P u)
  f-idt   : ∀ {A a b} → Frag A → Frag a → Frag b → Frag (idt A a b)
  f-rfl   : Frag rfl
  f-rwt   : ∀ {e P t} → Frag e → Frag P → Frag t → Frag (rwt e P t)
  f-def   : ∀ {i} → Frag (def i)
  f-ann   : ∀ {e A} → Frag e → Frag A → Frag (ann e A)
  f-prod  : ∀ {A B} → Frag A → Frag B → Frag (prod A B)
  f-pair  : ∀ {a b} → Frag a → Frag b → Frag (pair a b)
  f-letp  : ∀ {e t} → Frag e → Frag t → Frag (letp e t)
  f-nu    : ∀ {F} → Frag F → Frag (nu F)
  f-unf   : ∀ {s f} → Frag s → Frag f → FShape s f → Frag (unf s f)
  f-ucons : ∀ {s} → Frag s → Frag (ucons s)

data FragL where
  fl-[] : FragL []
  fl-∷  : ∀ {t ts} → Frag t → FragL ts → FragL (t ∷ ts)

UShape-ren : ∀ {n m} (ρ : Fin n → Fin m) {s f} → UShape s f → UShape (ren ρ s) (ren ρ f)
UShape-ren ρ us-pair = us-pair
UShape-ren ρ us-id = us-id
UShape-ren ρ us-step = us-step

UShape-unren : ∀ {n m} (ρ : Fin n → Fin m) (s f : Tm n)
  → UShape (ren ρ s) (ren ρ f) → UShape s f
UShape-unren ρ _ (lam _ _ (pair _ _)) us-pair = us-pair
UShape-unren ρ (pair _ _) (lam _ _ (var zero)) us-id = us-id
UShape-unren ρ _ (pair _ _) us-step = us-step

UShape-sub : ∀ {n k} {τ : Fin n → Tm k} {s f} → UShape s f → UShape (sub τ s) (sub τ f)
UShape-sub us-pair = us-pair
UShape-sub us-id = us-id
UShape-sub us-step = us-step

FShape-ren : ∀ {n m} (ρ : Fin n → Fin m) {s f} → FShape s f → FShape (ren ρ s) (ren ρ f)
FShape-ren ρ fs-pair = fs-pair
FShape-ren ρ fs-step = fs-step

FShape-unren : ∀ {n m} (ρ : Fin n → Fin m) (s f : Tm n)
  → FShape (ren ρ s) (ren ρ f) → FShape s f
FShape-unren ρ _ (lam _ _ (pair _ _)) fs-pair = fs-pair
FShape-unren ρ _ (pair _ _) fs-step = fs-step

FShape-sub : ∀ {n k} {τ : Fin n → Tm k} {s f} → FShape s f → FShape (sub τ s) (sub τ f)
FShape-sub fs-pair = fs-pair
FShape-sub fs-step = fs-step

------------------------------------------------------------------------
-- Closure.
------------------------------------------------------------------------

Frag-ren : ∀ {n k} (ρ : Fin n → Fin k) {t : Tm n} → Frag t → Frag (ren ρ t)
FragL-ren : ∀ {n k} (ρ : Fin n → Fin k) {ts : List (Tm n)} → FragL ts → FragL (renList ρ ts)

Frag-ren ρ f-var = f-var
Frag-ren ρ f-typ = f-typ
Frag-ren ρ (f-pi A B) = f-pi (Frag-ren ρ A) (Frag-ren (lift ρ) B)
Frag-ren ρ (f-lam A t) = f-lam (Frag-ren ρ A) (Frag-ren (lift ρ) t)
Frag-ren ρ (f-app f a) = f-app (Frag-ren ρ f) (Frag-ren ρ a)
Frag-ren ρ f-nat = f-nat
Frag-ren ρ f-ze = f-ze
Frag-ren ρ (f-su t) = f-su (Frag-ren ρ t)
Frag-ren ρ f-unit = f-unit
Frag-ren ρ f-one = f-one
Frag-ren ρ f-empty = f-empty
Frag-ren ρ f-dty = f-dty
Frag-ren ρ f-ctor = f-ctor
Frag-ren ρ (f-mData e P bs) = f-mData (Frag-ren ρ e) (Frag-ren (lift ρ) P) (FragL-ren ρ bs)
Frag-ren ρ (f-mNat e P z s) =
  f-mNat (Frag-ren ρ e) (Frag-ren (lift ρ) P) (Frag-ren ρ z) (Frag-ren (lift ρ) s)
Frag-ren ρ (f-mEmp e P) = f-mEmp (Frag-ren ρ e) (Frag-ren (lift ρ) P)
Frag-ren ρ (f-mUnit e P u) = f-mUnit (Frag-ren ρ e) (Frag-ren (lift ρ) P) (Frag-ren ρ u)
Frag-ren ρ (f-idt A a b) = f-idt (Frag-ren ρ A) (Frag-ren ρ a) (Frag-ren ρ b)
Frag-ren ρ f-rfl = f-rfl
Frag-ren ρ (f-rwt e P t) = f-rwt (Frag-ren ρ e) (Frag-ren (lift ρ) P) (Frag-ren ρ t)
Frag-ren ρ f-def = f-def
Frag-ren ρ (f-ann e A) = f-ann (Frag-ren ρ e) (Frag-ren ρ A)
Frag-ren ρ (f-prod A B) = f-prod (Frag-ren ρ A) (Frag-ren ρ B)
Frag-ren ρ (f-pair a b) = f-pair (Frag-ren ρ a) (Frag-ren ρ b)
Frag-ren ρ (f-letp e t) = f-letp (Frag-ren ρ e) (Frag-ren (lift (lift ρ)) t)
Frag-ren ρ (f-nu F) = f-nu (Frag-ren (lift ρ) F)
Frag-ren ρ (f-unf s f sh) = f-unf (Frag-ren ρ s) (Frag-ren ρ f) (FShape-ren ρ sh)
Frag-ren ρ (f-ucons s) = f-ucons (Frag-ren ρ s)

FragL-ren ρ fl-[] = fl-[]
FragL-ren ρ (fl-∷ t ts) = fl-∷ (Frag-ren ρ t) (FragL-ren ρ ts)

Frag-wk : ∀ {n} {t : Tm n} → Frag t → Frag (wk t)
Frag-wk = Frag-ren suc

-- The fragment does not look at variables, so it is also closed under
-- un-renaming: what Soundness needs of strengthen₂.
Frag-unren : ∀ {n k} (ρ : Fin n → Fin k) (t : Tm n) → Frag (ren ρ t) → Frag t
FragL-unren : ∀ {n k} (ρ : Fin n → Fin k) (ts : List (Tm n)) → FragL (renList ρ ts) → FragL ts
Frag-unren ρ (var _) f-var = f-var
Frag-unren ρ typ f-typ = f-typ
Frag-unren ρ (pi q A B) (f-pi FA FB) = f-pi (Frag-unren ρ A FA) (Frag-unren (lift ρ) B FB)
Frag-unren ρ (lam q A t) (f-lam FA Ft) = f-lam (Frag-unren ρ A FA) (Frag-unren (lift ρ) t Ft)
Frag-unren ρ (app f a) (f-app Ff Fa) = f-app (Frag-unren ρ f Ff) (Frag-unren ρ a Fa)
Frag-unren ρ nat f-nat = f-nat
Frag-unren ρ ze f-ze = f-ze
Frag-unren ρ (su t) (f-su Ft) = f-su (Frag-unren ρ t Ft)
Frag-unren ρ unit f-unit = f-unit
Frag-unren ρ one f-one = f-one
Frag-unren ρ empty f-empty = f-empty
Frag-unren ρ (dty _) f-dty = f-dty
Frag-unren ρ (ctor _ _) f-ctor = f-ctor
Frag-unren ρ (mData e P bs) (f-mData Fe FP Fbs) =
  f-mData (Frag-unren ρ e Fe) (Frag-unren (lift ρ) P FP) (FragL-unren ρ bs Fbs)
Frag-unren ρ (mNat e P z s) (f-mNat Fe FP Fz Fs) =
  f-mNat (Frag-unren ρ e Fe) (Frag-unren (lift ρ) P FP) (Frag-unren ρ z Fz) (Frag-unren (lift ρ) s Fs)
Frag-unren ρ (mEmp e P) (f-mEmp Fe FP) = f-mEmp (Frag-unren ρ e Fe) (Frag-unren (lift ρ) P FP)
Frag-unren ρ (mUnit e P u) (f-mUnit Fe FP Fu) =
  f-mUnit (Frag-unren ρ e Fe) (Frag-unren (lift ρ) P FP) (Frag-unren ρ u Fu)
Frag-unren ρ (idt A a b) (f-idt FA Fa Fb) = f-idt (Frag-unren ρ A FA) (Frag-unren ρ a Fa) (Frag-unren ρ b Fb)
Frag-unren ρ rfl f-rfl = f-rfl
Frag-unren ρ (rwt e P t) (f-rwt Fe FP Ft) =
  f-rwt (Frag-unren ρ e Fe) (Frag-unren (lift ρ) P FP) (Frag-unren ρ t Ft)
Frag-unren ρ (def _) f-def = f-def
Frag-unren ρ (ann e A) (f-ann Fe FA) = f-ann (Frag-unren ρ e Fe) (Frag-unren ρ A FA)
Frag-unren ρ (prod A B) (f-prod FA FB) = f-prod (Frag-unren ρ A FA) (Frag-unren ρ B FB)
Frag-unren ρ (pair a b) (f-pair Fa Fb) = f-pair (Frag-unren ρ a Fa) (Frag-unren ρ b Fb)
Frag-unren ρ (letp e t) (f-letp Fe Ft) = f-letp (Frag-unren ρ e Fe) (Frag-unren (lift (lift ρ)) t Ft)
Frag-unren ρ (nu F) (f-nu FF) = f-nu (Frag-unren (lift ρ) F FF)
Frag-unren ρ (unf s f) (f-unf Fs Ff sh) =
  f-unf (Frag-unren ρ s Fs) (Frag-unren ρ f Ff) (FShape-unren ρ s f sh)
Frag-unren ρ (ucons s) (f-ucons Fs) = f-ucons (Frag-unren ρ s Fs)
FragL-unren ρ [] fl-[] = fl-[]
FragL-unren ρ (t ∷ ts) (fl-∷ Ft Fts) = fl-∷ (Frag-unren ρ t Ft) (FragL-unren ρ ts Fts)

Frag-closed : ∀ {n} {t : Tm 0} → Frag t → Frag (closed {n} t)
Frag-closed = Frag-ren fromZero

-- A substitution into the fragment.
FragS : ∀ {n k} → (Fin n → Tm k) → Set
FragS τ = ∀ x → Frag (τ x)

FragS-lifts : ∀ {n k} {τ : Fin n → Tm k} → FragS τ → FragS (lifts τ)
FragS-lifts s zero = f-var
FragS-lifts s (suc x) = Frag-wk (s x)

Frag-sub : ∀ {n k} {τ : Fin n → Tm k} → FragS τ → {t : Tm n} → Frag t → Frag (sub τ t)
FragL-sub : ∀ {n k} {τ : Fin n → Tm k} → FragS τ → {ts : List (Tm n)} → FragL ts → FragL (subList τ ts)

Frag-sub s (f-var {x}) = s x
Frag-sub s f-typ = f-typ
Frag-sub s (f-pi A B) = f-pi (Frag-sub s A) (Frag-sub (FragS-lifts s) B)
Frag-sub s (f-lam A t) = f-lam (Frag-sub s A) (Frag-sub (FragS-lifts s) t)
Frag-sub s (f-app f a) = f-app (Frag-sub s f) (Frag-sub s a)
Frag-sub s f-nat = f-nat
Frag-sub s f-ze = f-ze
Frag-sub s (f-su t) = f-su (Frag-sub s t)
Frag-sub s f-unit = f-unit
Frag-sub s f-one = f-one
Frag-sub s f-empty = f-empty
Frag-sub s f-dty = f-dty
Frag-sub s f-ctor = f-ctor
Frag-sub s (f-mData e P bs) = f-mData (Frag-sub s e) (Frag-sub (FragS-lifts s) P) (FragL-sub s bs)
Frag-sub s (f-mNat e P z s′) =
  f-mNat (Frag-sub s e) (Frag-sub (FragS-lifts s) P) (Frag-sub s z) (Frag-sub (FragS-lifts s) s′)
Frag-sub s (f-mEmp e P) = f-mEmp (Frag-sub s e) (Frag-sub (FragS-lifts s) P)
Frag-sub s (f-mUnit e P u) = f-mUnit (Frag-sub s e) (Frag-sub (FragS-lifts s) P) (Frag-sub s u)
Frag-sub s (f-idt A a b) = f-idt (Frag-sub s A) (Frag-sub s a) (Frag-sub s b)
Frag-sub s f-rfl = f-rfl
Frag-sub s (f-rwt e P t) = f-rwt (Frag-sub s e) (Frag-sub (FragS-lifts s) P) (Frag-sub s t)
Frag-sub s f-def = f-def
Frag-sub s (f-ann e A) = f-ann (Frag-sub s e) (Frag-sub s A)
Frag-sub s (f-prod A B) = f-prod (Frag-sub s A) (Frag-sub s B)
Frag-sub s (f-pair a b) = f-pair (Frag-sub s a) (Frag-sub s b)
Frag-sub s (f-letp e t) = f-letp (Frag-sub s e) (Frag-sub (FragS-lifts (FragS-lifts s)) t)
Frag-sub s (f-nu F) = f-nu (Frag-sub (FragS-lifts s) F)
Frag-sub s (f-unf u f sh) = f-unf (Frag-sub s u) (Frag-sub s f) (FShape-sub sh)
Frag-sub s (f-ucons u) = f-ucons (Frag-sub s u)

FragL-sub s fl-[] = fl-[]
FragL-sub s (fl-∷ t ts) = fl-∷ (Frag-sub s t) (FragL-sub s ts)

FragS-instσ : ∀ {n} {a : Tm n} → Frag a → FragS (instσ a)
FragS-instσ Fa zero = Fa
FragS-instσ Fa (suc x) = f-var

Frag-inst : ∀ {n} {t : Tm (ℕ.suc n)} {a} → Frag t → Frag a → Frag (inst t a)
Frag-inst Ft Fa = Frag-sub (FragS-instσ Fa) Ft

FragS-motSucσ : ∀ {n} → FragS (motSucσ {n})
FragS-motSucσ zero = f-su f-var
FragS-motSucσ (suc x) = f-var

Frag-motSuc : ∀ {n} {P : Tm (ℕ.suc n)} → Frag P → Frag (motSuc P)
Frag-motSuc = Frag-sub FragS-motSucσ

Frag-appsFrom : ∀ {n} {h : Tm n} {as} → Frag h → FragL as → Frag (appsFrom h as)
Frag-appsFrom Fh fl-[] = Fh
Frag-appsFrom Fh (fl-∷ Fa Fas) = Frag-appsFrom (f-app Fh Fa) Fas

FragL-++ : ∀ {n} {as bs : List (Tm n)} → FragL as → FragL bs → FragL (as ++ bs)
FragL-++ fl-[] G = G
FragL-++ (fl-∷ F Fs) G = fl-∷ F (FragL-++ Fs G)

-- Reading a spine off a fragment term.
Frag-Spine : ∀ {n} {h : Tm n} {as e} → Spine h as e → Frag e → Frag h × FragL as
Frag-Spine sp-[] Fe = Fe , fl-[]
Frag-Spine (sp-snoc sp) (f-app Ff Fa) with Frag-Spine sp Ff
... | Fh , Fas = Fh , FragL-++ Fas (fl-∷ Fa fl-[])

FragL-lookup : ∀ {n} {bs : List (Tm n)} {k b} → FragL bs → lookupList bs k ≡ ok b → Frag b
FragL-lookup {k = ℕ.zero} (fl-∷ F _) refl = F
FragL-lookup {k = ℕ.suc k} (fl-∷ _ Fs) eq = FragL-lookup Fs eq

------------------------------------------------------------------------
-- A signature in the fragment: every def type and body, every
-- constructor type, every index type.
------------------------------------------------------------------------

data FragIdxs : List (Qty × Tm 0) → Set where
  fi-[] : FragIdxs []
  fi-∷  : ∀ {q T ixs} → Frag T → FragIdxs ixs → FragIdxs ((q , T) ∷ ixs)

data FragCtors : List Ctor → Set where
  fc-[] : FragCtors []
  fc-∷  : ∀ {c cs} → Frag (Ctor.ctype c) → FragCtors cs → FragCtors (c ∷ cs)

record FragSig (σ : Sig) : Set where
  field
    defs  : ∀ i d → lookupDef σ i ≡ ok d → Frag (Def.dtype d) × Frag (Def.dbody d)
    datas : ∀ i d → lookupData σ i ≡ ok d → FragIdxs (DataDecl.idxs d) × FragCtors (DataDecl.ctors d)

FragCtors-lookup : ∀ {cs j c} → FragCtors cs → lookupList cs j ≡ ok c → Frag (Ctor.ctype c)
FragCtors-lookup {j = ℕ.zero} (fc-∷ F _) refl = F
FragCtors-lookup {j = ℕ.suc j} (fc-∷ _ Fs) eq = FragCtors-lookup Fs eq

Frag-dtyType : ∀ {n} qs {ixs} → FragIdxs ixs → Frag (dtyType {n} qs ixs)
Frag-dtyType [] fi-[] = f-typ
Frag-dtyType (q ∷ qs) fi = f-pi f-typ (Frag-dtyType qs fi)
Frag-dtyType [] (fi-∷ F fi) = f-pi (Frag-closed F) (Frag-dtyType [] fi)

-- A context in the fragment.
FragCtx : ∀ {n} → Ctx n → Set
FragCtx Γ = ∀ x → Frag (typOf Γ x)

Frag-inst₂ : ∀ {n} {t : Tm (ℕ.suc (ℕ.suc n))} {a b} → Frag t → Frag a → Frag b → Frag (inst₂ t a b)
Frag-inst₂ Ft Fa Fb = Frag-inst (Frag-inst Ft (Frag-wk Fb)) Fa

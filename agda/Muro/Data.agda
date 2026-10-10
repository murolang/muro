------------------------------------------------------------------------
-- Data declarations as ⊢ and ⊨ read them, up to conversion.
--
--   IsData σ A        A is a Data type: Nat, Unit, Empty, or a declared
--                     data type applied to Data parameters, after ≈
--                     (Check.isData whnf-normalises before it looks).
--   ReuseOk σ q A     a binder (q x : A) is admissible: + needs Data.
--   InstParams σ T ps R
--                     the constructor type T instantiated at the
--                     parameters ps is R (Check.instParams: peel one Π
--                     per parameter, seen through ≈).
--   BrTy σ i j np T P acc X
--                     X is the type of the branch for constructor i.j
--                     of a data type with np parameters, whose remaining
--                     telescope is T, with motive P and the constructor
--                     arguments seen so far acc (Check.checkBr: one Π
--                     per field, then the motive at the indices of the
--                     constructor's target and at the constructor
--                     applied to its fields).
--   Clash σ np is T   the constructor with telescope T cannot produce a
--                     value at the indices is: some target index and
--                     the expected one are rigidly different Nat
--                     constructors, under su (Check.clashes). Its
--                     branch is skipped; Muro.Typing shows it never
--                     fires.
--
-- All are closed under renaming and substitution, and InstParams is
-- functional up to ≈. Nothing here mentions typing; Muro.Judgement and
-- Muro.Typing use these as premises.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Data where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_; take; drop; length)
open import Data.Nat.Base as ℕ using (ℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.SubstLemmas
open import Muro.Env
open import Muro.Spine
open import Muro.Reduction
open import Muro.Convert

------------------------------------------------------------------------
-- Data types.
------------------------------------------------------------------------

data IsData (σ : Sig) {n} : Tm n → Set
data AllData (σ : Sig) {n} : List (Tm n) → Set

data IsData σ where
  d-nat   : IsData σ nat
  d-unit  : IsData σ unit
  d-empty : IsData σ empty
  d-dty   : ∀ {i d as e}
    → lookupData σ i ≡ ok d → Spine (dty i) as e
    → AllData σ (take (nparams d) as)
    → IsData σ e
  d-prod  : ∀ {A B} → IsData σ A → IsData σ B → IsData σ (prod A B)
  d-conv  : ∀ {A A′} → σ ⊢[ spec ] A ≈ A′ → IsData σ A′ → IsData σ A

data AllData σ where
  ad-[] : AllData σ []
  ad-∷  : ∀ {A as} → IsData σ A → AllData σ as → AllData σ (A ∷ as)

ReuseOk : Sig → Qty → ∀ {n} → Tm n → Set
ReuseOk σ reuse  A = IsData σ A
ReuseOk σ affine A = ⊤
ReuseOk σ erased A = ⊤

IsData-ren : ∀ {σ n k} (ρ : Fin n → Fin k) {A : Tm n} → IsData σ A → IsData σ (ren ρ A)
AllData-ren : ∀ {σ n k} (ρ : Fin n → Fin k) {as : List (Tm n)}
  → AllData σ as → AllData σ (renList ρ as)

IsData-ren ρ d-nat = d-nat
IsData-ren ρ d-unit = d-unit
IsData-ren ρ d-empty = d-empty
IsData-ren ρ (d-dty {d = d} {as} lk sp ad) =
  d-dty lk (Spine-ren ρ sp)
    (subst (AllData _) (renList-take ρ (nparams d) as) (AllData-ren ρ ad))
IsData-ren ρ (d-prod a b) = d-prod (IsData-ren ρ a) (IsData-ren ρ b)
IsData-ren ρ (d-conv c d) = d-conv (≈-ren ρ c) (IsData-ren ρ d)

AllData-ren ρ ad-[] = ad-[]
AllData-ren ρ (ad-∷ d ad) = ad-∷ (IsData-ren ρ d) (AllData-ren ρ ad)

IsData-sub : ∀ {σ n k} (τ : Fin n → Tm k) {A : Tm n} → IsData σ A → IsData σ (sub τ A)
AllData-sub : ∀ {σ n k} (τ : Fin n → Tm k) {as : List (Tm n)}
  → AllData σ as → AllData σ (subList τ as)

IsData-sub τ d-nat = d-nat
IsData-sub τ d-unit = d-unit
IsData-sub τ d-empty = d-empty
IsData-sub τ (d-dty {d = d} {as} lk sp ad) =
  d-dty lk (Spine-sub τ sp)
    (subst (AllData _) (subList-take τ (nparams d) as) (AllData-sub τ ad))
IsData-sub τ (d-prod a b) = d-prod (IsData-sub τ a) (IsData-sub τ b)
IsData-sub τ (d-conv c d) = d-conv (≈-sub τ c) (IsData-sub τ d)

AllData-sub τ ad-[] = ad-[]
AllData-sub τ (ad-∷ d ad) = ad-∷ (IsData-sub τ d) (AllData-sub τ ad)

ReuseOk-ren : ∀ {σ n k} (ρ : Fin n → Fin k) q {A : Tm n}
  → ReuseOk σ q A → ReuseOk σ q (ren ρ A)
ReuseOk-ren ρ reuse  h = IsData-ren ρ h
ReuseOk-ren ρ affine _ = tt
ReuseOk-ren ρ erased _ = tt

ReuseOk-sub : ∀ {σ n k} (τ : Fin n → Tm k) q {A : Tm n}
  → ReuseOk σ q A → ReuseOk σ q (sub τ A)
ReuseOk-sub τ reuse  h = IsData-sub τ h
ReuseOk-sub τ affine _ = tt
ReuseOk-sub τ erased _ = tt

ReuseOk-≈ : ∀ {σ n} q {A A′ : Tm n} → σ ⊢[ spec ] A ≈ A′ → ReuseOk σ q A′ → ReuseOk σ q A
ReuseOk-≈ reuse  c h = d-conv c h
ReuseOk-≈ affine _ _ = tt
ReuseOk-≈ erased _ _ = tt

------------------------------------------------------------------------
-- Copyable: a value that a + binder may use more than once. Data copies
-- by value. A function copies by closure: what is duplicated is its
-- captured variables, so an argument of function type at a + position
-- is checked with its uses scaled to ω (Judgement.⇒-app-copy,
-- args-snoc-copy), and an affine capture is then refused by checkBound.
-- A pair is copyable when both components are. A binder (+ x : A) asks
-- CopyOk; a constructor argument at a + field that is Data keeps its
-- uses (ReuseOk), any other copyable one is scaled.
------------------------------------------------------------------------

data IsCopy (σ : Sig) {n} : Tm n → Set where
  c-data : ∀ {A} → IsData σ A → IsCopy σ A
  c-pi   : ∀ {q A B} → IsCopy σ (pi q A B)
  c-prod : ∀ {A B} → IsCopy σ A → IsCopy σ B → IsCopy σ (prod A B)
  c-conv : ∀ {A A′} → σ ⊢[ spec ] A ≈ A′ → IsCopy σ A′ → IsCopy σ A

IsCopy-ren : ∀ {σ n k} (ρ : Fin n → Fin k) {A : Tm n} → IsCopy σ A → IsCopy σ (ren ρ A)
IsCopy-ren ρ (c-data d) = c-data (IsData-ren ρ d)
IsCopy-ren ρ c-pi = c-pi
IsCopy-ren ρ (c-prod a b) = c-prod (IsCopy-ren ρ a) (IsCopy-ren ρ b)
IsCopy-ren ρ (c-conv c d) = c-conv (≈-ren ρ c) (IsCopy-ren ρ d)

IsCopy-sub : ∀ {σ n k} (τ : Fin n → Tm k) {A : Tm n} → IsCopy σ A → IsCopy σ (sub τ A)
IsCopy-sub τ (c-data d) = c-data (IsData-sub τ d)
IsCopy-sub τ c-pi = c-pi
IsCopy-sub τ (c-prod a b) = c-prod (IsCopy-sub τ a) (IsCopy-sub τ b)
IsCopy-sub τ (c-conv c d) = c-conv (≈-sub τ c) (IsCopy-sub τ d)

CopyOk : Sig → Qty → ∀ {n} → Tm n → Set
CopyOk σ reuse  A = IsCopy σ A
CopyOk σ affine A = ⊤
CopyOk σ erased A = ⊤

CopyOk-ren : ∀ {σ n k} (ρ : Fin n → Fin k) q {A : Tm n}
  → CopyOk σ q A → CopyOk σ q (ren ρ A)
CopyOk-ren ρ reuse  h = IsCopy-ren ρ h
CopyOk-ren ρ affine _ = tt
CopyOk-ren ρ erased _ = tt

CopyOk-sub : ∀ {σ n k} (τ : Fin n → Tm k) q {A : Tm n}
  → CopyOk σ q A → CopyOk σ q (sub τ A)
CopyOk-sub τ reuse  h = IsCopy-sub τ h
CopyOk-sub τ affine _ = tt
CopyOk-sub τ erased _ = tt

CopyOk-≈ : ∀ {σ n} q {A A′ : Tm n} → σ ⊢[ spec ] A ≈ A′ → CopyOk σ q A′ → CopyOk σ q A
CopyOk-≈ reuse  c h = c-conv c h
CopyOk-≈ affine _ _ = tt
CopyOk-≈ erased _ _ = tt

ReuseOk→CopyOk : ∀ {σ n} q {A : Tm n} → ReuseOk σ q A → CopyOk σ q A
ReuseOk→CopyOk reuse  h = c-data h
ReuseOk→CopyOk affine _ = tt
ReuseOk→CopyOk erased _ = tt

------------------------------------------------------------------------
-- Instantiating the parameters of a constructor type.
------------------------------------------------------------------------

data InstParams (σ : Sig) {n} : Tm n → List (Tm n) → Tm n → Set where
  ip-[] : ∀ {T} → InstParams σ T [] T
  ip-∷  : ∀ {T q A B p ps R}
    → σ ⊢[ spec ] T ≈ pi q A B
    → InstParams σ (inst B p) ps R
    → InstParams σ T (p ∷ ps) R

InstParams-ren : ∀ {σ n k} (ρ : Fin n → Fin k) {T : Tm n} {ps R}
  → InstParams σ T ps R → InstParams σ (ren ρ T) (renList ρ ps) (ren ρ R)
InstParams-ren ρ ip-[] = ip-[]
InstParams-ren ρ (ip-∷ {B = B} {p = p} c ip) =
  ip-∷ (≈-ren ρ c)
    (subst (λ T → InstParams _ T _ _) (ren-inst ρ B p) (InstParams-ren ρ ip))

InstParams-sub : ∀ {σ n k} (τ : Fin n → Tm k) {T : Tm n} {ps R}
  → InstParams σ T ps R → InstParams σ (sub τ T) (subList τ ps) (sub τ R)
InstParams-sub τ ip-[] = ip-[]
InstParams-sub τ (ip-∷ {B = B} {p = p} c ip) =
  ip-∷ (≈-sub τ c)
    (subst (λ T → InstParams _ T _ _) (sub-inst τ B p) (InstParams-sub τ ip))

-- Functional up to ≈, in the type and in the parameters.
InstParams-≈ : ∀ {σ n} {T T′ : Tm n} {ps ps′ R R′}
  → σ ⊢[ spec ] T ≈ T′ → σ ⊢[ spec ] ps ≈L ps′
  → InstParams σ T ps R → InstParams σ T′ ps′ R′ → σ ⊢[ spec ] R ≈ R′
InstParams-≈ c ≈L-[] ip-[] ip-[] = c
InstParams-≈ c (≈L-∷ cp cps) (ip-∷ c₁ ip₁) (ip-∷ c₂ ip₂)
  with ≈-pi-inj (≈-trans (≈-sym c₁) (≈-trans c c₂))
... | refl , _ , cB = InstParams-≈ (≈-inst₂ cB cp) cps ip₁ ip₂

------------------------------------------------------------------------
-- The type of a branch.
------------------------------------------------------------------------

-- List facts used below.
renList-drop : ∀ {n k} (ρ : Fin n → Fin k) m (as : List (Tm n))
  → renList ρ (drop m as) ≡ drop m (renList ρ as)
renList-drop ρ ℕ.zero as = refl
renList-drop ρ (ℕ.suc m) [] = refl
renList-drop ρ (ℕ.suc m) (a ∷ as) = renList-drop ρ m as

subList-drop : ∀ {n k} (τ : Fin n → Tm k) m (as : List (Tm n))
  → subList τ (drop m as) ≡ drop m (subList τ as)
subList-drop τ ℕ.zero as = refl
subList-drop τ (ℕ.suc m) [] = refl
subList-drop τ (ℕ.suc m) (a ∷ as) = subList-drop τ m as

drop-++ : ∀ {A : Set} m (xs ys : List A) → length xs ≡ m → drop m (xs ++ ys) ≡ ys
drop-++ ℕ.zero [] ys _ = refl
drop-++ (ℕ.suc m) (x ∷ xs) ys eq = drop-++ m xs ys (cong ℕ.pred eq)

≈L-drop : ∀ {σ m n} k {as bs : List (Tm n)} → σ ⊢[ m ] as ≈L bs → σ ⊢[ m ] drop k as ≈L drop k bs
≈L-drop ℕ.zero c = c
≈L-drop (ℕ.suc k) ≈L-[] = ≈L-[]
≈L-drop (ℕ.suc k) (≈L-∷ _ c) = ≈L-drop k c

≈L-++ : ∀ {σ m n} {as bs cs ds : List (Tm n)}
  → σ ⊢[ m ] as ≈L bs → σ ⊢[ m ] cs ≈L ds → σ ⊢[ m ] (as ++ cs) ≈L (bs ++ ds)
≈L-++ ≈L-[] c′ = c′
≈L-++ (≈L-∷ c cs) c′ = ≈L-∷ c (≈L-++ cs c′)

≈L-++-split : ∀ {σ m n} {as bs cs ds : List (Tm n)} → length as ≡ length bs
  → σ ⊢[ m ] (as ++ cs) ≈L (bs ++ ds) → (σ ⊢[ m ] as ≈L bs) × (σ ⊢[ m ] cs ≈L ds)
≈L-++-split {as = []} {bs = []} _ c = ≈L-[] , c
≈L-++-split {as = _ ∷ as} {bs = _ ∷ bs} len (≈L-∷ c cs) with ≈L-++-split {as = as} {bs = bs} (cong ℕ.pred len) cs
... | c₁ , c₂ = ≈L-∷ c c₁ , c₂

-- The motive at indices and scrutinee commutes with renaming and
-- substitution, and is a congruence in the indices.
ren-motApp : ∀ {n k} (ρ : Fin n → Fin k) (P : Tm (ℕ.suc n)) is (e : Tm n)
  → ren ρ (motApp P is e) ≡ motApp (ren (lift ρ) P) (renList ρ is) (ren ρ e)
ren-motApp ρ P [] e = ren-inst ρ P e
ren-motApp ρ P (i ∷ is) e
  rewrite ren-appsFrom ρ (inst P i) (is ++ (e ∷ [])) | ren-inst ρ P i | renList-++ ρ is (e ∷ []) = refl

sub-motApp : ∀ {n k} (τ : Fin n → Tm k) (P : Tm (ℕ.suc n)) is (e : Tm n)
  → sub τ (motApp P is e) ≡ motApp (sub (lifts τ) P) (subList τ is) (sub τ e)
sub-motApp τ P [] e = sub-inst τ P e
sub-motApp τ P (i ∷ is) e
  rewrite sub-appsFrom τ (inst P i) (is ++ (e ∷ [])) | sub-inst τ P i | subList-++ τ is (e ∷ []) = refl

≈-motApp : ∀ {σ n} (P : Tm (ℕ.suc n)) {is is′ : List (Tm n)} {e e′}
  → σ ⊢[ spec ] is ≈L is′ → σ ⊢[ spec ] e ≈ e′ → σ ⊢[ spec ] motApp P is e ≈ motApp P is′ e′
≈-motApp P ≈L-[] ce = ≈-inst P ce
≈-motApp P (≈L-∷ ci cis) ce = ≈-appsFrom (≈-inst P ci) (≈L-++ cis (≈L-∷ ce ≈L-[]))

-- The kind of a motive commutes with renaming and substitution.
ren-motiveTail : ∀ {n k} (ρ : Fin n → Fin k) di (args : List (Tm n)) ixs
  → ren ρ (motiveTail di args ixs) ≡ motiveTail di (renList ρ args) ixs
ren-motiveTail ρ di args [] rewrite ren-appsFrom ρ (dty di) args = refl
ren-motiveTail ρ di args ((q , T) ∷ ixs)
  rewrite closed-ren ρ T | ren-motiveTail (lift ρ) di (renList suc args ++ (var zero ∷ [])) ixs
        | renList-++ (lift ρ) (renList suc args) (var zero ∷ [])
        | renList-ren (lift ρ) suc args | sym (renList-ren suc ρ args) = refl

sub-motiveTail : ∀ {n k} (τ : Fin n → Tm k) di (args : List (Tm n)) ixs
  → sub τ (motiveTail di args ixs) ≡ motiveTail di (subList τ args) ixs
sub-motiveTail τ di args [] rewrite sub-appsFrom τ (dty di) args = refl
sub-motiveTail τ di args ((q , T) ∷ ixs)
  rewrite closed-sub τ T | sub-motiveTail (lifts τ) di (renList suc args ++ (var zero ∷ [])) ixs
        | subList-++ (lifts τ) (renList suc args) (var zero ∷ [])
        | subList-ren (lifts τ) suc args | sym (renList-sub suc τ args) = refl

data BrTy (σ : Sig) (i j np : ℕ) : ∀ {n} → Tm n → Tm (ℕ.suc n) → List (Tm n) → Tm n → Set where
  bt-pi  : ∀ {n} {T : Tm n} {q A B P acc X}
    → σ ⊢[ spec ] T ≈ pi q A B
    → CopyOk σ q A
    → BrTy σ i j np B (ren (lift suc) P) (renList suc acc ++ (var zero ∷ [])) X
    → BrTy σ i j np T P acc (pi q A X)
  bt-end : ∀ {n} {T : Tm n} {P acc qs D}
    → Spine (dty i) qs D
    → σ ⊢[ spec ] T ≈ D
    → BrTy σ i j np T P acc (motApp P (drop np qs) (appsFrom (ctor i j) acc))

BrTy-≈ : ∀ {σ i j np n} {T T′ : Tm n} {P acc X}
  → σ ⊢[ spec ] T ≈ T′ → BrTy σ i j np T P acc X → BrTy σ i j np T′ P acc X
BrTy-≈ c (bt-pi c′ rok bt) = bt-pi (≈-trans (≈-sym c) c′) rok bt
BrTy-≈ c (bt-end sp c′) = bt-end sp (≈-trans (≈-sym c) c′)

-- Commutations used under the field binder.
lift-lift-suc : ∀ {n k} (ρ : Fin n → Fin k) (x : Fin (ℕ.suc n))
  → lift (lift ρ) (lift suc x) ≡ lift suc (lift ρ x)
lift-lift-suc ρ zero = refl
lift-lift-suc ρ (suc x) = refl

ren-lift-suc : ∀ {n k} (ρ : Fin n → Fin k) (P : Tm (ℕ.suc n))
  → ren (lift (lift ρ)) (ren (lift suc) P) ≡ ren (lift suc) (ren (lift ρ) P)
ren-lift-suc ρ P =
  trans (ren-ren (lift (lift ρ)) (lift suc) P)
    (trans (ren-ext (lift-lift-suc ρ) P) (sym (ren-ren (lift suc) (lift ρ) P)))

renList-acc : ∀ {n k} (ρ : Fin n → Fin k) (acc : List (Tm n))
  → renList (lift ρ) (renList suc acc ++ (var zero ∷ []))
    ≡ renList suc (renList ρ acc) ++ (var zero ∷ [])
renList-acc ρ acc =
  trans (renList-++ (lift ρ) (renList suc acc) (var zero ∷ []))
    (cong (_++ (var zero ∷ []))
      (trans (renList-ren (lift ρ) suc acc) (sym (renList-ren suc ρ acc))))

lifts-lift-suc : ∀ {n k} (τ : Fin n → Tm k) (x : Fin (ℕ.suc n))
  → lifts (lifts τ) (lift suc x) ≡ ren (lift suc) (lifts τ x)
lifts-lift-suc τ zero = refl
lifts-lift-suc τ (suc x) =
  trans (ren-ren suc suc (τ x)) (sym (ren-ren (lift suc) suc (τ x)))

sub-lift-suc : ∀ {n k} (τ : Fin n → Tm k) (P : Tm (ℕ.suc n))
  → sub (lifts (lifts τ)) (ren (lift suc) P) ≡ ren (lift suc) (sub (lifts τ) P)
sub-lift-suc τ P =
  trans (sub-ren (lifts (lifts τ)) (lift suc) P)
    (trans (sub-ext (lifts-lift-suc τ) P) (sym (ren-sub (lift suc) (lifts τ) P)))

subList-acc : ∀ {n k} (τ : Fin n → Tm k) (acc : List (Tm n))
  → subList (lifts τ) (renList suc acc ++ (var zero ∷ []))
    ≡ renList suc (subList τ acc) ++ (var zero ∷ [])
subList-acc τ acc =
  trans (subList-++ (lifts τ) (renList suc acc) (var zero ∷ []))
    (cong (_++ (var zero ∷ []))
      (trans (subList-ren (lifts τ) suc acc) (sym (renList-sub suc τ acc))))

subst₂ : ∀ {A B : Set} (F : A → B → Set) {a a′ b b′}
  → a ≡ a′ → b ≡ b′ → F a b → F a′ b′
subst₂ F refl refl x = x

BrTy-ren : ∀ {σ i j np n k} (ρ : Fin n → Fin k) {T : Tm n} {P acc X}
  → BrTy σ i j np T P acc X
  → BrTy σ i j np (ren ρ T) (ren (lift ρ) P) (renList ρ acc) (ren ρ X)
BrTy-ren ρ (bt-pi {q = q} {P = P} {acc = acc} c rok bt) =
  bt-pi (≈-ren ρ c) (CopyOk-ren ρ q rok)
    (subst₂ (λ P′ acc′ → BrTy _ _ _ _ _ P′ acc′ _) (ren-lift-suc ρ P) (renList-acc ρ acc)
      (BrTy-ren (lift ρ) bt))
BrTy-ren {i = i} {j = j} {np = np} ρ (bt-end {P = P} {acc = acc} {qs = qs} sp c)
  rewrite ren-motApp ρ P (drop np qs) (appsFrom (ctor i j) acc) | ren-appsFrom ρ (ctor i j) acc
        | renList-drop ρ np qs =
  bt-end (Spine-ren ρ sp) (≈-ren ρ c)

BrTy-sub : ∀ {σ i j np n k} (τ : Fin n → Tm k) {T : Tm n} {P acc X}
  → BrTy σ i j np T P acc X
  → BrTy σ i j np (sub τ T) (sub (lifts τ) P) (subList τ acc) (sub τ X)
BrTy-sub τ (bt-pi {q = q} {P = P} {acc = acc} c rok bt) =
  bt-pi (≈-sub τ c) (CopyOk-sub τ q rok)
    (subst₂ (λ P′ acc′ → BrTy _ _ _ _ _ P′ acc′ _) (sub-lift-suc τ P) (subList-acc τ acc)
      (BrTy-sub (lifts τ) bt))
BrTy-sub {i = i} {j = j} {np = np} τ (bt-end {P = P} {acc = acc} {qs = qs} sp c)
  rewrite sub-motApp τ P (drop np qs) (appsFrom (ctor i j) acc) | sub-appsFrom τ (ctor i j) acc
        | subList-drop τ np qs =
  bt-end (Spine-sub τ sp) (≈-sub τ c)

-- Instantiating the field binder: the motive and the earlier arguments
-- were weakened past it, the new argument is var zero.
lifts-instσ-suc : ∀ {n} (a : Tm n) (x : Fin (ℕ.suc n))
  → lifts (instσ a) (lift suc x) ≡ var x
lifts-instσ-suc a zero = refl
lifts-instσ-suc a (suc x) = refl

inst-lift-suc : ∀ {n} (P : Tm (ℕ.suc n)) (a : Tm n)
  → sub (lifts (instσ a)) (ren (lift suc) P) ≡ P
inst-lift-suc P a =
  trans (sub-ren (lifts (instσ a)) (lift suc) P)
    (trans (sub-ext (lifts-instσ-suc a) P) (sub-var P))

subList-var : ∀ {n} (ts : List (Tm n)) → subList var ts ≡ ts
subList-var [] = refl
subList-var (t ∷ ts) rewrite sub-var t | subList-var ts = refl

inst-acc : ∀ {n} (acc : List (Tm n)) (a : Tm n)
  → subList (instσ a) (renList suc acc ++ (var zero ∷ [])) ≡ acc ++ (a ∷ [])
inst-acc acc a =
  trans (subList-++ (instσ a) (renList suc acc) (var zero ∷ []))
    (cong (_++ (a ∷ []))
      (trans (subList-ren (instσ a) suc acc) (subList-var acc)))

BrTy-inst : ∀ {σ i j np n} {B : Tm (ℕ.suc n)} {P acc X} (a : Tm n)
  → BrTy σ i j np B (ren (lift suc) P) (renList suc acc ++ (var zero ∷ [])) X
  → BrTy σ i j np (inst B a) P (acc ++ (a ∷ [])) (inst X a)
BrTy-inst {P = P} {acc = acc} a bt =
  subst₂ (λ P′ acc′ → BrTy _ _ _ _ _ P′ acc′ _) (inst-lift-suc P a) (inst-acc acc a)
    (BrTy-sub (instσ a) bt)

------------------------------------------------------------------------
-- Index clashes. Check.clashes walks the constructor telescope to its
-- target and compares each target index with the expected one after
-- whnf: su against su recurses, su against ze (either way) is a clash,
-- anything else says nothing. A clash means the branch cannot fire.
------------------------------------------------------------------------

data ClashIdx (σ : Sig) {n} : Tm n → Tm n → Set where
  ci-sz : ∀ {e t e′} → σ ⊢[ spec ] e ≈ su e′ → σ ⊢[ spec ] t ≈ ze → ClashIdx σ e t
  ci-zs : ∀ {e t t′} → σ ⊢[ spec ] e ≈ ze → σ ⊢[ spec ] t ≈ su t′ → ClashIdx σ e t
  ci-ss : ∀ {e t e′ t′} → σ ⊢[ spec ] e ≈ su e′ → σ ⊢[ spec ] t ≈ su t′
    → ClashIdx σ e′ t′ → ClashIdx σ e t

data ClashL (σ : Sig) {n} : List (Tm n) → List (Tm n) → Set where
  cl-here  : ∀ {e t es ts} → ClashIdx σ e t → ClashL σ (e ∷ es) (t ∷ ts)
  cl-there : ∀ {e t es ts} → ClashL σ es ts → ClashL σ (e ∷ es) (t ∷ ts)

-- Clash σ np is T: the telescope T, of a constructor of a data type with
-- np parameters, targets indices that clash with is.
data Clash (σ : Sig) (np : ℕ) : ∀ {n} → List (Tm n) → Tm n → Set where
  cl-pi  : ∀ {n} {is : List (Tm n)} {T q A B}
    → σ ⊢[ spec ] T ≈ pi q A B
    → Clash σ np (renList suc is) B
    → Clash σ np is T
  cl-end : ∀ {n} {is : List (Tm n)} {T qs D i}
    → Spine (dty i) qs D
    → σ ⊢[ spec ] T ≈ D
    → ClashL σ is (drop np qs)
    → Clash σ np is T

-- Clashing indices are not convertible.
ClashIdx-≈ : ∀ {σ n} {e t : Tm n} → ClashIdx σ e t → σ ⊢[ spec ] e ≈ t → ⊥
ClashIdx-≈ (ci-sz ce ct) c = ≈-su-ze (≈-trans (≈-sym ce) (≈-trans c ct))
ClashIdx-≈ (ci-zs ce ct) c = ≈-su-ze (≈-trans (≈-sym ct) (≈-trans (≈-sym c) ce))
ClashIdx-≈ (ci-ss ce ct cl) c =
  ClashIdx-≈ cl (≈-su-inj (≈-trans (≈-sym ce) (≈-trans c ct)))

ClashL-≈L : ∀ {σ n} {es ts : List (Tm n)} → ClashL σ es ts → σ ⊢[ spec ] es ≈L ts → ⊥
ClashL-≈L (cl-here cl) (≈L-∷ c _) = ClashIdx-≈ cl c
ClashL-≈L (cl-there cl) (≈L-∷ _ cs) = ClashL-≈L cl cs

Clash-≈ : ∀ {σ np n} {is : List (Tm n)} {T T′}
  → σ ⊢[ spec ] T ≈ T′ → Clash σ np is T → Clash σ np is T′
Clash-≈ c (cl-pi c′ cl) = cl-pi (≈-trans (≈-sym c) c′) cl
Clash-≈ c (cl-end sp c′ cl) = cl-end sp (≈-trans (≈-sym c) c′) cl

ClashIdx-ren : ∀ {σ n k} (ρ : Fin n → Fin k) {e t : Tm n}
  → ClashIdx σ e t → ClashIdx σ (ren ρ e) (ren ρ t)
ClashIdx-ren ρ (ci-sz ce ct) = ci-sz (≈-ren ρ ce) (≈-ren ρ ct)
ClashIdx-ren ρ (ci-zs ce ct) = ci-zs (≈-ren ρ ce) (≈-ren ρ ct)
ClashIdx-ren ρ (ci-ss ce ct cl) = ci-ss (≈-ren ρ ce) (≈-ren ρ ct) (ClashIdx-ren ρ cl)

ClashIdx-sub : ∀ {σ n k} (τ : Fin n → Tm k) {e t : Tm n}
  → ClashIdx σ e t → ClashIdx σ (sub τ e) (sub τ t)
ClashIdx-sub τ (ci-sz ce ct) = ci-sz (≈-sub τ ce) (≈-sub τ ct)
ClashIdx-sub τ (ci-zs ce ct) = ci-zs (≈-sub τ ce) (≈-sub τ ct)
ClashIdx-sub τ (ci-ss ce ct cl) = ci-ss (≈-sub τ ce) (≈-sub τ ct) (ClashIdx-sub τ cl)

ClashL-ren : ∀ {σ n k} (ρ : Fin n → Fin k) {es ts : List (Tm n)}
  → ClashL σ es ts → ClashL σ (renList ρ es) (renList ρ ts)
ClashL-ren ρ (cl-here cl) = cl-here (ClashIdx-ren ρ cl)
ClashL-ren ρ (cl-there cl) = cl-there (ClashL-ren ρ cl)

ClashL-sub : ∀ {σ n k} (τ : Fin n → Tm k) {es ts : List (Tm n)}
  → ClashL σ es ts → ClashL σ (subList τ es) (subList τ ts)
ClashL-sub τ (cl-here cl) = cl-here (ClashIdx-sub τ cl)
ClashL-sub τ (cl-there cl) = cl-there (ClashL-sub τ cl)

Clash-ren : ∀ {σ np n k} (ρ : Fin n → Fin k) {is : List (Tm n)} {T}
  → Clash σ np is T → Clash σ np (renList ρ is) (ren ρ T)
Clash-ren ρ (cl-pi {is = is} c cl) =
  cl-pi (≈-ren ρ c)
    (subst (λ xs → Clash _ _ xs _)
      (trans (renList-ren (lift ρ) suc is) (sym (renList-ren suc ρ is)))
      (Clash-ren (lift ρ) cl))
Clash-ren {np = np} ρ (cl-end {qs = qs} sp c cl) =
  cl-end (Spine-ren ρ sp) (≈-ren ρ c)
    (subst (ClashL _ _) (renList-drop ρ np qs) (ClashL-ren ρ cl))

Clash-sub : ∀ {σ np n k} (τ : Fin n → Tm k) {is : List (Tm n)} {T}
  → Clash σ np is T → Clash σ np (subList τ is) (sub τ T)
Clash-sub τ (cl-pi {is = is} c cl) =
  cl-pi (≈-sub τ c)
    (subst (λ xs → Clash _ _ xs _)
      (trans (subList-ren (lifts τ) suc is) (sym (renList-sub suc τ is)))
      (Clash-sub (lifts τ) cl))
Clash-sub {np = np} τ (cl-end {qs = qs} sp c cl) =
  cl-end (Spine-sub τ sp) (≈-sub τ c)
    (subst (ClashL _ _) (subList-drop τ np qs) (ClashL-sub τ cl))

-- Instantiating the field binder of a clash.
Clash-inst : ∀ {σ np n} {is : List (Tm n)} {B : Tm (ℕ.suc n)} (a : Tm n)
  → Clash σ np (renList suc is) B → Clash σ np is (inst B a)
Clash-inst {is = is} a cl =
  subst (λ xs → Clash _ _ xs _)
    (trans (subList-ren (instσ a) suc is) (subList-var is))
    (Clash-sub (instσ a) cl)

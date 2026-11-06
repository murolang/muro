------------------------------------------------------------------------
-- Application spines. Spine h as e says e is h applied to as, left to
-- right (e ≡ appsFrom h as). Data uses it for constructor applications
-- ctor i j a₁ … aₙ and data types dty i p₁ … pₙ, whose heads are rigid:
-- they are not λ, so a spine only reduces to a spine with the same head.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Spine where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length; take)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.SubstLemmas
open import Muro.Env using (lookupList)

-- The two list facts used, proved here to keep the import footprint small.
++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = refl
++-identityʳ (x ∷ xs) = cong (x ∷_) (++-identityʳ xs)

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)

data Spine {n} (h : Tm n) : List (Tm n) → Tm n → Set where
  sp-[]   : Spine h [] h
  sp-snoc : ∀ {as f a} → Spine h as f → Spine h (as ++ (a ∷ [])) (app f a)

------------------------------------------------------------------------
-- Spine and appsFrom.
------------------------------------------------------------------------

appsFrom-snoc : ∀ {n} (f : Tm n) as a
  → appsFrom f (as ++ (a ∷ [])) ≡ app (appsFrom f as) a
appsFrom-snoc f [] a = refl
appsFrom-snoc f (b ∷ as) a = appsFrom-snoc (app f b) as a

appsFrom-++ : ∀ {n} (f : Tm n) as bs
  → appsFrom f (as ++ bs) ≡ appsFrom (appsFrom f as) bs
appsFrom-++ f [] bs = refl
appsFrom-++ f (a ∷ as) bs = appsFrom-++ (app f a) as bs

Spine-≡ : ∀ {n} {h : Tm n} {as e} → Spine h as e → e ≡ appsFrom h as
Spine-≡ sp-[] = refl
Spine-≡ (sp-snoc {as = as} {a = a} sp) =
  trans (cong (λ f → app f a) (Spine-≡ sp)) (sym (appsFrom-snoc _ as a))

Spine-appsFrom′ : ∀ {n} {h : Tm n} as {as₀ f}
  → Spine h as₀ f → Spine h (as₀ ++ as) (appsFrom f as)
Spine-appsFrom′ [] {as₀} sp rewrite ++-identityʳ as₀ = sp
Spine-appsFrom′ (a ∷ as) {as₀} sp =
  subst (λ xs → Spine _ xs _) (++-assoc as₀ (a ∷ []) as)
    (Spine-appsFrom′ as (sp-snoc sp))

Spine-appsFrom : ∀ {n} (h : Tm n) as → Spine h as (appsFrom h as)
Spine-appsFrom h as = Spine-appsFrom′ as sp-[]

Spine-++ : ∀ {n} {h : Tm n} {as e} bs
  → Spine h as e → Spine h (as ++ bs) (appsFrom e bs)
Spine-++ bs sp = Spine-appsFrom′ bs sp

------------------------------------------------------------------------
-- Reading a spine off a term. unspine e = (h , as) with e ≡ appsFrom h as
-- and h not an application.
------------------------------------------------------------------------

unspine-go : ∀ {n} → Tm n → List (Tm n) → Tm n × List (Tm n)
unspine-go (app f a) acc = unspine-go f (a ∷ acc)
unspine-go h acc = h , acc

unspine : ∀ {n} → Tm n → Tm n × List (Tm n)
unspine e = unspine-go e []

-- Heads that unspine leaves alone.
Head : ∀ {n} → Tm n → Set
Head h = ∀ acc → unspine-go h acc ≡ (h , acc)

head-ctor : ∀ {n i j} → Head {n} (ctor i j)
head-ctor acc = refl

head-dty : ∀ {n i} → Head {n} (dty i)
head-dty acc = refl

Spine→unspine-go : ∀ {n} {h : Tm n} {as e} → Head h → Spine h as e
  → ∀ acc → unspine-go e acc ≡ (h , as ++ acc)
Spine→unspine-go hd sp-[] acc = hd acc
Spine→unspine-go hd (sp-snoc {as = as} {a = a} sp) acc =
  trans (Spine→unspine-go hd sp (a ∷ acc))
    (cong (λ xs → _ , xs) (sym (++-assoc as (a ∷ []) acc)))

Spine→unspine : ∀ {n} {h : Tm n} {as e} → Head h → Spine h as e
  → unspine e ≡ (h , as)
Spine→unspine {as = as} hd sp =
  trans (Spine→unspine-go hd sp []) (cong (λ xs → _ , xs) (++-identityʳ as))

unspine→Spine : ∀ {n} (e : Tm n) acc {h as} → unspine-go e acc ≡ (h , as)
  → ∃ λ as₀ → (as ≡ as₀ ++ acc) × Spine h as₀ e
unspine→Spine (app f a) acc eq with unspine→Spine f (a ∷ acc) eq
... | as₀ , eq′ , sp = as₀ ++ (a ∷ []) , trans eq′ (sym (++-assoc as₀ (a ∷ []) acc)) , sp-snoc sp
unspine→Spine (var _) acc refl = [] , refl , sp-[]
unspine→Spine (typ) acc refl = [] , refl , sp-[]
unspine→Spine (pi _ _ _) acc refl = [] , refl , sp-[]
unspine→Spine (lam _ _ _) acc refl = [] , refl , sp-[]
unspine→Spine (nat) acc refl = [] , refl , sp-[]
unspine→Spine (ze) acc refl = [] , refl , sp-[]
unspine→Spine (su _) acc refl = [] , refl , sp-[]
unspine→Spine (unit) acc refl = [] , refl , sp-[]
unspine→Spine (one) acc refl = [] , refl , sp-[]
unspine→Spine (empty) acc refl = [] , refl , sp-[]
unspine→Spine (dty _) acc refl = [] , refl , sp-[]
unspine→Spine (ctor _ _) acc refl = [] , refl , sp-[]
unspine→Spine (mData _ _ _) acc refl = [] , refl , sp-[]
unspine→Spine (mNat _ _ _ _) acc refl = [] , refl , sp-[]
unspine→Spine (mEmp _ _) acc refl = [] , refl , sp-[]
unspine→Spine (mUnit _ _ _) acc refl = [] , refl , sp-[]
unspine→Spine (idt _ _ _) acc refl = [] , refl , sp-[]
unspine→Spine (rfl) acc refl = [] , refl , sp-[]
unspine→Spine (rwt _ _ _) acc refl = [] , refl , sp-[]
unspine→Spine (def _) acc refl = [] , refl , sp-[]
unspine→Spine (ann _ _) acc refl = [] , refl , sp-[]
unspine→Spine (prod _ _) acc refl = [] , refl , sp-[]
unspine→Spine (pair _ _) acc refl = [] , refl , sp-[]
unspine→Spine (letp _ _) acc refl = [] , refl , sp-[]
unspine→Spine (nu _) acc refl = [] , refl , sp-[]
unspine→Spine (unf _ _) acc refl = [] , refl , sp-[]
unspine→Spine (ucons _) acc refl = [] , refl , sp-[]
unspine→Spine (i64) acc refl = [] , refl , sp-[]
unspine→Spine (f32ty) acc refl = [] , refl , sp-[]
unspine→Spine (tensor _ _) acc refl = [] , refl , sp-[]
unspine→Spine (addi _ _) acc refl = [] , refl , sp-[]
unspine→Spine (muli _ _) acc refl = [] , refl , sp-[]
unspine→Spine (addt _ _) acc refl = [] , refl , sp-[]
unspine→Spine (toi64 _) acc refl = [] , refl , sp-[]
unspine→Spine (packi _ _) acc refl = [] , refl , sp-[]
unspine→Spine (word _ _) acc refl = [] , refl , sp-[]

unspine→Spine′ : ∀ {n} {e h : Tm n} {as} → unspine e ≡ (h , as) → Spine h as e
unspine→Spine′ {e = e} eq with unspine→Spine e [] eq
... | as₀ , eq′ , sp rewrite eq′ | ++-identityʳ as₀ = sp

-- Spines with rigid heads are read uniquely.
Spine-unique : ∀ {n} {h h′ : Tm n} {as as′ e} → Head h → Head h′
  → Spine h as e → Spine h′ as′ e → (h ≡ h′) × (as ≡ as′)
Spine-unique hd hd′ sp sp′
  with trans (sym (Spine→unspine hd sp)) (Spine→unspine hd′ sp′)
... | refl = refl , refl

------------------------------------------------------------------------
-- Renaming and substitution.
------------------------------------------------------------------------

renList-++ : ∀ {n m} (ρ : Fin n → Fin m) (as bs : List (Tm n))
  → renList ρ (as ++ bs) ≡ renList ρ as ++ renList ρ bs
renList-++ ρ [] bs = refl
renList-++ ρ (a ∷ as) bs = cong (ren ρ a ∷_) (renList-++ ρ as bs)

subList-++ : ∀ {n m} (τ : Fin n → Tm m) (as bs : List (Tm n))
  → subList τ (as ++ bs) ≡ subList τ as ++ subList τ bs
subList-++ τ [] bs = refl
subList-++ τ (a ∷ as) bs = cong (sub τ a ∷_) (subList-++ τ as bs)

renList-length : ∀ {n m} (ρ : Fin n → Fin m) (as : List (Tm n))
  → length (renList ρ as) ≡ length as
renList-length ρ [] = refl
renList-length ρ (a ∷ as) = cong suc (renList-length ρ as)

subList-length : ∀ {n m} (τ : Fin n → Tm m) (as : List (Tm n))
  → length (subList τ as) ≡ length as
subList-length τ [] = refl
subList-length τ (a ∷ as) = cong suc (subList-length τ as)

renList-take : ∀ {n m} (ρ : Fin n → Fin m) k (as : List (Tm n))
  → renList ρ (take k as) ≡ take k (renList ρ as)
renList-take ρ zero as = refl
renList-take ρ (suc k) [] = refl
renList-take ρ (suc k) (a ∷ as) = cong (ren ρ a ∷_) (renList-take ρ k as)

subList-take : ∀ {n m} (τ : Fin n → Tm m) k (as : List (Tm n))
  → subList τ (take k as) ≡ take k (subList τ as)
subList-take τ zero as = refl
subList-take τ (suc k) [] = refl
subList-take τ (suc k) (a ∷ as) = cong (sub τ a ∷_) (subList-take τ k as)

ren-appsFrom : ∀ {n m} (ρ : Fin n → Fin m) (f : Tm n) as
  → ren ρ (appsFrom f as) ≡ appsFrom (ren ρ f) (renList ρ as)
ren-appsFrom ρ f [] = refl
ren-appsFrom ρ f (a ∷ as) = ren-appsFrom ρ (app f a) as

sub-appsFrom : ∀ {n m} (τ : Fin n → Tm m) (f : Tm n) as
  → sub τ (appsFrom f as) ≡ appsFrom (sub τ f) (subList τ as)
sub-appsFrom τ f [] = refl
sub-appsFrom τ f (a ∷ as) = sub-appsFrom τ (app f a) as

Spine-ren : ∀ {n m} (ρ : Fin n → Fin m) {h : Tm n} {as e}
  → Spine h as e → Spine (ren ρ h) (renList ρ as) (ren ρ e)
Spine-ren ρ sp-[] = sp-[]
Spine-ren ρ (sp-snoc {as = as} {a = a} sp) =
  subst (λ xs → Spine _ xs _) (sym (renList-++ ρ as (a ∷ [])))
    (sp-snoc (Spine-ren ρ sp))

Spine-sub : ∀ {n m} (τ : Fin n → Tm m) {h : Tm n} {as e}
  → Spine h as e → Spine (sub τ h) (subList τ as) (sub τ e)
Spine-sub τ sp-[] = sp-[]
Spine-sub τ (sp-snoc {as = as} {a = a} sp) =
  subst (λ xs → Spine _ xs _) (sym (subList-++ τ as (a ∷ [])))
    (sp-snoc (Spine-sub τ sp))

lookupList-ren : ∀ {n m} (ρ : Fin n → Fin m) (bs : List (Tm n)) k {b}
  → lookupList bs k ≡ ok b → lookupList (renList ρ bs) k ≡ ok (ren ρ b)
lookupList-ren ρ (b ∷ bs) zero refl = refl
lookupList-ren ρ (b ∷ bs) (suc k) eq = lookupList-ren ρ bs k eq
lookupList-ren ρ [] zero ()
lookupList-ren ρ [] (suc k) ()

lookupList-sub : ∀ {n m} (τ : Fin n → Tm m) (bs : List (Tm n)) k {b}
  → lookupList bs k ≡ ok b → lookupList (subList τ bs) k ≡ ok (sub τ b)
lookupList-sub τ (b ∷ bs) zero refl = refl
lookupList-sub τ (b ∷ bs) (suc k) eq = lookupList-sub τ bs k eq
lookupList-sub τ [] zero ()
lookupList-sub τ [] (suc k) ()

------------------------------------------------------------------------
-- Views used by the checker: the head of a spine tested for a specific
-- constructor. Each comes with its inversion lemma; the lemmas list the
-- other heads once so that no proof about the checker has to.
------------------------------------------------------------------------

open import Data.Maybe.Base using (Maybe; just; nothing)

-- Constructor applications ctor i j a₁ … aₙ.
ctorSpine : ∀ {n} → Tm n → Maybe (ℕ × ℕ × List (Tm n))
ctorSpine t with unspine t
... | (ctor i j , as) = just (i , j , as)
... | _ = nothing

ctorSpine-just : ∀ {n} {t : Tm n} {i j as}
  → ctorSpine t ≡ just (i , j , as) → Spine (ctor i j) as t
ctorSpine-just {t = t} eq with unspine t in ueq
ctorSpine-just refl | (ctor _ _ , _) = unspine→Spine′ ueq
ctorSpine-just () | ((var _) , _)
ctorSpine-just () | (typ , _)
ctorSpine-just () | ((pi _ _ _) , _)
ctorSpine-just () | ((lam _ _ _) , _)
ctorSpine-just () | ((app _ _) , _)
ctorSpine-just () | (nat , _)
ctorSpine-just () | (ze , _)
ctorSpine-just () | ((su _) , _)
ctorSpine-just () | (unit , _)
ctorSpine-just () | (one , _)
ctorSpine-just () | (empty , _)
ctorSpine-just () | ((dty _) , _)
ctorSpine-just () | ((mData _ _ _) , _)
ctorSpine-just () | ((mNat _ _ _ _) , _)
ctorSpine-just () | ((mEmp _ _) , _)
ctorSpine-just () | ((mUnit _ _ _) , _)
ctorSpine-just () | ((idt _ _ _) , _)
ctorSpine-just () | (rfl , _)
ctorSpine-just () | ((rwt _ _ _) , _)
ctorSpine-just () | ((def _) , _)
ctorSpine-just () | ((ann _ _) , _)
ctorSpine-just () | ((prod _ _) , _)
ctorSpine-just () | ((pair _ _) , _)
ctorSpine-just () | ((letp _ _) , _)
ctorSpine-just () | ((nu _) , _)
ctorSpine-just () | ((unf _ _) , _)
ctorSpine-just () | ((ucons _) , _)
ctorSpine-just () | (i64 , _)
ctorSpine-just () | (f32ty , _)
ctorSpine-just () | ((tensor _ _) , _)
ctorSpine-just () | ((addi _ _) , _)
ctorSpine-just () | ((muli _ _) , _)
ctorSpine-just () | ((addt _ _) , _)
ctorSpine-just () | ((toi64 _) , _)
ctorSpine-just () | ((packi _ _) , _)
ctorSpine-just () | ((word _ _) , _)

-- Data types dty i p₁ … pₙ.
dtyArgs : ∀ {n} → Tm n → Maybe (ℕ × List (Tm n))
dtyArgs t with unspine t
... | (dty i , as) = just (i , as)
... | _ = nothing

dtyArgs-just : ∀ {n} {t : Tm n} {i as}
  → dtyArgs t ≡ just (i , as) → Spine (dty i) as t
dtyArgs-just {t = t} eq with unspine t in ueq
dtyArgs-just refl | (dty _ , _) = unspine→Spine′ ueq
dtyArgs-just () | ((var _) , _)
dtyArgs-just () | (typ , _)
dtyArgs-just () | ((pi _ _ _) , _)
dtyArgs-just () | ((lam _ _ _) , _)
dtyArgs-just () | ((app _ _) , _)
dtyArgs-just () | (nat , _)
dtyArgs-just () | (ze , _)
dtyArgs-just () | ((su _) , _)
dtyArgs-just () | (unit , _)
dtyArgs-just () | (one , _)
dtyArgs-just () | (empty , _)
dtyArgs-just () | ((ctor _ _) , _)
dtyArgs-just () | ((mData _ _ _) , _)
dtyArgs-just () | ((mNat _ _ _ _) , _)
dtyArgs-just () | ((mEmp _ _) , _)
dtyArgs-just () | ((mUnit _ _ _) , _)
dtyArgs-just () | ((idt _ _ _) , _)
dtyArgs-just () | (rfl , _)
dtyArgs-just () | ((rwt _ _ _) , _)
dtyArgs-just () | ((def _) , _)
dtyArgs-just () | ((ann _ _) , _)
dtyArgs-just () | ((prod _ _) , _)
dtyArgs-just () | ((pair _ _) , _)
dtyArgs-just () | ((letp _ _) , _)
dtyArgs-just () | ((nu _) , _)
dtyArgs-just () | ((unf _ _) , _)
dtyArgs-just () | ((ucons _) , _)
dtyArgs-just () | (i64 , _)
dtyArgs-just () | (f32ty , _)
dtyArgs-just () | ((tensor _ _) , _)
dtyArgs-just () | ((addi _ _) , _)
dtyArgs-just () | ((muli _ _) , _)
dtyArgs-just () | ((addt _ _) , _)
dtyArgs-just () | ((toi64 _) , _)
dtyArgs-just () | ((packi _ _) , _)
dtyArgs-just () | ((word _ _) , _)

-- `def i` applied to at least one argument.
defArgs : ∀ {n} → Tm n → Maybe (ℕ × Tm n × List (Tm n))
defArgs t with unspine t
... | (def i , a ∷ as) = just (i , a , as)
... | _ = nothing

defArgs-just : ∀ {n} {t : Tm n} {i a as}
  → defArgs t ≡ just (i , a , as) → Spine (def i) (a ∷ as) t
defArgs-just {t = t} eq with unspine t in ueq
defArgs-just refl | (def _ , _ ∷ _) = unspine→Spine′ ueq
defArgs-just () | (def _ , [])
defArgs-just () | ((var _) , _)
defArgs-just () | (typ , _)
defArgs-just () | ((pi _ _ _) , _)
defArgs-just () | ((lam _ _ _) , _)
defArgs-just () | ((app _ _) , _)
defArgs-just () | (nat , _)
defArgs-just () | (ze , _)
defArgs-just () | ((su _) , _)
defArgs-just () | (unit , _)
defArgs-just () | (one , _)
defArgs-just () | (empty , _)
defArgs-just () | ((dty _) , _)
defArgs-just () | ((ctor _ _) , _)
defArgs-just () | ((mData _ _ _) , _)
defArgs-just () | ((mNat _ _ _ _) , _)
defArgs-just () | ((mEmp _ _) , _)
defArgs-just () | ((mUnit _ _ _) , _)
defArgs-just () | ((idt _ _ _) , _)
defArgs-just () | (rfl , _)
defArgs-just () | ((rwt _ _ _) , _)
defArgs-just () | ((ann _ _) , _)
defArgs-just () | ((prod _ _) , _)
defArgs-just () | ((pair _ _) , _)
defArgs-just () | ((letp _ _) , _)
defArgs-just () | ((nu _) , _)
defArgs-just () | ((unf _ _) , _)
defArgs-just () | ((ucons _) , _)
defArgs-just () | (i64 , _)
defArgs-just () | (f32ty , _)
defArgs-just () | ((tensor _ _) , _)
defArgs-just () | ((addi _ _) , _)
defArgs-just () | ((muli _ _) , _)
defArgs-just () | ((addt _ _) , _)
defArgs-just () | ((toi64 _) , _)
defArgs-just () | ((packi _ _) , _)
defArgs-just () | ((word _ _) , _)

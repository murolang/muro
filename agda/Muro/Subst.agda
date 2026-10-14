------------------------------------------------------------------------
-- Substitution on de Bruijn terms, plus toPHOAS. unembed is Muro.Unembed.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Subst where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_)
open import Data.Nat.Base using (ℕ; zero; suc)

open import Muro.Base
open import Muro.Syntax

------------------------------------------------------------------------
-- Renaming and substitution (de Bruijn).
------------------------------------------------------------------------

lift : ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
lift ρ zero    = zero
lift ρ (suc i) = suc (ρ i)

mutual
  ren : ∀ {n m} → (Fin n → Fin m) → Tm n → Tm m
  ren ρ (var i)       = var (ρ i)
  ren ρ typ           = typ
  ren ρ (pi q A B)    = pi q (ren ρ A) (ren (lift ρ) B)
  ren ρ (lam q A t)   = lam q (ren ρ A) (ren (lift ρ) t)
  ren ρ (app f a)     = app (ren ρ f) (ren ρ a)
  ren ρ nat           = nat
  ren ρ ze            = ze
  ren ρ (su t)        = su (ren ρ t)
  ren ρ unit          = unit
  ren ρ one           = one
  ren ρ empty         = empty
  ren ρ (dty i)       = dty i
  ren ρ (ctor i j)    = ctor i j
  ren ρ (mData e P bs)= mData (ren ρ e) (ren (lift ρ) P) (renList ρ bs)
  ren ρ (mNat e P z s)= mNat (ren ρ e) (ren (lift ρ) P) (ren ρ z) (ren (lift ρ) s)
  ren ρ (mEmp e P)    = mEmp (ren ρ e) (ren (lift ρ) P)
  ren ρ (mUnit e P u) = mUnit (ren ρ e) (ren (lift ρ) P) (ren ρ u)
  ren ρ (idt A a b)   = idt (ren ρ A) (ren ρ a) (ren ρ b)
  ren ρ rfl           = rfl
  ren ρ (rwt e P t)   = rwt (ren ρ e) (ren (lift ρ) P) (ren ρ t)
  ren ρ (def i)       = def i
  ren ρ (ann e A)     = ann (ren ρ e) (ren ρ A)
  ren ρ (prod A B)    = prod (ren ρ A) (ren ρ B)
  ren ρ (pair a b)    = pair (ren ρ a) (ren ρ b)
  ren ρ (letp e t)    = letp (ren ρ e) (ren (lift (lift ρ)) t)
  ren ρ (nu F)        = nu (ren (lift ρ) F)
  ren ρ (unf s f)     = unf (ren ρ s) (ren ρ f)
  ren ρ (ucons s)     = ucons (ren ρ s)
  ren ρ i64           = i64
  ren ρ f32ty         = f32ty
  ren ρ (tensor d s)  = tensor (ren ρ d) (ren ρ s)
  ren ρ (addi x y)    = addi (ren ρ x) (ren ρ y)
  ren ρ (muli x y)    = muli (ren ρ x) (ren ρ y)
  ren ρ (addt t u)    = addt (ren ρ t) (ren ρ u)
  ren ρ (toi64 t)     = toi64 (ren ρ t)
  ren ρ (packi x y)   = packi (ren ρ x) (ren ρ y)

  renList : ∀ {n m} → (Fin n → Fin m) → List (Tm n) → List (Tm m)
  renList ρ []       = []
  renList ρ (t ∷ ts) = ren ρ t ∷ renList ρ ts

wk : ∀ {n} → Tm n → Tm (suc n)
wk = ren suc

-- Stream A = ν X. A × X
stream : ∀ {n} → Tm n → Tm n
stream A = nu (prod (wk A) (var zero))

------------------------------------------------------------------------
-- Partial renaming: the map may refuse a variable, and then so does the
-- term. strengthen₂ undoes a double weakening where possible: it is how
-- Check decides whether the type inferred for a let body mentions the
-- two components (SubstLemmas.strengthen₂-sound).
------------------------------------------------------------------------

liftM : ∀ {n m} → (Fin n → Result (Fin m)) → Fin (suc n) → Result (Fin (suc m))
liftM ρ zero    = ok zero
liftM ρ (suc i) = suc <$> ρ i

mutual
  renM : ∀ {n m} → (Fin n → Result (Fin m)) → Tm n → Result (Tm m)
  renM ρ (var i) = var <$> ρ i
  renM ρ typ = ok typ
  renM ρ (pi q A B) = (pi q) <$> renM ρ A ⊛ renM (liftM ρ) B
  renM ρ (lam q A t) = (lam q) <$> renM ρ A ⊛ renM (liftM ρ) t
  renM ρ (app f a) = app <$> renM ρ f ⊛ renM ρ a
  renM ρ nat = ok nat
  renM ρ ze = ok ze
  renM ρ (su t) = su <$> renM ρ t
  renM ρ unit = ok unit
  renM ρ one = ok one
  renM ρ empty = ok empty
  renM ρ (dty i) = ok (dty i)
  renM ρ (ctor i j) = ok (ctor i j)
  renM ρ (mData e P bs) = mData <$> renM ρ e ⊛ renM (liftM ρ) P ⊛ renMList ρ bs
  renM ρ (mNat e P z s) = mNat <$> renM ρ e ⊛ renM (liftM ρ) P ⊛ renM ρ z ⊛ renM (liftM ρ) s
  renM ρ (mEmp e P) = mEmp <$> renM ρ e ⊛ renM (liftM ρ) P
  renM ρ (mUnit e P u) = mUnit <$> renM ρ e ⊛ renM (liftM ρ) P ⊛ renM ρ u
  renM ρ (idt A a b) = idt <$> renM ρ A ⊛ renM ρ a ⊛ renM ρ b
  renM ρ rfl = ok rfl
  renM ρ (rwt e P t) = rwt <$> renM ρ e ⊛ renM (liftM ρ) P ⊛ renM ρ t
  renM ρ (def i) = ok (def i)
  renM ρ (ann e A) = ann <$> renM ρ e ⊛ renM ρ A
  renM ρ (prod A B) = prod <$> renM ρ A ⊛ renM ρ B
  renM ρ (pair a b) = pair <$> renM ρ a ⊛ renM ρ b
  renM ρ (letp e t) = letp <$> renM ρ e ⊛ renM (liftM (liftM ρ)) t
  renM ρ (nu F) = nu <$> renM (liftM ρ) F
  renM ρ (unf s f) = unf <$> renM ρ s ⊛ renM ρ f
  renM ρ (ucons s) = ucons <$> renM ρ s
  renM ρ i64 = ok i64
  renM ρ f32ty = ok f32ty
  renM ρ (tensor d s) = tensor <$> renM ρ d ⊛ renM ρ s
  renM ρ (addi x y) = addi <$> renM ρ x ⊛ renM ρ y
  renM ρ (muli x y) = muli <$> renM ρ x ⊛ renM ρ y
  renM ρ (addt t u) = addt <$> renM ρ t ⊛ renM ρ u
  renM ρ (toi64 t) = toi64 <$> renM ρ t
  renM ρ (packi x y) = packi <$> renM ρ x ⊛ renM ρ y

  renMList : ∀ {n m} → (Fin n → Result (Fin m)) → List (Tm n) → Result (List (Tm m))
  renMList ρ []       = ok []
  renMList ρ (t ∷ ts) = _∷_ <$> renM ρ t ⊛ renMList ρ ts

unwk : ∀ {n} → Fin (suc n) → Result (Fin n)
unwk zero    = fail "not a weakening"
unwk (suc i) = ok i

-- Drop one unused binder. Stream's element type is a weakening.
strengthen : ∀ {n} → Tm (suc n) → Result (Tm n)
strengthen = renM unwk

unwk₂ : ∀ {n} → Fin (suc (suc n)) → Result (Fin n)
unwk₂ zero          = fail "let: the body's type mentions a component of the pair"
unwk₂ (suc zero)    = fail "let: the body's type mentions a component of the pair"
unwk₂ (suc (suc i)) = ok i

strengthen₂ : ∀ {n} → Tm (suc (suc n)) → Result (Tm n)
strengthen₂ = renM unwk₂

-- The projections are sugar for let: fst t = let (a, _) = t in a.
fstTm : ∀ {n} → Tm n → Tm n
fstTm t = letp t (var (suc zero))

sndTm : ∀ {n} → Tm n → Tm n
sndTm t = letp t (var zero)

-- Always P = ν (Y : Stream A → Type). λ s. P (head s) × Y (tail s)
-- Always P s unfolds to P (head s) × Always P (tail s).
alwaysFam : ∀ {n} → Tm n → Tm n → Tm (suc n)
alwaysFam A P =
  lam affine (wk (stream A))
    (prod
      (app (wk (wk P)) (fstTm (ucons (var zero))))
      (app (var (suc zero)) (sndTm (ucons (var zero)))))

always : ∀ {n} → Tm n → Tm n → Tm n → Tm n
always A P s = app (nu (alwaysFam A P)) s

-- σ ~ τ = ν (R : Stream A → Stream A → Type).
--           λ σ τ. {head σ ≡ head τ : A} × R (tail σ) (tail τ)
bisimFam : ∀ {n} → Tm n → Tm (suc n)
bisimFam A =
  lam affine (wk (stream A))
    (lam affine (wk (wk (stream A)))
      (prod
        (idt (wk (wk (wk A)))
             (fstTm (ucons (var (suc zero))))
             (fstTm (ucons (var zero))))
        (app
          (app (var (suc (suc zero))) (sndTm (ucons (var (suc zero)))))
          (sndTm (ucons (var zero))))))

bisim : ∀ {n} → Tm n → Tm n → Tm n → Tm n
bisim A σ τ = app (app (nu (bisimFam A)) σ) τ

fromZero : ∀ {n} → Fin 0 → Fin n
fromZero ()

closed : ∀ {n} → Tm 0 → Tm n
closed = ren fromZero

lifts : ∀ {n m} → (Fin n → Tm m) → Fin (suc n) → Tm (suc m)
lifts σ zero    = var zero
lifts σ (suc i) = wk (σ i)

mutual
  sub : ∀ {n m} → (Fin n → Tm m) → Tm n → Tm m
  sub σ (var i)        = σ i
  sub σ typ            = typ
  sub σ (pi q A B)     = pi q (sub σ A) (sub (lifts σ) B)
  sub σ (lam q A t)    = lam q (sub σ A) (sub (lifts σ) t)
  sub σ (app f a)      = app (sub σ f) (sub σ a)
  sub σ nat            = nat
  sub σ ze             = ze
  sub σ (su t)         = su (sub σ t)
  sub σ unit           = unit
  sub σ one            = one
  sub σ empty          = empty
  sub σ (dty i)        = dty i
  sub σ (ctor i j)     = ctor i j
  sub σ (mData e P bs) = mData (sub σ e) (sub (lifts σ) P) (subList σ bs)
  sub σ (mNat e P z s) = mNat (sub σ e) (sub (lifts σ) P) (sub σ z) (sub (lifts σ) s)
  sub σ (mEmp e P)     = mEmp (sub σ e) (sub (lifts σ) P)
  sub σ (mUnit e P u)  = mUnit (sub σ e) (sub (lifts σ) P) (sub σ u)
  sub σ (idt A a b)    = idt (sub σ A) (sub σ a) (sub σ b)
  sub σ rfl            = rfl
  sub σ (rwt e P t)    = rwt (sub σ e) (sub (lifts σ) P) (sub σ t)
  sub σ (def i)        = def i
  sub σ (ann e A)      = ann (sub σ e) (sub σ A)
  sub σ (prod A B)     = prod (sub σ A) (sub σ B)
  sub σ (pair a b)     = pair (sub σ a) (sub σ b)
  sub σ (letp e t)     = letp (sub σ e) (sub (lifts (lifts σ)) t)
  sub σ (nu F)         = nu (sub (lifts σ) F)
  sub σ (unf s f)      = unf (sub σ s) (sub σ f)
  sub σ (ucons s)      = ucons (sub σ s)
  sub σ i64            = i64
  sub σ f32ty          = f32ty
  sub σ (tensor d s)   = tensor (sub σ d) (sub σ s)
  sub σ (addi x y)     = addi (sub σ x) (sub σ y)
  sub σ (muli x y)     = muli (sub σ x) (sub σ y)
  sub σ (addt t u)     = addt (sub σ t) (sub σ u)
  sub σ (toi64 t)      = toi64 (sub σ t)
  sub σ (packi x y)    = packi (sub σ x) (sub σ y)

  subList : ∀ {n m} → (Fin n → Tm m) → List (Tm n) → List (Tm m)
  subList σ []       = []
  subList σ (t ∷ ts) = sub σ t ∷ subList σ ts

-- Open a binder: (x. t)[u].
-- Named helper: pattern-lambdas do not compute when passed to `sub`.
instσ : ∀ {n} → Tm n → Fin (suc n) → Tm n
instσ u zero    = u
instσ u (suc i) = var i

inst : ∀ {n} → Tm (suc n) → Tm n → Tm n
inst t u = sub (instσ u) t

-- Open two binders: (x. y. t)[a, b], y the inner one (var 0).
inst₂ : ∀ {n} → Tm (suc (suc n)) → Tm n → Tm n → Tm n
inst₂ t a b = inst (inst t (wk b)) a

motSucσ : ∀ {n} → Fin (suc n) → Tm (suc n)
motSucσ zero    = su (var zero)
motSucσ (suc i) = var (suc i)

motSuc : ∀ {n} → Tm (suc n) → Tm (suc n)
motSuc P = sub motSucσ P

appsFrom : ∀ {n} → Tm n → List (Tm n) → Tm n
appsFrom f []       = f
appsFrom f (a ∷ as) = appsFrom (app f a) as

-- The motive of a match at the indices is and the scrutinee e. P is the
-- motive under its first binder: the scrutinee when the data type has
-- no indices, the first index otherwise (Check writes the motive as a
-- λ; appsFrom (lam _ _ P) (is ++ [e]) β-reduces to this).
motApp : ∀ {n} → Tm (suc n) → List (Tm n) → Tm n → Tm n
motApp P []       e = inst P e
motApp P (i ∷ is) e = appsFrom (inst P i) (is ++ (e ∷ []))

-- The kind of a motive after its first index binder: one Π per further
-- index (index types are closed), then Π over the data type at the
-- parameters and indices so far, then Type.
motiveTail : ∀ {n} → ℕ → List (Tm n) → List (Qty × Tm 0) → Tm n
motiveTail di args []             = pi affine (appsFrom (dty di) args) typ
motiveTail di args ((q , T) ∷ is) =
  pi q (closed T) (motiveTail di (renList suc args ++ (var zero ∷ [])) is)

------------------------------------------------------------------------
-- toPHOAS : de Bruijn → PHOAS
------------------------------------------------------------------------

mutual
  toPHOAS : ∀ {n} {V : Set} → (Fin n → V) → Tm n → PTm V
  toPHOAS ρ (var i)        = var (ρ i)
  toPHOAS ρ typ            = typ
  toPHOAS ρ (pi q A B)     = pi q (toPHOAS ρ A) (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) B)
  toPHOAS ρ (lam q A t)    = lam q (toPHOAS ρ A) (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) t)
  toPHOAS ρ (app f a)      = app (toPHOAS ρ f) (toPHOAS ρ a)
  toPHOAS ρ nat            = nat
  toPHOAS ρ ze             = ze
  toPHOAS ρ (su t)         = su (toPHOAS ρ t)
  toPHOAS ρ unit           = unit
  toPHOAS ρ one            = one
  toPHOAS ρ empty          = empty
  toPHOAS ρ (dty i)        = dty i
  toPHOAS ρ (ctor i j)     = ctor i j
  toPHOAS ρ (mData e P bs) = mData (toPHOAS ρ e)
                                  (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) P)
                                  (toPHOASList ρ bs)
  toPHOAS ρ (mNat e P z s) = mNat (toPHOAS ρ e)
                                  (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) P)
                                  (toPHOAS ρ z)
                                  (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) s)
  toPHOAS ρ (mEmp e P)     = mEmp (toPHOAS ρ e)
                                  (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) P)
  toPHOAS ρ (mUnit e P u)  = mUnit (toPHOAS ρ e)
                                   (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) P)
                                   (toPHOAS ρ u)
  toPHOAS ρ (idt A a b)    = idt (toPHOAS ρ A) (toPHOAS ρ a) (toPHOAS ρ b)
  toPHOAS ρ rfl            = rfl
  toPHOAS ρ (rwt e P t)    = rwt (toPHOAS ρ e)
                                 (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) P)
                                 (toPHOAS ρ t)
  toPHOAS ρ (def i)        = def i
  toPHOAS ρ (ann e A)      = ann (toPHOAS ρ e) (toPHOAS ρ A)
  toPHOAS ρ (prod A B)     = prod (toPHOAS ρ A) (toPHOAS ρ B)
  toPHOAS ρ (pair a b)     = pair (toPHOAS ρ a) (toPHOAS ρ b)
  toPHOAS ρ (letp e t)     = letp (toPHOAS ρ e)
                                  (λ a b → toPHOAS (λ { zero → b ; (suc zero) → a ; (suc (suc i)) → ρ i }) t)
  toPHOAS ρ (nu F)         = nu (λ v → toPHOAS (λ { zero → v ; (suc i) → ρ i }) F)
  toPHOAS ρ (unf s f)      = unf (toPHOAS ρ s) (toPHOAS ρ f)
  toPHOAS ρ (ucons s)      = ucons (toPHOAS ρ s)
  toPHOAS ρ i64            = i64
  toPHOAS ρ f32ty          = f32ty
  toPHOAS ρ (tensor d s)   = tensor (toPHOAS ρ d) (toPHOAS ρ s)
  toPHOAS ρ (addi x y)     = addi (toPHOAS ρ x) (toPHOAS ρ y)
  toPHOAS ρ (muli x y)     = muli (toPHOAS ρ x) (toPHOAS ρ y)
  toPHOAS ρ (addt t u)     = addt (toPHOAS ρ t) (toPHOAS ρ u)
  toPHOAS ρ (toi64 t)      = toi64 (toPHOAS ρ t)
  toPHOAS ρ (packi x y)    = packi (toPHOAS ρ x) (toPHOAS ρ y)

  toPHOASList : ∀ {n} {V : Set} → (Fin n → V) → List (Tm n) → List (PTm V)
  toPHOASList ρ []       = []
  toPHOASList ρ (t ∷ ts) = toPHOAS ρ t ∷ toPHOASList ρ ts

toPHOAS0 : ∀ {V : Set} → Tm 0 → PTm V
toPHOAS0 t = toPHOAS (λ ()) t

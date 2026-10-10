------------------------------------------------------------------------
-- Declarative typing for the ⊢ fragment, without uses. This is the
-- judgment the metatheory is about.
--
--   σ , Γ ⊨[ m ] e ∶ A   is   σ , Γ ⊨⁰[ m ] e ∶ A₀  with  σ ⊢[ spec ] A₀ ≈ A
--
-- Conversion sits at the root of every rule and nowhere else, so
-- inversion is pattern matching (conv D c). The rules of ⊨⁰ are those
-- of Muro.Judgement with use vectors, checkBound and combine removed,
-- and the Π / ≡ views folded into the premises. Uses restrict which
-- terms are accepted; they do not change what a term's type is, so the
-- consistency argument can forget them (forget-⇐).
--
-- Data. dty is a spec term of its declared kind. A constructor
-- application is typed as a spine (t-ctor): the parameters come from
-- the type, the arguments are checked along the instantiated
-- constructor telescope (▹), and the residual must be the data type.
-- There is no rule for a bare constructor, so a constructor-headed
-- term has exactly one derivation shape (ctor-inv). match (t-mData)
-- types each branch by BrTy at the constructor's own indices, or skips
-- it when those clash with the scrutinee's (Clash); preservation for
-- ι-data is brApp, a branch applied to the constructor arguments, whose
-- indices are then convertible to the scrutinee's (≈-dty-inj), and
-- Clash-▹: a skipped branch has no constructor application to fire on.
--
-- Proved here:
--   forget-⇒ / forget-⇐   ⊢ is sound for ⊨
--   ⊨-mode                mode weakening along run ≤ evid ≤ spec
--   ⊨-ren                 renaming (contexts related pointwise by Ren)
--   ⊨-sub / ⊨-inst        substitution
--   pres / pres*          preservation: a ⟶ step, taken in any mode,
--                         keeps the type of a derivation in any mode,
--                         given a signature whose bodies have their
--                         declared types (WfSig)
--
-- Every premise of every rule is in a mode ≥ the mode of its
-- conclusion (the equation of a rewrite is read in rwtMode m: evidence,
-- or spec inside a spec term), so substitution and preservation hold
-- in every mode.
--
-- Why not ⊢ itself: ann e A ⟶ e removes the annotation a bidirectional
-- derivation needs (rwt rfl P t has no ⇒ derivation since rfl only
-- checks). Preservation of ⊢ up to re-annotation is not attempted.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Typing where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length; drop)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Vec.Base as Vec using ([]; _∷_; lookup; map)
open import Data.Vec.Properties using (lookup-map)
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
open import Muro.Data
open import Muro.Judgement

------------------------------------------------------------------------
-- Variables: which qty may be used in which mode.
------------------------------------------------------------------------

data VarOk : Mode → Qty → Set where
  v-spec : ∀ {q} → VarOk spec q
  v-run  : ∀ {q} → (q ≡ erased → ⊥) → VarOk run q
  v-evid : ∀ {q} → (q ≡ erased → ⊥) → VarOk evid q

VarOk-mono : ∀ {m m′ q} → m ≤ᵐ m′ → VarOk m q → VarOk m′ q
VarOk-mono {m′ = run}  ≤ᵐ-run (v-run h) = v-run h
VarOk-mono {m′ = evid} ≤ᵐ-run (v-run h) = v-evid h
VarOk-mono {m′ = spec} ≤ᵐ-run (v-run h) = v-spec
VarOk-mono ≤ᵐ-evid v = v
VarOk-mono ≤ᵐ-evsp _ = v-spec
VarOk-mono ≤ᵐ-spec v = v

------------------------------------------------------------------------
-- The judgment.
------------------------------------------------------------------------

infix 3 _,_⊨[_]_∶_ _,_⊨⁰[_]_∶_ _,_⊨_wf _,_⊨[_]_▹_⇝_ _,_⊨[_]_brs⟨_,_,_,_,_⟩_

data _,_⊨⁰[_]_∶_ (σ : Sig) {n} (Γ : Ctx n) : Mode → Tm n → Tm n → Set
data _,_⊨[_]_∶_ (σ : Sig) {n} (Γ : Ctx n) : Mode → Tm n → Tm n → Set
data _,_⊨_wf (σ : Sig) {n} (Γ : Ctx n) : Tm n → Set
-- Arguments along a telescope: σ , Γ ⊨[ m ] T ▹ as ⇝ R consumes as
-- from T and leaves R (up to ≈).
data _,_⊨[_]_▹_⇝_ (σ : Sig) {n} (Γ : Ctx n)
    : Mode → Tm n → List (Tm n) → Tm n → Set
-- A constructor application: constructor j of data type i, arguments
-- as, at the data type applied to the parameters and indices.
data CtorApp (σ : Sig) {n} (Γ : Ctx n) : Mode → ℕ → ℕ → List (Tm n) → Tm n → Set
-- Branches of a match, one per constructor from index ci on.
data _,_⊨[_]_brs⟨_,_,_,_,_⟩_ (σ : Sig) {n} (Γ : Ctx n)
    : Mode → List (Tm n) → ℕ → List (Tm n) → List (Tm n) → Tm (suc n) → ℕ → List Ctor → Set
-- The motive of a match (Judgement.MotiveOk without uses).
Mot⊨ : ∀ (σ : Sig) {n} (Γ : Ctx n) → ℕ → List (Tm n) → List (Qty × Tm 0) → Tm (suc n) → Set

data _,_⊨[_]_∶_ σ Γ where
  conv : ∀ {m e A B}
    → σ , Γ ⊨⁰[ m ] e ∶ A
    → σ ⊢[ spec ] A ≈ B
    → σ , Γ ⊨[ m ] e ∶ B

data _,_⊨_wf σ Γ where
  wf-typ : σ , Γ ⊨ typ wf
  wf-pi  : ∀ {q A B} → σ , Γ ⊨ A wf → σ , ext Γ q A ⊨ B wf → σ , Γ ⊨ pi q A B wf
  wf-el  : ∀ {A} → σ , Γ ⊨[ spec ] A ∶ typ → σ , Γ ⊨ A wf

data _,_⊨⁰[_]_∶_ σ Γ where
  t-var : ∀ {m x}
    → VarOk m (qtyOf Γ x)
    → σ , Γ ⊨⁰[ m ] var x ∶ typOf Γ x

  t-ze  : ∀ {m} → σ , Γ ⊨⁰[ m ] ze ∶ nat
  t-su  : ∀ {m t} → σ , Γ ⊨[ m ] t ∶ nat → σ , Γ ⊨⁰[ m ] su t ∶ nat
  t-one : ∀ {m} → σ , Γ ⊨⁰[ m ] one ∶ unit

  t-nat   : σ , Γ ⊨⁰[ spec ] nat   ∶ typ
  t-unit  : σ , Γ ⊨⁰[ spec ] unit  ∶ typ
  t-empty : σ , Γ ⊨⁰[ spec ] empty ∶ typ

  t-pi : ∀ {q A B}
    → σ , Γ ⊨ A wf
    → σ , ext Γ q A ⊨[ spec ] B ∶ typ
    → σ , Γ ⊨⁰[ spec ] pi q A B ∶ typ

  -- The binder type A is converted to the domain A′ the body is typed
  -- under (⇐-lam of ⊢; ⇒-lam is the case A′ = A).
  t-lam : ∀ {m q A A′ t B}
    → σ , Γ ⊨ A wf
    → σ ⊢[ spec ] A ≈ A′
    → ReuseOk σ q A′
    → σ , ext Γ q A′ ⊨[ m ] t ∶ B
    → σ , Γ ⊨⁰[ m ] lam q A t ∶ pi q A′ B

  t-app-aff : ∀ {m f a A B}
    → σ , Γ ⊨[ m ] f ∶ pi affine A B
    → σ , Γ ⊨[ m ] a ∶ A
    → σ , Γ ⊨⁰[ m ] app f a ∶ inst B a

  t-app-era : ∀ {m f a A B}
    → σ , Γ ⊨[ m ] f ∶ pi erased A B
    → σ , Γ ⊨[ spec ] a ∶ A
    → σ , Γ ⊨⁰[ m ] app f a ∶ inst B a

  t-app-reuse : ∀ {m f a A B}
    → σ , Γ ⊨[ m ] f ∶ pi reuse A B
    → IsData σ A
    → σ , Γ ⊨[ m ] a ∶ A
    → σ , Γ ⊨⁰[ m ] app f a ∶ inst B a

  t-idt : ∀ {A a b}
    → σ , Γ ⊨ A wf
    → σ , Γ ⊨[ spec ] a ∶ A
    → σ , Γ ⊨[ spec ] b ∶ A
    → σ , Γ ⊨⁰[ spec ] idt A a b ∶ typ

  t-rfl : ∀ {m A a b}
    → σ ⊢[ spec ] a ≈ b
    → σ , Γ ⊨⁰[ m ] rfl ∶ idt A a b

  t-rwt : ∀ {m eq A l r P t}
    → σ , Γ ⊨[ rwtMode m ] eq ∶ idt A l r
    → σ , ext Γ affine A ⊨ P wf
    → σ , Γ ⊨[ m ] t ∶ inst P r
    → σ , Γ ⊨⁰[ m ] rwt eq P t ∶ inst P l

  -- The predecessor's quantity is any q: ⊢ binds it at predQty Γ e, and
  -- ⊨ does not depend on which non-erased quantity it was.
  t-mNat : ∀ {m q e P z s}
    → σ , Γ ⊨[ m ] e ∶ nat
    → σ , ext Γ affine nat ⊨ P wf
    → σ , Γ ⊨[ m ] z ∶ inst P ze
    → σ , ext Γ q nat ⊨[ m ] s ∶ motSuc P
    → σ , Γ ⊨⁰[ m ] mNat e P z s ∶ inst P e

  t-mEmp : ∀ {m e P}
    → σ , Γ ⊨[ m ] e ∶ empty
    → σ , ext Γ affine empty ⊨ P wf
    → σ , Γ ⊨⁰[ m ] mEmp e P ∶ inst P e

  t-mUnit : ∀ {m e P u}
    → σ , Γ ⊨[ m ] e ∶ unit
    → σ , ext Γ affine unit ⊨ P wf
    → σ , Γ ⊨[ m ] u ∶ inst P one
    → σ , Γ ⊨⁰[ m ] mUnit e P u ∶ inst P e

  t-dty : ∀ {i d}
    → lookupData σ i ≡ ok d
    → σ , Γ ⊨⁰[ spec ] dty i ∶ dtyType (DataDecl.pqtys d) (DataDecl.idxs d)

  t-ctor : ∀ {m i j as e A}
    → Spine (ctor i j) as e
    → CtorApp σ Γ m i j as A
    → σ , Γ ⊨⁰[ m ] e ∶ A

  t-mData : ∀ {m e di ps is d P bs}
    → σ , Γ ⊨[ m ] e ∶ appsFrom (dty di) (ps ++ is)
    → lookupData σ di ≡ ok d
    → length ps ≡ nparams d
    → length is ≡ nidxs d
    → Mot⊨ σ Γ di ps (DataDecl.idxs d) P
    → σ , Γ ⊨[ m ] bs brs⟨ di , ps , is , P , 0 ⟩ DataDecl.ctors d
    → σ , Γ ⊨⁰[ m ] mData e P bs ∶ motApp P is e

  t-def : ∀ {m i d}
    → lookupDef σ i ≡ ok d
    → allowedDef (Def.dmode d) m ≡ true
    → σ , Γ ⊨⁰[ m ] def i ∶ closed (Def.dtype d)

  t-ann : ∀ {m e A}
    → σ , Γ ⊨ A wf
    → σ , Γ ⊨[ m ] e ∶ A
    → σ , Γ ⊨⁰[ m ] ann e A ∶ A

  t-prod : ∀ {A B}
    → σ , Γ ⊨[ spec ] A ∶ typ
    → σ , Γ ⊨[ spec ] B ∶ typ
    → σ , Γ ⊨⁰[ spec ] prod A B ∶ typ

  t-pair : ∀ {m a b A B}
    → σ , Γ ⊨[ m ] a ∶ A
    → σ , Γ ⊨[ m ] b ∶ B
    → σ , Γ ⊨⁰[ m ] pair a b ∶ prod A B

  -- let (a, b) = e in t: the body under two affine binders, at the
  -- result type weakened past them.
  t-letp : ∀ {m e t A B C}
    → σ , Γ ⊨[ m ] e ∶ prod A B
    → σ , ext (ext Γ affine A) affine (wk B) ⊨[ m ] t ∶ wk (wk C)
    → σ , Γ ⊨⁰[ m ] letp e t ∶ C

data _,_⊨[_]_▹_⇝_ σ Γ where
  a-[] : ∀ {m T R}
    → σ ⊢[ spec ] T ≈ R
    → σ , Γ ⊨[ m ] T ▹ [] ⇝ R
  a-∷  : ∀ {m T q A B a as R}
    → σ ⊢[ spec ] T ≈ pi q A B
    → σ , Γ ⊨[ fieldMode q m ] a ∶ A
    → σ , Γ ⊨[ m ] inst B a ▹ as ⇝ R
    → σ , Γ ⊨[ m ] T ▹ (a ∷ as) ⇝ R

data CtorApp σ Γ where
  ca : ∀ {m i j as ps idxs d c T}
    → lookupData σ i ≡ ok d
    → lookupCtor d j ≡ ok c
    → length ps ≡ nparams d
    → length idxs ≡ nidxs d
    → InstParams σ (closed (Ctor.ctype c)) ps T
    → σ , Γ ⊨[ m ] T ▹ as ⇝ appsFrom (dty i) (ps ++ idxs)
    → CtorApp σ Γ m i j as (appsFrom (dty i) (ps ++ idxs))

data _,_⊨[_]_brs⟨_,_,_,_,_⟩_ σ Γ where
  b-[] : ∀ {m di ps is P ci}
    → σ , Γ ⊨[ m ] [] brs⟨ di , ps , is , P , ci ⟩ []
  b-∷  : ∀ {m di ps is P ci c cs b bs T X}
    → InstParams σ (closed (Ctor.ctype c)) ps T
    → BrTy σ di ci (length ps) T P [] X
    → σ , Γ ⊨[ m ] b ∶ X
    → σ , Γ ⊨[ m ] bs brs⟨ di , ps , is , P , suc ci ⟩ cs
    → σ , Γ ⊨[ m ] (b ∷ bs) brs⟨ di , ps , is , P , ci ⟩ (c ∷ cs)
  b-skip : ∀ {m di ps is P ci c cs b bs T}
    → InstParams σ (closed (Ctor.ctype c)) ps T
    → Clash σ (length ps) is T
    → σ , Γ ⊨[ m ] bs brs⟨ di , ps , is , P , suc ci ⟩ cs
    → σ , Γ ⊨[ m ] (b ∷ bs) brs⟨ di , ps , is , P , ci ⟩ (c ∷ cs)

Mot⊨ σ Γ di ps [] P = σ , ext Γ affine (appsFrom (dty di) ps) ⊨ P wf
Mot⊨ σ Γ di ps ((q , T) ∷ ixs) P =
  σ , ext Γ q (closed T) ⊨[ spec ] P ∶ motiveTail di (renList suc ps ++ (var zero ∷ [])) ixs

-- Conversion composes.
conv-≈ : ∀ {σ n} {Γ : Ctx n} {m e A B}
  → σ , Γ ⊨[ m ] e ∶ A → σ ⊢[ spec ] A ≈ B → σ , Γ ⊨[ m ] e ∶ B
conv-≈ (conv D c) c′ = conv D (≈-trans c c′)

≈-≡ : ∀ {σ m n} {A B : Tm n} → A ≡ B → σ ⊢[ m ] A ≈ B
≈-≡ refl = ≈-refl

⊨-≡ : ∀ {σ n} {Γ : Ctx n} {m e A B}
  → A ≡ B → σ , Γ ⊨[ m ] e ∶ A → σ , Γ ⊨[ m ] e ∶ B
⊨-≡ refl D = D

⊨⁰-≡ : ∀ {σ n} {Γ : Ctx n} {m e A B}
  → A ≡ B → σ , Γ ⊨⁰[ m ] e ∶ A → σ , Γ ⊨⁰[ m ] e ∶ B
⊨⁰-≡ refl D = D

⊨-ctx : ∀ {σ n} {Γ Γ′ : Ctx n} {m e A}
  → Γ ≡ Γ′ → σ , Γ ⊨[ m ] e ∶ A → σ , Γ′ ⊨[ m ] e ∶ A
⊨-ctx refl D = D

-- The telescope of ▹ may be converted.
▹-≈ : ∀ {σ n} {Γ : Ctx n} {m T T′ as R}
  → σ ⊢[ spec ] T ≈ T′ → σ , Γ ⊨[ m ] T ▹ as ⇝ R → σ , Γ ⊨[ m ] T′ ▹ as ⇝ R
▹-≈ c (a-[] c′) = a-[] (≈-trans (≈-sym c) c′)
▹-≈ c (a-∷ c′ Da ar) = a-∷ (≈-trans (≈-sym c) c′) Da ar

-- Application at each quantity, the argument in the mode ⊢ checks it.
app-q : ∀ {σ n} {Γ : Ctx n} {m f a A B} q
  → σ , Γ ⊨[ m ] f ∶ pi q A B → ReuseOk σ q A
  → σ , Γ ⊨[ fieldMode q m ] a ∶ A
  → σ , Γ ⊨[ m ] app f a ∶ inst B a
app-q affine Df _   Da = conv (t-app-aff Df Da) ≈-refl
app-q erased Df _   Da = conv (t-app-era Df Da) ≈-refl
app-q reuse  Df isd Da = conv (t-app-reuse Df isd Da) ≈-refl

------------------------------------------------------------------------
-- ⊢ is sound for ⊨: forget the uses.
------------------------------------------------------------------------

-- The residual of ▹ may be converted.
▹-R : ∀ {σ n} {Γ : Ctx n} {m T as R R′}
  → σ ⊢[ spec ] R ≈ R′ → σ , Γ ⊨[ m ] T ▹ as ⇝ R → σ , Γ ⊨[ m ] T ▹ as ⇝ R′
▹-R c (a-[] c′) = a-[] (≈-trans c′ c)
▹-R c (a-∷ c′ Da ar) = a-∷ c′ Da (▹-R c ar)

-- One more argument at the end of ▹.
▹-snoc : ∀ {σ n} {Γ : Ctx n} {m T as R q A B a}
  → σ , Γ ⊨[ m ] T ▹ as ⇝ R → σ ⊢[ spec ] R ≈ pi q A B
  → σ , Γ ⊨[ fieldMode q m ] a ∶ A
  → σ , Γ ⊨[ m ] T ▹ (as ++ (a ∷ [])) ⇝ inst B a
▹-snoc (a-[] c′) c Da = a-∷ (≈-trans c′ c) Da (a-[] ≈-refl)
▹-snoc (a-∷ c′ Db ar) c Da = a-∷ c′ Db (▹-snoc ar c Da)

forget-⇒ : ∀ {σ n} {Γ : Ctx n} {m e A u}
  → σ , Γ ⊢[ m ] e ⇒ A ⊣ u → σ , Γ ⊨[ m ] e ∶ A
forget-⇐ : ∀ {σ n} {Γ : Ctx n} {m e A u}
  → σ , Γ ⊢[ m ] e ⇐ A ⊣ u → σ , Γ ⊨[ m ] e ∶ A
forget-wf : ∀ {σ n} {Γ : Ctx n} {A}
  → σ , Γ ⊢ A wf → σ , Γ ⊨ A wf
forget-args : ∀ {σ n} {Γ : Ctx n} {m T as R u}
  → σ , Γ ⊢[ m ] T ▹ as ⇝ R ⊣ u → σ , Γ ⊨[ m ] T ▹ as ⇝ R
forget-brs : ∀ {σ n} {Γ : Ctx n} {m bs di ps is P ci cs u}
  → σ , Γ ⊢[ m ] bs brs⟨ di , ps , is , P , ci ⟩ cs ⊣ u
  → σ , Γ ⊨[ m ] bs brs⟨ di , ps , is , P , ci ⟩ cs
forget-mot : ∀ {σ n} {Γ : Ctx n} {di ps ixs P}
  → MotiveOk σ Γ di ps ixs P → Mot⊨ σ Γ di ps ixs P

forget-⇒ (⇒-var-run h) = conv (t-var (v-run h)) ≈-refl
forget-⇒ (⇒-var-evid h) = conv (t-var (v-evid h)) ≈-refl
forget-⇒ ⇒-var-spec = conv (t-var v-spec) ≈-refl
forget-⇒ ⇒-ze = conv t-ze ≈-refl
forget-⇒ (⇒-su D) = conv (t-su (forget-⇐ D)) ≈-refl
forget-⇒ ⇒-one = conv t-one ≈-refl
forget-⇒ ⇒-nat = conv t-nat ≈-refl
forget-⇒ ⇒-unit = conv t-unit ≈-refl
forget-⇒ ⇒-empty = conv t-empty ≈-refl
forget-⇒ (⇒-pi W D) = conv (t-pi (forget-wf W) (forget-⇐ D)) ≈-refl
forget-⇒ (⇒-lam W rok D _) =
  conv (t-lam (forget-wf W) ≈-refl rok (forget-⇒ D)) ≈-refl
forget-⇒ (⇒-app-aff Df c Da _) =
  conv (t-app-aff (conv-≈ (forget-⇒ Df) c) (forget-⇐ Da)) ≈-refl
forget-⇒ (⇒-app-era Df c Da) =
  conv (t-app-era (conv-≈ (forget-⇒ Df) c) (forget-⇐ Da)) ≈-refl
forget-⇒ (⇒-app-reuse Df c isd Da _) =
  conv (t-app-reuse (conv-≈ (forget-⇒ Df) c) isd (forget-⇐ Da)) ≈-refl
forget-⇒ (⇒-idt W Da Db) =
  conv (t-idt (forget-wf W) (forget-⇐ Da) (forget-⇐ Db)) ≈-refl
forget-⇒ (⇒-rwt Deq c W Dt) =
  conv (t-rwt (conv-≈ (forget-⇒ Deq) c) (forget-wf W) (forget-⇐ Dt)) ≈-refl
forget-⇒ (⇒-mNat De W Dz Ds _ _) =
  conv (t-mNat (forget-⇐ De) (forget-wf W) (forget-⇐ Dz) (forget-⇐ Ds)) ≈-refl
forget-⇒ (⇒-mEmp De W) = conv (t-mEmp (forget-⇐ De) (forget-wf W)) ≈-refl
forget-⇒ (⇒-mUnit De W Du _) =
  conv (t-mUnit (forget-⇐ De) (forget-wf W) (forget-⇐ Du)) ≈-refl
forget-⇒ (⇒-dty lk) = conv (t-dty lk) ≈-refl
forget-⇒ (⇒-mData De c lk lps lis M Bs _) =
  conv (t-mData (conv-≈ (forget-⇒ De) c) lk lps lis (forget-mot M) (forget-brs Bs)) ≈-refl
forget-⇒ (⇒-def lk al) = conv (t-def lk al) ≈-refl
forget-⇒ (⇒-ann W D) = conv (t-ann (forget-wf W) (forget-⇐ D)) ≈-refl
forget-⇒ (⇒-prod DA DB) = conv (t-prod (forget-⇐ DA) (forget-⇐ DB)) ≈-refl
forget-⇒ (⇒-pair Da Db _) = conv (t-pair (forget-⇒ Da) (forget-⇒ Db)) ≈-refl
forget-⇒ (⇒-letp De c Dt cT _ _ _) =
  conv (t-letp (conv-≈ (forget-⇒ De) c) (conv-≈ (forget-⇒ Dt) cT)) ≈-refl

forget-⇐ (⇐-conv D c) = conv-≈ (forget-⇒ D) c
forget-⇐ (⇐-lam W cT c rok D _) =
  conv (t-lam (forget-wf W) c rok (forget-⇐ D)) (≈-sym cT)
forget-⇐ (⇐-refl cT c) = conv (t-rfl c) (≈-sym cT)
forget-⇐ (⇐-ctor sp c lk lps lidx lkc ip Ar cR) =
  conv (t-ctor sp (ca lk lkc lps lidx ip (▹-R cR (forget-args Ar)))) (≈-sym c)
forget-⇐ (⇐-pair cT Da Db _) = conv (t-pair (forget-⇐ Da) (forget-⇐ Db)) (≈-sym cT)
forget-⇐ (⇐-letp De c Dt _ _ _) =
  conv (t-letp (conv-≈ (forget-⇒ De) c) (forget-⇐ Dt)) ≈-refl

forget-args args-[] = a-[] ≈-refl
forget-args (args-snoc Ar c Da _) = ▹-snoc (forget-args Ar) c (forget-⇐ Da)

forget-brs brs-[] = b-[]
forget-brs (brs-∷ ip bt Db Bs) = b-∷ ip bt (forget-⇐ Db) (forget-brs Bs)
forget-brs (brs-skip ip cl Bs) = b-skip ip cl (forget-brs Bs)

forget-mot {ixs = []} W = forget-wf W
forget-mot {ixs = (q , T) ∷ ixs} (_ , D) = forget-⇐ D

forget-wf type-Type = wf-typ
forget-wf (type-pi WA WB) = wf-pi (forget-wf WA) (forget-wf WB)
forget-wf (type-el D c) = wf-el (conv-≈ (forget-⇒ D) c)

------------------------------------------------------------------------
-- Mode weakening.
------------------------------------------------------------------------

⊨-mode : ∀ {σ n} {Γ : Ctx n} {m m′ e A}
  → m ≤ᵐ m′ → σ , Γ ⊨[ m ] e ∶ A → σ , Γ ⊨[ m′ ] e ∶ A
⊨⁰-mode : ∀ {σ n} {Γ : Ctx n} {m m′ e A}
  → m ≤ᵐ m′ → σ , Γ ⊨⁰[ m ] e ∶ A → σ , Γ ⊨⁰[ m′ ] e ∶ A
▹-mode : ∀ {σ n} {Γ : Ctx n} {m m′ T as R}
  → m ≤ᵐ m′ → σ , Γ ⊨[ m ] T ▹ as ⇝ R → σ , Γ ⊨[ m′ ] T ▹ as ⇝ R
ca-mode : ∀ {σ n} {Γ : Ctx n} {m m′ i j as A}
  → m ≤ᵐ m′ → CtorApp σ Γ m i j as A → CtorApp σ Γ m′ i j as A
brs-mode : ∀ {σ n} {Γ : Ctx n} {m m′ bs di ps is P ci cs}
  → m ≤ᵐ m′ → σ , Γ ⊨[ m ] bs brs⟨ di , ps , is , P , ci ⟩ cs
  → σ , Γ ⊨[ m′ ] bs brs⟨ di , ps , is , P , ci ⟩ cs

fieldMode-mono : ∀ q {m m′} → m ≤ᵐ m′ → fieldMode q m ≤ᵐ fieldMode q m′
fieldMode-mono erased _ = ≤ᵐ-spec
fieldMode-mono affine h = h
fieldMode-mono reuse  h = h

⊨-mode h (conv D c) = conv (⊨⁰-mode h D) c

⊨⁰-mode h (t-var v) = t-var (VarOk-mono h v)
⊨⁰-mode h t-ze = t-ze
⊨⁰-mode h (t-su D) = t-su (⊨-mode h D)
⊨⁰-mode h t-one = t-one
⊨⁰-mode ≤ᵐ-spec t-nat = t-nat
⊨⁰-mode ≤ᵐ-spec t-unit = t-unit
⊨⁰-mode ≤ᵐ-spec t-empty = t-empty
⊨⁰-mode ≤ᵐ-spec (t-pi W D) = t-pi W D
⊨⁰-mode h (t-lam W c rok D) = t-lam W c rok (⊨-mode h D)
⊨⁰-mode h (t-app-aff Df Da) = t-app-aff (⊨-mode h Df) (⊨-mode h Da)
⊨⁰-mode h (t-app-era Df Da) = t-app-era (⊨-mode h Df) Da
⊨⁰-mode h (t-app-reuse Df isd Da) = t-app-reuse (⊨-mode h Df) isd (⊨-mode h Da)
⊨⁰-mode ≤ᵐ-spec (t-idt W Da Db) = t-idt W Da Db
⊨⁰-mode h (t-rfl c) = t-rfl c
⊨⁰-mode h (t-rwt Deq W Dt) = t-rwt (⊨-mode (rwtMode-mono h) Deq) W (⊨-mode h Dt)
⊨⁰-mode h (t-mNat De W Dz Ds) = t-mNat (⊨-mode h De) W (⊨-mode h Dz) (⊨-mode h Ds)
⊨⁰-mode h (t-mEmp De W) = t-mEmp (⊨-mode h De) W
⊨⁰-mode h (t-mUnit De W Du) = t-mUnit (⊨-mode h De) W (⊨-mode h Du)
⊨⁰-mode ≤ᵐ-spec (t-dty lk) = t-dty lk
⊨⁰-mode h (t-ctor sp c) = t-ctor sp (ca-mode h c)
⊨⁰-mode h (t-mData De lk lps lis M Bs) =
  t-mData (⊨-mode h De) lk lps lis M (brs-mode h Bs)
⊨⁰-mode h (t-def {d = d} lk al) = t-def lk (allowedDef-mono (Def.dmode d) h al)
⊨⁰-mode h (t-ann W D) = t-ann W (⊨-mode h D)
⊨⁰-mode ≤ᵐ-spec (t-prod DA DB) = t-prod DA DB
⊨⁰-mode h (t-pair Da Db) = t-pair (⊨-mode h Da) (⊨-mode h Db)
⊨⁰-mode h (t-letp De Dt) = t-letp (⊨-mode h De) (⊨-mode h Dt)

▹-mode h (a-[] c) = a-[] c
▹-mode h (a-∷ {q = q} c Da ar) = a-∷ c (⊨-mode (fieldMode-mono q h) Da) (▹-mode h ar)

ca-mode h (ca lk lkc lps lidx ip ar) = ca lk lkc lps lidx ip (▹-mode h ar)

brs-mode h b-[] = b-[]
brs-mode h (b-∷ ip bt Db Bs) = b-∷ ip bt (⊨-mode h Db) (brs-mode h Bs)
brs-mode h (b-skip ip cl Bs) = b-skip ip cl (brs-mode h Bs)

------------------------------------------------------------------------
-- Contexts: lookup under ext.
------------------------------------------------------------------------

qty-ext-suc : ∀ {n} (Γ : Ctx n) q A (x : Fin n)
  → qtyOf (ext Γ q A) (suc x) ≡ qtyOf Γ x
qty-ext-suc Γ q A x rewrite lookup-map x wkBind Γ = refl

typ-ext-suc : ∀ {n} (Γ : Ctx n) q A (x : Fin n)
  → typOf (ext Γ q A) (suc x) ≡ wk (typOf Γ x)
typ-ext-suc Γ q A x rewrite lookup-map x wkBind Γ = refl

------------------------------------------------------------------------
-- Renaming. Γ renames into Δ along ρ when qtys agree and types are
-- renamed.
------------------------------------------------------------------------

-- dtyType is closed.
dtyType-ren : ∀ {n k} (ρ : Fin n → Fin k) qs ixs
  → ren ρ (dtyType qs ixs) ≡ dtyType qs ixs
dtyType-ren ρ [] [] = refl
dtyType-ren ρ (q ∷ qs) ixs = cong (pi q typ) (dtyType-ren (lift ρ) qs ixs)
dtyType-ren ρ [] ((q , T) ∷ ixs) rewrite closed-ren ρ T = cong (pi q (closed T)) (dtyType-ren (lift ρ) [] ixs)

dtyType-sub : ∀ {n k} (τ : Fin n → Tm k) qs ixs
  → sub τ (dtyType qs ixs) ≡ dtyType qs ixs
dtyType-sub τ [] [] = refl
dtyType-sub τ (q ∷ qs) ixs = cong (pi q typ) (dtyType-sub (lifts τ) qs ixs)
dtyType-sub τ [] ((q , T) ∷ ixs) rewrite closed-sub τ T = cong (pi q (closed T)) (dtyType-sub (lifts τ) [] ixs)


Ren : ∀ {n k} → (Fin n → Fin k) → Ctx n → Ctx k → Set
Ren ρ Γ Δ = ∀ x → (qtyOf Δ (ρ x) ≡ qtyOf Γ x) × (typOf Δ (ρ x) ≡ ren ρ (typOf Γ x))

Ren-lift : ∀ {n k} {ρ : Fin n → Fin k} {Γ Δ}
  → Ren ρ Γ Δ → ∀ q A → Ren (lift ρ) (ext Γ q A) (ext Δ q (ren ρ A))
Ren-lift {ρ = ρ} r q A zero = refl , sym (ren-wk ρ A)
Ren-lift {ρ = ρ} {Γ} {Δ} r q A (suc x)
  rewrite qty-ext-suc Δ q (ren ρ A) (ρ x) | typ-ext-suc Δ q (ren ρ A) (ρ x)
        | qty-ext-suc Γ q A x | typ-ext-suc Γ q A x | proj₂ (r x) =
  proj₁ (r x) , sym (ren-wk ρ (typOf Γ x))

-- Weakening by one binder.
Ren-wk : ∀ {n} (Γ : Ctx n) q A → Ren suc Γ (ext Γ q A)
Ren-wk Γ q A x = qty-ext-suc Γ q A x , typ-ext-suc Γ q A x

-- The empty context renames into any context.
Ren-closed : ∀ {n} (Γ : Ctx n) → Ren fromZero ε Γ
Ren-closed Γ ()

⊨-ren : ∀ {σ n k} {ρ : Fin n → Fin k} {Γ Δ m e A}
  → Ren ρ Γ Δ → σ , Γ ⊨[ m ] e ∶ A → σ , Δ ⊨[ m ] ren ρ e ∶ ren ρ A
⊨⁰-ren : ∀ {σ n k} {ρ : Fin n → Fin k} {Γ Δ m e A}
  → Ren ρ Γ Δ → σ , Γ ⊨⁰[ m ] e ∶ A → σ , Δ ⊨⁰[ m ] ren ρ e ∶ ren ρ A
wf-ren : ∀ {σ n k} {ρ : Fin n → Fin k} {Γ Δ A}
  → Ren ρ Γ Δ → σ , Γ ⊨ A wf → σ , Δ ⊨ ren ρ A wf
▹-ren : ∀ {σ n k} {ρ : Fin n → Fin k} {Γ Δ m T as R}
  → Ren ρ Γ Δ → σ , Γ ⊨[ m ] T ▹ as ⇝ R
  → σ , Δ ⊨[ m ] ren ρ T ▹ renList ρ as ⇝ ren ρ R
ca-ren : ∀ {σ n k} {ρ : Fin n → Fin k} {Γ Δ m i j as A}
  → Ren ρ Γ Δ → CtorApp σ Γ m i j as A → CtorApp σ Δ m i j (renList ρ as) (ren ρ A)
brs-ren : ∀ {σ n k} {ρ : Fin n → Fin k} {Γ Δ m bs di ps is P ci cs}
  → Ren ρ Γ Δ → σ , Γ ⊨[ m ] bs brs⟨ di , ps , is , P , ci ⟩ cs
  → σ , Δ ⊨[ m ] renList ρ bs brs⟨ di , renList ρ ps , renList ρ is , ren (lift ρ) P , ci ⟩ cs
mot-ren : ∀ {σ n k} {ρ : Fin n → Fin k} {Γ Δ di ps ixs P}
  → Ren ρ Γ Δ → Mot⊨ σ Γ di ps ixs P → Mot⊨ σ Δ di (renList ρ ps) ixs (ren (lift ρ) P)

⊨-ren {ρ = ρ} r (conv D c) = conv (⊨⁰-ren r D) (≈-ren ρ c)

⊨⁰-ren {ρ = ρ} {Γ} {Δ} {m} r (t-var {x = x} v) with r x
... | eq , et =
  subst (λ T → _ , Δ ⊨⁰[ m ] var (ρ x) ∶ T) et
    (t-var (subst (VarOk m) (sym eq) v))
⊨⁰-ren r t-ze = t-ze
⊨⁰-ren r (t-su D) = t-su (⊨-ren r D)
⊨⁰-ren r t-one = t-one
⊨⁰-ren r t-nat = t-nat
⊨⁰-ren r t-unit = t-unit
⊨⁰-ren r t-empty = t-empty
⊨⁰-ren r (t-pi W D) = t-pi (wf-ren r W) (⊨-ren (Ren-lift r _ _) D)
⊨⁰-ren {ρ = ρ} r (t-lam {q = q} W c rok D) =
  t-lam (wf-ren r W) (≈-ren ρ c) (ReuseOk-ren ρ q rok) (⊨-ren (Ren-lift r _ _) D)
⊨⁰-ren {ρ = ρ} r (t-app-aff {a = a} {B = B} Df Da) rewrite ren-inst ρ B a =
  t-app-aff (⊨-ren r Df) (⊨-ren r Da)
⊨⁰-ren {ρ = ρ} r (t-app-era {a = a} {B = B} Df Da) rewrite ren-inst ρ B a =
  t-app-era (⊨-ren r Df) (⊨-ren r Da)
⊨⁰-ren {ρ = ρ} r (t-app-reuse {a = a} {B = B} Df isd Da) rewrite ren-inst ρ B a =
  t-app-reuse (⊨-ren r Df) (IsData-ren ρ isd) (⊨-ren r Da)
⊨⁰-ren r (t-idt W Da Db) = t-idt (wf-ren r W) (⊨-ren r Da) (⊨-ren r Db)
⊨⁰-ren {ρ = ρ} r (t-rfl c) = t-rfl (≈-ren ρ c)
⊨⁰-ren {ρ = ρ} r (t-rwt {l = l} {r = r′} {P = P} Deq W Dt) rewrite ren-inst ρ P l =
  t-rwt (⊨-ren r Deq) (wf-ren (Ren-lift r _ _) W)
    (⊨-≡ (ren-inst ρ P r′) (⊨-ren r Dt))
⊨⁰-ren {ρ = ρ} r (t-mNat {e = e} {P = P} De W Dz Ds) rewrite ren-inst ρ P e =
  t-mNat (⊨-ren r De) (wf-ren (Ren-lift r _ _) W)
    (⊨-≡ (ren-inst ρ P ze) (⊨-ren r Dz))
    (⊨-≡ (ren-motSuc ρ P) (⊨-ren (Ren-lift r _ _) Ds))
⊨⁰-ren {ρ = ρ} r (t-mEmp {e = e} {P = P} De W) rewrite ren-inst ρ P e =
  t-mEmp (⊨-ren r De) (wf-ren (Ren-lift r _ _) W)
⊨⁰-ren {ρ = ρ} r (t-mUnit {e = e} {P = P} De W Du) rewrite ren-inst ρ P e =
  t-mUnit (⊨-ren r De) (wf-ren (Ren-lift r _ _) W)
    (⊨-≡ (ren-inst ρ P one) (⊨-ren r Du))
⊨⁰-ren {ρ = ρ} r (t-dty {d = d} lk) rewrite dtyType-ren ρ (DataDecl.pqtys d) (DataDecl.idxs d) =
  t-dty lk
⊨⁰-ren {ρ = ρ} r (t-ctor sp c) = t-ctor (Spine-ren ρ sp) (ca-ren r c)
⊨⁰-ren {ρ = ρ} r (t-mData {e = e} {di} {ps} {is} {P = P} De lk lps lis M Bs)
  rewrite ren-motApp ρ P is e =
  t-mData (⊨-≡ (trans (ren-appsFrom ρ (dty di) (ps ++ is)) (cong (appsFrom (dty di)) (renList-++ ρ ps is)))
             (⊨-ren r De))
    lk (trans (renList-length ρ ps) lps) (trans (renList-length ρ is) lis)
    (mot-ren r M) (brs-ren r Bs)
⊨⁰-ren {ρ = ρ} r (t-def {d = d} lk al) rewrite closed-ren ρ (Def.dtype d) = t-def lk al
⊨⁰-ren r (t-ann W D) = t-ann (wf-ren r W) (⊨-ren r D)
⊨⁰-ren r (t-prod DA DB) = t-prod (⊨-ren r DA) (⊨-ren r DB)
⊨⁰-ren r (t-pair Da Db) = t-pair (⊨-ren r Da) (⊨-ren r Db)
⊨⁰-ren {ρ = ρ} r (t-letp {A = A} {B} {C} De Dt) =
  t-letp (⊨-ren r De)
    (⊨-≡ (trans (ren-wk (lift ρ) (wk C)) (cong wk (ren-wk ρ C)))
      (⊨-ctx (cong (ext _ affine) (ren-wk ρ B))
        (⊨-ren (Ren-lift (Ren-lift r affine A) affine (wk B)) Dt)))

▹-ren {ρ = ρ} r (a-[] c) = a-[] (≈-ren ρ c)
▹-ren {ρ = ρ} r (a-∷ {B = B} {a = a} c Da ar) =
  a-∷ (≈-ren ρ c) (⊨-ren r Da)
    (subst (λ T → _ , _ ⊨[ _ ] T ▹ _ ⇝ _) (ren-inst ρ B a) (▹-ren r ar))

ca-ren {ρ = ρ} r (ca {i = i} {ps = ps} {idxs} {c = c} lk lkc lps lidx ip ar)
  rewrite ren-appsFrom ρ (dty i) (ps ++ idxs) | renList-++ ρ ps idxs =
  ca lk lkc (trans (renList-length ρ ps) lps) (trans (renList-length ρ idxs) lidx)
    (subst (λ T → InstParams _ T _ _) (closed-ren ρ (Ctor.ctype c)) (InstParams-ren ρ ip))
    (subst (λ R → _ , _ ⊨[ _ ] _ ▹ _ ⇝ R)
      (trans (ren-appsFrom ρ (dty i) (ps ++ idxs))
        (cong (appsFrom (dty i)) (renList-++ ρ ps idxs)))
      (▹-ren r ar))

brs-ren r b-[] = b-[]
brs-ren {ρ = ρ} r (b-∷ {ps = ps} {c = c} ip bt Db Bs) =
  b-∷ (subst (λ T → InstParams _ T _ _) (closed-ren ρ (Ctor.ctype c)) (InstParams-ren ρ ip))
    (subst (λ k → BrTy _ _ _ k _ _ _ _) (sym (renList-length ρ ps)) (BrTy-ren ρ bt))
    (⊨-ren r Db) (brs-ren r Bs)
brs-ren {ρ = ρ} r (b-skip {ps = ps} {c = c} ip cl Bs) =
  b-skip (subst (λ T → InstParams _ T _ _) (closed-ren ρ (Ctor.ctype c)) (InstParams-ren ρ ip))
    (subst (λ k → Clash _ k _ _) (sym (renList-length ρ ps)) (Clash-ren ρ cl))
    (brs-ren r Bs)

mot-ren {ρ = ρ} {di = di} {ps = ps} {ixs = []} r W =
  subst (λ A → _ , ext _ affine A ⊨ _ wf) (ren-appsFrom ρ (dty di) ps)
    (wf-ren (Ren-lift r _ _) W)
mot-ren {ρ = ρ} {di = di} {ps = ps} {ixs = (q , T) ∷ ixs} r D =
  ⊨-≡ (trans (ren-motiveTail (lift ρ) di _ ixs) (cong (λ xs → motiveTail di xs ixs) (renList-acc ρ ps)))
    (⊨-ctx (cong (ext _ q) (closed-ren ρ T)) (⊨-ren (Ren-lift r q (closed T)) D))

wf-ren r wf-typ = wf-typ
wf-ren r (wf-pi WA WB) = wf-pi (wf-ren r WA) (wf-ren (Ren-lift r _ _) WB)
wf-ren r (wf-el D) = wf-el (⊨-ren r D)

-- A closed derivation holds in any context.
closed-⊨ : ∀ {σ n} {Γ : Ctx n} {m e A}
  → σ , ε ⊨[ m ] e ∶ A → σ , Γ ⊨[ m ] closed e ∶ closed A
closed-⊨ {Γ = Γ} D = ⊨-ren (Ren-closed Γ) D

------------------------------------------------------------------------
-- Substitution. τ maps Γ into Δ when each τ x has the (substituted)
-- type of x, in mode m₀ if x is usable computationally and in spec if
-- x is erased. m₀ ≤ m: the substituted terms are in a mode below the
-- derivation's, and every premise is in a mode ≥ its conclusion's.
------------------------------------------------------------------------

modeFor : Qty → Mode → Mode
modeFor erased _ = spec
modeFor affine m = m
modeFor reuse  m = m

-- The mode of a binder's argument is at or above the derivation's.
≤ᵐ-modeFor : ∀ q m → m ≤ᵐ modeFor q m
≤ᵐ-modeFor erased m = ≤ᵐ-spec-top
≤ᵐ-modeFor affine m = ≤ᵐ-refl
≤ᵐ-modeFor reuse  m = ≤ᵐ-refl

varOk-modeFor : ∀ q m₀ → VarOk (modeFor q m₀) q
varOk-modeFor erased m₀ = v-spec
varOk-modeFor affine run  = v-run (λ ())
varOk-modeFor affine evid = v-evid (λ ())
varOk-modeFor affine spec = v-spec
varOk-modeFor reuse  run  = v-run (λ ())
varOk-modeFor reuse  evid = v-evid (λ ())
varOk-modeFor reuse  spec = v-spec

-- A variable usable in mode m, substituted by a term in mode m₀ ≤ m.
modeFor-≤ : ∀ {m m₀ q} → VarOk m q → m₀ ≤ᵐ m → modeFor q m₀ ≤ᵐ m
modeFor-≤ v-spec _ = ≤ᵐ-spec-top
modeFor-≤ {q = erased} (v-run h) _ = ⊥-elim (h refl)
modeFor-≤ {q = affine} (v-run h) lm = lm
modeFor-≤ {q = reuse}  (v-run h) lm = lm
modeFor-≤ {q = erased} (v-evid h) _ = ⊥-elim (h refl)
modeFor-≤ {q = affine} (v-evid h) lm = lm
modeFor-≤ {q = reuse}  (v-evid h) lm = lm

Subst : ∀ {n k} → Sig → Mode → (Fin n → Tm k) → Ctx n → Ctx k → Set
Subst σ m₀ τ Γ Δ = ∀ x → σ , Δ ⊨[ modeFor (qtyOf Γ x) m₀ ] τ x ∶ sub τ (typOf Γ x)

Subst-lifts : ∀ {σ n k m₀} {τ : Fin n → Tm k} {Γ Δ}
  → Subst σ m₀ τ Γ Δ → ∀ q A → Subst σ m₀ (lifts τ) (ext Γ q A) (ext Δ q (sub τ A))
Subst-lifts {m₀ = m₀} {τ} s q A zero =
  conv (t-var (varOk-modeFor q m₀)) (≈-≡ (sym (sub-wk τ A)))
Subst-lifts {τ = τ} {Γ} {Δ} s q A (suc x)
  rewrite qty-ext-suc Γ q A x | typ-ext-suc Γ q A x | sub-wk τ (typOf Γ x) =
  ⊨-ren (Ren-wk Δ q (sub τ A)) (s x)

⊨-sub : ∀ {σ n k m₀ m} {τ : Fin n → Tm k} {Γ Δ e A}
  → m₀ ≤ᵐ m → Subst σ m₀ τ Γ Δ
  → σ , Γ ⊨[ m ] e ∶ A → σ , Δ ⊨[ m ] sub τ e ∶ sub τ A
⊨⁰-sub : ∀ {σ n k m₀ m} {τ : Fin n → Tm k} {Γ Δ e A}
  → m₀ ≤ᵐ m → Subst σ m₀ τ Γ Δ
  → σ , Γ ⊨⁰[ m ] e ∶ A → σ , Δ ⊨[ m ] sub τ e ∶ sub τ A
wf-sub : ∀ {σ n k m₀} {τ : Fin n → Tm k} {Γ Δ A}
  → Subst σ m₀ τ Γ Δ
  → σ , Γ ⊨ A wf → σ , Δ ⊨ sub τ A wf
▹-sub : ∀ {σ n k m₀ m} {τ : Fin n → Tm k} {Γ Δ T as R}
  → m₀ ≤ᵐ m → Subst σ m₀ τ Γ Δ
  → σ , Γ ⊨[ m ] T ▹ as ⇝ R → σ , Δ ⊨[ m ] sub τ T ▹ subList τ as ⇝ sub τ R
ca-sub : ∀ {σ n k m₀ m} {τ : Fin n → Tm k} {Γ Δ i j as A}
  → m₀ ≤ᵐ m → Subst σ m₀ τ Γ Δ
  → CtorApp σ Γ m i j as A → CtorApp σ Δ m i j (subList τ as) (sub τ A)
brs-sub : ∀ {σ n k m₀ m} {τ : Fin n → Tm k} {Γ Δ bs di ps is P ci cs}
  → m₀ ≤ᵐ m → Subst σ m₀ τ Γ Δ
  → σ , Γ ⊨[ m ] bs brs⟨ di , ps , is , P , ci ⟩ cs
  → σ , Δ ⊨[ m ] subList τ bs brs⟨ di , subList τ ps , subList τ is , sub (lifts τ) P , ci ⟩ cs
mot-sub : ∀ {σ n k m₀} {τ : Fin n → Tm k} {Γ Δ di ps ixs P}
  → Subst σ m₀ τ Γ Δ
  → Mot⊨ σ Γ di ps ixs P → Mot⊨ σ Δ di (subList τ ps) ixs (sub (lifts τ) P)

≤-fieldMode : ∀ {m₀ m} → m₀ ≤ᵐ m → ∀ q → m₀ ≤ᵐ fieldMode q m
≤-fieldMode _  erased = ≤ᵐ-spec-top
≤-fieldMode lm affine = lm
≤-fieldMode lm reuse  = lm

⊨-sub {τ = τ} lm s (conv D c) = conv-≈ (⊨⁰-sub lm s D) (≈-sub τ c)

⊨⁰-sub lm s (t-var {x = x} v) = ⊨-mode (modeFor-≤ v lm) (s x)
⊨⁰-sub lm s t-ze = conv t-ze ≈-refl
⊨⁰-sub lm s (t-su D) = conv (t-su (⊨-sub lm s D)) ≈-refl
⊨⁰-sub lm s t-one = conv t-one ≈-refl
⊨⁰-sub lm s t-nat = conv t-nat ≈-refl
⊨⁰-sub lm s t-unit = conv t-unit ≈-refl
⊨⁰-sub lm s t-empty = conv t-empty ≈-refl
⊨⁰-sub lm s (t-pi W D) =
  conv (t-pi (wf-sub s W) (⊨-sub ≤ᵐ-spec-top (Subst-lifts s _ _) D)) ≈-refl
⊨⁰-sub {τ = τ} lm s (t-lam {q = q} W c rok D) =
  conv (t-lam (wf-sub s W) (≈-sub τ c) (ReuseOk-sub τ q rok)
          (⊨-sub lm (Subst-lifts s _ _) D)) ≈-refl
⊨⁰-sub {τ = τ} lm s (t-app-aff {a = a} {B = B} Df Da) =
  conv (t-app-aff (⊨-sub lm s Df) (⊨-sub lm s Da)) (≈-≡ (sym (sub-inst τ B a)))
⊨⁰-sub {τ = τ} lm s (t-app-era {a = a} {B = B} Df Da) =
  conv (t-app-era (⊨-sub lm s Df) (⊨-sub ≤ᵐ-spec-top s Da))
    (≈-≡ (sym (sub-inst τ B a)))
⊨⁰-sub {τ = τ} lm s (t-app-reuse {a = a} {B = B} Df isd Da) =
  conv (t-app-reuse (⊨-sub lm s Df) (IsData-sub τ isd) (⊨-sub lm s Da))
    (≈-≡ (sym (sub-inst τ B a)))
⊨⁰-sub lm s (t-idt W Da Db) =
  conv (t-idt (wf-sub s W) (⊨-sub ≤ᵐ-spec-top s Da) (⊨-sub ≤ᵐ-spec-top s Db))
    ≈-refl
⊨⁰-sub {τ = τ} lm s (t-rfl c) = conv (t-rfl (≈-sub τ c)) ≈-refl
⊨⁰-sub {τ = τ} lm s (t-rwt {l = l} {r = r} {P = P} Deq W Dt) =
  conv (t-rwt (⊨-sub (≤ᵐ-trans lm (≤ᵐ-rwtMode _)) s Deq) (wf-sub (Subst-lifts s _ _) W)
          (⊨-≡ (sub-inst τ P r) (⊨-sub lm s Dt)))
    (≈-≡ (sym (sub-inst τ P l)))
⊨⁰-sub {τ = τ} lm s (t-mNat {e = e} {P = P} De W Dz Ds) =
  conv (t-mNat (⊨-sub lm s De) (wf-sub (Subst-lifts s _ _) W)
          (⊨-≡ (sub-inst τ P ze) (⊨-sub lm s Dz))
          (⊨-≡ (sub-motSuc τ P) (⊨-sub lm (Subst-lifts s _ _) Ds)))
    (≈-≡ (sym (sub-inst τ P e)))
⊨⁰-sub {τ = τ} lm s (t-mEmp {e = e} {P = P} De W) =
  conv (t-mEmp (⊨-sub lm s De) (wf-sub (Subst-lifts s _ _) W))
    (≈-≡ (sym (sub-inst τ P e)))
⊨⁰-sub {τ = τ} lm s (t-mUnit {e = e} {P = P} De W Du) =
  conv (t-mUnit (⊨-sub lm s De) (wf-sub (Subst-lifts s _ _) W)
          (⊨-≡ (sub-inst τ P one) (⊨-sub lm s Du)))
    (≈-≡ (sym (sub-inst τ P e)))
⊨⁰-sub {τ = τ} lm s (t-dty {d = d} lk) =
  conv (t-dty lk) (≈-≡ (sym (dtyType-sub τ (DataDecl.pqtys d) (DataDecl.idxs d))))
⊨⁰-sub {τ = τ} lm s (t-ctor sp c) = conv (t-ctor (Spine-sub τ sp) (ca-sub lm s c)) ≈-refl
⊨⁰-sub {τ = τ} lm s (t-mData {e = e} {di} {ps} {is} {P = P} De lk lps lis M Bs) =
  conv (t-mData (⊨-≡ (trans (sub-appsFrom τ (dty di) (ps ++ is)) (cong (appsFrom (dty di)) (subList-++ τ ps is)))
                   (⊨-sub lm s De))
          lk (trans (subList-length τ ps) lps) (trans (subList-length τ is) lis)
          (mot-sub s M) (brs-sub lm s Bs))
    (≈-≡ (sym (sub-motApp τ P is e)))
⊨⁰-sub {τ = τ} lm s (t-def {d = d} lk al) =
  conv (t-def lk al) (≈-≡ (sym (closed-sub τ (Def.dtype d))))
⊨⁰-sub lm s (t-ann W D) = conv (t-ann (wf-sub s W) (⊨-sub lm s D)) ≈-refl
⊨⁰-sub lm s (t-prod DA DB) =
  conv (t-prod (⊨-sub ≤ᵐ-spec-top s DA) (⊨-sub ≤ᵐ-spec-top s DB)) ≈-refl
⊨⁰-sub lm s (t-pair Da Db) = conv (t-pair (⊨-sub lm s Da) (⊨-sub lm s Db)) ≈-refl
⊨⁰-sub {τ = τ} lm s (t-letp {A = A} {B} {C} De Dt) =
  conv (t-letp (⊨-sub lm s De)
          (⊨-≡ (trans (sub-wk (lifts τ) (wk C)) (cong wk (sub-wk τ C)))
            (⊨-ctx (cong (ext _ affine) (sub-wk τ B))
              (⊨-sub lm (Subst-lifts (Subst-lifts s affine A) affine (wk B)) Dt))))
    ≈-refl

▹-sub {τ = τ} lm s (a-[] c) = a-[] (≈-sub τ c)
▹-sub {τ = τ} lm s (a-∷ {q = q} {B = B} {a = a} c Da ar) =
  a-∷ (≈-sub τ c) (⊨-sub (≤-fieldMode lm q) s Da)
    (subst (λ T → _ , _ ⊨[ _ ] T ▹ _ ⇝ _) (sub-inst τ B a) (▹-sub lm s ar))

ca-sub {τ = τ} lm s (ca {i = i} {ps = ps} {idxs} {c = c} lk lkc lps lidx ip ar)
  rewrite sub-appsFrom τ (dty i) (ps ++ idxs) | subList-++ τ ps idxs =
  ca lk lkc (trans (subList-length τ ps) lps) (trans (subList-length τ idxs) lidx)
    (subst (λ T → InstParams _ T _ _) (closed-sub τ (Ctor.ctype c)) (InstParams-sub τ ip))
    (subst (λ R → _ , _ ⊨[ _ ] _ ▹ _ ⇝ R)
      (trans (sub-appsFrom τ (dty i) (ps ++ idxs))
        (cong (appsFrom (dty i)) (subList-++ τ ps idxs)))
      (▹-sub lm s ar))

brs-sub lm s b-[] = b-[]
brs-sub {τ = τ} lm s (b-∷ {ps = ps} {c = c} ip bt Db Bs) =
  b-∷ (subst (λ T → InstParams _ T _ _) (closed-sub τ (Ctor.ctype c)) (InstParams-sub τ ip))
    (subst (λ k → BrTy _ _ _ k _ _ _ _) (sym (subList-length τ ps)) (BrTy-sub τ bt))
    (⊨-sub lm s Db) (brs-sub lm s Bs)
brs-sub {τ = τ} lm s (b-skip {ps = ps} {c = c} ip cl Bs) =
  b-skip (subst (λ T → InstParams _ T _ _) (closed-sub τ (Ctor.ctype c)) (InstParams-sub τ ip))
    (subst (λ k → Clash _ k _ _) (sym (subList-length τ ps)) (Clash-sub τ cl))
    (brs-sub lm s Bs)

mot-sub {τ = τ} {di = di} {ps = ps} {ixs = []} s W =
  subst (λ A → _ , ext _ affine A ⊨ _ wf) (sub-appsFrom τ (dty di) ps)
    (wf-sub (Subst-lifts s _ _) W)
mot-sub {τ = τ} {di = di} {ps = ps} {ixs = (q , T) ∷ ixs} s D =
  ⊨-≡ (trans (sub-motiveTail (lifts τ) di _ ixs) (cong (λ xs → motiveTail di xs ixs) (subList-acc τ ps)))
    (⊨-ctx (cong (ext _ q) (closed-sub τ T)) (⊨-sub ≤ᵐ-spec-top (Subst-lifts s q (closed T)) D))

wf-sub s wf-typ = wf-typ
wf-sub s (wf-pi WA WB) = wf-pi (wf-sub s WA) (wf-sub (Subst-lifts s _ _) WB)
wf-sub s (wf-el D) = wf-el (⊨-sub ≤ᵐ-spec-top s D)

-- Instantiating the last binder.
Subst-inst : ∀ {σ n m₀} {Γ : Ctx n} q A {a}
  → σ , Γ ⊨[ modeFor q m₀ ] a ∶ A
  → Subst σ m₀ (instσ a) (ext Γ q A) Γ
Subst-inst q A {a} Da zero = ⊨-≡ (sym (inst-wk A a)) Da
Subst-inst {m₀ = m₀} {Γ} q A {a} Da (suc x)
  rewrite qty-ext-suc Γ q A x | typ-ext-suc Γ q A x | inst-wk (typOf Γ x) a =
  conv (t-var (varOk-modeFor (qtyOf Γ x) m₀)) ≈-refl

⊨-inst : ∀ {σ n m₀ m} {Γ : Ctx n} {q A t B a}
  → m₀ ≤ᵐ m
  → σ , ext Γ q A ⊨[ m ] t ∶ B
  → σ , Γ ⊨[ modeFor q m₀ ] a ∶ A
  → σ , Γ ⊨[ m ] inst t a ∶ inst B a
⊨-inst {q = q} {A} lm D Da = ⊨-sub lm (Subst-inst q A Da) D

------------------------------------------------------------------------
-- Preservation.
------------------------------------------------------------------------

-- Every def body has its declared type, in its declared mode.
WfSig : Sig → Set
WfSig σ = ∀ i d → lookupDef σ i ≡ ok d
  → σ , ε ⊨[ Def.dmode d ] Def.dbody d ∶ Def.dtype d

WfSig-empty : WfSig σ-empty
WfSig-empty _ _ ()

allowedDef→≤ᵐ : ∀ d m → allowedDef d m ≡ true → d ≤ᵐ m
allowedDef→≤ᵐ run  _    _ = ≤ᵐ-run
allowedDef→≤ᵐ evid run  ()
allowedDef→≤ᵐ evid evid _ = ≤ᵐ-evid
allowedDef→≤ᵐ evid spec _ = ≤ᵐ-evsp
allowedDef→≤ᵐ spec run  ()
allowedDef→≤ᵐ spec evid ()
allowedDef→≤ᵐ spec spec _ = ≤ᵐ-spec

------------------------------------------------------------------------
-- Constructor spines have one derivation shape.
------------------------------------------------------------------------

ctor-inv : ∀ {σ n} {Γ : Ctx n} {m i j as e A}
  → Spine (ctor i j) as e → σ , Γ ⊨⁰[ m ] e ∶ A → CtorApp σ Γ m i j as A
ctor-inv sp (t-ctor sp′ c) with Spine-unique head-ctor head-ctor sp sp′
... | refl , refl = c
ctor-inv (sp-snoc sp) (t-app-aff (conv Df c) _) with ctor-inv sp Df
... | ca {i = i} {ps = ps} {idxs} _ _ _ _ _ _ =
  ⊥-elim (≈-Spine-shape dh-dty (Spine-appsFrom (dty i) (ps ++ idxs)) h-pi c)
ctor-inv (sp-snoc sp) (t-app-era (conv Df c) _) with ctor-inv sp Df
... | ca {i = i} {ps = ps} {idxs} _ _ _ _ _ _ =
  ⊥-elim (≈-Spine-shape dh-dty (Spine-appsFrom (dty i) (ps ++ idxs)) h-pi c)
ctor-inv (sp-snoc sp) (t-app-reuse (conv Df c) _ _) with ctor-inv sp Df
... | ca {i = i} {ps = ps} {idxs} _ _ _ _ _ _ =
  ⊥-elim (≈-Spine-shape dh-dty (Spine-appsFrom (dty i) (ps ++ idxs)) h-pi c)
ctor-inv () (t-var _)
ctor-inv () t-ze
ctor-inv () (t-su _)
ctor-inv () t-one
ctor-inv () t-nat
ctor-inv () t-unit
ctor-inv () t-empty
ctor-inv () (t-pi _ _)
ctor-inv () (t-lam _ _ _ _)
ctor-inv () (t-idt _ _ _)
ctor-inv () (t-rfl _)
ctor-inv () (t-rwt _ _ _)
ctor-inv () (t-mNat _ _ _ _)
ctor-inv () (t-mEmp _ _)
ctor-inv () (t-mUnit _ _ _)
ctor-inv () (t-dty _)
ctor-inv () (t-mData _ _ _ _ _ _)
ctor-inv () (t-def _ _)
ctor-inv () (t-ann _ _)
ctor-inv () (t-prod _ _)
ctor-inv () (t-pair _ _)
ctor-inv () (t-letp _ _)

------------------------------------------------------------------------
-- Branches: the branch for constructor k.
------------------------------------------------------------------------

-- The branch for constructor k: typed by BrTy, or skipped on a clash.
data BrAt (σ : Sig) {n} (Γ : Ctx n) (m : Mode) (di np : ℕ) (ps is : List (Tm n))
          (P : Tm (suc n)) (j : ℕ) (c : Ctor) (b : Tm n) : Set where
  br-typed : ∀ {T X}
    → InstParams σ (closed (Ctor.ctype c)) ps T
    → BrTy σ di j np T P [] X
    → σ , Γ ⊨[ m ] b ∶ X
    → BrAt σ Γ m di np ps is P j c b
  br-clash : ∀ {T}
    → InstParams σ (closed (Ctor.ctype c)) ps T
    → Clash σ np is T
    → BrAt σ Γ m di np ps is P j c b

brs-lookup : ∀ {σ n} {Γ : Ctx n} {m bs di ps is P ci cs k b c}
  → σ , Γ ⊨[ m ] bs brs⟨ di , ps , is , P , ci ⟩ cs
  → lookupList bs k ≡ ok b → lookupList cs k ≡ ok c
  → BrAt σ Γ m di (length ps) ps is P (ci + k) c b
brs-lookup {σ = σ} {di = di} {P = P} {ci = ci} {k = zero} (b-∷ {T = T} {X = X} ip bt Db Bs) refl refl =
  br-typed ip (subst (λ j → BrTy σ di j _ T P [] X) (sym (+-identityʳ ci)) bt) Db
brs-lookup {k = zero} (b-skip ip cl Bs) refl refl = br-clash ip cl
brs-lookup {σ = σ} {di = di} {ps = ps} {P = P} {ci = ci} {k = suc k} (b-∷ ip bt Db Bs) lb lc
  with brs-lookup Bs lb lc
... | br-typed {T = T} {X = X} ip′ bt′ Db′ =
  br-typed ip′ (subst (λ j → BrTy σ di j (length ps) T P [] X) (sym (+-suc ci k)) bt′) Db′
... | br-clash ip′ cl = br-clash ip′ cl
brs-lookup {σ = σ} {di = di} {ps = ps} {P = P} {ci = ci} {k = suc k} (b-skip ip cl Bs) lb lc
  with brs-lookup Bs lb lc
... | br-typed {T = T} {X = X} ip′ bt′ Db′ =
  br-typed ip′ (subst (λ j → BrTy σ di j (length ps) T P [] X) (sym (+-suc ci k)) bt′) Db′
... | br-clash ip′ cl = br-clash ip′ cl
brs-lookup {k = zero} b-[] () _
brs-lookup {k = suc _} b-[] () _

-- A branch applied to the constructor arguments has the motive at the
-- indices of the constructor's target and at the constructor
-- application. The telescope ends in a dty spine, which is what
-- separates bt-pi from bt-end at each step; at the end the target is
-- convertible to the type of the application, so their indices agree.
brApp : ∀ {σ n} {Γ : Ctx n} {m i j np T P acc X b R qs} as
  → BrTy σ i j np T P acc X
  → σ , Γ ⊨[ m ] b ∶ X
  → σ , Γ ⊨[ m ] T ▹ as ⇝ R
  → σ ⊢[ spec ] R ≈ appsFrom (dty i) qs
  → σ , Γ ⊨[ m ] appsFrom b as ∶ motApp P (drop np qs) (appsFrom (ctor i j) (acc ++ as))
brApp {i = i} {np = np} {P = P} {acc = acc} {qs = qs} [] (bt-end sp c) Db (a-[] c′) cR rewrite ++-identityʳ acc =
  conv-≈ Db
    (≈-motApp P
      (≈L-drop np (proj₂ (≈-dty-inj sp (Spine-appsFrom (dty i) qs) (≈-trans (≈-sym c) (≈-trans c′ cR)))))
      ≈-refl)
brApp {i = i} {qs = qs} [] (bt-pi c _ _) Db (a-[] c′) cR =
  ⊥-elim (≈-Spine-shape dh-dty (Spine-appsFrom (dty i) qs) h-pi (≈-trans (≈-sym cR) (≈-trans (≈-sym c′) c)))
brApp (a ∷ as) (bt-end sp c) Db (a-∷ c′ _ _) _ =
  ⊥-elim (≈-Spine-shape dh-dty sp h-pi (≈-trans (≈-sym c) c′))
brApp {σ = σ} {Γ = Γ} {m} {i} {j} {np} {P = P} {acc = acc} {b = b} {qs = qs} (a ∷ as) (bt-pi {q = q} c rok bt) Db (a-∷ c′ Da ar) cR
  with ≈-pi-inj (≈-trans (≈-sym c′) c)
... | refl , cA , cB =
  subst (λ xs → σ , Γ ⊨[ m ] appsFrom (app b a) as ∶ motApp P (drop np qs) (appsFrom (ctor i j) xs))
    (++-assoc acc (a ∷ []) as)
    (brApp as (BrTy-inst a bt) (app-q q Db rok (conv-≈ Da cA))
      (▹-≈ (≈-sub (instσ a) cB) ar) cR)

-- A clashing telescope has no constructor application at the
-- scrutinee's indices: along the arguments the telescope stays a
-- clash, and at the end its target indices would be convertible to
-- the clashing ones.
Clash-▹ : ∀ {σ n} {Γ : Ctx n} {m np is T as R i qs}
  → Clash σ np is T
  → σ , Γ ⊨[ m ] T ▹ as ⇝ R
  → σ ⊢[ spec ] R ≈ appsFrom (dty i) qs
  → σ ⊢[ spec ] drop np qs ≈L is → ⊥
Clash-▹ {np = np} {i = i} {qs = qs} (cl-end sp c cl) (a-[] c′) cR cis =
  ClashL-≈L cl
    (≈L-sym (≈L-trans
      (≈L-drop np (proj₂ (≈-dty-inj sp (Spine-appsFrom (dty i) qs) (≈-trans (≈-sym c) (≈-trans c′ cR)))))
      cis))
Clash-▹ {i = i} {qs = qs} (cl-pi c _) (a-[] c′) cR _ =
  ⊥-elim (≈-Spine-shape dh-dty (Spine-appsFrom (dty i) qs) h-pi (≈-trans (≈-sym cR) (≈-trans (≈-sym c′) c)))
Clash-▹ (cl-end sp c _) (a-∷ c′ _ _) _ _ =
  ⊥-elim (≈-Spine-shape dh-dty sp h-pi (≈-trans (≈-sym c) c′))
Clash-▹ (cl-pi c cl) (a-∷ {a = a} c′ _ ar) cR cis with ≈-pi-inj (≈-trans (≈-sym c) c′)
... | refl , _ , cB = Clash-▹ (Clash-≈ (≈-sub (instσ a) cB) (Clash-inst a cl)) ar cR cis

-- ι-data: the scrutinee is a constructor spine of the matched type, so
-- its parameters and indices are (convertible to) those of the match;
-- its branch is not a skipped one (Clash-▹), and applied to the
-- arguments it has the motive at the constructor's indices and at the
-- scrutinee (brApp), hence at the scrutinee's indices.
pres-ιdata : ∀ {σ n} {Γ : Ctx n} {m i j as e di ps₀ is₀ d P bs b}
  → Spine (ctor i j) as e → lookupList bs j ≡ ok b
  → σ , Γ ⊨[ m ] e ∶ appsFrom (dty di) (ps₀ ++ is₀)
  → lookupData σ di ≡ ok d → length ps₀ ≡ nparams d
  → σ , Γ ⊨[ m ] bs brs⟨ di , ps₀ , is₀ , P , 0 ⟩ DataDecl.ctors d
  → σ , Γ ⊨[ m ] appsFrom b as ∶ motApp P is₀ e
pres-ιdata {σ = σ} {Γ = Γ} {m} {as = as} {di = di} {ps₀} {is₀} {P = P} {b = b} sp lkb (conv D c) lk lps Bs
  with ctor-inv sp D
... | ca {ps = ps} {idxs} lk′ lkc lps′ lidx ip ar
  with ≈-dty-inj (Spine-appsFrom (dty _) (ps ++ idxs)) (Spine-appsFrom (dty di) (ps₀ ++ is₀)) c
... | refl , cps with ok-inj (trans (sym lk) lk′)
... | refl with ≈L-++-split (trans lps′ (sym lps)) cps
... | cps′ , cidx with brs-lookup Bs lkb lkc
... | br-typed {T = T′} {X} ip′ bt Db =
  conv-≈
    (subst (λ e → σ , Γ ⊨[ m ] appsFrom b as ∶ motApp P (drop (length ps₀) (ps ++ idxs)) e) (sym (Spine-≡ sp))
      (brApp as bt Db (▹-≈ (InstParams-≈ ≈-refl cps′ ip ip′) ar) ≈-refl))
    (≈-motApp P (subst (λ xs → σ ⊢[ spec ] xs ≈L is₀) (sym (drop-++ (length ps₀) ps idxs (trans lps′ (sym lps)))) cidx) ≈-refl)
... | br-clash ip′ cl =
  ⊥-elim (Clash-▹ (Clash-≈ (InstParams-≈ ≈-refl (≈L-sym cps′) ip′ ip) cl) ar ≈-refl
    (subst (λ xs → σ ⊢[ spec ] xs ≈L is₀) (sym (drop-++ (length ps₀) ps idxs (trans lps′ (sym lps)))) cidx))

-- The step may be taken in any mode m′: δ is justified by the typing's
-- allowedDef, not the step's.
pres : ∀ {σ n} {Γ : Ctx n} {m m′ e e′ A}
  → WfSig σ
  → σ , Γ ⊨[ m ] e ∶ A → σ ⊢[ m′ ] e ⟶ e′ → σ , Γ ⊨[ m ] e′ ∶ A
pres⁰ : ∀ {σ n} {Γ : Ctx n} {m m′ e e′ A}
  → WfSig σ
  → σ , Γ ⊨⁰[ m ] e ∶ A → σ ⊢[ m′ ] e ⟶ e′ → σ , Γ ⊨[ m ] e′ ∶ A

pres wf (conv D c) s = conv-≈ (pres⁰ wf D s) c

-- A step is a conversion (in spec mode, where every def unfolds).
step-≈ : ∀ {σ m n} {e e′ : Tm n} → σ ⊢[ m ] e ⟶ e′ → σ ⊢[ spec ] e′ ≈ e
step-≈ s = ≈-sym (≈-mode ≤ᵐ-spec-top (⟶→≈ s))

-- δ
pres⁰ wf (t-def {d = d} lk al) (δ lk′ _) with ok-inj (trans (sym lk) lk′)
... | refl = ⊨-mode (allowedDef→≤ᵐ (Def.dmode d) _ al) (closed-⊨ (wf _ _ lk))
-- β
pres⁰ wf (t-app-aff (conv (t-lam W c rok Dt) cpi) Da) β with ≈-pi-inj cpi
... | refl , cA , cB =
  conv-≈ (⊨-inst ≤ᵐ-refl Dt (conv-≈ Da (≈-sym cA))) (≈-sub _ cB)
pres⁰ wf (t-app-era (conv (t-lam W c rok Dt) cpi) Da) β with ≈-pi-inj cpi
... | refl , cA , cB =
  conv-≈ (⊨-inst ≤ᵐ-refl Dt (conv-≈ Da (≈-sym cA))) (≈-sub _ cB)
pres⁰ wf (t-app-reuse (conv (t-lam W c rok Dt) cpi) isd Da) β with ≈-pi-inj cpi
... | refl , cA , cB =
  conv-≈ (⊨-inst ≤ᵐ-refl Dt (conv-≈ Da (≈-sym cA))) (≈-sub _ cB)
-- congruence in the function
pres⁰ wf (t-app-aff Df Da) (app-f s) = conv (t-app-aff (pres wf Df s) Da) ≈-refl
pres⁰ wf (t-app-era Df Da) (app-f s) = conv (t-app-era (pres wf Df s) Da) ≈-refl
pres⁰ wf (t-app-reuse Df isd Da) (app-f s) =
  conv (t-app-reuse (pres wf Df s) isd Da) ≈-refl
-- ι
pres⁰ wf (t-mNat De W Dz Ds) ιz = Dz
pres⁰ wf (t-mNat {m = m} {q = q} {P = P} (conv (t-su Du) _) W Dz Ds) (ιs {u = u}) =
  conv-≈ (⊨-inst ≤ᵐ-refl Ds (⊨-mode (≤ᵐ-modeFor q m) Du)) (≈-≡ (inst-motSuc P u))
pres⁰ wf (t-mNat {P = P} De W Dz Ds) (mNat-e s) =
  conv (t-mNat (pres wf De s) W Dz Ds) (≈-inst P (step-≈ s))
pres⁰ wf (t-mUnit De W Du) ιtt = Du
pres⁰ wf (t-mUnit {P = P} De W Du) (mUnit-e s) =
  conv (t-mUnit (pres wf De s) W Du) (≈-inst P (step-≈ s))
pres⁰ wf (t-mEmp {P = P} De W) (mEmp-e s) =
  conv (t-mEmp (pres wf De s) W) (≈-inst P (step-≈ s))
pres⁰ wf (t-rwt {P = P} (conv (t-rfl cab) cid) W Dt) ιrfl with ≈-idt-inj cid
... | _ , cal , cbr =
  conv-≈ Dt (≈-inst P (≈-trans (≈-sym cbr) (≈-trans (≈-sym cab) cal)))
pres⁰ wf (t-rwt Deq W Dt) (rwt-e s) =
  conv (t-rwt (pres wf Deq s) W Dt) ≈-refl
-- data
pres⁰ wf (t-ctor sp _) s = ⊥-elim (Spine-no-step dh-ctor sp s)
pres⁰ wf (t-mData De lk lps lis M Bs) (ι-data sp lkb) = pres-ιdata sp lkb De lk lps Bs
pres⁰ wf (t-mData {is = is} {P = P} De lk lps lis M Bs) (mData-e s) =
  conv (t-mData (pres wf De s) lk lps lis M Bs) (≈-motApp P (≈L-refl is) (step-≈ s))
-- ann
pres⁰ wf (t-ann W D) ann-e = D
-- let (a, b) = (a₀, b₀) in t
pres⁰ {Γ = Γ} wf (t-letp {t = t} {A = A} {C = C} (conv (t-pair {a = a} {b} Da Db) cp) Dt) ι-letp
  with ≈-prod-inj cp
... | cA , cB =
  ⊨-≡ (inst-wk C a)
    (⊨-inst ≤ᵐ-refl
      (⊨-≡ (inst-wk (wk C) (wk b))
        (⊨-inst ≤ᵐ-refl Dt
          (⊨-ren (Ren-wk Γ affine A) (conv-≈ Db cB))))
      (conv-≈ Da cA))
pres⁰ wf (t-letp De Dt) (letp-e s) = conv (t-letp (pres wf De s) Dt) ≈-refl
-- rigid forms do not step
pres⁰ wf (t-var _) ()
pres⁰ wf t-ze ()
pres⁰ wf (t-su _) ()
pres⁰ wf t-one ()
pres⁰ wf t-nat ()
pres⁰ wf t-unit ()
pres⁰ wf t-empty ()
pres⁰ wf (t-pi _ _) ()
pres⁰ wf (t-lam _ _ _ _) ()
pres⁰ wf (t-idt _ _ _) ()
pres⁰ wf (t-rfl _) ()
pres⁰ wf (t-dty _) ()
pres⁰ wf (t-prod _ _) ()
pres⁰ wf (t-pair _ _) ()

pres* : ∀ {σ n} {Γ : Ctx n} {m m′ e e′ A}
  → WfSig σ
  → σ , Γ ⊨[ m ] e ∶ A → σ ⊢[ m′ ] e ⟶* e′ → σ , Γ ⊨[ m ] e′ ∶ A
pres* wf D ⟶*-refl = D
pres* wf D (⟶*-step s r) = pres* wf (pres wf D s) r

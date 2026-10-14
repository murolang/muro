------------------------------------------------------------------------
-- Declarative typing for the ⊢ fragment, without uses. This is the
-- judgment the metatheory is about.
{-# OPTIONS --safe #-}
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

module Muro.Typing where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_; length; drop)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product.Base using (_×_; _,_; ∃; proj₁; proj₂)
open import Data.Vec.Base as Vec using ([]; _∷_; lookup; map)
open import Data.Vec.Properties using (lookup-map)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

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
open import Muro.Frag using (UShape)
open import Muro.Check using (unfStepOf; unfSpine; unfFam; applyFam)

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
    → CopyOk σ q A′
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

  -- The argument is copyable; ⊨ forgets uses, so Data and closure
  -- arguments (⊢'s ⇒-app-reuse and ⇒-app-copy) share this rule.
  t-app-reuse : ∀ {m f a A B}
    → σ , Γ ⊨[ m ] f ∶ pi reuse A B
    → IsCopy σ A
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

  -- Positivity and the product-body test stay in ⊢. A ν that is typed
  -- has kind K and its body is a term of that kind.
  t-nu : ∀ {F K}
    → σ , ext Γ affine K ⊨[ spec ] F ∶ wk K
    → σ , Γ ⊨⁰[ spec ] nu F ∶ K

  -- Inferred unfold: Stream A, the codomain a product with the seed
  -- type in the tail. The pair shape is UShape, dropped here the way
  -- checkBound is.
  t-unf : ∀ {m q seed S f A}
    → σ , Γ ⊨[ m ] seed ∶ S
    → σ , Γ ⊨[ m ] f ∶ pi q S (prod (wk A) (wk S))
    → σ , Γ ⊨⁰[ m ] unf seed f ∶ nu (prod (wk A) (var zero))

  -- Checked unfold at a stream ν X. Eh × X. The tail is the next
  -- seed, so uncons wraps.
  t-unfG : ∀ {m q seed S A h t T Eh G fam}
    → σ , Γ ⊨[ m ] seed ∶ S
    → σ ⊢[ spec ] A ≈ S
    → unfStepOf S T ≡ ok (G , fam)
    → T ≡ nu (prod (wk Eh) (var zero))
    → σ , ext Γ q S ⊨[ m ] pair h t ∶ wk G
    → σ , Γ ⊨⁰[ m ] unf seed (lam q A (pair h t)) ∶ T

  -- Checked unfold at a declared family. The subject is the pair
  -- instantiated at the seed: the tail is already the proof at the
  -- next indices, and uncons reads it.
  t-unfR : ∀ {m q seed S A h t T G fam}
    → σ , Γ ⊨[ m ] seed ∶ S
    → σ ⊢[ spec ] A ≈ S
    → unfStepOf S T ≡ ok (G , fam)
    → fam ≡ true
    → σ , ext Γ q S ⊨[ m ] pair h t ∶ wk G
    → σ , Γ ⊨⁰[ m ] unf seed (pair (inst h seed) (inst t seed)) ∶ T

  t-ucons : ∀ {m s T T′ G fam}
    → σ , Γ ⊨[ m ] s ∶ T
    → σ ⊢[ spec ] T ≈ T′
    → unfStepOf T T′ ≡ ok (G , fam)
    → σ , Γ ⊨⁰[ m ] ucons s ∶ G

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
  → σ , Γ ⊨[ m ] f ∶ pi q A B → CopyOk σ q A
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
  conv (t-app-reuse (conv-≈ (forget-⇒ Df) c) (c-data isd) (forget-⇐ Da)) ≈-refl
forget-⇒ (⇒-app-copy Df c isc Da _) =
  conv (t-app-reuse (conv-≈ (forget-⇒ Df) c) isc (forget-⇐ Da)) ≈-refl
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
forget-⇒ (⇒-nu _ _ _ D) = conv (t-nu (forget-⇐ D)) ≈-refl
forget-⇒ (⇒-unf Ds Df c _ _) =
  conv (t-unf (forget-⇒ Ds) (conv-≈ (forget-⇒ Df) c)) ≈-refl
forget-⇒ (⇒-ucons Ds c st) = conv (t-ucons (forget-⇒ Ds) c st) ≈-refl

forget-⇐ (⇐-conv D c) = conv-≈ (forget-⇒ D) c
forget-⇐ (⇐-lam W cT c rok D _) =
  conv (t-lam (forget-wf W) c rok (forget-⇐ D)) (≈-sym cT)
forget-⇐ (⇐-refl cT c _) = conv (t-rfl c) (≈-sym cT)
forget-⇐ (⇐-ctor sp c lk lps lidx lkc ip Ar cR) =
  conv (t-ctor sp (ca lk lkc lps lidx ip (▹-R cR (forget-args Ar)))) (≈-sym c)
forget-⇐ (⇐-pair cT Da Db _) = conv (t-pair (forget-⇐ Da) (forget-⇐ Db)) (≈-sym cT)
forget-⇐ (⇐-letp De c Dt _ _ _) =
  conv (t-letp (conv-≈ (forget-⇒ De) c) (forget-⇐ Dt)) ≈-refl
forget-⇐ (⇐-unf Ds cA c st sh Dp _ _) =
  conv (t-unfG (forget-⇒ Ds) cA st sh (forget-⇐ Dp)) (≈-sym c)
forget-⇐ (⇐-unfR Ds cA c st nf Dp _ _) =
  conv (t-unfR (forget-⇒ Ds) cA st nf (forget-⇐ Dp)) (≈-sym c)

forget-args args-[] = a-[] ≈-refl
forget-args (args-snoc Ar c _ Da _) = ▹-snoc (forget-args Ar) c (forget-⇐ Da)
forget-args (args-snoc-copy Ar c _ Da _) = ▹-snoc (forget-args Ar) c (forget-⇐ Da)

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
⊨⁰-mode ≤ᵐ-spec (t-nu D) = t-nu D
⊨⁰-mode h (t-unf Ds Df) = t-unf (⊨-mode h Ds) (⊨-mode h Df)
⊨⁰-mode h (t-unfG Ds c st sh Dp) = t-unfG (⊨-mode h Ds) c st sh (⊨-mode h Dp)
⊨⁰-mode h (t-unfR Ds c st nf Dp) = t-unfR (⊨-mode h Ds) c st nf (⊨-mode h Dp)
⊨⁰-mode h (t-ucons Ds c st) = t-ucons (⊨-mode h Ds) c st

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


-- unfStepOf commutes with renaming. A bare ν instantiates the first
-- argument; an applied family ignores it and keeps the indices.
applyFam-ren : ∀ {n m} (ρ : Fin n → Fin m) (t : Tm n) (is : List (Tm n))
  → applyFam (ren ρ t) (renList ρ is) ≡ ren ρ (applyFam t is)
applyFam-ren ρ t [] = refl
applyFam-ren ρ (var x) (i ∷ is) = applyFam-ren ρ (app (var x) i) is
applyFam-ren ρ typ (i ∷ is) = applyFam-ren ρ (app typ i) is
applyFam-ren ρ (pi q A B) (i ∷ is) = applyFam-ren ρ (app (pi q A B) i) is
applyFam-ren ρ (lam q A b) (i ∷ is) rewrite sym (ren-inst ρ b i) =
  applyFam-ren ρ (inst b i) is
applyFam-ren ρ (app f a) (i ∷ is) = applyFam-ren ρ (app (app f a) i) is
applyFam-ren ρ nat (i ∷ is) = applyFam-ren ρ (app nat i) is
applyFam-ren ρ ze (i ∷ is) = applyFam-ren ρ (app ze i) is
applyFam-ren ρ (su u) (i ∷ is) = applyFam-ren ρ (app (su u) i) is
applyFam-ren ρ unit (i ∷ is) = applyFam-ren ρ (app unit i) is
applyFam-ren ρ one (i ∷ is) = applyFam-ren ρ (app one i) is
applyFam-ren ρ empty (i ∷ is) = applyFam-ren ρ (app empty i) is
applyFam-ren ρ (dty x) (i ∷ is) = applyFam-ren ρ (app (dty x) i) is
applyFam-ren ρ (ctor x y) (i ∷ is) = applyFam-ren ρ (app (ctor x y) i) is
applyFam-ren ρ (mData e P bs) (i ∷ is) = applyFam-ren ρ (app (mData e P bs) i) is
applyFam-ren ρ (mNat e P z s) (i ∷ is) = applyFam-ren ρ (app (mNat e P z s) i) is
applyFam-ren ρ (mEmp e P) (i ∷ is) = applyFam-ren ρ (app (mEmp e P) i) is
applyFam-ren ρ (mUnit e P u) (i ∷ is) = applyFam-ren ρ (app (mUnit e P u) i) is
applyFam-ren ρ (idt A a b) (i ∷ is) = applyFam-ren ρ (app (idt A a b) i) is
applyFam-ren ρ rfl (i ∷ is) = applyFam-ren ρ (app rfl i) is
applyFam-ren ρ (rwt e P t) (i ∷ is) = applyFam-ren ρ (app (rwt e P t) i) is
applyFam-ren ρ (def x) (i ∷ is) = applyFam-ren ρ (app (def x) i) is
applyFam-ren ρ (ann e A) (i ∷ is) = applyFam-ren ρ (app (ann e A) i) is
applyFam-ren ρ (prod A B) (i ∷ is) = applyFam-ren ρ (app (prod A B) i) is
applyFam-ren ρ (pair a b) (i ∷ is) = applyFam-ren ρ (app (pair a b) i) is
applyFam-ren ρ (letp e t) (i ∷ is) = applyFam-ren ρ (app (letp e t) i) is
applyFam-ren ρ (nu F) (i ∷ is) = applyFam-ren ρ (app (nu F) i) is
applyFam-ren ρ (unf s f) (i ∷ is) = applyFam-ren ρ (app (unf s f) i) is
applyFam-ren ρ (ucons s) (i ∷ is) = applyFam-ren ρ (app (ucons s) i) is
applyFam-ren ρ i64 (i ∷ is) = applyFam-ren ρ (app i64 i) is
applyFam-ren ρ f32ty (i ∷ is) = applyFam-ren ρ (app f32ty i) is
applyFam-ren ρ (tensor d s) (i ∷ is) = applyFam-ren ρ (app (tensor d s) i) is
applyFam-ren ρ (addi x y) (i ∷ is) = applyFam-ren ρ (app (addi x y) i) is
applyFam-ren ρ (muli x y) (i ∷ is) = applyFam-ren ρ (app (muli x y) i) is
applyFam-ren ρ (addt t u) (i ∷ is) = applyFam-ren ρ (app (addt t u) i) is
applyFam-ren ρ (toi64 t) (i ∷ is) = applyFam-ren ρ (app (toi64 t) i) is
applyFam-ren ρ (packi x y) (i ∷ is) = applyFam-ren ρ (app (packi x y) i) is

unfFam-ren : ∀ {n m} (ρ : Fin n → Fin m) S F is {G fam}
  → unfFam S F is ≡ ok (G , fam)
  → unfFam (ren ρ S) (ren (lift ρ) F) (renList ρ is) ≡ ok (ren ρ G , fam)
unfFam-ren ρ S F [] refl = cong (λ g → ok (g , false)) (sym (ren-inst ρ F S))
unfFam-ren ρ S (lam q A b) (i ∷ is) refl =
  cong (λ g → ok (g , true))
    (trans (cong (λ t → applyFam t (renList ρ (i ∷ is)))
             (sym (ren-inst ρ (lam q A b) (nu (lam q A b)))))
           (applyFam-ren ρ (inst (lam q A b) (nu (lam q A b))) (i ∷ is)))
unfFam-ren ρ S (var _) (_ ∷ _) ()
unfFam-ren ρ S typ (_ ∷ _) ()
unfFam-ren ρ S (pi _ _ _) (_ ∷ _) ()
unfFam-ren ρ S (app _ _) (_ ∷ _) ()
unfFam-ren ρ S nat (_ ∷ _) ()
unfFam-ren ρ S ze (_ ∷ _) ()
unfFam-ren ρ S (su _) (_ ∷ _) ()
unfFam-ren ρ S unit (_ ∷ _) ()
unfFam-ren ρ S one (_ ∷ _) ()
unfFam-ren ρ S empty (_ ∷ _) ()
unfFam-ren ρ S (dty _) (_ ∷ _) ()
unfFam-ren ρ S (ctor _ _) (_ ∷ _) ()
unfFam-ren ρ S (mData _ _ _) (_ ∷ _) ()
unfFam-ren ρ S (mNat _ _ _ _) (_ ∷ _) ()
unfFam-ren ρ S (mEmp _ _) (_ ∷ _) ()
unfFam-ren ρ S (mUnit _ _ _) (_ ∷ _) ()
unfFam-ren ρ S (idt _ _ _) (_ ∷ _) ()
unfFam-ren ρ S rfl (_ ∷ _) ()
unfFam-ren ρ S (rwt _ _ _) (_ ∷ _) ()
unfFam-ren ρ S (def _) (_ ∷ _) ()
unfFam-ren ρ S (ann _ _) (_ ∷ _) ()
unfFam-ren ρ S (prod _ _) (_ ∷ _) ()
unfFam-ren ρ S (pair _ _) (_ ∷ _) ()
unfFam-ren ρ S (letp _ _) (_ ∷ _) ()
unfFam-ren ρ S (nu _) (_ ∷ _) ()
unfFam-ren ρ S (unf _ _) (_ ∷ _) ()
unfFam-ren ρ S (ucons _) (_ ∷ _) ()
unfFam-ren ρ S i64 (_ ∷ _) ()
unfFam-ren ρ S f32ty (_ ∷ _) ()
unfFam-ren ρ S (tensor _ _) (_ ∷ _) ()
unfFam-ren ρ S (addi _ _) (_ ∷ _) ()
unfFam-ren ρ S (muli _ _) (_ ∷ _) ()
unfFam-ren ρ S (addt _ _) (_ ∷ _) ()
unfFam-ren ρ S (toi64 _) (_ ∷ _) ()
unfFam-ren ρ S (packi _ _) (_ ∷ _) ()

unfStepOf-ren : ∀ {n m} (ρ : Fin n → Fin m) (S T : Tm n) {G fam}
  → unfStepOf S T ≡ ok (G , fam)
  → unfStepOf (ren ρ S) (ren ρ T) ≡ ok (ren ρ G , fam)
unfStepOf-ren ρ S (nu F) refl = cong (λ g → ok (g , false)) (sym (ren-inst ρ F S))
unfStepOf-ren ρ S (app f a) eq = go f (a ∷ []) eq
  where
  go : ∀ (h : Tm _) is {G′ fam′}
    → unfSpine S (unspine-go h is) ≡ ok (G′ , fam′)
    → unfSpine (ren ρ S) (unspine-go (ren ρ h) (renList ρ is)) ≡ ok (ren ρ G′ , fam′)
  go (app f′ a′) is eq′ = go f′ (a′ ∷ is) eq′
  go (nu F) is eq′ = unfFam-ren ρ S F is eq′
  go (var _) _ ()
  go typ _ ()
  go (pi _ _ _) _ ()
  go (lam _ _ _) _ ()
  go nat _ ()
  go ze _ ()
  go (su _) _ ()
  go unit _ ()
  go one _ ()
  go empty _ ()
  go (dty _) _ ()
  go (ctor _ _) _ ()
  go (mData _ _ _) _ ()
  go (mNat _ _ _ _) _ ()
  go (mEmp _ _) _ ()
  go (mUnit _ _ _) _ ()
  go (idt _ _ _) _ ()
  go rfl _ ()
  go (rwt _ _ _) _ ()
  go (def _) _ ()
  go (ann _ _) _ ()
  go (prod _ _) _ ()
  go (pair _ _) _ ()
  go (letp _ _) _ ()
  go (unf _ _) _ ()
  go (ucons _) _ ()
  go i64 _ ()
  go f32ty _ ()
  go (tensor _ _) _ ()
  go (addi _ _) _ ()
  go (muli _ _) _ ()
  go (addt _ _) _ ()
  go (toi64 _) _ ()
  go (packi _ _) _ ()
unfStepOf-ren ρ S (var _) ()
unfStepOf-ren ρ S typ ()
unfStepOf-ren ρ S (pi _ _ _) ()
unfStepOf-ren ρ S (lam _ _ _) ()
unfStepOf-ren ρ S nat ()
unfStepOf-ren ρ S ze ()
unfStepOf-ren ρ S (su _) ()
unfStepOf-ren ρ S unit ()
unfStepOf-ren ρ S one ()
unfStepOf-ren ρ S empty ()
unfStepOf-ren ρ S (dty _) ()
unfStepOf-ren ρ S (ctor _ _) ()
unfStepOf-ren ρ S (mData _ _ _) ()
unfStepOf-ren ρ S (mNat _ _ _ _) ()
unfStepOf-ren ρ S (mEmp _ _) ()
unfStepOf-ren ρ S (mUnit _ _ _) ()
unfStepOf-ren ρ S (idt _ _ _) ()
unfStepOf-ren ρ S rfl ()
unfStepOf-ren ρ S (rwt _ _ _) ()
unfStepOf-ren ρ S (def _) ()
unfStepOf-ren ρ S (ann _ _) ()
unfStepOf-ren ρ S (prod _ _) ()
unfStepOf-ren ρ S (pair _ _) ()
unfStepOf-ren ρ S (letp _ _) ()
unfStepOf-ren ρ S (unf _ _) ()
unfStepOf-ren ρ S (ucons _) ()
unfStepOf-ren ρ S i64 ()
unfStepOf-ren ρ S f32ty ()
unfStepOf-ren ρ S (tensor _ _) ()
unfStepOf-ren ρ S (addi _ _) ()
unfStepOf-ren ρ S (muli _ _) ()
unfStepOf-ren ρ S (addt _ _) ()
unfStepOf-ren ρ S (toi64 _) ()
unfStepOf-ren ρ S (packi _ _) ()

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

-- The codomain of an inferred unfold sits under the Π, so wk commutes
-- with renaming there and the ν variable stays zero.
unf-ren⁰ : ∀ {σ n k m q} {ρ : Fin n → Fin k} {Δ : Ctx k} {seed′ f′}
  (S A : Tm n)
  → σ , Δ ⊨[ m ] seed′ ∶ ren ρ S
  → σ , Δ ⊨[ m ] f′ ∶ ren ρ (pi q S (prod (wk A) (wk S)))
  → σ , Δ ⊨⁰[ m ] unf seed′ f′ ∶ ren ρ (nu (prod (wk A) (var zero)))
unf-ren⁰ {ρ = ρ} S A Ds Df rewrite ren-wk ρ A | ren-wk ρ S = t-unf Ds Df

unf-sub⁰ : ∀ {σ n k m q} {τ : Fin n → Tm k} {Δ : Ctx k} {seed′ f′}
  (S A : Tm n)
  → σ , Δ ⊨[ m ] seed′ ∶ sub τ S
  → σ , Δ ⊨[ m ] f′ ∶ sub τ (pi q S (prod (wk A) (wk S)))
  → σ , Δ ⊨[ m ] unf seed′ f′ ∶ sub τ (nu (prod (wk A) (var zero)))
unf-sub⁰ {τ = τ} S A Ds Df rewrite sub-wk τ A | sub-wk τ S =
  conv (t-unf Ds Df) ≈-refl

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
  t-lam (wf-ren r W) (≈-ren ρ c) (CopyOk-ren ρ q rok) (⊨-ren (Ren-lift r _ _) D)
⊨⁰-ren {ρ = ρ} r (t-app-aff {a = a} {B = B} Df Da) rewrite ren-inst ρ B a =
  t-app-aff (⊨-ren r Df) (⊨-ren r Da)
⊨⁰-ren {ρ = ρ} r (t-app-era {a = a} {B = B} Df Da) rewrite ren-inst ρ B a =
  t-app-era (⊨-ren r Df) (⊨-ren r Da)
⊨⁰-ren {ρ = ρ} r (t-app-reuse {a = a} {B = B} Df isd Da) rewrite ren-inst ρ B a =
  t-app-reuse (⊨-ren r Df) (IsCopy-ren ρ isd) (⊨-ren r Da)
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
⊨⁰-ren {ρ = ρ} r (t-nu {K = K} D) =
  t-nu (⊨-≡ (ren-wk ρ K) (⊨-ren (Ren-lift r affine K) D))
⊨⁰-ren {ρ = ρ} r (t-unf {S = S} {A = A} Ds Df) =
  unf-ren⁰ S A (⊨-ren r Ds) (⊨-ren r Df)
⊨⁰-ren {ρ = ρ} {A = A} r (t-unfG {q = q} {S = S} {Eh = Eh} {G = G} Ds c st sh Dp) =
  t-unfG (⊨-ren r Ds) (≈-ren ρ c) (unfStepOf-ren ρ S A st)
    (trans (cong (ren ρ) sh) (cong (λ E → nu (prod E (var zero))) (ren-wk ρ Eh)))
    (⊨-≡ (ren-wk ρ G) (⊨-ren (Ren-lift r q S) Dp))
⊨⁰-ren {σ = σ} {ρ = ρ} {Δ = Δ} {m = m} r (t-unfR {q = q} {seed = seed} {S = S} {A = A} {h = h} {t = t} {T = T} {G = G} Ds c st nf Dp) =
  subst (λ e → σ , Δ ⊨⁰[ m ] e ∶ ren ρ T)
    (sym (cong₂ (λ x y → unf (ren ρ seed) (pair x y)) (ren-inst ρ h seed) (ren-inst ρ t seed)))
    (t-unfR (⊨-ren r Ds) (≈-ren ρ c) (unfStepOf-ren ρ S T st) nf
      (⊨-≡ (ren-wk ρ G) (⊨-ren (Ren-lift r q S) Dp)))
⊨⁰-ren {ρ = ρ} r (t-ucons {T = T} {T′ = T′} Ds c st) =
  t-ucons (⊨-ren r Ds) (≈-ren ρ c) (unfStepOf-ren ρ T T′ st)

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
-- applyFam instantiates a λ head. Substitution can turn a neutral index
-- into a λ, so the instantiated goal is the β-reduct of the substituted
-- spine, not the substituted goal. appsFrom never instantiates, and it
-- commutes with substitution on the nose; the two goals are convertible.
applyFam-apps : ∀ {σ n} (t : Tm n) (is : List (Tm n))
  → σ ⊢[ spec ] applyFam t is ≈ appsFrom t is
applyFam-apps t [] = ≈-refl
applyFam-apps (lam q A b) (i ∷ is) =
  ≈-trans (applyFam-apps (inst b i) is)
    (≈-appsFrom (≈-sym (⟶→≈ β)) (≈L-refl is))
applyFam-apps (var x) (i ∷ is) = applyFam-apps (app (var x) i) is
applyFam-apps typ (i ∷ is) = applyFam-apps (app typ i) is
applyFam-apps (pi q A B) (i ∷ is) = applyFam-apps (app (pi q A B) i) is
applyFam-apps (app f a) (i ∷ is) = applyFam-apps (app (app f a) i) is
applyFam-apps nat (i ∷ is) = applyFam-apps (app nat i) is
applyFam-apps ze (i ∷ is) = applyFam-apps (app ze i) is
applyFam-apps (su u) (i ∷ is) = applyFam-apps (app (su u) i) is
applyFam-apps unit (i ∷ is) = applyFam-apps (app unit i) is
applyFam-apps one (i ∷ is) = applyFam-apps (app one i) is
applyFam-apps empty (i ∷ is) = applyFam-apps (app empty i) is
applyFam-apps (dty x) (i ∷ is) = applyFam-apps (app (dty x) i) is
applyFam-apps (ctor x y) (i ∷ is) = applyFam-apps (app (ctor x y) i) is
applyFam-apps (mData e P bs) (i ∷ is) = applyFam-apps (app (mData e P bs) i) is
applyFam-apps (mNat e P z s) (i ∷ is) = applyFam-apps (app (mNat e P z s) i) is
applyFam-apps (mEmp e P) (i ∷ is) = applyFam-apps (app (mEmp e P) i) is
applyFam-apps (mUnit e P u) (i ∷ is) = applyFam-apps (app (mUnit e P u) i) is
applyFam-apps (idt A a b) (i ∷ is) = applyFam-apps (app (idt A a b) i) is
applyFam-apps rfl (i ∷ is) = applyFam-apps (app rfl i) is
applyFam-apps (rwt e P t) (i ∷ is) = applyFam-apps (app (rwt e P t) i) is
applyFam-apps (def x) (i ∷ is) = applyFam-apps (app (def x) i) is
applyFam-apps (ann e A) (i ∷ is) = applyFam-apps (app (ann e A) i) is
applyFam-apps (prod A B) (i ∷ is) = applyFam-apps (app (prod A B) i) is
applyFam-apps (pair a b) (i ∷ is) = applyFam-apps (app (pair a b) i) is
applyFam-apps (letp e t) (i ∷ is) = applyFam-apps (app (letp e t) i) is
applyFam-apps (nu F) (i ∷ is) = applyFam-apps (app (nu F) i) is
applyFam-apps (unf s f) (i ∷ is) = applyFam-apps (app (unf s f) i) is
applyFam-apps (ucons s) (i ∷ is) = applyFam-apps (app (ucons s) i) is
applyFam-apps i64 (i ∷ is) = applyFam-apps (app i64 i) is
applyFam-apps f32ty (i ∷ is) = applyFam-apps (app f32ty i) is
applyFam-apps (tensor d s) (i ∷ is) = applyFam-apps (app (tensor d s) i) is
applyFam-apps (addi x y) (i ∷ is) = applyFam-apps (app (addi x y) i) is
applyFam-apps (muli x y) (i ∷ is) = applyFam-apps (app (muli x y) i) is
applyFam-apps (addt t u) (i ∷ is) = applyFam-apps (app (addt t u) i) is
applyFam-apps (toi64 t) (i ∷ is) = applyFam-apps (app (toi64 t) i) is
applyFam-apps (packi x y) (i ∷ is) = applyFam-apps (app (packi x y) i) is

applyFam-sub≈ : ∀ {σ n k} (τ : Fin n → Tm k) (t : Tm n) (is : List (Tm n))
  → σ ⊢[ spec ] sub τ (applyFam t is) ≈ applyFam (sub τ t) (subList τ is)
applyFam-sub≈ τ t is =
  ≈-trans (≈-sub τ (applyFam-apps t is))
    (≈-trans (≈-≡ (sub-appsFrom τ t is))
      (≈-sym (applyFam-apps (sub τ t) (subList τ is))))

unfFam-sub : ∀ {σ n k} (τ : Fin n → Tm k) S F is {G fam}
  → unfFam S F is ≡ ok (G , fam)
  → ∃ λ G′ → unfFam (sub τ S) (sub (lifts τ) F) (subList τ is) ≡ ok (G′ , fam)
           × (σ ⊢[ spec ] sub τ G ≈ G′)
unfFam-sub τ S F [] refl =
  inst (sub (lifts τ) F) (sub τ S) , refl , ≈-≡ (sub-inst τ F S)
unfFam-sub {σ = σ} τ S (lam q A b) idxs@(i ∷ _) refl =
  G′ , refl , ≈-trans (applyFam-sub≈ {σ = σ} τ head idxs) (≈-≡ (cong (λ h → applyFam h (subList τ idxs)) head≡))
  where
  F = lam q A b
  head = inst F (nu F)
  head≡ : sub τ head ≡ inst (sub (lifts τ) F) (nu (sub (lifts τ) F))
  head≡ = sub-inst τ F (nu F)
  G′ = applyFam (inst (sub (lifts τ) F) (nu (sub (lifts τ) F))) (subList τ idxs)
unfFam-sub τ S (var _) (_ ∷ _) ()
unfFam-sub τ S typ (_ ∷ _) ()
unfFam-sub τ S (pi _ _ _) (_ ∷ _) ()
unfFam-sub τ S (app _ _) (_ ∷ _) ()
unfFam-sub τ S nat (_ ∷ _) ()
unfFam-sub τ S ze (_ ∷ _) ()
unfFam-sub τ S (su _) (_ ∷ _) ()
unfFam-sub τ S unit (_ ∷ _) ()
unfFam-sub τ S one (_ ∷ _) ()
unfFam-sub τ S empty (_ ∷ _) ()
unfFam-sub τ S (dty _) (_ ∷ _) ()
unfFam-sub τ S (ctor _ _) (_ ∷ _) ()
unfFam-sub τ S (mData _ _ _) (_ ∷ _) ()
unfFam-sub τ S (mNat _ _ _ _) (_ ∷ _) ()
unfFam-sub τ S (mEmp _ _) (_ ∷ _) ()
unfFam-sub τ S (mUnit _ _ _) (_ ∷ _) ()
unfFam-sub τ S (idt _ _ _) (_ ∷ _) ()
unfFam-sub τ S rfl (_ ∷ _) ()
unfFam-sub τ S (rwt _ _ _) (_ ∷ _) ()
unfFam-sub τ S (def _) (_ ∷ _) ()
unfFam-sub τ S (ann _ _) (_ ∷ _) ()
unfFam-sub τ S (prod _ _) (_ ∷ _) ()
unfFam-sub τ S (pair _ _) (_ ∷ _) ()
unfFam-sub τ S (letp _ _) (_ ∷ _) ()
unfFam-sub τ S (nu _) (_ ∷ _) ()
unfFam-sub τ S (unf _ _) (_ ∷ _) ()
unfFam-sub τ S (ucons _) (_ ∷ _) ()
unfFam-sub τ S i64 (_ ∷ _) ()
unfFam-sub τ S f32ty (_ ∷ _) ()
unfFam-sub τ S (tensor _ _) (_ ∷ _) ()
unfFam-sub τ S (addi _ _) (_ ∷ _) ()
unfFam-sub τ S (muli _ _) (_ ∷ _) ()
unfFam-sub τ S (addt _ _) (_ ∷ _) ()
unfFam-sub τ S (toi64 _) (_ ∷ _) ()
unfFam-sub τ S (packi _ _) (_ ∷ _) ()

unfStepOf-sub : ∀ {σ n k} (τ : Fin n → Tm k) (S T : Tm n) {G fam}
  → unfStepOf S T ≡ ok (G , fam)
  → ∃ λ G′ → unfStepOf (sub τ S) (sub τ T) ≡ ok (G′ , fam)
           × (σ ⊢[ spec ] sub τ G ≈ G′)
unfStepOf-sub τ S (nu F) refl =
  inst (sub (lifts τ) F) (sub τ S) , refl , ≈-≡ (sub-inst τ F S)
unfStepOf-sub {σ = σ} τ S (app f a) eq = go f (a ∷ []) eq
  where
  go : ∀ (h : Tm _) is {G′ fam′}
    → unfSpine S (unspine-go h is) ≡ ok (G′ , fam′)
    → ∃ λ G″ → unfSpine (sub τ S) (unspine-go (sub τ h) (subList τ is)) ≡ ok (G″ , fam′)
             × (σ ⊢[ spec ] sub τ G′ ≈ G″)
  go (app f′ a′) is eq′ = go f′ (a′ ∷ is) eq′
  go (nu F) is eq′ = unfFam-sub τ S F is eq′
  go (var _) _ ()
  go typ _ ()
  go (pi _ _ _) _ ()
  go (lam _ _ _) _ ()
  go nat _ ()
  go ze _ ()
  go (su _) _ ()
  go unit _ ()
  go one _ ()
  go empty _ ()
  go (dty _) _ ()
  go (ctor _ _) _ ()
  go (mData _ _ _) _ ()
  go (mNat _ _ _ _) _ ()
  go (mEmp _ _) _ ()
  go (mUnit _ _ _) _ ()
  go (idt _ _ _) _ ()
  go rfl _ ()
  go (rwt _ _ _) _ ()
  go (def _) _ ()
  go (ann _ _) _ ()
  go (prod _ _) _ ()
  go (pair _ _) _ ()
  go (letp _ _) _ ()
  go (unf _ _) _ ()
  go (ucons _) _ ()
  go i64 _ ()
  go f32ty _ ()
  go (tensor _ _) _ ()
  go (addi _ _) _ ()
  go (muli _ _) _ ()
  go (addt _ _) _ ()
  go (toi64 _) _ ()
  go (packi _ _) _ ()
unfStepOf-sub τ S (var _) ()
unfStepOf-sub τ S typ ()
unfStepOf-sub τ S (pi _ _ _) ()
unfStepOf-sub τ S (lam _ _ _) ()
unfStepOf-sub τ S nat ()
unfStepOf-sub τ S ze ()
unfStepOf-sub τ S (su _) ()
unfStepOf-sub τ S unit ()
unfStepOf-sub τ S one ()
unfStepOf-sub τ S empty ()
unfStepOf-sub τ S (dty _) ()
unfStepOf-sub τ S (ctor _ _) ()
unfStepOf-sub τ S (mData _ _ _) ()
unfStepOf-sub τ S (mNat _ _ _ _) ()
unfStepOf-sub τ S (mEmp _ _) ()
unfStepOf-sub τ S (mUnit _ _ _) ()
unfStepOf-sub τ S (idt _ _ _) ()
unfStepOf-sub τ S rfl ()
unfStepOf-sub τ S (rwt _ _ _) ()
unfStepOf-sub τ S (def _) ()
unfStepOf-sub τ S (ann _ _) ()
unfStepOf-sub τ S (prod _ _) ()
unfStepOf-sub τ S (pair _ _) ()
unfStepOf-sub τ S (letp _ _) ()
unfStepOf-sub τ S (unf _ _) ()
unfStepOf-sub τ S (ucons _) ()
unfStepOf-sub τ S i64 ()
unfStepOf-sub τ S f32ty ()
unfStepOf-sub τ S (tensor _ _) ()
unfStepOf-sub τ S (addi _ _) ()
unfStepOf-sub τ S (muli _ _) ()
unfStepOf-sub τ S (addt _ _) ()
unfStepOf-sub τ S (toi64 _) ()
unfStepOf-sub τ S (packi _ _) ()

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
  conv (t-lam (wf-sub s W) (≈-sub τ c) (CopyOk-sub τ q rok)
          (⊨-sub lm (Subst-lifts s _ _) D)) ≈-refl
⊨⁰-sub {τ = τ} lm s (t-app-aff {a = a} {B = B} Df Da) =
  conv (t-app-aff (⊨-sub lm s Df) (⊨-sub lm s Da)) (≈-≡ (sym (sub-inst τ B a)))
⊨⁰-sub {τ = τ} lm s (t-app-era {a = a} {B = B} Df Da) =
  conv (t-app-era (⊨-sub lm s Df) (⊨-sub ≤ᵐ-spec-top s Da))
    (≈-≡ (sym (sub-inst τ B a)))
⊨⁰-sub {τ = τ} lm s (t-app-reuse {a = a} {B = B} Df isd Da) =
  conv (t-app-reuse (⊨-sub lm s Df) (IsCopy-sub τ isd) (⊨-sub lm s Da))
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
⊨⁰-sub {τ = τ} lm s (t-nu {K = K} D) =
  conv (t-nu (⊨-≡ (sub-wk τ K) (⊨-sub ≤ᵐ-spec-top (Subst-lifts s affine K) D))) ≈-refl
⊨⁰-sub {τ = τ} lm s (t-unf {S = S} {A = A} Ds Df) =
  unf-sub⁰ S A (⊨-sub lm s Ds) (⊨-sub lm s Df)
⊨⁰-sub {σ = σ} {τ = τ} lm s (t-unfG {q = q} {S = S} {T = T} {Eh = Eh} {G = G} Ds c st sh Dp)
  with unfStepOf-sub {σ = σ} τ S T st
... | G′ , st′ , cG =
  conv (t-unfG (⊨-sub lm s Ds) (≈-sub τ c) st′
          (trans (cong (sub τ) sh) (cong (λ E → nu (prod E (var zero))) (sub-wk τ Eh)))
          (conv-≈ (⊨-≡ (sub-wk τ G) (⊨-sub lm (Subst-lifts s q S) Dp))
                  (≈-ren suc cG)))
    ≈-refl
⊨⁰-sub {σ = σ} {m = m} {τ = τ} {Δ = Δ} lm s (t-unfR {q = q} {seed = seed} {S = S} {h = h} {t = t} {T = T} {G = G} Ds c st nf Dp)
  with unfStepOf-sub {σ = σ} τ S T st
... | G′ , st′ , cG =
  conv (subst (λ e → σ , Δ ⊨⁰[ m ] e ∶ sub τ T)
          (sym (cong₂ (λ x y → unf (sub τ seed) (pair x y)) (sub-inst τ h seed) (sub-inst τ t seed)))
          (t-unfR (⊨-sub lm s Ds) (≈-sub τ c) st′ nf
            (conv-≈ (⊨-≡ (sub-wk τ G) (⊨-sub lm (Subst-lifts s q S) Dp))
                    (≈-ren suc cG))))
    ≈-refl
⊨⁰-sub {σ = σ} {τ = τ} lm s (t-ucons {T = T} {T′ = T′} Ds c st)
  with unfStepOf-sub {σ = σ} τ T T′ st
... | G′ , st′ , cG =
  conv (t-ucons (⊨-sub lm s Ds) (≈-sub τ c) st′) (≈-sym cG)

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
ctor-inv () (t-nu _)
ctor-inv () (t-unf _ _)
ctor-inv () (t-unfG _ _ _ _ _)
ctor-inv () (t-unfR _ _ _ _ _)
ctor-inv () (t-ucons _ _ _)

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

≈-prod : ∀ {σ n} {A A′ B B′ : Tm n}
  → σ ⊢[ spec ] A ≈ A′ → σ ⊢[ spec ] B ≈ B′
  → σ ⊢[ spec ] prod A B ≈ prod A′ B′
≈-prod {A′ = A′} {B = B} cA cB =
  ≈-trans (≈-map (λ x → prod x B) (λ d → ⇛-prod d (⇛-refl _)) cA)
          (≈-map (λ x → prod A′ x) (λ d → ⇛-prod (⇛-refl _) d) cB)

≈-nu-inj : ∀ {σ n} {F F′ : Tm (suc n)}
  → σ ⊢[ spec ] nu F ≈ nu F′ → σ ⊢[ spec ] F ≈ F′
≈-nu-inj c with ≈→join c
... | v , tv , uv with nu-⇛* tv
... | F₁ , refl , r1 with nu-⇛* uv
... | _ , refl , r2 = join→≈ r1 r2

nu-⇛-inv : ∀ {σ m n} {F : Tm (suc n)} {u}
  → σ ⊢[ m ] nu F ⇛ u → ∃ λ F′ → u ≡ nu F′
nu-⇛-inv (⇛-nu _) = _ , refl

app-nu-⇛* : ∀ {σ m n} {F : Tm (suc n)} {a u}
  → σ ⊢[ m ] app (nu F) a ⇛* u
  → ∃ λ F′ → ∃ λ a′ → u ≡ app (nu F′) a′
app-nu-⇛* ⇛*-refl = _ , _ , refl
app-nu-⇛* (⇛*-step (⇛-app d da) r) with nu-⇛-inv d
... | _ , refl = app-nu-⇛* r

data NuSpine {n} : Tm n → Set where
  ns-nu  : ∀ {F} → NuSpine (nu F)
  ns-app : ∀ {f a} → NuSpine f → NuSpine (app f a)

ns-step : ∀ {σ m n} {t u : Tm n} → NuSpine t → σ ⊢[ m ] t ⇛ u → NuSpine u
ns-step ns-nu (⇛-nu _) = ns-nu
ns-step (ns-app h) (⇛-app d _) = ns-app (ns-step h d)

ns-star : ∀ {σ m n} {t u : Tm n} → NuSpine t → σ ⊢[ m ] t ⇛* u → NuSpine u
ns-star h ⇛*-refl = h
ns-star h (⇛*-step s r) = ns-star (ns-step h s) r

ns-apps-go : ∀ {n} (f : Tm n) → NuSpine f → ∀ j js → NuSpine (appsFrom f (j ∷ js))
ns-apps-go f hf j [] = ns-app hf
ns-apps-go f hf j (k ∷ ks) = ns-apps-go (app f j) (ns-app hf) k ks

ns-apps : ∀ {n} (F : Tm (suc n)) i is → NuSpine (appsFrom (nu F) (i ∷ is))
ns-apps F i [] = ns-app ns-nu
ns-apps F i (j ∷ js) = ns-apps-go (app (nu F) i) (ns-app ns-nu) j js

appish : ∀ {n} {t : Tm n} → NuSpine t → Bool
appish ns-nu = false
appish (ns-app _) = true

ns-keep : ∀ {σ m n} {t u : Tm n} (h : NuSpine t)
  → appish h ≡ true → (s : σ ⊢[ m ] t ⇛ u) → appish (ns-step h s) ≡ true
ns-keep (ns-app _) refl (⇛-app _ _) = refl

ns-keep* : ∀ {σ m n} {t u : Tm n} (h : NuSpine t)
  → appish h ≡ true → (r : σ ⊢[ m ] t ⇛* u) → appish (ns-star h r) ≡ true
ns-keep* h a ⇛*-refl = a
ns-keep* h a (⇛*-step s r) = ns-keep* (ns-step h s) (ns-keep h a s) r

kill-nu : ∀ {n} {F : Tm (suc n)} (h : NuSpine (nu F)) → appish h ≡ true → ⊥
kill-nu ns-nu ()

appish-go : ∀ {n} {f : Tm n} (hf : NuSpine f) j js → appish (ns-apps-go f hf j js) ≡ true
appish-go hf j [] = refl
appish-go hf j (k ∷ ks) = appish-go (ns-app hf) k ks

appish-apps : ∀ {n} (F : Tm (suc n)) i is → appish (ns-apps F i is) ≡ true
appish-apps F i [] = refl
appish-apps F i (j ∷ js) = appish-go (ns-app ns-nu) j js

nu-app-body : ∀ {σ n} {T : Tm n} {G fam} {P : Tm (suc n)} {f a}
  → unfStepOf T (app f a) ≡ ok (G , fam)
  → σ ⊢[ spec ] nu P ≈ app f a → ⊥
nu-app-body {σ = σ} {T = T} {G = G} {fam = fam} eq c with ≈→join c
... | v , tv , uv with nu-⇛* tv
... | _ , refl , _ = spine eq uv
  where
  spine : ∀ {f a} → unfStepOf T (app f a) ≡ ok (G , fam)
    → σ ⊢[ spec ] app f a ⇛* v → ⊥
  spine {f} {a} eq r = go f a [] eq r
    where
    go : ∀ h i is → unfSpine T (unspine-go h (i ∷ is)) ≡ ok (G , fam)
      → σ ⊢[ spec ] appsFrom h (i ∷ is) ⇛* v → ⊥
    go (app h′ b) i is eq r = go h′ b (i ∷ is) eq r
    go (nu F) i is _ r =
      kill-nu (ns-star (ns-apps F i is) r) (ns-keep* (ns-apps F i is) (appish-apps F i is) r)
    go (var _) _ _ () _
    go typ _ _ () _
    go (pi _ _ _) _ _ () _
    go (lam _ _ _) _ _ () _
    go nat _ _ () _
    go ze _ _ () _
    go (su _) _ _ () _
    go unit _ _ () _
    go one _ _ () _
    go empty _ _ () _
    go (dty _) _ _ () _
    go (ctor _ _) _ _ () _
    go (mData _ _ _) _ _ () _
    go (mNat _ _ _ _) _ _ () _
    go (mEmp _ _) _ _ () _
    go (mUnit _ _ _) _ _ () _
    go (idt _ _ _) _ _ () _
    go rfl _ _ () _
    go (rwt _ _ _) _ _ () _
    go (def _) _ _ () _
    go (ann _ _) _ _ () _
    go (prod _ _) _ _ () _
    go (pair _ _) _ _ () _
    go (letp _ _) _ _ () _
    go (unf _ _) _ _ () _
    go (ucons _) _ _ () _
    go i64 _ _ () _
    go f32ty _ _ () _
    go (tensor _ _) _ _ () _
    go (addi _ _) _ _ () _
    go (muli _ _) _ _ () _
    go (addt _ _) _ _ () _
    go (toi64 _) _ _ () _
    go (packi _ _) _ _ () _

-- An inferred unfold's uncons goal is the element paired with the
-- stream. The λ's tail is the next seed; wrapping it in the same λ
-- rebuilds the stream.
stream-goal : ∀ {σ n} {Eh : Tm n} {T T′ G fam}
  → σ ⊢[ spec ] nu (prod (wk Eh) (var zero)) ≈ T
  → σ ⊢[ spec ] T ≈ T′
  → unfStepOf T T′ ≡ ok (G , fam)
  → σ ⊢[ spec ] prod Eh (nu (prod (wk Eh) (var zero))) ≈ G
stream-goal {σ = σ} {Eh = Eh} {T = T} {G = G} {fam = fam} cU cT st = go _ st (≈-trans cU cT)
  where
  P = prod (wk Eh) (var zero)
  go : ∀ T′ → unfStepOf T T′ ≡ ok (G , fam) → σ ⊢[ spec ] nu P ≈ T′
    → σ ⊢[ spec ] prod Eh (nu P) ≈ G
  go (nu F) refl cN =
    ≈-trans (≈-prod ≈-refl cU)
      (≈-trans (≈-≡ (sym (cong (λ B → prod B T) (inst-wk Eh T))))
        (≈-sub (instσ T) (≈-nu-inj cN)))
  go (app f a) eq cN = ⊥-elim (nu-app-body eq cN)
  go (var _) () _
  go typ () _
  go (pi _ _ _) () _
  go (lam _ _ _) () _
  go nat () _
  go ze () _
  go (su _) () _
  go unit () _
  go one () _
  go empty () _
  go (dty _) () _
  go (ctor _ _) () _
  go (mData _ _ _) () _
  go (mNat _ _ _ _) () _
  go (mEmp _ _) () _
  go (mUnit _ _ _) () _
  go (idt _ _ _) () _
  go rfl () _
  go (rwt _ _ _) () _
  go (def _) () _
  go (ann _ _) () _
  go (prod _ _) () _
  go (pair _ _) () _
  go (letp _ _) () _
  go (unf _ _) () _
  go (ucons _) () _
  go i64 () _
  go f32ty () _
  go (tensor _ _) () _
  go (addi _ _) () _
  go (muli _ _) () _
  go (addt _ _) () _
  go (toi64 _) () _
  go (packi _ _) () _

pres-ι-unf : ∀ {σ n} {Γ : Ctx n} {m q q′ A S Eh s h t T T′ G fam}
  → σ , Γ ⊨[ m ] s ∶ S
  → σ , Γ ⊨[ m ] lam q′ A (pair h t) ∶ pi q S (prod (wk Eh) (wk S))
  → σ ⊢[ spec ] nu (prod (wk Eh) (var zero)) ≈ T
  → σ ⊢[ spec ] T ≈ T′
  → unfStepOf T T′ ≡ ok (G , fam)
  → σ , Γ ⊨[ m ] pair (inst h s) (unf (inst t s) (lam q′ A (pair h t))) ∶ G
pres-ι-unf {m = m} {q′ = q′} Ds (conv (t-lam {q = q′} {A′ = A′} W cAnn rok Dbody) cpi) cU cT st
  with ≈-pi-inj cpi
... | refl , cA′ , cB with Dbody
... | conv (t-pair Dh Dt) cp with ≈-prod-inj (≈-trans cp cB)
... | cH , cTail =
  let Darg = ⊨-mode (≤ᵐ-modeFor q′ m) (conv-≈ Ds (≈-sym cA′))
      Dhead = conv-≈ (⊨-inst ≤ᵐ-refl Dh Darg)
                (≈-trans (≈-sub (instσ _) cH) (≈-≡ (inst-wk _ _)))
      Dnext = conv-≈ (⊨-inst ≤ᵐ-refl Dt Darg)
                (≈-trans (≈-sub (instσ _) cTail) (≈-≡ (inst-wk _ _)))
      Dtail = conv (t-unf Dnext (conv (t-lam W cAnn rok Dbody) cpi)) ≈-refl
  in conv-≈ (conv (t-pair Dhead Dtail) ≈-refl) (stream-goal cU cT st)

pres-ι-unfG : ∀ {σ n} {Γ : Ctx n} {m q s S A h t T0 Eh G0 fam0 T T′ G fam}
  → σ , Γ ⊨[ m ] s ∶ S
  → σ ⊢[ spec ] A ≈ S
  → unfStepOf S T0 ≡ ok (G0 , fam0)
  → T0 ≡ nu (prod (wk Eh) (var zero))
  → σ , ext Γ q S ⊨[ m ] pair h t ∶ wk G0
  → σ ⊢[ spec ] T0 ≈ T
  → σ ⊢[ spec ] T ≈ T′
  → unfStepOf T T′ ≡ ok (G , fam)
  → σ , Γ ⊨[ m ] pair (inst h s) (unf (inst t s) (lam q A (pair h t))) ∶ G
pres-ι-unfG {m = m} {q = q} {S = S} {A = A} {Eh = Eh} Ds cA stG sh Dp cU cT st
  rewrite sh with stG | Dp
... | refl | conv (t-pair Dh Dt) cp =
  let Darg = ⊨-mode (≤ᵐ-modeFor q m) Ds
      Dhead = conv-≈ (⊨-inst ≤ᵐ-refl Dh Darg)
                (≈-trans (≈-sub (instσ _) (proj₁ (≈-prod-inj cp)))
                  (≈-trans (≈-≡ (inst-wk (inst (wk Eh) S) _)) (≈-≡ (inst-wk Eh _))))
      Dnext = conv-≈ (⊨-inst ≤ᵐ-refl Dt Darg)
                (≈-trans (≈-sub (instσ _) (proj₂ (≈-prod-inj cp))) (≈-≡ (inst-wk S _)))
      Dtail = conv (t-unfG Dnext cA refl refl Dp) ≈-refl
  in conv-≈ (conv (t-pair Dhead Dtail) ≈-refl) (stream-goal cU cT st)

pres-ιp : ∀ {σ n} {Γ : Ctx n} {m s q A h t T T′ G fam}
  → WfSig σ
  → σ , Γ ⊨[ m ] unf s (lam q A (pair h t)) ∶ T
  → σ ⊢[ spec ] T ≈ T′
  → unfStepOf T T′ ≡ ok (G , fam)
  → σ , Γ ⊨[ m ] pair (inst h s) (unf (inst t s) (lam q A (pair h t))) ∶ G
pres-ιp wf (conv (t-unf Ds Df) cU) cT st = pres-ι-unf Ds Df cU cT st
pres-ιp wf (conv (t-unfG Ds cA stG sh Dp) cU) cT st = pres-ι-unfG Ds cA stG sh Dp cU cT st

-- Weakening is injective on conversion: instantiate the extra variable away.
≈-wk-inj : ∀ {σ m n} {A B : Tm n}
  → σ ⊢[ m ] wk A ≈ wk B → σ ⊢[ m ] A ≈ B
≈-wk-inj {A = A} {B = B} c =
  ≈-trans (≈-≡ (sym (inst-wk A ze)))
    (≈-trans (≈-sub (instσ ze) c) (≈-≡ (inst-wk B ze)))

≈-nu : ∀ {σ m n} {F F′ : Tm (suc n)}
  → σ ⊢[ m ] F ≈ F′ → σ ⊢[ m ] nu F ≈ nu F′
≈-nu (≈-step s) = ≈-step (⇛-nu s)
≈-nu ≈-refl = ≈-refl
≈-nu (≈-sym c) = ≈-sym (≈-nu c)
≈-nu (≈-trans c d) = ≈-trans (≈-nu c) (≈-nu d)

×2 : ∀ {A B : Set} {a c : A} {b d : B} → (a , b) ≡ (c , d) → (a ≡ c) × (b ≡ d)
×2 refl = refl , refl

false≢true : false ≡ true → ⊥
false≢true ()

-- applyFam instantiates a λ; appsFrom applies it. β makes them agree,
-- and on any other head they are the same recursion.
apps-apply : ∀ {σ m n} (t : Tm n) (is : List (Tm n))
  → σ ⊢[ m ] appsFrom t is ≈ applyFam t is
apps-apply t [] = ≈-refl
apps-apply (lam q A b) (i ∷ is) =
  ≈-trans (≈-appsFrom (≈-step (⇛-β (⇛-refl b) (⇛-refl i))) (≈L-refl is))
          (apps-apply (inst b i) is)
apps-apply (var x) (i ∷ is) = apps-apply (app (var x) i) is
apps-apply typ (i ∷ is) = apps-apply (app typ i) is
apps-apply (pi q A B) (i ∷ is) = apps-apply (app (pi q A B) i) is
apps-apply (app f a) (i ∷ is) = apps-apply (app (app f a) i) is
apps-apply nat (i ∷ is) = apps-apply (app nat i) is
apps-apply ze (i ∷ is) = apps-apply (app ze i) is
apps-apply (su t) (i ∷ is) = apps-apply (app (su t) i) is
apps-apply unit (i ∷ is) = apps-apply (app unit i) is
apps-apply one (i ∷ is) = apps-apply (app one i) is
apps-apply empty (i ∷ is) = apps-apply (app empty i) is
apps-apply (dty k) (i ∷ is) = apps-apply (app (dty k) i) is
apps-apply (ctor di ci) (i ∷ is) = apps-apply (app (ctor di ci) i) is
apps-apply (mData e P bs) (i ∷ is) = apps-apply (app (mData e P bs) i) is
apps-apply (mNat e P z s) (i ∷ is) = apps-apply (app (mNat e P z s) i) is
apps-apply (mEmp e P) (i ∷ is) = apps-apply (app (mEmp e P) i) is
apps-apply (mUnit e P u) (i ∷ is) = apps-apply (app (mUnit e P u) i) is
apps-apply (idt A a b) (i ∷ is) = apps-apply (app (idt A a b) i) is
apps-apply rfl (i ∷ is) = apps-apply (app rfl i) is
apps-apply (rwt e P t) (i ∷ is) = apps-apply (app (rwt e P t) i) is
apps-apply (def k) (i ∷ is) = apps-apply (app (def k) i) is
apps-apply (ann e A) (i ∷ is) = apps-apply (app (ann e A) i) is
apps-apply (prod A B) (i ∷ is) = apps-apply (app (prod A B) i) is
apps-apply (pair a b) (i ∷ is) = apps-apply (app (pair a b) i) is
apps-apply (letp e t) (i ∷ is) = apps-apply (app (letp e t) i) is
apps-apply (nu F) (i ∷ is) = apps-apply (app (nu F) i) is
apps-apply (unf s f) (i ∷ is) = apps-apply (app (unf s f) i) is
apps-apply (ucons s) (i ∷ is) = apps-apply (app (ucons s) i) is
apps-apply i64 (i ∷ is) = apps-apply (app i64 i) is
apps-apply f32ty (i ∷ is) = apps-apply (app f32ty i) is
apps-apply (tensor d s) (i ∷ is) = apps-apply (app (tensor d s) i) is
apps-apply (addi x y) (i ∷ is) = apps-apply (app (addi x y) i) is
apps-apply (muli x y) (i ∷ is) = apps-apply (app (muli x y) i) is
apps-apply (addt t u) (i ∷ is) = apps-apply (app (addt t u) i) is
apps-apply (toi64 t) (i ∷ is) = apps-apply (app (toi64 t) i) is
apps-apply (packi x y) (i ∷ is) = apps-apply (app (packi x y) i) is

head-nu : ∀ {n} {F : Tm (suc n)} → Head (nu F)
head-nu _ = refl

-- A ν-headed spine is not a λ, so β never fires on it.
spine-nu-one : ∀ {σ m n} {F : Tm (suc n)} {as e e′}
  → Spine (nu F) as e → σ ⊢[ m ] e ⇛ e′
  → ∃ λ F′ → ∃ λ as′
    → Spine (nu F′) as′ e′ × (σ ⊢[ m ] F ⇛ F′) × (σ ⊢[ m ] as ⇛L as′)
spine-nu-one sp-[] (⇛-nu d) = _ , [] , sp-[] , d , ⇛L-[]
spine-nu-one (sp-snoc ()) (⇛-β _ _)
spine-nu-one (sp-snoc sp) (⇛-app df da) with spine-nu-one sp df
... | F′ , as′ , sp′ , dF , das =
  F′ , as′ ++ (_ ∷ []) , sp-snoc sp′ , dF , ⇛L-++ das (⇛L-∷ da ⇛L-[])

spine-nu-star : ∀ {σ m n} {F : Tm (suc n)} {as e e′}
  → Spine (nu F) as e → σ ⊢[ m ] e ⇛* e′
  → ∃ λ F′ → ∃ λ as′
    → Spine (nu F′) as′ e′ × (σ ⊢[ m ] F ⇛* F′) × (σ ⊢[ m ] as ⇛L* as′)
spine-nu-star sp ⇛*-refl = _ , _ , sp , ⇛*-refl , ⇛L*-refl _
spine-nu-star sp (⇛*-step s r) with spine-nu-one sp s
... | F₁ , as₁ , sp₁ , dF , das with spine-nu-star sp₁ r
... | F′ , as′ , sp′ , rF , ras =
  F′ , as′ , sp′ , ⇛*-step dF rF , ⇛L-⇛L* das ras

-- unfStepOf on an application succeeds only for a ν of a λ applied to
-- at least one index, and the goal is that λ instantiated at the ν
-- and then at the indices. The seed is ignored.
fam-of : ∀ {n} {S f a G fam}
  → unfStepOf S (app f a) ≡ ok (G , fam)
  → ∃ λ (q : Qty) → ∃ λ (A : Tm (suc n)) → ∃ λ (b : Tm (suc (suc n))) →
     ∃ λ (is : List (Tm n)) →
     Spine (nu (lam q A b)) is (app f a)
     × (G ≡ applyFam (inst (lam q A b) (nu (lam q A b))) is)
fam-of {n = n} {S = S} {f = f} {a = a} {G = G} {fam = fam} eq = go f a [] refl eq
  where
  -- The index list is i ∷ is, so it is never empty: a bare ν is not an
  -- application, and unfFam only returns the family goal for a λ.
  go : ∀ h i is → app f a ≡ appsFrom h (i ∷ is)
    → unfSpine S (unspine-go h (i ∷ is)) ≡ ok (G , fam)
    → ∃ λ (q : Qty) → ∃ λ (A : Tm (suc n)) → ∃ λ (b : Tm (suc (suc n))) →
       ∃ λ (is′ : List (Tm n)) →
       Spine (nu (lam q A b)) is′ (app f a)
       × (G ≡ applyFam (inst (lam q A b) (nu (lam q A b))) is′)
  go (app f′ a′) i is eq eq′ = go f′ a′ (i ∷ is) eq eq′
  go (nu (lam q A b)) i is eq eq′ =
    let p = ×2 (ok-inj eq′) in
    q , A , b , (i ∷ is) ,
    subst (Spine (nu (lam q A b)) (i ∷ is)) (sym eq)
      (Spine-appsFrom (nu (lam q A b)) (i ∷ is)) ,
    sym (proj₁ p)
  go (nu (var _)) _ _ _ ()
  go (nu typ) _ _ _ ()
  go (nu (pi _ _ _)) _ _ _ ()
  go (nu (app _ _)) _ _ _ ()
  go (nu nat) _ _ _ ()
  go (nu ze) _ _ _ ()
  go (nu (su _)) _ _ _ ()
  go (nu unit) _ _ _ ()
  go (nu one) _ _ _ ()
  go (nu empty) _ _ _ ()
  go (nu (dty _)) _ _ _ ()
  go (nu (ctor _ _)) _ _ _ ()
  go (nu (mData _ _ _)) _ _ _ ()
  go (nu (mNat _ _ _ _)) _ _ _ ()
  go (nu (mEmp _ _)) _ _ _ ()
  go (nu (mUnit _ _ _)) _ _ _ ()
  go (nu (idt _ _ _)) _ _ _ ()
  go (nu rfl) _ _ _ ()
  go (nu (rwt _ _ _)) _ _ _ ()
  go (nu (def _)) _ _ _ ()
  go (nu (ann _ _)) _ _ _ ()
  go (nu (prod _ _)) _ _ _ ()
  go (nu (pair _ _)) _ _ _ ()
  go (nu (letp _ _)) _ _ _ ()
  go (nu (nu _)) _ _ _ ()
  go (nu (unf _ _)) _ _ _ ()
  go (nu (ucons _)) _ _ _ ()
  go (nu i64) _ _ _ ()
  go (nu f32ty) _ _ _ ()
  go (nu (tensor _ _)) _ _ _ ()
  go (nu (addi _ _)) _ _ _ ()
  go (nu (muli _ _)) _ _ _ ()
  go (nu (addt _ _)) _ _ _ ()
  go (nu (toi64 _)) _ _ _ ()
  go (nu (packi _ _)) _ _ _ ()
  go (var _) _ _ _ ()
  go typ _ _ _ ()
  go (pi _ _ _) _ _ _ ()
  go (lam _ _ _) _ _ _ ()
  go nat _ _ _ ()
  go ze _ _ _ ()
  go (su _) _ _ _ ()
  go unit _ _ _ ()
  go one _ _ _ ()
  go empty _ _ _ ()
  go (dty _) _ _ _ ()
  go (ctor _ _) _ _ _ ()
  go (mData _ _ _) _ _ _ ()
  go (mNat _ _ _ _) _ _ _ ()
  go (mEmp _ _) _ _ _ ()
  go (mUnit _ _ _) _ _ _ ()
  go (idt _ _ _) _ _ _ ()
  go rfl _ _ _ ()
  go (rwt _ _ _) _ _ _ ()
  go (def _) _ _ _ ()
  go (ann _ _) _ _ _ ()
  go (prod _ _) _ _ _ ()
  go (pair _ _) _ _ _ ()
  go (letp _ _) _ _ _ ()
  go (unf _ _) _ _ _ ()
  go (ucons _) _ _ _ ()
  go i64 _ _ _ ()
  go f32ty _ _ _ ()
  go (tensor _ _) _ _ _ ()
  go (addi _ _) _ _ _ ()
  go (muli _ _) _ _ _ ()
  go (addt _ _) _ _ _ ()
  go (toi64 _) _ _ _ ()
  go (packi _ _) _ _ _ ()

-- Two ν spines that join have the same instantiated family goal.
-- The λ lives under the ν binder: its domain is a term one level up.
fam-join : ∀ {σ n q q′} {A : Tm (suc n)} {b : Tm (suc (suc n))}
    {A′ : Tm (suc n)} {b′ : Tm (suc (suc n))}
    {is is′ : List (Tm n)} {f a f′ a′ : Tm n}
  → Spine (nu (lam q A b)) is (app f a)
  → Spine (nu (lam q′ A′ b′)) is′ (app f′ a′)
  → σ ⊢[ spec ] app f a ≈ app f′ a′
  → σ ⊢[ spec ]
      applyFam (inst (lam q A b) (nu (lam q A b))) is
    ≈ applyFam (inst (lam q′ A′ b′) (nu (lam q′ A′ b′))) is′
fam-join {σ = σ} {q = q} {q′ = q′} {A = A} {b = b} {A′ = A′} {b′ = b′}
    {is = is} {is′ = is′} {f = f} {a = a} {f′ = f′} {a′ = a′} sp sp′ c =
  go (≈→join c)
  where
  F  = lam q A b
  F0 = lam q′ A′ b′
  goal = σ ⊢[ spec ] applyFam (inst F (nu F)) is ≈ applyFam (inst F0 (nu F0)) is′
  go : (∃ λ v → (σ ⊢[ spec ] app f a ⇛* v) × (σ ⊢[ spec ] app f′ a′ ⇛* v)) → goal
  go (v , tv , uv) = close (spine-nu-star sp tv) (spine-nu-star sp′ uv)
    where
    close :
      (∃ λ G1 → ∃ λ i1 →
         Spine (nu G1) i1 v × (σ ⊢[ spec ] F ⇛* G1) × (σ ⊢[ spec ] is ⇛L* i1))
      → (∃ λ G2 → ∃ λ i2 →
         Spine (nu G2) i2 v × (σ ⊢[ spec ] F0 ⇛* G2) × (σ ⊢[ spec ] is′ ⇛L* i2))
      → goal
    close (_ , _ , spv , rF , ris) (_ , _ , spv′ , rF′ , ris′) =
      done (Spine-unique head-nu head-nu spv spv′) rF rF′ ris ris′
      where
      done : ∀ {G1 i1 G2 i2}
        → (nu G1 ≡ nu G2) × (i1 ≡ i2)
        → σ ⊢[ spec ] F ⇛* G1 → σ ⊢[ spec ] F0 ⇛* G2
        → σ ⊢[ spec ] is ⇛L* i1 → σ ⊢[ spec ] is′ ⇛L* i2
        → goal
      done (refl , refl) rF rF′ ris ris′ =
        ≈-trans (≈-sym (apps-apply (inst F (nu F)) is))
          (≈-trans
            (≈-appsFrom (≈-inst₂ (join→≈ rF rF′) (≈-nu (join→≈ rF rF′)))
                        (join→≈L ris ris′))
            (apps-apply (inst F0 (nu F0)) is′))

-- The two fam-of results are matched here, at a fixed context level,
-- and handed to fam-join.
fam-apps : ∀ {σ n S} {f a : Tm n} {G0 : Tm n} {T f′ a′ G fam}
  → unfStepOf S (app f a) ≡ ok (G0 , true)
  → σ ⊢[ spec ] app f a ≈ app f′ a′
  → unfStepOf T (app f′ a′) ≡ ok (G , fam)
  → σ ⊢[ spec ] G0 ≈ G
fam-apps {σ = σ} {n = n} st0 c st with fam-of st0
... | q , A , b , is , sp , refl with fam-of st
... | q′ , A′ , b′ , is′ , sp′ , refl =
  fam-join {σ = σ} {n = n} {q = q} {q′ = q′} {A = A} {b = b}
    {A′ = A′} {b′ = b′} {is = is} {is′ = is′} sp sp′ c

-- Two successful family steps at convertible types have convertible
-- goals. unfFam does not read the seed, and a ν spine reduces only in
-- its body and its indices.
fam-goal : ∀ {σ n} {S T0 G0 T T′ G fam}
  → unfStepOf S T0 ≡ ok (G0 , true)
  → σ ⊢[ spec ] T0 ≈ T
  → σ ⊢[ spec ] T ≈ T′
  → unfStepOf T T′ ≡ ok (G , fam)
  → σ ⊢[ spec ] G0 ≈ G
fam-goal {σ = σ} {n = n} {S = S} {T0 = app f a} {G0 = G0} {T = T}
    {T′ = app f′ a′} {G = G} {fam = fam} st0 cS c st =
  fam-apps {σ = σ} {n = n} {S = S} {f = f} {a = a} {G0 = G0} {T = T}
    {f′ = f′} {a′ = a′} {G = G} {fam = fam} st0 (≈-trans cS c) st
fam-goal {T0 = app _ _} {T′ = nu _} st0 cS c _ =
  ⊥-elim (nu-app-body st0 (≈-sym (≈-trans cS c)))
fam-goal {T0 = app _ _} {T′ = var _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = typ} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = pi _ _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = lam _ _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = nat} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = ze} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = su _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = unit} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = one} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = empty} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = dty _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = ctor _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = mData _ _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = mNat _ _ _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = mEmp _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = mUnit _ _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = idt _ _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = rfl} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = rwt _ _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = def _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = ann _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = prod _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = pair _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = letp _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = unf _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = ucons _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = i64} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = f32ty} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = tensor _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = addi _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = muli _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = addt _ _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = toi64 _} _ _ _ ()
fam-goal {T0 = app _ _} {T′ = packi _ _} _ _ _ ()
fam-goal {T0 = nu _} st0 _ _ _ = ⊥-elim (false≢true (proj₂ (×2 (ok-inj st0))))
fam-goal {T0 = var _} ()
fam-goal {T0 = typ} ()
fam-goal {T0 = pi _ _ _} ()
fam-goal {T0 = lam _ _ _} ()
fam-goal {T0 = nat} ()
fam-goal {T0 = ze} ()
fam-goal {T0 = su _} ()
fam-goal {T0 = unit} ()
fam-goal {T0 = one} ()
fam-goal {T0 = empty} ()
fam-goal {T0 = dty _} ()
fam-goal {T0 = ctor _ _} ()
fam-goal {T0 = mData _ _ _} ()
fam-goal {T0 = mNat _ _ _ _} ()
fam-goal {T0 = mEmp _ _} ()
fam-goal {T0 = mUnit _ _ _} ()
fam-goal {T0 = idt _ _ _} ()
fam-goal {T0 = rfl} ()
fam-goal {T0 = rwt _ _ _} ()
fam-goal {T0 = def _} ()
fam-goal {T0 = ann _ _} ()
fam-goal {T0 = prod _ _} ()
fam-goal {T0 = pair _ _} ()
fam-goal {T0 = letp _ _} ()
fam-goal {T0 = unf _ _} ()
fam-goal {T0 = ucons _} ()
fam-goal {T0 = i64} ()
fam-goal {T0 = f32ty} ()
fam-goal {T0 = tensor _ _} ()
fam-goal {T0 = addi _ _} ()
fam-goal {T0 = muli _ _} ()
fam-goal {T0 = addt _ _} ()
fam-goal {T0 = toi64 _} ()
fam-goal {T0 = packi _ _} ()

-- uncons of a family unfold reads the pair. The components are already
-- the head obligation and the tail proof, so the reduct is that pair.
pres-ιr : ∀ {σ n} {Γ : Ctx n} {m q s S A h t T0 G0 T T′ G fam}
  → σ , Γ ⊨[ m ] s ∶ S
  → σ ⊢[ spec ] A ≈ S
  → unfStepOf S T0 ≡ ok (G0 , true)
  → σ , ext Γ q S ⊨[ m ] pair h t ∶ wk G0
  → σ ⊢[ spec ] T0 ≈ T
  → σ ⊢[ spec ] T ≈ T′
  → unfStepOf T T′ ≡ ok (G , fam)
  → σ , Γ ⊨[ m ] pair (inst h s) (inst t s) ∶ G
pres-ιr {m = m} {q = q} {G0 = G0} Ds _ stG Dp cS c st with Dp
... | conv (t-pair Dh Dt) cp =
  let Darg = ⊨-mode (≤ᵐ-modeFor q m) Ds
      Dread = conv-≈ (conv (t-pair (⊨-inst ≤ᵐ-refl Dh Darg) (⊨-inst ≤ᵐ-refl Dt Darg)) ≈-refl)
                (≈-trans (≈-sub (instσ _) cp) (≈-≡ (inst-wk G0 _)))
  in conv-≈ Dread (fam-goal stG cS c st)

pres-ι0 : ∀ {σ n} {Γ : Ctx n} {m a b q A T T′ G fam}
  → WfSig σ
  → σ , Γ ⊨[ m ] unf (pair a b) (lam q A (var zero)) ∶ T
  → σ ⊢[ spec ] T ≈ T′
  → unfStepOf T T′ ≡ ok (G , fam)
  → σ , Γ ⊨[ m ] pair a (unf b (lam q A (var zero))) ∶ G
pres-ι0 {σ = σ} {m = m} {q = q} {G = G} wf (conv (t-unf {S = S} {A = Eh} Ds Df) cU) cT st =
  body Df Ds
  where
  body : σ , _ ⊨[ m ] lam q _ (var zero) ∶ pi _ S (prod (wk Eh) (wk S))
    → σ , _ ⊨[ m ] pair _ _ ∶ S
    → σ , _ ⊨[ m ] pair _ (unf _ (lam q _ (var zero))) ∶ G
  body (conv (t-lam _ _ _ (conv (t-var _) cB)) cpi) (conv (t-pair Da Db) cp)
    with ≈-pi-inj cpi
  ... | refl , cDom , cCod =
    let cS = ≈-wk-inj (≈-trans (≈-sym (≈-ren suc cDom)) (≈-trans cB cCod))
        cEh , cTail = ≈-prod-inj (≈-trans cp cS)
        Dseed = conv-≈ Db cTail
        Dtail = conv (t-unf Dseed Df) ≈-refl
        Dhead = conv-≈ Da cEh
    in conv-≈ (conv (t-pair Dhead Dtail) ≈-refl) (stream-goal cU cT st)

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
pres⁰ wf (t-nu _) ()
pres⁰ wf (t-unf _ _) ()
pres⁰ wf (t-unfG _ _ _ _ _) ()
pres⁰ wf (t-unfR _ _ _ _ _) ()
pres⁰ wf (t-ucons Ds c st) (ucons-e s) =
  conv (t-ucons (pres wf Ds s) c st) ≈-refl
pres⁰ wf (t-ucons Ds c st) ι-ucons-p = pres-ιp wf Ds c st
pres⁰ wf (t-ucons Ds c st) ι-ucons-0 = pres-ι0 wf Ds c st
pres⁰ wf (t-ucons (conv (t-unf _ (conv (t-pair _ _) cp)) _) _ _) ι-ucons-r
  with ≈-shape h-prod h-pi cp
... | ()
pres⁰ wf (t-ucons (conv (t-unfR Ds cA stG refl Dp) cS) c st) ι-ucons-r =
  pres-ιr Ds cA stG Dp cS c st

pres* : ∀ {σ n} {Γ : Ctx n} {m m′ e e′ A}
  → WfSig σ
  → σ , Γ ⊨[ m ] e ∶ A → σ ⊢[ m′ ] e ⟶* e′ → σ , Γ ⊨[ m ] e′ ∶ A
pres* wf D ⟶*-refl = D
pres* wf D (⟶*-step s r) = pres* wf (pres wf D s) r

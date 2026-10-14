------------------------------------------------------------------------
-- Closed evidence of Empty, on the ⊢ fragment, under --safe.
--
-- Proved here, with conversion the relation ≈ of Muro.Convert:
--
--   Empty-intro      an introduction form (ze, su, one, λ, refl) never
--                    checks against Empty, in any σ, Γ, and mode;
--   Empty-nf         no closed normal evidence term has type Empty
--                    (canonical evidence forms at Empty do not exist),
--                    for ⊢ and for the declarative ⊨ of Muro.Typing;
--                    σ-empty declares no data type, so constructor and
--                    dty spines are untyped here;
--   progress-⇐       a closed well-typed evidence term is normal or
--                    takes a ⟶ step;
--   preservation     a ⟶ step keeps closed evidence at Empty (⊨), a
--                    corollary of Muro.Typing.pres;
--   Empty-evid-from  normalisation of closed evidence gives: no closed
--                    evidence of Empty. The hypothesis is an argument
--                    of the lemma. Nothing is postulated.
--
-- Not proved: Empty-evid itself. What is missing is exactly the
-- hypothesis of Empty-evid-from: normalisation of closed evidence
-- terms. Type is impredicative (Π (X : Type) → X : Type), so a
-- set-theoretic model in Agda is not available; the argument must be
-- syntactic (reducibility candidates), and for evid it can use that
-- evid is affine outside Data.
-- Do not cite Empty-evid as a theorem of this development.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Consistency where

open import Data.Bool.Base using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_; ∃; Σ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst using (appsFrom)
open import Muro.Env
open import Muro.Spine
open import Muro.Reduction
open import Muro.Convert
open import Muro.Check using (unfStepOf; unfSpine)
open import Muro.Frag using (us-pair; us-id; us-step)
open import Muro.Judgement
open import Muro.Typing

fail≢ok : ∀ {A : Set} {e} {d : A} → fail e ≡ ok d → ⊥
fail≢ok ()

------------------------------------------------------------------------
-- σ-empty has no data types: no constructor or dty spine is typed.
------------------------------------------------------------------------

ctor-no-⇒ : ∀ {n} {Γ : Ctx n} {m i j as e B u}
  → Spine (ctor i j) as e → σ-empty , Γ ⊢[ m ] e ⇒ B ⊣ u → ⊥
ctor-no-⇒ sp-[] ()
ctor-no-⇒ (sp-snoc sp) (⇒-app-aff D _ _ _) = ctor-no-⇒ sp D
ctor-no-⇒ (sp-snoc sp) (⇒-app-era D _ _) = ctor-no-⇒ sp D
ctor-no-⇒ (sp-snoc sp) (⇒-app-reuse D _ _ _ _) = ctor-no-⇒ sp D
ctor-no-⇒ (sp-snoc sp) (⇒-app-copy D _ _ _ _) = ctor-no-⇒ sp D

ctor-no-⇐ : ∀ {n} {Γ : Ctx n} {m i j as e A u}
  → Spine (ctor i j) as e → σ-empty , Γ ⊢[ m ] e ⇐ A ⊣ u → ⊥
ctor-no-⇐ sp (⇐-conv D _) = ctor-no-⇒ sp D
ctor-no-⇐ _ (⇐-ctor _ _ lk _ _ _ _ _ _) = fail≢ok lk
ctor-no-⇐ () (⇐-lam _ _ _ _ _ _)
ctor-no-⇐ () (⇐-refl _ _ _)
ctor-no-⇐ () (⇐-pair _ _ _ _)
ctor-no-⇐ () (⇐-letp _ _ _ _ _ _)
ctor-no-⇐ () (⇐-unf _ _ _ _ _ _ _ _)
ctor-no-⇐ () (⇐-unfR _ _ _ _ _ _ _ _)

dty-no-⇒ : ∀ {n} {Γ : Ctx n} {m i as e B u}
  → Spine (dty i) as e → σ-empty , Γ ⊢[ m ] e ⇒ B ⊣ u → ⊥
dty-no-⇒ sp-[] (⇒-dty lk) = fail≢ok lk
dty-no-⇒ (sp-snoc sp) (⇒-app-aff D _ _ _) = dty-no-⇒ sp D
dty-no-⇒ (sp-snoc sp) (⇒-app-era D _ _) = dty-no-⇒ sp D
dty-no-⇒ (sp-snoc sp) (⇒-app-reuse D _ _ _ _) = dty-no-⇒ sp D
dty-no-⇒ (sp-snoc sp) (⇒-app-copy D _ _ _ _) = dty-no-⇒ sp D

dty-no-⇐ : ∀ {n} {Γ : Ctx n} {m i as e A u}
  → Spine (dty i) as e → σ-empty , Γ ⊢[ m ] e ⇐ A ⊣ u → ⊥
dty-no-⇐ sp (⇐-conv D _) = dty-no-⇒ sp D
dty-no-⇐ _ (⇐-ctor _ _ lk _ _ _ _ _ _) = fail≢ok lk
dty-no-⇐ () (⇐-lam _ _ _ _ _ _)
dty-no-⇐ () (⇐-refl _ _ _)
dty-no-⇐ () (⇐-pair _ _ _ _)
dty-no-⇐ () (⇐-letp _ _ _ _ _ _)
dty-no-⇐ () (⇐-unf _ _ _ _ _ _ _ _)
dty-no-⇐ () (⇐-unfR _ _ _ _ _ _ _ _)

ctor-no⊨ : ∀ {n} {Γ : Ctx n} {m i j as e A}
  → Spine (ctor i j) as e → σ-empty , Γ ⊨⁰[ m ] e ∶ A → ⊥
ctor-no⊨ sp D with ctor-inv sp D
... | ca lk _ _ _ _ _ = fail≢ok lk

dty-no⊨ : ∀ {n} {Γ : Ctx n} {m i as e A}
  → Spine (dty i) as e → σ-empty , Γ ⊨⁰[ m ] e ∶ A → ⊥
dty-no⊨ sp (t-ctor sp′ _) with Spine-unique head-dty head-ctor sp sp′
... | () , _
dty-no⊨ sp-[] (t-dty lk) = fail≢ok lk
dty-no⊨ (sp-snoc sp) (t-app-aff (conv D _) _) = dty-no⊨ sp D
dty-no⊨ (sp-snoc sp) (t-app-era (conv D _) _) = dty-no⊨ sp D
dty-no⊨ (sp-snoc sp) (t-app-reuse (conv D _) _ _) = dty-no⊨ sp D

------------------------------------------------------------------------
-- The term `empty` is spec-only.
------------------------------------------------------------------------

no-evid-empty-⇒ : ∀ {σ n} {Γ : Ctx n} {A u} →
  σ , Γ ⊢[ evid ] empty ⇒ A ⊣ u → ⊥
no-evid-empty-⇒ ()

no-evid-empty-⇐ : ∀ {σ n} {Γ : Ctx n} {A u} →
  σ , Γ ⊢[ evid ] empty ⇐ A ⊣ u → ⊥
no-evid-empty-⇐ (⇐-conv D _) = no-evid-empty-⇒ D
no-evid-empty-⇐ (⇐-ctor () _ _ _ _ _ _ _ _)

------------------------------------------------------------------------
-- Introduction forms are never evidence of Empty: they infer a canonical
-- type former other than Empty, and ≈ separates distinct normal forms.
------------------------------------------------------------------------

data Intro {n} : Tm n → Set where
  i-ze   : Intro ze
  i-su   : ∀ {t} → Intro (su t)
  i-one  : Intro one
  i-lam  : ∀ {q A t} → Intro (lam q A t)
  i-rfl  : Intro rfl
  i-pair : ∀ {a b} → Intro (pair a b)

Empty-intro-⇒ : ∀ {σ n} {Γ : Ctx n} {m e B u} →
  Intro e → σ , Γ ⊢[ m ] e ⇒ B ⊣ u → σ ⊢[ spec ] B ≈ empty → ⊥
Empty-intro-⇒ i-ze ⇒-ze c with ≈-shape h-nat h-empty c
... | ()
Empty-intro-⇒ i-su (⇒-su _) c with ≈-shape h-nat h-empty c
... | ()
Empty-intro-⇒ i-one ⇒-one c with ≈-shape h-unit h-empty c
... | ()
Empty-intro-⇒ i-lam (⇒-lam _ _ _ _) c with ≈-shape h-pi h-empty c
... | ()
Empty-intro-⇒ i-rfl () _
Empty-intro-⇒ i-pair (⇒-pair _ _ _) c with ≈-shape h-prod h-empty c
... | ()

Empty-intro : ∀ {σ n} {Γ : Ctx n} {m e u} →
  Intro e → σ , Γ ⊢[ m ] e ⇐ empty ⊣ u → ⊥
Empty-intro i (⇐-conv D c) = Empty-intro-⇒ i D c
Empty-intro i-lam (⇐-lam _ c _ _ _ _) with ≈-shape h-empty h-pi c
... | ()
Empty-intro i-rfl (⇐-refl c _ _) with ≈-shape h-empty h-idt c
... | ()
Empty-intro i-pair (⇐-pair c _ _ _) with ≈-shape h-empty h-prod c
... | ()
Empty-intro i-ze (⇐-ctor () _ _ _ _ _ _ _ _)
Empty-intro i-su (⇐-ctor () _ _ _ _ _ _ _ _)
Empty-intro i-one (⇐-ctor () _ _ _ _ _ _ _ _)
Empty-intro i-lam (⇐-ctor () _ _ _ _ _ _ _ _)
Empty-intro i-rfl (⇐-ctor () _ _ _ _ _ _ _ _)
Empty-intro i-pair (⇐-ctor () _ _ _ _ _ _ _ _)

------------------------------------------------------------------------
-- Closed neutral terms are not evidence: there is no variable, no
-- definition in σ-empty, and no ⊢ rule for terms outside the fragment.
------------------------------------------------------------------------

ne-untyped-⇒ : ∀ {e B u} →
  Ne σ-empty evid e → σ-empty , ε ⊢[ evid ] e ⇒ B ⊣ u → ⊥
ne-untyped-⇐ : ∀ {e A u} →
  Ne σ-empty evid e → σ-empty , ε ⊢[ evid ] e ⇐ A ⊣ u → ⊥

ne-untyped-⇒ (ne-var {x = ()}) _
ne-untyped-⇒ (ne-def _) (⇒-def lk _) = fail≢ok lk
ne-untyped-⇒ (ne-app ne) (⇒-app-aff D _ _ _) = ne-untyped-⇒ ne D
ne-untyped-⇒ (ne-app ne) (⇒-app-era D _ _) = ne-untyped-⇒ ne D
ne-untyped-⇒ (ne-app ne) (⇒-app-reuse D _ _ _ _) = ne-untyped-⇒ ne D
ne-untyped-⇒ (ne-app ne) (⇒-app-copy D _ _ _ _) = ne-untyped-⇒ ne D
ne-untyped-⇒ (ne-mNat ne) (⇒-mNat D _ _ _ _ _) = ne-untyped-⇐ ne D
ne-untyped-⇒ (ne-mUnit ne) (⇒-mUnit D _ _ _) = ne-untyped-⇐ ne D
ne-untyped-⇒ (ne-mEmp ne) (⇒-mEmp D _) = ne-untyped-⇐ ne D
ne-untyped-⇒ (ne-rwt ne) (⇒-rwt D _ _ _) = ne-untyped-⇒ ne D
ne-untyped-⇒ (ne-mData ne) (⇒-mData D _ _ _ _ _ _ _) = ne-untyped-⇒ ne D
ne-untyped-⇒ (ne-letp ne) (⇒-letp D _ _ _ _ _ _) = ne-untyped-⇒ ne D
ne-untyped-⇒ (ne-ucons ne) (⇒-ucons D _ _) = ne-untyped-⇒ ne D
ne-untyped-⇒ (ne-foreign f-i64) ()
ne-untyped-⇒ (ne-foreign f-f32ty) ()
ne-untyped-⇒ (ne-foreign f-tensor) ()
ne-untyped-⇒ (ne-foreign f-addi) ()
ne-untyped-⇒ (ne-foreign f-muli) ()
ne-untyped-⇒ (ne-foreign f-addt) ()
ne-untyped-⇒ (ne-foreign f-toi64) ()
ne-untyped-⇒ (ne-foreign f-packi) ()

ne-untyped-⇐ ne (⇐-conv D _) = ne-untyped-⇒ ne D
ne-untyped-⇐ _ (⇐-ctor _ _ lk _ _ _ _ _ _) = fail≢ok lk
ne-untyped-⇐ (ne-foreign ()) (⇐-lam _ _ _ _ _ _)
ne-untyped-⇐ (ne-foreign ()) (⇐-refl _ _ _)
ne-untyped-⇐ (ne-foreign ()) (⇐-pair _ _ _ _)
ne-untyped-⇐ (ne-letp ne) (⇐-letp D _ _ _ _ _) = ne-untyped-⇒ ne D
ne-untyped-⇐ (ne-foreign ()) (⇐-unf _ _ _ _ _ _ _ _)
ne-untyped-⇐ (ne-foreign ()) (⇐-unfR _ _ _ _ _ _ _ _)

-- unfStepOf on an application succeeds only when the head is ν, so the
-- application is a ν spine and stays one under reduction.
ok-nu-app : ∀ {n} {S G fam} {f a : Tm n}
  → unfStepOf S (app f a) ≡ ok (G , fam)
  → Σ (NuSpine (app f a)) (λ p → appish p ≡ true)
ok-nu-app {S = S} {G = G} {fam = fam} {f = f} {a = a} eq = go f a [] eq
  where
  go : ∀ h i is → unfSpine S (unspine-go h (i ∷ is)) ≡ ok (G , fam)
    → Σ (NuSpine (appsFrom h (i ∷ is))) (λ p → appish p ≡ true)
  go (app h′ b) i is eq′ = go h′ b (i ∷ is) eq′
  go (nu F) i is _ = ns-apps F i is , appish-apps F i is
  go (var _) _ _ ()
  go typ _ _ ()
  go (pi _ _ _) _ _ ()
  go (lam _ _ _) _ _ ()
  go nat _ _ ()
  go ze _ _ ()
  go (su _) _ _ ()
  go unit _ _ ()
  go one _ _ ()
  go empty _ _ ()
  go (dty _) _ _ ()
  go (ctor _ _) _ _ ()
  go (mData _ _ _) _ _ ()
  go (mNat _ _ _ _) _ _ ()
  go (mEmp _ _) _ _ ()
  go (mUnit _ _ _) _ _ ()
  go (idt _ _ _) _ _ ()
  go rfl _ _ ()
  go (rwt _ _ _) _ _ ()
  go (def _) _ _ ()
  go (ann _ _) _ _ ()
  go (prod _ _) _ _ ()
  go (pair _ _) _ _ ()
  go (letp _ _) _ _ ()
  go (unf _ _) _ _ ()
  go (ucons _) _ _ ()
  go i64 _ _ ()
  go f32ty _ _ ()
  go (tensor _ _) _ _ ()
  go (addi _ _) _ _ ()
  go (muli _ _) _ _ ()
  go (addt _ _) _ _ ()
  go (toi64 _) _ _ ()
  go (packi _ _) _ _ ()

-- An application is not a shaped term. A bare ν is.
shape-app : ∀ {n s} {t : Tm n}
  → HasShape t s → (h : NuSpine t) → appish h ≡ true → ⊥
shape-app _ ns-nu ()
shape-app () (ns-app _) _

-- The type a ν step reads is not a shaped term of a different head.
-- A bare ν keeps shape s-nu. An application of one stays an application.
rigid-spine : ∀ {σ n} {S T′ G : Tm n} {fam s} {A : Tm n}
  → HasShape A s → (s ≡ s-nu → ⊥)
  → unfStepOf S T′ ≡ ok (G , fam)
  → σ ⊢[ spec ] A ≈ T′ → ⊥
rigid-spine {σ = σ} {S = S} {G = G} {fam = fam} {s = s} hs diff eq c with ≈→join c
... | v , rv , uv = side eq uv (shape-⇛* hs rv)
  where
  side : ∀ {T′} → unfStepOf S T′ ≡ ok (G , fam)
    → σ ⊢[ spec ] T′ ⇛* v → HasShape v s → ⊥
  side {nu _} _ r hv with nu-⇛* r
  ... | _ , refl , _ = diff (shape-unique hv h-nu)
  side {app _ _} eq′ r hv =
    let p , q = ok-nu-app eq′ in
    shape-app hv (ns-star p r) (ns-keep* p q r)
  side {var _} () _ _
  side {typ} () _ _
  side {pi _ _ _} () _ _
  side {lam _ _ _} () _ _
  side {nat} () _ _
  side {ze} () _ _
  side {su _} () _ _
  side {unit} () _ _
  side {one} () _ _
  side {empty} () _ _
  side {dty _} () _ _
  side {ctor _ _} () _ _
  side {mData _ _ _} () _ _
  side {mNat _ _ _ _} () _ _
  side {mEmp _ _} () _ _
  side {mUnit _ _ _} () _ _
  side {idt _ _ _} () _ _
  side {rfl} () _ _
  side {rwt _ _ _} () _ _
  side {def _} () _ _
  side {ann _ _} () _ _
  side {prod _ _} () _ _
  side {pair _ _} () _ _
  side {letp _ _} () _ _
  side {unf _ _} () _ _
  side {ucons _} () _ _
  side {i64} () _ _
  side {f32ty} () _ _
  side {tensor _ _} () _ _
  side {addi _ _} () _ _
  side {muli _ _} () _ _
  side {addt _ _} () _ _
  side {toi64 _} () _ _
  side {packi _ _} () _ _

------------------------------------------------------------------------
-- No closed normal evidence of Empty.
------------------------------------------------------------------------

Empty-nf : ∀ {e u} →
  Nf σ-empty evid e → σ-empty , ε ⊢[ evid ] e ⇐ empty ⊣ u → ⊥
Empty-nf _ (⇐-ctor _ _ lk _ _ _ _ _ _) = fail≢ok lk
Empty-nf (nf-ne ne) D = ne-untyped-⇐ ne D
Empty-nf (nf-ctor sp) D = ctor-no-⇐ sp D
Empty-nf (nf-dty sp) D = dty-no-⇐ sp D
Empty-nf nf-typ (⇐-conv () _)
Empty-nf nf-pi (⇐-conv () _)
Empty-nf nf-lam D = Empty-intro i-lam D
Empty-nf nf-nat (⇐-conv () _)
Empty-nf nf-ze D = Empty-intro i-ze D
Empty-nf nf-su D = Empty-intro i-su D
Empty-nf nf-unit (⇐-conv () _)
Empty-nf nf-one D = Empty-intro i-one D
Empty-nf nf-empty D = no-evid-empty-⇐ D
Empty-nf nf-idt (⇐-conv () _)
Empty-nf nf-rfl D = Empty-intro i-rfl D
Empty-nf nf-prod (⇐-conv () _)
Empty-nf nf-pair D = Empty-intro i-pair D
Empty-nf nf-nu (⇐-conv () _)
Empty-nf nf-unf (⇐-conv (⇒-unf _ _ _ _ _) c) with ≈-shape h-nu h-empty c
... | ()
Empty-nf nf-unf (⇐-unf _ _ c _ refl _ _ _) with ≈-shape h-empty h-nu c
... | ()
Empty-nf nf-unf (⇐-unfR _ _ cT st _ _ _ _) =
  ⊥-elim (rigid-spine h-empty (λ ()) st cT) 


------------------------------------------------------------------------
-- Progress: a closed well-typed evidence term is normal or steps.
------------------------------------------------------------------------

Step : Tm 0 → Set
Step e = ∃ λ e′ → σ-empty ⊢[ evid ] e ⟶ e′

Prog : Tm 0 → Set
Prog e = Nf σ-empty evid e ⊎ Step e

-- uncons of a closed evidence term. An inferred unfold has UShape, so
-- the step is the stream wrap or the identity unfold. A neutral
-- scrutinee stays neutral. Any other canonical form has a type whose
-- shape is not a ν spine.
ucons-canon : ∀ {s T T′ G fam u} →
  Nf σ-empty evid s →
  σ-empty , ε ⊢[ evid ] s ⇒ T ⊣ u →
  σ-empty ⊢[ spec ] T ≈ T′ →
  unfStepOf T T′ ≡ ok (G , fam) →
  Prog (ucons s)
ucons-canon (nf-ne ne) _ _ _ = inj₁ (nf-ne (ne-ucons ne))
ucons-canon nf-ze ⇒-ze c st = ⊥-elim (rigid-spine h-nat (λ ()) st c)
ucons-canon nf-su (⇒-su _) c st = ⊥-elim (rigid-spine h-nat (λ ()) st c)
ucons-canon nf-one ⇒-one c st = ⊥-elim (rigid-spine h-unit (λ ()) st c)
ucons-canon nf-lam (⇒-lam _ _ _ _) c st = ⊥-elim (rigid-spine h-pi (λ ()) st c)
ucons-canon nf-pair (⇒-pair _ _ _) c st = ⊥-elim (rigid-spine h-prod (λ ()) st c)
ucons-canon nf-unf (⇒-unf _ _ _ us-pair _) _ _ = inj₂ (_ , ι-ucons-p)
ucons-canon nf-unf (⇒-unf _ _ _ us-id _) _ _ = inj₂ (_ , ι-ucons-0)
ucons-canon nf-unf (⇒-unf _ _ _ us-step _) _ _ = inj₂ (_ , ι-ucons-r)
ucons-canon (nf-ctor sp) D _ _ = ⊥-elim (ctor-no-⇒ sp D)
ucons-canon (nf-dty sp) D _ _ = ⊥-elim (dty-no-⇒ sp D)
ucons-canon nf-typ ()
ucons-canon nf-pi ()
ucons-canon nf-nat ()
ucons-canon nf-unit ()
ucons-canon nf-empty ()
ucons-canon nf-idt ()
ucons-canon nf-rfl ()
ucons-canon nf-prod ()
ucons-canon nf-nu ()

data IsLam {n} : Tm n → Set where
  is-lam : ∀ {q A t} → IsLam (lam q A t)

-- Canonical forms, for normal closed evidence at each type former.

nf-fun : ∀ {f F q A B u} →
  Nf σ-empty evid f → σ-empty , ε ⊢[ evid ] f ⇒ F ⊣ u →
  σ-empty ⊢[ spec ] F ≈ pi q A B → IsLam f
nf-fun (nf-ne ne) D _ = ⊥-elim (ne-untyped-⇒ ne D)
nf-fun (nf-ctor sp) D _ = ⊥-elim (ctor-no-⇒ sp D)
nf-fun (nf-dty sp) D _ = ⊥-elim (dty-no-⇒ sp D)
nf-fun nf-lam _ _ = is-lam
nf-fun nf-ze ⇒-ze c with ≈-shape h-nat h-pi c
... | ()
nf-fun nf-su (⇒-su _) c with ≈-shape h-nat h-pi c
... | ()
nf-fun nf-one ⇒-one c with ≈-shape h-unit h-pi c
... | ()
nf-fun nf-typ () _
nf-fun nf-pi () _
nf-fun nf-nat () _
nf-fun nf-unit () _
nf-fun nf-empty () _
nf-fun nf-idt () _
nf-fun nf-rfl () _
nf-fun nf-prod () _
nf-fun nf-pair (⇒-pair _ _ _) c with ≈-shape h-prod h-pi c
... | ()
nf-fun nf-nu ()
nf-fun nf-unf (⇒-unf _ _ _ _ _) c with ≈-shape h-nu h-pi c
... | ()

nf-nat-prog : ∀ {e P z s u} →
  Nf σ-empty evid e → σ-empty , ε ⊢[ evid ] e ⇐ nat ⊣ u →
  Prog (mNat e P z s)
nf-nat-prog _ (⇐-ctor _ _ lk _ _ _ _ _ _) = ⊥-elim (fail≢ok lk)
nf-nat-prog (nf-ne ne) D = ⊥-elim (ne-untyped-⇐ ne D)
nf-nat-prog (nf-ctor sp) D = ⊥-elim (ctor-no-⇐ sp D)
nf-nat-prog (nf-dty sp) D = ⊥-elim (dty-no-⇐ sp D)
nf-nat-prog nf-ze _ = inj₂ (_ , ιz)
nf-nat-prog nf-su _ = inj₂ (_ , ιs)
nf-nat-prog nf-lam (⇐-conv (⇒-lam _ _ _ _) c) with ≈-shape h-pi h-nat c
... | ()
nf-nat-prog nf-lam (⇐-lam _ c _ _ _ _) with ≈-shape h-nat h-pi c
... | ()
nf-nat-prog nf-rfl (⇐-refl c _ _) with ≈-shape h-nat h-idt c
... | ()
nf-nat-prog nf-one (⇐-conv ⇒-one c) with ≈-shape h-unit h-nat c
... | ()
nf-nat-prog nf-typ (⇐-conv () _)
nf-nat-prog nf-pi (⇐-conv () _)
nf-nat-prog nf-nat (⇐-conv () _)
nf-nat-prog nf-unit (⇐-conv () _)
nf-nat-prog nf-empty (⇐-conv () _)
nf-nat-prog nf-idt (⇐-conv () _)
nf-nat-prog nf-rfl (⇐-conv () _)
nf-nat-prog nf-prod (⇐-conv () _)
nf-nat-prog nf-pair (⇐-conv (⇒-pair _ _ _) c) with ≈-shape h-prod h-nat c
... | ()
nf-nat-prog nf-pair (⇐-pair c _ _ _) with ≈-shape h-nat h-prod c
... | ()
nf-nat-prog nf-nu (⇐-conv () _)
nf-nat-prog nf-unf (⇐-conv (⇒-unf _ _ _ _ _) c) with ≈-shape h-nu h-nat c
... | ()
nf-nat-prog nf-unf (⇐-unf _ _ c _ refl _ _ _) with ≈-shape h-nat h-nu c
... | ()
nf-nat-prog nf-unf (⇐-unfR _ _ cT st _ _ _ _) =
  ⊥-elim (rigid-spine h-nat (λ ()) st cT)

nf-unit-prog : ∀ {e P t u} →
  Nf σ-empty evid e → σ-empty , ε ⊢[ evid ] e ⇐ unit ⊣ u →
  Prog (mUnit e P t)
nf-unit-prog _ (⇐-ctor _ _ lk _ _ _ _ _ _) = ⊥-elim (fail≢ok lk)
nf-unit-prog (nf-ne ne) D = ⊥-elim (ne-untyped-⇐ ne D)
nf-unit-prog (nf-ctor sp) D = ⊥-elim (ctor-no-⇐ sp D)
nf-unit-prog (nf-dty sp) D = ⊥-elim (dty-no-⇐ sp D)
nf-unit-prog nf-one _ = inj₂ (_ , ιtt)
nf-unit-prog nf-ze (⇐-conv ⇒-ze c) with ≈-shape h-nat h-unit c
... | ()
nf-unit-prog nf-su (⇐-conv (⇒-su _) c) with ≈-shape h-nat h-unit c
... | ()
nf-unit-prog nf-lam (⇐-conv (⇒-lam _ _ _ _) c) with ≈-shape h-pi h-unit c
... | ()
nf-unit-prog nf-lam (⇐-lam _ c _ _ _ _) with ≈-shape h-unit h-pi c
... | ()
nf-unit-prog nf-rfl (⇐-refl c _ _) with ≈-shape h-unit h-idt c
... | ()
nf-unit-prog nf-typ (⇐-conv () _)
nf-unit-prog nf-pi (⇐-conv () _)
nf-unit-prog nf-nat (⇐-conv () _)
nf-unit-prog nf-unit (⇐-conv () _)
nf-unit-prog nf-empty (⇐-conv () _)
nf-unit-prog nf-idt (⇐-conv () _)
nf-unit-prog nf-rfl (⇐-conv () _)
nf-unit-prog nf-prod (⇐-conv () _)
nf-unit-prog nf-pair (⇐-conv (⇒-pair _ _ _) c) with ≈-shape h-prod h-unit c
... | ()
nf-unit-prog nf-pair (⇐-pair c _ _ _) with ≈-shape h-unit h-prod c
... | ()
nf-unit-prog nf-nu (⇐-conv () _)
nf-unit-prog nf-unf (⇐-conv (⇒-unf _ _ _ _ _) c) with ≈-shape h-nu h-unit c
... | ()
nf-unit-prog nf-unf (⇐-unf _ _ c _ refl _ _ _) with ≈-shape h-unit h-nu c
... | ()
nf-unit-prog nf-unf (⇐-unfR _ _ cT st _ _ _ _) =
  ⊥-elim (rigid-spine h-unit (λ ()) st cT)

nf-eq-prog : ∀ {eq E A l r P t u} →
  Nf σ-empty evid eq → σ-empty , ε ⊢[ evid ] eq ⇒ E ⊣ u →
  σ-empty ⊢[ spec ] E ≈ idt A l r → Prog (rwt eq P t)
nf-eq-prog (nf-ne ne) D _ = ⊥-elim (ne-untyped-⇒ ne D)
nf-eq-prog (nf-ctor sp) D _ = ⊥-elim (ctor-no-⇒ sp D)
nf-eq-prog (nf-dty sp) D _ = ⊥-elim (dty-no-⇒ sp D)
nf-eq-prog nf-rfl _ _ = inj₂ (_ , ιrfl)
nf-eq-prog nf-ze ⇒-ze c with ≈-shape h-nat h-idt c
... | ()
nf-eq-prog nf-su (⇒-su _) c with ≈-shape h-nat h-idt c
... | ()
nf-eq-prog nf-one ⇒-one c with ≈-shape h-unit h-idt c
... | ()
nf-eq-prog nf-lam (⇒-lam _ _ _ _) c with ≈-shape h-pi h-idt c
... | ()
nf-eq-prog nf-typ () _
nf-eq-prog nf-pi () _
nf-eq-prog nf-nat () _
nf-eq-prog nf-unit () _
nf-eq-prog nf-empty () _
nf-eq-prog nf-idt () _
nf-eq-prog nf-prod () _
nf-eq-prog nf-pair (⇒-pair _ _ _) c with ≈-shape h-prod h-idt c
... | ()
nf-eq-prog nf-nu ()
nf-eq-prog nf-unf (⇒-unf _ _ _ _ _) c with ≈-shape h-nu h-idt c
... | ()

nf-prod-prog : ∀ {e E A B t u} →
  Nf σ-empty evid e → σ-empty , ε ⊢[ evid ] e ⇒ E ⊣ u →
  σ-empty ⊢[ spec ] E ≈ prod A B → Prog (letp e t)
nf-prod-prog (nf-ne ne) D _ = ⊥-elim (ne-untyped-⇒ ne D)
nf-prod-prog (nf-ctor sp) D _ = ⊥-elim (ctor-no-⇒ sp D)
nf-prod-prog (nf-dty sp) D _ = ⊥-elim (dty-no-⇒ sp D)
nf-prod-prog nf-pair _ _ = inj₂ (_ , ι-letp)
nf-prod-prog nf-ze ⇒-ze c with ≈-shape h-nat h-prod c
... | ()
nf-prod-prog nf-su (⇒-su _) c with ≈-shape h-nat h-prod c
... | ()
nf-prod-prog nf-one ⇒-one c with ≈-shape h-unit h-prod c
... | ()
nf-prod-prog nf-lam (⇒-lam _ _ _ _) c with ≈-shape h-pi h-prod c
... | ()
nf-prod-prog nf-typ () _
nf-prod-prog nf-pi () _
nf-prod-prog nf-nat () _
nf-prod-prog nf-unit () _
nf-prod-prog nf-empty () _
nf-prod-prog nf-idt () _
nf-prod-prog nf-rfl () _
nf-prod-prog nf-prod () _
nf-prod-prog nf-nu ()
nf-prod-prog nf-unf (⇒-unf _ _ _ _ _) c with ≈-shape h-nu h-prod c
... | ()

progress-⇒ : ∀ {e B u} → σ-empty , ε ⊢[ evid ] e ⇒ B ⊣ u → Prog e
progress-⇐ : ∀ {e A u} → σ-empty , ε ⊢[ evid ] e ⇐ A ⊣ u → Prog e

progress-⇐ (⇐-conv D _) = progress-⇒ D
progress-⇐ (⇐-ctor _ _ lk _ _ _ _ _ _) = ⊥-elim (fail≢ok lk)
progress-⇐ (⇐-lam _ _ _ _ _ _) = inj₁ nf-lam
progress-⇐ (⇐-refl _ _ _) = inj₁ nf-rfl
progress-⇐ (⇐-pair _ _ _ _) = inj₁ nf-pair
progress-⇐ (⇐-letp De c _ _ _ _) with progress-⇒ De
... | inj₂ (_ , s) = inj₂ (_ , letp-e s)
... | inj₁ nf = nf-prod-prog nf De c
progress-⇐ (⇐-unf _ _ _ _ _ _ _ _) = inj₁ nf-unf
progress-⇐ (⇐-unfR _ _ _ _ _ _ _ _) = inj₁ nf-unf

progress-⇒ (⇒-var-evid {x = ()} _)
progress-⇒ ⇒-ze = inj₁ nf-ze
progress-⇒ (⇒-su D) = inj₁ nf-su
progress-⇒ ⇒-one = inj₁ nf-one
progress-⇒ (⇒-lam _ _ _ _) = inj₁ nf-lam
progress-⇒ (⇒-app-aff Df c _ _) with progress-⇒ Df
... | inj₂ (_ , s) = inj₂ (_ , app-f s)
... | inj₁ nf with nf-fun nf Df c
...   | is-lam = inj₂ (_ , β)
progress-⇒ (⇒-app-era Df c _) with progress-⇒ Df
... | inj₂ (_ , s) = inj₂ (_ , app-f s)
... | inj₁ nf with nf-fun nf Df c
...   | is-lam = inj₂ (_ , β)
progress-⇒ (⇒-app-reuse Df c _ _ _) with progress-⇒ Df
... | inj₂ (_ , s) = inj₂ (_ , app-f s)
... | inj₁ nf with nf-fun nf Df c
...   | is-lam = inj₂ (_ , β)
progress-⇒ (⇒-app-copy Df c _ _ _) with progress-⇒ Df
... | inj₂ (_ , s) = inj₂ (_ , app-f s)
... | inj₁ nf with nf-fun nf Df c
...   | is-lam = inj₂ (_ , β)
progress-⇒ (⇒-rwt Deq c _ _) with progress-⇒ Deq
... | inj₂ (_ , s) = inj₂ (_ , rwt-e s)
... | inj₁ nf = nf-eq-prog nf Deq c
progress-⇒ (⇒-mNat De _ _ _ _ _) with progress-⇐ De
... | inj₁ nf = nf-nat-prog nf De
... | inj₂ (_ , s) = inj₂ (_ , mNat-e s)
progress-⇒ (⇒-mEmp De _) with progress-⇐ De
... | inj₁ nf = ⊥-elim (Empty-nf nf De)
... | inj₂ (_ , s) = inj₂ (_ , mEmp-e s)
progress-⇒ (⇒-mUnit De _ _ _) with progress-⇐ De
... | inj₁ nf = nf-unit-prog nf De
... | inj₂ (_ , s) = inj₂ (_ , mUnit-e s)
progress-⇒ (⇒-mData _ _ lk _ _ _ _ _) = ⊥-elim (fail≢ok lk)
progress-⇒ (⇒-def lk _) = ⊥-elim (fail≢ok lk)
progress-⇒ (⇒-ann _ _) = inj₂ (_ , ann-e)
progress-⇒ (⇒-pair _ _ _) = inj₁ nf-pair
progress-⇒ (⇒-letp De c _ _ _ _ _) with progress-⇒ De
... | inj₂ (_ , s) = inj₂ (_ , letp-e s)
... | inj₁ nf = nf-prod-prog nf De c
progress-⇒ (⇒-unf _ _ _ _ _) = inj₁ nf-unf
progress-⇒ (⇒-ucons D c st) with progress-⇒ D
... | inj₂ (_ , s) = inj₂ (_ , ucons-e s)
... | inj₁ nf = ucons-canon nf D c st

------------------------------------------------------------------------
-- The same canonical-forms argument for the declarative judgment ⊨,
-- which is what preservation is proved for.
------------------------------------------------------------------------

ne-untyped⊨ : ∀ {m e A} → Ne σ-empty evid e → σ-empty , ε ⊨[ m ] e ∶ A → ⊥
ne-untyped⁰ : ∀ {m e A} → Ne σ-empty evid e → σ-empty , ε ⊨⁰[ m ] e ∶ A → ⊥

ne-untyped⊨ ne (conv D _) = ne-untyped⁰ ne D

ne-untyped⁰ ne (t-ctor sp _) = ne-Spine ne sp
ne-untyped⁰ ne-var (t-var {x = ()} _)
ne-untyped⁰ (ne-def _) (t-def () _)
ne-untyped⁰ (ne-app ne) (t-app-aff Df _) = ne-untyped⊨ ne Df
ne-untyped⁰ (ne-app ne) (t-app-era Df _) = ne-untyped⊨ ne Df
ne-untyped⁰ (ne-app ne) (t-app-reuse Df _ _) = ne-untyped⊨ ne Df
ne-untyped⁰ (ne-mNat ne) (t-mNat De _ _ _) = ne-untyped⊨ ne De
ne-untyped⁰ (ne-mUnit ne) (t-mUnit De _ _) = ne-untyped⊨ ne De
ne-untyped⁰ (ne-mEmp ne) (t-mEmp De _) = ne-untyped⊨ ne De
ne-untyped⁰ (ne-rwt ne) (t-rwt Deq _ _) = ne-untyped⊨ ne Deq
ne-untyped⁰ (ne-mData ne) (t-mData De _ _ _ _ _) = ne-untyped⊨ ne De
ne-untyped⁰ (ne-letp ne) (t-letp De _) = ne-untyped⊨ ne De
ne-untyped⁰ (ne-ucons ne) (t-ucons Ds _ _) = ne-untyped⊨ ne Ds
ne-untyped⁰ (ne-foreign ()) (t-nu _)
ne-untyped⁰ (ne-foreign ()) (t-unf _ _)
ne-untyped⁰ (ne-foreign ()) (t-unfG _ _ _ _ _)
ne-untyped⁰ (ne-foreign ()) (t-unfR _ _ _ _ _)
ne-untyped⁰ (ne-foreign ()) t-ze
ne-untyped⁰ (ne-foreign ()) (t-su _)
ne-untyped⁰ (ne-foreign ()) t-one
ne-untyped⁰ (ne-foreign ()) t-nat
ne-untyped⁰ (ne-foreign ()) t-unit
ne-untyped⁰ (ne-foreign ()) t-empty
ne-untyped⁰ (ne-foreign ()) (t-pi _ _)
ne-untyped⁰ (ne-foreign ()) (t-lam _ _ _ _)
ne-untyped⁰ (ne-foreign ()) (t-idt _ _ _)
ne-untyped⁰ (ne-foreign ()) (t-rfl _)
ne-untyped⁰ (ne-foreign ()) (t-ann _ _)
ne-untyped⁰ (ne-foreign ()) (t-prod _ _)
ne-untyped⁰ (ne-foreign ()) (t-pair _ _)

-- t-ctor is the one rule whose subject is a variable: the term must
-- then be a constructor spine.
Empty-nf⊨ : ∀ {e} → Nf σ-empty evid e → σ-empty , ε ⊨[ evid ] e ∶ empty → ⊥
Empty-nf⊨ (nf-ne ne) D = ne-untyped⊨ ne D
Empty-nf⊨ (nf-ctor sp) (conv D _) = ctor-no⊨ sp D
Empty-nf⊨ (nf-dty sp) (conv D _) = dty-no⊨ sp D
Empty-nf⊨ nf-typ (conv (t-ctor () _) _)
Empty-nf⊨ nf-pi (conv (t-ctor () _) _)
Empty-nf⊨ nf-lam (conv (t-lam _ _ _ _) c) with ≈-shape h-pi h-empty c
... | ()
Empty-nf⊨ nf-lam (conv (t-ctor () _) _)
Empty-nf⊨ nf-nat (conv (t-ctor () _) _)
Empty-nf⊨ nf-ze (conv t-ze c) with ≈-shape h-nat h-empty c
... | ()
Empty-nf⊨ nf-ze (conv (t-ctor () _) _)
Empty-nf⊨ nf-su (conv (t-su _) c) with ≈-shape h-nat h-empty c
... | ()
Empty-nf⊨ nf-su (conv (t-ctor () _) _)
Empty-nf⊨ nf-unit (conv (t-ctor () _) _)
Empty-nf⊨ nf-one (conv t-one c) with ≈-shape h-unit h-empty c
... | ()
Empty-nf⊨ nf-one (conv (t-ctor () _) _)
Empty-nf⊨ nf-empty (conv (t-ctor () _) _)
Empty-nf⊨ nf-idt (conv (t-ctor () _) _)
Empty-nf⊨ nf-rfl (conv (t-rfl _) c) with ≈-shape h-idt h-empty c
... | ()
Empty-nf⊨ nf-rfl (conv (t-ctor () _) _)
Empty-nf⊨ nf-prod (conv (t-ctor () _) _)
Empty-nf⊨ nf-pair (conv (t-pair _ _) c) with ≈-shape h-prod h-empty c
... | ()
Empty-nf⊨ nf-pair (conv (t-ctor () _) _)
Empty-nf⊨ nf-nu (conv (t-ctor () _) _)
Empty-nf⊨ nf-unf (conv (t-unf _ _) c) with ≈-shape h-nu h-empty c
... | ()
Empty-nf⊨ nf-unf (conv (t-unfG _ _ _ refl _) c) with ≈-shape h-nu h-empty c
... | ()
Empty-nf⊨ nf-unf (conv (t-unfR _ _ st _ _) c) =
  ⊥-elim (rigid-spine h-empty (λ ()) st (≈-sym c))
Empty-nf⊨ nf-unf (conv (t-ctor () _) _)

------------------------------------------------------------------------
-- Preservation, specialised. A corollary of Muro.Typing.pres.
------------------------------------------------------------------------

preservation : ∀ {e e′} →
  σ-empty , ε ⊨[ evid ] e ∶ empty →
  σ-empty ⊢[ evid ] e ⟶ e′ →
  σ-empty , ε ⊨[ evid ] e′ ∶ empty
preservation D s = pres WfSig-empty D s

------------------------------------------------------------------------
-- The remaining obligation, as a hypothesis. Not postulated.
------------------------------------------------------------------------

-- Normalisation: closed evidence at Empty reaches a normal form.
Normalising : Set
Normalising = ∀ {e u} →
  σ-empty , ε ⊢[ evid ] e ⇐ empty ⊣ u →
  ∃ λ v → (σ-empty ⊢[ evid ] e ⟶* v) × Nf σ-empty evid v

Empty-evid-from : Normalising →
  ∀ {e u} → σ-empty , ε ⊢[ evid ] e ⇐ empty ⊣ u → ⊥
Empty-evid-from norm D with norm D
... | v , r , nf = Empty-nf⊨ nf (pres* WfSig-empty (forget-⇐ D) r)

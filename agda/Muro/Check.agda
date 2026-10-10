------------------------------------------------------------------------
-- MuroTT bidirectional checker.
--
-- Decide: fuel-based Result, each clause commented with a ⊢ constructor.
-- The theorem-oriented inductive spec of the core fragment is
-- Muro.Judgement (conversion there is ≈, not this fuelled WHNF).
--
-- There is no promotion: spec ↛ evid, evid ↛ run, spec ↛ run.
-- Emit visibility (def vs defp) is an Elixir-only flag on run.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Check where

open import Data.Bool.Base
  using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base as List using (List; []; _∷_; length; take; drop)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_; _+_)
open import Data.Nat.Show using (show)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String; _++_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base as Vec using (Vec; []; _∷_; lookup; map)
open import Function.Base using (case_of_; _$_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Env public
open import Muro.Tag using (tmTag)
open import Muro.Spine using (unspine; ctorSpine; dtyArgs; defArgs)

------------------------------------------------------------------------
-- Recursion state: run and evid structural descent (not spec).
-- A recursive block (one definition, or a strongly connected component
-- of run/evid definitions) descends on one shared argument position
-- `pos`: the variable bound by the leading λ at that position is
-- `recOk`; a field of a match on a recOk or smaller variable is
-- `smaller` (structurally below argument pos). A call to any member of
-- the block must be the head of a maximal application spine whose
-- argument at `pos` is a smaller variable. checkDef tries each
-- non-erased position the whole block shares.
------------------------------------------------------------------------

record RecSt (n : ℕ) : Set where
  constructor recst
  field
    self    : Maybe ℕ        -- the definition being checked
    pos     : ℕ              -- the argument position the block descends on
    nextArg : Maybe ℕ        -- leading λs still to pass before that argument
    smaller : Vec Bool n
    recOk   : Vec Bool n
    -- Set on the step of an indexed ν (Always, ~). In evidence, a
    -- self-call there is the coinductive step and need not descend.
    coind   : Bool
    block   : List ℕ         -- indices of the recursive block, including self

extRec : ∀ {n} → RecSt n → Bool → Bool → RecSt (suc n)
extRec (recst sl p _ sm rok g blk) newSmall newOk =
  recst sl p nothing (newSmall ∷ sm) (newOk ∷ rok) g blk

-- A leading λ of a definition body binds argument `pos` when nextArg
-- is just 0; erased binders count as positions too.
lamRec : ∀ {n} → RecSt n → RecSt (suc n)
lamRec (recst sl p na sm rok g blk) = recst sl p (stepArg na) (false ∷ sm) (isArg na ∷ rok) g blk
  where
    isArg : Maybe ℕ → Bool
    isArg (just zero) = true
    isArg _           = false
    stepArg : Maybe ℕ → Maybe ℕ
    stepArg (just (suc k)) = just k
    stepArg _              = nothing

scrutOk : ∀ {n} → RecSt n → Tm n → Bool
scrutOk rs (var x) = lookup (RecSt.recOk rs) x ∨ lookup (RecSt.smaller rs) x
scrutOk _  _       = false

isSmallerVar : ∀ {n} → RecSt n → Tm n → Bool
isSmallerVar rs (var x) = lookup (RecSt.smaller rs) x
isSmallerVar _  _       = false

------------------------------------------------------------------------
-- Small helpers.
------------------------------------------------------------------------

eqFin : ∀ {n} → Fin n → Fin n → Bool
eqFin {suc _} zero    zero    = true
eqFin {suc _} (suc i) (suc j) = eqFin i j
eqFin {suc _} zero    (suc _) = false
eqFin {suc _} (suc _) zero    = false

apps : ∀ {n} → Tm n → Tm n × List (Tm n)
apps = unspine

nthQty : ∀ {n} → Tm n → ℕ → Result Qty
nthQty (pi q _ _) zero    = ok q
nthQty (pi _ _ B) (suc i) = nthQty B i
nthQty _          _       = fail "recursive-call spine longer than Π telescope"

------------------------------------------------------------------------
-- Weak-head normalisation (β, ι, δ, ann). Fuel is the clock: every
-- recursive call spends one unit, and running out is a failure of its
-- own (outOfFuel), never a silently unreduced term.
------------------------------------------------------------------------

outOfFuel : String
outOfFuel = "out of fuel (the checker gave up reducing; raise the fuel)"

mutual
  whnf : ∀ {n} → ℕ → Sig → Tm n → Result (Tm n)
  whnf zero    _ _ = fail outOfFuel
  whnf (suc k) σ (app f a) with whnf k σ f
  ... | fail e            = fail e
  ... | ok (lam _ _ t)    = whnf k σ (inst t a)
  ... | ok f′             = ok (app f′ a)
  whnf (suc k) σ (mNat e P z s) with whnf k σ e
  ... | fail m      = fail m
  ... | ok ze       = whnf k σ z
  ... | ok (su u)   = whnf k σ (inst s u)
  ... | ok e′       = ok (mNat e′ P z s)
  whnf (suc k) σ (mUnit e P u) with whnf k σ e
  ... | fail m   = fail m
  ... | ok one   = whnf k σ u
  ... | ok e′    = ok (mUnit e′ P u)
  whnf (suc k) σ (mEmp e P) = whnf k σ e >>= λ e′ → ok (mEmp e′ P)
  whnf (suc k) σ (mData e P bs) = whnf k σ e >>= λ e′ → dataWhnf k σ e′ P bs
  whnf (suc k) σ (def i) with lookupDef σ i
  ... | ok d    = whnf k σ (closed (Def.dbody d))
  ... | fail _  = ok (def i)
  whnf (suc k) σ (ann e _) = whnf k σ e
  whnf (suc k) σ (ucons e) = whnf k σ e >>= uconsWhnf k σ
  whnf (suc k) σ (letp e t) with whnf k σ e
  ... | fail m          = fail m
  ... | ok (pair a b)   = whnf k σ (inst₂ t a b)
  ... | ok e′           = ok (letp e′ t)
  whnf (suc _) _ t = ok t

  uconsWhnf : ∀ {n} → ℕ → Sig → Tm n → Result (Tm n)
  uconsWhnf k σ (unf s f) with whnf k σ (app f s)
  ... | fail m          = fail m
  ... | ok (pair h t)   = ok (pair h (unf t f))
  ... | ok _            = ok (ucons (unf s f))
  uconsWhnf _ _ e = ok (ucons e)

  dataWhnf : ∀ {n} → ℕ → Sig → Tm n → Tm (suc n) → List (Tm n) → Result (Tm n)
  dataWhnf k σ e P bs with ctorSpine e
  ... | just (_ , ci , args) =
    case lookupList bs ci of λ where
      (ok b)  → whnf k σ (appsFrom b args)
      (fail _) → ok (mData e P bs)
  ... | nothing = ok (mData e P bs)

-- Is a (spec) type Data: Nat, Unit, Empty, I64, F32, Tensor, or a data
-- type whose parameters are Data. Fuel also bounds the descent into the
-- parameters (a spec definition may be recursive: X : Type := D X).
mutual
  allData : ∀ {n} → ℕ → Sig → List (Tm n) → Result Bool
  allData _ _ []       = ok true
  allData k σ (a ∷ as) = isData k σ a >>= λ b → if b then allData k σ as else ok false

  isData : ∀ {n} → ℕ → Sig → Tm n → Result Bool
  isData zero    _ _ = fail outOfFuel
  isData (suc k) σ t = whnf (suc k) σ t >>= λ t′ → isDataN k σ (apps t′)

  isDataN : ∀ {n} → ℕ → Sig → Tm n × List (Tm n) → Result Bool
  isDataN k σ (nat , [])        = ok true
  isDataN k σ (unit , [])       = ok true
  isDataN k σ (empty , [])      = ok true
  isDataN k σ (i64 , [])        = ok true
  isDataN k σ (f32ty , [])      = ok true
  isDataN k σ (tensor _ _ , []) = ok true
  isDataN k σ (dty i , as)      = dataParamsData k σ i as
  isDataN k σ (prod A B , [])   = isData k σ A >>= λ b → if b then isData k σ B else ok false
  isDataN k σ _                 = ok false

  dataParamsData : ∀ {n} → ℕ → Sig → ℕ → List (Tm n) → Result Bool
  dataParamsData k σ i as with lookupData σ i
  ... | fail _ = ok false
  ... | ok d   = allData k σ (take (nparams d) as)

-- Is a type copyable (Data.IsCopy): Data, a Π, or a product of copyable
-- types. A + binder asks this; an argument at a + position that is
-- copyable and not Data has its uses scaled (Env.scaleω).
data CopyView {n} : Tm n → Set where
  cv-pi    : ∀ {q A B} → CopyView (pi q A B)
  cv-prod  : ∀ {A B} → CopyView (prod A B)
  cv-other : ∀ {t} → CopyView t

copyView : ∀ {n} (t : Tm n) → CopyView t
copyView (pi q A B) = cv-pi
copyView (prod A B) = cv-prod
copyView t          = cv-other

mutual
  isCopy : ∀ {n} → ℕ → Sig → Tm n → Result Bool
  isCopy zero    _ _ = fail outOfFuel
  isCopy (suc k) σ t = whnf (suc k) σ t >>= λ t′ → isCopyN k σ t′

  isCopyN : ∀ {n} → ℕ → Sig → Tm n → Result Bool
  isCopyN k σ t with copyView t
  ... | cv-pi              = ok true
  ... | cv-prod {A} {B}    = isCopy k σ A >>= λ b → if b then isCopy k σ B else ok false
  ... | cv-other           = isDataN k σ (apps t)

notCopy : String
notCopy = "+ requires a copyable type: Data, a pair of them, or a function"

-- Shape of a run type: Nat, Unit, Empty, I64, F32, Tensor, a data type,
-- a Π whose codomain is one, a product of two, ν F. Under ν the body is
-- read as it is, the bound variable counting as a run type: substituting
-- Unit for it (as the older definition did) gives the same answer, since
-- runTy accepts every variable and every leaf alike.
runTy : ∀ {n} → Tm n → Bool
runTy (var _)        = true
runTy nat            = true
runTy unit           = true
runTy empty          = true
runTy i64            = true
runTy f32ty          = true
runTy (tensor _ _)   = true
runTy (pi _ _ B)     = runTy B
runTy (nu F)         = runTy F
runTy (prod A B)     = runTy A ∧ runTy B
runTy (dty _)        = true
runTy (app f _)      = runTy f
runTy _              = false

isRunType : ∀ {n} → ℕ → Sig → Tm n → Result Bool
isRunType k σ t = runTy <$> whnf k σ t

------------------------------------------------------------------------
-- Conversion on weak-head normal forms.
-- Syntactic equality is tried first so recursive defs are not unfolded
-- just to compare a call with itself (otherwise plus n m ≁ plus n m loops).
------------------------------------------------------------------------

mutual
  synEqList : ∀ {n} → List (Tm n) → List (Tm n) → Bool
  synEqList []       []       = true
  synEqList (x ∷ xs) (y ∷ ys) = synEq x y ∧ synEqList xs ys
  synEqList _        _        = false

  -- Tags are compared first (Muro.Tag); synEqD only has to handle terms
  -- of the same shape.
  synEq : ∀ {n} → Tm n → Tm n → Bool
  synEq u v = (tmTag u ≡ᵇ tmTag v) ∧ synEqD u v

  synEqD : ∀ {n} → Tm n → Tm n → Bool
  synEqD (var i)        (var j)        = eqFin i j
  synEqD typ            typ            = true
  synEqD (pi q A B)     (pi q′ A′ B′)  = eqQty q q′ ∧ synEq A A′ ∧ synEq B B′
  synEqD (lam q A t)    (lam q′ A′ t′) = eqQty q q′ ∧ synEq A A′ ∧ synEq t t′
  synEqD (app f a)      (app g b)      = synEq f g ∧ synEq a b
  synEqD nat            nat            = true
  synEqD ze             ze             = true
  synEqD (su a)         (su b)         = synEq a b
  synEqD unit           unit           = true
  synEqD one            one            = true
  synEqD empty          empty          = true
  synEqD (dty i)        (dty j)        = i ≡ᵇ j
  synEqD (ctor i j)     (ctor i′ j′)   = (i ≡ᵇ i′) ∧ (j ≡ᵇ j′)
  synEqD (mData e P bs) (mData e′ P′ bs′) =
    synEq e e′ ∧ synEq P P′ ∧ synEqList bs bs′
  synEqD (mNat e P z s) (mNat e′ P′ z′ s′) =
    synEq e e′ ∧ synEq P P′ ∧ synEq z z′ ∧ synEq s s′
  synEqD (mEmp e P)     (mEmp e′ P′)   = synEq e e′ ∧ synEq P P′
  synEqD (mUnit e P u)  (mUnit e′ P′ u′) = synEq e e′ ∧ synEq P P′ ∧ synEq u u′
  synEqD (idt A a b)    (idt A′ a′ b′) = synEq A A′ ∧ synEq a a′ ∧ synEq b b′
  synEqD rfl            rfl            = true
  synEqD (rwt e P t)    (rwt e′ P′ t′) = synEq e e′ ∧ synEq P P′ ∧ synEq t t′
  synEqD (def i)        (def j)        = i ≡ᵇ j
  synEqD (ann e A)      (ann e′ A′)    = synEq e e′ ∧ synEq A A′
  synEqD (prod A B)     (prod A′ B′)   = synEq A A′ ∧ synEq B B′
  synEqD (pair a b)     (pair a′ b′)   = synEq a a′ ∧ synEq b b′
  synEqD (letp e t)     (letp e′ t′)   = synEq e e′ ∧ synEq t t′
  synEqD (nu F)         (nu F′)        = synEq F F′
  synEqD (unf s f)      (unf s′ f′)    = synEq s s′ ∧ synEq f f′
  synEqD (ucons s)      (ucons s′)     = synEq s s′
  synEqD i64            i64            = true
  synEqD f32ty          f32ty          = true
  synEqD (tensor d s)   (tensor d′ s′) = synEq d d′ ∧ synEq s s′
  synEqD (addi x y)     (addi x′ y′)   = synEq x x′ ∧ synEq y y′
  synEqD (muli x y)     (muli x′ y′)   = synEq x x′ ∧ synEq y y′
  synEqD (addt t u)     (addt t′ u′)   = synEq t t′ ∧ synEq u u′
  synEqD (toi64 t)      (toi64 t′)     = synEq t t′
  synEqD (packi x y)    (packi x′ y′)  = synEq x x′ ∧ synEq y y′
  synEqD _              _              = false

ctorHead : ∀ {n} → Tm n → Bool
ctorHead t with proj₁ (apps t)
... | ze       = true
... | su _     = true
... | one      = true
... | ctor _ _ = true
... | _        = false

mutual
  convArgs : ∀ {n} → ℕ → Sig → List (Tm n) → List (Tm n) → Result ⊤
  convArgs k σ []       []       = ok tt
  convArgs k σ (a ∷ as) (b ∷ bs) = conv k σ a b >> convArgs k σ as bs
  convArgs _ _ _        _        = fail "conv: spine length mismatch"

  conv : ∀ {n} → ℕ → Sig → Tm n → Tm n → Result ⊤
  conv zero    _ _ _ = fail outOfFuel
  conv (suc k) σ u v =
    if synEq u v then ok tt
    else convStuck k σ u v (defArgs u) (defArgs v)

  -- Two applications of the same def to arguments that are not
  -- constructor-headed are compared argumentwise before unfolding
  -- (otherwise a recursive def is unfolded just to compare a call with
  -- itself).
  convStuck : ∀ {n} → ℕ → Sig → Tm n → Tm n
    → Maybe (ℕ × Tm n × List (Tm n)) → Maybe (ℕ × Tm n × List (Tm n)) → Result ⊤
  convStuck k σ u v (just (i , a , as)) (just (j , b , bs)) =
    if (i ≡ᵇ j) ∧ not (ctorHead a) ∧ not (ctorHead b)
    then (conv k σ a b >> convArgs k σ as bs)
    else convWhnf k σ u v
  convStuck k σ u v _ _ = convWhnf k σ u v

  convWhnf : ∀ {n} → ℕ → Sig → Tm n → Tm n → Result ⊤
  convWhnf k σ u v = whnf k σ u >>= λ u′ → whnf k σ v >>= λ v′ → convN k σ u′ v′

  -- Tags are compared first (Muro.Tag); convND only has to handle terms
  -- of the same shape.
  convN : ∀ {n} → ℕ → Sig → Tm n → Tm n → Result ⊤
  convN k σ u v =
    if tmTag u ≡ᵇ tmTag v then convND k σ u v
    else fail ("cannot convert " ++ showTm u ++ " ≁ " ++ showTm v)

  convND : ∀ {n} → ℕ → Sig → Tm n → Tm n → Result ⊤
  convND k σ typ           typ           = ok tt
  convND k σ nat           nat           = ok tt
  convND k σ unit          unit          = ok tt
  convND k σ empty         empty         = ok tt
  convND k σ (dty i)       (dty j)       = guard "data index mismatch" (i ≡ᵇ j)
  convND k σ (ctor i j)    (ctor i′ j′)  =
    guard "constructor mismatch" ((i ≡ᵇ i′) ∧ (j ≡ᵇ j′))
  convND k σ (mData e P bs) (mData e′ P′ bs′) =
    conv k σ e e′ >> conv k σ P P′ >> convArgs k σ bs bs′
  convND k σ ze            ze            = ok tt
  convND k σ one           one           = ok tt
  convND k σ rfl           rfl           = ok tt
  convND k σ (su a)        (su b)        = conv k σ a b
  convND k σ (var i)       (var j)       = guard ("var " ++ showTm (var i) ++ " ≠ " ++ showTm (var j)) (eqFin i j)
  convND k σ (def i)       (def j)       = guard ("def " ++ showDef i ++ " ≠ " ++ showDef j) (i ≡ᵇ j)
  convND k σ (pi q A B)    (pi q′ A′ B′) =
    guard "Π quantity mismatch" (eqQty q q′) >> conv k σ A A′ >> conv k σ B B′
  convND k σ (lam q A t)   (lam q′ A′ t′) =
    guard "λ quantity mismatch" (eqQty q q′) >> conv k σ A A′ >> conv k σ t t′
  convND k σ (app f a)     (app g b)     = conv k σ f g >> conv k σ a b
  convND k σ (idt A a b)   (idt A′ a′ b′) = conv k σ A A′ >> conv k σ a a′ >> conv k σ b b′
  convND k σ (mNat e P z s) (mNat e′ P′ z′ s′) =
    conv k σ e e′ >> conv k σ P P′ >> conv k σ z z′ >> conv k σ s s′
  convND k σ (mEmp e P)    (mEmp e′ P′)  = conv k σ e e′ >> conv k σ P P′
  convND k σ (mUnit e P u) (mUnit e′ P′ u′) =
    conv k σ e e′ >> conv k σ P P′ >> conv k σ u u′
  convND k σ (rwt e P t)   (rwt e′ P′ t′) =
    conv k σ e e′ >> conv k σ P P′ >> conv k σ t t′
  convND k σ (ann e A)     (ann e′ A′)   = conv k σ e e′ >> conv k σ A A′
  convND k σ (prod A B)    (prod A′ B′)  = conv k σ A A′ >> conv k σ B B′
  convND k σ (pair a b)    (pair a′ b′)  = conv k σ a a′ >> conv k σ b b′
  convND k σ (letp e t)    (letp e′ t′)  = conv k σ e e′ >> conv k σ t t′
  convND k σ (nu F)        (nu F′)       = conv k σ F F′
  convND k σ (unf s f)     (unf s′ f′)   = conv k σ s s′ >> conv k σ f f′
  convND k σ (ucons s)     (ucons s′)    = conv k σ s s′
  convND k σ i64           i64           = ok tt
  convND k σ f32ty         f32ty         = ok tt
  convND k σ (tensor d s)  (tensor d′ s′) = conv k σ d d′ >> conv k σ s s′
  convND k σ (addi x y)    (addi x′ y′)  = conv k σ x x′ >> conv k σ y y′
  convND k σ (muli x y)    (muli x′ y′)  = conv k σ x x′ >> conv k σ y y′
  convND k σ (addt t u)    (addt t′ u′)  = conv k σ t t′ >> conv k σ u u′
  convND k σ (toi64 t)     (toi64 t′)    = conv k σ t t′
  convND k σ (packi x y)   (packi x′ y′) = conv k σ x x′ >> conv k σ y y′
  convND _ _ u            v             =
    fail ("cannot convert " ++ showTm u ++ " ≁ " ++ showTm v)

------------------------------------------------------------------------
-- Spec: conversion as an inductive relation (source of truth for ≡).
------------------------------------------------------------------------

data _≈[_]_ {n} : Tm n → Sig → Tm n → Set where
  ≈-refl  : ∀ {σ t} → t ≈[ σ ] t
  ≈-sym   : ∀ {σ u v} → u ≈[ σ ] v → v ≈[ σ ] u
  ≈-trans : ∀ {σ u v w} → u ≈[ σ ] v → v ≈[ σ ] w → u ≈[ σ ] w
  ≈-β     : ∀ {σ q A t u} → app (lam q A t) u ≈[ σ ] inst t u
  ≈-ιz    : ∀ {σ P z s} → mNat ze P z s ≈[ σ ] z
  ≈-ιs    : ∀ {σ u P z s} → mNat (su u) P z s ≈[ σ ] inst s u
  ≈-ιtt   : ∀ {σ P u} → mUnit one P u ≈[ σ ] u
  ≈-δ     : ∀ {σ i d} → lookupDef σ i ≡ ok d → def i ≈[ σ ] closed (Def.dbody d)
  ≈-ann   : ∀ {σ e A} → ann e A ≈[ σ ] e
  ≈-cong-app : ∀ {σ f f′ a a′} → f ≈[ σ ] f′ → a ≈[ σ ] a′ → app f a ≈[ σ ] app f′ a′
  ≈-cong-su  : ∀ {σ a a′} → a ≈[ σ ] a′ → su a ≈[ σ ] su a′
  ≈-cong-pi  : ∀ {σ q A A′ B B′} → A ≈[ σ ] A′ → B ≈[ σ ] B′ → pi q A B ≈[ σ ] pi q A′ B′
  ≈-cong-idt : ∀ {σ A A′ a a′ b b′} → A ≈[ σ ] A′ → a ≈[ σ ] a′ → b ≈[ σ ] b′ →
               idt A a b ≈[ σ ] idt A′ a′ b′
  ≈-ιletp : ∀ {σ a b t} → letp (pair a b) t ≈[ σ ] inst₂ t a b
  ≈-ιuncons : ∀ {σ s f h t} →
              app f s ≈[ σ ] pair h t →
              ucons (unf s f) ≈[ σ ] pair h (unf t f)
  ≈-ιdata  : ∀ {σ di ci args P bs b} →
             lookupList bs ci ≡ ok b →
             mData (appsFrom (ctor di ci) args) P bs ≈[ σ ] appsFrom b args

------------------------------------------------------------------------
-- Spec: bidirectional judgments.
-- Elixir Muro.Check clauses are commented with these constructor names.
------------------------------------------------------------------------

infix 3 _,_⊢[_]_⇒_ _,_⊢[_]_⇐_ _,_⊢_wf

data _,_⊢[_]_⇒_ (σ : Sig) {n} (Γ : Ctx n) : Mode → Tm n → Tm n → Set
data _,_⊢[_]_⇐_ (σ : Sig) {n} (Γ : Ctx n) : Mode → Tm n → Tm n → Set
data _,_⊢_wf    (σ : Sig) {n} (Γ : Ctx n) : Tm n → Set

data _,_⊢_wf σ Γ where
  type-Type : σ , Γ ⊢ typ wf                          -- Type is a sort, not Type : Type
  type-pi   : ∀ {q A B}                               -- kinds: Π (x : A) → K, not small
    → σ , Γ ⊢ A wf
    → σ , ext Γ q A ⊢ B wf
    → σ , Γ ⊢ pi q A B wf
  type-el   : ∀ {A} → σ , Γ ⊢[ spec ] A ⇒ typ → σ , Γ ⊢ A wf

data _,_⊢[_]_⇒_ σ Γ where
  ⇒-var-run : ∀ {x}
    → (qtyOf Γ x ≡ erased → ⊥)
    → σ , Γ ⊢[ run ] var x ⇒ typOf Γ x

  ⇒-var-evid : ∀ {x}
    → (qtyOf Γ x ≡ erased → ⊥)
    → σ , Γ ⊢[ evid ] var x ⇒ typOf Γ x

  ⇒-var-spec : ∀ {x}
    → σ , Γ ⊢[ spec ] var x ⇒ typOf Γ x

  ⇒-ze : ∀ {m} → σ , Γ ⊢[ m ] ze ⇒ nat
  ⇒-su : ∀ {m t} → σ , Γ ⊢[ m ] t ⇐ nat → σ , Γ ⊢[ m ] su t ⇒ nat
  ⇒-tt : ∀ {m} → σ , Γ ⊢[ m ] one ⇒ unit

  ⇒-nat   : σ , Γ ⊢[ spec ] nat   ⇒ typ
  ⇒-unit  : σ , Γ ⊢[ spec ] unit  ⇒ typ
  ⇒-empty : σ , Γ ⊢[ spec ] empty ⇒ typ

  ⇒-pi : ∀ {q A B}                                    -- codomain small
    → σ , Γ ⊢ A wf
    → σ , ext Γ q A ⊢[ spec ] B ⇒ typ
    → σ , Γ ⊢[ spec ] pi q A B ⇒ typ

  ⇒-lam : ∀ {m q A t B}
    → σ , Γ ⊢ A wf
    → σ , ext Γ q A ⊢[ m ] t ⇒ B
    → σ , Γ ⊢[ m ] lam q A t ⇒ pi q A B

  ⇒-app-aff : ∀ {m A B f a}
    → σ , Γ ⊢[ m ] f ⇒ pi affine A B
    → σ , Γ ⊢[ m ] a ⇐ A
    → σ , Γ ⊢[ m ] app f a ⇒ inst B a

  ⇒-app-era : ∀ {m A B f a}
    → σ , Γ ⊢[ m ] f ⇒ pi erased A B
    → σ , Γ ⊢[ spec ] a ⇐ A
    → σ , Γ ⊢[ m ] app f a ⇒ inst B a

  ⇒-app-reuse : ∀ {m A B f a}
    → σ , Γ ⊢[ m ] f ⇒ pi reuse A B
    → σ , Γ ⊢[ m ] a ⇐ A
    → σ , Γ ⊢[ m ] app f a ⇒ inst B a

  -- Kernel identity is refused when A WHNFs to F32 or Tensor F32 S
  -- (see floatIdForbidden in the decision procedure).
  ⇒-idt : ∀ {A a b}                                   -- A may be a kind; see Judgement
    → σ , Γ ⊢ A wf
    → σ , Γ ⊢[ spec ] a ⇐ A
    → σ , Γ ⊢[ spec ] b ⇐ A
    → σ , Γ ⊢[ spec ] idt A a b ⇒ typ

  ⇒-rwt : ∀ {m A l r eq P t}
    → σ , Γ ⊢[ rwtMode m ] eq ⇒ idt A l r
    → σ , ext Γ affine A ⊢ P wf
    → σ , Γ ⊢[ m ] t ⇐ inst P r
    → σ , Γ ⊢[ m ] rwt eq P t ⇒ inst P l

  ⇒-dty : ∀ {i d}
    → lookupData σ i ≡ ok d
    → σ , Γ ⊢[ spec ] dty i ⇒ dtyType (DataDecl.pqtys d) (DataDecl.idxs d)

  ⇒-mData : ∀ {m di params idxs e P bs d}
    → lookupData σ di ≡ ok d
    → σ , Γ ⊢[ m ] e ⇐ appsFrom (dty di) (List._++_ params idxs)
    → σ , Γ ⊢[ m ] mData e P bs ⇒ motApp P idxs e

  ⇒-mNat : ∀ {m e P z s}
    → σ , Γ ⊢[ m ] e ⇐ nat
    → σ , ext Γ affine nat ⊢ P wf
    → σ , Γ ⊢[ m ] z ⇐ inst P ze
    → σ , ext Γ affine nat ⊢[ m ] s ⇐ sub (λ { zero → su (var zero) ; (suc i) → var (suc i) }) P
    → σ , Γ ⊢[ m ] mNat e P z s ⇒ inst P e

  ⇒-mEmp : ∀ {m e P}
    → σ , Γ ⊢[ m ] e ⇐ empty
    → σ , ext Γ affine empty ⊢ P wf
    → σ , Γ ⊢[ m ] mEmp e P ⇒ inst P e

  ⇒-mUnit : ∀ {m e P u}
    → σ , Γ ⊢[ m ] e ⇐ unit
    → σ , ext Γ affine unit ⊢ P wf
    → σ , Γ ⊢[ m ] u ⇐ inst P one
    → σ , Γ ⊢[ m ] mUnit e P u ⇒ inst P e

  ⇒-def : ∀ {m i d}
    → lookupDef σ i ≡ ok d
    → σ , Γ ⊢[ m ] def i ⇒ closed (Def.dtype d)

  ⇒-ann : ∀ {m e A}
    → σ , Γ ⊢ A wf
    → σ , Γ ⊢[ m ] e ⇐ A
    → σ , Γ ⊢[ m ] ann e A ⇒ A

  ⇒-prod : ∀ {A B}                                    -- components small
    → σ , Γ ⊢[ spec ] A ⇒ typ
    → σ , Γ ⊢[ spec ] B ⇒ typ
    → σ , Γ ⊢[ spec ] prod A B ⇒ typ

  ⇒-pair : ∀ {m A B a b}
    → σ , Γ ⊢[ m ] a ⇐ A
    → σ , Γ ⊢[ m ] b ⇐ B
    → σ , Γ ⊢[ m ] pair a b ⇒ prod A B

  -- let in inference mode: the body's type must not mention the two
  -- components (strengthen₂ succeeds).
  ⇒-letp : ∀ {m A B e t T C}
    → σ , Γ ⊢[ m ] e ⇒ prod A B
    → σ , ext (ext Γ affine A) affine (wk B) ⊢[ m ] t ⇒ T
    → strengthen₂ T ≡ ok C
    → σ , Γ ⊢[ m ] letp e t ⇒ C

  ⇒-nu : ∀ {F K}                                   -- body small
    → σ , ext Γ affine K ⊢[ spec ] F ⇒ wk K
    → σ , Γ ⊢[ spec ] nu F ⇒ K

  ⇒-unf : ∀ {m S A seed f}
    → σ , Γ ⊢[ m ] seed ⇐ S
    → σ , Γ ⊢[ m ] f ⇐ pi affine S (prod (wk A) (wk S))
    → σ , Γ ⊢[ m ] unf seed f ⇒ nu (prod (wk A) (var zero))

  ⇒-ucons : ∀ {m F s}
    → σ , Γ ⊢[ m ] s ⇐ nu F
    → σ , Γ ⊢[ m ] ucons s ⇒ inst F (nu F)

  ⇒-i64 : σ , Γ ⊢[ spec ] i64 ⇒ typ
  ⇒-f32ty : σ , Γ ⊢[ spec ] f32ty ⇒ typ

  ⇒-tensor : ∀ {D S}
    → σ , Γ ⊢ D wf
    → σ , Γ ⊢[ spec ] S ⇐ i64
    → σ , Γ ⊢[ spec ] tensor D S ⇒ typ

  ⇒-addi : ∀ {m x y}
    → σ , Γ ⊢[ m ] x ⇐ i64
    → σ , Γ ⊢[ m ] y ⇐ i64
    → σ , Γ ⊢[ m ] addi x y ⇒ i64

  ⇒-muli : ∀ {m x y}
    → σ , Γ ⊢[ m ] x ⇐ i64
    → σ , Γ ⊢[ m ] y ⇐ i64
    → σ , Γ ⊢[ m ] muli x y ⇒ i64

  ⇒-addt : ∀ {m D S t u}
    → σ , Γ ⊢[ m ] t ⇐ tensor D S
    → σ , Γ ⊢[ m ] u ⇐ tensor D S
    → σ , Γ ⊢[ m ] addt t u ⇒ tensor D S

  ⇒-toi64 : ∀ {m n}
    → σ , Γ ⊢[ m ] n ⇐ nat
    → σ , Γ ⊢[ m ] toi64 n ⇒ i64

  ⇒-packi : ∀ {m x y}
    → σ , Γ ⊢[ m ] x ⇐ i64
    → σ , Γ ⊢[ m ] y ⇐ i64
    → σ , Γ ⊢[ m ] packi x y ⇒ tensor i64 (toi64 (su (su ze)))

data _,_⊢[_]_⇐_ σ Γ where
  ⇐-conv : ∀ {m e A B}
    → σ , Γ ⊢[ m ] e ⇒ B
    → B ≈[ σ ] A
    → σ , Γ ⊢[ m ] e ⇐ A

  ⇐-lam : ∀ {m q A A′ t B}
    → σ , Γ ⊢ A wf
    → A ≈[ σ ] A′
    → σ , ext Γ q A′ ⊢[ m ] t ⇐ B
    → σ , Γ ⊢[ m ] lam q A t ⇐ pi q A′ B

  ⇐-refl : ∀ {m A a b}
    → a ≈[ σ ] b
    → σ , Γ ⊢[ m ] rfl ⇐ idt A a b

  ⇐-ctor : ∀ {m di ci params args d}
    → lookupData σ di ≡ ok d
    → σ , Γ ⊢[ m ] appsFrom (ctor di ci) args ⇐ appsFrom (dty di) params

  ⇐-pair : ∀ {m A B a b}
    → σ , Γ ⊢[ m ] a ⇐ A
    → σ , Γ ⊢[ m ] b ⇐ B
    → σ , Γ ⊢[ m ] pair a b ⇐ prod A B

  -- let (a, b) = e in t: the tensor eliminator. Both components are
  -- bound affine (a at var 1, b at var 0); the body is checked against
  -- the expected type weakened past them. fst / snd are surface sugar:
  -- fst t = letp t (var 1), snd t = letp t (var 0).
  ⇐-letp : ∀ {m A B e t C}
    → σ , Γ ⊢[ m ] e ⇒ prod A B
    → σ , ext (ext Γ affine A) affine (wk B) ⊢[ m ] t ⇐ wk (wk C)
    → σ , Γ ⊢[ m ] letp e t ⇐ C

  -- Bare ν (Stream): the step is checked at F[Y := S].
  -- An applied family (Always, ~): the step is checked at
  -- (F[Y := ν F]) applied to the indices, so the recursive component
  -- is the predicate at the tail, not the seed.
  ⇐-unf : ∀ {m S F seed f}
    → σ , Γ ⊢[ m ] seed ⇐ S
    → σ , Γ ⊢[ m ] f ⇐ pi affine S (wk (inst F S))
    → σ , Γ ⊢[ m ] unf seed f ⇐ nu F

-- Intentionally absent: spec ⇒ evid, evid ⇒ run, spec ⇒ run.

------------------------------------------------------------------------
-- Decision procedure.
------------------------------------------------------------------------

viewPi : ∀ {n} → ℕ → Sig → Tm n → Result (Qty × Tm n × Tm (suc n))
viewPi k σ t with whnf k σ t
... | fail m          = fail m
... | ok (pi q A B)   = ok (q , A , B)
... | ok t′           = fail ("expected Π, got " ++ showTm t′)

viewId : ∀ {n} → ℕ → Sig → Tm n → Result (Tm n × Tm n × Tm n)
viewId k σ t with whnf k σ t
... | fail m          = fail m
... | ok (idt A a b)  = ok (A , a , b)
... | ok t′           = fail ("expected Id, got " ++ showTm t′)

-- Dtype of Tensor: I64 or F32 after WHNF.
isNxDtype : ∀ {n} → ℕ → Sig → Tm n → Result Bool
isNxDtype k σ t with whnf k σ t
... | fail m    = fail m
... | ok i64    = ok true
... | ok f32ty  = ok true
... | ok _      = ok false

isF32 : ∀ {n} → ℕ → Sig → Tm n → Result Bool
isF32 k σ t with whnf k σ t
... | fail m    = fail m
... | ok f32ty  = ok true
... | ok _      = ok false

-- Kernel ≡ is refused on F32 and on Tensor F32 S.
floatIdForbidden : ∀ {n} → ℕ → Sig → Tm n → Result Bool
floatIdForbidden k σ A with whnf k σ A
... | fail m            = fail m
... | ok f32ty          = ok true
... | ok (tensor d _)   = isF32 k σ d
... | ok _              = ok false

floatIdOk : ∀ {n} → ℕ → Sig → Tm n → Result ⊤
floatIdOk k σ A =
  floatIdForbidden k σ A >>= λ b →
  guard "kernel identity is not defined on F32" (not b)

i64two : ∀ {n} → Tm n
i64two = toi64 (su (su ze))

viewProd : ∀ {n} → ℕ → Sig → Tm n → Result (Tm n × Tm n)
viewProd k σ t with whnf k σ t
... | fail m          = fail m
... | ok (prod A B)   = ok (A , B)
... | ok t′           = fail ("expected ×, got " ++ showTm t′)

viewNu : ∀ {n} → ℕ → Sig → Tm n → Result (Tm (suc n))
viewNu k σ t with whnf k σ t
... | fail m      = fail m
... | ok (nu F)   = ok F
... | ok t′       = fail ("expected ν, got " ++ showTm t′)

splitData : ∀ {n} → Sig → ℕ → List (Tm n) → Result (ℕ × List (Tm n) × List (Tm n))
splitData σ i args =
  lookupData σ i >>= λ d →
  let np = nparams d
      ni = nidxs d
  in guard "data applied to the wrong number of arguments"
       (length args ≡ᵇ (np + ni)) >>
  ok (i , take np args , drop np args)

viewData : ∀ {n} → ℕ → Sig → Tm n → Result (ℕ × List (Tm n) × List (Tm n))
viewData k σ t with whnf k σ t
... | fail m = fail m
... | ok t′ with dtyArgs t′
...   | just (i , args) = splitData σ i args
...   | nothing         = fail ("expected data type, got " ++ showTm t′)

isDType : ∀ {n} → ℕ → Tm n → Bool
isDType i t with dtyArgs t
... | just (j , _) = i ≡ᵇ j
... | nothing      = false

elemℕ : ℕ → List ℕ → Bool
elemℕ _ []       = false
elemℕ i (j ∷ js) = (i ≡ᵇ j) ∨ elemℕ i js

mutual
  hasSelf : ∀ {n} → List ℕ → Tm n → Bool
  hasSelf blk (def i) = elemℕ i blk
  hasSelf s (app f a)      = hasSelf s f ∨ hasSelf s a
  hasSelf s (su t)         = hasSelf s t
  hasSelf s (pair a b)     = hasSelf s a ∨ hasSelf s b
  hasSelf s (letp e t)     = hasSelf s e ∨ hasSelf s t
  hasSelf s (unf u f)      = hasSelf s u ∨ hasSelf s f
  hasSelf s (ucons u)      = hasSelf s u
  hasSelf s (tensor d u)   = hasSelf s d ∨ hasSelf s u
  hasSelf s (addi x y)     = hasSelf s x ∨ hasSelf s y
  hasSelf s (muli x y)     = hasSelf s x ∨ hasSelf s y
  hasSelf s (addt t u)     = hasSelf s t ∨ hasSelf s u
  hasSelf s (toi64 t)      = hasSelf s t
  hasSelf s (packi x y)    = hasSelf s x ∨ hasSelf s y
  hasSelf s (lam _ A t)    = hasSelf s A ∨ hasSelf s t
  hasSelf s (pi _ A B)     = hasSelf s A ∨ hasSelf s B
  hasSelf s (prod A B)     = hasSelf s A ∨ hasSelf s B
  hasSelf s (nu F)         = hasSelf s F
  hasSelf s (dty _)        = false
  hasSelf s (ctor _ _)     = false
  hasSelf s (mData e P bs) = hasSelf s e ∨ hasSelf s P ∨ hasSelfList s bs
  hasSelf s (mNat e P z u) = hasSelf s e ∨ hasSelf s P ∨ hasSelf s z ∨ hasSelf s u
  hasSelf s (mEmp e P)     = hasSelf s e ∨ hasSelf s P
  hasSelf s (mUnit e P u)  = hasSelf s e ∨ hasSelf s P ∨ hasSelf s u
  hasSelf s (idt A a b)    = hasSelf s A ∨ hasSelf s a ∨ hasSelf s b
  hasSelf s (rwt e P t)    = hasSelf s e ∨ hasSelf s P ∨ hasSelf s t
  hasSelf s (ann e A)      = hasSelf s e ∨ hasSelf s A
  hasSelf _ _              = false

  hasSelfList : ∀ {n} → List ℕ → List (Tm n) → Bool
  hasSelfList _ []       = false
  hasSelfList s (t ∷ ts) = hasSelf s t ∨ hasSelfList s ts

-- On run/evid, unfold's λ-body must be a pair and the head must not
-- contain a self-call. spec skips the test.
checkUnfold : ∀ {n} → ℕ → Sig → Mode → RecSt n → Tm n → Result ⊤
checkUnfold _ _ spec _ _ = ok tt
checkUnfold k σ _ rs f = whnf k σ f >>= go
  where
    go : ∀ {n} → Tm n → Result ⊤
    go (lam _ _ t) = go t
    go (pair h _)  =
      if hasSelf (RecSt.block rs) h
      then fail "unguarded recursive call"
      else ok tt
    go _ = fail "unfold body must be a pair"

-- On run/evid, a definition whose type reduces to a ν (bare, or a
-- family applied to any number of indices) is an unfold, or it does not
-- mention its own block: a call into the block is productive only as
-- the tail of an unfold step, where checkUnfold guards it.
isNuHead : ∀ {n} → Tm n → Bool
isNuHead (nu _) = true
isNuHead _      = false

checkNu : ∀ {n} → ℕ → Sig → List ℕ → Mode → Tm n → Tm n → Result ⊤
checkNu _       _ _   spec _ _ = ok tt
checkNu zero    _ _   _    _ _ = fail outOfFuel
checkNu (suc k) σ blk m    T t = whnf (suc k) σ T >>= λ T′ → go T′ t
  where
    go : ∀ {n} → Tm n → Tm n → Result ⊤
    go (pi _ _ B) (lam _ _ u) = checkNu k σ blk m B u
    go _          (unf _ _)   = ok tt
    go T′         u           =
      if isNuHead (proj₁ (apps T′)) ∧ hasSelf blk u
      then fail "ν value calls its own block outside an unfold"
      else ok tt

mutual
  occurs : ∀ {n} → Fin n → Tm n → Bool
  occurs x (var y)        = eqFin x y
  occurs x (pi _ A B)     = occurs x A ∨ occurs (suc x) B
  occurs x (lam _ A t)    = occurs x A ∨ occurs (suc x) t
  occurs x (app f a)      = occurs x f ∨ occurs x a
  occurs x (su t)         = occurs x t
  occurs x (dty _)        = false
  occurs x (ctor _ _)     = false
  occurs x (mData e P bs) = occurs x e ∨ occurs (suc x) P ∨ occursList x bs
  occurs x (mNat e P z s) = occurs x e ∨ occurs (suc x) P ∨ occurs x z ∨ occurs (suc x) s
  occurs x (mEmp e P)     = occurs x e ∨ occurs (suc x) P
  occurs x (mUnit e P u)  = occurs x e ∨ occurs (suc x) P ∨ occurs x u
  occurs x (idt A a b)    = occurs x A ∨ occurs x a ∨ occurs x b
  occurs x (rwt e P t)    = occurs x e ∨ occurs (suc x) P ∨ occurs x t
  occurs x (ann e A)      = occurs x e ∨ occurs x A
  occurs x (prod A B)     = occurs x A ∨ occurs x B
  occurs x (pair a b)     = occurs x a ∨ occurs x b
  occurs x (letp e t)     = occurs x e ∨ occurs (suc (suc x)) t
  occurs x (nu F)         = occurs (suc x) F
  occurs x (unf s f)      = occurs x s ∨ occurs x f
  occurs x (ucons s)      = occurs x s
  occurs x (tensor d s)   = occurs x d ∨ occurs x s
  occurs x (addi a b)     = occurs x a ∨ occurs x b
  occurs x (muli a b)     = occurs x a ∨ occurs x b
  occurs x (addt t u)     = occurs x t ∨ occurs x u
  occurs x (toi64 t)      = occurs x t
  occurs x (packi a b)    = occurs x a ∨ occurs x b
  occurs _ _              = false

  occursList : ∀ {n} → Fin n → List (Tm n) → Bool
  occursList _ []       = false
  occursList x (t ∷ ts) = occurs x t ∨ occursList x ts

-- X is strictly positive: product ok; not in a Π-domain; an application
-- is positive when X is the head and does not occur in the arguments.
spos : ∀ {n} → Fin n → Tm n → Bool
-- An application of the recursive variable to arguments that do not
-- contain it is positive (Y (tail s)). A λ is positive when its domain
-- does not contain it.
argsPos : ∀ {n} → Fin n → List (Tm n) → Bool
argsPos _ []       = true
argsPos x (a ∷ as) = not (occurs x a) ∧ argsPos x as

sposSpine : ∀ {n} → Fin n → Tm n → Bool
sposSpine x t with unspine t
... | var y , args = if eqFin x y then argsPos x args else not (occurs x t)
... | _            = not (occurs x t)

spos x (var _)     = true
spos x (prod A B)  = spos x A ∧ spos x B
spos x (pi _ A B)  = not (occurs x A) ∧ spos (suc x) B
spos x (nu F)      = not (occurs (suc x) F)
spos x (lam _ A t) = not (occurs x A) ∧ spos (suc x) t
spos x (app f a)   = sposSpine x (app f a)
spos x t           = not (occurs x t)

strictPos : ∀ {n} → Tm (suc n) → Bool
strictPos F = spos zero F

mutual
  occursD : ∀ {n} → ℕ → Tm n → Bool
  occursD i (dty j)        = i ≡ᵇ j
  occursD i (app f a)      = occursD i f ∨ occursD i a
  occursD i (pi _ A B)     = occursD i A ∨ occursD i B
  occursD i (lam _ A t)    = occursD i A ∨ occursD i t
  occursD i (prod A B)     = occursD i A ∨ occursD i B
  occursD i (pair a b)     = occursD i a ∨ occursD i b
  occursD i (idt A a b)    = occursD i A ∨ occursD i a ∨ occursD i b
  occursD i (mNat e P z s) = occursD i e ∨ occursD i P ∨ occursD i z ∨ occursD i s
  occursD i (mData e P bs) = occursD i e ∨ occursD i P ∨ occursDList i bs
  occursD i (mEmp e P)     = occursD i e ∨ occursD i P
  occursD i (mUnit e P u)  = occursD i e ∨ occursD i P ∨ occursD i u
  occursD i (rwt e P t)    = occursD i e ∨ occursD i P ∨ occursD i t
  occursD i (ann e A)      = occursD i e ∨ occursD i A
  occursD i (nu F)         = occursD i F
  occursD i (unf s f)      = occursD i s ∨ occursD i f
  occursD i (ucons s)      = occursD i s
  occursD i (su t)         = occursD i t
  occursD i (letp e t)     = occursD i e ∨ occursD i t
  occursD i (tensor d s)   = occursD i d ∨ occursD i s
  occursD i (addi a b)     = occursD i a ∨ occursD i b
  occursD i (muli a b)     = occursD i a ∨ occursD i b
  occursD i (addt t u)     = occursD i t ∨ occursD i u
  occursD i (toi64 t)      = occursD i t
  occursD i (packi a b)    = occursD i a ∨ occursD i b
  occursD _ _              = false

  occursDList : ∀ {n} → ℕ → List (Tm n) → Bool
  occursDList _ []       = false
  occursDList i (t ∷ ts) = occursD i t ∨ occursDList i ts

instParams : ∀ {n} → ℕ → Sig → Tm n → List (Tm n) → Result (Tm n)
instParams k σ t [] = ok t
instParams k σ t (p ∷ ps) with whnf k σ t
... | fail m          = fail m
... | ok (pi _ _ B)   = instParams k σ (inst B p) ps
... | ok _            = fail "constructor type has too few parameter binders"

-- A field is strictly positive in data type i when, after unfolding,
-- i is absent, or i is the head of a spine whose arguments do not
-- contain i, or i occurs only to the right of a Π whose domain does
-- not contain i. A product is positive on both sides. i inside an
-- argument of i is refused (no nested inductives). Another data type
-- is not opaque: its parameters are instantiated and every field is
-- held to the same test, so i stored there and placed in a domain is
-- refused. A type already being unfolded is the inductive occurrence.
-- Fuel exhaustion is refusal. checkData sits outside ⊢; this restores
-- the invariant ⊢ relies on.
mutual
  absentD : ∀ {n} → ℕ → Sig → ℕ → List ℕ → Tm n → Bool
  absentD zero _ _ _ _ = false
  absentD (suc k) σ i seen t = absentWhnf k σ i seen (whnf (suc k) σ t)

  absentWhnf : ∀ {n} → ℕ → Sig → ℕ → List ℕ → Result (Tm n) → Bool
  absentWhnf k σ i seen (ok t)  = absentGo k σ i seen t
  absentWhnf _ _ _ _ (fail _) = false

  absentGo : ∀ {n} → ℕ → Sig → ℕ → List ℕ → Tm n → Bool
  absentGo k σ i seen (pi _ A B)     = absentD k σ i seen A ∧ absentD k σ i seen B
  absentGo k σ i seen (prod A B)     = absentD k σ i seen A ∧ absentD k σ i seen B
  absentGo k σ i seen (lam _ A t)    = absentD k σ i seen A ∧ absentD k σ i seen t
  absentGo k σ i seen (app f a)      = absentD k σ i seen f ∧ absentD k σ i seen a
  absentGo k σ i seen (pair a b)     = absentD k σ i seen a ∧ absentD k σ i seen b
  absentGo k σ i seen (idt A a b)    = absentD k σ i seen A ∧ absentD k σ i seen a ∧ absentD k σ i seen b
  absentGo k σ i seen (ann e A)      = absentD k σ i seen e ∧ absentD k σ i seen A
  absentGo k σ i seen (su t)         = absentD k σ i seen t
  absentGo k σ i seen (letp e t)     = absentD k σ i seen e ∧ absentD k σ i seen t
  absentGo k σ i seen (nu F)         = absentD k σ i seen F
  absentGo k σ i seen (unf s f)      = absentD k σ i seen s ∧ absentD k σ i seen f
  absentGo k σ i seen (ucons s)      = absentD k σ i seen s
  absentGo k σ i seen (mNat e P z s) = absentD k σ i seen e ∧ absentD k σ i seen P ∧ absentD k σ i seen z ∧ absentD k σ i seen s
  absentGo k σ i seen (mEmp e P)     = absentD k σ i seen e ∧ absentD k σ i seen P
  absentGo k σ i seen (mUnit e P u)  = absentD k σ i seen e ∧ absentD k σ i seen P ∧ absentD k σ i seen u
  absentGo k σ i seen (rwt e P t)    = absentD k σ i seen e ∧ absentD k σ i seen P ∧ absentD k σ i seen t
  absentGo k σ i seen (tensor d s)   = absentD k σ i seen d ∧ absentD k σ i seen s
  absentGo k σ i seen (addi a b)     = absentD k σ i seen a ∧ absentD k σ i seen b
  absentGo k σ i seen (muli a b)     = absentD k σ i seen a ∧ absentD k σ i seen b
  absentGo k σ i seen (addt t u)     = absentD k σ i seen t ∧ absentD k σ i seen u
  absentGo k σ i seen (toi64 t)      = absentD k σ i seen t
  absentGo k σ i seen (packi a b)    = absentD k σ i seen a ∧ absentD k σ i seen b
  absentGo k σ i seen (mData e P bs) = absentD k σ i seen e ∧ absentD k σ i seen P ∧ absentDList k σ i seen bs
  absentGo k σ i seen (dty j)        = absentData k σ i seen j
  absentGo _ _ _ _ _                 = true

  -- j already on the stack is an inductive occurrence, not a fresh copy of i.
  absentData : ℕ → Sig → ℕ → List ℕ → ℕ → Bool
  absentData zero    _ _ _    _ = false
  absentData (suc k) σ i seen j =
    if i ≡ᵇ j then false
    else if elemℕ j seen then true
    else absentDecl k σ i (j ∷ seen) j

  absentDecl : ℕ → Sig → ℕ → List ℕ → ℕ → Bool
  absentDecl k σ i seen j =
    case lookupData σ j of λ where
      (fail _) → false
      (ok d)   → absentCtors k σ i seen (nparams d) (DataDecl.ctors d)

  absentCtors : ℕ → Sig → ℕ → List ℕ → ℕ → List Ctor → Bool
  absentCtors _ _ _ _ _ []       = true
  absentCtors k σ i seen np (c ∷ cs) =
    absentTel k σ i seen np (Ctor.ctype c) ∧ absentCtors k σ i seen np cs

  absentTel : ∀ {n} → ℕ → Sig → ℕ → List ℕ → ℕ → Tm n → Bool
  absentTel zero    _ _ _ _ _ = false
  absentTel (suc k) σ i seen (suc c) (pi _ _ B) = absentTel k σ i seen c B
  absentTel (suc k) σ i seen zero (pi _ A B) =
    absentD k σ i seen A ∧ absentTel k σ i seen zero B
  absentTel _ _ _ _ _ _ = true

  absentDList : ∀ {n} → ℕ → Sig → ℕ → List ℕ → List (Tm n) → Bool
  absentDList _ _ _ _ []       = true
  absentDList k σ i seen (t ∷ ts) = absentD k σ i seen t ∧ absentDList k σ i seen ts

  allAbsent : ∀ {n} → ℕ → Sig → ℕ → List ℕ → List (Tm n) → Bool
  allAbsent _ _ _ _ []       = true
  allAbsent k σ i seen (a ∷ as) = absentD k σ i seen a ∧ allAbsent k σ i seen as

  posField : ∀ {n} → ℕ → Sig → ℕ → List ℕ → Tm n → Bool
  posField zero _ _ _ _ = false
  posField (suc k) σ i seen t = posWhnf k σ i seen (whnf (suc k) σ t)

  posWhnf : ∀ {n} → ℕ → Sig → ℕ → List ℕ → Result (Tm n) → Bool
  posWhnf _ _ _ _ (fail _)        = false
  posWhnf k σ i seen (ok (pi _ A B)) = absentD (suc k) σ i seen A ∧ posField k σ i seen B
  posWhnf k σ i seen (ok (prod A B)) = posField k σ i seen A ∧ posField k σ i seen B
  posWhnf k σ i seen (ok t)          = posSpine k σ i seen t (dtyArgs t)

  posSpine : ∀ {n} → ℕ → Sig → ℕ → List ℕ → Tm n → Maybe (ℕ × List (Tm n)) → Bool
  posSpine k σ i seen _ (just (j , args)) =
    if i ≡ᵇ j then allAbsent (suc k) σ i seen args
    else allAbsent (suc k) σ i seen args ∧ posData k σ i seen j args
  posSpine k σ i seen t nothing = absentGo k σ i seen t

  -- Parameters of j are instantiated with the spine. Each remaining
  -- field is strictly positive. j already on the stack is the inductive
  -- occurrence (Tree stored in Forest, Forest stored in Tree).
  posData : ∀ {n} → ℕ → Sig → ℕ → List ℕ → ℕ → List (Tm n) → Bool
  posData zero    _ _ _    _ _ = false
  posData (suc k) σ i seen j args =
    if elemℕ j seen then true
    else posDecl k σ i (j ∷ seen) j args

  posDecl : ∀ {n} → ℕ → Sig → ℕ → List ℕ → ℕ → List (Tm n) → Bool
  posDecl k σ i seen j args =
    case lookupData σ j of λ where
      (fail _) → false
      (ok d)   → posCtors k σ i seen (take (nparams d) args) (DataDecl.ctors d)

  posCtors : ∀ {n} → ℕ → Sig → ℕ → List ℕ → List (Tm n) → List Ctor → Bool
  posCtors _ _ _ _ _  []       = true
  posCtors k σ i seen ps (c ∷ cs) =
    posCtor k σ i seen ps (Ctor.ctype c) ∧ posCtors k σ i seen ps cs

  posCtor : ∀ {n} → ℕ → Sig → ℕ → List ℕ → List (Tm n) → Tm 0 → Bool
  posCtor k σ i seen ps ty =
    case instParams k σ (closed ty) ps of λ where
      (fail _) → false
      (ok t)   → posTel k σ i seen t

  posTel : ∀ {n} → ℕ → Sig → ℕ → List ℕ → Tm n → Bool
  posTel zero    _ _ _ _ = false
  posTel (suc k) σ i seen (pi _ A B) = posField k σ i seen A ∧ posTel k σ i seen B
  posTel _ _ _ _ _ = true

checkTelPos : ∀ {n} → ℕ → Sig → ℕ → ℕ → ℕ → Tm n → Result ⊤
checkTelPos k σ i np ni (pi _ A B) =
  guard "constructor is not strictly positive" (posField k σ i [] A) >>
  checkTelPos k σ i np ni B
checkTelPos k σ i np ni t =
  guard "constructor does not target the data type" (isDType i t) >>
  guard "constructor target has the wrong number of arguments"
    (length (proj₂ (apps t)) ≡ᵇ (np + ni))

-- Skip nparams Π-binders, then check the remaining telescope.
checkCtorRest : ∀ {n} → ℕ → Sig → ℕ → ℕ → ℕ → Tm n → Result ⊤
checkCtorRest k σ i np ni t = skip np t
  where
    skip : ∀ {n} → ℕ → Tm n → Result ⊤
    skip (suc c) (pi _ _ B) = skip c B
    skip (suc _) _          = fail "constructor type has too few parameter binders"
    skip zero    u          = checkTelPos k σ i np ni u

noDescent : String
noDescent = "recursive call does not descend on a smaller argument"

checkRecGo : ∀ {n} → RecSt n → Tm n → Result ⊤
checkRecGo rs t = go rs (apps t)
  where
    descend : ∀ {n} → RecSt n → List (Tm n) → Result ⊤
    descend rs args =
      case lookupList args (RecSt.pos rs) of λ where
        (ok a)   → if isSmallerVar rs a then ok tt else fail noDescent
        (fail _) → fail noDescent

    go : ∀ {n} → RecSt n → Tm n × List (Tm n) → Result ⊤
    go rs (def i , args) =
      if elemℕ i (RecSt.block rs) then descend rs args else ok tt
    go _ _ = ok tt

-- A maximal application spine headed by the definition being checked
-- (run and evid; spec is not checked): the argument at `pos` must be a
-- smaller variable. A shorter spine has no such argument. The Bool is
-- infer′'s: an inner application (the head of a larger spine) is not
-- the maximal spine and is not checked. An evidence self-call in the
-- step of an indexed ν is the coinductive step (`RecSt.coind`).
checkRec : ∀ {n} → Mode → Bool → RecSt n → Tm n → Result ⊤
checkRec spec _    _  _ = ok tt
checkRec _    true _  _ = ok tt
checkRec evid false rs t =
  if RecSt.coind rs then ok tt else checkRecGo rs t
checkRec _    false rs t = checkRecGo rs t

selfRefused : ∀ {n} → RecSt n → ℕ → Result ⊤
selfRefused rs i =
  if elemℕ i (RecSt.block rs)
  then fail "recursive definition must be applied to its arguments"
  else ok tt

-- The definition being checked may not occur unapplied in run or evid:
-- passed along, it could be applied to anything. The Bool is infer′'s:
-- at the head of a spine it is applied. Evidence under `RecSt.coind`
-- may name itself: that occurrence is the coinductive step.
selfApplied : ∀ {n} → Mode → Bool → RecSt n → ℕ → Result ⊤
selfApplied spec _    _  _ = ok tt
selfApplied _    true _  _ = ok tt
selfApplied evid false rs i =
  if RecSt.coind rs then ok tt else selfRefused rs i
selfApplied _    false rs i = selfRefused rs i

-- Index clash. Expected indices live at n; the constructor target may
-- mention ctor-argument variables (depth d). No unification: su is
-- inverted on both sides, a rigid mismatch of su against ze is a clash
-- (the constructor cannot produce these indices and its branch is
-- skipped), anything else says nothing. A constructor-argument variable
-- in the target is never forced: the branch binds it and is typed at
-- the constructor's own indices (Judgement.BrTy); a program that needs
-- the index equation states it in the motive and uses rewrite. Each
-- inversion of suc reduces both sides, so it spends a unit of fuel.
data NatView {n} : Tm n → Set where
  nv-su    : ∀ {t} → NatView (su t)
  nv-ze    : NatView ze
  nv-other : ∀ {t} → NatView t

natView : ∀ {n} (t : Tm n) → NatView t
natView (su t) = nv-su
natView ze     = nv-ze
natView t      = nv-other

mutual
  clashIdx : ∀ {n m} → ℕ → Sig → Tm n → Tm m → Result Bool
  clashIdx zero    _ _ _ = fail outOfFuel
  clashIdx (suc k) σ e t =
    whnf k σ e >>= λ e′ → whnf k σ t >>= λ t′ → clashIdxN k σ e′ t′

  clashIdxN : ∀ {n m} → ℕ → Sig → Tm n → Tm m → Result Bool
  clashIdxN k σ e′ t′ = clashIdxV k σ (natView e′) (natView t′)

  clashIdxV : ∀ {n m} → ℕ → Sig → {e′ : Tm n} {t′ : Tm m} → NatView e′ → NatView t′ → Result Bool
  clashIdxV k σ (nv-su {e″}) (nv-su {t″}) = clashIdx k σ e″ t″
  clashIdxV k σ nv-su nv-ze = ok true
  clashIdxV k σ nv-ze nv-su = ok true
  clashIdxV k σ _     _     = ok false

clashIdxs : ∀ {n m} → ℕ → Sig → List (Tm n) → List (Tm m) → Result Bool
clashIdxs _ _ []       []       = ok false
clashIdxs k σ (e ∷ es) (t ∷ ts) =
  clashIdx k σ e t >>= λ where
    true  → ok true
    false → clashIdxs k σ es ts
clashIdxs _ _ _ _ = fail "index telescope length mismatch"

-- Walk the constructor telescope to its target and compare the target's
-- indices (after the np parameters) with the expected ones.
clashes : ∀ {n m} → ℕ → Sig → ℕ → List (Tm n) → Tm m → Result Bool
clashes k σ np expected (pi _ _ B) = clashes k σ np expected B
clashes k σ np expected t =
  whnf k σ t >>= λ t′ →
  clashIdxs k σ expected (drop np (proj₂ (apps t′)))

-- The block is structurally recursive on the term being checked. Types
-- are never recursed on except by checkTy, which recurses on the type
-- as a term. A constructor spine is walked from its head
-- (inferCtorSpine), as an application is.

-- Drop de Bruijn index `at` (0 = nearest). Fails if that variable occurs.
skipAt : ∀ {n} → ℕ → Fin (suc n) → Result (Fin n)
skipAt zero    zero    = fail "ν kind mentions its binder"
skipAt zero    (suc j) = ok j
skipAt {suc n} (suc _) zero    = ok zero
skipAt {suc n} (suc k) (suc j) = suc <$> skipAt k j
skipAt {zero}  (suc _) _       = fail "ν kind mentions its binder"

setGuard : ∀ {n} → RecSt n → RecSt n
setGuard (recst sl p na sm rok _ blk) = recst sl p na sm rok true blk

-- Kind of a ν body. A product (Stream) has kind Type. A λ-telescope
-- of any length has the Π of its domains; the binder Y, `y` binders
-- out, does not occur in the kind.
nuKindAt : ∀ {n} → ℕ → Tm (suc n) → Result (Tm n)
nuKindAt y (lam q A t) =
  renM (skipAt y) A >>= λ A′ →
  nuKindAt (suc y) t >>= λ B →
  ok (pi q A′ B)
nuKindAt _ _ = ok typ

nuKind : ∀ {n} → Tm (suc n) → Result (Tm n)
nuKind = nuKindAt 0

applyFam : ∀ {n} → Tm n → List (Tm n) → Tm n
applyFam t []             = t
applyFam (lam _ _ b) (i ∷ is) = applyFam (inst b i) is
applyFam t (i ∷ is)     = applyFam (app t i) is

unfFam : ∀ {n} → Tm n → Tm (suc n) → List (Tm n) → Result (Tm n × Bool)
unfFam S F [] = ok (inst F S , false)
unfFam S (lam q A b) idxs =
  let F = lam q A b in
  ok (applyFam (inst F (nu F)) idxs , true)
unfFam _ _ _ = fail "expected a ν family"

unfSpine : ∀ {n} → Tm n → Tm n × List (Tm n) → Result (Tm n × Bool)
unfSpine S (nu F , idxs) = unfFam S F idxs
unfSpine _ (_ , _)       = fail "expected ν"

unfStepOf : ∀ {n} → Tm n → Tm n → Result (Tm n × Bool)
unfStepOf S (nu F) = ok (inst F S , false)
unfStepOf S t      = unfSpine S (unspine t)

-- Codomain of an unfold step, in the outer context, and whether the
-- expected type is an applied family (true) or a bare ν (false).
unfStep : ∀ {n} → ℕ → Sig → Tm n → Tm n → Result (Tm n × Bool)
unfStep k σ T S = whnf k σ T >>= unfStepOf S

mutual
  infer : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → Tm n → Result (Tm n × UseVec n)
  infer k σ rs Γ m t = infer′ k σ rs Γ t m false

  check : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → Tm n → Tm n → Result (UseVec n)
  check k σ rs Γ m e A = check′ k σ rs Γ m e A

  -- A type is Type, a kind Π (x : A) → K, or a small type (⇒ Type).
  -- Kinds are not small: Π (x : A) → Type is wf but has no type.
  -- Syntax-directed, as ⊢ wf: a kind is recognised by its shape, anything
  -- else must infer a type convertible to Type. (Reducing first would
  -- accept terms that merely reduce to Type or to a kind, such as
  -- (λ (x : Nat) → Type) 0, which have no derivation.)
  checkTy : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Tm n → Result ⊤
  checkTy k σ rs Γ typ = ok tt                               -- type-Type
  checkTy k σ rs Γ (pi q A₁ B) =                             -- type-pi
    checkTy k σ rs Γ A₁ >>
    checkTy k σ (extRec rs false false) (ext Γ q A₁) B
  checkTy k σ rs Γ A = infer′ k σ rs Γ A spec false >>= λ (T , _) → conv k σ T typ   -- type-el

  -- The term comes before the mode so that the case tree splits on the
  -- term first: infer′ … t m reduces for a known t and an unknown m.
  -- The Bool: the term is the head of an application spine. Only the
  -- app and def cases read it (descent); every other case passes on
  -- through infer / check, which is not a head.
  infer′ : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Tm n → Mode → Bool → Result (Tm n × UseVec n)
  check′ : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → Tm n → Tm n → Result (UseVec n)

  headTailU : ∀ {n} → UseVec (suc n) → Use × UseVec n
  headTailU (u ∷ us) = u , us

  -- ⇐-ctor: a constructor spine against the data type di at params. The
  -- spine is walked from the head: the constructor's type instantiated at
  -- the parameters, then one Π per argument; an erased field is checked
  -- in spec and contributes no uses (Env.fieldMode, Env.combineArg).
  inferCtorSpine : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → ℕ → List (Tm n) → Tm n → Result (Tm n × UseVec n)
  inferCtorSpine k σ rs Γ m di params (ctor di′ ci) =
    guard "constructor of another data type" (di ≡ᵇ di′) >>
    lookupData σ di >>= λ d →
    lookupCtor d ci >>= λ c →
    instParams k σ (closed (Ctor.ctype c)) params >>= λ rest →
    ok (rest , u0s)
  inferCtorSpine k σ rs Γ m di params (app f a) =
    inferCtorSpine k σ rs Γ m di params f >>= λ (ty , fu) →
    whnf k σ ty >>= λ where
      (pi q A B) →
        check k σ rs Γ (fieldMode q m) a A >>= λ au →
        fieldUses k σ q m A au fu >>= λ uses →
        ok (inst B a , uses)
      _ → fail "too many constructor arguments"
  inferCtorSpine _ _ _ _ _ _ _ _ = fail "not a constructor spine"

  -- Uses of a constructor argument: a + field that is Data keeps them,
  -- a + field that is copyable scales them (args-snoc / args-snoc-copy).
  fieldUses : ∀ {n} → ℕ → Sig → Qty → Mode → Tm n → UseVec n → UseVec n → Result (UseVec n)
  fieldUses k σ reuse m A au fu =
    isData k σ A >>= λ d →
    if d then combineArg reuse m au fu
    else (isCopy k σ A >>= guard notCopy >> combineArg reuse m (scaleω au) fu)
  fieldUses k σ affine m A au fu = combineArg affine m au fu
  fieldUses k σ erased m A au fu = combineArg erased m au fu

  -- After the arguments, the residual telescope must be exhausted and
  -- be the expected data type.
  checkCtorApp : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → ℕ → List (Tm n) → Tm n → Tm n → Result (UseVec n)
  checkCtorApp k σ rs Γ m di params e expected =
    inferCtorSpine k σ rs Γ m di params e >>= λ (R , u) →
    whnf k σ R >>= λ where
      (pi _ _ _) → fail "too few constructor arguments"
      R′         → conv k σ R′ expected >> ok u

  -- A branch of match against the constructor's telescope ty: one λ per
  -- remaining Π, then the body against the motive at the indices of the
  -- constructor's target and at the constructor applied to the
  -- arguments. sm: the scrutinee is a variable a self-call may descend
  -- on (scrutOk), so a field of type D … is smaller; the fields of a
  -- computed scrutinee are not smaller than anything.
  checkBr : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → ℕ → ℕ → Bool → Tm n → Tm n → Tm n → List (Tm n) → Result (UseVec n)
  checkBr k σ rs Γ m di ci sm ty br mot args with whnf k σ ty
  ... | fail msg          = fail msg
  ... | ok (pi q A B)     = checkBrPi k σ rs Γ m di ci sm q A B br mot args
  ... | ok ty′            =
    check k σ rs Γ m br
      (appsFrom mot
        (List._++_ (drop (nparamsOf σ di) (proj₂ (apps ty′)))
          (appsFrom (ctor di ci) args ∷ [])))

  checkBrPi : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → ℕ → ℕ → Bool → Qty → Tm n → Tm (suc n) → Tm n → Tm n → List (Tm n) → Result (UseVec n)
  checkBrPi k σ rs Γ m di ci sm q A B (lam q′ A′ t) mot args =
    guard "λ/Π quantity mismatch" (eqQty q q′) >>
    checkTy k σ rs Γ A′ >>
    conv k σ A′ A >>
    (if eqQty q reuse then isCopy k σ A >>= guard notCopy else ok tt) >>
    let rec? = sm ∧ isDType di A
        rs′  = extRec rs rec? rec?
        args′ = List._++_ (renList suc args) (var zero ∷ [])
    in checkBr k σ rs′ (ext Γ q A) m di ci sm B t (wk mot) args′ >>= λ uses →
    let (u₀ , us) = headTailU uses
    in checkBound m q u₀ >> ok us
  checkBrPi k σ rs Γ m di ci sm q A B _ mot args =
    fail "match branch expected a λ for a constructor argument"

  nparamsOf : Sig → ℕ → ℕ
  nparamsOf σ i with lookupData σ i
  ... | ok d   = nparams d
  ... | fail _ = 0

  -- One branch per constructor, in declaration order. A constructor
  -- whose target indices clash with the scrutinee's cannot occur: its
  -- branch is consumed and not checked.
  checkBranches : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → ℕ → Bool → List (Tm n) → List (Tm n) → Tm n → ℕ → List Ctor → List (Tm n) → Result (UseVec n)
  checkBranches _ _ _ _ _ _ _ _ _ _ _ [] [] = ok u0s
  checkBranches k σ rs Γ m di sm params idxs mot ci (c ∷ cs) bs =
    instParams k σ (closed (Ctor.ctype c)) params >>= λ rest →
    clashes k σ (nparamsOf σ di) idxs rest >>= λ where
      true →
        case bs of λ where
          []        → fail ("missing branch for " ++ Ctor.cname c)
          (_ ∷ bs′) →
            checkBranches k σ rs Γ m di sm params idxs mot (suc ci) cs bs′
      false →
        case bs of λ where
          []        → fail ("missing branch for " ++ Ctor.cname c)
          (b ∷ bs′) →
            checkBr k σ rs Γ m di ci sm rest b mot [] >>= λ u →
            checkBranches k σ rs Γ m di sm params idxs mot (suc ci) cs bs′ >>= λ v →
            ok (combineAlt m u v)
  checkBranches _ _ _ _ _ _ _ _ _ _ _ [] (_ ∷ _) =
    fail "match branch count does not match constructors"

  -- The motive as a λ: over the scrutinee when the data type has no
  -- indices, otherwise over the first index (the rest of the motive's
  -- telescope is the remaining indices and the scrutinee).
  firstMotLam : ∀ {n} → ℕ → List (Qty × Tm 0) → List (Tm n) → Tm (suc n) → Tm n
  firstMotLam di []            params P = lam affine (appsFrom (dty di) params) P
  firstMotLam di ((q , T) ∷ _) params P = lam q (closed T) P

  checkMotive : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → ℕ → List (Qty × Tm 0) → List (Tm n) → Tm (suc n) → Result ⊤
  checkMotive k σ rs Γ di [] params P =
    checkTy k σ (extRec rs false false) (ext Γ affine (appsFrom (dty di) params)) P
  checkMotive k σ rs Γ di ((q , T) ∷ rest) params P =
    let Γ1 = ext Γ q (closed T)
        tail = motiveTail di (List._++_ (renList suc params) (var zero ∷ [])) rest
    in check k σ (extRec rs false false) Γ1 spec P tail >>= λ _ → ok tt

  -- The argument of an application (⇒-app-*), by the quantity of the Π.
  inferArg : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → Tm n → Tm n → Qty → Tm n → UseVec n → Result (UseVec n)
  inferArg k σ rs Γ m f a erased A fu =
    check k σ rs Γ spec a A >>= λ _ →
    (if eqMode m spec then ok u0s else ok fu)
  inferArg k σ rs Γ m f a affine A fu =
    check k σ rs Γ m a A >>= λ au → appUses σ m f fu au
  inferArg k σ rs Γ m f a reuse A fu =
    isData k σ A >>= λ d →
    if d then (check k σ rs Γ m a A >>= λ au → appUses σ m f fu au)
    else (isCopy k σ A >>= guard notCopy >>
          check k σ rs Γ m a A >>= λ au → appUses σ m f fu (scaleω au))

  -- ⇒-var-run / ⇒-var-evid / ⇒-var-spec
  infer′ k σ rs Γ (var x) run _ with qtyOf Γ x
  ... | erased = fail "no promotion: erased variable in run mode"
  ... | q      =
    isRunType k σ (typOf Γ x) >>= λ b →
    if b
    then ok (typOf Γ x , oneHot x (if eqQty q reuse then Uω else U1))
    else fail ("no promotion: variable has a spec type " ++ showTm (typOf Γ x))
  infer′ k σ rs Γ (var x) evid _ with qtyOf Γ x
  ... | erased = fail "no promotion: erased variable in evidence mode"
  ... | q      = ok (typOf Γ x , oneHot x (if eqQty q reuse then Uω else U1))
  infer′ k σ rs Γ (var x) spec _ = ok (typOf Γ x , u0s)

  -- ⇒-ze
  infer′ k σ rs Γ ze m _ = ok (nat , u0s)

  -- ⇒-su
  infer′ k σ rs Γ (su t) m _ =
    check k σ rs Γ m t nat >>= λ u → ok (nat , u)

  -- ⇒-tt
  infer′ k σ rs Γ one m _ = ok (unit , u0s)

  -- ⇒-nat / ⇒-unit / ⇒-empty  (spec only: these are types)
  infer′ k σ rs Γ nat run _ = fail "no promotion: Nat is an erased term"
  infer′ k σ rs Γ nat evid _ = fail "no promotion: Nat is an erased term"
  infer′ k σ rs Γ unit run _ = fail "no promotion: Unit is an erased term"
  infer′ k σ rs Γ unit evid _ = fail "no promotion: Unit is an erased term"
  infer′ k σ rs Γ empty run _ = fail "no promotion: Empty is an erased term"
  infer′ k σ rs Γ empty evid _ = fail "no promotion: Empty is an erased term"
  infer′ k σ rs Γ typ run _ = fail "no promotion: Type is an erased term"
  infer′ k σ rs Γ typ evid _ = fail "no promotion: Type is an erased term"
  infer′ k σ rs Γ nat spec _ = ok (typ , u0s)
  infer′ k σ rs Γ unit spec _ = ok (typ , u0s)
  infer′ k σ rs Γ empty spec _ = ok (typ , u0s)
  infer′ k σ rs Γ typ spec _ = fail "Type has no type (no Type : Type)"

  -- ⇒-pi
  infer′ k σ rs Γ (pi _ _ _) run _ = fail "no promotion: Π is an erased term"
  infer′ k σ rs Γ (pi _ _ _) evid _ = fail "no promotion: Π is an erased term"
  -- The codomain must be small. With B wf instead, Π (x : A) → Type : Type
  -- and Type is a retract of a small type (Girard's paradox).
  infer′ k σ rs Γ (pi q A B) spec _ =
    checkTy k σ rs Γ A >>
    check k σ (extRec rs false false) (ext Γ q A) spec B typ >>
    ok (typ , u0s)

  -- ⇒-lam
  infer′ k σ rs Γ (lam q A t) m _ =
    checkTy k σ rs Γ A >>
    (if eqQty q reuse
     then isCopy k σ A >>= guard notCopy
     else ok tt) >>
    infer k σ (lamRec rs) (ext Γ q A) m t >>= λ (B , uses) →
    let (u₀ , us) = headTailU uses
    in checkBound m q u₀ >> ok (pi q A B , us)

  -- ⇒-app-aff / ⇒-app-era / ⇒-app-reuse
  -- The argument is checked in the mode of the application; at a call
  -- site of an evidence definition in evid mode its uses are discarded
  -- (Env.appUses: instantiating a theorem does not consume resources).
  -- The head is inferred as a head (hd = true): the descent check is
  -- the outermost app's, on the maximal spine.
  infer′ k σ rs Γ (app f a) m hd =
    infer′ k σ rs Γ f m true >>= λ (ft , fu) →
    viewPi k σ ft >>= λ (q , A , B) →
    inferArg k σ rs Γ m f a q A fu >>= λ uses →
    checkRec m hd rs (app f a) >>
    ok (inst B a , uses)

  -- ⇒-idt
  infer′ k σ rs Γ (idt _ _ _) run _ = fail "no promotion: identity type is an erased term"
  infer′ k σ rs Γ (idt _ _ _) evid _ = fail "no promotion: identity type is an erased term"
  infer′ k σ rs Γ (idt A a b) spec _ =
    checkTy k σ rs Γ A >>
    floatIdOk k σ A >>
    check k σ rs Γ spec a A >>
    check k σ rs Γ spec b A >>
    ok (typ , u0s)

  -- rfl must be checked (⇐-refl)
  infer′ k σ rs Γ rfl m _ = fail "refl requires an expected identity type"

  -- ⇒-rwt
  infer′ k σ rs Γ (rwt eq P t) m _ =
    infer k σ rs Γ (rwtMode m) eq >>= λ (et , _) →
    viewId k σ et >>= λ (A , l , r) →
    checkTy k σ (extRec rs false false) (ext Γ affine A) P >>
    check k σ rs Γ m t (inst P r) >>= λ tu →
    ok (inst P l , tu)

  -- ⇒-dty
  infer′ k σ rs Γ (dty _) run _ = fail "no promotion: a data former is an erased term"
  infer′ k σ rs Γ (dty _) evid _ = fail "no promotion: a data former is an erased term"
  infer′ k σ rs Γ (dty i) spec _ =
    lookupData σ i >>= λ d →
    ok (dtyType (DataDecl.pqtys d) (DataDecl.idxs d) , u0s)

  -- constructors are checked (⇐-ctor)
  infer′ k σ rs Γ (ctor _ _) m _ = fail "constructor requires an expected data type"

  -- ⇒-mData
  infer′ k σ rs Γ (mData e P bs) m _ =
    infer k σ rs Γ m e >>= λ (et , eu) →
    viewData k σ et >>= λ (di , params , idxs) →
    lookupData σ di >>= λ d →
    checkMotive k σ rs Γ di (DataDecl.idxs d) params P >>
    let motFun = firstMotLam di (DataDecl.idxs d) params P
    in checkBranches k σ rs Γ m di (scrutOk rs e) params idxs motFun 0 (DataDecl.ctors d) bs >>= λ bu →
    combine m eu bu >>= λ uses →
    ok (appsFrom motFun (List._++_ idxs (e ∷ [])) , uses)

  -- ⇒-mNat
  infer′ k σ rs Γ (mNat e P z s) m _ =
    check k σ rs Γ m e nat >>= λ eu →
    checkTy k σ (extRec rs false false) (ext Γ affine nat) P >>
    check k σ rs Γ m z (inst P ze) >>= λ zu →
    let ok? = scrutOk rs e
        rs′ = extRec rs ok? ok?
        Γ′  = ext Γ (predQty Γ e) nat
    in check k σ rs′ Γ′ m s (motSuc P) >>= λ su-uses →
    let (u₀ , sus) = headTailU su-uses
    in checkBound m (predQty Γ e) u₀ >>
       let bu = combineAlt m zu sus
       in combine m eu bu >>= λ uses → ok (inst P e , uses)

  -- ⇒-mEmp
  infer′ k σ rs Γ (mEmp e P) m _ =
    check k σ rs Γ m e empty >>= λ eu →
    checkTy k σ (extRec rs false false) (ext Γ affine empty) P >>
    ok (inst P e , eu)

  -- ⇒-mUnit
  infer′ k σ rs Γ (mUnit e P u) m _ =
    check k σ rs Γ m e unit >>= λ eu →
    checkTy k σ (extRec rs false false) (ext Γ affine unit) P >>
    check k σ rs Γ m u (inst P one) >>= λ uu →
    combine m eu uu >>= λ uses → ok (inst P e , uses)

  -- ⇒-def; unapplied, the definition being checked is refused
  infer′ {n} k σ rs Γ (def i) m hd =
    selfApplied m hd rs i >>
    lookupDef σ i >>= λ d →
    (if allowedDef (Def.dmode d) m
     then ok tt
     else fail ("no promotion: " ++ showMode (Def.dmode d) ++ " definition " ++ Def.dname d ++ " in " ++ showMode m ++ " mode")) >>
    (if eqMode m run
     then (isRunType k σ (closed {n} (Def.dtype d)) >>= λ b →
           guard ("no promotion: definition " ++ Def.dname d ++ " has a spec type") b)
     else ok tt) >>
    ok (closed {n} (Def.dtype d) , u0s)

  -- ⇒-ann
  infer′ k σ rs Γ (ann e A) m _ =
    checkTy k σ rs Γ A >>
    check k σ rs Γ m e A >>= λ u → ok (A , u)

  -- ⇒-prod
  infer′ k σ rs Γ (prod _ _) run _ = fail "no promotion: × is an erased term"
  infer′ k σ rs Γ (prod _ _) evid _ = fail "no promotion: × is an erased term"
  infer′ k σ rs Γ (prod A B) spec _ =                        -- components small
    check k σ rs Γ spec A typ >>
    check k σ rs Γ spec B typ >>
    ok (typ , u0s)

  -- ⇒-nu
  infer′ k σ rs Γ (nu _) run _ = fail "no promotion: ν is an erased term"
  infer′ k σ rs Γ (nu _) evid _ = fail "no promotion: ν is an erased term"
  infer′ k σ rs Γ (nu F) spec _ =
    nuKind F >>= λ K →
    check k σ (extRec rs false false) (ext Γ affine K) spec F (wk K) >>
    guard "ν body is not strictly positive" (strictPos F) >>
    ok (K , u0s)

  -- ⇒-pair
  infer′ k σ rs Γ (pair a b) m _ =
    infer k σ rs Γ m a >>= λ (A , au) →
    infer k σ rs Γ m b >>= λ (B , bu) →
    combine m au bu >>= λ uses →
    ok (prod A B , uses)

  -- ⇒-letp: as ⇐-letp, but the body is inferred and its type must be a
  -- double weakening (it does not mention the components).
  infer′ k σ rs Γ (letp e t) m _ =
    infer k σ rs Γ m e >>= λ (E , eu) →
    viewProd k σ E >>= λ (A , B) →
    infer k σ (extRec (extRec rs false false) false false)
          (ext (ext Γ affine A) affine (wk B)) m t >>= λ (T , uses) →
    strengthen₂ T >>= λ C →
    let (ub , us₁) = headTailU uses
        (ua , tus) = headTailU us₁
    in checkBound m affine ub >>
       checkBound m affine ua >>
       combine m eu tus >>= λ us →
       ok (C , us)

  -- ⇒-unf
  infer′ k σ rs Γ (unf seed f) m _ =
    infer k σ rs Γ m seed >>= λ (S , seedU) →
    infer k σ rs Γ m f >>= λ (ft , fu) →
    viewPi k σ ft >>= λ (_ , S′ , Body) →
    conv k σ S′ S >>
    viewProd k σ (inst Body seed) >>= λ (A , S2) →
    conv k σ S2 S >>
    checkUnfold k σ m rs f >>
    combine m seedU fu >>= λ uses →
    ok (nu (prod (wk A) (var zero)) , uses)

  -- ⇒-ucons
  -- ⇒-ucons. The same step an unfold checks: a bare ν substitutes
  -- the scrutinee's type for Y, and an applied family (Always, ~)
  -- substitutes ν F for Y and keeps the indices. The goal is that
  -- product; the family flag is the unfold check's, not this one's.
  infer′ k σ rs Γ (ucons s) m _ =
    infer k σ rs Γ m s >>= λ (T , u) →
    unfStep k σ T T >>= λ (goal , _) →
    ok (goal , u)

  -- ⇒-i64 / ⇒-f32ty / ⇒-tensor  (spec formers)
  infer′ k σ rs Γ i64 run _ = fail "no promotion: I64 is an erased term"
  infer′ k σ rs Γ i64 evid _ = fail "no promotion: I64 is an erased term"
  infer′ k σ rs Γ f32ty run _ = fail "no promotion: F32 is an erased term"
  infer′ k σ rs Γ f32ty evid _ = fail "no promotion: F32 is an erased term"
  infer′ k σ rs Γ i64 spec _ = ok (typ , u0s)
  infer′ k σ rs Γ f32ty spec _ = ok (typ , u0s)
  infer′ k σ rs Γ (tensor _ _) run _ = fail "no promotion: Tensor is an erased term"
  infer′ k σ rs Γ (tensor _ _) evid _ = fail "no promotion: Tensor is an erased term"
  infer′ k σ rs Γ (tensor D S) spec _ =
    checkTy k σ rs Γ D >>
    isNxDtype k σ D >>= guard "Tensor dtype must be I64 or F32" >>
    check k σ rs Γ spec S i64 >>= λ _ →
    ok (typ , u0s)

  -- ⇒-addi / ⇒-muli
  infer′ k σ rs Γ (addi x y) m _ =
    check k σ rs Γ m x i64 >>= λ xu →
    check k σ rs Γ m y i64 >>= λ yu →
    combine m xu yu >>= λ uses →
    ok (i64 , uses)
  infer′ k σ rs Γ (muli x y) m _ =
    check k σ rs Γ m x i64 >>= λ xu →
    check k σ rs Γ m y i64 >>= λ yu →
    combine m xu yu >>= λ uses →
    ok (i64 , uses)

  -- ⇒-addt
  infer′ k σ rs Γ (addt t u) m _ =
    infer k σ rs Γ m t >>= λ (T , tu) →
    whnf k σ T >>= λ where
      (tensor D S) →
        check k σ rs Γ m u (tensor D S) >>= λ uu →
        combine m tu uu >>= λ uses →
        ok (tensor D S , uses)
      T′ → fail ("addt expected a Tensor, got " ++ showTm T′)

  -- ⇒-toi64
  infer′ k σ rs Γ (toi64 n) m _ =
    check k σ rs Γ m n nat >>= λ u →
    ok (i64 , u)

  -- ⇒-packi
  infer′ k σ rs Γ (packi x y) m _ =
    check k σ rs Γ m x i64 >>= λ xu →
    check k σ rs Γ m y i64 >>= λ yu →
    combine m xu yu >>= λ uses →
    ok (tensor i64 i64two , uses)

  -- ⇐-lam: against a Π after whnf; otherwise inferred and converted.
  check′ k σ rs Γ m (lam q A t) T = checkLam k σ rs Γ m (lam q A t) T (viewPi k σ T)

  -- ⇐-refl
  check′ k σ rs Γ m rfl T =
    viewId k σ T >>= λ (A , a , b) →
    floatIdOk k σ A >>
    conv k σ a b >> ok u0s

  -- ⇐-pair
  check′ k σ rs Γ m (pair a b) T =
    viewProd k σ T >>= λ (A , B) →
    check k σ rs Γ m a A >>= λ au →
    check k σ rs Γ m b B >>= λ bu →
    combine m au bu

  -- ⇐-letp: the scrutinee is inferred and read as a product; the body
  -- is checked under two affine binders (a at var 1, b at var 0) against
  -- the expected type weakened twice; each binder's uses are bounded and
  -- the rest combined with the scrutinee's.
  check′ k σ rs Γ m (letp e t) T =
    infer k σ rs Γ m e >>= λ (E , eu) →
    viewProd k σ E >>= λ (A , B) →
    check k σ (extRec (extRec rs false false) false false)
          (ext (ext Γ affine A) affine (wk B)) m t (wk (wk T)) >>= λ uses →
    let (ub , us₁) = headTailU uses
        (ua , tus) = headTailU us₁
    in checkBound m affine ub >>
       checkBound m affine ua >>
       combine m eu tus

  -- ⇐-unf (λ may be affine or + on Data)
  check′ k σ rs Γ m (unf seed (lam q A t)) T =
    infer k σ rs Γ m seed >>= λ (S , seedU) →
    conv k σ A S >>
    unfStep k σ T S >>= λ (goal , fam) →
    check k σ (extRec (if fam then setGuard rs else rs) false false)
          (ext Γ q S) m t (wk goal) >>= λ uses →
    let (u₀ , us) = headTailU uses
    in checkBound m q u₀ >>
       checkUnfold k σ m rs (lam q A t) >>
       combine m seedU us

  check′ k σ rs Γ m (unf seed f) T =
    infer k σ rs Γ m seed >>= λ (S , seedU) →
    unfStep k σ T S >>= λ (goal , fam) →
    check k σ (if fam then setGuard rs else rs) Γ m f
          (pi affine S (wk goal)) >>= λ fu →
    checkUnfold k σ m rs f >>
    combine m seedU fu

  -- ⇐-ctor / ⇐-conv (default)
  check′ k σ rs Γ m e A = checkAgainst k σ rs Γ m e A (viewData k σ A) (ctorSpine e)

  checkLam : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → Tm n → Tm n → Result (Qty × Tm n × Tm (suc n)) → Result (UseVec n)
  checkLam k σ rs Γ m e T (fail _) = inferConv k σ rs Γ m e T
  checkLam k σ rs Γ m (lam q A t) T (ok (q′ , A′ , B)) =
    guard "λ/Π quantity mismatch" (eqQty q q′) >>
    checkTy k σ rs Γ A >>
    conv k σ A A′ >>
    (if eqQty q reuse then isCopy k σ A′ >>= guard notCopy else ok tt) >>
    check k σ (lamRec rs) (ext Γ q A′) m t B >>= λ uses →
    let (u₀ , us) = headTailU uses
    in checkBound m q u₀ >> ok us
  checkLam k σ rs Γ m _ T (ok _) = fail "checkLam: not a λ"

  -- ⇐-conv: infer, then convert to the expected type.
  inferConv : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → Tm n → Tm n → Result (UseVec n)
  inferConv k σ rs Γ m e A = infer k σ rs Γ m e >>= λ (B , u) → conv k σ B A >> ok u

  -- A constructor spine against a data type is checked along the
  -- constructor's telescope; anything else is inferred and converted.
  checkAgainst : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → Mode → Tm n → Tm n
    → Result (ℕ × List (Tm n) × List (Tm n)) → Maybe (ℕ × ℕ × List (Tm n)) → Result (UseVec n)
  checkAgainst k σ rs Γ m e A (ok (di , params , idxs)) (just (di′ , _ , _)) =
    if di ≡ᵇ di′
    then checkCtorApp k σ rs Γ m di params e
           (appsFrom (dty di) (List._++_ params idxs))
    else inferConv k σ rs Γ m e A
  checkAgainst k σ rs Γ m e A _ _ = inferConv k σ rs Γ m e A

------------------------------------------------------------------------
-- Check a whole signature. Run and evidence definitions that reach
-- each other are one block and descend on one shared argument.
-- Spec is not a logic: it is not in the block, and it is not checked
-- for descent.
------------------------------------------------------------------------

emptyRec : RecSt 0
emptyRec = recst nothing 0 nothing [] [] false []

-- The non-erased argument positions of a definition's type, read
-- syntactically: the candidates for the position a self-call descends on.
argPositions : ∀ {n} → ℕ → Tm n → List ℕ
argPositions j (pi q _ B) =
  (if eqQty q erased then [] else j ∷ []) List.++ argPositions (suc j) B
argPositions _ _ = []

-- Constructor fields must be small types. Parameters are (A : Type) and
-- are skipped; a field of type Type would make the data type a large
-- inductive in Type, and match with motive Type would retract Type into it.
checkCtorFields : ∀ {n} → ℕ → Sig → RecSt n → Ctx n → ℕ → Tm n → Result ⊤
checkCtorFields k σ rs Γ (suc np) (pi q A B) =
  checkCtorFields k σ (extRec rs false false) (ext Γ q A) np B
checkCtorFields _ _ _ _ (suc _) _ =
  fail "constructor type has too few parameter binders"
checkCtorFields k σ rs Γ zero (pi q A B) =
  check k σ rs Γ spec A typ >>
  (if eqQty q reuse then isCopy k σ A >>= guard notCopy else ok tt) >>
  checkCtorFields k σ (extRec rs false false) (ext Γ q A) zero B
checkCtorFields _ _ _ _ zero _ = ok tt

checkCtorTy : ℕ → Sig → ℕ → ℕ → ℕ → Tm 0 → Result ⊤
checkCtorTy k σ di np ni ctype =
  checkTy k σ emptyRec [] ctype >>
  checkCtorFields k σ emptyRec [] np ctype >>
  checkCtorRest k σ di np ni ctype

checkCtors : ℕ → Sig → ℕ → ℕ → ℕ → List Ctor → Result ⊤
checkCtors _ _ _  _  _  []       = ok tt
checkCtors k σ di np ni (c ∷ cs) =
  tag (Ctor.cname c) (checkCtorTy k σ di np ni (Ctor.ctype c)) >>
  checkCtors k σ di np ni cs

checkData : ℕ → Sig → ℕ → DataDecl → Result ⊤
checkData k σ di d =
  tag (DataDecl.dname d)
    (checkCtors k σ di (nparams d) (nidxs d) (DataDecl.ctors d))

checkDatas : ℕ → Sig → Result ⊤
checkDatas k σ = go 0 (Sig.datas σ)
  where
    go : ℕ → List DataDecl → Result ⊤
    go _ []       = ok tt
    go i (d ∷ ds) = checkData k σ i d >> go (suc i) ds

-- Definitions a run or evidence body names. The call graph is these
-- mentions; spec and data are not edges.
cats : List ℕ → List ℕ → List ℕ
cats []       ys = ys
cats (x ∷ xs) ys = x ∷ cats xs ys

mutual
  mentions : ∀ {n} → Tm n → List ℕ
  mentions (def i)        = i ∷ []
  mentions (app f a)      = cats (mentions f) (mentions a)
  mentions (pi _ A B)     = cats (mentions A) (mentions B)
  mentions (lam _ A t)    = cats (mentions A) (mentions t)
  mentions (su t)         = mentions t
  mentions (mData e P bs) = cats (mentions e) (cats (mentions P) (mentionsList bs))
  mentions (mNat e P z s) = cats (mentions e) (cats (mentions P) (cats (mentions z) (mentions s)))
  mentions (mEmp e P)     = cats (mentions e) (mentions P)
  mentions (mUnit e P u)  = cats (mentions e) (cats (mentions P) (mentions u))
  mentions (idt A a b)    = cats (mentions A) (cats (mentions a) (mentions b))
  mentions (rwt e P t)    = cats (mentions e) (cats (mentions P) (mentions t))
  mentions (ann e A)      = cats (mentions e) (mentions A)
  mentions (prod A B)     = cats (mentions A) (mentions B)
  mentions (pair a b)     = cats (mentions a) (mentions b)
  mentions (letp e t)     = cats (mentions e) (mentions t)
  mentions (nu F)         = mentions F
  mentions (unf s f)      = cats (mentions s) (mentions f)
  mentions (ucons s)      = mentions s
  mentions (tensor d s)   = cats (mentions d) (mentions s)
  mentions (addi a b)     = cats (mentions a) (mentions b)
  mentions (muli a b)     = cats (mentions a) (mentions b)
  mentions (addt t u)     = cats (mentions t) (mentions u)
  mentions (toi64 t)      = mentions t
  mentions (packi a b)    = cats (mentions a) (mentions b)
  mentions _              = []

  mentionsList : ∀ {n} → List (Tm n) → List ℕ
  mentionsList []       = []
  mentionsList (t ∷ ts) = cats (mentions t) (mentionsList ts)

recMode : Mode → Bool
recMode run  = true
recMode evid = true
recMode spec = false

keepRec : Sig → List ℕ → List ℕ
keepRec _ []       = []
keepRec σ (j ∷ js) with lookupDef σ j
... | ok d    = if recMode (Def.dmode d) then j ∷ keepRec σ js else keepRec σ js
... | fail _  = keepRec σ js

edge : Sig → ℕ → List ℕ
edge σ i with lookupDef σ i
... | fail _ = []
... | ok d   = if recMode (Def.dmode d) then keepRec σ (mentions (Def.dbody d)) else []

mutual
  reachGo : Sig → ℕ → ℕ → ℕ → List ℕ → Bool
  reachGo _ zero _ _ _ = false
  reachGo σ (suc f) tgt cur vis =
    if cur ≡ᵇ tgt then true
    else if elemℕ cur vis then false
    else reachAny σ f tgt (edge σ cur) (cur ∷ vis)

  reachAny : Sig → ℕ → ℕ → List ℕ → List ℕ → Bool
  reachAny _ _ _ [] _ = false
  reachAny σ f tgt (x ∷ xs) vis = reachGo σ f tgt x vis ∨ reachAny σ f tgt xs vis

reaches : Sig → ℕ → ℕ → Bool
reaches σ src tgt = reachGo σ (suc (length (Sig.defs σ))) tgt src []

-- Indices j such that i and j reach each other. i reaches i, so a
-- run or evidence definition is always in its own block.
component : Sig → ℕ → List ℕ
component σ i = go 0 (Sig.defs σ)
  where
    go : ℕ → List Def → List ℕ
    go _ []       = []
    go j (_ ∷ ds) =
      let rest = go (suc j) ds in
      if reaches σ i j ∧ reaches σ j i then j ∷ rest else rest

argsOf : Sig → ℕ → List ℕ
argsOf σ i with lookupDef σ i
... | ok d   = argPositions 0 (Def.dtype d)
... | fail _ = []

interℕ : List ℕ → List ℕ → List ℕ
interℕ [] _ = []
interℕ (x ∷ xs) ys = if elemℕ x ys then x ∷ interℕ xs ys else interℕ xs ys

sharedArgs : Sig → List ℕ → List ℕ
sharedArgs _ []            = []
sharedArgs σ (i ∷ [])      = argsOf σ i
sharedArgs σ (i ∷ j ∷ js)  = interℕ (argsOf σ i) (sharedArgs σ (j ∷ js))

-- Checking definition i, descending on argument position p, with every
-- mutually reachable run/evid definition counted as a self-call.
defRec : Sig → ℕ → ℕ → RecSt 0
defRec σ i p = recst (just i) p (just p) [] [] false (component σ i)

allOk : ℕ → Sig → List ℕ → ℕ → Bool
allOk _ _ [] _ = true
allOk k σ (i ∷ is) p with lookupDef σ i
... | fail _ = false
... | ok d with check k σ (defRec σ i p) [] (Def.dmode d) (Def.dbody d) (Def.dtype d)
... | ok _   = allOk k σ is p
... | fail _ = false

findPos : ℕ → Sig → List ℕ → List ℕ → Maybe ℕ
findPos _ _ _ []       = nothing
findPos k σ blk (p ∷ ps) =
  if allOk k σ blk p then just p else findPos k σ blk ps

-- Two or more members. A single definition keeps its own candidates.
mutual? : List ℕ → Bool
mutual? (_ ∷ _ ∷ _) = true
mutual? _            = false

-- The position the whole block descends on, as a singleton, when one
-- shared index works for every member. A block of two or more members
-- with no such index is empty here: handing back the candidates would
-- let each member pass on its own index. A single member keeps the
-- candidates, so the first failure is the one reported. Spec keeps its
-- own positions: descent is not checked there.
pickPos : ℕ → Sig → ℕ → Def → List ℕ
pickPos k σ i d =
  if recMode (Def.dmode d)
  then choose (component σ i) (sharedArgs σ (component σ i))
  else argPositions 0 (Def.dtype d)
  where
    choose : List ℕ → List ℕ → List ℕ
    choose blk ps with findPos k σ blk ps
    ... | just p  = p ∷ []
    ... | nothing = if mutual? blk then [] else ps

-- The body is checked descending on the first shared non-erased
-- argument that works for the whole block. A single definition keeps
-- its later candidates, and the first failure is the one reported. A
-- block of two or more with no such argument is refused. A definition
-- with no self-call passes the first attempt. The position only affects
-- the descent check, so a type error is the same for every position.
checkAt : ℕ → Sig → ℕ → Def → ℕ → Result (UseVec 0)
checkAt k σ i d p = check k σ (defRec σ i p) [] (Def.dmode d) (Def.dbody d) (Def.dtype d)

retryBody : ℕ → Sig → ℕ → Def → String → List ℕ → Result (UseVec 0)
retryBody k σ i d msg []       = fail msg
retryBody k σ i d msg (p ∷ ps) =
  case checkAt k σ i d p of λ where
    (ok u)   → ok u
    (fail _) → retryBody k σ i d msg ps

-- No shared index works for a block of two or more. The first candidate
-- is checked so its error is the one reported. A success there is still
-- noDescent: that member descended on its own index, not on one index
-- for the whole block.
refuseShared : ℕ → Sig → ℕ → Def → List ℕ → Result (UseVec 0)
refuseShared _ _ _ _ [] = fail noDescent
refuseShared k σ i d (p ∷ _) =
  case checkAt k σ i d p of λ where
    (fail msg) → fail msg
    (ok _)     → fail noDescent

checkBodyAt : ℕ → Sig → ℕ → Def → List ℕ → Result (UseVec 0)
checkBodyAt k σ i d [] with sharedArgs σ (component σ i)
... | [] = checkAt k σ i d 0
... | ps@(_ ∷ _) =
  if recMode (Def.dmode d) ∧ mutual? (component σ i)
  then refuseShared k σ i d ps
  else checkAt k σ i d 0
checkBodyAt k σ i d (p ∷ ps) =
  case checkAt k σ i d p of λ where
    (ok u)     → ok u
    (fail msg) → retryBody k σ i d msg ps

checkBody : ℕ → Sig → ℕ → Def → Result (UseVec 0)
checkBody k σ i d = checkBodyAt k σ i d (pickPos k σ i d)

checkDef : ℕ → Sig → ℕ → Result ⊤
checkDef k σ i =
  lookupDef σ i >>= λ d →
  tag (Def.dname d ++ " type") (checkTy k σ emptyRec [] (Def.dtype d)) >>
  tag (Def.dname d ++ " body") (checkBody k σ i d) >>
  tag (Def.dname d ++ " productivity")
      (checkNu k σ (component σ i) (Def.dmode d) (Def.dtype d) (Def.dbody d)) >>
  ok tt

checkDefs : ℕ → Sig → ℕ → List Def → Result ⊤
checkDefs _ _ _ []       = ok tt
checkDefs k σ i (_ ∷ ds) = checkDef k σ i >> checkDefs k σ (suc i) ds

checkSig : ℕ → Sig → Result ⊤
checkSig k σ = checkDatas k σ >> checkDefs k σ 0 (Sig.defs σ)

-- Default fuel for closed examples.
fuel : ℕ
fuel = 2000

checkSig! : Sig → Result ⊤
checkSig! = checkSig fuel

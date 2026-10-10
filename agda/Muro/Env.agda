------------------------------------------------------------------------
-- Signature, context, and uses. Safe kernel shared by Check and ⊢.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Env where

open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base as List using (List; []; _∷_; length)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.String.Base using (String)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base as Vec using (Vec; lookup; map)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst

record Def : Set where
  constructor mkDef
  field
    dname : String
    dmode : Mode
    dtype : Tm 0
    dbody : Tm 0

record Ctor : Set where
  constructor mkCtor
  field
    cname : String
    ctype : Tm 0

record DataDecl : Set where
  constructor mkData
  field
    dname : String
    pqtys : List Qty
    idxs  : List (Qty × Tm 0)
    ctors : List Ctor

record Sig : Set where
  constructor mkSig
  field
    datas : List DataDecl
    defs  : List Def

fromDefs : List Def → Sig
fromDefs ds = mkSig [] ds

lookupList : ∀ {A : Set} → List A → ℕ → Result A
lookupList []       _       = fail "unknown index"
lookupList (x ∷ _)  zero    = ok x
lookupList (_ ∷ xs) (suc i) = lookupList xs i

lookupDef : Sig → ℕ → Result Def
lookupDef σ i = lookupList (Sig.defs σ) i

lookupData : Sig → ℕ → Result DataDecl
lookupData σ i = lookupList (Sig.datas σ) i

lookupCtor : DataDecl → ℕ → Result Ctor
lookupCtor d i = lookupList (DataDecl.ctors d) i

nparams : DataDecl → ℕ
nparams d = length (DataDecl.pqtys d)

nidxs : DataDecl → ℕ
nidxs d = length (DataDecl.idxs d)

dtyType : ∀ {n} → List Qty → List (Qty × Tm 0) → Tm n
dtyType [] []              = typ
dtyType (q ∷ qs) ixs       = pi q typ (dtyType qs ixs)
dtyType [] ((q , T) ∷ ixs) = pi q (closed T) (dtyType [] ixs)

record Bind (n : ℕ) : Set where
  constructor bind
  field
    bqty : Qty
    btyp : Tm n

Ctx : ℕ → Set
Ctx n = Vec (Bind n) n

wkBind : ∀ {n} → Bind n → Bind (suc n)
wkBind (bind q A) = bind q (wk A)

ext : ∀ {n} → Ctx n → Qty → Tm n → Ctx (suc n)
ext Γ q A = bind q (wk A) Vec.∷ map wkBind Γ

qtyOf : ∀ {n} → Ctx n → Fin n → Qty
qtyOf Γ x = Bind.bqty (lookup Γ x)

typOf : ∀ {n} → Ctx n → Fin n → Tm n
typOf Γ x = Bind.btyp (lookup Γ x)

UseVec : ℕ → Set
UseVec n = Vec Use n

u0s : ∀ {n} → UseVec n
u0s {zero}  = Vec.[]
u0s {suc n} = U0 Vec.∷ u0s

-- An argument that will be copied: one use becomes many. Applied to the
-- uses of a term passed at a + position whose type is copyable but not
-- Data (a closure), so that an affine variable it captures is refused.
scaleUse : Use → Use
scaleUse U1 = Uω
scaleUse u  = u

scaleω : ∀ {n} → UseVec n → UseVec n
scaleω = map scaleUse

oneHot : ∀ {n} → Fin n → Use → UseVec n
oneHot {suc _} zero    u = u  Vec.∷ u0s
oneHot {suc _} (suc i) u = U0 Vec.∷ oneHot i u

addUse : Use → Use → Result Use
addUse U0 u  = ok u
addUse u  U0 = ok u
addUse U1 U1 = fail "affine variable used twice"
addUse Uω _  = ok Uω
addUse _  Uω = ok Uω

addUses : ∀ {n} → UseVec n → UseVec n → Result (UseVec n)
addUses Vec.[]       Vec.[]       = ok Vec.[]
addUses (x Vec.∷ xs) (y Vec.∷ ys) = (Vec._∷_) <$> addUse x y ⊛ addUses xs ys

maxUse : Use → Use → Use
maxUse Uω _  = Uω
maxUse _  Uω = Uω
maxUse U1 _  = U1
maxUse _  U1 = U1
maxUse U0 U0 = U0

maxUses : ∀ {n} → UseVec n → UseVec n → UseVec n
maxUses Vec.[]       Vec.[]       = Vec.[]
maxUses (x Vec.∷ xs) (y Vec.∷ ys) = maxUse x y Vec.∷ maxUses xs ys

combine : ∀ {n} → Mode → UseVec n → UseVec n → Result (UseVec n)
combine run  u v = addUses u v
combine evid u v = addUses u v
combine spec _ _ = ok u0s

combineAlt : ∀ {n} → Mode → UseVec n → UseVec n → UseVec n
combineAlt run  u v = maxUses u v
combineAlt evid u v = maxUses u v
combineAlt spec _ _ = u0s

checkBound : Mode → Qty → Use → Result ⊤
checkBound run  erased U1 = fail "erased variable used computationally"
checkBound evid erased U1 = fail "erased variable used computationally"
checkBound run  erased Uω = fail "erased variable used computationally"
checkBound evid erased Uω = fail "erased variable used computationally"
checkBound run  affine Uω = fail "affine variable used as reusable"
checkBound evid affine Uω = fail "affine variable used as reusable"
checkBound _    _      _  = ok tt

-- Mode of a constructor argument (Check.checkCtorArgs): an erased field
-- is checked in spec, the others in the mode of the application.
fieldMode : Qty → Mode → Mode
fieldMode erased _ = spec
fieldMode affine m = m
fieldMode reuse  m = m

-- Uses of a constructor application (Check.checkCtorArgs): an erased
-- argument contributes nothing, and spec forgets everything.
combineArg : ∀ {n} → Qty → Mode → UseVec n → UseVec n → Result (UseVec n)
combineArg erased spec _  _  = ok u0s
combineArg erased run  _  fu = ok fu
combineArg erased evid _  fu = ok fu
combineArg affine m    au fu = combine m au fu
combineArg reuse  m    au fu = combine m au fu

-- Uses of an application f a (Check.infer′ app): instantiating an
-- evidence definition in evid mode does not consume the argument's
-- resources (manual: wall.md). The argument is still checked in the
-- mode of the application.
headDef : ∀ {n} → Tm n → Maybe ℕ
headDef (app f _) = headDef f
headDef (def i)   = just i
headDef _         = nothing

evidCall : Sig → Mode → ∀ {n} → Tm n → Bool
evidCall σ evid f with headDef f
... | nothing = false
... | just i with lookupList (Sig.defs σ) i
...   | ok d   = eqMode (Def.dmode d) evid
...   | fail _ = false
evidCall σ _ _ = false

appUses : Sig → Mode → ∀ {n} → Tm n → UseVec n → UseVec n → Result (UseVec n)
appUses σ m f fu au = if evidCall σ m f then ok fu else combine m fu au

allowedDef : Mode → Mode → Bool
allowedDef run  _    = true
allowedDef evid spec = true
allowedDef evid evid = true
allowedDef spec spec = true
allowedDef _    _    = false

-- Modes are ordered run ≤ evid ≤ spec: a run term may be used as
-- evidence, evidence may be used in a spec. allowedDef d is monotone in
-- the use mode along this order, which is what mode weakening needs.
infix 4 _≤ᵐ_
data _≤ᵐ_ : Mode → Mode → Set where
  ≤ᵐ-run  : ∀ {m} → run ≤ᵐ m
  ≤ᵐ-evid : evid ≤ᵐ evid
  ≤ᵐ-evsp : evid ≤ᵐ spec
  ≤ᵐ-spec : spec ≤ᵐ spec

≤ᵐ-refl : ∀ {m} → m ≤ᵐ m
≤ᵐ-refl {run}  = ≤ᵐ-run
≤ᵐ-refl {evid} = ≤ᵐ-evid
≤ᵐ-refl {spec} = ≤ᵐ-spec

≤ᵐ-trans : ∀ {a b c} → a ≤ᵐ b → b ≤ᵐ c → a ≤ᵐ c
≤ᵐ-trans ≤ᵐ-run  _       = ≤ᵐ-run
≤ᵐ-trans ≤ᵐ-evid h       = h
≤ᵐ-trans ≤ᵐ-evsp ≤ᵐ-spec = ≤ᵐ-evsp
≤ᵐ-trans ≤ᵐ-spec ≤ᵐ-spec = ≤ᵐ-spec

≤ᵐ-spec-top : ∀ {m} → m ≤ᵐ spec
≤ᵐ-spec-top {run}  = ≤ᵐ-run
≤ᵐ-spec-top {evid} = ≤ᵐ-evsp
≤ᵐ-spec-top {spec} = ≤ᵐ-spec

-- The mode of the equation of a rewrite in mode m: evidence, except
-- that a spec rewrite reads a spec equation. Every premise of every
-- rule is then in a mode ≥ the mode of its conclusion.
rwtMode : Mode → Mode
rwtMode spec = spec
rwtMode _    = evid

≤ᵐ-rwtMode : ∀ m → m ≤ᵐ rwtMode m
≤ᵐ-rwtMode run  = ≤ᵐ-run
≤ᵐ-rwtMode evid = ≤ᵐ-evid
≤ᵐ-rwtMode spec = ≤ᵐ-spec

rwtMode-mono : ∀ {m m′} → m ≤ᵐ m′ → rwtMode m ≤ᵐ rwtMode m′
rwtMode-mono {m′ = run}  ≤ᵐ-run = ≤ᵐ-evid
rwtMode-mono {m′ = evid} ≤ᵐ-run = ≤ᵐ-evid
rwtMode-mono {m′ = spec} ≤ᵐ-run = ≤ᵐ-evsp
rwtMode-mono ≤ᵐ-evid = ≤ᵐ-evid
rwtMode-mono ≤ᵐ-evsp = ≤ᵐ-evsp
rwtMode-mono ≤ᵐ-spec = ≤ᵐ-spec

allowedDef-mono : ∀ d {m m′} → m ≤ᵐ m′
  → allowedDef d m ≡ true → allowedDef d m′ ≡ true
allowedDef-mono run  _       _ = refl
allowedDef-mono evid ≤ᵐ-run  ()
allowedDef-mono evid ≤ᵐ-evid h = h
allowedDef-mono evid ≤ᵐ-evsp _ = refl
allowedDef-mono evid ≤ᵐ-spec h = h
allowedDef-mono spec ≤ᵐ-run  ()
allowedDef-mono spec ≤ᵐ-evid ()
allowedDef-mono spec ≤ᵐ-evsp ()
allowedDef-mono spec ≤ᵐ-spec h = h

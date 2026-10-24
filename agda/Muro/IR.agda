------------------------------------------------------------------------
-- Closed-run image. Not a source syntax: none of these constructors is
-- added to Tm.
--
-- An atom is a nullary constructor of one closed data declaration named
-- Atom. `atom` and `matom` are `ctor` and `mData` of that declaration, so
-- they are inside Tm. An index outside the declaration is refused. Nothing
-- here builds an atom from a string.
--
-- Elaboration is well-founded on `size`. It does not re-check the book.
-- Affine and reuse are already discharged. Erased λ-arguments are dropped.
-- Motives, rewrite, and annotation erase to the run body.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.IR where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∨_)
open import Data.Fin.Base using (toℕ)
import Data.Fin.Base as F
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; _≡ᵇ_; s≤s; z≤n)
open import Data.Nat.Induction using (<-rec)
open import Data.Nat.Properties using (≤-refl; ≤-<-trans; <-≤-trans; <-trans; m≤m+n; m≤n+m)
open import Data.Nat.Show using (show)
open import Data.Product.Base using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Env
open import Muro.Subst using (stream)

infix 5 _<>_
_<>_ : String → String → String
_<>_ = Data.String.Base._++_

------------------------------------------------------------------------
-- Image.
------------------------------------------------------------------------

data Layout : Set where
  natL unitL opaqueL : Layout
  pairL : Layout → Layout → Layout
  streamL : Layout → Layout
  -- Nominal. Constructor fields live in `ctorShapes`, not in the layout:
  -- inlining them would make `layoutOf` recurse through a data type that
  -- mentions itself (List A inside cons).
  dataL : String → Layout

mutual
  data Term : Set where
    Var : String → Term
    Let : String → Layout → Term → Term → Term
    Call : String → List Term → Term
    Con : String → String → List Term → Term
    Match : Term → List Arm → Term
    Ze : Term
    Su : Term → Term
    Tt : Term
    Pair : Term → Term → Term
    -- Names are a then b. In the body, b is de Bruijn 0 and a is de Bruijn 1.
    Letp : String → String → Term → Term → Term
    Uncons : Term → Term
    Abort : Term
    Stream : Term → List (String × Term) → String → Term

  data Arm : Set where
    arm : String → List String → Term → Arm

record Fun : Set where
  constructor fn
  field
    fname : String
    fexport : Bool
    params : List (String × Layout)
    ret : Layout
    body : Term

record E : Set where
  constructor mkE
  field
    etm : Term
    elay : Layout
    esteps : List Fun

------------------------------------------------------------------------
-- Atoms. The declaration occupies data index 0 in the signature that
-- `atom` / `matom` are read against. Any other closed enumeration is an
-- ordinary `ctor` / `mData`; these two names are that case.
------------------------------------------------------------------------

atomDecl : (di : ℕ) → List String → DataDecl
atomDecl di names = mkData "Atom" [] [] (map (λ s → mkCtor s (dty di)) names)

atom : ∀ {n} → ℕ → Tm n
atom ci = ctor 0 ci

matom : ∀ {n} → Tm n → Tm (suc n) → List (Tm n) → Tm n
matom = mData

atomCon : (names : List String) → F.Fin (length names) → Term
atomCon names i = Con "Atom" (Data.List.Base.lookup names i) []

------------------------------------------------------------------------
-- Size. Every immediate child is strictly smaller.
------------------------------------------------------------------------

mutual
  size : ∀ {n} → Tm n → ℕ
  size (var _)        = 1
  size typ            = 1
  size (pi _ A B)     = suc (size A + size B)
  size (lam _ A t)    = suc (size A + size t)
  size (app f a)      = suc (size f + size a)
  size nat            = 1
  size ze             = 1
  size (su t)         = suc (size t)
  size unit           = 1
  size one            = 1
  size empty          = 1
  size (dty _)        = 1
  size (ctor _ _)     = 1
  size (mData e P bs) = suc (size e + size P + sumSize bs)
  size (mNat e P z s) = suc (size e + size P + size z + size s)
  size (mEmp e P)     = suc (size e + size P)
  size (mUnit e P u)  = suc (size e + size P + size u)
  size (idt A x y)    = suc (size A + size x + size y)
  size rfl            = 1
  size (rwt e P t)    = suc (size e + size P + size t)
  size (def _)        = 1
  size (ann e A)      = suc (size e + size A)
  size (prod A B)     = suc (size A + size B)
  size (pair a b)     = suc (size a + size b)
  size (letp e t)     = suc (size e + size t)
  size (nu F)         = suc (size F)
  size (unf s f)      = suc (size s + size f)
  size (ucons s)      = suc (size s)
  size i64            = 1
  size f32ty          = 1
  size (tensor d s)   = suc (size d + size s)
  size (addi x y)     = suc (size x + size y)
  size (muli x y)     = suc (size x + size y)
  size (addt t u)     = suc (size t + size u)
  size (toi64 t)      = suc (size t)
  size (packi x y)    = suc (size x + size y)

  sumSize : ∀ {n} → List (Tm n) → ℕ
  sumSize []       = 0
  sumSize (t ∷ ts) = size t + sumSize ts

a<+ : ∀ a b → a < suc (a + b)
a<+ a b = s≤s (m≤m+n a b)

b<+ : ∀ a b → b < suc (a + b)
b<+ a b = s≤s (m≤n+m b a)

abc-a : ∀ a b c → a < suc (a + b + c)
abc-a a b c = <-≤-trans (a<+ a b) (s≤s (m≤m+n (a + b) c))

abc-b : ∀ a b c → b < suc (a + b + c)
abc-b a b c = <-≤-trans (b<+ a b) (s≤s (m≤m+n (a + b) c))

abc-c : ∀ a b c → c < suc (a + b + c)
abc-c a b c = b<+ (a + b) c

abcd-a : ∀ a b c d → a < suc (a + b + c + d)
abcd-a a b c d = <-≤-trans (abc-a a b c) (s≤s (m≤m+n (a + b + c) d))

abcd-b : ∀ a b c d → b < suc (a + b + c + d)
abcd-b a b c d = <-≤-trans (abc-b a b c) (s≤s (m≤m+n (a + b + c) d))

abcd-c : ∀ a b c d → c < suc (a + b + c + d)
abcd-c a b c d = <-≤-trans (abc-c a b c) (s≤s (m≤m+n (a + b + c) d))

abcd-d : ∀ a b c d → d < suc (a + b + c + d)
abcd-d a b c d = b<+ (a + b + c) d

-- `suc (a + b)` is the size of a λ whose domain has size `a` and whose
-- body has size `b`. The body is smaller than any bound that λ sits under.
under : ∀ a b {n} → suc (a + b) < n → b < n
under a b p = <-trans (b<+ a b) p

here< : ∀ {ℓ b} (t : Tm ℓ) (ts : List (Tm ℓ)) → sumSize (t ∷ ts) < b → size t < b
here< t ts p = ≤-<-trans (m≤m+n (size t) (sumSize ts)) p

rest< : ∀ {ℓ b} (t : Tm ℓ) (ts : List (Tm ℓ)) → sumSize (t ∷ ts) < b → sumSize ts < b
rest< t ts p = ≤-<-trans (m≤n+m (sumSize ts) (size t)) p

------------------------------------------------------------------------
-- Names. de Bruijn 0 is the head of the list. A `gone` entry is an erased
-- λ-binder; using it is c:erased. An erased constructor field is `live`
-- at `opaqueL` instead, so a use is `Var`.
------------------------------------------------------------------------

data Entry : Set where
  live : String → Layout → Entry
  gone : Entry

ICtx : Set
ICtx = List Entry

lookupIx : ICtx → ℕ → Result Entry
lookupIx []       _       = fail "c:unsupported"
lookupIx (e ∷ _)  zero    = ok e
lookupIx (_ ∷ es) (suc i) = lookupIx es i

fresh : ICtx → String
fresh ctx = "b" <> show (length ctx)

hard : ∀ {A : Set} → Result A → Result A
hard (ok x)   = ok x
hard (fail _) = fail "c:unsupported"

isZero : ∀ {n} → Tm n → Bool
isZero (var i) = toℕ i ≡ᵇ 0
isZero _       = false

------------------------------------------------------------------------
-- Layouts. `app` peels to the head. A Π is an unknown layout: a use of a higher-order
-- value is c:lambda, not a layout. Machine formers are c:machine. A ν that
-- is not `ν X. A × X` is c:stream; that one shape is `streamL`.
------------------------------------------------------------------------

layoutOf : Sig → ∀ {n} → Tm n → Result Layout
layoutOf _ (var _) = ok opaqueL
layoutOf _ typ = ok opaqueL
layoutOf _ (pi _ _ _) = ok opaqueL
layoutOf _ (lam _ _ _) = fail "c:unsupported"
layoutOf σ (app f _) = layoutOf σ f
layoutOf _ nat = ok natL
layoutOf _ ze = fail "c:unsupported"
layoutOf _ (su _) = fail "c:unsupported"
layoutOf _ unit = ok unitL
layoutOf _ one = fail "c:unsupported"
layoutOf _ empty = ok opaqueL
layoutOf σ (dty i) with hard (lookupData σ i)
... | fail e = fail e
... | ok d = ok (dataL (DataDecl.dname d))
layoutOf _ (ctor _ _) = fail "c:unsupported"
layoutOf _ (mData _ _ _) = fail "c:unsupported"
layoutOf _ (mNat _ _ _ _) = fail "c:unsupported"
layoutOf _ (mEmp _ _) = fail "c:unsupported"
layoutOf _ (mUnit _ _ _) = fail "c:unsupported"
layoutOf _ (idt _ _ _) = ok opaqueL
layoutOf _ rfl = fail "c:unsupported"
layoutOf σ (rwt _ _ t) = layoutOf σ t
layoutOf _ (def _) = ok opaqueL
layoutOf σ (ann e _) = layoutOf σ e
layoutOf σ (prod A B) = pairL <$> layoutOf σ A ⊛ layoutOf σ B
layoutOf _ (pair _ _) = fail "c:unsupported"
layoutOf _ (letp _ _) = fail "c:unsupported"
layoutOf σ (nu (prod A arg)) =
  if isZero arg then streamL <$> layoutOf σ A else fail "c:stream"
layoutOf _ (nu _) = fail "c:stream"
layoutOf _ (unf _ _) = fail "c:unsupported"
layoutOf _ (ucons _) = fail "c:unsupported"
layoutOf _ i64 = fail "c:machine"
layoutOf _ f32ty = fail "c:machine"
layoutOf _ (tensor _ _) = fail "c:machine"
layoutOf _ (addi _ _) = fail "c:machine"
layoutOf _ (muli _ _) = fail "c:machine"
layoutOf _ (addt _ _) = fail "c:machine"
layoutOf _ (toi64 _) = fail "c:machine"
layoutOf _ (packi _ _) = fail "c:machine"

-- `var 0` in a motive is the scrutinee. Any other motive is a layout.
motiveLay : Sig → ∀ {n} → Tm (suc n) → Layout → Result Layout
motiveLay σ t scr = if isZero t then ok scr else layoutOf σ t

pairHalves : Layout → Layout × Layout
pairHalves (pairL a b) = a , b
pairHalves _           = opaqueL , opaqueL

unconsLay : Layout → Layout
unconsLay (streamL s) = pairL opaqueL (streamL s)
unconsLay _           = pairL opaqueL opaqueL

findData : Sig → String → Result DataDecl
findData σ name = go (Sig.datas σ)
  where
  go : List DataDecl → Result DataDecl
  go []       = fail "c:unsupported"
  go (d ∷ ds) = if DataDecl.dname d == name then ok d else go ds

dataKey : Layout → Result String
dataKey (dataL name) = ok name
dataKey _            = fail "c:unsupported"

------------------------------------------------------------------------
-- Side table of live fields. Erased fields are omitted. Names are lost
-- with de Bruijn, so a live field is `f` plus its position among live fields.
------------------------------------------------------------------------

record LiveField : Set where
  constructor liveF
  field
    lname : String
    llay : Layout

record CtorShape : Set where
  constructor cshape
  field
    sname : String
    sfields : List LiveField

fieldsOf : Sig → ℕ → ∀ {n} → Tm n → Result (List LiveField)
fieldsOf σ i (pi q A B) with eqQty q erased
... | true = fieldsOf σ i B
... | false with layoutOf σ A
... | fail e = fail e
... | ok lay with fieldsOf σ (suc i) B
... | fail e = fail e
... | ok fs = ok (liveF ("f" <> show i) lay ∷ fs)
fieldsOf _ _ _ = ok []

shapeCtor : Sig → ℕ → String → ∀ {n} → Tm n → Result CtorShape
shapeCtor σ (suc k) name (pi _ _ B) = shapeCtor σ k name B
shapeCtor _ (suc _) _ _ = fail "c:unsupported"
shapeCtor σ zero name ty = fieldsOf σ 0 ty >>= λ fs → ok (cshape name fs)

ctorShapes : Sig → ℕ → Result (String × List CtorShape)
ctorShapes σ i with hard (lookupData σ i)
... | fail e = fail e
... | ok d = go (nparams d) (DataDecl.ctors d) >>= λ cs → ok (DataDecl.dname d , cs)
  where
  go : ℕ → List Ctor → Result (List CtorShape)
  go _ [] = ok []
  go np (c ∷ cs) with shapeCtor σ np (Ctor.cname c) (Ctor.ctype c)
  ... | fail e = fail e
  ... | ok s with go np cs
  ... | fail e = fail e
  ... | ok ss = ok (s ∷ ss)

------------------------------------------------------------------------
-- Free de Bruijn indices, then the ones that escape one binder.
------------------------------------------------------------------------

outers : List ℕ → List ℕ
outers []           = []
outers (zero ∷ xs)  = outers xs
outers (suc i ∷ xs) = i ∷ outers xs

mutual
  freeIdxs : ∀ {n} → Tm n → List ℕ
  freeIdxs (var i)        = toℕ i ∷ []
  freeIdxs typ            = []
  freeIdxs (pi _ A B)     = freeIdxs A ++ outers (freeIdxs B)
  freeIdxs (lam _ A t)    = freeIdxs A ++ outers (freeIdxs t)
  freeIdxs (app f a)      = freeIdxs f ++ freeIdxs a
  freeIdxs nat            = []
  freeIdxs ze             = []
  freeIdxs (su t)         = freeIdxs t
  freeIdxs unit           = []
  freeIdxs one            = []
  freeIdxs empty          = []
  freeIdxs (dty _)        = []
  freeIdxs (ctor _ _)     = []
  freeIdxs (mData e P bs) = freeIdxs e ++ outers (freeIdxs P) ++ freeList bs
  freeIdxs (mNat e P z s) = freeIdxs e ++ outers (freeIdxs P) ++ freeIdxs z ++ outers (freeIdxs s)
  freeIdxs (mEmp e P)     = freeIdxs e ++ outers (freeIdxs P)
  freeIdxs (mUnit e P u)  = freeIdxs e ++ outers (freeIdxs P) ++ freeIdxs u
  freeIdxs (idt A x y)    = freeIdxs A ++ freeIdxs x ++ freeIdxs y
  freeIdxs rfl            = []
  freeIdxs (rwt e P t)    = freeIdxs e ++ outers (freeIdxs P) ++ freeIdxs t
  freeIdxs (def _)        = []
  freeIdxs (ann e A)      = freeIdxs e ++ freeIdxs A
  freeIdxs (prod A B)     = freeIdxs A ++ freeIdxs B
  freeIdxs (pair a b)     = freeIdxs a ++ freeIdxs b
  freeIdxs (letp e t)     = freeIdxs e ++ outers (outers (freeIdxs t))
  freeIdxs (nu F)         = outers (freeIdxs F)
  freeIdxs (unf s f)      = freeIdxs s ++ freeIdxs f
  freeIdxs (ucons s)      = freeIdxs s
  freeIdxs i64            = []
  freeIdxs f32ty          = []
  freeIdxs (tensor d s)   = freeIdxs d ++ freeIdxs s
  freeIdxs (addi x y)     = freeIdxs x ++ freeIdxs y
  freeIdxs (muli x y)     = freeIdxs x ++ freeIdxs y
  freeIdxs (addt t u)     = freeIdxs t ++ freeIdxs u
  freeIdxs (toi64 t)      = freeIdxs t
  freeIdxs (packi x y)    = freeIdxs x ++ freeIdxs y

  freeList : ∀ {n} → List (Tm n) → List ℕ
  freeList []       = []
  freeList (t ∷ ts) = freeIdxs t ++ freeList ts

elem : ℕ → List ℕ → Bool
elem _ []       = false
elem x (y ∷ ys) = if x ≡ᵇ y then true else elem x ys

uniq : List ℕ → List ℕ
uniq = go []
  where
  go : List ℕ → List ℕ → List ℕ
  go _ [] = []
  go seen (x ∷ xs) = if elem x seen then go seen xs else x ∷ go (x ∷ seen) xs

------------------------------------------------------------------------
-- Match arms. Skip the data parameters, then one λ per field. An erased
-- field is omitted from the binder list and wrapped as `Let x opaqueL Ze`
-- after the body is elaborated, so a use is `Var`.
------------------------------------------------------------------------

data Wrap : Set where
  wLive : String → Wrap
  wGone : String → Wrap

data Opened (bound : ℕ) : Set where
  opened : ∀ {ℓ} (ws : List Wrap) (body : Tm ℓ) (sp : size body < bound) (ctx : ICtx) → Opened bound

data Prep (bound : ℕ) : Set where
  mkPrep : String → Opened bound → Prep bound

data SArg (bound : ℕ) : Set where
  sarg : ∀ {ℓ} (t : Tm ℓ) (sp : size t < bound) (ctx : ICtx) → SArg bound

dropTo : ∀ {n} → ℕ → Tm n → Result (Σ ℕ (λ n' → Tm n'))
dropTo {n} zero t = ok (n , t)
dropTo (suc k) (pi _ _ B) = dropTo k B
dropTo (suc _) _ = fail "c:unsupported"

peelFields : Sig → (bound : ℕ) → ∀ {nc nb} (ty : Tm nc) (br : Tm nb) → size br < bound → ICtx → List Wrap → Result (Opened bound)
peelFields σ bound (pi q A B) (lam _ dom body) sp ctx ws with eqQty q erased
... | true =
  peelFields σ bound B body (under (size dom) (size body) sp)
    (live (fresh ctx) opaqueL ∷ ctx) (ws ++ (wGone (fresh ctx) ∷ []))
... | false with layoutOf σ A
... | fail e = fail e
... | ok lay =
  peelFields σ bound B body (under (size dom) (size body) sp)
    (live (fresh ctx) lay ∷ ctx) (ws ++ (wLive (fresh ctx) ∷ []))
peelFields _ _ (pi _ _ _) _ _ _ _ = fail "c:unsupported"
peelFields _ _ _ br sp ctx ws = ok (opened ws br sp ctx)

prepAll : Sig → (bound : ℕ) → ℕ → List Ctor → ∀ {ℓ} (bs : List (Tm ℓ)) → sumSize bs < bound → ICtx → Result (List (Prep bound))
prepAll _ _ _ [] [] _ _ = ok []
prepAll σ bound np (c ∷ cs) (b ∷ bs) sp ctx with dropTo np (Ctor.ctype c)
... | fail e = fail e
... | ok (_ , ty) with peelFields σ bound ty b (here< b bs sp) ctx []
... | fail e = fail e
... | ok op with prepAll σ bound np cs bs (rest< b bs sp) ctx
... | fail e = fail e
... | ok rest = ok (mkPrep (Ctor.cname c) op ∷ rest)
prepAll _ _ _ _ _ _ _ = fail "c:unsupported"

wrapTerm : List Wrap → Term → List String × Term
wrapTerm [] tm = [] , tm
wrapTerm (wLive x ∷ ws) tm =
  let (ns , tm') = wrapTerm ws tm
  in x ∷ ns , tm'
wrapTerm (wGone x ∷ ws) tm =
  let (ns , tm') = wrapTerm ws tm
  in ns , Let x opaqueL Ze tm'

------------------------------------------------------------------------
-- Stream captures. Index 0 of the step body is the seed.
------------------------------------------------------------------------

Cap : Set
Cap = String × Layout × Term

capγ : List ℕ → ICtx → List Cap
capγ [] _ = []
capγ (i ∷ is) ctx with lookupIx ctx i
... | ok (live name lay) = (name , lay , Var name) ∷ capγ is ctx
... | _ = capγ is ctx

capParams : List Cap → List (String × Layout)
capParams [] = []
capParams ((name , lay , _) ∷ xs) = (name , lay) ∷ capParams xs

capTerms : List Cap → List (String × Term)
capTerms [] = []
capTerms ((name , _ , tm) ∷ xs) = (name , tm) ∷ capTerms xs

seedCtx : Qty → String → Layout → ICtx → ICtx
seedCtx q x lay ctx = if eqQty q erased then gone ∷ ctx else live x lay ∷ ctx

seedParam : Qty → String → Layout → List (String × Layout)
seedParam q x lay = if eqQty q erased then [] else (x , lay) ∷ []

-- A head that is already a refusal, applied or not.
badHead : ∀ {n} → Tm n → Maybe String
badHead i64 = just "c:machine"
badHead f32ty = just "c:machine"
badHead (tensor _ _) = just "c:machine"
badHead (addi _ _) = just "c:machine"
badHead (muli _ _) = just "c:machine"
badHead (addt _ _) = just "c:machine"
badHead (toi64 _) = just "c:machine"
badHead (packi _ _) = just "c:machine"
badHead (nu _) = just "c:stream"
badHead _ = nothing

------------------------------------------------------------------------
-- Elaboration.
------------------------------------------------------------------------

Elab : ℕ → Set
Elab m = ∀ {ℓ} (t : Tm ℓ) → size t ≡ m → Sig → ℕ → ICtx → Result (E × ℕ)

Rec : ℕ → Set
Rec n = ∀ {m} → m < n → Elab m

call : ∀ {n} → Rec n → Sig → ∀ {ℓ} (t : Tm ℓ) → size t < n → ICtx → ℕ → Result (E × ℕ)
call ih σ t sp ctx k = ih sp t refl σ k ctx

zipLive : ∀ {n} → Rec n → Sig → ∀ {ℓ} → Tm ℓ → List (SArg n) → ℕ → Result (List Term × List Fun × ℕ × Layout)
zipLive ih σ (pi q _ B) (sarg t sp ctxa ∷ as) k with eqQty q erased
... | true = zipLive ih σ B as k
... | false with call ih σ t sp ctxa k
... | fail e = fail e
... | ok (mkE tm _ ss , k1) with zipLive ih σ B as k1
... | fail e = fail e
... | ok (ts , ss2 , k2 , lay) = ok (tm ∷ ts , ss ++ ss2 , k2 , lay)
zipLive _ _ (pi _ _ _) [] _ = fail "c:lambda"
zipLive _ σ ty [] k with layoutOf σ ty
... | fail e = fail e
... | ok lay = ok ([] , [] , k , lay)
zipLive _ _ _ (_ ∷ _) _ = fail "c:lambda"

finishDef : ∀ {n} → Rec n → Sig → ℕ → List (SArg n) → ℕ → Result (E × ℕ)
finishDef ih σ i args k with hard (lookupDef σ i)
... | fail e = fail e
... | ok d with eqMode (Def.dmode d) run
... | false = fail "c:unsupported"
... | true with zipLive ih σ (Def.dtype d) args k
... | fail e = fail e
... | ok (ts , ss , k' , lay) = ok (mkE (Call (Def.dname d) ts) lay ss , k')

finishCtor : ∀ {n} → Rec n → Sig → ℕ → ℕ → List (SArg n) → ℕ → Result (E × ℕ)
finishCtor ih σ di ci args k with hard (lookupData σ di)
... | fail e = fail e
... | ok d with hard (lookupCtor d ci)
... | fail e = fail e
... | ok c with dropTo (nparams d) (Ctor.ctype c)
... | fail e = fail e
... | ok (_ , rest) with zipLive ih σ rest args k
... | fail e = fail e
... | ok (ts , ss , k' , _) =
  ok (mkE (Con (DataDecl.dname d) (Ctor.cname c) ts) (dataL (DataDecl.dname d)) ss , k')

-- Spine arguments are stored with the context they were written in.
-- A λ consumes one. Its body is elaborated in the extended context.
-- Arguments that were already on the spine keep the context they carry,
-- which is the context outside that λ.
applyTo : ∀ {n} → Rec n → Sig → ∀ {ℓ} (t : Tm ℓ) → size t < n → List (SArg n) → ICtx → ℕ → Result (E × ℕ)
applyTo ih σ t sp [] ctx k = call ih σ t sp ctx k
applyTo ih σ (app f a) sp (s ∷ rest) ctx k =
  applyTo ih σ f (<-trans (a<+ (size f) (size a)) sp)
    (sarg a (<-trans (b<+ (size f) (size a)) sp) ctx ∷ s ∷ rest) ctx k
applyTo ih σ (ann e A) sp (s ∷ rest) ctx k =
  applyTo ih σ e (<-trans (a<+ (size e) (size A)) sp) (s ∷ rest) ctx k
applyTo ih σ (rwt eq mot body) sp (s ∷ rest) ctx k =
  applyTo ih σ body (<-trans (abc-c (size eq) (size mot) (size body)) sp) (s ∷ rest) ctx k
applyTo ih σ (lam q A body) sp (sarg t pt ctxa ∷ rest) ctx k with eqQty q erased
... | true =
  applyTo ih σ body (under (size A) (size body) sp) rest (gone ∷ ctx) k
... | false with layoutOf σ A
... | fail e = fail e
... | ok lay with call ih σ t pt ctxa k
... | fail e = fail e
... | ok (mkE atm _ ss , k1) with
    applyTo ih σ body (under (size A) (size body) sp) rest (live (fresh ctx) lay ∷ ctx) k1
... | fail e = fail e
... | ok (mkE btm blay ss2 , k2) =
  ok (mkE (Let (fresh ctx) lay atm btm) blay (ss ++ ss2) , k2)
applyTo ih σ (def i) _ (s ∷ rest) _ k = finishDef ih σ i (s ∷ rest) k
applyTo ih σ (ctor di ci) _ (s ∷ rest) _ k = finishCtor ih σ di ci (s ∷ rest) k
applyTo _ _ t _ (_ ∷ _) _ _ with badHead t
... | just e = fail e
... | nothing = fail "c:lambda"

elabPreps : ∀ {n} → Rec n → Sig → List (Prep n) → ℕ → Result (List Arm × List Fun × ℕ)
elabPreps _ _ [] k = ok ([] , [] , k)
elabPreps ih σ (mkPrep cname (opened ws body sp ctx) ∷ ps) k with call ih σ body sp ctx k
... | fail e = fail e
... | ok (mkE tm _ ss , k1) with elabPreps ih σ ps k1
... | fail e = fail e
... | ok (arms , ss2 , k2) =
  let (ns , tm') = wrapTerm ws tm
  in ok (arm cname ns tm' ∷ arms , ss ++ ss2 , k2)

step : ∀ n → Rec n → Elab n
step n ih t eq σ k ctx = go t eq
  where
  go : ∀ {ℓ} (u : Tm ℓ) → size u ≡ n → Result (E × ℕ)
  go (var i) refl with lookupIx ctx (toℕ i)
  ... | ok (live name lay) = ok (mkE (Var name) lay [] , k)
  ... | ok gone = fail "c:erased"
  ... | fail e = fail e
  go typ refl = fail "c:unsupported"
  go (pi _ _ _) refl = fail "c:unsupported"
  go (lam _ _ _) refl = fail "c:lambda"
  go (app f a) refl =
    applyTo ih σ f (a<+ (size f) (size a))
      (sarg a (b<+ (size f) (size a)) ctx ∷ []) ctx k
  go nat refl = fail "c:unsupported"
  go ze refl = ok (mkE Ze natL [] , k)
  go (su u) refl with call ih σ u (s≤s ≤-refl) ctx k
  ... | fail e = fail e
  ... | ok (mkE tm _ ss , k1) = ok (mkE (Su tm) natL ss , k1)
  go unit refl = fail "c:unsupported"
  go one refl = ok (mkE Tt unitL [] , k)
  go empty refl = fail "c:unsupported"
  go (dty _) refl = fail "c:unsupported"
  go (ctor di ci) refl = finishCtor ih σ di ci [] k
  go (mData e mot bs) refl with call ih σ e (abc-a (size e) (size mot) (sumSize bs)) ctx k
  ... | fail e' = fail e'
  ... | ok (mkE etm elay ess , k1) with dataKey elay
  ... | fail e' = fail e'
  ... | ok dname with findData σ dname
  ... | fail e' = fail e'
  ... | ok d with length (DataDecl.ctors d) ≡ᵇ 0
  ... | true = fail "c:unsupported"
  ... | false with length (DataDecl.ctors d) ≡ᵇ length bs
  ... | false = fail "c:unsupported"
  ... | true with prepAll σ n (nparams d) (DataDecl.ctors d) bs (abc-c (size e) (size mot) (sumSize bs)) ctx
  ... | fail e' = fail e'
  ... | ok preps with elabPreps ih σ preps k1
  ... | fail e' = fail e'
  ... | ok (arms , ss , k2) with motiveLay σ mot elay
  ... | fail e' = fail e'
  ... | ok rlay = ok (mkE (Match etm arms) rlay (ess ++ ss) , k2)
  -- The suc arm is already `Tm (suc n)`. Index 0 is the predecessor.
  -- A λ in that position is a value, and a value λ is c:lambda.
  go (mNat e mot z s) refl with call ih σ e (abcd-a (size e) (size mot) (size z) (size s)) ctx k
  ... | fail e' = fail e'
  ... | ok (mkE etm elay ess , k1) with call ih σ z (abcd-c (size e) (size mot) (size z) (size s)) ctx k1
  ... | fail e' = fail e'
  ... | ok (mkE ztm _ zss , k2) with call ih σ s (abcd-d (size e) (size mot) (size z) (size s)) (live (fresh ctx) natL ∷ ctx) k2
  ... | fail e' = fail e'
  ... | ok (mkE stm _ sss , k3) with motiveLay σ mot elay
  ... | fail e' = fail e'
  ... | ok rlay =
    ok (mkE (Match etm (arm "zero" [] ztm ∷ arm "suc" (fresh ctx ∷ []) stm ∷ [])) rlay
          (ess ++ zss ++ sss) , k3)
  go (mEmp e mot) refl with call ih σ e (a<+ (size e) (size mot)) ctx k
  ... | fail e' = fail e'
  ... | ok (mkE etm elay ess , k1) with motiveLay σ mot elay
  ... | fail e' = fail e'
  ... | ok rlay = ok (mkE (Let (fresh ctx) elay etm Abort) rlay ess , k1)
  go (mUnit e mot u) refl with call ih σ e (abc-a (size e) (size mot) (size u)) ctx k
  ... | fail e' = fail e'
  ... | ok (mkE etm _ ess , k1) with call ih σ u (abc-c (size e) (size mot) (size u)) ctx k1
  ... | fail e' = fail e'
  ... | ok (mkE utm ulay uss , k2) =
    ok (mkE (Let (fresh ctx) unitL etm utm) ulay (ess ++ uss) , k2)
  go (idt _ _ _) refl = fail "c:unsupported"
  go rfl refl = fail "c:unsupported"
  go (rwt eq mot body) refl = call ih σ body (abc-c (size eq) (size mot) (size body)) ctx k
  go (def i) refl = finishDef ih σ i [] k
  go (ann e A) refl = call ih σ e (a<+ (size e) (size A)) ctx k
  go (prod _ _) refl = fail "c:unsupported"
  go (pair a b) refl with call ih σ a (a<+ (size a) (size b)) ctx k
  ... | fail e = fail e
  ... | ok (mkE ta la sa , k1) with call ih σ b (b<+ (size a) (size b)) ctx k1
  ... | fail e = fail e
  ... | ok (mkE tb lb sb , k2) = ok (mkE (Pair ta tb) (pairL la lb) (sa ++ sb) , k2)
  go (letp e body) refl with call ih σ e (a<+ (size e) (size body)) ctx k
  ... | fail e' = fail e'
  ... | ok (mkE etm elay ess , k1) =
    let (la , lb) = pairHalves elay
        xa = fresh ctx
        xb = fresh (live xa la ∷ ctx)
    in bindBody xa xb la lb etm ess k1
    where
    bindBody : String → String → Layout → Layout → Term → List Fun → ℕ → Result (E × ℕ)
    bindBody xa xb la lb etm ess k1 with
      call ih σ body (b<+ (size e) (size body)) (live xb lb ∷ live xa la ∷ ctx) k1
    ... | fail e' = fail e'
    ... | ok (mkE btm blay bss , k2) =
      ok (mkE (Letp xa xb etm btm) blay (ess ++ bss) , k2)
  go (nu _) refl = fail "c:stream"
  go (unf seed (lam q dom body)) refl with call ih σ seed (a<+ (size seed) (size (lam q dom body))) ctx k
  ... | fail e = fail e
  ... | ok (mkE stm _ sss , k1) with layoutOf σ dom
  ... | fail e = fail e
  ... | ok dlay =
    let x = fresh ctx
        caps = capγ (uniq (outers (freeIdxs body))) ctx
        psp = under (size dom) (size body) (b<+ (size seed) (size (lam q dom body)))
    in closeStep k1 x dlay q caps stm sss body psp
    where
    closeStep : ℕ → String → Layout → Qty → List Cap → Term → List Fun → ∀ {ℓ} (body : Tm ℓ) → size body < n → Result (E × ℕ)
    closeStep id x dlay q caps stm sss body psp with
      call ih σ body psp (seedCtx q x dlay ctx) (suc id)
    ... | fail e = fail e
    ... | ok (mkE btm blay bss , k2) =
      let stepName = "step" <> show id
          stepf = fn stepName false (capParams caps ++ seedParam q x dlay) blay btm
      in ok (mkE (Stream stm (capTerms caps) stepName) (streamL dlay)
               (sss ++ bss ++ (stepf ∷ [])) , k2)
  go (unf _ _) refl = fail "c:lambda"
  go (ucons s) refl with call ih σ s (s≤s ≤-refl) ctx k
  ... | fail e = fail e
  ... | ok (mkE tm lay ss , k1) = ok (mkE (Uncons tm) (unconsLay lay) ss , k1)
  go i64 refl = fail "c:machine"
  go f32ty refl = fail "c:machine"
  go (tensor _ _) refl = fail "c:machine"
  go (addi _ _) refl = fail "c:machine"
  go (muli _ _) refl = fail "c:machine"
  go (addt _ _) refl = fail "c:machine"
  go (toi64 _) refl = fail "c:machine"
  go (packi _ _) refl = fail "c:machine"

elaborate : Sig → ℕ → ICtx → ∀ {ℓ} → Tm ℓ → Result (E × ℕ)
elaborate σ k ctx t = <-rec Elab step (size t) t refl σ k ctx

------------------------------------------------------------------------
-- A run definition. Supplied names are the live parameters, in order.
-- An erased Π is `gone` and is not a parameter. Fewer λs than Πs is
-- c:unsupported. Agda's `Def` has no export bit; the flag is an argument.
-- Generated step functions are returned beside the function.
------------------------------------------------------------------------

takeName : List String → ICtx → String × List String
takeName [] ctx = fresh ctx , []
takeName (s ∷ ss) _ = s , ss

peel : Sig → ICtx → List String → List (String × Layout) → ∀ {ℓ} → Tm ℓ → Tm ℓ
     → Result (List (String × Layout) × ICtx × Σ ℕ (λ ℓ' → Tm ℓ') × Layout)
peel σ ctx names acc (pi q A B) (lam q' _ body) with eqQty q erased ∨ eqQty q' erased
... | true = peel σ (gone ∷ ctx) names acc B body
... | false with layoutOf σ A
... | fail e = fail e
... | ok lay =
  let (x , names') = takeName names ctx
  in peel σ (live x lay ∷ ctx) names' (acc ++ ((x , lay) ∷ [])) B body
peel _ _ _ _ (pi _ _ _) _ = fail "c:unsupported"
peel σ ctx _ acc {ℓ} ty body with layoutOf σ ty
... | fail e = fail e
... | ok lay = ok (acc , ctx , (ℓ , body) , lay)

elabFun : Sig → ℕ → Bool → String → List String → Tm 0 → Tm 0 → Result (Fun × List Fun × ℕ)
elabFun σ k exp name names ty body with peel σ [] names [] ty body
... | fail e = fail e
... | ok (ps , ctx , (_ , inner) , ret) with elaborate σ k ctx inner
... | fail e = fail e
... | ok (mkE tm _ ss , k') = ok (fn name exp ps ret tm , ss , k')

elabRuns : Sig → Result (List Fun)
elabRuns σ = go 0 (Sig.defs σ)
  where
  go : ℕ → List Def → Result (List Fun)
  go _ [] = ok []
  go k (d ∷ ds) with eqMode (Def.dmode d) run
  ... | false = go k ds
  ... | true with elabFun σ k true (Def.dname d) [] (Def.dtype d) (Def.dbody d)
  ... | fail e = fail e
  ... | ok (f , ss , k') with go k' ds
  ... | fail e = fail e
  ... | ok fs = ok (f ∷ (ss ++ fs))

termOf : Result (E × ℕ) → Result Term
termOf (ok (mkE tm _ _ , _)) = ok tm
termOf (fail e) = fail e

------------------------------------------------------------------------
-- Agreement. Each `refl` is the elaboration computing to that image.
-- `atom` and `matom` are `ctor` and `mData`; the equations are definitional.
------------------------------------------------------------------------

atom-is-ctor : ∀ {n} → atom {n} 0 ≡ ctor {n} 0 0
atom-is-ctor = refl

matom-is-match : ∀ {n} → matom {n} ≡ mData {n}
matom-is-match = refl

ascDesc : List String
ascDesc = "asc" ∷ "desc" ∷ []

atomSig : Sig
atomSig = mkSig (atomDecl 0 ascDesc ∷ []) []

atom-shape : ctorShapes atomSig 0 ≡ ok ("Atom" , cshape "asc" [] ∷ cshape "desc" [] ∷ [])
atom-shape = refl

atom-elab : termOf (elaborate atomSig 0 [] {0} (atom {0} 0)) ≡ ok (atomCon ascDesc F.zero)
atom-elab = refl

atom-match : termOf (elaborate atomSig 0 [] {0} (matom {0} (atom {0} 0) nat (ze ∷ su ze ∷ [])))
           ≡ ok (Match (Con "Atom" "asc" []) (arm "asc" [] Ze ∷ arm "desc" [] (Su Ze) ∷ []))
atom-match = refl

atom-oob : elaborate atomSig 0 [] {0} (ctor {0} 0 2) ≡ fail "c:unsupported"
atom-oob = refl

plusTy : Tm 0
plusTy = pi affine nat (pi affine nat nat)

-- The suc arm is open at `Tm 3`. Variable 0 is the predecessor.
plusBody : Tm 0
plusBody =
  lam affine nat
    (lam affine nat
      (mNat (var (F.suc (F.zero {0}))) nat
        (var (F.zero {1}))
        (su (app (app (def 0) (var (F.zero {2}))) (var (F.suc {2} (F.zero {1})))))))

plusIR : Term
plusIR =
  Match (Var "n")
    ( arm "zero" [] (Var "m")
    ∷ arm "suc" ("b2" ∷ []) (Su (Call "plus" (Var "b2" ∷ Var "m" ∷ [])))
    ∷ [])

plusSig : Sig
plusSig = fromDefs (mkDef "plus" run plusTy plusBody ∷ [])

plus-elab : elabFun plusSig 0 true "plus" ("n" ∷ "m" ∷ []) plusTy plusBody
          ≡ ok ( fn "plus" true (("n" , natL) ∷ ("m" , natL) ∷ []) natL plusIR
               , []
               , 0)
plus-elab = refl

plus-value : elaborate plusSig 0 [] {0} (def {0} 0) ≡ fail "c:lambda"
plus-value = refl

let-elab : termOf (elaborate (fromDefs []) 0 [] {0} (app (lam affine nat (su (var (F.zero {0})))) ze))
         ≡ ok (Let "b0" natL Ze (Su (Var "b0")))
let-elab = refl

erased-drop : termOf (elaborate (fromDefs []) 0 [] {0} (app (lam erased nat ze) (su ze))) ≡ ok Ze
erased-drop = refl

erased-skips-machine : termOf (elaborate (fromDefs []) 0 [] {0} (app (lam erased nat ze) (addi ze ze))) ≡ ok Ze
erased-skips-machine = refl

erased-use : elaborate (fromDefs []) 0 [] {0} (app (lam erased nat (var (F.zero {0}))) ze) ≡ fail "c:erased"
erased-use = refl

bare-lam : elaborate (fromDefs []) 0 [] {0} (lam affine nat ze) ≡ fail "c:lambda"
bare-lam = refl

addi-refused : elaborate (fromDefs []) 0 [] {0} (addi ze ze) ≡ fail "c:machine"
addi-refused = refl

nu-refused : elaborate (fromDefs []) 0 [] {0} (nu nat) ≡ fail "c:stream"
nu-refused = refl

zerosTm : Tm 0
zerosTm = unf ze (lam affine nat (pair ze ze))

zeros-elab : elaborate (fromDefs []) 0 [] zerosTm
           ≡ ok ( mkE (Stream Ze [] "step0") (streamL natL)
                    (fn "step0" false (("b0" , natL) ∷ []) (pairL natL natL) (Pair Ze Ze) ∷ [])
                , 1)
zeros-elab = refl

stream-layout : layoutOf (fromDefs []) {0} (stream {0} nat) ≡ ok (streamL natL)
stream-layout = refl

spec-skip : elabRuns (fromDefs (mkDef "ghost" spec ze ze ∷ [])) ≡ ok []
spec-skip = refl

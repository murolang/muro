------------------------------------------------------------------------
-- Temporal layer. One linear-time formula of one buffered meeting,
-- decided on the meeting's compiled graph.
--
-- A run is an infinite sequence of configurations. A finished
-- configuration stutters: it steps to itself, so one coinductive
-- definition covers the finite maximal runs as well. `always`,
-- `eventually`, and `leads_to` are read on those runs.
--
-- The meeting derivation is an argument (`NoStuck`). This module does
-- not search the meeting again. Nothing here is added to Tm.
--
-- The surface sugar `always (P implies eventually Q)` is `P leads_to Q`.
-- `Holds` of `leadsTo` is □(p → ◇q) by the definition below.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal where

open import Data.Bool.Base using (Bool; true; false; not; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map; filterᵇ; length)
open import Data.List.Relation.Unary.Any using (Any; here)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; inspect; [_])
open import Relation.Binary.PropositionalEquality.Properties using (trans-reflʳ)
open import Relation.Nullary.Decidable.Core using (Dec)
  renaming (yes to yes′; no to no′)

open import Muro.Base using (Mode; evid; run)

open import Muro.AsyncRec
  using ( Atom; aNat; aBit; aCon
        ; Block; bDone; bStop; bPut; bEcho; bGrow; bGet; bPick0; bPick1
        ; bCover; bIget; bMget
        ; Tok; pay; lab
        ; RConf; rc; Graph; gr
        ; Act; AWait; ABad; AGo
        ; init; lt; nth; nthA; lookB; onL; onR
        ; reactL; reactR; halted; isHalt
        ; View; VFinal; VBad; VGo; view; kidsV; localB; idle; onIdle; merge
        ; Shape; sh-final; sh-step; shapeOf
        ; ilOf; irOf; l2rOf; r2lOf; elOf; erOf
        ; Reach; rhere; rstep
        )
open Graph

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- Which side moved. `fin` is the stutter at a finished configuration.
------------------------------------------------------------------------

data Who : Set where
  lside rside fin : Who

who≟ : (x y : Who) → Dec (x ≡ y)
who≟ lside lside = yes′ refl
who≟ lside rside = no′ (λ ())
who≟ lside fin = no′ (λ ())
who≟ rside lside = no′ (λ ())
who≟ rside rside = yes′ refl
who≟ rside fin = no′ (λ ())
who≟ fin lside = no′ (λ ())
who≟ fin rside = no′ (λ ())
who≟ fin fin = yes′ refl

------------------------------------------------------------------------
-- A state proposition, after names have been resolved to block indices,
-- slot indices, and literals. No temporal operator occurs here.
------------------------------------------------------------------------

data Role : Set where
  left right : Role

data Verb : Set where
  v-put v-get v-pick0 v-pick1 v-cover : Verb

data Lit : Set where
  l-nat : ℕ → Lit
  l-bit : Bool → Lit
  l-con : String → Lit
  l-pick0 l-pick1 : Lit

data StateProp : Set where
  sp-true sp-false : StateProp
  sp-not : StateProp → StateProp
  sp-and sp-or sp-imp : StateProp → StateProp → StateProp
  sp-done sp-stopped : Role → StateProp
  sp-at : Role → ℕ → Verb → StateProp
  sp-eq : Role → ℕ → Lit → StateProp
  sp-lt sp-le : Role → ℕ → ℕ → StateProp
  sp-is : Role → ℕ → String → StateProp
  sp-eq2 : Role → ℕ → Role → ℕ → StateProp
  sp-bound : Role → ℕ → StateProp
  sp-empty sp-full : Role → StateProp
  sp-head : Role → Lit → StateProp

data Formula : Set where
  always : StateProp → Formula
  eventually : StateProp → Formula
  leadsTo : StateProp → StateProp → Formula

------------------------------------------------------------------------
-- One step of the meeting. Left, then right, the order `merge` uses.
-- `finish` is the stutter: both queues empty and both blocks halted.
------------------------------------------------------------------------

data Step (g : Graph) : RConf → Who → RConf → Set where
  stepL : ∀ {c d} → reactL g c ≡ AGo d → Step g c lside d
  stepR : ∀ {c d} → reactR g c ≡ AGo d → Step g c rside d
  finish : ∀ {c} → l2rOf c ≡ [] → r2lOf c ≡ [] → halted g c ≡ true →
           Step g c fin c

------------------------------------------------------------------------
-- Boolean reading of a resolved proposition. Total on every configuration.
------------------------------------------------------------------------

verb≡ : Verb → Verb → Bool
verb≡ v-put v-put = true
verb≡ v-get v-get = true
verb≡ v-pick0 v-pick0 = true
verb≡ v-pick1 v-pick1 = true
verb≡ v-cover v-cover = true
verb≡ _ _ = false

verbOf : Block → Maybe Verb
verbOf bDone = nothing
verbOf bStop = nothing
verbOf (bPut _ _) = just v-put
verbOf (bEcho _ _) = just v-put
verbOf (bGrow _ _) = just v-put
verbOf (bGet _ _ _) = just v-get
verbOf (bPick0 _) = just v-pick0
verbOf (bPick1 _) = just v-pick1
verbOf (bCover _ _) = just v-cover
verbOf (bIget _ _ _) = just v-get
verbOf (bMget _ _ _) = just v-get

emptyQ : {A : Set} → List A → Bool
emptyQ [] = true
emptyQ (_ ∷ _) = false

orB : Bool → Bool → Bool
orB true _ = true
orB false b = b

codeOf : Graph → Role → List Block
codeOf g left = codeL g
codeOf g right = codeR g

ptrOf : Role → RConf → ℕ
ptrOf left c = ilOf c
ptrOf right c = irOf c

slotsOf : Role → RConf → List ℕ
slotsOf left c = elOf c
slotsOf right c = erOf c

-- The inbox of a role is the queue the other role has filled.
inboxOf : Role → RConf → List Tok
inboxOf left c = r2lOf c
inboxOf right c = l2rOf c

blockAt : Graph → Role → RConf → Maybe Block
blockAt g role c = lookB (codeOf g role) (ptrOf role c)

isDoneB : Maybe Block → Bool
isDoneB (just bDone) = true
isDoneB _ = false

isStopB : Maybe Block → Bool
isStopB (just bStop) = true
isStopB _ = false

matchLit : List Atom → ℕ → Lit → Bool
matchLit as k (l-nat n) with nthA as k
... | just (aNat m) = m ≡ᵇ n
... | _ = false
matchLit as k (l-bit false) with nthA as k
... | just (aBit false) = true
... | _ = false
matchLit as k (l-bit true) with nthA as k
... | just (aBit true) = true
... | _ = false
matchLit as k (l-con s) with nthA as k
... | just (aCon t) = t == s
... | _ = false
matchLit _ _ l-pick0 = false
matchLit _ _ l-pick1 = false

matchTok : List Atom → Tok → Lit → Bool
matchTok as (pay k) lit = matchLit as k lit
matchTok _ (lab false) l-pick0 = true
matchTok _ (lab true) l-pick1 = true
matchTok _ (lab _) _ = false

atomNat : List Atom → ℕ → Maybe ℕ
atomNat as k with nthA as k
... | just (aNat n) = just n
... | _ = nothing

natHeld : List Atom → List ℕ → ℕ → Maybe ℕ
natHeld as env i with nth env i
... | just (suc k) = atomNat as k
... | just zero = nothing
... | nothing = nothing

isCon : List Atom → ℕ → String → Bool
isCon as k name with nthA as k
... | just (aCon s) = s == name
... | _ = false

bound? : List ℕ → ℕ → Bool
bound? env i with nth env i
... | just (suc _) = true
... | _ = false

sameSlot : List ℕ → ℕ → List ℕ → ℕ → Bool
sameSlot e1 i e2 j with nth e1 i | nth e2 j
... | just (suc k) | just (suc m) = k ≡ᵇ m
... | _ | _ = false

at? : Graph → Role → ℕ → Verb → RConf → Bool
at? g role i verb c with ptrOf role c ≡ᵇ i | blockAt g role c
... | true | just b with verbOf b
... | just w = verb≡ w verb
... | nothing = false
at? _ _ _ _ _ | _ | _ = false

head? : List Atom → List Tok → Lit → Bool
head? _ [] _ = false
head? as (t ∷ _) lit = matchTok as t lit

full? : Graph → List Tok → Bool
full? g q = not (lt (length q) (cap g))

⟦_⟧ : Graph → StateProp → RConf → Bool
⟦_⟧ _ sp-true _ = true
⟦_⟧ _ sp-false _ = false
⟦_⟧ g (sp-not p) c = not (⟦_⟧ g p c)
⟦_⟧ g (sp-and p q) c = ⟦_⟧ g p c ∧ ⟦_⟧ g q c
⟦_⟧ g (sp-or p q) c = orB (⟦_⟧ g p c) (⟦_⟧ g q c)
⟦_⟧ g (sp-imp p q) c = orB (not (⟦_⟧ g p c)) (⟦_⟧ g q c)
⟦_⟧ g (sp-done role) c = isDoneB (blockAt g role c)
⟦_⟧ g (sp-stopped role) c = isStopB (blockAt g role c)
⟦_⟧ g (sp-at role i verb) c = at? g role i verb c
⟦_⟧ g (sp-eq role i lit) c with nth (slotsOf role c) i
... | just (suc k) = matchLit (alpha g) k lit
... | _ = false
⟦_⟧ g (sp-lt role i n) c with natHeld (alpha g) (slotsOf role c) i
... | just m = lt m n
... | nothing = false
⟦_⟧ g (sp-le role i n) c with natHeld (alpha g) (slotsOf role c) i
... | just m = not (lt n m)
... | nothing = false
⟦_⟧ g (sp-is role i name) c with nth (slotsOf role c) i
... | just (suc k) = isCon (alpha g) k name
... | just zero = false
... | nothing = false
⟦_⟧ _ (sp-eq2 r1 i r2 j) c = sameSlot (slotsOf r1 c) i (slotsOf r2 c) j
⟦_⟧ _ (sp-bound role i) c = bound? (slotsOf role c) i
⟦_⟧ _ (sp-empty role) c = emptyQ (inboxOf role c)
⟦_⟧ g (sp-full role) c = full? g (inboxOf role c)
⟦_⟧ g (sp-head role lit) c = head? (alpha g) (inboxOf role c) lit

------------------------------------------------------------------------
-- Infinite runs.
------------------------------------------------------------------------

record Path : Set where
  coinductive
  field
    head : RConf
    tail : Path

open Path public

record IsRun (g : Graph) (π : Path) : Set where
  coinductive
  field
    step : Σ Who (λ w → Step g (head π) w (head (tail π)))
    rest : IsRun g (tail π)

open IsRun public

record Globally (P : Path → Set) (π : Path) : Set where
  coinductive
  field
    now : P π
    later : Globally P (tail π)

open Globally public

data Eventually (P : Path → Set) : Path → Set where
  hereE : ∀ {π} → P π → Eventually P π
  thereE : ∀ {π} → Eventually P (tail π) → Eventually P π

Holds : Graph → Formula → Path → Set
Holds g (always p) = Globally (λ σ → ⟦ g ⟧ p (head σ) ≡ true)
Holds g (eventually p) = Eventually (λ σ → ⟦ g ⟧ p (head σ) ≡ true)
Holds g (leadsTo p q) =
  Globally (λ σ → ⟦ g ⟧ p (head σ) ≡ true →
                  Eventually (λ τ → ⟦ g ⟧ q (head τ) ≡ true) σ)

Satisfies : Graph → Formula → Set
Satisfies g φ = ∀ π → head π ≡ init g → IsRun g π → Holds g φ π

-- Every configuration reachable from the start is final or has a step.
-- This is the meeting derivation, passed in, not searched for here.
NoStuck : Graph → Set
NoStuck g = ∀ {c} → Reach g (init g) c → Shape (view g c)

TemporalOk : (g : Graph) → NoStuck g → Formula → Set
TemporalOk g _ φ = Satisfies g φ

------------------------------------------------------------------------
-- The wall. A temporal derivation is evidence. A run term has no seat.
------------------------------------------------------------------------

data Seat : Mode → Set where
  temporal : ∀ {g φ} (m : NoStuck g) → TemporalOk g m φ → Seat evid

no-run : ¬ Seat run
no-run ()

------------------------------------------------------------------------
-- Edges. Left successor, then right successor, then the stutter.
-- `real` drops the stutter, which is the only `fin` edge.
------------------------------------------------------------------------

keep : Who × RConf → Bool
keep (fin , _) = false
keep (lside , _) = true
keep (rside , _) = true

real : List (Who × RConf) → List RConf
real xs = map proj₂ (filterᵇ keep xs)

fromL : Act → List (Who × RConf)
fromL (AGo d) = (lside , d) ∷ []
fromL AWait = []
fromL (ABad _) = []

fromR : Act → List (Who × RConf)
fromR (AGo d) = (rside , d) ∷ []
fromR AWait = []
fromR (ABad _) = []

isFinalB : Graph → RConf → Bool
isFinalB g c = emptyQ (l2rOf c) ∧ emptyQ (r2lOf c) ∧ halted g c

stutterB : RConf → Bool → List (Who × RConf)
stutterB c true = (fin , c) ∷ []
stutterB c false = []

stutter : Graph → RConf → List (Who × RConf)
stutter g c = stutterB c (isFinalB g c)

edges : Graph → RConf → List (Who × RConf)
edges g c = fromL (reactL g c) ++ fromR (reactR g c) ++ stutter g c

real-++ : ∀ xs ys → real (xs ++ ys) ≡ real xs ++ real ys
real-++ [] ys = refl
real-++ ((fin , _) ∷ xs) ys = real-++ xs ys
real-++ ((lside , _) ∷ xs) ys = cong (_∷_ _) (real-++ xs ys)
real-++ ((rside , _) ∷ xs) ys = cong (_∷_ _) (real-++ xs ys)

filter-stutter : ∀ g c → filterᵇ keep (stutter g c) ≡ []
filter-stutter g c = no-fin (isFinalB g c)
  where
  no-fin : (b : Bool) → filterᵇ keep (stutterB c b) ≡ []
  no-fin true = refl
  no-fin false = refl

real-stutter : ∀ g c → real (stutter g c) ≡ []
real-stutter g c rewrite filter-stutter g c = refl

on-haltL : ∀ {g c} (b : Block) → isHalt b ≡ true → onL g c b ≡ AWait
on-haltL bDone refl = refl
on-haltL bStop refl = refl
on-haltL (bPut _ _) ()
on-haltL (bEcho _ _) ()
on-haltL (bGrow _ _) ()
on-haltL (bGet _ _ _) ()
on-haltL (bPick0 _) ()
on-haltL (bPick1 _) ()
on-haltL (bCover _ _) ()
on-haltL (bIget _ _ _) ()
on-haltL (bMget _ _ _) ()

on-haltR : ∀ {g c} (b : Block) → isHalt b ≡ true → onR g c b ≡ AWait
on-haltR bDone refl = refl
on-haltR bStop refl = refl
on-haltR (bPut _ _) ()
on-haltR (bEcho _ _) ()
on-haltR (bGrow _ _) ()
on-haltR (bGet _ _ _) ()
on-haltR (bPick0 _) ()
on-haltR (bPick1 _) ()
on-haltR (bCover _ _) ()
on-haltR (bIget _ _ _) ()
on-haltR (bMget _ _ _) ()

look-waitL : ∀ {g il ir q1 q2 e1 e2 b} →
  lookB (codeL g) il ≡ just b → isHalt b ≡ true →
  reactL g (rc il ir q1 q2 e1 e2) ≡ AWait
look-waitL {b = b} eq hb rewrite eq = on-haltL b hb

look-waitR : ∀ {g il ir q1 q2 e1 e2 b} →
  lookB (codeR g) ir ≡ just b → isHalt b ≡ true →
  reactR g (rc il ir q1 q2 e1 e2) ≡ AWait
look-waitR {b = b} eq hb rewrite eq = on-haltR b hb

true≢false : ¬ (true ≡ false)
true≢false ()

∧-left : ∀ {a b} → a ∧ b ≡ true → a ≡ true
∧-left {true} _ = refl
∧-left {false} ()

∧-right : ∀ {a b} → a ∧ b ≡ true → b ≡ true
∧-right {true} eq = eq
∧-right {false} ()

-- Both blocks are halted, so neither side can step. The lookup results
-- are arguments, not a `with`, so a caller can rewrite them.
react-halt : ∀ {g c} → halted g c ≡ true →
             reactL g c ≡ AWait × reactR g c ≡ AWait
react-halt {g} {rc il ir q1 q2 e1 e2} h =
  go (lookB (codeL g) il) (lookB (codeR g) ir) refl refl
  where
  c = rc il ir q1 q2 e1 e2
  deadL : ∀ {bl} (mr : Maybe Block) → isHalt bl ≡ false →
          lookB (codeL g) il ≡ just bl → lookB (codeR g) ir ≡ mr → ⊥
  deadL (just _) nb eqL eqR rewrite eqL | eqR | nb = true≢false (sym h)
  deadL nothing nb eqL eqR rewrite eqL | eqR = true≢false (sym h)
  deadDone : ∀ {br} → isHalt br ≡ false →
             lookB (codeL g) il ≡ just bDone → lookB (codeR g) ir ≡ just br → ⊥
  deadDone nb eqL eqR rewrite eqL | eqR | nb = true≢false (sym h)
  deadStop : ∀ {br} → isHalt br ≡ false →
             lookB (codeL g) il ≡ just bStop → lookB (codeR g) ir ≡ just br → ⊥
  deadStop nb eqL eqR rewrite eqL | eqR | nb = true≢false (sym h)
  go : (ml mr : Maybe Block) →
       lookB (codeL g) il ≡ ml → lookB (codeR g) ir ≡ mr →
       reactL g c ≡ AWait × reactR g c ≡ AWait
  go nothing (just _) eqL eqR rewrite eqL | eqR = ⊥-elim (true≢false (sym h))
  go nothing nothing eqL eqR rewrite eqL | eqR = ⊥-elim (true≢false (sym h))
  go (just bl) mr eqL eqR = onbl bl mr eqL eqR
    where
    onbl : (bl : Block) (mr : Maybe Block) →
           lookB (codeL g) il ≡ just bl → lookB (codeR g) ir ≡ mr →
           reactL g c ≡ AWait × reactR g c ≡ AWait
    onbl bDone (just bDone) eqL eqR rewrite eqL | eqR = refl , refl
    onbl bDone (just bStop) eqL eqR rewrite eqL | eqR = refl , refl
    onbl bStop (just bDone) eqL eqR rewrite eqL | eqR = refl , refl
    onbl bStop (just bStop) eqL eqR rewrite eqL | eqR = refl , refl
    onbl bDone nothing eqL eqR rewrite eqL | eqR = ⊥-elim (true≢false (sym h))
    onbl bStop nothing eqL eqR rewrite eqL | eqR = ⊥-elim (true≢false (sym h))
    onbl bDone (just (bPut _ _)) eqL eqR = ⊥-elim (deadDone refl eqL eqR)
    onbl bDone (just (bEcho _ _)) eqL eqR = ⊥-elim (deadDone refl eqL eqR)
    onbl bDone (just (bGrow _ _)) eqL eqR = ⊥-elim (deadDone refl eqL eqR)
    onbl bDone (just (bGet _ _ _)) eqL eqR = ⊥-elim (deadDone refl eqL eqR)
    onbl bDone (just (bPick0 _)) eqL eqR = ⊥-elim (deadDone refl eqL eqR)
    onbl bDone (just (bPick1 _)) eqL eqR = ⊥-elim (deadDone refl eqL eqR)
    onbl bDone (just (bCover _ _)) eqL eqR = ⊥-elim (deadDone refl eqL eqR)
    onbl bDone (just (bIget _ _ _)) eqL eqR = ⊥-elim (deadDone refl eqL eqR)
    onbl bDone (just (bMget _ _ _)) eqL eqR = ⊥-elim (deadDone refl eqL eqR)
    onbl bStop (just (bPut _ _)) eqL eqR = ⊥-elim (deadStop refl eqL eqR)
    onbl bStop (just (bEcho _ _)) eqL eqR = ⊥-elim (deadStop refl eqL eqR)
    onbl bStop (just (bGrow _ _)) eqL eqR = ⊥-elim (deadStop refl eqL eqR)
    onbl bStop (just (bGet _ _ _)) eqL eqR = ⊥-elim (deadStop refl eqL eqR)
    onbl bStop (just (bPick0 _)) eqL eqR = ⊥-elim (deadStop refl eqL eqR)
    onbl bStop (just (bPick1 _)) eqL eqR = ⊥-elim (deadStop refl eqL eqR)
    onbl bStop (just (bCover _ _)) eqL eqR = ⊥-elim (deadStop refl eqL eqR)
    onbl bStop (just (bIget _ _ _)) eqL eqR = ⊥-elim (deadStop refl eqL eqR)
    onbl bStop (just (bMget _ _ _)) eqL eqR = ⊥-elim (deadStop refl eqL eqR)
    onbl (bPut _ _) mr eqL eqR = ⊥-elim (deadL mr refl eqL eqR)
    onbl (bEcho _ _) mr eqL eqR = ⊥-elim (deadL mr refl eqL eqR)
    onbl (bGrow _ _) mr eqL eqR = ⊥-elim (deadL mr refl eqL eqR)
    onbl (bGet _ _ _) mr eqL eqR = ⊥-elim (deadL mr refl eqL eqR)
    onbl (bPick0 _) mr eqL eqR = ⊥-elim (deadL mr refl eqL eqR)
    onbl (bPick1 _) mr eqL eqR = ⊥-elim (deadL mr refl eqL eqR)
    onbl (bCover _ _) mr eqL eqR = ⊥-elim (deadL mr refl eqL eqR)
    onbl (bIget _ _ _) mr eqL eqR = ⊥-elim (deadL mr refl eqL eqR)
    onbl (bMget _ _ _) mr eqL eqR = ⊥-elim (deadL mr refl eqL eqR)

-- `onIdle` returns `VFinal` as soon as its boolean argument is `true`.
-- Matching the three variable equalities is J, so the queues and the
-- halted bit become `[]`, `[]` and `true` without rewriting under `view`.
onIdle-eq : ∀ {g c lq rq hz}
          → (eqL : l2rOf c ≡ lq) (eqR : r2lOf c ≡ rq) (eqH : halted g c ≡ hz)
          → (a : lq ≡ []) (b : rq ≡ []) (t : hz ≡ true)
          → onIdle g c lq rq hz eqL eqR eqH ≡
            VFinal (trans eqL a) (trans eqR b) (trans eqH t)
onIdle-eq eqL eqR eqH refl refl refl
  rewrite trans-reflʳ eqL | trans-reflʳ eqR | trans-reflʳ eqH = refl

idle-final : ∀ {g c} (a : l2rOf c ≡ []) (b : r2lOf c ≡ [])
             (h : halted g c ≡ true) →
             idle g c ≡ VFinal a b h
idle-final a b h = onIdle-eq refl refl refl a b h

view-wait : ∀ {g c} → reactL g c ≡ AWait → reactR g c ≡ AWait →
            view g c ≡ idle g c
view-wait eqL eqR rewrite eqL | eqR = refl

view-final : ∀ {g c} (a : l2rOf c ≡ []) (b : r2lOf c ≡ [])
             (h : halted g c ≡ true) →
             view g c ≡ VFinal a b h
view-final {g} {c} a b h =
  trans (view-wait {g} {c} (proj₁ (react-halt {g} {c} h)) (proj₂ (react-halt {g} {c} h)))
        (idle-final a b h)

final-only : ∀ {g c d} → Step g c fin d →
             ∃ λ (a : l2rOf c ≡ []) → ∃ λ (b : r2lOf c ≡ []) →
             ∃ λ (h : halted g c ≡ true) → view g c ≡ VFinal a b h × d ≡ c
final-only (finish a b h) = a , b , h , view-final a b h , refl

-- An `AGo` step is not a finished configuration. A nonempty queue makes
-- `isFinalB` false outright. Both queues empty leaves `isFinalB` equal
-- to `halted`, and a halted configuration cannot `AGo`.
goL-not-final : ∀ {g c d} → reactL g c ≡ AGo d → isFinalB g c ≡ false
goL-not-final {g} {rc il ir (_ ∷ _) _ _ _} eq = refl
goL-not-final {g} {rc il ir [] (_ ∷ _) _ _} eq = refl
goL-not-final {g} {rc il ir [] [] e1 e2} {d} eq = body (halted g c) refl
  where
  c : RConf
  c = rc il ir [] [] e1 e2
  ago≢wait : AGo d ≡ AWait → ⊥
  ago≢wait ()
  contra : reactL g c ≡ AGo d → halted g c ≡ true → ⊥
  contra e h = ago≢wait (trans (sym e) (proj₁ (react-halt {g} {c} h)))
  body : (z : Bool) → halted g c ≡ z → halted g c ≡ false
  body false hz = hz
  body true hz = ⊥-elim (contra eq hz)

goR-not-final : ∀ {g c d} → reactR g c ≡ AGo d → isFinalB g c ≡ false
goR-not-final {g} {rc il ir (_ ∷ _) _ _ _} eq = refl
goR-not-final {g} {rc il ir [] (_ ∷ _) _ _} eq = refl
goR-not-final {g} {rc il ir [] [] e1 e2} {d} eq = body (halted g c) refl
  where
  c : RConf
  c = rc il ir [] [] e1 e2
  ago≢wait : AGo d ≡ AWait → ⊥
  ago≢wait ()
  contra : reactR g c ≡ AGo d → halted g c ≡ true → ⊥
  contra e h = ago≢wait (trans (sym e) (proj₂ (react-halt {g} {c} h)))
  body : (z : Bool) → halted g c ≡ z → halted g c ≡ false
  body false hz = hz
  body true hz = ⊥-elim (contra eq hz)

-- A local view's successors are the non-stutter edges, in `merge`'s order.
edges-kids : ∀ {g c} → localB (view g c) ≡ true →
             real (edges g c) ≡ kidsV (view g c)
edges-kids {g} {c} eq
  with reactL g c | inspect (reactL g) c
     | reactR g c | inspect (reactR g) c
edges-kids eq | ABad _ | [ _ ] | _ | [ _ ] = ⊥-elim (true≢false (sym eq))
edges-kids eq | AGo _ | [ _ ] | ABad _ | [ _ ] = ⊥-elim (true≢false (sym eq))
edges-kids eq | AWait | [ _ ] | ABad _ | [ _ ] = ⊥-elim (true≢false (sym eq))
edges-kids {g} {c} eq | AGo d | [ eqL ] | AGo e | [ _ ] =
  subst (λ b → real (fromL (AGo d) ++ fromR (AGo e) ++ stutterB c b) ≡ d ∷ e ∷ [])
        (sym (goL-not-final {g} {c} {d} eqL)) refl
edges-kids {g} {c} eq | AGo d | [ eqL ] | AWait | [ _ ] =
  subst (λ b → real (fromL (AGo d) ++ fromR AWait ++ stutterB c b) ≡ d ∷ [])
        (sym (goL-not-final {g} {c} {d} eqL)) refl
edges-kids {g} {c} eq | AWait | [ _ ] | AGo e | [ eqR ] =
  subst (λ b → real (fromL AWait ++ fromR (AGo e) ++ stutterB c b) ≡ e ∷ [])
        (sym (goR-not-final {g} {c} {e} eqR)) refl
edges-kids {g} {c} eq | AWait | [ _ ] | AWait | [ _ ] = both-wait eq
  where
  kids-idle : (lq rq : List Tok) (hz : Bool)
            → (e1 : l2rOf c ≡ lq) (e2 : r2lOf c ≡ rq) (e3 : halted g c ≡ hz)
            → localB (onIdle g c lq rq hz e1 e2 e3) ≡ true
            → kidsV (onIdle g c lq rq hz e1 e2 e3) ≡ []
  kids-idle [] [] true _ _ _ _ = refl
  kids-idle [] [] false _ _ _ ()
  kids-idle [] (_ ∷ _) true _ _ _ ()
  kids-idle [] (_ ∷ _) false _ _ _ ()
  kids-idle (_ ∷ _) [] true _ _ _ ()
  kids-idle (_ ∷ _) [] false _ _ _ ()
  kids-idle (_ ∷ _) (_ ∷ _) true _ _ _ ()
  kids-idle (_ ∷ _) (_ ∷ _) false _ _ _ ()
  both-wait : localB (idle g c) ≡ true →
              real (stutter g c) ≡ kidsV (idle g c)
  both-wait eqW =
    trans (real-stutter g c)
          (sym (kids-idle (l2rOf c) (r2lOf c) (halted g c) refl refl refl eqW))

------------------------------------------------------------------------
-- From a reachable configuration of a meeting with no deadlock there
-- is an infinite run. A final configuration stutters. Any other local
-- view contributes its first successor, which `edges-kids` places first.
------------------------------------------------------------------------

firstStep : ∀ {g c k ks} → view g c ≡ VGo k ks →
            Σ Who (λ w → Step g c w k)
firstStep {g} {c} {k} {ks} eqv =
  go (reactL g c) (reactR g c) refl refl eqv
  where
  go : (la ra : Act) → reactL g c ≡ la → reactR g c ≡ ra →
       view g c ≡ VGo k ks → Σ Who (λ w → Step g c w k)
  go (AGo d) (AGo e) eqL eqR eqv rewrite eqL | eqR with eqv
  ... | refl = lside , stepL eqL
  go (AGo d) AWait eqL eqR eqv rewrite eqL | eqR with eqv
  ... | refl = lside , stepL eqL
  go AWait (AGo e) eqL eqR eqv rewrite eqL | eqR with eqv
  ... | refl = rside , stepR eqR
  go (ABad _) _ eqL eqR eqv rewrite eqL = ⊥-elim (bad eqv)
    where bad : VBad _ ≡ VGo k ks → ⊥
          bad ()
  go (AGo _) (ABad _) eqL eqR eqv rewrite eqL | eqR = ⊥-elim (bad eqv)
    where bad : VBad _ ≡ VGo k ks → ⊥
          bad ()
  go AWait (ABad _) eqL eqR eqv rewrite eqL | eqR = ⊥-elim (bad eqv)
    where bad : VBad _ ≡ VGo k ks → ⊥
          bad ()
  go AWait AWait eqL eqR eqv rewrite eqL | eqR =
    ⊥-elim (not-go (l2rOf c) (r2lOf c) (halted g c) refl refl refl eqv)
    where
    not-go : (lq rq : List Tok) (hz : Bool)
           → (e1 : l2rOf c ≡ lq) (e2 : r2lOf c ≡ rq) (e3 : halted g c ≡ hz)
           → onIdle g c lq rq hz e1 e2 e3 ≡ VGo k ks → ⊥
    not-go [] [] true _ _ _ ()
    not-go [] [] false _ _ _ ()
    not-go [] (_ ∷ _) true _ _ _ ()
    not-go [] (_ ∷ _) false _ _ _ ()
    not-go (_ ∷ _) [] true _ _ _ ()
    not-go (_ ∷ _) [] false _ _ _ ()
    not-go (_ ∷ _) (_ ∷ _) true _ _ _ ()
    not-go (_ ∷ _) (_ ∷ _) false _ _ _ ()

-- Append one view-step to a path from the start. `Reach` is built from
-- the start, so the new step goes on the end.
snocR : ∀ {g a c d} → Reach g a c → Any (_≡_ d) (kidsV (view g c)) →
        Reach g a d
snocR rhere step = rstep step rhere
snocR (rstep earlier later) step = rstep earlier (snocR later step)

-- One successor of a shaped view: the stutter at a final configuration,
-- or the first child `view` lists. `v ≡ view g c` lets the child witness
-- be moved onto `kidsV (view g c)`.
move : ∀ {g c} (v : View g c) → v ≡ view g c → Shape v →
       Reach g (init g) c →
       Σ RConf (λ d → Reach g (init g) d × Σ Who (λ w → Step g c w d))
move {c = c} (VFinal a b h) _ sh-final r = c , r , fin , finish a b h
move (VGo k ks) eq sh-step r =
  k , snocR r (subst (λ v → Any (_≡_ k) (kidsV v)) eq (here refl))
  , firstStep (sym eq)
move (VBad _) _ ()

runPath : ∀ {g c} (m : NoStuck g) → Reach g (init g) c → Path
runIs : ∀ {g c} (m : NoStuck g) (r : Reach g (init g) c) →
        IsRun g (runPath m r)

head (runPath {c = c} m r) = c
tail (runPath {g} {c} m r) with move (view g c) refl (m r) r
... | d , r′ , _ , _ = runPath m r′

step (runIs {g} {c} m r) with move (view g c) refl (m r) r
... | _ , _ , w , s = w , s
rest (runIs {g} {c} m r) with move (view g c) refl (m r) r
... | d , r′ , _ , _ = runIs m r′

run-exists : ∀ {g c} → NoStuck g → Reach g (init g) c →
             Σ Path (λ π → head π ≡ c × IsRun g π)
run-exists {c = c} m r = runPath m r , refl , runIs m r

------------------------------------------------------------------------
-- Counterexamples. `finite` is a shortest path on which `always` fails.
-- `lasso` is a stem from the start to a trigger, a walk to a repeat,
-- and a non-empty cycle, all inside the region that avoids the goal.
-- One data type, because the two forms are the same refusal.
------------------------------------------------------------------------

data Cex : Set where
  finite : List (Who × RConf) → Cex
  lasso  : (to-c stem loop : List (Who × RConf)) → Cex

data Answer : Set where
  yes : Answer
  no  : Cex → Answer

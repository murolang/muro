------------------------------------------------------------------------
-- Source processes of a buffered meeting.
--
-- `SProc` is `Muro.Session.Proc` (done, stop, put, get, pick0, pick1,
-- cover, iget, mget) plus `smu` and `svar`, the repetition forms.
-- `inj` sends a finite process here. A payload outside this layer
-- (a pair, a record, a vector, a fielded constructor, a computed
-- put, unit, a nullary constructor that does not inhabit its
-- declaration) is `pOut`, `sout`, or `abad`. A bare `mget` arm has
-- no constructor name, and an arm list that is not the declaration's
-- constructors in order is `sout`: the graph matches the name, so
-- those forms are not the injected process.
--
-- A step is one side's action. A jump is not its own step: unfolding
-- `smu` / `svar` is part of the action, and the continuation index is
-- the one `walk` computes the same way compilation numbers blocks.
-- A configuration whose queues are empty and whose two processes have
-- unfolded to done or stop stutters.
--
-- `abs` projects the block pointers, the queues, and the slots. It is
-- total. The correspondence with a compiled graph is stated in
-- `Muro.Temporal.Bridge` for the start configuration.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Source where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Muro.AsyncRec
  using ( Atom; aNat; aBit; aCon
        ; Tag; tagNat; tagBit; tagDat
        ; Tok; pay; lab
        ; RConf; rc
        ; setNth; findA; nthA; fits; conOf; elemS; slotVal
        )

import Muro.Session as S

------------------------------------------------------------------------
-- Payloads and processes.
------------------------------------------------------------------------

data Pay : Set where
  pNat : ℕ → Pay
  pBit : Bool → Pay
  pCon : String → Pay
  pEcho : String → Pay
  pOut : Pay

data SProc : Set
data Arm : Set

data Arm where
  aok : String → SProc → Arm
  abad : Arm

data SProc where
  sdone sstop sout : SProc
  sput : Pay → SProc → SProc
  sget : Tag → String → SProc → SProc
  spick0 spick1 : SProc → SProc
  scover : SProc → SProc → SProc
  siget : String → SProc → SProc → SProc
  smget : Tag → String → List Arm → SProc
  smu : String → SProc → SProc
  svar : String → SProc

------------------------------------------------------------------------
-- Where a process starts, and the counters just after it.
-- `entry` and `atSlot` are the block and the slot counter of the
-- first block. `next` and `slotN` are the counters compile would
-- return after the process. A jump uses the block and the slot the
-- binder was given, and it allocates nothing.
------------------------------------------------------------------------

record W : Set where
  constructor mkW
  field
    entry atSlot next slotN : ℕ

open W

EnvI : Set
EnvI = List (String × ℕ × ℕ)

EnvP : Set
EnvP = List (String × SProc)

addPend : List String → ℕ → ℕ → EnvI → EnvI
addPend [] _ _ ρ = ρ
addPend (x ∷ xs) n s ρ = (x , n , s) ∷ addPend xs n s ρ

lookupI : String → EnvI → Maybe (ℕ × ℕ)
lookupI _ [] = nothing
lookupI x ((y , i , s) ∷ rest) with x == y
... | true = just (i , s)
... | false = lookupI x rest

mutual
  walk : List String → EnvI → SProc → ℕ → ℕ → Maybe W
  walk pend ρ (smu x p) n s = walk (x ∷ pend) ρ p n s
  walk pend ρ (svar y) n s with elemS y pend
  ... | true = nothing
  ... | false with lookupI y ρ
  ... | nothing = nothing
  ... | just (i , s0) = just (mkW i s0 n s)
  walk _ _ sdone n s = just (mkW n s (suc n) s)
  walk _ _ sstop n s = just (mkW n s (suc n) s)
  walk _ _ sout _ _ = nothing
  walk pend ρ (sput _ p) n s with walk [] (addPend pend n s ρ) p (suc n) s
  ... | nothing = nothing
  ... | just w = just (mkW n s (next w) (slotN w))
  walk pend ρ (sget _ _ p) n s with walk [] (addPend pend n s ρ) p (suc n) (suc s)
  ... | nothing = nothing
  ... | just w = just (mkW n s (next w) (slotN w))
  walk pend ρ (spick0 p) n s with walk [] (addPend pend n s ρ) p (suc n) s
  ... | nothing = nothing
  ... | just w = just (mkW n s (next w) (slotN w))
  walk pend ρ (spick1 p) n s with walk [] (addPend pend n s ρ) p (suc n) s
  ... | nothing = nothing
  ... | just w = just (mkW n s (next w) (slotN w))
  walk pend ρ (scover p q) n s with walk [] (addPend pend n s ρ) p (suc n) s
  ... | nothing = nothing
  ... | just w1 with walk [] (addPend pend n s ρ) q (next w1) (slotN w1)
  ... | nothing = nothing
  ... | just w2 = just (mkW n s (next w2) (slotN w2))
  walk pend ρ (siget _ p q) n s with walk [] (addPend pend n s ρ) p (suc n) (suc s)
  ... | nothing = nothing
  ... | just w1 with walk [] (addPend pend n s ρ) q (next w1) (slotN w1)
  ... | nothing = nothing
  ... | just w2 = just (mkW n s (next w2) (slotN w2))
  walk pend ρ (smget _ _ as) n s with walkArms [] (addPend pend n s ρ) as (suc n) (suc s)
  ... | nothing = nothing
  ... | just (_ , n2 , s2) = just (mkW n s n2 s2)

  walkArms : List String → EnvI → List Arm → ℕ → ℕ → Maybe (List (String × W) × ℕ × ℕ)
  walkArms _ _ [] n s = just ([] , n , s)
  walkArms _ _ (abad ∷ _) _ _ = nothing
  walkArms pend ρ (aok y p ∷ as) n s with walk pend ρ p n s
  ... | nothing = nothing
  ... | just w with walkArms pend ρ as (next w) (slotN w)
  ... | nothing = nothing
  ... | just (ws , n2 , s2) = just ((y , w) ∷ ws , n2 , s2)

-- The arm named `y`, compiled from counter `(n, s)` across `as`.
armGo : EnvI → String → List Arm → ℕ → ℕ → Maybe (W × SProc)
armGo _ _ [] _ _ = nothing
armGo _ _ (abad ∷ _) _ _ = nothing
armGo ρ y (aok z p ∷ as) n s with walk [] ρ p n s
... | nothing = nothing
... | just w with y == z
... | true = just (w , p)
... | false = armGo ρ y as (next w) (slotN w)

------------------------------------------------------------------------
-- Configurations. Queues hold the same tokens as a compiled
-- configuration. `namesL` / `namesR` are the binders in slot order.
-- `envP` / `envI` are the recursion binders unfolded so far.
------------------------------------------------------------------------

record SConf : Set where
  constructor sc
  field
    cap : ℕ
    alpha : List Atom
    il ir slotL slotR : ℕ
    l2r r2l : List Tok
    el er : List ℕ
    left right : SProc
    namesL namesR : List String
    envPL envPR : EnvP
    envIL envIR : EnvI

open SConf

abs : SConf → RConf
abs c = rc (il c) (ir c) (l2r c) (r2l c) (el c) (er c)

snoc : {A : Set} → List A → A → List A
snoc [] m = m ∷ []
snoc (x ∷ xs) m = x ∷ snoc xs m

findS : String → List String → Maybe ℕ
findS _ [] = nothing
findS x (y ∷ ys) with x == y
... | true = just zero
... | false with findS x ys
... | just k = just (suc k)
... | nothing = nothing

asAtom : Pay → Maybe Atom
asAtom (pNat n) = just (aNat n)
asAtom (pBit false) = just (aBit false)
asAtom (pBit true) = just (aBit true)
asAtom (pCon s) = just (aCon s)
asAtom (pEcho _) = nothing
asAtom pOut = nothing

------------------------------------------------------------------------
-- Unfolding. A `smu` binds its name and continues. A `svar` continues
-- as the process that name was bound to. Neither is a step.
------------------------------------------------------------------------

data Focus : Set where
  f-done f-stop : Focus
  f-put : Pay → SProc → Focus
  f-get : Tag → String → SProc → Focus
  f-pick0 f-pick1 : SProc → Focus
  f-cover : SProc → SProc → Focus
  f-iget : String → SProc → SProc → Focus
  f-mget : Tag → String → List Arm → Focus

data Bound (x : String) (body : SProc) : EnvP → Set where
  b-here : ∀ {ρ} → Bound x body ((x , body) ∷ ρ)
  b-there : ∀ {y q ρ} → Bound x body ρ → Bound x body ((y , q) ∷ ρ)

data Unfold (ρ : EnvP) (pend : List String) : SProc → EnvP → List String → Focus → Set where
  u-done : Unfold ρ pend sdone ρ pend f-done
  u-stop : Unfold ρ pend sstop ρ pend f-stop
  u-put : ∀ {a p} → Unfold ρ pend (sput a p) ρ pend (f-put a p)
  u-get : ∀ {t x p} → Unfold ρ pend (sget t x p) ρ pend (f-get t x p)
  u-pick0 : ∀ {p} → Unfold ρ pend (spick0 p) ρ pend (f-pick0 p)
  u-pick1 : ∀ {p} → Unfold ρ pend (spick1 p) ρ pend (f-pick1 p)
  u-cover : ∀ {p q} → Unfold ρ pend (scover p q) ρ pend (f-cover p q)
  u-iget : ∀ {x p q} → Unfold ρ pend (siget x p q) ρ pend (f-iget x p q)
  u-mget : ∀ {t x as} → Unfold ρ pend (smget t x as) ρ pend (f-mget t x as)
  u-mu : ∀ {x p ρ′ pend′ f} →
         Unfold ((x , smu x p) ∷ ρ) (x ∷ pend) p ρ′ pend′ f →
         Unfold ρ pend (smu x p) ρ′ pend′ f
  u-var : ∀ {x body ρ′ pend′ f} →
          Bound x body ρ →
          Unfold ρ pend body ρ′ pend′ f →
          Unfold ρ pend (svar x) ρ′ pend′ f

data HaltF : Focus → Set where
  h-done : HaltF f-done
  h-stop : HaltF f-stop

------------------------------------------------------------------------
-- One step. Left reads `r2l` and writes `l2r`. Right does the opposite.
------------------------------------------------------------------------

data _⟶ₛ_ : SConf → SConf → Set where
  put-l : ∀ {c a p ρ′ pend′ atom k w} →
          Unfold (envPL c) [] (left c) ρ′ pend′ (f-put a p) →
          asAtom a ≡ just atom →
          findA atom (alpha c) ≡ just k →
          length (l2r c) < cap c →
          walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p (suc (il c)) (slotL c) ≡ just w →
          c ⟶ₛ record c
            { left = p ; il = entry w ; slotL = atSlot w
            ; l2r = snoc (l2r c) (pay k)
            ; envPL = ρ′ ; envIL = addPend pend′ (il c) (slotL c) (envIL c) }
  echo-l : ∀ {c x p ρ′ pend′ i k w} →
           Unfold (envPL c) [] (left c) ρ′ pend′ (f-put (pEcho x) p) →
           findS x (namesL c) ≡ just i →
           slotVal (el c) i ≡ just k →
           length (l2r c) < cap c →
           walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p (suc (il c)) (slotL c) ≡ just w →
           c ⟶ₛ record c
             { left = p ; il = entry w ; slotL = atSlot w
             ; l2r = snoc (l2r c) (pay k)
             ; envPL = ρ′ ; envIL = addPend pend′ (il c) (slotL c) (envIL c) }
  pick0-l : ∀ {c p ρ′ pend′ w} →
            Unfold (envPL c) [] (left c) ρ′ pend′ (f-pick0 p) →
            length (l2r c) < cap c →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p (suc (il c)) (slotL c) ≡ just w →
            c ⟶ₛ record c
              { left = p ; il = entry w ; slotL = atSlot w
              ; l2r = snoc (l2r c) (lab false)
              ; envPL = ρ′ ; envIL = addPend pend′ (il c) (slotL c) (envIL c) }
  pick1-l : ∀ {c p ρ′ pend′ w} →
            Unfold (envPL c) [] (left c) ρ′ pend′ (f-pick1 p) →
            length (l2r c) < cap c →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p (suc (il c)) (slotL c) ≡ just w →
            c ⟶ₛ record c
              { left = p ; il = entry w ; slotL = atSlot w
              ; l2r = snoc (l2r c) (lab true)
              ; envPL = ρ′ ; envIL = addPend pend′ (il c) (slotL c) (envIL c) }
  get-l : ∀ {c t x p ρ′ pend′ k rest a w} →
          Unfold (envPL c) [] (left c) ρ′ pend′ (f-get t x p) →
          r2l c ≡ pay k ∷ rest →
          nthA (alpha c) k ≡ just a →
          fits t a ≡ true →
          walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p (suc (il c)) (suc (slotL c)) ≡ just w →
          c ⟶ₛ record c
            { left = p ; il = entry w ; slotL = atSlot w
            ; r2l = rest ; el = setNth (slotL c) (suc k) (el c)
            ; envPL = ρ′ ; envIL = addPend pend′ (il c) (slotL c) (envIL c) }
  cover0-l : ∀ {c p q ρ′ pend′ rest w} →
             Unfold (envPL c) [] (left c) ρ′ pend′ (f-cover p q) →
             r2l c ≡ lab false ∷ rest →
             walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p (suc (il c)) (slotL c) ≡ just w →
             c ⟶ₛ record c
               { left = p ; il = entry w ; slotL = atSlot w
               ; r2l = rest
               ; envPL = ρ′ ; envIL = addPend pend′ (il c) (slotL c) (envIL c) }
  cover1-l : ∀ {c p q ρ′ pend′ rest w1 w2} →
             Unfold (envPL c) [] (left c) ρ′ pend′ (f-cover p q) →
             r2l c ≡ lab true ∷ rest →
             walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p (suc (il c)) (slotL c) ≡ just w1 →
             walk [] (addPend pend′ (il c) (slotL c) (envIL c)) q (next w1) (slotN w1) ≡ just w2 →
             c ⟶ₛ record c
               { left = q ; il = entry w2 ; slotL = atSlot w2
               ; r2l = rest
               ; envPL = ρ′ ; envIL = addPend pend′ (il c) (slotL c) (envIL c) }
  iget0-l : ∀ {c x p q ρ′ pend′ k rest w} →
            Unfold (envPL c) [] (left c) ρ′ pend′ (f-iget x p q) →
            r2l c ≡ pay k ∷ rest →
            nthA (alpha c) k ≡ just (aBit false) →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p (suc (il c)) (suc (slotL c)) ≡ just w →
            c ⟶ₛ record c
              { left = p ; il = entry w ; slotL = atSlot w
              ; r2l = rest ; el = setNth (slotL c) (suc k) (el c)
              ; envPL = ρ′ ; envIL = addPend pend′ (il c) (slotL c) (envIL c) }
  iget1-l : ∀ {c x p q ρ′ pend′ k rest w1 w2} →
            Unfold (envPL c) [] (left c) ρ′ pend′ (f-iget x p q) →
            r2l c ≡ pay k ∷ rest →
            nthA (alpha c) k ≡ just (aBit true) →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p (suc (il c)) (suc (slotL c)) ≡ just w1 →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) q (next w1) (slotN w1) ≡ just w2 →
            c ⟶ₛ record c
              { left = q ; il = entry w2 ; slotL = atSlot w2
              ; r2l = rest ; el = setNth (slotL c) (suc k) (el c)
              ; envPL = ρ′ ; envIL = addPend pend′ (il c) (slotL c) (envIL c) }
  mget-l : ∀ {c t x as ρ′ pend′ k rest a name w p} →
           Unfold (envPL c) [] (left c) ρ′ pend′ (f-mget t x as) →
           r2l c ≡ pay k ∷ rest →
           nthA (alpha c) k ≡ just a →
           fits t a ≡ true →
           conOf a ≡ just name →
           armGo (addPend pend′ (il c) (slotL c) (envIL c)) name as (suc (il c)) (suc (slotL c)) ≡ just (w , p) →
           c ⟶ₛ record c
             { left = p ; il = entry w ; slotL = atSlot w
             ; r2l = rest ; el = setNth (slotL c) (suc k) (el c)
             ; envPL = ρ′ ; envIL = addPend pend′ (il c) (slotL c) (envIL c) }

  put-r : ∀ {c a p ρ′ pend′ atom k w} →
          Unfold (envPR c) [] (right c) ρ′ pend′ (f-put a p) →
          asAtom a ≡ just atom →
          findA atom (alpha c) ≡ just k →
          length (r2l c) < cap c →
          walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p (suc (ir c)) (slotR c) ≡ just w →
          c ⟶ₛ record c
            { right = p ; ir = entry w ; slotR = atSlot w
            ; r2l = snoc (r2l c) (pay k)
            ; envPR = ρ′ ; envIR = addPend pend′ (ir c) (slotR c) (envIR c) }
  echo-r : ∀ {c x p ρ′ pend′ i k w} →
           Unfold (envPR c) [] (right c) ρ′ pend′ (f-put (pEcho x) p) →
           findS x (namesR c) ≡ just i →
           slotVal (er c) i ≡ just k →
           length (r2l c) < cap c →
           walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p (suc (ir c)) (slotR c) ≡ just w →
           c ⟶ₛ record c
             { right = p ; ir = entry w ; slotR = atSlot w
             ; r2l = snoc (r2l c) (pay k)
             ; envPR = ρ′ ; envIR = addPend pend′ (ir c) (slotR c) (envIR c) }
  pick0-r : ∀ {c p ρ′ pend′ w} →
            Unfold (envPR c) [] (right c) ρ′ pend′ (f-pick0 p) →
            length (r2l c) < cap c →
            walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p (suc (ir c)) (slotR c) ≡ just w →
            c ⟶ₛ record c
              { right = p ; ir = entry w ; slotR = atSlot w
              ; r2l = snoc (r2l c) (lab false)
              ; envPR = ρ′ ; envIR = addPend pend′ (ir c) (slotR c) (envIR c) }
  pick1-r : ∀ {c p ρ′ pend′ w} →
            Unfold (envPR c) [] (right c) ρ′ pend′ (f-pick1 p) →
            length (r2l c) < cap c →
            walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p (suc (ir c)) (slotR c) ≡ just w →
            c ⟶ₛ record c
              { right = p ; ir = entry w ; slotR = atSlot w
              ; r2l = snoc (r2l c) (lab true)
              ; envPR = ρ′ ; envIR = addPend pend′ (ir c) (slotR c) (envIR c) }
  get-r : ∀ {c t x p ρ′ pend′ k rest a w} →
          Unfold (envPR c) [] (right c) ρ′ pend′ (f-get t x p) →
          l2r c ≡ pay k ∷ rest →
          nthA (alpha c) k ≡ just a →
          fits t a ≡ true →
          walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p (suc (ir c)) (suc (slotR c)) ≡ just w →
          c ⟶ₛ record c
            { right = p ; ir = entry w ; slotR = atSlot w
            ; l2r = rest ; er = setNth (slotR c) (suc k) (er c)
            ; envPR = ρ′ ; envIR = addPend pend′ (ir c) (slotR c) (envIR c) }
  cover0-r : ∀ {c p q ρ′ pend′ rest w} →
             Unfold (envPR c) [] (right c) ρ′ pend′ (f-cover p q) →
             l2r c ≡ lab false ∷ rest →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p (suc (ir c)) (slotR c) ≡ just w →
             c ⟶ₛ record c
               { right = p ; ir = entry w ; slotR = atSlot w
               ; l2r = rest
               ; envPR = ρ′ ; envIR = addPend pend′ (ir c) (slotR c) (envIR c) }
  cover1-r : ∀ {c p q ρ′ pend′ rest w1 w2} →
             Unfold (envPR c) [] (right c) ρ′ pend′ (f-cover p q) →
             l2r c ≡ lab true ∷ rest →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p (suc (ir c)) (slotR c) ≡ just w1 →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) q (next w1) (slotN w1) ≡ just w2 →
             c ⟶ₛ record c
               { right = q ; ir = entry w2 ; slotR = atSlot w2
               ; l2r = rest
               ; envPR = ρ′ ; envIR = addPend pend′ (ir c) (slotR c) (envIR c) }
  iget0-r : ∀ {c x p q ρ′ pend′ k rest w} →
            Unfold (envPR c) [] (right c) ρ′ pend′ (f-iget x p q) →
            l2r c ≡ pay k ∷ rest →
            nthA (alpha c) k ≡ just (aBit false) →
            walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p (suc (ir c)) (suc (slotR c)) ≡ just w →
            c ⟶ₛ record c
              { right = p ; ir = entry w ; slotR = atSlot w
              ; l2r = rest ; er = setNth (slotR c) (suc k) (er c)
              ; envPR = ρ′ ; envIR = addPend pend′ (ir c) (slotR c) (envIR c) }
  iget1-r : ∀ {c x p q ρ′ pend′ k rest w1 w2} →
            Unfold (envPR c) [] (right c) ρ′ pend′ (f-iget x p q) →
            l2r c ≡ pay k ∷ rest →
            nthA (alpha c) k ≡ just (aBit true) →
            walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p (suc (ir c)) (suc (slotR c)) ≡ just w1 →
            walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) q (next w1) (slotN w1) ≡ just w2 →
            c ⟶ₛ record c
              { right = q ; ir = entry w2 ; slotR = atSlot w2
              ; l2r = rest ; er = setNth (slotR c) (suc k) (er c)
              ; envPR = ρ′ ; envIR = addPend pend′ (ir c) (slotR c) (envIR c) }
  mget-r : ∀ {c t x as ρ′ pend′ k rest a name w p} →
           Unfold (envPR c) [] (right c) ρ′ pend′ (f-mget t x as) →
           l2r c ≡ pay k ∷ rest →
           nthA (alpha c) k ≡ just a →
           fits t a ≡ true →
           conOf a ≡ just name →
           armGo (addPend pend′ (ir c) (slotR c) (envIR c)) name as (suc (ir c)) (suc (slotR c)) ≡ just (w , p) →
           c ⟶ₛ record c
             { right = p ; ir = entry w ; slotR = atSlot w
             ; l2r = rest ; er = setNth (slotR c) (suc k) (er c)
             ; envPR = ρ′ ; envIR = addPend pend′ (ir c) (slotR c) (envIR c) }

  finish : ∀ {c ρL pendL ρR pendR fL fR} →
           Unfold (envPL c) [] (left c) ρL pendL fL →
           HaltF fL →
           Unfold (envPR c) [] (right c) ρR pendR fR →
           HaltF fR →
           l2r c ≡ [] →
           r2l c ≡ [] →
           c ⟶ₛ c

------------------------------------------------------------------------
-- Reachability from a start configuration, and the coinductive run.
------------------------------------------------------------------------

data SReach : SConf → SConf → Set where
  sr-here : ∀ {c} → SReach c c
  sr-step : ∀ {a b c} → a ⟶ₛ b → SReach b c → SReach a c

CanFinish : SConf → Set
CanFinish c = Σ EnvP (λ ρL → Σ (List String) (λ pendL → Σ Focus (λ fL →
             Σ EnvP (λ ρR → Σ (List String) (λ pendR → Σ Focus (λ fR →
             Unfold (envPL c) [] (left c) ρL pendL fL × HaltF fL ×
             Unfold (envPR c) [] (right c) ρR pendR fR × HaltF fR ×
             l2r c ≡ [] × r2l c ≡ []))))))

SourceSafe : SConf → Set
SourceSafe c0 = ∀ {c} → SReach c0 c → CanFinish c ⊎ Σ SConf (λ d → c ⟶ₛ d)

-- Weaker than `NoStuck`. A step on one side beside a fault on the
-- other is allowed here, and `merge` returns `VBad`, which is not
-- `Shape`. `source-safe-iff` uses `SourceShape` in `Muro.Temporal.Span`.

record SPath : Set where
  coinductive
  field
    shead : SConf
    stail : SPath

open SPath public

record SIsRun (π : SPath) : Set where
  coinductive
  field
    smove : shead π ⟶ₛ shead (stail π)
    srest : SIsRun (stail π)

open SIsRun public

------------------------------------------------------------------------
-- Binders in the order slots are assigned, and the finite injection.
------------------------------------------------------------------------

mutual
  bnames : SProc → List String
  bnamesArms : List Arm → List String

  bnames sdone = []
  bnames sstop = []
  bnames sout = []
  bnames (sput _ p) = bnames p
  bnames (sget _ x p) = x ∷ bnames p
  bnames (spick0 p) = bnames p
  bnames (spick1 p) = bnames p
  bnames (scover p q) = bnames p ++ bnames q
  bnames (siget x p q) = x ∷ bnames p ++ bnames q
  bnames (smget _ x as) = x ∷ bnamesArms as
  bnames (smu _ p) = bnames p
  bnames (svar _) = []

  bnamesArms [] = []
  bnamesArms (abad ∷ as) = bnamesArms as
  bnamesArms (aok _ p ∷ as) = bnames p ++ bnamesArms as

nullFlds : List S.Fld → Bool
nullFlds [] = true
nullFlds (_ ∷ _) = false

nullCtors : List S.Ctor → Bool
nullCtors [] = true
nullCtors (S.ctor _ fs ∷ cs) = nullFlds fs ∧ nullCtors cs

declName : S.Decl → String
declName (S.mkDecl s _ _) = s

goodGet : S.Ty → Maybe Tag
goodGet S.nat = just tagNat
goodGet S.bit = just tagBit
goodGet S.unit = nothing
goodGet (S.pair _ _) = nothing
goodGet (S.rec _) = nothing
goodGet (S.vec _ _) = nothing
goodGet (S.dat d _) with nullCtors (S.ctorsOf d)
... | true = just (tagDat (declName d))
... | false = nothing

bump : Pay → Pay
bump (pNat n) = pNat (suc n)
bump _ = pOut

payVal : ∀ {A} → S.Val A → Pay
payVal S.zero = pNat zero
payVal (S.suc v) = bump (payVal v)
payVal S.b0 = pBit false
payVal S.b1 = pBit true
payVal S.tt = pOut
payVal (S.tup _ _) = pOut
payVal (S.rec _) = pOut
payVal (S.rep _) = pOut
payVal (S.con {d} {as} s S.snil) with S.fits (S.con {d} {as} s S.snil)
... | true = pCon s
... | false = pOut
payVal (S.con _ (S.scons _ _ _)) = pOut

payOf : ∀ {A} → S.ValExpr A → Pay
payOf (S.lit v) = payVal v
payOf (S.var x) = pEcho x
payOf (S.call _ _) = pOut

-- Constructors of a payload, or none when the type is not a declaration.
ctorsTy : S.Ty → List S.Ctor
ctorsTy (S.dat d _) = S.ctorsOf d
ctorsTy _ = []

-- Arm `k` against constructor `n`, in order. A bare arm, a fielded
-- arm, or a different name is not the list the graph matches.
mutual
  matchArms : List S.Ctor → List S.PArm → Maybe (List Arm)
  matchArms [] [] = just []
  matchArms (S.ctor n _ ∷ cs) (S.named k [] p ∷ ps) with n == k
  ... | false = nothing
  ... | true with matchArms cs ps
  ... | nothing = nothing
  ... | just bs = just (aok k (inj p) ∷ bs)
  matchArms _ _ = nothing

  injGot : Maybe Tag → String → S.Proc → SProc
  injGot (just t) x p = sget t x (inj p)
  injGot nothing _ _ = sout

  injMatched : Maybe Tag → List S.Ctor → String → List S.PArm → SProc
  injMatched nothing _ _ _ = sout
  injMatched (just t) cs x as with matchArms cs as
  ... | nothing = sout
  ... | just bs = smget t x bs

  inj : S.Proc → SProc
  inj S.done = sdone
  inj S.stop = sstop
  inj (S.put _ e p) = sput (payOf e) (inj p)
  inj (S.get A x p) = injGot (goodGet A) x p
  inj (S.pick0 p) = spick0 (inj p)
  inj (S.pick1 p) = spick1 (inj p)
  inj (S.cover p q) = scover (inj p) (inj q)
  inj (S.iget x p q) = siget x (inj p) (inj q)
  inj (S.mget A x as) = injMatched (goodGet A) (ctorsTy A) x as

-- A constructor the declaration does not have is not a payload.
bad-con : payOf (S.lit (S.con {S.boolDecl} {[]} "nope" S.snil)) ≡ pOut
bad-con = refl

-- A bare arm does not name a constructor, so the injection refuses it.
bare-mget : inj (S.mget S.nat "x" (S.bare S.done ∷ [])) ≡ sout
bare-mget = refl

------------------------------------------------------------------------
-- The processes the compiled examples use, written as source.
------------------------------------------------------------------------

src-loopL : SProc
src-loopL = smu "X" (sput (pNat zero) (svar "X"))

src-loopR : SProc
src-loopR = smu "Y" (sget tagNat "d" (svar "Y"))

src-cross : SProc
src-cross = sput (pNat zero) (sget tagNat "a" sdone)

src-echoA : SProc
src-echoA = smu "X" (sput (pNat zero) (sget tagNat "m" (svar "X")))

src-echoB : SProc
src-echoB = smu "Y" (sget tagNat "n" (sput (pEcho "n") (svar "Y")))

src-spinL : SProc
src-spinL = smu "X" (sput (pCon "bytes") (svar "X"))

src-spinR : SProc
src-spinR =
  smu "Y" (smget (tagDat "Frame") "f"
    (aok "bytes" (svar "Y") ∷ aok "trailers" sdone ∷ aok "headers" sdone ∷ []))

ex-walk-loop : walk [] [] src-loopL zero zero ≡ just (mkW zero zero (suc zero) zero)
ex-walk-loop = refl

ex-walk-echo : walk [] [] src-echoA zero zero ≡ just (mkW zero zero (suc (suc zero)) (suc zero))
ex-walk-echo = refl

------------------------------------------------------------------------
-- One graph step, computed from the block `lookB` returned.
-- `reactL′` is not a `with`-function, so rewriting the lookup makes
-- the step reduce. The same for the right-hand process.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Fire where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Product using (_×_; _,_; Σ)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; inspect; [_])

open import Muro.AsyncRec
  using ( Atom; aBit; Tag; Tok; pay; lab; Fault; fUnbounded
        ; Block; bDone; bStop; bPut; bEcho; bGet; bPick0; bPick1
        ; bCover; bIget; bMget
        ; RConf; rc; Graph; Act; AWait; ABad; AGo
        ; lookB; findA; nthA; fits; conOf; slotVal; armTo; setNth
        ; lt; room; snoc; reactL; reactL′; reactR; reactR′
        ; onL; onR; onL-get; onR-get; onL-cover; onR-cover
        ; onL-iget; onR-iget; onL-mget; onR-mget
        ; ilOf; irOf; l2rOf; r2lOf; elOf; erOf
        ; halted; halted′; isHalt; andb )
open Graph

import Muro.Temporal.Source as Src
open Src.SConf

------------------------------------------------------------------------
-- `room` is the boolean form of the queue bound.
------------------------------------------------------------------------

lt-yes : ∀ m n → m < n → lt m n ≡ true
lt-yes zero zero ()
lt-yes zero (suc _) _ = refl
lt-yes (suc _) zero ()
lt-yes (suc m) (suc n) (s≤s le) = lt-yes m n le

room-yes : ∀ cap q → length q < cap → room cap q ≡ true
room-yes cap q le = lt-yes (length q) cap le

snoc≡ : ∀ (xs : List Tok) t → Src.snoc xs t ≡ snoc xs t
snoc≡ [] _ = refl
snoc≡ (x ∷ xs) t = cong (x ∷_) (snoc≡ xs t)

bad≢go : ∀ {f r} → ABad f ≡ AGo r → ⊥
bad≢go ()

wait≢go : ∀ {r} → AWait ≡ AGo r → ⊥
wait≢go ()

ago-inj : ∀ {r r′} → AGo r ≡ AGo r′ → r ≡ r′
ago-inj refl = refl

------------------------------------------------------------------------
-- Left sends.
------------------------------------------------------------------------

react-put : ∀ g il ir (l2r r2l : List Tok) el er atom k j →
            findA atom (alpha g) ≡ just k →
            room (cap g) l2r ≡ true →
            lookB (codeL g) il ≡ just (bPut atom j) →
            reactL g (rc il ir l2r r2l el er) ≡
              AGo (rc j ir (snoc l2r (pay k)) r2l el er)
react-put g il ir l2r r2l el er atom k j eqF eqR eqB
  rewrite eqB | eqF | eqR = refl

react-echo : ∀ g il ir (l2r r2l : List Tok) el er s k j →
             slotVal el s ≡ just k →
             room (cap g) l2r ≡ true →
             lookB (codeL g) il ≡ just (bEcho s j) →
             reactL g (rc il ir l2r r2l el er) ≡
               AGo (rc j ir (snoc l2r (pay k)) r2l el er)
react-echo g il ir l2r r2l el er s k j eqS eqR eqB
  rewrite eqB | eqS | eqR = refl

react-pick0 : ∀ g il ir (l2r r2l : List Tok) el er j →
              room (cap g) l2r ≡ true →
              lookB (codeL g) il ≡ just (bPick0 j) →
              reactL g (rc il ir l2r r2l el er) ≡
                AGo (rc j ir (snoc l2r (lab false)) r2l el er)
react-pick0 g il ir l2r r2l el er j eqR eqB rewrite eqB | eqR = refl

react-pick1 : ∀ g il ir (l2r r2l : List Tok) el er j →
              room (cap g) l2r ≡ true →
              lookB (codeL g) il ≡ just (bPick1 j) →
              reactL g (rc il ir l2r r2l el er) ≡
                AGo (rc j ir (snoc l2r (lab true)) r2l el er)
react-pick1 g il ir l2r r2l el er j eqR eqB rewrite eqB | eqR = refl

------------------------------------------------------------------------
-- Left receives.
------------------------------------------------------------------------

react-get : ∀ g il ir (l2r : List Tok) k rest el er t s a i →
            (pay k ∷ rest) ≡ r2lOf (rc il ir l2r (pay k ∷ rest) el er) →
            nthA (alpha g) k ≡ just a →
            fits t a ≡ true →
            lookB (codeL g) il ≡ just (bGet t s i) →
            reactL g (rc il ir l2r (pay k ∷ rest) el er) ≡
              AGo (rc i ir l2r rest (setNth s (suc k) el) er)
react-get g il ir l2r k rest el er t s a i _ eqA eqF eqB
  rewrite eqB | eqA | eqF = refl

react-cover0 : ∀ g il ir l2r rest el er i j →
               lookB (codeL g) il ≡ just (bCover i j) →
               reactL g (rc il ir l2r (lab false ∷ rest) el er) ≡
                 AGo (rc i ir l2r rest el er)
react-cover0 g il ir l2r rest el er i j eqB rewrite eqB = refl

react-cover1 : ∀ g il ir l2r rest el er i j →
               lookB (codeL g) il ≡ just (bCover i j) →
               reactL g (rc il ir l2r (lab true ∷ rest) el er) ≡
                 AGo (rc j ir l2r rest el er)
react-cover1 g il ir l2r rest el er i j eqB rewrite eqB = refl

react-iget0 : ∀ g il ir l2r k rest el er s i j →
              nthA (alpha g) k ≡ just (aBit false) →
              lookB (codeL g) il ≡ just (bIget s i j) →
              reactL g (rc il ir l2r (pay k ∷ rest) el er) ≡
                AGo (rc i ir l2r rest (setNth s (suc k) el) er)
react-iget0 g il ir l2r k rest el er s i j eqA eqB
  rewrite eqB | eqA = refl

react-iget1 : ∀ g il ir l2r k rest el er s i j →
              nthA (alpha g) k ≡ just (aBit true) →
              lookB (codeL g) il ≡ just (bIget s i j) →
              reactL g (rc il ir l2r (pay k ∷ rest) el er) ≡
                AGo (rc j ir l2r rest (setNth s (suc k) el) er)
react-iget1 g il ir l2r k rest el er s i j eqA eqB
  rewrite eqB | eqA = refl

react-mget : ∀ g il ir l2r k rest el er t s arms a name j →
             nthA (alpha g) k ≡ just a →
             fits t a ≡ true →
             conOf a ≡ just name →
             armTo name arms ≡ just j →
             lookB (codeL g) il ≡ just (bMget t s arms) →
             reactL g (rc il ir l2r (pay k ∷ rest) el er) ≡
               AGo (rc j ir l2r rest (setNth s (suc k) el) er)
react-mget g il ir l2r k rest el er t s arms a name j eqA eqF eqC eqJ eqB
  rewrite eqB | eqA | eqF | eqC | eqJ = refl

------------------------------------------------------------------------
-- Right sends and receives. The queues are swapped.
------------------------------------------------------------------------

reactR-put : ∀ g il ir l2r r2l el er atom k j →
             findA atom (alpha g) ≡ just k →
             room (cap g) r2l ≡ true →
             lookB (codeR g) ir ≡ just (bPut atom j) →
             reactR g (rc il ir l2r r2l el er) ≡
               AGo (rc il j l2r (snoc r2l (pay k)) el er)
reactR-put g il ir l2r r2l el er atom k j eqF eqR eqB
  rewrite eqB | eqF | eqR = refl

reactR-echo : ∀ g il ir l2r r2l el er s k j →
              slotVal er s ≡ just k →
              room (cap g) r2l ≡ true →
              lookB (codeR g) ir ≡ just (bEcho s j) →
              reactR g (rc il ir l2r r2l el er) ≡
                AGo (rc il j l2r (snoc r2l (pay k)) el er)
reactR-echo g il ir l2r r2l el er s k j eqS eqR eqB
  rewrite eqB | eqS | eqR = refl

reactR-pick0 : ∀ g il ir l2r r2l el er j →
               room (cap g) r2l ≡ true →
               lookB (codeR g) ir ≡ just (bPick0 j) →
               reactR g (rc il ir l2r r2l el er) ≡
                 AGo (rc il j l2r (snoc r2l (lab false)) el er)
reactR-pick0 g il ir l2r r2l el er j eqR eqB rewrite eqB | eqR = refl

reactR-pick1 : ∀ g il ir l2r r2l el er j →
               room (cap g) r2l ≡ true →
               lookB (codeR g) ir ≡ just (bPick1 j) →
               reactR g (rc il ir l2r r2l el er) ≡
                 AGo (rc il j l2r (snoc r2l (lab true)) el er)
reactR-pick1 g il ir l2r r2l el er j eqR eqB rewrite eqB | eqR = refl

reactR-get : ∀ g il ir k rest r2l el er t s a i →
             nthA (alpha g) k ≡ just a →
             fits t a ≡ true →
             lookB (codeR g) ir ≡ just (bGet t s i) →
             reactR g (rc il ir (pay k ∷ rest) r2l el er) ≡
               AGo (rc il i rest r2l el (setNth s (suc k) er))
reactR-get g il ir k rest r2l el er t s a i eqA eqF eqB
  rewrite eqB | eqA | eqF = refl

reactR-cover0 : ∀ g il ir rest r2l el er i j →
                lookB (codeR g) ir ≡ just (bCover i j) →
                reactR g (rc il ir (lab false ∷ rest) r2l el er) ≡
                  AGo (rc il i rest r2l el er)
reactR-cover0 g il ir rest r2l el er i j eqB rewrite eqB = refl

reactR-cover1 : ∀ g il ir rest r2l el er i j →
                lookB (codeR g) ir ≡ just (bCover i j) →
                reactR g (rc il ir (lab true ∷ rest) r2l el er) ≡
                  AGo (rc il j rest r2l el er)
reactR-cover1 g il ir rest r2l el er i j eqB rewrite eqB = refl

reactR-iget0 : ∀ g il ir k rest r2l el er s i j →
               nthA (alpha g) k ≡ just (aBit false) →
               lookB (codeR g) ir ≡ just (bIget s i j) →
               reactR g (rc il ir (pay k ∷ rest) r2l el er) ≡
                 AGo (rc il i rest r2l el (setNth s (suc k) er))
reactR-iget0 g il ir k rest r2l el er s i j eqA eqB
  rewrite eqB | eqA = refl

reactR-iget1 : ∀ g il ir k rest r2l el er s i j →
               nthA (alpha g) k ≡ just (aBit true) →
               lookB (codeR g) ir ≡ just (bIget s i j) →
               reactR g (rc il ir (pay k ∷ rest) r2l el er) ≡
                 AGo (rc il j rest r2l el (setNth s (suc k) er))
reactR-iget1 g il ir k rest r2l el er s i j eqA eqB
  rewrite eqB | eqA = refl

reactR-mget : ∀ g il ir k rest r2l el er t s arms a name j →
              nthA (alpha g) k ≡ just a →
              fits t a ≡ true →
              conOf a ≡ just name →
              armTo name arms ≡ just j →
              lookB (codeR g) ir ≡ just (bMget t s arms) →
              reactR g (rc il ir (pay k ∷ rest) r2l el er) ≡
                AGo (rc il j rest r2l el (setNth s (suc k) er))
reactR-mget g il ir k rest r2l el er t s arms a name j eqA eqF eqC eqJ eqB
  rewrite eqB | eqA | eqF | eqC | eqJ = refl

------------------------------------------------------------------------
-- Both blocks halted, so the stutter is the graph's `finish` step.
------------------------------------------------------------------------

halt-of : ∀ g il ir l2r r2l el er bl br →
          isHalt bl ≡ true → isHalt br ≡ true →
          lookB (codeL g) il ≡ just bl →
          lookB (codeR g) ir ≡ just br →
          halted g (rc il ir l2r r2l el er) ≡ true
halt-of g il ir l2r r2l el er bl br hb hr eqL eqR
  rewrite eqL | eqR | hb | hr = refl

isHalt-done : isHalt bDone ≡ true
isHalt-done = refl

isHalt-stop : isHalt bStop ≡ true
isHalt-stop = refl

------------------------------------------------------------------------
-- The projected configuration ignores the process and the environments,
-- so a source update of those fields is the block configuration.
------------------------------------------------------------------------

abs-ix : ∀ (c : Src.SConf) j q →
         Src.abs (record c { il = j ; l2r = q }) ≡
         rc j (ir c) q (r2l c) (el c) (er c)
abs-ix _ _ _ = refl

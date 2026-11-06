------------------------------------------------------------------------
-- The ordinal of an action is its place among blocks of the same verb,
-- in the order `compile` allocates them. That is the order the Elixir
-- checker filters with `Enum.at (n - 1)`. A jump allocates no block, so
-- it is not an action. `put` and `echo` are both `v-put`. `get`, `iget`,
-- and `mget` are `v-get`.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Ordinal where

open import Data.Bool.Base using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.List.Base using (List; []; _∷_)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong)

open import Muro.AsyncRec
  using ( Block; bDone; bStop; bPut; bEcho; bGrow; bGet; bPick0; bPick1
        ; bCover; bIget; bMget; lookB; materialise
        ; COut; cok; cfail )
open import Muro.Temporal
  using (Verb; v-put; v-get; v-pick0; v-pick1; v-cover; verbOf; verb≡)
open import Muro.Temporal.Pic
  using ( Ord; o0; o1; _∈_; here; there; ord-lo; n<n; root-at
        ; Same; both-ok; both-bad; er0; echo-empty )
open import Muro.Temporal.Bridge
  using (Frag; echoOk; compiled)
open import Muro.Temporal.Source
  using (SProc; walk; bnames; W)
open W
open import Muro.Temporal.Agree
  using (agree; root-ns)

------------------------------------------------------------------------
-- One hit in the filtered list. `k` counts from zero, so the ordinal
-- a reader writes is `suc k`.
------------------------------------------------------------------------

data Pick (v : Verb) : List (ℕ × Block) → ℕ → ℕ → Set where
  p-this : ∀ {i b bs} →
           verbOf b ≡ just v →
           Pick v ((i , b) ∷ bs) zero i
  p-later : ∀ {i b bs k j} →
            verbOf b ≡ just v →
            Pick v bs k j →
            Pick v ((i , b) ∷ bs) (suc k) j
  p-other : ∀ {i b bs k j} →
            (verbOf b ≡ just v → ⊥) →
            Pick v bs k j →
            Pick v ((i , b) ∷ bs) k j

pick-mem : ∀ {v bs k i} → Pick v bs k i →
           Σ Block (λ b → (i , b) ∈ bs × verbOf b ≡ just v)
pick-mem (p-this {b = b} vb) = b , here , vb
pick-mem (p-later _ pk) =
  let b , mem , vb = pick-mem pk in b , there mem , vb
pick-mem (p-other _ pk) =
  let b , mem , vb = pick-mem pk in b , there mem , vb

------------------------------------------------------------------------
-- `materialise` reads the block `Pick` selected, and that block has
-- the verb. Distinct ordinals are distinct indices.
------------------------------------------------------------------------

block-of : ∀ {nL bs v k i} → Ord zero nL bs → Pick v bs k i →
           Σ Block (λ b →
             lookB (materialise nL zero bs) i ≡ just b × verbOf b ≡ just v)
block-of {nL} od pk =
  let b , mem , vb = pick-mem pk
  in b , root-at {nL} od mem , vb

i<≢ : ∀ {i j} → i < j → i ≢ j
i<≢ le refl = n<n le

head-tail : ∀ {lo hi i bs j} b c →
            Ord lo hi ((i , b) ∷ bs) → (j , c) ∈ bs → i ≢ j
head-tail _ c (o1 od) mem = i<≢ (ord-lo {b = c} od mem)

block-of-inj : ∀ {lo hi bs v k1 k2 i1 i2} →
               Ord lo hi bs →
               Pick v bs k1 i1 → Pick v bs k2 i2 →
               k1 ≢ k2 → i1 ≢ i2
block-of-inj (o1 _) (p-this _) (p-this _) neq = ⊥-elim (neq refl)
block-of-inj (o1 {b = b0} od) (p-this _) (p-later _ pk) _ =
  let c , mem , _ = pick-mem pk in head-tail b0 c (o1 {b = b0} od) mem
block-of-inj (o1 _) (p-this vb) (p-other no _) _ = ⊥-elim (no vb)
block-of-inj (o1 {b = b0} od) (p-later _ pk) (p-this _) _ =
  let c , mem , _ = pick-mem pk in λ eq → head-tail b0 c (o1 {b = b0} od) mem (sym eq)
block-of-inj (o1 od) (p-later _ pk1) (p-later _ pk2) neq =
  block-of-inj od pk1 pk2 (λ eq → neq (cong suc eq))
block-of-inj (o1 _) (p-later vb _) (p-other no _) _ = ⊥-elim (no vb)
block-of-inj (o1 _) (p-other no _) (p-this vb) _ = ⊥-elim (no vb)
block-of-inj (o1 _) (p-other no _) (p-later vb _) _ = ⊥-elim (no vb)
block-of-inj (o1 od) (p-other _ pk1) (p-other _ pk2) neq =
  block-of-inj od pk1 pk2 neq
block-of-inj o0 () _ _ _

------------------------------------------------------------------------
-- The block list of a source process is the one `compile` returns.
-- `block-of` reads that list. An ordinal in the process is an ordinal
-- in the materialised code.
------------------------------------------------------------------------

source-blocks : (P : SProc) (fp : Frag P) →
                echoOk (bnames P) [] P ≡ true →
                Same zero zero (bnames P)
                  (walk [] [] P zero zero) (compiled P fp)
source-blocks P fp ok =
  agree P fp [] [] [] [] (bnames P) [] [] [] zero zero
    er0 (echo-empty [] (bnames P)) ok refl (root-ns P)

-- `Same` is indexed by the walk and the compile result, which do not
-- reduce until the proof is inspected. `Opened` carries the counters
-- the inspection finds.
data Opened (bound : List String) (mw : Maybe W) (co : COut) : Set where
  opened-bad : ∀ {f} → mw ≡ nothing → co ≡ cfail f → Opened bound mw co
  opened-ok : ∀ w bs →
              Ord zero (next w) bs →
              mw ≡ just w →
              co ≡ cok (entry w) (next w) (slotN w) bs →
              Opened bound mw co

open-same : ∀ {bound mw co} → Same zero zero bound mw co → Opened bound mw co
open-same (both-bad {f}) = opened-bad refl refl
open-same (both-ok w bs _ od) = opened-ok w bs od refl refl

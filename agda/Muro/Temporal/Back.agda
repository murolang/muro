------------------------------------------------------------------------
-- A graph step, read back as the source step that ran it.
-- The cursor's place supplies the unfold. This file starts with the
-- leaf: the process standing at the cursor is already the action.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Back where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

open import Muro.AsyncRec
  using ( Atom; Block; bPut; Tok; pay; snoc; Graph
        ; RConf; rc; Act; AGo; findA; lookB; reactL
        ; room; lt )
open import Muro.Temporal using (Step; stepL; lside)
open import Muro.Temporal.Fire
  using (react-put; bad≢go; wait≢go; ago-inj)
open import Muro.Temporal.Source
  using ( SProc; SConf; abs; EnvI; addPend; walk; asAtom
        ; sput; W
        ; Unfold; u-put
        ; _⟶ₛ_; put-l )
open SConf
open W
open import Muro.Temporal.Den
  using ( Place; p-act; Den; d-put; Link; lk-put
        ; At; at-put; Cov; c-put; CovP; cp-act
        ; Align; al-put
        ; headIx; slotOf; envOf; Recipe; r-put )
open import Muro.Temporal.Run
  using (Cursor; Ext; Hold; walk-ext)
open import Muro.Temporal.Expose
  using (put-fwd; afterPut; seenL; walk-idx)
open import Muro.Temporal.Pic using (_∈_)

------------------------------------------------------------------------
-- `lt` on the queue length.
------------------------------------------------------------------------

lt-sound : ∀ m n → lt m n ≡ true → m < n
lt-sound zero zero ()
lt-sound zero (suc _) _ = s≤s z≤n
lt-sound (suc _) zero ()
lt-sound (suc m) (suc n) eq = s≤s (lt-sound m n eq)

tgtL : ∀ {g c d} → Step g c lside d → reactL g c ≡ AGo d
tgtL (stepL eq) = eq

-- A put block that steps names its alphabet index and has room.
put-inv : ∀ g il ir (l2r r2l : List Tok) el er atom j r →
          lookB (Graph.codeL g) il ≡ just (bPut atom j) →
          reactL g (rc il ir l2r r2l el er) ≡ AGo r →
          Σ ℕ (λ k → findA atom (Graph.alpha g) ≡ just k ×
                     room (Graph.cap g) l2r ≡ true ×
                     r ≡ rc j ir (snoc l2r (pay k)) r2l el er)
put-inv g il ir l2r r2l el er atom j r eqB eq =
  goF (findA atom (Graph.alpha g)) refl
  where
  goR : (k : ℕ) → findA atom (Graph.alpha g) ≡ just k →
        (b : Bool) → room (Graph.cap g) l2r ≡ b →
        Σ ℕ (λ k′ → findA atom (Graph.alpha g) ≡ just k′ ×
                    room (Graph.cap g) l2r ≡ true ×
                    r ≡ rc j ir (snoc l2r (pay k′)) r2l el er)
  goR k eqF false eqR rewrite eqB | eqF | eqR = ⊥-elim (wait≢go eq)
  goR k eqF true eqR =
    k , eqF , eqR ,
    ago-inj (trans (sym eq) (react-put g il ir l2r r2l el er atom k j eqF eqR eqB))

  goF : (mb : Maybe ℕ) → findA atom (Graph.alpha g) ≡ mb →
        Σ ℕ (λ k → findA atom (Graph.alpha g) ≡ just k ×
                   room (Graph.cap g) l2r ≡ true ×
                   r ≡ rc j ir (snoc l2r (pay k)) r2l el er)
  goF nothing eqF rewrite eqB | eqF = ⊥-elim (bad≢go eq)
  goF (just k) eqF = goR k eqF (room (Graph.cap g) l2r) refl

------------------------------------------------------------------------
-- The place is a put, with nothing pending. The graph's left step is
-- that put, and the source meeting takes the same step.
------------------------------------------------------------------------

data IsPut : {P : SProc} → Place P → Set where
  is-put : ∀ {n s a atom j p ρw w aeq wk ej dest dh ds de i0 s0 ρ} →
           IsPut (p-act (d-put n s a atom j p ρw w aeq wk ej dest dh ds de)
                        r-put i0 s0 ρ)

bwd-put : ∀ {g c r′} (h : Hold g c) →
          Step g (abs c) lside r′ →
          (pl : Place (left c)) →
          IsPut pl →
          Link pl →
          Align [] pl →
          CovP pl (Hold.bsL h) →
          At [] pl →
          il c ≡ headIx pl →
          slotL c ≡ slotOf pl →
          Ext (envOf pl) (envIL c) →
          Σ SConf (λ c′ → c ⟶ₛ c′ × abs c′ ≡ r′ × Hold g c′)
bwd-put {g} {c} {r′} h (stepL eq)
  (p-act (d-put n s a atom j p ρw w aeq wkD ej dest dh ds de) r-put i0 s0 ρden)
  is-put
  (lk-put eqi eqs eqρ lkD)
  (al-put eqAl alD)
  (cp-act (c-put mem cvD))
  (at-put pnil atD)
  ix ss sn =
  c′ , step , same , hold
  where
  en : il c ≡ n
  en = trans ix eqi
  es : slotL c ≡ s
  es = trans ss eqs
  -- `Align []` says the continuation was walked at the place's own
  -- environment: the pending list is empty, so `addPend` is the identity.
  wkρ : walk [] ρden p (suc n) s ≡ just w
  wkρ = subst (λ e → walk [] e p (suc n) s ≡ just w) eqAl wkD
  wkI : walk [] (envIL c) p (suc n) s ≡ just w
  wkI = walk-ext [] ρden (envIL c) p (suc n) s w sn wkρ
  wk : walk [] (addPend [] (il c) (slotL c) (envIL c)) p
           (suc (il c)) (slotL c) ≡ just w
  wk = walk-idx {ρ = envIL c} {p = p} {n = il c} {n′ = n}
         {s = slotL c} {s′ = s} {w = w} en es wkI
  memI : (il c , bPut atom j) ∈ Hold.bsL h
  memI = subst (λ i → (i , bPut atom j) ∈ Hold.bsL h) (sym en) mem
  look = seenL {b = bPut atom j} h memI
  inv = put-inv g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
          atom j r′ look eq
  k = proj₁ inv
  findG = proj₁ (proj₂ inv)
  roomG = proj₁ (proj₂ (proj₂ inv))
  findC : findA atom (alpha c) ≡ just k
  findC = subst (λ al → findA atom al ≡ just k) (sym (Hold.α h)) findG
  le : length (l2r c) < cap c
  le = subst (λ n₁ → length (l2r c) < n₁) (sym (Hold.κ h))
         (lt-sound (length (l2r c)) (Graph.cap g) roomG)
  fwd = put-fwd h u-put aeq findC le wk
  c′ = afterPut c p (envPL c) [] k w
  step : c ⟶ₛ c′
  step = put-l u-put aeq findC le wk
  same : abs c′ ≡ r′
  same = ago-inj (trans (sym (tgtL (proj₁ fwd))) eq)
  hold = proj₂ fwd

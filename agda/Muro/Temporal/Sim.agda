------------------------------------------------------------------------
-- Peeling a `smu`. The binder is new, or it is this table entry.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Sim where

open import Data.Bool.Base using (Bool; true)
open import Data.Nat.Base using (ℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong)

open import Muro.AsyncRec using (Block)
open import Muro.Temporal.Bridge using (distinct)
open import Muro.Temporal.Source using (SProc; smu; EnvI; EnvP; addPend)
open import Muro.Temporal.Den
  using ( Place; p-mu; p-act; Table; Link; lk-mu; At; at-mu
        ; CovP; cp-mu; Hosts; hs-mu; Links
        ; headIx; slotOf; envOf; ix-of; slot-at; ix-head; slot-head
        ; place-of; tnames; Recipe; r-mu; InTab )
open import Muro.Temporal.Run
  using ( Sync; sy0; sy1; Tied; td0; td1
        ; Ext; Fresh; Covered; fresh-mu; cov-mu; runtime-pin )

record Peeled (bs : List (ℕ × Block)) (tab : Table) (n s : ℕ) (base : EnvI)
              (x : String) (suf got : List String) (p : SProc) : Set where
  field
    pl : Place p
    cv : CovP pl bs
    lk : Link pl
    hs : Hosts tab pl
    ix : n ≡ headIx pl
    ss : s ≡ slotOf pl
    sn : Ext (envOf pl) base
    at : At (x ∷ suf) pl
    cvd : Covered (x ∷ suf) (x ∷ got) base n s
    fr : Fresh (x ∷ got) base n s

ix-eq : ∀ {x p tab n} {pl : Place p} (inn : InTab x (smu x p) tab) (ls : Links tab) →
        place-of inn ≡ p-mu x pl → n ≡ headIx (p-mu x pl) →
        ix-of inn ≡ n
ix-eq inn ls eq ix = trans (ix-head ls inn) (trans (cong headIx eq) (sym ix))

sl-eq : ∀ {x p tab s} {pl : Place p} (inn : InTab x (smu x p) tab) (ls : Links tab) →
        place-of inn ≡ p-mu x pl → s ≡ slotOf (p-mu x pl) →
        slot-at inn ≡ s
sl-eq inn ls eq ss = trans (slot-head ls inn) (trans (cong slotOf eq) (sym ss))

-- The cursor's table entry for this binder is the place being peeled.
-- Its counters are the cursor's, so the runtime pin applies.
peel-mu : ∀ {bs tab n s base suf got x p env} →
          (pl : Place (smu x p)) → CovP pl bs → Link pl → Hosts tab pl →
          At suf pl → Links tab →
          n ≡ headIx pl → s ≡ slotOf pl →
          Ext (envOf pl) base →
          Covered suf got base n s → Fresh got base n s →
          distinct (tnames tab) ≡ true →
          Sync tab env base →
          Peeled bs tab n s base x suf got p
peel-mu {n = n} {s = s} {base = base} {suf = suf} {got = got} {x = x}
        (p-mu .x pl) (cp-mu cv) (lk-mu lk) (hs-mu inn eq hs) (at-mu _ at) ls
        ix ss sn cvd fr nd sy =
  record
    { pl = pl
    ; cv = cv
    ; lk = lk
    ; hs = hs
    ; ix = ix
    ; ss = ss
    ; sn = sn
    ; at = at
    ; cvd = cov-mu {x = x} {suf = suf} {got = got} {base = base} {n = n} {s = s} cvd
    ; fr = fresh-mu {x = x} {got = got} {ρ = base} {n = n} {s = s}
            (runtime-pin {x = x} {ρ = base} {n = n} {s = s}
               inn (ix-eq inn ls eq ix) (sl-eq inn ls eq ss) nd sy)
            fr
    }
peel-mu (p-act _ (r-mu _) _ _ _) _ () _ _ _ _ _ _ _ _ _ _

-- Names peeled in one unfold, each bound at the action's counters.
data Pref (tab : Table) (n s : ℕ) : List String → EnvP → Set where
  pf0 : Pref tab n s [] []
  pf1 : ∀ {x p pend env} (m : InTab x (smu x p) tab) →
        ix-of m ≡ n → slot-at m ≡ s →
        Pref tab n s pend env →
        Pref tab n s (x ∷ pend) ((x , smu x p) ∷ env)

-- The peeled prefix sits in front of the environment the step started from.
tied-pref : ∀ {tab n s pend env base} →
            Pref tab n s pend env → Tied tab base →
            Tied tab (env ++ base)
tied-pref pf0 td = td
tied-pref (pf1 m _ _ pf) td = td1 m (tied-pref pf td)

sync-pref : ∀ {tab n s pend env baseE baseI} →
            Pref tab n s pend env → Sync tab baseE baseI →
            Sync tab (env ++ baseE) (addPend pend n s baseI)
sync-pref pf0 sy = sy
sync-pref {n = n} {s = s} (pf1 m ix≡ sl≡ pf) sy =
  sy1 {i = n} {s = s} m ix≡ sl≡ (sync-pref pf sy)

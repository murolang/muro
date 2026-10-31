------------------------------------------------------------------------
-- Where a denoted jump lands.
--
-- `spine` stops at a jump. The jump's target is an earlier entry of
-- the same table: a binder already in the environment, a binder still
-- pending, or a `mu` sealed before this one. `denote` builds that
-- fact. A root table has an empty environment and an empty pending
-- list, so every jump there is an earlier entry.
--
-- The position of an entry is the number of entries before it. A jump
-- recorded here names one of those, so the position is strictly
-- smaller. Chasing the jump is well-founded on that position.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Nest where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Product using (_,_)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Muro.AsyncRec using (elemS)
open import Muro.Temporal.Pic using (==-sound)
open import Muro.Temporal.Source using (SProc; smu; svar; EnvI; addPend; lookupI)
open import Muro.Temporal.Den
  using ( Place; p-mu; p-act; p-jump
        ; Table; t0; t1; appendT; tnames
        ; InTab; in-here; in-there )

------------------------------------------------------------------------
-- A name in a list, nearest end first.
------------------------------------------------------------------------

data Here (y : String) : List String → Set where
  h-here : ∀ {xs} → Here y (y ∷ xs)
  h-there : ∀ {x xs} → Here y xs → Here y (x ∷ xs)

-- Appending on the right does not move a name already found.
h-wk : ∀ {y xs ys} → Here y xs → Here y (xs ++ ys)
h-wk h-here = h-here
h-wk (h-there h) = h-there (h-wk h)

-- The name just sealed sits at the far end of the entries before this one.
at-end : ∀ {x} (above : List String) → Here x (above ++ (x ∷ []))
at-end [] = h-here
at-end (_ ∷ above) = h-there (at-end above)

ix-here : ∀ {y xs} → Here y xs → ℕ
ix-here h-here = zero
ix-here (h-there h) = suc (ix-here h)

ix<len : ∀ {y xs} (h : Here y xs) → ix-here h < length xs
ix<len h-here = s≤s z≤n
ix<len (h-there h) = s≤s (ix<len h)

elem→here : ∀ {y xs} → elemS y xs ≡ true → Here y xs
elem→here {xs = []} ()
elem→here {y} {x ∷ xs} eq = go (y == x) refl eq
  where
  go : (b : Bool) → (y == x) ≡ b → elemS y (x ∷ xs) ≡ true → Here y (x ∷ xs)
  go true eqy _ rewrite ==-sound eqy = h-here
  go false eqy eq2 rewrite eqy = h-there (elem→here eq2)

------------------------------------------------------------------------
-- Names of an index environment. `addPend` puts its list in front,
-- and that equation is definitional one cons at a time.
------------------------------------------------------------------------

namesI : EnvI → List String
namesI [] = []
namesI ((x , _ , _) ∷ ρ) = x ∷ namesI ρ

lookup-elem : ∀ {y i s ρ} → lookupI y ρ ≡ just (i , s) → elemS y (namesI ρ) ≡ true
lookup-elem {ρ = []} ()
lookup-elem {y} {i} {s} {ρ = (x , n , s0) ∷ ρ} eq = go (y == x) refl eq
  where
  go : (b : Bool) → (y == x) ≡ b →
       lookupI y ((x , n , s0) ∷ ρ) ≡ just (i , s) →
       elemS y (x ∷ namesI ρ) ≡ true
  go true eqy _ rewrite eqy = refl
  go false eqy eq2 rewrite eqy = lookup-elem {y = y} {i = i} {s = s} {ρ = ρ} eq2

lookup-here : ∀ {y i s ρ} → lookupI y ρ ≡ just (i , s) → Here y (namesI ρ)
lookup-here {y} {i} {s} {ρ} eq = elem→here {y} {namesI ρ} (lookup-elem {y} {i} {s} {ρ} eq)

------------------------------------------------------------------------
-- What the spine of a place may jump to.
--
-- `Spp` is a place returned by `denote`: its jumps name the environment
-- the place was denoted under, never a pending binder. Pending binders
-- are unguarded on that spine. `Sp` is an entry of a table, which may
-- also name a pending binder or an entry sealed earlier.
------------------------------------------------------------------------

data Spp (env : List String) : {P : SProc} → Place P → Set where
  spp-leaf : ∀ {P d i s ρ} {r : _} → Spp env (p-act {P} d r i s ρ)
  spp-mu : ∀ {x p} {pl : Place p} → Spp env pl → Spp env (p-mu x pl)
  spp-jump : ∀ {y i s ρ} → Here y env → Spp env (p-jump y i s ρ)

data Land (env pend above : List String) (y : String) : Set where
  ln-env : Here y env → Land env pend above y
  ln-pend : Here y pend → Land env pend above y
  ln-above : Here y above → Land env pend above y

data Sp (env pend above : List String) : {P : SProc} → Place P → Set where
  sp-leaf : ∀ {P d i s ρ} {r : _} → Sp env pend above (p-act {P} d r i s ρ)
  sp-mu : ∀ {x p} {pl : Place p} →
          Sp env pend above pl → Sp env pend above (p-mu x pl)
  sp-jump : ∀ {y i s ρ} → Land env pend above y → Sp env pend above (p-jump y i s ρ)

data Ts (env pend above : List String) : Table → Set where
  ts0 : Ts env pend above t0
  ts1 : ∀ {P x i s ρ pl tab} →
        Sp env pend above pl →
        Ts env pend (x ∷ above) tab →
        Ts env pend above (t1 {P} x i s ρ pl tab)

-- A returned place mentions only the environment.
spp→sp : ∀ {env pend above P} {pl : Place P} →
         Spp env pl → Sp env pend above pl
spp→sp spp-leaf = sp-leaf
spp→sp (spp-mu s) = sp-mu (spp→sp s)
spp→sp (spp-jump h) = sp-jump (ln-env h)

------------------------------------------------------------------------
-- Sealing `mu x`. The body was denoted with `x` pending. `x` is entered
-- in front of the body's table, so it is the nearest entry before the
-- body's first entry and the furthest entry before the body's later ones.
------------------------------------------------------------------------

seal-land : ∀ {env pend above x y} →
            Land env (x ∷ pend) above y →
            Land env pend (above ++ (x ∷ [])) y
seal-land (ln-env h) = ln-env h
seal-land (ln-pend h-here) = ln-above (at-end _)
seal-land (ln-pend (h-there h)) = ln-pend h
seal-land (ln-above h) = ln-above (h-wk h)

seal-sp : ∀ {env pend above x P} {pl : Place P} →
          Sp env (x ∷ pend) above pl →
          Sp env pend (above ++ (x ∷ [])) pl
seal-sp sp-leaf = sp-leaf
seal-sp (sp-mu s) = sp-mu (seal-sp s)
seal-sp (sp-jump l) = sp-jump (seal-land l)

seal-ts : ∀ {env pend above x tab} →
          Ts env (x ∷ pend) above tab →
          Ts env pend (above ++ (x ∷ [])) tab
seal-ts ts0 = ts0
seal-ts (ts1 sp rest) = ts1 (seal-sp sp) (seal-ts rest)

sealT : ∀ {env pend p x i s ρ tab} {pl : Place p} →
        Spp env pl →
        Ts env (x ∷ pend) [] tab →
        Ts env pend [] (t1 x i s ρ (p-mu x pl) tab)
sealT spp ts = ts1 (sp-mu (spp→sp spp)) (seal-ts ts)

------------------------------------------------------------------------
-- A continuation is denoted with the pending names pushed onto the
-- environment. Those names are pending again for the parent.
------------------------------------------------------------------------

pend-there : ∀ {env pend above x y} →
             Land env pend above y →
             Land env (x ∷ pend) above y
pend-there (ln-env h) = ln-env h
pend-there (ln-pend h) = ln-pend (h-there h)
pend-there (ln-above h) = ln-above h

repend-land : ∀ xs {n s ρ above y} →
              Land (namesI (addPend xs n s ρ)) [] above y →
              Land (namesI ρ) xs above y
repend-land [] (ln-env h) = ln-env h
repend-land [] (ln-pend ())
repend-land [] (ln-above h) = ln-above h
repend-land (x ∷ xs) (ln-env h-here) = ln-pend h-here
repend-land (x ∷ xs) (ln-env (h-there h)) =
  pend-there (repend-land xs (ln-env h))
repend-land (x ∷ xs) (ln-pend ())
repend-land (x ∷ xs) (ln-above h) = ln-above h

repend-sp : ∀ xs {n s ρ above P} {pl : Place P} →
            Sp (namesI (addPend xs n s ρ)) [] above pl →
            Sp (namesI ρ) xs above pl
repend-sp xs sp-leaf = sp-leaf
repend-sp xs (sp-mu s) = sp-mu (repend-sp xs s)
repend-sp xs (sp-jump l) = sp-jump (repend-land xs l)

repend-ts : ∀ xs n s ρ {above tab} →
            Ts (namesI (addPend xs n s ρ)) [] above tab →
            Ts (namesI ρ) xs above tab
repend-ts xs _ _ _ ts0 = ts0
repend-ts xs n s ρ (ts1 sp rest) =
  ts1 (repend-sp xs sp) (repend-ts xs n s ρ rest)

------------------------------------------------------------------------
-- Two tables denoted under the same environment. The right table's
-- entries sit behind every entry of the left table, so each name of
-- the left table is before them, nearest first.
------------------------------------------------------------------------

widen-land : ∀ {env pend above extra y} →
             Land env pend above y →
             Land env pend (above ++ extra) y
widen-land (ln-env h) = ln-env h
widen-land (ln-pend h) = ln-pend h
widen-land (ln-above h) = ln-above (h-wk h)

widen-sp : ∀ {env pend above extra P} {pl : Place P} →
           Sp env pend above pl →
           Sp env pend (above ++ extra) pl
widen-sp sp-leaf = sp-leaf
widen-sp (sp-mu s) = sp-mu (widen-sp s)
widen-sp (sp-jump l) = sp-jump (widen-land l)

widen-ts : ∀ {env pend above extra tab} →
           Ts env pend above tab →
           Ts env pend (above ++ extra) tab
widen-ts ts0 = ts0
widen-ts (ts1 sp rest) = ts1 (widen-sp sp) (widen-ts rest)

append-ts : ∀ {env pend above u} {t : Table} →
            Ts env pend above t →
            Ts env pend [] u →
            Ts env pend above (appendT t u)
append-ts ts0 tu = widen-ts tu
append-ts (ts1 sp rest) tu = ts1 sp (append-ts rest tu)

------------------------------------------------------------------------
-- The position of an entry. Zero is the front of the table.
------------------------------------------------------------------------

pos : ∀ {x P tab} → InTab x P tab → ℕ
pos (in-here _) = zero
pos (in-there m) = suc (pos m)

pos<len : ∀ {x P tab} (m : InTab x P tab) → pos m < length (tnames tab)
pos<len (in-here _) = s≤s z≤n
pos<len (in-there m) = s≤s (pos<len m)

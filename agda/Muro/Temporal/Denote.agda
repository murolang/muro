------------------------------------------------------------------------
-- A fragment process denotes the blocks `compile` allocates.
--
-- `denote` follows `agree`: the same counters, the same environment
-- extension, the same echo slot. It also keeps the place a jump returns
-- to and the coverage of every block on the list `compile` returns.
-- A `smu` allocates nothing. Its name is entered in the table at the
-- place it reaches, including a place that jumps onward.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Denote where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_; _≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Muro.AsyncRec
  using ( Atom; aNat; aBit; aCon; Tag
        ; RProc; rpick0; rpick1; rcover; riget; rmget; rvar
        ; Block; bDone; bStop; bPut; bEcho; bPick0; bPick1; bGet; bCover; bIget; bMget
        ; COut; cok; cfail; Fault; fUnguarded; fFree
        ; compile; compileArms; addNames; lookupN; elemS
        ; REnv; VEnv )
open import Muro.Temporal.Bridge
  using ( Frag; FragPay; FragArm; FragArms
        ; fdone; fstop; fput; fget; fpick0; fpick1; fcover; figet; fmget; fmu; fvar
        ; fnat; fbit; fcon; fecho; farm; farms0; farms1
        ; elab; elabArms; echoOk; echoOkArms; ∧-left; ∧-right
        ; mus; musArms; distinct; fresh; muOk
        ; echoAF; echo-mu )
open import Muro.Temporal.Source
  using ( Pay; pNat; pBit; pCon; pEcho
        ; Arm; aok; SProc; sdone; sstop; sput; sget; spick0; spick1
        ; scover; siget; smget; smu; svar
        ; W; mkW; EnvI; addPend; lookupI; walk; walkArms; findS; asAtom
        ; bnames; bnamesArms
        ; src-echoA )
open W
open import Muro.Temporal.Pic
  using ( Ord; o0; o1; ord-cat; _∈_; here; there; +-idr; ents
        ; ERel; er0; add-rel; Seen; seen-no; seen-yes; lookup-rel
        ; EchoRel; echo-empty; echo-extend
        ; true≢false; ++assoc )
open import Muro.Temporal.Agree
  using ( get-slot; get-names; split-left; split-right; cat-slot; shift-end; sum-len
        ; iget-p-ns; iget-q-ns; iget-q-slot; iget-end
        ; echoA-ok; root-ns )
open import Muro.Temporal.Den

------------------------------------------------------------------------
-- Moving coverage onto the list a parent allocates.
------------------------------------------------------------------------

under : ∀ {xs} {k : ℕ} {blk b : Block} {i : ℕ} →
        (i , b) ∈ xs → (i , b) ∈ ((k , blk) ∷ xs)
under m = there m

onˡ : ∀ {bs1 bs2} {k : ℕ} {blk b : Block} {i : ℕ} →
      (i , b) ∈ bs1 → (i , b) ∈ ((k , blk) ∷ (bs1 ++ bs2))
onˡ m = there (∈++ˡ m)

onʳ : ∀ {bs1 bs2} {k : ℕ} {blk b : Block} {i : ℕ} →
      (i , b) ∈ bs2 → (i , b) ∈ ((k , blk) ∷ (bs1 ++ bs2))
onʳ {bs1} m = there (∈++ʳ {xs = bs1} m)

inˡ : ∀ {bs1 bs2} {i : ℕ} {b : Block} → (i , b) ∈ bs1 → (i , b) ∈ (bs1 ++ bs2)
inˡ m = ∈++ˡ m

inʳ : ∀ {bs1 bs2} {i : ℕ} {b : Block} → (i , b) ∈ bs2 → (i , b) ∈ (bs1 ++ bs2)
inʳ {bs1} m = ∈++ʳ {xs = bs1} m

appendC : ∀ {t u bs} → CovT t bs → CovT u bs → CovT (appendT t u) bs
appendC ct0 cu = cu
appendC (ct1 c ct) cu = ct1 c (appendC ct cu)

appendL : ∀ {t u} → Links t → Links u → Links (appendT t u)
appendL ls0 lu = lu
appendL (ls1 l ix s hs at ls) lu = ls1 l ix s (hosts-grow hs) at (appendL ls lu)

-- Bind `x` at the place `pl` reaches. A jump allocates no block, and the
-- binder is recorded anyway: a later step unfolds it. The equality says
-- the new table is that one entry in front of the table the body returned.
BoundAt : ∀ {P} → String → EnvI → Place P → List (ℕ × Block) → Table → Set
BoundAt {P} x ρ pl bs tab =
  Σ Table (λ t → CovT t bs × Links t ×
            t ≡ t1 {P} x (headIx pl) (slotOf pl) ρ pl tab)

cons-bind : ∀ {P bs suf} (x : String) (ρ : EnvI) (pl : Place P) (c : CovP pl bs)
            (tab : Table) (ct : CovT tab bs) (ls : Links tab) (lk : Link pl) →
            Hosts (t1 {P} x (headIx pl) (slotOf pl) ρ pl tab) pl →
            At suf pl →
            BoundAt x ρ pl bs tab
cons-bind {bs = bs} x ρ pl c tab ct ls lk hs at = go pl c
  where
  add : BoundAt x ρ pl bs tab
  add = t1 x (headIx pl) (slotOf pl) ρ pl tab , ct1 c ct , ls1 lk refl refl hs at ls , refl
  go : ∀ {Q} (ql : Place Q) → CovP ql bs → BoundAt x ρ pl bs tab
  go (p-jump _ _ _ _) _ = add
  go (p-act _ _ _ _ _) _ = add
  go (p-mu _ inner) (cp-mu c2) = go inner c2

bit-atom : ∀ b → asAtom (pBit b) ≡ just (aBit b)
bit-atom false = refl
bit-atom true = refl

------------------------------------------------------------------------
-- What `denote` returns. `Yes` is a successful `walk` and `compile`,
-- together with the place and the table.
------------------------------------------------------------------------

record Yes (P : SProc) (fp : Frag P) (pend : List String) (ρ : EnvI)
           (renv : REnv) (venv : VEnv) (n slot : ℕ) (ns : List String) : Set where
  constructor yesB
  field
    w : W
    bs : List (ℕ × Block)
    wk : walk pend ρ P n slot ≡ just w
    cmp : compile (elab P fp) pend renv venv slot n ≡
            cok (entry w) (next w) (slotN w) bs
    od : Ord n (next w) bs
    end : slotN w ≡ slot + length (bnames P)
    pl : Place P
    tab : Table
    cv : CovP pl bs
    ct : CovT tab bs
    hd : headIx pl ≡ entry w
    sl : slotOf pl ≡ atSlot w
    ev : envOf pl ≡ ρ
    lk : Link pl
    ls : Links tab
    hs : Hosts tab pl
    at : At pend pl
    tn : tnames tab ≡ mus P
    ens : EchoNs ns pl
    al : Align pend pl

record No (P : SProc) (fp : Frag P) (pend : List String) (ρ : EnvI)
          (renv : REnv) (venv : VEnv) (n slot : ℕ) : Set where
  constructor noB
  field
    fault : Fault
    wk : walk pend ρ P n slot ≡ nothing
    cmp : compile (elab P fp) pend renv venv slot n ≡ cfail fault

data Built (P : SProc) (fp : Frag P) (pend : List String) (ρ : EnvI)
           (renv : REnv) (venv : VEnv) (n slot : ℕ) (ns : List String) : Set where
  ok : Yes P fp pend ρ renv venv n slot ns → Built P fp pend ρ renv venv n slot ns
  bad : No P fp pend ρ renv venv n slot → Built P fp pend ρ renv venv n slot ns

record YesA (as : List Arm) (fas : FragArms as) (ρ : EnvI) (renv : REnv)
            (venv : VEnv) (n slot : ℕ) (ns : List String) : Set where
  constructor yesA
  field
    ws : List (String × W)
    n2 s2 : ℕ
    bs : List (ℕ × Block)
    wk : walkArms [] ρ as n slot ≡ just (ws , n2 , s2)
    cmp : compileArms (elabArms as fas) renv venv slot n ≡
            (cok n2 n2 s2 [] , ents ws , bs)
    od : Ord n n2 bs
    end : s2 ≡ slot + length (bnamesArms as)
    dests : ArmPs ρ as ws
    tab : Table
    cv : CovA dests bs
    ct : CovT tab bs
    lka : LinkA dests
    ls : Links tab
    hsa : HostsA tab dests
    ata : AtA dests
    tn : tnames tab ≡ musArms as
    eaa : EchoNsA ns dests
    ala : AlignA dests

record NoA (as : List Arm) (fas : FragArms as) (ρ : EnvI) (renv : REnv)
           (venv : VEnv) (n slot : ℕ) : Set where
  constructor noA
  field
    fault : Fault
    wk : walkArms [] ρ as n slot ≡ nothing
    cmp : compileArms (elabArms as fas) renv venv slot n ≡ (cfail fault , [] , [])

data BuiltA (as : List Arm) (fas : FragArms as) (ρ : EnvI) (renv : REnv)
            (venv : VEnv) (n slot : ℕ) (ns : List String) : Set where
  okA : YesA as fas ρ renv venv n slot ns → BuiltA as fas ρ renv venv n slot ns
  badA : NoA as fas ρ renv venv n slot → BuiltA as fas ρ renv venv n slot ns

------------------------------------------------------------------------
-- One parent block in front of a child's place.
------------------------------------------------------------------------

finish-put :
  ∀ {a atom p fp pend ρ renv venv n slot ns}
  (fq : Frag (sput a p))
  (y : Yes p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv (suc n) slot ns) →
  asAtom a ≡ just atom →
  walk pend ρ (sput a p) n slot ≡
    just (mkW n slot (next (Yes.w y)) (slotN (Yes.w y))) →
  compile (elab (sput a p) fq) pend renv venv slot n ≡
    cok n (next (Yes.w y)) (slotN (Yes.w y))
      ((n , bPut atom (entry (Yes.w y))) ∷ Yes.bs y) →
  Yes (sput a p) fq pend ρ renv venv n slot ns
finish-put {a} {atom} {p} {fp} {pend} {ρ} {renv} {venv} {n} {slot} fq y aeq wk cmp =
  yesB (mkW n slot (next (Yes.w y)) (slotN (Yes.w y)))
       ((n , bPut atom (entry (Yes.w y))) ∷ Yes.bs y)
       wk cmp (o1 (Yes.od y)) (Yes.end y)
       (p-act (d-put n slot a atom (entry (Yes.w y)) p ρw (Yes.w y) aeq
                 (Yes.wk y) refl (Yes.pl y) (Yes.hd y) (Yes.sl y) (Yes.ev y))
              r-put n slot ρ)
       (Yes.tab y)
       (cp-act (c-put here (covP-lift under (Yes.cv y))))
       (covT-lift under (Yes.ct y))
       refl refl refl
       (lk-put refl refl refl (Yes.lk y))
       (Yes.ls y)
       (hs-put (Yes.hs y))
       (at-put refl (Yes.at y))
       (Yes.tn y)
       (en-put (Yes.ens y))
       (al-put refl (Yes.al y))
  where
  ρw = addPend pend n slot ρ

finish-echo :
  ∀ {x p fp pend ρ renv venv ns n slot sX}
  (fq : Frag (sput (pEcho x) p))
  (y : Yes p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv (suc n) slot ns) →
  lookupN x venv ≡ just sX →
  findS x ns ≡ just sX →
  walk pend ρ (sput (pEcho x) p) n slot ≡
    just (mkW n slot (next (Yes.w y)) (slotN (Yes.w y))) →
  compile (elab (sput (pEcho x) p) fq) pend renv venv slot n ≡
    cok n (next (Yes.w y)) (slotN (Yes.w y))
      ((n , bEcho sX (entry (Yes.w y))) ∷ Yes.bs y) →
  Yes (sput (pEcho x) p) fq pend ρ renv venv n slot ns
finish-echo {x} {p} {fp} {pend} {ρ} {renv} {venv} {ns} {n} {slot} {sX} fq y lk fd wk cmp =
  yesB (mkW n slot (next (Yes.w y)) (slotN (Yes.w y)))
       ((n , bEcho sX (entry (Yes.w y))) ∷ Yes.bs y)
       wk cmp (o1 (Yes.od y)) (Yes.end y)
       (p-act (d-echo n slot x ns sX (entry (Yes.w y)) p ρw (Yes.w y) fd
                 (Yes.wk y) refl (Yes.pl y) (Yes.hd y) (Yes.sl y) (Yes.ev y))
              r-echo n slot ρ)
       (Yes.tab y)
       (cp-act (c-echo here (covP-lift under (Yes.cv y))))
       (covT-lift under (Yes.ct y))
       refl refl refl
       (lk-echo refl refl refl (Yes.lk y))
       (Yes.ls y)
       (hs-echo (Yes.hs y))
       (at-echo refl (Yes.at y))
       (Yes.tn y)
       (en-echo refl (Yes.ens y))
       (al-echo refl (Yes.al y))
  where
  ρw = addPend pend n slot ρ

finish-pick0 :
  ∀ {p fp pend ρ renv venv n slot ns}
  (fq : Frag (spick0 p))
  (y : Yes p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv (suc n) slot ns) →
  walk pend ρ (spick0 p) n slot ≡
    just (mkW n slot (next (Yes.w y)) (slotN (Yes.w y))) →
  compile (elab (spick0 p) fq) pend renv venv slot n ≡
    cok n (next (Yes.w y)) (slotN (Yes.w y))
      ((n , bPick0 (entry (Yes.w y))) ∷ Yes.bs y) →
  Yes (spick0 p) fq pend ρ renv venv n slot ns
finish-pick0 {p} {fp} {pend} {ρ} {renv} {venv} {n} {slot} fq y wk cmp =
  yesB (mkW n slot (next (Yes.w y)) (slotN (Yes.w y)))
       ((n , bPick0 (entry (Yes.w y))) ∷ Yes.bs y)
       wk cmp (o1 (Yes.od y)) (Yes.end y)
       (p-act (d-pick0 n slot (entry (Yes.w y)) p ρw (Yes.w y)
                 (Yes.wk y) refl (Yes.pl y) (Yes.hd y) (Yes.sl y) (Yes.ev y))
              r-pick0 n slot ρ)
       (Yes.tab y)
       (cp-act (c-pick0 here (covP-lift under (Yes.cv y))))
       (covT-lift under (Yes.ct y))
       refl refl refl
       (lk-pick0 refl refl refl (Yes.lk y))
       (Yes.ls y)
       (hs-pick0 (Yes.hs y))
       (at-pick0 refl (Yes.at y))
       (Yes.tn y)
       (en-pick0 (Yes.ens y))
       (al-pick0 refl (Yes.al y))
  where
  ρw = addPend pend n slot ρ

finish-pick1 :
  ∀ {p fp pend ρ renv venv n slot ns}
  (fq : Frag (spick1 p))
  (y : Yes p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv (suc n) slot ns) →
  walk pend ρ (spick1 p) n slot ≡
    just (mkW n slot (next (Yes.w y)) (slotN (Yes.w y))) →
  compile (elab (spick1 p) fq) pend renv venv slot n ≡
    cok n (next (Yes.w y)) (slotN (Yes.w y))
      ((n , bPick1 (entry (Yes.w y))) ∷ Yes.bs y) →
  Yes (spick1 p) fq pend ρ renv venv n slot ns
finish-pick1 {p} {fp} {pend} {ρ} {renv} {venv} {n} {slot} fq y wk cmp =
  yesB (mkW n slot (next (Yes.w y)) (slotN (Yes.w y)))
       ((n , bPick1 (entry (Yes.w y))) ∷ Yes.bs y)
       wk cmp (o1 (Yes.od y)) (Yes.end y)
       (p-act (d-pick1 n slot (entry (Yes.w y)) p ρw (Yes.w y)
                 (Yes.wk y) refl (Yes.pl y) (Yes.hd y) (Yes.sl y) (Yes.ev y))
              r-pick1 n slot ρ)
       (Yes.tab y)
       (cp-act (c-pick1 here (covP-lift under (Yes.cv y))))
       (covT-lift under (Yes.ct y))
       refl refl refl
       (lk-pick1 refl refl refl (Yes.lk y))
       (Yes.ls y)
       (hs-pick1 (Yes.hs y))
       (at-pick1 refl (Yes.at y))
       (Yes.tn y)
       (en-pick1 (Yes.ens y))
       (al-pick1 refl (Yes.al y))
  where
  ρw = addPend pend n slot ρ

finish-get :
  ∀ {t x p fp pend ρ renv venv n slot ns}
  (fq : Frag (sget t x p))
  (y : Yes p fp [] (addPend pend n slot ρ) (addNames pend n renv)
         ((x , slot) ∷ venv) (suc n) (suc slot) ns) →
  walk pend ρ (sget t x p) n slot ≡
    just (mkW n slot (next (Yes.w y)) (slotN (Yes.w y))) →
  compile (elab (sget t x p) fq) pend renv venv slot n ≡
    cok n (next (Yes.w y)) (slotN (Yes.w y))
      ((n , bGet t slot (entry (Yes.w y))) ∷ Yes.bs y) →
  Yes (sget t x p) fq pend ρ renv venv n slot ns
finish-get {t} {x} {p} {fp} {pend} {ρ} {renv} {venv} {n} {slot} fq y wk cmp =
  yesB (mkW n slot (next (Yes.w y)) (slotN (Yes.w y)))
       ((n , bGet t slot (entry (Yes.w y))) ∷ Yes.bs y)
       wk cmp (o1 (Yes.od y))
       (shift-end {slot} {slotN (Yes.w y)} {length (bnames p)} (Yes.end y))
       (p-act (d-get n slot t x (entry (Yes.w y)) p ρw (Yes.w y)
                 (Yes.wk y) refl (Yes.pl y) (Yes.hd y) (Yes.sl y) (Yes.ev y))
              r-get n slot ρ)
       (Yes.tab y)
       (cp-act (c-get here (covP-lift under (Yes.cv y))))
       (covT-lift under (Yes.ct y))
       refl refl refl
       (lk-get refl refl refl (Yes.lk y))
       (Yes.ls y)
       (hs-get (Yes.hs y))
       (at-get refl (Yes.at y))
       (Yes.tn y)
       (en-get (Yes.ens y))
       (al-get refl (Yes.al y))
  where
  ρw = addPend pend n slot ρ

------------------------------------------------------------------------
-- `walk` and `compile` of the forms whose lemmas are not in `Den`.
------------------------------------------------------------------------

spick0-walk : ∀ {pend ρ p n s w} →
              walk [] (addPend pend n s ρ) p (suc n) s ≡ just w →
              walk pend ρ (spick0 p) n s ≡ just (mkW n s (next w) (slotN w))
spick0-walk eq rewrite eq = refl

spick0-miss : ∀ {pend ρ p n s} →
              walk [] (addPend pend n s ρ) p (suc n) s ≡ nothing →
              walk pend ρ (spick0 p) n s ≡ nothing
spick0-miss eq rewrite eq = refl

pick0-cmp : ∀ {pend renv venv slot n q e nxt slot' bs} →
            compile q [] (addNames pend n renv) venv slot (suc n) ≡
              cok e nxt slot' bs →
            compile (rpick0 q) pend renv venv slot n ≡
              cok n nxt slot' ((n , bPick0 e) ∷ bs)
pick0-cmp eq rewrite eq = refl

pick0-miss : ∀ {pend renv venv slot n q f} →
             compile q [] (addNames pend n renv) venv slot (suc n) ≡ cfail f →
             compile (rpick0 q) pend renv venv slot n ≡ cfail f
pick0-miss eq rewrite eq = refl

spick1-walk : ∀ {pend ρ p n s w} →
              walk [] (addPend pend n s ρ) p (suc n) s ≡ just w →
              walk pend ρ (spick1 p) n s ≡ just (mkW n s (next w) (slotN w))
spick1-walk eq rewrite eq = refl

spick1-miss : ∀ {pend ρ p n s} →
              walk [] (addPend pend n s ρ) p (suc n) s ≡ nothing →
              walk pend ρ (spick1 p) n s ≡ nothing
spick1-miss eq rewrite eq = refl

pick1-cmp : ∀ {pend renv venv slot n q e nxt slot' bs} →
            compile q [] (addNames pend n renv) venv slot (suc n) ≡
              cok e nxt slot' bs →
            compile (rpick1 q) pend renv venv slot n ≡
              cok n nxt slot' ((n , bPick1 e) ∷ bs)
pick1-cmp eq rewrite eq = refl

pick1-miss : ∀ {pend renv venv slot n q f} →
             compile q [] (addNames pend n renv) venv slot (suc n) ≡ cfail f →
             compile (rpick1 q) pend renv venv slot n ≡ cfail f
pick1-miss eq rewrite eq = refl

cover-walk-bad : ∀ {pend ρ p q n s} →
                 walk [] (addPend pend n s ρ) p (suc n) s ≡ nothing →
                 walk pend ρ (scover p q) n s ≡ nothing
cover-walk-bad eq rewrite eq = refl

cover-cmp-bad : ∀ {pend renv venv slot n q1 q2 f} →
                compile q1 [] (addNames pend n renv) venv slot (suc n) ≡ cfail f →
                compile (rcover q1 q2) pend renv venv slot n ≡ cfail f
cover-cmp-bad eq rewrite eq = refl

cover-walk-miss : ∀ {pend ρ p q n s w} →
                  walk [] (addPend pend n s ρ) p (suc n) s ≡ just w →
                  walk [] (addPend pend n s ρ) q (next w) (slotN w) ≡ nothing →
                  walk pend ρ (scover p q) n s ≡ nothing
cover-walk-miss eq1 eq2 rewrite eq1 | eq2 = refl

cover-cmp-miss : ∀ {pend renv venv slot n q1 q2 e nxt slot' bs f} →
                 compile q1 [] (addNames pend n renv) venv slot (suc n) ≡
                   cok e nxt slot' bs →
                 compile q2 [] (addNames pend n renv) venv slot' nxt ≡ cfail f →
                 compile (rcover q1 q2) pend renv venv slot n ≡ cfail f
cover-cmp-miss eq1 eq2 rewrite eq1 | eq2 = refl

cover-walk-hit : ∀ {pend ρ p q n s w1 w2} →
                 walk [] (addPend pend n s ρ) p (suc n) s ≡ just w1 →
                 walk [] (addPend pend n s ρ) q (next w1) (slotN w1) ≡ just w2 →
                 walk pend ρ (scover p q) n s ≡
                   just (mkW n s (next w2) (slotN w2))
cover-walk-hit eq1 eq2 rewrite eq1 | eq2 = refl

cover-cmp-hit : ∀ {pend renv venv slot n q1 q2 e1 nxt1 slot1 bs1 e2 nxt2 slot2 bs2} →
                compile q1 [] (addNames pend n renv) venv slot (suc n) ≡
                  cok e1 nxt1 slot1 bs1 →
                compile q2 [] (addNames pend n renv) venv slot1 nxt1 ≡
                  cok e2 nxt2 slot2 bs2 →
                compile (rcover q1 q2) pend renv venv slot n ≡
                  cok n nxt2 slot2 ((n , bCover e1 e2) ∷ bs1 ++ bs2)
cover-cmp-hit eq1 eq2 rewrite eq1 | eq2 = refl

iget-walk-bad : ∀ {pend ρ x p q n s} →
                walk [] (addPend pend n s ρ) p (suc n) (suc s) ≡ nothing →
                walk pend ρ (siget x p q) n s ≡ nothing
iget-walk-bad eq rewrite eq = refl

iget-cmp-bad : ∀ {pend renv venv slot n x q1 q2 f} →
               compile q1 [] (addNames pend n renv) ((x , slot) ∷ venv) (suc slot) (suc n) ≡
                 cfail f →
               compile (riget x q1 q2) pend renv venv slot n ≡ cfail f
iget-cmp-bad eq rewrite eq = refl

iget-walk-miss : ∀ {pend ρ x p q n s w} →
                 walk [] (addPend pend n s ρ) p (suc n) (suc s) ≡ just w →
                 walk [] (addPend pend n s ρ) q (next w) (slotN w) ≡ nothing →
                 walk pend ρ (siget x p q) n s ≡ nothing
iget-walk-miss eq1 eq2 rewrite eq1 | eq2 = refl

iget-cmp-miss : ∀ {pend renv venv slot n x q1 q2 e nxt slot' bs f} →
                compile q1 [] (addNames pend n renv) ((x , slot) ∷ venv) (suc slot) (suc n) ≡
                  cok e nxt slot' bs →
                compile q2 [] (addNames pend n renv) ((x , slot) ∷ venv) slot' nxt ≡ cfail f →
                compile (riget x q1 q2) pend renv venv slot n ≡ cfail f
iget-cmp-miss eq1 eq2 rewrite eq1 | eq2 = refl

iget-walk-hit : ∀ {pend ρ x p q n s w1 w2} →
                walk [] (addPend pend n s ρ) p (suc n) (suc s) ≡ just w1 →
                walk [] (addPend pend n s ρ) q (next w1) (slotN w1) ≡ just w2 →
                walk pend ρ (siget x p q) n s ≡
                  just (mkW n s (next w2) (slotN w2))
iget-walk-hit eq1 eq2 rewrite eq1 | eq2 = refl

iget-cmp-hit : ∀ {pend renv venv slot n x q1 q2 e1 nxt1 slot1 bs1 e2 nxt2 slot2 bs2} →
               compile q1 [] (addNames pend n renv) ((x , slot) ∷ venv) (suc slot) (suc n) ≡
                 cok e1 nxt1 slot1 bs1 →
               compile q2 [] (addNames pend n renv) ((x , slot) ∷ venv) slot1 nxt1 ≡
                 cok e2 nxt2 slot2 bs2 →
               compile (riget x q1 q2) pend renv venv slot n ≡
                 cok n nxt2 slot2 ((n , bIget slot e1 e2) ∷ bs1 ++ bs2)
iget-cmp-hit eq1 eq2 rewrite eq1 | eq2 = refl

arm-walk-bad : ∀ {ρ y p as n s} →
               walk [] ρ p n s ≡ nothing →
               walkArms [] ρ (aok y p ∷ as) n s ≡ nothing
arm-walk-bad eq rewrite eq = refl

arm-cmp-bad : ∀ {renv venv slot n y q rest f} →
              compile q [] renv venv slot n ≡ cfail f →
              compileArms ((y , q) ∷ rest) renv venv slot n ≡ (cfail f , [] , [])
arm-cmp-bad eq rewrite eq = refl

arm-walk-miss : ∀ {ρ y p as n s w} →
                walk [] ρ p n s ≡ just w →
                walkArms [] ρ as (next w) (slotN w) ≡ nothing →
                walkArms [] ρ (aok y p ∷ as) n s ≡ nothing
arm-walk-miss eq1 eq2 rewrite eq1 | eq2 = refl

arm-cmp-miss : ∀ {renv venv slot n y q rest e nxt slot1 bs1 f} →
               compile q [] renv venv slot n ≡ cok e nxt slot1 bs1 →
               compileArms rest renv venv slot1 nxt ≡ (cfail f , [] , []) →
               compileArms ((y , q) ∷ rest) renv venv slot n ≡ (cfail f , [] , [])
arm-cmp-miss eq1 eq2 rewrite eq1 | eq2 = refl

arm-walk-hit : ∀ {ρ y p as n s w ws n2 s2} →
               walk [] ρ p n s ≡ just w →
               walkArms [] ρ as (next w) (slotN w) ≡ just (ws , n2 , s2) →
               walkArms [] ρ (aok y p ∷ as) n s ≡ just ((y , w) ∷ ws , n2 , s2)
arm-walk-hit eq1 eq2 rewrite eq1 | eq2 = refl

arm-cmp-hit : ∀ {renv venv slot n y q rest e nxt slot1 bs1 n2 s2 named bs2} →
              compile q [] renv venv slot n ≡ cok e nxt slot1 bs1 →
              compileArms rest renv venv slot1 nxt ≡ (cok n2 n2 s2 [] , named , bs2) →
              compileArms ((y , q) ∷ rest) renv venv slot n ≡
                (cok n2 n2 s2 [] , (y , e) ∷ named , bs1 ++ bs2)
arm-cmp-hit eq1 eq2 rewrite eq1 | eq2 = refl

mget-walk-bad : ∀ {pend ρ t x as n s} →
                walkArms [] (addPend pend n s ρ) as (suc n) (suc s) ≡ nothing →
                walk pend ρ (smget t x as) n s ≡ nothing
mget-walk-bad eq rewrite eq = refl

mget-cmp-bad : ∀ {pend renv venv slot n t x qs f} →
               compileArms qs (addNames pend n renv) ((x , slot) ∷ venv) (suc slot) (suc n) ≡
                 (cfail f , [] , []) →
               compile (rmget t x qs) pend renv venv slot n ≡ cfail f
mget-cmp-bad eq rewrite eq = refl

mget-walk-hit : ∀ {pend ρ t x as n s ws n2 s2} →
                walkArms [] (addPend pend n s ρ) as (suc n) (suc s) ≡ just (ws , n2 , s2) →
                walk pend ρ (smget t x as) n s ≡ just (mkW n s n2 s2)
mget-walk-hit eq rewrite eq = refl

mget-cmp-hit : ∀ {pend renv venv slot n t x qs n2 s2 named bs} →
               compileArms qs (addNames pend n renv) ((x , slot) ∷ venv) (suc slot) (suc n) ≡
                 (cok n2 n2 s2 [] , named , bs) →
               compile (rmget t x qs) pend renv venv slot n ≡
                 cok n n2 s2 ((n , bMget t slot named) ∷ bs)
mget-cmp-hit eq rewrite eq = refl

var-walk-ung : ∀ {pend ρ y n s} → elemS y pend ≡ true →
               walk pend ρ (svar y) n s ≡ nothing
var-walk-ung eq rewrite eq = refl

var-cmp-ung : ∀ {pend renv venv slot n y} → elemS y pend ≡ true →
              compile (rvar y) pend renv venv slot n ≡ cfail fUnguarded
var-cmp-ung eq rewrite eq = refl

var-walk-no : ∀ {pend ρ y n s} → elemS y pend ≡ false → lookupI y ρ ≡ nothing →
              walk pend ρ (svar y) n s ≡ nothing
var-walk-no eqe eql rewrite eqe | eql = refl

var-cmp-no : ∀ {pend renv venv slot n y} → elemS y pend ≡ false →
             lookupN y renv ≡ nothing →
             compile (rvar y) pend renv venv slot n ≡ cfail fFree
var-cmp-no eqe eql rewrite eqe | eql = refl

var-walk-yes : ∀ {pend ρ y n s i s0} → elemS y pend ≡ false →
               lookupI y ρ ≡ just (i , s0) →
               walk pend ρ (svar y) n s ≡ just (mkW i s0 n s)
var-walk-yes eqe eql rewrite eqe | eql = refl

var-cmp-yes : ∀ {pend renv venv slot n y i} → elemS y pend ≡ false →
              lookupN y renv ≡ just i →
              compile (rvar y) pend renv venv slot n ≡ cok i n slot []
var-cmp-yes eqe eql rewrite eqe | eql = refl

------------------------------------------------------------------------
-- A binder is not in the environment it was denoted under. `muOk`
-- says the pending names, the environment, and the binders still to
-- come are pairwise distinct, so peeling one cannot shadow another.
------------------------------------------------------------------------

namesI : EnvI → List String
namesI [] = []
namesI ((x , _ , _) ∷ ρ) = x ∷ namesI ρ

names-add : ∀ xs n s ρ → namesI (addPend xs n s ρ) ≡ xs ++ namesI ρ
names-add [] n s ρ = refl
names-add (x ∷ xs) n s ρ = cong (x ∷_) (names-add xs n s ρ)

miss-names : ∀ ρ y → elemS y (namesI ρ) ≡ false → lookupI y ρ ≡ nothing
miss-names [] y eq = refl
miss-names ((x , i , s) ∷ ρ) y eq = go (y == x) refl eq
  where
  go : (b : Bool) → (y == x) ≡ b → elemS y (x ∷ namesI ρ) ≡ false →
       lookupI y ((x , i , s) ∷ ρ) ≡ nothing
  go true eqy eq2 rewrite eqy = ⊥-elim (true≢false eq2)
  go false eqy eq2 rewrite eqy = miss-names ρ y eq2

data AllFresh (x : String) : List String → Set where
  af0 : AllFresh x []
  af1 : ∀ {y ys} → (x == y) ≡ false → AllFresh x ys → AllFresh x (y ∷ ys)

data Dis : List String → Set where
  d0 : Dis []
  d1 : ∀ {x xs} → AllFresh x xs → Dis xs → Dis (x ∷ xs)

fresh→ : ∀ x xs → fresh x xs ≡ true → AllFresh x xs
fresh→ x [] eq = af0
fresh→ x (y ∷ ys) eq = go (x == y) refl eq
  where
  go : (b : Bool) → (x == y) ≡ b → fresh x (y ∷ ys) ≡ true → AllFresh x (y ∷ ys)
  go true eqy eq2 rewrite eqy = ⊥-elim (true≢false (sym eq2))
  go false eqy eq2 rewrite eqy = af1 eqy (fresh→ x ys eq2)

dis← : ∀ xs → distinct xs ≡ true → Dis xs
dis← [] eq = d0
dis← (x ∷ xs) eq = d1 (fresh→ x xs (∧-left eq)) (dis← xs (∧-right eq))

fresh← : ∀ {x xs} → AllFresh x xs → fresh x xs ≡ true
fresh← af0 = refl
fresh← {x} (af1 {y} {ys} eq f) rewrite eq = fresh← {x} {ys} f

dis→ : ∀ xs → Dis xs → distinct xs ≡ true
dis→ [] d0 = refl
dis→ (x ∷ xs) (d1 f d) rewrite fresh← f | dis→ xs d = refl

==-sym : ∀ x y → (x == y) ≡ (y == x)
==-sym x y with x ≟ y | y ≟ x
... | yes _ | yes _ = refl
... | yes p | no ¬q = ⊥-elim (¬q (sym p))
... | no ¬p | yes q = ⊥-elim (¬p (sym q))
... | no _ | no _ = refl

data Cross : List String → List String → Set where
  cr0 : ∀ {ys} → Cross [] ys
  cr1 : ∀ {x xs ys} → AllFresh x ys → Cross xs ys → Cross (x ∷ xs) ys

af-split : ∀ {x} xs ys → AllFresh x (xs ++ ys) → AllFresh x xs × AllFresh x ys
af-split [] ys f = af0 , f
af-split (z ∷ xs) ys (af1 eq f) =
  let fl , fr = af-split xs ys f in af1 eq fl , fr

af-join : ∀ {x xs ys} → AllFresh x xs → AllFresh x ys → AllFresh x (xs ++ ys)
af-join af0 g = g
af-join (af1 eq f) g = af1 eq (af-join f g)

af-tail : ∀ {x y ys} → AllFresh x (y ∷ ys) → AllFresh x ys
af-tail (af1 _ f) = f

fresh-one : ∀ {x y ys} → AllFresh x (y ∷ ys) → (y == x) ≡ false
fresh-one {x} {y} (af1 eq _) rewrite ==-sym x y = eq

col : ∀ xs {y ys} → Cross xs (y ∷ ys) → AllFresh y xs
col [] _ = af0
col (x ∷ xs) (cr1 f cr) = af1 (fresh-one f) (col xs cr)

cross-tail : ∀ xs {y ys} → Cross xs (y ∷ ys) → Cross xs ys
cross-tail [] cr0 = cr0
cross-tail (x ∷ xs) (cr1 f cr) = cr1 (af-tail f) (cross-tail xs cr)

cross-sym : ∀ xs ys → Cross xs ys → Cross ys xs
cross-sym xs [] cr = cr0
cross-sym xs (y ∷ ys) cr =
  cr1 (col xs cr) (cross-sym xs ys (cross-tail xs cr))

cross-left : ∀ xs ys zs → Cross xs (ys ++ zs) → Cross xs ys
cross-left [] ys zs cr = cr0
cross-left (x ∷ xs) ys zs (cr1 f cr) =
  cr1 (proj₁ (af-split ys zs f)) (cross-left xs ys zs cr)

cross-right : ∀ xs ys zs → Cross xs (ys ++ zs) → Cross xs zs
cross-right [] ys zs cr = cr0
cross-right (x ∷ xs) ys zs (cr1 f cr) =
  cr1 (proj₂ (af-split ys zs f)) (cross-right xs ys zs cr)

cross-cat : ∀ xs ys zs → Cross xs zs → Cross ys zs → Cross (xs ++ ys) zs
cross-cat [] ys zs cx cy = cy
cross-cat (x ∷ xs) ys zs (cr1 f cx) cy =
  cr1 f (cross-cat xs ys zs cx cy)

dis-split : ∀ xs ys → Dis (xs ++ ys) → Dis xs × Dis ys × Cross xs ys
dis-split [] ys d = d0 , d , cr0
dis-split (x ∷ xs) ys (d1 f d) =
  let dx , dy , cr = dis-split xs ys d
      fl , fr = af-split xs ys f
  in d1 fl dx , dy , cr1 fr cr

dis-join : ∀ xs ys → Dis xs → Dis ys → Cross xs ys → Dis (xs ++ ys)
dis-join [] ys dx dy cr = dy
dis-join (x ∷ xs) ys (d1 f dx) dy (cr1 fy cr) =
  d1 (af-join f fy) (dis-join xs ys dx dy cr)

sep-cont : ∀ ρ pend ms →
           Dis (namesI ρ ++ (pend ++ ms)) →
           Dis ((pend ++ namesI ρ) ++ ms)
sep-cont ρ pend ms d =
  let a , bc , cab = dis-split (namesI ρ) (pend ++ ms) d
      b , c , cbc = dis-split pend ms bc
      cabB = cross-left (namesI ρ) pend ms cab
      cabC = cross-right (namesI ρ) pend ms cab
      ba = cross-sym (namesI ρ) pend cabB
  in dis-join (pend ++ namesI ρ) ms
       (dis-join pend (namesI ρ) b a ba) c
       (cross-cat pend (namesI ρ) ms cbc cabC)

sep-cont-b : ∀ ρ pend ms →
             distinct (namesI ρ ++ (pend ++ ms)) ≡ true →
             distinct ((pend ++ namesI ρ) ++ ms) ≡ true
sep-cont-b ρ pend ms eq =
  dis→ ((pend ++ namesI ρ) ++ ms)
       (sep-cont ρ pend ms (dis← (namesI ρ ++ (pend ++ ms)) eq))

rot-eq : ∀ {a x} B C → AllFresh a (B ++ (x ∷ C)) → (a == x) ≡ false
rot-eq [] C (af1 eq _) = eq
rot-eq (b ∷ B) C (af1 _ f) = rot-eq B C f

rot-rest : ∀ {a x} B C → AllFresh a (B ++ (x ∷ C)) → AllFresh a (B ++ C)
rot-rest [] C (af1 _ f) = f
rot-rest (b ∷ B) C (af1 eq f) = af1 eq (rot-rest B C f)

af-rot : ∀ {a x} B C → AllFresh a (B ++ (x ∷ C)) → AllFresh a (x ∷ (B ++ C))
af-rot B C f = af1 (rot-eq B C f) (rot-rest B C f)

cross-rot : ∀ A {x} B C → Cross A (B ++ (x ∷ C)) → Cross A (x ∷ (B ++ C))
cross-rot [] B C cr = cr0
cross-rot (a ∷ A) {x} B C (cr1 f cr) =
  cr1 (af-rot {x = x} B C f) (cross-rot A {x} B C cr)

bubble : ∀ A B C x →
         Dis (A ++ (B ++ (x ∷ C))) →
         Dis (A ++ (x ∷ (B ++ C)))
bubble A B C x d =
  let a , rest , car = dis-split A (B ++ (x ∷ C)) d
      b , xc , cb = dis-split B (x ∷ C) rest
      fx = af-of xc
      dc = tail-of xc
      xb = col B cb
      bc = cross-tail B cb
      body = d1 (af-join xb fx) (dis-join B C b dc bc)
      cross = cross-rot A B C car
  in dis-join A (x ∷ (B ++ C)) a body cross
  where
  af-of : Dis (x ∷ C) → AllFresh x C
  af-of (d1 f _) = f
  tail-of : Dis (x ∷ C) → Dis C
  tail-of (d1 _ dC) = dC

sep-mu-b : ∀ ρ pend x ms →
           distinct (namesI ρ ++ (pend ++ (x ∷ ms))) ≡ true →
           distinct (namesI ρ ++ (x ∷ (pend ++ ms))) ≡ true
sep-mu-b ρ pend x ms eq =
  dis→ (namesI ρ ++ (x ∷ (pend ++ ms)))
       (bubble (namesI ρ) pend ms x
         (dis← (namesI ρ ++ (pend ++ (x ∷ ms))) eq))

sep-side : ∀ pre ms1 ms2 →
           Dis (pre ++ (ms1 ++ ms2)) →
           Dis (pre ++ ms1) × Dis (pre ++ ms2)
sep-side pre ms1 ms2 d =
  let p , both , cp = dis-split pre (ms1 ++ ms2) d
      m1 , m2 , _ = dis-split ms1 ms2 both
      c1 = cross-left pre ms1 ms2 cp
      c2 = cross-right pre ms1 ms2 cp
  in dis-join pre ms1 p m1 c1 , dis-join pre ms2 p m2 c2

-- A name fresh for a list does not occur in it.
not-elem : ∀ {y} xs → AllFresh y xs → elemS y xs ≡ false
not-elem [] af0 = refl
not-elem {y} (z ∷ zs) (af1 eq f) = go (y == z) refl eq f
  where
  go : (b : Bool) → (y == z) ≡ b → (y == z) ≡ false → AllFresh y zs →
       elemS y (z ∷ zs) ≡ false
  go true eqy eq2 _ rewrite eqy = ⊥-elim (true≢false eq2)
  go false eqy _ f rewrite eqy = not-elem {y} zs f

-- The binder about to be peeled is not in the environment.
pin-miss : ∀ ρ pend x ms →
           distinct (namesI ρ ++ (pend ++ (x ∷ ms))) ≡ true →
           lookupI x ρ ≡ nothing
pin-miss ρ pend x ms eq =
  miss-names ρ x
    (not-elem {y = x} (namesI ρ)
      (col (namesI ρ) {y = x} {ys = pend ++ ms}
        (cross-rot (namesI ρ) {x = x} pend ms
          (proj₂ (proj₂
            (dis-split (namesI ρ) (pend ++ (x ∷ ms))
              (dis← (namesI ρ ++ (pend ++ (x ∷ ms))) eq)))))))

-- A continuation is denoted under the pending names pushed into ρ.
cont-sep : ∀ pend n s ρ ms →
           distinct (namesI ρ ++ (pend ++ ms)) ≡ true →
           distinct (namesI (addPend pend n s ρ) ++ ms) ≡ true
cont-sep pend n s ρ ms eq rewrite names-add pend n s ρ =
  sep-cont-b ρ pend ms eq

-- The body of a mu is denoted with the binder in front of the pending list.
mu-sep : ∀ ρ pend x ms →
         distinct (namesI ρ ++ (pend ++ (x ∷ ms))) ≡ true →
         distinct (namesI ρ ++ ((x ∷ pend) ++ ms)) ≡ true
mu-sep ρ pend x ms eq = sep-mu-b ρ pend x ms eq

-- The two branches of a cover, an iget, or an arm list.
side-b : ∀ pre ms1 ms2 →
         distinct (pre ++ (ms1 ++ ms2)) ≡ true →
         distinct (pre ++ ms1) ≡ true × distinct (pre ++ ms2) ≡ true
side-b pre ms1 ms2 eq =
  let l , r = sep-side pre ms1 ms2 (dis← (pre ++ (ms1 ++ ms2)) eq)
  in dis→ (pre ++ ms1) l , dis→ (pre ++ ms2) r

-- The body's environment is the environment the mu was denoted under.
pin-of : ∀ {p fp renv venv n slot ns} {x : String} {pend : List String}
           {ρ : EnvI} {ms : List String} →
         (y : Yes p fp (x ∷ pend) ρ renv venv n slot ns) →
         distinct (namesI ρ ++ (pend ++ (x ∷ ms))) ≡ true →
         lookupI x (envOf (Yes.pl y)) ≡ nothing
pin-of {x = x} {pend = pend} {ρ = ρ} {ms = ms} y eq rewrite Yes.ev y =
  pin-miss ρ pend x ms eq

names-join : ∀ {t u ms1 ms2} →
             tnames t ≡ ms1 → tnames u ≡ ms2 →
             tnames (appendT t u) ≡ ms1 ++ ms2
names-join {t} {u} eq1 eq2 = trans (tnames-append t u) (both eq1 eq2)
  where
  both : ∀ {a b c d : List String} → a ≡ b → c ≡ d → a ++ c ≡ b ++ d
  both refl refl = refl

------------------------------------------------------------------------
-- The denotation. Structural on the process and on the arm list.
-- `sep` says the environment, the pending names, and the binders still
-- to come are pairwise distinct. At the root it is `muOk`.
------------------------------------------------------------------------

mutual
  denote : (P : SProc) (fp : Frag P) (pend : List String) (ρ : EnvI) (renv : REnv)
           (venv : VEnv) (ns scope pre post : List String) (n slot : ℕ) →
           ERel ρ renv → EchoRel venv ns scope →
           echoOk ns scope P ≡ true →
           slot ≡ length pre →
           ns ≡ pre ++ bnames P ++ post →
           distinct (namesI ρ ++ (pend ++ mus P)) ≡ true →
           Built P fp pend ρ renv venv n slot ns

  denote sdone fdone pend ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    ok (yesB (mkW n slot (suc n) slot) ((n , bDone) ∷ []) refl refl (o1 o0)
          (sym (+-idr slot))
          (p-act (d-done n) r-done n slot ρ) t0 (cp-act (c-done here)) ct0 refl refl refl
          (lk-done refl) ls0 hs-done at-done refl en-done al-done)
  denote sstop fstop pend ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    ok (yesB (mkW n slot (suc n) slot) ((n , bStop) ∷ []) refl refl (o1 o0)
          (sym (+-idr slot))
          (p-act (d-stop n) r-stop n slot ρ) t0 (cp-act (c-stop here)) ct0 refl refl refl
          (lk-stop refl) ls0 hs-stop at-stop refl en-stop al-stop)

  denote (sput .(pNat a) p) (fput (fnat a) fp) pend ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    on (denote p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv
          ns scope pre post (suc n) slot (add-rel pend n slot rel) er (∧-right eok) seq nseq (cont-sep pend n slot ρ (mus p) sep))
    where
    on : Built p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv (suc n) slot ns →
         Built (sput (pNat a) p) (fput (fnat a) fp) pend ρ renv venv n slot ns
    on (bad (noB f wk cmp)) =
      bad (noB f
        (sput-miss {pend = pend} {ρ = ρ} {a = pNat a} {p = p} {n = n} {s = slot} wk)
        (put-miss {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                  {q = elab p fp} {atom = aNat a} {f = f} cmp))
    on (ok y) =
      ok (finish-put (fput (fnat a) fp) y refl
        (sput-walk {pend = pend} {ρ = ρ} {a = pNat a} {p = p} {n = n} {s = slot}
                   {w = Yes.w y} (Yes.wk y))
        (put-cmp {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                 {q = elab p fp} {atom = aNat a}
                 {e = entry (Yes.w y)} {next = next (Yes.w y)}
                 {slot' = slotN (Yes.w y)} {bs = Yes.bs y} (Yes.cmp y)))

  denote (sput .(pBit b) p) (fput (fbit b) fp) pend ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    on (denote p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv
          ns scope pre post (suc n) slot (add-rel pend n slot rel) er (∧-right eok) seq nseq (cont-sep pend n slot ρ (mus p) sep))
    where
    on : Built p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv (suc n) slot ns →
         Built (sput (pBit b) p) (fput (fbit b) fp) pend ρ renv venv n slot ns
    on (bad (noB f wk cmp)) =
      bad (noB f
        (sput-miss {pend = pend} {ρ = ρ} {a = pBit b} {p = p} {n = n} {s = slot} wk)
        (put-miss {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                  {q = elab p fp} {atom = aBit b} {f = f} cmp))
    on (ok y) =
      ok (finish-put (fput (fbit b) fp) y (bit-atom b)
        (sput-walk {pend = pend} {ρ = ρ} {a = pBit b} {p = p} {n = n} {s = slot}
                   {w = Yes.w y} (Yes.wk y))
        (put-cmp {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                 {q = elab p fp} {atom = aBit b}
                 {e = entry (Yes.w y)} {next = next (Yes.w y)}
                 {slot' = slotN (Yes.w y)} {bs = Yes.bs y} (Yes.cmp y)))

  denote (sput .(pCon y) p) (fput (fcon y) fp) pend ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    on (denote p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv
          ns scope pre post (suc n) slot (add-rel pend n slot rel) er (∧-right eok) seq nseq (cont-sep pend n slot ρ (mus p) sep))
    where
    on : Built p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv (suc n) slot ns →
         Built (sput (pCon y) p) (fput (fcon y) fp) pend ρ renv venv n slot ns
    on (bad (noB f wk cmp)) =
      bad (noB f
        (sput-miss {pend = pend} {ρ = ρ} {a = pCon y} {p = p} {n = n} {s = slot} wk)
        (put-miss {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                  {q = elab p fp} {atom = aCon y} {f = f} cmp))
    on (ok yb) =
      ok (finish-put (fput (fcon y) fp) yb refl
        (sput-walk {pend = pend} {ρ = ρ} {a = pCon y} {p = p} {n = n} {s = slot}
                   {w = Yes.w yb} (Yes.wk yb))
        (put-cmp {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                 {q = elab p fp} {atom = aCon y}
                 {e = entry (Yes.w yb)} {next = next (Yes.w yb)}
                 {slot' = slotN (Yes.w yb)} {bs = Yes.bs yb} (Yes.cmp yb)))

  denote (sput .(pEcho x) p) (fput (fecho x) fp) pend ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    on heard
       (denote p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv
          ns scope pre post (suc n) slot (add-rel pend n slot rel) er (∧-right eok) seq nseq (cont-sep pend n slot ρ (mus p) sep))
    where
    scopeOk = ∧-left eok
    heard : Σ ℕ (λ sX → lookupN x venv ≡ just sX × findS x ns ≡ just sX)
    heard = er x (∧-right scopeOk) (∧-left scopeOk)
    on : Σ ℕ (λ sX → lookupN x venv ≡ just sX × findS x ns ≡ just sX) →
         Built p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv (suc n) slot ns →
         Built (sput (pEcho x) p) (fput (fecho x) fp) pend ρ renv venv n slot ns
    on (sX , lk , fd) (bad (noB f wk cmp)) =
      bad (noB f
        (sput-miss {pend = pend} {ρ = ρ} {a = pEcho x} {p = p} {n = n} {s = slot} wk)
        (echo-miss {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                   {x = x} {sX = sX} {q = elab p fp} {f = f} lk cmp))
    on (sX , lk , fd) (ok y) =
      ok (finish-echo {ns = ns} (fput (fecho x) fp) y lk fd
        (sput-walk {pend = pend} {ρ = ρ} {a = pEcho x} {p = p} {n = n} {s = slot}
                   {w = Yes.w y} (Yes.wk y))
        (echo-cmp {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                  {x = x} {sX = sX} {q = elab p fp}
                  {e = entry (Yes.w y)} {next = next (Yes.w y)}
                  {slot' = slotN (Yes.w y)} {bs = Yes.bs y} lk (Yes.cmp y)))

  denote (sget t x p) (fget fp) pend ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    on (denote p fp [] (addPend pend n slot ρ) (addNames pend n renv) ((x , slot) ∷ venv)
          ns (x ∷ scope) (pre ++ (x ∷ [])) post (suc n) (suc slot)
          (add-rel pend n slot rel)
          (echo-extend pre (bnames p ++ post) x slot er nseq seq)
          eok (get-slot pre x slot seq) (get-names pre x (bnames p) post nseq)
          (cont-sep pend n slot ρ (mus p) sep))
    where
    on : Built p fp [] (addPend pend n slot ρ) (addNames pend n renv)
               ((x , slot) ∷ venv) (suc n) (suc slot) ns →
         Built (sget t x p) (fget fp) pend ρ renv venv n slot ns
    on (bad (noB f wk cmp)) =
      bad (noB f
        (sget-miss {pend = pend} {ρ = ρ} {t = t} {x = x} {p = p} {n = n} {s = slot} wk)
        (get-miss {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                  {t = t} {x = x} {q = elab p fp} {f = f} cmp))
    on (ok y) =
      ok (finish-get (fget fp) y
        (sget-walk {pend = pend} {ρ = ρ} {t = t} {x = x} {p = p} {n = n} {s = slot}
                   {w = Yes.w y} (Yes.wk y))
        (get-cmp {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                 {t = t} {x = x} {q = elab p fp}
                 {e = entry (Yes.w y)} {next = next (Yes.w y)}
                 {slot' = slotN (Yes.w y)} {bs = Yes.bs y} (Yes.cmp y)))

  denote (spick0 p) (fpick0 fp) pend ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    on (denote p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv
          ns scope pre post (suc n) slot (add-rel pend n slot rel) er eok seq nseq (cont-sep pend n slot ρ (mus p) sep))
    where
    on : Built p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv (suc n) slot ns →
         Built (spick0 p) (fpick0 fp) pend ρ renv venv n slot ns
    on (bad (noB f wk cmp)) =
      bad (noB f
        (spick0-miss {pend = pend} {ρ = ρ} {p = p} {n = n} {s = slot} wk)
        (pick0-miss {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                    {q = elab p fp} {f = f} cmp))
    on (ok y) =
      ok (finish-pick0 (fpick0 fp) y
        (spick0-walk {pend = pend} {ρ = ρ} {p = p} {n = n} {s = slot}
                     {w = Yes.w y} (Yes.wk y))
        (pick0-cmp {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                   {q = elab p fp} {e = entry (Yes.w y)} {nxt = next (Yes.w y)}
                   {slot' = slotN (Yes.w y)} {bs = Yes.bs y} (Yes.cmp y)))

  denote (spick1 p) (fpick1 fp) pend ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    on (denote p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv
          ns scope pre post (suc n) slot (add-rel pend n slot rel) er eok seq nseq (cont-sep pend n slot ρ (mus p) sep))
    where
    on : Built p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv (suc n) slot ns →
         Built (spick1 p) (fpick1 fp) pend ρ renv venv n slot ns
    on (bad (noB f wk cmp)) =
      bad (noB f
        (spick1-miss {pend = pend} {ρ = ρ} {p = p} {n = n} {s = slot} wk)
        (pick1-miss {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                    {q = elab p fp} {f = f} cmp))
    on (ok y) =
      ok (finish-pick1 (fpick1 fp) y
        (spick1-walk {pend = pend} {ρ = ρ} {p = p} {n = n} {s = slot}
                     {w = Yes.w y} (Yes.wk y))
        (pick1-cmp {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                   {q = elab p fp} {e = entry (Yes.w y)} {nxt = next (Yes.w y)}
                   {slot' = slotN (Yes.w y)} {bs = Yes.bs y} (Yes.cmp y)))

  denote (scover p q) (fcover fp fq) pend ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    onL (denote p fp [] ρw renw venv
           ns scope pre (bnames q ++ post) (suc n) slot
           (add-rel pend n slot rel) er (∧-left eok) seq
           (split-left pre (bnames p) (bnames q) post nseq)
           sepL)
    where
    ρw = addPend pend n slot ρ
    renw = addNames pend n renv
    sepW = cont-sep pend n slot ρ (mus p ++ mus q) sep
    sepL = proj₁ (side-b (namesI ρw) (mus p) (mus q) sepW)
    sepR = proj₂ (side-b (namesI ρw) (mus p) (mus q) sepW)
    onL : Built p fp [] ρw renw venv (suc n) slot ns →
          Built (scover p q) (fcover fp fq) pend ρ renv venv n slot ns
    onL (bad (noB f wk cmp)) =
      bad (noB f
        (cover-walk-bad {pend = pend} {ρ = ρ} {p = p} {q = q} {n = n} {s = slot} wk)
        (cover-cmp-bad {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                       {q1 = elab p fp} {q2 = elab q fq} {f = f} cmp))
    onL (ok y1) =
      onR y1 (denote q fq [] ρw renw venv ns scope (pre ++ bnames p) post
                (next (Yes.w y1)) (slotN (Yes.w y1))
                (add-rel pend n slot rel) er (∧-right eok)
                (cat-slot pre (bnames p) (Yes.end y1) seq)
                (split-right pre (bnames p) (bnames q) post nseq)
                sepR)
      where
      onR : (y1 : Yes p fp [] ρw renw venv (suc n) slot ns) →
            Built q fq [] ρw renw venv (next (Yes.w y1)) (slotN (Yes.w y1)) ns →
            Built (scover p q) (fcover fp fq) pend ρ renv venv n slot ns
      onR y1 (bad (noB f wk cmp)) =
        bad (noB f
          (cover-walk-miss {pend = pend} {ρ = ρ} {p = p} {q = q} {n = n} {s = slot}
                           {w = Yes.w y1} (Yes.wk y1) wk)
          (cover-cmp-miss {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                          {q1 = elab p fp} {q2 = elab q fq}
                          {e = entry (Yes.w y1)} {nxt = next (Yes.w y1)}
                          {slot' = slotN (Yes.w y1)} {bs = Yes.bs y1} {f = f}
                          (Yes.cmp y1) cmp))
      onR y1 (ok y2) =
        ok (yesB (mkW n slot (next (Yes.w y2)) (slotN (Yes.w y2)))
              ((n , bCover (entry (Yes.w y1)) (entry (Yes.w y2))) ∷
                (Yes.bs y1 ++ Yes.bs y2))
              (cover-walk-hit {pend = pend} {ρ = ρ} {p = p} {q = q} {n = n} {s = slot}
                              {w1 = Yes.w y1} {w2 = Yes.w y2}
                              (Yes.wk y1) (Yes.wk y2))
              (cover-cmp-hit {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                             {q1 = elab p fp} {q2 = elab q fq}
                             {e1 = entry (Yes.w y1)} {nxt1 = next (Yes.w y1)}
                             {slot1 = slotN (Yes.w y1)} {bs1 = Yes.bs y1}
                             {e2 = entry (Yes.w y2)} {nxt2 = next (Yes.w y2)}
                             {slot2 = slotN (Yes.w y2)} {bs2 = Yes.bs y2}
                             (Yes.cmp y1) (Yes.cmp y2))
              (o1 (ord-cat (Yes.od y1) (Yes.od y2)))
              (sum-len (bnames p) (bnames q) (Yes.end y1) (Yes.end y2))
              (p-act (d-cover n slot (entry (Yes.w y1)) (entry (Yes.w y2)) p q ρw
                        (Yes.w y1) (Yes.w y2) (Yes.wk y1) refl (Yes.wk y2) refl
                        (Yes.pl y1) (Yes.pl y2)
                        (Yes.hd y1) (Yes.sl y1) (Yes.ev y1)
                        (Yes.hd y2) (Yes.sl y2) (Yes.ev y2))
                     r-cover n slot ρ)
              (appendT (Yes.tab y1) (Yes.tab y2))
              (cp-act (c-cover here (covP-lift onˡ (Yes.cv y1))
                                 (covP-lift (onʳ {bs1 = Yes.bs y1}) (Yes.cv y2))))
              (appendC (covT-lift onˡ (Yes.ct y1))
                       (covT-lift (onʳ {bs1 = Yes.bs y1}) (Yes.ct y2)))
              refl refl refl
              (lk-cover refl refl refl (Yes.lk y1) (Yes.lk y2))
              (appendL (Yes.ls y1) (Yes.ls y2))
              (hs-cover (hosts-appendˡ (Yes.hs y1)) (hosts-appendʳ (Yes.hs y2)))
              (at-cover refl (Yes.at y1) (Yes.at y2))
              (names-join {t = Yes.tab y1} {u = Yes.tab y2} (Yes.tn y1) (Yes.tn y2))
              (en-cover (Yes.ens y1) (Yes.ens y2))
              (al-cover refl (Yes.al y1) (Yes.al y2)))

  denote (siget x p q) (figet fp fq) pend ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    onL (denote p fp [] ρw renw venvX ns scopeX preX (bnames q ++ post) (suc n) (suc slot)
           (add-rel pend n slot rel) erX (∧-left eok)
           (get-slot pre x slot seq)
           (iget-p-ns pre x (bnames p) (bnames q) post nseq)
           sepL)
    where
    ρw = addPend pend n slot ρ
    renw = addNames pend n renv
    venvX = (x , slot) ∷ venv
    scopeX = x ∷ scope
    preX = pre ++ (x ∷ [])
    erX = echo-extend pre ((bnames p ++ bnames q) ++ post) x slot er nseq seq
    sepW = cont-sep pend n slot ρ (mus p ++ mus q) sep
    sepL = proj₁ (side-b (namesI ρw) (mus p) (mus q) sepW)
    sepR = proj₂ (side-b (namesI ρw) (mus p) (mus q) sepW)
    onL : Built p fp [] ρw renw venvX (suc n) (suc slot) ns →
          Built (siget x p q) (figet fp fq) pend ρ renv venv n slot ns
    onL (bad (noB f wk cmp)) =
      bad (noB f
        (iget-walk-bad {pend = pend} {ρ = ρ} {x = x} {p = p} {q = q} {n = n} {s = slot} wk)
        (iget-cmp-bad {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                      {x = x} {q1 = elab p fp} {q2 = elab q fq} {f = f} cmp))
    onL (ok y1) =
      onR y1 (denote q fq [] ρw renw venvX ns scopeX (pre ++ (x ∷ bnames p)) post
                (next (Yes.w y1)) (slotN (Yes.w y1))
                (add-rel pend n slot rel) erX (∧-right eok)
                (iget-q-slot pre x (bnames p) (Yes.end y1) seq)
                (iget-q-ns pre x (bnames p) (bnames q) post nseq)
                sepR)
      where
      onR : (y1 : Yes p fp [] ρw renw venvX (suc n) (suc slot) ns) →
            Built q fq [] ρw renw venvX (next (Yes.w y1)) (slotN (Yes.w y1)) ns →
            Built (siget x p q) (figet fp fq) pend ρ renv venv n slot ns
      onR y1 (bad (noB f wk cmp)) =
        bad (noB f
          (iget-walk-miss {pend = pend} {ρ = ρ} {x = x} {p = p} {q = q} {n = n} {s = slot}
                          {w = Yes.w y1} (Yes.wk y1) wk)
          (iget-cmp-miss {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                         {x = x} {q1 = elab p fp} {q2 = elab q fq}
                         {e = entry (Yes.w y1)} {nxt = next (Yes.w y1)}
                         {slot' = slotN (Yes.w y1)} {bs = Yes.bs y1} {f = f}
                         (Yes.cmp y1) cmp))
      onR y1 (ok y2) =
        ok (yesB (mkW n slot (next (Yes.w y2)) (slotN (Yes.w y2)))
              ((n , bIget slot (entry (Yes.w y1)) (entry (Yes.w y2))) ∷
                (Yes.bs y1 ++ Yes.bs y2))
              (iget-walk-hit {pend = pend} {ρ = ρ} {x = x} {p = p} {q = q} {n = n} {s = slot}
                             {w1 = Yes.w y1} {w2 = Yes.w y2}
                             (Yes.wk y1) (Yes.wk y2))
              (iget-cmp-hit {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                            {x = x} {q1 = elab p fp} {q2 = elab q fq}
                            {e1 = entry (Yes.w y1)} {nxt1 = next (Yes.w y1)}
                            {slot1 = slotN (Yes.w y1)} {bs1 = Yes.bs y1}
                            {e2 = entry (Yes.w y2)} {nxt2 = next (Yes.w y2)}
                            {slot2 = slotN (Yes.w y2)} {bs2 = Yes.bs y2}
                            (Yes.cmp y1) (Yes.cmp y2))
              (o1 (ord-cat (Yes.od y1) (Yes.od y2)))
              (iget-end (bnames p) (bnames q) (Yes.end y1) (Yes.end y2))
              (p-act (d-iget n slot x (entry (Yes.w y1)) (entry (Yes.w y2)) p q ρw
                        (Yes.w y1) (Yes.w y2) (Yes.wk y1) refl (Yes.wk y2) refl
                        (Yes.pl y1) (Yes.pl y2)
                        (Yes.hd y1) (Yes.sl y1) (Yes.ev y1)
                        (Yes.hd y2) (Yes.sl y2) (Yes.ev y2))
                     r-iget n slot ρ)
              (appendT (Yes.tab y1) (Yes.tab y2))
              (cp-act (c-iget here (covP-lift onˡ (Yes.cv y1))
                                (covP-lift (onʳ {bs1 = Yes.bs y1}) (Yes.cv y2))))
              (appendC (covT-lift onˡ (Yes.ct y1))
                       (covT-lift (onʳ {bs1 = Yes.bs y1}) (Yes.ct y2)))
              refl refl refl
              (lk-iget refl refl refl (Yes.lk y1) (Yes.lk y2))
              (appendL (Yes.ls y1) (Yes.ls y2))
              (hs-iget (hosts-appendˡ (Yes.hs y1)) (hosts-appendʳ (Yes.hs y2)))
              (at-iget refl (Yes.at y1) (Yes.at y2))
              (names-join {t = Yes.tab y1} {u = Yes.tab y2} (Yes.tn y1) (Yes.tn y2))
              (en-iget (Yes.ens y1) (Yes.ens y2))
              (al-iget refl (Yes.al y1) (Yes.al y2)))

  denote (smget t x as) (fmget fas) pend ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    on (denoteArms as fas (addPend pend n slot ρ) (addNames pend n renv) ((x , slot) ∷ venv)
          ns (x ∷ scope) (pre ++ (x ∷ [])) post (suc n) (suc slot)
          (add-rel pend n slot rel)
          (echo-extend pre (bnamesArms as ++ post) x slot er nseq seq)
          eok (get-slot pre x slot seq) (get-names pre x (bnamesArms as) post nseq)
          (cont-sep pend n slot ρ (musArms as) sep))
    where
    on : BuiltA as fas (addPend pend n slot ρ) (addNames pend n renv) ((x , slot) ∷ venv)
               (suc n) (suc slot) ns →
         Built (smget t x as) (fmget fas) pend ρ renv venv n slot ns
    on (badA (noA f wk cmp)) =
      bad (noB f
        (mget-walk-bad {pend = pend} {ρ = ρ} {t = t} {x = x} {as = as} {n = n} {s = slot} wk)
        (mget-cmp-bad {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                      {t = t} {x = x} {qs = elabArms as fas} {f = f} cmp))
    on (okA y) =
      ok (yesB (mkW n slot (YesA.n2 y) (YesA.s2 y))
            ((n , bMget t slot (ents (YesA.ws y))) ∷ YesA.bs y)
            (mget-walk-hit {pend = pend} {ρ = ρ} {t = t} {x = x} {as = as} {n = n} {s = slot}
                           {ws = YesA.ws y} {n2 = YesA.n2 y} {s2 = YesA.s2 y} (YesA.wk y))
            (mget-cmp-hit {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                          {t = t} {x = x} {qs = elabArms as fas}
                          {n2 = YesA.n2 y} {s2 = YesA.s2 y}
                          {named = ents (YesA.ws y)} {bs = YesA.bs y} (YesA.cmp y))
            (o1 (YesA.od y))
            (shift-end {slot} {YesA.s2 y} {length (bnamesArms as)} (YesA.end y))
            (p-act (d-mget n slot t x (ents (YesA.ws y)) as
                      (addPend pend n slot ρ) (YesA.ws y) (YesA.n2 y) (YesA.s2 y)
                      (YesA.wk y) refl (YesA.dests y))
                   r-mget n slot ρ)
            (YesA.tab y)
            (cp-act (c-mget here (covA-lift under (YesA.cv y))))
            (covT-lift under (YesA.ct y))
            refl refl refl
            (lk-mget refl refl refl (YesA.lka y))
            (YesA.ls y)
            (hs-mget (YesA.hsa y))
            (at-mget refl (YesA.ata y))
            (YesA.tn y)
            (en-mget (YesA.eaa y))
            (al-mget refl (YesA.ala y)))

  denote (smu x p) (fmu fp) pend ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    seal (denote p fp (x ∷ pend) ρ renv venv ns scope pre post n slot rel er eok seq nseq
            (mu-sep ρ pend x (mus p) sep))
    where
    seal : Built p fp (x ∷ pend) ρ renv venv n slot ns →
           Built (smu x p) (fmu fp) pend ρ renv venv n slot ns
    seal (bad (noB f wk cmp)) = bad (noB f wk cmp)
    seal (ok y) =
      place (cons-bind x ρ pl0 (cp-mu (Yes.cv y)) (Yes.tab y) (Yes.ct y)
               (Yes.ls y) (lk-mu (Yes.lk y)) hs0 at0)
      where
      pl0 = p-mu x (Yes.pl y)
      hs0 = hs-mu (in-here (lk-mu (Yes.lk y))) refl (hosts-there (Yes.hs y))
      at0 = at-mu (pin-of {ms = mus p} y sep) (Yes.at y)
      place : BoundAt x ρ (p-mu x (Yes.pl y)) (Yes.bs y) (Yes.tab y) →
              Built (smu x p) (fmu fp) pend ρ renv venv n slot ns
      place (tab , ct , ls , eq) rewrite eq =
        ok (yesB (Yes.w y) (Yes.bs y) (Yes.wk y) (Yes.cmp y) (Yes.od y) (Yes.end y)
              (p-mu x (Yes.pl y))
              (t1 x (headIx (p-mu x (Yes.pl y))) (slotOf (p-mu x (Yes.pl y))) ρ
                  (p-mu x (Yes.pl y)) (Yes.tab y))
              (cp-mu (Yes.cv y)) ct
              (Yes.hd y) (Yes.sl y) (Yes.ev y)
              (lk-mu (Yes.lk y)) ls
              (hs-mu (in-here (lk-mu (Yes.lk y))) refl (hosts-there (Yes.hs y)))
              at0
              (cong (x ∷_) (Yes.tn y))
              (en-mu (Yes.ens y))
              (al-mu (Yes.al y)))

  denote (svar y) fvar pend ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    var-go (lookup-rel y rel) (elemS y pend) refl
    where
    var-go : Seen ρ renv y → (b : Bool) → elemS y pend ≡ b →
             Built (svar y) fvar pend ρ renv venv n slot ns
    var-go _ true eq =
      bad (noB fUnguarded
        (var-walk-ung {pend = pend} {ρ = ρ} {y = y} {n = n} {s = slot} eq)
        (var-cmp-ung {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n} {y = y} eq))
    var-go (seen-no eqi eqn) false eq =
      bad (noB fFree
        (var-walk-no {pend = pend} {ρ = ρ} {y = y} {n = n} {s = slot} eq eqi)
        (var-cmp-no {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n} {y = y} eq eqn))
    var-go (seen-yes i s0 eqi eqn) false eq =
      ok (yesB (mkW i s0 n slot) []
            (var-walk-yes {pend = pend} {ρ = ρ} {y = y} {n = n} {s = slot} {i = i} {s0 = s0} eq eqi)
            (var-cmp-yes {pend = pend} {renv = renv} {venv = venv} {slot = slot} {n = n}
                         {y = y} {i = i} eq eqn)
            o0 (sym (+-idr slot)) (p-jump y i s0 ρ) t0 cp-jump ct0 refl refl refl
            (lk-jump eqi) ls0 hs-jump at-jump refl en-jump al-jump)

  denoteArms : (as : List Arm) (fas : FragArms as) (ρ : EnvI) (renv : REnv) (venv : VEnv)
               (ns scope pre post : List String) (n slot : ℕ) →
               ERel ρ renv → EchoRel venv ns scope →
               echoOkArms ns scope as ≡ true →
               slot ≡ length pre →
               ns ≡ pre ++ bnamesArms as ++ post →
               distinct (namesI ρ ++ musArms as) ≡ true →
               BuiltA as fas ρ renv venv n slot ns

  denoteArms [] farms0 ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    okA (yesA [] n slot [] refl refl o0 (sym (+-idr slot)) (ap0 {ρ = ρ}) t0 ca0 ct0
           la0 ls0 ha0 ata0 refl ea0 aa0)

  denoteArms (aok y p ∷ as) (farms1 (farm fp) fas) ρ renv venv ns scope pre post n slot rel er eok seq nseq sep =
    on (denote p fp [] ρ renv venv ns scope pre (bnamesArms as ++ post) n slot rel er
          (∧-left eok) seq
          (split-left pre (bnames p) (bnamesArms as) post nseq)
          sepP)
    where
    sepP = proj₁ (side-b (namesI ρ) (mus p) (musArms as) sep)
    sepA = proj₂ (side-b (namesI ρ) (mus p) (musArms as) sep)
    on : Built p fp [] ρ renv venv n slot ns →
         BuiltA (aok y p ∷ as) (farms1 (farm fp) fas) ρ renv venv n slot ns
    on (bad (noB f wk cmp)) =
      badA (noA f
        (arm-walk-bad {ρ = ρ} {y = y} {p = p} {as = as} {n = n} {s = slot} wk)
        (arm-cmp-bad {renv = renv} {venv = venv} {slot = slot} {n = n} {y = y}
                     {q = elab p fp} {rest = elabArms as fas} {f = f} cmp))
    on (ok yb) =
      more yb (denoteArms as fas ρ renv venv ns scope (pre ++ bnames p) post
                 (next (Yes.w yb)) (slotN (Yes.w yb)) rel er (∧-right eok)
                 (cat-slot pre (bnames p) (Yes.end yb) seq)
                 (split-right pre (bnames p) (bnamesArms as) post nseq)
                 sepA)
      where
      more : (yb : Yes p fp [] ρ renv venv n slot ns) →
             BuiltA as fas ρ renv venv (next (Yes.w yb)) (slotN (Yes.w yb)) ns →
             BuiltA (aok y p ∷ as) (farms1 (farm fp) fas) ρ renv venv n slot ns
      more yb (badA (noA f wk cmp)) =
        badA (noA f
          (arm-walk-miss {ρ = ρ} {y = y} {p = p} {as = as} {n = n} {s = slot}
                         {w = Yes.w yb} (Yes.wk yb) wk)
          (arm-cmp-miss {renv = renv} {venv = venv} {slot = slot} {n = n} {y = y}
                        {q = elab p fp} {rest = elabArms as fas}
                        {e = entry (Yes.w yb)} {nxt = next (Yes.w yb)}
                        {slot1 = slotN (Yes.w yb)} {bs1 = Yes.bs yb} {f = f}
                        (Yes.cmp yb) cmp))
      more yb (okA ya) =
        okA (yesA ((y , Yes.w yb) ∷ YesA.ws ya)
               (YesA.n2 ya) (YesA.s2 ya) (Yes.bs yb ++ YesA.bs ya)
               (arm-walk-hit {ρ = ρ} {y = y} {p = p} {as = as} {n = n} {s = slot}
                             {w = Yes.w yb} {ws = YesA.ws ya} {n2 = YesA.n2 ya} {s2 = YesA.s2 ya}
                             (Yes.wk yb) (YesA.wk ya))
               (arm-cmp-hit {renv = renv} {venv = venv} {slot = slot} {n = n} {y = y}
                            {q = elab p fp} {rest = elabArms as fas}
                            {e = entry (Yes.w yb)} {nxt = next (Yes.w yb)}
                            {slot1 = slotN (Yes.w yb)} {bs1 = Yes.bs yb}
                            {n2 = YesA.n2 ya} {s2 = YesA.s2 ya}
                            {named = ents (YesA.ws ya)} {bs2 = YesA.bs ya}
                            (Yes.cmp yb) (YesA.cmp ya))
               (ord-cat (Yes.od yb) (YesA.od ya))
               (sum-len (bnames p) (bnamesArms as) (Yes.end yb) (YesA.end ya))
               (ap1 (Yes.pl yb) (Yes.hd yb) (Yes.sl yb) (Yes.ev yb) (YesA.dests ya))
               (appendT (Yes.tab yb) (YesA.tab ya))
               (ca1 (covP-lift inˡ (Yes.cv yb))
                    (covA-lift (inʳ {bs1 = Yes.bs yb}) (YesA.cv ya)))
               (appendC (covT-lift inˡ (Yes.ct yb))
                        (covT-lift (inʳ {bs1 = Yes.bs yb}) (YesA.ct ya)))
               (la1 (Yes.lk yb) (YesA.lka ya))
               (appendL (Yes.ls yb) (YesA.ls ya))
               (ha1 (hosts-appendˡ (Yes.hs yb)) (hostsA-appendʳ (YesA.hsa ya)))
               (ata1 (Yes.at yb) (YesA.ata ya))
               (names-join {t = Yes.tab yb} {u = YesA.tab ya} (Yes.tn yb) (YesA.tn ya))
               (ea1 (Yes.ens yb) (YesA.eaa ya))
               (aa1 (Yes.al yb) (YesA.ala ya)))

------------------------------------------------------------------------
-- The echo denotes, and so does a process that only halts.
------------------------------------------------------------------------

done-built : Built sdone fdone [] [] [] [] zero zero []
done-built =
  denote sdone fdone [] [] [] [] [] [] [] [] zero zero
    er0 (echo-empty [] []) refl refl refl refl

echo-built : Built src-echoA echoAF [] [] [] [] zero zero (bnames src-echoA)
echo-built =
  denote src-echoA echoAF [] [] [] [] (bnames src-echoA) [] [] [] zero zero
    er0 (echo-empty [] (bnames src-echoA)) echoA-ok refl (root-ns src-echoA) echo-mu

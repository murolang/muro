------------------------------------------------------------------------
-- The jump-following unfold agrees with the block `abs` stands on,
-- and a graph step on that block is the source step.
--
-- `spine` stops at a jump. `unfoldL` and `unfoldR` follow it. `readL`
-- and `readR` are that unfold read by `descend`: the focus is the
-- action at the cursor `abs` projects. A graph step on the cursor is
-- that action, run backwards through the forward lemmas.
--
-- `sim-bwd` takes a `Hold`. The cursor is what ties the graph step to
-- the source process. The specification's bare configuration is the
-- configuration inside that `Hold`.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Follow where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; suc; _<_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; subst; cong)

open import Muro.AsyncRec
  using ( Atom; Tok; lab; pay; Graph; RConf; reactL; reactR
        ; Act; AGo; findA; nthA; fits; aBit; rc; setNth
        ; conOf; armTo
        ; bPick0; bPick1; bGet; bCover; bIget; bMget )
open import Muro.Temporal.Pic using (_∈_; ents)
open Graph
open import Muro.Temporal using (Step; stepL; stepR; finish; Who; lside; rside; fin)
open import Muro.Temporal.Fire using (ago-inj; wait≢go)
open import Muro.Temporal.Source
  using ( SProc; SConf; abs; EnvP; Pay; addPend
        ; Focus; f-done; f-stop; f-put; f-pick0; f-pick1
        ; f-get; f-cover; f-iget; f-mget
        ; HaltF; h-done; h-stop
        ; Unfold; findS; W; walk; walkArms; armGo
        ; Arm; aok; abad
        ; _⟶ₛ_; put-l; echo-l; pick0-l; pick1-l
        ; get-l; cover0-l; cover1-l; iget0-l; iget1-l; mget-l
        ; put-r; echo-r; pick0-r; pick1-r
        ; get-r; cover0-r; cover1-r; iget0-r; iget1-r; mget-r )
open W
open SConf
open import Muro.Temporal.Run using (Hold; Cursor; walk-ext; Ext; just-inj)
open import Muro.Temporal.Chase using (unfoldL; unfoldR; Opened)
open Opened
open import Muro.Temporal.Invert
  using ( haltL; putL; echoL; pick0L; pick1L; getL; coverL; igetL; mgetL
        ; haltR; putR; echoR; pick0R; pick1R; getR; coverR; igetR; mgetR
        ; room-sound )
open import Muro.Temporal.Expose
  using ( Stop; atAct; Send; sent; echoed; leftStop; rightStop; leftSend
        ; haltBlock; seenL; seenR; put-fwd; echo-fwd; pick0-fwd; pick1-fwd
        ; rightSend
        ; putR-fwd; echoR-fwd; pickR0-fwd; pickR1-fwd
        ; afterPut; afterTok; afterGet; afterPop
        ; sendCont; Gone; Bag; ext-leaf
        ; get-fwd; cover0-fwd; cover1-fwd; iget0-fwd; iget1-fwd; mget-fwd
        ; getR-fwd; coverR0-fwd; coverR1-fwd; igetR0-fwd; igetR1-fwd; mgetR-fwd
        ; lf-pick0; lf-pick1; lf-get; lf-cover; lf-iget; lf-mget
        ; nothing≢just; pairˡ
        ; armGo-take; armGo-skip; arms-nowalk; arms-notail; arms-head
        ; armTo-take; armTo-skip )
open Bag
open import Muro.Temporal.Den
  using ( Place; p-act
        ; d-pick0; d-pick1; d-get; d-cover; d-iget; d-mget
        ; r-pick0; r-pick1; r-get; r-cover; r-iget; r-mget
        ; cp-act; c-pick0; c-pick1; c-get; c-cover; c-iget; c-mget
        ; lk-pick0; lk-pick1; lk-get; lk-cover; lk-iget; lk-mget
        ; hs-pick0; hs-pick1; hs-get; hs-cover; hs-iget; hs-mget
        ; at-pick0; at-pick1; at-get; at-cover; at-iget; at-mget
        ; en-pick0; en-pick1; en-get; en-cover; en-iget; en-mget
        ; al-pick0; al-pick1; al-get; al-cover; al-iget; al-mget )

------------------------------------------------------------------------
-- The unfold is the block at the cursor.
------------------------------------------------------------------------

readL : ∀ {g c} (h : Hold g c) →
        Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
             (il c) (slotL c) (envIL c)
             (ρ′ (unfoldL h)) (pend′ (unfoldL h)) (f (unfoldL h))
readL h = leftStop h (unf (unfoldL h))

readR : ∀ {g c} (h : Hold g c) →
        Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
             (ir c) (slotR c) (envIR c)
             (ρ′ (unfoldR h)) (pend′ (unfoldR h)) (f (unfoldR h))
readR h = rightStop h (unf (unfoldR h))

------------------------------------------------------------------------
-- A forward step and the graph step it explains are the same target.
------------------------------------------------------------------------

tgtL : ∀ {g c d} → Step g c lside d → reactL g c ≡ AGo d
tgtL (stepL eq) = eq

backL : ∀ {g c c′ r′} →
        c ⟶ₛ c′ →
        Step g (abs c) lside (abs c′) →
        Hold g c′ →
        reactL g (abs c) ≡ AGo r′ →
        Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
backL step fwd hold eq =
  _ , step , ago-inj (trans (sym (tgtL fwd)) eq) , hold

-- A halted focus does not take a left step.
halt-stuckL : ∀ {g c ρ′ pend′ f r′} (h : Hold g c) →
              Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
                   (il c) (slotL c) (envIL c) ρ′ pend′ f →
              HaltF f →
              reactL g (abs c) ≡ AGo r′ →
              ⊥
halt-stuckL {g} {c} h st hf eq =
  let blk = haltBlock st hf
      look = seenL h (proj₁ (proj₂ blk))
      waited = haltL g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                 (proj₁ blk) look (proj₂ (proj₂ blk))
  in wait≢go (trans (sym waited) eq)

under : ∀ {g c} (h : Hold g c) → length (l2r c) < cap g → length (l2r c) < cap c
under {c = c} h le = subst (λ n → length (l2r c) < n) (sym (Hold.κ h)) le

onAlpha : ∀ {g c atom k} (h : Hold g c) →
          findA atom (alpha g) ≡ just k →
          findA atom (alpha c) ≡ just k
onAlpha {c = c} {atom} {k} h eq =
  subst (λ al → findA atom al ≡ just k) (sym (Hold.α h)) eq

-- A source put or echo, recovered from the send the unfold reached.
sendL : ∀ {g c a p ρ′ pend′ r′} (h : Hold g c) →
        Unfold (envPL c) [] (left c) ρ′ pend′ (f-put a p) →
        reactL g (abs c) ≡ AGo r′ →
        Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
sendL {g} {c} {a} {p} {ρ′} {pend′} {r′} h u eq = onS (leftSend h u)
  where
  onS : Send (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
             (il c) (slotL c) (envIL c) ρ′ pend′ a p →
        Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  onS (sent atom j w aeq _ mem wk _ _) =
    let inv = putL g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                atom j r′ (seenL h mem) eq
        k = proj₁ inv
        found = onAlpha h (proj₁ (proj₂ inv))
        le = under h (room-sound (cap g) (l2r c) (proj₁ (proj₂ (proj₂ inv))))
        fwd = put-fwd h u aeq found le wk
    in backL (put-l u aeq found le wk) (proj₁ fwd) (proj₂ fwd) eq
  onS (echoed x sX j w eqA fd _ mem wk _ _) =
    let uX = subst (λ z → Unfold (envPL c) [] (left c) ρ′ pend′ (f-put z p)) eqA u
        fdN = subst (λ ns → findS x ns ≡ just sX) (sym (Hold.nmL h)) fd
        inv = echoL g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                sX j r′ (seenL h mem) eq
        k = proj₁ inv
        slotG = proj₁ (proj₂ inv)
        le = under h (room-sound (cap g) (l2r c) (proj₁ (proj₂ (proj₂ inv))))
        fwd = echo-fwd h uX fdN slotG le wk
    in backL (echo-l uX fdN slotG le wk) (proj₁ fwd) (proj₂ fwd) eq

pick0B : ∀ {g c p ρ′ pend′ r′} (h : Hold g c) →
         Unfold (envPL c) [] (left c) ρ′ pend′ (f-pick0 p) →
         reactL g (abs c) ≡ AGo r′ →
         Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
pick0B {g} {c} {p} {ρ′} {pend′} {r′} h u eq = on (leftStop h u)
  where
  on : Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
            (il c) (slotL c) (envIL c) ρ′ pend′ (f-pick0 p) →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  on (atAct suf ρi bg _
       (p-act (d-pick0 nD sD j .p ρw wD wkD _ dest dh ds de)
              r-pick0 _ _ ρden)
       (cp-act (c-pick0 mem cvD))
       (lk-pick0 eqi eqs _ lkD)
       (hs-pick0 hsD)
       (at-pick0 _ atD)
       (en-pick0 ensD)
       (al-pick0 eqρ destAl)
       ix ss sn lf-pick0) =
    let en = trans ix eqi
        es = trans ss eqs
        go = sendCont {n = il c} {s = slotL c} {base = envIL c} {ρi = ρi}
               {pend = pend′} {suf = suf} {env = ρ′} {p = p}
               {nD = nD} {sD = sD} {sW = slotL c} {sW′ = sD}
               {ρden = ρden} {ρw = ρw} {w = wD} {dest = dest}
               bg en es es eqρ sn (cvd bg) wkD dh ds de
               cvD lkD hsD atD ensD destAl
        memN = subst (λ i → (i , bPick0 j) ∈ Hold.bsL h) (sym en) mem
        inv = pick0L g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                j r′ (seenL h memN) eq
        le = under h (room-sound (cap g) (l2r c) (proj₁ inv))
        wk = Gone.wk go
        fwd = pick0-fwd h u le wk
    in backL (pick0-l u le wk) (proj₁ fwd) (proj₂ fwd) eq

pick1B : ∀ {g c p ρ′ pend′ r′} (h : Hold g c) →
         Unfold (envPL c) [] (left c) ρ′ pend′ (f-pick1 p) →
         reactL g (abs c) ≡ AGo r′ →
         Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
pick1B {g} {c} {p} {ρ′} {pend′} {r′} h u eq = on (leftStop h u)
  where
  on : Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
            (il c) (slotL c) (envIL c) ρ′ pend′ (f-pick1 p) →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  on (atAct suf ρi bg _
       (p-act (d-pick1 nD sD j .p ρw wD wkD _ dest dh ds de)
              r-pick1 _ _ ρden)
       (cp-act (c-pick1 mem cvD))
       (lk-pick1 eqi eqs _ lkD)
       (hs-pick1 hsD)
       (at-pick1 _ atD)
       (en-pick1 ensD)
       (al-pick1 eqρ destAl)
       ix ss sn lf-pick1) =
    let en = trans ix eqi
        es = trans ss eqs
        go = sendCont {n = il c} {s = slotL c} {base = envIL c} {ρi = ρi}
               {pend = pend′} {suf = suf} {env = ρ′} {p = p}
               {nD = nD} {sD = sD} {sW = slotL c} {sW′ = sD}
               {ρden = ρden} {ρw = ρw} {w = wD} {dest = dest}
               bg en es es eqρ sn (cvd bg) wkD dh ds de
               cvD lkD hsD atD ensD destAl
        memN = subst (λ i → (i , bPick1 j) ∈ Hold.bsL h) (sym en) mem
        inv = pick1L g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                j r′ (seenL h memN) eq
        le = under h (room-sound (cap g) (l2r c) (proj₁ inv))
        wk = Gone.wk go
        fwd = pick1-fwd h u le wk
    in backL (pick1-l u le wk) (proj₁ fwd) (proj₂ fwd) eq

getB : ∀ {g c t x p ρ′ pend′ r′} (h : Hold g c) →
       Unfold (envPL c) [] (left c) ρ′ pend′ (f-get t x p) →
       reactL g (abs c) ≡ AGo r′ →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
getB {g} {c} {t} {x} {p} {ρ′} {pend′} {r′} h u eq = on (leftStop h u)
  where
  on : Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
            (il c) (slotL c) (envIL c) ρ′ pend′ (f-get t x p) →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  on (atAct suf ρi bg _
       (p-act (d-get nD sD .t .x j .p ρw wD wkD _ dest dh ds de)
              r-get _ _ ρden)
       (cp-act (c-get mem cvD))
       (lk-get eqi eqs _ lkD)
       (hs-get hsD)
       (at-get _ atD)
       (en-get ensD)
       (al-get eqρ destAl)
       ix ss sn lf-get) =
    let en = trans ix eqi
        es = trans ss eqs
        go = sendCont {n = il c} {s = slotL c} {base = envIL c} {ρi = ρi}
               {pend = pend′} {suf = suf} {env = ρ′} {p = p}
               {nD = nD} {sD = sD} {sW = suc (slotL c)} {sW′ = suc sD}
               {ρden = ρden} {ρw = ρw} {w = wD} {dest = dest}
               bg en es (cong suc es) eqρ sn (cvd bg) wkD dh ds de
               cvD lkD hsD atD ensD destAl
        memI = subst (λ i → (i , bGet t sD j) ∈ Hold.bsL h) (sym en) mem
        memN = subst (λ z → (il c , bGet t z j) ∈ Hold.bsL h) (sym es) memI
        inv = getL g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                t (slotL c) j r′ (seenL h memN) eq
        k = proj₁ inv
        rest = proj₁ (proj₂ inv)
        a = proj₁ (proj₂ (proj₂ inv))
        qeq = proj₁ (proj₂ (proj₂ (proj₂ inv)))
        nthG = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ inv))))
        fit = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ inv)))))
        nthC = subst (λ al → nthA al k ≡ just a) (sym (Hold.α h)) nthG
        wk = Gone.wk go
        fwd = get-fwd h u qeq nthC fit wk
    in backL (get-l u qeq nthC fit wk) (proj₁ fwd) (proj₂ fwd) eq

coverB : ∀ {g c p q ρ′ pend′ r′} (h : Hold g c) →
         Unfold (envPL c) [] (left c) ρ′ pend′ (f-cover p q) →
         reactL g (abs c) ≡ AGo r′ →
         Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
coverB {g} {c} {p} {q} {ρ′} {pend′} {r′} h u eq = on (leftStop h u)
  where
  on : Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
            (il c) (slotL c) (envIL c) ρ′ pend′ (f-cover p q) →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  on (atAct suf ρi bg _
       (p-act (d-cover nD sD i j .p .q ρw w1D w2D wk1D _ wk2D _
                       dp dq hp sp deP hq sq deQ)
              r-cover _ _ ρden)
       (cp-act (c-cover mem cvP cvQ))
       (lk-cover eqi eqs _ lkP lkQ)
       (hs-cover hsP hsQ)
       (at-cover _ atP atQ)
       (en-cover ensP ensQ)
       (al-cover eqρ alP alQ)
       ix ss sn lf-cover) =
    let en = trans ix eqi
        es = trans ss eqs
        go = sendCont {n = il c} {s = slotL c} {base = envIL c} {ρi = ρi}
               {pend = pend′} {suf = suf} {env = ρ′} {p = p}
               {nD = nD} {sD = sD} {sW = slotL c} {sW′ = sD}
               {ρden = ρden} {ρw = ρw} {w = w1D} {dest = dp}
               bg en es es eqρ sn (cvd bg) wk1D hp sp deP
               cvP lkP hsP atP ensP alP
        extW = ext-leaf suf pend′ (il c) (slotL c) nD sD ρden (envIL c)
                 ρw ρi suf en es refl eqρ (run bg) sn (cvd bg)
        wkI = walk-ext [] ρw ρi q (next w1D) (slotN w1D) w2D extW wk2D
        wk2 = subst (λ e → walk [] e q (next w1D) (slotN w1D) ≡ just w2D)
                (run bg) wkI
        memN = subst (λ z → (z , bCover i j) ∈ Hold.bsL h) (sym en) mem
        inv = coverL g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                i j r′ (seenL h memN) eq
        wk1 = Gone.wk go
    in branch (proj₂ inv) wk1 wk2
    where
    branch : ∀ {rest} →
             (r2l c ≡ lab false ∷ rest ×
              r′ ≡ rc i (ir c) (l2r c) rest (el c) (er c)) ⊎
             (r2l c ≡ lab true ∷ rest ×
              r′ ≡ rc j (ir c) (l2r c) rest (el c) (er c)) →
             walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                  (suc (il c)) (slotL c) ≡ just w1D →
             walk [] (addPend pend′ (il c) (slotL c) (envIL c)) q
                  (next w1D) (slotN w1D) ≡ just w2D →
             Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
    branch (inj₁ (qeq , _)) wk1 wk2 =
      let fwd = cover0-fwd h u qeq wk1
      in backL (cover0-l u qeq wk1) (proj₁ fwd) (proj₂ fwd) eq
    branch (inj₂ (qeq , _)) wk1 wk2 =
      let fwd = cover1-fwd h u qeq wk1 wk2
      in backL (cover1-l u qeq wk1 wk2) (proj₁ fwd) (proj₂ fwd) eq

-- An integer receive follows the bit the payload denotes. The false
-- bit is the first continuation. The true bit is the second walk.
igetB : ∀ {g c x p q ρ′ pend′ r′} (h : Hold g c) →
        Unfold (envPL c) [] (left c) ρ′ pend′ (f-iget x p q) →
        reactL g (abs c) ≡ AGo r′ →
        Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
igetB {g} {c} {x} {p} {q} {ρ′} {pend′} {r′} h u eq = on (leftStop h u)
  where
  on : Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
            (il c) (slotL c) (envIL c) ρ′ pend′ (f-iget x p q) →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  on (atAct suf ρi bg _
       (p-act (d-iget nD sD .x i j .p .q ρw w1D w2D wk1D _ wk2D _
                      dp dq hp sp deP hq sq deQ)
              r-iget _ _ ρden)
       (cp-act (c-iget mem cvP cvQ))
       (lk-iget eqi eqs _ lkP lkQ)
       (hs-iget hsP hsQ)
       (at-iget _ atP atQ)
       (en-iget ensP ensQ)
       (al-iget eqρ alP alQ)
       ix ss sn lf-iget) =
    let en = trans ix eqi
        es = trans ss eqs
        go = sendCont {n = il c} {s = slotL c} {base = envIL c} {ρi = ρi}
               {pend = pend′} {suf = suf} {env = ρ′} {p = p}
               {nD = nD} {sD = sD} {sW = suc (slotL c)} {sW′ = suc sD}
               {ρden = ρden} {ρw = ρw} {w = w1D} {dest = dp}
               bg en es (cong suc es) eqρ sn (cvd bg) wk1D hp sp deP
               cvP lkP hsP atP ensP alP
        extW = ext-leaf suf pend′ (il c) (slotL c) nD sD ρden (envIL c)
                 ρw ρi suf en es refl eqρ (run bg) sn (cvd bg)
        wkI = walk-ext [] ρw ρi q (next w1D) (slotN w1D) w2D extW wk2D
        wk2 = subst (λ e → walk [] e q (next w1D) (slotN w1D) ≡ just w2D)
                (run bg) wkI
        memI = subst (λ z → (z , bIget sD i j) ∈ Hold.bsL h) (sym en) mem
        memN = subst (λ z → (il c , bIget z i j) ∈ Hold.bsL h) (sym es) memI
        inv = igetL g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                (slotL c) i j r′ (seenL h memN) eq
        wk1 = Gone.wk go
    in branch (proj₂ (proj₂ inv)) wk1 wk2
    where
    branch : ∀ {k rest} →
             (r2l c ≡ pay k ∷ rest ×
              nthA (alpha g) k ≡ just (aBit false) ×
              r′ ≡ rc i (ir c) (l2r c) rest
                     (setNth (slotL c) (suc k) (el c)) (er c)) ⊎
             (r2l c ≡ pay k ∷ rest ×
              nthA (alpha g) k ≡ just (aBit true) ×
              r′ ≡ rc j (ir c) (l2r c) rest
                     (setNth (slotL c) (suc k) (el c)) (er c)) →
             walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                  (suc (il c)) (suc (slotL c)) ≡ just w1D →
             walk [] (addPend pend′ (il c) (slotL c) (envIL c)) q
                  (next w1D) (slotN w1D) ≡ just w2D →
             Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
    branch {k} (inj₁ (qeq , nthG , _)) wk1 wk2 =
      let nthC = subst (λ al → nthA al k ≡ just (aBit false)) (sym (Hold.α h)) nthG
          fwd = iget0-fwd h u qeq nthC wk1
      in backL (iget0-l u qeq nthC wk1) (proj₁ fwd) (proj₂ fwd) eq
    branch {k} (inj₂ (qeq , nthG , _)) wk1 wk2 =
      let nthC = subst (λ al → nthA al k ≡ just (aBit true)) (sym (Hold.α h)) nthG
          fwd = iget1-fwd h u qeq nthC wk1 wk2
      in backL (iget1-l u qeq nthC wk1 wk2) (proj₁ fwd) (proj₂ fwd) eq

------------------------------------------------------------------------
-- The arm `armTo` names is the arm `armGo` returns, and a successful
-- `armGo` stays successful on a larger environment.
------------------------------------------------------------------------

armGo-nowalk : ∀ {ρ name y p as n s} →
               walk [] ρ p n s ≡ nothing →
               armGo ρ name (aok y p ∷ as) n s ≡ nothing
armGo-nowalk eq rewrite eq = refl

arm-of : ∀ {ρ name n s j} (as : List Arm) {ws n2 s2} →
         walkArms [] ρ as n s ≡ just (ws , n2 , s2) →
         armTo name (ents ws) ≡ just j →
         Σ W (λ w → Σ SProc (λ proc →
           armGo ρ name as n s ≡ just (w , proc) × entry w ≡ j))
arm-of {name = name} [] eqw hit =
  ⊥-elim (nothing≢just
    (trans (cong (armTo name) (cong ents (pairˡ (just-inj eqw)))) hit))
arm-of (abad ∷ _) eqw _ = ⊥-elim (nothing≢just eqw)
arm-of {ρ = ρ} {name = name} {n = n} {s = s} {j = j} (aok y q ∷ as) eqw hit =
  onW (walk [] ρ q n s) refl
  where
  onW : (m : Maybe W) → walk [] ρ q n s ≡ m →
        Σ W (λ w → Σ SProc (λ proc →
          armGo ρ name (aok y q ∷ as) n s ≡ just (w , proc) × entry w ≡ j))
  onW nothing eq =
    ⊥-elim (nothing≢just
      (trans (sym (arms-nowalk {ρ = ρ} {y = y} {p = q} {as = as} {n = n} {s = s} eq)) eqw))
  onW (just w0) eq = onA w0 eq (walkArms [] ρ as (next w0) (slotN w0)) refl
    where
    onA : (w0 : W) → walk [] ρ q n s ≡ just w0 →
          (m : Maybe (List (String × W) × ℕ × ℕ)) →
          walkArms [] ρ as (next w0) (slotN w0) ≡ m →
          Σ W (λ w → Σ SProc (λ proc →
            armGo ρ name (aok y q ∷ as) n s ≡ just (w , proc) × entry w ≡ j))
    onA w0 eq nothing eqa =
      ⊥-elim (nothing≢just
        (trans (sym (arms-notail {ρ = ρ} {y = y} {p = q} {as = as}
                      {n = n} {s = s} {w = w0} eq eqa)) eqw))
    onA w0 eq (just (wsT , n2T , s2T)) eqa = onB (name == y) refl
      where
      head = arms-head {ρ = ρ} {y = y} {p = q} {as = as} {n = n} {s = s}
               {w = w0} {ws = wsT} {n2 = n2T} {s2 = s2T} eq eqa
      eqws = pairˡ (just-inj (trans (sym head) eqw))
      eqents = cong ents eqws
      onB : (b : Bool) → (name == y) ≡ b →
            Σ W (λ w → Σ SProc (λ proc →
              armGo ρ name (aok y q ∷ as) n s ≡ just (w , proc) × entry w ≡ j))
      onB true eqb =
        let here = armTo-take {name = name} {y = y} {j = entry w0} {rest = ents wsT} eqb
            moved = subst (λ xs → armTo name xs ≡ just (entry w0)) eqents here
            ej = just-inj (trans (sym moved) hit)
            ago = armGo-take {ρ = ρ} {name = name} {y = y} {p = q} {as = as}
                    {n = n} {s = s} {w = w0} eq eqb
        in w0 , q , ago , ej
      onB false eqb =
        let skipA = armTo-skip {name = name} {y = y} {j = entry w0} {rest = ents wsT} eqb
            moved = subst (λ xs → armTo name xs ≡ armTo name (ents wsT)) eqents skipA
            rec = arm-of as eqa (trans (sym moved) hit)
            agoR = proj₁ (proj₂ (proj₂ rec))
            skipG = armGo-skip {ρ = ρ} {name = name} {y = y} {p = q} {as = as}
                      {n = n} {s = s} {w = w0} eq eqb
        in proj₁ rec , proj₁ (proj₂ rec) , trans skipG agoR , proj₂ (proj₂ (proj₂ rec))

armGo-ext : ∀ {ρ0 ρ name n s w proc} (as : List Arm) →
            Ext ρ0 ρ →
            armGo ρ0 name as n s ≡ just (w , proc) →
            armGo ρ name as n s ≡ just (w , proc)
armGo-ext [] _ hit = ⊥-elim (nothing≢just hit)
armGo-ext (abad ∷ _) _ hit = ⊥-elim (nothing≢just hit)
armGo-ext {ρ0 = ρ0} {ρ = ρ} {name = name} {n = n} {s = s} {w = w} {proc = proc}
          (aok y q ∷ as) ext hit =
  onW (walk [] ρ0 q n s) refl
  where
  onW : (m : Maybe W) → walk [] ρ0 q n s ≡ m →
        armGo ρ name (aok y q ∷ as) n s ≡ just (w , proc)
  onW nothing eq =
    ⊥-elim (nothing≢just
      (trans (sym (armGo-nowalk {ρ = ρ0} {name = name} {y = y} {p = q} {as = as}
                  {n = n} {s = s} eq)) hit))
  onW (just w0) eq = onB (name == y) refl
    where
    onB : (b : Bool) → (name == y) ≡ b →
          armGo ρ name (aok y q ∷ as) n s ≡ just (w , proc)
    onB true eqb =
      let wkρ = walk-ext [] ρ0 ρ q n s w0 ext eq
          here0 = armGo-take {ρ = ρ0} {name = name} {y = y} {p = q} {as = as}
                    {n = n} {s = s} {w = w0} eq eqb
          here1 = armGo-take {ρ = ρ} {name = name} {y = y} {p = q} {as = as}
                    {n = n} {s = s} {w = w0} wkρ eqb
      in trans here1 (cong just (just-inj (trans (sym here0) hit)))
    onB false eqb =
      let wkρ = walk-ext [] ρ0 ρ q n s w0 ext eq
          skip0 = armGo-skip {ρ = ρ0} {name = name} {y = y} {p = q} {as = as}
                    {n = n} {s = s} {w = w0} eq eqb
          skip1 = armGo-skip {ρ = ρ} {name = name} {y = y} {p = q} {as = as}
                    {n = n} {s = s} {w = w0} wkρ eqb
      in trans skip1 (armGo-ext as ext (trans (sym skip0) hit))

-- A constructor receive takes the arm the payload names.
mgetB : ∀ {g c t x as ρ′ pend′ r′} (h : Hold g c) →
        Unfold (envPL c) [] (left c) ρ′ pend′ (f-mget t x as) →
        reactL g (abs c) ≡ AGo r′ →
        Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
mgetB {g} {c} {t} {x} {as} {ρ′} {pend′} {r′} h u eq = on (leftStop h u)
  where
  on : Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
            (il c) (slotL c) (envIL c) ρ′ pend′ (f-mget t x as) →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  on (atAct suf ρi bg _
       (p-act (d-mget nD sD .t .x named .as ρw ws _ _ wkD enW _)
              r-mget _ _ ρden)
       (cp-act (c-mget mem _))
       (lk-mget eqi eqs _ _)
       (hs-mget _)
       (at-mget _ _)
       (en-mget _)
       (al-mget eqρ _)
       ix ss sn lf-mget) =
    let en = trans ix eqi
        es = trans ss eqs
        memI = subst (λ z → (z , bMget t sD named) ∈ Hold.bsL h) (sym en) mem
        memN = subst (λ z → (il c , bMget t z named) ∈ Hold.bsL h) (sym es) memI
        inv = mgetL g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                t (slotL c) named r′ (seenL h memN) eq
        k = proj₁ inv
        rest = proj₁ (proj₂ inv)
        a = proj₁ (proj₂ (proj₂ inv))
        nm = proj₁ (proj₂ (proj₂ (proj₂ inv)))
        j = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ inv))))
        packed = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ inv))))
        qeq = proj₁ packed
        nthG = proj₁ (proj₂ packed)
        fit = proj₁ (proj₂ (proj₂ packed))
        con = proj₁ (proj₂ (proj₂ (proj₂ packed)))
        toN = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ packed))))
        toE = subst (λ xs → armTo nm xs ≡ just j) (sym enW) toN
        got = arm-of {name = nm} {j = j} as wkD toE
        w = proj₁ got
        proc = proj₁ (proj₂ got)
        hit0 = proj₁ (proj₂ (proj₂ got))
        extW = ext-leaf suf pend′ (il c) (slotL c) nD sD ρden (envIL c)
                 ρw ρi suf en es refl eqρ (run bg) sn (cvd bg)
        hit1 = armGo-ext as extW hit0
        hit2 = subst (λ z → armGo ρi nm as (suc z) (suc sD) ≡ just (w , proc))
                 (sym en) hit1
        hit3 = subst (λ z → armGo ρi nm as (suc (il c)) (suc z) ≡ just (w , proc))
                 (sym es) hit2
        hit4 = subst (λ e → armGo e nm as (suc (il c)) (suc (slotL c)) ≡ just (w , proc))
                 (run bg) hit3
        nthC = subst (λ al → nthA al k ≡ just a) (sym (Hold.α h)) nthG
        fwd = mget-fwd h u qeq nthC fit con hit4
    in backL (mget-l u qeq nthC fit con hit4) (proj₁ fwd) (proj₂ fwd) eq

------------------------------------------------------------------------
-- The right side. The step writes `r2l` and reads `l2r`.
------------------------------------------------------------------------

tgtR : ∀ {g c d} → Step g c rside d → reactR g c ≡ AGo d
tgtR (stepR eq) = eq

backR : ∀ {g c c′ r′} →
        c ⟶ₛ c′ →
        Step g (abs c) rside (abs c′) →
        Hold g c′ →
        reactR g (abs c) ≡ AGo r′ →
        Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
backR step fwd hold eq =
  _ , step , ago-inj (trans (sym (tgtR fwd)) eq) , hold

halt-stuckR : ∀ {g c ρ′ pend′ f r′} (h : Hold g c) →
              Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
                   (ir c) (slotR c) (envIR c) ρ′ pend′ f →
              HaltF f →
              reactR g (abs c) ≡ AGo r′ →
              ⊥
halt-stuckR {g} {c} h st hf eq =
  let blk = haltBlock st hf
      look = seenR h (proj₁ (proj₂ blk))
      waited = haltR g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                 (proj₁ blk) look (proj₂ (proj₂ blk))
  in wait≢go (trans (sym waited) eq)

underR : ∀ {g c} (h : Hold g c) → length (r2l c) < cap g → length (r2l c) < cap c
underR {c = c} h le = subst (λ n → length (r2l c) < n) (sym (Hold.κ h)) le

sendR : ∀ {g c a p ρ′ pend′ r′} (h : Hold g c) →
        Unfold (envPR c) [] (right c) ρ′ pend′ (f-put a p) →
        reactR g (abs c) ≡ AGo r′ →
        Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
sendR {g} {c} {a} {p} {ρ′} {pend′} {r′} h u eq = onS (rightSend h u)
  where
  onS : Send (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
             (ir c) (slotR c) (envIR c) ρ′ pend′ a p →
        Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  onS (sent atom j w aeq _ mem wk _ _) =
    let inv = putR g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                atom j r′ (seenR h mem) eq
        found = onAlpha h (proj₁ (proj₂ inv))
        le = underR h (room-sound (cap g) (r2l c) (proj₁ (proj₂ (proj₂ inv))))
        fwd = putR-fwd h u aeq found le wk
    in backR (put-r u aeq found le wk) (proj₁ fwd) (proj₂ fwd) eq
  onS (echoed x sX j w eqA fd _ mem wk _ _) =
    let uX = subst (λ z → Unfold (envPR c) [] (right c) ρ′ pend′ (f-put z p)) eqA u
        fdN = subst (λ ns → findS x ns ≡ just sX) (sym (Hold.nmR h)) fd
        inv = echoR g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                sX j r′ (seenR h mem) eq
        slotG = proj₁ (proj₂ inv)
        le = underR h (room-sound (cap g) (r2l c) (proj₁ (proj₂ (proj₂ inv))))
        fwd = echoR-fwd h uX fdN slotG le wk
    in backR (echo-r uX fdN slotG le wk) (proj₁ fwd) (proj₂ fwd) eq

pick0RB : ∀ {g c p ρ′ pend′ r′} (h : Hold g c) →
          Unfold (envPR c) [] (right c) ρ′ pend′ (f-pick0 p) →
          reactR g (abs c) ≡ AGo r′ →
          Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
pick0RB {g} {c} {p} {ρ′} {pend′} {r′} h u eq = on (rightStop h u)
  where
  on : Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
            (ir c) (slotR c) (envIR c) ρ′ pend′ (f-pick0 p) →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  on (atAct suf ρi bg _
       (p-act (d-pick0 nD sD j .p ρw wD wkD _ dest dh ds de)
              r-pick0 _ _ ρden)
       (cp-act (c-pick0 mem cvD))
       (lk-pick0 eqi eqs _ lkD)
       (hs-pick0 hsD)
       (at-pick0 _ atD)
       (en-pick0 ensD)
       (al-pick0 eqρ destAl)
       ix ss sn lf-pick0) =
    let en = trans ix eqi
        es = trans ss eqs
        go = sendCont {n = ir c} {s = slotR c} {base = envIR c} {ρi = ρi}
               {pend = pend′} {suf = suf} {env = ρ′} {p = p}
               {nD = nD} {sD = sD} {sW = slotR c} {sW′ = sD}
               {ρden = ρden} {ρw = ρw} {w = wD} {dest = dest}
               bg en es es eqρ sn (cvd bg) wkD dh ds de
               cvD lkD hsD atD ensD destAl
        memN = subst (λ i → (i , bPick0 j) ∈ Hold.bsR h) (sym en) mem
        inv = pick0R g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                j r′ (seenR h memN) eq
        le = underR h (room-sound (cap g) (r2l c) (proj₁ inv))
        wk = Gone.wk go
        fwd = pickR0-fwd h u le wk
    in backR (pick0-r u le wk) (proj₁ fwd) (proj₂ fwd) eq

pick1RB : ∀ {g c p ρ′ pend′ r′} (h : Hold g c) →
          Unfold (envPR c) [] (right c) ρ′ pend′ (f-pick1 p) →
          reactR g (abs c) ≡ AGo r′ →
          Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
pick1RB {g} {c} {p} {ρ′} {pend′} {r′} h u eq = on (rightStop h u)
  where
  on : Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
            (ir c) (slotR c) (envIR c) ρ′ pend′ (f-pick1 p) →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  on (atAct suf ρi bg _
       (p-act (d-pick1 nD sD j .p ρw wD wkD _ dest dh ds de)
              r-pick1 _ _ ρden)
       (cp-act (c-pick1 mem cvD))
       (lk-pick1 eqi eqs _ lkD)
       (hs-pick1 hsD)
       (at-pick1 _ atD)
       (en-pick1 ensD)
       (al-pick1 eqρ destAl)
       ix ss sn lf-pick1) =
    let en = trans ix eqi
        es = trans ss eqs
        go = sendCont {n = ir c} {s = slotR c} {base = envIR c} {ρi = ρi}
               {pend = pend′} {suf = suf} {env = ρ′} {p = p}
               {nD = nD} {sD = sD} {sW = slotR c} {sW′ = sD}
               {ρden = ρden} {ρw = ρw} {w = wD} {dest = dest}
               bg en es es eqρ sn (cvd bg) wkD dh ds de
               cvD lkD hsD atD ensD destAl
        memN = subst (λ i → (i , bPick1 j) ∈ Hold.bsR h) (sym en) mem
        inv = pick1R g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                j r′ (seenR h memN) eq
        le = underR h (room-sound (cap g) (r2l c) (proj₁ inv))
        wk = Gone.wk go
        fwd = pickR1-fwd h u le wk
    in backR (pick1-r u le wk) (proj₁ fwd) (proj₂ fwd) eq

getRB : ∀ {g c t x p ρ′ pend′ r′} (h : Hold g c) →
        Unfold (envPR c) [] (right c) ρ′ pend′ (f-get t x p) →
        reactR g (abs c) ≡ AGo r′ →
        Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
getRB {g} {c} {t} {x} {p} {ρ′} {pend′} {r′} h u eq = on (rightStop h u)
  where
  on : Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
            (ir c) (slotR c) (envIR c) ρ′ pend′ (f-get t x p) →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  on (atAct suf ρi bg _
       (p-act (d-get nD sD .t .x j .p ρw wD wkD _ dest dh ds de)
              r-get _ _ ρden)
       (cp-act (c-get mem cvD))
       (lk-get eqi eqs _ lkD)
       (hs-get hsD)
       (at-get _ atD)
       (en-get ensD)
       (al-get eqρ destAl)
       ix ss sn lf-get) =
    let en = trans ix eqi
        es = trans ss eqs
        go = sendCont {n = ir c} {s = slotR c} {base = envIR c} {ρi = ρi}
               {pend = pend′} {suf = suf} {env = ρ′} {p = p}
               {nD = nD} {sD = sD} {sW = suc (slotR c)} {sW′ = suc sD}
               {ρden = ρden} {ρw = ρw} {w = wD} {dest = dest}
               bg en es (cong suc es) eqρ sn (cvd bg) wkD dh ds de
               cvD lkD hsD atD ensD destAl
        memI = subst (λ i → (i , bGet t sD j) ∈ Hold.bsR h) (sym en) mem
        memN = subst (λ z → (ir c , bGet t z j) ∈ Hold.bsR h) (sym es) memI
        inv = getR g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                t (slotR c) j r′ (seenR h memN) eq
        k = proj₁ inv
        rest = proj₁ (proj₂ inv)
        a = proj₁ (proj₂ (proj₂ inv))
        qeq = proj₁ (proj₂ (proj₂ (proj₂ inv)))
        nthG = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ inv))))
        fit = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ inv)))))
        nthC = subst (λ al → nthA al k ≡ just a) (sym (Hold.α h)) nthG
        wk = Gone.wk go
        fwd = getR-fwd h u qeq nthC fit wk
    in backR (get-r u qeq nthC fit wk) (proj₁ fwd) (proj₂ fwd) eq

coverRB : ∀ {g c p q ρ′ pend′ r′} (h : Hold g c) →
          Unfold (envPR c) [] (right c) ρ′ pend′ (f-cover p q) →
          reactR g (abs c) ≡ AGo r′ →
          Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
coverRB {g} {c} {p} {q} {ρ′} {pend′} {r′} h u eq = on (rightStop h u)
  where
  on : Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
            (ir c) (slotR c) (envIR c) ρ′ pend′ (f-cover p q) →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  on (atAct suf ρi bg _
       (p-act (d-cover nD sD i j .p .q ρw w1D w2D wk1D _ wk2D _
                       dp dq hp sp deP hq sq deQ)
              r-cover _ _ ρden)
       (cp-act (c-cover mem cvP cvQ))
       (lk-cover eqi eqs _ lkP lkQ)
       (hs-cover hsP hsQ)
       (at-cover _ atP atQ)
       (en-cover ensP ensQ)
       (al-cover eqρ alP alQ)
       ix ss sn lf-cover) =
    let en = trans ix eqi
        es = trans ss eqs
        go = sendCont {n = ir c} {s = slotR c} {base = envIR c} {ρi = ρi}
               {pend = pend′} {suf = suf} {env = ρ′} {p = p}
               {nD = nD} {sD = sD} {sW = slotR c} {sW′ = sD}
               {ρden = ρden} {ρw = ρw} {w = w1D} {dest = dp}
               bg en es es eqρ sn (cvd bg) wk1D hp sp deP
               cvP lkP hsP atP ensP alP
        extW = ext-leaf suf pend′ (ir c) (slotR c) nD sD ρden (envIR c)
                 ρw ρi suf en es refl eqρ (run bg) sn (cvd bg)
        wkI = walk-ext [] ρw ρi q (next w1D) (slotN w1D) w2D extW wk2D
        wk2 = subst (λ e → walk [] e q (next w1D) (slotN w1D) ≡ just w2D)
                (run bg) wkI
        memN = subst (λ z → (z , bCover i j) ∈ Hold.bsR h) (sym en) mem
        inv = coverR g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                i j r′ (seenR h memN) eq
        wk1 = Gone.wk go
    in branch (proj₂ inv) wk1 wk2
    where
    branch : ∀ {rest} →
             (l2r c ≡ lab false ∷ rest ×
              r′ ≡ rc (il c) i rest (r2l c) (el c) (er c)) ⊎
             (l2r c ≡ lab true ∷ rest ×
              r′ ≡ rc (il c) j rest (r2l c) (el c) (er c)) →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                  (suc (ir c)) (slotR c) ≡ just w1D →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) q
                  (next w1D) (slotN w1D) ≡ just w2D →
             Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
    branch (inj₁ (qeq , _)) wk1 wk2 =
      let fwd = coverR0-fwd h u qeq wk1
      in backR (cover0-r u qeq wk1) (proj₁ fwd) (proj₂ fwd) eq
    branch (inj₂ (qeq , _)) wk1 wk2 =
      let fwd = coverR1-fwd h u qeq wk1 wk2
      in backR (cover1-r u qeq wk1 wk2) (proj₁ fwd) (proj₂ fwd) eq

igetRB : ∀ {g c x p q ρ′ pend′ r′} (h : Hold g c) →
         Unfold (envPR c) [] (right c) ρ′ pend′ (f-iget x p q) →
         reactR g (abs c) ≡ AGo r′ →
         Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
igetRB {g} {c} {x} {p} {q} {ρ′} {pend′} {r′} h u eq = on (rightStop h u)
  where
  on : Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
            (ir c) (slotR c) (envIR c) ρ′ pend′ (f-iget x p q) →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  on (atAct suf ρi bg _
       (p-act (d-iget nD sD .x i j .p .q ρw w1D w2D wk1D _ wk2D _
                      dp dq hp sp deP hq sq deQ)
              r-iget _ _ ρden)
       (cp-act (c-iget mem cvP cvQ))
       (lk-iget eqi eqs _ lkP lkQ)
       (hs-iget hsP hsQ)
       (at-iget _ atP atQ)
       (en-iget ensP ensQ)
       (al-iget eqρ alP alQ)
       ix ss sn lf-iget) =
    let en = trans ix eqi
        es = trans ss eqs
        go = sendCont {n = ir c} {s = slotR c} {base = envIR c} {ρi = ρi}
               {pend = pend′} {suf = suf} {env = ρ′} {p = p}
               {nD = nD} {sD = sD} {sW = suc (slotR c)} {sW′ = suc sD}
               {ρden = ρden} {ρw = ρw} {w = w1D} {dest = dp}
               bg en es (cong suc es) eqρ sn (cvd bg) wk1D hp sp deP
               cvP lkP hsP atP ensP alP
        extW = ext-leaf suf pend′ (ir c) (slotR c) nD sD ρden (envIR c)
                 ρw ρi suf en es refl eqρ (run bg) sn (cvd bg)
        wkI = walk-ext [] ρw ρi q (next w1D) (slotN w1D) w2D extW wk2D
        wk2 = subst (λ e → walk [] e q (next w1D) (slotN w1D) ≡ just w2D)
                (run bg) wkI
        memI = subst (λ z → (z , bIget sD i j) ∈ Hold.bsR h) (sym en) mem
        memN = subst (λ z → (ir c , bIget z i j) ∈ Hold.bsR h) (sym es) memI
        inv = igetR g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                (slotR c) i j r′ (seenR h memN) eq
        wk1 = Gone.wk go
    in branch (proj₂ (proj₂ inv)) wk1 wk2
    where
    branch : ∀ {k rest} →
             (l2r c ≡ pay k ∷ rest ×
              nthA (alpha g) k ≡ just (aBit false) ×
              r′ ≡ rc (il c) i rest (r2l c) (el c)
                     (setNth (slotR c) (suc k) (er c))) ⊎
             (l2r c ≡ pay k ∷ rest ×
              nthA (alpha g) k ≡ just (aBit true) ×
              r′ ≡ rc (il c) j rest (r2l c) (el c)
                     (setNth (slotR c) (suc k) (er c))) →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                  (suc (ir c)) (suc (slotR c)) ≡ just w1D →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) q
                  (next w1D) (slotN w1D) ≡ just w2D →
             Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
    branch {k} (inj₁ (qeq , nthG , _)) wk1 wk2 =
      let nthC = subst (λ al → nthA al k ≡ just (aBit false)) (sym (Hold.α h)) nthG
          fwd = igetR0-fwd h u qeq nthC wk1
      in backR (iget0-r u qeq nthC wk1) (proj₁ fwd) (proj₂ fwd) eq
    branch {k} (inj₂ (qeq , nthG , _)) wk1 wk2 =
      let nthC = subst (λ al → nthA al k ≡ just (aBit true)) (sym (Hold.α h)) nthG
          fwd = igetR1-fwd h u qeq nthC wk1 wk2
      in backR (iget1-r u qeq nthC wk1 wk2) (proj₁ fwd) (proj₂ fwd) eq

mgetRB : ∀ {g c t x as ρ′ pend′ r′} (h : Hold g c) →
         Unfold (envPR c) [] (right c) ρ′ pend′ (f-mget t x as) →
         reactR g (abs c) ≡ AGo r′ →
         Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
mgetRB {g} {c} {t} {x} {as} {ρ′} {pend′} {r′} h u eq = on (rightStop h u)
  where
  on : Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
            (ir c) (slotR c) (envIR c) ρ′ pend′ (f-mget t x as) →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  on (atAct suf ρi bg _
       (p-act (d-mget nD sD .t .x named .as ρw ws _ _ wkD enW _)
              r-mget _ _ ρden)
       (cp-act (c-mget mem _))
       (lk-mget eqi eqs _ _)
       (hs-mget _)
       (at-mget _ _)
       (en-mget _)
       (al-mget eqρ _)
       ix ss sn lf-mget) =
    let en = trans ix eqi
        es = trans ss eqs
        memI = subst (λ z → (z , bMget t sD named) ∈ Hold.bsR h) (sym en) mem
        memN = subst (λ z → (ir c , bMget t z named) ∈ Hold.bsR h) (sym es) memI
        inv = mgetR g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                t (slotR c) named r′ (seenR h memN) eq
        k = proj₁ inv
        rest = proj₁ (proj₂ inv)
        a = proj₁ (proj₂ (proj₂ inv))
        nm = proj₁ (proj₂ (proj₂ (proj₂ inv)))
        j = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ inv))))
        packed = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ inv))))
        qeq = proj₁ packed
        nthG = proj₁ (proj₂ packed)
        fit = proj₁ (proj₂ (proj₂ packed))
        con = proj₁ (proj₂ (proj₂ (proj₂ packed)))
        toN = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ packed))))
        toE = subst (λ xs → armTo nm xs ≡ just j) (sym enW) toN
        got = arm-of {name = nm} {j = j} as wkD toE
        w = proj₁ got
        proc = proj₁ (proj₂ got)
        hit0 = proj₁ (proj₂ (proj₂ got))
        extW = ext-leaf suf pend′ (ir c) (slotR c) nD sD ρden (envIR c)
                 ρw ρi suf en es refl eqρ (run bg) sn (cvd bg)
        hit1 = armGo-ext as extW hit0
        hit2 = subst (λ z → armGo ρi nm as (suc z) (suc sD) ≡ just (w , proc))
                 (sym en) hit1
        hit3 = subst (λ z → armGo ρi nm as (suc (ir c)) (suc z) ≡ just (w , proc))
                 (sym es) hit2
        hit4 = subst (λ e → armGo e nm as (suc (ir c)) (suc (slotR c)) ≡ just (w , proc))
                 (run bg) hit3
        nthC = subst (λ al → nthA al k ≡ just a) (sym (Hold.α h)) nthG
        fwd = mgetR-fwd h u qeq nthC fit con hit4
    in backR (mget-r u qeq nthC fit con hit4) (proj₁ fwd) (proj₂ fwd) eq

------------------------------------------------------------------------
-- A graph step is the source step of the focus the unfold reached.
-- `fin` is the stutter, handled by `final-iff`, so it is excluded.
------------------------------------------------------------------------

stepLB : ∀ {g c r′} (h : Hold g c) →
         reactL g (abs c) ≡ AGo r′ →
         Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
stepLB {g} {c} {r′} h eq = on (unfoldL h)
  where
  on : (o : Opened (envPL c) [] (left c)) →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  on o = onF (f o) (unf o)
    where
    onF : (foc : Focus) →
          Unfold (envPL c) [] (left c) (ρ′ o) (pend′ o) foc →
          Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
    onF f-done u = ⊥-elim (halt-stuckL h (leftStop h u) h-done eq)
    onF f-stop u = ⊥-elim (halt-stuckL h (leftStop h u) h-stop eq)
    onF (f-put a p) u = sendL h u eq
    onF (f-pick0 p) u = pick0B h u eq
    onF (f-pick1 p) u = pick1B h u eq
    onF (f-get t x p) u = getB h u eq
    onF (f-cover p q) u = coverB h u eq
    onF (f-iget x p q) u = igetB h u eq
    onF (f-mget t x as) u = mgetB h u eq

stepRB : ∀ {g c r′} (h : Hold g c) →
         reactR g (abs c) ≡ AGo r′ →
         Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
stepRB {g} {c} {r′} h eq = on (unfoldR h)
  where
  on : (o : Opened (envPR c) [] (right c)) →
       Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
  on o = onF (f o) (unf o)
    where
    onF : (foc : Focus) →
          Unfold (envPR c) [] (right c) (ρ′ o) (pend′ o) foc →
          Σ SConf (λ d → c ⟶ₛ d × abs d ≡ r′ × Hold g d)
    onF f-done u = ⊥-elim (halt-stuckR h (rightStop h u) h-done eq)
    onF f-stop u = ⊥-elim (halt-stuckR h (rightStop h u) h-stop eq)
    onF (f-put a p) u = sendR h u eq
    onF (f-pick0 p) u = pick0RB h u eq
    onF (f-pick1 p) u = pick1RB h u eq
    onF (f-get t x p) u = getRB h u eq
    onF (f-cover p q) u = coverRB h u eq
    onF (f-iget x p q) u = igetRB h u eq
    onF (f-mget t x as) u = mgetRB h u eq

sim-bwd : ∀ {g c w r′} →
          Hold g c →
          Step g (abs c) w r′ →
          w ≢ fin →
          Σ SConf (λ c′ → c ⟶ₛ c′ × abs c′ ≡ r′)
sim-bwd h (stepL eq) _ =
  let d , st , ab , _ = stepLB h eq in d , st , ab
sim-bwd h (stepR eq) _ =
  let d , st , ab , _ = stepRB h eq in d , st , ab
sim-bwd _ (finish _ _ _) neq = ⊥-elim (neq refl)

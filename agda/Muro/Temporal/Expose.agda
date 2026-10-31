------------------------------------------------------------------------
-- A source unfold, read against the cursor's place.
-- Peeling and jumping stay inside one step. The action at the end is
-- the block the graph runs, and the continuation is the next cursor.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Expose where

open import Data.Bool.Base using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Muro.AsyncRec
  using (Atom; Block; bPut; bEcho)
open import Muro.Temporal.Bridge using (distinct)
open import Muro.Temporal.Pic using (_∈_)
open import Muro.Temporal.Source
  using ( SProc; Pay; pEcho; W; EnvI; EnvP; addPend; lookupI; walk; asAtom
        ; smu; Bound; b-here; b-there
        ; Focus; f-put; Unfold; u-put; u-mu; u-var )
open W
open import Muro.Temporal.Den
  using ( Place; p-mu; p-act; p-jump; Den; d-put; d-echo; Table; Link; Links
        ; lk-mu; lk-jump; lk-put; lk-echo
        ; At; at-mu; at-put; at-echo
        ; CovP; cp-mu; cp-act; cp-jump; CovT
        ; c-put; c-echo
        ; Hosts; hs-mu; hs-put; hs-echo; hs-jump
        ; EchoNs; en-mu; en-put; en-echo; en-jump
        ; Align; al-mu; al-jump; al-put; al-echo
        ; headIx; slotOf; envOf
        ; InTab; place-of; link-of; ix-of; slot-at
        ; ix-head; slot-head; hosts-of; cov-of; tnames
        ; Recipe; r-put; r-echo; r-mu )
open import Muro.Temporal.Run
  using ( Cursor; Ext; Covered; Sync; sy1; Tied; td1; Knew; kn1
        ; ext-pend; cov-mu; cov-push; cov-cons; cov-pull; cov-cast
        ; runtime-pin; ext-front; kn-find; Found; kn-sync; kn-tied
        ; same-slot; sync-hit )
open import Muro.Temporal.Sim using (ix-eq; sl-eq)

------------------------------------------------------------------------
-- The denoted walk environment and the unfolded runtime environment
-- bind the same names at the action's counters.
------------------------------------------------------------------------

add-cast : ∀ xs n s n′ s′ ρ → n ≡ n′ → s ≡ s′ →
           addPend xs n s ρ ≡ addPend xs n′ s′ ρ
add-cast _ _ _ _ _ _ refl refl = refl

ext-leaf : ∀ suf pend n s nD sD ρden base ρw ρi pendD →
           n ≡ nD → s ≡ sD → pendD ≡ suf →
           ρw ≡ addPend pendD nD sD ρden →
           ρi ≡ addPend pend n s base →
           Ext ρden ρi →
           Covered suf pend base n s →
           Ext ρw ρi
ext-leaf suf pend n s nD sD ρden base ρw ρi pendD en es ep eqρ run sn cvd =
  subst (λ e → Ext e ρi) (sym ρw≡)
    (subst (λ e → Ext (addPend suf n s ρden) e) (sym run) extp)
  where
  extp : Ext (addPend suf n s ρden) (addPend pend n s base)
  extp = ext-pend suf pend n s ρden base (subst (Ext ρden) run sn) cvd
  ρw≡ : ρw ≡ addPend suf n s ρden
  ρw≡ = trans eqρ
          (trans (cong (λ xs → addPend xs nD sD ρden) ep)
            (add-cast suf nD sD n s ρden (sym en) (sym es)))

------------------------------------------------------------------------
-- The continuation cursor. Its index and slot are the walk's.
------------------------------------------------------------------------

arrive : ∀ {bs ns tab env ρi p} (dest : Place p) (w : W) →
         CovT tab bs → Links tab →
         Tied tab env → Sync tab env ρi → Knew ns tab env ρi →
         distinct (tnames tab) ≡ true →
         headIx dest ≡ entry w → slotOf dest ≡ atSlot w →
         CovP dest bs → Link dest → Hosts tab dest →
         At [] dest → EchoNs ns dest → Align [] dest →
         Ext (envOf dest) ρi →
         Cursor bs (entry w) (atSlot w) env ρi p
arrive {ns = ns} {tab = tab} dest w ct ls td sy kn nd dh ds cv lk hs at ens al sn =
  record
    { pl = dest ; cv = cv ; tab = tab ; ct = ct ; lk = lk ; ls = ls
    ; hs = hs ; td = td ; sy = sy ; echoNs = ns ; kn = kn ; ens = ens
    ; al = al ; ix = sym dh ; ss = sym ds ; sn = sn ; at = at ; nd = nd }

-- The cursor's fields that a peel or a jump does not match on.
record Bag (bs : List (ℕ × Block)) (ns : List String) (n s : ℕ)
           (base ρi : EnvI) (pend suf : List String)
           (env : EnvP) : Set where
  constructor bag
  field
    tab : Table
    ct : CovT tab bs
    ls : Links tab
    td : Tied tab env
    sy : Sync tab env ρi
    kn : Knew ns tab env ρi
    nd : distinct (tnames tab) ≡ true
    run : ρi ≡ addPend pend n s base
    cvd : Covered suf pend base n s
    pin : Covered suf [] ρi n s

open Bag

-- What an unfold to a send found. An echo is the other `f-put`.
data Send (bs : List (ℕ × Block)) (ns : List String) (n s : ℕ) (base : EnvI)
          (ρ′ : EnvP) (pend′ : List String) (a : Pay) (p : SProc) : Set where
  sent : (atom : Atom) (j : ℕ) (w : W) →
         asAtom a ≡ just atom → entry w ≡ j →
         (n , bPut atom j) ∈ bs →
         Cursor bs (entry w) (atSlot w) ρ′ (addPend pend′ n s base) p →
         Send bs ns n s base ρ′ pend′ a p
  echoed : (x : String) (sX j : ℕ) (w : W) →
           a ≡ pEcho x → entry w ≡ j →
           (n , bEcho sX j) ∈ bs →
           Cursor bs (entry w) (atSlot w) ρ′ (addPend pend′ n s base) p →
           Send bs ns n s base ρ′ pend′ a p

link-cast : ∀ {P : SProc} {pl pl′ : Place P} → pl ≡ pl′ → Link pl → Link pl′
link-cast refl lk = lk

hosts-cast : ∀ {P} {tab : Table} {pl pl′ : Place P} →
             pl ≡ pl′ → Hosts tab pl → Hosts tab pl′
hosts-cast refl hs = hs

cov-cast-pl : ∀ {P} {bs : List (ℕ × Block)} {pl pl′ : Place P} →
              pl ≡ pl′ → CovP pl bs → CovP pl′ bs
cov-cast-pl refl cv = cv

-- Peel and jump, then read the send. The cursor at the end is the
-- continuation, indexed at the counters the walk gave it.
openSend : ∀ {bs ns n s base ρi pend suf env proc a p ρ′ pend′}
             (bg : Bag bs ns n s base ρi pend suf env) →
           (pl : Place proc) → CovP pl bs → Link pl → Hosts (tab bg) pl →
           At suf pl → EchoNs ns pl → Align suf pl →
           n ≡ headIx pl → s ≡ slotOf pl → Ext (envOf pl) ρi →
           Unfold env pend proc ρ′ pend′ (f-put a p) →
           Send bs ns n s base ρ′ pend′ a p
openSend {n = n} {s = s} {base = base} {ρi = ρi} {pend = pend} {suf = suf}
         {env = env}
         bg (p-mu {p = q} x pl) (cp-mu cv) (lk-mu lk) (hs-mu inn eq hs)
         (at-mu miss atI) (en-mu ensI) (al-mu alI) ix ss sn (u-mu u) =
  openSend bg′ pl cv lk hs atI ensI alI ix ss sn′ u
  where
  ixE = ix-eq inn (ls bg) eq ix
  slE = sl-eq inn (ls bg) eq ss
  sn′ = ext-front {x = x} {i = n} {s = s} {ρ0 = envOf pl} {ρ = ρi}
          sn (inj₁ miss)
  pinX = runtime-pin {x = x} {ρ = ρi} {n = n} {s = s}
           inn ixE slE (nd bg) (sy bg)
  covX = cov-cons {x = x} {i = n} {s = s} {suf = suf} {ρ = ρi}
           {i0 = n} {s0 = s} (pin bg) pinX
  kn′ = kn1 {i = n} {s0 = s} {suf = suf} {pl = p-mu x pl}
          inn eq ixE slE (at-mu miss atI) (en-mu ensI) (al-mu alI)
          sn′ covX (kn bg)
  bg′ = bag (tab bg) (ct bg) (ls bg)
          (td1 inn (td bg))
          (sy1 {i = n} {s = s} inn ixE slE (sy bg))
          kn′ (nd bg)
          (cong ((x , n , s) ∷_) (run bg))
          (cov-mu {x = x} {suf = suf} {got = pend} {base = base} {n = n} {s = s}
             (cvd bg))
          (cov-push {x = x} {suf = suf} {ρ = ρi} {n = n} {s = s} (pin bg))

openSend {bs = bs} {ns = ns} {n = n} {s = s} {base = base} {ρi = ρi}
         {pend = pend} {env = env}
         bg (p-jump x iJ sJ ρJ) cp-jump (lk-jump look) hs-jump atJ en-jump
         al-jump ix ss sn (u-var {body = body} b u) =
  openSend bgJ (Found.pl f)
    (cov-cast-pl (Found.peq f) (cov-of (ct bg) (Found.m f)))
    (link-cast (Found.peq f) (link-of (Found.m f)))
    (hosts-cast (Found.peq f) (hosts-of (ls bg) (Found.m f)))
    (Found.at f) (Found.ens f) (Found.al f)
    n≡head s≡slot (Found.ext f) u
  where
  hit = sn x iJ sJ look
  got = sync-hit (sy bg) hit
  mQ = proj₁ (proj₂ got)
  ixQ = proj₁ (proj₂ (proj₂ got))
  slQ = proj₂ (proj₂ (proj₂ got))
  f : Found ns (tab bg) x body ρi
  f = kn-find {ns = ns} {x = x} {P = body} {tab = tab bg} {env = env} {ρ = ρi}
        (kn bg) b (nd bg)
  sm = same-slot (Found.m f) mQ (nd bg)
  ixQ≡n = trans ixQ (sym ix)
  ixF≡n = trans (proj₁ sm) ixQ≡n
  n≡head = trans (sym ixF≡n)
             (trans (ix-head (ls bg) (Found.m f)) (cong headIx (Found.peq f)))
  i≡n : Found.i f ≡ n
  i≡n = trans (sym (Found.ix≡ f)) ixF≡n
  slQ≡s = trans slQ (sym ss)
  slF≡s = trans (proj₂ sm) slQ≡s
  s≡slot = trans (sym slF≡s)
             (trans (slot-head (ls bg) (Found.m f)) (cong slotOf (Found.peq f)))
  s0≡s : Found.s0 f ≡ s
  s0≡s = trans (sym (Found.sl≡ f)) slF≡s
  pinJ : Covered (Found.suf f) [] ρi n s
  pinJ = cov-cast {suf = Found.suf f} {got = []} {base = ρi}
           {i = Found.i f} {s = Found.s0 f} {n = n} {s′ = s}
           i≡n s0≡s (Found.cov f)
  pinAdd = subst (λ e → Covered (Found.suf f) [] e n s) (run bg) pinJ
  cvdJ = cov-pull {suf = Found.suf f} {pend = pend} {base = base} {n = n} {s = s}
           pinAdd
  bgJ = bag (tab bg) (ct bg) (ls bg) (td bg) (sy bg) (kn bg) (nd bg)
          (run bg) cvdJ pinJ

openSend {bs = bs} {ns = ns} {n = n} {s = s} {base = base} {ρi = ρi}
         {pend = pend} {suf = suf} {env = env}
         bg (p-act (d-put nD sD a atom j p ρw w aeq wk ej dest dh ds de)
                   r-put i0 s0 ρden)
         (cp-act (c-put mem cvD))
         (lk-put eqi eqs eqρL lkD)
         (hs-put hsD)
         (at-put ep atD)
         (en-put ensD)
         (al-put eqρ destAl)
         ix ss sn u-put =
  sent atom j w aeq ej memN cur
  where
  en = trans ix eqi
  es = trans ss eqs
  memN = subst (λ i → (i , bPut atom j) ∈ bs) (sym en) mem
  extW = ext-leaf suf pend n s nD sD ρden base ρw ρi suf
           en es refl eqρ (run bg) sn (cvd bg)
  snD = subst (λ e → Ext e ρi) (sym de) extW
  cur0 = arrive {ns = ns} {tab = tab bg} dest w (ct bg) (ls bg)
           (td bg) (sy bg) (kn bg) (nd bg)
           dh ds cvD lkD hsD atD ensD destAl snD
  cur = subst (λ e → Cursor bs (entry w) (atSlot w) env e p) (run bg) cur0

openSend {bs = bs} {ns = ns} {n = n} {s = s} {base = base} {ρi = ρi}
         {pend = pend} {suf = suf} {env = env}
         bg (p-act (d-echo nD sD x nsE sX j p ρw w fd wk ej dest dh ds de)
                   r-echo i0 s0 ρden)
         (cp-act (c-echo mem cvD))
         (lk-echo eqi eqs eqρL lkD)
         (hs-echo hsD)
         (at-echo ep atD)
         (en-echo ns≡ ensD)
         (al-echo eqρ destAl)
         ix ss sn u-put =
  echoed x sX j w refl ej memN cur
  where
  en = trans ix eqi
  es = trans ss eqs
  memN = subst (λ i → (i , bEcho sX j) ∈ bs) (sym en) mem
  extW = ext-leaf suf pend n s nD sD ρden base ρw ρi suf
           en es refl eqρ (run bg) sn (cvd bg)
  snD = subst (λ e → Ext e ρi) (sym de) extW
  cur0 = arrive {ns = ns} {tab = tab bg} dest w (ct bg) (ls bg)
           (td bg) (sy bg) (kn bg) (nd bg)
           dh ds cvD lkD hsD atD ensD destAl snD
  cur = subst (λ e → Cursor bs (entry w) (atSlot w) env e p) (run bg) cur0

openSend _ (p-act _ (r-mu _) _ _ _) _ () _ _ _ _ _ _ _ _

------------------------------------------------------------------------
-- A source unfold, read against the cursor's place.
-- Peeling and jumping stay inside one step. The action at the end is
-- the block the graph runs, and the continuation is the next cursor.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Expose where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Muro.AsyncRec
  using ( Atom; Block; bPut; bEcho; Tok; pay; snoc; Graph
        ; RConf; rc; Act; AGo; findA; lookB; materialise; reactL; reactR
        ; room; slotVal; bPick0; bPick1; bGet; bCover; bIget; bMget; aBit
        ; bDone; bStop; isHalt
        ; lab; setNth; nthA; fits; conOf; armTo )
open import Muro.Temporal.Bridge using (distinct)
open import Muro.Temporal.Pic using (_∈_; root-at; ents)
open import Muro.Temporal.Source
  using ( SProc; SConf; abs; Pay; pEcho; Arm; aok; abad; W; EnvI; EnvP; addPend; lookupI
        ; walk; walkArms; armGo; findS; asAtom
        ; smu; sdone; sstop; sput; sget; spick0; spick1; scover; siget; smget
        ; Bound; b-here; b-there
        ; Focus; f-put; f-done; f-stop; f-get; f-pick0; f-pick1; f-cover; f-iget; f-mget
        ; HaltF; h-done; h-stop
        ; Unfold; u-put; u-mu; u-var; u-done; u-stop; u-get; u-pick0; u-pick1
        ; u-cover; u-iget; u-mget
        ; _⟶ₛ_
        ; put-l; echo-l; pick0-l; pick1-l; get-l; cover0-l; cover1-l
        ; iget0-l; iget1-l; mget-l
        ; put-r; echo-r; pick0-r; pick1-r; get-r; cover0-r; cover1-r
        ; iget0-r; iget1-r; mget-r )
  renaming (snoc to ssnoc; finish to sfinish)
open SConf
open import Muro.Temporal using (Step; stepL; stepR; finish; Who; lside; rside; fin)
open import Muro.Temporal.Fire
  using ( react-put; react-echo; react-pick0; react-pick1; react-get
        ; react-cover0; react-cover1; react-iget0; react-iget1; react-mget
        ; halt-of; isHalt-done; isHalt-stop
        ; reactR-put; reactR-echo; reactR-pick0; reactR-pick1; reactR-get
        ; reactR-cover0; reactR-cover1; reactR-iget0; reactR-iget1; reactR-mget
        ; room-yes; snoc≡ )
open W
open import Muro.Temporal.Den
  using ( Place; p-mu; p-act; p-jump; Den; d-put; d-echo; d-pick0; d-pick1
        ; d-done; d-stop; d-get; d-cover; d-iget; d-mget
        ; Table; Link; Links; LinkA; la0; la1
        ; ArmPs; ap0; ap1
        ; lk-mu; lk-jump; lk-done; lk-stop; lk-put; lk-echo; lk-pick0; lk-pick1
        ; lk-get; lk-cover; lk-iget; lk-mget
        ; At; AtA; ata0; ata1
        ; at-mu; at-put; at-echo; at-pick0; at-pick1; at-get; at-cover; at-iget; at-mget
        ; CovP; cp-mu; cp-act; cp-jump; CovT; CovA; ca0; ca1
        ; c-done; c-stop; c-put; c-echo; c-pick0; c-pick1; c-get; c-cover; c-iget; c-mget
        ; Hosts; HostsA; ha0; ha1
        ; hs-mu; hs-put; hs-echo; hs-jump; hs-pick0; hs-pick1; hs-get
        ; hs-cover; hs-iget; hs-mget
        ; EchoNs; EchoNsA; ea0; ea1
        ; en-mu; en-put; en-echo; en-jump; en-pick0; en-pick1; en-get
        ; en-cover; en-iget; en-mget
        ; Align; AlignA; aa0; aa1
        ; al-mu; al-jump; al-put; al-echo; al-pick0; al-pick1; al-get
        ; al-cover; al-iget; al-mget
        ; headIx; slotOf; envOf
        ; InTab; place-of; link-of; ix-of; slot-at
        ; ix-head; slot-head; hosts-of; cov-of; tnames
        ; Recipe; r-done; r-stop; r-put; r-echo; r-pick0; r-pick1; r-get
        ; r-cover; r-iget; r-mget; r-mu )
open import Muro.Temporal.Run
  using ( Cursor; Ext; Covered; Sync; sy1; Tied; td1; Knew; kn1
        ; ext-pend; cov-mu; cov-push; cov-cons; cov-pull; cov-cast
        ; cov-id; runtime-pin; ext-front; kn-find; Found; kn-sync; kn-tied
        ; same-slot; sync-hit; walk-ext; just-inj; Hold )
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
         walk [] (addPend pend′ n s base) p (suc n) s ≡ just w →
         (cur : Cursor bs (entry w) (atSlot w) ρ′ (addPend pend′ n s base) p) →
         Cursor.echoNs cur ≡ ns →
         Send bs ns n s base ρ′ pend′ a p
  echoed : (x : String) (sX j : ℕ) (w : W) →
           a ≡ pEcho x → findS x ns ≡ just sX → entry w ≡ j →
           (n , bEcho sX j) ∈ bs →
           walk [] (addPend pend′ n s base) p (suc n) s ≡ just w →
           (cur : Cursor bs (entry w) (atSlot w) ρ′ (addPend pend′ n s base) p) →
           Cursor.echoNs cur ≡ ns →
           Send bs ns n s base ρ′ pend′ a p

-- The continuation walk does not depend on which of two equal counters it starts at.
walk-idx : ∀ {ρ p n n′ s s′ w} → n ≡ n′ → s ≡ s′ →
           walk [] ρ p (suc n′) s′ ≡ just w →
           walk [] ρ p (suc n) s ≡ just w
walk-idx refl refl eq = eq

link-cast : ∀ {P : SProc} {pl pl′ : Place P} → pl ≡ pl′ → Link pl → Link pl′
link-cast refl lk = lk

hosts-cast : ∀ {P} {tab : Table} {pl pl′ : Place P} →
             pl ≡ pl′ → Hosts tab pl → Hosts tab pl′
hosts-cast refl hs = hs

cov-cast-pl : ∀ {P} {bs : List (ℕ × Block)} {pl pl′ : Place P} →
              pl ≡ pl′ → CovP pl bs → CovP pl′ bs
cov-cast-pl refl cv = cv

-- Substituting the cursor's runtime environment keeps its echo names.
echo-env : ∀ {bs i s env ρ ρ′ p} (eq : ρ ≡ ρ′) (cur : Cursor bs i s env ρ p) →
           Cursor.echoNs (subst (λ e → Cursor bs i s env e p) eq cur) ≡
           Cursor.echoNs cur
echo-env refl _ = refl

-- The continuation a one-arm action walked, in the runtime environment.
record Gone (bs : List (ℕ × Block)) (ns : List String) (n sW : ℕ)
            (env : EnvP) (ρRun : EnvI) (p : SProc) (w : W) : Set where
  constructor gone
  field
    wk : walk [] ρRun p (suc n) sW ≡ just w
    cur : Cursor bs (entry w) (atSlot w) env ρRun p
    nse : Cursor.echoNs cur ≡ ns

sendCont : ∀ {bs ns n s base ρi pend suf env p nD sD sW sW′ ρden ρw w}
             {dest : Place p} →
           (bg : Bag bs ns n s base ρi pend suf env) →
           n ≡ nD → s ≡ sD → sW ≡ sW′ →
           ρw ≡ addPend suf nD sD ρden →
           Ext ρden ρi →
           Covered suf pend base n s →
           walk [] ρw p (suc nD) sW′ ≡ just w →
           headIx dest ≡ entry w → slotOf dest ≡ atSlot w → envOf dest ≡ ρw →
           CovP dest bs → Link dest → Hosts (Bag.tab bg) dest →
           At [] dest → EchoNs ns dest → Align [] dest →
           Gone bs ns n sW env (addPend pend n s base) p w
sendCont {bs = bs} {ns = ns} {n = n} {s = s} {base = base} {ρi = ρi}
         {pend = pend} {suf = suf} {env = env} {p = p} {nD = nD} {sD = sD}
         {sW = sW} {sW′ = sW′} {ρden = ρden} {ρw = ρw} {w = w} {dest = dest}
         bg en es eW eqρ sn cvd wk dh ds de cv lk hs at ens al =
  gone wkRun cur (echo-env (run bg) cur0)
  where
  extW = ext-leaf suf pend n s nD sD ρden base ρw ρi suf
           en es refl eqρ (run bg) sn cvd
  wkI : walk [] ρi p (suc nD) sW′ ≡ just w
  wkI = walk-ext [] ρw ρi p (suc nD) sW′ w extW wk
  wkN : walk [] ρi p (suc n) sW ≡ just w
  wkN = walk-idx {ρ = ρi} {p = p} {n = n} {n′ = nD} {s = sW} {s′ = sW′} {w = w}
          en eW wkI
  wkRun = subst (λ e → walk [] e p (suc n) sW ≡ just w) (run bg) wkN
  snD = subst (λ e → Ext e ρi) (sym de) extW
  cur0 = arrive {ns = ns} {tab = tab bg} dest w (ct bg) (ls bg)
           (td bg) (sy bg) (kn bg) (nd bg)
           dh ds cv lk hs at ens al snD
  cur = subst (λ e → Cursor bs (entry w) (atSlot w) env e p) (run bg) cur0

-- A focus that is already an action or a halt. Peels and jumps are not leaves.
data Leaf : Focus → SProc → Set where
  lf-done : Leaf f-done sdone
  lf-stop : Leaf f-stop sstop
  lf-put : ∀ {a p} → Leaf (f-put a p) (sput a p)
  lf-get : ∀ {t x p} → Leaf (f-get t x p) (sget t x p)
  lf-pick0 : ∀ {p} → Leaf (f-pick0 p) (spick0 p)
  lf-pick1 : ∀ {p} → Leaf (f-pick1 p) (spick1 p)
  lf-cover : ∀ {p q} → Leaf (f-cover p q) (scover p q)
  lf-iget : ∀ {x p q} → Leaf (f-iget x p q) (siget x p q)
  lf-mget : ∀ {t x as} → Leaf (f-mget t x as) (smget t x as)

-- The place an unfold reaches, with the bag the walk was read under.
record Stop (bs : List (ℕ × Block)) (ns : List String) (n s : ℕ)
            (base : EnvI) (ρ′ : EnvP) (pend′ : List String) (f : Focus) : Set where
  constructor atAct
  field
    suf : List String
    ρi : EnvI
    bg : Bag bs ns n s base ρi pend′ suf ρ′
    proc : SProc
    pl : Place proc
    cv : CovP pl bs
    lk : Link pl
    hs : Hosts (Bag.tab bg) pl
    at : At suf pl
    ens : EchoNs ns pl
    al : Align suf pl
    ix : n ≡ headIx pl
    ss : s ≡ slotOf pl
    sn : Ext (envOf pl) ρi
    lf : Leaf f proc

-- A leaf unfold does not move the bag. `ρ′` and `pend′` are its `env` and `pend`.
land : ∀ {bs ns n s base ρi pend suf env proc f} →
       (bg : Bag bs ns n s base ρi pend suf env) →
       (pl : Place proc) → CovP pl bs → Link pl → Hosts (Bag.tab bg) pl →
       At suf pl → EchoNs ns pl → Align suf pl →
       n ≡ headIx pl → s ≡ slotOf pl → Ext (envOf pl) ρi →
       Leaf f proc →
       Stop bs ns n s base env pend f
land {ρi = ρi} {suf = suf} bg pl cv lk hs at ens al ix ss sn lf =
  atAct suf ρi bg _ pl cv lk hs at ens al ix ss sn lf

-- Peel a mu and follow a jump. Stop at the action, the halt, or the end.
descend : ∀ {bs ns n s base ρi pend suf env proc ρ′ pend′ f}
            (bg : Bag bs ns n s base ρi pend suf env) →
          (pl : Place proc) → CovP pl bs → Link pl → Hosts (Bag.tab bg) pl →
          At suf pl → EchoNs ns pl → Align suf pl →
          n ≡ headIx pl → s ≡ slotOf pl → Ext (envOf pl) ρi →
          Unfold env pend proc ρ′ pend′ f →
          Stop bs ns n s base ρ′ pend′ f
descend {n = n} {s = s} {base = base} {ρi = ρi} {pend = pend} {suf = suf}
        {env = env}
        bg (p-mu {p = q} x pl) (cp-mu cv) (lk-mu lk) (hs-mu inn eq hs)
        (at-mu miss atI) (en-mu ensI) (al-mu alI) ix ss sn (u-mu u) =
  descend bg′ pl cv lk hs atI ensI alI ix ss sn′ u
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

descend {bs = bs} {ns = ns} {n = n} {s = s} {base = base} {ρi = ρi}
        {pend = pend} {env = env}
        bg (p-jump x iJ sJ ρJ) cp-jump (lk-jump look) hs-jump atJ en-jump
        al-jump ix ss sn (u-var {body = body} b u) =
  descend bgJ (Found.pl f)
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

descend bg pl@(p-act _ _ _ _ _) cv lk hs at ens al ix ss sn u-done =
  land bg pl cv lk hs at ens al ix ss sn lf-done
descend bg pl@(p-act _ _ _ _ _) cv lk hs at ens al ix ss sn u-stop =
  land bg pl cv lk hs at ens al ix ss sn lf-stop
descend bg pl@(p-act _ _ _ _ _) cv lk hs at ens al ix ss sn u-put =
  land bg pl cv lk hs at ens al ix ss sn lf-put
descend bg pl@(p-act _ _ _ _ _) cv lk hs at ens al ix ss sn u-get =
  land bg pl cv lk hs at ens al ix ss sn lf-get
descend bg pl@(p-act _ _ _ _ _) cv lk hs at ens al ix ss sn u-pick0 =
  land bg pl cv lk hs at ens al ix ss sn lf-pick0
descend bg pl@(p-act _ _ _ _ _) cv lk hs at ens al ix ss sn u-pick1 =
  land bg pl cv lk hs at ens al ix ss sn lf-pick1
descend bg pl@(p-act _ _ _ _ _) cv lk hs at ens al ix ss sn u-cover =
  land bg pl cv lk hs at ens al ix ss sn lf-cover
descend bg pl@(p-act _ _ _ _ _) cv lk hs at ens al ix ss sn u-iget =
  land bg pl cv lk hs at ens al ix ss sn lf-iget
descend bg pl@(p-act _ _ _ _ _) cv lk hs at ens al ix ss sn u-mget =
  land bg pl cv lk hs at ens al ix ss sn lf-mget
descend _ (p-act _ (r-mu _) _ _ _) _ () _ _ _ _ _ _ _

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
  sent atom j w aeq ej memN wkRun cur (echo-env (run bg) cur0)
  where
  en = trans ix eqi
  es = trans ss eqs
  memN = subst (λ i → (i , bPut atom j) ∈ bs) (sym en) mem
  extW = ext-leaf suf pend n s nD sD ρden base ρw ρi suf
           en es refl eqρ (run bg) sn (cvd bg)
  wkI : walk [] ρi p (suc nD) sD ≡ just w
  wkI = walk-ext [] ρw ρi p (suc nD) sD w extW wk
  wkN : walk [] ρi p (suc n) s ≡ just w
  wkN = walk-idx {ρ = ρi} {p = p} {n = n} {n′ = nD} {s = s} {s′ = sD} {w = w}
          en es wkI
  wkRun = subst (λ e → walk [] e p (suc n) s ≡ just w) (run bg) wkN
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
  echoed x sX j w refl fdN ej memN wkRun cur (echo-env (run bg) cur0)
  where
  en = trans ix eqi
  es = trans ss eqs
  fdN = subst (λ z → findS x z ≡ just sX) (sym ns≡) fd
  memN = subst (λ i → (i , bEcho sX j) ∈ bs) (sym en) mem
  extW = ext-leaf suf pend n s nD sD ρden base ρw ρi suf
           en es refl eqρ (run bg) sn (cvd bg)
  wkI : walk [] ρi p (suc nD) sD ≡ just w
  wkI = walk-ext [] ρw ρi p (suc nD) sD w extW wk
  wkN : walk [] ρi p (suc n) s ≡ just w
  wkN = walk-idx {ρ = ρi} {p = p} {n = n} {n′ = nD} {s = s} {s′ = sD} {w = w}
          en es wkI
  wkRun = subst (λ e → walk [] e p (suc n) s ≡ just w) (run bg) wkN
  snD = subst (λ e → Ext e ρi) (sym de) extW
  cur0 = arrive {ns = ns} {tab = tab bg} dest w (ct bg) (ls bg)
           (td bg) (sy bg) (kn bg) (nd bg)
           dh ds cvD lkD hsD atD ensD destAl snD
  cur = subst (λ e → Cursor bs (entry w) (atSlot w) env e p) (run bg) cur0

openSend _ (p-act _ (r-mu _) _ _ _) _ () _ _ _ _ _ _ _ _

------------------------------------------------------------------------
-- A cursor's echo names survive a substitution of the walk it sits on.
------------------------------------------------------------------------

ns-keep : ∀ {bs env ρ p} {w w′ : W} (eq : w ≡ w′)
          (cur : Cursor bs (entry w) (atSlot w) env ρ p) →
          Cursor.echoNs
            (subst (λ z → Cursor bs (entry z) (atSlot z) env ρ p) eq cur)
            ≡ Cursor.echoNs cur
ns-keep refl _ = refl

-- The configuration a left send steps to. `ssnoc` is the source queue.
afterTok : SConf → SProc → EnvP → List String → Tok → W → SConf
afterTok c p ρ′ pend′ t w =
  record c { left = p ; il = entry w ; slotL = atSlot w
           ; l2r = ssnoc (l2r c) t
           ; envPL = ρ′
           ; envIL = addPend pend′ (il c) (slotL c) (envIL c) }

afterPut : SConf → SProc → EnvP → List String → ℕ → W → SConf
afterPut c p ρ′ pend′ k w = afterTok c p ρ′ pend′ (pay k) w

-- The left cursor, read at the counters the configuration is standing on.
leftBag : ∀ {g} {c : SConf} (h : Hold g c) →
          Bag (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
              (il c) (slotL c) (envIL c) (envIL c) [] [] (envPL c)
leftBag {c = c} h =
  bag {bs = Hold.bsL h} {ns = Cursor.echoNs lc} {n = il c} {s = slotL c}
      {base = envIL c} {ρi = envIL c} {pend = []} {suf = []} {env = envPL c}
      (Cursor.tab lc) (Cursor.ct lc) (Cursor.ls lc)
      (Cursor.td lc) (Cursor.sy lc) (Cursor.kn lc) (Cursor.nd lc)
      refl
      (cov-id {xs = []} {base = envIL c} {n = il c} {s = slotL c})
      (cov-id {xs = []} {base = envIL c} {n = il c} {s = slotL c})
  where lc = Hold.leftC h

-- The block at the left cursor is the block `lookB` returns.
seenL : ∀ {g c b} (h : Hold g c) → (il c , b) ∈ Hold.bsL h →
        lookB (Graph.codeL g) (il c) ≡ just b
seenL {c = c} {b = b} h mem =
  subst (λ code → lookB code (il c) ≡ just b) (sym (Hold.cL h))
    (root-at (Hold.odL h) mem)

-- The source queue bound is the graph's `room` test.
roomL : ∀ {g c} (h : Hold g c) → length (l2r c) < cap c →
        room (Graph.cap g) (l2r c) ≡ true
roomL {g} {c} h le =
  room-yes (Graph.cap g) (l2r c)
    (subst (λ n → length (l2r c) < n) (Hold.κ h) le)

find≡ : ∀ x xs ys → xs ≡ ys → findS x xs ≡ findS x ys
find≡ _ _ _ refl = refl

-- Once the block has run, the continuation cursor is the next `Hold`.
closeTok : ∀ {g c p ρ′ pend′ j w wS} (t : Tok) (h : Hold g c) →
           reactL g (abs c) ≡
             AGo (rc j (ir c) (snoc (l2r c) t) (r2l c) (el c) (er c)) →
           entry wS ≡ j →
           walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                (suc (il c)) (slotL c) ≡ just wS →
           walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                (suc (il c)) (slotL c) ≡ just w →
           (cur : Cursor (Hold.bsL h) (entry wS) (atSlot wS) ρ′
                         (addPend pend′ (il c) (slotL c) (envIL c)) p) →
           Cursor.echoNs cur ≡ Cursor.echoNs (Hold.leftC h) →
           Step g (abs c) lside (abs (afterTok c p ρ′ pend′ t w)) ×
           Hold g (afterTok c p ρ′ pend′ t w)
closeTok {g} {c} {p} {ρ′} {pend′} {j} {w} {wS} t h reacted ej wkS wk cur nse =
  stepL moved , record
    { nL = Hold.nL h ; bsL = Hold.bsL h ; odL = Hold.odL h ; cL = Hold.cL h
    ; nR = Hold.nR h ; bsR = Hold.bsR h ; odR = Hold.odR h ; cR = Hold.cR h
    ; α = Hold.α h ; κ = Hold.κ h
    ; leftC = curW ; rightC = Hold.rightC h
    ; nmL = trans (Hold.nmL h) (trans (sym nse) (sym (ns-keep weq cur)))
    ; nmR = Hold.nmR h }
  where
  weq : wS ≡ w
  weq = just-inj (trans (sym wkS) wk)
  j≡ : j ≡ entry w
  j≡ = trans (sym ej) (cong entry weq)
  atJ : reactL g (abs c) ≡
        AGo (rc (entry w) (ir c) (snoc (l2r c) t) (r2l c) (el c) (er c))
  atJ = subst (λ i → reactL g (abs c) ≡
                 AGo (rc i (ir c) (snoc (l2r c) t) (r2l c) (el c) (er c)))
          j≡ reacted
  moved : reactL g (abs c) ≡ AGo (abs (afterTok c p ρ′ pend′ t w))
  moved = subst (λ q → reactL g (abs c) ≡
                   AGo (rc (entry w) (ir c) q (r2l c) (el c) (er c)))
            (sym (snoc≡ (l2r c) t)) atJ
  curW = subst (λ z → Cursor (Hold.bsL h) (entry z) (atSlot z) ρ′
                        (addPend pend′ (il c) (slotL c) (envIL c)) p)
           weq cur

closeL : ∀ {g c p ρ′ pend′ k j w wS} (h : Hold g c) →
         reactL g (abs c) ≡
           AGo (rc j (ir c) (snoc (l2r c) (pay k)) (r2l c) (el c) (er c)) →
         entry wS ≡ j →
         walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
              (suc (il c)) (slotL c) ≡ just wS →
         walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
              (suc (il c)) (slotL c) ≡ just w →
         (cur : Cursor (Hold.bsL h) (entry wS) (atSlot wS) ρ′
                       (addPend pend′ (il c) (slotL c) (envIL c)) p) →
         Cursor.echoNs cur ≡ Cursor.echoNs (Hold.leftC h) →
         Step g (abs c) lside (abs (afterPut c p ρ′ pend′ k w)) ×
         Hold g (afterPut c p ρ′ pend′ k w)
closeL {k = k} h reacted ej wkS wk cur nse =
  closeTok (pay k) h reacted ej wkS wk cur nse

-- The left cursor, unfolded to the send its place denotes.
leftSend : ∀ {g c a p ρ′ pend′} (h : Hold g c) →
           Unfold (envPL c) [] (left c) ρ′ pend′ (f-put a p) →
           Send (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
                (il c) (slotL c) (envIL c) ρ′ pend′ a p
leftSend {c = c} h unf =
  openSend (leftBag h) (Cursor.pl lc) (Cursor.cv lc) (Cursor.lk lc)
           (Cursor.hs lc) (Cursor.at lc) (Cursor.ens lc) (Cursor.al lc)
           (Cursor.ix lc) (Cursor.ss lc) (Cursor.sn lc) unf
  where lc = Hold.leftC h

-- The same cursor, stopped at whatever action the unfold reaches.
leftStop : ∀ {g c ρ′ pend′ f} (h : Hold g c) →
           Unfold (envPL c) [] (left c) ρ′ pend′ f →
           Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
                (il c) (slotL c) (envIL c) ρ′ pend′ f
leftStop {c = c} h unf =
  descend (leftBag h) (Cursor.pl lc) (Cursor.cv lc) (Cursor.lk lc)
          (Cursor.hs lc) (Cursor.at lc) (Cursor.ens lc) (Cursor.al lc)
          (Cursor.ix lc) (Cursor.ss lc) (Cursor.sn lc) unf
  where lc = Hold.leftC h

------------------------------------------------------------------------
-- A source put is the block `openSend` read, run by `react-put`.
------------------------------------------------------------------------

put-fwd : ∀ {g c a p ρ′ pend′ atom k w} (h : Hold g c) →
          Unfold (envPL c) [] (left c) ρ′ pend′ (f-put a p) →
          asAtom a ≡ just atom →
          findA atom (alpha c) ≡ just k →
          length (l2r c) < cap c →
          walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
               (suc (il c)) (slotL c) ≡ just w →
          Step g (abs c) lside (abs (afterPut c p ρ′ pend′ k w)) ×
          Hold g (afterPut c p ρ′ pend′ k w)
put-fwd {g} {c} {a} {p} {ρ′} {pend′} {atom} {k} {w} h unf aq eqF le wk =
  use (leftSend h unf) aq
  where
  use : Send (Hold.bsL h) (Cursor.echoNs (Hold.leftC h)) (il c) (slotL c)
             (envIL c) ρ′ pend′ a p →
        asAtom a ≡ just atom →
        Step g (abs c) lside (abs (afterPut c p ρ′ pend′ k w)) ×
        Hold g (afterPut c p ρ′ pend′ k w)
  use (echoed _ _ _ _ refl _ _ _ _ _ _) ()
  use (sent atomS j wS aeq ej mem wkS cur nse) aq′ =
    closeL h reacted ej wkS wk cur nse
    where
    atom≡ : atomS ≡ atom
    atom≡ = just-inj (trans (sym aeq) aq′)
    memA : (il c , bPut atom j) ∈ Hold.bsL h
    memA = subst (λ z → (il c , bPut z j) ∈ Hold.bsL h) atom≡ mem
    findG : findA atom (Graph.alpha g) ≡ just k
    findG = subst (λ al → findA atom al ≡ just k) (Hold.α h) eqF
    reacted = react-put g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                atom k j findG (roomL h le) (seenL h memA)

------------------------------------------------------------------------
-- A source echo is the same step, with the value taken from a slot.
------------------------------------------------------------------------

echo-fwd : ∀ {g c x p ρ′ pend′ i k w} (h : Hold g c) →
           Unfold (envPL c) [] (left c) ρ′ pend′ (f-put (pEcho x) p) →
           findS x (namesL c) ≡ just i →
           slotVal (el c) i ≡ just k →
           length (l2r c) < cap c →
           walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                (suc (il c)) (slotL c) ≡ just w →
           Step g (abs c) lside (abs (afterPut c p ρ′ pend′ k w)) ×
           Hold g (afterPut c p ρ′ pend′ k w)
echo-fwd {g} {c} {x} {p} {ρ′} {pend′} {i} {k} {w} h unf eqN eqS le wk =
  use (leftSend h unf)
  where
  use : Send (Hold.bsL h) (Cursor.echoNs (Hold.leftC h)) (il c) (slotL c)
             (envIL c) ρ′ pend′ (pEcho x) p →
        Step g (abs c) lside (abs (afterPut c p ρ′ pend′ k w)) ×
        Hold g (afterPut c p ρ′ pend′ k w)
  use (sent _ _ _ () _ _ _ _ _)
  use (echoed .x sX j wS refl fd ej mem wkS cur nse) =
    closeL h reacted ej wkS wk cur nse
    where
    i≡ : i ≡ sX
    i≡ = just-inj (trans (sym eqN)
           (trans (find≡ x (namesL c) (Cursor.echoNs (Hold.leftC h)) (Hold.nmL h)) fd))
    slotG : slotVal (el c) sX ≡ just k
    slotG = subst (λ z → slotVal (el c) z ≡ just k) i≡ eqS
    reacted = react-echo g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                sX k j slotG (roomL h le) (seenL h mem)

------------------------------------------------------------------------
-- A source pick writes a boolean and continues at the walked block.
------------------------------------------------------------------------

pick0-use : ∀ {g c p ρ′ pend′ w} (h : Hold g c) →
            length (l2r c) < cap c →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                 (suc (il c)) (slotL c) ≡ just w →
            Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
                 (il c) (slotL c) (envIL c) ρ′ pend′ (f-pick0 p) →
            Step g (abs c) lside (abs (afterTok c p ρ′ pend′ (lab false) w)) ×
            Hold g (afterTok c p ρ′ pend′ (lab false) w)
pick0-use {g} {c} {p} {ρ′} {pend′} {w} h le wk
  (atAct suf ρi bg _
     (p-act (d-pick0 nD sD j .p ρw wD wkD ej dest dh ds de)
            r-pick0 i0 s0 ρden)
     (cp-act (c-pick0 mem cvD))
     (lk-pick0 eqi eqs _ lkD)
     (hs-pick0 hsD)
     (at-pick0 _ atD)
     (en-pick0 ensD)
     (al-pick0 eqρ destAl)
     ix ss sn lf-pick0) =
  closeTok (lab false) h reacted ej (Gone.wk go) wk (Gone.cur go) (Gone.nse go)
  where
  en = trans ix eqi
  es = trans ss eqs
  go = sendCont {bs = Hold.bsL h} {ns = Cursor.echoNs (Hold.leftC h)}
         {n = il c} {s = slotL c} {base = envIL c} {ρi = ρi}
         {pend = pend′} {suf = suf} {env = ρ′} {p = p}
         {nD = nD} {sD = sD} {sW = slotL c} {sW′ = sD}
         {ρden = ρden} {ρw = ρw} {w = wD} {dest = dest}
         bg en es es eqρ sn (cvd bg) wkD dh ds de cvD lkD hsD atD ensD destAl
  memN : (il c , bPick0 j) ∈ Hold.bsL h
  memN = subst (λ i → (i , bPick0 j) ∈ Hold.bsL h) (sym en) mem
  reacted = react-pick0 g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
              j (roomL h le) (seenL h memN)

pick0-fwd : ∀ {g c p ρ′ pend′ w} (h : Hold g c) →
            Unfold (envPL c) [] (left c) ρ′ pend′ (f-pick0 p) →
            length (l2r c) < cap c →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                 (suc (il c)) (slotL c) ≡ just w →
            Step g (abs c) lside (abs (afterTok c p ρ′ pend′ (lab false) w)) ×
            Hold g (afterTok c p ρ′ pend′ (lab false) w)
pick0-fwd h unf le wk = pick0-use h le wk (leftStop h unf)

pick1-use : ∀ {g c p ρ′ pend′ w} (h : Hold g c) →
            length (l2r c) < cap c →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                 (suc (il c)) (slotL c) ≡ just w →
            Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
                 (il c) (slotL c) (envIL c) ρ′ pend′ (f-pick1 p) →
            Step g (abs c) lside (abs (afterTok c p ρ′ pend′ (lab true) w)) ×
            Hold g (afterTok c p ρ′ pend′ (lab true) w)
pick1-use {g} {c} {p} {ρ′} {pend′} {w} h le wk
  (atAct suf ρi bg _
     (p-act (d-pick1 nD sD j .p ρw wD wkD ej dest dh ds de)
            r-pick1 i0 s0 ρden)
     (cp-act (c-pick1 mem cvD))
     (lk-pick1 eqi eqs _ lkD)
     (hs-pick1 hsD)
     (at-pick1 _ atD)
     (en-pick1 ensD)
     (al-pick1 eqρ destAl)
     ix ss sn lf-pick1) =
  closeTok (lab true) h reacted ej (Gone.wk go) wk (Gone.cur go) (Gone.nse go)
  where
  en = trans ix eqi
  es = trans ss eqs
  go = sendCont {bs = Hold.bsL h} {ns = Cursor.echoNs (Hold.leftC h)}
         {n = il c} {s = slotL c} {base = envIL c} {ρi = ρi}
         {pend = pend′} {suf = suf} {env = ρ′} {p = p}
         {nD = nD} {sD = sD} {sW = slotL c} {sW′ = sD}
         {ρden = ρden} {ρw = ρw} {w = wD} {dest = dest}
         bg en es es eqρ sn (cvd bg) wkD dh ds de cvD lkD hsD atD ensD destAl
  memN : (il c , bPick1 j) ∈ Hold.bsL h
  memN = subst (λ i → (i , bPick1 j) ∈ Hold.bsL h) (sym en) mem
  reacted = react-pick1 g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
              j (roomL h le) (seenL h memN)

pick1-fwd : ∀ {g c p ρ′ pend′ w} (h : Hold g c) →
            Unfold (envPL c) [] (left c) ρ′ pend′ (f-pick1 p) →
            length (l2r c) < cap c →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                 (suc (il c)) (slotL c) ≡ just w →
            Step g (abs c) lside (abs (afterTok c p ρ′ pend′ (lab true) w)) ×
            Hold g (afterTok c p ρ′ pend′ (lab true) w)
pick1-fwd h unf le wk = pick1-use h le wk (leftStop h unf)

------------------------------------------------------------------------
-- A source get pops one payload and stores it in the named slot.
------------------------------------------------------------------------

afterGet : SConf → SProc → EnvP → List String → List Tok → ℕ → W → SConf
afterGet c p ρ′ pend′ rest k w =
  record c { left = p ; il = entry w ; slotL = atSlot w
           ; r2l = rest ; el = setNth (slotL c) (suc k) (el c)
           ; envPL = ρ′
           ; envIL = addPend pend′ (il c) (slotL c) (envIL c) }

closeGet : ∀ {g c p ρ′ pend′ k rest j w wS n0 s0} (h : Hold g c) →
           reactL g (abs c) ≡
             AGo (rc j (ir c) (l2r c) rest (setNth (slotL c) (suc k) (el c)) (er c)) →
           entry wS ≡ j →
           walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p n0 s0 ≡ just wS →
           walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p n0 s0 ≡ just w →
           (cur : Cursor (Hold.bsL h) (entry wS) (atSlot wS) ρ′
                         (addPend pend′ (il c) (slotL c) (envIL c)) p) →
           Cursor.echoNs cur ≡ Cursor.echoNs (Hold.leftC h) →
           Step g (abs c) lside (abs (afterGet c p ρ′ pend′ rest k w)) ×
           Hold g (afterGet c p ρ′ pend′ rest k w)
closeGet {g} {c} {p} {ρ′} {pend′} {k} {rest} {j} {w} {wS} h reacted ej wkS wk cur nse =
  stepL moved , record
    { nL = Hold.nL h ; bsL = Hold.bsL h ; odL = Hold.odL h ; cL = Hold.cL h
    ; nR = Hold.nR h ; bsR = Hold.bsR h ; odR = Hold.odR h ; cR = Hold.cR h
    ; α = Hold.α h ; κ = Hold.κ h
    ; leftC = curW ; rightC = Hold.rightC h
    ; nmL = trans (Hold.nmL h) (trans (sym nse) (sym (ns-keep weq cur)))
    ; nmR = Hold.nmR h }
  where
  weq : wS ≡ w
  weq = just-inj (trans (sym wkS) wk)
  j≡ : j ≡ entry w
  j≡ = trans (sym ej) (cong entry weq)
  moved : reactL g (abs c) ≡ AGo (abs (afterGet c p ρ′ pend′ rest k w))
  moved = subst (λ i → reactL g (abs c) ≡
                   AGo (rc i (ir c) (l2r c) rest
                          (setNth (slotL c) (suc k) (el c)) (er c)))
            j≡ reacted
  curW = subst (λ z → Cursor (Hold.bsL h) (entry z) (atSlot z) ρ′
                        (addPend pend′ (il c) (slotL c) (envIL c)) p)
           weq cur

get-use : ∀ {g c t x p ρ′ pend′ k rest a w} (h : Hold g c) →
          r2l c ≡ pay k ∷ rest →
          nthA (alpha c) k ≡ just a →
          fits t a ≡ true →
          walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
               (suc (il c)) (suc (slotL c)) ≡ just w →
          Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
               (il c) (slotL c) (envIL c) ρ′ pend′ (f-get t x p) →
          Step g (abs c) lside (abs (afterGet c p ρ′ pend′ rest k w)) ×
          Hold g (afterGet c p ρ′ pend′ rest k w)
get-use {g} {c} {t} {x} {p} {ρ′} {pend′} {k} {rest} {a} {w} h qeq eqA eqF wk
  (atAct suf ρi bg _
     (p-act (d-get nD sD .t .x j .p ρw wD wkD ej dest dh ds de)
            r-get i0 s0 ρden)
     (cp-act (c-get mem cvD))
     (lk-get eqi eqs _ lkD)
     (hs-get hsD)
     (at-get _ atD)
     (en-get ensD)
     (al-get eqρ destAl)
     ix ss sn lf-get) =
  closeGet h reacted ej (Gone.wk go) wk (Gone.cur go) (Gone.nse go)
  where
  en = trans ix eqi
  es = trans ss eqs
  go = sendCont {bs = Hold.bsL h} {ns = Cursor.echoNs (Hold.leftC h)}
         {n = il c} {s = slotL c} {base = envIL c} {ρi = ρi}
         {pend = pend′} {suf = suf} {env = ρ′} {p = p}
         {nD = nD} {sD = sD} {sW = suc (slotL c)} {sW′ = suc sD}
         {ρden = ρden} {ρw = ρw} {w = wD} {dest = dest}
         bg en es (cong suc es) eqρ sn (cvd bg) wkD dh ds de
         cvD lkD hsD atD ensD destAl
  memI = subst (λ i → (i , bGet t sD j) ∈ Hold.bsL h) (sym en) mem
  memN : (il c , bGet t (slotL c) j) ∈ Hold.bsL h
  memN = subst (λ z → (il c , bGet t z j) ∈ Hold.bsL h) (sym es) memI
  nthG : nthA (Graph.alpha g) k ≡ just a
  nthG = subst (λ al → nthA al k ≡ just a) (Hold.α h) eqA
  got = react-get g (il c) (ir c) (l2r c) k rest (el c) (er c)
          t (slotL c) a j refl nthG eqF (seenL h memN)
  reacted = subst (λ q → reactL g (rc (il c) (ir c) (l2r c) q (el c) (er c)) ≡
                     AGo (rc j (ir c) (l2r c) rest
                            (setNth (slotL c) (suc k) (el c)) (er c)))
              (sym qeq) got

get-fwd : ∀ {g c t x p ρ′ pend′ k rest a w} (h : Hold g c) →
          Unfold (envPL c) [] (left c) ρ′ pend′ (f-get t x p) →
          r2l c ≡ pay k ∷ rest →
          nthA (alpha c) k ≡ just a →
          fits t a ≡ true →
          walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
               (suc (il c)) (suc (slotL c)) ≡ just w →
          Step g (abs c) lside (abs (afterGet c p ρ′ pend′ rest k w)) ×
          Hold g (afterGet c p ρ′ pend′ rest k w)
get-fwd h unf qeq eqA eqF wk = get-use h qeq eqA eqF wk (leftStop h unf)

------------------------------------------------------------------------
-- A source cover pops a label and continues in the selected branch.
------------------------------------------------------------------------

afterPop : SConf → SProc → EnvP → List String → List Tok → W → SConf
afterPop c proc ρ′ pend′ rest w =
  record c { left = proc ; il = entry w ; slotL = atSlot w
           ; r2l = rest
           ; envPL = ρ′
           ; envIL = addPend pend′ (il c) (slotL c) (envIL c) }

closePop : ∀ {g c proc ρ′ pend′ rest j w wS n0 s0} (h : Hold g c) →
           reactL g (abs c) ≡
             AGo (rc j (ir c) (l2r c) rest (el c) (er c)) →
           entry wS ≡ j →
           walk [] (addPend pend′ (il c) (slotL c) (envIL c)) proc n0 s0 ≡ just wS →
           walk [] (addPend pend′ (il c) (slotL c) (envIL c)) proc n0 s0 ≡ just w →
           (cur : Cursor (Hold.bsL h) (entry wS) (atSlot wS) ρ′
                         (addPend pend′ (il c) (slotL c) (envIL c)) proc) →
           Cursor.echoNs cur ≡ Cursor.echoNs (Hold.leftC h) →
           Step g (abs c) lside (abs (afterPop c proc ρ′ pend′ rest w)) ×
           Hold g (afterPop c proc ρ′ pend′ rest w)
closePop {g} {c} {proc} {ρ′} {pend′} {rest} {j} {w} {wS} h reacted ej wkS wk cur nse =
  stepL moved , record
    { nL = Hold.nL h ; bsL = Hold.bsL h ; odL = Hold.odL h ; cL = Hold.cL h
    ; nR = Hold.nR h ; bsR = Hold.bsR h ; odR = Hold.odR h ; cR = Hold.cR h
    ; α = Hold.α h ; κ = Hold.κ h
    ; leftC = curW ; rightC = Hold.rightC h
    ; nmL = trans (Hold.nmL h) (trans (sym nse) (sym (ns-keep weq cur)))
    ; nmR = Hold.nmR h }
  where
  weq : wS ≡ w
  weq = just-inj (trans (sym wkS) wk)
  moved : reactL g (abs c) ≡ AGo (abs (afterPop c proc ρ′ pend′ rest w))
  moved = subst (λ i → reactL g (abs c) ≡
                   AGo (rc i (ir c) (l2r c) rest (el c) (er c)))
            (trans (sym ej) (cong entry weq)) reacted
  curW = subst (λ z → Cursor (Hold.bsL h) (entry z) (atSlot z) ρ′
                        (addPend pend′ (il c) (slotL c) (envIL c)) proc)
           weq cur

cover0-use : ∀ {g c p q ρ′ pend′ rest w} (h : Hold g c) →
             r2l c ≡ lab false ∷ rest →
             walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                  (suc (il c)) (slotL c) ≡ just w →
             Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
                  (il c) (slotL c) (envIL c) ρ′ pend′ (f-cover p q) →
             Step g (abs c) lside (abs (afterPop c p ρ′ pend′ rest w)) ×
             Hold g (afterPop c p ρ′ pend′ rest w)
cover0-use {g} {c} {p} {q} {ρ′} {pend′} {rest} {w} h qeq wk
  (atAct suf ρi bg _
     (p-act (d-cover nD sD i j .p .q ρw w1 w2 wk1 ei wk2 ej
                     dp dq hp sp deP hq sq deQ)
            r-cover i0 s0 ρden)
     (cp-act (c-cover mem cvP cvQ))
     (lk-cover eqi eqs _ lkP lkQ)
     (hs-cover hsP hsQ)
     (at-cover _ atP atQ)
     (en-cover ensP ensQ)
     (al-cover eqρ alP alQ)
     ix ss sn lf-cover) =
  closePop h reacted ei (Gone.wk go) wk (Gone.cur go) (Gone.nse go)
  where
  en = trans ix eqi
  es = trans ss eqs
  go = sendCont {bs = Hold.bsL h} {ns = Cursor.echoNs (Hold.leftC h)}
         {n = il c} {s = slotL c} {base = envIL c} {ρi = ρi}
         {pend = pend′} {suf = suf} {env = ρ′} {p = p}
         {nD = nD} {sD = sD} {sW = slotL c} {sW′ = sD}
         {ρden = ρden} {ρw = ρw} {w = w1} {dest = dp}
         bg en es es eqρ sn (cvd bg) wk1 hp sp deP
         cvP lkP hsP atP ensP alP
  memN : (il c , bCover i j) ∈ Hold.bsL h
  memN = subst (λ z → (z , bCover i j) ∈ Hold.bsL h) (sym en) mem
  got = react-cover0 g (il c) (ir c) (l2r c) rest (el c) (er c) i j (seenL h memN)
  reacted = subst (λ queue →
              reactL g (rc (il c) (ir c) (l2r c) queue (el c) (er c)) ≡
                AGo (rc i (ir c) (l2r c) rest (el c) (er c)))
              (sym qeq) got

cover0-fwd : ∀ {g c p q ρ′ pend′ rest w} (h : Hold g c) →
             Unfold (envPL c) [] (left c) ρ′ pend′ (f-cover p q) →
             r2l c ≡ lab false ∷ rest →
             walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                  (suc (il c)) (slotL c) ≡ just w →
             Step g (abs c) lside (abs (afterPop c p ρ′ pend′ rest w)) ×
             Hold g (afterPop c p ρ′ pend′ rest w)
cover0-fwd h unf qeq wk = cover0-use h qeq wk (leftStop h unf)

cover1-use : ∀ {g c p q ρ′ pend′ rest w1 w2} (h : Hold g c) →
             r2l c ≡ lab true ∷ rest →
             walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                  (suc (il c)) (slotL c) ≡ just w1 →
             walk [] (addPend pend′ (il c) (slotL c) (envIL c)) q
                  (next w1) (slotN w1) ≡ just w2 →
             Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
                  (il c) (slotL c) (envIL c) ρ′ pend′ (f-cover p q) →
             Step g (abs c) lside (abs (afterPop c q ρ′ pend′ rest w2)) ×
             Hold g (afterPop c q ρ′ pend′ rest w2)
cover1-use {g} {c} {p} {q} {ρ′} {pend′} {rest} {w1} {w2} h qeq wk1 wk2
  (atAct suf ρi bg _
     (p-act (d-cover nD sD i j .p .q ρw w1D w2D wk1D ei wk2D ej
                     dp dq hp sp deP hq sq deQ)
            r-cover i0 s0 ρden)
     (cp-act (c-cover mem cvP cvQ))
     (lk-cover eqi eqs _ lkP lkQ)
     (hs-cover hsP hsQ)
     (at-cover _ atP atQ)
     (en-cover ensP ensQ)
     (al-cover eqρ alP alQ)
     ix ss sn lf-cover) =
  closePop h reacted ej wk2Run wk2 cur (echo-env (run bg) cur0)
  where
  en = trans ix eqi
  es = trans ss eqs
  go = sendCont {bs = Hold.bsL h} {ns = Cursor.echoNs (Hold.leftC h)}
         {n = il c} {s = slotL c} {base = envIL c} {ρi = ρi}
         {pend = pend′} {suf = suf} {env = ρ′} {p = p}
         {nD = nD} {sD = sD} {sW = slotL c} {sW′ = sD}
         {ρden = ρden} {ρw = ρw} {w = w1D} {dest = dp}
         bg en es es eqρ sn (cvd bg) wk1D hp sp deP
         cvP lkP hsP atP ensP alP
  same : w1D ≡ w1
  same = just-inj (trans (sym (Gone.wk go)) wk1)
  extW = ext-leaf suf pend′ (il c) (slotL c) nD sD ρden (envIL c) ρw ρi suf
           en es refl eqρ (run bg) sn (cvd bg)
  wkI = walk-ext [] ρw ρi q (next w1D) (slotN w1D) w2D extW wk2D
  wkAt = subst (λ z → walk [] ρi q (next z) (slotN z) ≡ just w2D) same wkI
  wk2Run = subst (λ e → walk [] e q (next w1) (slotN w1) ≡ just w2D) (run bg) wkAt
  snD = subst (λ e → Ext e ρi) (sym deQ) extW
  cur0 = arrive {ns = Cursor.echoNs (Hold.leftC h)} {tab = tab bg} dq w2D
           (ct bg) (ls bg) (td bg) (sy bg) (kn bg) (nd bg)
           hq sq cvQ lkQ hsQ atQ ensQ alQ snD
  cur = subst (λ e → Cursor (Hold.bsL h) (entry w2D) (atSlot w2D) ρ′ e q)
          (run bg) cur0
  memN : (il c , bCover i j) ∈ Hold.bsL h
  memN = subst (λ z → (z , bCover i j) ∈ Hold.bsL h) (sym en) mem
  got = react-cover1 g (il c) (ir c) (l2r c) rest (el c) (er c) i j (seenL h memN)
  reacted = subst (λ queue →
              reactL g (rc (il c) (ir c) (l2r c) queue (el c) (er c)) ≡
                AGo (rc j (ir c) (l2r c) rest (el c) (er c)))
              (sym qeq) got

cover1-fwd : ∀ {g c p q ρ′ pend′ rest w1 w2} (h : Hold g c) →
             Unfold (envPL c) [] (left c) ρ′ pend′ (f-cover p q) →
             r2l c ≡ lab true ∷ rest →
             walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                  (suc (il c)) (slotL c) ≡ just w1 →
             walk [] (addPend pend′ (il c) (slotL c) (envIL c)) q
                  (next w1) (slotN w1) ≡ just w2 →
             Step g (abs c) lside (abs (afterPop c q ρ′ pend′ rest w2)) ×
             Hold g (afterPop c q ρ′ pend′ rest w2)
cover1-fwd h unf qeq wk1 wk2 = cover1-use h qeq wk1 wk2 (leftStop h unf)

------------------------------------------------------------------------
-- A source integer receive stores the payload and follows the bit.
------------------------------------------------------------------------

iget0-use : ∀ {g c x p q ρ′ pend′ k rest w} (h : Hold g c) →
            r2l c ≡ pay k ∷ rest →
            nthA (alpha c) k ≡ just (aBit false) →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                 (suc (il c)) (suc (slotL c)) ≡ just w →
            Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
                 (il c) (slotL c) (envIL c) ρ′ pend′ (f-iget x p q) →
            Step g (abs c) lside (abs (afterGet c p ρ′ pend′ rest k w)) ×
            Hold g (afterGet c p ρ′ pend′ rest k w)
iget0-use {g} {c} {x} {p} {q} {ρ′} {pend′} {k} {rest} {w} h qeq eqA wk
  (atAct suf ρi bg _
     (p-act (d-iget nD sD .x i j .p .q ρw w1D w2D wk1D ei wk2D ej
                    dp dq hp sp deP hq sq deQ)
            r-iget i0 s0 ρden)
     (cp-act (c-iget mem cvP cvQ))
     (lk-iget eqi eqs _ lkP lkQ)
     (hs-iget hsP hsQ)
     (at-iget _ atP atQ)
     (en-iget ensP ensQ)
     (al-iget eqρ alP alQ)
     ix ss sn lf-iget) =
  closeGet h reacted ei (Gone.wk go) wk (Gone.cur go) (Gone.nse go)
  where
  en = trans ix eqi
  es = trans ss eqs
  go = sendCont {bs = Hold.bsL h} {ns = Cursor.echoNs (Hold.leftC h)}
         {n = il c} {s = slotL c} {base = envIL c} {ρi = ρi}
         {pend = pend′} {suf = suf} {env = ρ′} {p = p}
         {nD = nD} {sD = sD} {sW = suc (slotL c)} {sW′ = suc sD}
         {ρden = ρden} {ρw = ρw} {w = w1D} {dest = dp}
         bg en es (cong suc es) eqρ sn (cvd bg) wk1D hp sp deP
         cvP lkP hsP atP ensP alP
  memI = subst (λ z → (z , bIget sD i j) ∈ Hold.bsL h) (sym en) mem
  memN : (il c , bIget (slotL c) i j) ∈ Hold.bsL h
  memN = subst (λ z → (il c , bIget z i j) ∈ Hold.bsL h) (sym es) memI
  nthG : nthA (Graph.alpha g) k ≡ just (aBit false)
  nthG = subst (λ al → nthA al k ≡ just (aBit false)) (Hold.α h) eqA
  got = react-iget0 g (il c) (ir c) (l2r c) k rest (el c) (er c)
          (slotL c) i j nthG (seenL h memN)
  reacted = subst (λ queue →
              reactL g (rc (il c) (ir c) (l2r c) queue (el c) (er c)) ≡
                AGo (rc i (ir c) (l2r c) rest
                       (setNth (slotL c) (suc k) (el c)) (er c)))
              (sym qeq) got

iget0-fwd : ∀ {g c x p q ρ′ pend′ k rest w} (h : Hold g c) →
            Unfold (envPL c) [] (left c) ρ′ pend′ (f-iget x p q) →
            r2l c ≡ pay k ∷ rest →
            nthA (alpha c) k ≡ just (aBit false) →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                 (suc (il c)) (suc (slotL c)) ≡ just w →
            Step g (abs c) lside (abs (afterGet c p ρ′ pend′ rest k w)) ×
            Hold g (afterGet c p ρ′ pend′ rest k w)
iget0-fwd h unf qeq eqA wk = iget0-use h qeq eqA wk (leftStop h unf)

iget1-use : ∀ {g c x p q ρ′ pend′ k rest w1 w2} (h : Hold g c) →
            r2l c ≡ pay k ∷ rest →
            nthA (alpha c) k ≡ just (aBit true) →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                 (suc (il c)) (suc (slotL c)) ≡ just w1 →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) q
                 (next w1) (slotN w1) ≡ just w2 →
            Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
                 (il c) (slotL c) (envIL c) ρ′ pend′ (f-iget x p q) →
            Step g (abs c) lside (abs (afterGet c q ρ′ pend′ rest k w2)) ×
            Hold g (afterGet c q ρ′ pend′ rest k w2)
iget1-use {g} {c} {x} {p} {q} {ρ′} {pend′} {k} {rest} {w1} {w2} h qeq eqA wk1 wk2
  (atAct suf ρi bg _
     (p-act (d-iget nD sD .x i j .p .q ρw w1D w2D wk1D ei wk2D ej
                    dp dq hp sp deP hq sq deQ)
            r-iget i0 s0 ρden)
     (cp-act (c-iget mem cvP cvQ))
     (lk-iget eqi eqs _ lkP lkQ)
     (hs-iget hsP hsQ)
     (at-iget _ atP atQ)
     (en-iget ensP ensQ)
     (al-iget eqρ alP alQ)
     ix ss sn lf-iget) =
  closeGet h reacted ej wk2Run wk2 cur (echo-env (run bg) cur0)
  where
  en = trans ix eqi
  es = trans ss eqs
  go = sendCont {bs = Hold.bsL h} {ns = Cursor.echoNs (Hold.leftC h)}
         {n = il c} {s = slotL c} {base = envIL c} {ρi = ρi}
         {pend = pend′} {suf = suf} {env = ρ′} {p = p}
         {nD = nD} {sD = sD} {sW = suc (slotL c)} {sW′ = suc sD}
         {ρden = ρden} {ρw = ρw} {w = w1D} {dest = dp}
         bg en es (cong suc es) eqρ sn (cvd bg) wk1D hp sp deP
         cvP lkP hsP atP ensP alP
  same : w1D ≡ w1
  same = just-inj (trans (sym (Gone.wk go)) wk1)
  extW = ext-leaf suf pend′ (il c) (slotL c) nD sD ρden (envIL c) ρw ρi suf
           en es refl eqρ (run bg) sn (cvd bg)
  wkI = walk-ext [] ρw ρi q (next w1D) (slotN w1D) w2D extW wk2D
  wkAt = subst (λ z → walk [] ρi q (next z) (slotN z) ≡ just w2D) same wkI
  wk2Run = subst (λ e → walk [] e q (next w1) (slotN w1) ≡ just w2D) (run bg) wkAt
  snD = subst (λ e → Ext e ρi) (sym deQ) extW
  cur0 = arrive {ns = Cursor.echoNs (Hold.leftC h)} {tab = tab bg} dq w2D
           (ct bg) (ls bg) (td bg) (sy bg) (kn bg) (nd bg)
           hq sq cvQ lkQ hsQ atQ ensQ alQ snD
  cur = subst (λ e → Cursor (Hold.bsL h) (entry w2D) (atSlot w2D) ρ′ e q)
          (run bg) cur0
  memI = subst (λ z → (z , bIget sD i j) ∈ Hold.bsL h) (sym en) mem
  memN : (il c , bIget (slotL c) i j) ∈ Hold.bsL h
  memN = subst (λ z → (il c , bIget z i j) ∈ Hold.bsL h) (sym es) memI
  nthG : nthA (Graph.alpha g) k ≡ just (aBit true)
  nthG = subst (λ al → nthA al k ≡ just (aBit true)) (Hold.α h) eqA
  got = react-iget1 g (il c) (ir c) (l2r c) k rest (el c) (er c)
          (slotL c) i j nthG (seenL h memN)
  reacted = subst (λ queue →
              reactL g (rc (il c) (ir c) (l2r c) queue (el c) (er c)) ≡
                AGo (rc j (ir c) (l2r c) rest
                       (setNth (slotL c) (suc k) (el c)) (er c)))
              (sym qeq) got

iget1-fwd : ∀ {g c x p q ρ′ pend′ k rest w1 w2} (h : Hold g c) →
            Unfold (envPL c) [] (left c) ρ′ pend′ (f-iget x p q) →
            r2l c ≡ pay k ∷ rest →
            nthA (alpha c) k ≡ just (aBit true) →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) p
                 (suc (il c)) (suc (slotL c)) ≡ just w1 →
            walk [] (addPend pend′ (il c) (slotL c) (envIL c)) q
                 (next w1) (slotN w1) ≡ just w2 →
            Step g (abs c) lside (abs (afterGet c q ρ′ pend′ rest k w2)) ×
            Hold g (afterGet c q ρ′ pend′ rest k w2)
iget1-fwd h unf qeq eqA wk1 wk2 = iget1-use h qeq eqA wk1 wk2 (leftStop h unf)

------------------------------------------------------------------------
-- A source constructor receive stores the payload and takes that arm.
------------------------------------------------------------------------

nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

pairˡ : ∀ {A B : Set} {a c : A} {b d : B} → (a , b) ≡ (c , d) → a ≡ c
pairˡ refl = refl

pairʳ : ∀ {A B : Set} {a c : A} {b d : B} → (a , b) ≡ (c , d) → b ≡ d
pairʳ refl = refl

consˡ : ∀ {A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
consˡ refl = refl

consʳ : ∀ {A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
consʳ refl = refl

armGo-take : ∀ {ρ name y p as n s w} →
             walk [] ρ p n s ≡ just w →
             (name == y) ≡ true →
             armGo ρ name (aok y p ∷ as) n s ≡ just (w , p)
armGo-take eqw eq rewrite eqw | eq = refl

armGo-skip : ∀ {ρ name y p as n s w} →
             walk [] ρ p n s ≡ just w →
             (name == y) ≡ false →
             armGo ρ name (aok y p ∷ as) n s ≡ armGo ρ name as (next w) (slotN w)
armGo-skip eqw eq rewrite eqw | eq = refl

armTo-take : ∀ {name y j rest} →
             (name == y) ≡ true →
             armTo name ((y , j) ∷ rest) ≡ just j
armTo-take eq rewrite eq = refl

armTo-skip : ∀ {name y j rest} →
             (name == y) ≡ false →
             armTo name ((y , j) ∷ rest) ≡ armTo name rest
armTo-skip eq rewrite eq = refl

arms-nowalk : ∀ {ρ y p as n s} →
              walk [] ρ p n s ≡ nothing →
              walkArms [] ρ (aok y p ∷ as) n s ≡ nothing
arms-nowalk eq rewrite eq = refl

arms-notail : ∀ {ρ y p as n s w} →
              walk [] ρ p n s ≡ just w →
              walkArms [] ρ as (next w) (slotN w) ≡ nothing →
              walkArms [] ρ (aok y p ∷ as) n s ≡ nothing
arms-notail eqw eqa rewrite eqw | eqa = refl

arms-head : ∀ {ρ y p as n s w ws n2 s2} →
            walk [] ρ p n s ≡ just w →
            walkArms [] ρ as (next w) (slotN w) ≡ just (ws , n2 , s2) →
            walkArms [] ρ (aok y p ∷ as) n s ≡ just ((y , w) ∷ ws , n2 , s2)
arms-head eqw eqa rewrite eqw | eqa = refl

-- A walk that succeeds on every arm succeeds the same way on a larger
-- environment, so the arm `armGo` picks is the same arm.
armGo-agree : ∀ {ρ0 ρ name} (as : List Arm) {ws n s n2 s2 w p} →
              Ext ρ0 ρ →
              walkArms [] ρ0 as n s ≡ just (ws , n2 , s2) →
              armGo ρ name as n s ≡ just (w , p) →
              armGo ρ0 name as n s ≡ just (w , p)
armGo-agree [] _ _ hit = ⊥-elim (nothing≢just hit)
armGo-agree (abad ∷ _) _ wk _ = ⊥-elim (nothing≢just wk)
armGo-agree {ρ0 = ρ0} {ρ = ρ} {name = name} (aok y q ∷ as)
            {n = n} {s = s} {w = w} {p = p} ext wk hit =
  onW (walk [] ρ0 q n s) refl
  where
  onN : (w0 : W) → walk [] ρ0 q n s ≡ just w0 →
        {wsT : List (String × W)} {n2T s2T : ℕ} →
        walkArms [] ρ0 as (next w0) (slotN w0) ≡ just (wsT , n2T , s2T) →
        (b : Bool) → (name == y) ≡ b →
        armGo ρ0 name (aok y q ∷ as) n s ≡ just (w , p)
  onN w0 eqw eqa true eqb =
    let wkρ = walk-ext [] ρ0 ρ q n s w0 ext eqw
        here0 = armGo-take {ρ = ρ0} {name = name} {y = y} {p = q} {as = as}
                  {n = n} {s = s} {w = w0} eqw eqb
        here1 = armGo-take {ρ = ρ} {name = name} {y = y} {p = q} {as = as}
                  {n = n} {s = s} {w = w0} wkρ eqb
    in trans here0 (trans (sym here1) hit)
  onN w0 eqw eqa false eqb =
    let wkρ = walk-ext [] ρ0 ρ q n s w0 ext eqw
        skip0 = armGo-skip {ρ = ρ0} {name = name} {y = y} {p = q} {as = as}
                  {n = n} {s = s} {w = w0} eqw eqb
        skip1 = armGo-skip {ρ = ρ} {name = name} {y = y} {p = q} {as = as}
                  {n = n} {s = s} {w = w0} wkρ eqb
    in trans skip0
         (armGo-agree {ρ0 = ρ0} {ρ = ρ} {name = name} as
            {n = next w0} {s = slotN w0} {w = w} {p = p}
            ext eqa (trans (sym skip1) hit))

  onA : (w0 : W) → walk [] ρ0 q n s ≡ just w0 →
        (m : Maybe (List (String × W) × ℕ × ℕ)) →
        walkArms [] ρ0 as (next w0) (slotN w0) ≡ m →
        armGo ρ0 name (aok y q ∷ as) n s ≡ just (w , p)
  onA w0 eqw nothing eqa =
    ⊥-elim (nothing≢just
      (trans (sym (arms-notail {ρ = ρ0} {y = y} {p = q} {as = as}
                    {n = n} {s = s} {w = w0} eqw eqa)) wk))
  onA w0 eqw (just (wsT , n2T , s2T)) eqa =
    onN w0 eqw eqa (name == y) refl

  onW : (m : Maybe W) → walk [] ρ0 q n s ≡ m →
        armGo ρ0 name (aok y q ∷ as) n s ≡ just (w , p)
  onW nothing eqw =
    ⊥-elim (nothing≢just
      (trans (sym (arms-nowalk {ρ = ρ0} {y = y} {p = q} {as = as}
                    {n = n} {s = s} eqw)) wk))
  onW (just w0) eqw = onA w0 eqw (walkArms [] ρ0 as (next w0) (slotN w0)) refl

ix-proc : ∀ {p q} (eq : p ≡ q) (pl : Place p) →
          headIx (subst Place eq pl) ≡ headIx pl
ix-proc refl _ = refl

sl-proc : ∀ {p q} (eq : p ≡ q) (pl : Place p) →
          slotOf (subst Place eq pl) ≡ slotOf pl
sl-proc refl _ = refl

ev-proc : ∀ {p q} (eq : p ≡ q) (pl : Place p) →
          envOf (subst Place eq pl) ≡ envOf pl
ev-proc refl _ = refl

lk-proc : ∀ {p q} (eq : p ≡ q) (pl : Place p) →
          Link pl → Link (subst Place eq pl)
lk-proc refl _ lk = lk

hs-proc : ∀ {p q tab} (eq : p ≡ q) (pl : Place p) →
          Hosts tab pl → Hosts tab (subst Place eq pl)
hs-proc refl _ hs = hs

at-proc : ∀ {p q} (eq : p ≡ q) (pl : Place p) →
          At [] pl → At [] (subst Place eq pl)
at-proc refl _ at = at

ens-proc : ∀ {p q ns} (eq : p ≡ q) (pl : Place p) →
           EchoNs ns pl → EchoNs ns (subst Place eq pl)
ens-proc refl _ e = e

al-proc : ∀ {p q} (eq : p ≡ q) (pl : Place p) →
          Align [] pl → Align [] (subst Place eq pl)
al-proc refl _ al = al

cv-proc : ∀ {p q bs} (eq : p ≡ q) (pl : Place p) →
          CovP pl bs → CovP (subst Place eq pl) bs
cv-proc refl _ cv = cv

-- The arm whose name is the received constructor.
record Pick (bs : List (ℕ × Block)) (ns : List String) (tab : Table)
            (ρ : EnvI) (name : String) (w : W) (p : SProc)
            (ws : List (String × W)) : Set where
  constructor picked
  field
    pl : Place p
    hd : headIx pl ≡ entry w
    sl : slotOf pl ≡ atSlot w
    ev : envOf pl ≡ ρ
    cv : CovP pl bs
    lk : Link pl
    hs : Hosts tab pl
    at : At [] pl
    ens : EchoNs ns pl
    al : Align [] pl
    n0 : ℕ
    s0 : ℕ
    wk : walk [] ρ p n0 s0 ≡ just w
    aj : armTo name (ents ws) ≡ just (entry w)

armPick : ∀ {bs ns tab ρ name as ws n s n2 s2 w p} →
          (ps : ArmPs ρ as ws) →
          LinkA ps → HostsA tab ps → AtA ps → EchoNsA ns ps →
          AlignA ps → CovA ps bs →
          walkArms [] ρ as n s ≡ just (ws , n2 , s2) →
          armGo ρ name as n s ≡ just (w , p) →
          Pick bs ns tab ρ name w p ws
armPick ap0 la0 ha0 ata0 ea0 aa0 ca0 _ hit = ⊥-elim (nothing≢just hit)
armPick {bs = bs} {ns = ns} {tab = tab} {ρ = ρ} {name = name}
        {n = n} {s = s} {w = w} {p = p}
        (ap1 {y = y} {p = proc} {as = asT} {w = wA} {ws = wsT}
             pl hd0 sl0 ev0 rest)
        (la1 lkP lkR) (ha1 hsP hsR) (ata1 atP atR) (ea1 enP enR)
        (aa1 alP alR) (ca1 cvP cvR) wk hit =
  onW (walk [] ρ proc n s) refl
  where
  onN : (wGot : W) → walk [] ρ proc n s ≡ just wGot →
        (wsGot : List (String × W)) (n2G s2G : ℕ) →
        walkArms [] ρ asT (next wGot) (slotN wGot) ≡ just (wsGot , n2G , s2G) →
        (b : Bool) → (name == y) ≡ b →
        Pick bs ns tab ρ name w p ((y , wA) ∷ wsT)
  onN wGot eqw wsGot n2G s2G eqa true eqb =
    let head = arms-head {ρ = ρ} {y = y} {p = proc} {as = asT} {n = n} {s = s}
                 {w = wGot} {ws = wsGot} {n2 = n2G} {s2 = s2G} eqw eqa
        took = armGo-take {ρ = ρ} {name = name} {y = y} {p = proc} {as = asT}
                 {n = n} {s = s} {w = wGot} eqw eqb
        packed = just-inj (trans (sym head) wk)
        wGot≡ = pairʳ (consˡ (pairˡ packed))
        wp = just-inj (trans (sym took) hit)
        w≡ = pairˡ wp
        p≡ = pairʳ wp
        plP = subst Place p≡ pl
        same = trans (sym wGot≡) w≡
        hdP = trans (ix-proc p≡ pl) (trans hd0 (cong entry same))
        slP = trans (sl-proc p≡ pl) (trans sl0 (cong atSlot same))
        evP = trans (ev-proc p≡ pl) ev0
        wk1 = subst (λ z → walk [] ρ proc n s ≡ just z) w≡ eqw
        wkP = subst (λ q → walk [] ρ q n s ≡ just w) p≡ wk1
        ajP = trans (armTo-take eqb) (cong just (cong entry same))
    in picked plP hdP slP evP (cv-proc p≡ pl cvP) (lk-proc p≡ pl lkP)
              (hs-proc p≡ pl hsP) (at-proc p≡ pl atP) (ens-proc p≡ pl enP)
              (al-proc p≡ pl alP) n s wkP ajP
  onN wGot eqw wsGot n2G s2G eqa false eqb =
    let head = arms-head {ρ = ρ} {y = y} {p = proc} {as = asT} {n = n} {s = s}
                 {w = wGot} {ws = wsGot} {n2 = n2G} {s2 = s2G} eqw eqa
        skip = armGo-skip {ρ = ρ} {name = name} {y = y} {p = proc} {as = asT}
                 {n = n} {s = s} {w = wGot} eqw eqb
        packed = just-inj (trans (sym head) wk)
        ws≡ = consʳ (pairˡ packed)
        eqaT = subst (λ zs →
                 walkArms [] ρ asT (next wGot) (slotN wGot) ≡
                   just (zs , n2G , s2G))
                 ws≡ eqa
        hitT = trans (sym skip) hit
        rec = armPick rest lkR hsR atR enR alR cvR eqaT hitT
    in picked (Pick.pl rec) (Pick.hd rec) (Pick.sl rec) (Pick.ev rec)
              (Pick.cv rec) (Pick.lk rec) (Pick.hs rec) (Pick.at rec)
              (Pick.ens rec) (Pick.al rec) (Pick.n0 rec) (Pick.s0 rec)
              (Pick.wk rec) (trans (armTo-skip eqb) (Pick.aj rec))

  onA : (wGot : W) → walk [] ρ proc n s ≡ just wGot →
        (m : Maybe (List (String × W) × ℕ × ℕ)) →
        walkArms [] ρ asT (next wGot) (slotN wGot) ≡ m →
        Pick bs ns tab ρ name w p ((y , wA) ∷ wsT)
  onA wGot eqw nothing eqa =
    ⊥-elim (nothing≢just
      (trans (sym (arms-notail {ρ = ρ} {y = y} {p = proc} {as = asT}
                    {n = n} {s = s} {w = wGot} eqw eqa)) wk))
  onA wGot eqw (just (wsGot , n2G , s2G)) eqa =
    onN wGot eqw wsGot n2G s2G eqa (name == y) refl

  onW : (m : Maybe W) → walk [] ρ proc n s ≡ m →
        Pick bs ns tab ρ name w p ((y , wA) ∷ wsT)
  onW nothing eqw =
    ⊥-elim (nothing≢just
      (trans (sym (arms-nowalk {ρ = ρ} {y = y} {p = proc} {as = asT}
                    {n = n} {s = s} eqw)) wk))
  onW (just wGot) eqw =
    onA wGot eqw (walkArms [] ρ asT (next wGot) (slotN wGot)) refl

mget-use : ∀ {g c t x as ρ′ pend′ k rest a name w p} (h : Hold g c) →
           r2l c ≡ pay k ∷ rest →
           nthA (alpha c) k ≡ just a →
           fits t a ≡ true →
           conOf a ≡ just name →
           armGo (addPend pend′ (il c) (slotL c) (envIL c)) name as
                 (suc (il c)) (suc (slotL c)) ≡ just (w , p) →
           Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
                (il c) (slotL c) (envIL c) ρ′ pend′ (f-mget t x as) →
           Step g (abs c) lside (abs (afterGet c p ρ′ pend′ rest k w)) ×
           Hold g (afterGet c p ρ′ pend′ rest k w)
mget-use {g} {c} {t} {x} {as} {ρ′} {pend′} {k} {rest} {a} {name} {w} {p}
         h qeq eqA eqF eqC ago
  (atAct suf ρi bg _
     (p-act (d-mget nD sD .t .x named .as ρw ws n2 s2 wkD enW dests)
            r-mget i0 s0 ρden)
     (cp-act (c-mget mem cvA))
     (lk-mget eqi eqs _ lkA)
     (hs-mget hsA)
     (at-mget _ atA)
     (en-mget enA)
     (al-mget eqρ alA)
     ix ss sn lf-mget) =
  closeGet h reacted refl wkRun wkRun cur (echo-env (run bg) cur0)
  where
  en = trans ix eqi
  es = trans ss eqs
  extW = ext-leaf suf pend′ (il c) (slotL c) nD sD ρden (envIL c) ρw ρi suf
           en es refl eqρ (run bg) sn (cvd bg)
  wk1 = subst (λ z → walkArms [] ρw as (suc z) (suc sD) ≡ just (ws , n2 , s2))
          (sym en) wkD
  wkC = subst (λ z → walkArms [] ρw as (suc (il c)) (suc z) ≡ just (ws , n2 , s2))
          (sym es) wk1
  agoI = subst (λ e → armGo e name as (suc (il c)) (suc (slotL c)) ≡ just (w , p))
           (sym (run bg)) ago
  hitD = armGo-agree as extW wkC agoI
  pk = armPick dests lkA hsA atA enA alA cvA wkC hitD
  wkI = walk-ext [] ρw ρi p (Pick.n0 pk) (Pick.s0 pk) w extW (Pick.wk pk)
  wkRun = subst (λ e → walk [] e p (Pick.n0 pk) (Pick.s0 pk) ≡ just w)
            (run bg) wkI
  snD = subst (λ e → Ext e ρi) (sym (Pick.ev pk)) extW
  cur0 = arrive {ns = Cursor.echoNs (Hold.leftC h)} {tab = tab bg}
           (Pick.pl pk) w (ct bg) (ls bg) (td bg) (sy bg) (kn bg) (nd bg)
           (Pick.hd pk) (Pick.sl pk) (Pick.cv pk) (Pick.lk pk) (Pick.hs pk)
           (Pick.at pk) (Pick.ens pk) (Pick.al pk) snD
  cur = subst (λ e → Cursor (Hold.bsL h) (entry w) (atSlot w) ρ′ e p)
          (run bg) cur0
  memI = subst (λ z → (z , bMget t sD named) ∈ Hold.bsL h) (sym en) mem
  memN : (il c , bMget t (slotL c) named) ∈ Hold.bsL h
  memN = subst (λ z → (il c , bMget t z named) ∈ Hold.bsL h) (sym es) memI
  nthG : nthA (Graph.alpha g) k ≡ just a
  nthG = subst (λ al → nthA al k ≡ just a) (Hold.α h) eqA
  toN = subst (λ xs → armTo name xs ≡ just (entry w)) enW (Pick.aj pk)
  got = react-mget g (il c) (ir c) (l2r c) k rest (el c) (er c)
          t (slotL c) named a name (entry w) nthG eqF eqC toN (seenL h memN)
  reacted = subst (λ queue →
              reactL g (rc (il c) (ir c) (l2r c) queue (el c) (er c)) ≡
                AGo (rc (entry w) (ir c) (l2r c) rest
                       (setNth (slotL c) (suc k) (el c)) (er c)))
              (sym qeq) got

mget-fwd : ∀ {g c t x as ρ′ pend′ k rest a name w p} (h : Hold g c) →
           Unfold (envPL c) [] (left c) ρ′ pend′ (f-mget t x as) →
           r2l c ≡ pay k ∷ rest →
           nthA (alpha c) k ≡ just a →
           fits t a ≡ true →
           conOf a ≡ just name →
           armGo (addPend pend′ (il c) (slotL c) (envIL c)) name as
                 (suc (il c)) (suc (slotL c)) ≡ just (w , p) →
           Step g (abs c) lside (abs (afterGet c p ρ′ pend′ rest k w)) ×
           Hold g (afterGet c p ρ′ pend′ rest k w)
mget-fwd h unf qeq eqA eqF eqC ago = mget-use h qeq eqA eqF eqC ago (leftStop h unf)

------------------------------------------------------------------------
-- A halted focus is the halted block its place denotes.
------------------------------------------------------------------------

haltBlock : ∀ {bs ns n s base ρ′ pend′ f} →
            Stop bs ns n s base ρ′ pend′ f → HaltF f →
            Σ Block (λ b → (n , b) ∈ bs × isHalt b ≡ true)
haltBlock (atAct _ _ _ _
            (p-act (d-done nD) r-done i0 _ _)
            (cp-act (c-done mem))
            (lk-done eqi)
            _ _ _ _
            ix _ _ lf-done) h-done =
  bDone , subst (λ z → (z , bDone) ∈ _) (sym (trans ix eqi)) mem , isHalt-done
haltBlock (atAct _ _ _ _
            (p-act (d-stop nD) r-stop i0 _ _)
            (cp-act (c-stop mem))
            (lk-stop eqi)
            _ _ _ _
            ix _ _ lf-stop) h-stop =
  bStop , subst (λ z → (z , bStop) ∈ _) (sym (trans ix eqi)) mem , isHalt-stop

rightBag : ∀ {g} {c : SConf} (h : Hold g c) →
           Bag (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
               (ir c) (slotR c) (envIR c) (envIR c) [] [] (envPR c)
rightBag {c = c} h =
  bag {bs = Hold.bsR h} {ns = Cursor.echoNs rcur} {n = ir c} {s = slotR c}
      {base = envIR c} {ρi = envIR c} {pend = []} {suf = []} {env = envPR c}
      (Cursor.tab rcur) (Cursor.ct rcur) (Cursor.ls rcur)
      (Cursor.td rcur) (Cursor.sy rcur) (Cursor.kn rcur) (Cursor.nd rcur)
      refl
      (cov-id {xs = []} {base = envIR c} {n = ir c} {s = slotR c})
      (cov-id {xs = []} {base = envIR c} {n = ir c} {s = slotR c})
  where rcur = Hold.rightC h

seenR : ∀ {g c b} (h : Hold g c) → (ir c , b) ∈ Hold.bsR h →
        lookB (Graph.codeR g) (ir c) ≡ just b
seenR {c = c} {b = b} h mem =
  subst (λ code → lookB code (ir c) ≡ just b) (sym (Hold.cR h))
    (root-at (Hold.odR h) mem)

rightStop : ∀ {g c ρ′ pend′ f} (h : Hold g c) →
            Unfold (envPR c) [] (right c) ρ′ pend′ f →
            Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
                 (ir c) (slotR c) (envIR c) ρ′ pend′ f
rightStop {c = c} h unf =
  descend (rightBag h) (Cursor.pl rcur) (Cursor.cv rcur) (Cursor.lk rcur)
          (Cursor.hs rcur) (Cursor.at rcur) (Cursor.ens rcur) (Cursor.al rcur)
          (Cursor.ix rcur) (Cursor.ss rcur) (Cursor.sn rcur) unf
  where rcur = Hold.rightC h

-- Both source sides halted, both queues empty: the graph stutters.
fin-fwd : ∀ {g c ρL pendL ρR pendR fL fR} (h : Hold g c) →
          Unfold (envPL c) [] (left c) ρL pendL fL → HaltF fL →
          Unfold (envPR c) [] (right c) ρR pendR fR → HaltF fR →
          l2r c ≡ [] →
          r2l c ≡ [] →
          Step g (abs c) fin (abs c) × Hold g c
fin-fwd {g} {c} h unL hfL unR hfR eqL eqR =
  finish eqL eqR halted , h
  where
  L = haltBlock (leftStop h unL) hfL
  R = haltBlock (rightStop h unR) hfR
  halted = halt-of g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
             (proj₁ L) (proj₁ R) (proj₂ (proj₂ L)) (proj₂ (proj₂ R))
             (seenL h (proj₁ (proj₂ L))) (seenR h (proj₁ (proj₂ R)))

------------------------------------------------------------------------
-- A source step on the right writes `r2l` and advances the right cursor.
------------------------------------------------------------------------

afterR : SConf → SProc → EnvP → List String → Tok → W → SConf
afterR c p ρ′ pend′ t w =
  record c { right = p ; ir = entry w ; slotR = atSlot w
           ; r2l = ssnoc (r2l c) t
           ; envPR = ρ′
           ; envIR = addPend pend′ (ir c) (slotR c) (envIR c) }

roomR : ∀ {g c} (h : Hold g c) → length (r2l c) < cap c →
        room (Graph.cap g) (r2l c) ≡ true
roomR {g} {c} h le =
  room-yes (Graph.cap g) (r2l c)
    (subst (λ n → length (r2l c) < n) (Hold.κ h) le)

closeR : ∀ {g c p ρ′ pend′ j w wS} (t : Tok) (h : Hold g c) →
         reactR g (abs c) ≡
           AGo (rc (il c) j (l2r c) (snoc (r2l c) t) (el c) (er c)) →
         entry wS ≡ j →
         walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
              (suc (ir c)) (slotR c) ≡ just wS →
         walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
              (suc (ir c)) (slotR c) ≡ just w →
         (cur : Cursor (Hold.bsR h) (entry wS) (atSlot wS) ρ′
                       (addPend pend′ (ir c) (slotR c) (envIR c)) p) →
         Cursor.echoNs cur ≡ Cursor.echoNs (Hold.rightC h) →
         Step g (abs c) rside (abs (afterR c p ρ′ pend′ t w)) ×
         Hold g (afterR c p ρ′ pend′ t w)
closeR {g} {c} {p} {ρ′} {pend′} {j} {w} {wS} t h reacted ej wkS wk cur nse =
  stepR moved , record
    { nL = Hold.nL h ; bsL = Hold.bsL h ; odL = Hold.odL h ; cL = Hold.cL h
    ; nR = Hold.nR h ; bsR = Hold.bsR h ; odR = Hold.odR h ; cR = Hold.cR h
    ; α = Hold.α h ; κ = Hold.κ h
    ; leftC = Hold.leftC h ; rightC = curW
    ; nmL = Hold.nmL h
    ; nmR = trans (Hold.nmR h) (trans (sym nse) (sym (ns-keep weq cur))) }
  where
  weq : wS ≡ w
  weq = just-inj (trans (sym wkS) wk)
  atJ = subst (λ i → reactR g (abs c) ≡
                 AGo (rc (il c) i (l2r c) (snoc (r2l c) t) (el c) (er c)))
          (trans (sym ej) (cong entry weq)) reacted
  moved = subst (λ q → reactR g (abs c) ≡
                   AGo (rc (il c) (entry w) (l2r c) q (el c) (er c)))
            (sym (snoc≡ (r2l c) t)) atJ
  curW = subst (λ z → Cursor (Hold.bsR h) (entry z) (atSlot z) ρ′
                        (addPend pend′ (ir c) (slotR c) (envIR c)) p)
           weq cur

rightSend : ∀ {g c a p ρ′ pend′} (h : Hold g c) →
            Unfold (envPR c) [] (right c) ρ′ pend′ (f-put a p) →
            Send (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
                 (ir c) (slotR c) (envIR c) ρ′ pend′ a p
rightSend {c = c} h unf =
  openSend (rightBag h) (Cursor.pl rcur) (Cursor.cv rcur) (Cursor.lk rcur)
           (Cursor.hs rcur) (Cursor.at rcur) (Cursor.ens rcur) (Cursor.al rcur)
           (Cursor.ix rcur) (Cursor.ss rcur) (Cursor.sn rcur) unf
  where rcur = Hold.rightC h

putR-fwd : ∀ {g c a p ρ′ pend′ atom k w} (h : Hold g c) →
           Unfold (envPR c) [] (right c) ρ′ pend′ (f-put a p) →
           asAtom a ≡ just atom →
           findA atom (alpha c) ≡ just k →
           length (r2l c) < cap c →
           walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                (suc (ir c)) (slotR c) ≡ just w →
           Step g (abs c) rside (abs (afterR c p ρ′ pend′ (pay k) w)) ×
           Hold g (afterR c p ρ′ pend′ (pay k) w)
putR-fwd {g} {c} {a} {p} {ρ′} {pend′} {atom} {k} {w} h unf aq eqF le wk =
  use (rightSend h unf) aq
  where
  use : Send (Hold.bsR h) (Cursor.echoNs (Hold.rightC h)) (ir c) (slotR c)
             (envIR c) ρ′ pend′ a p →
        asAtom a ≡ just atom →
        Step g (abs c) rside (abs (afterR c p ρ′ pend′ (pay k) w)) ×
        Hold g (afterR c p ρ′ pend′ (pay k) w)
  use (echoed _ _ _ _ refl _ _ _ _ _ _) ()
  use (sent atomS j wS aeq ej mem wkS cur nse) aq′ =
    closeR (pay k) h reacted ej wkS wk cur nse
    where
    atom≡ = just-inj (trans (sym aeq) aq′)
    memA = subst (λ z → (ir c , bPut z j) ∈ Hold.bsR h) atom≡ mem
    findG = subst (λ al → findA atom al ≡ just k) (Hold.α h) eqF
    reacted = reactR-put g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                atom k j findG (roomR h le) (seenR h memA)

echoR-fwd : ∀ {g c x p ρ′ pend′ i k w} (h : Hold g c) →
            Unfold (envPR c) [] (right c) ρ′ pend′ (f-put (pEcho x) p) →
            findS x (namesR c) ≡ just i →
            slotVal (er c) i ≡ just k →
            length (r2l c) < cap c →
            walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                 (suc (ir c)) (slotR c) ≡ just w →
            Step g (abs c) rside (abs (afterR c p ρ′ pend′ (pay k) w)) ×
            Hold g (afterR c p ρ′ pend′ (pay k) w)
echoR-fwd {g} {c} {x} {p} {ρ′} {pend′} {i} {k} {w} h unf eqN eqS le wk =
  use (rightSend h unf)
  where
  use : Send (Hold.bsR h) (Cursor.echoNs (Hold.rightC h)) (ir c) (slotR c)
             (envIR c) ρ′ pend′ (pEcho x) p →
        Step g (abs c) rside (abs (afterR c p ρ′ pend′ (pay k) w)) ×
        Hold g (afterR c p ρ′ pend′ (pay k) w)
  use (sent _ _ _ () _ _ _ _ _)
  use (echoed .x sX j wS refl fd ej mem wkS cur nse) =
    closeR (pay k) h reacted ej wkS wk cur nse
    where
    i≡ = just-inj (trans (sym eqN)
           (trans (find≡ x (namesR c) (Cursor.echoNs (Hold.rightC h)) (Hold.nmR h)) fd))
    slotG = subst (λ z → slotVal (er c) z ≡ just k) i≡ eqS
    reacted = reactR-echo g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
                sX k j slotG (roomR h le) (seenR h mem)

pickR0-use : ∀ {g c p ρ′ pend′ w} (h : Hold g c) →
             length (r2l c) < cap c →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                  (suc (ir c)) (slotR c) ≡ just w →
             Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
                  (ir c) (slotR c) (envIR c) ρ′ pend′ (f-pick0 p) →
             Step g (abs c) rside (abs (afterR c p ρ′ pend′ (lab false) w)) ×
             Hold g (afterR c p ρ′ pend′ (lab false) w)
pickR0-use {g} {c} {p} {ρ′} {pend′} {w} h le wk
  (atAct suf ρi bg _
     (p-act (d-pick0 nD sD j .p ρw wD wkD ej dest dh ds de)
            r-pick0 i0 s0 ρden)
     (cp-act (c-pick0 mem cvD))
     (lk-pick0 eqi eqs _ lkD)
     (hs-pick0 hsD)
     (at-pick0 _ atD)
     (en-pick0 ensD)
     (al-pick0 eqρ destAl)
     ix ss sn lf-pick0) =
  closeR (lab false) h reacted ej (Gone.wk go) wk (Gone.cur go) (Gone.nse go)
  where
  en = trans ix eqi
  es = trans ss eqs
  go = sendCont {bs = Hold.bsR h} {ns = Cursor.echoNs (Hold.rightC h)}
         {n = ir c} {s = slotR c} {base = envIR c} {ρi = ρi}
         {pend = pend′} {suf = suf} {env = ρ′} {p = p}
         {nD = nD} {sD = sD} {sW = slotR c} {sW′ = sD}
         {ρden = ρden} {ρw = ρw} {w = wD} {dest = dest}
         bg en es es eqρ sn (cvd bg) wkD dh ds de cvD lkD hsD atD ensD destAl
  memN : (ir c , bPick0 j) ∈ Hold.bsR h
  memN = subst (λ i → (i , bPick0 j) ∈ Hold.bsR h) (sym en) mem
  reacted = reactR-pick0 g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
              j (roomR h le) (seenR h memN)

pickR0-fwd : ∀ {g c p ρ′ pend′ w} (h : Hold g c) →
             Unfold (envPR c) [] (right c) ρ′ pend′ (f-pick0 p) →
             length (r2l c) < cap c →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                  (suc (ir c)) (slotR c) ≡ just w →
             Step g (abs c) rside (abs (afterR c p ρ′ pend′ (lab false) w)) ×
             Hold g (afterR c p ρ′ pend′ (lab false) w)
pickR0-fwd h unf le wk = pickR0-use h le wk (rightStop h unf)

pickR1-use : ∀ {g c p ρ′ pend′ w} (h : Hold g c) →
             length (r2l c) < cap c →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                  (suc (ir c)) (slotR c) ≡ just w →
             Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
                  (ir c) (slotR c) (envIR c) ρ′ pend′ (f-pick1 p) →
             Step g (abs c) rside (abs (afterR c p ρ′ pend′ (lab true) w)) ×
             Hold g (afterR c p ρ′ pend′ (lab true) w)
pickR1-use {g} {c} {p} {ρ′} {pend′} {w} h le wk
  (atAct suf ρi bg _
     (p-act (d-pick1 nD sD j .p ρw wD wkD ej dest dh ds de)
            r-pick1 i0 s0 ρden)
     (cp-act (c-pick1 mem cvD))
     (lk-pick1 eqi eqs _ lkD)
     (hs-pick1 hsD)
     (at-pick1 _ atD)
     (en-pick1 ensD)
     (al-pick1 eqρ destAl)
     ix ss sn lf-pick1) =
  closeR (lab true) h reacted ej (Gone.wk go) wk (Gone.cur go) (Gone.nse go)
  where
  en = trans ix eqi
  es = trans ss eqs
  go = sendCont {bs = Hold.bsR h} {ns = Cursor.echoNs (Hold.rightC h)}
         {n = ir c} {s = slotR c} {base = envIR c} {ρi = ρi}
         {pend = pend′} {suf = suf} {env = ρ′} {p = p}
         {nD = nD} {sD = sD} {sW = slotR c} {sW′ = sD}
         {ρden = ρden} {ρw = ρw} {w = wD} {dest = dest}
         bg en es es eqρ sn (cvd bg) wkD dh ds de cvD lkD hsD atD ensD destAl
  memN : (ir c , bPick1 j) ∈ Hold.bsR h
  memN = subst (λ i → (i , bPick1 j) ∈ Hold.bsR h) (sym en) mem
  reacted = reactR-pick1 g (il c) (ir c) (l2r c) (r2l c) (el c) (er c)
              j (roomR h le) (seenR h memN)

pickR1-fwd : ∀ {g c p ρ′ pend′ w} (h : Hold g c) →
             Unfold (envPR c) [] (right c) ρ′ pend′ (f-pick1 p) →
             length (r2l c) < cap c →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                  (suc (ir c)) (slotR c) ≡ just w →
             Step g (abs c) rside (abs (afterR c p ρ′ pend′ (lab true) w)) ×
             Hold g (afterR c p ρ′ pend′ (lab true) w)
pickR1-fwd h unf le wk = pickR1-use h le wk (rightStop h unf)

------------------------------------------------------------------------
-- A source receive on the right pops `l2r`.
------------------------------------------------------------------------

afterGetR : SConf → SProc → EnvP → List String → List Tok → ℕ → W → SConf
afterGetR c p ρ′ pend′ rest k w =
  record c { right = p ; ir = entry w ; slotR = atSlot w
           ; l2r = rest ; er = setNth (slotR c) (suc k) (er c)
           ; envPR = ρ′
           ; envIR = addPend pend′ (ir c) (slotR c) (envIR c) }

closeGetR : ∀ {g c p ρ′ pend′ k rest j w wS n0 s0} (h : Hold g c) →
            reactR g (abs c) ≡
              AGo (rc (il c) j rest (r2l c) (el c)
                     (setNth (slotR c) (suc k) (er c))) →
            entry wS ≡ j →
            walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p n0 s0 ≡ just wS →
            walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p n0 s0 ≡ just w →
            (cur : Cursor (Hold.bsR h) (entry wS) (atSlot wS) ρ′
                          (addPend pend′ (ir c) (slotR c) (envIR c)) p) →
            Cursor.echoNs cur ≡ Cursor.echoNs (Hold.rightC h) →
            Step g (abs c) rside (abs (afterGetR c p ρ′ pend′ rest k w)) ×
            Hold g (afterGetR c p ρ′ pend′ rest k w)
closeGetR {g} {c} {p} {ρ′} {pend′} {k} {rest} {j} {w} {wS} h reacted ej wkS wk cur nse =
  stepR moved , record
    { nL = Hold.nL h ; bsL = Hold.bsL h ; odL = Hold.odL h ; cL = Hold.cL h
    ; nR = Hold.nR h ; bsR = Hold.bsR h ; odR = Hold.odR h ; cR = Hold.cR h
    ; α = Hold.α h ; κ = Hold.κ h
    ; leftC = Hold.leftC h ; rightC = curW
    ; nmL = Hold.nmL h
    ; nmR = trans (Hold.nmR h) (trans (sym nse) (sym (ns-keep weq cur))) }
  where
  weq : wS ≡ w
  weq = just-inj (trans (sym wkS) wk)
  moved = subst (λ i → reactR g (abs c) ≡
                   AGo (rc (il c) i rest (r2l c) (el c)
                          (setNth (slotR c) (suc k) (er c))))
            (trans (sym ej) (cong entry weq)) reacted
  curW = subst (λ z → Cursor (Hold.bsR h) (entry z) (atSlot z) ρ′
                        (addPend pend′ (ir c) (slotR c) (envIR c)) p)
           weq cur

afterPopR : SConf → SProc → EnvP → List String → List Tok → W → SConf
afterPopR c proc ρ′ pend′ rest w =
  record c { right = proc ; ir = entry w ; slotR = atSlot w
           ; l2r = rest
           ; envPR = ρ′
           ; envIR = addPend pend′ (ir c) (slotR c) (envIR c) }

closePopR : ∀ {g c proc ρ′ pend′ rest j w wS n0 s0} (h : Hold g c) →
            reactR g (abs c) ≡
              AGo (rc (il c) j rest (r2l c) (el c) (er c)) →
            entry wS ≡ j →
            walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) proc n0 s0 ≡ just wS →
            walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) proc n0 s0 ≡ just w →
            (cur : Cursor (Hold.bsR h) (entry wS) (atSlot wS) ρ′
                          (addPend pend′ (ir c) (slotR c) (envIR c)) proc) →
            Cursor.echoNs cur ≡ Cursor.echoNs (Hold.rightC h) →
            Step g (abs c) rside (abs (afterPopR c proc ρ′ pend′ rest w)) ×
            Hold g (afterPopR c proc ρ′ pend′ rest w)
closePopR {g} {c} {proc} {ρ′} {pend′} {rest} {j} {w} {wS} h reacted ej wkS wk cur nse =
  stepR moved , record
    { nL = Hold.nL h ; bsL = Hold.bsL h ; odL = Hold.odL h ; cL = Hold.cL h
    ; nR = Hold.nR h ; bsR = Hold.bsR h ; odR = Hold.odR h ; cR = Hold.cR h
    ; α = Hold.α h ; κ = Hold.κ h
    ; leftC = Hold.leftC h ; rightC = curW
    ; nmL = Hold.nmL h
    ; nmR = trans (Hold.nmR h) (trans (sym nse) (sym (ns-keep weq cur))) }
  where
  weq : wS ≡ w
  weq = just-inj (trans (sym wkS) wk)
  moved = subst (λ i → reactR g (abs c) ≡
                   AGo (rc (il c) i rest (r2l c) (el c) (er c)))
            (trans (sym ej) (cong entry weq)) reacted
  curW = subst (λ z → Cursor (Hold.bsR h) (entry z) (atSlot z) ρ′
                        (addPend pend′ (ir c) (slotR c) (envIR c)) proc)
           weq cur

getR-use : ∀ {g c t x p ρ′ pend′ k rest a w} (h : Hold g c) →
           l2r c ≡ pay k ∷ rest →
           nthA (alpha c) k ≡ just a →
           fits t a ≡ true →
           walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                (suc (ir c)) (suc (slotR c)) ≡ just w →
           Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
                (ir c) (slotR c) (envIR c) ρ′ pend′ (f-get t x p) →
           Step g (abs c) rside (abs (afterGetR c p ρ′ pend′ rest k w)) ×
           Hold g (afterGetR c p ρ′ pend′ rest k w)
getR-use {g} {c} {t} {x} {p} {ρ′} {pend′} {k} {rest} {a} {w} h qeq eqA eqF wk
  (atAct suf ρi bg _
     (p-act (d-get nD sD .t .x j .p ρw wD wkD ej dest dh ds de)
            r-get i0 s0 ρden)
     (cp-act (c-get mem cvD))
     (lk-get eqi eqs _ lkD)
     (hs-get hsD)
     (at-get _ atD)
     (en-get ensD)
     (al-get eqρ destAl)
     ix ss sn lf-get) =
  closeGetR h reacted ej (Gone.wk go) wk (Gone.cur go) (Gone.nse go)
  where
  en = trans ix eqi
  es = trans ss eqs
  go = sendCont {bs = Hold.bsR h} {ns = Cursor.echoNs (Hold.rightC h)}
         {n = ir c} {s = slotR c} {base = envIR c} {ρi = ρi}
         {pend = pend′} {suf = suf} {env = ρ′} {p = p}
         {nD = nD} {sD = sD} {sW = suc (slotR c)} {sW′ = suc sD}
         {ρden = ρden} {ρw = ρw} {w = wD} {dest = dest}
         bg en es (cong suc es) eqρ sn (cvd bg) wkD dh ds de
         cvD lkD hsD atD ensD destAl
  memI = subst (λ i → (i , bGet t sD j) ∈ Hold.bsR h) (sym en) mem
  memN : (ir c , bGet t (slotR c) j) ∈ Hold.bsR h
  memN = subst (λ z → (ir c , bGet t z j) ∈ Hold.bsR h) (sym es) memI
  nthG = subst (λ al → nthA al k ≡ just a) (Hold.α h) eqA
  got = reactR-get g (il c) (ir c) k rest (r2l c) (el c) (er c)
          t (slotR c) a j nthG eqF (seenR h memN)
  reacted = subst (λ queue →
              reactR g (rc (il c) (ir c) queue (r2l c) (el c) (er c)) ≡
                AGo (rc (il c) j rest (r2l c) (el c)
                       (setNth (slotR c) (suc k) (er c))))
              (sym qeq) got

getR-fwd : ∀ {g c t x p ρ′ pend′ k rest a w} (h : Hold g c) →
           Unfold (envPR c) [] (right c) ρ′ pend′ (f-get t x p) →
           l2r c ≡ pay k ∷ rest →
           nthA (alpha c) k ≡ just a →
           fits t a ≡ true →
           walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                (suc (ir c)) (suc (slotR c)) ≡ just w →
           Step g (abs c) rside (abs (afterGetR c p ρ′ pend′ rest k w)) ×
           Hold g (afterGetR c p ρ′ pend′ rest k w)
getR-fwd h unf qeq eqA eqF wk = getR-use h qeq eqA eqF wk (rightStop h unf)

coverR0-use : ∀ {g c p q ρ′ pend′ rest w} (h : Hold g c) →
              l2r c ≡ lab false ∷ rest →
              walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                   (suc (ir c)) (slotR c) ≡ just w →
              Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
                   (ir c) (slotR c) (envIR c) ρ′ pend′ (f-cover p q) →
              Step g (abs c) rside (abs (afterPopR c p ρ′ pend′ rest w)) ×
              Hold g (afterPopR c p ρ′ pend′ rest w)
coverR0-use {g} {c} {p} {q} {ρ′} {pend′} {rest} {w} h qeq wk
  (atAct suf ρi bg _
     (p-act (d-cover nD sD i j .p .q ρw w1 w2 wk1 ei wk2 ej
                     dp dq hp sp deP hq sq deQ)
            r-cover i0 s0 ρden)
     (cp-act (c-cover mem cvP cvQ))
     (lk-cover eqi eqs _ lkP lkQ)
     (hs-cover hsP hsQ)
     (at-cover _ atP atQ)
     (en-cover ensP ensQ)
     (al-cover eqρ alP alQ)
     ix ss sn lf-cover) =
  closePopR h reacted ei (Gone.wk go) wk (Gone.cur go) (Gone.nse go)
  where
  en = trans ix eqi
  es = trans ss eqs
  go = sendCont {bs = Hold.bsR h} {ns = Cursor.echoNs (Hold.rightC h)}
         {n = ir c} {s = slotR c} {base = envIR c} {ρi = ρi}
         {pend = pend′} {suf = suf} {env = ρ′} {p = p}
         {nD = nD} {sD = sD} {sW = slotR c} {sW′ = sD}
         {ρden = ρden} {ρw = ρw} {w = w1} {dest = dp}
         bg en es es eqρ sn (cvd bg) wk1 hp sp deP
         cvP lkP hsP atP ensP alP
  memN : (ir c , bCover i j) ∈ Hold.bsR h
  memN = subst (λ z → (z , bCover i j) ∈ Hold.bsR h) (sym en) mem
  got = reactR-cover0 g (il c) (ir c) rest (r2l c) (el c) (er c) i j (seenR h memN)
  reacted = subst (λ queue →
              reactR g (rc (il c) (ir c) queue (r2l c) (el c) (er c)) ≡
                AGo (rc (il c) i rest (r2l c) (el c) (er c)))
              (sym qeq) got

coverR0-fwd : ∀ {g c p q ρ′ pend′ rest w} (h : Hold g c) →
              Unfold (envPR c) [] (right c) ρ′ pend′ (f-cover p q) →
              l2r c ≡ lab false ∷ rest →
              walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                   (suc (ir c)) (slotR c) ≡ just w →
              Step g (abs c) rside (abs (afterPopR c p ρ′ pend′ rest w)) ×
              Hold g (afterPopR c p ρ′ pend′ rest w)
coverR0-fwd h unf qeq wk = coverR0-use h qeq wk (rightStop h unf)

coverR1-use : ∀ {g c p q ρ′ pend′ rest w1 w2} (h : Hold g c) →
              l2r c ≡ lab true ∷ rest →
              walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                   (suc (ir c)) (slotR c) ≡ just w1 →
              walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) q
                   (next w1) (slotN w1) ≡ just w2 →
              Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
                   (ir c) (slotR c) (envIR c) ρ′ pend′ (f-cover p q) →
              Step g (abs c) rside (abs (afterPopR c q ρ′ pend′ rest w2)) ×
              Hold g (afterPopR c q ρ′ pend′ rest w2)
coverR1-use {g} {c} {p} {q} {ρ′} {pend′} {rest} {w1} {w2} h qeq wk1 wk2
  (atAct suf ρi bg _
     (p-act (d-cover nD sD i j .p .q ρw w1D w2D wk1D ei wk2D ej
                     dp dq hp sp deP hq sq deQ)
            r-cover i0 s0 ρden)
     (cp-act (c-cover mem cvP cvQ))
     (lk-cover eqi eqs _ lkP lkQ)
     (hs-cover hsP hsQ)
     (at-cover _ atP atQ)
     (en-cover ensP ensQ)
     (al-cover eqρ alP alQ)
     ix ss sn lf-cover) =
  closePopR h reacted ej wk2Run wk2 cur (echo-env (run bg) cur0)
  where
  en = trans ix eqi
  es = trans ss eqs
  go = sendCont {bs = Hold.bsR h} {ns = Cursor.echoNs (Hold.rightC h)}
         {n = ir c} {s = slotR c} {base = envIR c} {ρi = ρi}
         {pend = pend′} {suf = suf} {env = ρ′} {p = p}
         {nD = nD} {sD = sD} {sW = slotR c} {sW′ = sD}
         {ρden = ρden} {ρw = ρw} {w = w1D} {dest = dp}
         bg en es es eqρ sn (cvd bg) wk1D hp sp deP
         cvP lkP hsP atP ensP alP
  same = just-inj (trans (sym (Gone.wk go)) wk1)
  extW = ext-leaf suf pend′ (ir c) (slotR c) nD sD ρden (envIR c) ρw ρi suf
           en es refl eqρ (run bg) sn (cvd bg)
  wkI = walk-ext [] ρw ρi q (next w1D) (slotN w1D) w2D extW wk2D
  wkAt = subst (λ z → walk [] ρi q (next z) (slotN z) ≡ just w2D) same wkI
  wk2Run = subst (λ e → walk [] e q (next w1) (slotN w1) ≡ just w2D) (run bg) wkAt
  snD = subst (λ e → Ext e ρi) (sym deQ) extW
  cur0 = arrive {ns = Cursor.echoNs (Hold.rightC h)} {tab = tab bg} dq w2D
           (ct bg) (ls bg) (td bg) (sy bg) (kn bg) (nd bg)
           hq sq cvQ lkQ hsQ atQ ensQ alQ snD
  cur = subst (λ e → Cursor (Hold.bsR h) (entry w2D) (atSlot w2D) ρ′ e q)
          (run bg) cur0
  memN : (ir c , bCover i j) ∈ Hold.bsR h
  memN = subst (λ z → (z , bCover i j) ∈ Hold.bsR h) (sym en) mem
  got = reactR-cover1 g (il c) (ir c) rest (r2l c) (el c) (er c) i j (seenR h memN)
  reacted = subst (λ queue →
              reactR g (rc (il c) (ir c) queue (r2l c) (el c) (er c)) ≡
                AGo (rc (il c) j rest (r2l c) (el c) (er c)))
              (sym qeq) got

coverR1-fwd : ∀ {g c p q ρ′ pend′ rest w1 w2} (h : Hold g c) →
              Unfold (envPR c) [] (right c) ρ′ pend′ (f-cover p q) →
              l2r c ≡ lab true ∷ rest →
              walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                   (suc (ir c)) (slotR c) ≡ just w1 →
              walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) q
                   (next w1) (slotN w1) ≡ just w2 →
              Step g (abs c) rside (abs (afterPopR c q ρ′ pend′ rest w2)) ×
              Hold g (afterPopR c q ρ′ pend′ rest w2)
coverR1-fwd h unf qeq wk1 wk2 = coverR1-use h qeq wk1 wk2 (rightStop h unf)

igetR0-use : ∀ {g c x p q ρ′ pend′ k rest w} (h : Hold g c) →
             l2r c ≡ pay k ∷ rest →
             nthA (alpha c) k ≡ just (aBit false) →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                  (suc (ir c)) (suc (slotR c)) ≡ just w →
             Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
                  (ir c) (slotR c) (envIR c) ρ′ pend′ (f-iget x p q) →
             Step g (abs c) rside (abs (afterGetR c p ρ′ pend′ rest k w)) ×
             Hold g (afterGetR c p ρ′ pend′ rest k w)
igetR0-use {g} {c} {x} {p} {q} {ρ′} {pend′} {k} {rest} {w} h qeq eqA wk
  (atAct suf ρi bg _
     (p-act (d-iget nD sD .x i j .p .q ρw w1D w2D wk1D ei wk2D ej
                    dp dq hp sp deP hq sq deQ)
            r-iget i0 s0 ρden)
     (cp-act (c-iget mem cvP cvQ))
     (lk-iget eqi eqs _ lkP lkQ)
     (hs-iget hsP hsQ)
     (at-iget _ atP atQ)
     (en-iget ensP ensQ)
     (al-iget eqρ alP alQ)
     ix ss sn lf-iget) =
  closeGetR h reacted ei (Gone.wk go) wk (Gone.cur go) (Gone.nse go)
  where
  en = trans ix eqi
  es = trans ss eqs
  go = sendCont {bs = Hold.bsR h} {ns = Cursor.echoNs (Hold.rightC h)}
         {n = ir c} {s = slotR c} {base = envIR c} {ρi = ρi}
         {pend = pend′} {suf = suf} {env = ρ′} {p = p}
         {nD = nD} {sD = sD} {sW = suc (slotR c)} {sW′ = suc sD}
         {ρden = ρden} {ρw = ρw} {w = w1D} {dest = dp}
         bg en es (cong suc es) eqρ sn (cvd bg) wk1D hp sp deP
         cvP lkP hsP atP ensP alP
  memI = subst (λ z → (z , bIget sD i j) ∈ Hold.bsR h) (sym en) mem
  memN : (ir c , bIget (slotR c) i j) ∈ Hold.bsR h
  memN = subst (λ z → (ir c , bIget z i j) ∈ Hold.bsR h) (sym es) memI
  nthG = subst (λ al → nthA al k ≡ just (aBit false)) (Hold.α h) eqA
  got = reactR-iget0 g (il c) (ir c) k rest (r2l c) (el c) (er c)
          (slotR c) i j nthG (seenR h memN)
  reacted = subst (λ queue →
              reactR g (rc (il c) (ir c) queue (r2l c) (el c) (er c)) ≡
                AGo (rc (il c) i rest (r2l c) (el c)
                       (setNth (slotR c) (suc k) (er c))))
              (sym qeq) got

igetR0-fwd : ∀ {g c x p q ρ′ pend′ k rest w} (h : Hold g c) →
             Unfold (envPR c) [] (right c) ρ′ pend′ (f-iget x p q) →
             l2r c ≡ pay k ∷ rest →
             nthA (alpha c) k ≡ just (aBit false) →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                  (suc (ir c)) (suc (slotR c)) ≡ just w →
             Step g (abs c) rside (abs (afterGetR c p ρ′ pend′ rest k w)) ×
             Hold g (afterGetR c p ρ′ pend′ rest k w)
igetR0-fwd h unf qeq eqA wk = igetR0-use h qeq eqA wk (rightStop h unf)

igetR1-use : ∀ {g c x p q ρ′ pend′ k rest w1 w2} (h : Hold g c) →
             l2r c ≡ pay k ∷ rest →
             nthA (alpha c) k ≡ just (aBit true) →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                  (suc (ir c)) (suc (slotR c)) ≡ just w1 →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) q
                  (next w1) (slotN w1) ≡ just w2 →
             Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
                  (ir c) (slotR c) (envIR c) ρ′ pend′ (f-iget x p q) →
             Step g (abs c) rside (abs (afterGetR c q ρ′ pend′ rest k w2)) ×
             Hold g (afterGetR c q ρ′ pend′ rest k w2)
igetR1-use {g} {c} {x} {p} {q} {ρ′} {pend′} {k} {rest} {w1} {w2} h qeq eqA wk1 wk2
  (atAct suf ρi bg _
     (p-act (d-iget nD sD .x i j .p .q ρw w1D w2D wk1D ei wk2D ej
                    dp dq hp sp deP hq sq deQ)
            r-iget i0 s0 ρden)
     (cp-act (c-iget mem cvP cvQ))
     (lk-iget eqi eqs _ lkP lkQ)
     (hs-iget hsP hsQ)
     (at-iget _ atP atQ)
     (en-iget ensP ensQ)
     (al-iget eqρ alP alQ)
     ix ss sn lf-iget) =
  closeGetR h reacted ej wk2Run wk2 cur (echo-env (run bg) cur0)
  where
  en = trans ix eqi
  es = trans ss eqs
  go = sendCont {bs = Hold.bsR h} {ns = Cursor.echoNs (Hold.rightC h)}
         {n = ir c} {s = slotR c} {base = envIR c} {ρi = ρi}
         {pend = pend′} {suf = suf} {env = ρ′} {p = p}
         {nD = nD} {sD = sD} {sW = suc (slotR c)} {sW′ = suc sD}
         {ρden = ρden} {ρw = ρw} {w = w1D} {dest = dp}
         bg en es (cong suc es) eqρ sn (cvd bg) wk1D hp sp deP
         cvP lkP hsP atP ensP alP
  same = just-inj (trans (sym (Gone.wk go)) wk1)
  extW = ext-leaf suf pend′ (ir c) (slotR c) nD sD ρden (envIR c) ρw ρi suf
           en es refl eqρ (run bg) sn (cvd bg)
  wkI = walk-ext [] ρw ρi q (next w1D) (slotN w1D) w2D extW wk2D
  wkAt = subst (λ z → walk [] ρi q (next z) (slotN z) ≡ just w2D) same wkI
  wk2Run = subst (λ e → walk [] e q (next w1) (slotN w1) ≡ just w2D) (run bg) wkAt
  snD = subst (λ e → Ext e ρi) (sym deQ) extW
  cur0 = arrive {ns = Cursor.echoNs (Hold.rightC h)} {tab = tab bg} dq w2D
           (ct bg) (ls bg) (td bg) (sy bg) (kn bg) (nd bg)
           hq sq cvQ lkQ hsQ atQ ensQ alQ snD
  cur = subst (λ e → Cursor (Hold.bsR h) (entry w2D) (atSlot w2D) ρ′ e q)
          (run bg) cur0
  memI = subst (λ z → (z , bIget sD i j) ∈ Hold.bsR h) (sym en) mem
  memN : (ir c , bIget (slotR c) i j) ∈ Hold.bsR h
  memN = subst (λ z → (ir c , bIget z i j) ∈ Hold.bsR h) (sym es) memI
  nthG = subst (λ al → nthA al k ≡ just (aBit true)) (Hold.α h) eqA
  got = reactR-iget1 g (il c) (ir c) k rest (r2l c) (el c) (er c)
          (slotR c) i j nthG (seenR h memN)
  reacted = subst (λ queue →
              reactR g (rc (il c) (ir c) queue (r2l c) (el c) (er c)) ≡
                AGo (rc (il c) j rest (r2l c) (el c)
                       (setNth (slotR c) (suc k) (er c))))
              (sym qeq) got

igetR1-fwd : ∀ {g c x p q ρ′ pend′ k rest w1 w2} (h : Hold g c) →
             Unfold (envPR c) [] (right c) ρ′ pend′ (f-iget x p q) →
             l2r c ≡ pay k ∷ rest →
             nthA (alpha c) k ≡ just (aBit true) →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) p
                  (suc (ir c)) (suc (slotR c)) ≡ just w1 →
             walk [] (addPend pend′ (ir c) (slotR c) (envIR c)) q
                  (next w1) (slotN w1) ≡ just w2 →
             Step g (abs c) rside (abs (afterGetR c q ρ′ pend′ rest k w2)) ×
             Hold g (afterGetR c q ρ′ pend′ rest k w2)
igetR1-fwd h unf qeq eqA wk1 wk2 = igetR1-use h qeq eqA wk1 wk2 (rightStop h unf)

mgetR-use : ∀ {g c t x as ρ′ pend′ k rest a name w p} (h : Hold g c) →
            l2r c ≡ pay k ∷ rest →
            nthA (alpha c) k ≡ just a →
            fits t a ≡ true →
            conOf a ≡ just name →
            armGo (addPend pend′ (ir c) (slotR c) (envIR c)) name as
                  (suc (ir c)) (suc (slotR c)) ≡ just (w , p) →
            Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
                 (ir c) (slotR c) (envIR c) ρ′ pend′ (f-mget t x as) →
            Step g (abs c) rside (abs (afterGetR c p ρ′ pend′ rest k w)) ×
            Hold g (afterGetR c p ρ′ pend′ rest k w)
mgetR-use {g} {c} {t} {x} {as} {ρ′} {pend′} {k} {rest} {a} {name} {w} {p}
          h qeq eqA eqF eqC ago
  (atAct suf ρi bg _
     (p-act (d-mget nD sD .t .x named .as ρw ws n2 s2 wkD enW dests)
            r-mget i0 s0 ρden)
     (cp-act (c-mget mem cvA))
     (lk-mget eqi eqs _ lkA)
     (hs-mget hsA)
     (at-mget _ atA)
     (en-mget enA)
     (al-mget eqρ alA)
     ix ss sn lf-mget) =
  closeGetR h reacted refl wkRun wkRun cur (echo-env (run bg) cur0)
  where
  en = trans ix eqi
  es = trans ss eqs
  extW = ext-leaf suf pend′ (ir c) (slotR c) nD sD ρden (envIR c) ρw ρi suf
           en es refl eqρ (run bg) sn (cvd bg)
  wk1 = subst (λ z → walkArms [] ρw as (suc z) (suc sD) ≡ just (ws , n2 , s2))
          (sym en) wkD
  wkC = subst (λ z → walkArms [] ρw as (suc (ir c)) (suc z) ≡ just (ws , n2 , s2))
          (sym es) wk1
  agoI = subst (λ e → armGo e name as (suc (ir c)) (suc (slotR c)) ≡ just (w , p))
           (sym (run bg)) ago
  hitD = armGo-agree as extW wkC agoI
  pk = armPick dests lkA hsA atA enA alA cvA wkC hitD
  wkI = walk-ext [] ρw ρi p (Pick.n0 pk) (Pick.s0 pk) w extW (Pick.wk pk)
  wkRun = subst (λ e → walk [] e p (Pick.n0 pk) (Pick.s0 pk) ≡ just w)
            (run bg) wkI
  snD = subst (λ e → Ext e ρi) (sym (Pick.ev pk)) extW
  cur0 = arrive {ns = Cursor.echoNs (Hold.rightC h)} {tab = tab bg}
           (Pick.pl pk) w (ct bg) (ls bg) (td bg) (sy bg) (kn bg) (nd bg)
           (Pick.hd pk) (Pick.sl pk) (Pick.cv pk) (Pick.lk pk) (Pick.hs pk)
           (Pick.at pk) (Pick.ens pk) (Pick.al pk) snD
  cur = subst (λ e → Cursor (Hold.bsR h) (entry w) (atSlot w) ρ′ e p)
          (run bg) cur0
  memI = subst (λ z → (z , bMget t sD named) ∈ Hold.bsR h) (sym en) mem
  memN : (ir c , bMget t (slotR c) named) ∈ Hold.bsR h
  memN = subst (λ z → (ir c , bMget t z named) ∈ Hold.bsR h) (sym es) memI
  nthG = subst (λ al → nthA al k ≡ just a) (Hold.α h) eqA
  toN = subst (λ xs → armTo name xs ≡ just (entry w)) enW (Pick.aj pk)
  got = reactR-mget g (il c) (ir c) k rest (r2l c) (el c) (er c)
          t (slotR c) named a name (entry w) nthG eqF eqC toN (seenR h memN)
  reacted = subst (λ queue →
              reactR g (rc (il c) (ir c) queue (r2l c) (el c) (er c)) ≡
                AGo (rc (il c) (entry w) rest (r2l c) (el c)
                       (setNth (slotR c) (suc k) (er c))))
              (sym qeq) got

mgetR-fwd : ∀ {g c t x as ρ′ pend′ k rest a name w p} (h : Hold g c) →
            Unfold (envPR c) [] (right c) ρ′ pend′ (f-mget t x as) →
            l2r c ≡ pay k ∷ rest →
            nthA (alpha c) k ≡ just a →
            fits t a ≡ true →
            conOf a ≡ just name →
            armGo (addPend pend′ (ir c) (slotR c) (envIR c)) name as
                  (suc (ir c)) (suc (slotR c)) ≡ just (w , p) →
            Step g (abs c) rside (abs (afterGetR c p ρ′ pend′ rest k w)) ×
            Hold g (afterGetR c p ρ′ pend′ rest k w)
mgetR-fwd h unf qeq eqA eqF eqC ago = mgetR-use h qeq eqA eqF eqC ago (rightStop h unf)

------------------------------------------------------------------------
-- Every source step is the graph step of the block it denotes.
------------------------------------------------------------------------

sim-fwd : ∀ {g c c′} → Hold g c → c ⟶ₛ c′ →
          Σ Who (λ w → Step g (abs c) w (abs c′) × Hold g c′)
sim-fwd h (put-l unf aq eqF le wk) = lside , put-fwd h unf aq eqF le wk
sim-fwd h (echo-l unf eqN eqS le wk) = lside , echo-fwd h unf eqN eqS le wk
sim-fwd h (pick0-l unf le wk) = lside , pick0-fwd h unf le wk
sim-fwd h (pick1-l unf le wk) = lside , pick1-fwd h unf le wk
sim-fwd h (get-l unf qeq eqA eqF wk) = lside , get-fwd h unf qeq eqA eqF wk
sim-fwd h (cover0-l unf qeq wk) = lside , cover0-fwd h unf qeq wk
sim-fwd h (cover1-l unf qeq wk1 wk2) = lside , cover1-fwd h unf qeq wk1 wk2
sim-fwd h (iget0-l unf qeq eqA wk) = lside , iget0-fwd h unf qeq eqA wk
sim-fwd h (iget1-l unf qeq eqA wk1 wk2) = lside , iget1-fwd h unf qeq eqA wk1 wk2
sim-fwd h (mget-l unf qeq eqA eqF eqC ago) = lside , mget-fwd h unf qeq eqA eqF eqC ago
sim-fwd h (put-r unf aq eqF le wk) = rside , putR-fwd h unf aq eqF le wk
sim-fwd h (echo-r unf eqN eqS le wk) = rside , echoR-fwd h unf eqN eqS le wk
sim-fwd h (pick0-r unf le wk) = rside , pickR0-fwd h unf le wk
sim-fwd h (pick1-r unf le wk) = rside , pickR1-fwd h unf le wk
sim-fwd h (get-r unf qeq eqA eqF wk) = rside , getR-fwd h unf qeq eqA eqF wk
sim-fwd h (cover0-r unf qeq wk) = rside , coverR0-fwd h unf qeq wk
sim-fwd h (cover1-r unf qeq wk1 wk2) = rside , coverR1-fwd h unf qeq wk1 wk2
sim-fwd h (iget0-r unf qeq eqA wk) = rside , igetR0-fwd h unf qeq eqA wk
sim-fwd h (iget1-r unf qeq eqA wk1 wk2) = rside , igetR1-fwd h unf qeq eqA wk1 wk2
sim-fwd h (mget-r unf qeq eqA eqF eqC ago) = rside , mgetR-fwd h unf qeq eqA eqF eqC ago
sim-fwd h (sfinish unL hfL unR hfR eqL eqR) = fin , fin-fwd h unL hfL unR hfR eqL eqR

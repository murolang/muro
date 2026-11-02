------------------------------------------------------------------------
-- The unfold that follows a jump.
--
-- `spine` stops at `p-jump`. The jump names a `mu` sealed earlier,
-- which sits in front of the entry that jumps. Reading the table from
-- the front, that target is already in hand, so the hop stores it.
-- Chasing the hop is structural. A `mu` peels. A jump continues as
-- the process it names, in the same environment. An action is the focus.
--
-- The cursor's place is not always an entry top. `place-hop` reads it
-- from the front: a `mu` peels, an action is a leaf, and a jump takes
-- the hop of the entry it names. `unfold-at` is that reading for the
-- cursor a configuration is standing on.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Chase where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Muro.AsyncRec using (elemS)
open import Muro.Temporal.Bridge using (distinct; ∧-left; ∧-right; true≢false)
open import Muro.Temporal.Pic using (==-sound)
open import Muro.Temporal.Source
  using ( SProc; smu; SConf; EnvP; EnvI; lookupI
        ; Focus; f-done; f-stop; f-put; f-get; f-pick0; f-pick1
        ; f-cover; f-iget; f-mget
        ; Unfold; u-mu; u-var; u-done; u-stop; u-put; u-get
        ; u-pick0; u-pick1; u-cover; u-iget; u-mget
        ; Bound; b-here; b-there )
open SConf
open import Muro.Temporal.Den
  using ( Place; p-mu; p-act; p-jump
        ; Den; d-done; d-stop; d-put; d-echo; d-pick0; d-pick1
        ; d-get; d-cover; d-iget; d-mget
        ; Recipe; r-done; r-stop; r-put; r-echo; r-pick0; r-pick1
        ; r-get; r-cover; r-iget; r-mget
        ; Table; t0; t1; tnames
        ; Link; lk-mu; lk-jump; lk-done; lk-stop; lk-put; lk-echo
        ; lk-pick0; lk-pick1; lk-get; lk-cover; lk-iget; lk-mget
        ; Hosts; hs-mu; hs-jump
        ; InTab; in-here; in-there; place-of; ix-of; slot-at
        ; ix-head; slot-head; headIx; slotOf; envOf
        ; Links; ls0; ls1; At; at-mu; at-of
        ; EchoNs; en-mu; Align; al-mu )
open import Muro.Temporal.Nest
  using ( Here; h-here; h-there
        ; Sp; sp-leaf; sp-mu; sp-jump
        ; Land; ln-env; ln-pend; ln-above
        ; Ts; ts0; ts1 )
open import Muro.Temporal.Run
  using ( Tied; td0; td1; Sync; sy0; sy1
        ; Knew; kn0; kn1; Ext; ext-front
        ; Covered; cov-cons; cov-push; cov-id
        ; runtime-pin; unique; fresh-occ; occurs
        ; sync-hit; sync-drop; kn-find; Found; same-slot
        ; Cursor; Hold )
open Cursor
open Hold

nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

-- Two entries of one name are the same row of the table.
same-place : ∀ {x P tab} (m n : InTab x P tab) →
             distinct (tnames tab) ≡ true →
             place-of m ≡ place-of n
same-place (in-here _) (in-here _) _ = refl
same-place {x = x} (in-here _) (in-there {tab = tab} n) eq =
  ⊥-elim (true≢false (trans (sym (∧-left eq))
           (fresh-occ x (tnames tab) (occurs n))))
same-place {x = x} (in-there {tab = tab} m) (in-here _) eq =
  ⊥-elim (true≢false (trans (sym (∧-left eq))
           (fresh-occ x (tnames tab) (occurs m))))
same-place (in-there m) (in-there n) eq = same-place m n (∧-right eq)

------------------------------------------------------------------------
-- A hop is the spine of a place, with the target of each jump stored
-- in the node. The target was built earlier, so the chase is structural.
------------------------------------------------------------------------

data Leaf : {P : SProc} → Place P → Set where
  lh-done : ∀ {n i s ρ} → Leaf (p-act (d-done n) r-done i s ρ)
  lh-stop : ∀ {n i s ρ} → Leaf (p-act (d-stop n) r-stop i s ρ)
  lh-put : ∀ {n s a atom j p ρw w aeq wk ej dest dh ds de i0 s0 ρ} →
           Leaf (p-act (d-put n s a atom j p ρw w aeq wk ej dest dh ds de)
                       r-put i0 s0 ρ)
  lh-echo : ∀ {n s x ns sX j p ρw w fd wk ej dest dh ds de i0 s0 ρ} →
            Leaf (p-act (d-echo n s x ns sX j p ρw w fd wk ej dest dh ds de)
                        r-echo i0 s0 ρ)
  lh-pick0 : ∀ {n s j p ρw w wk ej dest dh ds de i0 s0 ρ} →
             Leaf (p-act (d-pick0 n s j p ρw w wk ej dest dh ds de)
                         r-pick0 i0 s0 ρ)
  lh-pick1 : ∀ {n s j p ρw w wk ej dest dh ds de i0 s0 ρ} →
             Leaf (p-act (d-pick1 n s j p ρw w wk ej dest dh ds de)
                         r-pick1 i0 s0 ρ)
  lh-get : ∀ {n s t x j p ρw w wk ej dest dh ds de i0 s0 ρ} →
           Leaf (p-act (d-get n s t x j p ρw w wk ej dest dh ds de)
                       r-get i0 s0 ρ)
  lh-cover : ∀ {n s i j p q ρw w1 w2 wk1 ei wk2 ej dp dq hp sp ep hq sq eq₀
               i0 s0 ρ} →
             Leaf (p-act (d-cover n s i j p q ρw w1 w2 wk1 ei wk2 ej dp dq
                                  hp sp ep hq sq eq₀)
                         r-cover i0 s0 ρ)
  lh-iget : ∀ {n s x i j p q ρw w1 w2 wk1 ei wk2 ej dp dq hp sp ep hq sq eq₀
              i0 s0 ρ} →
             Leaf (p-act (d-iget n s x i j p q ρw w1 w2 wk1 ei wk2 ej dp dq
                                 hp sp ep hq sq eq₀)
                        r-iget i0 s0 ρ)
  lh-mget : ∀ {n s t x named as ρw ws n2 s2 wk en dests i0 s0 ρ} →
            Leaf (p-act (d-mget n s t x named as ρw ws n2 s2 wk en dests)
                        r-mget i0 s0 ρ)

-- `tab` is an index. A place does not determine which table it was
-- read from, and a leaf does not mention the table at all.
data Hop (tab : Table) : {P : SProc} → Place P → Set where
  hop-mu : ∀ {x p} {pl : Place p} →
           (inn : InTab x (smu x p) tab) →
           place-of inn ≡ p-mu x pl →
           Hop tab pl →
           Hop tab (p-mu x pl)
  hop-jump : ∀ {y Q i s ρ} →
             (m : InTab y Q tab) →
             lookupI y ρ ≡ just (i , s) →
             Hop tab (place-of m) →
             Hop tab (p-jump y i s ρ)
  hop-leaf : ∀ {P} {pl : Place P} → Leaf pl → Hop tab pl

------------------------------------------------------------------------
-- The front of the table is the entry just sealed. The tail was sealed
-- earlier. `Peel` remembers how many fronts were passed, so an entry
-- of the tail is an entry of the whole table.
------------------------------------------------------------------------

data Peel (full : Table) : Table → Set where
  pe0 : Peel full full
  peS : ∀ {Q y i s ρ ql suf} →
        Peel full (t1 {Q} y i s ρ ql suf) →
        Peel full suf

apply : ∀ {full suf x P} → Peel full suf → InTab x P suf → InTab x P full
apply pe0 m = m
apply (peS p) m = apply p (in-there m)

place-apply : ∀ {full suf x P} (p : Peel full suf) (m : InTab x P suf) →
              place-of (apply p m) ≡ place-of m
place-apply pe0 m = refl
place-apply (peS p) m = place-apply p (in-there m)

-- Names already read, nearest first. A jump's `above` list is this.
data Built (full : Table) : List String → Set where
  bd0 : Built full []
  bd1 : ∀ {y ys P} (m : InTab y P full) →
        Hop full (place-of m) →
        Built full ys →
        Built full (y ∷ ys)

get : ∀ {full y above} → Here y above → Built full above →
      Σ SProc (λ Q → Σ (InTab y Q full) (λ m → Hop full (place-of m)))
get h-here (bd1 m h _) = _ , m , h
get (h-there hr) (bd1 _ _ b) = get hr b

-- One hop for every entry, in table order.
data HTab (full : Table) : Table → Set where
  hz : HTab full t0
  hc : ∀ {P x i s ρ pl suf} →
       (m : InTab x P full) →
       place-of m ≡ pl →
       Hop full pl →
       HTab full suf →
       HTab full (t1 {P} x i s ρ pl suf)

open-hs : ∀ {tab x p} {pl : Place p} →
          Hosts tab (p-mu x pl) →
          Σ (InTab x (smu x p) tab) (λ inn →
            place-of inn ≡ p-mu x pl × Hosts tab pl)
open-hs (hs-mu inn eq hs) = inn , eq , hs

hopSp : ∀ {full suf above P} {pl : Place P} →
        Peel full suf →
        Sp [] [] above pl →
        Link pl →
        Hosts suf pl →
        Built full above →
        Hop full pl
hopSp peel (sp-mu sp) (lk-mu lk) hs b =
  let inn , eq , hsB = open-hs hs
  in hop-mu (apply peel inn)
       (trans (place-apply peel inn) eq)
       (hopSp peel sp lk hsB b)
hopSp _ (sp-jump (ln-above hr)) (lk-jump look) _ b =
  let _ , m , h = get hr b
  in hop-jump m look h
hopSp _ sp-leaf (lk-done _) _ _ = hop-leaf lh-done
hopSp _ sp-leaf (lk-stop _) _ _ = hop-leaf lh-stop
hopSp _ sp-leaf (lk-put _ _ _ _) _ _ = hop-leaf lh-put
hopSp _ sp-leaf (lk-echo _ _ _ _) _ _ = hop-leaf lh-echo
hopSp _ sp-leaf (lk-pick0 _ _ _ _) _ _ = hop-leaf lh-pick0
hopSp _ sp-leaf (lk-pick1 _ _ _ _) _ _ = hop-leaf lh-pick1
hopSp _ sp-leaf (lk-get _ _ _ _) _ _ = hop-leaf lh-get
hopSp _ sp-leaf (lk-cover _ _ _ _ _) _ _ = hop-leaf lh-cover
hopSp _ sp-leaf (lk-iget _ _ _ _ _) _ _ = hop-leaf lh-iget
hopSp _ sp-leaf (lk-mget _ _ _ _) _ _ = hop-leaf lh-mget
hopSp _ (sp-jump (ln-env ())) _ _ _
hopSp _ (sp-jump (ln-pend ())) _ _ _

table-go : ∀ {full suf above} →
           Peel full suf →
           Ts [] [] above suf →
           Links suf →
           Built full above →
           HTab full suf
table-go _ ts0 _ _ = hz
table-go {full = full} peel (ts1 {x = x} {pl = pl} sp rest) (ls1 lk _ _ hs _ ls) b =
  let h = hopSp peel sp lk hs b
      m = apply peel (in-here lk)
      eq = place-apply peel (in-here lk)
      b′ = bd1 m (subst (λ q → Hop full q) (sym eq) h) b
  in hc m eq h (table-go (peS peel) rest ls b′)

-- The root witness has an empty environment and an empty pending list,
-- so every jump in it is an earlier entry.
table-hops : ∀ {tab} → Ts [] [] [] tab → Links tab → HTab tab tab
table-hops ts ls = table-go pe0 ts ls bd0

lookupH : ∀ {full y P suf} (m : InTab y P suf) → HTab full suf →
          Hop full (place-of m)
lookupH (in-here _) (hc _ _ h _) = h
lookupH (in-there m) (hc _ _ _ rest) = lookupH m rest

-- The process a runtime environment binds for this entry.
sync-bound : ∀ {y Q tab env ρ i s} →
             Sync tab env ρ →
             lookupI y ρ ≡ just (i , s) →
             InTab y Q tab →
             distinct (tnames tab) ≡ true →
             Bound y Q env
sync-bound sy0 eq _ _ = ⊥-elim (nothing≢just eq)
sync-bound {y} {Q} {i = i} {s = s}
           (sy1 {x = x} {P = P} {i = j} {s = s0} m _ _ rest)
           look mQ nd =
  step (y == x) refl look
  where
  step : (b : Bool) → (y == x) ≡ b →
         lookupI y ((x , j , s0) ∷ _) ≡ just (i , s) →
         Bound y Q ((x , P) ∷ _)
  step true eqy _ =
    let y≡x = ==-sound eqy
        mQx = subst (λ z → InTab z Q _) y≡x mQ
        P≡Q = unique m mQx nd
        hereQ = subst (λ R → Bound x R ((x , P) ∷ _)) P≡Q b-here
    in subst (λ z → Bound z Q ((x , P) ∷ _)) (sym y≡x) hereQ
  step false eqy look′ =
    b-there (sync-bound rest
      (sync-drop {x = y} {y = x} {j = j} {s0 = s0} {i = i} {s = s} eqy look′)
      mQ nd)

------------------------------------------------------------------------
-- What the cursor denotes, read off its place. A jump uses the hop of
-- the entry `sync-hit` finds. The stored target is not walked again here.
------------------------------------------------------------------------

place-hop : ∀ {tab env ρi P} {pl : Place P} →
            HTab tab tab →
            Link pl →
            Hosts tab pl →
            Sync tab env ρi →
            Ext (envOf pl) ρi →
            distinct (tnames tab) ≡ true →
            Hop tab pl
place-hop ht (lk-mu lk) hs sy sn nd =
  let inn , eq , hsB = open-hs hs
  in hop-mu inn eq (place-hop ht lk hsB sy sn nd)
place-hop ht (lk-jump {x = y} {i = i} {s0 = s} look) _ sy sn nd =
  let got = sync-hit sy (sn y i s look)
      m = proj₁ (proj₂ got)
  in hop-jump m look (lookupH m ht)
place-hop _ (lk-done _) _ _ _ _ = hop-leaf lh-done
place-hop _ (lk-stop _) _ _ _ _ = hop-leaf lh-stop
place-hop _ (lk-put _ _ _ _) _ _ _ _ = hop-leaf lh-put
place-hop _ (lk-echo _ _ _ _) _ _ _ _ = hop-leaf lh-echo
place-hop _ (lk-pick0 _ _ _ _) _ _ _ _ = hop-leaf lh-pick0
place-hop _ (lk-pick1 _ _ _ _) _ _ _ _ = hop-leaf lh-pick1
place-hop _ (lk-get _ _ _ _) _ _ _ _ = hop-leaf lh-get
place-hop _ (lk-cover _ _ _ _ _) _ _ _ _ = hop-leaf lh-cover
place-hop _ (lk-iget _ _ _ _ _) _ _ _ _ = hop-leaf lh-iget
place-hop _ (lk-mget _ _ _ _) _ _ _ _ = hop-leaf lh-mget

------------------------------------------------------------------------
-- The unfold. The environment at a jump is the environment the jump
-- was reached in. Peeling a `mu` pushes that binder, which is how a
-- jump further out still has a source.
------------------------------------------------------------------------

record Opened (env : EnvP) (pend : List String) (P : SProc) : Set where
  constructor opened
  field
    ρ′ : EnvP
    pend′ : List String
    f : Focus
    unf : Unfold env pend P ρ′ pend′ f

open Opened

record Sit (tab : Table) {P : SProc} (pl : Place P) : Set where
  constructor mkSit
  field
    env : EnvP
    pend : List String
    ρi : EnvI
    suf : List String
    n s : ℕ
    ns : List String
    td : Tied tab env
    sy : Sync tab env ρi
    kn : Knew ns tab env ρi
    nd : distinct (tnames tab) ≡ true
    ls : Links tab
    sn : Ext (envOf pl) ρi
    at : At suf pl
    ens : EchoNs ns pl
    al : Align suf pl
    ix : n ≡ headIx pl
    ss : s ≡ slotOf pl
    pin : Covered suf [] ρi n s

open Sit

open-at : ∀ {x suf p} {pl : Place p} →
          At suf (p-mu x pl) →
          lookupI x (envOf pl) ≡ nothing × At (x ∷ suf) pl
open-at (at-mu miss atB) = miss , atB

open-ens : ∀ {ns x p} {pl : Place p} →
           EchoNs ns (p-mu x pl) → EchoNs ns pl
open-ens (en-mu e) = e

open-al : ∀ {x suf p} {pl : Place p} →
          Align suf (p-mu x pl) → Align (x ∷ suf) pl
open-al (al-mu a) = a

peel-sit : ∀ {tab x p} {pl : Place p} →
           (inn : InTab x (smu x p) tab) →
           place-of inn ≡ p-mu x pl →
           (st : Sit tab (p-mu x pl)) →
           lookupI x (envOf pl) ≡ nothing →
           At (x ∷ suf st) pl →
           EchoNs (ns st) pl →
           Align (x ∷ suf st) pl →
           Sit tab pl
peel-sit {x = x} {p = p} {pl = pl} inn peq st miss atB ensB alB =
  mkSit
    ((x , smu x p) ∷ env st)
    (x ∷ pend st)
    ((x , n st , s st) ∷ ρi st)
    (x ∷ suf st)
    (n st) (s st)
    (ns st)
    (td1 inn (td st))
    (sy1 inn ixE slE (sy st))
    kn′
    (nd st)
    (ls st)
    sn′
    atB
    ensB
    alB
    (ix st)
    (ss st)
    (cov-push {x = x} {suf = suf st} {ρ = ρi st} {n = n st} {s = s st} (pin st))
  where
  ixE : ix-of inn ≡ n st
  ixE = trans (ix-head (ls st) inn) (trans (cong headIx peq) (sym (ix st)))
  slE : slot-at inn ≡ s st
  slE = trans (slot-head (ls st) inn) (trans (cong slotOf peq) (sym (ss st)))
  sn′ = ext-front {x = x} {i = n st} {s = s st} {ρ0 = envOf pl} {ρ = ρi st}
          (sn st) (inj₁ miss)
  pinX = runtime-pin {x = x} {ρ = ρi st} {n = n st} {s = s st}
           inn ixE slE (nd st) (sy st)
  covX = cov-cons {x = x} {i = n st} {s = s st} {suf = suf st} {ρ = ρi st}
           {i0 = n st} {s0 = s st} (pin st) pinX
  kn′ = kn1 {i = n st} {s0 = s st} {suf = suf st} {pl = p-mu x pl}
          inn peq ixE slE (at st) (ens st) (al st) sn′ covX (kn st)

-- The entry a jump names, read in the environment the jump is standing in.
target-sit : ∀ {tab y Q i s ρ} →
             (m : InTab y Q tab) →
             lookupI y ρ ≡ just (i , s) →
             Sit tab (p-jump y i s ρ) →
             Sit tab (place-of m)
target-sit {y = y} {Q = Q} {i = i} {s = s} {ρ = ρ} m look st =
  mkSit
    (env st) (pend st) (ρi st)
    (Found.suf got)
    (Found.i got) (Found.s0 got)
    (ns st)
    (td st) (sy st) (kn st) (nd st) (ls st)
    snT atT ensT alT
    ixT ssT
    (Found.cov got)
  where
  hit = sn st y i s look
  b = sync-bound (sy st) hit m (nd st)
  got = kn-find (kn st) b (nd st)
  sm = same-slot m (Found.m got) (nd st)
  eqPl : place-of m ≡ Found.pl got
  eqPl = trans (same-place m (Found.m got) (nd st)) (Found.peq got)
  snT = subst (λ q → Ext (envOf q) (ρi st)) (sym eqPl) (Found.ext got)
  atT = subst (λ q → At (Found.suf got) q) (sym eqPl) (Found.at got)
  ensT = subst (λ q → EchoNs (ns st) q) (sym eqPl) (Found.ens got)
  alT = subst (λ q → Align (Found.suf got) q) (sym eqPl) (Found.al got)
  ixT : Found.i got ≡ headIx (place-of m)
  ixT = trans (trans (sym (Found.ix≡ got)) (sym (proj₁ sm)))
              (ix-head (ls st) m)
  ssT : Found.s0 got ≡ slotOf (place-of m)
  ssT = trans (trans (sym (Found.sl≡ got)) (sym (proj₂ sm)))
              (slot-head (ls st) m)

leaf-open : ∀ {P env pend} {pl : Place P} →
            Leaf pl → Opened env pend P
leaf-open lh-done = opened _ _ f-done u-done
leaf-open lh-stop = opened _ _ f-stop u-stop
leaf-open lh-put = opened _ _ (f-put _ _) u-put
leaf-open lh-echo = opened _ _ (f-put _ _) u-put
leaf-open lh-pick0 = opened _ _ (f-pick0 _) u-pick0
leaf-open lh-pick1 = opened _ _ (f-pick1 _) u-pick1
leaf-open lh-get = opened _ _ (f-get _ _ _) u-get
leaf-open lh-cover = opened _ _ (f-cover _ _) u-cover
leaf-open lh-iget = opened _ _ (f-iget _ _ _) u-iget
leaf-open lh-mget = opened _ _ (f-mget _ _ _) u-mget

chase : ∀ {tab P} {pl : Place P} →
        (hp : Hop tab pl) → (st : Sit tab pl) →
        Opened (env st) (pend st) P
chase (hop-mu {x = x} {p = p} inn peq sub) st =
  let miss , atB = open-at (at st)
      o = chase sub (peel-sit inn peq st miss atB (open-ens (ens st)) (open-al (al st)))
  in opened (ρ′ o) (pend′ o) (f o) (u-mu (unf o))
chase (hop-jump {y = y} {i = i} {s = s} m look sub) st =
  let o = chase sub (target-sit m look st)
      b = sync-bound (sy st) (sn st y i s look) m (nd st)
  in opened (ρ′ o) (pend′ o) (f o) (u-var b (unf o))
chase (hop-leaf lh) st = leaf-open {env = env st} {pend = pend st} lh

------------------------------------------------------------------------
-- The cursor is standing on a place. Its table witness names every
-- jump, and the environment it carries is the one the unfold starts from.
------------------------------------------------------------------------

sit-cursor : ∀ {bs proc} (idx slot : ℕ) (envP : EnvP) (envI : EnvI) →
             (lc : Cursor bs idx slot envP envI proc) →
             Sit (tab lc) (pl lc)
sit-cursor idx slot envP envI lc =
  mkSit envP [] envI [] idx slot
    (echoNs lc) (td lc) (sy lc) (kn lc) (nd lc) (ls lc)
    (sn lc) (at lc) (ens lc) (al lc) (ix lc) (ss lc)
    (cov-id {xs = []} {base = envI} {n = idx} {s = slot})

unfold-at : ∀ {bs proc} (idx slot : ℕ) (envP : EnvP) (envI : EnvI) →
            Cursor bs idx slot envP envI proc →
            Opened envP [] proc
unfold-at idx slot envP envI lc =
  let ht = table-hops (ts lc) (ls lc)
      hp = place-hop ht (lk lc) (hs lc) (sy lc) (sn lc) (nd lc)
  in chase hp (sit-cursor idx slot envP envI lc)

unfoldL : ∀ {g c} → Hold g c → Opened (envPL c) [] (left c)
unfoldL {c = c} h =
  unfold-at (il c) (slotL c) (envPL c) (envIL c) (leftC h)

unfoldR : ∀ {g c} → Hold g c → Opened (envPR c) [] (right c)
unfoldR {c = c} h =
  unfold-at (ir c) (slotR c) (envPR c) (envIR c) (rightC h)

------------------------------------------------------------------------
-- A compiled graph opens onto the source configuration it starts from.
-- The block a root action runs is the block `compile` allocated, and
-- its slot is the slot the source configuration starts in.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Run where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Muro.AsyncRec
  using ( Atom; Tok; Block; COut; cok; cfail; Fault
        ; Graph; gr; RConf; rc; materialise; alphabet; init
        ; compile; lookB; elemS )
open import Muro.AsyncRec using (module Graph)
open Graph

open import Muro.Temporal.Bridge
  using ( Frag; echoOk; muOk; mus; distinct; fresh; ∧-left; ∧-right
        ; graphOf; initS; pack; compiled; gok; gfail; elab )
open import Muro.Temporal.Source
  using ( SProc; SConf; sc; W; mkW; EnvI; EnvP; addPend; lookupI
        ; walk; walkArms
        ; sdone; sstop; sout; sput; sget; spick0; spick1
        ; scover; siget; smget; smu; svar
        ; Arm; aok; abad
        ; bnames; abs
        ; Bound; b-here; b-there )
open SConf
open W

open import Muro.Temporal.Pic
  using (Ord; ERel; er0; EchoRel; echo-empty; EnvEq; outside; ==-refl; ==-sound
        ; true≢false)
open import Muro.Temporal.Agree using (root-ns)
open import Muro.Temporal.Den
  using ( Place; Table; t0; t1; Link; Links; CovP; CovT; headIx; slotOf; envOf
        ; InTab; in-here; in-there; Hosts; At
        ; place-of; link-of; ix-of; slot-at; tnames )
open import Muro.Temporal.Denote
  using ( denote; Yes; No; noB; Built; ok; bad )

nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

cfail≢cok : ∀ {f e n s bs} → cfail f ≡ cok e n s bs → ⊥
cfail≢cok ()

cok-inj : ∀ {e n s bs e′ n′ s′ bs′} →
          cok e n s bs ≡ cok e′ n′ s′ bs′ →
          e ≡ e′ × n ≡ n′ × s ≡ s′ × bs ≡ bs′
cok-inj refl = refl , refl , refl , refl

------------------------------------------------------------------------
-- The counters of a walk that starts at slot zero, in an empty
-- environment, are that slot. A jump has nothing to look up.
------------------------------------------------------------------------

-- A jump from an empty environment has nothing to look up.
svar-empty : ∀ pend y n s → walk pend [] (svar y) n s ≡ nothing
svar-empty pend y n s = go (elemS y pend) refl
  where
  go : (b : Bool) → elemS y pend ≡ b → walk pend [] (svar y) n s ≡ nothing
  go true eq rewrite eq = refl
  go false eq rewrite eq = refl

atSlot0 : ∀ pend P w → walk pend [] P zero zero ≡ just w → atSlot w ≡ zero
atSlot0 pend (smu x p) w eq = atSlot0 (x ∷ pend) p w eq
atSlot0 pend (svar y) w eq =
  ⊥-elim (nothing≢just (trans (sym (svar-empty pend y zero zero)) eq))
atSlot0 pend sdone w refl = refl
atSlot0 pend sstop w refl = refl
atSlot0 pend sout w eq = ⊥-elim (nothing≢just eq)
atSlot0 pend (sput a p) w eq with walk [] (addPend pend zero zero []) p (suc zero) zero
... | nothing = ⊥-elim (nothing≢just eq)
... | just wb with eq
... | refl = refl
atSlot0 pend (sget t x p) w eq with walk [] (addPend pend zero zero []) p (suc zero) (suc zero)
... | nothing = ⊥-elim (nothing≢just eq)
... | just wb with eq
... | refl = refl
atSlot0 pend (spick0 p) w eq with walk [] (addPend pend zero zero []) p (suc zero) zero
... | nothing = ⊥-elim (nothing≢just eq)
... | just wb with eq
... | refl = refl
atSlot0 pend (spick1 p) w eq with walk [] (addPend pend zero zero []) p (suc zero) zero
... | nothing = ⊥-elim (nothing≢just eq)
... | just wb with eq
... | refl = refl
atSlot0 pend (scover p q) w eq with walk [] (addPend pend zero zero []) p (suc zero) zero
... | nothing = ⊥-elim (nothing≢just eq)
... | just w1 with walk [] (addPend pend zero zero []) q (next w1) (slotN w1)
... | nothing = ⊥-elim (nothing≢just eq)
... | just w2 with eq
... | refl = refl
atSlot0 pend (siget x p q) w eq with walk [] (addPend pend zero zero []) p (suc zero) (suc zero)
... | nothing = ⊥-elim (nothing≢just eq)
... | just w1 with walk [] (addPend pend zero zero []) q (next w1) (slotN w1)
... | nothing = ⊥-elim (nothing≢just eq)
... | just w2 with eq
... | refl = refl
atSlot0 pend (smget t x as) w eq with walkArms [] (addPend pend zero zero []) as (suc zero) (suc zero)
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with eq
... | refl = refl

------------------------------------------------------------------------
-- A name the denoted environment binds is bound the same way at run
-- time. The table holds the place each recursion binder denotes.
------------------------------------------------------------------------

-- Transport along an environment equality. The proof is reflexivity
-- after `refl`, so `lookupI` is not asked to unify a concrete `[]`.
env-cast : ∀ {ρ0 ρ1} → ρ0 ≡ ρ1 → EnvEq ρ0 ρ1
env-cast {ρ0} refl _ = refl

data Tied : Table → EnvP → Set where
  td0 : ∀ {tab} → Tied tab []
  td1 : ∀ {x P tab ρ} → InTab x P tab → Tied tab ρ →
        Tied tab ((x , P) ∷ ρ)

-- The process environment and the index environment name the same
-- binders, and each index is the table entry's index.
data Sync : Table → EnvP → EnvI → Set where
  sy0 : ∀ {tab} → Sync tab [] []
  sy1 : ∀ {tab x P i s env ρ} (m : InTab x P tab) →
        ix-of m ≡ i → slot-at m ≡ s → Sync tab env ρ →
        Sync tab ((x , P) ∷ env) ((x , i , s) ∷ ρ)

resolve : ∀ {x P tab env} → Tied tab env → Bound x P env → InTab x P tab
resolve (td1 inn _) b-here = inn
resolve (td1 _ rest) (b-there b) = resolve rest b
resolve td0 ()

-- A runtime environment may bind names the denoted one does not.
-- Every name the denoted environment does bind is bound the same way.
Ext : EnvI → EnvI → Set
Ext ρ0 ρ = ∀ x i s → lookupI x ρ0 ≡ just (i , s) → lookupI x ρ ≡ just (i , s)

ext-eq : ∀ {ρ0 ρ} → EnvEq ρ0 ρ → Ext ρ0 ρ
ext-eq eq x i s p = trans (sym (eq x)) p

ext-refl : ∀ ρ → Ext ρ ρ
ext-refl ρ x i s eq = eq

-- Names unfolded in one step are new, or already bound at these counters.
Fresh : List String → EnvI → ℕ → ℕ → Set
Fresh got ρ n s =
  ∀ y → elemS y got ≡ true →
        lookupI y ρ ≡ nothing ⊎ lookupI y ρ ≡ just (n , s)

-- A denoted pending name is either unfolded now or already bound here.
Covered : List String → List String → EnvI → ℕ → ℕ → Set
Covered suf got base n s =
  ∀ y → elemS y suf ≡ true →
        elemS y got ≡ true ⊎ lookupI y base ≡ just (n , s)

fr-nil : ∀ {ρ n s} → Fresh [] ρ n s
fr-nil _ ()

cov-nil : ∀ {got base n s} → Covered [] got base n s
cov-nil _ ()

-- What a step has already learned about each binder in scope.
-- The denoted place, its pending names, and the counters are the table's.
data Knew (tab : Table) : EnvP → EnvI → Set where
  kn0 : Knew tab [] []
  kn1 : ∀ {x P env ρ i s0 suf} {pl : Place P} →
        (m : InTab x P tab) →
        place-of m ≡ pl →
        ix-of m ≡ i →
        slot-at m ≡ s0 →
        At suf pl →
        Ext (envOf pl) ((x , i , s0) ∷ ρ) →
        Covered suf [] ((x , i , s0) ∷ ρ) i s0 →
        Knew tab env ρ →
        Knew tab ((x , P) ∷ env) ((x , i , s0) ∷ ρ)

kn-tied : ∀ {tab env ρ} → Knew tab env ρ → Tied tab env
kn-tied kn0 = td0
kn-tied (kn1 m _ _ _ _ _ _ k) = td1 m (kn-tied k)

record Cursor (bs : List (ℕ × Block)) (idx slot : ℕ)
              (envP : EnvP) (envI : EnvI) (proc : SProc) : Set where
  field
    pl : Place proc
    cv : CovP pl bs
    tab : Table
    ct : CovT tab bs
    lk : Link pl
    ls : Links tab
    hs : Hosts tab pl
    td : Tied tab envP
    sy : Sync tab envP envI
    kn : Knew tab envP envI
    ix : idx ≡ headIx pl
    ss : slot ≡ slotOf pl
    sn : Ext (envOf pl) envI
    at : At [] pl
    nd : distinct (tnames tab) ≡ true

record Hold (g : Graph) (c : SConf) : Set where
  field
    nL : ℕ
    bsL : List (ℕ × Block)
    odL : Ord zero nL bsL
    cL : Graph.codeL g ≡ materialise nL zero bsL
    nR : ℕ
    bsR : List (ℕ × Block)
    odR : Ord zero nR bsR
    cR : Graph.codeR g ≡ materialise nR zero bsR
    α : SConf.alpha c ≡ Graph.alpha g
    κ : SConf.cap c ≡ Graph.cap g
    leftC : Cursor bsL (il c) (slotL c) (envPL c) (envIL c) (left c)
    rightC : Cursor bsR (ir c) (slotR c) (envPR c) (envIR c) (right c)

gfail≢gok : ∀ {f g} → gfail f ≡ gok g → ⊥
gfail≢gok ()

ev-nil : ∀ {R fr} (y : Yes R fr [] [] [] [] zero zero) →
         envOf (Yes.pl y) ≡ []
ev-nil y = Yes.ev y

root-sn : ∀ {R fr} (y : Yes R fr [] [] [] [] zero zero) →
          EnvEq (envOf (Yes.pl y)) []
root-sn y = env-cast (ev-nil y)

------------------------------------------------------------------------
-- Both sides denoted under the root echo hypothesis. The packed graph
-- is the one `graphOf` returns, and the packed configuration is the
-- one `initS` returns. Its cursors are those denotations.
------------------------------------------------------------------------

init-hold : ∀ k (P Q : SProc) (fp : Frag P) (fq : Frag Q) →
            echoOk (bnames P) [] P ≡ true →
            echoOk (bnames Q) [] Q ≡ true →
            muOk P ≡ true →
            muOk Q ≡ true →
            ∀ g c →
            graphOf k P Q fp fq ≡ gok g →
            initS k P Q fp fq ≡ just c →
            Hold g c
init-hold k P Q fp fq eokP eokQ muP muQ g c eqg eqc =
  body (denote P fp [] [] [] [] (bnames P) [] [] [] zero zero
          er0 (echo-empty [] (bnames P)) eokP refl (root-ns P) muP)
       (denote Q fq [] [] [] [] (bnames Q) [] [] [] zero zero
          er0 (echo-empty [] (bnames Q)) eokQ refl (root-ns Q) muQ)
  where
  -- `compiled` does not unfold while a pattern is unified, so the
  -- output is an argument and the equality is matched as `refl`.
  lost : ∀ {f} (oL : COut) → oL ≡ cfail f → (oR : COut) →
         proj₁ (pack k P Q oL oR) ≡ gok g → ⊥
  lost (cfail _) refl _ p = gfail≢gok p
  lost (cok _ _ _ _) () _ _

  lostR : ∀ {f} (oL oR : COut) → oR ≡ cfail f →
          proj₁ (pack k P Q oL oR) ≡ gok g → ⊥
  lostR (cfail _) (cfail _) refl p = gfail≢gok p
  lostR (cok _ _ _ _) (cfail _) refl p = gfail≢gok p
  lostR _ (cok _ _ _ _) () _

  od-cast : ∀ {a b xs ys} → a ≡ b → xs ≡ ys → Ord zero a xs → Ord zero b ys
  od-cast refl refl od = od

  covP-cast : ∀ {R} {pl : Place R} {xs ys} → xs ≡ ys → CovP pl xs → CovP pl ys
  covP-cast refl cv = cv

  ct-cast : ∀ {tab xs ys} → xs ≡ ys → CovT tab xs → CovT tab ys
  ct-cast refl ct = ct

  nd-cast : ∀ {xs ys} → xs ≡ ys → distinct ys ≡ true → distinct xs ≡ true
  nd-cast refl eq = eq

  cursor : ∀ {R fr bs} (y : Yes R fr [] [] [] [] zero zero) →
           Yes.bs y ≡ bs →
           ∀ idx → idx ≡ entry (Yes.w y) →
           atSlot (Yes.w y) ≡ zero →
           distinct (mus R) ≡ true →
           Cursor bs idx zero [] [] R
  cursor y bs≡ idx ix≡ slot0 mu =
    record
      { pl = Yes.pl y
      ; cv = covP-cast bs≡ (Yes.cv y)
      ; tab = Yes.tab y
      ; ct = ct-cast bs≡ (Yes.ct y)
      ; lk = Yes.lk y
      ; ls = Yes.ls y
      ; hs = Yes.hs y
      ; td = td0
      ; sy = sy0
      ; kn = kn0
      ; ix = trans ix≡ (sym (Yes.hd y))
      ; ss = sym (trans (Yes.sl y) slot0)
      ; sn = ext-eq {ρ0 = envOf (Yes.pl y)} {ρ = []} (root-sn y)
      ; at = Yes.at y
      ; nd = nd-cast (Yes.tn y) mu
      }

  open-pack : (yL : Yes P fp [] [] [] [] zero zero)
              (yR : Yes Q fq [] [] [] [] zero zero)
              (oL oR : COut) →
              oL ≡ cok (entry (Yes.w yL)) (next (Yes.w yL))
                       (slotN (Yes.w yL)) (Yes.bs yL) →
              oR ≡ cok (entry (Yes.w yR)) (next (Yes.w yR))
                       (slotN (Yes.w yR)) (Yes.bs yR) →
              proj₁ (pack k P Q oL oR) ≡ gok g →
              proj₂ (pack k P Q oL oR) ≡ just c →
              Hold g c
  open-pack yL yR (cok eL nL sL bsL) (cok eR nR sR bsR) eqL eqR refl refl =
    let eL≡ , nL≡ , _ , bsL≡ = cok-inj eqL
        eR≡ , nR≡ , _ , bsR≡ = cok-inj eqR
    in record
      { nL = nL
      ; bsL = bsL
      ; odL = od-cast (sym nL≡) (sym bsL≡) (Yes.od yL)
      ; cL = refl
      ; nR = nR
      ; bsR = bsR
      ; odR = od-cast (sym nR≡) (sym bsR≡) (Yes.od yR)
      ; cR = refl
      ; α = refl
      ; κ = refl
      ; leftC = cursor yL (sym bsL≡) eL eL≡
                  (atSlot0 [] P (Yes.w yL) (Yes.wk yL)) muP
      ; rightC = cursor yR (sym bsR≡) eR eR≡
                   (atSlot0 [] Q (Yes.w yR) (Yes.wk yR)) muQ
      }
  open-pack _ _ (cfail _) _ () _ _ _
  open-pack _ _ (cok _ _ _ _) (cfail _) _ () _ _

  body : Built P fp [] [] [] [] zero zero →
         Built Q fq [] [] [] [] zero zero →
         Hold g c
  body (bad (noB _ _ cmp)) _ =
    ⊥-elim (lost (compiled P fp) cmp (compiled Q fq) eqg)
  body (ok _) (bad (noB _ _ cmp)) =
    ⊥-elim (lostR (compiled P fp) (compiled Q fq) cmp eqg)
  body (ok yL) (ok yR) =
    open-pack yL yR (compiled P fp) (compiled Q fq)
      (Yes.cmp yL) (Yes.cmp yR) eqg eqc

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

lookup-skip : ∀ {y x i s ρ} → (y == x) ≡ false →
              lookupI y ((x , i , s) ∷ ρ) ≡ lookupI y ρ
lookup-skip eq rewrite eq = refl

-- Pushing the same names keeps the hits that were already there.
ext-add : ∀ xs n s ρ0 ρ → Ext ρ0 ρ →
          Ext (addPend xs n s ρ0) (addPend xs n s ρ)
ext-add [] n s ρ0 ρ ext = ext
ext-add (x ∷ xs) n s ρ0 ρ ext y i s1 eq = go (y == x) refl eq
  where
  go : (b : Bool) → (y == x) ≡ b →
       lookupI y ((x , n , s) ∷ addPend xs n s ρ0) ≡ just (i , s1) →
       lookupI y ((x , n , s) ∷ addPend xs n s ρ) ≡ just (i , s1)
  go true eqy eq2 rewrite eqy | just-inj eq2 = refl
  go false eqy eq2 =
    trans (lookup-skip eqy)
      (ext-add xs n s ρ0 ρ ext y i s1 (trans (sym (lookup-skip eqy)) eq2))

-- A name in the pending list is bound at the counters `addPend` writes.
lookup-in : ∀ xs n s ρ y → elemS y xs ≡ true →
            lookupI y (addPend xs n s ρ) ≡ just (n , s)
lookup-in [] n s ρ y ()
lookup-in (x ∷ xs) n s ρ y eq = go (y == x) refl eq
  where
  go : (b : Bool) → (y == x) ≡ b → elemS y (x ∷ xs) ≡ true →
       lookupI y ((x , n , s) ∷ addPend xs n s ρ) ≡ just (n , s)
  go true eqy _ rewrite eqy = refl
  go false eqy eq2 rewrite eqy = lookup-in xs n s ρ y eq2

-- `Fresh` and `Covered` are defined with `Knew`, above.

elem-yes : ∀ {y x xs} → (y == x) ≡ true → elemS y (x ∷ xs) ≡ true
elem-yes eq rewrite eq = refl

elem-cons : ∀ {y x xs} → elemS y xs ≡ true → elemS y (x ∷ xs) ≡ true
elem-cons {y} {x} {xs} eq = go (y == x) refl
  where
  go : (b : Bool) → (y == x) ≡ b → elemS y (x ∷ xs) ≡ true
  go true eqy rewrite eqy = refl
  go false eqy rewrite eqy = eq

elem-tail : ∀ {y x xs} → (y == x) ≡ false →
            elemS y (x ∷ xs) ≡ true → elemS y xs ≡ true
elem-tail {y} {x} eq p with y == x
... | false = p
... | true = ⊥-elim (true≢false eq)

ext-trans : ∀ {ρ1 ρ2 ρ3} → Ext ρ1 ρ2 → Ext ρ2 ρ3 → Ext ρ1 ρ3
ext-trans a b x i s p = b x i s (a x i s p)

ext-miss : ∀ {y ρ dom} → Ext ρ dom →
           lookupI y dom ≡ nothing → lookupI y ρ ≡ nothing
ext-miss {y} {ρ} ext eq = go (lookupI y ρ) refl
  where
  go : (m : Maybe (ℕ × ℕ)) → lookupI y ρ ≡ m → lookupI y ρ ≡ nothing
  go nothing p = p
  go (just (i , s)) p = ⊥-elim (nothing≢just (trans (sym eq) (ext y i s p)))

pin-use : ∀ {y ρ n s i s1} →
          lookupI y ρ ≡ nothing ⊎ lookupI y ρ ≡ just (n , s) →
          lookupI y ρ ≡ just (i , s1) →
          (n , s) ≡ (i , s1)
pin-use (inj₁ no) eq = ⊥-elim (nothing≢just (trans (sym no) eq))
pin-use (inj₂ yes) eq = just-inj (trans (sym yes) eq)

bind-hit : ∀ got n s base y →
           elemS y got ≡ true ⊎ lookupI y base ≡ just (n , s) →
           lookupI y (addPend got n s base) ≡ just (n , s)
bind-hit got n s base y (inj₁ inn) = lookup-in got n s base y inn
bind-hit got n s base y (inj₂ eq) = go (elemS y got) refl
  where
  go : (b : Bool) → elemS y got ≡ b →
       lookupI y (addPend got n s base) ≡ just (n , s)
  go true inn = lookup-in got n s base y inn
  go false out = trans (sym (outside got n s base y out)) eq

grow-hit : ∀ y x got n s base i s1 →
           (y == x) ≡ true →
           (n , s) ≡ (i , s1) →
           lookupI y ((x , n , s) ∷ addPend got n s base) ≡ just (i , s1)
grow-hit y x got n s base i s1 eqy e rewrite eqy | e = refl

fresh-tail : ∀ {x got ρ n s} →
             (∀ y → elemS y (x ∷ got) ≡ true →
                    lookupI y ρ ≡ nothing ⊎ lookupI y ρ ≡ just (n , s)) →
             Fresh got ρ n s
fresh-tail {x} fr y inn = fr y (elem-cons {y} {x} inn)

-- Adding runtime names keeps a denoted hit when those names do not
-- shadow it at different counters.
ext-grow : ∀ got n s ρ base → Ext ρ base → Fresh got ρ n s →
           Ext ρ (addPend got n s base)
ext-grow [] n s ρ base ext fr = ext
ext-grow (x ∷ got) n s ρ base ext fr y i s1 eq = go (y == x) refl
  where
  go : (b : Bool) → (y == x) ≡ b →
       lookupI y (addPend (x ∷ got) n s base) ≡ just (i , s1)
  go true eqy =
    grow-hit y x got n s base i s1 eqy
      (pin-use {y = y} {ρ = ρ} {n = n} {s = s} {i = i} {s1 = s1}
         (fr y (elem-yes {y = y} {x = x} {xs = got} eqy)) eq)
  go false eqy =
    trans (lookup-skip eqy)
      (ext-grow got n s ρ base ext
         (fresh-tail {x = x} {got = got} {ρ = ρ} {n = n} {s = s} fr)
         y i s1 eq)

cov-tail : ∀ {x suf got base n s} →
           Covered (x ∷ suf) got base n s → Covered suf got base n s
cov-tail {x} cov y inn = cov y (elem-cons {y} {x} inn)

head-pin : ∀ {y x suf n s ρ i s1} →
           (y == x) ≡ true →
           lookupI y ((x , n , s) ∷ addPend suf n s ρ) ≡ just (i , s1) →
           (n , s) ≡ (i , s1)
head-pin eqy eq rewrite eqy = just-inj eq

both-hit : ∀ y got n s base i s1 →
           (n , s) ≡ (i , s1) →
           elemS y got ≡ true ⊎ lookupI y base ≡ just (n , s) →
           lookupI y (addPend got n s base) ≡ just (i , s1)
both-hit y got n s base i s1 e mem rewrite sym e = bind-hit got n s base y mem

fresh-lift : ∀ {got ρ dom n s} →
             Ext ρ dom → Fresh got dom n s → Fresh got ρ n s
fresh-lift {got} {ρ} {dom} {n} {s} ext fr y inn = go (lookupI y ρ) refl
  where
  go : (m : Maybe (ℕ × ℕ)) → lookupI y ρ ≡ m →
       lookupI y ρ ≡ nothing ⊎ lookupI y ρ ≡ just (n , s)
  go nothing p = inj₁ p
  go (just (i , s1)) p = inj₂ (same (fr y inn) (ext y i s1 p) p)
    where
    same : lookupI y dom ≡ nothing ⊎ lookupI y dom ≡ just (n , s) →
           lookupI y dom ≡ just (i , s1) →
           lookupI y ρ ≡ just (i , s1) →
           lookupI y ρ ≡ just (n , s)
    same (inj₁ no) hit _ = ⊥-elim (nothing≢just (trans (sym no) hit))
    same (inj₂ yes) hit q rewrite sym (just-inj (trans (sym yes) hit)) = q

cov-mu : ∀ {x suf got base n s} →
         Covered suf got base n s →
         Covered (x ∷ suf) (x ∷ got) base n s
cov-mu {x} {suf} {got} {base} {n} {s} cov y inn = go (y == x) refl inn
  where
  go : (b : Bool) → (y == x) ≡ b → elemS y (x ∷ suf) ≡ true →
       elemS y (x ∷ got) ≡ true ⊎ lookupI y base ≡ just (n , s)
  go true eqy _ rewrite eqy = inj₁ refl
  go false eqy inn′ rewrite eqy = cov y inn′

fresh-mu : ∀ {x got ρ n s} →
           lookupI x ρ ≡ nothing ⊎ lookupI x ρ ≡ just (n , s) →
           Fresh got ρ n s → Fresh (x ∷ got) ρ n s
fresh-mu {x} {got} {ρ} {n} {s} pin fr y inn = go (y == x) refl
  where
  go : (b : Bool) → (y == x) ≡ b →
       lookupI y ρ ≡ nothing ⊎ lookupI y ρ ≡ just (n , s)
  go true eqy rewrite ==-sound eqy = pin
  go false eqy rewrite eqy = fr y inn

-- `suf` is the pending list the action was denoted under. `got` is the
-- pending list the source step unfolded. The two lists share counters.
ext-both : ∀ suf got n s ρ base →
           Ext ρ base →
           Covered suf got base n s →
           Fresh got ρ n s →
           Ext (addPend suf n s ρ) (addPend got n s base)
ext-both [] got n s ρ base ext cov fr = ext-grow got n s ρ base ext fr
ext-both (x ∷ suf) got n s ρ base ext cov fr y i s1 eq = step (y == x) refl eq
  where
  step : (b : Bool) → (y == x) ≡ b →
         lookupI y (addPend (x ∷ suf) n s ρ) ≡ just (i , s1) →
         lookupI y (addPend got n s base) ≡ just (i , s1)
  step true eqy eq2 =
    both-hit y got n s base i s1
      (head-pin {y = y} {x = x} {suf = suf} {n = n} {s = s} {ρ = ρ}
         {i = i} {s1 = s1} eqy eq2)
      (cov y (elem-yes {y = y} {x = x} {xs = suf} eqy))
  step false eqy eq2 =
    ext-both suf got n s ρ base ext
      (cov-tail {x = x} {suf = suf} {got = got} {base = base} {n = n} {s = s} cov)
      fr y i s1
      (trans (sym (lookup-skip eqy)) eq2)

-- The denoted pending names are already bound in the runtime this step
-- unfolded into. Binding them on the denoted side does not move a hit.
ext-pend : ∀ suf got n s ρ base →
           Ext ρ (addPend got n s base) →
           Covered suf got base n s →
           Ext (addPend suf n s ρ) (addPend got n s base)
ext-pend [] got n s ρ base ext cov = ext
ext-pend (x ∷ suf) got n s ρ base ext cov y i s1 eq = step (y == x) refl eq
  where
  step : (b : Bool) → (y == x) ≡ b →
         lookupI y (addPend (x ∷ suf) n s ρ) ≡ just (i , s1) →
         lookupI y (addPend got n s base) ≡ just (i , s1)
  step true eqy eq2 =
    both-hit y got n s base i s1
      (head-pin {y = y} {x = x} {suf = suf} {n = n} {s = s} {ρ = ρ}
         {i = i} {s1 = s1} eqy eq2)
      (cov y (elem-yes {y = y} {x = x} {xs = suf} eqy))
  step false eqy eq2 =
    ext-pend suf got n s ρ base ext
      (cov-tail {x = x} {suf = suf} {got = got} {base = base} {n = n} {s = s} cov)
      y i s1
      (trans (sym (lookup-skip eqy)) eq2)

cov-id : ∀ {xs base n s} → Covered xs xs base n s
cov-id y inn = inj₁ inn

cov-cast : ∀ {suf got base i s n s′} →
           i ≡ n → s ≡ s′ →
           Covered suf got base i s → Covered suf got base n s′
cov-cast refl refl cov = cov

-- A lookup past `addPend` is either one of the peeled names or a hit
-- that was already in the base environment.
split-add : ∀ pend n s base y i s1 →
            lookupI y (addPend pend n s base) ≡ just (i , s1) →
            elemS y pend ≡ true ⊎ lookupI y base ≡ just (i , s1)
split-add pend n s base y i s1 eq = go (elemS y pend) refl
  where
  go : (b : Bool) → elemS y pend ≡ b →
       elemS y pend ≡ true ⊎ lookupI y base ≡ just (i , s1)
  go true p = inj₁ p
  go false p = inj₂ (trans (outside pend n s base y p) eq)

-- Names covered in the extended runtime are covered by the peeled
-- prefix or by the environment the step started from.
cov-pull : ∀ {suf pend base n s} →
           Covered suf [] (addPend pend n s base) n s →
           Covered suf pend base n s
cov-pull {pend = pend} {base = base} {n = n} {s = s} cov y inn =
  body (cov y inn)
  where
  body : elemS y [] ≡ true ⊎
         lookupI y (addPend pend n s base) ≡ just (n , s) →
         elemS y pend ≡ true ⊎ lookupI y base ≡ just (n , s)
  body (inj₁ ())
  body (inj₂ eq) = split-add pend n s base y n s eq

-- Peeling `x` at these counters covers `x` and keeps the old names.
cov-push : ∀ {x suf ρ n s} →
           Covered suf [] ρ n s →
           Covered (x ∷ suf) [] ((x , n , s) ∷ ρ) n s
cov-push {x = x} {suf = suf} {ρ = ρ} {n = n} {s = s} cov y inn =
  go (y == x) refl
  where
  front : (y == x) ≡ true →
          lookupI y ((x , n , s) ∷ ρ) ≡ just (n , s)
  front eqy rewrite eqy = refl
  keep : (y == x) ≡ false →
         lookupI y ρ ≡ just (n , s) →
         lookupI y ((x , n , s) ∷ ρ) ≡ just (n , s)
  keep eqy eq rewrite eqy = eq
  old : (y == x) ≡ false → lookupI y ρ ≡ just (n , s)
  old eqy = hit (cov y (elem-tail {y = y} {x = x} {xs = suf} eqy inn))
    where
    hit : elemS y [] ≡ true ⊎ lookupI y ρ ≡ just (n , s) →
          lookupI y ρ ≡ just (n , s)
    hit (inj₁ ())
    hit (inj₂ eq) = eq
  go : (b : Bool) → (y == x) ≡ b →
       elemS y [] ≡ true ⊎ lookupI y ((x , n , s) ∷ ρ) ≡ just (n , s)
  go true eqy = inj₂ (front eqy)
  go false eqy = inj₂ (keep eqy (old eqy))

------------------------------------------------------------------------
-- `walk` returns the same continuation when every denoted hit agrees.
------------------------------------------------------------------------

var-ung : ∀ {pend ρ y n s w} →
         elemS y pend ≡ true →
         walk pend ρ (svar y) n s ≡ just w → ⊥
var-ung eqe eq rewrite eqe = nothing≢just eq

var-miss : ∀ {pend ρ y n s w} →
           elemS y pend ≡ false →
           lookupI y ρ ≡ nothing →
           walk pend ρ (svar y) n s ≡ just w → ⊥
var-miss eqe eql eq rewrite eqe | eql = nothing≢just eq

var-w : ∀ pend ρ y n s i s0 w →
        elemS y pend ≡ false →
        lookupI y ρ ≡ just (i , s0) →
        walk pend ρ (svar y) n s ≡ just w →
        w ≡ mkW i s0 n s
var-w pend ρ y n s i s0 w eqe eql eq rewrite eqe | eql = sym (just-inj eq)

var-hit : ∀ pend ρ y n s w →
          walk pend ρ (svar y) n s ≡ just w →
          Σ ℕ (λ i → Σ ℕ (λ s0 →
            elemS y pend ≡ false × lookupI y ρ ≡ just (i , s0) ×
            w ≡ mkW i s0 n s))
var-hit pend ρ y n s w eq = go (elemS y pend) refl
  where
  go : (b : Bool) → elemS y pend ≡ b →
       Σ ℕ (λ i → Σ ℕ (λ s0 →
         elemS y pend ≡ false × lookupI y ρ ≡ just (i , s0) ×
         w ≡ mkW i s0 n s))
  go true eqe = ⊥-elim (var-ung {pend} {ρ} {y} {n} {s} {w} eqe eq)
  go false eqe = go2 (lookupI y ρ) refl
    where
    go2 : (m : Maybe (ℕ × ℕ)) → lookupI y ρ ≡ m →
          Σ ℕ (λ i → Σ ℕ (λ s0 →
            elemS y pend ≡ false × lookupI y ρ ≡ just (i , s0) ×
            w ≡ mkW i s0 n s))
    go2 nothing eql = ⊥-elim (var-miss {pend} {ρ} {y} {n} {s} {w} eqe eql eq)
    go2 (just (i , s0)) eql =
      i , s0 , eqe , eql , var-w pend ρ y n s i s0 w eqe eql eq

var-ext : ∀ pend ρ0 ρ y n s w → Ext ρ0 ρ →
          walk pend ρ0 (svar y) n s ≡ just w →
          walk pend ρ (svar y) n s ≡ just w
var-ext pend ρ0 ρ y n s w ext eq
  with var-hit pend ρ0 y n s w eq
... | i , s0 , eqe , eql , w≡ = same eqe eql (ext y i s0 eql) w≡
  where
  same : elemS y pend ≡ false →
         lookupI y ρ0 ≡ just (i , s0) →
         lookupI y ρ ≡ just (i , s0) →
         w ≡ mkW i s0 n s →
         walk pend ρ (svar y) n s ≡ just w
  same eqe eql eql' w≡ rewrite eqe | eql | eql' | w≡ = refl

sput-shape : ∀ {pend ρ a p n s wb w} →
             walk [] (addPend pend n s ρ) p (suc n) s ≡ just wb →
             walk pend ρ (sput a p) n s ≡ just w →
             w ≡ mkW n s (next wb) (slotN wb)
sput-shape eqb eq rewrite eqb = sym (just-inj eq)

sput-move : ∀ {pend ρ a p n s wb} →
            walk [] (addPend pend n s ρ) p (suc n) s ≡ just wb →
            walk pend ρ (sput a p) n s ≡ just (mkW n s (next wb) (slotN wb))
sput-move eq rewrite eq = refl

sget-shape : ∀ {pend ρ t x p n s wb w} →
             walk [] (addPend pend n s ρ) p (suc n) (suc s) ≡ just wb →
             walk pend ρ (sget t x p) n s ≡ just w →
             w ≡ mkW n s (next wb) (slotN wb)
sget-shape eqb eq rewrite eqb = sym (just-inj eq)

sget-move : ∀ {pend ρ t x p n s wb} →
            walk [] (addPend pend n s ρ) p (suc n) (suc s) ≡ just wb →
            walk pend ρ (sget t x p) n s ≡ just (mkW n s (next wb) (slotN wb))
sget-move eq rewrite eq = refl

spick-shape : ∀ {pend ρ p n s wb w} →
              walk [] (addPend pend n s ρ) p (suc n) s ≡ just wb →
              walk pend ρ (spick0 p) n s ≡ just w →
              w ≡ mkW n s (next wb) (slotN wb)
spick-shape eqb eq rewrite eqb = sym (just-inj eq)

spick0-move : ∀ {pend ρ p n s wb} →
              walk [] (addPend pend n s ρ) p (suc n) s ≡ just wb →
              walk pend ρ (spick0 p) n s ≡ just (mkW n s (next wb) (slotN wb))
spick0-move eq rewrite eq = refl

spick1-shape : ∀ {pend ρ p n s wb w} →
               walk [] (addPend pend n s ρ) p (suc n) s ≡ just wb →
               walk pend ρ (spick1 p) n s ≡ just w →
               w ≡ mkW n s (next wb) (slotN wb)
spick1-shape eqb eq rewrite eqb = sym (just-inj eq)

spick1-move : ∀ {pend ρ p n s wb} →
              walk [] (addPend pend n s ρ) p (suc n) s ≡ just wb →
              walk pend ρ (spick1 p) n s ≡ just (mkW n s (next wb) (slotN wb))
spick1-move eq rewrite eq = refl

scover-shape : ∀ {pend ρ p q n s w1 w2 w} →
               walk [] (addPend pend n s ρ) p (suc n) s ≡ just w1 →
               walk [] (addPend pend n s ρ) q (next w1) (slotN w1) ≡ just w2 →
               walk pend ρ (scover p q) n s ≡ just w →
               w ≡ mkW n s (next w2) (slotN w2)
scover-shape eq1 eq2 eq rewrite eq1 | eq2 = sym (just-inj eq)

scover-move : ∀ {pend ρ p q n s w1 w2} →
              walk [] (addPend pend n s ρ) p (suc n) s ≡ just w1 →
              walk [] (addPend pend n s ρ) q (next w1) (slotN w1) ≡ just w2 →
              walk pend ρ (scover p q) n s ≡ just (mkW n s (next w2) (slotN w2))
scover-move eq1 eq2 rewrite eq1 | eq2 = refl

siget-shape : ∀ {pend ρ x p q n s w1 w2 w} →
              walk [] (addPend pend n s ρ) p (suc n) (suc s) ≡ just w1 →
              walk [] (addPend pend n s ρ) q (next w1) (slotN w1) ≡ just w2 →
              walk pend ρ (siget x p q) n s ≡ just w →
              w ≡ mkW n s (next w2) (slotN w2)
siget-shape eq1 eq2 eq rewrite eq1 | eq2 = sym (just-inj eq)

siget-move : ∀ {pend ρ x p q n s w1 w2} →
             walk [] (addPend pend n s ρ) p (suc n) (suc s) ≡ just w1 →
             walk [] (addPend pend n s ρ) q (next w1) (slotN w1) ≡ just w2 →
             walk pend ρ (siget x p q) n s ≡ just (mkW n s (next w2) (slotN w2))
siget-move eq1 eq2 rewrite eq1 | eq2 = refl

smget-shape : ∀ {pend ρ t x as n s ws n2 s2 w} →
              walkArms [] (addPend pend n s ρ) as (suc n) (suc s) ≡ just (ws , n2 , s2) →
              walk pend ρ (smget t x as) n s ≡ just w →
              w ≡ mkW n s n2 s2
smget-shape eqa eq rewrite eqa = sym (just-inj eq)

smget-move : ∀ {pend ρ t x as n s ws n2 s2} →
             walkArms [] (addPend pend n s ρ) as (suc n) (suc s) ≡ just (ws , n2 , s2) →
             walk pend ρ (smget t x as) n s ≡ just (mkW n s n2 s2)
smget-move eq rewrite eq = refl

arm-shape : ∀ {pend ρ y p as n s w ws n2 s2 r} →
            walk pend ρ p n s ≡ just w →
            walkArms pend ρ as (next w) (slotN w) ≡ just (ws , n2 , s2) →
            walkArms pend ρ (aok y p ∷ as) n s ≡ just r →
            r ≡ ((y , w) ∷ ws , n2 , s2)
arm-shape eqw eqa eq rewrite eqw | eqa = sym (just-inj eq)

arm-move : ∀ {pend ρ y p as n s w ws n2 s2} →
           walk pend ρ p n s ≡ just w →
           walkArms pend ρ as (next w) (slotN w) ≡ just (ws , n2 , s2) →
           walkArms pend ρ (aok y p ∷ as) n s ≡
             just ((y , w) ∷ ws , n2 , s2)
arm-move eqw eqa rewrite eqw | eqa = refl

mutual
  arms-ext : ∀ pend ρ0 ρ as n s r → Ext ρ0 ρ →
             walkArms pend ρ0 as n s ≡ just r →
             walkArms pend ρ as n s ≡ just r
  arms-ext pend ρ0 ρ [] n s r ext refl = refl
  arms-ext pend ρ0 ρ (abad ∷ _) n s r ext eq = ⊥-elim (nothing≢just eq)
  arms-ext pend ρ0 ρ (aok y p ∷ as) n s r ext eq =
    arm1 (walk pend ρ0 p n s) refl
    where
    arm1 : (m : Maybe W) → walk pend ρ0 p n s ≡ m →
           walkArms pend ρ (aok y p ∷ as) n s ≡ just r
    arm1 nothing eqw rewrite eqw = ⊥-elim (nothing≢just eq)
    arm1 (just w) eqw = arm2 (walkArms pend ρ0 as (next w) (slotN w)) refl
      where
      arm2 : (m : Maybe (List (String × W) × ℕ × ℕ)) →
             walkArms pend ρ0 as (next w) (slotN w) ≡ m →
             walkArms pend ρ (aok y p ∷ as) n s ≡ just r
      arm2 nothing eqa rewrite eqw | eqa = ⊥-elim (nothing≢just eq)
      arm2 (just (ws , n2 , s2)) eqa =
        let eqw' = walk-ext pend ρ0 ρ p n s w ext eqw
            eqa' = arms-ext pend ρ0 ρ as (next w) (slotN w) (ws , n2 , s2) ext eqa
            r≡ : r ≡ ((y , w) ∷ ws , n2 , s2)
            r≡ = arm-shape {pend} {ρ0} {y} {p} {as} {n} {s} {w} {ws} {n2} {s2} {r} eqw eqa eq
        in trans (arm-move {pend} {ρ} {y} {p} {as} {n} {s} {w} {ws} {n2} {s2} eqw' eqa')
             (cong just (sym r≡))

  walk-ext : ∀ pend ρ0 ρ P n s w → Ext ρ0 ρ →
             walk pend ρ0 P n s ≡ just w →
             walk pend ρ P n s ≡ just w
  walk-ext pend ρ0 ρ (smu x p) n s w ext eq =
    walk-ext (x ∷ pend) ρ0 ρ p n s w ext eq
  walk-ext pend ρ0 ρ (svar y) n s w ext eq =
    var-ext pend ρ0 ρ y n s w ext eq
  walk-ext pend ρ0 ρ sdone n s w ext eq = eq
  walk-ext pend ρ0 ρ sstop n s w ext eq = eq
  walk-ext pend ρ0 ρ sout n s w ext eq = ⊥-elim (nothing≢just eq)
  walk-ext pend ρ0 ρ (sput a p) n s w ext eq =
    put1 (walk [] (addPend pend n s ρ0) p (suc n) s) refl
    where
    put1 : (m : Maybe W) →
           walk [] (addPend pend n s ρ0) p (suc n) s ≡ m →
           walk pend ρ (sput a p) n s ≡ just w
    put1 nothing eqb rewrite eqb = ⊥-elim (nothing≢just eq)
    put1 (just wb) eqb =
      let eqb' = walk-ext [] (addPend pend n s ρ0) (addPend pend n s ρ)
                   p (suc n) s wb (ext-add pend n s ρ0 ρ ext) eqb
          w≡ = sput-shape {pend} {ρ0} {a} {p} {n} {s} {wb} {w} eqb eq
      in trans (sput-move {pend} {ρ} {a} {p} {n} {s} {wb} eqb') (cong just (sym w≡))
  walk-ext pend ρ0 ρ (sget t x p) n s w ext eq =
    get1 (walk [] (addPend pend n s ρ0) p (suc n) (suc s)) refl
    where
    get1 : (m : Maybe W) →
           walk [] (addPend pend n s ρ0) p (suc n) (suc s) ≡ m →
           walk pend ρ (sget t x p) n s ≡ just w
    get1 nothing eqb rewrite eqb = ⊥-elim (nothing≢just eq)
    get1 (just wb) eqb =
      let eqb' = walk-ext [] (addPend pend n s ρ0) (addPend pend n s ρ)
                   p (suc n) (suc s) wb (ext-add pend n s ρ0 ρ ext) eqb
          w≡ = sget-shape {pend} {ρ0} {t} {x} {p} {n} {s} {wb} {w} eqb eq
      in trans (sget-move {pend} {ρ} {t} {x} {p} {n} {s} {wb} eqb') (cong just (sym w≡))
  walk-ext pend ρ0 ρ (spick0 p) n s w ext eq =
    pk (walk [] (addPend pend n s ρ0) p (suc n) s) refl
    where
    pk : (m : Maybe W) →
         walk [] (addPend pend n s ρ0) p (suc n) s ≡ m →
         walk pend ρ (spick0 p) n s ≡ just w
    pk nothing eqb rewrite eqb = ⊥-elim (nothing≢just eq)
    pk (just wb) eqb =
      let eqb' = walk-ext [] (addPend pend n s ρ0) (addPend pend n s ρ)
                   p (suc n) s wb (ext-add pend n s ρ0 ρ ext) eqb
          w≡ = spick-shape {pend} {ρ0} {p} {n} {s} {wb} {w} eqb eq
      in trans (spick0-move {pend} {ρ} {p} {n} {s} {wb} eqb') (cong just (sym w≡))
  walk-ext pend ρ0 ρ (spick1 p) n s w ext eq =
    pk (walk [] (addPend pend n s ρ0) p (suc n) s) refl
    where
    pk : (m : Maybe W) →
         walk [] (addPend pend n s ρ0) p (suc n) s ≡ m →
         walk pend ρ (spick1 p) n s ≡ just w
    pk nothing eqb rewrite eqb = ⊥-elim (nothing≢just eq)
    pk (just wb) eqb =
      let eqb' = walk-ext [] (addPend pend n s ρ0) (addPend pend n s ρ)
                   p (suc n) s wb (ext-add pend n s ρ0 ρ ext) eqb
          w≡ = spick1-shape {pend} {ρ0} {p} {n} {s} {wb} {w} eqb eq
      in trans (spick1-move {pend} {ρ} {p} {n} {s} {wb} eqb') (cong just (sym w≡))
  walk-ext pend ρ0 ρ (scover p q) n s w ext eq =
    cv1 (walk [] (addPend pend n s ρ0) p (suc n) s) refl
    where
    cv1 : (m : Maybe W) →
          walk [] (addPend pend n s ρ0) p (suc n) s ≡ m →
          walk pend ρ (scover p q) n s ≡ just w
    cv1 nothing eq1 rewrite eq1 = ⊥-elim (nothing≢just eq)
    cv1 (just w1) eq1 =
      cv2 (walk [] (addPend pend n s ρ0) q (next w1) (slotN w1)) refl
      where
      cv2 : (m : Maybe W) →
            walk [] (addPend pend n s ρ0) q (next w1) (slotN w1) ≡ m →
            walk pend ρ (scover p q) n s ≡ just w
      cv2 nothing eq2 rewrite eq1 | eq2 = ⊥-elim (nothing≢just eq)
      cv2 (just w2) eq2 =
        let extw = ext-add pend n s ρ0 ρ ext
            eq1' = walk-ext [] (addPend pend n s ρ0) (addPend pend n s ρ)
                     p (suc n) s w1 extw eq1
            eq2' = walk-ext [] (addPend pend n s ρ0) (addPend pend n s ρ)
                     q (next w1) (slotN w1) w2 extw eq2
            w≡ = scover-shape {pend} {ρ0} {p} {q} {n} {s} {w1} {w2} {w} eq1 eq2 eq
        in trans (scover-move {pend} {ρ} {p} {q} {n} {s} {w1} {w2} eq1' eq2')
             (cong just (sym w≡))
  walk-ext pend ρ0 ρ (siget x p q) n s w ext eq =
    ig1 (walk [] (addPend pend n s ρ0) p (suc n) (suc s)) refl
    where
    ig1 : (m : Maybe W) →
          walk [] (addPend pend n s ρ0) p (suc n) (suc s) ≡ m →
          walk pend ρ (siget x p q) n s ≡ just w
    ig1 nothing eq1 rewrite eq1 = ⊥-elim (nothing≢just eq)
    ig1 (just w1) eq1 =
      ig2 (walk [] (addPend pend n s ρ0) q (next w1) (slotN w1)) refl
      where
      ig2 : (m : Maybe W) →
            walk [] (addPend pend n s ρ0) q (next w1) (slotN w1) ≡ m →
            walk pend ρ (siget x p q) n s ≡ just w
      ig2 nothing eq2 rewrite eq1 | eq2 = ⊥-elim (nothing≢just eq)
      ig2 (just w2) eq2 =
        let extw = ext-add pend n s ρ0 ρ ext
            eq1' = walk-ext [] (addPend pend n s ρ0) (addPend pend n s ρ)
                     p (suc n) (suc s) w1 extw eq1
            eq2' = walk-ext [] (addPend pend n s ρ0) (addPend pend n s ρ)
                     q (next w1) (slotN w1) w2 extw eq2
            w≡ = siget-shape {pend} {ρ0} {x} {p} {q} {n} {s} {w1} {w2} {w} eq1 eq2 eq
        in trans (siget-move {pend} {ρ} {x} {p} {q} {n} {s} {w1} {w2} eq1' eq2')
             (cong just (sym w≡))
  walk-ext pend ρ0 ρ (smget t x as) n s w ext eq =
    mg (walkArms [] (addPend pend n s ρ0) as (suc n) (suc s)) refl
    where
    mg : (m : Maybe (List (String × W) × ℕ × ℕ)) →
         walkArms [] (addPend pend n s ρ0) as (suc n) (suc s) ≡ m →
         walk pend ρ (smget t x as) n s ≡ just w
    mg nothing eqa rewrite eqa = ⊥-elim (nothing≢just eq)
    mg (just (ws , n2 , s2)) eqa =
      let eqa' = arms-ext [] (addPend pend n s ρ0) (addPend pend n s ρ)
                   as (suc n) (suc s) (ws , n2 , s2)
                   (ext-add pend n s ρ0 ρ ext) eqa
          w≡ = smget-shape {pend} {ρ0} {t} {x} {as} {n} {s} {ws} {n2} {s2} {w} eqa eq
      in trans (smget-move {pend} {ρ} {t} {x} {as} {n} {s} {ws} {n2} {s2} eqa')
             (cong just (sym w≡))

------------------------------------------------------------------------
-- One entry per binder. A runtime hit is that entry's counters.
------------------------------------------------------------------------

pair : ∀ {a b c d : ℕ} → (a , b) ≡ (c , d) → a ≡ c × b ≡ d
pair refl = refl , refl

fresh-occ : ∀ x ys → elemS x ys ≡ true → fresh x ys ≡ false
fresh-occ x [] ()
fresh-occ x (y ∷ ys) eq = go (x == y) refl eq
  where
  go : (b : Bool) → (x == y) ≡ b → elemS x (y ∷ ys) ≡ true →
       fresh x (y ∷ ys) ≡ false
  go true eqy _ rewrite eqy = refl
  go false eqy eq2 rewrite eqy = fresh-occ x ys eq2

occurs : ∀ {x P tab} (m : InTab x P tab) → elemS x (tnames tab) ≡ true
occurs {x = x} (in-here _) rewrite ==-refl x = refl
occurs {x} (in-there {y = y} {tab = tab} m) =
  elem-cons {y = x} {x = y} {xs = tnames tab} (occurs m)

found : String → Table → Maybe (ℕ × ℕ)
found x t0 = nothing
found x (t1 y i s _ _ t) with x == y
... | true = just (i , s)
... | false = found x t

in-found : ∀ {x P tab} (m : InTab x P tab) →
           distinct (tnames tab) ≡ true →
           found x tab ≡ just (ix-of m , slot-at m)
in-found {x = x} (in-here {i = i} {s0 = s} _) _ rewrite ==-refl x = refl
in-found {x} (in-there {y = y} {i = i} {s0 = s0} {ρ = ρ} {pl = pl} {tab = tab} m) eq =
  step (x == y) refl
  where
  step : (b : Bool) → (x == y) ≡ b →
         found x (t1 y i s0 ρ pl tab) ≡ just (ix-of m , slot-at m)
  step true eqy = ⊥-elim (true≢false (trans (sym (∧-left eq)) (miss eqy)))
    where
    miss : (x == y) ≡ true → fresh y (tnames tab) ≡ false
    miss eqy = go (==-sound eqy)
      where
      go : x ≡ y → fresh y (tnames tab) ≡ false
      go refl = fresh-occ x (tnames tab) (occurs m)
  step false eqy rewrite eqy = in-found m (∧-right eq)

same-slot : ∀ {x P Q tab} (m : InTab x P tab) (n : InTab x Q tab) →
            distinct (tnames tab) ≡ true →
            ix-of m ≡ ix-of n × slot-at m ≡ slot-at n
same-slot m n eq =
  let p = pair (just-inj (trans (sym (in-found m eq)) (in-found n eq)))
  in proj₁ p , proj₂ p

-- One table, one process for a name.
unique : ∀ {x P Q tab} (m : InTab x P tab) (n : InTab x Q tab) →
         distinct (tnames tab) ≡ true → P ≡ Q
unique (in-here _) (in-here _) _ = refl
unique {x = x} (in-here _) (in-there {tab = tab} n) eq =
  ⊥-elim (true≢false (trans (sym (∧-left eq))
           (fresh-occ x (tnames tab) (occurs n))))
unique {x = x} (in-there {tab = tab} m) (in-here _) eq =
  ⊥-elim (true≢false (trans (sym (∧-left eq))
           (fresh-occ x (tnames tab) (occurs m))))
unique (in-there m) (in-there n) eq = unique m n (∧-right eq)

sync-take : ∀ {x y j s0 ρ i s} →
            (x == y) ≡ true →
            lookupI x ((y , j , s0) ∷ ρ) ≡ just (i , s) →
            (j , s0) ≡ (i , s)
sync-take eqy eq2 rewrite eqy = just-inj eq2

sync-drop : ∀ {x y j s0 ρ i s} →
            (x == y) ≡ false →
            lookupI x ((y , j , s0) ∷ ρ) ≡ just (i , s) →
            lookupI x ρ ≡ just (i , s)
sync-drop eqy eq2 rewrite eqy = eq2

sync-yes : ∀ {x y P tab j s0 i s} →
          (m : InTab y P tab) → ix-of m ≡ j → slot-at m ≡ s0 →
          x ≡ y → (j , s0) ≡ (i , s) →
          Σ SProc (λ Q → Σ (InTab x Q tab) (λ n → ix-of n ≡ i × slot-at n ≡ s))
sync-yes {P = P} m ix≡ sl≡ refl refl = P , m , ix≡ , sl≡

sync-hit : ∀ {x tab env ρ i s} →
           Sync tab env ρ →
           lookupI x ρ ≡ just (i , s) →
           Σ SProc (λ P → Σ (InTab x P tab) (λ m → ix-of m ≡ i × slot-at m ≡ s))
sync-hit sy0 eq = ⊥-elim (nothing≢just eq)
sync-hit {x} {i = i} {s = s} (sy1 {x = y} {P = P} {i = j} {s = s0} m ix≡ sl≡ rest) eq =
  split (x == y) refl eq
  where
  split : (b : Bool) → (x == y) ≡ b →
          lookupI x ((y , j , s0) ∷ _) ≡ just (i , s) →
          Σ SProc (λ Q → Σ (InTab x Q _) (λ n → ix-of n ≡ i × slot-at n ≡ s))
  split true eqy eq2 =
    sync-yes {x = x} {y = y} {j = j} {s0 = s0} {i = i} {s = s} m ix≡ sl≡
      (==-sound eqy)
      (sync-take {x = x} {y = y} {j = j} {s0 = s0} {i = i} {s = s} eqy eq2)
  split false eqy eq2 =
    sync-hit rest (sync-drop {x = x} {y = y} {j = j} {s0 = s0} {i = i} {s = s} eqy eq2)

both : ∀ {a c b d : ℕ} → a ≡ c → b ≡ d → (a , b) ≡ (c , d)
both refl refl = refl

-- The binder at this entry is absent from the runtime environment, or
-- already bound at these counters. A second entry would repeat its name.
runtime-pin : ∀ {x P tab env ρ n s} →
              (m : InTab x P tab) →
              ix-of m ≡ n → slot-at m ≡ s →
              distinct (tnames tab) ≡ true →
              Sync tab env ρ →
              lookupI x ρ ≡ nothing ⊎ lookupI x ρ ≡ just (n , s)
runtime-pin {x} {ρ = ρ} {n = n} {s = s} m ix≡ sl≡ nd sy = go (lookupI x ρ) refl
  where
  go : (b : Maybe (ℕ × ℕ)) → lookupI x ρ ≡ b →
       lookupI x ρ ≡ nothing ⊎ lookupI x ρ ≡ just (n , s)
  go nothing p = inj₁ p
  go (just (i , s1)) p =
    let Q , n0 , ix0 , sl0 = sync-hit sy p
        sm = same-slot m n0 nd
    in inj₂ (trans p (cong just (sym (both (trans (sym ix≡) (trans (proj₁ sm) ix0))
                                                 (trans (sym sl≡) (trans (proj₂ sm) sl0))))))

------------------------------------------------------------------------
-- A binder recorded in `Knew` is still recorded after later bindings
-- are pushed in front of it. Pushing a name does not move a hit whose
-- counters are the table's.
------------------------------------------------------------------------

kn-sync : ∀ {tab env ρ} → Knew tab env ρ → Sync tab env ρ
kn-sync kn0 = sy0
kn-sync (kn1 m _ ix≡ sl≡ _ _ _ k) = sy1 m ix≡ sl≡ (kn-sync k)

only-base : ∀ {y base i s} →
            (elemS y [] ≡ true ⊎ lookupI y base ≡ just (i , s)) →
            lookupI y base ≡ just (i , s)
only-base (inj₁ ())
only-base (inj₂ eq) = eq

move-lookup : ∀ {y x ρ b} → (y == x) ≡ true → lookupI x ρ ≡ b → lookupI y ρ ≡ b
move-lookup {y} {x} {ρ} {b} eqy e = go (==-sound eqy) e
  where
  go : y ≡ x → lookupI x ρ ≡ b → lookupI y ρ ≡ b
  go refl e = e

-- The front binding agrees with a denoted hit on the same name.
front-yes : ∀ {y x i s ρ0 ρ j s1} →
            (y == x) ≡ true →
            (lookupI x ρ0 ≡ nothing ⊎ lookupI x ρ0 ≡ just (i , s)) →
            lookupI y ρ0 ≡ just (j , s1) →
            lookupI y ((x , i , s) ∷ ρ) ≡ just (j , s1)
front-yes {y} {x} {i} {s} {ρ0} {ρ} {j} {s1} eqy pin eq =
  grow-hit y x [] i s ρ j s1 eqy
    (pin-use {y = y} {ρ = ρ0} {n = i} {s = s} {i = j} {s1 = s1}
       (move-sum eqy pin) eq)
  where
  move-sum : (y == x) ≡ true →
             (lookupI x ρ0 ≡ nothing ⊎ lookupI x ρ0 ≡ just (i , s)) →
             (lookupI y ρ0 ≡ nothing ⊎ lookupI y ρ0 ≡ just (i , s))
  move-sum eqz (inj₁ no) =
    inj₁ (move-lookup {y = y} {x = x} {ρ = ρ0} {b = nothing} eqz no)
  move-sum eqz (inj₂ yes) =
    inj₂ (move-lookup {y = y} {x = x} {ρ = ρ0} {b = just (i , s)} eqz yes)

ext-front : ∀ {x i s ρ0 ρ} →
            Ext ρ0 ρ →
            (lookupI x ρ0 ≡ nothing ⊎ lookupI x ρ0 ≡ just (i , s)) →
            Ext ρ0 ((x , i , s) ∷ ρ)
ext-front {x} {i} {s} {ρ0} ext pin y j s1 eq = go (y == x) refl
  where
  go : (b : Bool) → (y == x) ≡ b →
       lookupI y ((x , i , s) ∷ _) ≡ just (j , s1)
  go true eqy = front-yes {y = y} {x = x} {i = i} {s = s} {ρ0 = ρ0}
                  {j = j} {s1 = s1} eqy pin eq
  go false eqy rewrite eqy = ext y j s1 eq

cov-cons : ∀ {x i s suf ρ i0 s0} →
           Covered suf [] ρ i0 s0 →
           (lookupI x ρ ≡ nothing ⊎ lookupI x ρ ≡ just (i , s)) →
           Covered suf [] ((x , i , s) ∷ ρ) i0 s0
cov-cons {x} {i} {s} {ρ = ρ} {i0 = i0} {s0 = s0} cov pin y inn =
  inj₂ (body (y == x) refl
         (only-base {y = y} {base = ρ} {i = i0} {s = s0} (cov y inn)))
  where
  body : (b : Bool) → (y == x) ≡ b →
         lookupI y ρ ≡ just (i0 , s0) →
         lookupI y ((x , i , s) ∷ ρ) ≡ just (i0 , s0)
  body true eqy eq = front-yes {y = y} {x = x} {i = i} {s = s} {ρ0 = ρ}
                       {j = i0} {s1 = s0} eqy pin eq
  body false eqy eq rewrite eqy = eq

-- A denoted hit on the front name is that name's table entry.
den-pin : ∀ {x Q} {P : SProc} {pl : Place P} {ρ tab env i s} →
          Ext (envOf pl) ρ →
          Sync tab env ρ →
          (m : InTab x Q tab) →
          ix-of m ≡ i → slot-at m ≡ s →
          distinct (tnames tab) ≡ true →
          lookupI x (envOf pl) ≡ nothing ⊎ lookupI x (envOf pl) ≡ just (i , s)
den-pin {x} {pl = pl} {i = i} {s = s} ext sy m ix≡ sl≡ nd =
  go (lookupI x (envOf pl)) refl
  where
  go : (b : Maybe (ℕ × ℕ)) → lookupI x (envOf pl) ≡ b →
       lookupI x (envOf pl) ≡ nothing ⊎ lookupI x (envOf pl) ≡ just (i , s)
  go nothing p = inj₁ p
  go (just (j , s1)) p =
    let Q , n0 , ix0 , sl0 = sync-hit sy (ext x j s1 p)
        sm = same-slot m n0 nd
    in inj₂ (trans p (cong just (sym (both
         (trans (sym ix≡) (trans (proj₁ sm) ix0))
         (trans (sym sl≡) (trans (proj₂ sm) sl0))))))

record Found (tab : Table) (x : String) (P : SProc) (ρ : EnvI) : Set where
  field
    m : InTab x P tab
    pl : Place P
    peq : place-of m ≡ pl
    i s0 : ℕ
    ix≡ : ix-of m ≡ i
    sl≡ : slot-at m ≡ s0
    suf : List String
    at : At suf pl
    ext : Ext (envOf pl) ρ
    cov : Covered suf [] ρ i s0

kn-find : ∀ {x P tab env ρ} (k : Knew tab env ρ) →
          Bound x P env → distinct (tnames tab) ≡ true →
          Found tab x P ρ
kn-find {x} (kn1 {i = i} {s0 = s0} {suf = suf} {pl = pl} m peq ix≡ sl≡ at ext cov _) b-here _ =
  record
    { m = m ; pl = pl ; peq = peq ; i = i ; s0 = s0
    ; ix≡ = ix≡ ; sl≡ = sl≡ ; suf = suf ; at = at ; ext = ext ; cov = cov }
kn-find {x} (kn1 {x = y} {ρ = tail} {i = i} {s0 = s0} {pl = plF} mF _ ixF slF _ _ _ k) (b-there b) nd =
  let f = kn-find k b nd
      pinD = den-pin {x = y} {pl = Found.pl f} {ρ = tail} {i = i} {s = s0}
               (Found.ext f) (kn-sync k) mF ixF slF nd
      pinR = runtime-pin {x = y} {ρ = tail} {n = i} {s = s0} mF ixF slF nd (kn-sync k)
  in record
    { m = Found.m f ; pl = Found.pl f ; peq = Found.peq f
    ; i = Found.i f ; s0 = Found.s0 f
    ; ix≡ = Found.ix≡ f ; sl≡ = Found.sl≡ f
    ; suf = Found.suf f ; at = Found.at f
    ; ext = ext-front {x = y} {i = i} {s = s0}
              {ρ0 = envOf (Found.pl f)} {ρ = tail} (Found.ext f) pinD
    ; cov = cov-cons {x = y} {i = i} {s = s0} {suf = Found.suf f}
              {ρ = tail} {i0 = Found.i f} {s0 = Found.s0 f} (Found.cov f) pinR }
kn-find kn0 () _

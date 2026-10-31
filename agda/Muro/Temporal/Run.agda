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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Muro.AsyncRec
  using ( Atom; Tok; Block; COut; cok; cfail; Fault
        ; Graph; gr; RConf; rc; materialise; alphabet; init
        ; compile; lookB; elemS )
open import Muro.AsyncRec using (module Graph)
open Graph

open import Muro.Temporal.Bridge
  using ( Frag; echoOk; graphOf; initS; pack; compiled; gok; gfail; elab )
open import Muro.Temporal.Source
  using ( SProc; SConf; sc; W; mkW; EnvI; EnvP; addPend; lookupI
        ; walk; walkArms
        ; sdone; sstop; sout; sput; sget; spick0; spick1
        ; scover; siget; smget; smu; svar
        ; bnames; abs )
open SConf
open W

open import Muro.Temporal.Pic
  using (Ord; ERel; er0; EchoRel; echo-empty; EnvEq)
open import Muro.Temporal.Agree using (root-ns)
open import Muro.Temporal.Den
  using ( Place; Table; t1; Link; Links; CovP; CovT; headIx; slotOf; envOf
        ; InTab; Hosts )
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
    ix : idx ≡ headIx pl
    ss : slot ≡ slotOf pl
    sn : EnvEq (envOf pl) envI

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
            ∀ g c →
            graphOf k P Q fp fq ≡ gok g →
            initS k P Q fp fq ≡ just c →
            Hold g c
init-hold k P Q fp fq eokP eokQ g c eqg eqc =
  body (denote P fp [] [] [] [] (bnames P) [] [] [] zero zero
          er0 (echo-empty [] (bnames P)) eokP refl (root-ns P))
       (denote Q fq [] [] [] [] (bnames Q) [] [] [] zero zero
          er0 (echo-empty [] (bnames Q)) eokQ refl (root-ns Q))
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

  cursor : ∀ {R fr bs} (y : Yes R fr [] [] [] [] zero zero) →
           Yes.bs y ≡ bs →
           ∀ idx → idx ≡ entry (Yes.w y) →
           atSlot (Yes.w y) ≡ zero →
           Cursor bs idx zero [] [] R
  cursor y bs≡ idx ix≡ slot0 =
    record
      { pl = Yes.pl y
      ; cv = covP-cast bs≡ (Yes.cv y)
      ; tab = Yes.tab y
      ; ct = ct-cast bs≡ (Yes.ct y)
      ; lk = Yes.lk y
      ; ls = Yes.ls y
      ; hs = Yes.hs y
      ; td = td0
      ; ix = trans ix≡ (sym (Yes.hd y))
      ; ss = sym (trans (Yes.sl y) slot0)
      ; sn = root-sn y
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
                  (atSlot0 [] P (Yes.w yL) (Yes.wk yL))
      ; rightC = cursor yR (sym bsR≡) eR eR≡
                   (atSlot0 [] Q (Yes.w yR) (Yes.wk yR))
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

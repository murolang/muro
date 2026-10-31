------------------------------------------------------------------------
-- A source process denotes the blocks `compile` allocates.
--
-- A `smu` allocates nothing: it is peeled, and its name is entered in
-- the jump table at the action it reaches. A `svar` is a leaf. It
-- records the index and the slot the binding was given, which is where
-- a jump continues. The block list is built from the inside, and each
-- constructor stores the membership of its own block. Child membership
-- is moved onto the parent list by `there` and by concatenation, so
-- the root coverage proof talks about the root list.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Den where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Muro.AsyncRec
  using ( Atom; aNat; aBit; aCon; Tag
        ; RProc; rdone; rstop; rput; recho; rget; rpick0; rpick1
        ; rcover; riget; rmget; rmu; rvar
        ; REnv; VEnv; COut; cok; cfail; Fault; fUnguarded; fFree
        ; Block; bDone; bStop; bPut; bEcho; bGet; bPick0; bPick1
        ; bCover; bIget; bMget
        ; compile; compileArms; addNames; lookupN; elemS
        ; materialise; lookB )
open import Muro.Temporal.Pic
  using ( Ord; o0; o1; _∈_; here; there; ord-cat; root-at; ents
        ; ERel; er0; add-rel; Seen; seen-no; seen-yes; lookup-rel
        ; EchoRel; echo-empty; echo-extend
        ; +-idr )
open import Muro.Temporal.Bridge
  using ( Frag; FragPay; FragArm; FragArms
        ; fdone; fstop; fput; fget; fpick0; fpick1; fcover; figet; fmget; fmu; fvar
        ; fnat; fbit; fcon; fecho; farm; farms0; farms1
        ; elab; elabArms; echoOk; echoOkArms; echoHere; once
        ; ∧-left; ∧-right )
open import Muro.Temporal.Source
  using ( Pay; pNat; pBit; pCon; pEcho
        ; Arm; aok; SProc; sdone; sstop; sput; sget; spick0; spick1
        ; scover; siget; smget; smu; svar
        ; W; mkW; EnvI; addPend; lookupI; walk; walkArms; findS; asAtom
        ; bnames; bnamesArms )
open W
open import Muro.Temporal.Agree
  using (get-slot; get-names; split-left; split-right
        ; iget-p-ns; iget-q-ns; iget-q-slot)

------------------------------------------------------------------------
-- Moving a block membership onto a longer list.
------------------------------------------------------------------------

∈-tail : ∀ {A : Set} {x y : A} {xs} → x ∈ xs → x ∈ (y ∷ xs)
∈-tail m = there m

∈++ˡ : ∀ {A : Set} {x : A} {xs ys} → x ∈ xs → x ∈ (xs ++ ys)
∈++ˡ here = here
∈++ˡ (there m) = there (∈++ˡ m)

∈++ʳ : ∀ {A : Set} {x : A} {xs ys} → x ∈ ys → x ∈ (xs ++ ys)
∈++ʳ {xs = []} m = m
∈++ʳ {xs = _ ∷ xs} m = there (∈++ʳ {xs = xs} m)

------------------------------------------------------------------------
-- What an action denotes, and where a jump goes.
------------------------------------------------------------------------

mutual
  data Den : Set where
    d-done : ℕ → Den
    d-stop : ℕ → Den
    d-put : (n s : ℕ) (a : Pay) (atom : Atom) (j : ℕ) (p : SProc)
            (ρw : EnvI) (w : W)
            (aeq : asAtom a ≡ just atom)
            (wk : walk [] ρw p (suc n) s ≡ just w)
            (ej : entry w ≡ j)
            (dest : Place p)
            → Den
    d-echo : (n s : ℕ) (x : String) (ns : List String) (sX j : ℕ) (p : SProc)
             (ρw : EnvI) (w : W)
             (fd : findS x ns ≡ just sX)
             (wk : walk [] ρw p (suc n) s ≡ just w)
             (ej : entry w ≡ j)
             (dest : Place p)
             → Den
    d-pick0 : (n s j : ℕ) (p : SProc) (ρw : EnvI) (w : W)
              (wk : walk [] ρw p (suc n) s ≡ just w)
              (ej : entry w ≡ j) (dest : Place p) → Den
    d-pick1 : (n s j : ℕ) (p : SProc) (ρw : EnvI) (w : W)
              (wk : walk [] ρw p (suc n) s ≡ just w)
              (ej : entry w ≡ j) (dest : Place p) → Den
    d-get : (n s : ℕ) (t : Tag) (x : String) (j : ℕ) (p : SProc)
            (ρw : EnvI) (w : W)
            (wk : walk [] ρw p (suc n) (suc s) ≡ just w)
            (ej : entry w ≡ j) (dest : Place p) → Den
    d-cover : (n s i j : ℕ) (p q : SProc) (ρw : EnvI) (w1 w2 : W)
              (wk1 : walk [] ρw p (suc n) s ≡ just w1)
              (ei : entry w1 ≡ i)
              (wk2 : walk [] ρw q (next w1) (slotN w1) ≡ just w2)
              (ej : entry w2 ≡ j)
              (dp : Place p) (dq : Place q) → Den
    d-iget : (n s : ℕ) (x : String) (i j : ℕ) (p q : SProc) (ρw : EnvI)
             (w1 w2 : W)
             (wk1 : walk [] ρw p (suc n) (suc s) ≡ just w1)
             (ei : entry w1 ≡ i)
             (wk2 : walk [] ρw q (next w1) (slotN w1) ≡ just w2)
             (ej : entry w2 ≡ j)
             (dp : Place p) (dq : Place q) → Den
    d-mget : (n s : ℕ) (t : Tag) (x : String)
             (named : List (String × ℕ)) (arms : List Arm) (ρw : EnvI)
             (ws : List (String × W)) (n2 s2 : ℕ)
             (wk : walkArms [] ρw arms (suc n) (suc s) ≡ just (ws , n2 , s2))
             (en : ents ws ≡ named)
             (dests : ArmPs arms ws)
             → Den

  data Place : SProc → Set where
    p-mu : ∀ {p} (x : String) → Place p → Place (smu x p)
    p-act : ∀ {P} (d : Den) → Recipe d P → (i s0 : ℕ) → EnvI → Place P
    p-jump : (x : String) (i s0 : ℕ) (ρ : EnvI) → Place (svar x)

  data Recipe : Den → SProc → Set where
    r-done : ∀ {n} → Recipe (d-done n) sdone
    r-stop : ∀ {n} → Recipe (d-stop n) sstop
    r-put : ∀ {n s a atom j p ρw w aeq wk ej dest} →
            Recipe (d-put n s a atom j p ρw w aeq wk ej dest) (sput a p)
    r-echo : ∀ {n s x ns sX j p ρw w fd wk ej dest} →
             Recipe (d-echo n s x ns sX j p ρw w fd wk ej dest) (sput (pEcho x) p)
    r-pick0 : ∀ {n s j p ρw w wk ej dest} →
              Recipe (d-pick0 n s j p ρw w wk ej dest) (spick0 p)
    r-pick1 : ∀ {n s j p ρw w wk ej dest} →
              Recipe (d-pick1 n s j p ρw w wk ej dest) (spick1 p)
    r-get : ∀ {n s t x j p ρw w wk ej dest} →
            Recipe (d-get n s t x j p ρw w wk ej dest) (sget t x p)
    r-cover : ∀ {n s i j p q ρw w1 w2 wk1 ei wk2 ej dp dq} →
              Recipe (d-cover n s i j p q ρw w1 w2 wk1 ei wk2 ej dp dq) (scover p q)
    r-iget : ∀ {n s x i j p q ρw w1 w2 wk1 ei wk2 ej dp dq} →
             Recipe (d-iget n s x i j p q ρw w1 w2 wk1 ei wk2 ej dp dq) (siget x p q)
    r-mget : ∀ {n s t x named as ρw ws n2 s2 wk en dests} →
             Recipe (d-mget n s t x named as ρw ws n2 s2 wk en dests) (smget t x as)
    r-mu : ∀ {d x p} → Recipe d p → Recipe d (smu x p)

  data Table : Set where
    t0 : Table
    t1 : ∀ {P} (x : String) (i s0 : ℕ) (ρ : EnvI) (pl : Place P) → Table → Table

  data ArmPs : List Arm → List (String × W) → Set where
    ap0 : ArmPs [] []
    ap1 : ∀ {y p as w ws} → Place p → ArmPs as ws →
          ArmPs (aok y p ∷ as) ((y , w) ∷ ws)

data Cov : Den → List (ℕ × Block) → Set
data CovP : {P : SProc} → Place P → List (ℕ × Block) → Set
data CovA : {as : List Arm} {ws : List (String × W)} →
            ArmPs as ws → List (ℕ × Block) → Set
data CovT : Table → List (ℕ × Block) → Set

data Cov where
  c-done : ∀ {n bs} → (n , bDone) ∈ bs → Cov (d-done n) bs
  c-stop : ∀ {n bs} → (n , bStop) ∈ bs → Cov (d-stop n) bs
  c-put : ∀ {n s a atom j p ρw w aeq wk ej dest bs} →
          (n , bPut atom j) ∈ bs → CovP dest bs →
          Cov (d-put n s a atom j p ρw w aeq wk ej dest) bs
  c-echo : ∀ {n s x ns sX j p ρw w fd wk ej dest bs} →
           (n , bEcho sX j) ∈ bs → CovP dest bs →
           Cov (d-echo n s x ns sX j p ρw w fd wk ej dest) bs
  c-pick0 : ∀ {n s j p ρw w wk ej dest bs} →
            (n , bPick0 j) ∈ bs → CovP dest bs →
            Cov (d-pick0 n s j p ρw w wk ej dest) bs
  c-pick1 : ∀ {n s j p ρw w wk ej dest bs} →
            (n , bPick1 j) ∈ bs → CovP dest bs →
            Cov (d-pick1 n s j p ρw w wk ej dest) bs
  c-get : ∀ {n s t x j p ρw w wk ej dest bs} →
          (n , bGet t s j) ∈ bs → CovP dest bs →
          Cov (d-get n s t x j p ρw w wk ej dest) bs
  c-cover : ∀ {n s i j p q ρw w1 w2 wk1 ei wk2 ej dp dq bs} →
            (n , bCover i j) ∈ bs → CovP dp bs → CovP dq bs →
            Cov (d-cover n s i j p q ρw w1 w2 wk1 ei wk2 ej dp dq) bs
  c-iget : ∀ {n s x i j p q ρw w1 w2 wk1 ei wk2 ej dp dq bs} →
           (n , bIget s i j) ∈ bs → CovP dp bs → CovP dq bs →
           Cov (d-iget n s x i j p q ρw w1 w2 wk1 ei wk2 ej dp dq) bs
  c-mget : ∀ {n s t x named as ρw ws n2 s2 wk en dests bs} →
           (n , bMget t s named) ∈ bs → CovA dests bs →
           Cov (d-mget n s t x named as ρw ws n2 s2 wk en dests) bs

data CovP where
  cp-mu : ∀ {x p inner bs} → CovP inner bs → CovP (p-mu {p} x inner) bs
  cp-act : ∀ {P d r i s0 ρ bs} → Cov d bs → CovP (p-act {P} d r i s0 ρ) bs
  cp-jump : ∀ {x i s0 ρ bs} → CovP (p-jump x i s0 ρ) bs

data CovA where
  ca0 : ∀ {bs} → CovA ap0 bs
  ca1 : ∀ {y p as w ws pl rest bs} →
        CovP pl bs → CovA rest bs →
        CovA (ap1 {y} {p} {as} {w} {ws} pl rest) bs

data CovT where
  ct0 : ∀ {bs} → CovT t0 bs
  ct1 : ∀ {P x i s0 ρ pl tab bs} →
        CovP pl bs → CovT tab bs →
        CovT (t1 {P} x i s0 ρ pl tab) bs

mutual
  cov-lift : ∀ {d xs ys} →
             (∀ {i b} → (i , b) ∈ xs → (i , b) ∈ ys) →
             Cov d xs → Cov d ys
  cov-lift f (c-done m) = c-done (f m)
  cov-lift f (c-stop m) = c-stop (f m)
  cov-lift f (c-put m c) = c-put (f m) (covP-lift f c)
  cov-lift f (c-echo m c) = c-echo (f m) (covP-lift f c)
  cov-lift f (c-pick0 m c) = c-pick0 (f m) (covP-lift f c)
  cov-lift f (c-pick1 m c) = c-pick1 (f m) (covP-lift f c)
  cov-lift f (c-get m c) = c-get (f m) (covP-lift f c)
  cov-lift f (c-cover m cp cq) = c-cover (f m) (covP-lift f cp) (covP-lift f cq)
  cov-lift f (c-iget m cp cq) = c-iget (f m) (covP-lift f cp) (covP-lift f cq)
  cov-lift f (c-mget m ca) = c-mget (f m) (covA-lift f ca)

  covP-lift : ∀ {P} {pl : Place P} {xs ys} →
              (∀ {i b} → (i , b) ∈ xs → (i , b) ∈ ys) →
              CovP pl xs → CovP pl ys
  covP-lift f (cp-mu c) = cp-mu (covP-lift f c)
  covP-lift f (cp-act c) = cp-act (cov-lift f c)
  covP-lift f cp-jump = cp-jump

  covA-lift : ∀ {as ws} {ps : ArmPs as ws} {xs ys} →
              (∀ {i b} → (i , b) ∈ xs → (i , b) ∈ ys) →
              CovA ps xs → CovA ps ys
  covA-lift f ca0 = ca0
  covA-lift f (ca1 c cs) = ca1 (covP-lift f c) (covA-lift f cs)

covT-lift : ∀ {tab xs ys} →
            (∀ {i b} → (i , b) ∈ xs → (i , b) ∈ ys) →
            CovT tab xs → CovT tab ys
covT-lift f ct0 = ct0
covT-lift f (ct1 c ct) = ct1 (covP-lift f c) (covT-lift f ct)

headIx : ∀ {P} → Place P → ℕ
headIx (p-mu _ pl) = headIx pl
headIx (p-act _ _ i _ _) = i
headIx (p-jump _ i _ _) = i

slotOf : ∀ {P} → Place P → ℕ
slotOf (p-mu _ pl) = slotOf pl
slotOf (p-act _ _ _ s _) = s
slotOf (p-jump _ _ s _) = s

envOf : ∀ {P} → Place P → EnvI
envOf (p-mu _ pl) = envOf pl
envOf (p-act _ _ _ _ ρ) = ρ
envOf (p-jump _ _ _ ρ) = ρ

------------------------------------------------------------------------
-- `walk` and `compile` of a compound, from the body's result.
------------------------------------------------------------------------

sput-walk : ∀ {pend ρ a p n s w} →
            walk [] (addPend pend n s ρ) p (suc n) s ≡ just w →
            walk pend ρ (sput a p) n s ≡ just (mkW n s (next w) (slotN w))
sput-walk eq rewrite eq = refl

sput-miss : ∀ {pend ρ a p n s} →
            walk [] (addPend pend n s ρ) p (suc n) s ≡ nothing →
            walk pend ρ (sput a p) n s ≡ nothing
sput-miss eq rewrite eq = refl

put-cmp : ∀ {pend renv venv slot n q atom e next slot' bs} →
          compile q [] (addNames pend n renv) venv slot (suc n) ≡
            cok e next slot' bs →
          compile (rput atom q) pend renv venv slot n ≡
            cok n next slot' ((n , bPut atom e) ∷ bs)
put-cmp eq rewrite eq = refl

put-miss : ∀ {pend renv venv slot n q atom f} →
           compile q [] (addNames pend n renv) venv slot (suc n) ≡ cfail f →
           compile (rput atom q) pend renv venv slot n ≡ cfail f
put-miss eq rewrite eq = refl

echo-cmp : ∀ {pend renv venv slot n x sX q e next slot' bs} →
           lookupN x venv ≡ just sX →
           compile q [] (addNames pend n renv) venv slot (suc n) ≡
             cok e next slot' bs →
           compile (recho x q) pend renv venv slot n ≡
             cok n next slot' ((n , bEcho sX e) ∷ bs)
echo-cmp eqL eqC rewrite eqL | eqC = refl

echo-miss-name : ∀ {pend renv venv slot n x q} →
                 lookupN x venv ≡ nothing →
                 compile (recho x q) pend renv venv slot n ≡ cfail fFree
echo-miss-name eq rewrite eq = refl

echo-miss : ∀ {pend renv venv slot n x sX q f} →
            lookupN x venv ≡ just sX →
            compile q [] (addNames pend n renv) venv slot (suc n) ≡ cfail f →
            compile (recho x q) pend renv venv slot n ≡ cfail f
echo-miss eqL eqC rewrite eqL | eqC = refl

sget-walk : ∀ {pend ρ t x p n s w} →
            walk [] (addPend pend n s ρ) p (suc n) (suc s) ≡ just w →
            walk pend ρ (sget t x p) n s ≡ just (mkW n s (next w) (slotN w))
sget-walk eq rewrite eq = refl

sget-miss : ∀ {pend ρ t x p n s} →
            walk [] (addPend pend n s ρ) p (suc n) (suc s) ≡ nothing →
            walk pend ρ (sget t x p) n s ≡ nothing
sget-miss eq rewrite eq = refl

get-cmp : ∀ {pend renv venv slot n t x q e next slot' bs} →
          compile q [] (addNames pend n renv) ((x , slot) ∷ venv) (suc slot) (suc n) ≡
            cok e next slot' bs →
          compile (rget t x q) pend renv venv slot n ≡
            cok n next slot' ((n , bGet t slot e) ∷ bs)
get-cmp eq rewrite eq = refl

get-miss : ∀ {pend renv venv slot n t x q f} →
           compile q [] (addNames pend n renv) ((x , slot) ∷ venv) (suc slot) (suc n) ≡
             cfail f →
           compile (rget t x q) pend renv venv slot n ≡ cfail f
get-miss eq rewrite eq = refl

-- The pick, cover, iget, and match lemmas follow the same rewrite.

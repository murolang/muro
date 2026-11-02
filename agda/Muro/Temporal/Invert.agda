------------------------------------------------------------------------
-- A graph step, read off the block `lookB` returned.
--
-- `reactL` and `reactR` are functions of that block. When the result
-- is `AGo`, the block names the queue test that succeeded and the
-- configuration the step built. A halted block cannot step.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Invert where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

open import Muro.AsyncRec
  using ( Atom; aNat; aBit; aCon; Tag; Tok; pay; lab
        ; Block; bDone; bStop; bPut; bEcho; bGrow; bGet; bPick0; bPick1
        ; bCover; bIget; bMget
        ; RConf; rc; Graph; Act; AWait; ABad; AGo
        ; lookB; findA; nthA; fits; conOf; slotVal; armTo; setNth
        ; lt; room; snoc; reactL; reactR; isHalt )
open Graph
open import Muro.Temporal.Fire
  using ( react-put; react-echo; react-pick0; react-pick1
        ; react-get; react-cover0; react-cover1
        ; react-iget0; react-iget1; react-mget
        ; reactR-put; reactR-echo; reactR-pick0; reactR-pick1
        ; reactR-get; reactR-cover0; reactR-cover1
        ; reactR-iget0; reactR-iget1; reactR-mget
        ; bad≢go; wait≢go; ago-inj )

false≢true : false ≡ true → ⊥
false≢true ()

lt-sound : ∀ m n → lt m n ≡ true → m < n
lt-sound zero zero ()
lt-sound zero (suc _) _ = s≤s z≤n
lt-sound (suc _) zero ()
lt-sound (suc m) (suc n) eq = s≤s (lt-sound m n eq)

room-sound : ∀ cap (q : List Tok) → room cap q ≡ true → length q < cap
room-sound cap q eq = lt-sound (length q) cap eq

------------------------------------------------------------------------
-- A halt waits. The other blocks, when they step, name their target.
------------------------------------------------------------------------

haltL : ∀ g il ir (l2r r2l : List Tok) el er b →
        lookB (codeL g) il ≡ just b → isHalt b ≡ true →
        reactL g (rc il ir l2r r2l el er) ≡ AWait
haltL g il ir l2r r2l el er bDone eq refl rewrite eq = refl
haltL g il ir l2r r2l el er bStop eq refl rewrite eq = refl
haltL _ _ _ _ _ _ _ (bPut _ _) _ ()
haltL _ _ _ _ _ _ _ (bEcho _ _) _ ()
haltL _ _ _ _ _ _ _ (bGrow _ _) _ ()
haltL _ _ _ _ _ _ _ (bGet _ _ _) _ ()
haltL _ _ _ _ _ _ _ (bPick0 _) _ ()
haltL _ _ _ _ _ _ _ (bPick1 _) _ ()
haltL _ _ _ _ _ _ _ (bCover _ _) _ ()
haltL _ _ _ _ _ _ _ (bIget _ _ _) _ ()
haltL _ _ _ _ _ _ _ (bMget _ _ _) _ ()

haltR : ∀ g il ir (l2r r2l : List Tok) el er b →
        lookB (codeR g) ir ≡ just b → isHalt b ≡ true →
        reactR g (rc il ir l2r r2l el er) ≡ AWait
haltR g il ir l2r r2l el er bDone eq refl rewrite eq = refl
haltR g il ir l2r r2l el er bStop eq refl rewrite eq = refl
haltR _ _ _ _ _ _ _ (bPut _ _) _ ()
haltR _ _ _ _ _ _ _ (bEcho _ _) _ ()
haltR _ _ _ _ _ _ _ (bGrow _ _) _ ()
haltR _ _ _ _ _ _ _ (bGet _ _ _) _ ()
haltR _ _ _ _ _ _ _ (bPick0 _) _ ()
haltR _ _ _ _ _ _ _ (bPick1 _) _ ()
haltR _ _ _ _ _ _ _ (bCover _ _) _ ()
haltR _ _ _ _ _ _ _ (bIget _ _ _) _ ()
haltR _ _ _ _ _ _ _ (bMget _ _ _) _ ()

putL : ∀ g il ir (l2r r2l : List Tok) el er atom j r →
       lookB (codeL g) il ≡ just (bPut atom j) →
       reactL g (rc il ir l2r r2l el er) ≡ AGo r →
       Σ ℕ (λ k → findA atom (alpha g) ≡ just k ×
                  room (cap g) l2r ≡ true ×
                  r ≡ rc j ir (snoc l2r (pay k)) r2l el er)
putL g il ir l2r r2l el er atom j r eqB eq = onF (findA atom (alpha g)) refl
  where
  onR : (k : ℕ) → findA atom (alpha g) ≡ just k →
        (b : Bool) → room (cap g) l2r ≡ b →
        Σ ℕ (λ k′ → findA atom (alpha g) ≡ just k′ ×
                    room (cap g) l2r ≡ true ×
                    r ≡ rc j ir (snoc l2r (pay k′)) r2l el er)
  onR k eqF false eqR rewrite eqB | eqF | eqR = ⊥-elim (wait≢go eq)
  onR k eqF true eqR =
    k , eqF , eqR ,
    ago-inj (trans (sym eq)
      (react-put g il ir l2r r2l el er atom k j eqF eqR eqB))
  onF : (mb : Maybe ℕ) → findA atom (alpha g) ≡ mb →
        Σ ℕ (λ k → findA atom (alpha g) ≡ just k ×
                   room (cap g) l2r ≡ true ×
                   r ≡ rc j ir (snoc l2r (pay k)) r2l el er)
  onF nothing eqF rewrite eqB | eqF = ⊥-elim (bad≢go eq)
  onF (just k) eqF = onR k eqF (room (cap g) l2r) refl

echoL : ∀ g il ir (l2r r2l : List Tok) el er s j r →
        lookB (codeL g) il ≡ just (bEcho s j) →
        reactL g (rc il ir l2r r2l el er) ≡ AGo r →
        Σ ℕ (λ k → slotVal el s ≡ just k ×
                   room (cap g) l2r ≡ true ×
                   r ≡ rc j ir (snoc l2r (pay k)) r2l el er)
echoL g il ir l2r r2l el er s j r eqB eq = onS (slotVal el s) refl
  where
  onR : (k : ℕ) → slotVal el s ≡ just k →
        (b : Bool) → room (cap g) l2r ≡ b →
        Σ ℕ (λ k′ → slotVal el s ≡ just k′ ×
                    room (cap g) l2r ≡ true ×
                    r ≡ rc j ir (snoc l2r (pay k′)) r2l el er)
  onR k eqS false eqR rewrite eqB | eqS | eqR = ⊥-elim (wait≢go eq)
  onR k eqS true eqR =
    k , eqS , eqR ,
    ago-inj (trans (sym eq)
      (react-echo g il ir l2r r2l el er s k j eqS eqR eqB))
  onS : (mb : Maybe ℕ) → slotVal el s ≡ mb →
        Σ ℕ (λ k → slotVal el s ≡ just k ×
                   room (cap g) l2r ≡ true ×
                   r ≡ rc j ir (snoc l2r (pay k)) r2l el er)
  onS nothing eqS rewrite eqB | eqS = ⊥-elim (wait≢go eq)
  onS (just k) eqS = onR k eqS (room (cap g) l2r) refl

pick0L : ∀ g il ir (l2r r2l : List Tok) el er j r →
         lookB (codeL g) il ≡ just (bPick0 j) →
         reactL g (rc il ir l2r r2l el er) ≡ AGo r →
         room (cap g) l2r ≡ true ×
         r ≡ rc j ir (snoc l2r (lab false)) r2l el er
pick0L g il ir l2r r2l el er j r eqB eq = onR (room (cap g) l2r) refl
  where
  onR : (b : Bool) → room (cap g) l2r ≡ b →
        room (cap g) l2r ≡ true ×
        r ≡ rc j ir (snoc l2r (lab false)) r2l el er
  onR false eqR rewrite eqB | eqR = ⊥-elim (wait≢go eq)
  onR true eqR =
    eqR , ago-inj (trans (sym eq)
      (react-pick0 g il ir l2r r2l el er j eqR eqB))

pick1L : ∀ g il ir (l2r r2l : List Tok) el er j r →
         lookB (codeL g) il ≡ just (bPick1 j) →
         reactL g (rc il ir l2r r2l el er) ≡ AGo r →
         room (cap g) l2r ≡ true ×
         r ≡ rc j ir (snoc l2r (lab true)) r2l el er
pick1L g il ir l2r r2l el er j r eqB eq = onR (room (cap g) l2r) refl
  where
  onR : (b : Bool) → room (cap g) l2r ≡ b →
        room (cap g) l2r ≡ true ×
        r ≡ rc j ir (snoc l2r (lab true)) r2l el er
  onR false eqR rewrite eqB | eqR = ⊥-elim (wait≢go eq)
  onR true eqR =
    eqR , ago-inj (trans (sym eq)
      (react-pick1 g il ir l2r r2l el er j eqR eqB))

getL : ∀ g il ir (l2r r2l : List Tok) el er t s i r →
       lookB (codeL g) il ≡ just (bGet t s i) →
       reactL g (rc il ir l2r r2l el er) ≡ AGo r →
       Σ ℕ (λ k → Σ (List Tok) (λ rest → Σ Atom (λ a →
         r2l ≡ pay k ∷ rest ×
         nthA (alpha g) k ≡ just a ×
         fits t a ≡ true ×
         r ≡ rc i ir l2r rest (setNth s (suc k) el) er)))
getL g il ir l2r r2l el er t s i r eqB eq = onQ r2l refl
  where
  onQ : (q : List Tok) → r2l ≡ q →
        Σ ℕ (λ k → Σ (List Tok) (λ rest → Σ Atom (λ a →
          r2l ≡ pay k ∷ rest ×
          nthA (alpha g) k ≡ just a ×
          fits t a ≡ true ×
          r ≡ rc i ir l2r rest (setNth s (suc k) el) er)))
  onQ [] eqq rewrite eqB | eqq = ⊥-elim (wait≢go eq)
  onQ (lab _ ∷ _) eqq rewrite eqB | eqq = ⊥-elim (bad≢go eq)
  onQ (pay k ∷ rest) eqq = onA (nthA (alpha g) k) refl
    where
    onA : (mb : Maybe Atom) → nthA (alpha g) k ≡ mb →
          Σ ℕ (λ k′ → Σ (List Tok) (λ rest′ → Σ Atom (λ a →
            r2l ≡ pay k′ ∷ rest′ ×
            nthA (alpha g) k′ ≡ just a ×
            fits t a ≡ true ×
            r ≡ rc i ir l2r rest′ (setNth s (suc k′) el) er)))
    onA nothing eqA rewrite eqB | eqq | eqA = ⊥-elim (bad≢go eq)
    onA (just a) eqA = onF (fits t a) refl
      where
      onF : (b : Bool) → fits t a ≡ b →
            Σ ℕ (λ k′ → Σ (List Tok) (λ rest′ → Σ Atom (λ a′ →
              r2l ≡ pay k′ ∷ rest′ ×
              nthA (alpha g) k′ ≡ just a′ ×
              fits t a′ ≡ true ×
              r ≡ rc i ir l2r rest′ (setNth s (suc k′) el) er)))
      onF false eqF rewrite eqB | eqq | eqA | eqF = ⊥-elim (bad≢go eq)
      onF true eqF =
        let moved = subst (λ q → reactL g (rc il ir l2r q el er) ≡ AGo r) eqq eq
            tgt = ago-inj (trans (sym moved)
                    (react-get g il ir l2r k rest el er t s a i refl eqA eqF eqB))
        in k , rest , a , eqq , eqA , eqF , tgt

coverL : ∀ g il ir (l2r r2l : List Tok) el er i j r →
         lookB (codeL g) il ≡ just (bCover i j) →
         reactL g (rc il ir l2r r2l el er) ≡ AGo r →
         Σ (List Tok) (λ rest →
           (r2l ≡ lab false ∷ rest × r ≡ rc i ir l2r rest el er) ⊎
           (r2l ≡ lab true ∷ rest × r ≡ rc j ir l2r rest el er))
coverL g il ir l2r r2l el er i j r eqB eq = onQ r2l refl
  where
  onQ : (q : List Tok) → r2l ≡ q →
        Σ (List Tok) (λ rest →
          (r2l ≡ lab false ∷ rest × r ≡ rc i ir l2r rest el er) ⊎
          (r2l ≡ lab true ∷ rest × r ≡ rc j ir l2r rest el er))
  onQ [] eqq rewrite eqB | eqq = ⊥-elim (wait≢go eq)
  onQ (pay _ ∷ _) eqq rewrite eqB | eqq = ⊥-elim (bad≢go eq)
  onQ (lab false ∷ rest) eqq =
    let moved = subst (λ q → reactL g (rc il ir l2r q el er) ≡ AGo r) eqq eq
        tgt = ago-inj (trans (sym moved)
                (react-cover0 g il ir l2r rest el er i j eqB))
    in rest , inj₁ (eqq , tgt)
  onQ (lab true ∷ rest) eqq =
    let moved = subst (λ q → reactL g (rc il ir l2r q el er) ≡ AGo r) eqq eq
        tgt = ago-inj (trans (sym moved)
                (react-cover1 g il ir l2r rest el er i j eqB))
    in rest , inj₂ (eqq , tgt)

igetL : ∀ g il ir (l2r r2l : List Tok) el er s i j r →
        lookB (codeL g) il ≡ just (bIget s i j) →
        reactL g (rc il ir l2r r2l el er) ≡ AGo r →
        Σ ℕ (λ k → Σ (List Tok) (λ rest →
          (r2l ≡ pay k ∷ rest × nthA (alpha g) k ≡ just (aBit false) ×
           r ≡ rc i ir l2r rest (setNth s (suc k) el) er) ⊎
          (r2l ≡ pay k ∷ rest × nthA (alpha g) k ≡ just (aBit true) ×
           r ≡ rc j ir l2r rest (setNth s (suc k) el) er)))
igetL g il ir l2r r2l el er s i j r eqB eq = onQ r2l refl
  where
  onQ : (q : List Tok) → r2l ≡ q →
        Σ ℕ (λ k → Σ (List Tok) (λ rest →
          (r2l ≡ pay k ∷ rest × nthA (alpha g) k ≡ just (aBit false) ×
           r ≡ rc i ir l2r rest (setNth s (suc k) el) er) ⊎
          (r2l ≡ pay k ∷ rest × nthA (alpha g) k ≡ just (aBit true) ×
           r ≡ rc j ir l2r rest (setNth s (suc k) el) er)))
  onQ [] eqq rewrite eqB | eqq = ⊥-elim (wait≢go eq)
  onQ (lab _ ∷ _) eqq rewrite eqB | eqq = ⊥-elim (bad≢go eq)
  onQ (pay k ∷ rest) eqq = onA (nthA (alpha g) k) refl
    where
    onA : (mb : Maybe Atom) → nthA (alpha g) k ≡ mb →
          Σ ℕ (λ k′ → Σ (List Tok) (λ rest′ →
            (r2l ≡ pay k′ ∷ rest′ × nthA (alpha g) k′ ≡ just (aBit false) ×
             r ≡ rc i ir l2r rest′ (setNth s (suc k′) el) er) ⊎
            (r2l ≡ pay k′ ∷ rest′ × nthA (alpha g) k′ ≡ just (aBit true) ×
             r ≡ rc j ir l2r rest′ (setNth s (suc k′) el) er)))
    onA nothing eqA rewrite eqB | eqq | eqA = ⊥-elim (bad≢go eq)
    onA (just (aNat _)) eqA rewrite eqB | eqq | eqA = ⊥-elim (bad≢go eq)
    onA (just (aCon _)) eqA rewrite eqB | eqq | eqA = ⊥-elim (bad≢go eq)
    onA (just (aBit false)) eqA =
      let moved = subst (λ q → reactL g (rc il ir l2r q el er) ≡ AGo r) eqq eq
          tgt = ago-inj (trans (sym moved)
                  (react-iget0 g il ir l2r k rest el er s i j eqA eqB))
      in k , rest , inj₁ (eqq , eqA , tgt)
    onA (just (aBit true)) eqA =
      let moved = subst (λ q → reactL g (rc il ir l2r q el er) ≡ AGo r) eqq eq
          tgt = ago-inj (trans (sym moved)
                  (react-iget1 g il ir l2r k rest el er s i j eqA eqB))
      in k , rest , inj₂ (eqq , eqA , tgt)

mgetL : ∀ g il ir (l2r r2l : List Tok) el er t s arms r →
        lookB (codeL g) il ≡ just (bMget t s arms) →
        reactL g (rc il ir l2r r2l el er) ≡ AGo r →
        Σ ℕ (λ k → Σ (List Tok) (λ rest → Σ Atom (λ a → Σ String (λ name →
          Σ ℕ (λ j →
          r2l ≡ pay k ∷ rest ×
          nthA (alpha g) k ≡ just a ×
          fits t a ≡ true ×
          conOf a ≡ just name ×
          armTo name arms ≡ just j ×
          r ≡ rc j ir l2r rest (setNth s (suc k) el) er)))))
mgetL g il ir l2r r2l el er t s arms r eqB eq = onQ r2l refl
  where
  onQ : (q : List Tok) → r2l ≡ q →
        Σ ℕ (λ k → Σ (List Tok) (λ rest → Σ Atom (λ a → Σ String (λ name →
          Σ ℕ (λ j →
          r2l ≡ pay k ∷ rest ×
          nthA (alpha g) k ≡ just a ×
          fits t a ≡ true ×
          conOf a ≡ just name ×
          armTo name arms ≡ just j ×
          r ≡ rc j ir l2r rest (setNth s (suc k) el) er)))))
  onQ [] eqq rewrite eqB | eqq = ⊥-elim (wait≢go eq)
  onQ (lab _ ∷ _) eqq rewrite eqB | eqq = ⊥-elim (bad≢go eq)
  onQ (pay k ∷ rest) eqq = onA (nthA (alpha g) k) refl
    where
    onA : (mb : Maybe Atom) → nthA (alpha g) k ≡ mb →
          Σ ℕ (λ k′ → Σ (List Tok) (λ rest′ → Σ Atom (λ a → Σ String (λ name →
            Σ ℕ (λ j →
            r2l ≡ pay k′ ∷ rest′ ×
            nthA (alpha g) k′ ≡ just a ×
            fits t a ≡ true ×
            conOf a ≡ just name ×
            armTo name arms ≡ just j ×
            r ≡ rc j ir l2r rest′ (setNth s (suc k′) el) er)))))
    onA nothing eqA rewrite eqB | eqq | eqA = ⊥-elim (bad≢go eq)
    onA (just a) eqA = onF (fits t a) refl
      where
      onF : (b : Bool) → fits t a ≡ b →
            Σ ℕ (λ k′ → Σ (List Tok) (λ rest′ → Σ Atom (λ a′ → Σ String (λ name →
              Σ ℕ (λ j →
              r2l ≡ pay k′ ∷ rest′ ×
              nthA (alpha g) k′ ≡ just a′ ×
              fits t a′ ≡ true ×
              conOf a′ ≡ just name ×
              armTo name arms ≡ just j ×
              r ≡ rc j ir l2r rest′ (setNth s (suc k′) el) er)))))
      onF false eqF rewrite eqB | eqq | eqA | eqF = ⊥-elim (bad≢go eq)
      onF true eqF = onC (conOf a) refl
        where
        onC : (mb : Maybe String) → conOf a ≡ mb →
              Σ ℕ (λ k′ → Σ (List Tok) (λ rest′ → Σ Atom (λ a′ → Σ String (λ name →
                Σ ℕ (λ j →
                r2l ≡ pay k′ ∷ rest′ ×
                nthA (alpha g) k′ ≡ just a′ ×
                fits t a′ ≡ true ×
                conOf a′ ≡ just name ×
                armTo name arms ≡ just j ×
                r ≡ rc j ir l2r rest′ (setNth s (suc k′) el) er)))))
        onC nothing eqC rewrite eqB | eqq | eqA | eqF | eqC = ⊥-elim (bad≢go eq)
        onC (just name) eqC = onJ (armTo name arms) refl
          where
          onJ : (mb : Maybe ℕ) → armTo name arms ≡ mb →
                Σ ℕ (λ k′ → Σ (List Tok) (λ rest′ → Σ Atom (λ a′ → Σ String (λ name′ →
                  Σ ℕ (λ j →
                  r2l ≡ pay k′ ∷ rest′ ×
                  nthA (alpha g) k′ ≡ just a′ ×
                  fits t a′ ≡ true ×
                  conOf a′ ≡ just name′ ×
                  armTo name′ arms ≡ just j ×
                  r ≡ rc j ir l2r rest′ (setNth s (suc k′) el) er)))))
          onJ nothing eqJ rewrite eqB | eqq | eqA | eqF | eqC | eqJ =
            ⊥-elim (bad≢go eq)
          onJ (just j) eqJ =
            let moved = subst (λ q → reactL g (rc il ir l2r q el er) ≡ AGo r) eqq eq
                tgt = ago-inj (trans (sym moved)
                        (react-mget g il ir l2r k rest el er t s arms a name j
                          eqA eqF eqC eqJ eqB))
            in k , rest , a , name , j , eqq , eqA , eqF , eqC , eqJ , tgt

------------------------------------------------------------------------
-- Right side. The queues are swapped and the step writes `r2l`.
------------------------------------------------------------------------

putR : ∀ g il ir (l2r r2l : List Tok) el er atom j r →
       lookB (codeR g) ir ≡ just (bPut atom j) →
       reactR g (rc il ir l2r r2l el er) ≡ AGo r →
       Σ ℕ (λ k → findA atom (alpha g) ≡ just k ×
                  room (cap g) r2l ≡ true ×
                  r ≡ rc il j l2r (snoc r2l (pay k)) el er)
putR g il ir l2r r2l el er atom j r eqB eq = onF (findA atom (alpha g)) refl
  where
  onR : (k : ℕ) → findA atom (alpha g) ≡ just k →
        (b : Bool) → room (cap g) r2l ≡ b →
        Σ ℕ (λ k′ → findA atom (alpha g) ≡ just k′ ×
                    room (cap g) r2l ≡ true ×
                    r ≡ rc il j l2r (snoc r2l (pay k′)) el er)
  onR k eqF false eqR rewrite eqB | eqF | eqR = ⊥-elim (wait≢go eq)
  onR k eqF true eqR =
    k , eqF , eqR ,
    ago-inj (trans (sym eq)
      (reactR-put g il ir l2r r2l el er atom k j eqF eqR eqB))
  onF : (mb : Maybe ℕ) → findA atom (alpha g) ≡ mb →
        Σ ℕ (λ k → findA atom (alpha g) ≡ just k ×
                   room (cap g) r2l ≡ true ×
                   r ≡ rc il j l2r (snoc r2l (pay k)) el er)
  onF nothing eqF rewrite eqB | eqF = ⊥-elim (bad≢go eq)
  onF (just k) eqF = onR k eqF (room (cap g) r2l) refl

echoR : ∀ g il ir (l2r r2l : List Tok) el er s j r →
        lookB (codeR g) ir ≡ just (bEcho s j) →
        reactR g (rc il ir l2r r2l el er) ≡ AGo r →
        Σ ℕ (λ k → slotVal er s ≡ just k ×
                   room (cap g) r2l ≡ true ×
                   r ≡ rc il j l2r (snoc r2l (pay k)) el er)
echoR g il ir l2r r2l el er s j r eqB eq = onS (slotVal er s) refl
  where
  onR : (k : ℕ) → slotVal er s ≡ just k →
        (b : Bool) → room (cap g) r2l ≡ b →
        Σ ℕ (λ k′ → slotVal er s ≡ just k′ ×
                    room (cap g) r2l ≡ true ×
                    r ≡ rc il j l2r (snoc r2l (pay k′)) el er)
  onR k eqS false eqR rewrite eqB | eqS | eqR = ⊥-elim (wait≢go eq)
  onR k eqS true eqR =
    k , eqS , eqR ,
    ago-inj (trans (sym eq)
      (reactR-echo g il ir l2r r2l el er s k j eqS eqR eqB))
  onS : (mb : Maybe ℕ) → slotVal er s ≡ mb →
        Σ ℕ (λ k → slotVal er s ≡ just k ×
                   room (cap g) r2l ≡ true ×
                   r ≡ rc il j l2r (snoc r2l (pay k)) el er)
  onS nothing eqS rewrite eqB | eqS = ⊥-elim (wait≢go eq)
  onS (just k) eqS = onR k eqS (room (cap g) r2l) refl

pick0R : ∀ g il ir (l2r r2l : List Tok) el er j r →
         lookB (codeR g) ir ≡ just (bPick0 j) →
         reactR g (rc il ir l2r r2l el er) ≡ AGo r →
         room (cap g) r2l ≡ true ×
         r ≡ rc il j l2r (snoc r2l (lab false)) el er
pick0R g il ir l2r r2l el er j r eqB eq = onR (room (cap g) r2l) refl
  where
  onR : (b : Bool) → room (cap g) r2l ≡ b →
        room (cap g) r2l ≡ true ×
        r ≡ rc il j l2r (snoc r2l (lab false)) el er
  onR false eqR rewrite eqB | eqR = ⊥-elim (wait≢go eq)
  onR true eqR =
    eqR , ago-inj (trans (sym eq)
      (reactR-pick0 g il ir l2r r2l el er j eqR eqB))

pick1R : ∀ g il ir (l2r r2l : List Tok) el er j r →
         lookB (codeR g) ir ≡ just (bPick1 j) →
         reactR g (rc il ir l2r r2l el er) ≡ AGo r →
         room (cap g) r2l ≡ true ×
         r ≡ rc il j l2r (snoc r2l (lab true)) el er
pick1R g il ir l2r r2l el er j r eqB eq = onR (room (cap g) r2l) refl
  where
  onR : (b : Bool) → room (cap g) r2l ≡ b →
        room (cap g) r2l ≡ true ×
        r ≡ rc il j l2r (snoc r2l (lab true)) el er
  onR false eqR rewrite eqB | eqR = ⊥-elim (wait≢go eq)
  onR true eqR =
    eqR , ago-inj (trans (sym eq)
      (reactR-pick1 g il ir l2r r2l el er j eqR eqB))

getR : ∀ g il ir (l2r r2l : List Tok) el er t s i r →
       lookB (codeR g) ir ≡ just (bGet t s i) →
       reactR g (rc il ir l2r r2l el er) ≡ AGo r →
       Σ ℕ (λ k → Σ (List Tok) (λ rest → Σ Atom (λ a →
         l2r ≡ pay k ∷ rest ×
         nthA (alpha g) k ≡ just a ×
         fits t a ≡ true ×
         r ≡ rc il i rest r2l el (setNth s (suc k) er))))
getR g il ir l2r r2l el er t s i r eqB eq = onQ l2r refl
  where
  onQ : (q : List Tok) → l2r ≡ q →
        Σ ℕ (λ k → Σ (List Tok) (λ rest → Σ Atom (λ a →
          l2r ≡ pay k ∷ rest ×
          nthA (alpha g) k ≡ just a ×
          fits t a ≡ true ×
          r ≡ rc il i rest r2l el (setNth s (suc k) er))))
  onQ [] eqq rewrite eqB | eqq = ⊥-elim (wait≢go eq)
  onQ (lab _ ∷ _) eqq rewrite eqB | eqq = ⊥-elim (bad≢go eq)
  onQ (pay k ∷ rest) eqq = onA (nthA (alpha g) k) refl
    where
    onA : (mb : Maybe Atom) → nthA (alpha g) k ≡ mb →
          Σ ℕ (λ k′ → Σ (List Tok) (λ rest′ → Σ Atom (λ a →
            l2r ≡ pay k′ ∷ rest′ ×
            nthA (alpha g) k′ ≡ just a ×
            fits t a ≡ true ×
            r ≡ rc il i rest′ r2l el (setNth s (suc k′) er))))
    onA nothing eqA rewrite eqB | eqq | eqA = ⊥-elim (bad≢go eq)
    onA (just a) eqA = onF (fits t a) refl
      where
      onF : (b : Bool) → fits t a ≡ b →
            Σ ℕ (λ k′ → Σ (List Tok) (λ rest′ → Σ Atom (λ a′ →
              l2r ≡ pay k′ ∷ rest′ ×
              nthA (alpha g) k′ ≡ just a′ ×
              fits t a′ ≡ true ×
              r ≡ rc il i rest′ r2l el (setNth s (suc k′) er))))
      onF false eqF rewrite eqB | eqq | eqA | eqF = ⊥-elim (bad≢go eq)
      onF true eqF =
        let moved = subst (λ q → reactR g (rc il ir q r2l el er) ≡ AGo r) eqq eq
            tgt = ago-inj (trans (sym moved)
                    (reactR-get g il ir k rest r2l el er t s a i eqA eqF eqB))
        in k , rest , a , eqq , eqA , eqF , tgt

coverR : ∀ g il ir (l2r r2l : List Tok) el er i j r →
         lookB (codeR g) ir ≡ just (bCover i j) →
         reactR g (rc il ir l2r r2l el er) ≡ AGo r →
         Σ (List Tok) (λ rest →
           (l2r ≡ lab false ∷ rest × r ≡ rc il i rest r2l el er) ⊎
           (l2r ≡ lab true ∷ rest × r ≡ rc il j rest r2l el er))
coverR g il ir l2r r2l el er i j r eqB eq = onQ l2r refl
  where
  onQ : (q : List Tok) → l2r ≡ q →
        Σ (List Tok) (λ rest →
          (l2r ≡ lab false ∷ rest × r ≡ rc il i rest r2l el er) ⊎
          (l2r ≡ lab true ∷ rest × r ≡ rc il j rest r2l el er))
  onQ [] eqq rewrite eqB | eqq = ⊥-elim (wait≢go eq)
  onQ (pay _ ∷ _) eqq rewrite eqB | eqq = ⊥-elim (bad≢go eq)
  onQ (lab false ∷ rest) eqq =
    let moved = subst (λ q → reactR g (rc il ir q r2l el er) ≡ AGo r) eqq eq
        tgt = ago-inj (trans (sym moved)
                (reactR-cover0 g il ir rest r2l el er i j eqB))
    in rest , inj₁ (eqq , tgt)
  onQ (lab true ∷ rest) eqq =
    let moved = subst (λ q → reactR g (rc il ir q r2l el er) ≡ AGo r) eqq eq
        tgt = ago-inj (trans (sym moved)
                (reactR-cover1 g il ir rest r2l el er i j eqB))
    in rest , inj₂ (eqq , tgt)

igetR : ∀ g il ir (l2r r2l : List Tok) el er s i j r →
        lookB (codeR g) ir ≡ just (bIget s i j) →
        reactR g (rc il ir l2r r2l el er) ≡ AGo r →
        Σ ℕ (λ k → Σ (List Tok) (λ rest →
          (l2r ≡ pay k ∷ rest × nthA (alpha g) k ≡ just (aBit false) ×
           r ≡ rc il i rest r2l el (setNth s (suc k) er)) ⊎
          (l2r ≡ pay k ∷ rest × nthA (alpha g) k ≡ just (aBit true) ×
           r ≡ rc il j rest r2l el (setNth s (suc k) er))))
igetR g il ir l2r r2l el er s i j r eqB eq = onQ l2r refl
  where
  onQ : (q : List Tok) → l2r ≡ q →
        Σ ℕ (λ k → Σ (List Tok) (λ rest →
          (l2r ≡ pay k ∷ rest × nthA (alpha g) k ≡ just (aBit false) ×
           r ≡ rc il i rest r2l el (setNth s (suc k) er)) ⊎
          (l2r ≡ pay k ∷ rest × nthA (alpha g) k ≡ just (aBit true) ×
           r ≡ rc il j rest r2l el (setNth s (suc k) er))))
  onQ [] eqq rewrite eqB | eqq = ⊥-elim (wait≢go eq)
  onQ (lab _ ∷ _) eqq rewrite eqB | eqq = ⊥-elim (bad≢go eq)
  onQ (pay k ∷ rest) eqq = onA (nthA (alpha g) k) refl
    where
    onA : (mb : Maybe Atom) → nthA (alpha g) k ≡ mb →
          Σ ℕ (λ k′ → Σ (List Tok) (λ rest′ →
            (l2r ≡ pay k′ ∷ rest′ × nthA (alpha g) k′ ≡ just (aBit false) ×
             r ≡ rc il i rest′ r2l el (setNth s (suc k′) er)) ⊎
            (l2r ≡ pay k′ ∷ rest′ × nthA (alpha g) k′ ≡ just (aBit true) ×
             r ≡ rc il j rest′ r2l el (setNth s (suc k′) er))))
    onA nothing eqA rewrite eqB | eqq | eqA = ⊥-elim (bad≢go eq)
    onA (just (aNat _)) eqA rewrite eqB | eqq | eqA = ⊥-elim (bad≢go eq)
    onA (just (aCon _)) eqA rewrite eqB | eqq | eqA = ⊥-elim (bad≢go eq)
    onA (just (aBit false)) eqA =
      let moved = subst (λ q → reactR g (rc il ir q r2l el er) ≡ AGo r) eqq eq
          tgt = ago-inj (trans (sym moved)
                  (reactR-iget0 g il ir k rest r2l el er s i j eqA eqB))
      in k , rest , inj₁ (eqq , eqA , tgt)
    onA (just (aBit true)) eqA =
      let moved = subst (λ q → reactR g (rc il ir q r2l el er) ≡ AGo r) eqq eq
          tgt = ago-inj (trans (sym moved)
                  (reactR-iget1 g il ir k rest r2l el er s i j eqA eqB))
      in k , rest , inj₂ (eqq , eqA , tgt)

mgetR : ∀ g il ir (l2r r2l : List Tok) el er t s arms r →
        lookB (codeR g) ir ≡ just (bMget t s arms) →
        reactR g (rc il ir l2r r2l el er) ≡ AGo r →
        Σ ℕ (λ k → Σ (List Tok) (λ rest → Σ Atom (λ a → Σ String (λ name →
          Σ ℕ (λ j →
          l2r ≡ pay k ∷ rest ×
          nthA (alpha g) k ≡ just a ×
          fits t a ≡ true ×
          conOf a ≡ just name ×
          armTo name arms ≡ just j ×
          r ≡ rc il j rest r2l el (setNth s (suc k) er))))))
mgetR g il ir l2r r2l el er t s arms r eqB eq = onQ l2r refl
  where
  onQ : (q : List Tok) → l2r ≡ q →
        Σ ℕ (λ k → Σ (List Tok) (λ rest → Σ Atom (λ a → Σ String (λ name →
          Σ ℕ (λ j →
          l2r ≡ pay k ∷ rest ×
          nthA (alpha g) k ≡ just a ×
          fits t a ≡ true ×
          conOf a ≡ just name ×
          armTo name arms ≡ just j ×
          r ≡ rc il j rest r2l el (setNth s (suc k) er))))))
  onQ [] eqq rewrite eqB | eqq = ⊥-elim (wait≢go eq)
  onQ (lab _ ∷ _) eqq rewrite eqB | eqq = ⊥-elim (bad≢go eq)
  onQ (pay k ∷ rest) eqq = onA (nthA (alpha g) k) refl
    where
    onA : (mb : Maybe Atom) → nthA (alpha g) k ≡ mb →
          Σ ℕ (λ k′ → Σ (List Tok) (λ rest′ → Σ Atom (λ a → Σ String (λ name →
            Σ ℕ (λ j →
            l2r ≡ pay k′ ∷ rest′ ×
            nthA (alpha g) k′ ≡ just a ×
            fits t a ≡ true ×
            conOf a ≡ just name ×
            armTo name arms ≡ just j ×
            r ≡ rc il j rest′ r2l el (setNth s (suc k′) er))))))
    onA nothing eqA rewrite eqB | eqq | eqA = ⊥-elim (bad≢go eq)
    onA (just a) eqA = onF (fits t a) refl
      where
      onF : (b : Bool) → fits t a ≡ b →
            Σ ℕ (λ k′ → Σ (List Tok) (λ rest′ → Σ Atom (λ a′ → Σ String (λ name →
              Σ ℕ (λ j →
              l2r ≡ pay k′ ∷ rest′ ×
              nthA (alpha g) k′ ≡ just a′ ×
              fits t a′ ≡ true ×
              conOf a′ ≡ just name ×
              armTo name arms ≡ just j ×
              r ≡ rc il j rest′ r2l el (setNth s (suc k′) er))))))
      onF false eqF rewrite eqB | eqq | eqA | eqF = ⊥-elim (bad≢go eq)
      onF true eqF = onC (conOf a) refl
        where
        onC : (mb : Maybe String) → conOf a ≡ mb →
              Σ ℕ (λ k′ → Σ (List Tok) (λ rest′ → Σ Atom (λ a′ → Σ String (λ name →
                Σ ℕ (λ j →
                l2r ≡ pay k′ ∷ rest′ ×
                nthA (alpha g) k′ ≡ just a′ ×
                fits t a′ ≡ true ×
                conOf a′ ≡ just name ×
                armTo name arms ≡ just j ×
                r ≡ rc il j rest′ r2l el (setNth s (suc k′) er))))))
        onC nothing eqC rewrite eqB | eqq | eqA | eqF | eqC = ⊥-elim (bad≢go eq)
        onC (just name) eqC = onJ (armTo name arms) refl
          where
          onJ : (mb : Maybe ℕ) → armTo name arms ≡ mb →
                Σ ℕ (λ k′ → Σ (List Tok) (λ rest′ → Σ Atom (λ a′ → Σ String (λ name′ →
                  Σ ℕ (λ j →
                  l2r ≡ pay k′ ∷ rest′ ×
                  nthA (alpha g) k′ ≡ just a′ ×
                  fits t a′ ≡ true ×
                  conOf a′ ≡ just name′ ×
                  armTo name′ arms ≡ just j ×
                  r ≡ rc il j rest′ r2l el (setNth s (suc k′) er))))))
          onJ nothing eqJ rewrite eqB | eqq | eqA | eqF | eqC | eqJ =
            ⊥-elim (bad≢go eq)
          onJ (just j) eqJ =
            let moved = subst (λ q → reactR g (rc il ir q r2l el er) ≡ AGo r) eqq eq
                tgt = ago-inj (trans (sym moved)
                        (reactR-mget g il ir k rest r2l el er t s arms a name j
                          eqA eqF eqC eqJ eqB))
            in k , rest , a , name , j , eqq , eqA , eqF , eqC , eqJ , tgt

------------------------------------------------------------------------
-- Every infinite run of a two-party buffered meeting is already fair.
--
-- Φ of a side is the room left in the queue it sends into, plus the
-- messages waiting in the queue it receives from. A step of that side
-- spends exactly one, so a stretch of its steps is at most Φ long.
-- An infinite run that never finishes therefore takes both sides
-- infinitely often. A fairness clause would be a no-op.
--
-- `every-run-fair` is the implication the corollary uses: a run that
-- is not eventually final takes both sides infinitely often. The
-- classical sum (eventually final, or both sides recur) is proved
-- under double negation. A bare case split would decide whether an
-- arbitrary coinductive run ever finishes, which the finite bound on
-- a one-sided stretch does not decide.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Fair where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-mono-≤; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)

open import Muro.AsyncRec
  using ( Atom; aNat; aBit; aCon
        ; Tag
        ; Block; bDone; bStop; bPut; bEcho; bGrow; bGet; bPick0; bPick1
        ; bCover; bIget; bMget
        ; Tok; pay; lab
        ; RConf; rc; Graph
        ; Act; AWait; ABad; AGo
        ; Fault
        ; reactL; reactR; reactL′; reactR′; onL; onR; enqL; enqR
        ; lookB; room; lt; snoc
        ; l2rOf; r2lOf; ilOf; irOf; elOf; erOf; halted
        ; findA; nthA; slotVal; fits; setNth; conOf; armTo
        ; init
        ; Reach
        )
open Graph
open import Muro.Temporal
  using ( Who; lside; rside; fin
        ; Step; stepL; stepR; finish
        ; Path; head; tail
        ; IsRun; step; rest
        ; Eventually; hereE; thereE
        )
open import Muro.Temporal.Graph using (reached-wf; Wf)
open Wf using (l2r≤; r2l≤)

------------------------------------------------------------------------
-- Φ. Left sends into l2r and receives from r2l. Right is the swap.
------------------------------------------------------------------------

phiL : Graph → RConf → ℕ
phiL g c = (cap g ∸ length (l2rOf c)) + length (r2lOf c)

phiR : Graph → RConf → ℕ
phiR g c = (cap g ∸ length (r2lOf c)) + length (l2rOf c)

lt-sound : ∀ m n → lt m n ≡ true → m < n
lt-sound zero zero ()
lt-sound zero (suc _) _ = s≤s z≤n
lt-sound (suc _) zero ()
lt-sound (suc m) (suc n) eq = s≤s (lt-sound m n eq)

∸-suc-lt : ∀ cap n → n < cap → cap ∸ n ≡ suc (cap ∸ suc n)
∸-suc-lt zero zero ()
∸-suc-lt zero (suc _) ()
∸-suc-lt (suc _) zero _ = refl
∸-suc-lt (suc cap) (suc n) (s≤s lt′) = ∸-suc-lt cap n lt′

length-snoc : ∀ xs t → length (snoc xs t) ≡ suc (length xs)
length-snoc [] _ = refl
length-snoc (_ ∷ xs) t = cong suc (length-snoc xs t)

-- `_+_` recurses on the left, so the successor on the right is a lemma.
+suc : ∀ a m → a + suc m ≡ suc (a + m)
+suc zero m = refl
+suc (suc a) m = cong suc (+suc a m)

∸-≤ : ∀ a b → a ∸ b ≤ a
∸-≤ zero zero = ≤-refl
∸-≤ zero (suc _) = z≤n
∸-≤ (suc a) zero = ≤-refl
∸-≤ (suc a) (suc b) = ≤-trans (∸-≤ a b) (n≤1+n a)

-- A configuration reachable from the start is well formed, so both
-- queues have length at most `cap`, and Φ is at most twice the buffer.
phiL-bound : ∀ {g c} → Reach g (init g) c → phiL g c ≤ cap g + cap g
phiL-bound {g} {c} r =
  +-mono-≤ (∸-≤ (cap g) (length (l2rOf c))) (r2l≤ (reached-wf r))

phiR-bound : ∀ {g c} → Reach g (init g) c → phiR g c ≤ cap g + cap g
phiR-bound {g} {c} r =
  +-mono-≤ (∸-≤ (cap g) (length (r2lOf c))) (l2r≤ (reached-wf r))

------------------------------------------------------------------------
-- One step spends one unit of Φ. A send that fits lengthens the
-- outgoing queue; a receive shortens the incoming one.
------------------------------------------------------------------------

enqL-phi : ∀ {g il ir l2r r2l el er t i} →
           room (cap g) l2r ≡ true →
           phiL g (rc il ir l2r r2l el er) ≡
           suc (phiL g (rc i ir (snoc l2r t) r2l el er))
enqL-phi {g} {l2r = l2r} {t = t} rm
  rewrite length-snoc l2r t
        | ∸-suc-lt (cap g) (length l2r) (lt-sound (length l2r) (cap g) rm)
  = refl

enqR-phi : ∀ {g il ir l2r r2l el er t i} →
           room (cap g) r2l ≡ true →
           phiR g (rc il ir l2r r2l el er) ≡
           suc (phiR g (rc il i l2r (snoc r2l t) el er))
enqR-phi {g} {r2l = r2l} {t = t} rm
  rewrite length-snoc r2l t
        | ∸-suc-lt (cap g) (length r2l) (lt-sound (length r2l) (cap g) rm)
  = refl

recvL-phi : ∀ {g il ir l2r x rest el er i′ el′} →
            phiL g (rc il ir l2r (x ∷ rest) el er) ≡
            suc (phiL g (rc i′ ir l2r rest el′ er))
recvL-phi {g} {l2r = l2r} {rest = rest}
  rewrite +suc (cap g ∸ length l2r) (length rest) = refl

recvR-phi : ∀ {g il ir x rest r2l el er i′ er′} →
            phiR g (rc il ir (x ∷ rest) r2l el er) ≡
            suc (phiR g (rc il i′ rest r2l el er′))
recvR-phi {g} {rest = rest} {r2l = r2l}
  rewrite +suc (cap g ∸ length r2l) (length rest) = refl

wait≢go : ∀ {d} → AWait ≡ AGo d → ⊥
wait≢go ()

bad≢go : ∀ {f d} → ABad f ≡ AGo d → ⊥
bad≢go ()

-- Each clause follows one `with` of `onL`. The `AGo` branch is an
-- enqueue or a receive, and `refl` names the configuration it builds.
putPhi : ∀ {g il ir l2r r2l el er a i d} →
         onL g (rc il ir l2r r2l el er) (bPut a i) ≡ AGo d →
         phiL g (rc il ir l2r r2l el er) ≡ suc (phiL g d)
putPhi {g} {a = a} eq with findA a (alpha g)
putPhi eq | nothing = ⊥-elim (bad≢go eq)
putPhi {g} {l2r = l2r} eq | just k with room (cap g) l2r in rm
putPhi eq | just k | false = ⊥-elim (wait≢go eq)
putPhi {g} {il} {ir} {l2r} {r2l} {el} {er} {i = i} refl | just k | true =
  enqL-phi {g} {il} {ir} {l2r} {r2l} {el} {er} {pay k} {i} rm

echoPhi : ∀ {g il ir l2r r2l el er s i d} →
          onL g (rc il ir l2r r2l el er) (bEcho s i) ≡ AGo d →
          phiL g (rc il ir l2r r2l el er) ≡ suc (phiL g d)
echoPhi {g} {el = el} {s = s} eq with slotVal el s
echoPhi eq | nothing = ⊥-elim (wait≢go eq)
echoPhi {g} {l2r = l2r} eq | just k with room (cap g) l2r in rm
echoPhi eq | just k | false = ⊥-elim (wait≢go eq)
echoPhi {g} {il} {ir} {l2r} {r2l} {el} {er} {i = i} refl | just k | true =
  enqL-phi {g} {il} {ir} {l2r} {r2l} {el} {er} {pay k} {i} rm

growPhi : ∀ {g il ir l2r r2l el er s i d} →
          onL g (rc il ir l2r r2l el er) (bGrow s i) ≡ AGo d →
          phiL g (rc il ir l2r r2l el er) ≡ suc (phiL g d)
growPhi {g} {el = el} {s = s} eq with slotVal el s
growPhi eq | nothing = ⊥-elim (wait≢go eq)
growPhi {g} eq | just k with nthA (alpha g) k
growPhi eq | just _ | nothing = ⊥-elim (wait≢go eq)
growPhi eq | just _ | just (aBit _) = ⊥-elim (wait≢go eq)
growPhi eq | just _ | just (aCon _) = ⊥-elim (wait≢go eq)
growPhi {g} eq | just _ | just (aNat m) with findA (aNat (suc m)) (alpha g)
growPhi eq | just _ | just (aNat _) | nothing = ⊥-elim (bad≢go eq)
growPhi {g} {l2r = l2r} eq | just _ | just (aNat _) | just j
  with room (cap g) l2r in rm
growPhi eq | just _ | just (aNat _) | just _ | false = ⊥-elim (wait≢go eq)
growPhi {g} {il} {ir} {l2r} {r2l} {el} {er} {i = i} refl
  | just _ | just (aNat _) | just j | true =
  enqL-phi {g} {il} {ir} {l2r} {r2l} {el} {er} {pay j} {i} rm

pick0Phi : ∀ {g il ir l2r r2l el er i d} →
           onL g (rc il ir l2r r2l el er) (bPick0 i) ≡ AGo d →
           phiL g (rc il ir l2r r2l el er) ≡ suc (phiL g d)
pick0Phi {g} {l2r = l2r} eq with room (cap g) l2r in rm
pick0Phi eq | false = ⊥-elim (wait≢go eq)
pick0Phi {g} {il} {ir} {l2r} {r2l} {el} {er} {i = i} refl | true =
  enqL-phi {g} {il} {ir} {l2r} {r2l} {el} {er} {lab false} {i} rm

pick1Phi : ∀ {g il ir l2r r2l el er i d} →
           onL g (rc il ir l2r r2l el er) (bPick1 i) ≡ AGo d →
           phiL g (rc il ir l2r r2l el er) ≡ suc (phiL g d)
pick1Phi {g} {l2r = l2r} eq with room (cap g) l2r in rm
pick1Phi eq | false = ⊥-elim (wait≢go eq)
pick1Phi {g} {il} {ir} {l2r} {r2l} {el} {er} {i = i} refl | true =
  enqL-phi {g} {il} {ir} {l2r} {r2l} {el} {er} {lab true} {i} rm

getPhi : ∀ {g il ir l2r r2l el er t s i d} →
         onL g (rc il ir l2r r2l el er) (bGet t s i) ≡ AGo d →
         phiL g (rc il ir l2r r2l el er) ≡ suc (phiL g d)
getPhi {r2l = r2l} eq with r2l
getPhi eq | [] = ⊥-elim (wait≢go eq)
getPhi eq | lab _ ∷ _ = ⊥-elim (bad≢go eq)
getPhi {g} {t = t} eq | pay k ∷ rest with nthA (alpha g) k
getPhi eq | pay _ ∷ _ | nothing = ⊥-elim (bad≢go eq)
getPhi {t = t} eq | pay _ ∷ _ | just a with fits t a
getPhi eq | pay _ ∷ _ | just _ | false = ⊥-elim (bad≢go eq)
getPhi {g} {il} {ir} {l2r} {el = el} {er} {s = s} {i = i} refl
  | pay k ∷ rest | just _ | true =
  recvL-phi {g} {il} {ir} {l2r} {pay k} {rest} {el} {er} {i}
            {setNth s (suc k) el}

coverPhi : ∀ {g il ir l2r r2l el er i j d} →
           onL g (rc il ir l2r r2l el er) (bCover i j) ≡ AGo d →
           phiL g (rc il ir l2r r2l el er) ≡ suc (phiL g d)
coverPhi {r2l = r2l} eq with r2l
coverPhi eq | [] = ⊥-elim (wait≢go eq)
coverPhi eq | pay _ ∷ _ = ⊥-elim (bad≢go eq)
coverPhi {g} {il} {ir} {l2r} {el = el} {er} {i = i} refl | lab false ∷ rest =
  recvL-phi {g} {il} {ir} {l2r} {lab false} {rest} {el} {er} {i} {el}
coverPhi {g} {il} {ir} {l2r} {el = el} {er} {j = j} refl | lab true ∷ rest =
  recvL-phi {g} {il} {ir} {l2r} {lab true} {rest} {el} {er} {j} {el}

igetPhi : ∀ {g il ir l2r r2l el er s i j d} →
          onL g (rc il ir l2r r2l el er) (bIget s i j) ≡ AGo d →
          phiL g (rc il ir l2r r2l el er) ≡ suc (phiL g d)
igetPhi {r2l = r2l} eq with r2l
igetPhi eq | [] = ⊥-elim (wait≢go eq)
igetPhi eq | lab _ ∷ _ = ⊥-elim (bad≢go eq)
igetPhi {g} eq | pay k ∷ rest with nthA (alpha g) k
igetPhi eq | pay _ ∷ _ | nothing = ⊥-elim (bad≢go eq)
igetPhi eq | pay _ ∷ _ | just (aNat _) = ⊥-elim (bad≢go eq)
igetPhi eq | pay _ ∷ _ | just (aCon _) = ⊥-elim (bad≢go eq)
igetPhi {g} {il} {ir} {l2r} {el = el} {er} {s = s} {i = i} refl
  | pay k ∷ rest | just (aBit false) =
  recvL-phi {g} {il} {ir} {l2r} {pay k} {rest} {el} {er} {i}
            {setNth s (suc k) el}
igetPhi {g} {il} {ir} {l2r} {el = el} {er} {s = s} {j = j} refl
  | pay k ∷ rest | just (aBit true) =
  recvL-phi {g} {il} {ir} {l2r} {pay k} {rest} {el} {er} {j}
            {setNth s (suc k) el}

mgetPhi : ∀ {g il ir l2r r2l el er t s arms d} →
          onL g (rc il ir l2r r2l el er) (bMget t s arms) ≡ AGo d →
          phiL g (rc il ir l2r r2l el er) ≡ suc (phiL g d)
mgetPhi {r2l = r2l} eq with r2l
mgetPhi eq | [] = ⊥-elim (wait≢go eq)
mgetPhi eq | lab _ ∷ _ = ⊥-elim (bad≢go eq)
mgetPhi {g} {t = t} eq | pay k ∷ rest with nthA (alpha g) k
mgetPhi eq | pay _ ∷ _ | nothing = ⊥-elim (bad≢go eq)
mgetPhi {t = t} eq | pay _ ∷ _ | just a with fits t a
mgetPhi eq | pay _ ∷ _ | just _ | false = ⊥-elim (bad≢go eq)
mgetPhi {arms = arms} eq | pay _ ∷ _ | just a | true with conOf a
mgetPhi eq | pay _ ∷ _ | just _ | true | nothing = ⊥-elim (bad≢go eq)
mgetPhi {arms = arms} eq | pay _ ∷ _ | just _ | true | just name
  with armTo name arms
mgetPhi eq | pay _ ∷ _ | just _ | true | just _ | nothing = ⊥-elim (bad≢go eq)
mgetPhi {g} {il} {ir} {l2r} {el = el} {er} {s = s} refl
  | pay k ∷ rest | just _ | true | just _ | just j =
  recvL-phi {g} {il} {ir} {l2r} {pay k} {rest} {el} {er} {j}
            {setNth s (suc k) el}

onL-phi : ∀ {g c b d} → onL g c b ≡ AGo d → phiL g c ≡ suc (phiL g d)
onL-phi {c = rc _ _ _ _ _ _} {bDone} eq = ⊥-elim (wait≢go eq)
onL-phi {c = rc _ _ _ _ _ _} {bStop} eq = ⊥-elim (wait≢go eq)
onL-phi {g} {rc il ir l2r r2l el er} {bPut a i} eq =
  putPhi {g} {il} {ir} {l2r} {r2l} {el} {er} {a} {i} eq
onL-phi {g} {rc il ir l2r r2l el er} {bEcho s i} eq =
  echoPhi {g} {il} {ir} {l2r} {r2l} {el} {er} {s} {i} eq
onL-phi {g} {rc il ir l2r r2l el er} {bGrow s i} eq =
  growPhi {g} {il} {ir} {l2r} {r2l} {el} {er} {s} {i} eq
onL-phi {g} {rc il ir l2r r2l el er} {bGet t s i} eq =
  getPhi {g} {il} {ir} {l2r} {r2l} {el} {er} {t} {s} {i} eq
onL-phi {g} {rc il ir l2r r2l el er} {bPick0 i} eq =
  pick0Phi {g} {il} {ir} {l2r} {r2l} {el} {er} {i} eq
onL-phi {g} {rc il ir l2r r2l el er} {bPick1 i} eq =
  pick1Phi {g} {il} {ir} {l2r} {r2l} {el} {er} {i} eq
onL-phi {g} {rc il ir l2r r2l el er} {bCover i j} eq =
  coverPhi {g} {il} {ir} {l2r} {r2l} {el} {er} {i} {j} eq
onL-phi {g} {rc il ir l2r r2l el er} {bIget s i j} eq =
  igetPhi {g} {il} {ir} {l2r} {r2l} {el} {er} {s} {i} {j} eq
onL-phi {g} {rc il ir l2r r2l el er} {bMget t s arms} eq =
  mgetPhi {g} {il} {ir} {l2r} {r2l} {el} {er} {t} {s} {arms} eq

-- Right side. The same blocks, writing the other queue.
putPhiR : ∀ {g il ir l2r r2l el er a i d} →
          onR g (rc il ir l2r r2l el er) (bPut a i) ≡ AGo d →
          phiR g (rc il ir l2r r2l el er) ≡ suc (phiR g d)
putPhiR {g} {a = a} eq with findA a (alpha g)
putPhiR eq | nothing = ⊥-elim (bad≢go eq)
putPhiR {g} {r2l = r2l} eq | just k with room (cap g) r2l in rm
putPhiR eq | just k | false = ⊥-elim (wait≢go eq)
putPhiR {g} {il} {ir} {l2r} {r2l} {el} {er} {i = i} refl | just k | true =
  enqR-phi {g} {il} {ir} {l2r} {r2l} {el} {er} {pay k} {i} rm

echoPhiR : ∀ {g il ir l2r r2l el er s i d} →
           onR g (rc il ir l2r r2l el er) (bEcho s i) ≡ AGo d →
           phiR g (rc il ir l2r r2l el er) ≡ suc (phiR g d)
echoPhiR {g} {er = er} {s = s} eq with slotVal er s
echoPhiR eq | nothing = ⊥-elim (wait≢go eq)
echoPhiR {g} {r2l = r2l} eq | just k with room (cap g) r2l in rm
echoPhiR eq | just k | false = ⊥-elim (wait≢go eq)
echoPhiR {g} {il} {ir} {l2r} {r2l} {el} {er} {i = i} refl | just k | true =
  enqR-phi {g} {il} {ir} {l2r} {r2l} {el} {er} {pay k} {i} rm

growPhiR : ∀ {g il ir l2r r2l el er s i d} →
           onR g (rc il ir l2r r2l el er) (bGrow s i) ≡ AGo d →
           phiR g (rc il ir l2r r2l el er) ≡ suc (phiR g d)
growPhiR {g} {er = er} {s = s} eq with slotVal er s
growPhiR eq | nothing = ⊥-elim (wait≢go eq)
growPhiR {g} eq | just k with nthA (alpha g) k
growPhiR eq | just _ | nothing = ⊥-elim (wait≢go eq)
growPhiR eq | just _ | just (aBit _) = ⊥-elim (wait≢go eq)
growPhiR eq | just _ | just (aCon _) = ⊥-elim (wait≢go eq)
growPhiR {g} eq | just _ | just (aNat m) with findA (aNat (suc m)) (alpha g)
growPhiR eq | just _ | just (aNat _) | nothing = ⊥-elim (bad≢go eq)
growPhiR {g} {r2l = r2l} eq | just _ | just (aNat _) | just j
  with room (cap g) r2l in rm
growPhiR eq | just _ | just (aNat _) | just _ | false = ⊥-elim (wait≢go eq)
growPhiR {g} {il} {ir} {l2r} {r2l} {el} {er} {i = i} refl
  | just _ | just (aNat _) | just j | true =
  enqR-phi {g} {il} {ir} {l2r} {r2l} {el} {er} {pay j} {i} rm

pick0PhiR : ∀ {g il ir l2r r2l el er i d} →
            onR g (rc il ir l2r r2l el er) (bPick0 i) ≡ AGo d →
            phiR g (rc il ir l2r r2l el er) ≡ suc (phiR g d)
pick0PhiR {g} {r2l = r2l} eq with room (cap g) r2l in rm
pick0PhiR eq | false = ⊥-elim (wait≢go eq)
pick0PhiR {g} {il} {ir} {l2r} {r2l} {el} {er} {i = i} refl | true =
  enqR-phi {g} {il} {ir} {l2r} {r2l} {el} {er} {lab false} {i} rm

pick1PhiR : ∀ {g il ir l2r r2l el er i d} →
            onR g (rc il ir l2r r2l el er) (bPick1 i) ≡ AGo d →
            phiR g (rc il ir l2r r2l el er) ≡ suc (phiR g d)
pick1PhiR {g} {r2l = r2l} eq with room (cap g) r2l in rm
pick1PhiR eq | false = ⊥-elim (wait≢go eq)
pick1PhiR {g} {il} {ir} {l2r} {r2l} {el} {er} {i = i} refl | true =
  enqR-phi {g} {il} {ir} {l2r} {r2l} {el} {er} {lab true} {i} rm

getPhiR : ∀ {g il ir l2r r2l el er t s i d} →
          onR g (rc il ir l2r r2l el er) (bGet t s i) ≡ AGo d →
          phiR g (rc il ir l2r r2l el er) ≡ suc (phiR g d)
getPhiR {l2r = l2r} eq with l2r
getPhiR eq | [] = ⊥-elim (wait≢go eq)
getPhiR eq | lab _ ∷ _ = ⊥-elim (bad≢go eq)
getPhiR {g} {t = t} eq | pay k ∷ rest with nthA (alpha g) k
getPhiR eq | pay _ ∷ _ | nothing = ⊥-elim (bad≢go eq)
getPhiR {t = t} eq | pay _ ∷ _ | just a with fits t a
getPhiR eq | pay _ ∷ _ | just _ | false = ⊥-elim (bad≢go eq)
getPhiR {g} {il} {ir} {r2l = r2l} {el} {er} {s = s} {i = i} refl
  | pay k ∷ rest | just _ | true =
  recvR-phi {g} {il} {ir} {pay k} {rest} {r2l} {el} {er} {i}
            {setNth s (suc k) er}

coverPhiR : ∀ {g il ir l2r r2l el er i j d} →
            onR g (rc il ir l2r r2l el er) (bCover i j) ≡ AGo d →
            phiR g (rc il ir l2r r2l el er) ≡ suc (phiR g d)
coverPhiR {l2r = l2r} eq with l2r
coverPhiR eq | [] = ⊥-elim (wait≢go eq)
coverPhiR eq | pay _ ∷ _ = ⊥-elim (bad≢go eq)
coverPhiR {g} {il} {ir} {r2l = r2l} {el} {er} {i = i} refl | lab false ∷ rest =
  recvR-phi {g} {il} {ir} {lab false} {rest} {r2l} {el} {er} {i} {er}
coverPhiR {g} {il} {ir} {r2l = r2l} {el} {er} {j = j} refl | lab true ∷ rest =
  recvR-phi {g} {il} {ir} {lab true} {rest} {r2l} {el} {er} {j} {er}

igetPhiR : ∀ {g il ir l2r r2l el er s i j d} →
           onR g (rc il ir l2r r2l el er) (bIget s i j) ≡ AGo d →
           phiR g (rc il ir l2r r2l el er) ≡ suc (phiR g d)
igetPhiR {l2r = l2r} eq with l2r
igetPhiR eq | [] = ⊥-elim (wait≢go eq)
igetPhiR eq | lab _ ∷ _ = ⊥-elim (bad≢go eq)
igetPhiR {g} eq | pay k ∷ rest with nthA (alpha g) k
igetPhiR eq | pay _ ∷ _ | nothing = ⊥-elim (bad≢go eq)
igetPhiR eq | pay _ ∷ _ | just (aNat _) = ⊥-elim (bad≢go eq)
igetPhiR eq | pay _ ∷ _ | just (aCon _) = ⊥-elim (bad≢go eq)
igetPhiR {g} {il} {ir} {r2l = r2l} {el} {er} {s = s} {i = i} refl
  | pay k ∷ rest | just (aBit false) =
  recvR-phi {g} {il} {ir} {pay k} {rest} {r2l} {el} {er} {i}
            {setNth s (suc k) er}
igetPhiR {g} {il} {ir} {r2l = r2l} {el} {er} {s = s} {j = j} refl
  | pay k ∷ rest | just (aBit true) =
  recvR-phi {g} {il} {ir} {pay k} {rest} {r2l} {el} {er} {j}
            {setNth s (suc k) er}

mgetPhiR : ∀ {g il ir l2r r2l el er t s arms d} →
           onR g (rc il ir l2r r2l el er) (bMget t s arms) ≡ AGo d →
           phiR g (rc il ir l2r r2l el er) ≡ suc (phiR g d)
mgetPhiR {l2r = l2r} eq with l2r
mgetPhiR eq | [] = ⊥-elim (wait≢go eq)
mgetPhiR eq | lab _ ∷ _ = ⊥-elim (bad≢go eq)
mgetPhiR {g} {t = t} eq | pay k ∷ rest with nthA (alpha g) k
mgetPhiR eq | pay _ ∷ _ | nothing = ⊥-elim (bad≢go eq)
mgetPhiR {t = t} eq | pay _ ∷ _ | just a with fits t a
mgetPhiR eq | pay _ ∷ _ | just _ | false = ⊥-elim (bad≢go eq)
mgetPhiR {arms = arms} eq | pay _ ∷ _ | just a | true with conOf a
mgetPhiR eq | pay _ ∷ _ | just _ | true | nothing = ⊥-elim (bad≢go eq)
mgetPhiR {arms = arms} eq | pay _ ∷ _ | just _ | true | just name
  with armTo name arms
mgetPhiR eq | pay _ ∷ _ | just _ | true | just _ | nothing = ⊥-elim (bad≢go eq)
mgetPhiR {g} {il} {ir} {r2l = r2l} {el} {er} {s = s} refl
  | pay k ∷ rest | just _ | true | just _ | just j =
  recvR-phi {g} {il} {ir} {pay k} {rest} {r2l} {el} {er} {j}
            {setNth s (suc k) er}

onR-phi : ∀ {g c b d} → onR g c b ≡ AGo d → phiR g c ≡ suc (phiR g d)
onR-phi {c = rc _ _ _ _ _ _} {bDone} eq = ⊥-elim (wait≢go eq)
onR-phi {c = rc _ _ _ _ _ _} {bStop} eq = ⊥-elim (wait≢go eq)
onR-phi {g} {rc il ir l2r r2l el er} {bPut a i} eq =
  putPhiR {g} {il} {ir} {l2r} {r2l} {el} {er} {a} {i} eq
onR-phi {g} {rc il ir l2r r2l el er} {bEcho s i} eq =
  echoPhiR {g} {il} {ir} {l2r} {r2l} {el} {er} {s} {i} eq
onR-phi {g} {rc il ir l2r r2l el er} {bGrow s i} eq =
  growPhiR {g} {il} {ir} {l2r} {r2l} {el} {er} {s} {i} eq
onR-phi {g} {rc il ir l2r r2l el er} {bGet t s i} eq =
  getPhiR {g} {il} {ir} {l2r} {r2l} {el} {er} {t} {s} {i} eq
onR-phi {g} {rc il ir l2r r2l el er} {bPick0 i} eq =
  pick0PhiR {g} {il} {ir} {l2r} {r2l} {el} {er} {i} eq
onR-phi {g} {rc il ir l2r r2l el er} {bPick1 i} eq =
  pick1PhiR {g} {il} {ir} {l2r} {r2l} {el} {er} {i} eq
onR-phi {g} {rc il ir l2r r2l el er} {bCover i j} eq =
  coverPhiR {g} {il} {ir} {l2r} {r2l} {el} {er} {i} {j} eq
onR-phi {g} {rc il ir l2r r2l el er} {bIget s i j} eq =
  igetPhiR {g} {il} {ir} {l2r} {r2l} {el} {er} {s} {i} {j} eq
onR-phi {g} {rc il ir l2r r2l el er} {bMget t s arms} eq =
  mgetPhiR {g} {il} {ir} {l2r} {r2l} {el} {er} {t} {s} {arms} eq

reactL-phi : ∀ {g c d} → reactL g c ≡ AGo d → phiL g c ≡ suc (phiL g d)
reactL-phi {g} {c} {d} eq = go (lookB (codeL g) (ilOf c)) refl
  where
  open-eq : ∀ {m} → lookB (codeL g) (ilOf c) ≡ m → reactL′ g c m ≡ AGo d
  open-eq p = subst (λ m → reactL′ g c m ≡ AGo d) p eq
  go : (m : Maybe Block) → lookB (codeL g) (ilOf c) ≡ m →
       phiL g c ≡ suc (phiL g d)
  go nothing p = ⊥-elim (wait≢go (open-eq p))
  go (just b) p = onL-phi {g} {c} {b} (open-eq p)

reactR-phi : ∀ {g c d} → reactR g c ≡ AGo d → phiR g c ≡ suc (phiR g d)
reactR-phi {g} {c} {d} eq = go (lookB (codeR g) (irOf c)) refl
  where
  open-eq : ∀ {m} → lookB (codeR g) (irOf c) ≡ m → reactR′ g c m ≡ AGo d
  open-eq p = subst (λ m → reactR′ g c m ≡ AGo d) p eq
  go : (m : Maybe Block) → lookB (codeR g) (irOf c) ≡ m →
       phiR g c ≡ suc (phiR g d)
  go nothing p = ⊥-elim (wait≢go (open-eq p))
  go (just b) p = onR-phi {g} {c} {b} (open-eq p)

------------------------------------------------------------------------
-- A stretch of one side. `solo-bounded` is the pair of bounds.
------------------------------------------------------------------------

data Stretch (g : Graph) (w : Who) : RConf → RConf → ℕ → Set where
  s-zero : ∀ {c} → Stretch g w c c zero
  s-step : ∀ {a b c n} → Step g a w b → Stretch g w b c n →
           Stretch g w a c (suc n)

soloL : ∀ {g c e n} → Stretch g lside c e n → n ≤ phiL g c
soloL s-zero = z≤n
soloL {g} (s-step {a = a} {b = b} {n = n} (stepL eq) rest) =
  subst (λ k → suc n ≤ k) (sym (reactL-phi {g} {c = a} {d = b} eq))
        (s≤s (soloL rest))

soloR : ∀ {g c e n} → Stretch g rside c e n → n ≤ phiR g c
soloR s-zero = z≤n
soloR {g} (s-step {a = a} {b = b} {n = n} (stepR eq) rest) =
  subst (λ k → suc n ≤ k) (sym (reactR-phi {g} {c = a} {d = b} eq))
        (s≤s (soloR rest))

solo-bounded : (∀ {g c e n} → Stretch g lside c e n → n ≤ phiL g c) ×
               (∀ {g c e n} → Stretch g rside c e n → n ≤ phiR g c)
solo-bounded = soloL , soloR

------------------------------------------------------------------------
-- The next step of the side we are waiting for arrives within Φ of
-- the other side, or the run has already finished. `Recurs` says the
-- side is taken again after that, coinductively.
------------------------------------------------------------------------

Final : Graph → RConf → Set
Final g c = l2rOf c ≡ [] × r2lOf c ≡ [] × halted g c ≡ true

data Found (g : Graph) (w : Who) : Path → Set where
  here : ∀ {π} → Step g (head π) w (head (tail π)) → Found g w π
  there : ∀ {π} → Found g w (tail π) → Found g w π

skip : ∀ {g w π} → Found g w π → Path
skip (here {π} _) = tail π
skip (there f) = skip f

skip-run : ∀ {g w π} → IsRun g π → (f : Found g w π) → IsRun g (skip f)
skip-run r (here _) = rest r
skip-run r (there f) = skip-run (rest r) f

↓suc : ∀ {m n} → m ≡ suc n → n < m
↓suc refl = ≤-refl

-- `finish` is the only `fin` step, and it stutters, so the two
-- endpoints are the same configuration. Matching it here, on
-- variables, is what a split at `head` and `tail` cannot do.
step-final : ∀ {g c d} → Step g c fin d → Final g c × c ≡ d
step-final (finish e1 e2 h) = (e1 , e2 , h) , refl

map⊎ : ∀ {A B C D : Set} → (A → C) → (B → D) → A ⊎ B → C ⊎ D
map⊎ f _ (inj₁ a) = inj₁ (f a)
map⊎ _ g (inj₂ b) = inj₂ (g b)

-- Searching for a left step. A right step spends one unit of Φ_R.
findL : ∀ {g} (π : Path) → IsRun g π → Acc _<_ (phiR g (head π)) →
        Eventually (λ σ → Final g (head σ)) π ⊎ Found g lside π
findL {g} π r (acc wf) with step {g} {π} r
findL π r (acc wf) | lside , stepL eq = inj₂ (here (stepL eq))
findL π r (acc wf) | fin , s = inj₁ (hereE (proj₁ (step-final s)))
findL {g} π r (acc wf) | rside , stepR eq =
  map⊎ thereE there
    (findL (tail π) (rest {g} {π} r)
       (wf (↓suc (reactR-phi {g} {c = head π} {d = head (tail π)} eq))))

findR : ∀ {g} (π : Path) → IsRun g π → Acc _<_ (phiL g (head π)) →
        Eventually (λ σ → Final g (head σ)) π ⊎ Found g rside π
findR {g} π r (acc wf) with step {g} {π} r
findR π r (acc wf) | rside , stepR eq = inj₂ (here (stepR eq))
findR π r (acc wf) | fin , s = inj₁ (hereE (proj₁ (step-final s)))
findR {g} π r (acc wf) | lside , stepL eq =
  map⊎ thereE there
    (findR (tail π) (rest {g} {π} r)
       (wf (↓suc (reactL-phi {g} {c = head π} {d = head (tail π)} eq))))

record Recurs (g : Graph) (w : Who) (π : Path) : Set where
  coinductive
  field
    soon : Found g w π
    later : Recurs g w (skip soon)

open Recurs public

NotFinal : Graph → Path → Set
NotFinal g π = Eventually (λ σ → Final g (head σ)) π → ⊥

nf-tail : ∀ {g π} → NotFinal g π → NotFinal g (tail π)
nf-tail nf ev = nf (thereE ev)

nf-skip : ∀ {g w π} → NotFinal g π → (f : Found g w π) → NotFinal g (skip f)
nf-skip nf (here _) ev = nf (thereE ev)
nf-skip nf (there f) ev = nf-skip (nf-tail nf) f ev

forceL : ∀ {g} (π : Path) → IsRun g π → NotFinal g π → Found g lside π
forceL {g} π r nf with findL π r (<-wellFounded-fast (phiR g (head π)))
... | inj₁ ev = ⊥-elim (nf ev)
... | inj₂ f = f

forceR : ∀ {g} (π : Path) → IsRun g π → NotFinal g π → Found g rside π
forceR {g} π r nf with findR π r (<-wellFounded-fast (phiL g (head π)))
... | inj₁ ev = ⊥-elim (nf ev)
... | inj₂ f = f

recL : ∀ {g} (π : Path) → IsRun g π → NotFinal g π → Recurs g lside π
soon (recL π r nf) = forceL π r nf
later (recL π r nf) =
  recL (skip f) (skip-run r f) (nf-skip nf f)
  where f = forceL π r nf

recR : ∀ {g} (π : Path) → IsRun g π → NotFinal g π → Recurs g rside π
soon (recR π r nf) = forceR π r nf
later (recR π r nf) =
  recR (skip f) (skip-run r f) (nf-skip nf f)
  where f = forceR π r nf

-- A run that never finishes takes the left process infinitely often
-- and the right process infinitely often. The bound is the one-sided
-- stretch, which is read off the run itself.
every-run-fair : ∀ {g π} → IsRun g π → NotFinal g π →
                 Recurs g lside π × Recurs g rside π
every-run-fair r nf = recL _ r nf , recR _ r nf

-- The spec's sum, under double negation. Choosing a side now would
-- decide an unbounded question about the run.
fair-sum : ∀ {g π} → IsRun g π →
           ((Eventually (λ σ → Final g (head σ)) π ⊎
             (Recurs g lside π × Recurs g rside π)) → ⊥) → ⊥
fair-sum {g} {π} r neg =
  neg (inj₂ (every-run-fair r (λ ev → neg (inj₁ ev))))

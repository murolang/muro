------------------------------------------------------------------------
-- The decision for every formula. `always` is the safety scan.
-- `eventually` and `leads_to` are the worklist. Both read the
-- configurations `reachable` lists, and the meeting derivation is the
-- argument `NoStuck`, not a second search.
--
-- `closed-of` is why the liveness theorems apply to that list: it
-- contains the start, a step from a member stays in it, and every
-- member has a chain back to the start.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Decide where

open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe.Base using (Maybe)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; cong)

open import Muro.AsyncRec
  using ( Graph; RConf; Reach; init
        ; Act; AGo; reactL; reactR
        ; View; view; kidsV; Shape
        )
open import Muro.Temporal
  using ( Who; Step; stepL; stepR; finish
        ; StateProp; Formula; always; eventually; leadsTo
        ; Satisfies; NoStuck
        ; Answer; yes; no
        ; Cex
        )
open import Muro.Temporal.Graph
  using ( Node; queued; reachable
        ; any→elem; elem→any
        ; init-out; out-closed
        ; reachable-sound; trace-of
        ; PathTo; pt-here; pt-snoc
        )
open import Muro.Temporal.Live
  using ( Mem; find; mem-elem
        ; Chain; c-nil; End; snocC; end-snoc
        ; Closed; hasInit; shut; spine
        ; LiveF; lev; lto; embed
        ; checkLive; live-sound; live-deny; live-complete
        )
import Muro.Temporal.Safety as Safety
open Safety using (goL-kid; goR-kid)

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- A parent-chain is a cons-chain. `PathTo` grows at the end; `Chain`
-- grows at the front, and `snocC` is the end.
------------------------------------------------------------------------

whoStep : ∀ {g b d w} → Step g b w d → Who
whoStep {w = w} _ = w

toChain : ∀ {g a c xs} → PathTo g a c xs →
          Σ (Chain g a xs) (λ ch → End ch ≡ c)
toChain pt-here = c-nil , refl
toChain {c = c} (pt-snoc pre st) =
  let ch = proj₁ (toChain pre)
      end = proj₂ (toChain pre)
      stepped = subst (λ z → Step _ z (whoStep st) c) (sym end) st
  in snocC ch stepped , end-snoc ch stepped

-- The node whose configuration is `c`, with the parent the search stored.
locate : ∀ {c} (ns : List Node) → Any (_≡_ c) (queued ns) →
         Σ (Maybe (Who × RConf)) (λ p → Any (_≡_ (c , p)) ns)
locate [] ()
locate {c} ((x , p) ∷ ns) (here eq) =
  p , here (cong (λ z → (z , p)) eq)
locate (_ ∷ ns) (there more) =
  proj₁ (locate ns more) , there (proj₂ (locate ns more))

along : ∀ g {c} → Mem c (queued (reachable g)) →
        Σ (List (Who × RConf))
          (λ xs → Σ (Chain g (init g) xs) (λ ch → End ch ≡ c))
along g {c} mem =
  let anyC = elem→any c (queued (reachable g)) (mem-elem mem)
      at = proj₂ (locate (reachable g) anyC)
      built = toChain (proj₂ (trace-of at))
  in proj₁ (trace-of at) , proj₁ built , proj₂ built

-- A real step of a shaped configuration is a child of `view`, and the
-- search emitted every child. The stutter stays where it is.
keep : ∀ g (m : NoStuck g) {c w d} →
       Mem c (queued (reachable g)) → Step g c w d →
       Mem d (queued (reachable g))
keep g m {c} mem (finish _ _ _) = mem
keep g m {c} {d = d} mem (stepL eq) =
  let anyC = elem→any c (queued (reachable g)) (mem-elem mem)
  in find d (queued (reachable g))
       (any→elem (out-closed g anyC (goL-kid eq (m (reachable-sound anyC)))))
keep g m {c} {d = d} mem (stepR eq) =
  let anyC = elem→any c (queued (reachable g)) (mem-elem mem)
  in find d (queued (reachable g))
       (any→elem (out-closed g anyC (goR-kid eq (m (reachable-sound anyC)))))

closed-of : (g : Graph) (m : NoStuck g) → Closed g (queued (reachable g))
hasInit (closed-of g m) =
  find (init g) (queued (reachable g)) (any→elem (init-out g))
shut (closed-of g m) mem st = keep g m mem st
spine (closed-of g m) mem = along g mem

------------------------------------------------------------------------
-- One answer for every formula.
------------------------------------------------------------------------

check : (g : Graph) → NoStuck g → Formula → Answer
check g m (always p) = Safety.check g m p
check g m (eventually p) = checkLive g (queued (reachable g)) (lev p)
check g m (leadsTo p q) = checkLive g (queued (reachable g)) (lto p q)

check-sound : ∀ g (m : NoStuck g) φ → check g m φ ≡ yes → Satisfies g φ
check-sound g m (always p) eq = Safety.check-sound m eq
check-sound g m (eventually p) eq =
  live-sound g (queued (reachable g)) (lev p) eq (closed-of g m)
check-sound g m (leadsTo p q) eq =
  live-sound g (queued (reachable g)) (lto p q) eq (closed-of g m)

-- A refusal is an infinite run that misses the formula. For `always`
-- that run is the breadth-first path extended by `run-exists`. For the
-- two liveness forms it is the coinductive stay in the surviving
-- region, prefixed by the chain from the start when the trigger is not
-- the start.
-- Stable name for the refusal. `cex-sound` gains the `Valid` half;
-- this projection stays the negation.
check-refutes : ∀ g (m : NoStuck g) φ w → check g m φ ≡ no w → ¬ Satisfies g φ
check-refutes g m (always p) w eq = proj₂ (Safety.cex-sound m eq)
check-refutes g m (eventually p) w eq =
  live-deny g (queued (reachable g)) (lev p) w eq (closed-of g m)
check-refutes g m (leadsTo p q) w eq =
  live-deny g (queued (reachable g)) (lto p q) w eq (closed-of g m)

-- The refusal. The liveness half gains `Valid` with the lasso; until
-- then this is the negation `check-refutes` already gives.
cex-sound : ∀ g (m : NoStuck g) φ w → check g m φ ≡ no w → ¬ Satisfies g φ
cex-sound g m φ w eq = check-refutes g m φ w eq

check-complete : ∀ g (m : NoStuck g) φ → Satisfies g φ → check g m φ ≡ yes
check-complete g m (always p) sat = Safety.check-complete m sat
check-complete g m (eventually p) sat =
  live-complete g (queued (reachable g)) (lev p) (closed-of g m) sat
check-complete g m (leadsTo p q) sat =
  live-complete g (queued (reachable g)) (lto p q) (closed-of g m) sat

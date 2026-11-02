------------------------------------------------------------------------
-- `always P`, decided on the reachable graph.
--
-- The configurations `reachable` lists are exactly the ones a run can
-- be at. The first of them, in that breadth-first order, where `P`
-- fails is the counterexample. Its parent chain is the path. Extending
-- that path by `run-exists` at the last configuration is an infinite
-- run on which `P` fails. If none fails, every position of every run
-- satisfies `P`.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Safety where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst; inspect; [_])

open import Muro.AsyncRec
  using ( Graph; RConf; Reach; rhere
        ; View; VFinal; VBad; VGo; view; kidsV; Shape; sh-final
        ; Act; AWait; ABad; AGo; reactL; reactR; merge
        ; l2rOf; r2lOf; halted; init
        )
open import Muro.Temporal
  using ( Who; lside; rside; fin
        ; Step; stepL; stepR; finish
        ; StateProp; Formula; always; eventually; leadsTo
        ; ⟦_⟧
        ; Path; head; tail
        ; IsRun; step; rest
        ; Globally; now; later
        ; Eventually; hereE; thereE
        ; Holds; Satisfies
        ; NoStuck
        ; Cex; finite; lasso
        ; Answer; yes; no
        ; run-exists
        ; snocR
        ; goL-not-final; goR-not-final; isFinalB
        )
open import Muro.Temporal.Graph
  using ( Node; confN; queued; reachable
        ; reachable-sound; reachable-complete
        ; trace-of; PathTo; pt-here; pt-snoc
        )

¬_ : Set → Set
¬ A = A → ⊥

true≢false : true ≡ false → ⊥
true≢false ()

yes≢no : ∀ {w} → yes ≡ no w → ⊥
yes≢no ()

no≢yes : ∀ {w} → no w ≡ yes → ⊥
no≢yes ()

no-inj : ∀ {w w′} → no w ≡ no w′ → w ≡ w′
no-inj refl = refl

------------------------------------------------------------------------
-- A left or right step of a shaped configuration is a child of `view`.
------------------------------------------------------------------------

-- `inspect` freezes `reactR g c ≡ AGo e`, so `view` stays `merge` of
-- the two actions and the left child is the head of that list.
goL-kid : ∀ {g c d} → reactL g c ≡ AGo d → Shape (view g c) →
          Any (_≡_ d) (kidsV (view g c))
goL-kid {g} {c} {d} eq sh with reactR g c
goL-kid {g} {c} {d} eq _ | AGo e rewrite eq = here refl
goL-kid {g} {c} {d} eq _ | AWait rewrite eq = here refl
goL-kid {g} {c} {d} eq sh | ABad f rewrite eq = badShape sh
  where
  badShape : Shape (VBad f) → Any (_≡_ d) []
  badShape ()

goR-kid : ∀ {g c d} → reactR g c ≡ AGo d → Shape (view g c) →
          Any (_≡_ d) (kidsV (view g c))
goR-kid {g} {c} {d} eq sh with reactL g c
goR-kid {g} {c} {d} eq _ | AGo e rewrite eq = there (here refl)
goR-kid {g} {c} {d} eq _ | AWait rewrite eq = here refl
goR-kid {g} {c} {d} eq sh | ABad f = badShape sh
  where
  badShape : Shape (VBad f) → Any (_≡_ d) []
  badShape ()

-- One step keeps a configuration reachable from the start.
take : ∀ {g c w d} → NoStuck g → Reach g (init g) c → Step g c w d →
       Reach g (init g) d
take _ r (finish _ _ _) = r
take m r (stepL eq) = snocR r (goL-kid eq (m r))
take m r (stepR eq) = snocR r (goR-kid eq (m r))

-- Every position of a run that starts reachable stays reachable.
run-reach : ∀ {g π} → NoStuck g → IsRun g π → Reach g (init g) (head π) →
            Globally (λ σ → Reach g (init g) (head σ)) π
now (run-reach _ _ reach) = reach
later (run-reach m r reach) =
  run-reach m (rest r) (take m reach (proj₂ (step r)))

------------------------------------------------------------------------
-- The scan. Structural on the breadth-first list.
------------------------------------------------------------------------

Scan : Graph → StateProp → List Node → Set
Scan g p ns =
  (∀ {c} → Any (_≡_ c) (queued ns) → ⟦ g ⟧ p c ≡ true) ⊎
  Σ Node (λ n → Any (_≡_ n) ns × ⟦ g ⟧ p (confN n) ≡ false)

extend : ∀ {g p n ns} → ⟦ g ⟧ p (confN n) ≡ true →
         (∀ {c} → Any (_≡_ c) (queued ns) → ⟦ g ⟧ p c ≡ true) →
         ∀ {c} → Any (_≡_ c) (queued (n ∷ ns)) → ⟦ g ⟧ p c ≡ true
extend {g} {p} eq rest (here e) = subst (λ x → ⟦ g ⟧ p x ≡ true) (sym e) eq
extend eq rest (there q) = rest q

scan : ∀ g p (ns : List Node) → Scan g p ns
scan g p [] = inj₁ (λ ())
scan g p (n ∷ ns) = on (⟦ g ⟧ p (confN n)) refl
  where
  on : (b : Bool) → ⟦ g ⟧ p (confN n) ≡ b → Scan g p (n ∷ ns)
  on false eq = inj₂ (n , here refl , eq)
  on true eq = join (scan g p ns)
    where
    join : Scan g p ns → Scan g p (n ∷ ns)
    join (inj₁ rest) = inj₁ (extend {g} {p} {n} {ns} eq rest)
    join (inj₂ (m , mem , bad)) = inj₂ (m , there mem , bad)

node→conf : ∀ {n ns} → Any (_≡_ n) ns → Any (_≡_ (confN n)) (queued ns)
node→conf (here eq) = here (cong confN eq)
node→conf (there q) = there (node→conf q)

------------------------------------------------------------------------
-- Reading a `PathTo` as a cons-list, so the unrolling is guarded.
------------------------------------------------------------------------

data Steps (g : Graph) : RConf → RConf → List (Who × RConf) → Set where
  sdone : ∀ {c} → Steps g c c []
  sstep : ∀ {a b c w xs} → Step g a w b → Steps g b c xs →
          Steps g a c ((w , b) ∷ xs)

appendS : ∀ {g a b c w xs} → Steps g a b xs → Step g b w c →
          Steps g a c (xs ++ ((w , c) ∷ []))
appendS sdone st = sstep st sdone
appendS (sstep s rest) st = sstep s (appendS rest st)

toSteps : ∀ {g a c xs} → PathTo g a c xs → Steps g a c xs
toSteps pt-here = sdone
toSteps (pt-snoc pre st) = appendS (toSteps pre) st

walk : ∀ {g a c xs} → Steps g a c xs → Path → Path
head (walk sdone π) = head π
tail (walk sdone π) = tail π
head (walk (sstep {a = a} _ _) _) = a
tail (walk (sstep _ rest) π) = walk rest π

head-sdone : ∀ {g c} {π : Path} →
             head (walk {g} {c} {c} {[]} (sdone {g}) π) ≡ head π
head-sdone = refl

walk-head : ∀ {g a c xs} (s : Steps g a c xs) (π : Path) → head π ≡ c →
            head (walk s π) ≡ a
walk-head sdone π eq = eq
walk-head (sstep _ _) _ _ = refl

walkRun : ∀ {g a c xs} (s : Steps g a c xs) (π : Path) → head π ≡ c →
          IsRun g π → IsRun g (walk s π)
step (walkRun sdone π eq r) = step r
rest (walkRun sdone π eq r) = rest r
step (walkRun (sstep {a = a} {w = w} st rest) π eq r) =
  w , subst (λ z → Step _ a w z) (sym (walk-head rest π eq)) st
rest (walkRun (sstep st rest) π eq r) = walkRun rest π eq r

fails : ∀ {g p a c xs} (s : Steps g a c xs) (π : Path) → head π ≡ c →
        ⟦ g ⟧ p c ≡ false →
        Eventually (λ σ → ⟦ g ⟧ p (head σ) ≡ false) (walk s π)
fails {g} {p} {c = c} sdone π eq bad = hereE goal
  where
  goal : ⟦ g ⟧ p (head (walk {g} {c} {c} {[]} (sdone {g}) π)) ≡ false
  goal = subst (λ z → ⟦ g ⟧ p z ≡ false)
           (trans (sym eq) (sym (head-sdone {g} {c} {π}))) bad
fails {g} {p} (sstep {b = b} {c = c} _ rest) π eq bad =
  thereE (fails {g} {p} {a = b} {c = c} rest π eq bad)

not-glob : ∀ {g p π} →
           Eventually (λ σ → ⟦ g ⟧ p (head σ) ≡ false) π →
           ¬ Globally (λ σ → ⟦ g ⟧ p (head σ) ≡ true) π
not-glob {g} {p} (hereE {π} bad) gl =
  true≢false (trans (sym (now {P = λ σ → ⟦ g ⟧ p (head σ) ≡ true} {π} gl)) bad)
not-glob {g} {p} {π} (thereE later′) gl =
  not-glob {g} {p} {π = tail π} later′ (later gl)

-- The finite path, then the infinite run from its last configuration.
unroll : ∀ {g p c xs} (m : NoStuck g) → PathTo g (init g) c xs →
         ⟦ g ⟧ p c ≡ false → Reach g (init g) c →
         Σ Path (λ π → head π ≡ init g × IsRun g π × ¬ Holds g (always p) π)
unroll {g} {p} {c} m path bad reach =
  let e = run-exists {g} {c} m reach
      end = proj₁ e
      eq = proj₁ (proj₂ e)
      is = proj₂ (proj₂ e)
      s = toSteps {g} {init g} {c} path
      whole = walk {g} {init g} {c} s end
      hd : head whole ≡ init g
      hd = walk-head {g} {init g} {c} s end eq
      rn : IsRun g whole
      rn = walkRun {g} {init g} {c} s end eq is
      ng : ¬ Holds g (always p) whole
      ng = not-glob {g} {p} {π = whole}
             (fails {g} {p} {a = init g} {c = c} s end eq bad)
  in whole , hd , rn , ng

------------------------------------------------------------------------
-- The counterexample is valid when it is that parent chain and `P`
-- fails at its end. `lasso` validity is stated with the liveness check.
------------------------------------------------------------------------

data Valid (g : Graph) : Formula → Cex → Set where
  v-fin : ∀ {p c xs} → PathTo g (init g) c xs → ⟦ g ⟧ p c ≡ false →
          Valid g (always p) (finite xs)
  -- `ys` reaches the loop entry from the start. `zs` is a nonempty
  -- cycle on that entry. `eventually` has an empty prefix.
  v-ev : ∀ {p l ys zs} →
         PathTo g (init g) l ys →
         PathTo g l l zs →
         Σ (Who × RConf) (λ wd → Σ (List (Who × RConf)) (λ ys → zs ≡ wd ∷ ys)) →
         Valid g (eventually p) (lasso [] ys zs)
  -- `xs` is the path to the trigger, `ys` the walk from there to the
  -- loop entry, and `zs` a nonempty cycle on that entry.
  v-to : ∀ {p q c l xs ys zs} →
         PathTo g (init g) c xs →
         PathTo g c l ys →
         PathTo g l l zs →
         Σ (Who × RConf) (λ wd → Σ (List (Who × RConf)) (λ ys → zs ≡ wd ∷ ys)) →
         ⟦ g ⟧ p c ≡ true →
         Valid g (leadsTo p q) (lasso xs ys zs)

------------------------------------------------------------------------
-- Decision. The scan is split once, and the answer is returned with
-- the evidence, so the theorems do not reduce `emit` on `reachable`.
------------------------------------------------------------------------

start : ∀ {g π} → head π ≡ init g → Reach g (init g) (head π)
start {g} {π} eq = subst (Reach g (init g)) (sym eq) rhere

always-of : ∀ {g p π} (m : NoStuck g) →
            (∀ {c} → Any (_≡_ c) (queued (reachable g)) → ⟦ g ⟧ p c ≡ true) →
            IsRun g π → Reach g (init g) (head π) →
            Globally (λ σ → ⟦ g ⟧ p (head σ) ≡ true) π
now (always-of {g} {p} {π} m all r reach) =
  all (reachable-complete {g} {c = head π} reach)
later (always-of {g} {p} {π} m all r reach) =
  always-of {g} {p} {π = tail π} m all (rest {g} {π} r)
    (take {g} {c = head π} m reach (proj₂ (step {g} {π} r)))

holds-yes : ∀ {g p} (m : NoStuck g) →
            (∀ {c} → Any (_≡_ c) (queued (reachable g)) → ⟦ g ⟧ p c ≡ true) →
            yes ≡ yes → Satisfies g (always p)
holds-yes {g} {p} m all _ π h0 r =
  always-of {g} {p} {π} m all r (start {g} {π} h0)

no-yes : ∀ {g p w} → no w ≡ yes → Satisfies g (always p)
no-yes ()

yes-no : ∀ {g p w} → yes ≡ no w →
         Valid g (always p) w × ¬ Satisfies g (always p)
yes-no ()

-- Match the scan as an argument. A `with` on it rewrites the failure
-- proof, and `refl` then cannot see the counterexample.
fromScan : ∀ {g p} (m : NoStuck g) (s : Scan g p (reachable g)) →
           Σ Answer (λ a →
             (a ≡ yes → Satisfies g (always p)) ×
             (∀ {w} → a ≡ no w →
               Valid g (always p) w × ¬ Satisfies g (always p)))
fromScan {g} {p} m (inj₁ all) =
  yes , holds-yes {g} {p} m all , yes-no {g} {p}
fromScan {g} {p} m (inj₂ (n , mem , bad)) =
  no w , no-yes {g} {p} {w} , refuse
  where
  path = trace-of {g} {c = confN n} {p = proj₂ n} mem
  pr = proj₂ path
  w = finite (proj₁ path)
  reach = reachable-sound {g} {c = confN n} (node→conf mem)
  run = unroll {g} {p} {c = confN n} m pr bad reach
  denies : ¬ Satisfies g (always p)
  denies sat =
    proj₂ (proj₂ (proj₂ run))
      (sat (proj₁ run) (proj₁ (proj₂ run)) (proj₁ (proj₂ (proj₂ run))))
  refuse : ∀ {w′} → no w ≡ no w′ →
           Valid g (always p) w′ × ¬ Satisfies g (always p)
  refuse refl = v-fin {g} pr bad , denies

outcome : (g : Graph) (m : NoStuck g) (p : StateProp) →
          Σ Answer (λ a →
            (a ≡ yes → Satisfies g (always p)) ×
            (∀ {w} → a ≡ no w →
              Valid g (always p) w × ¬ Satisfies g (always p)))
outcome g m p = fromScan m (scan g p (reachable g))

check : (g : Graph) → NoStuck g → StateProp → Answer
check g m p = proj₁ (outcome g m p)

check-sound : ∀ {g} (m : NoStuck g) {p} → check g m p ≡ yes →
              Satisfies g (always p)
check-sound {g} m {p} eq = proj₁ (proj₂ (outcome g m p)) eq

cex-sound : ∀ {g} (m : NoStuck g) {p w} → check g m p ≡ no w →
            Valid g (always p) w × ¬ Satisfies g (always p)
cex-sound {g} m {p} eq = proj₂ (proj₂ (outcome g m p)) eq

check-complete : ∀ {g} (m : NoStuck g) {p} → Satisfies g (always p) →
                 check g m p ≡ yes
check-complete {g} m {p} sat with outcome g m p
... | yes , _ , _ = refl
... | no _ , _ , deny = ⊥-elim (proj₂ (deny refl) sat)

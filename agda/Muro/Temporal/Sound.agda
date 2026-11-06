------------------------------------------------------------------------
-- A boolean scan of `bfs` is a theorem about `Decide.check`.
--
-- `Search.bfs` is the first component of one well-founded recursion.
-- The second component is reachability, closure under `view`, and the
-- presence of the start. `holds` and `shapes` read that list. `yes-check`
-- turns a true scan into `Decide.check ≡ yes`, and `no-check` turns a
-- missed `always` into a refusal.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Sound where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []a; _∷_ to _∷a_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Muro.AsyncRec
  using ( Graph; RConf; Reach; rhere; rstep; init
        ; view; kidsV; localB; shapeOf
        ; elemB; elem→any
        )
open import Muro.Temporal
  using ( Who; Step; stepL; stepR; finish
        ; StateProp; Formula; always; eventually; leadsTo
        ; ⟦_⟧; Path; head; tail; IsRun; step; rest
        ; Globally; now; later
        ; Holds; Satisfies; NoStuck
        ; Answer; yes; no; Cex
        ; run-exists; kid-step
        )
open import Muro.Temporal.Graph using (any→elem)
open import Muro.Temporal.Safety using (run-reach; goL-kid; goR-kid)
open import Muro.Temporal.Live
  using ( Mem; m-here; m-there
        ; Chain; c-nil; c-cons; End
        ; Closed; hasInit; shut; spine
        ; LiveF; lev; lto; embed
        ; checkLive; live-sound; live-complete; live-deny
        )
open import Muro.Temporal.Search using (bfs)
import Muro.Temporal.Search as S
import Muro.Temporal.Decide as Decide

¬_ : Set → Set
¬ A = A → ⊥

true≢false : true ≡ false → ⊥
true≢false ()

module Of (g : Graph) where
  open S.Walk g public using (Good; searched)

lookupR : ∀ {g c cs} → All (Reach g (init g)) cs → Any (_≡_ c) cs →
          Reach g (init g) c
lookupR (r ∷a _) (here refl) = r
lookupR (_ ∷a rs) (there m) = lookupR rs m

in-bfs : ∀ {g c} → Reach g (init g) c → Any (_≡_ c) (bfs g)
in-bfs {g} r = walk r (Good.origin searched)
  where
  open Of g
  walk : ∀ {a c} → Reach g a c → Any (_≡_ a) (bfs g) → Any (_≡_ c) (bfs g)
  walk rhere ain = ain
  walk (rstep mem later) ain = walk later (Good.closed searched ain mem)

reach-of : ∀ {g c} → elemB c (bfs g) ≡ true → Reach g (init g) c
reach-of {g} eq = lookupR (Good.reached searched) (elem→any eq)
  where open Of g

origin-of : ∀ g → elemB (init g) (bfs g) ≡ true
origin-of g = any→elem (Good.origin searched)
  where open Of g

closed-of : ∀ {g c d} → elemB c (bfs g) ≡ true →
            Any (_≡_ d) (kidsV (view g c)) → elemB d (bfs g) ≡ true
closed-of {g} eq mem = any→elem (Good.closed searched (elem→any eq) mem)
  where open Of g

reach-bfs : ∀ {g c} → Reach g (init g) c → elemB c (bfs g) ≡ true
reach-bfs r = any→elem (in-bfs r)

holds : Graph → StateProp → List RConf → Bool
holds _ _ [] = true
holds g p (c ∷ cs) = ⟦ g ⟧ p c ∧ holds g p cs

shapes : Graph → List RConf → Bool
shapes _ [] = true
shapes g (c ∷ cs) = localB (view g c) ∧ shapes g cs

∧-left : ∀ {a b} → (a ∧ b) ≡ true → a ≡ true
∧-left {true} _ = refl
∧-left {false} {true} ()
∧-left {false} {false} ()

∧-right : ∀ {a b} → (a ∧ b) ≡ true → b ≡ true
∧-right {true} eq = eq
∧-right {false} {true} ()
∧-right {false} {false} ()

holds-at : ∀ {g p c cs} → holds g p cs ≡ true → Any (_≡_ c) cs →
           ⟦ g ⟧ p c ≡ true
holds-at eq (here refl) = ∧-left eq
holds-at eq (there m) = holds-at (∧-right eq) m

shape-at : ∀ {g c cs} → shapes g cs ≡ true → Any (_≡_ c) cs →
           localB (view g c) ≡ true
shape-at eq (here refl) = ∧-left eq
shape-at eq (there m) = shape-at (∧-right eq) m

nostuck : ∀ g → shapes g (bfs g) ≡ true → NoStuck g
nostuck g eq {c} r = shapeOf (view g c) (shape-at eq (in-bfs r))

------------------------------------------------------------------------
-- A run from the start that stands on a chosen reachable configuration.
------------------------------------------------------------------------

data Tour (g : Graph) : RConf → RConf → Set where
  t0 : ∀ {c} → Tour g c c
  t1 : ∀ {a b c w} → Step g a w b → Tour g b c → Tour g a c

toTour : ∀ {g a c} → Reach g a c → Tour g a c
toTour rhere = t0
toTour (rstep mem later) = t1 (proj₂ (kid-step mem)) (toTour later)

play : ∀ {g a c} → Tour g a c → Path → Path
play t0 π = π
head (play (t1 {a = a} _ _) _) = a
tail (play (t1 _ rest) π) = play rest π

play-head : ∀ {g a c} (t : Tour g a c) π → head π ≡ c → head (play t π) ≡ a
play-head t0 _ eq = eq
play-head (t1 _ _) _ _ = refl

play-run : ∀ {g a c} (t : Tour g a c) π → head π ≡ c → IsRun g π →
           IsRun g (play t π)
play-run t0 _ _ rn = rn
step (play-run (t1 {a = a} {w = w} st rest) π eq rn) =
  w , subst (λ z → Step _ a w z) (sym (play-head rest π eq)) st
rest (play-run (t1 _ rest) π eq rn) = play-run rest π eq rn

not-glob : ∀ {g p a c} (t : Tour g a c) π → head π ≡ c →
           ⟦ g ⟧ p c ≡ false →
           ¬ Globally (λ σ → ⟦ g ⟧ p (head σ) ≡ true) (play t π)
not-glob {g} {p} t0 π eq bad gl =
  true≢false (trans (trans (sym ok) (cong (⟦ g ⟧ p) eq)) bad)
  where
  ok : ⟦ g ⟧ p (head π) ≡ true
  ok = now gl
not-glob {p = p} (t1 _ rest) π eq bad gl =
  not-glob {p = p} rest π eq bad (later gl)

always-yes : ∀ {g p} → holds g p (bfs g) ≡ true → shapes g (bfs g) ≡ true →
             Satisfies g (always p)
always-yes {g} {p} hp hs π hd rn =
  glob (run-reach (nostuck g hs) rn
          (subst (λ z → Reach g (init g) z) (sym hd) rhere))
  where
  glob : ∀ {σ} → Globally (λ τ → Reach g (init g) (head τ)) σ →
         Globally (λ τ → ⟦ g ⟧ p (head τ) ≡ true) σ
  now (glob r) = holds-at hp (in-bfs (now r))
  later (glob r) = glob (later r)

find-bad : ∀ {g p} cs → holds g p cs ≡ false →
           Σ RConf (λ c → Any (_≡_ c) cs × ⟦ g ⟧ p c ≡ false)
find-bad [] ()
find-bad {g} {p} (c ∷ cs) eq = on (⟦ g ⟧ p c) refl eq
  where
  on : (b : Bool) → ⟦ g ⟧ p c ≡ b → (⟦ g ⟧ p c ∧ holds g p cs) ≡ false →
       Σ RConf (λ d → Any (_≡_ d) (c ∷ cs) × ⟦ g ⟧ p d ≡ false)
  on false pr _ = c , here refl , pr
  on true pr eq2 rewrite pr =
    let d , mem , bad = find-bad cs eq2
    in d , there mem , bad

always-no : ∀ {g} (p : StateProp) → holds g p (bfs g) ≡ false →
            shapes g (bfs g) ≡ true →
            ¬ Satisfies g (always p)
always-no {g} p hp hs sat =
  let open Of g
      c , mem , bad = find-bad (bfs g) hp
      r = lookupR (Good.reached searched) mem
      m = nostuck g hs
      π , hd , rn = run-exists m r
      t = toTour r
  in not-glob {p = p} t π hd bad
       (sat (play t π) (play-head t π hd) (play-run t π hd rn))

yes-check : ∀ {g p} (hp : holds g p (bfs g) ≡ true) (hs : shapes g (bfs g) ≡ true) →
            Decide.check g (nostuck g hs) (always p) ≡ yes
yes-check {g} {p} hp hs =
  Decide.check-complete g (nostuck g hs) (always p) (always-yes hp hs)

no-check : ∀ {g} (m : NoStuck g) φ → ¬ Satisfies g φ →
           Σ Cex (λ w → Decide.check g m φ ≡ no w)
no-check {g} m φ ¬sat = on (Decide.check g m φ) refl
  where
  on : (a : Answer) → Decide.check g m φ ≡ a →
       Σ Cex (λ w → Decide.check g m φ ≡ no w)
  on yes eq = ⊥-elim (¬sat (Decide.check-sound g m φ eq))
  on (no w) eq = w , eq

------------------------------------------------------------------------
-- The breadth-first list is closed, so liveness can use it.
------------------------------------------------------------------------

any→mem : ∀ {c} (xs : List RConf) → Any (_≡_ c) xs → Mem c xs
any→mem (_ ∷ _) (here p) = m-here p
any→mem (_ ∷ xs) (there m) = m-there (any→mem xs m)

mem→any : ∀ {c xs} → Mem c xs → Any (_≡_ c) xs
mem→any (m-here p) = here p
mem→any (m-there m) = there (mem→any m)

toChain : ∀ {g a c} → Reach g a c →
          Σ (List (Who × RConf)) (λ xs → Σ (Chain g a xs) (λ ch → End ch ≡ c))
toChain rhere = [] , c-nil , refl
toChain (rstep {d = d} mem later) =
  let w , st = kid-step mem
      xs , ch , end = toChain later
  in (w , d) ∷ xs , c-cons st ch , end

module Close (g : Graph) (hs : shapes g (bfs g) ≡ true) where
  open Of g

  reached : ∀ {c} → Mem c (bfs g) → Reach g (init g) c
  reached m = lookupR (Good.reached searched) (mem→any m)

  cl : Closed g (bfs g)
  hasInit cl = any→mem (bfs g) (Good.origin searched)
  shut cl m (finish _ _ _) = m
  shut cl m (stepL eq) =
    any→mem (bfs g) (Good.closed searched (mem→any m)
      (goL-kid eq (nostuck g hs (reached m))))
  shut cl m (stepR eq) =
    any→mem (bfs g) (Good.closed searched (mem→any m)
      (goR-kid eq (nostuck g hs (reached m))))
  spine cl m = toChain (reached m)

closed-bfs : ∀ {g} → shapes g (bfs g) ≡ true → Closed g (bfs g)
closed-bfs {g} hs = Close.cl g hs

live-yes : ∀ {g} (φ : LiveF) (hs : shapes g (bfs g) ≡ true) →
           checkLive g (bfs g) φ (closed-bfs hs) ≡ yes →
           Satisfies g (embed φ)
live-yes {g} φ hs eq = live-sound g (bfs g) φ (closed-bfs hs) eq

live-check : ∀ {g} (φ : LiveF) (hs : shapes g (bfs g) ≡ true) →
             checkLive g (bfs g) φ (closed-bfs hs) ≡ yes →
             Decide.check g (nostuck g hs) (embed φ) ≡ yes
live-check {g} φ hs eq =
  Decide.check-complete g (nostuck g hs) (embed φ) (live-yes φ hs eq)

live-miss : ∀ {g w} (φ : LiveF) (hs : shapes g (bfs g) ≡ true) →
            checkLive g (bfs g) φ (closed-bfs hs) ≡ no w →
            ¬ Satisfies g (embed φ)
live-miss {g} {w} φ hs eq = live-deny g (bfs g) φ w (closed-bfs hs) eq

------------------------------------------------------------------------
-- The source meeting and the compiled graph are the same run.
--
-- `SourceSafe` says each reachable source configuration is final or
-- takes some step. That is weaker than `NoStuck`: one side can step
-- while the other is a fault, and `merge` then returns `VBad`, which
-- has no `Shape`. `SourceShape` is the predicate `source-safe-iff`
-- uses. A configuration has it when every source-reachable view is
-- `Shape`.
--
-- A view child is a left or right step, so `sim-bwd` reads it. A
-- source step is a view child when the configuration is already
-- `Shape`, which `NoStuck` supplies on the graph-reachable ones.
-- `fin` stays on the source configuration. The two infinite runs are
-- identified up to the heads, which is what `Holds` reads.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Span where

open import Data.Bool.Base using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; [])
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong)

open import Muro.AsyncRec
  using ( Graph; RConf; init; Reach; rhere; rstep
        ; View; view; kidsV; Shape
        ; Act; AGo; reactL; reactR
        ; l2rOf; r2lOf; halted )
open import Muro.Temporal
  using ( Who; lside; rside; Step; stepL; stepR; finish; fin
        ; Path; head; tail; IsRun; step; rest
        ; StateProp; Formula; always; eventually; leadsTo
        ; ⟦_⟧; Globally; now; later; Eventually; hereE; thereE
        ; Holds; Satisfies; NoStuck
        ; kid-step; nil-any; view-final; snocR
        ; Answer; yes; no )
open Path
open IsRun
open Globally
open import Muro.Temporal.Source
  using ( SProc; SConf; abs; bnames; CanFinish
        ; SReach; sr-here; sr-step
        ; SPath; shead; stail; SIsRun; smove; srest
        ; _⟶ₛ_ )
  renaming (finish to sfinish)
open SPath
open SIsRun
open import Muro.Temporal.Run using (Hold; init-hold)
open import Muro.Temporal.Expose using (sim-fwd)
open import Muro.Temporal.Follow using (stepLB; stepRB)
open import Muro.Temporal.Carry using (source-final)
open import Muro.Temporal.Bridge
  using ( Frag; echoOk; muOk; graphOf; initS; init-sim; gok
        ; SourceSatisfies; absPath )
open import Muro.Temporal.Graph
  using (PathTo; pt-here; pt-snoc; queued; reachable)
open import Muro.Temporal.Safety
  using (goL-kid; goR-kid; unroll; Valid; v-fin)
  renaming (cex-sound to always-cex)
open import Muro.Temporal.Live
  using (LiveF; lev; lto; Witness; wit-ev; wit-to; live-witness)
open import Muro.Temporal.Decide
  using (check; check-sound; check-refutes; closed-of)

------------------------------------------------------------------------
-- A view child is a source step. `fin` is not a child.
------------------------------------------------------------------------

noKid : ∀ {g c d} →
        l2rOf c ≡ [] → r2lOf c ≡ [] → halted g c ≡ true →
        Any (_≡_ d) (kidsV (view g c)) → ⊥
noKid {d = d} a b ht mem =
  nil-any (subst (λ v → Any (_≡_ d) (kidsV v)) (view-final a b ht) mem)

read : ∀ {g c d} → Hold g c →
       Any (_≡_ d) (kidsV (view g (abs c))) →
       Σ SConf (λ e → c ⟶ₛ e × abs e ≡ d × Hold g e)
read {g} {c} {d = d} h mem = on (kid-step mem)
  where
  on : Σ Who (λ w → Step g (abs c) w d) →
       Σ SConf (λ e → c ⟶ₛ e × abs e ≡ d × Hold g e)
  on (_ , stepL eq) = stepLB h eq
  on (_ , stepR eq) = stepRB h eq
  on (_ , finish a b ht) = ⊥-elim (noKid a b ht mem)

-- The equality stays outside `Reach`, so the recursive call is the tail.
fromR : ∀ {g c gc r} → abs c ≡ gc → Reach g gc r → Hold g c →
        Σ SConf (λ d → SReach c d × abs d ≡ r × Hold g d)
fromR {c = c} eq rhere h = c , sr-here , eq , h
fromR {g} {c} {r = r} eq (rstep {d = mid} mem later) h =
  let mem′ = subst (λ z → Any (_≡_ mid) (kidsV (view g z))) (sym eq) mem
      e , st , ab , h′ = read h mem′
      d , sr , abd , hd = fromR ab later h′
  in d , sr-step st sr , abd , hd

source-of-graph : ∀ {g c r} → Reach g (abs c) r → Hold g c →
                  Σ SConf (λ d → SReach c d × abs d ≡ r × Hold g d)
source-of-graph = fromR refl

------------------------------------------------------------------------
-- A source step of a shaped configuration is a view child. The
-- stutter does not move `abs`.
------------------------------------------------------------------------

extend : ∀ {g a b} → NoStuck g → Reach g (init g) (abs a) →
         Hold g a → a ⟶ₛ b →
         Reach g (init g) (abs b) × Hold g b
extend {g} {a} {b} m acc h st = on (sim-fwd h st)
  where
  on : Σ Who (λ w → Step g (abs a) w (abs b) × Hold g b) →
       Reach g (init g) (abs b) × Hold g b
  on (_ , stepL eq , h′) = snocR acc (goL-kid eq (m acc)) , h′
  on (_ , stepR eq , h′) = snocR acc (goR-kid eq (m acc)) , h′
  on (_ , finish _ _ _ , h′) = acc , h′

span : ∀ {g a b} → NoStuck g → Reach g (init g) (abs a) → Hold g a →
       SReach a b → Reach g (init g) (abs b)
span m acc h sr-here = acc
span m acc h (sr-step st rest) =
  let acc′ , h′ = extend m acc h st
  in span m acc′ h′ rest

graph-of-source : ∀ {g c0 c} → NoStuck g → Hold g c0 → abs c0 ≡ init g →
                  SReach c0 c → Reach g (init g) (abs c)
graph-of-source {g} {c0} m h eq sr =
  span m (subst (λ z → Reach g z (abs c0)) eq rhere) h sr

------------------------------------------------------------------------
-- `SourceShape` replaces `SourceSafe`.
------------------------------------------------------------------------

SourceShape : Graph → SConf → Set
SourceShape g c0 = ∀ {c} → SReach c0 c → Shape (view g (abs c))

shape-of : ∀ {g c0} → NoStuck g → Hold g c0 → abs c0 ≡ init g →
           SourceShape g c0
shape-of {g} {c0} m h eq {c} sr =
  m (graph-of-source m h eq sr)

nostuck-of : ∀ {g c0} → Hold g c0 → abs c0 ≡ init g →
             SourceShape g c0 → NoStuck g
nostuck-of {g} {c0} h eq sh {c} r =
  let back = subst (λ z → Reach g z c) (sym eq) r
      d , sr , ab , _ = source-of-graph back h
  in subst (λ z → Shape (view g z)) ab (sh sr)

source-safe-iff :
  ∀ k (P Q : SProc) (fp : Frag P) (fq : Frag Q) →
  echoOk (bnames P) [] P ≡ true →
  echoOk (bnames Q) [] Q ≡ true →
  muOk P ≡ true →
  muOk Q ≡ true →
  ∀ g c →
  graphOf k P Q fp fq ≡ gok g →
  initS k P Q fp fq ≡ just c →
  (SourceShape g c → NoStuck g) ×
  (NoStuck g → SourceShape g c)
source-safe-iff k P Q fp fq eP eQ mP mQ g c eqg eqc =
  let h = init-hold k P Q fp fq eP eQ mP mQ g c eqg eqc
      eq = init-sim k P Q fp fq g c eqg eqc
  in (λ sh → nostuck-of h eq sh) , (λ m → shape-of m h eq)

------------------------------------------------------------------------
-- One graph step, read at the source. `fin` is the stutter.
------------------------------------------------------------------------

cast : ∀ {c} → CanFinish c → c ⟶ₛ c
cast (_ , _ , _ , _ , _ , _ , uL , hfL , uR , hfR , eL , eR) =
  sfinish uL hfL uR hfR eL eR

-- `finish` names one configuration twice. The two indices are that one.
endsSame : ∀ {g a b} → Step g a fin b → a ≡ b
endsSame (finish _ _ _) = refl

queues : ∀ {g a b} → Step g a fin b →
         l2rOf a ≡ [] × r2lOf a ≡ [] × halted g a ≡ true
queues (finish a b ht) = a , b , ht

record Next (g : Graph) (c : SConf) (π : Path) : Set where
  constructor mk
  field
    nxt : SConf
    nxH : Hold g nxt
    nxS : c ⟶ₛ nxt
    nxE : head (tail π) ≡ abs nxt

open Next

next : ∀ {g c π} → Hold g c → head π ≡ abs c → IsRun g π → Next g c π
next {g} {c} {π} h eq r = on (step r)
  where
  on : Σ Who (λ w → Step g (head π) w (head (tail π))) → Next g c π
  on (lside , stepL eqL) =
    let eqL′ = subst (λ z → reactL g z ≡ AGo (head (tail π))) eq eqL
        e , mv , ab , h′ = stepLB h eqL′
    in mk e h′ mv (sym ab)
  on (rside , stepR eqR) =
    let eqR′ = subst (λ z → reactR g z ≡ AGo (head (tail π))) eq eqR
        e , mv , ab , h′ = stepRB h eqR′
    in mk e h′ mv (sym ab)
  on (fin , st) =
    let e = endsSame st
        a , bq , ht = queues st
        a′ = subst (λ z → l2rOf z ≡ []) eq a
        b′ = subst (λ z → r2lOf z ≡ []) eq bq
        ht′ = subst (λ z → halted g z ≡ true) eq ht
    in mk c h (cast (source-final h a′ b′ ht′)) (trans (sym e) eq)

-- The tail is `nxt (next h eq r)`, written out so both copatterns share
-- that term. A `where` abbreviation would sit under a `let` and the
-- step proof would no longer be the head of the tail.
liftS : ∀ {g c π} (h : Hold g c) (eq : head π ≡ abs c) (r : IsRun g π) → SPath
shead (liftS {c = c} _ _ _) = c
stail (liftS {π = π} h eq r) =
  liftS {c = nxt (next h eq r)} {π = tail π}
        (nxH (next h eq r)) (nxE (next h eq r)) (rest r)

srun : ∀ {g c π} (h : Hold g c) (eq : head π ≡ abs c) (r : IsRun g π) →
       SIsRun (liftS h eq r)
smove (srun {π = π} h eq r) = nxS (next h eq r)
srest (srun {π = π} h eq r) =
  srun {c = nxt (next h eq r)} {π = tail π}
       (nxH (next h eq r)) (nxE (next h eq r)) (rest r)

------------------------------------------------------------------------
-- `Holds` reads heads. Two paths with the same heads agree on it.
------------------------------------------------------------------------

record Bisim (π σ : Path) : Set where
  coinductive
  field
    same : head π ≡ head σ
    more : Bisim (tail π) (tail σ)

open Bisim

track : ∀ {g c π} (h : Hold g c) (eq : head π ≡ abs c) (r : IsRun g π) →
        Bisim (absPath (liftS h eq r)) π
same (track h eq r) = sym eq
more (track {π = π} h eq r) =
  track {c = nxt (next h eq r)} {π = tail π}
        (nxH (next h eq r)) (nxE (next h eq r)) (rest r)

symB : ∀ {π σ} → Bisim π σ → Bisim σ π
same (symB b) = sym (same b)
more (symB b) = symB (more b)

-- Named so a `Globally` predicate unifies without inverting `⟦_⟧`.
satP : Graph → StateProp → Path → Set
satP g p τ = ⟦ g ⟧ p (head τ) ≡ true

toP : Graph → StateProp → StateProp → Path → Set
toP g p q τ = satP g p τ → Eventually (satP g q) τ

carryAlways : ∀ {g p π σ} → Bisim π σ →
              Globally (satP g p) π → Globally (satP g p) σ
now (carryAlways {g = g} {p = p} {π = π} b gl) =
  subst (λ z → ⟦ g ⟧ p z ≡ true) (same b)
    (now {P = satP g p} {π} gl)
later (carryAlways {g = g} {p = p} b gl) =
  carryAlways {g} {p} (more b) (later {P = satP g p} gl)

carryEv : ∀ {g p π σ} → Bisim π σ →
          Eventually (satP g p) π → Eventually (satP g p) σ
carryEv {g = g} {p = p} b (hereE ok) =
  hereE (subst (λ z → ⟦ g ⟧ p z ≡ true) (same b) ok)
carryEv {g = g} {p = p} b (thereE restE) =
  thereE (carryEv {g} {p} (more b) restE)

carryTo : ∀ {g p q π σ} → Bisim π σ →
          Globally (toP g p q) π → Globally (toP g p q) σ
now (carryTo {g = g} {p = p} {q = q} {π = π} b gl) ok =
  carryEv {g} {q} b
    (now {P = toP g p q} {π} gl
      (subst (λ z → ⟦ g ⟧ p z ≡ true) (sym (same b)) ok))
later (carryTo {g = g} {p = p} {q = q} b gl) =
  carryTo {g} {p} {q} (more b) (later {P = toP g p q} gl)

holds-bisim : ∀ {g φ π σ} → Bisim π σ → Holds g φ π → Holds g φ σ
holds-bisim {g} {always p} b h = carryAlways {g} {p} b h
holds-bisim {g} {eventually p} b h = carryEv {g} {p} b h
holds-bisim {g} {leadsTo p q} b h = carryTo {g} {p} {q} b h

------------------------------------------------------------------------
-- A source run projects. A graph run lifts. Satisfaction moves.
------------------------------------------------------------------------

projRun : ∀ {g π} → Hold g (shead π) → SIsRun π → IsRun g (absPath π)
step (projRun h r) =
  proj₁ (sim-fwd h (smove r)) , proj₁ (proj₂ (sim-fwd h (smove r)))
rest (projRun h r) =
  projRun (proj₂ (proj₂ (sim-fwd h (smove r)))) (srest r)

toSource : ∀ {g c φ} → Hold g c → abs c ≡ init g →
           Satisfies g φ → SourceSatisfies g c φ
toSource {g} h eq sat π hd rn =
  sat (absPath π) (trans (cong abs hd) eq)
      (projRun (subst (Hold g) (sym hd) h) rn)

toGraph : ∀ {g c φ} → Hold g c → abs c ≡ init g →
          SourceSatisfies g c φ → Satisfies g φ
toGraph {g} {c} h eq src π hd rn =
  let eqh = trans hd (sym eq)
      bi = track h eqh rn
      ho = src (liftS h eqh rn) refl (srun h eqh rn)
  in holds-bisim bi ho

transfer :
  ∀ k (P Q : SProc) (fp : Frag P) (fq : Frag Q) →
  echoOk (bnames P) [] P ≡ true →
  echoOk (bnames Q) [] Q ≡ true →
  muOk P ≡ true →
  muOk Q ≡ true →
  ∀ g c φ →
  graphOf k P Q fp fq ≡ gok g →
  initS k P Q fp fq ≡ just c →
  (Satisfies g φ → SourceSatisfies g c φ) ×
  (SourceSatisfies g c φ → Satisfies g φ)
transfer k P Q fp fq eP eQ mP mQ g c φ eqg eqc =
  let h = init-hold k P Q fp fq eP eQ mP mQ g c eqg eqc
      eq = init-sim k P Q fp fq g c eqg eqc
  in toSource h eq , toGraph h eq

------------------------------------------------------------------------
-- The recorded counterexample is a source run.
------------------------------------------------------------------------

ptReach : ∀ {g c xs} → NoStuck g → PathTo g (init g) c xs →
          Reach g (init g) c
ptReach _ pt-here = rhere
ptReach m (pt-snoc pre (stepL eq)) =
  snocR (ptReach m pre) (goL-kid eq (m (ptReach m pre)))
ptReach m (pt-snoc pre (stepR eq)) =
  snocR (ptReach m pre) (goR-kid eq (m (ptReach m pre)))
ptReach m (pt-snoc pre (finish _ _ _)) = ptReach m pre

graphRun : ∀ {g φ w} (m : NoStuck g) → check g m φ ≡ no w →
           Σ Path (λ π → head π ≡ init g × IsRun g π × (Holds g φ π → ⊥))
graphRun {g} {always p} {w} m eq = body (proj₁ (always-cex m eq))
  where
  body : Valid g (always p) w →
         Σ Path (λ π → head π ≡ init g × IsRun g π × (Holds g (always p) π → ⊥))
  body (v-fin path bad) = unroll {g} {p} m path bad (ptReach m path)
graphRun {g} {eventually p} {w} m eq =
  body (live-witness g (queued (reachable g)) (lev p) w (closed-of g m) eq)
  where
  body : Witness g (lev p) w →
         Σ Path (λ π → head π ≡ init g × IsRun g π ×
                       (Holds g (eventually p) π → ⊥))
  body (wit-ev _ _ _ _ _ π hd rn bad) = π , hd , rn , bad
graphRun {g} {leadsTo p q} {w} m eq =
  body (live-witness g (queued (reachable g)) (lto p q) w (closed-of g m) eq)
  where
  body : Witness g (lto p q) w →
         Σ Path (λ π → head π ≡ init g × IsRun g π ×
                       (Holds g (leadsTo p q) π → ⊥))
  body (wit-to _ _ _ _ _ _ _ _ π hd rn bad) = π , hd , rn , bad

check-yes :
  ∀ k (P Q : SProc) (fp : Frag P) (fq : Frag Q) →
  echoOk (bnames P) [] P ≡ true →
  echoOk (bnames Q) [] Q ≡ true →
  muOk P ≡ true →
  muOk Q ≡ true →
  ∀ g c φ (m : NoStuck g) →
  graphOf k P Q fp fq ≡ gok g →
  initS k P Q fp fq ≡ just c →
  check g m φ ≡ yes →
  SourceSatisfies g c φ
check-yes k P Q fp fq eP eQ mP mQ g c φ m eqg eqc ok =
  toSource (init-hold k P Q fp fq eP eQ mP mQ g c eqg eqc)
           (init-sim k P Q fp fq g c eqg eqc)
           (check-sound g m φ ok)

check-no :
  ∀ k (P Q : SProc) (fp : Frag P) (fq : Frag Q) →
  echoOk (bnames P) [] P ≡ true →
  echoOk (bnames Q) [] Q ≡ true →
  muOk P ≡ true →
  muOk Q ≡ true →
  ∀ g c φ w (m : NoStuck g) →
  graphOf k P Q fp fq ≡ gok g →
  initS k P Q fp fq ≡ just c →
  check g m φ ≡ no w →
  SourceSatisfies g c φ → ⊥
check-no k P Q fp fq eP eQ mP mQ g c φ w m eqg eqc no′ sat =
  check-refutes g m φ w no′
    (toGraph (init-hold k P Q fp fq eP eQ mP mQ g c eqg eqc)
             (init-sim k P Q fp fq g c eqg eqc)
             sat)

cex-source :
  ∀ k (P Q : SProc) (fp : Frag P) (fq : Frag Q) →
  echoOk (bnames P) [] P ≡ true →
  echoOk (bnames Q) [] Q ≡ true →
  muOk P ≡ true →
  muOk Q ≡ true →
  ∀ g c φ w (m : NoStuck g) →
  graphOf k P Q fp fq ≡ gok g →
  initS k P Q fp fq ≡ just c →
  check g m φ ≡ no w →
  Σ SPath (λ π → shead π ≡ c × SIsRun π × (Holds g φ (absPath π) → ⊥))
cex-source k P Q fp fq eP eQ mP mQ g c φ w m eqg eqc no′ =
  let h = init-hold k P Q fp fq eP eQ mP mQ g c eqg eqc
      eq = init-sim k P Q fp fq g c eqg eqc
      π , hd , rn , bad = graphRun m no′
      eqh = trans hd (sym eq)
      bi = track h eqh rn
      sp = liftS h eqh rn
  in sp , refl ,
     srun h eqh rn ,
     (λ ho → bad (holds-bisim bi ho))

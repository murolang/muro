------------------------------------------------------------------------
-- Productivity of an accepted unfold, as observations of the syntax.
--
-- An unfold the checker accepts can be read to any finite depth, and no
-- observation re-enters the block it came from. The measure is the depth
-- in ℕ. There is no fuel, no reduction recursion, and no coinduction.
--
-- What this module proves
--   hasSelf-ren, hasSelf-sub, guarded-sub (with GuardedCall), guarded-inst.
--   The occurrence-restricted forms hasSelf-sub-occ and guarded-sub-occ.
--   Theorem A, guarded-unrolls: a guarded tail unrolls to every depth.
--   Theorem B, observational productivity.
--     obs-stream: fam = false, tail block-free, every finite depth.
--     obs-fam: fam = true, every finite depth. Its type lists the
--     hypotheses: BlockClosed, a Memb (lookup, allowedDef, an Opened
--     body) for every block index, fitsOd for every member, a Nav
--     subject and fitsNav of it. Each unfold carries HeadSeed and
--     SeedCovered. A Nav is a def/app spine or a nested unfold.
--   checkSig-nu extracts the productivity check from an accepted
--   signature. checkSig-guarded reads that check off seedWalk, as
--   AllUnf: at every syntactic unfold, whnf of the step, StepGuard of
--   that whnf, and (seedFlows nothing · ∧ hasSelf of the seed) ≡ false,
--   and the same record on every subterm the walk enters.
--   unfFacts turns AllUnf of a one-λ pair into a block-free head, a
--   GuardedTail, HeadSeed, and SeedCovered. lamPairFacts is the boolean
--   on that pair. body-unf is the BodyShape. obs-stream-ok is obs-stream
--   once the tail term is block-free. opened-one is an Opened once the
--   tail is a Nav. unroll-accepted is guarded-unrolls of the tail
--   instantiated at the seed, given Bodies. lam-body is the body of a λ.
--   SeedCovered has three disjuncts: the tail does not read the seed,
--   the head does, or the seed does not mention the block. Acceptance
--   is one of those. A block-mentioning seed that the tail reads and
--   the head does not is refused by the checker.
--   UnfoldGuard of a single checkUnfold is checkUnfold-guarded, in
--   Muro.Check. The judgment ⊢ does not carry the guard.
--
-- What it does not prove
--   Stream call tails. For a stream unfold the tail is the next seed, so
--   a call in tail position (gt-call) puts a block member into the seed.
--   obs-stream asks hasSelf of the tail term to be false, and
--   obs-stream-ok takes that as a hypothesis. The checker accepts the
--   call. The call forms are proved for families (Always, ~, a declared
--   ν), not for streams.
--   Closure of component. reaches is reachGo with fuel suc (length of
--   the definitions) and a visited set. A mention is one edge only when
--   the target looks up, and the fuel is enough for a simple path, but
--   this module does not prove the search transitive. BlockClosed stays
--   an explicit hypothesis of Bodies and of obs-fam. It is not used to
--   build an observation, and it is not derived from checkSig.
--   fitsNav, and which tail is a Nav rather than a pair. AllUnf records
--   the guard and the seed boolean. nav-of-tail returns a Nav for a
--   def/app spine or a nested unfold, and misses a pair, an absent
--   tail, and an application of an unfold.
--   Spec. checkNu returns without walking. 
--   An unfold that appears only after whnf of a definition or an
--   annotation. The walk follows the syntax.
--   Normalisation of a block-free head (Empty-evid) and termination of
--   an accepted block by the descent check. Neither is this theorem.
--   A family tail that is merely block-free gives one head
--   (obs-unf-one); the next depth needs another Reads.
--   A step with more than one λ around the pair. guardedStep and
--   seedFlows strip every λ; unfFacts, nv-unf and rd-fam are exactly one.
--   ⊢ is unchanged: t-unf, t-unfG and t-unfR do not carry the guard.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Productive where

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.String.Base using () renaming (_++_ to _++s_)
import Data.Vec.Base as Vec
open import Data.Nat.Base using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_; _+_)
open import Data.Product.Base using (_×_; _,_; Σ; ∃; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.SubstLemmas
open import Muro.Env
open import Muro.Check
open import Muro.Reduction

------------------------------------------------------------------------
-- Boolean and occurrence facts.
------------------------------------------------------------------------

∨-both-false : ∀ {a b} → a ≡ false → b ≡ false → a ∨ b ≡ false
∨-both-false refl refl = refl

∨-left : ∀ {a b} → a ≡ true → a ∨ b ≡ true
∨-left {true} refl = refl
∨-left {false} ()

∨-right : ∀ {a b} → b ≡ true → a ∨ b ≡ true
∨-right {false} refl = refl
∨-right {true}  refl = refl

∧-imp : ∀ {a b} → a ∧ b ≡ false → a ≡ true → b ≡ false
∧-imp {true}  eq refl = eq
∧-imp {false} _  () 

eqFin-refl : ∀ {n} (x : Fin n) → eqFin x x ≡ true
eqFin-refl zero    = refl
eqFin-refl (suc x) = eqFin-refl x

eqFin-≡ᵇ : ∀ {n} (x y : Fin n) → eqFin x y ≡ (toℕ x ≡ᵇ toℕ y)
eqFin-≡ᵇ zero    zero    = refl
eqFin-≡ᵇ zero    (suc _) = refl
eqFin-≡ᵇ (suc _) zero    = refl
eqFin-≡ᵇ (suc x) (suc y) = eqFin-≡ᵇ x y

-- thin k skips index k: thin 0 is suc, and lift (thin k) is thin (suc k).
mutual
  thin : ∀ {n} → ℕ → Fin n → Fin (suc n)
  thin zero    x = suc x
  thin (suc k) x = thin↑ k x

  thin↑ : ∀ {n} → ℕ → Fin n → Fin (suc n)
  thin↑ {zero}   _ ()
  thin↑ {suc _} _ zero    = zero
  thin↑ {suc _} k (suc x) = suc (thin k x)

thin-lift : ∀ {n} (k : ℕ) → lift (thin {n} k) ≗ thin (suc k)
thin-lift _ zero    = refl
thin-lift _ (suc _) = refl

-- Where index i lands after thin k. Indices below k stay; the rest move up.
bump : ℕ → ℕ → ℕ
bump k i = if i <ᵇ k then i else suc i

bump-suc : ∀ k i → suc (bump k i) ≡ bump (suc k) (suc i)
bump-suc k i with i <ᵇ k
... | true  = refl
... | false = refl

-- A renaming that never returns index k still never returns it under lift,
-- at the shifted index.
lift-avoid : ∀ {n m} k (ρ : Fin n → Fin m)
  → (∀ x → (k ≡ᵇ toℕ (ρ x)) ≡ false)
  → ∀ y → (suc k ≡ᵇ toℕ (lift ρ y)) ≡ false
lift-avoid _ _ _  zero    = refl
lift-avoid _ _ hyp (suc y) = hyp y

mutual
  occℕ-ren-avoid : ∀ {n m} k (ρ : Fin n → Fin m) t
    → (∀ x → (k ≡ᵇ toℕ (ρ x)) ≡ false)
    → occℕ k (ren ρ t) ≡ false
  occℕ-ren-avoid k ρ (var x) hyp = hyp x
  occℕ-ren-avoid k ρ (pi _ A B) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ A hyp)
                 (occℕ-ren-avoid (suc k) (lift ρ) B (lift-avoid k ρ hyp))
  occℕ-ren-avoid k ρ (lam _ A t) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ A hyp)
                 (occℕ-ren-avoid (suc k) (lift ρ) t (lift-avoid k ρ hyp))
  occℕ-ren-avoid k ρ (app f a) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ f hyp) (occℕ-ren-avoid k ρ a hyp)
  occℕ-ren-avoid k ρ (su t) hyp = occℕ-ren-avoid k ρ t hyp
  occℕ-ren-avoid k ρ (mData e P bs) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ e hyp)
      (∨-both-false (occℕ-ren-avoid (suc k) (lift ρ) P (lift-avoid k ρ hyp))
                    (occℕList-ren-avoid k ρ bs hyp))
  occℕ-ren-avoid k ρ (mNat e P z s) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ e hyp)
      (∨-both-false (occℕ-ren-avoid (suc k) (lift ρ) P (lift-avoid k ρ hyp))
        (∨-both-false (occℕ-ren-avoid k ρ z hyp)
                      (occℕ-ren-avoid (suc k) (lift ρ) s (lift-avoid k ρ hyp))))
  occℕ-ren-avoid k ρ (mEmp e P) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ e hyp)
                 (occℕ-ren-avoid (suc k) (lift ρ) P (lift-avoid k ρ hyp))
  occℕ-ren-avoid k ρ (mUnit e P u) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ e hyp)
      (∨-both-false (occℕ-ren-avoid (suc k) (lift ρ) P (lift-avoid k ρ hyp))
                    (occℕ-ren-avoid k ρ u hyp))
  occℕ-ren-avoid k ρ (idt A a b) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ A hyp)
      (∨-both-false (occℕ-ren-avoid k ρ a hyp) (occℕ-ren-avoid k ρ b hyp))
  occℕ-ren-avoid k ρ (rwt e P t) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ e hyp)
      (∨-both-false (occℕ-ren-avoid (suc k) (lift ρ) P (lift-avoid k ρ hyp))
                    (occℕ-ren-avoid k ρ t hyp))
  occℕ-ren-avoid k ρ (ann e A) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ e hyp) (occℕ-ren-avoid k ρ A hyp)
  occℕ-ren-avoid k ρ (prod A B) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ A hyp) (occℕ-ren-avoid k ρ B hyp)
  occℕ-ren-avoid k ρ (pair a b) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ a hyp) (occℕ-ren-avoid k ρ b hyp)
  occℕ-ren-avoid k ρ (letp e t) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ e hyp)
                 (occℕ-ren-avoid (suc (suc k)) (lift (lift ρ)) t
                   (lift-avoid (suc k) (lift ρ) (lift-avoid k ρ hyp)))
  occℕ-ren-avoid k ρ (nu F) hyp =
    occℕ-ren-avoid (suc k) (lift ρ) F (lift-avoid k ρ hyp)
  occℕ-ren-avoid k ρ (unf s f) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ s hyp) (occℕ-ren-avoid k ρ f hyp)
  occℕ-ren-avoid k ρ (ucons s) hyp = occℕ-ren-avoid k ρ s hyp
  occℕ-ren-avoid k ρ (tensor d s) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ d hyp) (occℕ-ren-avoid k ρ s hyp)
  occℕ-ren-avoid k ρ (addi x y) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ x hyp) (occℕ-ren-avoid k ρ y hyp)
  occℕ-ren-avoid k ρ (muli x y) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ x hyp) (occℕ-ren-avoid k ρ y hyp)
  occℕ-ren-avoid k ρ (addt t u) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ t hyp) (occℕ-ren-avoid k ρ u hyp)
  occℕ-ren-avoid k ρ (toi64 t) hyp = occℕ-ren-avoid k ρ t hyp
  occℕ-ren-avoid k ρ (packi x y) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ x hyp) (occℕ-ren-avoid k ρ y hyp)
  occℕ-ren-avoid _ _ typ       _ = refl
  occℕ-ren-avoid _ _ nat       _ = refl
  occℕ-ren-avoid _ _ ze        _ = refl
  occℕ-ren-avoid _ _ unit      _ = refl
  occℕ-ren-avoid _ _ one       _ = refl
  occℕ-ren-avoid _ _ empty     _ = refl
  occℕ-ren-avoid _ _ (dty _)   _ = refl
  occℕ-ren-avoid _ _ (ctor _ _) _ = refl
  occℕ-ren-avoid _ _ rfl       _ = refl
  occℕ-ren-avoid _ _ (def _)   _ = refl
  occℕ-ren-avoid _ _ i64       _ = refl
  occℕ-ren-avoid _ _ f32ty     _ = refl

  occℕList-ren-avoid : ∀ {n m} k (ρ : Fin n → Fin m) ts
    → (∀ x → (k ≡ᵇ toℕ (ρ x)) ≡ false)
    → occℕList k (renList ρ ts) ≡ false
  occℕList-ren-avoid _ _ []       _   = refl
  occℕList-ren-avoid k ρ (t ∷ ts) hyp =
    ∨-both-false (occℕ-ren-avoid k ρ t hyp) (occℕList-ren-avoid k ρ ts hyp)

-- let weakens twice: lift (lift (thin k)) ≗ thin (suc (suc k)).
thin-lift² : ∀ {n} (k : ℕ) → lift (lift (thin {n} k)) ≗ thin (suc (suc k))
thin-lift² k zero          = refl
thin-lift² k (suc zero)    = refl
thin-lift² k (suc (suc _)) = refl

bump-suc² : ∀ k i → suc (suc (bump k i)) ≡ bump (suc (suc k)) (suc (suc i))
bump-suc² k i = trans (cong suc (bump-suc k i)) (bump-suc (suc k) (suc i))

-- Variable case of occℕ-thin. thin moves x, and ≡ᵇ follows the same move.
occℕ-thin-var : ∀ {n} k i (x : Fin n)
  → occℕ (bump k i) (var (thin k x)) ≡ (i ≡ᵇ toℕ x)
occℕ-thin-var zero    _       _       = refl
occℕ-thin-var (suc _) zero    zero    = refl
occℕ-thin-var (suc _) zero    (suc _) = refl
occℕ-thin-var (suc k) (suc i) zero with i <ᵇ k
... | true  = refl
... | false = refl
occℕ-thin-var (suc k) (suc i) (suc x) with i <ᵇ k in eq
... | true =
  subst (λ c → ((if c then i else suc i) ≡ᵇ toℕ (thin k x)) ≡ (i ≡ᵇ toℕ x))
        eq (occℕ-thin-var k i x)
... | false =
  subst (λ c → ((if c then i else suc i) ≡ᵇ toℕ (thin k x)) ≡ (i ≡ᵇ toℕ x))
        eq (occℕ-thin-var k i x)

-- Occurrence commutes with thin: the variable moves to bump k i.
mutual
  occℕ-thin : ∀ {n} k i (t : Tm n) → occℕ (bump k i) (ren (thin k) t) ≡ occℕ i t
  occℕ-thin k i (var x) = occℕ-thin-var k i x
  occℕ-thin k i (pi q A B) =
    cong₂ _∨_ (occℕ-thin k i A)
              (occℕ-thin-body k i B)
  occℕ-thin k i (lam q A t) =
    cong₂ _∨_ (occℕ-thin k i A)
              (occℕ-thin-body k i t)
  occℕ-thin k i (app f a) = cong₂ _∨_ (occℕ-thin k i f) (occℕ-thin k i a)
  occℕ-thin k i (su t) = occℕ-thin k i t
  occℕ-thin k i (mData e P bs) =
    cong₂ _∨_ (occℕ-thin k i e)
      (cong₂ _∨_ (occℕ-thin-body k i P)
                 (occℕList-thin k i bs))
  occℕ-thin k i (mNat e P z s) =
    cong₂ _∨_ (occℕ-thin k i e)
      (cong₂ _∨_ (occℕ-thin-body k i P)
        (cong₂ _∨_ (occℕ-thin k i z)
                   (occℕ-thin-body k i s)))
  occℕ-thin k i (mEmp e P) =
    cong₂ _∨_ (occℕ-thin k i e)
              (occℕ-thin-body k i P)
  occℕ-thin k i (mUnit e P u) =
    cong₂ _∨_ (occℕ-thin k i e)
      (cong₂ _∨_ (occℕ-thin-body k i P)
                 (occℕ-thin k i u))
  occℕ-thin k i (idt A a b) =
    cong₂ _∨_ (occℕ-thin k i A) (cong₂ _∨_ (occℕ-thin k i a) (occℕ-thin k i b))
  occℕ-thin k i (rwt e P t) =
    cong₂ _∨_ (occℕ-thin k i e)
      (cong₂ _∨_ (occℕ-thin-body k i P)
                 (occℕ-thin k i t))
  occℕ-thin k i (ann e A) = cong₂ _∨_ (occℕ-thin k i e) (occℕ-thin k i A)
  occℕ-thin k i (prod A B) = cong₂ _∨_ (occℕ-thin k i A) (occℕ-thin k i B)
  occℕ-thin k i (pair a b) = cong₂ _∨_ (occℕ-thin k i a) (occℕ-thin k i b)
  occℕ-thin k i (letp e t) =
    cong₂ _∨_ (occℕ-thin k i e) (occℕ-thin-let k i t)
  occℕ-thin k i (nu F) =
    occℕ-thin-body k i F
  occℕ-thin k i (unf s f) = cong₂ _∨_ (occℕ-thin k i s) (occℕ-thin k i f)
  occℕ-thin k i (ucons s) = occℕ-thin k i s
  occℕ-thin k i (tensor d s) = cong₂ _∨_ (occℕ-thin k i d) (occℕ-thin k i s)
  occℕ-thin k i (addi x y) = cong₂ _∨_ (occℕ-thin k i x) (occℕ-thin k i y)
  occℕ-thin k i (muli x y) = cong₂ _∨_ (occℕ-thin k i x) (occℕ-thin k i y)
  occℕ-thin k i (addt t u) = cong₂ _∨_ (occℕ-thin k i t) (occℕ-thin k i u)
  occℕ-thin k i (toi64 t) = occℕ-thin k i t
  occℕ-thin k i (packi x y) = cong₂ _∨_ (occℕ-thin k i x) (occℕ-thin k i y)
  occℕ-thin _ _ typ = refl
  occℕ-thin _ _ nat = refl
  occℕ-thin _ _ ze = refl
  occℕ-thin _ _ unit = refl
  occℕ-thin _ _ one = refl
  occℕ-thin _ _ empty = refl
  occℕ-thin _ _ (dty _) = refl
  occℕ-thin _ _ (ctor _ _) = refl
  occℕ-thin _ _ rfl = refl
  occℕ-thin _ _ (def _) = refl
  occℕ-thin _ _ i64 = refl
  occℕ-thin _ _ f32ty = refl

  occℕList-thin : ∀ {n} k i (ts : List (Tm n))
    → occℕList (bump k i) (renList (thin k) ts) ≡ occℕList i ts
  occℕList-thin _ _ []       = refl
  occℕList-thin k i (t ∷ ts) = cong₂ _∨_ (occℕ-thin k i t) (occℕList-thin k i ts)

  -- The body sits under lift (thin k), which is thin (suc k), and the index
  -- suc (bump k i) is bump (suc k) (suc i).
  occℕ-thin-body : ∀ {n} k i (t : Tm (suc n))
    → occℕ (suc (bump k i)) (ren (lift (thin {n} k)) t) ≡ occℕ (suc i) t
  occℕ-thin-body {n} k i t =
    trans (cong (λ j → occℕ j (ren (lift (thin {n} k)) t)) (bump-suc k i))
      (trans (cong (occℕ (bump (suc k) (suc i))) (ren-ext (thin-lift {n} k) t))
             (occℕ-thin (suc k) (suc i) t))

  occℕ-thin-let : ∀ {n} k i (t : Tm (suc (suc n)))
    → occℕ (suc (suc (bump k i))) (ren (lift (lift (thin k))) t)
    ≡ occℕ (suc (suc i)) t
  occℕ-thin-let k i t =
    trans (cong (λ n → occℕ n (ren (lift (lift (thin k))) t)) (bump-suc² k i))
      (trans (cong (occℕ (bump (suc (suc k)) (suc (suc i)))) (ren-ext (thin-lift² k) t))
             (occℕ-thin (suc (suc k)) (suc (suc i)) t))

-- wk is ren suc, and thin 0 is suc, so a weakened term's index i is the
-- original index at suc i.
thin-0 : ∀ {n} → thin {n} 0 ≗ suc
thin-0 _ = refl

occℕ-wk : ∀ {n} i (t : Tm n) → occℕ (suc i) (wk t) ≡ occℕ i t
occℕ-wk i t =
  trans (cong (occℕ (suc i)) (sym (ren-ext thin-0 t))) (occℕ-thin 0 i t)

-- lifts keeps variable 0 and weakens every other image, so index 0 occurs
-- in lifts σ x exactly when x is 0.
lifts-at-zero : ∀ {n m} (σ : Fin n → Tm m) (x : Fin (suc n))
  → occℕ 0 (lifts σ x) ≡ (0 ≡ᵇ toℕ x)
lifts-at-zero _ zero    = refl
lifts-at-zero σ (suc x) = occℕ-ren-avoid 0 suc (σ x) (λ _ → refl)

-- Pointwise, a substitution that acts as the identity on index i
-- preserves occurrence of i. The lifted substitution is the binder case.
lifts-occ : ∀ {n m} i (σ : Fin n → Tm m)
  → (∀ x → occℕ i (σ x) ≡ (i ≡ᵇ toℕ x))
  → ∀ y → occℕ (suc i) (lifts σ y) ≡ (suc i ≡ᵇ toℕ y)
lifts-occ i σ hyp zero    = refl
lifts-occ i σ hyp (suc y) = trans (occℕ-wk i (σ y)) (hyp y)


mutual
  occℕ-sub : ∀ {n m} i (σ : Fin n → Tm m) t
    → (∀ x → occℕ i (σ x) ≡ (i ≡ᵇ toℕ x))
    → occℕ i (sub σ t) ≡ occℕ i t

  occℕList-sub : ∀ {n m} i (σ : Fin n → Tm m) ts
    → (∀ x → occℕ i (σ x) ≡ (i ≡ᵇ toℕ x))
    → occℕList i (subList σ ts) ≡ occℕList i ts

  occℕ-sub i σ (var x) hyp = hyp x
  occℕ-sub i σ (pi _ A B) hyp =
    cong₂ _∨_ (occℕ-sub i σ A hyp) (occℕ-sub (suc i) (lifts σ) B (lifts-occ i σ hyp))
  occℕ-sub i σ (lam _ A t) hyp =
    cong₂ _∨_ (occℕ-sub i σ A hyp) (occℕ-sub (suc i) (lifts σ) t (lifts-occ i σ hyp))
  occℕ-sub i σ (app f a) hyp = cong₂ _∨_ (occℕ-sub i σ f hyp) (occℕ-sub i σ a hyp)
  occℕ-sub i σ (su t) hyp = occℕ-sub i σ t hyp
  occℕ-sub i σ (mData e P bs) hyp =
    cong₂ _∨_ (occℕ-sub i σ e hyp)
      (cong₂ _∨_ (occℕ-sub (suc i) (lifts σ) P (lifts-occ i σ hyp))
                 (occℕList-sub i σ bs hyp))
  occℕ-sub i σ (mNat e P z s) hyp =
    cong₂ _∨_ (occℕ-sub i σ e hyp)
      (cong₂ _∨_ (occℕ-sub (suc i) (lifts σ) P (lifts-occ i σ hyp))
        (cong₂ _∨_ (occℕ-sub i σ z hyp)
                   (occℕ-sub (suc i) (lifts σ) s (lifts-occ i σ hyp))))
  occℕ-sub i σ (mEmp e P) hyp =
    cong₂ _∨_ (occℕ-sub i σ e hyp) (occℕ-sub (suc i) (lifts σ) P (lifts-occ i σ hyp))
  occℕ-sub i σ (mUnit e P u) hyp =
    cong₂ _∨_ (occℕ-sub i σ e hyp)
      (cong₂ _∨_ (occℕ-sub (suc i) (lifts σ) P (lifts-occ i σ hyp))
                 (occℕ-sub i σ u hyp))
  occℕ-sub i σ (idt A a b) hyp =
    cong₂ _∨_ (occℕ-sub i σ A hyp) (cong₂ _∨_ (occℕ-sub i σ a hyp) (occℕ-sub i σ b hyp))
  occℕ-sub i σ (rwt e P t) hyp =
    cong₂ _∨_ (occℕ-sub i σ e hyp)
      (cong₂ _∨_ (occℕ-sub (suc i) (lifts σ) P (lifts-occ i σ hyp))
                 (occℕ-sub i σ t hyp))
  occℕ-sub i σ (ann e A) hyp = cong₂ _∨_ (occℕ-sub i σ e hyp) (occℕ-sub i σ A hyp)
  occℕ-sub i σ (prod A B) hyp = cong₂ _∨_ (occℕ-sub i σ A hyp) (occℕ-sub i σ B hyp)
  occℕ-sub i σ (pair a b) hyp = cong₂ _∨_ (occℕ-sub i σ a hyp) (occℕ-sub i σ b hyp)
  occℕ-sub i σ (letp e t) hyp =
    cong₂ _∨_ (occℕ-sub i σ e hyp)
              (occℕ-sub (suc (suc i)) (lifts (lifts σ)) t (lifts-occ (suc i) (lifts σ) (lifts-occ i σ hyp)))
  occℕ-sub i σ (nu F) hyp = occℕ-sub (suc i) (lifts σ) F (lifts-occ i σ hyp)
  occℕ-sub i σ (unf s f) hyp = cong₂ _∨_ (occℕ-sub i σ s hyp) (occℕ-sub i σ f hyp)
  occℕ-sub i σ (ucons s) hyp = occℕ-sub i σ s hyp
  occℕ-sub i σ (tensor d s) hyp = cong₂ _∨_ (occℕ-sub i σ d hyp) (occℕ-sub i σ s hyp)
  occℕ-sub i σ (addi x y) hyp = cong₂ _∨_ (occℕ-sub i σ x hyp) (occℕ-sub i σ y hyp)
  occℕ-sub i σ (muli x y) hyp = cong₂ _∨_ (occℕ-sub i σ x hyp) (occℕ-sub i σ y hyp)
  occℕ-sub i σ (addt t u) hyp = cong₂ _∨_ (occℕ-sub i σ t hyp) (occℕ-sub i σ u hyp)
  occℕ-sub i σ (toi64 t) hyp = occℕ-sub i σ t hyp
  occℕ-sub i σ (packi x y) hyp = cong₂ _∨_ (occℕ-sub i σ x hyp) (occℕ-sub i σ y hyp)
  occℕ-sub _ _ typ _ = refl
  occℕ-sub _ _ nat _ = refl
  occℕ-sub _ _ ze _ = refl
  occℕ-sub _ _ unit _ = refl
  occℕ-sub _ _ one _ = refl
  occℕ-sub _ _ empty _ = refl
  occℕ-sub _ _ (dty _) _ = refl
  occℕ-sub _ _ (ctor _ _) _ = refl
  occℕ-sub _ _ rfl _ = refl
  occℕ-sub _ _ (def _) _ = refl
  occℕ-sub _ _ i64 _ = refl
  occℕ-sub _ _ f32ty _ = refl

  occℕList-sub _ _ [] _ = refl
  occℕList-sub i σ (t ∷ ts) hyp = cong₂ _∨_ (occℕ-sub i σ t hyp) (occℕList-sub i σ ts hyp)

-- Index 0 in sub (lifts σ) is index 0 in the original, for any σ:
-- lifts σ zero is var zero, and every other image is a weakening.
occℕ-zero-lifts : ∀ {n m} (σ : Fin n → Tm m) t
  → occℕ 0 (sub (lifts σ) t) ≡ occℕ 0 t
occℕ-zero-lifts σ t = occℕ-sub 0 (lifts σ) t (lifts-at-zero σ)

------------------------------------------------------------------------
-- occurs and occℕ agree, so the seed walk's ℕ index is the checker's Fin.
------------------------------------------------------------------------

mutual
  occℕ-occurs : ∀ {n} (x : Fin n) t → occℕ (toℕ x) t ≡ occurs x t
  occℕ-occurs x (var y) = sym (eqFin-≡ᵇ x y)
  occℕ-occurs x (pi _ A B) =
    cong₂ _∨_ (occℕ-occurs x A) (occℕ-occurs (suc x) B)
  occℕ-occurs x (lam _ A t) =
    cong₂ _∨_ (occℕ-occurs x A) (occℕ-occurs (suc x) t)
  occℕ-occurs x (app f a) = cong₂ _∨_ (occℕ-occurs x f) (occℕ-occurs x a)
  occℕ-occurs x (su t) = occℕ-occurs x t
  occℕ-occurs x (mData e P bs) =
    cong₂ _∨_ (occℕ-occurs x e)
      (cong₂ _∨_ (occℕ-occurs (suc x) P) (occℕList-occurs x bs))
  occℕ-occurs x (mNat e P z s) =
    cong₂ _∨_ (occℕ-occurs x e)
      (cong₂ _∨_ (occℕ-occurs (suc x) P)
        (cong₂ _∨_ (occℕ-occurs x z) (occℕ-occurs (suc x) s)))
  occℕ-occurs x (mEmp e P) =
    cong₂ _∨_ (occℕ-occurs x e) (occℕ-occurs (suc x) P)
  occℕ-occurs x (mUnit e P u) =
    cong₂ _∨_ (occℕ-occurs x e)
      (cong₂ _∨_ (occℕ-occurs (suc x) P) (occℕ-occurs x u))
  occℕ-occurs x (idt A a b) =
    cong₂ _∨_ (occℕ-occurs x A) (cong₂ _∨_ (occℕ-occurs x a) (occℕ-occurs x b))
  occℕ-occurs x (rwt e P t) =
    cong₂ _∨_ (occℕ-occurs x e)
      (cong₂ _∨_ (occℕ-occurs (suc x) P) (occℕ-occurs x t))
  occℕ-occurs x (ann e A) = cong₂ _∨_ (occℕ-occurs x e) (occℕ-occurs x A)
  occℕ-occurs x (prod A B) = cong₂ _∨_ (occℕ-occurs x A) (occℕ-occurs x B)
  occℕ-occurs x (pair a b) = cong₂ _∨_ (occℕ-occurs x a) (occℕ-occurs x b)
  occℕ-occurs x (letp e t) =
    cong₂ _∨_ (occℕ-occurs x e) (occℕ-occurs (suc (suc x)) t)
  occℕ-occurs x (nu F) = occℕ-occurs (suc x) F
  occℕ-occurs x (unf s f) = cong₂ _∨_ (occℕ-occurs x s) (occℕ-occurs x f)
  occℕ-occurs x (ucons s) = occℕ-occurs x s
  occℕ-occurs x (tensor d s) = cong₂ _∨_ (occℕ-occurs x d) (occℕ-occurs x s)
  occℕ-occurs x (addi a b) = cong₂ _∨_ (occℕ-occurs x a) (occℕ-occurs x b)
  occℕ-occurs x (muli a b) = cong₂ _∨_ (occℕ-occurs x a) (occℕ-occurs x b)
  occℕ-occurs x (addt t u) = cong₂ _∨_ (occℕ-occurs x t) (occℕ-occurs x u)
  occℕ-occurs x (toi64 t) = occℕ-occurs x t
  occℕ-occurs x (packi a b) = cong₂ _∨_ (occℕ-occurs x a) (occℕ-occurs x b)
  occℕ-occurs _ typ = refl
  occℕ-occurs _ nat = refl
  occℕ-occurs _ ze = refl
  occℕ-occurs _ unit = refl
  occℕ-occurs _ one = refl
  occℕ-occurs _ empty = refl
  occℕ-occurs _ (dty _) = refl
  occℕ-occurs _ (ctor _ _) = refl
  occℕ-occurs _ rfl = refl
  occℕ-occurs _ (def _) = refl
  occℕ-occurs _ i64 = refl
  occℕ-occurs _ f32ty = refl

  occℕList-occurs : ∀ {n} (x : Fin n) ts → occℕList (toℕ x) ts ≡ occursList x ts
  occℕList-occurs _ [] = refl
  occℕList-occurs x (t ∷ ts) = cong₂ _∨_ (occℕ-occurs x t) (occℕList-occurs x ts)

-- Variable 0 is preserved by lifts, on the checker's occurs.
occurs-zero-lifts : ∀ {n m} (σ : Fin n → Tm m) t
  → occurs zero (sub (lifts σ) t) ≡ occurs zero t
occurs-zero-lifts σ t =
  trans (sym (occℕ-occurs zero (sub (lifts σ) t)))
    (trans (occℕ-zero-lifts σ t) (occℕ-occurs zero t))

------------------------------------------------------------------------
-- Stage 0. hasSelf ignores variables, so it is invariant under renaming
-- and is preserved by a substitution whose images are block-free on the
-- variables that actually occur.
------------------------------------------------------------------------

mutual
  hasSelf-ren : ∀ {n m} B (ρ : Fin n → Fin m) t → hasSelf B (ren ρ t) ≡ hasSelf B t
  hasSelf-ren B ρ (app f a) = cong₂ _∨_ (hasSelf-ren B ρ f) (hasSelf-ren B ρ a)
  hasSelf-ren B ρ (su t) = hasSelf-ren B ρ t
  hasSelf-ren B ρ (pair a b) = cong₂ _∨_ (hasSelf-ren B ρ a) (hasSelf-ren B ρ b)
  hasSelf-ren B ρ (letp e t) =
    cong₂ _∨_ (hasSelf-ren B ρ e) (hasSelf-ren B (lift (lift ρ)) t)
  hasSelf-ren B ρ (unf s f) = cong₂ _∨_ (hasSelf-ren B ρ s) (hasSelf-ren B ρ f)
  hasSelf-ren B ρ (ucons u) = hasSelf-ren B ρ u
  hasSelf-ren B ρ (tensor d u) = cong₂ _∨_ (hasSelf-ren B ρ d) (hasSelf-ren B ρ u)
  hasSelf-ren B ρ (addi x y) = cong₂ _∨_ (hasSelf-ren B ρ x) (hasSelf-ren B ρ y)
  hasSelf-ren B ρ (muli x y) = cong₂ _∨_ (hasSelf-ren B ρ x) (hasSelf-ren B ρ y)
  hasSelf-ren B ρ (addt t u) = cong₂ _∨_ (hasSelf-ren B ρ t) (hasSelf-ren B ρ u)
  hasSelf-ren B ρ (toi64 t) = hasSelf-ren B ρ t
  hasSelf-ren B ρ (packi x y) = cong₂ _∨_ (hasSelf-ren B ρ x) (hasSelf-ren B ρ y)
  hasSelf-ren B ρ (lam _ A t) =
    cong₂ _∨_ (hasSelf-ren B ρ A) (hasSelf-ren B (lift ρ) t)
  hasSelf-ren B ρ (pi _ A C) =
    cong₂ _∨_ (hasSelf-ren B ρ A) (hasSelf-ren B (lift ρ) C)
  hasSelf-ren B ρ (prod A C) = cong₂ _∨_ (hasSelf-ren B ρ A) (hasSelf-ren B ρ C)
  hasSelf-ren B ρ (nu F) = hasSelf-ren B (lift ρ) F
  hasSelf-ren B ρ (mData e P bs) =
    cong₂ _∨_ (hasSelf-ren B ρ e)
      (cong₂ _∨_ (hasSelf-ren B (lift ρ) P) (hasSelfList-ren B ρ bs))
  hasSelf-ren B ρ (mNat e P z u) =
    cong₂ _∨_ (hasSelf-ren B ρ e)
      (cong₂ _∨_ (hasSelf-ren B (lift ρ) P)
        (cong₂ _∨_ (hasSelf-ren B ρ z) (hasSelf-ren B (lift ρ) u)))
  hasSelf-ren B ρ (mEmp e P) =
    cong₂ _∨_ (hasSelf-ren B ρ e) (hasSelf-ren B (lift ρ) P)
  hasSelf-ren B ρ (mUnit e P u) =
    cong₂ _∨_ (hasSelf-ren B ρ e)
      (cong₂ _∨_ (hasSelf-ren B (lift ρ) P) (hasSelf-ren B ρ u))
  hasSelf-ren B ρ (idt A a b) =
    cong₂ _∨_ (hasSelf-ren B ρ A)
      (cong₂ _∨_ (hasSelf-ren B ρ a) (hasSelf-ren B ρ b))
  hasSelf-ren B ρ (rwt e P t) =
    cong₂ _∨_ (hasSelf-ren B ρ e)
      (cong₂ _∨_ (hasSelf-ren B (lift ρ) P) (hasSelf-ren B ρ t))
  hasSelf-ren B ρ (ann e A) = cong₂ _∨_ (hasSelf-ren B ρ e) (hasSelf-ren B ρ A)
  hasSelf-ren _ _ (var _) = refl
  hasSelf-ren _ _ typ = refl
  hasSelf-ren _ _ nat = refl
  hasSelf-ren _ _ ze = refl
  hasSelf-ren _ _ unit = refl
  hasSelf-ren _ _ one = refl
  hasSelf-ren _ _ empty = refl
  hasSelf-ren _ _ (dty _) = refl
  hasSelf-ren _ _ (ctor _ _) = refl
  hasSelf-ren _ _ rfl = refl
  hasSelf-ren _ _ (def _) = refl
  hasSelf-ren _ _ i64 = refl
  hasSelf-ren _ _ f32ty = refl

  hasSelfList-ren : ∀ {n m} B (ρ : Fin n → Fin m) ts
    → hasSelfList B (renList ρ ts) ≡ hasSelfList B ts
  hasSelfList-ren _ _ [] = refl
  hasSelfList-ren B ρ (t ∷ ts) =
    cong₂ _∨_ (hasSelf-ren B ρ t) (hasSelfList-ren B ρ ts)

lifts-hs : ∀ {n m} B (τ : Fin n → Tm m)
  → (∀ x → hasSelf B (τ x) ≡ false)
  → ∀ y → hasSelf B (lifts τ y) ≡ false
lifts-hs _ _ _  zero    = refl
lifts-hs B τ hf (suc y) = trans (hasSelf-ren B suc (τ y)) (hf y)

-- Push a disjunct under one more right-nested ∨. occurs clauses are
-- right-nested, so an occurrence in an inner subterm is a ∨ of a prefix.
push∨ : ∀ {a b c} → a ∨ b ≡ true → a ∨ (b ∨ c) ≡ true
push∨ {true}  refl = refl
push∨ {false} {true}  refl = refl
push∨ {false} {false} ()

-- A binder's new variable is var zero, which is block-free. A free
-- variable of the body is a free variable of the binder.
bind-hyp : ∀ {n m} B (τ : Fin n → Tm m) (A : Tm n) (t : Tm (suc n))
  → (∀ x → occurs x A ∨ occurs (suc x) t ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ y → occurs y t ≡ true → hasSelf B (lifts τ y) ≡ false
bind-hyp _ _ _ _ _ zero _ = refl
bind-hyp B τ A t hyp (suc y) oc =
  trans (hasSelf-ren B suc (τ y)) (hyp y (∨-right {a = occurs y A} oc))

letp-hyp : ∀ {n m} B (τ : Fin n → Tm m) (e : Tm n) (t : Tm (suc (suc n)))
  → (∀ x → occurs x e ∨ occurs (suc (suc x)) t ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ y → occurs y t ≡ true → hasSelf B (lifts (lifts τ) y) ≡ false
letp-hyp _ _ _ _ _ zero _ = refl
letp-hyp _ _ _ _ _ (suc zero) _ = refl
letp-hyp B τ e t hyp (suc (suc y)) oc =
  trans (hasSelf-ren B suc (wk (τ y)))
    (trans (hasSelf-ren B suc (τ y)) (hyp y (∨-right {a = occurs y e} oc)))

nu-hyp : ∀ {n m} B (τ : Fin n → Tm m) (F : Tm (suc n))
  → (∀ x → occurs (suc x) F ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ y → occurs y F ≡ true → hasSelf B (lifts τ y) ≡ false
nu-hyp _ _ _ _ zero _ = refl
nu-hyp B τ F hyp (suc y) oc =
  trans (hasSelf-ren B suc (τ y)) (hyp y oc)

-- Each router lifts an occurrence in one subterm to the constructor's
-- occurs clause. The nesting is the right-nested ∨ of `occurs`.
mnat-P : ∀ {n m} B (τ : Fin n → Tm m) (e : Tm n) (z : Tm n) (s P : Tm (suc n))
  → (∀ x → occurs x (mNat e P z s) ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ y → occurs y P ≡ true → hasSelf B (lifts τ y) ≡ false
mnat-P B τ e z s P hyp =
  bind-hyp B τ e P λ x oc →
    hyp x (push∨ {a = occurs x e} {b = occurs (suc x) P}
                 {c = occurs x z ∨ occurs (suc x) s} oc)

mnat-z : ∀ {n m} B (τ : Fin n → Tm m) (e : Tm n) (P : Tm (suc n)) (s : Tm (suc n)) (z : Tm n)
  → (∀ x → occurs x (mNat e P z s) ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ x → occurs x z ≡ true → hasSelf B (τ x) ≡ false
mnat-z B τ e P s _ hyp x oc =
  hyp x (∨-right {a = occurs x e}
          (∨-right {a = occurs (suc x) P} (∨-left {b = occurs (suc x) s} oc)))

mnat-s : ∀ {n m} B (τ : Fin n → Tm m) (e : Tm n) (P : Tm (suc n)) (z : Tm n) (s : Tm (suc n))
  → (∀ x → occurs x (mNat e P z s) ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ y → occurs y s ≡ true → hasSelf B (lifts τ y) ≡ false
mnat-s _ _ _ _ _ _ _ zero _ = refl
mnat-s B τ e P z s hyp (suc y) oc =
  trans (hasSelf-ren B suc (τ y))
    (hyp y (∨-right {a = occurs y e}
             (∨-right {a = occurs (suc y) P}
               (∨-right {a = occurs y z} oc))))

bind-list-hyp : ∀ {n m} B (τ : Fin n → Tm m) (e : Tm n) (bs : List (Tm n)) (P : Tm (suc n))
  → (∀ x → occurs x (mData e P bs) ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ y → occurs y P ≡ true → hasSelf B (lifts τ y) ≡ false
bind-list-hyp B τ e bs P hyp =
  bind-hyp B τ e P λ x oc →
    hyp x (push∨ {a = occurs x e} {b = occurs (suc x) P} {c = occursList x bs} oc)

list-in : ∀ {n m} B (τ : Fin n → Tm m) (e : Tm n) (P : Tm (suc n)) (bs : List (Tm n))
  → (∀ x → occurs x (mData e P bs) ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ x → occursList x bs ≡ true → hasSelf B (τ x) ≡ false
list-in B τ e P _ hyp x oc =
  hyp x (∨-right {a = occurs x e} (∨-right {a = occurs (suc x) P} oc))

munit-P : ∀ {n m} B (τ : Fin n → Tm m) (e u : Tm n) (P : Tm (suc n))
  → (∀ x → occurs x (mUnit e P u) ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ y → occurs y P ≡ true → hasSelf B (lifts τ y) ≡ false
munit-P B τ e u P hyp =
  bind-hyp B τ e P λ x oc →
    hyp x (push∨ {a = occurs x e} {b = occurs (suc x) P} {c = occurs x u} oc)

munit-u : ∀ {n m} B (τ : Fin n → Tm m) (e : Tm n) (P : Tm (suc n)) (u : Tm n)
  → (∀ x → occurs x (mUnit e P u) ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ x → occurs x u ≡ true → hasSelf B (τ x) ≡ false
munit-u B τ e P _ hyp x oc =
  hyp x (∨-right {a = occurs x e} (∨-right {a = occurs (suc x) P} oc))

idt-a : ∀ {n m} B (τ : Fin n → Tm m) (A a b : Tm n)
  → (∀ x → occurs x (idt A a b) ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ x → occurs x a ≡ true → hasSelf B (τ x) ≡ false
idt-a B τ A _ b hyp x oc =
  hyp x (∨-right {a = occurs x A} (∨-left {b = occurs x b} oc))

idt-b : ∀ {n m} B (τ : Fin n → Tm m) (A a b : Tm n)
  → (∀ x → occurs x (idt A a b) ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ x → occurs x b ≡ true → hasSelf B (τ x) ≡ false
idt-b B τ A a _ hyp x oc =
  hyp x (∨-right {a = occurs x A} (∨-right {a = occurs x a} oc))

bind-hyp2 : ∀ {n m} B (τ : Fin n → Tm m) (e t : Tm n) (P : Tm (suc n))
  → (∀ x → occurs x (rwt e P t) ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ y → occurs y P ≡ true → hasSelf B (lifts τ y) ≡ false
bind-hyp2 B τ e t P hyp =
  bind-hyp B τ e P λ x oc →
    hyp x (push∨ {a = occurs x e} {b = occurs (suc x) P} {c = occurs x t} oc)

rwt-t : ∀ {n m} B (τ : Fin n → Tm m) (e : Tm n) (P : Tm (suc n)) (t : Tm n)
  → (∀ x → occurs x (rwt e P t) ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ x → occurs x t ≡ true → hasSelf B (τ x) ≡ false
rwt-t B τ e P _ hyp x oc =
  hyp x (∨-right {a = occurs x e} (∨-right {a = occurs (suc x) P} oc))

-- Images may mention the block. Only a variable that occurs has to be
-- block-free, which is what a dead seed binder needs.
mutual
  hasSelf-sub-occ : ∀ {n m} B (τ : Fin n → Tm m) t
    → hasSelf B t ≡ false
    → (∀ x → occurs x t ≡ true → hasSelf B (τ x) ≡ false)
    → hasSelf B (sub τ t) ≡ false
  hasSelf-sub-occ B τ (var x) _ hyp = hyp x (eqFin-refl x)
  hasSelf-sub-occ B τ (def _) ht _ = ht
  hasSelf-sub-occ B τ (app f a) ht hyp =
    let hf , ha = ∨-false₂ (hasSelf B f) (hasSelf B a) ht in
    ∨-both-false (hasSelf-sub-occ B τ f hf (λ x oc → hyp x (∨-left oc)))
                 (hasSelf-sub-occ B τ a ha (λ x oc → hyp x (∨-right oc)))
  hasSelf-sub-occ B τ (su t) ht hyp = hasSelf-sub-occ B τ t ht hyp
  hasSelf-sub-occ B τ (pair a b) ht hyp =
    let ha , hb = ∨-false₂ (hasSelf B a) (hasSelf B b) ht in
    ∨-both-false (hasSelf-sub-occ B τ a ha (λ x oc → hyp x (∨-left oc)))
                 (hasSelf-sub-occ B τ b hb (λ x oc → hyp x (∨-right oc)))
  hasSelf-sub-occ B τ (letp e t) ht hyp =
    let he , ht′ = ∨-false₂ (hasSelf B e) (hasSelf B t) ht in
    ∨-both-false (hasSelf-sub-occ B τ e he (λ x oc → hyp x (∨-left oc)))
                 (hasSelf-sub-occ B (lifts (lifts τ)) t ht′ (letp-hyp B τ e t hyp))
  hasSelf-sub-occ B τ (unf s f) ht hyp =
    let hs , hf = ∨-false₂ (hasSelf B s) (hasSelf B f) ht in
    ∨-both-false (hasSelf-sub-occ B τ s hs (λ x oc → hyp x (∨-left oc)))
                 (hasSelf-sub-occ B τ f hf (λ x oc → hyp x (∨-right oc)))
  hasSelf-sub-occ B τ (ucons u) ht hyp = hasSelf-sub-occ B τ u ht hyp
  hasSelf-sub-occ B τ (tensor d u) ht hyp =
    let hd , hu = ∨-false₂ (hasSelf B d) (hasSelf B u) ht in
    ∨-both-false (hasSelf-sub-occ B τ d hd (λ x oc → hyp x (∨-left oc)))
                 (hasSelf-sub-occ B τ u hu (λ x oc → hyp x (∨-right oc)))
  hasSelf-sub-occ B τ (addi x y) ht hyp =
    let hx , hy = ∨-false₂ (hasSelf B x) (hasSelf B y) ht in
    ∨-both-false (hasSelf-sub-occ B τ x hx (λ z oc → hyp z (∨-left oc)))
                 (hasSelf-sub-occ B τ y hy (λ z oc → hyp z (∨-right oc)))
  hasSelf-sub-occ B τ (muli x y) ht hyp =
    let hx , hy = ∨-false₂ (hasSelf B x) (hasSelf B y) ht in
    ∨-both-false (hasSelf-sub-occ B τ x hx (λ z oc → hyp z (∨-left oc)))
                 (hasSelf-sub-occ B τ y hy (λ z oc → hyp z (∨-right oc)))
  hasSelf-sub-occ B τ (addt t u) ht hyp =
    let ht′ , hu = ∨-false₂ (hasSelf B t) (hasSelf B u) ht in
    ∨-both-false (hasSelf-sub-occ B τ t ht′ (λ x oc → hyp x (∨-left oc)))
                 (hasSelf-sub-occ B τ u hu (λ x oc → hyp x (∨-right oc)))
  hasSelf-sub-occ B τ (toi64 t) ht hyp = hasSelf-sub-occ B τ t ht hyp
  hasSelf-sub-occ B τ (packi x y) ht hyp =
    let hx , hy = ∨-false₂ (hasSelf B x) (hasSelf B y) ht in
    ∨-both-false (hasSelf-sub-occ B τ x hx (λ z oc → hyp z (∨-left oc)))
                 (hasSelf-sub-occ B τ y hy (λ z oc → hyp z (∨-right oc)))
  hasSelf-sub-occ B τ (lam _ A t) ht hyp =
    let hA , ht′ = ∨-false₂ (hasSelf B A) (hasSelf B t) ht in
    ∨-both-false (hasSelf-sub-occ B τ A hA (λ x oc → hyp x (∨-left oc)))
                 (hasSelf-sub-occ B (lifts τ) t ht′ (bind-hyp B τ A t hyp))
  hasSelf-sub-occ B τ (pi _ A C) ht hyp =
    let hA , hC = ∨-false₂ (hasSelf B A) (hasSelf B C) ht in
    ∨-both-false (hasSelf-sub-occ B τ A hA (λ x oc → hyp x (∨-left oc)))
                 (hasSelf-sub-occ B (lifts τ) C hC (bind-hyp B τ A C hyp))
  hasSelf-sub-occ B τ (prod A C) ht hyp =
    let hA , hC = ∨-false₂ (hasSelf B A) (hasSelf B C) ht in
    ∨-both-false (hasSelf-sub-occ B τ A hA (λ x oc → hyp x (∨-left oc)))
                 (hasSelf-sub-occ B τ C hC (λ x oc → hyp x (∨-right oc)))
  hasSelf-sub-occ B τ (nu F) ht hyp =
    hasSelf-sub-occ B (lifts τ) F ht (nu-hyp B τ F hyp)
  hasSelf-sub-occ B τ (mData e P bs) ht hyp =
    let he , rest = ∨-false₂ (hasSelf B e) (hasSelf B P ∨ hasSelfList B bs) ht
        hP , hbs = ∨-false₂ (hasSelf B P) (hasSelfList B bs) rest
    in ∨-both-false (hasSelf-sub-occ B τ e he (λ x oc → hyp x (∨-left oc)))
         (∨-both-false
           (hasSelf-sub-occ B (lifts τ) P hP (bind-list-hyp B τ e bs P hyp))
           (hasSelfList-sub-occ B τ bs hbs (list-in B τ e P bs hyp)))
  hasSelf-sub-occ B τ (mNat e P z s) ht hyp =
    let he , rest = ∨-false₂ (hasSelf B e) (hasSelf B P ∨ hasSelf B z ∨ hasSelf B s) ht
        hP , rest′ = ∨-false₂ (hasSelf B P) (hasSelf B z ∨ hasSelf B s) rest
        hz , hs = ∨-false₂ (hasSelf B z) (hasSelf B s) rest′
    in ∨-both-false (hasSelf-sub-occ B τ e he (λ x oc → hyp x (∨-left oc)))
         (∨-both-false
           (hasSelf-sub-occ B (lifts τ) P hP (mnat-P B τ e z s P hyp))
           (∨-both-false
             (hasSelf-sub-occ B τ z hz (mnat-z B τ e P s z hyp))
             (hasSelf-sub-occ B (lifts τ) s hs (mnat-s B τ e P z s hyp))))
  hasSelf-sub-occ B τ (mEmp e P) ht hyp =
    let he , hP = ∨-false₂ (hasSelf B e) (hasSelf B P) ht in
    ∨-both-false (hasSelf-sub-occ B τ e he (λ x oc → hyp x (∨-left oc)))
                 (hasSelf-sub-occ B (lifts τ) P hP (bind-hyp B τ e P hyp))
  hasSelf-sub-occ B τ (mUnit e P u) ht hyp =
    let he , rest = ∨-false₂ (hasSelf B e) (hasSelf B P ∨ hasSelf B u) ht
        hP , hu = ∨-false₂ (hasSelf B P) (hasSelf B u) rest
    in ∨-both-false (hasSelf-sub-occ B τ e he (λ x oc → hyp x (∨-left oc)))
         (∨-both-false
           (hasSelf-sub-occ B (lifts τ) P hP (munit-P B τ e u P hyp))
           (hasSelf-sub-occ B τ u hu (munit-u B τ e P u hyp)))
  hasSelf-sub-occ B τ (idt A a b) ht hyp =
    let hA , rest = ∨-false₂ (hasSelf B A) (hasSelf B a ∨ hasSelf B b) ht
        ha , hb = ∨-false₂ (hasSelf B a) (hasSelf B b) rest
    in ∨-both-false (hasSelf-sub-occ B τ A hA (λ x oc → hyp x (∨-left oc)))
         (∨-both-false
           (hasSelf-sub-occ B τ a ha (idt-a B τ A a b hyp))
           (hasSelf-sub-occ B τ b hb (idt-b B τ A a b hyp)))
  hasSelf-sub-occ B τ (rwt e P t) ht hyp =
    let he , rest = ∨-false₂ (hasSelf B e) (hasSelf B P ∨ hasSelf B t) ht
        hP , ht′ = ∨-false₂ (hasSelf B P) (hasSelf B t) rest
    in ∨-both-false (hasSelf-sub-occ B τ e he (λ x oc → hyp x (∨-left oc)))
         (∨-both-false
           (hasSelf-sub-occ B (lifts τ) P hP (bind-hyp2 B τ e t P hyp))
           (hasSelf-sub-occ B τ t ht′ (rwt-t B τ e P t hyp)))
  hasSelf-sub-occ B τ (ann e A) ht hyp =
    let he , hA = ∨-false₂ (hasSelf B e) (hasSelf B A) ht in
    ∨-both-false (hasSelf-sub-occ B τ e he (λ x oc → hyp x (∨-left oc)))
                 (hasSelf-sub-occ B τ A hA (λ x oc → hyp x (∨-right oc)))
  hasSelf-sub-occ _ _ typ _ _ = refl
  hasSelf-sub-occ _ _ nat _ _ = refl
  hasSelf-sub-occ _ _ ze _ _ = refl
  hasSelf-sub-occ _ _ unit _ _ = refl
  hasSelf-sub-occ _ _ one _ _ = refl
  hasSelf-sub-occ _ _ empty _ _ = refl
  hasSelf-sub-occ _ _ (dty _) _ _ = refl
  hasSelf-sub-occ _ _ (ctor _ _) _ _ = refl
  hasSelf-sub-occ _ _ rfl _ _ = refl
  hasSelf-sub-occ _ _ i64 _ _ = refl
  hasSelf-sub-occ _ _ f32ty _ _ = refl

  hasSelfList-sub-occ : ∀ {n m} B (τ : Fin n → Tm m) ts
    → hasSelfList B ts ≡ false
    → (∀ x → occursList x ts ≡ true → hasSelf B (τ x) ≡ false)
    → hasSelfList B (subList τ ts) ≡ false
  hasSelfList-sub-occ _ _ [] _ _ = refl
  hasSelfList-sub-occ B τ (t ∷ ts) ht hyp =
    let ht′ , hts = ∨-false₂ (hasSelf B t) (hasSelfList B ts) ht in
    ∨-both-false (hasSelf-sub-occ B τ t ht′ (λ x oc → hyp x (∨-left oc)))
                 (hasSelfList-sub-occ B τ ts hts (λ x oc → hyp x (∨-right oc)))

hasSelf-sub : ∀ {n m} B (τ : Fin n → Tm m) t
  → (∀ x → hasSelf B (τ x) ≡ false)
  → hasSelf B t ≡ false
  → hasSelf B (sub τ t) ≡ false
hasSelf-sub B τ t hf ht = hasSelf-sub-occ B τ t ht (λ x _ → hf x)

hasSelfList-sub : ∀ {n m} B (τ : Fin n → Tm m) ts
  → (∀ x → hasSelf B (τ x) ≡ false)
  → hasSelfList B ts ≡ false
  → hasSelfList B (subList τ ts) ≡ false
hasSelfList-sub B τ ts hf ht = hasSelfList-sub-occ B τ ts ht (λ x _ → hf x)

------------------------------------------------------------------------
-- GuardedTail and GuardedCall are stable under a block-free substitution,
-- and under a substitution that is block-free on the variables that occur.
------------------------------------------------------------------------

mutual
  guarded-sub : ∀ {n m} B (τ : Fin n → Tm m) t
    → (∀ x → hasSelf B (τ x) ≡ false)
    → GuardedTail B t
    → GuardedTail B (sub τ t)
  guarded-sub B τ t hf (gt-absent p) = gt-absent (hasSelf-sub B τ t hf p)
  guarded-sub B τ _ hf (gt-call c) = gt-call (guarded-call-sub B τ hf c)

  guarded-call-sub : ∀ {n m} B (τ : Fin n → Tm m) {t}
    → (∀ x → hasSelf B (τ x) ≡ false)
    → GuardedCall B t
    → GuardedCall B (sub τ t)
  guarded-call-sub _ _ _ (gc-def el) = gc-def el
  guarded-call-sub B τ hf (gc-app {a = a} ha c) =
    gc-app (hasSelf-sub B τ a hf ha) (guarded-call-sub B τ hf c)
  guarded-call-sub B τ hf (gc-pair {a = a} {b = b} ga gb) =
    gc-pair (guarded-sub B τ a hf ga) (guarded-sub B τ b hf gb)
  guarded-call-sub B τ hf (gc-unf {s = s} {A = A} {h = h} {t = t} hs hA hh tg) =
    gc-unf (hasSelf-sub B τ s hf hs)
           (hasSelf-sub B τ A hf hA)
           (hasSelf-sub B (lifts τ) h (lifts-hs B τ hf) hh)
           (guarded-sub B (lifts τ) t (lifts-hs B τ hf) tg)

-- An occurrence of the seed binder in the head, the binder type, or the
-- tail of a nested unfold is an occurrence in the unfold.
unf-occ-A : ∀ {n} {s : Tm n} {q A h t} {x : Fin n}
  → occurs x A ≡ true
  → occurs x (unf s (lam q A (pair h t))) ≡ true
unf-occ-A {s = s} {A = A} {h = h} {t = t} {x = x} oc =
  ∨-right {a = occurs x s}
    (∨-left {b = occurs (suc x) h ∨ occurs (suc x) t} oc)

unf-occ-h : ∀ {n} {s : Tm n} {q A h t} {x : Fin n}
  → occurs (suc x) h ≡ true
  → occurs x (unf s (lam q A (pair h t))) ≡ true
unf-occ-h {s = s} {A = A} {h = h} {t = t} {x = x} oc =
  ∨-right {a = occurs x s}
    (∨-right {a = occurs x A} (∨-left {b = occurs (suc x) t} oc))

unf-occ-t : ∀ {n} {s : Tm n} {q A h t} {x : Fin n}
  → occurs (suc x) t ≡ true
  → occurs x (unf s (lam q A (pair h t))) ≡ true
unf-occ-t {s = s} {A = A} {h = h} {x = x} oc =
  ∨-right {a = occurs x s}
    (∨-right {a = occurs x A} (∨-right {a = occurs (suc x) h} oc))

unf-h-lifts : ∀ {n m} B (τ : Fin n → Tm m) s q A h t
  → (∀ x → occurs x (unf s (lam q A (pair h t))) ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ y → occurs y h ≡ true → hasSelf B (lifts τ y) ≡ false
unf-h-lifts _ _ _ _ _ _ _ _ zero _ = refl
unf-h-lifts B τ s q A h t hyp (suc y) oc =
  trans (hasSelf-ren B suc (τ y))
    (hyp y (unf-occ-h {s = s} {q = q} {A = A} {h = h} {t = t} {x = y} oc))

unf-t-lifts : ∀ {n m} B (τ : Fin n → Tm m) s q A h t
  → (∀ x → occurs x (unf s (lam q A (pair h t))) ≡ true → hasSelf B (τ x) ≡ false)
  → ∀ y → occurs y t ≡ true → hasSelf B (lifts τ y) ≡ false
unf-t-lifts _ _ _ _ _ _ _ _ zero _ = refl
unf-t-lifts B τ s q A h t hyp (suc y) oc =
  trans (hasSelf-ren B suc (τ y))
    (hyp y (unf-occ-t {s = s} {q = q} {A = A} {h = h} {t = t} {x = y} oc))

mutual
  guarded-sub-occ : ∀ {n m} B (τ : Fin n → Tm m) t
    → GuardedTail B t
    → (∀ x → occurs x t ≡ true → hasSelf B (τ x) ≡ false)
    → GuardedTail B (sub τ t)
  guarded-sub-occ B τ t (gt-absent p) hyp =
    gt-absent (hasSelf-sub-occ B τ t p hyp)
  guarded-sub-occ B τ _ (gt-call c) hyp =
    gt-call (guarded-call-sub-occ B τ c hyp)

  guarded-call-sub-occ : ∀ {n m} B (τ : Fin n → Tm m) {t}
    → GuardedCall B t
    → (∀ x → occurs x t ≡ true → hasSelf B (τ x) ≡ false)
    → GuardedCall B (sub τ t)
  guarded-call-sub-occ _ _ (gc-def el) _ = gc-def el
  guarded-call-sub-occ B τ (gc-app {a = a} ha c) hyp =
    gc-app (hasSelf-sub-occ B τ a ha (λ x oc → hyp x (∨-right oc)))
           (guarded-call-sub-occ B τ c (λ x oc → hyp x (∨-left oc)))
  guarded-call-sub-occ B τ (gc-pair {a = a} {b = b} ga gb) hyp =
    gc-pair (guarded-sub-occ B τ a ga (λ x oc → hyp x (∨-left oc)))
            (guarded-sub-occ B τ b gb (λ x oc → hyp x (∨-right oc)))
  guarded-call-sub-occ B τ (gc-unf {s = s} {q = q} {A = A} {h = h} {t = t} hs hA hh tg) hyp =
    gc-unf (hasSelf-sub-occ B τ s hs (λ x oc → hyp x (∨-left oc)))
           (hasSelf-sub-occ B τ A hA (λ x oc → hyp x (unf-occ-A {s = s} {q = q} {A = A} {h = h} {t = t} {x = x} oc)))
           (hasSelf-sub-occ B (lifts τ) h hh (unf-h-lifts B τ s q A h t hyp))
           (guarded-sub-occ B (lifts τ) t tg (unf-t-lifts B τ s q A h t hyp))

instσ-free : ∀ {n} B {s : Tm n}
  → hasSelf B s ≡ false
  → ∀ x → hasSelf B (instσ s x) ≡ false
instσ-free _ hs zero    = hs
instσ-free _ _  (suc _) = refl

instσ-occ : ∀ {n} B {s : Tm n} {t : Tm (suc n)}
  → (occurs zero t ≡ true → hasSelf B s ≡ false)
  → ∀ x → occurs x t ≡ true → hasSelf B (instσ s x) ≡ false
instσ-occ _ hyp zero    oc = hyp oc
instσ-occ _ _   (suc _) _  = refl

guarded-inst : ∀ {n} B {t : Tm (suc n)} {s : Tm n}
  → GuardedTail B t → hasSelf B s ≡ false → GuardedTail B (inst t s)
guarded-inst B {t = t} {s = s} g hs = guarded-sub B (instσ s) t (instσ-free B hs) g

guarded-inst-occ : ∀ {n} B {t : Tm (suc n)} {s : Tm n}
  → GuardedTail B t
  → (occurs zero t ≡ true → hasSelf B s ≡ false)
  → GuardedTail B (inst t s)
guarded-inst-occ B {t = t} {s = s} g hyp =
  guarded-sub-occ B (instσ s) t g (instσ-occ B {s = s} {t = t} hyp)

hasSelf-inst : ∀ {n} B {t : Tm (suc n)} {s : Tm n}
  → hasSelf B t ≡ false → hasSelf B s ≡ false → hasSelf B (inst t s) ≡ false
hasSelf-inst B {t = t} {s = s} ht hs = hasSelf-sub B (instσ s) t (instσ-free B hs) ht

hasSelf-inst-occ : ∀ {n} B {t : Tm (suc n)} {s : Tm n}
  → hasSelf B t ≡ false
  → (occurs zero t ≡ true → hasSelf B s ≡ false)
  → hasSelf B (inst t s) ≡ false
hasSelf-inst-occ B {t = t} {s = s} ht hyp =
  hasSelf-sub-occ B (instσ s) t ht (instσ-occ B {s = s} {t = t} hyp)

------------------------------------------------------------------------
-- Stage 1. A guarded tail unrolls to every finite depth.
--
-- The measure is the depth. Instantiating a tail (Stage 0) happens
-- before the recursive call, which is at the predecessor depth.
-- BlockClosed is a hypothesis, not a consequence of checkSig: reaches
-- is reachGo with fuel suc (length of the definitions) and a visited
-- set. A mention is an edge when the target looks up, but closure of
-- component needs that search to be transitive, which is not proved.
------------------------------------------------------------------------

fromZero-id : ∀ (x : Fin 0) → fromZero {0} x ≡ x
fromZero-id ()

closed₀ : (t : Tm 0) → closed {0} t ≡ t
closed₀ t = trans (ren-ext (λ x → fromZero-id x) t) (ren-id t)

-- The seed binder occurs in the head. Acceptance of that unfold forces
-- the seed to be block-free; a dead head does not.
HeadSeed : ∀ {n} → List ℕ → Tm (suc n) → Tm n → Set
HeadSeed B h s = occurs zero h ≡ true → hasSelf B s ≡ false

-- The tail does not read the seed, or the head does (and then HeadSeed
-- applies), or the seed does not mention the block. A seed that mentions
-- the block and occurs only in the tail is none of these. The checker
-- refuses that form. A block-free seed is the third disjunct, so a tail
-- that reads it is covered.
SeedCovered : ∀ {n} → List ℕ → Tm (suc n) → Tm (suc n) → Tm n → Set
SeedCovered B h t s =
  occurs zero t ≡ false ⊎ occurs zero h ≡ true ⊎ hasSelf B s ≡ false

tail-from-cover : ∀ {n} B {h t : Tm (suc n)} {s : Tm n}
  → HeadSeed B h s → SeedCovered B h t s
  → occurs zero t ≡ true → hasSelf B s ≡ false
tail-from-cover _ hs (inj₁ dead) oc = ⊥-elim (true≢false (trans (sym oc) dead))
tail-from-cover _ hs (inj₂ (inj₁ oh)) _ = hs oh
tail-from-cover _ _  (inj₂ (inj₂ free)) _ = free

head-inst : ∀ {n} B {h : Tm (suc n)} {s : Tm n}
  → hasSelf B h ≡ false → HeadSeed B h s
  → hasSelf B (inst h s) ≡ false
head-inst B {h = h} {s = s} hh hs = hasSelf-inst-occ B {t = h} {s = s} hh hs

cov-sub : ∀ {n m} B (τ : Fin n → Tm m) (h t : Tm (suc n)) (s : Tm n)
  → (∀ x → hasSelf B (τ x) ≡ false)
  → SeedCovered B h t s
  → SeedCovered B (sub (lifts τ) h) (sub (lifts τ) t) (sub τ s)
cov-sub B τ h t s hf (inj₁ p) = inj₁ (trans (occurs-zero-lifts τ t) p)
cov-sub B τ h t s hf (inj₂ (inj₁ p)) = inj₂ (inj₁ (trans (occurs-zero-lifts τ h) p))
cov-sub B τ h t s hf (inj₂ (inj₂ p)) = inj₂ (inj₂ (hasSelf-sub B τ s hf p))

-- The occurrence-restricted form. Images may mention the block on
-- variables the seed does not read.
cov-occ : ∀ {n m} B (τ : Fin n → Tm m) (h t : Tm (suc n)) (s : Tm n)
  → SeedCovered B h t s
  → (∀ x → occurs x s ≡ true → hasSelf B (τ x) ≡ false)
  → SeedCovered B (sub (lifts τ) h) (sub (lifts τ) t) (sub τ s)
cov-occ B τ h t s (inj₁ p) _ = inj₁ (trans (occurs-zero-lifts τ t) p)
cov-occ B τ h t s (inj₂ (inj₁ p)) _ = inj₂ (inj₁ (trans (occurs-zero-lifts τ h) p))
cov-occ B τ h t s (inj₂ (inj₂ p)) hyp = inj₂ (inj₂ (hasSelf-sub-occ B τ s p hyp))

headseed-sub : ∀ {n m} B (τ : Fin n → Tm m) {h : Tm (suc n)} {s : Tm n}
  → (∀ x → hasSelf B (τ x) ≡ false)
  → HeadSeed B h s
  → HeadSeed B (sub (lifts τ) h) (sub τ s)
headseed-sub B τ {h} {s} hf hs oc =
  hasSelf-sub B τ s hf (hs (trans (sym (occurs-zero-lifts τ h)) oc))

-- What a block member's body is allowed to be. The seed is HeadSeed
-- and SeedCovered, not an unconditional hasSelf of the seed: that is
-- all acceptance gives. SeedCovered's third disjunct is the block-free
-- seed, including one the tail reads.
data BodyShape (B : List ℕ) : ∀ {n} → Tm n → Set where
  sh-free : ∀ {n} {t : Tm n} → hasSelf B t ≡ false → BodyShape B t
  sh-unf  : ∀ {n} {s : Tm n} {q A} {h t : Tm (suc n)}
          → hasSelf B h ≡ false
          → HeadSeed B h s
          → GuardedTail B t
          → SeedCovered B h t s
          → BodyShape B (unf s (lam q A (pair h t)))
  sh-lam  : ∀ {n q A} {t : Tm (suc n)} → BodyShape B t → BodyShape B (lam q A t)

shape-sub : ∀ {n m} B {t : Tm n} (τ : Fin n → Tm m)
  → (∀ x → hasSelf B (τ x) ≡ false)
  → BodyShape B t → BodyShape B (sub τ t)
shape-sub B {t} τ hf (sh-free p) = sh-free (hasSelf-sub B τ t hf p)
shape-sub B τ hf (sh-lam sh) =
  sh-lam (shape-sub B (lifts τ) (lifts-hs B τ hf) sh)
shape-sub B τ hf (sh-unf {s = s} {h = h} {t = t} hh hs tg cov) =
  sh-unf (hasSelf-sub B (lifts τ) h (lifts-hs B τ hf) hh)
         (headseed-sub B τ {h} {s} hf hs)
         (guarded-sub B (lifts τ) t (lifts-hs B τ hf) tg)
         (cov-sub B τ h t s hf cov)

shape-inst : ∀ {n} B {t : Tm (suc n)} {a : Tm n}
  → BodyShape B t → hasSelf B a ≡ false → BodyShape B (inst t a)
shape-inst B {t} {a} sh ha = shape-sub B {t} (instσ a) (instσ-free B ha) sh

mentionsBody : Sig → ℕ → List ℕ
mentionsBody σ i with lookupDef σ i
... | ok d   = mentions (Def.dbody d)
... | fail _ = []

-- If i is in the block, j is mentioned by i's body, and j reaches i,
-- then j is in the block. Not derived here.
BlockClosed : Sig → List ℕ → Set
BlockClosed σ B =
  ∀ i j → elemℕ i B ≡ true
        → elemℕ j (mentionsBody σ i) ≡ true
        → reaches σ j i ≡ true
        → elemℕ j B ≡ true

-- closed is carried so a use of Bodies is a use of the hypothesis.
Bodies : Sig → List ℕ → Set
Bodies σ B =
  BlockClosed σ B
  × (∀ i → elemℕ i B ≡ true
       → Σ Def λ d → lookupDef σ i ≡ ok d × BodyShape B (Def.dbody d))

bodies-closed : ∀ {σ B} → Bodies σ B → BlockClosed σ B
bodies-closed = proj₁

bodies-at : ∀ {σ B} → Bodies σ B → ∀ i → elemℕ i B ≡ true
  → Σ Def λ d → lookupDef σ i ≡ ok d × BodyShape B (Def.dbody d)
bodies-at = proj₂

data AllFree (B : List ℕ) : List (Tm 0) → Set where
  af-[] : AllFree B []
  af-∷  : ∀ {a as} → hasSelf B a ≡ false → AllFree B as → AllFree B (a ∷ as)

-- Innermost argument first: foldApp t (a ∷ b ∷ []) = app (app t a) b.
foldApp : Tm 0 → List (Tm 0) → Tm 0
foldApp t []       = t
foldApp t (a ∷ as) = foldApp (app t a) as

foldApp-++ : ∀ t as bs → foldApp t (as ++ bs) ≡ foldApp (foldApp t as) bs
foldApp-++ t []       bs = refl
foldApp-++ t (a ∷ as) bs = foldApp-++ (app t a) as bs

foldApp-snoc : ∀ t as a → foldApp t (as ++ a ∷ []) ≡ app (foldApp t as) a
foldApp-snoc t as a = foldApp-++ t as (a ∷ [])

allFree-snoc : ∀ {B a as} → AllFree B as → hasSelf B a ≡ false → AllFree B (as ++ a ∷ [])
allFree-snoc af-[]        h = af-∷ h af-[]
allFree-snoc (af-∷ h′ rs) h = af-∷ h′ (allFree-snoc rs h)

-- Substituting block-free arguments for leading lambdas.
data Open (B : List ℕ) : Tm 0 → List (Tm 0) → Tm 0 → Set where
  op-[] : ∀ {t} → Open B t [] t
  op-∷  : ∀ {q A t a as r}
        → hasSelf B a ≡ false
        → Open B (inst t a) as r
        → Open B (lam q A t) (a ∷ as) r

record Drove (B : List ℕ) (t : Tm 0) (as : List (Tm 0)) : Set where
  constructor drove
  field
    consumed : List (Tm 0)
    leftover : List (Tm 0)
    rest     : Tm 0
    opened   : Open B t consumed rest
    shape    : BodyShape B rest
    leftFree : AllFree B leftover
    split    : as ≡ consumed ++ leftover

drive : ∀ {B t as} → BodyShape B t → AllFree B as → Drove B t as
drive {t = t} sh af-[] = drove [] [] t op-[] sh af-[] refl
drive {t = t} (sh-free p) (af-∷ {a} {as} ha rest) =
  drove [] (a ∷ as) t op-[] (sh-free p) (af-∷ ha rest) refl
drive (sh-unf {s = s} {q = q} {A = A} {h = h} {t = t} hh hs tg cov) (af-∷ {a} {as} ha rest) =
  drove [] (a ∷ as) (unf s (lam q A (pair h t))) op-[] (sh-unf hh hs tg cov) (af-∷ ha rest) refl
drive {B} (sh-lam {t = t} sh) (af-∷ {a} ha rest) with drive (shape-inst B {t} {a} sh ha) rest
... | drove cs ls r op sh′ fr eq =
  drove (a ∷ cs) ls r (op-∷ ha op) sh′ fr (cong (a ∷_) eq)

data Unrolls (σ : Sig) (B : List ℕ) : ℕ → Tm 0 → Set where
  un-zero : ∀ {t} → Unrolls σ B zero t
  un-absent : ∀ {d t} → hasSelf B t ≡ false → Unrolls σ B (suc d) t
  un-pair : ∀ {d a b}
    → Unrolls σ B (suc d) a → Unrolls σ B (suc d) b
    → Unrolls σ B (suc d) (pair a b)
  un-nest : ∀ {d s q A h t}
    → hasSelf B (inst h s) ≡ false
    → Unrolls σ B d (inst t s)
    → Unrolls σ B (suc d) (unf s (lam q A (pair h t)))
  -- Nullary call. The body is the unfold itself.
  un-call : ∀ {d i s q A h t dfn}
    → lookupDef σ i ≡ ok dfn
    → elemℕ i B ≡ true
    → Def.dbody dfn ≡ unf s (lam q A (pair h t))
    → hasSelf B (inst h s) ≡ false
    → Unrolls σ B d (inst t s)
    → Unrolls σ B (suc d) (def i)
  -- The opened body is block-free, or still a λ (under-applied).
  un-stop : ∀ {d i as r dfn}
    → lookupDef σ i ≡ ok dfn
    → elemℕ i B ≡ true
    → Open B (Def.dbody dfn) as r
    → (hasSelf B r ≡ false) ⊎ (Σ Qty λ q → Σ (Tm 0) λ A → Σ (Tm 1) λ t → r ≡ lam q A t)
    → Unrolls σ B (suc d) (foldApp (def i) as)
  -- Leading λs consumed by block-free arguments, then an unfold.
  un-args : ∀ {d i as s q A h t dfn}
    → lookupDef σ i ≡ ok dfn
    → elemℕ i B ≡ true
    → Open B (Def.dbody dfn) as (unf s (lam q A (pair h t)))
    → hasSelf B (inst h s) ≡ false
    → Unrolls σ B d (inst t s)
    → Unrolls σ B (suc d) (foldApp (def i) as)
  -- An application of a call that is not a definition spine.
  un-keep : ∀ {d f a}
    → Unrolls σ B (suc d) f
    → hasSelf B a ≡ false
    → Unrolls σ B (suc d) (app f a)

un-keep* : ∀ {σ B d t as}
  → Unrolls σ B (suc d) t → AllFree B as
  → Unrolls σ B (suc d) (foldApp t as)
un-keep* u af-[] = u
un-keep* u (af-∷ ha rest) = un-keep* (un-keep u ha) rest

data Found (B : List ℕ) (t : Tm 0) : Set where
  fd-spine : ∀ i as
    → elemℕ i B ≡ true → AllFree B as → t ≡ foldApp (def i) as
    → Found B t
  fd-other : Found B t

find : ∀ {B t} → GuardedCall B t → Found B t
find (gc-def {i} el) = fd-spine i [] el af-[] refl
find (gc-app {f} {a} ha c) with find c
... | fd-spine i as el fr eq =
  fd-spine i (as ++ a ∷ []) el (allFree-snoc fr ha)
    (trans (cong (λ z → app z a) eq) (sym (foldApp-snoc (def i) as a)))
... | fd-other = fd-other
find (gc-pair _ _) = fd-other
find (gc-unf _ _ _ _) = fd-other

tail-inst : ∀ {n} B {h t : Tm (suc n)} {s : Tm n}
  → HeadSeed B h s → SeedCovered B h t s → GuardedTail B t
  → GuardedTail B (inst t s)
tail-inst B {h} {t} {s} hs cov tg =
  guarded-inst-occ B {t = t} {s = s} tg (tail-from-cover B {h} {t} {s} hs cov)

-- Theorem A. At every depth the head a guarded tail reaches is
-- block-free, and the observation continues into a call with the same
-- hypothesis. Calls with arguments substitute those arguments, which
-- are block-free, for the leading lambdas of the body.
mutual
  guarded-unrolls : ∀ {σ B t} → Bodies σ B → GuardedTail B t → ∀ d → Unrolls σ B d t
  guarded-unrolls _   _ zero    = un-zero
  guarded-unrolls bod g (suc d) = unroll-suc bod g d

  unroll-suc : ∀ {σ B t} → Bodies σ B → GuardedTail B t → ∀ d → Unrolls σ B (suc d) t
  unroll-suc _   (gt-absent p) d = un-absent p
  unroll-suc bod (gt-call c)   d = unroll-call bod c d

  unroll-call : ∀ {σ B t} → Bodies σ B → GuardedCall B t → ∀ d → Unrolls σ B (suc d) t
  unroll-call bod (gc-pair ga gb) d =
    un-pair (unroll-suc bod ga d) (unroll-suc bod gb d)
  unroll-call bod (gc-unf hs hA hh tg) d = nest-unroll bod hs hA hh tg d
  unroll-call bod (gc-def {i} el) d = finish i bod el af-[] (def i) refl d
  unroll-call bod (gc-app {f = f} {a = a} ha c) d with find c
  ... | fd-other = un-keep (unroll-call bod c d) ha
  ... | fd-spine i as el fr eq =
    finish i bod el (allFree-snoc fr ha) (app f a)
      (trans (cong (λ z → app z a) eq) (sym (foldApp-snoc (def i) as a))) d

  nest-unroll : ∀ {σ B s q A h t} → Bodies σ B
    → hasSelf B s ≡ false → hasSelf B A ≡ false → hasSelf B h ≡ false
    → GuardedTail B t → ∀ d
    → Unrolls σ B (suc d) (unf s (lam q A (pair h t)))
  nest-unroll {B = B} {s = s} {h = h} {t = t} bod hs _ hh tg d =
    un-nest (head-inst B {h = h} {s = s} hh (λ _ → hs))
            (guarded-unrolls bod (guarded-inst B {t = t} {s = s} tg hs) d)

  -- fd-spine already snocs in find, but unroll-call on gc-app redoes it
  -- from the function's find so the recursive call on a non-spine is the
  -- only same-depth call, and it is on a smaller GuardedCall.
  finish : ∀ {σ B} (i : ℕ) {as} → Bodies σ B → elemℕ i B ≡ true → AllFree B as
    → (t : Tm 0) → t ≡ foldApp (def i) as → ∀ d → Unrolls σ B (suc d) t
  finish {σ} {B} i bod el fr t eq d =
    finish-at {σ} {B} i bod el fr t eq d (bodies-at {σ} {B} bod i el)

  finish-at : ∀ {σ B} (i : ℕ) {as} → Bodies σ B → elemℕ i B ≡ true → AllFree B as
    → (t : Tm 0) → t ≡ foldApp (def i) as → ∀ d
    → Σ Def (λ dfn → lookupDef σ i ≡ ok dfn × BodyShape B (Def.dbody dfn))
    → Unrolls σ B (suc d) t
  finish-at {σ} {B} i bod el fr t eq d (dfn , lk , sh) =
    subst (λ z → Unrolls σ B (suc d) z) (sym eq)
      (cover {σ} {B} i bod el lk d (drive sh fr))

  cover : ∀ {σ B} (i : ℕ) {as dfn} → Bodies σ B → elemℕ i B ≡ true
    → lookupDef σ i ≡ ok dfn → ∀ d
    → Drove B (Def.dbody dfn) as
    → Unrolls σ B (suc d) (foldApp (def i) as)
  cover {σ} {B} i bod el lk d (drove cs ls r op sh fr split) =
    subst (λ zs → Unrolls σ B (suc d) (foldApp (def i) zs)) (sym split)
      (subst (λ z → Unrolls σ B (suc d) z)
        (sym (foldApp-++ (def i) cs ls))
        (un-keep* (core {σ} {B} i bod el lk d op sh) fr))

  core : ∀ {σ B} (i : ℕ) {cs r dfn} → Bodies σ B → elemℕ i B ≡ true
    → lookupDef σ i ≡ ok dfn → ∀ d
    → Open B (Def.dbody dfn) cs r
    → BodyShape B r
    → Unrolls σ B (suc d) (foldApp (def i) cs)
  core i _ el lk d op-[] (sh-free p) = un-stop lk el op-[] (inj₁ p)
  core i _ el lk d op (sh-free p) = un-stop lk el op (inj₁ p)
  core i _ el lk d op (sh-lam {q = q} {A = A} {t = t} _) =
    un-stop lk el op (inj₂ (q , A , t , refl))
  core {B = B} i bod el lk d op-[] (sh-unf {s = s} {q = q} {A = A} {h = h} {t = t} hh hs tg cov) =
    un-call lk el refl (head-inst B {h} {s} hh hs)
      (guarded-unrolls bod (tail-inst B {h} {t} {s} hs cov tg) d)
  core {B = B} i bod el lk d op (sh-unf {s = s} {q = q} {A = A} {h = h} {t = t} hh hs tg cov) =
    un-args lk el op (head-inst B {h} {s} hh hs)
      (guarded-unrolls bod (tail-inst B {h} {t} {s} hs cov tg) d)

------------------------------------------------------------------------
-- One observation. fam = true is the family reading: the subject
-- reduces to unf s (λ. (h , t)) and the pair is (inst h s, inst t s).
-- fam = false is the stream reading, and only for a block-free tail:
-- the next subject is the same step at the next seed. A call in a
-- stream tail is not a Reads here.
------------------------------------------------------------------------

data Reads (σ : Sig) (m : Mode) : Bool → Tm 0 → Tm 0 → Tm 0 → Set where
  rd-fam : ∀ {t s q A h tl}
    → σ ⊢[ m ] t ⇛* unf s (lam q A (pair h tl))
    → Reads σ m true t (inst h s) (inst tl s)
  rd-str : ∀ {s q A h tl}
    → σ ⊢[ m ] app (lam q A (pair h tl)) s ⇛* pair (inst h s) (inst tl s)
    → Reads σ m false (unf s (lam q A (pair h tl)))
        (inst h s) (unf (inst tl s) (lam q A (pair h tl)))

-- Obs d is d + 1 observations. The index counts the tails still to read
-- after the first head. Every head in the chain is block-free.
Obs : Sig → Mode → List ℕ → Bool → ℕ → Tm 0 → Set
Obs σ m B fam zero t =
  Σ (Tm 0) λ h → Σ (Tm 0) λ t′ → Reads σ m fam t h t′ × (hasSelf B h ≡ false)
Obs σ m B fam (suc d) t =
  Σ (Tm 0) λ h → Σ (Tm 0) λ t′ →
    Reads σ m fam t h t′ × (hasSelf B h ≡ false) × Obs σ m B fam d t′

β-unf : ∀ {σ m} {q} {A s : Tm 0} {h t : Tm 1}
  → σ ⊢[ m ] app (lam q A (pair h t)) s ⇛* pair (inst h s) (inst t s)
β-unf {σ} {m} {q} {A} {s} {h} {t} =
  ⇛*-one (⇛-β {q = q} {A = A} {t = pair h t} {a = s}
              (⇛-refl (pair h t)) (⇛-refl s))

δ-body : ∀ {σ m} (i : ℕ) (dfn : Def) (b : Tm 0)
  → lookupDef σ i ≡ ok dfn
  → allowedDef (Def.dmode dfn) m ≡ true
  → closed {0} (Def.dbody dfn) ≡ b
  → σ ⊢[ m ] def i ⇛* b
δ-body {σ} {m} i dfn b lk al eq =
  ⇛*-one (subst (λ z → σ ⊢[ m ] def i ⇛ z) eq
            (⇛-δ {n = 0} {i = i} {d = dfn} lk al))

δ-unf : ∀ {σ m} (i : ℕ) (dfn : Def)
  → lookupDef σ i ≡ ok dfn
  → allowedDef (Def.dmode dfn) m ≡ true
  → σ ⊢[ m ] def i ⇛* Def.dbody dfn
δ-unf {σ} {m} i dfn lk al =
  δ-body {σ} {m} i dfn (Def.dbody dfn) lk al (closed₀ (Def.dbody dfn))

app-step : ∀ {σ m} {f f′ a : Tm 0}
  → σ ⊢[ m ] f ⇛ f′ → σ ⊢[ m ] app f a ⇛ app f′ a
app-step {σ} {m} {a = a} d = ⇛-app {a = a} d (⇛-refl a)

app-star : ∀ {σ m} {f f′ a : Tm 0}
  → σ ⊢[ m ] f ⇛* f′ → σ ⊢[ m ] app f a ⇛* app f′ a
app-star {a = a} ⇛*-refl = ⇛*-refl
app-star {σ} {m} {a = a} (⇛*-step d r) =
  ⇛*-step (app-step {σ} {m} {a = a} d) (app-star {a = a} r)

fold-star : ∀ {σ m} {t t′ : Tm 0} {as : List (Tm 0)}
  → σ ⊢[ m ] t ⇛* t′ → σ ⊢[ m ] foldApp t as ⇛* foldApp t′ as
fold-star {as = []} r = r
fold-star {σ} {m} {as = a ∷ as} r =
  fold-star {σ} {m} {as = as} (app-star {σ} {m} {a = a} r)

β-inst : ∀ {σ m} {q} {A a : Tm 0} {t : Tm 1}
  → σ ⊢[ m ] app (lam q A t) a ⇛* inst t a
β-inst {σ} {m} {q} {A} {a} {t} =
  ⇛*-one (⇛-β {q = q} {A = A} {t = t} {a = a} (⇛-refl t) (⇛-refl a))

open-star : ∀ {σ m B t as r}
  → Open B t as r → σ ⊢[ m ] foldApp t as ⇛* r
open-star op-[] = ⇛*-refl
open-star {σ} {m} (op-∷ {q = q} {A = A} {t = t} {a = a} {as = as} _ op) =
  ⇛*-trans (fold-star {σ} {m} {as = as}
              (β-inst {σ} {m} {q = q} {A = A} {a = a} {t = t}))
           (open-star op)

spine-star : ∀ {σ m B i as r dfn}
  → lookupDef σ i ≡ ok dfn
  → allowedDef (Def.dmode dfn) m ≡ true
  → Open B (Def.dbody dfn) as r
  → σ ⊢[ m ] foldApp (def i) as ⇛* r
spine-star {σ} {m} {i = i} {as = as} {dfn = dfn} lk al op =
  ⇛*-trans (fold-star {σ} {m} {t = def i} {t′ = Def.dbody dfn} {as = as}
              (δ-unf {σ} {m} i dfn lk al))
           (open-star op)

-- The next seed of a block-free tail stays block-free when the head
-- reads the binder, because that is when the original seed is.
hs-next : ∀ {n} B {h t : Tm (suc n)} {s : Tm n}
  → HeadSeed B h s → hasSelf B t ≡ false
  → HeadSeed B h (inst t s)
hs-next B {t = t} {s = s} hs ht oc = hasSelf-inst B {t = t} {s = s} ht (hs oc)

-- Stream, block-free tail, every depth. The step λ does not change.
-- A tail that mentions the block is not this theorem.
obs-stream : ∀ {σ m B} {q} {A s : Tm 0} {h t : Tm 1}
  → hasSelf B h ≡ false → hasSelf B t ≡ false → HeadSeed B h s
  → ∀ d → Obs σ m B false d (unf s (lam q A (pair h t)))
obs-stream {σ} {m} {B} {q} {A} {s} {h} {t} hh ht hs zero =
  inst h s , unf (inst t s) (lam q A (pair h t)) ,
  rd-str (β-unf {σ} {m} {q = q} {A = A} {s = s} {h = h} {t = t}) ,
  head-inst B {h = h} {s = s} hh hs
obs-stream {σ} {m} {B} {q} {A} {s} {h} {t} hh ht hs (suc d) =
  inst h s , unf (inst t s) (lam q A (pair h t)) ,
  rd-str (β-unf {σ} {m} {q = q} {A = A} {s = s} {h = h} {t = t}) ,
  head-inst B {h = h} {s = s} hh hs ,
  obs-stream {σ} {m} {B} {q = q} {A = A} {s = inst t s} {h = h} {t = t}
    hh ht (hs-next B {h = h} {t = t} {s = s} hs ht) d

------------------------------------------------------------------------
-- Family calls. A call shape is a block member, an application of one
-- whose arguments do not mention the block, or a nested unfold whose
-- tail is again a call shape. Pairs are not a single observation chain.
-- self-calls are leaves (cs-def): the shape does not contain the
-- target's tail, so a loop is a finite derivation.
------------------------------------------------------------------------

data CallShape (B : List ℕ) {n} : Tm n → Set where
  cs-def : ∀ {i} → elemℕ i B ≡ true → CallShape B (def i)
  cs-app : ∀ {f a} → hasSelf B a ≡ false → CallShape B f → CallShape B (app f a)
  cs-unf : ∀ {s q A h t}
    → hasSelf B h ≡ false
    → HeadSeed B h s
    → SeedCovered B h t s
    → CallShape B t
    → CallShape B (unf s (lam q A (pair h t)))

callshape-sub : ∀ {n m} B (τ : Fin n → Tm m) (t : Tm n)
  → (∀ x → hasSelf B (τ x) ≡ false)
  → CallShape B t → CallShape B (sub τ t)
callshape-sub _ _ _ _ (cs-def el) = cs-def el
callshape-sub B τ _ hf (cs-app {f = f} {a = a} ha c) =
  cs-app (hasSelf-sub B τ a hf ha) (callshape-sub B τ f hf c)
callshape-sub B τ _ hf (cs-unf {s = s} {h = h} {t = t} hh hs cov c) =
  cs-unf (hasSelf-sub B (lifts τ) h (lifts-hs B τ hf) hh)
         (headseed-sub B τ {h} {s} hf hs)
         (cov-sub B τ h t s hf cov)
         (callshape-sub B (lifts τ) t (lifts-hs B τ hf) c)

callshape-inst : ∀ {n} B {t : Tm (suc n)} {a : Tm n}
  → CallShape B t → hasSelf B a ≡ false → CallShape B (inst t a)
callshape-inst B {t} {a} c ha = callshape-sub B (instσ a) t (instσ-free B ha) c

-- Occurrence-restricted, for the seed of an unfold. The seed may
-- mention the block when the term does not read it.
headseed-occ : ∀ {n m} B (τ : Fin n → Tm m) {h : Tm (suc n)} {s : Tm n}
  → HeadSeed B h s
  → (∀ x → occurs x s ≡ true → hasSelf B (τ x) ≡ false)
  → HeadSeed B (sub (lifts τ) h) (sub τ s)
headseed-occ B τ {h} {s} hs hyp oc =
  hasSelf-sub-occ B τ s (hs (trans (sym (occurs-zero-lifts τ h)) oc)) hyp

mutual
  callshape-occ : ∀ {n m} B (τ : Fin n → Tm m) (t : Tm n)
    → CallShape B t
    → (∀ x → occurs x t ≡ true → hasSelf B (τ x) ≡ false)
    → CallShape B (sub τ t)
  callshape-occ _ _ _ (cs-def el) _ = cs-def el
  callshape-occ B τ _ (cs-app {f = f} {a = a} ha c) hyp =
    cs-app (hasSelf-sub-occ B τ a ha (λ x oc → hyp x (∨-right {a = occurs x f} oc)))
           (callshape-occ B τ f c (λ x oc → hyp x (∨-left {b = occurs x a} oc)))
  callshape-occ B τ _ (cs-unf {s = s} {q = q} {A = A} {h = h} {t = t} hh hs cov c) hyp =
    cs-unf (hasSelf-sub-occ B (lifts τ) h hh (unf-h-lifts B τ s q A h t hyp))
           (headseed-occ B τ {h} {s} hs (λ x oc → hyp x (∨-left {b = occurs x (lam q A (pair h t))} oc)))
           (cov-occ B τ h t s cov (λ x oc → hyp x (∨-left {b = occurs x (lam q A (pair h t))} oc)))
           (callshape-occ B (lifts τ) t c (unf-t-lifts B τ s q A h t hyp))

callshape-seed : ∀ {n} B {t : Tm (suc n)} {s : Tm n}
  → CallShape B t
  → (occurs zero t ≡ true → hasSelf B s ≡ false)
  → CallShape B (inst t s)
callshape-seed B {t} {s} c hyp = callshape-occ B (instσ s) t c (instσ-occ B {s = s} {t = t} hyp)

data ProdBody (B : List ℕ) : ∀ {n} → Tm n → Set where
  pb-lam : ∀ {n q A} {t : Tm (suc n)} → ProdBody B t → ProdBody B (lam q A t)
  pb-unf : ∀ {n} {s : Tm n} {q A} {h t : Tm (suc n)}
    → hasSelf B h ≡ false
    → HeadSeed B h s
    → SeedCovered B h t s
    → CallShape B t
    → ProdBody B (unf s (lam q A (pair h t)))

-- What a block member must be for a family observation at every depth:
-- leading λs, then one unfold, whose tail is a call shape. Closure of
-- the block is kept beside it and is not used to build the observation.
record Prod (σ : Sig) (m : Mode) (B : List ℕ) : Set where
  constructor mkProd
  field
    blkClosed : BlockClosed σ B
    memb : ∀ i → elemℕ i B ≡ true → Σ Def λ d →
      lookupDef σ i ≡ ok d × allowedDef (Def.dmode d) m ≡ true ×
      ProdBody B (Def.dbody d)

prod-sub : ∀ {n m} B {t : Tm n} (τ : Fin n → Tm m)
  → (∀ x → hasSelf B (τ x) ≡ false)
  → ProdBody B t → ProdBody B (sub τ t)
prod-sub B τ hf (pb-lam pb) =
  pb-lam (prod-sub B (lifts τ) (lifts-hs B τ hf) pb)
prod-sub B τ hf (pb-unf {s = s} {h = h} {t = t} hh hs cov c) =
  pb-unf (hasSelf-sub B (lifts τ) h (lifts-hs B τ hf) hh)
         (headseed-sub B τ {h} {s} hf hs)
         (cov-sub B τ h t s hf cov)
         (callshape-sub B (lifts τ) t (lifts-hs B τ hf) c)

prod-inst : ∀ {n} B {t : Tm (suc n)} {a : Tm n}
  → ProdBody B t → hasSelf B a ≡ false → ProdBody B (inst t a)
prod-inst B {t} {a} pb ha = prod-sub B {t} (instσ a) (instσ-free B ha) pb

------------------------------------------------------------------------
-- Family navigation. A Nav is a block-member spine (arguments do not
-- mention the block) or one nested unfold whose tail is again a Nav.
-- An application of an unfold is not a Nav: that redex is not the
-- family reading. A self-call is a finite leaf (nv-sp); the target's
-- tail is not stored in the spine, so a loop does not have to be an
-- infinite derivation. The index i and the argument count k are
-- parameters of the spine, so substitution does not change the arity
-- fact.
------------------------------------------------------------------------

len : ∀ {n} → List (Tm n) → ℕ
len []       = zero
len (_ ∷ xs) = suc (len xs)

lenS : ∀ {n} {x : Tm n} {xs : List (Tm n)} {k}
  → len (x ∷ xs) ≡ suc k → len xs ≡ k
lenS refl = refl

z≢s : ∀ {n : ℕ} → zero ≡ suc n → ⊥
z≢s ()

s≢z : ∀ {n : ℕ} → suc n ≡ zero → ⊥
s≢z ()

len-snoc : ∀ {n} (xs : List (Tm n)) (x : Tm n) → len (xs ++ x ∷ []) ≡ suc (len xs)
len-snoc []       _ = refl
len-snoc (_ ∷ ys) x = cong suc (len-snoc ys x)

data Sp (B : List ℕ) (i : ℕ) {n} : Tm n → ℕ → Set where
  sp-def : elemℕ i B ≡ true → Sp B i (def i) zero
  sp-app : ∀ {f a k} → hasSelf B a ≡ false → Sp B i f k → Sp B i (app f a) (suc k)

spElem : ∀ {n B i k} {t : Tm n} → Sp B i t k → elemℕ i B ≡ true
spElem (sp-def el) = el
spElem (sp-app _ s) = spElem s

sp-sub : ∀ {n m i k} B (τ : Fin n → Tm m) {t : Tm n}
  → (∀ x → hasSelf B (τ x) ≡ false)
  → Sp B i t k → Sp B i (sub τ t) k
sp-sub _ _ _ (sp-def el) = sp-def el
sp-sub B τ hf (sp-app {a = a} ha s) =
  sp-app (hasSelf-sub B τ a hf ha) (sp-sub B τ hf s)

sp-occ : ∀ {n m i k} B (τ : Fin n → Tm m) {t : Tm n}
  → Sp B i t k
  → (∀ x → occurs x t ≡ true → hasSelf B (τ x) ≡ false)
  → Sp B i (sub τ t) k
sp-occ _ _ (sp-def el) _ = sp-def el
sp-occ B τ (sp-app {f = f} {a = a} ha s) hyp =
  sp-app (hasSelf-sub-occ B τ a ha (λ x oc → hyp x (∨-right {a = occurs x f} oc)))
         (sp-occ B τ s (λ x oc → hyp x (∨-left {b = occurs x a} oc)))

spArgs : ∀ {B i k} {t : Tm 0} → Sp B i t k → List (Tm 0)
spArgs (sp-def _) = []
spArgs (sp-app {a = a} _ s) = spArgs s ++ a ∷ []

spLen-args : ∀ {B i k} {t : Tm 0} (s : Sp B i t k) → len (spArgs s) ≡ k
spLen-args (sp-def _) = refl
spLen-args (sp-app {a = a} _ s) =
  trans (len-snoc (spArgs s) a) (cong suc (spLen-args s))

spFree : ∀ {B i k} {t : Tm 0} (s : Sp B i t k) → AllFree B (spArgs s)
spFree (sp-def _) = af-[]
spFree (sp-app ha s) = allFree-snoc (spFree s) ha

spFold : ∀ {B i k} {t : Tm 0} (s : Sp B i t k) → t ≡ foldApp (def i) (spArgs s)
spFold {i = i} (sp-def _) = refl
spFold {i = i} (sp-app {a = a} _ s) =
  trans (cong (λ z → app z a) (spFold s))
        (sym (foldApp-snoc (def i) (spArgs s) a))

data Nav (B : List ℕ) {n} : Tm n → Set where
  nv-sp  : ∀ {i k t} → Sp B i t k → Nav B t
  nv-unf : ∀ {s q A h t}
    → hasSelf B h ≡ false
    → HeadSeed B h s
    → SeedCovered B h t s
    → Nav B t
    → Nav B (unf s (lam q A (pair h t)))

nav-sub : ∀ {n m} B (τ : Fin n → Tm m) (t : Tm n)
  → (∀ x → hasSelf B (τ x) ≡ false)
  → Nav B t → Nav B (sub τ t)
nav-sub B τ _ hf (nv-sp s) = nv-sp (sp-sub B τ hf s)
nav-sub B τ _ hf (nv-unf {s = s} {h = h} {t = t} hh hs cov n) =
  nv-unf (hasSelf-sub B (lifts τ) h (lifts-hs B τ hf) hh)
         (headseed-sub B τ {h} {s} hf hs)
         (cov-sub B τ h t s hf cov)
         (nav-sub B (lifts τ) t (lifts-hs B τ hf) n)

nav-occ : ∀ {n m} B (τ : Fin n → Tm m) (t : Tm n)
  → Nav B t
  → (∀ x → occurs x t ≡ true → hasSelf B (τ x) ≡ false)
  → Nav B (sub τ t)
nav-occ B τ _ (nv-sp s) hyp = nv-sp (sp-occ B τ s hyp)
nav-occ B τ _ (nv-unf {s = s} {q = q} {A = A} {h = h} {t = t} hh hs cov n) hyp =
  nv-unf (hasSelf-sub-occ B (lifts τ) h hh (unf-h-lifts B τ s q A h t hyp))
         (headseed-occ B τ {h} {s} hs
            (λ x oc → hyp x (∨-left {b = occurs x (lam q A (pair h t))} oc)))
         (cov-occ B τ h t s cov
            (λ x oc → hyp x (∨-left {b = occurs x (lam q A (pair h t))} oc)))
         (nav-occ B (lifts τ) t n (unf-t-lifts B τ s q A h t hyp))

nav-seed : ∀ {n} B {t : Tm (suc n)} {s : Tm n}
  → Nav B t
  → (occurs zero t ≡ true → hasSelf B s ≡ false)
  → Nav B (inst t s)
nav-seed B {t} {s} nv hyp =
  nav-occ B (instσ s) t nv (instσ-occ B {s = s} {t = t} hyp)

-- Leading λs, then one unfold. The tail is a Nav, not a CallShape:
-- pairs and app-of-unfold are already excluded.
data Opened (B : List ℕ) : ∀ {n} → Tm n → Set where
  od-lam : ∀ {n q A} {t : Tm (suc n)} → Opened B t → Opened B (lam q A t)
  od-unf : ∀ {n} {s : Tm n} {q A} {h t : Tm (suc n)}
    → hasSelf B h ≡ false
    → HeadSeed B h s
    → SeedCovered B h t s
    → Nav B t
    → Opened B (unf s (lam q A (pair h t)))

odLams : ∀ {n B} {t : Tm n} → Opened B t → ℕ
odLams (od-lam o) = suc (odLams o)
odLams (od-unf _ _ _ _) = zero

opened-sub : ∀ {n m} B {t : Tm n} (τ : Fin n → Tm m)
  → (∀ x → hasSelf B (τ x) ≡ false)
  → Opened B t → Opened B (sub τ t)
opened-sub B τ hf (od-lam o) =
  od-lam (opened-sub B (lifts τ) (lifts-hs B τ hf) o)
opened-sub B τ hf (od-unf {s = s} {h = h} {t = t} hh hs cov n) =
  od-unf (hasSelf-sub B (lifts τ) h (lifts-hs B τ hf) hh)
         (headseed-sub B τ {h} {s} hf hs)
         (cov-sub B τ h t s hf cov)
         (nav-sub B (lifts τ) t (lifts-hs B τ hf) n)

opened-inst : ∀ {n} B {t : Tm (suc n)} {a : Tm n}
  → Opened B t → hasSelf B a ≡ false → Opened B (inst t a)
opened-inst B {t} {a} o ha = opened-sub B {t} (instσ a) (instσ-free B ha) o

odLams-sub : ∀ {n m B} {t : Tm n} (τ : Fin n → Tm m)
  → (hf : ∀ x → hasSelf B (τ x) ≡ false) (od : Opened B t)
  → odLams (opened-sub B τ hf od) ≡ odLams od
odLams-sub {B = B} τ hf (od-lam o) =
  cong suc (odLams-sub (lifts τ) (lifts-hs B τ hf) o)
odLams-sub _ _ (od-unf _ _ _ _) = refl

odLams-inst : ∀ {n B} {t : Tm (suc n)} {a : Tm n}
  → (od : Opened B t) (ha : hasSelf B a ≡ false)
  → odLams (opened-inst B {t = t} {a = a} od ha) ≡ odLams od
odLams-inst {B = B} {a = a} od ha =
  odLams-sub (instσ a) (instσ-free B ha) od

-- What every block member is, for a family observation: it looks up,
-- it is allowed at this mode, and its body opens as above.
Memb : Sig → Mode → List ℕ → Set
Memb σ m B = ∀ i → elemℕ i B ≡ true → Σ Def λ d →
  lookupDef σ i ≡ ok d × allowedDef (Def.dmode d) m ≡ true ×
  Opened B (Def.dbody d)

-- σ, m and B are explicit. Inferring them from a Memb would ask Agda
-- to see through lookupDef, and that leaves Sig.defs unsolved.
openedOf : (σ : Sig) (m : Mode) (B : List ℕ) (mb : Memb σ m B) (i : ℕ)
  → (el : elemℕ i B ≡ true)
  → Opened B (Def.dbody (proj₁ (mb i el)))
openedOf _ _ _ mb i el = proj₂ (proj₂ (proj₂ (mb i el)))

-- Leading-λ counts, one per block index. The table is a function on
-- ℕ, so the substitution lemmas never open the signature.
Lams : List ℕ → Set
Lams B = ∀ i → elemℕ i B ≡ true → ℕ

lamsOf : (σ : Sig) (m : Mode) (B : List ℕ) (mb : Memb σ m B) → Lams B
lamsOf σ m B mb i el = odLams (openedOf σ m B mb i el)

-- The table is the lam-count of the opened body. Both sides are the
-- same projection, so this is refl and never inspects Sig.defs.
lamsEq : (σ : Sig) (m : Mode) (B : List ℕ) (mb : Memb σ m B) (i : ℕ)
  → (el : elemℕ i B ≡ true)
  → lamsOf σ m B mb i el ≡ odLams (openedOf σ m B mb i el)
lamsEq _ _ _ _ _ _ = refl

odCount : ∀ {n B i k} {t : Tm n} → Lams B → Sp B i t k → ℕ
odCount {i = i} L (sp-def el) = L i el
odCount L (sp-app _ s) = odCount L s

odCount-sub : ∀ {n m B i k} {t : Tm n} {τ : Fin n → Tm m}
  → (L : Lams B) (hf : ∀ x → hasSelf B (τ x) ≡ false) (s : Sp B i t k)
  → odCount L (sp-sub B τ hf s) ≡ odCount L s
odCount-sub _ _ (sp-def _) = refl
odCount-sub L hf (sp-app _ s) = odCount-sub L hf s

odCount-occ : ∀ {n m B i k} {t : Tm n} {τ : Fin n → Tm m}
  → (L : Lams B) (s : Sp B i t k)
  → (hyp : ∀ x → occurs x t ≡ true → hasSelf B (τ x) ≡ false)
  → odCount L (sp-occ B τ s hyp) ≡ odCount L s
odCount-occ _ (sp-def _) _ = refl
odCount-occ L (sp-app {a = a} _ s) hyp =
  odCount-occ L s (λ x oc → hyp x (∨-left {b = occurs x a} oc))

odCount-at : ∀ {n B i k} {t : Tm n} (L : Lams B) (s : Sp B i t k)
  → odCount L s ≡ L i (spElem s)
odCount-at _ (sp-def _) = refl
odCount-at L (sp-app _ s) = odCount-at L s

fitsNav : ∀ {n B} {t : Tm n} → Lams B → Nav B t → Set
fitsNav L (nv-sp {k = k} s) = k ≡ odCount L s
fitsNav L (nv-unf _ _ _ n) = fitsNav L n

fitsOd : ∀ {n B} {t : Tm n} → Lams B → Opened B t → Set
fitsOd L (od-lam o) = fitsOd L o
fitsOd L (od-unf _ _ _ n) = fitsNav L n

fits-nav-sub : ∀ {n m B} {t : Tm n} (L : Lams B)
  → (τ : Fin n → Tm m) (hf : ∀ x → hasSelf B (τ x) ≡ false)
  → (nv : Nav B t) → fitsNav L nv → fitsNav L (nav-sub B τ t hf nv)
fits-nav-sub {B = B} L τ hf (nv-sp s) fit = trans fit (sym (odCount-sub L hf s))
fits-nav-sub {B = B} L τ hf (nv-unf _ _ _ n) fit =
  fits-nav-sub (lifts-table B τ hf L) (lifts τ) (lifts-hs B τ hf) n fit
  where
  -- The tail is under one binder. Its block indices are the same
  -- numbers, so the same table is the table at the next level.
  lifts-table : ∀ {n m} B (τ : Fin n → Tm m)
    → (∀ x → hasSelf B (τ x) ≡ false) → Lams B → Lams B
  lifts-table _ _ _ L′ = L′

fits-nav-occ : ∀ {n m B} {t : Tm n} (L : Lams B)
  → (τ : Fin n → Tm m) (nv : Nav B t)
  → (hyp : ∀ x → occurs x t ≡ true → hasSelf B (τ x) ≡ false)
  → fitsNav L nv → fitsNav L (nav-occ B τ t nv hyp)
fits-nav-occ {B = B} L τ (nv-sp s) hyp fit = trans fit (sym (odCount-occ L s hyp))
fits-nav-occ {B = B} L τ (nv-unf {s = s} {q = q} {A = A} {h = h} {t = t} _ _ _ n) hyp fit =
  fits-nav-occ L (lifts τ) n (unf-t-lifts B τ s q A h t hyp) fit

fits-nav-seed : ∀ {n B} {t : Tm (suc n)} {s : Tm n}
  → (L : Lams B) (nv : Nav B t)
  → (hyp : occurs zero t ≡ true → hasSelf B s ≡ false)
  → fitsNav L nv → fitsNav L (nav-seed B {t = t} {s = s} nv hyp)
fits-nav-seed {B = B} {t = t} {s = s} L nv hyp fit =
  fits-nav-occ L (instσ s) nv (instσ-occ B {s = s} {t = t} hyp) fit

fits-opened-sub : ∀ {n m B} {t : Tm n} (L : Lams B)
  → (τ : Fin n → Tm m) (hf : ∀ x → hasSelf B (τ x) ≡ false)
  → (od : Opened B t) → fitsOd L od → fitsOd L (opened-sub B τ hf od)
fits-opened-sub {B = B} L τ hf (od-lam o) fit =
  fits-opened-sub L (lifts τ) (lifts-hs B τ hf) o fit
fits-opened-sub {B = B} L τ hf (od-unf _ _ _ n) fit =
  fits-nav-sub L (lifts τ) (lifts-hs B τ hf) n fit

fits-opened-inst : ∀ {n B} {t : Tm (suc n)} {a : Tm n}
  → (L : Lams B) (od : Opened B t) (ha : hasSelf B a ≡ false)
  → fitsOd L od → fitsOd L (opened-inst B {t = t} {a = a} od ha)
fits-opened-inst {B = B} {a = a} L od ha fit =
  fits-opened-sub L (instσ a) (instσ-free B ha) od fit

-- The opened spine, as fields. Projecting them does not reduce the
-- signature: the arity table is a Lams, and the body is already an
-- Opened argument.
record OpenOut {B : List ℕ} (L : Lams B) (t : Tm 0) (as : List (Tm 0))
               (od : Opened B t) : Set where
  constructor mkOpen
  field
    seed   : Tm 0
    qty    : Qty
    dom    : Tm 0
    hd     : Tm 1
    tl     : Tm 1
    opened : Open B t as (unf seed (lam qty dom (pair hd tl)))
    hh     : hasSelf B hd ≡ false
    hs     : HeadSeed B hd seed
    cov    : SeedCovered B hd tl seed
    nav    : Nav B tl
    pres   : fitsOd L od → fitsNav L nav

-- Peel exactly the leading λs. A short or a long spine is the absurd
-- length equality. The recursive call is on the leftover arguments.
openExact : ∀ {B} (L : Lams B) {t : Tm 0} {as : List (Tm 0)}
  → (od : Opened B t) → AllFree B as → len as ≡ odLams od → OpenOut L t as od
openExact L (od-unf {s = s} {q = q} {A = A} {h = h} {t = tl} hh hs cov nv) af-[] _ =
  mkOpen s q A h tl op-[] hh hs cov nv (λ fit → fit)
openExact _ (od-unf _ _ _ _) (af-∷ _ _) eq = ⊥-elim (s≢z eq)
openExact _ (od-lam _) af-[] eq = ⊥-elim (z≢s eq)
openExact {B = B} L (od-lam {q = q} {A = A} {t = t} o) (af-∷ {a = a} {as = xs} ha rest) eq =
  peel (openExact L (opened-inst B {t = t} {a = a} o ha) rest
          (trans (lenS {x = a} {xs = xs} {k = odLams o} eq)
                 (sym (odLams-inst {B = B} {t = t} {a = a} o ha))))
  where
  peel : OpenOut L (inst t a) xs (opened-inst B {t = t} {a = a} o ha)
       → OpenOut L (lam q A t) (a ∷ xs) (od-lam o)
  peel got =
    mkOpen (OpenOut.seed got) (OpenOut.qty got) (OpenOut.dom got)
           (OpenOut.hd got) (OpenOut.tl got)
           (op-∷ ha (OpenOut.opened got))
           (OpenOut.hh got) (OpenOut.hs got) (OpenOut.cov got) (OpenOut.nav got)
           (λ fit → OpenOut.pres got (fits-opened-inst L o ha fit))

-- One family step. BlockClosed is not an argument here: obs-fam takes
-- it, and this step does not use it. reaches stays fuel-bounded.
record Step (σ : Sig) (m : Mode) (B : List ℕ) (L : Lams B) (t : Tm 0) : Set where
  constructor mkStep
  field
    hd  : Tm 0
    tl  : Tm 0
    rd  : Reads σ m true t hd tl
    hf  : hasSelf B hd ≡ false
    nxt : Nav B tl
    nft : fitsNav L nxt

rd-spine : ∀ {σ m B i as s q A h tl dfn}
  → lookupDef σ i ≡ ok dfn
  → allowedDef (Def.dmode dfn) m ≡ true
  → Open B (Def.dbody dfn) as (unf s (lam q A (pair h tl)))
  → (t : Tm 0) → t ≡ foldApp (def i) as
  → Reads σ m true t (inst h s) (inst tl s)
rd-spine {σ} {m} {B} {i} {as} {s} {q} {A} {h} {tl} {dfn} lk al op t eq =
  subst (λ z → Reads σ m true z (inst h s) (inst tl s)) (sym eq)
    (rd-fam (spine-star {σ} {m} {B = B} {i = i} {as = as}
              {r = unf s (lam q A (pair h tl))} {dfn = dfn} lk al op))

-- A navigation, classified without a signature in scope. The spine
-- case carries the arity fact and nothing from lookupDef; the caller
-- supplies the definition afterwards. Matching here therefore cannot
-- leave Sig.defs unsolved.
data Which (σ : Sig) (m : Mode) (B : List ℕ) (L : Lams B) (t : Tm 0) : Set where
  wh-unf : Step σ m B L t → Which σ m B L t
  wh-sp  : ∀ {i k} (s : Sp B i t k) → k ≡ odCount L s → Which σ m B L t

classify : (σ : Sig) (m : Mode) (B : List ℕ) (L : Lams B) {t : Tm 0}
  → (nv : Nav B t) → fitsNav L nv → Which σ m B L t
classify σ m B L
    (nv-unf {s = s} {q = q} {A = A} {h = h} {t = tl} hh hs cov n) fit =
  wh-unf
    (mkStep (inst h s) (inst tl s)
      (rd-fam (⇛*-refl {t = unf s (lam q A (pair h tl))}))
      (head-inst B {h = h} {s = s} hh hs)
      (nav-seed B {t = tl} {s = s} n
        (tail-from-cover B {h = h} {t = tl} {s = s} hs cov))
      (fits-nav-seed L n
        (tail-from-cover B {h = h} {t = tl} {s = s} hs cov) fit))
classify _ _ _ _ (nv-sp s) fit = wh-sp s fit

elimWhich : ∀ {σ m B} {L : Lams B}
  → (P : ∀ {t} → Which σ m B L t → Set)
  → (∀ {t} (st : Step σ m B L t) → P (wh-unf st))
  → (∀ {i k t} (s : Sp B i t k) (fit : k ≡ odCount L s) → P (wh-sp s fit))
  → ∀ {t} (w : Which σ m B L t) → P w
elimWhich _ onU _ (wh-unf st) = onU st
elimWhich _ _ onS (wh-sp s fit) = onS s fit

-- Open the definition a spine names. The lookup, the body and the
-- arity proof are arguments, already projected by the caller.
useSp : (σ : Sig) (m : Mode) (B : List ℕ) (L : Lams B)
  → ∀ {i k} {t : Tm 0} (s : Sp B i t k)
  → k ≡ odCount L s
  → (dfn : Def)
  → lookupDef σ i ≡ ok dfn
  → allowedDef (Def.dmode dfn) m ≡ true
  → (od : Opened B (Def.dbody dfn))
  → fitsOd L od
  → L i (spElem s) ≡ odLams od
  → Step σ m B L t
useSp σ m B L {i = i} {t = t} s fit dfn lk al od gd ar =
  let eq = trans (trans (spLen-args s) fit) (trans (odCount-at L s) ar)
      got = openExact L od (spFree s) eq
      sd = OpenOut.seed got
      hd′ = OpenOut.hd got
      tl′ = OpenOut.tl got
      hyp = tail-from-cover B {h = hd′} {t = tl′} {s = sd}
              (OpenOut.hs got) (OpenOut.cov got)
  in mkStep (inst hd′ sd) (inst tl′ sd)
       (rd-spine {σ} {m} {B} {i} {as = spArgs s} {s = sd}
          {q = OpenOut.qty got} {A = OpenOut.dom got} {h = hd′} {tl = tl′}
          {dfn = dfn} lk al (OpenOut.opened got) t (spFold s))
       (head-inst B {h = hd′} {s = sd} (OpenOut.hh got) (OpenOut.hs got))
       (nav-seed B {t = tl′} {s = sd} (OpenOut.nav got) hyp)
       (fits-nav-seed L (OpenOut.nav got) hyp (OpenOut.pres got gd))

-- One family step. The Nav match is classify, which has no Memb.
-- This function only dispatches on the result, through elimWhich.
oneStep : (σ : Sig) (m : Mode) (B : List ℕ) (mb : Memb σ m B)
  → (∀ i → (el : elemℕ i B ≡ true)
       → fitsOd (lamsOf σ m B mb) (openedOf σ m B mb i el))
  → ∀ {t : Tm 0} (nv : Nav B t) → fitsNav (lamsOf σ m B mb) nv
  → Step σ m B (lamsOf σ m B mb) t
oneStep σ m B mb good nv fit =
  elimWhich (λ {t′} _ → Step σ m B (lamsOf σ m B mb) t′)
    (λ st → st)
    (λ {i = i} s fit′ →
       let el = spElem s
           pack = mb i el
       in useSp σ m B (lamsOf σ m B mb) s fit′
            (proj₁ pack)
            (proj₁ (proj₂ pack))
            (proj₁ (proj₂ (proj₂ pack)))
            (openedOf σ m B mb i el)
            (good i el)
            (lamsEq σ m B mb i el))
    (classify σ m B (lamsOf σ m B mb) nv fit)

-- Theorem B, family reading (fam = true).
-- Hypotheses, in order:
--   BlockClosed σ B. Not used to build the observation. reaches is
--   bounded by suc (length of the definitions); Stage 4 does not
--   discharge it. The argument is kept so the hypothesis is visible.
--   mb: every i ∈ B looks up, is allowed at mode m, and its body is
--   leading λs then one unfold whose tail is a Nav.
--   good: every such body has the target's arity (fitsOd of lamsOf).
--   nv, fit: the subject is such a Nav, and its spines match too.
--   SeedCovered and HeadSeed sit on each unfold inside the Nav and
--   the Opened bodies. SeedCovered's third disjunct is a block-free
--   seed, including one only the tail reads. A block-mentioning seed
--   only the tail reads is refused, so it is not an accepted Nav.
--   Stream call tails are obs-stream's excluded case, not this one.
obs-fam : (σ : Sig) (m : Mode) (B : List ℕ)
  → BlockClosed σ B
  → (mb : Memb σ m B)
  → (∀ i → (el : elemℕ i B ≡ true)
       → fitsOd (lamsOf σ m B mb) (openedOf σ m B mb i el))
  → ∀ {t : Tm 0} (nv : Nav B t)
  → fitsNav (lamsOf σ m B mb) nv
  → ∀ d → Obs σ m B true d t
obs-fam σ m B _ mb good nv fit zero =
  let st = oneStep σ m B mb good nv fit
  in Step.hd st , Step.tl st , Step.rd st , Step.hf st
obs-fam σ m B cl mb good nv fit (suc d) =
  let st = oneStep σ m B mb good nv fit
  in Step.hd st , Step.tl st , Step.rd st , Step.hf st ,
     obs-fam σ m B cl mb good (Step.nxt st) (Step.nft st) d

-- One family observation, with no claim about the tail. This is the
-- gt-absent case: the head is block-free, and the chain stops.
obs-unf-one : ∀ {σ m B q} {A s : Tm 0} {h t : Tm 1}
  → hasSelf B h ≡ false → HeadSeed B h s
  → Obs σ m B true zero (unf s (lam q A (pair h t)))
obs-unf-one {σ} {m} {B} {q} {A} {s} {h} {t} hh hs =
  inst h s , inst t s ,
  rd-fam (⇛*-refl {t = unf s (lam q A (pair h t))}) ,
  head-inst B {h = h} {s = s} hh hs

------------------------------------------------------------------------
-- Acceptance extracts the productivity check. checkSig-nu is the
-- productivity tag of checkDef. checkSig-guarded, below, reads every
-- syntactic unfold in that body off seedWalk: StepGuard after whnf,
-- and the seed boolean that is HeadSeed and SeedCovered on a one-λ
-- pair. That is the walk the checker runs, not a mirror of check′.
------------------------------------------------------------------------

>>-ok : ∀ {A B : Set} {r : Result A} {r′ : Result B} {x}
  → (r >> r′) ≡ ok x → (∃ λ y → r ≡ ok y) × (r′ ≡ ok x)
>>-ok {r = ok y} eq = (y , refl) , eq

ok-tt : ∀ {r : Result ⊤} {y} → r ≡ ok y → r ≡ ok tt
ok-tt {y = tt} eq = eq

+0 : ∀ j → j + 0 ≡ j
+0 zero    = refl
+0 (suc j) = cong suc (+0 j)

+s : ∀ j i → j + suc i ≡ suc (j + i)
+s zero    i = refl
+s (suc j) i = cong suc (+s j i)

-- checkDefs walks the definition list from index j. A hit at offset i
-- is checkDef at j + i.
checkDefs-at : (k : ℕ) (σ : Sig) (j : ℕ) (ds : List Def)
  → checkDefs k σ j ds ≡ ok tt
  → (i : ℕ) {d : Def} → lookupList ds i ≡ ok d
  → checkDef k σ (j + i) ≡ ok tt
checkDefs-at _ _ _ [] eq i leq = ⊥-elim (fail≢ok leq)
checkDefs-at k σ j (_ ∷ ds) eq zero _ =
  subst (λ z → checkDef k σ z ≡ ok tt) (sym (+0 j))
    (ok-tt (proj₂ (proj₁ (>>-ok {r = checkDef k σ j} eq))))
checkDefs-at k σ j (_ ∷ ds) eq (suc i) leq =
  subst (λ z → checkDef k σ z ≡ ok tt) (sym (+s j i))
    (checkDefs-at k σ (suc j) ds (proj₂ (>>-ok {r = checkDef k σ j} eq)) i leq)

-- checkDef is lookup, then the type tag, the body tag, the productivity
-- tag, and ok. Written out so substituting ok d for the lookup reduces
-- the bind. A with on lookupDef leaves that bind stuck.
checkDef-open : ∀ k σ i →
  checkDef k σ i ≡
  (lookupDef σ i >>= λ d →
    tag (Def.dname d ++s " type")
      (checkTy k σ emptyRec Vec.[] (Def.dtype d) >>
       runDecl k σ (Def.dmode d) (Def.dtype d)) >>
    tag (Def.dname d ++s " body") (checkBody k σ i d) >>
    tag (Def.dname d ++s " productivity")
      (checkNu k σ (component σ i) (Def.dmode d) (Def.dtype d) (Def.dbody d)) >>
    ok tt)
checkDef-open _ _ _ = refl

checkDef-nu : (k : ℕ) (σ : Sig) (i : ℕ) {d : Def}
  → lookupDef σ i ≡ ok d
  → checkDef k σ i ≡ ok tt
  → checkNu k σ (component σ i) (Def.dmode d) (Def.dtype d) (Def.dbody d) ≡ ok tt
checkDef-nu k σ i {d} leq eq =
  takeNu (subst opened leq (subst (λ z → z ≡ ok tt) (sym (checkDef-open k σ i)) eq))
  where
  opened : Result Def → Set
  opened r =
    (r >>= λ d′ →
      tag (Def.dname d′ ++s " type")
        (checkTy k σ emptyRec Vec.[] (Def.dtype d′) >>
         runDecl k σ (Def.dmode d′) (Def.dtype d′)) >>
      tag (Def.dname d′ ++s " body") (checkBody k σ i d′) >>
      tag (Def.dname d′ ++s " productivity")
        (checkNu k σ (component σ i) (Def.dmode d′) (Def.dtype d′) (Def.dbody d′)) >>
      ok tt) ≡ ok tt
  Ty = tag (Def.dname d ++s " type")
         (checkTy k σ emptyRec Vec.[] (Def.dtype d) >>
          runDecl k σ (Def.dmode d) (Def.dtype d))
  Bd = tag (Def.dname d ++s " body") (checkBody k σ i d)
  Nu = tag (Def.dname d ++s " productivity")
         (checkNu k σ (component σ i) (Def.dmode d) (Def.dtype d) (Def.dbody d))

  -- tag does not reduce until its result is ok or fail, so >>-ok cannot
  -- split this chain. Each with matches the result, and `in` keeps the
  -- equality to the term that was split.
  takeNu : opened (ok d)
         → checkNu k σ (component σ i) (Def.dmode d) (Def.dtype d) (Def.dbody d) ≡ ok tt
  takeNu eq′ = peelNu (peelMid (peelOuter eq′))
    where
    peelOuter : ((((Ty >> Bd) >> Nu) >> ok tt) ≡ ok tt) → (((Ty >> Bd) >> Nu) ≡ ok tt)
    peelOuter eq with (Ty >> Bd) >> Nu
    ... | fail _ = ⊥-elim (fail≢ok eq)
    ... | ok tt  = refl

    peelMid : (((Ty >> Bd) >> Nu) ≡ ok tt) → (Nu ≡ ok tt)
    peelMid eq with Ty >> Bd
    ... | fail _ = ⊥-elim (fail≢ok eq)
    ... | ok _   = eq

    peelNu : (Nu ≡ ok tt)
           → checkNu k σ (component σ i) (Def.dmode d) (Def.dtype d) (Def.dbody d) ≡ ok tt
    peelNu eq with checkNu k σ (component σ i) (Def.dmode d) (Def.dtype d) (Def.dbody d)
    ... | fail _ = ⊥-elim (fail≢ok eq)
    ... | ok tt  = refl

-- The mode is not spec, as the issue states it. checkNu of spec is
-- ok immediately, so the equality does not use the inequality.
checkSig-nu : (k : ℕ) (σ : Sig) (i : ℕ) {d : Def}
  → checkSig k σ ≡ ok tt
  → lookupDef σ i ≡ ok d
  → (Def.dmode d ≡ spec → ⊥)
  → checkNu k σ (component σ i) (Def.dmode d) (Def.dtype d) (Def.dbody d) ≡ ok tt
checkSig-nu k σ i eq leq _ =
  checkDef-nu k σ i leq
    (checkDefs-at k σ 0 (Sig.defs σ)
       (proj₂ (>>-ok {r = checkDatas k σ} eq)) i leq)

------------------------------------------------------------------------
-- seedWalk establishes the guard and the seed fact of every syntactic
-- unfold. The recursion is the walk's, on the term.
------------------------------------------------------------------------

-- >> reduces to >>=, and `with` rewrites the result type, so copy the
-- left result and match the copy. A chain of more than one >> is
-- left-nested: the caller passes that whole left result as r.
-- Inferring r takes the innermost bind.
split>> : {r r′ : Result ⊤} → (r >> r′) ≡ ok tt → r ≡ ok tt × r′ ≡ ok tt
split>> {r = r} {r′ = r′} eq = go r refl eq
  where
  go : (r0 : Result ⊤) → r ≡ r0 → ((r >> r′) ≡ ok tt) → r ≡ ok tt × r′ ≡ ok tt
  go (fail _) er eq′ = ⊥-elim (fail≢ok (subst (λ z → ((z >> r′) ≡ ok tt)) er eq′))
  go (ok tt) er eq′ = er , subst (λ z → ((z >> r′) ≡ ok tt)) er eq′

-- What seedWalk records at each unfold, and passes down every subterm
-- the walk enters. A leaf the walk accepts in one step holds ⊤.
AllUnf : ∀ {n} → ℕ → Sig → List ℕ → Tm n → Set
AllUnfList : ∀ {n} → ℕ → Sig → List ℕ → List (Tm n) → Set

AllUnf {n} k σ B (unf s f) =
  Σ (Tm n) λ f′ →
    whnf k σ f ≡ ok f′
    × StepGuard B f′
    × ((seedFlows nothing f′ ∧ hasSelf B s) ≡ false)
    × AllUnf k σ B s
    × AllUnf k σ B f
AllUnf k σ B (app f a) = AllUnf k σ B f × AllUnf k σ B a
AllUnf k σ B (su t) = AllUnf k σ B t
AllUnf k σ B (lam _ A t) = AllUnf k σ B A × AllUnf k σ B t
AllUnf k σ B (pi _ A C) = AllUnf k σ B A × AllUnf k σ B C
AllUnf k σ B (mData e P bs) = AllUnf k σ B e × AllUnf k σ B P × AllUnfList k σ B bs
AllUnf k σ B (mNat e P z s) =
  AllUnf k σ B e × AllUnf k σ B P × AllUnf k σ B z × AllUnf k σ B s
AllUnf k σ B (mEmp e P) = AllUnf k σ B e × AllUnf k σ B P
AllUnf k σ B (mUnit e P u) = AllUnf k σ B e × AllUnf k σ B P × AllUnf k σ B u
AllUnf k σ B (idt A a b) = AllUnf k σ B A × AllUnf k σ B a × AllUnf k σ B b
AllUnf k σ B (rwt e P t) = AllUnf k σ B e × AllUnf k σ B P × AllUnf k σ B t
AllUnf k σ B (ann e A) = AllUnf k σ B e × AllUnf k σ B A
AllUnf k σ B (prod A C) = AllUnf k σ B A × AllUnf k σ B C
AllUnf k σ B (pair a b) = AllUnf k σ B a × AllUnf k σ B b
AllUnf k σ B (letp e t) = AllUnf k σ B e × AllUnf k σ B t
AllUnf k σ B (nu F) = AllUnf k σ B F
AllUnf k σ B (ucons u) = AllUnf k σ B u
AllUnf k σ B (tensor d u) = AllUnf k σ B d × AllUnf k σ B u
AllUnf k σ B (addi x y) = AllUnf k σ B x × AllUnf k σ B y
AllUnf k σ B (muli x y) = AllUnf k σ B x × AllUnf k σ B y
AllUnf k σ B (addt x y) = AllUnf k σ B x × AllUnf k σ B y
AllUnf k σ B (toi64 t) = AllUnf k σ B t
AllUnf k σ B (packi x y) = AllUnf k σ B x × AllUnf k σ B y
AllUnf _ _ _ (var _) = ⊤
AllUnf _ _ _ typ = ⊤
AllUnf _ _ _ nat = ⊤
AllUnf _ _ _ ze = ⊤
AllUnf _ _ _ unit = ⊤
AllUnf _ _ _ one = ⊤
AllUnf _ _ _ empty = ⊤
AllUnf _ _ _ (dty _) = ⊤
AllUnf _ _ _ (ctor _ _) = ⊤
AllUnf _ _ _ rfl = ⊤
AllUnf _ _ _ (def _) = ⊤
AllUnf _ _ _ i64 = ⊤
AllUnf _ _ _ f32ty = ⊤

AllUnfList _ _ _ [] = ⊤
AllUnfList k σ B (t ∷ ts) = AllUnf k σ B t × AllUnfList k σ B ts

-- whnf and the seed guard are the same call seedGuard makes. One with
-- rewrites both results.
takeUnf : ∀ {n} k σ (B : List ℕ) (s f : Tm n)
  → seedGuard k σ B s f ≡ ok tt
  → (whnf k σ f >>= guardedStep B) ≡ ok tt
  → Σ (Tm n) λ f′ →
      whnf k σ f ≡ ok f′ × StepGuard B f′
      × ((seedFlows nothing f′ ∧ hasSelf B s) ≡ false)
takeUnf k σ B s f seq geq with whnf k σ f
... | fail _ = ⊥-elim (fail≢ok geq)
... | ok f′ =
  f′ , refl , guardedStep-ok B f′ geq ,
  unguarded-ok (seedFlows nothing f′ ∧ hasSelf B s) seq

mutual
  seedWalk-all : ∀ {n} k σ B (t : Tm n) → seedWalk k σ B t ≡ ok tt → AllUnf k σ B t
  -- seedGuard reduces to whnf, a Result (Tm _), so the chain cannot be
  -- split by unifying with >> of two Result ⊤. Open the clause and
  -- case on each result, as checkDef-nu does for tags.
  seedWalk-all k σ B (unf s f) eq =
    fromOpen (subst (λ z → z ≡ ok tt) unf-open eq)
    where
    unf-open : seedWalk k σ B (unf s f) ≡
        (((seedGuard k σ B s f >> (whnf k σ f >>= guardedStep B))
           >> seedWalk k σ B s) >> seedWalk k σ B f)
    unf-open = refl
    SG = seedGuard k σ B s f
    GS = whnf k σ f >>= guardedStep B
    WS = seedWalk k σ B s
    WF = seedWalk k σ B f
    fromOpen : (((SG >> GS) >> WS) >> WF) ≡ ok tt → AllUnf k σ B (unf s f)
    fromOpen eq with (SG >> GS) >> WS in eWS
    ... | fail _ = ⊥-elim (fail≢ok eq)
    ... | ok tt with SG >> GS in eGS
    ... | fail _ = ⊥-elim (fail≢ok eWS)
    ... | ok tt with SG in eSG
    ... | fail _ = ⊥-elim (fail≢ok eGS)
    ... | ok tt =
      let f′ , weq , sg , bit = takeUnf k σ B s f eSG eGS
      in f′ , weq , sg , bit , seedWalk-all k σ B s eWS , seedWalk-all k σ B f eq
  seedWalk-all k σ B (app f a) eq =
    let ef , ea = split>> eq in seedWalk-all k σ B f ef , seedWalk-all k σ B a ea
  seedWalk-all k σ B (su t) eq = seedWalk-all k σ B t eq
  seedWalk-all k σ B (lam _ A t) eq =
    let eA , et = split>> eq in seedWalk-all k σ B A eA , seedWalk-all k σ B t et
  seedWalk-all k σ B (pi _ A C) eq =
    let eA , eC = split>> eq in seedWalk-all k σ B A eA , seedWalk-all k σ B C eC
  seedWalk-all k σ B (mData e P bs) eq =
    let eep , ebs = split>> {r = seedWalk k σ B e >> seedWalk k σ B P} eq
        ee , eP = split>> {r = seedWalk k σ B e} eep
    in seedWalk-all k σ B e ee , seedWalk-all k σ B P eP , seedWalkList-all k σ B bs ebs
  seedWalk-all k σ B (mNat e P z s) eq =
    let e3 , es = split>> {r = (seedWalk k σ B e >> seedWalk k σ B P) >> seedWalk k σ B z} eq
        eep , ez = split>> {r = seedWalk k σ B e >> seedWalk k σ B P} e3
        ee , eP = split>> {r = seedWalk k σ B e} eep
    in seedWalk-all k σ B e ee , seedWalk-all k σ B P eP
     , seedWalk-all k σ B z ez , seedWalk-all k σ B s es
  seedWalk-all k σ B (mEmp e P) eq =
    let ee , eP = split>> eq in seedWalk-all k σ B e ee , seedWalk-all k σ B P eP
  seedWalk-all k σ B (mUnit e P u) eq =
    let eep , eu = split>> {r = seedWalk k σ B e >> seedWalk k σ B P} eq
        ee , eP = split>> {r = seedWalk k σ B e} eep
    in seedWalk-all k σ B e ee , seedWalk-all k σ B P eP , seedWalk-all k σ B u eu
  seedWalk-all k σ B (idt A a b) eq =
    let eAa , eb = split>> {r = seedWalk k σ B A >> seedWalk k σ B a} eq
        eA , ea = split>> {r = seedWalk k σ B A} eAa
    in seedWalk-all k σ B A eA , seedWalk-all k σ B a ea , seedWalk-all k σ B b eb
  seedWalk-all k σ B (rwt e P t) eq =
    let eep , et = split>> {r = seedWalk k σ B e >> seedWalk k σ B P} eq
        ee , eP = split>> {r = seedWalk k σ B e} eep
    in seedWalk-all k σ B e ee , seedWalk-all k σ B P eP , seedWalk-all k σ B t et
  seedWalk-all k σ B (ann e A) eq =
    let ee , eA = split>> eq in seedWalk-all k σ B e ee , seedWalk-all k σ B A eA
  seedWalk-all k σ B (prod A C) eq =
    let eA , eC = split>> eq in seedWalk-all k σ B A eA , seedWalk-all k σ B C eC
  seedWalk-all k σ B (pair a b) eq =
    let ea , eb = split>> eq in seedWalk-all k σ B a ea , seedWalk-all k σ B b eb
  seedWalk-all k σ B (letp e t) eq =
    let ee , et = split>> eq in seedWalk-all k σ B e ee , seedWalk-all k σ B t et
  seedWalk-all k σ B (nu F) eq = seedWalk-all k σ B F eq
  seedWalk-all k σ B (ucons u) eq = seedWalk-all k σ B u eq
  seedWalk-all k σ B (tensor d u) eq =
    let ed , eu = split>> eq in seedWalk-all k σ B d ed , seedWalk-all k σ B u eu
  seedWalk-all k σ B (addi x y) eq =
    let ex , ey = split>> eq in seedWalk-all k σ B x ex , seedWalk-all k σ B y ey
  seedWalk-all k σ B (muli x y) eq =
    let ex , ey = split>> eq in seedWalk-all k σ B x ex , seedWalk-all k σ B y ey
  seedWalk-all k σ B (addt x y) eq =
    let ex , ey = split>> eq in seedWalk-all k σ B x ex , seedWalk-all k σ B y ey
  seedWalk-all k σ B (toi64 t) eq = seedWalk-all k σ B t eq
  seedWalk-all k σ B (packi x y) eq =
    let ex , ey = split>> eq in seedWalk-all k σ B x ex , seedWalk-all k σ B y ey
  seedWalk-all _ _ _ (var _) _ = tt
  seedWalk-all _ _ _ typ _ = tt
  seedWalk-all _ _ _ nat _ = tt
  seedWalk-all _ _ _ ze _ = tt
  seedWalk-all _ _ _ unit _ = tt
  seedWalk-all _ _ _ one _ = tt
  seedWalk-all _ _ _ empty _ = tt
  seedWalk-all _ _ _ (dty _) _ = tt
  seedWalk-all _ _ _ (ctor _ _) _ = tt
  seedWalk-all _ _ _ rfl _ = tt
  seedWalk-all _ _ _ (def _) _ = tt
  seedWalk-all _ _ _ i64 _ = tt
  seedWalk-all _ _ _ f32ty _ = tt

  seedWalkList-all : ∀ {n} k σ B (ts : List (Tm n))
    → seedWalkList k σ B ts ≡ ok tt → AllUnfList k σ B ts
  seedWalkList-all _ _ _ [] _ = tt
  seedWalkList-all k σ B (t ∷ ts) eq =
    let et , ets = split>> eq
    in seedWalk-all k σ B t et , seedWalkList-all k σ B ts ets

-- checkNu of a run or evidence body runs seedWalk before anything else.
nu-seeds : ∀ {n} k σ B m (T t : Tm n)
  → checkNu k σ B m T t ≡ ok tt
  → (m ≡ spec → ⊥)
  → AllUnf k σ B t
nu-seeds _ _ _ spec _ _ _ no = ⊥-elim (no refl)
nu-seeds zero _ _ run _ _ eq _ = ⊥-elim (fail≢ok eq)
nu-seeds zero _ _ evid _ _ eq _ = ⊥-elim (fail≢ok eq)
nu-seeds (suc k) σ B run T t eq _ = seedWalk-all (suc k) σ B t (walk-of eq)
  where
  -- checkNu is (seedWalk >> whnf) >>= go. The whnf result is a term,
  -- so this is not a >> of two Result ⊤. The walk is the left result.
  walk-of : checkNu (suc k) σ B run T t ≡ ok tt → seedWalk (suc k) σ B t ≡ ok tt
  walk-of eq with seedWalk (suc k) σ B t
  ... | fail _ = ⊥-elim (fail≢ok eq)
  ... | ok tt = refl
nu-seeds (suc k) σ B evid T t eq _ = seedWalk-all (suc k) σ B t (walk-of eq)
  where
  walk-of : checkNu (suc k) σ B evid T t ≡ ok tt → seedWalk (suc k) σ B t ≡ ok tt
  walk-of eq with seedWalk (suc k) σ B t
  ... | fail _ = ⊥-elim (fail≢ok eq)
  ... | ok tt = refl

-- Every syntactic unfold in an accepted run or evidence body has the
-- guard and the seed fact. Spec is skipped by checkNu, as checkUnfold is.
checkSig-guarded : (k : ℕ) (σ : Sig) (i : ℕ) {d : Def}
  → checkSig k σ ≡ ok tt
  → lookupDef σ i ≡ ok d
  → (Def.dmode d ≡ spec → ⊥)
  → AllUnf k σ (component σ i) (Def.dbody d)
checkSig-guarded k σ i {d} eq leq ns =
  nu-seeds k σ (component σ i) (Def.dmode d) (Def.dtype d) (Def.dbody d)
    (checkSig-nu k σ i eq leq ns) ns

-- The body of a λ. natsFrom is a λ whose body is the unfold.
lam-body : ∀ {n} {k : ℕ} {σ : Sig} {B : List ℕ} {q : Qty} {A : Tm n} {t : Tm (suc n)}
  → AllUnf k σ B (lam q A t) → AllUnf k σ B t
lam-body (_ , u) = u

-- A one-λ pair. seedFlows is the head occurrence or the tail occurrence.
-- hasSelf false is SeedCovered's third disjunct, so a block-free seed
-- the tail reads is covered. Both occurrences false is the first.
lamPairFacts : ∀ {n} B {s : Tm n} {h t : Tm (suc n)}
  → (occℕ 0 h ∨ occℕ 0 t) ∧ hasSelf B s ≡ false
  → HeadSeed B h s × SeedCovered B h t s
lamPairFacts {n} B {s} {h} {t} eq = go (onT (onH eq))
  where
  -- Case on `occurs`, which is what HeadSeed and SeedCovered say.
  -- `with` on occℕ does not rewrite occℕ (toℕ zero).
  onH : (occℕ 0 h ∨ occℕ 0 t) ∧ hasSelf B s ≡ false
      → (occurs zero h ∨ occℕ 0 t) ∧ hasSelf B s ≡ false
  onH = subst (λ x → ((x ∨ occℕ 0 t) ∧ hasSelf B s ≡ false)) (occℕ-occurs zero h)
  onT : (occurs zero h ∨ occℕ 0 t) ∧ hasSelf B s ≡ false
      → (occurs zero h ∨ occurs zero t) ∧ hasSelf B s ≡ false
  onT = subst (λ y → ((occurs zero h ∨ y) ∧ hasSelf B s ≡ false)) (occℕ-occurs zero t)
  go : (occurs zero h ∨ occurs zero t) ∧ hasSelf B s ≡ false
     → HeadSeed B h s × SeedCovered B h t s
  go eq with occurs zero h | occurs zero t | hasSelf B s
  ... | false | false | false = (λ _ → refl) , inj₁ refl
  ... | false | false | true  = (λ oc → ⊥-elim (true≢false (sym oc))) , inj₁ refl
  ... | false | true  | false = (λ _ → refl) , inj₂ (inj₂ refl)
  ... | false | true  | true  = ⊥-elim (true≢false eq)
  ... | true  | false | false = (λ _ → refl) , inj₂ (inj₂ refl)
  ... | true  | false | true  = ⊥-elim (true≢false eq)
  ... | true  | true  | false = (λ _ → refl) , inj₂ (inj₂ refl)
  ... | true  | true  | true  = ⊥-elim (true≢false eq)

-- Acceptance of a one-λ unfold is the block-free head, the guarded
-- tail, HeadSeed, and SeedCovered. Nothing else is supplied.
unfFacts : ∀ {n} {k : ℕ} {σ : Sig} {B : List ℕ} {s : Tm n} {q : Qty} {A : Tm n}
              {h t : Tm (suc n)}
  → AllUnf k σ B (unf s (lam q A (pair h t)))
  → hasSelf B h ≡ false × GuardedTail B t × HeadSeed B h s × SeedCovered B h t s
unfFacts {k = k} {σ = σ} {B = B} {s = s} {q = q} {A = A} {h = h} {t = t} u =
  facts k u
  where
  step = lam q A (pair h t)
  facts : ∀ k′ → AllUnf k′ σ B (unf s step)
        → hasSelf B h ≡ false × GuardedTail B t × HeadSeed B h s × SeedCovered B h t s
  facts zero (_ , weq , _) = ⊥-elim (fail≢ok weq)
  facts (suc _) (.step , refl , sg-lam (sg-pair hh gt) , bit , _) =
    let hs , cov = lamPairFacts B {s = s} {h = h} {t = t} bit
        r : hasSelf B h ≡ false × GuardedTail B t × HeadSeed B h s × SeedCovered B h t s
        r = hh , gt , hs , cov
    in r

-- The same facts, as the body shape Theorem A opens.
body-unf : ∀ {n k σ B} {s : Tm n} {q A} {h t : Tm (suc n)}
  → AllUnf k σ B (unf s (lam q A (pair h t)))
  → BodyShape B (unf s (lam q A (pair h t)))
body-unf {s = s} {q = q} {A = A} {h = h} {t = t} u =
  let hh , gt , hs , cov = unfFacts {s = s} {q = q} {A = A} {h = h} {t = t} u
  in sh-unf hh hs gt cov

-- Stream observation. The tail term is block-free: a call in the tail
-- is not this theorem. HeadSeed and the block-free head are unfFacts.
obs-stream-ok : ∀ {k σ m B q} {A s : Tm 0} {h t : Tm 1}
  → AllUnf k σ B (unf s (lam q A (pair h t)))
  → hasSelf B t ≡ false
  → ∀ d → Obs σ m B false d (unf s (lam q A (pair h t)))
obs-stream-ok {k = k} {σ = σ} {B = B} {q = q} {A = A} {s = s} {h = h} {t = t} u ht d =
  let hh , _ , hs , _ = unfFacts {k = k} {σ = σ} {B = B} {s = s} {q = q} {A = A} {h = h} {t = t} u
  in obs-stream {B = B} {q = q} {A = A} {s = s} {h = h} {t = t} hh ht hs d

-- The tail of an accepted unfold, read as the Nav obs-fam consumes.
-- A pair and a block-free tail are not a Nav. A nested unfold's seed
-- is block-free by gc-unf, so its HeadSeed and SeedCovered are that
-- fact. An application of an unfold is not a Nav.
data GotNav {n} (B : List ℕ) (t : Tm n) : Set where
  got  : Nav B t → GotNav B t
  miss : GotNav B t

nav-of-tail : ∀ {n} (B : List ℕ) (t : Tm n) → GuardedTail B t → GotNav B t
nav-of-call : ∀ {n} (B : List ℕ) {t : Tm n} → GuardedCall B t → GotNav B t

nav-of-tail B _ (gt-absent _) = miss
nav-of-tail B _ (gt-call c) = nav-of-call B c

nav-of-call B (gc-def el) = got (nv-sp (sp-def el))
nav-of-call B (gc-app ha c) with nav-of-call B c
... | miss = miss
... | got (nv-sp s) = got (nv-sp (sp-app ha s))
... | got (nv-unf _ _ _ _) = miss
nav-of-call _ (gc-pair _ _) = miss
nav-of-call B (gc-unf {s = s} {h = h} {t = t} hs _ hh tg) with nav-of-tail B t tg
... | miss = miss
... | got n = got (nv-unf hh (λ _ → hs) (inj₂ (inj₂ hs)) n)

-- One leading λ, then the unfold, when the tail is a Nav. The four
-- facts are unfFacts.
opened-one : ∀ {n k σ B} {s : Tm n} {q A} {h t : Tm (suc n)}
  → AllUnf k σ B (unf s (lam q A (pair h t)))
  → Nav B t
  → Opened B (unf s (lam q A (pair h t)))
opened-one {s = s} {q = q} {A = A} {h = h} {t = t} u n =
  let hh , _ , hs , cov = unfFacts {s = s} {q = q} {A = A} {h = h} {t = t} u
  in od-unf hh hs cov n

-- The instantiated tail of a closed one-λ unfold unrolls. GuardedTail,
-- HeadSeed, and SeedCovered are the ones acceptance recorded. Unrolls
-- is a closed observation, so the tail is read at the seed.
unroll-accepted : ∀ {k σ B q} {A s : Tm 0} {h t : Tm 1}
  → AllUnf k σ B (unf s (lam q A (pair h t)))
  → Bodies σ B
  → ∀ d → Unrolls σ B d (inst t s)
unroll-accepted {k = k} {σ = σ} {B = B} {q = q} {A = A} {s = s} {h = h} {t = t} u bod d =
  let _ , gt , hs , cov = unfFacts {k = k} {σ = σ} {B = B} {s = s} {q = q} {A = A} {h = h} {t = t} u
  in guarded-unrolls bod (tail-inst B {h = h} {t = t} {s = s} hs cov gt) d


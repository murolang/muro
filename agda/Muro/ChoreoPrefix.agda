------------------------------------------------------------------------
-- A list of global events is a legal prefix of a choreography, in the
-- order the choreography is written.
--
-- An event is a message (`msg a b ℓ A`: role `a` sends label `ℓ`
-- carrying type `A` to role `b`) or a choice (`pick p ℓ`: role `p`
-- takes branch `ℓ`). `Step g e g′` takes the first interaction written
-- in `g`. Two interactions that share no role are still taken in the
-- written order: the global type fixes one order, and the prefix
-- follows it. `GLeg es g` is a derivation that `es` is a legal prefix
-- of `g`. The empty list stops anywhere.
--
-- `accept` decides it. It is sound (`accept-sound`) and complete
-- (`accept-complete`). The Elixir checker (`Muro.Choreo.prefix/3`) and
-- the monitor `--backend fsm` emits for a choreography follow `step`.
-- The emitted monitor also checks a payload value against its type.
-- That check is the state machine's, and it is not this theorem.
--
-- This is spec. No constructor is added to Tm.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.ChoreoPrefix where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String.Base using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Negation.Core using (¬_)

open import Muro.Session using (Ty; unit; ty≟)
open import Muro.Choreo using (
  DecEq; yes′; no′; Role; role; role-eq; GType; endG; comm; choice)

------------------------------------------------------------------------
-- Events.
------------------------------------------------------------------------

data Ev : Set where
  msg  : Role → Role → String → Ty → Ev
  pick : Role → String → Ev

ev-eq : (e f : Ev) → DecEq (e ≡ f)
ev-eq (msg a b ℓ A) (msg c d k B) with role-eq a c
... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
... | yes′ refl with role-eq b d
... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
... | yes′ refl with ℓ ≟ k
... | no ¬eq = no′ (λ { refl → ¬eq refl })
... | yes refl with ty≟ A B
... | no ¬eq = no′ (λ { refl → ¬eq refl })
... | yes refl = yes′ refl
ev-eq (msg _ _ _ _) (pick _ _) = no′ (λ ())
ev-eq (pick _ _) (msg _ _ _ _) = no′ (λ ())
ev-eq (pick p ℓ) (pick q k) with role-eq p q
... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
... | yes′ refl with ℓ ≟ k
... | no ¬eq = no′ (λ { refl → ¬eq refl })
... | yes refl = yes′ refl

------------------------------------------------------------------------
-- One step in the written order.
------------------------------------------------------------------------

-- The branch labelled `ℓ`: the first one written with that label.
data Arm : String → List (String × GType) → GType → Set where
  here  : ∀ {ℓ g bs} → Arm ℓ ((ℓ , g) ∷ bs) g
  there : ∀ {ℓ k h bs g} → ¬ (k ≡ ℓ) → Arm ℓ bs g → Arm ℓ ((k , h) ∷ bs) g

data Step : GType → Ev → GType → Set where
  smsg  : ∀ {a b ℓ A g} → Step (comm a b ℓ A g) (msg a b ℓ A) g
  spick : ∀ {p ℓ bs g} → Arm ℓ bs g → Step (choice p bs) (pick p ℓ) g

data GLeg : List Ev → GType → Set where
  ghalt : ∀ {g} → GLeg [] g
  gstep : ∀ {g e g′ es} → Step g e g′ → GLeg es g′ → GLeg (e ∷ es) g

------------------------------------------------------------------------
-- Decision.
------------------------------------------------------------------------

arm : String → List (String × GType) → Maybe GType
arm ℓ [] = nothing
arm ℓ ((k , h) ∷ bs) with k ≟ ℓ
... | yes _ = just h
... | no _ = arm ℓ bs

step : GType → Ev → Maybe GType
step endG _ = nothing
step (comm a b ℓ A g) e with ev-eq (msg a b ℓ A) e
... | yes′ _ = just g
... | no′ _ = nothing
step (choice p bs) (msg _ _ _ _) = nothing
step (choice p bs) (pick q ℓ) with role-eq p q
... | yes′ _ = arm ℓ bs
... | no′ _ = nothing

mutual
  accept : List Ev → GType → Bool
  accept [] _ = true
  accept (e ∷ es) g = next (step g e) es

  next : Maybe GType → List Ev → Bool
  next nothing _ = false
  next (just g) es = accept es g

------------------------------------------------------------------------
-- Soundness and completeness.
------------------------------------------------------------------------

nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

arm-sound : ∀ ℓ bs g → arm ℓ bs ≡ just g → Arm ℓ bs g
arm-sound ℓ [] g ()
arm-sound ℓ ((k , h) ∷ bs) g eq with k ≟ ℓ
arm-sound ℓ ((.ℓ , h) ∷ bs) .h refl | yes refl = here
... | no ¬eq = there ¬eq (arm-sound ℓ bs g eq)

arm-complete : ∀ {ℓ bs g} → Arm ℓ bs g → arm ℓ bs ≡ just g
arm-complete {ℓ} here with ℓ ≟ ℓ
... | yes _ = refl
... | no ¬eq = ⊥-elim (¬eq refl)
arm-complete {ℓ} (there {k = k} ¬eq a) with k ≟ ℓ
... | yes eq = ⊥-elim (¬eq eq)
... | no _ = arm-complete a

step-sound : ∀ g e g′ → step g e ≡ just g′ → Step g e g′
step-sound endG _ _ ()
step-sound (comm a b ℓ A g) e g′ eq with ev-eq (msg a b ℓ A) e
step-sound (comm a b ℓ A g) .(msg a b ℓ A) .g refl | yes′ refl = smsg
... | no′ _ = ⊥-elim (nothing≢just eq)
step-sound (choice p bs) (msg _ _ _ _) _ ()
step-sound (choice p bs) (pick q ℓ) g′ eq with role-eq p q
... | yes′ refl = spick (arm-sound ℓ bs g′ eq)
... | no′ _ = ⊥-elim (nothing≢just eq)

step-complete : ∀ {g e g′} → Step g e g′ → step g e ≡ just g′
step-complete (smsg {a} {b} {ℓ} {A}) with ev-eq (msg a b ℓ A) (msg a b ℓ A)
... | yes′ _ = refl
... | no′ ¬eq = ⊥-elim (¬eq refl)
step-complete (spick {p} a) with role-eq p p
... | yes′ _ = arm-complete a
... | no′ ¬eq = ⊥-elim (¬eq refl)

next-sound : ∀ m es → next m es ≡ true → Σ GType (λ g′ → m ≡ just g′ × accept es g′ ≡ true)
next-sound nothing _ ()
next-sound (just g′) _ eq = g′ , refl , eq

accept-sound : ∀ es g → accept es g ≡ true → GLeg es g
accept-sound [] _ _ = ghalt
accept-sound (e ∷ es) g eq = from (next-sound (step g e) es eq)
  where
    from : Σ GType (λ g′ → step g e ≡ just g′ × accept es g′ ≡ true) → GLeg (e ∷ es) g
    from (g′ , hit , rest) = gstep (step-sound g e g′ hit) (accept-sound es g′ rest)

next-complete : ∀ {m g′} es → m ≡ just g′ → accept es g′ ≡ true → next m es ≡ true
next-complete _ refl t = t

accept-complete : ∀ {es g} → GLeg es g → accept es g ≡ true
accept-complete ghalt = refl
accept-complete {e ∷ es} (gstep s l) = next-complete es (step-complete s) (accept-complete l)

------------------------------------------------------------------------
-- The release of #308. The front is deployed before the worker. The
-- written order keeps that rule between two pairs that projection
-- separates.
------------------------------------------------------------------------

rel front worker : Role
rel = role "release"
front = role "front"
worker = role "worker"

plan : GType
plan =
  comm rel front "deploy" unit
    (comm front rel "deployed" unit
      (comm rel worker "deploy" unit
        (comm worker rel "deployed" unit endG)))

front-first : GLeg (msg rel front "deploy" unit ∷ msg front rel "deployed" unit ∷
                    msg rel worker "deploy" unit ∷ []) plan
front-first = gstep smsg (gstep smsg (gstep smsg ghalt))

front-first-accepts :
  accept (msg rel front "deploy" unit ∷ msg front rel "deployed" unit ∷
          msg rel worker "deploy" unit ∷ []) plan ≡ true
front-first-accepts = refl

-- The worker is not deployed while the front's reply is outstanding.
worker-early : ¬ GLeg (msg rel front "deploy" unit ∷ msg rel worker "deploy" unit ∷ []) plan
worker-early (gstep smsg (gstep () _))

worker-early-refused :
  accept (msg rel front "deploy" unit ∷ msg rel worker "deploy" unit ∷ []) plan ≡ false
worker-early-refused = refl

-- Two interactions that share no role keep their written order too.
apart : GType
apart = comm (role "a") (role "b") "x" unit (comm (role "c") (role "d") "y" unit endG)

apart-swapped : ¬ GLeg (msg (role "c") (role "d") "y" unit ∷ []) apart
apart-swapped (gstep () _)

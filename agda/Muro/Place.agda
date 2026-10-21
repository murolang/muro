------------------------------------------------------------------------
-- Placement as a coeffect. A value sits at a place. The default
-- place is ambient. A polymorphic value is instantiated at the
-- place where it is used, and that use stays. A fixed value used
-- at another place crosses once.
--
-- Spec holds the scheme. Evidence is the move. A run term has no
-- seat: run is placement-agnostic.
--
-- This is not a source syntax. None of these constructors is added
-- to Tm or PTm. `decide` chooses stay or one boundary. A later
-- checker can follow that choice. There is no RPC here.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Place where

open import Data.Empty using (⊥)
open import Data.String.Base using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

open import Muro.Base using (Mode; spec; evid; run)

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- Ambient is the place of a program that names none. A node is a
-- named place, the only place a boundary can point at.
------------------------------------------------------------------------

data Place : Set where
  ambient : Place
  node    : String → Place

place≟ : (p q : Place) → Dec (p ≡ q)
place≟ ambient    ambient    = yes refl
place≟ ambient    (node _)   = no (λ ())
place≟ (node _)   ambient    = no (λ ())
place≟ (node x)   (node y)   with x ≟ y
... | yes eq = yes (cong node eq)
... | no ¬eq = no (λ { refl → ¬eq refl })

------------------------------------------------------------------------
-- One move. `stay` has no boundary. `cross` has one. There is no
-- constructor with two.
------------------------------------------------------------------------

data Move : Place → Place → Set where
  stay  : ∀ {p} → Move p p
  cross : ∀ {p q} → ¬ (p ≡ q) → Move p q

data Bounds : Set where
  none : Bounds
  one  : Bounds

bounds : ∀ {p q} → Move p q → Bounds
bounds stay       = none
bounds (cross _)  = one

data How : Bounds → Set where
  local    : How none
  boundary : How one

how : ∀ {p q} (m : Move p q) → How (bounds m)
how stay       = local
how (cross _)  = boundary

decide : (p q : Place) → Move p q
decide p q with place≟ p q
... | yes eq = subst (λ r → Move p r) eq stay
... | no ¬eq = cross ¬eq

stay-here : decide ambient ambient ≡ stay
stay-here = refl

stay-node : decide (node "a") (node "a") ≡ stay
stay-node = refl

cross-away : decide ambient (node "a") ≡ cross (λ ())
cross-away = refl

cross-nodes : bounds (decide (node "a") (node "b")) ≡ one
cross-nodes = refl

------------------------------------------------------------------------
-- A scheme is the spec. `any` instantiates at the use. `fixed`
-- names the place. The default fixed place is ambient.
------------------------------------------------------------------------

data Scheme : Set where
  any   : Scheme
  fixed : Place → Scheme

ground : Scheme → Place → Place
ground any       q = q
ground (fixed p) _ = p

-- Evidence: reading the scheme at q stays, or crosses once.
conform : (s : Scheme) (q : Place) → Move (ground s q) q
conform any       q = stay
conform (fixed p) q = decide p q

-- Polymorphism introduces no boundary. Instantiating `any` at q
-- grounds at q, and the move stays.
poly-sound : ∀ q → ground any q ≡ q
poly-sound _ = refl

poly-bounds : ∀ q → bounds (conform any q) ≡ none
poly-bounds _ = refl

-- The default program is ambient, used at ambient, with no boundary.
home-bounds : bounds (conform (fixed ambient) ambient) ≡ none
home-bounds = refl

-- A fixed ambient value used at a node takes one boundary.
away-bounds : bounds (conform (fixed ambient) (node "a")) ≡ one
away-bounds = refl

------------------------------------------------------------------------
-- The wall. Spec holds the scheme. Evidence holds the move.
-- Run has no constructor.
------------------------------------------------------------------------

data Seat : Mode → Set where
  placed   : Scheme → Seat spec
  conforms : (s : Scheme) (q : Place) → Move (ground s q) q → Seat evid

no-run : ¬ Seat run
no-run ()

default-seat : Seat spec
default-seat = placed (fixed ambient)

home-evidence : Seat evid
home-evidence = conforms (fixed ambient) ambient (conform (fixed ambient) ambient)

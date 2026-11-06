------------------------------------------------------------------------
-- A party of a description sits at a place. A party is a name. A
-- place is ambient or a node. Two parties who have a session stay
-- when they sit at the same place, and cross once when the places
-- differ. A party with no session in the description has no
-- boundary.
--
-- The boundary is `decide` of the two places. The protocol is the
-- session, and it is the same protocol at every place. The payload
-- stays on the session. There is no constructor that carries a
-- payload on the move. A description has no evidence payload, so a
-- seated party owes no evidence.
--
-- Spec holds where the party sits. Evidence is the boundary. A run
-- term has no seat. None of these constructors is added to Tm.
-- The checker follows this seating: `seat` names the party,
-- the place, and the description, and `link` states stay or cross.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Seated where

open import Data.Empty using (⊥)
open import Data.Maybe.Base using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Muro.Base using (Mode; spec; evid; run)
open import Muro.Session using (Proto; nat; end; send; recv)
open import Muro.Dual using (dual)
open import Muro.Place using (Place; ambient; node; Bounds; none; one; bounds; decide)
open import Muro.Talk using
  ( Party; party; Talk; seen
  ; ping-talk; pong-seen; peer-seen
  ; split; split-log
  ; one-arm; one-arm-bc
  )

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- Two parties, the places they sit at, and a description that gives
-- them a session. The move is not stored: it is `decide` of the
-- places, so the same place cannot be written as a cross.
------------------------------------------------------------------------

data Apart (p : Party) (a : Place) (q : Party) (b : Place) (t : Talk) : Set where
  apart : ∀ {S} → seen p q t ≡ just S → Apart p a q b t

bound : ∀ {p a q b t} → Apart p a q b t → Bounds
bound {a = a} {b = b} _ = bounds (decide a b)

proto : ∀ {p a q b t} → Apart p a q b t → Proto
proto (apart {S} _) = S

nothing≢just : ∀ {S : Proto} → nothing ≡ just S → ⊥
nothing≢just ()

just-inj : ∀ {S T : Proto} → just S ≡ just T → S ≡ T
just-inj refl = refl

-- The protocol does not depend on the places.
bits-stay :
  ∀ {a b c d} →
  (h : Apart (party "pong") a (party "peer") b ping-talk) →
  (k : Apart (party "pong") c (party "peer") d ping-talk) →
  proto h ≡ proto k
bits-stay (apart eq) (apart eq′) = just-inj (trans (sym eq) eq′)

-- A party with no session has no boundary, at any place.
no-link : ∀ {a b} → ¬ Apart (party "log") a (party "peer") b split
no-link (apart eq) = nothing≢just (trans (sym split-log) eq)

no-arm : ∀ {u v} → ¬ Apart (party "b") u (party "c") v one-arm
no-arm (apart eq) = nothing≢just (trans (sym one-arm-bc) eq)

------------------------------------------------------------------------
-- `pong` and `peer` on `ping-talk`. At one node the boundary is
-- empty. At two nodes it is one. The session is the same session.
------------------------------------------------------------------------

home : Apart (party "pong") (node "a") (party "peer") (node "a") ping-talk
home = apart pong-seen

home-stays : bound home ≡ none
home-stays = refl

away : Apart (party "pong") (node "a") (party "peer") (node "b") ping-talk
away = apart pong-seen

away-crosses : bound away ≡ one
away-crosses = refl

-- The other party reads the same boundary.
peer-home : Apart (party "peer") (node "a") (party "pong") (node "a") ping-talk
peer-home = apart peer-seen

peer-home-stays : bound peer-home ≡ none
peer-home-stays = refl

away-back : Apart (party "peer") (node "b") (party "pong") (node "a") ping-talk
away-back = apart peer-seen

away-back-crosses : bound away-back ≡ one
away-back-crosses = refl

same-boundary : bound away ≡ bound away-back
same-boundary = refl

-- Ambient is a place. Two parties there stay. One of them at a node
-- crosses once.
both-ambient : Apart (party "pong") ambient (party "peer") ambient ping-talk
both-ambient = apart pong-seen

ambient-stays : bound both-ambient ≡ none
ambient-stays = refl

to-node : Apart (party "pong") ambient (party "peer") (node "a") ping-talk
to-node = apart pong-seen

to-node-crosses : bound to-node ≡ one
to-node-crosses = refl

home-bits : proto home ≡ recv nat (send nat end)
home-bits = refl

away-bits : proto away ≡ recv nat (send nat end)
away-bits = refl

same-bits : proto home ≡ proto away
same-bits = refl

-- The other party's session is the other end, at either place.
peer-bits : proto peer-home ≡ dual (proto home)
peer-bits = refl

peer-away-bits : proto away-back ≡ dual (proto away)
peer-away-bits = refl

------------------------------------------------------------------------
-- The wall. Spec holds where a party sits. Evidence is the boundary
-- of two parties the description seats. Run has no constructor.
------------------------------------------------------------------------

data Seat : Mode → Set where
  seated : Talk → Party → Place → Seat spec
  linked : ∀ {p a q b t} → Apart p a q b t → Seat evid

no-run : ¬ Seat run
no-run ()

pong-at : Seat spec
pong-at = seated ping-talk (party "pong") (node "a")

peer-at : Seat spec
peer-at = seated ping-talk (party "peer") (node "b")

pong-peer-away : Seat evid
pong-peer-away = linked away

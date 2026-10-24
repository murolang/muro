------------------------------------------------------------------------
-- A meeting sits where the parties sit. Two processes that meet are
-- the two parties of one description. They stay when those parties
-- sit at the same place, and cross once when the places differ.
--
-- The boundary is the seating's boundary: `decide` of the two
-- places. The same place cannot be written as a cross. The protocol
-- is the session, and it is the same protocol at every place. The
-- payload stays on the session. A party with no session has no
-- meeting, at any place. Processes that exchange some other payload
-- are not these parties. A description has no evidence payload, so
-- these meetings carry none.
--
-- The meeting is evidence. A run term has no seat. None of these
-- constructors is added to Tm. A `.muro` file does not write
-- this meeting. The emitters are unchanged.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Held where

open import Data.Empty using (⊥)
open import Data.List.Base using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Muro.Base using (Mode; evid; run)
open import Muro.Session using
  ( Proto; nat; end; send; recv; choose
  ; Proc; done; stop; put; get; zero; suc; lit
  ; Conforms; done-end; put-ok; get-ok; pick0-ok; cover-ok; lit-ok
  )
open import Muro.Dual using (dual)
open import Muro.Place using (Place; ambient; node; Bounds; none; one)
open import Muro.Meet using
  ( Meets; Meetsρ; meets-sym; done-done; put-get; get-put
  ; pong; peer; pong-peer; taker; giver; choice-meet
  )
open import Muro.Talk using
  ( Party; party; Talk; over
  ; ping-talk; pong-seen; arm; arm-a; arm-b; one-arm; split
  )
import Muro.Seated as Seated

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- The processes, the parties, and the places. The move is not
-- stored. It is the seating's move, so the meeting stays where the
-- parties stay and crosses once where they cross.
------------------------------------------------------------------------

data Held
  (P : Proc) (p : Party) (a : Place)
  (Q : Proc) (q : Party) (b : Place)
  (t : Talk) : Set where
  held :
    (h : Seated.Apart p a q b t) →
    Meets P Q →
    Conforms [] P (Seated.proto h) →
    Conforms [] Q (dual (Seated.proto h)) →
    Held P p a Q q b t

bound : ∀ {P p a Q q b t} → Held P p a Q q b t → Bounds
bound (held h _ _ _) = Seated.bound h

proto : ∀ {P p a Q q b t} → Held P p a Q q b t → Proto
proto (held h _ _ _) = Seated.proto h

-- The meeting's boundary is the seating's boundary.
boundary-is-seating :
  ∀ {P p a Q q b t}
  (h : Seated.Apart p a q b t)
  (m : Meets P Q)
  (c : Conforms [] P (Seated.proto h))
  (d : Conforms [] Q (dual (Seated.proto h))) →
  bound (held h m c d) ≡ Seated.bound h
boundary-is-seating _ _ _ _ = refl

------------------------------------------------------------------------
-- `pong` receives a nat and sends a nat. `peer` sends a nat and
-- receives a nat. At one node the boundary is empty. At two nodes
-- it is one. The session is the same session.
------------------------------------------------------------------------

home : Held pong (party "pong") (node "a") peer (party "peer") (node "a") ping-talk
home = held Seated.home pong-peer (get-ok refl (put-ok refl lit-ok done-end)) (put-ok refl lit-ok (get-ok refl done-end))

home-stays : bound home ≡ none
home-stays = refl

home-not-cross : ¬ (bound home ≡ one)
home-not-cross ()

away : Held pong (party "pong") (node "a") peer (party "peer") (node "b") ping-talk
away = held Seated.away pong-peer (get-ok refl (put-ok refl lit-ok done-end)) (put-ok refl lit-ok (get-ok refl done-end))

away-crosses : bound away ≡ one
away-crosses = refl

away-not-stay : ¬ (bound away ≡ none)
away-not-stay ()

-- The protocol does not depend on the places.
bits-stay : proto home ≡ proto away
bits-stay = refl

home-bits : proto home ≡ recv nat (send nat end)
home-bits = refl

away-bits : proto away ≡ recv nat (send nat end)
away-bits = refl

-- The other party reads the same boundary, and the other end.
away-back : Held peer (party "peer") (node "b") pong (party "pong") (node "a") ping-talk
away-back =
  held Seated.away-back (meets-sym pong-peer)
    (put-ok refl lit-ok (get-ok refl done-end))
    (get-ok refl (put-ok refl lit-ok done-end))

away-back-crosses : bound away-back ≡ one
away-back-crosses = refl

same-boundary : bound away ≡ bound away-back
same-boundary = refl

peer-bits : proto away-back ≡ dual (proto away)
peer-bits = refl

-- Ambient is a place. Two parties there stay. One of them at a
-- node crosses once.
both-ambient : Held pong (party "pong") ambient peer (party "peer") ambient ping-talk
both-ambient =
  held Seated.both-ambient pong-peer (get-ok refl (put-ok refl lit-ok done-end)) (put-ok refl lit-ok (get-ok refl done-end))

ambient-stays : bound both-ambient ≡ none
ambient-stays = refl

to-node : Held pong (party "pong") ambient peer (party "peer") (node "a") ping-talk
to-node =
  held Seated.to-node pong-peer (get-ok refl (put-ok refl lit-ok done-end)) (put-ok refl lit-ok (get-ok refl done-end))

to-node-crosses : bound to-node ≡ one
to-node-crosses = refl

------------------------------------------------------------------------
-- The empty description seats any two parties at `end`. `done`
-- meets `done`. The same place stays. Two places cross once.
------------------------------------------------------------------------

quiet : Held done (party "a") ambient done (party "b") ambient over
quiet = held (Seated.apart refl) done-done done-end done-end

quiet-stays : bound quiet ≡ none
quiet-stays = refl

quiet-bits : proto quiet ≡ end
quiet-bits = refl

quiet-away : Held done (party "a") ambient done (party "b") (node "a") over
quiet-away = held (Seated.apart refl) done-done done-end done-end

quiet-away-crosses : bound quiet-away ≡ one
quiet-away-crosses = refl

quiet-same-bits : proto quiet ≡ proto quiet-away
quiet-same-bits = refl

------------------------------------------------------------------------
-- The left arm finishes. The other party offers that arm. Two
-- places cross once. The other party's session is the other end.
------------------------------------------------------------------------

choice-away : Held taker (party "a") (node "a") giver (party "b") (node "b") arm
choice-away =
  held (Seated.apart arm-a) choice-meet
    (pick0-ok done-end)
    (cover-ok done-end (get-ok refl done-end))

choice-crosses : bound choice-away ≡ one
choice-crosses = refl

choice-bits : proto choice-away ≡ choose end (send nat end)
choice-bits = refl

choice-back : Held giver (party "b") (node "b") taker (party "a") (node "a") arm
choice-back =
  held (Seated.apart arm-b) (meets-sym choice-meet)
    (cover-ok done-end (get-ok refl done-end))
    (pick0-ok done-end)

choice-back-crosses : bound choice-back ≡ one
choice-back-crosses = refl

choice-back-bits : proto choice-back ≡ dual (proto choice-away)
choice-back-bits = refl

------------------------------------------------------------------------
-- A party with no session has no meeting, at any place. The
-- processes are not consulted. A type the two processes do not share
-- has no derivation. Processes that do meet, on a direction the
-- session does not name, are not these parties. One end finishing
-- and the other abandoning has no derivation.
------------------------------------------------------------------------

no-session : ∀ {P Q a b} → ¬ Held P (party "log") a Q (party "peer") b split
no-session (held h _ _ _) = Seated.no-link h

no-arm : ∀ {P Q u v} → ¬ Held P (party "b") u Q (party "c") v one-arm
no-arm (held h _ _ _) = Seated.no-arm h

not-type : ∀ {a b} →
  ¬ Held pong (party "pong") a (put nat (lit zero) done) (party "peer") b ping-talk
not-type (held _ (get-put _ ()) _ _)

¬done-stop : ∀ {σ τ} → ¬ Meetsρ σ τ done stop
¬done-stop ()

¬finishes-abandons : ∀ {σ τ} →
  ¬ Meetsρ σ τ (put nat (lit (suc zero)) done) (get nat "x" stop)
¬finishes-abandons (put-get _ ())

not-ending : ∀ {a b} →
  ¬ Held pong (party "pong") a (put nat (lit zero) (get nat "x" stop)) (party "peer") b ping-talk
not-ending (held _ (get-put _ m) _ _) = ¬finishes-abandons m

put-not-recv : ¬ Conforms [] (put nat (lit zero) done) (recv nat (send nat end))
put-not-recv ()

not-role : ∀ {a b} →
  ¬ Held (put nat (lit zero) done) (party "pong") a (get nat "x" done) (party "peer") b ping-talk
not-role (held (Seated.apart eq) _ c _) =
  put-not-recv
    (subst (Conforms [] (put nat (lit zero) done))
      (sym (Seated.just-inj (trans (sym pong-seen) eq)))
      c)

------------------------------------------------------------------------
-- The wall. Evidence is the meeting at the parties' places. Run has
-- no constructor.
------------------------------------------------------------------------

data Seat : Mode → Set where
  gathered : ∀ {P p a Q q b t} → Held P p a Q q b t → Seat evid

no-run : ¬ Seat run
no-run ()

pong-peer-home : Seat evid
pong-peer-home = gathered home

pong-peer-away : Seat evid
pong-peer-away = gathered away

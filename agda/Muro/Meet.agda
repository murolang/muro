------------------------------------------------------------------------
-- Two processes on one channel. A send meets a receive of the same
-- bit, and the continuations meet. A choice meets the arm that was
-- offered. Both ends close, or both abandon. A bit they do not
-- share has no derivation.
--
-- The meeting is evidence. One end conforms to the protocol. The
-- other conforms to the other end of that protocol. A run term has
-- no seat. None of these constructors is added to Tm or PTm. The
-- Elixir checker follows the meeting: `meet name : left with right`.
-- The OTP emitter starts those two processes as each other's peer.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Meet where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (Mode; evid; run)
open import Muro.Session hiding (¬_; Seat; no-run; ping; pong; Answer; yes; no; decide)
open import Muro.Dual using (dual)

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- The bits agree. `put` meets `get` of that bit. `pick0` meets the
-- left arm of `cover`. `pick1` meets the right arm. `done` meets
-- `done`. `stop` meets `stop`.
------------------------------------------------------------------------

data Meets : Proc → Proc → Set where
  done-done : Meets done done
  stop-stop : Meets stop stop

  put-get : ∀ {b P Q} → Meets P Q → Meets (put b P) (get b Q)
  get-put : ∀ {b P Q} → Meets P Q → Meets (get b P) (put b Q)

  pick0-cover : ∀ {P Q R} → Meets P Q → Meets (pick0 P) (cover Q R)
  pick1-cover : ∀ {P Q R} → Meets P R → Meets (pick1 P) (cover Q R)

  cover-pick0 : ∀ {P Q R} → Meets P R → Meets (cover P Q) (pick0 R)
  cover-pick1 : ∀ {P Q R} → Meets Q R → Meets (cover P Q) (pick1 R)

meets-sym : ∀ {P Q} → Meets P Q → Meets Q P
meets-sym done-done = done-done
meets-sym stop-stop = stop-stop
meets-sym (put-get m) = get-put (meets-sym m)
meets-sym (get-put m) = put-get (meets-sym m)
meets-sym (pick0-cover m) = cover-pick0 (meets-sym m)
meets-sym (pick1-cover m) = cover-pick1 (meets-sym m)
meets-sym (cover-pick0 m) = pick0-cover (meets-sym m)
meets-sym (cover-pick1 m) = pick1-cover (meets-sym m)

------------------------------------------------------------------------
-- The wall. A meeting sits at evidence.
------------------------------------------------------------------------

data Seat : Mode → Set where
  met : ∀ {P Q} → Meets P Q → Seat evid

no-run : ¬ Seat run
no-run ()

------------------------------------------------------------------------
-- One channel. The second process conforms to `dual` of the protocol.
------------------------------------------------------------------------

data Channel (P Q : Proc) (S : Proto) : Set where
  channel : Meets P Q → Conforms P S → Conforms Q (dual S) → Channel P Q S

------------------------------------------------------------------------
-- The search. `yes` carries a derivation. `no` carries its refutation.
------------------------------------------------------------------------

data Answer (P Q : Proc) : Set where
  yes : Meets P Q → Answer P Q
  no  : ¬ Meets P Q → Answer P Q

put-get-yes : ∀ {b P Q} → Answer P Q → Answer (put b P) (get b Q)
put-get-yes (yes m) = yes (put-get m)
put-get-yes (no nm) = no (λ { (put-get m) → nm m })

get-put-yes : ∀ {b P Q} → Answer P Q → Answer (get b P) (put b Q)
get-put-yes (yes m) = yes (get-put m)
get-put-yes (no nm) = no (λ { (get-put m) → nm m })

pick0-yes : ∀ {P Q R} → Answer P Q → Answer (pick0 P) (cover Q R)
pick0-yes (yes m) = yes (pick0-cover m)
pick0-yes (no nm) = no (λ { (pick0-cover m) → nm m })

pick1-yes : ∀ {P Q R} → Answer P R → Answer (pick1 P) (cover Q R)
pick1-yes (yes m) = yes (pick1-cover m)
pick1-yes (no nm) = no (λ { (pick1-cover m) → nm m })

cover0-yes : ∀ {P Q R} → Answer P R → Answer (cover P Q) (pick0 R)
cover0-yes (yes m) = yes (cover-pick0 m)
cover0-yes (no nm) = no (λ { (cover-pick0 m) → nm m })

cover1-yes : ∀ {P Q R} → Answer Q R → Answer (cover P Q) (pick1 R)
cover1-yes (yes m) = yes (cover-pick1 m)
cover1-yes (no nm) = no (λ { (cover-pick1 m) → nm m })

decide : (P Q : Proc) → Answer P Q
decide done done = yes done-done
decide done stop = no (λ ())
decide done (put _ _) = no (λ ())
decide done (get _ _) = no (λ ())
decide done (pick0 _) = no (λ ())
decide done (pick1 _) = no (λ ())
decide done (cover _ _) = no (λ ())
decide stop done = no (λ ())
decide stop stop = yes stop-stop
decide stop (put _ _) = no (λ ())
decide stop (get _ _) = no (λ ())
decide stop (pick0 _) = no (λ ())
decide stop (pick1 _) = no (λ ())
decide stop (cover _ _) = no (λ ())
decide (put b0 P) (get b0 Q) = put-get-yes (decide P Q)
decide (put b1 P) (get b1 Q) = put-get-yes (decide P Q)
decide (put b0 _) (get b1 _) = no (λ ())
decide (put b1 _) (get b0 _) = no (λ ())
decide (put _ _) done = no (λ ())
decide (put _ _) stop = no (λ ())
decide (put _ _) (put _ _) = no (λ ())
decide (put _ _) (pick0 _) = no (λ ())
decide (put _ _) (pick1 _) = no (λ ())
decide (put _ _) (cover _ _) = no (λ ())
decide (get b0 P) (put b0 Q) = get-put-yes (decide P Q)
decide (get b1 P) (put b1 Q) = get-put-yes (decide P Q)
decide (get b0 _) (put b1 _) = no (λ ())
decide (get b1 _) (put b0 _) = no (λ ())
decide (get _ _) done = no (λ ())
decide (get _ _) stop = no (λ ())
decide (get _ _) (get _ _) = no (λ ())
decide (get _ _) (pick0 _) = no (λ ())
decide (get _ _) (pick1 _) = no (λ ())
decide (get _ _) (cover _ _) = no (λ ())
decide (pick0 P) (cover Q _) = pick0-yes (decide P Q)
decide (pick0 _) done = no (λ ())
decide (pick0 _) stop = no (λ ())
decide (pick0 _) (put _ _) = no (λ ())
decide (pick0 _) (get _ _) = no (λ ())
decide (pick0 _) (pick0 _) = no (λ ())
decide (pick0 _) (pick1 _) = no (λ ())
decide (pick1 P) (cover _ R) = pick1-yes (decide P R)
decide (pick1 _) done = no (λ ())
decide (pick1 _) stop = no (λ ())
decide (pick1 _) (put _ _) = no (λ ())
decide (pick1 _) (get _ _) = no (λ ())
decide (pick1 _) (pick0 _) = no (λ ())
decide (pick1 _) (pick1 _) = no (λ ())
decide (cover P _) (pick0 R) = cover0-yes (decide P R)
decide (cover _ Q) (pick1 R) = cover1-yes (decide Q R)
decide (cover _ _) done = no (λ ())
decide (cover _ _) stop = no (λ ())
decide (cover _ _) (put _ _) = no (λ ())
decide (cover _ _) (get _ _) = no (λ ())
decide (cover _ _) (cover _ _) = no (λ ())

------------------------------------------------------------------------
-- `pong` receives `b1` and sends `b0`. `peer` sends `b1` and receives
-- `b0`. A different bit has no derivation, and neither do two sends.
------------------------------------------------------------------------

ping : Proto
ping = recv end (send end end)

pong : Proc
pong = get b1 (put b0 done)

peer : Proc
peer = put b1 (get b0 done)

pong-peer : Meets pong peer
pong-peer = get-put (put-get done-done)

meets-decides : decide pong peer ≡ yes pong-peer
meets-decides = refl

peer-pong : decide peer pong ≡ yes (meets-sym pong-peer)
peer-pong = refl

ping-channel : Channel pong peer ping
ping-channel = channel pong-peer (get1 (put0 done-end)) (put1 (get0 done-end))

not-bit : ¬ Meets (get b1 done) (put b0 done)
not-bit ()

not-send : ¬ Meets (put b0 done) (put b0 done)
not-send ()

not-ending : ¬ Meets (put b0 stop) (get b0 done)
not-ending (put-get ())

------------------------------------------------------------------------
-- Both abandon after the same bit. Choosing meets the offered arm.
------------------------------------------------------------------------

left : Proc
left = put b0 stop

right : Proc
right = get b0 stop

left-right : Meets left right
left-right = put-get stop-stop

left-decides : decide left right ≡ yes left-right
left-decides = refl

abandon-channel : Channel left right (send end end)
abandon-channel = channel left-right (put0 abandon) (get0 abandon)

choice : Proto
choice = choose end (send end end)

taker : Proc
taker = pick0 done

giver : Proc
giver = cover done (get b0 done)

choice-meet : Meets taker giver
choice-meet = pick0-cover done-done

choice-decides : decide taker giver ≡ yes choice-meet
choice-decides = refl

choice-channel : Channel taker giver choice
choice-channel =
  channel choice-meet (pick0-ok done-end) (cover-ok done-end (get0 done-end))

not-arm : ¬ Meets (pick0 done) (cover (put b0 done) done)
not-arm (pick0-cover ())

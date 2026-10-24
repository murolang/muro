------------------------------------------------------------------------
-- Two processes on one channel. A send meets a receive of the same
-- payload type, and the continuations meet. The values need not be
-- the same term. A choice meets the arm that was offered. Both ends
-- close, or both abandon. A type they do not share has no derivation.
-- A received nat instantiates vector lengths that name it. A vector
-- of another length has no derivation. An evidence payload meets as
-- a nat: the evidence is in each conformance, not in the meeting, so
-- a channel needs both conformances as well. A bit index meets the
-- arm of that same bit. `b0` meets the first arm. `b1` meets the
-- second. A variable bit selects neither arm.
--
-- The meeting is evidence. One end conforms to the protocol. The
-- other conforms to the other end of that protocol. A run term has
-- no seat. None of these constructors is added to Tm. The
-- Elixir checker follows this meeting. The OTP image carries the
-- value. The other emitters do not implement the meeting.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Meet where

open import Data.Empty using (⊥)
open import Data.List.Base using ([])
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym)
open import Relation.Nullary.Decidable.Core using (Dec) renaming (yes to yes′; no to no′)

open import Muro.Base using (Mode; evid; run)
open import Muro.Session hiding (¬_; Seat; no-run; ping; pong; Answer; Answerρ; yes; no; decide; decideρ)
open import Muro.Dual using (dual; grant; grant-ok)

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- The payload types agree. `put` meets `get` of that type. The
-- value is not compared. `pick0` meets the left arm of `cover`.
-- `pick1` meets the right arm. `done` meets `done`. `stop` meets
-- `stop`.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- A nat received under a name instantiates the lengths that name it,
-- on the receiver's side. Another payload shadows the name and does
-- not instantiate a length. The processes in the judgment stay as
-- written, so the search recurses on a continuation.
------------------------------------------------------------------------

ext : {A : Ty} → String → ValExpr A → Idx → Idx
ext {nat} x v ρ = bind x (natExp v) (shadow x ρ)
ext {bit} x _ ρ = shadow x ρ
ext {unit} x _ ρ = shadow x ρ
ext {pair _ _} x _ ρ = shadow x ρ
ext {rec _} x _ ρ = shadow x ρ
ext {vec _ _} x _ ρ = shadow x ρ

data Meetsρ (σ τ : Idx) : Proc → Proc → Set where
  done-done : Meetsρ σ τ done done
  stop-stop : Meetsρ σ τ stop stop

  put-get : ∀ {A B v x P Q} →
    applyTy σ A ≡ applyTy τ B →
    Meetsρ σ (ext x v τ) P Q →
    Meetsρ σ τ (put A v P) (get B x Q)

  get-put : ∀ {A B v x P Q} →
    applyTy σ A ≡ applyTy τ B →
    Meetsρ (ext x v σ) τ P Q →
    Meetsρ σ τ (get A x P) (put B v Q)

  pick0-cover : ∀ {P Q R} → Meetsρ σ τ P Q → Meetsρ σ τ (pick0 P) (cover Q R)
  pick1-cover : ∀ {P Q R} → Meetsρ σ τ P R → Meetsρ σ τ (pick1 P) (cover Q R)

  cover-pick0 : ∀ {P Q R} → Meetsρ σ τ P R → Meetsρ σ τ (cover P Q) (pick0 R)
  cover-pick1 : ∀ {P Q R} → Meetsρ σ τ Q R → Meetsρ σ τ (cover P Q) (pick1 R)

  -- The literal selects the arm. The bit does not instantiate a length.
  iget-b0 : ∀ {x P Q R} →
    Meetsρ (ext x (lit b0) σ) τ P R →
    Meetsρ σ τ (iget x P Q) (put bit (lit b0) R)
  iget-b1 : ∀ {x P Q R} →
    Meetsρ (ext x (lit b1) σ) τ Q R →
    Meetsρ σ τ (iget x P Q) (put bit (lit b1) R)
  b0-iget : ∀ {x P Q R} →
    Meetsρ σ (ext x (lit b0) τ) P Q →
    Meetsρ σ τ (put bit (lit b0) P) (iget x Q R)
  b1-iget : ∀ {x P Q R} →
    Meetsρ σ (ext x (lit b1) τ) P R →
    Meetsρ σ τ (put bit (lit b1) P) (iget x Q R)

Meets : Proc → Proc → Set
Meets P Q = Meetsρ none none P Q

meets-sym : ∀ {σ τ P Q} → Meetsρ σ τ P Q → Meetsρ τ σ Q P
meets-sym done-done = done-done
meets-sym stop-stop = stop-stop
meets-sym (put-get eq m) = get-put (sym eq) (meets-sym m)
meets-sym (get-put eq m) = put-get (sym eq) (meets-sym m)
meets-sym (pick0-cover m) = cover-pick0 (meets-sym m)
meets-sym (pick1-cover m) = cover-pick1 (meets-sym m)
meets-sym (cover-pick0 m) = pick0-cover (meets-sym m)
meets-sym (cover-pick1 m) = pick1-cover (meets-sym m)
meets-sym (iget-b0 m) = b0-iget (meets-sym m)
meets-sym (iget-b1 m) = b1-iget (meets-sym m)
meets-sym (b0-iget m) = iget-b0 (meets-sym m)
meets-sym (b1-iget m) = iget-b1 (meets-sym m)

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
  channel : Meets P Q → Conforms [] P S → Conforms [] Q (dual S) → Channel P Q S

------------------------------------------------------------------------
-- The search. `yes` carries a derivation. `no` carries its refutation.
------------------------------------------------------------------------

data Answerρ (σ τ : Idx) (P Q : Proc) : Set where
  yes : Meetsρ σ τ P Q → Answerρ σ τ P Q
  no  : ¬ Meetsρ σ τ P Q → Answerρ σ τ P Q

Answer : Proc → Proc → Set
Answer P Q = Answerρ none none P Q

on-put-get : ∀ {σ τ A B v x P Q} →
  Dec (applyTy σ A ≡ applyTy τ B) →
  Answerρ σ (ext x v τ) P Q →
  Answerρ σ τ (put A v P) (get B x Q)
on-put-get (yes′ eq) (yes m) = yes (put-get eq m)
on-put-get (yes′ _) (no nm) = no (λ { (put-get _ m) → nm m })
on-put-get (no′ ¬eq) _ = no (λ { (put-get eq _) → ¬eq eq })

on-get-put : ∀ {σ τ A B v x P Q} →
  Dec (applyTy σ A ≡ applyTy τ B) →
  Answerρ (ext x v σ) τ P Q →
  Answerρ σ τ (get A x P) (put B v Q)
on-get-put (yes′ eq) (yes m) = yes (get-put eq m)
on-get-put (yes′ _) (no nm) = no (λ { (get-put _ m) → nm m })
on-get-put (no′ ¬eq) _ = no (λ { (get-put eq _) → ¬eq eq })

pick0-yes : ∀ {σ τ P Q R} → Answerρ σ τ P Q → Answerρ σ τ (pick0 P) (cover Q R)
pick0-yes (yes m) = yes (pick0-cover m)
pick0-yes (no nm) = no (λ { (pick0-cover m) → nm m })

pick1-yes : ∀ {σ τ P Q R} → Answerρ σ τ P R → Answerρ σ τ (pick1 P) (cover Q R)
pick1-yes (yes m) = yes (pick1-cover m)
pick1-yes (no nm) = no (λ { (pick1-cover m) → nm m })

cover0-yes : ∀ {σ τ P Q R} → Answerρ σ τ P R → Answerρ σ τ (cover P Q) (pick0 R)
cover0-yes (yes m) = yes (cover-pick0 m)
cover0-yes (no nm) = no (λ { (cover-pick0 m) → nm m })

cover1-yes : ∀ {σ τ P Q R} → Answerρ σ τ Q R → Answerρ σ τ (cover P Q) (pick1 R)
cover1-yes (yes m) = yes (cover-pick1 m)
cover1-yes (no nm) = no (λ { (cover-pick1 m) → nm m })

on-iget-b0 : ∀ {σ τ x P Q R} →
  Answerρ (ext x (lit b0) σ) τ P R →
  Answerρ σ τ (iget x P Q) (put bit (lit b0) R)
on-iget-b0 (yes m) = yes (iget-b0 m)
on-iget-b0 (no nm) = no (λ { (iget-b0 m) → nm m })

on-iget-b1 : ∀ {σ τ x P Q R} →
  Answerρ (ext x (lit b1) σ) τ Q R →
  Answerρ σ τ (iget x P Q) (put bit (lit b1) R)
on-iget-b1 (yes m) = yes (iget-b1 m)
on-iget-b1 (no nm) = no (λ { (iget-b1 m) → nm m })

on-b0-iget : ∀ {σ τ x P Q R} →
  Answerρ σ (ext x (lit b0) τ) P Q →
  Answerρ σ τ (put bit (lit b0) P) (iget x Q R)
on-b0-iget (yes m) = yes (b0-iget m)
on-b0-iget (no nm) = no (λ { (b0-iget m) → nm m })

on-b1-iget : ∀ {σ τ x P Q R} →
  Answerρ σ (ext x (lit b1) τ) P R →
  Answerρ σ τ (put bit (lit b1) P) (iget x Q R)
on-b1-iget (yes m) = yes (b1-iget m)
on-b1-iget (no nm) = no (λ { (b1-iget m) → nm m })

decideρ : (σ τ : Idx) (P Q : Proc) → Answerρ σ τ P Q
decideρ _ _ done done = yes done-done
decideρ _ _ done stop = no (λ ())
decideρ _ _ done (put _ _ _) = no (λ ())
decideρ _ _ done (get _ _ _) = no (λ ())
decideρ _ _ done (pick0 _) = no (λ ())
decideρ _ _ done (pick1 _) = no (λ ())
decideρ _ _ done (cover _ _) = no (λ ())
decideρ _ _ done (iget _ _ _) = no (λ ())
decideρ _ _ stop done = no (λ ())
decideρ _ _ stop stop = yes stop-stop
decideρ _ _ stop (put _ _ _) = no (λ ())
decideρ _ _ stop (get _ _ _) = no (λ ())
decideρ _ _ stop (pick0 _) = no (λ ())
decideρ _ _ stop (pick1 _) = no (λ ())
decideρ _ _ stop (cover _ _) = no (λ ())
decideρ _ _ stop (iget _ _ _) = no (λ ())
decideρ σ τ (put A v P) (get B x Q) =
  on-put-get (ty≟ (applyTy σ A) (applyTy τ B)) (decideρ σ (ext x v τ) P Q)
decideρ _ _ (put _ _ _) done = no (λ ())
decideρ _ _ (put _ _ _) stop = no (λ ())
decideρ _ _ (put _ _ _) (put _ _ _) = no (λ ())
decideρ _ _ (put _ _ _) (pick0 _) = no (λ ())
decideρ _ _ (put _ _ _) (pick1 _) = no (λ ())
decideρ _ _ (put _ _ _) (cover _ _) = no (λ ())
decideρ σ τ (put bit (lit b0) P) (iget x Q _) = on-b0-iget (decideρ σ (ext x (lit b0) τ) P Q)
decideρ σ τ (put bit (lit b1) P) (iget x _ R) = on-b1-iget (decideρ σ (ext x (lit b1) τ) P R)
decideρ _ _ (put bit (var _) _) (iget _ _ _) = no (λ ())
decideρ _ _ (put nat _ _) (iget _ _ _) = no (λ ())
decideρ _ _ (put unit _ _) (iget _ _ _) = no (λ ())
decideρ _ _ (put (pair _ _) _ _) (iget _ _ _) = no (λ ())
decideρ _ _ (put (rec _) _ _) (iget _ _ _) = no (λ ())
decideρ _ _ (put (vec _ _) _ _) (iget _ _ _) = no (λ ())
decideρ σ τ (get A x P) (put B v Q) =
  on-get-put (ty≟ (applyTy σ A) (applyTy τ B)) (decideρ (ext x v σ) τ P Q)
decideρ _ _ (get _ _ _) done = no (λ ())
decideρ _ _ (get _ _ _) stop = no (λ ())
decideρ _ _ (get _ _ _) (get _ _ _) = no (λ ())
decideρ _ _ (get _ _ _) (pick0 _) = no (λ ())
decideρ _ _ (get _ _ _) (pick1 _) = no (λ ())
decideρ _ _ (get _ _ _) (cover _ _) = no (λ ())
decideρ _ _ (get _ _ _) (iget _ _ _) = no (λ ())
decideρ σ τ (pick0 P) (cover Q _) = pick0-yes (decideρ σ τ P Q)
decideρ _ _ (pick0 _) done = no (λ ())
decideρ _ _ (pick0 _) stop = no (λ ())
decideρ _ _ (pick0 _) (put _ _ _) = no (λ ())
decideρ _ _ (pick0 _) (get _ _ _) = no (λ ())
decideρ _ _ (pick0 _) (pick0 _) = no (λ ())
decideρ _ _ (pick0 _) (pick1 _) = no (λ ())
decideρ _ _ (pick0 _) (iget _ _ _) = no (λ ())
decideρ σ τ (pick1 P) (cover _ R) = pick1-yes (decideρ σ τ P R)
decideρ _ _ (pick1 _) done = no (λ ())
decideρ _ _ (pick1 _) stop = no (λ ())
decideρ _ _ (pick1 _) (put _ _ _) = no (λ ())
decideρ _ _ (pick1 _) (get _ _ _) = no (λ ())
decideρ _ _ (pick1 _) (pick0 _) = no (λ ())
decideρ _ _ (pick1 _) (pick1 _) = no (λ ())
decideρ _ _ (pick1 _) (iget _ _ _) = no (λ ())
decideρ σ τ (cover P _) (pick0 R) = cover0-yes (decideρ σ τ P R)
decideρ σ τ (cover _ Q) (pick1 R) = cover1-yes (decideρ σ τ Q R)
decideρ _ _ (cover _ _) done = no (λ ())
decideρ _ _ (cover _ _) stop = no (λ ())
decideρ _ _ (cover _ _) (put _ _ _) = no (λ ())
decideρ _ _ (cover _ _) (get _ _ _) = no (λ ())
decideρ _ _ (cover _ _) (cover _ _) = no (λ ())
decideρ _ _ (cover _ _) (iget _ _ _) = no (λ ())
decideρ σ τ (iget x P Q) (put bit (lit b0) R) = on-iget-b0 (decideρ (ext x (lit b0) σ) τ P R)
decideρ σ τ (iget x P Q) (put bit (lit b1) R) = on-iget-b1 (decideρ (ext x (lit b1) σ) τ Q R)
decideρ _ _ (iget _ _ _) (put bit (var _) _) = no (λ ())
decideρ _ _ (iget _ _ _) (put nat _ _) = no (λ ())
decideρ _ _ (iget _ _ _) (put unit _ _) = no (λ ())
decideρ _ _ (iget _ _ _) (put (pair _ _) _ _) = no (λ ())
decideρ _ _ (iget _ _ _) (put (rec _) _ _) = no (λ ())
decideρ _ _ (iget _ _ _) (put (vec _ _) _ _) = no (λ ())
decideρ _ _ (iget _ _ _) done = no (λ ())
decideρ _ _ (iget _ _ _) stop = no (λ ())
decideρ _ _ (iget _ _ _) (get _ _ _) = no (λ ())
decideρ _ _ (iget _ _ _) (pick0 _) = no (λ ())
decideρ _ _ (iget _ _ _) (pick1 _) = no (λ ())
decideρ _ _ (iget _ _ _) (cover _ _) = no (λ ())
decideρ _ _ (iget _ _ _) (iget _ _ _) = no (λ ())

decide : (P Q : Proc) → Answer P Q
decide P Q = decideρ none none P Q

------------------------------------------------------------------------
-- `pong` receives a nat and sends a nat. `peer` sends a nat and
-- receives a nat. `zero` and `two` are different values of that
-- type, and both meet. A tuple wrapping a fixed map meets a receive
-- of that type. A different type has no derivation, and neither do
-- two sends.
------------------------------------------------------------------------

ping : Proto
ping = recv nat (send nat end)

pong : Proc
pong = get nat "x" (put nat (lit one) done)

peer : Proc
peer = put nat (lit zero) (get nat "y" done)

pong-peer : Meets pong peer
pong-peer = get-put refl (put-get refl done-done)

meets-decides : decide pong peer ≡ yes pong-peer
meets-decides = refl

peer-pong : decide peer pong ≡ yes (meets-sym pong-peer)
peer-pong = refl

other : Proc
other = put nat (lit two) (get nat "z" done)

other-meets : Meets pong other
other-meets = get-put refl (put-get refl done-done)

other-decides : decide pong other ≡ yes other-meets
other-decides = refl

ping-channel : Channel pong peer ping
ping-channel = channel pong-peer (get-ok refl (put-ok refl lit-ok done-end)) (put-ok refl lit-ok (get-ok refl done-end))

box-meet : Meets (put box (lit v-here) done) (get box "a" done)
box-meet = put-get refl done-done

there-meet : Meets (put box (lit v-there) done) (get box "b" done)
there-meet = put-get refl done-done

box-decides : decide (put box (lit v-here) done) (get box "a" done) ≡ yes box-meet
box-decides = refl

not-payload : ¬ Meets (put nat (lit zero) done) (get box "x" done)
not-payload (put-get () _)

------------------------------------------------------------------------
-- A bound name is sent at the type it was received. `reply` receives
-- a nat and sends that name. It meets a process that receives a nat.
-- A receive of a bit has no meeting with that name. The value is not
-- compared. The type written on `put` is the type compared.
------------------------------------------------------------------------

reply : Proc
reply = get nat "k" (put nat (var "k") done)

reply-peer : Proc
reply-peer = put nat (lit zero) (get nat "n" done)

reply-meet : Meets reply reply-peer
reply-meet = get-put refl (put-get refl done-done)

reply-decides : decide reply reply-peer ≡ yes reply-meet
reply-decides = refl

not-bound-type : ¬ Meets reply (put nat (lit zero) (get bit "n" done))
not-bound-type (get-put refl (put-get () _))

------------------------------------------------------------------------
-- The length that was received is the length of the vector. A vector
-- of another length has no meeting.
------------------------------------------------------------------------

sized-meet : Meets sized-server sized-client
sized-meet = get-put refl (put-get refl done-done)

sized-decides : decide sized-server sized-client ≡ yes sized-meet
sized-decides = refl

sized-miss : ¬ Meets sized-server sized-bad
sized-miss (get-put refl (put-get () _))

------------------------------------------------------------------------
-- The window is granted and the data is sent within it. The meeting
-- compares the nats. The evidence is the server's conformance, so a
-- server that guesses meets the grant but has no channel.
------------------------------------------------------------------------

window-meet : Meets full grant
window-meet = get-put refl (put-get refl done-done)

window-decides : decide full grant ≡ yes window-meet
window-decides = refl

window-channel : Channel full grant window
window-channel = channel window-meet full-ok grant-ok

guess-meets : Meets guess grant
guess-meets = get-put refl (put-get refl done-done)

guess-no-channel : ¬ Channel guess grant window
guess-no-channel (channel _ c _) = guess-refused c

not-send : ¬ Meets (put nat (lit zero) done) (put nat (lit zero) done)
not-send ()

not-ending : ¬ Meets (put nat (lit zero) stop) (get nat "x" done)
not-ending (put-get refl ())

------------------------------------------------------------------------
-- Both abandon after the same payload type. Choosing meets the
-- offered arm.
------------------------------------------------------------------------

left : Proc
left = put nat (lit zero) stop

right : Proc
right = get nat "x" stop

left-right : Meets left right
left-right = put-get refl stop-stop

left-decides : decide left right ≡ yes left-right
left-decides = refl

abandon-channel : Channel left right (send nat end)
abandon-channel = channel left-right (put-ok refl lit-ok abandon) (get-ok refl abandon)

choice : Proto
choice = choose end (send nat end)

taker : Proc
taker = pick0 done

giver : Proc
giver = cover done (get nat "x" done)

choice-meet : Meets taker giver
choice-meet = pick0-cover done-done

choice-decides : decide taker giver ≡ yes choice-meet
choice-decides = refl

choice-channel : Channel taker giver choice
choice-channel =
  channel choice-meet (pick0-ok done-end) (cover-ok done-end (get-ok refl done-end))

not-arm : ¬ Meets (pick0 done) (cover (put nat (lit zero) done) done)
not-arm (pick0-cover ())

------------------------------------------------------------------------
-- The bit selects the arm. `b0` meets the first continuation. `b1`
-- meets the second. The same index with the other continuation has
-- no meeting. A variable bit selects neither arm. A channel also
-- needs the other end, so an arm that was not dualised has none.
------------------------------------------------------------------------

route-client : Proc
route-client = put bit (lit b0) (get nat "m" done)

route-meet : Meets route-server route-client
route-meet = iget-b0 (put-get refl done-done)

route-meet-decides : decide route-server route-client ≡ yes route-meet
route-meet-decides = refl

route-client-one : Proc
route-client-one = put bit (lit b1) (put nat (lit zero) done)

route-one : Meets route-server route-client-one
route-one = iget-b1 (get-put refl done-done)

route-one-decides : decide route-server route-client-one ≡ yes route-one
route-one-decides = refl

route-miss : Proc
route-miss = put bit (lit b0) (put nat (lit one) done)

not-route : ¬ Meets route-server route-miss
not-route (iget-b0 ())

not-route-decides : decide route-server route-miss ≡ no not-route
not-route-decides = refl

route-channel : Channel route-server route-client route
route-channel =
  channel route-meet route-server-ok (iput0-ok (get-ok refl done-end))

not-crossed-channel : ¬ Channel route-server route-miss route
not-crossed-channel (channel _ _ (iput0-ok ()))

ask : Proc
ask = put bit (lit b1) (get bit "c" done)

echo-meet : Meets echo-bit ask
echo-meet = iget-b1 (put-get refl done-done)

echo-meet-decides : decide echo-bit ask ≡ yes echo-meet
echo-meet-decides = refl

not-var : ¬ Meets echo-bit (put bit (var "b") (get bit "c" done))
not-var ()

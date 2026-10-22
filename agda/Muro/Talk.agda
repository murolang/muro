------------------------------------------------------------------------
-- One description of an exchange. A party is a name. `say` is one
-- party sending a bit to another: the first continuation is `b0`
-- and the second is `b1`. `offer` is one party choosing and the
-- other offering both arms. A party does not talk to itself.
--
-- On the channel between two parties, the sender's session is
-- `send` or `choose` and the receiver's session is `recv` or
-- `branch`. A party off that channel has a session only when both
-- continuations are the same description, and then it is that
-- continuation's session. The other party's session is the other
-- end. A description that does not give a party a session has no
-- evidence at that party.
--
-- Spec holds the description. Evidence is one party's session. A
-- run term has no seat. None of these constructors is added to Tm
-- or PTm. A `.muro` file writes the description, and the checker
-- follows `seen`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Talk where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.String.Base using (String)
open import Data.String.Properties using (_≟_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

open import Muro.Base using (Mode; spec; evid; run)
open import Muro.Session using (Proto; end; send; recv; choose; branch)
open import Muro.Dual using (dual)

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- A party is a name. The description finishes, or one party sends
-- a bit, or one party chooses.
------------------------------------------------------------------------

data Party : Set where
  party : String → Party

party≟ : (p q : Party) → Dec (p ≡ q)
party≟ (party x) (party y) with x ≟ y
... | yes eq = yes (cong party eq)
... | no ¬eq = no (λ { refl → ¬eq refl })

data Talk : Set where
  over  : Talk
  say   : Party → Party → Talk → Talk → Talk
  offer : Party → Party → Talk → Talk → Talk

------------------------------------------------------------------------
-- Where this pair sits in one communication. `out` sends. `got`
-- receives. `off` is some other channel. `bad` is a party talking
-- to itself, or a channel from a party to itself.
------------------------------------------------------------------------

data Hear : Set where
  out : Hear
  got : Hear
  off : Hear
  bad : Hear

hear-of :
  (p q a b : Party) →
  Dec (a ≡ b) → Dec (p ≡ q) →
  Dec (p ≡ a) → Dec (q ≡ b) →
  Dec (p ≡ b) → Dec (q ≡ a) →
  Hear
hear-of _ _ _ _ (yes _) _ _ _ _ _ = bad
hear-of _ _ _ _ (no _) (yes _) _ _ _ _ = bad
hear-of _ _ _ _ (no _) (no _) (yes _) (yes _) _ _ = out
hear-of _ _ _ _ (no _) (no _) _ _ (yes _) (yes _) = got
hear-of _ _ _ _ (no _) (no _) _ _ _ _ = off

hear : Party → Party → Party → Party → Hear
hear p q a b =
  hear-of p q a b
    (party≟ a b) (party≟ p q) (party≟ p a) (party≟ q b) (party≟ p b) (party≟ q a)

------------------------------------------------------------------------
-- The two views of one communication. Sending here is receiving
-- there. A channel that is off for one party is off for the other.
------------------------------------------------------------------------

data Swapped : Hear → Hear → Set where
  out-got : Swapped out got
  got-out : Swapped got out
  off-off : Swapped off off
  bad-bad : Swapped bad bad

swapped :
  (p q a b : Party) →
  (ab : Dec (a ≡ b)) (pq : Dec (p ≡ q)) (qp : Dec (q ≡ p)) →
  (pa : Dec (p ≡ a)) (qa : Dec (q ≡ a)) →
  (qb : Dec (q ≡ b)) (pb : Dec (p ≡ b)) →
  Swapped
    (hear-of p q a b ab pq pa qb pb qa)
    (hear-of q p a b ab qp qa pb qb pa)
swapped _ _ _ _ (yes _) _ _ _ _ _ _ = bad-bad
swapped _ _ _ _ (no _) (yes refl) (no ¬qp) _ _ _ _ = ⊥-elim (¬qp refl)
swapped _ _ _ _ (no _) (no ¬pq) (yes refl) _ _ _ _ = ⊥-elim (¬pq refl)
swapped _ _ _ _ (no _) (yes _) (yes _) _ _ _ _ = bad-bad
swapped _ _ _ _ (no ¬ab) (no ¬pq) (no _) pa qa qb pb with pa | qa | qb | pb
... | yes refl | yes refl | _        | _        = ⊥-elim (¬pq refl)
... | yes refl | no _     | yes refl | yes refl = ⊥-elim (¬ab refl)
... | yes refl | no _     | yes refl | no _     = out-got
... | yes refl | no _     | no _     | yes refl = ⊥-elim (¬ab refl)
... | yes refl | no _     | no _     | no _     = off-off
... | no _     | yes refl | yes refl | _        = ⊥-elim (¬ab refl)
... | no _     | yes refl | no _     | yes refl = got-out
... | no _     | yes refl | no _     | no _     = off-off
... | no _     | no _     | yes refl | yes refl = off-off
... | no _     | no _     | yes refl | no _     = off-off
... | no _     | no _     | no _     | yes refl = off-off
... | no _     | no _     | no _     | no _     = off-off

swapped-hear : (p q a b : Party) → Swapped (hear p q a b) (hear q p a b)
swapped-hear p q a b =
  swapped p q a b
    (party≟ a b) (party≟ p q) (party≟ q p)
    (party≟ p a) (party≟ q a) (party≟ q b) (party≟ p b)

------------------------------------------------------------------------
-- Two descriptions are the same, or they are not. An outsider needs
-- them to be the same.
------------------------------------------------------------------------

talk≟ : (t u : Talk) → Dec (t ≡ u)
talk≟ over over = yes refl
talk≟ over (say _ _ _ _) = no (λ ())
talk≟ over (offer _ _ _ _) = no (λ ())
talk≟ (say _ _ _ _) over = no (λ ())
talk≟ (offer _ _ _ _) over = no (λ ())
talk≟ (say _ _ _ _) (offer _ _ _ _) = no (λ ())
talk≟ (offer _ _ _ _) (say _ _ _ _) = no (λ ())
talk≟ (say a b t0 t1) (say c d u0 u1) with party≟ a c
... | no ¬eq = no (λ { refl → ¬eq refl })
... | yes refl with party≟ b d
... | no ¬eq = no (λ { refl → ¬eq refl })
... | yes refl with talk≟ t0 u0
... | no ¬eq = no (λ { refl → ¬eq refl })
... | yes refl with talk≟ t1 u1
... | no ¬eq = no (λ { refl → ¬eq refl })
... | yes refl = yes refl
talk≟ (offer a b t0 t1) (offer c d u0 u1) with party≟ a c
... | no ¬eq = no (λ { refl → ¬eq refl })
... | yes refl with party≟ b d
... | no ¬eq = no (λ { refl → ¬eq refl })
... | yes refl with talk≟ t0 u0
... | no ¬eq = no (λ { refl → ¬eq refl })
... | yes refl with talk≟ t1 u1
... | no ¬eq = no (λ { refl → ¬eq refl })
... | yes refl = yes refl

------------------------------------------------------------------------
-- The session one party has with another. `nothing` is a party
-- with no session there.
------------------------------------------------------------------------

data Kind : Set where
  said    : Kind
  offered : Kind

both : (Proto → Proto → Proto) → Maybe Proto → Maybe Proto → Maybe Proto
both _ nothing _ = nothing
both _ _ nothing = nothing
both ctor (just S) (just T) = just (ctor S T)

join : Kind → Hear → {A : Set} → Dec A → Maybe Proto → Maybe Proto → Maybe Proto
join _ bad _ _ _ = nothing
join _ off (no _) _ _ = nothing
join _ off (yes _) m _ = m
join said out _ m n = both send m n
join said got _ m n = both recv m n
join offered out _ m n = both choose m n
join offered got _ m n = both branch m n

seen : Party → Party → Talk → Maybe Proto
seen p q over = just end
seen p q (say a b t0 t1) =
  join said (hear p q a b) (talk≟ t0 t1) (seen p q t0) (seen p q t1)
seen p q (offer a b t0 t1) =
  join offered (hear p q a b) (talk≟ t0 t1) (seen p q t0) (seen p q t1)

------------------------------------------------------------------------
-- The other party's session is the other end. Both have one, or
-- neither does.
------------------------------------------------------------------------

data Agree : Maybe Proto → Maybe Proto → Set where
  none : Agree nothing nothing
  ends : ∀ {S T} → T ≡ dual S → Agree (just S) (just T)

join-dual :
  ∀ act h h′ {A} (eq : Dec A) m0 n0 m1 n1 →
  Swapped h h′ →
  Agree m0 n0 →
  Agree m1 n1 →
  Agree (join act h eq m0 m1) (join act h′ eq n0 n1)
join-dual _ _ _ _ _ _ _ _ bad-bad _ _ = none
join-dual _ off off (yes _) _ _ _ _ off-off agr0 _ = agr0
join-dual _ off off (no _) _ _ _ _ off-off _ _ = none
join-dual said out got _ _ _ _ _ out-got none none = none
join-dual said out got _ _ _ _ _ out-got none (ends _) = none
join-dual said out got _ _ _ _ _ out-got (ends _) none = none
join-dual said out got _ _ _ _ _ out-got (ends eq0) (ends eq1) = ends (cong₂ recv eq0 eq1)
join-dual said got out _ _ _ _ _ got-out none none = none
join-dual said got out _ _ _ _ _ got-out none (ends _) = none
join-dual said got out _ _ _ _ _ got-out (ends _) none = none
join-dual said got out _ _ _ _ _ got-out (ends eq0) (ends eq1) = ends (cong₂ send eq0 eq1)
join-dual offered out got _ _ _ _ _ out-got none none = none
join-dual offered out got _ _ _ _ _ out-got none (ends _) = none
join-dual offered out got _ _ _ _ _ out-got (ends _) none = none
join-dual offered out got _ _ _ _ _ out-got (ends eq0) (ends eq1) = ends (cong₂ branch eq0 eq1)
join-dual offered got out _ _ _ _ _ got-out none none = none
join-dual offered got out _ _ _ _ _ got-out none (ends _) = none
join-dual offered got out _ _ _ _ _ got-out (ends _) none = none
join-dual offered got out _ _ _ _ _ got-out (ends eq0) (ends eq1) = ends (cong₂ choose eq0 eq1)

ends-dual : (p q : Party) (t : Talk) → Agree (seen p q t) (seen q p t)
ends-dual p q over = ends refl
ends-dual p q (say a b t0 t1) =
  join-dual said (hear p q a b) (hear q p a b) (talk≟ t0 t1)
    (seen p q t0) (seen q p t0) (seen p q t1) (seen q p t1)
    (swapped-hear p q a b) (ends-dual p q t0) (ends-dual p q t1)
ends-dual p q (offer a b t0 t1) =
  join-dual offered (hear p q a b) (hear q p a b) (talk≟ t0 t1)
    (seen p q t0) (seen q p t0) (seen p q t1) (seen q p t1)
    (swapped-hear p q a b) (ends-dual p q t0) (ends-dual p q t1)

other-end : (p q : Party) (t : Talk) {S : Proto} →
  seen p q t ≡ just S → seen q p t ≡ just (dual S)
other-end p q t {S} eq = go (ends-dual p q t) eq
  where
  go : ∀ {m n} → Agree m n → m ≡ just S → n ≡ just (dual S)
  go (ends r) refl = cong just r
  go none ()

------------------------------------------------------------------------
-- The wall. Spec holds the description. Evidence is one party's
-- session.
------------------------------------------------------------------------

data Seat : Mode → Set where
  described : Talk → Seat spec
  projected : ∀ {p q t S} → seen p q t ≡ just S → Seat evid

no-run : ¬ Seat run
no-run ()

------------------------------------------------------------------------
-- `pong` receives `b1` and then sends `b0`. That is `ping`. The
-- other party sends `b1` and then receives `b0`. The two
-- continuations differ, so a third party has no session there.
------------------------------------------------------------------------

ping-talk : Talk
ping-talk =
  say (party "peer") (party "pong") over
    (say (party "pong") (party "peer") over over)

pong-seen : seen (party "pong") (party "peer") ping-talk ≡ just (recv end (send end end))
pong-seen = refl

peer-seen : seen (party "peer") (party "pong") ping-talk ≡ just (send end (recv end end))
peer-seen = refl

ping-ends : seen (party "peer") (party "pong") ping-talk ≡ just (dual (recv end (send end end)))
ping-ends = other-end (party "pong") (party "peer") ping-talk pong-seen

ping-log : seen (party "log") (party "peer") ping-talk ≡ nothing
ping-log = refl

-- Both arms carry the same message from `b` to `c`, so `a` with `c`
-- is `end`, and `b` with `c` is the send.
both-arms : Talk
both-arms =
  say (party "a") (party "b")
    (say (party "b") (party "c") over over)
    (say (party "b") (party "c") over over)

arms-ab : seen (party "a") (party "b") both-arms ≡ just (send end end)
arms-ab = refl

arms-bc : seen (party "b") (party "c") both-arms ≡ just (send end end)
arms-bc = refl

arms-ac : seen (party "a") (party "c") both-arms ≡ just end
arms-ac = refl

-- One arm is silence and the other is a message, so `b` with `c`
-- has no session.
one-arm : Talk
one-arm =
  say (party "a") (party "b") over
    (say (party "b") (party "c") over over)

one-arm-bc : seen (party "b") (party "c") one-arm ≡ nothing
one-arm-bc = refl

-- Choosing `b0` finishes. Choosing `b1` sends `b0`.
arm : Talk
arm =
  offer (party "a") (party "b") over
    (say (party "a") (party "b") over over)

arm-a : seen (party "a") (party "b") arm ≡ just (choose end (send end end))
arm-a = refl

arm-b : seen (party "b") (party "a") arm ≡ just (branch end (recv end end))
arm-b = refl

arm-log : seen (party "log") (party "a") arm ≡ nothing
arm-log = refl

-- A party does not talk to itself.
self : Talk
self = say (party "a") (party "a") over over

self-ab : seen (party "a") (party "b") self ≡ nothing
self-ab = refl

------------------------------------------------------------------------
-- The other end of a session. One channel has two ends. Sending
-- here is receiving there. Choosing here is offering there. The
-- payload type stays the payload type, and the continuation
-- dualises. The other end of the other end is the same protocol.
--
-- The other end is spec. A run term has no seat. The mark stays
-- the session's mark. None of these constructors is added to Tm
-- or PTm. The Elixir checker follows this form of `dual`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Dual where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Muro.Base using (Mode; spec; run)
open import Muro.Session hiding (¬_; Seat; no-run; ping)

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- `send` swaps with `recv`. `choose` swaps with `branch`. `end`
-- stays `end`. The payload type stays. The continuation dualises.
------------------------------------------------------------------------

dual : Proto → Proto
dual end = end
dual (send A S) = recv A (dual S)
dual (recv A S) = send A (dual S)
dual (choose S T) = branch (dual S) (dual T)
dual (branch S T) = choose (dual S) (dual T)

dual-invol : ∀ S → dual (dual S) ≡ S
dual-invol end = refl
dual-invol (send A S) = cong (send A) (dual-invol S)
dual-invol (recv A S) = cong (recv A) (dual-invol S)
dual-invol (choose S T) = cong₂ choose (dual-invol S) (dual-invol T)
dual-invol (branch S T) = cong₂ branch (dual-invol S) (dual-invol T)

------------------------------------------------------------------------
-- The wall. The other end is a protocol, so it sits at spec.
------------------------------------------------------------------------

data Seat : Mode → Set where
  other : Proto → Seat spec

no-run : ¬ Seat run
no-run ()

------------------------------------------------------------------------
-- `ping` receives a nat and then sends a nat. The other end sends
-- a nat and then receives a nat. The payload type is the same type.
-- Sending a tuple where the protocol says nat has no derivation.
------------------------------------------------------------------------

ping : Proto
ping = recv nat (send nat end)

ping-other : dual ping ≡ send nat (recv nat end)
ping-other = refl

ping-back : dual (dual ping) ≡ ping
ping-back = refl

peer : Proc
peer = put nat two (get nat done)

peer-ok : Conforms peer (dual ping)
peer-ok = put-ok (get-ok done-end)

early : ¬ Conforms (put box here done) (dual ping)
early ()

-- Abandonment still has a derivation at the other end.
peer-stop : Conforms stop (dual ping)
peer-stop = abandon

------------------------------------------------------------------------
-- Choosing swaps with offering. The payload type stays.
------------------------------------------------------------------------

choice : Proto
choice = choose end (send box end)

choice-other : dual choice ≡ branch end (recv box end)
choice-other = refl

offered : Conforms (cover done (get box done)) (dual choice)
offered = cover-ok done-end (get-ok done-end)

not-pick : ¬ Conforms (pick0 done) (dual choice)
not-pick ()

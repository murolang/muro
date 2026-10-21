------------------------------------------------------------------------
-- The other end of a session. One channel has two ends. Sending
-- here is receiving there. Choosing here is offering there. The
-- bit stays the bit: each continuation dualises, and the selector
-- does not. The other end of the other end is the same protocol.
--
-- The other end is spec. A run term has no seat. The mark stays
-- the session's mark. None of these constructors is added to Tm
-- or PTm. The Elixir checker follows `dual`: `session name := dual
-- name`. An omitted mark is the named session's mark.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Dual where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Muro.Base using (Mode; spec; run)
open import Muro.Session hiding (¬_; Seat; no-run; ping)

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- `send` swaps with `recv`. `choose` swaps with `branch`. `end`
-- stays `end`. Both continuations dualise.
------------------------------------------------------------------------

dual : Proto → Proto
dual end = end
dual (send S T) = recv (dual S) (dual T)
dual (recv S T) = send (dual S) (dual T)
dual (choose S T) = branch (dual S) (dual T)
dual (branch S T) = choose (dual S) (dual T)

dual-invol : ∀ S → dual (dual S) ≡ S
dual-invol end = refl
dual-invol (send S T) = cong₂ send (dual-invol S) (dual-invol T)
dual-invol (recv S T) = cong₂ recv (dual-invol S) (dual-invol T)
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
-- `ping` receives `b1` and then sends `b0`. The other end sends
-- `b1` and then receives `b0`. Sending `b1` and finishing has no
-- derivation there: that bit's continuation is a receive.
------------------------------------------------------------------------

ping : Proto
ping = recv end (send end end)

ping-other : dual ping ≡ send end (recv end end)
ping-other = refl

ping-back : dual (dual ping) ≡ ping
ping-back = refl

peer : Proc
peer = put b1 (get b0 done)

peer-ok : Conforms peer (dual ping)
peer-ok = put1 (get0 done-end)

early : ¬ Conforms (put b1 done) (dual ping)
early (put1 ())

-- Abandonment still has a derivation at the other end.
peer-stop : Conforms stop (dual ping)
peer-stop = abandon

------------------------------------------------------------------------
-- Choosing swaps with offering. The bit stays the selector.
------------------------------------------------------------------------

choice : Proto
choice = choose end (send end end)

choice-other : dual choice ≡ branch end (recv end end)
choice-other = refl

offered : Conforms (cover done (get b0 done)) (dual choice)
offered = cover-ok done-end (get0 done-end)

not-pick : ¬ Conforms (pick0 done) (dual choice)
not-pick ()

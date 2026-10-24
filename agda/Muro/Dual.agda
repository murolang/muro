------------------------------------------------------------------------
-- The other end of a session. One channel has two ends. Sending
-- here is receiving there. Choosing here is offering there. The
-- payload type stays the payload type, and the continuation
-- dualises. A dependent receive is a dependent send of the same
-- type. An evidence payload keeps its bound: the sender owes the
-- evidence and the receiver gets the nat. The other end of the other
-- end is the same protocol.
--
-- The other end is spec. A run term has no seat. The mark stays
-- the session's mark. None of these constructors is added to Tm
-- or PTm. The Elixir checker follows this form of `dual`.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Dual where

open import Data.Empty using (⊥)
open import Data.List.Base using ([])
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
dual (dsend x A S) = drecv x A (dual S)
dual (drecv x A S) = dsend x A (dual S)
dual (esend x e S) = erecv x e (dual S)
dual (erecv x e S) = esend x e (dual S)
dual (choose S T) = branch (dual S) (dual T)
dual (branch S T) = choose (dual S) (dual T)

dual-invol : ∀ S → dual (dual S) ≡ S
dual-invol end = refl
dual-invol (send A S) = cong (send A) (dual-invol S)
dual-invol (recv A S) = cong (recv A) (dual-invol S)
dual-invol (dsend x A S) = cong (dsend x A) (dual-invol S)
dual-invol (drecv x A S) = cong (drecv x A) (dual-invol S)
dual-invol (esend x e S) = cong (esend x e) (dual-invol S)
dual-invol (erecv x e S) = cong (erecv x e) (dual-invol S)
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

-- The dual of a dependent receive is a dependent send of the same type.
sized-other : dual sized ≡ dsend "n" nat (recv (vec nat (nvar "n")) end)
sized-other = refl

sized-back : dual (dual sized) ≡ sized
sized-back = refl

-- The window is sent at the other end, and the data is received as
-- a nat. The bound stays on the protocol. The receiver owes nothing.
window-other : dual window ≡ dsend "w" nat (erecv "d" (nvar "w") end)
window-other = refl

window-back : dual (dual window) ≡ window
window-back = refl

grant : Proc
grant = put nat (lit (num 8)) (get nat "d" done)

grant-ok : Conforms [] grant (dual window)
grant-ok = dput-ok refl lit-ok (eget-ok done-end)

-- The receiver gets a nat, not a bit.
grant-bit : ¬ Conforms [] (put nat (lit (num 8)) (get bit "d" done)) (dual window)
grant-bit (dput-ok refl _ ())

peer : Proc
peer = put nat (lit two) (get nat "x" done)

peer-ok : Conforms [] peer (dual ping)
peer-ok = put-ok refl lit-ok (get-ok refl done-end)

early : ¬ Conforms [] (put box (lit v-here) done) (dual ping)
early (put-ok () _ _)

-- Abandonment still has a derivation at the other end.
peer-stop : Conforms [] stop (dual ping)
peer-stop = abandon

------------------------------------------------------------------------
-- Choosing swaps with offering. The payload type stays.
------------------------------------------------------------------------

choice : Proto
choice = choose end (send box end)

choice-other : dual choice ≡ branch end (recv box end)
choice-other = refl

offered : Conforms [] (cover done (get box "x" done)) (dual choice)
offered = cover-ok done-end (get-ok refl done-end)

not-pick : ¬ Conforms [] (pick0 done) (dual choice)
not-pick ()

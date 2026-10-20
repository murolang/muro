------------------------------------------------------------------------
-- Affine sessions. One channel. The payload is a bit, and the
-- continuation depends on which bit was communicated.
--
-- A protocol is spec. A conformance derivation is evidence. Neither
-- is a run. `stop` abandons the channel at any protocol. A second
-- action the protocol does not name has no derivation. Linearity is
-- not in this judgment: abandonment is conformance, not an error.
--
-- This is not a source syntax. None of these constructors is added
-- to Tm or PTm. The Elixir checker does not decide this judgment.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Session where

open import Data.Empty using (⊥)

open import Muro.Base using (Mode; spec; evid; run)

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- A bit is the whole payload. Each communication names both
-- continuations, one per bit.
------------------------------------------------------------------------

data Bit : Set where
  b0 : Bit
  b1 : Bit

data Proto : Set where
  end    : Proto
  send   : Proto → Proto → Proto
  recv   : Proto → Proto → Proto
  choose : Proto → Proto → Proto
  branch : Proto → Proto → Proto

protoMode : Mode
protoMode = spec

------------------------------------------------------------------------
-- The process is the run's actions on the channel.
-- `put` and `get` communicate a bit. `pick0` and `pick1` are the
-- process's choice. `cover` offers both branches of the other
-- side's choice. `stop` uses the channel no further.
------------------------------------------------------------------------

data Proc : Set where
  done  : Proc
  stop  : Proc
  put   : Bit → Proc → Proc
  get   : Bit → Proc → Proc
  pick0 : Proc → Proc
  pick1 : Proc → Proc
  cover : Proc → Proc → Proc

data Conforms : Proc → Proto → Set where
  done-end : Conforms done end

  abandon : ∀ {S} → Conforms stop S

  put0 : ∀ {P S T} → Conforms P S → Conforms (put b0 P) (send S T)
  put1 : ∀ {P S T} → Conforms P T → Conforms (put b1 P) (send S T)

  get0 : ∀ {P S T} → Conforms P S → Conforms (get b0 P) (recv S T)
  get1 : ∀ {P S T} → Conforms P T → Conforms (get b1 P) (recv S T)

  pick0-ok : ∀ {P S T} → Conforms P S → Conforms (pick0 P) (choose S T)
  pick1-ok : ∀ {P S T} → Conforms P T → Conforms (pick1 P) (choose S T)

  cover-ok : ∀ {P Q S T} → Conforms P S → Conforms Q T → Conforms (cover P Q) (branch S T)

conformMode : Mode
conformMode = evid

------------------------------------------------------------------------
-- The wall, inside this judgment. A protocol sits at spec. A
-- conformance derivation sits at evidence. Run has neither.
------------------------------------------------------------------------

data Seat : Mode → Set where
  protocol : Proto → Seat spec
  conforms : ∀ {P S} → Conforms P S → Seat evid

no-run : ¬ Seat run
no-run ()

------------------------------------------------------------------------
-- Examples. The continuation after b0 is not the continuation after b1.
------------------------------------------------------------------------

ping : Proto
ping = recv end (send end end)

pong : Proc
pong = get b1 (put b0 done)

pong-ok : Conforms pong ping
pong-ok = get1 (put0 done-end)

-- Received b0, whose continuation is end, and then sent.
early-send : ¬ Conforms (get b0 (put b0 done)) ping
early-send (get0 ())

-- Two sends where the first bit's continuation is end.
twice : ¬ Conforms (put b0 (put b1 done)) (send end end)
twice (put0 ())

-- A send where the protocol says receive.
swapped : ¬ Conforms (put b0 done) (recv end end)
swapped ()

-- The channel is used once and then abandoned. Affine, not linear.
left-open : Conforms (put b0 stop) (send (send end end) end)
left-open = put0 abandon

-- Abandoned before any action.
untouched : Conforms stop (send end end)
untouched = abandon

chosen : Conforms (pick0 done) (choose end (send end end))
chosen = pick0-ok done-end

both : Conforms (cover done (put b0 done)) (branch end (send end end))
both = cover-ok done-end (put0 done-end)

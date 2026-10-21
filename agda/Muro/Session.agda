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
-- to Tm or PTm. `decide` searches for a derivation. The Elixir
-- checker follows that search for `session` and `conform`.
-- `skel` is that process as actions. `--backend otp` follows `skel`.
-- The BEAM runs the server. The proof stops at the derivation.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Session where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

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

------------------------------------------------------------------------
-- The search. `yes` carries a derivation. `no` carries its refutation.
-- The Elixir checker follows these clauses.
------------------------------------------------------------------------

data Answer (P : Proc) (S : Proto) : Set where
  yes : Conforms P S → Answer P S
  no  : ¬ Conforms P S → Answer P S

on0 : ∀ {P S T} → Answer P S → Answer (put b0 P) (send S T)
on0 (yes d) = yes (put0 d)
on0 (no nd) = no (λ { (put0 d) → nd d })

on1 : ∀ {P S T} → Answer P T → Answer (put b1 P) (send S T)
on1 (yes d) = yes (put1 d)
on1 (no nd) = no (λ { (put1 d) → nd d })

in0 : ∀ {P S T} → Answer P S → Answer (get b0 P) (recv S T)
in0 (yes d) = yes (get0 d)
in0 (no nd) = no (λ { (get0 d) → nd d })

in1 : ∀ {P S T} → Answer P T → Answer (get b1 P) (recv S T)
in1 (yes d) = yes (get1 d)
in1 (no nd) = no (λ { (get1 d) → nd d })

at0 : ∀ {P S T} → Answer P S → Answer (pick0 P) (choose S T)
at0 (yes d) = yes (pick0-ok d)
at0 (no nd) = no (λ { (pick0-ok d) → nd d })

at1 : ∀ {P S T} → Answer P T → Answer (pick1 P) (choose S T)
at1 (yes d) = yes (pick1-ok d)
at1 (no nd) = no (λ { (pick1-ok d) → nd d })

both-of : ∀ {P Q S T} → Answer P S → Answer Q T → Answer (cover P Q) (branch S T)
both-of (yes d) (yes e) = yes (cover-ok d e)
both-of (no nd) _ = no (λ { (cover-ok d _) → nd d })
both-of (yes _) (no nd) = no (λ { (cover-ok _ e) → nd e })

decide : (P : Proc) (S : Proto) → Answer P S
decide done end = yes done-end
decide done (send _ _) = no (λ ())
decide done (recv _ _) = no (λ ())
decide done (choose _ _) = no (λ ())
decide done (branch _ _) = no (λ ())
decide stop _ = yes abandon
decide (put b0 P) (send S _) = on0 (decide P S)
decide (put b0 _) end = no (λ ())
decide (put b0 _) (recv _ _) = no (λ ())
decide (put b0 _) (choose _ _) = no (λ ())
decide (put b0 _) (branch _ _) = no (λ ())
decide (put b1 P) (send _ T) = on1 (decide P T)
decide (put b1 _) end = no (λ ())
decide (put b1 _) (recv _ _) = no (λ ())
decide (put b1 _) (choose _ _) = no (λ ())
decide (put b1 _) (branch _ _) = no (λ ())
decide (get b0 P) (recv S _) = in0 (decide P S)
decide (get b0 _) end = no (λ ())
decide (get b0 _) (send _ _) = no (λ ())
decide (get b0 _) (choose _ _) = no (λ ())
decide (get b0 _) (branch _ _) = no (λ ())
decide (get b1 P) (recv _ T) = in1 (decide P T)
decide (get b1 _) end = no (λ ())
decide (get b1 _) (send _ _) = no (λ ())
decide (get b1 _) (choose _ _) = no (λ ())
decide (get b1 _) (branch _ _) = no (λ ())
decide (pick0 P) (choose S _) = at0 (decide P S)
decide (pick0 _) end = no (λ ())
decide (pick0 _) (send _ _) = no (λ ())
decide (pick0 _) (recv _ _) = no (λ ())
decide (pick0 _) (branch _ _) = no (λ ())
decide (pick1 P) (choose _ T) = at1 (decide P T)
decide (pick1 _) end = no (λ ())
decide (pick1 _) (send _ _) = no (λ ())
decide (pick1 _) (recv _ _) = no (λ ())
decide (pick1 _) (branch _ _) = no (λ ())
decide (cover P Q) (branch S T) = both-of (decide P S) (decide Q T)
decide (cover _ _) end = no (λ ())
decide (cover _ _) (send _ _) = no (λ ())
decide (cover _ _) (recv _ _) = no (λ ())
decide (cover _ _) (choose _ _) = no (λ ())

pong-decides : decide pong ping ≡ yes pong-ok
pong-decides = refl

left-open-decides : decide (put b0 stop) (send (send end end) end) ≡ yes left-open
left-open-decides = refl

untouched-decides : decide stop (send end end) ≡ yes untouched
untouched-decides = refl

chosen-decides : decide (pick0 done) (choose end (send end end)) ≡ yes chosen
chosen-decides = refl

both-decides : decide (cover done (put b0 done)) (branch end (send end end)) ≡ yes both
both-decides = refl

------------------------------------------------------------------------
-- The actions a process takes. `say` and `hear` are a bit. `choose`
-- is the process's choice. `offer` is both arms of the other side's
-- choice. `leave` abandons the channel. `finish` closes it.
------------------------------------------------------------------------

data Skel : Set where
  finish : Skel
  leave  : Skel
  say    : Bit → Skel → Skel
  hear   : Bit → Skel → Skel
  choose : Bit → Skel → Skel
  offer  : Skel → Skel → Skel

skel : Proc → Skel
skel done = finish
skel stop = leave
skel (put b P) = say b (skel P)
skel (get b P) = hear b (skel P)
skel (pick0 P) = choose b0 (skel P)
skel (pick1 P) = choose b1 (skel P)
skel (cover P Q) = offer (skel P) (skel Q)

pong-skel : skel pong ≡ hear b1 (say b0 finish)
pong-skel = refl

left-open-skel : skel (put b0 stop) ≡ say b0 leave
left-open-skel = refl

untouched-skel : skel stop ≡ leave
untouched-skel = refl

chosen-skel : skel (pick0 done) ≡ choose b0 finish
chosen-skel = refl

both-skel : skel (cover done (put b0 done)) ≡ offer finish (say b0 finish)
both-skel = refl

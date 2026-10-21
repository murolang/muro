------------------------------------------------------------------------
-- Affine sessions. One channel. The payload is a bit, and the
-- continuation depends on which bit was communicated.
--
-- A protocol is spec. A conformance derivation is evidence. Neither
-- is a run. `stop` abandons the channel at any protocol. A second
-- action the protocol does not name has no derivation.
--
-- `%0`, and an unmarked session, is this conformance: abandonment
-- is allowed. `%1` asks for `Ends` as well. The process finishes
-- at `done`, and `stop` has no derivation of `Ends`. Both marks
-- are the affine quantity. Neither is a new constructor of Qty.
--
-- This is not a source syntax. None of these constructors is added
-- to Tm or PTm. `decide` searches for a derivation. `finishes`
-- decides `Ends`. The Elixir checker follows both. `skel` is the
-- process as actions. `--backend otp` follows `skel`. The BEAM
-- runs the server. The proof stops at the derivation.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Session where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (Mode; spec; evid; run; Qty; affine)

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

------------------------------------------------------------------------
-- Finishing. `done` at every leaf. `stop` has no constructor, so an
-- abandoned channel does not finish. The Elixir checker follows
-- `finishes` when the session is `%1`.
------------------------------------------------------------------------

data Ends : Proc → Set where
  ends-done  : Ends done
  ends-put   : ∀ {b P} → Ends P → Ends (put b P)
  ends-get   : ∀ {b P} → Ends P → Ends (get b P)
  ends-pick0 : ∀ {P} → Ends P → Ends (pick0 P)
  ends-pick1 : ∀ {P} → Ends P → Ends (pick1 P)
  ends-cover : ∀ {P Q} → Ends P → Ends Q → Ends (cover P Q)

data Finish (P : Proc) : Set where
  ends   : Ends P → Finish P
  leaves : ¬ Ends P → Finish P

step-put : ∀ {b P} → Finish P → Finish (put b P)
step-put (ends d) = ends (ends-put d)
step-put (leaves nd) = leaves (λ { (ends-put d) → nd d })

step-get : ∀ {b P} → Finish P → Finish (get b P)
step-get (ends d) = ends (ends-get d)
step-get (leaves nd) = leaves (λ { (ends-get d) → nd d })

step-pick0 : ∀ {P} → Finish P → Finish (pick0 P)
step-pick0 (ends d) = ends (ends-pick0 d)
step-pick0 (leaves nd) = leaves (λ { (ends-pick0 d) → nd d })

step-pick1 : ∀ {P} → Finish P → Finish (pick1 P)
step-pick1 (ends d) = ends (ends-pick1 d)
step-pick1 (leaves nd) = leaves (λ { (ends-pick1 d) → nd d })

step-cover : ∀ {P Q} → Finish P → Finish Q → Finish (cover P Q)
step-cover (ends d) (ends e) = ends (ends-cover d e)
step-cover (leaves nd) _ = leaves (λ { (ends-cover d _) → nd d })
step-cover (ends _) (leaves nd) = leaves (λ { (ends-cover _ e) → nd e })

finishes : (P : Proc) → Finish P
finishes done = ends ends-done
finishes stop = leaves (λ ())
finishes (put _ P) = step-put (finishes P)
finishes (get _ P) = step-get (finishes P)
finishes (pick0 P) = step-pick0 (finishes P)
finishes (pick1 P) = step-pick1 (finishes P)
finishes (cover P Q) = step-cover (finishes P) (finishes Q)

pong-finishes : finishes pong ≡ ends (ends-get (ends-put ends-done))
pong-finishes = refl

stop-finishes : finishes stop ≡ leaves (λ ())
stop-finishes = refl

left-open-finishes : finishes (put b0 stop) ≡ step-put (leaves (λ ()))
left-open-finishes = refl

chosen-finishes : finishes (pick0 done) ≡ ends (ends-pick0 ends-done)
chosen-finishes = refl

both-finishes :
  finishes (cover done (put b0 done)) ≡ ends (ends-cover ends-done (ends-put ends-done))
both-finishes = refl

¬ends-stop : ¬ Ends stop
¬ends-stop ()

¬ends-left-open : ¬ Ends (put b0 stop)
¬ends-left-open (ends-put ())

------------------------------------------------------------------------
-- `%0` and `%1` name the same arrow quantity. The linear mark is
-- `Ends`, not a fourth constructor of Qty. An unmarked session is `%0`.
------------------------------------------------------------------------

data Mark : Set where
  aff : Mark
  lin : Mark

qty : Mark → Qty
qty aff = affine
qty lin = affine

same-qty : qty aff ≡ qty lin
same-qty = refl

-- A `%1` conformance is an affine conformance that also finishes.
-- `lin-aff` is `%1` implies `%0`.
record Linear (P : Proc) (S : Proto) : Set where
  constructor linear
  field
    held   : Conforms P S
    closed : Ends P

lin-aff : ∀ {P S} → Linear P S → Conforms P S
lin-aff = Linear.held

pong-linear : Linear pong ping
pong-linear = linear pong-ok (ends-get (ends-put ends-done))

------------------------------------------------------------------------
-- A process that finishes has no `leave` in the skeleton `--backend otp`
-- follows. `stop` is the only way to `leave`, and `Ends` has no `stop`.
------------------------------------------------------------------------

data NoLeave : Skel → Set where
  finish-ok : NoLeave finish
  say-ok    : ∀ {b k} → NoLeave k → NoLeave (say b k)
  hear-ok   : ∀ {b k} → NoLeave k → NoLeave (hear b k)
  choose-ok : ∀ {b k} → NoLeave k → NoLeave (choose b k)
  offer-ok  : ∀ {k q} → NoLeave k → NoLeave q → NoLeave (offer k q)

ends-no-leave : ∀ {P} → Ends P → NoLeave (skel P)
ends-no-leave ends-done = finish-ok
ends-no-leave (ends-put e) = say-ok (ends-no-leave e)
ends-no-leave (ends-get e) = hear-ok (ends-no-leave e)
ends-no-leave (ends-pick0 e) = choose-ok (ends-no-leave e)
ends-no-leave (ends-pick1 e) = choose-ok (ends-no-leave e)
ends-no-leave (ends-cover e f) = offer-ok (ends-no-leave e) (ends-no-leave f)

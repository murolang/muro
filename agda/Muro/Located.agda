------------------------------------------------------------------------
-- A session at a place. The endpoint is a protocol and a scheme.
-- Spec holds that endpoint. Evidence is a conformance together with
-- the move that reads the scheme.
--
-- Reading the scheme where it sits stays. Reading it at another
-- place crosses once. A polymorphic scheme stays wherever it is
-- read. `%0` is the affine session: abandonment has a derivation.
-- `%1` also finishes, and `stop` has none. The boundary is the
-- move. The bit stays on the session. A wrong bit has no derivation
-- at any place.
--
-- Neither mark is a constructor of Qty. This is not a source syntax.
-- None of these constructors is added to Tm or PTm. The Elixir
-- checker follows this sitting: `endpoint` names the session and the
-- scheme, and `read` states stay or cross. The run emitters omit
-- both. `--node` follows a cross reading with one call. The message
-- is the read of the scheme. The bit stays on the session. A stay
-- emits no call. `--backend otp` follows the process. The server
-- talks to one peer. The place stays on the reading.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Located where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (Mode; spec; evid; run)
open import Muro.Session hiding (¬_; Seat; no-run; conforms; decide)
open import Muro.Place hiding (¬_; Seat; no-run; conforms; boundary)

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- The endpoint. `aff` may abandon. `lin` must finish. Both marks are
-- the affine quantity. The scheme is the place: `fixed` names one,
-- `any` is read where it is used.
------------------------------------------------------------------------

data Endpoint : Set where
  endpoint : Mark → Proto → Scheme → Endpoint

------------------------------------------------------------------------
-- Evidence. The conformance is the bits. The move is the boundary.
-- There is no constructor that carries a bit on the move, and none
-- that adds a second boundary.
------------------------------------------------------------------------

data Sits : Proc → Endpoint → Place → Set where
  held : ∀ {P S s q} →
    Conforms P S →
    Move (ground s q) q →
    Sits P (endpoint aff S s) q
  finished : ∀ {P S s q} →
    Linear P S →
    Move (ground s q) q →
    Sits P (endpoint lin S s) q

boundary : ∀ {P E q} → Sits P E q → Bounds
boundary (held _ m) = bounds m
boundary (finished _ m) = bounds m

------------------------------------------------------------------------
-- `ping` at the ambient place. `pong` reads it there, and at a node.
------------------------------------------------------------------------

pong-home : Sits pong (endpoint aff ping (fixed ambient)) ambient
pong-home = held pong-ok (conform (fixed ambient) ambient)

pong-away : Sits pong (endpoint aff ping (fixed ambient)) (node "a")
pong-away = held pong-ok (conform (fixed ambient) (node "a"))

pong-poly : Sits pong (endpoint aff ping any) (node "a")
pong-poly = held pong-ok (conform any (node "a"))

pong-done-away : Sits pong (endpoint lin ping (fixed ambient)) (node "a")
pong-done-away = finished pong-linear (conform (fixed ambient) (node "a"))

-- Abandonment is allowed for `%0`, and the reading still crosses once.
open-away : Sits (put b0 stop) (endpoint aff (send (send end end) end) (fixed ambient)) (node "a")
open-away = held left-open (conform (fixed ambient) (node "a"))

sits-home : boundary pong-home ≡ none
sits-home = refl

sits-away : boundary pong-away ≡ one
sits-away = refl

sits-poly : boundary pong-poly ≡ none
sits-poly = refl

sits-done : boundary pong-done-away ≡ one
sits-done = refl

sits-open : boundary open-away ≡ one
sits-open = refl

-- The bits at home are the bits at the node.
bits-of : ∀ {P S s q} → Sits P (endpoint aff S s) q → Conforms P S
bits-of (held d _) = d

same-bits : bits-of pong-home ≡ bits-of pong-away
same-bits = refl

------------------------------------------------------------------------
-- A wrong bit is refused at every scheme and every reading place.
-- `%1` refuses abandonment the same way. The place does not excuse
-- either.
------------------------------------------------------------------------

early : Proc
early = get b0 (put b0 done)

early-any : ∀ {s q} → ¬ Sits early (endpoint aff ping s) q
early-any (held (get0 ()) _)

early-lin-any : ∀ {s q} → ¬ Sits early (endpoint lin ping s) q
early-lin-any (finished (linear (get0 ()) _) _)

abandon-any : ∀ {s q} →
  ¬ Sits (put b0 stop) (endpoint lin (send (send end end) end) s) q
abandon-any (finished l _) = ¬ends-left-open (Linear.closed l)

------------------------------------------------------------------------
-- The wall. Spec holds the endpoint. Evidence holds the sitting.
-- Run has no constructor.
------------------------------------------------------------------------

data Seat : Mode → Set where
  located : Endpoint → Seat spec
  read    : ∀ {P E q} → Sits P E q → Seat evid

no-run : ¬ Seat run
no-run ()

home-spec : Seat spec
home-spec = located (endpoint aff ping (fixed ambient))

home-evid : Seat evid
home-evid = read pong-home

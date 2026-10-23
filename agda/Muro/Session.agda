------------------------------------------------------------------------
-- Affine sessions. One channel. A communication carries a payload
-- and one continuation. The payload is a run type in this fragment:
-- a nat, a bit, unit, a pair, or a record of named fields. A pair
-- is a tuple. A record is a fixed map: the names are the type, and
-- a pair around a record is a tuple wrapping that map. An open map,
-- whose keys are chosen at run time, is not a type. The `get`
-- continuation is a function of the received value.
--
-- `send A S` sends a value of type A and continues as S. `recv A S`
-- receives one. Any value of that type conforms. `choose` and
-- `branch` select an arm. Two processes meet when the sent type is
-- the received type.
--
-- A protocol is spec. A conformance derivation is evidence. Neither
-- is a run. `stop` abandons the channel at any protocol. A second
-- action the protocol does not name has no derivation. A value of
-- the wrong type has none.
--
-- `%0`, and an unmarked session, is this conformance: abandonment
-- is allowed. `%1` asks for `Ends` as well. The process finishes
-- at `done`, and `stop` has no derivation of `Ends`. Both marks
-- are the affine quantity. Neither is a new constructor of Qty.
--
-- This is not a source syntax. None of these constructors is added
-- to Tm or PTm. `decide` searches for a derivation. `finishes`
-- decides `Ends`. The Elixir checker follows this judgment. `skel`
-- carries the value on `say` and the type on `hear`. The OTP image
-- exchanges that value. The other emitters do not implement the
-- meeting.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Session where

open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable.Core using (Dec)
open import Relation.Nullary.Decidable.Core using () renaming (yes to yes′; no to no′)

open import Muro.Base using (Mode; spec; evid; run; Qty; affine)

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- The payload types. `pair` is a tuple. `rec` is a fixed map, one
-- named field after another. The names are part of the type.
------------------------------------------------------------------------

data Ty : Set
data Fields : Set

data Fields where
  noFields : Fields
  named    : String → Ty → Fields → Fields

data Ty where
  nat  : Ty
  bit  : Ty
  unit : Ty
  pair : Ty → Ty → Ty
  rec  : Fields → Ty

data Row : Fields → Set
data Val : Ty → Set

data Row where
  noRow : Row noFields
  cell  : ∀ {n A fs} → Val A → Row fs → Row (named n A fs)

data Val where
  zero : Val nat
  suc  : Val nat → Val nat
  b0   : Val bit
  b1   : Val bit
  tt   : Val unit
  tup  : ∀ {A B} → Val A → Val B → Val (pair A B)
  rec  : ∀ {fs} → Row fs → Val (rec fs)

------------------------------------------------------------------------
-- Value expressions: literals or variable references
------------------------------------------------------------------------

data ValExpr : Ty → Set where
  lit : ∀ {A} → Val A → ValExpr A
  var : ∀ {A} → String → ValExpr A

mutual
  fields≟ : (fs gs : Fields) → Dec (fs ≡ gs)
  fields≟ noFields noFields = yes′ refl
  fields≟ noFields (named _ _ _) = no′ (λ ())
  fields≟ (named _ _ _) noFields = no′ (λ ())
  fields≟ (named n A fs) (named m B gs) with n ≟ m
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl with ty≟ A B
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl with fields≟ fs gs
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl

  ty≟ : (A B : Ty) → Dec (A ≡ B)
  ty≟ nat nat = yes′ refl
  ty≟ nat bit = no′ (λ ())
  ty≟ nat unit = no′ (λ ())
  ty≟ nat (pair _ _) = no′ (λ ())
  ty≟ nat (rec _) = no′ (λ ())
  ty≟ bit nat = no′ (λ ())
  ty≟ bit bit = yes′ refl
  ty≟ bit unit = no′ (λ ())
  ty≟ bit (pair _ _) = no′ (λ ())
  ty≟ bit (rec _) = no′ (λ ())
  ty≟ unit nat = no′ (λ ())
  ty≟ unit bit = no′ (λ ())
  ty≟ unit unit = yes′ refl
  ty≟ unit (pair _ _) = no′ (λ ())
  ty≟ unit (rec _) = no′ (λ ())
  ty≟ (pair _ _) nat = no′ (λ ())
  ty≟ (pair _ _) bit = no′ (λ ())
  ty≟ (pair _ _) unit = no′ (λ ())
  ty≟ (pair A B) (pair C D) with ty≟ A C
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl with ty≟ B D
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl
  ty≟ (pair _ _) (rec _) = no′ (λ ())
  ty≟ (rec _) nat = no′ (λ ())
  ty≟ (rec _) bit = no′ (λ ())
  ty≟ (rec _) unit = no′ (λ ())
  ty≟ (rec _) (pair _ _) = no′ (λ ())
  ty≟ (rec fs) (rec gs) with fields≟ fs gs
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl

------------------------------------------------------------------------
-- One continuation after the payload. Choice is a separate arm.
------------------------------------------------------------------------

data Proto : Set where
  end    : Proto
  send   : Ty → Proto → Proto
  recv   : Ty → Proto → Proto
  choose : Proto → Proto → Proto
  branch : Proto → Proto → Proto

protoMode : Mode
protoMode = spec

------------------------------------------------------------------------
-- The process is the run's actions on the channel. `put` sends a
-- value expression (literal or variable). `get` receives a value
-- and binds it to a named variable. The continuation may reference
-- that variable. `pick0` and `pick1` are the process's choice.
-- `cover` offers both branches. `stop` uses the channel no further.
------------------------------------------------------------------------

data Proc : Set where
  done  : Proc
  stop  : Proc
  put   : (A : Ty) → ValExpr A → Proc → Proc
  get   : (A : Ty) → String → Proc → Proc
  pick0 : Proc → Proc
  pick1 : Proc → Proc
  cover : Proc → Proc → Proc

------------------------------------------------------------------------
-- Variable context: list of (name, type) pairs
------------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_)

Ctx : Set
Ctx = List (String × Ty)

-- Variable lookup in context. The innermost binding of a name is the
-- one a variable refers to: `there` steps past a binding only when it
-- binds a different name, so a shadowed binding is out of reach. The
-- OTP image keeps the latest value bound to a name, and the Elixir
-- checker looks the name up the same way.
data _∈_∷_ : String → Ctx → Ty → Set where
  here  : ∀ {x A Γ} → x ∈ ((x , A) ∷ Γ) ∷ A
  there : ∀ {x y A B Γ} → x ≢ y → x ∈ Γ ∷ A → x ∈ ((y , B) ∷ Γ) ∷ A

-- Well-scoped value expressions
data ValExprOk : Ctx → ∀ {A} → ValExpr A → Set where
  lit-ok : ∀ {Γ A} {v : Val A} → ValExprOk Γ (lit v)
  var-ok : ∀ {Γ A} {x : String} → x ∈ Γ ∷ A → ValExprOk Γ (var {A} x)

-- Conformance with variable context
data Conforms : Ctx → Proc → Proto → Set where
  done-end : ∀ {Γ} → Conforms Γ done end

  abandon : ∀ {Γ S} → Conforms Γ stop S

  put-ok : ∀ {Γ A v P S} → ValExprOk Γ v → Conforms Γ P S → Conforms Γ (put A v P) (send A S)

  get-ok : ∀ {Γ A x P S} → Conforms ((x , A) ∷ Γ) P S → Conforms Γ (get A x P) (recv A S)

  pick0-ok : ∀ {Γ P S T} → Conforms Γ P S → Conforms Γ (pick0 P) (choose S T)
  pick1-ok : ∀ {Γ P S T} → Conforms Γ P T → Conforms Γ (pick1 P) (choose S T)

  cover-ok : ∀ {Γ P Q S T} → Conforms Γ P S → Conforms Γ Q T → Conforms Γ (cover P Q) (branch S T)

conformMode : Mode
conformMode = evid

------------------------------------------------------------------------
-- The wall, inside this judgment. A protocol sits at spec. A
-- conformance derivation sits at evidence. Run has neither.
------------------------------------------------------------------------

data Seat : Mode → Set where
  protocol : Proto → Seat spec
  conforms : ∀ {Γ P S} → Conforms Γ P S → Seat evid

no-run : ¬ Seat run
no-run ()

------------------------------------------------------------------------
-- A nat, and a tuple wrapping a two-field map. Two values of one
-- type both conform. A value of another type does not.
------------------------------------------------------------------------

one : Val nat
one = suc zero

two : Val nat
two = suc one

point : Fields
point = named "x" nat (named "y" nat noFields)

box : Ty
box = pair bit (rec point)

v-here : Val box
v-here = tup b0 (rec (cell zero (cell zero noRow)))

v-there : Val box
v-there = tup b1 (rec (cell one (cell two noRow)))

ping : Proto
ping = recv nat (send nat end)

pong : Proc
pong = get nat "x" (put nat (lit one) done)

pong-ok : Conforms [] pong ping
pong-ok = get-ok (put-ok lit-ok done-end)

other-nat : Conforms [] (get nat "x" (put nat (lit zero) done)) ping
other-nat = get-ok (put-ok lit-ok done-end)

-- Echo: receive a value and send it back.
echo : Proc
echo = get nat "v" (put nat (var "v") done)

echo-ok : Conforms [] echo ping
echo-ok = get-ok (put-ok (var-ok here) done-end)

v-here-ok : Conforms [] (put box (lit v-here) done) (send box end)
v-here-ok = put-ok lit-ok done-end

v-there-ok : Conforms [] (put box (lit v-there) done) (send box end)
v-there-ok = put-ok lit-ok done-end

not-type : ¬ Conforms [] (put nat (lit zero) done) (send box end)
not-type ()

-- A send where the protocol says receive.
swapped : ¬ Conforms [] (put nat (lit zero) done) (recv nat end)
swapped ()

-- The continuation is end, so a second send has no derivation.
twice : ¬ Conforms [] (put nat (lit zero) (put nat (lit zero) done)) (send nat end)
twice (put-ok _ ())

untouched : Conforms [] stop (send nat end)
untouched = abandon

chosen : Conforms [] (pick0 done) (choose end (send nat end))
chosen = pick0-ok done-end

both : Conforms [] (cover done (put box (lit v-here) done)) (branch end (send box end))
both = cover-ok done-end (put-ok lit-ok done-end)

------------------------------------------------------------------------
-- The search. `yes` carries a derivation. `no` carries its refutation.
-- The Elixir checker follows `decide`.
------------------------------------------------------------------------

data Answer (Γ : Ctx) (P : Proc) (S : Proto) : Set where
  yes : Conforms Γ P S → Answer Γ P S
  no  : ¬ Conforms Γ P S → Answer Γ P S

-- Decidable variable lookup
_∈?_∷?_ : (x : String) (Γ : Ctx) (A : Ty) → Dec (x ∈ Γ ∷ A)
x ∈? [] ∷? A = no′ (λ ())
x ∈? ((y , B) ∷ Γ) ∷? A with x ≟ y
... | yes′ refl with ty≟ A B
... | yes′ refl = yes′ here
... | no′ ¬AB = no′ (λ { here → ¬AB refl ; (there x≢x _) → x≢x refl })
x ∈? ((y , B) ∷ Γ) ∷? A | no′ ¬xy with x ∈? Γ ∷? A
... | yes′ p = yes′ (there ¬xy p)
... | no′ np = no′ (λ { here → ¬xy refl ; (there _ p) → np p })

-- Decide if a value expression is well-scoped
decideValExpr : ∀ {A} (Γ : Ctx) (v : ValExpr A) → Dec (ValExprOk Γ v)
decideValExpr Γ (lit v) = yes′ lit-ok
decideValExpr {A} Γ (var x) with x ∈? Γ ∷? A
... | yes′ p = yes′ (var-ok p)
... | no′ np = no′ (λ { (var-ok p) → np p })

put-type : ∀ {Γ A B v P S} → Conforms Γ (put A v P) (send B S) → A ≡ B
put-type (put-ok _ _) = refl

get-type : ∀ {Γ A B x P S} → Conforms Γ (get A x P) (recv B S) → A ≡ B
get-type (get-ok _) = refl

on-put : ∀ {Γ A B v P S} → Dec (A ≡ B) → Dec (ValExprOk Γ v) → Answer Γ P S → Answer Γ (put A v P) (send B S)
on-put (yes′ refl) (yes′ vok) (yes d) = yes (put-ok vok d)
on-put (yes′ refl) (yes′ vok) (no nd) = no (λ { (put-ok _ d) → nd d })
on-put (yes′ refl) (no′ nvok) _ = no (λ { (put-ok vok _) → nvok vok })
on-put (no′ ¬eq) _ _ = no (λ d → ¬eq (put-type d))

on-get : ∀ {Γ A B x P S} → Dec (A ≡ B) → Answer ((x , A) ∷ Γ) P S → Answer Γ (get A x P) (recv B S)
on-get (yes′ refl) (yes d) = yes (get-ok d)
on-get (yes′ refl) (no nd) = no (λ { (get-ok d) → nd d })
on-get (no′ ¬eq) _ = no (λ d → ¬eq (get-type d))

at0 : ∀ {Γ P S T} → Answer Γ P S → Answer Γ (pick0 P) (choose S T)
at0 (yes d) = yes (pick0-ok d)
at0 (no nd) = no (λ { (pick0-ok d) → nd d })

at1 : ∀ {Γ P S T} → Answer Γ P T → Answer Γ (pick1 P) (choose S T)
at1 (yes d) = yes (pick1-ok d)
at1 (no nd) = no (λ { (pick1-ok d) → nd d })

both-of : ∀ {Γ P Q S T} → Answer Γ P S → Answer Γ Q T → Answer Γ (cover P Q) (branch S T)
both-of (yes d) (yes e) = yes (cover-ok d e)
both-of (no nd) _ = no (λ { (cover-ok d _) → nd d })
both-of (yes _) (no nd) = no (λ { (cover-ok _ e) → nd e })

decide : (Γ : Ctx) (P : Proc) (S : Proto) → Answer Γ P S
decide Γ done end = yes done-end
decide Γ done (send _ _) = no (λ ())
decide Γ done (recv _ _) = no (λ ())
decide Γ done (choose _ _) = no (λ ())
decide Γ done (branch _ _) = no (λ ())
decide Γ stop _ = yes abandon
decide Γ (put A v P) (send B S) = on-put (ty≟ A B) (decideValExpr Γ v) (decide Γ P S)
decide Γ (put _ _ _) end = no (λ ())
decide Γ (put _ _ _) (recv _ _) = no (λ ())
decide Γ (put _ _ _) (choose _ _) = no (λ ())
decide Γ (put _ _ _) (branch _ _) = no (λ ())
decide Γ (get A x P) (recv B S) = on-get (ty≟ A B) (decide ((x , A) ∷ Γ) P S)
decide Γ (get _ _ _) end = no (λ ())
decide Γ (get _ _ _) (send _ _) = no (λ ())
decide Γ (get _ _ _) (choose _ _) = no (λ ())
decide Γ (get _ _ _) (branch _ _) = no (λ ())
decide Γ (pick0 P) (choose S _) = at0 (decide Γ P S)
decide Γ (pick0 _) end = no (λ ())
decide Γ (pick0 _) (send _ _) = no (λ ())
decide Γ (pick0 _) (recv _ _) = no (λ ())
decide Γ (pick0 _) (branch _ _) = no (λ ())
decide Γ (pick1 P) (choose _ T) = at1 (decide Γ P T)
decide Γ (pick1 _) end = no (λ ())
decide Γ (pick1 _) (send _ _) = no (λ ())
decide Γ (pick1 _) (recv _ _) = no (λ ())
decide Γ (pick1 _) (branch _ _) = no (λ ())
decide Γ (cover P Q) (branch S T) = both-of (decide Γ P S) (decide Γ Q T)
decide Γ (cover _ _) end = no (λ ())
decide Γ (cover _ _) (send _ _) = no (λ ())
decide Γ (cover _ _) (recv _ _) = no (λ ())
decide Γ (cover _ _) (choose _ _) = no (λ ())

pong-decides : decide [] pong ping ≡ yes pong-ok
pong-decides = refl

other-nat-decides : decide [] (get nat "x" (put nat (lit zero) done)) ping ≡ yes other-nat
other-nat-decides = refl

v-here-decides : decide [] (put box (lit v-here) done) (send box end) ≡ yes v-here-ok
v-here-decides = refl

v-there-decides : decide [] (put box (lit v-there) done) (send box end) ≡ yes v-there-ok
v-there-decides = refl

-- A name rebound at another type refers to the inner binding. Sending
-- it at the outer binding's type has no derivation, and `decide` says so.
shadowed : Proc
shadowed = get nat "v" (get bit "v" (put nat (var "v") done))

shadowed-refused : ¬ Conforms [] shadowed (recv nat (recv bit (send nat end)))
shadowed-refused (get-ok (get-ok (put-ok (var-ok (there v≢v _)) _))) = v≢v refl

-- The inner binding at its own type conforms.
inner : Conforms [] (get nat "v" (get bit "v" (put bit (var "v") done))) (recv nat (recv bit (send bit end)))
inner = get-ok (get-ok (put-ok (var-ok here) done-end))

inner-decides : decide [] (get nat "v" (get bit "v" (put bit (var "v") done))) (recv nat (recv bit (send bit end))) ≡ yes inner
inner-decides = refl

shadowed-decides : decide [] shadowed (recv nat (recv bit (send nat end))) ≡ no shadowed-refused
shadowed-decides = refl

left-open : Conforms [] (put nat (lit zero) stop) (send nat (send nat end))
left-open = put-ok lit-ok abandon

left-open-decides : decide [] (put nat (lit zero) stop) (send nat (send nat end)) ≡ yes left-open
left-open-decides = refl

untouched-decides : decide [] stop (send nat end) ≡ yes untouched
untouched-decides = refl

chosen-decides : decide [] (pick0 done) (choose end (send nat end)) ≡ yes chosen
chosen-decides = refl

both-decides : decide [] (cover done (put box (lit v-here) done)) (branch end (send box end)) ≡ yes both
both-decides = refl

------------------------------------------------------------------------
-- The actions a process takes. `say` carries the value expression.
-- `hear` carries the type and variable name. `choose0` and `choose1`
-- are the process's choice. `offer` is both arms. `leave` abandons
-- the channel. `finish` closes it.
------------------------------------------------------------------------

data Skel : Set where
  finish  : Skel
  leave   : Skel
  say     : ∀ {A} → ValExpr A → Skel → Skel
  hear    : Ty → String → Skel → Skel
  choose0 : Skel → Skel
  choose1 : Skel → Skel
  offer   : Skel → Skel → Skel

skel : Proc → Skel
skel done = finish
skel stop = leave
skel (put _ v P) = say v (skel P)
skel (get A x P) = hear A x (skel P)
skel (pick0 P) = choose0 (skel P)
skel (pick1 P) = choose1 (skel P)
skel (cover P Q) = offer (skel P) (skel Q)

pong-skel : skel pong ≡ hear nat "x" (say (lit one) finish)
pong-skel = refl

left-open-skel : skel (put nat (lit zero) stop) ≡ say (lit zero) leave
left-open-skel = refl

untouched-skel : skel stop ≡ leave
untouched-skel = refl

chosen-skel : skel (pick0 done) ≡ choose0 finish
chosen-skel = refl

both-skel : skel (cover done (put box (lit v-here) done)) ≡ offer finish (say (lit v-here) finish)
both-skel = refl

------------------------------------------------------------------------
-- Finishing. `done` at every leaf. `stop` has no constructor, so an
-- abandoned channel does not finish. The Elixir checker follows
-- `finishes`.
------------------------------------------------------------------------

data Ends : Proc → Set where
  ends-done  : Ends done
  ends-put   : ∀ {A v P} → Ends P → Ends (put A v P)
  ends-get   : ∀ {A x P} → Ends P → Ends (get A x P)
  ends-pick0 : ∀ {P} → Ends P → Ends (pick0 P)
  ends-pick1 : ∀ {P} → Ends P → Ends (pick1 P)
  ends-cover : ∀ {P Q} → Ends P → Ends Q → Ends (cover P Q)

data Finish (P : Proc) : Set where
  ends   : Ends P → Finish P
  leaves : ¬ Ends P → Finish P

step-put : ∀ {A v P} → Finish P → Finish (put A v P)
step-put (ends d) = ends (ends-put d)
step-put (leaves nd) = leaves (λ { (ends-put d) → nd d })

step-get : ∀ {A x P} → Finish P → Finish (get A x P)
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
finishes (put _ _ P) = step-put (finishes P)
finishes (get _ _ P) = step-get (finishes P)
finishes (pick0 P) = step-pick0 (finishes P)
finishes (pick1 P) = step-pick1 (finishes P)
finishes (cover P Q) = step-cover (finishes P) (finishes Q)

pong-finishes : finishes pong ≡ ends (ends-get (ends-put ends-done))
pong-finishes = refl

stop-finishes : finishes stop ≡ leaves (λ ())
stop-finishes = refl

left-open-finishes : finishes (put nat (lit zero) stop) ≡ step-put (leaves (λ ()))
left-open-finishes = refl

chosen-finishes : finishes (pick0 done) ≡ ends (ends-pick0 ends-done)
chosen-finishes = refl

both-finishes :
  finishes (cover done (put box (lit v-here) done)) ≡ ends (ends-cover ends-done (ends-put ends-done))
both-finishes = refl

¬ends-stop : ¬ Ends stop
¬ends-stop ()

¬ends-left-open : ¬ Ends (put nat (lit zero) stop)
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
    {ctx}  : Ctx
    held   : Conforms ctx P S
    closed : Ends P

lin-aff : ∀ {P S} (l : Linear P S) → Conforms (Linear.ctx l) P S
lin-aff = Linear.held

pong-linear : Linear pong ping
pong-linear = linear pong-ok (ends-get (ends-put ends-done))

------------------------------------------------------------------------
-- A process that finishes has no `leave` in its skeleton. `stop` is
-- the only way to `leave`, and `Ends` has no `stop`.
------------------------------------------------------------------------

data NoLeave : Skel → Set where
  finish-ok  : NoLeave finish
  say-ok     : ∀ {A v k} → NoLeave k → NoLeave (say {A} v k)
  hear-ok    : ∀ {A x k} → NoLeave k → NoLeave (hear A x k)
  choose0-ok : ∀ {k} → NoLeave k → NoLeave (choose0 k)
  choose1-ok : ∀ {k} → NoLeave k → NoLeave (choose1 k)
  offer-ok   : ∀ {k q} → NoLeave k → NoLeave q → NoLeave (offer k q)

ends-no-leave : ∀ {P} → Ends P → NoLeave (skel P)
ends-no-leave ends-done = finish-ok
ends-no-leave (ends-put e) = say-ok (ends-no-leave e)
ends-no-leave (ends-get e) = hear-ok (ends-no-leave e)
ends-no-leave (ends-pick0 e) = choose0-ok (ends-no-leave e)
ends-no-leave (ends-pick1 e) = choose1-ok (ends-no-leave e)
ends-no-leave (ends-cover e f) = offer-ok (ends-no-leave e) (ends-no-leave f)

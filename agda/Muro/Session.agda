------------------------------------------------------------------------
-- Affine sessions. One channel. A communication carries a payload
-- and one continuation. The payload is a run type in this fragment:
-- a nat, a bit, unit, a pair, a record of named fields, or a vector
-- whose length is a numeral or a nat name. A pair is a tuple. A
-- record is a fixed map: the names are the type, and a pair around a
-- record is a tuple wrapping that map. An open map, whose keys are
-- chosen at run time, is not a type.
--
-- `send A S` sends a value of type A and continues as S. `recv A S`
-- receives one. `drecv x A S` binds that value to `x`, and `S` may
-- mention `x` as the length of a vector. `dsend x A S` is the other
-- direction: the value sent for `x` instantiates `S`. A later payload
-- may mention that nat as a length. The action itself does not.
-- `esend x e S` sends a nat `x` with `x ≤ e`, where `e` is a numeral
-- or a nat bound earlier. The process owes that evidence. `erecv x e S`
-- receives such a nat as a nat. The evidence is part of the
-- conformance derivation, not of the process, so `skel` does not
-- carry it. `isend x S T` sends a bit. `b0` continues as `S` and
-- `b1` continues as `T`. `irecv x S T` receives that bit and binds
-- it. The two arms are the index. A nat does not choose an arm, and
-- a variable bit does not select one: the sender writes `b0` or
-- `b1`. `choose` and `branch` select an arm by a label, not by a
-- payload. Two processes meet when the sent type is the type the
-- continuation expects, and an index meets the arm of that same bit.
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
-- to Tm. `decide` searches for a derivation. `finishes`
-- decides `Ends`. The Elixir checker follows this judgment. `skel`
-- carries the value on `say` and the type on `hear`. The OTP image
-- exchanges that value. The other emitters do not implement the
-- meeting.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Session where

open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _≤_; z≤n; s≤s) renaming (zero to nzero; suc to nsuc)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
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
-- `vec A e` is a vector of `A` whose length is a numeral or a name.
------------------------------------------------------------------------

data NExp : Set where
  nlit : ℕ → NExp
  nvar : String → NExp

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
  vec  : Ty → NExp → Ty

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
  rep  : ∀ {A e} → Val A → Val (vec A e)

------------------------------------------------------------------------
-- Value expressions: literals or variable references
------------------------------------------------------------------------

data ValExpr : Ty → Set where
  lit : ∀ {A} → Val A → ValExpr A
  var : ∀ {A} → String → ValExpr A

nexp≟ : (e f : NExp) → Dec (e ≡ f)
nexp≟ (nlit m) (nlit n) with m ≟ℕ n
... | yes′ refl = yes′ refl
... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
nexp≟ (nlit _) (nvar _) = no′ (λ ())
nexp≟ (nvar _) (nlit _) = no′ (λ ())
nexp≟ (nvar x) (nvar y) with x ≟ y
... | yes′ refl = yes′ refl
... | no′ ¬eq = no′ (λ { refl → ¬eq refl })

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
  ty≟ nat (vec _ _) = no′ (λ ())
  ty≟ bit nat = no′ (λ ())
  ty≟ bit bit = yes′ refl
  ty≟ bit unit = no′ (λ ())
  ty≟ bit (pair _ _) = no′ (λ ())
  ty≟ bit (rec _) = no′ (λ ())
  ty≟ bit (vec _ _) = no′ (λ ())
  ty≟ unit nat = no′ (λ ())
  ty≟ unit bit = no′ (λ ())
  ty≟ unit unit = yes′ refl
  ty≟ unit (pair _ _) = no′ (λ ())
  ty≟ unit (rec _) = no′ (λ ())
  ty≟ unit (vec _ _) = no′ (λ ())
  ty≟ (pair _ _) nat = no′ (λ ())
  ty≟ (pair _ _) bit = no′ (λ ())
  ty≟ (pair _ _) unit = no′ (λ ())
  ty≟ (pair A B) (pair C D) with ty≟ A C
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl with ty≟ B D
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl
  ty≟ (pair _ _) (rec _) = no′ (λ ())
  ty≟ (pair _ _) (vec _ _) = no′ (λ ())
  ty≟ (rec _) nat = no′ (λ ())
  ty≟ (rec _) bit = no′ (λ ())
  ty≟ (rec _) unit = no′ (λ ())
  ty≟ (rec _) (pair _ _) = no′ (λ ())
  ty≟ (rec fs) (rec gs) with fields≟ fs gs
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl
  ty≟ (rec _) (vec _ _) = no′ (λ ())
  ty≟ (vec _ _) nat = no′ (λ ())
  ty≟ (vec _ _) bit = no′ (λ ())
  ty≟ (vec _ _) unit = no′ (λ ())
  ty≟ (vec _ _) (pair _ _) = no′ (λ ())
  ty≟ (vec _ _) (rec _) = no′ (λ ())
  ty≟ (vec A e) (vec B f) with ty≟ A B
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl with nexp≟ e f
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl

------------------------------------------------------------------------
-- One continuation after the payload. An indexed bit has two
-- continuations, one for each value. Choice is a separate arm.
------------------------------------------------------------------------

data Proto : Set where
  end    : Proto
  send   : Ty → Proto → Proto
  recv   : Ty → Proto → Proto
  dsend  : String → Ty → Proto → Proto
  drecv  : String → Ty → Proto → Proto
  esend  : String → NExp → Proto → Proto
  erecv  : String → NExp → Proto → Proto
  -- `b0` continues as the first protocol. `b1` continues as the second.
  -- The name is bound at bit in both arms, and it is not a length.
  isend  : String → Proto → Proto → Proto
  irecv  : String → Proto → Proto → Proto
  choose : Proto → Proto → Proto
  branch : Proto → Proto → Proto

protoMode : Mode
protoMode = spec

------------------------------------------------------------------------
-- The process is the run's actions on the channel. `put` sends a
-- value expression (literal or variable). `get` receives a value
-- and binds it to a named variable. The continuation may reference
-- that variable. `pick0` and `pick1` are the process's choice.
-- `cover` offers both branches. `iget x P Q` receives a bit, binds
-- it to `x`, and offers both arms: `b0` continues as `P` and `b1`
-- continues as `Q`. `stop` uses the channel no further.
------------------------------------------------------------------------

data Proc : Set where
  done  : Proc
  stop  : Proc
  put   : (A : Ty) → ValExpr A → Proc → Proc
  get   : (A : Ty) → String → Proc → Proc
  pick0 : Proc → Proc
  pick1 : Proc → Proc
  cover : Proc → Proc → Proc
  iget  : String → Proc → Proc → Proc

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

------------------------------------------------------------------------
-- A received nat instantiates the lengths that name it. `none` is
-- the identity. `bind` is the latest binding of a name, so a later
-- binder of that name hides it. Applying `none` is the protocol.
------------------------------------------------------------------------

data Idx : Set where
  none : Idx
  bind : String → NExp → Idx → Idx

lookupIdx : Idx → String → Maybe NExp
lookupIdx none _ = nothing
lookupIdx (bind y i ρ) x with x ≟ y
... | yes′ _ = just i
... | no′ _ = lookupIdx ρ x

shadow : String → Idx → Idx
shadow _ none = none
shadow x (bind y i ρ) with x ≟ y
... | yes′ _ = shadow x ρ
... | no′ _ = bind y i (shadow x ρ)

-- The protocol binder `y` is the process binder `x` in the continuation.
renameIdx : String → String → Idx → Idx
renameIdx y x ρ = bind y (nvar x) (shadow y ρ)

applyNExp : Idx → NExp → NExp
applyNExp _ (nlit n) = nlit n
applyNExp ρ (nvar x) with lookupIdx ρ x
... | nothing = nvar x
... | just e = e

applyTy : Idx → Ty → Ty
applyFields : Idx → Fields → Fields

applyTy none A = A
applyTy ρ@(bind _ _ _) nat = nat
applyTy ρ@(bind _ _ _) bit = bit
applyTy ρ@(bind _ _ _) unit = unit
applyTy ρ@(bind _ _ _) (pair A B) = pair (applyTy ρ A) (applyTy ρ B)
applyTy ρ@(bind _ _ _) (rec fs) = rec (applyFields ρ fs)
applyTy ρ@(bind _ _ _) (vec A e) = vec (applyTy ρ A) (applyNExp ρ e)

applyFields none fs = fs
applyFields ρ@(bind _ _ _) noFields = noFields
applyFields ρ@(bind _ _ _) (named n A fs) = named n (applyTy ρ A) (applyFields ρ fs)

applyProto : Idx → Proto → Proto
applyProto none S = S
applyProto ρ@(bind _ _ _) end = end
applyProto ρ@(bind _ _ _) (send A S) = send (applyTy ρ A) (applyProto ρ S)
applyProto ρ@(bind _ _ _) (recv A S) = recv (applyTy ρ A) (applyProto ρ S)
applyProto ρ@(bind _ _ _) (dsend y A S) = dsend y (applyTy ρ A) (applyProto (shadow y ρ) S)
applyProto ρ@(bind _ _ _) (drecv y A S) = drecv y (applyTy ρ A) (applyProto (shadow y ρ) S)
applyProto ρ@(bind _ _ _) (esend y e S) = esend y (applyNExp ρ e) (applyProto ρ S)
applyProto ρ@(bind _ _ _) (erecv y e S) = erecv y (applyNExp ρ e) (applyProto ρ S)
applyProto ρ@(bind _ _ _) (isend y S T) = isend y (applyProto (shadow y ρ) S) (applyProto (shadow y ρ) T)
applyProto ρ@(bind _ _ _) (irecv y S T) = irecv y (applyProto (shadow y ρ) S) (applyProto (shadow y ρ) T)
applyProto ρ@(bind _ _ _) (choose S T) = choose (applyProto ρ S) (applyProto ρ T)
applyProto ρ@(bind _ _ _) (branch S T) = branch (applyProto ρ S) (applyProto ρ T)

toℕ : Val nat → ℕ
toℕ zero = nzero
toℕ (suc n) = nsuc (toℕ n)

natExp : ValExpr nat → NExp
natExp (lit v) = nlit (toℕ v)
natExp (var x) = nvar x

-- A length comes from a nat. Another payload does not instantiate one.
ixOf : (A : Ty) → ValExpr A → NExp
ixOf nat v = natExp v
ixOf bit _ = nlit nzero
ixOf unit _ = nlit nzero
ixOf (pair _ _) _ = nlit nzero
ixOf (rec _) _ = nlit nzero
ixOf (vec _ _) _ = nlit nzero

------------------------------------------------------------------------
-- The evidence a sent nat owes. The bound is a numeral, or a name the
-- substitution resolves. A protocol name it does not resolve has no
-- bound. A numeral is at most a numeral by `≤`. Zero is at most a
-- name. A name is at most itself when the context binds it once, so
-- the value sent is the value the bound names. A name bound twice
-- has no evidence: the substitution may still name the outer binding.
------------------------------------------------------------------------

resolve : Idx → NExp → Maybe NExp
resolve _ (nlit n) = just (nlit n)
resolve ρ (nvar x) = lookupIdx ρ x

data Absent (x : String) : Ctx → Set where
  gone : Absent x []
  past : ∀ {y B Γ} → x ≢ y → Absent x Γ → Absent x ((y , B) ∷ Γ)

data Once (x : String) : Ctx → Set where
  first : ∀ {A Γ} → Absent x Γ → Once x ((x , A) ∷ Γ)
  later : ∀ {y B Γ} → x ≢ y → Once x Γ → Once x ((y , B) ∷ Γ)

data Le (Γ : Ctx) : ValExpr nat → NExp → Set where
  lit-le  : ∀ {m n} → toℕ m ≤ n → Le Γ (lit m) (nlit n)
  zero-le : ∀ {y} → Le Γ (lit zero) (nvar y)
  same-le : ∀ {x} → Once x Γ → Le Γ (var x) (nvar x)

data Owed (Γ : Ctx) (v : ValExpr nat) : Maybe NExp → Set where
  owed : ∀ {e} → Le Γ v e → Owed Γ v (just e)

-- Conformance under an index substitution. `none` is the identity,
-- which is the conformance a session is checked at. A dependent send
-- extends the substitution with the value. A dependent receive
-- extends it with the process's name for that binder. The protocol
-- in the index is the protocol as written.
data Conformsρ (Γ : Ctx) (ρ : Idx) : Proc → Proto → Set where
  done-end : Conformsρ Γ ρ done end

  abandon : ∀ {S} → Conformsρ Γ ρ stop S

  put-ok : ∀ {A B v P S} →
    A ≡ applyTy ρ B →
    ValExprOk Γ v →
    Conformsρ Γ ρ P S →
    Conformsρ Γ ρ (put A v P) (send B S)

  get-ok : ∀ {A B x P S} →
    A ≡ applyTy ρ B →
    Conformsρ ((x , A) ∷ Γ) ρ P S →
    Conformsρ Γ ρ (get A x P) (recv B S)

  dput-ok : ∀ {A B y v P S} →
    A ≡ applyTy ρ B →
    ValExprOk Γ v →
    Conformsρ Γ (bind y (ixOf A v) (shadow y ρ)) P S →
    Conformsρ Γ ρ (put A v P) (dsend y B S)

  dget-ok : ∀ {A B x y P S} →
    A ≡ applyTy ρ B →
    Conformsρ ((x , A) ∷ Γ) (renameIdx y x (shadow y ρ)) P S →
    Conformsρ Γ ρ (get A x P) (drecv y B S)

  -- The evidence is a premise. The process puts the nat alone.
  eput-ok : ∀ {y e v P S} →
    ValExprOk Γ v →
    Owed Γ v (resolve ρ e) →
    Conformsρ Γ ρ P S →
    Conformsρ Γ ρ (put nat v P) (esend y e S)

  eget-ok : ∀ {y e x P S} →
    Conformsρ ((x , nat) ∷ Γ) ρ P S →
    Conformsρ Γ ρ (get nat x P) (erecv y e S)

  -- The literal selects the arm. A variable bit has no rule.
  iput0-ok : ∀ {y P S T} →
    Conformsρ Γ (shadow y ρ) P S →
    Conformsρ Γ ρ (put bit (lit b0) P) (isend y S T)

  iput1-ok : ∀ {y P S T} →
    Conformsρ Γ (shadow y ρ) P T →
    Conformsρ Γ ρ (put bit (lit b1) P) (isend y S T)

  -- Both arms are checked. The name is bound at bit in each.
  -- The bit does not instantiate a length.
  iget-ok : ∀ {x y P Q S T} →
    Conformsρ ((x , bit) ∷ Γ) (shadow y ρ) P S →
    Conformsρ ((x , bit) ∷ Γ) (shadow y ρ) Q T →
    Conformsρ Γ ρ (iget x P Q) (irecv y S T)

  pick0-ok : ∀ {P S T} → Conformsρ Γ ρ P S → Conformsρ Γ ρ (pick0 P) (choose S T)
  pick1-ok : ∀ {P S T} → Conformsρ Γ ρ P T → Conformsρ Γ ρ (pick1 P) (choose S T)

  cover-ok : ∀ {P Q S T} → Conformsρ Γ ρ P S → Conformsρ Γ ρ Q T → Conformsρ Γ ρ (cover P Q) (branch S T)

Conforms : Ctx → Proc → Proto → Set
Conforms Γ P S = Conformsρ Γ none P S

------------------------------------------------------------------------
-- A protocol is well formed when every length is a numeral or a nat
-- in scope. The binder of a dependent action extends that scope.
------------------------------------------------------------------------

data TyOk : Ctx → Ty → Set
data FieldsOk : Ctx → Fields → Set

data NExpOk : Ctx → NExp → Set where
  nlit-ok : ∀ {Γ n} → NExpOk Γ (nlit n)
  nvar-ok : ∀ {Γ x} → x ∈ Γ ∷ nat → NExpOk Γ (nvar x)

data FieldsOk where
  noFields-ok : ∀ {Γ} → FieldsOk Γ noFields
  named-ok    : ∀ {Γ n A fs} → TyOk Γ A → FieldsOk Γ fs → FieldsOk Γ (named n A fs)

data TyOk where
  nat-ok  : ∀ {Γ} → TyOk Γ nat
  bit-ok  : ∀ {Γ} → TyOk Γ bit
  unit-ok : ∀ {Γ} → TyOk Γ unit
  pair-ok : ∀ {Γ A B} → TyOk Γ A → TyOk Γ B → TyOk Γ (pair A B)
  rec-ok  : ∀ {Γ fs} → FieldsOk Γ fs → TyOk Γ (rec fs)
  vec-ok  : ∀ {Γ A e} → TyOk Γ A → NExpOk Γ e → TyOk Γ (vec A e)

data ProtoOk : Ctx → Proto → Set where
  end-ok    : ∀ {Γ} → ProtoOk Γ end
  send-ok   : ∀ {Γ A S} → TyOk Γ A → ProtoOk Γ S → ProtoOk Γ (send A S)
  recv-ok   : ∀ {Γ A S} → TyOk Γ A → ProtoOk Γ S → ProtoOk Γ (recv A S)
  dsend-ok  : ∀ {Γ x A S} → TyOk Γ A → ProtoOk ((x , A) ∷ Γ) S → ProtoOk Γ (dsend x A S)
  drecv-ok  : ∀ {Γ x A S} → TyOk Γ A → ProtoOk ((x , A) ∷ Γ) S → ProtoOk Γ (drecv x A S)
  -- The name of an evidence payload is in scope in its bound only.
  esend-ok  : ∀ {Γ x e S} → NExpOk Γ e → ProtoOk Γ S → ProtoOk Γ (esend x e S)
  erecv-ok  : ∀ {Γ x e S} → NExpOk Γ e → ProtoOk Γ S → ProtoOk Γ (erecv x e S)
  -- The binder is a bit in both arms, so a length that names it is refused.
  isend-ok  : ∀ {Γ x S T} → ProtoOk ((x , bit) ∷ Γ) S → ProtoOk ((x , bit) ∷ Γ) T → ProtoOk Γ (isend x S T)
  irecv-ok  : ∀ {Γ x S T} → ProtoOk ((x , bit) ∷ Γ) S → ProtoOk ((x , bit) ∷ Γ) T → ProtoOk Γ (irecv x S T)
  choose-ok : ∀ {Γ S T} → ProtoOk Γ S → ProtoOk Γ T → ProtoOk Γ (choose S T)
  branch-ok : ∀ {Γ S T} → ProtoOk Γ S → ProtoOk Γ T → ProtoOk Γ (branch S T)

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
pong-ok = get-ok refl (put-ok refl lit-ok done-end)

other-nat : Conforms [] (get nat "x" (put nat (lit zero) done)) ping
other-nat = get-ok refl (put-ok refl lit-ok done-end)

-- Echo: receive a value and send it back.
echo : Proc
echo = get nat "v" (put nat (var "v") done)

echo-ok : Conforms [] echo ping
echo-ok = get-ok refl (put-ok refl (var-ok here) done-end)

v-here-ok : Conforms [] (put box (lit v-here) done) (send box end)
v-here-ok = put-ok refl lit-ok done-end

v-there-ok : Conforms [] (put box (lit v-there) done) (send box end)
v-there-ok = put-ok refl lit-ok done-end

not-type : ¬ Conforms [] (put nat (lit zero) done) (send box end)
not-type (put-ok () _ _)

-- A send where the protocol says receive.
swapped : ¬ Conforms [] (put nat (lit zero) done) (recv nat end)
swapped ()

-- The continuation is end, so a second send has no derivation.
twice : ¬ Conforms [] (put nat (lit zero) (put nat (lit zero) done)) (send nat end)
twice (put-ok _ _ ())

untouched : Conforms [] stop (send nat end)
untouched = abandon

chosen : Conforms [] (pick0 done) (choose end (send nat end))
chosen = pick0-ok done-end

both : Conforms [] (cover done (put box (lit v-here) done)) (branch end (send box end))
both = cover-ok done-end (put-ok refl lit-ok done-end)

------------------------------------------------------------------------
-- The search. `yes` carries a derivation. `no` carries its refutation.
-- The Elixir checker follows `decide`.
------------------------------------------------------------------------

data Answerρ (Γ : Ctx) (ρ : Idx) (P : Proc) (S : Proto) : Set where
  yes : Conformsρ Γ ρ P S → Answerρ Γ ρ P S
  no  : ¬ Conformsρ Γ ρ P S → Answerρ Γ ρ P S

Answer : Ctx → Proc → Proto → Set
Answer Γ P S = Answerρ Γ none P S

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

put-type : ∀ {Γ ρ A B v P S} → Conformsρ Γ ρ (put A v P) (send B S) → A ≡ applyTy ρ B
put-type (put-ok eq _ _) = eq

get-type : ∀ {Γ ρ A B x P S} → Conformsρ Γ ρ (get A x P) (recv B S) → A ≡ applyTy ρ B
get-type (get-ok eq _) = eq

dput-type : ∀ {Γ ρ A B y v P S} → Conformsρ Γ ρ (put A v P) (dsend y B S) → A ≡ applyTy ρ B
dput-type (dput-ok eq _ _) = eq

dget-type : ∀ {Γ ρ A B x y P S} → Conformsρ Γ ρ (get A x P) (drecv y B S) → A ≡ applyTy ρ B
dget-type (dget-ok eq _) = eq

on-put : ∀ {Γ ρ A B v P S} →
  Dec (A ≡ applyTy ρ B) → Dec (ValExprOk Γ v) → Answerρ Γ ρ P S →
  Answerρ Γ ρ (put A v P) (send B S)
on-put (yes′ refl) (yes′ vok) (yes d) = yes (put-ok refl vok d)
on-put (yes′ refl) (yes′ vok) (no nd) = no (λ { (put-ok refl _ d) → nd d })
on-put (yes′ refl) (no′ nvok) _ = no (λ { (put-ok refl vok _) → nvok vok })
on-put (no′ ¬eq) _ _ = no (λ { (put-ok eq _ _) → ¬eq eq })

on-get : ∀ {Γ ρ A B x P S} →
  Dec (A ≡ applyTy ρ B) → Answerρ ((x , A) ∷ Γ) ρ P S →
  Answerρ Γ ρ (get A x P) (recv B S)
on-get (yes′ refl) (yes d) = yes (get-ok refl d)
on-get (yes′ refl) (no nd) = no (λ { (get-ok refl d) → nd d })
on-get (no′ ¬eq) _ = no (λ { (get-ok eq _) → ¬eq eq })

on-dput : ∀ {Γ ρ B y v P S} →
  let A = applyTy ρ B in
  Dec (ValExprOk Γ v) →
  Answerρ Γ (bind y (ixOf A v) (shadow y ρ)) P S →
  Answerρ Γ ρ (put A v P) (dsend y B S)
on-dput (yes′ vok) (yes d) = yes (dput-ok refl vok d)
on-dput (yes′ vok) (no nd) = no (λ { (dput-ok refl _ d) → nd d })
on-dput (no′ nvok) _ = no (λ { (dput-ok refl vok _) → nvok vok })

on-dget : ∀ {Γ ρ B x y P S} →
  let A = applyTy ρ B in
  Answerρ ((x , A) ∷ Γ) (renameIdx y x (shadow y ρ)) P S →
  Answerρ Γ ρ (get A x P) (drecv y B S)
on-dget (yes d) = yes (dget-ok refl d)
on-dget (no nd) = no (λ { (dget-ok refl d) → nd d })

absent? : (x : String) (Γ : Ctx) → Dec (Absent x Γ)
absent? x [] = yes′ gone
absent? x ((y , _) ∷ Γ) with x ≟ y
... | yes′ refl = no′ (λ { (past x≢x _) → x≢x refl })
... | no′ ¬eq with absent? x Γ
...   | yes′ a = yes′ (past ¬eq a)
...   | no′ na = no′ (λ { (past _ a) → na a })

once? : (x : String) (Γ : Ctx) → Dec (Once x Γ)
once? x [] = no′ (λ ())
once? x ((y , _) ∷ Γ) with x ≟ y
... | yes′ refl with absent? x Γ
...   | yes′ a = yes′ (first a)
...   | no′ na = no′ (λ { (first a) → na a ; (later x≢x _) → x≢x refl })
once? x ((y , _) ∷ Γ) | no′ ¬eq with once? x Γ
...   | yes′ o = yes′ (later ¬eq o)
...   | no′ no-o = no′ (λ { (first _) → ¬eq refl ; (later _ o) → no-o o })

le? : (Γ : Ctx) (v : ValExpr nat) (e : NExp) → Dec (Le Γ v e)
le? Γ (lit m) (nlit n) with toℕ m ≤?ℕ n
... | yes′ p = yes′ (lit-le p)
... | no′ np = no′ (λ { (lit-le p) → np p })
le? Γ (lit zero) (nvar _) = yes′ zero-le
le? Γ (lit (suc _)) (nvar _) = no′ (λ ())
le? Γ (var _) (nlit _) = no′ (λ ())
le? Γ (var x) (nvar y) with x ≟ y
... | no′ ¬eq = no′ (λ { (same-le _) → ¬eq refl })
... | yes′ refl with once? x Γ
...   | yes′ o = yes′ (same-le o)
...   | no′ no-o = no′ (λ { (same-le o) → no-o o })

owed? : (Γ : Ctx) (v : ValExpr nat) (m : Maybe NExp) → Dec (Owed Γ v m)
owed? Γ v nothing = no′ (λ ())
owed? Γ v (just e) with le? Γ v e
... | yes′ l = yes′ (owed l)
... | no′ nl = no′ (λ { (owed l) → nl l })

on-eput : ∀ {Γ ρ y e v P S} →
  Dec (ValExprOk Γ v) → Dec (Owed Γ v (resolve ρ e)) → Answerρ Γ ρ P S →
  Answerρ Γ ρ (put nat v P) (esend y e S)
on-eput (yes′ vok) (yes′ ow) (yes d) = yes (eput-ok vok ow d)
on-eput (yes′ _) (yes′ _) (no nd) = no (λ { (eput-ok _ _ d) → nd d })
on-eput (yes′ _) (no′ nw) _ = no (λ { (eput-ok _ ow _) → nw ow })
on-eput (no′ nvok) _ _ = no (λ { (eput-ok vok _ _) → nvok vok })

on-eget : ∀ {Γ ρ y e x P S} →
  Answerρ ((x , nat) ∷ Γ) ρ P S →
  Answerρ Γ ρ (get nat x P) (erecv y e S)
on-eget (yes d) = yes (eget-ok d)
on-eget (no nd) = no (λ { (eget-ok d) → nd d })

-- A literal bit selects one arm. A variable selects neither.
isend-bit : ∀ {Γ ρ y P S T} →
  (v : ValExpr bit) →
  Answerρ Γ (shadow y ρ) P S →
  Answerρ Γ (shadow y ρ) P T →
  Answerρ Γ ρ (put bit v P) (isend y S T)
isend-bit (lit b0) (yes d) _ = yes (iput0-ok d)
isend-bit (lit b0) (no nd) _ = no (λ { (iput0-ok d) → nd d })
isend-bit (lit b1) _ (yes d) = yes (iput1-ok d)
isend-bit (lit b1) _ (no nd) = no (λ { (iput1-ok d) → nd d })
isend-bit (var _) _ _ = no (λ ())

on-iget : ∀ {Γ ρ x y P Q S T} →
  Answerρ ((x , bit) ∷ Γ) (shadow y ρ) P S →
  Answerρ ((x , bit) ∷ Γ) (shadow y ρ) Q T →
  Answerρ Γ ρ (iget x P Q) (irecv y S T)
on-iget (yes d) (yes e) = yes (iget-ok d e)
on-iget (no nd) _ = no (λ { (iget-ok d _) → nd d })
on-iget (yes _) (no nd) = no (λ { (iget-ok _ e) → nd e })

at0 : ∀ {Γ ρ P S T} → Answerρ Γ ρ P S → Answerρ Γ ρ (pick0 P) (choose S T)
at0 (yes d) = yes (pick0-ok d)
at0 (no nd) = no (λ { (pick0-ok d) → nd d })

at1 : ∀ {Γ ρ P S T} → Answerρ Γ ρ P T → Answerρ Γ ρ (pick1 P) (choose S T)
at1 (yes d) = yes (pick1-ok d)
at1 (no nd) = no (λ { (pick1-ok d) → nd d })

both-of : ∀ {Γ ρ P Q S T} → Answerρ Γ ρ P S → Answerρ Γ ρ Q T → Answerρ Γ ρ (cover P Q) (branch S T)
both-of (yes d) (yes e) = yes (cover-ok d e)
both-of (no nd) _ = no (λ { (cover-ok d _) → nd d })
both-of (yes _) (no nd) = no (λ { (cover-ok _ e) → nd e })

decideρ : (Γ : Ctx) (ρ : Idx) (P : Proc) (S : Proto) → Answerρ Γ ρ P S
decideρ Γ ρ done end = yes done-end
decideρ Γ ρ done (send _ _) = no (λ ())
decideρ Γ ρ done (recv _ _) = no (λ ())
decideρ Γ ρ done (dsend _ _ _) = no (λ ())
decideρ Γ ρ done (drecv _ _ _) = no (λ ())
decideρ Γ ρ done (esend _ _ _) = no (λ ())
decideρ Γ ρ done (erecv _ _ _) = no (λ ())
decideρ Γ ρ done (isend _ _ _) = no (λ ())
decideρ Γ ρ done (irecv _ _ _) = no (λ ())
decideρ Γ ρ done (choose _ _) = no (λ ())
decideρ Γ ρ done (branch _ _) = no (λ ())
decideρ Γ ρ stop _ = yes abandon
decideρ Γ ρ (put A v P) (send B S) = on-put (ty≟ A (applyTy ρ B)) (decideValExpr Γ v) (decideρ Γ ρ P S)
decideρ Γ ρ (put A v P) (dsend y B S) with ty≟ A (applyTy ρ B)
... | yes′ refl = on-dput (decideValExpr Γ v) (decideρ Γ (bind y (ixOf (applyTy ρ B) v) (shadow y ρ)) P S)
... | no′ ¬eq = no (λ d → ¬eq (dput-type d))
decideρ Γ ρ (put A v P) (esend y e S) with ty≟ A nat
... | yes′ refl = on-eput (decideValExpr Γ v) (owed? Γ v (resolve ρ e)) (decideρ Γ ρ P S)
... | no′ ¬eq = no (λ { (eput-ok _ _ _) → ¬eq refl })
decideρ Γ ρ (put A v P) (isend y S T) with ty≟ A bit
... | yes′ refl = isend-bit v (decideρ Γ (shadow y ρ) P S) (decideρ Γ (shadow y ρ) P T)
... | no′ ¬eq = no (λ { (iput0-ok _) → ¬eq refl ; (iput1-ok _) → ¬eq refl })
decideρ Γ ρ (put _ _ _) (erecv _ _ _) = no (λ ())
decideρ Γ ρ (put _ _ _) (irecv _ _ _) = no (λ ())
decideρ Γ ρ (put _ _ _) end = no (λ ())
decideρ Γ ρ (put _ _ _) (recv _ _) = no (λ ())
decideρ Γ ρ (put _ _ _) (drecv _ _ _) = no (λ ())
decideρ Γ ρ (put _ _ _) (choose _ _) = no (λ ())
decideρ Γ ρ (put _ _ _) (branch _ _) = no (λ ())
decideρ Γ ρ (get A x P) (recv B S) = on-get (ty≟ A (applyTy ρ B)) (decideρ ((x , A) ∷ Γ) ρ P S)
decideρ Γ ρ (get A x P) (drecv y B S) with ty≟ A (applyTy ρ B)
... | yes′ refl = on-dget (decideρ ((x , applyTy ρ B) ∷ Γ) (renameIdx y x (shadow y ρ)) P S)
... | no′ ¬eq = no (λ d → ¬eq (dget-type d))
decideρ Γ ρ (get A x P) (erecv y e S) with ty≟ A nat
... | yes′ refl = on-eget (decideρ ((x , nat) ∷ Γ) ρ P S)
... | no′ ¬eq = no (λ { (eget-ok _) → ¬eq refl })
decideρ Γ ρ (iget x P Q) (irecv y S T) =
  on-iget (decideρ ((x , bit) ∷ Γ) (shadow y ρ) P S) (decideρ ((x , bit) ∷ Γ) (shadow y ρ) Q T)
decideρ Γ ρ (get _ _ _) (esend _ _ _) = no (λ ())
decideρ Γ ρ (get _ _ _) (isend _ _ _) = no (λ ())
decideρ Γ ρ (get _ _ _) (irecv _ _ _) = no (λ ())
decideρ Γ ρ (get _ _ _) end = no (λ ())
decideρ Γ ρ (get _ _ _) (send _ _) = no (λ ())
decideρ Γ ρ (get _ _ _) (dsend _ _ _) = no (λ ())
decideρ Γ ρ (get _ _ _) (choose _ _) = no (λ ())
decideρ Γ ρ (get _ _ _) (branch _ _) = no (λ ())
decideρ Γ ρ (iget _ _ _) end = no (λ ())
decideρ Γ ρ (iget _ _ _) (send _ _) = no (λ ())
decideρ Γ ρ (iget _ _ _) (recv _ _) = no (λ ())
decideρ Γ ρ (iget _ _ _) (dsend _ _ _) = no (λ ())
decideρ Γ ρ (iget _ _ _) (drecv _ _ _) = no (λ ())
decideρ Γ ρ (iget _ _ _) (esend _ _ _) = no (λ ())
decideρ Γ ρ (iget _ _ _) (erecv _ _ _) = no (λ ())
decideρ Γ ρ (iget _ _ _) (isend _ _ _) = no (λ ())
decideρ Γ ρ (iget _ _ _) (choose _ _) = no (λ ())
decideρ Γ ρ (iget _ _ _) (branch _ _) = no (λ ())
decideρ Γ ρ (pick0 P) (choose S _) = at0 (decideρ Γ ρ P S)
decideρ Γ ρ (pick0 _) end = no (λ ())
decideρ Γ ρ (pick0 _) (send _ _) = no (λ ())
decideρ Γ ρ (pick0 _) (recv _ _) = no (λ ())
decideρ Γ ρ (pick0 _) (dsend _ _ _) = no (λ ())
decideρ Γ ρ (pick0 _) (drecv _ _ _) = no (λ ())
decideρ Γ ρ (pick0 _) (esend _ _ _) = no (λ ())
decideρ Γ ρ (pick0 _) (erecv _ _ _) = no (λ ())
decideρ Γ ρ (pick0 _) (isend _ _ _) = no (λ ())
decideρ Γ ρ (pick0 _) (irecv _ _ _) = no (λ ())
decideρ Γ ρ (pick0 _) (branch _ _) = no (λ ())
decideρ Γ ρ (pick1 P) (choose _ T) = at1 (decideρ Γ ρ P T)
decideρ Γ ρ (pick1 _) end = no (λ ())
decideρ Γ ρ (pick1 _) (send _ _) = no (λ ())
decideρ Γ ρ (pick1 _) (recv _ _) = no (λ ())
decideρ Γ ρ (pick1 _) (dsend _ _ _) = no (λ ())
decideρ Γ ρ (pick1 _) (drecv _ _ _) = no (λ ())
decideρ Γ ρ (pick1 _) (esend _ _ _) = no (λ ())
decideρ Γ ρ (pick1 _) (erecv _ _ _) = no (λ ())
decideρ Γ ρ (pick1 _) (isend _ _ _) = no (λ ())
decideρ Γ ρ (pick1 _) (irecv _ _ _) = no (λ ())
decideρ Γ ρ (pick1 _) (branch _ _) = no (λ ())
decideρ Γ ρ (cover P Q) (branch S T) = both-of (decideρ Γ ρ P S) (decideρ Γ ρ Q T)
decideρ Γ ρ (cover _ _) end = no (λ ())
decideρ Γ ρ (cover _ _) (send _ _) = no (λ ())
decideρ Γ ρ (cover _ _) (recv _ _) = no (λ ())
decideρ Γ ρ (cover _ _) (dsend _ _ _) = no (λ ())
decideρ Γ ρ (cover _ _) (drecv _ _ _) = no (λ ())
decideρ Γ ρ (cover _ _) (esend _ _ _) = no (λ ())
decideρ Γ ρ (cover _ _) (erecv _ _ _) = no (λ ())
decideρ Γ ρ (cover _ _) (isend _ _ _) = no (λ ())
decideρ Γ ρ (cover _ _) (irecv _ _ _) = no (λ ())
decideρ Γ ρ (cover _ _) (choose _ _) = no (λ ())

decide : (Γ : Ctx) (P : Proc) (S : Proto) → Answer Γ P S
decide Γ P S = decideρ Γ none P S

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
shadowed-refused (get-ok refl (get-ok refl (put-ok refl (var-ok (there v≢v _)) _))) = v≢v refl

-- The inner binding at its own type conforms.
inner : Conforms [] (get nat "v" (get bit "v" (put bit (var "v") done))) (recv nat (recv bit (send bit end)))
inner = get-ok refl (get-ok refl (put-ok refl (var-ok here) done-end))

inner-decides : decide [] (get nat "v" (get bit "v" (put bit (var "v") done))) (recv nat (recv bit (send bit end))) ≡ yes inner
inner-decides = refl

shadowed-decides : decide [] shadowed (recv nat (recv bit (send nat end))) ≡ no shadowed-refused
shadowed-decides = refl

left-open : Conforms [] (put nat (lit zero) stop) (send nat (send nat end))
left-open = put-ok refl lit-ok abandon

left-open-decides : decide [] (put nat (lit zero) stop) (send nat (send nat end)) ≡ yes left-open
left-open-decides = refl

untouched-decides : decide [] stop (send nat end) ≡ yes untouched
untouched-decides = refl

chosen-decides : decide [] (pick0 done) (choose end (send nat end)) ≡ yes chosen
chosen-decides = refl

both-decides : decide [] (cover done (put box (lit v-here) done)) (branch end (send box end)) ≡ yes both
both-decides = refl

------------------------------------------------------------------------
-- A received nat is the length of the vector sent next. The length
-- is that name. A bit is not a length. The continuation's action
-- does not depend on the value.
------------------------------------------------------------------------

sized : Proto
sized = drecv "n" nat (send (vec nat (nvar "n")) end)

sized-wf : ProtoOk [] sized
sized-wf = drecv-ok nat-ok (send-ok (vec-ok nat-ok (nvar-ok here)) end-ok)

len-two : NExp
len-two = natExp (lit two)

sized-server : Proc
sized-server = get nat "n" (put (vec nat (nvar "n")) (lit (rep zero)) done)

sized-client : Proc
sized-client = put nat (lit two) (get (vec nat len-two) "_" done)

sized-server-ok : Conforms [] sized-server sized
sized-server-ok = dget-ok refl (put-ok refl lit-ok done-end)

sized-client-ok : Conforms [] sized-client (dsend "n" nat (recv (vec nat (nvar "n")) end))
sized-client-ok = dput-ok refl lit-ok (get-ok refl done-end)

sized-server-decides : decide [] sized-server sized ≡ yes sized-server-ok
sized-server-decides = refl

sized-client-decides : decide [] sized-client (dsend "n" nat (recv (vec nat (nvar "n")) end)) ≡ yes sized-client-ok
sized-client-decides = refl

len-three : NExp
len-three = nlit (nsuc (nsuc (nsuc nzero)))

sized-bad : Proc
sized-bad = put nat (lit two) (get (vec nat len-three) "_" done)

sized-mismatch : ¬ Conforms [] sized-bad (dsend "n" nat (recv (vec nat (nvar "n")) end))
sized-mismatch (dput-ok refl _ (get-ok () _))

bit-len : Proto
bit-len = drecv "b" bit (send (vec nat (nvar "b")) end)

not-bit-len : ¬ ProtoOk [] bit-len
not-bit-len (drecv-ok _ (send-ok (vec-ok _ (nvar-ok (there _ ()))) _))

------------------------------------------------------------------------
-- A window is received, and data is sent within it. The process owes
-- `d ≤ w`. Sending the window itself is evidence, and so is zero. A
-- numeral against a window that was received has no evidence: the
-- window may be smaller. A window the process sent is a numeral, so
-- `≤` decides it. A name bound twice is refused.
------------------------------------------------------------------------

num : ℕ → Val nat
num nzero = zero
num (nsuc n) = suc (num n)

window : Proto
window = drecv "w" nat (esend "d" (nvar "w") end)

window-wf : ProtoOk [] window
window-wf = drecv-ok nat-ok (esend-ok (nvar-ok here) end-ok)

-- The bound of an evidence payload is a numeral or a nat in scope.
unbound-window : ¬ ProtoOk [] (esend "d" (nvar "w") end)
unbound-window (esend-ok (nvar-ok ()) _)

full : Proc
full = get nat "w" (put nat (var "w") done)

full-ok : Conforms [] full window
full-ok = dget-ok refl (eput-ok (var-ok here) (owed (same-le (first gone))) done-end)

full-decides : decide [] full window ≡ yes full-ok
full-decides = refl

empty : Proc
empty = get nat "w" (put nat (lit zero) done)

empty-ok : Conforms [] empty window
empty-ok = dget-ok refl (eput-ok lit-ok (owed zero-le) done-end)

empty-decides : decide [] empty window ≡ yes empty-ok
empty-decides = refl

guess : Proc
guess = get nat "w" (put nat (lit two) done)

guess-refused : ¬ Conforms [] guess window
guess-refused (dget-ok refl (eput-ok _ (owed ()) _))

guess-decides : decide [] guess window ≡ no guess-refused
guess-decides = refl

granted : Proto
granted = dsend "w" nat (esend "d" (nvar "w") end)

within : Proc
within = put nat (lit (num 8)) (put nat (lit (num 5)) done)

within-ok : Conforms [] within granted
within-ok =
  dput-ok refl lit-ok
    (eput-ok lit-ok (owed (lit-le (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) done-end)

within-decides : decide [] within granted ≡ yes within-ok
within-decides = refl

-- `d > w`: nine is not at most eight.
over : Proc
over = put nat (lit (num 8)) (put nat (lit (num 9)) done)

over-refused : ¬ Conforms [] over granted
over-refused
  (dput-ok refl _ (eput-ok _ (owed (lit-le (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))))) _))

over-decides : decide [] over granted ≡ no over-refused
over-decides = refl

-- A numeral bound in the protocol.
frame : Proto
frame = esend "d" (nlit 16384) end

frame-ok : Conforms [] (put nat (lit zero) done) frame
frame-ok = eput-ok lit-ok (owed (lit-le z≤n)) done-end

-- A second `w` hides the window. The bound still names the first.
stale-proto : Proto
stale-proto = drecv "w" nat (recv nat (esend "d" (nvar "w") end))

stale : Proc
stale = get nat "w" (get nat "w" (put nat (var "w") done))

stale-refused : ¬ Conforms [] stale stale-proto
stale-refused (dget-ok refl (get-ok refl (eput-ok _ (owed (same-le (first (past w≢w _)))) _))) = w≢w refl
stale-refused (dget-ok refl (get-ok refl (eput-ok _ (owed (same-le (later w≢w _))) _))) = w≢w refl

stale-decides : decide [] stale stale-proto ≡ no stale-refused
stale-decides = refl

------------------------------------------------------------------------
-- A received bit chooses the arm. `b0` continues as the first
-- protocol. `b1` continues as the second. The sender writes the
-- literal. A variable bit does not select an arm. A nat is not an
-- index, so it has no constructor here. The bit is not a length.
------------------------------------------------------------------------

route : Proto
route = irecv "b" (send nat end) (recv nat end)

route-server : Proc
route-server = iget "b" (put nat (lit one) done) (get nat "n" done)

route-server-ok : Conforms [] route-server route
route-server-ok = iget-ok (put-ok refl lit-ok done-end) (get-ok refl done-end)

route-decides : decide [] route-server route ≡ yes route-server-ok
route-decides = refl

one-arm : Proc
one-arm = get bit "b" (put nat (lit one) done)

one-arm-refused : ¬ Conforms [] one-arm route
one-arm-refused ()

one-arm-decides : decide [] one-arm route ≡ no one-arm-refused
one-arm-decides = refl

-- The sender writes `b0`. The received name does not select the arm.
route-fwd : Proto
route-fwd = drecv "b" bit (isend "c" end (send nat end))

fwd : Proc
fwd = get bit "b" (put bit (var "b") done)

fwd-refused : ¬ Conforms [] fwd route-fwd
fwd-refused (dget-ok refl ())

fwd-decides : decide [] fwd route-fwd ≡ no fwd-refused
fwd-decides = refl

fwd-lit : Proc
fwd-lit = get bit "b" (put bit (lit b0) done)

fwd-lit-ok : Conforms [] fwd-lit route-fwd
fwd-lit-ok = dget-ok refl (iput0-ok done-end)

fwd-lit-decides : decide [] fwd-lit route-fwd ≡ yes fwd-lit-ok
fwd-lit-decides = refl

route-back : Proto
route-back = isend "b" (recv nat end) (send nat end)

crossed-proc : Proc
crossed-proc = put bit (lit b0) (put nat (lit one) done)

crossed-refused : ¬ Conforms [] crossed-proc route-back
crossed-refused (iput0-ok ())

crossed-decides : decide [] crossed-proc route-back ≡ no crossed-refused
crossed-decides = refl

-- The received bit can be sent later as a bit. It does not select that send.
echo-bit : Proc
echo-bit = iget "b" (put bit (var "b") done) (put bit (var "b") done)

echo-proto : Proto
echo-proto = irecv "b" (send bit end) (send bit end)

echo-bit-ok : Conforms [] echo-bit echo-proto
echo-bit-ok = iget-ok (put-ok refl (var-ok here) done-end) (put-ok refl (var-ok here) done-end)

echo-bit-decides : decide [] echo-bit echo-proto ≡ yes echo-bit-ok
echo-bit-decides = refl

-- The index bit is not a vector length.
bit-arm : Proto
bit-arm = irecv "b" (send (vec nat (nvar "b")) end) end

not-bit-arm : ¬ ProtoOk [] bit-arm
not-bit-arm (irecv-ok (send-ok (vec-ok _ (nvar-ok (there _ ()))) _) _)

------------------------------------------------------------------------
-- The actions a process takes. `say` carries the value expression.
-- `hear` carries the type and variable name. `choose0` and `choose1`
-- are the process's choice. `offer` is both arms. `index` holds both
-- arms of a received bit. The bit itself is the message the other
-- process says, not a label beside it. `leave` abandons the channel.
-- `finish` closes it.
------------------------------------------------------------------------

data Skel : Set where
  finish  : Skel
  leave   : Skel
  say     : ∀ {A} → ValExpr A → Skel → Skel
  hear    : Ty → String → Skel → Skel
  choose0 : Skel → Skel
  choose1 : Skel → Skel
  offer   : Skel → Skel → Skel
  index   : String → Skel → Skel → Skel

skel : Proc → Skel
skel done = finish
skel stop = leave
skel (put _ v P) = say v (skel P)
skel (get A x P) = hear A x (skel P)
skel (pick0 P) = choose0 (skel P)
skel (pick1 P) = choose1 (skel P)
skel (cover P Q) = offer (skel P) (skel Q)
skel (iget x P Q) = index x (skel P) (skel Q)

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

-- The value goes on the channel. The evidence is not in the skeleton.
full-skel : skel full ≡ hear nat "w" (say (var "w") finish)
full-skel = refl

within-skel : skel within ≡ say (lit (num 8)) (say (lit (num 5)) finish)
within-skel = refl

-- Both arms are in the skeleton. The selecting bit is not a label.
route-skel : skel route-server ≡ index "b" (say (lit one) finish) (hear nat "n" finish)
route-skel = refl

-- The sender's literal is an ordinary payload. The other arm is not sent.
index-say : skel (put bit (lit b0) done) ≡ say (lit b0) finish
index-say = refl

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
  ends-iget  : ∀ {x P Q} → Ends P → Ends Q → Ends (iget x P Q)

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

step-iget : ∀ {x P Q} → Finish P → Finish Q → Finish (iget x P Q)
step-iget (ends d) (ends e) = ends (ends-iget d e)
step-iget (leaves nd) _ = leaves (λ { (ends-iget d _) → nd d })
step-iget (ends _) (leaves nd) = leaves (λ { (ends-iget _ e) → nd e })

finishes : (P : Proc) → Finish P
finishes done = ends ends-done
finishes stop = leaves (λ ())
finishes (put _ _ P) = step-put (finishes P)
finishes (get _ _ P) = step-get (finishes P)
finishes (pick0 P) = step-pick0 (finishes P)
finishes (pick1 P) = step-pick1 (finishes P)
finishes (cover P Q) = step-cover (finishes P) (finishes Q)
finishes (iget x P Q) = step-iget (finishes P) (finishes Q)

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

route-finishes :
  finishes route-server ≡ ends (ends-iget (ends-put ends-done) (ends-get ends-done))
route-finishes = refl

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
  index-ok   : ∀ {x k q} → NoLeave k → NoLeave q → NoLeave (index x k q)

ends-no-leave : ∀ {P} → Ends P → NoLeave (skel P)
ends-no-leave ends-done = finish-ok
ends-no-leave (ends-put e) = say-ok (ends-no-leave e)
ends-no-leave (ends-get e) = hear-ok (ends-no-leave e)
ends-no-leave (ends-pick0 e) = choose0-ok (ends-no-leave e)
ends-no-leave (ends-pick1 e) = choose1-ok (ends-no-leave e)
ends-no-leave (ends-cover e f) = offer-ok (ends-no-leave e) (ends-no-leave f)
ends-no-leave (ends-iget e f) = index-ok (ends-no-leave e) (ends-no-leave f)

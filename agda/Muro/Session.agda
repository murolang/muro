------------------------------------------------------------------------
-- Affine sessions. One channel. A communication carries a payload
-- and one continuation. The payload is a run type in this fragment:
-- a nat, a bit, unit, a pair, a record of named fields, a vector
-- whose length is a numeral or a nat name, or a declared data type.
-- The constructors are the ones that declaration already has. A
-- value inhabits the type when each field inhabits the field's type.
-- A pair is a tuple. A record is a fixed map: the names are the type,
-- and a pair around a record is a tuple wrapping that map. An open
-- map, whose keys are chosen at run time, is not a type. An indexed
-- declaration is not a payload. A put may send the value a run
-- definition computes from its arguments. The body is a first-order
-- term, and a definition may call only a definition declared before
-- it. Evaluation recurses on that prefix and on the term. A
-- definition whose body calls itself or a later definition does not
-- evaluate, including an arm the argument does not take. A variable
-- argument does not evaluate. The result is cast to the payload
-- type. A cast that fails, or a value that does not inhabit the
-- type, has no derivation. `get` may continue as a match on the
-- value it just bound. The arms are the constructors of that
-- payload, in order. A bare arm is that continuation. A named arm
-- binds the fields of its constructor, and those names are payload
-- data in the arm. A received pair has one product arm, `(a, b)`,
-- and a received record has one product arm naming every field in
-- the order the type writes them. A component is payload data, the
-- same way a constructor field is. Each arm conforms to the one
-- continuation, and the processes may differ. The meeting selects
-- the arm of the value that was sent and reads the fields of that
-- value, or the components of the pair or the record. A match that
-- does not cover the received value has no derivation. An indexed bit is
-- still the literal the sender writes.
--
-- A dependent continuation may also be a `case` on the name just
-- bound, or on a run applied to that name. The arms are one protocol
-- per constructor, in declaration order: of the payload, or of the
-- run's result. A sender whose value is known is checked on the arm
-- that value selects, by evaluating the run on the value. A receiver
-- matches every constructor of the payload. A run that only
-- distinguishes constructors selects one protocol per constructor. A
-- run that reads a field of a bit, a declared data type, or a nat
-- whose bound is a numeral selects one protocol for each value of the
-- fields it reads, and the process covers that split by a case on the
-- bound field. A bounded nat field contributes `w + 1`. A field the
-- run binds and does not read is not split. A received nat whose
-- bound is a numeral `w` is a finite split into `0` … `w`. A direct
-- case writes those numerals in order. A run that reads the nat is
-- evaluated at each of them, and the arm is the constructor it
-- returns. A run that reads several finite factors is evaluated on
-- their product. The length of that split is the product of the
-- widths, and the length of a data payload is the sum of those
-- products over its constructors. There is no fuel and no budget.
-- The two-factor derivation of one bounded nat and one bit or declared
-- data payload stays. Any other finite product is the same split on
-- the whole factor list. A nat with no numeral bound, a bound that is
-- a name, a pair, a record, a vector, unit, and a recursive field do
-- not split. Selecting an arm is the same evaluator. A case that is
-- not that continuation, a run outside the fragment, and a sender
-- whose value is not known when the arms differ, have no derivation.
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
-- it. The two arms are the index. An unbounded nat does not choose
-- an arm, and a variable bit does not select one: the sender writes
-- `b0` or `b1`. A numeral bound does. `choose` and `branch` select
-- an arm by a label, not by a payload. Two processes meet when the
-- sent type is the type the
-- continuation expects, the value inhabits that type, and an index
-- meets the arm of that same bit.
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

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; length; map)
open import Data.List.Properties using (length-++; length-map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _≤_; _+_; _*_; z≤n; s≤s) renaming (zero to nzero; suc to nsuc)
open import Data.Nat.Properties using (≤-pred; +-identityʳ; +-suc; +-assoc) renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using (_≟_; _==_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable.Core using (Dec)
open import Relation.Nullary.Decidable.Core using () renaming (yes to yes′; no to no′)

open import Muro.Base using (Mode; spec; evid; run; Qty; affine)

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- A declared data type, as a payload. Parameters are a count. Each
-- constructor carries the fields the declaration already has. `fPar`
-- is a parameter. `fBound w` is a nat field whose bound is the
-- numeral `w`. `fSelf` is this declaration, applied to payload
-- arguments. `fDat` is another such declaration. An index is not a
-- parameter, and a field that is a function is not a field here.
-- A bound that is not a numeral is not a field of this form.
------------------------------------------------------------------------

mutual
  data Fld : Set where
    fNat   : Fld
    fBound : ℕ → Fld
    fBit   : Fld
    fUnit  : Fld
    fPair  : Fld → Fld → Fld
    fPar   : ℕ → Fld
    fSelf  : List Fld → Fld
    fDat   : Decl → List Fld → Fld

  data Ctor : Set where
    ctor : String → List Fld → Ctor

  data Decl : Set where
    mkDecl : String → ℕ → List Ctor → Decl

np : Decl → ℕ
np (mkDecl _ n _) = n

ctorsOf : Decl → List Ctor
ctorsOf (mkDecl _ _ cs) = cs

true≢false : true ≢ false
true≢false ()

false≢true : false ≢ true
false≢true ()

just≢nothing : ∀ {A : Set} {x : A} → just x ≢ nothing
just≢nothing ()

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

mutual
  fld≟ : (a b : Fld) → Dec (a ≡ b)
  fld≟ fNat fNat = yes′ refl
  fld≟ fNat (fBound _) = no′ (λ ())
  fld≟ fNat fBit = no′ (λ ())
  fld≟ fNat fUnit = no′ (λ ())
  fld≟ fNat (fPair _ _) = no′ (λ ())
  fld≟ fNat (fPar _) = no′ (λ ())
  fld≟ fNat (fSelf _) = no′ (λ ())
  fld≟ fNat (fDat _ _) = no′ (λ ())
  fld≟ (fBound _) fNat = no′ (λ ())
  fld≟ (fBound m) (fBound n) with m ≟ℕ n
  ... | yes′ refl = yes′ refl
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  fld≟ (fBound _) fBit = no′ (λ ())
  fld≟ (fBound _) fUnit = no′ (λ ())
  fld≟ (fBound _) (fPair _ _) = no′ (λ ())
  fld≟ (fBound _) (fPar _) = no′ (λ ())
  fld≟ (fBound _) (fSelf _) = no′ (λ ())
  fld≟ (fBound _) (fDat _ _) = no′ (λ ())
  fld≟ fBit fNat = no′ (λ ())
  fld≟ fBit (fBound _) = no′ (λ ())
  fld≟ fBit fBit = yes′ refl
  fld≟ fBit fUnit = no′ (λ ())
  fld≟ fBit (fPair _ _) = no′ (λ ())
  fld≟ fBit (fPar _) = no′ (λ ())
  fld≟ fBit (fSelf _) = no′ (λ ())
  fld≟ fBit (fDat _ _) = no′ (λ ())
  fld≟ fUnit fNat = no′ (λ ())
  fld≟ fUnit (fBound _) = no′ (λ ())
  fld≟ fUnit fBit = no′ (λ ())
  fld≟ fUnit fUnit = yes′ refl
  fld≟ fUnit (fPair _ _) = no′ (λ ())
  fld≟ fUnit (fPar _) = no′ (λ ())
  fld≟ fUnit (fSelf _) = no′ (λ ())
  fld≟ fUnit (fDat _ _) = no′ (λ ())
  fld≟ (fPair _ _) fNat = no′ (λ ())
  fld≟ (fPair _ _) (fBound _) = no′ (λ ())
  fld≟ (fPair _ _) fBit = no′ (λ ())
  fld≟ (fPair _ _) fUnit = no′ (λ ())
  fld≟ (fPair a b) (fPair c d) with fld≟ a c
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl with fld≟ b d
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl
  fld≟ (fPair _ _) (fPar _) = no′ (λ ())
  fld≟ (fPair _ _) (fSelf _) = no′ (λ ())
  fld≟ (fPair _ _) (fDat _ _) = no′ (λ ())
  fld≟ (fPar _) fNat = no′ (λ ())
  fld≟ (fPar _) (fBound _) = no′ (λ ())
  fld≟ (fPar _) fBit = no′ (λ ())
  fld≟ (fPar _) fUnit = no′ (λ ())
  fld≟ (fPar _) (fPair _ _) = no′ (λ ())
  fld≟ (fPar m) (fPar n) with m ≟ℕ n
  ... | yes′ refl = yes′ refl
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  fld≟ (fPar _) (fSelf _) = no′ (λ ())
  fld≟ (fPar _) (fDat _ _) = no′ (λ ())
  fld≟ (fSelf _) fNat = no′ (λ ())
  fld≟ (fSelf _) (fBound _) = no′ (λ ())
  fld≟ (fSelf _) fBit = no′ (λ ())
  fld≟ (fSelf _) fUnit = no′ (λ ())
  fld≟ (fSelf _) (fPair _ _) = no′ (λ ())
  fld≟ (fSelf _) (fPar _) = no′ (λ ())
  fld≟ (fSelf fs) (fSelf gs) with flds≟ fs gs
  ... | yes′ refl = yes′ refl
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  fld≟ (fSelf _) (fDat _ _) = no′ (λ ())
  fld≟ (fDat _ _) fNat = no′ (λ ())
  fld≟ (fDat _ _) (fBound _) = no′ (λ ())
  fld≟ (fDat _ _) fBit = no′ (λ ())
  fld≟ (fDat _ _) fUnit = no′ (λ ())
  fld≟ (fDat _ _) (fPair _ _) = no′ (λ ())
  fld≟ (fDat _ _) (fPar _) = no′ (λ ())
  fld≟ (fDat _ _) (fSelf _) = no′ (λ ())
  fld≟ (fDat d fs) (fDat e gs) with decl≟ d e
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl with flds≟ fs gs
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl

  flds≟ : (fs gs : List Fld) → Dec (fs ≡ gs)
  flds≟ [] [] = yes′ refl
  flds≟ [] (_ ∷ _) = no′ (λ ())
  flds≟ (_ ∷ _) [] = no′ (λ ())
  flds≟ (f ∷ fs) (g ∷ gs) with fld≟ f g
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl with flds≟ fs gs
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl

  ctor≟ : (c d : Ctor) → Dec (c ≡ d)
  ctor≟ (ctor x fs) (ctor y gs) with x ≟ y
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl with flds≟ fs gs
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl

  ctors≟ : (cs ds : List Ctor) → Dec (cs ≡ ds)
  ctors≟ [] [] = yes′ refl
  ctors≟ [] (_ ∷ _) = no′ (λ ())
  ctors≟ (_ ∷ _) [] = no′ (λ ())
  ctors≟ (c ∷ cs) (d ∷ ds) with ctor≟ c d
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl with ctors≟ cs ds
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl

  decl≟ : (d e : Decl) → Dec (d ≡ e)
  decl≟ (mkDecl x m cs) (mkDecl y n ds) with x ≟ y
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl with m ≟ℕ n
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl with ctors≟ cs ds
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl

------------------------------------------------------------------------
-- The payload types. `pair` is a tuple. `rec` is a fixed map, one
-- named field after another. The names are part of the type.
-- `vec A e` is a vector of `A` whose length is a numeral or a name.
-- `dat d as` is the declaration `d` applied to the payload arguments
-- `as`.
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
  dat  : Decl → List Ty → Ty

data Row : Fields → Set
data Val : Ty → Set
data Spine : Set

data Spine where
  snil  : Spine
  scons : (A : Ty) → Val A → Spine → Spine

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
  -- The name need not be a constructor. `fits` refuses it.
  con  : ∀ {d as} → String → Spine → Val (dat d as)

------------------------------------------------------------------------
-- Value expressions. A literal is a value. A variable is a name
-- bound by `get`. A call is an application of a run definition in
-- this fragment. The index is the payload type the call claims.
------------------------------------------------------------------------

mutual
  data VArg : Set where
    varg : (B : Ty) → ValExpr B → VArg

  data ValExpr : Ty → Set where
    lit  : ∀ {A} → Val A → ValExpr A
    var  : ∀ {A} → String → ValExpr A
    call : ∀ {A} → String → List VArg → ValExpr A

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
  ty≟ nat (dat _ _) = no′ (λ ())
  ty≟ bit nat = no′ (λ ())
  ty≟ bit bit = yes′ refl
  ty≟ bit unit = no′ (λ ())
  ty≟ bit (pair _ _) = no′ (λ ())
  ty≟ bit (rec _) = no′ (λ ())
  ty≟ bit (vec _ _) = no′ (λ ())
  ty≟ bit (dat _ _) = no′ (λ ())
  ty≟ unit nat = no′ (λ ())
  ty≟ unit bit = no′ (λ ())
  ty≟ unit unit = yes′ refl
  ty≟ unit (pair _ _) = no′ (λ ())
  ty≟ unit (rec _) = no′ (λ ())
  ty≟ unit (vec _ _) = no′ (λ ())
  ty≟ unit (dat _ _) = no′ (λ ())
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
  ty≟ (pair _ _) (dat _ _) = no′ (λ ())
  ty≟ (rec _) nat = no′ (λ ())
  ty≟ (rec _) bit = no′ (λ ())
  ty≟ (rec _) unit = no′ (λ ())
  ty≟ (rec _) (pair _ _) = no′ (λ ())
  ty≟ (rec fs) (rec gs) with fields≟ fs gs
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl
  ty≟ (rec _) (vec _ _) = no′ (λ ())
  ty≟ (rec _) (dat _ _) = no′ (λ ())
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
  ty≟ (vec _ _) (dat _ _) = no′ (λ ())
  ty≟ (dat _ _) nat = no′ (λ ())
  ty≟ (dat _ _) bit = no′ (λ ())
  ty≟ (dat _ _) unit = no′ (λ ())
  ty≟ (dat _ _) (pair _ _) = no′ (λ ())
  ty≟ (dat _ _) (rec _) = no′ (λ ())
  ty≟ (dat _ _) (vec _ _) = no′ (λ ())
  ty≟ (dat d as) (dat e bs) with decl≟ d e
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl with tys≟ as bs
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl

  tys≟ : (as bs : List Ty) → Dec (as ≡ bs)
  tys≟ [] [] = yes′ refl
  tys≟ [] (_ ∷ _) = no′ (λ ())
  tys≟ (_ ∷ _) [] = no′ (λ ())
  tys≟ (A ∷ as) (B ∷ bs) with ty≟ A B
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl with tys≟ as bs
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  ... | yes′ refl = yes′ refl

------------------------------------------------------------------------
-- One continuation after the payload. An indexed bit has two
-- continuations, one for each value. Choice is a separate arm.
-- `pcase` is that continuation chosen by the value just bound:
-- `byVal` matches the payload's constructors, `byRun` matches the
-- constructors of the run's result. `bySplit` matches that result on
-- the product of the factors the run reads. The last tag is the
-- binder. Earlier tags are finite splits already in scope. A bounded
-- nat is `tagNat`. A bit is `tagBit`. A declared data type is
-- `tagDat`, with its constructors in declaration order.
------------------------------------------------------------------------

data Tag : Set where
  tagNat : String → ℕ → Tag
  tagBit : String → Tag
  tagDat : String → List String → Tag

-- A factor list with a finite product other than one bounded nat and
-- one bit or declared data payload. The two-factor shapes stay on
-- their own rules. There is no fuel: a list carries a tag when its
-- shape is one of these.
data WTag : List Tag → Set where
  wt-bit : ∀ {x t ts} → WTag (tagBit x ∷ t ∷ ts)
  wt-dat : ∀ {x cs t ts} → WTag (tagDat x cs ∷ t ∷ ts)
  wt-nn  : ∀ {a n b m ts} → WTag (tagNat a n ∷ tagNat b m ∷ ts)
  wt-nd  : ∀ {a n x cs t ts} → WTag (tagNat a n ∷ tagDat x cs ∷ t ∷ ts)
  wt-nb  : ∀ {a n x t ts} → WTag (tagNat a n ∷ tagBit x ∷ t ∷ ts)

wtag : (ts : List Tag) → Maybe (WTag ts)
wtag [] = nothing
wtag (_ ∷ []) = nothing
wtag (tagBit x ∷ t ∷ ts) = just (wt-bit {x = x} {t = t} {ts = ts})
wtag (tagDat x cs ∷ t ∷ ts) = just (wt-dat {x = x} {cs = cs} {t = t} {ts = ts})
wtag (tagNat a n ∷ tagNat b m ∷ ts) = just (wt-nn {a = a} {n = n} {b = b} {m = m} {ts = ts})
wtag (tagNat _ _ ∷ tagDat _ _ ∷ []) = nothing
wtag (tagNat a n ∷ tagDat x cs ∷ t ∷ ts) = just (wt-nd {a = a} {n = n} {x = x} {cs = cs} {t = t} {ts = ts})
wtag (tagNat _ _ ∷ tagBit _ ∷ []) = nothing
wtag (tagNat a n ∷ tagBit x ∷ t ∷ ts) = just (wt-nb {a = a} {n = n} {x = x} {t = t} {ts = ts})

wtag-just : ∀ {ts} (wt : WTag ts) → wtag ts ≡ just wt
wtag-just wt-bit = refl
wtag-just wt-dat = refl
wtag-just wt-nn = refl
wtag-just wt-nd = refl
wtag-just wt-nb = refl

tagBit≢Nat : ∀ {x y n} → tagBit x ≢ tagNat y n
tagBit≢Nat ()

tagDat≢Nat : ∀ {x cs y n} → tagDat x cs ≢ tagNat y n
tagDat≢Nat ()

tagNat-inj : ∀ {a b n m} → tagNat a n ≡ tagNat b m → a ≡ b × n ≡ m
tagNat-inj refl = refl , refl

wtag-nil : WTag [] → ⊥
wtag-nil ()

wtag-one : ∀ {t} → WTag (t ∷ []) → ⊥
wtag-one ()

badBit : ∀ {y w rest x t ts} → tagNat y w ∷ rest ≡ tagBit x ∷ t ∷ ts → ⊥
badBit ()

badDat : ∀ {y w rest x cs t ts} → tagNat y w ∷ rest ≡ tagDat x cs ∷ t ∷ ts → ⊥
badDat ()

cons-inj : ∀ {A : Set} {x y : A} {xs ys : List A} →
  x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
cons-inj refl = refl , refl

data Scrut : Set where
  byVal : String → Scrut
  byRun : String → String → Ty → Scrut
  bySplit : String → List Tag → Ty → Scrut

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
  pcase  : Scrut → List (String × Proto) → Proto

protoMode : Mode
protoMode = spec

-- The split at the end of a send or receive spine. Exact two-factor
-- shapes and a variable bound are nothing, so those rules stay.
findWide : Proto → Maybe (List Tag)
findWide (dsend _ _ S) = findWide S
findWide (esend _ (nlit _) S) = findWide S
findWide (esend _ (nvar _) _) = nothing
findWide (pcase (bySplit _ tags _) _) with wtag tags
... | nothing = nothing
... | just _ = just tags
findWide _ = nothing

------------------------------------------------------------------------
-- The process is the run's actions on the channel. `put` sends a
-- value expression: a literal, a variable, or a call of a run
-- definition. `get` receives a value and binds it to a named
-- variable. The continuation may reference that variable. `mget`
-- receives and matches that same name. The arms are one per
-- constructor, `b0` then `b1` for a bit, and declaration order for
-- data. A pair or a record has one product arm. A bare arm carries
-- no binders. A named arm names that constructor and binds its
-- fields, last name innermost. A product arm binds the two
-- components, or every record field in type order, last name
-- innermost. Each arm conforms to the one continuation, and the
-- processes may differ.
-- `pick0` and `pick1` are the process's choice. `cover` offers
-- both branches. `iget x P Q` receives a bit, binds it to `x`, and
-- offers both arms: `b0` continues as `P` and `b1` continues as `Q`.
-- `stop` uses the channel no further.
------------------------------------------------------------------------

-- A product pattern is one level. `pPair` binds the two components.
-- `pRec` names each field and binds it. The field names are the type's.
data Pat : Set where
  pPair : String → String → Pat
  pRec  : List (String × String) → Pat

mutual
  data Proc : Set where
    done  : Proc
    stop  : Proc
    put   : (A : Ty) → ValExpr A → Proc → Proc
    get   : (A : Ty) → String → Proc → Proc
    pick0 : Proc → Proc
    pick1 : Proc → Proc
    cover : Proc → Proc → Proc
    iget  : String → Proc → Proc → Proc
    mget  : (A : Ty) → String → List PArm → Proc

  -- `bare` is the positional arm. `named` binds the constructor's fields.
  -- `prod` binds the components of a pair or the fields of a record.
  -- `fork` is a named constructor arm whose continuation cases on one
  -- bound field. The inner arms are that field's constructors.
  data PArm : Set where
    bare  : Proc → PArm
    named : String → List String → Proc → PArm
    prod  : Pat → Proc → PArm
    fork  : String → List String → String → List PArm → PArm

body : PArm → Proc
body (bare p) = p
body (named _ _ p) = p
body (prod _ p) = p
body (fork _ _ _ qs) = mget unit "f" qs

-- The binders a product pattern introduces, first component first.
seconds : List (String × String) → List String
seconds [] = []
seconds ((_ , b) ∷ bs) = b ∷ seconds bs

patBinders : Pat → List String
patBinders (pPair x y) = x ∷ y ∷ []
patBinders (pRec bs) = seconds bs

------------------------------------------------------------------------
-- A parameter index, or nothing when the index is past the arguments.
------------------------------------------------------------------------

nth : ∀ {A : Set} → List A → ℕ → Maybe A
nth [] _ = nothing
nth (x ∷ _) nzero = just x
nth (_ ∷ xs) (nsuc n) = nth xs n

-- The binder at a left-to-right index is the name the case splits on.
hitName : (xs : List String) (i : ℕ) (y : String) → Dec (nth xs i ≡ just y)
hitName xs i y with nth xs i
... | nothing = no′ (λ ())
... | just z with z ≟ y
... | yes′ refl = yes′ refl
... | no′ z≢y = no′ (λ eq → z≢y (just-inj eq))

bindM : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
bindM nothing _ = nothing
bindM (just x) f = f x

-- `just` only when the instantiated arguments have the declaration's arity.
sameLen : Decl → List Ty → Maybe Ty
sameLen d ts = lenOk (length ts) (np d) ts
  where
  lenOk : ℕ → ℕ → List Ty → Maybe Ty
  lenOk nzero nzero us = just (dat d us)
  lenOk nzero (nsuc _) _ = nothing
  lenOk (nsuc _) nzero _ = nothing
  lenOk (nsuc m) (nsuc n) us = lenOk m n us

mutual
  inst : Decl → List Ty → Fld → Maybe Ty
  inst _ _ fNat = just nat
  inst _ _ (fBound _) = just nat
  inst _ _ fBit = just bit
  inst _ _ fUnit = just unit
  inst d as (fPair a b) =
    bindM (inst d as a) (λ A → bindM (inst d as b) (λ B → just (pair A B)))
  inst _ as (fPar i) = nth as i
  inst d as (fSelf fs) = bindM (instAll d as fs) (sameLen d)
  inst d as (fDat e fs) = bindM (instAll d as fs) (sameLen e)

  instAll : Decl → List Ty → List Fld → Maybe (List Ty)
  instAll _ _ [] = just []
  instAll d as (f ∷ fs) =
    bindM (inst d as f) (λ A → bindM (instAll d as fs) (λ ts → just (A ∷ ts)))

-- The numeral a nat value denotes. A bounded field admits it when
-- that numeral is at most the declared bound.
toℕ : Val nat → ℕ
toℕ zero = nzero
toℕ (suc n) = nsuc (toℕ n)

-- A bounded nat field admits a nat at most its numeral. Every other
-- field is admitted by its type alone. A bound that is not a numeral
-- is not a field of this form.
fieldOk : Fld → ∀ {A} → Val A → Bool
fieldOk (fBound w) {A} v with ty≟ A nat
... | no′ _ = false
... | yes′ refl with toℕ v ≤?ℕ w
... | yes′ _ = true
... | no′ _ = false
fieldOk _ _ = true

-- A literal inhabits its type when `fits` is true. A constructor the
-- declaration does not have, a field of the wrong type, or a nat past
-- the numeral bound on that field, is false. The recursion follows
-- the spine of the value.
mutual
  fits : ∀ {A} → Val A → Bool
  fits zero = true
  fits (suc v) = fits v
  fits b0 = true
  fits b1 = true
  fits tt = true
  fits (tup a b) = fits a ∧ fits b
  fits (rec r) = fitsRow r
  fits (rep v) = fits v
  fits (con {d} {as} c sp) = fitsCtors (ctorsOf d) d as c sp

  fitsRow : ∀ {fs} → Row fs → Bool
  fitsRow noRow = true
  fitsRow (cell v r) = fits v ∧ fitsRow r

  fitsCtors : List Ctor → Decl → List Ty → String → Spine → Bool
  fitsCtors [] _ _ _ _ = false
  fitsCtors (ctor n fs ∷ cs) d as c sp with c ≟ n
  ... | no′ _ = fitsCtors cs d as c sp
  ... | yes′ _ = fitsFlds d as fs sp

  fitsFlds : Decl → List Ty → List Fld → Spine → Bool
  fitsFlds _ _ [] snil = true
  fitsFlds _ _ [] (scons _ _ _) = false
  fitsFlds _ _ (_ ∷ _) snil = false
  fitsFlds d as (f ∷ fs) (scons B v sp) with inst d as f
  ... | nothing = false
  ... | just A with ty≟ A B
  ... | no′ _ = false
  ... | yes′ refl = fieldOk f v ∧ fits v ∧ fitsFlds d as fs sp

------------------------------------------------------------------------
-- Variable context: list of (name, type) pairs
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Declarations the run table and the examples share. A constructor
-- the declaration does not have does not inhabit the type.
------------------------------------------------------------------------

boolDecl : Decl
boolDecl = mkDecl "Bool" nzero (ctor "true" [] ∷ ctor "false" [] ∷ [])

boolTy : Ty
boolTy = dat boolDecl []

frameDecl : Decl
frameDecl = mkDecl "Frame" nzero
  (ctor "data" [] ∷ ctor "trailers" [] ∷ ctor "headers" [] ∷ [])

frameTy : Ty
frameTy = dat frameDecl []

trueV : Val boolTy
trueV = con "true" snil

falseV : Val boolTy
falseV = con "false" snil

noneV : Val boolTy
noneV = con "none" snil

maybeDecl : Decl
maybeDecl = mkDecl "Maybe" (nsuc nzero)
  (ctor "nothing" [] ∷ ctor "just" (fPar nzero ∷ []) ∷ [])

maybeNat : Ty
maybeNat = dat maybeDecl (nat ∷ [])

maybeBool : Ty
maybeBool = dat maybeDecl (boolTy ∷ [])

nothingV : Val maybeNat
nothingV = con "nothing" snil

just0 : Val maybeNat
just0 = con "just" (scons nat zero snil)

justBit : Val maybeNat
justBit = con "just" (scons bit b0 snil)

justTrue : Val maybeBool
justTrue = con "just" (scons boolTy trueV snil)

justFalse : Val maybeBool
justFalse = con "just" (scons boolTy falseV snil)

itemDecl : Decl
itemDecl = mkDecl "Item" nzero (ctor "self" [] ∷ ctor "other" [] ∷ [])

itemTy : Ty
itemTy = dat itemDecl []

selfV : Val itemTy
selfV = con "self" snil

otherV : Val itemTy
otherV = con "other" snil

nothingB : Val maybeBool
nothingB = con "nothing" snil

------------------------------------------------------------------------
-- A run term. A variable is one of the definition's parameters, de
-- Bruijn, with 0 the last parameter. A call names a definition. The
-- table is ordered latest first, so the tail of a definition is
-- every definition declared before it. Evaluation of a call recurses
-- on that tail and on the term. Before the body is evaluated, every
-- call in it must name a definition in that tail. A name that is not
-- in the tail, including the definition itself and any definition
-- declared later, does not evaluate.
------------------------------------------------------------------------

mutual
  data Arm : Set where
    arm : String → RTm → Arm

  data RTm : Set where
    rNat : ℕ → RTm
    rSuc : RTm → RTm
    rBit0 : RTm
    rBit1 : RTm
    rUnit : RTm
    rPair : RTm → RTm → RTm
    rVar : ℕ → RTm
    rCon : String → List RTm → RTm
    rMatch : RTm → List Arm → RTm
    rMatchNat : RTm → RTm → RTm → RTm
    rCall : String → List RTm → RTm

data RDef : Set where
  rdef : String → List Ty → Ty → RTm → RDef

-- `mark self` is `true`. `mark other` is `false`.
markBody : RTm
markBody = rMatch (rVar nzero)
  (arm "self" (rCon "true" []) ∷ arm "other" (rCon "false" []) ∷ [])

markRun : RDef
markRun = rdef "mark" (itemTy ∷ []) boolTy markBody

-- `effective self` is `just (mark self)`. `effective other` is `nothing`.
effBody : RTm
effBody = rMatch (rVar nzero)
  ( arm "self" (rCon "just" (rCall "mark" (rVar nzero ∷ []) ∷ []))
  ∷ arm "other" (rCon "nothing" [])
  ∷ [])

effectiveRun : RDef
effectiveRun = rdef "effective" (itemTy ∷ []) maybeBool effBody

countRun : RDef
countRun = rdef "count" [] nat (rSuc (rNat nzero))

badRun : RDef
badRun = rdef "bad" [] boolTy (rCon "none" [])

-- `size self` is 0. `size other` is 2.
sizeBody : RTm
sizeBody = rMatch (rVar nzero)
  ( arm "self" (rNat nzero)
  ∷ arm "other" (rSuc (rSuc (rNat nzero)))
  ∷ [])

sizeRun : RDef
sizeRun = rdef "size" (itemTy ∷ []) nat sizeBody

-- Calls itself, so the prefix does not contain the callee.
loopRun : RDef
loopRun = rdef "loop" (itemTy ∷ []) nat (rCall "loop" (rVar nzero ∷ []))

-- The zero arm returns the second argument. The successor arm calls
-- `plus`. The body calls itself, so neither argument is evaluated.
plusBody : RTm
plusBody = rMatchNat (rVar (nsuc nzero)) (rVar nzero)
  (rSuc (rCall "plus" (rVar nzero ∷ rVar (nsuc (nsuc nzero)) ∷ [])))

plusRun : RDef
plusRun = rdef "plus" (nat ∷ nat ∷ []) nat plusBody

-- Declared before `late`, and its body calls `late`.
earlyRun : RDef
earlyRun = rdef "early" [] nat (rCall "late" [])

lateRun : RDef
lateRun = rdef "late" [] nat (rNat nzero)

-- `lateFrame` is false on headers and true on the other frames.
lateFrameBody : RTm
lateFrameBody = rMatch (rVar nzero)
  ( arm "data" (rCon "true" [])
  ∷ arm "trailers" (rCon "true" [])
  ∷ arm "headers" (rCon "false" [])
  ∷ [])

lateFrameRun : RDef
lateFrameRun = rdef "lateFrame" (frameTy ∷ []) boolTy lateFrameBody

-- The `just` arm reads the field. An empty field environment does not.
onJustBody : RTm
onJustBody = rMatch (rVar nzero)
  ( arm "nothing" (rCon "true" [])
  ∷ arm "just" (rMatchNat (rVar nzero) (rCon "false" []) (rCon "true" []))
  ∷ [])

onJustRun : RDef
onJustRun = rdef "onJust" (maybeNat ∷ []) boolTy onJustBody

-- `grant true` is `true`. `grant false` is `false`.
grantBody : RTm
grantBody = rMatch (rVar nzero)
  (arm "true" (rCon "true" []) ∷ arm "false" (rCon "false" []) ∷ [])

grantRun : RDef
grantRun = rdef "grant" (boolTy ∷ []) boolTy grantBody

-- `lateBool nothing` is false. `lateBool (just b)` is `b`.
lateBoolBody : RTm
lateBoolBody = rMatch (rVar nzero)
  ( arm "nothing" (rCon "false" [])
  ∷ arm "just" (rVar nzero)
  ∷ [])

lateBoolRun : RDef
lateBoolRun = rdef "lateBool" (maybeBool ∷ []) boolTy lateBoolBody

-- Latest first. The tail of a definition is the earlier prefix.
runs : List RDef
runs =
  lateBoolRun ∷ grantRun ∷ onJustRun ∷ lateFrameRun ∷ plusRun ∷ loopRun ∷ lateRun
    ∷ sizeRun ∷ badRun ∷ countRun ∷ effectiveRun ∷ markRun ∷ earlyRun ∷ []

-- Every call in the body names a definition in the prefix. The check
-- walks the whole term, so a call in an arm that is not taken still
-- refuses the definition.
mutual
  namedBefore : List RDef → String → Bool
  namedBefore [] _ = false
  namedBefore (rdef n _ _ _ ∷ Δ) f = namedHere (f ≟ n) Δ f

  namedHere : {f n : String} → Dec (f ≡ n) → List RDef → String → Bool
  namedHere (yes′ _) _ _ = true
  namedHere (no′ _) Δ f = namedBefore Δ f

mutual
  callsBefore : List RDef → RTm → Bool
  callsBefore _ (rNat _) = true
  callsBefore Δ (rSuc t) = callsBefore Δ t
  callsBefore _ rBit0 = true
  callsBefore _ rBit1 = true
  callsBefore _ rUnit = true
  callsBefore Δ (rPair a b) = callsBefore Δ a ∧ callsBefore Δ b
  callsBefore _ (rVar _) = true
  callsBefore Δ (rCon _ ts) = callsAll Δ ts
  callsBefore Δ (rMatch t as) = callsBefore Δ t ∧ armsBefore Δ as
  callsBefore Δ (rMatchNat t z s) =
    callsBefore Δ t ∧ callsBefore Δ z ∧ callsBefore Δ s
  callsBefore Δ (rCall f ts) = namedBefore Δ f ∧ callsAll Δ ts

  callsAll : List RDef → List RTm → Bool
  callsAll _ [] = true
  callsAll Δ (t ∷ ts) = callsBefore Δ t ∧ callsAll Δ ts

  armsBefore : List RDef → List Arm → Bool
  armsBefore _ [] = true
  armsBefore Δ (arm _ b ∷ as) = callsBefore Δ b ∧ armsBefore Δ as

------------------------------------------------------------------------
-- Evaluate a term against a prefix. `apply` steps to the tail when
-- the name matches, and that tail is structurally smaller.
------------------------------------------------------------------------

data Raw : Set where
  rawNat  : ℕ → Raw
  rawBit  : Val bit → Raw
  rawUnit : Raw
  rawPair : Raw → Raw → Raw
  rawRec  : List Raw → Raw
  rawVec  : Raw → Raw
  rawCon  : String → List Raw → Raw

Env : Set
Env = List Raw

nthRaw : List Raw → ℕ → Maybe Raw
nthRaw [] _ = nothing
nthRaw (x ∷ _) nzero = just x
nthRaw (_ ∷ xs) (nsuc n) = nthRaw xs n

envOf : List Raw → Env
envOf [] = []
envOf (v ∷ vs) = envOf vs ++ (v ∷ [])

mutual
  eval : List RDef → RTm → Env → Maybe Raw
  eval _ (rNat n) _ = just (rawNat n)
  eval Δ (rSuc t) env = bindM (eval Δ t env) sucRaw
  eval _ rBit0 _ = just (rawBit b0)
  eval _ rBit1 _ = just (rawBit b1)
  eval _ rUnit _ = just rawUnit
  eval Δ (rPair a b) env =
    bindM (eval Δ a env) (λ a′ → bindM (eval Δ b env) (λ b′ → just (rawPair a′ b′)))
  eval _ (rVar i) env = nthRaw env i
  eval Δ (rCon c ts) env = bindM (evals Δ ts env) (λ vs → just (rawCon c vs))
  eval Δ (rCall f ts) env = bindM (evals Δ ts env) (apply Δ f)
  eval Δ (rMatch t arms) env = bindM (eval Δ t env) (matchArms Δ arms env)
  eval Δ (rMatchNat t z s) env = bindM (eval Δ t env) (matchNat Δ z s env)

  evals : List RDef → List RTm → Env → Maybe (List Raw)
  evals _ [] _ = just []
  evals Δ (t ∷ ts) env =
    bindM (eval Δ t env) (λ v → bindM (evals Δ ts env) (λ vs → just (v ∷ vs)))

  sucRaw : Raw → Maybe Raw
  sucRaw (rawNat n) = just (rawNat (nsuc n))
  sucRaw _ = nothing

  apply : List RDef → String → List Raw → Maybe Raw
  apply [] _ _ = nothing
  apply (rdef n ts _ body ∷ Δ) f args =
    applyHere (f ≟ n) (length args ≟ℕ length ts) Δ body f args

  applyHere :
    {f n : String} {k ar : ℕ} →
    Dec (f ≡ n) → Dec (k ≡ ar) → List RDef → RTm → String → List Raw → Maybe Raw
  applyHere (yes′ _) (yes′ _) Δ body _ args with callsBefore Δ body
  ... | true = eval Δ body (envOf args)
  ... | false = nothing
  applyHere (yes′ _) (no′ _) _ _ _ _ = nothing
  applyHere (no′ _) _ Δ _ f args = apply Δ f args

  matchNat : List RDef → RTm → RTm → Env → Raw → Maybe Raw
  matchNat Δ z _ env (rawNat nzero) = eval Δ z env
  matchNat Δ _ s env (rawNat (nsuc n)) = eval Δ s (rawNat n ∷ env)
  matchNat _ _ _ _ _ = nothing

  matchArms : List RDef → List Arm → Env → Raw → Maybe Raw
  matchArms _ [] _ _ = nothing
  matchArms Δ (arm c b ∷ as) env (rawCon d fs) =
    matchCon (c ≟ d) Δ as b fs env d
  matchArms Δ (arm c b ∷ as) env (rawBit b0) =
    matchNamed (c ≟ "b0") Δ as b env (rawBit b0)
  matchArms Δ (arm c b ∷ as) env (rawBit b1) =
    matchNamed (c ≟ "b1") Δ as b env (rawBit b1)
  matchArms Δ (_ ∷ as) env v@(rawNat _) = matchArms Δ as env v
  matchArms Δ (_ ∷ as) env v@rawUnit = matchArms Δ as env v
  matchArms Δ (_ ∷ as) env v@(rawPair _ _) = matchArms Δ as env v
  matchArms Δ (_ ∷ as) env v@(rawRec _) = matchArms Δ as env v
  matchArms Δ (_ ∷ as) env v@(rawVec _) = matchArms Δ as env v

  matchCon :
    {c d : String} → Dec (c ≡ d) → List RDef → List Arm → RTm →
    List Raw → Env → String → Maybe Raw
  matchCon (yes′ _) Δ _ b fs env _ = eval Δ b (envOf fs ++ env)
  matchCon (no′ _) Δ as _ fs env d = matchArms Δ as env (rawCon d fs)

  matchNamed :
    {c x : String} → Dec (c ≡ x) → List RDef → List Arm → RTm →
    Env → Raw → Maybe Raw
  matchNamed (yes′ _) Δ _ b env _ = eval Δ b env
  matchNamed (no′ _) Δ as _ env v = matchArms Δ as env v

mutual
  findCtor : List Ctor → String → Maybe (List Fld)
  findCtor [] _ = nothing
  findCtor (ctor n fs ∷ cs) c = findHere (c ≟ n) fs cs c

  findHere : {c n : String} → Dec (c ≡ n) → List Fld → List Ctor → String → Maybe (List Fld)
  findHere (yes′ _) fs _ _ = just fs
  findHere (no′ _) _ cs c = findCtor cs c

mutual
  rawOf : ∀ {A} → Val A → Maybe Raw
  rawOf zero = just (rawNat nzero)
  rawOf (suc v) = bindM (rawOf v) (λ r → sucRaw r)
  rawOf b0 = just (rawBit b0)
  rawOf b1 = just (rawBit b1)
  rawOf tt = just rawUnit
  rawOf (tup a b) =
    bindM (rawOf a) (λ a′ → bindM (rawOf b) (λ b′ → just (rawPair a′ b′)))
  rawOf (con c sp) = bindM (rawSpine sp) (λ vs → just (rawCon c vs))
  rawOf (rec row) = bindM (rawRow row) (λ rs → just (rawRec rs))
  rawOf (rep v) = bindM (rawOf v) (λ r → just (rawVec r))

  rawRow : ∀ {fs} → Row fs → Maybe (List Raw)
  rawRow noRow = just []
  rawRow (cell v row) =
    bindM (rawOf v) (λ r → bindM (rawRow row) (λ rs → just (r ∷ rs)))

  rawSpine : Spine → Maybe (List Raw)
  rawSpine snil = just []
  rawSpine (scons _ v sp) =
    bindM (rawOf v) (λ r → bindM (rawSpine sp) (λ rs → just (r ∷ rs)))

mutual
  cast : (A : Ty) → Raw → Maybe (Val A)
  cast nat (rawNat nzero) = just zero
  cast nat (rawNat (nsuc n)) = bindM (cast nat (rawNat n)) (λ v → just (suc v))
  cast bit (rawBit b0) = just b0
  cast bit (rawBit b1) = just b1
  cast unit rawUnit = just tt
  cast (pair A B) (rawPair a b) =
    bindM (cast A a) (λ a′ → bindM (cast B b) (λ b′ → just (tup a′ b′)))
  cast (rec fs) (rawRec rs) = bindM (castRow fs rs) (λ row → just (rec row))
  cast (vec A _) (rawVec r) = bindM (cast A r) (λ v → just (rep v))
  cast (dat d as) (rawCon c rs) = castFound d as c rs (findCtor (ctorsOf d) c)
  cast _ _ = nothing

  castRow : (fs : Fields) → List Raw → Maybe (Row fs)
  castRow noFields [] = just noRow
  castRow (named _ A fs) (r ∷ rs) =
    bindM (cast A r) (λ v → bindM (castRow fs rs) (λ row → just (cell v row)))
  castRow _ _ = nothing

  castFound :
    (d : Decl) (as : List Ty) (c : String) (rs : List Raw) →
    Maybe (List Fld) → Maybe (Val (dat d as))
  castFound d as c rs (just fs) =
    bindM (castFlds d as fs rs) (λ sp → just (con {d} {as} c sp))
  castFound d as c [] nothing = just (con {d} {as} c snil)
  castFound _ _ _ (_ ∷ _) nothing = nothing

  castFlds : Decl → List Ty → List Fld → List Raw → Maybe Spine
  castFlds _ _ [] [] = just snil
  castFlds d as (f ∷ fs) (r ∷ rs) =
    bindM (inst d as f) (λ A →
      bindM (cast A r) (λ v →
        bindM (castFlds d as fs rs) (λ sp → just (scons A v sp))))
  castFlds _ _ _ _ = nothing

mutual
  evalExpr : ∀ {A} → ValExpr A → Maybe (Val A)
  evalExpr (lit v) = just v
  evalExpr (var _) = nothing
  evalExpr (call {A} f as) =
    bindM (evalArgs as) (λ vs → bindM (apply runs f vs) (cast A))

  evalArgs : List VArg → Maybe (List Raw)
  evalArgs [] = just []
  evalArgs (varg _ e ∷ as) =
    bindM (evalArg e) (λ v → bindM (evalArgs as) (λ vs → just (v ∷ vs)))

  evalArg : ∀ {B} → ValExpr B → Maybe Raw
  evalArg (lit v) = rawOf v
  evalArg (var _) = nothing
  evalArg (call {B} f as) = bindM (evalExpr (call {B} f as)) rawOf

-- A name in an argument is unknown until the meeting supplies it.
-- A call that mentions one is checked by the run's declared type.
mutual
  mentions : ∀ {A} → ValExpr A → Bool
  mentions (lit _) = false
  mentions (var _) = true
  mentions (call _ as) = mentionsAll as

  mentionsAll : List VArg → Bool
  mentionsAll [] = false
  mentionsAll (varg _ e ∷ as) = mentions e ∨ mentionsAll as

bind-skip : ∀ {A B : Set} (m : Maybe A) (f : A → Maybe B) →
  (∀ x → f x ≡ nothing) → bindM m f ≡ nothing
bind-skip nothing _ _ = refl
bind-skip (just x) f p rewrite p x = refl

mutual
  evalArg-mention : ∀ {A} (e : ValExpr A) → mentions e ≡ true → evalArg e ≡ nothing
  evalArg-mention (lit _) ()
  evalArg-mention (var _) _ = refl
  evalArg-mention (call _ as) m rewrite evalArgs-mention as m = refl

  evalArgs-mention : (as : List VArg) → mentionsAll as ≡ true → evalArgs as ≡ nothing
  evalArgs-mention [] ()
  evalArgs-mention (varg _ e ∷ as) m = step (mentions e) m refl
    where
    step : (b : Bool) → b ∨ mentionsAll as ≡ true → mentions e ≡ b →
           evalArgs (varg _ e ∷ as) ≡ nothing
    step true _ eq rewrite evalArg-mention e eq = refl
    step false p _ =
      bind-skip (evalArg e) (λ v → bindM (evalArgs as) (λ vs → just (v ∷ vs)))
        (λ v → cong (λ r → bindM r (λ vs → just (v ∷ vs))) (evalArgs-mention as p))

closed-mention : ∀ {A} (f : String) (as : List VArg) →
  mentionsAll as ≡ true → evalExpr (call {A} f as) ≡ nothing
closed-mention f as mn rewrite evalArgs-mention as mn = refl

-- The run, its parameter types, its codomain, and the earlier prefix.
findRun : List RDef → String → Maybe (List Ty × Ty × RTm × List RDef)
findRun [] _ = nothing
findRun (rdef n ts cod body ∷ Δ) f with f ≟ n
... | yes′ _ = just (ts , cod , body , Δ)
... | no′ _ = findRun Δ f

tsAt : Maybe (List Ty × Ty × RTm × List RDef) → List Ty
tsAt (just (ts , _ , _ , _)) = ts
tsAt nothing = []

codAt : Maybe (List Ty × Ty × RTm × List RDef) → Ty
codAt (just (_ , cod , _ , _)) = cod
codAt nothing = nat

beforeAt : Maybe (List Ty × Ty × RTm × List RDef) → Bool
beforeAt (just (_ , _ , body , Δ)) = callsBefore Δ body
beforeAt nothing = false

-- An argument of a typed call is a literal or a bound name. A nested
-- call is outside this fragment.
data ArgOk (Γ : Ctx) : Ty → VArg → Set where
  arg-lit : ∀ {B} {v : Val B} → fits v ≡ true → ArgOk Γ B (varg B (lit v))
  arg-var : ∀ {B x} → x ∈ Γ ∷ B → ArgOk Γ B (varg B (var {B} x))

data ArgsOk (Γ : Ctx) : List Ty → List VArg → Set where
  args-nil  : ArgsOk Γ [] []
  args-cons : ∀ {B bs a as} →
    ArgOk Γ B a → ArgsOk Γ bs as → ArgsOk Γ (B ∷ bs) (a ∷ as)

-- A literal is in scope when it inhabits its type. A variable is in
-- scope when the innermost binding of its name has that type. A call
-- with no bound name is in scope when evaluation returns a value of
-- the claimed type and that value inhabits the type. A call that
-- mentions a bound name is in scope when the run is an earlier
-- definition, each argument is a literal or a bound name of the
-- parameter's type, and the declared codomain is the payload. The
-- context does not bind the function: a run definition has no seat.
data ValExprOk : Ctx → ∀ {A} → ValExpr A → Set where
  lit-ok  : ∀ {Γ A} {v : Val A} → fits v ≡ true → ValExprOk Γ (lit v)
  var-ok  : ∀ {Γ A} {x : String} → x ∈ Γ ∷ A → ValExprOk Γ (var {A} x)
  call-ok : ∀ {Γ A f as v} →
    evalExpr (call {A} f as) ≡ just v →
    fits v ≡ true →
    ValExprOk Γ (call {A} f as)
  -- The run is whatever `findRun` returns. The fields are that
  -- result's readiness, codomain, and parameter types, so a refusal
  -- does not invert the lookup.
  call-ty : ∀ {Γ A f as} →
    mentionsAll as ≡ true →
    beforeAt (findRun runs f) ≡ true →
    codAt (findRun runs f) ≡ A →
    ArgsOk Γ (tsAt (findRun runs f)) as →
    ValExprOk Γ (call {A} f as)

sentOf : ∀ {A} → Maybe (Val A) → Bool
sentOf nothing = false
sentOf (just v) = fits v

-- A bound variable inhabits the type it was bound at. A call inhabits
-- the type when evaluation returns an inhabitant.
sent : ∀ {A} → ValExpr A → Bool
sent (lit v) = fits v
sent (var _) = true
sent {A} (call f as) = sentOf (evalExpr (call {A} f as))

decTrue : (b : Bool) → Dec (b ≡ true)
decTrue true = yes′ refl
decTrue false = no′ false≢true

sent? : ∀ {A} (v : ValExpr A) → Dec (sent v ≡ true)
sent? (lit v) = decTrue (fits v)
sent? (var _) = yes′ refl
sent? {A} (call f as) = decTrue (sent {A} (call f as))

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
applyTys : Idx → List Ty → List Ty

applyTy none A = A
applyTy ρ@(bind _ _ _) nat = nat
applyTy ρ@(bind _ _ _) bit = bit
applyTy ρ@(bind _ _ _) unit = unit
applyTy ρ@(bind _ _ _) (pair A B) = pair (applyTy ρ A) (applyTy ρ B)
applyTy ρ@(bind _ _ _) (rec fs) = rec (applyFields ρ fs)
applyTy ρ@(bind _ _ _) (vec A e) = vec (applyTy ρ A) (applyNExp ρ e)
applyTy ρ@(bind _ _ _) (dat d as) = dat d (applyTys ρ as)

applyFields none fs = fs
applyFields ρ@(bind _ _ _) noFields = noFields
applyFields ρ@(bind _ _ _) (named n A fs) = named n (applyTy ρ A) (applyFields ρ fs)

applyTys none ts = ts
applyTys _ [] = []
applyTys ρ@(bind _ _ _) (A ∷ ts) = applyTy ρ A ∷ applyTys ρ ts

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
applyProto ρ@(bind _ _ _) (pcase scrut arms) = pcase scrut (applyArms ρ arms)
  where
  applyArms : Idx → List (String × Proto) → List (String × Proto)
  applyArms _ [] = []
  applyArms σ ((c , S) ∷ as) = (c , applyProto σ S) ∷ applyArms σ as

eqTy : Ty → Ty → Bool
eqTy A B with ty≟ A B
... | yes′ _ = true
... | no′ _ = false

eqN : NExp → NExp → Bool
eqN e f with nexp≟ e f
... | yes′ _ = true
... | no′ _ = false

eqℕ : ℕ → ℕ → Bool
eqℕ m n with m ≟ℕ n
... | yes′ _ = true
... | no′ _ = false

strsEq : List String → List String → Bool
strsEq [] [] = true
strsEq (x ∷ xs) (y ∷ ys) = (x == y) ∧ strsEq xs ys
strsEq _ _ = false

tagEq : Tag → Tag → Bool
tagEq (tagNat x m) (tagNat y n) = (x == y) ∧ eqℕ m n
tagEq (tagBit x) (tagBit y) = x == y
tagEq (tagDat x cs) (tagDat y ds) = (x == y) ∧ strsEq cs ds
tagEq _ _ = false

tagsEq : List Tag → List Tag → Bool
tagsEq [] [] = true
tagsEq (t ∷ ts) (u ∷ us) = tagEq t u ∧ tagsEq ts us
tagsEq _ _ = false

scrutEq : Scrut → Scrut → Bool
scrutEq (byVal x) (byVal y) = x == y
scrutEq (byRun f x R) (byRun g y S) = (f == g) ∧ (x == y) ∧ eqTy R S
scrutEq (bySplit f ts R) (bySplit g us S) = (f == g) ∧ tagsEq ts us ∧ eqTy R S
scrutEq _ _ = false

-- Syntactic equality of protocols. A sender whose value is not known
-- continues only when every arm is this same protocol.
mutual
  protoEq : Proto → Proto → Bool
  protoEq end end = true
  protoEq (send A S) (send B T) = eqTy A B ∧ protoEq S T
  protoEq (recv A S) (recv B T) = eqTy A B ∧ protoEq S T
  protoEq (dsend x A S) (dsend y B T) = (x == y) ∧ eqTy A B ∧ protoEq S T
  protoEq (drecv x A S) (drecv y B T) = (x == y) ∧ eqTy A B ∧ protoEq S T
  protoEq (esend x e S) (esend y f T) = (x == y) ∧ eqN e f ∧ protoEq S T
  protoEq (erecv x e S) (erecv y f T) = (x == y) ∧ eqN e f ∧ protoEq S T
  protoEq (isend x S T) (isend y U V) = (x == y) ∧ protoEq S U ∧ protoEq T V
  protoEq (irecv x S T) (irecv y U V) = (x == y) ∧ protoEq S U ∧ protoEq T V
  protoEq (choose S T) (choose U V) = protoEq S U ∧ protoEq T V
  protoEq (branch S T) (branch U V) = protoEq S U ∧ protoEq T V
  protoEq (pcase s as) (pcase t bs) = scrutEq s t ∧ armsEq as bs
  protoEq _ _ = false

  armsEq : List (String × Proto) → List (String × Proto) → Bool
  armsEq [] [] = true
  armsEq ((c , S) ∷ as) ((d , T) ∷ bs) = (c == d) ∧ protoEq S T ∧ armsEq as bs
  armsEq _ _ = false

natExp : ValExpr nat → NExp
natExp (lit v) = nlit (toℕ v)
natExp (var x) = nvar x
natExp (call f as) = computedNat (evalExpr (call {nat} f as))
  where
  -- A failed evaluation is not a numeral and not a name in scope.
  computedNat : Maybe (Val nat) → NExp
  computedNat (just v) = nlit (toℕ v)
  computedNat nothing = nvar " "

-- A length comes from a nat. Another payload does not instantiate one.
ixOf : (A : Ty) → ValExpr A → NExp
ixOf nat v = natExp v
ixOf bit _ = nlit nzero
ixOf unit _ = nlit nzero
ixOf (pair _ _) _ = nlit nzero
ixOf (rec _) _ = nlit nzero
ixOf (vec _ _) _ = nlit nzero
ixOf (dat _ _) _ = nlit nzero

------------------------------------------------------------------------
-- The arm a value selects. A bit's constructors are `b0` then `b1`.
-- A declared data type's constructors are the declaration's, in
-- order. A known value is a literal or a call the evaluator returns.
-- A variable is not known. A run is applied with that same evaluator,
-- and the result is cast to the result type written on the scrutinee.
-- A receiver probes each constructor. A field the run reads, whose
-- type is a bit or a declared data type, is split into the values of
-- that type. A field the run binds and does not read is not split. A
-- field that is not a finite split does not decide an arm.
------------------------------------------------------------------------

ctorNames : List Ctor → List String
ctorNames [] = []
ctorNames (ctor n _ ∷ cs) = n ∷ ctorNames cs

payCtors : Ty → Maybe (List String)
payCtors bit = just ("b0" ∷ "b1" ∷ [])
payCtors (dat d _) = just (ctorNames (ctorsOf d))
payCtors _ = nothing

armNames : List (String × Proto) → List String
armNames [] = []
armNames ((c , _) ∷ as) = c ∷ armNames as

namesEq : List String → List String → Bool
namesEq [] [] = true
namesEq (x ∷ xs) (y ∷ ys) = (x == y) ∧ namesEq xs ys
namesEq _ _ = false

------------------------------------------------------------------------
-- The numerals `0` … `w`. `natFrom n i` is `show i` through
-- `show (i + n − 1)`. There is no fuel and no budget: the recursion
-- is structural on the count. A bounded nat of bound `w` is this list
-- at `0`. A run's split is the cartesian product of one such list per
-- factor it reads. The length of that product is the product of the
-- widths, and that equality is `enum-size`.
------------------------------------------------------------------------

natFrom : ℕ → ℕ → List String
natFrom nzero _ = []
natFrom (nsuc k) i = show i ∷ natFrom k (nsuc i)

natArms : ℕ → List String
natArms w = natFrom (nsuc w) nzero

natFrom-len : ∀ n i → length (natFrom n i) ≡ n
natFrom-len nzero _ = refl
natFrom-len (nsuc k) i = cong nsuc (natFrom-len k (nsuc i))

natArms-len : ∀ w → length (natArms w) ≡ nsuc w
natArms-len w = natFrom-len (nsuc w) nzero

-- `k` below `n` is the label `show (i + k)`.
nth-from : ∀ n i k → nsuc k ≤ n → nth (natFrom n i) k ≡ just (show (i + k))
nth-from nzero _ _ ()
nth-from (nsuc n) i nzero (s≤s _) rewrite +-identityʳ i = refl
nth-from (nsuc n) i (nsuc k) (s≤s lt) rewrite +-suc i k = nth-from n (nsuc i) k lt

-- Every value in `0` … `w` occurs, at that index.
in-split : ∀ k w → k ≤ w → nth (natArms w) k ≡ just (show k)
in-split k w le = nth-from (nsuc w) nzero k (s≤s le)

nth-len : ∀ {A : Set} (xs : List A) k {x} → nth xs k ≡ just x → nsuc k ≤ length xs
nth-len [] _ ()
nth-len (_ ∷ _) nzero refl = s≤s z≤n
nth-len (_ ∷ xs) (nsuc k) eq = s≤s (nth-len xs k eq)

-- Every member of the split is an index within the bound.
split-bound : ∀ k w {s} → nth (natArms w) k ≡ just s → k ≤ w
split-bound k w eq =
  ≤-pred (subst (λ n → nsuc k ≤ n) (natArms-len w) (nth-len (natArms w) k eq))

-- One factor of a run split. A bounded nat contributes `w + 1` labels.
-- A bit contributes two. A declared data type contributes its constructors.
data Factor : Set where
  facNat  : ℕ → Factor
  facBit  : Factor
  facTags : List String → Factor

facWidth : Factor → ℕ
facWidth (facNat w) = nsuc w
facWidth facBit = 2
facWidth (facTags cs) = length cs

labelsOf : Factor → List String
labelsOf (facNat w) = natArms w
labelsOf facBit = "b0" ∷ "b1" ∷ []
labelsOf (facTags cs) = cs

labels-width : ∀ f → length (labelsOf f) ≡ facWidth f
labels-width (facNat w) = natArms-len w
labels-width facBit = refl
labels-width (facTags _) = refl

prodNs : List ℕ → ℕ
prodNs [] = nsuc nzero
prodNs (n ∷ ns) = n * prodNs ns

joinLabs : List String → List (List String) → List (List String)
joinLabs [] _ = []
joinLabs (x ∷ xs) ys = map (λ t → x ∷ t) ys ++ joinLabs xs ys

join-len : ∀ xs ys → length (joinLabs xs ys) ≡ length xs * length ys
join-len [] _ = refl
join-len (x ∷ xs) ys
  rewrite length-++ (map (λ t → x ∷ t) ys) {ys = joinLabs xs ys}
        | length-map (λ t → x ∷ t) ys
        | join-len xs ys = refl

cart : List (List String) → List (List String)
cart [] = [] ∷ []
cart (xs ∷ xss) = joinLabs xs (cart xss)

cart-len : ∀ xss → length (cart xss) ≡ prodNs (map length xss)
cart-len [] = refl
cart-len (xs ∷ xss) rewrite join-len xs (cart xss) | cart-len xss = refl

map-width : ∀ fs → map length (map labelsOf fs) ≡ map facWidth fs
map-width [] = refl
map-width (f ∷ fs) rewrite labels-width f | map-width fs = refl

enumFac : List Factor → List (List String)
enumFac fs = cart (map labelsOf fs)

-- The split of a run has exactly the product of the widths of the
-- factors it reads. The product is computed from those factors.
-- There is no limit, fuel, or budget on the count.
enum-size : ∀ fs → length (enumFac fs) ≡ prodNs (map facWidth fs)
enum-size fs rewrite cart-len (map labelsOf fs) | map-width fs = refl

*-one : ∀ n → n * nsuc nzero ≡ n
*-one nzero = refl
*-one (nsuc n) rewrite *-one n = refl

-- A bounded nat and one payload. The split has `(w + 1)` times the
-- number of constructors, which is the product of those two widths.
prod-card : ∀ w cs →
  length (enumFac (facNat w ∷ facTags cs ∷ [])) ≡ nsuc w * length cs
prod-card w cs rewrite enum-size (facNat w ∷ facTags cs ∷ []) | *-one (length cs) = refl

-- The splits of the constructors a run reads, laid end to end.
-- The length is the sum of the products of the field widths.
concat : ∀ {A : Set} → List (List A) → List A
concat [] = []
concat (xs ∷ xss) = xs ++ concat xss

sumNs : List ℕ → ℕ
sumNs [] = nzero
sumNs (n ∷ ns) = n + sumNs ns

sumProd : List (List Factor) → ℕ
sumProd gs = sumNs (map (λ fs → prodNs (map facWidth fs)) gs)

concat-len : ∀ {A : Set} (xss : List (List A)) → length (concat xss) ≡ sumNs (map length xss)
concat-len [] = refl
concat-len (xs ∷ xss) rewrite length-++ xs {ys = concat xss} | concat-len xss = refl

map-enum : ∀ gs → map length (map enumFac gs) ≡ map (λ fs → prodNs (map facWidth fs)) gs
map-enum [] = refl
map-enum (fs ∷ gs) rewrite enum-size fs | map-enum gs = refl

data-size : ∀ gs → length (concat (map enumFac gs)) ≡ sumProd gs
data-size gs rewrite concat-len (map enumFac gs) | map-enum gs = refl

-- A label the factor admits, and a tuple the product admits.
data Has (c : String) : List String → Set where
  has-z : ∀ {cs} → Has c (c ∷ cs)
  has-s : ∀ {d cs} → Has c cs → Has c (d ∷ cs)

data InLab : Factor → String → Set where
  lab-nat : ∀ {k w} → k ≤ w → InLab (facNat w) (show k)
  lab-b0  : InLab facBit "b0"
  lab-b1  : InLab facBit "b1"
  lab-tag : ∀ {c cs} → Has c cs → InLab (facTags cs) c

data Admitted : List Factor → List String → Set where
  adm-[] : Admitted [] []
  adm-∷  : ∀ {f fs x xs} → InLab f x → Admitted fs xs → Admitted (f ∷ fs) (x ∷ xs)

hasPos : ∀ {c cs} → Has c cs → ℕ
hasPos has-z = nzero
hasPos (has-s h) = nsuc (hasPos h)

labPos : ∀ {f s} → InLab f s → ℕ
labPos (lab-nat {k} _) = k
labPos lab-b0 = nzero
labPos lab-b1 = nsuc nzero
labPos (lab-tag h) = hasPos h

has-at : ∀ {c cs} (h : Has c cs) → nth cs (hasPos h) ≡ just c
has-at has-z = refl
has-at (has-s h) = has-at h

lab-at : ∀ {f s} (i : InLab f s) → nth (labelsOf f) (labPos i) ≡ just s
lab-at (lab-nat {k} {w} le) = in-split k w le
lab-at lab-b0 = refl
lab-at lab-b1 = refl
lab-at (lab-tag h) = has-at h

admPos : ∀ {fs labs} → Admitted fs labs → ℕ
admPos adm-[] = nzero
admPos (adm-∷ {fs = fs} i rest) = labPos i * length (enumFac fs) + admPos rest

nth-map-cons : ∀ (x : String) ys k {y} →
  nth ys k ≡ just y → nth (map (λ t → x ∷ t) ys) k ≡ just (x ∷ y)
nth-map-cons _ [] _ ()
nth-map-cons _ (_ ∷ _) nzero refl = refl
nth-map-cons x (_ ∷ ys) (nsuc k) eq = nth-map-cons x ys k eq

nth-left : ∀ {A : Set} (xs ys : List A) k → nsuc k ≤ length xs → nth (xs ++ ys) k ≡ nth xs k
nth-left [] _ _ ()
nth-left (_ ∷ _) _ nzero (s≤s _) = refl
nth-left (_ ∷ xs) ys (nsuc k) (s≤s le) = nth-left xs ys k le

nth-right : ∀ {A : Set} (xs ys : List A) k → nth (xs ++ ys) (length xs + k) ≡ nth ys k
nth-right [] _ _ = refl
nth-right (_ ∷ xs) ys k = nth-right xs ys k

nth-join : ∀ xs ys a b {x y} →
  nth xs a ≡ just x → nth ys b ≡ just y → nsuc b ≤ length ys →
  nth (joinLabs xs ys) (a * length ys + b) ≡ just (x ∷ y)
nth-join [] _ _ _ () _ _
nth-join (x ∷ xs) ys nzero b refl yb bb =
  trans
    (nth-left (map (λ t → x ∷ t) ys) (joinLabs xs ys) b
      (subst (λ n → nsuc b ≤ n) (sym (length-map (λ t → x ∷ t) ys)) bb))
    (nth-map-cons x ys b yb)
nth-join (h ∷ xs) ys (nsuc a) b {x = x} {y = y} eq yb bb =
  subst (λ n → nth (map (λ t → h ∷ t) ys ++ joinLabs xs ys) n ≡ just (x ∷ y))
    (sym (trans (+-assoc (length ys) (a * length ys) b)
           (cong (λ n → n + (a * length ys + b))
             (sym (length-map (λ t → h ∷ t) ys)))))
    (trans
      (nth-right (map (λ t → h ∷ t) ys) (joinLabs xs ys) (a * length ys + b))
      (nth-join xs ys a b eq yb bb))

-- Every tuple the factors admit occurs in the split, at the index
-- the widths assign it.
in-product : ∀ {fs labs} (a : Admitted fs labs) → nth (enumFac fs) (admPos a) ≡ just labs
in-product adm-[] = refl
in-product (adm-∷ {f} {fs} i rest) with in-product rest
... | ih =
  nth-join (labelsOf f) (enumFac fs) (labPos i) (admPos rest) (lab-at i) ih
    (nth-len (enumFac fs) (admPos rest) ih)

-- Every member of the split is a tuple the factors admit.
data Found {A : Set} (x : A) : List A → Set where
  found-z : ∀ {xs} → Found x (x ∷ xs)
  found-s : ∀ {y xs} → Found x xs → Found x (y ∷ xs)

found-++ : ∀ {A : Set} {z : A} (xs ys : List A) → Found z (xs ++ ys) → Found z xs ⊎ Found z ys
found-++ [] _ f = inj₂ f
found-++ (_ ∷ _) _ found-z = inj₁ found-z
found-++ (_ ∷ xs) ys (found-s f) with found-++ xs ys f
... | inj₁ g = inj₁ (found-s g)
... | inj₂ g = inj₂ g

inv-map : ∀ {x ys zs} → Found zs (map (λ t → x ∷ t) ys) →
  Σ (List String) (λ bs → zs ≡ x ∷ bs × Found bs ys)
inv-map {ys = []} ()
inv-map {ys = y ∷ _} found-z = y , refl , found-z
inv-map {ys = _ ∷ ys} (found-s f) with inv-map f
... | bs , eq , g = bs , eq , found-s g

from-left : ∀ x {xs ys zs} → Found zs (map (λ t → x ∷ t) ys) →
  Σ (String × List String)
    (λ p → zs ≡ proj₁ p ∷ proj₂ p × Found (proj₁ p) (x ∷ xs) × Found (proj₂ p) ys)
from-left x inn with inv-map inn
... | bs , refl , g = (x , bs) , refl , found-z , g

inv-join : ∀ xs ys zs → Found zs (joinLabs xs ys) →
  Σ (String × List String) (λ p → zs ≡ proj₁ p ∷ proj₂ p × Found (proj₁ p) xs × Found (proj₂ p) ys)
inv-join [] _ _ ()
inv-join (x ∷ xs) ys zs found with found-++ (map (λ t → x ∷ t) ys) (joinLabs xs ys) found
... | inj₁ inn = from-left x inn
... | inj₂ inn with inv-join xs ys zs inn
... | (a , bs) , eq , ha , hb = (a , bs) , eq , found-s ha , hb

found-nth : ∀ {A : Set} {x : A} {xs} → Found x xs → Σ ℕ (λ k → nth xs k ≡ just x)
found-nth found-z = nzero , refl
found-nth (found-s g) with found-nth g
... | k , eq = nsuc k , eq

lab-of : ∀ {f s} → Found s (labelsOf f) → InLab f s
lab-of {facNat w} h with found-nth h
... | k , eq =
  let le = split-bound k w eq in
  subst (InLab (facNat w)) (sym (just-inj (trans (sym eq) (in-split k w le)))) (lab-nat le)
lab-of {facBit} found-z = lab-b0
lab-of {facBit} (found-s found-z) = lab-b1
lab-of {facBit} (found-s (found-s ()))
lab-of {facTags cs} h = lab-tag (has-of h)
  where
  has-of : ∀ {c ds} → Found c ds → Has c ds
  has-of found-z = has-z
  has-of (found-s g) = has-s (has-of g)

member-admitted : ∀ {fs labs} → Found labs (enumFac fs) → Admitted fs labs
member-admitted {[]} found-z = adm-[]
member-admitted {[]} (found-s ())
member-admitted {f ∷ fs} found with inv-join (labelsOf f) (enumFac fs) _ found
... | (a , bs) , refl , ha , hb = adm-∷ (lab-of ha) (member-admitted hb)

labelled : Ty → List (String × Proto) → Bool
labelled A arms with payCtors A
... | nothing = false
... | just cs = namesEq cs (armNames arms)

known : ∀ {A} → ValExpr A → Maybe (Val A)
known (lit v) = just v
known (var _) = nothing
known (call f as) = evalExpr (call f as)

valCtor : ∀ {A} → Val A → Maybe String
valCtor b0 = just "b0"
valCtor b1 = just "b1"
valCtor (con c _) = just c
valCtor _ = nothing

findArm : String → List (String × Proto) → Maybe Proto
findArm _ [] = nothing
findArm c ((d , S) ∷ as) with c ≟ d
... | yes′ _ = just S
... | no′ _ = findArm c as

sameArms : List (String × Proto) → Maybe Proto
sameArms [] = nothing
sameArms ((_ , S) ∷ as) = agree S as
  where
  agree : Proto → List (String × Proto) → Maybe Proto
  agree S [] = just S
  agree S ((_ , T) ∷ bs) with protoEq S T
  ... | true = agree S bs
  ... | false = nothing

rawAt : Ty → String → Raw
rawAt bit "b0" = rawBit b0
rawAt bit "b1" = rawBit b1
rawAt bit _ = rawCon "" []
rawAt _ c = rawCon c []

evalAt : String → Ty → String → (R : Ty) → Maybe (Val R)
evalAt f A c R = bindM (apply runs f (rawAt A c ∷ [])) (cast R)

evalVal : ∀ {A} → String → Val A → (R : Ty) → Maybe (Val R)
evalVal f v R = bindM (rawOf v) (λ r → bindM (apply runs f (r ∷ [])) (cast R))

runReady : String → Bool
runReady f = readyAt runs f
  where
  readyAt : List RDef → String → Bool
  readyAt [] _ = false
  readyAt (rdef n ts _ body ∷ Δ) g with g ≟ n
  ... | no′ _ = readyAt Δ g
  ... | yes′ _ with length ts ≟ℕ (nsuc nzero)
  ... | no′ _ = false
  ... | yes′ _ = callsBefore Δ body

-- The protocol the sender continues as. `nothing` is not an arm:
-- the scrutinee is not the binder, the labels are not the
-- constructors, the run is not an earlier definition of one
-- argument, or the value does not select one arm. A variable
-- continues as the common protocol when every arm is that protocol.
selectProto : ∀ {A} → String → ValExpr A → Scrut → List (String × Proto) → Maybe Proto
selectProto {A} y v (byVal x) arms with x ≟ y
... | no′ _ = nothing
... | yes′ _ with labelled A arms
... | false = nothing
... | true with known v
... | nothing = sameArms arms
... | just u with valCtor u
... | nothing = nothing
... | just c = findArm c arms
selectProto {A} y v (byRun f x R) arms with x ≟ y
... | no′ _ = nothing
... | yes′ _ with labelled R arms
... | false = nothing
... | true with runReady f
... | false = nothing
... | true with known v
... | nothing = sameArms arms
... | just u with evalVal f u R
... | nothing = nothing
... | just r with valCtor r
... | nothing = nothing
... | just c = findArm c arms
selectProto _ _ (bySplit _ _ _) _ = nothing

zipVal : List (String × Proto) → List Proc → Maybe (List (Proc × Proto))
zipVal [] [] = just []
zipVal ((_ , S) ∷ as) (p ∷ ps) = bindM (zipVal as ps) (λ rs → just ((p , S) ∷ rs))
zipVal _ _ = nothing

-- `zipRun` and `zipCase` follow `splitOf`, below.

------------------------------------------------------------------------
-- A run is ready at an arity when that definition has that many
-- arguments and every call in its body names an earlier definition.
readyN : ℕ → String → Bool
readyN n f = readyAt runs f
  where
  readyAt : List RDef → String → Bool
  readyAt [] _ = false
  readyAt (rdef g ts _ body ∷ Δ) h with h ≟ g
  ... | no′ _ = readyAt Δ h
  ... | yes′ _ with length ts ≟ℕ n
  ... | no′ _ = false
  ... | yes′ _ = callsBefore Δ body

-- The protocol a run returns on these raw arguments, when the result
-- is a constructor written in the arms.
evalSplit : String → List Raw → Ty → List (String × Proto) → Maybe Proto
evalSplit f rs R arms =
  bindM (apply runs f rs) (λ r →
    bindM (cast R r) (λ v →
      bindM (valCtor v) (λ k → findArm k arms)))

-- A known nat at most `w` selects the arm named by its decimal.
-- An unknown nat selects the common arm, when every arm is that arm.
pickShown : ValExpr nat → ℕ → List (String × Proto) → Maybe Proto
pickShown v w arms with namesEq (natArms w) (armNames arms)
... | false = nothing
... | true with known v
... | nothing = sameArms arms
... | just u with toℕ u ≤?ℕ w
... | no′ _ = nothing
... | yes′ _ = findArm (show (toℕ u)) arms

pickRun : ValExpr nat → ℕ → String → Ty → List (String × Proto) → Maybe Proto
pickRun v w f R arms with readyN (nsuc nzero) f
... | false = nothing
... | true with labelled R arms
... | false = nothing
... | true with known v
... | nothing = sameArms arms
... | just u with toℕ u ≤?ℕ w
... | no′ _ = nothing
... | yes′ _ = evalSplit f (rawNat (toℕ u) ∷ []) R arms

payRaw : Ty → String → Raw
payRaw bit "b0" = rawBit b0
payRaw bit "b1" = rawBit b1
payRaw bit _ = rawBit b0
payRaw _ c = rawCon c []

-- The second value is the payload just sent. The first is the bounded
-- nat already in hand. Both are known, and the nat is at most `w`.
pickProd : ∀ {A} → ValExpr nat → ValExpr A → ℕ → String → Ty →
           List (String × Proto) → Maybe Proto
pickProd v u w f R arms with readyN (nsuc (nsuc nzero)) f
... | false = nothing
... | true with labelled R arms
... | false = nothing
... | true with known v
... | nothing = sameArms arms
... | just n with toℕ n ≤?ℕ w
... | no′ _ = nothing
... | yes′ _ with known u
... | nothing = sameArms arms
... | just b with rawOf b
... | nothing = nothing
... | just r = evalSplit f (rawNat (toℕ n) ∷ r ∷ []) R arms

-- `rowFrom n i` is the protocol at `i`, then `i + 1`, for `n` values.
rowFrom : String → Ty → List (String × Proto) → ℕ → ℕ → Maybe (List (String × Proto))
rowFrom _ _ _ _ nzero = just []
rowFrom f R arms i (nsuc k) =
  bindM (evalSplit f (rawNat i ∷ []) R arms) (λ S →
    bindM (rowFrom f R arms (nsuc i) k) (λ rest → just ((show i , S) ∷ rest)))

natRows : String → Ty → List (String × Proto) → ℕ → Maybe (List (String × Proto))
natRows f R arms w = rowFrom f R arms nzero (nsuc w)

colFrom : String → Raw → Ty → List (String × Proto) → ℕ → ℕ → Maybe (List (String × Proto))
colFrom _ _ _ _ _ nzero = just []
colFrom f second R arms i (nsuc k) =
  bindM (evalSplit f (rawNat i ∷ second ∷ []) R arms) (λ S →
    bindM (colFrom f second R arms (nsuc i) k) (λ rest → just ((show i , S) ∷ rest)))

colsFrom : String → Ty → List String → Ty → List (String × Proto) → ℕ →
           Maybe (List (List (String × Proto)))
colsFrom _ _ [] _ _ _ = just []
colsFrom f A (c ∷ cs) R arms w =
  bindM (colFrom f (payRaw A c) R arms nzero (nsuc w)) (λ col →
    bindM (colsFrom f A cs R arms w) (λ rest → just (col ∷ rest)))

-- One column per constructor of the payload, and in each column one
-- row per numeral `0` … `w`. Nothing when any tuple selects no arm.
prodGrid : ℕ → Ty → String → Ty → List (String × Proto) →
           Maybe (List (List (String × Proto)))
prodGrid w A f R arms with payCtors A
... | nothing = nothing
... | just cs = colsFrom f A cs R arms w

nthProto : List (String × Proto) → ℕ → Maybe Proto
nthProto [] _ = nothing
nthProto ((_ , S) ∷ _) nzero = just S
nthProto (_ ∷ as) (nsuc k) = nthProto as k

nthRow : List (String × Proto) → ℕ → Maybe (String × Proto)
nthRow [] _ = nothing
nthRow (row ∷ _) nzero = just row
nthRow (_ ∷ rows) (nsuc k) = nthRow rows k

-- Factors of a tag list, in source order. The last tag is the payload
-- the case stands on.
tagFac : Tag → Factor
tagFac (tagNat _ w) = facNat w
tagFac (tagBit _) = facBit
tagFac (tagDat _ cs) = facTags cs

tagsFac : List Tag → List Factor
tagsFac [] = []
tagsFac (t ∷ ts) = tagFac t ∷ tagsFac ts

tagLabs : Tag → List String
tagLabs (tagNat _ w) = natArms w
tagLabs (tagBit _) = "b0" ∷ "b1" ∷ []
tagLabs (tagDat _ cs) = cs

tagName : Tag → String
tagName (tagNat x _) = x
tagName (tagBit x) = x
tagName (tagDat x _) = x

lastTag : List Tag → Maybe Tag
lastTag [] = nothing
lastTag (t ∷ []) = just t
lastTag (_ ∷ t ∷ ts) = lastTag (t ∷ ts)

revApp : ∀ {A : Set} → List A → List A → List A
revApp [] ys = ys
revApp (x ∷ xs) ys = revApp xs (x ∷ ys)

rev : ∀ {A : Set} → List A → List A
rev xs = revApp xs []

-- Every factor but the one the case stands on.
dropLast : ∀ {A : Set} → List A → List A
dropLast [] = []
dropLast (_ ∷ []) = []
dropLast (x ∷ y ∷ xs) = x ∷ dropLast (y ∷ xs)

append-assoc : ∀ {A : Set} (xs ys zs : List A) →
  (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
append-assoc [] _ _ = refl
append-assoc (x ∷ xs) ys zs = cong (_∷_ x) (append-assoc xs ys zs)

×-inj₄ : ∀ {A B C D : Set} {a c : A} {b d : B} {p r : C} {q s : D} →
  (a , b , p , q) ≡ (c , d , r , s) →
  a ≡ c × b ≡ d × p ≡ r × q ≡ s
×-inj₄ refl = refl , refl , refl , refl

-- One point of a factor. The cartesian product is first-factor slowest,
-- the same order as `enumFac`.
data Pt : Set where
  pNat : ℕ → Pt
  pBit : Val bit → Pt
  pCon : String → Pt

ptRaw : Pt → Raw
ptRaw (pNat k) = rawNat k
ptRaw (pBit b) = rawBit b
ptRaw (pCon c) = rawCon c []

ptLab : Pt → String
ptLab (pNat k) = show k
ptLab (pBit b0) = "b0"
ptLab (pBit b1) = "b1"
ptLab (pCon c) = c

countFrom : ℕ → ℕ → List Pt
countFrom _ nzero = []
countFrom i (nsuc k) = pNat i ∷ countFrom (nsuc i) k

facPts : Factor → List Pt
facPts (facNat w) = countFrom nzero (nsuc w)
facPts facBit = pBit b0 ∷ pBit b1 ∷ []
facPts (facTags cs) = map pCon cs

joinPt : List Pt → List (List Pt) → List (List Pt)
joinPt [] _ = []
joinPt (x ∷ xs) ys = map (_∷_ x) ys ++ joinPt xs ys

cartPt : List (List Pt) → List (List Pt)
cartPt [] = [] ∷ []
cartPt (xs ∷ xss) = joinPt xs (cartPt xss)

ptsOf : List Factor → List (List Pt)
ptsOf fs = cartPt (map facPts fs)

rowPt : String → Ty → List (String × Proto) → List Pt → Maybe (List String × Proto)
rowPt f R arms pts =
  bindM (evalSplit f (map ptRaw pts) R arms) (λ S → just (map ptLab pts , S))

rowsPt : String → Ty → List (String × Proto) → List (List Pt) →
         Maybe (List (List String × Proto))
rowsPt _ _ _ [] = just []
rowsPt f R arms (p ∷ ps) =
  bindM (rowPt f R arms p) (λ row →
    bindM (rowsPt f R arms ps) (λ rest → just (row ∷ rest)))

-- The protocol at every tuple of the factor list. Nothing when any
-- tuple selects no arm. The length is the product of the widths.
wideRows : String → Ty → List (String × Proto) → List Factor →
           Maybe (List (List String × Proto))
wideRows f R arms fs = rowsPt f R arms (ptsOf fs)

agreeRows : Proto → List (List String × Proto) → Maybe Proto
agreeRows S [] = just S
agreeRows S ((_ , T) ∷ rs) with protoEq S T
... | true = agreeRows S rs
... | false = nothing

sameRows : List (List String × Proto) → Maybe Proto
sameRows [] = nothing
sameRows ((_ , S) ∷ rs) = agreeRows S rs

snocLast : List String → Maybe (List String × String)
snocLast [] = nothing
snocLast (x ∷ []) = just ([] , x)
snocLast (x ∷ xs) with snocLast xs
... | nothing = nothing
... | just (ys , z) = just ((x ∷ ys) , z)

keepLab : String → List (List String × Proto) → List (List String × Proto)
keepLab _ [] = []
keepLab lab ((xs , S) ∷ rs) with snocLast xs
... | nothing = keepLab lab rs
... | just (ys , z) with z ≟ lab
... | yes′ _ = (ys , S) ∷ keepLab lab rs
... | no′ _ = keepLab lab rs

-- A value read off a put. `gUnk` is a variable: the product continues
-- only when every arm is the same protocol.
data Got : Set where
  gVal : Raw → Got
  gUnk : Got

natGot : ValExpr nat → ℕ → Maybe Got
natGot v w with known v
... | nothing = just gUnk
... | just n with toℕ n ≤?ℕ w
... | yes′ _ = just (gVal (rawNat (toℕ n)))
... | no′ _ = nothing

payGot : ∀ {A} → ValExpr A → Maybe Got
payGot v with known v
... | nothing = just gUnk
... | just u with rawOf u
... | just r = just (gVal r)
... | nothing = nothing

mutual
  alignNat : List Tag → Proto → Proc → String → ℕ → ValExpr nat → Proc →
             Maybe (Proc × List Got)
  alignNat ts S P x w v Q with natGot v w
  ... | nothing = nothing
  ... | just g = alignGo ts S Q g
    where
    alignGo : List Tag → Proto → Proc → Got → Maybe (Proc × List Got)
    alignGo us T R h with align us T R
    ... | nothing = nothing
    ... | just (q , gs) = just (q , h ∷ gs)

  alignBit : List Tag → Proto → Proc → ValExpr bit → Maybe (Proc × List Got)
  alignBit ts S P v with payGot v
  ... | nothing = nothing
  ... | just g with align ts S P
  ... | nothing = nothing
  ... | just (q , gs) = just (q , g ∷ gs)

  alignDat : List Tag → Proto → Proc → ∀ {A} → ValExpr A → Maybe (Proc × List Got)
  alignDat ts S P v with payGot v
  ... | nothing = nothing
  ... | just g with align ts S P
  ... | nothing = nothing
  ... | just (q , gs) = just (q , g ∷ gs)

  -- The put spine of a wide product. Tags and actions are in source
  -- order. The case is the last protocol. The tail process is what
  -- remains after the last put.
  align : List Tag → Proto → Proc → Maybe (Proc × List Got)
  align [] (pcase (bySplit _ _ _) _) p = just (p , [])
  align (tagNat x w ∷ ts) (esend y (nlit n) S) (put nat v P) with x ≟ y
  ... | no′ _ = nothing
  ... | yes′ _ with w ≟ℕ n
  ... | no′ _ = nothing
  ... | yes′ _ = alignNat ts S P x w v P
  align (tagBit x ∷ ts) (dsend y B S) (put bit v P) with x ≟ y
  ... | no′ _ = nothing
  ... | yes′ _ with ty≟ B bit
  ... | no′ _ = nothing
  ... | yes′ _ = alignBit ts S P v
  align (tagDat x cs ∷ ts) (dsend y B S) (put A v P) with x ≟ y
  ... | no′ _ = nothing
  ... | yes′ _ with payCtors A
  ... | nothing = nothing
  ... | just ds with strsEq ds cs
  ... | false = nothing
  ... | true with ty≟ A B
  ... | no′ _ = nothing
  ... | yes′ _ = alignDat ts S P v
  align _ _ _ = nothing

readGots : List Got → Maybe (List Raw)
readGots [] = just []
readGots (gUnk ∷ _) = nothing
readGots (gVal r ∷ gs) with readGots gs
... | nothing = nothing
... | just rs = just (r ∷ rs)

anyUnk : List Got → Bool
anyUnk [] = false
anyUnk (gUnk ∷ _) = true
anyUnk (gVal _ ∷ gs) = anyUnk gs

pickRead : List Got → String → Ty → List (String × Proto) → Maybe Proto
pickRead gs f R arms with anyUnk gs
... | true = sameArms arms
... | false with readGots gs
... | nothing = nothing
... | just rs = evalSplit f rs R arms

splitAt : Proto → Maybe (String × List Tag × Ty × List (String × Proto))
splitAt (dsend _ _ S) = splitAt S
splitAt (esend _ (nlit _) S) = splitAt S
splitAt (esend _ (nvar _) _) = nothing
splitAt (pcase (bySplit f tags R) arms) = just (f , tags , R , arms)
splitAt _ = nothing

gUnk≢val : ∀ {r} → gUnk ≢ gVal r
gUnk≢val ()

shiftRead : ∀ {f R arms T} (pre : List Got) (g : Got) (gs : List Got) →
  pickRead ((pre ++ (g ∷ [])) ++ gs) f R arms ≡ just T →
  pickRead (pre ++ (g ∷ gs)) f R arms ≡ just T
shiftRead {f = f} {R = R} {arms = arms} {T = T} pre g gs pk =
  subst (λ as → pickRead as f R arms ≡ just T) (append-assoc pre (g ∷ []) gs) pk

unshiftRead : ∀ {f R arms T} (pre : List Got) (g : Got) (gs : List Got) →
  pickRead (pre ++ (g ∷ gs)) f R arms ≡ just T →
  pickRead ((pre ++ (g ∷ [])) ++ gs) f R arms ≡ just T
unshiftRead {f = f} {R = R} {arms = arms} {T = T} pre g gs pk =
  subst (λ as → pickRead as f R arms ≡ just T) (sym (append-assoc pre (g ∷ []) gs)) pk

-- The protocol is an argument. Inferring it from `splitAt` would ask
-- that function to be injective, and it is not.
splitTags : (proto : Proto) {f g : String} {ts us : List Tag} {R Q : Ty}
    {as bs : List (String × Proto)} →
  splitAt proto ≡ just (f , ts , R , as) →
  splitAt proto ≡ just (g , us , Q , bs) →
  ts ≡ us
splitTags _ p q =
  sym (proj₁ (proj₂ (×-inj₄ (just-inj (trans (sym q) p)))))

-- Two readings of one split name the same run, type, and arms.
splitQuad : (proto : Proto) {f g : String} {ts us : List Tag} {R Q : Ty}
    {as bs : List (String × Proto)} →
  splitAt proto ≡ just (f , ts , R , as) →
  splitAt proto ≡ just (g , us , Q , bs) →
  f ≡ g × ts ≡ us × R ≡ Q × as ≡ bs
splitQuad _ p q = ×-inj₄ (just-inj (trans (sym p) q))

-- The split of a dependent send is the case it carries. The arguments
-- are the reading, so a later proof does not solve them by inversion.
caseSplit : (y : String) (B : Ty) (f : String) (tags : List Tag) (R : Ty)
    (arms : List (String × Proto)) →
  splitAt (dsend y B (pcase (bySplit f tags R) arms)) ≡ just (f , tags , R , arms)
caseSplit _ _ _ _ _ _ = refl

readyQuad : ∀ {f f′ : String} {ts ts′ : List Tag} {R R′ : Ty}
    {as as′ : List (String × Proto)} →
  f ≡ f′ × ts ≡ ts′ × R ≡ R′ × as ≡ as′ →
  readyN (length ts) f ≡ false →
  readyN (length ts′) f′ ≡ true → ⊥
readyQuad (refl , refl , refl , refl) rd p = true≢false (trans (sym p) rd)

labQuad : ∀ {f f′ : String} {ts ts′ : List Tag} {R R′ : Ty}
    {as as′ : List (String × Proto)} →
  f ≡ f′ × ts ≡ ts′ × R ≡ R′ × as ≡ as′ →
  labelled R as ≡ false →
  labelled R′ as′ ≡ true → ⊥
labQuad (refl , refl , refl , refl) lb p = true≢false (trans (sym p) lb)

rowsQuad : ∀ {f f′ : String} {ts ts′ : List Tag} {R R′ : Ty}
    {as as′ : List (String × Proto)} {rows : List (List String × Proto)} →
  f ≡ f′ × ts ≡ ts′ × R ≡ R′ × as ≡ as′ →
  wideRows f R as (tagsFac ts) ≡ nothing →
  wideRows f′ R′ as′ (tagsFac ts′) ≡ just rows → ⊥
rowsQuad (refl , refl , refl , refl) wr p = just≢nothing (trans (sym p) wr)

lenQuad : ∀ {f f′ : String} {ts ts′ : List Tag} {R R′ : Ty}
    {as as′ : List (String × Proto)} {rows rows′ : List (List String × Proto)} →
  f ≡ f′ × ts ≡ ts′ × R ≡ R′ × as ≡ as′ →
  length rows ≢ prodNs (map facWidth (tagsFac ts)) →
  wideRows f R as (tagsFac ts) ≡ just rows →
  wideRows f′ R′ as′ (tagsFac ts′) ≡ just rows′ →
  length rows′ ≡ prodNs (map facWidth (tagsFac ts′)) → ⊥
lenQuad {ts = ts} (refl , refl , refl , refl) ¬len wr wr′ len =
  ¬len (subst (λ rs → length rs ≡ prodNs (map facWidth (tagsFac ts)))
          (just-inj (trans (sym wr′) wr)) len)

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
  call-le : ∀ {f as v e} →
    evalExpr (call {nat} f as) ≡ just v →
    Le Γ (lit v) e →
    Le Γ (call f as) e

data Owed (Γ : Ctx) (v : ValExpr nat) : Maybe NExp → Set where
  owed : ∀ {e} → Le Γ v e → Owed Γ v (just e)

-- The puts of a wide product, in source order. A nat owes its numeral
-- bound, so a variable is not a value of that factor. A bit or a data
-- value may be unknown. The tail process is what remains at the case.
data PutSpine (Γ : Ctx) : List Tag → Proto → Proc → Proc → List Got → Set where
  sp-case : ∀ {f ts R arms p} →
    PutSpine Γ [] (pcase (bySplit f ts R) arms) p p []
  sp-nat : ∀ {x w y n ts S v P Q r gs} →
    x ≡ y →
    w ≡ n →
    natGot v w ≡ just (gVal r) →
    Owed Γ v (just (nlit w)) →
    ValExprOk Γ v →
    PutSpine Γ ts S P Q gs →
    PutSpine Γ (tagNat x w ∷ ts) (esend y (nlit n) S) (put nat v P) Q
      (gVal r ∷ gs)
  sp-bit : ∀ {x y ts B S v P Q g gs} →
    x ≡ y →
    B ≡ bit →
    payGot v ≡ just g →
    ValExprOk Γ v →
    PutSpine Γ ts S P Q gs →
    PutSpine Γ (tagBit x ∷ ts) (dsend y B S) (put bit v P) Q (g ∷ gs)
  sp-dat : ∀ {x cs y A B ts S v P Q g gs ds} →
    x ≡ y →
    A ≡ B →
    payCtors A ≡ just ds →
    strsEq ds cs ≡ true →
    payGot v ≡ just g →
    ValExprOk Γ v →
    PutSpine Γ ts S P Q gs →
    PutSpine Γ (tagDat x cs ∷ ts) (dsend y B S) (put A v P) Q (g ∷ gs)

moveSpine : ∀ {Γ : Ctx} {ts ts′ : List Tag} {proto : Proto} {proc Q : Proc}
    {gs : List Got} {f f′ : String} {R R′ : Ty}
    {as as′ : List (String × Proto)} →
  f ≡ f′ × ts ≡ ts′ × R ≡ R′ × as ≡ as′ →
  PutSpine Γ ts′ proto proc Q gs →
  PutSpine Γ ts proto proc Q gs
moveSpine (refl , refl , refl , refl) spin = spin

movePick : ∀ {gs : List Got} {T : Proto} {f f′ : String} {ts ts′ : List Tag}
    {R R′ : Ty} {as as′ : List (String × Proto)} →
  f ≡ f′ × ts ≡ ts′ × R ≡ R′ × as ≡ as′ →
  pickRead gs f′ R′ as′ ≡ just T →
  pickRead gs f R as ≡ just T
movePick (refl , refl , refl , refl) pk = pk

-- A bit tag on a send whose value is not a bit has no spine.
badBitPut : ∀ {Γ x ts y B S A v P Q gs} →
  A ≢ bit →
  PutSpine Γ (tagBit x ∷ ts) (dsend y B S) (put A v P) Q gs → ⊥
badBitPut ¬A (sp-bit _ _ _ _ _) = ¬A refl

-- A nat tag is an evidence send. It is not a plain `dsend` spine.
dsendNat : ∀ {Γ a n ts y B S A v P Q gs} →
  PutSpine Γ (tagNat a n ∷ ts) (dsend y B S) (put A v P) Q gs → ⊥
dsendNat ()

castV : ∀ {A C} → A ≡ C → ValExpr A → ValExpr C
castV refl v = v

castSpine : ∀ {Γ A C tags y B S P Q gs} {v : ValExpr A} →
  (eq : A ≡ C) →
  PutSpine Γ tags (dsend y B S) (put C (castV eq v) P) Q gs →
  PutSpine Γ tags (dsend y B S) (put A v P) Q gs
castSpine refl spin = spin

-- A continuation that is not itself a case. `dput-ok` is that
-- continuation. A case is `dput-arm`: the value selects one arm.
data Plain : Proto → Set where
  plain-end    : Plain end
  plain-send   : ∀ {A S} → Plain (send A S)
  plain-recv   : ∀ {A S} → Plain (recv A S)
  plain-dsend  : ∀ {x A S} → Plain (dsend x A S)
  plain-drecv  : ∀ {x A S} → Plain (drecv x A S)
  plain-esend  : ∀ {x e S} → Plain (esend x e S)
  plain-erecv  : ∀ {x e S} → Plain (erecv x e S)
  plain-isend  : ∀ {x S T} → Plain (isend x S T)
  plain-irecv  : ∀ {x S T} → Plain (irecv x S T)
  plain-choose : ∀ {S T} → Plain (choose S T)
  plain-branch : ∀ {S T} → Plain (branch S T)

plain-not : ∀ {scrut arms} → Plain (pcase scrut arms) → ⊥
plain-not ()

-- Conformance under an index substitution. `none` is the identity,
-- which is the conformance a session is checked at. A dependent send
-- extends the substitution with the value. A dependent receive
-- extends it with the process's name for that binder. The protocol
-- in the index is the protocol as written.
--
-- A match covers a bit with two arms, `b0` then `b1`, or a declared
-- data type with one arm per constructor, in declaration order. Each
-- arm conforms to the same continuation. A bare arm sees only the
-- received name. A named arm also sees that constructor's fields,
-- instantiated at the payload's arguments, last binder innermost.
-- A pair is covered by one product arm `(a, b)`. A record is covered
-- by one product arm naming every field once, in the order the type
-- writes them, last binder innermost. A nat, unit, a vector, a
-- constructor arm on a pair or a record, or the wrong number of arms
-- does not cover. A case is the continuation of the dependent
-- action that binds the scrutinee. The sender is checked on the
-- selected arm by evaluating the run on the value. The receiver is
-- checked on every constructor. A field the run reads chooses the
-- protocol arm when that field is a bit or a declared data type.
fieldAt : List Ctor → ℕ → Decl → List Ty → Maybe (String × List Ty)
fieldAt [] _ _ _ = nothing
fieldAt (ctor n fs ∷ _) nzero d as =
  bindM (instAll d as fs) (λ ts → just (n , ts))
fieldAt (_ ∷ cs) (nsuc i) d as = fieldAt cs i d as

fieldTys : Ty → ℕ → Maybe (String × List Ty)
fieldTys bit nzero = just ("b0" , [])
fieldTys bit (nsuc nzero) = just ("b1" , [])
fieldTys bit (nsuc (nsuc _)) = nothing
fieldTys (dat d as) i = fieldAt (ctorsOf d) i d as
fieldTys _ _ = nothing

-- The last binder is innermost.
extend : List String → List Ty → Ctx → Maybe Ctx
extend [] [] Γ = just Γ
extend (x ∷ xs) (A ∷ ts) Γ = extend xs ts ((x , A) ∷ Γ)
extend _ _ _ = nothing

openArmCtx : Ty → ℕ → String → List String → Ctx → Maybe Ctx
openArmCtx A i c xs Γ with fieldTys A i
... | nothing = nothing
... | just (k , ts) with c ≟ k
... | no′ _ = nothing
... | yes′ _ = extend xs ts Γ

fieldLookup : List Ctor → String → Decl → List Ty → Maybe (List Ty)
fieldLookup [] _ _ _ = nothing
fieldLookup (ctor n fs ∷ cs) c d as with c ≟ n
... | yes′ _ = instAll d as fs
... | no′ _ = fieldLookup cs c d as

fieldsNamed : Ty → String → Maybe (List Ty)
fieldsNamed bit "b0" = just []
fieldsNamed bit "b1" = just []
fieldsNamed bit _ = nothing
fieldsNamed (dat d as) c = fieldLookup (ctorsOf d) c d as
-- A numeral arm of a nat binds nothing. The range is the bound, not a
-- constructor list, so `payCtors` stays nothing for nat.
fieldsNamed nat _ = just []
fieldsNamed _ _ = nothing

armCtxNamed : Ty → String → List String → Ctx → Maybe Ctx
armCtxNamed A c xs Γ = bindM (fieldsNamed A c) (λ ts → extend xs ts Γ)

-- The field a constructor binds at a left-to-right index.
tyAt : Ty → String → ℕ → Maybe Ty
tyAt A c i = bindM (fieldsNamed A c) (λ ts → nth ts i)

-- A slot is what the split sees. `inst` forgets a numeral bound and
-- turns a recursive field into the declaration, so the split keeps
-- its own view. `sBound w` is a nat field whose bound is the numeral
-- `w`. `sSelf` is this declaration. A field the run binds and does
-- not read is not a node.
data Slot : Set where
  sPlain : Ty → Slot
  sBound : ℕ → Slot
  sSelf  : Slot

slotOf : Decl → List Ty → Fld → Maybe Slot
slotOf _ _ fNat = just (sPlain nat)
slotOf _ _ (fBound w) = just (sBound w)
slotOf _ _ fBit = just (sPlain bit)
slotOf _ _ fUnit = just (sPlain unit)
slotOf d as (fPair a b) =
  bindM (inst d as a) (λ A → bindM (inst d as b) (λ B → just (sPlain (pair A B))))
slotOf _ as (fPar i) = bindM (nth as i) (λ A → just (sPlain A))
slotOf _ _ (fSelf _) = just sSelf
slotOf d as (fDat e fs) = bindM (inst d as (fDat e fs)) (λ A → just (sPlain A))

slotsAll : Decl → List Ty → List Fld → Maybe (List Slot)
slotsAll _ _ [] = just []
slotsAll d as (f ∷ fs) =
  bindM (slotOf d as f) (λ s → bindM (slotsAll d as fs) (λ ss → just (s ∷ ss)))

slotLookup : List Ctor → String → Decl → List Ty → Maybe (List Slot)
slotLookup [] _ _ _ = nothing
slotLookup (ctor n fs ∷ cs) c d as with c ≟ n
... | yes′ _ = slotsAll d as fs
... | no′ _ = slotLookup cs c d as

-- The slots of one constructor. A numeral arm of a nat binds nothing.
-- A bit's constructors bind nothing. A declared constructor carries
-- one slot per field.
slotsNamed : Ty → String → Maybe (List Slot)
slotsNamed bit "b0" = just []
slotsNamed bit "b1" = just []
slotsNamed bit _ = nothing
slotsNamed (dat d as) c = slotLookup (ctorsOf d) c d as
slotsNamed nat _ = just []
slotsNamed _ _ = nothing

-- The type a process binds for a slot. A bounded field is a nat.
-- The bound was checked when the value was built.
slotTy : Slot → Maybe Ty
slotTy (sPlain A) = just A
slotTy (sBound _) = just nat
slotTy sSelf = nothing

-- A bit, a declared data type, or a nat whose bound is a numeral.
-- A recursive field, an unbounded nat, a pair, a record, a vector,
-- or unit does not split.
splittableS : Slot → Bool
splittableS (sPlain bit) = true
splittableS (sPlain (dat _ _)) = true
splittableS (sBound _) = true
splittableS (sPlain nat) = false
splittableS (sPlain unit) = false
splittableS (sPlain (pair _ _)) = false
splittableS (sPlain (rec _)) = false
splittableS (sPlain (vec _ _)) = false
splittableS sSelf = false

-- Drop the index just chosen. The product continues on the rest.
dropIdx : ℕ → List ℕ → List ℕ
dropIdx _ [] = []
dropIdx i (j ∷ js) with i ≟ℕ j
... | yes′ _ = dropIdx i js
... | no′ _ = j ∷ dropIdx i js

------------------------------------------------------------------------
-- The split a run induces on one payload constructor. `one` is a
-- single protocol: every value of the fields the run reads selects
-- that protocol, or the run reads none. `node` cases on one field.
-- The index is that field, left to right, and the children are its
-- constructors in declaration order. A node whose children are the
-- same protocol collapses to `one`.
------------------------------------------------------------------------

data Split : Set where
  flat : Proto → Split
  node : ℕ → List (String × Split) → Split

flat≢node : ∀ {S i ch} → flat S ≢ node i ch
flat≢node ()

node≢flat : ∀ {i ch S} → node i ch ≢ flat S
node≢flat ()

flat-inj : ∀ {S T} → flat S ≡ flat T → S ≡ T
flat-inj refl = refl

-- A bit or a declared data type has finitely many constructors. A nat,
-- a pair, a record, a vector, or unit does not split.
splittable : Ty → Bool
splittable bit = true
splittable (dat _ _) = true
splittable nat = false
splittable unit = false
splittable (pair _ _) = false
splittable (rec _) = false
splittable (vec _ _) = false

eqNat : ℕ → ℕ → Bool
eqNat i j with i ≟ℕ j
... | yes′ _ = true
... | no′ _ = false

-- `lo ≤ j` and `j < hi`. An empty range, `lo` equal to `hi`, holds of
-- no index.
inRange : ℕ → ℕ → ℕ → Bool
inRange lo hi j with lo ≤?ℕ j
... | no′ _ = false
... | yes′ _ with hi ≤?ℕ j
... | yes′ _ = false
... | no′ _ = true

mutual
  anyVar : (ℕ → Bool) → RTm → Bool
  anyVar _ (rNat _) = false
  anyVar p (rSuc t) = anyVar p t
  anyVar _ rBit0 = false
  anyVar _ rBit1 = false
  anyVar _ rUnit = false
  anyVar p (rPair a b) = anyVar p a ∨ anyVar p b
  anyVar p (rVar i) = p i
  anyVar p (rCon _ ts) = anyVars p ts
  anyVar p (rMatch t as) = anyVar p t ∨ anyArms p as
  anyVar p (rMatchNat t z s) = anyVar p t ∨ anyVar p z ∨ anyVar p s
  anyVar p (rCall _ ts) = anyVars p ts

  anyVars : (ℕ → Bool) → List RTm → Bool
  anyVars _ [] = false
  anyVars p (t ∷ ts) = anyVar p t ∨ anyVars p ts

  anyArms : (ℕ → Bool) → List Arm → Bool
  anyArms _ [] = false
  anyArms p (arm _ b ∷ as) = anyVar p b ∨ anyArms p as

occursBetween : ℕ → ℕ → RTm → Bool
occursBetween lo hi t = anyVar (inRange lo hi) t

-- Left-to-right indices of the splittable fields the term reads.
-- A read of a field that does not split is `nothing`.
readIdxs : List Slot → RTm → Maybe (List ℕ)
readIdxs tys t = readGo nzero tys
  where
  readGo : ℕ → List Slot → Maybe (List ℕ)
  readGo _ [] = just []
  readGo i (s ∷ ts) with anyVar (eqNat (length ts)) t
  ... | false = readGo (nsuc i) ts
  ... | true with splittableS s
  ... | false = nothing
  ... | true = bindM (readGo (nsuc i) ts) (λ is → just (i ∷ is))

-- A field other than `i` occurs. `i` is a left-to-right index.
others : List Slot → ℕ → RTm → Bool
others tys i t = othersGo nzero tys
  where
  othersGo : ℕ → List Slot → Bool
  othersGo _ [] = false
  othersGo j (_ ∷ ts) with j ≟ℕ i
  ... | yes′ _ = othersGo (nsuc j) ts
  ... | no′ _ with anyVar (eqNat (length ts)) t
  ... | true = true
  ... | false = othersGo (nsuc j) ts

-- The de Bruijn index `k` names the field whose tail has that length.
lookupField : List Slot → ℕ → Maybe (ℕ × Slot)
lookupField tys k = look nzero tys
  where
  look : ℕ → List Slot → Maybe (ℕ × Slot)
  look _ [] = nothing
  look i (s ∷ ts) with length ts ≟ℕ k
  ... | yes′ _ = just (i , s)
  ... | no′ _ = look (nsuc i) ts

mutual
  dummy : Ty → Raw
  dummy nat = rawNat nzero
  dummy bit = rawBit b0
  dummy unit = rawUnit
  dummy (pair A B) = rawPair (dummy A) (dummy B)
  dummy (rec fs) = rawRec (dummyFields fs)
  dummy (vec A _) = rawVec (dummy A)
  dummy (dat _ _) = rawCon "•" []

  dummyFields : Fields → List Raw
  dummyFields noFields = []
  dummyFields (named _ A fs) = dummy A ∷ dummyFields fs

dummys : List Ty → List Raw
dummys [] = []
dummys (A ∷ ts) = dummy A ∷ dummys ts

-- A constructor applied to unread fields. A bit is the literal the
-- evaluator matches. A declared constructor carries a dummy per field.
mkRaw : Ty → String → List Ty → Raw
mkRaw bit "b0" _ = rawBit b0
mkRaw bit "b1" _ = rawBit b1
mkRaw bit _ _ = rawBit b0
mkRaw _ c ts = rawCon c (dummys ts)

setAt : List Raw → ℕ → Raw → List Raw
setAt [] _ _ = []
setAt (_ ∷ rs) nzero r = r ∷ rs
setAt (x ∷ rs) (nsuc i) r = x ∷ setAt rs i r

getF : Raw → ℕ → Maybe Raw
getF (rawCon _ rs) i = nth rs i
getF _ _ = nothing

setField : Raw → ℕ → Raw → Raw
setField (rawCon c rs) i r = rawCon c (setAt rs i r)
setField v _ _ = v

-- `path` is the fields already chosen, outermost first. `i` is the
-- field of the constructor those choices reach.
poke : Raw → List ℕ → ℕ → Raw → Raw
poke host [] i r = setField host i r
poke host (j ∷ js) i r with getF host j
... | nothing = host
... | just inner = setField host j (poke inner js i r)

evalRaw : String → Raw → (R : Ty) → Maybe (Val R)
evalRaw f r R = bindM (apply runs f (r ∷ [])) (cast R)

-- The same evaluator as `evalVal`, on a raw value already in hand.
eval-raw : ∀ {A} (f : String) (v : Val A) (r : Raw) (R : Ty) →
  rawOf v ≡ just r → evalVal f v R ≡ evalRaw f r R
eval-raw f v r R eq rewrite eq = refl

protoAt : String → Raw → Ty → List (String × Proto) → Maybe Proto
protoAt f r R arms =
  bindM (evalRaw f r R) (λ v → bindM (valCtor v) (λ k → findArm k arms))

agreeSplit : Proto → List (String × Split) → Maybe Proto
agreeSplit S [] = just S
agreeSplit S ((_ , flat T) ∷ ch) with protoEq S T
... | true = agreeSplit S ch
... | false = nothing
agreeSplit _ ((_ , node _ _) ∷ _) = nothing

-- Every child the same protocol is that protocol. An empty split, or
-- a child that still cases, stays a node.
collapse : ℕ → List (String × Split) → Split
collapse i [] = node i []
collapse i ((c , node j ch) ∷ rest) = node i ((c , node j ch) ∷ rest)
collapse i ((c , flat S) ∷ rest) with agreeSplit S rest
... | just T = flat T
... | nothing = node i ((c , flat S) ∷ rest)

armBody : List Arm → String → Maybe RTm
armBody [] _ = nothing
armBody (arm d b ∷ as) c with c == d
... | true = just b
... | false = armBody as c

-- The arm of a match on the payload, which is de Bruijn 0.
opened : RTm → String → Maybe RTm
opened (rMatch (rVar k) as) c with k ≟ℕ nzero
... | yes′ _ = armBody as c
... | no′ _ = nothing
opened _ _ = nothing

-- Constructors of a field, in declaration order, each probed by the
-- same evaluator. A bounded nat field is the numerals `0` … `w`.
-- Indices that remain are split under the value just chosen. This
-- does not walk the run term. The count of numerals is the bound.
mutual
  enumCs : String → Ty → List (String × Proto) → List Slot → Raw → ℕ →
           List ℕ → Ty → List String → Maybe (List (String × Split))
  enumOr : String → Ty → List (String × Proto) → List Slot → Raw →
           List ℕ → Maybe Split
  enumAt : String → Ty → List (String × Proto) → List Slot → Raw → ℕ →
           List ℕ → Slot → Maybe Split
  natsGo : String → Ty → List (String × Proto) → List Slot → Raw → ℕ →
           List ℕ → ℕ → ℕ → Maybe (List (String × Split))

  enumCs _ _ _ _ _ _ _ _ [] = just []
  enumCs f R arms tys host i is A (c ∷ cs) =
    bindM (fieldsNamed A c) (λ ts →
      bindM (enumOr f R arms tys (setField host i (mkRaw A c ts)) is) (λ s →
        bindM (enumCs f R arms tys host i is A cs) (λ ch → just ((c , s) ∷ ch))))

  enumOr f R arms _ host [] =
    bindM (protoAt f host R arms) (λ S → just (flat S))
  enumOr f R arms tys host (i ∷ is) =
    bindM (nth tys i) (λ s → enumAt f R arms tys host i is s)

  enumAt f R arms tys host i is (sBound w) =
    bindM (natsGo f R arms tys host i is nzero (nsuc w)) (λ ch → just (collapse i ch))
  enumAt f R arms tys host i is (sPlain A) =
    bindM (payCtors A) (λ cs →
      bindM (enumCs f R arms tys host i is A cs) (λ ch → just (collapse i ch)))
  enumAt _ _ _ _ _ _ _ sSelf = nothing

  natsGo _ _ _ _ _ _ _ _ nzero = just []
  natsGo f R arms tys host i is k (nsuc n) =
    bindM (enumOr f R arms tys (setField host i (rawNat k)) is) (λ s →
      bindM (natsGo f R arms tys host i is (nsuc k) n) (λ ch →
        just ((show k , s) ∷ ch)))

-- An empty-field probe. A constant arm decides. An arm that reads a
-- field does not, and `splitOf` uses the split below instead.
plainProbe : String → Ty → String → Ty → List (String × Proto) → Maybe Split
plainProbe f A c R arms =
  bindM (evalAt f A c R) (λ r →
    bindM (valCtor r) (λ k →
      bindM (findArm k arms) (λ S → just (flat S))))

-- `guard` follows the arm. A match on a splittable field becomes a
-- node whose children are that field's constructors. Any other shape
-- is the finite enumeration of the fields the arm reads, or one
-- evaluation when it reads none. `lo` and `hi` are the shifted
-- indices of fields already chosen; a read there does not decide.
mutual
  guard : String → Ty → List (String × Proto) → List Slot → List ℕ →
          ℕ → ℕ → Raw → RTm → Maybe Split
  guard f R arms tys path lo hi host (rMatch (rVar k) as)
    with occursBetween lo hi (rMatch (rVar k) as)
       | readIdxs tys (rMatch (rVar k) as)
  ... | true | _ = nothing
  ... | false | nothing = nothing
  ... | false | just is =
    onField (lookupField tys k) f R arms tys path host as is
  guard f R arms tys path lo hi host t
    with occursBetween lo hi t | readIdxs tys t
  ... | true | _ = nothing
  ... | false | nothing = nothing
  ... | false | just is = enumOr f R arms tys host is

  onField : Maybe (ℕ × Slot) → String → Ty → List (String × Proto) →
            List Slot → List ℕ → Raw → List Arm → List ℕ → Maybe Split
  onField nothing f R arms tys _ host _ is = enumOr f R arms tys host is
  onField (just (i , sPlain A)) f R arms tys path host as _ with splittable A
  ... | false = nothing
  ... | true with payCtors A
  ... | nothing = nothing
  ... | just cs = bindM (kids f R arms tys path host i A cs as)
                    (λ ch → just (collapse i ch))
  onField (just (_ , sBound _)) _ _ _ _ _ _ _ _ = nothing
  onField (just (_ , sSelf)) _ _ _ _ _ _ _ _ = nothing

  kids : String → Ty → List (String × Proto) → List Slot → List ℕ →
         Raw → ℕ → Ty → List String → List Arm → Maybe (List (String × Split))
  kids _ _ _ _ _ _ _ _ [] [] = just []
  kids f R arms tys path host i A (c ∷ cs) (arm d b ∷ as) with c == d
  ... | false = nothing
  ... | true with fieldsNamed A c
  ... | nothing = nothing
  ... | just ts =
    bindM (descend f R arms tys path host i A c ts b) (λ s →
      bindM (kids f R arms tys path host i A cs as) (λ ch → just ((c , s) ∷ ch)))
  kids _ _ _ _ _ _ _ _ _ _ = nothing

  -- A nullary arm that reads another field of this constructor
  -- continues the product on the parent slots. The field just chosen
  -- stays fixed. A constructor that has its own fields keeps those
  -- slots as the next split.
  descend : String → Ty → List (String × Proto) → List Slot → List ℕ →
            Raw → ℕ → Ty → String → List Ty → RTm → Maybe Split
  descend f R arms slots path host i A c [] b with others slots i b
  ... | true =
      bindM (readIdxs slots b) (λ is →
        enumOr f R arms slots (poke host path i (mkRaw A c [])) (dropIdx i is))
  ... | false =
      guard f R arms [] path nzero nzero (poke host path i (mkRaw A c [])) b
  descend f R arms slots path host i A c ts@(_ ∷ _) b =
    bindM (slotsNamed A c) (λ ss →
      guard f R arms ss (path ++ (i ∷ [])) (length ts) (length ts + length slots)
        (poke host path i (mkRaw A c ts)) b)

splitOf : String → Ty → String → Ty → List (String × Proto) → Maybe Split
splitOf f A c R arms with findRun runs f
... | nothing = nothing
... | just (ts , _ , body , _) with length ts ≟ℕ (nsuc nzero)
... | no′ _ = nothing
... | yes′ _ with fieldsNamed A c
... | nothing = nothing
... | just tys with slotsNamed A c
... | nothing = nothing
... | just slots with opened body c
... | nothing = plainProbe f A c R arms
... | just b = guard f R arms slots [] nzero nzero (mkRaw A c tys) b

-- A uniform split pairs the process with that protocol. A split that
-- still cases on a field is not a flat list of processes.
zipRun : String → Ty → Ty → List (String × Proto) → List String → List Proc → Maybe (List (Proc × Proto))
zipRun _ _ _ _ [] [] = just []
zipRun f A R arms (c ∷ cs) (p ∷ ps) with splitOf f A c R arms
... | just (flat S) = bindM (zipRun f A R arms cs ps) (λ rs → just ((p , S) ∷ rs))
... | just (node _ _) = nothing
... | nothing = nothing
zipRun _ _ _ _ _ _ = nothing

-- Each process arm is paired with the protocol arm its constructor
-- selects. Direct case zips in declaration order. A computed case
-- evaluates the run at each constructor of the payload.
zipCase : (A : Ty) → String → Scrut → List (String × Proto) → List Proc → Maybe (List (Proc × Proto))
zipCase A y (byVal x) arms ps with x ≟ y
... | no′ _ = nothing
... | yes′ _ with labelled A arms
... | false = nothing
... | true = zipVal arms ps
zipCase A y (byRun f x R) arms ps with x ≟ y
... | no′ _ = nothing
... | yes′ _ with labelled R arms
... | false = nothing
... | true with runReady f
... | false = nothing
... | true with payCtors A
... | nothing = nothing
... | just cs = zipRun f A R arms cs ps
zipCase _ _ (bySplit _ _ _) _ _ = nothing

-- The pattern's field names are the type's, in that order. The last
-- binder is innermost, as `extend` places a constructor's fields.
bindRow : Fields → List (String × String) → Ctx → Maybe Ctx
bindRow noFields [] Γ = just Γ
bindRow (named n A fs) ((m , b) ∷ bs) Γ with n ≟ m
... | yes′ _ = bindRow fs bs ((b , A) ∷ Γ)
... | no′ _ = nothing
bindRow _ _ _ = nothing

prodCtx : Ty → Pat → Ctx → Maybe Ctx
prodCtx (pair A B) (pPair x y) Γ = just ((y , B) ∷ (x , A) ∷ Γ)
prodCtx (rec fs) (pRec bs) Γ = bindRow fs bs Γ
prodCtx _ _ _ = nothing

data Fits : Fields → List (String × String) → Set where
  fits-nil  : Fits noFields []
  fits-cons : ∀ {n A fs b bs} → Fits fs bs → Fits (named n A fs) ((n , b) ∷ bs)

fits? : (fs : Fields) (bs : List (String × String)) → Dec (Fits fs bs)
fits? noFields [] = yes′ fits-nil
fits? noFields (_ ∷ _) = no′ (λ ())
fits? (named _ _ _) [] = no′ (λ ())
fits? (named n _ fs) ((m , _) ∷ bs) with n ≟ m
... | no′ ¬eq = no′ (λ { (fits-cons _) → ¬eq refl })
... | yes′ refl with fits? fs bs
... | yes′ f = yes′ (fits-cons f)
... | no′ ¬f = no′ (λ { (fits-cons f) → ¬f f })

-- The opened constructor binds a splittable field at this index.
-- A numeral and a nullary constructor do not.
data NestOk (B : Ty) (c : String) (xs : List String) (i : ℕ) (y : String) (Γ : Ctx) : Set where
  nest-ok : ∀ {Δ C} →
    armCtxNamed B c xs Γ ≡ just Δ →
    nth xs i ≡ just y →
    tyAt B c i ≡ just C →
    splittable C ≡ true →
    NestOk B c xs i y Γ

orEmpty : Maybe (List Slot) → List Slot
orEmpty (just ss) = ss
orEmpty nothing = []

mutual
  data Covered : Ty → List PArm → Set where
    bit-cov  : ∀ {p q} → Covered bit (p ∷ q ∷ [])
    dat-cov  : ∀ {d as ps} → length ps ≡ length (ctorsOf d) → Covered (dat d as) ps
    pair-cov : ∀ {A B x y p} → Covered (pair A B) (prod (pPair x y) p ∷ [])
    rec-cov  : ∀ {fs bs p} → Fits fs bs → Covered (rec fs) (prod (pRec bs) p ∷ [])

  data Arms (Γ : Ctx) (ρ : Idx) (A : Ty) : ℕ → List PArm → Proto → Set where
    arms-nil   : ∀ {i S} → Arms Γ ρ A i [] S
    arms-cons  : ∀ {i p ps S} →
      Conformsρ Γ ρ p S →
      Arms Γ ρ A (nsuc i) ps S →
      Arms Γ ρ A i (bare p ∷ ps) S
    arms-named : ∀ {i c xs p Δ ps S} →
      openArmCtx A i c xs Γ ≡ just Δ →
      Conformsρ Δ ρ p S →
      Arms Γ ρ A (nsuc i) ps S →
      Arms Γ ρ A i (named c xs p ∷ ps) S
    arms-prod  : ∀ {i pat p Δ ps S} →
      prodCtx A pat Γ ≡ just Δ →
      Conformsρ Δ ρ p S →
      Arms Γ ρ A (nsuc i) ps S →
      Arms Γ ρ A i (prod pat p ∷ ps) S

  -- One process per protocol arm, in order. The process is a subterm
  -- of the match, so the check recurses on it. A named arm binds the
  -- fields of that constructor. The protocol arm is the one written
  -- for that constructor.
  data ArmsAt (Γ : Ctx) (ρ : Idx) (A : Ty) : List (String × Proto) → List PArm → Set where
    at-nil   : ArmsAt Γ ρ A [] []
    at-cons  : ∀ {c S as p ps} →
      Conformsρ Γ ρ p S →
      ArmsAt Γ ρ A as ps →
      ArmsAt Γ ρ A ((c , S) ∷ as) (bare p ∷ ps)
    at-named : ∀ {c S as xs p Δ ps} →
      armCtxNamed A c xs Γ ≡ just Δ →
      Conformsρ Δ ρ p S →
      ArmsAt Γ ρ A as ps →
      ArmsAt Γ ρ A ((c , S) ∷ as) (named c xs p ∷ ps)

  -- The arms of a field the run reads. A uniform protocol is one
  -- process. A nested split is a `fork` on that field. `par` and
  -- `pxs` are the slots and binders of the constructor that owns the
  -- field. A sibling field is an index of that list. A field of the
  -- constructor just opened replaces them.
  data ForkArms (Γ : Ctx) (ρ : Idx) (B : Ty) (par : List Slot) (pxs : List String) :
      List (String × Split) → List PArm → Set where
    fork-nil   : ForkArms Γ ρ B par pxs [] []
    fork-bare  : ∀ {c S ch p ps} →
      Conformsρ Γ ρ p S →
      ForkArms Γ ρ B par pxs ch ps →
      ForkArms Γ ρ B par pxs ((c , flat S) ∷ ch) (bare p ∷ ps)
    fork-named : ∀ {c S ch xs p Δ ps} →
      armCtxNamed B c xs Γ ≡ just Δ →
      Conformsρ Δ ρ p S →
      ForkArms Γ ρ B par pxs ch ps →
      ForkArms Γ ρ B par pxs ((c , flat S) ∷ ch) (named c xs p ∷ ps)
    fork-nest  : ∀ {c xs y i ch2 qs Δ C ch ps} →
      armCtxNamed B c xs Γ ≡ just Δ →
      nth xs i ≡ just y →
      tyAt B c i ≡ just C →
      splittable C ≡ true →
      ForkArms Δ ρ C (orEmpty (slotsNamed B c)) xs ch2 qs →
      ForkArms Γ ρ B par pxs ch ps →
      ForkArms Γ ρ B par pxs ((c , node i ch2) ∷ ch) (fork c xs y qs ∷ ps)
    -- The label binds nothing, and the index is a sibling field.
    fork-sib   : ∀ {c xs y i s C ch2 qs ch ps} →
      ¬ NestOk B c xs i y Γ →
      nth pxs i ≡ just y →
      nth par i ≡ just s →
      splittableS s ≡ true →
      slotTy s ≡ just C →
      ForkArms Γ ρ C par pxs ch2 qs →
      ForkArms Γ ρ B par pxs ch ps →
      ForkArms Γ ρ B par pxs ((c , node i ch2) ∷ ch) (fork c xs y qs ∷ ps)

  -- A computed case. Each constructor is probed on the fields the run
  -- reads. `one` is a single continuation. `node` is a case on the
  -- bound field. A named process arm still binds the payload's fields.
  data ArmsRun (Γ : Ctx) (ρ : Idx) (f : String) (A R : Ty)
      (arms : List (String × Proto)) : List String → List PArm → Set where
    run-nil   : ArmsRun Γ ρ f A R arms [] []
    run-cons  : ∀ {c cs p ps S} →
      splitOf f A c R arms ≡ just (flat S) →
      Conformsρ Γ ρ p S →
      ArmsRun Γ ρ f A R arms cs ps →
      ArmsRun Γ ρ f A R arms (c ∷ cs) (bare p ∷ ps)
    run-named : ∀ {c cs xs p Δ ps S} →
      splitOf f A c R arms ≡ just (flat S) →
      armCtxNamed A c xs Γ ≡ just Δ →
      Conformsρ Δ ρ p S →
      ArmsRun Γ ρ f A R arms cs ps →
      ArmsRun Γ ρ f A R arms (c ∷ cs) (named c xs p ∷ ps)
    run-fork  : ∀ {c cs xs y qs Δ i ch B par ps} →
      splitOf f A c R arms ≡ just (node i ch) →
      armCtxNamed A c xs Γ ≡ just Δ →
      nth xs i ≡ just y →
      tyAt A c i ≡ just B →
      slotsNamed A c ≡ just par →
      ForkArms Δ ρ B par xs ch qs →
      ArmsRun Γ ρ f A R arms cs ps →
      ArmsRun Γ ρ f A R arms (c ∷ cs) (fork c xs y qs ∷ ps)

  -- One process per numeral of a bounded nat. A bare arm is that
  -- process. A named arm binds nothing and its name is the row's label.
  data CovNat (Γ : Ctx) (ρ : Idx) : List (String × Proto) → List PArm → Set where
    cn-nil   : CovNat Γ ρ [] []
    cn-bare  : ∀ {c S rows p ps} →
      Conformsρ Γ ρ p S →
      CovNat Γ ρ rows ps →
      CovNat Γ ρ ((c , S) ∷ rows) (bare p ∷ ps)
    cn-named : ∀ {c S rows p ps} →
      Conformsρ Γ ρ p S →
      CovNat Γ ρ rows ps →
      CovNat Γ ρ ((c , S) ∷ rows) (named c [] p ∷ ps)

  -- A column is one process when every numeral selects the same
  -- protocol, or a match on the bounded nat otherwise.
  data Cell (Γ : Ctx) (ρ : Idx) (x : String) : List (String × Proto) → Proc → Set where
    cell-one : ∀ {rows p S} →
      sameArms rows ≡ just S →
      Conformsρ Γ ρ p S →
      Cell Γ ρ x rows p
    cell-nat : ∀ {rows qs} →
      CovNat Γ ρ rows qs →
      Cell Γ ρ x rows (mget nat x qs)

  -- The payload's constructors, outer, and the numerals of the earlier
  -- nat, inner. Named arms bind the constructor's fields.
  data ProdCov (Γ : Ctx) (ρ : Idx) (A : Ty) (x : String) (w : ℕ) :
      List String → List (List (String × Proto)) → List PArm → Set where
    pc-nil : ProdCov Γ ρ A x w [] [] []
    pc-bare : ∀ {c cs rows grid p ps} →
      Cell Γ ρ x rows p →
      ProdCov Γ ρ A x w cs grid ps →
      ProdCov Γ ρ A x w (c ∷ cs) (rows ∷ grid) (bare p ∷ ps)
    pc-named : ∀ {c cs rows grid xs p Δ ps} →
      armCtxNamed A c xs Γ ≡ just Δ →
      Cell Δ ρ x rows p →
      ProdCov Γ ρ A x w cs grid ps →
      ProdCov Γ ρ A x w (c ∷ cs) (rows ∷ grid) (named c xs p ∷ ps)

  -- The continuation of an evidence send. A plain continuation is the
  -- protocol written after the nat. A case continues as the arm the
  -- value selects. A following send of a splittable payload continues
  -- as the arm the pair of values selects.
  data SendCont (Γ : Ctx) (ρ : Idx) (v : ValExpr nat) : Proc → NExp → Proto → Set where
    send-plain : ∀ {P e S} →
      Plain S →
      Conformsρ Γ ρ P S →
      SendCont Γ ρ v P e S
    send-val : ∀ {P y w arms T} →
      pickShown v w arms ≡ just T →
      Conformsρ Γ ρ P T →
      SendCont Γ ρ v P (nlit w) (pcase (byVal y) arms)
    send-run : ∀ {P y w f R arms T} →
      readyN (nsuc nzero) f ≡ true →
      labelled R arms ≡ true →
      pickRun v w f R arms ≡ just T →
      Conformsρ Γ ρ P T →
      SendCont Γ ρ v P (nlit w) (pcase (byRun f y R) arms)
    send-prod : ∀ {w y z A B u Q f R arms cs T} →
      A ≡ applyTy ρ B →
      payCtors A ≡ just cs →
      readyN (nsuc (nsuc nzero)) f ≡ true →
      labelled R arms ≡ true →
      pickProd v u w f R arms ≡ just T →
      Conformsρ Γ ρ Q T →
      SendCont Γ ρ v (put A u Q) (nlit w)
        (dsend z B (pcase (bySplit f (tagNat y w ∷ tagDat z cs ∷ []) R) arms))
    send-pbit : ∀ {w y z B u Q f R arms T} →
      bit ≡ applyTy ρ B →
      readyN (nsuc (nsuc nzero)) f ≡ true →
      labelled R arms ≡ true →
      pickProd v u w f R arms ≡ just T →
      Conformsρ Γ ρ Q T →
      SendCont Γ ρ v (put bit u Q) (nlit w)
        (dsend z B (pcase (bySplit f (tagNat y w ∷ tagBit z ∷ []) R) arms))

  -- One process arm per label of the factor the match stands on.
  -- The rows kept for a label are those whose last component is that
  -- label. A bare arm binds nothing. A named arm binds the fields.
  data WArms (Γ : Ctx) (ρ : Idx) (A : Ty) :
      List String → List Tag → List (List String × Proto) → List PArm → Set where
    wa-nil : ∀ {ts rows} → WArms Γ ρ A [] ts rows []
    wa-bare : ∀ {lab labs ts rows p ps} →
      WCover Γ ρ ts (keepLab lab rows) p →
      WArms Γ ρ A labs ts rows ps →
      WArms Γ ρ A (lab ∷ labs) ts rows (bare p ∷ ps)
    wa-named : ∀ {lab labs ts rows c xs p Δ ps} →
      c ≡ lab →
      armCtxNamed A c xs Γ ≡ just Δ →
      WCover Δ ρ ts (keepLab lab rows) p →
      WArms Γ ρ A labs ts rows ps →
      WArms Γ ρ A (lab ∷ labs) ts rows (named c xs p ∷ ps)

  -- The last factor is the head of the tag list. A bare continuation
  -- is the common protocol of the rows that remain. A match covers
  -- one arm per label of that factor.
  data WCover (Γ : Ctx) (ρ : Idx) : List Tag → List (List String × Proto) → Proc → Set where
    wc-same : ∀ {ts rows p S} →
      sameRows rows ≡ just S →
      Conformsρ Γ ρ p S →
      WCover Γ ρ ts rows p
    wc-nat : ∀ {a w ts rows x ps} →
      a ≡ x →
      WArms Γ ρ nat (natArms w) ts rows ps →
      WCover Γ ρ (tagNat a w ∷ ts) rows (mget nat x ps)
    wc-pay : ∀ {t ts rows A x ps cs} →
      tagName t ≡ x →
      payCtors A ≡ just cs →
      tagLabs t ≡ cs →
      WArms Γ ρ A cs ts rows ps →
      WCover Γ ρ (t ∷ ts) rows (mget A x ps)

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
      Plain S →
      Conformsρ Γ (bind y (ixOf A v) (shadow y ρ)) P S →
      Conformsρ Γ ρ (put A v P) (dsend y B S)

    -- The value selects one arm of the case. The continuation is that arm.
    dput-arm : ∀ {A B y v P scrut arms T} →
      A ≡ applyTy ρ B →
      ValExprOk Γ v →
      selectProto y v scrut arms ≡ just T →
      Conformsρ Γ (bind y (ixOf A v) (shadow y ρ)) P T →
      Conformsρ Γ ρ (put A v P) (dsend y B (pcase scrut arms))

    dget-ok : ∀ {A B x y P S} →
      A ≡ applyTy ρ B →
      Conformsρ ((x , A) ∷ Γ) (renameIdx y x (shadow y ρ)) P S →
      Conformsρ Γ ρ (get A x P) (drecv y B S)

    -- The evidence is a premise. The process puts the nat alone.
    eput-ok : ∀ {y e v P S} →
      ValExprOk Γ v →
      Owed Γ v (resolve ρ e) →
      SendCont Γ ρ v P e S →
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

    -- The name is the one `mget` just bound. Each arm is that continuation.
    -- A named arm's context also holds the constructor's fields.
    -- A product arm's context holds the components, last binder innermost.
    mget-ok : ∀ {A B x ps S} →
      A ≡ applyTy ρ B →
      Covered A ps →
      Arms ((x , A) ∷ Γ) ρ A nzero ps S →
      Conformsρ Γ ρ (mget A x ps) (recv B S)

    -- Each process arm conforms to the protocol arm of that constructor.
    mget-val : ∀ {A B x y ps arms} →
      A ≡ applyTy ρ B →
      Covered A ps →
      labelled A arms ≡ true →
      ArmsAt ((x , A) ∷ Γ) (renameIdx y x (shadow y ρ)) A arms ps →
      Conformsρ Γ ρ (mget A x ps) (drecv y B (pcase (byVal y) arms))

    mget-run : ∀ {A B x y f R ps arms cs} →
      A ≡ applyTy ρ B →
      Covered A ps →
      runReady f ≡ true →
      labelled R arms ≡ true →
      payCtors A ≡ just cs →
      ArmsRun ((x , A) ∷ Γ) (renameIdx y x (shadow y ρ)) f A R arms cs ps →
      Conformsρ Γ ρ (mget A x ps) (drecv y B (pcase (byRun f y R) arms))

    -- A numeral bound splits into `0` … `w`. The arms are those
    -- numerals, in order. Each process arm conforms to that protocol.
    eget-val : ∀ {x y w ps arms} →
      namesEq (natArms w) (armNames arms) ≡ true →
      ArmsAt ((x , nat) ∷ Γ) ρ nat arms ps →
      Conformsρ Γ ρ (mget nat x ps) (erecv y (nlit w) (pcase (byVal y) arms))

    -- The run is evaluated at every numeral. The process arm for that
    -- numeral conforms to the protocol the run returns.
    eget-run : ∀ {x y w f R ps arms rows} →
      readyN (nsuc nzero) f ≡ true →
      labelled R arms ≡ true →
      natRows f R arms w ≡ just rows →
      CovNat ((x , nat) ∷ Γ) ρ rows ps →
      Conformsρ Γ ρ (mget nat x ps) (erecv y (nlit w) (pcase (byRun f y R) arms))

    -- The payload just received is a bit or a declared data type, and
    -- an earlier nat is bounded by a numeral. The process covers the
    -- product: one arm per constructor, and under it one arm per numeral
    -- unless every numeral selects the same protocol.
    mget-prod : ∀ {A B x y d w f R ps arms cs grid} →
      A ≡ applyTy ρ B →
      payCtors A ≡ just cs →
      readyN (nsuc (nsuc nzero)) f ≡ true →
      labelled R arms ≡ true →
      prodGrid w A f R arms ≡ just grid →
      ProdCov ((x , A) ∷ Γ) ρ A d w cs grid ps →
      Conformsρ Γ ρ (mget A x ps)
        (drecv y B (pcase (bySplit f (tagNat d w ∷ tagDat y cs ∷ []) R) arms))

    mget-pbit : ∀ {x y d w f R ps arms grid} →
      readyN (nsuc (nsuc nzero)) f ≡ true →
      labelled R arms ≡ true →
      prodGrid w bit f R arms ≡ just grid →
      ProdCov ((x , bit) ∷ Γ) ρ bit d w ("b0" ∷ "b1" ∷ []) grid ps →
      Conformsρ Γ ρ (mget bit x ps)
        (drecv y bit (pcase (bySplit f (tagNat d w ∷ tagBit y ∷ []) R) arms))

    -- Any other finite product. The match stands on the last factor.
    -- Earlier factors are matched inside its arms. The length is the
    -- product of the widths named by the tags.
    mget-wide : ∀ {A B x y f tags R ps arms rows t cs} →
      (wt : WTag tags) →
      A ≡ applyTy ρ B →
      lastTag tags ≡ just t →
      tagName t ≡ y →
      payCtors A ≡ just cs →
      tagLabs t ≡ cs →
      readyN (length tags) f ≡ true →
      labelled R arms ≡ true →
      wideRows f R arms (tagsFac tags) ≡ just rows →
      length rows ≡ prodNs (map facWidth (tagsFac tags)) →
      WArms ((x , A) ∷ Γ) ρ A cs (rev (dropLast tags)) rows ps →
      Conformsρ Γ ρ (mget A x ps)
        (drecv y B (pcase (bySplit f tags R) arms))

    eget-wide : ∀ {x y w f tags R ps arms rows} →
      (wt : WTag tags) →
      lastTag tags ≡ just (tagNat y w) →
      readyN (length tags) f ≡ true →
      labelled R arms ≡ true →
      wideRows f R arms (tagsFac tags) ≡ just rows →
      length rows ≡ prodNs (map facWidth (tagsFac tags)) →
      WArms ((x , nat) ∷ Γ) ρ nat (natArms w) (rev (dropLast tags)) rows ps →
      Conformsρ Γ ρ (mget nat x ps)
        (erecv y (nlit w) (pcase (bySplit f tags R) arms))

    -- The whole put spine is decided at the first action. Each nat
    -- owes its numeral. The tail conforms to the arm the values select.
    eput-wide : ∀ {y w tags v P S Q gs f R arms T rows} →
      (wt : WTag (tagNat y w ∷ tags)) →
      PutSpine Γ (tagNat y w ∷ tags) (esend y (nlit w) S) (put nat v P) Q gs →
      splitAt (esend y (nlit w) S) ≡ just (f , (tagNat y w ∷ tags) , R , arms) →
      readyN (length (tagNat y w ∷ tags)) f ≡ true →
      labelled R arms ≡ true →
      wideRows f R arms (tagsFac (tagNat y w ∷ tags)) ≡ just rows →
      length rows ≡ prodNs (map facWidth (tagsFac (tagNat y w ∷ tags))) →
      pickRead gs f R arms ≡ just T →
      Conformsρ Γ ρ Q T →
      Conformsρ Γ ρ (put nat v P) (esend y (nlit w) S)

    dput-wide : ∀ {A B y v P S tags Q gs f R arms T rows} →
      A ≡ applyTy ρ B →
      (wt : WTag tags) →
      PutSpine Γ tags (dsend y B S) (put A v P) Q gs →
      splitAt (dsend y B S) ≡ just (f , tags , R , arms) →
      readyN (length tags) f ≡ true →
      labelled R arms ≡ true →
      wideRows f R arms (tagsFac tags) ≡ just rows →
      length rows ≡ prodNs (map facWidth (tagsFac tags)) →
      pickRead gs f R arms ≡ just T →
      Conformsρ Γ ρ Q T →
      Conformsρ Γ ρ (put A v P) (dsend y B S)

Conforms : Ctx → Proc → Proto → Set
Conforms Γ P S = Conformsρ Γ none P S

-- The value a call computes, or the literal. A variable is not a
-- concrete value, so it selects no arm.
ground : ∀ {A} → ValExpr A → Maybe (Val A)
ground (lit v) = just v
ground (var _) = nothing
ground {A} (call f as) = evalExpr (call {A} f as)

-- A field environment. The head is the innermost binding. `[]` is the
-- identity on a process, so a bare arm is the process it stores.
FEnv : Set
FEnv = List (String × Raw)

lookupF : FEnv → String → Maybe Raw
lookupF [] _ = nothing
lookupF ((y , r) ∷ e) x with x ≟ y
... | yes′ _ = just r
... | no′ _ = lookupF e x

shadowF : String → FEnv → FEnv
shadowF _ [] = []
shadowF x ((y , r) ∷ e) with x ≟ y
... | yes′ _ = shadowF x e
... | no′ _ = (y , r) ∷ shadowF x e

shadows : List String → FEnv → FEnv
shadows [] e = e
shadows (x ∷ xs) e = shadows xs (shadowF x e)

-- The last field is innermost. A different length is not an environment.
lenEnv : List String → List Raw → Maybe FEnv
lenEnv [] [] = just []
lenEnv [] (_ ∷ _) = nothing
lenEnv (_ ∷ _) [] = nothing
lenEnv (x ∷ xs) (r ∷ rs) =
  bindM (lenEnv xs rs) (λ e → just (e ++ ((x , r) ∷ [])))

mutual
  substVal : ∀ {A} → FEnv → ValExpr A → ValExpr A
  substVal [] v = v
  substVal (_ ∷ _) (lit v) = lit v
  substVal e@(_ ∷ _) (var {A} x) with lookupF e x
  ... | nothing = var x
  ... | just raw with cast A raw
  ... | just u = lit u
  ... | nothing = var x
  substVal e@(_ ∷ _) (call f as) = call f (substArgs e as)

  substArgs : FEnv → List VArg → List VArg
  substArgs _ [] = []
  substArgs e (varg B b ∷ as) = varg B (substVal e b) ∷ substArgs e as

  substProc : FEnv → Proc → Proc
  substProc [] p = p
  substProc (_ ∷ _) done = done
  substProc (_ ∷ _) stop = stop
  substProc e@(_ ∷ _) (put A v P) = put A (substVal e v) (substProc e P)
  substProc e@(_ ∷ _) (get A x P) = get A x (substProc (shadowF x e) P)
  substProc e@(_ ∷ _) (pick0 P) = pick0 (substProc e P)
  substProc e@(_ ∷ _) (pick1 P) = pick1 (substProc e P)
  substProc e@(_ ∷ _) (cover P Q) = cover (substProc e P) (substProc e Q)
  substProc e@(_ ∷ _) (iget x P Q) =
    iget x (substProc (shadowF x e) P) (substProc (shadowF x e) Q)
  substProc e@(_ ∷ _) (mget A x ps) = mget A x (substArms (shadowF x e) ps)

  substArms : FEnv → List PArm → List PArm
  substArms _ [] = []
  substArms e (bare p ∷ ps) = bare (substProc e p) ∷ substArms e ps
  substArms e (named c xs p ∷ ps) =
    named c xs (substProc (shadows xs e) p) ∷ substArms e ps
  substArms e (prod pat p ∷ ps) =
    prod pat (substProc (shadows (patBinders pat) e) p) ∷ substArms e ps
  substArms e (fork c xs y qs ∷ ps) =
    fork c xs y (substArms (shadows xs e) qs) ∷ substArms e ps

-- The constructor name matches and the binders match the spine.
-- Otherwise the arm is not the one the value takes. The clauses are
-- the ones a meeting follows, so a concrete value reduces by `refl`.
openNamed : String → String → List String → Proc → Spine → Maybe Proc
openNamed k c xs p sp with k == c | rawSpine sp
... | false | _ = nothing
... | true | nothing = nothing
... | true | just rs with lenEnv xs rs
... | nothing = nothing
... | just e = just (substProc e p)

-- The two components, last binder innermost. A component that has no
-- raw image does not open the arm.
openPair : ∀ {A B} → String → String → Val A → Val B → Maybe FEnv
openPair x y a b with rawOf a | rawOf b
... | just ra | just rb = lenEnv (x ∷ y ∷ []) (ra ∷ rb ∷ [])
... | just _ | nothing = nothing
... | nothing | _ = nothing

-- The record's fields, in type order, last binder innermost. A field
-- name the pattern does not write at that position does not open.
openRec : ∀ {fs} → List (String × String) → Row fs → Maybe FEnv
openRec [] noRow = just []
openRec ((n , b) ∷ bs) (cell {n = m} v row) with n ≟ m
... | no′ _ = nothing
... | yes′ _ =
  bindM (rawOf v) (λ r → bindM (openRec bs row) (λ e → just (e ++ ((b , r) ∷ []))))
openRec [] (cell _ _) = nothing
openRec (_ ∷ _) noRow = nothing

-- The process after a product arm's binders are replaced. `nothing`
-- is an arm the value does not open.
fillArm : Proc → Maybe FEnv → Maybe Proc
fillArm _ nothing = nothing
fillArm p (just e) = just (substProc e p)

-- A nat selects the arm at its index. Zero takes the head. A successor
-- takes the tail, one step per successor. A bare arm is that process.
-- A named arm is that process when its name is the decimal of the
-- index and it binds nothing. A product arm, a fork, or a name that
-- is not that decimal selects nothing. The bound is not an argument:
-- an index past the arms selects nothing, and the protocol checker
-- requires the arms to be exactly `0` … `w`.
hitName? : Bool → Proc → Maybe Proc
hitName? true p = just p
hitName? false _ = nothing

natGo : Val nat → List PArm → ℕ → Maybe Proc
natGo zero [] _ = nothing
natGo zero (bare p ∷ _) _ = just p
natGo zero (named c [] p ∷ _) i = hitName? (c == show i) p
natGo zero (named _ (_ ∷ _) _ ∷ _) _ = nothing
natGo zero (prod _ _ ∷ _) _ = nothing
natGo zero (fork _ _ _ _ ∷ _) _ = nothing
natGo (suc _) [] _ = nothing
natGo (suc v) (_ ∷ ps) i = natGo v ps (nsuc i)

-- The same walk on a numeral, so a covering proof can induct on it.
armGo : ℕ → List PArm → ℕ → Maybe Proc
armGo nzero [] _ = nothing
armGo nzero (bare p ∷ _) _ = just p
armGo nzero (named c [] p ∷ _) i = hitName? (c == show i) p
armGo nzero (named _ (_ ∷ _) _ ∷ _) _ = nothing
armGo nzero (prod _ _ ∷ _) _ = nothing
armGo nzero (fork _ _ _ _ ∷ _) _ = nothing
armGo (nsuc _) [] _ = nothing
armGo (nsuc k) (_ ∷ ps) i = armGo k ps (nsuc i)

-- `pickCtor` receives the Boolean comparison. `nthProc` makes it.
-- A meeting follows that same comparison, so the equality is the one
-- `pickCtor` computes. The false branch is the tail of the constructor list.
-- A bare arm is the stored process. A named arm is that process with
-- the value's fields substituted for its binders. A `fork` opens the
-- same way, then cases on the named field and substitutes the outer
-- fields into the arm that field selects.
mutual
  pickCtor : Bool → PArm → Spine → List Ctor → String → List PArm → Maybe Proc
  pickCtor true (bare p) _ _ _ _ = just p
  pickCtor true (named k xs p) sp _ c _ = openNamed k c xs p sp
  pickCtor true (prod _ _) _ _ _ _ = nothing
  pickCtor true (fork k xs y qs) sp _ c _ = openFork k c xs y qs sp
  pickCtor false _ sp cs name ps = nthProc cs name sp ps

  nthProc : List Ctor → String → Spine → List PArm → Maybe Proc
  nthProc [] _ _ _ = nothing
  nthProc (_ ∷ _) _ _ [] = nothing
  nthProc (ctor n _ ∷ cs) c sp (a ∷ ps) = pickCtor (c == n) a sp cs c ps

  openFork : String → String → List String → String → List PArm → Spine → Maybe Proc
  openFork k c xs y qs sp = openAt (k == c) (rawSpine sp) xs y qs sp

  -- The name comparison and the raw spine are arguments, so a proof
  -- can match them without a `with`.
  openAt : Bool → Maybe (List Raw) → List String → String → List PArm → Spine → Maybe Proc
  openAt false _ _ _ _ _ = nothing
  openAt true nothing _ _ _ _ = nothing
  openAt true (just rs) xs y qs sp = openEnv (lenEnv xs rs) xs y qs sp

  openEnv : Maybe FEnv → List String → String → List PArm → Spine → Maybe Proc
  openEnv nothing _ _ _ _ = nothing
  openEnv (just e) xs y qs sp = seek xs y e qs sp

  seek : List String → String → FEnv → List PArm → Spine → Maybe Proc
  seek [] _ _ _ _ = nothing
  seek (_ ∷ _) _ _ _ snil = nothing
  seek (x ∷ xs) y e qs (scons A v sp) = seekAt A x xs y e qs v sp (x ≟ y)

  seekAt : (A : Ty) (x : String) (xs : List String) (y : String) (e : FEnv)
           (qs : List PArm) (v : Val A) (sp : Spine) →
           Dec (x ≡ y) → Maybe Proc
  seekAt _ _ xs y e qs _ sp (no′ _) = seek xs y e qs sp
  seekAt A _ _ _ e qs v _ (yes′ _) = bindM (armOf A v qs) (λ p → just (substProc e p))

  armOf : (A : Ty) → Val A → List PArm → Maybe Proc
  armOf bit b0 [] = nothing
  armOf bit b0 (_ ∷ []) = nothing
  armOf bit b0 (_ ∷ _ ∷ _ ∷ _) = nothing
  armOf bit b0 (bare p ∷ _ ∷ []) = just p
  armOf bit b0 (named _ [] p ∷ _ ∷ []) = just p
  armOf bit b0 (named _ (_ ∷ _) _ ∷ _ ∷ []) = nothing
  armOf bit b0 (prod _ _ ∷ _ ∷ []) = nothing
  armOf bit b0 (fork _ _ _ _ ∷ _ ∷ []) = nothing
  armOf bit b1 [] = nothing
  armOf bit b1 (_ ∷ []) = nothing
  armOf bit b1 (_ ∷ _ ∷ _ ∷ _) = nothing
  armOf bit b1 (_ ∷ bare q ∷ []) = just q
  armOf bit b1 (_ ∷ named _ [] q ∷ []) = just q
  armOf bit b1 (_ ∷ named _ (_ ∷ _) _ ∷ []) = nothing
  armOf bit b1 (_ ∷ prod _ _ ∷ []) = nothing
  armOf bit b1 (_ ∷ fork _ _ _ _ ∷ []) = nothing
  armOf nat v ps = natGo v ps nzero
  armOf unit _ _ = nothing
  armOf (vec _ _) _ _ = nothing
  armOf (pair _ _) (tup _ _) (_ ∷ _ ∷ _) = nothing
  armOf (pair _ _) (tup _ _) [] = nothing
  armOf (pair _ _) (tup a b) (prod (pPair x y) p ∷ []) = fillArm p (openPair x y a b)
  armOf (pair _ _) (tup _ _) (prod (pRec _) _ ∷ []) = nothing
  armOf (pair _ _) (tup _ _) (bare _ ∷ []) = nothing
  armOf (pair _ _) (tup _ _) (named _ _ _ ∷ []) = nothing
  armOf (pair _ _) (tup _ _) (fork _ _ _ _ ∷ []) = nothing
  armOf (rec _) (rec _) (_ ∷ _ ∷ _) = nothing
  armOf (rec _) (rec _) [] = nothing
  armOf (rec _) (rec row) (prod (pRec bs) p ∷ []) = fillArm p (openRec bs row)
  armOf (rec _) (rec _) (prod (pPair _ _) _ ∷ []) = nothing
  armOf (rec _) (rec _) (bare _ ∷ []) = nothing
  armOf (rec _) (rec _) (named _ _ _ ∷ []) = nothing
  armOf (rec _) (rec _) (fork _ _ _ _ ∷ []) = nothing
  armOf (dat d _) (con c sp) ps = nthProc (ctorsOf d) c sp ps

-- One function for the value `ground` returns, so a meeting can
-- follow that step by congruence. `nothing` selects no arm.
armStep : ∀ {A} → List PArm → Maybe (Val A) → Maybe Proc
armStep _ nothing = nothing
armStep ps (just u) = armOf _ u ps

armExpr : ∀ {A} → ValExpr A → List PArm → Maybe Proc
armExpr v ps = armStep ps (ground v)

------------------------------------------------------------------------
-- A protocol is well formed when every length is a numeral or a nat
-- in scope. The binder of a dependent action extends that scope.
------------------------------------------------------------------------

data TyOk : Ctx → Ty → Set
data FieldsOk : Ctx → Fields → Set
data AllTy : Ctx → List Ty → Set
data FldsFit : Ctx → Decl → List Ty → List Fld → Set
data CtorsFit : Ctx → Decl → List Ty → List Ctor → Set
data FieldFit : Ctx → Decl → List Ty → Fld → Set

data NExpOk : Ctx → NExp → Set where
  nlit-ok : ∀ {Γ n} → NExpOk Γ (nlit n)
  nvar-ok : ∀ {Γ x} → x ∈ Γ ∷ nat → NExpOk Γ (nvar x)

data FieldsOk where
  noFields-ok : ∀ {Γ} → FieldsOk Γ noFields
  named-ok    : ∀ {Γ n A fs} → TyOk Γ A → FieldsOk Γ fs → FieldsOk Γ (named n A fs)

data AllTy where
  tys-nil  : ∀ {Γ} → AllTy Γ []
  tys-cons : ∀ {Γ A as} → TyOk Γ A → AllTy Γ as → AllTy Γ (A ∷ as)

data FldsFit where
  flds-nil  : ∀ {Γ d as} → FldsFit Γ d as []
  flds-cons : ∀ {Γ d as f fs} →
    FieldFit Γ d as f → FldsFit Γ d as fs → FldsFit Γ d as (f ∷ fs)

data CtorsFit where
  ctors-nil  : ∀ {Γ d as} → CtorsFit Γ d as []
  ctors-cons : ∀ {Γ d as n fs cs} →
    FldsFit Γ d as fs → CtorsFit Γ d as cs → CtorsFit Γ d as (ctor n fs ∷ cs)

-- A recursive field is not checked as a fresh `TyOk` of this same
-- declaration: the arguments are, and the declaration is checked once
-- at `dat-ok`. Another declaration is checked on its own.
data FieldFit where
  ff-nat   : ∀ {Γ d as} → FieldFit Γ d as fNat
  ff-bound : ∀ {Γ d as w} → FieldFit Γ d as (fBound w)
  ff-bit   : ∀ {Γ d as} → FieldFit Γ d as fBit
  ff-unit : ∀ {Γ d as} → FieldFit Γ d as fUnit
  ff-pair : ∀ {Γ d as a b} →
    FieldFit Γ d as a → FieldFit Γ d as b → FieldFit Γ d as (fPair a b)
  ff-par  : ∀ {Γ d as i A} → nth as i ≡ just A → TyOk Γ A → FieldFit Γ d as (fPar i)
  ff-self : ∀ {Γ d as fs A} →
    inst d as (fSelf fs) ≡ just A → FldsFit Γ d as fs → FieldFit Γ d as (fSelf fs)
  ff-dat  : ∀ {Γ d e as fs ts} →
    inst d as (fDat e fs) ≡ just (dat e ts) →
    FldsFit Γ d as fs → TyOk Γ (dat e ts) → FieldFit Γ d as (fDat e fs)

data TyOk where
  nat-ok  : ∀ {Γ} → TyOk Γ nat
  bit-ok  : ∀ {Γ} → TyOk Γ bit
  unit-ok : ∀ {Γ} → TyOk Γ unit
  pair-ok : ∀ {Γ A B} → TyOk Γ A → TyOk Γ B → TyOk Γ (pair A B)
  rec-ok  : ∀ {Γ fs} → FieldsOk Γ fs → TyOk Γ (rec fs)
  vec-ok  : ∀ {Γ A e} → TyOk Γ A → NExpOk Γ e → TyOk Γ (vec A e)
  dat-ok  : ∀ {Γ d as} →
    length as ≡ np d → AllTy Γ as → CtorsFit Γ d as (ctorsOf d) → TyOk Γ (dat d as)

-- A case is well formed only as the continuation of the action that
-- binds its scrutinee. The arms are that payload's constructors, or
-- the result's, in declaration order. Each arm is a protocol in the
-- scope of the binder. A bare case is not a protocol on its own.
mutual
  data ArmsOk (Γ : Ctx) : List (String × Proto) → Set where
    arms-none : ArmsOk Γ []
    arms-one  : ∀ {c S as} → ProtoOk Γ S → ArmsOk Γ as → ArmsOk Γ ((c , S) ∷ as)

  data CaseOk (Γ : Ctx) (x : String) (A : Ty) : Scrut → List (String × Proto) → Set where
    ok-val : ∀ {arms} →
      labelled A arms ≡ true →
      ArmsOk Γ arms →
      CaseOk Γ x A (byVal x) arms
    ok-run : ∀ {f R arms cs} →
      runReady f ≡ true →
      labelled R arms ≡ true →
      payCtors A ≡ just cs →
      ArmsOk Γ arms →
      CaseOk Γ x A (byRun f x R) arms

  data ProtoOk : Ctx → Proto → Set where
    end-ok    : ∀ {Γ} → ProtoOk Γ end
    send-ok   : ∀ {Γ A S} → TyOk Γ A → ProtoOk Γ S → ProtoOk Γ (send A S)
    recv-ok   : ∀ {Γ A S} → TyOk Γ A → ProtoOk Γ S → ProtoOk Γ (recv A S)
    dsend-ok  : ∀ {Γ x A S} → TyOk Γ A → ProtoOk ((x , A) ∷ Γ) S → ProtoOk Γ (dsend x A S)
    drecv-ok  : ∀ {Γ x A S} → TyOk Γ A → ProtoOk ((x , A) ∷ Γ) S → ProtoOk Γ (drecv x A S)
    dsend-case : ∀ {Γ x A scrut arms} →
      TyOk Γ A → CaseOk ((x , A) ∷ Γ) x A scrut arms →
      ProtoOk Γ (dsend x A (pcase scrut arms))
    drecv-case : ∀ {Γ x A scrut arms} →
      TyOk Γ A → CaseOk ((x , A) ∷ Γ) x A scrut arms →
      ProtoOk Γ (drecv x A (pcase scrut arms))
    -- The name of an evidence payload is in scope in its bound only.
    esend-ok  : ∀ {Γ x e S} → NExpOk Γ e → ProtoOk Γ S → ProtoOk Γ (esend x e S)
    erecv-ok  : ∀ {Γ x e S} → NExpOk Γ e → ProtoOk Γ S → ProtoOk Γ (erecv x e S)
    -- A numeral bound. The arms are `0` … `w`, and each arm is a
    -- protocol in the same scope: the nat is not a length.
    esend-val : ∀ {Γ x w arms} →
      namesEq (natArms w) (armNames arms) ≡ true →
      ArmsOk Γ arms →
      ProtoOk Γ (esend x (nlit w) (pcase (byVal x) arms))
    erecv-val : ∀ {Γ x w arms} →
      namesEq (natArms w) (armNames arms) ≡ true →
      ArmsOk Γ arms →
      ProtoOk Γ (erecv x (nlit w) (pcase (byVal x) arms))
    -- The run is ready at one nat argument. Every numeral `0` … `w`
    -- evaluates to a constructor of the result, and the arms are those
    -- constructors. The length of that split is `w + 1`.
    esend-run : ∀ {Γ x w f R arms rows} →
      readyN (nsuc nzero) f ≡ true →
      labelled R arms ≡ true →
      natRows f R arms w ≡ just rows →
      length rows ≡ nsuc w →
      ArmsOk Γ arms →
      ProtoOk Γ (esend x (nlit w) (pcase (byRun f x R) arms))
    erecv-run : ∀ {Γ x w f R arms rows} →
      readyN (nsuc nzero) f ≡ true →
      labelled R arms ≡ true →
      natRows f R arms w ≡ just rows →
      length rows ≡ nsuc w →
      ArmsOk Γ arms →
      ProtoOk Γ (erecv x (nlit w) (pcase (byRun f x R) arms))
    -- The product of a numeral-bounded nat and a splittable payload.
    -- The length premise is the product of the widths.
    esend-prod : ∀ {Γ d w b A f R arms cs grid} →
      TyOk Γ A →
      payCtors A ≡ just cs →
      readyN (nsuc (nsuc nzero)) f ≡ true →
      labelled R arms ≡ true →
      prodGrid w A f R arms ≡ just grid →
      length (enumFac (facNat w ∷ facTags cs ∷ [])) ≡ nsuc w * length cs →
      ArmsOk Γ arms →
      ProtoOk Γ (esend d (nlit w)
        (dsend b A (pcase (bySplit f (tagNat d w ∷ tagDat b cs ∷ []) R) arms)))
    erecv-prod : ∀ {Γ d w b A f R arms cs grid} →
      TyOk Γ A →
      payCtors A ≡ just cs →
      readyN (nsuc (nsuc nzero)) f ≡ true →
      labelled R arms ≡ true →
      prodGrid w A f R arms ≡ just grid →
      length (enumFac (facNat w ∷ facTags cs ∷ [])) ≡ nsuc w * length cs →
      ArmsOk Γ arms →
      ProtoOk Γ (erecv d (nlit w)
        (drecv b A (pcase (bySplit f (tagNat d w ∷ tagDat b cs ∷ []) R) arms)))
    -- A product of any other finite factors. The length is the product
    -- of the widths, on the action whose continuation is the case.
    -- The earlier actions are ordinary sends and receives.
    dsend-wide : ∀ {Γ y A f tags R arms rows t cs} →
      TyOk Γ A →
      (wt : WTag tags) →
      lastTag tags ≡ just t →
      tagName t ≡ y →
      payCtors A ≡ just cs →
      tagLabs t ≡ cs →
      readyN (length tags) f ≡ true →
      labelled R arms ≡ true →
      wideRows f R arms (tagsFac tags) ≡ just rows →
      length rows ≡ prodNs (map facWidth (tagsFac tags)) →
      ArmsOk ((y , A) ∷ Γ) arms →
      ProtoOk Γ (dsend y A (pcase (bySplit f tags R) arms))
    drecv-wide : ∀ {Γ y A f tags R arms rows t cs} →
      TyOk Γ A →
      (wt : WTag tags) →
      lastTag tags ≡ just t →
      tagName t ≡ y →
      payCtors A ≡ just cs →
      tagLabs t ≡ cs →
      readyN (length tags) f ≡ true →
      labelled R arms ≡ true →
      wideRows f R arms (tagsFac tags) ≡ just rows →
      length rows ≡ prodNs (map facWidth (tagsFac tags)) →
      ArmsOk ((y , A) ∷ Γ) arms →
      ProtoOk Γ (drecv y A (pcase (bySplit f tags R) arms))
    esend-wide : ∀ {Γ y w f tags R arms rows} →
      (wt : WTag tags) →
      lastTag tags ≡ just (tagNat y w) →
      readyN (length tags) f ≡ true →
      labelled R arms ≡ true →
      wideRows f R arms (tagsFac tags) ≡ just rows →
      length rows ≡ prodNs (map facWidth (tagsFac tags)) →
      ArmsOk Γ arms →
      ProtoOk Γ (esend y (nlit w) (pcase (bySplit f tags R) arms))
    erecv-wide : ∀ {Γ y w f tags R arms rows} →
      (wt : WTag tags) →
      lastTag tags ≡ just (tagNat y w) →
      readyN (length tags) f ≡ true →
      labelled R arms ≡ true →
      wideRows f R arms (tagsFac tags) ≡ just rows →
      length rows ≡ prodNs (map facWidth (tagsFac tags)) →
      ArmsOk Γ arms →
      ProtoOk Γ (erecv y (nlit w) (pcase (bySplit f tags R) arms))
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
pong-ok = get-ok refl (put-ok refl (lit-ok refl) done-end)

other-nat : Conforms [] (get nat "x" (put nat (lit zero) done)) ping
other-nat = get-ok refl (put-ok refl (lit-ok refl) done-end)

-- Echo: receive a value and send it back.
echo : Proc
echo = get nat "v" (put nat (var "v") done)

echo-ok : Conforms [] echo ping
echo-ok = get-ok refl (put-ok refl (var-ok here) done-end)

v-here-ok : Conforms [] (put box (lit v-here) done) (send box end)
v-here-ok = put-ok refl (lit-ok refl) done-end

v-there-ok : Conforms [] (put box (lit v-there) done) (send box end)
v-there-ok = put-ok refl (lit-ok refl) done-end

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
both = cover-ok done-end (put-ok refl (lit-ok refl) done-end)

------------------------------------------------------------------------
-- The search. `yes` carries a derivation. `no` carries its refutation.
-- The Elixir checker follows `decide`.
------------------------------------------------------------------------

data Answerρ (Γ : Ctx) (ρ : Idx) (P : Proc) (S : Proto) : Set where
  yes : Conformsρ Γ ρ P S → Answerρ Γ ρ P S
  no  : ¬ Conformsρ Γ ρ P S → Answerρ Γ ρ P S

-- `sealD` fixes the payload to `applyTy`. The put in hand may
-- only be propositionally that type.
movePut : ∀ {Γ ρ A C y B S P} {v : ValExpr A} →
  (eq : A ≡ C) →
  Answerρ Γ ρ (put C (castV eq v) P) (dsend y B S) →
  Answerρ Γ ρ (put A v P) (dsend y B S)
movePut refl ans = ans

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

decideArg : (Γ : Ctx) (B : Ty) (a : VArg) → Dec (ArgOk Γ B a)
decideArg Γ B (varg C (lit v)) with ty≟ B C
... | no′ ¬eq = no′ (λ { (arg-lit _) → ¬eq refl })
... | yes′ refl with fits v in fq
... | true = yes′ (arg-lit fq)
... | false = no′ (λ { (arg-lit p) → true≢false (trans (sym p) fq) })
decideArg Γ B (varg C (var x)) with ty≟ B C
... | no′ ¬eq = no′ (λ { (arg-var _) → ¬eq refl })
... | yes′ refl with x ∈? Γ ∷? B
... | yes′ p = yes′ (arg-var p)
... | no′ np = no′ (λ { (arg-var p) → np p })
decideArg _ _ (varg _ (call _ _)) = no′ (λ ())

decideArgs : (Γ : Ctx) (ts : List Ty) (as : List VArg) → Dec (ArgsOk Γ ts as)
decideArgs _ [] [] = yes′ args-nil
decideArgs _ [] (_ ∷ _) = no′ (λ ())
decideArgs _ (_ ∷ _) [] = no′ (λ ())
decideArgs Γ (B ∷ ts) (a ∷ as) with decideArg Γ B a
... | no′ na = no′ (λ { (args-cons p _) → na p })
... | yes′ p with decideArgs Γ ts as
... | yes′ ps = yes′ (args-cons p ps)
... | no′ nps = no′ (λ { (args-cons _ ps) → nps ps })

-- A call that mentions a bound name is not evaluated. The run's
-- declared type is the check.
decideTyped : ∀ {A} (Γ : Ctx) (f : String) (as : List VArg) →
  mentionsAll as ≡ true → Dec (ValExprOk Γ (call {A} f as))
decideTyped {A} Γ f as mn = typedOf (findRun runs f) refl
  where
  blocked : evalExpr (call {A} f as) ≡ nothing
  blocked = closed-mention f as mn
  typedOf : (hit : Maybe (List Ty × Ty × RTm × List RDef)) →
    findRun runs f ≡ hit → Dec (ValExprOk Γ (call {A} f as))
  typedOf nothing eq = no′ (λ where
    (call-ok p _) → just≢nothing (trans (sym p) blocked)
    (call-ty _ b _ _) → true≢false (trans (sym b) (cong beforeAt eq)))
  typedOf (just (ts , cod , body , Δ)) eq =
    onReady (callsBefore Δ body) refl (ty≟ cod A) (decideArgs Γ ts as)
    where
    onReady : (b : Bool) → callsBefore Δ body ≡ b →
              Dec (cod ≡ A) → Dec (ArgsOk Γ ts as) →
              Dec (ValExprOk Γ (call {A} f as))
    onReady false cb _ _ = no′ (λ where
      (call-ok p _) → just≢nothing (trans (sym p) blocked)
      (call-ty _ b _ _) → true≢false (trans (sym b) (trans (cong beforeAt eq) cb)))
    onReady true _ (no′ ¬cod) _ = no′ (λ where
      (call-ok p _) → just≢nothing (trans (sym p) blocked)
      (call-ty _ _ c _) → ¬cod (trans (sym (cong codAt eq)) c))
    onReady true _ (yes′ refl) (no′ na) = no′ (λ where
      (call-ok p _) → just≢nothing (trans (sym p) blocked)
      (call-ty _ _ _ ok) → na (subst (λ h → ArgsOk Γ h as) (cong tsAt eq) ok))
    onReady true cb (yes′ refl) (yes′ ok) =
      yes′ (call-ty mn (trans (cong beforeAt eq) cb) (cong codAt eq)
        (subst (λ h → ArgsOk Γ h as) (sym (cong tsAt eq)) ok))

-- Decide if a value expression is well-scoped
decideValExpr : ∀ {A} (Γ : Ctx) (v : ValExpr A) → Dec (ValExprOk Γ v)
decideValExpr Γ (lit v) with fits v in eq
... | true = yes′ (lit-ok eq)
... | false = no′ (λ { (lit-ok p) → true≢false (trans (sym p) eq) })
decideValExpr {A} Γ (var x) with x ∈? Γ ∷? A
... | yes′ p = yes′ (var-ok p)
... | no′ np = no′ (λ { (var-ok p) → np p })
decideValExpr Γ (call {A} f as) with mentionsAll as in mn
... | true = decideTyped Γ f as mn
... | false with evalExpr (call {A} f as) in eq
... | nothing = no′ (λ where
      (call-ok p _) → just≢nothing (trans (sym p) eq)
      (call-ty m _ _ _) → true≢false (trans (sym m) mn))
... | just v with fits v in fq
... | true = yes′ (call-ok eq fq)
... | false = no′ (λ where
      (call-ok p r) →
        true≢false (trans (sym r) (trans (cong fits (just-inj (trans (sym p) eq))) fq))
      (call-ty m _ _ _) → true≢false (trans (sym m) mn))

put-type : ∀ {Γ ρ A B v P S} → Conformsρ Γ ρ (put A v P) (send B S) → A ≡ applyTy ρ B
put-type (put-ok eq _ _) = eq

get-type : ∀ {Γ ρ A B x P S} → Conformsρ Γ ρ (get A x P) (recv B S) → A ≡ applyTy ρ B
get-type (get-ok eq _) = eq

dput-type : ∀ {Γ ρ A B y v P S} → Conformsρ Γ ρ (put A v P) (dsend y B S) → A ≡ applyTy ρ B
dput-type (dput-ok eq _ _ _) = eq
dput-type (dput-arm eq _ _ _) = eq
dput-type (dput-wide eq _ _ _ _ _ _ _ _ _) = eq

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
  Plain S →
  splitAt (dsend y B S) ≡ nothing →
  Dec (ValExprOk Γ v) →
  Answerρ Γ (bind y (ixOf A v) (shadow y ρ)) P S →
  Answerρ Γ ρ (put A v P) (dsend y B S)
on-dput pl sp (yes′ vok) (yes d) = yes (dput-ok refl vok pl d)
on-dput pl sp (yes′ _) (no nd) = no (λ where
  (dput-ok refl _ _ d) → nd d
  (dput-arm _ _ _ _) → plain-not pl
  (dput-wide _ _ _ p _ _ _ _ _ _) → just≢nothing (trans (sym p) sp))
on-dput pl sp (no′ nvok) _ = no (λ where
  (dput-ok refl vok _ _) → nvok vok
  (dput-arm _ vok _ _) → plain-not pl
  (dput-wide _ _ _ p _ _ _ _ _ _) → just≢nothing (trans (sym p) sp))

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

zero≢suc : ∀ {n} → zero ≢ suc n
zero≢suc ()

-- The computed numeral owes what that numeral owes. No recursive call:
-- `v` is the result of evaluation, not a subterm of the call.
leCall : ∀ {Γ f as} (v : Val nat) →
  evalExpr (call {nat} f as) ≡ just v →
  (e : NExp) → Dec (Le Γ (call f as) e)
leCall v eq (nlit n) with toℕ v ≤?ℕ n
... | yes′ p = yes′ (call-le eq (lit-le p))
... | no′ np = no′ (λ { (call-le p (lit-le q)) →
    np (subst (λ w → toℕ w ≤ n) (just-inj (trans (sym p) eq)) q) })
leCall zero eq (nvar _) = yes′ (call-le eq zero-le)
leCall (suc _) eq (nvar _) = no′ (λ { (call-le p zero-le) →
  zero≢suc (just-inj (trans (sym p) eq)) })

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
le? Γ (call f as) e with evalExpr (call {nat} f as) in eq
... | nothing = no′ (λ { (call-le p _) → just≢nothing (trans (sym p) eq) })
... | just v = leCall v eq e

owed? : (Γ : Ctx) (v : ValExpr nat) (m : Maybe NExp) → Dec (Owed Γ v m)
owed? Γ v nothing = no′ (λ ())
owed? Γ v (just e) with le? Γ v e
... | yes′ l = yes′ (owed l)
... | no′ nl = no′ (λ { (owed l) → nl l })

data AnswerSend (Γ : Ctx) (ρ : Idx) (v : ValExpr nat) (P : Proc) (e : NExp) (S : Proto) : Set where
  yes-send : SendCont Γ ρ v P e S → AnswerSend Γ ρ v P e S
  no-send  : ¬ SendCont Γ ρ v P e S → AnswerSend Γ ρ v P e S

on-eput : ∀ {Γ ρ y e v P S} →
  splitAt (esend y e S) ≡ nothing →
  Dec (ValExprOk Γ v) → Dec (Owed Γ v (resolve ρ e)) → AnswerSend Γ ρ v P e S →
  Answerρ Γ ρ (put nat v P) (esend y e S)
on-eput sp (yes′ vok) (yes′ ow) (yes-send s) = yes (eput-ok vok ow s)
on-eput sp (yes′ _) (yes′ _) (no-send ns) = no (λ where
  (eput-ok _ _ s) → ns s
  (eput-wide _ _ p _ _ _ _ _ _) → just≢nothing (trans (sym p) sp))
on-eput sp (yes′ _) (no′ nw) _ = no (λ where
  (eput-ok _ ow _) → nw ow
  (eput-wide _ _ p _ _ _ _ _ _) → just≢nothing (trans (sym p) sp))
on-eput sp (no′ nvok) _ _ = no (λ where
  (eput-ok vok _ _) → nvok vok
  (eput-wide _ _ p _ _ _ _ _ _) → just≢nothing (trans (sym p) sp))

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
isend-bit (call _ _) _ _ = no (λ ())

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

data AnswerArms (Γ : Ctx) (ρ : Idx) (A : Ty) (i : ℕ) (ps : List PArm) (S : Proto) : Set where
  yes-arms : Arms Γ ρ A i ps S → AnswerArms Γ ρ A i ps S
  no-arms  : ¬ Arms Γ ρ A i ps S → AnswerArms Γ ρ A i ps S

data AnswerAt (Γ : Ctx) (ρ : Idx) (A : Ty) (arms : List (String × Proto)) (ps : List PArm) : Set where
  yes-at : ArmsAt Γ ρ A arms ps → AnswerAt Γ ρ A arms ps
  no-at  : ¬ ArmsAt Γ ρ A arms ps → AnswerAt Γ ρ A arms ps

data AnswerRun (Γ : Ctx) (ρ : Idx) (f : String) (A R : Ty)
    (arms : List (String × Proto)) (cs : List String) (ps : List PArm) : Set where
  yes-cr : ArmsRun Γ ρ f A R arms cs ps → AnswerRun Γ ρ f A R arms cs ps
  no-cr  : ¬ ArmsRun Γ ρ f A R arms cs ps → AnswerRun Γ ρ f A R arms cs ps

data AnswerFork (Γ : Ctx) (ρ : Idx) (B : Ty) (par : List Slot) (pxs : List String)
    (ch : List (String × Split)) (qs : List PArm) : Set where
  yes-fk : ForkArms Γ ρ B par pxs ch qs → AnswerFork Γ ρ B par pxs ch qs
  no-fk  : ¬ ForkArms Γ ρ B par pxs ch qs → AnswerFork Γ ρ B par pxs ch qs

data AnswerCov (Γ : Ctx) (ρ : Idx) (rows : List (String × Proto)) (ps : List PArm) : Set where
  yes-cov : CovNat Γ ρ rows ps → AnswerCov Γ ρ rows ps
  no-cov  : ¬ CovNat Γ ρ rows ps → AnswerCov Γ ρ rows ps

data AnswerCell (Γ : Ctx) (ρ : Idx) (x : String) (rows : List (String × Proto)) (P : Proc) : Set where
  yes-cell : Cell Γ ρ x rows P → AnswerCell Γ ρ x rows P
  no-cell  : ¬ Cell Γ ρ x rows P → AnswerCell Γ ρ x rows P

data AnswerProd (Γ : Ctx) (ρ : Idx) (A : Ty) (x : String) (w : ℕ)
    (cs : List String) (grid : List (List (String × Proto))) (ps : List PArm) : Set where
  yes-pc : ProdCov Γ ρ A x w cs grid ps → AnswerProd Γ ρ A x w cs grid ps
  no-pc  : ¬ ProdCov Γ ρ A x w cs grid ps → AnswerProd Γ ρ A x w cs grid ps

data AnswerWA (Γ : Ctx) (ρ : Idx) (A : Ty) (labs : List String) (ts : List Tag)
    (rows : List (List String × Proto)) (ps : List PArm) : Set where
  yes-wa : WArms Γ ρ A labs ts rows ps → AnswerWA Γ ρ A labs ts rows ps
  no-wa  : ¬ WArms Γ ρ A labs ts rows ps → AnswerWA Γ ρ A labs ts rows ps

data AnswerW (Γ : Ctx) (ρ : Idx) (ts : List Tag)
    (rows : List (List String × Proto)) (P : Proc) : Set where
  yes-w : WCover Γ ρ ts rows P → AnswerW Γ ρ ts rows P
  no-w  : ¬ WCover Γ ρ ts rows P → AnswerW Γ ρ ts rows P

-- A process that is not itself a match. Only the common-protocol
-- continuation applies to it.
data NotMatch : Proc → Set where
  nm-done  : NotMatch done
  nm-stop  : NotMatch stop
  nm-put   : ∀ {A v P} → NotMatch (put A v P)
  nm-get   : ∀ {A x P} → NotMatch (get A x P)
  nm-pick0 : ∀ {P} → NotMatch (pick0 P)
  nm-pick1 : ∀ {P} → NotMatch (pick1 P)
  nm-cover : ∀ {P Q} → NotMatch (cover P Q)
  nm-iget  : ∀ {x P Q} → NotMatch (iget x P Q)

-- The puts read off a wide product, plus the arm they select.
data Walk (Γ : Ctx) (ρ : Idx) (f : String) (R : Ty)
    (arms : List (String × Proto)) (acc : List Got) :
    List Tag → Proto → Proc → Set where
  walk-yes : ∀ {ts proto proc Q gs T} →
    PutSpine Γ ts proto proc Q gs →
    pickRead (acc ++ gs) f R arms ≡ just T →
    Conformsρ Γ ρ Q T →
    Walk Γ ρ f R arms acc ts proto proc
  walk-no : ∀ {ts proto proc} →
    (∀ {Q gs T} →
      PutSpine Γ ts proto proc Q gs →
      pickRead (acc ++ gs) f R arms ≡ just T →
      Conformsρ Γ ρ Q T → ⊥) →
    Walk Γ ρ f R arms acc ts proto proc

noSpine : ∀ {Γ ρ f R arms acc ts proto proc} →
  (∀ {Q gs} → PutSpine Γ ts proto proc Q gs → ⊥) →
  Walk Γ ρ f R arms acc ts proto proc
noSpine ns = walk-no (λ spin _ _ → ns spin)

openCover : ∀ {Γ ρ ts rows P} → NotMatch P → WCover Γ ρ ts rows P →
  Σ Proto (λ S → sameRows rows ≡ just S × Conformsρ Γ ρ P S)
openCover nm-done (wc-same eq c) = _ , eq , c
openCover nm-stop (wc-same eq c) = _ , eq , c
openCover nm-put (wc-same eq c) = _ , eq , c
openCover nm-get (wc-same eq c) = _ , eq , c
openCover nm-pick0 (wc-same eq c) = _ , eq , c
openCover nm-pick1 (wc-same eq c) = _ , eq , c
openCover nm-cover (wc-same eq c) = _ , eq , c
openCover nm-iget (wc-same eq c) = _ , eq , c

list≟ : (xs ys : List String) → Dec (xs ≡ ys)
list≟ [] [] = yes′ refl
list≟ [] (_ ∷ _) = no′ (λ ())
list≟ (_ ∷ _) [] = no′ (λ ())
list≟ (x ∷ xs) (y ∷ ys) with x ≟ y
... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
... | yes′ refl with list≟ xs ys
... | yes′ eq = yes′ (cong (x ∷_) eq)
... | no′ ¬eq = no′ (λ { refl → ¬eq refl })

cover? : (A : Ty) (ps : List PArm) → Dec (Covered A ps)
cover? bit [] = no′ (λ ())
cover? bit (_ ∷ []) = no′ (λ ())
cover? bit (_ ∷ _ ∷ []) = yes′ bit-cov
cover? bit (_ ∷ _ ∷ _ ∷ _) = no′ (λ ())
cover? nat _ = no′ (λ ())
cover? unit _ = no′ (λ ())
cover? (pair _ _) (prod (pPair _ _) _ ∷ []) = yes′ pair-cov
cover? (pair _ _) (prod (pRec _) _ ∷ []) = no′ (λ ())
cover? (pair _ _) (bare _ ∷ []) = no′ (λ ())
cover? (pair _ _) (named _ _ _ ∷ []) = no′ (λ ())
cover? (pair _ _) (fork _ _ _ _ ∷ []) = no′ (λ ())
cover? (pair _ _) [] = no′ (λ ())
cover? (pair _ _) (_ ∷ _ ∷ _) = no′ (λ ())
cover? (rec fs) (prod (pRec bs) _ ∷ []) with fits? fs bs
... | yes′ f = yes′ (rec-cov f)
... | no′ ¬f = no′ (λ { (rec-cov f) → ¬f f })
cover? (rec _) (prod (pPair _ _) _ ∷ []) = no′ (λ ())
cover? (rec _) (bare _ ∷ []) = no′ (λ ())
cover? (rec _) (named _ _ _ ∷ []) = no′ (λ ())
cover? (rec _) (fork _ _ _ _ ∷ []) = no′ (λ ())
cover? (rec _) [] = no′ (λ ())
cover? (rec _) (_ ∷ _ ∷ _) = no′ (λ ())
cover? (vec _ _) _ = no′ (λ ())
cover? (dat d _) ps with length ps ≟ℕ length (ctorsOf d)
... | yes′ eq = yes′ (dat-cov eq)
... | no′ ¬eq = no′ (λ { (dat-cov eq) → ¬eq eq })

on-mget : ∀ {Γ ρ A B x ps S} →
  Dec (A ≡ applyTy ρ B) →
  Dec (Covered A ps) →
  AnswerArms ((x , A) ∷ Γ) ρ A nzero ps S →
  Answerρ Γ ρ (mget A x ps) (recv B S)
on-mget (yes′ refl) (yes′ c) (yes-arms ds) = yes (mget-ok refl c ds)
on-mget (yes′ refl) (yes′ _) (no-arms nd) = no (λ { (mget-ok refl _ ds) → nd ds })
on-mget (yes′ refl) (no′ nc) _ = no (λ { (mget-ok refl c _) → nc c })
on-mget (no′ ¬eq) _ _ = no (λ { (mget-ok eq _ _) → ¬eq eq })

-- The scrutinee is the binder, so the arm list is the one `mget` carries.
on-at : ∀ {Γ ρ B x y ps arms} →
  let A = applyTy ρ B in
  Covered A ps →
  labelled A arms ≡ true →
  AnswerAt ((x , A) ∷ Γ) (renameIdx y x (shadow y ρ)) A arms ps →
  Answerρ Γ ρ (mget A x ps) (drecv y B (pcase (byVal y) arms))
on-at c lb (yes-at ds) = yes (mget-val refl c lb ds)
on-at _ _ (no-at nd) = no (λ { (mget-val _ _ _ ds) → nd ds })

on-run : ∀ {Γ ρ B x y f R ps arms cs} →
  let A = applyTy ρ B in
  Covered A ps →
  runReady f ≡ true →
  labelled R arms ≡ true →
  payCtors A ≡ just cs →
  AnswerRun ((x , A) ∷ Γ) (renameIdx y x (shadow y ρ)) f A R arms cs ps →
  Answerρ Γ ρ (mget A x ps) (drecv y B (pcase (byRun f y R) arms))
on-run c rd lb eq (yes-cr ds) = yes (mget-run refl c rd lb eq ds)
on-run {Γ} {ρ} {B} {x} {y} {f} {R} {ps} {arms} _ _ _ eq (no-cr nd) =
  no (λ { (mget-run _ _ _ _ p ds) →
    nd (subst (λ cs →
          ArmsRun ((x , applyTy ρ B) ∷ Γ) (renameIdx y x (shadow y ρ)) f (applyTy ρ B) R arms cs ps)
        (just-inj (trans (sym p) eq)) ds) })

castFork : ∀ {ρ B C Δ Θ par pxs ch dh qs} →
  Δ ≡ Θ → B ≡ C → ch ≡ dh →
  ForkArms Δ ρ B par pxs ch qs → ForkArms Θ ρ C par pxs dh qs
castFork refl refl refl fk = fk

chOf : ∀ {i j ch dh} → node i ch ≡ node j dh → ch ≡ dh
chOf refl = refl

nodeIdx : ∀ {i j ch dh} → node i ch ≡ node j dh → i ≡ j
nodeIdx refl = refl

-- The product is decided before any recursive call. One `with` on this
-- view keeps the arm list a subterm of the `mget`.
data RecvView (Γ : Ctx) (ρ : Idx) (A : Ty) (x : String) (ps : List PArm)
              (y : String) (B : Ty) (f : String) (tags : List Tag)
              (R : Ty) (arms : List (String × Proto)) : Set where
  rv-data : (d : String) (w : ℕ) (cs : List String) (grid : List (List (String × Proto))) →
      tags ≡ (tagNat d w ∷ tagDat y cs ∷ []) →
      A ≡ applyTy ρ B →
      payCtors A ≡ just cs →
      readyN (nsuc (nsuc nzero)) f ≡ true →
      labelled R arms ≡ true →
      prodGrid w A f R arms ≡ just grid →
      RecvView Γ ρ A x ps y B f tags R arms
  rv-bit : (d : String) (w : ℕ) (grid : List (List (String × Proto))) →
      tags ≡ (tagNat d w ∷ tagBit y ∷ []) →
      A ≡ bit →
      B ≡ bit →
      readyN (nsuc (nsuc nzero)) f ≡ true →
      labelled R arms ≡ true →
      prodGrid w bit f R arms ≡ just grid →
      RecvView Γ ρ A x ps y B f tags R arms
  rv-wide : (wt : WTag tags) (t : Tag) (cs : List String)
      (rows : List (List String × Proto)) →
      A ≡ applyTy ρ B →
      lastTag tags ≡ just t →
      tagName t ≡ y →
      payCtors A ≡ just cs →
      tagLabs t ≡ cs →
      readyN (length tags) f ≡ true →
      labelled R arms ≡ true →
      wideRows f R arms (tagsFac tags) ≡ just rows →
      length rows ≡ prodNs (map facWidth (tagsFac tags)) →
      RecvView Γ ρ A x ps y B f tags R arms
  rv-no : (¬ Conformsρ Γ ρ (mget A x ps)
             (drecv y B (pcase (bySplit f tags R) arms))) →
      RecvView Γ ρ A x ps y B f tags R arms

dataView : (Γ : Ctx) (ρ : Idx) (A : Ty) (x : String) (ps : List PArm)
    (y : String) (B : Ty) (f : String) (R : Ty) (arms : List (String × Proto))
    (d : String) (w : ℕ) (z : String) (cs : List String) →
    RecvView Γ ρ A x ps y B f (tagNat d w ∷ tagDat z cs ∷ []) R arms
dataView Γ ρ A x ps y B f R arms d w z cs with z ≟ y
... | no′ z≢y = rv-no (λ where
      (mget-prod _ _ _ _ _ _) → z≢y refl
      (mget-wide () _ _ _ _ _ _ _ _ _ _))
... | yes′ refl with ty≟ A (applyTy ρ B)
... | no′ ¬eq = rv-no (λ where
      (mget-prod eq _ _ _ _ _) → ¬eq eq
      (mget-wide () _ _ _ _ _ _ _ _ _ _))
... | yes′ refl with payCtors A in ep
... | nothing = rv-no (λ where
      (mget-prod _ p _ _ _ _) → just≢nothing (trans (sym p) ep)
      (mget-wide () _ _ _ _ _ _ _ _ _ _))
... | just ds with list≟ ds cs
... | no′ ¬cs = rv-no (λ where
      (mget-prod _ p _ _ _ _) → ¬cs (just-inj (trans (sym ep) p))
      (mget-wide () _ _ _ _ _ _ _ _ _ _))
... | yes′ refl with readyN (nsuc (nsuc nzero)) f in rd
... | false = rv-no (λ where
      (mget-prod _ _ p _ _ _) → true≢false (trans (sym p) rd)
      (mget-wide () _ _ _ _ _ _ _ _ _ _))
... | true with labelled R arms in lb
... | false = rv-no (λ where
      (mget-prod _ _ _ p _ _) → true≢false (trans (sym p) lb)
      (mget-wide () _ _ _ _ _ _ _ _ _ _))
... | true with prodGrid w A f R arms in pg
... | nothing = rv-no (λ where
      (mget-prod _ _ _ _ p _) → just≢nothing (trans (sym p) pg)
      (mget-wide () _ _ _ _ _ _ _ _ _ _))
... | just grid = rv-data d w cs grid refl refl ep rd lb pg

bitView : (Γ : Ctx) (ρ : Idx) (A : Ty) (x : String) (ps : List PArm)
    (y : String) (B : Ty) (f : String) (R : Ty) (arms : List (String × Proto))
    (d : String) (w : ℕ) (z : String) →
    RecvView Γ ρ A x ps y B f (tagNat d w ∷ tagBit z ∷ []) R arms
bitView Γ ρ A x ps y B f R arms d w z with z ≟ y
... | no′ z≢y = rv-no (λ where
      (mget-pbit _ _ _ _) → z≢y refl
      (mget-wide () _ _ _ _ _ _ _ _ _ _))
... | yes′ refl with ty≟ A bit
... | no′ ¬eq = rv-no (λ where
      (mget-pbit _ _ _ _) → ¬eq refl
      (mget-wide () _ _ _ _ _ _ _ _ _ _))
... | yes′ refl with ty≟ B bit
... | no′ ¬eq = rv-no (λ where
      (mget-pbit _ _ _ _) → ¬eq refl
      (mget-wide () _ _ _ _ _ _ _ _ _ _))
... | yes′ refl with readyN (nsuc (nsuc nzero)) f in rd
... | false = rv-no (λ where
      (mget-pbit p _ _ _) → true≢false (trans (sym p) rd)
      (mget-wide () _ _ _ _ _ _ _ _ _ _))
... | true with labelled R arms in lb
... | false = rv-no (λ where
      (mget-pbit _ p _ _) → true≢false (trans (sym p) lb)
      (mget-wide () _ _ _ _ _ _ _ _ _ _))
... | true with prodGrid w bit f R arms in pg
... | nothing = rv-no (λ where
      (mget-pbit _ _ p _) → just≢nothing (trans (sym p) pg)
      (mget-wide () _ _ _ _ _ _ _ _ _ _))
... | just grid = rv-bit d w grid refl refl refl rd lb pg

-- A wide tag list has a last tag. The two-factor shapes are not wide.
lastSome : ∀ {t : Tag} (ts : List Tag) → lastTag (t ∷ ts) ≢ nothing
lastSome [] ()
lastSome (_ ∷ us) eq = lastSome us eq

lastWide : ∀ {ts} → WTag ts → lastTag ts ≡ nothing → ⊥
lastWide (wt-bit {ts = ts}) eq = lastSome ts eq
lastWide (wt-dat {ts = ts}) eq = lastSome ts eq
lastWide (wt-nn {ts = ts}) eq = lastSome ts eq
lastWide (wt-nd {ts = ts}) eq = lastSome ts eq
lastWide (wt-nb {ts = ts}) eq = lastSome ts eq

-- The only receive of a wide product. Matching it on a concrete tag
-- list keeps the exact two-factor rules from unifying.
data WideGet (Γ : Ctx) (ρ : Idx) (A : Ty) (x : String) (ps : List PArm)
    (y : String) (B : Ty) (f : String) (tags : List Tag)
    (R : Ty) (arms : List (String × Proto)) : Set where
  wide-get :
    WTag tags →
    A ≡ applyTy ρ B →
    (u : Tag) →
    lastTag tags ≡ just u →
    tagName u ≡ y →
    (cs : List String) →
    payCtors A ≡ just cs →
    tagLabs u ≡ cs →
    readyN (length tags) f ≡ true →
    labelled R arms ≡ true →
    (rows : List (List String × Proto)) →
    wideRows f R arms (tagsFac tags) ≡ just rows →
    length rows ≡ prodNs (map facWidth (tagsFac tags)) →
    WArms ((x , A) ∷ Γ) ρ A cs (rev (dropLast tags)) rows ps →
    WideGet Γ ρ A x ps y B f tags R arms

openWide : ∀ {Γ ρ A x ps y B f R arms} (tags : List Tag) →
  WTag tags →
  Conformsρ Γ ρ (mget A x ps) (drecv y B (pcase (bySplit f tags R) arms)) →
  WideGet Γ ρ A x ps y B f tags R arms
openWide [] () _
openWide (_ ∷ []) () _
openWide (tagNat _ _ ∷ tagDat _ _ ∷ []) () _
openWide (tagNat _ _ ∷ tagBit _ ∷ []) () _
openWide (tagBit _ ∷ _ ∷ _) wt c with c
... | mget-wide w eq p q pc tl rd lb wr len cov =
    wide-get w eq _ p q _ pc tl rd lb _ wr len cov
openWide (tagDat _ _ ∷ _ ∷ _) wt c with c
... | mget-wide w eq p q pc tl rd lb wr len cov =
    wide-get w eq _ p q _ pc tl rd lb _ wr len cov
openWide (tagNat _ _ ∷ tagNat _ _ ∷ _) wt c with c
... | mget-wide w eq p q pc tl rd lb wr len cov =
    wide-get w eq _ p q _ pc tl rd lb _ wr len cov
openWide (tagNat _ _ ∷ tagDat _ _ ∷ _ ∷ _) wt c with c
... | mget-wide w eq p q pc tl rd lb wr len cov =
    wide-get w eq _ p q _ pc tl rd lb _ wr len cov
openWide (tagNat _ _ ∷ tagBit _ ∷ _ ∷ _) wt c with c
... | mget-wide w eq p q pc tl rd lb wr len cov =
    wide-get w eq _ p q _ pc tl rd lb _ wr len cov

refuseName : ∀ {Γ ρ A x ps y B f tags R arms t} →
  tagName t ≢ y →
  lastTag tags ≡ just t →
  WideGet Γ ρ A x ps y B f tags R arms → ⊥
refuseName {y = y} ¬n lt (wide-get _ _ _ p q _ _ _ _ _ _ _ _ _) =
  ¬n (subst (λ z → tagName z ≡ y) (just-inj (trans (sym p) lt)) q)

refuseTy : ∀ {Γ ρ A x ps y B f tags R arms} →
  A ≢ applyTy ρ B →
  WideGet Γ ρ A x ps y B f tags R arms → ⊥
refuseTy ¬eq (wide-get _ eq _ _ _ _ _ _ _ _ _ _ _ _) = ¬eq eq

refusePay : ∀ {Γ ρ A x ps y B f tags R arms} →
  payCtors A ≡ nothing →
  WideGet Γ ρ A x ps y B f tags R arms → ⊥
refusePay ep (wide-get _ _ _ _ _ _ p _ _ _ _ _ _ _) =
  just≢nothing (trans (sym p) ep)

refuseLabs : ∀ {Γ ρ A x ps y B f tags R arms t ds} →
  tagLabs t ≢ ds →
  lastTag tags ≡ just t →
  payCtors A ≡ just ds →
  WideGet Γ ρ A x ps y B f tags R arms → ⊥
refuseLabs ¬labs lt ep (wide-get _ _ _ p0 _ _ p1 p2 _ _ _ _ _ _) =
  ¬labs (trans (sym (cong tagLabs (just-inj (trans (sym p0) lt))))
          (trans p2 (just-inj (trans (sym p1) ep))))

refuseReady : ∀ {Γ ρ A x ps y B f tags R arms} →
  readyN (length tags) f ≡ false →
  WideGet Γ ρ A x ps y B f tags R arms → ⊥
refuseReady rd (wide-get _ _ _ _ _ _ _ _ p _ _ _ _ _) =
  true≢false (trans (sym p) rd)

refuseLab : ∀ {Γ ρ A x ps y B f tags R arms} →
  labelled R arms ≡ false →
  WideGet Γ ρ A x ps y B f tags R arms → ⊥
refuseLab lb (wide-get _ _ _ _ _ _ _ _ _ p _ _ _ _) =
  true≢false (trans (sym p) lb)

refuseRows : ∀ {Γ ρ A x ps y B f tags R arms} →
  wideRows f R arms (tagsFac tags) ≡ nothing →
  WideGet Γ ρ A x ps y B f tags R arms → ⊥
refuseRows wr (wide-get _ _ _ _ _ _ _ _ _ _ _ p _ _) =
  just≢nothing (trans (sym p) wr)

refuseLen : ∀ {Γ ρ A x ps y B f tags R arms rows} →
  length rows ≢ prodNs (map facWidth (tagsFac tags)) →
  wideRows f R arms (tagsFac tags) ≡ just rows →
  WideGet Γ ρ A x ps y B f tags R arms → ⊥
refuseLen {tags = tags} ¬len wr (wide-get _ _ _ _ _ _ _ _ _ _ _ p len _) =
  ¬len (subst (λ rs → length rs ≡ prodNs (map facWidth (tagsFac tags)))
          (just-inj (trans (sym p) wr)) len)

-- The boolean premises of a wide receive. `armsDec` searches the arms.
wideNamed : (Γ : Ctx) (ρ : Idx) (A : Ty) (x : String) (ps : List PArm)
    (y : String) (B : Ty) (f : String) (tags : List Tag)
    (R : Ty) (arms : List (String × Proto)) (wt : WTag tags)
    (t : Tag) → lastTag tags ≡ just t →
    RecvView Γ ρ A x ps y B f tags R arms
wideNamed Γ ρ A x ps y B f tags R arms wt t lt with tagName t ≟ y
... | no′ ¬n = rv-no (λ c → refuseName ¬n lt (openWide tags wt c))
... | yes′ refl with ty≟ A (applyTy ρ B)
... | no′ ¬eq = rv-no (λ c → refuseTy ¬eq (openWide tags wt c))
... | yes′ refl with payCtors A in ep
... | nothing = rv-no (λ c → refusePay ep (openWide tags wt c))
... | just ds with list≟ (tagLabs t) ds
... | no′ ¬labs = rv-no (λ c → refuseLabs ¬labs lt ep (openWide tags wt c))
... | yes′ refl with readyN (length tags) f in rd
... | false = rv-no (λ c → refuseReady rd (openWide tags wt c))
... | true with labelled R arms in lb
... | false = rv-no (λ c → refuseLab lb (openWide tags wt c))
... | true with wideRows f R arms (tagsFac tags) in wr
... | nothing = rv-no (λ c → refuseRows wr (openWide tags wt c))
... | just rows with length rows ≟ℕ prodNs (map facWidth (tagsFac tags))
... | no′ ¬len = rv-no (λ c → refuseLen ¬len wr (openWide tags wt c))
... | yes′ len = rv-wide wt t ds rows refl lt refl ep refl rd lb wr len

wideView : (Γ : Ctx) (ρ : Idx) (A : Ty) (x : String) (ps : List PArm)
    (y : String) (B : Ty) (f : String) (tags : List Tag)
    (R : Ty) (arms : List (String × Proto)) (wt : WTag tags) →
    RecvView Γ ρ A x ps y B f tags R arms
wideView Γ ρ A x ps y B f tags R arms wt with lastTag tags in lt
... | nothing = rv-no (λ _ → lastWide wt lt)
... | just t = wideNamed Γ ρ A x ps y B f tags R arms wt t lt

recvView : (Γ : Ctx) (ρ : Idx) (A : Ty) (x : String) (ps : List PArm)
    (y : String) (B : Ty) (f : String) (tags : List Tag)
    (R : Ty) (arms : List (String × Proto)) →
    RecvView Γ ρ A x ps y B f tags R arms
recvView Γ ρ A x ps y B f [] R arms =
  rv-no (λ { (mget-wide () _ _ _ _ _ _ _ _ _ _) })
recvView Γ ρ A x ps y B f (_ ∷ []) R arms =
  rv-no (λ { (mget-wide () _ _ _ _ _ _ _ _ _ _) })
recvView Γ ρ A x ps y B f (tagBit x′ ∷ t ∷ ts) R arms =
  wideView Γ ρ A x ps y B f (tagBit x′ ∷ t ∷ ts) R arms wt-bit
recvView Γ ρ A x ps y B f (tagDat x′ cs ∷ t ∷ ts) R arms =
  wideView Γ ρ A x ps y B f (tagDat x′ cs ∷ t ∷ ts) R arms wt-dat
recvView Γ ρ A x ps y B f (tagNat a n ∷ tagNat b m ∷ ts) R arms =
  wideView Γ ρ A x ps y B f (tagNat a n ∷ tagNat b m ∷ ts) R arms wt-nn
recvView Γ ρ A x ps y B f (tagNat d w ∷ tagDat z cs ∷ []) R arms =
  dataView Γ ρ A x ps y B f R arms d w z cs
recvView Γ ρ A x ps y B f (tagNat a n ∷ tagDat x′ cs ∷ t ∷ ts) R arms =
  wideView Γ ρ A x ps y B f (tagNat a n ∷ tagDat x′ cs ∷ t ∷ ts) R arms wt-nd
recvView Γ ρ A x ps y B f (tagNat d w ∷ tagBit z ∷ []) R arms =
  bitView Γ ρ A x ps y B f R arms d w z
recvView Γ ρ A x ps y B f (tagNat a n ∷ tagBit x′ ∷ t ∷ ts) R arms =
  wideView Γ ρ A x ps y B f (tagNat a n ∷ tagBit x′ ∷ t ∷ ts) R arms wt-nb

data NameView (A : Ty) (c : String) (xs : List String) (Γ : Ctx) (k : String) : Set where
  nv-neq  : c ≢ k → NameView A c xs Γ k
  nv-none : armCtxNamed A c xs Γ ≡ nothing → c ≡ k → NameView A c xs Γ k
  nv-just : (Δ : Ctx) → armCtxNamed A c xs Γ ≡ just Δ → c ≡ k → NameView A c xs Γ k

nameView : (A : Ty) (c k : String) (xs : List String) (Γ : Ctx) → NameView A c xs Γ k
nameView A c k xs Γ with c ≟ k
... | no′ neq = nv-neq neq
... | yes′ refl with armCtxNamed A c xs Γ in ac
... | nothing = nv-none ac refl
... | just Δ = nv-just Δ ac refl

useOne : ∀ {Γ ρ x rows p S} →
  (∀ {qs} → p ≢ mget nat x qs) →
  sameArms rows ≡ just S →
  Answerρ Γ ρ p S →
  AnswerCell Γ ρ x rows p
useOne away sa (yes d) = yes-cell (cell-one sa d)
useOne {Γ = Γ} {ρ = ρ} {p = p} away sa (no nd) = no-cell (λ where
  (cell-one q e) →
    nd (subst (λ T → Conformsρ Γ ρ p T) (just-inj (trans (sym q) sa)) e)
  (cell-nat _) → away refl)

useAns : ∀ {Γ ρ x rows p S qs} →
  ¬ CovNat Γ ρ rows qs →
  sameArms rows ≡ just S →
  p ≡ mget nat x qs →
  Answerρ Γ ρ p S →
  AnswerCell Γ ρ x rows p
useAns nc sa refl (yes d) = yes-cell (cell-one sa d)
useAns {Γ = Γ} {ρ = ρ} {p = p} nc sa refl (no nd) = no-cell (λ where
  (cell-nat cov) → nc cov
  (cell-one q e) →
    nd (subst (λ T → Conformsρ Γ ρ p T) (just-inj (trans (sym q) sa)) e))

-- Either the opened constructor has a splittable field here, or it
-- does not. The two cases do not overlap.
data NestView (B : Ty) (c : String) (xs : List String) (i : ℕ) (y : String) (Γ : Ctx) : Set where
  nv-yes : ∀ {Δ C} →
    armCtxNamed B c xs Γ ≡ just Δ →
    nth xs i ≡ just y →
    tyAt B c i ≡ just C →
    splittable C ≡ true →
    NestView B c xs i y Γ
  nv-no  : ¬ NestOk B c xs i y Γ → NestView B c xs i y Γ

nestView : (B : Ty) (c : String) (xs : List String) (i : ℕ) (y : String) (Γ : Ctx) →
  NestView B c xs i y Γ
nestView B c xs i y Γ with armCtxNamed B c xs Γ in ac
... | nothing = nv-no (λ { (nest-ok q _ _ _) → just≢nothing (trans (sym q) ac) })
... | just Δ with hitName xs i y
... | no′ ¬h = nv-no (λ { (nest-ok _ q _ _) → ¬h q })
... | yes′ ni with tyAt B c i in tb
... | nothing = nv-no (λ { (nest-ok _ _ q _) → just≢nothing (trans (sym q) tb) })
... | just C with splittable C in sp
... | false = nv-no (λ { (nest-ok {C = C′} _ _ eq q) →
      true≢false (trans (sym q)
        (subst (λ D → splittable D ≡ false) (just-inj (trans (sym tb) eq)) sp)) })
... | true = nv-yes ac ni tb sp

data BitView (A : Ty) : Set where
  bv-yes : A ≡ bit → BitView A
  bv-no  : A ≢ bit → BitView A

data PremReady (n : ℕ) (f : String) : Set where
  prem-yes : readyN n f ≡ true → PremReady n f
  prem-no  : readyN n f ≡ false → PremReady n f

data PremLab (R : Ty) (arms : List (String × Proto)) : Set where
  plab-yes : labelled R arms ≡ true → PremLab R arms
  plab-no  : labelled R arms ≡ false → PremLab R arms

data PremRows (f : String) (R : Ty) (arms : List (String × Proto)) (ts : List Tag) : Set where
  prows-yes : ∀ {rows} → wideRows f R arms (tagsFac ts) ≡ just rows → PremRows f R arms ts
  prows-no  : wideRows f R arms (tagsFac ts) ≡ nothing → PremRows f R arms ts

data PremLen (rows : List (List String × Proto)) (ts : List Tag) : Set where
  plen-yes : length rows ≡ prodNs (map facWidth (tagsFac ts)) → PremLen rows ts
  plen-no  : length rows ≢ prodNs (map facWidth (tagsFac ts)) → PremLen rows ts

-- One `with` each, and nothing that matches a wide send. The send
-- cannot unfold these.
opaque
  asBit : (A : Ty) → BitView A
  asBit A with ty≟ A bit
  ... | yes′ p = bv-yes p
  ... | no′ ¬p = bv-no ¬p

  premReady : (n : ℕ) (f : String) → PremReady n f
  premReady n f with readyN n f in eq
  ... | true = prem-yes eq
  ... | false = prem-no eq

  premLab : (R : Ty) (arms : List (String × Proto)) → PremLab R arms
  premLab R arms with labelled R arms in eq
  ... | true = plab-yes eq
  ... | false = plab-no eq

  premRows : (f : String) (R : Ty) (arms : List (String × Proto)) (ts : List Tag) →
      PremRows f R arms ts
  premRows f R arms ts with wideRows f R arms (tagsFac ts) in eq
  ... | just rows = prows-yes eq
  ... | nothing = prows-no eq

  premLen : (rows : List (List String × Proto)) (ts : List Tag) → PremLen rows ts
  premLen rows ts with length rows ≟ℕ prodNs (map facWidth (tagsFac ts))
  ... | yes′ p = plen-yes p
  ... | no′ ¬p = plen-no ¬p

-- Every premise, as data. A later block reads it, so the `with`
-- above is not unfolded into the send.
data Prem (n : ℕ) (f : String) (R : Ty) (arms : List (String × Proto))
    (ts : List Tag) : Set where
  p-ready : readyN n f ≡ false → Prem n f R arms ts
  p-lab : readyN n f ≡ true → labelled R arms ≡ false → Prem n f R arms ts
  p-rows : readyN n f ≡ true → labelled R arms ≡ true →
      wideRows f R arms (tagsFac ts) ≡ nothing → Prem n f R arms ts
  p-len : ∀ {rows} → readyN n f ≡ true → labelled R arms ≡ true →
      wideRows f R arms (tagsFac ts) ≡ just rows →
      length rows ≢ prodNs (map facWidth (tagsFac ts)) →
      Prem n f R arms ts
  p-yes : ∀ {rows} → readyN n f ≡ true → labelled R arms ≡ true →
      wideRows f R arms (tagsFac ts) ≡ just rows →
      length rows ≡ prodNs (map facWidth (tagsFac ts)) →
      Prem n f R arms ts

opaque
  premises : (n : ℕ) (f : String) (R : Ty) (arms : List (String × Proto))
      (ts : List Tag) → Prem n f R arms ts
  premises n f R arms ts with premReady n f
  ... | prem-no rd = p-ready rd
  ... | prem-yes rd with premLab R arms
  ... | plab-no lb = p-lab rd lb
  ... | plab-yes lb with premRows f R arms ts
  ... | prows-no wr = p-rows rd lb wr
  ... | prows-yes {rows = rows} wr with premLen rows ts
  ... | plen-no ¬len = p-len rd lb wr ¬len
  ... | plen-yes len = p-yes rd lb wr len


-- The walk result stays opaque, so the premise `with` does not invert it.
opaque
  takeWalk : ∀ {Γ ρ f R arms acc ts proto proc} {B : Set} →
      Walk Γ ρ f R arms acc ts proto proc →
      ((∀ {Q gs T} →
          PutSpine Γ ts proto proc Q gs →
          pickRead (acc ++ gs) f R arms ≡ just T →
          Conformsρ Γ ρ Q T → ⊥) → B) →
      (∀ {Q gs T} →
          PutSpine Γ ts proto proc Q gs →
          pickRead (acc ++ gs) f R arms ≡ just T →
          Conformsρ Γ ρ Q T → B) →
      B
  takeWalk (walk-no nw) miss _ = miss nw
  takeWalk (walk-yes spin pk d) _ ok = ok spin pk d

-- A missed premise of a wide case. The constructor is matched here,
-- not under the `with` that computed the premise.
opaque
  noD : {A : Ty} (Γ : Ctx) (ρ : Idx) (y : String) (v : ValExpr A) (P : Proc)
      (B : Ty) (f : String) (tags : List Tag) (R : Ty)
      (arms : List (String × Proto)) →
      A ≡ applyTy ρ B →
      (∀ {us Q gs g Qy as T rows′} →
        WTag us →
        PutSpine Γ us
          (dsend y B (pcase (bySplit f tags R) arms))
          (put A v P) Q gs →
        splitAt (dsend y B (pcase (bySplit f tags R) arms)) ≡
          just (g , us , Qy , as) →
        readyN (length us) g ≡ true →
        labelled Qy as ≡ true →
        wideRows g Qy as (tagsFac us) ≡ just rows′ →
        length rows′ ≡ prodNs (map facWidth (tagsFac us)) →
        pickRead gs g Qy as ≡ just T →
        Conformsρ Γ ρ Q T → ⊥) →
      Answerρ Γ ρ (put A v P)
        (dsend y B (pcase (bySplit f tags R) arms))
  noD _ _ _ _ _ _ _ _ _ _ _ nw = no (λ where
    (dput-ok _ _ pl _) → plain-not pl
    (dput-arm _ _ p _) → just≢nothing (sym p)
    (dput-wide _ w spin p rd lb wr len pk c) →
      nw w spin p rd lb wr len pk c)

-- The missed premise of a wide put. The known split is an argument,
-- so the row equality is compared with variables, not solved by
-- inverting `wideRows` or `labelled` under a λ.
quadReady : ∀ {Γ : Ctx} {ρ : Idx} {proto : Proto} {proc : Proc}
    {f : String} {tags : List Tag} {R : Ty} {arms : List (String × Proto)} →
  readyN (length tags) f ≡ false →
  splitAt proto ≡ just (f , tags , R , arms) →
  ∀ {us : List Tag} {Q : Proc} {gs : List Got} {g : String} {Qy : Ty}
    {as : List (String × Proto)} {T : Proto}
    {rows′ : List (List String × Proto)} →
  WTag us →
  PutSpine Γ us proto proc Q gs →
  splitAt proto ≡ just (g , us , Qy , as) →
  readyN (length us) g ≡ true →
  labelled Qy as ≡ true →
  wideRows g Qy as (tagsFac us) ≡ just rows′ →
  length rows′ ≡ prodNs (map facWidth (tagsFac us)) →
  pickRead gs g Qy as ≡ just T →
  Conformsρ Γ ρ Q T → ⊥
quadReady {proto = proto} rd sp _ _ p q _ _ _ _ _ =
  readyQuad (splitQuad proto sp p) rd q

quadLab : ∀ {Γ : Ctx} {ρ : Idx} {proto : Proto} {proc : Proc}
    {f : String} {tags : List Tag} {R : Ty} {arms : List (String × Proto)} →
  labelled R arms ≡ false →
  splitAt proto ≡ just (f , tags , R , arms) →
  ∀ {us : List Tag} {Q : Proc} {gs : List Got} {g : String} {Qy : Ty}
    {as : List (String × Proto)} {T : Proto}
    {rows′ : List (List String × Proto)} →
  WTag us →
  PutSpine Γ us proto proc Q gs →
  splitAt proto ≡ just (g , us , Qy , as) →
  readyN (length us) g ≡ true →
  labelled Qy as ≡ true →
  wideRows g Qy as (tagsFac us) ≡ just rows′ →
  length rows′ ≡ prodNs (map facWidth (tagsFac us)) →
  pickRead gs g Qy as ≡ just T →
  Conformsρ Γ ρ Q T → ⊥
quadLab {proto = proto} lb sp _ _ p _ q _ _ _ _ =
  labQuad (splitQuad proto sp p) lb q

quadRows : ∀ {Γ : Ctx} {ρ : Idx} {proto : Proto} {proc : Proc}
    {f : String} {tags : List Tag} {R : Ty} {arms : List (String × Proto)} →
  wideRows f R arms (tagsFac tags) ≡ nothing →
  splitAt proto ≡ just (f , tags , R , arms) →
  ∀ {us : List Tag} {Q : Proc} {gs : List Got} {g : String} {Qy : Ty}
    {as : List (String × Proto)} {T : Proto}
    {rows′ : List (List String × Proto)} →
  WTag us →
  PutSpine Γ us proto proc Q gs →
  splitAt proto ≡ just (g , us , Qy , as) →
  readyN (length us) g ≡ true →
  labelled Qy as ≡ true →
  wideRows g Qy as (tagsFac us) ≡ just rows′ →
  length rows′ ≡ prodNs (map facWidth (tagsFac us)) →
  pickRead gs g Qy as ≡ just T →
  Conformsρ Γ ρ Q T → ⊥
quadRows {proto = proto} wr sp _ _ p _ _ q _ _ _ =
  rowsQuad (splitQuad proto sp p) wr q

quadLen : ∀ {Γ : Ctx} {ρ : Idx} {proto : Proto} {proc : Proc}
    {f : String} {tags : List Tag} {R : Ty} {arms : List (String × Proto)}
    {rows : List (List String × Proto)} →
  length rows ≢ prodNs (map facWidth (tagsFac tags)) →
  wideRows f R arms (tagsFac tags) ≡ just rows →
  splitAt proto ≡ just (f , tags , R , arms) →
  ∀ {us : List Tag} {Q : Proc} {gs : List Got} {g : String} {Qy : Ty}
    {as : List (String × Proto)} {T : Proto}
    {rows′ : List (List String × Proto)} →
  WTag us →
  PutSpine Γ us proto proc Q gs →
  splitAt proto ≡ just (g , us , Qy , as) →
  readyN (length us) g ≡ true →
  labelled Qy as ≡ true →
  wideRows g Qy as (tagsFac us) ≡ just rows′ →
  length rows′ ≡ prodNs (map facWidth (tagsFac us)) →
  pickRead gs g Qy as ≡ just T →
  Conformsρ Γ ρ Q T → ⊥
quadLen {proto = proto} ¬len wr sp _ _ p _ _ q len′ _ _ =
  lenQuad (splitQuad proto sp p) ¬len wr q len′

quadMove : ∀ {Γ : Ctx} {ρ : Idx} {proto : Proto} {proc : Proc}
    {f : String} {tags : List Tag} {R : Ty} {arms : List (String × Proto)} →
  (∀ {Q : Proc} {gs : List Got} {T : Proto} →
    PutSpine Γ tags proto proc Q gs →
    pickRead gs f R arms ≡ just T →
    Conformsρ Γ ρ Q T → ⊥) →
  splitAt proto ≡ just (f , tags , R , arms) →
  ∀ {us : List Tag} {Q : Proc} {gs : List Got} {g : String} {Qy : Ty}
    {as : List (String × Proto)} {T : Proto}
    {rows′ : List (List String × Proto)} →
  WTag us →
  PutSpine Γ us proto proc Q gs →
  splitAt proto ≡ just (g , us , Qy , as) →
  readyN (length us) g ≡ true →
  labelled Qy as ≡ true →
  wideRows g Qy as (tagsFac us) ≡ just rows′ →
  length rows′ ≡ prodNs (map facWidth (tagsFac us)) →
  pickRead gs g Qy as ≡ just T →
  Conformsρ Γ ρ Q T → ⊥
quadMove {proto = proto} nw sp {gs = gs} _ spin p _ _ _ _ pk c =
  nw (moveSpine {gs = gs} (splitQuad proto sp p) spin)
    (movePick {gs = gs} (splitQuad proto sp p) pk) c

-- The walk saw `put A v`. The premise sees the cast `put C (castV eq v)`.
quadCast : ∀ {Γ : Ctx} {ρ : Idx} {A C : Ty} {y : String} {B : Ty} {S : Proto}
    {v : ValExpr A} {P : Proc} {f : String} {tags : List Tag} {R : Ty}
    {arms : List (String × Proto)} →
  (eq : A ≡ C) →
  (∀ {Q : Proc} {gs : List Got} {T : Proto} →
    PutSpine Γ tags (dsend y B S) (put A v P) Q gs →
    pickRead gs f R arms ≡ just T →
    Conformsρ Γ ρ Q T → ⊥) →
  splitAt (dsend y B S) ≡ just (f , tags , R , arms) →
  ∀ {us : List Tag} {Q : Proc} {gs : List Got} {g : String} {Qy : Ty}
    {as : List (String × Proto)} {T : Proto}
    {rows′ : List (List String × Proto)} →
  WTag us →
  PutSpine Γ us (dsend y B S) (put C (castV eq v) P) Q gs →
  splitAt (dsend y B S) ≡ just (g , us , Qy , as) →
  readyN (length us) g ≡ true →
  labelled Qy as ≡ true →
  wideRows g Qy as (tagsFac us) ≡ just rows′ →
  length rows′ ≡ prodNs (map facWidth (tagsFac us)) →
  pickRead gs g Qy as ≡ just T →
  Conformsρ Γ ρ Q T → ⊥
quadCast {y = y} {B = B} {S = S} eq nw sp {gs = gs} _ spin p _ _ _ _ pk c =
  nw (castSpine eq (moveSpine {gs = gs} (splitQuad (dsend y B S) sp p) spin))
    (movePick {gs = gs} (splitQuad (dsend y B S) sp p) pk) c

-- A nat tag is an evidence send. It is not a plain `dsend` spine.
quadNat : ∀ {Γ : Ctx} {ρ : Idx} {A : Ty} {y : String} {B : Ty} {S : Proto}
    {v : ValExpr A} {P : Proc} {f : String} {a : String} {m : ℕ}
    {rest : List Tag} {R : Ty} {arms : List (String × Proto)} →
  splitAt (dsend y B S) ≡ just (f , (tagNat a m ∷ rest) , R , arms) →
  ∀ {us : List Tag} {Q : Proc} {gs : List Got} {g : String} {Qy : Ty}
    {as : List (String × Proto)} {T : Proto}
    {rows′ : List (List String × Proto)} →
  WTag us →
  PutSpine Γ us (dsend y B S) (put A v P) Q gs →
  splitAt (dsend y B S) ≡ just (g , us , Qy , as) →
  readyN (length us) g ≡ true →
  labelled Qy as ≡ true →
  wideRows g Qy as (tagsFac us) ≡ just rows′ →
  length rows′ ≡ prodNs (map facWidth (tagsFac us)) →
  pickRead gs g Qy as ≡ just T →
  Conformsρ Γ ρ Q T → ⊥
quadNat {y = y} {B = B} {S = S} sp _ spin p _ _ _ _ _ _ =
  dsendNat (moveSpine (splitQuad (dsend y B S) sp p) spin)

-- The continuation is the split itself, so a plain put is not a case
-- and `bySplit` selects no arm. A nat tag is an evidence send: it has
-- no spine on `dsend`.
notNat : ∀ {Γ : Ctx} {ρ : Idx} {A : Ty} {y : String} {B : Ty}
    {v : ValExpr A} {P : Proc} {f : String} {a : String} {m : ℕ}
    {rest : List Tag} {R : Ty} {arms : List (String × Proto)} →
  ¬ Conformsρ Γ ρ (put A v P)
      (dsend y B (pcase (bySplit f (tagNat a m ∷ rest) R) arms))
notNat (dput-ok _ _ pl _) = plain-not pl
notNat (dput-arm _ _ p _) = just≢nothing (sym p)
notNat {y = y} {B = B} {f = f} {a = a} {m = m} {rest = rest} {R = R} {arms = arms}
    (dput-wide _ _ spin p _ _ _ _ _ _) =
  dsendNat (moveSpine
    (splitQuad (dsend y B (pcase (bySplit f (tagNat a m ∷ rest) R) arms))
      (caseSplit y B f (tagNat a m ∷ rest) R arms) p) spin)

-- The same missed premise on an evidence send. There is no `WTag`
-- argument: the first tag is the nat being sent.
sendReady : ∀ {Γ : Ctx} {ρ : Idx} {y : String} {n : ℕ} {S : Proto}
    {v : ValExpr nat} {P : Proc} {f : String} {rest : List Tag} {R : Ty}
    {arms : List (String × Proto)} →
  readyN (length (tagNat y n ∷ rest)) f ≡ false →
  splitAt (esend y (nlit n) S) ≡ just (f , (tagNat y n ∷ rest) , R , arms) →
  ∀ {tail : List Tag} {Q : Proc} {gs : List Got} {g : String} {Qy : Ty}
    {as : List (String × Proto)} {T : Proto}
    {rows′ : List (List String × Proto)} →
  PutSpine Γ (tagNat y n ∷ tail) (esend y (nlit n) S) (put nat v P) Q gs →
  splitAt (esend y (nlit n) S) ≡
    just (g , (tagNat y n ∷ tail) , Qy , as) →
  readyN (length (tagNat y n ∷ tail)) g ≡ true →
  labelled Qy as ≡ true →
  wideRows g Qy as (tagsFac (tagNat y n ∷ tail)) ≡ just rows′ →
  length rows′ ≡ prodNs (map facWidth (tagsFac (tagNat y n ∷ tail))) →
  pickRead gs g Qy as ≡ just T →
  Conformsρ Γ ρ Q T → ⊥
sendReady {y = y} {n = n} {S = S} rd sp _ p q _ _ _ _ _ =
  readyQuad (splitQuad (esend y (nlit n) S) sp p) rd q

sendLab : ∀ {Γ : Ctx} {ρ : Idx} {y : String} {n : ℕ} {S : Proto}
    {v : ValExpr nat} {P : Proc} {f : String} {rest : List Tag} {R : Ty}
    {arms : List (String × Proto)} →
  labelled R arms ≡ false →
  splitAt (esend y (nlit n) S) ≡ just (f , (tagNat y n ∷ rest) , R , arms) →
  ∀ {tail : List Tag} {Q : Proc} {gs : List Got} {g : String} {Qy : Ty}
    {as : List (String × Proto)} {T : Proto}
    {rows′ : List (List String × Proto)} →
  PutSpine Γ (tagNat y n ∷ tail) (esend y (nlit n) S) (put nat v P) Q gs →
  splitAt (esend y (nlit n) S) ≡
    just (g , (tagNat y n ∷ tail) , Qy , as) →
  readyN (length (tagNat y n ∷ tail)) g ≡ true →
  labelled Qy as ≡ true →
  wideRows g Qy as (tagsFac (tagNat y n ∷ tail)) ≡ just rows′ →
  length rows′ ≡ prodNs (map facWidth (tagsFac (tagNat y n ∷ tail))) →
  pickRead gs g Qy as ≡ just T →
  Conformsρ Γ ρ Q T → ⊥
sendLab {y = y} {n = n} {S = S} lb sp _ p _ q _ _ _ _ =
  labQuad (splitQuad (esend y (nlit n) S) sp p) lb q

sendRows : ∀ {Γ : Ctx} {ρ : Idx} {y : String} {n : ℕ} {S : Proto}
    {v : ValExpr nat} {P : Proc} {f : String} {rest : List Tag} {R : Ty}
    {arms : List (String × Proto)} →
  wideRows f R arms (tagsFac (tagNat y n ∷ rest)) ≡ nothing →
  splitAt (esend y (nlit n) S) ≡ just (f , (tagNat y n ∷ rest) , R , arms) →
  ∀ {tail : List Tag} {Q : Proc} {gs : List Got} {g : String} {Qy : Ty}
    {as : List (String × Proto)} {T : Proto}
    {rows′ : List (List String × Proto)} →
  PutSpine Γ (tagNat y n ∷ tail) (esend y (nlit n) S) (put nat v P) Q gs →
  splitAt (esend y (nlit n) S) ≡
    just (g , (tagNat y n ∷ tail) , Qy , as) →
  readyN (length (tagNat y n ∷ tail)) g ≡ true →
  labelled Qy as ≡ true →
  wideRows g Qy as (tagsFac (tagNat y n ∷ tail)) ≡ just rows′ →
  length rows′ ≡ prodNs (map facWidth (tagsFac (tagNat y n ∷ tail))) →
  pickRead gs g Qy as ≡ just T →
  Conformsρ Γ ρ Q T → ⊥
sendRows {y = y} {n = n} {S = S} wr sp _ p _ _ q _ _ _ =
  rowsQuad (splitQuad (esend y (nlit n) S) sp p) wr q

sendLen : ∀ {Γ : Ctx} {ρ : Idx} {y : String} {n : ℕ} {S : Proto}
    {v : ValExpr nat} {P : Proc} {f : String} {rest : List Tag} {R : Ty}
    {arms : List (String × Proto)} {rows : List (List String × Proto)} →
  length rows ≢ prodNs (map facWidth (tagsFac (tagNat y n ∷ rest))) →
  wideRows f R arms (tagsFac (tagNat y n ∷ rest)) ≡ just rows →
  splitAt (esend y (nlit n) S) ≡ just (f , (tagNat y n ∷ rest) , R , arms) →
  ∀ {tail : List Tag} {Q : Proc} {gs : List Got} {g : String} {Qy : Ty}
    {as : List (String × Proto)} {T : Proto}
    {rows′ : List (List String × Proto)} →
  PutSpine Γ (tagNat y n ∷ tail) (esend y (nlit n) S) (put nat v P) Q gs →
  splitAt (esend y (nlit n) S) ≡
    just (g , (tagNat y n ∷ tail) , Qy , as) →
  readyN (length (tagNat y n ∷ tail)) g ≡ true →
  labelled Qy as ≡ true →
  wideRows g Qy as (tagsFac (tagNat y n ∷ tail)) ≡ just rows′ →
  length rows′ ≡ prodNs (map facWidth (tagsFac (tagNat y n ∷ tail))) →
  pickRead gs g Qy as ≡ just T →
  Conformsρ Γ ρ Q T → ⊥
sendLen {y = y} {n = n} {S = S} ¬len wr sp _ p _ _ q len′ _ _ =
  lenQuad (splitQuad (esend y (nlit n) S) sp p) ¬len wr q len′

sendMove : ∀ {Γ : Ctx} {ρ : Idx} {y : String} {n : ℕ} {S : Proto}
    {v : ValExpr nat} {P : Proc} {f : String} {rest : List Tag} {R : Ty}
    {arms : List (String × Proto)} →
  (∀ {Q : Proc} {gs : List Got} {T : Proto} →
    PutSpine Γ (tagNat y n ∷ rest) (esend y (nlit n) S) (put nat v P) Q gs →
    pickRead gs f R arms ≡ just T →
    Conformsρ Γ ρ Q T → ⊥) →
  splitAt (esend y (nlit n) S) ≡ just (f , (tagNat y n ∷ rest) , R , arms) →
  ∀ {tail : List Tag} {Q : Proc} {gs : List Got} {g : String} {Qy : Ty}
    {as : List (String × Proto)} {T : Proto}
    {rows′ : List (List String × Proto)} →
  PutSpine Γ (tagNat y n ∷ tail) (esend y (nlit n) S) (put nat v P) Q gs →
  splitAt (esend y (nlit n) S) ≡
    just (g , (tagNat y n ∷ tail) , Qy , as) →
  readyN (length (tagNat y n ∷ tail)) g ≡ true →
  labelled Qy as ≡ true →
  wideRows g Qy as (tagsFac (tagNat y n ∷ tail)) ≡ just rows′ →
  length rows′ ≡ prodNs (map facWidth (tagsFac (tagNat y n ∷ tail))) →
  pickRead gs g Qy as ≡ just T →
  Conformsρ Γ ρ Q T → ⊥
sendMove {y = y} {n = n} {S = S} nw sp {gs = gs} spin p _ _ _ _ pk c =
  nw (moveSpine {gs = gs} (splitQuad (esend y (nlit n) S) sp p) spin)
    (movePick {gs = gs} (splitQuad (esend y (nlit n) S) sp p) pk) c

-- The tail walk failed. The outer nat names the same raw value, so
-- the read moves back one got. The selected protocol is the one the
-- tail already named.
carryNat : ∀ {Γ : Ctx} {ρ : Idx} {f : String} {R : Ty}
    {arms : List (String × Proto)} {acc : List Got} {x : String} {w : ℕ}
    {ts : List Tag} {y : String} {m : ℕ} {S : Proto} {P : Proc} {r : Raw}
    {v : ValExpr nat} →
  natGot v w ≡ just (gVal r) →
  (∀ {Q : Proc} {gs : List Got} {T : Proto} →
    PutSpine Γ ts S P Q gs →
    pickRead ((acc ++ (gVal r ∷ [])) ++ gs) f R arms ≡ just T →
    Conformsρ Γ ρ Q T → ⊥) →
  ∀ {Q : Proc} {gs : List Got} {T : Proto} →
  PutSpine Γ (tagNat x w ∷ ts) (esend y (nlit m) S) (put nat v P) Q gs →
  pickRead (acc ++ gs) f R arms ≡ just T →
  Conformsρ Γ ρ Q T → ⊥
carryNat {f = f} {R = R} {arms = arms} {acc = acc} {r = r} ng k
    {T = T} (sp-nat {r = r′} {gs = gs} _ _ ng′ _ _ spin) q c =
  k spin (unshiftRead {f = f} {R = R} {arms = arms} {T = T} acc (gVal r) gs
    (subst (λ h → pickRead (acc ++ (h ∷ gs)) f R arms ≡ just T)
      (just-inj (trans (sym ng′) ng)) q)) c

-- Whether a sent value can be the bit tag. The `with`s stay here, so
-- the walk on the process under the put is not under them.
data BitPrep (Γ : Ctx) {A : Ty} (v : ValExpr A) (x y : String) (B : Ty) : Set where
  bp-ty : A ≢ bit → BitPrep Γ v x y B
  bp-name : A ≡ bit → x ≢ y → BitPrep Γ v x y B
  bp-payty : A ≡ bit → x ≡ y → B ≢ bit → BitPrep Γ v x y B
  bp-miss : A ≡ bit → x ≡ y → B ≡ bit → payGot v ≡ nothing → BitPrep Γ v x y B
  bp-bad : A ≡ bit → x ≡ y → B ≡ bit → (g : Got) → payGot v ≡ just g →
      ¬ ValExprOk Γ v → BitPrep Γ v x y B
  bp-yes : A ≡ bit → x ≡ y → B ≡ bit → (g : Got) → payGot v ≡ just g →
      ValExprOk Γ v → BitPrep Γ v x y B

opaque
  bitPrep : (Γ : Ctx) {A : Ty} (v : ValExpr A) (x y : String) (B : Ty) →
      BitPrep Γ v x y B
  bitPrep Γ {A} v x y B with ty≟ A bit
  ... | no′ ¬A = bp-ty ¬A
  ... | yes′ refl with x ≟ y
  ... | no′ ¬xy = bp-name refl ¬xy
  ... | yes′ refl with ty≟ B bit
  ... | no′ ¬B = bp-payty refl refl ¬B
  ... | yes′ refl with payGot v in pg
  ... | nothing = bp-miss refl refl refl pg
  ... | just g with decideValExpr Γ v
  ... | no′ nv = bp-bad refl refl refl g pg nv
  ... | yes′ vok = bp-yes refl refl refl g pg vok

closeBit : (Γ : Ctx) (ρ : Idx) (f : String) (R : Ty) (arms : List (String × Proto))
    (acc : List Got) (x : String) (ts : List Tag) (y : String) (B : Ty) (S : Proto)
    {A : Ty} (v : ValExpr A) (P : Proc) →
    BitPrep Γ v x y B →
    ((g : Got) → Walk Γ ρ f R arms (acc ++ (g ∷ [])) ts S P) →
    Walk Γ ρ f R arms acc (tagBit x ∷ ts) (dsend y B S) (put A v P)
closeBit _ _ _ _ _ _ _ _ _ _ _ _ _ (bp-ty ¬A) _ = noSpine (badBitPut ¬A)
closeBit _ _ _ _ _ _ _ _ _ _ _ _ _ (bp-name refl ¬xy) _ =
  noSpine (λ { (sp-bit q _ _ _ _) → ¬xy q })
closeBit _ _ _ _ _ _ _ _ _ _ _ _ _ (bp-payty refl refl ¬B) _ =
  noSpine (λ { (sp-bit _ q _ _ _) → ¬B q })
closeBit _ _ _ _ _ _ _ _ _ _ _ _ _ (bp-miss refl refl refl pg) _ =
  walk-no (λ { (sp-bit _ _ p _ _) _ _ → just≢nothing (trans (sym p) pg) })
closeBit _ _ _ _ _ _ _ _ _ _ _ _ _ (bp-bad refl refl refl _ _ nv) _ =
  walk-no (λ { (sp-bit _ _ _ vok _) _ _ → nv vok })
closeBit Γ ρ f R arms acc _ _ _ _ _ _ _ (bp-yes refl refl refl g pg vok) k
    with k g
... | walk-no n = walk-no (λ where
      (sp-bit {gs = gs} _ _ pg′ _ spin) q c →
        n spin (unshiftRead acc g gs
          (subst (λ h → pickRead (acc ++ (h ∷ gs)) f R arms ≡ just _)
            (just-inj (trans (sym pg′) pg)) q)) c)
... | walk-yes {gs = gs} spin pk d =
    walk-yes (sp-bit refl refl pg vok spin) (shiftRead acc g gs pk) d

-- The wide put is decided on the same process and protocol the
-- clause received. Rebuilding `put` or `dsend` is a new term, so
-- these casts only rename that term along a proof.
castAns : ∀ {Γ ρ proc proto A y B S} {v : ValExpr A} {P : Proc} →
    proc ≡ put A v P → proto ≡ dsend y B S →
    Answerρ Γ ρ (put A v P) (dsend y B S) →
    Answerρ Γ ρ proc proto
castAns refl refl a = a

castWalk : ∀ {Γ ρ f R arms acc ts proto proc S A} {v : ValExpr A} {P : Proc} →
    proc ≡ put A v P → proto ≡ S →
    Walk Γ ρ f R arms acc ts proto proc →
    Walk Γ ρ f R arms acc ts S (put A v P)
castWalk refl refl w = w

splitCast : ∀ {y B f tags R arms proto} →
    proto ≡ dsend y B (pcase (bySplit f tags R) arms) →
    splitAt proto ≡ just (f , tags , R , arms)
splitCast refl = refl

moveSplit : ∀ {proto S f tags R arms} →
    proto ≡ S →
    splitAt S ≡ just (f , tags , R , arms) →
    splitAt proto ≡ just (f , tags , R , arms)
moveSplit refl sp = sp

-- The split of a plain continuation, computed outside the decider.
-- Matching it there keeps the `with` away from the walk.
data PlainView (S : Proto) : Set where
  pv-none : splitAt S ≡ nothing → PlainView S
  pv-seal : (f : String) (tags : List Tag) (R : Ty) (arms : List (String × Proto)) →
      splitAt S ≡ just (f , tags , R , arms) →
      wtag tags ≡ nothing →
      PlainView S
  pv-wide : (f : String) (tags : List Tag) (R : Ty) (arms : List (String × Proto)) →
      (w : WTag tags) →
      splitAt S ≡ just (f , tags , R , arms) →
      PlainView S

data Inspect {A : Set} (x : A) : Set where
  _with≡_ : (y : A) → x ≡ y → Inspect x

inspect : ∀ {A : Set} (x : A) → Inspect x
inspect x = x with≡ refl

underD : ∀ {y B S} → PlainView S → PlainView (dsend y B S)
underD (pv-none p) = pv-none p
underD (pv-seal f tags R arms sp wt) = pv-seal f tags R arms sp wt
underD (pv-wide f tags R arms w sp) = pv-wide f tags R arms w sp

underE : ∀ {y n S} → PlainView S → PlainView (esend y (nlit n) S)
underE (pv-none p) = pv-none p
underE (pv-seal f tags R arms sp wt) = pv-seal f tags R arms sp wt
underE (pv-wide f tags R arms w sp) = pv-wide f tags R arms w sp

onTag : (f : String) (tags : List Tag) (R : Ty) (arms : List (String × Proto)) →
    Inspect (wtag tags) → PlainView (pcase (bySplit f tags R) arms)
onTag f tags R arms (nothing with≡ wt) = pv-seal f tags R arms refl wt
onTag f tags R arms (just w with≡ _) = pv-wide f tags R arms w refl

opaque
  plainView : (S : Proto) → PlainView S
  plainView end = pv-none refl
  plainView (send _ _) = pv-none refl
  plainView (recv _ _) = pv-none refl
  plainView (dsend y B S) = underD (plainView S)
  plainView (drecv _ _ _) = pv-none refl
  plainView (esend y (nlit n) S) = underE (plainView S)
  plainView (esend y (nvar _) _) = pv-none refl
  plainView (erecv _ _ _) = pv-none refl
  plainView (isend _ _ _) = pv-none refl
  plainView (irecv _ _ _) = pv-none refl
  plainView (choose _ _) = pv-none refl
  plainView (branch _ _) = pv-none refl
  plainView (pcase (byVal _) _) = pv-none refl
  plainView (pcase (byRun _ _ _) _) = pv-none refl
  plainView (pcase (bySplit f tags R) arms) = onTag f tags R arms (inspect (wtag tags))

mutual
  decideArms : (Γ : Ctx) (ρ : Idx) (A : Ty) (i : ℕ) (ps : List PArm) (S : Proto) →
    AnswerArms Γ ρ A i ps S
  decideArms Γ ρ A i [] _ = yes-arms arms-nil
  decideArms Γ ρ A i (bare p ∷ ps) S with decideρ Γ ρ p S
  ... | no nd = no-arms (λ { (arms-cons d _) → nd d })
  ... | yes d with decideArms Γ ρ A (nsuc i) ps S
  ... | yes-arms ds = yes-arms (arms-cons d ds)
  ... | no-arms nd = no-arms (λ { (arms-cons _ ds) → nd ds })
  decideArms Γ ρ A i (named c xs p ∷ ps) S with openArmCtx A i c xs Γ in eq
  ... | nothing = no-arms (λ { (arms-named q _ _) → just≢nothing (trans (sym q) eq) })
  ... | just Δ with decideρ Δ ρ p S
  ... | no nd = no-arms (λ { (arms-named q d _) →
        nd (subst (λ Θ → Conformsρ Θ ρ p S) (just-inj (trans (sym q) eq)) d) })
  ... | yes d with decideArms Γ ρ A (nsuc i) ps S
  ... | yes-arms ds = yes-arms (arms-named eq d ds)
  ... | no-arms nd = no-arms (λ { (arms-named _ _ ds) → nd ds })
  decideArms Γ ρ A i (prod pat p ∷ ps) S with prodCtx A pat Γ in eq
  ... | nothing = no-arms (λ { (arms-prod q _ _) → just≢nothing (trans (sym q) eq) })
  ... | just Δ with decideρ Δ ρ p S
  ... | no nd = no-arms (λ { (arms-prod q d _) →
        nd (subst (λ Θ → Conformsρ Θ ρ p S) (just-inj (trans (sym q) eq)) d) })
  ... | yes d with decideArms Γ ρ A (nsuc i) ps S
  ... | yes-arms ds = yes-arms (arms-prod eq d ds)
  ... | no-arms nd = no-arms (λ { (arms-prod _ _ ds) → nd ds })
  decideArms _ _ _ _ (fork _ _ _ _ ∷ _) _ = no-arms (λ ())

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
  decideρ Γ ρ done (pcase _ _) = no (λ ())
  decideρ Γ ρ stop _ = yes abandon
  decideρ Γ ρ (put A v P) (send B S) = on-put (ty≟ A (applyTy ρ B)) (decideValExpr Γ v) (decideρ Γ ρ P S)
  decideρ Γ ρ (put A v P) (dsend y B S) =
    sendBy Γ ρ y v P B S (put A v P) (dsend y B S) refl refl
  decideρ Γ ρ (put A v P) (esend y e S) with ty≟ A nat
  ... | no′ ¬eq = no (λ where
        (eput-ok _ _ _) → ¬eq refl
        (eput-wide _ _ _ _ _ _ _ _ _) → ¬eq refl)
  ... | yes′ refl with e
  ... | nvar x =
      on-eput refl (decideValExpr Γ v) (owed? Γ v (lookupIdx ρ x))
        (decideSend Γ ρ v (nvar x) P S)
  ... | nlit n with splitAt (esend y (nlit n) S) in sp
  ... | nothing =
      on-eput sp (decideValExpr Γ v) (owed? Γ v (just (nlit n)))
        (decideSend Γ ρ v (nlit n) P S)
  ... | just (f , tags , R , arms) with wtag tags in wtq
  ... | nothing =
      exactE wtq sp (decideValExpr Γ v) (owed? Γ v (just (nlit n)))
        (decideSend Γ ρ v (nlit n) P S)
  ... | just wt = putWideE Γ ρ y n v P S f tags R arms wt sp
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
  decideρ Γ ρ (put _ _ _) (pcase _ _) = no (λ ())
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
  decideρ Γ ρ (get _ _ _) (pcase _ _) = no (λ ())
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
  decideρ Γ ρ (iget _ _ _) (pcase _ _) = no (λ ())
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
  decideρ Γ ρ (pick0 _) (pcase _ _) = no (λ ())
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
  decideρ Γ ρ (pick1 _) (pcase _ _) = no (λ ())
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
  decideρ Γ ρ (cover _ _) (pcase _ _) = no (λ ())
  decideρ Γ ρ (mget A x ps) S = matchAnswer Γ ρ A x ps S

  decideAt : (Γ : Ctx) (ρ : Idx) (A : Ty) (arms : List (String × Proto)) (ps : List PArm) →
    AnswerAt Γ ρ A arms ps
  decideAt Γ ρ A [] [] = yes-at at-nil
  decideAt Γ ρ A ((c , S) ∷ as) (bare p ∷ ps) with decideρ Γ ρ p S
  ... | no nd = no-at (λ { (at-cons d _) → nd d })
  ... | yes d with decideAt Γ ρ A as ps
  ... | yes-at ds = yes-at (at-cons {c = c} d ds)
  ... | no-at nd = no-at (λ { (at-cons _ ds) → nd ds })
  decideAt Γ ρ A ((c , S) ∷ as) (named k xs p ∷ ps) with c ≟ k
  ... | no′ c≢k = no-at (λ { (at-named _ _ _) → c≢k refl })
  ... | yes′ refl with armCtxNamed A c xs Γ in ac
  ... | nothing = no-at (λ { (at-named q _ _) → just≢nothing (trans (sym q) ac) })
  ... | just Δ with decideρ Δ ρ p S
  ... | no nd = no-at (λ { (at-named q d _) →
        nd (subst (λ Θ → Conformsρ Θ ρ p S) (just-inj (trans (sym q) ac)) d) })
  ... | yes d with decideAt Γ ρ A as ps
  ... | yes-at ds = yes-at (at-named ac d ds)
  ... | no-at nd = no-at (λ { (at-named _ _ ds) → nd ds })
  decideAt Γ ρ A (_ ∷ _) (prod _ _ ∷ _) = no-at (λ ())
  decideAt Γ ρ A (_ ∷ _) (fork _ _ _ _ ∷ _) = no-at (λ ())
  decideAt Γ ρ A [] (_ ∷ _) = no-at (λ ())
  decideAt Γ ρ A (_ ∷ _) [] = no-at (λ ())

  decideFork : (Γ : Ctx) (ρ : Idx) (B : Ty) (par : List Slot) (pxs : List String)
    (ch : List (String × Split)) (qs : List PArm) → AnswerFork Γ ρ B par pxs ch qs
  decideFork _ _ _ _ _ [] [] = yes-fk fork-nil
  decideFork _ _ _ _ _ [] (_ ∷ _) = no-fk (λ ())
  decideFork _ _ _ _ _ (_ ∷ _) [] = no-fk (λ ())
  decideFork Γ ρ B par pxs ((c , flat S) ∷ ch) (bare p ∷ ps) with decideρ Γ ρ p S
  ... | no nd = no-fk (λ { (fork-bare d _) → nd d })
  ... | yes d with decideFork Γ ρ B par pxs ch ps
  ... | yes-fk ds = yes-fk (fork-bare d ds)
  ... | no-fk nd = no-fk (λ { (fork-bare _ ds) → nd ds })
  decideFork Γ ρ B par pxs ((c , flat S) ∷ ch) (named k xs p ∷ ps) with c ≟ k
  ... | no′ c≢k = no-fk (λ { (fork-named _ _ _) → c≢k refl })
  ... | yes′ refl with armCtxNamed B c xs Γ in ac
  ... | nothing = no-fk (λ { (fork-named q _ _) → just≢nothing (trans (sym q) ac) })
  ... | just Δ with decideρ Δ ρ p S
  ... | no nd = no-fk (λ { (fork-named q d _) →
        nd (subst (λ Θ → Conformsρ Θ ρ p S) (just-inj (trans (sym q) ac)) d) })
  ... | yes d with decideFork Γ ρ B par pxs ch ps
  ... | yes-fk ds = yes-fk (fork-named ac d ds)
  ... | no-fk nd = no-fk (λ { (fork-named _ _ ds) → nd ds })
  decideFork Γ ρ B par pxs ((c , node i ch2) ∷ ch) (fork k xs y qs ∷ ps) with c ≟ k
  ... | no′ c≢k = no-fk (λ where
        (fork-nest _ _ _ _ _ _) → c≢k refl
        (fork-sib _ _ _ _ _ _ _) → c≢k refl)
  ... | yes′ refl = nestFork Γ ρ B par pxs c i ch2 ch xs y qs ps
  decideFork _ _ _ _ _ (( _ , flat _) ∷ _) (fork _ _ _ _ ∷ _) = no-fk (λ ())
  decideFork _ _ _ _ _ (( _ , node _ _) ∷ _) (bare _ ∷ _) = no-fk (λ ())
  decideFork _ _ _ _ _ (( _ , node _ _) ∷ _) (named _ _ _ ∷ _) = no-fk (λ ())
  decideFork _ _ _ _ _ (_ ∷ _) (prod _ _ ∷ _) = no-fk (λ ())

  -- A nested field of the constructor just opened, or a sibling field
  -- of the constructor that owns this split.
  nestFork : (Γ : Ctx) (ρ : Idx) (B : Ty) (par : List Slot) (pxs : List String)
    (c : String) (i : ℕ) (ch2 : List (String × Split)) (ch : List (String × Split))
    (xs : List String) (y : String) (qs ps : List PArm) →
    AnswerFork Γ ρ B par pxs ((c , node i ch2) ∷ ch) (fork c xs y qs ∷ ps)
  nestFork Γ ρ B par pxs c i ch2 ch xs y qs ps with nestView B c xs i y Γ
  ... | nv-no ¬n = sibFork Γ ρ B par pxs c i ch2 ch xs y qs ps ¬n
  ... | nv-yes {Δ} {C} ac ni tb sp =
      nestYes Γ ρ B par pxs c i ch2 ch xs y qs ps ac ni tb sp

  nestYes : (Γ : Ctx) (ρ : Idx) (B : Ty) (par : List Slot) (pxs : List String)
    (c : String) (i : ℕ) (ch2 : List (String × Split)) (ch : List (String × Split))
    (xs : List String) (y : String) (qs ps : List PArm) →
    ∀ {Δ C} →
    armCtxNamed B c xs Γ ≡ just Δ →
    nth xs i ≡ just y →
    tyAt B c i ≡ just C →
    splittable C ≡ true →
    AnswerFork Γ ρ B par pxs ((c , node i ch2) ∷ ch) (fork c xs y qs ∷ ps)
  nestYes Γ ρ B par pxs c i ch2 ch xs y qs ps {Δ} {C} ac ni tb sp
    with decideFork Δ ρ C (orEmpty (slotsNamed B c)) xs ch2 qs
  ... | no-fk nd = no-fk (λ where
        (fork-nest {Δ = Δ′} {C = C′} ctx _ tq _ fk _) →
          nd (castFork (just-inj (trans (sym ctx) ac)) (just-inj (trans (sym tq) tb)) refl fk)
        (fork-sib ¬n _ _ _ _ _ _) → ¬n (nest-ok ac ni tb sp))
  ... | yes-fk fk with decideFork Γ ρ B par pxs ch ps
  ... | yes-fk ds = yes-fk (fork-nest ac ni tb sp fk ds)
  ... | no-fk nd = no-fk (λ where
        (fork-nest _ _ _ _ _ ds) → nd ds
        (fork-sib _ _ _ _ _ _ ds) → nd ds)

  -- The index is a sibling on the parent. The constructor just opened
  -- does not bind a splittable field there.
  sibFork : (Γ : Ctx) (ρ : Idx) (B : Ty) (par : List Slot) (pxs : List String)
    (c : String) (i : ℕ) (ch2 : List (String × Split)) (ch : List (String × Split))
    (xs : List String) (y : String) (qs ps : List PArm) →
    ¬ NestOk B c xs i y Γ →
    AnswerFork Γ ρ B par pxs ((c , node i ch2) ∷ ch) (fork c xs y qs ∷ ps)
  sibFork Γ ρ B par pxs c i ch2 ch xs y qs ps ¬n with nth pxs i in px
  ... | nothing = no-fk (λ where
        (fork-nest ac ni tb sp _ _) → ¬n (nest-ok ac ni tb sp)
        (fork-sib _ q _ _ _ _ _) → just≢nothing (trans (sym q) px))
  ... | just z = sibHave Γ ρ B par pxs c i ch2 ch xs y qs ps ¬n z px

  sibHave : (Γ : Ctx) (ρ : Idx) (B : Ty) (par : List Slot) (pxs : List String)
    (c : String) (i : ℕ) (ch2 ch : List (String × Split))
    (xs : List String) (y : String) (qs ps : List PArm) →
    ¬ NestOk B c xs i y Γ → (z : String) → nth pxs i ≡ just z →
    AnswerFork Γ ρ B par pxs ((c , node i ch2) ∷ ch) (fork c xs y qs ∷ ps)
  sibHave Γ ρ B par pxs c i ch2 ch xs y qs ps ¬n z px with z ≟ y
  ... | no′ z≢y = no-fk (λ where
        (fork-nest ac ni tb sp _ _) → ¬n (nest-ok ac ni tb sp)
        (fork-sib _ q _ _ _ _ _) → z≢y (just-inj (trans (sym px) q)))
  ... | yes′ refl = sibSlot Γ ρ B par pxs c i ch2 ch xs y qs ps ¬n px

  sibSlot : (Γ : Ctx) (ρ : Idx) (B : Ty) (par : List Slot) (pxs : List String)
    (c : String) (i : ℕ) (ch2 ch : List (String × Split))
    (xs : List String) (y : String) (qs ps : List PArm) →
    ¬ NestOk B c xs i y Γ → nth pxs i ≡ just y →
    AnswerFork Γ ρ B par pxs ((c , node i ch2) ∷ ch) (fork c xs y qs ∷ ps)
  sibSlot Γ ρ B par pxs c i ch2 ch xs y qs ps ¬n px with nth par i in sb
  ... | nothing = no-fk (λ where
        (fork-nest ac ni tb sp _ _) → ¬n (nest-ok ac ni tb sp)
        (fork-sib _ _ q _ _ _ _) → just≢nothing (trans (sym q) sb))
  ... | just s = sibOpen Γ ρ B par pxs c i ch2 ch xs y qs ps ¬n px s sb

  sibOpen : (Γ : Ctx) (ρ : Idx) (B : Ty) (par : List Slot) (pxs : List String)
    (c : String) (i : ℕ) (ch2 ch : List (String × Split))
    (xs : List String) (y : String) (qs ps : List PArm) →
    ¬ NestOk B c xs i y Γ → nth pxs i ≡ just y →
    (s : Slot) → nth par i ≡ just s →
    AnswerFork Γ ρ B par pxs ((c , node i ch2) ∷ ch) (fork c xs y qs ∷ ps)
  sibOpen Γ ρ B par pxs c i ch2 ch xs y qs ps ¬n px s sb with splittableS s in ssp
  ... | false = no-fk (λ where
        (fork-nest ac ni tb sp _ _) → ¬n (nest-ok ac ni tb sp)
        (fork-sib _ _ eq p _ _ _) →
          true≢false (trans (sym p)
            (subst (λ t → splittableS t ≡ false) (just-inj (trans (sym sb) eq)) ssp)))
  ... | true = sibTy Γ ρ B par pxs c i ch2 ch xs y qs ps ¬n px s sb ssp

  sibTy : (Γ : Ctx) (ρ : Idx) (B : Ty) (par : List Slot) (pxs : List String)
    (c : String) (i : ℕ) (ch2 ch : List (String × Split))
    (xs : List String) (y : String) (qs ps : List PArm) →
    ¬ NestOk B c xs i y Γ → nth pxs i ≡ just y →
    (s : Slot) → nth par i ≡ just s → splittableS s ≡ true →
    AnswerFork Γ ρ B par pxs ((c , node i ch2) ∷ ch) (fork c xs y qs ∷ ps)
  sibTy Γ ρ B par pxs c i ch2 ch xs y qs ps ¬n px s sb ssp with slotTy s in st
  ... | nothing = no-fk (λ where
        (fork-nest ac ni tb sp _ _) → ¬n (nest-ok ac ni tb sp)
        (fork-sib {s = s′} {C = C′} _ _ eq _ q _ _) →
          just≢nothing (trans
            (sym (subst (λ t → slotTy t ≡ just C′) (just-inj (trans (sym eq) sb)) q))
            st))
  ... | just C = sibRec Γ ρ B par pxs c i ch2 ch xs y qs ps ¬n px s sb ssp st

  sibRec : (Γ : Ctx) (ρ : Idx) (B : Ty) (par : List Slot) (pxs : List String)
    (c : String) (i : ℕ) (ch2 ch : List (String × Split))
    (xs : List String) (y : String) (qs ps : List PArm) →
    ¬ NestOk B c xs i y Γ → nth pxs i ≡ just y →
    (s : Slot) → nth par i ≡ just s → splittableS s ≡ true →
    ∀ {C} → slotTy s ≡ just C →
    AnswerFork Γ ρ B par pxs ((c , node i ch2) ∷ ch) (fork c xs y qs ∷ ps)
  sibRec Γ ρ B par pxs c i ch2 ch xs y qs ps ¬n px s sb ssp {C} st
    with decideFork Γ ρ C par pxs ch2 qs
  ... | no-fk nd = no-fk (λ where
        (fork-nest ac ni tb sp _ _) → ¬n (nest-ok ac ni tb sp)
        (fork-sib {s = s′} {C = C′} _ _ eq _ q fk _) →
          nd (castFork refl
               (just-inj (trans
                 (sym (subst (λ t → slotTy t ≡ just C′)
                        (just-inj (trans (sym eq) sb)) q))
                 st))
               refl fk))
  ... | yes-fk fk with decideFork Γ ρ B par pxs ch ps
  ... | yes-fk ds = yes-fk (fork-sib ¬n px sb ssp st fk ds)
  ... | no-fk nd = no-fk (λ where
        (fork-nest ac ni tb sp _ ds) → ¬n (nest-ok ac ni tb sp)
        (fork-sib _ _ _ _ _ _ ds) → nd ds)

  decideRun : (Γ : Ctx) (ρ : Idx) (f : String) (A R : Ty) (arms : List (String × Proto))
    (cs : List String) (ps : List PArm) → AnswerRun Γ ρ f A R arms cs ps
  decideRun _ _ _ _ _ _ [] [] = yes-cr run-nil
  decideRun Γ ρ f A R arms (c ∷ cs) (bare p ∷ ps) with splitOf f A c R arms in sp
  ... | nothing = no-cr (λ { (run-cons q _ _) → just≢nothing (trans (sym q) sp) })
  ... | just (node _ _) = no-cr (λ { (run-cons q _ _) → flat≢node (just-inj (trans (sym q) sp)) })
  ... | just (flat S) with decideρ Γ ρ p S
  ... | no nd = no-cr (λ { (run-cons q d _) →
        nd (subst (λ T → Conformsρ Γ ρ p T) (flat-inj (just-inj (trans (sym q) sp))) d) })
  ... | yes d with decideRun Γ ρ f A R arms cs ps
  ... | yes-cr ds = yes-cr (run-cons sp d ds)
  ... | no-cr nd = no-cr (λ { (run-cons _ _ ds) → nd ds })
  decideRun Γ ρ f A R arms (c ∷ cs) (named k xs p ∷ ps) with c ≟ k
  ... | no′ c≢k = no-cr (λ { (run-named _ _ _ _) → c≢k refl })
  ... | yes′ refl with splitOf f A c R arms in sp
  ... | nothing = no-cr (λ { (run-named q _ _ _) → just≢nothing (trans (sym q) sp) })
  ... | just (node _ _) = no-cr (λ { (run-named q _ _ _) → flat≢node (just-inj (trans (sym q) sp)) })
  ... | just (flat S) with armCtxNamed A c xs Γ in ac
  ... | nothing = no-cr (λ { (run-named _ q _ _) → just≢nothing (trans (sym q) ac) })
  ... | just Δ with decideρ Δ ρ p S
  ... | no nd = no-cr (λ { (run-named {Δ = Δ′} q ctx d _) →
        nd (subst (λ Θ → Conformsρ Θ ρ p S) (just-inj (trans (sym ctx) ac))
          (subst (λ T → Conformsρ Δ′ ρ p T) (flat-inj (just-inj (trans (sym q) sp))) d)) })
  ... | yes d with decideRun Γ ρ f A R arms cs ps
  ... | yes-cr ds = yes-cr (run-named sp ac d ds)
  ... | no-cr nd = no-cr (λ { (run-named _ _ _ ds) → nd ds })
  decideRun Γ ρ f A R arms (c ∷ cs) (fork k xs y qs ∷ ps) with c ≟ k
  ... | no′ c≢k = no-cr (λ { (run-fork _ _ _ _ _ _ _) → c≢k refl })
  ... | yes′ refl with splitOf f A c R arms in sp
  ... | nothing = no-cr (λ { (run-fork q _ _ _ _ _ _) → just≢nothing (trans (sym q) sp) })
  ... | just (flat _) = no-cr (λ { (run-fork q _ _ _ _ _ _) → node≢flat (just-inj (trans (sym q) sp)) })
  ... | just (node i ch) with armCtxNamed A c xs Γ in ac
  ... | nothing = no-cr (λ { (run-fork _ q _ _ _ _ _) → just≢nothing (trans (sym q) ac) })
  ... | just Δ with hitName xs i y
  ... | no′ ¬hit = no-cr (λ { (run-fork {i = i′} q _ p _ _ _ _) →
        ¬hit (subst (λ n → nth xs n ≡ just y) (nodeIdx (just-inj (trans (sym q) sp))) p) })
  ... | yes′ ni with tyAt A c i in tb
  ... | nothing = no-cr (λ { (run-fork {i = i′} {B = B′} q _ _ p _ _ _) →
        just≢nothing (trans (sym (subst (λ n → tyAt A c n ≡ just B′)
                                    (nodeIdx (just-inj (trans (sym q) sp))) p)) tb) })
  ... | just B with slotsNamed A c in sl
  ... | nothing = no-cr (λ { (run-fork _ _ _ _ p _ _) → just≢nothing (trans (sym p) sl) })
  ... | just par with decideFork Δ ρ B par xs ch qs
  ... | no-fk nd = no-cr (λ { (run-fork {Δ = Δ′} {ch = ch′} {B = B′} {par = par′} q ctx _ tq sq fk _) →
        nd (castFork (just-inj (trans (sym ctx) ac))
             (just-inj (trans (sym (subst (λ n → tyAt A c n ≡ just B′)
                                      (nodeIdx (just-inj (trans (sym q) sp))) tq)) tb))
             (chOf (just-inj (trans (sym q) sp)))
             (subst (λ r → ForkArms Δ′ ρ B′ r xs ch′ qs)
                (just-inj (trans (sym sq) sl)) fk)) })
  ... | yes-fk fk with decideRun Γ ρ f A R arms cs ps
  ... | yes-cr ds = yes-cr (run-fork sp ac ni tb sl fk ds)
  ... | no-cr nd = no-cr (λ { (run-fork _ _ _ _ _ _ ds) → nd ds })
  decideRun _ _ _ _ _ _ (_ ∷ _) (prod _ _ ∷ _) = no-cr (λ ())
  decideRun _ _ _ _ _ _ [] (_ ∷ _) = no-cr (λ ())
  decideRun _ _ _ _ _ _ (_ ∷ _) [] = no-cr (λ ())

  finishVal : ∀ {Γ ρ x y w ps arms} →
    namesEq (natArms w) (armNames arms) ≡ true →
    AnswerAt ((x , nat) ∷ Γ) ρ nat arms ps →
    Answerρ Γ ρ (mget nat x ps) (erecv y (nlit w) (pcase (byVal y) arms))
  finishVal eq (yes-at ds) = yes (eget-val eq ds)
  finishVal _ (no-at nd) = no (λ { (eget-val _ ds) → nd ds })

  finishRun : ∀ {Γ ρ x y w f R ps arms rows} →
    readyN (nsuc nzero) f ≡ true →
    labelled R arms ≡ true →
    natRows f R arms w ≡ just rows →
    AnswerCov ((x , nat) ∷ Γ) ρ rows ps →
    Answerρ Γ ρ (mget nat x ps) (erecv y (nlit w) (pcase (byRun f y R) arms))
  finishRun rd lb eq (yes-cov c) = yes (eget-run rd lb eq c)
  finishRun {Γ} {ρ} {x} {ps = ps} rd lb eq (no-cov nc) =
    no (λ { (eget-run _ _ p c) →
      nc (subst (λ rs → CovNat ((x , nat) ∷ Γ) ρ rs ps) (just-inj (trans (sym p) eq)) c) })

  decideCov : (Γ : Ctx) (ρ : Idx) (rows : List (String × Proto)) (ps : List PArm) →
    AnswerCov Γ ρ rows ps
  decideCov Γ ρ [] [] = yes-cov cn-nil
  decideCov _ _ [] (_ ∷ _) = no-cov (λ ())
  decideCov _ _ (_ ∷ _) [] = no-cov (λ ())
  decideCov Γ ρ ((c , S) ∷ rows) (bare p ∷ ps) with decideρ Γ ρ p S
  ... | no nd = no-cov (λ { (cn-bare d _) → nd d })
  ... | yes d with decideCov Γ ρ rows ps
  ... | yes-cov ds = yes-cov (cn-bare d ds)
  ... | no-cov nd = no-cov (λ { (cn-bare _ ds) → nd ds })
  decideCov Γ ρ ((c , S) ∷ rows) (named k [] p ∷ ps) with c ≟ k
  ... | no′ c≢k = no-cov (λ { (cn-named _ _) → c≢k refl })
  ... | yes′ refl with decideρ Γ ρ p S
  ... | no nd = no-cov (λ { (cn-named d _) → nd d })
  ... | yes d with decideCov Γ ρ rows ps
  ... | yes-cov ds = yes-cov (cn-named d ds)
  ... | no-cov nd = no-cov (λ { (cn-named _ ds) → nd ds })
  decideCov _ _ (_ ∷ _) (named _ (_ ∷ _) _ ∷ _) = no-cov (λ ())
  decideCov _ _ (_ ∷ _) (prod _ _ ∷ _) = no-cov (λ ())
  decideCov _ _ (_ ∷ _) (fork _ _ _ _ ∷ _) = no-cov (λ ())

  mgetName : ∀ {A B x y ps qs} → mget A x ps ≡ mget B y qs → x ≡ y
  mgetName refl = refl

  mgetTy : ∀ {A B x y ps qs} → mget A x ps ≡ mget B y qs → A ≡ B
  mgetTy refl = refl

  -- The arm is a match on this bounded nat, or it is not.
  data NatMatch (x : String) : Proc → Set where
    is-here : ∀ {qs} → NatMatch x (mget nat x qs)
    is-away : ∀ {P} → (∀ {qs} → P ≢ mget nat x qs) → NatMatch x P

  natMatch : (x : String) (P : Proc) → NatMatch x P
  natMatch _ done = is-away (λ ())
  natMatch _ stop = is-away (λ ())
  natMatch _ (put _ _ _) = is-away (λ ())
  natMatch _ (get _ _ _) = is-away (λ ())
  natMatch _ (pick0 _) = is-away (λ ())
  natMatch _ (pick1 _) = is-away (λ ())
  natMatch _ (cover _ _) = is-away (λ ())
  natMatch _ (iget _ _ _) = is-away (λ ())
  natMatch x (mget A y qs) with ty≟ A nat
  ... | no′ ¬nat = is-away (λ eq → ¬nat (mgetTy eq))
  ... | yes′ refl with x ≟ y
  ... | no′ y≢x = is-away (λ eq → y≢x (mgetName (sym eq)))
  ... | yes′ refl = is-here

  finishOne : (Γ : Ctx) (ρ : Idx) (x : String) (rows : List (String × Proto))
      (p : Proc) → (∀ {qs} → p ≢ mget nat x qs) →
      (m : Maybe Proto) → sameArms rows ≡ m → AnswerCell Γ ρ x rows p
  finishOne Γ ρ x rows p away nothing sa = no-cell (λ where
    (cell-one q _) → just≢nothing (trans (sym q) sa)
    (cell-nat _) → away refl)
  finishOne Γ ρ x rows p away (just S) sa = useOne away sa (decideρ Γ ρ p S)

  finishCol : (Γ : Ctx) (ρ : Idx) (x : String) (rows : List (String × Proto))
      (p : Proc) (qs : List PArm) → p ≡ mget nat x qs →
      AnswerCov Γ ρ rows qs → (m : Maybe Proto) → sameArms rows ≡ m →
      AnswerCell Γ ρ x rows p
  finishCol _ _ _ _ _ _ refl (yes-cov cov) _ _ = yes-cell (cell-nat cov)
  finishCol _ _ _ _ _ _ refl (no-cov nc) nothing sa = no-cell (λ where
    (cell-nat cov) → nc cov
    (cell-one q _) → just≢nothing (trans (sym q) sa))
  finishCol Γ ρ x rows p qs refl (no-cov nc) (just S) sa =
    useAns nc sa refl (decideρ Γ ρ p S)

  colOne : (Γ : Ctx) (ρ : Idx) (x : String) (rows : List (String × Proto))
      (p : Proc) → (∀ {qs} → p ≢ mget nat x qs) → AnswerCell Γ ρ x rows p
  colOne Γ ρ x rows p away = finishOne Γ ρ x rows p away (sameArms rows) refl

  colNat : (Γ : Ctx) (ρ : Idx) (x : String) (rows : List (String × Proto))
      (p : Proc) (qs : List PArm) → p ≡ mget nat x qs → AnswerCell Γ ρ x rows p
  colNat Γ ρ x rows p qs eq =
    finishCol Γ ρ x rows p qs eq (decideCov Γ ρ rows qs) (sameArms rows) refl

  pickCell : (Γ : Ctx) (ρ : Idx) (x : String) (rows : List (String × Proto))
      (p : Proc) → NatMatch x p → AnswerCell Γ ρ x rows p
  pickCell Γ ρ x rows p (is-away away) = colOne Γ ρ x rows p away
  pickCell Γ ρ x rows .(mget nat x qs) (is-here {qs = qs}) =
    colNat Γ ρ x rows (mget nat x qs) qs refl

  useBare : ∀ {Γ ρ A x w c cs rows grid p ps} →
    AnswerCell Γ ρ x rows p →
    AnswerProd Γ ρ A x w cs grid ps →
    AnswerProd Γ ρ A x w (c ∷ cs) (rows ∷ grid) (bare p ∷ ps)
  useBare (no-cell nc) _ = no-pc (λ { (pc-bare cl _) → nc cl })
  useBare (yes-cell cl) (yes-pc rest) = yes-pc (pc-bare cl rest)
  useBare (yes-cell _) (no-pc nr) = no-pc (λ { (pc-bare _ rest) → nr rest })

  useNamed : ∀ {Γ ρ A x w c cs rows grid xs p Δ ps} →
    armCtxNamed A c xs Γ ≡ just Δ →
    AnswerCell Δ ρ x rows p →
    AnswerProd Γ ρ A x w cs grid ps →
    AnswerProd Γ ρ A x w (c ∷ cs) (rows ∷ grid) (named c xs p ∷ ps)
  useNamed {ρ = ρ} {x = x} {rows = rows} {p = p} ac (no-cell nc) _ =
    no-pc (λ { (pc-named q cl _) →
      nc (subst (λ Θ → Cell Θ ρ x rows p) (just-inj (trans (sym q) ac)) cl) })
  useNamed ac (yes-cell cl) (yes-pc rest) = yes-pc (pc-named ac cl rest)
  useNamed _ (yes-cell _) (no-pc nr) = no-pc (λ { (pc-named _ _ rest) → nr rest })

  decideProd : (Γ : Ctx) (ρ : Idx) (A : Ty) (x : String) (w : ℕ)
    (cs : List String) (grid : List (List (String × Proto))) (ps : List PArm) →
    AnswerProd Γ ρ A x w cs grid ps
  decideProd _ _ _ _ _ [] [] [] = yes-pc pc-nil
  decideProd _ _ _ _ _ [] (_ ∷ _) _ = no-pc (λ ())
  decideProd _ _ _ _ _ [] [] (_ ∷ _) = no-pc (λ ())
  decideProd _ _ _ _ _ (_ ∷ _) [] _ = no-pc (λ ())
  decideProd _ _ _ _ _ (_ ∷ _) (_ ∷ _) [] = no-pc (λ ())
  decideProd Γ ρ A x w (c ∷ cs) (rows ∷ grid) (bare p ∷ ps) =
    useBare (pickCell Γ ρ x rows p (natMatch x p)) (decideProd Γ ρ A x w cs grid ps)
  decideProd Γ ρ A x w (c ∷ cs) (rows ∷ grid) (named k xs p ∷ ps) with nameView A c k xs Γ
  ... | nv-neq neq = no-pc (λ { (pc-named _ _ _) → neq refl })
  ... | nv-none ac refl = no-pc (λ { (pc-named q _ _) → just≢nothing (trans (sym q) ac) })
  ... | nv-just Δ ac refl =
      useNamed ac (pickCell Δ ρ x rows p (natMatch x p)) (decideProd Γ ρ A x w cs grid ps)
  decideProd _ _ _ _ _ (_ ∷ _) (_ ∷ _) (prod _ _ ∷ _) = no-pc (λ ())
  decideProd _ _ _ _ _ (_ ∷ _) (_ ∷ _) (fork _ _ _ _ ∷ _) = no-pc (λ ())

  finishProd : ∀ {Γ ρ A B x y d w f R ps arms cs grid} →
    A ≡ applyTy ρ B →
    payCtors A ≡ just cs →
    readyN (nsuc (nsuc nzero)) f ≡ true →
    labelled R arms ≡ true →
    prodGrid w A f R arms ≡ just grid →
    AnswerProd ((x , A) ∷ Γ) ρ A d w cs grid ps →
    Answerρ Γ ρ (mget A x ps)
      (drecv y B (pcase (bySplit f (tagNat d w ∷ tagDat y cs ∷ []) R) arms))
  finishProd eq ep rd lb pg (yes-pc cov) = yes (mget-prod eq ep rd lb pg cov)
  finishProd {Γ} {ρ} {A} {x = x} {d = d} {w = w} {ps = ps} {cs = cs} eq ep rd lb pg (no-pc np) =
    no (λ where
      (mget-prod _ _ _ _ p cov) →
        np (subst (λ g → ProdCov ((x , A) ∷ Γ) ρ A d w cs g ps)
              (just-inj (trans (sym p) pg)) cov)
      (mget-wide () _ _ _ _ _ _ _ _ _ _))

  finishBit : ∀ {Γ ρ x y d w f R ps arms grid} →
    readyN (nsuc (nsuc nzero)) f ≡ true →
    labelled R arms ≡ true →
    prodGrid w bit f R arms ≡ just grid →
    AnswerProd ((x , bit) ∷ Γ) ρ bit d w ("b0" ∷ "b1" ∷ []) grid ps →
    Answerρ Γ ρ (mget bit x ps)
      (drecv y bit (pcase (bySplit f (tagNat d w ∷ tagBit y ∷ []) R) arms))
  finishBit rd lb pg (yes-pc cov) = yes (mget-pbit rd lb pg cov)
  finishBit {Γ} {ρ} {x} {d = d} {w = w} {ps = ps} rd lb pg (no-pc np) =
    no (λ where
      (mget-pbit _ _ p cov) →
        np (subst (λ g → ProdCov ((x , bit) ∷ Γ) ρ bit d w ("b0" ∷ "b1" ∷ []) g ps)
              (just-inj (trans (sym p) pg)) cov)
      (mget-wide () _ _ _ _ _ _ _ _ _ _))

  decideENat : (Γ : Ctx) (ρ : Idx) (A : Ty) (x : String) (ps : List PArm)
    (y : String) (e : NExp) (S : Proto) →
    Answerρ Γ ρ (mget A x ps) (erecv y e S)
  decideENat Γ ρ A x ps y (nlit w) (pcase (byVal z) arms) with z ≟ y
  ... | no′ z≢y = no (λ { (eget-val _ _) → z≢y refl })
  ... | yes′ refl with ty≟ A nat
  ... | no′ ¬eq = no (λ { (eget-val _ _) → ¬eq refl })
  ... | yes′ refl with namesEq (natArms w) (armNames arms) in ne
  ... | false = no (λ { (eget-val p _) → true≢false (trans (sym p) ne) })
  ... | true = finishVal ne (decideAt ((x , nat) ∷ Γ) ρ nat arms ps)
  decideENat Γ ρ A x ps y (nlit w) (pcase (byRun f z R) arms) with z ≟ y
  ... | no′ z≢y = no (λ { (eget-run _ _ _ _) → z≢y refl })
  ... | yes′ refl with ty≟ A nat
  ... | no′ ¬eq = no (λ { (eget-run _ _ _ _) → ¬eq refl })
  ... | yes′ refl with readyN (nsuc nzero) f in rd
  ... | false = no (λ { (eget-run p _ _ _) → true≢false (trans (sym p) rd) })
  ... | true with labelled R arms in lb
  ... | false = no (λ { (eget-run _ p _ _) → true≢false (trans (sym p) lb) })
  ... | true with natRows f R arms w in nr
  ... | nothing = no (λ { (eget-run _ _ p _) → just≢nothing (trans (sym p) nr) })
  ... | just rows = finishRun rd lb nr (decideCov ((x , nat) ∷ Γ) ρ rows ps)
  decideENat Γ ρ A x ps y (nlit w) (pcase (bySplit f tags R) arms) =
    decideESplit Γ ρ A x ps y w f tags R arms
  decideENat _ _ _ _ _ _ (nlit _) end = no (λ ())
  decideENat _ _ _ _ _ _ (nlit _) (send _ _) = no (λ ())
  decideENat _ _ _ _ _ _ (nlit _) (recv _ _) = no (λ ())
  decideENat _ _ _ _ _ _ (nlit _) (dsend _ _ _) = no (λ ())
  decideENat _ _ _ _ _ _ (nlit _) (drecv _ _ _) = no (λ ())
  decideENat _ _ _ _ _ _ (nlit _) (esend _ _ _) = no (λ ())
  decideENat _ _ _ _ _ _ (nlit _) (erecv _ _ _) = no (λ ())
  decideENat _ _ _ _ _ _ (nlit _) (isend _ _ _) = no (λ ())
  decideENat _ _ _ _ _ _ (nlit _) (irecv _ _ _) = no (λ ())
  decideENat _ _ _ _ _ _ (nlit _) (choose _ _) = no (λ ())
  decideENat _ _ _ _ _ _ (nlit _) (branch _ _) = no (λ ())
  decideENat _ _ _ _ _ _ (nvar _) _ = no (λ ())

  -- A put does not conform to a dependent send whose continuation is a
  -- split that is not a wide product. The case is not a plain protocol,
  -- and `bySplit` selects nothing. A wide tag list is a different rule.
  no-split-put : ∀ {Γ ρ A u Q z B f tags R arms} →
    wtag tags ≡ nothing →
    ¬ Conformsρ Γ ρ (put A u Q) (dsend z B (pcase (bySplit f tags R) arms))
  no-split-put wt (dput-ok _ _ pl _) = plain-not pl
  no-split-put wt (dput-arm _ _ p _) = just≢nothing (sym p)
  no-split-put {z = z} {B = B} {f = f} {tags = tags} {R = R} {arms = arms} wt
      (dput-wide _ w _ p _ _ _ _ _ _) =
    just≢nothing (trans (sym (wtag-just w))
      (subst (λ zs → wtag zs ≡ nothing)
        (splitTags (dsend z B (pcase (bySplit f tags R) arms))
          (caseSplit z B f tags R arms) p) wt))

  prodSend : (Γ : Ctx) (ρ : Idx) (v : ValExpr nat) (w : ℕ)
      (A : Ty) (u : ValExpr A) (Q : Proc) (z : String) (B : Ty)
      (y : String) (n : ℕ) (b : String) (cs : List String)
      (f : String) (R : Ty) (arms : List (String × Proto)) →
      AnswerSend Γ ρ v (put A u Q) (nlit w)
        (dsend z B (pcase (bySplit f (tagNat y n ∷ tagDat b cs ∷ []) R) arms))
  prodSend Γ ρ v w A u Q z B y n b cs f R arms with b ≟ z
  ... | no′ b≢z = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-prod _ _ _ _ _ _) → b≢z refl)
  ... | yes′ refl with w ≟ℕ n
  ... | no′ w≢n = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-prod _ _ _ _ _ _) → w≢n refl)
  ... | yes′ refl with ty≟ A (applyTy ρ B)
  ... | no′ ¬eq = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-prod eq _ _ _ _ _) → ¬eq eq)
  ... | yes′ refl with payCtors A in ep
  ... | nothing = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-prod _ p _ _ _ _) → just≢nothing (trans (sym p) ep))
  ... | just ds with list≟ ds cs
  ... | no′ ¬cs = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-prod _ p _ _ _ _) → ¬cs (just-inj (trans (sym ep) p)))
  ... | yes′ refl with readyN (nsuc (nsuc nzero)) f in rd
  ... | false = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-prod _ _ p _ _ _) → true≢false (trans (sym p) rd))
  ... | true with labelled R arms in lb
  ... | false = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-prod _ _ _ p _ _) → true≢false (trans (sym p) lb))
  ... | true with pickProd v u w f R arms in pk
  ... | nothing = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-prod _ _ _ _ p _) → just≢nothing (trans (sym p) pk))
  ... | just T with decideρ Γ ρ Q T
  ... | no nd = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-prod _ _ _ _ p leaf) →
          nd (subst (λ S → Conformsρ Γ ρ Q S) (just-inj (trans (sym p) pk)) leaf))
  ... | yes d = yes-send (send-prod refl ep rd lb pk d)

  splitBit : (Γ : Ctx) (ρ : Idx) (v : ValExpr nat) (w : ℕ)
      (A : Ty) (u : ValExpr A) (Q : Proc) (z : String) (B : Ty)
      (y : String) (n : ℕ) (b : String)
      (f : String) (R : Ty) (arms : List (String × Proto)) →
      AnswerSend Γ ρ v (put A u Q) (nlit w)
        (dsend z B (pcase (bySplit f (tagNat y n ∷ tagBit b ∷ []) R) arms))
  splitBit Γ ρ v w A u Q z B y n b f R arms with b ≟ z
  ... | no′ b≢z = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-pbit _ _ _ _ _) → b≢z refl)
  ... | yes′ refl with w ≟ℕ n
  ... | no′ w≢n = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-pbit _ _ _ _ _) → w≢n refl)
  ... | yes′ refl with ty≟ A bit
  ... | no′ ¬A = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-pbit _ _ _ _ _) → ¬A refl)
  ... | yes′ refl with ty≟ (applyTy ρ B) bit
  ... | no′ ¬B = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-pbit eq _ _ _ _) → ¬B (sym eq))
  ... | yes′ Beq with readyN (nsuc (nsuc nzero)) f in rd
  ... | false = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-pbit _ p _ _ _) → true≢false (trans (sym p) rd))
  ... | true with labelled R arms in lb
  ... | false = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-pbit _ _ p _ _) → true≢false (trans (sym p) lb))
  ... | true with pickProd v u w f R arms in pk
  ... | nothing = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-pbit _ _ _ p _) → just≢nothing (trans (sym p) pk))
  ... | just T with decideρ Γ ρ Q T
  ... | no nd = no-send (λ where
        (send-plain _ c) → no-split-put refl c
        (send-pbit _ _ _ p leaf) →
          nd (subst (λ S → Conformsρ Γ ρ Q S) (just-inj (trans (sym p) pk)) leaf))
  ... | yes d = yes-send (send-pbit (sym Beq) rd lb pk d)

  -- Tag lists that are not one bounded nat followed by the payload.
  data Boring : List Tag → Set where
    b-nil  : Boring []
    b-one  : ∀ {t} → Boring (t ∷ [])
    b-bit  : ∀ {x ts} → Boring (tagBit x ∷ ts)
    b-dat  : ∀ {x cs ts} → Boring (tagDat x cs ∷ ts)
    b-nn   : ∀ {a n b m ts} → Boring (tagNat a n ∷ tagNat b m ∷ ts)
    b-nd   : ∀ {a n x cs t ts} → Boring (tagNat a n ∷ tagDat x cs ∷ t ∷ ts)
    b-nb   : ∀ {a n x t ts} → Boring (tagNat a n ∷ tagBit x ∷ t ∷ ts)

  data Bore : List Tag → Set where
    bored     : ∀ {ts} → Boring ts → Bore ts
    data-prod : ∀ {y n b cs} → Bore (tagNat y n ∷ tagDat b cs ∷ [])
    bit-prod  : ∀ {y n b} → Bore (tagNat y n ∷ tagBit b ∷ [])

  bore : (ts : List Tag) → Bore ts
  bore [] = bored b-nil
  bore (t ∷ []) = bored (b-one {t = t})
  bore (tagBit x ∷ t ∷ ts) = bored (b-bit {x = x} {ts = t ∷ ts})
  bore (tagDat x cs ∷ t ∷ ts) = bored (b-dat {x = x} {cs = cs} {ts = t ∷ ts})
  bore (tagNat a n ∷ tagNat b m ∷ ts) = bored (b-nn {a = a} {n = n} {b = b} {m = m} {ts = ts})
  bore (tagNat y n ∷ tagDat b cs ∷ []) = data-prod {y = y} {n = n} {b = b} {cs = cs}
  bore (tagNat a n ∷ tagDat x cs ∷ t ∷ ts) = bored (b-nd {a = a} {n = n} {x = x} {cs = cs} {t = t} {ts = ts})
  bore (tagNat y n ∷ tagBit b ∷ []) = bit-prod {y = y} {n = n} {b = b}
  bore (tagNat a n ∷ tagBit x ∷ t ∷ ts) = bored (b-nb {a = a} {n = n} {x = x} {t = t} {ts = ts})

  tagPlain : ∀ {Γ ρ v w A u Q z B f ts R arms} →
    Boring ts →
    Answerρ Γ ρ (put A u Q) (dsend z B (pcase (bySplit f ts R) arms)) →
    AnswerSend Γ ρ v (put A u Q) (nlit w)
      (dsend z B (pcase (bySplit f ts R) arms))
  tagPlain b-nil (yes d) = yes-send (send-plain plain-dsend d)
  tagPlain b-nil (no nd) = no-send (λ { (send-plain _ c) → nd c })
  tagPlain b-one (yes d) = yes-send (send-plain plain-dsend d)
  tagPlain b-one (no nd) = no-send (λ { (send-plain _ c) → nd c })
  tagPlain b-bit (yes d) = yes-send (send-plain plain-dsend d)
  tagPlain b-bit (no nd) = no-send (λ { (send-plain _ c) → nd c })
  tagPlain b-dat (yes d) = yes-send (send-plain plain-dsend d)
  tagPlain b-dat (no nd) = no-send (λ { (send-plain _ c) → nd c })
  tagPlain b-nn (yes d) = yes-send (send-plain plain-dsend d)
  tagPlain b-nn (no nd) = no-send (λ { (send-plain _ c) → nd c })
  tagPlain b-nd (yes d) = yes-send (send-plain plain-dsend d)
  tagPlain b-nd (no nd) = no-send (λ { (send-plain _ c) → nd c })
  tagPlain b-nb (yes d) = yes-send (send-plain plain-dsend d)
  tagPlain b-nb (no nd) = no-send (λ { (send-plain _ c) → nd c })

  splitAns : (Γ : Ctx) (ρ : Idx) (v : ValExpr nat) (e : NExp) (P : Proc)
      (z : String) (C : Ty) (f : String) (ts : List Tag) (R : Ty)
      (arms : List (String × Proto)) →
      Answerρ Γ ρ P (dsend z C (pcase (bySplit f ts R) arms)) →
      AnswerSend Γ ρ v P e (dsend z C (pcase (bySplit f ts R) arms))
  splitAns Γ ρ v (nvar _) P z C f ts R arms (yes d) = yes-send (send-plain plain-dsend d)
  splitAns Γ ρ v (nvar _) P z C f ts R arms (no nd) = no-send (λ { (send-plain _ c) → nd c })
  splitAns Γ ρ v (nlit _) done z C f ts R arms (yes d) = yes-send (send-plain plain-dsend d)
  splitAns Γ ρ v (nlit _) done z C f ts R arms (no nd) = no-send (λ { (send-plain _ c) → nd c })
  splitAns Γ ρ v (nlit _) stop z C f ts R arms (yes d) = yes-send (send-plain plain-dsend d)
  splitAns Γ ρ v (nlit _) stop z C f ts R arms (no nd) = no-send (λ { (send-plain _ c) → nd c })
  splitAns Γ ρ v (nlit _) (get _ _ _) z C f ts R arms (yes d) = yes-send (send-plain plain-dsend d)
  splitAns Γ ρ v (nlit _) (get _ _ _) z C f ts R arms (no nd) = no-send (λ { (send-plain _ c) → nd c })
  splitAns Γ ρ v (nlit _) (pick0 _) z C f ts R arms (yes d) = yes-send (send-plain plain-dsend d)
  splitAns Γ ρ v (nlit _) (pick0 _) z C f ts R arms (no nd) = no-send (λ { (send-plain _ c) → nd c })
  splitAns Γ ρ v (nlit _) (pick1 _) z C f ts R arms (yes d) = yes-send (send-plain plain-dsend d)
  splitAns Γ ρ v (nlit _) (pick1 _) z C f ts R arms (no nd) = no-send (λ { (send-plain _ c) → nd c })
  splitAns Γ ρ v (nlit _) (cover _ _) z C f ts R arms (yes d) = yes-send (send-plain plain-dsend d)
  splitAns Γ ρ v (nlit _) (cover _ _) z C f ts R arms (no nd) = no-send (λ { (send-plain _ c) → nd c })
  splitAns Γ ρ v (nlit _) (iget _ _ _) z C f ts R arms (yes d) = yes-send (send-plain plain-dsend d)
  splitAns Γ ρ v (nlit _) (iget _ _ _) z C f ts R arms (no nd) = no-send (λ { (send-plain _ c) → nd c })
  splitAns Γ ρ v (nlit _) (mget _ _ _) z C f ts R arms (yes d) = yes-send (send-plain plain-dsend d)
  splitAns Γ ρ v (nlit _) (mget _ _ _) z C f ts R arms (no nd) = no-send (λ { (send-plain _ c) → nd c })
  splitAns Γ ρ v (nlit w) (put A u Q) z C f ts R arms ans with bore ts
  ... | bored b = tagPlain b ans
  ... | data-prod {y = y} {n = n} {b = b} {cs = cs} =
        prodSend Γ ρ v w A u Q z C y n b cs f R arms
  ... | bit-prod {y = y} {n = n} {b = b} =
        splitBit Γ ρ v w A u Q z C y n b f R arms

  dsendAns : (Γ : Ctx) (ρ : Idx) (v : ValExpr nat) (e : NExp) (P : Proc)
      (z : String) (C : Ty) (S : Proto) →
      Answerρ Γ ρ P (dsend z C S) →
      AnswerSend Γ ρ v P e (dsend z C S)
  dsendAns _ _ _ _ _ _ _ end (yes d) = yes-send (send-plain plain-dsend d)
  dsendAns _ _ _ _ _ _ _ end (no nd) = no-send (λ { (send-plain _ c) → nd c })
  dsendAns _ _ _ _ _ _ _ (send _ _) (yes d) = yes-send (send-plain plain-dsend d)
  dsendAns _ _ _ _ _ _ _ (send _ _) (no nd) = no-send (λ { (send-plain _ c) → nd c })
  dsendAns _ _ _ _ _ _ _ (recv _ _) (yes d) = yes-send (send-plain plain-dsend d)
  dsendAns _ _ _ _ _ _ _ (recv _ _) (no nd) = no-send (λ { (send-plain _ c) → nd c })
  dsendAns _ _ _ _ _ _ _ (dsend _ _ _) (yes d) = yes-send (send-plain plain-dsend d)
  dsendAns _ _ _ _ _ _ _ (dsend _ _ _) (no nd) = no-send (λ { (send-plain _ c) → nd c })
  dsendAns _ _ _ _ _ _ _ (drecv _ _ _) (yes d) = yes-send (send-plain plain-dsend d)
  dsendAns _ _ _ _ _ _ _ (drecv _ _ _) (no nd) = no-send (λ { (send-plain _ c) → nd c })
  dsendAns _ _ _ _ _ _ _ (esend _ _ _) (yes d) = yes-send (send-plain plain-dsend d)
  dsendAns _ _ _ _ _ _ _ (esend _ _ _) (no nd) = no-send (λ { (send-plain _ c) → nd c })
  dsendAns _ _ _ _ _ _ _ (erecv _ _ _) (yes d) = yes-send (send-plain plain-dsend d)
  dsendAns _ _ _ _ _ _ _ (erecv _ _ _) (no nd) = no-send (λ { (send-plain _ c) → nd c })
  dsendAns _ _ _ _ _ _ _ (isend _ _ _) (yes d) = yes-send (send-plain plain-dsend d)
  dsendAns _ _ _ _ _ _ _ (isend _ _ _) (no nd) = no-send (λ { (send-plain _ c) → nd c })
  dsendAns _ _ _ _ _ _ _ (irecv _ _ _) (yes d) = yes-send (send-plain plain-dsend d)
  dsendAns _ _ _ _ _ _ _ (irecv _ _ _) (no nd) = no-send (λ { (send-plain _ c) → nd c })
  dsendAns _ _ _ _ _ _ _ (choose _ _) (yes d) = yes-send (send-plain plain-dsend d)
  dsendAns _ _ _ _ _ _ _ (choose _ _) (no nd) = no-send (λ { (send-plain _ c) → nd c })
  dsendAns _ _ _ _ _ _ _ (branch _ _) (yes d) = yes-send (send-plain plain-dsend d)
  dsendAns _ _ _ _ _ _ _ (branch _ _) (no nd) = no-send (λ { (send-plain _ c) → nd c })
  dsendAns _ _ _ _ _ _ _ (pcase (byVal _) _) (yes d) = yes-send (send-plain plain-dsend d)
  dsendAns _ _ _ _ _ _ _ (pcase (byVal _) _) (no nd) = no-send (λ { (send-plain _ c) → nd c })
  dsendAns _ _ _ _ _ _ _ (pcase (byRun _ _ _) _) (yes d) = yes-send (send-plain plain-dsend d)
  dsendAns _ _ _ _ _ _ _ (pcase (byRun _ _ _) _) (no nd) = no-send (λ { (send-plain _ c) → nd c })
  dsendAns Γ ρ v e P z C (pcase (bySplit f ts R) arms) ans =
    splitAns Γ ρ v e P z C f ts R arms ans

  plainEnd : ∀ {Γ ρ v e P} → Answerρ Γ ρ P end → AnswerSend Γ ρ v P e end
  plainEnd (yes d) = yes-send (send-plain plain-end d)
  plainEnd (no nd) = no-send (λ { (send-plain _ c) → nd c })

  plainSend : ∀ {Γ ρ v e P A S} → Answerρ Γ ρ P (send A S) → AnswerSend Γ ρ v P e (send A S)
  plainSend (yes d) = yes-send (send-plain plain-send d)
  plainSend (no nd) = no-send (λ { (send-plain _ c) → nd c })

  plainRecv : ∀ {Γ ρ v e P A S} → Answerρ Γ ρ P (recv A S) → AnswerSend Γ ρ v P e (recv A S)
  plainRecv (yes d) = yes-send (send-plain plain-recv d)
  plainRecv (no nd) = no-send (λ { (send-plain _ c) → nd c })

  plainDrecv : ∀ {Γ ρ v e P y A S} → Answerρ Γ ρ P (drecv y A S) → AnswerSend Γ ρ v P e (drecv y A S)
  plainDrecv (yes d) = yes-send (send-plain plain-drecv d)
  plainDrecv (no nd) = no-send (λ { (send-plain _ c) → nd c })

  plainEsend : ∀ {Γ ρ v e P y g S} → Answerρ Γ ρ P (esend y g S) → AnswerSend Γ ρ v P e (esend y g S)
  plainEsend (yes d) = yes-send (send-plain plain-esend d)
  plainEsend (no nd) = no-send (λ { (send-plain _ c) → nd c })

  plainErecv : ∀ {Γ ρ v e P y g S} → Answerρ Γ ρ P (erecv y g S) → AnswerSend Γ ρ v P e (erecv y g S)
  plainErecv (yes d) = yes-send (send-plain plain-erecv d)
  plainErecv (no nd) = no-send (λ { (send-plain _ c) → nd c })

  plainIsend : ∀ {Γ ρ v e P y S T} → Answerρ Γ ρ P (isend y S T) → AnswerSend Γ ρ v P e (isend y S T)
  plainIsend (yes d) = yes-send (send-plain plain-isend d)
  plainIsend (no nd) = no-send (λ { (send-plain _ c) → nd c })

  plainIrecv : ∀ {Γ ρ v e P y S T} → Answerρ Γ ρ P (irecv y S T) → AnswerSend Γ ρ v P e (irecv y S T)
  plainIrecv (yes d) = yes-send (send-plain plain-irecv d)
  plainIrecv (no nd) = no-send (λ { (send-plain _ c) → nd c })

  plainChoose : ∀ {Γ ρ v e P S T} → Answerρ Γ ρ P (choose S T) → AnswerSend Γ ρ v P e (choose S T)
  plainChoose (yes d) = yes-send (send-plain plain-choose d)
  plainChoose (no nd) = no-send (λ { (send-plain _ c) → nd c })

  plainBranch : ∀ {Γ ρ v e P S T} → Answerρ Γ ρ P (branch S T) → AnswerSend Γ ρ v P e (branch S T)
  plainBranch (yes d) = yes-send (send-plain plain-branch d)
  plainBranch (no nd) = no-send (λ { (send-plain _ c) → nd c })

  decideSend : (Γ : Ctx) (ρ : Idx) (v : ValExpr nat) (e : NExp) (P : Proc) (S : Proto) →
    AnswerSend Γ ρ v P e S
  decideSend Γ ρ v (nlit w) P (pcase (byVal y) arms) with pickShown v w arms in pk
  ... | nothing = no-send (λ where
        (send-plain pl _) → plain-not pl
        (send-val p _) → just≢nothing (trans (sym p) pk))
  ... | just T with decideρ Γ ρ P T
  ... | yes d = yes-send (send-val pk d)
  ... | no nd = no-send (λ where
        (send-plain pl _) → plain-not pl
        (send-val p c) →
          nd (subst (λ S → Conformsρ Γ ρ P S) (just-inj (trans (sym p) pk)) c))
  decideSend Γ ρ v (nlit w) P (pcase (byRun f y R) arms) with readyN (nsuc nzero) f in rd
  ... | false = no-send (λ where
        (send-plain pl _) → plain-not pl
        (send-run p _ _ _) → true≢false (trans (sym p) rd))
  ... | true with labelled R arms in lb
  ... | false = no-send (λ where
        (send-plain pl _) → plain-not pl
        (send-run _ p _ _) → true≢false (trans (sym p) lb))
  ... | true with pickRun v w f R arms in pk
  ... | nothing = no-send (λ where
        (send-plain pl _) → plain-not pl
        (send-run _ _ p _) → just≢nothing (trans (sym p) pk))
  ... | just T with decideρ Γ ρ P T
  ... | yes d = yes-send (send-run rd lb pk d)
  ... | no nd = no-send (λ where
        (send-plain pl _) → plain-not pl
        (send-run _ _ p c) →
          nd (subst (λ S → Conformsρ Γ ρ P S) (just-inj (trans (sym p) pk)) c))
  decideSend Γ ρ v (nvar _) P (pcase _ _) = no-send (λ { (send-plain pl _) → plain-not pl })
  decideSend Γ ρ v (nlit _) P (pcase (bySplit _ _ _) _) = no-send (λ { (send-plain pl _) → plain-not pl })
  decideSend Γ ρ v e P end = plainEnd (decideρ Γ ρ P end)
  decideSend Γ ρ v e P (send A S) = plainSend (decideρ Γ ρ P (send A S))
  decideSend Γ ρ v e P (recv A S) = plainRecv (decideρ Γ ρ P (recv A S))
  decideSend Γ ρ v e P (dsend z C S) = dsendAns Γ ρ v e P z C S (decideρ Γ ρ P (dsend z C S))
  decideSend Γ ρ v e P (drecv y A S) = plainDrecv (decideρ Γ ρ P (drecv y A S))
  decideSend Γ ρ v e P (esend y g S) = plainEsend (decideρ Γ ρ P (esend y g S))
  decideSend Γ ρ v e P (erecv y g S) = plainErecv (decideρ Γ ρ P (erecv y g S))
  decideSend Γ ρ v e P (isend y S T) = plainIsend (decideρ Γ ρ P (isend y S T))
  decideSend Γ ρ v e P (irecv y S T) = plainIrecv (decideρ Γ ρ P (irecv y S T))
  decideSend Γ ρ v e P (choose S T) = plainChoose (decideρ Γ ρ P (choose S T))
  decideSend Γ ρ v e P (branch S T) = plainBranch (decideρ Γ ρ P (branch S T))

  matchAnswer : (Γ : Ctx) (ρ : Idx) (A : Ty) (x : String) (ps : List PArm) (S : Proto) →
    Answerρ Γ ρ (mget A x ps) S
  matchAnswer Γ ρ A x ps (recv B S) =
    on-mget (ty≟ A (applyTy ρ B)) (cover? A ps) (decideArms ((x , A) ∷ Γ) ρ A nzero ps S)
  matchAnswer _ _ _ _ _ end = no (λ ())
  matchAnswer _ _ _ _ _ (send _ _) = no (λ ())
  matchAnswer _ _ _ _ _ (dsend _ _ _) = no (λ ())
  matchAnswer Γ ρ A x ps (drecv y B (pcase (byVal z) arms)) with z ≟ y
  ... | no′ z≢y = no (λ { (mget-val _ _ _ _) → z≢y refl })
  ... | yes′ refl with ty≟ A (applyTy ρ B)
  ... | no′ ¬eq = no (λ { (mget-val eq _ _ _) → ¬eq eq })
  ... | yes′ refl with cover? A ps
  ... | no′ nc = no (λ { (mget-val _ c _ _) → nc c })
  ... | yes′ c with labelled A arms in lb
  ... | false = no (λ { (mget-val _ _ p _) → true≢false (trans (sym p) lb) })
  ... | true = on-at c lb (decideAt ((x , A) ∷ Γ) (renameIdx y x (shadow y ρ)) A arms ps)
  matchAnswer Γ ρ A x ps (drecv y B (pcase (byRun f z R) arms)) with z ≟ y
  ... | no′ z≢y = no (λ { (mget-run _ _ _ _ _ _) → z≢y refl })
  ... | yes′ refl with ty≟ A (applyTy ρ B)
  ... | no′ ¬eq = no (λ { (mget-run eq _ _ _ _ _) → ¬eq eq })
  ... | yes′ refl with cover? A ps
  ... | no′ nc = no (λ { (mget-run _ c _ _ _ _) → nc c })
  ... | yes′ c with runReady f in rd
  ... | false = no (λ { (mget-run _ _ p _ _ _) → true≢false (trans (sym p) rd) })
  ... | true with labelled R arms in lb
  ... | false = no (λ { (mget-run _ _ _ p _ _) → true≢false (trans (sym p) lb) })
  ... | true with payCtors A in ep
  ... | nothing = no (λ { (mget-run _ _ _ _ p _) → just≢nothing (trans (sym p) ep) })
  ... | just cs = on-run c rd lb ep (decideRun ((x , A) ∷ Γ) (renameIdx y x (shadow y ρ)) f A R arms cs ps)
  matchAnswer Γ ρ A x ps (drecv y B (pcase (bySplit f tags R) arms))
    with recvView Γ ρ A x ps y B f tags R arms
  ... | rv-no ¬c = no ¬c
  ... | rv-data d w cs grid refl eq ep rd lb pg =
      finishProd eq ep rd lb pg (decideProd ((x , A) ∷ Γ) ρ A d w cs grid ps)
  ... | rv-bit d w grid refl refl refl rd lb pg =
      finishBit rd lb pg (decideProd ((x , bit) ∷ Γ) ρ bit d w ("b0" ∷ "b1" ∷ []) grid ps)
  ... | rv-wide wt t cs rows eq lt tn ep labs rd lb wr len =
      finishWide wt eq lt tn ep labs rd lb wr len
        (armsDec ((x , A) ∷ Γ) ρ A cs (rev (dropLast tags)) rows ps)
  matchAnswer _ _ _ _ _ (drecv _ _ end) = no (λ ())
  matchAnswer _ _ _ _ _ (drecv _ _ (send _ _)) = no (λ ())
  matchAnswer _ _ _ _ _ (drecv _ _ (recv _ _)) = no (λ ())
  matchAnswer _ _ _ _ _ (drecv _ _ (dsend _ _ _)) = no (λ ())
  matchAnswer _ _ _ _ _ (drecv _ _ (drecv _ _ _)) = no (λ ())
  matchAnswer _ _ _ _ _ (drecv _ _ (esend _ _ _)) = no (λ ())
  matchAnswer _ _ _ _ _ (drecv _ _ (erecv _ _ _)) = no (λ ())
  matchAnswer _ _ _ _ _ (drecv _ _ (isend _ _ _)) = no (λ ())
  matchAnswer _ _ _ _ _ (drecv _ _ (irecv _ _ _)) = no (λ ())
  matchAnswer _ _ _ _ _ (drecv _ _ (choose _ _)) = no (λ ())
  matchAnswer _ _ _ _ _ (drecv _ _ (branch _ _)) = no (λ ())
  matchAnswer _ _ _ _ _ (esend _ _ _) = no (λ ())
  matchAnswer Γ ρ A x ps (erecv y e S) = decideENat Γ ρ A x ps y e S
  matchAnswer _ _ _ _ _ (isend _ _ _) = no (λ ())
  matchAnswer _ _ _ _ _ (irecv _ _ _) = no (λ ())
  matchAnswer _ _ _ _ _ (choose _ _) = no (λ ())
  matchAnswer _ _ _ _ _ (branch _ _) = no (λ ())
  matchAnswer _ _ _ _ _ (pcase _ _) = no (λ ())

  finishWide : ∀ {Γ ρ A B x y f tags R ps arms rows t cs} →
    (wt : WTag tags) →
    A ≡ applyTy ρ B →
    lastTag tags ≡ just t →
    tagName t ≡ y →
    payCtors A ≡ just cs →
    tagLabs t ≡ cs →
    readyN (length tags) f ≡ true →
    labelled R arms ≡ true →
    wideRows f R arms (tagsFac tags) ≡ just rows →
    length rows ≡ prodNs (map facWidth (tagsFac tags)) →
    AnswerWA ((x , A) ∷ Γ) ρ A cs (rev (dropLast tags)) rows ps →
    Answerρ Γ ρ (mget A x ps)
      (drecv y B (pcase (bySplit f tags R) arms))
  finishWide wt eq lt tn ep labs rd lb wr len (yes-wa cov) =
    yes (mget-wide wt eq lt tn ep labs rd lb wr len cov)
  finishWide {Γ = Γ} {ρ = ρ} {A = A} {x = x} {tags = tags} {ps = ps} {cs = cs}
      wt eq lt tn ep labs rd lb wr len (no-wa nw) =
    no (λ { (mget-wide {rows = rows′} {cs = cs′} _ _ _ _ pc _ _ _ wr′ _ cov) →
      nw (subst (λ rs → WArms ((x , A) ∷ Γ) ρ A cs (rev (dropLast tags)) rs ps)
            (just-inj (trans (sym wr′) wr))
            (subst (λ zs → WArms ((x , A) ∷ Γ) ρ A zs (rev (dropLast tags)) rows′ ps)
              (just-inj (trans (sym pc) ep)) cov)) })

  finishEWide : ∀ {Γ ρ x y w f tags R ps arms rows} →
    (wt : WTag tags) →
    lastTag tags ≡ just (tagNat y w) →
    readyN (length tags) f ≡ true →
    labelled R arms ≡ true →
    wideRows f R arms (tagsFac tags) ≡ just rows →
    length rows ≡ prodNs (map facWidth (tagsFac tags)) →
    AnswerWA ((x , nat) ∷ Γ) ρ nat (natArms w) (rev (dropLast tags)) rows ps →
    Answerρ Γ ρ (mget nat x ps)
      (erecv y (nlit w) (pcase (bySplit f tags R) arms))
  finishEWide wt lt rd lb wr len (yes-wa cov) =
    yes (eget-wide wt lt rd lb wr len cov)
  finishEWide {Γ = Γ} {ρ = ρ} {x = x} {w = w} {tags = tags} {ps = ps}
      wt lt rd lb wr len (no-wa nw) =
    no (λ { (eget-wide {rows = rows′} _ _ _ _ wr′ _ cov) →
      nw (subst (λ rs → WArms ((x , nat) ∷ Γ) ρ nat (natArms w) (rev (dropLast tags)) rs ps)
            (just-inj (trans (sym wr′) wr)) cov) })

  decideESplit : (Γ : Ctx) (ρ : Idx) (A : Ty) (x : String) (ps : List PArm)
      (y : String) (w : ℕ) (f : String) (tags : List Tag) (R : Ty)
      (arms : List (String × Proto)) →
      Answerρ Γ ρ (mget A x ps)
        (erecv y (nlit w) (pcase (bySplit f tags R) arms))
  decideESplit Γ ρ A x ps y w f tags R arms with wtag tags in wtq
  ... | nothing = no (λ { (eget-wide wt _ _ _ _ _ _) →
        just≢nothing (trans (sym (wtag-just wt)) wtq) })
  ... | just wt with ty≟ A nat
  ... | no′ ¬A = no (λ { (eget-wide _ _ _ _ _ _ _) → ¬A refl })
  ... | yes′ refl with lastTag tags in lt
  ... | nothing = no (λ { (eget-wide _ p _ _ _ _ _) → just≢nothing (trans (sym p) lt) })
  ... | just (tagBit _) = no (λ { (eget-wide _ p _ _ _ _ _) →
        tagBit≢Nat (just-inj (trans (sym lt) p)) })
  ... | just (tagDat _ _) = no (λ { (eget-wide _ p _ _ _ _ _) →
        tagDat≢Nat (just-inj (trans (sym lt) p)) })
  ... | just (tagNat z n) with z ≟ y
  ... | no′ ¬z = no (λ { (eget-wide _ p _ _ _ _ _) →
        ¬z (proj₁ (tagNat-inj (just-inj (trans (sym lt) p)))) })
  ... | yes′ refl with n ≟ℕ w
  ... | no′ ¬n = no (λ { (eget-wide _ p _ _ _ _ _) →
        ¬n (proj₂ (tagNat-inj (just-inj (trans (sym lt) p)))) })
  ... | yes′ refl with readyN (length tags) f in rd
  ... | false = no (λ { (eget-wide _ _ p _ _ _ _) → true≢false (trans (sym p) rd) })
  ... | true with labelled R arms in lb
  ... | false = no (λ { (eget-wide _ _ _ p _ _ _) → true≢false (trans (sym p) lb) })
  ... | true with wideRows f R arms (tagsFac tags) in wr
  ... | nothing = no (λ { (eget-wide _ _ _ _ p _ _) → just≢nothing (trans (sym p) wr) })
  ... | just rows with length rows ≟ℕ prodNs (map facWidth (tagsFac tags))
  ... | no′ ¬len = no (λ { (eget-wide {rows = rows′} _ _ _ _ wr′ len′ _) →
        ¬len (subst (λ rs → length rs ≡ prodNs (map facWidth (tagsFac tags)))
               (just-inj (trans (sym wr′) wr)) len′) })
  ... | yes′ len =
      finishEWide wt lt rd lb wr len
        (armsDec ((x , nat) ∷ Γ) ρ nat (natArms w) (rev (dropLast tags)) rows ps)

  walk0 : (Γ : Ctx) (ρ : Idx) (f : String) (R : Ty) (arms : List (String × Proto))
      (acc : List Got) (proto : Proto) (proc : Proc) {full : List Tag} →
      splitAt proto ≡ just (f , full , R , arms) →
      Walk Γ ρ f R arms acc [] proto proc
  walk0 Γ ρ f R arms acc (pcase (bySplit _ _ _) _) proc _
      with pickRead (acc ++ []) f R arms in pk
  ... | nothing = walk-no (λ { sp-case q _ → just≢nothing (trans (sym q) pk) })
  ... | just T with decideρ Γ ρ proc T
  ... | yes d = walk-yes sp-case pk d
  ... | no nd = walk-no (λ { sp-case q c →
        nd (subst (λ S → Conformsρ Γ ρ proc S) (just-inj (trans (sym q) pk)) c) })
  walk0 _ _ _ _ _ _ end _ _ = noSpine (λ ())
  walk0 _ _ _ _ _ _ (send _ _) _ _ = noSpine (λ ())
  walk0 _ _ _ _ _ _ (recv _ _) _ _ = noSpine (λ ())
  walk0 _ _ _ _ _ _ (dsend _ _ _) _ _ = noSpine (λ ())
  walk0 _ _ _ _ _ _ (drecv _ _ _) _ _ = noSpine (λ ())
  walk0 _ _ _ _ _ _ (esend _ _ _) _ _ = noSpine (λ ())
  walk0 _ _ _ _ _ _ (erecv _ _ _) _ _ = noSpine (λ ())
  walk0 _ _ _ _ _ _ (isend _ _ _) _ _ = noSpine (λ ())
  walk0 _ _ _ _ _ _ (irecv _ _ _) _ _ = noSpine (λ ())
  walk0 _ _ _ _ _ _ (choose _ _) _ _ = noSpine (λ ())
  walk0 _ _ _ _ _ _ (branch _ _) _ _ = noSpine (λ ())
  walk0 _ _ _ _ _ _ (pcase (byVal _) _) _ _ = noSpine (λ ())
  walk0 _ _ _ _ _ _ (pcase (byRun _ _ _) _) _ _ = noSpine (λ ())

  walkNat : (Γ : Ctx) (ρ : Idx) (f : String) (R : Ty) (arms : List (String × Proto))
      (acc : List Got) (x : String) (w : ℕ) (ts : List Tag) (proto : Proto)
      {A : Ty} (v : ValExpr A) (P : Proc) {full : List Tag} →
      splitAt proto ≡ just (f , full , R , arms) →
      Walk Γ ρ f R arms acc (tagNat x w ∷ ts) proto (put A v P)
  walkNat Γ ρ f R arms acc x w ts (esend y (nlit n) S) {A = A} v P eq with ty≟ A nat
  ... | no′ ¬A = noSpine (λ { (sp-nat _ _ _ _ _ _) → ¬A refl })
  ... | yes′ refl with x ≟ y
  ... | no′ ¬xy = noSpine (λ { (sp-nat q _ _ _ _ _) → ¬xy q })
  ... | yes′ refl with w ≟ℕ n
  ... | no′ ¬wn = noSpine (λ { (sp-nat _ q _ _ _ _) → ¬wn q })
  ... | yes′ refl with natGot v w in ng
  ... | nothing = walk-no (λ { (sp-nat _ _ p _ _ _) _ _ → just≢nothing (trans (sym p) ng) })
  ... | just gUnk = walk-no (λ { (sp-nat _ _ p _ _ _) _ _ →
        gUnk≢val (just-inj (trans (sym ng) p)) })
  ... | just (gVal r) with owed? Γ v (just (nlit w))
  ... | no′ now = walk-no (λ { (sp-nat _ _ _ ow _ _) _ _ → now ow })
  ... | yes′ ow with decideValExpr Γ v
  ... | no′ nv = walk-no (λ { (sp-nat _ _ _ _ vok _) _ _ → nv vok })
  ... | yes′ vok with walk Γ ρ f R arms (acc ++ (gVal r ∷ [])) ts S P eq
  ... | walk-yes {gs = gs} spin pk d =
      walk-yes (sp-nat refl refl ng ow vok spin) (shiftRead acc (gVal r) gs pk) d
  ... | walk-no n = walk-no (carryNat {f = f} {R = R} {arms = arms} {acc = acc} {r = r} ng n)
  walkNat _ _ _ _ _ _ _ _ _ end _ _ _ = noSpine (λ ())
  walkNat _ _ _ _ _ _ _ _ _ (send _ _) _ _ _ = noSpine (λ ())
  walkNat _ _ _ _ _ _ _ _ _ (recv _ _) _ _ _ = noSpine (λ ())
  walkNat _ _ _ _ _ _ _ _ _ (dsend _ _ _) _ _ _ = noSpine (λ ())
  walkNat _ _ _ _ _ _ _ _ _ (drecv _ _ _) _ _ _ = noSpine (λ ())
  walkNat _ _ _ _ _ _ _ _ _ (esend _ (nvar _) _) _ _ _ = noSpine (λ ())
  walkNat _ _ _ _ _ _ _ _ _ (erecv _ _ _) _ _ _ = noSpine (λ ())
  walkNat _ _ _ _ _ _ _ _ _ (isend _ _ _) _ _ _ = noSpine (λ ())
  walkNat _ _ _ _ _ _ _ _ _ (irecv _ _ _) _ _ _ = noSpine (λ ())
  walkNat _ _ _ _ _ _ _ _ _ (choose _ _) _ _ _ = noSpine (λ ())
  walkNat _ _ _ _ _ _ _ _ _ (branch _ _) _ _ _ = noSpine (λ ())
  walkNat _ _ _ _ _ _ _ _ _ (pcase _ _) _ _ _ = noSpine (λ ())

  walkBit : (Γ : Ctx) (ρ : Idx) (f : String) (R : Ty) (arms : List (String × Proto))
      (acc : List Got) (x : String) (ts : List Tag) (proto : Proto)
      {A : Ty} (v : ValExpr A) (P : Proc) {full : List Tag} →
      splitAt proto ≡ just (f , full , R , arms) →
      Walk Γ ρ f R arms acc (tagBit x ∷ ts) proto (put A v P)
  walkBit Γ ρ f R arms acc x ts (dsend y B S) {A = A} v P eq =
    closeBit Γ ρ f R arms acc x ts y B S v P (bitPrep Γ v x y B)
      (λ g → walk Γ ρ f R arms (acc ++ (g ∷ [])) ts S P eq)
  walkBit _ _ _ _ _ _ _ _ end _ _ _ = noSpine (λ ())
  walkBit _ _ _ _ _ _ _ _ (send _ _) _ _ _ = noSpine (λ ())
  walkBit _ _ _ _ _ _ _ _ (recv _ _) _ _ _ = noSpine (λ ())
  walkBit _ _ _ _ _ _ _ _ (drecv _ _ _) _ _ _ = noSpine (λ ())
  walkBit _ _ _ _ _ _ _ _ (esend _ _ _) _ _ _ = noSpine (λ ())
  walkBit _ _ _ _ _ _ _ _ (erecv _ _ _) _ _ _ = noSpine (λ ())
  walkBit _ _ _ _ _ _ _ _ (isend _ _ _) _ _ _ = noSpine (λ ())
  walkBit _ _ _ _ _ _ _ _ (irecv _ _ _) _ _ _ = noSpine (λ ())
  walkBit _ _ _ _ _ _ _ _ (choose _ _) _ _ _ = noSpine (λ ())
  walkBit _ _ _ _ _ _ _ _ (branch _ _) _ _ _ = noSpine (λ ())
  walkBit _ _ _ _ _ _ _ _ (pcase _ _) _ _ _ = noSpine (λ ())

  walkDat : (Γ : Ctx) (ρ : Idx) (f : String) (R : Ty) (arms : List (String × Proto))
      (acc : List Got) (x : String) (cs : List String) (ts : List Tag) (proto : Proto)
      {A : Ty} (v : ValExpr A) (P : Proc) {full : List Tag} →
      splitAt proto ≡ just (f , full , R , arms) →
      Walk Γ ρ f R arms acc (tagDat x cs ∷ ts) proto (put A v P)
  walkDat Γ ρ f R arms acc x cs ts (dsend y B S) {A = A} v P eq with x ≟ y
  ... | no′ ¬xy = noSpine (λ { (sp-dat q _ _ _ _ _ _) → ¬xy q })
  ... | yes′ refl with ty≟ A B
  ... | no′ ¬AB = noSpine (λ { (sp-dat _ q _ _ _ _ _) → ¬AB q })
  ... | yes′ refl with payCtors A in ep
  ... | nothing = walk-no (λ { (sp-dat _ _ p _ _ _ _) _ _ → just≢nothing (trans (sym p) ep) })
  ... | just ds with strsEq ds cs in se
  ... | false = walk-no (λ { (sp-dat {ds = ds′} _ _ p q _ _ _) _ _ →
        true≢false (trans (sym
          (subst (λ zs → strsEq zs cs ≡ true) (sym (just-inj (trans (sym ep) p))) q)) se) })
  ... | true with payGot v in pg
  ... | nothing = walk-no (λ { (sp-dat _ _ _ _ p _ _) _ _ → just≢nothing (trans (sym p) pg) })
  ... | just g with decideValExpr Γ v
  ... | no′ nv = walk-no (λ { (sp-dat _ _ _ _ _ vok _) _ _ → nv vok })
  ... | yes′ vok with walk Γ ρ f R arms (acc ++ (g ∷ [])) ts S P eq
  ... | walk-yes {gs = gs} spin pk d =
      walk-yes (sp-dat refl refl ep se pg vok spin) (shiftRead acc g gs pk) d
  ... | walk-no n = walk-no (λ where
        (sp-dat {g = g′} {gs = gs} _ _ _ _ pg′ _ spin) q c →
          n spin (unshiftRead acc g gs
            (subst (λ h → pickRead (acc ++ (h ∷ gs)) f R arms ≡ just _)
              (just-inj (trans (sym pg′) pg)) q)) c)
  walkDat _ _ _ _ _ _ _ _ _ end _ _ _ = noSpine (λ ())
  walkDat _ _ _ _ _ _ _ _ _ (send _ _) _ _ _ = noSpine (λ ())
  walkDat _ _ _ _ _ _ _ _ _ (recv _ _) _ _ _ = noSpine (λ ())
  walkDat _ _ _ _ _ _ _ _ _ (drecv _ _ _) _ _ _ = noSpine (λ ())
  walkDat _ _ _ _ _ _ _ _ _ (esend _ _ _) _ _ _ = noSpine (λ ())
  walkDat _ _ _ _ _ _ _ _ _ (erecv _ _ _) _ _ _ = noSpine (λ ())
  walkDat _ _ _ _ _ _ _ _ _ (isend _ _ _) _ _ _ = noSpine (λ ())
  walkDat _ _ _ _ _ _ _ _ _ (irecv _ _ _) _ _ _ = noSpine (λ ())
  walkDat _ _ _ _ _ _ _ _ _ (choose _ _) _ _ _ = noSpine (λ ())
  walkDat _ _ _ _ _ _ _ _ _ (branch _ _) _ _ _ = noSpine (λ ())
  walkDat _ _ _ _ _ _ _ _ _ (pcase _ _) _ _ _ = noSpine (λ ())

  walk : (Γ : Ctx) (ρ : Idx) (f : String) (R : Ty) (arms : List (String × Proto))
      (acc : List Got) (ts : List Tag) (proto : Proto) (proc : Proc) {full : List Tag} →
      splitAt proto ≡ just (f , full , R , arms) →
      Walk Γ ρ f R arms acc ts proto proc
  walk Γ ρ f R arms acc [] proto proc eq = walk0 Γ ρ f R arms acc proto proc eq
  walk Γ ρ f R arms acc (tagNat x w ∷ ts) proto (put A v P) eq =
    walkNat Γ ρ f R arms acc x w ts proto v P eq
  walk _ _ _ _ _ _ (tagNat _ _ ∷ _) _ done _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagNat _ _ ∷ _) _ stop _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagNat _ _ ∷ _) _ (get _ _ _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagNat _ _ ∷ _) _ (pick0 _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagNat _ _ ∷ _) _ (pick1 _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagNat _ _ ∷ _) _ (cover _ _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagNat _ _ ∷ _) _ (iget _ _ _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagNat _ _ ∷ _) _ (mget _ _ _) _ = noSpine (λ ())
  walk Γ ρ f R arms acc (tagBit x ∷ ts) proto (put A v P) eq =
    walkBit Γ ρ f R arms acc x ts proto v P eq
  walk _ _ _ _ _ _ (tagBit _ ∷ _) _ done _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagBit _ ∷ _) _ stop _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagBit _ ∷ _) _ (get _ _ _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagBit _ ∷ _) _ (pick0 _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagBit _ ∷ _) _ (pick1 _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagBit _ ∷ _) _ (cover _ _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagBit _ ∷ _) _ (iget _ _ _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagBit _ ∷ _) _ (mget _ _ _) _ = noSpine (λ ())
  walk Γ ρ f R arms acc (tagDat x cs ∷ ts) proto (put A v P) eq =
    walkDat Γ ρ f R arms acc x cs ts proto v P eq
  walk _ _ _ _ _ _ (tagDat _ _ ∷ _) _ done _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagDat _ _ ∷ _) _ stop _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagDat _ _ ∷ _) _ (get _ _ _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagDat _ _ ∷ _) _ (pick0 _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagDat _ _ ∷ _) _ (pick1 _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagDat _ _ ∷ _) _ (cover _ _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagDat _ _ ∷ _) _ (iget _ _ _) _ = noSpine (λ ())
  walk _ _ _ _ _ _ (tagDat _ _ ∷ _) _ (mget _ _ _) _ = noSpine (λ ())

  -- A non-empty factor list. There is no empty clause, so this cannot
  -- reach the case split on the same process.
  walkCons : (Γ : Ctx) (ρ : Idx) (f : String) (R : Ty) (arms : List (String × Proto))
      (acc : List Got) (t : Tag) (ts : List Tag) (proto : Proto) (proc : Proc)
      {full : List Tag} →
      splitAt proto ≡ just (f , full , R , arms) →
      Walk Γ ρ f R arms acc (t ∷ ts) proto proc
  walkCons Γ ρ f R arms acc (tagNat x w) ts proto (put A v P) eq =
    walkNat Γ ρ f R arms acc x w ts proto v P eq
  walkCons Γ ρ f R arms acc (tagBit x) ts proto (put A v P) eq =
    walkBit Γ ρ f R arms acc x ts proto v P eq
  walkCons Γ ρ f R arms acc (tagDat x cs) ts proto (put A v P) eq =
    walkDat Γ ρ f R arms acc x cs ts proto v P eq
  walkCons _ _ _ _ _ _ _ _ _ done _ = noSpine (λ ())
  walkCons _ _ _ _ _ _ _ _ _ stop _ = noSpine (λ ())
  walkCons _ _ _ _ _ _ _ _ _ (get _ _ _) _ = noSpine (λ ())
  walkCons _ _ _ _ _ _ _ _ _ (pick0 _) _ = noSpine (λ ())
  walkCons _ _ _ _ _ _ _ _ _ (pick1 _) _ = noSpine (λ ())
  walkCons _ _ _ _ _ _ _ _ _ (cover _ _) _ = noSpine (λ ())
  walkCons _ _ _ _ _ _ _ _ _ (iget _ _ _) _ = noSpine (λ ())
  walkCons _ _ _ _ _ _ _ _ _ (mget _ _ _) _ = noSpine (λ ())

  sealD : ∀ {Γ ρ B y v P S} →
    let A = applyTy ρ B in
    Plain S →
    (∀ {tags Q gs f R arms T rows} →
      WTag tags →
      PutSpine Γ tags (dsend y B S) (put A v P) Q gs →
      splitAt (dsend y B S) ≡ just (f , tags , R , arms) →
      readyN (length tags) f ≡ true →
      labelled R arms ≡ true →
      wideRows f R arms (tagsFac tags) ≡ just rows →
      length rows ≡ prodNs (map facWidth (tagsFac tags)) →
      pickRead gs f R arms ≡ just T →
      Conformsρ Γ ρ Q T → ⊥) →
    Dec (ValExprOk Γ v) →
    Answerρ Γ (bind y (ixOf A v) (shadow y ρ)) P S →
    Answerρ Γ ρ (put A v P) (dsend y B S)
  sealD pl nw (yes′ vok) (yes d) = yes (dput-ok refl vok pl d)
  sealD pl nw (yes′ _) (no nd) = no (λ where
    (dput-ok refl _ _ c) → nd c
    (dput-arm _ _ _ _) → plain-not pl
    (dput-wide _ w spin p rd lb wr len pk c) → nw w spin p rd lb wr len pk c)
  sealD pl nw (no′ nv) _ = no (λ where
    (dput-ok refl vok _ _) → nv vok
    (dput-arm _ vok _ _) → plain-not pl
    (dput-wide _ w spin p rd lb wr len pk c) → nw w spin p rd lb wr len pk c)

  -- The ordinary dependent send. The payload is only
  -- propositionally `applyTy`, so `sealD` sees the cast value.
  plainOf : {A : Ty} (Γ : Ctx) (ρ : Idx) (B : Ty)
      (y : String) (v : ValExpr A) (P : Proc) (S : Proto) →
      (eq : A ≡ applyTy ρ B) →
      (∀ {us Q gs g Qy as T rows′} →
        WTag us →
        PutSpine Γ us (dsend y B S) (put (applyTy ρ B) (castV eq v) P) Q gs →
        splitAt (dsend y B S) ≡ just (g , us , Qy , as) →
        readyN (length us) g ≡ true →
        labelled Qy as ≡ true →
        wideRows g Qy as (tagsFac us) ≡ just rows′ →
        length rows′ ≡ prodNs (map facWidth (tagsFac us)) →
        pickRead gs g Qy as ≡ just T →
        Conformsρ Γ ρ Q T → ⊥) →
      Plain S →
      Answerρ Γ ρ (put A v P) (dsend y B S)
  plainOf Γ ρ B y v P S eq nw pl =
    movePut eq
      (sealD pl nw
        (decideValExpr Γ (castV eq v))
        (decideρ Γ (bind y (ixOf (applyTy ρ B) (castV eq v)) (shadow y ρ)) P S))

  -- Premises and the walk are arguments. This function matches the
  -- premise data only, so the walk is not unfolded here.
  armBit : {A : Ty} (Γ : Ctx) (ρ : Idx) (y : String) (v : ValExpr A) (P : Proc)
      (B : Ty) (S : Proto) → A ≡ applyTy ρ B →
      (f : String) (x : String) (t : Tag) (ts : List Tag) (R : Ty)
      (arms : List (String × Proto)) →
      Prem (length (tagBit x ∷ t ∷ ts)) f R arms (tagBit x ∷ t ∷ ts) →
      Walk Γ ρ f R arms [] (tagBit x ∷ t ∷ ts) (dsend y B S) (put A v P) →
      splitAt (dsend y B S) ≡ just (f , (tagBit x ∷ t ∷ ts) , R , arms) →
      Plain S →
      Answerρ Γ ρ (put A v P) (dsend y B S)
  armBit Γ ρ y v P B S eq f _ _ _ R arms (p-ready rd) _ sp pl =
    plainOf Γ ρ B y v P S eq (quadReady rd sp) pl
  armBit Γ ρ y v P B S eq f _ _ _ R arms (p-lab _ lb) _ sp pl =
    plainOf Γ ρ B y v P S eq (quadLab lb sp) pl
  armBit Γ ρ y v P B S eq f _ _ _ R arms (p-rows _ _ wr) _ sp pl =
    plainOf Γ ρ B y v P S eq (quadRows wr sp) pl
  armBit Γ ρ y v P B S eq f _ _ _ R arms (p-len _ _ wr ¬len) _ sp pl =
    plainOf Γ ρ B y v P S eq (quadLen ¬len wr sp) pl
  armBit Γ ρ y v P B S eq f x t ts R arms (p-yes rd lb wr len) w sp pl =
    takeWalk w
      (λ nw → plainOf Γ ρ B y v P S eq (quadCast eq nw sp) pl)
      (λ spin pk d →
        yes (dput-wide eq (wt-bit {x = x} {t = t} {ts = ts}) spin sp rd lb wr len pk d))

  armDat : {A : Ty} (Γ : Ctx) (ρ : Idx) (y : String) (v : ValExpr A) (P : Proc)
      (B : Ty) (S : Proto) → A ≡ applyTy ρ B →
      (f : String) (x : String) (cs : List String) (t : Tag) (ts : List Tag) (R : Ty)
      (arms : List (String × Proto)) →
      Prem (length (tagDat x cs ∷ t ∷ ts)) f R arms (tagDat x cs ∷ t ∷ ts) →
      Walk Γ ρ f R arms [] (tagDat x cs ∷ t ∷ ts) (dsend y B S) (put A v P) →
      splitAt (dsend y B S) ≡ just (f , (tagDat x cs ∷ t ∷ ts) , R , arms) →
      Plain S →
      Answerρ Γ ρ (put A v P) (dsend y B S)
  armDat Γ ρ y v P B S eq f _ _ _ _ R arms (p-ready rd) _ sp pl =
    plainOf Γ ρ B y v P S eq (quadReady rd sp) pl
  armDat Γ ρ y v P B S eq f _ _ _ _ R arms (p-lab _ lb) _ sp pl =
    plainOf Γ ρ B y v P S eq (quadLab lb sp) pl
  armDat Γ ρ y v P B S eq f _ _ _ _ R arms (p-rows _ _ wr) _ sp pl =
    plainOf Γ ρ B y v P S eq (quadRows wr sp) pl
  armDat Γ ρ y v P B S eq f _ _ _ _ R arms (p-len _ _ wr ¬len) _ sp pl =
    plainOf Γ ρ B y v P S eq (quadLen ¬len wr sp) pl
  armDat Γ ρ y v P B S eq f x cs t ts R arms (p-yes rd lb wr len) w sp pl =
    takeWalk w
      (λ nw → plainOf Γ ρ B y v P S eq (quadCast eq nw sp) pl)
      (λ spin pk d →
        yes (dput-wide eq (wt-dat {x = x} {cs = cs} {t = t} {ts = ts}) spin sp rd lb wr len pk d))

  armCaseBit : {A : Ty} (Γ : Ctx) (ρ : Idx) (y : String) (v : ValExpr A) (P : Proc)
      (B : Ty) (f : String) (x : String) (t : Tag) (ts : List Tag) (R : Ty)
      (arms : List (String × Proto)) →
      A ≡ applyTy ρ B →
      Prem (length (tagBit x ∷ t ∷ ts)) f R arms (tagBit x ∷ t ∷ ts) →
      Walk Γ ρ f R arms [] (tagBit x ∷ t ∷ ts)
        (dsend y B (pcase (bySplit f (tagBit x ∷ t ∷ ts) R) arms)) (put A v P) →
      Answerρ Γ ρ (put A v P)
        (dsend y B (pcase (bySplit f (tagBit x ∷ t ∷ ts) R) arms))
  armCaseBit Γ ρ y v P B f x t ts R arms eq (p-ready rd) _ =
    noD Γ ρ y v P B f (tagBit x ∷ t ∷ ts) R arms eq
      (quadReady rd (caseSplit y B f (tagBit x ∷ t ∷ ts) R arms))
  armCaseBit Γ ρ y v P B f x t ts R arms eq (p-lab _ lb) _ =
    noD Γ ρ y v P B f (tagBit x ∷ t ∷ ts) R arms eq
      (quadLab lb (caseSplit y B f (tagBit x ∷ t ∷ ts) R arms))
  armCaseBit Γ ρ y v P B f x t ts R arms eq (p-rows _ _ wr) _ =
    noD Γ ρ y v P B f (tagBit x ∷ t ∷ ts) R arms eq
      (quadRows wr (caseSplit y B f (tagBit x ∷ t ∷ ts) R arms))
  armCaseBit Γ ρ y v P B f x t ts R arms eq (p-len _ _ wr ¬len) _ =
    noD Γ ρ y v P B f (tagBit x ∷ t ∷ ts) R arms eq
      (quadLen ¬len wr (caseSplit y B f (tagBit x ∷ t ∷ ts) R arms))
  armCaseBit Γ ρ y v P B f x t ts R arms eq (p-yes rd lb wr len) w =
    takeWalk w
      (λ nw → noD Γ ρ y v P B f (tagBit x ∷ t ∷ ts) R arms eq
        (quadMove nw (caseSplit y B f (tagBit x ∷ t ∷ ts) R arms)))
      (λ spin pk d →
        yes (dput-wide eq (wt-bit {x = x} {t = t} {ts = ts}) spin refl rd lb wr len pk d))

  armCaseDat : {A : Ty} (Γ : Ctx) (ρ : Idx) (y : String) (v : ValExpr A) (P : Proc)
      (B : Ty) (f : String) (x : String) (cs : List String) (t : Tag) (ts : List Tag)
      (R : Ty) (arms : List (String × Proto)) →
      A ≡ applyTy ρ B →
      Prem (length (tagDat x cs ∷ t ∷ ts)) f R arms (tagDat x cs ∷ t ∷ ts) →
      Walk Γ ρ f R arms [] (tagDat x cs ∷ t ∷ ts)
        (dsend y B (pcase (bySplit f (tagDat x cs ∷ t ∷ ts) R) arms)) (put A v P) →
      Answerρ Γ ρ (put A v P)
        (dsend y B (pcase (bySplit f (tagDat x cs ∷ t ∷ ts) R) arms))
  armCaseDat Γ ρ y v P B f x cs t ts R arms eq (p-ready rd) _ =
    noD Γ ρ y v P B f (tagDat x cs ∷ t ∷ ts) R arms eq
      (quadReady rd (caseSplit y B f (tagDat x cs ∷ t ∷ ts) R arms))
  armCaseDat Γ ρ y v P B f x cs t ts R arms eq (p-lab _ lb) _ =
    noD Γ ρ y v P B f (tagDat x cs ∷ t ∷ ts) R arms eq
      (quadLab lb (caseSplit y B f (tagDat x cs ∷ t ∷ ts) R arms))
  armCaseDat Γ ρ y v P B f x cs t ts R arms eq (p-rows _ _ wr) _ =
    noD Γ ρ y v P B f (tagDat x cs ∷ t ∷ ts) R arms eq
      (quadRows wr (caseSplit y B f (tagDat x cs ∷ t ∷ ts) R arms))
  armCaseDat Γ ρ y v P B f x cs t ts R arms eq (p-len _ _ wr ¬len) _ =
    noD Γ ρ y v P B f (tagDat x cs ∷ t ∷ ts) R arms eq
      (quadLen ¬len wr (caseSplit y B f (tagDat x cs ∷ t ∷ ts) R arms))
  armCaseDat Γ ρ y v P B f x cs t ts R arms eq (p-yes rd lb wr len) w =
    takeWalk w
      (λ nw → noD Γ ρ y v P B f (tagDat x cs ∷ t ∷ ts) R arms eq
        (quadMove nw (caseSplit y B f (tagDat x cs ∷ t ∷ ts) R arms)))
      (λ spin pk d →
        yes (dput-wide eq (wt-dat {x = x} {cs = cs} {t = t} {ts = ts}) spin refl rd lb wr len pk d))

  -- The clause builds the walk. `armBit` matches the premises.
  putWidePlain : (Γ : Ctx) (ρ : Idx) (proc : Proc) (proto : Proto)
      {A : Ty} (y : String) (v : ValExpr A) (P : Proc)
      (B : Ty) (S : Proto) → A ≡ applyTy ρ B →
      proc ≡ put A v P → proto ≡ dsend y B S →
      (f : String) (tags : List Tag) (R : Ty) (arms : List (String × Proto)) →
      WTag tags →
      splitAt (dsend y B S) ≡ just (f , tags , R , arms) →
      Plain S →
      Answerρ Γ ρ (put A v P) (dsend y B S)
  putWidePlain Γ ρ proc proto {A = A} y v P B S eq peq seq f _ R arms (wt-bit {x = x} {t = t} {ts = ts}) sp pl =
    armBit Γ ρ y v P B S eq f x t ts R arms
      (premises (length (tagBit x ∷ t ∷ ts)) f R arms (tagBit x ∷ t ∷ ts))
      (castWalk peq seq
        (walkCons Γ ρ f R arms [] (tagBit x) (t ∷ ts) proto proc (moveSplit seq sp)))
      sp pl
  putWidePlain Γ ρ proc proto {A = A} y v P B S eq peq seq f _ R arms (wt-dat {x = x} {cs = cs} {t = t} {ts = ts}) sp pl =
    armDat Γ ρ y v P B S eq f x cs t ts R arms
      (premises (length (tagDat x cs ∷ t ∷ ts)) f R arms (tagDat x cs ∷ t ∷ ts))
      (castWalk peq seq
        (walkCons Γ ρ f R arms [] (tagDat x cs) (t ∷ ts) proto proc (moveSplit seq sp)))
      sp pl

  putWidePlain Γ ρ _ _ y v P B S eq _ _ _ _ _ _ wt-nn sp pl =
    plainOf Γ ρ B y v P S eq (quadNat sp) pl
  putWidePlain Γ ρ _ _ y v P B S eq _ _ _ _ _ _ wt-nd sp pl =
    plainOf Γ ρ B y v P S eq (quadNat sp) pl
  putWidePlain Γ ρ _ _ y v P B S eq _ _ _ _ _ _ wt-nb sp pl =
    plainOf Γ ρ B y v P S eq (quadNat sp) pl

  -- `proc` and `proto` are the put and the dependent send the
  -- decider matched. The walk receives those arguments, so the
  -- continuation is a subterm of the protocol.
  putWideCase : (Γ : Ctx) (ρ : Idx) (proc : Proc) (proto : Proto)
      {A : Ty} (y : String) (v : ValExpr A) (P : Proc)
      (B : Ty) (f : String) (tags : List Tag) (R : Ty) (arms : List (String × Proto)) →
      A ≡ applyTy ρ B →
      proc ≡ put A v P →
      proto ≡ dsend y B (pcase (bySplit f tags R) arms) →
      WTag tags →
      Answerρ Γ ρ (put A v P) (dsend y B (pcase (bySplit f tags R) arms))
  putWideCase Γ ρ proc proto {A = A} y v P B f _ R arms aeq peq seq (wt-bit {x = x} {t = t} {ts = ts}) =
    armCaseBit Γ ρ y v P B f x t ts R arms aeq
      (premises (length (tagBit x ∷ t ∷ ts)) f R arms (tagBit x ∷ t ∷ ts))
      (castWalk peq seq
        (walkCons Γ ρ f R arms [] (tagBit x) (t ∷ ts) proto proc (splitCast seq)))
  putWideCase Γ ρ proc proto {A = A} y v P B f _ R arms aeq peq seq (wt-dat {x = x} {cs = cs} {t = t} {ts = ts}) =
    armCaseDat Γ ρ y v P B f x cs t ts R arms aeq
      (premises (length (tagDat x cs ∷ t ∷ ts)) f R arms (tagDat x cs ∷ t ∷ ts))
      (castWalk peq seq
        (walkCons Γ ρ f R arms [] (tagDat x cs) (t ∷ ts) proto proc (splitCast seq)))

  putWideCase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wt-nn = no notNat
  putWideCase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wt-nd = no notNat
  putWideCase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ wt-nb = no notNat

  exactE : ∀ {Γ ρ y n v P S f tags R arms} →
    wtag tags ≡ nothing →
    splitAt (esend y (nlit n) S) ≡ just (f , tags , R , arms) →
    Dec (ValExprOk Γ v) →
    Dec (Owed Γ v (just (nlit n))) →
    AnswerSend Γ ρ v P (nlit n) S →
    Answerρ Γ ρ (put nat v P) (esend y (nlit n) S)
  exactE _ _ (yes′ vok) (yes′ ow) (yes-send s) = yes (eput-ok vok ow s)
  exactE {y = y} {n = n} {S = S} wt sp (yes′ _) (yes′ _) (no-send ns) = no (λ where
    (eput-ok _ _ s) → ns s
    (eput-wide w _ p _ _ _ _ _ _) →
      just≢nothing (trans (sym (wtag-just w))
        (subst (λ zs → wtag zs ≡ nothing) (splitTags (esend y (nlit n) S) sp p) wt)))
  exactE _ _ (yes′ _) (no′ now) _ = no (λ where
    (eput-ok _ ow _) → now ow
    (eput-wide _ (sp-nat _ _ _ ow _ _) _ _ _ _ _ _ _) → now ow)
  exactE _ _ (no′ nv) _ _ = no (λ where
    (eput-ok vok _ _) → nv vok
    (eput-wide _ (sp-nat _ _ _ _ vok _) _ _ _ _ _ _ _) → nv vok)

  joinE : ∀ {Γ ρ y n v P S} →
    ValExprOk Γ v →
    Owed Γ v (just (nlit n)) →
    (∀ {tags Q gs f R arms T rows} →
      PutSpine Γ (tagNat y n ∷ tags) (esend y (nlit n) S) (put nat v P) Q gs →
      splitAt (esend y (nlit n) S) ≡ just (f , (tagNat y n ∷ tags) , R , arms) →
      readyN (length (tagNat y n ∷ tags)) f ≡ true →
      labelled R arms ≡ true →
      wideRows f R arms (tagsFac (tagNat y n ∷ tags)) ≡ just rows →
      length rows ≡ prodNs (map facWidth (tagsFac (tagNat y n ∷ tags))) →
      pickRead gs f R arms ≡ just T →
      Conformsρ Γ ρ Q T → ⊥) →
    AnswerSend Γ ρ v P (nlit n) S →
    Answerρ Γ ρ (put nat v P) (esend y (nlit n) S)
  joinE vok ow _ (yes-send s) = yes (eput-ok vok ow s)
  joinE _ _ nw (no-send ns) = no (λ where
    (eput-ok _ _ s) → ns s
    (eput-wide _ spin p rd lb wr len pk c) → nw spin p rd lb wr len pk c)

  putWideGo : (Γ : Ctx) (ρ : Idx) (y : String) (n : ℕ) (v : ValExpr nat) (P : Proc)
      (S : Proto) (f : String) (rest : List Tag) (R : Ty) (arms : List (String × Proto)) →
      WTag (tagNat y n ∷ rest) →
      splitAt (esend y (nlit n) S) ≡ just (f , (tagNat y n ∷ rest) , R , arms) →
      Answerρ Γ ρ (put nat v P) (esend y (nlit n) S)
  putWideGo Γ ρ y n v P S f rest R arms wt sp with decideValExpr Γ v
  ... | no′ nv = no (λ where
        (eput-ok vok _ _) → nv vok
        (eput-wide _ (sp-nat _ _ _ _ vok _) _ _ _ _ _ _ _) → nv vok)
  ... | yes′ vok with owed? Γ v (just (nlit n))
  ... | no′ now = no (λ where
        (eput-ok _ ow _) → now ow
        (eput-wide _ (sp-nat _ _ _ ow _ _) _ _ _ _ _ _ _) → now ow)
  ... | yes′ ow with readyN (length (tagNat y n ∷ rest)) f in rd
  ... | false = joinE vok ow (sendReady rd sp)
        (decideSend Γ ρ v (nlit n) P S)
  ... | true with labelled R arms in lb
  ... | false = joinE vok ow (sendLab lb sp)
        (decideSend Γ ρ v (nlit n) P S)
  ... | true with wideRows f R arms (tagsFac (tagNat y n ∷ rest)) in wr
  ... | nothing = joinE vok ow (sendRows wr sp)
        (decideSend Γ ρ v (nlit n) P S)
  ... | just rows with length rows ≟ℕ prodNs (map facWidth (tagsFac (tagNat y n ∷ rest)))
  ... | no′ ¬len = joinE vok ow (sendLen ¬len wr sp)
        (decideSend Γ ρ v (nlit n) P S)
  ... | yes′ len with walkNat Γ ρ f R arms [] y n rest (esend y (nlit n) S) v P sp
  ... | walk-no nw = joinE vok ow (sendMove nw sp)
        (decideSend Γ ρ v (nlit n) P S)
  ... | walk-yes spin pk d = yes (eput-wide wt spin sp rd lb wr len pk d)

  -- The split found here does not begin with the nat being sent.
  -- The ordinary evidence send is still a derivation. A wide put
  -- would name that nat as its first tag, which this split does not.
  missE : (Γ : Ctx) (ρ : Idx) (y : String) (n : ℕ) (v : ValExpr nat) (P : Proc)
      (S : Proto) →
      (∀ {tags Q gs f R arms T rows} →
        WTag (tagNat y n ∷ tags) →
        PutSpine Γ (tagNat y n ∷ tags) (esend y (nlit n) S) (put nat v P) Q gs →
        splitAt (esend y (nlit n) S) ≡ just (f , (tagNat y n ∷ tags) , R , arms) →
        readyN (length (tagNat y n ∷ tags)) f ≡ true →
        labelled R arms ≡ true →
        wideRows f R arms (tagsFac (tagNat y n ∷ tags)) ≡ just rows →
        length rows ≡ prodNs (map facWidth (tagsFac (tagNat y n ∷ tags))) →
        pickRead gs f R arms ≡ just T →
        Conformsρ Γ ρ Q T → ⊥) →
      Answerρ Γ ρ (put nat v P) (esend y (nlit n) S)
  missE Γ ρ y n v P S nw with decideValExpr Γ v
  ... | no′ nv = no (λ where
        (eput-ok vok _ _) → nv vok
        (eput-wide _ (sp-nat _ _ _ _ vok _) _ _ _ _ _ _ _) → nv vok)
  ... | yes′ vok with owed? Γ v (just (nlit n))
  ... | no′ now = no (λ where
        (eput-ok _ ow _) → now ow
        (eput-wide _ (sp-nat _ _ _ ow _ _) _ _ _ _ _ _ _) → now ow)
  ... | yes′ ow with decideSend Γ ρ v (nlit n) P S
  ... | yes-send s = yes (eput-ok vok ow s)
  ... | no-send ns = no (λ where
        (eput-ok _ _ s) → ns s
        (eput-wide wt spin p rd lb wr len pk c) → nw wt spin p rd lb wr len pk c)

  putWideNat : (Γ : Ctx) (ρ : Idx) (y : String) (n : ℕ) (v : ValExpr nat) (P : Proc)
      (S : Proto) (f : String) (z : String) (m : ℕ) (rest : List Tag) (R : Ty)
      (arms : List (String × Proto)) →
      WTag (tagNat z m ∷ rest) →
      splitAt (esend y (nlit n) S) ≡ just (f , (tagNat z m ∷ rest) , R , arms) →
      Answerρ Γ ρ (put nat v P) (esend y (nlit n) S)
  putWideNat Γ ρ y n v P S f z m rest R arms wt sp with z ≟ y
  ... | no′ ¬z = missE Γ ρ y n v P S (λ _ _ p _ _ _ _ _ _ →
        ¬z (sym (proj₁ (tagNat-inj (proj₁ (cons-inj (splitTags (esend y (nlit n) S) p sp)))))))
  ... | yes′ refl with m ≟ℕ n
  ... | no′ ¬m = missE Γ ρ y n v P S (λ _ _ p _ _ _ _ _ _ →
        ¬m (sym (proj₂ (tagNat-inj (proj₁ (cons-inj (splitTags (esend y (nlit n) S) p sp)))))))
  ... | yes′ refl = putWideGo Γ ρ y n v P S f rest R arms wt sp

  putWideE : (Γ : Ctx) (ρ : Idx) (y : String) (n : ℕ) (v : ValExpr nat) (P : Proc)
      (S : Proto) (f : String) (tags : List Tag) (R : Ty) (arms : List (String × Proto)) →
      WTag tags →
      splitAt (esend y (nlit n) S) ≡ just (f , tags , R , arms) →
      Answerρ Γ ρ (put nat v P) (esend y (nlit n) S)
  putWideE Γ ρ y n v P S f tags R arms wt sp with tags
  ... | [] = missE Γ ρ y n v P S (λ w _ p _ _ _ _ _ _ →
        wtag-nil (subst WTag (splitTags (esend y (nlit n) S) p sp) w))
  ... | _ ∷ [] = missE Γ ρ y n v P S (λ w _ p _ _ _ _ _ _ →
        wtag-one (subst WTag (splitTags (esend y (nlit n) S) p sp) w))
  ... | tagBit _ ∷ _ ∷ _ = missE Γ ρ y n v P S (λ _ _ p _ _ _ _ _ _ →
        badBit (splitTags (esend y (nlit n) S) p sp))
  ... | tagDat _ _ ∷ _ ∷ _ = missE Γ ρ y n v P S (λ _ _ p _ _ _ _ _ _ →
        badDat (splitTags (esend y (nlit n) S) p sp))
  ... | tagNat z m ∷ rest = putWideNat Γ ρ y n v P S f z m rest R arms wt sp

  coverNil : (Γ : Ctx) (ρ : Idx) (rows : List (List String × Proto)) (P : Proc) →
    AnswerW Γ ρ [] rows P
  coverNil Γ ρ rows P with sameRows rows in sr
  ... | nothing = no-w (λ { (wc-same eq _) → just≢nothing (trans (sym eq) sr) })
  ... | just S with decideρ Γ ρ P S
  ... | yes d = yes-w (wc-same sr d)
  ... | no nd = no-w (λ { (wc-same eq c) →
        nd (subst (λ T → Conformsρ Γ ρ P T) (just-inj (trans (sym eq) sr)) c) })

  coverPlain : (Γ : Ctx) (ρ : Idx) (ts : List Tag) (rows : List (List String × Proto))
      (P : Proc) → NotMatch P → AnswerW Γ ρ ts rows P
  coverPlain Γ ρ ts rows P nm with sameRows rows in sr
  ... | nothing = no-w (λ cov →
        let _ , eq , _ = openCover nm cov in just≢nothing (trans (sym eq) sr))
  ... | just S with decideρ Γ ρ P S
  ... | yes d = yes-w (wc-same sr d)
  ... | no nd = no-w (λ cov →
        let _ , eq , c = openCover nm cov in
        nd (subst (λ T → Conformsρ Γ ρ P T) (just-inj (trans (sym eq) sr)) c))

  natSame : (Γ : Ctx) (ρ : Idx) (a : String) (w : ℕ) (ts : List Tag)
      (rows : List (List String × Proto)) (A : Ty) (x : String) (ps : List PArm) →
      (A ≡ nat → a ≡ x → WArms Γ ρ nat (natArms w) ts rows ps → ⊥) →
      (∀ {cs} → a ≡ x → payCtors A ≡ just cs → natArms w ≡ cs →
         WArms Γ ρ A cs ts rows ps → ⊥) →
      AnswerW Γ ρ (tagNat a w ∷ ts) rows (mget A x ps)
  natSame Γ ρ a w ts rows A x ps nn np with sameRows rows in sr
  ... | nothing = no-w (λ where
        (wc-nat q cov) → nn refl q cov
        (wc-pay q p l cov) → np q p l cov
        (wc-same eq _) → just≢nothing (trans (sym eq) sr))
  ... | just S with matchAnswer Γ ρ A x ps S
  ... | yes d = yes-w (wc-same sr d)
  ... | no nd = no-w (λ where
        (wc-nat q cov) → nn refl q cov
        (wc-pay q p l cov) → np q p l cov
        (wc-same eq c) →
          nd (subst (λ T → Conformsρ Γ ρ (mget A x ps) T) (just-inj (trans (sym eq) sr)) c))

  coverNat : (Γ : Ctx) (ρ : Idx) (a : String) (w : ℕ) (ts : List Tag)
      (rows : List (List String × Proto)) (A : Ty) (x : String) (ps : List PArm) →
      AnswerW Γ ρ (tagNat a w ∷ ts) rows (mget A x ps)
  coverNat Γ ρ a w ts rows A x ps with a ≟ x
  ... | no′ ¬a = natSame Γ ρ a w ts rows A x ps
        (λ _ q _ → ¬a q) (λ q _ _ _ → ¬a q)
  ... | yes′ refl with ty≟ A nat
  ... | yes′ refl with armsDec Γ ρ nat (natArms w) ts rows ps
  ... | yes-wa cov = yes-w (wc-nat refl cov)
  ... | no-wa nw = natSame Γ ρ a w ts rows nat x ps
        (λ _ _ cov → nw cov)
        (λ _ p _ _ → just≢nothing (sym p))
  coverNat Γ ρ a w ts rows A x ps | yes′ refl | no′ ¬nat with payCtors A in ep
  ... | nothing = natSame Γ ρ a w ts rows A x ps
        (λ eq _ _ → ¬nat eq) (λ _ p _ _ → just≢nothing (trans (sym p) ep))
  ... | just ds with list≟ (natArms w) ds
  ... | no′ ¬cs = natSame Γ ρ a w ts rows A x ps
        (λ eq _ _ → ¬nat eq)
        (λ _ p l _ → ¬cs (trans l (sym (just-inj (trans (sym ep) p)))))
  ... | yes′ refl with armsDec Γ ρ A ds ts rows ps
  ... | yes-wa cov = yes-w (wc-pay refl ep refl cov)
  ... | no-wa nw = natSame Γ ρ a w ts rows A x ps
        (λ eq _ _ → ¬nat eq)
        (λ _ _ l cov → nw (subst (λ zs → WArms Γ ρ A zs ts rows ps) (sym l) cov))

  paySame : (Γ : Ctx) (ρ : Idx) (t : Tag) (ts : List Tag)
      (rows : List (List String × Proto)) (A : Ty) (x : String) (ps : List PArm) →
      (∀ {a w} → t ≡ tagNat a w → A ≡ nat → a ≡ x →
         WArms Γ ρ nat (natArms w) ts rows ps → ⊥) →
      (∀ {cs} → tagName t ≡ x → payCtors A ≡ just cs → tagLabs t ≡ cs →
         WArms Γ ρ A cs ts rows ps → ⊥) →
      AnswerW Γ ρ (t ∷ ts) rows (mget A x ps)
  paySame Γ ρ t ts rows A x ps nn np with sameRows rows in sr
  ... | nothing = no-w (λ where
        (wc-nat q cov) → nn refl refl q cov
        (wc-pay q p l cov) → np q p l cov
        (wc-same eq _) → just≢nothing (trans (sym eq) sr))
  ... | just S with matchAnswer Γ ρ A x ps S
  ... | yes d = yes-w (wc-same sr d)
  ... | no nd = no-w (λ where
        (wc-nat q cov) → nn refl refl q cov
        (wc-pay q p l cov) → np q p l cov
        (wc-same eq c) →
          nd (subst (λ T → Conformsρ Γ ρ (mget A x ps) T) (just-inj (trans (sym eq) sr)) c))

  coverBit : (Γ : Ctx) (ρ : Idx) (b : String) (ts : List Tag)
      (rows : List (List String × Proto)) (A : Ty) (x : String) (ps : List PArm) →
      AnswerW Γ ρ (tagBit b ∷ ts) rows (mget A x ps)
  coverBit Γ ρ b ts rows A x ps with b ≟ x
  ... | no′ ¬b = paySame Γ ρ (tagBit b) ts rows A x ps
        (λ eq _ _ _ → tagBit≢Nat eq) (λ q _ _ _ → ¬b q)
  ... | yes′ refl with payCtors A in ep
  ... | nothing = paySame Γ ρ (tagBit b) ts rows A x ps
        (λ eq _ _ _ → tagBit≢Nat eq)
        (λ _ p _ _ → just≢nothing (trans (sym p) ep))
  ... | just ds with list≟ (tagLabs (tagBit b)) ds
  ... | no′ ¬cs = paySame Γ ρ (tagBit b) ts rows A x ps
        (λ eq _ _ _ → tagBit≢Nat eq)
        (λ _ p l _ → ¬cs (trans l (sym (just-inj (trans (sym ep) p)))))
  ... | yes′ refl with armsDec Γ ρ A ds ts rows ps
  ... | yes-wa cov = yes-w (wc-pay refl ep refl cov)
  ... | no-wa nw = paySame Γ ρ (tagBit b) ts rows A x ps
        (λ eq _ _ _ → tagBit≢Nat eq)
        (λ _ _ l cov → nw (subst (λ zs → WArms Γ ρ A zs ts rows ps) (sym l) cov))

  coverDat : (Γ : Ctx) (ρ : Idx) (b : String) (cs : List String) (ts : List Tag)
      (rows : List (List String × Proto)) (A : Ty) (x : String) (ps : List PArm) →
      AnswerW Γ ρ (tagDat b cs ∷ ts) rows (mget A x ps)
  coverDat Γ ρ b cs ts rows A x ps with b ≟ x
  ... | no′ ¬b = paySame Γ ρ (tagDat b cs) ts rows A x ps
        (λ eq _ _ _ → tagDat≢Nat eq) (λ q _ _ _ → ¬b q)
  ... | yes′ refl with payCtors A in ep
  ... | nothing = paySame Γ ρ (tagDat b cs) ts rows A x ps
        (λ eq _ _ _ → tagDat≢Nat eq)
        (λ _ p _ _ → just≢nothing (trans (sym p) ep))
  ... | just ds with list≟ (tagLabs (tagDat b cs)) ds
  ... | no′ ¬labs = paySame Γ ρ (tagDat b cs) ts rows A x ps
        (λ eq _ _ _ → tagDat≢Nat eq)
        (λ _ p l _ → ¬labs (trans l (sym (just-inj (trans (sym ep) p)))))
  ... | yes′ refl with armsDec Γ ρ A ds ts rows ps
  ... | yes-wa cov = yes-w (wc-pay refl ep refl cov)
  ... | no-wa nw = paySame Γ ρ (tagDat b cs) ts rows A x ps
        (λ eq _ _ _ → tagDat≢Nat eq)
        (λ _ _ l cov → nw (subst (λ zs → WArms Γ ρ A zs ts rows ps) (sym l) cov))

  coverDec : (Γ : Ctx) (ρ : Idx) (ts : List Tag) (rows : List (List String × Proto))
      (P : Proc) → AnswerW Γ ρ ts rows P
  coverDec Γ ρ [] rows P = coverNil Γ ρ rows P
  coverDec Γ ρ (t ∷ ts) rows done = coverPlain Γ ρ (t ∷ ts) rows done nm-done
  coverDec Γ ρ (t ∷ ts) rows stop = coverPlain Γ ρ (t ∷ ts) rows stop nm-stop
  coverDec Γ ρ (t ∷ ts) rows (put A v P) = coverPlain Γ ρ (t ∷ ts) rows (put A v P) nm-put
  coverDec Γ ρ (t ∷ ts) rows (get A x P) = coverPlain Γ ρ (t ∷ ts) rows (get A x P) nm-get
  coverDec Γ ρ (t ∷ ts) rows (pick0 P) = coverPlain Γ ρ (t ∷ ts) rows (pick0 P) nm-pick0
  coverDec Γ ρ (t ∷ ts) rows (pick1 P) = coverPlain Γ ρ (t ∷ ts) rows (pick1 P) nm-pick1
  coverDec Γ ρ (t ∷ ts) rows (cover P Q) = coverPlain Γ ρ (t ∷ ts) rows (cover P Q) nm-cover
  coverDec Γ ρ (t ∷ ts) rows (iget x P Q) = coverPlain Γ ρ (t ∷ ts) rows (iget x P Q) nm-iget
  coverDec Γ ρ (tagNat a w ∷ ts) rows (mget A x ps) = coverNat Γ ρ a w ts rows A x ps
  coverDec Γ ρ (tagBit b ∷ ts) rows (mget A x ps) = coverBit Γ ρ b ts rows A x ps
  coverDec Γ ρ (tagDat b cs ∷ ts) rows (mget A x ps) = coverDat Γ ρ b cs ts rows A x ps

  useBareW : ∀ {Γ ρ A lab labs ts rows p ps} →
    AnswerW Γ ρ ts (keepLab lab rows) p →
    AnswerWA Γ ρ A labs ts rows ps →
    AnswerWA Γ ρ A (lab ∷ labs) ts rows (bare p ∷ ps)
  useBareW (yes-w c) (yes-wa rest) = yes-wa (wa-bare c rest)
  useBareW (no-w nc) _ = no-wa (λ { (wa-bare c _) → nc c })
  useBareW (yes-w _) (no-wa nr) = no-wa (λ { (wa-bare _ rest) → nr rest })

  useNamedW : ∀ {Γ ρ A c xs lab labs ts rows p ps Δ} →
    c ≡ lab →
    armCtxNamed A c xs Γ ≡ just Δ →
    AnswerW Δ ρ ts (keepLab lab rows) p →
    AnswerWA Γ ρ A labs ts rows ps →
    AnswerWA Γ ρ A (lab ∷ labs) ts rows (named c xs p ∷ ps)
  useNamedW eq ac (yes-w cov) (yes-wa rest) = yes-wa (wa-named eq ac cov rest)
  useNamedW {ρ = ρ} {lab = lab} {ts = ts} {rows = rows} {p = p} {Δ = Δ} _ ac (no-w nc) _ =
    no-wa (λ { (wa-named _ q cov _) →
      nc (subst (λ Θ → WCover Θ ρ ts (keepLab lab rows) p)
            (just-inj (trans (sym q) ac)) cov) })
  useNamedW _ _ (yes-w _) (no-wa nr) = no-wa (λ { (wa-named _ _ _ rest) → nr rest })

  armsDec : (Γ : Ctx) (ρ : Idx) (A : Ty) (labs : List String) (ts : List Tag)
      (rows : List (List String × Proto)) (ps : List PArm) →
      AnswerWA Γ ρ A labs ts rows ps
  armsDec _ _ _ [] _ _ [] = yes-wa wa-nil
  armsDec _ _ _ [] _ _ (_ ∷ _) = no-wa (λ ())
  armsDec _ _ _ (_ ∷ _) _ _ [] = no-wa (λ ())
  armsDec Γ ρ A (lab ∷ labs) ts rows (bare p ∷ ps) =
    useBareW (coverDec Γ ρ ts (keepLab lab rows) p) (armsDec Γ ρ A labs ts rows ps)
  armsDec Γ ρ A (lab ∷ labs) ts rows (named c xs p ∷ ps) with nameView A c lab xs Γ
  ... | nv-neq neq = no-wa (λ { (wa-named q _ _ _) → neq q })
  ... | nv-none ac refl = no-wa (λ { (wa-named _ q _ _) → just≢nothing (trans (sym q) ac) })
  ... | nv-just Δ ac refl =
      useNamedW refl ac (coverDec Δ ρ ts (keepLab lab rows) p) (armsDec Γ ρ A labs ts rows ps)
  armsDec _ _ _ (_ ∷ _) _ _ (prod _ _ ∷ _) = no-wa (λ ())
  armsDec _ _ _ (_ ∷ _) _ _ (fork _ _ _ _ ∷ _) = no-wa (λ ())

  -- A value case selects one arm. `splitAt` of `byVal` and `byRun` is
  -- nothing, so a wide spine does not apply. The proof is passed in
  -- because the scrutinee is a parameter.
  sendCase : (Γ : Ctx) (ρ : Idx) {A : Ty} (y : String) (v : ValExpr A) (P : Proc)
      (B : Ty) (scrut : Scrut) (arms : List (String × Proto)) →
      A ≡ applyTy ρ B →
      splitAt (dsend y B (pcase scrut arms)) ≡ nothing →
      Answerρ Γ ρ (put A v P) (dsend y B (pcase scrut arms))
  sendCase Γ ρ {A} y v P B scrut arms refl sp
      with selectProto y v scrut arms in eq
  ... | nothing = no (λ where
        (dput-ok _ _ pl _) → plain-not pl
        (dput-arm _ _ p _) → just≢nothing (trans (sym p) eq)
        (dput-wide _ _ _ q _ _ _ _ _ _) → just≢nothing (trans (sym q) sp))
  ... | just T with decideValExpr Γ v
  ... | no′ nv = no (λ where
        (dput-ok _ vok _ _) → nv vok
        (dput-arm _ vok _ _) → nv vok
        (dput-wide _ _ _ q _ _ _ _ _ _) → just≢nothing (trans (sym q) sp))
  ... | yes′ vok with decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P T
  ... | yes d = yes (dput-arm refl vok eq d)
  ... | no nd = no (λ where
        (dput-ok _ _ pl _) → plain-not pl
        (dput-arm _ _ p d) →
          nd (subst (λ S → Conformsρ Γ (bind y (ixOf A v) (shadow y ρ)) P S)
                (just-inj (trans (sym p) eq)) d)
        (dput-wide _ _ _ q _ _ _ _ _ _) → just≢nothing (trans (sym q) sp))

  -- A plain continuation. A wide product whose case sits further down
  -- the spine is decided here. An exact two-factor list is not wide,
  -- so that put stays `dput-ok` and the product is decided on the
  -- evidence send.
  sendNest : (Γ : Ctx) (ρ : Idx) (proc : Proc) (proto : Proto)
      {A : Ty} (y : String) (v : ValExpr A) (P : Proc)
      (B : Ty) (S : Proto) →
      proc ≡ put A v P → proto ≡ dsend y B S →
      A ≡ applyTy ρ B → Plain S →
      Answerρ Γ ρ (put A v P) (dsend y B S)
  sendNest Γ ρ proc proto {A} y v P B S peq seq refl pl =
    onNest Γ ρ proc proto y v P B S peq seq refl pl (plainView (dsend y B S))

  onNest : (Γ : Ctx) (ρ : Idx) (proc : Proc) (proto : Proto)
      {A : Ty} (y : String) (v : ValExpr A) (P : Proc)
      (B : Ty) (S : Proto) →
      proc ≡ put A v P → proto ≡ dsend y B S →
      A ≡ applyTy ρ B → Plain S → PlainView (dsend y B S) →
      Answerρ Γ ρ (put A v P) (dsend y B S)
  onNest Γ ρ proc proto {A} y v P B S peq seq refl pl (pv-none sp) =
    on-dput pl sp (decideValExpr Γ v)
      (decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P S)
  onNest Γ ρ proc proto {A} y v P B S peq seq refl pl (pv-seal f tags R arms sp wt) =
    sealD pl
      (λ w _ p _ _ _ _ _ _ →
        just≢nothing (trans (sym (wtag-just w))
          (subst (λ zs → wtag zs ≡ nothing) (splitTags (dsend y B S) sp p) wt)))
      (decideValExpr Γ v)
      (decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P S)
  onNest Γ ρ proc proto {A} y v P B S peq seq refl pl (pv-wide f tags R arms w sp) =
    putWidePlain Γ ρ proc proto y v P B S refl peq seq f tags R arms w sp pl

  -- The process and the protocol stay the arguments matched above.
  -- Dispatch reads the continuation. It does not rebuild the put.
  sendBy : (Γ : Ctx) (ρ : Idx) {A : Ty} (y : String) (v : ValExpr A) (P : Proc)
      (B : Ty) (S : Proto) (proc : Proc) (proto : Proto) →
      proc ≡ put A v P → proto ≡ dsend y B S →
      Answerρ Γ ρ proc proto
  sendBy Γ ρ {A = A} y v P B S proc proto refl refl =
    dispatchSend Γ ρ y v P B S proc proto refl refl (ty≟ A (applyTy ρ B))

  dispatchSend : (Γ : Ctx) (ρ : Idx) {A : Ty} (y : String) (v : ValExpr A) (P : Proc)
      (B : Ty) (S : Proto) (proc : Proc) (proto : Proto) →
      proc ≡ put A v P → proto ≡ dsend y B S →
      Dec (A ≡ applyTy ρ B) →
      Answerρ Γ ρ proc proto
  dispatchSend Γ ρ y v P B (pcase (byVal z) arms) proc proto peq seq (yes′ refl) =
    castAns peq seq (sendCase Γ ρ y v P B (byVal z) arms refl refl)
  dispatchSend Γ ρ y v P B (pcase (byRun f z R) arms) proc proto peq seq (yes′ refl) =
    castAns peq seq (sendCase Γ ρ y v P B (byRun f z R) arms refl refl)
  dispatchSend Γ ρ y v P B (pcase (bySplit f tags R) arms) proc proto peq seq (yes′ refl)
      with wtag tags in wt
  ... | nothing = castAns peq seq (no (no-split-put wt))
  ... | just w =
      castAns peq seq
        (putWideCase Γ ρ proc proto y v P B f tags R arms refl peq seq w)
  dispatchSend Γ ρ y v P B S proc proto peq seq (no′ ¬eq) =
    castAns peq seq (no (λ d → ¬eq (dput-type d)))
  dispatchSend Γ ρ y v P B end proc proto peq seq (yes′ refl) =
    castAns peq seq (sendNest Γ ρ proc proto y v P B end peq seq refl plain-end)
  dispatchSend Γ ρ y v P B (send C S) proc proto peq seq (yes′ refl) =
    castAns peq seq (sendNest Γ ρ proc proto y v P B (send C S) peq seq refl plain-send)
  dispatchSend Γ ρ y v P B (recv C S) proc proto peq seq (yes′ refl) =
    castAns peq seq (sendNest Γ ρ proc proto y v P B (recv C S) peq seq refl plain-recv)
  dispatchSend Γ ρ y v P B (dsend z C S) proc proto peq seq (yes′ refl) =
    castAns peq seq (sendNest Γ ρ proc proto y v P B (dsend z C S) peq seq refl plain-dsend)
  dispatchSend Γ ρ y v P B (drecv z C S) proc proto peq seq (yes′ refl) =
    castAns peq seq (sendNest Γ ρ proc proto y v P B (drecv z C S) peq seq refl plain-drecv)
  dispatchSend Γ ρ y v P B (esend z e S) proc proto peq seq (yes′ refl) =
    castAns peq seq (sendNest Γ ρ proc proto y v P B (esend z e S) peq seq refl plain-esend)
  dispatchSend Γ ρ y v P B (erecv z e S) proc proto peq seq (yes′ refl) =
    castAns peq seq (sendNest Γ ρ proc proto y v P B (erecv z e S) peq seq refl plain-erecv)
  dispatchSend Γ ρ y v P B (isend z S T) proc proto peq seq (yes′ refl) =
    castAns peq seq (sendNest Γ ρ proc proto y v P B (isend z S T) peq seq refl plain-isend)
  dispatchSend Γ ρ y v P B (irecv z S T) proc proto peq seq (yes′ refl) =
    castAns peq seq (sendNest Γ ρ proc proto y v P B (irecv z S T) peq seq refl plain-irecv)
  dispatchSend Γ ρ y v P B (choose S T) proc proto peq seq (yes′ refl) =
    castAns peq seq (sendNest Γ ρ proc proto y v P B (choose S T) peq seq refl plain-choose)
  dispatchSend Γ ρ y v P B (branch S T) proc proto peq seq (yes′ refl) =
    castAns peq seq (sendNest Γ ρ proc proto y v P B (branch S T) peq seq refl plain-branch)

decide : (Γ : Ctx) (P : Proc) (S : Proto) → Answer Γ P S
decide Γ P S = decideρ Γ none P S

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  pong-decides : decide [] pong ping ≡ yes pong-ok
  pong-decides = refl

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  other-nat-decides : decide [] (get nat "x" (put nat (lit zero) done)) ping ≡ yes other-nat
  other-nat-decides = refl

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  v-here-decides : decide [] (put box (lit v-here) done) (send box end) ≡ yes v-here-ok
  v-here-decides = refl

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
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

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  inner-decides : decide [] (get nat "v" (get bit "v" (put bit (var "v") done))) (recv nat (recv bit (send bit end))) ≡ yes inner
  inner-decides = refl

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  shadowed-decides : decide [] shadowed (recv nat (recv bit (send nat end))) ≡ no shadowed-refused
  shadowed-decides = refl

left-open : Conforms [] (put nat (lit zero) stop) (send nat (send nat end))
left-open = put-ok refl (lit-ok refl) abandon

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  left-open-decides : decide [] (put nat (lit zero) stop) (send nat (send nat end)) ≡ yes left-open
  left-open-decides = refl

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  untouched-decides : decide [] stop (send nat end) ≡ yes untouched
  untouched-decides = refl

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  chosen-decides : decide [] (pick0 done) (choose end (send nat end)) ≡ yes chosen
  chosen-decides = refl

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
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
sized-server-ok = dget-ok refl (put-ok refl (lit-ok refl) done-end)

sized-client-ok : Conforms [] sized-client (dsend "n" nat (recv (vec nat (nvar "n")) end))
sized-client-ok = dput-ok refl (lit-ok refl) plain-recv (get-ok refl done-end)

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  sized-server-decides : decide [] sized-server sized ≡ yes sized-server-ok
  sized-server-decides = refl

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  sized-client-decides : decide [] sized-client (dsend "n" nat (recv (vec nat (nvar "n")) end)) ≡ yes sized-client-ok
  sized-client-decides = refl

len-three : NExp
len-three = nlit (nsuc (nsuc (nsuc nzero)))

sized-bad : Proc
sized-bad = put nat (lit two) (get (vec nat len-three) "_" done)

sized-mismatch : ¬ Conforms [] sized-bad (dsend "n" nat (recv (vec nat (nvar "n")) end))
sized-mismatch (dput-ok refl _ _ (get-ok () _))

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

num-fits : ∀ k → fits (num k) ≡ true
num-fits nzero = refl
num-fits (nsuc k) = num-fits k

==-refl : ∀ s → (s == s) ≡ true
==-refl s with s ≟ s
... | yes′ refl = refl
... | no′ ¬eq = ⊥-elim (¬eq refl)

-- `armGo` is the covering walk. `natGo` is the walk a meeting takes.
armGo-num : ∀ k ps i → armGo k ps i ≡ natGo (num k) ps i
armGo-num nzero [] _ = refl
armGo-num nzero (bare _ ∷ _) _ = refl
armGo-num nzero (named _ [] _ ∷ _) _ = refl
armGo-num nzero (named _ (_ ∷ _) _ ∷ _) _ = refl
armGo-num nzero (prod _ _ ∷ _) _ = refl
armGo-num nzero (fork _ _ _ _ ∷ _) _ = refl
armGo-num (nsuc _) [] _ = refl
armGo-num (nsuc k) (_ ∷ ps) i = armGo-num k ps (nsuc i)

-- A process that covers the numeral arms conforms at every numeral
-- whose label is the arm it selects. `i` is the index the walk has
-- already passed.
val-sound : ∀ {Γ ρ} k i (arms : List (String × Proto)) (ps : List PArm) {S p} →
  ArmsAt Γ ρ nat arms ps →
  nth arms k ≡ just (show (i + k) , S) →
  armGo k ps i ≡ just p →
  Conformsρ Γ ρ p S
val-sound _ _ [] _ _ () _
val-sound _ _ (_ ∷ _) [] () _ _
val-sound _ _ (_ ∷ _) (prod _ _ ∷ _) () _ _
val-sound _ _ (_ ∷ _) (fork _ _ _ _ ∷ _) () _ _
val-sound nzero i ((._ , S) ∷ _) (bare p ∷ _) (at-cons d _) refl refl = d
val-sound {Γ} {ρ} nzero i ((c , S) ∷ _) (named .c [] p ∷ _) (at-named ac d _) eq ag
  rewrite +-identityʳ i with eq
... | refl rewrite ==-refl c =
    subst (λ q → Conformsρ Γ ρ q S) (just-inj ag)
      (subst (λ Θ → Conformsρ Θ ρ p S) (sym (just-inj ac)) d)
val-sound nzero _ (_ ∷ _) (named _ (_ ∷ _) _ ∷ _) _ _ ()
val-sound (nsuc k) i (_ ∷ as) (_ ∷ ps) (at-cons _ rest) eq ag
  rewrite +-suc i k = val-sound k (nsuc i) as ps rest eq ag
val-sound (nsuc k) i (_ ∷ as) (_ ∷ ps) (at-named _ _ rest) eq ag
  rewrite +-suc i k = val-sound k (nsuc i) as ps rest eq ag

-- The same fact for the rows a run returns. A named row binds nothing.
rows-at : ∀ {Γ ρ} k i (rows : List (String × Proto)) (ps : List PArm) {S p} →
  CovNat Γ ρ rows ps →
  nth rows k ≡ just (show (i + k) , S) →
  armGo k ps i ≡ just p →
  Conformsρ Γ ρ p S
rows-at _ _ [] _ _ () _
rows-at _ _ (_ ∷ _) [] () _ _
rows-at _ _ (_ ∷ _) (prod _ _ ∷ _) () _ _
rows-at _ _ (_ ∷ _) (fork _ _ _ _ ∷ _) () _ _
rows-at _ _ (_ ∷ _) (named _ (_ ∷ _) _ ∷ _) () _ _
rows-at nzero i ((._ , S) ∷ _) (bare p ∷ _) (cn-bare d _) refl refl = d
rows-at {Γ} {ρ} nzero i ((c , S) ∷ _) (named .c [] p ∷ _) (cn-named d _) eq ag
  rewrite +-identityʳ i with eq
... | refl rewrite ==-refl c = subst (λ q → Conformsρ Γ ρ q S) (just-inj ag) d
rows-at (nsuc k) i (_ ∷ rows) (_ ∷ ps) (cn-bare _ rest) eq ag
  rewrite +-suc i k = rows-at k (nsuc i) rows ps rest eq ag
rows-at (nsuc k) i (_ ∷ rows) (_ ∷ ps) (cn-named _ rest) eq ag
  rewrite +-suc i k = rows-at k (nsuc i) rows ps rest eq ag

-- Bound `1`. Arms `0` then `1`. The receiver covers both.
bound1 : Proto
bound1 = erecv "d" (nlit (nsuc nzero)) (pcase (byVal "d")
  (("0" , end) ∷ ("1" , send nat end) ∷ []))

boundRecv : Proc
boundRecv = mget nat "d" (bare done ∷ bare (put nat (lit zero) done) ∷ [])

bound1-wf : ProtoOk [] bound1
bound1-wf = erecv-val refl
  (arms-one end-ok (arms-one (send-ok nat-ok end-ok) arms-none))

bound-recv-ok : Conforms [] boundRecv bound1
bound-recv-ok = eget-val refl
  (at-cons done-end (at-cons (put-ok refl (lit-ok refl) done-end) at-nil))

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  bound-recv-decides : decide [] boundRecv bound1 ≡ yes bound-recv-ok
  bound-recv-decides = refl

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
full-ok = dget-ok refl (eput-ok (var-ok here) (owed (same-le (first gone))) (send-plain plain-end done-end))

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  full-decides : decide [] full window ≡ yes full-ok
  full-decides = refl

empty : Proc
empty = get nat "w" (put nat (lit zero) done)

empty-ok : Conforms [] empty window
empty-ok = dget-ok refl (eput-ok (lit-ok refl) (owed zero-le) (send-plain plain-end done-end))

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  empty-decides : decide [] empty window ≡ yes empty-ok
  empty-decides = refl

guess : Proc
guess = get nat "w" (put nat (lit two) done)

guess-refused : ¬ Conforms [] guess window
guess-refused (dget-ok refl (eput-ok _ (owed ()) _))

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  guess-decides : decide [] guess window ≡ no guess-refused
  guess-decides = refl

granted : Proto
granted = dsend "w" nat (esend "d" (nvar "w") end)

within : Proc
within = put nat (lit (num 8)) (put nat (lit (num 5)) done)

within-ok : Conforms [] within granted
within-ok =
  dput-ok refl (lit-ok refl) plain-esend
    (eput-ok (lit-ok refl) (owed (lit-le (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) (send-plain plain-end done-end))

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  within-decides : decide [] within granted ≡ yes within-ok
  within-decides = refl

-- `d > w`: nine is not at most eight.
over : Proc
over = put nat (lit (num 8)) (put nat (lit (num 9)) done)

over-refused : ¬ Conforms [] over granted
over-refused
  (dput-ok refl _ _ (eput-ok _ (owed (lit-le (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))))) _))

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  over-decides : decide [] over granted ≡ no over-refused
  over-decides = refl

-- A numeral bound in the protocol.
frame : Proto
frame = esend "d" (nlit 16384) end

frame-ok : Conforms [] (put nat (lit zero) done) frame
frame-ok = eput-ok (lit-ok refl) (owed (lit-le z≤n)) (send-plain plain-end done-end)

-- A second `w` hides the window. The bound still names the first.
stale-proto : Proto
stale-proto = drecv "w" nat (recv nat (esend "d" (nvar "w") end))

stale : Proc
stale = get nat "w" (get nat "w" (put nat (var "w") done))

stale-refused : ¬ Conforms [] stale stale-proto
stale-refused (dget-ok refl (get-ok refl (eput-ok _ (owed (same-le (first (past w≢w _)))) _))) = w≢w refl
stale-refused (dget-ok refl (get-ok refl (eput-ok _ (owed (same-le (later w≢w _))) _))) = w≢w refl

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
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
route-server-ok = iget-ok (put-ok refl (lit-ok refl) done-end) (get-ok refl done-end)

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  route-decides : decide [] route-server route ≡ yes route-server-ok
  route-decides = refl

one-arm : Proc
one-arm = get bit "b" (put nat (lit one) done)

one-arm-refused : ¬ Conforms [] one-arm route
one-arm-refused ()

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  one-arm-decides : decide [] one-arm route ≡ no one-arm-refused
  one-arm-decides = refl

-- The sender writes `b0`. The received name does not select the arm.
route-fwd : Proto
route-fwd = drecv "b" bit (isend "c" end (send nat end))

fwd : Proc
fwd = get bit "b" (put bit (var "b") done)

fwd-refused : ¬ Conforms [] fwd route-fwd
fwd-refused (dget-ok refl ())

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  fwd-decides : decide [] fwd route-fwd ≡ no fwd-refused
  fwd-decides = refl

fwd-lit : Proc
fwd-lit = get bit "b" (put bit (lit b0) done)

fwd-lit-ok : Conforms [] fwd-lit route-fwd
fwd-lit-ok = dget-ok refl (iput0-ok done-end)

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  fwd-lit-decides : decide [] fwd-lit route-fwd ≡ yes fwd-lit-ok
  fwd-lit-decides = refl

route-back : Proto
route-back = isend "b" (recv nat end) (send nat end)

crossed-proc : Proc
crossed-proc = put bit (lit b0) (put nat (lit one) done)

crossed-refused : ¬ Conforms [] crossed-proc route-back
crossed-refused (iput0-ok ())

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  crossed-decides : decide [] crossed-proc route-back ≡ no crossed-refused
  crossed-decides = refl

-- The received bit can be sent later as a bit. It does not select that send.
echo-bit : Proc
echo-bit = iget "b" (put bit (var "b") done) (put bit (var "b") done)

echo-proto : Proto
echo-proto = irecv "b" (send bit end) (send bit end)

echo-bit-ok : Conforms [] echo-bit echo-proto
echo-bit-ok = iget-ok (put-ok refl (var-ok here) done-end) (put-ok refl (var-ok here) done-end)

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
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
  -- The arms of a match. The value that selects one was heard just before.
  pick    : List Skel → Skel

mutual
  skel : Proc → Skel
  skel done = finish
  skel stop = leave
  skel (put _ v P) = say v (skel P)
  skel (get A x P) = hear A x (skel P)
  skel (pick0 P) = choose0 (skel P)
  skel (pick1 P) = choose1 (skel P)
  skel (cover P Q) = offer (skel P) (skel Q)
  skel (iget x P Q) = index x (skel P) (skel Q)
  skel (mget A x ps) = hear A x (pick (skelAll ps))

  skelAll : List PArm → List Skel
  skelAll [] = []
  skelAll (bare p ∷ ps) = skel p ∷ skelAll ps
  skelAll (named _ _ p ∷ ps) = skel p ∷ skelAll ps
  skelAll (prod _ p ∷ ps) = skel p ∷ skelAll ps
  skelAll (fork _ _ _ qs ∷ ps) = pick (skelAll qs) ∷ skelAll ps

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

mutual
  data Ends : Proc → Set where
    ends-done  : Ends done
    ends-put   : ∀ {A v P} → Ends P → Ends (put A v P)
    ends-get   : ∀ {A x P} → Ends P → Ends (get A x P)
    ends-pick0 : ∀ {P} → Ends P → Ends (pick0 P)
    ends-pick1 : ∀ {P} → Ends P → Ends (pick1 P)
    ends-cover : ∀ {P Q} → Ends P → Ends Q → Ends (cover P Q)
    ends-iget  : ∀ {x P Q} → Ends P → Ends Q → Ends (iget x P Q)
    ends-mget  : ∀ {A x ps} → AllEnds ps → Ends (mget A x ps)

  data AllEnds : List PArm → Set where
    ends-nil  : AllEnds []
    ends-cons : ∀ {a ps} → Ends (body a) → AllEnds ps → AllEnds (a ∷ ps)

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

data FinishAll (ps : List PArm) : Set where
  all-ends   : AllEnds ps → FinishAll ps
  all-leaves : ¬ AllEnds ps → FinishAll ps

step-all : ∀ {a ps} → Finish (body a) → FinishAll ps → FinishAll (a ∷ ps)
step-all (ends d) (all-ends e) = all-ends (ends-cons d e)
step-all (leaves nd) _ = all-leaves (λ { (ends-cons d _) → nd d })
step-all (ends _) (all-leaves ne) = all-leaves (λ { (ends-cons _ e) → ne e })

step-mget : ∀ {A x ps} → FinishAll ps → Finish (mget A x ps)
step-mget (all-ends d) = ends (ends-mget d)
step-mget (all-leaves nd) = leaves (λ { (ends-mget d) → nd d })

mutual
  finishes : (P : Proc) → Finish P
  finishes done = ends ends-done
  finishes stop = leaves (λ ())
  finishes (put _ _ P) = step-put (finishes P)
  finishes (get _ _ P) = step-get (finishes P)
  finishes (pick0 P) = step-pick0 (finishes P)
  finishes (pick1 P) = step-pick1 (finishes P)
  finishes (cover P Q) = step-cover (finishes P) (finishes Q)
  finishes (iget x P Q) = step-iget (finishes P) (finishes Q)
  finishes (mget _ _ ps) = step-mget (finishesAll ps)

  finishesAll : (ps : List PArm) → FinishAll ps
  finishesAll [] = all-ends ends-nil
  finishesAll (bare p ∷ ps) = step-all (finishes p) (finishesAll ps)
  finishesAll (named _ _ p ∷ ps) = step-all (finishes p) (finishesAll ps)
  finishesAll (prod _ p ∷ ps) = step-all (finishes p) (finishesAll ps)
  finishesAll (fork _ _ _ qs ∷ ps) =
    step-all (step-mget (finishesAll qs)) (finishesAll ps)

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

mutual
  data NoLeave : Skel → Set where
    finish-ok  : NoLeave finish
    say-ok     : ∀ {A v k} → NoLeave k → NoLeave (say {A} v k)
    hear-ok    : ∀ {A x k} → NoLeave k → NoLeave (hear A x k)
    choose0-ok : ∀ {k} → NoLeave k → NoLeave (choose0 k)
    choose1-ok : ∀ {k} → NoLeave k → NoLeave (choose1 k)
    offer-ok   : ∀ {k q} → NoLeave k → NoLeave q → NoLeave (offer k q)
    index-ok   : ∀ {x k q} → NoLeave k → NoLeave q → NoLeave (index x k q)
    pick-ok    : ∀ {ks} → AllLeave ks → NoLeave (pick ks)

  data AllLeave : List Skel → Set where
    leave-nil  : AllLeave []
    leave-cons : ∀ {k ks} → NoLeave k → AllLeave ks → AllLeave (k ∷ ks)

mutual
  ends-no-leave : ∀ {P} → Ends P → NoLeave (skel P)
  ends-no-leave ends-done = finish-ok
  ends-no-leave (ends-put e) = say-ok (ends-no-leave e)
  ends-no-leave (ends-get e) = hear-ok (ends-no-leave e)
  ends-no-leave (ends-pick0 e) = choose0-ok (ends-no-leave e)
  ends-no-leave (ends-pick1 e) = choose1-ok (ends-no-leave e)
  ends-no-leave (ends-cover e f) = offer-ok (ends-no-leave e) (ends-no-leave f)
  ends-no-leave (ends-iget e f) = index-ok (ends-no-leave e) (ends-no-leave f)
  ends-no-leave (ends-mget e) = hear-ok (pick-ok (ends-all e))

  ends-all : ∀ {ps} → AllEnds ps → AllLeave (skelAll ps)
  ends-all ends-nil = leave-nil
  ends-all {bare _ ∷ _} (ends-cons e es) = leave-cons (ends-no-leave e) (ends-all es)
  ends-all {named _ _ _ ∷ _} (ends-cons e es) = leave-cons (ends-no-leave e) (ends-all es)
  ends-all {prod _ _ ∷ _} (ends-cons e es) = leave-cons (ends-no-leave e) (ends-all es)
  ends-all {fork _ _ _ _ ∷ _} (ends-cons (ends-mget e) es) =
    leave-cons (pick-ok (ends-all e)) (ends-all es)

------------------------------------------------------------------------
-- A declared data type is a payload. The constructors are the ones
-- the declaration has. A constructor it does not have does not
-- inhabit the type, and neither does a field of the wrong type.
------------------------------------------------------------------------

flag : Proto
flag = send boolTy end

up : Proc
up = put boolTy (lit trueV) done

up-ok : Conforms [] up flag
up-ok = put-ok refl (lit-ok refl) done-end

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  up-decides : decide [] up flag ≡ yes up-ok
  up-decides = refl

bad-bool : ¬ Conforms [] (put boolTy (lit noneV) done) flag
bad-bool (put-ok refl (lit-ok ()) _)

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  bad-bool-decides : decide [] (put boolTy (lit noneV) done) flag ≡ no bad-bool
  bad-bool-decides = refl

bool-formed : TyOk [] boolTy
bool-formed = dat-ok refl tys-nil (ctors-cons flds-nil (ctors-cons flds-nil ctors-nil))

opt : Proto
opt = send maybeNat end

opt-ok : Conforms [] (put maybeNat (lit just0) done) opt
opt-ok = put-ok refl (lit-ok refl) done-end

opt-none : Conforms [] (put maybeNat (lit nothingV) done) opt
opt-none = put-ok refl (lit-ok refl) done-end

bad-maybe : ¬ Conforms [] (put maybeNat (lit justBit) done) opt
bad-maybe (put-ok refl (lit-ok ()) _)

maybe-formed : TyOk [] maybeNat
maybe-formed =
  dat-ok refl (tys-cons nat-ok tys-nil)
    (ctors-cons flds-nil
      (ctors-cons (flds-cons (ff-par refl nat-ok) flds-nil) ctors-nil))

listDecl : Decl
listDecl = mkDecl "List" (nsuc nzero)
  (ctor "nil" [] ∷ ctor "cons" (fPar nzero ∷ fSelf (fPar nzero ∷ []) ∷ []) ∷ [])

listNat : Ty
listNat = dat listDecl (nat ∷ [])

nilV : Val listNat
nilV = con "nil" snil

consV : Val listNat
consV = con "cons" (scons nat zero (scons listNat nilV snil))

list-ok : Conforms [] (put listNat (lit nilV) done) (send listNat end)
list-ok = put-ok refl (lit-ok refl) done-end

list-cons-ok : Conforms [] (put listNat (lit consV) done) (send listNat end)
list-cons-ok = put-ok refl (lit-ok refl) done-end

list-formed : TyOk [] listNat
list-formed =
  dat-ok refl (tys-cons nat-ok tys-nil)
    (ctors-cons flds-nil
      (ctors-cons
        (flds-cons (ff-par refl nat-ok)
          (flds-cons (ff-self refl (flds-cons (ff-par refl nat-ok) flds-nil)) flds-nil))
        ctors-nil))

eitherDecl : Decl
eitherDecl = mkDecl "Either" (nsuc (nsuc nzero))
  (ctor "left" (fPar nzero ∷ []) ∷ ctor "right" (fPar (nsuc nzero) ∷ []) ∷ [])

eitherNB : Ty
eitherNB = dat eitherDecl (nat ∷ bit ∷ [])

left0 : Val eitherNB
left0 = con "left" (scons nat zero snil)

rightB : Val eitherNB
rightB = con "right" (scons bit b0 snil)

badRight : Val eitherNB
badRight = con "right" (scons nat zero snil)

either-ok : Conforms [] (put eitherNB (lit left0) done) (send eitherNB end)
either-ok = put-ok refl (lit-ok refl) done-end

either-right-ok : Conforms [] (put eitherNB (lit rightB) done) (send eitherNB end)
either-right-ok = put-ok refl (lit-ok refl) done-end

either-miss : ¬ Conforms [] (put eitherNB (lit badRight) done) (send eitherNB end)
either-miss (put-ok refl (lit-ok ()) _)

either-formed : TyOk [] eitherNB
either-formed =
  dat-ok refl (tys-cons nat-ok (tys-cons bit-ok tys-nil))
    (ctors-cons (flds-cons (ff-par refl nat-ok) flds-nil)
      (ctors-cons (flds-cons (ff-par refl bit-ok) flds-nil) ctors-nil))

------------------------------------------------------------------------
-- A put of a run application. The value sent is the value computed.
-- A result of the wrong type has no derivation. A value that does
-- not inhabit the type has none either.
------------------------------------------------------------------------

effCall : ValExpr maybeBool
effCall = call "effective" (varg itemTy (lit selfV) ∷ [])

eff-sent : sent effCall ≡ true
eff-sent = refl

effReply : Proc
effReply = put maybeBool effCall done

effAnswer : Proto
effAnswer = send maybeBool end

effReply-ok : Conforms [] effReply effAnswer
effReply-ok = put-ok refl (call-ok refl refl) done-end

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  effReply-decides : decide [] effReply effAnswer ≡ yes effReply-ok
  effReply-decides = refl

countCall : ValExpr boolTy
countCall = call "count" []

bad-count : ¬ Conforms [] (put boolTy countCall done) (send boolTy end)
bad-count (put-ok refl (call-ok p _) _) = just≢nothing (trans (sym p) loop-count)
  where loop-count : evalExpr countCall ≡ nothing
        loop-count = refl
bad-count (put-ok refl (call-ty m _ _ _) _) = true≢false (trans (sym m) refl)

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  bad-count-decides : decide [] (put boolTy countCall done) (send boolTy end) ≡ no bad-count
  bad-count-decides = refl

badCall : ValExpr boolTy
badCall = call "bad" []

bad-eval : evalExpr badCall ≡ just noneV
bad-eval = refl

bad-fits : fits noneV ≡ false
bad-fits = refl

bad-fit : ¬ Conforms [] (put boolTy badCall done) (send boolTy end)
bad-fit (put-ok refl (call-ok eq p) _) =
  true≢false
    (trans (sym p)
      (trans (cong fits (just-inj (trans (sym eq) bad-eval))) bad-fits))
bad-fit (put-ok refl (call-ty m _ _ _) _) = true≢false (trans (sym m) refl)

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  bad-fit-decides : decide [] (put boolTy badCall done) (send boolTy end) ≡ no bad-fit
  bad-fit-decides = refl

-- `effective` matches its argument and calls `mark`, declared before it.
otherCall : ValExpr maybeBool
otherCall = call "effective" (varg itemTy (lit otherV) ∷ [])

eff-eval : evalExpr effCall ≡ just justTrue
eff-eval = refl

other-eval : evalExpr otherCall ≡ just nothingB
other-eval = refl

markCall : ValExpr boolTy
markCall = call "mark" (varg itemTy (lit selfV) ∷ [])

mark-eval : evalExpr markCall ≡ just trueV
mark-eval = refl

sizeSelf : ValExpr nat
sizeSelf = call "size" (varg itemTy (lit selfV) ∷ [])

sizeOther : ValExpr nat
sizeOther = call "size" (varg itemTy (lit otherV) ∷ [])

size-self-eval : evalExpr sizeSelf ≡ just zero
size-self-eval = refl

size-other-eval : evalExpr sizeOther ≡ just two
size-other-eval = refl

sizeCap : Proto
sizeCap = esend "d" (nlit (nsuc nzero)) end

size-le : Le [] sizeSelf (nlit (nsuc nzero))
size-le = call-le size-self-eval (lit-le z≤n)

size-under : Conforms [] (put nat sizeSelf done) sizeCap
size-under = eput-ok (call-ok size-self-eval refl) (owed size-le) (send-plain plain-end done-end)

two≰one : nsuc (nsuc nzero) ≤ nsuc nzero → ⊥
two≰one (s≤s ())

size-over : ¬ Conforms [] (put nat sizeOther done) sizeCap
size-over (eput-ok _ (owed (call-le eq (lit-le q))) _) =
  two≰one
    (subst (λ w → toℕ w ≤ nsuc nzero)
      (just-inj (trans (sym eq) size-other-eval)) q)

loopCall : ValExpr nat
loopCall = call "loop" (varg nat (lit zero) ∷ [])

loop-eval : evalExpr loopCall ≡ nothing
loop-eval = refl

loop-refused : ¬ Conforms [] (put nat loopCall done) (send nat end)
loop-refused (put-ok refl (call-ok () _) _)
loop-refused (put-ok refl (call-ty () _ _ _) _)

-- `plus 0 0` takes the arm that does not call `plus`. The body still
-- calls itself, so the application does not evaluate.
plusCall : ValExpr nat
plusCall = call "plus" (varg nat (lit zero) ∷ varg nat (lit zero) ∷ [])

plus-eval : evalExpr plusCall ≡ nothing
plus-eval = refl

plus-refused : ¬ Conforms [] (put nat plusCall done) (send nat end)
plus-refused (put-ok refl (call-ok () _) _)
plus-refused (put-ok refl (call-ty () _ _ _) _)

earlyCall : ValExpr nat
earlyCall = call "early" []

early-eval : evalExpr earlyCall ≡ nothing
early-eval = refl

early-refused : ¬ Conforms [] (put nat earlyCall done) (send nat end)
early-refused (put-ok refl (call-ok () _) _)
early-refused (put-ok refl (call-ty () _ _ _) _)

lateCall : ValExpr nat
lateCall = call "late" []

late-eval : evalExpr lateCall ≡ just zero
late-eval = refl

------------------------------------------------------------------------
-- A get followed by a match. Each arm conforms to the one
-- continuation. The processes may differ. A short match, a nat, and
-- a third arm do not cover.
------------------------------------------------------------------------

bitChoice : Proto
bitChoice = recv bit (choose end end)

bitTaker : Proc
bitTaker = mget bit "b" (bare (pick0 done) ∷ bare (pick1 done) ∷ [])

bitTaker-ok : Conforms [] bitTaker bitChoice
bitTaker-ok =
  mget-ok refl bit-cov
    (arms-cons (pick0-ok done-end)
      (arms-cons (pick1-ok done-end) arms-nil))

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  bitTaker-decides : decide [] bitTaker bitChoice ≡ yes bitTaker-ok
  bitTaker-decides = refl

boolChoice : Proto
boolChoice = recv boolTy end

boolTaker : Proc
boolTaker = mget boolTy "b" (bare done ∷ bare done ∷ [])

bool-taker-ok : Conforms [] boolTaker boolChoice
bool-taker-ok = mget-ok refl (dat-cov refl) (arms-cons done-end (arms-cons done-end arms-nil))

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  bool-taker-decides : decide [] boolTaker boolChoice ≡ yes bool-taker-ok
  bool-taker-decides = refl

optChoice : Proto
optChoice = recv maybeNat end

optTaker : Proc
optTaker = mget maybeNat "m" (bare done ∷ bare done ∷ [])

opt-taker-ok : Conforms [] optTaker optChoice
opt-taker-ok = mget-ok refl (dat-cov refl) (arms-cons done-end (arms-cons done-end arms-nil))

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  opt-taker-decides : decide [] optTaker optChoice ≡ yes opt-taker-ok
  opt-taker-decides = refl

shortMatch : Proc
shortMatch = mget bit "b" (bare done ∷ [])

short-refused : ¬ Conforms [] shortMatch (recv bit end)
short-refused (mget-ok refl () _)

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  short-decides : decide [] shortMatch (recv bit end) ≡ no short-refused
  short-decides = refl

nat-match : Proc
nat-match = mget nat "n" (bare done ∷ bare done ∷ [])

nat-match-refused : ¬ Conforms [] nat-match (recv nat end)
nat-match-refused (mget-ok refl () _)

third-arm : Proc
third-arm = mget bit "b" (bare done ∷ bare done ∷ bare done ∷ [])

third-refused : ¬ Conforms [] third-arm (recv bit end)
third-refused (mget-ok refl () _)

-- A match finishes when every arm does. One abandoned arm does not.
match-finishes : finishes bitTaker ≡ ends (ends-mget (ends-cons (ends-pick0 ends-done) (ends-cons (ends-pick1 ends-done) ends-nil)))
match-finishes = refl

match-skel : skel bitTaker ≡ hear bit "b" (pick (choose0 finish ∷ choose1 finish ∷ []))
match-skel = refl

-- A named arm binds the constructor's fields. `b` has the field's
-- type at this payload, `Bool`. The name is payload data: the arm
-- may send it, and may send the value a run computes from it. The
-- run's codomain is the payload. The field is not known here, so the
-- check is the declared type, not an evaluation.
grantCall : ValExpr boolTy
grantCall = call "grant" (varg boolTy (var "b") ∷ [])

fieldReply : Proc
fieldReply = mget maybeBool "m"
  ( named "nothing" [] (put boolTy (lit falseV) done)
  ∷ named "just" ("b" ∷ []) (put boolTy grantCall done)
  ∷ [])

fieldAsk : Proto
fieldAsk = recv maybeBool (send boolTy end)

field-reply-ok : Conforms [] fieldReply fieldAsk
field-reply-ok =
  mget-ok refl (dat-cov refl)
    (arms-named refl (put-ok refl (lit-ok refl) done-end)
      (arms-named refl
        (put-ok refl
          (call-ty refl refl refl (args-cons (arg-var here) args-nil))
          done-end)
        arms-nil))

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  field-reply-decides : decide [] fieldReply fieldAsk ≡ yes field-reply-ok
  field-reply-decides = refl

-- The same field sent as itself.
fwdField : Proc
fwdField = mget maybeBool "m"
  ( named "nothing" [] (put boolTy (lit falseV) done)
  ∷ named "just" ("b" ∷ []) (put boolTy (var "b") done)
  ∷ [])

fwd-field-ok : Conforms [] fwdField fieldAsk
fwd-field-ok =
  mget-ok refl (dat-cov refl)
    (arms-named refl (put-ok refl (lit-ok refl) done-end)
      (arms-named refl (put-ok refl (var-ok here) done-end) arms-nil))

-- A field may be sent twice. It is not a linear endpoint.
twiceField : Proc
twiceField = mget maybeBool "m"
  ( named "nothing" [] (put boolTy (lit falseV) (put boolTy (lit falseV) done))
  ∷ named "just" ("b" ∷ []) (put boolTy (var "b") (put boolTy (var "b") done))
  ∷ [])

twice-ok : Conforms [] twiceField (recv maybeBool (send boolTy (send boolTy end)))
twice-ok =
  mget-ok refl (dat-cov refl)
    (arms-named refl (put-ok refl (lit-ok refl) (put-ok refl (lit-ok refl) done-end))
      (arms-named refl
        (put-ok refl (var-ok here) (put-ok refl (var-ok here) done-end))
        arms-nil))

-- The tail of a list is that same data type.
tailPass : Proc
tailPass = mget listNat "xs"
  ( named "nil" [] (put listNat (lit nilV) done)
  ∷ named "cons" ("n" ∷ "ys" ∷ []) (put listNat (var "ys") done)
  ∷ [])

tail-ok : Conforms [] tailPass (recv listNat (send listNat end))
tail-ok =
  mget-ok refl (dat-cov refl)
    (arms-named refl (put-ok refl (lit-ok refl) done-end)
      (arms-named refl (put-ok refl (var-ok here) done-end) arms-nil))

-- The meeting reads the fields of the value it received. `just true`
-- turns `grant b` into `grant true`, and `ys` on `cons 0 []` is `[]`.
field-reply-just :
  armOf maybeBool justTrue
    (named "nothing" [] (put boolTy (lit falseV) done)
      ∷ named "just" ("b" ∷ []) (put boolTy grantCall done) ∷ [])
    ≡ just (put boolTy (call "grant" (varg boolTy (lit trueV) ∷ [])) done)
field-reply-just = refl

field-reply-nothing :
  armOf maybeBool nothingB
    (named "nothing" [] (put boolTy (lit falseV) done)
      ∷ named "just" ("b" ∷ []) (put boolTy grantCall done) ∷ [])
    ≡ just (put boolTy (lit falseV) done)
field-reply-nothing = refl

grant-true : evalExpr (call {boolTy} "grant" (varg boolTy (lit trueV) ∷ [])) ≡ just trueV
grant-true = refl

tail-cons :
  armOf listNat consV
    (named "nil" [] done
      ∷ named "cons" ("n" ∷ "ys" ∷ []) (put listNat (var "ys") done) ∷ [])
    ≡ just (put listNat (lit nilV) done)
tail-cons = refl

------------------------------------------------------------------------
-- A received pair or record binds its components. A component is
-- payload data: the arm may send it, and may send the value a run
-- computes from it. The innermost binding wins. A constructor arm
-- does not cover a pair.
------------------------------------------------------------------------

pairNatBit : Ty
pairNatBit = pair nat bit

pairReply : Proc
pairReply =
  mget pairNatBit "p" (prod (pPair "n" "c") (put nat (var "n") done) ∷ [])

n≢c : "n" ≢ "c"
n≢c eq with "n" ≟ "c"
... | no′ ¬eq = ¬eq eq

pair-reply-ok : Conforms [] pairReply (recv pairNatBit (send nat end))
pair-reply-ok =
  mget-ok refl pair-cov
    (arms-prod refl (put-ok refl (var-ok (there n≢c here)) done-end) arms-nil)

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  pair-reply-decides : decide [] pairReply (recv pairNatBit (send nat end)) ≡ yes pair-reply-ok
  pair-reply-decides = refl

pairBoolBit : Ty
pairBoolBit = pair boolTy bit

grantOnPair : ValExpr boolTy
grantOnPair = call "grant" (varg boolTy (var "a") ∷ [])

a≢c : "a" ≢ "c"
a≢c eq with "a" ≟ "c"
... | no′ ¬eq = ¬eq eq

pairGrant : Proc
pairGrant =
  mget pairBoolBit "p" (prod (pPair "a" "c") (put boolTy grantOnPair done) ∷ [])

pair-grant-ok : Conforms [] pairGrant (recv pairBoolBit (send boolTy end))
pair-grant-ok =
  mget-ok refl pair-cov
    (arms-prod refl
      (put-ok refl
        (call-ty refl refl refl (args-cons (arg-var (there a≢c here)) args-nil))
        done-end)
      arms-nil)

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  pair-grant-decides : decide [] pairGrant (recv pairBoolBit (send boolTy end)) ≡ yes pair-grant-ok
  pair-grant-decides = refl

pair-grant-arm :
  armOf pairBoolBit (tup trueV b0)
    (prod (pPair "a" "c") (put boolTy grantOnPair done) ∷ [])
    ≡ just (put boolTy (call "grant" (varg boolTy (lit trueV) ∷ [])) done)
pair-grant-arm = refl

pair-nat-arm :
  armOf pairNatBit (tup zero b1)
    (prod (pPair "n" "c") (put nat (var "n") done) ∷ [])
    ≡ just (put nat (lit zero) done)
pair-nat-arm = refl

-- The second component hides the first when both binders are `n`.
pair-shadow-arm :
  armOf pairNatBit (tup zero b1)
    (prod (pPair "n" "n") (put bit (var "n") done) ∷ [])
    ≡ just (put bit (lit b1) done)
pair-shadow-arm = refl

noteTy : Ty
noteTy = rec (named "x" nat (named "y" bit noFields))

noteReply : Proc
noteReply =
  mget noteTy "r"
    (prod (pRec (("x" , "a") ∷ ("y" , "c") ∷ [])) (put bit (var "c") done) ∷ [])

note-ok : Conforms [] noteReply (recv noteTy (send bit end))
note-ok =
  mget-ok refl (rec-cov (fits-cons (fits-cons fits-nil)))
    (arms-prod refl (put-ok refl (var-ok here) done-end) arms-nil)

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  note-decides : decide [] noteReply (recv noteTy (send bit end)) ≡ yes note-ok
  note-decides = refl

noteVal : Val noteTy
noteVal = rec (cell zero (cell b1 noRow))

note-arm :
  armOf noteTy noteVal
    (prod (pRec (("x" , "a") ∷ ("y" , "c") ∷ [])) (put bit (var "c") done) ∷ [])
    ≡ just (put bit (lit b1) done)
note-arm = refl

-- A component that is itself a record is bound whole and sent whole.
innerTy : Ty
innerTy = rec (named "z" nat noFields)

wrapTy : Ty
wrapTy = pair innerTy bit

innerVal : Val innerTy
innerVal = rec (cell one noRow)

wrap-arm :
  armOf wrapTy (tup innerVal b0)
    (prod (pPair "a" "c") (put innerTy (var "a") done) ∷ [])
    ≡ just (put innerTy (lit innerVal) done)
wrap-arm = refl

twicePair : Proc
twicePair =
  mget pairNatBit "p"
    (prod (pPair "n" "c") (put nat (var "n") (put nat (var "n") done)) ∷ [])

twice-pair-ok : Conforms [] twicePair (recv pairNatBit (send nat (send nat end)))
twice-pair-ok =
  mget-ok refl pair-cov
    (arms-prod refl
      (put-ok refl (var-ok (there n≢c here))
        (put-ok refl (var-ok (there n≢c here)) done-end))
      arms-nil)

-- A constructor arm does not cover a pair.
ctorOnPair : Proc
ctorOnPair = mget pairNatBit "p" (named "pair" ("n" ∷ "c" ∷ []) done ∷ [])

ctor-on-pair : ¬ Conforms [] ctorOnPair (recv pairNatBit end)
ctor-on-pair (mget-ok refl () _)

-- Too few binders for `just`. A bare arm is not an arity check.
shortJust : Proc
shortJust = mget maybeBool "m"
  ( named "nothing" [] done
  ∷ named "just" [] done
  ∷ [])

short-just : ¬ Conforms [] shortJust (recv maybeBool end)
short-just (mget-ok refl _ (arms-named _ _ (arms-named eq _ _))) =
  just≢nothing (trans (sym eq) refl)

-- The constructor at that position is `nothing`, not another name.
badName : Proc
badName = mget maybeBool "m"
  ( named "none" [] done
  ∷ named "just" ("b" ∷ []) done
  ∷ [])

bad-name : ¬ Conforms [] badName (recv maybeBool end)
bad-name (mget-ok refl _ (arms-named eq _ _)) =
  just≢nothing (trans (sym eq) refl)

-- `b` is a `Bool`. It is not a nat.
badField : Proc
badField = mget maybeBool "m"
  ( named "nothing" [] done
  ∷ named "just" ("b" ∷ []) (put nat (var "b") done)
  ∷ [])

fieldCtx : Ctx
fieldCtx = ("b" , boolTy) ∷ ("m" , maybeBool) ∷ []

¬bool-nat : ¬ ("b" ∈ fieldCtx ∷ nat)
¬bool-nat (there b≢b _) = b≢b refl

bad-field : ¬ Conforms [] badField (recv maybeBool (send nat end))
bad-field (mget-ok refl _ (arms-named _ _ (arms-named eq (put-ok _ (var-ok mem) _) _))) =
  ¬bool-nat (subst (λ Θ → "b" ∈ Θ ∷ nat) (just-inj (trans (sym eq) refl)) mem)

------------------------------------------------------------------------
-- A declared session used as a continuation. The table is latest
-- first, as the run table is. A call of a session in the tail unfolds
-- by structural recursion on that tail and on the protocol. A call of
-- the session being opened is not in the tail: under an action it is
-- a guarded loop, and at the head it is refused. A name that is in
-- the book but not in the tail was declared later. A name in neither
-- is unknown. An argument is a numeral, a nat in scope, a successor,
-- or a run application. The run application is `apply` on `runs`.
-- Nothing here is added to `Tm`.
------------------------------------------------------------------------

data SArg : Set where
  saLit  : ℕ → SArg
  saVar  : String → SArg
  saSuc  : SArg → SArg
  saCall : String → List SArg → SArg

data QProto : Set where
  q-end    : QProto
  q-send   : Ty → QProto → QProto
  q-recv   : Ty → QProto → QProto
  q-dsend  : String → Ty → QProto → QProto
  q-drecv  : String → Ty → QProto → QProto
  q-esend  : String → NExp → QProto → QProto
  q-erecv  : String → NExp → QProto → QProto
  q-isend  : String → QProto → QProto → QProto
  q-irecv  : String → QProto → QProto → QProto
  q-choose : QProto → QProto → QProto
  q-branch : QProto → QProto → QProto
  q-case   : Scrut → List (String × QProto) → QProto
  q-call   : String → List SArg → QProto

data SDecl : Set where
  sdecl : String → List String → QProto → SDecl

data ArgR : Set where
  argOk : List NExp → ArgR
  argNo : String → ArgR

data Opened : Set where
  finite    : Proto → Opened
  looping   : Opened
  unguarded : Opened
  later     : String → Opened
  unknown   : String → Opened
  badArity  : String → Opened
  badArg    : String → Opened

namedS : List SDecl → String → Bool
namedS [] _ = false
namedS (sdecl n _ _ ∷ Δ) f with f ≟ n
... | yes′ _ = true
... | no′ _ = namedS Δ f

missing : List SDecl → String → Opened
missing Δ f with namedS Δ f
... | true = later f
... | false = unknown f

envOfS : List String → List NExp → Idx
envOfS [] _ = none
envOfS (_ ∷ _) [] = none
envOfS (x ∷ xs) (e ∷ es) = bind x e (envOfS xs es)

idxBind : String → Ty → Idx → Idx
idxBind x nat ρ = bind x (nvar x) (shadow x ρ)
idxBind x _ ρ = shadow x ρ

badOf : SArg → String
badOf (saLit _) = "literal"
badOf (saVar x) = x
badOf (saSuc a) = badOf a
badOf (saCall f _) = f

natsRaw : List NExp → Maybe (List Raw)
natsRaw [] = just []
natsRaw (nlit n ∷ es) = bindM (natsRaw es) (λ rs → just (rawNat n ∷ rs))
natsRaw (nvar _ ∷ _) = nothing

sucN : NExp → Maybe NExp
sucN (nlit n) = just (nlit (nsuc n))
sucN (nvar _) = nothing

rawToN : Raw → Maybe NExp
rawToN (rawNat n) = just (nlit n)
rawToN _ = nothing

callArg : ArgR → String → Maybe NExp
callArg (argOk xs) f = bindM (natsRaw xs) (λ rs → bindM (apply runs f rs) rawToN)
callArg (argNo _) _ = nothing

mutual
  evalS : Idx → SArg → Maybe NExp
  evalS _ (saLit n) = just (nlit n)
  evalS ρ (saVar x) with lookupIdx ρ x
  ... | just e = just e
  ... | nothing = nothing
  evalS ρ (saSuc a) = bindM (evalS ρ a) sucN
  evalS ρ (saCall f as) = callArg (evalSArgs ρ as) f

  evalSArgs : Idx → List SArg → ArgR
  evalSArgs _ [] = argOk []
  evalSArgs ρ (a ∷ as) with evalS ρ a
  ... | nothing = argNo (badOf a)
  ... | just e with evalSArgs ρ as
  ... | argNo msg = argNo msg
  ... | argOk es = argOk (e ∷ es)

sendOf : Ty → Opened → Opened
sendOf A (finite p) = finite (send A p)
sendOf _ o = o

recvOf : Ty → Opened → Opened
recvOf A (finite p) = finite (recv A p)
recvOf _ o = o

dsendOf : String → Ty → Opened → Opened
dsendOf x A (finite p) = finite (dsend x A p)
dsendOf _ _ o = o

drecvOf : String → Ty → Opened → Opened
drecvOf x A (finite p) = finite (drecv x A p)
drecvOf _ _ o = o

esendOf : String → NExp → Opened → Opened
esendOf x e (finite p) = finite (esend x e p)
esendOf _ _ o = o

erecvOf : String → NExp → Opened → Opened
erecvOf x e (finite p) = finite (erecv x e p)
erecvOf _ _ o = o

isendOf : String → Opened → Opened → Opened
isendOf x (finite p) (finite q) = finite (isend x p q)
isendOf _ (finite _) o = o
isendOf _ o _ = o

irecvOf : String → Opened → Opened → Opened
irecvOf x (finite p) (finite q) = finite (irecv x p q)
irecvOf _ (finite _) o = o
irecvOf _ o _ = o

chooseOf : Opened → Opened → Opened
chooseOf (finite p) (finite q) = finite (choose p q)
chooseOf (finite _) o = o
chooseOf o _ = o

branchOf : Opened → Opened → Opened
branchOf (finite p) (finite q) = finite (branch p q)
branchOf (finite _) o = o
branchOf o _ = o

armFinite : List (String × Opened) → Maybe (List (String × Proto))
armFinite [] = just []
armFinite ((c , finite p) ∷ as) = bindM (armFinite as) (λ ps → just ((c , p) ∷ ps))
armFinite (_ ∷ _) = nothing

firstBad : List (String × Opened) → Opened
firstBad [] = unknown "case"
firstBad ((_ , finite _) ∷ as) = firstBad as
firstBad ((_ , o) ∷ _) = o

caseOf : Scrut → List (String × Opened) → Opened
caseOf scrut as with armFinite as
... | just ps = finite (pcase scrut ps)
... | nothing = firstBad as

mutual
  expand : List SDecl → List SDecl → String → Bool → QProto → Idx → Opened
  expandArms : List SDecl → List SDecl → String → Bool → List (String × QProto) → Idx → List (String × Opened)
  expand _ _ _ _ q-end _ = finite end
  expand book Δ self _ (q-send A s) ρ =
    sendOf (applyTy ρ A) (expand book Δ self true s ρ)
  expand book Δ self _ (q-recv A s) ρ =
    recvOf (applyTy ρ A) (expand book Δ self true s ρ)
  expand book Δ self _ (q-dsend x A s) ρ =
    dsendOf x (applyTy ρ A) (expand book Δ self true s (idxBind x (applyTy ρ A) ρ))
  expand book Δ self _ (q-drecv x A s) ρ =
    drecvOf x (applyTy ρ A) (expand book Δ self true s (idxBind x (applyTy ρ A) ρ))
  expand book Δ self _ (q-esend x e s) ρ =
    esendOf x (applyNExp ρ e) (expand book Δ self true s ρ)
  expand book Δ self _ (q-erecv x e s) ρ =
    erecvOf x (applyNExp ρ e) (expand book Δ self true s ρ)
  expand book Δ self _ (q-isend x s t) ρ =
    isendOf x (expand book Δ self true s (shadow x ρ)) (expand book Δ self true t (shadow x ρ))
  expand book Δ self _ (q-irecv x s t) ρ =
    irecvOf x (expand book Δ self true s (shadow x ρ)) (expand book Δ self true t (shadow x ρ))
  expand book Δ self _ (q-choose s t) ρ =
    chooseOf (expand book Δ self true s ρ) (expand book Δ self true t ρ)
  expand book Δ self _ (q-branch s t) ρ =
    branchOf (expand book Δ self true s ρ) (expand book Δ self true t ρ)
  expand book Δ self g (q-case scrut arms) ρ =
    caseOf scrut (expandArms book Δ self g arms ρ)
  expand book Δ self g (q-call f as) ρ with evalSArgs ρ as | f ≟ self | g
  ... | argNo msg | _ | _ = badArg msg
  ... | argOk _ | yes′ _ | true = looping
  ... | argOk _ | yes′ _ | false = unguarded
  ... | argOk es | no′ _ | _ = openName book Δ f es

  openName : List SDecl → List SDecl → String → List NExp → Opened
  openName book [] f _ = missing book f
  openName book (sdecl n ps body ∷ Δ) f es =
    openHere (f ≟ n) (length es ≟ℕ length ps) book Δ n ps body f es

  openHere :
    {f n : String} {k ar : ℕ} →
    Dec (f ≡ n) → Dec (k ≡ ar) →
    List SDecl → List SDecl → String → List String → QProto → String → List NExp → Opened
  openHere (yes′ _) (yes′ _) book Δ n ps body _ es =
    expand book Δ n false body (envOfS ps es)
  openHere (yes′ _) (no′ _) _ _ n _ _ _ _ = badArity n
  openHere (no′ _) _ book Δ _ _ _ f es = openName book Δ f es

  expandArms _ _ _ _ [] _ = []
  expandArms book Δ self g ((c , s) ∷ as) ρ =
    (c , expand book Δ self g s ρ) ∷ expandArms book Δ self g as ρ

-- The book is latest first. Opening starts at that book, so the tail
-- of the matching declaration is everything declared before it.
openTop : List SDecl → String → List SArg → Opened
openTop book f as with evalSArgs none as
... | argNo msg = badArg msg
... | argOk es = openName book book f es

------------------------------------------------------------------------
-- `ack` is `send Bit end`. `req` is `send Nat ack`, which opens to
-- `send Nat (send Bit end)`. A choice arm, an indexed arm, and a
-- dependent continuation open the same way. `frames 3` is a vector
-- of that length. `frames (count)` is the nat `count` computes.
-- `s := s` is unguarded. A call of a later session is refused.
-- A guarded self-call is a loop, not a finite protocol.
------------------------------------------------------------------------

sessAck : SDecl
sessAck = sdecl "ack" [] (q-send bit q-end)

sessReq : SDecl
sessReq = sdecl "req" [] (q-send nat (q-call "ack" []))

sessBook : List SDecl
sessBook = sessReq ∷ sessAck ∷ []

sessReqProto : Proto
sessReqProto = send nat (send bit end)

sess-req : openTop sessBook "req" [] ≡ finite sessReqProto
sess-req = refl

sess-ack : openTop sessBook "ack" [] ≡ finite (send bit end)
sess-ack = refl

sessClient : Proc
sessClient = put nat (lit zero) (put bit (lit b0) done)

sessServer : Proc
sessServer = get nat "n" (get bit "b" done)

sess-client : Conforms [] sessClient sessReqProto
sess-client = put-ok refl (lit-ok refl) (put-ok refl (lit-ok refl) done-end)

sess-server : Conforms [] sessServer (recv nat (recv bit end))
sess-server = get-ok refl (get-ok refl done-end)

sessChoice : SDecl
sessChoice = sdecl "choice" [] (q-choose (q-call "ack" []) q-end)

sessChoiceProto : Proto
sessChoiceProto = choose (send bit end) end

sess-choice : openTop (sessChoice ∷ sessAck ∷ []) "choice" [] ≡ finite sessChoiceProto
sess-choice = refl

sess-choice-ok : Conforms [] (pick0 (put bit (lit b0) done)) sessChoiceProto
sess-choice-ok = pick0-ok (put-ok refl (lit-ok refl) done-end)

sessBranch : SDecl
sessBranch = sdecl "offered" [] (q-branch (q-call "ack" []) q-end)

sess-branch : openTop (sessBranch ∷ sessAck ∷ []) "offered" [] ≡ finite (branch (send bit end) end)
sess-branch = refl

sessRoute : SDecl
sessRoute = sdecl "route" [] (q-irecv "b" (q-call "ack" []) (q-recv nat q-end))

sess-route :
  openTop (sessRoute ∷ sessAck ∷ []) "route" []
    ≡ finite (irecv "b" (send bit end) (recv nat end))
sess-route = refl

sessRest : SDecl
sessRest = sdecl "rest" ("k" ∷ []) (q-send (vec nat (nvar "k")) q-end)

sessSized : SDecl
sessSized = sdecl "sized" [] (q-drecv "n" nat (q-call "rest" (saVar "n" ∷ [])))

sess-sized :
  openTop (sessSized ∷ sessRest ∷ []) "sized" []
    ≡ finite (drecv "n" nat (send (vec nat (nvar "n")) end))
sess-sized = refl

three : ℕ
three = nsuc (nsuc (nsuc nzero))

sessFrames : SDecl
sessFrames = sdecl "frames" ("k" ∷ []) (q-send (vec nat (nvar "k")) q-end)

sessFramesProto : Proto
sessFramesProto = send (vec nat (nlit three)) end

sess-frames : openTop (sessFrames ∷ []) "frames" (saLit three ∷ []) ≡ finite sessFramesProto
sess-frames = refl

sess-frames-count :
  openTop (sessFrames ∷ []) "frames" (saCall "count" [] ∷ [])
    ≡ finite (send (vec nat (nlit (nsuc nzero))) end)
sess-frames-count = refl

sessFramesClient : Proc
sessFramesClient = put (vec nat (nlit three)) (lit (rep zero)) done

sess-frames-ok : Conforms [] sessFramesClient sessFramesProto
sess-frames-ok = put-ok refl (lit-ok refl) done-end

sessNote : SDecl
sessNote = sdecl "note" ("k" ∷ []) (q-send boolTy q-end)

sess-note : openTop (sessNote ∷ []) "note" (saLit (nsuc nzero) ∷ []) ≡ finite (send boolTy end)
sess-note = refl

sess-note-ok : Conforms [] (put boolTy (lit trueV) done) (send boolTy end)
sess-note-ok = put-ok refl (lit-ok refl) done-end

sessSelf : SDecl
sessSelf = sdecl "s" [] (q-call "s" [])

sess-unguarded : openTop (sessSelf ∷ []) "s" [] ≡ unguarded
sess-unguarded = refl

sessSpin : SDecl
sessSpin = sdecl "spin" [] (q-send nat (q-call "spin" []))

sess-loop : openTop (sessSpin ∷ []) "spin" [] ≡ looping
sess-loop = refl

sessStream : SDecl
sessStream =
  sdecl "stream" ("n" ∷ [])
    (q-esend "d" (nvar "n") (q-call "stream" (saSuc (saVar "n") ∷ [])))

sess-stream : openTop (sessStream ∷ []) "stream" (saLit nzero ∷ []) ≡ looping
sess-stream = refl

sessEarly : SDecl
sessEarly = sdecl "early" [] (q-call "late" [])

sessLate : SDecl
sessLate = sdecl "late" [] q-end

sess-later : openTop (sessLate ∷ sessEarly ∷ []) "early" [] ≡ later "late"
sess-later = refl

sess-unknown : openTop sessBook "gone" [] ≡ unknown "gone"
sess-unknown = refl

sess-arity : openTop (sessFrames ∷ []) "frames" [] ≡ badArity "frames"
sess-arity = refl

sess-arg : openTop (sessFrames ∷ []) "frames" (saVar "nope" ∷ []) ≡ badArg "nope"
sess-arg = refl

sess-plus :
  openTop (sessFrames ∷ []) "frames" (saCall "plus" (saLit nzero ∷ saLit nzero ∷ []) ∷ [])
    ≡ badArg "plus"
sess-plus = refl

------------------------------------------------------------------------
-- A protocol continues by the value just exchanged. The arms are the
-- payload's constructors, in declaration order. A sender is checked
-- on the arm that value selects. A receiver is checked on every arm.
-- A run of the value selects the arm of the run's result instead.
------------------------------------------------------------------------

dataV : Val frameTy
dataV = con "data" snil

trailV : Val frameTy
trailV = con "trailers" snil

headV : Val frameTy
headV = con "headers" snil

frameArms : List (String × Proto)
frameArms =
  ("data" , send bit end) ∷
  ("trailers" , send bit end) ∷
  ("headers" , recv nat end) ∷ []

frameCase : Proto
frameCase = drecv "f" frameTy (pcase (byVal "f") frameArms)

frameClientProto : Proto
frameClientProto = dsend "f" frameTy (pcase (byVal "f") (
  ("data" , recv bit end) ∷
  ("trailers" , recv bit end) ∷
  ("headers" , send nat end) ∷ []))

frame-formed : TyOk [] frameTy
frame-formed = dat-ok refl tys-nil
  (ctors-cons flds-nil (ctors-cons flds-nil (ctors-cons flds-nil ctors-nil)))

frame-wf : ProtoOk [] frameCase
frame-wf = drecv-case frame-formed (ok-val refl
  (arms-one (send-ok bit-ok end-ok)
    (arms-one (send-ok bit-ok end-ok)
      (arms-one (recv-ok nat-ok end-ok) arms-none))))

frameServer : Proc
frameServer = mget frameTy "f"
  ( bare (put bit (lit b0) done)
  ∷ bare (put bit (lit b0) done)
  ∷ bare (get nat "n" done)
  ∷ [])

frame-server-ok : Conforms [] frameServer frameCase
frame-server-ok = mget-val refl (dat-cov refl) refl
  (at-cons (put-ok refl (lit-ok refl) done-end)
    (at-cons (put-ok refl (lit-ok refl) done-end)
      (at-cons (get-ok refl done-end) at-nil)))

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  frame-server-decides : decide [] frameServer frameCase ≡ yes frame-server-ok
  frame-server-decides = refl

-- Headers selects the third arm. The data arm is not checked.
frameClient : Proc
frameClient = put frameTy (lit headV) (put nat (lit zero) done)

frame-client-ok : Conforms [] frameClient frameClientProto
frame-client-ok = dput-arm refl (lit-ok refl) refl (put-ok refl (lit-ok refl) done-end)

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  frame-client-decides : decide [] frameClient frameClientProto ≡ yes frame-client-ok
  frame-client-decides = refl

-- Data selects the first arm, a receive of a bit.
frameData : Proc
frameData = put frameTy (lit dataV) (get bit "c" done)

frame-data-ok : Conforms [] frameData frameClientProto
frame-data-ok = dput-arm refl (lit-ok refl) refl (get-ok refl done-end)

-- An in-flight frame continues as a bit, not as the headers nat.
goawayForData : Proc
goawayForData = put frameTy (lit dataV) (put nat (lit zero) done)

goaway-for-data : ¬ Conforms [] goawayForData frameClientProto
goaway-for-data (dput-ok _ _ () _)
goaway-for-data (dput-arm {T = T} _ _ p d) = refuse (just-inj (trans (sym p) data-arm)) d
  where
  data-arm : selectProto "f" (lit dataV) (byVal "f")
      (("data" , recv bit end) ∷ ("trailers" , recv bit end) ∷ ("headers" , send nat end) ∷ [])
      ≡ just (recv bit end)
  data-arm = refl
  refuse : ∀ {T} → T ≡ recv bit end →
    Conformsρ [] (bind "f" (ixOf frameTy (lit dataV)) (shadow "f" none))
      (put nat (lit zero) done) T → ⊥
  refuse refl ()

-- The received name does not select an arm when the arms differ.
splitArms : List (String × Proto)
splitArms =
  ("data" , end) ∷
  ("trailers" , send bit end) ∷
  ("headers" , end) ∷ []

fwd-split : ¬ Conforms (("f" , frameTy) ∷ []) (put frameTy (var "f") done)
  (dsend "f" frameTy (pcase (byVal "f") splitArms))
fwd-split (dput-ok _ _ () _)
fwd-split (dput-arm _ _ () _)

-- Every arm is the same protocol, so the variable has one continuation.
agreeArms : List (String × Proto)
agreeArms = ("data" , end) ∷ ("trailers" , end) ∷ ("headers" , end) ∷ []

agree-fwd : Conforms (("f" , frameTy) ∷ []) (put frameTy (var "f") done)
  (dsend "f" frameTy (pcase (byVal "f") agreeArms))
agree-fwd = dput-arm refl (var-ok here) refl done-end

-- `lateFrame` is true on data and trailers, false on headers.
lateArms : List (String × Proto)
lateArms = ("true" , send bit end) ∷ ("false" , send nat end) ∷ []

lateCase : Proto
lateCase = drecv "f" frameTy (pcase (byRun "lateFrame" "f" boolTy) lateArms)

late-wf : ProtoOk [] lateCase
late-wf = drecv-case frame-formed (ok-run refl refl refl
  (arms-one (send-ok bit-ok end-ok) (arms-one (send-ok nat-ok end-ok) arms-none)))

lateServer : Proc
lateServer = mget frameTy "f"
  ( bare (put bit (lit b0) done)
  ∷ bare (put bit (lit b0) done)
  ∷ bare (put nat (lit zero) done)
  ∷ [])

late-server-ok : Conforms [] lateServer lateCase
late-server-ok = mget-run refl (dat-cov refl) refl refl refl
  (run-cons refl (put-ok refl (lit-ok refl) done-end)
    (run-cons refl (put-ok refl (lit-ok refl) done-end)
      (run-cons refl (put-ok refl (lit-ok refl) done-end) run-nil)))

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  late-server-decides : decide [] lateServer lateCase ≡ yes late-server-ok
  late-server-decides = refl

lateClientProto : Proto
lateClientProto = dsend "f" frameTy (pcase (byRun "lateFrame" "f" boolTy) (
  ("true" , recv bit end) ∷ ("false" , recv nat end) ∷ []))

lateClient : Proc
lateClient = put frameTy (lit headV) (get nat "n" done)

late-client-ok : Conforms [] lateClient lateClientProto
late-client-ok = dput-arm refl (lit-ok refl) refl (get-ok refl done-end)

-- Sending a nat for an in-flight frame follows the true arm, which receives a bit.
lateGoaway : Proc
lateGoaway = mget frameTy "f"
  ( bare (put nat (lit zero) done)
  ∷ bare (put bit (lit b0) done)
  ∷ bare (put nat (lit zero) done)
  ∷ [])

late-goaway : ¬ Conforms [] lateGoaway lateCase
late-goaway (mget-run _ _ _ _ refl (run-cons refl (put-ok () _ _) _))

-- The `just` arm reads a field. Probing passes none, so the receiver has no derivation.
onJustCase : Proto
onJustCase = drecv "m" maybeNat (pcase (byRun "onJust" "m" boolTy) (
  ("true" , end) ∷ ("false" , end) ∷ []))

onJust-wf : ProtoOk [] onJustCase
onJust-wf = drecv-case
  (dat-ok refl (tys-cons nat-ok tys-nil)
    (ctors-cons flds-nil
      (ctors-cons (flds-cons (ff-par refl nat-ok) flds-nil) ctors-nil)))
  (ok-run refl refl refl (arms-one end-ok (arms-one end-ok arms-none)))

onJust-recv : ¬ Conforms [] (mget maybeNat "m" (bare done ∷ bare done ∷ [])) onJustCase
onJust-recv (mget-run _ _ _ _ refl (run-cons refl done-end (run-cons () _ _)))

-- `lateBool` reads the field of `just`. `nothing` is false. `just b`
-- is `b`. The receiver covers that split by a case on the bound field.
ctlDecl : Decl
ctlDecl = mkDecl "Ctl" nzero (ctor "rst" [] ∷ [])

ctlTy : Ty
ctlTy = dat ctlDecl []

rstV : Val ctlTy
rstV = con "rst" snil

gateArms : List (String × Proto)
gateArms = ("true" , send ctlTy end) ∷ ("false" , end) ∷ []

gateProto : Proto
gateProto = drecv "m" maybeBool (pcase (byRun "lateBool" "m" boolTy) gateArms)

gateBack : Proto
gateBack = dsend "m" maybeBool (pcase (byRun "lateBool" "m" boolTy) (
  ("true" , recv ctlTy end) ∷ ("false" , end) ∷ []))

gateServer : Proc
gateServer = mget maybeBool "m"
  ( named "nothing" [] done
  ∷ fork "just" ("b" ∷ []) "b"
      ( named "true" [] (put ctlTy (lit rstV) done)
      ∷ named "false" [] done
      ∷ [])
  ∷ [])

gateTrue : Proc
gateTrue = put maybeBool (lit justTrue) (get ctlTy "c" done)

gateFalse : Proc
gateFalse = put maybeBool (lit justFalse) done

gateNone : Proc
gateNone = put maybeBool (lit nothingB) done

lateBool-true : evalVal "lateBool" justTrue boolTy ≡ just trueV
lateBool-true = refl

lateBool-false : evalVal "lateBool" justFalse boolTy ≡ just falseV
lateBool-false = refl

lateBool-none : evalVal "lateBool" nothingB boolTy ≡ just falseV
lateBool-none = refl

split-just : splitOf "lateBool" maybeBool "just" boolTy gateArms
  ≡ just (node nzero (("true" , flat (send ctlTy end)) ∷ ("false" , flat end) ∷ []))
split-just = refl

split-none : splitOf "lateBool" maybeBool "nothing" boolTy gateArms
  ≡ just (flat end)
split-none = refl

gate-server-ok : Conforms [] gateServer gateProto
gate-server-ok = mget-run refl (dat-cov refl) refl refl refl
  (run-named refl refl done-end
    (run-fork refl refl refl refl refl
      (fork-named refl (put-ok refl (lit-ok refl) done-end)
        (fork-named refl done-end fork-nil))
      run-nil))

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  gate-server-decides : decide [] gateServer gateProto ≡ yes gate-server-ok
  gate-server-decides = refl

gate-true-ok : Conforms [] gateTrue gateBack
gate-true-ok = dput-arm refl (lit-ok refl) refl (get-ok refl done-end)

gate-false-ok : Conforms [] gateFalse gateBack
gate-false-ok = dput-arm refl (lit-ok refl) refl done-end

gate-none-ok : Conforms [] gateNone gateBack
gate-none-ok = dput-arm refl (lit-ok refl) refl done-end

-- One arm sends evidence. The skeleton carries the nat and not the bound.
evCase : Proto
evCase = drecv "f" frameTy (pcase (byVal "f") (
  ("data" , esend "d" (nlit (nsuc nzero)) end) ∷
  ("trailers" , end) ∷
  ("headers" , end) ∷ []))

evServer : Proc
evServer = mget frameTy "f" (bare (put nat (lit zero) done) ∷ bare done ∷ bare done ∷ [])

ev-ok : Conforms [] evServer evCase
ev-ok = mget-val refl (dat-cov refl) refl
  (at-cons (eput-ok (lit-ok refl) (owed (lit-le z≤n)) (send-plain plain-end done-end))
    (at-cons done-end (at-cons done-end at-nil)))

ev-skel : skel evServer ≡ hear frameTy "f" (pick (say (lit zero) finish ∷ finish ∷ finish ∷ []))
ev-skel = refl

-- A nat is not a scrutinee. The scrutinee is the binder, not an earlier name.
-- A run that calls itself is not ready. An arm list is the constructors, no more and no fewer.
natCase : Proto
natCase = drecv "n" nat (pcase (byVal "n") (("zero" , end) ∷ []))

nat-case-refused : ¬ ProtoOk [] natCase
nat-case-refused (drecv-ok _ ())
nat-case-refused (drecv-case _ (ok-val () _))

earlyCase : Proto
earlyCase = drecv "f" frameTy (pcase (byVal "g") frameArms)

early-case-refused : ¬ ProtoOk [] earlyCase
early-case-refused (drecv-ok _ ())
early-case-refused (drecv-case _ ())

loopCase : Proto
loopCase = drecv "f" frameTy (pcase (byRun "loop" "f" boolTy) lateArms)

loop-case-refused : ¬ ProtoOk [] loopCase
loop-case-refused (drecv-ok _ ())
loop-case-refused (drecv-case _ (ok-run () _ _ _))

shortCase : Proto
shortCase = drecv "f" frameTy (pcase (byVal "f") (("data" , end) ∷ []))

short-case-refused : ¬ ProtoOk [] shortCase
short-case-refused (drecv-ok _ ())
short-case-refused (drecv-case _ (ok-val () _))

extraCase : Proto
extraCase = drecv "f" frameTy (pcase (byVal "f") (
  ("data" , end) ∷ ("trailers" , end) ∷ ("headers" , end) ∷ ("pad" , end) ∷ []))

extra-case-refused : ¬ ProtoOk [] extraCase
extra-case-refused (drecv-ok _ ())
extra-case-refused (drecv-case _ (ok-val () _))

-- A bit is the other scrutinee. `b0` then `b1`.
bitCase : Proto
bitCase = drecv "b" bit (pcase (byVal "b") (("b0" , send nat end) ∷ ("b1" , end) ∷ []))

bitServer : Proc
bitServer = mget bit "b" (bare (put nat (lit zero) done) ∷ bare done ∷ [])

bit-server-ok : Conforms [] bitServer bitCase
bit-server-ok = mget-val refl bit-cov refl
  (at-cons (put-ok refl (lit-ok refl) done-end) (at-cons done-end at-nil))

opaque
  unfolding plainView bitPrep premises premReady premLab premRows premLen takeWalk asBit noD
  bit-server-decides : decide [] bitServer bitCase ≡ yes bit-server-ok
  bit-server-decides = refl

-- A call under the receive is guarded. The data arm opens `ack`.
sessSrv : SDecl
sessSrv = sdecl "srv" [] (q-drecv "f" frameTy (q-case (byVal "f") (
  ("data" , q-call "ack" []) ∷
  ("trailers" , q-end) ∷
  ("headers" , q-recv nat q-end) ∷ [])))

sess-srv :
  openTop (sessSrv ∷ sessAck ∷ []) "srv" []
    ≡ finite (drecv "f" frameTy (pcase (byVal "f") (
        ("data" , send bit end) ∷
        ("trailers" , end) ∷
        ("headers" , recv nat end) ∷ [])))
sess-srv = refl

sessGate : SDecl
sessGate = sdecl "gate" ("k" ∷ []) (q-drecv "b" bit (q-case (byVal "b") (
  ("b0" , q-send (vec nat (nvar "k")) q-end) ∷
  ("b1" , q-end) ∷ [])))

sess-gate :
  openTop (sessGate ∷ []) "gate" (saLit three ∷ [])
    ≡ finite (drecv "b" bit (pcase (byVal "b") (
        ("b0" , send (vec nat (nlit three)) end) ∷
        ("b1" , end) ∷ [])))
sess-gate = refl

-- The self-call sits under the receive, so the case keeps the guard.
sessLoopCase : SDecl
sessLoopCase = sdecl "lc" [] (q-drecv "f" frameTy (q-case (byVal "f") (
  ("data" , q-call "lc" []) ∷
  ("trailers" , q-end) ∷
  ("headers" , q-end) ∷ [])))

sess-loop-case : openTop (sessLoopCase ∷ []) "lc" [] ≡ looping
sess-loop-case = refl

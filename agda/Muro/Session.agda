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
-- data in the arm. Each arm conforms to the one continuation, and
-- the processes may differ. The meeting selects the arm of the value
-- that was sent and reads the fields of that value. A match that does not
-- cover the received value has no derivation. An indexed bit is
-- still the literal the sender writes.
--
-- A dependent continuation may also be a `case` on the name just
-- bound, or on a run applied to that name. The arms are one protocol
-- per constructor, in declaration order: of the payload, or of the
-- run's result. A sender whose value is known is checked on the arm
-- that value selects. A receiver matches every constructor of the
-- payload, and each process arm conforms to the protocol arm that
-- constructor selects. Selecting an arm is the same evaluator. It
-- uses no fuel. A case that is not that continuation, a scrutinee
-- other than a bit or a declared data type, a run outside the
-- fragment, and a sender whose value is not known when the arms
-- differ, have no derivation.
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
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _≤_; z≤n; s≤s) renaming (zero to nzero; suc to nsuc)
open import Data.Nat.Properties using () renaming (_≟_ to _≟ℕ_; _≤?_ to _≤?ℕ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
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
-- is a parameter. `fSelf` is this declaration, applied to payload
-- arguments. `fDat` is another such declaration. An index is not a
-- parameter, and a field that is a function is not a field here.
------------------------------------------------------------------------

mutual
  data Fld : Set where
    fNat  : Fld
    fBit  : Fld
    fUnit : Fld
    fPair : Fld → Fld → Fld
    fPar  : ℕ → Fld
    fSelf : List Fld → Fld
    fDat  : Decl → List Fld → Fld

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
  fld≟ fNat fBit = no′ (λ ())
  fld≟ fNat fUnit = no′ (λ ())
  fld≟ fNat (fPair _ _) = no′ (λ ())
  fld≟ fNat (fPar _) = no′ (λ ())
  fld≟ fNat (fSelf _) = no′ (λ ())
  fld≟ fNat (fDat _ _) = no′ (λ ())
  fld≟ fBit fNat = no′ (λ ())
  fld≟ fBit fBit = yes′ refl
  fld≟ fBit fUnit = no′ (λ ())
  fld≟ fBit (fPair _ _) = no′ (λ ())
  fld≟ fBit (fPar _) = no′ (λ ())
  fld≟ fBit (fSelf _) = no′ (λ ())
  fld≟ fBit (fDat _ _) = no′ (λ ())
  fld≟ fUnit fNat = no′ (λ ())
  fld≟ fUnit fBit = no′ (λ ())
  fld≟ fUnit fUnit = yes′ refl
  fld≟ fUnit (fPair _ _) = no′ (λ ())
  fld≟ fUnit (fPar _) = no′ (λ ())
  fld≟ fUnit (fSelf _) = no′ (λ ())
  fld≟ fUnit (fDat _ _) = no′ (λ ())
  fld≟ (fPair _ _) fNat = no′ (λ ())
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
  fld≟ (fPar _) fBit = no′ (λ ())
  fld≟ (fPar _) fUnit = no′ (λ ())
  fld≟ (fPar _) (fPair _ _) = no′ (λ ())
  fld≟ (fPar m) (fPar n) with m ≟ℕ n
  ... | yes′ refl = yes′ refl
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  fld≟ (fPar _) (fSelf _) = no′ (λ ())
  fld≟ (fPar _) (fDat _ _) = no′ (λ ())
  fld≟ (fSelf _) fNat = no′ (λ ())
  fld≟ (fSelf _) fBit = no′ (λ ())
  fld≟ (fSelf _) fUnit = no′ (λ ())
  fld≟ (fSelf _) (fPair _ _) = no′ (λ ())
  fld≟ (fSelf _) (fPar _) = no′ (λ ())
  fld≟ (fSelf fs) (fSelf gs) with flds≟ fs gs
  ... | yes′ refl = yes′ refl
  ... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
  fld≟ (fSelf _) (fDat _ _) = no′ (λ ())
  fld≟ (fDat _ _) fNat = no′ (λ ())
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
-- constructors of the run's result. The name is the binder.
------------------------------------------------------------------------

data Scrut : Set where
  byVal : String → Scrut
  byRun : String → String → Ty → Scrut

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

------------------------------------------------------------------------
-- The process is the run's actions on the channel. `put` sends a
-- value expression: a literal, a variable, or a call of a run
-- definition. `get` receives a value and binds it to a named
-- variable. The continuation may reference that variable. `mget`
-- receives and matches that same name. The arms are one per
-- constructor, `b0` then `b1` for a bit, and declaration order for
-- data. A bare arm carries no binders. A named arm names that
-- constructor and binds its fields, last name innermost. Each arm
-- conforms to the one continuation, and the processes may differ.
-- `pick0` and `pick1` are the process's choice. `cover` offers
-- both branches. `iget x P Q` receives a bit, binds it to `x`, and
-- offers both arms: `b0` continues as `P` and `b1` continues as `Q`.
-- `stop` uses the channel no further.
------------------------------------------------------------------------

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
  data PArm : Set where
    bare  : Proc → PArm
    named : String → List String → Proc → PArm

body : PArm → Proc
body (bare p) = p
body (named _ _ p) = p

------------------------------------------------------------------------
-- A parameter index, or nothing when the index is past the arguments.
------------------------------------------------------------------------

nth : ∀ {A : Set} → List A → ℕ → Maybe A
nth [] _ = nothing
nth (x ∷ _) nzero = just x
nth (_ ∷ xs) (nsuc n) = nth xs n

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

-- A literal inhabits its type when `fits` is true. A constructor the
-- declaration does not have, or a field of the wrong type, is false.
-- The recursion follows the spine of the value.
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
  ... | yes′ _ = fits v ∧ fitsFlds d as fs sp

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

-- Latest first. The tail of a definition is the earlier prefix.
runs : List RDef
runs =
  grantRun ∷ onJustRun ∷ lateFrameRun ∷ plusRun ∷ loopRun ∷ lateRun ∷ sizeRun ∷ badRun
    ∷ countRun ∷ effectiveRun ∷ markRun ∷ earlyRun ∷ []

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
  rawNat : ℕ → Raw
  rawBit : Val bit → Raw
  rawUnit : Raw
  rawPair : Raw → Raw → Raw
  rawCon : String → List Raw → Raw

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
  rawOf (rec _) = nothing
  rawOf (rep _) = nothing

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
  cast (dat d as) (rawCon c rs) = castFound d as c rs (findCtor (ctorsOf d) c)
  cast _ _ = nothing

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

scrutEq : Scrut → Scrut → Bool
scrutEq (byVal x) (byVal y) = x == y
scrutEq (byRun f x R) (byRun g y S) = (f == g) ∧ (x == y) ∧ eqTy R S
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

toℕ : Val nat → ℕ
toℕ zero = nzero
toℕ (suc n) = nsuc (toℕ n)

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
-- Probing a constructor passes no fields: an arm that reads a field
-- does not decide, and no field value is invented.
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

zipVal : List (String × Proto) → List Proc → Maybe (List (Proc × Proto))
zipVal [] [] = just []
zipVal ((_ , S) ∷ as) (p ∷ ps) = bindM (zipVal as ps) (λ rs → just ((p , S) ∷ rs))
zipVal _ _ = nothing

zipRun : String → Ty → Ty → List (String × Proto) → List String → List Proc → Maybe (List (Proc × Proto))
zipRun _ _ _ _ [] [] = just []
zipRun f A R arms (c ∷ cs) (p ∷ ps) =
  bindM (evalAt f A c R) (λ r →
    bindM (valCtor r) (λ k →
      bindM (findArm k arms) (λ S →
        bindM (zipRun f A R arms cs ps) (λ rs → just ((p , S) ∷ rs)))))
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
  call-le : ∀ {f as v e} →
    evalExpr (call {nat} f as) ≡ just v →
    Le Γ (lit v) e →
    Le Γ (call f as) e

data Owed (Γ : Ctx) (v : ValExpr nat) : Maybe NExp → Set where
  owed : ∀ {e} → Le Γ v e → Owed Γ v (just e)

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
-- A nat, unit, a pair, a record, a vector, or the wrong number of
-- arms does not cover. A case is the continuation of the dependent
-- action that binds the scrutinee. The sender is checked on the
-- selected arm. The receiver is checked on every arm. The fields do
-- not choose the protocol arm.
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
fieldsNamed _ _ = nothing

armCtxNamed : Ty → String → List String → Ctx → Maybe Ctx
armCtxNamed A c xs Γ = bindM (fieldsNamed A c) (λ ts → extend xs ts Γ)

mutual
  data Covered : Ty → List PArm → Set where
    bit-cov : ∀ {p q} → Covered bit (p ∷ q ∷ [])
    dat-cov : ∀ {d as ps} → length ps ≡ length (ctorsOf d) → Covered (dat d as) ps

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

  -- One process per protocol arm, in order. The process is a subterm
  -- of the match, so the check recurses on it. A named arm binds the
  -- fields of that constructor. The protocol arm was chosen with no fields.
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

  -- A computed case. Each constructor of the payload is evaluated
  -- with no fields, and the process arm conforms to the arm of that
  -- result. A named process arm still binds the payload's fields.
  data ArmsRun (Γ : Ctx) (ρ : Idx) (f : String) (A R : Ty)
      (arms : List (String × Proto)) : List String → List PArm → Set where
    run-nil   : ArmsRun Γ ρ f A R arms [] []
    run-cons  : ∀ {c cs p ps r k S} →
      evalAt f A c R ≡ just r →
      valCtor r ≡ just k →
      findArm k arms ≡ just S →
      Conformsρ Γ ρ p S →
      ArmsRun Γ ρ f A R arms cs ps →
      ArmsRun Γ ρ f A R arms (c ∷ cs) (bare p ∷ ps)
    run-named : ∀ {c cs xs p Δ ps r k S} →
      evalAt f A c R ≡ just r →
      valCtor r ≡ just k →
      findArm k arms ≡ just S →
      armCtxNamed A c xs Γ ≡ just Δ →
      Conformsρ Δ ρ p S →
      ArmsRun Γ ρ f A R arms cs ps →
      ArmsRun Γ ρ f A R arms (c ∷ cs) (named c xs p ∷ ps)

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

    -- The name is the one `mget` just bound. Each arm is that continuation.
    -- A named arm's context also holds the constructor's fields.
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

-- `pickCtor` receives the Boolean comparison. `nthProc` makes it.
-- A meeting follows that same comparison, so the equality is the one
-- `pickCtor` computes. The false branch is the tail of the constructor list.
-- A bare arm is the stored process. A named arm is that process with
-- the value's fields substituted for its binders.
mutual
  pickCtor : Bool → PArm → Spine → List Ctor → String → List PArm → Maybe Proc
  pickCtor true (bare p) _ _ _ _ = just p
  pickCtor true (named k xs p) sp _ c _ = openNamed k c xs p sp
  pickCtor false _ sp cs name ps = nthProc cs name sp ps

  nthProc : List Ctor → String → Spine → List PArm → Maybe Proc
  nthProc [] _ _ _ = nothing
  nthProc (_ ∷ _) _ _ [] = nothing
  nthProc (ctor n _ ∷ cs) c sp (a ∷ ps) = pickCtor (c == n) a sp cs c ps

armOf : (A : Ty) → Val A → List PArm → Maybe Proc
armOf bit b0 [] = nothing
armOf bit b0 (_ ∷ []) = nothing
armOf bit b0 (_ ∷ _ ∷ _ ∷ _) = nothing
armOf bit b0 (bare p ∷ _ ∷ []) = just p
armOf bit b0 (named _ [] p ∷ _ ∷ []) = just p
armOf bit b0 (named _ (_ ∷ _) _ ∷ _ ∷ []) = nothing
armOf bit b1 [] = nothing
armOf bit b1 (_ ∷ []) = nothing
armOf bit b1 (_ ∷ _ ∷ _ ∷ _) = nothing
armOf bit b1 (_ ∷ bare q ∷ []) = just q
armOf bit b1 (_ ∷ named _ [] q ∷ []) = just q
armOf bit b1 (_ ∷ named _ (_ ∷ _) _ ∷ []) = nothing
armOf nat _ _ = nothing
armOf unit _ _ = nothing
armOf (pair _ _) _ _ = nothing
armOf (rec _) _ _ = nothing
armOf (vec _ _) _ _ = nothing
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
  ff-nat  : ∀ {Γ d as} → FieldFit Γ d as fNat
  ff-bit  : ∀ {Γ d as} → FieldFit Γ d as fBit
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
  Dec (ValExprOk Γ v) →
  Answerρ Γ (bind y (ixOf A v) (shadow y ρ)) P S →
  Answerρ Γ ρ (put A v P) (dsend y B S)
on-dput pl (yes′ vok) (yes d) = yes (dput-ok refl vok pl d)
on-dput pl (yes′ _) (no nd) = no (λ where
  (dput-ok refl _ _ d) → nd d
  (dput-arm _ _ _ _) → plain-not pl)
on-dput pl (no′ nvok) _ = no (λ where
  (dput-ok refl vok _ _) → nvok vok
  (dput-arm _ vok _ _) → plain-not pl)

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

cover? : (A : Ty) (ps : List PArm) → Dec (Covered A ps)
cover? bit [] = no′ (λ ())
cover? bit (_ ∷ []) = no′ (λ ())
cover? bit (_ ∷ _ ∷ []) = yes′ bit-cov
cover? bit (_ ∷ _ ∷ _ ∷ _) = no′ (λ ())
cover? nat _ = no′ (λ ())
cover? unit _ = no′ (λ ())
cover? (pair _ _) _ = no′ (λ ())
cover? (rec _) _ = no′ (λ ())
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
  decideρ Γ ρ (put A v P) (dsend y B S) with ty≟ A (applyTy ρ B)
  ... | yes′ refl = sendBy Γ ρ y v P B S refl
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
  decideρ Γ ρ (mget A x ps) (recv B S) =
    on-mget (ty≟ A (applyTy ρ B)) (cover? A ps) (decideArms ((x , A) ∷ Γ) ρ A nzero ps S)
  decideρ Γ ρ (mget _ _ _) end = no (λ ())
  decideρ Γ ρ (mget _ _ _) (send _ _) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (dsend _ _ _) = no (λ ())
  decideρ Γ ρ (mget A x ps) (drecv y B (pcase (byVal z) arms)) with z ≟ y
  ... | no′ z≢y = no (λ { (mget-val _ _ _ _) → z≢y refl })
  ... | yes′ refl with ty≟ A (applyTy ρ B)
  ... | no′ ¬eq = no (λ { (mget-val eq _ _ _) → ¬eq eq })
  ... | yes′ refl with cover? A ps
  ... | no′ nc = no (λ { (mget-val _ c _ _) → nc c })
  ... | yes′ c with labelled A arms in lb
  ... | false = no (λ { (mget-val _ _ p _) → true≢false (trans (sym p) lb) })
  ... | true = on-at c lb (decideAt ((x , A) ∷ Γ) (renameIdx y x (shadow y ρ)) A arms ps)
  decideρ Γ ρ (mget A x ps) (drecv y B (pcase (byRun f z R) arms)) with z ≟ y
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
  decideρ Γ ρ (mget _ _ _) (drecv _ _ end) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (drecv _ _ (send _ _)) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (drecv _ _ (recv _ _)) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (drecv _ _ (dsend _ _ _)) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (drecv _ _ (drecv _ _ _)) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (drecv _ _ (esend _ _ _)) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (drecv _ _ (erecv _ _ _)) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (drecv _ _ (isend _ _ _)) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (drecv _ _ (irecv _ _ _)) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (drecv _ _ (choose _ _)) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (drecv _ _ (branch _ _)) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (esend _ _ _) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (erecv _ _ _) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (isend _ _ _) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (irecv _ _ _) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (choose _ _) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (branch _ _) = no (λ ())
  decideρ Γ ρ (mget _ _ _) (pcase _ _) = no (λ ())

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
  decideAt Γ ρ A [] (_ ∷ _) = no-at (λ ())
  decideAt Γ ρ A (_ ∷ _) [] = no-at (λ ())

  decideRun : (Γ : Ctx) (ρ : Idx) (f : String) (A R : Ty) (arms : List (String × Proto))
    (cs : List String) (ps : List PArm) → AnswerRun Γ ρ f A R arms cs ps
  decideRun Γ ρ f A R arms [] [] = yes-cr run-nil
  decideRun Γ ρ f A R arms (c ∷ cs) (bare p ∷ ps) with evalAt f A c R in er
  ... | nothing = no-cr (λ { (run-cons q _ _ _ _) → just≢nothing (trans (sym q) er) })
  ... | just r with valCtor r in ek
  ... | nothing = no-cr (λ { (run-cons q k _ _ _) →
        just≢nothing (trans (sym k) (trans (cong valCtor (just-inj (trans (sym q) er))) ek)) })
  ... | just k with findArm k arms in ef
  ... | nothing = no-cr (λ { (run-cons q kp sp _ _) →
        just≢nothing (trans (sym sp)
          (trans (cong (λ n → findArm n arms)
            (just-inj (trans (sym kp)
              (trans (cong valCtor (just-inj (trans (sym q) er))) ek))))
            ef)) })
  ... | just S with decideρ Γ ρ p S
  ... | no nd = no-cr (λ { (run-cons q kp sp d _) →
        nd (subst (λ T → Conformsρ Γ ρ p T)
          (just-inj (trans (sym sp)
            (trans (cong (λ n → findArm n arms)
              (just-inj (trans (sym kp)
                (trans (cong valCtor (just-inj (trans (sym q) er))) ek))))
              ef)))
          d) })
  ... | yes d with decideRun Γ ρ f A R arms cs ps
  ... | yes-cr ds = yes-cr (run-cons er ek ef d ds)
  ... | no-cr nd = no-cr (λ { (run-cons _ _ _ _ ds) → nd ds })
  decideRun Γ ρ f A R arms (c ∷ cs) (named k xs p ∷ ps) with c ≟ k
  ... | no′ c≢k = no-cr (λ { (run-named _ _ _ _ _ _) → c≢k refl })
  ... | yes′ refl with evalAt f A c R in er
  ... | nothing = no-cr (λ { (run-named q _ _ _ _ _) → just≢nothing (trans (sym q) er) })
  ... | just r with valCtor r in ek
  ... | nothing = no-cr (λ { (run-named q k′ _ _ _ _) →
        just≢nothing (trans (sym k′) (trans (cong valCtor (just-inj (trans (sym q) er))) ek)) })
  ... | just k′ with findArm k′ arms in ef
  ... | nothing = no-cr (λ { (run-named q kp sp _ _ _) →
        just≢nothing (trans (sym sp)
          (trans (cong (λ n → findArm n arms)
            (just-inj (trans (sym kp)
              (trans (cong valCtor (just-inj (trans (sym q) er))) ek))))
            ef)) })
  ... | just S with armCtxNamed A c xs Γ in ac
  ... | nothing = no-cr (λ { (run-named _ _ _ q _ _) → just≢nothing (trans (sym q) ac) })
  ... | just Δ with decideρ Δ ρ p S
  ... | no nd = no-cr (λ { (run-named {Δ = Δ′} q kp sp ctx d _) →
        nd (subst (λ Θ → Conformsρ Θ ρ p S) (just-inj (trans (sym ctx) ac))
          (subst (λ T → Conformsρ Δ′ ρ p T)
            (just-inj (trans (sym sp)
              (trans (cong (λ n → findArm n arms)
                (just-inj (trans (sym kp)
                  (trans (cong valCtor (just-inj (trans (sym q) er))) ek))))
                ef)))
            d)) })
  ... | yes d with decideRun Γ ρ f A R arms cs ps
  ... | yes-cr ds = yes-cr (run-named er ek ef ac d ds)
  ... | no-cr nd = no-cr (λ { (run-named _ _ _ _ _ ds) → nd ds })
  decideRun _ _ _ _ _ _ [] (_ ∷ _) = no-cr (λ ())
  decideRun _ _ _ _ _ _ (_ ∷ _) [] = no-cr (λ ())

  sendBy : (Γ : Ctx) (ρ : Idx) {A : Ty} (y : String) (v : ValExpr A) (P : Proc)
    (B : Ty) (S : Proto) → A ≡ applyTy ρ B →
    Answerρ Γ ρ (put A v P) (dsend y B S)
  sendBy Γ ρ {A} y v P B (pcase scrut arms) refl
    with selectProto y v scrut arms in eq
  ... | nothing = no (λ where
        (dput-ok _ _ pl _) → plain-not pl
        (dput-arm _ _ p _) → just≢nothing (trans (sym p) eq))
  ... | just T with decideValExpr Γ v
  ... | no′ nv = no (λ where
        (dput-ok _ vok _ _) → nv vok
        (dput-arm _ vok _ _) → nv vok)
  ... | yes′ vok with decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P T
  ... | yes d = yes (dput-arm refl vok eq d)
  ... | no nd = no (λ where
        (dput-ok _ _ pl _) → plain-not pl
        (dput-arm _ _ p d) →
          nd (subst (λ S → Conformsρ Γ (bind y (ixOf A v) (shadow y ρ)) P S)
                (just-inj (trans (sym p) eq)) d))
  sendBy Γ ρ {A} y v P B end refl =
    on-dput plain-end (decideValExpr Γ v) (decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P end)
  sendBy Γ ρ {A} y v P B (send C S) refl =
    on-dput plain-send (decideValExpr Γ v) (decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P (send C S))
  sendBy Γ ρ {A} y v P B (recv C S) refl =
    on-dput plain-recv (decideValExpr Γ v) (decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P (recv C S))
  sendBy Γ ρ {A} y v P B (dsend z C S) refl =
    on-dput plain-dsend (decideValExpr Γ v) (decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P (dsend z C S))
  sendBy Γ ρ {A} y v P B (drecv z C S) refl =
    on-dput plain-drecv (decideValExpr Γ v) (decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P (drecv z C S))
  sendBy Γ ρ {A} y v P B (esend z e S) refl =
    on-dput plain-esend (decideValExpr Γ v) (decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P (esend z e S))
  sendBy Γ ρ {A} y v P B (erecv z e S) refl =
    on-dput plain-erecv (decideValExpr Γ v) (decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P (erecv z e S))
  sendBy Γ ρ {A} y v P B (isend z S T) refl =
    on-dput plain-isend (decideValExpr Γ v) (decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P (isend z S T))
  sendBy Γ ρ {A} y v P B (irecv z S T) refl =
    on-dput plain-irecv (decideValExpr Γ v) (decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P (irecv z S T))
  sendBy Γ ρ {A} y v P B (choose S T) refl =
    on-dput plain-choose (decideValExpr Γ v) (decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P (choose S T))
  sendBy Γ ρ {A} y v P B (branch S T) refl =
    on-dput plain-branch (decideValExpr Γ v) (decideρ Γ (bind y (ixOf A v) (shadow y ρ)) P (branch S T))

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
left-open = put-ok refl (lit-ok refl) abandon

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
sized-server-ok = dget-ok refl (put-ok refl (lit-ok refl) done-end)

sized-client-ok : Conforms [] sized-client (dsend "n" nat (recv (vec nat (nvar "n")) end))
sized-client-ok = dput-ok refl (lit-ok refl) plain-recv (get-ok refl done-end)

sized-server-decides : decide [] sized-server sized ≡ yes sized-server-ok
sized-server-decides = refl

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
empty-ok = dget-ok refl (eput-ok (lit-ok refl) (owed zero-le) done-end)

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
  dput-ok refl (lit-ok refl) plain-esend
    (eput-ok (lit-ok refl) (owed (lit-le (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))) done-end)

within-decides : decide [] within granted ≡ yes within-ok
within-decides = refl

-- `d > w`: nine is not at most eight.
over : Proc
over = put nat (lit (num 8)) (put nat (lit (num 9)) done)

over-refused : ¬ Conforms [] over granted
over-refused
  (dput-ok refl _ _ (eput-ok _ (owed (lit-le (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s ())))))))))) _))

over-decides : decide [] over granted ≡ no over-refused
over-decides = refl

-- A numeral bound in the protocol.
frame : Proto
frame = esend "d" (nlit 16384) end

frame-ok : Conforms [] (put nat (lit zero) done) frame
frame-ok = eput-ok (lit-ok refl) (owed (lit-le z≤n)) done-end

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
route-server-ok = iget-ok (put-ok refl (lit-ok refl) done-end) (get-ok refl done-end)

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

up-decides : decide [] up flag ≡ yes up-ok
up-decides = refl

bad-bool : ¬ Conforms [] (put boolTy (lit noneV) done) flag
bad-bool (put-ok refl (lit-ok ()) _)

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

effReply-decides : decide [] effReply effAnswer ≡ yes effReply-ok
effReply-decides = refl

countCall : ValExpr boolTy
countCall = call "count" []

bad-count : ¬ Conforms [] (put boolTy countCall done) (send boolTy end)
bad-count (put-ok refl (call-ok p _) _) = just≢nothing (trans (sym p) loop-count)
  where loop-count : evalExpr countCall ≡ nothing
        loop-count = refl
bad-count (put-ok refl (call-ty m _ _ _) _) = true≢false (trans (sym m) refl)

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
size-under = eput-ok (call-ok size-self-eval refl) (owed size-le) done-end

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

bitTaker-decides : decide [] bitTaker bitChoice ≡ yes bitTaker-ok
bitTaker-decides = refl

boolChoice : Proto
boolChoice = recv boolTy end

boolTaker : Proc
boolTaker = mget boolTy "b" (bare done ∷ bare done ∷ [])

bool-taker-ok : Conforms [] boolTaker boolChoice
bool-taker-ok = mget-ok refl (dat-cov refl) (arms-cons done-end (arms-cons done-end arms-nil))

bool-taker-decides : decide [] boolTaker boolChoice ≡ yes bool-taker-ok
bool-taker-decides = refl

optChoice : Proto
optChoice = recv maybeNat end

optTaker : Proc
optTaker = mget maybeNat "m" (bare done ∷ bare done ∷ [])

opt-taker-ok : Conforms [] optTaker optChoice
opt-taker-ok = mget-ok refl (dat-cov refl) (arms-cons done-end (arms-cons done-end arms-nil))

opt-taker-decides : decide [] optTaker optChoice ≡ yes opt-taker-ok
opt-taker-decides = refl

shortMatch : Proc
shortMatch = mget bit "b" (bare done ∷ [])

short-refused : ¬ Conforms [] shortMatch (recv bit end)
short-refused (mget-ok refl () _)

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

frame-server-decides : decide [] frameServer frameCase ≡ yes frame-server-ok
frame-server-decides = refl

-- Headers selects the third arm. The data arm is not checked.
frameClient : Proc
frameClient = put frameTy (lit headV) (put nat (lit zero) done)

frame-client-ok : Conforms [] frameClient frameClientProto
frame-client-ok = dput-arm refl (lit-ok refl) refl (put-ok refl (lit-ok refl) done-end)

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
  (run-cons refl refl refl (put-ok refl (lit-ok refl) done-end)
    (run-cons refl refl refl (put-ok refl (lit-ok refl) done-end)
      (run-cons refl refl refl (put-ok refl (lit-ok refl) done-end) run-nil)))

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
late-goaway (mget-run _ _ _ _ refl (run-cons refl refl refl (put-ok () _ _) _))

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
onJust-recv (mget-run _ _ _ _ refl (run-cons refl refl refl done-end (run-cons () _ _ _ _)))

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
  (at-cons (eput-ok (lit-ok refl) (owed (lit-le z≤n)) done-end)
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

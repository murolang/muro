------------------------------------------------------------------------
-- Multiplicity on a session endpoint. A binder is affine by default:
-- at most one use. A session endpoint may be bound linearly, and then
-- it is used exactly once. The obligation is the multiplicity of the
-- value, so it travels when the value is returned, passed, or dualised.
--
-- A linear binder is the surface `λ¹`. An arrow that accepts or
-- returns a linear endpoint is the surface `⊸`. Both are this
-- multiplicity. The quantity underneath is affine. `checkMult` for
-- the linear multiplicity is `checkArrow` for `%1`: `checkBound` for
-- the affine quantity, then the must-use check. An affine endpoint
-- is `checkBound` alone, so an unused affine endpoint is accepted
-- and a second use is still the affine refusal.
--
-- `dualS` keeps the multiplicity and dualises the protocol. The
-- protocol is the finite syntax of `Muro.Rec`, so a repeating
-- protocol is `mu` and a declared data payload is a `Ty` inside
-- `send` or `recv`. `dualS` keeps `mu`, keeps the variable, and
-- keeps the payload. This module does not unfold the coinductive
-- protocol. Its recursion is structural on that finite syntax.
-- Importing `Muro.Rec` requires `--guardedness`, which `--safe`
-- allows.
--
-- A meeting keeps the multiplicity. It refuses a linear endpoint
-- that is not consumed exactly once: the two sides are dual, and
-- each side's consumption is one use. Abandoning a linear channel
-- is that refusal. An affine meeting still abandons.
--
-- Ordinary data, evidence, and run terms stay affine or erased.
-- Neither multiplicity is a constructor of Qty. None of these
-- constructors is added to Tm. The protocol stays spec. The process
-- stays evidence. The endpoint function is evidence, so it is erased
-- before emit. The OTP image carries the value.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Linear where

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not)
open import Data.List.Base using (List; []; _∷_)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.String.Base using (String)
open import Data.String.Properties using () renaming (_≟_ to _≟S_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary.Decidable.Core using (⌊_⌋)

open import Muro.Base using
  (Mode; evid; spec; Qty; affine; Use; U0; U1; Uω; Result; ok; fail; guard; _>>=_; _>>_)
open import Muro.Env using (checkBound; combine; oneHot)
open import Muro.Arrow using (m1; checkArrow)
open import Muro.Session using
  ( nat; bit; boolTy; maybeBool
  ; ty≟; nexp≟
  ; Proc; done; stop; put; get; pick0; pick1; cover; iget; mget
  ; lit; b0
  ; effCall; bitTaker
  ; pong)
open import Muro.Dual using (peer)
open import Muro.Rec using
  ( SExp; dualS
  ; end; send; recv; dsend; drecv; esend; erecv; isend; irecv; choose; branch
  ; svar; mu)
open import Muro.Meet using (bitGiver) renaming (decide to meetDecide; yes to meetYes; no to meetNo)

------------------------------------------------------------------------
-- Affine is the default. Linear is exactly once. Both sit on the
-- affine quantity.
------------------------------------------------------------------------

data Mult : Set where
  aff : Mult
  lin : Mult

qty : Mult → Qty
qty aff = affine
qty lin = affine

qty-affine : qty lin ≡ affine
qty-affine = refl

eqMult : Mult → Mult → Bool
eqMult aff aff = true
eqMult lin lin = true
eqMult _   _   = false

-- Affine is the existing bound. Linear is the existing must-use check.
checkMult : Mode → Mult → Use → Result ⊤
checkMult m aff u = checkBound m (qty aff) u
checkMult m lin u = checkArrow m m1 u

aff-drop : checkMult evid aff U0 ≡ ok tt
aff-drop = refl

aff-once : checkMult evid aff U1 ≡ ok tt
aff-once = refl

aff-many : checkMult evid aff Uω ≡ fail "affine variable used as reusable"
aff-many = refl

lin-once : checkMult evid lin U1 ≡ ok tt
lin-once = refl

lin-drop : checkMult evid lin U0 ≡ fail "linear variable unused"
lin-drop = refl

lin-many : checkMult evid lin Uω ≡ fail "affine variable used as reusable"
lin-many = refl

-- Spec forgets uses, as `checkArrow` does.
spec-drop : checkMult spec lin U0 ≡ ok tt
spec-drop = refl

------------------------------------------------------------------------
-- An endpoint term is not a Tm. `met` is the surface `done`: the
-- meeting has consumed the endpoints.
------------------------------------------------------------------------

data ETy : Set
data ETm (n : ℕ) : Set

data ETy where
  sess : Mult → SExp → ETy
  arr  : Mult → ETy → ETy → ETy
  met  : ETy

data ETm n where
  var  : Fin n → ETm n
  lam  : Mult → ETy → ETm (suc n) → ETm n
  app  : ETm n → ETm n → ETm n
  dualₑ : ETm n → ETm n
  meet : ETm n → ETm n → ETm n

-- A session name is in scope in Agda as its protocol. The surface
-- writes the name; elaboration resolves it before this judgment.
Ctx : ℕ → Set
Ctx n = Vec ETy n

------------------------------------------------------------------------
-- The obligation travels with the value. An arrow is linear when
-- its domain or its codomain carries a linear endpoint.
------------------------------------------------------------------------

carries : ETy → Bool
carries (sess lin _) = true
carries (sess aff _) = false
carries (arr _ A B)  = carries A ∨ carries B
carries met          = false

arrowOk : Mult → ETy → ETy → Bool
arrowOk lin A B = carries A ∨ carries B
arrowOk aff A B = not (carries A) ∧ not (carries B)

-- A linear binder binds a session endpoint. An affine binder does
-- not bind a linear one: that obligation would be lost.
bindOk : Mult → ETy → Bool
bindOk lin (sess lin _) = true
bindOk lin _            = false
bindOk aff (sess lin _) = false
bindOk aff _            = true

protoEq : SExp → SExp → Bool
protoEq end end = true
protoEq (send A S) (send B T) = ⌊ ty≟ A B ⌋ ∧ protoEq S T
protoEq (recv A S) (recv B T) = ⌊ ty≟ A B ⌋ ∧ protoEq S T
protoEq (dsend x A S) (dsend y B T) = ⌊ x ≟S y ⌋ ∧ ⌊ ty≟ A B ⌋ ∧ protoEq S T
protoEq (drecv x A S) (drecv y B T) = ⌊ x ≟S y ⌋ ∧ ⌊ ty≟ A B ⌋ ∧ protoEq S T
protoEq (esend x e S) (esend y f T) = ⌊ x ≟S y ⌋ ∧ ⌊ nexp≟ e f ⌋ ∧ protoEq S T
protoEq (erecv x e S) (erecv y f T) = ⌊ x ≟S y ⌋ ∧ ⌊ nexp≟ e f ⌋ ∧ protoEq S T
protoEq (isend x S T) (isend y U V) = ⌊ x ≟S y ⌋ ∧ protoEq S U ∧ protoEq T V
protoEq (irecv x S T) (irecv y U V) = ⌊ x ≟S y ⌋ ∧ protoEq S U ∧ protoEq T V
protoEq (choose S T) (choose U V) = protoEq S U ∧ protoEq T V
protoEq (branch S T) (branch U V) = protoEq S U ∧ protoEq T V
protoEq (svar x) (svar y) = ⌊ x ≟S y ⌋
protoEq (mu x s) (mu y t) = ⌊ x ≟S y ⌋ ∧ protoEq s t
protoEq _ _ = false

eqETy : ETy → ETy → Bool
eqETy (sess q S) (sess q' T) = eqMult q q' ∧ protoEq S T
eqETy (arr q A B) (arr q' A' B') = eqMult q q' ∧ eqETy A A' ∧ eqETy B B'
eqETy met met = true
eqETy _ _ = false

mismatch : ETy → ETy → String
mismatch (arr q _ _) (arr q' _ _) with eqMult q q'
... | false = "λ/arrow multiplicity mismatch"
... | true  = "endpoint type mismatch"
mismatch _ _ = "endpoint type mismatch"

-- One consumption of the endpoint the meeting is given. A variable
-- is one use. Duality and an application pass that use on. A second
-- meeting is not one use.
spent : ∀ {n} → ETm n → Use
spent (var _)      = U1
spent (dualₑ t)    = spent t
spent (app _ a)    = spent a
spent (lam _ _ _)  = U0
spent (meet _ _)   = Uω

-- The two endpoints meet when they carry one multiplicity and the
-- second protocol is the dual of the first.
meetTy : ETy → ETy → Result Mult
meetTy (sess q S) (sess q' T) =
  guard "multiplicity mismatch" (eqMult q q') >>
  guard "expected the other end" (protoEq T (dualS S)) >>
  ok q
meetTy _ _ = fail "a meeting meets session endpoints"

------------------------------------------------------------------------
-- Inference. Structural on the endpoint term. The mode is evidence
-- for an endpoint function, so uses count. Spec forgets them, by
-- `combine` and `checkMult`.
------------------------------------------------------------------------

infer : ∀ {n} → Mode → Ctx n → ETm n → Result (ETy × Vec Use n)
infer _ Γ (var i) = ok (lookup Γ i , oneHot i U1)
infer m Γ (lam q A t) =
  guard "a linear binder binds a session endpoint" (bindOk q A) >>
  infer m (A ∷ Γ) t >>= λ where
    (B , u ∷ us) →
      guard "linear arrow is ⊸" (arrowOk q A B) >>
      checkMult m q u >>
      ok (arr q A B , us)
infer m Γ (app f a) =
  infer m Γ f >>= λ where
    (arr q A B , uf) →
      infer m Γ a >>= λ (Aa , ua) →
      guard (mismatch A Aa) (eqETy A Aa) >>
      combine m uf ua >>= λ us →
      ok (B , us)
    (_ , _) → fail "expected an arrow"
infer m Γ (dualₑ t) =
  infer m Γ t >>= λ where
    (sess q S , u) → ok (sess q (dualS S) , u)
    (_ , _) → fail "dual of a session endpoint"
infer m Γ (meet t u) =
  infer m Γ t >>= λ (At , ut) →
  infer m Γ u >>= λ (Au , uu) →
  meetTy At Au >>= λ q →
  combine m ut uu >>= λ us →
  checkMult m q (spent t) >>
  checkMult m q (spent u) >>
  ok (met , us)

check : ∀ {n} → Mode → Ctx n → ETy → ETm n → Result (Vec Use n)
check m Γ A t =
  infer m Γ t >>= λ (B , u) →
  guard (mismatch A B) (eqETy A B) >>
  ok u

------------------------------------------------------------------------
-- A process consumes its endpoint once when it finishes, and not at
-- all when it abandons. A cover consumes once when both arms do. A
-- match consumes once when every arm does. An empty match consumes
-- once. `meetProc` is a meeting of those consumptions. Affine
-- abandonment stays. A linear endpoint that is not consumed once is
-- refused.
------------------------------------------------------------------------

once : Use → Use → Use
once U1 U1 = U1
once _  _  = U0

mutual
  consume : Proc → Use
  consume done = U1
  consume stop = U0
  consume (put _ _ P) = consume P
  consume (get _ _ P) = consume P
  consume (pick0 P) = consume P
  consume (pick1 P) = consume P
  consume (cover P Q) = once (consume P) (consume Q)
  consume (iget _ P Q) = once (consume P) (consume Q)
  consume (mget _ _ ps) = arms ps

  arms : List Proc → Use
  arms [] = U1
  arms (p ∷ ps) = once (consume p) (arms ps)

meetProc : Mult → Proc → Proc → Result ⊤
meetProc q P Q with meetDecide P Q
... | meetYes _ = checkMult evid q (consume P) >> checkMult evid q (consume Q)
... | meetNo  _ = fail "processes do not meet"

------------------------------------------------------------------------
-- `(s : ping) ⊸ ping`, written `λ¹ (s : ping) → s`.
-- `ping` is finite syntax, the same carrier as `rec` and a `dat` payload.
-- `reqS` is the protocol `req` opens to: a nat, then `ack`.
------------------------------------------------------------------------

ping : SExp
ping = recv nat (send nat end)

reqS : SExp
reqS = send nat (send bit end)

reqPassTy : ETy
reqPassTy = arr lin (sess lin reqS) (sess lin reqS)

reqPass : ETm 0
reqPass = lam lin (sess lin reqS) (var fzero)

reqPass-ok : check evid [] reqPassTy reqPass ≡ ok []
reqPass-ok = refl

forwardTy : ETy
forwardTy = arr lin (sess lin ping) (sess lin ping)

forward : ETm 0
forward = lam lin (sess lin ping) (var fzero)

forward-ok : check evid [] forwardTy forward ≡ ok []
forward-ok = refl

-- Duality keeps the linear multiplicity.
backedTy : ETy
backedTy = arr lin (sess lin ping) (sess lin (dualS ping))

backed : ETm 0
backed = lam lin (sess lin ping) (dualₑ (var fzero))

backed-ok : check evid [] backedTy backed ≡ ok []
backed-ok = refl

dual-keeps :
  infer evid (sess lin ping ∷ []) (dualₑ (var fzero))
    ≡ ok (sess lin (dualS ping) , U1 ∷ [])
dual-keeps = refl

-- A matching pair. Each linear endpoint is consumed once.
wireTy : ETy
wireTy = arr lin (sess lin ping) (arr lin (sess lin (dualS ping)) met)

wire : ETm 0
wire =
  lam lin (sess lin ping)
    (lam lin (sess lin (dualS ping))
      (meet (var (fsuc fzero)) (var fzero)))

wire-ok : check evid [] wireTy wire ≡ ok []
wire-ok = refl

-- The meeting of the two processes, linear on both ends.
lin-meet : meetProc lin pong peer ≡ ok tt
lin-meet = refl

-- An unused linear endpoint is refused.
unusedTy : ETy
unusedTy = arr lin (sess lin ping) (arr lin (sess lin ping) (sess lin ping))

unused : ETm 0
unused = lam lin (sess lin ping) (lam lin (sess lin ping) (var fzero))

unused-no : check evid [] unusedTy unused ≡ fail "linear variable unused"
unused-no = refl

lin-stop : meetProc lin stop stop ≡ fail "linear variable unused"
lin-stop = refl

-- A linear endpoint used twice is the affine refusal. The meeting
-- is where the two uses are combined.
twiceTy : ETy
twiceTy = arr lin (sess lin ping) met

twice : ETm 0
twice = lam lin (sess lin ping) (meet (var fzero) (dualₑ (var fzero)))

twice-no : check evid [] twiceTy twice ≡ fail "affine variable used twice"
twice-no = refl

-- Affine behaviour is unchanged: an unused affine endpoint checks,
-- and abandoning an affine channel checks.
forgetTy : ETy
forgetTy = arr aff (sess aff ping) (arr aff (sess aff ping) (sess aff ping))

forget : ETm 0
forget = lam aff (sess aff ping) (lam aff (sess aff ping) (var fzero))

forget-ok : check evid [] forgetTy forget ≡ ok []
forget-ok = refl

aff-stop : meetProc aff stop stop ≡ ok tt
aff-stop = refl

aff-twiceTy : ETy
aff-twiceTy = arr aff (sess aff ping) met

aff-twice : ETm 0
aff-twice = lam aff (sess aff ping) (meet (var fzero) (dualₑ (var fzero)))

aff-twice-no : check evid [] aff-twiceTy aff-twice ≡ fail "affine variable used twice"
aff-twice-no = refl

-- The obligation travels through an application.
travel : ETm 1
travel = app (lam lin (sess lin ping) (var fzero)) (var fzero)

travel-ok :
  infer evid (sess lin ping ∷ []) travel
    ≡ ok (sess lin ping , U1 ∷ [])
travel-ok = refl

------------------------------------------------------------------------
-- A linear endpoint of a repeating protocol. `dualS` keeps `mu`.
------------------------------------------------------------------------

loopProto : SExp
loopProto = mu "X" (recv nat (send nat (svar "X")))

echoTy : ETy
echoTy = arr lin (sess lin loopProto) (sess lin loopProto)

echo : ETm 0
echo = lam lin (sess lin loopProto) (var fzero)

echo-ok : check evid [] echoTy echo ≡ ok []
echo-ok = refl

echoBackTy : ETy
echoBackTy = arr lin (sess lin loopProto) (sess lin (dualS loopProto))

echoBack : ETm 0
echoBack = lam lin (sess lin loopProto) (dualₑ (var fzero))

echo-back-ok : check evid [] echoBackTy echoBack ≡ ok []
echo-back-ok = refl

loopWireTy : ETy
loopWireTy =
  arr lin (sess lin loopProto) (arr lin (sess lin (dualS loopProto)) met)

loopWire : ETm 0
loopWire =
  lam lin (sess lin loopProto)
    (lam lin (sess lin (dualS loopProto))
      (meet (var (fsuc fzero)) (var fzero)))

loop-wire-ok : check evid [] loopWireTy loopWire ≡ ok []
loop-wire-ok = refl

unusedLoopTy : ETy
unusedLoopTy =
  arr lin (sess lin loopProto)
    (arr lin (sess lin loopProto) (sess lin loopProto))

unusedLoop : ETm 0
unusedLoop =
  lam lin (sess lin loopProto) (lam lin (sess lin loopProto) (var fzero))

unused-loop :
  check evid [] unusedLoopTy unusedLoop ≡ fail "linear variable unused"
unused-loop = refl

------------------------------------------------------------------------
-- A linear endpoint whose payload is a declared data type.
------------------------------------------------------------------------

flagProto : SExp
flagProto = send boolTy end

passTy : ETy
passTy = arr lin (sess lin flagProto) (sess lin flagProto)

pass : ETm 0
pass = lam lin (sess lin flagProto) (var fzero)

pass-ok : check evid [] passTy pass ≡ ok []
pass-ok = refl

passBackTy : ETy
passBackTy = arr lin (sess lin flagProto) (sess lin (dualS flagProto))

passBack : ETm 0
passBack = lam lin (sess lin flagProto) (dualₑ (var fzero))

pass-back-ok : check evid [] passBackTy passBack ≡ ok []
pass-back-ok = refl

------------------------------------------------------------------------
-- Both: a repeating protocol that sends `Bool` at every step.
------------------------------------------------------------------------

flagsProto : SExp
flagsProto = mu "X" (send boolTy (svar "X"))

flagsTy : ETy
flagsTy = arr lin (sess lin flagsProto) (sess lin flagsProto)

flagsPass : ETm 0
flagsPass = lam lin (sess lin flagsProto) (var fzero)

flags-ok : check evid [] flagsTy flagsPass ≡ ok []
flags-ok = refl

flagsBackTy : ETy
flagsBackTy = arr lin (sess lin flagsProto) (sess lin (dualS flagsProto))

flagsBack : ETm 0
flagsBack = lam lin (sess lin flagsProto) (dualₑ (var fzero))

flags-back-ok : check evid [] flagsBackTy flagsBack ≡ ok []
flags-back-ok = refl

-- A computed put, and a match on the received bit, each consume the
-- linear endpoint once. One abandoned arm does not.
lin-computed : meetProc lin (put maybeBool effCall done) (get maybeBool "m" done) ≡ ok tt
lin-computed = refl

lin-match : meetProc lin bitTaker bitGiver ≡ ok tt
lin-match = refl

lin-match-stop : meetProc lin (mget bit "b" (done ∷ stop ∷ [])) (put bit (lit b0) done) ≡ fail "linear variable unused"
lin-match-stop = refl

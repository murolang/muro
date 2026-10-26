------------------------------------------------------------------------
-- Two processes on one channel. A send meets a receive of the same
-- payload type, and the continuations meet. The sent value inhabits
-- that type. The values need not be the same term. A choice meets
-- the arm that was offered. Both ends
-- close, or both abandon. A type they do not share has no derivation.
-- A received nat instantiates vector lengths that name it. A vector
-- of another length has no derivation. An evidence payload meets as
-- a nat: the evidence is in each conformance, not in the meeting, so
-- a channel needs both conformances as well. A bit index meets the
-- arm of that same bit. `b0` meets the first arm. `b1` meets the
-- second. A variable bit selects neither arm. A computed value meets
-- a receive when the value it computes inhabits the payload. A match
-- on the received value meets the arm of that value. A value the
-- match does not cover has no derivation.
--
-- The meeting is evidence. One end conforms to the protocol. The
-- other conforms to the other end of that protocol. A run term has
-- no seat. None of these constructors is added to Tm. The
-- Elixir checker follows this meeting. The OTP image carries the
-- value. The other emitters do not implement the meeting.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Meet where

open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (just; nothing)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable.Core using (Dec) renaming (yes to yes′; no to no′)

open import Muro.Base using (Mode; evid; run)
open import Muro.Session hiding (¬_; Seat; no-run; ping; pong; Answer; Answerρ; yes; no; decide; decideρ)
open import Muro.Dual using (dual; grant; grant-ok)

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- The payload types agree, and the sent value inhabits that type.
-- Two values of one type both meet. A value that does not inhabit
-- the type has no derivation. `pick0` meets the left arm of `cover`.
-- `pick1` meets the right arm. `done` meets `done`. `stop` meets
-- `stop`.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- A nat received under a name instantiates the lengths that name it,
-- on the receiver's side. Another payload shadows the name and does
-- not instantiate a length. The processes in the judgment stay as
-- written, so the search recurses on a continuation.
------------------------------------------------------------------------

ext : {A : Ty} → String → ValExpr A → Idx → Idx
ext {nat} x v ρ = bind x (natExp v) (shadow x ρ)
ext {bit} x _ ρ = shadow x ρ
ext {unit} x _ ρ = shadow x ρ
ext {pair _ _} x _ ρ = shadow x ρ
ext {rec _} x _ ρ = shadow x ρ
ext {vec _ _} x _ ρ = shadow x ρ
ext {dat _ _} x _ ρ = shadow x ρ

data Meetsρ (σ τ : Idx) : Proc → Proc → Set where
  done-done : Meetsρ σ τ done done
  stop-stop : Meetsρ σ τ stop stop

  put-get : ∀ {A B v x P Q} →
    applyTy σ A ≡ applyTy τ B →
    sent v ≡ true →
    Meetsρ σ (ext x v τ) P Q →
    Meetsρ σ τ (put A v P) (get B x Q)

  get-put : ∀ {A B v x P Q} →
    applyTy σ A ≡ applyTy τ B →
    sent v ≡ true →
    Meetsρ (ext x v σ) τ P Q →
    Meetsρ σ τ (get A x P) (put B v Q)

  pick0-cover : ∀ {P Q R} → Meetsρ σ τ P Q → Meetsρ σ τ (pick0 P) (cover Q R)
  pick1-cover : ∀ {P Q R} → Meetsρ σ τ P R → Meetsρ σ τ (pick1 P) (cover Q R)

  cover-pick0 : ∀ {P Q R} → Meetsρ σ τ P R → Meetsρ σ τ (cover P Q) (pick0 R)
  cover-pick1 : ∀ {P Q R} → Meetsρ σ τ Q R → Meetsρ σ τ (cover P Q) (pick1 R)

  -- The literal selects the arm. The bit does not instantiate a length.
  iget-b0 : ∀ {x P Q R} →
    Meetsρ (ext x (lit b0) σ) τ P R →
    Meetsρ σ τ (iget x P Q) (put bit (lit b0) R)
  iget-b1 : ∀ {x P Q R} →
    Meetsρ (ext x (lit b1) σ) τ Q R →
    Meetsρ σ τ (iget x P Q) (put bit (lit b1) R)
  b0-iget : ∀ {x P Q R} →
    Meetsρ σ (ext x (lit b0) τ) P Q →
    Meetsρ σ τ (put bit (lit b0) P) (iget x Q R)
  b1-iget : ∀ {x P Q R} →
    Meetsρ σ (ext x (lit b1) τ) P R →
    Meetsρ σ τ (put bit (lit b1) P) (iget x Q R)

  -- The sent value selects the arm. The scrutinee is the name `mget` bound.
  put-mget : ∀ {A B v x ps R P} →
    applyTy σ A ≡ applyTy τ B →
    sent v ≡ true →
    armExpr v ps ≡ just R →
    Meetsρ σ (ext x v τ) P R →
    Meetsρ σ τ (put A v P) (mget B x ps)

  mget-put : ∀ {A B v x ps R P} →
    applyTy σ A ≡ applyTy τ B →
    sent v ≡ true →
    armExpr v ps ≡ just R →
    Meetsρ (ext x v σ) τ R P →
    Meetsρ σ τ (mget A x ps) (put B v P)

Meets : Proc → Proc → Set
Meets P Q = Meetsρ none none P Q

meets-sym : ∀ {σ τ P Q} → Meetsρ σ τ P Q → Meetsρ τ σ Q P
meets-sym done-done = done-done
meets-sym stop-stop = stop-stop
meets-sym (put-get eq fv m) = get-put (sym eq) fv (meets-sym m)
meets-sym (get-put eq fv m) = put-get (sym eq) fv (meets-sym m)
meets-sym (pick0-cover m) = cover-pick0 (meets-sym m)
meets-sym (pick1-cover m) = cover-pick1 (meets-sym m)
meets-sym (cover-pick0 m) = pick0-cover (meets-sym m)
meets-sym (cover-pick1 m) = pick1-cover (meets-sym m)
meets-sym (iget-b0 m) = b0-iget (meets-sym m)
meets-sym (iget-b1 m) = b1-iget (meets-sym m)
meets-sym (b0-iget m) = iget-b0 (meets-sym m)
meets-sym (b1-iget m) = iget-b1 (meets-sym m)
meets-sym (put-mget eq fv sel m) = mget-put (sym eq) fv sel (meets-sym m)
meets-sym (mget-put eq fv sel m) = put-mget (sym eq) fv sel (meets-sym m)

------------------------------------------------------------------------
-- The wall. A meeting sits at evidence.
------------------------------------------------------------------------

data Seat : Mode → Set where
  met : ∀ {P Q} → Meets P Q → Seat evid

no-run : ¬ Seat run
no-run ()

------------------------------------------------------------------------
-- One channel. The second process conforms to `dual` of the protocol.
------------------------------------------------------------------------

data Channel (P Q : Proc) (S : Proto) : Set where
  channel : Meets P Q → Conforms [] P S → Conforms [] Q (dual S) → Channel P Q S

------------------------------------------------------------------------
-- The search. `yes` carries a derivation. `no` carries its refutation.
------------------------------------------------------------------------

data Answerρ (σ τ : Idx) (P Q : Proc) : Set where
  yes : Meetsρ σ τ P Q → Answerρ σ τ P Q
  no  : ¬ Meetsρ σ τ P Q → Answerρ σ τ P Q

Answer : Proc → Proc → Set
Answer P Q = Answerρ none none P Q

on-put-get : ∀ {σ τ A B v x P Q} →
  Dec (applyTy σ A ≡ applyTy τ B) →
  Dec (sent v ≡ true) →
  Answerρ σ (ext x v τ) P Q →
  Answerρ σ τ (put A v P) (get B x Q)
on-put-get (yes′ eq) (yes′ fv) (yes m) = yes (put-get eq fv m)
on-put-get (yes′ _) (yes′ _) (no nm) = no (λ { (put-get _ _ m) → nm m })
on-put-get (yes′ _) (no′ nf) _ = no (λ { (put-get _ fv _) → nf fv })
on-put-get (no′ ¬eq) _ _ = no (λ { (put-get eq _ _) → ¬eq eq })

on-get-put : ∀ {σ τ A B v x P Q} →
  Dec (applyTy σ A ≡ applyTy τ B) →
  Dec (sent v ≡ true) →
  Answerρ (ext x v σ) τ P Q →
  Answerρ σ τ (get A x P) (put B v Q)
on-get-put (yes′ eq) (yes′ fv) (yes m) = yes (get-put eq fv m)
on-get-put (yes′ _) (yes′ _) (no nm) = no (λ { (get-put _ _ m) → nm m })
on-get-put (yes′ _) (no′ nf) _ = no (λ { (get-put _ fv _) → nf fv })
on-get-put (no′ ¬eq) _ _ = no (λ { (get-put eq _ _) → ¬eq eq })

pick0-yes : ∀ {σ τ P Q R} → Answerρ σ τ P Q → Answerρ σ τ (pick0 P) (cover Q R)
pick0-yes (yes m) = yes (pick0-cover m)
pick0-yes (no nm) = no (λ { (pick0-cover m) → nm m })

pick1-yes : ∀ {σ τ P Q R} → Answerρ σ τ P R → Answerρ σ τ (pick1 P) (cover Q R)
pick1-yes (yes m) = yes (pick1-cover m)
pick1-yes (no nm) = no (λ { (pick1-cover m) → nm m })

cover0-yes : ∀ {σ τ P Q R} → Answerρ σ τ P R → Answerρ σ τ (cover P Q) (pick0 R)
cover0-yes (yes m) = yes (cover-pick0 m)
cover0-yes (no nm) = no (λ { (cover-pick0 m) → nm m })

cover1-yes : ∀ {σ τ P Q R} → Answerρ σ τ Q R → Answerρ σ τ (cover P Q) (pick1 R)
cover1-yes (yes m) = yes (cover-pick1 m)
cover1-yes (no nm) = no (λ { (cover-pick1 m) → nm m })

on-iget-b0 : ∀ {σ τ x P Q R} →
  Answerρ (ext x (lit b0) σ) τ P R →
  Answerρ σ τ (iget x P Q) (put bit (lit b0) R)
on-iget-b0 (yes m) = yes (iget-b0 m)
on-iget-b0 (no nm) = no (λ { (iget-b0 m) → nm m })

on-iget-b1 : ∀ {σ τ x P Q R} →
  Answerρ (ext x (lit b1) σ) τ Q R →
  Answerρ σ τ (iget x P Q) (put bit (lit b1) R)
on-iget-b1 (yes m) = yes (iget-b1 m)
on-iget-b1 (no nm) = no (λ { (iget-b1 m) → nm m })

on-b0-iget : ∀ {σ τ x P Q R} →
  Answerρ σ (ext x (lit b0) τ) P Q →
  Answerρ σ τ (put bit (lit b0) P) (iget x Q R)
on-b0-iget (yes m) = yes (b0-iget m)
on-b0-iget (no nm) = no (λ { (b0-iget m) → nm m })

on-b1-iget : ∀ {σ τ x P Q R} →
  Answerρ σ (ext x (lit b1) τ) P R →
  Answerρ σ τ (put bit (lit b1) P) (iget x Q R)
on-b1-iget (yes m) = yes (b1-iget m)
on-b1-iget (no nm) = no (λ { (b1-iget m) → nm m })

-- One meeting per arm, in order. The search builds these by recursion
-- on the arm list, so each call of `decideρ` is on an arm.
data ArmAns (ans : Proc → Set) : List Proc → Set where
  aa-nil  : ArmAns ans []
  aa-cons : ∀ {R qs} → ans R → ArmAns ans qs → ArmAns ans (R ∷ qs)

data Found (ans : Proc → Set) (cs : List Ctor) (c : String) (qs : List Proc) : Set where
  got    : (R : Proc) → ans R → nthProc cs c qs ≡ just R → Found ans cs c qs
  missed : nthProc cs c qs ≡ nothing → Found ans cs c qs

-- Remember the comparison `nthProc` makes. The proof is `refl` when
-- the names are concrete, which is what a computed meeting needs.
data Reveal {A B : Set} (f : A → B) (x : A) (y : B) : Set where
  ≡is : f x ≡ y → Reveal f x y

reveal : ∀ {A B : Set} (f : A → B) (x : A) → Reveal f x (f x)
reveal _ _ = ≡is refl

nthBoth : ∀ {ans} (cs : List Ctor) (c : String) (qs : List Proc) →
  ArmAns ans qs → Found ans cs c qs
nthBoth [] _ _ _ = missed refl
nthBoth (_ ∷ _) _ [] _ = missed refl
nthBoth (ctor n _ ∷ cs′) c (r ∷ qs) (aa-cons a as) with c == n | reveal (_==_ c) n
... | true | ≡is eqn =
  got r a (trans (cong (λ b → pickCtor b r cs′ c qs) eqn) refl)
... | false | ≡is eqn with nthBoth cs′ c qs as
... | got R b pr =
  got R b (trans (cong (λ b → pickCtor b r cs′ c qs) eqn) pr)
... | missed pr =
  missed (trans (cong (λ b → pickCtor b r cs′ c qs) eqn) pr)

usePut : ∀ {σ τ A B v x ps R P} →
  applyTy σ A ≡ applyTy τ B →
  sent v ≡ true →
  armExpr v ps ≡ just R →
  Answerρ σ (ext x v τ) P R →
  Answerρ σ τ (put A v P) (mget B x ps)
usePut eq fv sel (yes m) = yes (put-mget eq fv sel m)
usePut {σ} {τ} {v = v} {x = x} {P = P} eq fv sel (no nm) = no (λ { (put-mget _ _ p m) →
  nm (subst (λ S → Meetsρ σ (ext x v τ) P S) (just-inj (trans (sym p) sel)) m) })

useMget : ∀ {σ τ A B v x ps R P} →
  applyTy σ A ≡ applyTy τ B →
  sent v ≡ true →
  armExpr v ps ≡ just R →
  Answerρ (ext x v σ) τ R P →
  Answerρ σ τ (mget A x ps) (put B v P)
useMget eq fv sel (yes m) = yes (mget-put eq fv sel m)
useMget {σ} {τ} {v = v} {x = x} {P = P} eq fv sel (no nm) = no (λ { (mget-put _ _ p m) →
  nm (subst (λ S → Meetsρ (ext x v σ) τ S P) (just-inj (trans (sym p) sel)) m) })

-- `ground` nothing means the expression selects no arm.
noGround : ∀ {σ τ A B v x ps P} →
  ground v ≡ nothing →
  ¬ Meetsρ σ τ (put A v P) (mget B x ps)
noGround {ps = ps} geq (put-mget _ _ p _) =
  just≢nothing (trans (sym p) (cong (armStep ps) geq))

noGround′ : ∀ {σ τ A B v x ps P} →
  ground v ≡ nothing →
  ¬ Meetsρ σ τ (mget A x ps) (put B v P)
noGround′ {ps = ps} geq (mget-put _ _ p _) =
  just≢nothing (trans (sym p) (cong (armStep ps) geq))

selLit : ∀ {A} {v : ValExpr A} {u : Val A} {ps : List Proc} {R : Proc} →
  ground v ≡ just u →
  armOf A u ps ≡ just R →
  armExpr v ps ≡ just R
selLit {v = v} {ps = ps} geq aeq = trans (cong (armStep ps) geq) aeq

missedLit : ∀ {A} {v : ValExpr A} {u : Val A} {ps : List Proc} →
  ground v ≡ just u →
  armOf A u ps ≡ nothing →
  armExpr v ps ≡ nothing
missedLit {v = v} {ps = ps} geq aeq = trans (cong (armStep ps) geq) aeq

takePut : ∀ {σ τ A B x P} (v : ValExpr A) →
  applyTy σ A ≡ applyTy τ B →
  sent v ≡ true →
  (w : Val A) →
  ground v ≡ just w →
  (qs : List Proc) →
  ArmAns (Answerρ σ (ext x v τ) P) qs →
  Answerρ σ τ (put A v P) (mget B x qs)
takePut v eq fv b0 geq (p ∷ q ∷ []) (aa-cons a _) =
  usePut eq fv (selLit {v = v} {ps = p ∷ q ∷ []} geq refl) a
takePut v eq fv b1 geq (p ∷ q ∷ []) (aa-cons _ (aa-cons a _)) =
  usePut eq fv (selLit {v = v} {ps = p ∷ q ∷ []} geq refl) a
takePut v eq fv b0 geq [] _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = []} geq refl)) })
takePut v eq fv b0 geq (p ∷ []) _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = p ∷ []} geq refl)) })
takePut v eq fv b0 geq (p ∷ q ∷ r ∷ rs) _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = p ∷ q ∷ r ∷ rs} geq refl)) })
takePut v eq fv b1 geq [] _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = []} geq refl)) })
takePut v eq fv b1 geq (p ∷ []) _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = p ∷ []} geq refl)) })
takePut v eq fv b1 geq (p ∷ q ∷ r ∷ rs) _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = p ∷ q ∷ r ∷ rs} geq refl)) })
takePut v eq fv (con {d} c _) geq qs as′ with nthBoth (ctorsOf d) c qs as′
... | got R a pr = usePut eq fv (selLit {v = v} {ps = qs} geq pr) a
... | missed pr =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq pr)) })
takePut v eq fv zero geq qs _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takePut v eq fv (suc _) geq qs _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takePut v eq fv tt geq qs _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takePut v eq fv (tup _ _) geq qs _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takePut v eq fv (rec _) geq qs _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takePut v eq fv (rep _) geq qs _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })

takeMget : ∀ {σ τ A B x P} (v : ValExpr B) →
  applyTy σ A ≡ applyTy τ B →
  sent v ≡ true →
  (w : Val B) →
  ground v ≡ just w →
  (qs : List Proc) →
  ArmAns (λ R → Answerρ (ext x v σ) τ R P) qs →
  Answerρ σ τ (mget A x qs) (put B v P)
takeMget v eq fv b0 geq (p ∷ q ∷ []) (aa-cons a _) =
  useMget eq fv (selLit {v = v} {ps = p ∷ q ∷ []} geq refl) a
takeMget v eq fv b1 geq (p ∷ q ∷ []) (aa-cons _ (aa-cons a _)) =
  useMget eq fv (selLit {v = v} {ps = p ∷ q ∷ []} geq refl) a
takeMget v eq fv b0 geq [] _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = []} geq refl)) })
takeMget v eq fv b0 geq (p ∷ []) _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = p ∷ []} geq refl)) })
takeMget v eq fv b0 geq (p ∷ q ∷ r ∷ rs) _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = p ∷ q ∷ r ∷ rs} geq refl)) })
takeMget v eq fv b1 geq [] _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = []} geq refl)) })
takeMget v eq fv b1 geq (p ∷ []) _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = p ∷ []} geq refl)) })
takeMget v eq fv b1 geq (p ∷ q ∷ r ∷ rs) _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = p ∷ q ∷ r ∷ rs} geq refl)) })
takeMget v eq fv (con {d} c _) geq qs as′ with nthBoth (ctorsOf d) c qs as′
... | got R a pr = useMget eq fv (selLit {v = v} {ps = qs} geq pr) a
... | missed pr =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq pr)) })
takeMget v eq fv zero geq qs _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takeMget v eq fv (suc _) geq qs _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takeMget v eq fv tt geq qs _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takeMget v eq fv (tup _ _) geq qs _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takeMget v eq fv (rec _) geq qs _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takeMget v eq fv (rep _) geq qs _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })

concludePut : ∀ {σ τ A B v x P} (ps : List Proc) →
  ArmAns (Answerρ σ (ext x v τ) P) ps →
  Answerρ σ τ (put A v P) (mget B x ps)
concludePut {σ} {τ} {A} {B} {v} {x} {P} ps as
  with ty≟ (applyTy σ A) (applyTy τ B) | sent? v | ground v in geq
... | no′ ¬eq | _ | _ = no (λ { (put-mget eq _ _ _) → ¬eq eq })
... | yes′ _ | no′ nf | _ = no (λ { (put-mget _ fv _ _) → nf fv })
... | yes′ _ | yes′ _ | nothing = no (noGround geq)
... | yes′ eq | yes′ fv | just u = takePut v eq fv u geq ps as

concludeMget : ∀ {σ τ A B v x P} (ps : List Proc) →
  ArmAns (λ R → Answerρ (ext x v σ) τ R P) ps →
  Answerρ σ τ (mget A x ps) (put B v P)
concludeMget {σ} {τ} {A} {B} {v} {x} {P} ps as
  with ty≟ (applyTy σ A) (applyTy τ B) | sent? v | ground v in geq
... | no′ ¬eq | _ | _ = no (λ { (mget-put eq _ _ _) → ¬eq eq })
... | yes′ _ | no′ nf | _ = no (λ { (mget-put _ fv _ _) → nf fv })
... | yes′ _ | yes′ _ | nothing = no (noGround′ geq)
... | yes′ eq | yes′ fv | just u = takeMget v eq fv u geq ps as


mutual
  decideρ : (σ τ : Idx) (P Q : Proc) → Answerρ σ τ P Q
  decideρ _ _ done done = yes done-done
  decideρ _ _ done stop = no (λ ())
  decideρ _ _ done (put _ _ _) = no (λ ())
  decideρ _ _ done (get _ _ _) = no (λ ())
  decideρ _ _ done (pick0 _) = no (λ ())
  decideρ _ _ done (pick1 _) = no (λ ())
  decideρ _ _ done (cover _ _) = no (λ ())
  decideρ _ _ done (iget _ _ _) = no (λ ())
  decideρ _ _ done (mget _ _ _) = no (λ ())
  decideρ _ _ stop done = no (λ ())
  decideρ _ _ stop stop = yes stop-stop
  decideρ _ _ stop (put _ _ _) = no (λ ())
  decideρ _ _ stop (get _ _ _) = no (λ ())
  decideρ _ _ stop (pick0 _) = no (λ ())
  decideρ _ _ stop (pick1 _) = no (λ ())
  decideρ _ _ stop (cover _ _) = no (λ ())
  decideρ _ _ stop (iget _ _ _) = no (λ ())
  decideρ _ _ stop (mget _ _ _) = no (λ ())
  decideρ σ τ (put A v P) (get B x Q) =
    on-put-get (ty≟ (applyTy σ A) (applyTy τ B)) (sent? v) (decideρ σ (ext x v τ) P Q)
  decideρ σ τ (put A v P) (mget B x ps) =
    concludePut ps (armAns {σ} {ext x v τ} P ps)
  decideρ _ _ (put _ _ _) done = no (λ ())
  decideρ _ _ (put _ _ _) stop = no (λ ())
  decideρ _ _ (put _ _ _) (put _ _ _) = no (λ ())
  decideρ _ _ (put _ _ _) (pick0 _) = no (λ ())
  decideρ _ _ (put _ _ _) (pick1 _) = no (λ ())
  decideρ _ _ (put _ _ _) (cover _ _) = no (λ ())
  decideρ σ τ (put bit (lit b0) P) (iget x Q _) = on-b0-iget (decideρ σ (ext x (lit b0) τ) P Q)
  decideρ σ τ (put bit (lit b1) P) (iget x _ R) = on-b1-iget (decideρ σ (ext x (lit b1) τ) P R)
  decideρ _ _ (put bit (var _) _) (iget _ _ _) = no (λ ())
  decideρ _ _ (put bit (call _ _) _) (iget _ _ _) = no (λ ())
  decideρ _ _ (put nat _ _) (iget _ _ _) = no (λ ())
  decideρ _ _ (put unit _ _) (iget _ _ _) = no (λ ())
  decideρ _ _ (put (pair _ _) _ _) (iget _ _ _) = no (λ ())
  decideρ _ _ (put (rec _) _ _) (iget _ _ _) = no (λ ())
  decideρ _ _ (put (vec _ _) _ _) (iget _ _ _) = no (λ ())
  decideρ _ _ (put (dat _ _) _ _) (iget _ _ _) = no (λ ())
  decideρ σ τ (get A x P) (put B v Q) =
    on-get-put (ty≟ (applyTy σ A) (applyTy τ B)) (sent? v) (decideρ (ext x v σ) τ P Q)
  decideρ σ τ (mget A x ps) (put B v P) =
    concludeMget ps (armFirst {ext x v σ} {τ} P ps)
  decideρ _ _ (get _ _ _) done = no (λ ())
  decideρ _ _ (get _ _ _) stop = no (λ ())
  decideρ _ _ (get _ _ _) (get _ _ _) = no (λ ())
  decideρ _ _ (get _ _ _) (pick0 _) = no (λ ())
  decideρ _ _ (get _ _ _) (pick1 _) = no (λ ())
  decideρ _ _ (get _ _ _) (cover _ _) = no (λ ())
  decideρ _ _ (get _ _ _) (iget _ _ _) = no (λ ())
  decideρ _ _ (get _ _ _) (mget _ _ _) = no (λ ())
  decideρ σ τ (pick0 P) (cover Q _) = pick0-yes (decideρ σ τ P Q)
  decideρ _ _ (pick0 _) done = no (λ ())
  decideρ _ _ (pick0 _) stop = no (λ ())
  decideρ _ _ (pick0 _) (put _ _ _) = no (λ ())
  decideρ _ _ (pick0 _) (get _ _ _) = no (λ ())
  decideρ _ _ (pick0 _) (pick0 _) = no (λ ())
  decideρ _ _ (pick0 _) (pick1 _) = no (λ ())
  decideρ _ _ (pick0 _) (iget _ _ _) = no (λ ())
  decideρ _ _ (pick0 _) (mget _ _ _) = no (λ ())
  decideρ σ τ (pick1 P) (cover _ R) = pick1-yes (decideρ σ τ P R)
  decideρ _ _ (pick1 _) done = no (λ ())
  decideρ _ _ (pick1 _) stop = no (λ ())
  decideρ _ _ (pick1 _) (put _ _ _) = no (λ ())
  decideρ _ _ (pick1 _) (get _ _ _) = no (λ ())
  decideρ _ _ (pick1 _) (pick0 _) = no (λ ())
  decideρ _ _ (pick1 _) (pick1 _) = no (λ ())
  decideρ _ _ (pick1 _) (iget _ _ _) = no (λ ())
  decideρ _ _ (pick1 _) (mget _ _ _) = no (λ ())
  decideρ σ τ (cover P _) (pick0 R) = cover0-yes (decideρ σ τ P R)
  decideρ σ τ (cover _ Q) (pick1 R) = cover1-yes (decideρ σ τ Q R)
  decideρ _ _ (cover _ _) done = no (λ ())
  decideρ _ _ (cover _ _) stop = no (λ ())
  decideρ _ _ (cover _ _) (put _ _ _) = no (λ ())
  decideρ _ _ (cover _ _) (get _ _ _) = no (λ ())
  decideρ _ _ (cover _ _) (cover _ _) = no (λ ())
  decideρ _ _ (cover _ _) (iget _ _ _) = no (λ ())
  decideρ _ _ (cover _ _) (mget _ _ _) = no (λ ())
  decideρ σ τ (iget x P Q) (put bit (lit b0) R) = on-iget-b0 (decideρ (ext x (lit b0) σ) τ P R)
  decideρ σ τ (iget x P Q) (put bit (lit b1) R) = on-iget-b1 (decideρ (ext x (lit b1) σ) τ Q R)
  decideρ _ _ (iget _ _ _) (put bit (var _) _) = no (λ ())
  decideρ _ _ (iget _ _ _) (put bit (call _ _) _) = no (λ ())
  decideρ _ _ (iget _ _ _) (put nat _ _) = no (λ ())
  decideρ _ _ (iget _ _ _) (put unit _ _) = no (λ ())
  decideρ _ _ (iget _ _ _) (put (pair _ _) _ _) = no (λ ())
  decideρ _ _ (iget _ _ _) (put (rec _) _ _) = no (λ ())
  decideρ _ _ (iget _ _ _) (put (vec _ _) _ _) = no (λ ())
  decideρ _ _ (iget _ _ _) (put (dat _ _) _ _) = no (λ ())
  decideρ _ _ (iget _ _ _) done = no (λ ())
  decideρ _ _ (iget _ _ _) stop = no (λ ())
  decideρ _ _ (iget _ _ _) (get _ _ _) = no (λ ())
  decideρ _ _ (iget _ _ _) (pick0 _) = no (λ ())
  decideρ _ _ (iget _ _ _) (pick1 _) = no (λ ())
  decideρ _ _ (iget _ _ _) (cover _ _) = no (λ ())
  decideρ _ _ (iget _ _ _) (iget _ _ _) = no (λ ())
  decideρ _ _ (iget _ _ _) (mget _ _ _) = no (λ ())
  decideρ _ _ (mget _ _ _) done = no (λ ())
  decideρ _ _ (mget _ _ _) stop = no (λ ())
  decideρ _ _ (mget _ _ _) (get _ _ _) = no (λ ())
  decideρ _ _ (mget _ _ _) (pick0 _) = no (λ ())
  decideρ _ _ (mget _ _ _) (pick1 _) = no (λ ())
  decideρ _ _ (mget _ _ _) (cover _ _) = no (λ ())
  decideρ _ _ (mget _ _ _) (iget _ _ _) = no (λ ())
  decideρ _ _ (mget _ _ _) (mget _ _ _) = no (λ ())

  -- Each arm is a subterm of the match, so the search is structural.
  armAns : {ι κ : Idx} (P : Proc) (qs : List Proc) → ArmAns (Answerρ ι κ P) qs
  armAns _ [] = aa-nil
  armAns {ι} {κ} P (r ∷ qs) = aa-cons (decideρ ι κ P r) (armAns P qs)

  armFirst : {ι κ : Idx} (P : Proc) (qs : List Proc) → ArmAns (λ R → Answerρ ι κ R P) qs
  armFirst _ [] = aa-nil
  armFirst {ι} {κ} P (r ∷ qs) = aa-cons (decideρ ι κ r P) (armFirst P qs)

decide : (P Q : Proc) → Answer P Q
decide P Q = decideρ none none P Q

------------------------------------------------------------------------
-- `pong` receives a nat and sends a nat. `peer` sends a nat and
-- receives a nat. `zero` and `two` are different values of that
-- type, and both meet. A tuple wrapping a fixed map meets a receive
-- of that type. A different type has no derivation, and neither do
-- two sends.
------------------------------------------------------------------------

ping : Proto
ping = recv nat (send nat end)

pong : Proc
pong = get nat "x" (put nat (lit one) done)

peer : Proc
peer = put nat (lit zero) (get nat "y" done)

pong-peer : Meets pong peer
pong-peer = get-put refl refl (put-get refl refl done-done)

meets-decides : decide pong peer ≡ yes pong-peer
meets-decides = refl

peer-pong : decide peer pong ≡ yes (meets-sym pong-peer)
peer-pong = refl

other : Proc
other = put nat (lit two) (get nat "z" done)

other-meets : Meets pong other
other-meets = get-put refl refl (put-get refl refl done-done)

other-decides : decide pong other ≡ yes other-meets
other-decides = refl

ping-channel : Channel pong peer ping
ping-channel = channel pong-peer (get-ok refl (put-ok refl (lit-ok refl) done-end)) (put-ok refl (lit-ok refl) (get-ok refl done-end))

box-meet : Meets (put box (lit v-here) done) (get box "a" done)
box-meet = put-get refl refl done-done

there-meet : Meets (put box (lit v-there) done) (get box "b" done)
there-meet = put-get refl refl done-done

box-decides : decide (put box (lit v-here) done) (get box "a" done) ≡ yes box-meet
box-decides = refl

not-payload : ¬ Meets (put nat (lit zero) done) (get box "x" done)
not-payload (put-get () _ _)

------------------------------------------------------------------------
-- A bound name is sent at the type it was received. `reply` receives
-- a nat and sends that name. It meets a process that receives a nat.
-- A receive of a bit has no meeting with that name. The value is not
-- compared. The type written on `put` is the type compared.
------------------------------------------------------------------------

reply : Proc
reply = get nat "k" (put nat (var "k") done)

reply-peer : Proc
reply-peer = put nat (lit zero) (get nat "n" done)

reply-meet : Meets reply reply-peer
reply-meet = get-put refl refl (put-get refl refl done-done)

reply-decides : decide reply reply-peer ≡ yes reply-meet
reply-decides = refl

not-bound-type : ¬ Meets reply (put nat (lit zero) (get bit "n" done))
not-bound-type (get-put refl refl (put-get () _ _))

------------------------------------------------------------------------
-- The length that was received is the length of the vector. A vector
-- of another length has no meeting.
------------------------------------------------------------------------

sized-meet : Meets sized-server sized-client
sized-meet = get-put refl refl (put-get refl refl done-done)

sized-decides : decide sized-server sized-client ≡ yes sized-meet
sized-decides = refl

sized-miss : ¬ Meets sized-server sized-bad
sized-miss (get-put refl refl (put-get () _ _))

------------------------------------------------------------------------
-- The window is granted and the data is sent within it. The meeting
-- compares the nats. The evidence is the server's conformance, so a
-- server that guesses meets the grant but has no channel.
------------------------------------------------------------------------

window-meet : Meets full grant
window-meet = get-put refl refl (put-get refl refl done-done)

window-decides : decide full grant ≡ yes window-meet
window-decides = refl

window-channel : Channel full grant window
window-channel = channel window-meet full-ok grant-ok

guess-meets : Meets guess grant
guess-meets = get-put refl refl (put-get refl refl done-done)

guess-no-channel : ¬ Channel guess grant window
guess-no-channel (channel _ c _) = guess-refused c

not-send : ¬ Meets (put nat (lit zero) done) (put nat (lit zero) done)
not-send ()

not-ending : ¬ Meets (put nat (lit zero) stop) (get nat "x" done)
not-ending (put-get refl refl ())

------------------------------------------------------------------------
-- Both abandon after the same payload type. Choosing meets the
-- offered arm.
------------------------------------------------------------------------

left : Proc
left = put nat (lit zero) stop

right : Proc
right = get nat "x" stop

left-right : Meets left right
left-right = put-get refl refl stop-stop

left-decides : decide left right ≡ yes left-right
left-decides = refl

abandon-channel : Channel left right (send nat end)
abandon-channel = channel left-right (put-ok refl (lit-ok refl) abandon) (get-ok refl abandon)

choice : Proto
choice = choose end (send nat end)

taker : Proc
taker = pick0 done

giver : Proc
giver = cover done (get nat "x" done)

choice-meet : Meets taker giver
choice-meet = pick0-cover done-done

choice-decides : decide taker giver ≡ yes choice-meet
choice-decides = refl

choice-channel : Channel taker giver choice
choice-channel =
  channel choice-meet (pick0-ok done-end) (cover-ok done-end (get-ok refl done-end))

not-arm : ¬ Meets (pick0 done) (cover (put nat (lit zero) done) done)
not-arm (pick0-cover ())

------------------------------------------------------------------------
-- The bit selects the arm. `b0` meets the first continuation. `b1`
-- meets the second. The same index with the other continuation has
-- no meeting. A variable bit selects neither arm. A channel also
-- needs the other end, so an arm that was not dualised has none.
------------------------------------------------------------------------

route-client : Proc
route-client = put bit (lit b0) (get nat "m" done)

route-meet : Meets route-server route-client
route-meet = iget-b0 (put-get refl refl done-done)

route-meet-decides : decide route-server route-client ≡ yes route-meet
route-meet-decides = refl

route-client-one : Proc
route-client-one = put bit (lit b1) (put nat (lit zero) done)

route-one : Meets route-server route-client-one
route-one = iget-b1 (get-put refl refl done-done)

route-one-decides : decide route-server route-client-one ≡ yes route-one
route-one-decides = refl

route-miss : Proc
route-miss = put bit (lit b0) (put nat (lit one) done)

not-route : ¬ Meets route-server route-miss
not-route (iget-b0 ())

not-route-decides : decide route-server route-miss ≡ no not-route
not-route-decides = refl

route-channel : Channel route-server route-client route
route-channel =
  channel route-meet route-server-ok (iput0-ok (get-ok refl done-end))

not-crossed-channel : ¬ Channel route-server route-miss route
not-crossed-channel (channel _ _ (iput0-ok ()))

ask : Proc
ask = put bit (lit b1) (get bit "c" done)

echo-meet : Meets echo-bit ask
echo-meet = iget-b1 (put-get refl refl done-done)

echo-meet-decides : decide echo-bit ask ≡ yes echo-meet
echo-meet-decides = refl

not-var : ¬ Meets echo-bit (put bit (var "b") (get bit "c" done))
not-var ()

------------------------------------------------------------------------
-- A declared data payload meets a receive of that type when the
-- value inhabits it. A constructor the declaration does not have
-- has no meeting.
------------------------------------------------------------------------

flag-meet : Meets (put boolTy (lit trueV) done) (get boolTy "b" done)
flag-meet = put-get refl refl done-done

flag-decides : decide (put boolTy (lit trueV) done) (get boolTy "b" done) ≡ yes flag-meet
flag-decides = refl

miss-meet : ¬ Meets (put boolTy (lit noneV) done) (get boolTy "b" done)
miss-meet (put-get _ () _)

opt-meet : Meets (put maybeNat (lit just0) done) (get maybeNat "m" done)
opt-meet = put-get refl refl done-done

opt-decides : decide (put maybeNat (lit just0) done) (get maybeNat "m" done) ≡ yes opt-meet
opt-decides = refl

------------------------------------------------------------------------
-- A computed put meets a receive of the payload it computes. A
-- result of the wrong type, and a value that does not inhabit the
-- type, have no meeting. The other end is the dual.
------------------------------------------------------------------------

eff-meet : Meets effReply (get maybeBool "m" done)
eff-meet = put-get refl refl done-done

eff-meet-decides : decide effReply (get maybeBool "m" done) ≡ yes eff-meet
eff-meet-decides = refl

eff-channel : Channel effReply (get maybeBool "m" done) effAnswer
eff-channel =
  channel eff-meet effReply-ok (get-ok refl done-end)

-- `effective` computes `just true`, so the meeting takes the second arm.
maybeSplit : Proc
maybeSplit = mget maybeBool "m" (stop ∷ done ∷ [])

maybeSplit-ok : Conforms [] maybeSplit (recv maybeBool end)
maybeSplit-ok =
  mget-ok refl (dat-cov refl) (arms-cons abandon (arms-cons done-end arms-nil))

eff-arm : Meets effReply maybeSplit
eff-arm = put-mget refl refl refl done-done

eff-arm-decides : decide effReply maybeSplit ≡ yes eff-arm
eff-arm-decides = refl

eff-arm-sym : decide maybeSplit effReply ≡ yes (meets-sym eff-arm)
eff-arm-sym = refl

eff-arm-channel : Channel effReply maybeSplit (send maybeBool end)
eff-arm-channel = channel eff-arm effReply-ok maybeSplit-ok

not-count : ¬ Meets (put boolTy countCall done) (get boolTy "b" done)
not-count (put-get _ () _)

not-bad : ¬ Meets (put boolTy badCall done) (get boolTy "b" done)
not-bad (put-get _ () _)

------------------------------------------------------------------------
-- The received value selects the arm. The other party covers that
-- arm. A short match does not cover the value. `Bool` and `Maybe`
-- select by constructor order.
------------------------------------------------------------------------

bitGiver : Proc
bitGiver = put bit (lit b0) (cover done done)

bit-meet : Meets bitGiver bitTaker
bit-meet = put-mget refl refl refl (cover-pick0 done-done)

bit-meet-decides : decide bitGiver bitTaker ≡ yes bit-meet
bit-meet-decides = refl

bit-meet-sym : decide bitTaker bitGiver ≡ yes (meets-sym bit-meet)
bit-meet-sym = refl

bit-channel : Channel bitGiver bitTaker (send bit (branch end end))
bit-channel =
  channel bit-meet
    (put-ok refl (lit-ok refl) (cover-ok done-end done-end))
    bitTaker-ok

bool-meet : Meets (put boolTy (lit trueV) done) boolTaker
bool-meet = put-mget refl refl refl done-done

bool-meet-decides : decide (put boolTy (lit trueV) done) boolTaker ≡ yes bool-meet
bool-meet-decides = refl

false-meet : Meets (put boolTy (lit falseV) done) boolTaker
false-meet = put-mget refl refl refl done-done

opt-arm : Meets (put maybeNat (lit nothingV) done) optTaker
opt-arm = put-mget refl refl refl done-done

just-arm : Meets (put maybeNat (lit just0) done) optTaker
just-arm = put-mget refl refl refl done-done

just-arm-decides : decide (put maybeNat (lit just0) done) optTaker ≡ yes just-arm
just-arm-decides = refl

not-short : ¬ Meets (put bit (lit b0) done) (mget bit "b" (done ∷ []))
not-short (put-mget _ _ () _)

not-var-arm : ¬ Meets (put bit (var "b") done) (mget bit "b" (done ∷ done ∷ []))
not-var-arm (put-mget _ _ () _)

not-nat-arm : ¬ Meets (put nat (lit zero) done) (mget nat "n" (done ∷ done ∷ []))
not-nat-arm (put-mget _ _ () _)

not-bad-arm : ¬ Meets (put boolTy badCall done) (mget boolTy "b" (done ∷ done ∷ []))
not-bad-arm (put-mget _ () _ _)

-- The arms differ, so the selected constructor is the arm that meets.
boolSplit : Proc
boolSplit = mget boolTy "b" (done ∷ stop ∷ [])

false-split : Meets (put boolTy (lit falseV) stop) boolSplit
false-split = put-mget refl refl refl stop-stop

false-split-decides : decide (put boolTy (lit falseV) stop) boolSplit ≡ yes false-split
false-split-decides = refl

optSplit : Proc
optSplit = mget maybeNat "m" (stop ∷ done ∷ [])

nothing-split : Meets (put maybeNat (lit nothingV) stop) optSplit
nothing-split = put-mget refl refl refl stop-stop

nothing-split-decides : decide (put maybeNat (lit nothingV) stop) optSplit ≡ yes nothing-split
nothing-split-decides = refl

just-split : Meets (put maybeNat (lit just0) done) optSplit
just-split = put-mget refl refl refl done-done

just-split-decides : decide (put maybeNat (lit just0) done) optSplit ≡ yes just-split
just-split-decides = refl

------------------------------------------------------------------------
-- A named session opens to its body. The meeting is the meeting of
-- that body. Both orders meet. `frames 3` is the opened vector.
------------------------------------------------------------------------

sess-meet : Meets sessClient sessServer
sess-meet = put-get refl refl (put-get refl refl done-done)

sess-meet-swap : Meets sessServer sessClient
sess-meet-swap = get-put refl refl (get-put refl refl done-done)

sess-channel : Channel sessClient sessServer sessReqProto
sess-channel = channel sess-meet sess-client sess-server-dual
  where
  sess-server-dual : Conforms [] sessServer (dual sessReqProto)
  sess-server-dual = get-ok refl (get-ok refl done-end)

sess-meet-decides : decide sessClient sessServer ≡ yes sess-meet
sess-meet-decides = refl

framesServer : Proc
framesServer = get (vec nat (nlit three)) "v" done

frames-meet : Meets sessFramesClient framesServer
frames-meet = put-get refl refl done-done

frames-meet-swap : Meets framesServer sessFramesClient
frames-meet-swap = get-put refl refl done-done

frames-channel : Channel sessFramesClient framesServer sessFramesProto
frames-channel = channel frames-meet sess-frames-ok frames-back
  where
  frames-back : Conforms [] framesServer (dual sessFramesProto)
  frames-back = get-ok refl done-end

noteServer : Proc
noteServer = get boolTy "b" done

note-meet : Meets (put boolTy (lit trueV) done) noteServer
note-meet = put-get refl refl done-done

note-meet-swap : Meets noteServer (put boolTy (lit trueV) done)
note-meet-swap = get-put refl refl done-done

------------------------------------------------------------------------
-- A put of headers meets the headers arm. Data meets the data arm.
-- The two protocol arms are the case of that same value.
------------------------------------------------------------------------

frame-meet : Meets frameClient frameServer
frame-meet = put-mget refl refl refl (put-get refl refl done-done)

frame-meet-swap : Meets frameServer frameClient
frame-meet-swap = mget-put refl refl refl (get-put refl refl done-done)

frame-meet-decides : decide frameClient frameServer ≡ yes frame-meet
frame-meet-decides = refl

frame-meet-swap-decides : decide frameServer frameClient ≡ yes frame-meet-swap
frame-meet-swap-decides = refl

frame-channel : Channel frameServer frameClient frameCase
frame-channel = channel frame-meet-swap frame-server-ok frame-client-ok

data-meet : Meets frameData frameServer
data-meet = put-mget refl refl refl (get-put refl refl done-done)

data-meet-swap : Meets frameServer frameData
data-meet-swap = mget-put refl refl refl (put-get refl refl done-done)

data-channel : Channel frameData frameServer frameClientProto
data-channel = channel data-meet frame-data-ok frame-server-ok

late-meet : Meets lateClient lateServer
late-meet = put-mget refl refl refl (get-put refl refl done-done)

late-meet-swap : Meets lateServer lateClient
late-meet-swap = mget-put refl refl refl (put-get refl refl done-done)

late-meet-decides : decide lateClient lateServer ≡ yes late-meet
late-meet-decides = refl

late-meet-swap-decides : decide lateServer lateClient ≡ yes late-meet-swap
late-meet-swap-decides = refl

late-channel : Channel lateServer lateClient lateCase
late-channel = channel late-meet-swap late-server-ok late-client-ok

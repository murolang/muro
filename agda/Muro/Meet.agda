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
-- on the received value meets the arm of that value. A named arm
-- meets after the received fields replace its binders. A product arm
-- meets after the received components replace its binders. A fork
-- cases on one bound field and meets the arm that field selects.
-- A value the match does not cover has no derivation.
--
-- The meeting is evidence. One end conforms to the protocol. The
-- other conforms to the other end of that protocol. A run term has
-- no seat. None of these constructors is added to Tm. The
-- Elixir checker follows this meeting. The OTP image carries the
-- value. The other emitters do not implement the meeting.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Meet where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product using (_×_; Σ; _,_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_; _≟_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable.Core using (Dec) renaming (yes to yes′; no to no′)

open import Muro.Base using (Mode; evid; run)
open import Muro.Session hiding (¬_; Seat; no-run; ping; pong; Answer; Answerρ; yes; no; decide; decideρ; opened)
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

-- One meeting per arm, in order. A bare arm is its process. A named
-- arm is that process after the received fields replace its binders.
-- The search builds the meetings by recursion on the arm list.

substValN : ∀ {A} → List FEnv → ValExpr A → ValExpr A
substValN [] v = v
substValN (e ∷ es) v = substVal e (substValN es v)

substN : List FEnv → Proc → Proc
substN [] p = p
substN (e ∷ es) p = substProc e (substN es p)

shadowN : String → List FEnv → List FEnv
shadowN _ [] = []
shadowN x (e ∷ es) = shadowF x e ∷ shadowN x es

shadowAll : List String → List FEnv → List FEnv
shadowAll _ [] = []
shadowAll xs (e ∷ es) = shadows xs e ∷ shadowAll xs es

substArmsN : List FEnv → List PArm → List PArm
substArmsN _ [] = []
substArmsN es (bare p ∷ qs) = bare (substN es p) ∷ substArmsN es qs
substArmsN es (named c xs p ∷ qs) =
  named c xs (substN (shadowAll xs es) p) ∷ substArmsN es qs
substArmsN es (prod pat p ∷ qs) =
  prod pat (substN (shadowAll (patBinders pat) es) p) ∷ substArmsN es qs
substArmsN es (fork c xs y qs ∷ ps) =
  fork c xs y (substArmsN (shadowAll xs es) qs) ∷ substArmsN es ps

≡cons : {a b : PArm} → a ≡ b → {ps qs : List PArm} → ps ≡ qs → a ∷ ps ≡ b ∷ qs
≡cons refl refl = refl

≡mget : ∀ {A x ps qs} → ps ≡ qs → mget A x ps ≡ mget A x qs
≡mget refl = refl

shadowsNil : (xs : List String) → shadows xs [] ≡ []
shadowsNil [] = refl
shadowsNil (_ ∷ xs) = shadowsNil xs

armsId : (ps : List PArm) → substArms [] ps ≡ ps
armsId [] = refl
armsId (bare _ ∷ ps) rewrite armsId ps = refl
armsId (named _ xs _ ∷ ps) rewrite shadowsNil xs | armsId ps = refl
armsId (prod pat _ ∷ ps) rewrite shadowsNil (patBinders pat) | armsId ps = refl
armsId (fork _ xs _ qs ∷ ps) rewrite shadowsNil xs | armsId qs | armsId ps = refl

armsIdN : (ps : List PArm) → substArmsN [] ps ≡ ps
armsIdN [] = refl
armsIdN (bare _ ∷ ps) rewrite armsIdN ps = refl
armsIdN (named _ _ _ ∷ ps) rewrite armsIdN ps = refl
armsIdN (prod _ _ ∷ ps) rewrite armsIdN ps = refl
armsIdN (fork _ _ _ qs ∷ ps) rewrite armsIdN qs | armsIdN ps = refl

pushArms : (e : FEnv) (es : List FEnv) (ps : List PArm) →
  substArms e (substArmsN es ps) ≡ substArmsN (e ∷ es) ps
pushArms _ _ [] = refl
pushArms e es (bare p ∷ ps) =
  ≡cons {bare (substProc e (substN es p))} {bare (substN (e ∷ es) p)}
    refl (pushArms e es ps)
pushArms e es (named c xs p ∷ ps) =
  ≡cons
    {named c xs (substProc (shadows xs e) (substN (shadowAll xs es) p))}
    {named c xs (substN (shadowAll xs (e ∷ es)) p)}
    refl (pushArms e es ps)
pushArms e es (prod pat p ∷ ps) =
  ≡cons
    {prod pat (substProc (shadows (patBinders pat) e) (substN (shadowAll (patBinders pat) es) p))}
    {prod pat (substN (shadowAll (patBinders pat) (e ∷ es)) p)}
    refl (pushArms e es ps)
pushArms e es (fork c xs y qs ∷ ps) =
  ≡cons
    {fork c xs y (substArms (shadows xs e) (substArmsN (shadowAll xs es) qs))}
    {fork c xs y (substArmsN (shadowAll xs (e ∷ es)) qs)}
    (cong (fork c xs y) (pushArms (shadows xs e) (shadowAll xs es) qs))
    (pushArms e es ps)

subDone : (e : FEnv) → substProc e done ≡ done
subDone [] = refl
subDone (_ ∷ _) = refl

subStop : (e : FEnv) → substProc e stop ≡ stop
subStop [] = refl
subStop (_ ∷ _) = refl

subPut : ∀ {A} (e : FEnv) (v : ValExpr A) (P : Proc) →
  substProc e (put A v P) ≡ put A (substVal e v) (substProc e P)
subPut [] _ _ = refl
subPut (_ ∷ _) _ _ = refl

subGet : ∀ (e : FEnv) (A : Ty) (x : String) (P : Proc) →
  substProc e (get A x P) ≡ get A x (substProc (shadowF x e) P)
subGet [] _ _ _ = refl
subGet (_ ∷ _) _ _ _ = refl

subPick0 : ∀ (e : FEnv) (P : Proc) → substProc e (pick0 P) ≡ pick0 (substProc e P)
subPick0 [] _ = refl
subPick0 (_ ∷ _) _ = refl

subPick1 : ∀ (e : FEnv) (P : Proc) → substProc e (pick1 P) ≡ pick1 (substProc e P)
subPick1 [] _ = refl
subPick1 (_ ∷ _) _ = refl

subCover : ∀ (e : FEnv) (P Q : Proc) →
  substProc e (cover P Q) ≡ cover (substProc e P) (substProc e Q)
subCover [] _ _ = refl
subCover (_ ∷ _) _ _ = refl

subIget : ∀ (e : FEnv) (x : String) (P Q : Proc) →
  substProc e (iget x P Q) ≡
  iget x (substProc (shadowF x e) P) (substProc (shadowF x e) Q)
subIget [] _ _ _ = refl
subIget (_ ∷ _) _ _ _ = refl

subMget : ∀ (e : FEnv) (A : Ty) (x : String) (ps : List PArm) →
  substProc e (mget A x ps) ≡ mget A x (substArms (shadowF x e) ps)
subMget [] _ _ ps = ≡mget (sym (armsId ps))
subMget (_ ∷ _) _ _ _ = refl

subNDone : (es : List FEnv) → substN es done ≡ done
subNDone [] = refl
subNDone (e ∷ es) rewrite subNDone es = subDone e

subNStop : (es : List FEnv) → substN es stop ≡ stop
subNStop [] = refl
subNStop (e ∷ es) rewrite subNStop es = subStop e

subNPut : ∀ {A} (es : List FEnv) (v : ValExpr A) (P : Proc) →
  substN es (put A v P) ≡ put A (substValN es v) (substN es P)
subNPut [] _ _ = refl
subNPut (e ∷ es) v P rewrite subNPut es v P = subPut e (substValN es v) (substN es P)

subNGet : ∀ (es : List FEnv) (A : Ty) (x : String) (P : Proc) →
  substN es (get A x P) ≡ get A x (substN (shadowN x es) P)
subNGet [] _ _ _ = refl
subNGet (e ∷ es) A x P rewrite subNGet es A x P =
  subGet e A x (substN (shadowN x es) P)

subNPick0 : ∀ (es : List FEnv) (P : Proc) → substN es (pick0 P) ≡ pick0 (substN es P)
subNPick0 [] _ = refl
subNPick0 (e ∷ es) P rewrite subNPick0 es P = subPick0 e (substN es P)

subNPick1 : ∀ (es : List FEnv) (P : Proc) → substN es (pick1 P) ≡ pick1 (substN es P)
subNPick1 [] _ = refl
subNPick1 (e ∷ es) P rewrite subNPick1 es P = subPick1 e (substN es P)

subNCover : ∀ (es : List FEnv) (P Q : Proc) →
  substN es (cover P Q) ≡ cover (substN es P) (substN es Q)
subNCover [] _ _ = refl
subNCover (e ∷ es) P Q rewrite subNCover es P Q =
  subCover e (substN es P) (substN es Q)

subNIget : ∀ (es : List FEnv) (x : String) (P Q : Proc) →
  substN es (iget x P Q) ≡
  iget x (substN (shadowN x es) P) (substN (shadowN x es) Q)
subNIget [] _ _ _ = refl
subNIget (e ∷ es) x P Q rewrite subNIget es x P Q =
  subIget e x (substN (shadowN x es) P) (substN (shadowN x es) Q)

subNMget : ∀ (es : List FEnv) (A : Ty) (x : String) (ps : List PArm) →
  substN es (mget A x ps) ≡ mget A x (substArmsN (shadowN x es) ps)
subNMget [] _ _ ps = ≡mget (sym (armsIdN ps))
subNMget (e ∷ es) A x ps rewrite subNMget es A x ps =
  trans (subMget e A x (substArmsN (shadowN x es) ps))
        (≡mget (pushArms (shadowF x e) (shadowN x es) ps))

-- `pre` is applied before `es`. A concrete prefix reduces to `refl`.
substN-++ : (pre es : List FEnv) (p : Proc) →
  substN (pre ++ es) p ≡ substN pre (substN es p)
substN-++ [] _ p = refl
substN-++ (e ∷ pre) es p rewrite substN-++ pre es p = refl

-- Every index is explicit. An implicit solved inside `armsPre` does
-- not unify with the one the meeting goal needs.
shiftPre : (σ τ : Idx) (ls : List FEnv) (L : Proc)
           (pre es : List FEnv) (p : Proc) →
  Answerρ σ τ (substN ls L) (substN (pre ++ es) p) →
  Answerρ σ τ (substN ls L) (substN pre (substN es p))
shiftPre σ τ ls L pre es p m =
  subst (λ r → Answerρ σ τ (substN ls L) r) (substN-++ pre es p) m

shiftPreL : (σ τ : Idx) (rs : List FEnv) (R : Proc)
            (pre es : List FEnv) (p : Proc) →
  Answerρ σ τ (substN (pre ++ es) p) (substN rs R) →
  Answerρ σ τ (substN pre (substN es p)) (substN rs R)
shiftPreL σ τ rs R pre es p m =
  subst (λ r → Answerρ σ τ r (substN rs R)) (substN-++ pre es p) m

-- The arm `openNamed` returns, so the equality a concrete value needs is `refl`.
opened : Proc → Maybe FEnv → Maybe Proc
opened _ nothing = nothing
opened p (just e) = just (substProc e p)

openView : String → String → List String → Spine → Maybe FEnv
openView k c xs sp with k == c | rawSpine sp
... | false | _ = nothing
... | true | nothing = nothing
... | true | just rs = lenEnv xs rs

open-agree : (k c : String) (xs : List String) (p : Proc) (sp : Spine) →
  openNamed k c xs p sp ≡ opened p (openView k c xs sp)
open-agree k c xs p sp with k == c | rawSpine sp
open-agree k c xs p sp | false | _ = refl
open-agree k c xs p sp | true | nothing = refl
open-agree k c xs p sp | true | just rs with lenEnv xs rs
open-agree k c xs p sp | true | just rs | nothing = refl
open-agree k c xs p sp | true | just rs | just _ = refl

data ArmAns (ans : Proc → Set) : List PArm → Set where
  aa-nil   : ArmAns ans []
  aa-bare  : ∀ {p qs} → ans p → ArmAns ans qs → ArmAns ans (bare p ∷ qs)
  aa-named : ∀ {c xs p qs} →
    ((e : FEnv) → ans (substProc e p)) →
    ArmAns ans qs →
    ArmAns ans (named c xs p ∷ qs)
  aa-prod  : ∀ {pat p qs} →
    ((e : FEnv) → ans (substProc e p)) →
    ArmAns ans qs →
    ArmAns ans (prod pat p ∷ qs)
  aa-fork  : ∀ {c xs y qs ps} →
    ((e : FEnv) → ArmAns (λ R → ans (substProc e R)) qs) →
    ArmAns ans ps →
    ArmAns ans (fork c xs y qs ∷ ps)

data Found (ans : Proc → Set) (cs : List Ctor) (c : String) (sp : Spine) (qs : List PArm) : Set where
  got    : (R : Proc) → ans R → nthProc cs c sp qs ≡ just R → Found ans cs c sp qs
  missed : nthProc cs c sp qs ≡ nothing → Found ans cs c sp qs

-- Remember the comparison `nthProc` makes. The proof is `refl` when
-- the names are concrete, which is what a computed meeting needs.
data Reveal {A B : Set} (f : A → B) (x : A) (y : B) : Set where
  ≡is : f x ≡ y → Reveal f x y

reveal : ∀ {A B : Set} (f : A → B) (x : A) → Reveal f x (f x)
reveal _ _ = ≡is refl

namedHit : ∀ {ans} (k : String) (xs : List String) (p : Proc) (sp : Spine)
  (cs′ : List Ctor) (c : String) (qs : List PArm) (n : String) (fs : List Fld) →
  (c == n) ≡ true →
  (e? : Maybe FEnv) →
  openNamed k c xs p sp ≡ opened p e? →
  ((e : FEnv) → ans (substProc e p)) →
  Found ans (ctor n fs ∷ cs′) c sp (named k xs p ∷ qs)
namedHit k xs p sp cs′ c qs n fs eqn nothing ag _ =
  missed (trans (cong (λ b → pickCtor b (named k xs p) sp cs′ c qs) eqn) ag)
namedHit k xs p sp cs′ c qs n fs eqn (just e) ag f =
  got (substProc e p) (f e)
    (trans (cong (λ b → pickCtor b (named k xs p) sp cs′ c qs) eqn) ag)

tailAns : ∀ {ans a ps} → ArmAns ans (a ∷ ps) → ArmAns ans ps
tailAns (aa-bare _ as) = as
tailAns (aa-named _ as) = as
tailAns (aa-prod _ as) = as
tailAns (aa-fork _ as) = as

-- The process half of an answer. `openFork` returns that process.
proj : ∀ {ans : Proc → Set} → Maybe (Σ Proc ans) → Maybe Proc
proj nothing = nothing
proj (just (R , _)) = just R

-- Substitute the process `armAns` selected. The answer is already the
-- outer one, so it is not substituted again.
mapPick : (ans : Proc → Set) (e : FEnv) →
         Maybe (Σ Proc (λ R → ans (substProc e R))) → Maybe (Σ Proc ans)
mapPick _ _ nothing = nothing
mapPick _ e (just (R , a)) = just (substProc e R , a)

map-proj : (ans : Proc → Set) (e : FEnv)
           (hit : Maybe (Σ Proc (λ R → ans (substProc e R)))) →
           proj (mapPick ans e hit) ≡ bindM (proj hit) (λ p → just (substProc e p))
map-proj _ _ nothing = refl
map-proj _ _ (just (_ , _)) = refl

-- The arm `armOf` returns, together with the answer stored for it.
-- A fork reads one field and substitutes the outer fields into the
-- arm that field selects.
mutual
  armAns : ∀ {ans} (A : Ty) (u : Val A) (qs : List PArm) →
           ArmAns ans qs → Maybe (Σ Proc ans)
  armAns bit b0 [] _ = nothing
  armAns bit b0 (_ ∷ []) _ = nothing
  armAns bit b0 (_ ∷ _ ∷ _ ∷ _) _ = nothing
  armAns bit b0 (bare p ∷ _ ∷ []) (aa-bare a _) = just (p , a)
  armAns bit b0 (named _ [] p ∷ _ ∷ []) (aa-named f _) = just (p , f [])
  armAns bit b0 (named _ (_ ∷ _) _ ∷ _ ∷ []) _ = nothing
  armAns bit b0 (prod _ _ ∷ _ ∷ []) _ = nothing
  armAns bit b0 (fork _ _ _ _ ∷ _ ∷ []) _ = nothing
  armAns bit b1 [] _ = nothing
  armAns bit b1 (_ ∷ []) _ = nothing
  armAns bit b1 (_ ∷ _ ∷ _ ∷ _) _ = nothing
  armAns bit b1 (_ ∷ bare q ∷ []) an with tailAns an
  ... | aa-bare a _ = just (q , a)
  armAns bit b1 (_ ∷ named _ [] q ∷ []) an with tailAns an
  ... | aa-named f _ = just (q , f [])
  armAns bit b1 (_ ∷ named _ (_ ∷ _) _ ∷ []) _ = nothing
  armAns bit b1 (_ ∷ prod _ _ ∷ []) _ = nothing
  armAns bit b1 (_ ∷ fork _ _ _ _ ∷ []) _ = nothing
  armAns nat _ _ _ = nothing
  armAns unit _ _ _ = nothing
  armAns (vec _ _) _ _ _ = nothing
  armAns (pair _ _) (tup _ _) (_ ∷ _ ∷ _) _ = nothing
  armAns (pair _ _) (tup _ _) [] _ = nothing
  armAns (pair _ _) (tup a b) (prod (pPair x y) p ∷ []) (aa-prod f _)
    with openPair x y a b
  ... | nothing = nothing
  ... | just e = just (substProc e p , f e)
  armAns (pair _ _) (tup _ _) (prod (pRec _) _ ∷ []) _ = nothing
  armAns (pair _ _) (tup _ _) (bare _ ∷ []) _ = nothing
  armAns (pair _ _) (tup _ _) (named _ _ _ ∷ []) _ = nothing
  armAns (pair _ _) (tup _ _) (fork _ _ _ _ ∷ []) _ = nothing
  armAns (rec _) (rec _) (_ ∷ _ ∷ _) _ = nothing
  armAns (rec _) (rec _) [] _ = nothing
  armAns (rec _) (rec row) (prod (pRec bs) p ∷ []) (aa-prod f _)
    with openRec bs row
  ... | nothing = nothing
  ... | just e = just (substProc e p , f e)
  armAns (rec _) (rec _) (prod (pPair _ _) _ ∷ []) _ = nothing
  armAns (rec _) (rec _) (bare _ ∷ []) _ = nothing
  armAns (rec _) (rec _) (named _ _ _ ∷ []) _ = nothing
  armAns (rec _) (rec _) (fork _ _ _ _ ∷ []) _ = nothing
  armAns (dat d _) (con c sp) qs an = nthAns (ctorsOf d) c sp qs an

  nthAns : ∀ {ans} (cs : List Ctor) (c : String) (sp : Spine) (qs : List PArm) →
           ArmAns ans qs → Maybe (Σ Proc ans)
  nthAns [] _ _ _ _ = nothing
  nthAns (_ ∷ _) _ _ [] _ = nothing
  nthAns (ctor n _ ∷ cs) c sp (bare p ∷ qs) (aa-bare a as) with c == n
  ... | true = just (p , a)
  ... | false = nthAns cs c sp qs as
  nthAns (ctor n _ ∷ cs) c sp (named k xs p ∷ qs) (aa-named f as) with c == n
  ... | false = nthAns cs c sp qs as
  ... | true with openView k c xs sp
  ... | nothing = nothing
  ... | just e = just (substProc e p , f e)
  nthAns (ctor n _ ∷ cs) c sp (prod _ _ ∷ qs) (aa-prod _ as) with c == n
  ... | true = nothing
  ... | false = nthAns cs c sp qs as
  nthAns (ctor n _ ∷ cs) c sp (fork k xs y inner ∷ qs) (aa-fork g as) with c == n
  ... | true = forkAns k c xs y inner sp g
  ... | false = nthAns cs c sp qs as

  forkAns : ∀ {ans} (k c : String) (xs : List String) (y : String)
            (inner : List PArm) (sp : Spine) →
            ((e : FEnv) → ArmAns (λ R → ans (substProc e R)) inner) →
            Maybe (Σ Proc ans)
  forkAns k c xs y inner sp g =
    forkAt (k == c) (rawSpine sp) k c xs y inner sp g

  forkAt : ∀ {ans} (b : Bool) (mr : Maybe (List Raw))
           (k c : String) (xs : List String) (y : String)
           (inner : List PArm) (sp : Spine) →
           ((e : FEnv) → ArmAns (λ R → ans (substProc e R)) inner) →
           Maybe (Σ Proc ans)
  forkAt false _ _ _ _ _ _ _ _ = nothing
  forkAt true nothing _ _ _ _ _ _ _ = nothing
  forkAt true (just rs) _ _ xs y inner sp g =
    forkEnv (lenEnv xs rs) xs y inner sp g

  forkEnv : ∀ {ans} (me : Maybe FEnv) (xs : List String) (y : String)
            (inner : List PArm) (sp : Spine) →
            ((e : FEnv) → ArmAns (λ R → ans (substProc e R)) inner) →
            Maybe (Σ Proc ans)
  forkEnv nothing _ _ _ _ _ = nothing
  forkEnv (just e) xs y inner sp g = seekAns xs y e inner sp (g e)

  -- The answer in `an` is already the outer answer after this
  -- field environment replaces the binders. The process is substituted
  -- once; the answer is not.
  pickAns : ∀ {ans A} (e : FEnv) (v : Val A) (qs : List PArm) →
            ArmAns (λ R → ans (substProc e R)) qs → Maybe (Σ Proc ans)
  pickAns {ans} e v qs an = mapPick ans e (armAns _ v qs an)

  seekAns : ∀ {ans} (xs : List String) (y : String) (e : FEnv)
            (qs : List PArm) (sp : Spine) →
            ArmAns (λ R → ans (substProc e R)) qs → Maybe (Σ Proc ans)
  seekAns [] _ _ _ _ _ = nothing
  seekAns (_ ∷ _) _ _ _ snil _ = nothing
  seekAns (x ∷ xs) y e qs (scons A v sp) an =
    seekAnsAt A x xs y e qs v sp an (x ≟ y)

  seekAnsAt : ∀ {ans} (A : Ty) (x : String) (xs : List String) (y : String)
              (e : FEnv) (qs : List PArm) (v : Val A) (sp : Spine) →
              ArmAns (λ R → ans (substProc e R)) qs →
              Dec (x ≡ y) → Maybe (Σ Proc ans)
  seekAnsAt _ _ xs y e qs _ sp an (no′ _) = seekAns xs y e qs sp an
  seekAnsAt _ _ _ _ e qs v _ an (yes′ _) = pickAns e v qs an

-- `armAns` agrees with `armOf`. The lemmas sit outside the evaluator
-- so a constructor value unfolds `armAns` while the proof is checked.
-- The comparisons are arguments, rewritten to constructors. A `with`
-- would turn the answer predicate into a function of the scrutinee.
mutual
  arm-proj : ∀ {ans} (A : Ty) (u : Val A) (qs : List PArm) (an : ArmAns ans qs) →
             proj (armAns A u qs an) ≡ armOf A u qs
  arm-proj bit b0 [] _ = refl
  arm-proj bit b0 (_ ∷ []) _ = refl
  arm-proj bit b0 (_ ∷ _ ∷ _ ∷ _) _ = refl
  arm-proj bit b0 (bare _ ∷ _ ∷ []) (aa-bare _ _) = refl
  arm-proj bit b0 (named _ [] _ ∷ _ ∷ []) (aa-named _ _) = refl
  arm-proj bit b0 (named _ (_ ∷ _) _ ∷ _ ∷ []) _ = refl
  arm-proj bit b0 (prod _ _ ∷ _ ∷ []) _ = refl
  arm-proj bit b0 (fork _ _ _ _ ∷ _ ∷ []) _ = refl
  arm-proj bit b1 [] _ = refl
  arm-proj bit b1 (_ ∷ []) _ = refl
  arm-proj bit b1 (_ ∷ _ ∷ _ ∷ _) _ = refl
  arm-proj bit b1 (_ ∷ bare _ ∷ []) an with tailAns an
  ... | aa-bare _ _ = refl
  arm-proj bit b1 (_ ∷ named _ [] _ ∷ []) an with tailAns an
  ... | aa-named _ _ = refl
  arm-proj bit b1 (_ ∷ named _ (_ ∷ _) _ ∷ []) _ = refl
  arm-proj bit b1 (_ ∷ prod _ _ ∷ []) _ = refl
  arm-proj bit b1 (_ ∷ fork _ _ _ _ ∷ []) _ = refl
  arm-proj nat _ _ _ = refl
  arm-proj unit _ _ _ = refl
  arm-proj (vec _ _) _ _ _ = refl
  arm-proj (pair _ _) (tup a b) (prod (pPair x y) p ∷ []) (aa-prod _ _)
    with openPair x y a b
  ... | nothing = refl
  ... | just _ = refl
  arm-proj (pair _ _) (tup _ _) (prod (pRec _) _ ∷ []) _ = refl
  arm-proj (pair _ _) (tup _ _) (bare _ ∷ []) _ = refl
  arm-proj (pair _ _) (tup _ _) (named _ _ _ ∷ []) _ = refl
  arm-proj (pair _ _) (tup _ _) (fork _ _ _ _ ∷ []) _ = refl
  arm-proj (pair _ _) (tup _ _) [] _ = refl
  arm-proj (pair _ _) (tup _ _) (_ ∷ _ ∷ _) _ = refl
  arm-proj (rec _) (rec row) (prod (pRec bs) p ∷ []) (aa-prod _ _)
    with openRec bs row
  ... | nothing = refl
  ... | just _ = refl
  arm-proj (rec _) (rec _) (prod (pPair _ _) _ ∷ []) _ = refl
  arm-proj (rec _) (rec _) (bare _ ∷ []) _ = refl
  arm-proj (rec _) (rec _) (named _ _ _ ∷ []) _ = refl
  arm-proj (rec _) (rec _) (fork _ _ _ _ ∷ []) _ = refl
  arm-proj (rec _) (rec _) [] _ = refl
  arm-proj (rec _) (rec _) (_ ∷ _ ∷ _) _ = refl
  arm-proj (dat d _) (con c sp) qs an = nth-proj (ctorsOf d) c sp qs an

  nth-proj : ∀ {ans} (cs : List Ctor) (c : String) (sp : Spine) (qs : List PArm)
             (an : ArmAns ans qs) →
             proj (nthAns cs c sp qs an) ≡ nthProc cs c sp qs
  nth-proj [] _ _ _ _ = refl
  nth-proj (_ ∷ _) _ _ [] _ = refl
  nth-proj (ctor n _ ∷ cs) c sp (bare _ ∷ qs) (aa-bare _ as) with c == n
  ... | true = refl
  ... | false = nth-proj cs c sp qs as
  nth-proj (ctor n _ ∷ cs) c sp (named k xs p ∷ qs) (aa-named _ as) with c == n
  ... | false = nth-proj cs c sp qs as
  ... | true rewrite open-agree k c xs p sp with openView k c xs sp
  ... | nothing = refl
  ... | just _ = refl
  nth-proj (ctor n _ ∷ cs) c sp (prod _ _ ∷ qs) (aa-prod _ as) with c == n
  ... | true = refl
  ... | false = nth-proj cs c sp qs as
  nth-proj {ans} (ctor n _ ∷ cs) c sp (fork k xs y inner ∷ qs) (aa-fork g as) with c == n
  ... | true = fork-agree ans k c xs y inner sp g
  ... | false = nth-proj cs c sp qs as

  -- `ans` is explicit. An implicit here is solved apart for each
  -- mutually recursive clause, and those solutions do not unify.
  fork-agree : (ans : Proc → Set) (k c : String) (xs : List String) (y : String)
               (inner : List PArm) (sp : Spine)
               (g : (e : FEnv) → ArmAns (λ R → ans (substProc e R)) inner) →
               proj (forkAns k c xs y inner sp g) ≡ openFork k c xs y inner sp
  fork-agree ans k c xs y inner sp g =
    fork-at ans (k == c) (rawSpine sp) k c xs y inner sp g

  fork-at : (ans : Proc → Set) (b : Bool) (mr : Maybe (List Raw))
            (k c : String) (xs : List String) (y : String)
            (inner : List PArm) (sp : Spine)
            (g : (e : FEnv) → ArmAns (λ R → ans (substProc e R)) inner) →
            proj (forkAt b mr k c xs y inner sp g) ≡ openAt b mr xs y inner sp
  fork-at _ false _ _ _ _ _ _ _ _ = refl
  fork-at _ true nothing _ _ _ _ _ _ _ = refl
  fork-at ans true (just rs) _ _ xs y inner sp g =
    fork-env ans (lenEnv xs rs) xs y inner sp g

  fork-env : (ans : Proc → Set) (me : Maybe FEnv) (xs : List String) (y : String)
             (inner : List PArm) (sp : Spine)
             (g : (e : FEnv) → ArmAns (λ R → ans (substProc e R)) inner) →
             proj (forkEnv me xs y inner sp g) ≡ openEnv me xs y inner sp
  fork-env _ nothing _ _ _ _ _ = refl
  fork-env ans (just e) xs y inner sp g = seek-agree ans xs y e inner sp (g e)

  pick-agree : (ans : Proc → Set) {A : Ty} (e : FEnv) (v : Val A) (qs : List PArm)
               (an : ArmAns (λ R → ans (substProc e R)) qs) →
               proj (pickAns e v qs an) ≡
               bindM (armOf A v qs) (λ p → just (substProc e p))
  pick-agree ans {A} e v qs an =
    trans (map-proj ans e (armAns A v qs an))
          (cong (λ h → bindM h (λ p → just (substProc e p))) (arm-proj A v qs an))

  seek-agree : (ans : Proc → Set) (xs : List String) (y : String) (e : FEnv)
               (qs : List PArm) (sp : Spine)
               (an : ArmAns (λ R → ans (substProc e R)) qs) →
               proj (seekAns xs y e qs sp an) ≡ seek xs y e qs sp
  seek-agree _ [] _ _ _ _ _ = refl
  seek-agree _ (_ ∷ _) _ _ _ snil _ = refl
  seek-agree ans (x ∷ xs) y e qs (scons A v sp) an =
    seek-at ans A x xs y e qs v sp an (x ≟ y)

  seek-at : (ans : Proc → Set) (A : Ty) (x : String) (xs : List String) (y : String)
            (e : FEnv) (qs : List PArm) (v : Val A) (sp : Spine)
            (an : ArmAns (λ R → ans (substProc e R)) qs)
            (d : Dec (x ≡ y)) →
            proj (seekAnsAt A x xs y e qs v sp an d) ≡
            seekAt A x xs y e qs v sp d
  seek-at ans _ _ xs y e qs _ sp an (no′ _) = seek-agree ans xs y e qs sp an
  seek-at ans _ _ _ _ e qs v _ an (yes′ _) = pick-agree ans e v qs an

-- A fork hits when `forkAns` returns the process `openFork` returns.
hitFork : ∀ {ans} (k : String) (xs : List String) (y : String) (inner : List PArm)
  (sp : Spine) (cs′ : List Ctor) (c : String) (qs : List PArm)
  (n : String) (fs : List Fld) →
  (g : (e : FEnv) → ArmAns (λ R → ans (substProc e R)) inner) →
  (c == n) ≡ true →
  (hit : Maybe (Σ Proc ans)) →
  forkAns k c xs y inner sp g ≡ hit →
  Found ans (ctor n fs ∷ cs′) c sp (fork k xs y inner ∷ qs)
hitFork {ans} k xs y inner sp cs′ c qs n fs g eqn nothing eq =
  missed (trans (cong (λ b → pickCtor b (fork k xs y inner) sp cs′ c qs) eqn)
                (trans (sym (fork-agree ans k c xs y inner sp g)) (cong proj eq)))
hitFork {ans} k xs y inner sp cs′ c qs n fs g eqn (just (R , a)) eq =
  got R a (trans (cong (λ b → pickCtor b (fork k xs y inner) sp cs′ c qs) eqn)
                 (trans (sym (fork-agree ans k c xs y inner sp g)) (cong proj eq)))

forkHit : ∀ {ans} (k : String) (xs : List String) (y : String) (inner : List PArm)
  (sp : Spine) (cs′ : List Ctor) (c : String) (qs : List PArm)
  (n : String) (fs : List Fld) →
  ((e : FEnv) → ArmAns (λ R → ans (substProc e R)) inner) →
  (c == n) ≡ true →
  Found ans (ctor n fs ∷ cs′) c sp (fork k xs y inner ∷ qs)
forkHit k xs y inner sp cs′ c qs n fs g eqn =
  hitFork k xs y inner sp cs′ c qs n fs g eqn (forkAns k c xs y inner sp g) refl

nthBoth : ∀ {ans} (cs : List Ctor) (c : String) (sp : Spine) (qs : List PArm) →
  ArmAns ans qs → Found ans cs c sp qs
nthBoth [] _ _ _ _ = missed refl
nthBoth (_ ∷ _) _ _ [] _ = missed refl
nthBoth (ctor n _ ∷ cs′) c sp (bare r ∷ qs) (aa-bare a as) with c == n | reveal (_==_ c) n
... | true | ≡is eqn =
  got r a (trans (cong (λ b → pickCtor b (bare r) sp cs′ c qs) eqn) refl)
... | false | ≡is eqn with nthBoth cs′ c sp qs as
... | got R b pr =
  got R b (trans (cong (λ b → pickCtor b (bare r) sp cs′ c qs) eqn) pr)
... | missed pr =
  missed (trans (cong (λ b → pickCtor b (bare r) sp cs′ c qs) eqn) pr)
nthBoth (ctor n fs ∷ cs′) c sp (named k xs p ∷ qs) (aa-named f as) with c == n | reveal (_==_ c) n
... | true | ≡is eqn = namedHit k xs p sp cs′ c qs n fs eqn (openView k c xs sp) (open-agree k c xs p sp) f
... | false | ≡is eqn with nthBoth cs′ c sp qs as
... | got R b pr =
  got R b (trans (cong (λ b → pickCtor b (named k xs p) sp cs′ c qs) eqn) pr)
... | missed pr =
  missed (trans (cong (λ b → pickCtor b (named k xs p) sp cs′ c qs) eqn) pr)
nthBoth (ctor n _ ∷ cs′) c sp (prod pat q ∷ qs) (aa-prod _ as) with c == n | reveal (_==_ c) n
... | true | ≡is eqn =
  missed (trans (cong (λ b → pickCtor b (prod pat q) sp cs′ c qs) eqn) refl)
... | false | ≡is eqn with nthBoth cs′ c sp qs as
... | got R b pr =
  got R b (trans (cong (λ b → pickCtor b (prod pat q) sp cs′ c qs) eqn) pr)
... | missed pr =
  missed (trans (cong (λ b → pickCtor b (prod pat q) sp cs′ c qs) eqn) pr)
nthBoth (ctor n fs ∷ cs′) c sp (fork k xs y inner ∷ qs) (aa-fork g as)
  with c == n | reveal (_==_ c) n
... | true | ≡is eqn = forkHit k xs y inner sp cs′ c qs n fs g eqn
... | false | ≡is eqn with nthBoth cs′ c sp qs as
... | got R b pr =
  got R b (trans (cong (λ b → pickCtor b (fork k xs y inner) sp cs′ c qs) eqn) pr)
... | missed pr =
  missed (trans (cong (λ b → pickCtor b (fork k xs y inner) sp cs′ c qs) eqn) pr)

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

selLit : ∀ {A} {v : ValExpr A} {u : Val A} {ps : List PArm} {R : Proc} →
  ground v ≡ just u →
  armOf A u ps ≡ just R →
  armExpr v ps ≡ just R
selLit {v = v} {ps = ps} geq aeq = trans (cong (armStep ps) geq) aeq

missedLit : ∀ {A} {v : ValExpr A} {u : Val A} {ps : List PArm} →
  ground v ≡ just u →
  armOf A u ps ≡ nothing →
  armExpr v ps ≡ nothing
missedLit {v = v} {ps = ps} geq aeq = trans (cong (armStep ps) geq) aeq

-- A bit literal selects one side. The other answer is not used.
finishPutBit : ∀ {σ τ x P Q R} →
  (w : ValExpr bit) →
  Answerρ σ (ext x (lit b0) τ) P Q →
  Answerρ σ (ext x (lit b1) τ) P R →
  Answerρ σ τ (put bit w P) (iget x Q R)
finishPutBit (lit b0) a _ = on-b0-iget a
finishPutBit (lit b1) _ a = on-b1-iget a
finishPutBit (var _) _ _ = no (λ ())
finishPutBit (call _ _) _ _ = no (λ ())

finishIgetBit : ∀ {σ τ x P Q R} →
  (w : ValExpr bit) →
  Answerρ (ext x (lit b0) σ) τ P R →
  Answerρ (ext x (lit b1) σ) τ Q R →
  Answerρ σ τ (iget x P Q) (put bit w R)
finishIgetBit (lit b0) a _ = on-iget-b0 a
finishIgetBit (lit b1) _ a = on-iget-b1 a
finishIgetBit (var _) _ _ = no (λ ())
finishIgetBit (call _ _) _ _ = no (λ ())

-- `armOf` on a product arm is `fillArm` of the components. Case on
-- that environment, so the equality the meeting needs is the one
-- `fillArm` computes.
onPairPut : ∀ {σ τ B x P X Y} (v : ValExpr (pair X Y)) →
  applyTy σ (pair X Y) ≡ applyTy τ B →
  sent v ≡ true →
  (n y : String) (a : Val X) (b : Val Y) (p : Proc) (e? : Maybe FEnv) →
  ground v ≡ just (tup a b) →
  armOf (pair X Y) (tup a b) (prod (pPair n y) p ∷ []) ≡ fillArm p e? →
  ((e : FEnv) → Answerρ σ (ext x v τ) P (substProc e p)) →
  Answerρ σ τ (put (pair X Y) v P) (mget B x (prod (pPair n y) p ∷ []))
onPairPut v eq fv n y a b p nothing geq aeq _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq)
      (missedLit {v = v} {ps = prod (pPair n y) p ∷ []} geq aeq)) })
onPairPut v eq fv n y a b p (just e) geq aeq f =
  usePut eq fv (selLit {v = v} {ps = prod (pPair n y) p ∷ []} geq aeq) (f e)

onPairMget : ∀ {σ τ A x P X Y} (v : ValExpr (pair X Y)) →
  applyTy σ A ≡ applyTy τ (pair X Y) →
  sent v ≡ true →
  (n y : String) (a : Val X) (b : Val Y) (p : Proc) (e? : Maybe FEnv) →
  ground v ≡ just (tup a b) →
  armOf (pair X Y) (tup a b) (prod (pPair n y) p ∷ []) ≡ fillArm p e? →
  ((e : FEnv) → Answerρ (ext x v σ) τ (substProc e p) P) →
  Answerρ σ τ (mget A x (prod (pPair n y) p ∷ [])) (put (pair X Y) v P)
onPairMget v eq fv n y a b p nothing geq aeq _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq)
      (missedLit {v = v} {ps = prod (pPair n y) p ∷ []} geq aeq)) })
onPairMget v eq fv n y a b p (just e) geq aeq f =
  useMget eq fv (selLit {v = v} {ps = prod (pPair n y) p ∷ []} geq aeq) (f e)

onRecPut : ∀ {σ τ B x P fs} (v : ValExpr (rec fs)) →
  applyTy σ (rec fs) ≡ applyTy τ B →
  sent v ≡ true →
  (bs : List (String × String)) (row : Row fs) (p : Proc) (e? : Maybe FEnv) →
  ground v ≡ just (rec row) →
  armOf (rec fs) (rec row) (prod (pRec bs) p ∷ []) ≡ fillArm p e? →
  ((e : FEnv) → Answerρ σ (ext x v τ) P (substProc e p)) →
  Answerρ σ τ (put (rec fs) v P) (mget B x (prod (pRec bs) p ∷ []))
onRecPut v eq fv bs row p nothing geq aeq _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq)
      (missedLit {v = v} {ps = prod (pRec bs) p ∷ []} geq aeq)) })
onRecPut v eq fv bs row p (just e) geq aeq f =
  usePut eq fv (selLit {v = v} {ps = prod (pRec bs) p ∷ []} geq aeq) (f e)

onRecMget : ∀ {σ τ A x P fs} (v : ValExpr (rec fs)) →
  applyTy σ A ≡ applyTy τ (rec fs) →
  sent v ≡ true →
  (bs : List (String × String)) (row : Row fs) (p : Proc) (e? : Maybe FEnv) →
  ground v ≡ just (rec row) →
  armOf (rec fs) (rec row) (prod (pRec bs) p ∷ []) ≡ fillArm p e? →
  ((e : FEnv) → Answerρ (ext x v σ) τ (substProc e p) P) →
  Answerρ σ τ (mget A x (prod (pRec bs) p ∷ [])) (put (rec fs) v P)
onRecMget v eq fv bs row p nothing geq aeq _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq)
      (missedLit {v = v} {ps = prod (pRec bs) p ∷ []} geq aeq)) })
onRecMget v eq fv bs row p (just e) geq aeq f =
  useMget eq fv (selLit {v = v} {ps = prod (pRec bs) p ∷ []} geq aeq) (f e)

takePut : ∀ {σ τ A B x P} (v : ValExpr A) →
  applyTy σ A ≡ applyTy τ B →
  sent v ≡ true →
  (w : Val A) →
  ground v ≡ just w →
  (qs : List PArm) →
  ArmAns (Answerρ σ (ext x v τ) P) qs →
  Answerρ σ τ (put A v P) (mget B x qs)
takePut v eq fv b0 geq (bare p ∷ q ∷ []) (aa-bare a _) =
  usePut eq fv (selLit {v = v} {ps = bare p ∷ q ∷ []} geq refl) a
takePut v eq fv b0 geq (named c [] p ∷ q ∷ []) (aa-named f _) =
  usePut eq fv (selLit {v = v} {ps = named c [] p ∷ q ∷ []} geq refl) (f [])
takePut v eq fv b0 geq (named c (y ∷ ys) p ∷ q ∷ []) (aa-named _ _) =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = named c (y ∷ ys) p ∷ q ∷ []} geq refl)) })
takePut v eq fv b0 geq (prod pat r ∷ q ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = prod pat r ∷ q ∷ []} geq refl)) })
takePut v eq fv b0 geq (fork k xs y qs ∷ q ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = fork k xs y qs ∷ q ∷ []} geq refl)) })
takePut v eq fv b1 geq (bare p ∷ bare q ∷ []) (aa-bare _ (aa-bare a _)) =
  usePut eq fv (selLit {v = v} {ps = bare p ∷ bare q ∷ []} geq refl) a
takePut v eq fv b1 geq (bare p ∷ named c [] q ∷ []) (aa-bare _ (aa-named f _)) =
  usePut eq fv (selLit {v = v} {ps = bare p ∷ named c [] q ∷ []} geq refl) (f [])
takePut v eq fv b1 geq (bare p ∷ named c (y ∷ ys) q ∷ []) (aa-bare _ (aa-named _ _)) =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = bare p ∷ named c (y ∷ ys) q ∷ []} geq refl)) })
takePut v eq fv b1 geq (named c [] p ∷ bare q ∷ []) (aa-named _ (aa-bare a _)) =
  usePut eq fv (selLit {v = v} {ps = named c [] p ∷ bare q ∷ []} geq refl) a
takePut v eq fv b1 geq (named c [] p ∷ named d [] q ∷ []) (aa-named _ (aa-named f _)) =
  usePut eq fv (selLit {v = v} {ps = named c [] p ∷ named d [] q ∷ []} geq refl) (f [])
takePut v eq fv b1 geq (named c [] p ∷ named d (y ∷ ys) q ∷ []) (aa-named _ (aa-named _ _)) =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = named c [] p ∷ named d (y ∷ ys) q ∷ []} geq refl)) })
takePut v eq fv b1 geq (named c (z ∷ zs) p ∷ bare q ∷ []) (aa-named _ (aa-bare a _)) =
  usePut eq fv (selLit {v = v} {ps = named c (z ∷ zs) p ∷ bare q ∷ []} geq refl) a
takePut v eq fv b1 geq (named c (z ∷ zs) p ∷ named d [] q ∷ []) (aa-named _ (aa-named f _)) =
  usePut eq fv (selLit {v = v} {ps = named c (z ∷ zs) p ∷ named d [] q ∷ []} geq refl) (f [])
takePut v eq fv b1 geq (named c (z ∷ zs) p ∷ named d (y ∷ ys) q ∷ []) (aa-named _ (aa-named _ _)) =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = named c (z ∷ zs) p ∷ named d (y ∷ ys) q ∷ []} geq refl)) })
takePut v eq fv b1 geq (prod pat r ∷ bare q ∷ []) (aa-prod _ (aa-bare a _)) =
  usePut eq fv (selLit {v = v} {ps = prod pat r ∷ bare q ∷ []} geq refl) a
takePut v eq fv b1 geq (prod pat r ∷ named c [] q ∷ []) (aa-prod _ (aa-named f _)) =
  usePut eq fv (selLit {v = v} {ps = prod pat r ∷ named c [] q ∷ []} geq refl) (f [])
takePut v eq fv b1 geq (prod pat r ∷ named c (y ∷ ys) q ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = prod pat r ∷ named c (y ∷ ys) q ∷ []} geq refl)) })
takePut v eq fv b1 geq (p ∷ prod pat r ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = p ∷ prod pat r ∷ []} geq refl)) })
takePut v eq fv b1 geq (fork k xs y r ∷ bare q ∷ []) (aa-fork _ (aa-bare a _)) =
  usePut eq fv (selLit {v = v} {ps = fork k xs y r ∷ bare q ∷ []} geq refl) a
takePut v eq fv b1 geq (fork k xs y r ∷ named c [] q ∷ []) (aa-fork _ (aa-named f _)) =
  usePut eq fv (selLit {v = v} {ps = fork k xs y r ∷ named c [] q ∷ []} geq refl) (f [])
takePut v eq fv b1 geq (fork k xs y r ∷ named c (z ∷ zs) q ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = fork k xs y r ∷ named c (z ∷ zs) q ∷ []} geq refl)) })
takePut v eq fv b1 geq (fork k xs y r ∷ fork k′ xs′ y′ r′ ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = fork k xs y r ∷ fork k′ xs′ y′ r′ ∷ []} geq refl)) })
takePut v eq fv b1 geq (p ∷ fork k xs y r ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = p ∷ fork k xs y r ∷ []} geq refl)) })
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
takePut v eq fv (con {d} c sp) geq qs as′ with nthBoth (ctorsOf d) c sp qs as′
... | got R a pr = usePut eq fv (selLit {v = v} {ps = qs} geq pr) a
... | missed pr =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq pr)) })
takePut v eq fv zero geq qs _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takePut v eq fv (suc _) geq qs _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takePut v eq fv tt geq qs _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takePut v eq fv (tup a b) geq (prod (pPair x y) p ∷ []) (aa-prod f _) =
  onPairPut v eq fv x y a b p (openPair x y a b) geq refl f
takePut v eq fv (tup _ _) geq (prod (pRec bs) q ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = prod (pRec bs) q ∷ []} geq refl)) })
takePut v eq fv (tup _ _) geq (bare q ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = bare q ∷ []} geq refl)) })
takePut v eq fv (tup _ _) geq (named c xs q ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = named c xs q ∷ []} geq refl)) })
takePut v eq fv (tup _ _) geq (fork k xs y r ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = fork k xs y r ∷ []} geq refl)) })
takePut v eq fv (tup _ _) geq [] _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = []} geq refl)) })
takePut v eq fv (tup _ _) geq (q ∷ r ∷ rs) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = q ∷ r ∷ rs} geq refl)) })
takePut v eq fv (rec row) geq (prod (pRec bs) p ∷ []) (aa-prod f _) =
  onRecPut v eq fv bs row p (openRec bs row) geq refl f
takePut v eq fv (rec _) geq (prod (pPair x y) q ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = prod (pPair x y) q ∷ []} geq refl)) })
takePut v eq fv (rec _) geq (bare q ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = bare q ∷ []} geq refl)) })
takePut v eq fv (rec _) geq (named c xs q ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = named c xs q ∷ []} geq refl)) })
takePut v eq fv (rec _) geq (fork k xs y r ∷ []) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = fork k xs y r ∷ []} geq refl)) })
takePut v eq fv (rec _) geq [] _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = []} geq refl)) })
takePut v eq fv (rec _) geq (q ∷ r ∷ rs) _ =
  no (λ { (put-mget _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = q ∷ r ∷ rs} geq refl)) })
takePut v eq fv (rep _) geq qs _ =
  no (λ { (put-mget _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })

takeMget : ∀ {σ τ A B x P} (v : ValExpr B) →
  applyTy σ A ≡ applyTy τ B →
  sent v ≡ true →
  (w : Val B) →
  ground v ≡ just w →
  (qs : List PArm) →
  ArmAns (λ R → Answerρ (ext x v σ) τ R P) qs →
  Answerρ σ τ (mget A x qs) (put B v P)
takeMget v eq fv b0 geq (bare p ∷ q ∷ []) (aa-bare a _) =
  useMget eq fv (selLit {v = v} {ps = bare p ∷ q ∷ []} geq refl) a
takeMget v eq fv b0 geq (named c [] p ∷ q ∷ []) (aa-named f _) =
  useMget eq fv (selLit {v = v} {ps = named c [] p ∷ q ∷ []} geq refl) (f [])
takeMget v eq fv b0 geq (named c (y ∷ ys) p ∷ q ∷ []) (aa-named _ _) =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = named c (y ∷ ys) p ∷ q ∷ []} geq refl)) })
takeMget v eq fv b0 geq (prod pat r ∷ q ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = prod pat r ∷ q ∷ []} geq refl)) })
takeMget v eq fv b0 geq (fork k xs y qs ∷ q ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = fork k xs y qs ∷ q ∷ []} geq refl)) })
takeMget v eq fv b1 geq (bare p ∷ bare q ∷ []) (aa-bare _ (aa-bare a _)) =
  useMget eq fv (selLit {v = v} {ps = bare p ∷ bare q ∷ []} geq refl) a
takeMget v eq fv b1 geq (bare p ∷ named c [] q ∷ []) (aa-bare _ (aa-named f _)) =
  useMget eq fv (selLit {v = v} {ps = bare p ∷ named c [] q ∷ []} geq refl) (f [])
takeMget v eq fv b1 geq (bare p ∷ named c (y ∷ ys) q ∷ []) (aa-bare _ (aa-named _ _)) =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = bare p ∷ named c (y ∷ ys) q ∷ []} geq refl)) })
takeMget v eq fv b1 geq (named c [] p ∷ bare q ∷ []) (aa-named _ (aa-bare a _)) =
  useMget eq fv (selLit {v = v} {ps = named c [] p ∷ bare q ∷ []} geq refl) a
takeMget v eq fv b1 geq (named c [] p ∷ named d [] q ∷ []) (aa-named _ (aa-named f _)) =
  useMget eq fv (selLit {v = v} {ps = named c [] p ∷ named d [] q ∷ []} geq refl) (f [])
takeMget v eq fv b1 geq (named c [] p ∷ named d (y ∷ ys) q ∷ []) (aa-named _ (aa-named _ _)) =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = named c [] p ∷ named d (y ∷ ys) q ∷ []} geq refl)) })
takeMget v eq fv b1 geq (named c (z ∷ zs) p ∷ bare q ∷ []) (aa-named _ (aa-bare a _)) =
  useMget eq fv (selLit {v = v} {ps = named c (z ∷ zs) p ∷ bare q ∷ []} geq refl) a
takeMget v eq fv b1 geq (named c (z ∷ zs) p ∷ named d [] q ∷ []) (aa-named _ (aa-named f _)) =
  useMget eq fv (selLit {v = v} {ps = named c (z ∷ zs) p ∷ named d [] q ∷ []} geq refl) (f [])
takeMget v eq fv b1 geq (named c (z ∷ zs) p ∷ named d (y ∷ ys) q ∷ []) (aa-named _ (aa-named _ _)) =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = named c (z ∷ zs) p ∷ named d (y ∷ ys) q ∷ []} geq refl)) })
takeMget v eq fv b1 geq (prod pat r ∷ bare q ∷ []) (aa-prod _ (aa-bare a _)) =
  useMget eq fv (selLit {v = v} {ps = prod pat r ∷ bare q ∷ []} geq refl) a
takeMget v eq fv b1 geq (prod pat r ∷ named c [] q ∷ []) (aa-prod _ (aa-named f _)) =
  useMget eq fv (selLit {v = v} {ps = prod pat r ∷ named c [] q ∷ []} geq refl) (f [])
takeMget v eq fv b1 geq (prod pat r ∷ named c (y ∷ ys) q ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = prod pat r ∷ named c (y ∷ ys) q ∷ []} geq refl)) })
takeMget v eq fv b1 geq (p ∷ prod pat r ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = p ∷ prod pat r ∷ []} geq refl)) })
takeMget v eq fv b1 geq (fork k xs y r ∷ bare q ∷ []) (aa-fork _ (aa-bare a _)) =
  useMget eq fv (selLit {v = v} {ps = fork k xs y r ∷ bare q ∷ []} geq refl) a
takeMget v eq fv b1 geq (fork k xs y r ∷ named c [] q ∷ []) (aa-fork _ (aa-named f _)) =
  useMget eq fv (selLit {v = v} {ps = fork k xs y r ∷ named c [] q ∷ []} geq refl) (f [])
takeMget v eq fv b1 geq (fork k xs y r ∷ named c (z ∷ zs) q ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = fork k xs y r ∷ named c (z ∷ zs) q ∷ []} geq refl)) })
takeMget v eq fv b1 geq (fork k xs y r ∷ fork k′ xs′ y′ r′ ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = fork k xs y r ∷ fork k′ xs′ y′ r′ ∷ []} geq refl)) })
takeMget v eq fv b1 geq (p ∷ fork k xs y r ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = p ∷ fork k xs y r ∷ []} geq refl)) })
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
takeMget v eq fv (con {d} c sp) geq qs as′ with nthBoth (ctorsOf d) c sp qs as′
... | got R a pr = useMget eq fv (selLit {v = v} {ps = qs} geq pr) a
... | missed pr =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq pr)) })
takeMget v eq fv zero geq qs _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takeMget v eq fv (suc _) geq qs _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takeMget v eq fv tt geq qs _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })
takeMget v eq fv (tup a b) geq (prod (pPair x y) p ∷ []) (aa-prod f _) =
  onPairMget v eq fv x y a b p (openPair x y a b) geq refl f
takeMget v eq fv (tup _ _) geq (prod (pRec bs) q ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = prod (pRec bs) q ∷ []} geq refl)) })
takeMget v eq fv (tup _ _) geq (bare q ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = bare q ∷ []} geq refl)) })
takeMget v eq fv (tup _ _) geq (named c xs q ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = named c xs q ∷ []} geq refl)) })
takeMget v eq fv (tup _ _) geq (fork k xs y r ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = fork k xs y r ∷ []} geq refl)) })
takeMget v eq fv (tup _ _) geq [] _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = []} geq refl)) })
takeMget v eq fv (tup _ _) geq (q ∷ r ∷ rs) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = q ∷ r ∷ rs} geq refl)) })
takeMget v eq fv (rec row) geq (prod (pRec bs) p ∷ []) (aa-prod f _) =
  onRecMget v eq fv bs row p (openRec bs row) geq refl f
takeMget v eq fv (rec _) geq (prod (pPair x y) q ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = prod (pPair x y) q ∷ []} geq refl)) })
takeMget v eq fv (rec _) geq (bare q ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = bare q ∷ []} geq refl)) })
takeMget v eq fv (rec _) geq (named c xs q ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = named c xs q ∷ []} geq refl)) })
takeMget v eq fv (rec _) geq (fork k xs y r ∷ []) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = fork k xs y r ∷ []} geq refl)) })
takeMget v eq fv (rec _) geq [] _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = []} geq refl)) })
takeMget v eq fv (rec _) geq (q ∷ r ∷ rs) _ =
  no (λ { (mget-put _ _ neq _) →
    just≢nothing (trans (sym neq) (missedLit {v = v} {ps = q ∷ r ∷ rs} geq refl)) })
takeMget v eq fv (rep _) geq qs _ =
  no (λ { (mget-put _ _ neq _) → just≢nothing (trans (sym neq) (missedLit {v = v} {ps = qs} geq refl)) })

concludePut : ∀ {σ τ A B v x P} (ps : List PArm) →
  ArmAns (Answerρ σ (ext x v τ) P) ps →
  Answerρ σ τ (put A v P) (mget B x ps)
concludePut {σ} {τ} {A} {B} {v} {x} {P} ps as
  with ty≟ (applyTy σ A) (applyTy τ B) | sent? v | ground v in geq
... | no′ ¬eq | _ | _ = no (λ { (put-mget eq _ _ _) → ¬eq eq })
... | yes′ _ | no′ nf | _ = no (λ { (put-mget _ fv _ _) → nf fv })
... | yes′ _ | yes′ _ | nothing = no (noGround geq)
... | yes′ eq | yes′ fv | just u = takePut v eq fv u geq ps as

concludeMget : ∀ {σ τ A B v x P} (ps : List PArm) →
  ArmAns (λ R → Answerρ (ext x v σ) τ R P) ps →
  Answerρ σ τ (mget A x ps) (put B v P)
concludeMget {σ} {τ} {A} {B} {v} {x} {P} ps as
  with ty≟ (applyTy σ A) (applyTy τ B) | sent? v | ground v in geq
... | no′ ¬eq | _ | _ = no (λ { (mget-put eq _ _ _) → ¬eq eq })
... | yes′ _ | no′ nf | _ = no (λ { (mget-put _ fv _ _) → nf fv })
... | yes′ _ | yes′ _ | nothing = no (noGround′ geq)
... | yes′ eq | yes′ fv | just u = takeMget v eq fv u geq ps as

-- Move an answer across a predicate that agrees on every process.
retarget : ∀ {ans1 ans2 ps} →
  (∀ {R} → ans1 R → ans2 R) →
  ArmAns ans1 ps → ArmAns ans2 ps
retarget _ aa-nil = aa-nil
retarget f (aa-bare a as) = aa-bare (f a) (retarget f as)
retarget f (aa-named g as) = aa-named (λ e → f (g e)) (retarget f as)
retarget f (aa-prod g as) = aa-prod (λ e → f (g e)) (retarget f as)
retarget f (aa-fork g as) = aa-fork (λ e → retarget f (g e)) (retarget f as)

mutual
  -- `ls` substitutes the left process and `rs` the right one, outermost
  -- environment first. An empty list is the process as written.
  meetN : (ls rs : List FEnv) (σ τ : Idx) (L R : Proc) →
    Answerρ σ τ (substN ls L) (substN rs R)

  armsR : (ls rs : List FEnv) (σ τ : Idx) (L : Proc) (qs : List PArm) →
    ArmAns (λ S → Answerρ σ τ (substN ls L) S) (substArmsN rs qs)

  armsL : (ls rs : List FEnv) (σ τ : Idx) (R : Proc) (qs : List PArm) →
    ArmAns (λ S → Answerρ σ τ S (substN rs R)) (substArmsN ls qs)

  -- `pre` substitutes the result and `es` substitutes the arm index.
  -- A fork's field environment is `pre`, applied after the field the
  -- inner arm binds, which is how `openFork` substitutes.
  armsPre : (pre es ls : List FEnv) (σ τ : Idx) (L : Proc) (qs : List PArm) →
    ArmAns (λ R → Answerρ σ τ (substN ls L) (substN pre R)) (substArmsN es qs)

  armsPreL : (pre es rs : List FEnv) (σ τ : Idx) (R : Proc) (qs : List PArm) →
    ArmAns (λ S → Answerρ σ τ (substN pre S) (substN rs R)) (substArmsN es qs)

  meetN ls rs _ _ done done rewrite subNDone ls | subNDone rs = yes done-done
  meetN ls rs _ _ done stop rewrite subNDone ls | subNStop rs = no (λ ())
  meetN ls rs _ _ done (put A v P) rewrite subNDone ls | subNPut rs v P = no (λ ())
  meetN ls rs _ _ done (get A x P) rewrite subNDone ls | subNGet rs A x P = no (λ ())
  meetN ls rs _ _ done (pick0 P) rewrite subNDone ls | subNPick0 rs P = no (λ ())
  meetN ls rs _ _ done (pick1 P) rewrite subNDone ls | subNPick1 rs P = no (λ ())
  meetN ls rs _ _ done (cover P Q) rewrite subNDone ls | subNCover rs P Q = no (λ ())
  meetN ls rs _ _ done (iget x P Q) rewrite subNDone ls | subNIget rs x P Q = no (λ ())
  meetN ls rs _ _ done (mget A x ps) rewrite subNDone ls | subNMget rs A x ps = no (λ ())

  meetN ls rs _ _ stop done rewrite subNStop ls | subNDone rs = no (λ ())
  meetN ls rs _ _ stop stop rewrite subNStop ls | subNStop rs = yes stop-stop
  meetN ls rs _ _ stop (put A v P) rewrite subNStop ls | subNPut rs v P = no (λ ())
  meetN ls rs _ _ stop (get A x P) rewrite subNStop ls | subNGet rs A x P = no (λ ())
  meetN ls rs _ _ stop (pick0 P) rewrite subNStop ls | subNPick0 rs P = no (λ ())
  meetN ls rs _ _ stop (pick1 P) rewrite subNStop ls | subNPick1 rs P = no (λ ())
  meetN ls rs _ _ stop (cover P Q) rewrite subNStop ls | subNCover rs P Q = no (λ ())
  meetN ls rs _ _ stop (iget x P Q) rewrite subNStop ls | subNIget rs x P Q = no (λ ())
  meetN ls rs _ _ stop (mget A x ps) rewrite subNStop ls | subNMget rs A x ps = no (λ ())

  meetN ls rs σ τ (put A v P) (get B x Q) rewrite subNPut ls v P | subNGet rs B x Q =
    on-put-get (ty≟ (applyTy σ A) (applyTy τ B)) (sent? (substValN ls v))
      (meetN ls (shadowN x rs) σ (ext x (substValN ls v) τ) P Q)
  meetN ls rs σ τ (put A v P) (mget B x ps) rewrite subNPut ls v P | subNMget rs B x ps =
    concludePut (substArmsN (shadowN x rs) ps)
      (armsR ls (shadowN x rs) σ (ext x (substValN ls v) τ) P ps)
  meetN ls rs _ _ (put A v P) done rewrite subNPut ls v P | subNDone rs = no (λ ())
  meetN ls rs _ _ (put A v P) stop rewrite subNPut ls v P | subNStop rs = no (λ ())
  meetN ls rs _ _ (put A v P) (put B w Q) rewrite subNPut ls v P | subNPut rs w Q = no (λ ())
  meetN ls rs _ _ (put A v P) (pick0 Q) rewrite subNPut ls v P | subNPick0 rs Q = no (λ ())
  meetN ls rs _ _ (put A v P) (pick1 Q) rewrite subNPut ls v P | subNPick1 rs Q = no (λ ())
  meetN ls rs _ _ (put A v P) (cover Q R) rewrite subNPut ls v P | subNCover rs Q R = no (λ ())
  meetN ls rs σ τ (put bit v P) (iget x Q R) rewrite subNPut ls v P | subNIget rs x Q R =
    finishPutBit (substValN ls v)
      (meetN ls (shadowN x rs) σ (ext x (lit b0) τ) P Q)
      (meetN ls (shadowN x rs) σ (ext x (lit b1) τ) P R)
  meetN ls rs _ _ (put nat v P) (iget x Q R) rewrite subNPut ls v P | subNIget rs x Q R = no (λ ())
  meetN ls rs _ _ (put unit v P) (iget x Q R) rewrite subNPut ls v P | subNIget rs x Q R = no (λ ())
  meetN ls rs _ _ (put (pair A B) v P) (iget x Q R) rewrite subNPut ls v P | subNIget rs x Q R = no (λ ())
  meetN ls rs _ _ (put (rec fs) v P) (iget x Q R) rewrite subNPut ls v P | subNIget rs x Q R = no (λ ())
  meetN ls rs _ _ (put (vec A e) v P) (iget x Q R) rewrite subNPut ls v P | subNIget rs x Q R = no (λ ())
  meetN ls rs _ _ (put (dat d as) v P) (iget x Q R) rewrite subNPut ls v P | subNIget rs x Q R = no (λ ())

  meetN ls rs σ τ (get A x P) (put B v Q) rewrite subNGet ls A x P | subNPut rs v Q =
    on-get-put (ty≟ (applyTy σ A) (applyTy τ B)) (sent? (substValN rs v))
      (meetN (shadowN x ls) rs (ext x (substValN rs v) σ) τ P Q)
  meetN ls rs _ _ (get A x P) done rewrite subNGet ls A x P | subNDone rs = no (λ ())
  meetN ls rs _ _ (get A x P) stop rewrite subNGet ls A x P | subNStop rs = no (λ ())
  meetN ls rs _ _ (get A x P) (get B y Q) rewrite subNGet ls A x P | subNGet rs B y Q = no (λ ())
  meetN ls rs _ _ (get A x P) (pick0 Q) rewrite subNGet ls A x P | subNPick0 rs Q = no (λ ())
  meetN ls rs _ _ (get A x P) (pick1 Q) rewrite subNGet ls A x P | subNPick1 rs Q = no (λ ())
  meetN ls rs _ _ (get A x P) (cover Q R) rewrite subNGet ls A x P | subNCover rs Q R = no (λ ())
  meetN ls rs _ _ (get A x P) (iget y Q R) rewrite subNGet ls A x P | subNIget rs y Q R = no (λ ())
  meetN ls rs _ _ (get A x P) (mget B y ps) rewrite subNGet ls A x P | subNMget rs B y ps = no (λ ())

  meetN ls rs σ τ (pick0 P) (cover Q R) rewrite subNPick0 ls P | subNCover rs Q R =
    pick0-yes (meetN ls rs σ τ P Q)
  meetN ls rs _ _ (pick0 P) done rewrite subNPick0 ls P | subNDone rs = no (λ ())
  meetN ls rs _ _ (pick0 P) stop rewrite subNPick0 ls P | subNStop rs = no (λ ())
  meetN ls rs _ _ (pick0 P) (put A v Q) rewrite subNPick0 ls P | subNPut rs v Q = no (λ ())
  meetN ls rs _ _ (pick0 P) (get A x Q) rewrite subNPick0 ls P | subNGet rs A x Q = no (λ ())
  meetN ls rs _ _ (pick0 P) (pick0 Q) rewrite subNPick0 ls P | subNPick0 rs Q = no (λ ())
  meetN ls rs _ _ (pick0 P) (pick1 Q) rewrite subNPick0 ls P | subNPick1 rs Q = no (λ ())
  meetN ls rs _ _ (pick0 P) (iget x Q R) rewrite subNPick0 ls P | subNIget rs x Q R = no (λ ())
  meetN ls rs _ _ (pick0 P) (mget A x ps) rewrite subNPick0 ls P | subNMget rs A x ps = no (λ ())

  meetN ls rs σ τ (pick1 P) (cover Q R) rewrite subNPick1 ls P | subNCover rs Q R =
    pick1-yes (meetN ls rs σ τ P R)
  meetN ls rs _ _ (pick1 P) done rewrite subNPick1 ls P | subNDone rs = no (λ ())
  meetN ls rs _ _ (pick1 P) stop rewrite subNPick1 ls P | subNStop rs = no (λ ())
  meetN ls rs _ _ (pick1 P) (put A v Q) rewrite subNPick1 ls P | subNPut rs v Q = no (λ ())
  meetN ls rs _ _ (pick1 P) (get A x Q) rewrite subNPick1 ls P | subNGet rs A x Q = no (λ ())
  meetN ls rs _ _ (pick1 P) (pick0 Q) rewrite subNPick1 ls P | subNPick0 rs Q = no (λ ())
  meetN ls rs _ _ (pick1 P) (pick1 Q) rewrite subNPick1 ls P | subNPick1 rs Q = no (λ ())
  meetN ls rs _ _ (pick1 P) (iget x Q R) rewrite subNPick1 ls P | subNIget rs x Q R = no (λ ())
  meetN ls rs _ _ (pick1 P) (mget A x ps) rewrite subNPick1 ls P | subNMget rs A x ps = no (λ ())

  meetN ls rs σ τ (cover P Q) (pick0 R) rewrite subNCover ls P Q | subNPick0 rs R =
    cover0-yes (meetN ls rs σ τ P R)
  meetN ls rs σ τ (cover P Q) (pick1 R) rewrite subNCover ls P Q | subNPick1 rs R =
    cover1-yes (meetN ls rs σ τ Q R)
  meetN ls rs _ _ (cover P Q) done rewrite subNCover ls P Q | subNDone rs = no (λ ())
  meetN ls rs _ _ (cover P Q) stop rewrite subNCover ls P Q | subNStop rs = no (λ ())
  meetN ls rs _ _ (cover P Q) (put A v R) rewrite subNCover ls P Q | subNPut rs v R = no (λ ())
  meetN ls rs _ _ (cover P Q) (get A x R) rewrite subNCover ls P Q | subNGet rs A x R = no (λ ())
  meetN ls rs _ _ (cover P Q) (cover R S) rewrite subNCover ls P Q | subNCover rs R S = no (λ ())
  meetN ls rs _ _ (cover P Q) (iget x R S) rewrite subNCover ls P Q | subNIget rs x R S = no (λ ())
  meetN ls rs _ _ (cover P Q) (mget A x ps) rewrite subNCover ls P Q | subNMget rs A x ps = no (λ ())

  meetN ls rs σ τ (iget x P Q) (put bit v R) rewrite subNIget ls x P Q | subNPut rs v R =
    finishIgetBit (substValN rs v)
      (meetN (shadowN x ls) rs (ext x (lit b0) σ) τ P R)
      (meetN (shadowN x ls) rs (ext x (lit b1) σ) τ Q R)
  meetN ls rs _ _ (iget x P Q) (put nat v R) rewrite subNIget ls x P Q | subNPut rs v R = no (λ ())
  meetN ls rs _ _ (iget x P Q) (put unit v R) rewrite subNIget ls x P Q | subNPut rs v R = no (λ ())
  meetN ls rs _ _ (iget x P Q) (put (pair A B) v R) rewrite subNIget ls x P Q | subNPut rs v R = no (λ ())
  meetN ls rs _ _ (iget x P Q) (put (rec fs) v R) rewrite subNIget ls x P Q | subNPut rs v R = no (λ ())
  meetN ls rs _ _ (iget x P Q) (put (vec A e) v R) rewrite subNIget ls x P Q | subNPut rs v R = no (λ ())
  meetN ls rs _ _ (iget x P Q) (put (dat d as) v R) rewrite subNIget ls x P Q | subNPut rs v R = no (λ ())
  meetN ls rs _ _ (iget x P Q) done rewrite subNIget ls x P Q | subNDone rs = no (λ ())
  meetN ls rs _ _ (iget x P Q) stop rewrite subNIget ls x P Q | subNStop rs = no (λ ())
  meetN ls rs _ _ (iget x P Q) (get A y R) rewrite subNIget ls x P Q | subNGet rs A y R = no (λ ())
  meetN ls rs _ _ (iget x P Q) (pick0 R) rewrite subNIget ls x P Q | subNPick0 rs R = no (λ ())
  meetN ls rs _ _ (iget x P Q) (pick1 R) rewrite subNIget ls x P Q | subNPick1 rs R = no (λ ())
  meetN ls rs _ _ (iget x P Q) (cover R S) rewrite subNIget ls x P Q | subNCover rs R S = no (λ ())
  meetN ls rs _ _ (iget x P Q) (iget y R S) rewrite subNIget ls x P Q | subNIget rs y R S = no (λ ())
  meetN ls rs _ _ (iget x P Q) (mget A y ps) rewrite subNIget ls x P Q | subNMget rs A y ps = no (λ ())

  meetN ls rs σ τ (mget A x ps) (put B v P) rewrite subNMget ls A x ps | subNPut rs v P =
    concludeMget (substArmsN (shadowN x ls) ps)
      (armsL (shadowN x ls) rs (ext x (substValN rs v) σ) τ P ps)
  meetN ls rs _ _ (mget A x ps) done rewrite subNMget ls A x ps | subNDone rs = no (λ ())
  meetN ls rs _ _ (mget A x ps) stop rewrite subNMget ls A x ps | subNStop rs = no (λ ())
  meetN ls rs _ _ (mget A x ps) (get B y Q) rewrite subNMget ls A x ps | subNGet rs B y Q = no (λ ())
  meetN ls rs _ _ (mget A x ps) (pick0 Q) rewrite subNMget ls A x ps | subNPick0 rs Q = no (λ ())
  meetN ls rs _ _ (mget A x ps) (pick1 Q) rewrite subNMget ls A x ps | subNPick1 rs Q = no (λ ())
  meetN ls rs _ _ (mget A x ps) (cover Q R) rewrite subNMget ls A x ps | subNCover rs Q R = no (λ ())
  meetN ls rs _ _ (mget A x ps) (iget y Q R) rewrite subNMget ls A x ps | subNIget rs y Q R = no (λ ())
  meetN ls rs _ _ (mget A x ps) (mget B y qs) rewrite subNMget ls A x ps | subNMget rs B y qs = no (λ ())

  armsR _ _ _ _ _ [] = aa-nil
  armsR ls rs σ τ L (bare p ∷ qs) =
    aa-bare (meetN ls rs σ τ L p) (armsR ls rs σ τ L qs)
  armsR ls rs σ τ L (named _ xs p ∷ qs) =
    aa-named (λ e → meetN ls (e ∷ shadowAll xs rs) σ τ L p)
             (armsR ls rs σ τ L qs)
  armsR ls rs σ τ L (prod pat p ∷ qs) =
    aa-prod (λ e → meetN ls (e ∷ shadowAll (patBinders pat) rs) σ τ L p)
            (armsR ls rs σ τ L qs)
  armsR ls rs σ τ L (fork _ xs _ qs ∷ ps) =
    aa-fork (λ e → armsPre (e ∷ []) (shadowAll xs rs) ls σ τ L qs)
            (armsR ls rs σ τ L ps)

  armsPre _ _ _ _ _ _ [] = aa-nil
  armsPre pre es ls σ τ L (bare p ∷ qs) =
    aa-bare (shiftPre σ τ ls L pre es p (meetN ls (pre ++ es) σ τ L p))
            (armsPre pre es ls σ τ L qs)
  armsPre pre es ls σ τ L (named _ xs p ∷ qs) =
    aa-named (λ e' →
      shiftPre σ τ ls L pre (e' ∷ shadowAll xs es) p
               (meetN ls (pre ++ (e' ∷ shadowAll xs es)) σ τ L p))
             (armsPre pre es ls σ τ L qs)
  armsPre pre es ls σ τ L (prod pat p ∷ qs) =
    aa-prod (λ e' →
      shiftPre σ τ ls L pre (e' ∷ shadowAll (patBinders pat) es) p
               (meetN ls (pre ++ (e' ∷ shadowAll (patBinders pat) es)) σ τ L p))
            (armsPre pre es ls σ τ L qs)
  armsPre pre es ls σ τ L (fork _ xs _ inner ∷ ps) =
    aa-fork (λ e' →
      retarget (λ {R} m → shiftPre σ τ ls L pre (e' ∷ []) R m)
               (armsPre (pre ++ (e' ∷ [])) (shadowAll xs es) ls σ τ L inner))
            (armsPre pre es ls σ τ L ps)

  armsL _ _ _ _ _ [] = aa-nil
  armsL ls rs σ τ R (bare p ∷ qs) =
    aa-bare (meetN ls rs σ τ p R) (armsL ls rs σ τ R qs)
  armsL ls rs σ τ R (named _ xs p ∷ qs) =
    aa-named (λ e → meetN (e ∷ shadowAll xs ls) rs σ τ p R)
             (armsL ls rs σ τ R qs)
  armsL ls rs σ τ R (prod pat p ∷ qs) =
    aa-prod (λ e → meetN (e ∷ shadowAll (patBinders pat) ls) rs σ τ p R)
            (armsL ls rs σ τ R qs)
  armsL ls rs σ τ R (fork _ xs _ qs ∷ ps) =
    aa-fork (λ e → armsPreL (e ∷ []) (shadowAll xs ls) rs σ τ R qs)
            (armsL ls rs σ τ R ps)

  armsPreL _ _ _ _ _ _ [] = aa-nil
  armsPreL pre es rs σ τ R (bare p ∷ qs) =
    aa-bare (shiftPreL σ τ rs R pre es p (meetN (pre ++ es) rs σ τ p R))
            (armsPreL pre es rs σ τ R qs)
  armsPreL pre es rs σ τ R (named _ xs p ∷ qs) =
    aa-named (λ e' →
      shiftPreL σ τ rs R pre (e' ∷ shadowAll xs es) p
                (meetN (pre ++ (e' ∷ shadowAll xs es)) rs σ τ p R))
             (armsPreL pre es rs σ τ R qs)
  armsPreL pre es rs σ τ R (prod pat p ∷ qs) =
    aa-prod (λ e' →
      shiftPreL σ τ rs R pre (e' ∷ shadowAll (patBinders pat) es) p
                (meetN (pre ++ (e' ∷ shadowAll (patBinders pat) es)) rs σ τ p R))
            (armsPreL pre es rs σ τ R qs)
  armsPreL pre es rs σ τ R (fork _ xs _ inner ∷ ps) =
    aa-fork (λ e' →
      retarget (λ {S} m → shiftPreL σ τ rs R pre (e' ∷ []) S m)
               (armsPreL (pre ++ (e' ∷ [])) (shadowAll xs es) rs σ τ R inner))
            (armsPreL pre es rs σ τ R ps)

decideρ : (σ τ : Idx) (P Q : Proc) → Answerρ σ τ P Q
decideρ σ τ P Q = meetN [] [] σ τ P Q

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
maybeSplit = mget maybeBool "m" (bare stop ∷ bare done ∷ [])

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

not-short : ¬ Meets (put bit (lit b0) done) (mget bit "b" (bare done ∷ []))
not-short (put-mget _ _ () _)

not-var-arm : ¬ Meets (put bit (var "b") done) (mget bit "b" (bare done ∷ bare done ∷ []))
not-var-arm (put-mget _ _ () _)

not-nat-arm : ¬ Meets (put nat (lit zero) done) (mget nat "n" (bare done ∷ bare done ∷ []))
not-nat-arm (put-mget _ _ () _)

not-bad-arm : ¬ Meets (put boolTy badCall done) (mget boolTy "b" (bare done ∷ bare done ∷ []))
not-bad-arm (put-mget _ () _ _)

-- The arms differ, so the selected constructor is the arm that meets.
boolSplit : Proc
boolSplit = mget boolTy "b" (bare done ∷ bare stop ∷ [])

false-split : Meets (put boolTy (lit falseV) stop) boolSplit
false-split = put-mget refl refl refl stop-stop

false-split-decides : decide (put boolTy (lit falseV) stop) boolSplit ≡ yes false-split
false-split-decides = refl

optSplit : Proc
optSplit = mget maybeNat "m" (bare stop ∷ bare done ∷ [])

nothing-split : Meets (put maybeNat (lit nothingV) stop) optSplit
nothing-split = put-mget refl refl refl stop-stop

nothing-split-decides : decide (put maybeNat (lit nothingV) stop) optSplit ≡ yes nothing-split
nothing-split-decides = refl

just-split : Meets (put maybeNat (lit just0) done) optSplit
just-split = put-mget refl refl refl done-done

just-split-decides : decide (put maybeNat (lit just0) done) optSplit ≡ yes just-split
just-split-decides = refl

------------------------------------------------------------------------
-- A named arm reads the fields of the value it received. `just true`
-- meets the arm that sends `grant true`. Forwarding the field sends
-- that `Bool`. `cons 0 []` meets the arm that sends the tail `[]`.
------------------------------------------------------------------------

fieldSender : Proc
fieldSender = put maybeBool (lit justTrue) (get boolTy "k" done)

field-meet : Meets fieldSender fieldReply
field-meet = put-mget refl refl refl (get-put refl refl done-done)

field-meet-decides : decide fieldSender fieldReply ≡ yes field-meet
field-meet-decides = refl

field-meet-swap : decide fieldReply fieldSender ≡ yes (meets-sym field-meet)
field-meet-swap = refl

fwd-meet : Meets fieldSender fwdField
fwd-meet = put-mget refl refl refl (get-put refl refl done-done)

fwd-meet-decides : decide fieldSender fwdField ≡ yes fwd-meet
fwd-meet-decides = refl

nothingSender : Proc
nothingSender = put maybeBool (lit nothingB) (get boolTy "k" done)

nothing-meet : Meets nothingSender fieldReply
nothing-meet = put-mget refl refl refl (get-put refl refl done-done)

nothing-meet-decides : decide nothingSender fieldReply ≡ yes nothing-meet
nothing-meet-decides = refl

-- `just true` follows the arm that sends `rst`. `just false` and
-- `nothing` close. Either order meets.
gate-true-meet : Meets gateTrue gateServer
gate-true-meet = put-mget refl refl refl (get-put refl refl done-done)

gate-true-decides : decide gateTrue gateServer ≡ yes gate-true-meet
gate-true-decides = refl

gate-true-swap : decide gateServer gateTrue ≡ yes (meets-sym gate-true-meet)
gate-true-swap = refl

gate-false-meet : Meets gateFalse gateServer
gate-false-meet = put-mget refl refl refl done-done

gate-false-decides : decide gateFalse gateServer ≡ yes gate-false-meet
gate-false-decides = refl

gate-false-swap : decide gateServer gateFalse ≡ yes (meets-sym gate-false-meet)
gate-false-swap = refl

gate-none-meet : Meets gateNone gateServer
gate-none-meet = put-mget refl refl refl done-done

gate-none-decides : decide gateNone gateServer ≡ yes gate-none-meet
gate-none-decides = refl

gate-none-swap : decide gateServer gateNone ≡ yes (meets-sym gate-none-meet)
gate-none-swap = refl

tailSender : Proc
tailSender = put listNat (lit consV) (get listNat "ys" done)

tail-meet : Meets tailSender tailPass
tail-meet = put-mget refl refl refl (get-put refl refl done-done)

tail-meet-decides : decide tailSender tailPass ≡ yes tail-meet
tail-meet-decides = refl

------------------------------------------------------------------------
-- A product arm reads the components of the value it received.
-- `grant a` on `true` meets the arm that sends `grant true`. The
-- record's bit is the bit that was sent. Both orders meet.
------------------------------------------------------------------------

pairSender : Proc
pairSender = put pairBoolBit (lit (tup trueV b0)) (get boolTy "k" done)

pair-meet : Meets pairSender pairGrant
pair-meet = put-mget refl refl refl (get-put refl refl done-done)

pair-meet-decides : decide pairSender pairGrant ≡ yes pair-meet
pair-meet-decides = refl

pair-meet-swap : decide pairGrant pairSender ≡ yes (meets-sym pair-meet)
pair-meet-swap = refl

natSender : Proc
natSender = put pairNatBit (lit (tup zero b1)) (get nat "k" done)

nat-meet : Meets natSender pairReply
nat-meet = put-mget refl refl refl (get-put refl refl done-done)

nat-meet-decides : decide natSender pairReply ≡ yes nat-meet
nat-meet-decides = refl

nat-meet-swap : decide pairReply natSender ≡ yes (meets-sym nat-meet)
nat-meet-swap = refl

recSender : Proc
recSender = put noteTy (lit noteVal) (get bit "k" done)

rec-meet : Meets recSender noteReply
rec-meet = put-mget refl refl refl (get-put refl refl done-done)

rec-meet-decides : decide recSender noteReply ≡ yes rec-meet
rec-meet-decides = refl

rec-meet-swap : decide noteReply recSender ≡ yes (meets-sym rec-meet)
rec-meet-swap = refl

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

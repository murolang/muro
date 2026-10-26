------------------------------------------------------------------------
-- Asynchronous meeting of two processes over bounded FIFO queues.
-- One queue in each direction. A send enqueues when its queue holds
-- fewer than k messages. A full queue is not an error: that send
-- waits. A receive dequeues the head of the opposite queue. The head
-- must be the type, label, or arm the receiver names. Both ends
-- finish only with both queues empty. Until then some step remains
-- possible.
--
-- The bound k = 0 blocks every send. It is not the synchronous
-- meeting. The synchronous meeting stays the rendezvous in
-- `Muro.Meet`. This checker is the bounded transport.
--
-- A value carried in a queue selects a `mget` arm. Evidence is not
-- queued: the sender has already discharged it, and the message is
-- the payload. The queued value is resolved, so an echo selects the
-- arm of the value that was received. The length index is the
-- expression the sender wrote, which is the expression the
-- synchronous meeting instantiates.
--
-- Finite processes shrink at every step. The search recurses on that
-- size. Zero is the empty process, not a fuel bound: a step from a
-- process of size zero cannot exist. Recursive processes are
-- `Muro.AsyncRec`.
--
-- Nothing here is added to Tm.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Async where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_+_; _≤_; _<_; z≤n; s≤s)
  renaming (ℕ to ℕ; zero to nzero; suc to nsuc)
open import Data.Nat.Properties using (≤-pred; ≤-trans; ≤-refl; m≤m+n; m≤n+m; _<?_)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using (_≟_; _==_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Decidable.Core using (Dec)
  renaming (yes to yes′; no to no′)

open import Muro.Session hiding (yes; no; pong)
open import Muro.Meet using (ext)

------------------------------------------------------------------------
-- Size. `done` and `stop` are zero. Every other constructor adds one,
-- plus the size of the arms it still holds.
------------------------------------------------------------------------

size : Proc → ℕ
sizeArms : List Proc → ℕ

size done = nzero
size stop = nzero
size (put _ _ P) = nsuc (size P)
size (get _ _ P) = nsuc (size P)
size (pick0 P) = nsuc (size P)
size (pick1 P) = nsuc (size P)
size (cover P Q) = nsuc (size P + size Q)
size (iget _ P Q) = nsuc (size P + size Q)
size (mget _ _ ps) = nsuc (sizeArms ps)

sizeArms [] = nzero
sizeArms (P ∷ ps) = size P + sizeArms ps

ltSucL : (n : ℕ) (Q : Proc) → n + size Q < nsuc n + size Q
ltSucL n Q = s≤s ≤-refl

shrinkPut : ∀ m n → m + n < m + nsuc n
shrinkPut nzero n = s≤s ≤-refl
shrinkPut (nsuc m) n = s≤s (shrinkPut m n)

ltSucR : (P : Proc) (n : ℕ) → size P + n < size P + nsuc n
ltSucR P n = shrinkPut (size P) n

leAddR : ∀ a b c → a ≤ b → a + c ≤ b + c
leAddR nzero b c z≤n = m≤n+m c b
leAddR (nsuc a) (nsuc b) c (s≤s le) = s≤s (leAddR a b c le)
leAddR (nsuc _) nzero _ ()

ltCoverL : (P Q R : Proc) → size P + size R < nsuc (size P + size Q) + size R
ltCoverL P Q R =
  s≤s (leAddR (size P) (size P + size Q) (size R) (m≤m+n (size P) (size Q)))

ltCoverR : (P Q R : Proc) → size Q + size R < nsuc (size P + size Q) + size R
ltCoverR P Q R =
  s≤s (leAddR (size Q) (size P + size Q) (size R) (m≤n+m (size Q) (size P)))

ltArmL : (R : Proc) (ps : List Proc) (Q : Proc) → size R ≤ sizeArms ps →
         size R + size Q < nsuc (sizeArms ps) + size Q
ltArmL R ps Q le = s≤s (leAddR (size R) (sizeArms ps) (size Q) le)

shrinkArm : ∀ m r arms → r ≤ arms → m + r < m + nsuc arms
shrinkArm nzero r arms le = s≤s le
shrinkArm (nsuc m) r arms le = s≤s (shrinkArm m r arms le)

ltArmR : (P R : Proc) (ps : List Proc) → size R ≤ sizeArms ps →
         size P + size R < size P + nsuc (sizeArms ps)
ltArmR P R ps le = shrinkArm (size P) (size R) (sizeArms ps) le

b1≤ : (P Q : Proc) → size Q ≤ sizeArms (P ∷ Q ∷ [])
b1≤ P Q =
  ≤-trans (m≤m+n (size Q) nzero) (m≤n+m (size Q + nzero) (size P))

------------------------------------------------------------------------
-- The arm a concrete value selects, together with the size bound the
-- search needs. A variable selects nothing. A call selects the arm of
-- the value it returns.
------------------------------------------------------------------------

findIn : String → List Ctor → (ps : List Proc) →
         Maybe (Σ Proc (λ R → size R ≤ sizeArms ps))
findIn _ [] _ = nothing
findIn _ (_ ∷ _) [] = nothing
findIn name (ctor n _ ∷ cs) (P ∷ ps) with name == n
... | true = just (P , m≤m+n (size P) (sizeArms ps))
... | false = lift (findIn name cs ps)
  where
  lift : Maybe (Σ Proc (λ R → size R ≤ sizeArms ps)) →
         Maybe (Σ Proc (λ R → size R ≤ size P + sizeArms ps))
  lift nothing = nothing
  lift (just (R , le)) = just (R , ≤-trans le (m≤n+m (sizeArms ps) (size P)))

armPick : (A : Ty) → Val A → (ps : List Proc) →
          Maybe (Σ Proc (λ R → size R ≤ sizeArms ps))
armPick bit b0 (P ∷ Q ∷ []) = just (P , m≤m+n (size P) (sizeArms (Q ∷ [])))
armPick bit b1 (P ∷ Q ∷ []) = just (Q , b1≤ P Q)
armPick (dat d _) (con c _) ps = findIn c (ctorsOf d) ps
armPick _ _ _ = nothing

armExprPick : ∀ {A} → ValExpr A → (ps : List Proc) →
              Maybe (Σ Proc (λ R → size R ≤ sizeArms ps))
armExprPick v ps with known v
... | nothing = nothing
... | just u = armPick _ u ps

------------------------------------------------------------------------
-- Messages. `pay` is a payload. The type is the wire type at the
-- send. The carrier is the value, evidence already dropped. `lab` is
-- a choice: false is `pick0`, true is `pick1`.
------------------------------------------------------------------------

-- `orig` instantiates lengths. `ready` is that value after the
-- sender's names are resolved, and it is what an arm or a bit matches.
data Carrier : Set where
  car : (A : Ty) → ValExpr A → ValExpr A → Carrier

data Msg : Set where
  pay : Ty → Carrier → Msg
  lab : Bool → Msg

data Entry : Set where
  evar : (A : Ty) → ValExpr A → Entry

VEnv : Set
VEnv = List (String × Entry)

lookupVEnv : String → VEnv → Maybe Entry
lookupVEnv x [] = nothing
lookupVEnv x ((y , e) ∷ es) with x ≟ y
... | yes′ _ = just e
... | no′ _ = lookupVEnv x es

pickEntry : ∀ {A} → Entry → Maybe (ValExpr A)
pickEntry {A} (evar B v) with ty≟ A B
... | yes′ eq = just (subst ValExpr (sym eq) v)
... | no′ _ = nothing

resolveV : ∀ {A} → VEnv → ValExpr A → ValExpr A
resolveV _ (lit v) = lit v
resolveV _ (call f as) = call f as
resolveV e (var x) with lookupVEnv x e
... | nothing = var x
... | just en with pickEntry en
... | nothing = var x
... | just v = v

normV : ∀ {A} → ValExpr A → ValExpr A
normV (lit v) = lit v
normV (var x) = var x
normV (call f as) with known (call f as)
... | just u = lit u
... | nothing = call f as

prepare : ∀ {A} → VEnv → ValExpr A → ValExpr A
prepare e v = normV (resolveV e v)

extCar : String → Carrier → Idx → Idx
extCar x (car A orig _) ρ = ext {A} x orig ρ

bindV : String → Carrier → VEnv → VEnv
bindV x (car A _ ready) e = (x , evar A ready) ∷ e

asBit : Carrier → Maybe (Val bit)
asBit (car bit _ (lit b)) = just b
asBit (car bit _ (var _)) = nothing
asBit (car bit _ (call f as)) with known (call f as)
... | just b = just b
... | nothing = nothing
asBit (car nat _ _) = nothing
asBit (car unit _ _) = nothing
asBit (car (pair _ _) _ _) = nothing
asBit (car (rec _) _ _) = nothing
asBit (car (vec _ _) _ _) = nothing
asBit (car (dat _ _) _ _) = nothing

------------------------------------------------------------------------
-- A configuration. `l2r` is what the left process has sent and the
-- right has not yet taken. `cap` is the bound on each queue.
------------------------------------------------------------------------

record Conf : Set where
  constructor mk
  field
    cap : ℕ
    lp rp : Proc
    l2r r2l : List Msg
    lv rv : VEnv
    σ τ : Idx

open Conf

measure : Conf → ℕ
measure c = size (lp c) + size (rp c)

snoc : List Msg → Msg → List Msg
snoc [] m = m ∷ []
snoc (x ∷ xs) m = x ∷ snoc xs m

mkPayL : (c : Conf) {A : Ty} → ValExpr A → Msg
mkPayL c {A} v = pay (applyTy (σ c) A) (car A v (prepare (lv c) v))

mkPayR : (c : Conf) {A : Ty} → ValExpr A → Msg
mkPayR c {A} v = pay (applyTy (τ c) A) (car A v (prepare (rv c) v))

data Side : Set where
  sideL sideR : Side

------------------------------------------------------------------------
-- One side's action. `does` is a real step, and the process size has
-- dropped. `waits` is a send into a full queue, a receive from an
-- empty queue, or a value that was not discharged. `bads` is a head
-- the receiver cannot take.
------------------------------------------------------------------------

data Act (c : Conf) : Set where
  does : (c' : Conf) → measure c' < measure c → Act c
  waits : Act c
  bads : Msg → Act c

data TakePay : Set where
  tbad : TakePay
  tpay : Carrier → TakePay

takePay : Idx → Ty → Msg → TakePay
takePay _ _ (lab _) = tbad
takePay ρ A (pay w ca) with ty≟ (applyTy ρ A) w
... | yes′ _ = tpay ca
... | no′ _ = tbad

data TakeLab : Set where
  lbad l0 l1 : TakeLab

takeLab : Msg → TakeLab
takeLab (lab false) = l0
takeLab (lab true) = l1
takeLab (pay _ _) = lbad

data TakeBit : Set where
  bbad : TakeBit
  bb0 bb1 : Carrier → TakeBit

takeBit : Msg → TakeBit
takeBit (lab _) = bbad
takeBit (pay w ca) with ty≟ w bit
... | no′ _ = bbad
... | yes′ refl with asBit ca
... | just b0 = bb0 ca
... | just b1 = bb1 ca
... | nothing = bbad

data TakeArm (ps : List Proc) : Set where
  abad : TakeArm ps
  aarm : (R : Proc) → Carrier → size R ≤ sizeArms ps → TakeArm ps

armOfCar : Carrier → (ps : List Proc) → Maybe (Σ Proc (λ R → size R ≤ sizeArms ps))
armOfCar (car _ _ ready) ps = armExprPick ready ps

takeArm : Idx → Ty → (ps : List Proc) → Msg → TakeArm ps
takeArm _ _ _ (lab _) = abad
takeArm ρ A ps (pay w ca) with ty≟ (applyTy ρ A) w
... | no′ _ = abad
... | yes′ _ with armOfCar ca ps
... | nothing = abad
... | just (R , le) = aarm R ca le

sendPutL : (c : Conf) {A : Ty} (v : ValExpr A) (P : Proc) →
           lp c ≡ put A v P → Act c
sendPutL c v P eq with length (l2r c) <? cap c
... | no′ _ = waits
... | yes′ _ with sent? v
... | no′ _ = waits
... | yes′ _ = does (record c { lp = P ; l2r = snoc (l2r c) (mkPayL c v) }) (drop eq)
  where
  drop : lp c ≡ put _ v P → size P + size (rp c) < measure c
  drop refl = ltSucL (size P) (rp c)

sendPutR : (c : Conf) {A : Ty} (v : ValExpr A) (P : Proc) →
           rp c ≡ put A v P → Act c
sendPutR c v P eq with length (r2l c) <? cap c
... | no′ _ = waits
... | yes′ _ with sent? v
... | no′ _ = waits
... | yes′ _ = does (record c { rp = P ; r2l = snoc (r2l c) (mkPayR c v) }) (drop eq)
  where
  drop : rp c ≡ put _ v P → size (lp c) + size P < measure c
  drop refl = ltSucR (lp c) (size P)

sendLabL : (c : Conf) (b : Bool) (P : Proc) →
           (lp c ≡ pick0 P) ⊎ (lp c ≡ pick1 P) → Act c
sendLabL c b P eq with length (l2r c) <? cap c
... | no′ _ = waits
... | yes′ _ = does (record c { lp = P ; l2r = snoc (l2r c) (lab b) }) (drop eq)
  where
  drop : (lp c ≡ pick0 P) ⊎ (lp c ≡ pick1 P) → size P + size (rp c) < measure c
  drop (inj₁ refl) = ltSucL (size P) (rp c)
  drop (inj₂ refl) = ltSucL (size P) (rp c)

sendLabR : (c : Conf) (b : Bool) (P : Proc) →
           (rp c ≡ pick0 P) ⊎ (rp c ≡ pick1 P) → Act c
sendLabR c b P eq with length (r2l c) <? cap c
... | no′ _ = waits
... | yes′ _ = does (record c { rp = P ; r2l = snoc (r2l c) (lab b) }) (drop eq)
  where
  drop : (rp c ≡ pick0 P) ⊎ (rp c ≡ pick1 P) → size (lp c) + size P < measure c
  drop (inj₁ refl) = ltSucR (lp c) (size P)
  drop (inj₂ refl) = ltSucR (lp c) (size P)

recvGetL : (c : Conf) (A : Ty) (x : String) (P : Proc) →
           lp c ≡ get A x P → Act c
recvGetL c A x P eq with r2l c
... | [] = waits
... | m ∷ rest with takePay (σ c) A m
... | tbad = bads m
... | tpay ca =
  does (record c { lp = P ; r2l = rest ; lv = bindV x ca (lv c) ; σ = extCar x ca (σ c) })
       (drop eq)
  where
  drop : lp c ≡ get A x P → size P + size (rp c) < measure c
  drop refl = ltSucL (size P) (rp c)

recvGetR : (c : Conf) (A : Ty) (x : String) (P : Proc) →
           rp c ≡ get A x P → Act c
recvGetR c A x P eq with l2r c
... | [] = waits
... | m ∷ rest with takePay (τ c) A m
... | tbad = bads m
... | tpay ca =
  does (record c { rp = P ; l2r = rest ; rv = bindV x ca (rv c) ; τ = extCar x ca (τ c) })
       (drop eq)
  where
  drop : rp c ≡ get A x P → size (lp c) + size P < measure c
  drop refl = ltSucR (lp c) (size P)

covL0 : (c : Conf) (P Q : Proc) → lp c ≡ cover P Q → size P + size (rp c) < measure c
covL0 c P Q refl = ltCoverL P Q (rp c)

covL1 : (c : Conf) (P Q : Proc) → lp c ≡ cover P Q → size Q + size (rp c) < measure c
covL1 c P Q refl = ltCoverR P Q (rp c)

covR0 : (c : Conf) (P Q : Proc) → rp c ≡ cover P Q → size (lp c) + size P < measure c
covR0 c P Q refl =
  shrinkArm (size (lp c)) (size P) (size P + size Q) (m≤m+n (size P) (size Q))

covR1 : (c : Conf) (P Q : Proc) → rp c ≡ cover P Q → size (lp c) + size Q < measure c
covR1 c P Q refl =
  shrinkArm (size (lp c)) (size Q) (size P + size Q) (m≤n+m (size Q) (size P))

igL0 : (c : Conf) (x : String) (P Q : Proc) → lp c ≡ iget x P Q →
       size P + size (rp c) < measure c
igL0 c x P Q refl = ltCoverL P Q (rp c)

igL1 : (c : Conf) (x : String) (P Q : Proc) → lp c ≡ iget x P Q →
       size Q + size (rp c) < measure c
igL1 c x P Q refl = ltCoverR P Q (rp c)

igR0 : (c : Conf) (x : String) (P Q : Proc) → rp c ≡ iget x P Q →
       size (lp c) + size P < measure c
igR0 c x P Q refl =
  shrinkArm (size (lp c)) (size P) (size P + size Q) (m≤m+n (size P) (size Q))

igR1 : (c : Conf) (x : String) (P Q : Proc) → rp c ≡ iget x P Q →
       size (lp c) + size Q < measure c
igR1 c x P Q refl =
  shrinkArm (size (lp c)) (size Q) (size P + size Q) (m≤n+m (size Q) (size P))

recvCoverL : (c : Conf) (P Q : Proc) → lp c ≡ cover P Q → Act c
recvCoverL c P Q eq with r2l c
... | [] = waits
... | m ∷ rest with takeLab m
... | lbad = bads m
... | l0 = does (record c { lp = P ; r2l = rest }) (covL0 c P Q eq)
... | l1 = does (record c { lp = Q ; r2l = rest }) (covL1 c P Q eq)

recvCoverR : (c : Conf) (P Q : Proc) → rp c ≡ cover P Q → Act c
recvCoverR c P Q eq with l2r c
... | [] = waits
... | m ∷ rest with takeLab m
... | lbad = bads m
... | l0 = does (record c { rp = P ; l2r = rest }) (covR0 c P Q eq)
... | l1 = does (record c { rp = Q ; l2r = rest }) (covR1 c P Q eq)

recvIgetL : (c : Conf) (x : String) (P Q : Proc) → lp c ≡ iget x P Q → Act c
recvIgetL c x P Q eq with r2l c
... | [] = waits
... | m ∷ rest with takeBit m
... | bbad = bads m
... | bb0 ca =
  does (record c { lp = P ; r2l = rest ; lv = bindV x ca (lv c) ; σ = extCar x ca (σ c) })
       (igL0 c x P Q eq)
... | bb1 ca =
  does (record c { lp = Q ; r2l = rest ; lv = bindV x ca (lv c) ; σ = extCar x ca (σ c) })
       (igL1 c x P Q eq)

recvIgetR : (c : Conf) (x : String) (P Q : Proc) → rp c ≡ iget x P Q → Act c
recvIgetR c x P Q eq with l2r c
... | [] = waits
... | m ∷ rest with takeBit m
... | bbad = bads m
... | bb0 ca =
  does (record c { rp = P ; l2r = rest ; rv = bindV x ca (rv c) ; τ = extCar x ca (τ c) })
       (igR0 c x P Q eq)
... | bb1 ca =
  does (record c { rp = Q ; l2r = rest ; rv = bindV x ca (rv c) ; τ = extCar x ca (τ c) })
       (igR1 c x P Q eq)

recvMgetL : (c : Conf) (A : Ty) (x : String) (ps : List Proc) →
            lp c ≡ mget A x ps → Act c
recvMgetL c A x ps eq with r2l c
... | [] = waits
... | m ∷ rest with takeArm (σ c) A ps m
... | abad = bads m
... | aarm R ca le =
  does (record c { lp = R ; r2l = rest ; lv = bindV x ca (lv c) ; σ = extCar x ca (σ c) })
       (drop eq le)
  where
  drop : lp c ≡ mget A x ps → size R ≤ sizeArms ps → size R + size (rp c) < measure c
  drop refl le = ltArmL R ps (rp c) le

recvMgetR : (c : Conf) (A : Ty) (x : String) (ps : List Proc) →
            rp c ≡ mget A x ps → Act c
recvMgetR c A x ps eq with l2r c
... | [] = waits
... | m ∷ rest with takeArm (τ c) A ps m
... | abad = bads m
... | aarm R ca le =
  does (record c { rp = R ; l2r = rest ; rv = bindV x ca (rv c) ; τ = extCar x ca (τ c) })
       (drop eq le)
  where
  drop : rp c ≡ mget A x ps → size R ≤ sizeArms ps → size (lp c) + size R < measure c
  drop refl le = ltArmR (lp c) R ps le

reactL : (c : Conf) → Act c
reactL c = onL (lp c) refl
  where
  onL : (P : Proc) → lp c ≡ P → Act c
  onL done _ = waits
  onL stop _ = waits
  onL (put _ v P) eq = sendPutL c v P eq
  onL (get A x P) eq = recvGetL c A x P eq
  onL (pick0 P) eq = sendLabL c false P (inj₁ eq)
  onL (pick1 P) eq = sendLabL c true P (inj₂ eq)
  onL (cover P Q) eq = recvCoverL c P Q eq
  onL (iget x P Q) eq = recvIgetL c x P Q eq
  onL (mget A x ps) eq = recvMgetL c A x ps eq

reactR : (c : Conf) → Act c
reactR c = onR (rp c) refl
  where
  onR : (P : Proc) → rp c ≡ P → Act c
  onR done _ = waits
  onR stop _ = waits
  onR (put _ v P) eq = sendPutR c v P eq
  onR (get A x P) eq = recvGetR c A x P eq
  onR (pick0 P) eq = sendLabR c false P (inj₁ eq)
  onR (pick1 P) eq = sendLabR c true P (inj₂ eq)
  onR (cover P Q) eq = recvCoverR c P Q eq
  onR (iget x P Q) eq = recvIgetR c x P Q eq
  onR (mget A x ps) eq = recvMgetR c A x ps eq

------------------------------------------------------------------------
-- Classification. A reception on either side wins, the left one
-- first. Otherwise the left step is explored before the right step.
-- Both halted and both queues empty is success, including `done`
-- against `stop`. Both halted with a message left is an orphan.
-- Anything else that cannot step is a deadlock.
------------------------------------------------------------------------

halt : Proc → Bool
halt done = true
halt stop = true
halt (put _ _ _) = false
halt (get _ _ _) = false
halt (pick0 _) = false
halt (pick1 _) = false
halt (cover _ _) = false
halt (iget _ _ _) = false
halt (mget _ _ _) = false

halt? : (P : Proc) → Maybe (halt P ≡ true)
halt? done = just refl
halt? stop = just refl
halt? (put _ _ _) = nothing
halt? (get _ _ _) = nothing
halt? (pick0 _) = nothing
halt? (pick1 _) = nothing
halt? (cover _ _) = nothing
halt? (iget _ _ _) = nothing
halt? (mget _ _ _) = nothing

data Class (c : Conf) : Set where
  isFinal : (a : l2r c ≡ []) (b : r2l c ≡ [])
          (d : halt (lp c) ≡ true) (e : halt (rp c) ≡ true) → Class c
  isOrphan : Class c
  isDead : Class c
  isRecv : Msg → Side → Class c
  isGo : (c0 : Conf) → measure c0 < measure c →
         List (Σ Conf (λ d → measure d < measure c)) → Class c

idle : (c : Conf) → Class c
idle c = on (halt? (lp c)) (halt? (rp c)) (l2r c) (r2l c) refl refl
  where
  on : Maybe (halt (lp c) ≡ true) → Maybe (halt (rp c) ≡ true) →
       (lq rq : List Msg) → l2r c ≡ lq → r2l c ≡ rq → Class c
  on (just hp) (just hq) [] [] eqL eqR = isFinal eqL eqR hp hq
  on (just _) (just _) [] (_ ∷ _) _ _ = isOrphan
  on (just _) (just _) (_ ∷ _) _ _ _ = isOrphan
  on (just _) nothing _ _ _ _ = isDead
  on nothing _ _ _ _ _ = isDead

merge : ∀ {c} → Act c → Act c → Class c
merge {c} (bads m) _ = isRecv m sideL
merge (does _ _) (bads m) = isRecv m sideR
merge waits (bads m) = isRecv m sideR
merge (does c1 lt1) (does c2 lt2) = isGo c1 lt1 ((c2 , lt2) ∷ [])
merge (does c1 lt1) waits = isGo c1 lt1 []
merge waits (does c2 lt2) = isGo c2 lt2 []
merge {c} waits waits = idle c

classify : (c : Conf) → Class c
classify c = merge (reactL c) (reactR c)

Child : Conf → Set
Child c = Σ Conf (λ d → measure d < measure c)

data All {A : Set} (P : A → Set) : List A → Set where
  anil : All P []
  acons : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

-- The class is an index, so a final configuration and a step are
-- different constructors. Soundness matches on that index. `Safe`
-- is the class `classify` actually returns.
data SafeAt (c : Conf) : Class c → Set where
  s-final : (a : l2r c ≡ []) (b : r2l c ≡ [])
          (d : halt (lp c) ≡ true) (e : halt (rp c) ≡ true)
          → SafeAt c (isFinal a b d e)
  s-go : (c0 : Conf) (lt : measure c0 < measure c) (cs : List (Child c))
       → SafeAt c0 (classify c0)
       → All (λ p → SafeAt (proj₁ p) (classify (proj₁ p))) cs
       → SafeAt c (isGo c0 lt cs)

Safe : Conf → Set
Safe c = SafeAt c (classify c)

data Fault : Set where
  freception : Msg → Side → Fault
  forphan : Fault
  fdead : Fault

data Result (c : Conf) : Set where
  ok : Safe c → Result c
  bad : Fault → Result c

data Kind : Set where
  is-yes is-recv is-orphan is-dead : Kind

kind : ∀ {c} → Result c → Kind
kind (ok _) = is-yes
kind (bad (freception _ _)) = is-recv
kind (bad forphan) = is-orphan
kind (bad fdead) = is-dead

suc≤0 : ∀ {m} → nsuc m ≤ nzero → ⊥
suc≤0 ()

notBoth : ∀ {a b} → a < b → b ≤ nzero → ⊥
notBoth a<b b≤z = suc≤0 (≤-trans a<b b≤z)

boundNext : ∀ {a b n} → a < b → b ≤ nsuc n → a ≤ n
boundNext a<b b≤ = ≤-pred (≤-trans a<b b≤)

------------------------------------------------------------------------
-- The search. `n` starts at the size of the two processes. Each step
-- calls it at `n ∸ 1`, which is still an upper bound because the step
-- dropped the size. At zero a step would be a process smaller than
-- empty, which `notBoth` refuses.
------------------------------------------------------------------------

-- `deliver` matches the class as a value. The equality puts that
-- class back on `classify`, so the result is `Safe` of this
-- configuration. At zero a step is `notBoth`. The two clauses are
-- split on `n` so the bound `le` is `≤ nzero` or `≤ suc n`.
checkN : (n : ℕ) (c : Conf) → measure c ≤ n → Result c
checkN nzero c le = deliver (classify c) refl
  where
  deliver : (cl : Class c) → classify c ≡ cl → Result c
  deliver (isFinal a b d e) eq = ok (subst (SafeAt c) (sym eq) (s-final a b d e))
  deliver isOrphan _ = bad forphan
  deliver isDead _ = bad fdead
  deliver (isRecv m s) _ = bad (freception m s)
  deliver (isGo _ lt _) _ = ⊥-elim (notBoth lt le)
checkN (nsuc n′) c le = deliver (classify c) refl
  where
  deliver : (cl : Class c) → classify c ≡ cl → Result c
  deliver (isFinal a b d e) eq = ok (subst (SafeAt c) (sym eq) (s-final a b d e))
  deliver isOrphan _ = bad forphan
  deliver isDead _ = bad fdead
  deliver (isRecv m s) _ = bad (freception m s)
  deliver (isGo c0 lt cs) eq = next (checkN n′ c0 (boundNext lt le))
    where
    next : Result c0 → Result c
    next (bad f) = bad f
    next (ok s0) = sealed s0 (kids cs)
      where
      kids : (ps : List (Child c)) → Fault ⊎ All (λ p → Safe (proj₁ p)) ps
      kids [] = inj₂ anil
      kids ((d , ltd) ∷ ps) = cons (checkN n′ d (boundNext ltd le)) (kids ps)
        where
        cons : Result d → Fault ⊎ All (λ p → Safe (proj₁ p)) ps →
               Fault ⊎ All (λ p → Safe (proj₁ p)) ((d , ltd) ∷ ps)
        cons (bad f) _ = inj₁ f
        cons (ok _) (inj₁ f) = inj₁ f
        cons (ok s) (inj₂ ss) = inj₂ (acons s ss)
      sealed : Safe c0 → Fault ⊎ All (λ p → Safe (proj₁ p)) cs → Result c
      sealed _ (inj₁ f) = bad f
      sealed s0 (inj₂ ss) = ok (subst (SafeAt c) (sym eq) (s-go c0 lt cs s0 ss))

check : (c : Conf) → Result c
check c = checkN (measure c) c ≤-refl

------------------------------------------------------------------------
-- Soundness. A safe configuration is final, both queues empty, or it
-- has a step whose target is safe. Reception, orphan, and deadlock
-- are not safe. Every configuration reached by those steps is safe.
------------------------------------------------------------------------

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

-- A step is a child of the class. The index is the class itself, so
-- the same configuration cannot be both final and a step.
data StepAt (c : Conf) : Class c → Conf → Set where
  to0 : ∀ {c0 lt cs} → StepAt c (isGo c0 lt cs) c0
  toS : ∀ {c0 lt cs} {p : Child c} → p ∈ cs → StepAt c (isGo c0 lt cs) (proj₁ p)

_⟶_ : Conf → Conf → Set
c ⟶ d = StepAt c (classify c) d

data Reach (c : Conf) : Conf → Set where
  rhere : Reach c c
  rthere : ∀ {c' d} → c ⟶ c' → Reach c' d → Reach c d

look : (c : Conf) {p : Child c} (cs : List (Child c)) → p ∈ cs →
       All (λ q → Safe (proj₁ q)) cs → Safe (proj₁ p)
look c (_ ∷ _) here (acons s _) = s
look c (_ ∷ xs) (there m) (acons _ ss) = look c xs m ss

step-safeAt : ∀ {c cl d} → SafeAt c cl → StepAt c cl d → Safe d
step-safeAt (s-final _ _ _ _) ()
step-safeAt {c} {d = d} (s-go c0 lt cs s0 ss) st = take s0 ss st
  where
  take : Safe c0 → All (λ q → Safe (proj₁ q)) cs →
         StepAt c (isGo c0 lt cs) d → Safe d
  take s0 _ to0 = s0
  take _ ss (toS mem) = look c cs mem ss

step-safe : ∀ {c d} → Safe c → c ⟶ d → Safe d
step-safe s st = step-safeAt s st

reach-safe : ∀ {c d} → Safe c → Reach c d → Safe d
reach-safe s rhere = s
reach-safe s (rthere st r) = reach-safe (step-safe s st) r

-- A safe class is a finished pair of empty queues, or a step.
data LocalAt (c : Conf) (cl : Class c) : Set where
  lfin : (a : l2r c ≡ []) (b : r2l c ≡ [])
       (d : halt (lp c) ≡ true) (e : halt (rp c) ≡ true)
       → cl ≡ isFinal a b d e
       → LocalAt c cl
  lstep : (c' : Conf) → StepAt c cl c' → LocalAt c cl

localAt : ∀ {c cl} → SafeAt c cl → LocalAt c cl
localAt (s-final a b d e) = lfin a b d e refl
localAt (s-go c0 _ _ _ _) = lstep c0 to0

local : ∀ {c} → Safe c → LocalAt c (classify c)
local s = localAt s

-- Reception, an orphan, and a deadlock are not classes of a safe
-- configuration. The class index has no constructor for them.
notSafe : ∀ {c cl} → SafeAt c cl →
          (∀ {a b d e} → cl ≢ isFinal a b d e) →
          (∀ {c0 lt cs} → cl ≢ isGo c0 lt cs) → ⊥
notSafe (s-final a b d e) ¬f _ = ¬f refl
notSafe (s-go c0 lt cs _ _) _ ¬g = ¬g refl

no-class : ∀ {c cl} → Safe c → classify c ≡ cl →
           (∀ {a b d e} → cl ≢ isFinal a b d e) →
           (∀ {c0 lt cs} → cl ≢ isGo {c} c0 lt cs) → ⊥
no-class {c} okp eq ¬f ¬g = notSafe (subst (SafeAt c) eq okp) ¬f ¬g

no-recv : ∀ {c m s} → Safe c → classify c ≡ isRecv m s → ⊥
no-recv okp eq = no-class okp eq (λ {_} {_} {_} {_} ()) (λ {_} {_} {_} ())

no-orphan : ∀ {c} → Safe c → classify c ≡ isOrphan → ⊥
no-orphan okp eq = no-class okp eq (λ {_} {_} {_} {_} ()) (λ {_} {_} {_} ())

no-dead : ∀ {c} → Safe c → classify c ≡ isDead → ⊥
no-dead okp eq = no-class okp eq (λ {_} {_} {_} {_} ()) (λ {_} {_} {_} ())

reach-local : ∀ {c d} → Safe c → Reach c d → LocalAt d (classify d)
reach-local s r = local (reach-safe s r)

fromYes : ∀ {c} (r : Result c) → kind r ≡ is-yes → Safe c
fromYes (ok s) refl = s
fromYes (bad (freception _ _)) ()
fromYes (bad forphan) ()
fromYes (bad fdead) ()

------------------------------------------------------------------------
-- The initial configuration. Empty queues, empty environments.
------------------------------------------------------------------------

init : ℕ → Proc → Proc → Conf
init k P Q = mk k P Q [] [] [] [] none none

k0 : ℕ
k0 = nzero

k1 : ℕ
k1 = nsuc nzero

pong : Proc
pong = get nat "x" (put nat (lit one) done)

peer : Proc
peer = put nat (lit zero) (get nat "y" done)

ex-pong : kind (check (init k1 pong peer)) ≡ is-yes
ex-pong = refl

cross : Proc
cross = put nat (lit zero) (get nat "y" done)

ex-cross : kind (check (init k1 cross cross)) ≡ is-yes
ex-cross = refl

ex-cross-k0 : kind (check (init k0 cross cross)) ≡ is-dead
ex-cross-k0 = refl

only : Proc
only = put nat (lit zero) done

ex-orphan : kind (check (init k1 only done)) ≡ is-orphan
ex-orphan = refl

bitSend : Proc
bitSend = put bit (lit b0) done

natRecv : Proc
natRecv = get nat "x" done

ex-recv : kind (check (init k1 bitSend natRecv)) ≡ is-recv
ex-recv = refl

twoSend : Proc
twoSend = put nat (lit zero) (put nat (lit one) done)

twoGet : Proc
twoGet = get nat "x" (get nat "y" done)

ex-buf : kind (check (init k1 twoSend twoGet)) ≡ is-yes
ex-buf = refl

blockL : Proc
blockL = put nat (lit zero) (put nat (lit one) (get nat "a" done))

blockR : Proc
blockR = put nat (lit zero) (put nat (lit one) (get nat "b" done))

ex-block : kind (check (init k1 blockL blockR)) ≡ is-dead
ex-block = refl

ex-choice : kind (check (init k1 (pick0 done) (cover done done))) ≡ is-yes
ex-choice = refl

ex-mget : kind (check (init k1 (put boolTy (lit trueV) done)
                                 (mget boolTy "b" (done ∷ stop ∷ [])))) ≡ is-yes
ex-mget = refl

ex-iget : kind (check (init k1 (put bit (lit b0) done) (iget "b" done stop))) ≡ is-yes
ex-iget = refl

ex-halt : kind (check (init k1 done stop)) ≡ is-yes
ex-halt = refl

echoBack : Proc
echoBack = get boolTy "b" (put boolTy (var "b") done)

askBack : Proc
askBack = put boolTy (lit trueV) (mget boolTy "b" (done ∷ stop ∷ []))

ex-echo : kind (check (init k1 echoBack askBack)) ≡ is-yes
ex-echo = refl

pay-erases : mkPayL (init k1 done done) (lit zero) ≡
             pay nat (car nat (lit zero) (lit zero))
pay-erases = refl

pong-safe : Safe (init k1 pong peer)
pong-safe = fromYes (check (init k1 pong peer)) refl

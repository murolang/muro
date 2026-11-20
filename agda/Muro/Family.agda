------------------------------------------------------------------------
-- A keyed family, for any number of keys and any number of instances.
--
-- An instance has a key, a creation index, and a kind. `init` is never
-- held. `signal` is held while an earlier instance of its key is
-- unresolved. Unresolved means live: `opened` or `held`. A resolved
-- instance is not in the state. `arrive` opens or holds. `resolve`
-- drops an opened instance and opens every held signal of that key
-- which no longer has an earlier live instance. `rerun` and `meet`
-- leave an opened instance as it is. `rerun` is not bounded.
--
-- The invariant is the known-at-open reading. An opened signal of key
-- k has every earlier instance of k that had already arrived resolved.
-- An instance that arrives later is not one of those, so a smaller
-- creation index can still be live beside it. That is the overtake
-- this rule permits. It is not a lost signal: the signal opened when
-- nothing earlier was unresolved.
--
-- `no-starve` is a progress lemma. A held signal has an earlier live
-- instance of its own key, the least of those is opened, and the
-- creation index descends, so the wait is well-founded. The resolve
-- that clears the last earlier instance opens the signal.
--
-- A violation is an opened signal with an earlier live instance that
-- was already there when it opened. It projects to one key and two
-- instances. Renaming that pair lands on the script the family graph
-- explores on key `a`: `init` at 0 before `signal` at 1, or `signal`
-- at 1 before `signal` at 2. Key `b` is one `init` and cannot witness it.
--
-- Not in this module: the meeting graph, one retry then give-up,
-- `fail stop`, the book atom `resolved k init`, and the generator
-- that writes the dispatcher. `Muro.Temporal` is unchanged.
-- Elixir `Muro.Family.Step` mirrors `holdOf`, `blocked?`, `decide`,
-- `onKey`, `arriveTo`, `resolveTo`, `touchTo`, `NoOvertake`,
-- `HeldBlocked`, `BadOpen`, `script-a`, and `script-b` by those names.
--
-- The second half, from `Mode` on, is a parallel `Rules` development
-- of the same step for an arbitrary rule table: `mnever`, `mearlier`,
-- and `many`. It is not a transport of the theorems above.
-- `decideMode`, `anyBlocked?`, `earlierBlocked?`, `arriveMode`,
-- `resolveMode`, `withdrawTo`, `touchMode`, `RulesInv`, `AtMostOne`,
-- `NoOvertakeR`, `EarlierResolved`, `noStarve`, `withdrawGone`,
-- `cutoffTwo`, `cutoffScript`, and `anyGap` are the names `Step` uses.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Family where

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; T; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Nat.Properties
  using ( _≟_; _<?_; ≤-refl; ≤-trans; ≤-antisym; <⇒≤; <⇒≱; <⇒≢; n≮n; ≮⇒≥
        ; m<n⇒m<1+n; n<1+n; <-asym; <-trans )
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Nullary.Decidable.Core
  using (Dec; yes; no; ⌊_⌋; toWitness; fromWitness)

------------------------------------------------------------------------
-- Kinds and the one hold rule this development proves.
------------------------------------------------------------------------

data Kind : Set where
  init signal : Kind

data Hold : Set where
  never earlier : Hold

-- `init` opens on arrival. `signal` waits on earlier instances of its key.
holdOf : Kind → Hold
holdOf init = never
holdOf signal = earlier

data Phase : Set where
  opened held : Phase

-- key, creation index, id, birth tick, open tick, kind, phase.
data Row : Set where
  row : (key index ident born openedAt : ℕ) (kd : Kind) (ph : Phase) → Row

keyOf : Row → ℕ
keyOf (row k _ _ _ _ _ _) = k

indexOf : Row → ℕ
indexOf (row _ i _ _ _ _ _) = i

identOf : Row → ℕ
identOf (row _ _ n _ _ _ _) = n

bornOf : Row → ℕ
bornOf (row _ _ _ b _ _ _) = b

openedAtOf : Row → ℕ
openedAtOf (row _ _ _ _ a _ _) = a

kindOf : Row → Kind
kindOf (row _ _ _ _ _ kd _) = kd

phaseOf : Row → Phase
phaseOf (row _ _ _ _ _ _ p) = p

data State : Set where
  st : (next tick : ℕ) (rows : List Row) → State

rowsOf : State → List Row
rowsOf (st _ _ rs) = rs

nextOf : State → ℕ
nextOf (st n _ _) = n

tickOf : State → ℕ
tickOf (st _ t _) = t

empty : State
empty = st zero zero []

------------------------------------------------------------------------
-- Boolean order. `T` reflects the decision back into a proof.
------------------------------------------------------------------------

T-not : ∀ {b} → T (not b) → T b → ⊥
T-not {true} ()
T-not {false} _ ()

∧-intro : ∀ {x y} → T x → T y → T (x ∧ y)
∧-intro {true} {true} _ _ = tt
∧-intro {true} {false} _ ()
∧-intro {false} {_} ()

∧-left : ∀ {x y} → T (x ∧ y) → T x
∧-left {true} {_} _ = tt
∧-left {false} {_} ()

∧-right : ∀ {x y} → T (x ∧ y) → T y
∧-right {true} {true} _ = tt
∧-right {true} {false} ()
∧-right {false} {_} ()

∨-introˡ : ∀ {x y} → T x → T (x ∨ y)
∨-introˡ {true} {_} _ = tt
∨-introˡ {false} {_} ()

∨-introʳ : ∀ {x y} → T y → T (x ∨ y)
∨-introʳ {false} {true} _ = tt
∨-introʳ {true} {true} _ = tt
∨-introʳ {_} {false} ()

∨-elim : ∀ {x y} → T (x ∨ y) → T x ⊎ T y
∨-elim {true} {_} _ = inj₁ tt
∨-elim {false} {true} _ = inj₂ tt
∨-elim {false} {false} ()

yes-T : ∀ {P : Set} (d : Dec P) → P → T ⌊ d ⌋
yes-T d p = fromWitness {a? = d} p

no-T : ∀ {P : Set} (d : Dec P) → T ⌊ d ⌋ → P
no-T d t = toWitness {a? = d} t

opened≢held : opened ≡ held → ⊥
opened≢held ()

held≢opened : held ≡ held → opened ≡ held → ⊥
held≢opened _ ()

------------------------------------------------------------------------
-- Whether a signal is held reads only rows of its own key.
------------------------------------------------------------------------

blocked? : List Row → ℕ → ℕ → Bool
blocked? [] k i = false
blocked? (r ∷ rs) k i =
  ⌊ keyOf r ≟ k ⌋ ∧ ⌊ indexOf r <? i ⌋ ∨ blocked? rs k i

assign : Hold → Bool → Phase
assign never _ = opened
assign earlier true = held
assign earlier false = opened

decide : List Row → ℕ → ℕ → Kind → Phase
decide rs k i kd = assign (holdOf kd) (blocked? rs k i)

onKey : ℕ → List Row → List Row
onKey k [] = []
onKey k (r ∷ rs) with keyOf r ≟ k
... | yes _ = r ∷ onKey k rs
... | no _ = onKey k rs

onKey-skip : ∀ r rs k → ¬ (keyOf r ≡ k) → onKey k (r ∷ rs) ≡ onKey k rs
onKey-skip r rs k ¬k with keyOf r ≟ k
... | yes eq = ⊥-elim (¬k eq)
... | no _ = refl

------------------------------------------------------------------------
-- A blocked list really does contain an earlier row, and conversely.
------------------------------------------------------------------------

blocked-sound : ∀ rs k i → T (blocked? rs k i) →
                Σ Row (λ e → Any (_≡ e) rs × keyOf e ≡ k × indexOf e < i)
blocked-sound [] k i ()
blocked-sound (r ∷ rs) k i p with keyOf r ≟ k | indexOf r <? i
... | yes qk | yes qi = r , here refl , qk , qi
... | yes _ | no _ = let e , m , qk , qi = blocked-sound rs k i p in e , there m , qk , qi
... | no _ | _ = let e , m , qk , qi = blocked-sound rs k i p in e , there m , qk , qi

blocked-complete : ∀ rs k i e → Any (_≡ e) rs → keyOf e ≡ k → indexOf e < i →
                   T (blocked? rs k i)
blocked-complete (r ∷ rs) k i e (here refl) qk qi =
  ∨-introˡ (∧-intro (yes-T (keyOf e ≟ k) qk) (yes-T (indexOf e <? i) qi))
blocked-complete (r ∷ rs) k i e (there m) qk qi =
  ∨-introʳ {⌊ keyOf r ≟ k ⌋ ∧ ⌊ indexOf r <? i ⌋} (blocked-complete rs k i e m qk qi)

not-blocked : ∀ rs k i → T (not (blocked? rs k i)) →
              ∀ e → Any (_≡ e) rs → keyOf e ≡ k → ¬ (indexOf e < i)
not-blocked rs k i nb e m qk qi =
  T-not {blocked? rs k i} nb (blocked-complete rs k i e m qk qi)

held-decide : ∀ rs k i kd → decide rs k i kd ≡ held →
              T (blocked? rs k i) × kd ≡ signal
held-decide rs k i init eq = ⊥-elim (opened≢held eq)
held-decide rs k i signal eq with blocked? rs k i
... | true = tt , refl
... | false = ⊥-elim (opened≢held eq)

opened-clear : ∀ rs k i → decide rs k i signal ≡ opened → blocked? rs k i ≡ false
opened-clear rs k i eq with blocked? rs k i
... | false = refl
... | true = ⊥-elim (opened≢held (sym eq))

-- Rows of one key, in the order the list already has.
onKey-keep : ∀ {k rs r} → Any (_≡ r) rs → keyOf r ≡ k → Any (_≡ r) (onKey k rs)
onKey-keep {k} {r ∷ rs} {e} m qk with keyOf r ≟ k
... | yes _ with m
... | here refl = here refl
... | there mt = there (onKey-keep mt qk)
onKey-keep {k} {r ∷ rs} {e} m qk | no ¬k with m
... | here refl = ⊥-elim (¬k qk)
... | there mt = onKey-keep mt qk

onKey-lift : ∀ {k rs r} → Any (_≡ r) (onKey k rs) → Any (_≡ r) rs
onKey-lift {k} {r ∷ rs} m with keyOf r ≟ k
... | yes _ with m
... | here refl = here refl
... | there mt = there (onKey-lift mt)
onKey-lift {k} {r ∷ rs} m | no _ = there (onKey-lift m)

-- (a) Whether an arrival is held depends only on rows of its key.
-- `blocked?` is true of the whole list exactly when it is true of that key.
bool≡ : ∀ {b c} → (T b → T c) → (T c → T b) → b ≡ c
bool≡ {true} {true} _ _ = refl
bool≡ {false} {false} _ _ = refl
bool≡ {true} {false} f _ = ⊥-elim (f tt)
bool≡ {false} {true} _ g = ⊥-elim (g tt)

blocked?-onKey : ∀ rs k i → blocked? rs k i ≡ blocked? (onKey k rs) k i
blocked?-onKey rs k i =
  bool≡
    (λ tb →
      let e , m , qk , qi = blocked-sound rs k i tb
      in blocked-complete (onKey k rs) k i e (onKey-keep m qk) qk qi)
    (λ tb →
      let e , m , qk , qi = blocked-sound (onKey k rs) k i tb
      in blocked-complete rs k i e (onKey-lift m) qk qi)

decide-key : ∀ rs k i kd → decide rs k i kd ≡ decide (onKey k rs) k i kd
decide-key rs k i kd = cong (assign (holdOf kd)) (blocked?-onKey rs k i)

------------------------------------------------------------------------
-- Fresh arrivals, lookup, removal.
------------------------------------------------------------------------

clash : Row → ℕ → ℕ → Bool
clash r k i = ⌊ keyOf r ≟ k ⌋ ∧ ⌊ indexOf r ≟ i ⌋

fresh? : List Row → ℕ → ℕ → Bool
fresh? [] k i = true
fresh? (r ∷ rs) k i = not (clash r k i) ∧ fresh? rs k i

fresh-sound : ∀ rs k i → T (fresh? rs k i) →
              ∀ r → Any (_≡ r) rs → ¬ (keyOf r ≡ k × indexOf r ≡ i)
fresh-sound [] k i _ r ()
fresh-sound (x ∷ rs) k i p r (here refl) (qk , qi) =
  let nb = ∧-left {not (clash x k i)} p in
  T-not {clash x k i} nb
    (∧-intro (yes-T (keyOf x ≟ k) qk) (yes-T (indexOf x ≟ i) qi))
fresh-sound (x ∷ rs) k i p r (there m) pr =
  fresh-sound rs k i (∧-right {not (clash x k i)} p) r m pr

isHeld : Row → Bool
isHeld (row _ _ _ _ _ _ held) = true
isHeld (row _ _ _ _ _ _ opened) = false

isSignal : Row → Bool
isSignal (row _ _ _ _ _ signal _) = true
isSignal (row _ _ _ _ _ init _) = false

find : ℕ → List Row → Maybe Row
find id [] = nothing
find id (r ∷ rs) with identOf r ≟ id
... | yes _ = just r
... | no _ = find id rs

remove : ℕ → List Row → List Row
remove id [] = []
remove id (r ∷ rs) with identOf r ≟ id
... | yes _ = remove id rs
... | no _ = r ∷ remove id rs

stamp : ℕ → Row → Row
stamp t (row k i n b _ kd _) = row k i n b t kd opened

release? : ℕ → List Row → Row → Bool
release? k all r =
  ⌊ keyOf r ≟ k ⌋ ∧ isHeld r ∧ isSignal r ∧ not (blocked? all (keyOf r) (indexOf r))

openOne : ℕ → List Row → ℕ → Row → Row
openOne k all t r with release? k all r
... | true = stamp t r
... | false = r

openAll : ℕ → List Row → ℕ → List Row → List Row
openAll k all t [] = []
openAll k all t (r ∷ rs) = openOne k all t r ∷ openAll k all t rs

------------------------------------------------------------------------
-- The step relation. `rerun` and `meet` are the same family state:
-- an opened instance stays opened. The session that `meet` steps,
-- and the done-session side condition `check_trace` puts on `rerun`,
-- are not this relation.
------------------------------------------------------------------------

arriveTo : State → ℕ → Kind → ℕ → Maybe State
arriveTo (st n t rs) k kd i with fresh? rs k i
... | true = just (st (suc n) (suc t) (row k i n t t kd (decide rs k i kd) ∷ rs))
... | false = nothing

resolveTo : State → ℕ → Maybe State
resolveTo (st n t rs) id with find id rs
... | nothing = nothing
... | just r with phaseOf r
... | held = nothing
... | opened =
  let gone = remove id rs in
  just (st n (suc t) (openAll (keyOf r) gone t gone))

touchTo : State → ℕ → Maybe State
touchTo (st n t rs) id with find id rs
... | nothing = nothing
... | just r with phaseOf r
... | held = nothing
... | opened = just (st n t rs)

data Act : Set where
  arrive : (key index : ℕ) (kd : Kind) → Act
  resolve : ℕ → Act
  rerun : ℕ → Act
  meet : ℕ → Act

apply : State → Act → Maybe State
apply s (arrive k i kd) = arriveTo s k kd i
apply s (resolve id) = resolveTo s id
apply s (rerun id) = touchTo s id
apply s (meet id) = touchTo s id

------------------------------------------------------------------------
-- Invariant pieces.
------------------------------------------------------------------------

data NoDup : List Row → Set where
  dnone : NoDup []
  dmore : ∀ {r rs} →
          (∀ e → Any (_≡ e) rs → identOf e ≢ identOf r) →
          NoDup rs → NoDup (r ∷ rs)

data NoDupIx : List Row → Set where
  inone : NoDupIx []
  imore : ∀ {r rs} →
          (∀ e → Any (_≡ e) rs → ¬ (keyOf e ≡ keyOf r × indexOf e ≡ indexOf r)) →
          NoDupIx rs → NoDupIx (r ∷ rs)

data Below (n : ℕ) : List Row → Set where
  bnone : Below n []
  bmore : ∀ {r rs} → identOf r < n → Below n rs → Below n (r ∷ rs)

data Clock (t : ℕ) : List Row → Set where
  cnone : Clock t []
  cmore : ∀ {r rs} → bornOf r < t → openedAtOf r < t → Clock t rs → Clock t (r ∷ rs)

data HeldSig : List Row → Set where
  hnone : HeldSig []
  hmore : ∀ {r rs} → (phaseOf r ≡ held → kindOf r ≡ signal) → HeldSig rs → HeldSig (r ∷ rs)

-- An opened signal has no earlier live row that was already born.
NoOvertake : List Row → Set
NoOvertake rs =
  ∀ r e → Any (_≡ r) rs → Any (_≡ e) rs →
  kindOf r ≡ signal → phaseOf r ≡ opened →
  keyOf e ≡ keyOf r → indexOf e < indexOf r →
  bornOf e ≤ openedAtOf r → ⊥

-- A held row has an earlier live row of its key.
HeldBlocked : List Row → Set
HeldBlocked rs =
  ∀ r → Any (_≡ r) rs → phaseOf r ≡ held →
  Σ Row (λ e → Any (_≡ e) rs × keyOf e ≡ keyOf r × indexOf e < indexOf r)

record Invariant (s : State) : Set where
  constructor invariant
  field
    ids : NoDup (rowsOf s)
    ixs : NoDupIx (rowsOf s)
    below : Below (nextOf s) (rowsOf s)
    clock : Clock (tickOf s) (rowsOf s)
    held-sig : HeldSig (rowsOf s)
    blocked : HeldBlocked (rowsOf s)
    overtake : NoOvertake (rowsOf s)

open Invariant

clock-born : ∀ {t rs r} → Clock t rs → Any (_≡ r) rs → bornOf r < t
clock-born (cmore b _ _) (here refl) = b
clock-born (cmore _ _ c) (there m) = clock-born c m

clock-at : ∀ {t rs r} → Clock t rs → Any (_≡ r) rs → openedAtOf r < t
clock-at (cmore _ a _) (here refl) = a
clock-at (cmore _ _ c) (there m) = clock-at c m

below-at : ∀ {n rs r} → Below n rs → Any (_≡ r) rs → identOf r < n
below-at (bmore i _) (here refl) = i
below-at (bmore _ b) (there m) = below-at b m

held-at : ∀ {rs r} → HeldSig rs → Any (_≡ r) rs → phaseOf r ≡ held → kindOf r ≡ signal
held-at (hmore f _) (here refl) eq = f eq
held-at (hmore _ h) (there m) eq = held-at h m eq

clock-suc : ∀ {t rs} → Clock t rs → Clock (suc t) rs
clock-suc cnone = cnone
clock-suc (cmore b a c) = cmore (m<n⇒m<1+n b) (m<n⇒m<1+n a) (clock-suc c)

below-suc : ∀ {n rs} → Below n rs → Below (suc n) rs
below-suc bnone = bnone
below-suc (bmore i b) = bmore (m<n⇒m<1+n i) (below-suc b)

nodup-eq : ∀ {rs r e} → NoDup rs → Any (_≡ r) rs → Any (_≡ e) rs →
           identOf r ≡ identOf e → r ≡ e
nodup-eq (dmore _ _) (here refl) (here refl) _ = refl
nodup-eq (dmore sep _) (here refl) (there m) eq = ⊥-elim (sep _ m (sym eq))
nodup-eq (dmore sep _) (there m) (here refl) eq = ⊥-elim (sep _ m eq)
nodup-eq (dmore _ nd) (there mr) (there me) eq = nodup-eq nd mr me eq

index-sep : ∀ {e r} → indexOf e < indexOf r → e ≢ r
index-sep lt eq = <⇒≢ lt (cong indexOf eq)

------------------------------------------------------------------------
-- Empty state, and arrival.
------------------------------------------------------------------------

overtake-nil : NoOvertake []
overtake-nil _ _ ()

blocked-nil : HeldBlocked []
blocked-nil _ ()

empty-inv : Invariant empty
empty-inv = invariant dnone inone bnone cnone hnone blocked-nil overtake-nil

arrive-no : ∀ {rs k i n t kd} →
            NoOvertake rs → Clock t rs → T (fresh? rs k i) →
            let r0 = row k i n t t kd (decide rs k i kd) in
            NoOvertake (r0 ∷ rs)
arrive-no _ _ _ _ _ (here refl) (here refl) _ _ _ ixE _ = n≮n _ ixE
arrive-no {rs} {k} {i} _ _ _ _ e (here refl) (there me) refl op qk ixE _ =
  let eqb = opened-clear rs k i op
      tb = blocked-complete rs k i e me qk ixE
  in ⊥-elim (subst T eqb tb)
arrive-no _ clk _ r _ (there mr) (here refl) _ op _ _ bornE =
  <⇒≱ (clock-at clk mr) bornE
arrive-no noO _ _ r e (there mr) (there me) sig op qk ixE bornE =
  noO r e mr me sig op qk ixE bornE

arrive-blocked : ∀ {rs k i n t kd} →
                 HeldBlocked rs →
                 let r0 = row k i n t t kd (decide rs k i kd) in
                 HeldBlocked (r0 ∷ rs)
arrive-blocked {rs} {k} {i} {kd = kd} hb r (here refl) ph =
  let tb = proj₁ (held-decide rs k i kd ph)
      e , m , qk , qi = blocked-sound rs k i tb
  in e , there m , qk , qi
arrive-blocked hb r (there m) ph =
  let e , me , qk , qi = hb r m ph in e , there me , qk , qi

arrive-held : ∀ {rs k i n t kd} →
              HeldSig rs →
              let r0 = row k i n t t kd (decide rs k i kd) in
              (phaseOf r0 ≡ held → kindOf r0 ≡ signal) →
              HeldSig (r0 ∷ rs)
arrive-held h f = hmore f h

arrive-held-ok : ∀ {rs k i n t kd} →
                 let r0 = row k i n t t kd (decide rs k i kd) in
                 phaseOf r0 ≡ held → kindOf r0 ≡ signal
arrive-held-ok {rs} {k} {i} {kd = kd} eq = proj₂ (held-decide rs k i kd eq)

arrive-inv : ∀ {n t rs k kd i} →
             Invariant (st n t rs) → T (fresh? rs k i) →
             Invariant (st (suc n) (suc t) (row k i n t t kd (decide rs k i kd) ∷ rs))
arrive-inv {n} {t} {rs} {k} {kd} {i} inv fr =
  let r0 = row k i n t t kd (decide rs k i kd) in
  invariant
    (dmore (λ e m → <⇒≢ (below-at (below inv) m)) (ids inv))
    (imore (fresh-sound rs k i fr) (ixs inv))
    (bmore (n<1+n n) (below-suc (below inv)))
    (cmore (n<1+n t) (n<1+n t) (clock-suc (clock inv)))
    (arrive-held (held-sig inv) (arrive-held-ok {rs} {k} {i} {n} {t} {kd}))
    (arrive-blocked (blocked inv))
    (arrive-no (overtake inv) (clock inv) fr)

------------------------------------------------------------------------
-- Removal keeps the invariant's list facts, minus the resolved row.
------------------------------------------------------------------------

remove-mem : ∀ {rs e id} → Any (_≡ e) (remove id rs) → Any (_≡ e) rs × identOf e ≢ id
remove-mem {[]} ()
remove-mem {r ∷ rs} {e} {id} m with identOf r ≟ id
remove-mem {r ∷ rs} {e} {id} m | yes _ =
  let m' , ne = remove-mem {rs} m in there m' , ne
remove-mem {r ∷ rs} {e} {id} m | no ¬id with m
... | here refl = here refl , ¬id
... | there mt = let m' , ne = remove-mem {rs} mt in there m' , ne

remove-keep : ∀ {rs r id} → Any (_≡ r) rs → identOf r ≢ id → Any (_≡ r) (remove id rs)
remove-keep {r ∷ rs} {e} {id} m ne with identOf r ≟ id
... | yes eq with m
... | here refl = ⊥-elim (ne eq)
... | there mt = remove-keep {rs} mt ne
remove-keep {r ∷ rs} {e} {id} m ne | no ¬id with m
... | here refl = here refl
... | there mt = there (remove-keep {rs} mt ne)

sub-overtake : ∀ {rs id} → NoOvertake rs → NoOvertake (remove id rs)
sub-overtake noO r e mr me sig op qk qi bq =
  let mr' , _ = remove-mem mr
      me' , _ = remove-mem me
  in noO r e mr' me' sig op qk qi bq

nodup-remove : ∀ {id rs} → NoDup rs → NoDup (remove id rs)
nodup-remove {id} {[]} dnone = dnone
nodup-remove {id} {r ∷ rs} (dmore sep nd) with identOf r ≟ id
... | yes _ = nodup-remove nd
... | no _ =
  dmore (λ e m → let m' , _ = remove-mem m in sep e m') (nodup-remove nd)

nodupix-remove : ∀ {id rs} → NoDupIx rs → NoDupIx (remove id rs)
nodupix-remove {id} {[]} inone = inone
nodupix-remove {id} {r ∷ rs} (imore sep nd) with identOf r ≟ id
... | yes _ = nodupix-remove nd
... | no _ =
  imore (λ e m pr → let m' , _ = remove-mem m in sep e m' pr) (nodupix-remove nd)

below-remove : ∀ {n id rs} → Below n rs → Below n (remove id rs)
below-remove {n} {id} {[]} bnone = bnone
below-remove {n} {id} {r ∷ rs} (bmore i b) with identOf r ≟ id
... | yes _ = below-remove b
... | no _ = bmore i (below-remove b)

clock-remove : ∀ {t id rs} → Clock t rs → Clock t (remove id rs)
clock-remove {t} {id} {[]} cnone = cnone
clock-remove {t} {id} {r ∷ rs} (cmore b a c) with identOf r ≟ id
... | yes _ = clock-remove c
... | no _ = cmore b a (clock-remove c)

held-remove : ∀ {id rs} → HeldSig rs → HeldSig (remove id rs)
held-remove {id} {[]} hnone = hnone
held-remove {id} {r ∷ rs} (hmore f h) with identOf r ≟ id
... | yes _ = held-remove h
... | no _ = hmore f (held-remove h)

------------------------------------------------------------------------
-- openAll keeps identity and birth. It changes phase and openedAt
-- only for a held signal of the resolved key that is no longer blocked.
------------------------------------------------------------------------

open-key : ∀ k all t r → keyOf (openOne k all t r) ≡ keyOf r
open-key k all t r with release? k all r
open-key k all t (row _ _ _ _ _ _ _) | true = refl
open-key k all t r | false = refl

open-index : ∀ k all t r → indexOf (openOne k all t r) ≡ indexOf r
open-index k all t r with release? k all r
open-index k all t (row _ _ _ _ _ _ _) | true = refl
open-index k all t r | false = refl

open-ident : ∀ k all t r → identOf (openOne k all t r) ≡ identOf r
open-ident k all t r with release? k all r
open-ident k all t (row _ _ _ _ _ _ _) | true = refl
open-ident k all t r | false = refl

open-born : ∀ k all t r → bornOf (openOne k all t r) ≡ bornOf r
open-born k all t r with release? k all r
open-born k all t (row _ _ _ _ _ _ _) | true = refl
open-born k all t r | false = refl

open-kind : ∀ k all t r → kindOf (openOne k all t r) ≡ kindOf r
open-kind k all t r with release? k all r
open-kind k all t (row _ _ _ _ _ _ _) | true = refl
open-kind k all t r | false = refl

open-from : ∀ {k all t rs e} → Any (_≡ e) (openAll k all t rs) →
            Σ Row (λ s → Any (_≡ s) rs × e ≡ openOne k all t s)
open-from {rs = []} ()
open-from {rs = r ∷ rs} (here refl) = r , here refl , refl
open-from {rs = r ∷ rs} (there m) =
  let s , ms , eq = open-from m in s , there ms , eq

open-keep : ∀ {k all t rs r} → Any (_≡ r) rs →
            Any (_≡ openOne k all t r) (openAll k all t rs)
open-keep {rs = _ ∷ _} (here refl) = here refl
open-keep {rs = _ ∷ _} (there m) = there (open-keep m)

open-held : ∀ k all t r → phaseOf (openOne k all t r) ≡ held →
            openOne k all t r ≡ r × phaseOf r ≡ held
open-held k all t r eq with release? k all r
open-held k all t (row _ _ _ _ _ _ _) eq | true = ⊥-elim (opened≢held eq)
open-held k all t r eq | false = refl , eq

nodup-open : ∀ {k all t rs} → NoDup rs → NoDup (openAll k all t rs)
nodup-open {k} {all} {t} dnone = dnone
nodup-open {k} {all} {t} (dmore {r} sep nd) =
  dmore (λ e m eq →
    let s , ms , es = open-from m
    in sep s ms
         (trans (sym (trans (cong identOf es) (open-ident k all t s)))
                (trans eq (open-ident k all t r))))
       (nodup-open nd)

nodupix-open : ∀ {k all t rs} → NoDupIx rs → NoDupIx (openAll k all t rs)
nodupix-open {k} {all} {t} inone = inone
nodupix-open {k} {all} {t} (imore {r} sep nd) =
  imore (λ e m pr →
    let s , ms , es = open-from m
    in sep s ms
         ( trans (sym (trans (cong keyOf es) (open-key k all t s)))
                 (trans (proj₁ pr) (open-key k all t r))
         , trans (sym (trans (cong indexOf es) (open-index k all t s)))
                 (trans (proj₂ pr) (open-index k all t r)) ))
       (nodupix-open nd)

below-open : ∀ {n k all t rs} → Below n rs → Below n (openAll k all t rs)
below-open bnone = bnone
below-open {n} {k} {all} {t} (bmore {r} i b) =
  bmore (subst (_< n) (sym (open-ident k all t r)) i) (below-open b)

clock-open : ∀ {k all t rs} → Clock t rs → Clock (suc t) (openAll k all t rs)
clock-open {k} {all} {t} cnone = cnone
clock-open {k} {all} {t} (cmore {r} b a c) with release? k all r
clock-open {k} {all} {t} (cmore {row _ _ _ _ _ _ _} b a c) | true =
  cmore (m<n⇒m<1+n b) (n<1+n t) (clock-open c)
clock-open {k} {all} {t} (cmore {r} b a c) | false =
  cmore (m<n⇒m<1+n b) (m<n⇒m<1+n a) (clock-open c)

held-open : ∀ {k all t rs} → HeldSig rs → HeldSig (openAll k all t rs)
held-open {k} {all} {t} hnone = hnone
held-open {k} {all} {t} (hmore {r} f h) =
  hmore (λ ph →
    let _ , phs = open-held k all t r ph
    in trans (open-kind k all t r) (f phs))
       (held-open h)

∧⇒ʳ : ∀ {x y} → x ∧ y ≡ true → y ≡ true
∧⇒ʳ {true} {true} refl = refl
∧⇒ʳ {true} {false} ()
∧⇒ʳ {false} {_} ()

∧⇒ˡ : ∀ {x y} → x ∧ y ≡ true → x ≡ true
∧⇒ˡ {true} {true} refl = refl
∧⇒ˡ {true} {false} ()
∧⇒ˡ {false} {_} ()

∧-cong : ∀ {a b c d} → a ≡ b → c ≡ d → a ∧ c ≡ b ∧ d
∧-cong refl refl = refl

T→≡ : ∀ {b} → T b → b ≡ true
T→≡ {true} _ = refl
T→≡ {false} ()

not-inv : ∀ b → not b ≡ false → b ≡ true
not-inv true refl = refl
not-inv false ()

key-bit : ∀ s k → keyOf s ≡ k → ⌊ keyOf s ≟ k ⌋ ≡ true
key-bit s k eq with keyOf s ≟ k
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p eq)

held-bit : ∀ s → phaseOf s ≡ held → isHeld s ≡ true
held-bit (row _ _ _ _ _ _ held) refl = refl
held-bit (row _ _ _ _ _ _ opened) ()

signal-bit : ∀ s → kindOf s ≡ signal → isSignal s ≡ true
signal-bit (row _ _ _ _ _ signal _) refl = refl
signal-bit (row _ _ _ _ _ init _) ()

release-clear : ∀ k all r → release? k all r ≡ true →
                T (not (blocked? all (keyOf r) (indexOf r)))
release-clear k all r eq =
  subst T
    (sym (∧⇒ʳ {isSignal r}
           (∧⇒ʳ {isHeld r} (∧⇒ʳ {⌊ keyOf r ≟ k ⌋} eq))))
    tt

release-false-blocked : ∀ k all s →
  release? k all s ≡ false →
  keyOf s ≡ k → phaseOf s ≡ held → kindOf s ≡ signal →
  T (blocked? all (keyOf s) (indexOf s))
release-false-blocked k all s eq qk ph sg = from-true (not-inv _ cleared)
  where
  B = not (blocked? all (keyOf s) (indexOf s))
  bits : release? k all s ≡ B
  bits =
    ∧-cong (key-bit s k qk)
      (∧-cong (held-bit s ph) (∧-cong (signal-bit s sg) refl))
  cleared : B ≡ false
  cleared = trans (sym bits) eq
  from-true : ∀ {b} → b ≡ true → T b
  from-true refl = tt

still-false : ∀ k all t s → phaseOf (openOne k all t s) ≡ held →
              release? k all s ≡ false
still-false k all t s eq with release? k all s
still-false k all t (row _ _ _ _ _ _ _) eq | true = ⊥-elim (opened≢held eq)
still-false k all t s eq | false = refl

open-phase : ∀ k all t r → release? k all r ≡ false →
             phaseOf (openOne k all t r) ≡ phaseOf r
open-phase k all t r eq with release? k all r | eq
... | false | refl = refl
... | true | ()

open-at-keep : ∀ k all t r → release? k all r ≡ false →
               openedAtOf (openOne k all t r) ≡ openedAtOf r
open-at-keep k all t r eq with release? k all r | eq
... | false | refl = refl
... | true | ()

open-stamp : ∀ k all t r → release? k all r ≡ true →
             openOne k all t r ≡ stamp t r
open-stamp k all t r eq with release? k all r | eq
... | true | refl = refl
... | false | ()

-- A signal stamped open at this tick has no earlier live row: release
-- requires that. A signal that was already open lifts the old fact.
open-no : ∀ {k t rs} → NoOvertake rs → NoOvertake (openAll k rs t rs)
open-no {k} {t} {rs} noO r e mr me sig op qk ixE bq
  with open-from mr | open-from me
... | s , ms , refl | u , mu , refl = split (release? k rs s) refl
  where
  qks : keyOf u ≡ keyOf s
  qks = trans (sym (open-key k rs t u)) (trans qk (open-key k rs t s))
  ix-src : indexOf u < indexOf s
  ix-src =
    subst (λ z → z < indexOf s) (open-index k rs t u)
      (subst (λ z → indexOf (openOne k rs t u) < z) (open-index k rs t s) ixE)
  split : ∀ b → release? k rs s ≡ b → ⊥
  split true rel =
    T-not (release-clear k rs s rel)
          (blocked-complete rs (keyOf s) (indexOf s) u mu qks ix-src)
  split false rel =
    noO s u ms mu
      (trans (sym (open-kind k rs t s)) sig)
      (trans (sym (open-phase k rs t s rel)) op)
      qks
      ix-src
      (subst (λ z → bornOf u ≤ z) (open-at-keep k rs t s rel)
        (subst (λ z → z ≤ openedAtOf (openOne k rs t s)) (open-born k rs t u) bq))

-- A row left held was not released. On the resolved key that means an
-- earlier row is still live. On any other key the old witness is still
-- live, because the resolved row has a different key.
resolve-blocked : ∀ {rs id t} (r0 : Row) →
  NoDup rs → HeldBlocked rs → HeldSig rs →
  Any (_≡ r0) rs → identOf r0 ≡ id →
  HeldBlocked (openAll (keyOf r0) (remove id rs) t (remove id rs))
resolve-blocked {rs} {id} {t} r0 nd hb hs m0 idp heldRow mrow ph
  with open-from mrow
... | s , ms , refl = answer (keyOf s ≟ keyOf r0)
  where
  gone = remove id rs
  k0 = keyOf r0
  eqo = proj₁ (open-held k0 gone t s ph)
  phs = proj₂ (open-held k0 gone t s ph)
  ms' = proj₁ (remove-mem ms)
  ks = held-at hs ms' phs
  keyW : ∀ e → keyOf e ≡ keyOf s → keyOf (openOne k0 gone t e) ≡ keyOf heldRow
  keyW e ek =
    trans (open-key k0 gone t e) (trans ek (sym (cong keyOf eqo)))
  ixW : ∀ e → indexOf e < indexOf s → indexOf (openOne k0 gone t e) < indexOf heldRow
  ixW e ei =
    subst (λ z → z < indexOf heldRow) (sym (open-index k0 gone t e))
      (subst (λ z → indexOf e < z) (sym (cong indexOf eqo)) ei)
  answer : Dec (keyOf s ≡ keyOf r0) →
           Σ Row (λ e → Any (_≡ e) (openAll k0 gone t gone) ×
                        keyOf e ≡ keyOf heldRow × indexOf e < indexOf heldRow)
  answer (yes qk) =
    let rel = still-false k0 gone t s ph
        tb = release-false-blocked k0 gone s rel qk phs ks
        e , me , ek , ei = blocked-sound gone (keyOf s) (indexOf s) tb
    in openOne k0 gone t e , open-keep me , keyW e ek , ixW e ei
  answer (no ¬qk) =
    let e , me , ek , ei = hb s ms' phs
        ne : identOf e ≢ id
        ne eq = ¬qk (trans (sym ek)
                  (cong keyOf (nodup-eq nd me m0 (trans eq (sym idp)))))
    in openOne k0 gone t e , open-keep (remove-keep me ne) , keyW e ek , ixW e ei

resolve-go : ∀ {n t rs id} {r0 : Row} →
  Invariant (st n t rs) →
  Any (_≡ r0) rs → identOf r0 ≡ id →
  Invariant (st n (suc t) (openAll (keyOf r0) (remove id rs) t (remove id rs)))
resolve-go {n} {t} {rs} {id} {r0} inv m0 idp =
  let gone = remove id rs
      k0 = keyOf r0
  in invariant
       (nodup-open {k0} {gone} {t} (nodup-remove {id} (ids inv)))
       (nodupix-open {k0} {gone} {t} (nodupix-remove {id} (ixs inv)))
       (below-open {n} {k0} {gone} {t} (below-remove {n} {id} (below inv)))
       (clock-open {k0} {gone} {t} (clock-remove {t} {id} (clock inv)))
       (held-open {k0} {gone} {t} (held-remove {id} (held-sig inv)))
       (resolve-blocked {rs} {id} {t} r0 (ids inv) (blocked inv) (held-sig inv) m0 idp)
       (open-no {k0} {t} {gone} (sub-overtake {rs} {id} (overtake inv)))

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

nothing≢just : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nothing≢just ()

find-mem : ∀ {rs id r} → find id rs ≡ just r → Any (_≡ r) rs × identOf r ≡ id
find-mem {[]} ()
find-mem {x ∷ rs} {id} {r} eq with identOf x ≟ id
find-mem {x ∷ rs} {id} {r} eq | yes p =
  here (just-inj eq) , trans (cong identOf (sym (just-inj eq))) p
find-mem {x ∷ rs} {id} {r} eq | no ¬p =
  let m , ip = find-mem eq in there m , ip

arrive-pres : ∀ {n t rs k kd i s'} →
  Invariant (st n t rs) →
  arriveTo (st n t rs) k kd i ≡ just s' →
  Invariant s'
arrive-pres {n} {t} {rs} {k} {kd} {i} inv eq with fresh? rs k i in fr
... | false = ⊥-elim (nothing≢just eq)
... | true =
  subst Invariant (just-inj eq) (arrive-inv inv (subst T (sym fr) tt))

resolve-pres : ∀ {n t rs id s'} →
  Invariant (st n t rs) →
  resolveTo (st n t rs) id ≡ just s' →
  Invariant s'
resolve-pres {n} {t} {rs} {id} inv eq with find id rs in feq
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseOf r
... | held = ⊥-elim (nothing≢just eq)
... | opened =
  let m , idp = find-mem feq
  in subst Invariant (just-inj eq) (resolve-go inv m idp)

touch-pres : ∀ {n t rs id s'} →
  Invariant (st n t rs) →
  touchTo (st n t rs) id ≡ just s' →
  Invariant s'
touch-pres {rs = rs} {id = id} inv eq with find id rs
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseOf r
... | held = ⊥-elim (nothing≢just eq)
... | opened = subst Invariant (just-inj eq) inv

-- (b) Every accepted step preserves the invariant, at any size.
apply-inv : ∀ {s a s'} → Invariant s → apply s a ≡ just s' → Invariant s'
apply-inv {st _ _ _} {arrive k i kd} inv eq = arrive-pres inv eq
apply-inv {st _ _ _} {resolve id} inv eq = resolve-pres inv eq
apply-inv {st _ _ _} {rerun id} inv eq = touch-pres inv eq
apply-inv {st _ _ _} {meet id} inv eq = touch-pres inv eq

invariant-step : ∀ {s a s'} → Invariant s → apply s a ≡ just s' → Invariant s'
invariant-step {s} {a} {s'} inv eq = apply-inv {s} {a} {s'} inv eq

------------------------------------------------------------------------
-- (a) A step on one key does not change the rows of another key.
-- Heldness of an arrival is `decide-key`: it reads `onKey` only.
------------------------------------------------------------------------

onKey-remove-other : ∀ {id k rs} →
  NoDup rs →
  (∀ r → Any (_≡ r) rs → identOf r ≡ id → keyOf r ≢ k) →
  onKey k (remove id rs) ≡ onKey k rs
onKey-remove-other {id} {k} {[]} _ _ = refl
onKey-remove-other {id} {k} {x ∷ rs} (dmore _ nd) hyp with identOf x ≟ id
... | yes p =
  trans (onKey-remove-other nd (λ r m eq → hyp r (there m) eq))
        (sym (onKey-skip x rs k (hyp x (here refl) p)))
... | no ¬p with keyOf x ≟ k
... | yes _ =
  cong (x ∷_) (onKey-remove-other nd (λ r m eq → hyp r (there m) eq))
... | no _ =
  onKey-remove-other nd (λ r m eq → hyp r (there m) eq)

release-key : ∀ k all r → release? k all r ≡ true → keyOf r ≡ k
release-key k all r eq =
  no-T (keyOf r ≟ k) (subst T (sym (∧⇒ˡ eq)) tt)

open-stable : ∀ k' all t r → keyOf r ≢ k' → openOne k' all t r ≡ r
open-stable k' all t r ¬k with release? k' all r in eq
... | false = refl
... | true = ⊥-elim (¬k (release-key k' all r eq))

onKey-keep-head : ∀ r rs k → keyOf r ≡ k → onKey k (r ∷ rs) ≡ r ∷ onKey k rs
onKey-keep-head r rs k eq with keyOf r ≟ k
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p eq)

onKey-openAll-other : ∀ {k' k all t rs} → k' ≢ k →
  onKey k (openAll k' all t rs) ≡ onKey k rs
onKey-openAll-other {rs = []} _ = refl
onKey-openAll-other {k'} {k} {all} {t} {r ∷ rs} ¬eq = go (keyOf r ≟ k)
  where
  head = openOne k' all t r
  tail = openAll k' all t rs
  go : Dec (keyOf r ≡ k) → onKey k (head ∷ tail) ≡ onKey k (r ∷ rs)
  go (yes qk) =
    let kop = trans (open-key k' all t r) qk
        stable = open-stable k' all t r (λ z → ¬eq (sym (trans (sym qk) z)))
        ih = onKey-openAll-other {k'} {k} {all} {t} {rs} ¬eq
    in trans (onKey-keep-head head tail k kop)
         (trans (cong (λ z → z ∷ onKey k tail) stable)
           (trans (cong (r ∷_) ih)
                  (sym (onKey-keep-head r rs k qk))))
  go (no ¬k) =
    trans (onKey-skip head tail k (λ z → ¬k (trans (sym (open-key k' all t r)) z)))
          (trans (onKey-openAll-other {k'} {k} {all} {t} {rs} ¬eq)
                 (sym (onKey-skip r rs k ¬k)))

arrive-other : ∀ {k' k i n t kd rs} → k' ≢ k →
  onKey k (row k' i n t t kd (decide rs k' i kd) ∷ rs) ≡ onKey k rs
arrive-other {k'} {k} {i} {n} {t} {kd} {rs} ¬eq =
  onKey-skip (row k' i n t t kd (decide rs k' i kd)) rs k ¬eq

arrive-other-decide : ∀ rs k k' i kd i' n t kd' → k' ≢ k →
  decide (row k' i' n t t kd' (decide rs k' i' kd') ∷ rs) k i kd ≡ decide rs k i kd
arrive-other-decide rs k k' i kd i' n t kd' ¬eq =
  trans (decide-key (row k' i' n t t kd' (decide rs k' i' kd') ∷ rs) k i kd)
        (trans (cong (λ zs → decide zs k i kd)
                      (arrive-other {k'} {k} {i'} {n} {t} {kd'} {rs} ¬eq))
               (sym (decide-key rs k i kd)))

resolve-other : ∀ {n t rs id k s'} →
  Invariant (st n t rs) →
  resolveTo (st n t rs) id ≡ just s' →
  (∀ r → Any (_≡ r) rs → identOf r ≡ id → keyOf r ≢ k) →
  onKey k (rowsOf s') ≡ onKey k rs
resolve-other {n} {t} {rs} {id} {k} {s'} inv eq hyp with find id rs in feq
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseOf r
... | held = ⊥-elim (nothing≢just eq)
... | opened =
  let m , idp = find-mem feq
      gone = remove id rs
      rowsEq = cong rowsOf (just-inj eq)
      same = onKey-openAll-other {keyOf r} {k} {gone} {t} {gone} (hyp r m idp)
      drop = onKey-remove-other {id} {k} {rs} (ids inv) hyp
  in trans (sym (cong (onKey k) rowsEq)) (trans same drop)

touch-other : ∀ {n t rs id s'} →
  touchTo (st n t rs) id ≡ just s' → rowsOf s' ≡ rs
touch-other {rs = rs} {id = id} eq with find id rs
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseOf r
... | held = ⊥-elim (nothing≢just eq)
... | opened = sym (cong rowsOf (just-inj eq))

onKey-overtake : ∀ k rs → NoOvertake rs → NoOvertake (onKey k rs)
onKey-overtake k rs noO r e mr me sig op qk ixE bq =
  noO r e (onKey-lift mr) (onKey-lift me) sig op qk ixE bq

------------------------------------------------------------------------
-- (c) A held row waits on an opened earlier row of its own key.
-- The creation index descends, so the wait is well-founded. Resolving
-- the last earlier row opens it in that step. The host may never
-- resolve. This is not leads-to.
------------------------------------------------------------------------

data Earlier (k i : ℕ) : List Row → Row → Set where
  ehere : ∀ {r rs} → keyOf r ≡ k → indexOf r < i → Earlier k i (r ∷ rs) r
  ethere : ∀ {r rs e} → Earlier k i rs e → Earlier k i (r ∷ rs) e

earlier-mem : ∀ {k i rs e} → Earlier k i rs e → Any (_≡ e) rs
earlier-mem (ehere _ _) = here refl
earlier-mem (ethere m) = there (earlier-mem m)

earlier-key : ∀ {k i rs e} → Earlier k i rs e → keyOf e ≡ k
earlier-key (ehere qk _) = qk
earlier-key (ethere m) = earlier-key m

earlier-ix : ∀ {k i rs e} → Earlier k i rs e → indexOf e < i
earlier-ix (ehere _ qi) = qi
earlier-ix (ethere m) = earlier-ix m

earlier-of : ∀ {k i rs e} → Any (_≡ e) rs → keyOf e ≡ k → indexOf e < i →
             Earlier k i rs e
earlier-of (here refl) qk qi = ehere qk qi
earlier-of (there m) qk qi = ethere (earlier-of m qk qi)

phase? : (p : Phase) → p ≡ opened ⊎ p ≡ held
phase? opened = inj₁ refl
phase? held = inj₂ refl

pick : ∀ rs k i → T (blocked? rs k i) →
       Σ Row (λ e → Earlier k i rs e ×
                    (∀ e' → Earlier k i rs e' → indexOf e ≤ indexOf e'))
pick [] _ _ ()
pick (r ∷ rs) k i p with keyOf r ≟ k | indexOf r <? i
pick (r ∷ rs) k i p | yes qk | yes qi with blocked? rs k i in beq
... | false =
  r , (ehere qk qi , λ
    { .(r) (ehere _ _) → ≤-refl
    ; e' (ethere m) →
        ⊥-elim (not-blocked rs k i (subst T (sym (cong not beq)) tt)
                  e' (earlier-mem m) (earlier-key m) (earlier-ix m)) })
... | true =
  let m , em , least = pick rs k i (subst T (sym beq) tt) in choose m em least
  where
  choose : (m : Row) → Earlier k i rs m →
           (∀ e' → Earlier k i rs e' → indexOf m ≤ indexOf e') →
           Σ Row (λ e → Earlier k i (r ∷ rs) e ×
                        (∀ e' → Earlier k i (r ∷ rs) e' → indexOf e ≤ indexOf e'))
  choose m em least with indexOf r <? indexOf m
  ... | yes lt =
    r , (ehere qk qi , λ
      { .(r) (ehere _ _) → ≤-refl
      ; e' (ethere er) → ≤-trans (<⇒≤ lt) (least e' er) })
  ... | no ¬lt =
    m , (ethere em , λ
      { .(r) (ehere _ _) → ≮⇒≥ ¬lt
      ; e' (ethere er) → least e' er })
pick (r ∷ rs) k i p | yes _ | no ¬qi =
  let m , em , least = pick rs k i p in
  m , (ethere em , λ
    { .(r) (ehere _ qi) → ⊥-elim (¬qi qi)
    ; e' (ethere er) → least e' er })
pick (r ∷ rs) k i p | no ¬k | _ =
  let m , em , least = pick rs k i p in
  m , (ethere em , λ
    { .(r) (ehere qk _) → ⊥-elim (¬k qk)
    ; e' (ethere er) → least e' er })

least-open : ∀ {k i rs e} →
  HeldBlocked rs →
  Earlier k i rs e →
  (∀ e' → Earlier k i rs e' → indexOf e ≤ indexOf e') →
  phaseOf e ≡ opened
least-open {e = e} hb er least with phase? (phaseOf e)
... | inj₁ eq = eq
... | inj₂ eq =
  let w , mw , qk , qi = hb e (earlier-mem er) eq
      er' = earlier-of mw (trans qk (earlier-key er)) (<-trans qi (earlier-ix er))
  in ⊥-elim (<⇒≱ qi (least w er'))

no-starve : ∀ {rs r} →
  HeldBlocked rs → HeldSig rs →
  Any (_≡ r) rs → phaseOf r ≡ held →
  Σ Row (λ e →
    Any (_≡ e) rs × keyOf e ≡ keyOf r × indexOf e < indexOf r ×
    phaseOf e ≡ opened × kindOf r ≡ signal ×
    (∀ e' → Any (_≡ e') rs → keyOf e' ≡ keyOf r → indexOf e' < indexOf r →
       indexOf e ≤ indexOf e') ×
    Acc _<_ (indexOf r))
no-starve {rs} {r} hb hs mr ph =
  let w0 , mw0 , qk0 , qi0 = hb r mr ph
      picked = pick rs (keyOf r) (indexOf r)
                 (blocked-complete rs (keyOf r) (indexOf r) w0 mw0 qk0 qi0)
      e = proj₁ picked
      er = proj₁ (proj₂ picked)
      least = proj₂ (proj₂ picked)
  in e , earlier-mem er , earlier-key er , earlier-ix er
   , least-open hb er least
   , held-at hs mr ph
   , (λ e' m qk qi → least e' (earlier-of m qk qi))
   , <-wellFounded (indexOf r)

clear⇒open : ∀ {rs r} →
  HeldBlocked rs → Any (_≡ r) rs →
  (∀ e → Any (_≡ e) rs → keyOf e ≡ keyOf r → ¬ (indexOf e < indexOf r)) →
  phaseOf r ≢ held
clear⇒open hb m none ph =
  let e , me , qk , qi = hb _ m ph in none e me qk qi

notT→false : ∀ b → ¬ T b → b ≡ false
notT→false true ¬t = ⊥-elim (¬t tt)
notT→false false _ = refl

release-yes : ∀ k all s →
  keyOf s ≡ k → phaseOf s ≡ held → kindOf s ≡ signal →
  T (not (blocked? all (keyOf s) (indexOf s))) →
  release? k all s ≡ true
release-yes k all s qk ph sg nb = trans bits (T→≡ nb)
  where
  B = not (blocked? all (keyOf s) (indexOf s))
  bits : release? k all s ≡ B
  bits =
    ∧-cong (key-bit s k qk)
      (∧-cong (held-bit s ph) (∧-cong (signal-bit s sg) refl))

stamp-phase : ∀ t r → phaseOf (stamp t r) ≡ opened
stamp-phase t (row _ _ _ _ _ _ _) = refl

stamp-ident : ∀ t r → identOf (stamp t r) ≡ identOf r
stamp-ident t (row _ _ _ _ _ _ _) = refl

stamp-key : ∀ t r → keyOf (stamp t r) ≡ keyOf r
stamp-key t (row _ _ _ _ _ _ _) = refl

stamp-index : ∀ t r → indexOf (stamp t r) ≡ indexOf r
stamp-index t (row _ _ _ _ _ _ _) = refl

find-hit : ∀ {rs r} → NoDup rs → Any (_≡ r) rs → find (identOf r) rs ≡ just r
find-hit {[]} _ ()
find-hit {x ∷ rs} {r} (dmore sep nd) m with identOf x ≟ identOf r
find-hit {x ∷ rs} {r} (dmore sep nd) (here refl) | yes _ = refl
find-hit {x ∷ rs} {r} (dmore sep nd) (here refl) | no ¬eq = ⊥-elim (¬eq refl)
find-hit {x ∷ rs} {r} (dmore sep nd) (there m) | yes eq = ⊥-elim (sep r m (sym eq))
find-hit {x ∷ rs} {r} (dmore sep nd) (there m) | no _ = find-hit nd m

-- Resolving the only earlier live row opens the held signal.
release-open : ∀ {n t rs e r} →
  Invariant (st n t rs) →
  Any (_≡ e) rs → phaseOf e ≡ opened →
  Any (_≡ r) rs → phaseOf r ≡ held →
  keyOf r ≡ keyOf e → indexOf e < indexOf r →
  (∀ e' → Any (_≡ e') rs → keyOf e' ≡ keyOf r → indexOf e' < indexOf r → e' ≡ e) →
  Any (_≡ stamp t r) (openAll (keyOf e) (remove (identOf e) rs) t (remove (identOf e) rs))
release-open {t = t} {rs = rs} {e = e} {r = r} inv me _ mr ph qk ix uniq =
  let gone = remove (identOf e) rs
      k0 = keyOf e
      r≢ : identOf r ≢ identOf e
      r≢ eqid = index-sep ix (sym (nodup-eq (ids inv) mr me eqid))
      kept = remove-keep mr r≢
      clear : ¬ T (blocked? gone (keyOf r) (indexOf r))
      clear tb =
        let w , mw , qkw , qiw = blocked-sound gone (keyOf r) (indexOf r) tb
            mw' , wid = remove-mem mw
        in wid (trans (cong identOf (uniq w mw' qkw qiw)) refl)
      nb = subst T (sym (cong not (notT→false _ clear))) tt
      rel = release-yes k0 gone r qk ph (held-at (held-sig inv) mr ph) nb
  in subst (λ z → Any (_≡ z) (openAll k0 gone t gone))
           (open-stamp k0 gone t r rel) (open-keep kept)

release-last : ∀ {n t rs e r s'} →
  Invariant (st n t rs) →
  Any (_≡ e) rs → phaseOf e ≡ opened →
  Any (_≡ r) rs → phaseOf r ≡ held →
  keyOf r ≡ keyOf e → indexOf e < indexOf r →
  (∀ e' → Any (_≡ e') rs → keyOf e' ≡ keyOf r → indexOf e' < indexOf r → e' ≡ e) →
  resolveTo (st n t rs) (identOf e) ≡ just s' →
  Σ Row (λ r' → Any (_≡ r') (rowsOf s') × identOf r' ≡ identOf r ×
         keyOf r' ≡ keyOf r × indexOf r' ≡ indexOf r × phaseOf r' ≡ opened)
release-last {n} {t} {rs} {e} {r} {s'} inv me op mr ph qk ix uniq eq
  with find (identOf e) rs | find-hit (ids inv) me
... | just .e | refl with phaseOf e | op
... | opened | refl =
  let mem = release-open {n} {t} {rs} {e} {r} inv me op mr ph qk ix uniq
      r' = stamp t r
  in r' , subst (λ xs → Any (_≡ r') xs) (cong rowsOf (just-inj eq)) mem
       , stamp-ident t r , stamp-key t r , stamp-index t r , stamp-phase t r
... | held | ()

------------------------------------------------------------------------
-- A violation anywhere is a violation on one key and two rows, and
-- that pair renames onto script-a. script-b has no signal.
-- The meeting graph, one retry then give-up, and the generator are
-- not this argument. 171649 is not a bound of this proof.
------------------------------------------------------------------------

BadOpen : List Row → Set
BadOpen rs =
  Σ Row (λ r → Σ Row (λ e →
    Any (_≡ r) rs × Any (_≡ e) rs ×
    kindOf r ≡ signal × phaseOf r ≡ opened ×
    keyOf e ≡ keyOf r × indexOf e < indexOf r ×
    bornOf e ≤ openedAtOf r))

no-bad-open : ∀ {s} → Invariant s → ¬ BadOpen (rowsOf s)
no-bad-open inv (r , e , mr , me , sig , op , qk , ix , bq) =
  overtake inv r e mr me sig op qk ix bq

bad-widen : ∀ {k rs} → BadOpen (onKey k rs) → BadOpen rs
bad-widen (r , e , mr , me , sig , op , qk , ix , bq) =
  r , e , onKey-lift mr , onKey-lift me , sig , op , qk , ix , bq

data Reach : State → Set where
  start : Reach empty
  step : ∀ {s a s'} → Reach s → apply s a ≡ just s' → Reach s'

reach-inv : ∀ {s} → Reach s → Invariant s
reach-inv start = empty-inv
reach-inv (step {s} {a} {s'} prev eq) =
  invariant-step {s} {a} {s'} (reach-inv prev) eq

reach-safe : ∀ {s} → Reach s → ¬ BadOpen (rowsOf s)
reach-safe prev bad = no-bad-open (reach-inv prev) bad

data Slot : Set where
  slot : Kind → ℕ → Slot

script-a : List Slot
script-a = slot init 0 ∷ slot signal 1 ∷ slot signal 2 ∷ []

script-b : List Slot
script-b = slot init 0 ∷ []

witness-init : Any (_≡ slot init 0) script-a × Any (_≡ slot signal 1) script-a × 0 < 1
witness-init = here refl , there (here refl) , s≤s z≤n

witness-signal : Any (_≡ slot signal 1) script-a × Any (_≡ slot signal 2) script-a × 1 < 2
witness-signal = there (here refl) , there (there (here refl)) , s≤s (s≤s z≤n)

script-b-silent : ∀ j → ¬ Any (_≡ slot signal j) script-b
script-b-silent j (here ())
script-b-silent j (there ())

kind-either : ∀ kd → kd ≡ init ⊎ kd ≡ signal
kind-either init = inj₁ refl
kind-either signal = inj₂ refl

cutoff : ∀ {rs} → BadOpen rs →
  Σ Row (λ r → Σ Row (λ e →
    keyOf e ≡ keyOf r × kindOf r ≡ signal ×
    (kindOf e ≡ init ⊎ kindOf e ≡ signal) ×
    BadOpen (r ∷ e ∷ [])))
cutoff (r , e , _ , _ , sig , op , qk , ix , bq) =
  r , e , qk , sig , kind-either (kindOf e) ,
  (r , e , here refl , there (here refl) , sig , op , qk , ix , bq)

rename : ℕ → ℕ → Kind → Phase → Row → Row
rename k i kd ph (row _ _ n b a _ _) = row k i n b a kd ph

rename-born : ∀ k i kd ph r → bornOf (rename k i kd ph r) ≡ bornOf r
rename-born k i kd ph (row _ _ _ _ _ _ _) = refl

rename-at : ∀ k i kd ph r → openedAtOf (rename k i kd ph r) ≡ openedAtOf r
rename-at k i kd ph (row _ _ _ _ _ _ _) = refl

rename-key : ∀ k i kd ph r → keyOf (rename k i kd ph r) ≡ k
rename-key k i kd ph (row _ _ _ _ _ _ _) = refl

rename-index : ∀ k i kd ph r → indexOf (rename k i kd ph r) ≡ i
rename-index k i kd ph (row _ _ _ _ _ _ _) = refl

rename-kind : ∀ k i kd ph r → kindOf (rename k i kd ph r) ≡ kd
rename-kind k i kd ph (row _ _ _ _ _ _ _) = refl

rename-phase : ∀ k i kd ph r → phaseOf (rename k i kd ph r) ≡ ph
rename-phase k i kd ph (row _ _ _ _ _ _ _) = refl

-- Move `ie < ir` onto the renamed rows. Both rows share key 0.
shift-ix : ∀ {ie ir ke ph kr ph'} (e r : Row) → ie < ir →
  indexOf (rename 0 ie ke ph e) < indexOf (rename 0 ir kr ph' r)
shift-ix {ie} {ir} {ke} {ph} {kr} {ph'} e r lt =
  subst (λ z → z < indexOf (rename 0 ir kr ph' r))
        (sym (rename-index 0 ie ke ph e))
        (subst (ie <_) (sym (rename-index 0 ir kr ph' r)) lt)

cutoff-bound : ∀ {rs} → BadOpen rs →
  Σ Row (λ r' → Σ Row (λ e' →
    BadOpen (r' ∷ e' ∷ []) ×
    ( (kindOf e' ≡ init × indexOf e' ≡ 0 × indexOf r' ≡ 1 ×
       Any (_≡ slot init 0) script-a × Any (_≡ slot signal 1) script-a)
    ⊎ (kindOf e' ≡ signal × indexOf e' ≡ 1 × indexOf r' ≡ 2 ×
       Any (_≡ slot signal 1) script-a × Any (_≡ slot signal 2) script-a))))
cutoff-bound (r , e , _ , _ , _ , _ , _ , _ , bq) with kindOf e
... | init =
  let ph = phaseOf e
      r' = rename 0 1 signal opened r
      e' = rename 0 0 init ph e
      bq' = subst (λ z → bornOf e' ≤ z) (sym (rename-at 0 1 signal opened r))
              (subst (λ z → z ≤ openedAtOf r) (sym (rename-born 0 0 init ph e)) bq)
      qk' = trans (rename-key 0 0 init ph e) (sym (rename-key 0 1 signal opened r))
      bad : BadOpen (r' ∷ e' ∷ [])
      bad = r' , e' , here refl , there (here refl)
          , rename-kind 0 1 signal opened r , rename-phase 0 1 signal opened r
          , qk' , shift-ix {0} {1} {init} {ph} {signal} {opened} e r (s≤s z≤n) , bq'
  in r' , e' , bad
   , inj₁ ( rename-kind 0 0 init ph e , rename-index 0 0 init ph e
          , rename-index 0 1 signal opened r
          , here refl , there (here refl) )
... | signal =
  let ph = phaseOf e
      r' = rename 0 2 signal opened r
      e' = rename 0 1 signal ph e
      bq' = subst (λ z → bornOf e' ≤ z) (sym (rename-at 0 2 signal opened r))
              (subst (λ z → z ≤ openedAtOf r) (sym (rename-born 0 1 signal ph e)) bq)
      qk' = trans (rename-key 0 1 signal ph e) (sym (rename-key 0 2 signal opened r))
      bad : BadOpen (r' ∷ e' ∷ [])
      bad = r' , e' , here refl , there (here refl)
          , rename-kind 0 2 signal opened r , rename-phase 0 2 signal opened r
          , qk' , shift-ix {1} {2} {signal} {ph} {signal} {opened} e r (s≤s (s≤s z≤n)) , bq'
  in r' , e' , bad
   , inj₂ ( rename-kind 0 1 signal ph e , rename-index 0 1 signal ph e
          , rename-index 0 2 signal opened r
          , there (here refl) , there (there (here refl)) )

------------------------------------------------------------------------
-- Arbitrary rules. `mnever` opens on arrival. `mearlier` is the rule
-- above, for whatever kind carries it. `many` is held while any other
-- row of its key is opened, and a release opens at most one such row
-- of the key, the least creation index, and only when that release
-- opens no `mearlier` row. Kinds are numbers, so a family may have any
-- number of them. Keys and instances are unbounded, as above.
--
-- `withdrawTo` drops a held row and runs the same release. The id is
-- not reused. A left id is absent, so it is not a blocker.
--
-- `EarlierResolved` is the book atom for one key and one kind: an
-- opened row has no earlier live row of that same kind whose birth is
-- at most its open tick. It holds for `mearlier` and for `many`. It
-- does not hold for `mnever`.
--
-- A violation is still two rows of one key. It lands on `script-a`
-- only when the opened row is `mearlier` and the earlier row is
-- `mnever` or `mearlier`. Two opened `many` rows do not. Withdraw
-- adds no third shape. The meeting, the retry, give-up, `fail stop`,
-- and `resolved k init` stay outside, as they do above.
------------------------------------------------------------------------

data Mode : Set where
  mnever mearlier many : Mode

-- A rule for every kind tag. Kinds the family does not use may be
-- `mnever`; the step only reads the kind it is given.
Rules : Set
Rules = ℕ → Mode

isEarlier : Mode → Bool
isEarlier mearlier = true
isEarlier mnever = false
isEarlier many = false

isAny : Mode → Bool
isAny many = true
isAny mnever = false
isAny mearlier = false

earlier-bit : ∀ m → m ≡ mearlier → isEarlier m ≡ true
earlier-bit mearlier refl = refl

earlier-only : ∀ m → isEarlier m ≡ true → m ≡ mearlier
earlier-only mearlier refl = refl
earlier-only mnever ()
earlier-only many ()

any-bit : ∀ m → m ≡ many → isAny m ≡ true
any-bit many refl = refl

any-only : ∀ m → isAny m ≡ true → m ≡ many
any-only many refl = refl
any-only mnever ()
any-only mearlier ()

modes-split : ∀ m → m ≡ mearlier ⊎ m ≡ many ⊎ m ≡ mnever
modes-split mearlier = inj₁ refl
modes-split many = inj₂ (inj₁ refl)
modes-split mnever = inj₂ (inj₂ refl)

data RRow : Set where
  rr : (key index ident born openedAt kind : ℕ) (ph : Phase) → RRow

keyR : RRow → ℕ
keyR (rr k _ _ _ _ _ _) = k

indexR : RRow → ℕ
indexR (rr _ i _ _ _ _ _) = i

identR : RRow → ℕ
identR (rr _ _ n _ _ _ _) = n

bornR : RRow → ℕ
bornR (rr _ _ _ b _ _ _) = b

openedAtR : RRow → ℕ
openedAtR (rr _ _ _ _ a _ _) = a

kindR : RRow → ℕ
kindR (rr _ _ _ _ _ kd _) = kd

phaseR : RRow → Phase
phaseR (rr _ _ _ _ _ _ p) = p

data RState : Set where
  rst : (next tick : ℕ) (rows : List RRow) → RState

rowsR : RState → List RRow
rowsR (rst _ _ rs) = rs

nextR : RState → ℕ
nextR (rst n _ _) = n

tickR : RState → ℕ
tickR (rst _ t _) = t

emptyR : RState
emptyR = rst zero zero []

heldR : RRow → Bool
heldR (rr _ _ _ _ _ _ held) = true
heldR (rr _ _ _ _ _ _ opened) = false

openedR : RRow → Bool
openedR (rr _ _ _ _ _ _ opened) = true
openedR (rr _ _ _ _ _ _ held) = false

modeEarlier : Rules → RRow → Bool
modeEarlier ρ r = isEarlier (ρ (kindR r))

modeAny : Rules → RRow → Bool
modeAny ρ r = isAny (ρ (kindR r))

-- `blocked?` for `mearlier`: a live row of this key with a smaller index.
earlierBlocked? : List RRow → ℕ → ℕ → Bool
earlierBlocked? [] k i = false
earlierBlocked? (r ∷ rs) k i =
  ⌊ keyR r ≟ k ⌋ ∧ ⌊ indexR r <? i ⌋ ∨ earlierBlocked? rs k i

-- `anyBlocked?`. True when a row of `key` is opened. A held row is not
-- opened, so a held subject does not block itself. On arrival the new
-- row is not in the list.
anyBlocked? : List RRow → ℕ → Bool
anyBlocked? [] k = false
anyBlocked? (rr k' _ _ _ _ _ opened ∷ rs) k with k' ≟ k
... | yes _ = true
... | no _ = anyBlocked? rs k
anyBlocked? (rr _ _ _ _ _ _ held ∷ rs) k = anyBlocked? rs k

phaseOfBlocked : Bool → Phase
phaseOfBlocked true = held
phaseOfBlocked false = opened

decideMode : Rules → List RRow → ℕ → ℕ → ℕ → Phase
decideMode ρ rs k i kd with ρ kd
... | mnever = opened
... | mearlier = phaseOfBlocked (earlierBlocked? rs k i)
... | many = phaseOfBlocked (anyBlocked? rs k)

onKeyR : ℕ → List RRow → List RRow
onKeyR k [] = []
onKeyR k (r ∷ rs) with keyR r ≟ k
... | yes _ = r ∷ onKeyR k rs
... | no _ = onKeyR k rs

len : ∀ {A : Set} → List A → ℕ
len [] = zero
len (_ ∷ xs) = suc (len xs)

clashR : RRow → ℕ → ℕ → Bool
clashR r k i = ⌊ keyR r ≟ k ⌋ ∧ ⌊ indexR r ≟ i ⌋

freshR? : List RRow → ℕ → ℕ → Bool
freshR? [] k i = true
freshR? (r ∷ rs) k i = not (clashR r k i) ∧ freshR? rs k i

findR : ℕ → List RRow → Maybe RRow
findR id [] = nothing
findR id (r ∷ rs) with identR r ≟ id
... | yes _ = just r
... | no _ = findR id rs

removeR : ℕ → List RRow → List RRow
removeR id [] = []
removeR id (r ∷ rs) with identR r ≟ id
... | yes _ = removeR id rs
... | no _ = r ∷ removeR id rs

stampR : ℕ → RRow → RRow
stampR t (rr k i n b _ kd _) = rr k i n b t kd opened

-- `(index, id)` order. The least creation index wins; the id splits a
-- tie the invariant does not allow.
before? : RRow → RRow → Bool
before? (rr _ i n _ _ _ _) (rr _ j m _ _ _ _) with i <? j
... | yes _ = true
... | no _ with i ≟ j
... | yes _ = ⌊ n <? m ⌋
... | no _ = false

-- Another held `many` row of the same key, strictly before `r`.
smallerAny? : Rules → List RRow → RRow → Bool
smallerAny? ρ [] r = false
smallerAny? ρ (x ∷ xs) r =
  ⌊ keyR x ≟ keyR r ⌋ ∧ heldR x ∧ modeAny ρ x ∧ before? x r
  ∨ smallerAny? ρ xs r

-- A held `mearlier` row of this key that has no smaller live row.
hasEarlierCand : Rules → ℕ → List RRow → List RRow → Bool
hasEarlierCand ρ k all [] = false
hasEarlierCand ρ k all (x ∷ xs) =
  ⌊ keyR x ≟ k ⌋ ∧ heldR x ∧ modeEarlier ρ x ∧ not (earlierBlocked? all (keyR x) (indexR x))
  ∨ hasEarlierCand ρ k all xs

-- One row of a release. An unblocked `mearlier` row opens. An unblocked
-- `many` row opens only when no `mearlier` row opens, and only when no
-- earlier `many` row is also unblocked. `all` is the list after the
-- removed id, and it is the list `blocked` reads.
earlierClause : Rules → ℕ → List RRow → RRow → Bool
earlierClause ρ k all r =
  ⌊ keyR r ≟ k ⌋ ∧ heldR r ∧ modeEarlier ρ r ∧ not (earlierBlocked? all (keyR r) (indexR r))

anyClause : Rules → ℕ → List RRow → RRow → Bool
anyClause ρ k all r =
  ⌊ keyR r ≟ k ⌋ ∧ heldR r ∧ modeAny ρ r ∧ not (anyBlocked? all (keyR r))
    ∧ not (hasEarlierCand ρ k all all) ∧ not (smallerAny? ρ all r)

opens? : Rules → ℕ → List RRow → RRow → Bool
opens? ρ k all r = earlierClause ρ k all r ∨ anyClause ρ k all r

openOneR : Rules → ℕ → List RRow → ℕ → RRow → RRow
openOneR ρ k all t r with opens? ρ k all r
... | true = stampR t r
... | false = r

openAllR : Rules → ℕ → List RRow → ℕ → List RRow → List RRow
openAllR ρ k all t [] = []
openAllR ρ k all t (r ∷ rs) = openOneR ρ k all t r ∷ openAllR ρ k all t rs

arriveMode : Rules → RState → ℕ → ℕ → ℕ → Maybe RState
arriveMode ρ (rst n t rs) k kd i with freshR? rs k i
... | true =
  just (rst (suc n) (suc t) (rr k i n t t kd (decideMode ρ rs k i kd) ∷ rs))
... | false = nothing

resolveMode : Rules → RState → ℕ → Maybe RState
resolveMode ρ (rst n t rs) id with findR id rs
... | nothing = nothing
... | just r with phaseR r
... | held = nothing
... | opened =
  let gone = removeR id rs in
  just (rst n (suc t) (openAllR ρ (keyR r) gone t gone))

-- A held row leaves. The release is the release of `resolveMode`.
withdrawTo : Rules → RState → ℕ → Maybe RState
withdrawTo ρ (rst n t rs) id with findR id rs
... | nothing = nothing
... | just r with phaseR r
... | opened = nothing
... | held =
  let gone = removeR id rs in
  just (rst n (suc t) (openAllR ρ (keyR r) gone t gone))

touchMode : RState → ℕ → Maybe RState
touchMode (rst n t rs) id with findR id rs
... | nothing = nothing
... | just r with phaseR r
... | held = nothing
... | opened = just (rst n t rs)

data ActR : Set where
  arriveR : (key index kind : ℕ) → ActR
  resolveR : ℕ → ActR
  withdrawR : ℕ → ActR
  rerunR : ℕ → ActR
  meetR : ℕ → ActR

applyMode : Rules → RState → ActR → Maybe RState
applyMode ρ s (arriveR k i kd) = arriveMode ρ s k kd i
applyMode ρ s (resolveR id) = resolveMode ρ s id
applyMode ρ s (withdrawR id) = withdrawTo ρ s id
applyMode ρ s (rerunR id) = touchMode s id
applyMode ρ s (meetR id) = touchMode s id

------------------------------------------------------------------------
-- Invariant. `NoOvertakeR` is the known-at-open reading for `mearlier`.
-- `ResolvedAny` is that reading for an opened `many` row and an earlier
-- row of the same kind. `AtMostOne` is one opened `many` row per key.
------------------------------------------------------------------------

data NoDupR : List RRow → Set where
  drnone : NoDupR []
  drmore : ∀ {r rs} →
           (∀ e → Any (_≡ e) rs → identR e ≢ identR r) →
           NoDupR rs → NoDupR (r ∷ rs)

data NoDupIxR : List RRow → Set where
  irnone : NoDupIxR []
  irmore : ∀ {r rs} →
           (∀ e → Any (_≡ e) rs → ¬ (keyR e ≡ keyR r × indexR e ≡ indexR r)) →
           NoDupIxR rs → NoDupIxR (r ∷ rs)

data BelowR (n : ℕ) : List RRow → Set where
  brnone : BelowR n []
  brmore : ∀ {r rs} → identR r < n → BelowR n rs → BelowR n (r ∷ rs)

data ClockR (t : ℕ) : List RRow → Set where
  crnone : ClockR t []
  crmore : ∀ {r rs} → bornR r < t → openedAtR r < t → ClockR t rs → ClockR t (r ∷ rs)

HeldMode : Rules → List RRow → Set
HeldMode ρ rs =
  ∀ r → Any (_≡ r) rs → phaseR r ≡ held →
  ρ (kindR r) ≡ mearlier ⊎ ρ (kindR r) ≡ many

HeldEarlier : Rules → List RRow → Set
HeldEarlier ρ rs =
  ∀ r → Any (_≡ r) rs → phaseR r ≡ held → ρ (kindR r) ≡ mearlier →
  Σ RRow (λ e → Any (_≡ e) rs × keyR e ≡ keyR r × indexR e < indexR r)

HeldAny : Rules → List RRow → Set
HeldAny ρ rs =
  ∀ r → Any (_≡ r) rs → phaseR r ≡ held → ρ (kindR r) ≡ many →
  Σ RRow (λ e → Any (_≡ e) rs × keyR e ≡ keyR r × phaseR e ≡ opened)

AtMostOne : Rules → List RRow → Set
AtMostOne ρ rs =
  ∀ r e → Any (_≡ r) rs → Any (_≡ e) rs →
  keyR e ≡ keyR r → phaseR r ≡ opened → phaseR e ≡ opened →
  ρ (kindR r) ≡ many → ρ (kindR e) ≡ many → identR r ≡ identR e

NoOvertakeR : Rules → List RRow → Set
NoOvertakeR ρ rs =
  ∀ r e → Any (_≡ r) rs → Any (_≡ e) rs →
  ρ (kindR r) ≡ mearlier → phaseR r ≡ opened →
  keyR e ≡ keyR r → indexR e < indexR r →
  bornR e ≤ openedAtR r → ⊥

ResolvedAny : Rules → List RRow → Set
ResolvedAny ρ rs =
  ∀ r e → Any (_≡ r) rs → Any (_≡ e) rs →
  ρ (kindR r) ≡ many → phaseR r ≡ opened →
  kindR e ≡ kindR r → keyR e ≡ keyR r →
  indexR e < indexR r → bornR e ≤ openedAtR r → ⊥

record RulesInv (ρ : Rules) (s : RState) : Set where
  constructor rinv
  field
    rids : NoDupR (rowsR s)
    rixs : NoDupIxR (rowsR s)
    rbelow : BelowR (nextR s) (rowsR s)
    rclock : ClockR (tickR s) (rowsR s)
    rheld : HeldMode ρ (rowsR s)
    rearlier : HeldEarlier ρ (rowsR s)
    rany : HeldAny ρ (rowsR s)
    rone : AtMostOne ρ (rowsR s)
    rover : NoOvertakeR ρ (rowsR s)
    rresolved : ResolvedAny ρ (rowsR s)

open RulesInv

-- The book atom, for one key and one kind. The opening row is not
-- earlier than itself. A row that arrives later has a greater birth.
EarlierResolved : List RRow → ℕ → ℕ → Set
EarlierResolved rs k kd =
  ∀ r e → Any (_≡ r) rs → Any (_≡ e) rs →
  keyR r ≡ k → kindR r ≡ kd → keyR e ≡ k → kindR e ≡ kd →
  phaseR r ≡ opened → indexR e < indexR r →
  bornR e ≤ openedAtR r → ⊥

------------------------------------------------------------------------
-- Boolean reflection for the two block predicates.
------------------------------------------------------------------------

earlier-sound : ∀ rs k i → T (earlierBlocked? rs k i) →
                Σ RRow (λ e → Any (_≡ e) rs × keyR e ≡ k × indexR e < i)
earlier-sound [] k i ()
earlier-sound (r ∷ rs) k i p with keyR r ≟ k | indexR r <? i
... | yes qk | yes qi = r , here refl , qk , qi
... | yes _ | no _ =
  let e , m , qk , qi = earlier-sound rs k i p in e , there m , qk , qi
... | no _ | _ =
  let e , m , qk , qi = earlier-sound rs k i p in e , there m , qk , qi

earlier-complete : ∀ rs k i e → Any (_≡ e) rs → keyR e ≡ k → indexR e < i →
                   T (earlierBlocked? rs k i)
earlier-complete (r ∷ rs) k i e (here refl) qk qi =
  ∨-introˡ (∧-intro (yes-T (keyR e ≟ k) qk) (yes-T (indexR e <? i) qi))
earlier-complete (r ∷ rs) k i e (there m) qk qi =
  ∨-introʳ {⌊ keyR r ≟ k ⌋ ∧ ⌊ indexR r <? i ⌋}
           (earlier-complete rs k i e m qk qi)

not-earlier : ∀ rs k i → T (not (earlierBlocked? rs k i)) →
              ∀ e → Any (_≡ e) rs → keyR e ≡ k → ¬ (indexR e < i)
not-earlier rs k i nb e m qk qi =
  T-not {earlierBlocked? rs k i} nb (earlier-complete rs k i e m qk qi)

any-sound : ∀ rs k → T (anyBlocked? rs k) →
            Σ RRow (λ e → Any (_≡ e) rs × keyR e ≡ k × phaseR e ≡ opened)
any-sound [] k ()
any-sound (rr k' i n b a kd opened ∷ rs) k p with k' ≟ k
... | yes qk = rr k' i n b a kd opened , here refl , qk , refl
... | no _ =
  let e , m , qk , op = any-sound rs k p in e , there m , qk , op
any-sound (rr _ _ _ _ _ _ held ∷ rs) k p =
  let e , m , qk , op = any-sound rs k p in e , there m , qk , op

any-complete : ∀ rs k e → Any (_≡ e) rs → keyR e ≡ k → phaseR e ≡ opened →
               T (anyBlocked? rs k)
any-complete (rr k' i n b a kd opened ∷ rs) k e (here refl) qk refl with k' ≟ k
... | yes _ = tt
... | no ¬k = ⊥-elim (¬k qk)
any-complete (rr _ _ _ _ _ _ held ∷ rs) k e (here refl) qk ()
any-complete (rr k' i n b a kd opened ∷ rs) k e (there m) qk op with k' ≟ k
... | yes _ = tt
... | no _ = any-complete rs k e m qk op
any-complete (rr _ _ _ _ _ _ held ∷ rs) k e (there m) qk op =
  any-complete rs k e m qk op

not-any : ∀ rs k → T (not (anyBlocked? rs k)) →
          ∀ e → Any (_≡ e) rs → keyR e ≡ k → phaseR e ≢ opened
not-any rs k nb e m qk op =
  T-not {anyBlocked? rs k} nb (any-complete rs k e m qk op)

held-mode-arrive : ∀ ρ rs k i kd →
                   decideMode ρ rs k i kd ≡ held →
                   ρ kd ≡ mearlier ⊎ ρ kd ≡ many
held-mode-arrive ρ rs k i kd eq with ρ kd
held-mode-arrive ρ rs k i kd eq | mnever = ⊥-elim (opened≢held eq)
held-mode-arrive ρ rs k i kd eq | mearlier = inj₁ refl
held-mode-arrive ρ rs k i kd eq | many = inj₂ refl

earlier-decide : ∀ ρ rs k i kd →
                 decideMode ρ rs k i kd ≡ held → ρ kd ≡ mearlier →
                 T (earlierBlocked? rs k i)
earlier-decide ρ rs k i kd eq ρe with ρ kd | ρe
earlier-decide ρ rs k i kd eq ρe | mearlier | refl with earlierBlocked? rs k i
... | true = tt
... | false = ⊥-elim (opened≢held eq)

any-decide : ∀ ρ rs k i kd →
             decideMode ρ rs k i kd ≡ held → ρ kd ≡ many →
             T (anyBlocked? rs k)
any-decide ρ rs k i kd eq ρa with ρ kd | ρa
any-decide ρ rs k i kd eq ρa | many | refl with anyBlocked? rs k
... | true = tt
... | false = ⊥-elim (opened≢held eq)

opened-earlier-clear : ∀ ρ rs k i kd →
                       decideMode ρ rs k i kd ≡ opened → ρ kd ≡ mearlier →
                       earlierBlocked? rs k i ≡ false
opened-earlier-clear ρ rs k i kd eq ρe with ρ kd | ρe
opened-earlier-clear ρ rs k i kd eq ρe | mearlier | refl with earlierBlocked? rs k i
... | false = refl
... | true = ⊥-elim (opened≢held (sym eq))

opened-any-clear : ∀ ρ rs k i kd →
                   decideMode ρ rs k i kd ≡ opened → ρ kd ≡ many →
                   anyBlocked? rs k ≡ false
opened-any-clear ρ rs k i kd eq ρa with ρ kd | ρa
opened-any-clear ρ rs k i kd eq ρa | many | refl with anyBlocked? rs k
... | false = refl
... | true = ⊥-elim (opened≢held (sym eq))

modeEarlier-yes : ∀ ρ r → ρ (kindR r) ≡ mearlier → modeEarlier ρ r ≡ true
modeEarlier-yes ρ r eq = earlier-bit (ρ (kindR r)) eq

modeAny-yes : ∀ ρ r → ρ (kindR r) ≡ many → modeAny ρ r ≡ true
modeAny-yes ρ r eq = any-bit (ρ (kindR r)) eq

modeEarlier-no : ∀ ρ r → ρ (kindR r) ≢ mearlier → modeEarlier ρ r ≡ false
modeEarlier-no ρ r ¬e with ρ (kindR r) | ¬e
... | mnever | _ = refl
... | many | _ = refl
... | mearlier | ne = ⊥-elim (ne refl)

modeAny-no : ∀ ρ r → ρ (kindR r) ≢ many → modeAny ρ r ≡ false
modeAny-no ρ r ¬a with ρ (kindR r) | ¬a
... | mnever | _ = refl
... | mearlier | _ = refl
... | many | na = ⊥-elim (na refl)

held-bitR : ∀ r → phaseR r ≡ held → heldR r ≡ true
held-bitR (rr _ _ _ _ _ _ held) refl = refl

opened-bitR : ∀ r → phaseR r ≡ opened → openedR r ≡ true
opened-bitR (rr _ _ _ _ _ _ opened) refl = refl

key-bitR : ∀ r k → keyR r ≡ k → ⌊ keyR r ≟ k ⌋ ≡ true
key-bitR r k eq with keyR r ≟ k
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p eq)

clockR-born : ∀ {t rs r} → ClockR t rs → Any (_≡ r) rs → bornR r < t
clockR-born (crmore b _ _) (here refl) = b
clockR-born (crmore _ _ c) (there m) = clockR-born c m

clockR-at : ∀ {t rs r} → ClockR t rs → Any (_≡ r) rs → openedAtR r < t
clockR-at (crmore _ a _) (here refl) = a
clockR-at (crmore _ _ c) (there m) = clockR-at c m

belowR-at : ∀ {n rs r} → BelowR n rs → Any (_≡ r) rs → identR r < n
belowR-at (brmore i _) (here refl) = i
belowR-at (brmore _ b) (there m) = belowR-at b m

clockR-suc : ∀ {t rs} → ClockR t rs → ClockR (suc t) rs
clockR-suc crnone = crnone
clockR-suc (crmore b a c) = crmore (m<n⇒m<1+n b) (m<n⇒m<1+n a) (clockR-suc c)

belowR-suc : ∀ {n rs} → BelowR n rs → BelowR (suc n) rs
belowR-suc brnone = brnone
belowR-suc (brmore i b) = brmore (m<n⇒m<1+n i) (belowR-suc b)

nodupR-eq : ∀ {rs r e} → NoDupR rs → Any (_≡ r) rs → Any (_≡ e) rs →
            identR r ≡ identR e → r ≡ e
nodupR-eq (drmore _ _) (here refl) (here refl) _ = refl
nodupR-eq (drmore sep _) (here refl) (there m) eq = ⊥-elim (sep _ m (sym eq))
nodupR-eq (drmore sep _) (there m) (here refl) eq = ⊥-elim (sep _ m eq)
nodupR-eq (drmore _ nd) (there mr) (there me) eq = nodupR-eq nd mr me eq

freshR-sound : ∀ rs k i → T (freshR? rs k i) →
               ∀ r → Any (_≡ r) rs → ¬ (keyR r ≡ k × indexR r ≡ i)
freshR-sound [] k i _ r ()
freshR-sound (x ∷ rs) k i p r (here refl) (qk , qi) =
  let nb = ∧-left {not (clashR x k i)} p in
  T-not {clashR x k i} nb
    (∧-intro (yes-T (keyR x ≟ k) qk) (yes-T (indexR x ≟ i) qi))
freshR-sound (x ∷ rs) k i p r (there m) pr =
  freshR-sound rs k i (∧-right {not (clashR x k i)} p) r m pr

overR-nil : ∀ {ρ} → NoOvertakeR ρ []
overR-nil _ _ ()

resR-nil : ∀ {ρ} → ResolvedAny ρ []
resR-nil _ _ ()

oneR-nil : ∀ {ρ} → AtMostOne ρ []
oneR-nil _ _ ()

heldM-nil : ∀ {ρ} → HeldMode ρ []
heldM-nil _ ()

heldE-nil : ∀ {ρ} → HeldEarlier ρ []
heldE-nil _ ()

heldA-nil : ∀ {ρ} → HeldAny ρ []
heldA-nil _ ()

emptyR-inv : ∀ {ρ} → RulesInv ρ emptyR
emptyR-inv {ρ} =
  rinv drnone irnone brnone crnone
    (heldM-nil {ρ}) (heldE-nil {ρ}) (heldA-nil {ρ})
    (oneR-nil {ρ}) (overR-nil {ρ}) (resR-nil {ρ})

------------------------------------------------------------------------
-- Arrival preserves `RulesInv`.
------------------------------------------------------------------------

arriveR-over : ∀ {ρ rs k i n t kd} →
               NoOvertakeR ρ rs → ClockR t rs →
               let r0 = rr k i n t t kd (decideMode ρ rs k i kd) in
               NoOvertakeR ρ (r0 ∷ rs)
arriveR-over _ _ _ _ (here refl) (here refl) _ _ _ ix _ = n≮n _ ix
arriveR-over {ρ} {rs} {k} {i} {kd = kd} _ _ r e (here refl) (there me) ρe op qk ix _ =
  let clr = opened-earlier-clear ρ rs k i kd op ρe
      tb = earlier-complete rs k i e me qk ix
  in ⊥-elim (subst T clr tb)
arriveR-over _ clk r e (there mr) (here refl) _ _ _ _ bornE =
  <⇒≱ (clockR-at clk mr) bornE
arriveR-over noO _ r e (there mr) (there me) ρe op qk ix bornE =
  noO r e mr me ρe op qk ix bornE

arriveR-resolved : ∀ {ρ rs k i n t kd} →
                   HeldAny ρ rs → ResolvedAny ρ rs → ClockR t rs →
                   let r0 = rr k i n t t kd (decideMode ρ rs k i kd) in
                   ResolvedAny ρ (r0 ∷ rs)
arriveR-resolved _ _ _ _ _ (here refl) (here refl) _ _ _ _ ix _ = n≮n _ ix
arriveR-resolved {ρ} {rs} {k} {i} {kd = kd} ha _ _ r e (here refl) (there me) ρa op ke qk ix _
  with phase? (phaseR e)
... | inj₁ ope =
  let clr = opened-any-clear ρ rs k i kd op ρa
      tb = any-complete rs k e me qk ope
  in ⊥-elim (subst T clr tb)
... | inj₂ hde =
  let ρe = trans (cong ρ ke) ρa
      w , mw , kw , ow = ha e me hde ρe
      clr = opened-any-clear ρ rs k i kd op ρa
      tb = any-complete rs k w mw (trans kw qk) ow
  in ⊥-elim (subst T clr tb)
arriveR-resolved _ _ clk r e (there mr) (here refl) _ _ _ _ _ bq =
  <⇒≱ (clockR-at clk mr) bq
arriveR-resolved _ old _ r e (there mr) (there me) ρa op ke qk ix bq =
  old r e mr me ρa op ke qk ix bq

arriveR-held : ∀ {ρ rs k i n t kd} →
               HeldMode ρ rs →
               let r0 = rr k i n t t kd (decideMode ρ rs k i kd) in
               HeldMode ρ (r0 ∷ rs)
arriveR-held {ρ} {rs} {k} {i} {kd = kd} hm r (here refl) ph =
  held-mode-arrive ρ rs k i kd ph
arriveR-held hm r (there m) ph = hm r m ph

arriveR-earlier : ∀ {ρ rs k i n t kd} →
                  HeldEarlier ρ rs →
                  let r0 = rr k i n t t kd (decideMode ρ rs k i kd) in
                  HeldEarlier ρ (r0 ∷ rs)
arriveR-earlier {ρ} {rs} {k} {i} {kd = kd} he r (here refl) ph ρe =
  let tb = earlier-decide ρ rs k i kd ph ρe
      e , m , qk , qi = earlier-sound rs k i tb
  in e , there m , qk , qi
arriveR-earlier he r (there m) ph ρe =
  let e , me , qk , qi = he r m ph ρe in e , there me , qk , qi

arriveR-any : ∀ {ρ rs k i n t kd} →
              HeldAny ρ rs →
              let r0 = rr k i n t t kd (decideMode ρ rs k i kd) in
              HeldAny ρ (r0 ∷ rs)
arriveR-any {ρ} {rs} {k} {i} {kd = kd} ha r (here refl) ph ρa =
  let tb = any-decide ρ rs k i kd ph ρa
      e , m , qk , op = any-sound rs k tb
  in e , there m , qk , op
arriveR-any ha r (there m) ph ρa =
  let e , me , qk , op = ha r m ph ρa in e , there me , qk , op

arriveR-one : ∀ {ρ rs k i n t kd} →
              AtMostOne ρ rs →
              let r0 = rr k i n t t kd (decideMode ρ rs k i kd) in
              AtMostOne ρ (r0 ∷ rs)
arriveR-one _ _ _ (here refl) (here refl) _ _ _ _ _ = refl
arriveR-one {ρ} {rs} {k} {i} {kd = kd} _ r e (here refl) (there me) qk opr ope ρr ρe =
  let clr = opened-any-clear ρ rs k i kd opr ρr
      tb = any-complete rs k e me (trans qk refl) ope
  in ⊥-elim (subst T clr tb)
arriveR-one {ρ} {rs} {k} {i} {kd = kd} _ r e (there mr) (here refl) qk opr ope ρr ρe =
  let clr = opened-any-clear ρ rs k i kd ope ρe
      tb = any-complete rs k r mr (sym qk) opr
  in ⊥-elim (subst T clr tb)
arriveR-one one _ _ (there mr) (there me) qk opr ope ρr ρe =
  one _ _ mr me qk opr ope ρr ρe

arriveR-inv : ∀ {ρ n t rs k kd i} →
              RulesInv ρ (rst n t rs) → T (freshR? rs k i) →
              RulesInv ρ (rst (suc n) (suc t)
                (rr k i n t t kd (decideMode ρ rs k i kd) ∷ rs))
arriveR-inv {ρ} {n} {t} {rs} {k} {kd} {i} inv fr =
  rinv
    (drmore (λ e m → <⇒≢ (belowR-at (rbelow inv) m)) (rids inv))
    (irmore (freshR-sound rs k i fr) (rixs inv))
    (brmore (n<1+n n) (belowR-suc (rbelow inv)))
    (crmore (n<1+n t) (n<1+n t) (clockR-suc (rclock inv)))
    (arriveR-held {ρ} {rs} {k} {i} {n} {t} {kd} (rheld inv))
    (arriveR-earlier {ρ} {rs} {k} {i} {n} {t} {kd} (rearlier inv))
    (arriveR-any {ρ} {rs} {k} {i} {n} {t} {kd} (rany inv))
    (arriveR-one {ρ} {rs} {k} {i} {n} {t} {kd} (rone inv))
    (arriveR-over {ρ} {rs} {k} {i} {n} {t} {kd} (rover inv) (rclock inv))
    (arriveR-resolved {ρ} {rs} {k} {i} {n} {t} {kd} (rany inv) (rresolved inv) (rclock inv))

------------------------------------------------------------------------
-- Release. `opens?` is one unblocked `mearlier` row, or the least
-- unblocked `many` row when no `mearlier` row opens. `openAllR` then
-- keeps both invariants: an opened `mearlier` row still has no earlier
-- row that was already there, and an opened `many` row still has no
-- earlier row of its own kind that was already there. At most one
-- opened `many` row of a key remains.
------------------------------------------------------------------------

true≢false : true ≡ false → ⊥
true≢false ()

≡→T : ∀ {b} → b ≡ true → T b
≡→T refl = tt

not-true : ∀ b → not b ≡ true → b ≡ false
not-true true ()
not-true false refl = refl

force-true : ∀ b → (b ≡ false → ⊥) → b ≡ true
force-true true _ = refl
force-true false refuse = ⊥-elim (refuse refl)

not-T→false : ∀ b → T (not b) → b ≡ false
not-T→false true ()
not-T→false false tt = refl

many≢earlier : many ≡ mearlier → ⊥
many≢earlier ()

earlier≢many : mearlier ≡ many → ⊥
earlier≢many ()

∨-cong : ∀ {a b c d} → a ≡ b → c ≡ d → a ∨ c ≡ b ∨ d
∨-cong refl refl = refl

∨-trueˡ : ∀ {x y} → x ≡ true → x ∨ y ≡ true
∨-trueˡ refl = refl

∨-trueʳ : ∀ {x y} → y ≡ true → x ∨ y ≡ true
∨-trueʳ {false} refl = refl
∨-trueʳ {true} refl = refl

false∨ : ∀ b → false ∨ b ≡ b
false∨ true = refl
false∨ false = refl

∨-falseʳ : ∀ b → b ∨ false ≡ b
∨-falseʳ true = refl
∨-falseʳ false = refl

∧4 : ∀ {a b c d} → a ≡ true → b ≡ true → c ≡ true → d ≡ true →
     a ∧ b ∧ c ∧ d ≡ true
∧4 refl refl refl refl = refl

∧6 : ∀ {a b c d e f} →
     a ≡ true → b ≡ true → c ≡ true → d ≡ true → e ≡ true → f ≡ true →
     a ∧ b ∧ c ∧ d ∧ e ∧ f ≡ true
∧6 refl refl refl refl refl refl = refl

-- The held bit sits second. A false there kills the clause.
clause4-kill2 : ∀ a b c d → b ≡ false → a ∧ b ∧ c ∧ d ≡ false
clause4-kill2 false _ _ _ _ = refl
clause4-kill2 true false _ _ refl = refl
clause4-kill2 true true _ _ ()

clause4-kill3 : ∀ a b c d → c ≡ false → a ∧ b ∧ c ∧ d ≡ false
clause4-kill3 false _ _ _ _ = refl
clause4-kill3 true false _ _ _ = refl
clause4-kill3 true true false _ refl = refl
clause4-kill3 true true true _ ()

clause6-kill2 : ∀ a b c d e f → b ≡ false → a ∧ b ∧ c ∧ d ∧ e ∧ f ≡ false
clause6-kill2 false _ _ _ _ _ _ = refl
clause6-kill2 true false _ _ _ _ refl = refl
clause6-kill2 true true _ _ _ _ ()

clause6-kill3 : ∀ a b c d e f → c ≡ false → a ∧ b ∧ c ∧ d ∧ e ∧ f ≡ false
clause6-kill3 false _ _ _ _ _ _ = refl
clause6-kill3 true false _ _ _ _ _ = refl
clause6-kill3 true true false _ _ _ refl = refl
clause6-kill3 true true true _ _ _ ()

-- The last conjunct of a true clause. The proof need not be `refl`:
-- once the earlier bits are `true`, the clause is that last bit.
clause4-last : ∀ a b c d → a ∧ b ∧ c ∧ d ≡ true → d ≡ true
clause4-last true true true _ eq = eq
clause4-last true true false _ ()
clause4-last true false _ _ ()
clause4-last false _ _ _ ()

clause6-at4 : ∀ a b c d e f → a ∧ b ∧ c ∧ d ∧ e ∧ f ≡ true → d ≡ true
clause6-at4 true true true true _ _ _ = refl
clause6-at4 true true true false _ _ ()
clause6-at4 true true false _ _ _ ()
clause6-at4 true false _ _ _ _ ()
clause6-at4 false _ _ _ _ _ ()

clause6-last : ∀ a b c d e f → a ∧ b ∧ c ∧ d ∧ e ∧ f ≡ true → f ≡ true
clause6-last true true true true true _ eq = eq
clause6-last true true true true false _ ()
clause6-last true true true false _ _ ()
clause6-last true true false _ _ _ ()
clause6-last true false _ _ _ _ ()
clause6-last false _ _ _ _ _ ()

split4 : ∀ {a b c d} → T (a ∧ b ∧ c ∧ d) → T a × T b × T c × T d
split4 {true} {true} {true} {true} _ = tt , tt , tt , tt
split4 {true} {true} {true} {false} ()
split4 {true} {true} {false} {_} ()
split4 {true} {false} {_} {_} ()
split4 {false} {_} {_} {_} ()

stampR-key : ∀ t r → keyR (stampR t r) ≡ keyR r
stampR-key t (rr _ _ _ _ _ _ _) = refl

stampR-index : ∀ t r → indexR (stampR t r) ≡ indexR r
stampR-index t (rr _ _ _ _ _ _ _) = refl

stampR-ident : ∀ t r → identR (stampR t r) ≡ identR r
stampR-ident t (rr _ _ _ _ _ _ _) = refl

stampR-born : ∀ t r → bornR (stampR t r) ≡ bornR r
stampR-born t (rr _ _ _ _ _ _ _) = refl

stampR-kind : ∀ t r → kindR (stampR t r) ≡ kindR r
stampR-kind t (rr _ _ _ _ _ _ _) = refl

stampR-phase : ∀ t r → phaseR (stampR t r) ≡ opened
stampR-phase t (rr _ _ _ _ _ _ _) = refl

heldR→phase : ∀ r → heldR r ≡ true → phaseR r ≡ held
heldR→phase (rr _ _ _ _ _ _ held) refl = refl
heldR→phase (rr _ _ _ _ _ _ opened) ()

held-opened : ∀ r → phaseR r ≡ opened → heldR r ≡ false
held-opened (rr _ _ _ _ _ _ opened) refl = refl

opens-earlier : ∀ ρ k all r →
  keyR r ≡ k → phaseR r ≡ held → ρ (kindR r) ≡ mearlier →
  earlierBlocked? all (keyR r) (indexR r) ≡ false →
  opens? ρ k all r ≡ true
opens-earlier ρ k all r qk ph ρe eb =
  ∨-trueˡ {earlierClause ρ k all r} {anyClause ρ k all r}
    (∧4 (key-bitR r k qk) (held-bitR r ph) (modeEarlier-yes ρ r ρe) (cong not eb))

opens-any-yes : ∀ ρ k all r →
  keyR r ≡ k → phaseR r ≡ held → ρ (kindR r) ≡ many →
  anyBlocked? all (keyR r) ≡ false →
  hasEarlierCand ρ k all all ≡ false →
  smallerAny? ρ all r ≡ false →
  opens? ρ k all r ≡ true
opens-any-yes ρ k all r qk ph ρa ab hc sm =
  ∨-trueʳ {earlierClause ρ k all r} {anyClause ρ k all r}
    (∧6 (key-bitR r k qk) (held-bitR r ph) (modeAny-yes ρ r ρa)
        (cong not ab) (cong not hc) (cong not sm))

opens-opened : ∀ ρ k all r → phaseR r ≡ opened → opens? ρ k all r ≡ false
opens-opened ρ k all r op =
  let hb = held-opened r op in
  trans
    (∨-cong
      (clause4-kill2 (⌊ keyR r ≟ k ⌋) (heldR r) (modeEarlier ρ r)
         (not (earlierBlocked? all (keyR r) (indexR r))) hb)
      (clause6-kill2 (⌊ keyR r ≟ k ⌋) (heldR r) (modeAny ρ r)
         (not (anyBlocked? all (keyR r)))
         (not (hasEarlierCand ρ k all all))
         (not (smallerAny? ρ all r)) hb))
    (false∨ false)

opens-key : ∀ ρ k all r → opens? ρ k all r ≡ true → keyR r ≡ k
opens-key ρ k all r eq = key-of (∨-elim (≡→T eq))
  where
  key-of : T (earlierClause ρ k all r) ⊎ T (anyClause ρ k all r) → keyR r ≡ k
  key-of (inj₁ t) = no-T (keyR r ≟ k) (∧-left t)
  key-of (inj₂ t) = no-T (keyR r ≟ k) (∧-left t)

opens-was-held : ∀ ρ k all r → opens? ρ k all r ≡ true → phaseR r ≡ held
opens-was-held ρ k all (rr _ _ _ _ _ _ held) _ = refl
opens-was-held ρ k all (rr k' i n b a kd opened) eq =
  ⊥-elim (true≢false
    (trans (sym eq) (opens-opened ρ k all (rr k' i n b a kd opened) refl)))

opens-as-earlier : ∀ ρ k all r → ρ (kindR r) ≡ mearlier →
                   opens? ρ k all r ≡ earlierClause ρ k all r
opens-as-earlier ρ k all r ρe =
  trans
    (∨-cong refl
      (clause6-kill3 (⌊ keyR r ≟ k ⌋) (heldR r) (modeAny ρ r)
         (not (anyBlocked? all (keyR r)))
         (not (hasEarlierCand ρ k all all))
         (not (smallerAny? ρ all r))
         (modeAny-no ρ r (λ eq → earlier≢many (trans (sym ρe) eq)))))
    (∨-falseʳ (earlierClause ρ k all r))

opens-as-any : ∀ ρ k all r → ρ (kindR r) ≡ many →
               opens? ρ k all r ≡ anyClause ρ k all r
opens-as-any ρ k all r ρa =
  trans
    (∨-cong
      (clause4-kill3 (⌊ keyR r ≟ k ⌋) (heldR r) (modeEarlier ρ r)
         (not (earlierBlocked? all (keyR r) (indexR r)))
         (modeEarlier-no ρ r (λ eq → many≢earlier (trans (sym ρa) eq))))
      refl)
    (false∨ (anyClause ρ k all r))

opens-clear-earlier : ∀ ρ k all r →
  opens? ρ k all r ≡ true → ρ (kindR r) ≡ mearlier →
  earlierBlocked? all (keyR r) (indexR r) ≡ false
opens-clear-earlier ρ k all r eq ρe =
  not-true (earlierBlocked? all (keyR r) (indexR r))
    (clause4-last (⌊ keyR r ≟ k ⌋) (heldR r) (modeEarlier ρ r)
       (not (earlierBlocked? all (keyR r) (indexR r)))
       (trans (sym (opens-as-earlier ρ k all r ρe)) eq))

opens-clear-any : ∀ ρ k all r →
  opens? ρ k all r ≡ true → ρ (kindR r) ≡ many →
  anyBlocked? all (keyR r) ≡ false
opens-clear-any ρ k all r eq ρa =
  not-true (anyBlocked? all (keyR r))
    (clause6-at4 (⌊ keyR r ≟ k ⌋) (heldR r) (modeAny ρ r)
       (not (anyBlocked? all (keyR r)))
       (not (hasEarlierCand ρ k all all))
       (not (smallerAny? ρ all r))
       (trans (sym (opens-as-any ρ k all r ρa)) eq))

opens-clear-smaller : ∀ ρ k all r →
  opens? ρ k all r ≡ true → ρ (kindR r) ≡ many →
  smallerAny? ρ all r ≡ false
opens-clear-smaller ρ k all r eq ρa =
  not-true (smallerAny? ρ all r)
    (clause6-last (⌊ keyR r ≟ k ⌋) (heldR r) (modeAny ρ r)
       (not (anyBlocked? all (keyR r)))
       (not (hasEarlierCand ρ k all all))
       (not (smallerAny? ρ all r))
       (trans (sym (opens-as-any ρ k all r ρa)) eq))

opens-false-earlier : ∀ ρ k all r →
  opens? ρ k all r ≡ false →
  keyR r ≡ k → phaseR r ≡ held → ρ (kindR r) ≡ mearlier →
  T (earlierBlocked? all (keyR r) (indexR r))
opens-false-earlier ρ k all r eq qk ph ρe =
  ≡→T (force-true (earlierBlocked? all (keyR r) (indexR r))
        (λ eb → true≢false (trans (sym (opens-earlier ρ k all r qk ph ρe eb)) eq)))

opens-false-any : ∀ ρ k all r →
  opens? ρ k all r ≡ false →
  keyR r ≡ k → phaseR r ≡ held → ρ (kindR r) ≡ many →
  T (anyBlocked? all k) ⊎ T (hasEarlierCand ρ k all all) ⊎ T (smallerAny? ρ all r)
opens-false-any ρ k all r eq qk ph ρa =
  finish
    (classify (anyBlocked? all (keyR r)) (hasEarlierCand ρ k all all) (smallerAny? ρ all r)
      (λ ab hc sm →
         true≢false (trans (sym (opens-any-yes ρ k all r qk ph ρa ab hc sm)) eq)))
  where
  classify : ∀ a b c →
             (a ≡ false → b ≡ false → c ≡ false → ⊥) →
             T a ⊎ T b ⊎ T c
  classify true _ _ _ = inj₁ tt
  classify false true _ _ = inj₂ (inj₁ tt)
  classify false false true _ = inj₂ (inj₂ tt)
  classify false false false refuse = ⊥-elim (refuse refl refl refl)
  finish : T (anyBlocked? all (keyR r)) ⊎ T (hasEarlierCand ρ k all all) ⊎
           T (smallerAny? ρ all r) →
           T (anyBlocked? all k) ⊎ T (hasEarlierCand ρ k all all) ⊎
           T (smallerAny? ρ all r)
  finish (inj₁ p) = inj₁ (subst T (cong (anyBlocked? all) qk) p)
  finish (inj₂ (inj₁ p)) = inj₂ (inj₁ p)
  finish (inj₂ (inj₂ p)) = inj₂ (inj₂ p)

openR-key : ∀ ρ k all t r → keyR (openOneR ρ k all t r) ≡ keyR r
openR-key ρ k all t r with opens? ρ k all r
openR-key ρ k all t (rr _ _ _ _ _ _ _) | true = refl
openR-key ρ k all t r | false = refl

openR-index : ∀ ρ k all t r → indexR (openOneR ρ k all t r) ≡ indexR r
openR-index ρ k all t r with opens? ρ k all r
openR-index ρ k all t (rr _ _ _ _ _ _ _) | true = refl
openR-index ρ k all t r | false = refl

openR-ident : ∀ ρ k all t r → identR (openOneR ρ k all t r) ≡ identR r
openR-ident ρ k all t r with opens? ρ k all r
openR-ident ρ k all t (rr _ _ _ _ _ _ _) | true = refl
openR-ident ρ k all t r | false = refl

openR-born : ∀ ρ k all t r → bornR (openOneR ρ k all t r) ≡ bornR r
openR-born ρ k all t r with opens? ρ k all r
openR-born ρ k all t (rr _ _ _ _ _ _ _) | true = refl
openR-born ρ k all t r | false = refl

openR-kind : ∀ ρ k all t r → kindR (openOneR ρ k all t r) ≡ kindR r
openR-kind ρ k all t r with opens? ρ k all r
openR-kind ρ k all t (rr _ _ _ _ _ _ _) | true = refl
openR-kind ρ k all t r | false = refl

openR-phase-stay : ∀ ρ k all t r → opens? ρ k all r ≡ false →
                   phaseR (openOneR ρ k all t r) ≡ phaseR r
openR-phase-stay ρ k all t r eq with opens? ρ k all r | eq
... | false | refl = refl
... | true | ()

openR-at-stay : ∀ ρ k all t r → opens? ρ k all r ≡ false →
                openedAtR (openOneR ρ k all t r) ≡ openedAtR r
openR-at-stay ρ k all t r eq with opens? ρ k all r | eq
... | false | refl = refl
... | true | ()

openR-stamp : ∀ ρ k all t r → opens? ρ k all r ≡ true →
              openOneR ρ k all t r ≡ stampR t r
openR-stamp ρ k all t r eq with opens? ρ k all r | eq
... | true | refl = refl
... | false | ()

openR-id : ∀ ρ k all t r → opens? ρ k all r ≡ false → openOneR ρ k all t r ≡ r
openR-id ρ k all t r eq with opens? ρ k all r | eq
... | false | refl = refl
... | true | ()

openR-held-src : ∀ ρ k all t r → phaseR (openOneR ρ k all t r) ≡ held →
                 openOneR ρ k all t r ≡ r × phaseR r ≡ held
openR-held-src ρ k all t r eq with opens? ρ k all r
openR-held-src ρ k all t (rr _ _ _ _ _ _ _) eq | true = ⊥-elim (opened≢held eq)
openR-held-src ρ k all t r eq | false = refl , eq

stillR-false : ∀ ρ k all t r → phaseR (openOneR ρ k all t r) ≡ held →
               opens? ρ k all r ≡ false
stillR-false ρ k all t r eq with opens? ρ k all r
stillR-false ρ k all t (rr _ _ _ _ _ _ _) eq | true = ⊥-elim (opened≢held eq)
stillR-false ρ k all t r eq | false = refl

openR-stable : ∀ ρ k all t r → keyR r ≢ k → openOneR ρ k all t r ≡ r
openR-stable ρ k all t r ¬k with opens? ρ k all r in eq
... | false = refl
... | true = ⊥-elim (¬k (opens-key ρ k all r eq))

open-fromR : ∀ {ρ k all t rs e} → Any (_≡ e) (openAllR ρ k all t rs) →
             Σ RRow (λ s → Any (_≡ s) rs × e ≡ openOneR ρ k all t s)
open-fromR {rs = []} ()
open-fromR {rs = r ∷ rs} (here refl) = r , here refl , refl
open-fromR {ρ} {k} {all} {t} {r ∷ rs} (there m) =
  let s , ms , eq = open-fromR m in s , there ms , eq

open-keepR : ∀ {ρ k all t rs r} → Any (_≡ r) rs →
             Any (_≡ openOneR ρ k all t r) (openAllR ρ k all t rs)
open-keepR {rs = _ ∷ _} (here refl) = here refl
open-keepR {rs = _ ∷ _} (there m) = there (open-keepR m)

removeR-mem : ∀ {rs e id} → Any (_≡ e) (removeR id rs) →
              Any (_≡ e) rs × identR e ≢ id
removeR-mem {[]} ()
removeR-mem {r ∷ rs} {e} {id} m with identR r ≟ id
removeR-mem {r ∷ rs} {e} {id} m | yes _ =
  let m' , ne = removeR-mem {rs} m in there m' , ne
removeR-mem {r ∷ rs} {e} {id} m | no ¬id with m
... | here refl = here refl , ¬id
... | there mt = let m' , ne = removeR-mem {rs} mt in there m' , ne

removeR-keep : ∀ {rs r id} → Any (_≡ r) rs → identR r ≢ id →
               Any (_≡ r) (removeR id rs)
removeR-keep {r ∷ rs} {e} {id} m ne with identR r ≟ id
... | yes eq with m
... | here refl = ⊥-elim (ne eq)
... | there mt = removeR-keep {rs} mt ne
removeR-keep {r ∷ rs} {e} {id} m ne | no ¬id with m
... | here refl = here refl
... | there mt = there (removeR-keep {rs} mt ne)

nodupR-remove : ∀ {id rs} → NoDupR rs → NoDupR (removeR id rs)
nodupR-remove {id} {[]} drnone = drnone
nodupR-remove {id} {r ∷ rs} (drmore sep nd) with identR r ≟ id
... | yes _ = nodupR-remove nd
... | no _ =
  drmore (λ e m → let m' , _ = removeR-mem m in sep e m') (nodupR-remove nd)

nodupIxR-remove : ∀ {id rs} → NoDupIxR rs → NoDupIxR (removeR id rs)
nodupIxR-remove {id} {[]} irnone = irnone
nodupIxR-remove {id} {r ∷ rs} (irmore sep nd) with identR r ≟ id
... | yes _ = nodupIxR-remove nd
... | no _ =
  irmore (λ e m pr → let m' , _ = removeR-mem m in sep e m' pr) (nodupIxR-remove nd)

belowR-remove : ∀ {n id rs} → BelowR n rs → BelowR n (removeR id rs)
belowR-remove {n} {id} {[]} brnone = brnone
belowR-remove {n} {id} {r ∷ rs} (brmore i b) with identR r ≟ id
... | yes _ = belowR-remove b
... | no _ = brmore i (belowR-remove b)

clockR-remove : ∀ {t id rs} → ClockR t rs → ClockR t (removeR id rs)
clockR-remove {t} {id} {[]} crnone = crnone
clockR-remove {t} {id} {r ∷ rs} (crmore b a c) with identR r ≟ id
... | yes _ = clockR-remove c
... | no _ = crmore b a (clockR-remove c)

heldMode-remove : ∀ {ρ id rs} → HeldMode ρ rs → HeldMode ρ (removeR id rs)
heldMode-remove hm r m ph = let m' , _ = removeR-mem m in hm r m' ph

over-remove : ∀ {ρ id rs} → NoOvertakeR ρ rs → NoOvertakeR ρ (removeR id rs)
over-remove noO r e mr me ρe op qk ix bq =
  let mr' , _ = removeR-mem mr
      me' , _ = removeR-mem me
  in noO r e mr' me' ρe op qk ix bq

resolved-remove : ∀ {ρ id rs} → ResolvedAny ρ rs → ResolvedAny ρ (removeR id rs)
resolved-remove old r e mr me ρa op ke qk ix bq =
  let mr' , _ = removeR-mem mr
      me' , _ = removeR-mem me
  in old r e mr' me' ρa op ke qk ix bq

one-remove : ∀ {ρ id rs} → AtMostOne ρ rs → AtMostOne ρ (removeR id rs)
one-remove one r e mr me qk opr ope ρr ρe =
  let mr' , _ = removeR-mem mr
      me' , _ = removeR-mem me
  in one r e mr' me' qk opr ope ρr ρe

nodupR-open : ∀ {ρ k all t rs} → NoDupR rs → NoDupR (openAllR ρ k all t rs)
nodupR-open {ρ} {k} {all} {t} drnone = drnone
nodupR-open {ρ} {k} {all} {t} (drmore {r} sep nd) =
  drmore (λ e m eq →
    let s , ms , es = open-fromR m
    in sep s ms
         (trans (sym (trans (cong identR es) (openR-ident ρ k all t s)))
                (trans eq (openR-ident ρ k all t r))))
       (nodupR-open nd)

nodupIxR-open : ∀ {ρ k all t rs} → NoDupIxR rs → NoDupIxR (openAllR ρ k all t rs)
nodupIxR-open {ρ} {k} {all} {t} irnone = irnone
nodupIxR-open {ρ} {k} {all} {t} (irmore {r} sep nd) =
  irmore (λ e m pr →
    let s , ms , es = open-fromR m
    in sep s ms
         ( trans (sym (trans (cong keyR es) (openR-key ρ k all t s)))
                 (trans (proj₁ pr) (openR-key ρ k all t r))
         , trans (sym (trans (cong indexR es) (openR-index ρ k all t s)))
                 (trans (proj₂ pr) (openR-index ρ k all t r))))
       (nodupIxR-open nd)

belowR-open : ∀ {n ρ k all t rs} → BelowR n rs → BelowR n (openAllR ρ k all t rs)
belowR-open brnone = brnone
belowR-open {n} {ρ} {k} {all} {t} (brmore {r} i b) =
  brmore (subst (_< n) (sym (openR-ident ρ k all t r)) i) (belowR-open b)

clockR-open : ∀ {ρ k all t rs} → ClockR t rs → ClockR (suc t) (openAllR ρ k all t rs)
clockR-open {ρ} {k} {all} {t} crnone = crnone
clockR-open {ρ} {k} {all} {t} (crmore {r} b a c) with opens? ρ k all r
clockR-open {ρ} {k} {all} {t} (crmore {rr _ _ _ _ _ _ _} b a c) | true =
  crmore (m<n⇒m<1+n b) (n<1+n t) (clockR-open c)
clockR-open {ρ} {k} {all} {t} (crmore {r} b a c) | false =
  crmore (m<n⇒m<1+n b) (m<n⇒m<1+n a) (clockR-open c)

heldMode-open : ∀ {ρ k all t rs} →
                HeldMode ρ rs → HeldMode ρ (openAllR ρ k all t rs)
heldMode-open {ρ} {k} {all} {t} hm r m ph =
  let s , ms , eq = open-fromR m
      _ , phs = openR-held-src ρ k all t s
                  (subst (λ z → phaseR z ≡ held) eq ph)
      mode = hm s ms phs
      kq = trans (cong kindR eq) (openR-kind ρ k all t s)
  in subst (λ z → ρ z ≡ mearlier ⊎ ρ z ≡ many) (sym kq) mode

-- An opened `mearlier` row is not stamped over an earlier live row, and
-- a row that was already open keeps the old fact.
open-noR : ∀ {ρ k t rs} →
           NoOvertakeR ρ rs → NoOvertakeR ρ (openAllR ρ k rs t rs)
open-noR {ρ} {k} {t} {rs} noO r e mr me ρr op qk ix bq
  with open-fromR mr | open-fromR me
... | s , ms , refl | u , mu , refl = splitNo (opens? ρ k rs s) refl
  where
  qks : keyR u ≡ keyR s
  qks = trans (sym (openR-key ρ k rs t u)) (trans qk (openR-key ρ k rs t s))
  ix-src : indexR u < indexR s
  ix-src =
    subst (λ z → z < indexR s) (openR-index ρ k rs t u)
      (subst (λ z → indexR (openOneR ρ k rs t u) < z) (openR-index ρ k rs t s) ix)
  ρs : ρ (kindR s) ≡ mearlier
  ρs = subst (λ z → ρ z ≡ mearlier) (openR-kind ρ k rs t s) ρr
  splitNo : ∀ b → opens? ρ k rs s ≡ b → ⊥
  splitNo true oeq =
    true≢false
      (trans (sym (T→≡ (earlier-complete rs (keyR s) (indexR s) u mu qks ix-src)))
             (opens-clear-earlier ρ k rs s oeq ρs))
  splitNo false oeq =
    noO s u ms mu
      ρs
      (trans (sym (openR-phase-stay ρ k rs t s oeq)) op)
      qks
      ix-src
      (subst (λ z → bornR u ≤ z) (openR-at-stay ρ k rs t s oeq)
        (subst (λ z → z ≤ openedAtR (openOneR ρ k rs t s)) (openR-born ρ k rs t u) bq))

before-lt : ∀ e r → indexR e < indexR r → before? e r ≡ true
before-lt (rr _ i _ _ _ _ _) (rr _ j _ _ _ _ _) lt with i <? j
... | yes _ = refl
... | no ¬lt = ⊥-elim (¬lt lt)

hasEarlierCand-sound : ∀ ρ k all xs → T (hasEarlierCand ρ k all xs) →
  Σ RRow (λ e → Any (_≡ e) xs × keyR e ≡ k × heldR e ≡ true ×
            modeEarlier ρ e ≡ true ×
            earlierBlocked? all (keyR e) (indexR e) ≡ false)
hasEarlierCand-sound ρ k all [] ()
hasEarlierCand-sound ρ k all (x ∷ xs) p with
  ∨-elim {⌊ keyR x ≟ k ⌋ ∧ heldR x ∧ modeEarlier ρ x ∧
          not (earlierBlocked? all (keyR x) (indexR x))}
         {hasEarlierCand ρ k all xs} p
... | inj₁ t =
  let ta , tb , tc , td = split4 t in
  x , here refl , no-T (keyR x ≟ k) ta , T→≡ tb , T→≡ tc , not-T→false _ td
... | inj₂ t =
  let e , m , qk , hd , md , nb = hasEarlierCand-sound ρ k all xs t
  in e , there m , qk , hd , md , nb

smallerAny-sound : ∀ ρ xs r → T (smallerAny? ρ xs r) →
  Σ RRow (λ e → Any (_≡ e) xs × keyR e ≡ keyR r × heldR e ≡ true ×
            modeAny ρ e ≡ true × before? e r ≡ true)
smallerAny-sound ρ [] r ()
smallerAny-sound ρ (x ∷ xs) r p with
  ∨-elim {⌊ keyR x ≟ keyR r ⌋ ∧ heldR x ∧ modeAny ρ x ∧ before? x r}
         {smallerAny? ρ xs r} p
... | inj₁ t =
  let ta , tb , tc , td = split4 t in
  x , here refl , no-T (keyR x ≟ keyR r) ta , T→≡ tb , T→≡ tc , T→≡ td
... | inj₂ t =
  let e , m , qk , hd , md , bf = smallerAny-sound ρ xs r t
  in e , there m , qk , hd , md , bf

smallerAny-complete : ∀ ρ xs r e → Any (_≡ e) xs →
  keyR e ≡ keyR r → heldR e ≡ true → modeAny ρ e ≡ true → before? e r ≡ true →
  T (smallerAny? ρ xs r)
smallerAny-complete ρ (x ∷ xs) r .x (here refl) qk hd ma bf =
  ∨-introˡ (∧-intro (yes-T (keyR x ≟ keyR r) qk)
            (∧-intro (≡→T hd) (∧-intro (≡→T ma) (≡→T bf))))
smallerAny-complete ρ (x ∷ xs) r e (there m) qk hd ma bf =
  ∨-introʳ {⌊ keyR x ≟ keyR r ⌋ ∧ heldR x ∧ modeAny ρ x ∧ before? x r}
           (smallerAny-complete ρ xs r e m qk hd ma bf)

-- A newly opened `many` row has no earlier live row of its kind: an
-- opened one would block it, and a held one would be smaller.
open-resolved : ∀ {ρ k t rs} →
                ResolvedAny ρ rs → ResolvedAny ρ (openAllR ρ k rs t rs)
open-resolved {ρ} {k} {t} {rs} old r e mr me ρa op ke qk ix bq
  with open-fromR mr | open-fromR me
... | s , ms , refl | u , mu , refl = splitRes (opens? ρ k rs s) refl
  where
  qks : keyR u ≡ keyR s
  qks = trans (sym (openR-key ρ k rs t u)) (trans qk (openR-key ρ k rs t s))
  kes : kindR u ≡ kindR s
  kes = trans (sym (openR-kind ρ k rs t u)) (trans ke (openR-kind ρ k rs t s))
  ix-src : indexR u < indexR s
  ix-src =
    subst (λ z → z < indexR s) (openR-index ρ k rs t u)
      (subst (λ z → indexR (openOneR ρ k rs t u) < z) (openR-index ρ k rs t s) ix)
  ρs : ρ (kindR s) ≡ many
  ρs = subst (λ z → ρ z ≡ many) (openR-kind ρ k rs t s) ρa
  ρu : ρ (kindR u) ≡ many
  ρu = subst (λ z → ρ z ≡ many) (sym kes) ρs
  splitRes : ∀ b → opens? ρ k rs s ≡ b → ⊥
  splitRes false oeq =
    old s u ms mu ρs
      (trans (sym (openR-phase-stay ρ k rs t s oeq)) op)
      kes qks ix-src
      (subst (λ z → bornR u ≤ z) (openR-at-stay ρ k rs t s oeq)
        (subst (λ z → z ≤ openedAtR (openOneR ρ k rs t s))
               (openR-born ρ k rs t u) bq))
  splitRes true oeq = byPhase (phase? (phaseR u))
    where
    byPhase : phaseR u ≡ opened ⊎ phaseR u ≡ held → ⊥
    byPhase (inj₁ ou) =
      true≢false
        (trans (sym (T→≡ (any-complete rs (keyR s) u mu qks ou)))
               (opens-clear-any ρ k rs s oeq ρs))
    byPhase (inj₂ hu) =
      true≢false
        (trans
          (sym (T→≡ (smallerAny-complete ρ rs s u mu qks
                      (held-bitR u hu) (modeAny-yes ρ u ρu) (before-lt u s ix-src))))
          (opens-clear-smaller ρ k rs s oeq ρs))

before-index : ∀ e r → before? e r ≡ true →
               (indexR e < indexR r) ⊎ (indexR e ≡ indexR r × identR e < identR r)
before-index (rr _ i n _ _ _ _) (rr _ j m _ _ _ _) eq with i <? j
... | yes lt = inj₁ lt
... | no _ with i ≟ j
... | yes q with n <? m
... | yes nid = inj₂ (q , nid)
... | no _ = ⊥-elim (true≢false (sym eq))
before-index (rr _ _ _ _ _ _ _) (rr _ _ _ _ _ _ _) eq | no _ | no _ =
  ⊥-elim (true≢false (sym eq))

nodupIxR-eq : ∀ {rs r e} → NoDupIxR rs → Any (_≡ r) rs → Any (_≡ e) rs →
              keyR r ≡ keyR e → indexR r ≡ indexR e → r ≡ e
nodupIxR-eq (irmore _ _) (here refl) (here refl) _ _ = refl
nodupIxR-eq (irmore sep _) (here refl) (there m) qk qi =
  ⊥-elim (sep _ m (sym qk , sym qi))
nodupIxR-eq (irmore sep _) (there m) (here refl) qk qi =
  ⊥-elim (sep _ m (qk , qi))
nodupIxR-eq (irmore _ nd) (there mr) (there me) qk qi =
  nodupIxR-eq nd mr me qk qi

before-smaller : ∀ {rs e r} → NoDupIxR rs → Any (_≡ e) rs → Any (_≡ r) rs →
                 keyR e ≡ keyR r → before? e r ≡ true → indexR e < indexR r
before-smaller {e = e} {r = r} ix me mr qk bf with before-index e r bf
... | inj₁ lt = lt
... | inj₂ (qi , ni) =
  ⊥-elim (n≮n (identR r)
    (subst (λ z → z < identR r)
           (cong identR (nodupIxR-eq ix me mr qk qi)) ni))

-- A held row has an opened row of its key. `mearlier` walks down the
-- creation index. `many` is blocked by an opened row directly.
noStarve-go : ∀ {ρ rs r} →
  HeldMode ρ rs → HeldEarlier ρ rs → HeldAny ρ rs →
  Any (_≡ r) rs → phaseR r ≡ held → Acc _<_ (indexR r) →
  Σ RRow (λ e → Any (_≡ e) rs × keyR e ≡ keyR r × phaseR e ≡ opened)
noStarve-go {ρ} hm he ha mr ph (acc rec) with hm _ mr ph
noStarve-go {ρ} hm he ha mr ph (acc rec) | inj₂ ρa =
  let e , me , qk , op = ha _ mr ph ρa in e , me , qk , op
noStarve-go {ρ} hm he ha mr ph (acc rec) | inj₁ ρe with he _ mr ph ρe
noStarve-go {ρ} hm he ha mr ph (acc rec) | inj₁ ρe | e , me , qk , qi
  with phase? (phaseR e)
noStarve-go {ρ} hm he ha mr ph (acc rec) | inj₁ ρe | e , me , qk , qi | inj₁ op =
  e , me , qk , op
noStarve-go {ρ} hm he ha mr ph (acc rec) | inj₁ ρe | e , me , qk , qi | inj₂ hd =
  let w , mw , kw , ow = noStarve-go {ρ} hm he ha me hd (rec {y = indexR e} qi)
  in w , mw , trans kw qk , ow

noStarve : ∀ {ρ rs r} →
  HeldMode ρ rs → HeldEarlier ρ rs → HeldAny ρ rs →
  Any (_≡ r) rs → phaseR r ≡ held →
  Σ RRow (λ e →
    Any (_≡ e) rs × keyR e ≡ keyR r × phaseR e ≡ opened × Acc _<_ (indexR r))
noStarve {ρ} {r = r} hm he ha mr ph =
  let e , me , qk , op = noStarve-go {ρ} hm he ha mr ph (<-wellFounded (indexR r))
  in e , me , qk , op , <-wellFounded (indexR r)

------------------------------------------------------------------------
-- A release keeps `HeldEarlier`. On the released key a row left held
-- is still `earlierBlocked?`. On any other key the old witness has a
-- different id, so it is still in the list.
------------------------------------------------------------------------

release-earlier : ∀ {ρ rs id t} (r0 : RRow) →
  NoDupR rs → HeldEarlier ρ rs →
  Any (_≡ r0) rs → identR r0 ≡ id →
  HeldEarlier ρ (openAllR ρ (keyR r0) (removeR id rs) t (removeR id rs))
release-earlier {ρ} {rs} {id} {t} r0 nd he m0 idp heldRow mrow ph ρe
  with open-fromR mrow
... | s , ms , refl = onKey? (keyR s ≟ keyR r0)
  where
  gone = removeR id rs
  k0 = keyR r0
  eqo = proj₁ (openR-held-src ρ k0 gone t s ph)
  phs = proj₂ (openR-held-src ρ k0 gone t s ph)
  ms' = proj₁ (removeR-mem ms)
  ρs : ρ (kindR s) ≡ mearlier
  ρs = subst (λ z → ρ (kindR z) ≡ mearlier) eqo ρe
  keyW : ∀ e → keyR e ≡ keyR s →
         keyR (openOneR ρ k0 gone t e) ≡ keyR heldRow
  keyW e ek =
    trans (openR-key ρ k0 gone t e) (trans ek (sym (cong keyR eqo)))
  ixW : ∀ e → indexR e < indexR s →
        indexR (openOneR ρ k0 gone t e) < indexR heldRow
  ixW e ei =
    subst (λ z → z < indexR heldRow) (sym (openR-index ρ k0 gone t e))
      (subst (λ z → indexR e < z) (sym (cong indexR eqo)) ei)
  onKey? : Dec (keyR s ≡ keyR r0) →
           Σ RRow (λ e →
             Any (_≡ e) (openAllR ρ k0 gone t gone) ×
             keyR e ≡ keyR heldRow × indexR e < indexR heldRow)
  onKey? (yes qk) =
    let rel = stillR-false ρ k0 gone t s ph
        tb = opens-false-earlier ρ k0 gone s rel qk phs ρs
        e , me , ek , ei = earlier-sound gone (keyR s) (indexR s) tb
    in openOneR ρ k0 gone t e , open-keepR me , keyW e ek , ixW e ei
  onKey? (no ¬qk) =
    let e , me , ek , ei = he s ms' phs ρs
        ne : identR e ≢ id
        ne eqid =
          ¬qk (trans (sym ek)
                 (cong keyR (nodupR-eq nd me m0 (trans eqid (sym idp)))))
    in openOneR ρ k0 gone t e , open-keepR (removeR-keep me ne) , keyW e ek , ixW e ei

whyHeld : ∀ {ρ rs id t} (r0 s : RRow) →
  keyR s ≡ keyR r0 → phaseR (openOneR ρ (keyR r0) (removeR id rs) t s) ≡ held →
  ρ (kindR (openOneR ρ (keyR r0) (removeR id rs) t s)) ≡ many →
  T (anyBlocked? (removeR id rs) (keyR r0)) ⊎
  T (hasEarlierCand ρ (keyR r0) (removeR id rs) (removeR id rs)) ⊎
  T (smallerAny? ρ (removeR id rs) s)
whyHeld {ρ} {rs} {id} {t} r0 s qk ph ρa =
  let gone = removeR id rs
      k0 = keyR r0
      eqo = proj₁ (openR-held-src ρ k0 gone t s ph)
      phs = proj₂ (openR-held-src ρ k0 gone t s ph)
      ρs = subst (λ z → ρ (kindR z) ≡ many) eqo ρa
      rel = stillR-false ρ k0 gone t s ph
  in opens-false-any ρ k0 gone s rel qk phs ρs

-- A release keeps `HeldAny`. A held `many` row of the released key is
-- unopened for one of three reasons, and each reason supplies an opened
-- row of that key: an opened blocker, an unblocked `mearlier` row that
-- this release stamps, or a smaller `many` row. The last case descends
-- on the creation index. A held `many` row of another key keeps the
-- opened row it already had.
any-post-go : ∀ {ρ rs id t} (r0 : RRow) →
  NoDupR rs → NoDupIxR rs → HeldAny ρ rs →
  Any (_≡ r0) rs → identR r0 ≡ id →
  ∀ h → Any (_≡ h) (openAllR ρ (keyR r0) (removeR id rs) t (removeR id rs)) →
  phaseR h ≡ held → ρ (kindR h) ≡ many → keyR h ≡ keyR r0 →
  Acc _<_ (indexR h) →
  Σ RRow (λ e →
    Any (_≡ e) (openAllR ρ (keyR r0) (removeR id rs) t (removeR id rs)) ×
    keyR e ≡ keyR h × phaseR e ≡ opened)
any-post-go {ρ} {rs} {id} {t} r0 nd ix ha m0 idp h mh ph ρa qh (acc rec)
  with open-fromR mh
... | s , ms , refl with
  whyHeld {ρ} {rs} {id} {t} r0 s
    (trans (sym (openR-key ρ (keyR r0) (removeR id rs) t s)) qh) ph ρa
... | inj₁ blocked =
  let gone = removeR id rs
      k0 = keyR r0
      eqo = proj₁ (openR-held-src ρ k0 gone t s ph)
      w , mw , qkw , opw = any-sound gone k0 blocked
      stays = openR-id ρ k0 gone t w (opens-opened ρ k0 gone w opw)
  in openOneR ρ k0 gone t w , open-keepR mw
   , trans (cong keyR stays) (trans qkw (sym qh))
   , trans (cong phaseR stays) opw
... | inj₂ (inj₁ cand) =
  let gone = removeR id rs
      k0 = keyR r0
      eqo = proj₁ (openR-held-src ρ k0 gone t s ph)
      c , mc , qkc , hdc , mdc , nbc = hasEarlierCand-sound ρ k0 gone gone cand
      ρc = earlier-only (ρ (kindR c)) mdc
      phc = heldR→phase c hdc
      openedC =
        opens-earlier ρ k0 gone c qkc phc ρc nbc
      stamped = openR-stamp ρ k0 gone t c openedC
  in openOneR ρ k0 gone t c , open-keepR mc
   , trans (cong keyR stamped) (trans (stampR-key t c) (trans qkc (sym qh)))
   , trans (cong phaseR stamped) (stampR-phase t c)
... | inj₂ (inj₂ smaller) with smallerAny-sound ρ (removeR id rs) s smaller
... | c , mc , qkc , hdc , mac , bfc with phase? (phaseR (openOneR ρ (keyR r0) (removeR id rs) t c))
... | inj₁ opc =
  let gone = removeR id rs
      k0 = keyR r0
      eqo = proj₁ (openR-held-src ρ k0 gone t s ph)
  in openOneR ρ k0 gone t c , open-keepR mc
   , trans (openR-key ρ k0 gone t c) (trans qkc (sym (cong keyR eqo)))
   , opc
... | inj₂ hdc2 =
  let gone = removeR id rs
      k0 = keyR r0
      eqo = proj₁ (openR-held-src ρ k0 gone t s ph)
      ixG = nodupIxR-remove {id} ix
      lt = before-smaller ixG mc ms qkc bfc
      img = openOneR ρ k0 gone t c
      ixRec : indexR img < indexR h
      ixRec =
        subst (λ z → z < indexR h) (sym (openR-index ρ k0 gone t c))
          (subst (λ z → indexR c < z) (sym (cong indexR eqo)) lt)
      ρc = any-only (ρ (kindR c)) mac
      ρImg = subst (λ z → ρ z ≡ many) (sym (openR-kind ρ k0 gone t c)) ρc
      qImg =
        trans (trans (openR-key ρ k0 gone t c) (trans qkc (sym (cong keyR eqo)))) qh
      w , mw , qkw , opw =
        any-post-go {ρ} r0 nd ix ha m0 idp img (open-keepR mc) hdc2 ρImg qImg
          (rec {y = indexR img} ixRec)
  in w , mw
   , trans qkw (trans (openR-key ρ k0 gone t c) (trans qkc (sym (cong keyR eqo))))
   , opw

any-post : ∀ {ρ rs id t} (r0 : RRow) →
  NoDupR rs → NoDupIxR rs → HeldAny ρ rs →
  Any (_≡ r0) rs → identR r0 ≡ id →
  HeldAny ρ (openAllR ρ (keyR r0) (removeR id rs) t (removeR id rs))
any-post {ρ} {rs} {id} {t} r0 nd ix ha m0 idp h mh ph ρa with open-fromR mh
... | s , ms , refl = choose (keyR s ≟ keyR r0)
  where
  gone = removeR id rs
  k0 = keyR r0
  eqo = proj₁ (openR-held-src ρ k0 gone t s ph)
  phs = proj₂ (openR-held-src ρ k0 gone t s ph)
  ρs = subst (λ z → ρ (kindR z) ≡ many) eqo ρa
  ms' = proj₁ (removeR-mem ms)
  choose : Dec (keyR s ≡ keyR r0) →
           Σ RRow (λ e →
             Any (_≡ e) (openAllR ρ k0 gone t gone) ×
             keyR e ≡ keyR h × phaseR e ≡ opened)
  choose (yes qk) =
    any-post-go {ρ} r0 nd ix ha m0 idp h mh ph ρa
      (trans (openR-key ρ k0 gone t s) qk) (<-wellFounded (indexR h))
  choose (no ¬qk) =
    let w , mw , qkw , opw = ha s ms' phs ρs
        ne : identR w ≢ id
        ne eqid =
          ¬qk (trans (sym qkw)
                 (cong keyR (nodupR-eq nd mw m0 (trans eqid (sym idp)))))
        stable = openR-stable ρ k0 gone t w (λ eq → ¬qk (trans (sym qkw) eq))
    in openOneR ρ k0 gone t w , open-keepR (removeR-keep mw ne)
     , trans (cong keyR stable) (trans qkw (sym (cong keyR eqo)))
     , trans (cong phaseR stable) opw

-- At most one opened `many` row of a key. A row that opens was not
-- `anyBlocked?`, so no opened row of its key was already there, and it
-- was not behind another unblocked `many` row.
open-at-most : ∀ {ρ k t rs} →
  NoDupIxR rs → AtMostOne ρ rs →
  AtMostOne ρ (openAllR ρ k rs t rs)
open-at-most {ρ} {k} {t} {rs} ix one r e mr me qk opr ope ρr ρe
  with open-fromR mr | open-fromR me
... | s , ms , refl | u , mu , refl = both (opens? ρ k rs s) (opens? ρ k rs u) refl refl
  where
  qks : keyR u ≡ keyR s
  qks = trans (sym (openR-key ρ k rs t u)) (trans qk (openR-key ρ k rs t s))
  ρs : ρ (kindR s) ≡ many
  ρs = subst (λ z → ρ z ≡ many) (openR-kind ρ k rs t s) ρr
  ρu : ρ (kindR u) ≡ many
  ρu = subst (λ z → ρ z ≡ many) (openR-kind ρ k rs t u) ρe
  id-of : identR s ≡ identR u →
          identR (openOneR ρ k rs t s) ≡ identR (openOneR ρ k rs t u)
  id-of eqi =
    trans (openR-ident ρ k rs t s)
      (trans eqi (sym (openR-ident ρ k rs t u)))
  both : ∀ bs bu → opens? ρ k rs s ≡ bs → opens? ρ k rs u ≡ bu →
         identR (openOneR ρ k rs t s) ≡ identR (openOneR ρ k rs t u)
  both false false eqs equ =
    let ops = trans (sym (openR-phase-stay ρ k rs t s eqs)) opr
        opu = trans (sym (openR-phase-stay ρ k rs t u equ)) ope
    in id-of (one s u ms mu qks ops opu ρs ρu)
  both true false eqs equ =
    let opu = trans (sym (openR-phase-stay ρ k rs t u equ)) ope
        clr = opens-clear-any ρ k rs s eqs ρs
        tb = any-complete rs (keyR s) u mu qks opu
    in ⊥-elim (true≢false (trans (sym (T→≡ tb)) clr))
  both false true eqs equ =
    let ops = trans (sym (openR-phase-stay ρ k rs t s eqs)) opr
        clr = opens-clear-any ρ k rs u equ ρu
        tb = any-complete rs (keyR u) s ms (sym qks) ops
    in ⊥-elim (true≢false (trans (sym (T→≡ tb)) clr))
  both true true eqs equ = order (indexR u <? indexR s)
    where
    phu = opens-was-held ρ k rs u equ
    order : Dec (indexR u < indexR s) →
            identR (openOneR ρ k rs t s) ≡ identR (openOneR ρ k rs t u)
    order (yes lt) =
      ⊥-elim (true≢false
        (trans
          (sym (T→≡ (smallerAny-complete ρ rs s u mu qks
                      (held-bitR u phu) (modeAny-yes ρ u ρu) (before-lt u s lt))))
          (opens-clear-smaller ρ k rs s eqs ρs)))
    order (no ¬lt) = order2 (indexR s <? indexR u)
      where
      phs = opens-was-held ρ k rs s eqs
      order2 : Dec (indexR s < indexR u) →
               identR (openOneR ρ k rs t s) ≡ identR (openOneR ρ k rs t u)
      order2 (yes lt) =
        ⊥-elim (true≢false
          (trans
            (sym (T→≡ (smallerAny-complete ρ rs u s ms (sym qks)
                        (held-bitR s phs) (modeAny-yes ρ s ρs) (before-lt s u lt))))
            (opens-clear-smaller ρ k rs u equ ρu)))
      order2 (no ¬lt2) =
        let qix = ≤-antisym (≮⇒≥ ¬lt2) (≮⇒≥ ¬lt)
        in id-of (cong identR (nodupIxR-eq ix ms mu (sym qks) (sym qix)))

releaseR-go : ∀ {ρ n t rs id} {r0 : RRow} →
  RulesInv ρ (rst n t rs) →
  Any (_≡ r0) rs → identR r0 ≡ id →
  RulesInv ρ (rst n (suc t)
    (openAllR ρ (keyR r0) (removeR id rs) t (removeR id rs)))
releaseR-go {ρ} {n} {t} {rs} {id} {r0} inv m0 idp =
  let gone = removeR id rs
      k0 = keyR r0
  in rinv
       (nodupR-open {ρ} {k0} {gone} {t} (nodupR-remove {id} (rids inv)))
       (nodupIxR-open {ρ} {k0} {gone} {t} (nodupIxR-remove {id} (rixs inv)))
       (belowR-open {n} {ρ} {k0} {gone} {t} (belowR-remove {n} {id} (rbelow inv)))
       (clockR-open {ρ} {k0} {gone} {t} (clockR-remove {t} {id} (rclock inv)))
       (heldMode-open {ρ} {k0} {gone} {t} (heldMode-remove {ρ} {id} (rheld inv)))
       (release-earlier {ρ} {rs} {id} {t} r0 (rids inv) (rearlier inv) m0 idp)
       (any-post {ρ} {rs} {id} {t} r0 (rids inv) (rixs inv) (rany inv) m0 idp)
       (open-at-most {ρ} {k0} {t} {gone}
          (nodupIxR-remove {id} (rixs inv)) (one-remove {ρ} {id} (rone inv)))
       (open-noR {ρ} {k0} {t} {gone} (over-remove {ρ} {id} (rover inv)))
       (open-resolved {ρ} {k0} {t} {gone} (resolved-remove {ρ} {id} (rresolved inv)))

findR-mem : ∀ {rs id r} → findR id rs ≡ just r → Any (_≡ r) rs × identR r ≡ id
findR-mem {[]} ()
findR-mem {x ∷ rs} {id} {r} eq with identR x ≟ id
findR-mem {x ∷ rs} {id} {r} eq | yes p =
  here (just-inj eq) , trans (cong identR (sym (just-inj eq))) p
findR-mem {x ∷ rs} {id} {r} eq | no _ =
  let m , ip = findR-mem eq in there m , ip

arriveM-pres : ∀ {ρ n t rs k kd i s'} →
  RulesInv ρ (rst n t rs) →
  arriveMode ρ (rst n t rs) k kd i ≡ just s' →
  RulesInv ρ s'
arriveM-pres {ρ} {n} {t} {rs} {k} {kd} {i} inv eq with freshR? rs k i in fr
... | false = ⊥-elim (nothing≢just eq)
... | true =
  subst (RulesInv ρ) (just-inj eq) (arriveR-inv {ρ} inv (subst T (sym fr) tt))

resolveM-pres : ∀ {ρ n t rs id s'} →
  RulesInv ρ (rst n t rs) →
  resolveMode ρ (rst n t rs) id ≡ just s' →
  RulesInv ρ s'
resolveM-pres {ρ} {n} {t} {rs} {id} inv eq with findR id rs in feq
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseR r
... | held = ⊥-elim (nothing≢just eq)
... | opened =
  let m , idp = findR-mem feq
  in subst (RulesInv ρ) (just-inj eq) (releaseR-go {ρ} inv m idp)

withdrawM-pres : ∀ {ρ n t rs id s'} →
  RulesInv ρ (rst n t rs) →
  withdrawTo ρ (rst n t rs) id ≡ just s' →
  RulesInv ρ s'
withdrawM-pres {ρ} {n} {t} {rs} {id} inv eq with findR id rs in feq
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseR r
... | opened = ⊥-elim (nothing≢just eq)
... | held =
  let m , idp = findR-mem feq
  in subst (RulesInv ρ) (just-inj eq) (releaseR-go {ρ} inv m idp)

touchM-pres : ∀ {ρ n t rs id s'} →
  RulesInv ρ (rst n t rs) →
  touchMode (rst n t rs) id ≡ just s' →
  RulesInv ρ s'
touchM-pres {ρ} {rs = rs} {id = id} inv eq with findR id rs
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseR r
... | held = ⊥-elim (nothing≢just eq)
... | opened = subst (RulesInv ρ) (just-inj eq) inv

-- Every accepted step preserves `RulesInv`, at any number of keys,
-- kinds, and instances. `withdrawR` is the held case of the same release
-- as `resolveR`.
rules-step : ∀ {ρ s a s'} → RulesInv ρ s → applyMode ρ s a ≡ just s' → RulesInv ρ s'
rules-step {ρ} {rst _ _ _} {arriveR k i kd} inv eq = arriveM-pres {ρ} inv eq
rules-step {ρ} {rst _ _ _} {resolveR id} inv eq = resolveM-pres {ρ} inv eq
rules-step {ρ} {rst _ _ _} {withdrawR id} inv eq = withdrawM-pres {ρ} inv eq
rules-step {ρ} {rst _ _ _} {rerunR id} inv eq = touchM-pres {ρ} inv eq
rules-step {ρ} {rst _ _ _} {meetR id} inv eq = touchM-pres {ρ} inv eq

------------------------------------------------------------------------
-- Key independence. `decideMode` reads `onKeyR` only. A release on one
-- key does not change the rows of another key. `withdrawTo` is the same
-- release as `resolveMode`.
------------------------------------------------------------------------

onKeyR-yes : ∀ r rs k → keyR r ≡ k → onKeyR k (r ∷ rs) ≡ r ∷ onKeyR k rs
onKeyR-yes r rs k eq with keyR r ≟ k
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p eq)

onKeyR-no : ∀ r rs k → keyR r ≢ k → onKeyR k (r ∷ rs) ≡ onKeyR k rs
onKeyR-no r rs k ¬k with keyR r ≟ k
... | yes eq = ⊥-elim (¬k eq)
... | no _ = refl

onKeyR-keep : ∀ {k rs r} → Any (_≡ r) rs → keyR r ≡ k → Any (_≡ r) (onKeyR k rs)
onKeyR-keep {k} {r ∷ rs} m qk with keyR r ≟ k
... | yes _ with m
... | here refl = here refl
... | there mt = there (onKeyR-keep mt qk)
onKeyR-keep {k} {r ∷ rs} m qk | no ¬k with m
... | here refl = ⊥-elim (¬k qk)
... | there mt = onKeyR-keep mt qk

onKeyR-lift : ∀ {k rs r} → Any (_≡ r) (onKeyR k rs) → Any (_≡ r) rs
onKeyR-lift {k} {r ∷ rs} m with keyR r ≟ k
... | yes _ with m
... | here refl = here refl
... | there mt = there (onKeyR-lift mt)
onKeyR-lift {k} {r ∷ rs} m | no _ = there (onKeyR-lift m)

onKeyR-eq : ∀ {k k' rs} → k ≡ k' → onKeyR k rs ≡ onKeyR k' rs
onKeyR-eq refl = refl

earlierBlocked?-onKey : ∀ rs k i →
  earlierBlocked? rs k i ≡ earlierBlocked? (onKeyR k rs) k i
earlierBlocked?-onKey rs k i =
  bool≡
    (λ tb →
      let e , m , qk , qi = earlier-sound rs k i tb
      in earlier-complete (onKeyR k rs) k i e (onKeyR-keep m qk) qk qi)
    (λ tb →
      let e , m , qk , qi = earlier-sound (onKeyR k rs) k i tb
      in earlier-complete rs k i e (onKeyR-lift m) qk qi)

anyBlocked?-onKey : ∀ rs k → anyBlocked? rs k ≡ anyBlocked? (onKeyR k rs) k
anyBlocked?-onKey rs k =
  bool≡
    (λ tb →
      let e , m , qk , op = any-sound rs k tb
      in any-complete (onKeyR k rs) k e (onKeyR-keep m qk) qk op)
    (λ tb →
      let e , m , qk , op = any-sound (onKeyR k rs) k tb
      in any-complete rs k e (onKeyR-lift m) qk op)

decideMode-key : ∀ ρ rs k i kd →
  decideMode ρ rs k i kd ≡ decideMode ρ (onKeyR k rs) k i kd
decideMode-key ρ rs k i kd with ρ kd
... | mnever = refl
... | mearlier = cong phaseOfBlocked (earlierBlocked?-onKey rs k i)
... | many = cong phaseOfBlocked (anyBlocked?-onKey rs k)

onKeyR-remove-other : ∀ {id k rs} →
  NoDupR rs →
  (∀ r → Any (_≡ r) rs → identR r ≡ id → keyR r ≢ k) →
  onKeyR k (removeR id rs) ≡ onKeyR k rs
onKeyR-remove-other {id} {k} {[]} _ _ = refl
onKeyR-remove-other {id} {k} {x ∷ rs} (drmore _ nd) hyp with identR x ≟ id
... | yes p =
  trans (onKeyR-remove-other nd (λ r m eq → hyp r (there m) eq))
        (sym (onKeyR-no x rs k (hyp x (here refl) p)))
... | no _ with keyR x ≟ k
... | yes _ =
  cong (x ∷_) (onKeyR-remove-other nd (λ r m eq → hyp r (there m) eq))
... | no _ =
  onKeyR-remove-other nd (λ r m eq → hyp r (there m) eq)

onKeyR-openAll-other : ∀ {ρ k' k all t rs} → k' ≢ k →
  onKeyR k (openAllR ρ k' all t rs) ≡ onKeyR k rs
onKeyR-openAll-other {rs = []} _ = refl
onKeyR-openAll-other {ρ} {k'} {k} {all} {t} {r ∷ rs} ¬eq = side (keyR r ≟ k)
  where
  head = openOneR ρ k' all t r
  tail = openAllR ρ k' all t rs
  side : Dec (keyR r ≡ k) → onKeyR k (head ∷ tail) ≡ onKeyR k (r ∷ rs)
  side (yes qk) =
    let kop = trans (openR-key ρ k' all t r) qk
        stable = openR-stable ρ k' all t r (λ z → ¬eq (sym (trans (sym qk) z)))
        ih = onKeyR-openAll-other {ρ} {k'} {k} {all} {t} {rs} ¬eq
    in trans (onKeyR-yes head tail k kop)
         (trans (cong (λ z → z ∷ onKeyR k tail) stable)
           (trans (cong (r ∷_) ih)
                  (sym (onKeyR-yes r rs k qk))))
  side (no ¬k) =
    trans (onKeyR-no head tail k (λ z → ¬k (trans (sym (openR-key ρ k' all t r)) z)))
          (trans (onKeyR-openAll-other {ρ} {k'} {k} {all} {t} {rs} ¬eq)
                 (sym (onKeyR-no r rs k ¬k)))

release-rows-other : ∀ {ρ rs id t k} (r0 : RRow) →
  NoDupR rs → Any (_≡ r0) rs → identR r0 ≡ id → keyR r0 ≢ k →
  onKeyR k (openAllR ρ (keyR r0) (removeR id rs) t (removeR id rs)) ≡ onKeyR k rs
release-rows-other {ρ} {rs} {id} {t} {k} r0 nd m0 idp ¬k =
  let gone = removeR id rs
  in trans (onKeyR-openAll-other {ρ} {keyR r0} {k} {gone} {t} {gone} ¬k)
           (onKeyR-remove-other {id} {k} {rs} nd
              (λ r m eq qkr →
                 ¬k (trans (sym (cong keyR (nodupR-eq nd m m0 (trans eq (sym idp))))) qkr)))

-- The remove hypothesis: a row of key k is not the removed id, because
-- the removed row's key is not k. `nodupR-eq` above uses that.
arriveM-other : ∀ {ρ k' k i n t kd rs} → k' ≢ k →
  onKeyR k (rr k' i n t t kd (decideMode ρ rs k' i kd) ∷ rs) ≡ onKeyR k rs
arriveM-other {ρ} {k'} {k} {i} {n} {t} {kd} {rs} ¬eq =
  onKeyR-no (rr k' i n t t kd (decideMode ρ rs k' i kd)) rs k ¬eq

resolveM-other : ∀ {ρ n t rs id k s'} →
  RulesInv ρ (rst n t rs) →
  resolveMode ρ (rst n t rs) id ≡ just s' →
  (∀ r → Any (_≡ r) rs → identR r ≡ id → keyR r ≢ k) →
  onKeyR k (rowsR s') ≡ onKeyR k rs
resolveM-other {ρ} {n} {t} {rs} {id} {k} inv eq hyp with findR id rs in feq
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseR r
... | held = ⊥-elim (nothing≢just eq)
... | opened =
  let m , idp = findR-mem feq
      gone = removeR id rs
      rowsEq = cong rowsR (just-inj eq)
      same = onKeyR-openAll-other {ρ} {keyR r} {k} {gone} {t} {gone} (hyp r m idp)
      drop = onKeyR-remove-other {id} {k} {rs} (rids inv) hyp
  in trans (sym (cong (onKeyR k) rowsEq)) (trans same drop)

withdrawM-other : ∀ {ρ n t rs id k s'} →
  RulesInv ρ (rst n t rs) →
  withdrawTo ρ (rst n t rs) id ≡ just s' →
  (∀ r → Any (_≡ r) rs → identR r ≡ id → keyR r ≢ k) →
  onKeyR k (rowsR s') ≡ onKeyR k rs
withdrawM-other {ρ} {n} {t} {rs} {id} {k} inv eq hyp with findR id rs in feq
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseR r
... | opened = ⊥-elim (nothing≢just eq)
... | held =
  let m , idp = findR-mem feq
      gone = removeR id rs
      rowsEq = cong rowsR (just-inj eq)
      same = onKeyR-openAll-other {ρ} {keyR r} {k} {gone} {t} {gone} (hyp r m idp)
      drop = onKeyR-remove-other {id} {k} {rs} (rids inv) hyp
  in trans (sym (cong (onKeyR k) rowsEq)) (trans same drop)

touchM-other : ∀ {n t rs id s'} →
  touchMode (rst n t rs) id ≡ just s' → rowsR s' ≡ rs
touchM-other {rs = rs} {id = id} eq with findR id rs
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseR r
... | held = ⊥-elim (nothing≢just eq)
... | opened = sym (cong rowsR (just-inj eq))

------------------------------------------------------------------------
-- Progress. Every held row has an opened row of its key (`noStarve`).
-- Resolving that opened row shortens the key by one, and the held row's
-- id is still live: it opened, or it is still held. The host is not
-- obliged to take that step. A later `mnever` arrival can open beside
-- the waiter, so this is not a bound on traces that keep arriving.
-- On a key whose held rows are all `mearlier`, the least earlier row
-- is opened. That is the stronger fact, and it needs the extra premise.
------------------------------------------------------------------------

Absent : ℕ → List RRow → Set
Absent id rs = ∀ r → Any (_≡ r) rs → identR r ≢ id

remove-absent : ∀ {id rs} → NoDupR rs → Absent id rs → removeR id rs ≡ rs
remove-absent {id} {[]} _ _ = refl
remove-absent {id} {r ∷ rs} (drmore _ nd) abs with identR r ≟ id
... | yes eq = ⊥-elim (abs r (here refl) eq)
... | no _ = cong (r ∷_) (remove-absent nd (λ e m → abs e (there m)))

removed-absent : ∀ {id rs} → Absent id (removeR id rs)
removed-absent {id} {rs} e m = proj₂ (removeR-mem {rs} {e} {id} m)

absent-remove : ∀ {id id' rs} → Absent id rs → Absent id (removeR id' rs)
absent-remove abs e m = abs e (proj₁ (removeR-mem m))

absent-open : ∀ {ρ k all t id rs} → Absent id rs →
              Absent id (openAllR ρ k all t rs)
absent-open {ρ} {k} {all} {t} abs e m eqid =
  let s , ms , eq = open-fromR m
  in abs s ms
       (trans (sym (trans (cong identR eq) (openR-ident ρ k all t s))) eqid)

absent-cons : ∀ {id r rs} → identR r ≢ id → Absent id rs → Absent id (r ∷ rs)
absent-cons ne _ _ (here refl) = ne
absent-cons _ abs e (there m) = abs e m

len-onKey-remove : ∀ {rs r} → NoDupR rs → Any (_≡ r) rs →
  len (onKeyR (keyR r) rs) ≡ suc (len (onKeyR (keyR r) (removeR (identR r) rs)))
len-onKey-remove {[]} _ ()
len-onKey-remove {r ∷ rs} (drmore sep nd) (here refl) with identR r ≟ identR r
... | yes _ with keyR r ≟ keyR r
... | yes _ =
  sym (cong suc
        (cong (λ zs → len (onKeyR (keyR r) zs))
              (remove-absent nd sep)))
... | no ¬k = ⊥-elim (¬k refl)
len-onKey-remove {r ∷ rs} (drmore _ _) (here refl) | no ¬id = ⊥-elim (¬id refl)
len-onKey-remove {x ∷ rs} {r} (drmore sep nd) (there m) with identR x ≟ identR r
... | yes eq = ⊥-elim (sep r m (sym eq))
... | no _ with keyR x ≟ keyR r
... | yes _ = cong suc (len-onKey-remove nd m)
... | no _ = len-onKey-remove nd m

len-openAll : ∀ ρ k' k all t rs →
  len (onKeyR k (openAllR ρ k' all t rs)) ≡ len (onKeyR k rs)
len-openAll ρ k' k all t [] = refl
len-openAll ρ k' k all t (r ∷ rs) with keyR r ≟ k
... | yes qk =
  trans (cong len (onKeyR-yes (openOneR ρ k' all t r) (openAllR ρ k' all t rs) k
                    (trans (openR-key ρ k' all t r) qk)))
        (cong suc (len-openAll ρ k' k all t rs))
... | no ¬k =
  trans (cong len (onKeyR-no (openOneR ρ k' all t r) (openAllR ρ k' all t rs) k
                    (λ eq → ¬k (trans (sym (openR-key ρ k' all t r)) eq))))
        (len-openAll ρ k' k all t rs)

findR-hit : ∀ {rs r} → NoDupR rs → Any (_≡ r) rs → findR (identR r) rs ≡ just r
findR-hit {[]} _ ()
findR-hit {x ∷ rs} {r} (drmore sep nd) m with identR x ≟ identR r
findR-hit {x ∷ rs} {r} (drmore sep nd) (here refl) | yes _ = refl
findR-hit {x ∷ rs} {r} (drmore sep nd) (here refl) | no ¬eq = ⊥-elim (¬eq refl)
findR-hit {x ∷ rs} {r} (drmore sep nd) (there m) | yes eq = ⊥-elim (sep r m (sym eq))
findR-hit {x ∷ rs} {r} (drmore sep nd) (there m) | no _ = findR-hit nd m

resolve-open : ∀ {ρ n t rs e} →
  NoDupR rs → Any (_≡ e) rs → phaseR e ≡ opened →
  resolveMode ρ (rst n t rs) (identR e) ≡
    just (rst n (suc t)
      (openAllR ρ (keyR e) (removeR (identR e) rs) t (removeR (identR e) rs)))
resolve-open {ρ} {n} {t} {rs} {e} nd me op with findR (identR e) rs | findR-hit nd me
... | just .e | refl with phaseR e | op
... | opened | refl = refl
... | held | ()

anyProgress : ∀ {ρ n t rs r} →
  RulesInv ρ (rst n t rs) →
  Any (_≡ r) rs → phaseR r ≡ held →
  Σ RRow (λ e → Σ RState (λ s' →
    Any (_≡ e) rs × keyR e ≡ keyR r × phaseR e ≡ opened ×
    resolveMode ρ (rst n t rs) (identR e) ≡ just s' ×
    len (onKeyR (keyR r) rs) ≡ suc (len (onKeyR (keyR r) (rowsR s'))) ×
    Σ RRow (λ r' → Any (_≡ r') (rowsR s') × identR r' ≡ identR r)))
anyProgress {ρ} {n} {t} {rs} {r} inv mr ph =
  let e , me , qk , op , _ =
        noStarve {ρ} (rheld inv) (rearlier inv) (rany inv) mr ph
      diff : identR r ≢ identR e
      diff eqid =
        opened≢held
          (trans (sym op)
             (trans (sym (cong phaseR (nodupR-eq (rids inv) mr me eqid))) ph))
      gone = removeR (identR e) rs
      openedRows = openAllR ρ (keyR e) gone t gone
      s' = rst n (suc t) openedRows
      step = resolve-open {ρ} {n} {t} {rs} {e} (rids inv) me op
      shorter =
        trans (cong len (onKeyR-eq {keyR r} {keyR e} {rs} (sym qk)))
          (trans (len-onKey-remove {rs} {e} (rids inv) me)
            (trans (cong suc (sym (len-openAll ρ (keyR e) (keyR e) gone t gone)))
              (trans (cong suc (cong len (onKeyR-eq {keyR e} {keyR r} {openedRows} qk)))
                     (refl {x = suc (len (onKeyR (keyR r) openedRows))}))))
      r' = openOneR ρ (keyR e) gone t r
      mem = open-keepR {ρ} {keyR e} {gone} {t} {gone}
              (removeR-keep {rs} {r} {identR e} mr diff)
  in e , s' , me , qk , op , step , shorter , (r' , mem , openR-ident ρ (keyR e) gone t r)

-- The shorter proof above chains four equalities onto
-- `len (onKey (keyR r) rs) ≡ suc (len (onKey (keyR r) openedRows))`,
-- and `rowsR s'` is `openedRows`. `refl` at the end is that last step.

onlyEarlier-open : ∀ {ρ rs k i e} →
  HeldEarlier ρ rs →
  (∀ x → Any (_≡ x) rs → keyR x ≡ k → phaseR x ≡ held → ρ (kindR x) ≡ mearlier) →
  Any (_≡ e) rs → keyR e ≡ k → indexR e < i →
  (∀ e' → Any (_≡ e') rs → keyR e' ≡ k → indexR e' < i → indexR e ≤ indexR e') →
  phaseR e ≡ opened
onlyEarlier-open {ρ} {rs} {k} {i} {e} he only me qk ix least with phase? (phaseR e)
... | inj₁ op = op
... | inj₂ hd =
  let ρe = only e me qk hd
      w , mw , qkw , qw = he e me hd ρe
  in ⊥-elim (<⇒≱ qw (least w mw (trans qkw qk) (<-trans qw ix)))

------------------------------------------------------------------------
-- `EarlierResolved` for `mearlier` and for `many`. It does not hold for
-- `mnever`: an opened `mnever` row can sit beside an earlier live row.
-- `ee` is two `mearlier` kinds. `mix` is `mearlier` beside `many`.
------------------------------------------------------------------------

rules-resolved : ∀ {ρ rs k kd} →
  NoOvertakeR ρ rs → ResolvedAny ρ rs →
  (ρ kd ≡ mearlier ⊎ ρ kd ≡ many) →
  EarlierResolved rs k kd
rules-resolved {ρ} noO _ (inj₁ ρe) r e mr me qkr kdr qke _ op ix bq =
  noO r e mr me (subst (λ z → ρ z ≡ mearlier) (sym kdr) ρe) op
      (trans qke (sym qkr)) ix bq
rules-resolved {ρ} _ old (inj₂ ρa) r e mr me qkr kdr qke kde op ix bq =
  old r e mr me (subst (λ z → ρ z ≡ many) (sym kdr) ρa) op
      (trans kde (sym kdr)) (trans qke (sym qkr)) ix bq

inv-resolved : ∀ {ρ s k kd} → RulesInv ρ s →
  (ρ kd ≡ mearlier ⊎ ρ kd ≡ many) →
  EarlierResolved (rowsR s) k kd
inv-resolved inv m = rules-resolved (rover inv) (rresolved inv) m

ee : Rules
ee zero = mearlier
ee (suc zero) = mearlier
ee (suc (suc _)) = mnever

mix : Rules
mix zero = mearlier
mix (suc zero) = many
mix (suc (suc _)) = mnever

ee-resolved : ∀ {s k kd} → RulesInv ee s → ee kd ≡ mearlier →
  EarlierResolved (rowsR s) k kd
ee-resolved inv eq = inv-resolved inv (inj₁ eq)

mix-earlier : ∀ {s k} → RulesInv mix s → EarlierResolved (rowsR s) k zero
mix-earlier inv = inv-resolved inv (inj₁ refl)

mix-any : ∀ {s k} → RulesInv mix s → EarlierResolved (rowsR s) k (suc zero)
mix-any inv = inv-resolved inv (inj₂ refl)

------------------------------------------------------------------------
-- `withdrawTo` drops a held id. The id stays below `next` and out of
-- the rows, so it is not issued again and it is not a later blocker.
-- `decideMode` after removing an already absent id is the old decision.
------------------------------------------------------------------------

record Gone (id : ℕ) (s : RState) : Set where
  constructor mkGone
  field
    past : id < nextR s
    away : Absent id (rowsR s)

open Gone

gone-step : ∀ {ρ id s a s'} → Gone id s → applyMode ρ s a ≡ just s' → Gone id s'
gone-step {ρ} {id} {rst n t rs} {arriveR k i kd} g eq with freshR? rs k i
... | false = ⊥-elim (nothing≢just eq)
... | true =
  subst (Gone id) (just-inj eq)
    (mkGone (m<n⇒m<1+n (past g))
            (absent-cons (λ eqid → <⇒≢ (past g) (sym eqid)) (away g)))
gone-step {ρ} {id} {rst n t rs} {resolveR j} g eq with findR j rs
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseR r
... | held = ⊥-elim (nothing≢just eq)
... | opened =
  let goneRows = removeR j rs
  in subst (Gone id) (just-inj eq)
       (mkGone (past g) (absent-open (absent-remove (away g))))
gone-step {ρ} {id} {rst n t rs} {withdrawR j} g eq with findR j rs
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseR r
... | opened = ⊥-elim (nothing≢just eq)
... | held =
  let goneRows = removeR j rs
  in subst (Gone id) (just-inj eq)
       (mkGone (past g) (absent-open (absent-remove (away g))))
gone-step {ρ} {id} {rst n t rs} {rerunR j} g eq with findR j rs
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseR r
... | held = ⊥-elim (nothing≢just eq)
... | opened = subst (Gone id) (just-inj eq) g
gone-step {ρ} {id} {rst n t rs} {meetR j} g eq with findR j rs
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseR r
... | held = ⊥-elim (nothing≢just eq)
... | opened = subst (Gone id) (just-inj eq) g

withdrawGone : ∀ {ρ n t rs id s'} →
  RulesInv ρ (rst n t rs) →
  withdrawTo ρ (rst n t rs) id ≡ just s' →
  Gone id s'
withdrawGone {ρ} {n} {t} {rs} {id} inv eq with findR id rs in feq
... | nothing = ⊥-elim (nothing≢just eq)
... | just r with phaseR r
... | opened = ⊥-elim (nothing≢just eq)
... | held =
  let m , idp = findR-mem feq
      below = subst (_< n) idp (belowR-at (rbelow inv) m)
      goneRows = removeR id rs
  in subst (Gone id) (just-inj eq)
       (mkGone below
          (absent-open {ρ} {keyR r} {goneRows} {t} {id} {goneRows}
             (removed-absent {id} {rs})))

decide-after-gone : ∀ ρ rs id k i kd → NoDupR rs → Absent id rs →
  decideMode ρ (removeR id rs) k i kd ≡ decideMode ρ rs k i kd
decide-after-gone ρ rs id k i kd nd abs =
  cong (λ zs → decideMode ρ zs k i kd) (remove-absent nd abs)

------------------------------------------------------------------------
-- A violation is two rows of one key. One row cannot be one. Three are
-- unnecessary. It renames onto `script-a` only when the opened row is
-- `mearlier` and the earlier row is `mnever` or `mearlier`. Two opened
-- `many` rows do not, and neither does a `mearlier` overtake whose
-- earlier row is `many`. Withdraw adds no third shape.
--
-- Not in this argument: the generator, the meeting steps, one retry
-- then give-up, `fail stop`, and the book atom `resolved k init`.
-- The family-graph state and transition counts are not a bound.
------------------------------------------------------------------------

data BadFamily (ρ : Rules) (rs : List RRow) : Set where
  bad-earlier : (r e : RRow) →
    Any (_≡ r) rs → Any (_≡ e) rs →
    ρ (kindR r) ≡ mearlier → phaseR r ≡ opened →
    keyR e ≡ keyR r → indexR e < indexR r → bornR e ≤ openedAtR r →
    BadFamily ρ rs
  bad-any : (r e : RRow) →
    Any (_≡ r) rs → Any (_≡ e) rs →
    keyR e ≡ keyR r → phaseR r ≡ opened → phaseR e ≡ opened →
    ρ (kindR r) ≡ many → ρ (kindR e) ≡ many → identR r ≢ identR e →
    BadFamily ρ rs

g-no-bad : ∀ {ρ s} → RulesInv ρ s → ¬ BadFamily ρ (rowsR s)
g-no-bad inv (bad-earlier r e mr me ρr op qk ix bq) =
  rover inv r e mr me ρr op qk ix bq
g-no-bad inv (bad-any r e mr me qk opr ope ρr ρe ¬eq) =
  ¬eq (rone inv r e mr me qk opr ope ρr ρe)

cutoffTwo : ∀ {ρ rs} → BadFamily ρ rs →
  Σ RRow (λ r → Σ RRow (λ e → BadFamily ρ (r ∷ e ∷ [])))
cutoffTwo (bad-earlier r e _ _ ρr op qk ix bq) =
  r , e , bad-earlier r e (here refl) (there (here refl)) ρr op qk ix bq
cutoffTwo (bad-any r e _ _ qk opr ope ρr ρe ¬eq) =
  r , e , bad-any r e (here refl) (there (here refl)) qk opr ope ρr ρe ¬eq

cutoff-one : ∀ {ρ r} → ¬ BadFamily ρ (r ∷ [])
cutoff-one (bad-earlier r e (here refl) (here refl) _ _ _ ix _) = n≮n (indexR r) ix
cutoff-one (bad-earlier _ _ (here refl) (there ()) _ _ _ _ _)
cutoff-one (bad-earlier _ _ (there ()) _ _ _ _ _ _)
cutoff-one (bad-any r e (here refl) (here refl) _ _ _ _ _ ¬eq) = ¬eq refl
cutoff-one (bad-any _ _ (here refl) (there ()) _ _ _ _ _ _)
cutoff-one (bad-any _ _ (there ()) _ _ _ _ _ _ _)

kindOfMode : Mode → Kind
kindOfMode mnever = init
kindOfMode mearlier = signal
kindOfMode many = signal

asRow : RRow → Mode → Row
asRow (rr k i n b a _ ph) m = row k i n b a (kindOfMode m) ph

as-key : ∀ r m → keyOf (asRow r m) ≡ keyR r
as-key (rr _ _ _ _ _ _ _) _ = refl

as-index : ∀ r m → indexOf (asRow r m) ≡ indexR r
as-index (rr _ _ _ _ _ _ _) _ = refl

as-born : ∀ r m → bornOf (asRow r m) ≡ bornR r
as-born (rr _ _ _ _ _ _ _) _ = refl

as-at : ∀ r m → openedAtOf (asRow r m) ≡ openedAtR r
as-at (rr _ _ _ _ _ _ _) _ = refl

as-phase : ∀ r m → phaseOf (asRow r m) ≡ phaseR r
as-phase (rr _ _ _ _ _ _ _) _ = refl

as-kind : ∀ r m → kindOf (asRow r m) ≡ kindOfMode m
as-kind (rr _ _ _ _ _ _ _) _ = refl

-- `asRow` does not reduce on a variable, so the old fields move across
-- the projections before `cutoff-bound` sees the pair.
script-pair : (r e : RRow) (mb : Mode) →
  phaseR r ≡ opened → keyR e ≡ keyR r →
  indexR e < indexR r → bornR e ≤ openedAtR r →
  BadOpen (asRow r mearlier ∷ asRow e mb ∷ [])
script-pair r e mb op qk ix bq =
  asRow r mearlier , asRow e mb , here refl , there (here refl)
  , as-kind r mearlier
  , trans (as-phase r mearlier) op
  , trans (as-key e mb) (trans qk (sym (as-key r mearlier)))
  , subst (λ z → z < indexOf (asRow r mearlier)) (sym (as-index e mb))
      (subst (indexR e <_) (sym (as-index r mearlier)) ix)
  , subst (λ z → bornOf (asRow e mb) ≤ z) (sym (as-at r mearlier))
      (subst (_≤ openedAtR r) (sym (as-born e mb)) bq)

cutoffScript : ∀ {ρ : Rules} {rs : List RRow} (r e : RRow) →
  Any (_≡ r) rs → Any (_≡ e) rs →
  ρ (kindR r) ≡ mearlier → phaseR r ≡ opened →
  keyR e ≡ keyR r → indexR e < indexR r → bornR e ≤ openedAtR r →
  (ρ (kindR e) ≡ mnever ⊎ ρ (kindR e) ≡ mearlier) →
  Σ Row (λ r' → Σ Row (λ e' →
    BadOpen (r' ∷ e' ∷ []) ×
    ((kindOf e' ≡ init × indexOf e' ≡ 0 × indexOf r' ≡ 1 ×
      Any (_≡ slot init 0) script-a × Any (_≡ slot signal 1) script-a)
    ⊎ (kindOf e' ≡ signal × indexOf e' ≡ 1 × indexOf r' ≡ 2 ×
      Any (_≡ slot signal 1) script-a × Any (_≡ slot signal 2) script-a))))
cutoffScript {ρ} {rs} r e mr me ρr op qk ix bq (inj₁ ρe) =
  let bad : BadOpen (asRow r mearlier ∷ asRow e mnever ∷ [])
      bad = script-pair r e mnever op qk ix bq
  in cutoff-bound {asRow r mearlier ∷ asRow e mnever ∷ []} bad
cutoffScript {ρ} {rs} r e mr me ρr op qk ix bq (inj₂ ρe) =
  let bad : BadOpen (asRow r mearlier ∷ asRow e mearlier ∷ [])
      bad = script-pair r e mearlier op qk ix bq
  in cutoff-bound {asRow r mearlier ∷ asRow e mearlier ∷ []} bad

many≢never : many ≡ mnever → ⊥
many≢never ()

anyGap : ∀ {ρ : Rules} {kd : ℕ} → ρ kd ≡ many →
  (ρ kd ≡ mearlier → ⊥) × (ρ kd ≡ mnever → ⊥)
anyGap {ρ} {kd} eq =
  let left : ρ kd ≡ mearlier → ⊥
      left eqe = many≢earlier (trans (sym eq) eqe)
      right : ρ kd ≡ mnever → ⊥
      right eqn = many≢never (trans (sym eq) eqn)
  in left , right

data RulesReach (ρ : Rules) : RState → Set where
  rstart : RulesReach ρ emptyR
  rstep : ∀ {s a s'} → RulesReach ρ s → applyMode ρ s a ≡ just s' →
          RulesReach ρ s'

rules-reach-inv : ∀ {ρ s} → RulesReach ρ s → RulesInv ρ s
rules-reach-inv {ρ} rstart = emptyR-inv {ρ}
rules-reach-inv {ρ} (rstep {s} {a} {s'} prev eq) =
  rules-step {ρ} {s} {a} {s'} (rules-reach-inv prev) eq

reach-no-bad : ∀ {ρ s} → RulesReach ρ s → ¬ BadFamily ρ (rowsR s)
reach-no-bad prev bad = g-no-bad (rules-reach-inv prev) bad

reach-resolved : ∀ {ρ s k kd} → RulesReach ρ s →
  (ρ kd ≡ mearlier ⊎ ρ kd ≡ many) → EarlierResolved (rowsR s) k kd
reach-resolved prev m = inv-resolved (rules-reach-inv prev) m

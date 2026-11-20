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
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Family where

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; not; T; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Induction using (Acc; <-wellFounded)
open import Data.Nat.Properties
  using ( _≟_; _<?_; ≤-refl; ≤-trans; <⇒≤; <⇒≱; <⇒≢; n≮n; ≮⇒≥
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

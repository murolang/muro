------------------------------------------------------------------------
-- The reachable fragment of a buffered meeting.
--
-- `Universe g` lists every well-formed configuration. A step stays
-- inside it. The search from `init g` recurses on the length of the
-- still-unvisited part of that list: each call deletes the
-- configuration it expands, and that length is
-- `length (Unvisited (Universe g) seen)`. There is no counter to
-- peel and no early answer at zero.
--
-- `reachable` does not take a meeting derivation. `decide-nostuck`
-- reads the configurations it returns.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Graph where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap; length; filterᵇ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Properties using (length-++)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; m≤n⇒m≤1+n; m≤m⊔n; m≤n⊔m
        ; +-suc; +-identityʳ; _≟_)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_)
open import Induction.WellFounded using (Acc; acc)
open import Data.String.Properties using (_==_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst; inspect; [_])
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

open import Muro.AsyncRec
  using ( Atom; aNat; aBit; aCon
        ; Block; bDone; bStop; bPut; bEcho; bGrow; bGet; bPick0; bPick1
        ; bCover; bIget; bMget; conts
        ; Tok; pay; lab
        ; RConf; rc; Graph; gr
        ; Act; AWait; ABad; AGo
        ; init; lt; nth; lookB; onL; onR
        ; reactL; reactR; reactL′; reactR′; halted
        ; enqL; enqR; room; snoc; setNth; findA; findGo; eqA
        ; slotVal; nthA; armTo; fits; conOf; contsArms
        ; elemB; conf≟; replicate
        ; View; VFinal; VBad; VGo; view; kidsV; localB; shapeOf; merge; onIdle
        ; Shape; sh-final; sh-step
        ; ilOf; irOf; l2rOf; r2lOf; elOf; erOf
        ; Reach; rhere; rstep
        ; Tag; tagNat; tagBit; tagDat
        ; compile; materialise; alphabet
        ; COut; cok; cfail
        ; loopL; loopR
        )
open Graph

¬_ : Set → Set
¬ A = A → ⊥

open import Muro.Temporal
  using ( Who; lside; rside; fin; who≟
        ; Step; stepL; stepR; finish
        ; edges; fromL; fromR; stutter; stutterB; isFinalB; real; keep
        ; edges-kids
        ; emptyQ
        ; NoStuck
        ; snocR; goL-not-final; goR-not-final
        )
  public

open import Muro.Temporal using () renaming (kid-step to view-kid)

------------------------------------------------------------------------
-- A pointer may land on a continuation stored in the table, which can
-- sit one past the last block a jump names. `ptrBound` is that range.
-- It is a superset of the block indices, so a step stays inside it on
-- every graph, not only on a graph a compiler produced.
------------------------------------------------------------------------

maxℕ : List ℕ → ℕ
maxℕ [] = zero
maxℕ (n ∷ ns) = n ⊔ maxℕ ns

maxCont : List Block → ℕ
maxCont [] = zero
maxCont (b ∷ bs) = maxℕ (conts b) ⊔ maxCont bs

ptrBound : List Block → ℕ → ℕ
ptrBound bs e = suc (e ⊔ length bs ⊔ maxCont bs)

ptrL : Graph → ℕ
ptrL g = ptrBound (codeL g) (entryL g)

ptrR : Graph → ℕ
ptrR g = ptrBound (codeR g) (entryR g)

------------------------------------------------------------------------
-- Well-formed configurations. Queues are bounded by the buffer.
-- A `pay` token names an alphabet entry. A slot is `zero` when it is
-- empty and `suc i` when it holds alphabet entry `i`.
------------------------------------------------------------------------

data TokOk (g : Graph) : Tok → Set where
  ok-lab : (b : Bool) → TokOk g (lab b)
  ok-pay : ∀ {k} → k < length (alpha g) → TokOk g (pay k)

SlotOk : Graph → ℕ → Set
SlotOk g n = n < suc (length (alpha g))

record Wf (g : Graph) (c : RConf) : Set where
  constructor mkWf
  field
    il<  : ilOf c < ptrL g
    ir<  : irOf c < ptrR g
    l2r≤ : length (l2rOf c) ≤ cap g
    r2l≤ : length (r2lOf c) ≤ cap g
    l2rOk : All (TokOk g) (l2rOf c)
    r2lOk : All (TokOk g) (r2lOf c)
    el≡  : length (elOf c) ≡ slotsL g
    er≡  : length (erOf c) ≡ slotsR g
    elOk : All (SlotOk g) (elOf c)
    erOk : All (SlotOk g) (erOf c)

open Wf

------------------------------------------------------------------------
-- Lists used to enumerate the universe. Membership is proved from the
-- bound, so the search never has to build the list in order to run.
------------------------------------------------------------------------

below : ℕ → List ℕ
below zero = []
below (suc n) = below n ++ (n ∷ [])

listsExact : ∀ {A : Set} → ℕ → List A → List (List A)
listsExact zero _ = [] ∷ []
listsExact (suc n) as = concatMap (λ a → map (a ∷_) (listsExact n as)) as

lists≤ : ∀ {A : Set} → ℕ → List A → List (List A)
lists≤ zero _ = [] ∷ []
lists≤ (suc n) as = lists≤ n as ++ listsExact (suc n) as

toks : Graph → List Tok
toks g = lab false ∷ lab true ∷ map pay (below (length (alpha g)))

queues : Graph → List (List Tok)
queues g = lists≤ (cap g) (toks g)

envs : ℕ → ℕ → List (List ℕ)
envs bound zero = [] ∷ []
envs bound (suc n) =
  concatMap (λ v → map (v ∷_) (envs bound n)) (below (suc bound))

Universe : Graph → List RConf
Universe g =
  concatMap (λ il →
  concatMap (λ ir →
  concatMap (λ l2r →
  concatMap (λ r2l →
  concatMap (λ el →
    map (λ er → rc il ir l2r r2l el er) (envs (length (alpha g)) (slotsR g)))
    (envs (length (alpha g)) (slotsL g)))
    (queues g))
    (queues g))
    (below (ptrR g)))
    (below (ptrL g))

Unvisited : List RConf → List RConf → List RConf
Unvisited u seen = filterᵇ (λ c → not (elemB c seen)) u

------------------------------------------------------------------------
-- List membership. The universe proof is built from these; the search
-- itself deletes configurations from the pool, which starts as `Universe`.
------------------------------------------------------------------------

true≢false : ¬ (true ≡ false)
true≢false ()

wait≢go : ∀ {d} → ¬ (AWait ≡ AGo d)
wait≢go ()

bad≢go : ∀ {f d} → ¬ (ABad f ≡ AGo d)
bad≢go ()

ago-inj : ∀ {c d} → AGo c ≡ AGo d → c ≡ d
ago-inj refl = refl

∧-both : ∀ {a b} → a ∧ b ≡ true → a ≡ true × b ≡ true
∧-both {true} eq = refl , eq
∧-both {false} ()

empty-nil : ∀ {A} {q : List A} → emptyQ q ≡ true → q ≡ []
empty-nil {q = []} _ = refl
empty-nil {q = _ ∷ _} ()

m<m+suc : ∀ m n → m < m + suc n
m<m+suc zero n = s≤s z≤n
m<m+suc (suc m) n = s≤s (m<m+suc m n)

≤≢→< : ∀ {m n} → m ≤ n → m ≢ n → m < n
≤≢→< {zero} {zero} _ neq = ⊥-elim (neq refl)
≤≢→< {zero} {suc _} _ _ = s≤s z≤n
≤≢→< {suc m} {suc n} (s≤s le) neq = s≤s (≤≢→< le (λ eq → neq (cong suc eq)))
≤≢→< {suc _} {zero} ()

≤s≢ : ∀ {m n} → m ≤ suc n → m ≢ suc n → m ≤ n
≤s≢ {zero} _ _ = z≤n
≤s≢ {suc m} {n} (s≤s le) neq = ≤≢→< le (λ eq → neq (cong suc eq))

length-map : ∀ {A B : Set} {f : A → B} (xs : List A) → length (map f xs) ≡ length xs
length-map [] = refl
length-map (_ ∷ xs) = cong suc (length-map xs)

++-∈ˡ : ∀ {A : Set} {x : A} {xs ys : List A} → Any (_≡_ x) xs → Any (_≡_ x) (xs ++ ys)
++-∈ˡ (here eq) = here eq
++-∈ˡ (there p) = there (++-∈ˡ p)

++-∈ʳ : ∀ {A : Set} {x : A} (xs : List A) {ys : List A} →
        Any (_≡_ x) ys → Any (_≡_ x) (xs ++ ys)
++-∈ʳ [] p = p
++-∈ʳ (_ ∷ xs) p = there (++-∈ʳ xs p)

++-split : ∀ {A : Set} {x : A} (xs ys : List A) →
           Any (_≡_ x) (xs ++ ys) → Any (_≡_ x) xs ⊎ Any (_≡_ x) ys
++-split [] ys p = inj₂ p
++-split (x ∷ xs) ys (here eq) = inj₁ (here eq)
++-split (_ ∷ xs) ys (there p) with ++-split xs ys p
... | inj₁ q = inj₁ (there q)
... | inj₂ q = inj₂ q

map-∈ : ∀ {A B : Set} {f : A → B} {x : A} {xs : List A} →
        Any (_≡_ x) xs → Any (_≡_ (f x)) (map f xs)
map-∈ (here refl) = here refl
map-∈ (there p) = there (map-∈ p)

concatMap-∈ : ∀ {A B : Set} {f : A → List B} {x : A} {y : B} {xs : List A} →
              Any (_≡_ x) xs → Any (_≡_ y) (f x) → Any (_≡_ y) (concatMap f xs)
concatMap-∈ {f = f} (here refl) q = ++-∈ˡ q
concatMap-∈ {f = f} (there p) q = ++-∈ʳ (f _) (concatMap-∈ p q)

all-lookup : ∀ {A : Set} {P : A → Set} {x : A} {xs : List A} →
             All P xs → Any (_≡_ x) xs → P x
all-lookup (px ∷ _) (here refl) = px
all-lookup (_ ∷ ps) (there q) = all-lookup ps q

s≤s⁻¹ : ∀ {m n} → suc m ≤ suc n → m ≤ n
s≤s⁻¹ (s≤s le) = le

below-complete : ∀ {k n} → k < n → Any (_≡_ k) (below n)
below-complete {n = zero} ()
below-complete {k} {suc n} k< with k ≟ n
... | yes refl = ++-∈ʳ (below n) (here refl)
... | no k≢n = ++-∈ˡ (below-complete (≤≢→< (s≤s⁻¹ k<) k≢n))

below-lt : ∀ {k n} → Any (_≡_ k) (below n) → k < n
below-lt {k} {zero} ()
below-lt {k} {suc n} p with ++-split (below n) (n ∷ []) p
... | inj₂ (here refl) = s≤s ≤-refl
... | inj₂ (there ())
... | inj₁ q = m≤n⇒m≤1+n (below-lt q)

exact-complete : ∀ {A : Set} {n : ℕ} (xs as : List A) →
                 length xs ≡ n → All (λ x → Any (_≡_ x) as) xs →
                 Any (_≡_ xs) (listsExact n as)
exact-complete [] as refl [] = here refl
exact-complete (x ∷ xs) as refl (px ∷ ps) =
  concatMap-∈ px (map-∈ (exact-complete xs as refl ps))

lists≤-complete : ∀ {A : Set} {n : ℕ} (xs as : List A) →
                  length xs ≤ n → All (λ x → Any (_≡_ x) as) xs →
                  Any (_≡_ xs) (lists≤ n as)
lists≤-complete {n = zero} [] as _ _ = here refl
lists≤-complete {n = suc n} [] as _ _ = ++-∈ˡ (lists≤-complete {n = n} [] as z≤n [])
lists≤-complete {n = zero} (x ∷ xs) as ()
lists≤-complete {n = suc n} (x ∷ xs) as le all with length (x ∷ xs) ≟ suc n
... | yes p = ++-∈ʳ (lists≤ n as) (exact-complete (x ∷ xs) as p all)
... | no neq = ++-∈ˡ (lists≤-complete {n = n} (x ∷ xs) as (≤s≢ le neq) all)

envs-complete : ∀ {bound n} (xs : List ℕ) →
                length xs ≡ n → All (λ v → v < suc bound) xs →
                Any (_≡_ xs) (envs bound n)
envs-complete [] refl [] = here refl
envs-complete (v ∷ xs) refl (pv ∷ ps) =
  concatMap-∈ (below-complete pv) (map-∈ (envs-complete xs refl ps))

tok-∈ : ∀ {g} {t : Tok} → TokOk g t → Any (_≡_ t) (toks g)
tok-∈ (ok-lab false) = here refl
tok-∈ (ok-lab true) = there (here refl)
tok-∈ (ok-pay {k} k<) = there (there (map-∈ (below-complete k<)))

all-tok : ∀ {g} {q : List Tok} → All (TokOk g) q → All (λ t → Any (_≡_ t) (toks g)) q
all-tok [] = []
all-tok (p ∷ ps) = tok-∈ p ∷ all-tok ps

queue-∈ : ∀ {g} {q : List Tok} → length q ≤ cap g → All (TokOk g) q →
          Any (_≡_ q) (queues g)
queue-∈ {g} le ok = lists≤-complete _ (toks g) le (all-tok ok)

universe-complete : ∀ {g} {c} → Wf g c → Any (_≡_ c) (Universe g)
universe-complete {g} {rc il ir l2r r2l el er} w =
  concatMap-∈ (below-complete (il< w))
    (concatMap-∈ (below-complete (ir< w))
      (concatMap-∈ (queue-∈ (l2r≤ w) (l2rOk w))
        (concatMap-∈ (queue-∈ (r2l≤ w) (r2lOk w))
          (concatMap-∈ (envL (el≡ w) (elOk w))
            (map-∈ (envR (er≡ w) (erOk w)))))))
  where
  envL : ∀ {xs} → length xs ≡ slotsL g → All (SlotOk g) xs →
         Any (_≡_ xs) (envs (length (alpha g)) (slotsL g))
  envL eq ok = envs-complete _ eq ok
  envR : ∀ {xs} → length xs ≡ slotsR g → All (SlotOk g) xs →
         Any (_≡_ xs) (envs (length (alpha g)) (slotsR g))
  envR eq ok = envs-complete _ eq ok

------------------------------------------------------------------------
-- The start configuration is well formed, and a step stays well formed.
------------------------------------------------------------------------

len-replicate : ∀ n → length (replicate n) ≡ n
len-replicate zero = refl
len-replicate (suc n) = cong suc (len-replicate n)

all-zero : ∀ {g} n → All (SlotOk g) (replicate n)
all-zero zero = []
all-zero {g} (suc n) = s≤s (z≤n {n = length (alpha g)}) ∷ all-zero {g} n

entry< : ∀ (bs : List Block) (e : ℕ) → e < ptrBound bs e
entry< bs e = s≤s (≤-trans (m≤m⊔n e (length bs)) (m≤m⊔n (e ⊔ length bs) (maxCont bs)))

wf-init : ∀ g → Wf g (init g)
wf-init g = record
  { il< = entry< (codeL g) (entryL g)
  ; ir< = entry< (codeR g) (entryR g)
  ; l2r≤ = z≤n
  ; r2l≤ = z≤n
  ; l2rOk = []
  ; r2lOk = []
  ; el≡ = len-replicate (slotsL g)
  ; er≡ = len-replicate (slotsR g)
  ; elOk = all-zero {g} (slotsL g)
  ; erOk = all-zero {g} (slotsR g)
  }

∈-max : ∀ {j ns} → Any (_≡_ j) ns → j ≤ maxℕ ns
∈-max (here refl) = m≤m⊔n _ _
∈-max (there p) = ≤-trans (∈-max p) (m≤n⊔m _ _)

∈-maxCont : ∀ {j b bs} → Any (_≡_ b) bs → Any (_≡_ j) (conts b) → j ≤ maxCont bs
∈-maxCont (here refl) js = ≤-trans (∈-max js) (m≤m⊔n _ _)
∈-maxCont (there p) js = ≤-trans (∈-maxCont p js) (m≤n⊔m _ _)

-- Membership of a block the table returned, by recursion on the table.
-- Applying it to an abstract index does not invert `lookB`.
look-mem : (bs : List Block) (i : ℕ) (b : Block) → lookB bs i ≡ just b → Any (_≡_ b) bs
look-mem [] _ _ ()
look-mem (b′ ∷ bs) zero b eq = here (sym (unwrap eq))
  where
  unwrap : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
  unwrap refl = refl
look-mem (_ ∷ bs) (suc i) b eq = there (look-mem bs i b eq)

idx< : ∀ {g} {b j} → Any (_≡_ b) (codeL g) → Any (_≡_ j) (conts b) → j < ptrL g
idx< {g} mem js = s≤s (≤-trans (∈-maxCont mem js)
  (m≤n⊔m (entryL g ⊔ length (codeL g)) (maxCont (codeL g))))

idx<R : ∀ {g} {b j} → Any (_≡_ b) (codeR g) → Any (_≡_ j) (conts b) → j < ptrR g
idx<R {g} mem js = s≤s (≤-trans (∈-maxCont mem js)
  (m≤n⊔m (entryR g ⊔ length (codeR g)) (maxCont (codeR g))))

lt-sound : ∀ m n → lt m n ≡ true → m < n
lt-sound zero zero ()
lt-sound zero (suc n) _ = s≤s z≤n
lt-sound (suc m) zero ()
lt-sound (suc m) (suc n) eq = s≤s (lt-sound m n eq)

snoc-len : ∀ xs t → length (snoc xs t) ≡ suc (length xs)
snoc-len [] t = refl
snoc-len (x ∷ xs) t = cong suc (snoc-len xs t)

all-snoc : ∀ {g} {xs : List Tok} {t : Tok} →
           All (TokOk g) xs → TokOk g t → All (TokOk g) (snoc xs t)
all-snoc [] pt = pt ∷ []
all-snoc (px ∷ pxs) pt = px ∷ all-snoc pxs pt

set-len : ∀ n v xs → length (setNth n v xs) ≡ length xs
set-len zero v [] = refl
set-len (suc n) v [] = refl
set-len zero v (_ ∷ xs) = refl
set-len (suc n) v (_ ∷ xs) = cong suc (set-len n v xs)

set-all : ∀ {g n v xs} → All (SlotOk g) xs → SlotOk g v → All (SlotOk g) (setNth n v xs)
set-all {n = zero} [] _ = []
set-all {n = suc _} [] _ = []
set-all {g} {n = zero} (_ ∷ ps) pv = pv ∷ ps
set-all {g} {n = suc n} (px ∷ ps) pv = px ∷ set-all {g} {n = n} ps pv

nth-ok : ∀ {g env s v} → All (SlotOk g) env → nth env s ≡ just v → SlotOk g v
nth-ok {g} {env = x ∷ env} {zero} (px ∷ _) refl = px
nth-ok {g} {env = _ ∷ env} {suc s} (_ ∷ ps) eq = nth-ok {g} ps eq
nth-ok {env = []} _ ()

findGo-bound : ∀ n a as i → findGo n a as ≡ just i → i < n + length as
findGo-bound n a (x ∷ xs) i eq with eqA a x
... | true = subst (λ z → z < n + suc (length xs)) (just-inj eq) (m<m+suc n (length xs))
  where
  just-inj : ∀ {m k} → just m ≡ just k → m ≡ k
  just-inj refl = refl
... | false = subst (λ z → i < z) (sym (+-suc n (length xs))) (findGo-bound (suc n) a xs i eq)
findGo-bound n a [] i ()

findA-bound : ∀ {a as i} → findA a as ≡ just i → i < length as
findA-bound {a} {as} {i} eq = findGo-bound zero a as i eq

------------------------------------------------------------------------
-- A step stays inside the universe. Every `AGo` is a send into the
-- side's own queue or a receive from the other queue, and the block
-- it jumps to is a continuation of the block it left.
------------------------------------------------------------------------

just≡ : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just≡ refl = refl

-- `room` is `lt` on the length. `inspect` freezes that equality so a
-- `with` on the boolean does not hide it from the successor proof.
room-sound : ∀ {cap q} → room cap q ≡ true → lt (length q) cap ≡ true
room-sound eq = eq

tail≤ : ∀ {m n} → suc m ≤ n → m ≤ n
tail≤ {m} le = ≤-trans (m≤n⇒m≤1+n (≤-refl {x = m})) le

all-tail : ∀ {A : Set} {P : A → Set} {x : A} {xs : List A} → All P (x ∷ xs) → All P xs
all-tail (_ ∷ ps) = ps

jL : ∀ {g il b j} → lookB (codeL g) il ≡ just b → Any (_≡_ j) (conts b) → j < ptrL g
jL {g} {il} {b} lk mem = idx< {g} (look-mem (codeL g) il b lk) mem

jR : ∀ {g ir b j} → lookB (codeR g) ir ≡ just b → Any (_≡_ j) (conts b) → j < ptrR g
jR {g} {ir} {b} lk mem = idx<R {g} (look-mem (codeR g) ir b lk) mem

arm-∈ : ∀ {t s name arms j} → armTo name arms ≡ just j →
        Any (_≡_ j) (conts (bMget t s arms))
arm-∈ {t} {s} {name} {[]} ()
arm-∈ {t} {s} {name} {(y , k) ∷ rest} {j} eq with name == y
... | true =
  subst (λ z → Any (_≡_ z) (conts (bMget t s ((y , k) ∷ rest)))) (just≡ eq) (here refl)
... | false = there (arm-∈ {t} {s} {name} {rest} {j} eq)

slot-ix : ∀ {g env s k} → All (SlotOk g) env → slotVal env s ≡ just k →
          k < length (alpha g)
slot-ix {g} {env = env} {s = s} all eq with nth env s | inspect (nth env) s
slot-ix all () | nothing | _
slot-ix all () | just zero | _
slot-ix {g} all eq | just (suc i) | [ p ] =
  subst (λ z → z < length (alpha g)) (just≡ eq) (s≤s⁻¹ (nth-ok {g} all p))

sendL : ∀ {g il ir l2r r2l el er t i} →
        Wf g (rc il ir l2r r2l el er) → TokOk g t → i < ptrL g →
        lt (length l2r) (cap g) ≡ true →
        Wf g (rc i ir (snoc l2r t) r2l el er)
sendL {g} {l2r = l2r} {t = t} w tok i< room = record
  { il< = i<
  ; ir< = ir< w
  ; l2r≤ = subst (λ n → n ≤ cap g) (sym (snoc-len l2r t))
             (lt-sound (length l2r) (cap g) room)
  ; r2l≤ = r2l≤ w
  ; l2rOk = all-snoc (l2rOk w) tok
  ; r2lOk = r2lOk w
  ; el≡ = el≡ w
  ; er≡ = er≡ w
  ; elOk = elOk w
  ; erOk = erOk w
  }

sendR : ∀ {g il ir l2r r2l el er t i} →
        Wf g (rc il ir l2r r2l el er) → TokOk g t → i < ptrR g →
        lt (length r2l) (cap g) ≡ true →
        Wf g (rc il i l2r (snoc r2l t) el er)
sendR {g} {r2l = r2l} {t = t} w tok i< room = record
  { il< = il< w
  ; ir< = i<
  ; l2r≤ = l2r≤ w
  ; r2l≤ = subst (λ n → n ≤ cap g) (sym (snoc-len r2l t))
             (lt-sound (length r2l) (cap g) room)
  ; l2rOk = l2rOk w
  ; r2lOk = all-snoc (r2lOk w) tok
  ; el≡ = el≡ w
  ; er≡ = er≡ w
  ; elOk = elOk w
  ; erOk = erOk w
  }

dropL : ∀ {g il ir l2r t rest el er i} →
        Wf g (rc il ir l2r (t ∷ rest) el er) → i < ptrL g →
        Wf g (rc i ir l2r rest el er)
dropL w i< = record
  { il< = i<
  ; ir< = ir< w
  ; l2r≤ = l2r≤ w
  ; r2l≤ = tail≤ (r2l≤ w)
  ; l2rOk = l2rOk w
  ; r2lOk = all-tail (r2lOk w)
  ; el≡ = el≡ w
  ; er≡ = er≡ w
  ; elOk = elOk w
  ; erOk = erOk w
  }

dropR : ∀ {g il ir t rest r2l el er i} →
        Wf g (rc il ir (t ∷ rest) r2l el er) → i < ptrR g →
        Wf g (rc il i rest r2l el er)
dropR w i< = record
  { il< = il< w
  ; ir< = i<
  ; l2r≤ = tail≤ (l2r≤ w)
  ; r2l≤ = r2l≤ w
  ; l2rOk = all-tail (l2rOk w)
  ; r2lOk = r2lOk w
  ; el≡ = el≡ w
  ; er≡ = er≡ w
  ; elOk = elOk w
  ; erOk = erOk w
  }

paySlot : ∀ {g k ts} → All (TokOk g) (pay k ∷ ts) → SlotOk g (suc k)
paySlot (ok-pay k< ∷ _) = s≤s k<

recvL : ∀ {g il ir l2r k rest el er i s} →
        Wf g (rc il ir l2r (pay k ∷ rest) el er) → i < ptrL g →
        Wf g (rc i ir l2r rest (setNth s (suc k) el) er)
recvL {g} {k = k} {el = el} {s = s} w i< = record
  { il< = i<
  ; ir< = ir< w
  ; l2r≤ = l2r≤ w
  ; r2l≤ = tail≤ (r2l≤ w)
  ; l2rOk = l2rOk w
  ; r2lOk = all-tail (r2lOk w)
  ; el≡ = trans (set-len s (suc k) el) (el≡ w)
  ; er≡ = er≡ w
  ; elOk = set-all {g} (elOk w) (paySlot (r2lOk w))
  ; erOk = erOk w
  }

recvR : ∀ {g il ir k rest r2l el er i s} →
        Wf g (rc il ir (pay k ∷ rest) r2l el er) → i < ptrR g →
        Wf g (rc il i rest r2l el (setNth s (suc k) er))
recvR {g} {k = k} {er = er} {s = s} w i< = record
  { il< = il< w
  ; ir< = i<
  ; l2r≤ = tail≤ (l2r≤ w)
  ; r2l≤ = r2l≤ w
  ; l2rOk = all-tail (l2rOk w)
  ; r2lOk = r2lOk w
  ; el≡ = el≡ w
  ; er≡ = trans (set-len s (suc k) er) (er≡ w)
  ; elOk = elOk w
  ; erOk = set-all {g} (erOk w) (paySlot (l2rOk w))
  }

-- Left sends and receives. Each clause follows one `with` in `onL`.

putL : ∀ {g il ir l2r r2l el er a i d} →
       Wf g (rc il ir l2r r2l el er) →
       lookB (codeL g) il ≡ just (bPut a i) →
       onL g (rc il ir l2r r2l el er) (bPut a i) ≡ AGo d → Wf g d
putL {g} {l2r = l2r} {a = a} w lk eq with findA a (alpha g) in fa
putL w lk () | nothing
putL {g} {il} {l2r = l2r} {a = a} w lk eq | just k with room (cap g) l2r in rm
putL w lk () | just k | false
putL {g} {il} {l2r = l2r} {a = a} w lk refl | just k | true =
  sendL w (ok-pay (findA-bound {a} {alpha g} fa))
        (jL {g} {il} lk (here refl))
        (room-sound {cap g} {l2r} rm)

echoL : ∀ {g il ir l2r r2l el er s i d} →
        Wf g (rc il ir l2r r2l el er) →
        lookB (codeL g) il ≡ just (bEcho s i) →
        onL g (rc il ir l2r r2l el er) (bEcho s i) ≡ AGo d → Wf g d
echoL {g} {l2r = l2r} {el = el} {s = s} w lk eq with slotVal el s in sv
echoL w lk () | nothing
echoL {g} {il} {l2r = l2r} {el = el} {s = s} w lk eq | just k with room (cap g) l2r in rm
echoL w lk () | just k | false
echoL {g} {il} {l2r = l2r} {el = el} {s = s} w lk refl | just k | true =
  sendL w (ok-pay (slot-ix {g} {el} {s} {k} (elOk w) sv))
        (jL {g} {il} lk (here refl))
        (room-sound {cap g} {l2r} rm)

growL : ∀ {g il ir l2r r2l el er s i d} →
        Wf g (rc il ir l2r r2l el er) →
        lookB (codeL g) il ≡ just (bGrow s i) →
        onL g (rc il ir l2r r2l el er) (bGrow s i) ≡ AGo d → Wf g d
growL {g} {el = el} {s = s} w lk eq with slotVal el s
growL w lk () | nothing
growL {g} w lk eq | just k with nthA (alpha g) k
growL w lk () | just k | nothing
growL w lk () | just k | just (aBit _)
growL w lk () | just k | just (aCon _)
growL {g} {l2r = l2r} w lk eq | just k | just (aNat m)
  with findA (aNat (suc m)) (alpha g) in fa
growL w lk () | just k | just (aNat m) | nothing
growL {g} {il} {l2r = l2r} w lk eq | just k | just (aNat m) | just j
  with room (cap g) l2r in rm
growL w lk () | just k | just (aNat m) | just j | false
growL {g} {il} {l2r = l2r} w lk refl | just k | just (aNat m) | just j | true =
  sendL w (ok-pay (findA-bound {aNat (suc m)} {alpha g} fa))
        (jL {g} {il} lk (here refl))
        (room-sound {cap g} {l2r} rm)

pick0L : ∀ {g il ir l2r r2l el er i d} →
         Wf g (rc il ir l2r r2l el er) →
         lookB (codeL g) il ≡ just (bPick0 i) →
         onL g (rc il ir l2r r2l el er) (bPick0 i) ≡ AGo d → Wf g d
pick0L {g} {l2r = l2r} w lk eq with room (cap g) l2r in rm
pick0L w lk () | false
pick0L {g} {il} {l2r = l2r} w lk refl | true =
  sendL w (ok-lab false) (jL {g} {il} lk (here refl)) (room-sound {cap g} {l2r} rm)

pick1L : ∀ {g il ir l2r r2l el er i d} →
         Wf g (rc il ir l2r r2l el er) →
         lookB (codeL g) il ≡ just (bPick1 i) →
         onL g (rc il ir l2r r2l el er) (bPick1 i) ≡ AGo d → Wf g d
pick1L {g} {l2r = l2r} w lk eq with room (cap g) l2r in rm
pick1L w lk () | false
pick1L {g} {il} {l2r = l2r} w lk refl | true =
  sendL w (ok-lab true) (jL {g} {il} lk (here refl)) (room-sound {cap g} {l2r} rm)

getL : ∀ {g il ir l2r r2l el er t s i d} →
       Wf g (rc il ir l2r r2l el er) →
       lookB (codeL g) il ≡ just (bGet t s i) →
       onL g (rc il ir l2r r2l el er) (bGet t s i) ≡ AGo d → Wf g d
getL {r2l = r2l} w lk eq with r2l
getL w lk () | []
getL w lk () | lab _ ∷ _
getL {g} {t = t} w lk eq | pay k ∷ rest with nthA (alpha g) k
getL w lk () | pay k ∷ rest | nothing
getL {t = t} w lk eq | pay k ∷ rest | just a with fits t a
getL w lk () | pay k ∷ rest | just a | false
getL {g} {il} w lk refl | pay k ∷ rest | just a | true = recvL w (jL {g} {il} lk (here refl))

coverL : ∀ {g il ir l2r r2l el er i j d} →
         Wf g (rc il ir l2r r2l el er) →
         lookB (codeL g) il ≡ just (bCover i j) →
         onL g (rc il ir l2r r2l el er) (bCover i j) ≡ AGo d → Wf g d
coverL {r2l = r2l} w lk eq with r2l
coverL w lk () | []
coverL w lk () | pay _ ∷ _
coverL {g} {il} w lk refl | lab false ∷ rest = dropL w (jL {g} {il} lk (here refl))
coverL {g} {il} w lk refl | lab true ∷ rest = dropL w (jL {g} {il} lk (there (here refl)))

igetL : ∀ {g il ir l2r r2l el er s i j d} →
        Wf g (rc il ir l2r r2l el er) →
        lookB (codeL g) il ≡ just (bIget s i j) →
        onL g (rc il ir l2r r2l el er) (bIget s i j) ≡ AGo d → Wf g d
igetL {r2l = r2l} w lk eq with r2l
igetL w lk () | []
igetL w lk () | lab _ ∷ _
igetL {g} w lk eq | pay k ∷ rest with nthA (alpha g) k
igetL w lk () | pay k ∷ rest | nothing
igetL w lk () | pay k ∷ rest | just (aNat _)
igetL w lk () | pay k ∷ rest | just (aCon _)
igetL {g} {il} w lk refl | pay k ∷ rest | just (aBit false) = recvL w (jL {g} {il} lk (here refl))
igetL {g} {il} w lk refl | pay k ∷ rest | just (aBit true) = recvL w (jL {g} {il} lk (there (here refl)))

mgetL : ∀ {g il ir l2r r2l el er t s arms d} →
        Wf g (rc il ir l2r r2l el er) →
        lookB (codeL g) il ≡ just (bMget t s arms) →
        onL g (rc il ir l2r r2l el er) (bMget t s arms) ≡ AGo d → Wf g d
mgetL {r2l = r2l} {t = t} {s = s} {arms = arms} w lk eq with r2l
mgetL w lk () | []
mgetL w lk () | lab _ ∷ _
mgetL {g} {t = t} w lk eq | pay k ∷ rest with nthA (alpha g) k
mgetL w lk () | pay k ∷ rest | nothing
mgetL {t = t} w lk eq | pay k ∷ rest | just a with fits t a
mgetL w lk () | pay k ∷ rest | just a | false
mgetL {t = t} {arms = arms} w lk eq | pay k ∷ rest | just a | true with conOf a
mgetL w lk () | pay k ∷ rest | just a | true | nothing
mgetL {g} {il} {t = t} {s = s} {arms = arms} w lk eq | pay k ∷ rest | just a | true | just name
  with armTo name arms in aj
mgetL w lk () | pay k ∷ rest | just a | true | just name | nothing
mgetL {g} {il} {t = t} {s = s} {arms = arms} w lk refl
  | pay k ∷ rest | just a | true | just name | just j =
  recvL w (jL {g} {il} lk (arm-∈ {t} {s} {name} {arms} {j} aj))

wf-onL : ∀ {g il ir l2r r2l el er b d} →
         Wf g (rc il ir l2r r2l el er) →
         lookB (codeL g) il ≡ just b →
         onL g (rc il ir l2r r2l el er) b ≡ AGo d → Wf g d
wf-onL {b = bDone} _ _ ()
wf-onL {b = bStop} _ _ ()
wf-onL {b = bPut a i} w lk eq = putL w lk eq
wf-onL {b = bEcho s i} w lk eq = echoL w lk eq
wf-onL {b = bGrow s i} w lk eq = growL w lk eq
wf-onL {b = bGet t s i} w lk eq = getL w lk eq
wf-onL {b = bPick0 i} w lk eq = pick0L w lk eq
wf-onL {b = bPick1 i} w lk eq = pick1L w lk eq
wf-onL {b = bCover i j} w lk eq = coverL w lk eq
wf-onL {b = bIget s i j} w lk eq = igetL w lk eq
wf-onL {b = bMget t s arms} w lk eq = mgetL w lk eq

-- Right side. The same blocks, writing the other queue and the other slots.

putR : ∀ {g il ir l2r r2l el er a i d} →
       Wf g (rc il ir l2r r2l el er) →
       lookB (codeR g) ir ≡ just (bPut a i) →
       onR g (rc il ir l2r r2l el er) (bPut a i) ≡ AGo d → Wf g d
putR {g} {ir = ir} {r2l = r2l} {a = a} w lk eq with findA a (alpha g) in fa
... | nothing = ⊥-elim (bad≢go eq)
... | just k with room (cap g) r2l in rm
... | false = ⊥-elim (wait≢go eq)
... | true =
  subst (Wf g) (ago-inj eq)
    (sendR w (ok-pay (findA-bound {a} {alpha g} fa))
           (jR {g} {ir} lk (here refl))
           (room-sound {cap g} {r2l} rm))

echoR : ∀ {g il ir l2r r2l el er s i d} →
        Wf g (rc il ir l2r r2l el er) →
        lookB (codeR g) ir ≡ just (bEcho s i) →
        onR g (rc il ir l2r r2l el er) (bEcho s i) ≡ AGo d → Wf g d
echoR {g} {ir = ir} {r2l = r2l} {er = er} {s = s} w lk eq with slotVal er s in sv
... | nothing = ⊥-elim (wait≢go eq)
... | just k with room (cap g) r2l in rm
... | false = ⊥-elim (wait≢go eq)
... | true =
  subst (Wf g) (ago-inj eq)
    (sendR w (ok-pay (slot-ix {g} {er} {s} {k} (erOk w) sv))
           (jR {g} {ir} lk (here refl))
           (room-sound {cap g} {r2l} rm))

growR : ∀ {g il ir l2r r2l el er s i d} →
        Wf g (rc il ir l2r r2l el er) →
        lookB (codeR g) ir ≡ just (bGrow s i) →
        onR g (rc il ir l2r r2l el er) (bGrow s i) ≡ AGo d → Wf g d
growR {g} {ir = ir} {r2l = r2l} {er = er} {s = s} w lk eq with slotVal er s
... | nothing = ⊥-elim (wait≢go eq)
... | just k with nthA (alpha g) k
... | nothing = ⊥-elim (wait≢go eq)
... | just (aBit _) = ⊥-elim (wait≢go eq)
... | just (aCon _) = ⊥-elim (wait≢go eq)
... | just (aNat m) with findA (aNat (suc m)) (alpha g) in fa
... | nothing = ⊥-elim (bad≢go eq)
... | just j with room (cap g) r2l in rm
... | false = ⊥-elim (wait≢go eq)
... | true =
  subst (Wf g) (ago-inj eq)
    (sendR w (ok-pay (findA-bound {aNat (suc m)} {alpha g} fa))
           (jR {g} {ir} lk (here refl))
           (room-sound {cap g} {r2l} rm))

pick0R : ∀ {g il ir l2r r2l el er i d} →
         Wf g (rc il ir l2r r2l el er) →
         lookB (codeR g) ir ≡ just (bPick0 i) →
         onR g (rc il ir l2r r2l el er) (bPick0 i) ≡ AGo d → Wf g d
pick0R {g} {ir = ir} {r2l = r2l} w lk eq with room (cap g) r2l in rm
... | false = ⊥-elim (wait≢go eq)
... | true =
  subst (Wf g) (ago-inj eq)
    (sendR w (ok-lab false) (jR {g} {ir} lk (here refl)) (room-sound {cap g} {r2l} rm))

pick1R : ∀ {g il ir l2r r2l el er i d} →
         Wf g (rc il ir l2r r2l el er) →
         lookB (codeR g) ir ≡ just (bPick1 i) →
         onR g (rc il ir l2r r2l el er) (bPick1 i) ≡ AGo d → Wf g d
pick1R {g} {ir = ir} {r2l = r2l} w lk eq with room (cap g) r2l in rm
... | false = ⊥-elim (wait≢go eq)
... | true =
  subst (Wf g) (ago-inj eq)
    (sendR w (ok-lab true) (jR {g} {ir} lk (here refl)) (room-sound {cap g} {r2l} rm))

getR : ∀ {g il ir l2r r2l el er t s i d} →
       Wf g (rc il ir l2r r2l el er) →
       lookB (codeR g) ir ≡ just (bGet t s i) →
       onR g (rc il ir l2r r2l el er) (bGet t s i) ≡ AGo d → Wf g d
getR {g} {ir = ir} {l2r = l2r} {t = t} w lk eq with l2r
... | [] = ⊥-elim (wait≢go eq)
... | lab _ ∷ _ = ⊥-elim (bad≢go eq)
... | pay k ∷ rest with nthA (alpha g) k
... | nothing = ⊥-elim (bad≢go eq)
... | just a with fits t a
... | false = ⊥-elim (bad≢go eq)
... | true = subst (Wf g) (ago-inj eq) (recvR w (jR {g} {ir} lk (here refl)))

coverR : ∀ {g il ir l2r r2l el er i j d} →
         Wf g (rc il ir l2r r2l el er) →
         lookB (codeR g) ir ≡ just (bCover i j) →
         onR g (rc il ir l2r r2l el er) (bCover i j) ≡ AGo d → Wf g d
coverR {g} {ir = ir} {l2r = l2r} w lk eq with l2r
... | [] = ⊥-elim (wait≢go eq)
... | pay _ ∷ _ = ⊥-elim (bad≢go eq)
... | lab false ∷ rest =
  subst (Wf g) (ago-inj eq) (dropR w (jR {g} {ir} lk (here refl)))
... | lab true ∷ rest =
  subst (Wf g) (ago-inj eq) (dropR w (jR {g} {ir} lk (there (here refl))))

igetR : ∀ {g il ir l2r r2l el er s i j d} →
        Wf g (rc il ir l2r r2l el er) →
        lookB (codeR g) ir ≡ just (bIget s i j) →
        onR g (rc il ir l2r r2l el er) (bIget s i j) ≡ AGo d → Wf g d
igetR {g} {ir = ir} {l2r = l2r} w lk eq with l2r
... | [] = ⊥-elim (wait≢go eq)
... | lab _ ∷ _ = ⊥-elim (bad≢go eq)
... | pay k ∷ rest with nthA (alpha g) k
... | nothing = ⊥-elim (bad≢go eq)
... | just (aNat _) = ⊥-elim (bad≢go eq)
... | just (aCon _) = ⊥-elim (bad≢go eq)
... | just (aBit false) =
  subst (Wf g) (ago-inj eq) (recvR w (jR {g} {ir} lk (here refl)))
... | just (aBit true) =
  subst (Wf g) (ago-inj eq) (recvR w (jR {g} {ir} lk (there (here refl))))

mgetR : ∀ {g il ir l2r r2l el er t s arms d} →
        Wf g (rc il ir l2r r2l el er) →
        lookB (codeR g) ir ≡ just (bMget t s arms) →
        onR g (rc il ir l2r r2l el er) (bMget t s arms) ≡ AGo d → Wf g d
mgetR {g} {ir = ir} {l2r = l2r} {t = t} {s = s} {arms = arms} w lk eq with l2r
... | [] = ⊥-elim (wait≢go eq)
... | lab _ ∷ _ = ⊥-elim (bad≢go eq)
... | pay k ∷ rest with nthA (alpha g) k
... | nothing = ⊥-elim (bad≢go eq)
... | just a with fits t a
... | false = ⊥-elim (bad≢go eq)
... | true with conOf a
... | nothing = ⊥-elim (bad≢go eq)
... | just name with armTo name arms in aj
... | nothing = ⊥-elim (bad≢go eq)
... | just j =
  subst (Wf g) (ago-inj eq)
    (recvR w (jR {g} {ir} lk (arm-∈ {t} {s} {name} {arms} {j} aj)))

wf-onR : ∀ {g il ir l2r r2l el er b d} →
         Wf g (rc il ir l2r r2l el er) →
         lookB (codeR g) ir ≡ just b →
         onR g (rc il ir l2r r2l el er) b ≡ AGo d → Wf g d
wf-onR {b = bDone} _ _ ()
wf-onR {b = bStop} _ _ ()
wf-onR {b = bPut a i} w lk eq = putR w lk eq
wf-onR {b = bEcho s i} w lk eq = echoR w lk eq
wf-onR {b = bGrow s i} w lk eq = growR w lk eq
wf-onR {b = bGet t s i} w lk eq = getR w lk eq
wf-onR {b = bPick0 i} w lk eq = pick0R w lk eq
wf-onR {b = bPick1 i} w lk eq = pick1R w lk eq
wf-onR {b = bCover i j} w lk eq = coverR w lk eq
wf-onR {b = bIget s i j} w lk eq = igetR w lk eq
wf-onR {b = bMget t s arms} w lk eq = mgetR w lk eq

wf-stepL : ∀ {g c d} → Wf g c → reactL g c ≡ AGo d → Wf g d
wf-stepL {g} {c = rc il ir l2r r2l el er} {d = d} w eq = go (lookB (codeL g) il) refl
  where
  c′ = rc il ir l2r r2l el er
  open-eq : ∀ {m} → lookB (codeL g) il ≡ m → reactL′ g c′ m ≡ AGo d
  open-eq p = subst (λ m → reactL′ g c′ m ≡ AGo d) p eq
  go : (m : Maybe Block) → lookB (codeL g) il ≡ m → Wf g d
  go nothing p = ⊥-elim (wait≢go (open-eq p))
  go (just b) p = wf-onL w p (open-eq p)

wf-stepR : ∀ {g c d} → Wf g c → reactR g c ≡ AGo d → Wf g d
wf-stepR {g} {c = rc il ir l2r r2l el er} {d = d} w eq = go (lookB (codeR g) ir) refl
  where
  c′ = rc il ir l2r r2l el er
  open-eq : ∀ {m} → lookB (codeR g) ir ≡ m → reactR′ g c′ m ≡ AGo d
  open-eq p = subst (λ m → reactR′ g c′ m ≡ AGo d) p eq
  go : (m : Maybe Block) → lookB (codeR g) ir ≡ m → Wf g d
  go nothing p = ⊥-elim (wait≢go (open-eq p))
  go (just b) p = wf-onR w p (open-eq p)

wf-step : ∀ {g c who d} → Wf g c → Step g c who d → Wf g d
wf-step w (stepL eq) = wf-stepL w eq
wf-step w (stepR eq) = wf-stepR w eq
wf-step w (finish _ _ _) = w

-- A child of `view` stays well formed, and so does every configuration
-- reachable from a well-formed one. The start is well formed, so every
-- configuration reachable from it has queues of length at most `cap`.
wf-kid : ∀ {g c d} → Wf g c → Any (_≡_ d) (kidsV (view g c)) → Wf g d
wf-kid w mem = wf-step w (proj₂ (view-kid mem))

wf-along : ∀ {g a c} → Wf g a → Reach g a c → Wf g c
wf-along w rhere = w
wf-along w (rstep mem later) = wf-along (wf-kid w mem) later

reached-wf : ∀ {g c} → Reach g (init g) c → Wf g c
reached-wf {g} r = wf-along (wf-init g) r

------------------------------------------------------------------------
-- Breadth-first reachability.
--
-- The pool starts as `Universe g` and each call deletes the
-- configuration it expands. The length of the pool is
-- `length (Unvisited (Universe g) seen)`: the deleted configurations
-- are the ones already visited, and a successor that is still in the
-- pool has not been expanded. The recursion is `Acc` on that length.
-- A head that is not in the pool cannot occur; the branch is empty.
------------------------------------------------------------------------

Node : Set
Node = RConf × Maybe (Who × RConf)

confN : Node → RConf
confN = proj₁

queued : List Node → List RConf
queued = map confN

data UConf : List RConf → Set where
  u0 : UConf []
  u1 : ∀ {c cs} → elemB c cs ≡ false → UConf cs → UConf (c ∷ cs)

del : RConf → List RConf → List RConf
del c [] = []
del c (x ∷ xs) with conf≟ c x
... | yes _ = del c xs
... | no _ = x ∷ del c xs

del-≤ : ∀ c xs → length (del c xs) ≤ length xs
del-≤ c [] = z≤n
del-≤ c (x ∷ xs) with conf≟ c x
... | yes _ = ≤-trans (del-≤ c xs) (m≤n⇒m≤1+n (≤-refl {x = length xs}))
... | no _ = s≤s (del-≤ c xs)

del-shrink : ∀ c xs → elemB c xs ≡ true → length (del c xs) < length xs
del-shrink c [] ()
del-shrink c (x ∷ xs) eq with conf≟ c x
... | yes refl = s≤s (del-≤ c xs)
... | no _ = s≤s (del-shrink c xs eq)

lt-of-< : ∀ {m n} → m < n → lt m n ≡ true
lt-of-< {zero} {suc _} _ = refl
lt-of-< {suc m} {suc n} (s≤s le) = lt-of-< le

not-lt : ∀ {c pool} → elemB c pool ≡ true →
         lt (length (del c pool)) (length pool) ≡ false → ⊥
not-lt {c} {pool} p eq =
  true≢false (trans (sym (lt-of-< {length (del c pool)} {length pool}
                          (del-shrink c pool p))) eq)

any→elem : ∀ {c xs} → Any (_≡_ c) xs → elemB c xs ≡ true
any→elem {c} {x ∷ xs} (here p) with conf≟ c x
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p p)
any→elem {c} {x ∷ xs} (there more) with conf≟ c x
... | yes _ = refl
... | no _ = any→elem more

init-in : ∀ g → elemB (init g) (Universe g) ≡ true
init-in g = any→elem (universe-complete (wf-init g))

del-keep : ∀ {c d xs} → d ≢ c → elemB d xs ≡ true → elemB d (del c xs) ≡ true
del-keep {xs = []} _ ()
del-keep {c} {d} {x ∷ xs} neq eq with conf≟ c x
del-keep {c} {d} {x ∷ xs} neq eq | yes refl with conf≟ d c
... | yes refl = ⊥-elim (neq refl)
... | no _ = del-keep {c = c} {d = d} {xs = xs} neq eq
del-keep {c} {d} {x ∷ xs} neq eq | no _ with conf≟ d x
... | yes _ = refl
... | no _ = del-keep {c = c} {d = d} {xs = xs} neq eq

elem-head-¬ : ∀ {c x xs} → elemB c (x ∷ xs) ≡ false → c ≢ x
elem-head-¬ {c} {x} eq with conf≟ c x
... | yes refl = λ _ → true≢false eq
... | no ¬p = ¬p

elem-cons-false : ∀ {c x xs} → elemB c (x ∷ xs) ≡ false → elemB c xs ≡ false
elem-cons-false {c} {x} eq with conf≟ c x
... | yes _ = ⊥-elim (true≢false eq)
... | no _ = eq

nodes-¬ : ∀ c ns → elemB c (queued ns) ≡ false → All (λ n → confN n ≢ c) ns
nodes-¬ c [] _ = []
nodes-¬ c (n ∷ ns) eq =
  (λ p → elem-head-¬ {c} {confN n} {queued ns} eq (sym p)) ∷
  nodes-¬ c ns (elem-cons-false {c} {confN n} {queued ns} eq)

rest-in : ∀ c pool ns →
          All (λ n → elemB (confN n) pool ≡ true) ns →
          All (λ n → confN n ≢ c) ns →
          All (λ n → elemB (confN n) (del c pool) ≡ true) ns
rest-in c pool [] _ _ = []
rest-in c pool (n ∷ ns) (p ∷ ps) (neq ∷ neqs) =
  del-keep {c = c} {d = confN n} {xs = pool} neq p ∷ rest-in c pool ns ps neqs

-- One term in the two acts, so a proof can substitute either act.
stepsActs : Graph → RConf → Act → Act → List (Who × RConf)
stepsActs g c la ra =
  if localB (merge g c la ra) then
    filterᵇ keep (fromL la ++ fromR ra ++ stutter g c)
  else []

stepsOf : Graph → RConf → List (Who × RConf)
stepsOf g c = stepsActs g c (reactL g c) (reactR g c)

push : List RConf → List RConf → RConf → List (Who × RConf) → List Node
push pool busy parent [] = []
push pool busy parent ((w , d) ∷ ws) with elemB d pool | elemB d busy
... | true | false = (d , just (w , parent)) ∷ push pool (d ∷ busy) parent ws
... | true | true = push pool busy parent ws
... | false | true = push pool busy parent ws
... | false | false = push pool busy parent ws

push-ok : ∀ pool busy parent ws →
          All (λ n → elemB (confN n) pool ≡ true) (push pool busy parent ws)
push-ok pool busy parent [] = []
push-ok pool busy parent ((w , d) ∷ ws)
  with elemB d pool in inP | elemB d busy
... | true | false = inP ∷ push-ok pool (d ∷ busy) parent ws
... | true | true = push-ok pool busy parent ws
... | false | true = push-ok pool busy parent ws
... | false | false = push-ok pool busy parent ws

weaken-disj : ∀ d busy ns →
              All (λ n → elemB (confN n) (d ∷ busy) ≡ false) ns →
              All (λ n → elemB (confN n) busy ≡ false) ns
weaken-disj d busy [] _ = []
weaken-disj d busy (n ∷ ns) (p ∷ ps) =
  elem-cons-false {confN n} {d} {busy} p ∷ weaken-disj d busy ns ps

push-disj : ∀ pool busy parent ws →
            All (λ n → elemB (confN n) busy ≡ false) (push pool busy parent ws)
push-disj pool busy parent [] = []
push-disj pool busy parent ((w , d) ∷ ws)
  with elemB d pool | elemB d busy in inB
... | true | false =
  inB ∷ weaken-disj d busy (push pool (d ∷ busy) parent ws)
                     (push-disj pool (d ∷ busy) parent ws)
... | true | true = push-disj pool busy parent ws
... | false | true = push-disj pool busy parent ws
... | false | false = push-disj pool busy parent ws

not-mem : ∀ d ns → All (λ n → confN n ≢ d) ns → elemB d (queued ns) ≡ false
not-mem d [] _ = refl
not-mem d (n ∷ ns) (neq ∷ neqs) with conf≟ d (confN n)
... | yes p = ⊥-elim (neq (sym p))
... | no _ = not-mem d ns neqs

all-≢ : ∀ d busy ns →
        All (λ n → elemB (confN n) (d ∷ busy) ≡ false) ns →
        All (λ n → confN n ≢ d) ns
all-≢ d busy [] _ = []
all-≢ d busy (n ∷ ns) (p ∷ ps) =
  elem-head-¬ {confN n} {d} {busy} p ∷ all-≢ d busy ns ps

push-uq : ∀ pool busy parent ws → UConf (queued (push pool busy parent ws))
push-uq pool busy parent [] = u0
push-uq pool busy parent ((w , d) ∷ ws) with elemB d pool | elemB d busy
... | true | false =
  u1 (not-mem d (push pool (d ∷ busy) parent ws)
        (all-≢ d busy (push pool (d ∷ busy) parent ws)
              (push-disj pool (d ∷ busy) parent ws)))
     (push-uq pool (d ∷ busy) parent ws)
... | true | true = push-uq pool busy parent ws
... | false | true = push-uq pool busy parent ws
... | false | false = push-uq pool busy parent ws

elem-join : ∀ {z} xs ys → elemB z xs ≡ false → elemB z ys ≡ false →
            elemB z (xs ++ ys) ≡ false
elem-join [] ys _ q = q
elem-join {z} (x ∷ xs) ys p q with conf≟ z x
... | yes _ = ⊥-elim (true≢false p)
... | no _ = elem-join {z} xs ys p q

-- `x ≡ y` puts `y` at the head of a list that starts with `x`.
elem-hit : ∀ {y x xs} → x ≡ y → elemB y (x ∷ xs) ≡ true
elem-hit {y} {x} eq with conf≟ y x
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p (sym eq))

none-ys : ∀ x xs ys → All (λ y → elemB y (x ∷ xs) ≡ false) ys → elemB x ys ≡ false
none-ys x xs [] _ = refl
none-ys x xs (y ∷ ys) (p ∷ ps) with conf≟ x y
... | yes xy = ⊥-elim (true≢false (trans (sym (elem-hit xy)) p))
... | no _ = none-ys x xs ys ps

map-cons-false : ∀ {x xs ys} →
                 All (λ y → elemB y (x ∷ xs) ≡ false) ys →
                 All (λ y → elemB y xs ≡ false) ys
map-cons-false [] = []
map-cons-false {x} {xs} {y ∷ ys} (p ∷ ps) =
  elem-cons-false {y} {x} {xs} p ∷ map-cons-false {x} {xs} {ys} ps

u-cat : ∀ {xs ys} → UConf xs → UConf ys →
        All (λ y → elemB y xs ≡ false) ys → UConf (xs ++ ys)
u-cat {[]} _ uy _ = uy
u-cat {x ∷ xs} {ys} (u1 notx ux) uy dis =
  u1 (elem-join {x} xs ys notx (none-ys x xs ys dis))
     (u-cat {xs} {ys} ux uy (map-cons-false {x} {xs} {ys} dis))

u-tail : ∀ {x xs} → UConf (x ∷ xs) → UConf xs
u-tail (u1 _ u) = u

u-notin : ∀ {x xs} → UConf (x ∷ xs) → elemB x xs ≡ false
u-notin (u1 p _) = p

queued-++ : ∀ xs ys → queued (xs ++ ys) ≡ queued xs ++ queued ys
queued-++ [] ys = refl
queued-++ (x ∷ xs) ys = cong (_∷_ (confN x)) (queued-++ xs ys)

queued-disj : ∀ c cs ns →
              All (λ n → elemB (confN n) (c ∷ cs) ≡ false) ns →
              All (λ y → elemB y cs ≡ false) (queued ns)
queued-disj c cs [] _ = []
queued-disj c cs (n ∷ ns) (p ∷ ps) =
  elem-cons-false {confN n} {c} {cs} p ∷ queued-disj c cs ns ps

all-++ : ∀ {A : Set} {P : A → Set} {xs ys : List A} →
         All P xs → All P ys → All P (xs ++ ys)
all-++ [] qs = qs
all-++ (p ∷ ps) qs = p ∷ all-++ ps qs

all-head : ∀ {P : Node → Set} {n ns} → All P (n ∷ ns) → P n
all-head (p ∷ _) = p

all-rest : ∀ {P : Node → Set} {n ns} → All P (n ∷ ns) → All P ns
all-rest (_ ∷ ps) = ps

-- The frontier after expanding `n` is the old tail plus the new kids.
-- `queued` of that concatenation is the concatenation of the queues,
-- and the kids are disjoint from the tail by `push-disj`.
next-u : ∀ {n : Node} {rest : List Node} →
         UConf (queued (n ∷ rest)) → (kids : List Node) →
         UConf (queued kids) →
         All (λ nd → elemB (confN nd) (queued (n ∷ rest)) ≡ false) kids →
         UConf (queued (rest ++ kids))
next-u {n} {rest} unq kids uk dis =
  subst UConf (sym (queued-++ rest kids))
    (u-cat (u-tail unq) uk
      (queued-disj (confN n) (queued rest) kids dis))

-- One level of the search. `pool` is the part of `Universe g` not yet
-- expanded. Deleting the head strictly shortens it, which is the
-- measure. The `false` branch is empty: the head is in the pool.
-- `expand` matches the boolean, so the `true` arm is the cons by
-- computation. `go` does not abstract the measure: a `with` on `del`
-- does not invert.
measure : List RConf → Node → Bool
measure pool n = lt (length (del (confN n) pool)) (length pool)

mutual
  expand : (g : Graph) (pool : List RConf) (n : Node) (rest : List Node) →
           (rec : ∀ {y} → y < length pool → Acc _<_ y) →
           All (λ nd → elemB (confN nd) pool ≡ true) (n ∷ rest) →
           UConf (queued (n ∷ rest)) →
           (b : Bool) → measure pool n ≡ b → List Node
  expand g pool n rest rec mem unq true eq =
    n ∷ go g (del (confN n) pool)
           (rest ++ push (del (confN n) pool) (queued (n ∷ rest)) (confN n)
                         (stepsOf g (confN n)))
           (rec (lt-sound (length (del (confN n) pool)) (length pool) eq))
           (all-++ (rest-in (confN n) pool rest (all-rest mem)
                             (nodes-¬ (confN n) rest (u-notin unq)))
                   (push-ok (del (confN n) pool) (queued (n ∷ rest))
                            (confN n) (stepsOf g (confN n))))
           (next-u {n} {rest} unq
              (push (del (confN n) pool) (queued (n ∷ rest)) (confN n)
                    (stepsOf g (confN n)))
              (push-uq (del (confN n) pool) (queued (n ∷ rest)) (confN n)
                       (stepsOf g (confN n)))
              (push-disj (del (confN n) pool) (queued (n ∷ rest)) (confN n)
                         (stepsOf g (confN n))))
  expand g pool n rest rec mem unq false eq =
    ⊥-elim (not-lt {c = confN n} {pool = pool} (all-head mem) eq)

  go : (g : Graph) (pool : List RConf) (fr : List Node) →
       Acc _<_ (length pool) →
       All (λ n → elemB (confN n) pool ≡ true) fr →
       UConf (queued fr) →
       List Node
  go g pool [] _ _ _ = []
  go g pool (n ∷ rest) (acc rec) mem unq =
    expand g pool n rest rec mem unq (measure pool n) refl

------------------------------------------------------------------------
-- Closed examples. `finG` stutters at the start. `loopG` is the
-- compiled `loopL` / `loopR` meeting at buffer 1, built by `compile`
-- and `materialise`.
------------------------------------------------------------------------

finG : Graph
finG = gr (bDone ∷ []) (bDone ∷ []) [] zero zero zero zero zero

loopG : Graph
loopG with compile loopL [] [] [] zero zero | compile loopR [] [] [] zero zero
... | cok eL nL sL bsL | cok eR nR sR bsR =
  let L = materialise nL zero bsL
      R = materialise nR zero bsR
  in gr L R (alphabet L R) (suc zero) eL eR sL sR
... | cok _ _ _ _ | cfail _ = finG
... | cfail _ | _ = finG

-- The body stays hidden. A proof may use `reachable-is`; it does not
-- unfold `Universe` while comparing two occurrences of `reachable g`.
abstract
  reachable : Graph → List Node
  reachable g =
    go g (Universe g) ((init g , nothing) ∷ [])
      (<-wellFounded-fast (length (Universe g)))
      (init-in g ∷ [])
      (u1 refl u0)

  reachable-is : ∀ g →
    reachable g ≡
    go g (Universe g) ((init g , nothing) ∷ [])
      (<-wellFounded-fast (length (Universe g)))
      (init-in g ∷ [])
      (u1 refl u0)
  reachable-is g = refl

  ex-fin : length (reachable finG) ≡ 1
  ex-fin = refl

  ex-loop-len : length (reachable loopG) ≡ 4
  ex-loop-len = refl

------------------------------------------------------------------------
-- A real edge is a `Step`, and its target is a child of `view`.
-- `stepsOf` is empty on a fault and on a stutter, so membership in it
-- is a left or right step.
------------------------------------------------------------------------

stutter-nil : ∀ {g c} → isFinalB g c ≡ false → stutter g c ≡ []
stutter-nil {g} {c} eq rewrite eq = refl

nil-any : ∀ {A : Set} {P : A → Set} → Any P [] → ⊥
nil-any ()

StepKid : (g : Graph) (c : RConf) → Who × RConf → Set
StepKid g c (w , d) = Step g c w d × Any (_≡_ d) (kidsV (view g c))

-- Replace each reaction in `view` by the act the caller already has.
view-acts : ∀ {g c la ra} → reactL g c ≡ la → reactR g c ≡ ra →
            view g c ≡ merge g c la ra
view-acts {g} {c} {la} {ra} eqL eqR =
  subst (λ a → view g c ≡ merge g c a ra) eqL
    (subst (λ b → view g c ≡ merge g c (reactL g c) b) eqR refl)

atKid : ∀ {g c d xs} → kidsV (view g c) ≡ d ∷ xs → Any (_≡_ d) (kidsV (view g c))
atKid eq = subst (λ ys → Any (_≡_ _) ys) (sym eq) (here refl)

-- Both sides waiting. The only edge is the stutter, and `keep` drops
-- it. A fault view contributes nothing. Matching the queues here, at
-- the top level, avoids a rewrite under the `with` of `steps-all`.
idleSteps : (g : Graph) (c : RConf) (lq rq : List Tok) (h : Bool) →
            l2rOf c ≡ lq → r2lOf c ≡ rq → halted g c ≡ h →
            List (Who × RConf)
idleSteps g c lq rq h e1 e2 e3 =
  if localB (onIdle g c lq rq h e1 e2 e3) then
    filterᵇ keep (stutterB c (emptyQ lq ∧ emptyQ rq ∧ h))
  else []

idle-empty : ∀ g c lq rq h e1 e2 e3 → idleSteps g c lq rq h e1 e2 e3 ≡ []
idle-empty g c [] [] true e1 e2 e3 = refl
idle-empty g c [] [] false e1 e2 e3 = refl
idle-empty g c [] (_ ∷ _) true e1 e2 e3 = refl
idle-empty g c [] (_ ∷ _) false e1 e2 e3 = refl
idle-empty g c (_ ∷ _) [] true e1 e2 e3 = refl
idle-empty g c (_ ∷ _) [] false e1 e2 e3 = refl
idle-empty g c (_ ∷ _) (_ ∷ _) true e1 e2 e3 = refl
idle-empty g c (_ ∷ _) (_ ∷ _) false e1 e2 e3 = refl

idle-acts : ∀ g c →
            stepsActs g c AWait AWait ≡
            idleSteps g c (l2rOf c) (r2lOf c) (halted g c) refl refl refl
idle-acts g c = refl

-- `inspect` remembers `reactL g c ≡ AGo e` without unfolding `reactL`
-- to `reactL′`. A fault view and a stutter contribute no kept edge.
steps-all : ∀ g c → All (StepKid g c) (stepsOf g c)
steps-all g c with reactL g c | inspect (reactL g) c
                 | reactR g c | inspect (reactR g) c
steps-all g c | ABad _ | [ _ ] | _ | [ _ ] = []
steps-all g c | AGo _ | [ _ ] | ABad _ | [ _ ] = []
steps-all g c | AWait | [ _ ] | ABad _ | [ _ ] = []
steps-all g c | AGo e | [ eqL ] | AGo f | [ eqR ] =
  subst (λ b → All (StepKid g c)
           (filterᵇ keep ((lside , e) ∷ (rside , f) ∷ stutterB c b)))
        (sym (goL-not-final {g} {c} {e} eqL))
        ((stepL eqL , atKid (cong kidsV (view-acts {g} {c} {AGo e} {AGo f} eqL eqR))) ∷
         (stepR eqR , subst (λ ys → Any (_≡_ f) ys)
                            (sym (cong kidsV (view-acts {g} {c} {AGo e} {AGo f} eqL eqR)))
                            (there (here refl))) ∷
         [])
steps-all g c | AGo e | [ eqL ] | AWait | [ eqR ] =
  subst (λ b → All (StepKid g c)
           (filterᵇ keep ((lside , e) ∷ stutterB c b)))
        (sym (goL-not-final {g} {c} {e} eqL))
        ((stepL eqL , atKid (cong kidsV (view-acts {g} {c} {AGo e} {AWait} eqL eqR))) ∷ [])
steps-all g c | AWait | [ eqL ] | AGo f | [ eqR ] =
  subst (λ b → All (StepKid g c)
           (filterᵇ keep ((rside , f) ∷ stutterB c b)))
        (sym (goR-not-final {g} {c} {f} eqR))
        ((stepR eqR , atKid (cong kidsV (view-acts {g} {c} {AWait} {AGo f} eqL eqR))) ∷ [])
steps-all g c | AWait | [ _ ] | AWait | [ _ ] =
  subst (λ xs → All (StepKid g c) xs)
        (sym (trans (idle-acts g c)
                    (idle-empty g c (l2rOf c) (r2lOf c) (halted g c)
                               refl refl refl)))
        []

-- The nodes `push` keeps are a sublist of its input, in order, so the
-- child proofs travel with them.
pushR : ∀ {g} pool busy parent → Reach g (init g) parent →
        ∀ ws → All (StepKid g parent) ws →
        All (λ n → Reach g (init g) (confN n)) (push pool busy parent ws)
pushR pool busy parent rp [] [] = []
pushR pool busy parent rp ((w , d) ∷ ws) (sk ∷ sks) with elemB d pool | elemB d busy
... | true | false = snocR rp (proj₂ sk) ∷ pushR pool (d ∷ busy) parent rp ws sks
... | true | true = pushR pool busy parent rp ws sks
... | false | true = pushR pool busy parent rp ws sks
... | false | false = pushR pool busy parent rp ws sks

AllReach : Graph → List Node → Set
AllReach g ns = All (λ n → Reach g (init g) (confN n)) ns

-- `subst (λ z → x ≡ z) eq refl` is `eq`, once `eq` is `refl`.
subst-eq : ∀ {A : Set} {x y : A} (eq : x ≡ y) →
           subst (λ z → x ≡ z) eq refl ≡ eq
subst-eq refl = refl

-- Move `expand` onto `true`. The transported proof is then replaced
-- by the caller's `eq`, so the cons is the one `go-reach` builds.
cast-expand : ∀ {g pool n rest mem unq}
              (rec : ∀ {y} → y < length pool → Acc _<_ y)
              (b : Bool) (p : measure pool n ≡ b) (q : b ≡ true) →
              expand g pool n rest rec mem unq b p ≡
              expand g pool n rest rec mem unq true
                (subst (λ z → measure pool n ≡ z) q p)
cast-expand rec true p refl = refl
cast-expand rec false _ ()

go-expand : ∀ {g pool n rest mem unq} (rec : ∀ {y} → y < length pool → Acc _<_ y)
            (eq : measure pool n ≡ true) →
            go g pool (n ∷ rest) (acc rec) mem unq ≡
            n ∷ go g (del (confN n) pool)
                   (rest ++ push (del (confN n) pool) (queued (n ∷ rest)) (confN n)
                                 (stepsOf g (confN n)))
                   (rec (lt-sound (length (del (confN n) pool)) (length pool) eq))
                   (all-++ (rest-in (confN n) pool rest (all-rest mem)
                                     (nodes-¬ (confN n) rest (u-notin unq)))
                           (push-ok (del (confN n) pool) (queued (n ∷ rest))
                                    (confN n) (stepsOf g (confN n))))
                   (next-u {n} {rest} unq
                      (push (del (confN n) pool) (queued (n ∷ rest)) (confN n)
                            (stepsOf g (confN n)))
                      (push-uq (del (confN n) pool) (queued (n ∷ rest)) (confN n)
                               (stepsOf g (confN n)))
                      (push-disj (del (confN n) pool) (queued (n ∷ rest)) (confN n)
                                 (stepsOf g (confN n))))
go-expand {g} {pool} {n} {rest} {mem} {unq} rec eq =
  trans (cast-expand rec (measure pool n) refl eq)
        (cong (expand g pool n rest rec mem unq true) (subst-eq eq))

go-reach : ∀ g pool fr acc mem unq → AllReach g fr →
           AllReach g (go g pool fr acc mem unq)
go-reach g pool [] _ _ _ _ = []
go-reach g pool (n ∷ rest) (acc rec) mem unq (rp ∷ rps) = body smaller refl
  where
  pool′ = del (confN n) pool
  steps = stepsOf g (confN n)
  busy = queued (n ∷ rest)
  kids = push pool′ busy (confN n) steps
  fr′ = rest ++ kids
  mem′ = all-++ (rest-in (confN n) pool rest (all-rest mem)
                          (nodes-¬ (confN n) rest (u-notin unq)))
                (push-ok pool′ busy (confN n) steps)
  unq′ = next-u {n} {rest} unq kids (push-uq pool′ busy (confN n) steps)
                                 (push-disj pool′ busy (confN n) steps)
  smaller = lt (length pool′) (length pool)
  kidR = pushR pool′ busy (confN n) rp steps (steps-all g (confN n))
  body : (b : Bool) → smaller ≡ b → AllReach g (go g pool (n ∷ rest) (acc rec) mem unq)
  body false eq = ⊥-elim (not-lt {c = confN n} {pool = pool} (all-head mem) eq)
  body true eq =
    subst (AllReach g) (sym (go-expand {g} {pool} {n} {rest} {mem} {unq} rec eq))
      (rp ∷ go-reach g pool′ fr′ (rec (lt-sound (length pool′) (length pool) eq))
                       mem′ unq′ (all-++ rps kidR))

------------------------------------------------------------------------
-- Soundness. Every configuration the search emits is reachable from
-- `init g`, by the child edge `steps-all` recovered.
------------------------------------------------------------------------

all-mapf : ∀ {A B : Set} {P : B → Set} {f : A → B} {xs : List A} →
           All (λ a → P (f a)) xs → All P (map f xs)
all-mapf [] = []
all-mapf (p ∷ ps) = p ∷ all-mapf ps

reachable-reach : ∀ g → AllReach g (reachable g)
reachable-reach g =
  subst (AllReach g) (sym (reachable-is g))
    (go-reach g (Universe g) ((init g , nothing) ∷ [])
      (<-wellFounded-fast (length (Universe g)))
      (init-in g ∷ [])
      (u1 refl u0)
      (rhere ∷ []))

reachable-sound : ∀ {g c} → Any (_≡_ c) (queued (reachable g)) → Reach g (init g) c
reachable-sound {g} mem = all-lookup (all-mapf (reachable-reach g)) mem

------------------------------------------------------------------------
-- No duplicates. A configuration that has left the pool, and is not on
-- the frontier, is not emitted again. The head is deleted before the
-- recursive call, and `push` refuses anything already queued.
------------------------------------------------------------------------

del-gone : ∀ c xs → elemB c (del c xs) ≡ false
del-gone c [] = refl
del-gone c (x ∷ xs) with conf≟ c x
del-gone c (x ∷ xs) | yes refl = del-gone c xs
del-gone c (x ∷ xs) | no ¬p with conf≟ c x
... | yes eq = ⊥-elim (¬p eq)
... | no _ = del-gone c xs

≢-sym : ∀ {A : Set} {x y : A} → x ≢ y → y ≢ x
≢-sym neq eq = neq (sym eq)

del-skip : ∀ {c d xs} → d ≢ c → elemB d (del c xs) ≡ elemB d xs
del-skip {xs = []} _ = refl
del-skip {c} {d} {x ∷ xs} neq with conf≟ c x
del-skip {c} {d} {x ∷ xs} neq | yes refl with conf≟ d c
... | yes refl = ⊥-elim (neq refl)
... | no _ = del-skip {c = c} {d = d} {xs = xs} neq
del-skip {c} {d} {x ∷ xs} neq | no _ with conf≟ d x
... | yes _ = refl
... | no _ = del-skip {c = c} {d = d} {xs = xs} neq

none-queued : ∀ c ns → All (λ n → confN n ≢ c) ns → elemB c (queued ns) ≡ false
none-queued c [] _ = refl
none-queued c (n ∷ ns) (neq ∷ neqs) with conf≟ c (confN n)
... | yes eq = ⊥-elim (neq (sym eq))
... | no _ = none-queued c ns neqs

push-neq : ∀ pool busy parent ws {c} → elemB c pool ≡ false →
           All (λ n → confN n ≢ c) (push pool busy parent ws)
push-neq pool busy parent [] _ = []
push-neq pool busy parent ((w , d) ∷ ws) {c} abs
  with elemB d pool in inP | elemB d busy
... | true | false =
  (λ eq → true≢false (trans (sym (subst (λ x → elemB x pool ≡ true) eq inP)) abs)) ∷
  push-neq pool (d ∷ busy) parent ws abs
... | true | true = push-neq pool busy parent ws abs
... | false | true = push-neq pool busy parent ws abs
... | false | false = push-neq pool busy parent ws abs

shrink-ok : ∀ {pool n} → elemB (confN n) pool ≡ true → measure pool n ≡ true
shrink-ok {pool} {n} p =
  lt-of-< {length (del (confN n) pool)} {length pool} (del-shrink (confN n) pool p)

go-avoids : ∀ g pool fr acc mem unq c →
            elemB c pool ≡ false →
            All (λ n → confN n ≢ c) fr →
            All (λ n → confN n ≢ c) (go g pool fr acc mem unq)
go-avoids g pool [] _ _ _ c _ _ = []
go-avoids g pool (n ∷ rest) (acc rec) mem unq c absent (neq ∷ neqs) =
  subst (All (λ nd → confN nd ≢ c)) (sym (go-expand {g} {pool} {n} {rest} {mem} {unq} rec ok))
    (neq ∷ go-avoids g pool′ fr′ (rec (lt-sound (length pool′) (length pool) ok))
                     mem′ unq′ c absent′ (all-++ neqs (push-neq pool′ busy (confN n) steps absent′)))
  where
  ok = shrink-ok {pool} {n} (all-head mem)
  pool′ = del (confN n) pool
  steps = stepsOf g (confN n)
  busy = queued (n ∷ rest)
  kids = push pool′ busy (confN n) steps
  fr′ = rest ++ kids
  mem′ = all-++ (rest-in (confN n) pool rest (all-rest mem)
                          (nodes-¬ (confN n) rest (u-notin unq)))
                (push-ok pool′ busy (confN n) steps)
  unq′ = next-u {n} {rest} unq kids (push-uq pool′ busy (confN n) steps)
                                 (push-disj pool′ busy (confN n) steps)
  absent′ = subst (λ b → b ≡ false)
                 (sym (del-skip {c = confN n} {d = c} {xs = pool} (≢-sym neq)))
                 absent

go-unique : ∀ g pool fr acc mem unq → UConf (queued (go g pool fr acc mem unq))
go-unique g pool [] _ _ _ = u0
go-unique g pool (n ∷ rest) (acc rec) mem unq =
  subst UConf (sym (cong queued (go-expand {g} {pool} {n} {rest} {mem} {unq} rec ok)))
    (u1 (none-queued (confN n) tail tail-≠) (go-unique g pool′ fr′ (rec (lt-sound (length pool′) (length pool) ok)) mem′ unq′))
  where
  ok = shrink-ok {pool} {n} (all-head mem)
  pool′ = del (confN n) pool
  steps = stepsOf g (confN n)
  busy = queued (n ∷ rest)
  kids = push pool′ busy (confN n) steps
  fr′ = rest ++ kids
  mem′ = all-++ (rest-in (confN n) pool rest (all-rest mem)
                          (nodes-¬ (confN n) rest (u-notin unq)))
                (push-ok pool′ busy (confN n) steps)
  unq′ = next-u {n} {rest} unq kids (push-uq pool′ busy (confN n) steps)
                                 (push-disj pool′ busy (confN n) steps)
  rest-≠ = nodes-¬ (confN n) rest (u-notin unq)
  kids-≠ = push-neq pool′ busy (confN n) steps {c = confN n} (del-gone (confN n) pool)
  -- push-neq needs elemB (confN n) pool′ ≡ false, which is del-gone.
  -- But kids may equal n only if n is still in pool′, which it is not.
  -- The disjunction with the frontier uses push-disj against `busy`,
  -- which already contains n, so a pushed kid is not n. `push-neq`
  -- against pool′ is the wrong fact for a kid that was refused because
  -- it is busy: those kids are not in the output. `fr′` is rest ++ kids,
  -- and kids are exactly the pushed nodes, which are disjoint from busy.
  kids-≠′ = all-≠ (push-disj pool′ busy (confN n) steps)
    where
    all-≠ : ∀ {ns} → All (λ nd → elemB (confN nd) busy ≡ false) ns →
            All (λ nd → confN nd ≢ confN n) ns
    all-≠ [] = []
    all-≠ {nd ∷ ns} (p ∷ ps) =
      elem-head-¬ {confN nd} {confN n} {queued rest} p ∷ all-≠ ps
  tail = go g pool′ fr′ (rec (lt-sound (length pool′) (length pool) ok)) mem′ unq′
  tail-≠ = go-avoids g pool′ fr′ (rec (lt-sound (length pool′) (length pool) ok))
                     mem′ unq′ (confN n) (del-gone (confN n) pool)
                     (all-++ rest-≠ kids-≠′)

reachable-nodup : ∀ g → UConf (queued (reachable g))
reachable-nodup g =
  subst (λ ns → UConf (queued ns)) (sym (reachable-is g))
    (go-unique g (Universe g) ((init g , nothing) ∷ [])
      (<-wellFounded-fast (length (Universe g)))
      (init-in g ∷ [])
      (u1 refl u0))

------------------------------------------------------------------------
-- Completeness. The frontier is emitted, and a kid of an emitted
-- configuration is emitted: it is pushed, it is already on the
-- frontier, or it was deleted earlier and so already sits in the prefix.
------------------------------------------------------------------------

++-assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

all-take : ∀ {A : Set} {P : A → Set} (xs : List A) {ys : List A} →
           All P (xs ++ ys) → All P xs
all-take [] _ = []
all-take (x ∷ xs) (p ∷ ps) = p ∷ all-take xs ps

all-drop : ∀ {A : Set} {P : A → Set} (xs : List A) {ys : List A} →
           All P (xs ++ ys) → All P ys
all-drop [] ps = ps
all-drop (_ ∷ xs) (_ ∷ ps) = all-drop xs ps

there-all : ∀ {c ns ms} →
            All (λ n → Any (_≡_ (confN n)) ms) ns →
            All (λ n → Any (_≡_ (confN n)) (c ∷ ms)) ns
there-all [] = []
there-all (p ∷ ps) = there p ∷ there-all ps

any-proj : ∀ {A B : Set} {f : A → B} {y : B} (xs : List A) →
           Any (_≡_ y) (map f xs) → Any (λ x → f x ≡ y) xs
any-proj [] p = ⊥-elim (nil-any p)
any-proj {B = B} {f = f} {y = y} (x ∷ xs) p = step (map f (x ∷ xs)) p refl
  where
  step : (ys : List B) → Any (_≡_ y) ys → ys ≡ f x ∷ map f xs →
         Any (λ z → f z ≡ y) (x ∷ xs)
  step (.(f x) ∷ .(map f xs)) (here eq) refl = here (sym eq)
  step (.(f x) ∷ .(map f xs)) (there q) refl = there (any-proj xs q)
  step [] _ ()

steps-local : ∀ {g c} → localB (view g c) ≡ true →
              stepsOf g c ≡ filterᵇ keep (edges g c)
steps-local {g} {c} eq =
  subst (λ b → (if b then filterᵇ keep (fromL (reactL g c) ++ fromR (reactR g c) ++ stutter g c)
                else [])
               ≡ filterᵇ keep (edges g c))
        (sym eq) refl

real-steps : ∀ {g c} → localB (view g c) ≡ true →
             map proj₂ (stepsOf g c) ≡ kidsV (view g c)
real-steps eq = trans (cong (map proj₂) (steps-local eq)) (edges-kids eq)

kid-local : ∀ {g c d} → Any (_≡_ d) (kidsV (view g c)) → localB (view g c) ≡ true
kid-local {g} {c} {d} p with view g c
kid-local {g} {c} {d} p | VFinal a b h = ⊥-elim (nil-any p)
kid-local {g} {c} {d} p | VBad f = ⊥-elim (nil-any p)
kid-local {g} {c} {d} p | VGo k ks = refl

kid-step : ∀ {g c d} → Any (_≡_ d) (kidsV (view g c)) →
           Any (λ p → proj₂ p ≡ d) (stepsOf g c)
kid-step {d = d} has =
  any-proj _ (subst (Any (_≡_ d)) (sym (real-steps (kid-local has))) has)

lookup-step : ∀ {g c d} (ws : List (Who × RConf)) →
              All (StepKid g c) ws → Any (λ p → proj₂ p ≡ d) ws →
              Σ Who (λ w → Step g c w d)
lookup-step ((w , e) ∷ _) ((step , _) ∷ _) (here eq) =
  w , subst (λ z → Step _ _ w z) eq step
lookup-step (_ ∷ ws) (_ ∷ ss) (there p) = lookup-step ws ss p
lookup-step [] _ ()

elem→any : ∀ c (xs : List RConf) → elemB c xs ≡ true → Any (_≡_ c) xs
elem→any c [] ()
elem→any c (x ∷ xs) eq with conf≟ c x
... | yes refl = here refl
... | no _ = there (elem→any c xs eq)

elem-split : ∀ {c x xs} → elemB c (x ∷ xs) ≡ true → c ≡ x ⊎ elemB c xs ≡ true
elem-split {c} {x} eq with conf≟ c x
... | yes p = inj₁ p
... | no _ = inj₂ eq

queued-of : ∀ {d ns} → Any (λ n → confN n ≡ d) ns → Any (_≡_ d) (queued ns)
queued-of (here eq) = here (sym eq)
queued-of (there p) = there (queued-of p)

push-place : ∀ pool busy parent ws d →
             Any (λ p → proj₂ p ≡ d) ws →
             Any (λ n → confN n ≡ d) (push pool busy parent ws)
             ⊎ elemB d busy ≡ true ⊎ elemB d pool ≡ false
push-place pool busy parent [] d ()
push-place pool busy parent ((w , e) ∷ ws) d (here eq)
  with elemB e pool in inP | elemB e busy in inB
... | true | false = inj₁ (here eq)
... | true | true = inj₂ (inj₁ (subst (λ x → elemB x busy ≡ true) eq inB))
... | false | true = inj₂ (inj₁ (subst (λ x → elemB x busy ≡ true) eq inB))
... | false | false = inj₂ (inj₂ (subst (λ x → elemB x pool ≡ false) eq inP))
push-place pool busy parent ((w , e) ∷ ws) d (there p) with elemB e pool | elemB e busy
push-place pool busy parent ((w , e) ∷ ws) d (there p) | true | false =
  place-kept (push-place pool (e ∷ busy) parent ws d p)
  where
  place-kept : Any (λ n → confN n ≡ d) (push pool (e ∷ busy) parent ws)
             ⊎ elemB d (e ∷ busy) ≡ true ⊎ elemB d pool ≡ false →
             Any (λ n → confN n ≡ d)
                 ((e , just (w , parent)) ∷ push pool (e ∷ busy) parent ws)
             ⊎ elemB d busy ≡ true ⊎ elemB d pool ≡ false
  place-kept (inj₁ q) = inj₁ (there q)
  place-kept (inj₂ (inj₁ b)) with elem-split b
  ... | inj₁ eq = inj₁ (here (sym eq))
  ... | inj₂ b′ = inj₂ (inj₁ b′)
  place-kept (inj₂ (inj₂ u)) = inj₂ (inj₂ u)
push-place pool busy parent ((w , e) ∷ ws) d (there p) | true | true =
  push-place pool busy parent ws d p
push-place pool busy parent ((w , e) ∷ ws) d (there p) | false | true =
  push-place pool busy parent ws d p
push-place pool busy parent ((w , e) ∷ ws) d (there p) | false | false =
  push-place pool busy parent ws d p

go-in-front : ∀ g pool fr acc mem unq →
              All (λ n → Any (_≡_ (confN n)) (queued (go g pool fr acc mem unq))) fr
go-in-front g pool [] _ _ _ = []
go-in-front g pool (n ∷ rest) (acc rec) mem unq =
  subst (λ out → All (λ nd → Any (_≡_ (confN nd)) (queued out)) (n ∷ rest))
        (sym (go-expand {g} {pool} {n} {rest} {mem} {unq} rec ok))
        (here refl ∷ there-all (all-take rest fronts))
  where
  ok = shrink-ok {pool} {n} (all-head mem)
  pool′ = del (confN n) pool
  steps = stepsOf g (confN n)
  busy = queued (n ∷ rest)
  kids = push pool′ busy (confN n) steps
  fr′ = rest ++ kids
  mem′ = all-++ (rest-in (confN n) pool rest (all-rest mem)
                          (nodes-¬ (confN n) rest (u-notin unq)))
                (push-ok pool′ busy (confN n) steps)
  unq′ = next-u {n} {rest} unq kids (push-uq pool′ busy (confN n) steps)
                                 (push-disj pool′ busy (confN n) steps)
  fronts = go-in-front g pool′ fr′ (rec (lt-sound (length pool′) (length pool) ok)) mem′ unq′

-- Where a kid of the configuration being expanded sits: already emitted,
-- or on the frontier that the recursive call still has to emit.
placed : ∀ {g} (n : Node) (rest : List Node) (pool : List RConf) (pre : List Node) →
         Wf g (confN n) →
         (∀ {c} → Wf g c → Any (_≡_ c) (queued pre) ⊎ elemB c pool ≡ true) →
         ∀ {d} → Any (_≡_ d) (kidsV (view g (confN n))) →
         Any (_≡_ d) (queued (pre ++ (n ∷ []))) ⊎
         Any (_≡_ d) (queued (rest ++ push (del (confN n) pool) (queued (n ∷ rest)) (confN n) (stepsOf g (confN n))))
placed {g} n rest pool pre wfN pc {d} kid = conclude (push-place pool′ busy (confN n) steps d edge)
  where
  pool′ = del (confN n) pool
  busy = queued (n ∷ rest)
  steps = stepsOf g (confN n)
  edge = kid-step kid
  wD = wf-step wfN (proj₂ (lookup-step steps (steps-all g (confN n)) edge))
  queued-pre′ = queued (pre ++ (n ∷ []))
  to-pre′ : ∀ {x} → Any (_≡_ x) (queued pre ++ (confN n ∷ [])) → Any (_≡_ x) queued-pre′
  to-pre′ p = subst (Any (_≡_ _)) (sym (queued-++ pre (n ∷ []))) p
  in-head : Any (_≡_ (confN n)) queued-pre′
  in-head = to-pre′ (++-∈ʳ (queued pre) (here refl))
  to-fr : ∀ {x} →
          Any (_≡_ x) (queued rest ++ queued (push pool′ busy (confN n) steps)) →
          Any (_≡_ x) (queued (rest ++ push pool′ busy (confN n) steps))
  to-fr p = subst (Any (_≡_ _)) (sym (queued-++ rest (push pool′ busy (confN n) steps))) p
  conclude : Any (λ nd → confN nd ≡ d) (push pool′ busy (confN n) steps)
           ⊎ elemB d busy ≡ true ⊎ elemB d pool′ ≡ false →
           Any (_≡_ d) queued-pre′ ⊎ Any (_≡_ d) (queued (rest ++ push pool′ busy (confN n) steps))
  conclude (inj₁ inKids) = inj₂ (to-fr (++-∈ʳ (queued rest) (queued-of inKids)))
  conclude (inj₂ (inj₁ inBusy)) with elem-split inBusy
  ... | inj₁ eq = inj₁ (subst (λ x → Any (_≡_ x) queued-pre′) (sym eq) in-head)
  ... | inj₂ inRest = inj₂ (to-fr (++-∈ˡ (elem→any d (queued rest) inRest)))
  conclude (inj₂ (inj₂ notP)) with conf≟ d (confN n)
  ... | yes eq = inj₁ (subst (λ x → Any (_≡_ x) queued-pre′) (sym eq) in-head)
  ... | no neq with pc wD
  ... | inj₁ inPre = inj₁ (to-pre′ (++-∈ˡ inPre))
  ... | inj₂ inPool =
    ⊥-elim (true≢false (trans (sym inPool)
      (subst (λ b → b ≡ false) (del-skip {c = confN n} {d = d} {xs = pool} neq) notP)))

++[] : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++[] [] = refl
++[] (x ∷ xs) = cong (_∷_ x) (++[] xs)

push-wf : ∀ {g} pool busy parent ws →
          Wf g parent → All (StepKid g parent) ws →
          All (λ nd → Wf g (confN nd)) (push pool busy parent ws)
push-wf pool busy parent [] _ _ = []
push-wf pool busy parent ((w , e) ∷ ws) wf ((step , _) ∷ ss)
  with elemB e pool | elemB e busy
... | true | false = wf-step wf step ∷ push-wf pool (e ∷ busy) parent ws wf ss
... | true | true = push-wf pool busy parent ws wf ss
... | false | true = push-wf pool busy parent ws wf ss
... | false | false = push-wf pool busy parent ws wf ss

PoolCov : Graph → List Node → List RConf → Set
PoolCov g pre pool = ∀ {c} → Wf g c → Any (_≡_ c) (queued pre) ⊎ elemB c pool ≡ true

KidCov : Graph → List Node → List Node → Set
KidCov g pre fr =
  ∀ {c d} → Any (_≡_ c) (queued pre) → Any (_≡_ d) (kidsV (view g c)) →
  Any (_≡_ d) (queued pre) ⊎ Any (_≡_ d) (queued fr)

from-all : ∀ {ms} d (ns : List Node) →
           All (λ n → Any (_≡_ (confN n)) ms) ns →
           Any (_≡_ d) (queued ns) → Any (_≡_ d) ms
from-all d [] _ ()
from-all d (n ∷ ns) (p ∷ ps) mem with conf≟ d (confN n)
... | yes refl = p
... | no neq with mem
... | here eq = ⊥-elim (neq eq)
... | there q = from-all d ns ps q

-- Every frontier configuration is emitted, and the emitted set stays
-- closed under `kidsV`. `pre` is what earlier calls have already emitted.
go-close : ∀ g pre pool fr acc mem unq →
           PoolCov g pre pool → KidCov g pre fr →
           All (λ nd → Wf g (confN nd)) pre →
           All (λ nd → Wf g (confN nd)) fr →
           ∀ {c d} → Any (_≡_ c) (queued (pre ++ go g pool fr acc mem unq)) →
           Any (_≡_ d) (kidsV (view g c)) →
           Any (_≡_ d) (queued (pre ++ go g pool fr acc mem unq))
go-close g pre pool [] _ _ _ pc kc wfP wfF {c} {d} has step
  with kc (subst (Any (_≡_ c)) (cong queued (++[] pre)) has) step
... | inj₁ p = subst (Any (_≡_ d)) (sym (cong queued (++[] pre))) p
... | inj₂ ()
go-close g pre pool (n ∷ rest) (acc rec) mem unq pc kc wfP (wfN ∷ wfR) {c} {d} has step =
  subst (λ out → Any (_≡_ d) (queued (pre ++ out)))
        (sym (go-expand {g} {pool} {n} {rest} {mem} {unq} rec ok))
        (dispatch (split has′))
  where
  ok = shrink-ok {pool} {n} (all-head mem)
  pool′ = del (confN n) pool
  steps = stepsOf g (confN n)
  busy = queued (n ∷ rest)
  kids = push pool′ busy (confN n) steps
  fr′ = rest ++ kids
  mem′ = all-++ (rest-in (confN n) pool rest (all-rest mem)
                          (nodes-¬ (confN n) rest (u-notin unq)))
                (push-ok pool′ busy (confN n) steps)
  unq′ = next-u {n} {rest} unq kids (push-uq pool′ busy (confN n) steps)
                                 (push-disj pool′ busy (confN n) steps)
  tail = go g pool′ fr′ (rec (lt-sound (length pool′) (length pool) ok)) mem′ unq′
  preN = pre ++ (n ∷ [])
  fronts = go-in-front g pool′ fr′ (rec (lt-sound (length pool′) (length pool) ok)) mem′ unq′
  has′ : Any (_≡_ c) (queued (pre ++ (n ∷ tail)))
  has′ = subst (λ out → Any (_≡_ c) (queued (pre ++ out)))
             (go-expand {g} {pool} {n} {rest} {mem} {unq} rec ok) has
  split : Any (_≡_ c) (queued (pre ++ (n ∷ tail))) →
          Any (_≡_ c) (queued pre) ⊎ Any (_≡_ c) (confN n ∷ queued tail)
  split p = ++-split (queued pre) (confN n ∷ queued tail)
              (subst (Any (_≡_ c)) (queued-++ pre (n ∷ tail)) p)
  in-left : Any (_≡_ d) (queued pre) → Any (_≡_ d) (queued (pre ++ (n ∷ tail)))
  in-left p = subst (Any (_≡_ d)) (sym (queued-++ pre (n ∷ tail))) (++-∈ˡ p)
  in-tail : Any (_≡_ d) (queued tail) → Any (_≡_ d) (queued (pre ++ (n ∷ tail)))
  in-tail p = subst (Any (_≡_ d)) (sym (queued-++ pre (n ∷ tail)))
                (++-∈ʳ (queued pre) (there p))
  in-here : Any (_≡_ (confN n)) (queued (pre ++ (n ∷ tail)))
  in-here = subst (Any (_≡_ (confN n))) (sym (queued-++ pre (n ∷ tail)))
              (++-∈ʳ (queued pre) (here refl))
  dispatch : Any (_≡_ c) (queued pre) ⊎ Any (_≡_ c) (confN n ∷ queued tail) →
             Any (_≡_ d) (queued (pre ++ (n ∷ tail)))
  dispatch (inj₁ inPre) with kc inPre step
  ... | inj₁ p = in-left p
  ... | inj₂ onFr with onFr
  ... | here eq = subst (λ x → Any (_≡_ x) (queued (pre ++ (n ∷ tail)))) (sym eq) in-here
  ... | there q = in-tail (from-all d rest (all-take rest fronts) q)
  dispatch (inj₂ (here eq)) =
    embed (placed n rest pool pre wfN pc
             (subst (λ x → Any (_≡_ d) (kidsV (view g x))) eq step))
    where
    embed : Any (_≡_ d) (queued preN) ⊎ Any (_≡_ d) (queued fr′) →
            Any (_≡_ d) (queued (pre ++ (n ∷ tail)))
    embed (inj₁ p) = subst (Any (_≡_ d)) (cong queued (++-assoc pre (n ∷ []) tail))
                      (subst (Any (_≡_ d)) (sym (queued-++ preN tail)) (++-∈ˡ p))
    embed (inj₂ p) = in-tail (from-all d fr′ fronts p)
  dispatch (inj₂ (there inTail)) =
    subst (Any (_≡_ d)) (cong queued (++-assoc pre (n ∷ []) tail))
      (go-close g preN pool′ fr′ (rec (lt-sound (length pool′) (length pool) ok))
                mem′ unq′ pc′ kc′ (all-++ wfP (wfN ∷ []))
                (all-++ wfR (push-wf pool′ busy (confN n) steps wfN (steps-all g (confN n))))
                inRec step)
    where
    inRec : Any (_≡_ c) (queued (preN ++ tail))
    inRec = subst (Any (_≡_ c)) (sym (queued-++ preN tail)) (++-∈ʳ (queued preN) inTail)
    pc′ : PoolCov g preN pool′
    pc′ {c = x} wx with pc wx
    ... | inj₁ p = inj₁ (subst (Any (_≡_ x)) (sym (queued-++ pre (n ∷ []))) (++-∈ˡ p))
    ... | inj₂ inP with conf≟ x (confN n)
    ... | yes refl = inj₁ (subst (Any (_≡_ (confN n))) (sym (queued-++ pre (n ∷ [])))
                            (++-∈ʳ (queued pre) (here refl)))
    ... | no neq = inj₂ (subst (λ b → b ≡ true)
                           (sym (del-skip {c = confN n} {d = x} {xs = pool} neq)) inP)
    kc′ : KidCov g preN fr′
    kc′ {c = x} {d = y} hasX stepY = on-parent (split-pre hasX) stepY
      where
      split-pre : Any (_≡_ x) (queued preN) →
                  Any (_≡_ x) (queued pre) ⊎ Any (_≡_ x) (confN n ∷ [])
      split-pre p = ++-split (queued pre) (confN n ∷ [])
                      (subst (Any (_≡_ x)) (queued-++ pre (n ∷ [])) p)
      on-old : Any (_≡_ y) (queued pre) ⊎ Any (_≡_ y) (queued (n ∷ rest)) →
               Any (_≡_ y) (queued preN) ⊎ Any (_≡_ y) (queued fr′)
      on-old (inj₁ p) =
        inj₁ (subst (Any (_≡_ y)) (sym (queued-++ pre (n ∷ []))) (++-∈ˡ p))
      on-old (inj₂ (here eq)) =
        inj₁ (subst (λ z → Any (_≡_ z) (queued preN)) (sym eq)
               (subst (Any (_≡_ (confN n))) (sym (queued-++ pre (n ∷ [])))
                 (++-∈ʳ (queued pre) (here refl))))
      on-old (inj₂ (there q)) =
        inj₂ (subst (Any (_≡_ y)) (sym (queued-++ rest kids)) (++-∈ˡ q))
      on-parent : Any (_≡_ x) (queued pre) ⊎ Any (_≡_ x) (confN n ∷ []) →
                  Any (_≡_ y) (kidsV (view g x)) →
                  Any (_≡_ y) (queued preN) ⊎ Any (_≡_ y) (queued fr′)
      on-parent (inj₁ inPre) stepX = on-old (kc inPre stepX)
      on-parent (inj₂ (here eq)) stepX =
        placed n rest pool pre wfN pc
          (subst (λ z → Any (_≡_ y) (kidsV (view g z))) eq stepX)
      on-parent (inj₂ (there ())) _

------------------------------------------------------------------------
-- Completeness. `init` is emitted, and a kid of an emitted configuration
-- is emitted. `Reach` is built by prepending, so the membership walks
-- the derivation from the start.
------------------------------------------------------------------------

out-closed : ∀ g {c d} →
             Any (_≡_ c) (queued (reachable g)) →
             Any (_≡_ d) (kidsV (view g c)) →
             Any (_≡_ d) (queued (reachable g))
out-closed g {c} {d} has step =
  subst (λ ns → Any (_≡_ d) (queued ns)) (sym (reachable-is g))
    (go-close g [] (Universe g) ((init g , nothing) ∷ [])
      (<-wellFounded-fast (length (Universe g)))
      (init-in g ∷ [])
      (u1 refl u0)
      pc0 kc0 [] (wf-init g ∷ [])
      (subst (λ ns → Any (_≡_ c) (queued ns)) (reachable-is g) has)
      step)
  where
  pc0 : PoolCov g [] (Universe g)
  pc0 {c = x} w = inj₂ (any→elem {x} {Universe g} (universe-complete w))
  kc0 : KidCov g [] ((init g , nothing) ∷ [])
  kc0 ()

init-out : ∀ g → Any (_≡_ (init g)) (queued (reachable g))
init-out g =
  subst (λ ns → Any (_≡_ (init g)) (queued ns)) (sym (reachable-is g))
    (all-head (go-in-front g (Universe g) ((init g , nothing) ∷ [])
                (<-wellFounded-fast (length (Universe g)))
                (init-in g ∷ [])
                (u1 refl u0)))

reachable-complete : ∀ {g c} → Reach g (init g) c →
                     Any (_≡_ c) (queued (reachable g))
reachable-complete {g} r = close (init-out g) r
  where
  close : ∀ {a b} → Any (_≡_ a) (queued (reachable g)) →
          Reach g a b → Any (_≡_ b) (queued (reachable g))
  close has rhere = has
  close has (rstep {d = mid} step later) =
    close (out-closed g has step) later

------------------------------------------------------------------------
-- The path the search recorded. Each cons is the step `push` stored
-- as the parent of the child, so the list is the parent chain from
-- `init g`.
------------------------------------------------------------------------

data PathTo (g : Graph) (a : RConf) : RConf → List (Who × RConf) → Set where
  pt-here : PathTo g a a []
  pt-snoc : ∀ {b c w xs} → PathTo g a b xs → Step g b w c →
            PathTo g a c (xs ++ ((w , c) ∷ []))

AllPath : Graph → List Node → Set
AllPath g ns = All (λ n → Σ (List (Who × RConf)) (λ xs → PathTo g (init g) (confN n) xs)) ns

pushPath : ∀ {g} pool busy parent xs → PathTo g (init g) parent xs →
           ∀ ws → All (StepKid g parent) ws →
           AllPath g (push pool busy parent ws)
pushPath pool busy parent xs p [] [] = []
pushPath pool busy parent xs p ((w , d) ∷ ws) ((step , _) ∷ ss)
  with elemB d pool | elemB d busy
... | true | false =
  (xs ++ ((w , d) ∷ []) , pt-snoc p step) ∷
  pushPath pool (d ∷ busy) parent xs p ws ss
... | true | true = pushPath pool busy parent xs p ws ss
... | false | true = pushPath pool busy parent xs p ws ss
... | false | false = pushPath pool busy parent xs p ws ss

go-path : ∀ g pool fr acc mem unq → AllPath g fr →
          AllPath g (go g pool fr acc mem unq)
go-path g pool [] _ _ _ _ = []
go-path g pool (n ∷ rest) (acc rec) mem unq (pp ∷ pps) = body smaller refl
  where
  pool′ = del (confN n) pool
  steps = stepsOf g (confN n)
  busy = queued (n ∷ rest)
  kids = push pool′ busy (confN n) steps
  fr′ = rest ++ kids
  mem′ = all-++ (rest-in (confN n) pool rest (all-rest mem)
                          (nodes-¬ (confN n) rest (u-notin unq)))
                (push-ok pool′ busy (confN n) steps)
  unq′ = next-u {n} {rest} unq kids (push-uq pool′ busy (confN n) steps)
                                 (push-disj pool′ busy (confN n) steps)
  smaller = lt (length pool′) (length pool)
  kidP = pushPath pool′ busy (confN n) (proj₁ pp) (proj₂ pp) steps
                  (steps-all g (confN n))
  body : (b : Bool) → smaller ≡ b → AllPath g (go g pool (n ∷ rest) (acc rec) mem unq)
  body false eq = ⊥-elim (not-lt {c = confN n} {pool = pool} (all-head mem) eq)
  body true eq =
    subst (AllPath g) (sym (go-expand {g} {pool} {n} {rest} {mem} {unq} rec eq))
      (pp ∷ go-path g pool′ fr′ (rec (lt-sound (length pool′) (length pool) eq))
                       mem′ unq′ (all-++ pps kidP))

reachable-paths : ∀ g → AllPath g (reachable g)
reachable-paths g =
  subst (AllPath g) (sym (reachable-is g))
    (go-path g (Universe g) ((init g , nothing) ∷ [])
      (<-wellFounded-fast (length (Universe g)))
      (init-in g ∷ [])
      (u1 refl u0)
      (([] , pt-here) ∷ []))

trace-of : ∀ {g c p} → Any (_≡_ (c , p)) (reachable g) →
           Σ (List (Who × RConf)) (λ xs → PathTo g (init g) c xs)
trace-of {g} mem = all-lookup (reachable-paths g) mem

------------------------------------------------------------------------
-- The no-deadlock fact, decided from `reachable` alone. A configuration
-- the search emits is final or has a step, or it is a witness that
-- `NoStuck` fails.
------------------------------------------------------------------------

shape? : ∀ {g} (c : RConf) → Dec (Shape (view g c))
shape? {g} c = classify (view g c) refl
  where
  no-bad : ∀ {f} → Shape (VBad f) → ⊥
  no-bad ()
  classify : (v : View g c) → v ≡ view g c → Dec (Shape (view g c))
  classify (VFinal a b h) eq = yes (subst Shape eq sh-final)
  classify (VGo k ks) eq = yes (subst Shape eq sh-step)
  classify (VBad f) eq = no (λ sh → no-bad (subst Shape (sym eq) sh))

find-bad : ∀ {g} (ns : List Node) →
           Σ RConf (λ c → Any (_≡_ c) (queued ns) × ¬ Shape (view g c))
           ⊎ (∀ {c} → Any (_≡_ c) (queued ns) → Shape (view g c))
find-bad [] = inj₂ (λ ())
find-bad {g} (n ∷ ns) with shape? {g} (confN n)
find-bad {g} (n ∷ ns) | no ¬sh = inj₁ (confN n , here refl , ¬sh)
find-bad {g} (n ∷ ns) | yes sh = lift sh (find-bad ns)
  where
  extend : Shape (view g (confN n)) →
           (∀ {c} → Any (_≡_ c) (queued ns) → Shape (view g c)) →
           ∀ {c} → Any (_≡_ c) (queued (n ∷ ns)) → Shape (view g c)
  extend sh0 rest (here eq) = subst (λ x → Shape (view g x)) (sym eq) sh0
  extend sh0 rest (there p) = rest p
  lift : Shape (view g (confN n)) →
         Σ RConf (λ c → Any (_≡_ c) (queued ns) × ¬ Shape (view g c))
         ⊎ (∀ {c} → Any (_≡_ c) (queued ns) → Shape (view g c)) →
         Σ RConf (λ c → Any (_≡_ c) (queued (n ∷ ns)) × ¬ Shape (view g c))
         ⊎ (∀ {c} → Any (_≡_ c) (queued (n ∷ ns)) → Shape (view g c))
  lift _ (inj₁ (c , mem , ¬sh′)) = inj₁ (c , there mem , ¬sh′)
  lift sh0 (inj₂ rest) = inj₂ (extend sh0 rest)

decide-nostuck : (g : Graph) → Dec (NoStuck g)
decide-nostuck g with find-bad (reachable g)
... | inj₂ all = yes (λ r → all (reachable-complete r))
... | inj₁ (c , mem , ¬sh) = no (λ m → ¬sh (m (reachable-sound mem)))


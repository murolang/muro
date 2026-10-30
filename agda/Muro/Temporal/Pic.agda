------------------------------------------------------------------------
-- `walk` and `compile` agree on the fragment, and a process opens
-- onto its first action. A jump is not unfolded into its continuation.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Pic where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_; _≟_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; inspect; [_])
open import Relation.Nullary.Decidable.Core using (yes; no; Dec)

open import Muro.AsyncRec
  using ( Atom; aNat; aBit; aCon; Tag
        ; RProc; rdone; rstop; rput; recho; rget; rpick0; rpick1
        ; rcover; riget; rmget; rmu; rvar
        ; Block; bDone; bStop; bPut; bEcho; bGet; bPick0; bPick1; bCover; bIget; bMget
        ; COut; cok; cfail; Fault; fUnguarded; fFree
        ; compile; compileArms; addNames; lookupN; elemS
        ; materialise; findB; lookB
        ; REnv; VEnv
        )
open import Muro.Temporal.Bridge
  using ( Frag; fdone; fstop; fput; fget; fpick0; fpick1; fcover; figet; fmget; fmu; fvar
        ; FragPay; fnat; fbit; fcon; fecho
        ; FragArm; farm; FragArms; farms0; farms1
        ; elab; elabArms; echoOk; echoHere; once; occ; ∧-left; ∧-right
        )
open import Muro.Temporal.Source
  using ( Pay; pNat; pBit; pCon; pEcho
        ; Arm; aok; abad; SProc; sdone; sstop; sout; sput; sget; spick0; spick1
        ; scover; siget; smget; smu; svar
        ; W; mkW; EnvI; EnvP; addPend; lookupI; walk; walkArms; findS; bnames; bnamesArms
        ; Focus; f-done; f-stop; f-put; f-get; f-pick0; f-pick1; f-cover; f-iget; f-mget
        ; Unfold; u-done; u-stop; u-put; u-get; u-pick0; u-pick1; u-cover; u-iget; u-mget
        ; u-mu; u-var; Bound; b-here; b-there
        )
open W

------------------------------------------------------------------------
-- Arithmetic and list facts the slot counter needs.
------------------------------------------------------------------------

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

+-idr : ∀ n → n + zero ≡ n
+-idr zero = refl
+-idr (suc n) = cong suc (+-idr n)

++assoc : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++assoc [] ys zs = refl
++assoc (x ∷ xs) ys zs = cong (x ∷_) (++assoc xs ys zs)

len++ : ∀ {A : Set} (xs ys : List A) → length (xs ++ ys) ≡ length xs + length ys
len++ [] ys = refl
len++ (x ∷ xs) ys = cong suc (len++ xs ys)

------------------------------------------------------------------------
-- Arm entries, in the order `compileArms` records them.
------------------------------------------------------------------------

ents : List (String × W) → List (String × ℕ)
ents [] = []
ents ((y , w) ∷ ws) = (y , entry w) ∷ ents ws

------------------------------------------------------------------------
-- String equality, used by lookup and by the echo count.
------------------------------------------------------------------------

==-refl : ∀ x → (x == x) ≡ true
==-refl x with x ≟ x
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

==-sound : ∀ {x y} → (x == y) ≡ true → x ≡ y
==-sound {x} {y} eq with x ≟ y
... | yes p = p
... | no _ with eq
... | ()

false≡true : false ≡ true → ⊥
false≡true ()

------------------------------------------------------------------------
-- `findS` of the unique binder sits at the slot `compile` recorded.
------------------------------------------------------------------------

occS : String → List String → ℕ
occS x [] = zero
occS x (y ∷ ys) with x == y
... | true = suc (occS x ys)
... | false = occS x ys

once-skip : ∀ {x y ys} → (x == y) ≡ false → once x (y ∷ ys) ≡ once x ys
once-skip eq rewrite eq = refl

occ-skip : ∀ {x y ys} → (x == y) ≡ false → occS x (y ∷ ys) ≡ occS x ys
occ-skip eq rewrite eq = refl

find-skip : ∀ {x y ys} → (x == y) ≡ false →
            findS x (y ∷ ys) ≡ map suc (findS x ys)
find-skip {x} {y} {ys} eq rewrite eq with findS x ys
... | just k = refl
... | nothing = refl

occ-here : ∀ x ys → occ x (x ∷ ys) ≡ suc (occ x ys)
occ-here x ys rewrite ==-refl x = refl

occ-cat : ∀ pre rest x → Σ ℕ (λ k → occ x (pre ++ (x ∷ rest)) ≡ suc k)
occ-cat [] rest x = occ x rest , occ-here x rest
occ-cat (y ∷ pre) rest x = go (x == y) refl
  where
  go : (b : Bool) → (x == y) ≡ b → Σ ℕ (λ k → occ x ((y ∷ pre) ++ (x ∷ rest)) ≡ suc k)
  go true eq rewrite eq = occ x (pre ++ (x ∷ rest)) , refl
  go false eq rewrite eq = occ-cat pre rest x

twice : ∀ pre rest x → once x (x ∷ pre ++ (x ∷ rest)) ≡ false
twice pre rest x with occ-cat pre rest x
... | k , eq rewrite ==-refl x | eq = refl

find-at : ∀ pre x rest → once x (pre ++ (x ∷ rest)) ≡ true →
          findS x (pre ++ (x ∷ rest)) ≡ just (length pre)
find-at [] x rest ok rewrite ==-refl x = refl
find-at (y ∷ pre) x rest ok = go (x == y) refl
  where
  hit : (x == y) ≡ true → once x (y ∷ pre ++ (x ∷ rest)) ≡ false
  hit eqy rewrite ==-sound eqy = twice pre rest y
  go : (b : Bool) → (x == y) ≡ b →
       findS x (y ∷ pre ++ (x ∷ rest)) ≡ just (suc (length pre))
  go true eq = ⊥-elim (false≡true (trans (sym (hit eq)) ok))
  go false eq =
    trans (find-skip eq)
      (cong (map suc) (find-at pre x rest (trans (sym (once-skip eq)) ok)))

+-assoc : ∀ m n p → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)

++[] : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++[] [] = refl
++[] (x ∷ xs) = cong (x ∷_) (++[] xs)

------------------------------------------------------------------------
-- Block indices compiled from `lo` up to `hi`, in order, with no gaps.
------------------------------------------------------------------------

data _∈_ {A : Set} (x : A) : List A → Set where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

data Ord : ℕ → ℕ → List (ℕ × Block) → Set where
  o0 : ∀ {n} → Ord n n []
  o1 : ∀ {n hi b bs} → Ord (suc n) hi bs → Ord n hi ((n , b) ∷ bs)

findB-here : ∀ i b bs → findB i ((i , b) ∷ bs) ≡ b
findB-here i b bs with i ≟ℕ i
... | yes refl = refl
... | no ¬eq = ⊥-elim (¬eq refl)

findB-skip : ∀ i j b bs → i ≢ j → findB i ((j , b) ∷ bs) ≡ findB i bs
findB-skip i j b bs neq with i ≟ℕ j
... | yes eq = ⊥-elim (neq eq)
... | no _ = refl

n<n : ∀ {n} → suc n ≤ n → ⊥
n<n {suc n} (s≤s le) = n<n le
n<n {zero} ()

i≢lo : ∀ {n i} → suc n ≤ i → i ≢ n
i≢lo le refl = n<n le

n≤1+n : ∀ n → n ≤ suc n
n≤1+n zero = z≤n
n≤1+n (suc n) = s≤s (n≤1+n n)

ord-end : ∀ {lo hi bs} → Ord lo hi bs → lo ≤ hi
ord-end o0 = ≤-refl
ord-end (o1 od) = ≤-trans (n≤1+n _) (ord-end od)

ord-lo : ∀ {lo hi i b bs} → Ord lo hi bs → (i , b) ∈ bs → lo ≤ i
ord-lo (o1 _) here = ≤-refl
ord-lo (o1 od) (there mem) = ≤-trans (n≤1+n _) (ord-lo od mem)

ord-hi : ∀ {lo hi i b bs} → Ord lo hi bs → (i , b) ∈ bs → i < hi
ord-hi (o1 od) here = ord-end od
ord-hi (o1 od) (there mem) = ord-hi od mem

ord-find : ∀ {lo hi i b bs} → Ord lo hi bs → (i , b) ∈ bs → findB i bs ≡ b
ord-find (o1 {n} {b = b0} od) here = findB-here n b0 _
ord-find (o1 {n} {b = b0} od) (there mem) =
  trans (findB-skip _ n b0 _ (i≢lo (ord-lo od mem))) (ord-find od mem)

ord-cat : ∀ {a b c xs ys} → Ord a b xs → Ord b c ys → Ord a c (xs ++ ys)
ord-cat o0 od = od
ord-cat (o1 od) od2 = o1 (ord-cat od od2)

look-mat : ∀ r start bs i → i < r →
           lookB (materialise r start bs) i ≡ just (findB (start + i) bs)
look-mat (suc r) start bs zero (s≤s _) rewrite +-idr start = refl
look-mat (suc r) start bs (suc i) (s≤s le) rewrite +-suc start i =
  look-mat r (suc start) bs i le
look-mat zero _ _ _ ()

root-at : ∀ {nL bs i b} → Ord zero nL bs → (i , b) ∈ bs →
          lookB (materialise nL zero bs) i ≡ just b
root-at od mem =
  trans (look-mat _ zero _ _ (ord-hi od mem)) (cong just (ord-find od mem))

------------------------------------------------------------------------
-- `walk` and `compile` return the same counters, and the blocks occupy
-- the half-open interval from the block counter to `next`.
------------------------------------------------------------------------

data Same (n0 s0 : ℕ) (bound : List String) : Maybe W → COut → Set where
  both-bad : ∀ {f} → Same n0 s0 bound nothing (cfail f)
  both-ok : ∀ w bs →
            slotN w ≡ s0 + length bound →
            Ord n0 (next w) bs →
            Same n0 s0 bound (just w) (cok (entry w) (next w) (slotN w) bs)

data SameA (n0 s0 : ℕ) (bound : List String) :
     Maybe (List (String × W) × ℕ × ℕ) →
     (COut × List (String × ℕ) × List (ℕ × Block)) → Set where
  arms-bad : ∀ {f} → SameA n0 s0 bound nothing (cfail f , [] , [])
  arms-ok : ∀ ws n2 s2 bs →
            s2 ≡ s0 + length bound →
            Ord n0 n2 bs →
            SameA n0 s0 bound (just (ws , n2 , s2))
              (cok n2 n2 s2 [] , ents ws , bs)

------------------------------------------------------------------------
-- The jump environment. `compile` drops the slot `walk` keeps.
------------------------------------------------------------------------

data ERel : EnvI → REnv → Set where
  er0 : ERel [] []
  er1 : ∀ {x i s ρ r} → ERel ρ r → ERel ((x , i , s) ∷ ρ) ((x , i) ∷ r)

add-rel : ∀ xs n s {ρ r} → ERel ρ r →
          ERel (addPend xs n s ρ) (addNames xs n r)
add-rel [] n s rel = rel
add-rel (x ∷ xs) n s rel = er1 (add-rel xs n s rel)

data Seen (ρ : EnvI) (r : REnv) (x : String) : Set where
  seen-no : lookupI x ρ ≡ nothing → lookupN x r ≡ nothing → Seen ρ r x
  seen-yes : ∀ i s0 → lookupI x ρ ≡ just (i , s0) → lookupN x r ≡ just i →
             Seen ρ r x

lookup-rel : ∀ {ρ r} x → ERel ρ r → Seen ρ r x
lookup-rel x er0 = seen-no refl refl
lookup-rel x (er1 {y} {i} {s} {ρ} {r} rel) = go (x == y) refl
  where
  lkI : (x == y) ≡ true → lookupI x ((y , i , s) ∷ ρ) ≡ just (i , s)
  lkI eq rewrite eq = refl
  lkN : (x == y) ≡ true → lookupN x ((y , i) ∷ r) ≡ just i
  lkN eq rewrite eq = refl
  skipI : (x == y) ≡ false → lookupI x ((y , i , s) ∷ ρ) ≡ lookupI x ρ
  skipI eq rewrite eq = refl
  skipN : (x == y) ≡ false → lookupN x ((y , i) ∷ r) ≡ lookupN x r
  skipN eq rewrite eq = refl
  go : (b : Bool) → (x == y) ≡ b → Seen ((y , i , s) ∷ ρ) ((y , i) ∷ r) x
  go true eq = seen-yes i s (lkI eq) (lkN eq)
  go false eq = skip eq (lookup-rel x rel)
    where
    skip : (x == y) ≡ false → Seen ρ r x → Seen ((y , i , s) ∷ ρ) ((y , i) ∷ r) x
    skip eqf (seen-no eqi eqn) = seen-no (trans (skipI eqf) eqi) (trans (skipN eqf) eqn)
    skip eqf (seen-yes j s0 eqi eqn) =
      seen-yes j s0 (trans (skipI eqf) eqi) (trans (skipN eqf) eqn)

------------------------------------------------------------------------
-- An echo of a unique in-scope name reads the slot `compile` stored.
------------------------------------------------------------------------

EchoRel : VEnv → List String → List String → Set
EchoRel venv ns scope =
  ∀ x → elemS x scope ≡ true → once x ns ≡ true →
        Σ ℕ (λ s → lookupN x venv ≡ just s × findS x ns ≡ just s)

echo-empty : ∀ venv ns → EchoRel venv ns []
echo-empty _ _ _ () _

skip-mem : ∀ {y x scope} → (y == x) ≡ false →
           elemS y (x ∷ scope) ≡ true → elemS y scope ≡ true
skip-mem eq m rewrite eq = m

skip-lk : ∀ {y x s venv} → (y == x) ≡ false →
          lookupN y ((x , s) ∷ venv) ≡ lookupN y venv
skip-lk eq rewrite eq = refl

echo-extend : ∀ {venv ns scope} pre rest x s →
              EchoRel venv ns scope →
              ns ≡ pre ++ (x ∷ rest) →
              s ≡ length pre →
              EchoRel ((x , s) ∷ venv) ns (x ∷ scope)
echo-extend {venv} {ns} pre rest x s rel eqns eqs y mem onceY = go (y == x) refl
  where
  go : (b : Bool) → (y == x) ≡ b →
       Σ ℕ (λ s′ → lookupN y ((x , s) ∷ venv) ≡ just s′ × findS y ns ≡ just s′)
  go true eq = hit (==-sound eq)
    where
    hit : y ≡ x →
          Σ ℕ (λ s′ → lookupN y ((x , s) ∷ venv) ≡ just s′ × findS y ns ≡ just s′)
    hit refl rewrite eq | eqs | eqns =
      length pre , refl , find-at pre y rest onceY
  go false eq =
    let s′ , lk , fd = rel y (skip-mem eq mem) onceY
    in s′ , trans (skip-lk eq) lk , fd

------------------------------------------------------------------------
-- `walk` depends on the jump environment only through lookup.
------------------------------------------------------------------------

EnvEq : EnvI → EnvI → Set
EnvEq ρ1 ρ2 = ∀ x → lookupI x ρ1 ≡ lookupI x ρ2

add-eq : ∀ xs n s {ρ1 ρ2} → EnvEq ρ1 ρ2 →
         EnvEq (addPend xs n s ρ1) (addPend xs n s ρ2)
add-eq [] n s eq = eq
add-eq (x ∷ xs) n s {ρ1} {ρ2} eq y = go (y == x) refl
  where
  go : (b : Bool) → (y == x) ≡ b →
       lookupI y ((x , n , s) ∷ addPend xs n s ρ1) ≡
       lookupI y ((x , n , s) ∷ addPend xs n s ρ2)
  go true eqy rewrite eqy = refl
  go false eqy rewrite eqy = add-eq xs n s {ρ1} {ρ2} eq y

var-true : ∀ n s (y : String) pend ρ1 ρ2 → elemS y pend ≡ true →
           walk pend ρ1 (svar y) n s ≡ walk pend ρ2 (svar y) n s
var-true n s y pend ρ1 ρ2 eq rewrite eq = refl

var-false : ∀ n s (y : String) pend ρ1 ρ2 → elemS y pend ≡ false →
            lookupI y ρ1 ≡ lookupI y ρ2 →
            walk pend ρ1 (svar y) n s ≡ walk pend ρ2 (svar y) n s
var-false n s y pend ρ1 ρ2 eqe eql rewrite eqe | eql = refl

var-cong : ∀ n s y pend ρ1 ρ2 → EnvEq ρ1 ρ2 →
           walk pend ρ1 (svar y) n s ≡ walk pend ρ2 (svar y) n s
var-cong n s y pend ρ1 ρ2 eq = go (elemS y pend) refl
  where
  go : (b : Bool) → elemS y pend ≡ b →
       walk pend ρ1 (svar y) n s ≡ walk pend ρ2 (svar y) n s
  go true eqe = var-true n s y pend ρ1 ρ2 eqe
  go false eqe = var-false n s y pend ρ1 ρ2 eqe (eq y)

one-cong : ∀ {n s a p pend ρ1 ρ2} →
           walk [] (addPend pend n s ρ1) p (suc n) s ≡
           walk [] (addPend pend n s ρ2) p (suc n) s →
           walk pend ρ1 (sput a p) n s ≡ walk pend ρ2 (sput a p) n s
one-cong eq rewrite eq = refl

get-walk : ∀ {n s t x p pend ρ1 ρ2} →
           walk [] (addPend pend n s ρ1) p (suc n) (suc s) ≡
           walk [] (addPend pend n s ρ2) p (suc n) (suc s) →
           walk pend ρ1 (sget t x p) n s ≡ walk pend ρ2 (sget t x p) n s
get-walk eq rewrite eq = refl

pick0-walk : ∀ {n s p pend ρ1 ρ2} →
             walk [] (addPend pend n s ρ1) p (suc n) s ≡
             walk [] (addPend pend n s ρ2) p (suc n) s →
             walk pend ρ1 (spick0 p) n s ≡ walk pend ρ2 (spick0 p) n s
pick0-walk eq rewrite eq = refl

pick1-walk : ∀ {n s p pend ρ1 ρ2} →
             walk [] (addPend pend n s ρ1) p (suc n) s ≡
             walk [] (addPend pend n s ρ2) p (suc n) s →
             walk pend ρ1 (spick1 p) n s ≡ walk pend ρ2 (spick1 p) n s
pick1-walk eq rewrite eq = refl

cover-walk : ∀ {n s p q pend ρ1 ρ2} →
             walk [] (addPend pend n s ρ1) p (suc n) s ≡
             walk [] (addPend pend n s ρ2) p (suc n) s →
             (∀ n1 s1 →
                walk [] (addPend pend n s ρ1) q n1 s1 ≡
                walk [] (addPend pend n s ρ2) q n1 s1) →
             walk pend ρ1 (scover p q) n s ≡ walk pend ρ2 (scover p q) n s
cover-walk {n} {s} {p} {q} {pend} {ρ1} {ρ2} eqp eqq
  with walk [] (addPend pend n s ρ1) p (suc n) s
     | walk [] (addPend pend n s ρ2) p (suc n) s
     | eqp
... | just w1 | .(just w1) | refl rewrite eqq (next w1) (slotN w1) = refl
... | nothing | .nothing | refl = refl

iget-walk : ∀ {n s x p q pend ρ1 ρ2} →
            walk [] (addPend pend n s ρ1) p (suc n) (suc s) ≡
            walk [] (addPend pend n s ρ2) p (suc n) (suc s) →
            (∀ n1 s1 →
               walk [] (addPend pend n s ρ1) q n1 s1 ≡
               walk [] (addPend pend n s ρ2) q n1 s1) →
            walk pend ρ1 (siget x p q) n s ≡ walk pend ρ2 (siget x p q) n s
iget-walk {n} {s} {x} {p} {q} {pend} {ρ1} {ρ2} eqp eqq
  with walk [] (addPend pend n s ρ1) p (suc n) (suc s)
     | walk [] (addPend pend n s ρ2) p (suc n) (suc s)
     | eqp
... | just w1 | .(just w1) | refl rewrite eqq (next w1) (slotN w1) = refl
... | nothing | .nothing | refl = refl

mget-walk : ∀ {n s t x as pend ρ1 ρ2} →
            walkArms [] (addPend pend n s ρ1) as (suc n) (suc s) ≡
            walkArms [] (addPend pend n s ρ2) as (suc n) (suc s) →
            walk pend ρ1 (smget t x as) n s ≡ walk pend ρ2 (smget t x as) n s
mget-walk eq rewrite eq = refl

mutual
  arms-walk : ∀ pend ρ1 ρ2 as n s → EnvEq ρ1 ρ2 →
              walkArms pend ρ1 as n s ≡ walkArms pend ρ2 as n s
  arms-walk pend ρ1 ρ2 [] n s eq = refl
  arms-walk pend ρ1 ρ2 (abad ∷ as) n s eq = refl
  arms-walk pend ρ1 ρ2 (aok y p ∷ as) n s eq =
    step (walk-cong pend ρ1 ρ2 p n s eq)
         (λ n1 s1 → arms-walk pend ρ1 ρ2 as n1 s1 eq)
    where
    step : walk pend ρ1 p n s ≡ walk pend ρ2 p n s →
           (∀ n1 s1 → walkArms pend ρ1 as n1 s1 ≡ walkArms pend ρ2 as n1 s1) →
           walkArms pend ρ1 (aok y p ∷ as) n s ≡ walkArms pend ρ2 (aok y p ∷ as) n s
    step eqp eqa
      with walk pend ρ1 p n s | walk pend ρ2 p n s | eqp
    ... | just w | .(just w) | refl rewrite eqa (next w) (slotN w) = refl
    ... | nothing | .nothing | refl = refl

  walk-cong : ∀ pend ρ1 ρ2 P n s → EnvEq ρ1 ρ2 →
              walk pend ρ1 P n s ≡ walk pend ρ2 P n s
  walk-cong pend ρ1 ρ2 (smu x p) n s eq = walk-cong (x ∷ pend) ρ1 ρ2 p n s eq
  walk-cong pend ρ1 ρ2 (svar y) n s eq = var-cong n s y pend ρ1 ρ2 eq
  walk-cong pend ρ1 ρ2 sdone n s eq = refl
  walk-cong pend ρ1 ρ2 sstop n s eq = refl
  walk-cong pend ρ1 ρ2 sout n s eq = refl
  walk-cong pend ρ1 ρ2 (sput a p) n s eq =
    one-cong {n} {s} {a} {p} {pend} {ρ1} {ρ2}
      (walk-cong [] (addPend pend n s ρ1) (addPend pend n s ρ2) p (suc n) s
         (add-eq pend n s eq))
  walk-cong pend ρ1 ρ2 (sget t x p) n s eq =
    get-walk {n} {s} {t} {x} {p} {pend} {ρ1} {ρ2}
      (walk-cong [] (addPend pend n s ρ1) (addPend pend n s ρ2) p (suc n) (suc s)
         (add-eq pend n s eq))
  walk-cong pend ρ1 ρ2 (spick0 p) n s eq =
    pick0-walk {n} {s} {p} {pend} {ρ1} {ρ2}
      (walk-cong [] (addPend pend n s ρ1) (addPend pend n s ρ2) p (suc n) s
         (add-eq pend n s eq))
  walk-cong pend ρ1 ρ2 (spick1 p) n s eq =
    pick1-walk {n} {s} {p} {pend} {ρ1} {ρ2}
      (walk-cong [] (addPend pend n s ρ1) (addPend pend n s ρ2) p (suc n) s
         (add-eq pend n s eq))
  walk-cong pend ρ1 ρ2 (scover p q) n s eq =
    cover-walk {n} {s} {p} {q} {pend} {ρ1} {ρ2}
      (walk-cong [] (addPend pend n s ρ1) (addPend pend n s ρ2) p (suc n) s (add-eq pend n s eq))
      (λ n1 s1 →
         walk-cong [] (addPend pend n s ρ1) (addPend pend n s ρ2) q n1 s1 (add-eq pend n s eq))
  walk-cong pend ρ1 ρ2 (siget x p q) n s eq =
    iget-walk {n} {s} {x} {p} {q} {pend} {ρ1} {ρ2}
      (walk-cong [] (addPend pend n s ρ1) (addPend pend n s ρ2) p (suc n) (suc s) (add-eq pend n s eq))
      (λ n1 s1 →
         walk-cong [] (addPend pend n s ρ1) (addPend pend n s ρ2) q n1 s1 (add-eq pend n s eq))
  walk-cong pend ρ1 ρ2 (smget t x as) n s eq =
    mget-walk {n} {s} {t} {x} {as} {pend} {ρ1} {ρ2}
      (arms-walk [] (addPend pend n s ρ1) (addPend pend n s ρ2) as (suc n) (suc s)
         (add-eq pend n s eq))

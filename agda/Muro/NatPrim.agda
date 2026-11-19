------------------------------------------------------------------------
-- Library Nat runs and the integer operations Elixir emits for them.
--
-- `Muro.Emit.NatPrim` replaces a run whose type and body are exactly a
-- library definition with an Elixir integer expression. That
-- replacement is trusted. This module states the two sides and proves
-- them equal on every natural number.
--
-- Each `…M` below is the library definition, transcribed clause for
-- clause from `lib/muro/prelude.muro`, `lib/muro/std/le.muro`, and
-- `lib/muro/std/ord.muro`. The transcription is not checked against the
-- `.muro` text. Each `host…` is the emitted Elixir expression over ℤ,
-- because Elixir integers are signed: `minus` is `max(x0 - x1, 0)`, and
-- the subtraction can go below zero before the max. The emitted function
-- is guarded on `is_integer(x) and x >= 0`, so it is only called at
-- `+ n`. That guard, and Elixir integer arithmetic being ℤ arithmetic,
-- are the remaining trust.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.NatPrim where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; not)
open import Data.Integer.Base as ℤ using (ℤ; +_; -_; -[1+_]; _⊖_)
open import Data.Integer.Properties using ([+m]-[+n]≡m⊖n; ⊖-≥; ⊖-<)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; _∸_)
open import Data.Nat.Properties as ℕP using (m≤n⇒m∸n≡0; <⇒≤; ≮⇒≥; ⊔-identityʳ)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; trans; sym)

------------------------------------------------------------------------
-- The library definitions.
------------------------------------------------------------------------

predM : ℕ → ℕ
predM zero    = zero
predM (suc m) = m

plusM : ℕ → ℕ → ℕ
plusM zero    m = m
plusM (suc n) m = suc (plusM n m)

maxM : ℕ → ℕ → ℕ
maxM zero    n       = n
maxM (suc p) zero    = suc p
maxM (suc p) (suc q) = suc (maxM p q)

minM : ℕ → ℕ → ℕ
minM zero    n       = zero
minM (suc p) zero    = zero
minM (suc p) (suc q) = suc (minM p q)

-- `minus` matches its second argument first.
minusM : ℕ → ℕ → ℕ
minusM m       zero    = m
minusM zero    (suc q) = zero
minusM (suc p) (suc q) = minusM p q

data Ordering : Set where
  lt eq gt : Ordering

compareM : ℕ → ℕ → Ordering
compareM zero    zero    = eq
compareM zero    (suc _) = lt
compareM (suc p) zero    = gt
compareM (suc p) (suc q) = compareM p q

------------------------------------------------------------------------
-- The emitted Elixir expressions, over ℤ.
------------------------------------------------------------------------

-- Kernel.max(x0 - 1, 0)
hostPred : ℤ → ℤ
hostPred x = (x ℤ.- + 1) ℤ.⊔ + 0

-- x0 + x1
hostPlus : ℤ → ℤ → ℤ
hostPlus x y = x ℤ.+ y

-- Kernel.max(x0, x1)
hostMax : ℤ → ℤ → ℤ
hostMax x y = x ℤ.⊔ y

-- Kernel.min(x0, x1)
hostMin : ℤ → ℤ → ℤ
hostMin x y = x ℤ.⊓ y

-- Kernel.max(x0 - x1, 0)
hostMinus : ℤ → ℤ → ℤ
hostMinus x y = (x ℤ.- y) ℤ.⊔ + 0

-- cond do x0 < x1 -> :lt; x0 == x1 -> :eq; true -> :gt end
-- x < y is not (y ≤ x), and x == y is x ≤ y once x < y is false.
hostCompare : ℤ → ℤ → Ordering
hostCompare x y =
  if not (y ℤ.≤ᵇ x) then lt else (if x ℤ.≤ᵇ y then eq else gt)

------------------------------------------------------------------------
-- Each library definition is the ℕ operation it names.
------------------------------------------------------------------------

predM≡∸1 : ∀ m → predM m ≡ m ∸ 1
predM≡∸1 zero    = refl
predM≡∸1 (suc m) = refl

plusM≡+ : ∀ n m → plusM n m ≡ n ℕ.+ m
plusM≡+ zero    m = refl
plusM≡+ (suc n) m = cong suc (plusM≡+ n m)

maxM≡⊔ : ∀ m n → maxM m n ≡ m ℕ.⊔ n
maxM≡⊔ zero    n       = refl
maxM≡⊔ (suc p) zero    = refl
maxM≡⊔ (suc p) (suc q) = cong suc (maxM≡⊔ p q)

minM≡⊓ : ∀ m n → minM m n ≡ m ℕ.⊓ n
minM≡⊓ zero    n       = refl
minM≡⊓ (suc p) zero    = refl
minM≡⊓ (suc p) (suc q) = cong suc (minM≡⊓ p q)

minusM≡∸ : ∀ m n → minusM m n ≡ m ∸ n
minusM≡∸ m       zero    = refl
minusM≡∸ zero    (suc q) = refl
minusM≡∸ (suc p) (suc q) = minusM≡∸ p q

------------------------------------------------------------------------
-- Clamping a difference at zero is truncated subtraction.
------------------------------------------------------------------------

neg⊔0 : ∀ k → (- (+ k)) ℤ.⊔ + 0 ≡ + 0
neg⊔0 zero    = refl
neg⊔0 (suc k) = refl

⊖⊔0 : ∀ m n → (m ⊖ n) ℤ.⊔ + 0 ≡ + (m ∸ n)
⊖⊔0 m n with m ℕP.<? n
... | yes m<n =
  trans (cong (ℤ._⊔ + 0) (⊖-< m<n))
        (trans (neg⊔0 (n ∸ m)) (cong +_ (sym (m≤n⇒m∸n≡0 (<⇒≤ m<n)))))
... | no m≮n =
  trans (cong (ℤ._⊔ + 0) (⊖-≥ (≮⇒≥ m≮n))) (cong +_ (⊔-identityʳ (m ∸ n)))

------------------------------------------------------------------------
-- The emitted expression at a natural number is the library definition.
------------------------------------------------------------------------

pred-host : ∀ m → hostPred (+ m) ≡ + predM m
pred-host m =
  trans (cong (ℤ._⊔ + 0) ([+m]-[+n]≡m⊖n m 1))
        (trans (⊖⊔0 m 1) (cong +_ (sym (predM≡∸1 m))))

plus-host : ∀ n m → hostPlus (+ n) (+ m) ≡ + plusM n m
plus-host n m = cong +_ (sym (plusM≡+ n m))

max-host : ∀ m n → hostMax (+ m) (+ n) ≡ + maxM m n
max-host m n = cong +_ (sym (maxM≡⊔ m n))

min-host : ∀ m n → hostMin (+ m) (+ n) ≡ + minM m n
min-host m n = cong +_ (sym (minM≡⊓ m n))

minus-host : ∀ m n → hostMinus (+ m) (+ n) ≡ + minusM m n
minus-host m n =
  trans (cong (ℤ._⊔ + 0) ([+m]-[+n]≡m⊖n m n))
        (trans (⊖⊔0 m n) (cong +_ (sym (minusM≡∸ m n))))

-- On naturals, the host comparison steps down both successors.
≤ᵇ-suc : ∀ m n → (suc m ℕ.≤ᵇ suc n) ≡ (m ℕ.≤ᵇ n)
≤ᵇ-suc zero    n = refl
≤ᵇ-suc (suc m) n = refl

compare-host : ∀ m n → hostCompare (+ m) (+ n) ≡ compareM m n
compare-host zero    zero    = refl
compare-host zero    (suc n) = refl
compare-host (suc m) zero    = refl
compare-host (suc m) (suc n)
  rewrite ≤ᵇ-suc n m | ≤ᵇ-suc m n = compare-host m n

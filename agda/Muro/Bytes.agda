------------------------------------------------------------------------
-- An octet sequence. The Elixir kernel spells the type :bytes and the
-- view :slice. A literal is {:blit, octets}. Concatenation, length,
-- equality, indexing, and slicing are the operations below. A backend
-- emits a pointer and a length. This list is the meaning. It is not a
-- Tm constructor. An octet is below 256.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Bytes where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_; _∸_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

Bytes : Set
Bytes = List ℕ

octet : ℕ → Bool
octet n = n <ᵇ 256

cat : Bytes → Bytes → Bytes
cat = _++_

len : Bytes → ℕ
len = length

eq : Bytes → Bytes → Bool
eq [] [] = true
eq [] (_ ∷ _) = false
eq (_ ∷ _) [] = false
eq (x ∷ xs) (y ∷ ys) = if x ≡ᵇ y then eq xs ys else false

data Opt (A : Set) : Set where
  none : Opt A
  some : A → Opt A

get : Bytes → ℕ → Opt ℕ
get [] _ = none
get (x ∷ _) zero = some x
get (_ ∷ xs) (suc i) = get xs i

take : ℕ → Bytes → Bytes
take zero _ = []
take (suc _) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : ℕ → Bytes → Bytes
drop zero xs = xs
drop (suc _) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

-- Out of range is empty. An in-range span is those octets.
slice : Bytes → ℕ → ℕ → Bytes
slice xs off n =
  if (off ≤ᵇ length xs) ∧ (n ≤ᵇ (length xs ∸ off))
  then take n (drop off xs)
  else []

-- The prefix before the first matching octet, or the whole sequence.
until : Bytes → ℕ → Bytes
until [] _ = []
until (x ∷ xs) b = if x ≡ᵇ b then [] else x ∷ until xs b

-- The suffix strictly after the first matching octet, or empty.
aft : Bytes → ℕ → Bytes
aft [] _ = []
aft (x ∷ xs) b = if x ≡ᵇ b then xs else aft xs b

fold : {A : Set} → (ℕ → Bytes → A → A) → A → Bytes → A
fold _ z [] = z
fold f z (x ∷ xs) = fold f (f x xs z) xs

hello : Bytes
hello = 104 ∷ 101 ∷ 108 ∷ 108 ∷ 111 ∷ []

cat-hello : cat (104 ∷ 101 ∷ 108 ∷ []) (108 ∷ 111 ∷ []) ≡ hello
cat-hello = refl

len-ff : len (255 ∷ []) ≡ 1
len-ff = refl

len-hello : len hello ≡ 5
len-hello = refl

eq-yes : eq hello hello ≡ true
eq-yes = refl

eq-no : eq hello (97 ∷ []) ≡ false
eq-no = refl

get-h : get hello 0 ≡ some 104
get-h = refl

get-miss : get hello 5 ≡ none
get-miss = refl

slice-ell : slice hello 1 3 ≡ (101 ∷ 108 ∷ 108 ∷ [])
slice-ell = refl

slice-past : slice hello 6 1 ≡ []
slice-past = refl

slice-empty : slice hello 2 0 ≡ []
slice-empty = refl

until-get : until hello 32 ≡ hello
until-get = refl

until-space : until (71 ∷ 69 ∷ 84 ∷ 32 ∷ 47 ∷ []) 32 ≡ (71 ∷ 69 ∷ 84 ∷ [])
until-space = refl

aft-space : aft (71 ∷ 69 ∷ 84 ∷ 32 ∷ 47 ∷ []) 32 ≡ (47 ∷ [])
aft-space = refl

aft-miss : aft hello 32 ≡ []
aft-miss = refl

octet-ff : octet 255 ≡ true
octet-ff = refl

octet-past : octet 256 ≡ false
octet-past = refl

fold-sum : fold (λ x _ n → n + x) 0 (1 ∷ 2 ∷ []) ≡ 3
fold-sum = refl

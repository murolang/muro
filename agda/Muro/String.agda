------------------------------------------------------------------------
-- A string is a list of Unicode scalars. The Elixir kernel spells the
-- type :string, a literal {:slit, utf8}, concatenation {:scat, a, b},
-- length {:slen, a}, and equality {:seq, a, b} as a WBool. A backend
-- emits a host string. This list is the meaning. It is not a Tm
-- constructor. A scalar is at most 10FFFF₁₆ and is not a surrogate.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.String where

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Nat.Base using (ℕ; _≡ᵇ_; _<ᵇ_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

String : Set
String = List ℕ

cat : String → String → String
cat = _++_

len : String → ℕ
len = length

eq : String → String → Bool
eq [] [] = true
eq [] (_ ∷ _) = false
eq (_ ∷ _) [] = false
eq (x ∷ xs) (y ∷ ys) = if x ≡ᵇ y then eq xs ys else false

-- n < 1114112 and (n < 55296 or n > 57343).
isScalar : ℕ → Bool
isScalar n = (n <ᵇ 1114112) ∧ ((n <ᵇ 55296) ∨ (57343 <ᵇ n))

hello : String
hello = 104 ∷ 101 ∷ 108 ∷ 108 ∷ 111 ∷ []

cat-hello : cat (104 ∷ 101 ∷ 108 ∷ []) (108 ∷ 111 ∷ []) ≡ hello
cat-hello = refl

len-eacute : len (233 ∷ []) ≡ 1
len-eacute = refl

len-combining : len (101 ∷ 769 ∷ []) ≡ 2
len-combining = refl

len-wave : len (128075 ∷ []) ≡ 1
len-wave = refl

eq-yes : eq hello hello ≡ true
eq-yes = refl

eq-no : eq hello (119 ∷ 111 ∷ 114 ∷ 108 ∷ 100 ∷ []) ≡ false
eq-no = refl

scalar-nul : isScalar 0 ≡ true
scalar-nul = refl

scalar-eacute : isScalar 233 ≡ true
scalar-eacute = refl

scalar-wave : isScalar 128075 ≡ true
scalar-wave = refl

surrogate-not : isScalar 55296 ≡ false
surrogate-not = refl

past-not : isScalar 1114112 ≡ false
past-not = refl

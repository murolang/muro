------------------------------------------------------------------------
-- Match on WBool and Opt. The Elixir spelling is mwbool and mopt.
-- wtrue reduces to the first arm and wfalse to the second.
-- wsome instantiates the payload binder. wnone takes the second arm.
-- Nothing here is added to Tm.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.WordElim where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

data WBool : Set where
  wtrue : WBool
  wfalse : WBool

data Opt (A : Set) : Set where
  wsome : A → Opt A
  wnone : Opt A

elimBool : {P : WBool → Set} → (b : WBool) → P wtrue → P wfalse → P b
elimBool wtrue t _ = t
elimBool wfalse _ f = f

elimOpt : {A : Set} {P : Opt A → Set} → (o : Opt A) → ((a : A) → P (wsome a)) → P wnone → P o
elimOpt (wsome a) s _ = s a
elimOpt wnone _ n = n

pick : WBool → ℕ
pick b = elimBool b 1 0

unwrap : Opt ℕ → ℕ
unwrap o = elimOpt o (λ n → n) 0

pick-true : pick wtrue ≡ 1
pick-true = refl

pick-false : pick wfalse ≡ 0
pick-false = refl

unwrap-some : unwrap (wsome 1) ≡ 1
unwrap-some = refl

unwrap-none : unwrap wnone ≡ 0
unwrap-none = refl

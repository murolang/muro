------------------------------------------------------------------------
-- Constructor tags. `tmTag` numbers the constructors of Tm; `TmShape k t`
-- says t is built from constructor number k. The checker compares tags
-- before structural comparison (synEq, convN) so that proofs about
-- those functions can case on two terms of equal tag without listing
-- every off-diagonal pair.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Tag where

open import Data.Nat.Base using (ℕ)
open import Muro.Syntax

tmTag : ∀ {n} → Tm n → ℕ
tmTag (var _) = 0
tmTag typ = 1
tmTag (pi _ _ _) = 2
tmTag (lam _ _ _) = 3
tmTag (app _ _) = 4
tmTag nat = 5
tmTag ze = 6
tmTag (su _) = 7
tmTag unit = 8
tmTag one = 9
tmTag empty = 10
tmTag (dty _) = 11
tmTag (ctor _ _) = 12
tmTag (mData _ _ _) = 13
tmTag (mNat _ _ _ _) = 14
tmTag (mEmp _ _) = 15
tmTag (mUnit _ _ _) = 16
tmTag (idt _ _ _) = 17
tmTag rfl = 18
tmTag (rwt _ _ _) = 19
tmTag (def _) = 20
tmTag (ann _ _) = 21
tmTag (prod _ _) = 22
tmTag (pair _ _) = 23
tmTag (nu _) = 26
tmTag (unf _ _) = 27
tmTag (ucons _) = 28
tmTag i64 = 29
tmTag f32ty = 30
tmTag (tensor _ _) = 31
tmTag (addi _ _) = 32
tmTag (muli _ _) = 33
tmTag (addt _ _) = 34
tmTag (toi64 _) = 35
tmTag (packi _ _) = 36
tmTag (letp _ _) = 37
tmTag (word _ _) = 38

data TmShape {n} : ℕ → Tm n → Set where
  sh-var : ∀ {a} → TmShape 0 (var a)
  sh-typ : TmShape 1 typ
  sh-pi : ∀ {a b c} → TmShape 2 (pi a b c)
  sh-lam : ∀ {a b c} → TmShape 3 (lam a b c)
  sh-app : ∀ {a b} → TmShape 4 (app a b)
  sh-nat : TmShape 5 nat
  sh-ze : TmShape 6 ze
  sh-su : ∀ {a} → TmShape 7 (su a)
  sh-unit : TmShape 8 unit
  sh-one : TmShape 9 one
  sh-empty : TmShape 10 empty
  sh-dty : ∀ {a} → TmShape 11 (dty a)
  sh-ctor : ∀ {a b} → TmShape 12 (ctor a b)
  sh-mData : ∀ {a b c} → TmShape 13 (mData a b c)
  sh-mNat : ∀ {a b c d} → TmShape 14 (mNat a b c d)
  sh-mEmp : ∀ {a b} → TmShape 15 (mEmp a b)
  sh-mUnit : ∀ {a b c} → TmShape 16 (mUnit a b c)
  sh-idt : ∀ {a b c} → TmShape 17 (idt a b c)
  sh-rfl : TmShape 18 rfl
  sh-rwt : ∀ {a b c} → TmShape 19 (rwt a b c)
  sh-def : ∀ {a} → TmShape 20 (def a)
  sh-ann : ∀ {a b} → TmShape 21 (ann a b)
  sh-prod : ∀ {a b} → TmShape 22 (prod a b)
  sh-pair : ∀ {a b} → TmShape 23 (pair a b)
  sh-nu : ∀ {a} → TmShape 26 (nu a)
  sh-unf : ∀ {a b} → TmShape 27 (unf a b)
  sh-ucons : ∀ {a} → TmShape 28 (ucons a)
  sh-i64 : TmShape 29 i64
  sh-f32ty : TmShape 30 f32ty
  sh-tensor : ∀ {a b} → TmShape 31 (tensor a b)
  sh-addi : ∀ {a b} → TmShape 32 (addi a b)
  sh-muli : ∀ {a b} → TmShape 33 (muli a b)
  sh-addt : ∀ {a b} → TmShape 34 (addt a b)
  sh-toi64 : ∀ {a} → TmShape 35 (toi64 a)
  sh-packi : ∀ {a b} → TmShape 36 (packi a b)
  sh-letp : ∀ {a b} → TmShape 37 (letp a b)
  sh-word : ∀ {op ts} → TmShape 38 (word op ts)

shape : ∀ {n} (t : Tm n) → TmShape (tmTag t) t
shape (var _) = sh-var
shape typ = sh-typ
shape (pi _ _ _) = sh-pi
shape (lam _ _ _) = sh-lam
shape (app _ _) = sh-app
shape nat = sh-nat
shape ze = sh-ze
shape (su _) = sh-su
shape unit = sh-unit
shape one = sh-one
shape empty = sh-empty
shape (dty _) = sh-dty
shape (ctor _ _) = sh-ctor
shape (mData _ _ _) = sh-mData
shape (mNat _ _ _ _) = sh-mNat
shape (mEmp _ _) = sh-mEmp
shape (mUnit _ _ _) = sh-mUnit
shape (idt _ _ _) = sh-idt
shape rfl = sh-rfl
shape (rwt _ _ _) = sh-rwt
shape (def _) = sh-def
shape (ann _ _) = sh-ann
shape (prod _ _) = sh-prod
shape (pair _ _) = sh-pair
shape (nu _) = sh-nu
shape (unf _ _) = sh-unf
shape (ucons _) = sh-ucons
shape i64 = sh-i64
shape f32ty = sh-f32ty
shape (tensor _ _) = sh-tensor
shape (addi _ _) = sh-addi
shape (muli _ _) = sh-muli
shape (addt _ _) = sh-addt
shape (toi64 _) = sh-toi64
shape (packi _ _) = sh-packi
shape (letp _ _) = sh-letp
shape (word _ _) = sh-word

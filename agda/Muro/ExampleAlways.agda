------------------------------------------------------------------------
-- Always P s unfolds to P (head s) × Always P (tail s).
-- The recursive component is a proof about the tail, not Unit.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.ExampleAlways where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base
open import Muro.Syntax
open import Muro.Subst
open import Muro.Check

const0≡0 : Tm 0
const0≡0 = lam affine nat (idt nat ze ze)

zerosTy : Tm 0
zerosTy = stream nat

zerosTm : Tm 0
zerosTm = unf ze (lam affine nat (pair ze ze))

-- Always (λ _ → {0 ≡ 0}) zeros
alwaysTy : Tm 0
alwaysTy = always nat const0≡0 (def 0)

-- unfold tt (λ (_ : Unit) → (refl, zeros-always-zero))
-- The tail of zeros is zeros, so the self-call is the tail proof.
alwaysTm : Tm 0
alwaysTm = unf one (lam affine unit (pair rfl (def 1)))

alwaysBook : Sig
alwaysBook = fromDefs (
  mkDef "zeros"             run  zerosTy  zerosTm  ∷
  mkDef "zeros-always-zero" evid alwaysTy alwaysTm ∷
  [])

always-checks : checkSig! alwaysBook ≡ ok tt
always-checks = refl

-- Unguarded evidence: self-call is not an unfold.
badAlways : Sig
badAlways = fromDefs (
  mkDef "zeros" run (stream nat) zerosTm ∷
  mkDef "bad" evid (always nat const0≡0 (def 0)) (def 1) ∷
  [])

isFail : ∀ {A : Set} → Result A → Bool
isFail (fail _) = true
isFail (ok _)   = false

-- tail p, snd (uncons p) and let (a, b) = uncons p in b are this term.
tail-form : Tm 0
tail-form = sndTm (ucons (def 0))

tail-form-refused : guardedTail (0 ∷ []) tail-form ≡ false
tail-form-refused = refl

head-form : Tm 0
head-form = fstTm (ucons (def 0))

head-form-refused : guardedTail (0 ∷ []) head-form ≡ false
head-form-refused = refl

match-form : Tm 0
match-form = mNat ze nat (def 0) (def 0)

match-form-refused : guardedTail (0 ∷ []) match-form ≡ false
match-form-refused = refl

rewrite-form : Tm 0
rewrite-form = rwt rfl nat (def 0)

rewrite-form-refused : guardedTail (0 ∷ []) rewrite-form ≡ false
rewrite-form-refused = refl

idx-tail : Tm 1
idx-tail = sndTm (ucons (app (def 0) (var zero)))

idx-tail-refused : guardedTail (0 ∷ []) idx-tail ≡ false
idx-tail-refused = refl

nested-bad : Tm 0
nested-bad =
  unf one (lam affine unit (pair rfl (sndTm (ucons (sndTm (ucons (def 0)))))))

nested-bad-refused : guardedTail (0 ∷ []) nested-bad ≡ false
nested-bad-refused = refl

-- A call, a pair of calls, a nested unfold with a guarded tail.
call-form : Tm 0
call-form = def 0

def-call-ok : guardedTail (0 ∷ []) call-form ≡ true
def-call-ok = refl

app-form : Tm 0
app-form = app (def 0) ze

app-ok : guardedTail (0 ∷ []) app-form ≡ true
app-ok = refl

pair-form : Tm 0
pair-form = pair (def 0) (def 0)

pair-ok : guardedTail (0 ∷ []) pair-form ≡ true
pair-ok = refl

nested-ok : Tm 0
nested-ok = unf one (lam affine unit (pair rfl (def 0)))

nested-form-ok : guardedTail (0 ∷ []) nested-ok ≡ true
nested-form-ok = refl

------------------------------------------------------------------------
-- tail p is not a guarded tail: snd (uncons p) forces the block, so
-- GuardedTail fails for the tail of p (Theorem A).
-- The attack. s is 0, 1, 0, 1, …. p's tail is p's own tail.
-- Disc, one-eq-zero and bad are the rest of the closed Empty proof.
------------------------------------------------------------------------

sTm : Tm 0
sTm = unf ze (lam reuse nat (pair (var zero) (mNat (var zero) nat (su ze) ze)))

discTm : Tm 0
discTm = lam affine nat (mNat (var zero) typ unit empty)

predN : Tm 0
predN = lam affine nat (idt nat (var zero) ze)

pTy : Tm 0
pTy = always nat predN (def 0)

pTm : Tm 0
pTm = unf one (lam affine unit (pair rfl (sndTm (ucons (def 2)))))

oneZero : Tm 0
oneZero = fstTm (ucons (sndTm (ucons (def 2))))

badTm : Tm 0
badTm = rwt (def 3) (app (def 1) (var zero)) one

-- snd (uncons p) is not GuardedTail: it mentions the block and it is
-- not one of the four call forms, so Theorem A's GuardedTail fails.
tailBook : Sig
tailBook = fromDefs (
  mkDef "s"           run  (stream nat)         sTm     ∷
  mkDef "Disc"        spec (pi affine nat typ)  discTm  ∷
  mkDef "p"           evid pTy                  pTm     ∷
  mkDef "one-eq-zero" evid (idt nat (su ze) ze) oneZero ∷
  mkDef "bad"         evid empty                badTm   ∷
  [])

tail-refused : checkSig! tailBook ≡ fail "p body: unguarded recursive call"
tail-refused = refl

tail-fails : isFail (checkSig! tailBook) ≡ true
tail-fails rewrite tail-refused = refl

-- tail (p n) is not a guarded call: the argument is block-free, but
-- snd (uncons (p n)) is not one of the four call forms (Theorem A).
-- tail (p n), with natsFrom as the stream.
natsFromTm : Tm 0
natsFromTm =
  lam affine nat (unf (var zero) (lam reuse nat (pair (var zero) (su (var zero)))))

pIdxTy : Tm 0
pIdxTy =
  pi affine nat
    (always nat
      (lam affine nat (idt nat (var zero) (var (suc zero))))
      (app (def 0) (var zero)))

pIdxTm : Tm 0
pIdxTm =
  lam affine nat
    (unf one
      (lam affine unit
        (pair rfl (sndTm (ucons (app (def 1) (var (suc zero))))))))

idxBook : Sig
idxBook = fromDefs (
  mkDef "natsFrom" run (pi affine nat (stream nat)) natsFromTm ∷
  mkDef "p"        evid pIdxTy                      pIdxTm     ∷
  [])

idx-fails : isFail (checkSig! idxBook) ≡ true
idx-fails = refl

-- The inner unfold's tail is tail (tail p), which is not GuardedTail,
-- so gc-unf does not hold (Theorem A).
-- Nested unfold whose tail is tail (tail p).
nestBook : Sig
nestBook = fromDefs (
  mkDef "zeros" run zerosTy zerosTm ∷
  mkDef "p" evid alwaysTy
    (unf one (lam affine unit
      (pair rfl (unf one (lam affine unit
        (pair rfl (sndTm (ucons (sndTm (ucons (def 1))))))))))) ∷
  [])

nest-fails : isFail (checkSig! nestBook) ≡ true
nest-fails = refl

-- head p in the tail. Both components of Same are the head equation.
sameFam : Tm 1
sameFam =
  lam affine (stream nat)
    (prod (idt nat (fstTm (ucons (var zero))) ze)
          (idt nat (fstTm (ucons (var zero))) ze))

sameTy : Tm 0
sameTy = app (def 1) (def 0)

sameOkBook : Sig
sameOkBook = fromDefs (
  mkDef "zeros" run (stream nat) zerosTm ∷
  mkDef "Same"  spec (pi affine (stream nat) typ) (nu sameFam) ∷
  mkDef "p"     evid sameTy (unf one (lam affine unit (pair rfl rfl))) ∷
  [])

same-ok-checks : checkSig! sameOkBook ≡ ok tt
same-ok-checks = refl

-- head p in the tail is not a guarded call: fst (uncons p) forces the
-- block, so GuardedTail fails (Theorem A).
sameBadBook : Sig
sameBadBook = fromDefs (
  mkDef "zeros" run (stream nat) zerosTm ∷
  mkDef "Same"  spec (pi affine (stream nat) typ) (nu sameFam) ∷
  mkDef "p"     evid sameTy
    (unf one (lam affine unit (pair rfl (fstTm (ucons (def 2)))))) ∷
  [])

same-fails : isFail (checkSig! sameBadBook) ≡ true
same-fails = refl

-- (refl, p) is a guarded tail and the wrong type on the alternating stream.
selfBook : Sig
selfBook = fromDefs (
  mkDef "s" run (stream nat) sTm ∷
  mkDef "p" evid (always nat predN (def 0))
    (unf one (lam affine unit (pair rfl (def 1)))) ∷
  [])

self-fails : isFail (checkSig! selfBook) ≡ true
self-fails = refl

-- The seed is head (s m). It mentions s, and the step's head is the
-- seed binder, so the observed head would be that call. HeadSeed fails
-- (Theorem A): the binder occurs in the head and hasSelf of the seed
-- is true. A seed that mentions the block only in a term the head does
-- not read is not this book.
seedTm : Tm 0
seedTm =
  lam affine nat
    (unf (mNat (var zero) nat ze
            (fstTm (ucons (app (def 0) (var zero)))))
         (lam affine nat (pair (var zero) ze)))

seedBook : Sig
seedBook = fromDefs (
  mkDef "s" run (pi affine nat (stream nat)) seedTm ∷ [])

seed-refused : checkSig! seedBook ≡ fail "s productivity: unguarded recursive call"
seed-refused = refl

oneZeroBook : Sig
oneZeroBook = fromDefs (
  mkDef "one-eq-zero" evid (idt nat (su ze) ze) rfl ∷ [])

one-zero-fails : isFail (checkSig! oneZeroBook) ≡ true
one-zero-fails = refl

badOneBook : Sig
badOneBook = fromDefs (
  mkDef "bad" evid empty one ∷ [])

bad-one-fails : isFail (checkSig! badOneBook) ≡ true
bad-one-fails = refl

-- Positives: a pair of guarded tails, a nested unfold, a family call.
twoFam : Tm 1
twoFam =
  lam affine (stream nat)
    (prod unit
      (prod (app (var (suc zero)) (sndTm (ucons (var zero))))
            (app (var (suc zero)) (sndTm (ucons (var zero))))))

twoBook : Sig
twoBook = fromDefs (
  mkDef "zeros" run (stream nat) zerosTm ∷
  mkDef "Two"   spec (pi affine (stream nat) typ) (nu twoFam) ∷
  mkDef "two"   evid (app (def 1) (def 0))
    (unf one (lam affine unit (pair one (pair (def 2) (def 2))))) ∷
  [])

two-checks : checkSig! twoBook ≡ ok tt
two-checks = refl

nestedGoodBook : Sig
nestedGoodBook = fromDefs (
  mkDef "zeros" run zerosTy zerosTm ∷
  mkDef "p" evid alwaysTy
    (unf one (lam affine unit
      (pair rfl (unf one (lam affine unit (pair rfl (def 1))))))) ∷
  [])

nested-good-checks : checkSig! nestedGoodBook ≡ ok tt
nested-good-checks = refl

famCallBook : Sig
famCallBook = fromDefs (
  mkDef "zeros" run zerosTy zerosTm ∷
  mkDef "p" evid (pi affine nat (wk alwaysTy))
    (lam affine nat
      (unf one (lam affine unit
        (pair rfl (app (def 1) (su (var (suc zero)))))))) ∷
  [])

fam-call-checks : checkSig! famCallBook ≡ ok tt
fam-call-checks = refl

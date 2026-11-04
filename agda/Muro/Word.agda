------------------------------------------------------------------------
-- Fixed-width words. U8, U32, and U64 are ℕ modulo 2^w. I64 is two's
-- complement on the same 64 bits: wrapping add, sub, and mul are the
-- bit-pattern operations, and ordering, checked arithmetic, and
-- division use the signed value.
--
-- ofNat is width-specific (toU8, toU32, toU64, toI64): a bare ofNat
-- has no kind to reduce under. toNat returns the canonical residue, so
-- toNat of I64 −1 is 2^64−1. Shifts are total: an amount at or past the
-- width yields the guarded value (0, or the sign fill for a signed
-- right shift) and is never evaluated as a host shift. div and rem are
-- Opt; signed div and rem are also empty for INT64_MIN / −1. Checked
-- I64 arithmetic succeeds exactly when the ℤ result lies in
-- [−2^63, 2^63−1]. Casts reduce modulo the destination width, which
-- zero-extends a narrower unsigned source and reinterprets U64 ↔ I64.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.Word where

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; _xor_; not; if_then_else_)
open import Data.Fin.Base using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ<n; fromℕ<-toℕ; fromℕ<-cong; toℕ-fromℕ<)
open import Data.Integer.Base as ℤ using (ℤ) renaming (+_ to pos; -[1+_] to negsuc; _+_ to _ℤ+_; _-_ to _ℤ-_; _*_ to _ℤ*_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _∸_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_; _<_; _≤_; _/_; _%_; z≤n; s≤s; NonZero)
open import Data.Nat.DivMod using (_mod_; m%n<n; m<n⇒m%n≡m; [m+n]%n≡m%n)
open import Data.Nat.Properties using (m+[n∸m]≡n; m∸n+n≡m; +-assoc; +-comm; +-cancelʳ-≡; <⇒≤; ≤-<-trans; m∸n≤m; m<n⇒0<n∸m)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; cong₂)

open import Muro.Syntax
open import Muro.Subst using (ren; renList; sub; subList)

------------------------------------------------------------------------
-- Widths. Each modulus is a successor, so `%` and `/` see NonZero.
------------------------------------------------------------------------

modulus : WKind → ℕ
modulus ku8  = 256
modulus ku32 = 4294967296
modulus ku64 = 18446744073709551616
modulus ki64 = 18446744073709551616

bits : WKind → ℕ
bits ku8  = 8
bits ku32 = 32
bits ku64 = 64
bits ki64 = 64

mod64 : ℕ
mod64 = 18446744073709551616

half64 : ℕ
half64 = 9223372036854775808

_%w_ : ℕ → WKind → ℕ
n %w ku8  = n % 256
n %w ku32 = n % 4294967296
n %w ku64 = n % mod64
n %w ki64 = n % mod64

pow2 : ℕ → ℕ
pow2 zero    = 1
pow2 (suc n) = pow2 n * 2

divℕ : ℕ → ℕ → ℕ
divℕ a zero    = 0
divℕ a (suc b) = a / suc b

remℕ : ℕ → ℕ → ℕ
remℕ a zero    = 0
remℕ a (suc b) = a % suc b

------------------------------------------------------------------------
-- Wrapping operations agree with the ℕ operation modulo 2^w.
-- Subtraction is not monus: x − y wraps as (x + (2^w − (y mod 2^w))) mod 2^w.
------------------------------------------------------------------------

wrapAddN : WKind → ℕ → ℕ → ℕ
wrapAddN k x y = (x + y) %w k

wrapMulN : WKind → ℕ → ℕ → ℕ
wrapMulN k x y = (x * y) %w k

wrapSubN : WKind → ℕ → ℕ → ℕ
wrapSubN k x y = (x + (modulus k ∸ (y %w k))) %w k

wrapAdd-mod : ∀ k x y → wrapAddN k x y ≡ (x + y) %w k
wrapAdd-mod _ _ _ = refl

wrapMul-mod : ∀ k x y → wrapMulN k x y ≡ (x * y) %w k
wrapMul-mod _ _ _ = refl

wrapSub-mod : ∀ k x y → y < modulus k → wrapSubN k x y ≡ (x + (modulus k ∸ y)) %w k
wrapSub-mod ku8  x y y< = cong (λ z → (x + (256 ∸ z)) % 256) (m<n⇒m%n≡m y<)
wrapSub-mod ku32 x y y< = cong (λ z → (x + (4294967296 ∸ z)) % 4294967296) (m<n⇒m%n≡m y<)
wrapSub-mod ku64 x y y< = cong (λ z → (x + (mod64 ∸ z)) % mod64) (m<n⇒m%n≡m y<)
wrapSub-mod ki64 x y y< = cong (λ z → (x + (mod64 ∸ z)) % mod64) (m<n⇒m%n≡m y<)

-- Below the modulus, subtraction is monus when y ≤ x and the complement
-- 2^w − (y − x) when x < y.
pos-∸-< : ∀ d k → 0 < k → k ≤ d → d ∸ k < d
pos-∸-< _          zero    () _
pos-∸-< zero       (suc _) _  ()
pos-∸-< (suc d)    (suc k) _  _  = s≤s (m∸n≤m d k)

wrapSub-lo′ : ∀ d x y .{{_ : NonZero d}} → y ≤ x → x < d → y < d → (x + (d ∸ y)) % d ≡ x ∸ y
wrapSub-lo′ d x y y≤x x<d y<d =
  let y≤d = <⇒≤ y<d
      step =
        trans (cong (_+ (d ∸ y)) (sym (m+[n∸m]≡n y≤x)))
        (trans (cong (_+ (d ∸ y)) (+-comm y (x ∸ y)))
        (trans (+-assoc (x ∸ y) y (d ∸ y))
               (cong ((x ∸ y) +_) (m+[n∸m]≡n y≤d))))
      small = ≤-<-trans (m∸n≤m x y) x<d
  in trans (cong (_% d) step)
           (trans ([m+n]%n≡m%n (x ∸ y) d)
                  (m<n⇒m%n≡m small))

wrapSub-hi′ : ∀ d x y .{{_ : NonZero d}} → x < y → y < d → (x + (d ∸ y)) % d ≡ d ∸ (y ∸ x)
wrapSub-hi′ d x y x<y y<d =
  let x≤y = <⇒≤ x<y
      y≤d = <⇒≤ y<d
      k   = y ∸ x
      0<k = m<n⇒0<n∸m x<y
      k≤d = <⇒≤ (≤-<-trans (m∸n≤m y x) y<d)
      lhs =
        trans (+-assoc x (d ∸ y) k)
        (trans (cong (x +_) (+-comm (d ∸ y) k))
        (trans (sym (+-assoc x k (d ∸ y)))
        (trans (cong (_+ (d ∸ y)) (m+[n∸m]≡n x≤y))
               (m+[n∸m]≡n y≤d))))
      rhs = m∸n+n≡m k≤d
      sum = +-cancelʳ-≡ k (x + (d ∸ y)) (d ∸ k) (trans lhs (sym rhs))
  in trans (cong (_% d) sum) (m<n⇒m%n≡m (pos-∸-< d k 0<k k≤d))

-- `rewrite` would reduce m<n⇒m%n≡m, and that proof walks the modulus.
-- cong leaves the proof abstract, so 2^32 and 2^64 stay small.
sub-below : ∀ d x y .{{_ : NonZero d}} → y < d →
            (x + (d ∸ (y % d))) % d ≡ (x + (d ∸ y)) % d
sub-below d x y y< = cong (λ z → (x + (d ∸ z)) % d) (m<n⇒m%n≡m y<)

wrapSub-lo : ∀ k x y → y ≤ x → x < modulus k → y < modulus k → wrapSubN k x y ≡ x ∸ y
wrapSub-lo ku8  x y y≤x x< y< = trans (sub-below 256 x y y<) (wrapSub-lo′ 256 x y y≤x x< y<)
wrapSub-lo ku32 x y y≤x x< y< = trans (sub-below 4294967296 x y y<) (wrapSub-lo′ 4294967296 x y y≤x x< y<)
wrapSub-lo ku64 x y y≤x x< y< = trans (sub-below mod64 x y y<) (wrapSub-lo′ mod64 x y y≤x x< y<)
wrapSub-lo ki64 x y y≤x x< y< = trans (sub-below mod64 x y y<) (wrapSub-lo′ mod64 x y y≤x x< y<)

wrapSub-hi : ∀ k x y → x < y → x < modulus k → y < modulus k → wrapSubN k x y ≡ modulus k ∸ (y ∸ x)
wrapSub-hi ku8  x y x<y x< y< = trans (sub-below 256 x y y<) (wrapSub-hi′ 256 x y x<y y<)
wrapSub-hi ku32 x y x<y x< y< = trans (sub-below 4294967296 x y y<) (wrapSub-hi′ 4294967296 x y x<y y<)
wrapSub-hi ku64 x y x<y x< y< = trans (sub-below mod64 x y y<) (wrapSub-hi′ mod64 x y x<y y<)
wrapSub-hi ki64 x y x<y x< y< = trans (sub-below mod64 x y y<) (wrapSub-hi′ mod64 x y x<y y<)

------------------------------------------------------------------------
-- Signed interpretation of a 64-bit pattern. Only residues are intended.
------------------------------------------------------------------------

toℤ : ℕ → ℤ
toℤ n = if n <ᵇ half64 then pos n else negsuc ((mod64 ∸ 1) ∸ n)

fromℤ : ℤ → ℕ
fromℤ (pos n)    = n
fromℤ (negsuc n) = mod64 ∸ suc n

inRange : ℤ → Bool
inRange (pos n)    = n <ᵇ half64
inRange (negsuc n) = suc n ≤ᵇ half64

absBits : ℕ → ℕ
absBits n = if n <ᵇ half64 then n else suc ((mod64 ∸ 1) ∸ n)

negBits : ℕ → ℕ
negBits n = if n ≡ᵇ 0 then 0 else mod64 ∸ n

neg? : ℕ → Bool
neg? n = half64 ≤ᵇ n

------------------------------------------------------------------------
-- Checked arithmetic. Unsigned: the ℕ result fits in the width
-- (subtraction fits when there is no borrow). Signed: the ℤ result
-- fits in [−2^63, 2^63−1]. The payload is that result.
------------------------------------------------------------------------

addPayload : WKind → ℕ → ℕ → ℕ
addPayload ki64 x y = fromℤ (toℤ (x %w ki64) ℤ+ toℤ (y %w ki64))
addPayload k    x y = (x %w k) + (y %w k)

subPayload : WKind → ℕ → ℕ → ℕ
subPayload ki64 x y = fromℤ (toℤ (x %w ki64) ℤ- toℤ (y %w ki64))
subPayload k    x y = (x %w k) ∸ (y %w k)

mulPayload : WKind → ℕ → ℕ → ℕ
mulPayload ki64 x y = fromℤ (toℤ (x %w ki64) ℤ* toℤ (y %w ki64))
mulPayload k    x y = (x %w k) * (y %w k)

fitsAdd : WKind → ℕ → ℕ → Bool
fitsAdd ki64 x y = inRange (toℤ (x %w ki64) ℤ+ toℤ (y %w ki64))
fitsAdd k    x y = addPayload k x y <ᵇ modulus k

fitsSub : WKind → ℕ → ℕ → Bool
fitsSub ki64 x y = inRange (toℤ (x %w ki64) ℤ- toℤ (y %w ki64))
fitsSub k    x y = (y %w k) ≤ᵇ (x %w k)

fitsMul : WKind → ℕ → ℕ → Bool
fitsMul ki64 x y = inRange (toℤ (x %w ki64) ℤ* toℤ (y %w ki64))
fitsMul k    x y = mulPayload k x y <ᵇ modulus k

checkedAddN : WKind → ℕ → ℕ → Maybe ℕ
checkedAddN k x y = if fitsAdd k x y then just (addPayload k x y) else nothing

checkedSubN : WKind → ℕ → ℕ → Maybe ℕ
checkedSubN k x y = if fitsSub k x y then just (subPayload k x y) else nothing

checkedMulN : WKind → ℕ → ℕ → Maybe ℕ
checkedMulN k x y = if fitsMul k x y then just (mulPayload k x y) else nothing

if-just : ∀ {A : Set} (b : Bool) (v : A) → is-just (if b then just v else nothing) ≡ b
if-just true  _ = refl
if-just false _ = refl

is-just-not : ∀ {A : Set} (b : Bool) (v : A) → is-just (if b then nothing else (just v)) ≡ not b
is-just-not true  _ = refl
is-just-not false _ = refl

checkedAdd-iff : ∀ k x y → is-just (checkedAddN k x y) ≡ fitsAdd k x y
checkedAdd-iff k x y = if-just (fitsAdd k x y) (addPayload k x y)

checkedSub-iff : ∀ k x y → is-just (checkedSubN k x y) ≡ fitsSub k x y
checkedSub-iff k x y = if-just (fitsSub k x y) (subPayload k x y)

checkedMul-iff : ∀ k x y → is-just (checkedMulN k x y) ≡ fitsMul k x y
checkedMul-iff k x y = if-just (fitsMul k x y) (mulPayload k x y)

checkedAdd-val : ∀ k x y r → checkedAddN k x y ≡ just r → r ≡ addPayload k x y
checkedAdd-val k x y r eq with fitsAdd k x y
checkedAdd-val k x y .(addPayload k x y) refl | true  = refl
checkedAdd-val _ _ _ _ () | false

checkedSub-val : ∀ k x y r → checkedSubN k x y ≡ just r → r ≡ subPayload k x y
checkedSub-val k x y r eq with fitsSub k x y
checkedSub-val k x y .(subPayload k x y) refl | true  = refl
checkedSub-val _ _ _ _ () | false

checkedMul-val : ∀ k x y r → checkedMulN k x y ≡ just r → r ≡ mulPayload k x y
checkedMul-val k x y r eq with fitsMul k x y
checkedMul-val k x y .(mulPayload k x y) refl | true  = refl
checkedMul-val _ _ _ _ () | false

------------------------------------------------------------------------
-- Bitwise operations, by structural recursion on the width.
------------------------------------------------------------------------

andB : ℕ → ℕ → ℕ → ℕ
andB zero    _ _ = 0
andB (suc w) x y =
  ((x % 2) * (y % 2)) + 2 * andB w (x / 2) (y / 2)

andN : WKind → ℕ → ℕ → ℕ
andN k x y = andB (bits k) (x %w k) (y %w k) %w k

notN : WKind → ℕ → ℕ
notN k x = (modulus k ∸ 1) ∸ (x %w k)

orN : WKind → ℕ → ℕ → ℕ
orN k x y = notN k (andN k (notN k x) (notN k y))

xorN : WKind → ℕ → ℕ → ℕ
xorN k x y = orN k (andN k x (notN k y)) (andN k (notN k x) y)

------------------------------------------------------------------------
-- Comparisons. Unsigned order is ℕ order of the residues. Signed order
-- compares signs first; the same sign uses the residue order, which on
-- two's-complement negatives agrees with ℤ.
------------------------------------------------------------------------

eqN : WKind → ℕ → ℕ → Bool
eqN k x y = (x %w k) ≡ᵇ (y %w k)

slt : ℕ → ℕ → Bool
slt x y =
  if (x <ᵇ half64) ∧ (y <ᵇ half64) then x <ᵇ y
  else if (half64 ≤ᵇ x) ∧ (half64 ≤ᵇ y) then x <ᵇ y
  else half64 ≤ᵇ x

ltN : WKind → ℕ → ℕ → Bool
ltN ki64 x y = slt (x %w ki64) (y %w ki64)
ltN k    x y = (x %w k) <ᵇ (y %w k)

leN : WKind → ℕ → ℕ → Bool
leN k x y = eqN k x y ∨ ltN k x y

------------------------------------------------------------------------
-- Shifts. Total. n ≥ width does not perform a host shift: left and
-- logical right yield 0; arithmetic right yields the sign fill.
------------------------------------------------------------------------

shlN : WKind → ℕ → ℕ → ℕ
shlN k x n =
  if n <ᵇ bits k then ((x %w k) * pow2 n) %w k else 0

ushrN : WKind → ℕ → ℕ → ℕ
ushrN k x n =
  if n <ᵇ bits k then divℕ (x %w k) (pow2 n) else 0

ashr : ℕ → ℕ → ℕ
ashr x n =
  if n <ᵇ 64
  then (let q = divℕ x (pow2 n) in
        if x <ᵇ half64 then q else (q + (mod64 ∸ pow2 (64 ∸ n))) % mod64)
  else (if x <ᵇ half64 then 0 else mod64 ∸ 1)

shrN : WKind → ℕ → ℕ → ℕ
shrN ki64 x n = ashr (x %w ki64) n
shrN k    x n = ushrN k x n

------------------------------------------------------------------------
-- Truncating division (toward zero). Empty when the divisor is zero,
-- and for I64 also when the quotient is not representable
-- (INT64_MIN / −1 and INT64_MIN % −1). Remainder takes the sign of
-- the dividend.
------------------------------------------------------------------------

quotBits : ℕ → ℕ → ℕ
quotBits x y =
  let mag = divℕ (absBits x) (absBits y) in
  if neg? x xor neg? y then negBits mag else mag

remBits : ℕ → ℕ → ℕ
remBits x y =
  let mag = remℕ (absBits x) (absBits y) in
  if neg? x then negBits mag else mag

overflowDiv : ℕ → ℕ → Bool
overflowDiv x y = (x ≡ᵇ half64) ∧ (y ≡ᵇ (mod64 ∸ 1))

badDiv : WKind → ℕ → ℕ → Bool
badDiv ki64 x y =
  let yn = y %w ki64 in (yn ≡ᵇ 0) ∨ overflowDiv (x %w ki64) yn
badDiv k x y = (y %w k) ≡ᵇ 0

divBits : WKind → ℕ → ℕ → ℕ
divBits ki64 x y = quotBits (x %w ki64) (y %w ki64)
divBits k    x y = divℕ (x %w k) (y %w k)

remBitsK : WKind → ℕ → ℕ → ℕ
remBitsK ki64 x y = remBits (x %w ki64) (y %w ki64)
remBitsK k    x y = remℕ (x %w k) (y %w k)

divPayload : WKind → ℕ → ℕ → Maybe ℕ
divPayload k x y = if badDiv k x y then nothing else just (divBits k x y)

remPayload : WKind → ℕ → ℕ → Maybe ℕ
remPayload k x y = if badDiv k x y then nothing else just (remBitsK k x y)

divOk : WKind → ℕ → ℕ → Bool
divOk k x y = not (badDiv k x y)

div-iff : ∀ k x y → is-just (divPayload k x y) ≡ divOk k x y
div-iff k x y = is-just-not (badDiv k x y) (divBits k x y)

rem-iff : ∀ k x y → is-just (remPayload k x y) ≡ divOk k x y
rem-iff k x y = is-just-not (badDiv k x y) (remBitsK k x y)

castN : WKind → ℕ → ℕ
castN k n = n %w k

------------------------------------------------------------------------
-- Residue as Fin. ofNat ∘ toNat is the identity; toNat ∘ ofNat is mod.
------------------------------------------------------------------------

ofNatF : (k : WKind) → ℕ → Fin (modulus k)
ofNatF ku8  n = n mod 256
ofNatF ku32 n = n mod 4294967296
ofNatF ku64 n = n mod mod64
ofNatF ki64 n = n mod mod64

toNat∘ofNat : ∀ k n → toℕ (ofNatF k n) ≡ n %w k
toNat∘ofNat ku8  n = toℕ-fromℕ< (m%n<n n 256)
toNat∘ofNat ku32 n = toℕ-fromℕ< (m%n<n n 4294967296)
toNat∘ofNat ku64 n = toℕ-fromℕ< (m%n<n n mod64)
toNat∘ofNat ki64 n = toℕ-fromℕ< (m%n<n n mod64)

ofNat∘toNat : ∀ k (x : Fin (modulus k)) → ofNatF k (toℕ x) ≡ x
ofNat∘toNat ku8 x =
  trans (fromℕ<-cong (toℕ x % 256) (toℕ x) (m<n⇒m%n≡m (toℕ<n x)) (m%n<n (toℕ x) 256) (toℕ<n x))
        (fromℕ<-toℕ x (toℕ<n x))
ofNat∘toNat ku32 x =
  trans (fromℕ<-cong (toℕ x % 4294967296) (toℕ x) (m<n⇒m%n≡m (toℕ<n x)) (m%n<n (toℕ x) 4294967296) (toℕ<n x))
        (fromℕ<-toℕ x (toℕ<n x))
ofNat∘toNat ku64 x =
  trans (fromℕ<-cong (toℕ x % mod64) (toℕ x) (m<n⇒m%n≡m (toℕ<n x)) (m%n<n (toℕ x) mod64) (toℕ<n x))
        (fromℕ<-toℕ x (toℕ<n x))
ofNat∘toNat ki64 x =
  trans (fromℕ<-cong (toℕ x % mod64) (toℕ x) (m<n⇒m%n≡m (toℕ<n x)) (m%n<n (toℕ x) mod64) (toℕ<n x))
        (fromℕ<-toℕ x (toℕ<n x))

------------------------------------------------------------------------
-- Values wordStep returns, and the redexes it fires on. A canonical
-- term has no free variables, so renaming and substitution leave it.
------------------------------------------------------------------------

data Canon {n} : Tm n → Set where
  can-ze    : Canon ze
  can-su    : ∀ {t} → Canon t → Canon (su t)
  can-lit   : ∀ {k m} → Canon (word (wlit k m) [])
  can-true  : Canon (word wtrue [])
  can-false : Canon (word wfalse [])
  can-none  : Canon (word wnone [])
  can-some  : ∀ {k m} → Canon (word wsome (word (wlit k m) [] ∷ []))
  can-ty    : ∀ {k} → Canon (word (wty k) [])
  can-bool  : Canon (word wbool [])
  can-opt   : ∀ {k} → Canon (word (woptk k) [])
  can-i64   : Canon i64

infixr 5 _ac∷_

data AllC {n} : List (Tm n) → Set where
  ac0 : AllC []
  _ac∷_ : ∀ {t ts} → Canon t → AllC ts → AllC (t ∷ ts)

numeral : ∀ {n} → ℕ → Tm n
numeral zero    = ze
numeral (suc m) = su (numeral m)

numCanon : ∀ {n} (m : ℕ) → Canon (numeral {n} m)
numCanon zero    = can-ze
numCanon (suc m) = can-su (numCanon m)

wlitT : ∀ {n} → WKind → ℕ → Tm n
wlitT k m = word (wlit k m) []

Lit : ∀ {n} → Tm n → Set
Lit t = Σ WKind (λ k → Σ ℕ (λ m → t ≡ wlitT k m))

litArg : ∀ {n} (t : Tm n) → Maybe (Lit t)
litArg (word (wlit k m) []) = just (k , m , refl)
litArg _                     = nothing

litCanon : ∀ {n} {t : Tm n} → Lit t → Canon t
litCanon (_ , _ , refl) = can-lit

-- The successor case is a plain function, not a with, so a rewrite of
-- ℕ← (numeral a) is visible in ℕ← (su (numeral a)).
ℕ←-su : ∀ {n} {t : Tm n} →
  Maybe (Σ ℕ (λ m → t ≡ numeral m)) → Maybe (Σ ℕ (λ m → su t ≡ numeral m))
ℕ←-su (just (m , eq)) = just (suc m , cong su eq)
ℕ←-su nothing         = nothing

ℕ← : ∀ {n} (t : Tm n) → Maybe (Σ ℕ (λ m → t ≡ numeral m))
ℕ← ze     = just (0 , refl)
ℕ← (su t) = ℕ←-su (ℕ← t)
ℕ← _      = nothing

natCanon : ∀ {n} {t : Tm n} → Σ ℕ (λ m → t ≡ numeral m) → Canon t
natCanon (m , refl) = numCanon m

data TyArg {n} (t : Tm n) : Set where
  ty-i64 : t ≡ i64 → TyArg t
  ty-wd  : ∀ k → t ≡ word (wty k) [] → TyArg t

kindOfTy : ∀ {n} (t : Tm n) → Maybe (TyArg t)
kindOfTy i64                 = just (ty-i64 refl)
kindOfTy (word (wty k) [])   = just (ty-wd k refl)
kindOfTy _                   = nothing

tyCanon : ∀ {n} {t : Tm n} → TyArg t → Canon t
tyCanon (ty-i64 refl)   = can-i64
tyCanon (ty-wd _ refl)  = can-ty

boolT : ∀ {n} → Bool → Tm n
boolT true  = word wtrue []
boolT false = word wfalse []

boolCanon : ∀ {n} (b : Bool) → Canon (boolT {n} b)
boolCanon true  = can-true
boolCanon false = can-false

optTerm : ∀ {n} → WKind → Maybe ℕ → Tm n
optTerm k (just m) = word wsome (wlitT k m ∷ [])
optTerm k nothing  = word wnone []

optCanon : ∀ {n} k (mb : Maybe ℕ) → Canon (optTerm {n} k mb)
optCanon k (just _) = can-some
optCanon k nothing  = can-none

wordTy : ∀ {n} → WKind → Tm n
wordTy ki64 = i64
wordTy k    = word (wty k) []

optTy : ∀ {n} → WKind → Tm n
optTy k = word (woptk k) []

onLits : ∀ {n} → (WKind → ℕ → ℕ → ℕ) → Tm n → Tm n → Maybe (Tm n)
onLits f x y with litArg x | litArg y
... | just (k , a , _) | just (k′ , b , _) =
      if wk≡ᵇ k k′ then just (wlitT k (f k a b)) else nothing
... | _ | _ = nothing

onLits-res : ∀ {n} f (x y : Tm n) {r} → onLits f x y ≡ just r → Canon r
onLits-res f x y eq with litArg x | litArg y
onLits-res f x y eq | just (k , a , _) | just (k′ , b , _) with wk≡ᵇ k k′
onLits-res f x y refl | just (k , a , _) | just (k′ , b , _) | true  = can-lit
onLits-res f x y ()   | just (k , a , _) | just (k′ , b , _) | false
onLits-res f x y ()   | just _           | nothing
onLits-res f x y ()   | nothing          | just _
onLits-res f x y ()   | nothing          | nothing

onLits-args : ∀ {n} f (x y : Tm n) {r} → onLits f x y ≡ just r → AllC (x ∷ y ∷ [])
onLits-args f x y eq with litArg x | litArg y
onLits-args f x y eq | just (k , a , px) | just (k′ , b , py) with wk≡ᵇ k k′
onLits-args f x y refl | just (k , a , px) | just (k′ , b , py) | true =
  litCanon (k , a , px) ac∷ litCanon (k′ , b , py) ac∷ ac0
onLits-args f x y ()   | just _ | just _ | false
onLits-args f x y ()   | just _ | nothing
onLits-args f x y ()   | nothing | just _
onLits-args f x y ()   | nothing | nothing

onCmp : ∀ {n} → (WKind → ℕ → ℕ → Bool) → Tm n → Tm n → Maybe (Tm n)
onCmp f x y with litArg x | litArg y
... | just (k , a , _) | just (k′ , b , _) =
      if wk≡ᵇ k k′ then just (boolT (f k a b)) else nothing
... | _ | _ = nothing

onCmp-res : ∀ {n} f (x y : Tm n) {r} → onCmp f x y ≡ just r → Canon r
onCmp-res f x y eq with litArg x | litArg y
onCmp-res f x y eq | just (k , a , _) | just (k′ , b , _) with wk≡ᵇ k k′
onCmp-res f x y refl | just (k , a , _) | just (k′ , b , _) | true  = boolCanon (f k a b)
onCmp-res f x y ()   | just (k , a , _) | just (k′ , b , _) | false
onCmp-res f x y ()   | just _           | nothing
onCmp-res f x y ()   | nothing          | just _
onCmp-res f x y ()   | nothing          | nothing

onCmp-args : ∀ {n} f (x y : Tm n) {r} → onCmp f x y ≡ just r → AllC (x ∷ y ∷ [])
onCmp-args f x y eq with litArg x | litArg y
onCmp-args f x y eq | just (k , a , px) | just (k′ , b , py) with wk≡ᵇ k k′
onCmp-args f x y refl | just (k , a , px) | just (k′ , b , py) | true =
  litCanon (k , a , px) ac∷ litCanon (k′ , b , py) ac∷ ac0
onCmp-args f x y ()   | just _ | just _ | false
onCmp-args f x y ()   | just _ | nothing
onCmp-args f x y ()   | nothing | just _
onCmp-args f x y ()   | nothing | nothing

onOpt : ∀ {n} → (WKind → ℕ → ℕ → Maybe ℕ) → Tm n → Tm n → Maybe (Tm n)
onOpt f x y with litArg x | litArg y
... | just (k , a , _) | just (k′ , b , _) =
      if wk≡ᵇ k k′ then just (optTerm k (f k a b)) else nothing
... | _ | _ = nothing

onOpt-res : ∀ {n} f (x y : Tm n) {r} → onOpt f x y ≡ just r → Canon r
onOpt-res f x y eq with litArg x | litArg y
onOpt-res f x y eq | just (k , a , _) | just (k′ , b , _) with wk≡ᵇ k k′
onOpt-res f x y refl | just (k , a , _) | just (k′ , b , _) | true  = optCanon k (f k a b)
onOpt-res f x y ()   | just (k , a , _) | just (k′ , b , _) | false
onOpt-res f x y ()   | just _           | nothing
onOpt-res f x y ()   | nothing          | just _
onOpt-res f x y ()   | nothing          | nothing

onOpt-args : ∀ {n} f (x y : Tm n) {r} → onOpt f x y ≡ just r → AllC (x ∷ y ∷ [])
onOpt-args f x y eq with litArg x | litArg y
onOpt-args f x y eq | just (k , a , px) | just (k′ , b , py) with wk≡ᵇ k k′
onOpt-args f x y refl | just (k , a , px) | just (k′ , b , py) | true =
  litCanon (k , a , px) ac∷ litCanon (k′ , b , py) ac∷ ac0
onOpt-args f x y ()   | just _ | just _ | false
onOpt-args f x y ()   | just _ | nothing
onOpt-args f x y ()   | nothing | just _
onOpt-args f x y ()   | nothing | nothing

onUn : ∀ {n} → (WKind → ℕ → ℕ) → Tm n → Maybe (Tm n)
onUn f x with litArg x
... | just (k , a , _) = just (wlitT k (f k a))
... | nothing          = nothing

onUn-res : ∀ {n} f (x : Tm n) {r} → onUn f x ≡ just r → Canon r
onUn-res f x eq with litArg x
onUn-res f x refl | just _ = can-lit
onUn-res f x ()   | nothing

onUn-args : ∀ {n} f (x : Tm n) {r} → onUn f x ≡ just r → AllC (x ∷ [])
onUn-args f x eq with litArg x
onUn-args f x refl | just lx = litCanon lx ac∷ ac0
onUn-args f x ()   | nothing

shiftFrom : ∀ {n} (f : WKind → ℕ → ℕ → ℕ) (x amt : Tm n) →
  Maybe (Lit x) → Maybe (Σ ℕ (λ m → amt ≡ numeral m)) → Maybe (Tm n)
shiftFrom f x amt (just (k , a , _)) (just (b , _)) = just (wlitT k (f k a b))
shiftFrom _ _ _ _ _ = nothing

onShift : ∀ {n} → (WKind → ℕ → ℕ → ℕ) → Tm n → Tm n → Maybe (Tm n)
onShift f x amt = shiftFrom f x amt (litArg x) (ℕ← amt)

onShift-res : ∀ {n} f (x n : Tm n) {r} → onShift f x n ≡ just r → Canon r
onShift-res f x n eq with litArg x | ℕ← n
onShift-res f x n refl | just _ | just _ = can-lit
onShift-res f x n ()   | just _ | nothing
onShift-res f x n ()   | nothing | just _
onShift-res f x n ()   | nothing | nothing

onShift-args : ∀ {n} f (x n : Tm n) {r} → onShift f x n ≡ just r → AllC (x ∷ n ∷ [])
onShift-args f x n eq with litArg x | ℕ← n
onShift-args f x n refl | just lx | just nn = litCanon lx ac∷ natCanon nn ac∷ ac0
onShift-args f x n ()   | just _  | nothing
onShift-args f x n ()   | nothing | just _
onShift-args f x n ()   | nothing | nothing

-- ofNat's step takes the numeral view as an argument, so rewriting
-- ℕ← (numeral a) is not hidden under with.
wof-from : ∀ {n} {t : Tm n} (k : WKind) →
  Maybe (Σ ℕ (λ m → t ≡ numeral m)) → Maybe (Tm n)
wof-from k (just (m , _)) = just (wlitT k (m %w k))
wof-from _ nothing        = nothing

-- Opt's step takes the type view as an argument. A with on kindOfTy
-- inside wordStep does not reduce while the canon proof matches refl.
wopt-from : ∀ {n} {t : Tm n} → Maybe (TyArg t) → Maybe (Tm n)
wopt-from (just (ty-i64 _))  = just (optTy ki64)
wopt-from (just (ty-wd k _)) = just (optTy k)
wopt-from nothing            = nothing

-- Fires only when every argument is already a value. whnf reduces
-- arguments first, then calls this, then whnfs the contractum.
wordStep : ∀ {n} → WOp → List (Tm n) → Maybe (Tm n)
wordStep (wof k)     (t ∷ [])       = wof-from k (ℕ← t)
wordStep wton        (t ∷ [])       with litArg t
... | just (k , a , _)               = just (numeral (a %w k))
... | nothing                        = nothing
wordStep wadd        (x ∷ y ∷ [])   = onLits wrapAddN x y
wordStep wsub        (x ∷ y ∷ [])   = onLits wrapSubN x y
wordStep wmul        (x ∷ y ∷ [])   = onLits wrapMulN x y
wordStep wcadd       (x ∷ y ∷ [])   = onOpt checkedAddN x y
wordStep wcsub       (x ∷ y ∷ [])   = onOpt checkedSubN x y
wordStep wcmul       (x ∷ y ∷ [])   = onOpt checkedMulN x y
wordStep wdiv        (x ∷ y ∷ [])   = onOpt divPayload x y
wordStep wrem        (x ∷ y ∷ [])   = onOpt remPayload x y
wordStep weq         (x ∷ y ∷ [])   = onCmp eqN x y
wordStep wlt         (x ∷ y ∷ [])   = onCmp ltN x y
wordStep wle         (x ∷ y ∷ [])   = onCmp leN x y
wordStep wand        (x ∷ y ∷ [])   = onLits andN x y
wordStep wor         (x ∷ y ∷ [])   = onLits orN x y
wordStep wxor        (x ∷ y ∷ [])   = onLits xorN x y
wordStep wnot        (x ∷ [])       = onUn notN x
wordStep wshl        (x ∷ n ∷ [])   = onShift shlN x n
wordStep wshr        (x ∷ n ∷ [])   = onShift shrN x n
wordStep (wcast k)   (t ∷ [])       with litArg t
... | just (_ , a , _)               = just (wlitT k (castN k a))
... | nothing                        = nothing
wordStep wopt        (t ∷ [])       = wopt-from (kindOfTy t)
wordStep _           _              = nothing

wordStep-res-canon : ∀ {n} op (ts : List (Tm n)) {r} → wordStep op ts ≡ just r → Canon r
wordStep-res-canon (wof k) (t ∷ []) eq with ℕ← t
wordStep-res-canon (wof k) (t ∷ []) refl | just _ = can-lit
wordStep-res-canon (wof k) (t ∷ []) ()   | nothing
wordStep-res-canon (wof _) [] ()
wordStep-res-canon (wof _) (_ ∷ _ ∷ _) ()
wordStep-res-canon wton (t ∷ []) eq with litArg t
wordStep-res-canon wton (t ∷ []) refl | just (k , a , _) = numCanon (a %w k)
wordStep-res-canon wton (t ∷ []) ()   | nothing
wordStep-res-canon wton [] ()
wordStep-res-canon wton (_ ∷ _ ∷ _) ()
wordStep-res-canon wadd (x ∷ y ∷ []) eq = onLits-res wrapAddN x y eq
wordStep-res-canon wadd [] ()
wordStep-res-canon wadd (_ ∷ []) ()
wordStep-res-canon wadd (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon wsub (x ∷ y ∷ []) eq = onLits-res wrapSubN x y eq
wordStep-res-canon wsub [] ()
wordStep-res-canon wsub (_ ∷ []) ()
wordStep-res-canon wsub (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon wmul (x ∷ y ∷ []) eq = onLits-res wrapMulN x y eq
wordStep-res-canon wmul [] ()
wordStep-res-canon wmul (_ ∷ []) ()
wordStep-res-canon wmul (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon wcadd (x ∷ y ∷ []) eq = onOpt-res checkedAddN x y eq
wordStep-res-canon wcadd [] ()
wordStep-res-canon wcadd (_ ∷ []) ()
wordStep-res-canon wcadd (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon wcsub (x ∷ y ∷ []) eq = onOpt-res checkedSubN x y eq
wordStep-res-canon wcsub [] ()
wordStep-res-canon wcsub (_ ∷ []) ()
wordStep-res-canon wcsub (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon wcmul (x ∷ y ∷ []) eq = onOpt-res checkedMulN x y eq
wordStep-res-canon wcmul [] ()
wordStep-res-canon wcmul (_ ∷ []) ()
wordStep-res-canon wcmul (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon wdiv (x ∷ y ∷ []) eq = onOpt-res divPayload x y eq
wordStep-res-canon wdiv [] ()
wordStep-res-canon wdiv (_ ∷ []) ()
wordStep-res-canon wdiv (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon wrem (x ∷ y ∷ []) eq = onOpt-res remPayload x y eq
wordStep-res-canon wrem [] ()
wordStep-res-canon wrem (_ ∷ []) ()
wordStep-res-canon wrem (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon weq (x ∷ y ∷ []) eq = onCmp-res eqN x y eq
wordStep-res-canon weq [] ()
wordStep-res-canon weq (_ ∷ []) ()
wordStep-res-canon weq (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon wlt (x ∷ y ∷ []) eq = onCmp-res ltN x y eq
wordStep-res-canon wlt [] ()
wordStep-res-canon wlt (_ ∷ []) ()
wordStep-res-canon wlt (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon wle (x ∷ y ∷ []) eq = onCmp-res leN x y eq
wordStep-res-canon wle [] ()
wordStep-res-canon wle (_ ∷ []) ()
wordStep-res-canon wle (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon wand (x ∷ y ∷ []) eq = onLits-res andN x y eq
wordStep-res-canon wand [] ()
wordStep-res-canon wand (_ ∷ []) ()
wordStep-res-canon wand (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon wor (x ∷ y ∷ []) eq = onLits-res orN x y eq
wordStep-res-canon wor [] ()
wordStep-res-canon wor (_ ∷ []) ()
wordStep-res-canon wor (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon wxor (x ∷ y ∷ []) eq = onLits-res xorN x y eq
wordStep-res-canon wxor [] ()
wordStep-res-canon wxor (_ ∷ []) ()
wordStep-res-canon wxor (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon wnot (x ∷ []) eq = onUn-res notN x eq
wordStep-res-canon wnot [] ()
wordStep-res-canon wnot (_ ∷ _ ∷ _) ()
wordStep-res-canon wshl (x ∷ n ∷ []) eq = onShift-res shlN x n eq
wordStep-res-canon wshl [] ()
wordStep-res-canon wshl (_ ∷ []) ()
wordStep-res-canon wshl (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon wshr (x ∷ n ∷ []) eq = onShift-res shrN x n eq
wordStep-res-canon wshr [] ()
wordStep-res-canon wshr (_ ∷ []) ()
wordStep-res-canon wshr (_ ∷ _ ∷ _ ∷ _) ()
wordStep-res-canon (wcast k) (t ∷ []) eq with litArg t
wordStep-res-canon (wcast k) (t ∷ []) refl | just _ = can-lit
wordStep-res-canon (wcast k) (t ∷ []) ()   | nothing
wordStep-res-canon (wcast _) [] ()
wordStep-res-canon (wcast _) (_ ∷ _ ∷ _) ()
wordStep-res-canon wopt (t ∷ []) eq with kindOfTy t
wordStep-res-canon wopt (t ∷ []) refl | just (ty-i64 _) = can-opt
wordStep-res-canon wopt (t ∷ []) refl | just (ty-wd _ _) = can-opt
wordStep-res-canon wopt (t ∷ []) ()   | nothing
wordStep-res-canon wopt [] ()
wordStep-res-canon wopt (_ ∷ _ ∷ _) ()
wordStep-res-canon (wty _) _ ()
wordStep-res-canon (wlit _ _) _ ()
wordStep-res-canon wbool _ ()
wordStep-res-canon wtrue _ ()
wordStep-res-canon wfalse _ ()
wordStep-res-canon (woptk _) _ ()
wordStep-res-canon wsome _ ()
wordStep-res-canon wnone _ ()

wordStep-args-canon : ∀ {n} op (ts : List (Tm n)) {r} → wordStep op ts ≡ just r → AllC ts
wordStep-args-canon (wof k) (t ∷ []) eq with ℕ← t
wordStep-args-canon (wof k) (t ∷ []) refl | just nn = natCanon nn ac∷ ac0
wordStep-args-canon (wof k) (t ∷ []) ()   | nothing
wordStep-args-canon (wof _) [] ()
wordStep-args-canon (wof _) (_ ∷ _ ∷ _) ()
wordStep-args-canon wton (t ∷ []) eq with litArg t
wordStep-args-canon wton (t ∷ []) refl | just lx = litCanon lx ac∷ ac0
wordStep-args-canon wton (t ∷ []) ()   | nothing
wordStep-args-canon wton [] ()
wordStep-args-canon wton (_ ∷ _ ∷ _) ()
wordStep-args-canon wadd (x ∷ y ∷ []) eq = onLits-args wrapAddN x y eq
wordStep-args-canon wadd [] ()
wordStep-args-canon wadd (_ ∷ []) ()
wordStep-args-canon wadd (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon wsub (x ∷ y ∷ []) eq = onLits-args wrapSubN x y eq
wordStep-args-canon wsub [] ()
wordStep-args-canon wsub (_ ∷ []) ()
wordStep-args-canon wsub (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon wmul (x ∷ y ∷ []) eq = onLits-args wrapMulN x y eq
wordStep-args-canon wmul [] ()
wordStep-args-canon wmul (_ ∷ []) ()
wordStep-args-canon wmul (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon wcadd (x ∷ y ∷ []) eq = onOpt-args checkedAddN x y eq
wordStep-args-canon wcadd [] ()
wordStep-args-canon wcadd (_ ∷ []) ()
wordStep-args-canon wcadd (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon wcsub (x ∷ y ∷ []) eq = onOpt-args checkedSubN x y eq
wordStep-args-canon wcsub [] ()
wordStep-args-canon wcsub (_ ∷ []) ()
wordStep-args-canon wcsub (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon wcmul (x ∷ y ∷ []) eq = onOpt-args checkedMulN x y eq
wordStep-args-canon wcmul [] ()
wordStep-args-canon wcmul (_ ∷ []) ()
wordStep-args-canon wcmul (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon wdiv (x ∷ y ∷ []) eq = onOpt-args divPayload x y eq
wordStep-args-canon wdiv [] ()
wordStep-args-canon wdiv (_ ∷ []) ()
wordStep-args-canon wdiv (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon wrem (x ∷ y ∷ []) eq = onOpt-args remPayload x y eq
wordStep-args-canon wrem [] ()
wordStep-args-canon wrem (_ ∷ []) ()
wordStep-args-canon wrem (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon weq (x ∷ y ∷ []) eq = onCmp-args eqN x y eq
wordStep-args-canon weq [] ()
wordStep-args-canon weq (_ ∷ []) ()
wordStep-args-canon weq (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon wlt (x ∷ y ∷ []) eq = onCmp-args ltN x y eq
wordStep-args-canon wlt [] ()
wordStep-args-canon wlt (_ ∷ []) ()
wordStep-args-canon wlt (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon wle (x ∷ y ∷ []) eq = onCmp-args leN x y eq
wordStep-args-canon wle [] ()
wordStep-args-canon wle (_ ∷ []) ()
wordStep-args-canon wle (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon wand (x ∷ y ∷ []) eq = onLits-args andN x y eq
wordStep-args-canon wand [] ()
wordStep-args-canon wand (_ ∷ []) ()
wordStep-args-canon wand (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon wor (x ∷ y ∷ []) eq = onLits-args orN x y eq
wordStep-args-canon wor [] ()
wordStep-args-canon wor (_ ∷ []) ()
wordStep-args-canon wor (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon wxor (x ∷ y ∷ []) eq = onLits-args xorN x y eq
wordStep-args-canon wxor [] ()
wordStep-args-canon wxor (_ ∷ []) ()
wordStep-args-canon wxor (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon wnot (x ∷ []) eq = onUn-args notN x eq
wordStep-args-canon wnot [] ()
wordStep-args-canon wnot (_ ∷ _ ∷ _) ()
wordStep-args-canon wshl (x ∷ n ∷ []) eq = onShift-args shlN x n eq
wordStep-args-canon wshl [] ()
wordStep-args-canon wshl (_ ∷ []) ()
wordStep-args-canon wshl (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon wshr (x ∷ n ∷ []) eq = onShift-args shrN x n eq
wordStep-args-canon wshr [] ()
wordStep-args-canon wshr (_ ∷ []) ()
wordStep-args-canon wshr (_ ∷ _ ∷ _ ∷ _) ()
wordStep-args-canon (wcast k) (t ∷ []) eq with litArg t
wordStep-args-canon (wcast k) (t ∷ []) refl | just lx = litCanon lx ac∷ ac0
wordStep-args-canon (wcast k) (t ∷ []) ()   | nothing
wordStep-args-canon (wcast _) [] ()
wordStep-args-canon (wcast _) (_ ∷ _ ∷ _) ()
wordStep-args-canon wopt (t ∷ []) eq with kindOfTy t
wordStep-args-canon wopt (t ∷ []) refl | just (ty-i64 p) = tyCanon (ty-i64 p) ac∷ ac0
wordStep-args-canon wopt (t ∷ []) refl | just (ty-wd k p) = tyCanon (ty-wd k p) ac∷ ac0
wordStep-args-canon wopt (t ∷ []) ()   | nothing
wordStep-args-canon wopt [] ()
wordStep-args-canon wopt (_ ∷ _ ∷ _) ()
wordStep-args-canon (wty _) _ ()
wordStep-args-canon (wlit _ _) _ ()
wordStep-args-canon wbool _ ()
wordStep-args-canon wtrue _ ()
wordStep-args-canon wfalse _ ()
wordStep-args-canon (woptk _) _ ()
wordStep-args-canon wsome _ ()
wordStep-args-canon wnone _ ()

-- A successful step reads only closed values. Renaming or substituting
-- those values recomputes the same contractum. Kind agreement is split
-- into constructors: a fresh wk≡ᵇ on two variables does not reduce just
-- because an earlier with-branch saw true. A numeral is closed, so
-- renaming it is the identity, proved by induction on the number.

ren-numeral : ∀ {n m} (ρ : Data.Fin.Base.Fin n → Data.Fin.Base.Fin m) (a : ℕ) →
  ren ρ (numeral a) ≡ numeral a
ren-numeral ρ zero    = refl
ren-numeral ρ (suc a) = cong su (ren-numeral ρ a)

sub-numeral : ∀ {n m} (σ : Data.Fin.Base.Fin n → Tm m) (a : ℕ) →
  sub σ (numeral a) ≡ numeral a
sub-numeral σ zero    = refl
sub-numeral σ (suc a) = cong su (sub-numeral σ a)

-- subst from the standard library. Written here so the motive stays Set.
transport : ∀ {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
transport P refl px = px

ℕ←-num : ∀ {n} (a : ℕ) → ℕ← (numeral {n} a) ≡ just (a , refl)
ℕ←-num zero    = refl
ℕ←-num (suc a) =
  transport (λ e → ℕ←-su e ≡ just (suc a , refl)) (sym (ℕ←-num a)) refl

wof-on-num : ∀ {n} k a →
  wordStep (wof k) (numeral {n} a ∷ []) ≡ just (wlitT k (a %w k))
wof-on-num k a =
  transport (λ e → wof-from k e ≡ just (wlitT k (a %w k))) (sym (ℕ←-num a)) refl

wof-ren : ∀ {n m} (ρ : Data.Fin.Base.Fin n → Data.Fin.Base.Fin m) k a →
  wordStep (wof k) (ren ρ (numeral {n} a) ∷ []) ≡ just (wlitT k (a %w k))
wof-ren ρ k a =
  transport (λ t → wordStep (wof k) (t ∷ []) ≡ just (wlitT k (a %w k)))
            (sym (ren-numeral ρ a)) (wof-on-num k a)

wof-sub : ∀ {n m} (σ : Data.Fin.Base.Fin n → Tm m) k a →
  wordStep (wof k) (sub σ (numeral {n} a) ∷ []) ≡ just (wlitT k (a %w k))
wof-sub σ k a =
  transport (λ t → wordStep (wof k) (t ∷ []) ≡ just (wlitT k (a %w k)))
            (sym (sub-numeral σ a)) (wof-on-num k a)

ren-bool : ∀ {n m} (ρ : Data.Fin.Base.Fin n → Data.Fin.Base.Fin m) b →
  ren ρ (boolT b) ≡ boolT b
ren-bool ρ true  = refl
ren-bool ρ false = refl

sub-bool : ∀ {n m} (σ : Data.Fin.Base.Fin n → Tm m) b →
  sub σ (boolT b) ≡ boolT b
sub-bool σ true  = refl
sub-bool σ false = refl

ren-opt : ∀ {n m} (ρ : Data.Fin.Base.Fin n → Data.Fin.Base.Fin m) k mb →
  ren ρ (optTerm {n} k mb) ≡ optTerm k mb
ren-opt ρ k (just _) = refl
ren-opt ρ k nothing  = refl

sub-opt : ∀ {n m} (σ : Data.Fin.Base.Fin n → Tm m) k mb →
  sub σ (optTerm {n} k mb) ≡ optTerm k mb
sub-opt σ k (just _) = refl
sub-opt σ k nothing  = refl

onShift-on-num : ∀ {n} f k a b →
  onShift f (wlitT k a) (numeral {n} b) ≡ just (wlitT k (f k a b))
onShift-on-num f k a b =
  transport
    (λ e → shiftFrom f (wlitT k a) (numeral b) (litArg (wlitT k a)) e
             ≡ just (wlitT k (f k a b)))
    (sym (ℕ←-num b)) refl

onShift-ren-go : ∀ {n m} (ρ : Data.Fin.Base.Fin n → Data.Fin.Base.Fin m) f k a b →
  onShift f (ren ρ (wlitT {n} k a)) (ren ρ (numeral b)) ≡ just (wlitT k (f k a b))
onShift-ren-go ρ f k a b =
  transport (λ amt → onShift f (wlitT k a) amt ≡ just (wlitT k (f k a b)))
            (sym (ren-numeral ρ b)) (onShift-on-num f k a b)

onShift-sub-go : ∀ {n m} (σ : Data.Fin.Base.Fin n → Tm m) f k a b →
  onShift f (sub σ (wlitT {n} k a)) (sub σ (numeral b)) ≡ just (wlitT k (f k a b))
onShift-sub-go σ f k a b =
  transport (λ amt → onShift f (wlitT k a) amt ≡ just (wlitT k (f k a b)))
            (sym (sub-numeral σ b)) (onShift-on-num f k a b)

onLits-both : ∀ {n m r} (ρ : Data.Fin.Base.Fin n → Data.Fin.Base.Fin m)
  (f : WKind → ℕ → ℕ → ℕ) k k′ a b →
  onLits f (wlitT {n} k a) (wlitT k′ b) ≡ just r →
  onLits f (ren ρ (wlitT k a)) (ren ρ (wlitT k′ b)) ≡ just (ren ρ r)
onLits-both ρ f ku8  ku8  a b refl = refl
onLits-both ρ f ku8  ku32 a b ()
onLits-both ρ f ku8  ku64 a b ()
onLits-both ρ f ku8  ki64 a b ()
onLits-both ρ f ku32 ku8  a b ()
onLits-both ρ f ku32 ku32 a b refl = refl
onLits-both ρ f ku32 ku64 a b ()
onLits-both ρ f ku32 ki64 a b ()
onLits-both ρ f ku64 ku8  a b ()
onLits-both ρ f ku64 ku32 a b ()
onLits-both ρ f ku64 ku64 a b refl = refl
onLits-both ρ f ku64 ki64 a b ()
onLits-both ρ f ki64 ku8  a b ()
onLits-both ρ f ki64 ku32 a b ()
onLits-both ρ f ki64 ku64 a b ()
onLits-both ρ f ki64 ki64 a b refl = refl

onLits-both-sub : ∀ {n m r} (σ : Data.Fin.Base.Fin n → Tm m)
  (f : WKind → ℕ → ℕ → ℕ) k k′ a b →
  onLits f (wlitT {n} k a) (wlitT k′ b) ≡ just r →
  onLits f (sub σ (wlitT k a)) (sub σ (wlitT k′ b)) ≡ just (sub σ r)
onLits-both-sub σ f ku8  ku8  a b refl = refl
onLits-both-sub σ f ku8  ku32 a b ()
onLits-both-sub σ f ku8  ku64 a b ()
onLits-both-sub σ f ku8  ki64 a b ()
onLits-both-sub σ f ku32 ku8  a b ()
onLits-both-sub σ f ku32 ku32 a b refl = refl
onLits-both-sub σ f ku32 ku64 a b ()
onLits-both-sub σ f ku32 ki64 a b ()
onLits-both-sub σ f ku64 ku8  a b ()
onLits-both-sub σ f ku64 ku32 a b ()
onLits-both-sub σ f ku64 ku64 a b refl = refl
onLits-both-sub σ f ku64 ki64 a b ()
onLits-both-sub σ f ki64 ku8  a b ()
onLits-both-sub σ f ki64 ku32 a b ()
onLits-both-sub σ f ki64 ku64 a b ()
onLits-both-sub σ f ki64 ki64 a b refl = refl

onCmp-both : ∀ {n m r} (ρ : Data.Fin.Base.Fin n → Data.Fin.Base.Fin m)
  (f : WKind → ℕ → ℕ → Bool) k k′ a b →
  onCmp f (wlitT {n} k a) (wlitT k′ b) ≡ just r →
  onCmp f (ren ρ (wlitT k a)) (ren ρ (wlitT k′ b)) ≡ just (ren ρ r)
onCmp-both ρ f ku8  ku8  a b refl = cong just (sym (ren-bool ρ (f ku8 a b)))
onCmp-both ρ f ku8  ku32 a b ()
onCmp-both ρ f ku8  ku64 a b ()
onCmp-both ρ f ku8  ki64 a b ()
onCmp-both ρ f ku32 ku8  a b ()
onCmp-both ρ f ku32 ku32 a b refl = cong just (sym (ren-bool ρ (f ku32 a b)))
onCmp-both ρ f ku32 ku64 a b ()
onCmp-both ρ f ku32 ki64 a b ()
onCmp-both ρ f ku64 ku8  a b ()
onCmp-both ρ f ku64 ku32 a b ()
onCmp-both ρ f ku64 ku64 a b refl = cong just (sym (ren-bool ρ (f ku64 a b)))
onCmp-both ρ f ku64 ki64 a b ()
onCmp-both ρ f ki64 ku8  a b ()
onCmp-both ρ f ki64 ku32 a b ()
onCmp-both ρ f ki64 ku64 a b ()
onCmp-both ρ f ki64 ki64 a b refl = cong just (sym (ren-bool ρ (f ki64 a b)))

onCmp-both-sub : ∀ {n m r} (σ : Data.Fin.Base.Fin n → Tm m)
  (f : WKind → ℕ → ℕ → Bool) k k′ a b →
  onCmp f (wlitT {n} k a) (wlitT k′ b) ≡ just r →
  onCmp f (sub σ (wlitT k a)) (sub σ (wlitT k′ b)) ≡ just (sub σ r)
onCmp-both-sub σ f ku8  ku8  a b refl = cong just (sym (sub-bool σ (f ku8 a b)))
onCmp-both-sub σ f ku8  ku32 a b ()
onCmp-both-sub σ f ku8  ku64 a b ()
onCmp-both-sub σ f ku8  ki64 a b ()
onCmp-both-sub σ f ku32 ku8  a b ()
onCmp-both-sub σ f ku32 ku32 a b refl = cong just (sym (sub-bool σ (f ku32 a b)))
onCmp-both-sub σ f ku32 ku64 a b ()
onCmp-both-sub σ f ku32 ki64 a b ()
onCmp-both-sub σ f ku64 ku8  a b ()
onCmp-both-sub σ f ku64 ku32 a b ()
onCmp-both-sub σ f ku64 ku64 a b refl = cong just (sym (sub-bool σ (f ku64 a b)))
onCmp-both-sub σ f ku64 ki64 a b ()
onCmp-both-sub σ f ki64 ku8  a b ()
onCmp-both-sub σ f ki64 ku32 a b ()
onCmp-both-sub σ f ki64 ku64 a b ()
onCmp-both-sub σ f ki64 ki64 a b refl = cong just (sym (sub-bool σ (f ki64 a b)))

onOpt-both : ∀ {n m r} (ρ : Data.Fin.Base.Fin n → Data.Fin.Base.Fin m)
  (f : WKind → ℕ → ℕ → Maybe ℕ) k k′ a b →
  onOpt f (wlitT {n} k a) (wlitT k′ b) ≡ just r →
  onOpt f (ren ρ (wlitT k a)) (ren ρ (wlitT k′ b)) ≡ just (ren ρ r)
onOpt-both ρ f ku8  ku8  a b refl = cong just (sym (ren-opt ρ ku8 (f ku8 a b)))
onOpt-both ρ f ku8  ku32 a b ()
onOpt-both ρ f ku8  ku64 a b ()
onOpt-both ρ f ku8  ki64 a b ()
onOpt-both ρ f ku32 ku8  a b ()
onOpt-both ρ f ku32 ku32 a b refl = cong just (sym (ren-opt ρ ku32 (f ku32 a b)))
onOpt-both ρ f ku32 ku64 a b ()
onOpt-both ρ f ku32 ki64 a b ()
onOpt-both ρ f ku64 ku8  a b ()
onOpt-both ρ f ku64 ku32 a b ()
onOpt-both ρ f ku64 ku64 a b refl = cong just (sym (ren-opt ρ ku64 (f ku64 a b)))
onOpt-both ρ f ku64 ki64 a b ()
onOpt-both ρ f ki64 ku8  a b ()
onOpt-both ρ f ki64 ku32 a b ()
onOpt-both ρ f ki64 ku64 a b ()
onOpt-both ρ f ki64 ki64 a b refl = cong just (sym (ren-opt ρ ki64 (f ki64 a b)))

onOpt-both-sub : ∀ {n m r} (σ : Data.Fin.Base.Fin n → Tm m)
  (f : WKind → ℕ → ℕ → Maybe ℕ) k k′ a b →
  onOpt f (wlitT {n} k a) (wlitT k′ b) ≡ just r →
  onOpt f (sub σ (wlitT k a)) (sub σ (wlitT k′ b)) ≡ just (sub σ r)
onOpt-both-sub σ f ku8  ku8  a b refl = cong just (sym (sub-opt σ ku8 (f ku8 a b)))
onOpt-both-sub σ f ku8  ku32 a b ()
onOpt-both-sub σ f ku8  ku64 a b ()
onOpt-both-sub σ f ku8  ki64 a b ()
onOpt-both-sub σ f ku32 ku8  a b ()
onOpt-both-sub σ f ku32 ku32 a b refl = cong just (sym (sub-opt σ ku32 (f ku32 a b)))
onOpt-both-sub σ f ku32 ku64 a b ()
onOpt-both-sub σ f ku32 ki64 a b ()
onOpt-both-sub σ f ku64 ku8  a b ()
onOpt-both-sub σ f ku64 ku32 a b ()
onOpt-both-sub σ f ku64 ku64 a b refl = cong just (sym (sub-opt σ ku64 (f ku64 a b)))
onOpt-both-sub σ f ku64 ki64 a b ()
onOpt-both-sub σ f ki64 ku8  a b ()
onOpt-both-sub σ f ki64 ku32 a b ()
onOpt-both-sub σ f ki64 ku64 a b ()
onOpt-both-sub σ f ki64 ki64 a b refl = cong just (sym (sub-opt σ ki64 (f ki64 a b)))

onLits-ren : ∀ {n m} (ρ : Data.Fin.Base.Fin n → Data.Fin.Base.Fin m) f (x y : Tm n) {r}
  → onLits f x y ≡ just r → onLits f (ren ρ x) (ren ρ y) ≡ just (ren ρ r)
onLits-ren ρ f x y eq with litArg x | litArg y
onLits-ren ρ f x y eq | just (k , a , refl) | just (k′ , b , refl) =
  onLits-both ρ f k k′ a b eq
onLits-ren ρ f x y () | just _ | nothing
onLits-ren ρ f x y () | nothing | just _
onLits-ren ρ f x y () | nothing | nothing

onLits-sub : ∀ {n m} (σ : Data.Fin.Base.Fin n → Tm m) f (x y : Tm n) {r}
  → onLits f x y ≡ just r → onLits f (sub σ x) (sub σ y) ≡ just (sub σ r)
onLits-sub σ f x y eq with litArg x | litArg y
onLits-sub σ f x y eq | just (k , a , refl) | just (k′ , b , refl) =
  onLits-both-sub σ f k k′ a b eq
onLits-sub σ f x y () | just _ | nothing
onLits-sub σ f x y () | nothing | just _
onLits-sub σ f x y () | nothing | nothing

onCmp-ren : ∀ {n m} (ρ : Data.Fin.Base.Fin n → Data.Fin.Base.Fin m) f (x y : Tm n) {r}
  → onCmp f x y ≡ just r → onCmp f (ren ρ x) (ren ρ y) ≡ just (ren ρ r)
onCmp-ren ρ f x y eq with litArg x | litArg y
onCmp-ren ρ f x y eq | just (k , a , refl) | just (k′ , b , refl) =
  onCmp-both ρ f k k′ a b eq
onCmp-ren ρ f x y () | just _ | nothing
onCmp-ren ρ f x y () | nothing | just _
onCmp-ren ρ f x y () | nothing | nothing

onCmp-sub : ∀ {n m} (σ : Data.Fin.Base.Fin n → Tm m) f (x y : Tm n) {r}
  → onCmp f x y ≡ just r → onCmp f (sub σ x) (sub σ y) ≡ just (sub σ r)
onCmp-sub σ f x y eq with litArg x | litArg y
onCmp-sub σ f x y eq | just (k , a , refl) | just (k′ , b , refl) =
  onCmp-both-sub σ f k k′ a b eq
onCmp-sub σ f x y () | just _ | nothing
onCmp-sub σ f x y () | nothing | just _
onCmp-sub σ f x y () | nothing | nothing

onOpt-ren : ∀ {n m} (ρ : Data.Fin.Base.Fin n → Data.Fin.Base.Fin m) f (x y : Tm n) {r}
  → onOpt f x y ≡ just r → onOpt f (ren ρ x) (ren ρ y) ≡ just (ren ρ r)
onOpt-ren ρ f x y eq with litArg x | litArg y
onOpt-ren ρ f x y eq | just (k , a , refl) | just (k′ , b , refl) =
  onOpt-both ρ f k k′ a b eq
onOpt-ren ρ f x y () | just _ | nothing
onOpt-ren ρ f x y () | nothing | just _
onOpt-ren ρ f x y () | nothing | nothing

onOpt-sub : ∀ {n m} (σ : Data.Fin.Base.Fin n → Tm m) f (x y : Tm n) {r}
  → onOpt f x y ≡ just r → onOpt f (sub σ x) (sub σ y) ≡ just (sub σ r)
onOpt-sub σ f x y eq with litArg x | litArg y
onOpt-sub σ f x y eq | just (k , a , refl) | just (k′ , b , refl) =
  onOpt-both-sub σ f k k′ a b eq
onOpt-sub σ f x y () | just _ | nothing
onOpt-sub σ f x y () | nothing | just _
onOpt-sub σ f x y () | nothing | nothing

onUn-ren : ∀ {n m} (ρ : Data.Fin.Base.Fin n → Data.Fin.Base.Fin m) f (x : Tm n) {r}
  → onUn f x ≡ just r → onUn f (ren ρ x) ≡ just (ren ρ r)
onUn-ren ρ f x eq with litArg x
onUn-ren ρ f x refl | just (_ , _ , refl) = refl
onUn-ren ρ f x ()   | nothing

onUn-sub : ∀ {n m} (σ : Data.Fin.Base.Fin n → Tm m) f (x : Tm n) {r}
  → onUn f x ≡ just r → onUn f (sub σ x) ≡ just (sub σ r)
onUn-sub σ f x eq with litArg x
onUn-sub σ f x refl | just (_ , _ , refl) = refl
onUn-sub σ f x ()   | nothing

onShift-ren : ∀ {n m} (ρ : Data.Fin.Base.Fin n → Data.Fin.Base.Fin m) f (x n′ : Tm n) {r}
  → onShift f x n′ ≡ just r → onShift f (ren ρ x) (ren ρ n′) ≡ just (ren ρ r)
onShift-ren ρ f x n′ eq with litArg x | ℕ← n′
onShift-ren ρ f x n′ refl | just (k , a , refl) | just (b , refl) =
  onShift-ren-go ρ f k a b
onShift-ren ρ f x n′ ()   | just _ | nothing
onShift-ren ρ f x n′ ()   | nothing | just _
onShift-ren ρ f x n′ ()   | nothing | nothing

onShift-sub : ∀ {n m} (σ : Data.Fin.Base.Fin n → Tm m) f (x n′ : Tm n) {r}
  → onShift f x n′ ≡ just r → onShift f (sub σ x) (sub σ n′) ≡ just (sub σ r)
onShift-sub σ f x n′ eq with litArg x | ℕ← n′
onShift-sub σ f x n′ refl | just (k , a , refl) | just (b , refl) =
  onShift-sub-go σ f k a b
onShift-sub σ f x n′ ()   | just _ | nothing
onShift-sub σ f x n′ ()   | nothing | just _
onShift-sub σ f x n′ ()   | nothing | nothing

wordStep-ren : ∀ {n m} (ρ : Data.Fin.Base.Fin n → Data.Fin.Base.Fin m) op (ts : List (Tm n)) {r}
  → wordStep op ts ≡ just r → wordStep op (renList ρ ts) ≡ just (ren ρ r)
wordStep-ren ρ (wof k) (t ∷ []) eq with ℕ← t
wordStep-ren ρ (wof k) (t ∷ []) refl | just (a , refl) = wof-ren ρ k a
wordStep-ren ρ (wof _) (t ∷ []) ()   | nothing
wordStep-ren ρ (wof _) [] ()
wordStep-ren ρ (wof _) (_ ∷ _ ∷ _) ()
wordStep-ren ρ wton (t ∷ []) eq with litArg t
wordStep-ren ρ wton (t ∷ []) refl | just (k , a , refl) =
  cong just (sym (ren-numeral ρ (a %w k)))
wordStep-ren ρ wton (t ∷ []) ()   | nothing
wordStep-ren ρ wton [] ()
wordStep-ren ρ wton (_ ∷ _ ∷ _) ()
wordStep-ren ρ wadd (x ∷ y ∷ []) eq = onLits-ren ρ wrapAddN x y eq
wordStep-ren ρ wadd [] ()
wordStep-ren ρ wadd (_ ∷ []) ()
wordStep-ren ρ wadd (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ wsub (x ∷ y ∷ []) eq = onLits-ren ρ wrapSubN x y eq
wordStep-ren ρ wsub [] ()
wordStep-ren ρ wsub (_ ∷ []) ()
wordStep-ren ρ wsub (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ wmul (x ∷ y ∷ []) eq = onLits-ren ρ wrapMulN x y eq
wordStep-ren ρ wmul [] ()
wordStep-ren ρ wmul (_ ∷ []) ()
wordStep-ren ρ wmul (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ wcadd (x ∷ y ∷ []) eq = onOpt-ren ρ checkedAddN x y eq
wordStep-ren ρ wcadd [] ()
wordStep-ren ρ wcadd (_ ∷ []) ()
wordStep-ren ρ wcadd (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ wcsub (x ∷ y ∷ []) eq = onOpt-ren ρ checkedSubN x y eq
wordStep-ren ρ wcsub [] ()
wordStep-ren ρ wcsub (_ ∷ []) ()
wordStep-ren ρ wcsub (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ wcmul (x ∷ y ∷ []) eq = onOpt-ren ρ checkedMulN x y eq
wordStep-ren ρ wcmul [] ()
wordStep-ren ρ wcmul (_ ∷ []) ()
wordStep-ren ρ wcmul (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ wdiv (x ∷ y ∷ []) eq = onOpt-ren ρ divPayload x y eq
wordStep-ren ρ wdiv [] ()
wordStep-ren ρ wdiv (_ ∷ []) ()
wordStep-ren ρ wdiv (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ wrem (x ∷ y ∷ []) eq = onOpt-ren ρ remPayload x y eq
wordStep-ren ρ wrem [] ()
wordStep-ren ρ wrem (_ ∷ []) ()
wordStep-ren ρ wrem (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ weq (x ∷ y ∷ []) eq = onCmp-ren ρ eqN x y eq
wordStep-ren ρ weq [] ()
wordStep-ren ρ weq (_ ∷ []) ()
wordStep-ren ρ weq (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ wlt (x ∷ y ∷ []) eq = onCmp-ren ρ ltN x y eq
wordStep-ren ρ wlt [] ()
wordStep-ren ρ wlt (_ ∷ []) ()
wordStep-ren ρ wlt (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ wle (x ∷ y ∷ []) eq = onCmp-ren ρ leN x y eq
wordStep-ren ρ wle [] ()
wordStep-ren ρ wle (_ ∷ []) ()
wordStep-ren ρ wle (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ wand (x ∷ y ∷ []) eq = onLits-ren ρ andN x y eq
wordStep-ren ρ wand [] ()
wordStep-ren ρ wand (_ ∷ []) ()
wordStep-ren ρ wand (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ wor (x ∷ y ∷ []) eq = onLits-ren ρ orN x y eq
wordStep-ren ρ wor [] ()
wordStep-ren ρ wor (_ ∷ []) ()
wordStep-ren ρ wor (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ wxor (x ∷ y ∷ []) eq = onLits-ren ρ xorN x y eq
wordStep-ren ρ wxor [] ()
wordStep-ren ρ wxor (_ ∷ []) ()
wordStep-ren ρ wxor (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ wnot (x ∷ []) eq = onUn-ren ρ notN x eq
wordStep-ren ρ wnot [] ()
wordStep-ren ρ wnot (_ ∷ _ ∷ _) ()
wordStep-ren ρ wshl (x ∷ n′ ∷ []) eq = onShift-ren ρ shlN x n′ eq
wordStep-ren ρ wshl [] ()
wordStep-ren ρ wshl (_ ∷ []) ()
wordStep-ren ρ wshl (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ wshr (x ∷ n′ ∷ []) eq = onShift-ren ρ shrN x n′ eq
wordStep-ren ρ wshr [] ()
wordStep-ren ρ wshr (_ ∷ []) ()
wordStep-ren ρ wshr (_ ∷ _ ∷ _ ∷ _) ()
wordStep-ren ρ (wcast k) (t ∷ []) eq with litArg t
wordStep-ren ρ (wcast k) (t ∷ []) refl | just (_ , _ , refl) = refl
wordStep-ren ρ (wcast _) (t ∷ []) ()   | nothing
wordStep-ren ρ (wcast _) [] ()
wordStep-ren ρ (wcast _) (_ ∷ _ ∷ _) ()
wordStep-ren ρ wopt (t ∷ []) eq with kindOfTy t
wordStep-ren ρ wopt (t ∷ []) refl | just (ty-i64 refl) = refl
wordStep-ren ρ wopt (t ∷ []) refl | just (ty-wd _ refl) = refl
wordStep-ren ρ wopt (t ∷ []) ()   | nothing
wordStep-ren ρ wopt [] ()
wordStep-ren ρ wopt (_ ∷ _ ∷ _) ()
wordStep-ren ρ (wty _) _ ()
wordStep-ren ρ (wlit _ _) _ ()
wordStep-ren ρ wbool _ ()
wordStep-ren ρ wtrue _ ()
wordStep-ren ρ wfalse _ ()
wordStep-ren ρ (woptk _) _ ()
wordStep-ren ρ wsome _ ()
wordStep-ren ρ wnone _ ()

wordStep-sub : ∀ {n m} (σ : Data.Fin.Base.Fin n → Tm m) op (ts : List (Tm n)) {r}
  → wordStep op ts ≡ just r → wordStep op (subList σ ts) ≡ just (sub σ r)
wordStep-sub σ (wof k) (t ∷ []) eq with ℕ← t
wordStep-sub σ (wof k) (t ∷ []) refl | just (a , refl) = wof-sub σ k a
wordStep-sub σ (wof _) (t ∷ []) ()   | nothing
wordStep-sub σ (wof _) [] ()
wordStep-sub σ (wof _) (_ ∷ _ ∷ _) ()
wordStep-sub σ wton (t ∷ []) eq with litArg t
wordStep-sub σ wton (t ∷ []) refl | just (k , a , refl) =
  cong just (sym (sub-numeral σ (a %w k)))
wordStep-sub σ wton (t ∷ []) ()   | nothing
wordStep-sub σ wton [] ()
wordStep-sub σ wton (_ ∷ _ ∷ _) ()
wordStep-sub σ wadd (x ∷ y ∷ []) eq = onLits-sub σ wrapAddN x y eq
wordStep-sub σ wadd [] ()
wordStep-sub σ wadd (_ ∷ []) ()
wordStep-sub σ wadd (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ wsub (x ∷ y ∷ []) eq = onLits-sub σ wrapSubN x y eq
wordStep-sub σ wsub [] ()
wordStep-sub σ wsub (_ ∷ []) ()
wordStep-sub σ wsub (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ wmul (x ∷ y ∷ []) eq = onLits-sub σ wrapMulN x y eq
wordStep-sub σ wmul [] ()
wordStep-sub σ wmul (_ ∷ []) ()
wordStep-sub σ wmul (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ wcadd (x ∷ y ∷ []) eq = onOpt-sub σ checkedAddN x y eq
wordStep-sub σ wcadd [] ()
wordStep-sub σ wcadd (_ ∷ []) ()
wordStep-sub σ wcadd (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ wcsub (x ∷ y ∷ []) eq = onOpt-sub σ checkedSubN x y eq
wordStep-sub σ wcsub [] ()
wordStep-sub σ wcsub (_ ∷ []) ()
wordStep-sub σ wcsub (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ wcmul (x ∷ y ∷ []) eq = onOpt-sub σ checkedMulN x y eq
wordStep-sub σ wcmul [] ()
wordStep-sub σ wcmul (_ ∷ []) ()
wordStep-sub σ wcmul (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ wdiv (x ∷ y ∷ []) eq = onOpt-sub σ divPayload x y eq
wordStep-sub σ wdiv [] ()
wordStep-sub σ wdiv (_ ∷ []) ()
wordStep-sub σ wdiv (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ wrem (x ∷ y ∷ []) eq = onOpt-sub σ remPayload x y eq
wordStep-sub σ wrem [] ()
wordStep-sub σ wrem (_ ∷ []) ()
wordStep-sub σ wrem (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ weq (x ∷ y ∷ []) eq = onCmp-sub σ eqN x y eq
wordStep-sub σ weq [] ()
wordStep-sub σ weq (_ ∷ []) ()
wordStep-sub σ weq (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ wlt (x ∷ y ∷ []) eq = onCmp-sub σ ltN x y eq
wordStep-sub σ wlt [] ()
wordStep-sub σ wlt (_ ∷ []) ()
wordStep-sub σ wlt (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ wle (x ∷ y ∷ []) eq = onCmp-sub σ leN x y eq
wordStep-sub σ wle [] ()
wordStep-sub σ wle (_ ∷ []) ()
wordStep-sub σ wle (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ wand (x ∷ y ∷ []) eq = onLits-sub σ andN x y eq
wordStep-sub σ wand [] ()
wordStep-sub σ wand (_ ∷ []) ()
wordStep-sub σ wand (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ wor (x ∷ y ∷ []) eq = onLits-sub σ orN x y eq
wordStep-sub σ wor [] ()
wordStep-sub σ wor (_ ∷ []) ()
wordStep-sub σ wor (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ wxor (x ∷ y ∷ []) eq = onLits-sub σ xorN x y eq
wordStep-sub σ wxor [] ()
wordStep-sub σ wxor (_ ∷ []) ()
wordStep-sub σ wxor (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ wnot (x ∷ []) eq = onUn-sub σ notN x eq
wordStep-sub σ wnot [] ()
wordStep-sub σ wnot (_ ∷ _ ∷ _) ()
wordStep-sub σ wshl (x ∷ n′ ∷ []) eq = onShift-sub σ shlN x n′ eq
wordStep-sub σ wshl [] ()
wordStep-sub σ wshl (_ ∷ []) ()
wordStep-sub σ wshl (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ wshr (x ∷ n′ ∷ []) eq = onShift-sub σ shrN x n′ eq
wordStep-sub σ wshr [] ()
wordStep-sub σ wshr (_ ∷ []) ()
wordStep-sub σ wshr (_ ∷ _ ∷ _ ∷ _) ()
wordStep-sub σ (wcast k) (t ∷ []) eq with litArg t
wordStep-sub σ (wcast k) (t ∷ []) refl | just (_ , _ , refl) = refl
wordStep-sub σ (wcast _) (t ∷ []) ()   | nothing
wordStep-sub σ (wcast _) [] ()
wordStep-sub σ (wcast _) (_ ∷ _ ∷ _) ()
wordStep-sub σ wopt (t ∷ []) eq with kindOfTy t
wordStep-sub σ wopt (t ∷ []) refl | just (ty-i64 refl) = refl
wordStep-sub σ wopt (t ∷ []) refl | just (ty-wd _ refl) = refl
wordStep-sub σ wopt (t ∷ []) ()   | nothing
wordStep-sub σ wopt [] ()
wordStep-sub σ wopt (_ ∷ _ ∷ _) ()
wordStep-sub σ (wty _) _ ()
wordStep-sub σ (wlit _ _) _ ()
wordStep-sub σ wbool _ ()
wordStep-sub σ wtrue _ ()
wordStep-sub σ wfalse _ ()
wordStep-sub σ (woptk _) _ ()
wordStep-sub σ wsome _ ()
wordStep-sub σ wnone _ ()

------------------------------------------------------------------------
-- Closed residue computations. Each one is definitional.
------------------------------------------------------------------------

ex-add : wrapAddN ku8 200 100 ≡ 44
ex-add = refl

ex-add-max : wrapAddN ku8 255 1 ≡ 0
ex-add-max = refl

ex-sub-wrap : wrapSubN ku8 1 2 ≡ 255
ex-sub-wrap = refl

ex-mul : wrapMulN ku8 20 20 ≡ 144
ex-mul = refl

ex-cadd-over : checkedAddN ku8 200 100 ≡ nothing
ex-cadd-over = refl

ex-cadd-ok : checkedAddN ku8 1 2 ≡ just 3
ex-cadd-ok = refl

ex-csub-borrow : checkedSubN ku8 0 1 ≡ nothing
ex-csub-borrow = refl

ex-cmul-over : checkedMulN ku8 20 20 ≡ nothing
ex-cmul-over = refl

ex-shl : shlN ku8 1 7 ≡ 128
ex-shl = refl

ex-shl-wide : shlN ku8 1 8 ≡ 0
ex-shl-wide = refl

ex-shr : shrN ku8 128 7 ≡ 1
ex-shr = refl

ex-not0 : notN ku8 0 ≡ 255
ex-not0 = refl

ex-div0 : divPayload ku8 10 0 ≡ nothing
ex-div0 = refl

ex-div : divPayload ku8 10 3 ≡ just 3
ex-div = refl

ex-rem : remPayload ku8 10 3 ≡ just 1
ex-rem = refl

-- Signed residues at 2^63 and above are not closed `refl` tests here:
-- the standard-library remainder walks the dividend. The signed
-- equations are the lemmas above (wrapAdd-mod, div-iff, inRange).

ex-step : ∀ {n} →
  wordStep wadd (wlitT {n} ku8 200 ∷ wlitT ku8 100 ∷ []) ≡ just (wlitT ku8 44)
ex-step = refl

ex-of : toℕ (ofNatF ku8 300) ≡ 44
ex-of = toNat∘ofNat ku8 300

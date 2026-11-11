------------------------------------------------------------------------
-- Grades on an affine binder. A binder may carry a pair `(c, t)`.
-- `c` is how many times run and evidence use the variable. `t` is how
-- many times a type uses it. Neither component is a constructor of
-- Qty, and neither is added to Tm.
--
-- An unmarked binder is the interval [0, 1]: at most one run use.
-- `checkGrade` on that interval is `checkBound` for the affine
-- quantity (`ungraded-fragment`). Grade 1 is the `%1` mark
-- (`linear-is-one`). Grade 0 is the erased quantity. Grade ω is the
-- reusable quantity. Spec forgets the computational obligation.
--
-- The internal term `GTm` is the grade judgment: a binder, an
-- application, and a match. Application adds the two counts. It does
-- not scale the argument by the domain grade. A match takes the
-- maximum of the branches. The predecessor inherits the scrutinee
-- variable's grade, or the affine interval and ω when the scrutinee
-- is not a variable. The motive is checked in spec and its binder
-- carries no grade.
--
-- The Elixir checker follows `checkGrade` (`lib/muro/grade.ex`).
-- The emitters erase a grade pair back to the affine quantity.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Grade where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _⊔_; _⊓_; _≤ᵇ_; _≡ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product.Base using (_×_; _,_)
open import Data.String.Base using (String; _++_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (Mode; run; spec; evid; Qty; affine; reuse; erased; Use; U0; U1; Uω; Result; ok; fail; _>>=_; _>>_)
open import Muro.Env using (checkBound)
open import Muro.Arrow using (checkArrow; m1)

------------------------------------------------------------------------
-- Points and grades. 0 ≤ 1 ≤ … ≤ ω. An interval is inclusive.
-- [ω, ω] accepts every count, the same as the point ω. A tighter
-- grade is smaller: a point lies under an interval that contains it.
------------------------------------------------------------------------

data Point : Set where
  fin : ℕ → Point
  inf : Point

data Grade : Set where
  pt : Point → Grade
  iv : Point → Point → Grade

g0 : Grade
g0 = pt (fin zero)

g1 : Grade
g1 = pt (fin (suc zero))

gω : Grade
gω = pt inf

-- The unmarked binder: at most one computational use.
aff : Grade
aff = iv (fin zero) (fin (suc zero))

_≤ᵖ_ : Point → Point → Bool
fin m ≤ᵖ fin n = m ≤ᵇ n
fin _ ≤ᵖ inf   = true
inf   ≤ᵖ fin _ = false
inf   ≤ᵖ inf   = true

_⊔ᵖ_ : Point → Point → Point
fin m ⊔ᵖ fin n = fin (m ⊔ n)
fin _ ⊔ᵖ inf   = inf
inf   ⊔ᵖ _     = inf

_⊓ᵖ_ : Point → Point → Point
fin m ⊓ᵖ fin n = fin (m ⊓ n)
fin m ⊓ᵖ inf   = fin m
inf   ⊓ᵖ p     = p

-- Inclusion on intervals. A point is the degenerate interval at that point.
_≤ᵍ_ : Grade → Grade → Bool
pt p    ≤ᵍ pt q    = p ≤ᵖ q
pt p    ≤ᵍ iv lo hi = lo ≤ᵖ p ∧ p ≤ᵖ hi
iv a b  ≤ᵍ pt p    = a ≤ᵖ p ∧ p ≤ᵖ a ∧ b ≤ᵖ p ∧ p ≤ᵖ b
iv a b  ≤ᵍ iv c d  = c ≤ᵖ a ∧ b ≤ᵖ d

-- Join is the hull. Meet is the intersection, which may be inverted
-- when the intervals are disjoint. The parser rejects an empty interval.
_⊔ᵍ_ : Grade → Grade → Grade
pt p   ⊔ᵍ pt q   = pt (p ⊔ᵖ q)
pt p   ⊔ᵍ iv a b = iv (a ⊓ᵖ p) (b ⊔ᵖ p)
iv a b ⊔ᵍ pt p   = iv (a ⊓ᵖ p) (b ⊔ᵖ p)
iv a b ⊔ᵍ iv c d = iv (a ⊓ᵖ c) (b ⊔ᵖ d)

_⊓ᵍ_ : Grade → Grade → Grade
pt p   ⊓ᵍ pt q   = pt (p ⊓ᵖ q)
pt p   ⊓ᵍ iv a b = iv (a ⊔ᵖ p) (b ⊓ᵖ p)
iv a b ⊓ᵍ pt p   = iv (a ⊔ᵖ p) (b ⊓ᵖ p)
iv a b ⊓ᵍ iv c d = iv (a ⊔ᵖ c) (b ⊓ᵖ d)

≤-0-1 : (fin zero ≤ᵖ fin (suc zero)) ≡ true
≤-0-1 = refl

≤-1-ω : (fin (suc zero) ≤ᵖ inf) ≡ true
≤-1-ω = refl

≤-ω-1 : (inf ≤ᵖ fin (suc zero)) ≡ false
≤-ω-1 = refl

join-0-1 : (fin zero ⊔ᵖ fin (suc zero)) ≡ fin (suc zero)
join-0-1 = refl

meet-1-ω : (fin (suc zero) ⊓ᵖ inf) ≡ fin (suc zero)
meet-1-ω = refl

join-g0-g1 : (g0 ⊔ᵍ g1) ≡ g1
join-g0-g1 = refl

join-g1-gω : (g1 ⊔ᵍ gω) ≡ gω
join-g1-gω = refl

meet-g0-g1 : (g0 ⊓ᵍ g1) ≡ g0
meet-g0-g1 = refl

meet-g1-gω : (g1 ⊓ᵍ gω) ≡ g1
meet-g1-gω = refl

g0≤aff : (g0 ≤ᵍ aff) ≡ true
g0≤aff = refl

g1≤aff : (g1 ≤ᵍ aff) ≡ true
g1≤aff = refl

gω≰aff : (gω ≤ᵍ aff) ≡ false
gω≰aff = refl

------------------------------------------------------------------------
-- A count is a finite number of textual uses, or many.
------------------------------------------------------------------------

data Count : Set where
  finᶜ : ℕ → Count
  many : Count

embed : Use → Count
embed U0 = finᶜ zero
embed U1 = finᶜ (suc zero)
embed Uω = many

showPoint : Point → String
showPoint (fin n) = showℕ n
showPoint inf     = "ω"

showGrade : Grade → String
showGrade (pt p)    = showPoint p
showGrade (iv a b)  = "[" ++ showPoint a ++ ", " ++ showPoint b ++ "]"

showCount : Count → String
showCount (finᶜ n) = showℕ n
showCount many     = "ω"

-- Exact point: that finite count. ω: every count. An interval holds a
-- finite count inside it, and holds many when its upper bound is ω.
-- [ω, ω] holds every count.
sat : Grade → Count → Bool
sat (pt (fin n)) (finᶜ k) = n ≡ᵇ k
sat (pt (fin _)) many     = false
sat (pt inf)     _        = true
sat (iv inf inf) _        = true
sat (iv lo hi)   (finᶜ k) = lo ≤ᵖ fin k ∧ fin k ≤ᵖ hi
sat (iv _ hi)    many     = hi ≤ᵖ inf ∧ inf ≤ᵖ hi

-- Messages that the kernel already uses, on the grades that are those
-- quantities. Every other refusal names the grade and the count.
refuse : Grade → Count → String
refuse (pt (fin zero))           _                = "erased variable used computationally"
refuse (pt (fin (suc zero)))     (finᶜ zero)      = "linear variable unused"
refuse (pt (fin (suc zero)))     many             = "affine variable used as reusable"
refuse (iv (fin zero) (fin (suc zero))) many      = "affine variable used as reusable"
refuse g                         k                = "grade " ++ showGrade g ++ " does not allow " ++ showCount k ++ " uses"

typeRefuse : Grade → Count → String
typeRefuse g k = "type grade " ++ showGrade g ++ " does not allow " ++ showCount k ++ " uses"

-- Spec forgets computational uses. Otherwise the count must sit in the grade.
checkCount : Mode → Grade → Count → Result ⊤
checkCount spec _ _ = ok tt
checkCount _    g k = if sat g k then ok tt else fail (refuse g k)

checkType : Grade → Count → Result ⊤
checkType g k = if sat g k then ok tt else fail (typeRefuse g k)

checkGrade : Mode → Grade → Use → Result ⊤
checkGrade m g u = checkCount m g (embed u)

-- An unmarked binder is the affine interval, and its check is the affine one.
ungraded-fragment : ∀ m u → checkGrade m aff u ≡ checkBound m affine u
ungraded-fragment run  U0 = refl
ungraded-fragment run  U1 = refl
ungraded-fragment run  Uω = refl
ungraded-fragment spec U0 = refl
ungraded-fragment spec U1 = refl
ungraded-fragment spec Uω = refl
ungraded-fragment evid U0 = refl
ungraded-fragment evid U1 = refl
ungraded-fragment evid Uω = refl

-- Grade 1 is the `%1` mark.
linear-is-one : ∀ m u → checkGrade m g1 u ≡ checkArrow m m1 u
linear-is-one run  U0 = refl
linear-is-one run  U1 = refl
linear-is-one run  Uω = refl
linear-is-one spec U0 = refl
linear-is-one spec U1 = refl
linear-is-one spec Uω = refl
linear-is-one evid U0 = refl
linear-is-one evid U1 = refl
linear-is-one evid Uω = refl

-- Grade 0 is the erased quantity.
erased-is-zero : ∀ m u → checkGrade m g0 u ≡ checkBound m erased u
erased-is-zero run  U0 = refl
erased-is-zero run  U1 = refl
erased-is-zero run  Uω = refl
erased-is-zero spec U0 = refl
erased-is-zero spec U1 = refl
erased-is-zero spec Uω = refl
erased-is-zero evid U0 = refl
erased-is-zero evid U1 = refl
erased-is-zero evid Uω = refl

-- Grade ω is the reusable quantity.
reuse-is-omega : ∀ m u → checkGrade m gω u ≡ checkBound m reuse u
reuse-is-omega run  U0 = refl
reuse-is-omega run  U1 = refl
reuse-is-omega run  Uω = refl
reuse-is-omega spec U0 = refl
reuse-is-omega spec U1 = refl
reuse-is-omega spec Uω = refl
reuse-is-omega evid U0 = refl
reuse-is-omega evid U1 = refl
reuse-is-omega evid Uω = refl

------------------------------------------------------------------------
-- The grade judgment. Not a term of the core theory.
------------------------------------------------------------------------

data Pair : Set where
  gp : Grade → Grade → Pair

data Spent : Set where
  sp : Count → Count → Spent

Uses : ℕ → Set
Uses n = Vec Spent n

GCtx : ℕ → Set
GCtx n = Vec Pair n

data GTm (n : ℕ) : Set where
  gvar   : Fin n → GTm n
  gtyp   : Fin n → GTm n
  glam   : Grade → Grade → GTm (suc n) → GTm n
  gpi    : Grade → Grade → GTm (suc n) → GTm n
  gapp   : GTm n → GTm n → GTm n
  gze    : GTm n
  gsu    : GTm n → GTm n
  gmatch : GTm n → GTm n → GTm (suc n) → GTm n

zeros : ∀ {n} → Uses n
zeros {zero}  = Vec.[]
zeros {suc n} = sp (finᶜ zero) (finᶜ zero) Vec.∷ zeros

oneS : ∀ {n} → Fin n → Spent → Uses n
oneS fzero     s = s Vec.∷ zeros
oneS (fsuc i)  s = sp (finᶜ zero) (finᶜ zero) Vec.∷ oneS i s

charge : Mode → Spent
charge run  = sp (finᶜ (suc zero)) (finᶜ zero)
charge evid = sp (finᶜ (suc zero)) (finᶜ zero)
charge spec = sp (finᶜ zero) (finᶜ (suc zero))

addᶜ : Count → Count → Count
addᶜ (finᶜ m) (finᶜ n) = finᶜ (m + n)
addᶜ many     _        = many
addᶜ _        many     = many

addS : Spent → Spent → Spent
addS (sp c1 t1) (sp c2 t2) = sp (addᶜ c1 c2) (addᶜ t1 t2)

addU : ∀ {n} → Uses n → Uses n → Uses n
addU Vec.[]         Vec.[]         = Vec.[]
addU (x Vec.∷ xs)   (y Vec.∷ ys)   = addS x y Vec.∷ addU xs ys

maxᶜ : Count → Count → Count
maxᶜ many     _        = many
maxᶜ _        many     = many
maxᶜ (finᶜ m) (finᶜ n) = finᶜ (m ⊔ n)

maxS : Spent → Spent → Spent
maxS (sp c1 t1) (sp c2 t2) = sp (maxᶜ c1 c2) (maxᶜ t1 t2)

maxU : ∀ {n} → Uses n → Uses n → Uses n
maxU Vec.[]         Vec.[]         = Vec.[]
maxU (x Vec.∷ xs)   (y Vec.∷ ys)   = maxS x y Vec.∷ maxU xs ys

-- Run and evidence check both grades. Spec forgets the computational one.
hold : Mode → Grade → Grade → Spent → Result ⊤
hold spec _ t (sp _ ty)  = checkType t ty
hold m    c t (sp co ty) = checkCount m c co >> checkType t ty

under : ∀ {n} → Mode → Grade → Grade → Uses (suc n) → Result (Uses n)
under m c t (s Vec.∷ rest) = hold m c t s >> ok rest

-- The predecessor of a variable inherits that variable's grade.
-- Any other scrutinee binds an affine predecessor whose type grade is ω.
predPair : ∀ {n} → GCtx n → GTm n → Pair
predPair Γ (gvar x) = Vec.lookup Γ x
predPair _ _        = gp aff gω

pcomp : Pair → Grade
pcomp (gp c _) = c

ptype : Pair → Grade
ptype (gp _ t) = t

decide : ∀ {n} → Mode → GCtx n → GTm n → Result (Uses n)
decide m _ (gvar x) = ok (oneS x (charge m))
decide _ _ (gtyp x) = ok (oneS x (sp (finᶜ zero) (finᶜ (suc zero))))
decide m Γ (glam c t body) =
  decide m (gp c t Vec.∷ Γ) body >>= λ us →
  under m c t us
decide _ Γ (gpi c t body) =
  decide spec (gp c t Vec.∷ Γ) body >>= λ us →
  under spec c t us
decide m Γ (gapp f a) =
  decide m Γ f >>= λ fu →
  decide m Γ a >>= λ au →
  ok (addU fu au)
decide _ _ gze = ok zeros
decide m Γ (gsu e) = decide m Γ e
decide m Γ (gmatch e z s) =
  decide m Γ e >>= λ eu →
  decide m Γ z >>= λ zu →
  let p = predPair Γ e in
  decide m (p Vec.∷ Γ) s >>= λ su →
  under m (pcomp p) (ptype p) su >>= λ srest →
  ok (addU eu (maxU zu srest))

-- Exactly once.
grade-once : decide run Vec.[] (glam g1 g0 (gvar fzero)) ≡ ok Vec.[]
grade-once = refl

-- ω accepts two uses.
grade-twice : decide run Vec.[] (glam gω g0 (gapp (gvar fzero) (gvar fzero))) ≡ ok Vec.[]
grade-twice = refl

-- The affine interval may drop the binder.
grade-affine-drop : decide run Vec.[] (glam aff g0 gze) ≡ ok Vec.[]
grade-affine-drop = refl

-- Grade 1 may not.
grade-linear-drop : decide run Vec.[] (glam g1 g0 gze) ≡ fail "linear variable unused"
grade-linear-drop = refl

-- The computational grade is checked first. A type-grade failure is
-- reported only when that check accepts.
grade-type : decide run Vec.[] (glam g1 g1 (gvar fzero)) ≡ fail "type grade 1 does not allow 0 uses"
grade-type = refl

grade-erased-first : decide run Vec.[] (glam g0 g1 (gvar fzero)) ≡ fail "erased variable used computationally"
grade-erased-first = refl

-- A type occurrence of a variable whose type grade is 0.
grade-type-used : decide run Vec.[] (glam g0 g0 (gtyp fzero)) ≡ fail "type grade 0 does not allow 1 uses"
grade-type-used = refl

-- A Π is a type, so spec forgets the computational obligation.
grade-pi-forget : decide run Vec.[] (gpi g1 g0 gze) ≡ ok Vec.[]
grade-pi-forget = refl

-- Spec forgets a drop of grade 1.
grade-spec-drop : decide spec Vec.[] (glam g1 g0 gze) ≡ ok Vec.[]
grade-spec-drop = refl

-- The predecessor is the scrutinee's grade, and it is used once.
grade-match-once :
  decide run Vec.[] (glam g1 g0 (gmatch (gvar fzero) gze (gvar fzero))) ≡ ok Vec.[]
grade-match-once = refl

-- An unused predecessor of grade 1 is refused.
grade-match-drop :
  decide run Vec.[] (glam g1 g0 (gmatch (gvar fzero) gze gze)) ≡ fail "linear variable unused"
grade-match-drop = refl

-- ω on the scrutinee lets the predecessor be used twice.
grade-match-many :
  decide run Vec.[] (glam gω g0 (gmatch (gvar fzero) gze (gapp (gvar fzero) (gvar fzero)))) ≡ ok Vec.[]
grade-match-many = refl

-- Two uses sit outside [0, 1].
grade-aff-twice :
  decide run Vec.[] (glam aff g0 (gapp (gvar fzero) (gvar fzero)))
    ≡ fail "grade [0, 1] does not allow 2 uses"
grade-aff-twice = refl

------------------------------------------------------------------------
-- Evidence that unsigned checked arithmetic agrees with Nat.
--
-- `wlink` is one evidence form, not a new term constructor and not
-- twenty-seven kernel constants. `decide` accepts only the value
-- equation and both directions of the fit equation for addc, subc,
-- and mulc at U8, U32, and U64. Each `Link` constructor is that
-- surface statement. The `link-*` theorems are the ℕ facts, taken
-- from Muro.Word. Nothing here executes the schema at 2^64, and
-- nothing here is a denotational interpreter.
--
-- I64 is refused. toNat of −1 is 2^64−1, so the Nat equation is false.
-- A wrapping addi, subi, or muli is not a checked operation.
-- plus, minus, times, and Le are accepted only as the standard
-- definitions: plus from the prelude, minus and Le from le.muro, and
-- times from word.muro. The mode, the type, and the body are compared.
-- times calls plus, so times is standard only when that plus is too.
-- A different binding is refused. Both checkers read the body.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module Muro.WordLink where

open import Data.Bool.Base using (Bool; true; false; T; not; if_then_else_; _∧_; _∨_)
open import Data.Fin.Base using (Fin) renaming (zero to fz; suc to fs)
open import Data.Fin.Properties using () renaming (_≟_ to _≟F_)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _∸_; _<ᵇ_; _≤ᵇ_; _<_; _≤_)
open import Data.Nat.Properties using (_≟_; <ᵇ⇒<; <⇒<ᵇ; ≤ᵇ⇒≤; ≤⇒≤ᵇ)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Data.String.Base using (String; _++_)
open import Data.String.Properties using () renaming (_≟_ to _≟S_; _==_ to _==S_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import Muro.Base
  using (Mode; run; spec; eqMode; Result; ok; fail; _>>=_; Qty; affine; reuse; erased)
open import Muro.Syntax
open import Muro.Env using (Sig; Def; mkDef; lookupDef; fromDefs)
open import Muro.Word
  using ( modulus; _%w_
        ; addPayload; subPayload; mulPayload
        ; fitsAdd; fitsSub; fitsMul
        ; checkedAddN; checkedSubN; checkedMulN
        ; checkedAdd-val; checkedSub-val; checkedMul-val
        ; numeral; ℕ←; wlitT)

------------------------------------------------------------------------
-- Unsigned widths. I64 is not a case.
------------------------------------------------------------------------

data Unsigned : WKind → Set where
  is-u8  : Unsigned ku8
  is-u32 : Unsigned ku32
  is-u64 : Unsigned ku64

data Wdt : Set where
  dt8 dt32 dt64 : Wdt

wdtK : Wdt → WKind
wdtK dt8  = ku8
wdtK dt32 = ku32
wdtK dt64 = ku64

------------------------------------------------------------------------
-- The ℕ facts. Case on the width so the Word.agda clauses unfold.
-- A rewrite at an abstract kind would not, because the ki64 clause
-- is still open.
------------------------------------------------------------------------

payload-add : ∀ {k} → Unsigned k → ∀ x y →
  addPayload k x y ≡ (x %w k) + (y %w k)
payload-add is-u8  _ _ = refl
payload-add is-u32 _ _ = refl
payload-add is-u64 _ _ = refl

payload-sub : ∀ {k} → Unsigned k → ∀ x y →
  subPayload k x y ≡ (x %w k) ∸ (y %w k)
payload-sub is-u8  _ _ = refl
payload-sub is-u32 _ _ = refl
payload-sub is-u64 _ _ = refl

payload-mul : ∀ {k} → Unsigned k → ∀ x y →
  mulPayload k x y ≡ (x %w k) * (y %w k)
payload-mul is-u8  _ _ = refl
payload-mul is-u32 _ _ = refl
payload-mul is-u64 _ _ = refl

fits-add-sum : ∀ {k} → Unsigned k → ∀ x y →
  fitsAdd k x y ≡ ((x %w k) + (y %w k) <ᵇ modulus k)
fits-add-sum is-u8  _ _ = refl
fits-add-sum is-u32 _ _ = refl
fits-add-sum is-u64 _ _ = refl

fits-sub-le : ∀ {k} → Unsigned k → ∀ x y →
  fitsSub k x y ≡ ((y %w k) ≤ᵇ (x %w k))
fits-sub-le is-u8  _ _ = refl
fits-sub-le is-u32 _ _ = refl
fits-sub-le is-u64 _ _ = refl

fits-mul-sum : ∀ {k} → Unsigned k → ∀ x y →
  fitsMul k x y ≡ ((x %w k) * (y %w k) <ᵇ modulus k)
fits-mul-sum is-u8  _ _ = refl
fits-mul-sum is-u32 _ _ = refl
fits-mul-sum is-u64 _ _ = refl

true-of : ∀ {b} → T b → b ≡ true
true-of {true}  tt = refl
true-of {false} ()

if-just-true : ∀ {A : Set} {b : Bool} {v : A} →
  b ≡ true → (if b then just v else nothing) ≡ just v
if-just-true refl = refl

add-fit-if : ∀ sum md r →
  (if sum <ᵇ md then just sum else nothing) ≡ just r → sum < md
add-fit-if sum md r eq with sum <ᵇ md in p
add-fit-if sum md _ _ | true  = <ᵇ⇒< sum md (subst T (sym p) tt)
add-fit-if _   _  _ () | false

sub-fit-if : ∀ yx xx r →
  (if yx ≤ᵇ xx then just (xx ∸ yx) else nothing) ≡ just r → yx ≤ xx
sub-fit-if yx xx r eq with yx ≤ᵇ xx in p
sub-fit-if yx xx _ _ | true  = ≤ᵇ⇒≤ yx xx (subst T (sym p) tt)
sub-fit-if _  _  _ () | false

mul-fit-if : ∀ pr md r →
  (if pr <ᵇ md then just pr else nothing) ≡ just r → pr < md
mul-fit-if pr md r eq with pr <ᵇ md in p
mul-fit-if pr md _ _ | true  = <ᵇ⇒< pr md (subst T (sym p) tt)
mul-fit-if _  _  _ () | false

link-add-val : ∀ {k} (u : Unsigned k) x y r →
  checkedAddN k x y ≡ just r → r ≡ (x %w k) + (y %w k)
link-add-val {k} u x y r eq = trans (checkedAdd-val k x y r eq) (payload-add u x y)

link-sub-val : ∀ {k} (u : Unsigned k) x y r →
  checkedSubN k x y ≡ just r → r ≡ (x %w k) ∸ (y %w k)
link-sub-val {k} u x y r eq = trans (checkedSub-val k x y r eq) (payload-sub u x y)

link-mul-val : ∀ {k} (u : Unsigned k) x y r →
  checkedMulN k x y ≡ just r → r ≡ (x %w k) * (y %w k)
link-mul-val {k} u x y r eq = trans (checkedMul-val k x y r eq) (payload-mul u x y)

link-add-fit : ∀ {k} (u : Unsigned k) x y r →
  checkedAddN k x y ≡ just r → (x %w k) + (y %w k) < modulus k
link-add-fit {k} u x y r eq rewrite payload-add u x y | fits-add-sum u x y =
  add-fit-if ((x %w k) + (y %w k)) (modulus k) r eq

link-sub-fit : ∀ {k} (u : Unsigned k) x y r →
  checkedSubN k x y ≡ just r → (y %w k) ≤ (x %w k)
link-sub-fit {k} u x y r eq rewrite payload-sub u x y | fits-sub-le u x y =
  sub-fit-if (y %w k) (x %w k) r eq

link-mul-fit : ∀ {k} (u : Unsigned k) x y r →
  checkedMulN k x y ≡ just r → (x %w k) * (y %w k) < modulus k
link-mul-fit {k} u x y r eq rewrite payload-mul u x y | fits-mul-sum u x y =
  mul-fit-if ((x %w k) * (y %w k)) (modulus k) r eq

link-add-some : ∀ {k} (u : Unsigned k) x y →
  (x %w k) + (y %w k) < modulus k →
  checkedAddN k x y ≡ just ((x %w k) + (y %w k))
link-add-some {k} u x y lt rewrite payload-add u x y | fits-add-sum u x y =
  if-just-true (true-of (<⇒<ᵇ lt))

link-sub-some : ∀ {k} (u : Unsigned k) x y →
  (y %w k) ≤ (x %w k) →
  checkedSubN k x y ≡ just ((x %w k) ∸ (y %w k))
link-sub-some {k} u x y le rewrite payload-sub u x y | fits-sub-le u x y =
  if-just-true (true-of (≤⇒≤ᵇ le))

link-mul-some : ∀ {k} (u : Unsigned k) x y →
  (x %w k) * (y %w k) < modulus k →
  checkedMulN k x y ≡ just ((x %w k) * (y %w k))
link-mul-some {k} u x y lt rewrite payload-mul u x y | fits-mul-sum u x y =
  if-just-true (true-of (<⇒<ᵇ lt))

------------------------------------------------------------------------
-- Messages. The Elixir checker uses these strings.
------------------------------------------------------------------------

unsignedMsg : String
unsignedMsg = "word-to-Nat lemmas are unsigned"

wrapMsg : String
wrapMsg = "wlink expected a checked unsigned operation"

widthMsg : String
widthMsg = "wlink width does not match"

opMsg : String
opMsg = "wlink operation does not match"

shapeMsg : String
shapeMsg = "wlink does not prove this type"

stdMsg : String → String
stdMsg s = "wlink expected the standard definition of " ++ s

isStd : String → Bool
isStd s =
  (s ==S stdMsg "plus") ∨ (s ==S stdMsg "minus") ∨
  (s ==S stdMsg "times") ∨ (s ==S stdMsg "Le")

rank : String → ℕ
rank s = if isStd s then 3 else if s ==S widthMsg then 2 else if s ==S opMsg then 1 else 0

best : ∀ {A : Set} → Result A → Result A → Result A
best (ok x)    _        = ok x
best (fail _)  (ok y)   = ok y
best (fail e1) (fail e2) = fail (if rank e1 <ᵇ rank e2 then e2 else e1)

------------------------------------------------------------------------
-- Surface shapes. Both spellings of Opt Uk are accepted.
-- The modulus is the closed numeral, recognised by its value.
------------------------------------------------------------------------

data Side : Set where
  side-add side-sub side-mul : Side

sideOp : Side → WOp
sideOp side-add = wcadd
sideOp side-sub = wcsub
sideOp side-mul = wcmul

sideName : Side → String
sideName side-add = "plus"
sideName side-sub = "minus"
sideName side-mul = "times"

data FitAdd : Side → Set where
  fit-add : FitAdd side-add
  fit-mul : FitAdd side-mul

data IsOpt {n} : Wdt → Tm n → Set where
  opt-k : (w : Wdt) → IsOpt w (word (woptk (wdtK w)) [])
  opt-w : (w : Wdt) → IsOpt w (word wopt (word (wty (wdtK w)) [] ∷ []))

asOpt : ∀ {n} (t : Tm n) → Maybe (Σ Wdt (λ w → IsOpt w t))
asOpt (word (woptk ku8) [])                    = just (dt8  , opt-k dt8)
asOpt (word (woptk ku32) [])                   = just (dt32 , opt-k dt32)
asOpt (word (woptk ku64) [])                   = just (dt64 , opt-k dt64)
asOpt (word wopt (word (wty ku8) [] ∷ []))     = just (dt8  , opt-w dt8)
asOpt (word wopt (word (wty ku32) [] ∷ []))    = just (dt32 , opt-w dt32)
asOpt (word wopt (word (wty ku64) [] ∷ []))    = just (dt64 , opt-w dt64)
asOpt _                                        = nothing

signedOpt? : ∀ {n} → Tm n → Bool
signedOpt? (word (woptk ki64) [])                 = true
signedOpt? (word wopt (i64 ∷ []))                 = true
signedOpt? (word wopt (word (wty ki64) [] ∷ []))  = true
signedOpt? _                                      = false

isWrap : ∀ {n} → Tm n → Bool
isWrap (word wadd _) = true
isWrap (word wsub _) = true
isWrap (word wmul _) = true
isWrap _             = false

data AsChk {n} (t : Tm n) : Set where
  as-chk : (s : Side) (a b : Tm n) →
    t ≡ word (sideOp s) (a ∷ b ∷ []) → AsChk t

asChk : ∀ {n} (t : Tm n) → Maybe (AsChk t)
asChk (word wcadd (a ∷ b ∷ [])) = just (as-chk side-add a b refl)
asChk (word wcsub (a ∷ b ∷ [])) = just (as-chk side-sub a b refl)
asChk (word wcmul (a ∷ b ∷ [])) = just (as-chk side-mul a b refl)
asChk _                         = nothing

data AsSome {n} (t : Tm n) : Set where
  as-some : (c : Tm n) → t ≡ word wsome (c ∷ []) → AsSome t

asSome : ∀ {n} (t : Tm n) → Maybe (AsSome t)
asSome (word wsome (c ∷ [])) = just (as-some c refl)
asSome _                     = nothing

data AsId {n} (t : Tm n) : Set where
  as-id : (A a b : Tm n) → t ≡ idt A a b → AsId t

asId : ∀ {n} (t : Tm n) → Maybe (AsId t)
asId (idt A a b) = just (as-id A a b refl)
asId _           = nothing

data AsBin {n} (t : Tm n) : Set where
  as-bin : (i : ℕ) (x y : Tm n) → t ≡ app (app (def i) x) y → AsBin t

asBin : ∀ {n} (t : Tm n) → Maybe (AsBin t)
asBin (app (app (def i) x) y) = just (as-bin i x y refl)
asBin _                       = nothing

data AsTon {n} (t : Tm n) : Set where
  as-ton : (x : Tm n) → t ≡ word wton (x ∷ []) → AsTon t

asTon : ∀ {n} (t : Tm n) → Maybe (AsTon t)
asTon (word wton (x ∷ [])) = just (as-ton x refl)
asTon _                    = nothing

data AsSu {n} (t : Tm n) : Set where
  as-su : (x : Tm n) → t ≡ su x → AsSu t

asSu : ∀ {n} (t : Tm n) → Maybe (AsSu t)
asSu (su x) = just (as-su x refl)
asSu _      = nothing

data OfView {n} (t : Tm n) : Set where
  of-u   : (w : Wdt) (x : Tm n) → t ≡ word (wof (wdtK w)) (x ∷ []) → OfView t
  of-i64 : (x : Tm n) → t ≡ word (wof ki64) (x ∷ []) → OfView t

ofView : ∀ {n} (t : Tm n) → Maybe (OfView t)
ofView (word (wof ku8)  (x ∷ [])) = just (of-u dt8 x refl)
ofView (word (wof ku32) (x ∷ [])) = just (of-u dt32 x refl)
ofView (word (wof ku64) (x ∷ [])) = just (of-u dt64 x refl)
ofView (word (wof ki64) (x ∷ [])) = just (of-i64 x refl)
ofView _                          = nothing

data WdtEq : Wdt → Wdt → Set where
  weq : ∀ {w} → WdtEq w w

wdtEq? : (w w′ : Wdt) → Maybe (WdtEq w w′)
wdtEq? dt8  dt8  = just weq
wdtEq? dt32 dt32 = just weq
wdtEq? dt64 dt64 = just weq
wdtEq? _    _    = nothing

chk : ∀ {n} → Side → Tm n → Tm n → Tm n
chk s a b = word (sideOp s) (a ∷ b ∷ [])

someT : ∀ {n} → Tm n → Tm n
someT c = word wsome (c ∷ [])

ton : ∀ {n} → Tm n → Tm n
ton x = word wton (x ∷ [])

bin : ∀ {n} → ℕ → Tm n → Tm n → Tm n
bin i x y = app (app (def i) x) y

ofT : ∀ {n} → Wdt → Tm n → Tm n
ofT w x = word (wof (wdtK w)) (x ∷ [])

------------------------------------------------------------------------
-- Structural equality. The proof is cong, never a match on refl
-- of a computed proof. Views above may match refl: they build it.
------------------------------------------------------------------------

infixl 1 _>>=ᵐ_
infixl 4 _<$>ᵐ_ _<*>ᵐ_

_>>=ᵐ_ : ∀ {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just x  >>=ᵐ f = f x
nothing >>=ᵐ _ = nothing

_<$>ᵐ_ : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
f <$>ᵐ just x  = just (f x)
_ <$>ᵐ nothing = nothing

_<*>ᵐ_ : ∀ {A B : Set} → Maybe (A → B) → Maybe A → Maybe B
just f  <*>ᵐ just x  = just (f x)
_       <*>ᵐ _       = nothing

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a′ b b′ c c′} →
  a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ _ refl refl refl = refl

cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E) {a a′ b b′ c c′ d d′} →
  a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → f a b c d ≡ f a′ b′ c′ d′
cong₄ _ refl refl refl refl = refl

nsame : (m n : ℕ) → Maybe (m ≡ n)
nsame m n with m ≟ n
... | yes p = just p
... | no _  = nothing

fsame : ∀ {n} (i j : Fin n) → Maybe (i ≡ j)
fsame i j with i ≟F j
... | yes p = just p
... | no _  = nothing

qsame : (q q′ : Qty) → Maybe (q ≡ q′)
qsame affine affine = just refl
qsame reuse  reuse  = just refl
qsame erased erased = just refl
qsame _      _      = nothing

ksame : (k k′ : WKind) → Maybe (k ≡ k′)
ksame ku8  ku8  = just refl
ksame ku32 ku32 = just refl
ksame ku64 ku64 = just refl
ksame ki64 ki64 = just refl
ksame _    _    = nothing

wsame : (op op′ : WOp) → Maybe (op ≡ op′)
wsame (wty k)    (wty k′)     = cong wty <$>ᵐ ksame k k′
wsame (wlit k n) (wlit k′ n′) = cong₂ wlit <$>ᵐ ksame k k′ <*>ᵐ nsame n n′
wsame (wof k)    (wof k′)     = cong wof <$>ᵐ ksame k k′
wsame wton       wton         = just refl
wsame wadd       wadd         = just refl
wsame wsub       wsub         = just refl
wsame wmul       wmul         = just refl
wsame wcadd      wcadd        = just refl
wsame wcsub      wcsub        = just refl
wsame wcmul      wcmul        = just refl
wsame wdiv       wdiv         = just refl
wsame wrem       wrem         = just refl
wsame weq        weq          = just refl
wsame wlt        wlt          = just refl
wsame wle        wle          = just refl
wsame wand       wand         = just refl
wsame wor        wor          = just refl
wsame wxor       wxor         = just refl
wsame wnot       wnot         = just refl
wsame wshl       wshl         = just refl
wsame wshr       wshr         = just refl
wsame (wcast k)  (wcast k′)   = cong wcast <$>ᵐ ksame k k′
wsame wbool      wbool        = just refl
wsame wtrue      wtrue        = just refl
wsame wfalse     wfalse       = just refl
wsame wopt       wopt         = just refl
wsame (woptk k)  (woptk k′)   = cong woptk <$>ᵐ ksame k k′
wsame wsome      wsome        = just refl
wsame wnone      wnone        = just refl
wsame wlink      wlink        = just refl
wsame _          _            = nothing

mutual
  same : ∀ {n} (u v : Tm n) → Maybe (u ≡ v)
  same (var i) (var j) = cong var <$>ᵐ fsame i j
  same typ typ = just refl
  same (pi q a b) (pi q′ a′ b′) =
    cong₃ pi <$>ᵐ qsame q q′ <*>ᵐ same a a′ <*>ᵐ same b b′
  same (lam q a b) (lam q′ a′ b′) =
    cong₃ lam <$>ᵐ qsame q q′ <*>ᵐ same a a′ <*>ᵐ same b b′
  same (app f a) (app f′ a′) = cong₂ app <$>ᵐ same f f′ <*>ᵐ same a a′
  same nat nat = just refl
  same ze ze = just refl
  same (su a) (su b) = cong su <$>ᵐ same a b
  same unit unit = just refl
  same one one = just refl
  same empty empty = just refl
  same (dty i) (dty j) = cong dty <$>ᵐ nsame i j
  same (ctor d c) (ctor d′ c′) = cong₂ ctor <$>ᵐ nsame d d′ <*>ᵐ nsame c c′
  same (mData e p bs) (mData e′ p′ bs′) =
    cong₃ mData <$>ᵐ same e e′ <*>ᵐ same p p′ <*>ᵐ sameL bs bs′
  same (mNat e p z s) (mNat e′ p′ z′ s′) =
    cong₄ mNat <$>ᵐ same e e′ <*>ᵐ same p p′ <*>ᵐ same z z′ <*>ᵐ same s s′
  same (mEmp e p) (mEmp e′ p′) = cong₂ mEmp <$>ᵐ same e e′ <*>ᵐ same p p′
  same (mUnit e p u) (mUnit e′ p′ u′) =
    cong₃ mUnit <$>ᵐ same e e′ <*>ᵐ same p p′ <*>ᵐ same u u′
  same (idt A a b) (idt A′ a′ b′) =
    cong₃ idt <$>ᵐ same A A′ <*>ᵐ same a a′ <*>ᵐ same b b′
  same rfl rfl = just refl
  same (rwt e p b) (rwt e′ p′ b′) =
    cong₃ rwt <$>ᵐ same e e′ <*>ᵐ same p p′ <*>ᵐ same b b′
  same (def i) (def j) = cong def <$>ᵐ nsame i j
  same (ann e a) (ann e′ a′) = cong₂ ann <$>ᵐ same e e′ <*>ᵐ same a a′
  same (prod a b) (prod a′ b′) = cong₂ prod <$>ᵐ same a a′ <*>ᵐ same b b′
  same (pair a b) (pair a′ b′) = cong₂ pair <$>ᵐ same a a′ <*>ᵐ same b b′
  same (letp e t) (letp e′ t′) = cong₂ letp <$>ᵐ same e e′ <*>ᵐ same t t′
  same (nu t) (nu t′) = cong nu <$>ᵐ same t t′
  same (unf a b) (unf a′ b′) = cong₂ unf <$>ᵐ same a a′ <*>ᵐ same b b′
  same (ucons a) (ucons b) = cong ucons <$>ᵐ same a b
  same i64 i64 = just refl
  same f32ty f32ty = just refl
  same (tensor a b) (tensor a′ b′) = cong₂ tensor <$>ᵐ same a a′ <*>ᵐ same b b′
  same (addi a b) (addi a′ b′) = cong₂ addi <$>ᵐ same a a′ <*>ᵐ same b b′
  same (muli a b) (muli a′ b′) = cong₂ muli <$>ᵐ same a a′ <*>ᵐ same b b′
  same (addt a b) (addt a′ b′) = cong₂ addt <$>ᵐ same a a′ <*>ᵐ same b b′
  same (toi64 a) (toi64 b) = cong toi64 <$>ᵐ same a b
  same (packi a b) (packi a′ b′) = cong₂ packi <$>ᵐ same a a′ <*>ᵐ same b b′
  same (word op ts) (word op′ ts′) =
    cong₂ word <$>ᵐ wsame op op′ <*>ᵐ sameL ts ts′
  same _ _ = nothing

  sameL : ∀ {n} (xs ys : List (Tm n)) → Maybe (xs ≡ ys)
  sameL [] [] = just refl
  sameL (x ∷ xs) (y ∷ ys) = cong₂ _∷_ <$>ᵐ same x y <*>ᵐ sameL xs ys
  sameL _ _ = nothing

------------------------------------------------------------------------
-- The standard definitions. plus is the prelude's, minus and Le are
-- le.muro's, and times is word.muro's. A binding is that definition
-- when the mode, the type, and the body are these terms. times calls
-- plus, so it is standard only when that plus is. The innermost
-- variable is var fz. The transcription is the library recursion.
------------------------------------------------------------------------

natOpTy : Tm 0
natOpTy =
  pi affine nat
    (pi affine nat nat)

timesTy : Tm 0
timesTy =
  pi reuse nat
    (pi affine nat nat)

leTy : Tm 0
leTy =
  pi affine nat
    (pi affine nat typ)

plusBody : ℕ → Tm 0
plusBody i =
  lam affine nat
    (lam affine nat
      (mNat (var (fs fz)) nat
        (var fz)
        (su (app (app (def i) (var fz)) (var (fs fz))))))

minusBody : ℕ → Tm 0
minusBody i =
  lam affine nat
    (lam affine nat
      (mNat (var fz) nat
        (var (fs fz))
        (mNat (var (fs (fs fz))) nat
          ze
          (app (app (def i) (var fz)) (var (fs fz))))))

timesBody : ℕ → ℕ → Tm 0
timesBody p i =
  lam reuse nat
    (lam affine nat
      (mNat (var fz) nat
        ze
        (app (app (def p) (var (fs (fs fz))))
             (app (app (def i) (var (fs (fs fz)))) (var fz)))))

leBody : ℕ → Tm 0
leBody i =
  lam affine nat
    (lam affine nat
      (mNat (var (fs fz)) typ
        unit
        (mNat (var (fs fz)) typ
          empty
          (app (app (def i) (var (fs fz))) (var fz)))))

isJust : ∀ {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust nothing  = false

modeIs : Def → Mode → Bool
modeIs d m = eqMode (Def.dmode d) m

tyIs : Def → Tm 0 → Bool
tyIs d t = isJust (same (Def.dtype d) t)

bodyIs : Def → Tm 0 → Bool
bodyIs d t = isJust (same (Def.dbody d) t)

stdPlus : Sig → ℕ → Bool
stdPlus σ i with lookupDef σ i
... | fail _ = false
... | ok d =
  (Def.dname d ==S "plus") ∧ modeIs d run ∧ tyIs d natOpTy ∧ bodyIs d (plusBody i)

stdMinus : Sig → ℕ → Bool
stdMinus σ i with lookupDef σ i
... | fail _ = false
... | ok d =
  (Def.dname d ==S "minus") ∧ modeIs d run ∧ tyIs d natOpTy ∧ bodyIs d (minusBody i)

stdLe : Sig → ℕ → Bool
stdLe σ i with lookupDef σ i
... | fail _ = false
... | ok d =
  (Def.dname d ==S "Le") ∧ modeIs d spec ∧ tyIs d leTy ∧ bodyIs d (leBody i)

range : ℕ → List ℕ
range n = go 0 n
  where
  go : ℕ → ℕ → List ℕ
  go _ zero    = []
  go i (suc k) = i ∷ go (suc i) k

timesAt : Sig → ℕ → Tm 0 → List ℕ → Bool
timesAt _ _ _ [] = false
timesAt σ i body (p ∷ ps) =
  (stdPlus σ p ∧ isJust (same body (timesBody p i))) ∨ timesAt σ i body ps

stdTimes : Sig → ℕ → Bool
stdTimes σ i with lookupDef σ i
... | fail _ = false
... | ok d =
  (Def.dname d ==S "times") ∧ modeIs d run ∧ tyIs d timesTy ∧
  timesAt σ i (Def.dbody d) (range (length (Sig.defs σ)))

std? : Sig → ℕ → String → Bool
std? σ i s =
  if s ==S "plus"  then stdPlus σ i  else
  if s ==S "minus" then stdMinus σ i else
  if s ==S "times" then stdTimes σ i else
  if s ==S "Le"    then stdLe σ i    else
  false

data Named (σ : Sig) (i : ℕ) (s : String) : Set where
  named : (d : Def) → lookupDef σ i ≡ ok d → Def.dname d ≡ s
        → T (std? σ i s) → Named σ i s

nameOf : Sig → ℕ → Maybe String
nameOf σ i with lookupDef σ i
... | ok d   = just (Def.dname d)
... | fail _ = nothing

natOp? : String → Bool
natOp? s = (s ==S "plus") ∨ (s ==S "minus") ∨ (s ==S "times")

expectStd : (σ : Sig) (i : ℕ) (s : String) (d : Def) →
  lookupDef σ i ≡ ok d → Def.dname d ≡ s → Result (Named σ i s)
expectStd σ i s d eq p with std? σ i s in stb
... | true  = ok (named d eq p (subst T (sym stb) tt))
... | false = fail (stdMsg s)

expectName : (σ : Sig) (i : ℕ) (s : String) → Result (Named σ i s)
expectName σ i s with lookupDef σ i in lu
... | fail _ = fail shapeMsg
... | ok d with Def.dname d ≟S s
...   | yes p = expectStd σ i s d lu p
...   | no _ with nameOf σ i
...     | just found = if natOp? found then fail opMsg else fail shapeMsg
...     | nothing    = fail shapeMsg

diffNat : Sig → Side → ℕ → Bool
diffNat σ s i with nameOf σ i
... | just found = natOp? found ∧ not (found ==S sideName s)
... | nothing    = false

opOrShape : ∀ {n} → Sig → Side → Tm n → String
opOrShape σ s t with asBin t
... | just (as-bin i _ _ _) = if diffNat σ s i then opMsg else shapeMsg
... | nothing               = shapeMsg

isMod : ℕ → Wdt → Bool
isMod m w with m ≟ modulus (wdtK w)
... | yes _ = true
... | no _  = false

otherWidth : ℕ → Wdt → Bool
otherWidth m dt8  = isMod m dt32 ∨ isMod m dt64
otherWidth m dt32 = isMod m dt8  ∨ isMod m dt64
otherWidth m dt64 = isMod m dt8  ∨ isMod m dt32

data ModView {n} (w : Wdt) (t : Tm n) : Set where
  mod-here : t ≡ numeral (modulus (wdtK w)) → ModView w t
  mod-else : Bool → ModView w t

mod? : ∀ {n} (w : Wdt) (t : Tm n) → ModView w t
mod? w t with ℕ← t
... | nothing = mod-else false
... | just (m , eq) with m ≟ modulus (wdtK w)
...   | yes p = mod-here (trans eq (cong numeral p))
...   | no _  = mod-else (otherWidth m w)

------------------------------------------------------------------------
-- Link. Five constructors: value, fit, and the bound-to-wsome
-- direction, with subtraction's bound written as Le rather than a
-- successor below the modulus.
------------------------------------------------------------------------

data Link (σ : Sig) {n} : Tm n → Tm n → Set where
  L-val : ∀ {w s i opt a b c}
    → IsOpt w opt
    → Named σ i (sideName s)
    → Link σ (idt opt (chk s a b) (someT c))
             (idt nat (ton c) (bin i (ton a) (ton b)))

  L-fit : ∀ {w s i j opt a b c mod}
    → FitAdd s
    → IsOpt w opt
    → Named σ i (sideName s)
    → Named σ j "Le"
    → mod ≡ numeral (modulus (wdtK w))
    → Link σ (idt opt (chk s a b) (someT c))
             (bin j (su (bin i (ton a) (ton b))) mod)

  L-fit-sub : ∀ {w j opt a b c}
    → IsOpt w opt
    → Named σ j "Le"
    → Link σ (idt opt (chk side-sub a b) (someT c))
             (bin j (ton b) (ton a))

  L-some : ∀ {w s i j opt a b mod}
    → FitAdd s
    → IsOpt w opt
    → Named σ i (sideName s)
    → Named σ j "Le"
    → mod ≡ numeral (modulus (wdtK w))
    → Link σ (bin j (su (bin i (ton a) (ton b))) mod)
             (idt opt (chk s a b) (someT (ofT w (bin i (ton a) (ton b)))))

  L-some-sub : ∀ {w i j opt a b}
    → IsOpt w opt
    → Named σ i "minus"
    → Named σ j "Le"
    → Link σ (bin j (ton b) (ton a))
             (idt opt (chk side-sub a b)
                      (someT (ofT w (bin i (ton a) (ton b)))))

castH : ∀ {σ n} {H H′ G : Tm n} → H ≡ H′ → Link σ H′ G → Link σ H G
castH {G = G} eq l = subst (λ X → Link _ X G) (sym eq) l

castG : ∀ {σ n} {H G G′ : Tm n} → G ≡ G′ → Link σ H G′ → Link σ H G
castG {H = H} eq l = subst (λ X → Link _ H X) (sym eq) l

castHG : ∀ {σ n} {H H′ G G′ : Tm n} →
  H ≡ H′ → G ≡ G′ → Link σ H′ G′ → Link σ H G
castHG eqH eqG l = castH eqH (castG eqG l)


tonEq : ∀ {n} (t x : Tm n) → Maybe (t ≡ ton x)
tonEq t x with asTon t
... | just (as-ton y refl) = cong (λ z → word wton (z ∷ [])) <$>ᵐ same y x
... | nothing              = nothing

binEq : ∀ {n} i {x x′ y y′ : Tm n} → x ≡ x′ → y ≡ y′ → bin i x y ≡ bin i x′ y′
binEq _ refl refl = refl

------------------------------------------------------------------------
-- decide. Match the type as written. Do not whnf: plus would become
-- a match, and Le would become Unit on one checker and not the other.
-- The clauses call each other, so they sit in one mutual block.
------------------------------------------------------------------------

mutual
  tryVal : ∀ {n w s opt a b c}
    (σ : Sig) (optw : IsOpt {n} w opt) (goal : Tm n) →
    Result (Link σ (idt opt (chk s a b) (someT c)) goal)
  tryVal {s = s} {a = a} {b = b} {c = c} σ optw goal with asId goal
  ... | nothing = fail shapeMsg
  ... | just (as-id B gl gr refl) with same B nat
  ...   | nothing = fail shapeMsg
  ...   | just eB with tonEq gl c
  ...     | nothing = fail shapeMsg
  ...     | just eL with asBin gr
  ...       | nothing = fail shapeMsg
  ...       | just (as-bin i x y refl) with tonEq x a
  ...         | nothing = fail shapeMsg
  ...         | just eX with tonEq y b
  ...           | nothing = fail shapeMsg
  ...           | just eY =
                  expectName σ i (sideName s) >>= λ nm →
                  ok (castG (cong₃ idt eB eL (binEq i eX eY)) (L-val optw nm))

  tryFitSub : ∀ {n w opt a b c}
    (σ : Sig) (optw : IsOpt {n} w opt) (goal : Tm n) →
    Result (Link σ (idt opt (chk side-sub a b) (someT c)) goal)
  tryFitSub σ optw goal with asBin goal
  ... | nothing = fail shapeMsg
  ... | just (as-bin j x y refl) =
        expectName σ j "Le" >>= λ nmJ →
        fitSubNm σ optw nmJ x y

  fitSubNm : ∀ {n w j opt a b c}
    (σ : Sig) (optw : IsOpt {n} w opt) (nmJ : Named σ j "Le") →
    (x y : Tm n) →
    Result (Link σ (idt opt (chk side-sub a b) (someT c)) (bin j x y))
  fitSubNm {a = a} {b = b} σ optw nmJ x y with tonEq x b
  ... | nothing = fail shapeMsg
  ... | just eX with tonEq y a
  ...   | nothing = fail shapeMsg
  ...   | just eY = ok (castG (binEq _ eX eY) (L-fit-sub optw nmJ))

  tryFitAdd : ∀ {n w s opt a b c}
    (fit : FitAdd s) (σ : Sig) (optw : IsOpt {n} w opt) (goal : Tm n) →
    Result (Link σ (idt opt (chk s a b) (someT c)) goal)
  tryFitAdd fit σ optw goal with asBin goal
  ... | nothing = fail shapeMsg
  ... | just (as-bin j arg mod refl) =
        expectName σ j "Le" >>= λ nmJ →
        fitAddLe fit σ optw nmJ arg mod

  fitAddLe : ∀ {n w s j opt a b c}
    (fit : FitAdd s) (σ : Sig) (optw : IsOpt {n} w opt) (nmJ : Named σ j "Le") →
    (arg mod : Tm n) →
    Result (Link σ (idt opt (chk s a b) (someT c)) (bin j arg mod))
  fitAddLe {s = s} {a = a} {b = b} fit σ optw nmJ arg mod with asSu arg
  ... | nothing = fail shapeMsg
  ... | just (as-su body refl) with asBin body
  ...   | nothing = fail shapeMsg
  ...   | just (as-bin i x y refl) with tonEq x a
  ...     | nothing = fail shapeMsg
  ...     | just eX with tonEq y b
  ...       | nothing = fail shapeMsg
  ...       | just eY =
              expectName σ i (sideName s) >>= λ nmI →
              fitAddMod fit σ optw nmI nmJ (binEq i eX eY) mod

  fitAddMod : ∀ {n w s i j opt a b c body}
    (fit : FitAdd s) (σ : Sig) (optw : IsOpt {n} w opt)
    (nmI : Named σ i (sideName s)) (nmJ : Named σ j "Le") →
    body ≡ bin i (ton a) (ton b) → (mod : Tm n) →
    Result (Link σ (idt opt (chk s a b) (someT c))
                   (bin j (su body) mod))
  fitAddMod {w = w} {i = i} {a = a} {b = b} fit σ optw nmI nmJ eBody mod with mod? w mod
  ... | mod-here eMod =
        ok (castG (cong (λ z → bin _ (su z) mod) eBody)
                  (L-fit fit optw nmI nmJ eMod))
  ... | mod-else true  = fail widthMsg
  ... | mod-else false = fail shapeMsg

  tryFit : ∀ {n w s opt a b c}
    (σ : Sig) (optw : IsOpt {n} w opt) (goal : Tm n) →
    Result (Link σ (idt opt (chk s a b) (someT c)) goal)
  tryFit {s = s} {opt = opt} {a = a} {b = b} {c = c} σ optw goal = go s
    where
    go : (s′ : Side) → Result (Link σ (idt opt (chk s′ a b) (someT c)) goal)
    go side-sub = tryFitSub σ optw goal
    go side-add = tryFitAdd fit-add σ optw goal
    go side-mul = tryFitAdd fit-mul σ optw goal

  fromHyp : ∀ {n} (σ : Sig) (A lhs rhs goal : Tm n) →
    Result (Link σ (idt A lhs rhs) goal)
  fromHyp σ A lhs rhs goal with isWrap lhs
  ... | true  = fail wrapMsg
  ... | false with signedOpt? A
  ...   | true  = fail unsignedMsg
  ...   | false with asChk lhs
  ...     | nothing = fail shapeMsg
  ...     | just (as-chk s a b eqL) with asOpt A
  ...       | nothing = fail shapeMsg
  ...       | just (w , optw) with asSome rhs
  ...         | nothing = fail shapeMsg
  ...         | just (as-some c eqR) =
                best (tryVal σ optw goal) (tryFit σ optw goal) >>= λ l →
                ok (castH (cong₃ idt refl eqL eqR) l)

  -- Bound → wsome. The payload is toUk of the Nat operation.
  -- A toI64 payload is unsigned. A toUk of another width is width,
  -- before the hypothesis is read.

  boundAdd : ∀ {n w s i j opt a b body} (σ : Sig)
    (fit : FitAdd s) (optw : IsOpt {n} w opt)
    (nmI : Named σ i (sideName s)) (nmJ : Named σ j "Le") →
    body ≡ bin i (ton a) (ton b) → (mod : Tm n) →
    Result (Link σ (bin j (su body) mod)
                   (idt opt (chk s a b) (someT (ofT w (bin i (ton a) (ton b))))))
  boundAdd {i = i} {j = j} σ fit (opt-k w) nmI nmJ eBody mod with mod? w mod
  ... | mod-here eMod =
        ok (castH (cong (λ z → bin j (su z) mod) eBody)
                  (L-some fit (opt-k w) nmI nmJ eMod))
  ... | mod-else true  = fail widthMsg
  ... | mod-else false = fail shapeMsg
  boundAdd {i = i} {j = j} σ fit (opt-w w) nmI nmJ eBody mod with mod? w mod
  ... | mod-here eMod =
        ok (castH (cong (λ z → bin j (su z) mod) eBody)
                  (L-some fit (opt-w w) nmI nmJ eMod))
  ... | mod-else true  = fail widthMsg
  ... | mod-else false = fail shapeMsg

  onBoundAdd : ∀ {n w s i opt a b}
    (fit : FitAdd s) (σ : Sig) (optw : IsOpt {n} w opt)
    (nmI : Named σ i (sideName s)) (hyp : Tm n) →
    Result (Link σ hyp (idt opt (chk s a b) (someT (ofT w (bin i (ton a) (ton b))))))
  onBoundAdd fit σ optw nmI hyp with asBin hyp
  ... | nothing = fail shapeMsg
  ... | just (as-bin j arg mod refl) =
        expectName σ j "Le" >>= λ nmJ →
        onBoundLe fit σ optw nmI nmJ arg mod

  onBoundLe : ∀ {n w s i j opt a b}
    (fit : FitAdd s) (σ : Sig) (optw : IsOpt {n} w opt)
    (nmI : Named σ i (sideName s)) (nmJ : Named σ j "Le") →
    (arg mod : Tm n) →
    Result (Link σ (bin j arg mod)
                   (idt opt (chk s a b) (someT (ofT w (bin i (ton a) (ton b))))))
  onBoundLe {s = s} {i = i} {a = a} {b = b} fit σ optw nmI nmJ arg mod with asSu arg
  ... | nothing = fail shapeMsg
  ... | just (as-su body refl) with same body (bin i (ton a) (ton b))
  ...   | nothing = fail (opOrShape σ s body)
  ...   | just eBody = boundAdd σ fit optw nmI nmJ eBody mod

  onBoundSub : ∀ {n w i opt a b}
    (σ : Sig) (optw : IsOpt {n} w opt) (nmI : Named σ i "minus") (hyp : Tm n) →
    Result (Link σ hyp
               (idt opt (chk side-sub a b) (someT (ofT w (bin i (ton a) (ton b))))))
  onBoundSub {a = a} {b = b} σ optw nmI hyp with asBin hyp
  ... | nothing = fail shapeMsg
  ... | just (as-bin j x y refl) =
        expectName σ j "Le" >>= λ nmJ →
        subLe σ a b optw nmI nmJ x y

  subLe : ∀ {n w i j opt} (σ : Sig) (a b : Tm n)
    (optw : IsOpt {n} w opt) (nmI : Named σ i "minus") (nmJ : Named σ j "Le") →
    (x y : Tm n) →
    Result (Link σ (bin j x y)
               (idt opt (chk side-sub a b) (someT (ofT w (bin i (ton a) (ton b))))))
  subLe {w = w} {i = i} {j = j} {opt = opt} σ a b optw nmI nmJ x y =
    answer (tonEq x b) (tonEq y a)
    where
    answer : Maybe (x ≡ ton b) → Maybe (y ≡ ton a) →
             Result (Link σ (bin j x y)
                        (idt opt (chk side-sub a b)
                               (someT (ofT w (bin i (ton a) (ton b))))))
    answer (just eX) (just eY) = ok (castH (binEq j eX eY) (L-some-sub optw nmI nmJ))
    answer _         _         = fail shapeMsg

  payloadOf : ∀ {n w s opt a b}
    (σ : Sig) (optw : IsOpt {n} w opt) (nPay : Tm n) (hyp : Tm n) →
    Result (Link σ hyp (idt opt (chk s a b) (someT (ofT w nPay))))
  payloadOf {s = s} {a = a} {b = b} σ optw nPay hyp with asBin nPay
  ... | nothing = fail shapeMsg
  ... | just (as-bin i x y refl) with tonEq x a
  ...   | nothing = fail shapeMsg
  ...   | just eX with tonEq y b
  ...     | nothing = fail shapeMsg
  ...     | just eY =
            expectName σ i (sideName s) >>= λ nmI →
            paySide σ optw nmI (binEq i eX eY) hyp

  paySide : ∀ {n w s i opt a b pay}
    (σ : Sig) (optw : IsOpt {n} w opt) (nmI : Named σ i (sideName s)) →
    pay ≡ bin i (ton a) (ton b) → (hyp : Tm n) →
    Result (Link σ hyp (idt opt (chk s a b) (someT (ofT w pay))))
  paySide {w = w} {s = s} {i = i} {opt = opt} {a = a} {b = b} {pay = pay}
    σ optw nmI ePay hyp = go s nmI
    where
    castPay : ∀ {s′} →
      pay ≡ bin i (ton a) (ton b) →
      Result (Link σ hyp (idt opt (chk s′ a b) (someT (ofT w (bin i (ton a) (ton b)))))) →
      Result (Link σ hyp (idt opt (chk s′ a b) (someT (ofT w pay))))
    castPay eq r =
      subst (λ z → Result (Link σ hyp (idt opt (chk _ a b) (someT (ofT w z)))))
            (sym eq) r

    go : (s′ : Side) (nm : Named σ i (sideName s′)) →
         Result (Link σ hyp (idt opt (chk s′ a b) (someT (ofT w pay))))
    go side-add nm = castPay ePay (onBoundAdd fit-add σ optw nm hyp)
    go side-mul nm = castPay ePay (onBoundAdd fit-mul σ optw nm hyp)
    go side-sub nm = castPay ePay (onBoundSub σ optw nm hyp)

  fromOf : ∀ {n} (σ : Sig) (w : Wdt) {opt a b s}
    (optw : IsOpt w opt) (pay hyp : Tm n) →
    Result (Link σ hyp (idt opt (chk s a b) (someT pay)))
  fromOf σ w optw pay hyp with ofView pay
  ... | nothing = fail shapeMsg
  ... | just (of-i64 _ _) = fail unsignedMsg
  ... | just (of-u w′ nPay refl) with wdtEq? w w′
  ...   | nothing = fail widthMsg
  ...   | just weq = payloadOf σ optw nPay hyp

  fromBound : ∀ {n} (σ : Sig) (hyp goal : Tm n) → Result (Link σ hyp goal)
  fromBound σ hyp goal with asId goal
  ... | nothing = fail shapeMsg
  ... | just (as-id opt lhs rhs refl) with isWrap lhs
  ...   | true = fail wrapMsg
  ...   | false with signedOpt? opt
  ...     | true = fail unsignedMsg
  ...     | false with asChk lhs
  ...       | nothing = fail shapeMsg
  ...       | just (as-chk s a b eqL) with asOpt opt
  ...         | nothing = fail shapeMsg
  ...         | just (w , optw) with asSome rhs
  ...           | nothing = fail shapeMsg
  ...           | just (as-some pay eqR) =
                  fromOf σ w optw pay hyp >>= λ l →
                  ok (castG (cong₃ idt refl eqL eqR) l)

  decide : ∀ {n} (σ : Sig) (hyp goal : Tm n) → Result (Link σ hyp goal)
  decide σ hyp goal with asId hyp
  ... | just (as-id A lhs rhs refl) = fromHyp σ A lhs rhs goal
  ... | nothing                     = fromBound σ hyp goal

------------------------------------------------------------------------
-- U8 examples. A failure is `fail` of the message, so the mismatch
-- prints that message. A success is `showR`, for the same reason.
-- Moduli of other widths are not built as successor towers: 256 is
-- U8's modulus and a different width's numeral, and that is enough
-- to take the width branch.
------------------------------------------------------------------------

showR : ∀ {A : Set} → Result A → String
showR (ok _)   = "ok"
showR (fail e) = e

withBodies : Tm 0 → Tm 0 → Tm 0 → Tm 0 → Sig
withBodies plusB minusB timesB leB = fromDefs
  (mkDef "plus"  run  natOpTy plusB  ∷
   mkDef "minus" run  natOpTy minusB ∷
   mkDef "times" run  timesTy  timesB ∷
   mkDef "Le"    spec leTy     leB    ∷ [])

exσ : Sig
exσ = withBodies (plusBody 0) (minusBody 1) (timesBody 0 2) (leBody 3)

-- A body that is not the library recursion. Le constantly Unit, times
-- written as the plus recursion, and plus or minus replaced by 0.
badPlusσ badMinusσ badTimesσ badLeσ : Sig
badPlusσ  = withBodies ze (minusBody 1) (timesBody 0 2) (leBody 3)
badMinusσ = withBodies (plusBody 0) ze (timesBody 0 2) (leBody 3)
badTimesσ = withBodies (plusBody 0) (minusBody 1) (plusBody 2) (leBody 3)
badLeσ    = withBodies (plusBody 0) (minusBody 1) (timesBody 0 2)
              (lam affine nat (lam affine nat unit))

a0 : Tm 0
a0 = wlitT ku8 1

b0 : Tm 0
b0 = wlitT ku8 2

c0 : Tm 0
c0 = wlitT ku8 3

opt8 : Tm 0
opt8 = word (woptk ku8) []

opt8w : Tm 0
opt8w = word wopt (word (wty ku8) [] ∷ [])

exHyp : Tm 0
exHyp = idt opt8 (word wcadd (a0 ∷ b0 ∷ [])) (word wsome (c0 ∷ []))

exHypW : Tm 0
exHypW = idt opt8w (word wcadd (a0 ∷ b0 ∷ [])) (word wsome (c0 ∷ []))

exGoal : Tm 0
exGoal = idt nat (ton c0) (bin 0 (ton a0) (ton b0))

ex-val : showR (decide exσ exHyp exGoal) ≡ "ok"
ex-val = refl

ex-val-w : showR (decide exσ exHypW exGoal) ≡ "ok"
ex-val-w = refl

fitGoal : Tm 0
fitGoal = bin 3 (su (bin 0 (ton a0) (ton b0))) (numeral 256)

ex-fit : showR (decide exσ exHyp fitGoal) ≡ "ok"
ex-fit = refl

someGoal : Tm 0
someGoal = idt opt8 (word wcadd (a0 ∷ b0 ∷ []))
               (word wsome (word (wof ku8) (bin 0 (ton a0) (ton b0) ∷ []) ∷ []))

ex-some : showR (decide exσ fitGoal someGoal) ≡ "ok"
ex-some = refl

subHyp : Tm 0
subHyp = idt opt8 (word wcsub (a0 ∷ b0 ∷ [])) (word wsome (c0 ∷ []))

subGoal : Tm 0
subGoal = idt nat (ton c0) (bin 1 (ton a0) (ton b0))

ex-sub-val : showR (decide exσ subHyp subGoal) ≡ "ok"
ex-sub-val = refl

subFit : Tm 0
subFit = bin 3 (ton b0) (ton a0)

ex-sub-fit : showR (decide exσ subHyp subFit) ≡ "ok"
ex-sub-fit = refl

subSome : Tm 0
subSome = idt opt8 (word wcsub (a0 ∷ b0 ∷ []))
              (word wsome (word (wof ku8) (bin 1 (ton a0) (ton b0) ∷ []) ∷ []))

ex-sub-some : showR (decide exσ subFit subSome) ≡ "ok"
ex-sub-some = refl

mulHyp : Tm 0
mulHyp = idt opt8 (word wcmul (a0 ∷ b0 ∷ [])) (word wsome (c0 ∷ []))

mulGoal : Tm 0
mulGoal = idt nat (ton c0) (bin 2 (ton a0) (ton b0))

ex-mul-val : showR (decide exσ mulHyp mulGoal) ≡ "ok"
ex-mul-val = refl

i64Hyp : Tm 0
i64Hyp = idt (word wopt (i64 ∷ [])) (word wcadd (a0 ∷ b0 ∷ [])) (word wsome (c0 ∷ []))

ex-i64 : decide exσ i64Hyp exGoal ≡ fail unsignedMsg
ex-i64 = refl

wrapHyp : Tm 0
wrapHyp = idt (word wopt (i64 ∷ [])) (word wadd (a0 ∷ b0 ∷ [])) (word wsome (c0 ∷ []))

ex-wrap : decide exσ wrapHyp exGoal ≡ fail wrapMsg
ex-wrap = refl

ex-op : decide exσ subHyp exGoal ≡ fail opMsg
ex-op = refl

wideGoal : Tm 0
wideGoal = idt opt8 (word wcadd (a0 ∷ b0 ∷ []))
               (word wsome (word (wof ku32) (ze ∷ []) ∷ []))

ex-width : decide exσ one wideGoal ≡ fail widthMsg
ex-width = refl

opt32 : Tm 0
opt32 = word (woptk ku32) []

u32Hyp : Tm 0
u32Hyp = idt opt32 (word wcadd (a0 ∷ b0 ∷ [])) (word wsome (c0 ∷ []))

ex-fit-width : decide exσ u32Hyp fitGoal ≡ fail widthMsg
ex-fit-width = refl

ex-miss : decide exσ one exGoal ≡ fail shapeMsg
ex-miss = refl

ex-mod-8 : isMod 256 dt8 ≡ true
ex-mod-8 = refl

ex-mod-32 : isMod 256 dt32 ≡ false
ex-mod-32 = refl

ex-other : otherWidth 256 dt32 ≡ true
ex-other = refl

ex-other-no : otherWidth 7 dt8 ≡ false
ex-other-no = refl

ex-plus-redef : decide badPlusσ exHyp exGoal ≡ fail (stdMsg "plus")
ex-plus-redef = refl

ex-minus-redef : decide badMinusσ subHyp subGoal ≡ fail (stdMsg "minus")
ex-minus-redef = refl

ex-times-redef : decide badTimesσ mulHyp mulGoal ≡ fail (stdMsg "times")
ex-times-redef = refl

-- times has the library body, and the plus it calls does not.
ex-times-bad-plus : decide badPlusσ mulHyp mulGoal ≡ fail (stdMsg "times")
ex-times-bad-plus = refl

ex-le-redef : decide badLeσ exHyp fitGoal ≡ fail (stdMsg "Le")
ex-le-redef = refl

swapSub : Tm 0
swapSub = bin 3 (ton a0) (ton b0)

ex-sub-swap : decide exσ subHyp swapSub ≡ fail shapeMsg
ex-sub-swap = refl

oddMod : Tm 0
oddMod = bin 3 (su (bin 0 (ton a0) (ton b0))) (numeral 7)

ex-mod-shape : decide exσ exHyp oddMod ≡ fail shapeMsg
ex-mod-shape = refl

mulSome : Tm 0
mulSome =
  idt opt8 (word wcmul (a0 ∷ b0 ∷ []))
      (word wsome (word (wof ku8) (bin 2 (ton a0) (ton b0) ∷ []) ∷ []))

ex-mul-some-hyp : decide exσ mulHyp mulSome ≡ fail shapeMsg
ex-mul-some-hyp = refl

ex-sub-some-hyp : decide exσ subHyp subSome ≡ fail shapeMsg
ex-sub-some-hyp = refl

nestedA : Tm 0
nestedA = word wadd (a0 ∷ b0 ∷ [])

nestHyp : Tm 0
nestHyp = idt opt8 (word wcadd (nestedA ∷ c0 ∷ [])) (word wsome (c0 ∷ []))

nestGoal : Tm 0
nestGoal = idt nat (ton c0) (bin 0 (ton nestedA) (ton c0))

ex-nested : showR (decide exσ nestHyp nestGoal) ≡ "ok"
ex-nested = refl

nestBad : Tm 0
nestBad = idt nat (ton c0) (bin 0 (ton a0) (ton c0))

ex-nested-bad : decide exσ nestHyp nestBad ≡ fail shapeMsg
ex-nested-bad = refl

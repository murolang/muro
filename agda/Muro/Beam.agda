------------------------------------------------------------------------
-- Erase a core term to the grade judgment.
--
-- `erase` reads a binder's quantity the way `Muro.Grade` does:
-- affine is the interval [0, 1], reuse is ω, erased is 0. The type
-- component of each of those is 0. A grade pair and the `%1` mark are
-- not constructors of `Tm`; the Elixir emitter reads them.
--
-- Domains, annotations, and a match motive are dropped. Everything
-- else fails, and the failure is the first constructor, not a walk
-- into it. `GTm` and `decide` are unchanged. The image is text. The
-- runtime that reads it checks the term again, so this erasure is not
-- part of that check.
--
-- There is no lemma that `decide` accepts `erase t`. A binder used
-- only as a type is charged one type use, and type grade 0 refuses it
-- (`type-use-refused`).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Beam where

open import Data.Fin.Base using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using ([])
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String.Base using (String; _++_)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

open import Muro.Base using (Qty; affine; reuse; erased; Result; ok; fail; run; _<$>_; _⊛_)
open import Muro.Syntax using (Tm; var; typ; pi; lam; app; nat; ze; su; unit; one; empty; dty; ctor; mData; mNat; mEmp; mUnit; idt; rfl; rwt; def; ann; prod; pair; letp; nu; unf; ucons; i64; f32ty; tensor; addi; muli; addt; toi64; packi; word; wadd)
open import Muro.Grade using (Grade; Point; fin; inf; pt; iv; g0; g1; gω; aff; GTm; gvar; gtyp; glam; gpi; gapp; gze; gsu; gmatch; decide)

------------------------------------------------------------------------
-- Image version. Both numbers are printed by `showℕ`, so a change
-- breaks the closed equalities below.
------------------------------------------------------------------------

format-version : ℕ
format-version = 1

boundary-version : ℕ
boundary-version = 1

------------------------------------------------------------------------
-- A quantity atom. The type grade is 0: a run use charges one
-- computational use and no type use, so an identity checks.
------------------------------------------------------------------------

type0 : Grade
type0 = g0

compGrade : Qty → Grade
compGrade affine = aff
compGrade reuse  = gω
compGrade erased = g0

erase : ∀ {n} → Tm n → Result (GTm n)
erase (var x) = ok (gvar x)
erase (lam q _ t) = glam (compGrade q) type0 <$> erase t
erase (pi q _ t) = gpi (compGrade q) type0 <$> erase t
erase (app f a) = gapp <$> erase f ⊛ erase a
erase ze = ok gze
erase (su t) = gsu <$> erase t
erase (mNat e _ z s) = (λ e z s → gmatch e z s) <$> erase e ⊛ erase z ⊛ erase s
erase (ann e _) = erase e
erase typ = fail "typ"
erase nat = fail "nat"
erase unit = fail "unit"
erase one = fail "unit"
erase (mUnit _ _ _) = fail "unit"
erase empty = fail "empty"
erase (mEmp _ _) = fail "empty"
erase (dty _) = fail "data"
erase (ctor _ _) = fail "data"
erase (mData _ _ ars _) = fail "data"
erase (idt _ _ _) = fail "id"
erase rfl = fail "id"
erase (rwt _ _ _) = fail "id"
erase (def _) = fail "def"
erase (prod _ _) = fail "pair"
erase (pair _ _) = fail "pair"
erase (letp _ _) = fail "pair"
erase (nu _) = fail "stream"
erase (unf _ _) = fail "stream"
erase (ucons _) = fail "stream"
erase i64 = fail "machine"
erase f32ty = fail "machine"
erase (tensor _ _) = fail "machine"
erase (addi _ _) = fail "machine"
erase (muli _ _) = fail "machine"
erase (addt _ _) = fail "machine"
erase (toi64 _) = fail "machine"
erase (packi _ _) = fail "machine"
erase (word _ _) = fail "word"

------------------------------------------------------------------------
-- Printer. Points are decimal, with no leading zero except 0. ω is `w`.
-- An interval is `(iv a b)`. A pair is `(c t)`. `gze` is bare.
------------------------------------------------------------------------

showPoint : Point → String
showPoint (fin n) = showℕ n
showPoint inf     = "w"

showGrade : Grade → String
showGrade (pt p)   = showPoint p
showGrade (iv a b) = "(iv " ++ showPoint a ++ " " ++ showPoint b ++ ")"

showPair : Grade → Grade → String
showPair c t = "(" ++ showGrade c ++ " " ++ showGrade t ++ ")"

showGTm : ∀ {n} → GTm n → String
showGTm (gvar x) = "(gvar " ++ showℕ (toℕ x) ++ ")"
showGTm (gtyp x) = "(gtyp " ++ showℕ (toℕ x) ++ ")"
showGTm (glam c t b) = "(glam " ++ showPair c t ++ " " ++ showGTm b ++ ")"
showGTm (gpi c t b) = "(gpi " ++ showPair c t ++ " " ++ showGTm b ++ ")"
showGTm (gapp f a) = "(gapp " ++ showGTm f ++ " " ++ showGTm a ++ ")"
showGTm gze = "gze"
showGTm (gsu e) = "(gsu " ++ showGTm e ++ ")"
showGTm (gmatch e z s) = "(gmatch " ++ showGTm e ++ " " ++ showGTm z ++ " " ++ showGTm s ++ ")"

showPure : ∀ {n} → GTm n → String
showPure t =
  "(muro-beam-image " ++ showℕ format-version ++ " (boundary " ++ showℕ boundary-version
    ++ ") (entry (seq " ++ showGTm t ++ " (done))))"

------------------------------------------------------------------------
-- Closed terms. Each `agree:` name is the string the Elixir emitter
-- prints for the same term.
------------------------------------------------------------------------

-- agree:once
show-once : showPure {zero} (glam g1 g0 (gvar fzero)) ≡ "(muro-beam-image 1 (boundary 1) (entry (seq (glam (1 0) (gvar 0)) (done))))"
show-once = refl

once-decides : decide run Vec.[] (glam g1 g0 (gvar fzero)) ≡ ok Vec.[]
once-decides = refl

-- agree:affine
show-affine : showPure {zero} (glam aff g0 (gvar fzero)) ≡ "(muro-beam-image 1 (boundary 1) (entry (seq (glam ((iv 0 1) 0) (gvar 0)) (done))))"
show-affine = refl

erase-affine : erase {zero} (lam affine nat (var fzero)) ≡ ok (glam aff g0 (gvar fzero))
erase-affine = refl

affine-decides : decide run Vec.[] (glam aff g0 (gvar fzero)) ≡ ok Vec.[]
affine-decides = refl

-- agree:reuse
show-reuse : showPure {zero} (glam gω g0 (gvar fzero)) ≡ "(muro-beam-image 1 (boundary 1) (entry (seq (glam (w 0) (gvar 0)) (done))))"
show-reuse = refl

-- agree:twice
show-twice : showPure {zero} (glam gω g0 (gapp (gvar fzero) (gvar fzero))) ≡ "(muro-beam-image 1 (boundary 1) (entry (seq (glam (w 0) (gapp (gvar 0) (gvar 0))) (done))))"
show-twice = refl

erase-reuse : erase {zero} (lam reuse nat (app (var fzero) (var fzero))) ≡ ok (glam gω g0 (gapp (gvar fzero) (gvar fzero)))
erase-reuse = refl

reuse-decides : decide run Vec.[] (glam gω g0 (gapp (gvar fzero) (gvar fzero))) ≡ ok Vec.[]
reuse-decides = refl

-- agree:drop
show-drop : showPure {zero} (glam g0 g0 gze) ≡ "(muro-beam-image 1 (boundary 1) (entry (seq (glam (0 0) gze) (done))))"
show-drop = refl

erase-drop : erase {zero} (lam erased nat ze) ≡ ok (glam g0 g0 gze)
erase-drop = refl

drop-decides : decide run Vec.[] (glam g0 g0 gze) ≡ ok Vec.[]
drop-decides = refl

-- agree:app
show-app : showPure {zero} (gapp (glam aff g0 (gvar fzero)) gze) ≡ "(muro-beam-image 1 (boundary 1) (entry (seq (gapp (glam ((iv 0 1) 0) (gvar 0)) gze) (done))))"
show-app = refl

erase-app : erase {zero} (app (lam affine nat (var fzero)) ze) ≡ ok (gapp (glam aff g0 (gvar fzero)) gze)
erase-app = refl

app-decides : decide run Vec.[] (gapp (glam aff g0 (gvar fzero)) gze) ≡ ok Vec.[]
app-decides = refl

-- agree:suc
show-suc : showPure {zero} (gsu (gsu gze)) ≡ "(muro-beam-image 1 (boundary 1) (entry (seq (gsu (gsu gze)) (done))))"
show-suc = refl

erase-suc : erase {zero} (su (su ze)) ≡ ok (gsu (gsu gze))
erase-suc = refl

suc-decides : decide run Vec.[] (gsu (gsu gze)) ≡ ok Vec.[]
suc-decides = refl

-- agree:match
show-match : showPure {zero} (gmatch gze gze (gvar fzero)) ≡ "(muro-beam-image 1 (boundary 1) (entry (seq (gmatch gze gze (gvar 0)) (done))))"
show-match = refl

erase-match : erase {zero} (mNat ze (lam affine nat nat) ze (var fzero)) ≡ ok (gmatch gze gze (gvar fzero))
erase-match = refl

match-decides : decide run Vec.[] (gmatch gze gze (gvar fzero)) ≡ ok Vec.[]
match-decides = refl

erase-match-ze : erase {zero} (mNat ze nat ze ze) ≡ ok (gmatch gze gze gze)
erase-match-ze = refl

-- agree:pi
show-pi : showPure {zero} (gpi aff g0 (gvar fzero)) ≡ "(muro-beam-image 1 (boundary 1) (entry (seq (gpi ((iv 0 1) 0) (gvar 0)) (done))))"
show-pi = refl

erase-pi : erase {zero} (pi affine nat (var fzero)) ≡ ok (gpi aff g0 (gvar fzero))
erase-pi = refl

-- agree:iv
show-iv : showPure {zero} (glam (iv (fin zero) (fin 2)) g0 (gvar fzero)) ≡ "(muro-beam-image 1 (boundary 1) (entry (seq (glam ((iv 0 2) 0) (gvar 0)) (done))))"
show-iv = refl

erase-ann : erase {zero} (ann ze nat) ≡ ok gze
erase-ann = refl

erase-domain : erase {zero} (lam affine (prod nat nat) (var fzero)) ≡ ok (glam aff g0 (gvar fzero))
erase-domain = refl

-- The outer binder is used once, as a type, under the Π. Spec charges
-- that use to the type grade. Grade 0 does not allow it.
erase-type-use :
  erase {zero} (lam affine nat (pi affine nat (var (fsuc fzero))))
    ≡ ok (glam aff g0 (gpi aff g0 (gvar (fsuc fzero))))
erase-type-use = refl

type-use-refused :
  decide run Vec.[] (glam aff g0 (gpi aff g0 (gvar (fsuc fzero))))
    ≡ fail "type grade 0 does not allow 1 uses"
type-use-refused = refl

-- agree:fail-typ
fail-typ : erase {zero} typ ≡ fail "typ"
fail-typ = refl

-- agree:fail-nat
fail-nat : erase {zero} nat ≡ fail "nat"
fail-nat = refl

-- agree:fail-unit
fail-unit : erase {zero} unit ≡ fail "unit"
fail-unit = refl

fail-one : erase {zero} one ≡ fail "unit"
fail-one = refl

-- agree:fail-empty
fail-empty : erase {zero} empty ≡ fail "empty"
fail-empty = refl

-- agree:fail-data
fail-data : erase {zero} (dty 0) ≡ fail "data"
fail-data = refl

-- agree:fail-id
fail-id : erase {zero} rfl ≡ fail "id"
fail-id = refl

-- agree:fail-def
fail-def : erase {zero} (def 0) ≡ fail "def"
fail-def = refl

-- agree:fail-pair
fail-pair : erase {zero} (pair ze ze) ≡ fail "pair"
fail-pair = refl

-- agree:fail-stream
fail-stream : erase {zero} (nu ze) ≡ fail "stream"
fail-stream = refl

-- agree:fail-machine
fail-machine : erase {zero} i64 ≡ fail "machine"
fail-machine = refl

-- agree:fail-word
fail-word : erase {zero} (word wadd []) ≡ fail "word"
fail-word = refl

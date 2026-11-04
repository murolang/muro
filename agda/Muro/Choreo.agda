------------------------------------------------------------------------
-- A choreography is a global type. A role is a name. `endG` finishes.
-- `comm` is one role sending a payload of a type to another, then one
-- continuation. `choice` is one role choosing a labelled branch. A
-- role does not interact with itself. The label selects the branch.
-- The projected session records the payload and the choice, not the
-- label text.
--
-- Projection is pairwise. `g ↾ r / s ≡ b` is the binary session role
-- `r` runs with role `s`, written on `Bin` and erased to `Proto`.
-- On a message from `a` to `b`, `(a, b)` sends and `(b, a)` receives.
-- Any other pair keeps the continuation. On a choice by `p`, `(p, s)`
-- is an internal choice and `(r, p)` is an external choice. More than
-- two branches nest to the right. A pair that is neither end of that
-- choice has a session only when every branch projects to the same
-- session. That is plain merge. Fewer than two branches is not a
-- choice.
--
-- `project` decides the judgment: it is sound and complete. For every
-- pair of roles, the session `r` has with `s` is dual to the session
-- `s` has with `r`.
--
-- The choreography is spec. A projected session is evidence a `seen`
-- session can name. No constructor is added to Tm. A run term does
-- not carry a choreography.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Choreo where

open import Data.Bool.Base using (Bool; true; false; if_then_else_; _∧_)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String.Base using (String)
open import Data.String.Properties using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Relation.Nullary.Negation.Core using (¬_)

open import Muro.Session using (Proto; Ty; unit; end; send; recv; choose; branch; ty≟)
open import Muro.Dual using (dual)

------------------------------------------------------------------------
-- A comparison is a data type. `ok` is the boolean the projection
-- branches on, so a proof that matches `yes′` or `no′` takes the
-- same branch as the function.
------------------------------------------------------------------------

data DecEq (A : Set) : Set where
  yes′ : A → DecEq A
  no′  : ¬ A → DecEq A

ok : {A : Set} → DecEq A → Bool
ok (yes′ _) = true
ok (no′ _) = false

------------------------------------------------------------------------
-- Roles and global types.
------------------------------------------------------------------------

data Role : Set where
  role : String → Role

role-eq : (p q : Role) → DecEq (p ≡ q)
role-eq (role x) (role y) with x ≟ y
... | yes eq = yes′ (cong role eq)
... | no ¬eq = no′ (λ { refl → ¬eq refl })

data GType : Set where
  endG   : GType
  comm   : Role → Role → String → Ty → GType → GType
  choice : Role → List (String × GType) → GType

------------------------------------------------------------------------
-- The image of projection. `Bin` is the fragment of `Proto` a
-- choreography can produce: end, send, recv, choose, branch.
-- `⌊_⌋` erases it. `bin-dual` is `dual` on that fragment.
------------------------------------------------------------------------

data Bin : Set where
  bend    : Bin
  bsend   : Ty → Bin → Bin
  brecv   : Ty → Bin → Bin
  bchoose : Bin → Bin → Bin
  bbranch : Bin → Bin → Bin

⌊_⌋ : Bin → Proto
⌊ bend ⌋ = end
⌊ bsend A b ⌋ = send A ⌊ b ⌋
⌊ brecv A b ⌋ = recv A ⌊ b ⌋
⌊ bchoose b c ⌋ = choose ⌊ b ⌋ ⌊ c ⌋
⌊ bbranch b c ⌋ = branch ⌊ b ⌋ ⌊ c ⌋

bin-dual : Bin → Bin
bin-dual bend = bend
bin-dual (bsend A b) = brecv A (bin-dual b)
bin-dual (brecv A b) = bsend A (bin-dual b)
bin-dual (bchoose b c) = bbranch (bin-dual b) (bin-dual c)
bin-dual (bbranch b c) = bchoose (bin-dual b) (bin-dual c)

⌊-dual⌋ : ∀ b → ⌊ bin-dual b ⌋ ≡ dual ⌊ b ⌋
⌊-dual⌋ bend = refl
⌊-dual⌋ (bsend A b) = cong (recv A) (⌊-dual⌋ b)
⌊-dual⌋ (brecv A b) = cong (send A) (⌊-dual⌋ b)
⌊-dual⌋ (bchoose b c) = cong₂ branch (⌊-dual⌋ b) (⌊-dual⌋ c)
⌊-dual⌋ (bbranch b c) = cong₂ choose (⌊-dual⌋ b) (⌊-dual⌋ c)

bin-eq : (b c : Bin) → DecEq (b ≡ c)
bin-eq bend bend = yes′ refl
bin-eq bend (bsend _ _) = no′ (λ ())
bin-eq bend (brecv _ _) = no′ (λ ())
bin-eq bend (bchoose _ _) = no′ (λ ())
bin-eq bend (bbranch _ _) = no′ (λ ())
bin-eq (bsend _ _) bend = no′ (λ ())
bin-eq (bsend A b) (bsend B c) with ty≟ A B
... | no ¬eq = no′ (λ { refl → ¬eq refl })
... | yes refl with bin-eq b c
... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
... | yes′ refl = yes′ refl
bin-eq (bsend _ _) (brecv _ _) = no′ (λ ())
bin-eq (bsend _ _) (bchoose _ _) = no′ (λ ())
bin-eq (bsend _ _) (bbranch _ _) = no′ (λ ())
bin-eq (brecv _ _) bend = no′ (λ ())
bin-eq (brecv _ _) (bsend _ _) = no′ (λ ())
bin-eq (brecv A b) (brecv B c) with ty≟ A B
... | no ¬eq = no′ (λ { refl → ¬eq refl })
... | yes refl with bin-eq b c
... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
... | yes′ refl = yes′ refl
bin-eq (brecv _ _) (bchoose _ _) = no′ (λ ())
bin-eq (brecv _ _) (bbranch _ _) = no′ (λ ())
bin-eq (bchoose _ _) bend = no′ (λ ())
bin-eq (bchoose _ _) (bsend _ _) = no′ (λ ())
bin-eq (bchoose _ _) (brecv _ _) = no′ (λ ())
bin-eq (bchoose b c) (bchoose d e) with bin-eq b d
... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
... | yes′ refl with bin-eq c e
... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
... | yes′ refl = yes′ refl
bin-eq (bchoose _ _) (bbranch _ _) = no′ (λ ())
bin-eq (bbranch _ _) bend = no′ (λ ())
bin-eq (bbranch _ _) (bsend _ _) = no′ (λ ())
bin-eq (bbranch _ _) (brecv _ _) = no′ (λ ())
bin-eq (bbranch _ _) (bchoose _ _) = no′ (λ ())
bin-eq (bbranch b c) (bbranch d e) with bin-eq b d
... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
... | yes′ refl with bin-eq c e
... | no′ ¬eq = no′ (λ { refl → ¬eq refl })
... | yes′ refl = yes′ refl

------------------------------------------------------------------------
-- Plain merge needs every branch session to be the same one.
-- A choice nests when the chooser is one end of the pair.
------------------------------------------------------------------------

data EqAll : Bin → List Bin → Set where
  eq[] : ∀ {b} → EqAll b []
  eq∷  : ∀ {b x xs} → b ≡ x → EqAll b xs → EqAll b (x ∷ xs)

-- The list has at least two sessions, and each of them is `b`.
data Some : Bin → List Bin → Set where
  some : ∀ {b x xs} → EqAll b (x ∷ xs) → Some b (b ∷ x ∷ xs)

data NestC : List Bin → Bin → Set where
  nest-two  : ∀ {b c} → NestC (b ∷ c ∷ []) (bchoose b c)
  nest-more : ∀ {b c cs n} → NestC (c ∷ cs) n → NestC (b ∷ c ∷ cs) (bchoose b n)

data NestB : List Bin → Bin → Set where
  nest-two  : ∀ {b c} → NestB (b ∷ c ∷ []) (bbranch b c)
  nest-more : ∀ {b c cs n} → NestB (c ∷ cs) n → NestB (b ∷ c ∷ cs) (bbranch b n)

------------------------------------------------------------------------
-- `g ↾ r / s ≡ b`. One rule for the end, three for a message
-- (send, receive, skip), three for a choice (internal, external,
-- plain merge).
------------------------------------------------------------------------

mutual
  infix 4 _↾_/_≡_

  data _↾_/_≡_ : GType → Role → Role → Bin → Set where
    rend : ∀ {r s} →
      ¬ (r ≡ s) →
      endG ↾ r / s ≡ bend

    rsend : ∀ {a b ℓ A g r s c} →
      ¬ (a ≡ b) →
      ¬ (r ≡ s) →
      r ≡ a →
      s ≡ b →
      g ↾ r / s ≡ c →
      comm a b ℓ A g ↾ r / s ≡ bsend A c

    rrecv : ∀ {a b ℓ A g r s c} →
      ¬ (a ≡ b) →
      ¬ (r ≡ s) →
      r ≡ b →
      s ≡ a →
      g ↾ r / s ≡ c →
      comm a b ℓ A g ↾ r / s ≡ brecv A c

    rskip : ∀ {a b ℓ A g r s c} →
      ¬ (a ≡ b) →
      ¬ (r ≡ s) →
      ¬ (r ≡ a × s ≡ b) →
      ¬ (r ≡ b × s ≡ a) →
      g ↾ r / s ≡ c →
      comm a b ℓ A g ↾ r / s ≡ c

    rchoose : ∀ {p r s bs cs n} →
      ¬ (r ≡ s) →
      r ≡ p →
      AllP bs r s cs →
      NestC cs n →
      choice p bs ↾ r / s ≡ n

    rbranch : ∀ {p r s bs cs n} →
      ¬ (r ≡ s) →
      s ≡ p →
      AllP bs r s cs →
      NestB cs n →
      choice p bs ↾ r / s ≡ n

    rmerge : ∀ {p r s bs cs c} →
      ¬ (r ≡ s) →
      ¬ (r ≡ p) →
      ¬ (s ≡ p) →
      AllP bs r s cs →
      Some c cs →
      choice p bs ↾ r / s ≡ c

  data AllP : List (String × GType) → Role → Role → List Bin → Set where
    ap[] : ∀ {r s} → AllP [] r s []
    ap∷  : ∀ {ℓ g b bs cs r s} →
      g ↾ r / s ≡ b →
      AllP bs r s cs →
      AllP ((ℓ , g) ∷ bs) r s (b ∷ cs)

------------------------------------------------------------------------
-- The projection function.
------------------------------------------------------------------------

mmap : (Bin → Bin) → Maybe Bin → Maybe Bin
mmap _ nothing = nothing
mmap f (just b) = just (f b)

project-end : {r s : Role} → DecEq (r ≡ s) → Maybe Bin
project-end d = if ok d then nothing else just bend

project-comm : {a b r s : Role} →
  Ty → Maybe Bin →
  DecEq (a ≡ b) → DecEq (r ≡ s) →
  DecEq (r ≡ a) → DecEq (s ≡ b) →
  DecEq (r ≡ b) → DecEq (s ≡ a) →
  Maybe Bin
project-comm A m ab rs ra sb rb sa =
  if ok ab then nothing
  else if ok rs then nothing
  else if ok ra ∧ ok sb then mmap (bsend A) m
  else if ok rb ∧ ok sa then mmap (brecv A) m
  else m

data Part : Set where
  sameR internal external merged : Part

parts-of : {r s p : Role} → DecEq (r ≡ s) → DecEq (r ≡ p) → DecEq (s ≡ p) → Part
parts-of rs rp sp =
  if ok rs then sameR
  else if ok rp then internal
  else if ok sp then external
  else merged

nestc : Bin → Bin → List Bin → Bin
nestc b c [] = bchoose b c
nestc b c (d ∷ ds) = bchoose b (nestc c d ds)

nestb : Bin → Bin → List Bin → Bin
nestb b c [] = bbranch b c
nestb b c (d ∷ ds) = bbranch b (nestb c d ds)

nest-choose : List Bin → Maybe Bin
nest-choose [] = nothing
nest-choose (_ ∷ []) = nothing
nest-choose (b ∷ c ∷ ds) = just (nestc b c ds)

nest-branch : List Bin → Maybe Bin
nest-branch [] = nothing
nest-branch (_ ∷ []) = nothing
nest-branch (b ∷ c ∷ ds) = just (nestb b c ds)

merge-step : {b x : Bin} → DecEq (b ≡ x) → Maybe Bin → Maybe Bin
merge-step d m = if ok d then m else nothing

merge-from : Bin → List Bin → Maybe Bin
merge-from b [] = just b
merge-from b (x ∷ xs) = merge-step (bin-eq b x) (merge-from b xs)

merge-all : List Bin → Maybe Bin
merge-all [] = nothing
merge-all (_ ∷ []) = nothing
merge-all (b ∷ x ∷ xs) = merge-from b (x ∷ xs)

project-choice : Part → Maybe (List Bin) → Maybe Bin
project-choice sameR _ = nothing
project-choice internal nothing = nothing
project-choice internal (just cs) = nest-choose cs
project-choice external nothing = nothing
project-choice external (just cs) = nest-branch cs
project-choice merged nothing = nothing
project-choice merged (just cs) = merge-all cs

cons-m : Maybe Bin → Maybe (List Bin) → Maybe (List Bin)
cons-m nothing _ = nothing
cons-m (just _) nothing = nothing
cons-m (just b) (just cs) = just (b ∷ cs)

mutual
  projectBin : GType → Role → Role → Maybe Bin
  projectBin endG r s = project-end (role-eq r s)
  projectBin (comm a b _ A g) r s =
    project-comm A (projectBin g r s)
      (role-eq a b) (role-eq r s)
      (role-eq r a) (role-eq s b)
      (role-eq r b) (role-eq s a)
  projectBin (choice p bs) r s =
    project-choice
      (parts-of (role-eq r s) (role-eq r p) (role-eq s p))
      (projects bs r s)

  projects : List (String × GType) → Role → Role → Maybe (List Bin)
  projects [] _ _ = just []
  projects ((_ , g) ∷ bs) r s = cons-m (projectBin g r s) (projects bs r s)

erase : Maybe Bin → Maybe Proto
erase nothing = nothing
erase (just b) = just ⌊ b ⌋

project : GType → Role → Role → Maybe Proto
project g r s = erase (projectBin g r s)

------------------------------------------------------------------------
-- Soundness. A session the function returns is a derivation.
------------------------------------------------------------------------

not-left : ∀ {A B : Set} → ¬ A → ¬ (A × B)
not-left ¬a (a , _) = ¬a a

not-right : ∀ {A B : Set} → ¬ B → ¬ (A × B)
not-right ¬b (_ , b) = ¬b b

nestc-ok : ∀ b c ds → NestC (b ∷ c ∷ ds) (nestc b c ds)
nestc-ok b c [] = nest-two
nestc-ok b c (d ∷ ds) = nest-more (nestc-ok c d ds)

nestb-ok : ∀ b c ds → NestB (b ∷ c ∷ ds) (nestb b c ds)
nestb-ok b c [] = nest-two
nestb-ok b c (d ∷ ds) = nest-more (nestb-ok c d ds)

nest-inv : ∀ cs n → nest-choose cs ≡ just n → NestC cs n
nest-inv [] _ ()
nest-inv (_ ∷ []) _ ()
nest-inv (b ∷ c ∷ ds) .(nestc b c ds) refl = nestc-ok b c ds

nestb-inv : ∀ cs n → nest-branch cs ≡ just n → NestB cs n
nestb-inv [] _ ()
nestb-inv (_ ∷ []) _ ()
nestb-inv (b ∷ c ∷ ds) .(nestb b c ds) refl = nestb-ok b c ds

pair-inv : ∀ {b x xs d} → b ≡ x → d ≡ b × EqAll b xs → d ≡ b × EqAll b (x ∷ xs)
pair-inv p (refl , rest) = refl , eq∷ p rest

some-of : ∀ {b x xs c} → c ≡ b × EqAll b (x ∷ xs) → Some c (b ∷ x ∷ xs)
some-of (refl , e) = some e

mutual
  from-inv : (b : Bin) (xs : List Bin) (d : Bin) →
    merge-from b xs ≡ just d → d ≡ b × EqAll b xs
  from-inv b [] .b refl = refl , eq[]
  from-inv b (x ∷ xs) d eq = step-inv (bin-eq b x) xs d eq

  step-inv : {b x : Bin} (dec : DecEq (b ≡ x)) (xs : List Bin) (d : Bin) →
    merge-step dec (merge-from b xs) ≡ just d →
    d ≡ b × EqAll b (x ∷ xs)
  step-inv (no′ _) _ _ ()
  step-inv (yes′ p) xs d eq = pair-inv p (from-inv _ xs d eq)

merge-inv : ∀ cs c → merge-all cs ≡ just c → Some c cs
merge-inv [] _ ()
merge-inv (_ ∷ []) _ ()
merge-inv (b ∷ x ∷ xs) c eq = some-of (from-inv b (x ∷ xs) c eq)

send-go : ∀ {a b ℓ A g r s c} →
  ¬ (a ≡ b) → ¬ (r ≡ s) → r ≡ a → s ≡ b →
  (m : Maybe Bin) →
  (∀ d → m ≡ just d → g ↾ r / s ≡ d) →
  mmap (bsend A) m ≡ just c →
  comm a b ℓ A g ↾ r / s ≡ c
send-go ¬ab ¬rs ra sb nothing _ ()
send-go ¬ab ¬rs ra sb (just d) ih refl =
  rsend ¬ab ¬rs ra sb (ih d refl)

recv-go : ∀ {a b ℓ A g r s c} →
  ¬ (a ≡ b) → ¬ (r ≡ s) → r ≡ b → s ≡ a →
  (m : Maybe Bin) →
  (∀ d → m ≡ just d → g ↾ r / s ≡ d) →
  mmap (brecv A) m ≡ just c →
  comm a b ℓ A g ↾ r / s ≡ c
recv-go ¬ab ¬rs rb sa nothing _ ()
recv-go ¬ab ¬rs rb sa (just d) ih refl =
  rrecv ¬ab ¬rs rb sa (ih d refl)

after-self : {a b r s : Role} {ℓ : String} {A : Ty} {g : GType} {c : Bin} →
  (¬ab : ¬ (a ≡ b)) (¬rs : ¬ (r ≡ s)) →
  (m : Maybe Bin) →
  (ra : DecEq (r ≡ a)) (sb : DecEq (s ≡ b)) →
  (rb : DecEq (r ≡ b)) (sa : DecEq (s ≡ a)) →
  (∀ d → m ≡ just d → g ↾ r / s ≡ d) →
  project-comm A m (no′ ¬ab) (no′ ¬rs) ra sb rb sa ≡ just c →
  comm a b ℓ A g ↾ r / s ≡ c
after-self ¬ab ¬rs m (yes′ ra) (yes′ sb) _ _ ih eq =
  send-go ¬ab ¬rs ra sb m ih eq
after-self ¬ab ¬rs m (yes′ _) (no′ _) (yes′ rb) (yes′ sa) ih eq =
  recv-go ¬ab ¬rs rb sa m ih eq
after-self {c = c} ¬ab ¬rs _ (yes′ _) (no′ ¬sb) (yes′ _) (no′ ¬sa) ih eq =
  rskip ¬ab ¬rs (not-right ¬sb) (not-right ¬sa) (ih c eq)
after-self {c = c} ¬ab ¬rs _ (yes′ _) (no′ ¬sb) (no′ ¬rb) (yes′ _) ih eq =
  rskip ¬ab ¬rs (not-right ¬sb) (not-left ¬rb) (ih c eq)
after-self {c = c} ¬ab ¬rs _ (yes′ _) (no′ ¬sb) (no′ ¬rb) (no′ ¬sa) ih eq =
  rskip ¬ab ¬rs (not-right ¬sb) (not-right ¬sa) (ih c eq)
after-self ¬ab ¬rs m (no′ _) (yes′ _) (yes′ rb) (yes′ sa) ih eq =
  recv-go ¬ab ¬rs rb sa m ih eq
after-self {c = c} ¬ab ¬rs _ (no′ ¬ra) (yes′ _) (yes′ _) (no′ ¬sa) ih eq =
  rskip ¬ab ¬rs (not-left ¬ra) (not-right ¬sa) (ih c eq)
after-self {c = c} ¬ab ¬rs _ (no′ ¬ra) (yes′ _) (no′ ¬rb) (yes′ _) ih eq =
  rskip ¬ab ¬rs (not-left ¬ra) (not-left ¬rb) (ih c eq)
after-self {c = c} ¬ab ¬rs _ (no′ ¬ra) (yes′ _) (no′ ¬rb) (no′ ¬sa) ih eq =
  rskip ¬ab ¬rs (not-left ¬ra) (not-right ¬sa) (ih c eq)
after-self ¬ab ¬rs m (no′ _) (no′ _) (yes′ rb) (yes′ sa) ih eq =
  recv-go ¬ab ¬rs rb sa m ih eq
after-self {c = c} ¬ab ¬rs _ (no′ ¬ra) (no′ _) (yes′ _) (no′ ¬sa) ih eq =
  rskip ¬ab ¬rs (not-left ¬ra) (not-right ¬sa) (ih c eq)
after-self {c = c} ¬ab ¬rs _ (no′ ¬ra) (no′ _) (no′ ¬rb) (yes′ _) ih eq =
  rskip ¬ab ¬rs (not-left ¬ra) (not-left ¬rb) (ih c eq)
after-self {c = c} ¬ab ¬rs _ (no′ ¬ra) (no′ _) (no′ _) (no′ ¬sa) ih eq =
  rskip ¬ab ¬rs (not-left ¬ra) (not-right ¬sa) (ih c eq)

comm-sound : {a b r s : Role} {ℓ : String} {A : Ty} {g : GType} {c : Bin} {m : Maybe Bin} →
  (ab : DecEq (a ≡ b)) (rs : DecEq (r ≡ s)) →
  (ra : DecEq (r ≡ a)) (sb : DecEq (s ≡ b)) →
  (rb : DecEq (r ≡ b)) (sa : DecEq (s ≡ a)) →
  (∀ d → m ≡ just d → g ↾ r / s ≡ d) →
  project-comm A m ab rs ra sb rb sa ≡ just c →
  comm a b ℓ A g ↾ r / s ≡ c
comm-sound (yes′ _) _ _ _ _ _ _ ()
comm-sound (no′ _) (yes′ _) _ _ _ _ _ ()
comm-sound {m = m} (no′ ¬ab) (no′ ¬rs) ra sb rb sa ih eq =
  after-self ¬ab ¬rs m ra sb rb sa ih eq

end-sound : {r s : Role} {c : Bin} (d : DecEq (r ≡ s)) →
  project-end d ≡ just c → endG ↾ r / s ≡ c
end-sound (yes′ _) ()
end-sound (no′ ¬eq) refl = rend ¬eq

choice-sound : {p r s : Role} {bs : List (String × GType)} {c : Bin} →
  (rs : DecEq (r ≡ s)) (rp : DecEq (r ≡ p)) (sp : DecEq (s ≡ p)) →
  (m : Maybe (List Bin)) →
  (∀ cs → m ≡ just cs → AllP bs r s cs) →
  project-choice (parts-of rs rp sp) m ≡ just c →
  choice p bs ↾ r / s ≡ c
choice-sound (yes′ _) _ _ _ _ ()
choice-sound (no′ _) (yes′ _) _ nothing _ ()
choice-sound {c = c} (no′ ¬rs) (yes′ rp) _ (just cs) ih eq =
  rchoose ¬rs rp (ih cs refl) (nest-inv cs c eq)
choice-sound (no′ _) (no′ _) (yes′ _) nothing _ ()
choice-sound {c = c} (no′ ¬rs) (no′ _) (yes′ sp) (just cs) ih eq =
  rbranch ¬rs sp (ih cs refl) (nestb-inv cs c eq)
choice-sound (no′ _) (no′ _) (no′ _) nothing _ ()
choice-sound {c = c} (no′ ¬rs) (no′ ¬rp) (no′ ¬sp) (just cs) ih eq =
  rmerge ¬rs ¬rp ¬sp (ih cs refl) (merge-inv cs c eq)

mutual
  project-sound : ∀ g r s b → projectBin g r s ≡ just b → g ↾ r / s ≡ b
  project-sound endG r s b eq = end-sound (role-eq r s) eq
  project-sound (comm a b _ A g) r s c eq =
    comm-sound (role-eq a b) (role-eq r s) (role-eq r a) (role-eq s b)
      (role-eq r b) (role-eq s a) (project-sound g r s) eq
  project-sound (choice p bs) r s c eq =
    choice-sound (role-eq r s) (role-eq r p) (role-eq s p)
      (projects bs r s) (projects-sound bs r s) eq

  projects-sound : ∀ bs r s cs →
    projects bs r s ≡ just cs → AllP bs r s cs
  projects-sound [] _ _ .[] refl = ap[]
  projects-sound ((_ , g) ∷ bs) r s cs eq
    with projectBin g r s in peq | projects bs r s in qeq
  projects-sound ((_ , g) ∷ bs) r s cs () | nothing | _
  projects-sound ((_ , g) ∷ bs) r s cs () | just _ | nothing
  projects-sound ((_ , g) ∷ bs) r s .(b ∷ ds) refl | just b | just ds =
    ap∷ (project-sound g r s b peq) (projects-sound bs r s ds qeq)

------------------------------------------------------------------------
-- Completeness. A derivation is a session the function returns.
------------------------------------------------------------------------

mutual
  from-eq : {b : Bin} {xs : List Bin} → EqAll b xs → merge-from b xs ≡ just b
  from-eq eq[] = refl
  from-eq (eq∷ {b = b} {x = x} p rest) = step-eq (bin-eq b x) p rest

  step-eq : {b x : Bin} {xs : List Bin} (d : DecEq (b ≡ x)) → b ≡ x → EqAll b xs →
    merge-step d (merge-from b xs) ≡ just b
  step-eq (no′ ¬eq) eq _ = ⊥-elim (¬eq eq)
  step-eq (yes′ _) _ rest = from-eq rest

some-complete : ∀ {b cs} → Some b cs → merge-all cs ≡ just b
some-complete (some e) = from-eq e

nestc≡ : ∀ {c ds n} (b : Bin) → NestC (c ∷ ds) n → nestc b c ds ≡ bchoose b n
nestc≡ _ nest-two = refl
nestc≡ b (nest-more d) = cong (bchoose b) (nestc≡ _ d)

nestb≡ : ∀ {c ds n} (b : Bin) → NestB (c ∷ ds) n → nestb b c ds ≡ bbranch b n
nestb≡ _ nest-two = refl
nestb≡ b (nest-more d) = cong (bbranch b) (nestb≡ _ d)

nest-complete : ∀ {cs n} → NestC cs n → nest-choose cs ≡ just n
nest-complete nest-two = refl
nest-complete (nest-more {b = b} d) = cong just (nestc≡ b d)

nestb-complete : ∀ {cs n} → NestB cs n → nest-branch cs ≡ just n
nestb-complete nest-two = refl
nestb-complete (nest-more {b = b} d) = cong just (nestb≡ b d)

end-complete : {r s : Role} (d : DecEq (r ≡ s)) → ¬ (r ≡ s) →
  project-end d ≡ just bend
end-complete (yes′ eq) ¬eq = ⊥-elim (¬eq eq)
end-complete (no′ _) _ = refl

send-complete : {A : Ty} {c : Bin} {a b r s : Role} {m : Maybe Bin}
  (ab : DecEq (a ≡ b)) (rs : DecEq (r ≡ s))
  (ra : DecEq (r ≡ a)) (sb : DecEq (s ≡ b))
  (rb : DecEq (r ≡ b)) (sa : DecEq (s ≡ a)) →
  ¬ (a ≡ b) → ¬ (r ≡ s) → r ≡ a → s ≡ b →
  m ≡ just c →
  project-comm A m ab rs ra sb rb sa ≡ just (bsend A c)
send-complete (yes′ eq) _ _ _ _ _ ¬ab _ _ _ _ = ⊥-elim (¬ab eq)
send-complete (no′ _) (yes′ eq) _ _ _ _ _ ¬rs _ _ _ = ⊥-elim (¬rs eq)
send-complete (no′ _) (no′ _) (no′ ¬ra) _ _ _ _ _ ra _ _ = ⊥-elim (¬ra ra)
send-complete (no′ _) (no′ _) (yes′ _) (no′ ¬sb) _ _ _ _ _ sb _ = ⊥-elim (¬sb sb)
send-complete (no′ _) (no′ _) (yes′ _) (yes′ _) _ _ _ _ _ _ refl = refl

recv-complete : {A : Ty} {c : Bin} {a b r s : Role} {m : Maybe Bin}
  (ab : DecEq (a ≡ b)) (rs : DecEq (r ≡ s))
  (ra : DecEq (r ≡ a)) (sb : DecEq (s ≡ b))
  (rb : DecEq (r ≡ b)) (sa : DecEq (s ≡ a)) →
  ¬ (a ≡ b) → ¬ (r ≡ s) → r ≡ b → s ≡ a →
  m ≡ just c →
  project-comm A m ab rs ra sb rb sa ≡ just (brecv A c)
recv-complete (yes′ eq) _ _ _ _ _ ¬ab _ _ _ _ = ⊥-elim (¬ab eq)
recv-complete (no′ _) (yes′ eq) _ _ _ _ _ ¬rs _ _ _ = ⊥-elim (¬rs eq)
recv-complete (no′ _) (no′ _) (yes′ ra) _ _ _ ¬ab _ rb _ _ =
  ⊥-elim (¬ab (trans (sym ra) rb))
recv-complete (no′ _) (no′ _) (no′ _) _ (no′ ¬rb) _ _ _ rb _ _ = ⊥-elim (¬rb rb)
recv-complete (no′ _) (no′ _) (no′ _) _ (yes′ _) (no′ ¬sa) _ _ _ sa _ =
  ⊥-elim (¬sa sa)
recv-complete (no′ _) (no′ _) (no′ _) _ (yes′ _) (yes′ _) _ _ _ _ refl = refl

skip-complete : {A : Ty} {c : Bin} {a b r s : Role} {m : Maybe Bin}
  (ab : DecEq (a ≡ b)) (rs : DecEq (r ≡ s))
  (ra : DecEq (r ≡ a)) (sb : DecEq (s ≡ b))
  (rb : DecEq (r ≡ b)) (sa : DecEq (s ≡ a)) →
  ¬ (a ≡ b) → ¬ (r ≡ s) →
  ¬ (r ≡ a × s ≡ b) → ¬ (r ≡ b × s ≡ a) →
  m ≡ just c →
  project-comm A m ab rs ra sb rb sa ≡ just c
skip-complete (yes′ eq) _ _ _ _ _ ¬ab _ _ _ _ = ⊥-elim (¬ab eq)
skip-complete (no′ _) (yes′ eq) _ _ _ _ _ ¬rs _ _ _ = ⊥-elim (¬rs eq)
skip-complete (no′ _) (no′ _) (yes′ ra) (yes′ sb) _ _ _ _ ¬send _ _ =
  ⊥-elim (¬send (ra , sb))
skip-complete (no′ _) (no′ _) (yes′ _) (no′ _) (yes′ rb) (yes′ sa) _ _ _ ¬recv _ =
  ⊥-elim (¬recv (rb , sa))
skip-complete (no′ _) (no′ _) (yes′ _) (no′ _) (yes′ _) (no′ _) _ _ _ _ refl = refl
skip-complete (no′ _) (no′ _) (yes′ _) (no′ _) (no′ _) (yes′ _) _ _ _ _ refl = refl
skip-complete (no′ _) (no′ _) (yes′ _) (no′ _) (no′ _) (no′ _) _ _ _ _ refl = refl
skip-complete (no′ _) (no′ _) (no′ _) (yes′ _) (yes′ rb) (yes′ sa) _ _ _ ¬recv _ =
  ⊥-elim (¬recv (rb , sa))
skip-complete (no′ _) (no′ _) (no′ _) (yes′ _) (yes′ _) (no′ _) _ _ _ _ refl = refl
skip-complete (no′ _) (no′ _) (no′ _) (yes′ _) (no′ _) (yes′ _) _ _ _ _ refl = refl
skip-complete (no′ _) (no′ _) (no′ _) (yes′ _) (no′ _) (no′ _) _ _ _ _ refl = refl
skip-complete (no′ _) (no′ _) (no′ _) (no′ _) (yes′ rb) (yes′ sa) _ _ _ ¬recv _ =
  ⊥-elim (¬recv (rb , sa))
skip-complete (no′ _) (no′ _) (no′ _) (no′ _) (yes′ _) (no′ _) _ _ _ _ refl = refl
skip-complete (no′ _) (no′ _) (no′ _) (no′ _) (no′ _) (yes′ _) _ _ _ _ refl = refl
skip-complete (no′ _) (no′ _) (no′ _) (no′ _) (no′ _) (no′ _) _ _ _ _ refl = refl

choose-complete : {r s p : Role} {cs : List Bin} {n : Bin}
  (rs : DecEq (r ≡ s)) (rp : DecEq (r ≡ p)) (sp : DecEq (s ≡ p)) →
  {m : Maybe (List Bin)} →
  ¬ (r ≡ s) → r ≡ p →
  m ≡ just cs →
  nest-choose cs ≡ just n →
  project-choice (parts-of rs rp sp) m ≡ just n
choose-complete (yes′ eq) _ _ ¬rs _ _ _ = ⊥-elim (¬rs eq)
choose-complete (no′ _) (no′ ¬rp) _ _ rp _ _ = ⊥-elim (¬rp rp)
choose-complete (no′ _) (yes′ _) _ _ _ refl nc = nc

branch-complete : {r s p : Role} {cs : List Bin} {n : Bin}
  (rs : DecEq (r ≡ s)) (rp : DecEq (r ≡ p)) (sp : DecEq (s ≡ p)) →
  {m : Maybe (List Bin)} →
  ¬ (r ≡ s) → s ≡ p →
  m ≡ just cs →
  nest-branch cs ≡ just n →
  project-choice (parts-of rs rp sp) m ≡ just n
branch-complete (yes′ eq) _ _ ¬rs _ _ _ = ⊥-elim (¬rs eq)
branch-complete (no′ _) (yes′ eq) _ ¬rs sp _ _ =
  ⊥-elim (¬rs (trans eq (sym sp)))
branch-complete (no′ _) (no′ _) (no′ ¬sp) _ sp _ _ = ⊥-elim (¬sp sp)
branch-complete (no′ _) (no′ _) (yes′ _) _ _ refl nb = nb

merge-complete : {r s p : Role} {cs : List Bin} {c : Bin}
  (rs : DecEq (r ≡ s)) (rp : DecEq (r ≡ p)) (sp : DecEq (s ≡ p)) →
  {m : Maybe (List Bin)} →
  ¬ (r ≡ s) → ¬ (r ≡ p) → ¬ (s ≡ p) →
  m ≡ just cs →
  merge-all cs ≡ just c →
  project-choice (parts-of rs rp sp) m ≡ just c
merge-complete (yes′ eq) _ _ ¬rs _ _ _ _ = ⊥-elim (¬rs eq)
merge-complete (no′ _) (yes′ eq) _ _ ¬rp _ _ _ = ⊥-elim (¬rp eq)
merge-complete (no′ _) (no′ _) (yes′ eq) _ _ ¬sp _ _ = ⊥-elim (¬sp eq)
merge-complete (no′ _) (no′ _) (no′ _) _ _ _ refl sm = sm

cons-eq : ∀ {b cs} {m : Maybe Bin} {ms : Maybe (List Bin)} →
  m ≡ just b → ms ≡ just cs → cons-m m ms ≡ just (b ∷ cs)
cons-eq refl refl = refl

mutual
  project-complete : ∀ {g r s b} → g ↾ r / s ≡ b → projectBin g r s ≡ just b
  project-complete (rend {r = r} {s = s} ¬rs) =
    end-complete (role-eq r s) ¬rs
  project-complete (rsend {a = a} {b = b} {A = A} {r = r} {s = s} ¬ab ¬rs ra sb d) =
    send-complete {A = A} (role-eq a b) (role-eq r s) (role-eq r a) (role-eq s b)
      (role-eq r b) (role-eq s a) ¬ab ¬rs ra sb (project-complete d)
  project-complete (rrecv {a = a} {b = b} {A = A} {r = r} {s = s} ¬ab ¬rs rb sa d) =
    recv-complete {A = A} (role-eq a b) (role-eq r s) (role-eq r a) (role-eq s b)
      (role-eq r b) (role-eq s a) ¬ab ¬rs rb sa (project-complete d)
  project-complete (rskip {a = a} {b = b} {A = A} {r = r} {s = s} ¬ab ¬rs ¬send ¬recv d) =
    skip-complete {A = A} (role-eq a b) (role-eq r s) (role-eq r a) (role-eq s b)
      (role-eq r b) (role-eq s a) ¬ab ¬rs ¬send ¬recv (project-complete d)
  project-complete {r = r} {s = s} (rchoose {p = chooser} ¬rs rp ap nc) =
    choose-complete (role-eq r s) (role-eq r chooser) (role-eq s chooser)
      ¬rs rp (all-complete ap) (nest-complete nc)
  project-complete {r = r} {s = s} (rbranch {p = chooser} ¬rs sp ap nb) =
    branch-complete (role-eq r s) (role-eq r chooser) (role-eq s chooser)
      ¬rs sp (all-complete ap) (nestb-complete nb)
  project-complete {r = r} {s = s} (rmerge {p = chooser} ¬rs ¬rp ¬sp ap sm) =
    merge-complete (role-eq r s) (role-eq r chooser) (role-eq s chooser)
      ¬rs ¬rp ¬sp (all-complete ap) (some-complete sm)

  all-complete : ∀ {bs r s cs} → AllP bs r s cs → projects bs r s ≡ just cs
  all-complete ap[] = refl
  all-complete (ap∷ d ds) = cons-eq (project-complete d) (all-complete ds)

------------------------------------------------------------------------
-- The other role's session is the other end.
------------------------------------------------------------------------

eqall-dual : ∀ {b xs} → EqAll b xs → EqAll (bin-dual b) (map bin-dual xs)
eqall-dual eq[] = eq[]
eqall-dual (eq∷ p rest) = eq∷ (cong bin-dual p) (eqall-dual rest)

some-dual : ∀ {b cs} → Some b cs → Some (bin-dual b) (map bin-dual cs)
some-dual (some e) = some (eqall-dual e)

nestc-dual : ∀ {cs n} → NestC cs n → NestB (map bin-dual cs) (bin-dual n)
nestc-dual nest-two = nest-two
nestc-dual (nest-more d) = nest-more (nestc-dual d)

nestb-dual : ∀ {cs n} → NestB cs n → NestC (map bin-dual cs) (bin-dual n)
nestb-dual nest-two = nest-two
nestb-dual (nest-more d) = nest-more (nestb-dual d)

flip-recv : {r s a b : Role} → ¬ (r ≡ b × s ≡ a) → ¬ (s ≡ a × r ≡ b)
flip-recv ¬p (sa , rb) = ¬p (rb , sa)

flip-send : {r s a b : Role} → ¬ (r ≡ a × s ≡ b) → ¬ (s ≡ b × r ≡ a)
flip-send ¬p (sb , ra) = ¬p (ra , sb)

mutual
  proj-dual : ∀ {g r s b} → g ↾ r / s ≡ b → g ↾ s / r ≡ bin-dual b
  proj-dual (rend ¬rs) = rend (λ eq → ¬rs (sym eq))
  proj-dual (rsend ¬ab ¬rs ra sb d) =
    rrecv ¬ab (λ eq → ¬rs (sym eq)) sb ra (proj-dual d)
  proj-dual (rrecv ¬ab ¬rs rb sa d) =
    rsend ¬ab (λ eq → ¬rs (sym eq)) sa rb (proj-dual d)
  proj-dual (rskip ¬ab ¬rs ¬send ¬recv d) =
    rskip ¬ab (λ eq → ¬rs (sym eq))
      (flip-recv ¬recv) (flip-send ¬send) (proj-dual d)
  proj-dual (rchoose ¬rs rp ap nc) =
    rbranch (λ eq → ¬rs (sym eq)) rp (all-dual ap) (nestc-dual nc)
  proj-dual (rbranch ¬rs sp ap nb) =
    rchoose (λ eq → ¬rs (sym eq)) sp (all-dual ap) (nestb-dual nb)
  proj-dual (rmerge ¬rs ¬rp ¬sp ap sm) =
    rmerge (λ eq → ¬rs (sym eq)) ¬sp ¬rp (all-dual ap) (some-dual sm)

  all-dual : ∀ {bs r s cs} → AllP bs r s cs → AllP bs s r (map bin-dual cs)
  all-dual ap[] = ap[]
  all-dual (ap∷ d ds) = ap∷ (proj-dual d) (all-dual ds)

-- For every pair of roles, the session `r` has with `s` is dual to
-- the session `s` has with `r`.
pairwise-dual : ∀ g r s S →
  project g r s ≡ just S →
  project g s r ≡ just (dual S)
pairwise-dual g r s S eq with projectBin g r s in beq
pairwise-dual g r s S () | nothing
pairwise-dual g r s .(⌊ b ⌋) refl | just b
  rewrite project-complete (proj-dual (project-sound g r s b beq))
  = cong just (⌊-dual⌋ b)

------------------------------------------------------------------------
-- Computed projections. A chooser on the channel always has a
-- choice, even when the arms agree. A role off the choice keeps the
-- arm only when the arms agree. An untold disagreement is refused.
------------------------------------------------------------------------

pingG : GType
pingG = comm (role "a") (role "b") "ping" unit endG

ping-send : project pingG (role "a") (role "b") ≡ just (send unit end)
ping-send = refl

ping-recv : project pingG (role "b") (role "a") ≡ just (recv unit end)
ping-recv = refl

ping-off : project pingG (role "c") (role "a") ≡ just end
ping-off = refl

ping-self : project pingG (role "a") (role "a") ≡ nothing
ping-self = refl

ping-ends : project pingG (role "b") (role "a") ≡ just (dual (send unit end))
ping-ends = pairwise-dual pingG (role "a") (role "b") (send unit end) ping-send

selfG : GType
selfG = comm (role "a") (role "a") "x" unit endG

self-ab : project selfG (role "a") (role "b") ≡ nothing
self-ab = refl

armG : GType
armG =
  choice (role "a")
    (("left" , endG) ∷
     ("right" , comm (role "a") (role "b") "x" unit endG) ∷ [])

arm-ab : project armG (role "a") (role "b") ≡ just (choose end (send unit end))
arm-ab = refl

arm-ba : project armG (role "b") (role "a") ≡ just (branch end (recv unit end))
arm-ba = refl

same-arm : GType
same-arm =
  choice (role "a")
    (("go" , comm (role "b") (role "c") "go" unit endG) ∷
     ("stop" , comm (role "b") (role "c") "stop" unit endG) ∷ [])

same-bc : project same-arm (role "b") (role "c") ≡ just (send unit end)
same-bc = refl

same-ab : project same-arm (role "a") (role "b") ≡ just (choose end end)
same-ab = refl

untold : GType
untold =
  choice (role "coordinator")
    (("commit" , comm (role "alice") (role "bob") "go" unit endG) ∷
     ("abort" , comm (role "bob") (role "alice") "stop" unit endG) ∷ [])

untold-ab : project untold (role "alice") (role "bob") ≡ nothing
untold-ab = refl

one-branch : GType
one-branch = choice (role "a") (("only" , endG) ∷ [])

one-ab : project one-branch (role "a") (role "b") ≡ nothing
one-ab = refl

three : GType
three =
  choice (role "a")
    (("l" , endG) ∷ ("m" , endG) ∷
     ("r" , comm (role "a") (role "b") "z" unit endG) ∷ [])

three-ab : project three (role "a") (role "b") ≡
  just (choose end (choose end (send unit end)))
three-ab = refl

msg : Role → Role → String → GType → GType
msg x y ℓ g = comm x y ℓ unit g

C : Role
C = role "coordinator"

Al : Role
Al = role "alice"

Bo : Role
Bo = role "bob"

tpc : GType
tpc =
  msg C Al "prepare"
  (msg C Bo "prepare"
  (msg Al C "vote"
  (msg Bo C "vote"
  (choice C
    (("commit" , msg C Al "commit" (msg C Bo "commit" endG)) ∷
     ("abort" , msg C Al "abort" (msg C Bo "abort" endG)) ∷ [])))))

tpc-ca : project tpc C Al ≡
  just (send unit (recv unit (choose (send unit end) (send unit end))))
tpc-ca = refl

tpc-ac : project tpc Al C ≡
  just (recv unit (send unit (branch (recv unit end) (recv unit end))))
tpc-ac = refl

tpc-ab : project tpc Al Bo ≡ just end
tpc-ab = refl

tpc-dual : project tpc Al C ≡
  just (dual (send unit (recv unit (choose (send unit end) (send unit end)))))
tpc-dual = pairwise-dual tpc C Al _ tpc-ca

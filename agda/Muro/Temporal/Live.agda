------------------------------------------------------------------------
-- Liveness. `eventually` and `leads_to` are decided by a worklist on
-- the finite region where the goal fails.
--
-- A configuration is removed when it has no successor left in the
-- region. Removing it deletes every edge into it, which is the
-- decrement, and the queue is exactly the configurations whose
-- surviving successor list is empty. What remains is `Z`. The measure
-- is the length of the surviving list. A final configuration stutters,
-- so it survives. There is no fuel.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Live where

open import Data.Bool.Base using (Bool; true; false; not; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; _<_; s≤s)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Nat.Properties using (≤-refl; m≤n⇒m≤1+n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; ∃-syntax)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; subst; inspect; [_])
open import Relation.Nullary.Decidable.Core using (Dec)
  renaming (yes to yesD; no to noD)

open import Muro.AsyncRec
  using ( Graph; RConf; Act; AWait; ABad; AGo
        ; reactL; reactR; l2rOf; r2lOf; halted
        ; conf≟; elemB; init
        )
open import Muro.Temporal
  using ( Who; lside; rside; fin
        ; Step; stepL; stepR; finish
        ; Path; head; tail
        ; IsRun; step; rest
        ; StateProp
        ; ⟦_⟧
        ; Formula; always; eventually; leadsTo
        ; Globally; now; later
        ; Eventually; hereE; thereE
        ; Holds; Satisfies
        ; Cex; lasso
        ; Answer; yes; no
        ; edges; isFinalB; fromL; fromR; stutter; stutterB
        ; emptyQ
        )

¬_ : Set → Set
¬ A = A → ⊥

true≢false : true ≡ false → ⊥
true≢false ()

------------------------------------------------------------------------
-- Where a configuration sits, so deleting it shortens the list.
------------------------------------------------------------------------

data Mem (c : RConf) : List RConf → Set where
  m-here : ∀ {x xs} → c ≡ x → Mem c (x ∷ xs)
  m-there : ∀ {x xs} → Mem c xs → Mem c (x ∷ xs)

deleteP : ∀ {c xs} → Mem c xs → List RConf
deleteP (m-here {xs = xs} _) = xs
deleteP (m-there {x = x} m) = x ∷ deleteP m

del-< : ∀ {c xs} (m : Mem c xs) → length (deleteP m) < length xs
del-< (m-here {xs = xs} _) = ≤-refl
del-< (m-there m) = s≤s (del-< m)

------------------------------------------------------------------------
-- One successor list per configuration. An edge is kept when its
-- target is still in the region, duplicates and all.
------------------------------------------------------------------------

-- A boolean filter with no `with`. The bool is an argument of `consB`,
-- so a proof can match it without abstracting `edges`.
consB : {A : Set} → Bool → A → List A → List A
consB true x xs = x ∷ xs
consB false _ xs = xs

filt : {A : Set} → (A → Bool) → List A → List A
filt _ [] = []
filt p (x ∷ xs) = consB (p x) x (filt p xs)

outs : Graph → List RConf → RConf → List (Who × RConf)
outs g S c = filt (λ wd → elemB (proj₂ wd) S) (edges g c)

raise : ∀ {c cs} {P : RConf → Set} →
       Maybe (Σ RConf (λ d → Mem d cs × P d)) →
       Maybe (Σ RConf (λ d → Mem d (c ∷ cs) × P d))
raise nothing = nothing
raise (just (d , m , p)) = just (d , m-there m , p)

-- Emptiness of a successor list is decided by matching the list as an
-- argument. The proof is an equality, never an inversion of `filter`.
neCons : ∀ {A : Set} {x : A} {xs : List A} → [] ≡ x ∷ xs → ⊥
neCons ()

nonempty : ∀ {A : Set} (xs : List A) → xs ≢ [] → Σ A (λ y → Any (_≡_ y) xs)
nonempty [] np = ⊥-elim (np refl)
nonempty (x ∷ xs) _ = x , here refl

zero? : (g : Graph) (S : List RConf) (c : RConf) → Dec (outs g S c ≡ [])
zero? g S c = classify (outs g S c) refl
  where
  classify : (zs : List (Who × RConf)) → outs g S c ≡ zs → Dec (outs g S c ≡ [])
  classify [] eq = yesD eq
  classify (_ ∷ _) eq = noD (λ p → neCons (trans (sym p) eq))

just≢ : ∀ {A : Set} {x : A} → just x ≡ nothing → ⊥
just≢ ()

-- `dispatch` takes the decision as an argument, so the empty case is
-- the constructor `yesD` and a pop is `()`. Nothing inverts `edges`.
mutual
  dispatch : (g : Graph) (S : List RConf) (c : RConf) (cs : List RConf) →
             Dec (outs g S c ≡ []) →
             Maybe (Σ RConf (λ d → Mem d (c ∷ cs) × outs g S d ≡ []))
  dispatch g S c cs (yesD eq) = just (c , m-here refl , eq)
  dispatch g S c cs (noD _) = raise (firstZero g S cs)

  firstZero : (g : Graph) (S cs : List RConf) →
              Maybe (Σ RConf (λ c → Mem c cs × outs g S c ≡ []))
  firstZero g S [] = nothing
  firstZero g S (c ∷ cs) = dispatch g S c cs (zero? g S c)

-- Every survivor has a successor edge that is still a survivor.
HasOut : Graph → List RConf → Set
HasOut g S = ∀ c → Mem c S → Σ (Who × RConf) (λ wd → Any (_≡_ wd) (outs g S c))

allNext : ∀ g S cs → firstZero g S cs ≡ nothing →
          ∀ c → Mem c cs → Σ (Who × RConf) (λ wd → Any (_≡_ wd) (outs g S c))
allNext g S [] eq c ()
allNext g S (c₀ ∷ cs) eq c m = onDec (zero? g S c₀) eq c m
  where
  -- `raise m ≡ nothing` gives `m ≡ nothing` by matching `m`, which is
  -- an argument, so `firstZero` is not inverted.
  peel : (mz : Maybe (Σ RConf (λ d → Mem d cs × outs g S d ≡ []))) →
         firstZero g S cs ≡ mz →
         raise (firstZero g S cs) ≡ nothing →
         firstZero g S cs ≡ nothing
  peel nothing q _ = q
  peel (just _) q r = ⊥-elim (just≢ (subst (λ z → raise z ≡ nothing) q r))
  onDec : (d : Dec (outs g S c₀ ≡ [])) →
          dispatch g S c₀ cs d ≡ nothing →
          ∀ c → Mem c (c₀ ∷ cs) →
          Σ (Who × RConf) (λ wd → Any (_≡_ wd) (outs g S c))
  onDec (yesD _) () _ _
  onDec (noD np) _ c (m-here p) =
    subst (λ z → Σ (Who × RConf) (λ wd → Any (_≡_ wd) (outs g S z))) (sym p)
          (nonempty (outs g S c₀) np)
  onDec (noD _) eq′ c (m-there m′) =
    allNext g S cs (peel (firstZero g S cs) refl eq′) c m′

-- I1. The surviving count is the length of the recomputed successor
-- list. Recomputing it is the decrement: every edge into a removed
-- configuration disappears, and no count is stored that could go
-- below zero.
cnt : Graph → List RConf → RConf → ℕ
cnt g S c = length (outs g S c)

-- I1. `cnt c` is the number of edges from `c` that still land in `S`.
I1 : ∀ g S c → cnt g S c ≡ length (outs g S c)
I1 _ _ _ = refl

-- I2. `firstZero` returns nothing exactly when every successor list is
-- nonempty, and it returns the first configuration whose list is
-- empty. By `I1` that configuration has count zero. `dispatch` takes
-- the head as soon as `zero?` says the list is empty, and `Rem` records
-- that emptiness, so a pop never subtracts from a positive count.
I2-miss : ∀ g S cs → (∀ {c} → Mem c cs → outs g S c ≢ []) →
          firstZero g S cs ≡ nothing
I2-miss g S [] _ = refl
I2-miss g S (c ∷ cs) all = on (zero? g S c) refl
  where
  on : (d : Dec (outs g S c ≡ [])) → zero? g S c ≡ d →
       firstZero g S (c ∷ cs) ≡ nothing
  on (yesD eq) _ = ⊥-elim (all (m-here refl) eq)
  on (noD _) eqz rewrite eqz =
    cong raise (I2-miss g S cs (λ m → all (m-there m)))

I2-hit : ∀ g S cs → Σ RConf (λ c → Mem c cs × outs g S c ≡ []) →
         Σ RConf (λ c → Σ (Mem c cs) (λ m → Σ (outs g S c ≡ []) (λ eq →
           firstZero g S cs ≡ just (c , m , eq))))
I2-hit g S [] (_ , () , _)
I2-hit g S (c ∷ cs) (d , m-here p , zeq) with p
... | refl = on (zero? g S c) refl
  where
  on : (dec : Dec (outs g S c ≡ [])) → zero? g S c ≡ dec →
       Σ RConf (λ x → Σ (Mem x (c ∷ cs)) (λ m → Σ (outs g S x ≡ []) (λ eq →
         firstZero g S (c ∷ cs) ≡ just (x , m , eq))))
  on (yesD eq) eqz rewrite eqz = c , m-here refl , eq , refl
  on (noD np) _ = ⊥-elim (np zeq)
I2-hit g S (c ∷ cs) (d , m-there m , zeq) = on (zero? g S c) refl
  where
  on : (dec : Dec (outs g S c ≡ [])) → zero? g S c ≡ dec →
       Σ RConf (λ x → Σ (Mem x (c ∷ cs)) (λ md → Σ (outs g S x ≡ []) (λ eq →
         firstZero g S (c ∷ cs) ≡ just (x , md , eq))))
  on (yesD eq) eqz rewrite eqz = c , m-here refl , eq , refl
  on (noD _) eqz rewrite eqz =
    let x , mx , eq , hit = I2-hit g S cs (d , m , zeq)
    in x , m-there mx , eq , cong raise hit

-- `Z` is what survives, and every survivor was already in `S`.
Sub : List RConf → List RConf → Set
Sub Z S = ∀ {c} → Mem c Z → Mem c S

sub-refl : ∀ {S} → Sub S S
sub-refl m = m

del-back : ∀ {d xs c} (m : Mem d xs) → Mem c (deleteP m) → Mem c xs
del-back (m-here _) mem = m-there mem
del-back (m-there _) (m-here eq) = m-here eq
del-back (m-there m) (m-there mem) = m-there (del-back m mem)

-- The only configuration `deleteP` drops is the one the membership names.
only-gone : ∀ {c d xs} (m : Mem d xs) → Mem c xs → ¬ Mem c (deleteP m) → c ≡ d
only-gone (m-here eq) (m-here eqc) _ = trans eqc (sym eq)
only-gone (m-here _) (m-there mem) absent = ⊥-elim (absent mem)
only-gone (m-there _) (m-here eqc) absent = ⊥-elim (absent (m-here eqc))
only-gone (m-there m) (m-there mem) absent =
  only-gone m mem (λ z → absent (m-there z))

-- How `prune` reached `Z`. Each pop records that the configuration had
-- no surviving successor, which is the decrement and the no-underflow
-- fact: the edge list was already empty, so nothing is subtracted
-- below zero.
data Rem (g : Graph) : List RConf → List RConf → Set where
  r-end : ∀ {S} → HasOut g S → Rem g S S
  r-pop : ∀ {S Z c} (m : Mem c S) → outs g S c ≡ [] →
          Rem g (deleteP m) Z → Rem g S Z

-- `died` is the removal order, earliest first. `Z` is what survives.
prune : (g : Graph) (S : List RConf) → Acc _<_ (length S) →
        Σ (List RConf) (λ died →
          Σ (List RConf) (λ Z → HasOut g Z × Sub Z S × Rem g S Z))
prune g S (acc rec) = onHit (firstZero g S S) refl (acc rec)
  where
  onHit : (hit : Maybe (Σ RConf (λ c → Mem c S × outs g S c ≡ []))) →
          firstZero g S S ≡ hit → Acc _<_ (length S) →
          Σ (List RConf) (λ died →
            Σ (List RConf) (λ Z → HasOut g Z × Sub Z S × Rem g S Z))
  onHit nothing eq _ =
    [] , S , allNext g S S eq , sub-refl , r-end (allNext g S S eq)
  onHit (just (c , m , oeq)) eq (acc rec) =
    let died , Z , ho , sub , rem = prune g (deleteP m) (rec (del-< m))
    in (c ∷ died) , Z , ho , (λ mem → del-back m (sub mem)) , r-pop m oeq rem

------------------------------------------------------------------------
-- An edge of `edges` is a step. The stutter is the final case.
------------------------------------------------------------------------

any-++ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
         Any P (xs ++ ys) → Any P xs ⊎ Any P ys
any-++ [] ys mem = inj₂ mem
any-++ (x ∷ xs) ys (here p) = inj₁ (here p)
any-++ (x ∷ xs) ys (there mem) with any-++ xs ys mem
... | inj₁ a = inj₁ (there a)
... | inj₂ b = inj₂ b

-- Membership in the right summand is membership in the concatenation.
skip++ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
         Any P ys → Any P (xs ++ ys)
skip++ [] ys mem = mem
skip++ (_ ∷ xs) ys mem = there (skip++ xs ys mem)

-- `isFinalB` is true exactly when both queues are empty and both
-- blocks are halted. The three `refl`s are the bits `finish` carries.
bits : ∀ {g c} → l2rOf c ≡ [] → r2lOf c ≡ [] → halted g c ≡ true →
       isFinalB g c ≡ true
bits eqL eqR eqH rewrite eqL | eqR | eqH = refl

-- Every step is one of the edges, in the order `edges` lists them.
step→edge : ∀ {g c w d} → Step g c w d → Any (_≡_ (w , d)) (edges g c)
step→edge {g} {c} (stepL {d = d} eq) rewrite eq = here refl
step→edge {g} {c} (stepR {d = d} eq) rewrite eq =
  skip++ (fromL (reactL g c)) (fromR (AGo d) ++ stutter g c) (here refl)
step→edge {g} {c} (finish a b h) =
  subst (λ b′ → Any (_≡_ (fin , c))
           (fromL (reactL g c) ++ fromR (reactR g c) ++ stutterB c b′))
        (sym (bits {g} {c} a b h))
        (skip++ (fromL (reactL g c))
                (fromR (reactR g c) ++ stutterB c true)
                (skip++ (fromR (reactR g c)) (stutterB c true) (here refl)))

nilQ : ∀ {A : Set} (xs : List A) → emptyQ xs ≡ true → xs ≡ []
nilQ [] _ = refl
nilQ (_ ∷ _) ()

left-go : ∀ {g c w d} → Any (_≡_ (w , d)) (fromL (reactL g c)) →
          Step g c lside d × w ≡ lside
left-go {g} {c} {w} {d} mem = onAct (reactL g c) refl mem
  where
  onAct : (a : Act) → reactL g c ≡ a → Any (_≡_ (w , d)) (fromL a) →
          Step g c lside d × w ≡ lside
  onAct AWait _ ()
  onAct (ABad _) _ ()
  onAct (AGo e) eq (here refl) =
    subst (λ d′ → Step g c lside d′ × w ≡ lside) refl (stepL eq , refl)
  onAct (AGo _) _ (there ())

right-go : ∀ {g c w d} → Any (_≡_ (w , d)) (fromR (reactR g c)) →
           Step g c rside d × w ≡ rside
right-go {g} {c} {w} {d} mem = onAct (reactR g c) refl mem
  where
  onAct : (a : Act) → reactR g c ≡ a → Any (_≡_ (w , d)) (fromR a) →
          Step g c rside d × w ≡ rside
  onAct AWait _ ()
  onAct (ABad _) _ ()
  onAct (AGo e) eq (here refl) =
    subst (λ d′ → Step g c rside d′ × w ≡ rside) refl (stepR eq , refl)
  onAct (AGo _) _ (there ())

-- The three bits of `isFinalB` are arguments. A `false` bit makes the
-- stutter list empty, so the membership is `()`. No inversion of
-- `halted`.
fin-go : ∀ {g c w d} → Any (_≡_ (w , d)) (stutter g c) →
         (w ≡ fin × d ≡ c) ×
         (l2rOf c ≡ [] × r2lOf c ≡ [] × halted g c ≡ true)
fin-go {g} {c} {w} {d} mem =
  go (emptyQ (l2rOf c)) refl (emptyQ (r2lOf c)) refl (halted g c) refl mem
  where
  go : (a : Bool) → emptyQ (l2rOf c) ≡ a →
       (b : Bool) → emptyQ (r2lOf c) ≡ b →
       (h : Bool) → halted g c ≡ h →
       Any (_≡_ (w , d)) (stutterB c (a ∧ b ∧ h)) →
       (w ≡ fin × d ≡ c) ×
       (l2rOf c ≡ [] × r2lOf c ≡ [] × halted g c ≡ true)
  go false _ _ _ _ _ ()
  go true _ false _ _ _ ()
  go true _ true _ false _ ()
  go true eqa true eqb true eqh (here refl) =
    (refl , refl) , (nilQ (l2rOf c) eqa , nilQ (r2lOf c) eqb , eqh)
  go true _ true _ true _ (there ())

edge→step : ∀ {g c w d} → Any (_≡_ (w , d)) (edges g c) → Step g c w d
edge→step {g} {c} {w} {d} mem =
  onSide (any-++ (fromL (reactL g c)) (fromR (reactR g c) ++ stutter g c) mem)
  where
  onRight : Any (_≡_ (w , d)) (fromR (reactR g c)) ⊎
            Any (_≡_ (w , d)) (stutter g c) → Step g c w d
  onRight (inj₁ onR) =
    let s , we = right-go onR
    in subst (λ w′ → Step g c w′ d) (sym we) s
  onRight (inj₂ onF) =
    let (we , de) , bits = fin-go onF
        e1 , e2 , h = bits
        stuttered = finish e1 e2 h
        at-d = subst (λ d′ → Step g c fin d′) (sym de) stuttered
    in subst (λ w′ → Step g c w′ d) (sym we) at-d
  onSide : Any (_≡_ (w , d)) (fromL (reactL g c)) ⊎
           Any (_≡_ (w , d)) (fromR (reactR g c) ++ stutter g c) →
           Step g c w d
  onSide (inj₁ onL) =
    let s , we = left-go onL
    in subst (λ w′ → Step g c w′ d) (sym we) s
  onSide (inj₂ onRest) =
    onRight (any-++ (fromR (reactR g c)) (stutter g c) onRest)

------------------------------------------------------------------------
-- A survivor starts an infinite run that stays in `Z`. The corecursive
-- call is the tail.
------------------------------------------------------------------------

filt-true : ∀ {A : Set} (p : A → Bool) {x} (xs : List A) →
            Any (_≡_ x) (filt p xs) → p x ≡ true
filt-true p [] ()
filt-true p {x} (y ∷ xs) mem = on (p y) refl mem
  where
  on : (b : Bool) → p y ≡ b → Any (_≡_ x) (consB b y (filt p xs)) → p x ≡ true
  on true eq (here refl) = eq
  on true eq (there rest) = filt-true p xs rest
  on false eq mem′ = filt-true p xs mem′

filt⊆ : ∀ {A : Set} (p : A → Bool) {x} (xs : List A) →
        Any (_≡_ x) (filt p xs) → Any (_≡_ x) xs
filt⊆ p [] ()
filt⊆ p {x} (y ∷ xs) mem = on (p y) refl mem
  where
  on : (b : Bool) → p y ≡ b → Any (_≡_ x) (consB b y (filt p xs)) → Any (_≡_ x) (y ∷ xs)
  on true _ (here px) = here px
  on true _ (there rest) = there (filt⊆ p xs rest)
  on false _ mem′ = there (filt⊆ p xs mem′)

-- A true element survives the filter.
filt-keep : ∀ {A : Set} (p : A → Bool) {x : A} (xs : List A) →
            p x ≡ true → Any (_≡_ x) xs → Any (_≡_ x) (filt p xs)
filt-keep p [] _ ()
filt-keep p {x} (y ∷ xs) pt mem = on (p y) refl mem
  where
  on : (b : Bool) → p y ≡ b → Any (_≡_ x) (y ∷ xs) →
       Any (_≡_ x) (consB b y (filt p xs))
  on true _ (here px) = here px
  on true _ (there rest) = there (filt-keep p xs pt rest)
  on false eq (here refl) = ⊥-elim (true≢false (trans (sym pt) eq))
  on false _ (there rest) = filt-keep p xs pt rest

mem-elem : ∀ {c xs} → Mem c xs → elemB c xs ≡ true
mem-elem {c} {x ∷ xs} (m-here p) with conf≟ c x
... | yesD _ = refl
... | noD np = ⊥-elim (np p)
mem-elem {c} {x ∷ xs} (m-there m) with conf≟ c x
... | yesD _ = refl
... | noD _ = mem-elem m

find : ∀ c xs → elemB c xs ≡ true → Mem c xs
find c [] ()
find c (x ∷ xs) eq with conf≟ c x
... | yesD p = m-here p
... | noD _ = m-there (find c xs eq)

¬mem : ∀ {c xs} → elemB c xs ≡ false → ¬ Mem c xs
¬mem eq m = true≢false (trans (sym (mem-elem m)) eq)

-- An empty surviving list has no edge back into the region.
-- Abstract and fully explicit, so a caller does not invert `elemB`
-- under `edges` and does not invent a fresh region meta.
abstract
  out-miss : (g : Graph) (S : List RConf) (c d : RConf) (w : Who) →
             outs g S c ≡ [] → Step g c w d → elemB d S ≡ false
  out-miss g S c d w eq st = body (elemB d S) refl
    where
    stuck : (zs : List (Who × RConf)) → outs g S c ≡ zs →
            Any (_≡_ (w , d)) zs → outs g S c ≡ [] → ⊥
    stuck [] _ () _
    stuck (_ ∷ _) eqZ _ eq0 = ⊥-elim (neCons (trans (sym eq0) eqZ))
    body : (b : Bool) → elemB d S ≡ b → elemB d S ≡ false
    body false bq = bq
    body true bq =
      ⊥-elim (stuck (outs g S c) refl
                (filt-keep (λ wd → elemB (proj₂ wd) S) (edges g c) bq (step→edge st))
                eq)

------------------------------------------------------------------------
-- A configuration the worklist removed cannot stay in the region.
-- The argument is the removal certificate, so the recursion is
-- structural. No fuel.
------------------------------------------------------------------------

Gone : Graph → List RConf → Path → Set
Gone g S σ = ¬ Mem (head σ) S

lift-gone : ∀ {g S popped π} (m0 : Mem popped S) →
            outs g S popped ≡ [] → IsRun g π →
            Eventually (Gone g (deleteP m0)) π →
            Eventually (Gone g S) π
lift-gone {g = g} {S = S} {π = π} m0 empty rn (hereE gone) = onHead (elemB (head π) S) refl
  where
  onHead : (b : Bool) → elemB (head π) S ≡ b → Eventually (Gone g S) π
  onHead false eq = hereE (¬mem eq)
  onHead true eq =
    let eqp = only-gone m0 (find (head π) S eq) gone
        emptyH = subst (λ z → outs g S z ≡ []) (sym eqp) empty
        w = proj₁ (step {g} {π} rn)
        st = proj₂ (step {g} {π} rn)
    in thereE (hereE (¬mem (out-miss g S (head π) (head (tail π)) w emptyH st)))
lift-gone {g = g} {π = π} m0 empty rn (thereE ev) =
  thereE (lift-gone {g = g} {π = tail π} m0 empty (rest {g} {π} rn) ev)

leaves : ∀ {g S Z} → Rem g S Z →
         ∀ c → Mem c S → ¬ Mem c Z →
         ∀ π → head π ≡ c → IsRun g π →
         Eventually (Gone g S) π
leaves (r-end _) c m absent _ _ _ = ⊥-elim (absent m)
leaves {g = g} (r-pop {S = S} {c = popped} m0 empty rest) c m absent π hd rn =
  branch (elemB c (deleteP m0)) refl
  where
  branch : (b : Bool) → elemB c (deleteP m0) ≡ b → Eventually (Gone g S) π
  branch true eq =
    lift-gone m0 empty rn
      (leaves rest c (find c (deleteP m0) eq) absent π hd rn)
  branch false eq =
    let eqc = only-gone m0 m (λ mem → ¬mem eq mem)
        emptyC = subst (λ z → outs g S z ≡ []) (sym eqc) empty
        w = proj₁ (step rn)
        st = proj₂ (step rn)
        stepped = subst (λ z → Step g z w (head (tail π))) hd st
    in thereE (hereE (¬mem (out-miss g S c (head (tail π)) w emptyC stepped)))

-- The copatterns below only project a `Step`. The edge list stays in
-- `seal`, which is not unfolded under a copattern, so the graph record
-- is not split into field metas.
HasNext : Graph → List RConf → Set
HasNext g S =
  ∀ c → Mem c S →
  Σ (Who × RConf) (λ wd → Step g c (proj₁ wd) (proj₂ wd) × Mem (proj₂ wd) S)

seal1 : ∀ {g S c} → Σ (Who × RConf) (λ wd → Any (_≡_ wd) (outs g S c)) →
        Σ (Who × RConf) (λ wd → Step g c (proj₁ wd) (proj₂ wd) × Mem (proj₂ wd) S)
seal1 {g} {S} {c} (wd , onOuts) =
  wd , edge→step (filt⊆ (λ we → elemB (proj₂ we) S) (edges g c) onOuts)
     , find (proj₂ wd) S (filt-true (λ we → elemB (proj₂ we) S) (edges g c) onOuts)

seal : ∀ {g S} → HasOut g S → HasNext g S
seal ho c m = seal1 (ho c m)

zpath : (g : Graph) (Z : List RConf) (hn : HasNext g Z)
        (c : RConf) → Mem c Z → Path
head (zpath g Z hn c m) = c
tail (zpath g Z hn c m) =
  zpath g Z hn (proj₂ (proj₁ (hn c m))) (proj₂ (proj₂ (hn c m)))

zrun : (g : Graph) (Z : List RConf) (hn : HasNext g Z)
       (c : RConf) (m : Mem c Z) → IsRun g (zpath g Z hn c m)
step (zrun g Z hn c m) = proj₁ (proj₁ (hn c m)) , proj₁ (proj₂ (hn c m))
rest (zrun g Z hn c m) =
  zrun g Z hn (proj₂ (proj₁ (hn c m))) (proj₂ (proj₂ (hn c m)))

------------------------------------------------------------------------
-- Boolean membership lemmas used by the measure and the region.
------------------------------------------------------------------------

elem-hit : ∀ {y x xs} → x ≡ y → elemB y (x ∷ xs) ≡ true
elem-hit {y} {x} eq with conf≟ y x
... | yesD _ = refl
... | noD np = ⊥-elim (np (sym eq))

-- The lasso measure. Comparing two configurations is done once, in
-- `split`, and the branches of `unseen-drop` match the resulting
-- constructors. They do not take a second look at `conf≟`.
------------------------------------------------------------------------

mutual
  unseen : List RConf → List RConf → ℕ
  unseen [] seen = zero
  unseen (c ∷ Z) seen = ucons (elemB c seen) Z seen

  ucons : Bool → List RConf → List RConf → ℕ
  ucons true Z seen = unseen Z seen
  ucons false Z seen = suc (unseen Z seen)

same-shrink : ∀ Z seen c (b : Bool) → elemB c seen ≡ b →
            unseen Z (c ∷ seen) ≤ unseen Z seen →
            unseen Z (c ∷ seen) ≤ ucons b Z seen
same-shrink Z seen c true _ ih = ih
same-shrink Z seen c false _ ih = m≤n⇒m≤1+n ih

mutual
  both-shrink : ∀ Z seen x (b : Bool) → ucons b Z (x ∷ seen) ≤ ucons b Z seen
  both-shrink Z seen x true = unseen-shrink Z seen x
  both-shrink Z seen x false = s≤s (unseen-shrink Z seen x)

  unseen-shrink : ∀ Z seen x → unseen Z (x ∷ seen) ≤ unseen Z seen
  unseen-shrink [] _ _ = ≤-refl
  unseen-shrink (c ∷ Z) seen x with conf≟ c x
  ... | yesD refl = same-shrink Z seen c (elemB c seen) refl (unseen-shrink Z seen c)
  ... | noD _ = both-shrink Z seen x (elemB c seen)

-- Diagonal membership stays inside this helper. The caller is under a
-- `with` on `conf≟`, and a second `with` there does not unify.
diag : ∀ x Z seen → elemB x seen ≡ false →
       unseen (x ∷ Z) (x ∷ seen) < unseen (x ∷ Z) seen
diag x Z seen fr =
  subst (λ a → ucons a Z (x ∷ seen) < ucons (elemB x seen) Z seen)
        (sym (elem-hit {y = x} {x = x} {xs = seen} refl))
        (subst (λ b → ucons true Z (x ∷ seen) < ucons b Z seen) (sym fr)
               (s≤s (unseen-shrink Z seen x)))

-- One comparison, in two functions so the `with`s are not nested. In
-- the distinct case both booleans are the membership of `x` in `seen`.
data Split (c x : RConf) (Z seen : List RConf) (fr : elemB c seen ≡ false) : Set where
  sp-yes : c ≡ x → Split c x Z seen fr
  sp-no : (a b : Bool) → elemB c Z ≡ true →
          elemB x (c ∷ seen) ≡ a → elemB x seen ≡ b → a ≡ b →
          Split c x Z seen fr

skip-eq : ∀ {x c xs} → x ≢ c → elemB x (c ∷ xs) ≡ elemB x xs
skip-eq {x} {c} {xs} np with conf≟ x c
... | yesD p = ⊥-elim (np p)
... | noD _ = refl

≢-sym : ∀ {A : Set} {x y : A} → x ≢ y → y ≢ x
≢-sym np eq = np (sym eq)

differ : ∀ c x Z seen → c ≢ x → elemB c Z ≡ true →
         (fr : elemB c seen ≡ false) → Split c x Z seen fr
differ c x Z seen np el fr =
  sp-no (elemB x (c ∷ seen)) (elemB x seen) el refl refl (skip-eq (≢-sym np))

split : ∀ c x Z seen → elemB c (x ∷ Z) ≡ true →
        (fr : elemB c seen ≡ false) → Split c x Z seen fr
split c x Z seen el fr with conf≟ c x
... | yesD p = sp-yes p
... | noD np = differ c x Z seen np el fr

unseen-drop : ∀ c Z seen → elemB c Z ≡ true → elemB c seen ≡ false →
              unseen Z (c ∷ seen) < unseen Z seen
unseen-drop c [] _ () _
unseen-drop c (x ∷ Z) seen el fresh = on (split c x Z seen el fresh)
  where
  on : Split c x Z seen fresh →
       unseen (x ∷ Z) (c ∷ seen) < unseen (x ∷ Z) seen
  on (sp-yes refl) = diag x Z seen fresh
  on (sp-no true true elZ ea eb _) =
    subst (λ a → ucons a Z (c ∷ seen) < ucons (elemB x seen) Z seen) (sym ea)
    (subst (λ b → ucons true Z (c ∷ seen) < ucons b Z seen) (sym eb)
           (unseen-drop c Z seen elZ fresh))
  on (sp-no false false elZ ea eb _) =
    subst (λ a → ucons a Z (c ∷ seen) < ucons (elemB x seen) Z seen) (sym ea)
    (subst (λ b → ucons false Z (c ∷ seen) < ucons b Z seen) (sym eb)
           (s≤s (unseen-drop c Z seen elZ fresh)))
  on (sp-no false true _ _ _ ())
  on (sp-no true false _ _ _ ())

------------------------------------------------------------------------
-- A finite path, stored oldest step first, and the cycle it closes.
------------------------------------------------------------------------

data Chain (g : Graph) : RConf → List (Who × RConf) → Set where
  c-nil : ∀ {c} → Chain g c []
  c-cons : ∀ {c w d xs} → Step g c w d → Chain g d xs →
           Chain g c ((w , d) ∷ xs)

End : ∀ {g a xs} → Chain g a xs → RConf
End {a = a} c-nil = a
End (c-cons {d = d} _ rest) = End rest

snocC : ∀ {g a xs w d} (ch : Chain g a xs) → Step g (End ch) w d →
        Chain g a (xs ++ ((w , d) ∷ []))
snocC c-nil st = c-cons st c-nil
snocC (c-cons s rest) st = c-cons s (snocC rest st)

end-snoc : ∀ {g a xs w d} (ch : Chain g a xs) (st : Step g (End ch) w d) →
           End (snocC ch st) ≡ d
end-snoc c-nil _ = refl
end-snoc (c-cons _ rest) st = end-snoc rest st

-- A finite chain, then an infinite run. The corecursive call is the
-- tail of a cons, so the definition is guarded.
follow : ∀ {g a xs} → Chain g a xs → Path → Path
head (follow c-nil π) = head π
tail (follow c-nil π) = tail π
head (follow (c-cons {c = a} _ _) _) = a
tail (follow (c-cons _ rest) π) = follow rest π

follow-head : ∀ {g a c xs} (ch : Chain g a xs) (π : Path) →
              End ch ≡ c → head π ≡ c → head (follow ch π) ≡ a
follow-head c-nil π end hd = trans hd (sym end)
follow-head (c-cons _ _) _ _ _ = refl

follow-run : ∀ {g a xs} (ch : Chain g a xs) (π : Path) →
             End ch ≡ head π → IsRun g π → IsRun g (follow ch π)
step (follow-run c-nil π end r) = step r
rest (follow-run c-nil π end r) = rest r
step (follow-run (c-cons {c = a} {w = w} {d = d} st rest) π end r) =
  w , subst (λ z → Step _ a w z) (sym (follow-head rest π end refl)) st
rest (follow-run (c-cons _ rest) π end r) = follow-run rest π end r

-- Split when the current configuration is the repeated one. The prefix
-- is the stem; the remainder is the cycle.
cut : ∀ {g a xs} (l : RConf) → Chain g a xs →
      List (Who × RConf) × List (Who × RConf)
cut {a = a} {xs = xs} l ch with conf≟ l a
... | yesD _ = [] , xs
... | noD _ with ch
... | c-nil = [] , []
... | c-cons {w = w} {d = d} _ rest =
  let s , lp = cut l rest
  in ((w , d) ∷ s) , lp

-- Walk the first surviving successor until a configuration repeats.
-- The measure is the part of `Z` not yet on the walk.
walk : (g : Graph) (Z : List RConf) (hn : HasNext g Z)
       (c : RConf) (m : Mem c Z) (seen : List RConf)
       {a : RConf} {xs : List (Who × RConf)} (ch : Chain g a xs) →
       End ch ≡ c → Acc _<_ (unseen Z seen) →
       List (Who × RConf) × List (Who × RConf)
walk g Z hn c m seen ch end (acc rec) = onSeen (elemB c seen) refl
  where
  onSeen : (b : Bool) → elemB c seen ≡ b →
           List (Who × RConf) × List (Who × RConf)
  onSeen true _ = cut c ch
  onSeen false fr =
    let wd = proj₁ (hn c m)
        st = proj₁ (proj₂ (hn c m))
        md = proj₂ (proj₂ (hn c m))
        w = proj₁ wd
        d = proj₂ wd
        stepped = subst (λ z → Step g z w d) (sym end) st
    in walk g Z hn d md (c ∷ seen) (snocC ch stepped) (end-snoc ch stepped)
         (rec (unseen-drop c Z seen (mem-elem m) fr))

------------------------------------------------------------------------
-- The same walk, keeping the chain. `Pref` says the repeated
-- configuration already occurs on it, with a nonempty suffix back to
-- the present end. `Cover` says every configuration on the chain is
-- still in the region.
------------------------------------------------------------------------

data Pref {g : Graph} (l : RConf) :
          {a : RConf} {xs : List (Who × RConf)} → Chain g a xs → Set where
  pf-here : ∀ {w d ys} {st : Step g l w d} {rest : Chain g d ys} →
            Pref l (c-cons st rest)
  pf-there : ∀ {a w d xs} {st : Step g a w d} {rest : Chain g d xs} →
             Pref l rest → Pref l (c-cons st rest)

data Cover (Z : List RConf) {g : Graph} :
           {a : RConf} {xs : List (Who × RConf)} → Chain g a xs → Set where
  cv-nil : ∀ {c} → Mem c Z → Cover Z (c-nil {c = c})
  cv-cons : ∀ {a w d xs} {st : Step g a w d} {rest : Chain g d xs} →
            Mem a Z → Cover Z rest → Cover Z (c-cons st rest)

cover-head : ∀ {g a xs Z} {ch : Chain g a xs} → Cover Z ch → Mem a Z
cover-head (cv-nil m) = m
cover-head (cv-cons m _) = m

cover-snoc : ∀ {g a xs Z w d} (ch : Chain g a xs) (st : Step g (End ch) w d) →
             Cover Z ch → Mem d Z → Cover Z (snocC ch st)
cover-snoc c-nil st (cv-nil m) md = cv-cons m (cv-nil md)
cover-snoc (c-cons s rest) st (cv-cons m cr) md =
  cv-cons m (cover-snoc rest st cr md)

pref-end : ∀ {g a xs w d} (ch : Chain g a xs) (st : Step g (End ch) w d) →
           Pref (End ch) (snocC ch st)
pref-end c-nil st = pf-here
pref-end (c-cons s rest) st = pf-there (pref-end rest st)

pref-mono : ∀ {g a xs l w d} {ch : Chain g a xs} (st : Step g (End ch) w d) →
            Pref l ch → Pref l (snocC ch st)
pref-mono st pf-here = pf-here
pref-mono st (pf-there p) = pf-there (pref-mono st p)

data Bag {g : Graph} {a : RConf} {xs : List (Who × RConf)}
         (ch : Chain g a xs) : List RConf → Set where
  bnil : Bag ch []
  bcons : ∀ {c cs} → Pref c ch → Bag ch cs → Bag ch (c ∷ cs)

bag-mono : ∀ {g a xs w d seen} {ch : Chain g a xs}
           (st : Step g (End ch) w d) →
           Bag ch seen → Bag (snocC ch st) seen
bag-mono st bnil = bnil
bag-mono st (bcons p bg) = bcons (pref-mono st p) (bag-mono st bg)

bag-add : ∀ {g a xs w d seen} (ch : Chain g a xs) (st : Step g (End ch) w d) →
          Bag ch seen → Bag (snocC ch st) (End ch ∷ seen)
bag-add ch st bg = bcons (pref-end ch st) (bag-mono st bg)

bag-mem : ∀ {g a xs c seen} {ch : Chain g a xs} →
          Mem c seen → Bag ch seen → Pref c ch
bag-mem (m-here p) (bcons pr _) = subst (λ z → Pref z _) (sym p) pr
bag-mem (m-there m) (bcons _ bg) = bag-mem m bg

record Cycle (g : Graph) (Z : List RConf) (a l : RConf) : Set where
  constructor mkCy
  field
    stem loop : List (Who × RConf)
    chS : Chain g a stem
    eS : End chS ≡ l
    chL : Chain g l loop
    eL : End chL ≡ l
    ne : Σ (Who × RConf) (λ wd → Σ (List (Who × RConf)) (λ ys → loop ≡ wd ∷ ys))
    cvS : Cover Z chS
    cvL : Cover Z chL

-- The first mark is the loop entry. The suffix of the chain is the
-- cycle, and it is nonempty because the mark was stored when the
-- configuration was left.
cutC : ∀ {g a xs Z} (l : RConf) (ch : Chain g a xs) →
       End ch ≡ l → Pref l ch → Cover Z ch → Cycle g Z a l
cutC l c-nil _ () _
cutC {xs = (w , d) ∷ ys} l (c-cons st rest) end pf-here cv =
  mkCy [] ((w , d) ∷ ys) c-nil refl (c-cons st rest) end
       ((w , d) , ys , refl) (cv-nil (cover-head cv)) cv
cutC {Z = Z} l (c-cons {w = w} {d = d} st rest) end (pf-there pr) (cv-cons m cr) =
  let s = cutC l rest end pr cr
  in mkCy ((w , d) ∷ Cycle.stem s) (Cycle.loop s)
          (c-cons st (Cycle.chS s)) (Cycle.eS s)
          (Cycle.chL s) (Cycle.eL s) (Cycle.ne s)
          (cv-cons m (Cycle.cvS s)) (Cycle.cvL s)

Tour : Graph → List RConf → RConf → Set
Tour g Z a = Σ RConf (λ l → Cycle g Z a l)

walkC : (g : Graph) (Z : List RConf) (hn : HasNext g Z)
        (c : RConf) (m : Mem c Z) (seen : List RConf)
        {a : RConf} {xs : List (Who × RConf)} (ch : Chain g a xs) →
        End ch ≡ c → Cover Z ch → Bag ch seen →
        Acc _<_ (unseen Z seen) → Tour g Z a
walkC g Z hn c m seen {a = a} ch end cv bg (acc rec) = onSeen (elemB c seen) refl
  where
  onSeen : (b : Bool) → elemB c seen ≡ b → Tour g Z a
  onSeen true eq = c , cutC c ch end (bag-mem (find c seen eq) bg) cv
  onSeen false fr =
    let wd = proj₁ (hn c m)
        st = proj₁ (proj₂ (hn c m))
        md = proj₂ (proj₂ (hn c m))
        w = proj₁ wd
        d = proj₂ wd
        stepped = subst (λ z → Step g z w d) (sym end) st
        ch′ = snocC ch stepped
        bg′ = subst (λ z → Bag ch′ (z ∷ seen)) end (bag-add ch stepped bg)
    in walkC g Z hn d md (c ∷ seen) ch′ (end-snoc ch stepped)
         (cover-snoc ch stepped cv md) bg′
         (rec (unseen-drop c Z seen (mem-elem m) fr))

tour-of : (g : Graph) (Z : List RConf) (ho : HasOut g Z) (c : RConf) (m : Mem c Z) →
          Tour g Z c
tour-of g Z ho c m =
  walkC g Z (seal ho) c m [] (c-nil {c = c}) refl (cv-nil m) bnil
        (<-wellFounded-fast (unseen Z []))

-- Play a nonempty cycle forever. `suf` is the part still ahead. When it
-- runs out, the first step of `full` is taken again. Both chains end at
-- the entry, so the configuration the suffix runs out on is that entry.
replay : ∀ {g l a ys xs} (suf : Chain g a ys) → End suf ≡ l →
         (full : Chain g l xs) → End full ≡ l →
         Σ (Who × RConf) (λ wd → Σ (List (Who × RConf)) (λ zs → xs ≡ wd ∷ zs)) →
         Path
head (replay {a = a} _ _ _ _ _) = a
tail (replay (c-cons _ rest) endS full endF ne) = replay rest endS full endF ne
tail (replay c-nil endS (c-cons st rest) endF ne) =
  replay rest endF (c-cons st rest) endF ne
tail (replay c-nil _ c-nil _ (_ , _ , ()))

replay-run : ∀ {g l a ys xs} (suf : Chain g a ys) (endS : End suf ≡ l)
             (full : Chain g l xs) (endF : End full ≡ l)
             (ne : Σ (Who × RConf) (λ wd → Σ (List (Who × RConf)) (λ zs → xs ≡ wd ∷ zs))) →
             IsRun g (replay suf endS full endF ne)
step (replay-run (c-cons {w = w} st rest) endS full endF ne) = w , st
rest (replay-run (c-cons _ rest) endS full endF ne) =
  replay-run rest endS full endF ne
step (replay-run {g = g} c-nil endS (c-cons {w = w} {d = d} st rest) endF ne) =
  w , subst (λ z → Step g z w d) (sym endS) st
rest (replay-run c-nil endS (c-cons st rest) endF ne) =
  replay-run rest endF (c-cons st rest) endF ne
step (replay-run c-nil _ c-nil _ (_ , _ , ()))
rest (replay-run c-nil _ c-nil _ (_ , _ , ()))

spin : ∀ {g l xs} (ch : Chain g l xs) (end : End ch ≡ l)
       (ne : Σ (Who × RConf) (λ wd → Σ (List (Who × RConf)) (λ zs → xs ≡ wd ∷ zs))) →
       Path
spin ch end ne = replay ch end ch end ne

spin-run : ∀ {g l xs} (ch : Chain g l xs) (end : End ch ≡ l)
           (ne : Σ (Who × RConf) (λ wd → Σ (List (Who × RConf)) (λ zs → xs ≡ wd ∷ zs))) →
           IsRun g (spin ch end ne)
spin-run ch end ne = replay-run ch end ch end ne

-- The recorded stem, then the recorded cycle. The head is the stem's start.
open-path : ∀ {g Z a l} → Cycle g Z a l → Path
open-path cy =
  follow (Cycle.chS cy) (spin (Cycle.chL cy) (Cycle.eL cy) (Cycle.ne cy))

open-head : ∀ {g Z a l} (cy : Cycle g Z a l) → head (open-path cy) ≡ a
open-head cy =
  follow-head (Cycle.chS cy) (spin (Cycle.chL cy) (Cycle.eL cy) (Cycle.ne cy))
    (Cycle.eS cy) refl

open-run : ∀ {g Z a l} (cy : Cycle g Z a l) → IsRun g (open-path cy)
open-run cy =
  follow-run (Cycle.chS cy) (spin (Cycle.chL cy) (Cycle.eL cy) (Cycle.ne cy))
    (Cycle.eS cy) (spin-run (Cycle.chL cy) (Cycle.eL cy) (Cycle.ne cy))

------------------------------------------------------------------------
-- A run that stays in `Z` never meets a proposition that fails on `Z`.
------------------------------------------------------------------------

Fails : Graph → StateProp → Path → Set
Fails g p σ = ⟦ g ⟧ p (head σ) ≡ false

HoldsP : Graph → StateProp → Path → Set
HoldsP g p σ = ⟦ g ⟧ p (head σ) ≡ true

stay-out : ∀ {g p Z} (hn : HasNext g Z) (c : RConf) (m : Mem c Z) →
           (∀ {x} → Mem x Z → ⟦ g ⟧ p x ≡ false) →
           Globally (Fails g p) (zpath g Z hn c m)
now (stay-out {g} {p} hn c m all) = all m
later (stay-out {g} {p} hn c m all) =
  stay-out {g} {p} hn (proj₂ (proj₁ (hn c m))) (proj₂ (proj₂ (hn c m))) all

no-hit : ∀ {g p π} →
         Globally (Fails g p) π →
         ¬ Eventually (HoldsP g p) π
no-hit {g} {p} {π} gl (hereE bad) =
  true≢false (trans (sym bad) (now {P = Fails g p} {π} gl))
no-hit {g} {p} {π} gl (thereE later′) =
  no-hit {g} {p} {π = tail π} (later {P = Fails g p} {π} gl) later′

ev-denied : ∀ {g p Z} (hn : HasNext g Z) →
            Mem (init g) Z →
            (∀ {x} → Mem x Z → ⟦ g ⟧ p x ≡ false) →
            ¬ Satisfies g (eventually p)
ev-denied {g} {p} {Z} hn m all sat =
  no-hit {g} {p} (stay-out {g} {p} {Z} hn (init g) m all)
    (sat (zpath g Z hn (init g) m) refl (zrun g Z hn (init g) m))

cover-rest : ∀ {g Z a w d xs} {st : Step g a w d} {rest : Chain g d xs} →
             Cover Z (c-cons st rest) → Cover Z rest
cover-rest (cv-cons _ cr) = cr

-- Every configuration of the recorded cycle is in `Z`, and so is every
-- configuration of the stem in front of it.
replay-miss : ∀ {g p l a ys xs Z}
              (suf : Chain g a ys) (endS : End suf ≡ l)
              (full : Chain g l xs) (endF : End full ≡ l)
              (ne : Σ (Who × RConf) (λ wd → Σ (List (Who × RConf)) (λ zs → xs ≡ wd ∷ zs))) →
              Cover Z suf → Cover Z full →
              (∀ {x} → Mem x Z → ⟦ g ⟧ p x ≡ false) →
              Globally (Fails g p) (replay suf endS full endF ne)
now (replay-miss {g = g} {p = p} suf _ _ _ _ cvS _ all) = all (cover-head cvS)
later (replay-miss {g = g} {p = p} (c-cons _ rest) endS full endF ne (cv-cons _ cr) cvF all) =
  replay-miss {g} {p} rest endS full endF ne cr cvF all
later (replay-miss {g = g} {p = p} c-nil _ (c-cons st rest) endF ne _ cvF all) =
  replay-miss {g} {p} rest endF (c-cons st rest) endF ne (cover-rest cvF) cvF all
later (replay-miss c-nil _ c-nil _ (_ , _ , ()) _ _ _)

spin-miss : ∀ {g p l xs Z} (ch : Chain g l xs) (end : End ch ≡ l)
            (ne : Σ (Who × RConf) (λ wd → Σ (List (Who × RConf)) (λ zs → xs ≡ wd ∷ zs))) →
            Cover Z ch →
            (∀ {x} → Mem x Z → ⟦ g ⟧ p x ≡ false) →
            Globally (Fails g p) (spin ch end ne)
spin-miss {g} {p} ch end ne cv all =
  replay-miss {g} {p} ch end ch end ne cv cv all

follow-miss : ∀ {g p a xs Z} (ch : Chain g a xs) (π : Path) →
              Cover Z ch → End ch ≡ head π →
              Globally (Fails g p) π →
              (∀ {x} → Mem x Z → ⟦ g ⟧ p x ≡ false) →
              Globally (Fails g p) (follow ch π)
now (follow-miss {g = g} {p = p} c-nil _ (cv-nil m) end _ all) =
  subst (λ z → ⟦ g ⟧ p z ≡ false) end (all m)
now (follow-miss {g = g} {p = p} (c-cons _ _) _ cv _ _ all) = all (cover-head cv)
later (follow-miss {g = g} {p = p} c-nil _ _ _ gl _) = later {P = Fails g p} gl
later (follow-miss {g = g} {p = p} (c-cons _ rest) π (cv-cons _ cr) end gl all) =
  follow-miss {g} {p} rest π cr end gl all

open-miss : ∀ {g p Z a l} (cy : Cycle g Z a l) →
            (∀ {x} → Mem x Z → ⟦ g ⟧ p x ≡ false) →
            Globally (Fails g p) (open-path cy)
open-miss {g} {p} cy all =
  follow-miss {g} {p} (Cycle.chS cy) (spin (Cycle.chL cy) (Cycle.eL cy) (Cycle.ne cy))
    (Cycle.cvS cy) (Cycle.eS cy)
    (spin-miss {g} {p} (Cycle.chL cy) (Cycle.eL cy) (Cycle.ne cy) (Cycle.cvL cy) all)
    all

------------------------------------------------------------------------
-- `eventually` fails when the start survives in the region that avoids
-- the proposition. `leads_to` fails when some state of the region has
-- the trigger.
------------------------------------------------------------------------

avoid : Graph → StateProp → List RConf → List RConf
avoid g p [] = []
avoid g p (c ∷ cs) with ⟦ g ⟧ p c
... | true = avoid g p cs
... | false = c ∷ avoid g p cs

trigger : Graph → StateProp → StateProp → List RConf → List RConf → Maybe RConf
trigger g p q Z [] = nothing
trigger g p q Z (c ∷ cs) with ⟦ g ⟧ p c
... | false = trigger g p q Z cs
... | true with elemB c Z
... | true = just c
... | false = trigger g p q Z cs

avoid-no : ∀ g p c cs → Mem c (avoid g p cs) → ⟦ g ⟧ p c ≡ false
avoid-no g p c [] ()
avoid-no g p c (x ∷ cs) m with ⟦ g ⟧ p x in eq
... | true = avoid-no g p c cs m
... | false with m
... | m-here refl = eq
... | m-there m′ = avoid-no g p c cs m′

avoid-in : ∀ g p c cs → Mem c cs → ⟦ g ⟧ p c ≡ false → Mem c (avoid g p cs)
avoid-in g p c [] () _
avoid-in g p c (x ∷ cs) m eq = onB (⟦ g ⟧ p x) refl m
  where
  onB : (b : Bool) → ⟦ g ⟧ p x ≡ b → Mem c (x ∷ cs) → Mem c (avoid g p (x ∷ cs))
  onB true bq (m-here refl) rewrite bq = ⊥-elim (true≢false eq)
  onB true bq (m-there m″) rewrite bq = avoid-in g p c cs m″ eq
  onB false bq (m-here refl) rewrite bq = m-here refl
  onB false bq (m-there m″) rewrite bq = m-there (avoid-in g p c cs m″ eq)

in-or : ∀ g p c cs → Mem c cs → ⟦ g ⟧ p c ≡ true ⊎ Mem c (avoid g p cs)
in-or g p c cs m = on (⟦ g ⟧ p c) refl
  where
  on : (b : Bool) → ⟦ g ⟧ p c ≡ b → ⟦ g ⟧ p c ≡ true ⊎ Mem c (avoid g p cs)
  on true eq = inj₁ eq
  on false eq = inj₂ (avoid-in g p c cs m eq)

hit-p : ∀ g p c cs → Mem c cs → ¬ Mem c (avoid g p cs) → ⟦ g ⟧ p c ≡ true
hit-p g p c cs m absent = on (in-or g p c cs m)
  where
  on : ⟦ g ⟧ p c ≡ true ⊎ Mem c (avoid g p cs) → ⟦ g ⟧ p c ≡ true
  on (inj₁ eq) = eq
  on (inj₂ inn) = ⊥-elim (absent inn)

region-no : ∀ {g p cs Z} → Sub Z (avoid g p cs) →
            ∀ {x} → Mem x Z → ⟦ g ⟧ p x ≡ false
region-no {g} {p} {cs} sub {x} m = avoid-no g p x cs (sub m)

-- `trigger` returns nothing exactly when no visited configuration is
-- both the trigger and a survivor.
nextT : Graph → StateProp → StateProp → List RConf → List RConf → RConf →
        Bool → Bool → Maybe RConf
nextT g p q Z cs y false _ = trigger g p q Z cs
nextT g p q Z cs y true true = just y
nextT g p q Z cs y true false = trigger g p q Z cs

trig-eq : ∀ g p q Z y cs (b : Bool) → ⟦ g ⟧ p y ≡ b →
          (e : Bool) → elemB y Z ≡ e →
          trigger g p q Z (y ∷ cs) ≡ nextT g p q Z cs y b e
trig-eq g p q Z y cs false bq e eb rewrite bq = refl
trig-eq g p q Z y cs true bq true eb rewrite bq | eb = refl
trig-eq g p q Z y cs true bq false eb rewrite bq | eb = refl

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

trigger-none : ∀ g p q Z cs c → trigger g p q Z cs ≡ nothing →
               Mem c cs → ⟦ g ⟧ p c ≡ true → elemB c Z ≡ false
trigger-none g p q Z [] c _ () _
trigger-none g p q Z (y ∷ cs) c eq m pt =
  use (⟦ g ⟧ p y) refl (elemB y Z) refl
  where
  use : (b : Bool) → ⟦ g ⟧ p y ≡ b → (e : Bool) → elemB y Z ≡ e →
        elemB c Z ≡ false
  use false bq e eb =
    trigger-none g p q Z cs c (trans (sym (trig-eq g p q Z y cs false bq e eb)) eq)
      (peel m) pt
    where
    peel : Mem c (y ∷ cs) → Mem c cs
    peel (m-here refl) = ⊥-elim (true≢false (trans (sym pt) bq))
    peel (m-there m′) = m′
  use true bq true eb =
    ⊥-elim (just≢ (trans (sym (trig-eq g p q Z y cs true bq true eb)) eq))
  use true bq false eb = at m
    where
    at : Mem c (y ∷ cs) → elemB c Z ≡ false
    at (m-here refl) = eb
    at (m-there m′) =
      trigger-none g p q Z cs c
        (trans (sym (trig-eq g p q Z y cs true bq false eb)) eq) m′ pt

trigger-yes : ∀ g p q Z cs c → trigger g p q Z cs ≡ just c →
              ⟦ g ⟧ p c ≡ true × elemB c Z ≡ true × Mem c cs
trigger-yes g p q Z [] c ()
trigger-yes g p q Z (y ∷ cs) c eq = use (⟦ g ⟧ p y) refl (elemB y Z) refl
  where
  use : (b : Bool) → ⟦ g ⟧ p y ≡ b → (e : Bool) → elemB y Z ≡ e →
        ⟦ g ⟧ p c ≡ true × elemB c Z ≡ true × Mem c (y ∷ cs)
  use b bq e eb = body (nextT g p q Z cs y b e)
                       (trig-eq g p q Z y cs b bq e eb)
    where
    body : (hit : Maybe RConf) → trigger g p q Z (y ∷ cs) ≡ hit →
           ⟦ g ⟧ p c ≡ true × elemB c Z ≡ true × Mem c (y ∷ cs)
    body nothing eqH = ⊥-elim (just≢ (trans (sym eq) eqH))
    body (just found) eqH = onFound b e bq eb
      where
      same : found ≡ c
      same = just-inj (trans (sym eqH) eq)
      onFound : (b e : Bool) → ⟦ g ⟧ p y ≡ b → elemB y Z ≡ e →
                ⟦ g ⟧ p c ≡ true × elemB c Z ≡ true × Mem c (y ∷ cs)
      onFound false e bq eb =
        let pt , ez , mem = trigger-yes g p q Z cs c
              (trans (sym (trig-eq g p q Z y cs false bq e eb)) eq)
        in pt , ez , m-there mem
      onFound true true bq eb =
        let yc = trans (just-inj (trans (sym (trig-eq g p q Z y cs true bq true eb)) eqH)) same
        in subst (λ z → ⟦ g ⟧ p z ≡ true) yc bq ,
           subst (λ z → elemB z Z ≡ true) yc eb ,
           subst (λ z → Mem z (y ∷ cs)) yc (m-here refl)
      onFound true false bq eb =
        let pt , ez , mem = trigger-yes g p q Z cs c
              (trans (sym (trig-eq g p q Z y cs true bq false eb)) eq)
        in pt , ez , m-there mem

-- A list the search can reason about: it contains the start, it is
-- closed under steps, and every member has a chain back to the start.
record Closed (g : Graph) (cs : List RConf) : Set where
  field
    hasInit : Mem (init g) cs
    shut : ∀ {c w d} → Mem c cs → Step g c w d → Mem d cs
    spine : ∀ {c} → Mem c cs →
            Σ (List (Who × RConf))
              (λ xs → Σ (Chain g (init g) xs) (λ ch → End ch ≡ c))
open Closed public

InL : List RConf → Path → Set
InL cs σ = Mem (head σ) cs

stay : (g : Graph) (cs : List RConf) (cl : Closed g cs) (π : Path) →
       IsRun g π → Mem (head π) cs → Globally (InL cs) π
now (stay g cs cl π r m) = m
later (stay g cs cl π r m) =
  stay g cs cl (tail π) (rest {g} {π} r)
       (shut cl m (proj₂ (step {g} {π} r)))

first-hit : ∀ g p cs π →
            Globally (InL cs) π →
            Eventually (Gone g (avoid g p cs)) π →
            Eventually (HoldsP g p) π
first-hit g p cs π gl (hereE gone) =
  hereE (hit-p g p (head π) cs (now {P = InL cs} {π} gl) gone)
first-hit g p cs π gl (thereE ev) =
  thereE (first-hit g p cs (tail π) (later {P = InL cs} {π} gl) ev)

ev-run : (g : Graph) (p : StateProp) (cs Z : List RConf) →
         Closed g cs → Rem g (avoid g p cs) Z →
         elemB (init g) Z ≡ false →
         (π : Path) → head π ≡ init g → IsRun g π →
         Eventually (HoldsP g p) π
ev-run g p cs Z cl rem fz π hd rn = at (elemB (init g) (avoid g p cs)) refl
  where
  at : (b : Bool) → elemB (init g) (avoid g p cs) ≡ b → Eventually (HoldsP g p) π
  at false eq =
    hereE (subst (λ z → ⟦ g ⟧ p z ≡ true) (sym hd)
             (hit-p g p (init g) cs (hasInit cl) (¬mem eq)))
  at true eq =
    let mA = find (init g) (avoid g p cs) eq
        mH = subst (λ z → Mem z cs) (sym hd) (hasInit cl)
    in first-hit g p cs π (stay g cs cl π rn mH)
         (leaves rem (init g) mA (¬mem fz) π hd rn)

q-comes : (g : Graph) (q : StateProp) (cs Z : List RConf) →
          Closed g cs → Rem g (avoid g q cs) Z →
          (π : Path) → IsRun g π → Mem (head π) cs →
          elemB (head π) Z ≡ false →
          Eventually (HoldsP g q) π
q-comes g q cs Z cl rem π rn m fz = at (elemB (head π) (avoid g q cs)) refl
  where
  at : (b : Bool) → elemB (head π) (avoid g q cs) ≡ b → Eventually (HoldsP g q) π
  at false eq = hereE (hit-p g q (head π) cs m (¬mem eq))
  at true eq =
    first-hit g q cs π (stay g cs cl π rn m)
      (leaves rem (head π) (find (head π) (avoid g q cs) eq) (¬mem fz) π refl rn)

Waits : Graph → StateProp → StateProp → Path → Set
Waits g p q σ = ⟦ g ⟧ p (head σ) ≡ true → Eventually (HoldsP g q) σ

to-glob : (g : Graph) (p q : StateProp) (cs Z : List RConf) →
          Closed g cs → Rem g (avoid g q cs) Z →
          (∀ {x} → Mem x cs → ⟦ g ⟧ p x ≡ true → elemB x Z ≡ false) →
          (π : Path) → IsRun g π → Mem (head π) cs →
          Globally (Waits g p q) π
now (to-glob g p q cs Z cl rem none π rn m) imp =
  q-comes g q cs Z cl rem π rn m (none m imp)
later (to-glob g p q cs Z cl rem none π rn m) =
  to-glob g p q cs Z cl rem none (tail π) (rest {g} {π} rn)
          (shut cl m (proj₂ (step {g} {π} rn)))

not-now : ∀ {g p q π} → ¬ Waits g p q π → ¬ Holds g (leadsTo p q) π
not-now {g} {p} {q} {π} ¬w gl = ¬w (now {P = Waits g p q} {π} gl)

-- `follow` of an empty chain is the same run, observed one step at a time.
record Same (π ρ : Path) : Set where
  coinductive
  field
    same-head : head π ≡ head ρ
    same-tail : Same (tail π) (tail ρ)
open Same public

same-refl : ∀ {π} → Same π π
same-head same-refl = refl
same-tail same-refl = same-refl

same-nil : ∀ {g a π} → Same (follow (c-nil {g} {a}) π) π
same-head (same-nil {π = π}) = refl
same-tail (same-nil {π = π}) = same-refl

cast-ev : ∀ {g q π ρ} → Same π ρ → Eventually (HoldsP g q) π → Eventually (HoldsP g q) ρ
cast-ev {g} {q} s (hereE ok) = hereE (subst (λ z → ⟦ g ⟧ q z ≡ true) (same-head s) ok)
cast-ev {g} {q} s (thereE ev) = thereE (cast-ev {g} {q} (same-tail s) ev)

cast-glob : ∀ {g p q π ρ} → Same π ρ →
            Globally (Waits g p q) π → Globally (Waits g p q) ρ
now (cast-glob {g} {p} {q} {π} s gl) imp =
  cast-ev {g} {q} s (now {P = Waits g p q} {π} gl
              (subst (λ z → ⟦ g ⟧ p z ≡ true) (sym (same-head s)) imp))
later (cast-glob {g} {p} {q} {π} {ρ} s gl) =
  cast-glob {g} {p} {q} {π = tail π} {ρ = tail ρ} (same-tail s)
    (later {P = Waits g p q} {π} gl)

prefix-fail : ∀ {g p q a xs} (ch : Chain g a xs) (π : Path) →
              End ch ≡ head π →
              ¬ Holds g (leadsTo p q) π →
              ¬ Holds g (leadsTo p q) (follow ch π)
prefix-fail {g} {p} {q} c-nil π _ ¬h h =
  ¬h (cast-glob {g} {p} {q} same-nil h)
prefix-fail {g} {p} {q} (c-cons st rest) π end ¬h h =
  prefix-fail {g} {p} {q} rest π end ¬h
    (later {P = Waits g p q} {π = follow (c-cons st rest) π} h)

to-denied : ∀ g p q cs Z c → HasOut g Z → Sub Z (avoid g q cs) →
            trigger g p q Z cs ≡ just c → Closed g cs →
            ¬ Satisfies g (leadsTo p q)
to-denied g p q cs Z c ho sub eq cl sat =
  let pt , ez , mem = trigger-yes g p q Z cs c eq
      xs , ch , end = spine cl mem
      hn = seal ho
      mZ = find c Z ez
      π = zpath g Z hn c mZ
      runZ = zrun g Z hn c mZ
      ¬here = not-now {g} {p} {q} {π}
                (λ imp → no-hit {g} {q} {π}
                   (stay-out {g} {q} {Z} hn c mZ (region-no {g} {p = q} {cs} {Z} sub))
                   (imp pt))
      whole = follow ch π
  in prefix-fail {g} {p} {q} ch π end ¬here
       (sat whole (follow-head ch π end refl) (follow-run ch π end runZ))

data LiveF : Set where
  lev : StateProp → LiveF
  lto : StateProp → StateProp → LiveF

-- Stem and loop of the first-successor walk from a survivor.
-- The lists are the chains `tour-of` keeps.
loop-of : (g : Graph) (Z : List RConf) (ho : HasOut g Z) (c : RConf) (m : Mem c Z) →
          List (Who × RConf) × List (Who × RConf)
loop-of g Z ho c m =
  let cy = proj₂ (tour-of g Z ho c m)
  in Cycle.stem cy , Cycle.loop cy

answerEv : (g : Graph) (Z : List RConf) (ho : HasOut g Z) (b : Bool) →
           elemB (init g) Z ≡ b → Answer
answerEv g Z ho false _ = yes
answerEv g Z ho true eq =
  let stem , lp = loop-of g Z ho (init g) (find (init g) Z eq)
  in no (lasso [] stem lp)

answerTo : (g : Graph) (Z : List RConf) (ho : HasOut g Z) (hit : Maybe RConf) →
           List (Who × RConf) → Answer
answerTo g Z ho nothing _ = yes
answerTo g Z ho (just c) pre = onIn (elemB c Z) refl
  where
  onIn : (b : Bool) → elemB c Z ≡ b → Answer
  onIn false _ = yes
  onIn true eq =
    let stem , lp = loop-of g Z ho c (find c Z eq)
    in no (lasso pre stem lp)

embed : LiveF → Formula
embed (lev p) = eventually p
embed (lto p q) = leadsTo p q

yes-skip : ∀ {A : Set} {w} → yes ≡ no w → A
yes-skip ()

no-skip : ∀ {A : Set} {w} → no w ≡ yes → A
no-skip ()

-- The lasso `checkLive` stores, together with the run obtained by
-- prefixing its chains onto the cycle played forever.
data Witness (g : Graph) : LiveF → Cex → Set where
  wit-ev : ∀ {p l stem loop} →
           (chS : Chain g (init g) stem) → End chS ≡ l →
           (chL : Chain g l loop) → End chL ≡ l →
           Σ (Who × RConf) (λ wd → Σ (List (Who × RConf)) (λ ys → loop ≡ wd ∷ ys)) →
           (π : Path) → head π ≡ init g → IsRun g π →
           ¬ Holds g (eventually p) π →
           Witness g (lev p) (lasso [] stem loop)
  wit-to : ∀ {p q c l xs stem loop} →
           (pre : Chain g (init g) xs) → End pre ≡ c →
           ⟦ g ⟧ p c ≡ true →
           (chS : Chain g c stem) → End chS ≡ l →
           (chL : Chain g l loop) → End chL ≡ l →
           Σ (Who × RConf) (λ wd → Σ (List (Who × RConf)) (λ ys → loop ≡ wd ∷ ys)) →
           (π : Path) → head π ≡ init g → IsRun g π →
           ¬ Holds g (leadsTo p q) π →
           Witness g (lto p q) (lasso xs stem loop)

miss : ∀ {g φ w} → Witness g φ w → ¬ Satisfies g (embed φ)
miss (wit-ev _ _ _ _ _ π hd rn bad) sat = bad (sat π hd rn)
miss (wit-to _ _ _ _ _ _ _ _ π hd rn bad) sat = bad (sat π hd rn)

Judged : Graph → List RConf → LiveF → Set
Judged g cs φ =
  Σ Answer (λ a →
    (a ≡ yes → Closed g cs → Satisfies g (embed φ)) ×
    (∀ {w} → a ≡ no w → Closed g cs → Witness g φ w))

packEv : (g : Graph) (p : StateProp) (cs Z : List RConf) →
         HasOut g Z → Sub Z (avoid g p cs) → Rem g (avoid g p cs) Z →
         (b : Bool) → elemB (init g) Z ≡ b →
         Judged g cs (lev p)
packEv g p cs Z ho sub rem false eq =
  yes , (λ _ cl π hd rn → ev-run g p cs Z cl rem eq π hd rn) , yes-skip
packEv g p cs Z ho sub rem true eq = no w , no-skip , refuse
  where
  cy = proj₂ (tour-of g Z ho (init g) (find (init g) Z eq))
  w = lasso [] (Cycle.stem cy) (Cycle.loop cy)
  π = open-path cy
  refuse : ∀ {w′} → no w ≡ no w′ → Closed g cs → Witness g (lev p) w′
  refuse refl _ =
    wit-ev (Cycle.chS cy) (Cycle.eS cy) (Cycle.chL cy) (Cycle.eL cy) (Cycle.ne cy)
      π (open-head cy) (open-run cy)
      (no-hit {g} {p} (open-miss {g} {p} cy (region-no {g} {p} {cs} {Z} sub)))

packTo : (g : Graph) (p q : StateProp) (cs Z : List RConf) →
         HasOut g Z → Sub Z (avoid g q cs) → Rem g (avoid g q cs) Z →
         (hit : Maybe RConf) → trigger g p q Z cs ≡ hit →
         Closed g cs →
         Judged g cs (lto p q)
packTo g p q cs Z ho sub rem nothing eq _ =
  yes , (λ _ cl π hd rn →
           let mH = subst (λ z → Mem z cs) (sym hd) (hasInit cl)
           in to-glob g p q cs Z cl rem
                (λ {x} mx pt → trigger-none g p q Z cs x eq mx pt)
                π rn mH) , yes-skip
packTo g p q cs Z ho sub rem (just c) eq cl0 = no w , no-skip , refuse
  where
  pt = proj₁ (trigger-yes g p q Z cs c eq)
  ez = proj₁ (proj₂ (trigger-yes g p q Z cs c eq))
  mem = proj₂ (proj₂ (trigger-yes g p q Z cs c eq))
  cy = proj₂ (tour-of g Z ho c (find c Z ez))
  sp = spine cl0 mem
  pre = proj₁ (proj₂ sp)
  endPre = proj₂ (proj₂ sp)
  inner = open-path cy
  hdI = open-head cy
  link = trans endPre (sym hdI)
  whole = follow pre inner
  w = lasso (proj₁ sp) (Cycle.stem cy) (Cycle.loop cy)
  ¬q = no-hit {g} {q} (open-miss {g} {p = q} cy (region-no {g} {p = q} {cs} {Z} sub))
  ¬inner = not-now {g} {p} {q} {π = inner}
             (λ imp → ¬q (imp (subst (λ z → ⟦ g ⟧ p z ≡ true) (sym hdI) pt)))
  refuse : ∀ {w′} → no w ≡ no w′ → Closed g cs → Witness g (lto p q) w′
  refuse refl _ =
    wit-to pre endPre pt (Cycle.chS cy) (Cycle.eS cy)
      (Cycle.chL cy) (Cycle.eL cy) (Cycle.ne cy)
      whole (follow-head pre inner endPre hdI)
      (follow-run pre inner link (open-run cy))
      (prefix-fail {g} {p} {q} pre inner link ¬inner)

outcome : (g : Graph) (cs : List RConf) (φ : LiveF) → Closed g cs → Judged g cs φ
outcome g cs (lev p) _ =
  let G = avoid g p cs
      _ , Z , ho , sub , rem = prune g G (<-wellFounded-fast (length G))
  in packEv g p cs Z ho sub rem (elemB (init g) Z) refl
outcome g cs (lto p q) cl =
  let G = avoid g q cs
      _ , Z , ho , sub , rem = prune g G (<-wellFounded-fast (length G))
  in packTo g p q cs Z ho sub rem (trigger g p q Z cs) refl cl

checkLive : (g : Graph) (cs : List RConf) (φ : LiveF) → Closed g cs → Answer
checkLive g cs φ cl = proj₁ (outcome g cs φ cl)

live-sound : ∀ g cs φ (cl : Closed g cs) → checkLive g cs φ cl ≡ yes →
             Satisfies g (embed φ)
live-sound g cs φ cl eq = proj₁ (proj₂ (outcome g cs φ cl)) eq cl

live-witness : ∀ g cs φ w (cl : Closed g cs) → checkLive g cs φ cl ≡ no w →
               Witness g φ w
live-witness g cs φ w cl eq = proj₂ (proj₂ (outcome g cs φ cl)) {w} eq cl

live-deny : ∀ g cs φ w (cl : Closed g cs) → checkLive g cs φ cl ≡ no w →
            ¬ Satisfies g (embed φ)
live-deny g cs φ w cl eq = miss (live-witness g cs φ w cl eq)

live-complete : ∀ g cs φ (cl : Closed g cs) → Satisfies g (embed φ) →
                checkLive g cs φ cl ≡ yes
live-complete g cs φ cl sat with outcome g cs φ cl
... | yes , _ , _ = refl
... | no _ , _ , deny = ⊥-elim (miss (deny refl cl) sat)

------------------------------------------------------------------------
-- Fuel-free reachability agrees with the fuel-bounded search, and a
-- component is closed under a mention that reaches back.
--
-- reachGo is the search Check used through 0.19.4: fuel
-- suc (length of the definitions) and a visited list. reaches is
-- reachAt, well-founded on the unvisited list. Both are true of exactly
-- the paths in Path, so they agree on every signature. reaches is
-- transitive, and component is closed.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.Productive.Reach where

open import Data.Bool.Base using (Bool; true; false; _∧_; _∨_; T; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Nat.Base
  using (ℕ; zero; suc; _≡ᵇ_; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Product.Base using (_×_; _,_; Σ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong; subst)

open import Muro.Base using (Mode; run; evid; spec; Result; ok; fail)
open import Muro.Env using (Sig; Def; lookupDef; lookupList)
open import Muro.Check
  using ( elemℕ; mentions; keepRec; keepStep; recMode; edge; edgeOf
        ; removeℕ; removeℕ-len
        ; downFrom; reachOn; reachAt; reachEdges; reaches; compGo; component )

------------------------------------------------------------------------
-- Small boolean and order facts.
------------------------------------------------------------------------

true≢false : true ≡ false → ⊥
true≢false ()

ok≢fail : ∀ {A : Set} {a : A} {s} → ok a ≡ fail s → ⊥
ok≢fail ()

≡ᵇ-≡ : ∀ m n → (m ≡ᵇ n) ≡ true → m ≡ n
≡ᵇ-≡ m n eq = ≡ᵇ⇒≡ m n (subst T (sym eq) tt)

≡ᵇ-refl : ∀ n → (n ≡ᵇ n) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc n) = ≡ᵇ-refl n

≡ᵇ-sym : ∀ m n → (m ≡ᵇ n) ≡ (n ≡ᵇ m)
≡ᵇ-sym zero    zero    = refl
≡ᵇ-sym zero    (suc _) = refl
≡ᵇ-sym (suc _) zero    = refl
≡ᵇ-sym (suc m) (suc n) = ≡ᵇ-sym m n

∨-false₂ : ∀ a b → (a ∨ b) ≡ false → a ≡ false × b ≡ false
∨-false₂ false false refl = refl , refl
∨-false₂ true  _    ()
∨-false₂ false true ()

∨-false : ∀ {a b} → a ≡ false → b ≡ false → (a ∨ b) ≡ false
∨-false refl refl = refl

∨-left : ∀ {a b} → a ≡ true → (a ∨ b) ≡ true
∨-left refl = refl

∨-introʳ : ∀ a {b} → b ≡ true → (a ∨ b) ≡ true
∨-introʳ true  _  = refl
∨-introʳ false eq = eq

∨-trueʳ : ∀ {a b} → a ≡ false → (a ∨ b) ≡ true → b ≡ true
∨-trueʳ refl eq = eq

∧-true₂ : ∀ a b → (a ∧ b) ≡ true → a ≡ true × b ≡ true
∧-true₂ true b eq = refl , eq
∧-true₂ false _ ()

∧-intro : ∀ {a b} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
∧-intro refl refl = refl

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero}  = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
≤-trans z≤n      _        = z≤n
≤-trans (s≤s ab) (s≤s bc) = s≤s (≤-trans ab bc)

n≤sucn : ∀ n → n ≤ suc n
n≤sucn zero    = z≤n
n≤sucn (suc n) = s≤s (n≤sucn n)

<⇒≤ : ∀ {a b} → a < b → a ≤ b
<⇒≤ (s≤s le) = ≤-trans le (n≤sucn _)

<-suc : ∀ {a b} → a < b → a < suc b
<-suc ab = ≤-trans ab (n≤sucn _)

≤-≢ : ∀ {j n} → j ≤ n → (j ≡ᵇ n) ≡ false → j < n
≤-≢ {zero}  {zero}  z≤n      eq = ⊥-elim (true≢false eq)
≤-≢ {zero}  {suc _} z≤n      _  = s≤s z≤n
≤-≢ {suc j} {suc n} (s≤s le) eq = s≤s (≤-≢ le eq)

n≮n : ∀ {n} → n < n → ⊥
n≮n (s≤s le) = n≮n le

≤-split : ∀ {k j} → k ≤ j → k ≡ j ⊎ suc k ≤ j
≤-split {zero}  {zero}  z≤n      = inj₁ refl
≤-split {zero}  {suc _} z≤n      = inj₂ (s≤s z≤n)
≤-split {suc k} {suc j} (s≤s le) with ≤-split le
... | inj₁ eq = inj₁ (cong suc eq)
... | inj₂ lt = inj₂ (s≤s lt)

+-0 : ∀ m → m + 0 ≡ m
+-0 zero    = refl
+-0 (suc m) = cong suc (+-0 m)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero    n = refl
+-suc (suc m) n = cong suc (+-suc m n)

elem-head : ∀ x xs → elemℕ x (x ∷ xs) ≡ true
elem-head x xs = ∨-left {b = elemℕ x xs} (≡ᵇ-refl x)

elem-tail : ∀ {j x xs} → elemℕ j xs ≡ true → elemℕ j (x ∷ xs) ≡ true
elem-tail {j} {x} {xs} eq = ∨-introʳ (j ≡ᵇ x) {b = elemℕ j xs} eq

elem-subst : ∀ {a b xs} → a ≡ b → elemℕ a xs ≡ true → elemℕ b xs ≡ true
elem-subst {xs = xs} eq el = subst (λ z → elemℕ z xs ≡ true) eq el

------------------------------------------------------------------------
-- Paths. One step is an edge of the definition graph.
------------------------------------------------------------------------

data Path (σ : Sig) : ℕ → ℕ → Set where
  p-here : ∀ i → Path σ i i
  p-step : ∀ {i j k} → elemℕ j (edge σ i) ≡ true → Path σ j k → Path σ i k

path-trans : ∀ {σ i j k} → Path σ i j → Path σ j k → Path σ i k
path-trans (p-here _) q = q
path-trans (p-step e p) q = p-step e (path-trans p q)

------------------------------------------------------------------------
-- The fuel-bounded search, as it stood through 0.19.4. Fuel zero
-- refuses even the target. Visited nodes are not expanded.
------------------------------------------------------------------------

mutual
  reachGo : Sig → ℕ → ℕ → ℕ → List ℕ → Bool
  reachGo _ zero    _   _   _   = false
  reachGo σ (suc f) tgt cur vis =
    if cur ≡ᵇ tgt then true
    else if elemℕ cur vis then false
    else reachAny σ f tgt (edge σ cur) (cur ∷ vis)

  reachAny : Sig → ℕ → ℕ → List ℕ → List ℕ → Bool
  reachAny _ _   _   []       _   = false
  reachAny σ f tgt (x ∷ xs) vis =
    reachGo σ f tgt x vis ∨ reachAny σ f tgt xs vis

reachFuel : Sig → ℕ → ℕ → Bool
reachFuel σ src tgt = reachGo σ (suc (length (Sig.defs σ))) tgt src []

------------------------------------------------------------------------
-- A chain is a path written as the nodes after the start.
------------------------------------------------------------------------

data Chain (σ : Sig) : ℕ → List ℕ → Set where
  c-nil  : ∀ i → Chain σ i []
  c-cons : ∀ {i j xs}
    → elemℕ j (edge σ i) ≡ true → Chain σ j xs → Chain σ i (j ∷ xs)

ends : ∀ {σ i xs} → Chain σ i xs → ℕ
ends (c-nil i)     = i
ends (c-cons _ ch) = ends ch

ends-subst : ∀ {σ a b xs} (eq : a ≡ b) (ch : Chain σ a xs)
  → ends (subst (λ z → Chain σ z xs) eq ch) ≡ ends ch
ends-subst refl ch = refl

chain-path : ∀ {σ i xs} (ch : Chain σ i xs) → Path σ i (ends ch)
chain-path (c-nil i)     = p-here i
chain-path (c-cons e ch) = p-step e (chain-path ch)

path-chain : ∀ {σ i k} → Path σ i k
  → Σ (List ℕ) λ xs → Σ (Chain σ i xs) λ ch → ends ch ≡ k
path-chain (p-here i)   = [] , c-nil i , refl
path-chain (p-step e p) =
  let xs , ch , eq = path-chain p
  in _ , c-cons e ch , eq

data NoDup : List ℕ → Set where
  nd-[] : NoDup []
  nd-∷  : ∀ {x xs} → elemℕ x xs ≡ false → NoDup xs → NoDup (x ∷ xs)

data Below (n : ℕ) : List ℕ → Set where
  bw-[] : Below n []
  bw-∷  : ∀ {x xs} → x < n → Below n xs → Below n (x ∷ xs)

data InList (rest : List ℕ) : List ℕ → Set where
  in-[] : InList rest []
  in-∷  : ∀ {x xs} → elemℕ x rest ≡ true → InList rest xs → InList rest (x ∷ xs)

data Sub : List ℕ → List ℕ → Set where
  s-[] : ∀ {ys} → Sub [] ys
  s-∷  : ∀ {z xs ys} → elemℕ z ys ≡ true → Sub xs ys → Sub (z ∷ xs) ys

no-mem-[] : ∀ z → elemℕ z [] ≡ true → ⊥
no-mem-[] z eq = true≢false (sym eq)

sub-[] : ∀ {ys} → Sub [] ys
sub-[] = s-[]

sub-weaken : ∀ {y xs ys} → Sub xs ys → Sub xs (y ∷ ys)
sub-weaken s-[] = s-[]
sub-weaken {y} (s-∷ {z} {xs} {ys} el s) =
  s-∷ (elem-tail {j = z} {x = y} {xs = ys} el) (sub-weaken s)

sub-refl : ∀ xs → Sub xs xs
sub-refl [] = s-[]
sub-refl (z ∷ ys) = s-∷ (elem-head z ys) (sub-weaken (sub-refl ys))

sub-tail : ∀ {x xs} → Sub xs (x ∷ xs)
sub-tail {x} {xs} = sub-weaken {y = x} (sub-refl xs)

sub-lookup : ∀ {z xs ys} → Sub xs ys → elemℕ z xs ≡ true → elemℕ z ys ≡ true
sub-lookup s-[] ()
sub-lookup {z = z} (s-∷ {z = w} {xs = xs} {ys = ys} ew s) el = look (z ≡ᵇ w) refl el
  where
  look : (b : Bool) → (z ≡ᵇ w) ≡ b
    → (b ∨ elemℕ z xs) ≡ true → elemℕ z ys ≡ true
  look true  beq _   = elem-subst {a = w} {b = z} {xs = ys} (sym (≡ᵇ-≡ z w beq)) ew
  look false _   el′ = sub-lookup s el′

sub-trans : ∀ {xs ys zs} → Sub xs ys → Sub ys zs → Sub xs zs
sub-trans s-[]        _ = s-[]
sub-trans (s-∷ el s) t = s-∷ (sub-lookup t el) (sub-trans s t)

sub-cons : ∀ {j zs ys} → Sub zs ys → Sub (j ∷ zs) (j ∷ ys)
sub-cons {j} {ys = ys} s = s-∷ (elem-head j ys) (sub-weaken s)

mutual
  notin-sub : ∀ i ys zs → elemℕ i ys ≡ false → Sub zs ys → elemℕ i zs ≡ false
  notin-sub _ _ _ _ s-[] = refl
  notin-sub i ys _ el (s-∷ {z = z} {xs = zs} ez s) =
    notin-step i z ys zs (i ≡ᵇ z) refl el ez s

  notin-step : ∀ i z ys zs → (b : Bool) → (i ≡ᵇ z) ≡ b
    → elemℕ i ys ≡ false → elemℕ z ys ≡ true → Sub zs ys
    → (b ∨ elemℕ i zs) ≡ false
  notin-step i z ys _ true beq el ez _ =
    ⊥-elim (true≢false
      (trans (sym (elem-subst {a = z} {b = i} {xs = ys} (sym (≡ᵇ-≡ i z beq)) ez)) el))
  notin-step i z ys zs false _ el _ s = notin-sub i ys zs el s

------------------------------------------------------------------------
-- Soundness: a true answer of the fuel-free search is a path.
------------------------------------------------------------------------

find-edge : ∀ {σ tgt rest′} (a : Acc _<_ (length rest′)) (xs : List ℕ)
  → reachEdges σ tgt xs rest′ a ≡ true
  → Σ ℕ λ j → elemℕ j xs ≡ true × reachAt σ tgt j rest′ a ≡ true
find-edge _ [] ()
find-edge {σ} {tgt} {rest′} a (x ∷ xs) eq = body (reachAt σ tgt x rest′ a) refl eq
  where
  body : (b : Bool) → reachAt σ tgt x rest′ a ≡ b
    → (b ∨ reachEdges σ tgt xs rest′ a) ≡ true
    → Σ ℕ λ j → elemℕ j (x ∷ xs) ≡ true × reachAt σ tgt j rest′ a ≡ true
  body true  ra _   = x , elem-head x xs , ra
  body false _  eq′ =
    let j , ej , rat = find-edge a xs eq′
    in j , elem-tail {j = j} {x = x} {xs = xs} ej , rat

at-sound : ∀ {σ tgt cur rest} (a : Acc _<_ (length rest))
  → reachAt σ tgt cur rest a ≡ true → Path σ cur tgt
at-sound {σ} {tgt} {cur} {rest} (acc rec) eq = body (cur ≡ᵇ tgt) refl eq
  where
  body : (b : Bool) → (cur ≡ᵇ tgt) ≡ b
    → (if b then true else reachOn σ tgt cur rest (elemℕ cur rest) refl rec) ≡ true
    → Path σ cur tgt
  body true beq _ = subst (Path σ cur) (≡ᵇ-≡ cur tgt beq) (p-here cur)
  body false _ eq′ = expand (elemℕ cur rest) refl eq′
    where
    expand : (e : Bool) (pe : elemℕ cur rest ≡ e)
      → reachOn σ tgt cur rest e pe rec ≡ true → Path σ cur tgt
    expand false _ eq″ = ⊥-elim (true≢false (sym eq″))
    expand true pe eq″ =
      let j , ej , rat = find-edge (rec (removeℕ-len cur rest pe)) (edge σ cur) eq″
      in p-step ej (at-sound {rest = removeℕ cur rest}
                     (rec (removeℕ-len cur rest pe)) rat)

reaches-sound : ∀ {σ src tgt} → reaches σ src tgt ≡ true → Path σ src tgt
reaches-sound {σ} eq =
  at-sound {rest = downFrom (length (Sig.defs σ))}
    (<-wellFounded (length (downFrom (length (Sig.defs σ))))) eq

------------------------------------------------------------------------
-- Soundness of the fuel-bounded search.
------------------------------------------------------------------------

mutual
  go-sound : ∀ {σ f tgt cur vis} → reachGo σ f tgt cur vis ≡ true → Path σ cur tgt
  go-sound {f = zero} ()
  go-sound {σ} {suc f} {tgt} {cur} {vis} eq = body (cur ≡ᵇ tgt) refl eq
    where
    body : (b : Bool) → (cur ≡ᵇ tgt) ≡ b
      → (if b then true
         else if elemℕ cur vis then false
         else reachAny σ f tgt (edge σ cur) (cur ∷ vis)) ≡ true
      → Path σ cur tgt
    body true beq _ = subst (Path σ cur) (≡ᵇ-≡ cur tgt beq) (p-here cur)
    body false _ eq′ = visited (elemℕ cur vis) refl eq′
      where
      visited : (e : Bool) → elemℕ cur vis ≡ e
        → (if e then false
           else reachAny σ f tgt (edge σ cur) (cur ∷ vis)) ≡ true
        → Path σ cur tgt
      visited true  _ eq″ = ⊥-elim (true≢false (sym eq″))
      visited false _ eq″ =
        let j , ej , pj = any-sound (edge σ cur) eq″
        in p-step ej pj

  any-sound : ∀ {σ f tgt vis} (xs : List ℕ)
    → reachAny σ f tgt xs vis ≡ true
    → Σ ℕ λ j → elemℕ j xs ≡ true × Path σ j tgt
  any-sound [] ()
  any-sound {σ} {f} {tgt} {vis} (x ∷ xs) eq = body (reachGo σ f tgt x vis) refl eq
    where
    body : (b : Bool) → reachGo σ f tgt x vis ≡ b
      → (b ∨ reachAny σ f tgt xs vis) ≡ true
      → Σ ℕ λ j → elemℕ j (x ∷ xs) ≡ true × Path σ j tgt
    body true  rg _   = x , elem-head x xs
      , go-sound {σ = σ} {f = f} {tgt = tgt} {cur = x} {vis = vis} rg
    body false _  eq′ =
      let j , ej , pj = any-sound xs eq′
      in j , elem-tail {j = j} {x = x} {xs = xs} ej , pj

fuel-sound : ∀ {σ src tgt} → reachFuel σ src tgt ≡ true → Path σ src tgt
fuel-sound {σ} {src} {tgt} eq =
  go-sound {f = suc (length (Sig.defs σ))} {cur = src} {vis = []} eq

------------------------------------------------------------------------
-- Cutting a cycle, then dropping every repeated node.
------------------------------------------------------------------------

cut : ∀ {σ} (i : ℕ) {j xs} (ch : Chain σ j xs)
  → elemℕ i xs ≡ true
  → Σ (List ℕ) λ ys →
      Σ (Chain σ i ys) λ ch′ →
        length ys < length xs × ends ch′ ≡ ends ch × Sub ys xs
cut _ (c-nil _) ()
cut {σ} i (c-cons {j = m} {xs = ys} _ ch) eq = body (i ≡ᵇ m) refl eq
  where
  body : (b : Bool) → (i ≡ᵇ m) ≡ b → elemℕ i (m ∷ ys) ≡ true
    → Σ (List ℕ) λ zs →
        Σ (Chain σ i zs) λ ch′ →
          length zs < suc (length ys) × ends ch′ ≡ ends ch × Sub zs (m ∷ ys)
  body true beq _ =
    ys , subst (λ z → Chain σ z ys) (sym (≡ᵇ-≡ i m beq)) ch
       , s≤s ≤-refl , ends-subst (sym (≡ᵇ-≡ i m beq)) ch , sub-tail {x = m} {xs = ys}
  body false beq eq′ =
    let zs , ch′ , lt , en , sub = cut i ch (∨-trueʳ beq eq′)
    in zs , ch′ , <-suc lt , en , sub-trans sub (sub-tail {x = m} {xs = ys})

simplify : ∀ {σ i xs} (ch : Chain σ i xs)
  → Σ (List ℕ) λ ys →
      Σ (Chain σ i ys) λ ch′ →
        NoDup (i ∷ ys) × ends ch′ ≡ ends ch × Sub ys xs
simplify {σ} {i} {xs} ch = go i xs ch (<-wellFounded (length xs))
  where
  go : ∀ i xs (ch : Chain σ i xs) → Acc _<_ (length xs)
    → Σ (List ℕ) λ ys →
        Σ (Chain σ i ys) λ ch′ →
          NoDup (i ∷ ys) × ends ch′ ≡ ends ch × Sub ys xs
  go i [] (c-nil .i) _ = [] , c-nil i , nd-∷ refl nd-[] , refl , sub-[]
  go i (j ∷ ys) (c-cons e ch) (acc rec) = step (elemℕ i (j ∷ ys)) refl
    where
    step : (b : Bool) → elemℕ i (j ∷ ys) ≡ b
      → Σ (List ℕ) λ zs →
          Σ (Chain σ i zs) λ ch′ →
            NoDup (i ∷ zs) × ends ch′ ≡ ends (c-cons e ch) × Sub zs (j ∷ ys)
    step true el =
      let zs , ch′ , lt , en , sub = cut i (c-cons e ch) el
          ys′ , ch″ , nd , en′ , sub′ = go i zs ch′ (rec lt)
      in ys′ , ch″ , nd , trans en′ en , sub-trans sub′ sub
    step false el =
      let zs , ch′ , nd , en , sub = go j ys ch (rec (s≤s ≤-refl))
          neq , nys = ∨-false₂ (i ≡ᵇ j) (elemℕ i ys) el
      in j ∷ zs , c-cons e ch′
         , nd-∷ (∨-false neq (notin-sub i ys zs nys sub)) nd
         , en
         , sub-cons sub

------------------------------------------------------------------------
-- Completeness of the fuel-free search, on a simple chain whose nodes
-- are still in the unvisited list.
------------------------------------------------------------------------

here-ok : ∀ {σ tgt cur rest} (a : Acc _<_ (length rest))
  → cur ≡ tgt → reachAt σ tgt cur rest a ≡ true
here-ok {σ} {tgt} {cur} {rest} (acc rec) eq = body (cur ≡ᵇ tgt) refl
  where
  body : (b : Bool) → (cur ≡ᵇ tgt) ≡ b
    → (if b then true
       else reachOn σ tgt cur rest (elemℕ cur rest) refl rec) ≡ true
  body true  _   = refl
  body false beq =
    ⊥-elim (true≢false
      (trans (sym (subst (λ z → (cur ≡ᵇ z) ≡ true) eq (≡ᵇ-refl cur))) beq))

j-not-x : ∀ {i j x} → (i ≡ᵇ j) ≡ false → (i ≡ᵇ x) ≡ true → (j ≡ᵇ x) ≡ false
j-not-x {i} {j} {x} neq ib =
  trans (cong (j ≡ᵇ_) (sym (≡ᵇ-≡ i x ib))) (trans (≡ᵇ-sym j i) neq)

remove-keep : ∀ i j xs → (i ≡ᵇ j) ≡ false → elemℕ j xs ≡ true
  → elemℕ j (removeℕ i xs) ≡ true
remove-keep _ _ [] _ ()
remove-keep i j (x ∷ xs) neq el = step (i ≡ᵇ x) refl el
  where
  step : (b : Bool) → (i ≡ᵇ x) ≡ b → elemℕ j (x ∷ xs) ≡ true
    → elemℕ j (if b then xs else x ∷ removeℕ i xs) ≡ true
  step true ib el′ =
    ∨-trueʳ {a = j ≡ᵇ x} {b = elemℕ j xs}
      (j-not-x {i = i} {j = j} {x = x} neq ib) el′
  step false _ el′ = member (j ≡ᵇ x) refl el′
    where
    member : (c : Bool) → (j ≡ᵇ x) ≡ c → (c ∨ elemℕ j xs) ≡ true
      → (c ∨ elemℕ j (removeℕ i xs)) ≡ true
    member true  _   _   = refl
    member false _   el″ = remove-keep i j xs neq el″

in-remove : ∀ {i rest xs} → elemℕ i xs ≡ false → InList rest xs
  → InList (removeℕ i rest) xs
in-remove _ in-[] = in-[]
in-remove {i} {rest} el (in-∷ {x = x} {xs = xs} ex inn) =
  let neq , el′ = ∨-false₂ (i ≡ᵇ x) (elemℕ i xs) el
  in in-∷ (remove-keep i x rest neq ex) (in-remove el′ inn)

edges-hit : ∀ {σ tgt j rest′} (xs : List ℕ) (a : Acc _<_ (length rest′))
  → elemℕ j xs ≡ true
  → reachAt σ tgt j rest′ a ≡ true
  → reachEdges σ tgt xs rest′ a ≡ true
edges-hit [] _ () _
edges-hit {σ} {tgt} {j} {rest′} (x ∷ xs) a el rat = step (j ≡ᵇ x) refl el
  where
  step : (b : Bool) → (j ≡ᵇ x) ≡ b → (b ∨ elemℕ j xs) ≡ true
    → (reachAt σ tgt x rest′ a ∨ reachEdges σ tgt xs rest′ a) ≡ true
  step true beq _ =
    ∨-left {b = reachEdges σ tgt xs rest′ a}
      (subst (λ z → reachAt σ tgt z rest′ a ≡ true) (≡ᵇ-≡ j x beq) rat)
  step false _ el′ =
    ∨-introʳ (reachAt σ tgt x rest′ a) (edges-hit xs a el′ rat)

complete : ∀ {σ tgt cur xs rest}
  → (ch : Chain σ cur xs)
  → ends ch ≡ tgt
  → NoDup (cur ∷ xs)
  → elemℕ cur rest ≡ true
  → InList rest xs
  → (a : Acc _<_ (length rest))
  → reachAt σ tgt cur rest a ≡ true
complete {σ} {cur = cur} {rest = rest} (c-nil .cur) refl _ _ _ a =
  here-ok {rest = rest} a refl
complete {σ} {tgt} {cur} {j ∷ ys} {rest}
  (c-cons {j = j} e ch) en (nd-∷ ncur nd) here (in-∷ ej inn) (acc rec) =
  step (cur ≡ᵇ tgt) refl
  where
  step : (b : Bool) → (cur ≡ᵇ tgt) ≡ b
    → (if b then true
       else reachOn σ tgt cur rest (elemℕ cur rest) refl rec) ≡ true
  step true _ = refl
  step false _ = member (elemℕ cur rest) refl
    where
    member : (eᵇ : Bool) (pe : elemℕ cur rest ≡ eᵇ)
      → reachOn σ tgt cur rest eᵇ pe rec ≡ true
    member false p = ⊥-elim (true≢false (trans (sym here) p))
    member true p =
      let neq , ntail = ∨-false₂ (cur ≡ᵇ j) (elemℕ cur ys) ncur
          smaller = rec (removeℕ-len cur rest p)
          rat = complete ch en nd
                  (remove-keep cur j rest neq ej)
                  (in-remove ntail inn)
                  smaller
      in edges-hit (edge σ cur) smaller e rat

------------------------------------------------------------------------
-- Edge targets and sources are definition indices.
------------------------------------------------------------------------

lookupList-len : ∀ {A : Set} (xs : List A) i {a : A}
  → lookupList xs i ≡ ok a → i < length xs
lookupList-len []       _       ()
lookupList-len (_ ∷ _)  zero    _  = s≤s z≤n
lookupList-len (_ ∷ xs) (suc i) eq = s≤s (lookupList-len xs i eq)

lookup-len : ∀ σ i {d} → lookupDef σ i ≡ ok d → i < length (Sig.defs σ)
lookup-len σ i eq = lookupList-len (Sig.defs σ) i eq

mutual
  keep-len : ∀ {σ j js} → elemℕ j (keepRec σ js) ≡ true → j < length (Sig.defs σ)
  keep-len {js = []} ()
  keep-len {σ} {j} {x ∷ xs} eq = keep-len-step σ j x xs (lookupDef σ x) refl eq

  keep-len-step : ∀ σ j x xs (r : Result Def) → lookupDef σ x ≡ r
    → elemℕ j (keepStep σ x xs r) ≡ true
    → j < length (Sig.defs σ)
  keep-len-step σ j _ xs (fail _) _ eq′ = keep-len {σ} {j} {xs} eq′
  keep-len-step σ j x xs (ok d) lu eq′ =
    keep-len-mode σ j x xs d lu (Def.dmode d) eq′

  keep-len-mode : ∀ σ j x xs d → lookupDef σ x ≡ ok d → (m : Mode)
    → elemℕ j (if recMode m then (x ∷ keepRec σ xs) else keepRec σ xs) ≡ true
    → j < length (Sig.defs σ)
  keep-len-mode σ j x xs d lu run  eq″ = kept-len σ j x xs d eq″ lu
  keep-len-mode σ j x xs d lu evid eq″ = kept-len σ j x xs d eq″ lu
  keep-len-mode σ j x xs d lu spec eq″ = kept-len σ j x xs d eq″ lu

  kept-len : ∀ σ j x xs d
    → elemℕ j (x ∷ keepRec σ xs) ≡ true
    → lookupDef σ x ≡ ok d
    → j < length (Sig.defs σ)
  kept-len σ j x xs d eq lu = kept-hit σ j x xs d (j ≡ᵇ x) refl eq lu

  kept-hit : ∀ σ j x xs d (b : Bool) → (j ≡ᵇ x) ≡ b
    → (b ∨ elemℕ j (keepRec σ xs)) ≡ true
    → lookupDef σ x ≡ ok d
    → j < length (Sig.defs σ)
  kept-hit σ j x _ d true beq _ lu =
    lookup-len σ j
      (subst (λ z → lookupDef σ z ≡ ok d) (sym (≡ᵇ-≡ j x beq)) lu)
  kept-hit σ j _ xs _ false _ eq′ _ = keep-len {σ} {j} {xs} eq′

edge-tgt-mode : ∀ σ j d (m : Mode)
  → elemℕ j (if recMode m then keepRec σ (mentions (Def.dbody d)) else []) ≡ true
  → j < length (Sig.defs σ)
edge-tgt-mode σ j d run  eq = keep-len {js = mentions (Def.dbody d)} eq
edge-tgt-mode σ j d evid eq = keep-len {js = mentions (Def.dbody d)} eq
edge-tgt-mode σ j d spec eq = keep-len {js = mentions (Def.dbody d)} eq

edge-tgt-step : ∀ σ i j (r : Result Def) → lookupDef σ i ≡ r
  → elemℕ j (edgeOf σ r) ≡ true
  → j < length (Sig.defs σ)
edge-tgt-step σ _ j (fail _) _ eq = ⊥-elim (true≢false (sym eq))
edge-tgt-step σ _ j (ok d) _ eq = edge-tgt-mode σ j d (Def.dmode d) eq

edge-tgt : ∀ {σ i j} → elemℕ j (edge σ i) ≡ true → j < length (Sig.defs σ)
edge-tgt {σ} {i} {j} eq = edge-tgt-step σ i j (lookupDef σ i) refl eq

edge-src-step : ∀ σ i j (r : Result Def) → lookupDef σ i ≡ r
  → elemℕ j (edgeOf σ r) ≡ true
  → i < length (Sig.defs σ)
edge-src-step σ i _ (fail _) _ eq = ⊥-elim (true≢false (sym eq))
edge-src-step σ i _ (ok _) lu _ = lookup-len σ i lu

edge-src : ∀ {σ i j} → elemℕ j (edge σ i) ≡ true → i < length (Sig.defs σ)
edge-src {σ} {i} {j} eq = edge-src-step σ i j (lookupDef σ i) refl eq

edge-fail : ∀ {σ i s} → lookupDef σ i ≡ fail s → edge σ i ≡ []
edge-fail {σ} {i} eq = subst (λ r → edgeOf σ r ≡ []) (sym eq) refl

below-in : ∀ {j n} → j < n → elemℕ j (downFrom n) ≡ true
below-in {n = zero} ()
below-in {j} {suc n} (s≤s le) = step (j ≡ᵇ n) refl
  where
  step : (b : Bool) → (j ≡ᵇ n) ≡ b
    → (b ∨ elemℕ j (downFrom n)) ≡ true
  step true  _   = refl
  step false beq = below-in (≤-≢ le beq)

below-inlist : ∀ {n xs} → Below n xs → InList (downFrom n) xs
below-inlist bw-[]        = in-[]
below-inlist (bw-∷ lt bw) = in-∷ (below-in lt) (below-inlist bw)

chain-below : ∀ {σ i xs} (ch : Chain σ i xs) → Below (length (Sig.defs σ)) xs
chain-below (c-nil _) = bw-[]
chain-below {σ} {i} (c-cons {j = j} e ch) =
  bw-∷ (edge-tgt {σ = σ} {i = i} {j = j} e) (chain-below {σ = σ} {i = j} ch)

reaches-complete : ∀ {σ i k} → Path σ i k → reaches σ i k ≡ true
reaches-complete {σ} {i} {k} p =
  let _ , ch , en = path-chain p
      _ , ch′ , nd , en′ , _ = simplify ch
  in from ch′ (trans en′ en) nd
  where
  n = length (Sig.defs σ)
  from : ∀ {ys} (ch : Chain σ i ys) → ends ch ≡ k → NoDup (i ∷ ys)
    → reaches σ i k ≡ true
  from (c-nil _) en _ =
    here-ok {rest = downFrom n} (<-wellFounded (length (downFrom n))) en
  from ch@(c-cons {j = j} e _) en nd =
    complete ch en nd
      (below-in (edge-src {σ = σ} {i = i} {j = j} e))
      (below-inlist (chain-below {σ = σ} {i = i} ch))
      (<-wellFounded (length (downFrom n)))

------------------------------------------------------------------------
-- The fuel bound. A simple list of numbers below n has length at most n.
------------------------------------------------------------------------

tighten : ∀ n xs → elemℕ n xs ≡ false → Below (suc n) xs → Below n xs
tighten _ [] _ _ = bw-[]
tighten n (x ∷ xs) el (bw-∷ (s≤s le) bw) =
  let neq , el′ = ∨-false₂ (n ≡ᵇ x) (elemℕ n xs) el
  in bw-∷ (≤-≢ le (trans (≡ᵇ-sym x n) neq)) (tighten n xs el′ bw)

Drop : ℕ → List ℕ → Set
Drop n xs =
  Σ (List ℕ) λ ys →
    NoDup ys × Below n ys × length xs ≡ suc (length ys) × Sub ys xs

mutual
  drop-hit : ∀ n xs → elemℕ n xs ≡ true → NoDup xs → Below (suc n) xs → Drop n xs
  drop-hit _ [] () _ _
  drop-hit n (x ∷ xs) el (nd-∷ ni nd) (bw-∷ (s≤s le) bw) =
    drop-step n x xs el ni nd le bw (n ≡ᵇ x) refl

  drop-step : ∀ n x xs
    → elemℕ n (x ∷ xs) ≡ true
    → elemℕ x xs ≡ false
    → NoDup xs
    → x ≤ n
    → Below (suc n) xs
    → (b : Bool) → (n ≡ᵇ x) ≡ b
    → Drop n (x ∷ xs)
  drop-step n x xs _ ni nd le bw true beq =
    xs , nd
       , tighten n xs
           (subst (λ z → elemℕ z xs ≡ false) (sym (≡ᵇ-≡ n x beq)) ni) bw
       , refl
       , sub-tail {x = x} {xs = xs}
  drop-step n x xs el ni nd le bw false beq =
    let ys , nd′ , bw′ , eq , sub =
          drop-hit n xs (∨-trueʳ {a = n ≡ᵇ x} {b = elemℕ n xs} beq el) nd bw
        x< = ≤-≢ le (trans (≡ᵇ-sym x n) beq)
    in x ∷ ys
       , nd-∷ (notin-sub x xs ys ni sub) nd′
       , bw-∷ x< bw′
       , cong suc eq
       , sub-cons {j = x} {zs = ys} {ys = xs} sub

mutual
  bounded : ∀ n xs → NoDup xs → Below n xs → length xs ≤ n
  bounded _ [] _ _ = z≤n
  bounded zero (_ ∷ _) _ (bw-∷ () _)
  bounded (suc n) (x ∷ xs) (nd-∷ ni nd) (bw-∷ lt bw) =
    bound-step n x xs ni nd lt bw (elemℕ n (x ∷ xs)) refl

  bound-step : ∀ n x xs
    → elemℕ x xs ≡ false
    → NoDup xs
    → x < suc n
    → Below (suc n) xs
    → (b : Bool) → elemℕ n (x ∷ xs) ≡ b
    → length (x ∷ xs) ≤ suc n
  bound-step n x xs ni nd lt bw false el =
    ≤-trans (bounded n (x ∷ xs) (nd-∷ ni nd) (tighten n (x ∷ xs) el (bw-∷ lt bw)))
            (n≤sucn n)
  bound-step n x xs ni nd lt bw true el =
    let ys , nd′ , bw′ , eq , _ =
          drop-hit n (x ∷ xs) el (nd-∷ ni nd) (bw-∷ lt bw)
    in subst (λ z → z ≤ suc n) (sym eq) (s≤s (bounded n ys nd′ bw′))

------------------------------------------------------------------------
-- Completeness of the fuel-bounded search, hence agreement.
------------------------------------------------------------------------

data Avoid (vis : List ℕ) : List ℕ → Set where
  av-[] : Avoid vis []
  av-∷  : ∀ {x xs} → elemℕ x vis ≡ false → Avoid vis xs → Avoid vis (x ∷ xs)

avoid-[] : ∀ xs → Avoid [] xs
avoid-[] []       = av-[]
avoid-[] (x ∷ xs) = av-∷ refl (avoid-[] xs)

avoid-shift : ∀ {cur vis ys}
  → elemℕ cur ys ≡ false → Avoid vis ys → Avoid (cur ∷ vis) ys
avoid-shift _ av-[] = av-[]
avoid-shift {cur} el (av-∷ {x} {xs} xv rest) =
  let neq , el′ = ∨-false₂ (cur ≡ᵇ x) (elemℕ cur xs) el
  in av-∷ (∨-false (trans (≡ᵇ-sym x cur) neq) xv) (avoid-shift el′ rest)

avoid-under : ∀ {cur vis j ys}
  → elemℕ cur (j ∷ ys) ≡ false
  → Avoid vis (cur ∷ j ∷ ys)
  → Avoid (cur ∷ vis) (j ∷ ys)
avoid-under {cur = cur} {j = j} {ys = ys} ncur (av-∷ _ (av-∷ jv rest)) =
  let neq , ntail = ∨-false₂ (cur ≡ᵇ j) (elemℕ cur ys) ncur
  in av-∷ (∨-false (trans (≡ᵇ-sym j cur) neq) jv) (avoid-shift ntail rest)

mutual
  any-hit : ∀ {σ f tgt j vis} (xs : List ℕ)
    → elemℕ j xs ≡ true
    → reachGo σ f tgt j vis ≡ true
    → reachAny σ f tgt xs vis ≡ true
  any-hit [] () _
  any-hit {σ} {f} {tgt} {j} {vis} (x ∷ xs) el rg =
    any-step σ f tgt j vis x xs rg (j ≡ᵇ x) refl el

  any-step : ∀ σ f tgt j vis x xs
    → reachGo σ f tgt j vis ≡ true
    → (b : Bool) → (j ≡ᵇ x) ≡ b
    → (b ∨ elemℕ j xs) ≡ true
    → (reachGo σ f tgt x vis ∨ reachAny σ f tgt xs vis) ≡ true
  any-step σ f tgt j vis x xs rg true beq _ =
    ∨-left {b = reachAny σ f tgt xs vis}
      (subst (λ z → reachGo σ f tgt z vis ≡ true) (≡ᵇ-≡ j x beq) rg)
  any-step σ f tgt j vis x xs rg false _ el′ =
    ∨-introʳ (reachGo σ f tgt x vis)
      (any-hit {σ = σ} {f = f} {tgt = tgt} {j = j} {vis = vis} xs el′ rg)

go-complete : ∀ {σ f tgt cur vis xs}
  → (ch : Chain σ cur xs)
  → ends ch ≡ tgt
  → NoDup (cur ∷ xs)
  → Avoid vis (cur ∷ xs)
  → suc (length xs) ≤ f
  → reachGo σ f tgt cur vis ≡ true
go-complete {f = zero} _ _ _ _ ()
go-complete {σ} {suc f} {tgt} {cur} {vis} (c-nil _) en _ _ _ =
  same (cur ≡ᵇ tgt) refl
  where
  same : (b : Bool) → (cur ≡ᵇ tgt) ≡ b
    → (if b then true
       else if elemℕ cur vis then false
       else reachAny σ f tgt (edge σ cur) (cur ∷ vis)) ≡ true
  same true _ = refl
  same false beq =
    ⊥-elim (true≢false
      (trans (sym (subst (λ z → (cur ≡ᵇ z) ≡ true) en (≡ᵇ-refl cur))) beq))
go-complete {σ} {suc f} {tgt} {cur} {vis}
  (c-cons {j = j} {xs = ys} e ch) en (nd-∷ ncur nd) (av-∷ cv av) (s≤s le) =
  step (cur ≡ᵇ tgt) refl
  where
  step : (b : Bool) → (cur ≡ᵇ tgt) ≡ b
    → (if b then true
       else if elemℕ cur vis then false
       else reachAny σ f tgt (edge σ cur) (cur ∷ vis)) ≡ true
  step true _ = refl
  step false _ = visited (elemℕ cur vis) refl
    where
    visited : (e : Bool) → elemℕ cur vis ≡ e
      → (if e then false else reachAny σ f tgt (edge σ cur) (cur ∷ vis)) ≡ true
    visited true p = ⊥-elim (true≢false (trans (sym p) cv))
    visited false _ =
      any-hit (edge σ cur) e
        (go-complete ch en nd (avoid-under ncur (av-∷ cv av)) le)

fuel-complete : ∀ {σ i k} → Path σ i k → reachFuel σ i k ≡ true
fuel-complete {σ} {i} {k} p =
  let _ , ch , en = path-chain p
      ys , ch′ , nd , en′ , _ = simplify ch
  in from ys ch′ (trans en′ en) nd
  where
  n = length (Sig.defs σ)
  from : ∀ ys (ch : Chain σ i ys) → ends ch ≡ k → NoDup (i ∷ ys)
    → reachFuel σ i k ≡ true
  from _ (c-nil .i) en nd =
    go-complete {σ = σ} {f = suc n} {tgt = k} {cur = i} {vis = []} {xs = []}
      (c-nil i) en nd (av-∷ refl av-[]) (s≤s z≤n)
  from ys ch@(c-cons {j = j} e _) en nd =
    go-complete {σ = σ} {f = suc n} {tgt = k} {cur = i} {vis = []} {xs = ys}
      ch en nd (avoid-[] (i ∷ ys))
      (≤-trans (bounded n (i ∷ ys) nd
        (bw-∷ (edge-src {σ = σ} {i = i} {j = j} e)
              (chain-below {σ = σ} {i = i} ch)))
               (n≤sucn n))

bool-same : ∀ {a b : Bool}
  → (a ≡ true → b ≡ true) → (b ≡ true → a ≡ true) → a ≡ b
bool-same {false} {false} _ _ = refl
bool-same {true}  {true}  _ _ = refl
bool-same {true}  {false} f _ = ⊥-elim (true≢false (sym (f refl)))
bool-same {false} {true}  _ g = ⊥-elim (true≢false (sym (g refl)))

-- The two searches agree on every signature.
reaches-fuel : ∀ σ src tgt → reaches σ src tgt ≡ reachFuel σ src tgt
reaches-fuel σ src tgt =
  bool-same {a = reaches σ src tgt} {b = reachFuel σ src tgt}
    (λ r → fuel-complete (reaches-sound {σ = σ} {src = src} {tgt = tgt} r))
    (λ f → reaches-complete (fuel-sound {σ = σ} {src = src} {tgt = tgt} f))

reaches-trans : ∀ σ i j k
  → reaches σ i j ≡ true → reaches σ j k ≡ true → reaches σ i k ≡ true
reaches-trans σ i j k p q =
  reaches-complete
    (path-trans (reaches-sound {σ = σ} {src = i} {tgt = j} p)
                (reaches-sound {σ = σ} {src = j} {tgt = k} q))

------------------------------------------------------------------------
-- component is the set of indices that reach i and that i reaches.
-- It is closed under an edge that reaches back, and therefore under a
-- mention of a definition that reaches back.
------------------------------------------------------------------------

mutual
  compGo-elim : ∀ σ i j k ds
    → elemℕ j (compGo σ i k ds) ≡ true
    → reaches σ i j ≡ true × reaches σ j i ≡ true
  compGo-elim _ _ _ _ [] ()
  compGo-elim σ i j k (_ ∷ ds) eq =
    compGo-body σ i j k ds (reaches σ i k ∧ reaches σ k i) refl eq

  compGo-body : ∀ σ i j k ds (b : Bool)
    → (reaches σ i k ∧ reaches σ k i) ≡ b
    → elemℕ j (if b then (k ∷ compGo σ i (suc k) ds) else compGo σ i (suc k) ds) ≡ true
    → reaches σ i j ≡ true × reaches σ j i ≡ true
  compGo-body σ i j k ds true pr el =
    compGo-hit σ i j k ds pr (j ≡ᵇ k) refl el
  compGo-body σ i j k ds false _ el =
    compGo-elim σ i j (suc k) ds el

  compGo-hit : ∀ σ i j k ds
    → (reaches σ i k ∧ reaches σ k i) ≡ true
    → (b : Bool) → (j ≡ᵇ k) ≡ b
    → (b ∨ elemℕ j (compGo σ i (suc k) ds)) ≡ true
    → reaches σ i j ≡ true × reaches σ j i ≡ true
  compGo-hit σ i j k ds pr true beq _ =
    let rk , kr = ∧-true₂ (reaches σ i k) (reaches σ k i) pr
        eqj = ≡ᵇ-≡ j k beq
    in subst (λ z → reaches σ i z ≡ true) (sym eqj) rk
     , subst (λ z → reaches σ z i ≡ true) (sym eqj) kr
  compGo-hit σ i j k ds _ false _ el′ =
    compGo-elim σ i j (suc k) ds el′

compGo-bump : ∀ {k j} → k ≤ j → (j ≡ᵇ k) ≡ false → suc k ≤ j
compGo-bump {k} {j} k≤j beq = go (≤-split k≤j)
  where
  go : k ≡ j ⊎ suc k ≤ j → suc k ≤ j
  go (inj₂ lt) = lt
  go (inj₁ eq) =
    ⊥-elim (true≢false
      (trans (sym (subst (λ z → (z ≡ᵇ k) ≡ true) eq (≡ᵇ-refl k))) beq))

compGo-shift : ∀ k j n → j < k + suc n → j < suc k + n
compGo-shift k j n lt = subst (λ z → j < z) (+-suc k n) lt

mutual
  compGo-intro : ∀ σ i k j ds
    → k ≤ j
    → j < k + length ds
    → reaches σ i j ≡ true
    → reaches σ j i ≡ true
    → elemℕ j (compGo σ i k ds) ≡ true
  compGo-intro _ _ k j [] k≤j j< _ _ =
    ⊥-elim (n≮n (≤-trans (s≤s k≤j) (subst (λ z → suc j ≤ z) (+-0 k) j<)))
  compGo-intro σ i k j (_ ∷ ds) k≤j j< rij rji =
    compGo-put σ i k j ds k≤j j< rij rji
      (reaches σ i k ∧ reaches σ k i) refl

  compGo-put : ∀ σ i k j ds
    → k ≤ j
    → j < k + suc (length ds)
    → reaches σ i j ≡ true
    → reaches σ j i ≡ true
    → (b : Bool) → (reaches σ i k ∧ reaches σ k i) ≡ b
    → elemℕ j (if b then (k ∷ compGo σ i (suc k) ds) else compGo σ i (suc k) ds) ≡ true
  compGo-put σ i k j ds k≤j j< rij rji true _ =
    compGo-yes σ i k j ds k≤j j< rij rji (j ≡ᵇ k) refl
  compGo-put σ i k j ds k≤j j< rij rji false pr =
    compGo-no σ i k j ds k≤j j< rij rji pr (j ≡ᵇ k) refl

  compGo-yes : ∀ σ i k j ds
    → k ≤ j
    → j < k + suc (length ds)
    → reaches σ i j ≡ true
    → reaches σ j i ≡ true
    → (b : Bool) → (j ≡ᵇ k) ≡ b
    → elemℕ j (k ∷ compGo σ i (suc k) ds) ≡ true
  compGo-yes σ i k j ds _ _ _ _ true beq =
    ∨-left {b = elemℕ j (compGo σ i (suc k) ds)} beq
  compGo-yes σ i k j ds k≤j j< rij rji false beq =
    ∨-introʳ (j ≡ᵇ k)
      (compGo-intro σ i (suc k) j ds
        (compGo-bump {k = k} {j = j} k≤j beq)
        (compGo-shift k j (length ds) j<) rij rji)

  compGo-no : ∀ σ i k j ds
    → k ≤ j
    → j < k + suc (length ds)
    → reaches σ i j ≡ true
    → reaches σ j i ≡ true
    → (reaches σ i k ∧ reaches σ k i) ≡ false
    → (b : Bool) → (j ≡ᵇ k) ≡ b
    → elemℕ j (compGo σ i (suc k) ds) ≡ true
  compGo-no σ i k j ds _ _ rij rji pr true beq =
    ⊥-elim (true≢false
      (trans (sym (∧-intro
        (subst (λ z → reaches σ i z ≡ true) (≡ᵇ-≡ j k beq) rij)
        (subst (λ z → reaches σ z i ≡ true) (≡ᵇ-≡ j k beq) rji))) pr))
  compGo-no σ i k j ds k≤j j< rij rji _ false beq =
    compGo-intro σ i (suc k) j ds
      (compGo-bump {k = k} {j = j} k≤j beq)
      (compGo-shift k j (length ds) j<) rij rji

no-edge-refl : ∀ {σ b a} → edge σ b ≡ [] → reaches σ b a ≡ true → b ≡ a
no-edge-refl {σ = σ} {b = b} {a = a} eq rb =
  go (reaches-sound {σ = σ} {src = b} {tgt = a} rb)
  where
  go : Path σ b a → b ≡ a
  go (p-here _) = refl
  go (p-step {j = j} e _) =
    ⊥-elim (true≢false (sym (subst (λ xs → elemℕ j xs ≡ true) eq e)))

mutual
  keep-of : ∀ {σ j js}
    → elemℕ j js ≡ true
    → (Σ Def λ d → lookupDef σ j ≡ ok d)
    → elemℕ j (keepRec σ js) ≡ true
  keep-of {js = []} () _
  keep-of {σ} {j} {x ∷ xs} el jd =
    keep-of-step σ j x xs (lookupDef σ x) refl el jd

  keep-of-step : ∀ σ j x xs (r : Result Def) → lookupDef σ x ≡ r
    → elemℕ j (x ∷ xs) ≡ true
    → (Σ Def λ d → lookupDef σ j ≡ ok d)
    → elemℕ j (keepStep σ x xs r) ≡ true
  keep-of-step σ j x xs (fail s) lu el jd =
    keep-miss σ j x xs s (j ≡ᵇ x) refl el jd lu
  keep-of-step σ j x xs (ok d) _ el jd =
    keep-of-kept σ j x xs (Def.dmode d) el jd

  -- recMode is true on each constructor, so the kept list is x ∷ keepRec.
  keep-of-kept : ∀ σ j x xs (m : Mode)
    → elemℕ j (x ∷ xs) ≡ true
    → (Σ Def λ d → lookupDef σ j ≡ ok d)
    → elemℕ j (if recMode m then (x ∷ keepRec σ xs) else keepRec σ xs) ≡ true
  keep-of-kept σ j x xs run  el jd = keep-of-mode σ j x xs (j ≡ᵇ x) refl el jd
  keep-of-kept σ j x xs evid el jd = keep-of-mode σ j x xs (j ≡ᵇ x) refl el jd
  keep-of-kept σ j x xs spec el jd = keep-of-mode σ j x xs (j ≡ᵇ x) refl el jd

  keep-of-mode : ∀ σ j x xs (b : Bool) → (j ≡ᵇ x) ≡ b
    → (b ∨ elemℕ j xs) ≡ true
    → (Σ Def λ d → lookupDef σ j ≡ ok d)
    → (b ∨ elemℕ j (keepRec σ xs)) ≡ true
  keep-of-mode _ _ _ _ true _ _ _ = refl
  keep-of-mode σ j _ xs false _ el jd =
    keep-of {σ} {j} {xs} el jd

  keep-miss : ∀ σ j x xs s (b : Bool) → (j ≡ᵇ x) ≡ b
    → elemℕ j (x ∷ xs) ≡ true
    → (Σ Def λ d → lookupDef σ j ≡ ok d)
    → lookupDef σ x ≡ fail s
    → elemℕ j (keepRec σ xs) ≡ true
  keep-miss σ j x _ s true beq _ (d , lj) lx =
    ⊥-elim (ok≢fail
      (trans (sym lj)
        (subst (λ z → lookupDef σ z ≡ fail s) (sym (≡ᵇ-≡ j x beq)) lx)))
  keep-miss σ j x xs _ false beq el jd _ =
    keep-of {σ} {j} {xs}
      (∨-trueʳ {a = j ≡ᵇ x} {b = elemℕ j xs} beq el) jd

mentionsBody : Result Def → List ℕ
mentionsBody (ok d)   = mentions (Def.dbody d)
mentionsBody (fail _) = []

mentionsOf : Sig → ℕ → List ℕ
mentionsOf σ a = mentionsBody (lookupDef σ a)

mention-mode : ∀ σ b d (m : Mode)
  → elemℕ b (mentions (Def.dbody d)) ≡ true
  → (Σ Def λ d′ → lookupDef σ b ≡ ok d′)
  → elemℕ b (if recMode m then keepRec σ (mentions (Def.dbody d)) else []) ≡ true
mention-mode σ b d run  mb jd =
  keep-of {σ} {j = b} {js = mentions (Def.dbody d)} mb jd
mention-mode σ b d evid mb jd =
  keep-of {σ} {j = b} {js = mentions (Def.dbody d)} mb jd
mention-mode σ b d spec mb jd =
  keep-of {σ} {j = b} {js = mentions (Def.dbody d)} mb jd

mention-step : ∀ σ a b (r : Result Def) → lookupDef σ a ≡ r
  → elemℕ b (mentionsBody r) ≡ true
  → (Σ Def λ d → lookupDef σ b ≡ ok d)
  → elemℕ b (edgeOf σ r) ≡ true
mention-step _ _ _ (fail _) _ mb _ = ⊥-elim (true≢false (sym mb))
mention-step σ _ b (ok d) _ mb jd = mention-mode σ b d (Def.dmode d) mb jd

mention-edge : ∀ {σ a b}
  → elemℕ b (mentionsOf σ a) ≡ true
  → (Σ Def λ d → lookupDef σ b ≡ ok d)
  → elemℕ b (edge σ a) ≡ true
mention-edge {σ} {a} {b} mb jd =
  mention-step σ a b (lookupDef σ a) refl mb jd

component-step : ∀ σ i a b (r : Result Def) → lookupDef σ b ≡ r
  → elemℕ a (component σ i) ≡ true
  → elemℕ b (mentionsOf σ a) ≡ true
  → reaches σ b a ≡ true
  → elemℕ b (component σ i) ≡ true
component-step σ i a b (fail s) lb ia _ rb =
  elem-subst {a = a} {b = b} {xs = component σ i}
    (sym (no-edge-refl {σ = σ} {b = b} {a = a}
           (edge-fail {σ = σ} {i = b} lb) rb)) ia
component-step σ i a b (ok d) lb ia mb rb =
  let ria , rai = compGo-elim σ i a 0 (Sig.defs σ) ia
      ab = reaches-complete {σ = σ} {i = a} {k = b}
             (p-step {σ = σ} {i = a} {j = b} {k = b}
               (mention-edge {σ = σ} {a = a} {b = b} mb (d , lb))
               (p-here {σ = σ} b))
  in compGo-intro σ i 0 b (Sig.defs σ) z≤n (lookup-len σ b lb)
       (reaches-trans σ i a b ria ab)
       (reaches-trans σ b a i rb rai)

component-closed : ∀ σ i a b
  → elemℕ a (component σ i) ≡ true
  → elemℕ b (mentionsOf σ a) ≡ true
  → reaches σ b a ≡ true
  → elemℕ b (component σ i) ≡ true
component-closed σ i a b ia mb rb =
  component-step σ i a b (lookupDef σ b) refl ia mb rb

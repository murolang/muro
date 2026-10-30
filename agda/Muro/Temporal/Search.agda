------------------------------------------------------------------------
-- A breadth-first enumeration of the reachable configurations.
--
-- The recursion is well-founded on the pair
-- `(bound ∸ length seen , length queue)`. A fresh configuration
-- shortens the first component: a duplicate-free list of well-formed
-- configurations injects into `Fin (bound g)`, so it cannot already
-- be as long as the bound. A repeated configuration shortens the
-- queue. The bound is the product of the pointer, queue, and slot
-- ranges. It is not `length (Universe g)`, and the search does not
-- build that list.
--
-- `bfs` is the list. The same recursion returns the reachability
-- proof: every configuration it keeps is reachable from the start,
-- and a successor `view` lists is in the list. The injection is
-- consulted in the branch a concrete search does not take.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Search where

open import Data.Bool.Base using (Bool; true; false; T; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []a; _∷_ to _∷a_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe.Base using (Maybe)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; _<_; _<ᵇ_; z≤n; s≤s; s≤s⁻¹; NonZero)
open import Data.Nat.Properties
  using ( ≤-refl; ≤-trans; ≤-antisym; _≟_
        ; +-monoˡ-<; +-monoʳ-<; +-mono-≤; +-comm; +-cancelˡ-≡; +-cancelʳ-≡; +-suc
        ; *-suc; *-monoʳ-≤
        ; <-cmp; ≤∧≢⇒<; ≮⇒≥; <-irrefl; <-≤-trans; ≤-<-trans
        ; <ᵇ⇒<; <⇒<ᵇ
        ; m≤m+n; m≤n+m; m+n≤o⇒n≤o
        ; +-identityʳ; m+[n∸m]≡n
        )
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; inspect; [_])
open import Relation.Nullary.Decidable.Core using (Dec; yes; no)

open import Muro.AsyncRec
  using ( Graph; RConf; rc; Tok; pay; lab; init
        ; ilOf; irOf; l2rOf; r2lOf; elOf; erOf
        ; elemB; conf≟; elem→any
        ; Reach; rhere; rstep; view; kidsV
        )
open Graph

open import Muro.Temporal.Graph
  using ( Wf; wf-init; wf-step; stepsOf; steps-all; StepKid
        ; ptrL; ptrR; UConf; u0; u1
        ; real-steps; kid-local
        ; TokOk; ok-lab; ok-pay; SlotOk
        )
open Wf

open import Muro.Temporal using (Step; snocR)

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- Lexicographic order on a pair of naturals.
------------------------------------------------------------------------

data Lex : ℕ × ℕ → ℕ × ℕ → Set where
  lex₁ : ∀ {m n m′ n′} → m < m′ → Lex (m , n) (m′ , n′)
  lex₂ : ∀ {m n n′} → n < n′ → Lex (m , n) (m , n′)

mutual
  outer : ∀ m → Acc _<_ m → ∀ n → Acc Lex (m , n)
  outer m (acc recM) n = inner m recM n (<-wellFounded-fast n)

  inner : ∀ m → (∀ {m′} → m′ < m → Acc _<_ m′) → ∀ n → Acc _<_ n → Acc Lex (m , n)
  inner m recM n (acc recN) = acc body
    where
    body : ∀ {y} → Lex y (m , n) → Acc Lex y
    body {m′ , n′} (lex₁ p) = outer m′ (recM p) n′
    body {_ , n′} (lex₂ p) = inner m recM n′ (recN p)

wfLex : ∀ m n → Acc Lex (m , n)
wfLex m n = outer m (<-wellFounded-fast m) n

------------------------------------------------------------------------
-- The rectangle a well-formed configuration injects into.
------------------------------------------------------------------------

pow : ℕ → ℕ → ℕ
pow b zero = suc zero
pow b (suc n) = b * pow b n

pack : ℕ → List ℕ → ℕ
pack b [] = zero
pack b (x ∷ xs) = x + b * pack b xs

off : ℕ → ℕ → ℕ
off b zero = zero
off b (suc k) = pow b k + off b k

qBound : ℕ → ℕ → ℕ
qBound b zero = suc zero
qBound b (suc n) = qBound b n + pow b (suc n)

tbase : Graph → ℕ
tbase g = suc (suc (length (alpha g)))

sbase : Graph → ℕ
sbase g = suc (length (alpha g))

tokIx : Tok → ℕ
tokIx (lab false) = zero
tokIx (lab true) = suc zero
tokIx (pay k) = suc (suc k)

module Code (g : Graph) where
  PL = ptrL g
  PR = ptrR g
  TB = tbase g
  SB = sbase g
  QB = qBound TB (cap g)
  EL = pow SB (slotsL g)
  ER = pow SB (slotsR g)

  bound : ℕ
  bound = PL * (PR * (QB * (QB * (EL * ER))))

  radix< : ∀ {b x y} → x < b → x + b * y < b * suc y
  radix< {b} {x} {y} x<b =
    subst (λ n → x + b * y < n) (sym (*-suc b y))
          (+-monoˡ-< (b * y) x<b)

  nest< : ∀ {a A b y} → a < A → y < b → a + A * y < A * b
  nest< {a} {A} {b} {y} a<A y<b =
    <-≤-trans (radix< a<A) (*-monoʳ-≤ A y<b)

  less : ∀ {b x0 y0 x1 y1} → y0 < y1 → x0 < b → x1 < b →
        x0 + b * y0 ≡ x1 + b * y1 → ⊥
  less {b} {x0} {y0} {x1} {y1} y0<y1 x0< x1< e =
    <-irrefl refl (subst (λ n → n < x1 + b * y1) e step)
    where
    step : x0 + b * y0 < x1 + b * y1
    step = <-≤-trans (<-≤-trans (radix< x0<) (*-monoʳ-≤ b y0<y1))
                     (m≤n+m (b * y1) x1)

  split : ∀ {b x y x′ y′} → x < b → x′ < b →
          x + b * y ≡ x′ + b * y′ → x ≡ x′ × y ≡ y′
  split {b} {x} {y} {x′} {y′} xb x′b eq with <-cmp y y′
  ... | tri< y<y′ _ _ = ⊥-elim (less y<y′ xb x′b eq)
  ... | tri> _ _ y′<y = ⊥-elim (less y′<y x′b xb (sym eq))
  ... | tri≈ _ refl _ = +-cancelʳ-≡ (b * y) x x′ eq , refl

  pack< : ∀ {b} xs → All (_< b) xs → pack b xs < pow b (length xs)
  pack< [] _ = s≤s z≤n
  pack< {b} (x ∷ xs) (px ∷a ps) =
    <-≤-trans (radix< px) (*-monoʳ-≤ b (pack< xs ps))

  tok< : ∀ {t} → TokOk g t → tokIx t < TB
  tok< (ok-lab false) = s≤s z≤n
  tok< (ok-lab true) = s≤s (s≤s z≤n)
  tok< (ok-pay {k} p) = s≤s (s≤s p)

  digs< : ∀ {q} → All (TokOk g) q → All (_< TB) (map tokIx q)
  digs< []a = []a
  digs< (p ∷a ps) = tok< p ∷a digs< ps

  suc∸ : ∀ {b} → suc zero ≤ b → suc (b ∸ suc zero) ≡ b
  suc∸ {suc _} (s≤s z≤n) = refl

  pow≥1 : ∀ b n → suc zero ≤ b → suc zero ≤ pow b n
  pow≥1 b zero _ = ≤-refl
  pow≥1 b (suc n) b≥1 =
    ≤-trans (pow≥1 b n b≥1)
      (subst (λ k → pow b n ≤ k * pow b n) (suc∸ b≥1)
             (m≤m+n (pow b n) ((b ∸ suc zero) * pow b n)))

  off-plus : ∀ b m k → off b m ≤ off b (m + k)
  off-plus b m zero =
    subst (λ z → off b m ≤ off b z) (sym (+-identityʳ m)) ≤-refl
  off-plus b m (suc k) =
    subst (λ z → off b m ≤ off b z) (sym (+-suc m k))
          (≤-trans (off-plus b m k)
                   (m≤n+m (off b (m + k)) (pow b (m + k))))

  off-mono : ∀ b m n → m ≤ n → off b m ≤ off b n
  off-mono b m n le =
    subst (λ z → off b m ≤ off b z) (m+[n∸m]≡n le)
          (off-plus b m (n ∸ m))

  off-q : ∀ b n → off b (suc n) ≡ qBound b n
  off-q b zero = refl
  off-q b (suc n) =
    trans (cong (pow b (suc n) +_) (off-q b n))
          (+-comm (pow b (suc n)) (qBound b n))

  len-map : ∀ xs → length (map tokIx xs) ≡ length xs
  len-map [] = refl
  len-map (_ ∷ xs) = cong suc (len-map xs)

  qCode : List Tok → ℕ
  qCode q = off TB (length q) + pack TB (map tokIx q)

  qShift : ∀ {q} → All (TokOk g) q → qCode q < off TB (suc (length q))
  qShift {q} ok =
    subst (λ n → off TB (length q) + pack TB (map tokIx q) < n)
          (cong (_+ off TB (length q)) (cong (pow TB) (len-map q)))
          (subst (λ n → off TB (length q) + pack TB (map tokIx q) < n)
                 (+-comm (off TB (length q)) (pow TB (length (map tokIx q))))
                 (+-monoʳ-< (off TB (length q))
                            (pack< (map tokIx q) (digs< ok))))

  tb≥1 : suc zero ≤ TB
  tb≥1 = s≤s z≤n

  qCode< : ∀ {q} → length q ≤ cap g → All (TokOk g) q → qCode q < QB
  qCode< {q} le ok =
    subst (λ n → qCode q < n) (off-q TB (cap g))
          (<-≤-trans (qShift ok) (off-mono TB (suc (length q)) (suc (cap g)) (s≤s le)))

  ix : RConf → ℕ
  ix (rc il ir l2r r2l el er) =
    il + PL * (ir + PR * (qCode l2r + QB * (qCode r2l + QB * (pack SB el + EL * pack SB er))))

  ix< : ∀ {c} → Wf g c → ix c < bound
  ix< {rc il ir l2r r2l el er} w =
    nest< (il< w)
      (nest< (ir< w)
        (nest< (qCode< (l2r≤ w) (l2rOk w))
          (nest< (qCode< (r2l≤ w) (r2lOk w))
            (nest< (env< (el≡ w) (elOk w))
                   (env< (er≡ w) (erOk w))))))
    where
    env< : ∀ {e n} → length e ≡ n → All (SlotOk g) e → pack SB e < pow SB n
    env< {e} {n} eq ok = subst (λ k → pack SB e < pow SB k) eq (pack< e ok)

  peel : ∀ {m n} → suc m ≡ suc n → m ≡ n
  peel refl = refl

  pack-inj : ∀ {b} xs ys → All (_< b) xs → All (_< b) ys →
             length xs ≡ length ys → pack b xs ≡ pack b ys → xs ≡ ys
  pack-inj [] [] _ _ _ _ = refl
  pack-inj (x ∷ xs) (y ∷ ys) (px ∷a pxs) (py ∷a pys) eqlen eqp =
    cong₂ _∷_ (proj₁ sp) (pack-inj xs ys pxs pys (peel eqlen) (proj₂ sp))
    where
    sp = split px py eqp
  pack-inj [] (y ∷ ys) _ _ () _
  pack-inj (x ∷ xs) [] _ _ () _

  tok-inj : ∀ {a b} → tokIx a ≡ tokIx b → a ≡ b
  tok-inj {lab false} {lab false} _ = refl
  tok-inj {lab false} {lab true} ()
  tok-inj {lab false} {pay _} ()
  tok-inj {lab true} {lab false} ()
  tok-inj {lab true} {lab true} _ = refl
  tok-inj {lab true} {pay _} ()
  tok-inj {pay _} {lab false} ()
  tok-inj {pay _} {lab true} ()
  tok-inj {pay k} {pay m} eq = cong pay (peel (peel eq))

  ∷-inj : ∀ {A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
  ∷-inj refl = refl , refl

  map-tok : ∀ {q q′} → map tokIx q ≡ map tokIx q′ → q ≡ q′
  map-tok {[]} {[]} _ = refl
  map-tok {x ∷ xs} {y ∷ ys} eq =
    cong₂ _∷_ (tok-inj (proj₁ (∷-inj eq))) (map-tok (proj₂ (∷-inj eq)))
  map-tok {[]} {y ∷ ys} ()
  map-tok {x ∷ xs} {[]} ()

  q-gap : ∀ {a b} → length a < length b → All (TokOk g) a → qCode a < qCode b
  q-gap {a} {b} lt oka =
    <-≤-trans (qShift oka)
      (≤-trans (off-mono TB (suc (length a)) (length b) lt)
               (m≤m+n (off TB (length b)) (pack TB (map tokIx b))))

  q-uneq : ∀ {a b} → length a < length b → All (TokOk g) a →
           qCode a ≡ qCode b → ⊥
  q-uneq {a} {b} lt oka e =
    <-irrefl refl (subst (λ n → n < qCode b) e (q-gap {a} {b} lt oka))

  q-inj : ∀ {q q′} → All (TokOk g) q → All (TokOk g) q′ →
          qCode q ≡ qCode q′ → q ≡ q′
  q-inj {q} {q′} ok ok′ eq = trich (<-cmp (length q) (length q′))
    where
    trich : Tri (length q < length q′) (length q ≡ length q′) (length q′ < length q) →
            q ≡ q′
    trich (tri< lt _ _) = ⊥-elim (q-uneq {q} {q′} lt ok eq)
    trich (tri> _ _ gt) = ⊥-elim (q-uneq {q′} {q} gt ok′ (sym eq))
    trich (tri≈ _ len _) =
      map-tok (pack-inj (map tokIx q) (map tokIx q′) (digs< ok) (digs< ok′)
                 (trans (len-map q) (trans len (sym (len-map q′))))
                 (+-cancelˡ-≡ (off TB (length q)) _ _
                    (trans eq (cong (λ n → off TB n + pack TB (map tokIx q′)) (sym len)))))

  env-inj : ∀ {e e′ n} → length e ≡ n → length e′ ≡ n →
            All (SlotOk g) e → All (SlotOk g) e′ →
            pack SB e ≡ pack SB e′ → e ≡ e′
  env-inj {e} {e′} {n} le le′ oe oe′ eq =
    pack-inj e e′ oe oe′ (trans le (sym le′)) eq

  ix-inj : ∀ {c d} → Wf g c → Wf g d → ix c ≡ ix d → c ≡ d
  ix-inj {rc il ir l2r r2l el er} {rc il′ ir′ l2r′ r2l′ el′ er′} w v eq =
    rc-eq (proj₁ spL) (proj₁ spR) (q-inj (l2rOk w) (l2rOk v) (proj₁ spQ))
          (q-inj (r2lOk w) (r2lOk v) (proj₁ spS))
          (env-inj (el≡ w) (el≡ v) (elOk w) (elOk v) (proj₁ spE))
          (env-inj (er≡ w) (er≡ v) (erOk w) (erOk v) (proj₂ spE))
    where
    rc-eq : ∀ {a b c d e f a′ b′ c′ d′ e′ f′} →
            a ≡ a′ → b ≡ b′ → c ≡ c′ → d ≡ d′ → e ≡ e′ → f ≡ f′ →
            rc a b c d e f ≡ rc a′ b′ c′ d′ e′ f′
    rc-eq refl refl refl refl refl refl = refl
    envB : ∀ {e} → length e ≡ slotsL g → All (SlotOk g) e → pack SB e < EL
    envB {e} le ok = subst (λ k → pack SB e < pow SB k) le (pack< e ok)
    spL = split (il< w) (il< v) eq
    spR = split (ir< w) (ir< v) (proj₂ spL)
    spQ = split (qCode< (l2r≤ w) (l2rOk w)) (qCode< (l2r≤ v) (l2rOk v)) (proj₂ spR)
    spS = split (qCode< (r2l≤ w) (r2lOk w)) (qCode< (r2l≤ v) (r2lOk v)) (proj₂ spQ)
    spE = split (envB (el≡ w) (elOk w)) (envB (el≡ v) (elOk v)) (proj₂ spS)

------------------------------------------------------------------------
-- Distinct codes below the bound are at most `bound` many.
------------------------------------------------------------------------

elemN : ℕ → List ℕ → Bool
elemN _ [] = false
elemN n (x ∷ xs) with n ≟ x
... | yes _ = true
... | no _ = elemN n xs

bit : Bool → ℕ
bit true = suc zero
bit false = zero

sumUnder : ℕ → List ℕ → ℕ
sumUnder zero _ = zero
sumUnder (suc k) xs = bit (elemN k xs) + sumUnder k xs

module Card (g : Graph) where
  open Code g public using (bound; ix; ix<; ix-inj)

  codes : (xs : List RConf) → All (Wf g) xs → List ℕ
  codes [] []a = []
  codes (c ∷ cs) (_ ∷a ws) = ix c ∷ codes cs ws

  bit≤1 : ∀ b → bit b ≤ suc zero
  bit≤1 true = ≤-refl
  bit≤1 false = z≤n

  sum≤n : ∀ n xs → sumUnder n xs ≤ n
  sum≤n zero _ = z≤n
  sum≤n (suc k) xs = +-mono-≤ (bit≤1 (elemN k xs)) (sum≤n k xs)

  suc≰ : ∀ {n} → suc n ≤ n → ⊥
  suc≰ {zero} ()
  suc≰ {suc n} (s≤s le) = suc≰ le

  elem-other : ∀ {j x xs} → j ≢ x → elemN j (x ∷ xs) ≡ elemN j xs
  elem-other {j} {x} {xs} neq with j ≟ x
  ... | yes eq = ⊥-elim (neq eq)
  ... | no _ = refl

  j≢ : ∀ {j x} → suc j ≤ x → j ≢ x
  j≢ le refl = suc≰ le

  down : ∀ {j x} → suc j ≤ x → j ≤ x
  down le = m+n≤o⇒n≤o 1 le

  sum-below : ∀ {n x xs} → n ≤ x → sumUnder n (x ∷ xs) ≡ sumUnder n xs
  sum-below {zero} _ = refl
  sum-below {suc j} {x} {xs} sj≤x rewrite elem-other {j} {x} {xs} (j≢ sj≤x) =
    cong (bit (elemN j xs) +_) (sum-below (down sj≤x))

  pred< : ∀ {x k} → x < suc k → x ≢ k → x < k
  pred< x<sk x≢k = ≤∧≢⇒< (s≤s⁻¹ x<sk) x≢k

  sum-ins : ∀ {n x xs} → x < n → elemN x xs ≡ false →
            sumUnder n (x ∷ xs) ≡ suc (sumUnder n xs)
  sum-ins {zero} () 
  sum-ins {suc k} {x} {xs} x< fr with x ≟ k | inspect (_≟_ x) k
  ... | yes refl | [ pr ] rewrite pr | fr =
    cong suc (sum-below {k} {k} {xs} ≤-refl)
  ... | no x≢k | _ =
    let ih = sum-ins (pred< x< x≢k) fr
        same = elem-other {k} {x} {xs} (λ eq → x≢k (sym eq))
    in trans (cong (λ b → bit b + sumUnder k (x ∷ xs)) same)
             (trans (cong (bit (elemN k xs) +_) ih)
                    (+-suc (bit (elemN k xs)) (sumUnder k xs)))

  true≢false : true ≡ false → ⊥
  true≢false ()

  code-hit : ∀ {c cs} (ws : All (Wf g) cs) →
             elemN (ix c) (codes cs ws) ≡ true → Wf g c → elemB c cs ≡ true
  code-hit {c} {[]} []a () _
  code-hit {c} {d ∷ cs} (v ∷a ws) eq w with ix c ≟ ix d
  ... | yes i = subst (λ z → elemB z (d ∷ cs) ≡ true) (sym (ix-inj w v i))
                      (elem-hit d cs)
    where
    elem-hit : ∀ x xs → elemB x (x ∷ xs) ≡ true
    elem-hit x xs with conf≟ x x
    ... | yes _ = refl
    ... | no neq = ⊥-elim (neq refl)
  ... | no _ = step (code-hit ws eq w)
    where
    step : elemB c cs ≡ true → elemB c (d ∷ cs) ≡ true
    step e with conf≟ c d
    ... | yes refl = refl
    ... | no _ = e

  code-fresh : ∀ {c cs} (ws : All (Wf g) cs) (w : Wf g c) →
               elemB c cs ≡ false → elemN (ix c) (codes cs ws) ≡ false
  code-fresh {c} {cs} ws w fr with elemN (ix c) (codes cs ws) | inspect (elemN (ix c)) (codes cs ws)
  ... | false | _ = refl
  ... | true | [ eq ] = ⊥-elim (true≢false (trans (sym (code-hit ws eq w)) fr))

  sum0 : ∀ n → sumUnder n [] ≡ zero
  sum0 zero = refl
  sum0 (suc n) rewrite sum0 n = refl

  len≡ : ∀ xs (ws : All (Wf g) xs) → UConf xs →
         length xs ≡ sumUnder bound (codes xs ws)
  len≡ [] []a _ = sym (sum0 bound)
  len≡ (c ∷ cs) (w ∷a ws) (u1 fr u) =
    trans (cong suc (len≡ cs ws u))
          (sym (sum-ins (ix< w) (code-fresh ws w fr)))

  len≤ : ∀ xs (ws : All (Wf g) xs) → UConf xs → length xs ≤ bound
  len≤ xs ws u = subst (_≤ bound) (sym (len≡ xs ws u)) (sum≤n bound (codes xs ws))

  not< : ∀ {m n} → (m <ᵇ n) ≡ false → ¬ (m < n)
  not< eq lt = subst T eq (<⇒<ᵇ lt)

  tooMany : ∀ {c} seen (ws : All (Wf g) seen) → UConf seen → Wf g c →
            elemB c seen ≡ false → (length seen <ᵇ bound) ≡ false → ⊥
  tooMany {c} seen ws u w fr eq =
    suc≰ (subst (λ n → suc n ≤ bound) (≤-antisym (len≤ seen ws u) ge) more)
    where
    ge : bound ≤ length seen
    ge = ≮⇒≥ (not< eq)
    more : suc (length seen) ≤ bound
    more = len≤ (c ∷ seen) (w ∷a ws) (u1 fr u)

------------------------------------------------------------------------
-- The search.
------------------------------------------------------------------------

kids : Graph → RConf → List RConf
kids g c = map proj₂ (stepsOf g c)

kidsWf : ∀ {g c} → Wf g c → All (Wf g) (kids g c)
kidsWf {g} {c} w = go (steps-all g c)
  where
  go : ∀ {ws} → All (StepKid g c) ws → All (Wf g) (map proj₂ ws)
  go []a = []a
  go ((st , _) ∷a rest) = wf-step w st ∷a go rest

all++ : ∀ {A : Set} {P : A → Set} {xs ys : List A} →
        All P xs → All P ys → All P (xs ++ ys)
all++ []a q = q
all++ (p ∷a ps) q = p ∷a all++ ps q

record Inv (g : Graph) (seen qs : List RConf) : Set where
  constructor mkI
  field
    sWf : All (Wf g) seen
    sU : UConf seen
    qWf : All (Wf g) qs

open Inv

module Walk (g : Graph) where
  open Code g using (bound)
  open Card g using (tooMany)

  fromᵇ : ∀ {m n} → (m <ᵇ n) ≡ true → m < n
  fromᵇ {m} {n} eq = <ᵇ⇒< m n (subst T (sym eq) tt)

  shrink : ∀ {m n} → m < n → n ∸ suc m < n ∸ m
  shrink {m} {zero} ()
  shrink {zero} {suc n} (s≤s z≤n) = s≤s ≤-refl
  shrink {suc m} {suc n} (s≤s lt) = shrink lt

  drop : ∀ {seen c qs} → Inv g seen (c ∷ qs) → Inv g seen qs
  drop (mkI sw su (_ ∷a qw)) = mkI sw su qw

  push : ∀ {seen c qs} → elemB c seen ≡ false → Inv g seen (c ∷ qs) →
         Inv g (c ∷ seen) (kids g c ++ qs)
  push fr (mkI sw su (w ∷a qw)) = mkI (w ∷a sw) (u1 fr su) (all++ (kidsWf w) qw)

  headW : ∀ {c qs} → All (Wf g) (c ∷ qs) → Wf g c
  headW (w ∷a _) = w

  ------------------------------------------------------------------------
  -- Reachability, kept beside the list so the two share one recursion.
  ------------------------------------------------------------------------

  ++ˡ : ∀ {d : RConf} {xs ys : List RConf} →
        Any (_≡_ d) xs → Any (_≡_ d) (xs ++ ys)
  ++ˡ (here p) = here p
  ++ˡ (there m) = there (++ˡ m)

  ++ʳ : ∀ {d : RConf} {ys : List RConf} (xs : List RConf) →
        Any (_≡_ d) ys → Any (_≡_ d) (xs ++ ys)
  ++ʳ [] m = m
  ++ʳ (_ ∷ xs) m = there (++ʳ xs m)

  ++-idʳ : (xs : List RConf) → xs ++ [] ≡ xs
  ++-idʳ [] = refl
  ++-idʳ (x ∷ xs) = cong (x ∷_) (++-idʳ xs)

  split++ : ∀ {d : RConf} {ys : List RConf} (xs : List RConf) →
            Any (_≡_ d) (xs ++ ys) →
            Any (_≡_ d) xs ⊎ Any (_≡_ d) ys
  split++ [] m = inj₂ m
  split++ (_ ∷ _) (here p) = inj₁ (here p)
  split++ (_ ∷ xs) (there m) with split++ xs m
  ... | inj₁ a = inj₁ (there a)
  ... | inj₂ b = inj₂ b

  lose : ∀ {d c : RConf} {qs seen : List RConf} → Any (_≡_ c) seen →
         Any (_≡_ d) (seen ++ (c ∷ qs)) → Any (_≡_ d) (seen ++ qs)
  lose {d} {c} {qs} {seen} cin m = on (split++ seen m)
    where
    on : Any (_≡_ d) seen ⊎ Any (_≡_ d) (c ∷ qs) → Any (_≡_ d) (seen ++ qs)
    on (inj₁ inS) = ++ˡ inS
    on (inj₂ (here refl)) = ++ˡ cin
    on (inj₂ (there inQ)) = ++ʳ seen inQ

  still : ∀ {d c : RConf} {qs ks seen : List RConf} →
          Any (_≡_ d) (seen ++ (c ∷ qs)) →
          Any (_≡_ d) ((c ∷ seen) ++ (ks ++ qs))
  still {d} {c} {qs} {ks} {seen} m = on (split++ seen m)
    where
    on : Any (_≡_ d) seen ⊎ Any (_≡_ d) (c ∷ qs) →
         Any (_≡_ d) ((c ∷ seen) ++ (ks ++ qs))
    on (inj₁ inS) = there (++ˡ {ys = ks ++ qs} inS)
    on (inj₂ (here refl)) = here refl
    on (inj₂ (there inQ)) = ++ʳ (c ∷ seen) (++ʳ ks inQ)

  kidAny : ∀ {c d} → Any (_≡_ d) (kidsV (view g c)) → Any (_≡_ d) (kids g c)
  kidAny {d = d} mem =
    subst (Any (_≡_ d)) (sym (real-steps (kid-local mem))) mem

  kidsR : ∀ {c} → Reach g (init g) c → All (Reach g (init g)) (kids g c)
  kidsR {c} r = walk (steps-all g c)
    where
    walk : ∀ {ws} → All (StepKid g c) ws → All (Reach g (init g)) (map proj₂ ws)
    walk []a = []a
    walk ((_ , mem) ∷a rest) = snocR r mem ∷a walk rest

  record Rich (seen qs : List RConf) : Set where
    constructor mkR
    field
      rS : All (Reach g (init g)) seen
      rQ : All (Reach g (init g)) qs
      orig : Any (_≡_ (init g)) (seen ++ qs)
      shut : ∀ {c d} → Any (_≡_ c) seen →
             Any (_≡_ d) (kidsV (view g c)) → Any (_≡_ d) (seen ++ qs)
  open Rich

  record Good (cs : List RConf) : Set where
    constructor mkG
    field
      reached : All (Reach g (init g)) cs
      origin : Any (_≡_ (init g)) cs
      closed : ∀ {c d} → Any (_≡_ c) cs →
               Any (_≡_ d) (kidsV (view g c)) → Any (_≡_ d) cs
  open Good

  doneR : ∀ {seen} → Rich seen [] → Good seen
  reached (doneR ρ) = rS ρ
  origin (doneR {seen} ρ) = subst (Any (_≡_ (init g))) (++-idʳ seen) (orig ρ)
  closed (doneR {seen} ρ) {d = d} xin mem =
    subst (Any (_≡_ d)) (++-idʳ seen) (shut ρ xin mem)

  dropR : ∀ {seen c qs} → Any (_≡_ c) seen → Rich seen (c ∷ qs) → Rich seen qs
  dropR cin ρ =
    mkR (rS ρ) (tailQ (rQ ρ)) (lose cin (orig ρ)) (λ xin mem → lose cin (shut ρ xin mem))
    where
    tailQ : ∀ {x xs} → All (Reach g (init g)) (x ∷ xs) → All (Reach g (init g)) xs
    tailQ (_ ∷a rs) = rs

  pushR : ∀ {seen c qs} → Rich seen (c ∷ qs) → Rich (c ∷ seen) (kids g c ++ qs)
  pushR {seen} {c = c} {qs = qs} ρ =
    mkR (headQ (rQ ρ) ∷a rS ρ) (all++ (kidsR (headQ (rQ ρ))) (tailQ (rQ ρ)))
        (still (orig ρ)) shut′
    where
    headQ : ∀ {x xs} → All (Reach g (init g)) (x ∷ xs) → Reach g (init g) x
    headQ (r ∷a _) = r
    tailQ : ∀ {x xs} → All (Reach g (init g)) (x ∷ xs) → All (Reach g (init g)) xs
    tailQ (_ ∷a rs) = rs
    shut′ : ∀ {x d} → Any (_≡_ x) (c ∷ seen) →
            Any (_≡_ d) (kidsV (view g x)) →
            Any (_≡_ d) ((c ∷ seen) ++ (kids g c ++ qs))
    shut′ (here refl) mem =
      ++ʳ (c ∷ seen) (++ˡ {xs = kids g c} {ys = qs} (kidAny mem))
    shut′ (there xin) mem = still (shut ρ xin mem)

  startR : Rich [] (init g ∷ [])
  startR = mkR []a (rhere ∷a []a) (here refl) (λ ())

  Result : Set
  Result = Σ (List RConf) Good

  go : (seen qs : List RConf) →
       Acc Lex (bound ∸ length seen , length qs) →
       Inv g seen qs → Rich seen qs → Result
  go seen [] _ _ ρ = seen , doneR ρ
  go seen (c ∷ qs) (acc rec) inv ρ with elemB c seen | inspect (elemB c) seen
  ... | true | [ hit ] =
    go seen qs
       (rec {y = bound ∸ length seen , length qs}
            (lex₂ {m = bound ∸ length seen} {n = length qs} {n′ = suc (length qs)}
                  (s≤s ≤-refl)))
       (drop inv) (dropR (elem→any hit) ρ)
  ... | false | [ fr ] = add (length seen <ᵇ bound) refl
    where
    add : (b : Bool) → (length seen <ᵇ bound) ≡ b → Result
    add true eq =
      go (c ∷ seen) (kids g c ++ qs)
         (rec {y = bound ∸ suc (length seen) , length (kids g c ++ qs)}
              (lex₁ {m = bound ∸ suc (length seen)}
                    {n = length (kids g c ++ qs)}
                    {m′ = bound ∸ length seen}
                    {n′ = length (c ∷ qs)}
                    (shrink {m = length seen} {n = bound}
                            (fromᵇ {m = length seen} {n = bound} eq))))
         (push fr inv) (pushR ρ)
    add false eq =
      ⊥-elim (tooMany seen (sWf inv) (sU inv) (headW (qWf inv)) fr eq)

  start : Inv g [] (init g ∷ [])
  start = mkI []a u0 (wf-init g ∷a []a)

  ran : Result
  ran = go [] (init g ∷ []) (wfLex bound 1) start startR

  bfs : List RConf
  bfs = proj₁ ran

  searched : Good bfs
  searched = proj₂ ran

bfs : Graph → List RConf
bfs g = Walk.bfs g

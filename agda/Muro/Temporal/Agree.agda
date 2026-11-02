------------------------------------------------------------------------
-- On the fragment, with each echoed name bound once, `walk` and
-- `compile` return the same counters. The blocks they allocate occupy
-- the interval from the current block number up to `next`, in order.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Agree where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Muro.AsyncRec
  using ( Atom; aNat; aBit; aCon; Tag
        ; RProc; rdone; rstop; rput; recho; rget; rpick0; rpick1
        ; rcover; riget; rmget; rmu; rvar
        ; bDone; bStop; bPut; bEcho; bGet; bPick0; bPick1; bCover; bIget; bMget
        ; COut; cok; cfail
        ; compile; compileArms; addNames; lookupN; elemS
        ; REnv; VEnv
        )
open import Muro.Temporal.Bridge
  using ( Frag; fdone; fstop; fput; fget; fpick0; fpick1; fcover; figet; fmget; fmu; fvar
        ; fnat; fbit; fcon; fecho
        ; FragArms; farm; farms0; farms1
        ; elab; elabArms; echoOk; echoOkArms; echoHere; once; ∧-left; ∧-right
        ; echoAF; echoBF; spinRF; echo-plain; spin-plain
        )
open import Muro.Temporal.Pic
open import Muro.Temporal.Source
  using ( Pay; pNat; pBit; pCon; pEcho
        ; Arm; aok
        ; SProc; sdone; sstop; sput; sget; spick0; spick1
        ; scover; siget; smget; smu; svar
        ; W; mkW; EnvI; addPend; walk; walkArms; findS; bnames; bnamesArms
        ; src-echoA; src-echoB; src-spinR
        )
open W

------------------------------------------------------------------------
-- Where the next binder sits, and how two successive bodies meet.
------------------------------------------------------------------------

get-slot : ∀ (pre : List String) (x : String) s →
          s ≡ length pre → suc s ≡ length (pre ++ (x ∷ []))
get-slot pre x s eq =
  trans (cong suc eq)
    (sym (trans (len++ pre (x ∷ []))
          (trans (+-suc (length pre) zero) (cong suc (+-idr (length pre))))))

get-names : ∀ (pre : List String) (x : String) (bp post : List String) {ns : List String} →
            ns ≡ pre ++ (x ∷ bp) ++ post →
            ns ≡ (pre ++ (x ∷ [])) ++ bp ++ post
get-names pre x bp post eq = trans eq (sym (++assoc pre (x ∷ []) (bp ++ post)))

split-left : ∀ (pre bp bq post : List String) {ns : List String} →
             ns ≡ pre ++ (bp ++ bq) ++ post →
             ns ≡ pre ++ bp ++ (bq ++ post)
split-left pre bp bq post eq =
  trans eq (cong (λ ys → pre ++ ys) (++assoc bp bq post))

split-right : ∀ (pre bp bq post : List String) {ns : List String} →
              ns ≡ pre ++ (bp ++ bq) ++ post →
              ns ≡ (pre ++ bp) ++ bq ++ post
split-right pre bp bq post eq =
  trans eq (trans (cong (λ ys → pre ++ ys) (++assoc bp bq post))
                  (sym (++assoc pre bp (bq ++ post))))

cat-slot : ∀ {s s1} (pre bp : List String) →
           s1 ≡ s + length bp → s ≡ length pre →
           s1 ≡ length (pre ++ bp)
cat-slot {s} {s1} pre bp end seq =
  trans end (trans (cong (λ z → z + length bp) seq) (sym (len++ pre bp)))

shift-end : ∀ {s s2 lp} → s2 ≡ suc s + lp → s2 ≡ s + suc lp
shift-end {s} {_} {lp} eq = trans eq (sym (+-suc s lp))

sum-len : ∀ {s s1 s2} (bp bq : List String) →
          s1 ≡ s + length bp → s2 ≡ s1 + length bq →
          s2 ≡ s + length (bp ++ bq)
sum-len {s} {_} {_} bp bq e1 e2 =
  trans (trans e2 (trans (cong (λ z → z + length bq) e1)
                         (+-assoc s (length bp) (length bq))))
        (cong (λ n → s + n) (sym (len++ bp bq)))

iget-p-ns : ∀ pre (x : String) bp bq post {ns : List String} →
            ns ≡ pre ++ (x ∷ (bp ++ bq)) ++ post →
            ns ≡ (pre ++ (x ∷ [])) ++ bp ++ (bq ++ post)
iget-p-ns pre x bp bq post eq =
  trans eq (trans (cong (λ ys → pre ++ (x ∷ ys)) (++assoc bp bq post))
                  (sym (++assoc pre (x ∷ []) (bp ++ (bq ++ post)))))

iget-q-ns : ∀ pre (x : String) bp bq post {ns : List String} →
            ns ≡ pre ++ (x ∷ (bp ++ bq)) ++ post →
            ns ≡ (pre ++ (x ∷ bp)) ++ bq ++ post
iget-q-ns pre x bp bq post eq =
  trans eq (trans (cong (λ ys → pre ++ (x ∷ ys)) (++assoc bp bq post))
                  (sym (++assoc pre (x ∷ bp) (bq ++ post))))

iget-q-slot : ∀ {s s1} pre (x : String) bp →
              s1 ≡ suc s + length bp → s ≡ length pre →
              s1 ≡ length (pre ++ (x ∷ bp))
iget-q-slot {s} {s1} pre x bp end seq =
  trans (trans (subst-end end) (sym (+-suc (length pre) (length bp))))
        (sym (len++ pre (x ∷ bp)))
  where
  subst-end : s1 ≡ suc s + length bp → s1 ≡ suc (length pre) + length bp
  subst-end eq = trans eq (cong (λ z → suc z + length bp) seq)

iget-end : ∀ {s s1 s2} (bp bq : List String) →
           s1 ≡ suc s + length bp → s2 ≡ s1 + length bq →
           s2 ≡ s + suc (length (bp ++ bq))
iget-end {s} {_} {_} bp bq e1 e2 =
  trans (trans e2 (cong (λ z → z + length bq) e1))
    (trans (cong suc (+-assoc s (length bp) (length bq)))
      (trans (sym (+-suc s (length bp + length bq)))
        (cong (λ n → s + n) (cong suc (sym (len++ bp bq))))))

------------------------------------------------------------------------
-- Lifts. Each one rewrites the body's result into the parent `with`.
------------------------------------------------------------------------

done-at : ∀ pend ρ renv venv n s →
          Same n s [] (walk pend ρ sdone n s) (compile rdone pend renv venv s n)
done-at pend ρ renv venv n s =
  both-ok (mkW n s (suc n) s) ((n , bDone) ∷ []) (sym (+-idr s)) (o1 o0)

stop-at : ∀ pend ρ renv venv n s →
          Same n s [] (walk pend ρ sstop n s) (compile rstop pend renv venv s n)
stop-at pend ρ renv venv n s =
  both-ok (mkW n s (suc n) s) ((n , bStop) ∷ []) (sym (+-idr s)) (o1 o0)

var-apply : ∀ n s y pend ρ renv venv →
            Seen ρ renv y → (b : Bool) → elemS y pend ≡ b →
            Same n s [] (walk pend ρ (svar y) n s)
              (compile (rvar y) pend renv venv s n)
var-apply n s y pend ρ renv venv seen true eq rewrite eq = both-bad
var-apply n s y pend ρ renv venv (seen-no eqi eqn) false eq
  rewrite eq | eqi | eqn = both-bad
var-apply n s y pend ρ renv venv (seen-yes i s0 eqi eqn) false eq
  rewrite eq | eqi | eqn =
  both-ok (mkW i s0 n s) [] (sym (+-idr s)) o0

put-bad : ∀ {n s} (a : Pay) {p pend ρ renv venv q atom f} →
          walk [] (addPend pend n s ρ) p (suc n) s ≡ nothing →
          compile q [] (addNames pend n renv) venv s (suc n) ≡ cfail f →
          Same n s (bnames (sput a p))
            (walk pend ρ (sput a p) n s)
            (compile (rput atom q) pend renv venv s n)
put-bad a eqw eqc rewrite eqw | eqc = both-bad

put-ok : ∀ {n s} (a : Pay) {p pend ρ renv venv w bs} (q : RProc) (atom : Atom) →
         walk [] (addPend pend n s ρ) p (suc n) s ≡ just w →
         compile q [] (addNames pend n renv) venv s (suc n) ≡
           cok (entry w) (next w) (slotN w) bs →
         slotN w ≡ s + length (bnames p) →
         Ord (suc n) (next w) bs →
         Same n s (bnames (sput a p))
           (walk pend ρ (sput a p) n s)
           (compile (rput atom q) pend renv venv s n)
put-ok {n} {s} a {w = w} {bs = bs} q atom eqw eqc end od rewrite eqw | eqc =
  both-ok (mkW n s (next w) (slotN w)) ((n , bPut atom (entry w)) ∷ bs) end (o1 od)

on-lit : ∀ n s (a : Pay) p pend ρ renv venv q atom {mw co} →
         Same (suc n) s (bnames p) mw co →
         mw ≡ walk [] (addPend pend n s ρ) p (suc n) s →
         co ≡ compile q [] (addNames pend n renv) venv s (suc n) →
         Same n s (bnames (sput a p))
           (walk pend ρ (sput a p) n s)
           (compile (rput atom q) pend renv venv s n)
on-lit n s a p pend ρ renv venv q atom (both-bad {f}) eqw eqc =
  put-bad {n} {s} a {p} {pend} {ρ} {renv} {venv} {q} {atom} {f} (sym eqw) (sym eqc)
on-lit n s a p pend ρ renv venv q atom (both-ok w bs end od) eqw eqc =
  put-ok {n} {s} a {p} {pend} {ρ} {renv} {venv} {w} {bs} q atom
    (sym eqw) (sym eqc) end od

echo-bad : ∀ {n s x sX p pend ρ renv venv q f} →
           lookupN x venv ≡ just sX →
           walk [] (addPend pend n s ρ) p (suc n) s ≡ nothing →
           compile q [] (addNames pend n renv) venv s (suc n) ≡ cfail f →
           Same n s (bnames (sput (pEcho x) p))
             (walk pend ρ (sput (pEcho x) p) n s)
             (compile (recho x q) pend renv venv s n)
echo-bad lkup eqw eqc rewrite lkup | eqw | eqc = both-bad

echo-ok : ∀ {n s x sX p pend ρ renv venv w bs q} →
          lookupN x venv ≡ just sX →
          walk [] (addPend pend n s ρ) p (suc n) s ≡ just w →
          compile q [] (addNames pend n renv) venv s (suc n) ≡
            cok (entry w) (next w) (slotN w) bs →
          slotN w ≡ s + length (bnames p) →
          Ord (suc n) (next w) bs →
          Same n s (bnames (sput (pEcho x) p))
            (walk pend ρ (sput (pEcho x) p) n s)
            (compile (recho x q) pend renv venv s n)
echo-ok {n} {s} {x} {sX} {w = w} {bs = bs} lkup eqw eqc end od
  rewrite lkup | eqw | eqc =
  both-ok (mkW n s (next w) (slotN w)) ((n , bEcho sX (entry w)) ∷ bs) end (o1 od)

on-echo : ∀ n s x sX p pend ρ renv venv q {mw co} →
          lookupN x venv ≡ just sX →
          Same (suc n) s (bnames p) mw co →
          mw ≡ walk [] (addPend pend n s ρ) p (suc n) s →
          co ≡ compile q [] (addNames pend n renv) venv s (suc n) →
          Same n s (bnames (sput (pEcho x) p))
            (walk pend ρ (sput (pEcho x) p) n s)
            (compile (recho x q) pend renv venv s n)
on-echo n s x sX p pend ρ renv venv q lkup (both-bad {f}) eqw eqc =
  echo-bad {n} {s} {x} {sX} {p} {pend} {ρ} {renv} {venv} {q} {f}
    lkup (sym eqw) (sym eqc)
on-echo n s x sX p pend ρ renv venv q lkup (both-ok w bs end od) eqw eqc =
  echo-ok {n} {s} {x} {sX} {p} {pend} {ρ} {renv} {venv} {w} {bs} {q}
    lkup (sym eqw) (sym eqc) end od

get-bad : ∀ {n s t x p pend ρ renv venv q f} →
          walk [] (addPend pend n s ρ) p (suc n) (suc s) ≡ nothing →
          compile q [] (addNames pend n renv) ((x , s) ∷ venv) (suc s) (suc n) ≡ cfail f →
          Same n s (bnames (sget t x p))
            (walk pend ρ (sget t x p) n s)
            (compile (rget t x q) pend renv venv s n)
get-bad eqw eqc rewrite eqw | eqc = both-bad

get-ok : ∀ {n s t x p pend ρ renv venv w bs q} →
         walk [] (addPend pend n s ρ) p (suc n) (suc s) ≡ just w →
         compile q [] (addNames pend n renv) ((x , s) ∷ venv) (suc s) (suc n) ≡
           cok (entry w) (next w) (slotN w) bs →
         slotN w ≡ suc s + length (bnames p) →
         Ord (suc n) (next w) bs →
         Same n s (bnames (sget t x p))
           (walk pend ρ (sget t x p) n s)
           (compile (rget t x q) pend renv venv s n)
get-ok {n} {s} {t} {x} {p} {w = w} {bs = bs} eqw eqc end od rewrite eqw | eqc =
  both-ok (mkW n s (next w) (slotN w)) ((n , bGet t s (entry w)) ∷ bs)
    (shift-end {s} {slotN w} {length (bnames p)} end) (o1 od)

on-get : ∀ n s t x p pend ρ renv venv q {mw co} →
         Same (suc n) (suc s) (bnames p) mw co →
         mw ≡ walk [] (addPend pend n s ρ) p (suc n) (suc s) →
         co ≡ compile q [] (addNames pend n renv) ((x , s) ∷ venv) (suc s) (suc n) →
         Same n s (bnames (sget t x p))
           (walk pend ρ (sget t x p) n s)
           (compile (rget t x q) pend renv venv s n)
on-get n s t x p pend ρ renv venv q (both-bad {f}) eqw eqc =
  get-bad {n} {s} {t} {x} {p} {pend} {ρ} {renv} {venv} {q} {f} (sym eqw) (sym eqc)
on-get n s t x p pend ρ renv venv q (both-ok w bs end od) eqw eqc =
  get-ok {n} {s} {t} {x} {p} {pend} {ρ} {renv} {venv} {w} {bs} {q}
    (sym eqw) (sym eqc) end od

pick0-bad : ∀ {n s p pend ρ renv venv q f} →
            walk [] (addPend pend n s ρ) p (suc n) s ≡ nothing →
            compile q [] (addNames pend n renv) venv s (suc n) ≡ cfail f →
            Same n s (bnames (spick0 p))
              (walk pend ρ (spick0 p) n s)
              (compile (rpick0 q) pend renv venv s n)
pick0-bad eqw eqc rewrite eqw | eqc = both-bad

pick0-ok : ∀ {n s p pend ρ renv venv w bs q} →
           walk [] (addPend pend n s ρ) p (suc n) s ≡ just w →
           compile q [] (addNames pend n renv) venv s (suc n) ≡
             cok (entry w) (next w) (slotN w) bs →
           slotN w ≡ s + length (bnames p) →
           Ord (suc n) (next w) bs →
           Same n s (bnames (spick0 p))
             (walk pend ρ (spick0 p) n s)
             (compile (rpick0 q) pend renv venv s n)
pick0-ok {n} {s} {w = w} {bs = bs} eqw eqc end od rewrite eqw | eqc =
  both-ok (mkW n s (next w) (slotN w)) ((n , bPick0 (entry w)) ∷ bs) end (o1 od)

on-pick0 : ∀ n s p pend ρ renv venv q {mw co} →
           Same (suc n) s (bnames p) mw co →
           mw ≡ walk [] (addPend pend n s ρ) p (suc n) s →
           co ≡ compile q [] (addNames pend n renv) venv s (suc n) →
           Same n s (bnames (spick0 p))
             (walk pend ρ (spick0 p) n s)
             (compile (rpick0 q) pend renv venv s n)
on-pick0 n s p pend ρ renv venv q (both-bad {f}) eqw eqc =
  pick0-bad {n} {s} {p} {pend} {ρ} {renv} {venv} {q} {f} (sym eqw) (sym eqc)
on-pick0 n s p pend ρ renv venv q (both-ok w bs end od) eqw eqc =
  pick0-ok {n} {s} {p} {pend} {ρ} {renv} {venv} {w} {bs} {q}
    (sym eqw) (sym eqc) end od

pick1-bad : ∀ {n s p pend ρ renv venv q f} →
            walk [] (addPend pend n s ρ) p (suc n) s ≡ nothing →
            compile q [] (addNames pend n renv) venv s (suc n) ≡ cfail f →
            Same n s (bnames (spick1 p))
              (walk pend ρ (spick1 p) n s)
              (compile (rpick1 q) pend renv venv s n)
pick1-bad eqw eqc rewrite eqw | eqc = both-bad

pick1-ok : ∀ {n s p pend ρ renv venv w bs q} →
           walk [] (addPend pend n s ρ) p (suc n) s ≡ just w →
           compile q [] (addNames pend n renv) venv s (suc n) ≡
             cok (entry w) (next w) (slotN w) bs →
           slotN w ≡ s + length (bnames p) →
           Ord (suc n) (next w) bs →
           Same n s (bnames (spick1 p))
             (walk pend ρ (spick1 p) n s)
             (compile (rpick1 q) pend renv venv s n)
pick1-ok {n} {s} {w = w} {bs = bs} eqw eqc end od rewrite eqw | eqc =
  both-ok (mkW n s (next w) (slotN w)) ((n , bPick1 (entry w)) ∷ bs) end (o1 od)

on-pick1 : ∀ n s p pend ρ renv venv q {mw co} →
           Same (suc n) s (bnames p) mw co →
           mw ≡ walk [] (addPend pend n s ρ) p (suc n) s →
           co ≡ compile q [] (addNames pend n renv) venv s (suc n) →
           Same n s (bnames (spick1 p))
             (walk pend ρ (spick1 p) n s)
             (compile (rpick1 q) pend renv venv s n)
on-pick1 n s p pend ρ renv venv q (both-bad {f}) eqw eqc =
  pick1-bad {n} {s} {p} {pend} {ρ} {renv} {venv} {q} {f} (sym eqw) (sym eqc)
on-pick1 n s p pend ρ renv venv q (both-ok w bs end od) eqw eqc =
  pick1-ok {n} {s} {p} {pend} {ρ} {renv} {venv} {w} {bs} {q}
    (sym eqw) (sym eqc) end od

cover-bad : ∀ {n s p q pend ρ renv venv q1 q2 f} →
            walk [] (addPend pend n s ρ) p (suc n) s ≡ nothing →
            compile q1 [] (addNames pend n renv) venv s (suc n) ≡ cfail f →
            Same n s (bnames (scover p q))
              (walk pend ρ (scover p q) n s)
              (compile (rcover q1 q2) pend renv venv s n)
cover-bad eqw eqc rewrite eqw | eqc = both-bad

cover-miss : ∀ {n s p q pend ρ renv venv q1 q2 w bs f} →
             walk [] (addPend pend n s ρ) p (suc n) s ≡ just w →
             compile q1 [] (addNames pend n renv) venv s (suc n) ≡
               cok (entry w) (next w) (slotN w) bs →
             walk [] (addPend pend n s ρ) q (next w) (slotN w) ≡ nothing →
             compile q2 [] (addNames pend n renv) venv (slotN w) (next w) ≡ cfail f →
             Same n s (bnames (scover p q))
               (walk pend ρ (scover p q) n s)
               (compile (rcover q1 q2) pend renv venv s n)
cover-miss eqw eqc eqw2 eqc2 rewrite eqw | eqc | eqw2 | eqc2 = both-bad

cover-hit : ∀ {n s p q pend ρ renv venv q1 q2 w1 bs1 w2 bs2} →
            walk [] (addPend pend n s ρ) p (suc n) s ≡ just w1 →
            compile q1 [] (addNames pend n renv) venv s (suc n) ≡
              cok (entry w1) (next w1) (slotN w1) bs1 →
            walk [] (addPend pend n s ρ) q (next w1) (slotN w1) ≡ just w2 →
            compile q2 [] (addNames pend n renv) venv (slotN w1) (next w1) ≡
              cok (entry w2) (next w2) (slotN w2) bs2 →
            slotN w1 ≡ s + length (bnames p) →
            slotN w2 ≡ slotN w1 + length (bnames q) →
            Ord (suc n) (next w1) bs1 →
            Ord (next w1) (next w2) bs2 →
            Same n s (bnames (scover p q))
              (walk pend ρ (scover p q) n s)
              (compile (rcover q1 q2) pend renv venv s n)
cover-hit {n} {s} {p} {q} {w1 = w1} {bs1 = bs1} {w2 = w2} {bs2 = bs2}
  eqw eqc eqw2 eqc2 e1 e2 od1 od2 rewrite eqw | eqc | eqw2 | eqc2 =
  both-ok (mkW n s (next w2) (slotN w2))
    ((n , bCover (entry w1) (entry w2)) ∷ bs1 ++ bs2)
    (sum-len (bnames p) (bnames q) e1 e2)
    (o1 (ord-cat od1 od2))

iget-bad : ∀ {n s x p q pend ρ renv venv q1 q2 f} →
           walk [] (addPend pend n s ρ) p (suc n) (suc s) ≡ nothing →
           compile q1 [] (addNames pend n renv) ((x , s) ∷ venv) (suc s) (suc n) ≡ cfail f →
           Same n s (bnames (siget x p q))
             (walk pend ρ (siget x p q) n s)
             (compile (riget x q1 q2) pend renv venv s n)
iget-bad eqw eqc rewrite eqw | eqc = both-bad

iget-miss : ∀ {n s x p q pend ρ renv venv q1 q2 w bs f} →
            walk [] (addPend pend n s ρ) p (suc n) (suc s) ≡ just w →
            compile q1 [] (addNames pend n renv) ((x , s) ∷ venv) (suc s) (suc n) ≡
              cok (entry w) (next w) (slotN w) bs →
            walk [] (addPend pend n s ρ) q (next w) (slotN w) ≡ nothing →
            compile q2 [] (addNames pend n renv) ((x , s) ∷ venv) (slotN w) (next w) ≡ cfail f →
            Same n s (bnames (siget x p q))
              (walk pend ρ (siget x p q) n s)
              (compile (riget x q1 q2) pend renv venv s n)
iget-miss eqw eqc eqw2 eqc2 rewrite eqw | eqc | eqw2 | eqc2 = both-bad

iget-hit : ∀ {n s x p q pend ρ renv venv q1 q2 w1 bs1 w2 bs2} →
           walk [] (addPend pend n s ρ) p (suc n) (suc s) ≡ just w1 →
           compile q1 [] (addNames pend n renv) ((x , s) ∷ venv) (suc s) (suc n) ≡
             cok (entry w1) (next w1) (slotN w1) bs1 →
           walk [] (addPend pend n s ρ) q (next w1) (slotN w1) ≡ just w2 →
           compile q2 [] (addNames pend n renv) ((x , s) ∷ venv) (slotN w1) (next w1) ≡
             cok (entry w2) (next w2) (slotN w2) bs2 →
           slotN w1 ≡ suc s + length (bnames p) →
           slotN w2 ≡ slotN w1 + length (bnames q) →
           Ord (suc n) (next w1) bs1 →
           Ord (next w1) (next w2) bs2 →
           Same n s (bnames (siget x p q))
             (walk pend ρ (siget x p q) n s)
             (compile (riget x q1 q2) pend renv venv s n)
iget-hit {n} {s} {x} {p} {q} {w1 = w1} {bs1 = bs1} {w2 = w2} {bs2 = bs2}
  eqw eqc eqw2 eqc2 e1 e2 od1 od2 rewrite eqw | eqc | eqw2 | eqc2 =
  both-ok (mkW n s (next w2) (slotN w2))
    ((n , bIget s (entry w1) (entry w2)) ∷ bs1 ++ bs2)
    (iget-end (bnames p) (bnames q) e1 e2)
    (o1 (ord-cat od1 od2))

mget-bad : ∀ {n s t x as pend ρ renv venv qs f} →
           walkArms [] (addPend pend n s ρ) as (suc n) (suc s) ≡ nothing →
           compileArms qs (addNames pend n renv) ((x , s) ∷ venv) (suc s) (suc n) ≡
             (cfail f , [] , []) →
           Same n s (bnames (smget t x as))
             (walk pend ρ (smget t x as) n s)
             (compile (rmget t x qs) pend renv venv s n)
mget-bad eqw eqc rewrite eqw | eqc = both-bad

mget-ok : ∀ {n s t x as pend ρ renv venv qs ws n2 s2 bs} →
          walkArms [] (addPend pend n s ρ) as (suc n) (suc s) ≡ just (ws , n2 , s2) →
          compileArms qs (addNames pend n renv) ((x , s) ∷ venv) (suc s) (suc n) ≡
            (cok n2 n2 s2 [] , ents ws , bs) →
          s2 ≡ suc s + length (bnamesArms as) →
          Ord (suc n) n2 bs →
          Same n s (bnames (smget t x as))
            (walk pend ρ (smget t x as) n s)
            (compile (rmget t x qs) pend renv venv s n)
mget-ok {n} {s} {t} {x} {as} {ws = ws} {n2 = n2} {s2 = s2} {bs = bs}
  eqw eqc end od rewrite eqw | eqc =
  both-ok (mkW n s n2 s2) ((n , bMget t s (ents ws)) ∷ bs)
    (shift-end {s} {s2} {length (bnamesArms as)} end) (o1 od)

arm-bad : ∀ {n s y p as ρ renv venv q qs f} →
          walk [] ρ p n s ≡ nothing →
          compile q [] renv venv s n ≡ cfail f →
          SameA n s (bnamesArms (aok y p ∷ as))
            (walkArms [] ρ (aok y p ∷ as) n s)
            (compileArms ((y , q) ∷ qs) renv venv s n)
arm-bad eqw eqc rewrite eqw | eqc = arms-bad

arm-miss : ∀ {n s y p as ρ renv venv q qs w bs f} →
           walk [] ρ p n s ≡ just w →
           compile q [] renv venv s n ≡ cok (entry w) (next w) (slotN w) bs →
           walkArms [] ρ as (next w) (slotN w) ≡ nothing →
           compileArms qs renv venv (slotN w) (next w) ≡ (cfail f , [] , []) →
           SameA n s (bnamesArms (aok y p ∷ as))
             (walkArms [] ρ (aok y p ∷ as) n s)
             (compileArms ((y , q) ∷ qs) renv venv s n)
arm-miss eqw eqc eqa eqc2 rewrite eqw | eqc | eqa | eqc2 = arms-bad

arm-hit : ∀ {n s y p as ρ renv venv q qs w bs1 ws n2 s2 bs2} →
          walk [] ρ p n s ≡ just w →
          compile q [] renv venv s n ≡ cok (entry w) (next w) (slotN w) bs1 →
          walkArms [] ρ as (next w) (slotN w) ≡ just (ws , n2 , s2) →
          compileArms qs renv venv (slotN w) (next w) ≡ (cok n2 n2 s2 [] , ents ws , bs2) →
          slotN w ≡ s + length (bnames p) →
          s2 ≡ slotN w + length (bnamesArms as) →
          Ord n (next w) bs1 →
          Ord (next w) n2 bs2 →
          SameA n s (bnamesArms (aok y p ∷ as))
            (walkArms [] ρ (aok y p ∷ as) n s)
            (compileArms ((y , q) ∷ qs) renv venv s n)
arm-hit {n} {s} {y} {p} {as} {w = w} {bs1 = bs1} {ws = ws} {n2 = n2} {s2 = s2} {bs2 = bs2}
  eqw eqc eqa eqc2 e1 e2 od1 od2 rewrite eqw | eqc | eqa | eqc2 =
  arms-ok ((y , w) ∷ ws) n2 s2 (bs1 ++ bs2)
    (sum-len (bnames p) (bnamesArms as) e1 e2)
    (ord-cat od1 od2)

------------------------------------------------------------------------
-- The agreement. Recursion follows the fragment proof.
------------------------------------------------------------------------

mutual
  agree : (P : SProc) (fp : Frag P) (pend : List String) (ρ : EnvI) (renv : REnv)
          (venv : VEnv) (ns scope pre post : List String) (n slot : ℕ) →
          ERel ρ renv → EchoRel venv ns scope →
          echoOk ns scope P ≡ true →
          slot ≡ length pre →
          ns ≡ pre ++ bnames P ++ post →
          Same n slot (bnames P)
            (walk pend ρ P n slot)
            (compile (elab P fp) pend renv venv slot n)

  agree sdone fdone pend ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    done-at pend ρ renv venv n slot
  agree sstop fstop pend ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    stop-at pend ρ renv venv n slot
  agree (sput .(pNat a) p) (fput (fnat a) fp) pend ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    on-lit n slot (pNat a) p pend ρ renv venv (elab p fp) (aNat a)
      (agree p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv
         ns scope pre post (suc n) slot (add-rel pend n slot rel) er (∧-right ok) seq nseq)
      refl refl
  agree (sput .(pBit b) p) (fput (fbit b) fp) pend ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    on-lit n slot (pBit b) p pend ρ renv venv (elab p fp) (aBit b)
      (agree p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv
         ns scope pre post (suc n) slot (add-rel pend n slot rel) er (∧-right ok) seq nseq)
      refl refl
  agree (sput .(pCon y) p) (fput (fcon y) fp) pend ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    on-lit n slot (pCon y) p pend ρ renv venv (elab p fp) (aCon y)
      (agree p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv
         ns scope pre post (suc n) slot (add-rel pend n slot rel) er (∧-right ok) seq nseq)
      refl refl
  agree (sput .(pEcho x) p) (fput (fecho x) fp) pend ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    on-echo n slot x (proj₁ heard) p pend ρ renv venv (elab p fp) (proj₁ (proj₂ heard))
      (agree p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv
         ns scope pre post (suc n) slot (add-rel pend n slot rel) er (∧-right ok) seq nseq)
      refl refl
    where
    heard : Σ ℕ (λ sX → lookupN x venv ≡ just sX × findS x ns ≡ just sX)
    heard = er x (∧-right {once x ns} {elemS x scope} inScope) (∧-left {once x ns} {elemS x scope} inScope)
      where
      inScope = ∧-left {once x ns ∧ elemS x scope} {echoOk ns scope p} ok
  agree (sget t x p) (fget fp) pend ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    on-get n slot t x p pend ρ renv venv (elab p fp)
      (agree p fp [] (addPend pend n slot ρ) (addNames pend n renv)
         ((x , slot) ∷ venv) ns (x ∷ scope) (pre ++ (x ∷ [])) post (suc n) (suc slot)
         (add-rel pend n slot rel)
         (echo-extend pre (bnames p ++ post) x slot er nseq seq)
         ok (get-slot pre x slot seq) (get-names pre x (bnames p) post nseq))
      refl refl
  agree (spick0 p) (fpick0 fp) pend ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    on-pick0 n slot p pend ρ renv venv (elab p fp)
      (agree p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv
         ns scope pre post (suc n) slot (add-rel pend n slot rel) er ok seq nseq)
      refl refl
  agree (spick1 p) (fpick1 fp) pend ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    on-pick1 n slot p pend ρ renv venv (elab p fp)
      (agree p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv
         ns scope pre post (suc n) slot (add-rel pend n slot rel) er ok seq nseq)
      refl refl
  agree (scover p q) (fcover fp fq) pend ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    cover-go (agree p fp [] (addPend pend n slot ρ) (addNames pend n renv) venv
               ns scope pre (bnames q ++ post) (suc n) slot
               (add-rel pend n slot rel) er (∧-left ok) seq
               (split-left pre (bnames p) (bnames q) post nseq))
             refl refl
    where
    cover-more : ∀ w bs end od →
                 walk [] (addPend pend n slot ρ) p (suc n) slot ≡ just w →
                 compile (elab p fp) [] (addNames pend n renv) venv slot (suc n) ≡
                   cok (entry w) (next w) (slotN w) bs →
                 ∀ {mw2 co2} → Same (next w) (slotN w) (bnames q) mw2 co2 →
                 mw2 ≡ walk [] (addPend pend n slot ρ) q (next w) (slotN w) →
                 co2 ≡ compile (elab q fq) [] (addNames pend n renv) venv (slotN w) (next w) →
                 Same n slot (bnames (scover p q))
                   (walk pend ρ (scover p q) n slot)
                   (compile (rcover (elab p fp) (elab q fq)) pend renv venv slot n)
    cover-more w bs end od eqw eqc (both-bad {f}) eqw2 eqc2 =
      cover-miss {n} {slot} {p} {q} {pend} {ρ} {renv} {venv}
        {elab p fp} {elab q fq} {w} {bs} {f} eqw eqc (sym eqw2) (sym eqc2)
    cover-more w bs end od eqw eqc (both-ok w2 bs2 end2 od2) eqw2 eqc2 =
      cover-hit {n} {slot} {p} {q} {pend} {ρ} {renv} {venv}
        {elab p fp} {elab q fq} {w} {bs} {w2} {bs2}
        eqw eqc (sym eqw2) (sym eqc2) end end2 od od2
    cover-go : ∀ {mw co} → Same (suc n) slot (bnames p) mw co →
               mw ≡ walk [] (addPend pend n slot ρ) p (suc n) slot →
               co ≡ compile (elab p fp) [] (addNames pend n renv) venv slot (suc n) →
               Same n slot (bnames (scover p q))
                 (walk pend ρ (scover p q) n slot)
                 (compile (rcover (elab p fp) (elab q fq)) pend renv venv slot n)
    cover-go (both-bad {f}) eqw eqc =
      cover-bad {n} {slot} {p} {q} {pend} {ρ} {renv} {venv} {elab p fp} {elab q fq} {f}
        (sym eqw) (sym eqc)
    cover-go (both-ok w bs end od) eqw eqc =
      cover-more w bs end od (sym eqw) (sym eqc)
        (agree q fq [] (addPend pend n slot ρ) (addNames pend n renv) venv
           ns scope (pre ++ bnames p) post (next w) (slotN w)
           (add-rel pend n slot rel) er (∧-right ok)
           (cat-slot pre (bnames p) end seq)
           (split-right pre (bnames p) (bnames q) post nseq))
        refl refl

  agree (siget x p q) (figet fp fq) pend ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    iget-go (agree p fp [] (addPend pend n slot ρ) (addNames pend n renv) venvX
              ns scopeX preX (bnames q ++ post) (suc n) (suc slot)
              (add-rel pend n slot rel) erX (∧-left ok)
              (get-slot pre x slot seq) (iget-p-ns pre x (bnames p) (bnames q) post nseq))
            refl refl
    where
    scopeX = x ∷ scope
    venvX = (x , slot) ∷ venv
    preX = pre ++ (x ∷ [])
    erX = echo-extend pre ((bnames p ++ bnames q) ++ post) x slot er nseq seq
    iget-more : ∀ w bs end od →
                walk [] (addPend pend n slot ρ) p (suc n) (suc slot) ≡ just w →
                compile (elab p fp) [] (addNames pend n renv) venvX (suc slot) (suc n) ≡
                  cok (entry w) (next w) (slotN w) bs →
                ∀ {mw2 co2} → Same (next w) (slotN w) (bnames q) mw2 co2 →
                mw2 ≡ walk [] (addPend pend n slot ρ) q (next w) (slotN w) →
                co2 ≡ compile (elab q fq) [] (addNames pend n renv) venvX (slotN w) (next w) →
                Same n slot (bnames (siget x p q))
                  (walk pend ρ (siget x p q) n slot)
                  (compile (riget x (elab p fp) (elab q fq)) pend renv venv slot n)
    iget-more w bs end od eqw eqc (both-bad {f}) eqw2 eqc2 =
      iget-miss {n} {slot} {x} {p} {q} {pend} {ρ} {renv} {venv}
        {elab p fp} {elab q fq} {w} {bs} {f} eqw eqc (sym eqw2) (sym eqc2)
    iget-more w bs end od eqw eqc (both-ok w2 bs2 end2 od2) eqw2 eqc2 =
      iget-hit {n} {slot} {x} {p} {q} {pend} {ρ} {renv} {venv}
        {elab p fp} {elab q fq} {w} {bs} {w2} {bs2}
        eqw eqc (sym eqw2) (sym eqc2) end end2 od od2
    iget-go : ∀ {mw co} → Same (suc n) (suc slot) (bnames p) mw co →
              mw ≡ walk [] (addPend pend n slot ρ) p (suc n) (suc slot) →
              co ≡ compile (elab p fp) [] (addNames pend n renv) venvX (suc slot) (suc n) →
              Same n slot (bnames (siget x p q))
                (walk pend ρ (siget x p q) n slot)
                (compile (riget x (elab p fp) (elab q fq)) pend renv venv slot n)
    iget-go (both-bad {f}) eqw eqc =
      iget-bad {n} {slot} {x} {p} {q} {pend} {ρ} {renv} {venv} {elab p fp} {elab q fq} {f}
        (sym eqw) (sym eqc)
    iget-go (both-ok w bs end od) eqw eqc =
      iget-more w bs end od (sym eqw) (sym eqc)
        (agree q fq [] (addPend pend n slot ρ) (addNames pend n renv) venvX
           ns scopeX (pre ++ (x ∷ bnames p)) post (next w) (slotN w)
           (add-rel pend n slot rel) erX (∧-right ok)
           (iget-q-slot pre x (bnames p) end seq)
           (iget-q-ns pre x (bnames p) (bnames q) post nseq))
        refl refl

  agree (smget t x as) (fmget fas) pend ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    mget-go (agreeArms as fas (addPend pend n slot ρ) (addNames pend n renv)
              ((x , slot) ∷ venv) ns (x ∷ scope) (pre ++ (x ∷ [])) post (suc n) (suc slot)
              (add-rel pend n slot rel)
              (echo-extend pre (bnamesArms as ++ post) x slot er nseq seq)
              ok (get-slot pre x slot seq)
              (get-names pre x (bnamesArms as) post nseq))
            refl refl
    where
    mget-go : ∀ {mw co} →
              SameA (suc n) (suc slot) (bnamesArms as) mw co →
              mw ≡ walkArms [] (addPend pend n slot ρ) as (suc n) (suc slot) →
              co ≡ compileArms (elabArms as fas) (addNames pend n renv)
                     ((x , slot) ∷ venv) (suc slot) (suc n) →
              Same n slot (bnames (smget t x as))
                (walk pend ρ (smget t x as) n slot)
                (compile (rmget t x (elabArms as fas)) pend renv venv slot n)
    mget-go (arms-bad {f}) eqw eqc =
      mget-bad {n} {slot} {t} {x} {as} {pend} {ρ} {renv} {venv} {elabArms as fas} {f}
        (sym eqw) (sym eqc)
    mget-go (arms-ok ws n2 s2 bs end od) eqw eqc =
      mget-ok {n} {slot} {t} {x} {as} {pend} {ρ} {renv} {venv} {elabArms as fas}
        {ws} {n2} {s2} {bs} (sym eqw) (sym eqc) end od

  agree (smu x p) (fmu fp) pend ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    agree p fp (x ∷ pend) ρ renv venv ns scope pre post n slot rel er ok seq nseq
  agree (svar y) fvar pend ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    var-apply n slot y pend ρ renv venv (lookup-rel y rel) (elemS y pend) refl

  agreeArms : (as : List _) (fas : FragArms as) (ρ : EnvI) (renv : REnv) (venv : VEnv)
              (ns scope pre post : List String) (n slot : ℕ) →
              ERel ρ renv → EchoRel venv ns scope →
              echoOkArms ns scope as ≡ true →
              slot ≡ length pre →
              ns ≡ pre ++ bnamesArms as ++ post →
              SameA n slot (bnamesArms as)
                (walkArms [] ρ as n slot)
                (compileArms (elabArms as fas) renv venv slot n)
  agreeArms [] farms0 ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    arms-ok [] n slot [] (sym (+-idr slot)) o0
  agreeArms (aok y p ∷ as) (farms1 (farm fp) fas) ρ renv venv ns scope pre post n slot rel er ok seq nseq =
    arm-go (agree p fp [] ρ renv venv ns scope pre (bnamesArms as ++ post) n slot rel er
             (∧-left ok) seq (split-left pre (bnames p) (bnamesArms as) post nseq))
           refl refl
    where
    arm-more : ∀ w bs end od →
               walk [] ρ p n slot ≡ just w →
               compile (elab p fp) [] renv venv slot n ≡
                 cok (entry w) (next w) (slotN w) bs →
               ∀ {mw2 co2} → SameA (next w) (slotN w) (bnamesArms as) mw2 co2 →
               mw2 ≡ walkArms [] ρ as (next w) (slotN w) →
               co2 ≡ compileArms (elabArms as fas) renv venv (slotN w) (next w) →
               SameA n slot (bnamesArms (aok y p ∷ as))
                 (walkArms [] ρ (aok y p ∷ as) n slot)
                 (compileArms ((y , elab p fp) ∷ elabArms as fas) renv venv slot n)
    arm-more w bs end od eqw eqc (arms-bad {f}) eqa eqc2 =
      arm-miss {n} {slot} {y} {p} {as} {ρ} {renv} {venv}
        {elab p fp} {elabArms as fas} {w} {bs} {f}
        eqw eqc (sym eqa) (sym eqc2)
    arm-more w bs end od eqw eqc (arms-ok ws n2 s2 bs2 end2 od2) eqa eqc2 =
      arm-hit {n} {slot} {y} {p} {as} {ρ} {renv} {venv}
        {elab p fp} {elabArms as fas} {w} {bs} {ws} {n2} {s2} {bs2}
        eqw eqc (sym eqa) (sym eqc2) end end2 od od2
    arm-go : ∀ {mw co} → Same n slot (bnames p) mw co →
             mw ≡ walk [] ρ p n slot →
             co ≡ compile (elab p fp) [] renv venv slot n →
             SameA n slot (bnamesArms (aok y p ∷ as))
               (walkArms [] ρ (aok y p ∷ as) n slot)
               (compileArms (elabArms (aok y p ∷ as) (farms1 (farm fp) fas)) renv venv slot n)
    arm-go (both-bad {f}) eqw eqc =
      arm-bad {n} {slot} {y} {p} {as} {ρ} {renv} {venv} {elab p fp} {elabArms as fas} {f}
        (sym eqw) (sym eqc)
    arm-go (both-ok w bs end od) eqw eqc =
      arm-more w bs end od (sym eqw) (sym eqc)
        (agreeArms as fas ρ renv venv ns scope (pre ++ bnames p) post (next w) (slotN w)
           rel er (∧-right ok) (cat-slot pre (bnames p) end seq)
           (split-right pre (bnames p) (bnamesArms as) post nseq))
        refl refl

------------------------------------------------------------------------
-- The echo, which sends a received name, and the spin, which matches.
------------------------------------------------------------------------

echoA-ok : echoOk (bnames src-echoA) [] src-echoA ≡ true
echoA-ok = refl

root-ns : ∀ (P : SProc) → bnames P ≡ [] ++ bnames P ++ []
root-ns P = sym (++[] (bnames P))

echoA-same : Same zero zero (bnames src-echoA)
               (walk [] [] src-echoA zero zero)
               (compile (elab src-echoA echoAF) [] [] [] zero zero)
echoA-same =
  agree src-echoA echoAF [] [] [] [] (bnames src-echoA) [] [] [] zero zero
    er0 (echo-empty [] (bnames src-echoA)) echoA-ok refl (root-ns src-echoA)

echoB-same : Same zero zero (bnames src-echoB)
               (walk [] [] src-echoB zero zero)
               (compile (elab src-echoB echoBF) [] [] [] zero zero)
echoB-same =
  agree src-echoB echoBF [] [] [] [] (bnames src-echoB) [] [] [] zero zero
    er0 (echo-empty [] (bnames src-echoB)) echo-plain refl (root-ns src-echoB)

spinR-same : Same zero zero (bnames src-spinR)
               (walk [] [] src-spinR zero zero)
               (compile (elab src-spinR spinRF) [] [] [] zero zero)
spinR-same =
  agree src-spinR spinRF [] [] [] [] (bnames src-spinR) [] [] [] zero zero
    er0 (echo-empty [] (bnames src-spinR)) spin-plain refl (root-ns src-spinR)

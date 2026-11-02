------------------------------------------------------------------------
-- The buffered examples, closed by computation.
--
-- A `refl` on `holds`, `shapes`, or `checkLive` is the scan of the
-- breadth-first list. `yes-check`, `live-check`, and `no-check` turn
-- that scan into `Decide.check`. The abstract search inside
-- `Decide.check` is not unfolded.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Examples where

open import Data.Bool.Base using (true; false)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.String.Base using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Muro.AsyncRec using (Tag; tagDat)
open import Muro.Temporal
  using ( Role; left; right
        ; Verb; v-put
        ; Lit; l-nat
        ; StateProp; sp-imp; sp-at; sp-eq; sp-head; sp-empty; sp-done; sp-is
        ; always; eventually; leadsTo
        ; Answer; yes; no; Cex
        )
open import Muro.Temporal.Live using (LiveF; lev; lto; checkLive)
open import Muro.Temporal.Search using (bfs)
open import Muro.Temporal.Sound
  using ( holds; shapes; nostuck; yes-check; no-check; always-no
        ; closed-bfs; live-check; live-miss
        )
open import Muro.Temporal.Source
  using ( Pay; pCon
        ; Arm; aok
        ; SProc; sdone; sput; sget; smget
        ; src-echoA; src-echoB; src-spinL; src-spinR
        )
open import Muro.Temporal.Bridge
  using (Frag; FragPay; FragArm; FragArms; fput; fget; fcon; fmget; farm; farms0; farms1; fdone
        ; fromOk; graphOf; echoAF; echoBF; spinLF; spinRF)
import Muro.Temporal.Decide as Decide

echoG = fromOk (graphOf (suc zero) src-echoA src-echoB echoAF echoBF)

echo-count : length (bfs echoG) ≡ 8
echo-count = refl

echo-shapes : shapes echoG (bfs echoG) ≡ true
echo-shapes = refl

echo-m = nostuck echoG echo-shapes

-- echo-b's get is block 0. Its first put is the echo, block 1.
-- The binder `n` is slot 0.
echo-zero : StateProp
echo-zero = sp-imp (sp-at right (suc zero) v-put) (sp-eq right zero (l-nat zero))

echo-zero-holds : holds echoG echo-zero (bfs echoG) ≡ true
echo-zero-holds = refl

echo-returns-zero : Decide.check echoG echo-m (always echo-zero) ≡ yes
echo-returns-zero = yes-check echo-zero-holds echo-shapes

echo-back : StateProp
echo-back = sp-eq left zero (l-nat zero)

echo-answers-live :
  checkLive echoG (bfs echoG) (lev echo-back) (closed-bfs echo-shapes) ≡ yes
echo-answers-live = refl

echo-answers : Decide.check echoG echo-m (eventually echo-back) ≡ yes
echo-answers = live-check (lev echo-back) echo-shapes echo-answers-live

echo-wire : StateProp
echo-wire = sp-head right (l-nat zero)

echo-home : StateProp
echo-home = sp-head left (l-nat zero)

echo-answered-live :
  checkLive echoG (bfs echoG) (lto echo-wire echo-home) (closed-bfs echo-shapes) ≡ yes
echo-answered-live = refl

echo-answered : Decide.check echoG echo-m (leadsTo echo-wire echo-home) ≡ yes
echo-answered = live-check (lto echo-wire echo-home) echo-shapes echo-answered-live

------------------------------------------------------------------------
-- Spin. The inbox of the server is the right queue. It is not always
-- empty, and the server's done block is never reached.
------------------------------------------------------------------------

spinG = fromOk (graphOf (suc zero) src-spinL src-spinR spinLF spinRF)

spin-count : length (bfs spinG) ≡ 4
spin-count = refl

spin-shapes : shapes spinG (bfs spinG) ≡ true
spin-shapes = refl

spin-m = nostuck spinG spin-shapes

spin-empty : StateProp
spin-empty = sp-empty right

spin-drained-holds : holds spinG spin-empty (bfs spinG) ≡ false
spin-drained-holds = refl

spin-drained :
  Σ Cex (λ w → Decide.check spinG spin-m (always spin-empty) ≡ no w)
spin-drained =
  no-check spin-m (always spin-empty)
    (always-no spin-empty spin-drained-holds spin-shapes)

spin-end : StateProp
spin-end = sp-done right

spin-ends-at : Answer
spin-ends-at =
  checkLive spinG (bfs spinG) (lev spin-end) (closed-bfs spin-shapes)

miss-of : (a : Answer) → spin-ends-at ≡ a → Σ Cex (λ w → spin-ends-at ≡ no w)
miss-of yes ()
miss-of (no w) eq = w , eq

spin-ends-live : Σ Cex (λ w → spin-ends-at ≡ no w)
spin-ends-live = miss-of spin-ends-at refl

spin-ends :
  Σ Cex (λ w → Decide.check spinG spin-m (eventually spin-end) ≡ no w)
spin-ends =
  no-check spin-m (eventually spin-end)
    (live-miss (lev spin-end) spin-shapes (proj₂ spin-ends-live))

------------------------------------------------------------------------
-- Inflight. The client sends two frames and receives `rst`. The server
-- answers `rst` on every outer frame and then finishes the inner one.
------------------------------------------------------------------------

ctl : Tag
ctl = tagDat "Ctl"

frame : Tag
frame = tagDat "Frame"

src-client : SProc
src-client =
  sput (pCon "headers") (sput (pCon "trailers") (sget ctl "c" sdone))

doneArm : String → Arm
doneArm s = aok s sdone

inner : SProc
inner = smget frame "g" (doneArm "bytes" ∷ doneArm "trailers" ∷ doneArm "headers" ∷ [])

reply : String → Arm
reply s = aok s (sput (pCon "rst") inner)

src-server : SProc
src-server =
  smget frame "f" (reply "bytes" ∷ reply "trailers" ∷ reply "headers" ∷ [])

clientF : Frag src-client
clientF = fput (fcon "headers") (fput (fcon "trailers") (fget fdone))

doneAF : ∀ {s} → FragArm (doneArm s)
doneAF = farm fdone

innerF : Frag inner
innerF = fmget (farms1 doneAF (farms1 doneAF (farms1 doneAF farms0)))

replyF : ∀ {s} → FragArm (reply s)
replyF = farm (fput (fcon "rst") innerF)

serverF : Frag src-server
serverF = fmget (farms1 replyF (farms1 replyF (farms1 replyF farms0)))

flyG = fromOk (graphOf (suc zero) src-client src-server clientF serverF)

fly-count : length (bfs flyG) ≡ 9
fly-count = refl

fly-shapes : shapes flyG (bfs flyG) ≡ true
fly-shapes = refl

fly-m = nostuck flyG fly-shapes

fly-seen : StateProp
fly-seen = sp-imp (sp-done left) (sp-is left zero "rst")

fly-holds : holds flyG fly-seen (bfs flyG) ≡ true
fly-holds = refl

ctl-seen : Decide.check flyG fly-m (always fly-seen) ≡ yes
ctl-seen = yes-check fly-holds fly-shapes

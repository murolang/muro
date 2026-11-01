------------------------------------------------------------------------
-- Elaboration of a source process into the compiled graph.
--
-- `frag?` accepts nat literals, bits, nullary constructors, and an
-- echo of a received name. A pair, a record, a vector, a fielded
-- constructor, unit, and a computed put are outside it.
--
-- `graphOf` is `compile` on both sides, then `materialise` and
-- `alphabet`. `init-sim` is the start configuration: `abs` of that
-- source configuration is `init` of the graph.
--
-- `elab` of the loop, the crossing pair, the echo, and the spin is
-- the process the compiled graph already uses. `block-of` for those
-- processes is the block `lookB` reads, by computation.
--
-- `sim-fwd`, in `Muro.Temporal.Expose`, says a source step is the
-- graph step on `abs`. `bwd-put`, in `Muro.Temporal.Back`, reads a
-- graph step on a left put back as that source put when the place is
-- already the put and nothing is pending. `spine`, in
-- `Muro.Temporal.Reveal`, peels a `smu` and stops at a jump.
-- `Muro.Temporal.Chase` follows that jump to the `mu` it names.
-- `readL` and `readR` in `Muro.Temporal.Follow` agree with `abs`.
--
-- Under a cursor `Hold`, `sim-bwd` reads a graph step other than the
-- stutter as the source step, and `final-iff` in `Muro.Temporal.Carry`
-- says the source configuration is final exactly when `abs` of it is.
-- `SourceSafe` is weaker than `NoStuck`: one side can step beside a
-- fault, and `merge` returns `VBad`. `source-safe-iff` in
-- `Muro.Temporal.Span` uses `SourceShape` (every source-reachable view
-- is `Shape`) and equates that with `NoStuck` under `graphOf ≡ gok`,
-- `echoOk`, and `muOk`. `transfer` there equates `Satisfies` with
-- `SourceSatisfies` for `always`, `eventually`, and `leads_to`.
-- `check-yes` and `check-no` say `Decide.check` accepts exactly when
-- the source meeting satisfies the formula. `cex-source` reads a
-- refusal as a source run. Those statements quantify over `SConf`,
-- `_⟶ₛ_`, `abs`, `graphOf`, and `SourceSatisfies`. `sim-bwd` takes
-- the `Hold`, not a bare configuration: the cursor is what ties the
-- graph step to the source process.
--
-- `inj-fwd` and `inj-bwd` in `Muro.Temporal.Finite` are the two
-- directions of one embedded step. `Embed` relates an `Async.Conf`,
-- including its typed messages, value environments, and index
-- contexts, to the source configuration `inj` builds. `inj-fwd`
-- sends an async step to a graph step. `inj-bwd` reads a graph step
-- other than the stutter back as an async step, and it takes `Safe`:
-- a payload received as another declaration is a graph step and a
-- bad reception. `init-embed` is that relation at the start.
-- `safe→nostuck` says that under `graphOf ≡ gok`, `initS`, and
-- `echoOk`, a safe finite meeting is `NoStuck`. `muOk` of `inj`
-- holds whenever `Frag` does. `inj` is `sout` or `pOut` for a bare
-- arm, an arm list other than the declaration, a constructor the
-- declaration does not inhabit, an ill-typed echo, an open index, a
-- second binding of a name already in scope, or a name that occurs
-- twice anywhere in the process.
--
-- Importing `Muro.Temporal.Source` requires `--guardedness`. The
-- option is infective.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Bridge where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; inspect; [_])
open import Relation.Nullary.Decidable.Core using (Dec)
  renaming (yes to yes′; no to no′)

open import Muro.AsyncRec
  using ( Atom; aNat; aBit; aCon
        ; Tag; tagNat; tagDat
        ; RProc; rdone; rstop; rput; recho; rget; rpick0; rpick1
        ; rcover; riget; rmget; rmu; rvar
        ; Block; bDone; bPut; bGet; bEcho; bMget
        ; COut; cok; cfail; Fault
        ; compile; materialise; alphabet; elemS
        ; Graph; gr; init; lookB; replicate
        ; loopL; loopR; cross
        )
open Graph

open import Muro.Temporal
  using (Path; head; tail; Formula; Holds)

open import Muro.Temporal.Source
  using ( Pay; pNat; pBit; pCon; pEcho; pOut
        ; Arm; aok; abad
        ; SProc; sdone; sstop; sout; sput; sget; spick0; spick1
        ; scover; siget; smget; smu; svar
        ; SConf; sc; abs; bnames
        ; SPath; shead; stail; SIsRun
        ; payOf
        ; src-loopL; src-loopR; src-cross
        ; src-echoA; src-echoB; src-spinL; src-spinR
        )
import Muro.Session as S

------------------------------------------------------------------------
-- The fragment. Positive cases are the payloads the alphabet holds.
------------------------------------------------------------------------

data FragPay : Pay → Set where
  fnat : ∀ n → FragPay (pNat n)
  fbit : ∀ b → FragPay (pBit b)
  fcon : ∀ s → FragPay (pCon s)
  fecho : ∀ s → FragPay (pEcho s)

data Frag : SProc → Set
data FragArm : Arm → Set
data FragArms : List Arm → Set

data Frag where
  fdone : Frag sdone
  fstop : Frag sstop
  fput : ∀ {a p} → FragPay a → Frag p → Frag (sput a p)
  fget : ∀ {t x p} → Frag p → Frag (sget t x p)
  fpick0 : ∀ {p} → Frag p → Frag (spick0 p)
  fpick1 : ∀ {p} → Frag p → Frag (spick1 p)
  fcover : ∀ {p q} → Frag p → Frag q → Frag (scover p q)
  figet : ∀ {x p q} → Frag p → Frag q → Frag (siget x p q)
  fmget : ∀ {t x as} → FragArms as → Frag (smget t x as)
  fmu : ∀ {x p} → Frag p → Frag (smu x p)
  fvar : ∀ {x} → Frag (svar x)

data FragArm where
  farm : ∀ {s p} → Frag p → FragArm (aok s p)

data FragArms where
  farms0 : FragArms []
  farms1 : ∀ {a as} → FragArm a → FragArms as → FragArms (a ∷ as)

fragPay : Pay → Bool
fragPay (pNat _) = true
fragPay (pBit _) = true
fragPay (pCon _) = true
fragPay (pEcho _) = true
fragPay pOut = false

fragB : SProc → Bool
fragArm : Arm → Bool
fragArms : List Arm → Bool

fragB sdone = true
fragB sstop = true
fragB sout = false
fragB (sput a p) = fragPay a ∧ fragB p
fragB (sget _ _ p) = fragB p
fragB (spick0 p) = fragB p
fragB (spick1 p) = fragB p
fragB (scover p q) = fragB p ∧ fragB q
fragB (siget _ p q) = fragB p ∧ fragB q
fragB (smget _ _ as) = fragArms as
fragB (smu _ p) = fragB p
fragB (svar _) = true

fragArm (aok _ p) = fragB p
fragArm abad = false

fragArms [] = true
fragArms (a ∷ as) = fragArm a ∧ fragArms as

------------------------------------------------------------------------
-- An echo names one binder. Two bindings of the same name make the
-- source lookup and the compiled slot disagree, so `frag?` refuses it.
------------------------------------------------------------------------

occ : String → List String → ℕ
occ x [] = zero
occ x (y ∷ ys) with x == y
... | true = suc (occ x ys)
... | false = occ x ys

once : String → List String → Bool
once x ys with occ x ys
... | suc zero = true
... | zero = false
... | suc (suc _) = false

echoHere : List String → List String → Pay → Bool
echoHere ns scope (pEcho x) = once x ns ∧ elemS x scope
echoHere _ _ _ = true

echoOk : List String → List String → SProc → Bool
echoOkArms : List String → List String → List Arm → Bool

echoOk ns scope sdone = true
echoOk ns scope sstop = true
echoOk ns scope sout = true
echoOk ns scope (sput a p) = echoHere ns scope a ∧ echoOk ns scope p
echoOk ns scope (sget _ x p) = echoOk ns (x ∷ scope) p
echoOk ns scope (spick0 p) = echoOk ns scope p
echoOk ns scope (spick1 p) = echoOk ns scope p
echoOk ns scope (scover p q) = echoOk ns scope p ∧ echoOk ns scope q
echoOk ns scope (siget x p q) = echoOk ns (x ∷ scope) p ∧ echoOk ns (x ∷ scope) q
echoOk ns scope (smget _ x as) = echoOkArms ns (x ∷ scope) as
echoOk ns scope (smu _ p) = echoOk ns scope p
echoOk ns scope (svar _) = true

echoOkArms _ _ [] = true
echoOkArms ns scope (abad ∷ as) = echoOkArms ns scope as
echoOkArms ns scope (aok _ p ∷ as) = echoOk ns scope p ∧ echoOkArms ns scope as

-- A repeated `smu` binder is refused. Re-entering the outer binder would
-- otherwise see the inner one, and the compiled jump would not be the
-- jump the source walk takes.
mus : SProc → List String
musArms : List Arm → List String

mus sdone = []
mus sstop = []
mus sout = []
mus (sput _ p) = mus p
mus (sget _ _ p) = mus p
mus (spick0 p) = mus p
mus (spick1 p) = mus p
mus (scover p q) = mus p ++ mus q
mus (siget _ p q) = mus p ++ mus q
mus (smget _ _ as) = musArms as
mus (smu x p) = x ∷ mus p
mus (svar _) = []

musArms [] = []
musArms (abad ∷ as) = musArms as
musArms (aok _ p ∷ as) = mus p ++ musArms as

fresh : String → List String → Bool
fresh _ [] = true
fresh x (y ∷ ys) with x == y
... | true = false
... | false = fresh x ys

distinct : List String → Bool
distinct [] = true
distinct (x ∷ xs) = fresh x xs ∧ distinct xs

muOk : SProc → Bool
muOk P = distinct (mus P)

∧-left : ∀ {a b} → a ∧ b ≡ true → a ≡ true
∧-left {true} _ = refl
∧-left {false} ()

∧-right : ∀ {a b} → a ∧ b ≡ true → b ≡ true
∧-right {true} eq = eq
∧-right {false} ()

true≢false : true ≡ false → ⊥
true≢false ()

mutual
  pay-sound : ∀ a → fragPay a ≡ true → FragPay a
  pay-sound (pNat n) _ = fnat n
  pay-sound (pBit b) _ = fbit b
  pay-sound (pCon s) _ = fcon s
  pay-sound (pEcho s) _ = fecho s
  pay-sound pOut ()

  frag-sound : (P : SProc) → fragB P ≡ true → Frag P
  frag-sound sdone _ = fdone
  frag-sound sstop _ = fstop
  frag-sound sout ()
  frag-sound (sput a p) eq = fput (pay-sound a (∧-left eq)) (frag-sound p (∧-right eq))
  frag-sound (sget _ _ p) eq = fget (frag-sound p eq)
  frag-sound (spick0 p) eq = fpick0 (frag-sound p eq)
  frag-sound (spick1 p) eq = fpick1 (frag-sound p eq)
  frag-sound (scover p q) eq = fcover (frag-sound p (∧-left eq)) (frag-sound q (∧-right eq))
  frag-sound (siget _ p q) eq = figet (frag-sound p (∧-left eq)) (frag-sound q (∧-right eq))
  frag-sound (smget _ _ as) eq = fmget (arms-sound as eq)
  frag-sound (smu _ p) eq = fmu (frag-sound p eq)
  frag-sound (svar _) _ = fvar

  arm-sound : (a : Arm) → fragArm a ≡ true → FragArm a
  arm-sound (aok _ p) eq = farm (frag-sound p eq)
  arm-sound abad ()

  arms-sound : (as : List Arm) → fragArms as ≡ true → FragArms as
  arms-sound [] _ = farms0
  arms-sound (a ∷ as) eq = farms1 (arm-sound a (∧-left eq)) (arms-sound as (∧-right eq))

mutual
  pay-complete : ∀ {a} → FragPay a → fragPay a ≡ true
  pay-complete (fnat _) = refl
  pay-complete (fbit _) = refl
  pay-complete (fcon _) = refl
  pay-complete (fecho _) = refl

  frag-complete : ∀ {P} → Frag P → fragB P ≡ true
  frag-complete fdone = refl
  frag-complete fstop = refl
  frag-complete (fput fa fp) rewrite pay-complete fa | frag-complete fp = refl
  frag-complete (fget fp) = frag-complete fp
  frag-complete (fpick0 fp) = frag-complete fp
  frag-complete (fpick1 fp) = frag-complete fp
  frag-complete (fcover fp fq) rewrite frag-complete fp | frag-complete fq = refl
  frag-complete (figet fp fq) rewrite frag-complete fp | frag-complete fq = refl
  frag-complete (fmget fas) = arms-complete fas
  frag-complete (fmu fp) = frag-complete fp
  frag-complete fvar = refl

  arm-complete : ∀ {a} → FragArm a → fragArm a ≡ true
  arm-complete (farm fp) = frag-complete fp

  arms-complete : ∀ {as} → FragArms as → fragArms as ≡ true
  arms-complete farms0 = refl
  arms-complete (farms1 fa fas) rewrite arm-complete fa | arms-complete fas = refl

∧-intro : ∀ {a b} → a ≡ true → b ≡ true → (a ∧ b) ≡ true
∧-intro {true} {true} _ _ = refl
∧-intro {true} {false} _ ()
∧-intro {false} {_} () _

-- A process is accepted when it is in the fragment, every echo names
-- exactly one binder, and every `smu` binder is used once.
open? : SProc → Bool
open? P = (fragB P ∧ echoOk (bnames P) [] P) ∧ muOk P

frag? : (P : SProc) →
        Dec (Σ (Frag P) (λ _ → echoOk (bnames P) [] P ≡ true × muOk P ≡ true))
frag? P = go (fragB P) (echoOk (bnames P) [] P) (muOk P) refl refl refl
  where
  Accept = Σ (Frag P) (λ _ → echoOk (bnames P) [] P ≡ true × muOk P ≡ true)
  go : (a b c : Bool) → fragB P ≡ a → echoOk (bnames P) [] P ≡ b → muOk P ≡ c →
       Dec Accept
  go true true true eqf eqe eqm = yes′ (frag-sound P eqf , eqe , eqm)
  go false _ _ eqf _ _ = no′ λ { (fp , _) → true≢false (trans (sym (frag-complete fp)) eqf) }
  go true false _ _ eqe _ = no′ λ { (_ , eok , _) → true≢false (trans (sym eok) eqe) }
  go true true false _ _ eqm = no′ λ { (_ , _ , mok) → true≢false (trans (sym mok) eqm) }

echo-mu : muOk src-echoA ≡ true
echo-mu = refl

spin-mu : muOk src-spinR ≡ true
spin-mu = refl

------------------------------------------------------------------------
-- Outside the fragment: the payload forms the alphabet does not hold.
------------------------------------------------------------------------

ex-pair : payOf (S.lit (S.tup {S.nat} {S.bit} S.zero S.b0)) ≡ pOut
ex-pair = refl

ex-rec : ∀ {fs} {r : S.Row fs} → payOf (S.lit (S.rec r)) ≡ pOut
ex-rec = refl

ex-vec : payOf (S.lit (S.rep {S.nat} {S.nlit zero} S.zero)) ≡ pOut
ex-vec = refl

ex-field : payOf (S.lit (S.con {S.mkDecl "Box" zero []} {[]} "just"
              (S.scons S.nat S.zero S.snil))) ≡ pOut
ex-field = refl

ex-call : payOf (S.call {S.nat} "f" []) ≡ pOut
ex-call = refl

ex-unit : payOf (S.lit S.tt) ≡ pOut
ex-unit = refl

ex-out : Frag (sput pOut sdone) → ⊥
ex-out (fput () _)

------------------------------------------------------------------------
-- Elaboration. A jump stays a jump. An echo stays an echo.
------------------------------------------------------------------------

elab : (P : SProc) → Frag P → RProc
elabArms : (as : List Arm) → FragArms as → List (String × RProc)

elab sdone fdone = rdone
elab sstop fstop = rstop
elab (sput .(pNat n) p) (fput (fnat n) fp) = rput (aNat n) (elab p fp)
elab (sput .(pBit b) p) (fput (fbit b) fp) = rput (aBit b) (elab p fp)
elab (sput .(pCon s) p) (fput (fcon s) fp) = rput (aCon s) (elab p fp)
elab (sput .(pEcho s) p) (fput (fecho s) fp) = recho s (elab p fp)
elab (sget t x p) (fget fp) = rget t x (elab p fp)
elab (spick0 p) (fpick0 fp) = rpick0 (elab p fp)
elab (spick1 p) (fpick1 fp) = rpick1 (elab p fp)
elab (scover p q) (fcover fp fq) = rcover (elab p fp) (elab q fq)
elab (siget x p q) (figet fp fq) = riget x (elab p fp) (elab q fq)
elab (smget t x as) (fmget fas) = rmget t x (elabArms as fas)
elab (smu x p) (fmu fp) = rmu x (elab p fp)
elab (svar x) fvar = rvar x

elabArms [] farms0 = []
elabArms (aok s p ∷ as) (farms1 (farm fp) fas) = (s , elab p fp) ∷ elabArms as fas

loopF : Frag src-loopL
loopF = fmu (fput (fnat zero) fvar)

loopRF : Frag src-loopR
loopRF = fmu (fget fvar)

crossF : Frag src-cross
crossF = fput (fnat zero) (fget fdone)

echoAF : Frag src-echoA
echoAF = fmu (fput (fnat zero) (fget fvar))

echoBF : Frag src-echoB
echoBF = fmu (fget (fput (fecho "n") fvar))

echo-plain : echoOk (bnames src-echoB) [] src-echoB ≡ true
echo-plain = refl

spin-plain : echoOk (bnames src-spinR) [] src-spinR ≡ true
spin-plain = refl

spinLF : Frag src-spinL
spinLF = fmu (fput (fcon "bytes") fvar)

spinRF : Frag src-spinR
spinRF = fmu (fmget (farms1 (farm fvar) (farms1 (farm fdone) (farms1 (farm fdone) farms0))))

echoAR : RProc
echoAR = rmu "X" (rput (aNat zero) (rget tagNat "m" (rvar "X")))

echoBR : RProc
echoBR = rmu "Y" (rget tagNat "n" (recho "n" (rvar "Y")))

spinLR : RProc
spinLR = rmu "X" (rput (aCon "bytes") (rvar "X"))

spinRR : RProc
spinRR = rmu "Y" (rmget (tagDat "Frame") "f"
  (("bytes" , rvar "Y") ∷ ("trailers" , rdone) ∷ ("headers" , rdone) ∷ []))

elab-loop : elab src-loopL loopF ≡ loopL
elab-loop = refl

elab-loopR : elab src-loopR loopRF ≡ loopR
elab-loopR = refl

elab-cross : elab src-cross crossF ≡ cross
elab-cross = refl

elab-echoA : elab src-echoA echoAF ≡ echoAR
elab-echoA = refl

elab-echoB : elab src-echoB echoBF ≡ echoBR
elab-echoB = refl

elab-spinL : elab src-spinL spinLF ≡ spinLR
elab-spinL = refl

elab-spinR : elab src-spinR spinRF ≡ spinRR
elab-spinR = refl

------------------------------------------------------------------------
-- The graph, and the start configuration.
------------------------------------------------------------------------

data GOut : Set where
  gok : Graph → GOut
  gfail : Fault → GOut

compiled : (P : SProc) → Frag P → COut
compiled P fp = compile (elab P fp) [] [] [] zero zero

pack : ℕ → SProc → SProc → COut → COut → GOut × Maybe SConf
pack k P Q (cok eL nL sL bsL) (cok eR nR sR bsR) =
  let L = materialise nL zero bsL
      R = materialise nR zero bsR
      al = alphabet L R
      g = gr L R al k eL eR sL sR
  in gok g , just (sc k al eL eR zero zero [] [] (replicate sL) (replicate sR)
                      P Q (bnames P) (bnames Q) [] [] [] [])
pack _ _ _ (cfail f) _ = gfail f , nothing
pack _ _ _ (cok _ _ _ _) (cfail f) = gfail f , nothing

graphOf : ℕ → (P Q : SProc) → Frag P → Frag Q → GOut
graphOf k P Q fp fq = proj₁ (pack k P Q (compiled P fp) (compiled Q fq))

initS : ℕ → (P Q : SProc) → Frag P → Frag Q → Maybe SConf
initS k P Q fp fq = proj₂ (pack k P Q (compiled P fp) (compiled Q fq))

-- Both sides compiled: the projected start is the graph's start.
init-sim : ∀ k (P Q : SProc) (fp : Frag P) (fq : Frag Q) g c →
           graphOf k P Q fp fq ≡ gok g →
           initS k P Q fp fq ≡ just c →
           abs c ≡ init g
init-sim k P Q fp fq g c eqg eqc = go (compiled P fp) (compiled Q fq) eqg eqc
  where
  go : ∀ oL oR →
       proj₁ (pack k P Q oL oR) ≡ gok g →
       proj₂ (pack k P Q oL oR) ≡ just c →
       abs c ≡ init g
  go (cok _ _ _ _) (cok _ _ _ _) refl refl = refl
  go (cfail _) _ () _
  go (cok _ _ _ _) (cfail _) () _

fromOk : GOut → Graph
fromOk (gok g) = g
fromOk (gfail _) = gr [] [] [] zero zero zero zero zero

unjust : Maybe SConf → SConf
unjust (just c) = c
unjust nothing = sc zero [] zero zero zero zero [] [] [] [] sdone sdone [] [] [] [] [] []

ex-init-loop : abs (unjust (initS (suc zero) src-loopL src-loopR loopF loopRF))
             ≡ init (fromOk (graphOf (suc zero) src-loopL src-loopR loopF loopRF))
ex-init-loop = refl

------------------------------------------------------------------------
-- Blocks. The entry `compile` returns is the block of that action.
------------------------------------------------------------------------

-- The echo, the spin, and the crossing pair, read off the compiled table.
-- Distinct actions are distinct blocks: a put block is not a get block.

ex-block-loop : lookB (codeL (fromOk (graphOf (suc zero) src-loopL src-loopR loopF loopRF))) zero
              ≡ just (bPut (aNat zero) zero)
ex-block-loop = refl

ex-block-echo-put : lookB (codeL (fromOk (graphOf (suc zero) src-echoA src-echoB echoAF echoBF))) zero
                  ≡ just (bPut (aNat zero) (suc zero))
ex-block-echo-put = refl

ex-block-echo-get : lookB (codeL (fromOk (graphOf (suc zero) src-echoA src-echoB echoAF echoBF))) (suc zero)
                  ≡ just (bGet tagNat zero zero)
ex-block-echo-get = refl

ex-block-echo-distinct :
  lookB (codeL (fromOk (graphOf (suc zero) src-echoA src-echoB echoAF echoBF))) zero
  ≢ lookB (codeL (fromOk (graphOf (suc zero) src-echoA src-echoB echoAF echoBF))) (suc zero)
ex-block-echo-distinct ()

ex-block-spin : lookB (codeL (fromOk (graphOf (suc zero) src-spinL src-spinR spinLF spinRF))) zero
              ≡ just (bPut (aCon "bytes") zero)
ex-block-spin = refl

ex-block-spinR : lookB (codeR (fromOk (graphOf (suc zero) src-spinL src-spinR spinLF spinRF))) zero
               ≡ just (bMget (tagDat "Frame") zero
                        (("bytes" , zero) ∷ ("trailers" , suc zero) ∷ ("headers" , suc (suc zero)) ∷ []))
ex-block-spinR = refl

ex-block-cross : lookB (codeL (fromOk (graphOf (suc zero) src-cross src-cross crossF crossF))) zero
               ≡ just (bPut (aNat zero) (suc zero))
ex-block-cross = refl

------------------------------------------------------------------------
-- A source run satisfies a formula when the projected run does.
-- `transfer`, `check-yes`, `check-no`, and `cex-source` in
-- `Muro.Temporal.Span` are that equivalence and both directions of
-- `Decide.check`. They start from `init-hold`, so they take `echoOk`
-- and `muOk` on top of `graphOf ≡ gok`. `sim-bwd` is the backward step.
------------------------------------------------------------------------

absPath : SPath → Path
head (absPath π) = abs (shead π)
tail (absPath π) = absPath (stail π)

SourceSatisfies : Graph → SConf → Formula → Set
SourceSatisfies g c0 φ = ∀ π → shead π ≡ c0 → SIsRun π → Holds g φ (absPath π)

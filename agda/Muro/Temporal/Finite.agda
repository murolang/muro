------------------------------------------------------------------------
-- A finite buffered meeting, as `Muro.Async` runs it, is the source
-- meeting `inj` builds. `inj-fwd` and `inj-bwd` are the two directions
-- of that step. `safe→nostuck` says a safe finite meeting is a graph
-- with no deadlock.
--
-- `inj` refuses a bare arm, an arm list that is not the declaration,
-- a constructor the declaration does not inhabit, an echo whose type
-- is not the binder's type, and a payload type that still contains an
-- index variable. A second binding of a name already in scope is
-- `sout`. A name that occurs twice anywhere, including the two
-- branches of a cover or the arms of an `mget`, is `sout` as well.
-- `Frag` of the injection gives globally unique binder names, so the
-- graph's first slot and the typed step's latest value are that one
-- binding. `inj` builds no `mu`, so `muOk` holds whenever `Frag`
-- does. `echoOk` stays a premise of `init-embed` and `safe→nostuck`.
-- `inj-bwd` takes `Safe` and a step other than the stutter: `fits`
-- does not read the declaration, so a payload received as another
-- declaration is a graph step and a bad reception. `Safe` of the
-- start configuration excludes that reception.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Finite where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; length; reverse)
open import Data.List.Properties using (length-++; ++-assoc)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (+-suc; +-assoc; +-identityʳ; ≤-refl; ≤-trans; n≤1+n; n∸n≡0; _<?_; m≤n+m)
  renaming (_≟_ to _≟ℕ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_; _≟_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; inspect; [_])
open import Relation.Nullary.Decidable.Core using (Dec)
  renaming (yes to yes′; no to no′)
open import Relation.Nullary.Negation.Core using (¬_)

open import Muro.AsyncRec
  using ( Atom; aNat; aBit; aCon; eqA; elemA; addA; adds; lits; layers
        ; alphabet; findA; findGo; growCount; sucAll
        ; Block; bDone; bStop; bPut; bEcho; bGrow; bGet; bPick0; bPick1
        ; bCover; bIget; bMget
        ; lookB; Graph; replicate; room; COut; cok; cfail; halted
        ; Tok; pay; lab; nth; setNth; nthA; slotVal; fits; conOf
        ; Tag; tagNat; tagBit; tagDat
        ; Shape; sh-final; sh-step
        ; View; VFinal; VGo
        ; Reach; rhere; rstep
        ; RConf; init
        ; Act; AGo; AWait; ABad; reactL; reactR
        )
  renaming (lt to glt; view to gview)
open Graph

import Muro.Async as A
import Muro.Session as S

open import Muro.Temporal
  using ( Who; lside; rside; fin; Step; stepL; stepR; finish; NoStuck
        ; view-final; kid-step )
open import Muro.Temporal.Source
  using ( SProc; sdone; sstop; sout; sput; sget; spick0; spick1; scover; siget; smget
        ; smu; svar
        ; Pay; pNat; pBit; pCon; pEcho; pOut; asAtom
        ; Arm; aok; abad; SConf; sc; abs; W; mkW
        ; bnames; bnamesArms; walk; walkArms; armGo
        ; walkCont; walkEnd; walkTwo; walkM; walkArm; consArm
        ; EnvP; EnvI; addPend
        ; Focus; f-put; f-get; f-pick0; f-pick1; f-cover; f-iget; f-mget; f-done; f-stop
        ; Unfold; u-done; u-stop; u-put; u-get; u-pick0; u-pick1
        ; u-cover; u-iget; u-mget
        ; _⟶ₛ_; put-l; echo-l; pick0-l; pick1-l; get-l; cover0-l; cover1-l
        ; iget0-l; iget1-l; mget-l
        ; put-r; echo-r; pick0-r; pick1-r; get-r; cover0-r; cover1-r
        ; iget0-r; iget1-r; mget-r
        ; snoc; findS; go; inj; payIn; payVal; payClosed; bump
        ; closedTy; closedN; closedFs; closedTs
        ; lookupTy; goodGet; ctorsTy; matchArms; newName
        ; freshN; distinctN; inj-go; inj-sout; nullCtors; declName
        ; HaltF; h-done; h-stop
        )
open SConf
open W
open import Muro.Temporal.Bridge
  using ( Frag; fdone; fstop; fput; fget; fpick0; fpick1; fcover; figet; fmget
        ; FragPay; fnat; fbit; fcon; fecho
        ; FragArm; farm; FragArms; farms0; farms1
        ; echoOk; muOk; mus; musArms; graphOf; initS; gok; gfail
        ; compiled; init-sim
        ; ∧-left; ∧-right; elab; fresh
        )
  renaming (pack to gpack)
open import Muro.Temporal.Pic
  using (ERel; er0; EchoRel; echo-empty; Same; both-ok; both-bad; ++[]; _∈_)
open import Muro.Temporal.Agree using (agree; root-ns)
open import Muro.Temporal.Run using (Hold; init-hold)
open import Muro.Temporal.Expose
  using ( sim-fwd; leftSend; rightSend; Send; sent; echoed; seenL; seenR
        ; armGo-take; armGo-skip
        ; leftStop; rightStop; Stop; atAct; Leaf
        ; lf-done; lf-stop; lf-pick0; lf-pick1; lf-get; lf-cover; lf-iget; lf-mget
        ; fin-fwd; haltBlock )
open import Muro.Temporal.Denote
  using (denote; Yes; No; noB; Built; ok; bad)
open import Muro.Temporal.Fire using (ago-inj)
open import Muro.Temporal.Follow using (stepLB; stepRB; tgtL; tgtR; halt-stuckL; halt-stuckR)
open import Muro.Temporal.Den
  using ( Place; p-act
        ; d-pick0; d-pick1; d-get; d-cover; d-iget; d-mget
        ; r-pick0; r-pick1; r-get; r-cover; r-iget; r-mget
        ; lk-pick0; lk-pick1; lk-get; lk-cover; lk-iget; lk-mget
        ; c-pick0; c-pick1; c-get; c-cover; c-iget; c-mget
        ; cp-act
        ; hs-pick0; hs-pick1; hs-get; hs-cover; hs-iget; hs-mget
        ; at-pick0; at-pick1; at-get; at-cover; at-iget; at-mget
        ; en-pick0; en-pick1; en-get; en-cover; en-iget; en-mget
        ; al-pick0; al-pick1; al-get; al-cover; al-iget; al-mget )
import Muro.Temporal.Invert as Inv

------------------------------------------------------------------------
-- An atom already in a list stays there. `addA`, `adds`, and `layers`
-- never drop one, so a `bPut` in the code is an `findA` hit in the
-- alphabet. The layer count is irrelevant.
------------------------------------------------------------------------

data InA : Atom → List Atom → Set where
  here : ∀ {a xs} → InA a (a ∷ xs)
  there : ∀ {a b xs} → InA a xs → InA a (b ∷ xs)

==-refl : ∀ s → (s == s) ≡ true
==-refl s with s ≟ s
... | yes′ _ = refl
... | no′ ¬eq = ⊥-elim (¬eq refl)

==-≟ : ∀ x y → (x == y) ≡ true → x ≡ y
==-≟ x y eq with x ≟ y
==-≟ x y refl | yes′ p = p
==-≟ x y () | no′ _

eqA-refl : ∀ a → eqA a a ≡ true
eqA-refl (aNat n) with n ≟ℕ n
... | yes′ _ = refl
... | no′ ¬eq = ⊥-elim (¬eq refl)
eqA-refl (aBit false) = refl
eqA-refl (aBit true) = refl
eqA-refl (aCon s) = ==-refl s

eqA-≡ : ∀ a b → eqA a b ≡ true → a ≡ b
eqA-≡ (aNat m) (aNat n) eq with m ≟ℕ n
eqA-≡ (aNat m) (aNat .m) refl | yes′ refl = refl
eqA-≡ (aNat m) (aNat n) () | no′ _
eqA-≡ (aBit false) (aBit false) _ = refl
eqA-≡ (aBit true) (aBit true) _ = refl
eqA-≡ (aBit false) (aBit true) ()
eqA-≡ (aBit true) (aBit false) ()
eqA-≡ (aCon x) (aCon y) eq with x ≟ y
eqA-≡ (aCon x) (aCon .x) refl | yes′ refl = refl
eqA-≡ (aCon x) (aCon y) () | no′ _
eqA-≡ (aNat _) (aBit false) ()
eqA-≡ (aNat _) (aBit true) ()
eqA-≡ (aNat _) (aCon _) ()
eqA-≡ (aBit false) (aNat _) ()
eqA-≡ (aBit true) (aNat _) ()
eqA-≡ (aBit false) (aCon _) ()
eqA-≡ (aBit true) (aCon _) ()
eqA-≡ (aCon _) (aNat _) ()
eqA-≡ (aCon _) (aBit false) ()
eqA-≡ (aCon _) (aBit true) ()

elem-in : ∀ a as → elemA a as ≡ true → InA a as
elem-in a (x ∷ xs) eq with eqA a x | inspect (eqA a) x
... | true | [ ab ] = subst (λ z → InA z (x ∷ xs)) (sym (eqA-≡ a x ab)) here
... | false | _ = there (elem-in a xs eq)
elem-in a [] ()

add-in : ∀ a as → InA a (addA a as)
add-in a as with elemA a as | inspect (elemA a) as
... | false | _ = here
... | true | [ eq ] = elem-in a as eq

add-keep : ∀ {a b as} → InA a as → InA a (addA b as)
add-keep {a} {b} {as} mem with elemA b as
... | true = mem
... | false = there mem

adds-keep : ∀ a xs ys → InA a ys → InA a (adds xs ys)
adds-keep a [] ys mem = mem
adds-keep a (x ∷ xs) ys mem = adds-keep a xs (addA x ys) (add-keep mem)

adds-left : ∀ a xs ys → InA a xs → InA a (adds xs ys)
adds-left a (.a ∷ xs) ys here = adds-keep a xs (addA a ys) (add-in a ys)
adds-left a (x ∷ xs) ys (there mem) = adds-left a xs (addA x ys) mem

layers-keep : ∀ n a as → InA a as → InA a (layers n as)
layers-keep zero a as mem = mem
layers-keep (suc n) a as mem =
  layers-keep n a (adds (sucAll as) as) (adds-keep a (sucAll as) as mem)

in-alpha : ∀ a L R → InA a (lits L) → InA a (alphabet L R)
in-alpha a L R mem =
  layers-keep (growCount L + growCount R) a (adds (lits L) (lits R))
    (adds-left a (lits L) (lits R) mem)

find-in : ∀ i a as → InA a as → Σ ℕ (λ k → findGo i a as ≡ just k)
find-in i .a (a ∷ xs) here rewrite eqA-refl a = i , refl
find-in i a (b ∷ xs) (there mem) with eqA a b
... | true = i , refl
... | false = find-in (suc i) a xs mem

find-hit : ∀ a as → InA a as → Σ ℕ (λ k → findA a as ≡ just k)
find-hit a as mem = find-in zero a as mem

-- The block `lookB` returned is a literal of `lits`.
lits-in : ∀ bs i a e → lookB bs i ≡ just (bPut a e) → InA a (lits bs)
lits-in (bPut a e ∷ bs) zero .a .e refl = add-in a (lits bs)
lits-in (bPut b j ∷ bs) (suc i) a e eq = add-keep (lits-in bs i a e eq)
lits-in (bDone ∷ bs) (suc i) a e eq = lits-in bs i a e eq
lits-in (bStop ∷ bs) (suc i) a e eq = lits-in bs i a e eq
lits-in (bEcho s j ∷ bs) (suc i) a e eq = lits-in bs i a e eq
lits-in (bGrow s j ∷ bs) (suc i) a e eq = lits-in bs i a e eq
lits-in (bGet t s j ∷ bs) (suc i) a e eq = lits-in bs i a e eq
lits-in (bPick0 j ∷ bs) (suc i) a e eq = lits-in bs i a e eq
lits-in (bPick1 j ∷ bs) (suc i) a e eq = lits-in bs i a e eq
lits-in (bCover j k ∷ bs) (suc i) a e eq = lits-in bs i a e eq
lits-in (bIget s j k ∷ bs) (suc i) a e eq = lits-in bs i a e eq
lits-in (bMget t s as ∷ bs) (suc i) a e eq = lits-in bs i a e eq
lits-in (bDone ∷ _) zero _ _ ()
lits-in (bStop ∷ _) zero _ _ ()
lits-in (bEcho _ _ ∷ _) zero _ _ ()
lits-in (bGrow _ _ ∷ _) zero _ _ ()
lits-in (bGet _ _ _ ∷ _) zero _ _ ()
lits-in (bPick0 _ ∷ _) zero _ _ ()
lits-in (bPick1 _ ∷ _) zero _ _ ()
lits-in (bCover _ _ ∷ _) zero _ _ ()
lits-in (bIget _ _ _ ∷ _) zero _ _ ()
lits-in (bMget _ _ _ ∷ _) zero _ _ ()
lits-in [] _ _ _ ()

------------------------------------------------------------------------
-- No jump, no refusal. The image of `go` is plain whenever it is in
-- the fragment, and `walk` on a plain fragment process is total.
------------------------------------------------------------------------

plain : SProc → Bool
plainArm : Arm → Bool
plainArms : List Arm → Bool

plain sdone = true
plain sstop = true
plain sout = false
plain (sput _ p) = plain p
plain (sget _ _ p) = plain p
plain (spick0 p) = plain p
plain (spick1 p) = plain p
plain (scover p q) = plain p ∧ plain q
plain (siget _ p q) = plain p ∧ plain q
plain (smget _ _ as) = plainArms as
plain (smu _ _) = false
plain (svar _) = false

plainArm (aok _ p) = plain p
plainArm abad = false

plainArms [] = true
plainArms (a ∷ as) = plainArm a ∧ plainArms as

∧-both : ∀ {a b} → a ≡ true → b ≡ true → a ∧ b ≡ true
∧-both refl refl = refl

mutual
  go-plain : ∀ Γ P → Frag (go Γ P) → plain (go Γ P) ≡ true
  arms-plain : ∀ Γ cs ps bs → matchArms Γ cs ps ≡ just bs → FragArms bs →
               plainArms bs ≡ true

  go-plain Γ S.done _ = refl
  go-plain Γ S.stop _ = refl
  go-plain Γ (S.put A e p) fp with closedTy A
  go-plain Γ (S.put A e p) (fput _ fq) | true = go-plain Γ p fq
  go-plain Γ (S.put A e p) (fput () _) | false
  go-plain Γ (S.get A x p) fp with closedTy A
  go-plain Γ (S.get A x p) () | false
  go-plain Γ (S.get A x p) fp | true with goodGet A
  go-plain Γ (S.get A x p) () | true | nothing
  go-plain Γ (S.get A x p) fp | true | just _ with newName x Γ
  go-plain Γ (S.get A x p) () | true | just _ | false
  go-plain Γ (S.get A x p) (fget fq) | true | just _ | true =
    go-plain ((x , A) ∷ Γ) p fq
  go-plain Γ (S.pick0 p) (fpick0 fp) = go-plain Γ p fp
  go-plain Γ (S.pick1 p) (fpick1 fp) = go-plain Γ p fp
  go-plain Γ (S.cover p q) (fcover fp fq) =
    ∧-both (go-plain Γ p fp) (go-plain Γ q fq)
  go-plain Γ (S.iget x p q) fp with newName x Γ
  go-plain Γ (S.iget x p q) () | false
  go-plain Γ (S.iget x p q) (figet fp fq) | true =
    ∧-both (go-plain ((x , S.bit) ∷ Γ) p fp) (go-plain ((x , S.bit) ∷ Γ) q fq)
  go-plain Γ (S.mget A x as) fp with closedTy A
  go-plain Γ (S.mget A x as) () | false
  go-plain Γ (S.mget A x as) fp | true with goodGet A
  go-plain Γ (S.mget A x as) () | true | nothing
  go-plain Γ (S.mget A x as) fp | true | just t with newName x Γ
  go-plain Γ (S.mget A x as) () | true | just t | false
  go-plain Γ (S.mget A x as) fp | true | just t | true
    with matchArms ((x , A) ∷ Γ) (ctorsTy A) as
       | inspect (matchArms ((x , A) ∷ Γ) (ctorsTy A)) as
  go-plain Γ (S.mget A x as) () | true | just t | true | nothing | _
  go-plain Γ (S.mget A x as) (fmget fas) | true | just t | true | just bs | [ eq ] =
    arms-plain ((x , A) ∷ Γ) (ctorsTy A) as bs eq fas

  arms-plain _ [] [] .[] refl farms0 = refl
  arms-plain _ [] (_ ∷ _) _ () _
  arms-plain _ (S.ctor _ _ ∷ _) [] _ () _
  arms-plain _ (S.ctor _ _ ∷ _) (S.bare _ ∷ _) _ () _
  arms-plain _ (S.ctor _ _ ∷ _) (S.prod _ _ ∷ _) _ () _
  arms-plain _ (S.ctor _ _ ∷ _) (S.fork _ _ _ _ ∷ _) _ () _
  arms-plain _ (S.ctor _ _ ∷ _) (S.named _ (_ ∷ _) _ ∷ _) _ () _
  arms-plain Γ (S.ctor n _ ∷ cs) (S.named k [] p ∷ ps) bs eq fas with n == k
  arms-plain Γ (S.ctor n _ ∷ cs) (S.named k [] p ∷ ps) _ () _ | false
  arms-plain Γ (S.ctor n _ ∷ cs) (S.named k [] p ∷ ps) bs eq fas | true
    with matchArms Γ cs ps | inspect (matchArms Γ cs) ps
  arms-plain Γ (S.ctor n _ ∷ cs) (S.named k [] p ∷ ps) _ () _
    | true | nothing | _
  arms-plain Γ (S.ctor n _ ∷ cs) (S.named k [] p ∷ ps) bs eq fas
    | true | just bs′ | [ eqm ] = hit eq fas
    where
    hit : just (aok k (go Γ p) ∷ bs′) ≡ just bs → FragArms bs →
          plainArms bs ≡ true
    hit refl (farms1 (farm fp) fas′) =
      ∧-both (go-plain Γ p fp) (arms-plain Γ cs ps bs′ eqm fas′)

------------------------------------------------------------------------
-- A closed type is unchanged by an index context, so the wire type
-- of an injected payload is the type the meeting wrote.
------------------------------------------------------------------------

closedN-id : ∀ ρ e → closedN e ≡ true → S.applyNExp ρ e ≡ e
closedN-id _ (S.nlit _) _ = refl
closedN-id _ (S.nvar _) ()

mutual
  applyTy-id : ∀ ρ A → closedTy A ≡ true → S.applyTy ρ A ≡ A
  applyFs-id : ∀ ρ fs → closedFs fs ≡ true → S.applyFields ρ fs ≡ fs
  applyTs-id : ∀ ρ ts → closedTs ts ≡ true → S.applyTys ρ ts ≡ ts

  applyTy-id S.none _ _ = refl
  applyTy-id (S.bind _ _ _) S.nat _ = refl
  applyTy-id (S.bind _ _ _) S.bit _ = refl
  applyTy-id (S.bind _ _ _) S.unit _ = refl
  applyTy-id ρ@(S.bind _ _ _) (S.pair A B) eq =
    cong₂ S.pair (applyTy-id ρ A (∧-left eq)) (applyTy-id ρ B (∧-right eq))
  applyTy-id ρ@(S.bind _ _ _) (S.rec fs) eq =
    cong S.rec (applyFs-id ρ fs eq)
  applyTy-id ρ@(S.bind _ _ _) (S.vec A e) eq =
    cong₂ S.vec (applyTy-id ρ A (∧-left eq)) (closedN-id ρ e (∧-right eq))
  applyTy-id ρ@(S.bind _ _ _) (S.dat d as) eq =
    cong (S.dat d) (applyTs-id ρ as eq)

  applyFs-id S.none _ _ = refl
  applyFs-id (S.bind _ _ _) S.noFields _ = refl
  applyFs-id ρ@(S.bind _ _ _) (S.named n A fs) eq =
    cong₂ (S.named n) (applyTy-id ρ A (∧-left eq)) (applyFs-id ρ fs (∧-right eq))

  applyTs-id S.none _ _ = refl
  applyTs-id (S.bind _ _ _) [] _ = refl
  applyTs-id ρ@(S.bind _ _ _) (A ∷ ts) eq =
    cong₂ _∷_ (applyTy-id ρ A (∧-left eq)) (applyTs-id ρ ts (∧-right eq))

------------------------------------------------------------------------
-- The image of `go` has no `smu`, so `muOk` holds without a premise.
------------------------------------------------------------------------

nil-++ : {A : Set} {xs ys : List A} → xs ≡ [] → ys ≡ [] → xs ++ ys ≡ []
nil-++ refl refl = refl

mutual
  mu-go : ∀ Γ P → mus (go Γ P) ≡ []
  mu-arms : ∀ Γ cs ps bs → matchArms Γ cs ps ≡ just bs → musArms bs ≡ []

  mu-go _ S.done = refl
  mu-go _ S.stop = refl
  mu-go _ (S.put _ _ p) = mu-go _ p
  mu-go Γ (S.get A x p) with closedTy A
  mu-go Γ (S.get A x p) | false = refl
  mu-go Γ (S.get A x p) | true with goodGet A
  mu-go Γ (S.get A x p) | true | nothing = refl
  mu-go Γ (S.get A x p) | true | just _ with newName x Γ
  mu-go Γ (S.get A x p) | true | just _ | false = refl
  mu-go Γ (S.get A x p) | true | just _ | true = mu-go ((x , A) ∷ Γ) p
  mu-go Γ (S.pick0 p) = mu-go Γ p
  mu-go Γ (S.pick1 p) = mu-go Γ p
  mu-go Γ (S.cover p q) rewrite mu-go Γ p | mu-go Γ q = refl
  mu-go Γ (S.iget x p q) with newName x Γ
  mu-go Γ (S.iget x p q) | false = refl
  mu-go Γ (S.iget x p q) | true
    rewrite mu-go ((x , S.bit) ∷ Γ) p | mu-go ((x , S.bit) ∷ Γ) q = refl
  mu-go Γ (S.mget A x as) with closedTy A
  mu-go Γ (S.mget A x as) | false = refl
  mu-go Γ (S.mget A x as) | true with goodGet A
  mu-go Γ (S.mget A x as) | true | nothing = refl
  mu-go Γ (S.mget A x as) | true | just _ with newName x Γ
  mu-go Γ (S.mget A x as) | true | just _ | false = refl
  mu-go Γ (S.mget A x as) | true | just _ | true
    with matchArms ((x , A) ∷ Γ) (ctorsTy A) as
       | inspect (matchArms ((x , A) ∷ Γ) (ctorsTy A)) as
  mu-go Γ (S.mget A x as) | true | just _ | true | nothing | _ = refl
  mu-go Γ (S.mget A x as) | true | just _ | true | just bs | [ eq ] =
    mu-arms ((x , A) ∷ Γ) (ctorsTy A) as bs eq

  mu-arms _ [] [] .[] refl = refl
  mu-arms _ [] (_ ∷ _) _ ()
  mu-arms _ (S.ctor _ _ ∷ _) [] _ ()
  mu-arms _ (S.ctor _ _ ∷ _) (S.bare _ ∷ _) _ ()
  mu-arms _ (S.ctor _ _ ∷ _) (S.prod _ _ ∷ _) _ ()
  mu-arms _ (S.ctor _ _ ∷ _) (S.fork _ _ _ _ ∷ _) _ ()
  mu-arms _ (S.ctor _ _ ∷ _) (S.named _ (_ ∷ _) _ ∷ _) _ ()
  mu-arms Γ (S.ctor n _ ∷ cs) (S.named k [] p ∷ ps) bs eq with n == k
  mu-arms Γ (S.ctor n _ ∷ cs) (S.named k [] p ∷ ps) _ () | false
  mu-arms Γ (S.ctor n _ ∷ cs) (S.named k [] p ∷ ps) bs eq | true
    with matchArms Γ cs ps | inspect (matchArms Γ cs) ps
  mu-arms Γ (S.ctor n _ ∷ cs) (S.named k [] p ∷ ps) _ () | true | nothing | _
  mu-arms Γ (S.ctor n _ ∷ cs) (S.named k [] p ∷ ps) bs eq | true | just bs′ | [ eqm ] =
    hit eq
    where
    hit : just (aok k (go Γ p) ∷ bs′) ≡ just bs → musArms bs ≡ []
    hit refl = nil-++ (mu-go Γ p) (mu-arms Γ cs ps bs′ eqm)

mu-ok : ∀ Γ P → muOk (go Γ P) ≡ true
mu-ok Γ P rewrite mu-go Γ P = refl

------------------------------------------------------------------------
-- `walk` of a plain process is the counters it starts from. A put
-- keeps the slot. A binder consumes one. A cover sequences the two
-- branches.
------------------------------------------------------------------------

record Walked (n s : ℕ) (p : SProc) : Set where
  constructor walked
  field
    w : W
    eq : walk [] [] p n s ≡ just w
    en : entry w ≡ n
    at : atSlot w ≡ s
    sn : slotN w ≡ s + length (bnames p)

record WalkedA (n s : ℕ) (as : List Arm) : Set where
  constructor walkedA
  field
    ws : List (String × W)
    n2 s2 : ℕ
    eq : walkArms [] [] as n s ≡ just (ws , n2 , s2)
    sn : s2 ≡ s + length (bnamesArms as)

slot-bind : ∀ s n → suc s + n ≡ s + suc n
slot-bind s n = sym (+-suc s n)

sameW : ∀ p n s n' s' →
       walk [] (addPend [] n s []) p n' s' ≡ walk [] [] p n' s'
sameW _ _ _ _ _ = refl

sameA : ∀ as n s n' s' →
        walkArms [] (addPend [] n s []) as n' s' ≡ walkArms [] [] as n' s'
sameA _ _ _ _ _ = refl

-- The continuation walk is an argument, so `walk` of the compound
-- reduces when that argument is `just`. A `with` under the record
-- match does not.
putW : ∀ a p n s w → walk [] [] p (suc n) s ≡ just w →
       slotN w ≡ s + length (bnames p) → Walked n s (sput a p)
putW a p n s w eq sn =
  walked (mkW n s (next w) (slotN w))
    (cong (walkCont n s) (trans (sameW p n s (suc n) s) eq)) refl refl sn

getW : ∀ t x p n s w → walk [] [] p (suc n) (suc s) ≡ just w →
       slotN w ≡ suc s + length (bnames p) → Walked n s (sget t x p)
getW t x p n s w eq sn =
  walked (mkW n s (next w) (slotN w))
    (cong (walkCont n s) (trans (sameW p n s (suc n) (suc s)) eq))
    refl refl
    (trans sn (slot-bind s (length (bnames p))))

p0W : ∀ p n s w → walk [] [] p (suc n) s ≡ just w →
      slotN w ≡ s + length (bnames p) → Walked n s (spick0 p)
p0W p n s w eq sn =
  walked (mkW n s (next w) (slotN w))
    (cong (walkCont n s) (trans (sameW p n s (suc n) s) eq)) refl refl sn

p1W : ∀ p n s w → walk [] [] p (suc n) s ≡ just w →
      slotN w ≡ s + length (bnames p) → Walked n s (spick1 p)
p1W p n s w eq sn =
  walked (mkW n s (next w) (slotN w))
    (cong (walkCont n s) (trans (sameW p n s (suc n) s) eq)) refl refl sn

cov-sn : ∀ {p q s w1 w2} →
         slotN w1 ≡ s + length (bnames p) →
         slotN w2 ≡ slotN w1 + length (bnames q) →
         slotN w2 ≡ s + length (bnames p ++ bnames q)
cov-sn {p} {q} {s} a b =
  trans b (trans (cong (_+ length (bnames q)) a)
    (trans (+-assoc s (length (bnames p)) (length (bnames q)))
      (cong (s +_) (sym (length-++ (bnames p) {bnames q})))))

covW : ∀ p q n s w1 w2 →
       walk [] [] p (suc n) s ≡ just w1 →
       walk [] [] q (next w1) (slotN w1) ≡ just w2 →
       slotN w1 ≡ s + length (bnames p) →
       slotN w2 ≡ slotN w1 + length (bnames q) →
       Walked n s (scover p q)
covW p q n s w1 w2 e1 e2 sn1 sn2 =
  walked (mkW n s (next w2) (slotN w2)) (cov-eq e1 e2) refl refl
    (cov-sn {p} {q} {s} {w1} {w2} sn1 sn2)
  where
  k : W → Maybe W
  k w = walk [] (addPend [] n s []) q (next w) (slotN w)
  cov-eq : walk [] [] p (suc n) s ≡ just w1 →
           walk [] [] q (next w1) (slotN w1) ≡ just w2 →
           walk [] [] (scover p q) n s ≡ just (mkW n s (next w2) (slotN w2))
  cov-eq a b =
    trans (cong (λ m → walkTwo n s m k) (trans (sameW p n s (suc n) s) a))
          (cong (walkEnd n s w1) (trans (sameW q n s (next w1) (slotN w1)) b))

iget-sn : ∀ {x p q s w1 w2} →
          slotN w1 ≡ suc s + length (bnames p) →
          slotN w2 ≡ slotN w1 + length (bnames q) →
          slotN w2 ≡ s + length (x ∷ bnames p ++ bnames q)
iget-sn {x} {p} {q} {s} a b =
  trans b (trans (cong (_+ length (bnames q)) a)
    (trans (cong (_+ length (bnames q)) (slot-bind s (length (bnames p))))
      (trans (+-assoc s (suc (length (bnames p))) (length (bnames q)))
        (cong (s +_) (sym (cong suc (length-++ (bnames p) {bnames q})))))))

igW : ∀ x p q n s w1 w2 →
      walk [] [] p (suc n) (suc s) ≡ just w1 →
      walk [] [] q (next w1) (slotN w1) ≡ just w2 →
      slotN w1 ≡ suc s + length (bnames p) →
      slotN w2 ≡ slotN w1 + length (bnames q) →
      Walked n s (siget x p q)
igW x p q n s w1 w2 e1 e2 sn1 sn2 =
  walked (mkW n s (next w2) (slotN w2)) (ig-eq e1 e2) refl refl
    (iget-sn {x} {p} {q} {s} {w1} {w2} sn1 sn2)
  where
  k : W → Maybe W
  k w = walk [] (addPend [] n s []) q (next w) (slotN w)
  ig-eq : walk [] [] p (suc n) (suc s) ≡ just w1 →
          walk [] [] q (next w1) (slotN w1) ≡ just w2 →
          walk [] [] (siget x p q) n s ≡ just (mkW n s (next w2) (slotN w2))
  ig-eq a b =
    trans (cong (λ m → walkTwo n s m k) (trans (sameW p n s (suc n) (suc s)) a))
          (cong (walkEnd n s w1) (trans (sameW q n s (next w1) (slotN w1)) b))

mgW : ∀ t x as n s ws n2 s2 →
      walkArms [] [] as (suc n) (suc s) ≡ just (ws , n2 , s2) →
      s2 ≡ suc s + length (bnamesArms as) →
      Walked n s (smget t x as)
mgW t x as n s ws n2 s2 eq sn =
  walked (mkW n s n2 s2)
    (cong (walkM n s) (trans (sameA as n s (suc n) (suc s)) eq))
    refl refl
    (trans sn (slot-bind s (length (bnamesArms as))))

arm-sn : ∀ {p as s w s2} →
         slotN w ≡ s + length (bnames p) →
         s2 ≡ slotN w + length (bnamesArms as) →
         s2 ≡ s + length (bnames p ++ bnamesArms as)
arm-sn {p} {as} {s} a b =
  trans b (trans (cong (_+ length (bnamesArms as)) a)
    (trans (+-assoc s (length (bnames p)) (length (bnamesArms as)))
      (cong (s +_) (sym (length-++ (bnames p) {bnamesArms as})))))

armW : ∀ y p as n s w ws n2 s2 →
       walk [] [] p n s ≡ just w →
       walkArms [] [] as (next w) (slotN w) ≡ just (ws , n2 , s2) →
       slotN w ≡ s + length (bnames p) →
       s2 ≡ slotN w + length (bnamesArms as) →
       WalkedA n s (aok y p ∷ as)
armW y p as n s w ws n2 s2 e1 e2 sn1 sn2 =
  walkedA ((y , w) ∷ ws) n2 s2 (arm-eq e1 e2)
    (arm-sn {p} {as} {s} {w} {s2} sn1 sn2)
  where
  k : W → Maybe (List (String × W) × ℕ × ℕ)
  k w' = walkArms [] [] as (next w') (slotN w')
  arm-eq : walk [] [] p n s ≡ just w →
           walkArms [] [] as (next w) (slotN w) ≡ just (ws , n2 , s2) →
           walkArms [] [] (aok y p ∷ as) n s ≡ just ((y , w) ∷ ws , n2 , s2)
  arm-eq a b =
    trans (cong (λ m → walkArm y m k) a) (cong (consArm y w) b)

mutual
  walk-plain : ∀ p n s → plain p ≡ true → Walked n s p
  walkA-plain : ∀ as n s → plainArms as ≡ true → WalkedA n s as

  walk-plain sdone n s _ =
    walked (mkW n s (suc n) s) refl refl refl (sym (+-identityʳ s))
  walk-plain sstop n s _ =
    walked (mkW n s (suc n) s) refl refl refl (sym (+-identityʳ s))
  walk-plain sout _ _ ()
  walk-plain (sput a p) n s pl = put-use (walk-plain p (suc n) s pl)
    where
    put-use : Walked (suc n) s p → Walked n s (sput a p)
    put-use (walked w e _ _ sn) = putW a p n s w e sn
  walk-plain (sget t x p) n s pl = get-use (walk-plain p (suc n) (suc s) pl)
    where
    get-use : Walked (suc n) (suc s) p → Walked n s (sget t x p)
    get-use (walked w e _ _ sn) = getW t x p n s w e sn
  walk-plain (spick0 p) n s pl = p0-use (walk-plain p (suc n) s pl)
    where
    p0-use : Walked (suc n) s p → Walked n s (spick0 p)
    p0-use (walked w e _ _ sn) = p0W p n s w e sn
  walk-plain (spick1 p) n s pl = p1-use (walk-plain p (suc n) s pl)
    where
    p1-use : Walked (suc n) s p → Walked n s (spick1 p)
    p1-use (walked w e _ _ sn) = p1W p n s w e sn
  walk-plain (scover p q) n s pl = cov-use (walk-plain p (suc n) s (∧-left pl))
    where
    cov-use : Walked (suc n) s p → Walked n s (scover p q)
    cov-use (walked w1 e1 _ _ sn1) =
      cov-use2 (walk-plain q (next w1) (slotN w1) (∧-right pl))
      where
      cov-use2 : Walked (next w1) (slotN w1) q → Walked n s (scover p q)
      cov-use2 (walked w2 e2 _ _ sn2) = covW p q n s w1 w2 e1 e2 sn1 sn2
  walk-plain (siget x p q) n s pl =
    ig-use (walk-plain p (suc n) (suc s) (∧-left pl))
    where
    ig-use : Walked (suc n) (suc s) p → Walked n s (siget x p q)
    ig-use (walked w1 e1 _ _ sn1) =
      ig-use2 (walk-plain q (next w1) (slotN w1) (∧-right pl))
      where
      ig-use2 : Walked (next w1) (slotN w1) q → Walked n s (siget x p q)
      ig-use2 (walked w2 e2 _ _ sn2) = igW x p q n s w1 w2 e1 e2 sn1 sn2
  walk-plain (smget t x as) n s pl = mg-use (walkA-plain as (suc n) (suc s) pl)
    where
    mg-use : WalkedA (suc n) (suc s) as → Walked n s (smget t x as)
    mg-use (walkedA ws n2 s2 e snA) = mgW t x as n s ws n2 s2 e snA
  walk-plain (smu _ _) _ _ ()
  walk-plain (svar _) _ _ ()

  walkA-plain [] n s _ = walkedA [] n s refl (sym (+-identityʳ s))
  walkA-plain (abad ∷ _) _ _ ()
  walkA-plain (aok y p ∷ as) n s pl = arm-use (walk-plain p n s (∧-left pl))
    where
    arm-use : Walked n s p → WalkedA n s (aok y p ∷ as)
    arm-use (walked w e _ _ sn1) =
      arm-use2 (walkA-plain as (next w) (slotN w) (∧-right pl))
      where
      arm-use2 : WalkedA (next w) (slotN w) as → WalkedA n s (aok y p ∷ as)
      arm-use2 (walkedA ws n2 s2 e2 sn2) =
        armW y p as n s w ws n2 s2 e e2 sn1 sn2

------------------------------------------------------------------------
-- A fragment payload was sent. A call, a tuple, and a constructor the
-- declaration does not inhabit are `pOut`, which `Frag` excludes.
------------------------------------------------------------------------

nat-fits : ∀ (v : S.Val S.nat) → S.fits v ≡ true
nat-fits S.zero = refl
nat-fits (S.suc v) = nat-fits v

bit-fits : ∀ (v : S.Val S.bit) → S.fits v ≡ true
bit-fits S.b0 = refl
bit-fits S.b1 = refl

con-fits : ∀ {d as} (s : String) (sp : S.Spine) →
           FragPay (payVal (S.con {d} {as} s sp)) →
           S.fits (S.con {d} {as} s sp) ≡ true
con-fits {d} {as} s S.snil fp with S.fits (S.con {d} {as} s S.snil)
con-fits {d} {as} s S.snil _ | true = refl
con-fits {d} {as} s S.snil () | false
con-fits _ (S.scons _ _ _) ()

lit-sent : ∀ {A} (v : S.Val A) Γ (P : S.Proc) →
           Frag (go Γ (S.put A (S.lit v) P)) → S.fits v ≡ true
lit-sent S.zero _ _ _ = refl
lit-sent (S.suc v) _ _ _ = nat-fits (S.suc v)
lit-sent S.b0 _ _ _ = refl
lit-sent S.b1 _ _ _ = refl
lit-sent S.tt _ _ _ = refl
lit-sent (S.tup {A} {B} _ _) Γ P fp with closedTy A ∧ closedTy B
lit-sent (S.tup _ _) Γ P (fput () _) | false
lit-sent (S.tup _ _) Γ P (fput () _) | true
lit-sent (S.rec {fs} _) Γ P fp with closedFs fs
lit-sent (S.rec _) Γ P (fput () _) | false
lit-sent (S.rec _) Γ P (fput () _) | true
lit-sent (S.rep {A} {e} _) Γ P fp with closedTy A ∧ closedN e
lit-sent (S.rep _) Γ P (fput () _) | false
lit-sent (S.rep _) Γ P (fput () _) | true
lit-sent {S.dat _ as} (S.con s sp) Γ P fp with closedTs as
lit-sent (S.con s sp) Γ P (fput () _) | false
lit-sent (S.con s sp) Γ P (fput fp _) | true = con-fits s sp fp

image-sent : ∀ Γ {A} (v : S.ValExpr A) (P : S.Proc) →
             Frag (go Γ (S.put A v P)) → S.sent v ≡ true
image-sent Γ (S.lit v) P fp = lit-sent v Γ P fp
image-sent _ (S.var _) _ _ = refl
image-sent Γ {A} (S.call _ _) P fp with closedTy A
image-sent Γ (S.call _ _) P (fput () _) | false
image-sent Γ (S.call _ _) P (fput () _) | true

-- A call is not a fragment payload, so it never stands under `Frag`.
no-call : ∀ Γ {A} (f : String) (as : List S.VArg) (P : S.Proc) →
          Frag (go Γ (S.put A (S.call f as) P)) → ⊥
no-call Γ {A} f as P fp with closedTy A
no-call Γ f as P (fput () _) | false
no-call Γ f as P (fput () _) | true

------------------------------------------------------------------------
-- Writing one slot leaves the others, and the written cell is the value.
------------------------------------------------------------------------

nth-set : ∀ i v xs → i < length xs → nth (setNth i v xs) i ≡ just v
nth-set zero v (_ ∷ _) (s≤s _) = refl
nth-set (suc i) v (_ ∷ xs) (s≤s le) = nth-set i v xs le
nth-set zero _ [] ()
nth-set (suc _) _ [] ()

nth-other : ∀ i j v xs → i ≢ j → nth (setNth i v xs) j ≡ nth xs j
nth-other zero zero _ (_ ∷ _) neq = ⊥-elim (neq refl)
nth-other zero (suc _) _ (_ ∷ _) _ = refl
nth-other (suc _) zero _ (_ ∷ _) _ = refl
nth-other (suc i) (suc j) v (_ ∷ xs) neq = nth-other i j v xs (λ eq → neq (cong suc eq))
nth-other zero zero _ [] neq = ⊥-elim (neq refl)
nth-other zero (suc _) _ [] _ = refl
nth-other (suc _) zero _ [] _ = refl
nth-other (suc _) (suc _) _ [] _ = refl

-- No earlier copy of `x`: its first slot is the length of the prefix.
findS-at : ∀ x pre suf → fresh x pre ≡ true →
           findS x (pre ++ x ∷ suf) ≡ just (length pre)
findS-at x [] suf _ rewrite ==-refl x = refl
findS-at x (y ∷ pre) suf fr with x == y
findS-at x (y ∷ pre) suf () | true
findS-at x (y ∷ pre) suf fr | false rewrite findS-at x pre suf fr = refl

-- `findGo` returns the first hit, so that index still holds the atom.
-- Rewriting the boolean unfolds the foreign `with` inside `findGo`.
find-here : ∀ i a x xs → eqA a x ≡ true → findGo i a (x ∷ xs) ≡ just i
find-here i a x xs eq rewrite eq = refl

find-skip : ∀ i a x xs → eqA a x ≡ false →
            findGo i a (x ∷ xs) ≡ findGo (suc i) a xs
find-skip i a x xs eq rewrite eq = refl

find-low : ∀ i a as k → findGo i a as ≡ just k → i ≤ k
find-low i a (x ∷ xs) k eq = on (eqA a x) refl
  where
  on : (b : Bool) → eqA a x ≡ b → i ≤ k
  on true ab = low (trans (sym (find-here i a x xs ab)) eq)
    where
    low : just i ≡ just k → i ≤ k
    low refl = ≤-refl
  on false ab = ≤-trans (n≤1+n i) (find-low (suc i) a xs k (trans (sym (find-skip i a x xs ab)) eq))
find-low _ _ [] _ ()

∸-suc : ∀ i k → i ≤ k → suc k ∸ i ≡ suc (k ∸ i)
∸-suc zero k _ = refl
∸-suc (suc i) (suc k) (s≤s le) = ∸-suc i k le

suc-∸ : ∀ {i k} → suc i ≤ k → k ∸ i ≡ suc (k ∸ suc i)
suc-∸ {i} {suc k} (s≤s le) = ∸-suc i k le

find-at : ∀ i a as k → findGo i a as ≡ just k → nthA as (k ∸ i) ≡ just a
find-at i a (x ∷ xs) k eq = on (eqA a x) refl
  where
  on : (b : Bool) → eqA a x ≡ b → nthA (x ∷ xs) (k ∸ i) ≡ just a
  on true ab = hit (trans (sym (find-here i a x xs ab)) eq)
    where
    hit : just i ≡ just k → nthA (x ∷ xs) (k ∸ i) ≡ just a
    hit refl =
      subst (λ z → nthA (x ∷ xs) (i ∸ i) ≡ just z) (sym (eqA-≡ a x ab))
        (subst (λ n → nthA (x ∷ xs) n ≡ just x) (sym (n∸n≡0 i)) refl)
  on false ab =
    subst (λ n → nthA (x ∷ xs) n ≡ just a)
      (sym (suc-∸ (find-low (suc i) a xs k (trans (sym (find-skip i a x xs ab)) eq))))
      (find-at (suc i) a xs k (trans (sym (find-skip i a x xs ab)) eq))
find-at _ _ [] _ ()

findA-nth : ∀ a as k → findA a as ≡ just k → nthA as k ≡ just a
findA-nth a as k eq = find-at zero a as k eq

-- A process that is already a `put` is the left action `reactL` runs.
react-put : ∀ (c : A.Conf) {B : S.Ty} {v : S.ValExpr B} {P : S.Proc}
            (eq : A.Conf.lp c ≡ S.put B v P) →
            A.reactL c ≡ A.sendPutL c v P eq
react-put c refl = refl

------------------------------------------------------------------------
-- A typed message and a graph token carry the same atom. `lab` is the
-- same bit. The index `k` is the atom's place in the alphabet.
------------------------------------------------------------------------

valAtom : ∀ {B} → S.ValExpr B → Maybe Atom
valAtom (S.lit v) = asAtom (payVal v)
valAtom (S.var _) = nothing
valAtom (S.call _ _) = nothing

data TokOf (al : List Atom) : A.Msg → Tok → Set where
  of-lab : ∀ b → TokOf al (A.lab b) (lab b)
  of-pay : ∀ {W B : S.Ty} {v r k a} →
           W ≡ B →
           closedTy B ≡ true →
           nthA al k ≡ just a →
           valAtom {B} r ≡ just a →
           TokOf al (A.pay W (A.car B v r)) (pay k)

data QRel (al : List Atom) : List A.Msg → List Tok → Set where
  qnil : QRel al [] []
  qcons : ∀ {m t ms ts} → TokOf al m t → QRel al ms ts →
          QRel al (m ∷ ms) (t ∷ ts)

qrel-len : ∀ {al ms ts} → QRel al ms ts → length ms ≡ length ts
qrel-len qnil = refl
qrel-len (qcons _ q) = cong suc (qrel-len q)

qrel-snoc : ∀ {al ms ts m t} → QRel al ms ts → TokOf al m t →
            QRel al (A.snoc ms m) (snoc ts t)
qrel-snoc qnil tk = qcons tk qnil
qrel-snoc (qcons h q) tk = qcons h (qrel-snoc q tk)

-- Each binder still in scope is one literal in the typed environment,
-- and `names` holds that literal at the slot `findS` returns.
data VRel (al : List Atom) (slots : List ℕ) (names : List String)
          (bound : ℕ) : List (String × S.Ty) → A.VEnv → Set where
  vr0 : VRel al slots names bound [] []
  vr1 : ∀ {Γ ve A u i k a} (x : String) →
        findS x names ≡ just i →
        i < bound →
        nth slots i ≡ just (suc k) →
        nthA al k ≡ just a →
        valAtom (S.lit u) ≡ just a →
        VRel al slots names bound Γ ve →
        VRel al slots names bound ((x , A) ∷ Γ) ((x , A.evar A (S.lit u)) ∷ ve)

slot-suc : ∀ slots i k → nth slots i ≡ just (suc k) → slotVal slots i ≡ just k
slot-suc slots i k eq rewrite eq = refl

put-closed : ∀ Γ {B} (v : S.ValExpr B) P →
             Frag (go Γ (S.put B v P)) → closedTy B ≡ true
put-closed Γ {B} v P fp with closedTy B
put-closed Γ v P (fput _ _) | true = refl
put-closed Γ v P (fput () _) | false

go-put : ∀ Γ {B} (v : S.ValExpr B) P → closedTy B ≡ true →
         go Γ (S.put B v P) ≡ sput (payClosed Γ v) (go Γ P)
go-put Γ {B} v P eq with closedTy B
go-put Γ v P refl | true = refl
go-put Γ v P () | false

put-body : ∀ Γ {B} (v : S.ValExpr B) P →
           Frag (go Γ (S.put B v P)) → Frag (go Γ P)
put-body Γ {B} v P fp with closedTy B
put-body Γ v P (fput _ fq) | true = fq
put-body Γ v P (fput () _) | false

-- The block at the left cursor puts `atom`, so the alphabet contains it.
atom-of : ∀ {g s atom j} (h : Hold g s) →
          alpha s ≡ alphabet (codeL g) (codeR g) →
          (il s , bPut atom j) ∈ Hold.bsL h →
          Σ ℕ (λ k → findA atom (alpha s) ≡ just k)
atom-of {g} {s} {atom} h al≡ mem =
  let inn = lits-in (codeL g) (il s) atom _ (seenL h mem)
      k , fk = find-hit atom (alphabet (codeL g) (codeR g))
                 (in-alpha atom (codeL g) (codeR g) inn)
  in k , subst (λ xs → findA atom xs ≡ just k) (sym al≡) fk

src-room : ∀ {a b n m} → a < n → a ≡ b → n ≡ m → b < m
src-room le refl refl = le

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

-- `payVal` is a literal atom or `pOut`. It is never an echo.
bump-echo : ∀ p x → bump p ≡ pEcho x → ⊥
bump-echo (pNat _) _ ()
bump-echo (pBit _) _ ()
bump-echo (pCon _) _ ()
bump-echo (pEcho _) _ ()
bump-echo pOut _ ()

pay-echo : ∀ {A} (u : S.Val A) x → payVal u ≡ pEcho x → ⊥
pay-echo S.zero _ ()
pay-echo (S.suc v) x eq = bump-echo (payVal v) x eq
pay-echo S.b0 _ ()
pay-echo S.b1 _ ()
pay-echo S.tt _ ()
pay-echo (S.tup _ _) _ ()
pay-echo (S.rec _) _ ()
pay-echo (S.rep _) _ ()
pay-echo (S.con {d} {as} s S.snil) x eq with S.fits (S.con {d} {as} s S.snil)
pay-echo (S.con s S.snil) x () | true
pay-echo (S.con s S.snil) x () | false
pay-echo (S.con _ (S.scons _ _ _)) _ ()

-- `payIn` reads the closed-type guard and then is `payClosed`.
payIn-closed : ∀ Γ {A} (e : S.ValExpr A) → closedTy A ≡ true →
               payIn Γ e ≡ payClosed Γ e
payIn-closed Γ {A} e eq with closedTy A
payIn-closed Γ e refl | true = refl
payIn-closed Γ e () | false

-- The source configuration a left literal put reaches. The counters
-- are the ones the continuation walk returns.
putLitS : SConf → SProc → ℕ → W → SConf
putLitS s p k w = record s
  { left = p ; il = entry w ; slotL = atSlot w
  ; l2r = snoc (l2r s) (pay k)
  ; envPL = [] ; envIL = addPend [] (il s) (slotL s) (envIL s) }

-- The queued message is the atom `payVal` already found.
pay-tok : ∀ {al σ B u k a} → closedTy B ≡ true →
          nthA al k ≡ just a → valAtom (S.lit u) ≡ just a →
          TokOf al (A.pay (S.applyTy σ B) (A.car B (S.lit u) (S.lit u))) (pay k)
pay-tok {σ = σ} {B} {u} cl nth va =
  of-pay (applyTy-id σ B cl) cl nth va

-- A left literal put of a fragment process is the source put, and
-- that source put is the graph step. The token is the message
-- `mkPayL` enqueues.
lit-step : ∀ {g c s Γ B u P} (h : Hold g s) →
           alpha s ≡ alphabet (codeL g) (codeR g) →
           envPL s ≡ [] → envIL s ≡ [] →
           left s ≡ go Γ (S.put B (S.lit u) P) →
           Frag (left s) →
           A.Conf.cap c ≡ cap s →
           QRel (alpha s) (A.Conf.l2r c) (l2r s) →
           length (A.Conf.l2r c) < A.Conf.cap c →
           Σ ℕ (λ k → Σ W (λ w →
             let s′ = putLitS s (go Γ P) k w in
             s ⟶ₛ s′ × Step g (abs s) lside (abs s′) × Hold g s′
             × atSlot w ≡ slotL s
             × TokOf (alpha s) (A.mkPayL c (S.lit u)) (pay k)))
lit-step {g} {c} {s} {Γ} {B} {u} {P} h al≡ zP zI lp≡ fr ck qL le =
  step (put-closed Γ (S.lit u) P (subst Frag lp≡ fr))
  where
  step : closedTy B ≡ true →
         Σ ℕ (λ k → Σ W (λ w →
           let s′ = putLitS s (go Γ P) k w in
           s ⟶ₛ s′ × Step g (abs s) lside (abs s′) × Hold g s′
           × atSlot w ≡ slotL s
           × TokOf (alpha s) (A.mkPayL c (S.lit u)) (pay k)))
  step cl = onSend (leftSend h unf)
    where
    unf : Unfold (envPL s) [] (left s) [] []
            (f-put (payClosed Γ (S.lit u)) (go Γ P))
    unf =
      let aeq = payIn-closed Γ (S.lit u) cl
          lit = subst (λ a → Unfold [] [] (sput a (go Γ P)) [] []
                               (f-put a (go Γ P)))
                  aeq u-put
          proc≡ = trans (sym (cong (λ a → sput a (go Γ P)) aeq)) (sym lp≡)
          atLeft = subst (λ p → Unfold [] [] p [] []
                             (f-put (payClosed Γ (S.lit u)) (go Γ P)))
                    proc≡ lit
      in subst (λ e → Unfold e [] (left s) [] []
                    (f-put (payClosed Γ (S.lit u)) (go Γ P)))
           (sym zP) atLeft
    wp : Walked (suc (il s)) (slotL s) (go Γ P)
    wp = walk-plain (go Γ P) (suc (il s)) (slotL s)
           (go-plain Γ P (put-body Γ (S.lit u) P (subst Frag lp≡ fr)))
    onSend : Send (Hold.bsL h) _ (il s) (slotL s) (envIL s) [] []
                 (payClosed Γ (S.lit u)) (go Γ P) →
            Σ ℕ (λ k → Σ W (λ w →
              let s′ = putLitS s (go Γ P) k w in
              s ⟶ₛ s′ × Step g (abs s) lside (abs s′) × Hold g s′
              × atSlot w ≡ slotL s
              × TokOf (alpha s) (A.mkPayL c (S.lit u)) (pay k)))
    onSend (echoed x _ _ _ aeq _ _ _ _ _ _) = ⊥-elim (pay-echo u x aeq)
    onSend (sent atom j wd aeq _ mem _ _ _) =
      let k , fk = atom-of h al≡ mem
          w = Walked.w wp
          wk = subst (λ e → walk [] e (go Γ P) (suc (il s)) (slotL s) ≡ just w)
                 (sym (cong (λ e → addPend [] (il s) (slotL s) e) zI))
                 (Walked.eq wp)
          rm = src-room le (qrel-len qL) ck
          st = put-l unf aeq fk rm wk
          _ , gs , h′ = sim-fwd h st
          tok = pay-tok cl (findA-nth atom (alpha s) k fk) aeq
      in k , w , st , gs , h′ , Walked.at wp , tok

-- The configuration `sendPutL` steps to. Written with `mk` so the
-- field names stay qualified.
putD : (c : A.Conf) (P : S.Proc) {B : S.Ty} → S.ValExpr B → A.Conf
putD c P v = A.mk (A.Conf.cap c) P (A.Conf.rp c)
                  (A.snoc (A.Conf.l2r c) (A.mkPayL c v))
                  (A.Conf.r2l c) (A.Conf.lv c) (A.Conf.rv c)
                  (A.Conf.σ c) (A.Conf.τ c)

-- Both guards of `sendPutL` are the `yes` the fragment already has.
put-does : ∀ (c : A.Conf) {B : S.Ty} {v : S.ValExpr B} {P : S.Proc}
           (eq : A.Conf.lp c ≡ S.put B v P) →
           length (A.Conf.l2r c) < A.Conf.cap c →
           S.sent v ≡ true →
           Σ (A.measure (putD c P v) < A.measure c)
             (λ lt → A.sendPutL c v P eq ≡ A.does (putD c P v) lt)
put-does c {v = v} eq le sv with length (A.Conf.l2r c) <? A.Conf.cap c
... | no′ ¬le = ⊥-elim (¬le le)
... | yes′ _ with S.sent? v
... | no′ ¬p = ⊥-elim (¬p sv)
... | yes′ _ = _ , refl

------------------------------------------------------------------------
-- A finite configuration is the source configuration `go` builds.
-- Binders already passed sit in `passed`, oldest first, and `pre` is
-- that list most-recent first. `names` keeps every binder of the
-- original process, so a step does not change it. Both environments
-- stay empty: `go` builds no `mu`.
------------------------------------------------------------------------

record Embed (g : Graph) (c : A.Conf) (s : SConf) : Set where
  field
    hold : Hold g s
    al≡ : alpha s ≡ alphabet (codeL g) (codeR g)
    cap≡ : A.Conf.cap c ≡ cap s
    qL : QRel (alpha s) (A.Conf.l2r c) (l2r s)
    qR : QRel (alpha s) (A.Conf.r2l c) (r2l s)
    preL : List (String × S.Ty)
    preR : List (String × S.Ty)
    lp≡ : left s ≡ go preL (A.Conf.lp c)
    rp≡ : right s ≡ go preR (A.Conf.rp c)
    zPL : envPL s ≡ []
    zPR : envPR s ≡ []
    zIL : envIL s ≡ []
    zIR : envIR s ≡ []
    frL : Frag (left s)
    frR : Frag (right s)
    passedL sufL passedR sufR : List String
    layL : namesL s ≡ passedL ++ bnames (left s) ++ sufL
    layR : namesR s ≡ passedR ++ bnames (right s) ++ sufR
    slot≡L : slotL s ≡ length passedL
    slot≡R : slotR s ≡ length passedR
    disL : distinctN (namesL s) ≡ true
    disR : distinctN (namesR s) ≡ true
    lenL : length (el s) ≡ length (namesL s)
    lenR : length (er s) ≡ length (namesR s)
    vL : VRel (alpha s) (el s) (namesL s) (length passedL) preL (A.Conf.lv c)
    vR : VRel (alpha s) (er s) (namesR s) (length passedR) preR (A.Conf.rv c)

-- A literal put on the left is one async step, one source step, and
-- the embedding of the pair it reaches.
step-put-lit : ∀ {g c s B u P} (e : Embed g c s)
               (eq : A.Conf.lp c ≡ S.put B (S.lit u) P) →
               length (A.Conf.l2r c) < A.Conf.cap c →
               let d = putD c P (S.lit u) in
               Σ (A.measure d < A.measure c) (λ lt →
                 Σ SConf (λ s′ →
                   A.sendPutL c (S.lit u) P eq ≡ A.does d lt
                   × Embed g d s′
                   × s ⟶ₛ s′
                   × Step g (abs s) lside (abs s′)))
step-put-lit {g} {c} {s} {B} {u} {P} e eq le =
  lt , s′ , does , e′ , st , gs
  where
  Γ = Embed.preL e
  d = putD c P (S.lit u)
  lpE : left s ≡ go Γ (S.put B (S.lit u) P)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  frPut : Frag (go Γ (S.put B (S.lit u) P))
  frPut = subst Frag lpE (Embed.frL e)
  moved = put-does c {v = S.lit u} eq le (image-sent Γ (S.lit u) P frPut)
  lt = proj₁ moved
  does = proj₂ moved
  packed : Σ ℕ (λ k → Σ W (λ w →
             let s0 = putLitS s (go Γ P) k w in
             s ⟶ₛ s0 × Step g (abs s) lside (abs s0) × Hold g s0
             × atSlot w ≡ slotL s
             × TokOf (alpha s) (A.mkPayL c {A = B} (S.lit u)) (pay k)))
  packed = lit-step {g = g} {c = c} {s = s} {Γ = Γ} {B = B} {u = u} {P = P}
             (Embed.hold e) (Embed.al≡ e) (Embed.zPL e) (Embed.zIL e)
             lpE (Embed.frL e) (Embed.cap≡ e) (Embed.qL e) le
  k = proj₁ packed
  rest = proj₂ packed
  w = proj₁ rest
  rest2 = proj₂ rest
  st = proj₁ rest2
  gs = proj₁ (proj₂ rest2)
  h′ = proj₁ (proj₂ (proj₂ rest2))
  atw = proj₁ (proj₂ (proj₂ (proj₂ rest2)))
  tok = proj₂ (proj₂ (proj₂ (proj₂ rest2)))
  s′ = putLitS s (go Γ P) k w
  sameB = cong bnames lpE
  e′ : Embed g d s′
  e′ = record
    { hold = h′
    ; al≡ = Embed.al≡ e
    ; cap≡ = Embed.cap≡ e
    ; qL = qrel-snoc (Embed.qL e) tok
    ; qR = Embed.qR e
    ; preL = Γ
    ; preR = Embed.preR e
    ; lp≡ = refl
    ; rp≡ = Embed.rp≡ e
    ; zPL = refl
    ; zPR = Embed.zPR e
    ; zIL = Embed.zIL e
    ; zIR = Embed.zIR e
    ; frL = put-body Γ (S.lit u) P frPut
    ; frR = Embed.frR e
    ; vL = Embed.vL e
    ; vR = Embed.vR e
    ; passedL = Embed.passedL e
    ; sufL = Embed.sufL e
    ; passedR = Embed.passedR e
    ; sufR = Embed.sufR e
    ; layL = subst (λ bs → namesL s ≡ Embed.passedL e ++ bs ++ Embed.sufL e)
                sameB (Embed.layL e)
    ; layR = Embed.layR e
    ; slot≡L = trans atw (Embed.slot≡L e)
    ; slot≡R = Embed.slot≡R e
    ; disL = Embed.disL e
    ; disR = Embed.disR e
    ; lenL = Embed.lenL e
    ; lenR = Embed.lenR e
    }

-- An empty pending list does not change the environment the walk sees.
walk-env : ∀ (s : SConf) p n slot w → envIL s ≡ [] →
           walk [] [] p n slot ≡ just w →
           walk [] (addPend [] (il s) (slotL s) (envIL s)) p n slot ≡ just w
walk-env s p n slot w z eq =
  subst (λ e → walk [] e p n slot ≡ just w)
    (sym (cong (addPend [] (il s) (slotL s)) z)) eq

-- `go` never builds a `mu`, so the unfold is the action itself.
castU : ∀ (s : SConf) (f : Focus) {p} → envPL s ≡ [] → left s ≡ p →
        Unfold [] [] p [] [] f →
        Unfold (envPL s) [] (left s) [] [] f
castU s f z lp u =
  subst (λ e → Unfold e [] (left s) [] [] f) (sym z)
    (subst (λ q → Unfold [] [] q [] [] f) (sym lp) u)

pick0-body : ∀ Γ P → Frag (go Γ (S.pick0 P)) → Frag (go Γ P)
pick0-body Γ P (fpick0 fq) = fq

pick1-body : ∀ Γ P → Frag (go Γ (S.pick1 P)) → Frag (go Γ P)
pick1-body Γ P (fpick1 fq) = fq

pickS : SConf → SProc → Bool → W → SConf
pickS s p b w = record s
  { left = p ; il = entry w ; slotL = atSlot w
  ; l2r = snoc (l2r s) (lab b)
  ; envPL = [] ; envIL = addPend [] (il s) (slotL s) (envIL s) }

labD : (c : A.Conf) (P : S.Proc) (b : Bool) → A.Conf
labD c P b = A.mk (A.Conf.cap c) P (A.Conf.rp c)
                  (A.snoc (A.Conf.l2r c) (A.lab b))
                  (A.Conf.r2l c) (A.Conf.lv c) (A.Conf.rv c)
                  (A.Conf.σ c) (A.Conf.τ c)

lab-does : ∀ (c : A.Conf) (b : Bool) (P : S.Proc)
           (eq : (A.Conf.lp c ≡ S.pick0 P) ⊎ (A.Conf.lp c ≡ S.pick1 P)) →
           length (A.Conf.l2r c) < A.Conf.cap c →
           Σ (A.measure (labD c P b) < A.measure c)
             (λ lt → A.sendLabL c b P eq ≡ A.does (labD c P b) lt)
lab-does c b P eq le with length (A.Conf.l2r c) <? A.Conf.cap c
... | no′ ¬le = ⊥-elim (¬le le)
... | yes′ _ = _ , refl

-- A pick writes its bit and continues. The other side is untouched.
step-pick0 : ∀ {g c s P} (e : Embed g c s)
             (eq : A.Conf.lp c ≡ S.pick0 P) →
             length (A.Conf.l2r c) < A.Conf.cap c →
             let d = labD c P false in
             Σ (A.measure d < A.measure c) (λ lt →
               Σ SConf (λ s′ →
                 A.sendLabL c false P (inj₁ eq) ≡ A.does d lt
                 × Embed g d s′
                 × s ⟶ₛ s′
                 × Step g (abs s) lside (abs s′)))
step-pick0 {g} {c} {s} {P} e eq le = lt , s′ , does , e′ , st , gs
  where
  Γ = Embed.preL e
  d = labD c P false
  lpE : left s ≡ go Γ (S.pick0 P)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  fq = pick0-body Γ P (subst Frag lpE (Embed.frL e))
  wp = walk-plain (go Γ P) (suc (il s)) (slotL s) (go-plain Γ P fq)
  w = Walked.w wp
  unf = castU s (f-pick0 (go Γ P)) (Embed.zPL e) lpE u-pick0
  wk = walk-env s (go Γ P) (suc (il s)) (slotL s) w (Embed.zIL e) (Walked.eq wp)
  rm = src-room le (qrel-len (Embed.qL e)) (Embed.cap≡ e)
  st : s ⟶ₛ pickS s (go Γ P) false w
  st = pick0-l unf rm wk
  fwd = sim-fwd (Embed.hold e) st
  gs = proj₁ (proj₂ fwd)
  h′ = proj₂ (proj₂ fwd)
  moved = lab-does c false P (inj₁ eq) le
  lt = proj₁ moved
  does = proj₂ moved
  s′ = pickS s (go Γ P) false w
  e′ : Embed g d s′
  e′ = record
    { hold = h′
    ; al≡ = Embed.al≡ e
    ; cap≡ = Embed.cap≡ e
    ; qL = qrel-snoc (Embed.qL e) (of-lab false)
    ; qR = Embed.qR e
    ; preL = Γ
    ; preR = Embed.preR e
    ; lp≡ = refl
    ; rp≡ = Embed.rp≡ e
    ; zPL = refl
    ; zPR = Embed.zPR e
    ; zIL = Embed.zIL e
    ; zIR = Embed.zIR e
    ; frL = fq
    ; frR = Embed.frR e
    ; vL = Embed.vL e
    ; vR = Embed.vR e
    ; passedL = Embed.passedL e
    ; sufL = Embed.sufL e
    ; passedR = Embed.passedR e
    ; sufR = Embed.sufR e
    ; layL = subst (λ bs → namesL s ≡ Embed.passedL e ++ bs ++ Embed.sufL e)
                (cong bnames lpE) (Embed.layL e)
    ; layR = Embed.layR e
    ; slot≡L = trans (Walked.at wp) (Embed.slot≡L e)
    ; slot≡R = Embed.slot≡R e
    ; disL = Embed.disL e
    ; disR = Embed.disR e
    ; lenL = Embed.lenL e
    ; lenR = Embed.lenR e
    }

step-pick1 : ∀ {g c s P} (e : Embed g c s)
             (eq : A.Conf.lp c ≡ S.pick1 P) →
             length (A.Conf.l2r c) < A.Conf.cap c →
             let d = labD c P true in
             Σ (A.measure d < A.measure c) (λ lt →
               Σ SConf (λ s′ →
                 A.sendLabL c true P (inj₂ eq) ≡ A.does d lt
                 × Embed g d s′
                 × s ⟶ₛ s′
                 × Step g (abs s) lside (abs s′)))
step-pick1 {g} {c} {s} {P} e eq le = lt , s′ , does , e′ , st , gs
  where
  Γ = Embed.preL e
  d = labD c P true
  lpE : left s ≡ go Γ (S.pick1 P)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  fq = pick1-body Γ P (subst Frag lpE (Embed.frL e))
  wp = walk-plain (go Γ P) (suc (il s)) (slotL s) (go-plain Γ P fq)
  w = Walked.w wp
  unf = castU s (f-pick1 (go Γ P)) (Embed.zPL e) lpE u-pick1
  wk = walk-env s (go Γ P) (suc (il s)) (slotL s) w (Embed.zIL e) (Walked.eq wp)
  rm = src-room le (qrel-len (Embed.qL e)) (Embed.cap≡ e)
  st : s ⟶ₛ pickS s (go Γ P) true w
  st = pick1-l unf rm wk
  fwd = sim-fwd (Embed.hold e) st
  gs = proj₁ (proj₂ fwd)
  h′ = proj₂ (proj₂ fwd)
  moved = lab-does c true P (inj₂ eq) le
  lt = proj₁ moved
  does = proj₂ moved
  s′ = pickS s (go Γ P) true w
  e′ : Embed g d s′
  e′ = record
    { hold = h′
    ; al≡ = Embed.al≡ e
    ; cap≡ = Embed.cap≡ e
    ; qL = qrel-snoc (Embed.qL e) (of-lab true)
    ; qR = Embed.qR e
    ; preL = Γ
    ; preR = Embed.preR e
    ; lp≡ = refl
    ; rp≡ = Embed.rp≡ e
    ; zPL = refl
    ; zPR = Embed.zPR e
    ; zIL = Embed.zIL e
    ; zIR = Embed.zIR e
    ; frL = fq
    ; frR = Embed.frR e
    ; vL = Embed.vL e
    ; vR = Embed.vR e
    ; passedL = Embed.passedL e
    ; sufL = Embed.sufL e
    ; passedR = Embed.passedR e
    ; sufR = Embed.sufR e
    ; layL = subst (λ bs → namesL s ≡ Embed.passedL e ++ bs ++ Embed.sufL e)
                (cong bnames lpE) (Embed.layL e)
    ; layR = Embed.layR e
    ; slot≡L = trans (Walked.at wp) (Embed.slot≡L e)
    ; slot≡R = Embed.slot≡R e
    ; disL = Embed.disL e
    ; disR = Embed.disR e
    ; lenL = Embed.lenL e
    ; lenR = Embed.lenR e
    }

lookup-here : ∀ x A Γ → lookupTy x ((x , A) ∷ Γ) ≡ just A
lookup-here x A Γ rewrite ==-refl x = refl

lookup-skip : ∀ x y A Γ → (x == y) ≡ false →
              lookupTy x ((y , A) ∷ Γ) ≡ lookupTy x Γ
lookup-skip x y A Γ eq rewrite eq = refl

venv-here : ∀ {A} x (v : S.ValExpr A) ve →
            A.lookupVEnv x ((x , A.evar A v) ∷ ve) ≡ just (A.evar A v)
venv-here x v ve with x ≟ x
... | yes′ _ = refl
... | no′ ¬eq = ⊥-elim (¬eq refl)

==-≢ : ∀ x y → (x == y) ≡ false → x ≢ y
==-≢ x y eq p with x ≟ y
==-≢ x y () p | yes′ _
==-≢ x y refl p | no′ ¬p = ¬p p

-- A different head name does not hide the binding `lookupVEnv` returns.
venv-skip : ∀ {B} x y (v : S.ValExpr B) ve (e : A.Entry) →
            x ≢ y →
            A.lookupVEnv x ve ≡ just e →
            A.lookupVEnv x ((y , A.evar B v) ∷ ve) ≡ just e
venv-skip x y v ve e neq eq with x ≟ y
... | yes′ p = ⊥-elim (neq p)
... | no′ _ rewrite eq = refl

-- A fragment echo is an echo of the binder's own type.
var-echo : ∀ Γ {A} x P → Frag (go Γ (S.put A (S.var {A} x) P)) →
           lookupTy x Γ ≡ just A × payClosed Γ (S.var {A} x) ≡ pEcho x
var-echo Γ {A} x P fp with closedTy A
var-echo Γ x P (fput () _) | false
var-echo Γ {A} x P fp | true with lookupTy x Γ | inspect (lookupTy x) Γ
var-echo Γ x P (fput () _) | true | nothing | _
var-echo Γ {A} x P fp | true | just B | [ lq ] with S.ty≟ A B
var-echo Γ x P (fput () _) | true | just B | [ _ ] | no′ _
var-echo Γ {A} x P (fput (fecho _) _) | true | just .A | [ _ ] | yes′ refl =
  refl , refl

-- The typed environment's literal is the value `prepare` sends.
resolve-var : ∀ {A} ve x (u : S.Val A) →
              A.lookupVEnv x ve ≡ just (A.evar A (S.lit u)) →
              A.resolveV ve (S.var {A} x) ≡ S.lit u
resolve-var ve x u eq with A.lookupVEnv x ve
resolve-var ve x u () | nothing
resolve-var {A} ve x u refl | just (A.evar .A (S.lit .u)) with S.ty≟ A A
... | yes′ refl = refl
... | no′ ¬p = ⊥-elim (¬p refl)

vrel-hit : ∀ {al slots names b Γ ve A} x →
           VRel al slots names b Γ ve →
           lookupTy x Γ ≡ just A →
           Σ (S.Val A) (λ u → Σ ℕ (λ i → Σ ℕ (λ k → Σ Atom (λ a →
             findS x names ≡ just i
             × nth slots i ≡ just (suc k)
             × nthA al k ≡ just a
             × valAtom (S.lit u) ≡ just a
             × A.lookupVEnv x ve ≡ just (A.evar A (S.lit u))))))
vrel-hit x vr0 ()
vrel-hit {al} {slots} {names} {A = A} x
         (vr1 {Γ} {ve = tail} {B} {u} {i} {k} {a} y fd _ nt na va rest) eq =
  on (x == y) refl
  where
  Hit = Σ (S.Val A) (λ u′ → Σ ℕ (λ i′ → Σ ℕ (λ k′ → Σ Atom (λ a′ →
        findS x names ≡ just i′ × nth slots i′ ≡ just (suc k′)
        × nthA al k′ ≡ just a′ × valAtom (S.lit u′) ≡ just a′
        × A.lookupVEnv x ((y , A.evar B (S.lit u)) ∷ tail) ≡
          just (A.evar A (S.lit u′))))))
  on : ∀ b → (x == y) ≡ b → Hit
  on true ab = same (==-≟ x y ab) eq
    where
    same : x ≡ y → lookupTy x ((y , B) ∷ Γ) ≡ just A → Hit
    same refl eq′ = cast (just-inj (trans (sym (lookup-here x B Γ)) eq′))
      where
      cast : B ≡ A → Hit
      cast refl = u , i , k , a , fd , nt , na , va , venv-here x (S.lit u) tail
  on false ab = lift (vrel-hit x rest skipped)
    where
    skipped : lookupTy x Γ ≡ just A
    skipped = trans (sym (lookup-skip x y B Γ ab)) eq
    Found = Σ (S.Val A) (λ u′ → Σ ℕ (λ i′ → Σ ℕ (λ k′ → Σ Atom (λ a′ →
            findS x names ≡ just i′ × nth slots i′ ≡ just (suc k′)
            × nthA al k′ ≡ just a′ × valAtom (S.lit u′) ≡ just a′
            × A.lookupVEnv x tail ≡ just (A.evar A (S.lit u′))))))
    lift : Found → Hit
    lift (u′ , i′ , k′ , a′ , fd′ , nt′ , na′ , va′ , lk) =
      u′ , i′ , k′ , a′ , fd′ , nt′ , na′ , va′ ,
      venv-skip x y (S.lit u) tail (A.evar A (S.lit u′)) (==-≢ x y ab) lk

-- `prepare` of an echo is the literal the typed environment stores.
prepare-var : ∀ {A} ve x (u : S.Val A) →
              A.lookupVEnv x ve ≡ just (A.evar A (S.lit u)) →
              A.prepare ve (S.var {A} x) ≡ S.lit u
prepare-var ve x u eq = cong A.normV (resolve-var ve x u eq)

-- The queued echo is that literal, at the carrier's own type.
echo-tok : ∀ {al σ A x u k a} → closedTy A ≡ true →
           nthA al k ≡ just a →
           valAtom (S.lit u) ≡ just a →
           TokOf al (A.pay (S.applyTy σ A) (A.car A (S.var {A} x) (S.lit u))) (pay k)
echo-tok {σ = σ} {A} {x} {u} cl nt va =
  of-pay (applyTy-id σ A cl) cl nt va

msg-ready : ∀ {A} (c : A.Conf) (x : String) (u : S.Val A) →
            A.prepare (A.Conf.lv c) (S.var {A} x) ≡ S.lit u →
            A.mkPayL c (S.var {A} x) ≡
              A.pay (S.applyTy (A.Conf.σ c) A) (A.car A (S.var {A} x) (S.lit u))
msg-ready {A} c x u eq =
  cong (λ r → A.pay (S.applyTy (A.Conf.σ c) A) (A.car A (S.var {A} x) r)) eq

-- A left echo of a fragment process is the source echo, and that
-- source echo is the graph step. The token is the message `mkPayL`
-- enqueues once `prepare` has read the literal.
echo-step : ∀ {g c s Γ A x P b} (h : Hold g s) →
            alpha s ≡ alphabet (codeL g) (codeR g) →
            envPL s ≡ [] → envIL s ≡ [] →
            left s ≡ go Γ (S.put A (S.var {A} x) P) →
            Frag (left s) →
            A.Conf.cap c ≡ cap s →
            QRel (alpha s) (A.Conf.l2r c) (l2r s) →
            VRel (alpha s) (el s) (namesL s) b Γ (A.Conf.lv c) →
            length (A.Conf.l2r c) < A.Conf.cap c →
            Σ ℕ (λ k → Σ W (λ w →
              let s′ = putLitS s (go Γ P) k w in
              s ⟶ₛ s′ × Step g (abs s) lside (abs s′) × Hold g s′
              × atSlot w ≡ slotL s
              × TokOf (alpha s) (A.mkPayL c (S.var {A} x)) (pay k)))
echo-step {g} {c} {s} {Γ} {A} {x} {P} h al≡ zP zI lp≡ fr ck qL vr le =
  step (put-closed Γ (S.var {A} x) P frG)
  where
  frG : Frag (go Γ (S.put A (S.var {A} x) P))
  frG = subst Frag lp≡ fr
  body = go Γ P
  step : closedTy A ≡ true →
         Σ ℕ (λ k → Σ W (λ w →
           let s′ = putLitS s body k w in
           s ⟶ₛ s′ × Step g (abs s) lside (abs s′) × Hold g s′
           × atSlot w ≡ slotL s
           × TokOf (alpha s) (A.mkPayL c (S.var {A} x)) (pay k)))
  step cl = use (var-echo Γ x P frG)
    where
    use : lookupTy x Γ ≡ just A × payClosed Γ (S.var {A} x) ≡ pEcho x →
          Σ ℕ (λ k → Σ W (λ w →
            let s′ = putLitS s body k w in
            s ⟶ₛ s′ × Step g (abs s) lside (abs s′) × Hold g s′
            × atSlot w ≡ slotL s
            × TokOf (alpha s) (A.mkPayL c (S.var {A} x)) (pay k)))
    use (lA , peq) = use2 (vrel-hit x vr lA)
      where
      aeq : payIn Γ (S.var {A} x) ≡ pEcho x
      aeq = trans (payIn-closed Γ (S.var {A} x) cl) peq
      proc≡ : left s ≡ sput (pEcho x) body
      proc≡ = trans lp≡ (cong (λ a → sput a body) aeq)
      HitV = Σ (S.Val A) (λ u → Σ ℕ (λ i → Σ ℕ (λ k → Σ Atom (λ atom →
             findS x (namesL s) ≡ just i
             × nth (el s) i ≡ just (suc k)
             × nthA (alpha s) k ≡ just atom
             × valAtom (S.lit u) ≡ just atom
             × A.lookupVEnv x (A.Conf.lv c) ≡ just (A.evar A (S.lit u))))))
      use2 : HitV →
             Σ ℕ (λ k → Σ W (λ w →
               let s′ = putLitS s body k w in
               s ⟶ₛ s′ × Step g (abs s) lside (abs s′) × Hold g s′
               × atSlot w ≡ slotL s
               × TokOf (alpha s) (A.mkPayL c (S.var {A} x)) (pay k)))
      use2 (u , i , k , atom , fd , nt , na , va , lk) =
        k , w , st , gs , h′ , Walked.at wp , tok
        where
        sv = slot-suc (el s) i k nt
        u0 : Unfold [] [] (sput (pEcho x) body) [] [] (f-put (pEcho x) body)
        u0 = u-put
        u1 : Unfold [] [] (left s) [] [] (f-put (pEcho x) body)
        u1 = subst (λ p → Unfold [] [] p [] [] (f-put (pEcho x) body))
               (sym proc≡) u0
        unf : Unfold (envPL s) [] (left s) [] [] (f-put (pEcho x) body)
        unf = subst (λ e → Unfold e [] (left s) [] [] (f-put (pEcho x) body))
                (sym zP) u1
        wp = walk-plain body (suc (il s)) (slotL s)
               (go-plain Γ P (put-body Γ (S.var {A} x) P frG))
        w = Walked.w wp
        wk = subst (λ e → walk [] e body (suc (il s)) (slotL s) ≡ just w)
               (sym (cong (λ e → addPend [] (il s) (slotL s) e) zI))
               (Walked.eq wp)
        rm = src-room le (qrel-len qL) ck
        st = echo-l unf fd sv rm wk
        moved = sim-fwd h st
        gs = proj₁ (proj₂ moved)
        h′ = proj₂ (proj₂ moved)
        prep = prepare-var (A.Conf.lv c) x u lk
        tok0 = echo-tok {σ = A.Conf.σ c} {x = x} cl na va
        tok = subst (λ m → TokOf (alpha s) m (pay k))
                (sym (msg-ready c x u prep)) tok0

-- A variable put on the left is one async step, one source echo, and
-- the embedding of the pair it reaches.
step-put-var : ∀ {g c s A x P} (e : Embed g c s)
               (eq : A.Conf.lp c ≡ S.put A (S.var {A} x) P) →
               length (A.Conf.l2r c) < A.Conf.cap c →
               let d = putD c P (S.var {A} x) in
               Σ (A.measure d < A.measure c) (λ lt →
                 Σ SConf (λ s′ →
                   A.sendPutL c (S.var {A} x) P eq ≡ A.does d lt
                   × Embed g d s′
                   × s ⟶ₛ s′
                   × Step g (abs s) lside (abs s′)))
step-put-var {g} {c} {s} {A} {x} {P} e eq le =
  lt , s′ , does , e′ , st , gs
  where
  Γ = Embed.preL e
  d = putD c P (S.var {A} x)
  lpE : left s ≡ go Γ (S.put A (S.var {A} x) P)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  frPut : Frag (go Γ (S.put A (S.var {A} x) P))
  frPut = subst Frag lpE (Embed.frL e)
  moved = put-does c {v = S.var {A} x} eq le refl
  lt = proj₁ moved
  does = proj₂ moved
  packed = echo-step {g = g} {c = c} {s = s} {Γ = Γ} {A = A} {x = x} {P = P}
             (Embed.hold e) (Embed.al≡ e) (Embed.zPL e) (Embed.zIL e)
             lpE (Embed.frL e) (Embed.cap≡ e) (Embed.qL e) (Embed.vL e) le
  k = proj₁ packed
  rest1 = proj₂ packed
  w = proj₁ rest1
  rest2 = proj₂ rest1
  st = proj₁ rest2
  gs = proj₁ (proj₂ rest2)
  h′ = proj₁ (proj₂ (proj₂ rest2))
  atw = proj₁ (proj₂ (proj₂ (proj₂ rest2)))
  tok = proj₂ (proj₂ (proj₂ (proj₂ rest2)))
  s′ = putLitS s (go Γ P) k w
  sameB = cong bnames lpE
  e′ : Embed g d s′
  e′ = record
    { hold = h′
    ; al≡ = Embed.al≡ e
    ; cap≡ = Embed.cap≡ e
    ; qL = qrel-snoc (Embed.qL e) tok
    ; qR = Embed.qR e
    ; preL = Γ
    ; preR = Embed.preR e
    ; lp≡ = refl
    ; rp≡ = Embed.rp≡ e
    ; zPL = refl
    ; zPR = Embed.zPR e
    ; zIL = Embed.zIL e
    ; zIR = Embed.zIR e
    ; frL = put-body Γ (S.var {A} x) P frPut
    ; frR = Embed.frR e
    ; vL = Embed.vL e
    ; vR = Embed.vR e
    ; passedL = Embed.passedL e
    ; sufL = Embed.sufL e
    ; passedR = Embed.passedR e
    ; sufR = Embed.sufR e
    ; layL = subst (λ bs → namesL s ≡ Embed.passedL e ++ bs ++ Embed.sufL e)
                sameB (Embed.layL e)
    ; layR = Embed.layR e
    ; slot≡L = trans atw (Embed.slot≡L e)
    ; slot≡R = Embed.slot≡R e
    ; disL = Embed.disL e
    ; disR = Embed.disR e
    ; lenL = Embed.lenL e
    ; lenR = Embed.lenR e
    }

------------------------------------------------------------------------
-- A repeated name is not fresh in the prefix that already holds it.
------------------------------------------------------------------------

true≢false : true ≢ false
true≢false ()

fresh-hit : ∀ x pre suf → freshN x (pre ++ x ∷ suf) ≡ false
fresh-hit x [] suf rewrite ==-refl x = refl
fresh-hit x (y ∷ pre) suf with x == y
... | true = refl
... | false = fresh-hit x pre suf

≢-== : ∀ x y → x ≢ y → (x == y) ≡ false
≢-== x y neq with x ≟ y
... | yes′ p = ⊥-elim (neq p)
... | no′ _ = refl

fresh-not : ∀ y x pre suf → freshN y (pre ++ x ∷ suf) ≡ true → x ≢ y
fresh-not y x pre suf eq refl =
  true≢false (sym (trans (sym (fresh-hit y pre suf)) eq))

fresh-skip : ∀ x y pre → (x == y) ≡ false →
             freshN x pre ≡ true → freshN x (y ∷ pre) ≡ true
fresh-skip x y pre eq fr rewrite eq = fr

-- Distinct binders put the first copy of `x` at the end of `pre`.
dist-fresh : ∀ pre x suf → distinctN (pre ++ x ∷ suf) ≡ true → freshN x pre ≡ true
dist-fresh [] x suf _ = refl
dist-fresh (y ∷ pre) x suf eq =
  fresh-skip x y pre
    (≢-== x y (fresh-not y x pre suf (∧-left eq)))
    (dist-fresh pre x suf (∧-right eq))

m≤m+n : ∀ m n → m ≤ m + n
m≤m+n zero n = z≤n
m≤m+n (suc m) n = s≤s (m≤m+n m n)

length-set : ∀ i v xs → length (setNth i v xs) ≡ length xs
length-set zero _ [] = refl
length-set (suc _) _ [] = refl
length-set zero _ (_ ∷ _) = refl
length-set (suc i) v (_ ∷ xs) = cong suc (length-set i v xs)

<-suc : ∀ {i b} → i < b → i < suc b
<-suc le = ≤-trans le (n≤1+n _)

i≢ : ∀ {i j} → i < j → i ≢ j
i≢ le refl = no le
  where
  no : ∀ {n} → suc n ≤ n → ⊥
  no {zero} ()
  no {suc n} (s≤s p) = no p

vrel-widen : ∀ {al slots names b Γ ve} →
             VRel al slots names b Γ ve →
             VRel al slots names (suc b) Γ ve
vrel-widen vr0 = vr0
vrel-widen (vr1 x fd lt nt na va rest) =
  vr1 x fd (<-suc lt) nt na va (vrel-widen rest)

-- A step that skips a branch widens the bound by that branch's length.
vrel-plus : ∀ {al slots names b Γ ve} n →
            VRel al slots names b Γ ve →
            VRel al slots names (b + n) Γ ve
vrel-plus {al} {slots} {names} {b} {Γ} {ve} zero vr =
  subst (λ n → VRel al slots names n Γ ve) (sym (+-identityʳ b)) vr
vrel-plus {al} {slots} {names} {b} {Γ} {ve} (suc n) vr =
  subst (λ n → VRel al slots names n Γ ve) (sym (+-suc b n))
    (vrel-plus n (vrel-widen vr))

vrel-write : ∀ {al names Γ ve} b slots v →
             VRel al slots names b Γ ve →
             VRel al (setNth b v slots) names b Γ ve
vrel-write _ _ _ vr0 = vr0
vrel-write b slots v (vr1 {i = i} x fd lt nt na va rest) =
  vr1 x fd lt
      (trans (nth-other b i v slots (λ eq → i≢ lt (sym eq))) nt)
      na va (vrel-write b slots v rest)

-- What `go` builds for a fragment get.
get-view : ∀ Γ A x P → Frag (go Γ (S.get A x P)) →
           Σ Tag (λ t →
             go Γ (S.get A x P) ≡ sget t x (go ((x , A) ∷ Γ) P)
             × Frag (go ((x , A) ∷ Γ) P)
             × closedTy A ≡ true
             × newName x Γ ≡ true
             × goodGet A ≡ just t)
get-view Γ A x P fp with closedTy A
get-view Γ A x P () | false
get-view Γ A x P fp | true with goodGet A
get-view Γ A x P () | true | nothing
get-view Γ A x P fp | true | just t with newName x Γ
get-view Γ A x P () | true | just t | false
get-view Γ A x P (fget fq) | true | just t | true =
  t , refl , fq , refl , refl , refl

bump-atom : ∀ p a → asAtom (bump p) ≡ just a → Σ ℕ (λ n → a ≡ aNat (suc n))
bump-atom (pNat n) .(aNat (suc n)) refl = n , refl
bump-atom (pBit _) _ ()
bump-atom (pCon _) _ ()
bump-atom (pEcho _) _ ()
bump-atom pOut _ ()

-- A value the fragment can receive fits the tag `goodGet` stored.
fits-val : ∀ {A} t a (u : S.Val A) →
           goodGet A ≡ just t →
           valAtom (S.lit u) ≡ just a →
           fits t a ≡ true
fits-val {S.nat} t a S.zero refl refl = refl
fits-val {S.nat} t a (S.suc u) refl va =
  let n , aeq = bump-atom (payVal u) a va
  in subst (λ z → fits tagNat z ≡ true) (sym aeq) refl
fits-val {S.bit} t a S.b0 refl refl = refl
fits-val {S.bit} t a S.b1 refl refl = refl
fits-val {S.unit} t a S.tt () va
fits-val {S.pair _ _} t a (S.tup _ _) () va
fits-val {S.rec _} t a (S.rec _) () va
fits-val {S.vec _ _} t a (S.rep _) () va
fits-val {S.dat d as} t a (S.con s sp) gt va with nullCtors (S.ctorsOf d)
fits-val _ _ (S.con _ _) () _ | false
fits-val {S.dat d as} t a (S.con s S.snil) refl va | true
  with S.fits (S.con {d} {as} s S.snil)
fits-val _ _ (S.con _ S.snil) refl () | true | false
fits-val _ _ (S.con _ S.snil) refl refl | true | true = refl
fits-val _ _ (S.con _ (S.scons _ _ _)) _ () | true

slot-lt : ∀ {A : Set} (pre : List A) x (suf : List A) →
          length pre < length (pre ++ x ∷ suf)
slot-lt pre x suf =
  subst (λ n → suc (length pre) ≤ n)
    (sym (length-++ pre {x ∷ suf}))
    (subst (λ n → suc (length pre) ≤ n)
       (sym (+-suc (length pre) (length suf)))
       (s≤s (m≤m+n (length pre) (length suf))))

len-snoc : ∀ {A : Set} (xs : List A) (y : A) → length (xs ++ y ∷ []) ≡ suc (length xs)
len-snoc xs y =
  trans (length-++ xs {y ∷ []})
    (trans (+-suc (length xs) zero) (cong suc (+-identityʳ (length xs))))

val-lit : ∀ {B} (r : S.ValExpr B) a → valAtom r ≡ just a → Σ (S.Val B) (λ u → r ≡ S.lit u)
val-lit (S.lit u) _ _ = u , refl
val-lit (S.var _) _ ()
val-lit (S.call _ _) _ ()

-- `takePay` succeeds only when the wire type is the receiver's type.
take-eq : ∀ σ (T W : S.Ty) (ca0 ca : A.Carrier) →
          A.takePay σ T (A.pay W ca0) ≡ A.tpay ca →
          S.applyTy σ T ≡ W
take-eq σ T W ca0 ca eq with S.ty≟ (S.applyTy σ T) W
take-eq σ T W ca0 ca _ | yes′ p = p
take-eq σ T W ca0 ca () | no′ _

react-get : ∀ (c : A.Conf) (T : S.Ty) x P (eq : A.Conf.lp c ≡ S.get T x P) →
            A.reactL c ≡ A.recvGetL c T x P eq
react-get c T x P refl = refl

getD : (c : A.Conf) (P : S.Proc) (x : String) (ca : A.Carrier)
       (rest : List A.Msg) → A.Conf
getD c P x ca rest =
  A.mk (A.Conf.cap c) P (A.Conf.rp c) (A.Conf.l2r c) rest
       (A.bindV x ca (A.Conf.lv c)) (A.Conf.rv c)
       (A.extCar x ca (A.Conf.σ c)) (A.Conf.τ c)

recv-does : ∀ (c : A.Conf) (T : S.Ty) x P (eq : A.Conf.lp c ≡ S.get T x P)
            m rest ca →
            A.Conf.r2l c ≡ m ∷ rest →
            A.takePay (A.Conf.σ c) T m ≡ A.tpay ca →
            Σ (A.measure (getD c P x ca rest) < A.measure c)
              (λ lt → A.recvGetL c T x P eq ≡ A.does (getD c P x ca rest) lt)
recv-does c T x P eq m rest ca qe te rewrite qe | te = _ , refl

-- The source configuration a left get reaches.
getS : SConf → SProc → List Tok → ℕ → W → SConf
getS s p rest k w = record s
  { left = p ; il = entry w ; slotL = atSlot w
  ; r2l = rest ; el = setNth (slotL s) (suc k) (el s)
  ; envPL = [] ; envIL = addPend [] (il s) (slotL s) (envIL s) }

-- `freshN` and `fresh` are the same walk. `findS-at` is stated with `fresh`.
fresh≡ : ∀ x xs → freshN x xs ≡ fresh x xs
fresh≡ _ [] = refl
fresh≡ x (y ∷ ys) with x == y
... | true = refl
... | false = fresh≡ x ys

-- `xs ++ (y ∷ ys)` is the prefix `xs ++ [y]` followed by `ys`.
cons-++ : ∀ {A : Set} (xs : List A) (y : A) (ys : List A) →
          xs ++ (y ∷ ys) ≡ (xs ++ (y ∷ [])) ++ ys
cons-++ xs y ys = sym (++-assoc xs (y ∷ []) ys)

-- A label is not a payload, so `takePay` refuses it.
lab-not : ∀ σ (T : S.Ty) (b : Bool) (ca : A.Carrier) →
          A.takePay σ T (A.lab b) ≡ A.tpay ca → ⊥
lab-not _ _ _ _ ()

-- The carrier `takePay` returns is the carrier the message carried.
take-car : ∀ σ (T W : S.Ty) (ca0 ca : A.Carrier) →
           A.takePay σ T (A.pay W ca0) ≡ A.tpay ca →
           ca0 ≡ ca
take-car σ T W ca0 ca eq with S.ty≟ (S.applyTy σ T) W
take-car σ T W ca0 .ca0 refl | yes′ _ = refl
take-car σ T W ca0 ca () | no′ _

-- The head of a related queue is one token, and the tails stay related.
qrel-head : ∀ {al m ms ts} → QRel al (m ∷ ms) ts →
            Σ Tok (λ t → Σ (List Tok) (λ us →
              ts ≡ t ∷ us × TokOf al m t × QRel al ms us))
qrel-head (qcons {t = t} {ts = us} tk q) = t , us , refl , tk , q

-- The other direction: a cons of tokens is a cons of messages.
qrel-cons : ∀ {al ms ts t us} → QRel al ms ts → ts ≡ t ∷ us →
            Σ A.Msg (λ m → Σ (List A.Msg) (λ ms′ →
              ms ≡ m ∷ ms′ × TokOf al m t × QRel al ms′ us))
qrel-cons qnil ()
qrel-cons (qcons {m = m} tk q) refl = m , _ , refl , tk , q

-- An empty message queue is an empty token queue.
qrel-nil : ∀ {al ts} → QRel al [] ts → ts ≡ []
qrel-nil qnil = refl

nil≢cons : ∀ {A : Set} {x : A} {xs} → [] ≡ x ∷ xs → ⊥
nil≢cons ()

-- A left get that `takePay` accepts is one async step, one source get,
-- and the embedding of the pair it reaches. The new binding is the
-- literal the token carried, written at the slot `namesL` reserved.
step-get-pay : ∀ {g c s T x P m rest ca} (e : Embed g c s)
               (eq : A.Conf.lp c ≡ S.get T x P) →
               A.Conf.r2l c ≡ m ∷ rest →
               A.takePay (A.Conf.σ c) T m ≡ A.tpay ca →
               let d = getD c P x ca rest in
               Σ (A.measure d < A.measure c) (λ lt →
                 Σ SConf (λ s′ →
                   A.recvGetL c T x P eq ≡ A.does d lt
                   × Embed g d s′
                   × s ⟶ₛ s′
                   × Step g (abs s) lside (abs s′)))
step-get-pay {g} {c} {s} {T} {x} {P} {m} {rest} {ca} e eq qe te =
  proj₁ moved , from (qrel-head qHere)
  where
  Γ = Embed.preL e
  passed = Embed.passedL e
  suf = Embed.sufL e
  lpE : left s ≡ go Γ (S.get T x P)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  frG : Frag (go Γ (S.get T x P))
  frG = subst Frag lpE (Embed.frL e)
  view = get-view Γ T x P frG
  t = proj₁ view
  geq = proj₁ (proj₂ view)
  fq = proj₁ (proj₂ (proj₂ view))
  clT = proj₁ (proj₂ (proj₂ (proj₂ view)))
  gt = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ view))))
  body = go ((x , T) ∷ Γ) P
  proc≡ : left s ≡ sget t x body
  proc≡ = trans lpE geq
  d = getD c P x ca rest
  moved = recv-does c T x P eq m rest ca qe te
  qHere : QRel (alpha s) (m ∷ rest) (r2l s)
  qHere = subst (λ ms → QRel (alpha s) ms (r2l s)) qe (Embed.qR e)
  Result = Σ SConf (λ s′ →
             A.recvGetL c T x P eq ≡ A.does d (proj₁ moved)
             × Embed g d s′
             × s ⟶ₛ s′
             × Step g (abs s) lside (abs s′))
  from : Σ Tok (λ tok → Σ (List Tok) (λ us →
           r2l s ≡ tok ∷ us × TokOf (alpha s) m tok × QRel (alpha s) rest us)) →
         Result
  from (_ , _ , _ , of-lab b , _) = ⊥-elim (lab-not (A.Conf.σ c) T b ca te)
  from (.(pay k) , us , qeq , of-pay {W} {B} {v} {r} {k} {a} wEq clB na va , qTail) =
    cast (trans (sym (applyTy-id (A.Conf.σ c) T clT))
                (trans (take-eq (A.Conf.σ c) T W (A.car B v r) ca te) wEq))
    where
    cast : T ≡ B → Result
    cast refl =
      s′ , proj₂ moved , e′ , st , gs
      where
      u = proj₁ (val-lit r a va)
      r≡ = proj₂ (val-lit r a va)
      vaU : valAtom (S.lit u) ≡ just a
      vaU = subst (λ e → valAtom e ≡ just a) r≡ va
      fit = fits-val t a u gt vaU
      ca≡ : A.car T v (S.lit u) ≡ ca
      ca≡ = trans (sym (cong (A.car T v) r≡))
                  (take-car (A.Conf.σ c) T W (A.car T v r) ca te)
      ve≡ : A.bindV x ca (A.Conf.lv c) ≡ (x , A.evar T (S.lit u)) ∷ A.Conf.lv c
      ve≡ = cong (λ z → A.bindV x z (A.Conf.lv c)) (sym ca≡)
      suf′ = bnames body ++ suf
      names≡ : namesL s ≡ passed ++ (x ∷ suf′)
      names≡ = trans (Embed.layL e) (cong (λ bs → passed ++ bs ++ suf) (cong bnames proc≡))
      disAt : distinctN (passed ++ (x ∷ suf′)) ≡ true
      disAt = subst (λ ns → distinctN ns ≡ true) names≡ (Embed.disL e)
      fr = trans (sym (fresh≡ x passed)) (dist-fresh passed x suf′ disAt)
      fd : findS x (namesL s) ≡ just (length passed)
      fd = trans (cong (findS x) names≡) (findS-at x passed suf′ fr)
      slot< : length passed < length (el s)
      slot< = subst (λ n → length passed < n)
                (sym (trans (Embed.lenL e) (cong length names≡)))
                (slot-lt passed x suf′)
      b = length passed
      nt = nth-set b (suc k) (el s) slot<
      kept = vrel-widen (vrel-write b (el s) (suc k) (Embed.vL e))
      built = vr1 x fd ≤-refl nt na vaU kept
      slots≡ : setNth (slotL s) (suc k) (el s) ≡ setNth b (suc k) (el s)
      slots≡ = cong (λ i → setNth i (suc k) (el s)) (Embed.slot≡L e)
      vHere = subst (λ xs → VRel (alpha s) xs (namesL s) (suc b)
                              ((x , T) ∷ Γ)
                              (A.bindV x ca (A.Conf.lv c)))
               (sym slots≡)
               (subst (λ ve → VRel (alpha s) (setNth b (suc k) (el s)) (namesL s)
                                  (suc b) ((x , T) ∷ Γ) ve)
                  (sym ve≡) built)
      vDone = subst (λ n → VRel (alpha s) (setNth (slotL s) (suc k) (el s))
                                 (namesL s) n ((x , T) ∷ Γ)
                                 (A.bindV x ca (A.Conf.lv c)))
                (sym (len-snoc passed x)) vHere
      u0 : Unfold [] [] (sget t x body) [] [] (f-get t x body)
      u0 = u-get
      u1 = subst (λ p → Unfold [] [] p [] [] (f-get t x body)) (sym proc≡) u0
      unf = subst (λ e → Unfold e [] (left s) [] [] (f-get t x body))
              (sym (Embed.zPL e)) u1
      wp = walk-plain body (suc (il s)) (suc (slotL s))
             (go-plain ((x , T) ∷ Γ) P fq)
      w = Walked.w wp
      wk = subst (λ e → walk [] e body (suc (il s)) (suc (slotL s)) ≡ just w)
             (sym (cong (λ e → addPend [] (il s) (slotL s) e) (Embed.zIL e)))
             (Walked.eq wp)
      st = get-l unf qeq na fit wk
      stepped = sim-fwd (Embed.hold e) st
      gs = proj₁ (proj₂ stepped)
      h′ = proj₂ (proj₂ stepped)
      s′ = getS s body us k w
      e′ : Embed g d s′
      e′ = record
        { hold = h′
        ; al≡ = Embed.al≡ e
        ; cap≡ = Embed.cap≡ e
        ; qL = Embed.qL e
        ; qR = qTail
        ; preL = (x , T) ∷ Γ
        ; preR = Embed.preR e
        ; lp≡ = refl
        ; rp≡ = Embed.rp≡ e
        ; zPL = refl
        ; zPR = Embed.zPR e
        ; zIL = cong (addPend [] (il s) (slotL s)) (Embed.zIL e)
        ; zIR = Embed.zIR e
        ; frL = fq
        ; frR = Embed.frR e
        ; vL = vDone
        ; vR = Embed.vR e
        ; passedL = passed ++ (x ∷ [])
        ; sufL = suf
        ; passedR = Embed.passedR e
        ; sufR = Embed.sufR e
        ; layL = trans names≡ (cons-++ passed x suf′)
        ; layR = Embed.layR e
        ; slot≡L = trans (trans (Walked.at wp) (cong suc (Embed.slot≡L e)))
                         (sym (len-snoc passed x))
        ; slot≡R = Embed.slot≡R e
        ; disL = Embed.disL e
        ; disR = Embed.disR e
        ; lenL = trans (length-set (slotL s) (suc k) (el s)) (Embed.lenL e)
        ; lenR = Embed.lenR e
        }

------------------------------------------------------------------------
-- The right-hand literal put. The alphabet membership is read from
-- the right code, and the token joins `r2l`.
------------------------------------------------------------------------

in-alphaR : ∀ a L R → InA a (lits R) → InA a (alphabet L R)
in-alphaR a L R mem =
  layers-keep (growCount L + growCount R) a (adds (lits L) (lits R))
    (adds-keep a (lits L) (lits R) mem)

atom-ofR : ∀ {g s atom j} (h : Hold g s) →
           alpha s ≡ alphabet (codeL g) (codeR g) →
           (ir s , bPut atom j) ∈ Hold.bsR h →
           Σ ℕ (λ k → findA atom (alpha s) ≡ just k)
atom-ofR {g} {s} {atom} h al≡ mem =
  let inn = lits-in (codeR g) (ir s) atom _ (seenR h mem)
      k , fk = find-hit atom (alphabet (codeL g) (codeR g))
                 (in-alphaR atom (codeL g) (codeR g) inn)
  in k , subst (λ xs → findA atom xs ≡ just k) (sym al≡) fk

putLitR : SConf → SProc → ℕ → W → SConf
putLitR s p k w = record s
  { right = p ; ir = entry w ; slotR = atSlot w
  ; r2l = snoc (r2l s) (pay k)
  ; envPR = [] ; envIR = addPend [] (ir s) (slotR s) (envIR s) }

castUR : ∀ (s : SConf) (f : Focus) {p} → envPR s ≡ [] → right s ≡ p →
         Unfold [] [] p [] [] f →
         Unfold (envPR s) [] (right s) [] [] f
castUR s f z rp u =
  subst (λ e → Unfold e [] (right s) [] [] f) (sym z)
    (subst (λ q → Unfold [] [] q [] [] f) (sym rp) u)

walk-envR : ∀ (s : SConf) p n slot w → envIR s ≡ [] →
            walk [] [] p n slot ≡ just w →
            walk [] (addPend [] (ir s) (slotR s) (envIR s)) p n slot ≡ just w
walk-envR s p n slot w z eq =
  subst (λ e → walk [] e p n slot ≡ just w)
    (sym (cong (addPend [] (ir s) (slotR s)) z)) eq

lit-stepR : ∀ {g c s Γ B u P} (h : Hold g s) →
            alpha s ≡ alphabet (codeL g) (codeR g) →
            envPR s ≡ [] → envIR s ≡ [] →
            right s ≡ go Γ (S.put B (S.lit u) P) →
            Frag (right s) →
            A.Conf.cap c ≡ cap s →
            QRel (alpha s) (A.Conf.r2l c) (r2l s) →
            length (A.Conf.r2l c) < A.Conf.cap c →
            Σ ℕ (λ k → Σ W (λ w →
              let s′ = putLitR s (go Γ P) k w in
              s ⟶ₛ s′ × Step g (abs s) rside (abs s′) × Hold g s′
              × atSlot w ≡ slotR s
              × TokOf (alpha s) (A.mkPayR c {A = B} (S.lit u)) (pay k)))
lit-stepR {g} {c} {s} {Γ} {B} {u} {P} h al≡ zP zI rp≡ fr ck qR le =
  step (put-closed Γ (S.lit u) P (subst Frag rp≡ fr))
  where
  step : closedTy B ≡ true →
         Σ ℕ (λ k → Σ W (λ w →
           let s′ = putLitR s (go Γ P) k w in
           s ⟶ₛ s′ × Step g (abs s) rside (abs s′) × Hold g s′
           × atSlot w ≡ slotR s
           × TokOf (alpha s) (A.mkPayR c {A = B} (S.lit u)) (pay k)))
  step cl = onSend (rightSend h unf)
    where
    unf : Unfold (envPR s) [] (right s) [] []
            (f-put (payClosed Γ (S.lit u)) (go Γ P))
    unf =
      let aeq = payIn-closed Γ (S.lit u) cl
          lit = subst (λ a → Unfold [] [] (sput a (go Γ P)) [] []
                               (f-put a (go Γ P)))
                  aeq u-put
          proc≡ = trans (sym (cong (λ a → sput a (go Γ P)) aeq)) (sym rp≡)
          atRight = subst (λ p → Unfold [] [] p [] []
                              (f-put (payClosed Γ (S.lit u)) (go Γ P)))
                     proc≡ lit
      in subst (λ e → Unfold e [] (right s) [] []
                    (f-put (payClosed Γ (S.lit u)) (go Γ P)))
           (sym zP) atRight
    wp : Walked (suc (ir s)) (slotR s) (go Γ P)
    wp = walk-plain (go Γ P) (suc (ir s)) (slotR s)
           (go-plain Γ P (put-body Γ (S.lit u) P (subst Frag rp≡ fr)))
    onSend : Send (Hold.bsR h) _ (ir s) (slotR s) (envIR s) [] []
                 (payClosed Γ (S.lit u)) (go Γ P) →
            Σ ℕ (λ k → Σ W (λ w →
              let s′ = putLitR s (go Γ P) k w in
              s ⟶ₛ s′ × Step g (abs s) rside (abs s′) × Hold g s′
              × atSlot w ≡ slotR s
              × TokOf (alpha s) (A.mkPayR c {A = B} (S.lit u)) (pay k)))
    onSend (echoed x _ _ _ aeq _ _ _ _ _ _) = ⊥-elim (pay-echo u x aeq)
    onSend (sent atom j wd aeq _ mem _ _ _) =
      let k , fk = atom-ofR h al≡ mem
          w = Walked.w wp
          wk = subst (λ e → walk [] e (go Γ P) (suc (ir s)) (slotR s) ≡ just w)
                 (sym (cong (λ e → addPend [] (ir s) (slotR s) e) zI))
                 (Walked.eq wp)
          rm = src-room le (qrel-len qR) ck
          st = put-r unf aeq fk rm wk
          _ , gs , h′ = sim-fwd h st
          tok = pay-tok cl (findA-nth atom (alpha s) k fk) aeq
      in k , w , st , gs , h′ , Walked.at wp , tok

putDR : (c : A.Conf) (P : S.Proc) {B : S.Ty} → S.ValExpr B → A.Conf
putDR c P v = A.mk (A.Conf.cap c) (A.Conf.lp c) P
                   (A.Conf.l2r c)
                   (A.snoc (A.Conf.r2l c) (A.mkPayR c v))
                   (A.Conf.lv c) (A.Conf.rv c)
                   (A.Conf.σ c) (A.Conf.τ c)

put-doesR : ∀ (c : A.Conf) {B : S.Ty} {v : S.ValExpr B} {P : S.Proc}
            (eq : A.Conf.rp c ≡ S.put B v P) →
            length (A.Conf.r2l c) < A.Conf.cap c →
            S.sent v ≡ true →
            Σ (A.measure (putDR c P v) < A.measure c)
              (λ lt → A.sendPutR c v P eq ≡ A.does (putDR c P v) lt)
put-doesR c {v = v} eq le sv with length (A.Conf.r2l c) <? A.Conf.cap c
... | no′ ¬le = ⊥-elim (¬le le)
... | yes′ _ with S.sent? v
... | no′ ¬p = ⊥-elim (¬p sv)
... | yes′ _ = _ , refl

step-put-litR : ∀ {g c s B u P} (e : Embed g c s)
                (eq : A.Conf.rp c ≡ S.put B (S.lit u) P) →
                length (A.Conf.r2l c) < A.Conf.cap c →
                let d = putDR c P (S.lit u) in
                Σ (A.measure d < A.measure c) (λ lt →
                  Σ SConf (λ s′ →
                    A.sendPutR c (S.lit u) P eq ≡ A.does d lt
                    × Embed g d s′
                    × s ⟶ₛ s′
                    × Step g (abs s) rside (abs s′)))
step-put-litR {g} {c} {s} {B} {u} {P} e eq le =
  lt , s′ , does , e′ , st , gs
  where
  Γ = Embed.preR e
  d = putDR c P (S.lit u)
  rpE : right s ≡ go Γ (S.put B (S.lit u) P)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  frPut : Frag (go Γ (S.put B (S.lit u) P))
  frPut = subst Frag rpE (Embed.frR e)
  moved = put-doesR c {v = S.lit u} eq le (image-sent Γ (S.lit u) P frPut)
  lt = proj₁ moved
  does = proj₂ moved
  packed = lit-stepR {g = g} {c = c} {s = s} {Γ = Γ} {B = B} {u = u} {P = P}
             (Embed.hold e) (Embed.al≡ e) (Embed.zPR e) (Embed.zIR e)
             rpE (Embed.frR e) (Embed.cap≡ e) (Embed.qR e) le
  k = proj₁ packed
  rest = proj₂ packed
  w = proj₁ rest
  rest2 = proj₂ rest
  st = proj₁ rest2
  gs = proj₁ (proj₂ rest2)
  h′ = proj₁ (proj₂ (proj₂ rest2))
  atw = proj₁ (proj₂ (proj₂ (proj₂ rest2)))
  tok = proj₂ (proj₂ (proj₂ (proj₂ rest2)))
  s′ = putLitR s (go Γ P) k w
  sameB = cong bnames rpE
  e′ : Embed g d s′
  e′ = record
    { hold = h′
    ; al≡ = Embed.al≡ e
    ; cap≡ = Embed.cap≡ e
    ; qL = Embed.qL e
    ; qR = qrel-snoc (Embed.qR e) tok
    ; preL = Embed.preL e
    ; preR = Γ
    ; lp≡ = Embed.lp≡ e
    ; rp≡ = refl
    ; zPL = Embed.zPL e
    ; zPR = refl
    ; zIL = Embed.zIL e
    ; zIR = Embed.zIR e
    ; frL = Embed.frL e
    ; frR = put-body Γ (S.lit u) P frPut
    ; vL = Embed.vL e
    ; vR = Embed.vR e
    ; passedL = Embed.passedL e
    ; sufL = Embed.sufL e
    ; passedR = Embed.passedR e
    ; sufR = Embed.sufR e
    ; layL = Embed.layL e
    ; layR = subst (λ bs → namesR s ≡ Embed.passedR e ++ bs ++ Embed.sufR e)
                sameB (Embed.layR e)
    ; slot≡L = Embed.slot≡L e
    ; slot≡R = trans atw (Embed.slot≡R e)
    ; disL = Embed.disL e
    ; disR = Embed.disR e
    ; lenL = Embed.lenL e
    ; lenR = Embed.lenR e
    }

msg-readyR : ∀ {T : S.Ty} (c : A.Conf) (x : String) (u : S.Val T) →
             A.prepare (A.Conf.rv c) (S.var {T} x) ≡ S.lit u →
             A.mkPayR c (S.var {T} x) ≡
               A.pay (S.applyTy (A.Conf.τ c) T) (A.car T (S.var {T} x) (S.lit u))
msg-readyR {T} c x u eq =
  cong (λ r → A.pay (S.applyTy (A.Conf.τ c) T) (A.car T (S.var {T} x) r)) eq

echo-stepR : ∀ {g c s Γ T x P b} (h : Hold g s) →
             alpha s ≡ alphabet (codeL g) (codeR g) →
             envPR s ≡ [] → envIR s ≡ [] →
             right s ≡ go Γ (S.put T (S.var {T} x) P) →
             Frag (right s) →
             A.Conf.cap c ≡ cap s →
             QRel (alpha s) (A.Conf.r2l c) (r2l s) →
             VRel (alpha s) (er s) (namesR s) b Γ (A.Conf.rv c) →
             length (A.Conf.r2l c) < A.Conf.cap c →
             Σ ℕ (λ k → Σ W (λ w →
               let s′ = putLitR s (go Γ P) k w in
               s ⟶ₛ s′ × Step g (abs s) rside (abs s′) × Hold g s′
               × atSlot w ≡ slotR s
               × TokOf (alpha s) (A.mkPayR c (S.var {T} x)) (pay k)))
echo-stepR {g} {c} {s} {Γ} {T} {x} {P} h al≡ zP zI rp≡ fr ck qR vr le =
  step (put-closed Γ (S.var {T} x) P frG)
  where
  frG : Frag (go Γ (S.put T (S.var {T} x) P))
  frG = subst Frag rp≡ fr
  body = go Γ P
  step : closedTy T ≡ true →
         Σ ℕ (λ k → Σ W (λ w →
           let s′ = putLitR s body k w in
           s ⟶ₛ s′ × Step g (abs s) rside (abs s′) × Hold g s′
           × atSlot w ≡ slotR s
           × TokOf (alpha s) (A.mkPayR c (S.var {T} x)) (pay k)))
  step cl = use (var-echo Γ x P frG)
    where
    use : lookupTy x Γ ≡ just T × payClosed Γ (S.var {T} x) ≡ pEcho x →
          Σ ℕ (λ k → Σ W (λ w →
            let s′ = putLitR s body k w in
            s ⟶ₛ s′ × Step g (abs s) rside (abs s′) × Hold g s′
            × atSlot w ≡ slotR s
            × TokOf (alpha s) (A.mkPayR c (S.var {T} x)) (pay k)))
    use (lA , peq) = use2 (vrel-hit x vr lA)
      where
      aeq : payIn Γ (S.var {T} x) ≡ pEcho x
      aeq = trans (payIn-closed Γ (S.var {T} x) cl) peq
      proc≡ : right s ≡ sput (pEcho x) body
      proc≡ = trans rp≡ (cong (λ a → sput a body) aeq)
      HitV = Σ (S.Val T) (λ u → Σ ℕ (λ i → Σ ℕ (λ k → Σ Atom (λ atom →
             findS x (namesR s) ≡ just i
             × nth (er s) i ≡ just (suc k)
             × nthA (alpha s) k ≡ just atom
             × valAtom (S.lit u) ≡ just atom
             × A.lookupVEnv x (A.Conf.rv c) ≡ just (A.evar T (S.lit u))))))
      use2 : HitV →
             Σ ℕ (λ k → Σ W (λ w →
               let s′ = putLitR s body k w in
               s ⟶ₛ s′ × Step g (abs s) rside (abs s′) × Hold g s′
               × atSlot w ≡ slotR s
               × TokOf (alpha s) (A.mkPayR c (S.var {T} x)) (pay k)))
      use2 (u , i , k , atom , fd , nt , na , va , lk) =
        k , w , st , gs , h′ , Walked.at wp , tok
        where
        sv = slot-suc (er s) i k nt
        u0 : Unfold [] [] (sput (pEcho x) body) [] [] (f-put (pEcho x) body)
        u0 = u-put
        u1 : Unfold [] [] (right s) [] [] (f-put (pEcho x) body)
        u1 = subst (λ p → Unfold [] [] p [] [] (f-put (pEcho x) body))
               (sym proc≡) u0
        unf : Unfold (envPR s) [] (right s) [] [] (f-put (pEcho x) body)
        unf = subst (λ e → Unfold e [] (right s) [] [] (f-put (pEcho x) body))
                (sym zP) u1
        wp = walk-plain body (suc (ir s)) (slotR s)
               (go-plain Γ P (put-body Γ (S.var {T} x) P frG))
        w = Walked.w wp
        wk = subst (λ e → walk [] e body (suc (ir s)) (slotR s) ≡ just w)
               (sym (cong (λ e → addPend [] (ir s) (slotR s) e) zI))
               (Walked.eq wp)
        rm = src-room le (qrel-len qR) ck
        st = echo-r unf fd sv rm wk
        moved = sim-fwd h st
        gs = proj₁ (proj₂ moved)
        h′ = proj₂ (proj₂ moved)
        prep = prepare-var (A.Conf.rv c) x u lk
        tok0 = echo-tok {σ = A.Conf.τ c} {x = x} cl na va
        tok = subst (λ m → TokOf (alpha s) m (pay k))
                (sym (msg-readyR c x u prep)) tok0

step-put-varR : ∀ {g c s T x P} (e : Embed g c s)
                (eq : A.Conf.rp c ≡ S.put T (S.var {T} x) P) →
                length (A.Conf.r2l c) < A.Conf.cap c →
                let d = putDR c P (S.var {T} x) in
                Σ (A.measure d < A.measure c) (λ lt →
                  Σ SConf (λ s′ →
                    A.sendPutR c (S.var {T} x) P eq ≡ A.does d lt
                    × Embed g d s′
                    × s ⟶ₛ s′
                    × Step g (abs s) rside (abs s′)))
step-put-varR {g} {c} {s} {T} {x} {P} e eq le =
  lt , s′ , does , e′ , st , gs
  where
  Γ = Embed.preR e
  d = putDR c P (S.var {T} x)
  rpE : right s ≡ go Γ (S.put T (S.var {T} x) P)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  frPut : Frag (go Γ (S.put T (S.var {T} x) P))
  frPut = subst Frag rpE (Embed.frR e)
  moved = put-doesR c {v = S.var {T} x} eq le refl
  lt = proj₁ moved
  does = proj₂ moved
  packed = echo-stepR {g = g} {c = c} {s = s} {Γ = Γ} {T = T} {x = x} {P = P}
             (Embed.hold e) (Embed.al≡ e) (Embed.zPR e) (Embed.zIR e)
             rpE (Embed.frR e) (Embed.cap≡ e) (Embed.qR e) (Embed.vR e) le
  k = proj₁ packed
  rest1 = proj₂ packed
  w = proj₁ rest1
  rest2 = proj₂ rest1
  st = proj₁ rest2
  gs = proj₁ (proj₂ rest2)
  h′ = proj₁ (proj₂ (proj₂ rest2))
  atw = proj₁ (proj₂ (proj₂ (proj₂ rest2)))
  tok = proj₂ (proj₂ (proj₂ (proj₂ rest2)))
  s′ = putLitR s (go Γ P) k w
  sameB = cong bnames rpE
  e′ : Embed g d s′
  e′ = record
    { hold = h′
    ; al≡ = Embed.al≡ e
    ; cap≡ = Embed.cap≡ e
    ; qL = Embed.qL e
    ; qR = qrel-snoc (Embed.qR e) tok
    ; preL = Embed.preL e
    ; preR = Γ
    ; lp≡ = Embed.lp≡ e
    ; rp≡ = refl
    ; zPL = Embed.zPL e
    ; zPR = refl
    ; zIL = Embed.zIL e
    ; zIR = Embed.zIR e
    ; frL = Embed.frL e
    ; frR = put-body Γ (S.var {T} x) P frPut
    ; vL = Embed.vL e
    ; vR = Embed.vR e
    ; passedL = Embed.passedL e
    ; sufL = Embed.sufL e
    ; passedR = Embed.passedR e
    ; sufR = Embed.sufR e
    ; layL = Embed.layL e
    ; layR = subst (λ bs → namesR s ≡ Embed.passedR e ++ bs ++ Embed.sufR e)
                sameB (Embed.layR e)
    ; slot≡L = Embed.slot≡L e
    ; slot≡R = trans atw (Embed.slot≡R e)
    ; disL = Embed.disL e
    ; disR = Embed.disR e
    ; lenL = Embed.lenL e
    ; lenR = Embed.lenR e
    }

pickSR : SConf → SProc → Bool → W → SConf
pickSR s p b w = record s
  { right = p ; ir = entry w ; slotR = atSlot w
  ; r2l = snoc (r2l s) (lab b)
  ; envPR = [] ; envIR = addPend [] (ir s) (slotR s) (envIR s) }

labDR : (c : A.Conf) (P : S.Proc) (b : Bool) → A.Conf
labDR c P b =
  A.mk (A.Conf.cap c) (A.Conf.lp c) P
       (A.Conf.l2r c) (A.snoc (A.Conf.r2l c) (A.lab b))
       (A.Conf.lv c) (A.Conf.rv c) (A.Conf.σ c) (A.Conf.τ c)

lab-doesR : ∀ (c : A.Conf) (b : Bool) (P : S.Proc)
            (eq : (A.Conf.rp c ≡ S.pick0 P) ⊎ (A.Conf.rp c ≡ S.pick1 P)) →
            length (A.Conf.r2l c) < A.Conf.cap c →
            Σ (A.measure (labDR c P b) < A.measure c)
              (λ lt → A.sendLabR c b P eq ≡ A.does (labDR c P b) lt)
lab-doesR c b P eq le with length (A.Conf.r2l c) <? A.Conf.cap c
... | no′ ¬le = ⊥-elim (¬le le)
... | yes′ _ = _ , refl

step-pick0R : ∀ {g c s P} (e : Embed g c s)
              (eq : A.Conf.rp c ≡ S.pick0 P) →
              length (A.Conf.r2l c) < A.Conf.cap c →
              let d = labDR c P false in
              Σ (A.measure d < A.measure c) (λ lt →
                Σ SConf (λ s′ →
                  A.sendLabR c false P (inj₁ eq) ≡ A.does d lt
                  × Embed g d s′
                  × s ⟶ₛ s′
                  × Step g (abs s) rside (abs s′)))
step-pick0R {g} {c} {s} {P} e eq le = lt , s′ , does , e′ , st , gs
  where
  Γ = Embed.preR e
  d = labDR c P false
  rpE : right s ≡ go Γ (S.pick0 P)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  fq = pick0-body Γ P (subst Frag rpE (Embed.frR e))
  wp = walk-plain (go Γ P) (suc (ir s)) (slotR s) (go-plain Γ P fq)
  w = Walked.w wp
  unf = castUR s (f-pick0 (go Γ P)) (Embed.zPR e) rpE u-pick0
  wk = walk-envR s (go Γ P) (suc (ir s)) (slotR s) w (Embed.zIR e) (Walked.eq wp)
  rm = src-room le (qrel-len (Embed.qR e)) (Embed.cap≡ e)
  st : s ⟶ₛ pickSR s (go Γ P) false w
  st = pick0-r unf rm wk
  fwd = sim-fwd (Embed.hold e) st
  gs = proj₁ (proj₂ fwd)
  h′ = proj₂ (proj₂ fwd)
  moved = lab-doesR c false P (inj₁ eq) le
  lt = proj₁ moved
  does = proj₂ moved
  s′ = pickSR s (go Γ P) false w
  e′ : Embed g d s′
  e′ = record
    { hold = h′
    ; al≡ = Embed.al≡ e
    ; cap≡ = Embed.cap≡ e
    ; qL = Embed.qL e
    ; qR = qrel-snoc (Embed.qR e) (of-lab false)
    ; preL = Embed.preL e
    ; preR = Γ
    ; lp≡ = Embed.lp≡ e
    ; rp≡ = refl
    ; zPL = Embed.zPL e
    ; zPR = refl
    ; zIL = Embed.zIL e
    ; zIR = Embed.zIR e
    ; frL = Embed.frL e
    ; frR = fq
    ; vL = Embed.vL e
    ; vR = Embed.vR e
    ; passedL = Embed.passedL e
    ; sufL = Embed.sufL e
    ; passedR = Embed.passedR e
    ; sufR = Embed.sufR e
    ; layL = Embed.layL e
    ; layR = subst (λ bs → namesR s ≡ Embed.passedR e ++ bs ++ Embed.sufR e)
                (cong bnames rpE) (Embed.layR e)
    ; slot≡L = Embed.slot≡L e
    ; slot≡R = trans (Walked.at wp) (Embed.slot≡R e)
    ; disL = Embed.disL e
    ; disR = Embed.disR e
    ; lenL = Embed.lenL e
    ; lenR = Embed.lenR e
    }

step-pick1R : ∀ {g c s P} (e : Embed g c s)
              (eq : A.Conf.rp c ≡ S.pick1 P) →
              length (A.Conf.r2l c) < A.Conf.cap c →
              let d = labDR c P true in
              Σ (A.measure d < A.measure c) (λ lt →
                Σ SConf (λ s′ →
                  A.sendLabR c true P (inj₂ eq) ≡ A.does d lt
                  × Embed g d s′
                  × s ⟶ₛ s′
                  × Step g (abs s) rside (abs s′)))
step-pick1R {g} {c} {s} {P} e eq le = lt , s′ , does , e′ , st , gs
  where
  Γ = Embed.preR e
  d = labDR c P true
  rpE : right s ≡ go Γ (S.pick1 P)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  fq = pick1-body Γ P (subst Frag rpE (Embed.frR e))
  wp = walk-plain (go Γ P) (suc (ir s)) (slotR s) (go-plain Γ P fq)
  w = Walked.w wp
  unf = castUR s (f-pick1 (go Γ P)) (Embed.zPR e) rpE u-pick1
  wk = walk-envR s (go Γ P) (suc (ir s)) (slotR s) w (Embed.zIR e) (Walked.eq wp)
  rm = src-room le (qrel-len (Embed.qR e)) (Embed.cap≡ e)
  st : s ⟶ₛ pickSR s (go Γ P) true w
  st = pick1-r unf rm wk
  fwd = sim-fwd (Embed.hold e) st
  gs = proj₁ (proj₂ fwd)
  h′ = proj₂ (proj₂ fwd)
  moved = lab-doesR c true P (inj₂ eq) le
  lt = proj₁ moved
  does = proj₂ moved
  s′ = pickSR s (go Γ P) true w
  e′ : Embed g d s′
  e′ = record
    { hold = h′
    ; al≡ = Embed.al≡ e
    ; cap≡ = Embed.cap≡ e
    ; qL = Embed.qL e
    ; qR = qrel-snoc (Embed.qR e) (of-lab true)
    ; preL = Embed.preL e
    ; preR = Γ
    ; lp≡ = Embed.lp≡ e
    ; rp≡ = refl
    ; zPL = Embed.zPL e
    ; zPR = refl
    ; zIL = Embed.zIL e
    ; zIR = Embed.zIR e
    ; frL = Embed.frL e
    ; frR = fq
    ; vL = Embed.vL e
    ; vR = Embed.vR e
    ; passedL = Embed.passedL e
    ; sufL = Embed.sufL e
    ; passedR = Embed.passedR e
    ; sufR = Embed.sufR e
    ; layL = Embed.layL e
    ; layR = subst (λ bs → namesR s ≡ Embed.passedR e ++ bs ++ Embed.sufR e)
                (cong bnames rpE) (Embed.layR e)
    ; slot≡L = Embed.slot≡L e
    ; slot≡R = trans (Walked.at wp) (Embed.slot≡R e)
    ; disL = Embed.disL e
    ; disR = Embed.disR e
    ; lenL = Embed.lenL e
    ; lenR = Embed.lenR e
    }

getDR : (c : A.Conf) (P : S.Proc) (x : String) (ca : A.Carrier)
        (rest : List A.Msg) → A.Conf
getDR c P x ca rest =
  A.mk (A.Conf.cap c) (A.Conf.lp c) P rest (A.Conf.r2l c)
       (A.Conf.lv c) (A.bindV x ca (A.Conf.rv c))
       (A.Conf.σ c) (A.extCar x ca (A.Conf.τ c))

recv-doesR : ∀ (c : A.Conf) (T : S.Ty) x P (eq : A.Conf.rp c ≡ S.get T x P)
             m rest ca →
             A.Conf.l2r c ≡ m ∷ rest →
             A.takePay (A.Conf.τ c) T m ≡ A.tpay ca →
             Σ (A.measure (getDR c P x ca rest) < A.measure c)
               (λ lt → A.recvGetR c T x P eq ≡ A.does (getDR c P x ca rest) lt)
recv-doesR c T x P eq m rest ca qe te rewrite qe | te = _ , refl

getSR : SConf → SProc → List Tok → ℕ → W → SConf
getSR s p rest k w = record s
  { right = p ; ir = entry w ; slotR = atSlot w
  ; l2r = rest ; er = setNth (slotR s) (suc k) (er s)
  ; envPR = [] ; envIR = addPend [] (ir s) (slotR s) (envIR s) }

-- A right get reads the queue the left has filled.
step-get-payR : ∀ {g c s T x P m rest ca} (e : Embed g c s)
                (eq : A.Conf.rp c ≡ S.get T x P) →
                A.Conf.l2r c ≡ m ∷ rest →
                A.takePay (A.Conf.τ c) T m ≡ A.tpay ca →
                let d = getDR c P x ca rest in
                Σ (A.measure d < A.measure c) (λ lt →
                  Σ SConf (λ s′ →
                    A.recvGetR c T x P eq ≡ A.does d lt
                    × Embed g d s′
                    × s ⟶ₛ s′
                    × Step g (abs s) rside (abs s′)))
step-get-payR {g} {c} {s} {T} {x} {P} {m} {rest} {ca} e eq qe te =
  proj₁ moved , from (qrel-head qHere)
  where
  Γ = Embed.preR e
  passed = Embed.passedR e
  suf = Embed.sufR e
  rpE : right s ≡ go Γ (S.get T x P)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  frG : Frag (go Γ (S.get T x P))
  frG = subst Frag rpE (Embed.frR e)
  view = get-view Γ T x P frG
  t = proj₁ view
  geq = proj₁ (proj₂ view)
  fq = proj₁ (proj₂ (proj₂ view))
  clT = proj₁ (proj₂ (proj₂ (proj₂ view)))
  gt = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ view))))
  body = go ((x , T) ∷ Γ) P
  proc≡ : right s ≡ sget t x body
  proc≡ = trans rpE geq
  d = getDR c P x ca rest
  moved = recv-doesR c T x P eq m rest ca qe te
  qHere : QRel (alpha s) (m ∷ rest) (l2r s)
  qHere = subst (λ ms → QRel (alpha s) ms (l2r s)) qe (Embed.qL e)
  Result = Σ SConf (λ s′ →
             A.recvGetR c T x P eq ≡ A.does d (proj₁ moved)
             × Embed g d s′
             × s ⟶ₛ s′
             × Step g (abs s) rside (abs s′))
  from : Σ Tok (λ tok → Σ (List Tok) (λ us →
           l2r s ≡ tok ∷ us × TokOf (alpha s) m tok × QRel (alpha s) rest us)) →
         Result
  from (_ , _ , _ , of-lab b , _) = ⊥-elim (lab-not (A.Conf.τ c) T b ca te)
  from (.(pay k) , us , qeq , of-pay {W} {B} {v} {r} {k} {a} wEq clB na va , qTail) =
    cast (trans (sym (applyTy-id (A.Conf.τ c) T clT))
                (trans (take-eq (A.Conf.τ c) T W (A.car B v r) ca te) wEq))
    where
    cast : T ≡ B → Result
    cast refl =
      s′ , proj₂ moved , e′ , st , gs
      where
      u = proj₁ (val-lit r a va)
      r≡ = proj₂ (val-lit r a va)
      vaU : valAtom (S.lit u) ≡ just a
      vaU = subst (λ e → valAtom e ≡ just a) r≡ va
      fit = fits-val t a u gt vaU
      ca≡ : A.car T v (S.lit u) ≡ ca
      ca≡ = trans (sym (cong (A.car T v) r≡))
                  (take-car (A.Conf.τ c) T W (A.car T v r) ca te)
      ve≡ : A.bindV x ca (A.Conf.rv c) ≡ (x , A.evar T (S.lit u)) ∷ A.Conf.rv c
      ve≡ = cong (λ z → A.bindV x z (A.Conf.rv c)) (sym ca≡)
      suf′ = bnames body ++ suf
      names≡ : namesR s ≡ passed ++ (x ∷ suf′)
      names≡ = trans (Embed.layR e) (cong (λ bs → passed ++ bs ++ suf) (cong bnames proc≡))
      disAt : distinctN (passed ++ (x ∷ suf′)) ≡ true
      disAt = subst (λ ns → distinctN ns ≡ true) names≡ (Embed.disR e)
      fr = trans (sym (fresh≡ x passed)) (dist-fresh passed x suf′ disAt)
      fd : findS x (namesR s) ≡ just (length passed)
      fd = trans (cong (findS x) names≡) (findS-at x passed suf′ fr)
      slot< : length passed < length (er s)
      slot< = subst (λ n → length passed < n)
                (sym (trans (Embed.lenR e) (cong length names≡)))
                (slot-lt passed x suf′)
      b = length passed
      nt = nth-set b (suc k) (er s) slot<
      kept = vrel-widen (vrel-write b (er s) (suc k) (Embed.vR e))
      built = vr1 x fd ≤-refl nt na vaU kept
      slots≡ : setNth (slotR s) (suc k) (er s) ≡ setNth b (suc k) (er s)
      slots≡ = cong (λ i → setNth i (suc k) (er s)) (Embed.slot≡R e)
      vHere = subst (λ xs → VRel (alpha s) xs (namesR s) (suc b)
                              ((x , T) ∷ Γ)
                              (A.bindV x ca (A.Conf.rv c)))
               (sym slots≡)
               (subst (λ ve → VRel (alpha s) (setNth b (suc k) (er s)) (namesR s)
                                  (suc b) ((x , T) ∷ Γ) ve)
                  (sym ve≡) built)
      vDone = subst (λ n → VRel (alpha s) (setNth (slotR s) (suc k) (er s))
                                 (namesR s) n ((x , T) ∷ Γ)
                                 (A.bindV x ca (A.Conf.rv c)))
                (sym (len-snoc passed x)) vHere
      u0 : Unfold [] [] (sget t x body) [] [] (f-get t x body)
      u0 = u-get
      u1 = subst (λ p → Unfold [] [] p [] [] (f-get t x body)) (sym proc≡) u0
      unf = subst (λ e → Unfold e [] (right s) [] [] (f-get t x body))
              (sym (Embed.zPR e)) u1
      wp = walk-plain body (suc (ir s)) (suc (slotR s))
             (go-plain ((x , T) ∷ Γ) P fq)
      w = Walked.w wp
      wk = subst (λ e → walk [] e body (suc (ir s)) (suc (slotR s)) ≡ just w)
             (sym (cong (λ e → addPend [] (ir s) (slotR s) e) (Embed.zIR e)))
             (Walked.eq wp)
      st = get-r unf qeq na fit wk
      stepped = sim-fwd (Embed.hold e) st
      gs = proj₁ (proj₂ stepped)
      h′ = proj₂ (proj₂ stepped)
      s′ = getSR s body us k w
      e′ : Embed g d s′
      e′ = record
        { hold = h′
        ; al≡ = Embed.al≡ e
        ; cap≡ = Embed.cap≡ e
        ; qL = qTail
        ; qR = Embed.qR e
        ; preL = Embed.preL e
        ; preR = (x , T) ∷ Γ
        ; lp≡ = Embed.lp≡ e
        ; rp≡ = refl
        ; zPL = Embed.zPL e
        ; zPR = refl
        ; zIL = Embed.zIL e
        ; zIR = cong (addPend [] (ir s) (slotR s)) (Embed.zIR e)
        ; frL = Embed.frL e
        ; frR = fq
        ; vL = Embed.vL e
        ; vR = vDone
        ; passedL = Embed.passedL e
        ; sufL = Embed.sufL e
        ; passedR = passed ++ (x ∷ [])
        ; sufR = suf
        ; layL = Embed.layL e
        ; layR = trans names≡ (cons-++ passed x suf′)
        ; slot≡L = Embed.slot≡L e
        ; slot≡R = trans (trans (Walked.at wp) (cong suc (Embed.slot≡R e)))
                         (sym (len-snoc passed x))
        ; disL = Embed.disL e
        ; disR = Embed.disR e
        ; lenL = Embed.lenL e
        ; lenR = trans (length-set (slotR s) (suc k) (er s)) (Embed.lenR e)
        }

cover-body : ∀ Γ P Q → Frag (go Γ (S.cover P Q)) →
             Frag (go Γ P) × Frag (go Γ Q)
cover-body Γ P Q (fcover fp fq) = fp , fq

which0 : ∀ b → A.takeLab (A.lab b) ≡ A.l0 → b ≡ false
which0 false refl = refl
which0 true ()

which1 : ∀ b → A.takeLab (A.lab b) ≡ A.l1 → b ≡ true
which1 true refl = refl
which1 false ()

pay-lab0 : ∀ W (ca : A.Carrier) → A.takeLab (A.pay W ca) ≡ A.l0 → ⊥
pay-lab0 _ _ ()

pay-lab1 : ∀ W (ca : A.Carrier) → A.takeLab (A.pay W ca) ≡ A.l1 → ⊥
pay-lab1 _ _ ()

covD : (c : A.Conf) (P : S.Proc) (rest : List A.Msg) → A.Conf
covD c P rest =
  A.mk (A.Conf.cap c) P (A.Conf.rp c) (A.Conf.l2r c) rest
       (A.Conf.lv c) (A.Conf.rv c) (A.Conf.σ c) (A.Conf.τ c)

cov-does0 : ∀ (c : A.Conf) P Q (eq : A.Conf.lp c ≡ S.cover P Q)
            m rest → A.Conf.r2l c ≡ m ∷ rest → A.takeLab m ≡ A.l0 →
            Σ (A.measure (covD c P rest) < A.measure c)
              (λ lt → A.recvCoverL c P Q eq ≡ A.does (covD c P rest) lt)
cov-does0 c P Q eq m rest qe tl rewrite qe | tl = _ , refl

cov-does1 : ∀ (c : A.Conf) P Q (eq : A.Conf.lp c ≡ S.cover P Q)
            m rest → A.Conf.r2l c ≡ m ∷ rest → A.takeLab m ≡ A.l1 →
            Σ (A.measure (covD c Q rest) < A.measure c)
              (λ lt → A.recvCoverL c P Q eq ≡ A.does (covD c Q rest) lt)
cov-does1 c P Q eq m rest qe tl rewrite qe | tl = _ , refl

covS0 : SConf → SProc → List Tok → W → SConf
covS0 s p rest w = record s
  { left = p ; il = entry w ; slotL = atSlot w ; r2l = rest
  ; envPL = [] ; envIL = addPend [] (il s) (slotL s) (envIL s) }

covS1 : SConf → SProc → List Tok → W → SConf
covS1 s q rest w = record s
  { left = q ; il = entry w ; slotL = atSlot w ; r2l = rest
  ; envPL = [] ; envIL = addPend [] (il s) (slotL s) (envIL s) }

-- The false label takes the first branch. Its binders stay where they
-- were, and the other branch's binders move into the suffix.
step-cover0 : ∀ {g c s P Q m rest} (e : Embed g c s)
              (eq : A.Conf.lp c ≡ S.cover P Q) →
              A.Conf.r2l c ≡ m ∷ rest →
              A.takeLab m ≡ A.l0 →
              let d = covD c P rest in
              Σ (A.measure d < A.measure c) (λ lt →
                Σ SConf (λ s′ →
                  A.recvCoverL c P Q eq ≡ A.does d lt
                  × Embed g d s′
                  × s ⟶ₛ s′
                  × Step g (abs s) lside (abs s′)))
step-cover0 {g} {c} {s} {P} {Q} {m} {rest} e eq qe tl =
  proj₁ moved , from (qrel-head qHere)
  where
  Γ = Embed.preL e
  passed = Embed.passedL e
  suf = Embed.sufL e
  lpE : left s ≡ go Γ (S.cover P Q)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  both = cover-body Γ P Q (subst Frag lpE (Embed.frL e))
  fp = proj₁ both
  fq = proj₂ both
  p = go Γ P
  q = go Γ Q
  d = covD c P rest
  moved = cov-does0 c P Q eq m rest qe tl
  qHere : QRel (alpha s) (m ∷ rest) (r2l s)
  qHere = subst (λ ms → QRel (alpha s) ms (r2l s)) qe (Embed.qR e)
  Result = Σ SConf (λ s′ →
             A.recvCoverL c P Q eq ≡ A.does d (proj₁ moved)
             × Embed g d s′ × s ⟶ₛ s′ × Step g (abs s) lside (abs s′))
  from : Σ Tok (λ tok → Σ (List Tok) (λ us →
           r2l s ≡ tok ∷ us × TokOf (alpha s) m tok × QRel (alpha s) rest us)) →
         Result
  from (.(pay _) , _ , _ , of-pay {W} {B} {v} {r} _ _ _ _ , _) =
    ⊥-elim (pay-lab0 W (A.car B v r) tl)
  from (.(lab b) , us , qeq , of-lab b , qTail) = use (which0 b tl)
    where
    use : b ≡ false → Result
    use refl =
      s′ , proj₂ moved , e′ , st , gs
      where
      wp = walk-plain p (suc (il s)) (slotL s) (go-plain Γ P fp)
      w = Walked.w wp
      unf = castU s (f-cover p q) (Embed.zPL e) lpE u-cover
      wk = walk-env s p (suc (il s)) (slotL s) w (Embed.zIL e) (Walked.eq wp)
      st = cover0-l unf qeq wk
      stepped = sim-fwd (Embed.hold e) st
      gs = proj₁ (proj₂ stepped)
      h′ = proj₂ (proj₂ stepped)
      s′ = covS0 s p us w
      bp = bnames p
      bq = bnames q
      names≡ : namesL s ≡ passed ++ (bp ++ bq) ++ suf
      names≡ = trans (Embed.layL e)
                 (cong (λ bs → passed ++ bs ++ suf) (cong bnames lpE))
      e′ : Embed g d s′
      e′ = record
        { hold = h′
        ; al≡ = Embed.al≡ e
        ; cap≡ = Embed.cap≡ e
        ; qL = Embed.qL e
        ; qR = qTail
        ; preL = Γ
        ; preR = Embed.preR e
        ; lp≡ = refl
        ; rp≡ = Embed.rp≡ e
        ; zPL = refl
        ; zPR = Embed.zPR e
        ; zIL = cong (addPend [] (il s) (slotL s)) (Embed.zIL e)
        ; zIR = Embed.zIR e
        ; frL = fp
        ; frR = Embed.frR e
        ; vL = Embed.vL e
        ; vR = Embed.vR e
        ; passedL = passed
        ; sufL = bq ++ suf
        ; passedR = Embed.passedR e
        ; sufR = Embed.sufR e
        ; layL = trans names≡ (cong (passed ++_) (++-assoc bp bq suf))
        ; layR = Embed.layR e
        ; slot≡L = trans (Walked.at wp) (Embed.slot≡L e)
        ; slot≡R = Embed.slot≡R e
        ; disL = Embed.disL e
        ; disR = Embed.disR e
        ; lenL = Embed.lenL e
        ; lenR = Embed.lenR e
        }

-- The true label skips the first branch. Those binders join `passed`,
-- so the slot of the second branch is where `findS` will look.
step-cover1 : ∀ {g c s P Q m rest} (e : Embed g c s)
              (eq : A.Conf.lp c ≡ S.cover P Q) →
              A.Conf.r2l c ≡ m ∷ rest →
              A.takeLab m ≡ A.l1 →
              let d = covD c Q rest in
              Σ (A.measure d < A.measure c) (λ lt →
                Σ SConf (λ s′ →
                  A.recvCoverL c P Q eq ≡ A.does d lt
                  × Embed g d s′
                  × s ⟶ₛ s′
                  × Step g (abs s) lside (abs s′)))
step-cover1 {g} {c} {s} {P} {Q} {m} {rest} e eq qe tl =
  proj₁ moved , from (qrel-head qHere)
  where
  Γ = Embed.preL e
  passed = Embed.passedL e
  suf = Embed.sufL e
  lpE : left s ≡ go Γ (S.cover P Q)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  both = cover-body Γ P Q (subst Frag lpE (Embed.frL e))
  fp = proj₁ both
  fq = proj₂ both
  p = go Γ P
  q = go Γ Q
  d = covD c Q rest
  moved = cov-does1 c P Q eq m rest qe tl
  qHere : QRel (alpha s) (m ∷ rest) (r2l s)
  qHere = subst (λ ms → QRel (alpha s) ms (r2l s)) qe (Embed.qR e)
  Result = Σ SConf (λ s′ →
             A.recvCoverL c P Q eq ≡ A.does d (proj₁ moved)
             × Embed g d s′ × s ⟶ₛ s′ × Step g (abs s) lside (abs s′))
  from : Σ Tok (λ tok → Σ (List Tok) (λ us →
           r2l s ≡ tok ∷ us × TokOf (alpha s) m tok × QRel (alpha s) rest us)) →
         Result
  from (.(pay _) , _ , _ , of-pay {W} {B} {v} {r} _ _ _ _ , _) =
    ⊥-elim (pay-lab1 W (A.car B v r) tl)
  from (.(lab b) , us , qeq , of-lab b , qTail) = use (which1 b tl)
    where
    use : b ≡ true → Result
    use refl =
      s′ , proj₂ moved , e′ , st , gs
      where
      wp = walk-plain p (suc (il s)) (slotL s) (go-plain Γ P fp)
      w1 = Walked.w wp
      wq = walk-plain q (next w1) (slotN w1) (go-plain Γ Q fq)
      w2 = Walked.w wq
      unf = castU s (f-cover p q) (Embed.zPL e) lpE u-cover
      wk1 = walk-env s p (suc (il s)) (slotL s) w1 (Embed.zIL e) (Walked.eq wp)
      wk2 = walk-env s q (next w1) (slotN w1) w2 (Embed.zIL e) (Walked.eq wq)
      st = cover1-l unf qeq wk1 wk2
      stepped = sim-fwd (Embed.hold e) st
      gs = proj₁ (proj₂ stepped)
      h′ = proj₂ (proj₂ stepped)
      s′ = covS1 s q us w2
      bp = bnames p
      bq = bnames q
      names≡ : namesL s ≡ passed ++ (bp ++ bq) ++ suf
      names≡ = trans (Embed.layL e)
                 (cong (λ bs → passed ++ bs ++ suf) (cong bnames lpE))
      shifted = trans names≡ (cong (passed ++_) (++-assoc bp bq suf))
      vShift = subst (λ n → VRel (alpha s) (el s) (namesL s) n Γ (A.Conf.lv c))
                 (sym (length-++ passed {bp}))
                 (vrel-plus (length bp) (Embed.vL e))
      e′ : Embed g d s′
      e′ = record
        { hold = h′
        ; al≡ = Embed.al≡ e
        ; cap≡ = Embed.cap≡ e
        ; qL = Embed.qL e
        ; qR = qTail
        ; preL = Γ
        ; preR = Embed.preR e
        ; lp≡ = refl
        ; rp≡ = Embed.rp≡ e
        ; zPL = refl
        ; zPR = Embed.zPR e
        ; zIL = cong (addPend [] (il s) (slotL s)) (Embed.zIL e)
        ; zIR = Embed.zIR e
        ; frL = fq
        ; frR = Embed.frR e
        ; vL = vShift
        ; vR = Embed.vR e
        ; passedL = passed ++ bp
        ; sufL = suf
        ; passedR = Embed.passedR e
        ; sufR = Embed.sufR e
        ; layL = trans shifted (sym (++-assoc passed bp (bq ++ suf)))
        ; layR = Embed.layR e
        ; slot≡L = trans (trans (Walked.at wq) (Walked.sn wp))
                     (trans (cong (_+ length bp) (Embed.slot≡L e))
                            (sym (length-++ passed {bp})))
        ; slot≡R = Embed.slot≡R e
        ; disL = Embed.disL e
        ; disR = Embed.disR e
        ; lenL = Embed.lenL e
        ; lenR = Embed.lenR e
        }

covDR : (c : A.Conf) (P : S.Proc) (rest : List A.Msg) → A.Conf
covDR c P rest =
  A.mk (A.Conf.cap c) (A.Conf.lp c) P rest (A.Conf.r2l c)
       (A.Conf.lv c) (A.Conf.rv c) (A.Conf.σ c) (A.Conf.τ c)

cov-does0R : ∀ (c : A.Conf) P Q (eq : A.Conf.rp c ≡ S.cover P Q)
             m rest → A.Conf.l2r c ≡ m ∷ rest → A.takeLab m ≡ A.l0 →
             Σ (A.measure (covDR c P rest) < A.measure c)
               (λ lt → A.recvCoverR c P Q eq ≡ A.does (covDR c P rest) lt)
cov-does0R c P Q eq m rest qe tl rewrite qe | tl = _ , refl

cov-does1R : ∀ (c : A.Conf) P Q (eq : A.Conf.rp c ≡ S.cover P Q)
             m rest → A.Conf.l2r c ≡ m ∷ rest → A.takeLab m ≡ A.l1 →
             Σ (A.measure (covDR c Q rest) < A.measure c)
               (λ lt → A.recvCoverR c P Q eq ≡ A.does (covDR c Q rest) lt)
cov-does1R c P Q eq m rest qe tl rewrite qe | tl = _ , refl

covSR0 : SConf → SProc → List Tok → W → SConf
covSR0 s p rest w = record s
  { right = p ; ir = entry w ; slotR = atSlot w ; l2r = rest
  ; envPR = [] ; envIR = addPend [] (ir s) (slotR s) (envIR s) }

covSR1 : SConf → SProc → List Tok → W → SConf
covSR1 s q rest w = record s
  { right = q ; ir = entry w ; slotR = atSlot w ; l2r = rest
  ; envPR = [] ; envIR = addPend [] (ir s) (slotR s) (envIR s) }

step-cover0R : ∀ {g c s P Q m rest} (e : Embed g c s)
               (eq : A.Conf.rp c ≡ S.cover P Q) →
               A.Conf.l2r c ≡ m ∷ rest →
               A.takeLab m ≡ A.l0 →
               let d = covDR c P rest in
               Σ (A.measure d < A.measure c) (λ lt →
                 Σ SConf (λ s′ →
                   A.recvCoverR c P Q eq ≡ A.does d lt
                   × Embed g d s′
                   × s ⟶ₛ s′
                   × Step g (abs s) rside (abs s′)))
step-cover0R {g} {c} {s} {P} {Q} {m} {rest} e eq qe tl =
  proj₁ moved , from (qrel-head qHere)
  where
  Γ = Embed.preR e
  passed = Embed.passedR e
  suf = Embed.sufR e
  rpE : right s ≡ go Γ (S.cover P Q)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  both = cover-body Γ P Q (subst Frag rpE (Embed.frR e))
  fp = proj₁ both
  fq = proj₂ both
  p = go Γ P
  q = go Γ Q
  d = covDR c P rest
  moved = cov-does0R c P Q eq m rest qe tl
  qHere : QRel (alpha s) (m ∷ rest) (l2r s)
  qHere = subst (λ ms → QRel (alpha s) ms (l2r s)) qe (Embed.qL e)
  Result = Σ SConf (λ s′ →
             A.recvCoverR c P Q eq ≡ A.does d (proj₁ moved)
             × Embed g d s′ × s ⟶ₛ s′ × Step g (abs s) rside (abs s′))
  from : Σ Tok (λ tok → Σ (List Tok) (λ us →
           l2r s ≡ tok ∷ us × TokOf (alpha s) m tok × QRel (alpha s) rest us)) →
         Result
  from (.(pay _) , _ , _ , of-pay {W} {B} {v} {r} _ _ _ _ , _) =
    ⊥-elim (pay-lab0 W (A.car B v r) tl)
  from (.(lab b) , us , qeq , of-lab b , qTail) = use (which0 b tl)
    where
    use : b ≡ false → Result
    use refl =
      s′ , proj₂ moved , e′ , st , gs
      where
      wp = walk-plain p (suc (ir s)) (slotR s) (go-plain Γ P fp)
      w = Walked.w wp
      unf = castUR s (f-cover p q) (Embed.zPR e) rpE u-cover
      wk = walk-envR s p (suc (ir s)) (slotR s) w (Embed.zIR e) (Walked.eq wp)
      st = cover0-r unf qeq wk
      stepped = sim-fwd (Embed.hold e) st
      gs = proj₁ (proj₂ stepped)
      h′ = proj₂ (proj₂ stepped)
      s′ = covSR0 s p us w
      bp = bnames p
      bq = bnames q
      names≡ : namesR s ≡ passed ++ (bp ++ bq) ++ suf
      names≡ = trans (Embed.layR e)
                 (cong (λ bs → passed ++ bs ++ suf) (cong bnames rpE))
      e′ : Embed g d s′
      e′ = record
        { hold = h′
        ; al≡ = Embed.al≡ e
        ; cap≡ = Embed.cap≡ e
        ; qL = qTail
        ; qR = Embed.qR e
        ; preL = Embed.preL e
        ; preR = Γ
        ; lp≡ = Embed.lp≡ e
        ; rp≡ = refl
        ; zPL = Embed.zPL e
        ; zPR = refl
        ; zIL = Embed.zIL e
        ; zIR = cong (addPend [] (ir s) (slotR s)) (Embed.zIR e)
        ; frL = Embed.frL e
        ; frR = fp
        ; vL = Embed.vL e
        ; vR = Embed.vR e
        ; passedL = Embed.passedL e
        ; sufL = Embed.sufL e
        ; passedR = passed
        ; sufR = bq ++ suf
        ; layL = Embed.layL e
        ; layR = trans names≡ (cong (passed ++_) (++-assoc bp bq suf))
        ; slot≡L = Embed.slot≡L e
        ; slot≡R = trans (Walked.at wp) (Embed.slot≡R e)
        ; disL = Embed.disL e
        ; disR = Embed.disR e
        ; lenL = Embed.lenL e
        ; lenR = Embed.lenR e
        }

step-cover1R : ∀ {g c s P Q m rest} (e : Embed g c s)
               (eq : A.Conf.rp c ≡ S.cover P Q) →
               A.Conf.l2r c ≡ m ∷ rest →
               A.takeLab m ≡ A.l1 →
               let d = covDR c Q rest in
               Σ (A.measure d < A.measure c) (λ lt →
                 Σ SConf (λ s′ →
                   A.recvCoverR c P Q eq ≡ A.does d lt
                   × Embed g d s′
                   × s ⟶ₛ s′
                   × Step g (abs s) rside (abs s′)))
step-cover1R {g} {c} {s} {P} {Q} {m} {rest} e eq qe tl =
  proj₁ moved , from (qrel-head qHere)
  where
  Γ = Embed.preR e
  passed = Embed.passedR e
  suf = Embed.sufR e
  rpE : right s ≡ go Γ (S.cover P Q)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  both = cover-body Γ P Q (subst Frag rpE (Embed.frR e))
  fp = proj₁ both
  fq = proj₂ both
  p = go Γ P
  q = go Γ Q
  d = covDR c Q rest
  moved = cov-does1R c P Q eq m rest qe tl
  qHere : QRel (alpha s) (m ∷ rest) (l2r s)
  qHere = subst (λ ms → QRel (alpha s) ms (l2r s)) qe (Embed.qL e)
  Result = Σ SConf (λ s′ →
             A.recvCoverR c P Q eq ≡ A.does d (proj₁ moved)
             × Embed g d s′ × s ⟶ₛ s′ × Step g (abs s) rside (abs s′))
  from : Σ Tok (λ tok → Σ (List Tok) (λ us →
           l2r s ≡ tok ∷ us × TokOf (alpha s) m tok × QRel (alpha s) rest us)) →
         Result
  from (.(pay _) , _ , _ , of-pay {W} {B} {v} {r} _ _ _ _ , _) =
    ⊥-elim (pay-lab1 W (A.car B v r) tl)
  from (.(lab b) , us , qeq , of-lab b , qTail) = use (which1 b tl)
    where
    use : b ≡ true → Result
    use refl =
      s′ , proj₂ moved , e′ , st , gs
      where
      wp = walk-plain p (suc (ir s)) (slotR s) (go-plain Γ P fp)
      w1 = Walked.w wp
      wq = walk-plain q (next w1) (slotN w1) (go-plain Γ Q fq)
      w2 = Walked.w wq
      unf = castUR s (f-cover p q) (Embed.zPR e) rpE u-cover
      wk1 = walk-envR s p (suc (ir s)) (slotR s) w1 (Embed.zIR e) (Walked.eq wp)
      wk2 = walk-envR s q (next w1) (slotN w1) w2 (Embed.zIR e) (Walked.eq wq)
      st = cover1-r unf qeq wk1 wk2
      stepped = sim-fwd (Embed.hold e) st
      gs = proj₁ (proj₂ stepped)
      h′ = proj₂ (proj₂ stepped)
      s′ = covSR1 s q us w2
      bp = bnames p
      bq = bnames q
      names≡ : namesR s ≡ passed ++ (bp ++ bq) ++ suf
      names≡ = trans (Embed.layR e)
                 (cong (λ bs → passed ++ bs ++ suf) (cong bnames rpE))
      shifted = trans names≡ (cong (passed ++_) (++-assoc bp bq suf))
      vShift = subst (λ n → VRel (alpha s) (er s) (namesR s) n Γ (A.Conf.rv c))
                 (sym (length-++ passed {bp}))
                 (vrel-plus (length bp) (Embed.vR e))
      e′ : Embed g d s′
      e′ = record
        { hold = h′
        ; al≡ = Embed.al≡ e
        ; cap≡ = Embed.cap≡ e
        ; qL = qTail
        ; qR = Embed.qR e
        ; preL = Embed.preL e
        ; preR = Γ
        ; lp≡ = Embed.lp≡ e
        ; rp≡ = refl
        ; zPL = Embed.zPL e
        ; zPR = refl
        ; zIL = Embed.zIL e
        ; zIR = cong (addPend [] (ir s) (slotR s)) (Embed.zIR e)
        ; frL = Embed.frL e
        ; frR = fq
        ; vL = Embed.vL e
        ; vR = vShift
        ; passedL = Embed.passedL e
        ; sufL = Embed.sufL e
        ; passedR = passed ++ bp
        ; sufR = suf
        ; layL = Embed.layL e
        ; layR = trans shifted (sym (++-assoc passed bp (bq ++ suf)))
        ; slot≡L = Embed.slot≡L e
        ; slot≡R = trans (trans (Walked.at wq) (Walked.sn wp))
                     (trans (cong (_+ length bp) (Embed.slot≡R e))
                            (sym (length-++ passed {bp})))
        ; disL = Embed.disL e
        ; disR = Embed.disR e
        ; lenL = Embed.lenL e
        ; lenR = Embed.lenR e
        }

-- `go` of an `iget` is the two branches under the fresh bit binder.
iget-view : ∀ Γ x P Q → Frag (go Γ (S.iget x P Q)) →
            go Γ (S.iget x P Q) ≡
              siget x (go ((x , S.bit) ∷ Γ) P) (go ((x , S.bit) ∷ Γ) Q)
            × Frag (go ((x , S.bit) ∷ Γ) P)
            × Frag (go ((x , S.bit) ∷ Γ) Q)
            × newName x Γ ≡ true
iget-view Γ x P Q fp with newName x Γ
iget-view Γ x P Q () | false
iget-view Γ x P Q (figet fp fq) | true = refl , fp , fq , refl

lab-bit0 : ∀ b (ca : A.Carrier) → A.takeBit (A.lab b) ≡ A.bb0 ca → ⊥
lab-bit0 _ _ ()

lab-bit1 : ∀ b (ca : A.Carrier) → A.takeBit (A.lab b) ≡ A.bb1 ca → ⊥
lab-bit1 _ _ ()

-- `takeBit` returns the carrier it was given, and only for a bit.
take-bit0 : ∀ W (ca0 ca : A.Carrier) →
            A.takeBit (A.pay W ca0) ≡ A.bb0 ca →
            W ≡ S.bit × ca0 ≡ ca × A.asBit ca0 ≡ just S.b0
take-bit0 W ca0 ca eq with S.ty≟ W S.bit
take-bit0 W ca0 ca () | no′ _
take-bit0 .S.bit ca0 ca eq | yes′ refl with A.asBit ca0
take-bit0 .S.bit ca0 ca () | yes′ refl | nothing
take-bit0 .S.bit ca0 ca () | yes′ refl | just S.b1
take-bit0 .S.bit ca0 .ca0 refl | yes′ refl | just S.b0 = refl , refl , refl

take-bit1 : ∀ W (ca0 ca : A.Carrier) →
            A.takeBit (A.pay W ca0) ≡ A.bb1 ca →
            W ≡ S.bit × ca0 ≡ ca × A.asBit ca0 ≡ just S.b1
take-bit1 W ca0 ca eq with S.ty≟ W S.bit
take-bit1 W ca0 ca () | no′ _
take-bit1 .S.bit ca0 ca eq | yes′ refl with A.asBit ca0
take-bit1 .S.bit ca0 ca () | yes′ refl | nothing
take-bit1 .S.bit ca0 ca () | yes′ refl | just S.b0
take-bit1 .S.bit ca0 .ca0 refl | yes′ refl | just S.b1 = refl , refl , refl

-- A token whose ready value is a literal bit is that bit.
ready-b0 : ∀ (v r : S.ValExpr S.bit) a →
           valAtom r ≡ just a →
           A.asBit (A.car S.bit v r) ≡ just S.b0 →
           r ≡ S.lit S.b0 × a ≡ aBit false
ready-b0 _ (S.lit S.b0) .(aBit false) refl refl = refl , refl
ready-b0 _ (S.lit S.b1) _ _ ()
ready-b0 _ (S.var _) _ () _
ready-b0 _ (S.call _ _) _ () _

ready-b1 : ∀ (v r : S.ValExpr S.bit) a →
           valAtom r ≡ just a →
           A.asBit (A.car S.bit v r) ≡ just S.b1 →
           r ≡ S.lit S.b1 × a ≡ aBit true
ready-b1 _ (S.lit S.b1) .(aBit true) refl refl = refl , refl
ready-b1 _ (S.lit S.b0) _ _ ()
ready-b1 _ (S.var _) _ () _
ready-b1 _ (S.call _ _) _ () _

ig-does0 : ∀ (c : A.Conf) x P Q (eq : A.Conf.lp c ≡ S.iget x P Q)
           m rest ca →
           A.Conf.r2l c ≡ m ∷ rest →
           A.takeBit m ≡ A.bb0 ca →
           Σ (A.measure (getD c P x ca rest) < A.measure c)
             (λ lt → A.recvIgetL c x P Q eq ≡ A.does (getD c P x ca rest) lt)
ig-does0 c x P Q eq m rest ca qe tb rewrite qe | tb = _ , refl

ig-does1 : ∀ (c : A.Conf) x P Q (eq : A.Conf.lp c ≡ S.iget x P Q)
           m rest ca →
           A.Conf.r2l c ≡ m ∷ rest →
           A.takeBit m ≡ A.bb1 ca →
           Σ (A.measure (getD c Q x ca rest) < A.measure c)
             (λ lt → A.recvIgetL c x P Q eq ≡ A.does (getD c Q x ca rest) lt)
ig-does1 c x P Q eq m rest ca qe tb rewrite qe | tb = _ , refl

-- The false bit takes the first branch. `x` is written at the slot
-- the layout reserved, and the other branch's binders move into the
-- suffix, behind the branch that continues.
step-iget0 : ∀ {g c s x P Q m rest ca} (e : Embed g c s)
             (eq : A.Conf.lp c ≡ S.iget x P Q) →
             A.Conf.r2l c ≡ m ∷ rest →
             A.takeBit m ≡ A.bb0 ca →
             let d = getD c P x ca rest in
             Σ (A.measure d < A.measure c) (λ lt →
               Σ SConf (λ s′ →
                 A.recvIgetL c x P Q eq ≡ A.does d lt
                 × Embed g d s′
                 × s ⟶ₛ s′
                 × Step g (abs s) lside (abs s′)))
step-iget0 {g} {c} {s} {x} {P} {Q} {m} {rest} {ca} e eq qe tb =
  proj₁ moved , from (qrel-head qHere)
  where
  Γ = Embed.preL e
  passed = Embed.passedL e
  suf = Embed.sufL e
  lpE : left s ≡ go Γ (S.iget x P Q)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  frG : Frag (go Γ (S.iget x P Q))
  frG = subst Frag lpE (Embed.frL e)
  view = iget-view Γ x P Q frG
  geq = proj₁ view
  fp = proj₁ (proj₂ view)
  fq = proj₁ (proj₂ (proj₂ view))
  p = go ((x , S.bit) ∷ Γ) P
  q = go ((x , S.bit) ∷ Γ) Q
  proc≡ : left s ≡ siget x p q
  proc≡ = trans lpE geq
  d = getD c P x ca rest
  moved = ig-does0 c x P Q eq m rest ca qe tb
  qHere : QRel (alpha s) (m ∷ rest) (r2l s)
  qHere = subst (λ ms → QRel (alpha s) ms (r2l s)) qe (Embed.qR e)
  Result = Σ SConf (λ s′ →
             A.recvIgetL c x P Q eq ≡ A.does d (proj₁ moved)
             × Embed g d s′
             × s ⟶ₛ s′
             × Step g (abs s) lside (abs s′))
  from : Σ Tok (λ tok → Σ (List Tok) (λ us →
           r2l s ≡ tok ∷ us × TokOf (alpha s) m tok × QRel (alpha s) rest us)) →
         Result
  from (_ , _ , _ , of-lab b , _) = ⊥-elim (lab-bit0 b ca tb)
  from (.(pay k) , us , qeq , of-pay {W} {B} {v} {r} {k} {a} wEq _ na va , qTail) =
    bitW (take-bit0 W (A.car B v r) ca tb)
    where
    bitW : W ≡ S.bit × A.car B v r ≡ ca × A.asBit (A.car B v r) ≡ just S.b0 →
           Result
    bitW (refl , ce , ab) = bitB (sym wEq)
      where
      bitB : B ≡ S.bit → Result
      bitB refl = ready (ready-b0 v r a va ab)
        where
        ready : r ≡ S.lit S.b0 × a ≡ aBit false → Result
        ready (refl , refl) =
          s′ , proj₂ moved , e′ , st , gs
          where
          bp = bnames p
          bq = bnames q
          mid = (bp ++ bq) ++ suf
          names≡ : namesL s ≡ passed ++ (x ∷ mid)
          names≡ = trans (Embed.layL e)
                     (cong (λ bs → passed ++ bs ++ suf) (cong bnames proc≡))
          disAt : distinctN (passed ++ (x ∷ mid)) ≡ true
          disAt = subst (λ ns → distinctN ns ≡ true) names≡ (Embed.disL e)
          fr = trans (sym (fresh≡ x passed)) (dist-fresh passed x mid disAt)
          fd : findS x (namesL s) ≡ just (length passed)
          fd = trans (cong (findS x) names≡) (findS-at x passed mid fr)
          slot< : length passed < length (el s)
          slot< = subst (λ n → length passed < n)
                    (sym (trans (Embed.lenL e) (cong length names≡)))
                    (slot-lt passed x mid)
          b = length passed
          nt = nth-set b (suc k) (el s) slot<
          kept = vrel-widen (vrel-write b (el s) (suc k) (Embed.vL e))
          built = vr1 x fd ≤-refl nt na va kept
          slots≡ : setNth (slotL s) (suc k) (el s) ≡ setNth b (suc k) (el s)
          slots≡ = cong (λ i → setNth i (suc k) (el s)) (Embed.slot≡L e)
          ve≡ : A.bindV x ca (A.Conf.lv c) ≡
                (x , A.evar S.bit (S.lit S.b0)) ∷ A.Conf.lv c
          ve≡ = cong (λ z → A.bindV x z (A.Conf.lv c)) (sym ce)
          vHere = subst (λ xs → VRel (alpha s) xs (namesL s) (suc b)
                                  ((x , S.bit) ∷ Γ)
                                  (A.bindV x ca (A.Conf.lv c)))
                   (sym slots≡)
                   (subst (λ ve → VRel (alpha s) (setNth b (suc k) (el s))
                                      (namesL s) (suc b) ((x , S.bit) ∷ Γ) ve)
                      (sym ve≡) built)
          vDone = subst (λ n → VRel (alpha s) (setNth (slotL s) (suc k) (el s))
                                     (namesL s) n ((x , S.bit) ∷ Γ)
                                     (A.bindV x ca (A.Conf.lv c)))
                    (sym (len-snoc passed x)) vHere
          unf = castU s (f-iget x p q) (Embed.zPL e) proc≡ u-iget
          wp = walk-plain p (suc (il s)) (suc (slotL s))
                 (go-plain ((x , S.bit) ∷ Γ) P fp)
          w = Walked.w wp
          wk = walk-env s p (suc (il s)) (suc (slotL s)) w
                 (Embed.zIL e) (Walked.eq wp)
          st = iget0-l unf qeq na wk
          stepped = sim-fwd (Embed.hold e) st
          gs = proj₁ (proj₂ stepped)
          h′ = proj₂ (proj₂ stepped)
          s′ = getS s p us k w
          e′ : Embed g d s′
          e′ = record
            { hold = h′
            ; al≡ = Embed.al≡ e
            ; cap≡ = Embed.cap≡ e
            ; qL = Embed.qL e
            ; qR = qTail
            ; preL = (x , S.bit) ∷ Γ
            ; preR = Embed.preR e
            ; lp≡ = refl
            ; rp≡ = Embed.rp≡ e
            ; zPL = refl
            ; zPR = Embed.zPR e
            ; zIL = cong (addPend [] (il s) (slotL s)) (Embed.zIL e)
            ; zIR = Embed.zIR e
            ; frL = fp
            ; frR = Embed.frR e
            ; vL = vDone
            ; vR = Embed.vR e
            ; passedL = passed ++ (x ∷ [])
            ; sufL = bq ++ suf
            ; passedR = Embed.passedR e
            ; sufR = Embed.sufR e
            ; layL = trans (trans names≡ (cons-++ passed x mid))
                       (cong ((passed ++ (x ∷ [])) ++_) (++-assoc bp bq suf))
            ; layR = Embed.layR e
            ; slot≡L = trans (trans (Walked.at wp) (cong suc (Embed.slot≡L e)))
                             (sym (len-snoc passed x))
            ; slot≡R = Embed.slot≡R e
            ; disL = Embed.disL e
            ; disR = Embed.disR e
            ; lenL = trans (length-set (slotL s) (suc k) (el s)) (Embed.lenL e)
            ; lenR = Embed.lenR e
            }

-- The true bit skips the first branch. `x` is written, and that
-- branch's binders join `passed`, so the second branch starts where
-- `findS` will look.
step-iget1 : ∀ {g c s x P Q m rest ca} (e : Embed g c s)
             (eq : A.Conf.lp c ≡ S.iget x P Q) →
             A.Conf.r2l c ≡ m ∷ rest →
             A.takeBit m ≡ A.bb1 ca →
             let d = getD c Q x ca rest in
             Σ (A.measure d < A.measure c) (λ lt →
               Σ SConf (λ s′ →
                 A.recvIgetL c x P Q eq ≡ A.does d lt
                 × Embed g d s′
                 × s ⟶ₛ s′
                 × Step g (abs s) lside (abs s′)))
step-iget1 {g} {c} {s} {x} {P} {Q} {m} {rest} {ca} e eq qe tb =
  proj₁ moved , from (qrel-head qHere)
  where
  Γ = Embed.preL e
  passed = Embed.passedL e
  suf = Embed.sufL e
  lpE : left s ≡ go Γ (S.iget x P Q)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  frG : Frag (go Γ (S.iget x P Q))
  frG = subst Frag lpE (Embed.frL e)
  view = iget-view Γ x P Q frG
  geq = proj₁ view
  fp = proj₁ (proj₂ view)
  fq = proj₁ (proj₂ (proj₂ view))
  p = go ((x , S.bit) ∷ Γ) P
  q = go ((x , S.bit) ∷ Γ) Q
  proc≡ : left s ≡ siget x p q
  proc≡ = trans lpE geq
  d = getD c Q x ca rest
  moved = ig-does1 c x P Q eq m rest ca qe tb
  qHere : QRel (alpha s) (m ∷ rest) (r2l s)
  qHere = subst (λ ms → QRel (alpha s) ms (r2l s)) qe (Embed.qR e)
  Result = Σ SConf (λ s′ →
             A.recvIgetL c x P Q eq ≡ A.does d (proj₁ moved)
             × Embed g d s′
             × s ⟶ₛ s′
             × Step g (abs s) lside (abs s′))
  from : Σ Tok (λ tok → Σ (List Tok) (λ us →
           r2l s ≡ tok ∷ us × TokOf (alpha s) m tok × QRel (alpha s) rest us)) →
         Result
  from (_ , _ , _ , of-lab b , _) = ⊥-elim (lab-bit1 b ca tb)
  from (.(pay k) , us , qeq , of-pay {W} {B} {v} {r} {k} {a} wEq _ na va , qTail) =
    bitW (take-bit1 W (A.car B v r) ca tb)
    where
    bitW : W ≡ S.bit × A.car B v r ≡ ca × A.asBit (A.car B v r) ≡ just S.b1 →
           Result
    bitW (refl , ce , ab) = bitB (sym wEq)
      where
      bitB : B ≡ S.bit → Result
      bitB refl = ready (ready-b1 v r a va ab)
        where
        ready : r ≡ S.lit S.b1 × a ≡ aBit true → Result
        ready (refl , refl) =
          s′ , proj₂ moved , e′ , st , gs
          where
          bp = bnames p
          bq = bnames q
          mid = (bp ++ bq) ++ suf
          names≡ : namesL s ≡ passed ++ (x ∷ mid)
          names≡ = trans (Embed.layL e)
                     (cong (λ bs → passed ++ bs ++ suf) (cong bnames proc≡))
          disAt : distinctN (passed ++ (x ∷ mid)) ≡ true
          disAt = subst (λ ns → distinctN ns ≡ true) names≡ (Embed.disL e)
          fr = trans (sym (fresh≡ x passed)) (dist-fresh passed x mid disAt)
          fd : findS x (namesL s) ≡ just (length passed)
          fd = trans (cong (findS x) names≡) (findS-at x passed mid fr)
          slot< : length passed < length (el s)
          slot< = subst (λ n → length passed < n)
                    (sym (trans (Embed.lenL e) (cong length names≡)))
                    (slot-lt passed x mid)
          b = length passed
          nt = nth-set b (suc k) (el s) slot<
          kept = vrel-widen (vrel-write b (el s) (suc k) (Embed.vL e))
          built = vr1 x fd ≤-refl nt na va kept
          slots≡ : setNth (slotL s) (suc k) (el s) ≡ setNth b (suc k) (el s)
          slots≡ = cong (λ i → setNth i (suc k) (el s)) (Embed.slot≡L e)
          ve≡ : A.bindV x ca (A.Conf.lv c) ≡
                (x , A.evar S.bit (S.lit S.b1)) ∷ A.Conf.lv c
          ve≡ = cong (λ z → A.bindV x z (A.Conf.lv c)) (sym ce)
          vHere = subst (λ xs → VRel (alpha s) xs (namesL s) (suc b)
                                  ((x , S.bit) ∷ Γ)
                                  (A.bindV x ca (A.Conf.lv c)))
                   (sym slots≡)
                   (subst (λ ve → VRel (alpha s) (setNth b (suc k) (el s))
                                      (namesL s) (suc b) ((x , S.bit) ∷ Γ) ve)
                      (sym ve≡) built)
          vDone = subst (λ n → VRel (alpha s) (setNth (slotL s) (suc k) (el s))
                                     (namesL s) n ((x , S.bit) ∷ Γ)
                                     (A.bindV x ca (A.Conf.lv c)))
                    (sym (len-snoc passed x)) vHere
          vShift = subst (λ n → VRel (alpha s) (setNth (slotL s) (suc k) (el s))
                                      (namesL s) n ((x , S.bit) ∷ Γ)
                                      (A.bindV x ca (A.Conf.lv c)))
                     (sym (length-++ (passed ++ (x ∷ [])) {bp}))
                     (vrel-plus (length bp) vDone)
          unf = castU s (f-iget x p q) (Embed.zPL e) proc≡ u-iget
          wp = walk-plain p (suc (il s)) (suc (slotL s))
                 (go-plain ((x , S.bit) ∷ Γ) P fp)
          w1 = Walked.w wp
          wq = walk-plain q (next w1) (slotN w1)
                 (go-plain ((x , S.bit) ∷ Γ) Q fq)
          w2 = Walked.w wq
          wk1 = walk-env s p (suc (il s)) (suc (slotL s)) w1
                  (Embed.zIL e) (Walked.eq wp)
          wk2 = walk-env s q (next w1) (slotN w1) w2
                  (Embed.zIL e) (Walked.eq wq)
          st = iget1-l unf qeq na wk1 wk2
          stepped = sim-fwd (Embed.hold e) st
          gs = proj₁ (proj₂ stepped)
          h′ = proj₂ (proj₂ stepped)
          s′ = getS s q us k w2
          e′ : Embed g d s′
          e′ = record
            { hold = h′
            ; al≡ = Embed.al≡ e
            ; cap≡ = Embed.cap≡ e
            ; qL = Embed.qL e
            ; qR = qTail
            ; preL = (x , S.bit) ∷ Γ
            ; preR = Embed.preR e
            ; lp≡ = refl
            ; rp≡ = Embed.rp≡ e
            ; zPL = refl
            ; zPR = Embed.zPR e
            ; zIL = cong (addPend [] (il s) (slotL s)) (Embed.zIL e)
            ; zIR = Embed.zIR e
            ; frL = fq
            ; frR = Embed.frR e
            ; vL = vShift
            ; vR = Embed.vR e
            ; passedL = (passed ++ (x ∷ [])) ++ bp
            ; sufL = suf
            ; passedR = Embed.passedR e
            ; sufR = Embed.sufR e
            ; layL = trans (trans (trans names≡ (cons-++ passed x mid))
                              (cong ((passed ++ (x ∷ [])) ++_)
                                 (++-assoc bp bq suf)))
                       (sym (++-assoc (passed ++ (x ∷ [])) bp (bq ++ suf)))
            ; layR = Embed.layR e
            ; slot≡L = trans (trans (Walked.at wq) (Walked.sn wp))
                         (trans (cong (_+ length bp)
                                   (trans (cong suc (Embed.slot≡L e))
                                          (sym (len-snoc passed x))))
                                (sym (length-++ (passed ++ (x ∷ [])) {bp})))
            ; slot≡R = Embed.slot≡R e
            ; disL = Embed.disL e
            ; disR = Embed.disR e
            ; lenL = trans (length-set (slotL s) (suc k) (el s)) (Embed.lenL e)
            ; lenR = Embed.lenR e
            }

ig-does0R : ∀ (c : A.Conf) x P Q (eq : A.Conf.rp c ≡ S.iget x P Q)
            m rest ca →
            A.Conf.l2r c ≡ m ∷ rest →
            A.takeBit m ≡ A.bb0 ca →
            Σ (A.measure (getDR c P x ca rest) < A.measure c)
              (λ lt → A.recvIgetR c x P Q eq ≡ A.does (getDR c P x ca rest) lt)
ig-does0R c x P Q eq m rest ca qe tb rewrite qe | tb = _ , refl

ig-does1R : ∀ (c : A.Conf) x P Q (eq : A.Conf.rp c ≡ S.iget x P Q)
            m rest ca →
            A.Conf.l2r c ≡ m ∷ rest →
            A.takeBit m ≡ A.bb1 ca →
            Σ (A.measure (getDR c Q x ca rest) < A.measure c)
              (λ lt → A.recvIgetR c x P Q eq ≡ A.does (getDR c Q x ca rest) lt)
ig-does1R c x P Q eq m rest ca qe tb rewrite qe | tb = _ , refl

step-iget0R : ∀ {g c s x P Q m rest ca} (e : Embed g c s)
              (eq : A.Conf.rp c ≡ S.iget x P Q) →
              A.Conf.l2r c ≡ m ∷ rest →
              A.takeBit m ≡ A.bb0 ca →
              let d = getDR c P x ca rest in
              Σ (A.measure d < A.measure c) (λ lt →
                Σ SConf (λ s′ →
                  A.recvIgetR c x P Q eq ≡ A.does d lt
                  × Embed g d s′
                  × s ⟶ₛ s′
                  × Step g (abs s) rside (abs s′)))
step-iget0R {g} {c} {s} {x} {P} {Q} {m} {rest} {ca} e eq qe tb =
  proj₁ moved , from (qrel-head qHere)
  where
  Γ = Embed.preR e
  passed = Embed.passedR e
  suf = Embed.sufR e
  rpE : right s ≡ go Γ (S.iget x P Q)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  frG : Frag (go Γ (S.iget x P Q))
  frG = subst Frag rpE (Embed.frR e)
  view = iget-view Γ x P Q frG
  geq = proj₁ view
  fp = proj₁ (proj₂ view)
  fq = proj₁ (proj₂ (proj₂ view))
  p = go ((x , S.bit) ∷ Γ) P
  q = go ((x , S.bit) ∷ Γ) Q
  proc≡ : right s ≡ siget x p q
  proc≡ = trans rpE geq
  d = getDR c P x ca rest
  moved = ig-does0R c x P Q eq m rest ca qe tb
  qHere : QRel (alpha s) (m ∷ rest) (l2r s)
  qHere = subst (λ ms → QRel (alpha s) ms (l2r s)) qe (Embed.qL e)
  Result = Σ SConf (λ s′ →
             A.recvIgetR c x P Q eq ≡ A.does d (proj₁ moved)
             × Embed g d s′
             × s ⟶ₛ s′
             × Step g (abs s) rside (abs s′))
  from : Σ Tok (λ tok → Σ (List Tok) (λ us →
           l2r s ≡ tok ∷ us × TokOf (alpha s) m tok × QRel (alpha s) rest us)) →
         Result
  from (_ , _ , _ , of-lab b , _) = ⊥-elim (lab-bit0 b ca tb)
  from (.(pay k) , us , qeq , of-pay {W} {B} {v} {r} {k} {a} wEq _ na va , qTail) =
    bitW (take-bit0 W (A.car B v r) ca tb)
    where
    bitW : W ≡ S.bit × A.car B v r ≡ ca × A.asBit (A.car B v r) ≡ just S.b0 →
           Result
    bitW (refl , ce , ab) = bitB (sym wEq)
      where
      bitB : B ≡ S.bit → Result
      bitB refl = ready (ready-b0 v r a va ab)
        where
        ready : r ≡ S.lit S.b0 × a ≡ aBit false → Result
        ready (refl , refl) =
          s′ , proj₂ moved , e′ , st , gs
          where
          bp = bnames p
          bq = bnames q
          mid = (bp ++ bq) ++ suf
          names≡ : namesR s ≡ passed ++ (x ∷ mid)
          names≡ = trans (Embed.layR e)
                     (cong (λ bs → passed ++ bs ++ suf) (cong bnames proc≡))
          disAt : distinctN (passed ++ (x ∷ mid)) ≡ true
          disAt = subst (λ ns → distinctN ns ≡ true) names≡ (Embed.disR e)
          fr = trans (sym (fresh≡ x passed)) (dist-fresh passed x mid disAt)
          fd : findS x (namesR s) ≡ just (length passed)
          fd = trans (cong (findS x) names≡) (findS-at x passed mid fr)
          slot< : length passed < length (er s)
          slot< = subst (λ n → length passed < n)
                    (sym (trans (Embed.lenR e) (cong length names≡)))
                    (slot-lt passed x mid)
          b = length passed
          nt = nth-set b (suc k) (er s) slot<
          kept = vrel-widen (vrel-write b (er s) (suc k) (Embed.vR e))
          built = vr1 x fd ≤-refl nt na va kept
          slots≡ : setNth (slotR s) (suc k) (er s) ≡ setNth b (suc k) (er s)
          slots≡ = cong (λ i → setNth i (suc k) (er s)) (Embed.slot≡R e)
          ve≡ : A.bindV x ca (A.Conf.rv c) ≡
                (x , A.evar S.bit (S.lit S.b0)) ∷ A.Conf.rv c
          ve≡ = cong (λ z → A.bindV x z (A.Conf.rv c)) (sym ce)
          vHere = subst (λ xs → VRel (alpha s) xs (namesR s) (suc b)
                                  ((x , S.bit) ∷ Γ)
                                  (A.bindV x ca (A.Conf.rv c)))
                   (sym slots≡)
                   (subst (λ ve → VRel (alpha s) (setNth b (suc k) (er s))
                                      (namesR s) (suc b) ((x , S.bit) ∷ Γ) ve)
                      (sym ve≡) built)
          vDone = subst (λ n → VRel (alpha s) (setNth (slotR s) (suc k) (er s))
                                     (namesR s) n ((x , S.bit) ∷ Γ)
                                     (A.bindV x ca (A.Conf.rv c)))
                    (sym (len-snoc passed x)) vHere
          unf = castUR s (f-iget x p q) (Embed.zPR e) proc≡ u-iget
          wp = walk-plain p (suc (ir s)) (suc (slotR s))
                 (go-plain ((x , S.bit) ∷ Γ) P fp)
          w = Walked.w wp
          wk = walk-envR s p (suc (ir s)) (suc (slotR s)) w
                 (Embed.zIR e) (Walked.eq wp)
          st = iget0-r unf qeq na wk
          stepped = sim-fwd (Embed.hold e) st
          gs = proj₁ (proj₂ stepped)
          h′ = proj₂ (proj₂ stepped)
          s′ = getSR s p us k w
          e′ : Embed g d s′
          e′ = record
            { hold = h′
            ; al≡ = Embed.al≡ e
            ; cap≡ = Embed.cap≡ e
            ; qL = qTail
            ; qR = Embed.qR e
            ; preL = Embed.preL e
            ; preR = (x , S.bit) ∷ Γ
            ; lp≡ = Embed.lp≡ e
            ; rp≡ = refl
            ; zPL = Embed.zPL e
            ; zPR = refl
            ; zIL = Embed.zIL e
            ; zIR = cong (addPend [] (ir s) (slotR s)) (Embed.zIR e)
            ; frL = Embed.frL e
            ; frR = fp
            ; vL = Embed.vL e
            ; vR = vDone
            ; passedL = Embed.passedL e
            ; sufL = Embed.sufL e
            ; passedR = passed ++ (x ∷ [])
            ; sufR = bq ++ suf
            ; layL = Embed.layL e
            ; layR = trans (trans names≡ (cons-++ passed x mid))
                       (cong ((passed ++ (x ∷ [])) ++_) (++-assoc bp bq suf))
            ; slot≡L = Embed.slot≡L e
            ; slot≡R = trans (trans (Walked.at wp) (cong suc (Embed.slot≡R e)))
                             (sym (len-snoc passed x))
            ; disL = Embed.disL e
            ; disR = Embed.disR e
            ; lenL = Embed.lenL e
            ; lenR = trans (length-set (slotR s) (suc k) (er s)) (Embed.lenR e)
            }

step-iget1R : ∀ {g c s x P Q m rest ca} (e : Embed g c s)
              (eq : A.Conf.rp c ≡ S.iget x P Q) →
              A.Conf.l2r c ≡ m ∷ rest →
              A.takeBit m ≡ A.bb1 ca →
              let d = getDR c Q x ca rest in
              Σ (A.measure d < A.measure c) (λ lt →
                Σ SConf (λ s′ →
                  A.recvIgetR c x P Q eq ≡ A.does d lt
                  × Embed g d s′
                  × s ⟶ₛ s′
                  × Step g (abs s) rside (abs s′)))
step-iget1R {g} {c} {s} {x} {P} {Q} {m} {rest} {ca} e eq qe tb =
  proj₁ moved , from (qrel-head qHere)
  where
  Γ = Embed.preR e
  passed = Embed.passedR e
  suf = Embed.sufR e
  rpE : right s ≡ go Γ (S.iget x P Q)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  frG : Frag (go Γ (S.iget x P Q))
  frG = subst Frag rpE (Embed.frR e)
  view = iget-view Γ x P Q frG
  geq = proj₁ view
  fp = proj₁ (proj₂ view)
  fq = proj₁ (proj₂ (proj₂ view))
  p = go ((x , S.bit) ∷ Γ) P
  q = go ((x , S.bit) ∷ Γ) Q
  proc≡ : right s ≡ siget x p q
  proc≡ = trans rpE geq
  d = getDR c Q x ca rest
  moved = ig-does1R c x P Q eq m rest ca qe tb
  qHere : QRel (alpha s) (m ∷ rest) (l2r s)
  qHere = subst (λ ms → QRel (alpha s) ms (l2r s)) qe (Embed.qL e)
  Result = Σ SConf (λ s′ →
             A.recvIgetR c x P Q eq ≡ A.does d (proj₁ moved)
             × Embed g d s′
             × s ⟶ₛ s′
             × Step g (abs s) rside (abs s′))
  from : Σ Tok (λ tok → Σ (List Tok) (λ us →
           l2r s ≡ tok ∷ us × TokOf (alpha s) m tok × QRel (alpha s) rest us)) →
         Result
  from (_ , _ , _ , of-lab b , _) = ⊥-elim (lab-bit1 b ca tb)
  from (.(pay k) , us , qeq , of-pay {W} {B} {v} {r} {k} {a} wEq _ na va , qTail) =
    bitW (take-bit1 W (A.car B v r) ca tb)
    where
    bitW : W ≡ S.bit × A.car B v r ≡ ca × A.asBit (A.car B v r) ≡ just S.b1 →
           Result
    bitW (refl , ce , ab) = bitB (sym wEq)
      where
      bitB : B ≡ S.bit → Result
      bitB refl = ready (ready-b1 v r a va ab)
        where
        ready : r ≡ S.lit S.b1 × a ≡ aBit true → Result
        ready (refl , refl) =
          s′ , proj₂ moved , e′ , st , gs
          where
          bp = bnames p
          bq = bnames q
          mid = (bp ++ bq) ++ suf
          names≡ : namesR s ≡ passed ++ (x ∷ mid)
          names≡ = trans (Embed.layR e)
                     (cong (λ bs → passed ++ bs ++ suf) (cong bnames proc≡))
          disAt : distinctN (passed ++ (x ∷ mid)) ≡ true
          disAt = subst (λ ns → distinctN ns ≡ true) names≡ (Embed.disR e)
          fr = trans (sym (fresh≡ x passed)) (dist-fresh passed x mid disAt)
          fd : findS x (namesR s) ≡ just (length passed)
          fd = trans (cong (findS x) names≡) (findS-at x passed mid fr)
          slot< : length passed < length (er s)
          slot< = subst (λ n → length passed < n)
                    (sym (trans (Embed.lenR e) (cong length names≡)))
                    (slot-lt passed x mid)
          b = length passed
          nt = nth-set b (suc k) (er s) slot<
          kept = vrel-widen (vrel-write b (er s) (suc k) (Embed.vR e))
          built = vr1 x fd ≤-refl nt na va kept
          slots≡ : setNth (slotR s) (suc k) (er s) ≡ setNth b (suc k) (er s)
          slots≡ = cong (λ i → setNth i (suc k) (er s)) (Embed.slot≡R e)
          ve≡ : A.bindV x ca (A.Conf.rv c) ≡
                (x , A.evar S.bit (S.lit S.b1)) ∷ A.Conf.rv c
          ve≡ = cong (λ z → A.bindV x z (A.Conf.rv c)) (sym ce)
          vHere = subst (λ xs → VRel (alpha s) xs (namesR s) (suc b)
                                  ((x , S.bit) ∷ Γ)
                                  (A.bindV x ca (A.Conf.rv c)))
                   (sym slots≡)
                   (subst (λ ve → VRel (alpha s) (setNth b (suc k) (er s))
                                      (namesR s) (suc b) ((x , S.bit) ∷ Γ) ve)
                      (sym ve≡) built)
          vDone = subst (λ n → VRel (alpha s) (setNth (slotR s) (suc k) (er s))
                                     (namesR s) n ((x , S.bit) ∷ Γ)
                                     (A.bindV x ca (A.Conf.rv c)))
                    (sym (len-snoc passed x)) vHere
          vShift = subst (λ n → VRel (alpha s) (setNth (slotR s) (suc k) (er s))
                                      (namesR s) n ((x , S.bit) ∷ Γ)
                                      (A.bindV x ca (A.Conf.rv c)))
                     (sym (length-++ (passed ++ (x ∷ [])) {bp}))
                     (vrel-plus (length bp) vDone)
          unf = castUR s (f-iget x p q) (Embed.zPR e) proc≡ u-iget
          wp = walk-plain p (suc (ir s)) (suc (slotR s))
                 (go-plain ((x , S.bit) ∷ Γ) P fp)
          w1 = Walked.w wp
          wq = walk-plain q (next w1) (slotN w1)
                 (go-plain ((x , S.bit) ∷ Γ) Q fq)
          w2 = Walked.w wq
          wk1 = walk-envR s p (suc (ir s)) (suc (slotR s)) w1
                  (Embed.zIR e) (Walked.eq wp)
          wk2 = walk-envR s q (next w1) (slotN w1) w2
                  (Embed.zIR e) (Walked.eq wq)
          st = iget1-r unf qeq na wk1 wk2
          stepped = sim-fwd (Embed.hold e) st
          gs = proj₁ (proj₂ stepped)
          h′ = proj₂ (proj₂ stepped)
          s′ = getSR s q us k w2
          e′ : Embed g d s′
          e′ = record
            { hold = h′
            ; al≡ = Embed.al≡ e
            ; cap≡ = Embed.cap≡ e
            ; qL = qTail
            ; qR = Embed.qR e
            ; preL = Embed.preL e
            ; preR = (x , S.bit) ∷ Γ
            ; lp≡ = Embed.lp≡ e
            ; rp≡ = refl
            ; zPL = Embed.zPL e
            ; zPR = refl
            ; zIL = Embed.zIL e
            ; zIR = cong (addPend [] (ir s) (slotR s)) (Embed.zIR e)
            ; frL = Embed.frL e
            ; frR = fq
            ; vL = Embed.vL e
            ; vR = vShift
            ; passedL = Embed.passedL e
            ; sufL = Embed.sufL e
            ; passedR = (passed ++ (x ∷ [])) ++ bp
            ; sufR = suf
            ; layL = Embed.layL e
            ; layR = trans (trans (trans names≡ (cons-++ passed x mid))
                              (cong ((passed ++ (x ∷ [])) ++_)
                                 (++-assoc bp bq suf)))
                       (sym (++-assoc (passed ++ (x ∷ [])) bp (bq ++ suf)))
            ; slot≡L = Embed.slot≡L e
            ; slot≡R = trans (trans (Walked.at wq) (Walked.sn wp))
                         (trans (cong (_+ length bp)
                                   (trans (cong suc (Embed.slot≡R e))
                                          (sym (len-snoc passed x))))
                                (sym (length-++ (passed ++ (x ∷ [])) {bp})))
            ; disL = Embed.disL e
            ; disR = Embed.disR e
            ; lenL = Embed.lenL e
            ; lenR = trans (length-set (slotR s) (suc k) (er s)) (Embed.lenR e)
            }

-- A nullary constructor arm is the process it stores. `openHit` and
-- `findIn` are `with`s, so the name test is rewritten before they reduce.
==-sym : ∀ x y → (x == y) ≡ true → (y == x) ≡ true
==-sym x y eq with x ≟ y
==-sym x y refl | yes′ refl with y ≟ x
==-sym x y refl | yes′ refl | yes′ _ = refl
==-sym x y refl | yes′ refl | no′ ¬eq = ⊥-elim (¬eq refl)
==-sym x y () | no′ _

open-nil : ∀ y name (P : S.Proc) ps → (y == name) ≡ true →
           A.openHit y name [] P S.snil ps ≡ just (P , A.leSubst [] P ps)
open-nil y name P ps eq rewrite eq = refl

arm-here : ∀ name y (fs : List S.Fld) (P : S.Proc) cs ps →
           (name == y) ≡ true → (y == name) ≡ true →
           A.findIn name S.snil (S.ctor y fs ∷ cs) (S.named y [] P ∷ ps) ≡
             just (P , A.leSubst [] P ps)
arm-here name y fs P cs ps eq1 eq2 rewrite eq1 = open-nil y name P ps eq2

arm-raise : (ps : List S.PArm) (p : S.Proc) →
            Maybe (Σ S.Proc (λ R → A.size R ≤ A.sizeArms ps)) →
            Maybe (Σ S.Proc (λ R → A.size R ≤ A.size p + A.sizeArms ps))
arm-raise _ _ nothing = nothing
arm-raise ps p (just (R , le)) =
  just (R , ≤-trans le (m≤n+m (A.sizeArms ps) (A.size p)))

arm-skip : ∀ name y (fs : List S.Fld) (P : S.Proc) cs ps mq →
           (name == y) ≡ false →
           A.findIn name S.snil cs ps ≡ mq →
           A.findIn name S.snil (S.ctor y fs ∷ cs) (S.named y [] P ∷ ps) ≡
             arm-raise ps P mq
arm-skip name y fs P cs ps nothing eq1 eq2 rewrite eq1 | eq2 = refl
arm-skip name y fs P cs ps (just (R , le)) eq1 eq2 rewrite eq1 | eq2 = refl

nojust : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
nojust ()

find-empty : ∀ name sp cs → A.findIn name sp cs [] ≡ nothing
find-empty _ _ [] = refl
find-empty _ _ (_ ∷ _) = refl

expr-lit : ∀ {T} (u : S.Val T) ps →
           A.armExprPick (S.lit u) ps ≡ A.armPick T u ps
expr-lit _ _ = refl

pick-con : ∀ d as c sp ps →
           A.armPick (S.dat d as) (S.con c sp) ps ≡
             A.findIn c sp (S.ctorsOf d) ps
pick-con _ _ _ _ _ = refl

pick-empty : ∀ {T} (u : S.Val T) → A.armPick T u [] ≡ nothing
pick-empty {S.nat} S.zero = refl
pick-empty {S.nat} (S.suc _) = refl
pick-empty {S.bit} S.b0 = refl
pick-empty {S.bit} S.b1 = refl
pick-empty {S.unit} S.tt = refl
pick-empty {S.pair _ _} (S.tup _ _) = refl
pick-empty {S.rec _} (S.rec _) = refl
pick-empty {S.vec _ _} (S.rep _) = refl
pick-empty {S.dat d as} (S.con c sp) = find-empty c sp (S.ctorsOf d)

empty-arms : ∀ Γ ps bs → matchArms Γ [] ps ≡ just bs → ps ≡ [] × bs ≡ []
empty-arms _ [] .[] refl = refl , refl
empty-arms _ (_ ∷ _) _ ()

-- A fragment `mget` is a nullary declaration: each arm is that
-- constructor's name, in order, with no binders. The source arm is
-- the session process read under the binder the `mget` introduces.
data Rows (Γ : List (String × S.Ty)) :
         List S.Ctor → List S.PArm → List Arm → Set where
  r0 : Rows Γ [] [] []
  r1 : ∀ {n fs P cs ps bs} →
       Frag (go Γ P) →
       Rows Γ cs ps bs →
       Rows Γ (S.ctor n fs ∷ cs) (S.named n [] P ∷ ps) (aok n (go Γ P) ∷ bs)

rows : ∀ Γ cs ps bs →
       matchArms Γ cs ps ≡ just bs →
       FragArms bs →
       Rows Γ cs ps bs
rows _ [] [] .[] refl farms0 = r0
rows _ [] (_ ∷ _) _ () _
rows _ (S.ctor _ _ ∷ _) [] _ () _
rows _ (S.ctor _ _ ∷ _) (S.bare _ ∷ _) _ () _
rows _ (S.ctor _ _ ∷ _) (S.prod _ _ ∷ _) _ () _
rows _ (S.ctor _ _ ∷ _) (S.fork _ _ _ _ ∷ _) _ () _
rows _ (S.ctor _ _ ∷ _) (S.named _ (_ ∷ _) _ ∷ _) _ () _
rows Γ (S.ctor n _ ∷ cs) (S.named k [] P ∷ ps) bs eq fas
  with n == k | inspect (n ==_) k
rows Γ (S.ctor n _ ∷ cs) (S.named k [] P ∷ ps) _ () _ | false | _
rows Γ (S.ctor n _ ∷ cs) (S.named k [] P ∷ ps) bs eq fas | true | [ eqb ]
  with matchArms Γ cs ps | inspect (matchArms Γ cs) ps
rows Γ (S.ctor n _ ∷ cs) (S.named k [] P ∷ ps) _ () _ | true | [ eqb ] | nothing | _
rows Γ (S.ctor n _ ∷ cs) (S.named k [] P ∷ ps) bs eq fas
  | true | [ eqb ] | just bs′ | [ eqm ] = same (==-≟ n k eqb) eq fas
  where
  same : n ≡ k →
         just (aok k (go Γ P) ∷ bs′) ≡ just bs →
         FragArms bs →
         Rows Γ (S.ctor n _ ∷ cs) (S.named k [] P ∷ ps) bs
  same refl refl (farms1 (farm fp) fas′) =
    r1 fp (rows Γ cs ps bs′ eqm fas′)

-- The arm `findIn` returns, read at the counters `armGo` starts from.
-- `skip` is the binders of the arms before it. `suf` is the binders after.
record Hit (Γ : List (String × S.Ty)) (name : String)
           (bs : List Arm) (n s : ℕ) (goal : S.Proc) : Set where
  field
    R : S.Proc
    rid : R ≡ goal
    proc : SProc
    w : W
    skip suf : List String
    fr : Frag proc
    same : proc ≡ go Γ R
    ago : armGo [] name bs n s ≡ just (w , proc)
    at0 : atSlot w ≡ s + length skip
    split : bnamesArms bs ≡ skip ++ bnames proc ++ suf

-- Rewrite the name test in the clause that owns the `findIn` equality.
-- A `with` on that test abstracts the equality and leaves it unreduced.
mutual
  hitHere : ∀ {Γ name y fs P cs ps bs R n s} →
            (le : A.size R ≤ A.sizeArms (S.named y [] P ∷ ps)) →
            Frag (go Γ P) →
            Rows Γ cs ps bs →
            (name == y) ≡ true →
            A.findIn name S.snil (S.ctor y fs ∷ cs) (S.named y [] P ∷ ps) ≡
              just (R , le) →
            Hit Γ name (aok y (go Γ P) ∷ bs) n s R
  hitHere {Γ} {name} {y} {fs} {P} {cs} {ps} {bs} {R = R} {n = n} {s = s}
          le fp rest eb eq = build (paired eb (==-sym name y eb) eq)
    where
    paired : (name == y) ≡ true → (y == name) ≡ true →
             A.findIn name S.snil (S.ctor y fs ∷ cs) (S.named y [] P ∷ ps) ≡
               just (R , le) →
             (P , A.leSubst [] P ps) ≡ (R , le)
    paired eb′ sy eq′ =
      just-inj (trans (sym (arm-here name y fs P cs ps eb′ sy)) eq′)
    build : (P , A.leSubst [] P ps) ≡ (R , le) →
            Hit Γ name (aok y (go Γ P) ∷ bs) n s R
    build refl = record
      { R = P
      ; rid = refl
      ; proc = go Γ P
      ; w = Walked.w wp
      ; skip = []
      ; suf = bnamesArms bs
      ; fr = fp
      ; same = refl
      ; ago = armGo-take {ρ = []} {name = name} {y = y} {p = go Γ P} {as = bs}
                {n = n} {s = s} {w = Walked.w wp} (Walked.eq wp) eb
      ; at0 = trans (Walked.at wp) (sym (+-identityʳ s))
      ; split = refl
      }
      where
      wp = walk-plain (go Γ P) n s (go-plain Γ P fp)

  hitSkip : ∀ {Γ name y fs P cs ps bs R n s} →
            (le : A.size R ≤ A.sizeArms (S.named y [] P ∷ ps)) →
            Frag (go Γ P) →
            Rows Γ cs ps bs →
            (name == y) ≡ false →
            A.findIn name S.snil (S.ctor y fs ∷ cs) (S.named y [] P ∷ ps) ≡
              just (R , le) →
            Hit Γ name (aok y (go Γ P) ∷ bs) n s R
  hitSkip {Γ} {name} {y} {fs} {P} {cs} {ps} {bs} {R = R} {n = n} {s = s}
          le fp rest eb eq = step eb eq (A.findIn name S.snil cs ps) refl
    where
    step : (name == y) ≡ false →
           A.findIn name S.snil (S.ctor y fs ∷ cs) (S.named y [] P ∷ ps) ≡
             just (R , le) →
           (mq : Maybe (Σ S.Proc (λ R′ → A.size R′ ≤ A.sizeArms ps))) →
           A.findIn name S.snil cs ps ≡ mq →
           Hit Γ name (aok y (go Γ P) ∷ bs) n s R
    step eb′ eq′ nothing eqt = ⊥-elim (gone eb′ eqt eq′)
      where
      gone : (name == y) ≡ false →
             A.findIn name S.snil cs ps ≡ nothing →
             A.findIn name S.snil (S.ctor y fs ∷ cs) (S.named y [] P ∷ ps) ≡
               just (R , le) →
             ⊥
      gone eb′ eqt eq′ =
        nojust (trans (sym (arm-skip name y fs P cs ps nothing eb′ eqt)) eq′)
    step eb′ eq′ (just (R′ , le′)) eqt = build (raised eb′ eqt eq′) eqt
      where
      raised : (name == y) ≡ false →
               A.findIn name S.snil cs ps ≡ just (R′ , le′) →
               A.findIn name S.snil (S.ctor y fs ∷ cs) (S.named y [] P ∷ ps) ≡
                 just (R , le) →
               (R′ , ≤-trans le′ (m≤n+m (A.sizeArms ps) (A.size P))) ≡ (R , le)
      raised eb′ eqt eq′ =
        just-inj (trans (sym (arm-skip name y fs P cs ps (just (R′ , le′)) eb′ eqt)) eq′)
      build : (R′ , ≤-trans le′ (m≤n+m (A.sizeArms ps) (A.size P))) ≡ (R , le) →
              A.findIn name S.snil cs ps ≡ just (R′ , le′) →
              Hit Γ name (aok y (go Γ P) ∷ bs) n s R
      build refl eqt = record
        { R = Hit.R rec
        ; rid = Hit.rid rec
        ; proc = Hit.proc rec
        ; w = Hit.w rec
        ; skip = bnames (go Γ P) ++ Hit.skip rec
        ; suf = Hit.suf rec
        ; fr = Hit.fr rec
        ; same = Hit.same rec
        ; ago = trans (armGo-skip {ρ = []} {name = name} {y = y}
                        {p = go Γ P} {as = bs} {n = n} {s = s} {w = w0}
                        (Walked.eq wp) eb)
                      (Hit.ago rec)
        ; at0 = trans (trans (Hit.at0 rec)
                         (cong (_+ length (Hit.skip rec)) (Walked.sn wp)))
                      (trans (+-assoc s (length (bnames (go Γ P)))
                                (length (Hit.skip rec)))
                         (cong (s +_)
                            (sym (length-++ (bnames (go Γ P)) {Hit.skip rec}))))
        ; split = trans (cong (bnames (go Γ P) ++_) (Hit.split rec))
                    (sym (++-assoc (bnames (go Γ P)) (Hit.skip rec)
                           (bnames (Hit.proc rec) ++ Hit.suf rec)))
        }
        where
        wp = walk-plain (go Γ P) n s (go-plain Γ P fp)
        w0 = Walked.w wp
        rec = pickHit {n = next w0} {s = slotN w0} le′ rest eqt

  pickHit : ∀ {Γ name cs ps bs R n s}
            (le : A.size R ≤ A.sizeArms ps) →
            Rows Γ cs ps bs →
            A.findIn name S.snil cs ps ≡ just (R , le) →
            Hit Γ name bs n s R
  pickHit _ r0 eq = ⊥-elim (nojust eq)
  pickHit {Γ = Γ} {name = name} {R = R} {n = n} {s = s} le
          (r1 {n = y} {fs = fs} {P = P} fp rest) eq = branch (name == y) refl
    where
    branch : (b : Bool) → (name == y) ≡ b →
             Hit Γ name (aok y (go Γ P) ∷ _) n s R
    branch true eb = hitHere {fs = fs} {n = n} {s = s} le fp rest eb eq
    branch false eb = hitSkip {fs = fs} {n = n} {s = s} le fp rest eb eq

con-here : ∀ {d as} (s : String) →
           S.fits (S.con {d} {as} s S.snil) ≡ true →
           asAtom (payVal (S.con {d} {as} s S.snil)) ≡ just (aCon s)
con-here s eq rewrite eq = refl

con-miss : ∀ {d as} (s : String) →
           S.fits (S.con {d} {as} s S.snil) ≡ false →
           asAtom (payVal (S.con {d} {as} s S.snil)) ≡ nothing
con-miss s eq rewrite eq = refl

con-val : ∀ {d as} (u : S.Val (S.dat d as)) a →
          valAtom (S.lit u) ≡ just a →
          Σ String (λ c →
            u ≡ S.con {d} {as} c S.snil × a ≡ aCon c × S.fits u ≡ true)
con-val {d} {as} (S.con s S.snil) a va =
  on (S.fits (S.con {d} {as} s S.snil)) refl va
  where
  on : (b : Bool) → S.fits (S.con {d} {as} s S.snil) ≡ b →
       asAtom (payVal (S.con {d} {as} s S.snil)) ≡ just a →
       Σ String (λ c →
         S.con {d} {as} s S.snil ≡ S.con {d} {as} c S.snil ×
         a ≡ aCon c × S.fits (S.con {d} {as} s S.snil) ≡ true)
  on true eq va =
    s , refl , sym (just-inj (trans (sym (con-here {d} {as} s eq)) va)) , eq
  on false eq va = ⊥-elim (nojust (trans (sym (con-miss {d} {as} s eq)) va))
con-val (S.con _ (S.scons _ _ _)) _ va = ⊥-elim (nojust va)

dat-yes : ∀ d as → nullCtors (S.ctorsOf d) ≡ true →
          goodGet (S.dat d as) ≡ just (tagDat (declName d))
dat-yes d as eq rewrite eq = refl

dat-no : ∀ d as → nullCtors (S.ctorsOf d) ≡ false →
         goodGet (S.dat d as) ≡ nothing
dat-no d as eq rewrite eq = refl

dat-good : ∀ d as t → goodGet (S.dat d as) ≡ just t →
           nullCtors (S.ctorsOf d) ≡ true × t ≡ tagDat (declName d)
dat-good d as t eq = on (nullCtors (S.ctorsOf d)) refl eq
  where
  on : (b : Bool) → nullCtors (S.ctorsOf d) ≡ b →
       goodGet (S.dat d as) ≡ just t →
       nullCtors (S.ctorsOf d) ≡ true × t ≡ tagDat (declName d)
  on true eb eq =
    eb , sym (just-inj (trans (sym (dat-yes d as eb)) eq))
  on false eb eq = ⊥-elim (nojust (trans (sym (dat-no d as eb)) eq))

take-arm : ∀ σ (T : S.Ty) ps W (ca0 ca : A.Carrier) R le →
           A.takeArm σ T ps (A.pay W ca0) ≡ A.aarm R ca le →
           S.applyTy σ T ≡ W × ca0 ≡ ca × A.armOfCar ca0 ps ≡ just (R , le)
take-arm σ T ps W ca0 ca R le eq with S.ty≟ (S.applyTy σ T) W
take-arm σ T ps W ca0 ca R le () | no′ _
take-arm σ T ps W ca0 ca R le eq | yes′ p with A.armOfCar ca0 ps
take-arm σ T ps W ca0 ca R le () | yes′ _ | nothing
take-arm σ T ps W ca0 ca R le eq | yes′ p | just (R′ , le′) = use eq
  where
  use : A.aarm R′ ca0 le′ ≡ A.aarm R ca le →
        S.applyTy σ T ≡ W × ca0 ≡ ca × just (R′ , le′) ≡ just (R , le)
  use refl = p , refl , refl

mget-view : ∀ Γ (T : S.Ty) x ps → Frag (go Γ (S.mget T x ps)) →
            Σ Tag (λ t → Σ (List Arm) (λ bs →
              go Γ (S.mget T x ps) ≡ smget t x bs
              × matchArms ((x , T) ∷ Γ) (ctorsTy T) ps ≡ just bs
              × FragArms bs
              × closedTy T ≡ true
              × newName x Γ ≡ true
              × goodGet T ≡ just t))
mget-view Γ T x ps fp with closedTy T
mget-view Γ T x ps () | false
mget-view Γ T x ps fp | true with goodGet T
mget-view Γ T x ps () | true | nothing
mget-view Γ T x ps fp | true | just t with newName x Γ
mget-view Γ T x ps () | true | just t | false
mget-view Γ T x ps fp | true | just t | true
  with matchArms ((x , T) ∷ Γ) (ctorsTy T) ps
mget-view Γ T x ps () | true | just t | true | nothing
mget-view Γ T x ps (fmget fas) | true | just t | true | just bs =
  t , bs , refl , refl , fas , refl , refl , refl

-- An empty pending list does not change the arm walk.
arm-env : ∀ (s : SConf) name as n slot w p → envIL s ≡ [] →
          armGo [] name as n slot ≡ just (w , p) →
          armGo (addPend [] (il s) (slotL s) (envIL s)) name as n slot ≡
            just (w , p)
arm-env s name as n slot w p z eq =
  subst (λ e → armGo e name as n slot ≡ just (w , p))
    (sym (cong (addPend [] (il s) (slotL s)) z)) eq

-- A literal constructor is the arm `findIn` selects.
arm-lit : ∀ d as (v : S.ValExpr (S.dat d as)) c ps →
          A.armOfCar (A.car (S.dat d as) v
                       (S.lit (S.con {d} {as} c S.snil))) ps ≡
            A.findIn c S.snil (S.ctorsOf d) ps
arm-lit _ _ _ _ _ = refl

lit-empty : ∀ {T} (v : S.ValExpr T) (u : S.Val T) →
           A.armOfCar (A.car T v (S.lit u)) [] ≡ nothing
lit-empty _ u = pick-empty u

take-lit : ∀ σ (T : S.Ty) W (v : S.ValExpr T) (u : S.Val T) R ca le →
           A.takeArm σ T [] (A.pay W (A.car T v (S.lit u))) ≡ A.aarm R ca le → ⊥
take-lit σ T W v u R ca le eq with S.ty≟ (S.applyTy σ T) W
take-lit _ _ _ _ _ _ _ _ () | no′ _
take-lit σ T W v u R ca le eq | yes′ _ rewrite lit-empty v u = use eq
  where
  use : A.abad ≡ A.aarm R ca le → ⊥
  use ()

nil-arm : ∀ σ (T : S.Ty) W (ca0 ca : A.Carrier) R ps le →
          ps ≡ [] →
          A.takeArm σ T ps (A.pay W ca0) ≡ A.aarm R ca le →
          Σ (A.size R ≤ 0) (λ le′ →
            A.takeArm σ T [] (A.pay W ca0) ≡ A.aarm R ca le′)
nil-arm σ T W ca0 ca R ps le eq ta rewrite eq = le , ta

mg-does : ∀ (c : A.Conf) (T : S.Ty) x ps R ca le
          (eq : A.Conf.lp c ≡ S.mget T x ps) m rest →
          A.Conf.r2l c ≡ m ∷ rest →
          A.takeArm (A.Conf.σ c) T ps m ≡ A.aarm R ca le →
          Σ (A.measure (getD c R x ca rest) < A.measure c)
            (λ lt → A.recvMgetL c T x ps eq ≡ A.does (getD c R x ca rest) lt)
mg-does c T x ps R ca le eq m rest qe ta rewrite qe | ta = _ , refl

-- A label is not an arm payload.
lab-arm : ∀ σ (T : S.Ty) ps (b : Bool) R ca le →
          A.takeArm σ T ps (A.lab b) ≡ A.aarm R ca le → ⊥
lab-arm _ _ _ _ _ _ _ ()

-- A left `mget` that `takeArm` accepts is one async step and the source
-- step into the arm it names. The binder is the constructor literal,
-- written at the slot `namesL` reserved; arms before the hit only
-- advance that slot.
step-mget : ∀ {g c s T x ps m rest R ca le} (e : Embed g c s)
            (eq : A.Conf.lp c ≡ S.mget T x ps) →
            A.Conf.r2l c ≡ m ∷ rest →
            A.takeArm (A.Conf.σ c) T ps m ≡ A.aarm R ca le →
            let d = getD c R x ca rest in
            Σ (A.measure d < A.measure c) (λ lt →
              Σ SConf (λ s′ →
                A.recvMgetL c T x ps eq ≡ A.does d lt
                × Embed g d s′
                × s ⟶ₛ s′
                × Step g (abs s) lside (abs s′)))
step-mget {g} {c} {s} {T} {x} {ps} {m} {rest} {R} {ca} {le} e eq qe tb =
  proj₁ moved , from (qrel-head qHere)
  where
  Γ = Embed.preL e
  passed = Embed.passedL e
  suf = Embed.sufL e
  lpE : left s ≡ go Γ (S.mget T x ps)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  frG : Frag (go Γ (S.mget T x ps))
  frG = subst Frag lpE (Embed.frL e)
  view = mget-view Γ T x ps frG
  t = proj₁ view
  bs = proj₁ (proj₂ view)
  geq = proj₁ (proj₂ (proj₂ view))
  meq = proj₁ (proj₂ (proj₂ (proj₂ view)))
  fas = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ view))))
  clT = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ view)))))
  gt = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ view))))))
  proc≡ : left s ≡ smget t x bs
  proc≡ = trans lpE geq
  dst = getD c R x ca rest
  moved = mg-does c T x ps R ca le eq m rest qe tb
  qHere : QRel (alpha s) (m ∷ rest) (r2l s)
  qHere = subst (λ ms → QRel (alpha s) ms (r2l s)) qe (Embed.qR e)
  Result = Σ SConf (λ s′ →
             A.recvMgetL c T x ps eq ≡ A.does dst (proj₁ moved)
             × Embed g dst s′
             × s ⟶ₛ s′
             × Step g (abs s) lside (abs s′))
  from : Σ Tok (λ tok → Σ (List Tok) (λ us →
           r2l s ≡ tok ∷ us × TokOf (alpha s) m tok × QRel (alpha s) rest us)) →
         Result
  from (_ , _ , _ , of-lab b , _) =
    ⊥-elim (lab-arm (A.Conf.σ c) T ps b R ca le tb)
  from (.(pay k) , us , qeq , of-pay {W} {B} {v} {r} {k} {a} wEq _ na va , qTail) =
    cast (trans (sym (applyTy-id (A.Conf.σ c) T clT))
                (trans (proj₁ (take-arm (A.Conf.σ c) T ps W (A.car B v r) ca R le tb))
                       wEq))
    where
    cast : T ≡ B → Result
    cast refl = form T refl gt
      where
      form : (U : S.Ty) → T ≡ U → goodGet U ≡ just t → Result
      form S.nat refl _ = ⊥-elim (noNat (proj₁ (val-lit r a va)) (proj₂ (val-lit r a va)))
        where
        noNat : (u : S.Val S.nat) → r ≡ S.lit u → ⊥
        noNat u r≡ =
          let ps≡ = proj₁ (empty-arms ((x , S.nat) ∷ Γ) ps bs meq)
              le′ , tb0 = nil-arm (A.Conf.σ c) S.nat W (A.car S.nat v r) ca
                            R ps le ps≡ tb
          in take-lit (A.Conf.σ c) S.nat W v u R ca le′
               (subst (λ e → A.takeArm (A.Conf.σ c) S.nat []
                                (A.pay W (A.car S.nat v e)) ≡ A.aarm R ca le′)
                  r≡ tb0)
      form S.bit refl _ = ⊥-elim (noBit (proj₁ (val-lit r a va)) (proj₂ (val-lit r a va)))
        where
        noBit : (u : S.Val S.bit) → r ≡ S.lit u → ⊥
        noBit u r≡ =
          let ps≡ = proj₁ (empty-arms ((x , S.bit) ∷ Γ) ps bs meq)
              le′ , tb0 = nil-arm (A.Conf.σ c) S.bit W (A.car S.bit v r) ca
                            R ps le ps≡ tb
          in take-lit (A.Conf.σ c) S.bit W v u R ca le′
               (subst (λ e → A.takeArm (A.Conf.σ c) S.bit []
                                (A.pay W (A.car S.bit v e)) ≡ A.aarm R ca le′)
                  r≡ tb0)
      form S.unit refl ()
      form (S.pair _ _) refl ()
      form (S.rec _) refl ()
      form (S.vec _ _) refl ()
      form (S.dat d as) refl gtd =
        s′ , proj₂ moved , e′ , st , gs
        where
        dg = dat-good d as t gtd
        t≡ = proj₂ dg
        u = proj₁ (val-lit r a va)
        r≡ = proj₂ (val-lit r a va)
        vaU : valAtom (S.lit u) ≡ just a
        vaU = subst (λ e → valAtom e ≡ just a) r≡ va
        cv = con-val u a vaU
        cname = proj₁ cv
        u≡ = proj₁ (proj₂ cv)
        a≡ = proj₁ (proj₂ (proj₂ cv))
        fitA : fits t a ≡ true
        fitA = subst (λ z → fits z a ≡ true) (sym t≡)
                 (subst (λ atom → fits (tagDat (declName d)) atom ≡ true)
                    (sym a≡) refl)
        conA : conOf a ≡ just cname
        conA = subst (λ atom → conOf atom ≡ just cname) (sym a≡) refl
        arm0 = proj₂ (proj₂ (take-arm (A.Conf.σ c) (S.dat d as) ps W
                              (A.car (S.dat d as) v r) ca R le tb))
        arm1 : A.armOfCar (A.car (S.dat d as) v
                            (S.lit (S.con {d} {as} cname S.snil))) ps ≡
                 just (R , le)
        arm1 = subst (λ e → A.armOfCar (A.car (S.dat d as) v e) ps ≡ just (R , le))
                 (trans r≡ (cong S.lit u≡)) arm0
        got = trans (sym (arm-lit d as v cname ps)) arm1
        Γ′ = (x , S.dat d as) ∷ Γ
        table = rows Γ′ (S.ctorsOf d) ps bs meq fas
        hit = pickHit {Γ = Γ′} {name = cname}
                {n = suc (il s)} {s = suc (slotL s)} le table got
        proc = Hit.proc hit
        skip = Hit.skip hit
        sufH = Hit.suf hit
        w = Hit.w hit
        sameP : proc ≡ go Γ′ R
        sameP = trans (Hit.same hit) (cong (go Γ′) (Hit.rid hit))
        ca≡ : A.car (S.dat d as) v (S.lit u) ≡ ca
        ca≡ = trans (sym (cong (A.car (S.dat d as) v) r≡))
                    (proj₁ (proj₂ (take-arm (A.Conf.σ c) (S.dat d as) ps W
                                   (A.car (S.dat d as) v r) ca R le tb)))
        ve≡ : A.bindV x ca (A.Conf.lv c) ≡
              (x , A.evar (S.dat d as) (S.lit u)) ∷ A.Conf.lv c
        ve≡ = cong (λ z → A.bindV x z (A.Conf.lv c)) (sym ca≡)
        mid = bnamesArms bs ++ suf
        names≡ : namesL s ≡ passed ++ (x ∷ mid)
        names≡ = trans (Embed.layL e)
                   (cong (λ ys → passed ++ ys ++ suf) (cong bnames proc≡))
        disAt : distinctN (passed ++ (x ∷ mid)) ≡ true
        disAt = subst (λ ns → distinctN ns ≡ true) names≡ (Embed.disL e)
        fr = trans (sym (fresh≡ x passed)) (dist-fresh passed x mid disAt)
        fd : findS x (namesL s) ≡ just (length passed)
        fd = trans (cong (findS x) names≡) (findS-at x passed mid fr)
        slot< : length passed < length (el s)
        slot< = subst (λ n → length passed < n)
                  (sym (trans (Embed.lenL e) (cong length names≡)))
                  (slot-lt passed x mid)
        b = length passed
        nt = nth-set b (suc k) (el s) slot<
        kept = vrel-widen (vrel-write b (el s) (suc k) (Embed.vL e))
        built = vr1 x fd ≤-refl nt na vaU kept
        slots≡ : setNth (slotL s) (suc k) (el s) ≡ setNth b (suc k) (el s)
        slots≡ = cong (λ i → setNth i (suc k) (el s)) (Embed.slot≡L e)
        vHere = subst (λ xs → VRel (alpha s) xs (namesL s) (suc b) Γ′
                                (A.bindV x ca (A.Conf.lv c)))
                 (sym slots≡)
                 (subst (λ ve → VRel (alpha s) (setNth b (suc k) (el s))
                                    (namesL s) (suc b) Γ′ ve)
                    (sym ve≡) built)
        vDone = subst (λ n → VRel (alpha s) (setNth (slotL s) (suc k) (el s))
                                   (namesL s) n Γ′
                                   (A.bindV x ca (A.Conf.lv c)))
                  (sym (len-snoc passed x)) vHere
        vShift = subst (λ n → VRel (alpha s) (setNth (slotL s) (suc k) (el s))
                                    (namesL s) n Γ′
                                    (A.bindV x ca (A.Conf.lv c)))
                   (sym (length-++ (passed ++ (x ∷ [])) {skip}))
                   (vrel-plus (length skip) vDone)
        unf = castU s (f-mget t x bs) (Embed.zPL e) proc≡ u-mget
        ago = arm-env s cname bs (suc (il s)) (suc (slotL s)) w proc
                (Embed.zIL e) (Hit.ago hit)
        st = mget-l unf qeq na fitA conA ago
        stepped = sim-fwd (Embed.hold e) st
        gs = proj₁ (proj₂ stepped)
        h′ = proj₂ (proj₂ stepped)
        s′ = getS s proc us k w
        restA = bnames proc ++ (sufH ++ suf)
        armsSplit : bnamesArms bs ++ suf ≡ skip ++ restA
        armsSplit = trans (cong (_++ suf) (Hit.split hit))
                      (trans (++-assoc skip (bnames proc ++ sufH) suf)
                         (cong (skip ++_) (++-assoc (bnames proc) sufH suf)))
        lay′ : namesL s ≡ ((passed ++ (x ∷ [])) ++ skip) ++ restA
        lay′ = trans names≡
                 (trans (cons-++ passed x (bnamesArms bs ++ suf))
                    (trans (cong ((passed ++ (x ∷ [])) ++_) armsSplit)
                       (sym (++-assoc (passed ++ (x ∷ [])) skip restA))))
        e′ : Embed g dst s′
        e′ = record
          { hold = h′
          ; al≡ = Embed.al≡ e
          ; cap≡ = Embed.cap≡ e
          ; qL = Embed.qL e
          ; qR = qTail
          ; preL = Γ′
          ; preR = Embed.preR e
          ; lp≡ = sameP
          ; rp≡ = Embed.rp≡ e
          ; zPL = refl
          ; zPR = Embed.zPR e
          ; zIL = cong (addPend [] (il s) (slotL s)) (Embed.zIL e)
          ; zIR = Embed.zIR e
          ; frL = Hit.fr hit
          ; frR = Embed.frR e
          ; vL = vShift
          ; vR = Embed.vR e
          ; passedL = (passed ++ (x ∷ [])) ++ skip
          ; sufL = sufH ++ suf
          ; passedR = Embed.passedR e
          ; sufR = Embed.sufR e
          ; layL = lay′
          ; layR = Embed.layR e
          ; slot≡L = trans (Hit.at0 hit)
                       (trans (cong (_+ length skip) (cong suc (Embed.slot≡L e)))
                          (trans (cong (_+ length skip) (sym (len-snoc passed x)))
                             (sym (length-++ (passed ++ (x ∷ [])) {skip}))))
          ; slot≡R = Embed.slot≡R e
          ; disL = Embed.disL e
          ; disR = Embed.disR e
          ; lenL = trans (length-set (slotL s) (suc k) (el s)) (Embed.lenL e)
          ; lenR = Embed.lenR e
          }


-- The right-hand mirror of `arm-env`.
arm-envR : ∀ (s : SConf) name as n slot w p → envIR s ≡ [] →
           armGo [] name as n slot ≡ just (w , p) →
           armGo (addPend [] (ir s) (slotR s) (envIR s)) name as n slot ≡
             just (w , p)
arm-envR s name as n slot w p z eq =
  subst (λ e → armGo e name as n slot ≡ just (w , p))
    (sym (cong (addPend [] (ir s) (slotR s)) z)) eq

-- `recvMgetR` does what the record update says once the arm is taken.
mg-doesR : ∀ (c : A.Conf) (T : S.Ty) x ps R ca le
           (eq : A.Conf.rp c ≡ S.mget T x ps) m rest →
           A.Conf.l2r c ≡ m ∷ rest →
           A.takeArm (A.Conf.τ c) T ps m ≡ A.aarm R ca le →
           Σ (A.measure (getDR c R x ca rest) < A.measure c)
             (λ lt → A.recvMgetR c T x ps eq ≡ A.does (getDR c R x ca rest) lt)
mg-doesR c T x ps R ca le eq m rest qe ta rewrite qe | ta = _ , refl

-- A right `mget` that `takeArm` accepts is one async step and the source
-- step into the arm it names.
step-mgetR : ∀ {g c s T x ps m rest R ca le} (e : Embed g c s)
            (eq : A.Conf.rp c ≡ S.mget T x ps) →
            A.Conf.l2r c ≡ m ∷ rest →
            A.takeArm (A.Conf.τ c) T ps m ≡ A.aarm R ca le →
            let d = getDR c R x ca rest in
            Σ (A.measure d < A.measure c) (λ lt →
              Σ SConf (λ s′ →
                A.recvMgetR c T x ps eq ≡ A.does d lt
                × Embed g d s′
                × s ⟶ₛ s′
                × Step g (abs s) rside (abs s′)))
step-mgetR {g} {c} {s} {T} {x} {ps} {m} {rest} {R} {ca} {le} e eq qe tb =
  proj₁ moved , from (qrel-head qHere)
  where
  Γ = Embed.preR e
  passed = Embed.passedR e
  suf = Embed.sufR e
  rpE : right s ≡ go Γ (S.mget T x ps)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  frG : Frag (go Γ (S.mget T x ps))
  frG = subst Frag rpE (Embed.frR e)
  view = mget-view Γ T x ps frG
  t = proj₁ view
  bs = proj₁ (proj₂ view)
  geq = proj₁ (proj₂ (proj₂ view))
  meq = proj₁ (proj₂ (proj₂ (proj₂ view)))
  fas = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ view))))
  clT = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ view)))))
  gt = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ view))))))
  proc≡ : right s ≡ smget t x bs
  proc≡ = trans rpE geq
  dst = getDR c R x ca rest
  moved = mg-doesR c T x ps R ca le eq m rest qe tb
  qHere : QRel (alpha s) (m ∷ rest) (l2r s)
  qHere = subst (λ ms → QRel (alpha s) ms (l2r s)) qe (Embed.qL e)
  Result = Σ SConf (λ s′ →
             A.recvMgetR c T x ps eq ≡ A.does dst (proj₁ moved)
             × Embed g dst s′
             × s ⟶ₛ s′
             × Step g (abs s) rside (abs s′))
  from : Σ Tok (λ tok → Σ (List Tok) (λ us →
           l2r s ≡ tok ∷ us × TokOf (alpha s) m tok × QRel (alpha s) rest us)) →
         Result
  from (_ , _ , _ , of-lab b , _) =
    ⊥-elim (lab-arm (A.Conf.τ c) T ps b R ca le tb)
  from (.(pay k) , us , qeq , of-pay {W} {B} {v} {r} {k} {a} wEq _ na va , qTail) =
    cast (trans (sym (applyTy-id (A.Conf.τ c) T clT))
                (trans (proj₁ (take-arm (A.Conf.τ c) T ps W (A.car B v r) ca R le tb))
                       wEq))
    where
    cast : T ≡ B → Result
    cast refl = form T refl gt
      where
      form : (U : S.Ty) → T ≡ U → goodGet U ≡ just t → Result
      form S.nat refl _ = ⊥-elim (noNat (proj₁ (val-lit r a va)) (proj₂ (val-lit r a va)))
        where
        noNat : (u : S.Val S.nat) → r ≡ S.lit u → ⊥
        noNat u r≡ =
          let ps≡ = proj₁ (empty-arms ((x , S.nat) ∷ Γ) ps bs meq)
              le′ , tb0 = nil-arm (A.Conf.τ c) S.nat W (A.car S.nat v r) ca
                            R ps le ps≡ tb
          in take-lit (A.Conf.τ c) S.nat W v u R ca le′
               (subst (λ e → A.takeArm (A.Conf.τ c) S.nat []
                                (A.pay W (A.car S.nat v e)) ≡ A.aarm R ca le′)
                  r≡ tb0)
      form S.bit refl _ = ⊥-elim (noBit (proj₁ (val-lit r a va)) (proj₂ (val-lit r a va)))
        where
        noBit : (u : S.Val S.bit) → r ≡ S.lit u → ⊥
        noBit u r≡ =
          let ps≡ = proj₁ (empty-arms ((x , S.bit) ∷ Γ) ps bs meq)
              le′ , tb0 = nil-arm (A.Conf.τ c) S.bit W (A.car S.bit v r) ca
                            R ps le ps≡ tb
          in take-lit (A.Conf.τ c) S.bit W v u R ca le′
               (subst (λ e → A.takeArm (A.Conf.τ c) S.bit []
                                (A.pay W (A.car S.bit v e)) ≡ A.aarm R ca le′)
                  r≡ tb0)
      form S.unit refl ()
      form (S.pair _ _) refl ()
      form (S.rec _) refl ()
      form (S.vec _ _) refl ()
      form (S.dat d as) refl gtd =
        s′ , proj₂ moved , e′ , st , gs
        where
        dg = dat-good d as t gtd
        t≡ = proj₂ dg
        u = proj₁ (val-lit r a va)
        r≡ = proj₂ (val-lit r a va)
        vaU : valAtom (S.lit u) ≡ just a
        vaU = subst (λ e → valAtom e ≡ just a) r≡ va
        cv = con-val u a vaU
        cname = proj₁ cv
        u≡ = proj₁ (proj₂ cv)
        a≡ = proj₁ (proj₂ (proj₂ cv))
        fitA : fits t a ≡ true
        fitA = subst (λ z → fits z a ≡ true) (sym t≡)
                 (subst (λ atom → fits (tagDat (declName d)) atom ≡ true)
                    (sym a≡) refl)
        conA : conOf a ≡ just cname
        conA = subst (λ atom → conOf atom ≡ just cname) (sym a≡) refl
        arm0 = proj₂ (proj₂ (take-arm (A.Conf.τ c) (S.dat d as) ps W
                              (A.car (S.dat d as) v r) ca R le tb))
        arm1 : A.armOfCar (A.car (S.dat d as) v
                            (S.lit (S.con {d} {as} cname S.snil))) ps ≡
                 just (R , le)
        arm1 = subst (λ e → A.armOfCar (A.car (S.dat d as) v e) ps ≡ just (R , le))
                 (trans r≡ (cong S.lit u≡)) arm0
        got = trans (sym (arm-lit d as v cname ps)) arm1
        Γ′ = (x , S.dat d as) ∷ Γ
        table = rows Γ′ (S.ctorsOf d) ps bs meq fas
        hit = pickHit {Γ = Γ′} {name = cname}
                {n = suc (ir s)} {s = suc (slotR s)} le table got
        proc = Hit.proc hit
        skip = Hit.skip hit
        sufH = Hit.suf hit
        w = Hit.w hit
        sameP : proc ≡ go Γ′ R
        sameP = trans (Hit.same hit) (cong (go Γ′) (Hit.rid hit))
        ca≡ : A.car (S.dat d as) v (S.lit u) ≡ ca
        ca≡ = trans (sym (cong (A.car (S.dat d as) v) r≡))
                    (proj₁ (proj₂ (take-arm (A.Conf.τ c) (S.dat d as) ps W
                                   (A.car (S.dat d as) v r) ca R le tb)))
        ve≡ : A.bindV x ca (A.Conf.rv c) ≡
              (x , A.evar (S.dat d as) (S.lit u)) ∷ A.Conf.rv c
        ve≡ = cong (λ z → A.bindV x z (A.Conf.rv c)) (sym ca≡)
        mid = bnamesArms bs ++ suf
        names≡ : namesR s ≡ passed ++ (x ∷ mid)
        names≡ = trans (Embed.layR e)
                   (cong (λ ys → passed ++ ys ++ suf) (cong bnames proc≡))
        disAt : distinctN (passed ++ (x ∷ mid)) ≡ true
        disAt = subst (λ ns → distinctN ns ≡ true) names≡ (Embed.disR e)
        fr = trans (sym (fresh≡ x passed)) (dist-fresh passed x mid disAt)
        fd : findS x (namesR s) ≡ just (length passed)
        fd = trans (cong (findS x) names≡) (findS-at x passed mid fr)
        slot< : length passed < length (er s)
        slot< = subst (λ n → length passed < n)
                  (sym (trans (Embed.lenR e) (cong length names≡)))
                  (slot-lt passed x mid)
        b = length passed
        nt = nth-set b (suc k) (er s) slot<
        kept = vrel-widen (vrel-write b (er s) (suc k) (Embed.vR e))
        built = vr1 x fd ≤-refl nt na vaU kept
        slots≡ : setNth (slotR s) (suc k) (er s) ≡ setNth b (suc k) (er s)
        slots≡ = cong (λ i → setNth i (suc k) (er s)) (Embed.slot≡R e)
        vHere = subst (λ xs → VRel (alpha s) xs (namesR s) (suc b) Γ′
                                (A.bindV x ca (A.Conf.rv c)))
                 (sym slots≡)
                 (subst (λ ve → VRel (alpha s) (setNth b (suc k) (er s))
                                    (namesR s) (suc b) Γ′ ve)
                    (sym ve≡) built)
        vDone = subst (λ n → VRel (alpha s) (setNth (slotR s) (suc k) (er s))
                                   (namesR s) n Γ′
                                   (A.bindV x ca (A.Conf.rv c)))
                  (sym (len-snoc passed x)) vHere
        vShift = subst (λ n → VRel (alpha s) (setNth (slotR s) (suc k) (er s))
                                    (namesR s) n Γ′
                                    (A.bindV x ca (A.Conf.rv c)))
                   (sym (length-++ (passed ++ (x ∷ [])) {skip}))
                   (vrel-plus (length skip) vDone)
        unf = castUR s (f-mget t x bs) (Embed.zPR e) proc≡ u-mget
        ago = arm-envR s cname bs (suc (ir s)) (suc (slotR s)) w proc
                (Embed.zIR e) (Hit.ago hit)
        st = mget-r unf qeq na fitA conA ago
        stepped = sim-fwd (Embed.hold e) st
        gs = proj₁ (proj₂ stepped)
        h′ = proj₂ (proj₂ stepped)
        s′ = getSR s proc us k w
        restA = bnames proc ++ (sufH ++ suf)
        armsSplit : bnamesArms bs ++ suf ≡ skip ++ restA
        armsSplit = trans (cong (_++ suf) (Hit.split hit))
                      (trans (++-assoc skip (bnames proc ++ sufH) suf)
                         (cong (skip ++_) (++-assoc (bnames proc) sufH suf)))
        lay′ : namesR s ≡ ((passed ++ (x ∷ [])) ++ skip) ++ restA
        lay′ = trans names≡
                 (trans (cons-++ passed x (bnamesArms bs ++ suf))
                    (trans (cong ((passed ++ (x ∷ [])) ++_) armsSplit)
                       (sym (++-assoc (passed ++ (x ∷ [])) skip restA))))
        e′ : Embed g dst s′
        e′ = record
          { hold = h′
          ; al≡ = Embed.al≡ e
          ; cap≡ = Embed.cap≡ e
          ; qL = qTail
          ; qR = Embed.qR e
          ; preL = Embed.preL e
          ; preR = Γ′
          ; lp≡ = Embed.lp≡ e
          ; rp≡ = sameP
          ; zPL = Embed.zPL e
          ; zPR = refl
          ; zIL = Embed.zIL e
          ; zIR = cong (addPend [] (ir s) (slotR s)) (Embed.zIR e)
          ; frL = Embed.frL e
          ; frR = Hit.fr hit
          ; vL = Embed.vL e
          ; vR = vShift
          ; passedL = Embed.passedL e
          ; sufL = Embed.sufL e
          ; passedR = (passed ++ (x ∷ [])) ++ skip
          ; sufR = sufH ++ suf
          ; layL = Embed.layL e
          ; layR = lay′
          ; slot≡L = Embed.slot≡L e
          ; slot≡R = trans (Hit.at0 hit)
                       (trans (cong (_+ length skip) (cong suc (Embed.slot≡R e)))
                          (trans (cong (_+ length skip) (sym (len-snoc passed x)))
                             (sym (length-++ (passed ++ (x ∷ [])) {skip}))))
          ; disL = Embed.disL e
          ; disR = Embed.disR e
          ; lenL = Embed.lenL e
          ; lenR = trans (length-set (slotR s) (suc k) (er s)) (Embed.lenR e)
          }

------------------------------------------------------------------------
-- `inj` is `go` exactly when the binder names are globally unique.
-- A repeated name is `sout`, which is outside `Frag`.
------------------------------------------------------------------------

no-sout : Frag sout → ⊥
no-sout ()

inj-ok : ∀ P → Frag (inj P) → distinctN (bnames (inj P)) ≡ true
inj-ok P fp with distinctN (bnames (go [] P)) | inspect (λ Q → distinctN (bnames (go [] Q))) P
inj-ok P fp | true | [ eq ] = eq
inj-ok P fp | false | [ eq ] = ⊥-elim (no-sout fp)

-- `reactL` of a halted process waits. Matching `refl` unfolds `onL`.
react-done : ∀ (c : A.Conf) → A.Conf.lp c ≡ S.done → A.reactL c ≡ A.waits
react-done c refl = refl

react-stop : ∀ (c : A.Conf) → A.Conf.lp c ≡ S.stop → A.reactL c ≡ A.waits
react-stop c refl = refl

-- A concrete final configuration reduces. This pins down `idle`.
idle-done : A.idle (A.init 0 S.done S.done) ≡ A.isFinal refl refl refl refl
idle-done = refl

-- `idle` is final, an orphan, or a deadlock. Matching the two
-- processes and the two queues makes it a constructor, and `StepAt`
-- has none of those.
no-idle : ∀ {c d} → A.StepAt c (A.idle c) d → ⊥
no-idle {c} {d} st =
  end (A.Conf.lp c) (A.Conf.rp c) refl refl
      (A.Conf.l2r c) (A.Conf.r2l c) refl refl st
  where
  end : (P Q : S.Proc) → A.Conf.lp c ≡ P → A.Conf.rp c ≡ Q →
        (lq rq : List A.Msg) → A.Conf.l2r c ≡ lq → A.Conf.r2l c ≡ rq →
        A.StepAt c (A.idle c) d → ⊥
  end (S.put _ _ _) _ refl _ _ _ _ _ ()
  end (S.get _ _ _) _ refl _ _ _ _ _ ()
  end (S.pick0 _) _ refl _ _ _ _ _ ()
  end (S.pick1 _) _ refl _ _ _ _ _ ()
  end (S.cover _ _) _ refl _ _ _ _ _ ()
  end (S.iget _ _ _) _ refl _ _ _ _ _ ()
  end (S.mget _ _ _) _ refl _ _ _ _ _ ()
  end S.done (S.put _ _ _) refl refl _ _ _ _ ()
  end S.done (S.get _ _ _) refl refl _ _ _ _ ()
  end S.done (S.pick0 _) refl refl _ _ _ _ ()
  end S.done (S.pick1 _) refl refl _ _ _ _ ()
  end S.done (S.cover _ _) refl refl _ _ _ _ ()
  end S.done (S.iget _ _ _) refl refl _ _ _ _ ()
  end S.done (S.mget _ _ _) refl refl _ _ _ _ ()
  end S.stop (S.put _ _ _) refl refl _ _ _ _ ()
  end S.stop (S.get _ _ _) refl refl _ _ _ _ ()
  end S.stop (S.pick0 _) refl refl _ _ _ _ ()
  end S.stop (S.pick1 _) refl refl _ _ _ _ ()
  end S.stop (S.cover _ _) refl refl _ _ _ _ ()
  end S.stop (S.iget _ _ _) refl refl _ _ _ _ ()
  end S.stop (S.mget _ _ _) refl refl _ _ _ _ ()
  end S.done S.done refl refl [] [] refl refl ()
  end S.done S.done refl refl [] (_ ∷ _) refl refl ()
  end S.done S.done refl refl (_ ∷ _) _ refl refl ()
  end S.done S.stop refl refl [] [] refl refl ()
  end S.done S.stop refl refl [] (_ ∷ _) refl refl ()
  end S.done S.stop refl refl (_ ∷ _) _ refl refl ()
  end S.stop S.done refl refl [] [] refl refl ()
  end S.stop S.done refl refl [] (_ ∷ _) refl refl ()
  end S.stop S.done refl refl (_ ∷ _) _ refl refl ()
  end S.stop S.stop refl refl [] [] refl refl ()
  end S.stop S.stop refl refl [] (_ ∷ _) refl refl ()
  end S.stop S.stop refl refl (_ ∷ _) _ refl refl ()

-- Which side the async step took. The other side is a wait or a step,
-- never a bad reception: `merge` would otherwise be `isRecv`, and
-- `StepAt` has no such constructor.
data Moved (c d : A.Conf) : Set where
  mvL : (lt : A.measure d < A.measure c) →
        A.reactL c ≡ A.does d lt →
        (A.reactR c ≡ A.waits ⊎
         Σ A.Conf (λ e → Σ (A.measure e < A.measure c)
                      (λ lt2 → A.reactR c ≡ A.does e lt2))) →
        Moved c d
  mvR : (lt : A.measure d < A.measure c) →
        A.reactR c ≡ A.does d lt →
        (A.reactL c ≡ A.waits ⊎
         Σ A.Conf (λ e → Σ (A.measure e < A.measure c)
                      (λ lt1 → A.reactL c ≡ A.does e lt1))) →
        Moved c d

split-step : ∀ {c d} (al ar : A.Act c) →
             A.reactL c ≡ al → A.reactR c ≡ ar →
             A.StepAt c (A.merge al ar) d → Moved c d
split-step (A.does d1 lt1) A.waits eql eqr A.to0 =
  mvL lt1 eql (inj₁ eqr)
split-step (A.does _ _) A.waits _ _ (A.toS ())
split-step (A.does d1 lt1) (A.does d2 lt2) eql eqr A.to0 =
  mvL lt1 eql (inj₂ (d2 , lt2 , eqr))
split-step (A.does d1 lt1) (A.does d2 lt2) eql eqr (A.toS A.here) =
  mvR lt2 eqr (inj₂ (d1 , lt1 , eql))
split-step (A.does _ _) (A.does _ _) _ _ (A.toS (A.there ()))
split-step A.waits (A.does d2 lt2) eql eqr A.to0 =
  mvR lt2 eqr (inj₁ eql)
split-step A.waits (A.does _ _) _ _ (A.toS ())
split-step (A.bads _) _ _ _ ()
split-step (A.does _ _) (A.bads _) _ _ ()
split-step A.waits (A.bads _) _ _ ()
split-step A.waits A.waits _ _ st = ⊥-elim (no-idle st)

-- `does` remembers the configuration it stepped to.
-- The configuration a `does` names. The measure proof is not an index
-- of the result, so two `does` steps with different proofs still agree.
actConf : ∀ {c} → A.Act c → Maybe A.Conf
actConf (A.does d _) = just d
actConf A.waits = nothing
actConf (A.bads _) = nothing

-- Drop the `does` proof. It mentions the measure, so it cannot be a
-- parameter of the Σ that binds that measure.
pull : ∀ {A B C D : Set} → A × B × C × D → B × C × D
pull (_ , b , c , d) = b , c , d

-- A left `does` is the source step of that process, and the graph
-- step `sim-fwd` reads off it. A wait or a bad reception is not a
-- `does`, so those branches are empty.
left-does : ∀ {g c s dst} {lt : A.measure dst < A.measure c}
            (e : Embed g c s) →
            A.reactL c ≡ A.does dst lt →
            Σ SConf (λ s′ →
              Embed g dst s′ × (s ⟶ₛ s′) × Step g (abs s) lside (abs s′))
left-does {g} {c} {s} {dst} {lt} e eq = act (A.Conf.lp c) refl eq
  where
  Goal = Σ SConf (λ s′ →
           Embed g dst s′ × (s ⟶ₛ s′) × Step g (abs s) lside (abs s′))
  -- The tail of a step lemma, after the measure proof and the `does`
  -- proof. Both mention the measure, and the successor does not.
  land : ∀ {d0} →
         Σ SConf (λ s′ →
           Embed g d0 s′ × (s ⟶ₛ s′) × Step g (abs s) lside (abs s′)) →
         d0 ≡ dst → Goal
  land (s′ , emb , st , gs) eqd =
    s′ , subst (λ z → Embed g z s′) eqd emb , st , gs
  act : (P : S.Proc) → A.Conf.lp c ≡ P → A.reactL c ≡ A.does dst lt → Goal
  act S.done refl ()
  act S.stop refl ()
  act (S.put B v P) refl eq with length (A.Conf.l2r c) <? A.Conf.cap c
  act (S.put _ _ _) refl () | no′ _
  act (S.put B v P) refl eq | yes′ le with S.sent? v
  act (S.put _ _ _) refl () | yes′ _ | no′ _
  act (S.put B (S.lit u) P) refl eq | yes′ le | yes′ _ =
    let p = proj₂ (step-put-lit e refl le)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.put B (S.var {B} x) P) refl eq | yes′ le | yes′ _ =
    let p = proj₂ (step-put-var e refl le)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.put B (S.call f as) P) refl eq | yes′ _ | yes′ _ =
    ⊥-elim (no-call (Embed.preL e) {B} f as P
              (subst Frag (Embed.lp≡ e) (Embed.frL e)))
  act (S.pick0 P) refl eq with length (A.Conf.l2r c) <? A.Conf.cap c
  act (S.pick0 _) refl () | no′ _
  act (S.pick0 P) refl eq | yes′ le =
    let p = proj₂ (step-pick0 e refl le)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.pick1 P) refl eq with length (A.Conf.l2r c) <? A.Conf.cap c
  act (S.pick1 _) refl () | no′ _
  act (S.pick1 P) refl eq | yes′ le =
    let p = proj₂ (step-pick1 e refl le)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.get T x P) refl eq with A.Conf.r2l c
  act (S.get _ _ _) refl () | []
  act (S.get T x P) refl eq | m ∷ rest
    with A.takePay (A.Conf.σ c) T m | inspect (A.takePay (A.Conf.σ c) T) m
  act (S.get _ _ _) refl () | _ ∷ _ | A.tbad | _
  act (S.get T x P) refl eq | m ∷ rest | A.tpay ca | [ te ] =
    let p = proj₂ (step-get-pay e refl refl te)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.cover P Q) refl eq with A.Conf.r2l c
  act (S.cover _ _) refl () | []
  act (S.cover P Q) refl eq | m ∷ rest
    with A.takeLab m | inspect A.takeLab m
  act (S.cover _ _) refl () | _ ∷ _ | A.lbad | _
  act (S.cover P Q) refl eq | m ∷ rest | A.l0 | [ tl ] =
    let p = proj₂ (step-cover0 e refl refl tl)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.cover P Q) refl eq | m ∷ rest | A.l1 | [ tl ] =
    let p = proj₂ (step-cover1 e refl refl tl)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.iget x P Q) refl eq with A.Conf.r2l c
  act (S.iget _ _ _) refl () | []
  act (S.iget x P Q) refl eq | m ∷ rest
    with A.takeBit m | inspect A.takeBit m
  act (S.iget _ _ _) refl () | _ ∷ _ | A.bbad | _
  act (S.iget x P Q) refl eq | m ∷ rest | A.bb0 ca | [ tb ] =
    let p = proj₂ (step-iget0 e refl refl tb)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.iget x P Q) refl eq | m ∷ rest | A.bb1 ca | [ tb ] =
    let p = proj₂ (step-iget1 e refl refl tb)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.mget T x ps) refl eq with A.Conf.r2l c
  act (S.mget _ _ _) refl () | []
  act (S.mget T x ps) refl eq | m ∷ rest
    with A.takeArm (A.Conf.σ c) T ps m | inspect (A.takeArm (A.Conf.σ c) T ps) m
  act (S.mget _ _ _) refl () | _ ∷ _ | A.abad | _
  act (S.mget T x ps) refl eq | m ∷ rest | A.aarm R ca le | [ ta ] =
    let p = proj₂ (step-mget e refl refl ta)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))

-- A right `does`, read the same way. The queue it fills is `r2l`,
-- and the queue it reads is `l2r`.
right-does : ∀ {g c s dst} {lt : A.measure dst < A.measure c}
             (e : Embed g c s) →
             A.reactR c ≡ A.does dst lt →
             Σ SConf (λ s′ →
               Embed g dst s′ × (s ⟶ₛ s′) × Step g (abs s) rside (abs s′))
right-does {g} {c} {s} {dst} {lt} e eq = act (A.Conf.rp c) refl eq
  where
  Goal = Σ SConf (λ s′ →
           Embed g dst s′ × (s ⟶ₛ s′) × Step g (abs s) rside (abs s′))
  land : ∀ {d0} →
         Σ SConf (λ s′ →
           Embed g d0 s′ × (s ⟶ₛ s′) × Step g (abs s) rside (abs s′)) →
         d0 ≡ dst → Goal
  land (s′ , emb , st , gs) eqd =
    s′ , subst (λ z → Embed g z s′) eqd emb , st , gs
  act : (P : S.Proc) → A.Conf.rp c ≡ P → A.reactR c ≡ A.does dst lt → Goal
  act S.done refl ()
  act S.stop refl ()
  act (S.put B v P) refl eq with length (A.Conf.r2l c) <? A.Conf.cap c
  act (S.put _ _ _) refl () | no′ _
  act (S.put B v P) refl eq | yes′ le with S.sent? v
  act (S.put _ _ _) refl () | yes′ _ | no′ _
  act (S.put B (S.lit u) P) refl eq | yes′ le | yes′ _ =
    let p = proj₂ (step-put-litR e refl le)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.put B (S.var {B} x) P) refl eq | yes′ le | yes′ _ =
    let p = proj₂ (step-put-varR e refl le)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.put B (S.call f as) P) refl eq | yes′ _ | yes′ _ =
    ⊥-elim (no-call (Embed.preR e) {B} f as P
              (subst Frag (Embed.rp≡ e) (Embed.frR e)))
  act (S.pick0 P) refl eq with length (A.Conf.r2l c) <? A.Conf.cap c
  act (S.pick0 _) refl () | no′ _
  act (S.pick0 P) refl eq | yes′ le =
    let p = proj₂ (step-pick0R e refl le)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.pick1 P) refl eq with length (A.Conf.r2l c) <? A.Conf.cap c
  act (S.pick1 _) refl () | no′ _
  act (S.pick1 P) refl eq | yes′ le =
    let p = proj₂ (step-pick1R e refl le)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.get T x P) refl eq with A.Conf.l2r c
  act (S.get _ _ _) refl () | []
  act (S.get T x P) refl eq | m ∷ rest
    with A.takePay (A.Conf.τ c) T m | inspect (A.takePay (A.Conf.τ c) T) m
  act (S.get _ _ _) refl () | _ ∷ _ | A.tbad | _
  act (S.get T x P) refl eq | m ∷ rest | A.tpay ca | [ te ] =
    let p = proj₂ (step-get-payR e refl refl te)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.cover P Q) refl eq with A.Conf.l2r c
  act (S.cover _ _) refl () | []
  act (S.cover P Q) refl eq | m ∷ rest
    with A.takeLab m | inspect A.takeLab m
  act (S.cover _ _) refl () | _ ∷ _ | A.lbad | _
  act (S.cover P Q) refl eq | m ∷ rest | A.l0 | [ tl ] =
    let p = proj₂ (step-cover0R e refl refl tl)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.cover P Q) refl eq | m ∷ rest | A.l1 | [ tl ] =
    let p = proj₂ (step-cover1R e refl refl tl)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.iget x P Q) refl eq with A.Conf.l2r c
  act (S.iget _ _ _) refl () | []
  act (S.iget x P Q) refl eq | m ∷ rest
    with A.takeBit m | inspect A.takeBit m
  act (S.iget _ _ _) refl () | _ ∷ _ | A.bbad | _
  act (S.iget x P Q) refl eq | m ∷ rest | A.bb0 ca | [ tb ] =
    let p = proj₂ (step-iget0R e refl refl tb)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.iget x P Q) refl eq | m ∷ rest | A.bb1 ca | [ tb ] =
    let p = proj₂ (step-iget1R e refl refl tb)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))
  act (S.mget T x ps) refl eq with A.Conf.l2r c
  act (S.mget _ _ _) refl () | []
  act (S.mget T x ps) refl eq | m ∷ rest
    with A.takeArm (A.Conf.τ c) T ps m | inspect (A.takeArm (A.Conf.τ c) T ps) m
  act (S.mget _ _ _) refl () | _ ∷ _ | A.abad | _
  act (S.mget T x ps) refl eq | m ∷ rest | A.aarm R ca le | [ ta ] =
    let p = proj₂ (step-mgetR e refl refl ta)
    in land (proj₁ p , pull (proj₂ p)) (just-inj (cong actConf eq))

-- The side `merge` actually stepped. `split-step` names it, and that
-- side's process is the source step.
inj-fwd : ∀ {g c d s} → Embed g c s → c A.⟶ d →
          Σ Who (λ w → Σ SConf (λ s′ →
            Embed g d s′ × Step g (abs s) w (abs s′)))
inj-fwd {c = c} e st with split-step (A.reactL c) (A.reactR c) refl refl st
... | mvL _ eql _ =
  let s′ , emb , _ , gs = left-does e eql
  in lside , s′ , emb , gs
... | mvR _ eqr _ =
  let s′ , emb , _ , gs = right-does e eqr
  in rside , s′ , emb , gs

-- What the right process does. The sum mentions `reactR`, so the
-- room and queue tests rewrite it. `Safe` rules out a bad reception,
-- and a left `does` is then the step `to0` names.
SideR : A.Conf → Set
SideR c = A.reactR c ≡ A.waits
        ⊎ (Σ A.Conf (λ d → Σ (A.measure d < A.measure c)
                        (λ lt → A.reactR c ≡ A.does d lt)))
        ⊎ (Σ A.Msg (λ m → A.reactR c ≡ A.bads m))

armR : (c : A.Conf) → SideR c
armR c = act (A.Conf.rp c) refl
  where
  act : (P : S.Proc) → A.Conf.rp c ≡ P → SideR c
  act S.done refl = inj₁ refl
  act S.stop refl = inj₁ refl
  act (S.put B v P) refl =
    on (length (A.Conf.r2l c) <? A.Conf.cap c) refl
    where
    on : (w : Dec (length (A.Conf.r2l c) < A.Conf.cap c)) →
         (length (A.Conf.r2l c) <? A.Conf.cap c) ≡ w → SideR c
    on (no′ _) eq rewrite eq = inj₁ refl
    on (yes′ le) eq rewrite eq with S.sent? v
    on (yes′ _) eq | no′ _ = inj₁ refl
    on (yes′ _) eq | yes′ _ = inj₂ (inj₁ (putDR c P v , _ , refl))
  act (S.pick0 P) refl = pick (length (A.Conf.r2l c) <? A.Conf.cap c) refl
    where
    pick : (w : Dec (length (A.Conf.r2l c) < A.Conf.cap c)) →
           (length (A.Conf.r2l c) <? A.Conf.cap c) ≡ w → SideR c
    pick (no′ _) eq rewrite eq = inj₁ refl
    pick (yes′ _) eq rewrite eq = inj₂ (inj₁ (labDR c P false , _ , refl))
  act (S.pick1 P) refl = pick (length (A.Conf.r2l c) <? A.Conf.cap c) refl
    where
    pick : (w : Dec (length (A.Conf.r2l c) < A.Conf.cap c)) →
           (length (A.Conf.r2l c) <? A.Conf.cap c) ≡ w → SideR c
    pick (no′ _) eq rewrite eq = inj₁ refl
    pick (yes′ _) eq rewrite eq = inj₂ (inj₁ (labDR c P true , _ , refl))
  act (S.get T x P) refl = recv (A.Conf.l2r c) refl
    where
    recv : (q : List A.Msg) → A.Conf.l2r c ≡ q → SideR c
    recv [] eq rewrite eq = inj₁ refl
    recv (m ∷ rest) eq rewrite eq with A.takePay (A.Conf.τ c) T m
    recv (m ∷ _) eq | A.tbad = inj₂ (inj₂ (m , refl))
    recv (m ∷ rest) eq | A.tpay ca =
      inj₂ (inj₁ (getDR c P x ca rest , _ , refl))
  act (S.cover P Q) refl = recv (A.Conf.l2r c) refl
    where
    recv : (q : List A.Msg) → A.Conf.l2r c ≡ q → SideR c
    recv [] eq rewrite eq = inj₁ refl
    recv (m ∷ rest) eq rewrite eq with A.takeLab m
    recv (m ∷ _) eq | A.lbad = inj₂ (inj₂ (m , refl))
    recv (m ∷ rest) eq | A.l0 = inj₂ (inj₁ (covDR c P rest , _ , refl))
    recv (m ∷ rest) eq | A.l1 = inj₂ (inj₁ (covDR c Q rest , _ , refl))
  act (S.iget x P Q) refl = recv (A.Conf.l2r c) refl
    where
    recv : (q : List A.Msg) → A.Conf.l2r c ≡ q → SideR c
    recv [] eq rewrite eq = inj₁ refl
    recv (m ∷ rest) eq rewrite eq with A.takeBit m
    recv (m ∷ _) eq | A.bbad = inj₂ (inj₂ (m , refl))
    recv (m ∷ rest) eq | A.bb0 ca =
      inj₂ (inj₁ (getDR c P x ca rest , _ , refl))
    recv (m ∷ rest) eq | A.bb1 ca =
      inj₂ (inj₁ (getDR c Q x ca rest , _ , refl))
  act (S.mget T x ps) refl = recv (A.Conf.l2r c) refl
    where
    recv : (q : List A.Msg) → A.Conf.l2r c ≡ q → SideR c
    recv [] eq rewrite eq = inj₁ refl
    recv (m ∷ rest) eq rewrite eq with A.takeArm (A.Conf.τ c) T ps m
    recv (m ∷ _) eq | A.abad = inj₂ (inj₂ (m , refl))
    recv (m ∷ rest) eq | A.aarm R ca le =
      inj₂ (inj₁ (getDR c R x ca rest , _ , refl))

commitL : ∀ {c d} {lt : A.measure d < A.measure c} →
          A.reactL c ≡ A.does d lt → A.Safe c → c A.⟶ d
commitL {c} {d} eql safe = use (armR c)
  where
  use : SideR c → c A.⟶ d
  use (inj₁ eqr) rewrite eql | eqr = A.to0
  use (inj₂ (inj₁ (_ , _ , eqr))) rewrite eql | eqr = A.to0
  use (inj₂ (inj₂ (_ , eqr))) =
    ⊥-elim (A.no-recv safe (cong₂ A.merge eql eqr))

-- A graph step on the left names the configuration `sim-fwd` reaches.
ago-same : ∀ {g c d r} → Step g c lside d →
           reactL g c ≡ AGo r → d ≡ r
ago-same (stepL eq) eqG = ago-inj (trans (sym eq) eqG)

-- `sput` unfolds only as the put it is.
open-sput : ∀ {a0 p0 a p ρ′ pend′} →
            Unfold [] [] (sput a0 p0) ρ′ pend′ (f-put a p) →
            a0 ≡ a × p0 ≡ p
open-sput u-put = refl , refl

-- A get is not a put, once `go` has chosen.
no-put-get : ∀ Γ T x P {a p ρ′ pend′} →
             Unfold [] [] (go Γ (S.get T x P)) ρ′ pend′ (f-put a p) → ⊥
no-put-get Γ T x P u with closedTy T
no-put-get Γ T x P () | false
no-put-get Γ T x P u | true with goodGet T
no-put-get Γ T x P () | true | nothing
no-put-get Γ T x P u | true | just _ with newName x Γ
no-put-get Γ T x P () | true | just _ | false
no-put-get Γ T x P () | true | just _ | true

-- The async room is the source room: the queues have the same length
-- and the capacities agree.
roomL : ∀ {g c s} (e : Embed g c s) →
        length (l2r s) < cap s →
        length (A.Conf.l2r c) < A.Conf.cap c
roomL e le = src-room le (sym (qrel-len (Embed.qL e))) (sym (Embed.cap≡ e))

roomR : ∀ {g c s} (e : Embed g c s) →
        length (r2l s) < cap s →
        length (A.Conf.r2l c) < A.Conf.cap c
roomR e le = src-room le (sym (qrel-len (Embed.qR e))) (sym (Embed.cap≡ e))

-- A put the graph accepted is a literal. An echo is `echo-l`, and a
-- call is not a fragment payload.
lit-pay : ∀ Γ {B} (v : S.ValExpr B) atom →
          asAtom (payIn Γ v) ≡ just atom →
          Σ (S.Val B) (λ u → v ≡ S.lit u)
lit-pay Γ {B} v atom eq with closedTy B
lit-pay Γ v atom () | false
lit-pay Γ (S.lit u) atom eq | true = u , refl
lit-pay Γ (S.var {B} x) atom eq | true with lookupTy x Γ
lit-pay Γ (S.var _) atom () | true | nothing
lit-pay Γ (S.var {B} _) atom eq | true | just C with S.ty≟ B C
lit-pay Γ (S.var _) atom () | true | just _ | yes′ _
lit-pay Γ (S.var _) atom () | true | just _ | no′ _
lit-pay Γ (S.call _ _) atom () | true

pout≢echo : ∀ {x} → pOut ≡ pEcho x → ⊥
pout≢echo ()

pecho-inj : ∀ {y x} → pEcho y ≡ pEcho x → y ≡ x
pecho-inj refl = refl

-- An echo put names the variable. `payIn` is `pEcho` only then.
-- The `with` is this function's own, so each clause already computes.
echo-pay : ∀ Γ {B} (v : S.ValExpr B) x →
           payIn Γ v ≡ pEcho x → v ≡ S.var {B} x
echo-pay Γ {B} v x eq with closedTy B
echo-pay Γ v x eq | false = ⊥-elim (pout≢echo eq)
echo-pay Γ (S.lit u) x eq | true = ⊥-elim (pay-echo u x eq)
echo-pay Γ (S.call _ _) x eq | true = ⊥-elim (pout≢echo eq)
echo-pay Γ (S.var {B} y) x eq | true with lookupTy y Γ
echo-pay Γ (S.var _) x eq | true | nothing = ⊥-elim (pout≢echo eq)
echo-pay Γ (S.var {B} y) x eq | true | just C with S.ty≟ B C
echo-pay Γ (S.var _) x eq | true | just _ | no′ _ = ⊥-elim (pout≢echo eq)
echo-pay Γ (S.var {B} y) x eq | true | just _ | yes′ _ =
  subst (λ z → S.var {B} y ≡ S.var {B} z) (pecho-inj eq) refl

-- The graph's `room` test is the source queue bound.
src-cap : ∀ {g s} (h : Hold g s) →
          length (l2r s) < cap g → length (l2r s) < cap s
src-cap {s = s} h le =
  subst (λ n → length (l2r s) < n) (sym (Hold.κ h)) le

-- What `inj-bwd` returns: the async step, the source it embeds, and
-- the graph configuration that step landed on.
Back : (g : Graph) (c : A.Conf) (s : SConf) (r : RConf) → Set
Back g c s r =
  Σ A.Conf (λ d → Σ SConf (λ s′ → c A.⟶ d × Embed g d s′ × abs s′ ≡ r))

-- A left put the graph accepted. The unfold is the `sput` `go` built,
-- so the send is a literal or an echo, and `Invert` reads the room
-- off that block. The right-hand source steps never appear.
backPut : ∀ {g c s r B v P} (e : Embed g c s) →
          A.Safe c →
          (eq : A.Conf.lp c ≡ S.put B v P) →
          reactL g (abs s) ≡ AGo r →
          Back g c s r
backPut {g} {c} {s} {r} {B} {v} {P} e safe eq eqG =
  use (leftSend (Embed.hold e) unf)
  where
  Γ = Embed.preL e
  lpE : left s ≡ sput (payIn Γ v) (go Γ P)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  unf : Unfold (envPL s) [] (left s) [] []
          (f-put (payIn Γ v) (go Γ P))
  unf = castU s (f-put (payIn Γ v) (go Γ P)) (Embed.zPL e) lpE u-put
  pack : (d : A.Conf) →
         Σ (A.measure d < A.measure c) (λ lt →
           Σ SConf (λ s′ →
             A.reactL c ≡ A.does d lt × Embed g d s′ ×
             (s ⟶ₛ s′) × Step g (abs s) lside (abs s′))) →
         Back g c s r
  pack d (_ , s′ , does , emb , _ , gs) =
    d , s′ , commitL does safe , emb , ago-same gs eqG
  ship : (u0 : S.Val B) → v ≡ S.lit u0 →
         length (A.Conf.l2r c) < A.Conf.cap c → Back g c s r
  ship u0 refl le =
    let whole = step-put-lit e eq le
        s′ = proj₁ (proj₂ whole)
        quad = proj₂ (proj₂ whole)
    in pack (putD c P v)
         (_ , s′ , trans (react-put c {v = v} {P = P} eq) (proj₁ quad) ,
          proj₁ (proj₂ quad) , proj₁ (proj₂ (proj₂ quad)) ,
          proj₂ (proj₂ (proj₂ quad)))
  shipE : (x : String) → v ≡ S.var {B} x →
          length (A.Conf.l2r c) < A.Conf.cap c → Back g c s r
  shipE x refl le =
    let whole = step-put-var e eq le
        s′ = proj₁ (proj₂ whole)
        quad = proj₂ (proj₂ whole)
    in pack (putD c P v)
         (_ , s′ , trans (react-put c {v = v} {P = P} eq) (proj₁ quad) ,
          proj₁ (proj₂ quad) , proj₁ (proj₂ (proj₂ quad)) ,
          proj₂ (proj₂ (proj₂ quad)))
  use : ∀ {ns} →
        Send (Hold.bsL (Embed.hold e)) ns (il s) (slotL s) (envIL s)
             [] [] (payIn Γ v) (go Γ P) →
        Back g c s r
  use (sent atom j _ aeq _ mem _ _ _) =
    let look = seenL (Embed.hold e) mem
        inv = Inv.putL g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
                atom j r look eqG
        le = roomL e (src-cap (Embed.hold e)
               (Inv.room-sound (cap g) (l2r s)
                 (proj₁ (proj₂ (proj₂ inv)))))
        u0 , veq = lit-pay Γ v atom aeq
    in ship u0 veq le
  use (echoed x sX j _ eqA _ _ mem _ _ _) =
    let look = seenL (Embed.hold e) mem
        inv = Inv.echoL g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
                sX j r look eqG
        le = roomL e (src-cap (Embed.hold e)
               (Inv.room-sound (cap g) (l2r s)
                 (proj₁ (proj₂ (proj₂ inv)))))
    in shipE x (echo-pay Γ v x eqA) le

-- One graph step, sealed as the async step `Safe` allows. The left
-- child is the one `classify` runs when the left process steps.
sealL : ∀ {g c s r} (e : Embed g c s) → A.Safe c →
        reactL g (abs s) ≡ AGo r →
        (d : A.Conf) →
        Σ (A.measure d < A.measure c) (λ lt →
          Σ SConf (λ s′ →
            A.reactL c ≡ A.does d lt × Embed g d s′ ×
            (s ⟶ₛ s′) × Step g (abs s) lside (abs s′))) →
        Back g c s r
sealL e safe eqG d (_ , s′ , does , emb , _ , gs) =
  d , s′ , commitL does safe , emb , ago-same gs eqG

-- A bad reception is not a safe configuration, whichever way the
-- other side classifies.
noRecv : ∀ {c m} → A.reactL c ≡ A.bads m → A.Safe c → ⊥
noRecv {c} eql safe = use (armR c)
  where
  use : SideR c → ⊥
  use (inj₁ eqr) = ⊥-elim (A.no-recv safe (cong₂ A.merge eql eqr))
  use (inj₂ (inj₁ (_ , _ , eqr))) =
    ⊥-elim (A.no-recv safe (cong₂ A.merge eql eqr))
  use (inj₂ (inj₂ (_ , eqr))) =
    ⊥-elim (A.no-recv safe (cong₂ A.merge eql eqr))

-- The block a left pick, get, cover, iget, or mget denotes. The link
-- puts that block at the cursor's index, and a receive's slot is the
-- cursor's slot. Naming each record is what makes the two indices meet.
pick0-at : ∀ {bs ns n s base ρ′ pend′ p} →
           Stop bs ns n s base ρ′ pend′ (f-pick0 p) →
           Σ ℕ (λ j → (n , bPick0 j) ∈ bs)
pick0-at {bs = bs} {n = n} {p = p}
    (atAct suf ρi bg _
       (p-act (d-pick0 nD sD j .p ρw wD wkD _ dest dh ds de)
              r-pick0 _ _ ρden)
       (cp-act (c-pick0 mem cvD))
       (lk-pick0 eqi eqs _ lkD)
       (hs-pick0 hsD)
       (at-pick0 _ atD)
       (en-pick0 ensD)
       (al-pick0 eqρ destAl)
       ix ss sn lf-pick0) =
  j , subst (λ i → (i , bPick0 j) ∈ bs) (sym (trans ix eqi)) mem

pick1-at : ∀ {bs ns n s base ρ′ pend′ p} →
           Stop bs ns n s base ρ′ pend′ (f-pick1 p) →
           Σ ℕ (λ j → (n , bPick1 j) ∈ bs)
pick1-at {bs = bs} {n = n} {p = p}
    (atAct suf ρi bg _
       (p-act (d-pick1 nD sD j .p ρw wD wkD _ dest dh ds de)
              r-pick1 _ _ ρden)
       (cp-act (c-pick1 mem cvD))
       (lk-pick1 eqi eqs _ lkD)
       (hs-pick1 hsD)
       (at-pick1 _ atD)
       (en-pick1 ensD)
       (al-pick1 eqρ destAl)
       ix ss sn lf-pick1) =
  j , subst (λ i → (i , bPick1 j) ∈ bs) (sym (trans ix eqi)) mem

get-at : ∀ {bs ns n s base ρ′ pend′ t x p} →
         Stop bs ns n s base ρ′ pend′ (f-get t x p) →
         Σ ℕ (λ j → (n , bGet t s j) ∈ bs)
get-at {bs = bs} {n = n} {s = s} {t = t} {x = x} {p = p}
    (atAct suf ρi bg _
       (p-act (d-get nD sD .t .x j .p ρw wD wkD _ dest dh ds de)
              r-get _ _ ρden)
       (cp-act (c-get mem cvD))
       (lk-get eqi eqs _ lkD)
       (hs-get hsD)
       (at-get _ atD)
       (en-get ensD)
       (al-get eqρ destAl)
       ix ss sn lf-get) =
  let en = trans ix eqi
      es = trans ss eqs
      memI = subst (λ i → (i , bGet t sD j) ∈ bs) (sym en) mem
  in j , subst (λ z → (n , bGet t z j) ∈ bs) (sym es) memI

cover-at : ∀ {bs ns n s base ρ′ pend′ p q} →
           Stop bs ns n s base ρ′ pend′ (f-cover p q) →
           Σ ℕ (λ i → Σ ℕ (λ j → (n , bCover i j) ∈ bs))
cover-at {bs = bs} {n = n} {p = p} {q = q}
    (atAct suf ρi bg _
       (p-act (d-cover nD sD i j .p .q ρw w1D w2D wk1D _ wk2D _
                       dp dq hp sp deP hq sq deQ)
              r-cover _ _ ρden)
       (cp-act (c-cover mem cvP cvQ))
       (lk-cover eqi eqs _ lkP lkQ)
       (hs-cover hsP hsQ)
       (at-cover _ atP atQ)
       (en-cover ensP ensQ)
       (al-cover eqρ alP alQ)
       ix ss sn lf-cover) =
  i , j , subst (λ z → (z , bCover i j) ∈ bs) (sym (trans ix eqi)) mem

iget-at : ∀ {bs ns n s base ρ′ pend′ x p q} →
          Stop bs ns n s base ρ′ pend′ (f-iget x p q) →
          Σ ℕ (λ i → Σ ℕ (λ j → (n , bIget s i j) ∈ bs))
iget-at {bs = bs} {n = n} {s = s} {x = x} {p = p} {q = q}
    (atAct suf ρi bg _
       (p-act (d-iget nD sD .x i j .p .q ρw w1D w2D wk1D _ wk2D _
                      dp dq hp sp deP hq sq deQ)
              r-iget _ _ ρden)
       (cp-act (c-iget mem cvP cvQ))
       (lk-iget eqi eqs _ lkP lkQ)
       (hs-iget hsP hsQ)
       (at-iget _ atP atQ)
       (en-iget ensP ensQ)
       (al-iget eqρ alP alQ)
       ix ss sn lf-iget) =
  let en = trans ix eqi
      es = trans ss eqs
      memI = subst (λ z → (z , bIget sD i j) ∈ bs) (sym en) mem
  in i , j , subst (λ z → (n , bIget z i j) ∈ bs) (sym es) memI

mget-at : ∀ {bs ns n s base ρ′ pend′ t x as} →
          Stop bs ns n s base ρ′ pend′ (f-mget t x as) →
          Σ (List (String × ℕ)) (λ named → (n , bMget t s named) ∈ bs)
mget-at {bs = bs} {n = n} {s = s} {t = t} {x = x} {as = as}
    (atAct suf ρi bg _
       (p-act (d-mget nD sD .t .x named .as ρw ws _ _ wkD enW _)
              r-mget _ _ ρden)
       (cp-act (c-mget mem _))
       (lk-mget eqi eqs _ _)
       (hs-mget _)
       (at-mget _ _)
       (en-mget _)
       (al-mget eqρ _)
       ix ss sn lf-mget) =
  let en = trans ix eqi
      es = trans ss eqs
      memI = subst (λ z → (z , bMget t sD named) ∈ bs) (sym en) mem
  in named , subst (λ z → (n , bMget t z named) ∈ bs) (sym es) memI

-- `reactL` on each left action. Matching the process unfolds it.
react-pick0 : (c : A.Conf) (P : S.Proc) (eq : A.Conf.lp c ≡ S.pick0 P) →
              A.reactL c ≡ A.sendLabL c false P (inj₁ eq)
react-pick0 c P refl = refl

react-pick1 : (c : A.Conf) (P : S.Proc) (eq : A.Conf.lp c ≡ S.pick1 P) →
              A.reactL c ≡ A.sendLabL c true P (inj₂ eq)
react-pick1 c P refl = refl

react-cover : (c : A.Conf) (P Q : S.Proc) (eq : A.Conf.lp c ≡ S.cover P Q) →
              A.reactL c ≡ A.recvCoverL c P Q eq
react-cover c P Q refl = refl

react-iget : (c : A.Conf) (x : String) (P Q : S.Proc)
             (eq : A.Conf.lp c ≡ S.iget x P Q) →
             A.reactL c ≡ A.recvIgetL c x P Q eq
react-iget c x P Q refl = refl

react-mget : (c : A.Conf) (T : S.Ty) (x : String) (ps : List S.PArm)
             (eq : A.Conf.lp c ≡ S.mget T x ps) →
             A.reactL c ≡ A.recvMgetL c T x ps eq
react-mget c T x ps refl = refl

-- A halted left process does not take a graph step.
stuckDone : ∀ {g c s r} (e : Embed g c s) →
            A.Conf.lp c ≡ S.done →
            reactL g (abs s) ≡ AGo r → ⊥
stuckDone {s = s} e eq eqG =
  halt-stuckL (Embed.hold e) (leftStop (Embed.hold e) unf) h-done eqG
  where
  lpE : left s ≡ sdone
  lpE = trans (Embed.lp≡ e) (cong (go (Embed.preL e)) eq)
  unf = castU s f-done (Embed.zPL e) lpE u-done

stuckStop : ∀ {g c s r} (e : Embed g c s) →
            A.Conf.lp c ≡ S.stop →
            reactL g (abs s) ≡ AGo r → ⊥
stuckStop {s = s} e eq eqG =
  halt-stuckL (Embed.hold e) (leftStop (Embed.hold e) unf) h-stop eqG
  where
  lpE : left s ≡ sstop
  lpE = trans (Embed.lp≡ e) (cong (go (Embed.preL e)) eq)
  unf = castU s f-stop (Embed.zPL e) lpE u-stop

-- A left pick the graph accepted. The block names the room.
backPick0 : ∀ {g c s r P} (e : Embed g c s) →
            A.Safe c →
            (eq : A.Conf.lp c ≡ S.pick0 P) →
            reactL g (abs s) ≡ AGo r →
            Back g c s r
backPick0 {g} {c} {s} {r} {P} e safe eq eqG =
  let Γ = Embed.preL e
      lpE : left s ≡ spick0 (go Γ P)
      lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
      unf = castU s (f-pick0 (go Γ P)) (Embed.zPL e) lpE u-pick0
      j , mem = pick0-at (leftStop (Embed.hold e) unf)
      look = seenL (Embed.hold e) mem
      inv = Inv.pick0L g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
              j r look eqG
      le = roomL e (src-cap (Embed.hold e)
             (Inv.room-sound (cap g) (l2r s) (proj₁ inv)))
      whole = step-pick0 e eq le
      s′ = proj₁ (proj₂ whole)
      quad = proj₂ (proj₂ whole)
  in sealL e safe eqG (labD c P false)
       (_ , s′ , trans (react-pick0 c P eq) (proj₁ quad) ,
        proj₁ (proj₂ quad) , proj₁ (proj₂ (proj₂ quad)) ,
        proj₂ (proj₂ (proj₂ quad)))

backPick1 : ∀ {g c s r P} (e : Embed g c s) →
            A.Safe c →
            (eq : A.Conf.lp c ≡ S.pick1 P) →
            reactL g (abs s) ≡ AGo r →
            Back g c s r
backPick1 {g} {c} {s} {r} {P} e safe eq eqG =
  let Γ = Embed.preL e
      lpE : left s ≡ spick1 (go Γ P)
      lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
      unf = castU s (f-pick1 (go Γ P)) (Embed.zPL e) lpE u-pick1
      j , mem = pick1-at (leftStop (Embed.hold e) unf)
      look = seenL (Embed.hold e) mem
      inv = Inv.pick1L g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
              j r look eqG
      le = roomL e (src-cap (Embed.hold e)
             (Inv.room-sound (cap g) (l2r s) (proj₁ inv)))
      whole = step-pick1 e eq le
      s′ = proj₁ (proj₂ whole)
      quad = proj₂ (proj₂ whole)
  in sealL e safe eqG (labD c P true)
       (_ , s′ , trans (react-pick1 c P eq) (proj₁ quad) ,
        proj₁ (proj₂ quad) , proj₁ (proj₂ (proj₂ quad)) ,
        proj₂ (proj₂ (proj₂ quad)))

-- The async queue beside a source cons.
queueR : ∀ {g c s} (e : Embed g c s) {t us} →
         r2l s ≡ t ∷ us →
         Σ A.Msg (λ m → Σ (List A.Msg) (λ ms → A.Conf.r2l c ≡ m ∷ ms))
queueR {c = c} {s = s} e eq =
  let m , ms , mq , _ , _ =
        qrel-cons (subst (λ ts → QRel (alpha s) (A.Conf.r2l c) ts) eq
                     (Embed.qR e))
                  refl
  in m , ms , mq

-- A left get the graph accepted. `takePay` either steps, or it is the
-- bad reception `Safe` excludes.
backGet : ∀ {g c s r T x P} (e : Embed g c s) →
          A.Safe c →
          (eq : A.Conf.lp c ≡ S.get T x P) →
          reactL g (abs s) ≡ AGo r →
          Back g c s r
backGet {g} {c} {s} {r} {T} {x} {P} e safe eq eqG =
  let view = get-view Γ T x P frG
      t = proj₁ view
      geq = proj₁ (proj₂ view)
      proc≡ = trans lpE geq
      body = go ((x , T) ∷ Γ) P
      unf = castU s (f-get t x body) (Embed.zPL e) proc≡ u-get
      j , mem = get-at (leftStop (Embed.hold e) unf)
      look = seenL (Embed.hold e) mem
      inv = Inv.getL g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
              t (slotL s) j r look eqG
      rest = proj₁ (proj₂ inv)
      qeq = proj₁ (proj₂ (proj₂ (proj₂ inv)))
      m , ms , mq = queueR e qeq
  in recv m ms mq
  where
  Γ = Embed.preL e
  lpE : left s ≡ go Γ (S.get T x P)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  frG = subst Frag lpE (Embed.frL e)
  recv : (m : A.Msg) (ms : List A.Msg) → A.Conf.r2l c ≡ m ∷ ms →
         Back g c s r
  recv m ms mq with A.takePay (A.Conf.σ c) T m
                  | inspect (A.takePay (A.Conf.σ c) T) m
  recv m ms mq | A.tbad | [ te ] =
    ⊥-elim (noRecv (trans (react-get c T x P eq) (isBad mq te)) safe)
    where
    -- `recvGetL` reduces only when the queue and `takePay` are
    -- rewritten in the clause whose type mentions them.
    isBad : A.Conf.r2l c ≡ m ∷ ms →
            A.takePay (A.Conf.σ c) T m ≡ A.tbad →
            A.recvGetL c T x P eq ≡ A.bads m
    isBad qe te′ rewrite qe | te′ = refl
  recv m ms mq | A.tpay ca | [ te ] =
    let whole = step-get-pay e eq mq te
        s′ = proj₁ (proj₂ whole)
        quad = proj₂ (proj₂ whole)
    in sealL e safe eqG (getD c P x ca ms)
         (_ , s′ , trans (react-get c T x P eq) (proj₁ quad) ,
          proj₁ (proj₂ quad) , proj₁ (proj₂ (proj₂ quad)) ,
          proj₂ (proj₂ (proj₂ quad)))

-- The successor `step-cover` builds, packed the way `sealL` takes it.
shipC : ∀ {g c s r P Q} (e : Embed g c s) → A.Safe c →
        (eq : A.Conf.lp c ≡ S.cover P Q) →
        reactL g (abs s) ≡ AGo r →
        (d : A.Conf) →
        Σ (A.measure d < A.measure c) (λ lt →
          Σ SConf (λ s′ →
            A.recvCoverL c P Q eq ≡ A.does d lt × Embed g d s′ ×
            (s ⟶ₛ s′) × Step g (abs s) lside (abs s′))) →
        Back g c s r
shipC {c = c} {P = P} {Q = Q} e safe eq eqG d (lt , s′ , does , emb , st , gs) =
  sealL e safe eqG d
    (lt , s′ , trans (react-cover c P Q eq) does , emb , st , gs)

-- A left cover the graph accepted. An empty queue cannot be that
-- step. `takeLab` either takes the branch or it is the reception
-- `Safe` excludes.
backCover : ∀ {g c s r P Q} (e : Embed g c s) →
            A.Safe c →
            (eq : A.Conf.lp c ≡ S.cover P Q) →
            reactL g (abs s) ≡ AGo r →
            Back g c s r
backCover {g} {c} {s} {r} {P} {Q} e safe eq eqG = recv (A.Conf.r2l c) refl
  where
  Γ = Embed.preL e
  lpE : left s ≡ scover (go Γ P) (go Γ Q)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  unf = castU s (f-cover (go Γ P) (go Γ Q)) (Embed.zPL e) lpE u-cover
  i = proj₁ (cover-at (leftStop (Embed.hold e) unf))
  j = proj₁ (proj₂ (cover-at (leftStop (Embed.hold e) unf)))
  mem = proj₂ (proj₂ (cover-at (leftStop (Embed.hold e) unf)))
  look = seenL (Embed.hold e) mem
  inv = Inv.coverL g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
          i j r look eqG
  recv : (q : List A.Msg) → A.Conf.r2l c ≡ q → Back g c s r
  recv [] qe =
    ⊥-elim (empty (proj₂ inv)
              (qrel-nil (subst (λ ms → QRel (alpha s) ms (r2l s)) qe
                           (Embed.qR e))))
    where
    empty : ∀ {rest} {A B : Set} →
            (r2l s ≡ lab false ∷ rest × A) ⊎ (r2l s ≡ lab true ∷ rest × B) →
            r2l s ≡ [] → ⊥
    empty (inj₁ (q , _)) nil = nil≢cons (trans (sym nil) q)
    empty (inj₂ (q , _)) nil = nil≢cons (trans (sym nil) q)
  recv (m ∷ ms) qe with A.takeLab m | inspect A.takeLab m
  recv (m ∷ ms) qe | A.lbad | [ tl ] =
    ⊥-elim (noRecv (trans (react-cover c P Q eq) (isBad qe tl)) safe)
    where
    isBad : A.Conf.r2l c ≡ m ∷ ms →
            A.takeLab m ≡ A.lbad →
            A.recvCoverL c P Q eq ≡ A.bads m
    isBad qe′ tl′ rewrite qe′ | tl′ = refl
  recv (m ∷ ms) qe | A.l0 | [ tl ] =
    shipC e safe eq eqG (covD c P ms) (step-cover0 e eq qe tl)
  recv (m ∷ ms) qe | A.l1 | [ tl ] =
    shipC e safe eq eqG (covD c Q ms) (step-cover1 e eq qe tl)

-- Same packing for an `iget`. The two branches share `recvIgetL`.
shipI : ∀ {g c s r x P Q} (e : Embed g c s) → A.Safe c →
        (eq : A.Conf.lp c ≡ S.iget x P Q) →
        reactL g (abs s) ≡ AGo r →
        (d : A.Conf) →
        Σ (A.measure d < A.measure c) (λ lt →
          Σ SConf (λ s′ →
            A.recvIgetL c x P Q eq ≡ A.does d lt × Embed g d s′ ×
            (s ⟶ₛ s′) × Step g (abs s) lside (abs s′))) →
        Back g c s r
shipI {c = c} {x = x} {P = P} {Q = Q} e safe eq eqG d (lt , s′ , does , emb , st , gs) =
  sealL e safe eqG d
    (lt , s′ , trans (react-iget c x P Q eq) does , emb , st , gs)

backIget : ∀ {g c s r x P Q} (e : Embed g c s) →
           A.Safe c →
           (eq : A.Conf.lp c ≡ S.iget x P Q) →
           reactL g (abs s) ≡ AGo r →
           Back g c s r
backIget {g} {c} {s} {r} {x} {P} {Q} e safe eq eqG = recv (A.Conf.r2l c) refl
  where
  Γ = Embed.preL e
  lpE : left s ≡ go Γ (S.iget x P Q)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  frG = subst Frag lpE (Embed.frL e)
  view = iget-view Γ x P Q frG
  geq = proj₁ view
  p = go ((x , S.bit) ∷ Γ) P
  q = go ((x , S.bit) ∷ Γ) Q
  proc≡ : left s ≡ siget x p q
  proc≡ = trans lpE geq
  unf = castU s (f-iget x p q) (Embed.zPL e) proc≡ u-iget
  got = iget-at (leftStop (Embed.hold e) unf)
  i = proj₁ got
  j = proj₁ (proj₂ got)
  mem = proj₂ (proj₂ got)
  look = seenL (Embed.hold e) mem
  inv = Inv.igetL g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
          (slotL s) i j r look eqG
  recv : (qs : List A.Msg) → A.Conf.r2l c ≡ qs → Back g c s r
  recv [] qe =
    ⊥-elim (empty (proj₂ (proj₂ inv))
              (qrel-nil (subst (λ ms → QRel (alpha s) ms (r2l s)) qe
                           (Embed.qR e))))
    where
    empty : ∀ {k rest} {A B : Set} →
            (r2l s ≡ pay k ∷ rest × A) ⊎ (r2l s ≡ pay k ∷ rest × B) →
            r2l s ≡ [] → ⊥
    empty (inj₁ (qe′ , _)) nil = nil≢cons (trans (sym nil) qe′)
    empty (inj₂ (qe′ , _)) nil = nil≢cons (trans (sym nil) qe′)
  recv (m ∷ ms) qe with A.takeBit m | inspect A.takeBit m
  recv (m ∷ ms) qe | A.bbad | [ tb ] =
    ⊥-elim (noRecv (trans (react-iget c x P Q eq) (isBad qe tb)) safe)
    where
    isBad : A.Conf.r2l c ≡ m ∷ ms →
            A.takeBit m ≡ A.bbad →
            A.recvIgetL c x P Q eq ≡ A.bads m
    isBad qe′ tb′ rewrite qe′ | tb′ = refl
  recv (m ∷ ms) qe | A.bb0 ca | [ tb ] =
    shipI e safe eq eqG (getD c P x ca ms) (step-iget0 e eq qe tb)
  recv (m ∷ ms) qe | A.bb1 ca | [ tb ] =
    shipI e safe eq eqG (getD c Q x ca ms) (step-iget1 e eq qe tb)

-- Same packing for an `mget`.
shipM : ∀ {g c s r T x ps} (e : Embed g c s) → A.Safe c →
        (eq : A.Conf.lp c ≡ S.mget T x ps) →
        reactL g (abs s) ≡ AGo r →
        (d : A.Conf) →
        Σ (A.measure d < A.measure c) (λ lt →
          Σ SConf (λ s′ →
            A.recvMgetL c T x ps eq ≡ A.does d lt × Embed g d s′ ×
            (s ⟶ₛ s′) × Step g (abs s) lside (abs s′))) →
        Back g c s r
shipM {c = c} {T = T} {x = x} {ps = ps} e safe eq eqG d (lt , s′ , does , emb , st , gs) =
  sealL e safe eqG d
    (lt , s′ , trans (react-mget c T x ps eq) does , emb , st , gs)

backMget : ∀ {g c s r T x ps} (e : Embed g c s) →
           A.Safe c →
           (eq : A.Conf.lp c ≡ S.mget T x ps) →
           reactL g (abs s) ≡ AGo r →
           Back g c s r
backMget {g} {c} {s} {r} {T} {x} {ps} e safe eq eqG = recv (A.Conf.r2l c) refl
  where
  Γ = Embed.preL e
  lpE : left s ≡ go Γ (S.mget T x ps)
  lpE = trans (Embed.lp≡ e) (cong (go Γ) eq)
  frG = subst Frag lpE (Embed.frL e)
  view = mget-view Γ T x ps frG
  t = proj₁ view
  bs = proj₁ (proj₂ view)
  geq = proj₁ (proj₂ (proj₂ view))
  proc≡ : left s ≡ smget t x bs
  proc≡ = trans lpE geq
  unf = castU s (f-mget t x bs) (Embed.zPL e) proc≡ u-mget
  got = mget-at (leftStop (Embed.hold e) unf)
  named = proj₁ got
  mem = proj₂ got
  look = seenL (Embed.hold e) mem
  inv = Inv.mgetL g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
          t (slotL s) named r look eqG
  packed = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ inv))))
  qSrc = proj₁ packed
  recv : (qs : List A.Msg) → A.Conf.r2l c ≡ qs → Back g c s r
  recv [] qe =
    ⊥-elim (nil≢cons
      (trans (sym (qrel-nil (subst (λ ms → QRel (alpha s) ms (r2l s)) qe
                               (Embed.qR e))))
             qSrc))
  recv (m ∷ ms) qe with A.takeArm (A.Conf.σ c) T ps m
                      | inspect (A.takeArm (A.Conf.σ c) T ps) m
  recv (m ∷ ms) qe | A.abad | [ ta ] =
    ⊥-elim (noRecv (trans (react-mget c T x ps eq) (isBad qe ta)) safe)
    where
    isBad : A.Conf.r2l c ≡ m ∷ ms →
            A.takeArm (A.Conf.σ c) T ps m ≡ A.abad →
            A.recvMgetL c T x ps eq ≡ A.bads m
    isBad qe′ ta′ rewrite qe′ | ta′ = refl
  recv (m ∷ ms) qe | A.aarm R ca le | [ ta ] =
    shipM e safe eq eqG (getD c R x ca ms) (step-mget e eq qe ta)

------------------------------------------------------------------------
-- The right side. It writes `r2l` and reads `l2r`. `commitR` takes
-- the right child: `to0` when the left waits, `toS here` when the
-- left also steps.
------------------------------------------------------------------------

castR : ∀ (s : SConf) (f : Focus) {p} → envPR s ≡ [] → right s ≡ p →
        Unfold [] [] p [] [] f →
        Unfold (envPR s) [] (right s) [] [] f
castR s f z rp u =
  subst (λ e → Unfold e [] (right s) [] [] f) (sym z)
    (subst (λ q → Unfold [] [] q [] [] f) (sym rp) u)

react-putR : (c : A.Conf) {B : S.Ty} {v : S.ValExpr B} {P : S.Proc}
             (eq : A.Conf.rp c ≡ S.put B v P) →
             A.reactR c ≡ A.sendPutR c v P eq
react-putR c refl = refl

react-pick0R : (c : A.Conf) (P : S.Proc) (eq : A.Conf.rp c ≡ S.pick0 P) →
               A.reactR c ≡ A.sendLabR c false P (inj₁ eq)
react-pick0R c P refl = refl

react-pick1R : (c : A.Conf) (P : S.Proc) (eq : A.Conf.rp c ≡ S.pick1 P) →
               A.reactR c ≡ A.sendLabR c true P (inj₂ eq)
react-pick1R c P refl = refl

react-getR : (c : A.Conf) (T : S.Ty) (x : String) (P : S.Proc)
             (eq : A.Conf.rp c ≡ S.get T x P) →
             A.reactR c ≡ A.recvGetR c T x P eq
react-getR c T x P refl = refl

react-coverR : (c : A.Conf) (P Q : S.Proc) (eq : A.Conf.rp c ≡ S.cover P Q) →
               A.reactR c ≡ A.recvCoverR c P Q eq
react-coverR c P Q refl = refl

react-igetR : (c : A.Conf) (x : String) (P Q : S.Proc)
              (eq : A.Conf.rp c ≡ S.iget x P Q) →
              A.reactR c ≡ A.recvIgetR c x P Q eq
react-igetR c x P Q refl = refl

react-mgetR : (c : A.Conf) (T : S.Ty) (x : String) (ps : List S.PArm)
              (eq : A.Conf.rp c ≡ S.mget T x ps) →
              A.reactR c ≡ A.recvMgetR c T x ps eq
react-mgetR c T x ps refl = refl

src-capR : ∀ {g s} (h : Hold g s) →
           length (r2l s) < cap g → length (r2l s) < cap s
src-capR {s = s} h le =
  subst (λ n → length (r2l s) < n) (sym (Hold.κ h)) le

ago-sameR : ∀ {g c d r} → Step g c rside d →
            reactR g c ≡ AGo r → d ≡ r
ago-sameR (stepR eq) eqG = ago-inj (trans (sym eq) eqG)

-- The left queue, read by a right receive.
queueL : ∀ {g c s} (e : Embed g c s) {t us} →
         l2r s ≡ t ∷ us →
         Σ A.Msg (λ m → Σ (List A.Msg) (λ ms → A.Conf.l2r c ≡ m ∷ ms))
queueL {c = c} {s = s} e eq =
  let m , ms , mq , _ , _ =
        qrel-cons (subst (λ ts → QRel (alpha s) (A.Conf.l2r c) ts) eq
                     (Embed.qL e))
                  refl
  in m , ms , mq

SideL : A.Conf → Set
SideL c = A.reactL c ≡ A.waits
        ⊎ (Σ A.Conf (λ d → Σ (A.measure d < A.measure c)
                        (λ lt → A.reactL c ≡ A.does d lt)))
        ⊎ (Σ A.Msg (λ m → A.reactL c ≡ A.bads m))

sideL : (c : A.Conf) → SideL c
sideL c = act (A.Conf.lp c) refl
  where
  act : (P : S.Proc) → A.Conf.lp c ≡ P → SideL c
  act S.done refl = inj₁ refl
  act S.stop refl = inj₁ refl
  act (S.put B v P) refl =
    on (length (A.Conf.l2r c) <? A.Conf.cap c) refl
    where
    on : (w : Dec (length (A.Conf.l2r c) < A.Conf.cap c)) →
         (length (A.Conf.l2r c) <? A.Conf.cap c) ≡ w → SideL c
    on (no′ _) eq rewrite eq = inj₁ refl
    on (yes′ _) eq rewrite eq with S.sent? v
    on (yes′ _) eq | no′ _ = inj₁ refl
    on (yes′ _) eq | yes′ _ = inj₂ (inj₁ (putD c P v , _ , refl))
  act (S.pick0 P) refl = pick (length (A.Conf.l2r c) <? A.Conf.cap c) refl
    where
    pick : (w : Dec (length (A.Conf.l2r c) < A.Conf.cap c)) →
           (length (A.Conf.l2r c) <? A.Conf.cap c) ≡ w → SideL c
    pick (no′ _) eq rewrite eq = inj₁ refl
    pick (yes′ _) eq rewrite eq = inj₂ (inj₁ (labD c P false , _ , refl))
  act (S.pick1 P) refl = pick (length (A.Conf.l2r c) <? A.Conf.cap c) refl
    where
    pick : (w : Dec (length (A.Conf.l2r c) < A.Conf.cap c)) →
           (length (A.Conf.l2r c) <? A.Conf.cap c) ≡ w → SideL c
    pick (no′ _) eq rewrite eq = inj₁ refl
    pick (yes′ _) eq rewrite eq = inj₂ (inj₁ (labD c P true , _ , refl))
  act (S.get T x P) refl = recv (A.Conf.r2l c) refl
    where
    recv : (q : List A.Msg) → A.Conf.r2l c ≡ q → SideL c
    recv [] eq rewrite eq = inj₁ refl
    recv (m ∷ rest) eq rewrite eq with A.takePay (A.Conf.σ c) T m
    recv (m ∷ _) eq | A.tbad = inj₂ (inj₂ (m , refl))
    recv (m ∷ rest) eq | A.tpay ca =
      inj₂ (inj₁ (getD c P x ca rest , _ , refl))
  act (S.cover P Q) refl = recv (A.Conf.r2l c) refl
    where
    recv : (q : List A.Msg) → A.Conf.r2l c ≡ q → SideL c
    recv [] eq rewrite eq = inj₁ refl
    recv (m ∷ rest) eq rewrite eq with A.takeLab m
    recv (m ∷ _) eq | A.lbad = inj₂ (inj₂ (m , refl))
    recv (m ∷ rest) eq | A.l0 = inj₂ (inj₁ (covD c P rest , _ , refl))
    recv (m ∷ rest) eq | A.l1 = inj₂ (inj₁ (covD c Q rest , _ , refl))
  act (S.iget x P Q) refl = recv (A.Conf.r2l c) refl
    where
    recv : (q : List A.Msg) → A.Conf.r2l c ≡ q → SideL c
    recv [] eq rewrite eq = inj₁ refl
    recv (m ∷ rest) eq rewrite eq with A.takeBit m
    recv (m ∷ _) eq | A.bbad = inj₂ (inj₂ (m , refl))
    recv (m ∷ rest) eq | A.bb0 ca =
      inj₂ (inj₁ (getD c P x ca rest , _ , refl))
    recv (m ∷ rest) eq | A.bb1 ca =
      inj₂ (inj₁ (getD c Q x ca rest , _ , refl))
  act (S.mget T x ps) refl = recv (A.Conf.r2l c) refl
    where
    recv : (q : List A.Msg) → A.Conf.r2l c ≡ q → SideL c
    recv [] eq rewrite eq = inj₁ refl
    recv (m ∷ rest) eq rewrite eq with A.takeArm (A.Conf.σ c) T ps m
    recv (m ∷ _) eq | A.abad = inj₂ (inj₂ (m , refl))
    recv (m ∷ rest) eq | A.aarm R ca le =
      inj₂ (inj₁ (getD c R x ca rest , _ , refl))

commitR : ∀ {c d} {lt : A.measure d < A.measure c} →
          A.reactR c ≡ A.does d lt → A.Safe c → c A.⟶ d
commitR {c} {d} eqr safe = use (sideL c)
  where
  use : SideL c → c A.⟶ d
  use (inj₁ eql) rewrite eqr | eql = A.to0
  use (inj₂ (inj₁ (_ , _ , eql))) rewrite eqr | eql = A.toS A.here
  use (inj₂ (inj₂ (_ , eql))) =
    ⊥-elim (A.no-recv safe (cong₂ A.merge eql eqr))

sealR : ∀ {g c s r} (e : Embed g c s) → A.Safe c →
        reactR g (abs s) ≡ AGo r →
        (d : A.Conf) →
        Σ (A.measure d < A.measure c) (λ lt →
          Σ SConf (λ s′ →
            A.reactR c ≡ A.does d lt × Embed g d s′ ×
            (s ⟶ₛ s′) × Step g (abs s) rside (abs s′))) →
        Back g c s r
sealR e safe eqG d (_ , s′ , does , emb , _ , gs) =
  d , s′ , commitR does safe , emb , ago-sameR gs eqG

noRecvR : ∀ {c m} → A.reactR c ≡ A.bads m → A.Safe c → ⊥
noRecvR {c} eqr safe = use (sideL c)
  where
  use : SideL c → ⊥
  use (inj₁ eql) = ⊥-elim (A.no-recv safe (cong₂ A.merge eql eqr))
  use (inj₂ (inj₁ (_ , _ , eql))) =
    ⊥-elim (A.no-recv safe (cong₂ A.merge eql eqr))
  use (inj₂ (inj₂ (_ , eql))) =
    ⊥-elim (A.no-recv safe (cong₂ A.merge eql eqr))

backPutR : ∀ {g c s r B v P} (e : Embed g c s) →
           A.Safe c →
           (eq : A.Conf.rp c ≡ S.put B v P) →
           reactR g (abs s) ≡ AGo r →
           Back g c s r
backPutR {g} {c} {s} {r} {B} {v} {P} e safe eq eqG =
  use (rightSend (Embed.hold e) unf)
  where
  Γ = Embed.preR e
  rpE : right s ≡ sput (payIn Γ v) (go Γ P)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  unf = castR s (f-put (payIn Γ v) (go Γ P)) (Embed.zPR e) rpE u-put
  pack : (d : A.Conf) →
         Σ (A.measure d < A.measure c) (λ lt →
           Σ SConf (λ s′ →
             A.reactR c ≡ A.does d lt × Embed g d s′ ×
             (s ⟶ₛ s′) × Step g (abs s) rside (abs s′))) →
         Back g c s r
  pack d (_ , s′ , does , emb , _ , gs) =
    d , s′ , commitR does safe , emb , ago-sameR gs eqG
  ship : (u0 : S.Val B) → v ≡ S.lit u0 →
         length (A.Conf.r2l c) < A.Conf.cap c → Back g c s r
  ship u0 refl le =
    let whole = step-put-litR e eq le
        s′ = proj₁ (proj₂ whole)
        quad = proj₂ (proj₂ whole)
    in pack (putDR c P v)
         (_ , s′ , trans (react-putR c {v = v} {P = P} eq) (proj₁ quad) ,
          proj₁ (proj₂ quad) , proj₁ (proj₂ (proj₂ quad)) ,
          proj₂ (proj₂ (proj₂ quad)))
  shipE : (x : String) → v ≡ S.var {B} x →
          length (A.Conf.r2l c) < A.Conf.cap c → Back g c s r
  shipE x refl le =
    let whole = step-put-varR e eq le
        s′ = proj₁ (proj₂ whole)
        quad = proj₂ (proj₂ whole)
    in pack (putDR c P v)
         (_ , s′ , trans (react-putR c {v = v} {P = P} eq) (proj₁ quad) ,
          proj₁ (proj₂ quad) , proj₁ (proj₂ (proj₂ quad)) ,
          proj₂ (proj₂ (proj₂ quad)))
  use : ∀ {ns} →
        Send (Hold.bsR (Embed.hold e)) ns (ir s) (slotR s) (envIR s)
             [] [] (payIn Γ v) (go Γ P) →
        Back g c s r
  use (sent atom j _ aeq _ mem _ _ _) =
    let look = seenR (Embed.hold e) mem
        inv = Inv.putR g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
                atom j r look eqG
        le = roomR e (src-capR (Embed.hold e)
               (Inv.room-sound (cap g) (r2l s)
                 (proj₁ (proj₂ (proj₂ inv)))))
        u0 , veq = lit-pay Γ v atom aeq
    in ship u0 veq le
  use (echoed x sX j _ eqA _ _ mem _ _ _) =
    let look = seenR (Embed.hold e) mem
        inv = Inv.echoR g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
                sX j r look eqG
        le = roomR e (src-capR (Embed.hold e)
               (Inv.room-sound (cap g) (r2l s)
                 (proj₁ (proj₂ (proj₂ inv)))))
    in shipE x (echo-pay Γ v x eqA) le

backPick0R : ∀ {g c s r P} (e : Embed g c s) →
             A.Safe c →
             (eq : A.Conf.rp c ≡ S.pick0 P) →
             reactR g (abs s) ≡ AGo r →
             Back g c s r
backPick0R {g} {c} {s} {r} {P} e safe eq eqG =
  let Γ = Embed.preR e
      rpE : right s ≡ spick0 (go Γ P)
      rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
      unf = castR s (f-pick0 (go Γ P)) (Embed.zPR e) rpE u-pick0
      j , mem = pick0-at (rightStop (Embed.hold e) unf)
      look = seenR (Embed.hold e) mem
      inv = Inv.pick0R g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
              j r look eqG
      le = roomR e (src-capR (Embed.hold e)
             (Inv.room-sound (cap g) (r2l s) (proj₁ inv)))
      whole = step-pick0R e eq le
      s′ = proj₁ (proj₂ whole)
      quad = proj₂ (proj₂ whole)
  in sealR e safe eqG (labDR c P false)
       (_ , s′ , trans (react-pick0R c P eq) (proj₁ quad) ,
        proj₁ (proj₂ quad) , proj₁ (proj₂ (proj₂ quad)) ,
        proj₂ (proj₂ (proj₂ quad)))

backPick1R : ∀ {g c s r P} (e : Embed g c s) →
             A.Safe c →
             (eq : A.Conf.rp c ≡ S.pick1 P) →
             reactR g (abs s) ≡ AGo r →
             Back g c s r
backPick1R {g} {c} {s} {r} {P} e safe eq eqG =
  let Γ = Embed.preR e
      rpE : right s ≡ spick1 (go Γ P)
      rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
      unf = castR s (f-pick1 (go Γ P)) (Embed.zPR e) rpE u-pick1
      j , mem = pick1-at (rightStop (Embed.hold e) unf)
      look = seenR (Embed.hold e) mem
      inv = Inv.pick1R g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
              j r look eqG
      le = roomR e (src-capR (Embed.hold e)
             (Inv.room-sound (cap g) (r2l s) (proj₁ inv)))
      whole = step-pick1R e eq le
      s′ = proj₁ (proj₂ whole)
      quad = proj₂ (proj₂ whole)
  in sealR e safe eqG (labDR c P true)
       (_ , s′ , trans (react-pick1R c P eq) (proj₁ quad) ,
        proj₁ (proj₂ quad) , proj₁ (proj₂ (proj₂ quad)) ,
        proj₂ (proj₂ (proj₂ quad)))

stuckDoneR : ∀ {g c s r} (e : Embed g c s) →
             A.Conf.rp c ≡ S.done →
             reactR g (abs s) ≡ AGo r → ⊥
stuckDoneR {s = s} e eq eqG =
  halt-stuckR (Embed.hold e) (rightStop (Embed.hold e) unf) h-done eqG
  where
  rpE : right s ≡ sdone
  rpE = trans (Embed.rp≡ e) (cong (go (Embed.preR e)) eq)
  unf = castR s f-done (Embed.zPR e) rpE u-done

stuckStopR : ∀ {g c s r} (e : Embed g c s) →
             A.Conf.rp c ≡ S.stop →
             reactR g (abs s) ≡ AGo r → ⊥
stuckStopR {s = s} e eq eqG =
  halt-stuckR (Embed.hold e) (rightStop (Embed.hold e) unf) h-stop eqG
  where
  rpE : right s ≡ sstop
  rpE = trans (Embed.rp≡ e) (cong (go (Embed.preR e)) eq)
  unf = castR s f-stop (Embed.zPR e) rpE u-stop

shipGR : ∀ {g c s r T x P} (e : Embed g c s) → A.Safe c →
         (eq : A.Conf.rp c ≡ S.get T x P) →
         reactR g (abs s) ≡ AGo r →
         (d : A.Conf) →
         Σ (A.measure d < A.measure c) (λ lt →
           Σ SConf (λ s′ →
             A.recvGetR c T x P eq ≡ A.does d lt × Embed g d s′ ×
             (s ⟶ₛ s′) × Step g (abs s) rside (abs s′))) →
         Back g c s r
shipGR {c = c} {T = T} {x = x} {P = P} e safe eq eqG d
    (lt , s′ , does , emb , st , gs) =
  sealR e safe eqG d
    (lt , s′ , trans (react-getR c T x P eq) does , emb , st , gs)

backGetR : ∀ {g c s r T x P} (e : Embed g c s) →
           A.Safe c →
           (eq : A.Conf.rp c ≡ S.get T x P) →
           reactR g (abs s) ≡ AGo r →
           Back g c s r
backGetR {g} {c} {s} {r} {T} {x} {P} e safe eq eqG =
  let view = get-view Γ T x P frG
      t = proj₁ view
      geq = proj₁ (proj₂ view)
      proc≡ = trans rpE geq
      body = go ((x , T) ∷ Γ) P
      unf = castR s (f-get t x body) (Embed.zPR e) proc≡ u-get
      j , mem = get-at (rightStop (Embed.hold e) unf)
      look = seenR (Embed.hold e) mem
      inv = Inv.getR g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
              t (slotR s) j r look eqG
      qeq = proj₁ (proj₂ (proj₂ (proj₂ inv)))
      m , ms , mq = queueL e qeq
  in recv m ms mq
  where
  Γ = Embed.preR e
  rpE : right s ≡ go Γ (S.get T x P)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  frG = subst Frag rpE (Embed.frR e)
  recv : (m : A.Msg) (ms : List A.Msg) → A.Conf.l2r c ≡ m ∷ ms →
         Back g c s r
  recv m ms mq with A.takePay (A.Conf.τ c) T m
                  | inspect (A.takePay (A.Conf.τ c) T) m
  recv m ms mq | A.tbad | [ te ] =
    ⊥-elim (noRecvR (trans (react-getR c T x P eq) (isBad mq te)) safe)
    where
    isBad : A.Conf.l2r c ≡ m ∷ ms →
            A.takePay (A.Conf.τ c) T m ≡ A.tbad →
            A.recvGetR c T x P eq ≡ A.bads m
    isBad qe te′ rewrite qe | te′ = refl
  recv m ms mq | A.tpay ca | [ te ] =
    shipGR e safe eq eqG (getDR c P x ca ms) (step-get-payR e eq mq te)

shipCR : ∀ {g c s r P Q} (e : Embed g c s) → A.Safe c →
         (eq : A.Conf.rp c ≡ S.cover P Q) →
         reactR g (abs s) ≡ AGo r →
         (d : A.Conf) →
         Σ (A.measure d < A.measure c) (λ lt →
           Σ SConf (λ s′ →
             A.recvCoverR c P Q eq ≡ A.does d lt × Embed g d s′ ×
             (s ⟶ₛ s′) × Step g (abs s) rside (abs s′))) →
         Back g c s r
shipCR {c = c} {P = P} {Q = Q} e safe eq eqG d (lt , s′ , does , emb , st , gs) =
  sealR e safe eqG d
    (lt , s′ , trans (react-coverR c P Q eq) does , emb , st , gs)

backCoverR : ∀ {g c s r P Q} (e : Embed g c s) →
             A.Safe c →
             (eq : A.Conf.rp c ≡ S.cover P Q) →
             reactR g (abs s) ≡ AGo r →
             Back g c s r
backCoverR {g} {c} {s} {r} {P} {Q} e safe eq eqG = recv (A.Conf.l2r c) refl
  where
  Γ = Embed.preR e
  rpE : right s ≡ scover (go Γ P) (go Γ Q)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  unf = castR s (f-cover (go Γ P) (go Γ Q)) (Embed.zPR e) rpE u-cover
  got = cover-at (rightStop (Embed.hold e) unf)
  i = proj₁ got
  j = proj₁ (proj₂ got)
  mem = proj₂ (proj₂ got)
  look = seenR (Embed.hold e) mem
  inv = Inv.coverR g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
          i j r look eqG
  recv : (q : List A.Msg) → A.Conf.l2r c ≡ q → Back g c s r
  recv [] qe =
    ⊥-elim (empty (proj₂ inv)
              (qrel-nil (subst (λ ms → QRel (alpha s) ms (l2r s)) qe
                           (Embed.qL e))))
    where
    empty : ∀ {rest} {A B : Set} →
            (l2r s ≡ lab false ∷ rest × A) ⊎ (l2r s ≡ lab true ∷ rest × B) →
            l2r s ≡ [] → ⊥
    empty (inj₁ (q , _)) nil = nil≢cons (trans (sym nil) q)
    empty (inj₂ (q , _)) nil = nil≢cons (trans (sym nil) q)
  recv (m ∷ ms) qe with A.takeLab m | inspect A.takeLab m
  recv (m ∷ ms) qe | A.lbad | [ tl ] =
    ⊥-elim (noRecvR (trans (react-coverR c P Q eq) (isBad qe tl)) safe)
    where
    isBad : A.Conf.l2r c ≡ m ∷ ms →
            A.takeLab m ≡ A.lbad →
            A.recvCoverR c P Q eq ≡ A.bads m
    isBad qe′ tl′ rewrite qe′ | tl′ = refl
  recv (m ∷ ms) qe | A.l0 | [ tl ] =
    shipCR e safe eq eqG (covDR c P ms) (step-cover0R e eq qe tl)
  recv (m ∷ ms) qe | A.l1 | [ tl ] =
    shipCR e safe eq eqG (covDR c Q ms) (step-cover1R e eq qe tl)

shipIR : ∀ {g c s r x P Q} (e : Embed g c s) → A.Safe c →
         (eq : A.Conf.rp c ≡ S.iget x P Q) →
         reactR g (abs s) ≡ AGo r →
         (d : A.Conf) →
         Σ (A.measure d < A.measure c) (λ lt →
           Σ SConf (λ s′ →
             A.recvIgetR c x P Q eq ≡ A.does d lt × Embed g d s′ ×
             (s ⟶ₛ s′) × Step g (abs s) rside (abs s′))) →
         Back g c s r
shipIR {c = c} {x = x} {P = P} {Q = Q} e safe eq eqG d
    (lt , s′ , does , emb , st , gs) =
  sealR e safe eqG d
    (lt , s′ , trans (react-igetR c x P Q eq) does , emb , st , gs)

backIgetR : ∀ {g c s r x P Q} (e : Embed g c s) →
            A.Safe c →
            (eq : A.Conf.rp c ≡ S.iget x P Q) →
            reactR g (abs s) ≡ AGo r →
            Back g c s r
backIgetR {g} {c} {s} {r} {x} {P} {Q} e safe eq eqG = recv (A.Conf.l2r c) refl
  where
  Γ = Embed.preR e
  rpE : right s ≡ go Γ (S.iget x P Q)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  frG = subst Frag rpE (Embed.frR e)
  view = iget-view Γ x P Q frG
  geq = proj₁ view
  p = go ((x , S.bit) ∷ Γ) P
  q = go ((x , S.bit) ∷ Γ) Q
  proc≡ : right s ≡ siget x p q
  proc≡ = trans rpE geq
  unf = castR s (f-iget x p q) (Embed.zPR e) proc≡ u-iget
  got = iget-at (rightStop (Embed.hold e) unf)
  i = proj₁ got
  j = proj₁ (proj₂ got)
  mem = proj₂ (proj₂ got)
  look = seenR (Embed.hold e) mem
  inv = Inv.igetR g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
          (slotR s) i j r look eqG
  recv : (qs : List A.Msg) → A.Conf.l2r c ≡ qs → Back g c s r
  recv [] qe =
    ⊥-elim (empty (proj₂ (proj₂ inv))
              (qrel-nil (subst (λ ms → QRel (alpha s) ms (l2r s)) qe
                           (Embed.qL e))))
    where
    empty : ∀ {k rest} {A B : Set} →
            (l2r s ≡ pay k ∷ rest × A) ⊎ (l2r s ≡ pay k ∷ rest × B) →
            l2r s ≡ [] → ⊥
    empty (inj₁ (qe′ , _)) nil = nil≢cons (trans (sym nil) qe′)
    empty (inj₂ (qe′ , _)) nil = nil≢cons (trans (sym nil) qe′)
  recv (m ∷ ms) qe with A.takeBit m | inspect A.takeBit m
  recv (m ∷ ms) qe | A.bbad | [ tb ] =
    ⊥-elim (noRecvR (trans (react-igetR c x P Q eq) (isBad qe tb)) safe)
    where
    isBad : A.Conf.l2r c ≡ m ∷ ms →
            A.takeBit m ≡ A.bbad →
            A.recvIgetR c x P Q eq ≡ A.bads m
    isBad qe′ tb′ rewrite qe′ | tb′ = refl
  recv (m ∷ ms) qe | A.bb0 ca | [ tb ] =
    shipIR e safe eq eqG (getDR c P x ca ms) (step-iget0R e eq qe tb)
  recv (m ∷ ms) qe | A.bb1 ca | [ tb ] =
    shipIR e safe eq eqG (getDR c Q x ca ms) (step-iget1R e eq qe tb)

shipMR : ∀ {g c s r T x ps} (e : Embed g c s) → A.Safe c →
         (eq : A.Conf.rp c ≡ S.mget T x ps) →
         reactR g (abs s) ≡ AGo r →
         (d : A.Conf) →
         Σ (A.measure d < A.measure c) (λ lt →
           Σ SConf (λ s′ →
             A.recvMgetR c T x ps eq ≡ A.does d lt × Embed g d s′ ×
             (s ⟶ₛ s′) × Step g (abs s) rside (abs s′))) →
         Back g c s r
shipMR {c = c} {T = T} {x = x} {ps = ps} e safe eq eqG d
    (lt , s′ , does , emb , st , gs) =
  sealR e safe eqG d
    (lt , s′ , trans (react-mgetR c T x ps eq) does , emb , st , gs)

backMgetR : ∀ {g c s r T x ps} (e : Embed g c s) →
            A.Safe c →
            (eq : A.Conf.rp c ≡ S.mget T x ps) →
            reactR g (abs s) ≡ AGo r →
            Back g c s r
backMgetR {g} {c} {s} {r} {T} {x} {ps} e safe eq eqG = recv (A.Conf.l2r c) refl
  where
  Γ = Embed.preR e
  rpE : right s ≡ go Γ (S.mget T x ps)
  rpE = trans (Embed.rp≡ e) (cong (go Γ) eq)
  frG = subst Frag rpE (Embed.frR e)
  view = mget-view Γ T x ps frG
  t = proj₁ view
  bs = proj₁ (proj₂ view)
  geq = proj₁ (proj₂ (proj₂ view))
  proc≡ : right s ≡ smget t x bs
  proc≡ = trans rpE geq
  unf = castR s (f-mget t x bs) (Embed.zPR e) proc≡ u-mget
  got = mget-at (rightStop (Embed.hold e) unf)
  named = proj₁ got
  mem = proj₂ got
  look = seenR (Embed.hold e) mem
  inv = Inv.mgetR g (il s) (ir s) (l2r s) (r2l s) (el s) (er s)
          t (slotR s) named r look eqG
  qSrc = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ inv)))))
  recv : (qs : List A.Msg) → A.Conf.l2r c ≡ qs → Back g c s r
  recv [] qe =
    ⊥-elim (nil≢cons
      (trans (sym (qrel-nil (subst (λ ms → QRel (alpha s) ms (l2r s)) qe
                               (Embed.qL e))))
             qSrc))
  recv (m ∷ ms) qe with A.takeArm (A.Conf.τ c) T ps m
                      | inspect (A.takeArm (A.Conf.τ c) T ps) m
  recv (m ∷ ms) qe | A.abad | [ ta ] =
    ⊥-elim (noRecvR (trans (react-mgetR c T x ps eq) (isBad qe ta)) safe)
    where
    isBad : A.Conf.l2r c ≡ m ∷ ms →
            A.takeArm (A.Conf.τ c) T ps m ≡ A.abad →
            A.recvMgetR c T x ps eq ≡ A.bads m
    isBad qe′ ta′ rewrite qe′ | ta′ = refl
  recv (m ∷ ms) qe | A.aarm R ca le | [ ta ] =
    shipMR e safe eq eqG (getDR c R x ca ms) (step-mgetR e eq qe ta)

-- A graph step that is not the stutter is the async step of the
-- process `abs` is standing on. `Safe` refuses the reception `fits`
-- cannot see.
inj-bwd : ∀ {g c s w r} → Embed g c s → A.Safe c →
          Step g (abs s) w r → w ≢ fin →
          Back g c s r
inj-bwd {g = g} {c = c} {s = s} {r = r} e safe (stepL eq) _ =
  onL (A.Conf.lp c) refl eq
  where
  onL : (P : S.Proc) → A.Conf.lp c ≡ P →
        reactL g (abs s) ≡ AGo r → Back g c s r
  onL S.done eqP eqG = ⊥-elim (stuckDone e eqP eqG)
  onL S.stop eqP eqG = ⊥-elim (stuckStop e eqP eqG)
  onL (S.put B v P) eqP eqG = backPut e safe eqP eqG
  onL (S.pick0 P) eqP eqG = backPick0 e safe eqP eqG
  onL (S.pick1 P) eqP eqG = backPick1 e safe eqP eqG
  onL (S.get T x P) eqP eqG = backGet e safe eqP eqG
  onL (S.cover P Q) eqP eqG = backCover e safe eqP eqG
  onL (S.iget x P Q) eqP eqG = backIget e safe eqP eqG
  onL (S.mget T x ps) eqP eqG = backMget e safe eqP eqG
inj-bwd {g = g} {c = c} {s = s} {r = r} e safe (stepR eq) _ =
  onR (A.Conf.rp c) refl eq
  where
  onR : (P : S.Proc) → A.Conf.rp c ≡ P →
        reactR g (abs s) ≡ AGo r → Back g c s r
  onR S.done eqP eqG = ⊥-elim (stuckDoneR e eqP eqG)
  onR S.stop eqP eqG = ⊥-elim (stuckStopR e eqP eqG)
  onR (S.put B v P) eqP eqG = backPutR e safe eqP eqG
  onR (S.pick0 P) eqP eqG = backPick0R e safe eqP eqG
  onR (S.pick1 P) eqP eqG = backPick1R e safe eqP eqG
  onR (S.get T x P) eqP eqG = backGetR e safe eqP eqG
  onR (S.cover P Q) eqP eqG = backCoverR e safe eqP eqG
  onR (S.iget x P Q) eqP eqG = backIgetR e safe eqP eqG
  onR (S.mget T x ps) eqP eqG = backMgetR e safe eqP eqG
inj-bwd e safe (finish _ _ _) neq = ⊥-elim (neq refl)

------------------------------------------------------------------------
-- A safe embedded configuration is a local graph view. An async
-- `does` is already a graph `AGo` (`left-does`, `right-does`). An
-- async `waits` is a graph `AWait`: the fragment sends, the buffer
-- is the same buffer, and a receive waits only on an empty queue.
-- `Safe` rules out a bad reception, so neither side is `ABad`.
------------------------------------------------------------------------

does-wait : ∀ {c d lt} → A.does {c} d lt ≡ A.waits → ⊥
does-wait ()

bad-wait : ∀ {c m} → A.bads {c} m ≡ A.waits → ⊥
bad-wait ()

lt-cong : ∀ {a b m n} → a ≡ b → m ≡ n → a < m → b < n
lt-cong refl refl p = p

glt-false : ∀ m n → ¬ (m < n) → glt m n ≡ false
glt-false zero zero _ = refl
glt-false zero (suc _) ¬le = ⊥-elim (¬le (s≤s z≤n))
glt-false (suc _) zero _ = refl
glt-false (suc m) (suc n) ¬le = glt-false m n (λ p → ¬le (s≤s p))

-- The async queue is full exactly when the source queue is full.
fullL : ∀ {g c s} (e : Embed g c s) →
        ¬ (length (A.Conf.l2r c) < A.Conf.cap c) →
        room (cap g) (l2r s) ≡ false
fullL {g} {c} {s} e ¬le =
  glt-false (length (l2r s)) (cap g)
    (λ p → ¬le (lt-cong (sym len) (sym capc) p))
  where
  len : length (A.Conf.l2r c) ≡ length (l2r s)
  len = qrel-len (Embed.qL e)
  capc : A.Conf.cap c ≡ cap g
  capc = trans (Embed.cap≡ e) (Hold.κ (Embed.hold e))

fullR : ∀ {g c s} (e : Embed g c s) →
        ¬ (length (A.Conf.r2l c) < A.Conf.cap c) →
        room (cap g) (r2l s) ≡ false
fullR {g} {c} {s} e ¬le =
  glt-false (length (r2l s)) (cap g)
    (λ p → ¬le (lt-cong (sym len) (sym capc) p))
  where
  len : length (A.Conf.r2l c) ≡ length (r2l s)
  len = qrel-len (Embed.qR e)
  capc : A.Conf.cap c ≡ cap g
  capc = trans (Embed.cap≡ e) (Hold.κ (Embed.hold e))

src-nil : ∀ {g c s} (e : Embed g c s) → A.Conf.r2l c ≡ [] → r2l s ≡ []
src-nil {s = s} e qe =
  qrel-nil (subst (λ ms → QRel (alpha s) ms (r2l s)) qe (Embed.qR e))

src-nilL : ∀ {g c s} (e : Embed g c s) → A.Conf.l2r c ≡ [] → l2r s ≡ []
src-nilL {s = s} e qe =
  qrel-nil (subst (λ ms → QRel (alpha s) ms (l2r s)) qe (Embed.qL e))

-- A block the cursor denotes, rewritten under `reactL` / `reactR`.
put-wait : ∀ {g s atom j k} →
           lookB (codeL g) (il s) ≡ just (bPut atom j) →
           findA atom (alpha g) ≡ just k →
           room (cap g) (l2r s) ≡ false →
           reactL g (abs s) ≡ AWait
put-wait eq fk rm rewrite eq | fk | rm = refl

put-waitR : ∀ {g s atom j k} →
            lookB (codeR g) (ir s) ≡ just (bPut atom j) →
            findA atom (alpha g) ≡ just k →
            room (cap g) (r2l s) ≡ false →
            reactR g (abs s) ≡ AWait
put-waitR eq fk rm rewrite eq | fk | rm = refl

echo-wait : ∀ {g s sX j} →
            lookB (codeL g) (il s) ≡ just (bEcho sX j) →
            room (cap g) (l2r s) ≡ false →
            reactL g (abs s) ≡ AWait
echo-wait {g} {s} {sX} eq rm = on (slotVal (el s) sX) refl
  where
  on : (mb : Maybe ℕ) → slotVal (el s) sX ≡ mb →
       reactL g (abs s) ≡ AWait
  on nothing eqS rewrite eq | eqS = refl
  on (just _) eqS rewrite eq | eqS | rm = refl

echo-waitR : ∀ {g s sX j} →
             lookB (codeR g) (ir s) ≡ just (bEcho sX j) →
             room (cap g) (r2l s) ≡ false →
             reactR g (abs s) ≡ AWait
echo-waitR {g} {s} {sX} eq rm = on (slotVal (er s) sX) refl
  where
  on : (mb : Maybe ℕ) → slotVal (er s) sX ≡ mb →
       reactR g (abs s) ≡ AWait
  on nothing eqS rewrite eq | eqS = refl
  on (just _) eqS rewrite eq | eqS | rm = refl

pick0-wait : ∀ {g s j} →
             lookB (codeL g) (il s) ≡ just (bPick0 j) →
             room (cap g) (l2r s) ≡ false →
             reactL g (abs s) ≡ AWait
pick0-wait eq rm rewrite eq | rm = refl

pick1-wait : ∀ {g s j} →
             lookB (codeL g) (il s) ≡ just (bPick1 j) →
             room (cap g) (l2r s) ≡ false →
             reactL g (abs s) ≡ AWait
pick1-wait eq rm rewrite eq | rm = refl

pick0-waitR : ∀ {g s j} →
              lookB (codeR g) (ir s) ≡ just (bPick0 j) →
              room (cap g) (r2l s) ≡ false →
              reactR g (abs s) ≡ AWait
pick0-waitR eq rm rewrite eq | rm = refl

pick1-waitR : ∀ {g s j} →
              lookB (codeR g) (ir s) ≡ just (bPick1 j) →
              room (cap g) (r2l s) ≡ false →
              reactR g (abs s) ≡ AWait
pick1-waitR eq rm rewrite eq | rm = refl

get-empty : ∀ {g s t sl j} →
            lookB (codeL g) (il s) ≡ just (bGet t sl j) →
            r2l s ≡ [] →
            reactL g (abs s) ≡ AWait
get-empty eq q rewrite eq | q = refl

cover-empty : ∀ {g s i j} →
              lookB (codeL g) (il s) ≡ just (bCover i j) →
              r2l s ≡ [] →
              reactL g (abs s) ≡ AWait
cover-empty eq q rewrite eq | q = refl

iget-empty : ∀ {g s sl i j} →
             lookB (codeL g) (il s) ≡ just (bIget sl i j) →
             r2l s ≡ [] →
             reactL g (abs s) ≡ AWait
iget-empty eq q rewrite eq | q = refl

mget-empty : ∀ {g s t sl named} →
             lookB (codeL g) (il s) ≡ just (bMget t sl named) →
             r2l s ≡ [] →
             reactL g (abs s) ≡ AWait
mget-empty eq q rewrite eq | q = refl

get-emptyR : ∀ {g s t sl j} →
             lookB (codeR g) (ir s) ≡ just (bGet t sl j) →
             l2r s ≡ [] →
             reactR g (abs s) ≡ AWait
get-emptyR eq q rewrite eq | q = refl

cover-emptyR : ∀ {g s i j} →
               lookB (codeR g) (ir s) ≡ just (bCover i j) →
               l2r s ≡ [] →
               reactR g (abs s) ≡ AWait
cover-emptyR eq q rewrite eq | q = refl

iget-emptyR : ∀ {g s sl i j} →
              lookB (codeR g) (ir s) ≡ just (bIget sl i j) →
              l2r s ≡ [] →
              reactR g (abs s) ≡ AWait
iget-emptyR eq q rewrite eq | q = refl

mget-emptyR : ∀ {g s t sl named} →
              lookB (codeR g) (ir s) ≡ just (bMget t sl named) →
              l2r s ≡ [] →
              reactR g (abs s) ≡ AWait
mget-emptyR eq q rewrite eq | q = refl

done-waitL : ∀ {g c s} (e : Embed g c s) →
             A.Conf.lp c ≡ S.done →
             reactL g (abs s) ≡ AWait
done-waitL {g} {s = s} e eq =
  Inv.haltL g (il s) (ir s) (l2r s) (r2l s) (el s) (er s) b look ht
  where
  lpE : left s ≡ sdone
  lpE = trans (Embed.lp≡ e) (cong (go (Embed.preL e)) eq)
  unf = castU s f-done (Embed.zPL e) lpE u-done
  blk = haltBlock (leftStop (Embed.hold e) unf) h-done
  b = proj₁ blk
  look = seenL (Embed.hold e) (proj₁ (proj₂ blk))
  ht = proj₂ (proj₂ blk)

stop-waitL : ∀ {g c s} (e : Embed g c s) →
             A.Conf.lp c ≡ S.stop →
             reactL g (abs s) ≡ AWait
stop-waitL {g} {s = s} e eq =
  Inv.haltL g (il s) (ir s) (l2r s) (r2l s) (el s) (er s) b look ht
  where
  lpE : left s ≡ sstop
  lpE = trans (Embed.lp≡ e) (cong (go (Embed.preL e)) eq)
  unf = castU s f-stop (Embed.zPL e) lpE u-stop
  blk = haltBlock (leftStop (Embed.hold e) unf) h-stop
  b = proj₁ blk
  look = seenL (Embed.hold e) (proj₁ (proj₂ blk))
  ht = proj₂ (proj₂ blk)

done-waitR : ∀ {g c s} (e : Embed g c s) →
             A.Conf.rp c ≡ S.done →
             reactR g (abs s) ≡ AWait
done-waitR {g} {s = s} e eq =
  Inv.haltR g (il s) (ir s) (l2r s) (r2l s) (el s) (er s) b look ht
  where
  rpE : right s ≡ sdone
  rpE = trans (Embed.rp≡ e) (cong (go (Embed.preR e)) eq)
  unf = castR s f-done (Embed.zPR e) rpE u-done
  blk = haltBlock (rightStop (Embed.hold e) unf) h-done
  b = proj₁ blk
  look = seenR (Embed.hold e) (proj₁ (proj₂ blk))
  ht = proj₂ (proj₂ blk)

stop-waitR : ∀ {g c s} (e : Embed g c s) →
             A.Conf.rp c ≡ S.stop →
             reactR g (abs s) ≡ AWait
stop-waitR {g} {s = s} e eq =
  Inv.haltR g (il s) (ir s) (l2r s) (r2l s) (el s) (er s) b look ht
  where
  rpE : right s ≡ sstop
  rpE = trans (Embed.rp≡ e) (cong (go (Embed.preR e)) eq)
  unf = castR s f-stop (Embed.zPR e) rpE u-stop
  blk = haltBlock (rightStop (Embed.hold e) unf) h-stop
  b = proj₁ blk
  look = seenR (Embed.hold e) (proj₁ (proj₂ blk))
  ht = proj₂ (proj₂ blk)

-- A left put waits only because the buffer is full. `Frag` sends.
quiet-put : ∀ {g c s B v P} (e : Embed g c s) →
            A.Conf.lp c ≡ S.put B v P →
            A.reactL c ≡ A.waits →
            reactL g (abs s) ≡ AWait
quiet-put {g} {c} {s} {B} {v} {P} e refl eqW =
  on (length (A.Conf.l2r c) <? A.Conf.cap c) refl eqW
  where
  Γ = Embed.preL e
  lpE : left s ≡ sput (payIn Γ v) (go Γ P)
  lpE = Embed.lp≡ e
  frGo = subst Frag lpE (Embed.frL e)
  unf = castU s (f-put (payIn Γ v) (go Γ P)) (Embed.zPL e) lpE u-put
  on : (w : Dec (length (A.Conf.l2r c) < A.Conf.cap c)) →
       (length (A.Conf.l2r c) <? A.Conf.cap c) ≡ w →
       A.reactL c ≡ A.waits → reactL g (abs s) ≡ AWait
  on (no′ ¬le) _ _ = use (leftSend (Embed.hold e) unf)
    where
    use : ∀ {ns} →
          Send (Hold.bsL (Embed.hold e)) ns (il s) (slotL s) (envIL s)
               [] [] (payIn Γ v) (go Γ P) →
          reactL g (abs s) ≡ AWait
    use (sent atom j _ _ _ mem _ _ _) =
      let k , fk = atom-of (Embed.hold e) (Embed.al≡ e) mem
          fkG = subst (λ al → findA atom al ≡ just k)
                  (Hold.α (Embed.hold e)) fk
      in put-wait {g} {s} {atom} {j} {k}
           (seenL (Embed.hold e) mem) fkG (fullL e ¬le)
    use (echoed _ sX j _ _ _ _ mem _ _ _) =
      echo-wait {g} {s} (seenL (Embed.hold e) mem) (fullL e ¬le)
  on (yes′ _) eqD eqw rewrite eqD with S.sent? v
  ... | no′ ¬s = ⊥-elim (¬s (image-sent Γ v P frGo))
  ... | yes′ _ = ⊥-elim (does-wait eqw)

quiet-putR : ∀ {g c s B v P} (e : Embed g c s) →
             A.Conf.rp c ≡ S.put B v P →
             A.reactR c ≡ A.waits →
             reactR g (abs s) ≡ AWait
quiet-putR {g} {c} {s} {B} {v} {P} e refl eqW =
  on (length (A.Conf.r2l c) <? A.Conf.cap c) refl eqW
  where
  Γ = Embed.preR e
  rpE : right s ≡ sput (payIn Γ v) (go Γ P)
  rpE = Embed.rp≡ e
  frGo = subst Frag rpE (Embed.frR e)
  unf = castR s (f-put (payIn Γ v) (go Γ P)) (Embed.zPR e) rpE u-put
  on : (w : Dec (length (A.Conf.r2l c) < A.Conf.cap c)) →
       (length (A.Conf.r2l c) <? A.Conf.cap c) ≡ w →
       A.reactR c ≡ A.waits → reactR g (abs s) ≡ AWait
  on (no′ ¬le) _ _ = use (rightSend (Embed.hold e) unf)
    where
    use : ∀ {ns} →
          Send (Hold.bsR (Embed.hold e)) ns (ir s) (slotR s) (envIR s)
               [] [] (payIn Γ v) (go Γ P) →
          reactR g (abs s) ≡ AWait
    use (sent atom j _ _ _ mem _ _ _) =
      let k , fk = atom-ofR (Embed.hold e) (Embed.al≡ e) mem
          fkG = subst (λ al → findA atom al ≡ just k)
                  (Hold.α (Embed.hold e)) fk
      in put-waitR {g} {s} {atom} {j} {k}
           (seenR (Embed.hold e) mem) fkG (fullR e ¬le)
    use (echoed _ sX j _ _ _ _ mem _ _ _) =
      echo-waitR {g} {s} (seenR (Embed.hold e) mem) (fullR e ¬le)
  on (yes′ _) eqD eqw rewrite eqD with S.sent? v
  ... | no′ ¬s = ⊥-elim (¬s (image-sent Γ v P frGo))
  ... | yes′ _ = ⊥-elim (does-wait eqw)

quiet-pick0 : ∀ {g c s P} (e : Embed g c s) →
              A.Conf.lp c ≡ S.pick0 P →
              A.reactL c ≡ A.waits →
              reactL g (abs s) ≡ AWait
quiet-pick0 {g} {c} {s} {P} e refl eqW =
  on (length (A.Conf.l2r c) <? A.Conf.cap c) refl eqW
  where
  Γ = Embed.preL e
  lpE : left s ≡ spick0 (go Γ P)
  lpE = Embed.lp≡ e
  unf = castU s (f-pick0 (go Γ P)) (Embed.zPL e) lpE u-pick0
  got = pick0-at (leftStop (Embed.hold e) unf)
  look = seenL (Embed.hold e) (proj₂ got)
  on : (w : Dec (length (A.Conf.l2r c) < A.Conf.cap c)) →
       (length (A.Conf.l2r c) <? A.Conf.cap c) ≡ w →
       A.reactL c ≡ A.waits → reactL g (abs s) ≡ AWait
  on (no′ ¬le) _ _ = pick0-wait {g} {s} look (fullL e ¬le)
  on (yes′ _) eqD eqw rewrite eqD = ⊥-elim (does-wait eqw)

quiet-pick1 : ∀ {g c s P} (e : Embed g c s) →
              A.Conf.lp c ≡ S.pick1 P →
              A.reactL c ≡ A.waits →
              reactL g (abs s) ≡ AWait
quiet-pick1 {g} {c} {s} {P} e refl eqW =
  on (length (A.Conf.l2r c) <? A.Conf.cap c) refl eqW
  where
  Γ = Embed.preL e
  lpE : left s ≡ spick1 (go Γ P)
  lpE = Embed.lp≡ e
  unf = castU s (f-pick1 (go Γ P)) (Embed.zPL e) lpE u-pick1
  got = pick1-at (leftStop (Embed.hold e) unf)
  look = seenL (Embed.hold e) (proj₂ got)
  on : (w : Dec (length (A.Conf.l2r c) < A.Conf.cap c)) →
       (length (A.Conf.l2r c) <? A.Conf.cap c) ≡ w →
       A.reactL c ≡ A.waits → reactL g (abs s) ≡ AWait
  on (no′ ¬le) _ _ = pick1-wait {g} {s} look (fullL e ¬le)
  on (yes′ _) eqD eqw rewrite eqD = ⊥-elim (does-wait eqw)

quiet-pick0R : ∀ {g c s P} (e : Embed g c s) →
               A.Conf.rp c ≡ S.pick0 P →
               A.reactR c ≡ A.waits →
               reactR g (abs s) ≡ AWait
quiet-pick0R {g} {c} {s} {P} e refl eqW =
  on (length (A.Conf.r2l c) <? A.Conf.cap c) refl eqW
  where
  Γ = Embed.preR e
  rpE : right s ≡ spick0 (go Γ P)
  rpE = Embed.rp≡ e
  unf = castR s (f-pick0 (go Γ P)) (Embed.zPR e) rpE u-pick0
  got = pick0-at (rightStop (Embed.hold e) unf)
  look = seenR (Embed.hold e) (proj₂ got)
  on : (w : Dec (length (A.Conf.r2l c) < A.Conf.cap c)) →
       (length (A.Conf.r2l c) <? A.Conf.cap c) ≡ w →
       A.reactR c ≡ A.waits → reactR g (abs s) ≡ AWait
  on (no′ ¬le) _ _ = pick0-waitR {g} {s} look (fullR e ¬le)
  on (yes′ _) eqD eqw rewrite eqD = ⊥-elim (does-wait eqw)

quiet-pick1R : ∀ {g c s P} (e : Embed g c s) →
               A.Conf.rp c ≡ S.pick1 P →
               A.reactR c ≡ A.waits →
               reactR g (abs s) ≡ AWait
quiet-pick1R {g} {c} {s} {P} e refl eqW =
  on (length (A.Conf.r2l c) <? A.Conf.cap c) refl eqW
  where
  Γ = Embed.preR e
  rpE : right s ≡ spick1 (go Γ P)
  rpE = Embed.rp≡ e
  unf = castR s (f-pick1 (go Γ P)) (Embed.zPR e) rpE u-pick1
  got = pick1-at (rightStop (Embed.hold e) unf)
  look = seenR (Embed.hold e) (proj₂ got)
  on : (w : Dec (length (A.Conf.r2l c) < A.Conf.cap c)) →
       (length (A.Conf.r2l c) <? A.Conf.cap c) ≡ w →
       A.reactR c ≡ A.waits → reactR g (abs s) ≡ AWait
  on (no′ ¬le) _ _ = pick1-waitR {g} {s} look (fullR e ¬le)
  on (yes′ _) eqD eqw rewrite eqD = ⊥-elim (does-wait eqw)

quiet-get : ∀ {g c s T x P} (e : Embed g c s) →
            A.Conf.lp c ≡ S.get T x P →
            A.reactL c ≡ A.waits →
            reactL g (abs s) ≡ AWait
quiet-get {g} {c} {s} {T} {x} {P} e refl eqW =
  recv (A.Conf.r2l c) refl eqW
  where
  Γ = Embed.preL e
  lpE : left s ≡ go Γ (S.get T x P)
  lpE = Embed.lp≡ e
  frG = subst Frag lpE (Embed.frL e)
  vw = get-view Γ T x P frG
  t = proj₁ vw
  geq = proj₁ (proj₂ vw)
  proc≡ = trans lpE geq
  unf = castU s (f-get t x (go ((x , T) ∷ Γ) P)) (Embed.zPL e) proc≡ u-get
  look = seenL (Embed.hold e) (proj₂ (get-at (leftStop (Embed.hold e) unf)))
  recv : (qs : List A.Msg) → A.Conf.r2l c ≡ qs →
         A.reactL c ≡ A.waits → reactL g (abs s) ≡ AWait
  recv [] qe _ = get-empty {g} {s} look (src-nil e qe)
  recv (m ∷ ms) qe eqw rewrite qe with A.takePay (A.Conf.σ c) T m
  ... | A.tbad = ⊥-elim (bad-wait eqw)
  ... | A.tpay _ = ⊥-elim (does-wait eqw)

quiet-getR : ∀ {g c s T x P} (e : Embed g c s) →
             A.Conf.rp c ≡ S.get T x P →
             A.reactR c ≡ A.waits →
             reactR g (abs s) ≡ AWait
quiet-getR {g} {c} {s} {T} {x} {P} e refl eqW =
  recv (A.Conf.l2r c) refl eqW
  where
  Γ = Embed.preR e
  rpE : right s ≡ go Γ (S.get T x P)
  rpE = Embed.rp≡ e
  frG = subst Frag rpE (Embed.frR e)
  vw = get-view Γ T x P frG
  t = proj₁ vw
  geq = proj₁ (proj₂ vw)
  proc≡ = trans rpE geq
  unf = castR s (f-get t x (go ((x , T) ∷ Γ) P)) (Embed.zPR e) proc≡ u-get
  look = seenR (Embed.hold e) (proj₂ (get-at (rightStop (Embed.hold e) unf)))
  recv : (qs : List A.Msg) → A.Conf.l2r c ≡ qs →
         A.reactR c ≡ A.waits → reactR g (abs s) ≡ AWait
  recv [] qe _ = get-emptyR {g} {s} look (src-nilL e qe)
  recv (m ∷ ms) qe eqw rewrite qe with A.takePay (A.Conf.τ c) T m
  ... | A.tbad = ⊥-elim (bad-wait eqw)
  ... | A.tpay _ = ⊥-elim (does-wait eqw)

quiet-cover : ∀ {g c s P Q} (e : Embed g c s) →
              A.Conf.lp c ≡ S.cover P Q →
              A.reactL c ≡ A.waits →
              reactL g (abs s) ≡ AWait
quiet-cover {g} {c} {s} {P} {Q} e refl eqW =
  recv (A.Conf.r2l c) refl eqW
  where
  Γ = Embed.preL e
  lpE : left s ≡ scover (go Γ P) (go Γ Q)
  lpE = Embed.lp≡ e
  unf = castU s (f-cover (go Γ P) (go Γ Q)) (Embed.zPL e) lpE u-cover
  got = cover-at (leftStop (Embed.hold e) unf)
  look = seenL (Embed.hold e) (proj₂ (proj₂ got))
  recv : (qs : List A.Msg) → A.Conf.r2l c ≡ qs →
         A.reactL c ≡ A.waits → reactL g (abs s) ≡ AWait
  recv [] qe _ = cover-empty {g} {s} look (src-nil e qe)
  recv (m ∷ ms) qe eqw rewrite qe with A.takeLab m
  ... | A.lbad = ⊥-elim (bad-wait eqw)
  ... | A.l0 = ⊥-elim (does-wait eqw)
  ... | A.l1 = ⊥-elim (does-wait eqw)

quiet-coverR : ∀ {g c s P Q} (e : Embed g c s) →
               A.Conf.rp c ≡ S.cover P Q →
               A.reactR c ≡ A.waits →
               reactR g (abs s) ≡ AWait
quiet-coverR {g} {c} {s} {P} {Q} e refl eqW =
  recv (A.Conf.l2r c) refl eqW
  where
  Γ = Embed.preR e
  rpE : right s ≡ scover (go Γ P) (go Γ Q)
  rpE = Embed.rp≡ e
  unf = castR s (f-cover (go Γ P) (go Γ Q)) (Embed.zPR e) rpE u-cover
  got = cover-at (rightStop (Embed.hold e) unf)
  look = seenR (Embed.hold e) (proj₂ (proj₂ got))
  recv : (qs : List A.Msg) → A.Conf.l2r c ≡ qs →
         A.reactR c ≡ A.waits → reactR g (abs s) ≡ AWait
  recv [] qe _ = cover-emptyR {g} {s} look (src-nilL e qe)
  recv (m ∷ ms) qe eqw rewrite qe with A.takeLab m
  ... | A.lbad = ⊥-elim (bad-wait eqw)
  ... | A.l0 = ⊥-elim (does-wait eqw)
  ... | A.l1 = ⊥-elim (does-wait eqw)

quiet-iget : ∀ {g c s x P Q} (e : Embed g c s) →
             A.Conf.lp c ≡ S.iget x P Q →
             A.reactL c ≡ A.waits →
             reactL g (abs s) ≡ AWait
quiet-iget {g} {c} {s} {x} {P} {Q} e refl eqW =
  recv (A.Conf.r2l c) refl eqW
  where
  Γ = Embed.preL e
  lpE : left s ≡ go Γ (S.iget x P Q)
  lpE = Embed.lp≡ e
  frG = subst Frag lpE (Embed.frL e)
  geq = proj₁ (iget-view Γ x P Q frG)
  proc≡ = trans lpE geq
  p = go ((x , S.bit) ∷ Γ) P
  q = go ((x , S.bit) ∷ Γ) Q
  unf = castU s (f-iget x p q) (Embed.zPL e) proc≡ u-iget
  got = iget-at (leftStop (Embed.hold e) unf)
  look = seenL (Embed.hold e) (proj₂ (proj₂ got))
  recv : (qs : List A.Msg) → A.Conf.r2l c ≡ qs →
         A.reactL c ≡ A.waits → reactL g (abs s) ≡ AWait
  recv [] qe _ = iget-empty {g} {s} look (src-nil e qe)
  recv (m ∷ ms) qe eqw rewrite qe with A.takeBit m
  ... | A.bbad = ⊥-elim (bad-wait eqw)
  ... | A.bb0 _ = ⊥-elim (does-wait eqw)
  ... | A.bb1 _ = ⊥-elim (does-wait eqw)

quiet-igetR : ∀ {g c s x P Q} (e : Embed g c s) →
              A.Conf.rp c ≡ S.iget x P Q →
              A.reactR c ≡ A.waits →
              reactR g (abs s) ≡ AWait
quiet-igetR {g} {c} {s} {x} {P} {Q} e refl eqW =
  recv (A.Conf.l2r c) refl eqW
  where
  Γ = Embed.preR e
  rpE : right s ≡ go Γ (S.iget x P Q)
  rpE = Embed.rp≡ e
  frG = subst Frag rpE (Embed.frR e)
  geq = proj₁ (iget-view Γ x P Q frG)
  proc≡ = trans rpE geq
  p = go ((x , S.bit) ∷ Γ) P
  q = go ((x , S.bit) ∷ Γ) Q
  unf = castR s (f-iget x p q) (Embed.zPR e) proc≡ u-iget
  got = iget-at (rightStop (Embed.hold e) unf)
  look = seenR (Embed.hold e) (proj₂ (proj₂ got))
  recv : (qs : List A.Msg) → A.Conf.l2r c ≡ qs →
         A.reactR c ≡ A.waits → reactR g (abs s) ≡ AWait
  recv [] qe _ = iget-emptyR {g} {s} look (src-nilL e qe)
  recv (m ∷ ms) qe eqw rewrite qe with A.takeBit m
  ... | A.bbad = ⊥-elim (bad-wait eqw)
  ... | A.bb0 _ = ⊥-elim (does-wait eqw)
  ... | A.bb1 _ = ⊥-elim (does-wait eqw)

quiet-mget : ∀ {g c s T x ps} (e : Embed g c s) →
             A.Conf.lp c ≡ S.mget T x ps →
             A.reactL c ≡ A.waits →
             reactL g (abs s) ≡ AWait
quiet-mget {g} {c} {s} {T} {x} {ps} e refl eqW =
  recv (A.Conf.r2l c) refl eqW
  where
  Γ = Embed.preL e
  lpE : left s ≡ go Γ (S.mget T x ps)
  lpE = Embed.lp≡ e
  frG = subst Frag lpE (Embed.frL e)
  vw = mget-view Γ T x ps frG
  t = proj₁ vw
  bs = proj₁ (proj₂ vw)
  geq = proj₁ (proj₂ (proj₂ vw))
  proc≡ = trans lpE geq
  unf = castU s (f-mget t x bs) (Embed.zPL e) proc≡ u-mget
  got = mget-at (leftStop (Embed.hold e) unf)
  look = seenL (Embed.hold e) (proj₂ got)
  recv : (qs : List A.Msg) → A.Conf.r2l c ≡ qs →
         A.reactL c ≡ A.waits → reactL g (abs s) ≡ AWait
  recv [] qe _ = mget-empty {g} {s} look (src-nil e qe)
  recv (m ∷ ms) qe eqw rewrite qe with A.takeArm (A.Conf.σ c) T ps m
  ... | A.abad = ⊥-elim (bad-wait eqw)
  ... | A.aarm _ _ _ = ⊥-elim (does-wait eqw)

quiet-mgetR : ∀ {g c s T x ps} (e : Embed g c s) →
              A.Conf.rp c ≡ S.mget T x ps →
              A.reactR c ≡ A.waits →
              reactR g (abs s) ≡ AWait
quiet-mgetR {g} {c} {s} {T} {x} {ps} e refl eqW =
  recv (A.Conf.l2r c) refl eqW
  where
  Γ = Embed.preR e
  rpE : right s ≡ go Γ (S.mget T x ps)
  rpE = Embed.rp≡ e
  frG = subst Frag rpE (Embed.frR e)
  vw = mget-view Γ T x ps frG
  t = proj₁ vw
  bs = proj₁ (proj₂ vw)
  geq = proj₁ (proj₂ (proj₂ vw))
  proc≡ = trans rpE geq
  unf = castR s (f-mget t x bs) (Embed.zPR e) proc≡ u-mget
  got = mget-at (rightStop (Embed.hold e) unf)
  look = seenR (Embed.hold e) (proj₂ got)
  recv : (qs : List A.Msg) → A.Conf.l2r c ≡ qs →
         A.reactR c ≡ A.waits → reactR g (abs s) ≡ AWait
  recv [] qe _ = mget-emptyR {g} {s} look (src-nilL e qe)
  recv (m ∷ ms) qe eqw rewrite qe with A.takeArm (A.Conf.τ c) T ps m
  ... | A.abad = ⊥-elim (bad-wait eqw)
  ... | A.aarm _ _ _ = ⊥-elim (does-wait eqw)

-- Whatever the left process is, a wait there is a graph wait.
quietL : ∀ {g c s} (e : Embed g c s) →
         A.reactL c ≡ A.waits → reactL g (abs s) ≡ AWait
quietL {g} {c} {s} e eqW = act (A.Conf.lp c) refl eqW
  where
  act : (P : S.Proc) → A.Conf.lp c ≡ P →
        A.reactL c ≡ A.waits → reactL g (abs s) ≡ AWait
  act S.done refl _ = done-waitL e refl
  act S.stop refl _ = stop-waitL e refl
  act (S.put B v P) refl eqw = quiet-put e refl eqw
  act (S.pick0 P) refl eqw = quiet-pick0 e refl eqw
  act (S.pick1 P) refl eqw = quiet-pick1 e refl eqw
  act (S.get T x P) refl eqw = quiet-get e refl eqw
  act (S.cover P Q) refl eqw = quiet-cover e refl eqw
  act (S.iget x P Q) refl eqw = quiet-iget e refl eqw
  act (S.mget T x ps) refl eqw = quiet-mget e refl eqw

quietR : ∀ {g c s} (e : Embed g c s) →
         A.reactR c ≡ A.waits → reactR g (abs s) ≡ AWait
quietR {g} {c} {s} e eqW = act (A.Conf.rp c) refl eqW
  where
  act : (P : S.Proc) → A.Conf.rp c ≡ P →
        A.reactR c ≡ A.waits → reactR g (abs s) ≡ AWait
  act S.done refl _ = done-waitR e refl
  act S.stop refl _ = stop-waitR e refl
  act (S.put B v P) refl eqw = quiet-putR e refl eqw
  act (S.pick0 P) refl eqw = quiet-pick0R e refl eqw
  act (S.pick1 P) refl eqw = quiet-pick1R e refl eqw
  act (S.get T x P) refl eqw = quiet-getR e refl eqw
  act (S.cover P Q) refl eqw = quiet-coverR e refl eqw
  act (S.iget x P Q) refl eqw = quiet-igetR e refl eqw
  act (S.mget T x ps) refl eqw = quiet-mgetR e refl eqw

view-lw : ∀ {g c r} → reactL g c ≡ AGo r → reactR g c ≡ AWait →
          gview g c ≡ VGo r []
view-lw eqL eqR rewrite eqL | eqR = refl

view-rw : ∀ {g c r} → reactL g c ≡ AWait → reactR g c ≡ AGo r →
          gview g c ≡ VGo r []
view-rw eqL eqR rewrite eqL | eqR = refl

view-both : ∀ {g c r1 r2} →
            reactL g c ≡ AGo r1 → reactR g c ≡ AGo r2 →
            gview g c ≡ VGo r1 (r2 ∷ [])
view-both eqL eqR rewrite eqL | eqR = refl

shape-go : ∀ {g c r ks} → gview g c ≡ VGo r ks → Shape (gview g c)
shape-go eq = subst Shape (sym eq) sh-step

-- Both processes halted and both async queues empty: the graph is final.
haltedL : ∀ {g c s} (e : Embed g c s) →
          A.halt (A.Conf.lp c) ≡ true →
          Σ Focus (λ f → Unfold (envPL s) [] (left s) [] [] f × HaltF f)
haltedL {c = c} {s = s} e hp = on (A.Conf.lp c) refl hp
  where
  on : (P : S.Proc) → A.Conf.lp c ≡ P → A.halt P ≡ true →
       Σ Focus (λ f → Unfold (envPL s) [] (left s) [] [] f × HaltF f)
  on S.done eq _ =
    f-done , castU s f-done (Embed.zPL e) (asDone eq) u-done , h-done
    where
    asDone : A.Conf.lp c ≡ S.done → left s ≡ sdone
    asDone eqP = trans (Embed.lp≡ e) (cong (go (Embed.preL e)) eqP)
  on S.stop eq _ =
    f-stop , castU s f-stop (Embed.zPL e) (asStop eq) u-stop , h-stop
    where
    asStop : A.Conf.lp c ≡ S.stop → left s ≡ sstop
    asStop eqP = trans (Embed.lp≡ e) (cong (go (Embed.preL e)) eqP)
  on (S.put _ _ _) _ ()
  on (S.get _ _ _) _ ()
  on (S.pick0 _) _ ()
  on (S.pick1 _) _ ()
  on (S.cover _ _) _ ()
  on (S.iget _ _ _) _ ()
  on (S.mget _ _ _) _ ()

haltedR : ∀ {g c s} (e : Embed g c s) →
          A.halt (A.Conf.rp c) ≡ true →
          Σ Focus (λ f → Unfold (envPR s) [] (right s) [] [] f × HaltF f)
haltedR {c = c} {s = s} e hp = on (A.Conf.rp c) refl hp
  where
  on : (P : S.Proc) → A.Conf.rp c ≡ P → A.halt P ≡ true →
       Σ Focus (λ f → Unfold (envPR s) [] (right s) [] [] f × HaltF f)
  on S.done eq _ =
    f-done , castR s f-done (Embed.zPR e) (asDone eq) u-done , h-done
    where
    asDone : A.Conf.rp c ≡ S.done → right s ≡ sdone
    asDone eqP = trans (Embed.rp≡ e) (cong (go (Embed.preR e)) eqP)
  on S.stop eq _ =
    f-stop , castR s f-stop (Embed.zPR e) (asStop eq) u-stop , h-stop
    where
    asStop : A.Conf.rp c ≡ S.stop → right s ≡ sstop
    asStop eqP = trans (Embed.rp≡ e) (cong (go (Embed.preR e)) eqP)
  on (S.put _ _ _) _ ()
  on (S.get _ _ _) _ ()
  on (S.pick0 _) _ ()
  on (S.pick1 _) _ ()
  on (S.cover _ _) _ ()
  on (S.iget _ _ _) _ ()
  on (S.mget _ _ _) _ ()

fin-ht : ∀ {g c} → Step g c fin c → halted g c ≡ true
fin-ht (finish _ _ h) = h

final-shape : ∀ {g c s} (e : Embed g c s) →
              A.Conf.l2r c ≡ [] → A.Conf.r2l c ≡ [] →
              A.halt (A.Conf.lp c) ≡ true →
              A.halt (A.Conf.rp c) ≡ true →
              Shape (gview g (abs s))
final-shape {s = s} e nilA nilB hp hq =
  let _ , uL , hfL = haltedL e hp
      _ , uR , hfR = haltedR e hq
      st , _ = fin-fwd (Embed.hold e) uL hfL uR hfR
                 (src-nilL e nilA) (src-nil e nilB)
  in subst Shape
       (sym (view-final (src-nilL e nilA) (src-nil e nilB) (fin-ht st)))
       sh-final

-- `lstep` names one `does`. The other side waits or steps, never badly.
stepped : ∀ {g c s d} (e : Embed g c s) →
          A.StepAt c (A.classify c) d →
          Shape (gview g (abs s))
stepped {c = c} e st with split-step (A.reactL c) (A.reactR c) refl refl st
... | mvL _ eql (inj₁ eqr) =
  let _ , _ , _ , gs = left-does e eql
  in shape-go (view-lw (tgtL gs) (quietR e eqr))
... | mvL _ eql (inj₂ (_ , _ , eqr)) =
  let _ , _ , _ , gsL = left-does e eql
      _ , _ , _ , gsR = right-does e eqr
  in shape-go (view-both (tgtL gsL) (tgtR gsR))
... | mvR _ eqr (inj₁ eql) =
  let _ , _ , _ , gs = right-does e eqr
  in shape-go (view-rw (quietL e eql) (tgtR gs))
... | mvR _ eqr (inj₂ (_ , _ , eql)) =
  let _ , _ , _ , gsL = left-does e eql
      _ , _ , _ , gsR = right-does e eqr
  in shape-go (view-both (tgtL gsL) (tgtR gsR))

kept : ∀ {g c s} (e : Embed g c s) → A.Safe c → Shape (gview g (abs s))
kept e safe with A.local safe
... | A.lfin a b hp hq _ = final-shape e a b hp hq
... | A.lstep _ st = stepped e st

-- `inj` has no `mu`, and `Frag` has already refused a repeated name.
mu-inj : ∀ (P : S.Proc) → Frag (inj P) → muOk (inj P) ≡ true
mu-inj P fp with distinctN (bnames (go [] P))
... | true = mu-ok [] P
... | false = ⊥-elim (no-sout fp)

left-is : ∀ (P : S.Proc) → Frag (inj P) → inj P ≡ go [] P
left-is P fp with distinctN (bnames (go [] P))
... | true = refl
... | false = ⊥-elim (no-sout fp)

len-rep : ∀ n → length (replicate n) ≡ n
len-rep zero = refl
len-rep (suc n) = cong suc (len-rep n)

cok-inj : ∀ {e n s bs e′ n′ s′ bs′} →
          cok e n s bs ≡ cok e′ n′ s′ bs′ →
          e ≡ e′ × n ≡ n′ × s ≡ s′ × bs ≡ bs′
cok-inj refl = refl , refl , refl , refl

-- The start configuration of a finite meeting is the source
-- configuration `initS` returns. `echoOk` is the premise `init-hold`
-- reads. `muOk` is `mu-inj`.
init-embed : ∀ k (P Q : S.Proc) (fp : Frag (inj P)) (fq : Frag (inj Q))
             g s0 →
             graphOf k (inj P) (inj Q) fp fq ≡ gok g →
             initS k (inj P) (inj Q) fp fq ≡ just s0 →
             echoOk (bnames (inj P)) [] (inj P) ≡ true →
             echoOk (bnames (inj Q)) [] (inj Q) ≡ true →
             Embed g (A.init k P Q) s0
init-embed k P Q fp fq g s0 eqg eqc eP eQ =
  body (denote (inj P) fp [] [] [] [] (bnames (inj P)) [] [] [] zero zero
          er0 (echo-empty [] (bnames (inj P))) eP refl (root-ns (inj P))
          (mu-inj P fp))
       (denote (inj Q) fq [] [] [] [] (bnames (inj Q)) [] [] [] zero zero
          er0 (echo-empty [] (bnames (inj Q))) eQ refl (root-ns (inj Q))
          (mu-inj Q fq))
  where
  lost : ∀ {f} (oL : COut) → oL ≡ cfail f → (oR : COut) →
         proj₁ (gpack k (inj P) (inj Q) oL oR) ≡ gok g → ⊥
  lost (cfail _) refl _ ()
  lost (cok _ _ _ _) () _ _

  lostR : ∀ {f} (oL oR : COut) → oR ≡ cfail f →
          proj₁ (gpack k (inj P) (inj Q) oL oR) ≡ gok g → ⊥
  lostR (cfail _) (cfail _) refl ()
  lostR (cok _ _ _ _) (cfail _) refl ()
  lostR _ (cok _ _ _ _) () _

  fields : (yL : Yes (inj P) fp [] [] [] [] zero zero (bnames (inj P)))
           (yR : Yes (inj Q) fq [] [] [] [] zero zero (bnames (inj Q)))
           (oL oR : COut) →
           oL ≡ cok (entry (Yes.w yL)) (next (Yes.w yL))
                    (slotN (Yes.w yL)) (Yes.bs yL) →
           oR ≡ cok (entry (Yes.w yR)) (next (Yes.w yR))
                    (slotN (Yes.w yR)) (Yes.bs yR) →
           proj₁ (gpack k (inj P) (inj Q) oL oR) ≡ gok g →
           proj₂ (gpack k (inj P) (inj Q) oL oR) ≡ just s0 →
           Embed g (A.init k P Q) s0
  fields yL yR (cok eL nL sL bsL) (cok eR nR sR bsR) eqL eqR refl refl =
    record
      { hold = init-hold k (inj P) (inj Q) fp fq eP eQ
                 (mu-inj P fp) (mu-inj Q fq) g s0 eqg eqc
      ; al≡ = refl
      ; cap≡ = refl
      ; qL = qnil
      ; qR = qnil
      ; preL = []
      ; preR = []
      ; lp≡ = left-is P fp
      ; rp≡ = left-is Q fq
      ; zPL = refl
      ; zPR = refl
      ; zIL = refl
      ; zIR = refl
      ; frL = fp
      ; frR = fq
      ; passedL = []
      ; sufL = []
      ; passedR = []
      ; sufR = []
      ; layL = sym (++[] (bnames (inj P)))
      ; layR = sym (++[] (bnames (inj Q)))
      ; slot≡L = refl
      ; slot≡R = refl
      ; disL = inj-ok P fp
      ; disR = inj-ok Q fq
      ; lenL = trans (len-rep sL) (trans sL≡ (Yes.end yL))
      ; lenR = trans (len-rep sR) (trans sR≡ (Yes.end yR))
      ; vL = vr0
      ; vR = vr0
      }
    where
    sL≡ : sL ≡ slotN (Yes.w yL)
    sL≡ = proj₁ (proj₂ (proj₂ (cok-inj eqL)))
    sR≡ : sR ≡ slotN (Yes.w yR)
    sR≡ = proj₁ (proj₂ (proj₂ (cok-inj eqR)))
  fields _ _ (cfail _) _ () _ _ _
  fields _ _ (cok _ _ _ _) (cfail _) _ () _ _

  body : Built (inj P) fp [] [] [] [] zero zero (bnames (inj P)) →
         Built (inj Q) fq [] [] [] [] zero zero (bnames (inj Q)) →
         Embed g (A.init k P Q) s0
  body (bad (noB _ _ cmp)) _ =
    ⊥-elim (lost (compiled (inj P) fp) cmp (compiled (inj Q) fq) eqg)
  body (ok _) (bad (noB _ _ cmp)) =
    ⊥-elim (lostR (compiled (inj P) fp) (compiled (inj Q) fq) cmp eqg)
  body (ok yL) (ok yR) =
    fields yL yR (compiled (inj P) fp) (compiled (inj Q) fq)
      (Yes.cmp yL) (Yes.cmp yR) eqg eqc

-- Every graph configuration reachable from an embedded safe state is
-- final or has a step. A `fin` edge stays put. Any other child is the
-- async step `inj-bwd` reads, and `step-safe` keeps `Safe`.
carry : ∀ {g cA s cg ce} → Embed g cA s → A.Safe cA →
        abs s ≡ cg → Reach g cg ce → Shape (gview g ce)
carry {g} e safe ab rhere =
  subst (λ z → Shape (gview g z)) ab (kept e safe)
carry {g} {cA} {s} {cg} {ce} e safe ab (rstep {d = d} mem later)
  with kid-step mem
... | lside , st =
  onward (inj-bwd e safe
            (subst (λ z → Step g z lside d) (sym ab) st) (λ ()))
  where
  onward : Back g cA s d → Shape (gview g ce)
  onward (_ , s′ , astep , emb , ab′) =
    carry emb (A.step-safe safe astep) ab′ later
... | rside , st =
  onward (inj-bwd e safe
            (subst (λ z → Step g z rside d) (sym ab) st) (λ ()))
  where
  onward : Back g cA s d → Shape (gview g ce)
  onward (_ , s′ , astep , emb , ab′) =
    carry emb (A.step-safe safe astep) ab′ later
... | fin , st =
  carry e safe (sym (fin-eq (subst (λ z → Step g z fin d) (sym ab) st))) later
  where
  fin-eq : Step g (abs s) fin d → d ≡ abs s
  fin-eq (finish _ _ _) = refl

-- A safe finite meeting has no deadlock on the graph it compiles to.
safe→nostuck : ∀ k (P Q : S.Proc) (fp : Frag (inj P)) (fq : Frag (inj Q))
               g s0 →
               graphOf k (inj P) (inj Q) fp fq ≡ gok g →
               initS k (inj P) (inj Q) fp fq ≡ just s0 →
               echoOk (bnames (inj P)) [] (inj P) ≡ true →
               echoOk (bnames (inj Q)) [] (inj Q) ≡ true →
               A.Safe (A.init k P Q) →
               NoStuck g
safe→nostuck k P Q fp fq g s0 eqg eqc eP eQ safe =
  carry (init-embed k P Q fp fq g s0 eqg eqc eP eQ) safe
    (init-sim k (inj P) (inj Q) fp fq g s0 eqg eqc)

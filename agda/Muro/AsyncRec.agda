------------------------------------------------------------------------
-- Asynchronous meetings of recursive processes.
--
-- A configuration is two instruction pointers, two queues of length at
-- most the buffer bound, and the value each binder holds. The pointers
-- range over the blocks of the two processes, and a queue entry is a
-- literal from a finite alphabet or a choice label. That set is finite.
-- The search recurses on a budget computed from its size: every call
-- peels one from that budget, which counts the configurations not yet
-- visited, including revisits of a configuration already on the stack.
-- A repeat is a safe cycle, not a deadlock. Zero does not accept a
-- fresh configuration.
--
-- A send on a cycle is a literal, an echo of a received value, or it is
-- refused. `suc` of a received nat on a cycle is `unbounded recursive
-- payload`: the alphabet would not be finite. A `rec` whose body is
-- only a jump back is `unguarded recursion`.
--
-- `okB` says the visited set is locally safe and closed under the step.
-- A yes answer carries that proof. Every configuration reachable from
-- the start is therefore locally safe: a final one has empty queues and
-- both ends halted, and any other has a step. A reception error, an
-- orphan, and a deadlock are not local.
--
-- Nothing here is added to Tm.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.AsyncRec where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_)
open import Data.List.Properties using (≡-dec)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable.Core using (Dec)
  renaming (yes to yes′; no to no′)

------------------------------------------------------------------------
-- Payloads. A literal is closed. An echo is the variable itself.
-- `rgrow` is `suc` of a received nat.
------------------------------------------------------------------------

data Atom : Set where
  aNat : ℕ → Atom
  aBit : Bool → Atom
  aCon : String → Atom

data Tag : Set where
  tagNat tagBit : Tag
  tagDat : String → Tag

data RProc : Set where
  rdone rstop : RProc
  rput : Atom → RProc → RProc
  recho : String → RProc → RProc
  rgrow : String → RProc → RProc
  rget : Tag → String → RProc → RProc
  rpick0 rpick1 : RProc → RProc
  rcover : RProc → RProc → RProc
  riget : String → RProc → RProc → RProc
  rmget : Tag → String → List (String × RProc) → RProc
  rmu : String → RProc → RProc
  rvar : String → RProc

data Fault : Set where
  fRecvL fRecvR fOrphan fDead fUnguarded fUnbounded fFree : Fault

data Answer : Set where
  yes : Answer
  no : Fault → Answer

------------------------------------------------------------------------
-- Blocks. Continuations and binder slots are indices.
------------------------------------------------------------------------

data Block : Set where
  bDone bStop : Block
  bPut : Atom → ℕ → Block
  bEcho : ℕ → ℕ → Block
  bGrow : ℕ → ℕ → Block
  bGet : Tag → ℕ → ℕ → Block
  bPick0 bPick1 : ℕ → Block
  bCover : ℕ → ℕ → Block
  bIget : ℕ → ℕ → ℕ → Block
  bMget : Tag → ℕ → List (String × ℕ) → Block

data COut : Set where
  cfail : Fault → COut
  cok : (entry next slot : ℕ) (bs : List (ℕ × Block)) → COut

REnv : Set
REnv = List (String × ℕ)

VEnv : Set
VEnv = List (String × ℕ)

lookupN : String → List (String × ℕ) → Maybe ℕ
lookupN x [] = nothing
lookupN x ((y , n) ∷ rest) with x == y
... | true = just n
... | false = lookupN x rest

elemS : String → List String → Bool
elemS x [] = false
elemS x (y ∷ ys) with x == y
... | true = true
... | false = elemS x ys

addNames : List String → ℕ → REnv → REnv
addNames [] n renv = renv
addNames (x ∷ xs) n renv = (x , n) ∷ addNames xs n renv

------------------------------------------------------------------------
-- Compile. Pending names are bound to the next block this process
-- allocates. A jump to one of them, with no block in between, is
-- unguarded. The recursion is structural on the process.
------------------------------------------------------------------------

compile : RProc → List String → REnv → VEnv → ℕ → ℕ → COut

compileArms : List (String × RProc) → REnv → VEnv → ℕ → ℕ →
              COut × List (String × ℕ) × List (ℕ × Block)

compile (rmu x p) pending renv venv slot n =
  compile p (x ∷ pending) renv venv slot n
compile (rvar y) pending renv venv slot n with elemS y pending
... | true = cfail fUnguarded
... | false with lookupN y renv
... | just i = cok i n slot []
... | nothing = cfail fFree
compile rdone pending renv venv slot n =
  cok n (suc n) slot ((n , bDone) ∷ [])
compile rstop pending renv venv slot n =
  cok n (suc n) slot ((n , bStop) ∷ [])
compile (rput a p) pending renv venv slot n
  with compile p [] (addNames pending n renv) venv slot (suc n)
... | cfail f = cfail f
... | cok e next slot' bs =
  cok n next slot' ((n , bPut a e) ∷ bs)
compile (recho x p) pending renv venv slot n with lookupN x venv
... | nothing = cfail fFree
... | just s with compile p [] (addNames pending n renv) venv slot (suc n)
... | cfail f = cfail f
... | cok e next slot' bs =
  cok n next slot' ((n , bEcho s e) ∷ bs)
compile (rgrow x p) pending renv venv slot n with lookupN x venv
... | nothing = cfail fFree
... | just s with compile p [] (addNames pending n renv) venv slot (suc n)
... | cfail f = cfail f
... | cok e next slot' bs =
  cok n next slot' ((n , bGrow s e) ∷ bs)
compile (rget t x p) pending renv venv slot n
  with compile p [] (addNames pending n renv) ((x , slot) ∷ venv) (suc slot) (suc n)
... | cfail f = cfail f
... | cok e next slot' bs =
  cok n next slot' ((n , bGet t slot e) ∷ bs)
compile (rpick0 p) pending renv venv slot n
  with compile p [] (addNames pending n renv) venv slot (suc n)
... | cfail f = cfail f
... | cok e next slot' bs =
  cok n next slot' ((n , bPick0 e) ∷ bs)
compile (rpick1 p) pending renv venv slot n
  with compile p [] (addNames pending n renv) venv slot (suc n)
... | cfail f = cfail f
... | cok e next slot' bs =
  cok n next slot' ((n , bPick1 e) ∷ bs)
compile (rcover p q) pending renv venv slot n
  with compile p [] (addNames pending n renv) venv slot (suc n)
... | cfail f = cfail f
... | cok e1 next1 slot1 bs1
  with compile q [] (addNames pending n renv) venv slot1 next1
... | cfail f = cfail f
... | cok e2 next2 slot2 bs2 =
  cok n next2 slot2 ((n , bCover e1 e2) ∷ bs1 ++ bs2)
compile (riget x p q) pending renv venv slot n
  with compile p [] (addNames pending n renv) ((x , slot) ∷ venv) (suc slot) (suc n)
... | cfail f = cfail f
... | cok e1 next1 slot1 bs1
  with compile q [] (addNames pending n renv) ((x , slot) ∷ venv) slot1 next1
... | cfail f = cfail f
... | cok e2 next2 slot2 bs2 =
  cok n next2 slot2 ((n , bIget slot e1 e2) ∷ bs1 ++ bs2)
compile (rmget t x arms) pending renv venv slot n
  with compileArms arms (addNames pending n renv) ((x , slot) ∷ venv) (suc slot) (suc n)
... | cfail f , _ , _ = cfail f
... | cok _ next slot' _ , named , bs =
  cok n next slot' ((n , bMget t slot named) ∷ bs)

compileArms [] renv venv slot n = cok n n slot [] , [] , []
compileArms ((name , p) ∷ rest) renv venv slot n
  with compile p [] renv venv slot n
... | cfail f = cfail f , [] , []
... | cok e next slot1 bs1
  with compileArms rest renv venv slot1 next
... | cfail f , _ , _ = cfail f , [] , []
... | cok _ next2 slot2 _ , named , bs2 =
  cok next2 next2 slot2 [] , (name , e) ∷ named , bs1 ++ bs2

------------------------------------------------------------------------
-- A flat table. `next` is the first free index, so the table has
-- that many blocks.
------------------------------------------------------------------------

findB : ℕ → List (ℕ × Block) → Block
findB i [] = bDone
findB i ((j , b) ∷ rest) with i ≟ j
... | yes′ _ = b
... | no′ _ = findB i rest

materialise : ℕ → ℕ → List (ℕ × Block) → List Block
materialise zero i bs = []
materialise (suc r) i bs = findB i bs ∷ materialise r (suc i) bs

conts : Block → List ℕ
conts bDone = []
conts bStop = []
conts (bPut _ j) = j ∷ []
conts (bEcho _ j) = j ∷ []
conts (bGrow _ j) = j ∷ []
conts (bGet _ _ j) = j ∷ []
conts (bPick0 j) = j ∷ []
conts (bPick1 j) = j ∷ []
conts (bCover i j) = i ∷ j ∷ []
conts (bIget _ i j) = i ∷ j ∷ []
conts (bMget _ _ as) = map₂ as
  where
  map₂ : List (String × ℕ) → List ℕ
  map₂ [] = []
  map₂ (( _ , j) ∷ rest) = j ∷ map₂ rest

isGrow : Block → Bool
isGrow (bGrow _ _) = true
isGrow _ = false

growCount : List Block → ℕ
growCount [] = zero
growCount (b ∷ bs) with isGrow b
... | true = suc (growCount bs)
... | false = growCount bs

elemℕ : ℕ → List ℕ → Bool
elemℕ n [] = false
elemℕ n (x ∷ xs) with n ≟ x
... | yes′ _ = true
... | no′ _ = elemℕ n xs

-- `start` is on a cycle when a walk returns to it. The budget is one
-- more than the length of the table, and every call peels one from it.
cyclic : List Block → ℕ → Bool
cyclic bs start = walk (suc (length bs)) [] (start ∷ [])
  where
  blockAt : ℕ → List Block → Maybe Block
  blockAt _ [] = nothing
  blockAt zero (b ∷ _) = just b
  blockAt (suc n) (_ ∷ rest) = blockAt n rest
  succs : ℕ → List ℕ
  succs i with blockAt i bs
  ... | nothing = []
  ... | just b = conts b
  walk : ℕ → List ℕ → List ℕ → Bool
  walk zero _ _ = false
  walk (suc fuel) seen [] = false
  walk (suc fuel) seen (i ∷ rest) with elemℕ i seen
  ... | true with i ≟ start
  ... | yes′ _ = true
  ... | no′ _ = walk fuel seen rest
  walk (suc fuel) seen (i ∷ rest) | false =
    walk fuel (i ∷ seen) (succs i ++ rest)

anyCyclicGrow : List Block → Bool
anyCyclicGrow bs = go zero bs
  where
  go : ℕ → List Block → Bool
  go i [] = false
  go i (b ∷ rest) with isGrow b
  ... | true with cyclic bs i
  ... | true = true
  ... | false = go (suc i) rest
  go i (_ ∷ rest) | false = go (suc i) rest

------------------------------------------------------------------------
-- Alphabet. Literals are collected. Each non-cyclic `suc` adds one
-- layer, and a path meets each such `suc` once, so that many layers
-- close the set.
------------------------------------------------------------------------

eqA : Atom → Atom → Bool
eqA (aNat m) (aNat n) with m ≟ n
... | yes′ _ = true
... | no′ _ = false
eqA (aBit false) (aBit false) = true
eqA (aBit true) (aBit true) = true
eqA (aBit _) (aBit _) = false
eqA (aCon x) (aCon y) = x == y
eqA _ _ = false

elemA : Atom → List Atom → Bool
elemA a [] = false
elemA a (x ∷ xs) with eqA a x
... | true = true
... | false = elemA a xs

addA : Atom → List Atom → List Atom
addA a as with elemA a as
... | true = as
... | false = a ∷ as

adds : List Atom → List Atom → List Atom
adds [] as = as
adds (a ∷ xs) as = adds xs (addA a as)

lits : List Block → List Atom
lits [] = []
lits (bPut a _ ∷ bs) = addA a (lits bs)
lits (_ ∷ bs) = lits bs

sucAll : List Atom → List Atom
sucAll [] = []
sucAll (aNat m ∷ as) = aNat (suc m) ∷ sucAll as
sucAll (_ ∷ as) = sucAll as

layers : ℕ → List Atom → List Atom
layers zero as = as
layers (suc n) as = layers n (adds (sucAll as) as)

------------------------------------------------------------------------
-- Configurations. A slot holds `zero` when it is empty and `suc i`
-- when it holds alphabet entry `i`.
------------------------------------------------------------------------

data Tok : Set where
  pay : ℕ → Tok
  lab : Bool → Tok

data RConf : Set where
  rc : (il ir : ℕ) (l2r r2l : List Tok) (el er : List ℕ) → RConf

record Graph : Set where
  constructor gr
  field
    codeL codeR : List Block
    alpha : List Atom
    cap : ℕ
    entryL entryR : ℕ
    slotsL slotsR : ℕ

open Graph

replicate : ℕ → List ℕ
replicate zero = []
replicate (suc n) = zero ∷ replicate n

init : Graph → RConf
init g = rc (entryL g) (entryR g) [] [] (replicate (slotsL g)) (replicate (slotsR g))

------------------------------------------------------------------------
-- One step. A full queue waits. An empty queue waits. A wrong head
-- is a reception error. Left is tried first.
------------------------------------------------------------------------

lt : ℕ → ℕ → Bool
lt zero zero = false
lt zero (suc _) = true
lt (suc _) zero = false
lt (suc m) (suc n) = lt m n

room : ℕ → List Tok → Bool
room cap q = lt (length q) cap

snoc : List Tok → Tok → List Tok
snoc [] t = t ∷ []
snoc (x ∷ xs) t = x ∷ snoc xs t

nth : List ℕ → ℕ → Maybe ℕ
nth [] _ = nothing
nth (x ∷ _) zero = just x
nth (_ ∷ xs) (suc n) = nth xs n

setNth : ℕ → ℕ → List ℕ → List ℕ
setNth zero v (_ ∷ xs) = v ∷ xs
setNth (suc n) v (x ∷ xs) = x ∷ setNth n v xs
setNth _ _ [] = []

nthA : List Atom → ℕ → Maybe Atom
nthA [] _ = nothing
nthA (a ∷ _) zero = just a
nthA (_ ∷ as) (suc n) = nthA as n

findA : Atom → List Atom → Maybe ℕ
findA a as = go zero as
  where
  go : ℕ → List Atom → Maybe ℕ
  go i [] = nothing
  go i (x ∷ xs) with eqA a x
  ... | true = just i
  ... | false = go (suc i) xs

fits : Tag → Atom → Bool
fits tagNat (aNat _) = true
fits tagBit (aBit _) = true
fits (tagDat _) (aCon _) = true
fits _ _ = false

bitOf : Atom → Maybe Bool
bitOf (aBit b) = just b
bitOf _ = nothing

natOf : Atom → Maybe ℕ
natOf (aNat n) = just n
natOf _ = nothing

conOf : Atom → Maybe String
conOf (aCon s) = just s
conOf _ = nothing

armTo : String → List (String × ℕ) → Maybe ℕ
armTo name [] = nothing
armTo name ((y , j) ∷ rest) with name == y
... | true = just j
... | false = armTo name rest

lookB : List Block → ℕ → Maybe Block
lookB [] _ = nothing
lookB (b ∷ _) zero = just b
lookB (_ ∷ bs) (suc n) = lookB bs n

data Act : Set where
  AWait : Act
  ABad : Fault → Act
  AGo : RConf → Act

ilOf : RConf → ℕ
ilOf (rc i _ _ _ _ _) = i

irOf : RConf → ℕ
irOf (rc _ i _ _ _ _) = i

l2rOf : RConf → List Tok
l2rOf (rc _ _ q _ _ _) = q

r2lOf : RConf → List Tok
r2lOf (rc _ _ _ q _ _) = q

elOf : RConf → List ℕ
elOf (rc _ _ _ _ e _) = e

erOf : RConf → List ℕ
erOf (rc _ _ _ _ _ e) = e

enqL : Graph → RConf → Tok → ℕ → Act
enqL g (rc il ir l2r r2l el er) t i with room (cap g) l2r
... | false = AWait
... | true = AGo (rc i ir (snoc l2r t) r2l el er)

enqR : Graph → RConf → Tok → ℕ → Act
enqR g (rc il ir l2r r2l el er) t i with room (cap g) r2l
... | false = AWait
... | true = AGo (rc il i l2r (snoc r2l t) el er)

slotVal : List ℕ → ℕ → Maybe ℕ
slotVal env s with nth env s
... | just zero = nothing
... | just (suc i) = just i
... | nothing = nothing

-- A `suc` of a queued nat. Missing from the alphabet is the unbounded
-- fault. Anything that is not a nat waits.
growL : Graph → RConf → ℕ → Maybe Atom → Act
growL g c i nothing = AWait
growL g c i (just (aNat m)) with findA (aNat (suc m)) (alpha g)
... | just j = enqL g c (pay j) i
... | nothing = ABad fUnbounded
growL g c i (just (aBit _)) = AWait
growL g c i (just (aCon _)) = AWait

growR : Graph → RConf → ℕ → Maybe Atom → Act
growR g c i nothing = AWait
growR g c i (just (aNat m)) with findA (aNat (suc m)) (alpha g)
... | just j = enqR g c (pay j) i
... | nothing = ABad fUnbounded
growR g c i (just (aBit _)) = AWait
growR g c i (just (aCon _)) = AWait

onL-get : Graph → RConf → Tag → ℕ → ℕ → Act
onL-get g (rc il ir l2r r2l el er) t s i with r2l
... | [] = AWait
... | lab _ ∷ _ = ABad fRecvL
... | pay k ∷ rest with nthA (alpha g) k
... | nothing = ABad fRecvL
... | just a with fits t a
... | false = ABad fRecvL
... | true = AGo (rc i ir l2r rest (setNth s (suc k) el) er)

onL-cover : Graph → RConf → ℕ → ℕ → Act
onL-cover g (rc il ir l2r r2l el er) i j with r2l
... | [] = AWait
... | pay _ ∷ _ = ABad fRecvL
... | lab false ∷ rest = AGo (rc i ir l2r rest el er)
... | lab true ∷ rest = AGo (rc j ir l2r rest el er)

onL-iget : Graph → RConf → ℕ → ℕ → ℕ → Act
onL-iget g (rc il ir l2r r2l el er) s i j with r2l
... | [] = AWait
... | lab _ ∷ _ = ABad fRecvL
... | pay k ∷ rest with nthA (alpha g) k
... | nothing = ABad fRecvL
... | just (aNat _) = ABad fRecvL
... | just (aBit false) = AGo (rc i ir l2r rest (setNth s (suc k) el) er)
... | just (aBit true) = AGo (rc j ir l2r rest (setNth s (suc k) el) er)
... | just (aCon _) = ABad fRecvL

onL-mget : Graph → RConf → Tag → ℕ → List (String × ℕ) → Act
onL-mget g (rc il ir l2r r2l el er) t s arms with r2l
... | [] = AWait
... | lab _ ∷ _ = ABad fRecvL
... | pay k ∷ rest with nthA (alpha g) k
... | nothing = ABad fRecvL
... | just a with fits t a
... | false = ABad fRecvL
... | true with conOf a
... | nothing = ABad fRecvL
... | just name with armTo name arms
... | nothing = ABad fRecvL
... | just j = AGo (rc j ir l2r rest (setNth s (suc k) el) er)

onR-get : Graph → RConf → Tag → ℕ → ℕ → Act
onR-get g (rc il ir l2r r2l el er) t s i with l2r
... | [] = AWait
... | lab _ ∷ _ = ABad fRecvR
... | pay k ∷ rest with nthA (alpha g) k
... | nothing = ABad fRecvR
... | just a with fits t a
... | false = ABad fRecvR
... | true = AGo (rc il i rest r2l el (setNth s (suc k) er))

onR-cover : Graph → RConf → ℕ → ℕ → Act
onR-cover g (rc il ir l2r r2l el er) i j with l2r
... | [] = AWait
... | pay _ ∷ _ = ABad fRecvR
... | lab false ∷ rest = AGo (rc il i rest r2l el er)
... | lab true ∷ rest = AGo (rc il j rest r2l el er)

onR-iget : Graph → RConf → ℕ → ℕ → ℕ → Act
onR-iget g (rc il ir l2r r2l el er) s i j with l2r
... | [] = AWait
... | lab _ ∷ _ = ABad fRecvR
... | pay k ∷ rest with nthA (alpha g) k
... | nothing = ABad fRecvR
... | just (aNat _) = ABad fRecvR
... | just (aBit false) = AGo (rc il i rest r2l el (setNth s (suc k) er))
... | just (aBit true) = AGo (rc il j rest r2l el (setNth s (suc k) er))
... | just (aCon _) = ABad fRecvR

onR-mget : Graph → RConf → Tag → ℕ → List (String × ℕ) → Act
onR-mget g (rc il ir l2r r2l el er) t s arms with l2r
... | [] = AWait
... | lab _ ∷ _ = ABad fRecvR
... | pay k ∷ rest with nthA (alpha g) k
... | nothing = ABad fRecvR
... | just a with fits t a
... | false = ABad fRecvR
... | true with conOf a
... | nothing = ABad fRecvR
... | just name with armTo name arms
... | nothing = ABad fRecvR
... | just j = AGo (rc il j rest r2l el (setNth s (suc k) er))

onL : Graph → RConf → Block → Act
onL g c bDone = AWait
onL g c bStop = AWait
onL g c (bPut a i) with findA a (alpha g)
... | nothing = ABad fUnbounded
... | just k = enqL g c (pay k) i
onL g c (bEcho s i) with slotVal (elOf c) s
... | nothing = AWait
... | just k = enqL g c (pay k) i
onL g c (bGrow s i) with slotVal (elOf c) s
... | nothing = AWait
... | just k = growL g c i (nthA (alpha g) k)
onL g c (bPick0 i) = enqL g c (lab false) i
onL g c (bPick1 i) = enqL g c (lab true) i
onL g c (bGet t s i) = onL-get g c t s i
onL g c (bCover i j) = onL-cover g c i j
onL g c (bIget s i j) = onL-iget g c s i j
onL g c (bMget t s arms) = onL-mget g c t s arms

onR : Graph → RConf → Block → Act
onR g c bDone = AWait
onR g c bStop = AWait
onR g c (bPut a i) with findA a (alpha g)
... | nothing = ABad fUnbounded
... | just k = enqR g c (pay k) i
onR g c (bEcho s i) with slotVal (erOf c) s
... | nothing = AWait
... | just k = enqR g c (pay k) i
onR g c (bGrow s i) with slotVal (erOf c) s
... | nothing = AWait
... | just k = growR g c i (nthA (alpha g) k)
onR g c (bPick0 i) = enqR g c (lab false) i
onR g c (bPick1 i) = enqR g c (lab true) i
onR g c (bGet t s i) = onR-get g c t s i
onR g c (bCover i j) = onR-cover g c i j
onR g c (bIget s i j) = onR-iget g c s i j
onR g c (bMget t s arms) = onR-mget g c t s arms

reactL : Graph → RConf → Act
reactL g c with lookB (codeL g) (ilOf c)
... | nothing = AWait
... | just b = onL g c b

reactR : Graph → RConf → Act
reactR g c with lookB (codeR g) (irOf c)
... | nothing = AWait
... | just b = onR g c b

andb : Bool → Bool → Bool
andb true b = b
andb false _ = false

isHalt : Block → Bool
isHalt bDone = true
isHalt bStop = true
isHalt _ = false

halted : Graph → RConf → Bool
halted g (rc il ir _ _ _ _) with lookB (codeL g) il | lookB (codeR g) ir
... | just bl | just br = andb (isHalt bl) (isHalt br)
... | just _ | nothing = false
... | nothing | just _ = false
... | nothing | nothing = false

------------------------------------------------------------------------
-- A view is final, a fault, or a nonempty list of steps. Left is
-- first. A full buffer waits. Both halted with a queued message is
-- an orphan. Both halted with empty queues is success, `done` against
-- `stop` included.
------------------------------------------------------------------------

data View (g : Graph) (c : RConf) : Set where
  VFinal : l2rOf c ≡ [] → r2lOf c ≡ [] → halted g c ≡ true → View g c
  VBad : Fault → View g c
  VGo : RConf → List RConf → View g c

idle : (g : Graph) (c : RConf) → View g c
idle g c = on (l2rOf c) (r2lOf c) (halted g c) refl refl refl
  where
  on : (lq rq : List Tok) (h : Bool) →
       l2rOf c ≡ lq → r2lOf c ≡ rq → halted g c ≡ h → View g c
  on [] [] true eqL eqR eqH = VFinal eqL eqR eqH
  on [] [] false _ _ _ = VBad fDead
  on [] (_ ∷ _) true _ _ _ = VBad fOrphan
  on [] (_ ∷ _) false _ _ _ = VBad fDead
  on (_ ∷ _) [] true _ _ _ = VBad fOrphan
  on (_ ∷ _) [] false _ _ _ = VBad fDead
  on (_ ∷ _) (_ ∷ _) true _ _ _ = VBad fOrphan
  on (_ ∷ _) (_ ∷ _) false _ _ _ = VBad fDead

merge : (g : Graph) (c : RConf) → Act → Act → View g c
merge g c (ABad f) _ = VBad f
merge g c (AGo _) (ABad f) = VBad f
merge g c AWait (ABad f) = VBad f
merge g c (AGo c1) (AGo c2) = VGo c1 (c2 ∷ [])
merge g c (AGo c1) AWait = VGo c1 []
merge g c AWait (AGo c2) = VGo c2 []
merge g c AWait AWait = idle g c

view : (g : Graph) (c : RConf) → View g c
view g c = merge g c (reactL g c) (reactR g c)

kidsV : ∀ {g c} → View g c → List RConf
kidsV (VFinal _ _ _) = []
kidsV (VBad _) = []
kidsV (VGo k ks) = k ∷ ks

localB : ∀ {g c} → View g c → Bool
localB (VFinal _ _ _) = true
localB (VBad _) = false
localB (VGo _ _) = true

-- A local view is either final, with the empty-queue proofs the
-- constructor carries, or a step. A reception error, an orphan, and
-- a deadlock are not local.
data Shape {g : Graph} {c : RConf} : View g c → Set where
  sh-final : ∀ {a b h} → Shape (VFinal a b h)
  sh-step : ∀ {k ks} → Shape (VGo k ks)

shapeOf : ∀ {g c} (v : View g c) → localB v ≡ true → Shape v
shapeOf (VFinal _ _ _) _ = sh-final
shapeOf (VBad _) ()
shapeOf (VGo _ _) _ = sh-step

------------------------------------------------------------------------
-- Equality of configurations, so the visited set can be searched.
------------------------------------------------------------------------

tok≟ : (x y : Tok) → Dec (x ≡ y)
tok≟ (pay m) (pay n) with m ≟ n
... | yes′ refl = yes′ refl
... | no′ ¬p = no′ (λ { refl → ¬p refl })
tok≟ (pay _) (lab _) = no′ (λ ())
tok≟ (lab _) (pay _) = no′ (λ ())
tok≟ (lab false) (lab false) = yes′ refl
tok≟ (lab true) (lab true) = yes′ refl
tok≟ (lab false) (lab true) = no′ (λ ())
tok≟ (lab true) (lab false) = no′ (λ ())

toks≟ : (xs ys : List Tok) → Dec (xs ≡ ys)
toks≟ = ≡-dec tok≟

nats≟ : (xs ys : List ℕ) → Dec (xs ≡ ys)
nats≟ = ≡-dec _≟_

conf≟ : (x y : RConf) → Dec (x ≡ y)
conf≟ (rc a b c d e f) (rc a′ b′ c′ d′ e′ f′) with a ≟ a′
... | no′ ¬p = no′ (λ { refl → ¬p refl })
... | yes′ refl with b ≟ b′
... | no′ ¬p = no′ (λ { refl → ¬p refl })
... | yes′ refl with toks≟ c c′
... | no′ ¬p = no′ (λ { refl → ¬p refl })
... | yes′ refl with toks≟ d d′
... | no′ ¬p = no′ (λ { refl → ¬p refl })
... | yes′ refl with nats≟ e e′
... | no′ ¬p = no′ (λ { refl → ¬p refl })
... | yes′ refl with nats≟ f f′
... | no′ ¬p = no′ (λ { refl → ¬p refl })
... | yes′ refl = yes′ refl

elemB : RConf → List RConf → Bool
elemB c [] = false
elemB c (x ∷ xs) with conf≟ c x
... | yes′ _ = true
... | no′ _ = elemB c xs

findC : (c : RConf) (xs : List RConf) → Dec (Any (_≡_ c) xs)
findC c [] = no′ (λ ())
findC c (x ∷ xs) with conf≟ c x
... | yes′ refl = yes′ (here refl)
... | no′ ¬eq with findC c xs
... | yes′ has = yes′ (there has)
... | no′ ¬has = no′ (λ { (here eq) → ¬eq eq ; (there has) → ¬has has })

------------------------------------------------------------------------
-- The search recurses on a budget. Every call, including a revisit,
-- peels one. A revisit is a safe cycle. The budget is one more than
-- three times the size of the configuration space: each visit pushes
-- at most two children, so the pops run out only after the reachable
-- fragment has been closed. The environment is a vector, one slot per
-- binder, so that space is finite.
------------------------------------------------------------------------

explore : (g : Graph) (n : ℕ) (seen work : List RConf) → List RConf
explore g zero seen _ = seen
explore g (suc n) seen [] = seen
explore g (suc n) seen (c ∷ rest) with elemB c seen
... | true = explore g n seen rest
... | false with view g c
... | VGo k ks = explore g n (seen ++ (c ∷ [])) (k ∷ ks ++ rest)
... | VFinal _ _ _ = explore g n (seen ++ (c ∷ [])) rest
... | VBad _ = explore g n (seen ++ (c ∷ [])) rest

pow : ℕ → ℕ → ℕ
pow b zero = suc zero
pow b (suc n) = pow b n * b

qcount : ℕ → ℕ → ℕ
qcount t zero = suc zero
qcount t (suc k) = qcount t k + pow t (suc k)

budget : Graph → ℕ
budget g = suc (uni * 3)
  where
  tokens = length (alpha g) + 2
  queues = qcount tokens (cap g)
  envsL = pow (suc (length (alpha g))) (slotsL g)
  envsR = pow (suc (length (alpha g))) (slotsR g)
  uni =
    length (codeL g) * length (codeR g) * queues * queues * envsL * envsR

------------------------------------------------------------------------
-- `okB` is local safety and closure. Boolean membership does not yield
-- an equality, so the lemmas below rebuild the proof `Any` carries.
------------------------------------------------------------------------

allB : {A : Set} → (A → Bool) → List A → Bool
allB p [] = true
allB p (x ∷ xs) = andb (p x) (allB p xs)

kidsIn : (g : Graph) (s : List RConf) (c : RConf) → Bool
kidsIn g s c = allB (λ d → elemB d s) (kidsV (view g c))

okB : (g : Graph) (s : List RConf) → Bool
okB g s = allB (λ c → andb (localB (view g c)) (kidsIn g s c)) s

and-left : ∀ {a b} → andb a b ≡ true → a ≡ true
and-left {true} _ = refl
and-left {false} ()

and-right : ∀ {a b} → andb a b ≡ true → b ≡ true
and-right {true} eq = eq
and-right {false} ()

all→ : ∀ {A : Set} {p : A → Bool} {x : A} {xs : List A} →
       allB p xs ≡ true → Any (_≡_ x) xs → p x ≡ true
all→ eq (here refl) = and-left eq
all→ eq (there later) = all→ (and-right eq) later

elem→any : ∀ {c : RConf} {xs : List RConf} →
           elemB c xs ≡ true → Any (_≡_ c) xs
elem→any {c} {[]} ()
elem→any {c} {x ∷ xs} eq with conf≟ c x
... | yes′ refl = here refl
... | no′ _ = there (elem→any eq)

kids-true : ∀ {g s c} → okB g s ≡ true → Any (_≡_ c) s → kidsIn g s c ≡ true
kids-true ok has = and-right (all→ ok has)

local-true : ∀ {g s c} → okB g s ≡ true → Any (_≡_ c) s →
             localB (view g c) ≡ true
local-true ok has = and-left (all→ ok has)

kid-elem : ∀ {g s c d} → kidsIn g s c ≡ true →
           Any (_≡_ d) (kidsV (view g c)) → elemB d s ≡ true
kid-elem eq has = all→ eq has

data Reach (g : Graph) : RConf → RConf → Set where
  rhere : ∀ {c} → Reach g c c
  rstep : ∀ {c d e} → Any (_≡_ d) (kidsV (view g c)) →
          Reach g d e → Reach g c e

reachable-local : ∀ {g s c d} →
                  okB g s ≡ true → Any (_≡_ c) s → Reach g c d →
                  localB (view g d) ≡ true
reachable-local {g} {s} {c} ok has rhere = local-true {g} {s} {c} ok has
reachable-local {g} {s} {c} {d} ok has (rstep {d = mid} step later) =
  reachable-local {g} {s} {mid} {d} ok
    (elem→any {mid} {s}
      (kid-elem {g} {s} {c} {mid}
        (kids-true {g} {s} {c} ok has) step))
    later

data Result (g : Graph) : Set where
  accepted : (s : List RConf) → okB g s ≡ true → Any (_≡_ (init g)) s →
             Result g
  rejected : Fault → Result g

firstFault : Graph → List RConf → Fault
firstFault g [] = fDead
firstFault g (c ∷ cs) with view g c
... | VBad f = f
... | VFinal _ _ _ = firstFault g cs
... | VGo _ _ = firstFault g cs

pack : (g : Graph) (s : List RConf) → Result g
pack g s = go (okB g s) (findC (init g) s) refl
  where
  go : (b : Bool) → Dec (Any (_≡_ (init g)) s) → okB g s ≡ b → Result g
  go true (yes′ has) eq = accepted s eq has
  go true (no′ _) _ = rejected fDead
  go false _ _ = rejected (firstFault g s)

decideR : (g : Graph) → Result g
decideR g = pack g (explore g (budget g) [] (init g ∷ []))

verdict : ∀ {g} → Result g → Answer
verdict (accepted _ _ _) = yes
verdict (rejected f) = no f

-- Every configuration reachable from an accepted start is locally
-- safe. Final ones have empty queues and both ends halted. Any other
-- has a step. A reception error, an orphan, and a deadlock do not.
sound : ∀ {g} {s : List RConf} {ok : okB g s ≡ true}
          {has : Any (_≡_ (init g)) s} {d : RConf} →
        decideR g ≡ accepted s ok has →
        Reach g (init g) d →
        Shape (view g d)
sound {g = g} {ok = ok} {has = has} {d = d} _ reach =
  shapeOf (view g d) (reachable-local ok has reach)

------------------------------------------------------------------------
-- Compile, refuse a cyclic `suc`, then search.
------------------------------------------------------------------------

alphabet : List Block → List Block → List Atom
alphabet L R = layers (growCount L + growCount R) (adds (lits L) (lits R))

answerOf : ℕ → List Block → List Block → ℕ → ℕ → ℕ → ℕ → Answer
answerOf k L R eL eR sL sR with anyCyclicGrow L | anyCyclicGrow R
... | true | _ = no fUnbounded
... | false | true = no fUnbounded
... | false | false =
  verdict (decideR (gr L R (alphabet L R) k eL eR sL sR))

build : ℕ → COut → COut → Answer
build k (cfail f) _ = no f
build k (cok _ _ _ _) (cfail f) = no f
build k (cok eL nL sL bsL) (cok eR nR sR bsR) =
  answerOf k (materialise nL zero bsL) (materialise nR zero bsR)
           eL eR sL sR

check : ℕ → RProc → RProc → Answer
check k p q =
  build k (compile p [] [] [] zero zero) (compile q [] [] [] zero zero)

------------------------------------------------------------------------
-- Constant send against a receive loops and stays inside the alphabet.
-- A jump with no action is unguarded. `suc` of a received nat on a
-- cycle is refused. Two sends in a row at buffer 1 deadlock. Both
-- sending first meets.
------------------------------------------------------------------------

loopL : RProc
loopL = rmu "X" (rput (aNat zero) (rvar "X"))

loopR : RProc
loopR = rmu "Y" (rget tagNat "d" (rvar "Y"))

ex-loop : check (suc zero) loopL loopR ≡ yes
ex-loop = refl

ex-unguarded : check (suc zero) (rmu "X" (rvar "X")) rdone ≡ no fUnguarded
ex-unguarded = refl

growP : RProc
growP = rmu "X" (rget tagNat "n" (rgrow "n" (rvar "X")))

ex-grow : check (suc zero) growP loopR ≡ no fUnbounded
ex-grow = refl

dbl : RProc
dbl = rput (aNat zero) (rput (aNat (suc zero)) rdone)

ex-dead : check (suc zero) dbl dbl ≡ no fDead
ex-dead = refl

cross : RProc
cross = rput (aNat zero) (rget tagNat "a" rdone)

ex-cross : check (suc zero) cross cross ≡ yes
ex-cross = refl

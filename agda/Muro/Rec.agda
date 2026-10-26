------------------------------------------------------------------------
-- Recursive sessions. A protocol may repeat. The surface form is
-- `rec X. S`: X in S is that same protocol. A variable must sit
-- under an action of its own `rec`. `rec X. X` is not a protocol.
-- A name with no `rec` is not a protocol. Leading `rec`s are one
-- loop, so `rec X. rec Y. send Nat X` is that send, and both names
-- are the loop. `rec X. end` is `end`.
--
-- The finite syntax is inductive. `dual` on it is structural:
-- `rec` stays `rec`, a variable stays, and each action swaps as
-- in `Muro.Dual`. The other end of the other end is the same
-- syntax. That walk is structural.
--
-- The protocol a `rec` denotes is coinductive. `unfold` reads one
-- guarded action and ties the loop under that action, so the
-- definition is productive. `dual∞` swaps one action and dualises
-- the continuations. `_~_` is the bisimulation. `dual∞` is an
-- involution up to `_~_`, and unfolding the dual syntax is the
-- dual of the unfolding.
--
-- A process repeats with the same `rec`. `Conforms∞` and `Meets∞`
-- are bisimulations: one step, then the continuations. `Finishes`
-- is a finite walk. A jump back to `rec` has no derivation of
-- `Finishes`, so `%1` still refuses a loop. `run` is unchanged.
-- None of these constructors is added to `Tm`.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Rec where

open import Data.Bool.Base using (true)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; z≤n) renaming (zero to nzero; suc to nsuc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.String.Base using (String)
open import Data.String.Properties using (_≟_)
open import Data.Unit.Base using (⊤)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary.Decidable.Core using (yes; no)

open import Muro.Base using (Mode; spec; evid; run)
open import Muro.Session using
  ( Ty; nat; bit; unit; pair; vec; dat
  ; Decl; mkDecl; ctor
  ; Spine; snil; con
  ; NExp; nlit; nvar
  ; Val; zero; suc; b0; b1; tt; one
  ; ValExpr; lit; var; call
  ; maybeBool; effCall
  ; Ctx; _∈_∷_; here
  ; ValExprOk; lit-ok; var-ok; call-ok
  ; sent
  ; Idx; none; bind; shadow; renameIdx; applyTy; ixOf
  ; Owed; owed; Le; lit-le; resolve
  ; Scrut; byVal; byRun
  )

¬_ : Set → Set
¬ A = A → ⊥

------------------------------------------------------------------------
-- Finite syntax. One continuation after a payload. An indexed bit
-- and a choice have two. `svar` is a recursion variable. `mu`
-- binds one.
------------------------------------------------------------------------

data SExp : Set where
  end    : SExp
  send   : Ty → SExp → SExp
  recv   : Ty → SExp → SExp
  dsend  : String → Ty → SExp → SExp
  drecv  : String → Ty → SExp → SExp
  esend  : String → NExp → SExp → SExp
  erecv  : String → NExp → SExp → SExp
  isend  : String → SExp → SExp → SExp
  irecv  : String → SExp → SExp → SExp
  choose : SExp → SExp → SExp
  branch : SExp → SExp → SExp
  -- The scrutinee is the name the enclosing action binds. The arms
  -- are elaborated in that action's context, so the case itself
  -- does not guard a variable.
  pcase  : Scrut → List (String × SExp) → SExp
  svar   : String → SExp
  mu     : String → SExp → SExp

data PExp : Set where
  pdone  : PExp
  pstop  : PExp
  pput   : (A : Ty) → ValExpr A → PExp → PExp
  pget   : Ty → String → PExp → PExp
  ppick0 : PExp → PExp
  ppick1 : PExp → PExp
  pcover : PExp → PExp → PExp
  piget  : String → PExp → PExp → PExp
  pvar   : String → PExp
  pmu    : String → PExp → PExp

------------------------------------------------------------------------
-- `dual` on the finite syntax. `rec` stays. A variable stays.
-- The continuation dualises. Structural, so it terminates.
------------------------------------------------------------------------

mutual
  dualS : SExp → SExp
  dualS end = end
  dualS (send A s) = recv A (dualS s)
  dualS (recv A s) = send A (dualS s)
  dualS (dsend x A s) = drecv x A (dualS s)
  dualS (drecv x A s) = dsend x A (dualS s)
  dualS (esend x e s) = erecv x e (dualS s)
  dualS (erecv x e s) = esend x e (dualS s)
  dualS (isend x s t) = irecv x (dualS s) (dualS t)
  dualS (irecv x s t) = isend x (dualS s) (dualS t)
  dualS (choose s t) = branch (dualS s) (dualS t)
  dualS (branch s t) = choose (dualS s) (dualS t)
  dualS (pcase scrut as) = pcase scrut (dualSArms as)
  dualS (svar x) = svar x
  dualS (mu x s) = mu x (dualS s)

  dualSArms : List (String × SExp) → List (String × SExp)
  dualSArms [] = []
  dualSArms ((c , s) ∷ as) = (c , dualS s) ∷ dualSArms as

  dualS-invol : (s : SExp) → dualS (dualS s) ≡ s
  dualS-invol end = refl
  dualS-invol (send A s) = cong (send A) (dualS-invol s)
  dualS-invol (recv A s) = cong (recv A) (dualS-invol s)
  dualS-invol (dsend x A s) = cong (dsend x A) (dualS-invol s)
  dualS-invol (drecv x A s) = cong (drecv x A) (dualS-invol s)
  dualS-invol (esend x e s) = cong (esend x e) (dualS-invol s)
  dualS-invol (erecv x e s) = cong (erecv x e) (dualS-invol s)
  dualS-invol (isend x s t) = cong₂ (isend x) (dualS-invol s) (dualS-invol t)
  dualS-invol (irecv x s t) = cong₂ (irecv x) (dualS-invol s) (dualS-invol t)
  dualS-invol (choose s t) = cong₂ choose (dualS-invol s) (dualS-invol t)
  dualS-invol (branch s t) = cong₂ branch (dualS-invol s) (dualS-invol t)
  dualS-invol (pcase scrut as) = cong (pcase scrut) (dualSArms-invol as)
  dualS-invol (svar x) = refl
  dualS-invol (mu x s) = cong (mu x) (dualS-invol s)

  dualSArms-invol : ∀ as → dualSArms (dualSArms as) ≡ as
  dualSArms-invol [] = refl
  dualSArms-invol ((c , s) ∷ as) =
    cong₂ (λ s′ as′ → (c , s′) ∷ as′) (dualS-invol s) (dualSArms-invol as)

------------------------------------------------------------------------
-- Guarded syntax. A head is an action. A continuation is that
-- head's child: an embedded action, a variable that is already
-- guarded, or a `rec` whose body is an action. `elab` refuses a
-- variable that is not guarded and a name that is not bound.
------------------------------------------------------------------------

data GExp : Set
data CExp : Set

data GExp where
  g-end    : GExp
  g-send   : Ty → CExp → GExp
  g-recv   : Ty → CExp → GExp
  g-dsend  : String → Ty → CExp → GExp
  g-drecv  : String → Ty → CExp → GExp
  g-esend  : String → NExp → CExp → GExp
  g-erecv  : String → NExp → CExp → GExp
  g-isend  : String → CExp → CExp → GExp
  g-irecv  : String → CExp → CExp → GExp
  g-choose : CExp → CExp → GExp
  g-branch : CExp → CExp → GExp
  g-case   : Scrut → List (String × CExp) → GExp

data CExp where
  c-emb : GExp → CExp
  c-var : String → CExp
  c-mu  : List String → GExp → CExp

data Stat : Set where
  ung gua : Stat

SCtx : Set
SCtx = List (String × Stat)

guard : SCtx → SCtx
guard [] = []
guard ((x , _) ∷ Γ) = (x , gua) ∷ guard Γ

find : String → SCtx → Maybe Stat
find x [] = nothing
find x ((y , s) ∷ Γ) with x ≟ y
... | yes _ = just s
... | no _ = find x Γ

data Elab (A : Set) : Set where
  good           : A → Elab A
  bad-free       : String → Elab A
  bad-unguarded  : Elab A

infixl 1 _>>=_
_>>=_ : {A B : Set} → Elab A → (A → Elab B) → Elab B
good x >>= f = f x
bad-free x >>= _ = bad-free x
bad-unguarded >>= _ = bad-unguarded

elabC : SCtx → SExp → Elab CExp
elabNest : List String → SCtx → SExp → Elab CExp
elabArms : SCtx → List (String × SExp) → Elab (List (String × CExp))

elabVar : SCtx → String → Elab CExp
elabVar Γ x with find x Γ
... | nothing = bad-free x
... | just ung = bad-unguarded
... | just gua = good (c-var x)

elabC Γ end = good (c-emb g-end)
elabC Γ (send A s) = elabC (guard Γ) s >>= λ c → good (c-emb (g-send A c))
elabC Γ (recv A s) = elabC (guard Γ) s >>= λ c → good (c-emb (g-recv A c))
elabC Γ (dsend x A s) = elabC (guard Γ) s >>= λ c → good (c-emb (g-dsend x A c))
elabC Γ (drecv x A s) = elabC (guard Γ) s >>= λ c → good (c-emb (g-drecv x A c))
elabC Γ (esend x e s) = elabC (guard Γ) s >>= λ c → good (c-emb (g-esend x e c))
elabC Γ (erecv x e s) = elabC (guard Γ) s >>= λ c → good (c-emb (g-erecv x e c))
elabC Γ (isend x s t) =
  elabC (guard Γ) s >>= λ c →
  elabC (guard Γ) t >>= λ d →
  good (c-emb (g-isend x c d))
elabC Γ (irecv x s t) =
  elabC (guard Γ) s >>= λ c →
  elabC (guard Γ) t >>= λ d →
  good (c-emb (g-irecv x c d))
elabC Γ (choose s t) =
  elabC (guard Γ) s >>= λ c →
  elabC (guard Γ) t >>= λ d →
  good (c-emb (g-choose c d))
elabC Γ (branch s t) =
  elabC (guard Γ) s >>= λ c →
  elabC (guard Γ) t >>= λ d →
  good (c-emb (g-branch c d))
elabC Γ (pcase scrut as) = elabArms Γ as >>= λ es → good (c-emb (g-case scrut es))
elabC Γ (svar x) = elabVar Γ x
elabC Γ (mu x s) = elabNest (x ∷ []) ((x , ung) ∷ Γ) s

elabNest xs Γ (mu y s) = elabNest (y ∷ xs) ((y , ung) ∷ Γ) s
elabNest xs Γ (svar x) = elabVar Γ x
elabNest _ _ end = good (c-emb g-end)
elabNest xs Γ (send A s) = elabC (guard Γ) s >>= λ c → good (c-mu xs (g-send A c))
elabNest xs Γ (recv A s) = elabC (guard Γ) s >>= λ c → good (c-mu xs (g-recv A c))
elabNest xs Γ (dsend x A s) = elabC (guard Γ) s >>= λ c → good (c-mu xs (g-dsend x A c))
elabNest xs Γ (drecv x A s) = elabC (guard Γ) s >>= λ c → good (c-mu xs (g-drecv x A c))
elabNest xs Γ (esend x e s) = elabC (guard Γ) s >>= λ c → good (c-mu xs (g-esend x e c))
elabNest xs Γ (erecv x e s) = elabC (guard Γ) s >>= λ c → good (c-mu xs (g-erecv x e c))
elabNest xs Γ (isend x s t) =
  elabC (guard Γ) s >>= λ c →
  elabC (guard Γ) t >>= λ d →
  good (c-mu xs (g-isend x c d))
elabNest xs Γ (irecv x s t) =
  elabC (guard Γ) s >>= λ c →
  elabC (guard Γ) t >>= λ d →
  good (c-mu xs (g-irecv x c d))
elabNest xs Γ (choose s t) =
  elabC (guard Γ) s >>= λ c →
  elabC (guard Γ) t >>= λ d →
  good (c-mu xs (g-choose c d))
elabNest xs Γ (branch s t) =
  elabC (guard Γ) s >>= λ c →
  elabC (guard Γ) t >>= λ d →
  good (c-mu xs (g-branch c d))
elabNest xs Γ (pcase scrut as) = elabArms Γ as >>= λ es → good (c-mu xs (g-case scrut es))

-- A case keeps the context it was elaborated in. The enclosing
-- action is what guards a variable inside an arm.
elabArms _ [] = good []
elabArms Γ ((c , s) ∷ as) =
  elabC Γ s >>= λ e →
  elabArms Γ as >>= λ es →
  good ((c , e) ∷ es)

-- `rec X. X` is unguarded. `rec X. rec Y. X` is unguarded.
-- A bare name is free. A name under an action of its `rec` is a loop.

rec-x-x : elabC [] (mu "X" (svar "X")) ≡ bad-unguarded
rec-x-x = refl

rec-x-y-x : elabC [] (mu "X" (mu "Y" (svar "X"))) ≡ bad-unguarded
rec-x-y-x = refl

free-x : elabC [] (svar "X") ≡ bad-free "X"
free-x = refl

free-inside : elabC [] (send nat (svar "Y")) ≡ bad-free "Y"
free-inside = refl

echoSyn : SExp
echoSyn = mu "X" (recv nat (send nat (svar "X")))

echoC : CExp
echoC = c-mu ("X" ∷ []) (g-recv nat (c-emb (g-send nat (c-var "X"))))

echo-elab : elabC [] echoSyn ≡ good echoC
echo-elab = refl

flatSyn : SExp
flatSyn = mu "X" (mu "Y" (send nat (svar "X")))

flatC : CExp
flatC = c-mu ("Y" ∷ "X" ∷ []) (g-send nat (c-var "X"))

flat-elab : elabC [] flatSyn ≡ good flatC
flat-elab = refl

bitSyn : SExp
bitSyn = mu "X" (irecv "b" (svar "X") end)

bitC : CExp
bitC = c-mu ("X" ∷ []) (g-irecv "b" (c-var "X") (c-emb g-end))

bit-elab : elabC [] bitSyn ≡ good bitC
bit-elab = refl

-- A variable under only a case is unguarded. Under the receive, it is the loop.
bareCase : SExp
bareCase = mu "X" (pcase (byVal "b") (("b0" , svar "X") ∷ []))

bare-case : elabC [] bareCase ≡ bad-unguarded
bare-case = refl

caseSyn : SExp
caseSyn = mu "X" (drecv "b" bit (pcase (byVal "b") (("b0" , svar "X") ∷ ("b1" , end) ∷ [])))

caseC : CExp
caseC = c-mu ("X" ∷ []) (g-drecv "b" bit (c-emb (g-case (byVal "b")
  (("b0" , c-var "X") ∷ ("b1" , c-emb g-end) ∷ []))))

case-elab : elabC [] caseSyn ≡ good caseC
case-elab = refl

case-round : dualS (dualS caseSyn) ≡ caseSyn
case-round = refl

------------------------------------------------------------------------
-- The coinductive protocol. One observation is one action.
-- `unfold` places the recursive call under that action.
------------------------------------------------------------------------

data SStep (P : Set) : Set
data ArmF (P A : Set) : Set
record ∞Proto : Set
record Arms∞ : Set

data ArmF P A where
  a-nil  : ArmF P A
  a-cons : String → P → A → ArmF P A

data SStep P where
  s-end    : SStep P
  s-send   : Ty → P → SStep P
  s-recv   : Ty → P → SStep P
  s-dsend  : String → Ty → P → SStep P
  s-drecv  : String → Ty → P → SStep P
  s-esend  : String → NExp → P → SStep P
  s-erecv  : String → NExp → P → SStep P
  s-isend  : String → P → P → SStep P
  s-irecv  : String → P → P → SStep P
  s-choose : P → P → SStep P
  s-branch : P → P → SStep P
  s-case   : Scrut → Arms∞ → SStep P

record ∞Proto where
  coinductive
  field observe : SStep ∞Proto

-- One constructor of the case, then the rest. The tail is the
-- coinductive record, so unfolding an arm sits under `a-cons`.
record Arms∞ where
  coinductive
  field ahead : ArmF ∞Proto Arms∞

open ∞Proto
open Arms∞

Env : Set
Env = List (String × GExp)

lookupG : String → Env → GExp
lookupG x [] = g-end
lookupG x ((y , g) ∷ ρ) with x ≟ y
... | yes _ = g
... | no _ = lookupG x ρ

bindAll : List String → GExp → Env → Env
bindAll [] _ ρ = ρ
bindAll (x ∷ xs) g ρ = (x , g) ∷ bindAll xs g ρ

cont : Env → CExp → Env × GExp
cont ρ (c-emb g) = ρ , g
cont ρ (c-var x) = ρ , lookupG x ρ
cont ρ (c-mu xs g) = bindAll xs g ρ , g

mutual
  unfold : Env → GExp → ∞Proto
  observe (unfold ρ g-end) = s-end
  observe (unfold ρ (g-send A c)) = s-send A (unfold (proj₁ (cont ρ c)) (proj₂ (cont ρ c)))
  observe (unfold ρ (g-recv A c)) = s-recv A (unfold (proj₁ (cont ρ c)) (proj₂ (cont ρ c)))
  observe (unfold ρ (g-dsend x A c)) = s-dsend x A (unfold (proj₁ (cont ρ c)) (proj₂ (cont ρ c)))
  observe (unfold ρ (g-drecv x A c)) = s-drecv x A (unfold (proj₁ (cont ρ c)) (proj₂ (cont ρ c)))
  observe (unfold ρ (g-esend x e c)) = s-esend x e (unfold (proj₁ (cont ρ c)) (proj₂ (cont ρ c)))
  observe (unfold ρ (g-erecv x e c)) = s-erecv x e (unfold (proj₁ (cont ρ c)) (proj₂ (cont ρ c)))
  observe (unfold ρ (g-isend x c d)) =
    s-isend x (unfold (proj₁ (cont ρ c)) (proj₂ (cont ρ c))) (unfold (proj₁ (cont ρ d)) (proj₂ (cont ρ d)))
  observe (unfold ρ (g-irecv x c d)) =
    s-irecv x (unfold (proj₁ (cont ρ c)) (proj₂ (cont ρ c))) (unfold (proj₁ (cont ρ d)) (proj₂ (cont ρ d)))
  observe (unfold ρ (g-choose c d)) =
    s-choose (unfold (proj₁ (cont ρ c)) (proj₂ (cont ρ c))) (unfold (proj₁ (cont ρ d)) (proj₂ (cont ρ d)))
  observe (unfold ρ (g-branch c d)) =
    s-branch (unfold (proj₁ (cont ρ c)) (proj₂ (cont ρ c))) (unfold (proj₁ (cont ρ d)) (proj₂ (cont ρ d)))
  observe (unfold ρ (g-case scrut as)) = s-case scrut (armsOf ρ as)

  -- The recursive unfolding of an arm is an argument of `a-cons`.
  armsOf : Env → List (String × CExp) → Arms∞
  ahead (armsOf _ []) = a-nil
  ahead (armsOf ρ ((c , c-emb g) ∷ as)) = a-cons c (unfold ρ g) (armsOf ρ as)
  ahead (armsOf ρ ((c , c-var x) ∷ as)) = a-cons c (unfold ρ (lookupG x ρ)) (armsOf ρ as)
  ahead (armsOf ρ ((c , c-mu xs g) ∷ as)) = a-cons c (unfold (bindAll xs g ρ) g) (armsOf ρ as)

------------------------------------------------------------------------
-- Processes, the same way. A jump is a variable under an action.
------------------------------------------------------------------------

data PStep (P : Set) : Set where
  p-done  : PStep P
  p-stop  : PStep P
  p-put   : (A : Ty) → ValExpr A → P → PStep P
  p-get   : Ty → String → P → PStep P
  p-pick0 : P → PStep P
  p-pick1 : P → PStep P
  p-cover : P → P → PStep P
  p-iget  : String → P → P → PStep P

record ∞Proc : Set where
  coinductive
  field act : PStep ∞Proc

open ∞Proc

data PG : Set
data PC : Set

data PG where
  pg-done  : PG
  pg-stop  : PG
  pg-put   : (A : Ty) → ValExpr A → PC → PG
  pg-get   : Ty → String → PC → PG
  pg-pick0 : PC → PG
  pg-pick1 : PC → PG
  pg-cover : PC → PC → PG
  pg-iget  : String → PC → PC → PG

data PC where
  pc-emb : PG → PC
  pc-var : String → PC
  pc-mu  : List String → PG → PC

PEnv : Set
PEnv = List (String × PG)

lookupP : String → PEnv → PG
lookupP x [] = pg-done
lookupP x ((y , g) ∷ ρ) with x ≟ y
... | yes _ = g
... | no _ = lookupP x ρ

bindP : List String → PG → PEnv → PEnv
bindP [] _ ρ = ρ
bindP (x ∷ xs) g ρ = (x , g) ∷ bindP xs g ρ

pcont : PEnv → PC → PEnv × PG
pcont ρ (pc-emb g) = ρ , g
pcont ρ (pc-var x) = ρ , lookupP x ρ
pcont ρ (pc-mu xs g) = bindP xs g ρ , g

unfoldP : PEnv → PG → ∞Proc
act (unfoldP ρ pg-done) = p-done
act (unfoldP ρ pg-stop) = p-stop
act (unfoldP ρ (pg-put A v c)) = p-put A v (unfoldP (proj₁ (pcont ρ c)) (proj₂ (pcont ρ c)))
act (unfoldP ρ (pg-get A x c)) = p-get A x (unfoldP (proj₁ (pcont ρ c)) (proj₂ (pcont ρ c)))
act (unfoldP ρ (pg-pick0 c)) = p-pick0 (unfoldP (proj₁ (pcont ρ c)) (proj₂ (pcont ρ c)))
act (unfoldP ρ (pg-pick1 c)) = p-pick1 (unfoldP (proj₁ (pcont ρ c)) (proj₂ (pcont ρ c)))
act (unfoldP ρ (pg-cover c d)) =
  p-cover (unfoldP (proj₁ (pcont ρ c)) (proj₂ (pcont ρ c))) (unfoldP (proj₁ (pcont ρ d)) (proj₂ (pcont ρ d)))
act (unfoldP ρ (pg-iget x c d)) =
  p-iget x (unfoldP (proj₁ (pcont ρ c)) (proj₂ (pcont ρ c))) (unfoldP (proj₁ (pcont ρ d)) (proj₂ (pcont ρ d)))

------------------------------------------------------------------------
-- Process elaboration. Same guard as a protocol.
------------------------------------------------------------------------

elabP : SCtx → PExp → Elab PC
elabPNest : List String → SCtx → PExp → Elab PC

elabPVar : SCtx → String → Elab PC
elabPVar Γ x with find x Γ
... | nothing = bad-free x
... | just ung = bad-unguarded
... | just gua = good (pc-var x)

elabP Γ pdone = good (pc-emb pg-done)
elabP Γ pstop = good (pc-emb pg-stop)
elabP Γ (pput A v p) = elabP (guard Γ) p >>= λ c → good (pc-emb (pg-put A v c))
elabP Γ (pget A x p) = elabP (guard Γ) p >>= λ c → good (pc-emb (pg-get A x c))
elabP Γ (ppick0 p) = elabP (guard Γ) p >>= λ c → good (pc-emb (pg-pick0 c))
elabP Γ (ppick1 p) = elabP (guard Γ) p >>= λ c → good (pc-emb (pg-pick1 c))
elabP Γ (pcover p q) =
  elabP (guard Γ) p >>= λ c →
  elabP (guard Γ) q >>= λ d →
  good (pc-emb (pg-cover c d))
elabP Γ (piget x p q) =
  elabP (guard Γ) p >>= λ c →
  elabP (guard Γ) q >>= λ d →
  good (pc-emb (pg-iget x c d))
elabP Γ (pvar x) = elabPVar Γ x
elabP Γ (pmu x p) = elabPNest (x ∷ []) ((x , ung) ∷ Γ) p

elabPNest xs Γ (pmu y p) = elabPNest (y ∷ xs) ((y , ung) ∷ Γ) p
elabPNest xs Γ (pvar x) = elabPVar Γ x
elabPNest _ _ pdone = good (pc-emb pg-done)
elabPNest _ _ pstop = good (pc-emb pg-stop)
elabPNest xs Γ (pput A v p) = elabP (guard Γ) p >>= λ c → good (pc-mu xs (pg-put A v c))
elabPNest xs Γ (pget A x p) = elabP (guard Γ) p >>= λ c → good (pc-mu xs (pg-get A x c))
elabPNest xs Γ (ppick0 p) = elabP (guard Γ) p >>= λ c → good (pc-mu xs (pg-pick0 c))
elabPNest xs Γ (ppick1 p) = elabP (guard Γ) p >>= λ c → good (pc-mu xs (pg-pick1 c))
elabPNest xs Γ (pcover p q) =
  elabP (guard Γ) p >>= λ c →
  elabP (guard Γ) q >>= λ d →
  good (pc-mu xs (pg-cover c d))
elabPNest xs Γ (piget x p q) =
  elabP (guard Γ) p >>= λ c →
  elabP (guard Γ) q >>= λ d →
  good (pc-mu xs (pg-iget x c d))

proc-x-x : elabP [] (pmu "X" (pvar "X")) ≡ bad-unguarded
proc-x-x = refl

------------------------------------------------------------------------
-- `Finishes` is finite. A variable is a jump, and a jump does not
-- finish. `rec X. done` finishes. `rec X. get Nat X` does not.
------------------------------------------------------------------------

data Finishes : PExp → Set where
  f-done  : Finishes pdone
  f-put   : ∀ {A v p} → Finishes p → Finishes (pput A v p)
  f-get   : ∀ {A x p} → Finishes p → Finishes (pget A x p)
  f-pick0 : ∀ {p} → Finishes p → Finishes (ppick0 p)
  f-pick1 : ∀ {p} → Finishes p → Finishes (ppick1 p)
  f-cover : ∀ {p q} → Finishes p → Finishes q → Finishes (pcover p q)
  f-iget  : ∀ {x p q} → Finishes p → Finishes q → Finishes (piget x p q)
  f-mu    : ∀ {x p} → Finishes p → Finishes (pmu x p)

rec-done : Finishes (pmu "X" pdone)
rec-done = f-mu f-done

loop-open : ¬ Finishes (pmu "X" (pget nat "n" (pput nat (var "n") (pvar "X"))))
loop-open (f-mu (f-get (f-put ())))

------------------------------------------------------------------------
-- Duality on the infinite protocol. One action swaps. The
-- continuations dualise under that action.
------------------------------------------------------------------------

dualG : GExp → GExp
dualC : CExp → CExp
dualList : List (String × CExp) → List (String × CExp)
dualG g-end = g-end
dualG (g-send A c) = g-recv A (dualC c)
dualG (g-recv A c) = g-send A (dualC c)
dualG (g-dsend x A c) = g-drecv x A (dualC c)
dualG (g-drecv x A c) = g-dsend x A (dualC c)
dualG (g-esend x e c) = g-erecv x e (dualC c)
dualG (g-erecv x e c) = g-esend x e (dualC c)
dualG (g-isend x c d) = g-irecv x (dualC c) (dualC d)
dualG (g-irecv x c d) = g-isend x (dualC c) (dualC d)
dualG (g-choose c d) = g-branch (dualC c) (dualC d)
dualG (g-branch c d) = g-choose (dualC c) (dualC d)
dualG (g-case scrut as) = g-case scrut (dualList as)
dualC (c-emb g) = c-emb (dualG g)
dualC (c-var x) = c-var x
dualC (c-mu xs g) = c-mu xs (dualG g)

dualList [] = []
dualList ((c , e) ∷ as) = (c , dualC e) ∷ dualList as

dualEnv : Env → Env
dualEnv [] = []
dualEnv ((x , g) ∷ ρ) = (x , dualG g) ∷ dualEnv ρ

dual∞ : ∞Proto → ∞Proto
dualArms∞ : Arms∞ → Arms∞
observe (dual∞ p) = mapDual (observe p)
  where
    mapDual : SStep ∞Proto → SStep ∞Proto
    mapDual s-end = s-end
    mapDual (s-send A q) = s-recv A (dual∞ q)
    mapDual (s-recv A q) = s-send A (dual∞ q)
    mapDual (s-dsend x A q) = s-drecv x A (dual∞ q)
    mapDual (s-drecv x A q) = s-dsend x A (dual∞ q)
    mapDual (s-esend x e q) = s-erecv x e (dual∞ q)
    mapDual (s-erecv x e q) = s-esend x e (dual∞ q)
    mapDual (s-isend x q r) = s-irecv x (dual∞ q) (dual∞ r)
    mapDual (s-irecv x q r) = s-isend x (dual∞ q) (dual∞ r)
    mapDual (s-choose q r) = s-branch (dual∞ q) (dual∞ r)
    mapDual (s-branch q r) = s-choose (dual∞ q) (dual∞ r)
    mapDual (s-case scrut as) = s-case scrut (dualArms∞ as)

ahead (dualArms∞ as) with ahead as
... | a-nil = a-nil
... | a-cons c p qs = a-cons c (dual∞ p) (dualArms∞ qs)

data _~S_ : SStep ∞Proto → SStep ∞Proto → Set
data _~AS_ : ArmF ∞Proto Arms∞ → ArmF ∞Proto Arms∞ → Set
record _~_ (p q : ∞Proto) : Set where
  coinductive
  field obs : observe p ~S observe q
record _~A_ (as bs : Arms∞) : Set where
  coinductive
  field aobs : ahead as ~AS ahead bs

data _~S_ where
  ~end    : s-end ~S s-end
  ~send   : ∀ {A p q} → p ~ q → s-send A p ~S s-send A q
  ~recv   : ∀ {A p q} → p ~ q → s-recv A p ~S s-recv A q
  ~dsend  : ∀ {x A p q} → p ~ q → s-dsend x A p ~S s-dsend x A q
  ~drecv  : ∀ {x A p q} → p ~ q → s-drecv x A p ~S s-drecv x A q
  ~esend  : ∀ {x e p q} → p ~ q → s-esend x e p ~S s-esend x e q
  ~erecv  : ∀ {x e p q} → p ~ q → s-erecv x e p ~S s-erecv x e q
  ~isend  : ∀ {x p q p' q'} → p ~ q → p' ~ q' → s-isend x p p' ~S s-isend x q q'
  ~irecv  : ∀ {x p q p' q'} → p ~ q → p' ~ q' → s-irecv x p p' ~S s-irecv x q q'
  ~choose : ∀ {p q p' q'} → p ~ q → p' ~ q' → s-choose p p' ~S s-choose q q'
  ~branch : ∀ {p q p' q'} → p ~ q → p' ~ q' → s-branch p p' ~S s-branch q q'
  ~case   : ∀ {scrut as bs} → as ~A bs → s-case scrut as ~S s-case scrut bs

data _~AS_ where
  ~anil  : a-nil ~AS a-nil
  ~acons : ∀ {c p q as bs} → p ~ q → as ~A bs → a-cons c p as ~AS a-cons c q bs

open _~_
open _~A_

invol : (p : ∞Proto) → dual∞ (dual∞ p) ~ p
involA : (as : Arms∞) → dualArms∞ (dualArms∞ as) ~A as
obs (invol p) with observe p
... | s-end = ~end
... | s-send A q = ~send (invol q)
... | s-recv A q = ~recv (invol q)
... | s-dsend x A q = ~dsend (invol q)
... | s-drecv x A q = ~drecv (invol q)
... | s-esend x e q = ~esend (invol q)
... | s-erecv x e q = ~erecv (invol q)
... | s-isend x q r = ~isend (invol q) (invol r)
... | s-irecv x q r = ~irecv (invol q) (invol r)
... | s-choose q r = ~choose (invol q) (invol r)
... | s-branch q r = ~branch (invol q) (invol r)
... | s-case scrut as = ~case (involA as)

aobs (involA as) with ahead as
... | a-nil = ~anil
... | a-cons c p qs = ~acons (invol p) (involA qs)

lookup-dual : (x : String) (ρ : Env) → lookupG x (dualEnv ρ) ≡ dualG (lookupG x ρ)
lookup-dual x [] = refl
lookup-dual x ((y , g) ∷ ρ) with x ≟ y
... | yes _ = refl
... | no _ = lookup-dual x ρ

-- The goal of `comm` has already reduced `cont` of a `c-mu`, so the
-- environment on that side is `bindAll` of the dual body. This
-- equation faces that way. `rewrite` then meets `comm` on the dual
-- environment.
bindAll-dual : (xs : List String) (g : GExp) (ρ : Env) →
  bindAll xs (dualG g) (dualEnv ρ) ≡ dualEnv (bindAll xs g ρ)
bindAll-dual [] g ρ = refl
bindAll-dual (x ∷ xs) g ρ = cong ((x , dualG g) ∷_) (bindAll-dual xs g ρ)

-- Unfolding `dual` is dualising the unfolding.
comm : (ρ : Env) (g : GExp) → dual∞ (unfold ρ g) ~ unfold (dualEnv ρ) (dualG g)
commA : (ρ : Env) (as : List (String × CExp)) →
  dualArms∞ (armsOf ρ as) ~A armsOf (dualEnv ρ) (dualList as)
obs (comm ρ g-end) = ~end
obs (comm ρ (g-send A (c-emb g))) = ~recv (comm ρ g)
obs (comm ρ (g-send A (c-var v))) rewrite lookup-dual v ρ = ~recv (comm ρ (lookupG v ρ))
obs (comm ρ (g-send A (c-mu xs g))) rewrite bindAll-dual xs g ρ = ~recv (comm (bindAll xs g ρ) g)
obs (comm ρ (g-recv A (c-emb g))) = ~send (comm ρ g)
obs (comm ρ (g-recv A (c-var v))) rewrite lookup-dual v ρ = ~send (comm ρ (lookupG v ρ))
obs (comm ρ (g-recv A (c-mu xs g))) rewrite bindAll-dual xs g ρ = ~send (comm (bindAll xs g ρ) g)
obs (comm ρ (g-dsend x A (c-emb g))) = ~drecv (comm ρ g)
obs (comm ρ (g-dsend x A (c-var v))) rewrite lookup-dual v ρ = ~drecv (comm ρ (lookupG v ρ))
obs (comm ρ (g-dsend x A (c-mu xs g))) rewrite bindAll-dual xs g ρ = ~drecv (comm (bindAll xs g ρ) g)
obs (comm ρ (g-drecv x A (c-emb g))) = ~dsend (comm ρ g)
obs (comm ρ (g-drecv x A (c-var v))) rewrite lookup-dual v ρ = ~dsend (comm ρ (lookupG v ρ))
obs (comm ρ (g-drecv x A (c-mu xs g))) rewrite bindAll-dual xs g ρ = ~dsend (comm (bindAll xs g ρ) g)
obs (comm ρ (g-esend x e (c-emb g))) = ~erecv (comm ρ g)
obs (comm ρ (g-esend x e (c-var v))) rewrite lookup-dual v ρ = ~erecv (comm ρ (lookupG v ρ))
obs (comm ρ (g-esend x e (c-mu xs g))) rewrite bindAll-dual xs g ρ = ~erecv (comm (bindAll xs g ρ) g)
obs (comm ρ (g-erecv x e (c-emb g))) = ~esend (comm ρ g)
obs (comm ρ (g-erecv x e (c-var v))) rewrite lookup-dual v ρ = ~esend (comm ρ (lookupG v ρ))
obs (comm ρ (g-erecv x e (c-mu xs g))) rewrite bindAll-dual xs g ρ = ~esend (comm (bindAll xs g ρ) g)
obs (comm ρ (g-isend x (c-emb g) (c-emb h))) = ~irecv (comm ρ g) (comm ρ h)
obs (comm ρ (g-isend x (c-emb g) (c-var w))) rewrite lookup-dual w ρ = ~irecv (comm ρ g) (comm ρ (lookupG w ρ))
obs (comm ρ (g-isend x (c-emb g) (c-mu ys h))) rewrite bindAll-dual ys h ρ = ~irecv (comm ρ g) (comm (bindAll ys h ρ) h)
obs (comm ρ (g-isend x (c-var v) (c-emb h))) rewrite lookup-dual v ρ = ~irecv (comm ρ (lookupG v ρ)) (comm ρ h)
obs (comm ρ (g-isend x (c-var v) (c-var w))) rewrite lookup-dual v ρ | lookup-dual w ρ = ~irecv (comm ρ (lookupG v ρ)) (comm ρ (lookupG w ρ))
obs (comm ρ (g-isend x (c-var v) (c-mu ys h))) rewrite lookup-dual v ρ | bindAll-dual ys h ρ = ~irecv (comm ρ (lookupG v ρ)) (comm (bindAll ys h ρ) h)
obs (comm ρ (g-isend x (c-mu xs g) (c-emb h))) rewrite bindAll-dual xs g ρ = ~irecv (comm (bindAll xs g ρ) g) (comm ρ h)
obs (comm ρ (g-isend x (c-mu xs g) (c-var w))) rewrite bindAll-dual xs g ρ | lookup-dual w ρ = ~irecv (comm (bindAll xs g ρ) g) (comm ρ (lookupG w ρ))
obs (comm ρ (g-isend x (c-mu xs g) (c-mu ys h))) rewrite bindAll-dual xs g ρ | bindAll-dual ys h ρ = ~irecv (comm (bindAll xs g ρ) g) (comm (bindAll ys h ρ) h)
obs (comm ρ (g-irecv x (c-emb g) (c-emb h))) = ~isend (comm ρ g) (comm ρ h)
obs (comm ρ (g-irecv x (c-emb g) (c-var w))) rewrite lookup-dual w ρ = ~isend (comm ρ g) (comm ρ (lookupG w ρ))
obs (comm ρ (g-irecv x (c-emb g) (c-mu ys h))) rewrite bindAll-dual ys h ρ = ~isend (comm ρ g) (comm (bindAll ys h ρ) h)
obs (comm ρ (g-irecv x (c-var v) (c-emb h))) rewrite lookup-dual v ρ = ~isend (comm ρ (lookupG v ρ)) (comm ρ h)
obs (comm ρ (g-irecv x (c-var v) (c-var w))) rewrite lookup-dual v ρ | lookup-dual w ρ = ~isend (comm ρ (lookupG v ρ)) (comm ρ (lookupG w ρ))
obs (comm ρ (g-irecv x (c-var v) (c-mu ys h))) rewrite lookup-dual v ρ | bindAll-dual ys h ρ = ~isend (comm ρ (lookupG v ρ)) (comm (bindAll ys h ρ) h)
obs (comm ρ (g-irecv x (c-mu xs g) (c-emb h))) rewrite bindAll-dual xs g ρ = ~isend (comm (bindAll xs g ρ) g) (comm ρ h)
obs (comm ρ (g-irecv x (c-mu xs g) (c-var w))) rewrite bindAll-dual xs g ρ | lookup-dual w ρ = ~isend (comm (bindAll xs g ρ) g) (comm ρ (lookupG w ρ))
obs (comm ρ (g-irecv x (c-mu xs g) (c-mu ys h))) rewrite bindAll-dual xs g ρ | bindAll-dual ys h ρ = ~isend (comm (bindAll xs g ρ) g) (comm (bindAll ys h ρ) h)
obs (comm ρ (g-choose (c-emb g) (c-emb h))) = ~branch (comm ρ g) (comm ρ h)
obs (comm ρ (g-choose (c-emb g) (c-var w))) rewrite lookup-dual w ρ = ~branch (comm ρ g) (comm ρ (lookupG w ρ))
obs (comm ρ (g-choose (c-emb g) (c-mu ys h))) rewrite bindAll-dual ys h ρ = ~branch (comm ρ g) (comm (bindAll ys h ρ) h)
obs (comm ρ (g-choose (c-var v) (c-emb h))) rewrite lookup-dual v ρ = ~branch (comm ρ (lookupG v ρ)) (comm ρ h)
obs (comm ρ (g-choose (c-var v) (c-var w))) rewrite lookup-dual v ρ | lookup-dual w ρ = ~branch (comm ρ (lookupG v ρ)) (comm ρ (lookupG w ρ))
obs (comm ρ (g-choose (c-var v) (c-mu ys h))) rewrite lookup-dual v ρ | bindAll-dual ys h ρ = ~branch (comm ρ (lookupG v ρ)) (comm (bindAll ys h ρ) h)
obs (comm ρ (g-choose (c-mu xs g) (c-emb h))) rewrite bindAll-dual xs g ρ = ~branch (comm (bindAll xs g ρ) g) (comm ρ h)
obs (comm ρ (g-choose (c-mu xs g) (c-var w))) rewrite bindAll-dual xs g ρ | lookup-dual w ρ = ~branch (comm (bindAll xs g ρ) g) (comm ρ (lookupG w ρ))
obs (comm ρ (g-choose (c-mu xs g) (c-mu ys h))) rewrite bindAll-dual xs g ρ | bindAll-dual ys h ρ = ~branch (comm (bindAll xs g ρ) g) (comm (bindAll ys h ρ) h)
obs (comm ρ (g-branch (c-emb g) (c-emb h))) = ~choose (comm ρ g) (comm ρ h)
obs (comm ρ (g-branch (c-emb g) (c-var w))) rewrite lookup-dual w ρ = ~choose (comm ρ g) (comm ρ (lookupG w ρ))
obs (comm ρ (g-branch (c-emb g) (c-mu ys h))) rewrite bindAll-dual ys h ρ = ~choose (comm ρ g) (comm (bindAll ys h ρ) h)
obs (comm ρ (g-branch (c-var v) (c-emb h))) rewrite lookup-dual v ρ = ~choose (comm ρ (lookupG v ρ)) (comm ρ h)
obs (comm ρ (g-branch (c-var v) (c-var w))) rewrite lookup-dual v ρ | lookup-dual w ρ = ~choose (comm ρ (lookupG v ρ)) (comm ρ (lookupG w ρ))
obs (comm ρ (g-branch (c-var v) (c-mu ys h))) rewrite lookup-dual v ρ | bindAll-dual ys h ρ = ~choose (comm ρ (lookupG v ρ)) (comm (bindAll ys h ρ) h)
obs (comm ρ (g-branch (c-mu xs g) (c-emb h))) rewrite bindAll-dual xs g ρ = ~choose (comm (bindAll xs g ρ) g) (comm ρ h)
obs (comm ρ (g-branch (c-mu xs g) (c-var w))) rewrite bindAll-dual xs g ρ | lookup-dual w ρ = ~choose (comm (bindAll xs g ρ) g) (comm ρ (lookupG w ρ))
obs (comm ρ (g-branch (c-mu xs g) (c-mu ys h))) rewrite bindAll-dual xs g ρ | bindAll-dual ys h ρ = ~choose (comm (bindAll xs g ρ) g) (comm (bindAll ys h ρ) h)
obs (comm ρ (g-case scrut as)) = ~case (commA ρ as)

aobs (commA _ []) = ~anil
aobs (commA ρ ((c , c-emb g) ∷ as)) = ~acons (comm ρ g) (commA ρ as)
aobs (commA ρ ((c , c-var v) ∷ as)) rewrite lookup-dual v ρ =
  ~acons (comm ρ (lookupG v ρ)) (commA ρ as)
aobs (commA ρ ((c , c-mu xs g) ∷ as)) rewrite bindAll-dual xs g ρ =
  ~acons (comm (bindAll xs g ρ) g) (commA ρ as)

------------------------------------------------------------------------
-- Conformance is a bisimulation. One action agrees, then the
-- continuations conform. The context at a loop head is the context
-- the loop is entered at; a later iteration may extend it, and the
-- next head is checked at that context. A jump does not finish.
------------------------------------------------------------------------

-- A nat instantiates lengths. Every other payload shadows the name.
ext : {A : Ty} → String → ValExpr A → Idx → Idx
ext {nat} x v ρ = bind x (ixOf nat v) (shadow x ρ)
ext {_} x _ ρ = shadow x ρ

data Conf (Γ : Ctx) (ρ : Idx) : PStep ∞Proc → SStep ∞Proto → Set
record Conforms∞ (Γ : Ctx) (ρ : Idx) (p : ∞Proc) (s : ∞Proto) : Set where
  coinductive
  field ok : Conf Γ ρ (act p) (observe s)

data Conf Γ ρ where
  done-end : Conf Γ ρ p-done s-end
  abandon  : ∀ {s} → Conf Γ ρ p-stop s

  put-ok : ∀ {A B v p s} →
    A ≡ applyTy ρ B →
    ValExprOk Γ v →
    Conforms∞ Γ ρ p s →
    Conf Γ ρ (p-put A v p) (s-send B s)

  get-ok : ∀ {A B x p s} →
    A ≡ applyTy ρ B →
    Conforms∞ ((x , A) ∷ Γ) ρ p s →
    Conf Γ ρ (p-get A x p) (s-recv B s)

  dput-ok : ∀ {A B y v p s} →
    A ≡ applyTy ρ B →
    ValExprOk Γ v →
    Conforms∞ Γ (bind y (ixOf A v) (shadow y ρ)) p s →
    Conf Γ ρ (p-put A v p) (s-dsend y B s)

  dget-ok : ∀ {A B x y p s} →
    A ≡ applyTy ρ B →
    Conforms∞ ((x , A) ∷ Γ) (renameIdx y x (shadow y ρ)) p s →
    Conf Γ ρ (p-get A x p) (s-drecv y B s)

  eput-ok : ∀ {y e v p s} →
    ValExprOk Γ v →
    Owed Γ v (resolve ρ e) →
    Conforms∞ Γ ρ p s →
    Conf Γ ρ (p-put nat v p) (s-esend y e s)

  eget-ok : ∀ {y e x p s} →
    Conforms∞ ((x , nat) ∷ Γ) ρ p s →
    Conf Γ ρ (p-get nat x p) (s-erecv y e s)

  iput0-ok : ∀ {y p s t} →
    Conforms∞ Γ (shadow y ρ) p s →
    Conf Γ ρ (p-put bit (lit b0) p) (s-isend y s t)

  iput1-ok : ∀ {y p s t} →
    Conforms∞ Γ (shadow y ρ) p t →
    Conf Γ ρ (p-put bit (lit b1) p) (s-isend y s t)

  iget-ok : ∀ {x y p q s t} →
    Conforms∞ ((x , bit) ∷ Γ) (shadow y ρ) p s →
    Conforms∞ ((x , bit) ∷ Γ) (shadow y ρ) q t →
    Conf Γ ρ (p-iget x p q) (s-irecv y s t)

  pick0-ok : ∀ {p s t} → Conforms∞ Γ ρ p s → Conf Γ ρ (p-pick0 p) (s-choose s t)
  pick1-ok : ∀ {p s t} → Conforms∞ Γ ρ p t → Conf Γ ρ (p-pick1 p) (s-choose s t)
  cover-ok : ∀ {p q s t} →
    Conforms∞ Γ ρ p s → Conforms∞ Γ ρ q t →
    Conf Γ ρ (p-cover p q) (s-branch s t)

open Conforms∞

------------------------------------------------------------------------
-- Two processes. A send meets a receive of that type when the value
-- inhabits it (`sent`, the same premise as `Muro.Meet`). A literal
-- bit meets that arm. Both ends close, or both abandon. The step is
-- one observation; the continuations are the bisimulation.
------------------------------------------------------------------------

data MStep (σ τ : Idx) : PStep ∞Proc → PStep ∞Proc → Set
record Meets∞ (σ τ : Idx) (p q : ∞Proc) : Set where
  coinductive
  field mstep : MStep σ τ (act p) (act q)

data MStep σ τ where
  m-done : MStep σ τ p-done p-done
  m-stop : MStep σ τ p-stop p-stop

  -- A value meets when it inhabits the payload. `sent` is `fits`
  -- for a literal and the computed value for a call. A variable
  -- already inhabits its binding.
  m-put-get : ∀ {A B v x p q} →
    applyTy σ A ≡ applyTy τ B →
    sent v ≡ true →
    Meets∞ σ (ext x v τ) p q →
    MStep σ τ (p-put A v p) (p-get B x q)

  m-get-put : ∀ {A B v x p q} →
    applyTy σ A ≡ applyTy τ B →
    sent v ≡ true →
    Meets∞ (ext x v σ) τ p q →
    MStep σ τ (p-get A x p) (p-put B v q)

  m-pick0 : ∀ {p q r} → Meets∞ σ τ p q → MStep σ τ (p-pick0 p) (p-cover q r)
  m-pick1 : ∀ {p q r} → Meets∞ σ τ p r → MStep σ τ (p-pick1 p) (p-cover q r)
  m-cover0 : ∀ {p q r} → Meets∞ σ τ p r → MStep σ τ (p-cover p q) (p-pick0 r)
  m-cover1 : ∀ {p q r} → Meets∞ σ τ q r → MStep σ τ (p-cover p q) (p-pick1 r)

  m-iget-b0 : ∀ {x p q r} →
    Meets∞ (ext x (lit b0) σ) τ p r →
    MStep σ τ (p-iget x p q) (p-put bit (lit b0) r)
  m-iget-b1 : ∀ {x p q r} →
    Meets∞ (ext x (lit b1) σ) τ q r →
    MStep σ τ (p-iget x p q) (p-put bit (lit b1) r)
  m-b0-iget : ∀ {x p q r} →
    Meets∞ σ (ext x (lit b0) τ) p q →
    MStep σ τ (p-put bit (lit b0) p) (p-iget x q r)
  m-b1-iget : ∀ {x p q r} →
    Meets∞ σ (ext x (lit b1) τ) p r →
    MStep σ τ (p-put bit (lit b1) p) (p-iget x q r)

open Meets∞

------------------------------------------------------------------------
-- The wall. A recursive protocol is spec. A conformance is evidence.
-- A meeting is evidence. Run has none of them.
------------------------------------------------------------------------

data Seat : Mode → Set where
  protocol : ∞Proto → Seat spec
  conforms : ∀ {Γ ρ p s} → Conforms∞ Γ ρ p s → Seat evid
  met      : ∀ {σ τ p q} → Meets∞ σ τ p q → Seat evid

no-run : ¬ Seat run
no-run ()

-- `applyTy` does not reduce on an abstract index. A nat is still a nat.
apply-nat : (ρ : Idx) → applyTy ρ nat ≡ nat
apply-nat none = refl
apply-nat (bind _ _ _) = refl

nat-here : (ρ : Idx) → nat ≡ applyTy ρ nat
nat-here ρ = sym (apply-nat ρ)

nat-eq : (σ τ : Idx) → applyTy σ nat ≡ applyTy τ nat
nat-eq σ τ = trans (apply-nat σ) (sym (apply-nat τ))

------------------------------------------------------------------------
-- A server that receives a nat and sends it back, forever.
-- The client sends `1` and receives a nat, forever.
------------------------------------------------------------------------

natG : GExp
natG = g-recv nat (c-emb (g-send nat (c-var "X")))

natEnv : Env
natEnv = ("X" , natG) ∷ []

natS : ∞Proto
natS = unfold natEnv natG

natPG : PG
natPG = pg-get nat "n" (pc-emb (pg-put nat (var "n") (pc-var "X")))

natPEnv : PEnv
natPEnv = ("X" , natPG) ∷ []

natP : ∞Proc
natP = unfoldP natPEnv natPG

nat-ok : ∀ {Γ ρ} → Conforms∞ Γ ρ natP natS
ok (nat-ok {Γ} {ρ}) = get-ok (nat-here ρ) (nat-put {Γ} {ρ})
  where
    nat-put : ∀ {Γ ρ} →
      Conforms∞ (( "n" , nat ) ∷ Γ) ρ
        (unfoldP natPEnv (pg-put nat (var "n") (pc-var "X")))
        (unfold natEnv (g-send nat (c-var "X")))
    ok (nat-put {Γ} {ρ}) = put-ok (nat-here ρ) (var-ok here) (nat-ok {("n" , nat) ∷ Γ} {ρ})

natBack : ∞Proto
natBack = unfold (dualEnv natEnv) (dualG natG)

nat-dual : dual∞ natS ~ natBack
nat-dual = comm natEnv natG

cliPG : PG
cliPG = pg-put nat (lit one) (pc-emb (pg-get nat "m" (pc-var "Y")))

cliPEnv : PEnv
cliPEnv = ("Y" , cliPG) ∷ []

cliP : ∞Proc
cliP = unfoldP cliPEnv cliPG

cli-ok : ∀ {Γ ρ} → Conforms∞ Γ ρ cliP natBack
ok (cli-ok {Γ} {ρ}) = put-ok (nat-here ρ) (lit-ok refl) (cli-get {Γ} {ρ})
  where
    cli-get : ∀ {Γ ρ} →
      Conforms∞ Γ ρ
        (unfoldP cliPEnv (pg-get nat "m" (pc-var "Y")))
        (unfold (dualEnv natEnv) (g-recv nat (c-var "X")))
    ok (cli-get {Γ} {ρ}) = get-ok (nat-here ρ) (cli-ok {("m" , nat) ∷ Γ} {ρ})

mutual
  forever : ∀ {σ τ} → Meets∞ σ τ natP cliP
  mstep (forever {σ} {τ}) = m-get-put (nat-eq σ τ) refl (forever-put {σ} {τ})

  forever-put : ∀ {σ τ} →
    Meets∞ (ext {nat} "n" (lit one) σ) τ
      (unfoldP natPEnv (pg-put nat (var "n") (pc-var "X")))
      (unfoldP cliPEnv (pg-get nat "m" (pc-var "Y")))
  mstep (forever-put {σ} {τ}) =
    m-put-get (nat-eq (ext {nat} "n" (lit one) σ) τ) refl
      (forever {ext {nat} "n" (lit one) σ} {ext {nat} "m" (var "n") τ})

------------------------------------------------------------------------
-- A bit chooses whether to repeat. `b0` receives a nat, sends it
-- back, and repeats. `b1` ends. The client does that once.
------------------------------------------------------------------------

routeG : GExp
routeG = g-irecv "b"
  (c-emb (g-recv nat (c-emb (g-send nat (c-var "X")))))
  (c-emb g-end)

routeEnv : Env
routeEnv = ("X" , routeG) ∷ []

routeS : ∞Proto
routeS = unfold routeEnv routeG

routePG : PG
routePG = pg-iget "b"
  (pc-emb (pg-get nat "n" (pc-emb (pg-put nat (var "n") (pc-var "X")))))
  (pc-emb pg-done)

routePEnv : PEnv
routePEnv = ("X" , routePG) ∷ []

routeP : ∞Proc
routeP = unfoldP routePEnv routePG

route-ok : ∀ {Γ ρ} → Conforms∞ Γ ρ routeP routeS
ok (route-ok {Γ} {ρ}) = iget-ok (route-arm {Γ} {ρ}) (route-end {Γ} {ρ})
  where
    route-put : ∀ {Γ ρ} →
      Conforms∞ (("n" , nat) ∷ ("b" , bit) ∷ Γ) (shadow "b" ρ)
        (unfoldP routePEnv (pg-put nat (var "n") (pc-var "X")))
        (unfold routeEnv (g-send nat (c-var "X")))
    ok (route-put {Γ} {ρ}) =
      put-ok (nat-here (shadow "b" ρ)) (var-ok here)
        (route-ok {("n" , nat) ∷ ("b" , bit) ∷ Γ} {shadow "b" ρ})

    route-arm : ∀ {Γ ρ} →
      Conforms∞ (("b" , bit) ∷ Γ) (shadow "b" ρ)
        (unfoldP routePEnv (pg-get nat "n" (pc-emb (pg-put nat (var "n") (pc-var "X")))))
        (unfold routeEnv (g-recv nat (c-emb (g-send nat (c-var "X")))))
    ok (route-arm {Γ} {ρ}) = get-ok (nat-here (shadow "b" ρ)) (route-put {Γ} {ρ})

    route-end : ∀ {Γ ρ} →
      Conforms∞ (("b" , bit) ∷ Γ) (shadow "b" ρ)
        (unfoldP routePEnv pg-done)
        (unfold routeEnv g-end)
    ok route-end = done-end

oncePG : PG
oncePG = pg-put bit (lit b0)
  (pc-emb (pg-put nat (lit one)
    (pc-emb (pg-get nat "k"
      (pc-emb (pg-put bit (lit b1) (pc-emb pg-done)))))))

onceP : ∞Proc
onceP = unfoldP [] oncePG

routeBack : ∞Proto
routeBack = unfold (dualEnv routeEnv) (dualG routeG)

route-dual : dual∞ routeS ~ routeBack
route-dual = comm routeEnv routeG

once-ok : ∀ {Γ} → Conforms∞ Γ none onceP routeBack
ok (once-ok {Γ}) = iput0-ok (once-nat {Γ})
  where
    once-done : ∀ {Γ} →
      Conforms∞ (("k" , nat) ∷ Γ) (shadow "b" (shadow "b" none))
        (unfoldP [] pg-done)
        (unfold (dualEnv routeEnv) g-end)
    ok once-done = done-end

    once-stop : ∀ {Γ} →
      Conforms∞ (("k" , nat) ∷ Γ) (shadow "b" none)
        (unfoldP [] (pg-put bit (lit b1) (pc-emb pg-done)))
        routeBack
    ok (once-stop {Γ}) = iput1-ok (once-done {Γ})

    once-get : ∀ {Γ} →
      Conforms∞ Γ (shadow "b" none)
        (unfoldP [] (pg-get nat "k"
          (pc-emb (pg-put bit (lit b1) (pc-emb pg-done)))))
        (unfold (dualEnv routeEnv) (g-recv nat (c-var "X")))
    ok (once-get {Γ}) = get-ok (nat-here (shadow "b" none)) (once-stop {Γ})

    once-nat : ∀ {Γ} →
      Conforms∞ Γ (shadow "b" none)
        (unfoldP [] (pg-put nat (lit one)
          (pc-emb (pg-get nat "k"
            (pc-emb (pg-put bit (lit b1) (pc-emb pg-done)))))))
        (unfold (dualEnv routeEnv)
          (g-send nat (c-emb (g-recv nat (c-var "X")))))
    ok (once-nat {Γ}) = put-ok (nat-here (shadow "b" none)) (lit-ok refl) (once-get {Γ})

wire : ∀ {σ τ} → Meets∞ σ τ routeP onceP
mstep (wire {σ} {τ}) = m-iget-b0 (wire-nat {ext "b" (lit b0) σ} {τ})
  where
    wire-done : ∀ {σ τ} →
      Meets∞ σ τ (unfoldP routePEnv pg-done) (unfoldP [] pg-done)
    mstep wire-done = m-done

    wire-end : ∀ {σ τ} →
      Meets∞ σ τ
        routeP
        (unfoldP [] (pg-put bit (lit b1) (pc-emb pg-done)))
    mstep (wire-end {σ} {τ}) = m-iget-b1 (wire-done {ext "b" (lit b1) σ} {τ})

    wire-back : ∀ {σ τ} →
      Meets∞ σ τ
        (unfoldP routePEnv (pg-put nat (var "n") (pc-var "X")))
        (unfoldP [] (pg-get nat "k"
          (pc-emb (pg-put bit (lit b1) (pc-emb pg-done)))))
    mstep (wire-back {σ} {τ}) =
      m-put-get (nat-eq σ τ) refl (wire-end {σ} {ext {nat} "k" (var "n") τ})

    wire-nat : ∀ {σ τ} →
      Meets∞ σ τ
        (unfoldP routePEnv (pg-get nat "n" (pc-emb (pg-put nat (var "n") (pc-var "X")))))
        (unfoldP [] (pg-put nat (lit one)
          (pc-emb (pg-get nat "k"
            (pc-emb (pg-put bit (lit b1) (pc-emb pg-done)))))))
    mstep (wire-nat {σ} {τ}) =
      m-get-put (nat-eq σ τ) refl (wire-back {ext {nat} "n" (lit one) σ} {τ})

------------------------------------------------------------------------
-- A declared data payload inside `rec`. `Bool` is sent forever.
-- `applyTy` does not reduce on an abstract index. A declaration with
-- no arguments is still that declaration.
------------------------------------------------------------------------

boolDecl : Decl
boolDecl = mkDecl "Bool" nzero (ctor "true" [] ∷ ctor "false" [] ∷ [])

boolTy : Ty
boolTy = dat boolDecl []

trueV : Val boolTy
trueV = con "true" snil

noneV : Val boolTy
noneV = con "none" snil

apply-nil : ∀ {d} (ρ : Idx) → applyTy ρ (dat d []) ≡ dat d []
apply-nil none = refl
apply-nil (bind _ _ _) = refl

bool-eq : (σ τ : Idx) → applyTy σ boolTy ≡ applyTy τ boolTy
bool-eq σ τ = trans (apply-nil {boolDecl} σ) (sym (apply-nil {boolDecl} τ))

flagSyn : SExp
flagSyn = mu "X" (send boolTy (svar "X"))

flagC : CExp
flagC = c-mu ("X" ∷ []) (g-send boolTy (c-var "X"))

flag-elab : elabC [] flagSyn ≡ good flagC
flag-elab = refl

flagG : GExp
flagG = g-send boolTy (c-var "X")

flagEnv : Env
flagEnv = ("X" , flagG) ∷ []

flagS : ∞Proto
flagS = unfold flagEnv flagG

flagPG : PG
flagPG = pg-put boolTy (lit trueV) (pc-var "X")

flagPEnv : PEnv
flagPEnv = ("X" , flagPG) ∷ []

flagP : ∞Proc
flagP = unfoldP flagPEnv flagPG

flag-ok : ∀ {Γ ρ} → Conforms∞ Γ ρ flagP flagS
ok (flag-ok {Γ} {ρ}) = put-ok (sym (apply-nil ρ)) (lit-ok refl) (flag-ok {Γ} {ρ})

flagBack : ∞Proto
flagBack = unfold (dualEnv flagEnv) (dualG flagG)

flag-dual : dual∞ flagS ~ flagBack
flag-dual = comm flagEnv flagG

downG : GExp
downG = g-recv boolTy (c-var "Y")

downEnv : Env
downEnv = ("Y" , downG) ∷ []

downPG : PG
downPG = pg-get boolTy "b" (pc-var "Y")

downPEnv : PEnv
downPEnv = ("Y" , downPG) ∷ []

downP : ∞Proc
downP = unfoldP downPEnv downPG

flag-meet : ∀ {σ τ} → Meets∞ σ τ flagP downP
mstep (flag-meet {σ} {τ}) =
  m-put-get (bool-eq σ τ) refl
    (flag-meet {σ} {ext {boolTy} "b" (lit trueV) τ})

-- A constructor the declaration does not have has no meeting.
missPG : PG
missPG = pg-put boolTy (lit noneV) (pc-var "Z")

missPEnv : PEnv
missPEnv = ("Z" , missPG) ∷ []

missP : ∞Proc
missP = unfoldP missPEnv missPG

miss-flag : ∀ {σ τ} → ¬ Meets∞ σ τ missP downP
miss-flag {σ} {τ} m = bad (mstep m)
  where
    bad : MStep σ τ (act missP) (act downP) → ⊥
    bad (m-put-get _ () _)

------------------------------------------------------------------------
-- A computed put inside `rec`. Each turn sends the value `effective`
-- computes, and the other end receives it. The loop is guarded by
-- that action.
------------------------------------------------------------------------

maybe-eq : (ρ : Idx) → applyTy ρ maybeBool ≡ maybeBool
maybe-eq none = refl
maybe-eq (bind _ _ _) = refl

loop-ty : (σ τ : Idx) → applyTy σ maybeBool ≡ applyTy τ maybeBool
loop-ty σ τ = trans (maybe-eq σ) (sym (maybe-eq τ))

loopSyn : SExp
loopSyn = mu "X" (send maybeBool (svar "X"))

loopC : CExp
loopC = c-mu ("X" ∷ []) (g-send maybeBool (c-var "X"))

loop-elab : elabC [] loopSyn ≡ good loopC
loop-elab = refl

loopG : GExp
loopG = g-send maybeBool (c-var "X")

loopEnv : Env
loopEnv = ("X" , loopG) ∷ []

loopS : ∞Proto
loopS = unfold loopEnv loopG

loopPG : PG
loopPG = pg-put maybeBool effCall (pc-var "X")

loopPEnv : PEnv
loopPEnv = ("X" , loopPG) ∷ []

loopP : ∞Proc
loopP = unfoldP loopPEnv loopPG

loop-ok : ∀ {Γ ρ} → Conforms∞ Γ ρ loopP loopS
ok (loop-ok {Γ} {ρ}) = put-ok (sym (maybe-eq ρ)) (call-ok refl refl) (loop-ok {Γ} {ρ})

loopBack : ∞Proto
loopBack = unfold (dualEnv loopEnv) (dualG loopG)

loop-dual : dual∞ loopS ~ loopBack
loop-dual = comm loopEnv loopG

loopDownG : GExp
loopDownG = g-recv maybeBool (c-var "Y")

loopDownEnv : Env
loopDownEnv = ("Y" , loopDownG) ∷ []

loopDownPG : PG
loopDownPG = pg-get maybeBool "m" (pc-var "Y")

loopDownPEnv : PEnv
loopDownPEnv = ("Y" , loopDownPG) ∷ []

loopDown : ∞Proc
loopDown = unfoldP loopDownPEnv loopDownPG

loop-meet : ∀ {σ τ} → Meets∞ σ τ loopP loopDown
mstep (loop-meet {σ} {τ}) =
  m-put-get (loop-ty σ τ) refl
    (loop-meet {σ} {ext {maybeBool} "m" effCall τ})

------------------------------------------------------------------------
-- `stream n` sends a nat at most `n` and continues as `stream (suc n)`.
-- The self-call sits under the evidence send, so the copattern is
-- guarded. `dual` swaps that send for a receive and keeps the next
-- counter. Zero is at most every bound, so one process conforms at
-- every counter. Both orders meet.
------------------------------------------------------------------------

stream : ℕ → ∞Proto
observe (stream n) = s-esend "d" (nlit n) (stream (nsuc n))

streamDual : ℕ → ∞Proto
observe (streamDual n) = s-erecv "d" (nlit n) (streamDual (nsuc n))

puts : ∞Proc
act puts = p-put nat (lit zero) puts

takes : ∞Proc
act takes = p-get nat "d" takes

stream-ok : (n : ℕ) → ∀ {Γ ρ} → Conforms∞ Γ ρ puts (stream n)
ok (stream-ok n {Γ} {ρ}) =
  eput-ok (lit-ok refl) (owed (lit-le z≤n)) (stream-ok (nsuc n) {Γ} {ρ})

stream-dual-ok : (n : ℕ) → ∀ {Γ ρ} → Conforms∞ Γ ρ takes (dual∞ (stream n))
ok (stream-dual-ok n {Γ} {ρ}) =
  eget-ok (stream-dual-ok (nsuc n) {("d" , nat) ∷ Γ} {ρ})

stream~ : (n : ℕ) → dual∞ (stream n) ~ streamDual n
obs (stream~ n) = ~erecv (stream~ (nsuc n))

stream-meet : ∀ {σ τ} → Meets∞ σ τ puts takes
mstep (stream-meet {σ} {τ}) =
  m-put-get (nat-eq σ τ) refl
    (stream-meet {σ} {ext {nat} "d" (lit zero) τ})

stream-meet-swap : ∀ {σ τ} → Meets∞ σ τ takes puts
mstep (stream-meet-swap {σ} {τ}) =
  m-get-put (nat-eq σ τ) refl
    (stream-meet-swap {ext {nat} "d" (lit zero) σ} {τ})

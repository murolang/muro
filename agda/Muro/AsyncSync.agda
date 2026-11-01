------------------------------------------------------------------------
-- A synchronous meeting is an asynchronous meeting at buffer 1.
-- The statement is this bound, for every value environment: a larger
-- bound is not proved here. The buffer holds the one message the
-- rendezvous has already sent and not yet taken. The other direction
-- stays empty, so exactly one side can move: the sender while both
-- queues are empty, then the receiver once that message is queued.
-- A full buffer blocks the sender. It is not an error.
--
-- The length index is the expression written on the send, which is
-- the expression `Muro.Meet` instantiates. The queued value is that
-- expression with the sender's names resolved, so an arm matches the
-- value. Either queue starts empty. The value environments may
-- already hold bindings; a literal does not consult them, and a
-- synchronous `mget` only meets a known value.
--
-- Nothing here is added to Tm.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

module Muro.AsyncSync where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; _≤_; _+_) renaming (zero to nzero; suc to nsuc)
open import Data.Nat.Properties using (≤-trans; m≤m+n; m≤n+m)
open import Data.Nat.Show using (show)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.String.Base using (String)
open import Data.String.Properties using (_==_; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Relation.Nullary.Decidable.Core using () renaming (yes to yes′; no to no′)

open import Muro.Session using (Proc; done; stop; put; get; pick0; pick1; cover
  ; iget; mget; Val; ValExpr; Ty; Idx; Ctor; ctor; nthProc
  ; armOf; armExpr; sent; sent?; applyTy; ty≟; known; lit; b0; b1; con; ctorsOf
  ; evalExpr; var; call; tup; natGo; zero; suc
  ; nat; unit; bit; none; bind
  ; pair; rec; vec; dat; Row; FEnv
  ; Spine; snil; scons; PArm; bare; named; prod; fork; pPair; pRec
  ; openNamed; openPair; openRec
  ; rawSpine; lenEnv; substProc; openFork; seek
  ; fieldReply; fwdField; tailPass
  ; pairGrant; pairReply; noteReply
  ; gateTrue; gateFalse; gateNone; gateServer)
open import Muro.Async
open import Muro.Meet using (ext; Meetsρ; done-done; stop-stop; put-get; get-put
  ; pick0-cover; pick1-cover; cover-pick0; cover-pick1
  ; iget-b0; iget-b1; b0-iget; b1-iget; put-mget; mget-put
  ; meets-sym; fieldSender; field-meet; fwd-meet
  ; nothingSender; nothing-meet; tailSender; tail-meet
  ; pairSender; pair-meet; natSender; nat-meet; recSender; rec-meet
  ; gate-true-meet; gate-false-meet; gate-none-meet)

------------------------------------------------------------------------
-- One enabled step. The other side waits, so the class is that step
-- and it has no sibling.
------------------------------------------------------------------------

fromL : ∀ {c c′ lt} →
        reactL c ≡ does c′ lt → reactR c ≡ waits → Safe c′ → Safe c
fromL {c} {c′} {lt} eqL eqR s rewrite eqL | eqR = s-go c′ lt [] s anil

fromR : ∀ {c c′ lt} →
        reactL c ≡ waits → reactR c ≡ does c′ lt → Safe c′ → Safe c
fromR {c} {c′} {lt} eqL eqR s rewrite eqL | eqR = s-go c′ lt [] s anil

------------------------------------------------------------------------
-- At buffer 1 a singleton queue is full, and the opposite queue is
-- empty. Whichever process is running, that side waits.
------------------------------------------------------------------------

fullL : (P Q : Proc) (m : Msg) (lv rv : VEnv) (σ τ : Idx) →
        reactL (mk k1 P Q (m ∷ []) [] lv rv σ τ) ≡ waits
fullL done _ _ _ _ _ _ = refl
fullL stop _ _ _ _ _ _ = refl
fullL (put _ _ _) _ _ _ _ _ _ = refl
fullL (get _ _ _) _ _ _ _ _ _ = refl
fullL (pick0 _) _ _ _ _ _ _ = refl
fullL (pick1 _) _ _ _ _ _ _ = refl
fullL (cover _ _) _ _ _ _ _ _ = refl
fullL (iget _ _ _) _ _ _ _ _ _ = refl
fullL (mget _ _ _) _ _ _ _ _ _ = refl

fullR : (P Q : Proc) (m : Msg) (lv rv : VEnv) (σ τ : Idx) →
        reactR (mk k1 P Q [] (m ∷ []) lv rv σ τ) ≡ waits
fullR _ done _ _ _ _ _ = refl
fullR _ stop _ _ _ _ _ = refl
fullR _ (put _ _ _) _ _ _ _ _ = refl
fullR _ (get _ _ _) _ _ _ _ _ = refl
fullR _ (pick0 _) _ _ _ _ _ = refl
fullR _ (pick1 _) _ _ _ _ _ = refl
fullR _ (cover _ _) _ _ _ _ _ = refl
fullR _ (iget _ _ _) _ _ _ _ _ = refl
fullR _ (mget _ _ _) _ _ _ _ _ = refl

------------------------------------------------------------------------
-- The arm `armOf` returns is the arm `armPick` returns, with the size
-- bound the search records.
------------------------------------------------------------------------

-- `openHit` returns the process `openNamed` returns, with the size
-- of the stored process. The two functions follow one comparison.
open-spec : (k c : String) (xs : List String) (p : Proc) (sp : Spine)
            (ps : List PArm) (R : Proc) →
            openNamed k c xs p sp ≡ just R →
            Σ (size R ≤ size p + sizeArms ps)
              (λ le → openHit k c xs p sp ps ≡ just (R , le))
open-spec k c xs p sp ps R eq with k == c | rawSpine sp
open-spec k c xs p sp ps R () | false | _
open-spec k c xs p sp ps R () | true | nothing
open-spec k c xs p sp ps R eq | true | just rs with lenEnv xs rs
open-spec k c xs p sp ps R () | true | just rs | nothing
open-spec k c xs p sp ps .(substProc e p) refl | true | just rs | just e =
  leSubst e p ps , refl

-- `armPick` on a product arm is `pickArm` of the same environment
-- `armOf` fills. The size is the stored process.
specPair : ∀ {X Y} (a : Val X) (b : Val Y) (x y : String) (p R : Proc) →
  armOf (pair X Y) (tup a b) (prod (pPair x y) p ∷ []) ≡ just R →
  Σ (size R ≤ sizeArms (prod (pPair x y) p ∷ []))
    (λ le → armPick (pair X Y) (tup a b) (prod (pPair x y) p ∷ []) ≡ just (R , le))
specPair a b x y p R eq with openPair x y a b
specPair a b x y p R () | nothing
specPair a b x y p .(substProc e p) refl | just e = leSubst e p [] , refl

specRec : ∀ {fs} (row : Row fs) (bs : List (String × String)) (p R : Proc) →
  armOf (rec fs) (rec row) (prod (pRec bs) p ∷ []) ≡ just R →
  Σ (size R ≤ sizeArms (prod (pRec bs) p ∷ []))
    (λ le → armPick (rec fs) (rec row) (prod (pRec bs) p ∷ []) ≡ just (R , le))
specRec row bs p R eq with openRec bs row
specRec row bs p R () | nothing
specRec row bs p .(substProc e p) refl | just e = leSubst e p [] , refl


-- `openFork` and `seek` case on the comparison. `openForkHit` and
-- `seekHit` abstract the same comparison, so the equality is `refl`.
-- `pickNat` returns the arm `natGo` selects, with the size bound.
pick-spec : (v : Val nat) (ps : List PArm) (i : ℕ) (R : Proc) →
            natGo v ps i ≡ just R →
            Σ (size R ≤ sizeArms ps) (λ le → pickNat v ps i ≡ just (R , le))
pick-spec zero [] _ _ ()
pick-spec zero (bare p ∷ ps) _ .p refl = m≤m+n (size p) (sizeArms ps) , refl
pick-spec zero (named c [] p ∷ ps) i R eq with c == show i
pick-spec zero (named c [] p ∷ ps) i .p refl | true =
  m≤m+n (size p) (sizeArms ps) , refl
pick-spec zero (named c [] p ∷ ps) i R () | false
pick-spec zero (named _ (_ ∷ _) _ ∷ _) _ _ ()
pick-spec zero (prod _ _ ∷ _) _ _ ()
pick-spec zero (fork _ _ _ _ ∷ _) _ _ ()
pick-spec (suc _) [] _ _ ()
pick-spec (suc v) (q ∷ ps) i R eq with pick-spec v ps (nsuc i) R eq
... | le , p rewrite p = ≤-trans le (m≤n+m (sizeArms ps) (armSize q)) , refl

mutual
  openFork-spec : (k c : String) (xs : List String) (y : String) (qs : List PArm)
                  (sp : Spine) (ps : List PArm) (R : Proc) →
                  openFork k c xs y qs sp ≡ just R →
                  Σ (size R ≤ sizeArms qs + sizeArms ps)
                    (λ le → openForkHit k c xs y qs sp ps ≡ just (R , le))
  openFork-spec k c xs y qs sp ps R eq with k == c | rawSpine sp
  openFork-spec k c xs y qs sp ps R () | false | _
  openFork-spec k c xs y qs sp ps R () | true | nothing
  openFork-spec k c xs y qs sp ps R eq | true | just rs with lenEnv xs rs
  openFork-spec k c xs y qs sp ps R () | true | just rs | nothing
  openFork-spec k c xs y qs sp ps R eq | true | just rs | just e =
    seek-spec xs y e qs sp ps R eq

  seek-spec : (xs : List String) (y : String) (e : FEnv) (qs : List PArm)
              (sp : Spine) (ps : List PArm) (R : Proc) →
              seek xs y e qs sp ≡ just R →
              Σ (size R ≤ sizeArms qs + sizeArms ps)
                (λ le → seekHit xs y e qs sp ps ≡ just (R , le))
  seek-spec [] _ _ _ _ _ _ ()
  seek-spec (_ ∷ _) _ _ _ snil _ _ ()
  seek-spec (x ∷ xs) y e qs (scons A v sp) ps R eq with x ≟ y
  seek-spec (x ∷ xs) y e qs (scons A v sp) ps R eq | no′ _ =
    seek-spec xs y e qs sp ps R eq
  seek-spec (x ∷ xs) y e qs (scons A v sp) ps R eq | yes′ _ with armOf A v qs in aeq
  seek-spec (x ∷ xs) y e qs (scons A v sp) ps R () | yes′ _ | nothing
  seek-spec (x ∷ xs) y e qs (scons A v sp) ps .(substProc e p) refl | yes′ _ | just p
    with armPick-spec v qs p aeq
  ... | le , eqA rewrite eqA = boundFork e p qs ps le , refl

  find-spec : (name : String) (sp : Spine) (cs : List Ctor) (ps : List PArm) (R : Proc) →
              nthProc cs name sp ps ≡ just R →
              Σ (size R ≤ sizeArms ps) (λ le → findIn name sp cs ps ≡ just (R , le))
  find-spec _ _ [] _ _ ()
  find-spec _ _ (_ ∷ _) [] _ ()
  find-spec name sp (ctor n _ ∷ cs) (bare P ∷ ps) R eq with name == n
  find-spec name sp (ctor n _ ∷ cs) (bare P ∷ ps) .P refl | true =
    m≤m+n (size P) (sizeArms ps) , refl
  find-spec name sp (ctor n _ ∷ cs) (bare P ∷ ps) R eq | false
    with find-spec name sp cs ps R eq
  ... | le , eqf rewrite eqf =
    ≤-trans le (m≤n+m (sizeArms ps) (size P)) , refl
  find-spec name sp (ctor n _ ∷ cs) (named k xs p ∷ ps) R eq with name == n
  find-spec name sp (ctor n _ ∷ cs) (named k xs p ∷ ps) R eq | true
    with open-spec k name xs p sp ps R eq
  ... | le , eqh rewrite eqh = le , refl
  find-spec name sp (ctor n _ ∷ cs) (named k xs p ∷ ps) R eq | false
    with find-spec name sp cs ps R eq
  ... | le , eqf rewrite eqf =
    ≤-trans le (m≤n+m (sizeArms ps) (size p)) , refl
  find-spec name sp (ctor n _ ∷ cs) (prod _ p ∷ ps) R eq with name == n
  find-spec name sp (ctor n _ ∷ cs) (prod _ p ∷ ps) R () | true
  find-spec name sp (ctor n _ ∷ cs) (prod _ p ∷ ps) R eq | false
    with find-spec name sp cs ps R eq
  ... | le , eqf rewrite eqf =
    ≤-trans le (m≤n+m (sizeArms ps) (size p)) , refl
  find-spec name sp (ctor n _ ∷ cs) (fork k xs y qs ∷ ps) R eq with name == n
  find-spec name sp (ctor n _ ∷ cs) (fork k xs y qs ∷ ps) R eq | true
    with openFork-spec k name xs y qs sp ps R eq
  ... | le , eqh rewrite eqh = le , refl
  find-spec name sp (ctor n _ ∷ cs) (fork k xs y qs ∷ ps) R eq | false
    with find-spec name sp cs ps R eq
  ... | le , eqf rewrite eqf =
    ≤-trans le (m≤n+m (sizeArms ps) (sizeArms qs)) , refl

  armPick-spec : ∀ {A} (u : Val A) (ps : List PArm) (R : Proc) →
                 armOf A u ps ≡ just R →
                 Σ (size R ≤ sizeArms ps) (λ le → armPick A u ps ≡ just (R , le))
  armPick-spec b0 [] _ ()
  armPick-spec b0 (_ ∷ []) _ ()
  armPick-spec b0 (_ ∷ _ ∷ _ ∷ _) _ ()
  armPick-spec b0 (bare P ∷ Q ∷ []) .P refl =
    m≤m+n (size P) (sizeArms (Q ∷ [])) , refl
  armPick-spec b0 (named _ [] P ∷ Q ∷ []) .P refl =
    m≤m+n (size P) (sizeArms (Q ∷ [])) , refl
  armPick-spec b0 (named _ (_ ∷ _) _ ∷ _ ∷ []) _ ()
  armPick-spec b0 (prod _ _ ∷ _ ∷ []) _ ()
  armPick-spec b0 (fork _ _ _ _ ∷ _ ∷ []) _ ()
  armPick-spec b1 [] _ ()
  armPick-spec b1 (_ ∷ []) _ ()
  armPick-spec b1 (_ ∷ _ ∷ _ ∷ _) _ ()
  armPick-spec b1 (A ∷ bare Q ∷ []) .Q refl = b1≤ A (bare Q) , refl
  armPick-spec b1 (A ∷ named c [] Q ∷ []) .Q refl = b1≤ A (named c [] Q) , refl
  armPick-spec b1 (_ ∷ named _ (_ ∷ _) _ ∷ []) _ ()
  armPick-spec b1 (_ ∷ prod _ _ ∷ []) _ ()
  armPick-spec b1 (_ ∷ fork _ _ _ _ ∷ []) _ ()
  armPick-spec {nat} v ps R eq = pick-spec v ps nzero R eq
  armPick-spec {unit} _ _ _ ()
  armPick-spec {vec _ _} _ _ _ ()
  armPick-spec {pair _ _} (tup a b) (prod (pPair x y) p ∷ []) R eq =
    specPair a b x y p R eq
  armPick-spec {pair _ _} (tup _ _) (prod (pRec _) _ ∷ []) _ ()
  armPick-spec {pair _ _} (tup _ _) (bare _ ∷ []) _ ()
  armPick-spec {pair _ _} (tup _ _) (named _ _ _ ∷ []) _ ()
  armPick-spec {pair _ _} (tup _ _) (fork _ _ _ _ ∷ []) _ ()
  armPick-spec {pair _ _} (tup _ _) [] _ ()
  armPick-spec {pair _ _} (tup _ _) (_ ∷ _ ∷ _) _ ()
  armPick-spec {rec _} (rec row) (prod (pRec bs) p ∷ []) R eq =
    specRec row bs p R eq
  armPick-spec {rec _} (rec _) (prod (pPair _ _) _ ∷ []) _ ()
  armPick-spec {rec _} (rec _) (bare _ ∷ []) _ ()
  armPick-spec {rec _} (rec _) (named _ _ _ ∷ []) _ ()
  armPick-spec {rec _} (rec _) (fork _ _ _ _ ∷ []) _ ()
  armPick-spec {rec _} (rec _) [] _ ()
  armPick-spec {rec _} (rec _) (_ ∷ _ ∷ _) _ ()
  armPick-spec {dat d _} (con c sp) ps R eq = find-spec c sp (ctorsOf d) ps R eq

------------------------------------------------------------------------
-- Buffer 1. `lv` and `rv` are the names already received. The
-- meeting's own sends extend them.
------------------------------------------------------------------------

apply-bit : (ρ : Idx) → applyTy ρ bit ≡ bit
apply-bit none = refl
apply-bit (bind _ _ _) = refl

var-arm : ∀ {A} {x : String} {ps : List PArm} {R : Proc} →
          armExpr (var {A} x) ps ≡ just R → ⊥
var-arm ()

ready-arm : ∀ {A} (e : VEnv) (v : ValExpr A) (ps : List PArm) (R : Proc) →
            sent v ≡ true → armExpr v ps ≡ just R →
            Σ (size R ≤ sizeArms ps)
              (λ le → armExprPick (prepare e v) ps ≡ just (R , le))
ready-arm _ (lit u) ps R _ eq = armPick-spec u ps R eq
ready-arm {A} _ (var x) ps R _ eq = ⊥-elim (var-arm {A} {x} {ps} {R} eq)
ready-arm e (call {A} f as) ps R fv eq with evalExpr (call {A} f as)
ready-arm e (call {A} f as) ps R () _ | nothing
ready-arm e (call {A} f as) ps R _ eq | just u = armPick-spec u ps R eq

meets-async : ∀ {σ τ P Q} (lv rv : VEnv) → Meetsρ σ τ P Q →
              Safe (mk k1 P Q [] [] lv rv σ τ)

meets-async _ _ done-done = s-final refl refl refl refl
meets-async _ _ stop-stop = s-final refl refl refl refl

meets-async {σ} {τ} lv rv (put-get {A} {B} {v} {x} {P} {Q} tyeq fv m) =
  fromL (put-go fv) refl (fromR (fullL P (get B x Q) wire lv rv σ τ) (get-go tyeq) next)
  where
  c₀ : Conf
  c₀ = mk k1 (put A v P) (get B x Q) [] [] lv rv σ τ
  wire : Msg
  wire = mkPayL c₀ v
  c₁ : Conf
  c₁ = mk k1 P (get B x Q) (wire ∷ []) [] lv rv σ τ
  rv′ : VEnv
  rv′ = bindV x (car A v (prepare lv v)) rv
  τ′ : Idx
  τ′ = ext x v τ
  put-go : sent v ≡ true → reactL c₀ ≡ does c₁ (ltSucL (size P) (get B x Q))
  put-go p with sent? v
  ... | yes′ _ = refl
  ... | no′ ¬p = ⊥-elim (¬p p)
  get-go : applyTy σ A ≡ applyTy τ B →
           reactR c₁ ≡ does (mk k1 P Q [] [] lv rv′ σ τ′) (ltSucR P (size Q))
  get-go eq with ty≟ (applyTy τ B) (applyTy σ A)
  ... | yes′ _ = refl
  ... | no′ ¬eq = ⊥-elim (¬eq (sym eq))
  next : Safe (mk k1 P Q [] [] lv rv′ σ τ′)
  next = meets-async lv rv′ m

meets-async {σ} {τ} lv rv (get-put {A} {B} {v} {x} {P} {Q} tyeq fv m) =
  fromR refl (put-go fv) (fromL (get-go tyeq) (fullR (get A x P) Q wire lv rv σ τ) next)
  where
  c₀ : Conf
  c₀ = mk k1 (get A x P) (put B v Q) [] [] lv rv σ τ
  wire : Msg
  wire = mkPayR c₀ v
  c₁ : Conf
  c₁ = mk k1 (get A x P) Q [] (wire ∷ []) lv rv σ τ
  lv′ : VEnv
  lv′ = bindV x (car B v (prepare rv v)) lv
  σ′ : Idx
  σ′ = ext x v σ
  put-go : sent v ≡ true → reactR c₀ ≡ does c₁ (ltSucR (get A x P) (size Q))
  put-go p with sent? v
  ... | yes′ _ = refl
  ... | no′ ¬p = ⊥-elim (¬p p)
  get-go : applyTy σ A ≡ applyTy τ B →
           reactL c₁ ≡ does (mk k1 P Q [] [] lv′ rv σ′ τ) (ltSucL (size P) Q)
  get-go eq with ty≟ (applyTy σ A) (applyTy τ B)
  ... | yes′ _ = refl
  ... | no′ ¬eq = ⊥-elim (¬eq eq)
  next : Safe (mk k1 P Q [] [] lv′ rv σ′ τ)
  next = meets-async lv′ rv m

meets-async {σ} {τ} lv rv (pick0-cover {P} {Q} {R} m) =
  fromL refl refl (fromR (fullL P (cover Q R) (lab false) lv rv σ τ) refl next)
  where
  next : Safe (mk k1 P Q [] [] lv rv σ τ)
  next = meets-async lv rv m

meets-async {σ} {τ} lv rv (pick1-cover {P} {Q} {R} m) =
  fromL refl refl (fromR (fullL P (cover Q R) (lab true) lv rv σ τ) refl next)
  where
  next : Safe (mk k1 P R [] [] lv rv σ τ)
  next = meets-async lv rv m

meets-async {σ} {τ} lv rv (cover-pick0 {P} {Q} {R} m) =
  fromR refl refl (fromL refl (fullR (cover P Q) R (lab false) lv rv σ τ) next)
  where
  next : Safe (mk k1 P R [] [] lv rv σ τ)
  next = meets-async lv rv m

meets-async {σ} {τ} lv rv (cover-pick1 {P} {Q} {R} m) =
  fromR refl refl (fromL refl (fullR (cover P Q) R (lab true) lv rv σ τ) next)
  where
  next : Safe (mk k1 Q R [] [] lv rv σ τ)
  next = meets-async lv rv m

meets-async {σ} {τ} lv rv (b0-iget {x} {P} {Q} {R} m) =
  fromL refl refl (fromR (fullL P (iget x Q R) wire lv rv σ τ) bit-go next)
  where
  c₀ : Conf
  c₀ = mk k1 (put bit (lit b0) P) (iget x Q R) [] [] lv rv σ τ
  wire : Msg
  wire = mkPayL c₀ (lit b0)
  ca : Carrier
  ca = car bit (lit b0) (lit b0)
  c₁ : Conf
  c₁ = mk k1 P (iget x Q R) (wire ∷ []) [] lv rv σ τ
  bit-go : reactR c₁ ≡
           does (mk k1 P Q [] [] lv (bindV x ca rv) σ (ext x (lit b0) τ))
                (igR0 c₁ x Q R refl)
  bit-go rewrite apply-bit σ = refl
  next : Safe (mk k1 P Q [] [] lv (bindV x ca rv) σ (ext x (lit b0) τ))
  next = meets-async lv (bindV x ca rv) m

meets-async {σ} {τ} lv rv (b1-iget {x} {P} {Q} {R} m) =
  fromL refl refl (fromR (fullL P (iget x Q R) wire lv rv σ τ) bit-go next)
  where
  c₀ : Conf
  c₀ = mk k1 (put bit (lit b1) P) (iget x Q R) [] [] lv rv σ τ
  wire : Msg
  wire = mkPayL c₀ (lit b1)
  ca : Carrier
  ca = car bit (lit b1) (lit b1)
  c₁ : Conf
  c₁ = mk k1 P (iget x Q R) (wire ∷ []) [] lv rv σ τ
  bit-go : reactR c₁ ≡
           does (mk k1 P R [] [] lv (bindV x ca rv) σ (ext x (lit b1) τ))
                (igR1 c₁ x Q R refl)
  bit-go rewrite apply-bit σ = refl
  next : Safe (mk k1 P R [] [] lv (bindV x ca rv) σ (ext x (lit b1) τ))
  next = meets-async lv (bindV x ca rv) m

meets-async {σ} {τ} lv rv (iget-b0 {x} {P} {Q} {R} m) =
  fromR refl refl (fromL bit-go (fullR (iget x P Q) R wire lv rv σ τ) next)
  where
  c₀ : Conf
  c₀ = mk k1 (iget x P Q) (put bit (lit b0) R) [] [] lv rv σ τ
  wire : Msg
  wire = mkPayR c₀ (lit b0)
  ca : Carrier
  ca = car bit (lit b0) (lit b0)
  c₁ : Conf
  c₁ = mk k1 (iget x P Q) R [] (wire ∷ []) lv rv σ τ
  bit-go : reactL c₁ ≡
           does (mk k1 P R [] [] (bindV x ca lv) rv (ext x (lit b0) σ) τ)
                (igL0 c₁ x P Q refl)
  bit-go rewrite apply-bit τ = refl
  next : Safe (mk k1 P R [] [] (bindV x ca lv) rv (ext x (lit b0) σ) τ)
  next = meets-async (bindV x ca lv) rv m

meets-async {σ} {τ} lv rv (iget-b1 {x} {P} {Q} {R} m) =
  fromR refl refl (fromL bit-go (fullR (iget x P Q) R wire lv rv σ τ) next)
  where
  c₀ : Conf
  c₀ = mk k1 (iget x P Q) (put bit (lit b1) R) [] [] lv rv σ τ
  wire : Msg
  wire = mkPayR c₀ (lit b1)
  ca : Carrier
  ca = car bit (lit b1) (lit b1)
  c₁ : Conf
  c₁ = mk k1 (iget x P Q) R [] (wire ∷ []) lv rv σ τ
  bit-go : reactL c₁ ≡
           does (mk k1 Q R [] [] (bindV x ca lv) rv (ext x (lit b1) σ) τ)
                (igL1 c₁ x P Q refl)
  bit-go rewrite apply-bit τ = refl
  next : Safe (mk k1 Q R [] [] (bindV x ca lv) rv (ext x (lit b1) σ) τ)
  next = meets-async (bindV x ca lv) rv m

meets-async {σ} {τ} lv rv (put-mget {A} {B} {v} {x} {ps} {R} {P} tyeq fv sel m) =
  fromL (put-go fv) refl
        (fromR (fullL P (mget B x ps) wire lv rv σ τ) (arm-go tyeq fv sel) next)
  where
  c₀ : Conf
  c₀ = mk k1 (put A v P) (mget B x ps) [] [] lv rv σ τ
  wire : Msg
  wire = mkPayL c₀ v
  c₁ : Conf
  c₁ = mk k1 P (mget B x ps) (wire ∷ []) [] lv rv σ τ
  rv′ : VEnv
  rv′ = bindV x (car A v (prepare lv v)) rv
  τ′ : Idx
  τ′ = ext x v τ
  put-go : sent v ≡ true → reactL c₀ ≡ does c₁ (ltSucL (size P) (mget B x ps))
  put-go p with sent? v
  ... | yes′ _ = refl
  ... | no′ ¬p = ⊥-elim (¬p p)
  arm-go : (eq : applyTy σ A ≡ applyTy τ B) (p : sent v ≡ true)
           (sel′ : armExpr v ps ≡ just R) →
           reactR c₁ ≡
           does (mk k1 P R [] [] lv rv′ σ τ′)
                (ltArmR P R ps (proj₁ (ready-arm lv v ps R p sel′)))
  arm-go eq p sel′ with ty≟ (applyTy τ B) (applyTy σ A) | ready-arm lv v ps R p sel′
  ... | yes′ _ | le , eqA rewrite eqA = refl
  ... | no′ ¬eq | _ = ⊥-elim (¬eq (sym eq))
  next : Safe (mk k1 P R [] [] lv rv′ σ τ′)
  next = meets-async lv rv′ m

meets-async {σ} {τ} lv rv (mget-put {A} {B} {v} {x} {ps} {R} {P} tyeq fv sel m) =
  fromR refl (put-go fv)
        (fromL (arm-go tyeq fv sel) (fullR (mget A x ps) P wire lv rv σ τ) next)
  where
  c₀ : Conf
  c₀ = mk k1 (mget A x ps) (put B v P) [] [] lv rv σ τ
  wire : Msg
  wire = mkPayR c₀ v
  c₁ : Conf
  c₁ = mk k1 (mget A x ps) P [] (wire ∷ []) lv rv σ τ
  lv′ : VEnv
  lv′ = bindV x (car B v (prepare rv v)) lv
  σ′ : Idx
  σ′ = ext x v σ
  put-go : sent v ≡ true → reactR c₀ ≡ does c₁ (ltSucR (mget A x ps) (size P))
  put-go p with sent? v
  ... | yes′ _ = refl
  ... | no′ ¬p = ⊥-elim (¬p p)
  arm-go : (eq : applyTy σ A ≡ applyTy τ B) (p : sent v ≡ true)
           (sel′ : armExpr v ps ≡ just R) →
           reactL c₁ ≡
           does (mk k1 R P [] [] lv′ rv σ′ τ)
                (ltArmL R ps P (proj₁ (ready-arm rv v ps R p sel′)))
  arm-go eq p sel′ with ty≟ (applyTy σ A) (applyTy τ B) | ready-arm rv v ps R p sel′
  ... | yes′ _ | le , eqA rewrite eqA = refl
  ... | no′ ¬eq | _ = ⊥-elim (¬eq eq)
  next : Safe (mk k1 R P [] [] lv′ rv σ′ τ)
  next = meets-async lv′ rv m

------------------------------------------------------------------------
-- A named arm meets asynchronously. The queued value fills the
-- binders. `just true` evaluates `grant b` to `true`, and forwarding
-- the field sends that `Bool`. Either order is the synchronous
-- meeting at buffer 1. An empty spine and a list tail do the same.
------------------------------------------------------------------------

field-async : Safe (mk k1 fieldSender fieldReply [] [] [] [] none none)
field-async = meets-async [] [] field-meet

field-async-swap : Safe (mk k1 fieldReply fieldSender [] [] [] [] none none)
field-async-swap = meets-async [] [] (meets-sym field-meet)

fwd-async : Safe (mk k1 fieldSender fwdField [] [] [] [] none none)
fwd-async = meets-async [] [] fwd-meet

nothing-async : Safe (mk k1 nothingSender fieldReply [] [] [] [] none none)
nothing-async = meets-async [] [] nothing-meet

tail-async : Safe (mk k1 tailSender tailPass [] [] [] [] none none)
tail-async = meets-async [] [] tail-meet

-- A product arm meets asynchronously. The queued tuple or record
-- fills the binders, and a run in the arm is the value it computes.
pair-async : Safe (mk k1 pairSender pairGrant [] [] [] [] none none)
pair-async = meets-async [] [] pair-meet

pair-async-swap : Safe (mk k1 pairGrant pairSender [] [] [] [] none none)
pair-async-swap = meets-async [] [] (meets-sym pair-meet)

nat-async : Safe (mk k1 natSender pairReply [] [] [] [] none none)
nat-async = meets-async [] [] nat-meet

rec-async : Safe (mk k1 recSender noteReply [] [] [] [] none none)
rec-async = meets-async [] [] rec-meet

-- `just true` sends `rst`. `just false` and `nothing` close. The
-- receiver cases on the field the run reads. Either order is the
-- synchronous meeting at buffer 1.
gate-true-async : Safe (mk k1 gateTrue gateServer [] [] [] [] none none)
gate-true-async = meets-async [] [] gate-true-meet

gate-true-async-swap : Safe (mk k1 gateServer gateTrue [] [] [] [] none none)
gate-true-async-swap = meets-async [] [] (meets-sym gate-true-meet)

gate-false-async : Safe (mk k1 gateFalse gateServer [] [] [] [] none none)
gate-false-async = meets-async [] [] gate-false-meet

gate-false-async-swap : Safe (mk k1 gateServer gateFalse [] [] [] [] none none)
gate-false-async-swap = meets-async [] [] (meets-sym gate-false-meet)

gate-none-async : Safe (mk k1 gateNone gateServer [] [] [] [] none none)
gate-none-async = meets-async [] [] gate-none-meet

gate-none-async-swap : Safe (mk k1 gateServer gateNone [] [] [] [] none none)
gate-none-async-swap = meets-async [] [] (meets-sym gate-none-meet)

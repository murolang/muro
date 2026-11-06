------------------------------------------------------------------------
-- The source configuration and the graph agree on final states.
--
-- A source configuration is final when both focuses are `done` or
-- `stop` and both queues are empty. The graph is final when `halted`
-- is true and both queues are empty. Under a `Hold`, those are the
-- same fact: the unfold's block is the block `lookB` reads.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Carry where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; [])
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

open import Muro.AsyncRec
  using ( Block; bPut; bEcho; bPick0; bPick1; bGet; bCover; bIget; bMget
        ; isHalt; lookB; halted; Graph; RConf; rc; Tok )
open Graph
open import Muro.Temporal using (Step; finish; fin)
open import Muro.Temporal.Pic using (_∈_)
open import Muro.Temporal.Source
  using ( SProc; SConf; abs; CanFinish; HaltF; h-done; h-stop
        ; sput; sget; spick0; spick1; scover; siget; smget )
open SConf
open import Muro.Temporal.Run using (Hold; Cursor)
open import Muro.Temporal.Chase using (unfoldL; unfoldR; Opened)
open import Muro.Temporal.Expose
  using ( Stop; leftStop; rightStop; seenL; seenR; fin-fwd
        ; Leaf; lf-done; lf-stop; lf-put; lf-get; lf-pick0; lf-pick1
        ; lf-cover; lf-iget; lf-mget )
open import Muro.Temporal.Den
  using ( Place; p-act; CovP; Link; headIx
        ; d-put; d-echo; d-pick0; d-pick1; d-get; d-cover; d-iget; d-mget
        ; r-put; r-echo; r-pick0; r-pick1; r-get; r-cover; r-iget; r-mget
        ; cp-act
        ; c-put; c-echo; c-pick0; c-pick1; c-get; c-cover; c-iget; c-mget
        ; lk-put; lk-echo; lk-pick0; lk-pick1; lk-get; lk-cover; lk-iget; lk-mget )

true≢false : true ≡ false → ⊥
true≢false ()

-- A non-halt block on the left makes `halted` false.
deadL : ∀ {g il ir q1 q2 e1 e2 b} →
        lookB (codeL g) il ≡ just b →
        isHalt b ≡ false →
        halted g (rc il ir q1 q2 e1 e2) ≡ true →
        ⊥
deadL {g} {ir = ir} {b = b} eqB nh ht = go (lookB (codeR g) ir) refl
  where
  go : (mr : Maybe Block) → lookB (codeR g) ir ≡ mr → ⊥
  go nothing eqR rewrite eqB | eqR = true≢false (sym ht)
  go (just _) eqR rewrite eqB | eqR | nh = true≢false (sym ht)

-- A non-halt block on the right makes `halted` false. `andb` cases on
-- its first argument, so the left block is split before the right bit.
deadR : ∀ {g il ir q1 q2 e1 e2 b} →
        lookB (codeR g) ir ≡ just b →
        isHalt b ≡ false →
        halted g (rc il ir q1 q2 e1 e2) ≡ true →
        ⊥
deadR {g} {il = il} {b = b} eqB nh ht = go (lookB (codeL g) il) refl
  where
  go : (ml : Maybe Block) → lookB (codeL g) il ≡ ml → ⊥
  go nothing eqL rewrite eqL | eqB = true≢false (sym ht)
  go (just bl) eqL = onH (isHalt bl) refl
    where
    onH : (bit : Bool) → isHalt bl ≡ bit → ⊥
    onH false eq rewrite eqL | eqB | eq = true≢false (sym ht)
    onH true eq rewrite eqL | eqB | eq | nh = true≢false (sym ht)

badPut : ∀ {bs a p n} (pl : Place (sput a p)) →
         CovP pl bs → Link pl → n ≡ headIx pl →
         Σ Block (λ b → (n , b) ∈ bs × isHalt b ≡ false)
badPut (p-act (d-put _ _ _ atom j _ _ _ _ _ _ _ _ _ _) r-put _ _ _)
       (cp-act (c-put mem _)) (lk-put eqi _ _ _) ix =
  bPut atom j , subst (λ z → (z , bPut atom j) ∈ _) (sym (trans ix eqi)) mem , refl
badPut (p-act (d-echo _ _ _ _ sX j _ _ _ _ _ _ _ _ _ _) r-echo _ _ _)
       (cp-act (c-echo mem _)) (lk-echo eqi _ _ _) ix =
  bEcho sX j , subst (λ z → (z , bEcho sX j) ∈ _) (sym (trans ix eqi)) mem , refl

badPick0 : ∀ {bs p n} (pl : Place (spick0 p)) →
           CovP pl bs → Link pl → n ≡ headIx pl →
           Σ Block (λ b → (n , b) ∈ bs × isHalt b ≡ false)
badPick0 (p-act (d-pick0 _ _ j _ _ _ _ _ _ _ _ _) r-pick0 _ _ _)
         (cp-act (c-pick0 mem _)) (lk-pick0 eqi _ _ _) ix =
  bPick0 j , subst (λ z → (z , bPick0 j) ∈ _) (sym (trans ix eqi)) mem , refl

badPick1 : ∀ {bs p n} (pl : Place (spick1 p)) →
           CovP pl bs → Link pl → n ≡ headIx pl →
           Σ Block (λ b → (n , b) ∈ bs × isHalt b ≡ false)
badPick1 (p-act (d-pick1 _ _ j _ _ _ _ _ _ _ _ _) r-pick1 _ _ _)
         (cp-act (c-pick1 mem _)) (lk-pick1 eqi _ _ _) ix =
  bPick1 j , subst (λ z → (z , bPick1 j) ∈ _) (sym (trans ix eqi)) mem , refl

badGet : ∀ {bs t x p n} (pl : Place (sget t x p)) →
         CovP pl bs → Link pl → n ≡ headIx pl →
         Σ Block (λ b → (n , b) ∈ bs × isHalt b ≡ false)
badGet (p-act (d-get _ s t _ j _ _ _ _ _ _ _ _ _) r-get _ _ _)
       (cp-act (c-get mem _)) (lk-get eqi _ _ _) ix =
  bGet t s j , subst (λ z → (z , bGet t s j) ∈ _) (sym (trans ix eqi)) mem , refl

badCover : ∀ {bs p q n} (pl : Place (scover p q)) →
           CovP pl bs → Link pl → n ≡ headIx pl →
           Σ Block (λ b → (n , b) ∈ bs × isHalt b ≡ false)
badCover (p-act (d-cover _ _ i j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) r-cover _ _ _)
         (cp-act (c-cover mem _ _)) (lk-cover eqi _ _ _ _) ix =
  bCover i j , subst (λ z → (z , bCover i j) ∈ _) (sym (trans ix eqi)) mem , refl

badIget : ∀ {bs x p q n} (pl : Place (siget x p q)) →
          CovP pl bs → Link pl → n ≡ headIx pl →
          Σ Block (λ b → (n , b) ∈ bs × isHalt b ≡ false)
badIget (p-act (d-iget _ s _ i j _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) r-iget _ _ _)
        (cp-act (c-iget mem _ _)) (lk-iget eqi _ _ _ _) ix =
  bIget s i j , subst (λ z → (z , bIget s i j) ∈ _) (sym (trans ix eqi)) mem , refl

badMget : ∀ {bs t x as n} (pl : Place (smget t x as)) →
          CovP pl bs → Link pl → n ≡ headIx pl →
          Σ Block (λ b → (n , b) ∈ bs × isHalt b ≡ false)
badMget (p-act (d-mget _ s t _ named _ _ _ _ _ _ _ _) r-mget _ _ _)
        (cp-act (c-mget mem _)) (lk-mget eqi _ _ _) ix =
  bMget t s named , subst (λ z → (z , bMget t s named) ∈ _) (sym (trans ix eqi)) mem , refl

-- The focus is a halt. An action focus denotes a block `isHalt` rejects,
-- which cannot be what `halted` read.
asHaltL : ∀ {g c f ρ′ pend′} (h : Hold g c) →
          Stop (Hold.bsL h) (Cursor.echoNs (Hold.leftC h))
               (il c) (slotL c) (envIL c) ρ′ pend′ f →
          halted g (abs c) ≡ true →
          HaltF f
asHaltL {g} {c} {f} h st ht =
  go (Stop.pl st) (Stop.cv st) (Stop.lk st) (Stop.ix st) (Stop.lf st)
  where
  refuse : ∀ {b} → (il c , b) ∈ Hold.bsL h → isHalt b ≡ false → HaltF f
  refuse mem nh =
    ⊥-elim (deadL {g} {il = il c} {ir = ir c} {q1 = l2r c} {q2 = r2l c}
                  {e1 = el c} {e2 = er c} (seenL h mem) nh ht)
  go : ∀ {proc} (pl : Place proc) → CovP pl (Hold.bsL h) → Link pl →
       il c ≡ headIx pl → Leaf f proc → HaltF f
  go _ _ _ _ lf-done = h-done
  go _ _ _ _ lf-stop = h-stop
  go pl cv lk ix lf-put =
    let got = badPut pl cv lk ix in refuse (proj₁ (proj₂ got)) (proj₂ (proj₂ got))
  go pl cv lk ix lf-pick0 =
    let got = badPick0 pl cv lk ix in refuse (proj₁ (proj₂ got)) (proj₂ (proj₂ got))
  go pl cv lk ix lf-pick1 =
    let got = badPick1 pl cv lk ix in refuse (proj₁ (proj₂ got)) (proj₂ (proj₂ got))
  go pl cv lk ix lf-get =
    let got = badGet pl cv lk ix in refuse (proj₁ (proj₂ got)) (proj₂ (proj₂ got))
  go pl cv lk ix lf-cover =
    let got = badCover pl cv lk ix in refuse (proj₁ (proj₂ got)) (proj₂ (proj₂ got))
  go pl cv lk ix lf-iget =
    let got = badIget pl cv lk ix in refuse (proj₁ (proj₂ got)) (proj₂ (proj₂ got))
  go pl cv lk ix lf-mget =
    let got = badMget pl cv lk ix in refuse (proj₁ (proj₂ got)) (proj₂ (proj₂ got))

asHaltR : ∀ {g c f ρ′ pend′} (h : Hold g c) →
          Stop (Hold.bsR h) (Cursor.echoNs (Hold.rightC h))
               (ir c) (slotR c) (envIR c) ρ′ pend′ f →
          halted g (abs c) ≡ true →
          HaltF f
asHaltR {g} {c} {f} h st ht =
  go (Stop.pl st) (Stop.cv st) (Stop.lk st) (Stop.ix st) (Stop.lf st)
  where
  refuse : ∀ {b} → (ir c , b) ∈ Hold.bsR h → isHalt b ≡ false → HaltF f
  refuse mem nh =
    ⊥-elim (deadR {g} {il = il c} {ir = ir c} {q1 = l2r c} {q2 = r2l c}
                  {e1 = el c} {e2 = er c} (seenR h mem) nh ht)
  go : ∀ {proc} (pl : Place proc) → CovP pl (Hold.bsR h) → Link pl →
       ir c ≡ headIx pl → Leaf f proc → HaltF f
  go _ _ _ _ lf-done = h-done
  go _ _ _ _ lf-stop = h-stop
  go pl cv lk ix lf-put =
    let got = badPut pl cv lk ix in refuse (proj₁ (proj₂ got)) (proj₂ (proj₂ got))
  go pl cv lk ix lf-pick0 =
    let got = badPick0 pl cv lk ix in refuse (proj₁ (proj₂ got)) (proj₂ (proj₂ got))
  go pl cv lk ix lf-pick1 =
    let got = badPick1 pl cv lk ix in refuse (proj₁ (proj₂ got)) (proj₂ (proj₂ got))
  go pl cv lk ix lf-get =
    let got = badGet pl cv lk ix in refuse (proj₁ (proj₂ got)) (proj₂ (proj₂ got))
  go pl cv lk ix lf-cover =
    let got = badCover pl cv lk ix in refuse (proj₁ (proj₂ got)) (proj₂ (proj₂ got))
  go pl cv lk ix lf-iget =
    let got = badIget pl cv lk ix in refuse (proj₁ (proj₂ got)) (proj₂ (proj₂ got))
  go pl cv lk ix lf-mget =
    let got = badMget pl cv lk ix in refuse (proj₁ (proj₂ got)) (proj₂ (proj₂ got))

-- `CanFinish` is the source final state. The three equations are the
-- graph final state: `l2rOf` and `r2lOf` of `abs` are the source queues.
graph-final : ∀ {g c} → Hold g c → CanFinish c →
              l2r c ≡ [] × r2l c ≡ [] × halted g (abs c) ≡ true
graph-final {g} {c} h (_ , _ , _ , _ , _ , _ , uL , hL , uR , hR , eqL , eqR) =
  eqL , eqR , hal (proj₁ (fin-fwd h uL hL uR hR eqL eqR))
  where
  hal : Step g (abs c) fin (abs c) → halted g (abs c) ≡ true
  hal (finish _ _ ht) = ht

source-final : ∀ {g c} → Hold g c →
               l2r c ≡ [] → r2l c ≡ [] → halted g (abs c) ≡ true →
               CanFinish c
source-final {c = c} h eqL eqR ht =
  let oL = unfoldL h
      oR = unfoldR h
  in Opened.ρ′ oL , Opened.pend′ oL , Opened.f oL ,
     Opened.ρ′ oR , Opened.pend′ oR , Opened.f oR ,
     Opened.unf oL , asHaltL h (leftStop h (Opened.unf oL)) ht ,
     Opened.unf oR , asHaltR h (rightStop h (Opened.unf oR)) ht ,
     eqL , eqR

final-iff : ∀ {g c} → Hold g c →
            (CanFinish c → l2r c ≡ [] × r2l c ≡ [] × halted g (abs c) ≡ true) ×
            ((l2r c ≡ [] × r2l c ≡ [] × halted g (abs c) ≡ true) → CanFinish c)
final-iff h = graph-final h , (λ { (eqL , eqR , ht) → source-final h eqL eqR ht })

------------------------------------------------------------------------
-- The unfold a place determines.
--
-- A `smu` peels. An action is the focus. A jump is not followed here:
-- its target is another place, and this reading stops rather than guess
-- it. The result is the unfold a backward step consumes.
------------------------------------------------------------------------

{-# OPTIONS --safe --guardedness #-}

module Muro.Temporal.Reveal where

open import Data.List.Base using (List; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing; map)
open import Data.Product using (Σ; _,_)
open import Data.String.Base using (String)

open import Muro.Temporal.Source
  using ( SProc; smu; EnvP
        ; Pay; pEcho
        ; Focus; f-done; f-stop; f-put; f-get; f-pick0; f-pick1
        ; f-cover; f-iget; f-mget
        ; Unfold; u-mu; u-done; u-stop; u-put; u-get; u-pick0; u-pick1
        ; u-cover; u-iget; u-mget )
open import Muro.Temporal.Den
  using ( Place; p-mu; p-act; p-jump
        ; Den; d-done; d-stop; d-put; d-echo; d-pick0; d-pick1
        ; d-get; d-cover; d-iget; d-mget
        ; Link; lk-mu; lk-jump; lk-done; lk-stop; lk-put; lk-echo
        ; lk-pick0; lk-pick1; lk-get; lk-cover; lk-iget; lk-mget
        ; Recipe; r-done; r-stop; r-put; r-echo; r-pick0; r-pick1
        ; r-get; r-cover; r-iget; r-mget; r-mu )

-- The environment and the pending names an unfold arrives at.
record Sp (env : EnvP) (pend : List String) (P : SProc) : Set where
  constructor sp
  field
    ρ′ : EnvP
    pend′ : List String
    f : Focus
    unf : Unfold env pend P ρ′ pend′ f

spine : ∀ {P env pend} (pl : Place P) → Link pl → Maybe (Sp env pend P)
spine {env = env} {pend = pend} (p-mu {p = q} x pl) (lk-mu lk) =
  map wrap (spine {env = (x , smu x q) ∷ env} {pend = x ∷ pend} pl lk)
  where
  wrap : Sp ((x , smu x q) ∷ env) (x ∷ pend) q → Sp env pend (smu x q)
  wrap (sp ρ′ pend′ f u) = sp ρ′ pend′ f (u-mu u)
spine {env = env} {pend = pend}
  (p-act (d-done _) r-done _ _ _) (lk-done _) =
  just (sp env pend f-done u-done)
spine {env = env} {pend = pend}
  (p-act (d-stop _) r-stop _ _ _) (lk-stop _) =
  just (sp env pend f-stop u-stop)
spine {env = env} {pend = pend}
  (p-act (d-put _ _ a _ _ p _ _ _ _ _ _ _ _ _) r-put _ _ _) (lk-put _ _ _ _) =
  just (sp env pend (f-put a p) u-put)
spine {env = env} {pend = pend}
  (p-act (d-echo _ _ x _ _ _ p _ _ _ _ _ _ _ _ _) r-echo _ _ _) (lk-echo _ _ _ _) =
  just (sp env pend (f-put (pEcho x) p) u-put)
spine {env = env} {pend = pend}
  (p-act (d-pick0 _ _ _ p _ _ _ _ _ _ _ _) r-pick0 _ _ _) (lk-pick0 _ _ _ _) =
  just (sp env pend (f-pick0 p) u-pick0)
spine {env = env} {pend = pend}
  (p-act (d-pick1 _ _ _ p _ _ _ _ _ _ _ _) r-pick1 _ _ _) (lk-pick1 _ _ _ _) =
  just (sp env pend (f-pick1 p) u-pick1)
spine {env = env} {pend = pend}
  (p-act (d-get _ _ t x _ p _ _ _ _ _ _ _ _) r-get _ _ _) (lk-get _ _ _ _) =
  just (sp env pend (f-get t x p) u-get)
spine {env = env} {pend = pend}
  (p-act (d-cover _ _ _ _ p q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) r-cover _ _ _)
  (lk-cover _ _ _ _ _) =
  just (sp env pend (f-cover p q) u-cover)
spine {env = env} {pend = pend}
  (p-act (d-iget _ _ x _ _ p q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) r-iget _ _ _)
  (lk-iget _ _ _ _ _) =
  just (sp env pend (f-iget x p q) u-iget)
spine {env = env} {pend = pend}
  (p-act (d-mget _ _ t x _ as _ _ _ _ _ _ _) r-mget _ _ _) (lk-mget _ _ _ _) =
  just (sp env pend (f-mget t x as) u-mget)
spine (p-jump _ _ _ _) (lk-jump _) = nothing
spine (p-act _ (r-mu _) _ _ _) ()

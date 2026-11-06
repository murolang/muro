------------------------------------------------------------------------
-- Muro — an explicit affine dependent type theory:
-- Elixir checks it, Agda specifies it, only run terms run.
------------------------------------------------------------------------

-- `Muro.Rec` and `Muro.Temporal` are coinductive. `--guardedness`
-- is infective, and it is allowed under `--safe`. `Muro.Linear`
-- imports `Muro.Rec`. The temporal modules import `Muro.Temporal`.
{-# OPTIONS --safe --guardedness #-}
module Muro where

open import Muro.Base public
open import Muro.Syntax public
open import Muro.Subst public
open import Muro.Env public
open import Muro.Check public
import Muro.SubstLemmas
import Muro.Spine
import Muro.Reduction
import Muro.Convert
import Muro.Data
import Muro.Judgement
import Muro.Typing
import Muro.Wall
import Muro.Consistency
import Muro.Frag
import Muro.Tag
import Muro.Soundness.Conv
import Muro.Soundness.Views
import Muro.Soundness
import Muro.Productive
import Muro.IR
import Muro.Session
import Muro.Rec
import Muro.Dual
import Muro.Meet
import Muro.Async
import Muro.AsyncSync
import Muro.AsyncRec
import Muro.Temporal
import Muro.Temporal.Source
import Muro.Temporal.Bridge
import Muro.Temporal.Pic
import Muro.Temporal.Agree
import Muro.Temporal.Ordinal
import Muro.Temporal.Fire
import Muro.Temporal.Den
import Muro.Temporal.Denote
import Muro.Temporal.Nest
import Muro.Temporal.Reveal
import Muro.Temporal.Chase
import Muro.Temporal.Expose
import Muro.Temporal.Back
import Muro.Temporal.Invert
import Muro.Temporal.Follow
import Muro.Temporal.Carry
import Muro.Temporal.Graph
import Muro.Temporal.Safety
import Muro.Temporal.Live
import Muro.Temporal.Fair
import Muro.Temporal.Decide
import Muro.Temporal.Span
import Muro.Temporal.Finite
import Muro.Temporal.Search
import Muro.Temporal.Sound
import Muro.Temporal.Examples
import Muro.Talk
import Muro.Choreo
import Muro.Seated
import Muro.Held
import Muro.Arrow
import Muro.Linear
import Muro.Place
import Muro.Located
open import Muro.Example public
open import Muro.ExampleStream public
import Muro.ExampleEither
import Muro.ExampleAlways
import Muro.ExampleBisim
import Muro.ExampleFamily
import Muro.ExampleList
import Muro.ExampleVec
import Muro.ExampleNx

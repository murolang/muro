------------------------------------------------------------------------
-- Muro — an explicit affine dependent type theory:
-- Elixir checks it, Agda specifies it, only run terms run.
------------------------------------------------------------------------

module Muro where

open import Muro.Base public
open import Muro.Syntax public
open import Muro.Subst public
open import Muro.Unembed public
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
open import Muro.Example public
open import Muro.ExampleStream public
import Muro.ExampleEither
import Muro.ExampleAlways
import Muro.ExampleBisim
import Muro.ExampleFamily
import Muro.ExampleList
import Muro.ExampleVec
import Muro.ExampleNx

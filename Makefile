AGDA  := agda
# --no-libraries: vendored stdlib ships extra .agda-lib files (tests, cubical).
AFLAGS := --no-libraries -i agda -i vendor/agda-stdlib/src --warning=noUnsupportedIndexedMatch

# The Agda tree — Judgement, Wall, Consistency, Typing, Convert,
# Reduction, Spine, Data, Frag, Tag, Session, Rec, Dual, Meet, Talk, Choreo, Seated, Held, Arrow, Linear, Place, Located, the checker Check and its
# soundness proof Soundness (with Soundness.Conv, Soundness.Views),
# what they import (Base, Syntax, Subst, SubstLemmas, Env), Async,
# AsyncSync, AsyncRec, Temporal (Source, Bridge, Graph, Safety, Live,
# Fair, Decide, Search, Sound, Examples, Pic, Agree, Ordinal, Fire, Den,
# Denote, Nest, Expose, Back, Reveal), and the examples — is checked under --safe: no postulates,
# no TERMINATING, no --type-in-type. `Muro.agda`, `Muro.Rec`, `Muro.Linear`,
# and `Muro.Temporal` also pass `--guardedness`, which `--safe` allows.
# A repeating protocol, and an infinite run of a buffered meeting, are
# guarded coinductive definitions. The option is infective, so a module
# that imports one of those carries it too. `Muro.Linear` imports `Muro.Rec`.
# Check is structurally recursive on the term, with fuel only where it reduces.
# Productive is the observation theorem for an accepted unfold. It is --safe
# and is not imported by Check or Soundness.
.PHONY: agda agda-safe agda-all agda-soundness agda-syntax agda-check elixir clean

agda: agda-safe agda-all

agda-safe:
	$(AGDA) $(AFLAGS) --safe agda/Muro/IR.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Session.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Rec.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Dual.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Meet.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Async.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/AsyncSync.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/AsyncRec.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Source.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Bridge.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Pic.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Agree.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Ordinal.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Fire.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Den.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Denote.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Nest.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Reveal.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Chase.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Expose.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Back.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Invert.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Follow.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Carry.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Graph.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Safety.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Live.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Fair.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Decide.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Span.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Finite.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Search.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Sound.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Temporal/Examples.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Talk.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Choreo.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Seated.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Held.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Arrow.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Linear.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Place.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Located.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Wall.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Consistency.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Frag.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Tag.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Word.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Check.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Productive.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Soundness.agda

agda-soundness:
	$(AGDA) $(AFLAGS) --safe agda/Muro/Soundness.agda

agda-all:
	$(AGDA) $(AFLAGS) --safe agda/Muro.agda

agda-syntax:
	$(AGDA) $(AFLAGS) agda/Muro/Syntax.agda
	$(AGDA) $(AFLAGS) agda/Muro/Subst.agda

agda-check:
	$(AGDA) $(AFLAGS) --safe agda/Muro/Check.agda

elixir:
	mix test

clean:
	find agda -name '*.agdai' -delete
	rm -rf agda/_build _build deps

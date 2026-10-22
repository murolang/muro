AGDA  := agda
# --no-libraries: vendored stdlib ships extra .agda-lib files (tests, cubical).
AFLAGS := --no-libraries -i agda -i vendor/agda-stdlib/src --warning=noUnsupportedIndexedMatch

# Theorem modules — Judgement, Wall, Consistency, Typing, Convert,
# Reduction, Spine, Data, Frag, Tag, Session, Dual, Meet, Talk, Place, Located, the checker Check and its
# soundness proof Soundness (with Soundness.Conv, Soundness.Views), and
# what they import (Base, Syntax, Subst, SubstLemmas, Env) — are checked
# under --safe: no postulates, no TERMINATING, no --type-in-type. Check is
# structurally recursive on the term, with fuel only where it reduces.
# Unembed (PHOAS → de Bruijn, for the examples only) carries a
# TERMINATING pragma, so the full tree with the examples is checked
# without --safe.
.PHONY: agda agda-safe agda-all agda-soundness agda-syntax agda-check elixir clean

agda: agda-safe agda-all

agda-safe:
	$(AGDA) $(AFLAGS) --safe agda/Muro/IR.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Session.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Dual.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Meet.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Talk.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Arrow.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Place.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Located.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Wall.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Consistency.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Frag.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Tag.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Check.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Soundness.agda

agda-soundness:
	$(AGDA) $(AFLAGS) --safe agda/Muro/Soundness.agda

agda-all:
	$(AGDA) $(AFLAGS) agda/Muro.agda

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

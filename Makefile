AGDA  := agda
# --no-libraries: vendored stdlib ships extra .agda-lib files (tests, cubical).
AFLAGS := --no-libraries -i agda -i vendor/agda-stdlib/src --warning=noUnsupportedIndexedMatch

# The Agda tree — Judgement, Wall, Consistency, Typing, Convert,
# Reduction, Spine, Data, Frag, Tag, Session, Rec, Dual, Meet, Talk, Seated, Held, Arrow, Linear, Place, Located, the checker Check and its
# soundness proof Soundness (with Soundness.Conv, Soundness.Views),
# what they import (Base, Syntax, Subst, SubstLemmas, Env), and the
# examples — is checked under --safe: no postulates, no TERMINATING,
# no --type-in-type. `Muro.agda`, `Muro.Rec`, and `Muro.Linear` also pass
# `--guardedness`, which `--safe` allows, so a repeating protocol is
# a guarded coinductive definition. `Muro.Linear` imports `Muro.Rec`.
# Check is structurally recursive on the term, with fuel only where it reduces.
.PHONY: agda agda-safe agda-all agda-soundness agda-syntax agda-check elixir clean

agda: agda-safe agda-all

agda-safe:
	$(AGDA) $(AFLAGS) --safe agda/Muro/IR.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Session.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Rec.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Dual.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Meet.agda
	$(AGDA) $(AFLAGS) --safe agda/Muro/Talk.agda
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
	$(AGDA) $(AFLAGS) --safe agda/Muro/Check.agda
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

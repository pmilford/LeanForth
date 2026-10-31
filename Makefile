GFORTH ?= $(if $(wildcard .tools/gforth/bin/gforth),.tools/gforth/bin/gforth,gforth)
LEAN ?= lean

.PHONY: test-tagged-infer-differential test-tagged-binder-differential
.PHONY: smoke reference reference-export test-harness test-core test-symbolic-infer-draft test-composition-fixture test-name-differential test-scope-differential test-shift-differential test-instantiate-differential test-beta-differential test-compare-differential test-infer-differential test-declaration-differential test-level-differential test-level-assignment-differential test-level-compare-differential test-poly-specialization-differential test-program test-program-differential test-program-stack-differential
smoke:
	$(GFORTH) tests/smoke/smoke.fs

reference:
	LEAN=$(LEAN) bash tests/reference/check.sh

reference-export:
	LEAN=$(LEAN) bash tests/reference/export-check.sh

test-harness:
	GFORTH=$(GFORTH) bash tests/harness/check.sh

test-core:
	$(GFORTH) tests/core/arena.fs
	$(GFORTH) tests/core/terms.fs
	$(GFORTH) tests/core/tagged-sort-boundary.fs
	$(GFORTH) tests/core/symbolic-session.fs
	$(GFORTH) tests/core/symbolic-session-extra.fs
	$(GFORTH) tests/core/generation-handles.fs
	$(GFORTH) tests/core/handle-reference-integrity.fs
	$(GFORTH) tests/core/tagged-infer.fs
	$(GFORTH) tests/core/tagged-shift.fs
	$(GFORTH) tests/core/tagged-integration.fs
	$(GFORTH) tests/core/names.fs
	$(GFORTH) tests/core/levels.fs
	$(GFORTH) tests/core/level-scope.fs
	$(GFORTH) tests/core/level-value.fs
	$(GFORTH) tests/core/level-compare.fs
	$(GFORTH) tests/core/load.fs
	$(GFORTH) tests/core/scope.fs
	$(GFORTH) tests/core/shift.fs
	$(GFORTH) tests/core/instantiate.fs
	$(GFORTH) tests/core/beta.fs
	$(GFORTH) tests/core/compare.fs
	$(GFORTH) tests/core/infer.fs
	$(GFORTH) tests/core/declaration-probe.fs
	$(GFORTH) tests/core/infer-composition-probe.fs

# Explicitly opt in to the unsafe draft; this target does not enable it for use.
test-symbolic-infer-draft:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/symbolic-infer-draft.sh

test-tagged-infer-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/tagged-infer-differential.sh

test-tagged-binder-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/tagged-binder-differential.sh

test-composition-fixture:
	python3 tests/core/test_composition_fixture.py
	GFORTH=$(GFORTH) python3 tests/core/test_ndjson_preview.py
	GFORTH=$(GFORTH) python3 tests/core/test_named_levels.py
	GFORTH=$(GFORTH) python3 tests/core/test_poly_specialization.py
	GFORTH=$(GFORTH) python3 tests/core/check_composition_fixture.py

test-name-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/name-differential.sh

test-scope-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/scope-differential.sh

test-shift-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/shift-differential.sh

test-instantiate-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/instantiate-differential.sh

test-beta-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/beta-differential.sh

test-compare-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/compare-differential.sh

test-infer-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/infer-differential.sh

test-declaration-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/declaration-differential.sh

test-level-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) python3 tests/core/level-differential.py

test-level-assignment-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/level-assignment-differential.sh

test-level-compare-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/level-compare-differential.sh

test-poly-specialization-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/poly-specialization-differential.sh

test-program:
	$(GFORTH) tests/program/clamp.fs

test-program-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/program/differential.sh

test-program-stack-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/program/stack-differential.sh

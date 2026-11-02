GFORTH ?= $(if $(wildcard .tools/gforth/bin/gforth),.tools/gforth/bin/gforth,gforth)
LEAN ?= lean

.PHONY: test-tagged-infer-differential test-tagged-binder-differential test-tagged-application-differential test-tagged-beta-differential test-tagged-convert-differential test-tagged-universe-differential test-program-depth-differential
.PHONY: test-level-substitute-differential
.PHONY: test-term-level-substitute-differential
.PHONY: test-program-values-differential
.PHONY: test-signature-fixture-differential
.PHONY: test-example-reference-differential
.PHONY: test-constant-signature-differential test-add-reference-differential
.PHONY: test-abs-reference-differential
.PHONY: test-constant-term-type-differential
.PHONY: test-factorial-reference-differential
.PHONY: test-gcd-reference-differential
.PHONY: test-range-64-differential
.PHONY: test-memory-reference-differential
.PHONY: test-mixed-shift-differential
.PHONY: test-mixed-instantiate-differential
.PHONY: test-mixed-beta-differential
.PHONY: test-mixed-convert-differential
.PHONY: test-mixed-level-substitute-differential
.PHONY: test-mixed-signature-differential
.PHONY: profile-existing
.PHONY: profile-history
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
	$(GFORTH) tests/core/raw-declaration-index.fs
	$(GFORTH) tests/core/raw-index-reset.fs
	$(GFORTH) tests/core/constant-references.fs
	$(GFORTH) tests/core/constant-term-boundary.fs
	$(GFORTH) tests/core/constant-term-scope.fs
	$(GFORTH) tests/core/mixed-shift.fs
	$(GFORTH) tests/core/mixed-instantiate.fs
	$(GFORTH) tests/core/mixed-beta.fs
	$(GFORTH) tests/core/mixed-compare.fs
	$(GFORTH) tests/core/mixed-convert.fs
	$(GFORTH) tests/core/mixed-level-substitute.fs
	$(GFORTH) tests/core/mixed-signature-probe.fs
	$(GFORTH) tests/core/constant-term-type-probe.fs
	$(GFORTH) tests/core/constant-application-oracle.fs
	$(GFORTH) tests/core/constant-application-probe.fs
	$(GFORTH) tests/core/constant-spine-probe.fs
	$(GFORTH) tests/core/context-constant-spine.fs
	$(GFORTH) tests/core/validated-context-spine.fs
	$(GFORTH) tests/core/constant-signature-probe.fs
	$(GFORTH) tests/core/raw-declaration-capacity.fs
	$(GFORTH) tests/core/raw-signature-specialize.fs
	$(GFORTH) tests/core/tagged-infer.fs
	$(GFORTH) tests/core/tagged-context-infer.fs
	$(GFORTH) tests/core/context-validation-probe.fs
	$(GFORTH) tests/core/tagged-shift.fs
	$(GFORTH) tests/core/tagged-instantiate.fs
	$(GFORTH) tests/core/tagged-compare.fs
	$(GFORTH) tests/core/tagged-application.fs
	$(GFORTH) tests/core/tagged-beta.fs
	$(GFORTH) tests/core/tagged-convert.fs
	$(GFORTH) tests/core/tagged-declaration-probe.fs
	$(GFORTH) tests/core/candidate-definition-probe.fs
	$(GFORTH) tests/core/tagged-integration.fs
	$(GFORTH) tests/core/names.fs
	$(GFORTH) tests/core/levels.fs
	$(GFORTH) tests/core/level-scope.fs
	$(GFORTH) tests/core/level-substitute.fs
	$(GFORTH) tests/core/term-level-substitute.fs
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

test-mixed-shift-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/mixed-shift-differential.sh

test-mixed-instantiate-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/mixed-instantiate-differential.sh

test-mixed-beta-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/mixed-beta-differential.sh

test-mixed-convert-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/mixed-convert-differential.sh

test-mixed-level-substitute-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/mixed-level-substitute-differential.sh

test-mixed-signature-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/mixed-signature-differential.sh

test-tagged-binder-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/tagged-binder-differential.sh

test-tagged-application-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/tagged-application-differential.sh

test-tagged-beta-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/tagged-beta-differential.sh

test-tagged-convert-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/tagged-convert-differential.sh

test-tagged-universe-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/tagged-universe-differential.sh

test-composition-fixture:
	python3 tests/core/test_composition_fixture.py
	GFORTH=$(GFORTH) python3 tests/core/test_ndjson_preview.py
	python3 tests/core/test_preview_constants.py
	GFORTH=$(GFORTH) python3 tests/core/constant-term-fixture-test.py
	GFORTH=$(GFORTH) python3 tests/core/context-constant-fixture-test.py
	python3 tests/core/test_preview_dependencies.py
	GFORTH=$(GFORTH) python3 tests/core/test_named_levels.py
	GFORTH=$(GFORTH) python3 tests/core/test_poly_specialization.py
	GFORTH=$(GFORTH) python3 tests/core/test_tagged_poly_fixture.py
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

test-level-substitute-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/level-substitute-differential.sh

test-term-level-substitute-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/term-level-substitute-differential.sh

test-signature-fixture-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) python3 tests/core/signature-fixture-test.py

test-constant-signature-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/constant-signature-differential.sh

test-constant-term-type-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/constant-term-type-differential.sh

test-level-compare-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/level-compare-differential.sh

test-poly-specialization-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/core/poly-specialization-differential.sh

test-program:
	$(GFORTH) tests/program/clamp.fs
	$(GFORTH) tests/program/examples.fs
	$(GFORTH) tests/program/program-depth.fs

test-program-values-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/program/program-values-differential.sh

test-example-reference-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/program/example-reference-differential.sh

test-add-reference-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/program/add-reference-differential.sh

test-abs-reference-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/program/abs-reference-differential.sh

test-factorial-reference-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/program/factorial-reference-differential.sh

test-gcd-reference-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/program/gcd-reference-differential.sh

test-range-64-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/program/extra-program-range-differential.sh

test-memory-reference-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/program/memory-reference-differential.sh

profile-existing:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash scripts/profile-existing.sh

profile-history:
	LEAN=$(LEAN) GFORTH=$(GFORTH) python3 scripts/profile-history.py

test-program-depth-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/program/program-depth-differential.sh

test-program-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/program/differential.sh

test-program-stack-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) bash tests/program/stack-differential.sh

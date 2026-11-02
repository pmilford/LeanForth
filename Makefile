# Toolchains. Prefer the project-local copies under .tools/ (see
# docs/development/INSTALLATION_LOG.md); override with GFORTH=... or LEAN=... .
# LEAN names the pinned toolchain binary directly rather than the elan proxy,
# so no ELAN_HOME is needed and nothing is downloaded into ~/.elan.
LOCAL_GFORTH := .tools/gforth/bin/gforth
LOCAL_LEAN := $(CURDIR)/.tools/elan/toolchains/leanprover--lean4---v4.35.0/bin/lean
GFORTH ?= $(if $(wildcard $(LOCAL_GFORTH)),$(LOCAL_GFORTH),gforth)
LEAN ?= $(if $(wildcard $(LOCAL_LEAN)),$(LOCAL_LEAN),lean)

# Every test command is stopped after TEST_TIMEOUT seconds and then fails,
# so a looping test cannot stall a local run or CI. Uses GNU timeout(1).
TEST_TIMEOUT ?= 600
RUN := timeout $(TEST_TIMEOUT)

# Every pinned-Lean oracle and differential comparison. Excludes the unsafe
# test-symbolic-infer-draft and the profiling targets.
DIFFERENTIAL_TARGETS := \
	reference reference-export \
	test-name-differential test-scope-differential test-shift-differential \
	test-instantiate-differential test-beta-differential \
	test-compare-differential test-infer-differential \
	test-declaration-differential test-level-differential \
	test-level-assignment-differential test-level-compare-differential \
	test-level-substitute-differential test-term-level-substitute-differential \
	test-poly-specialization-differential test-signature-fixture-differential \
	test-constant-signature-differential test-constant-term-type-differential \
	test-tagged-infer-differential test-tagged-binder-differential \
	test-tagged-application-differential test-tagged-beta-differential \
	test-tagged-convert-differential test-tagged-universe-differential \
	test-mixed-shift-differential test-mixed-instantiate-differential \
	test-mixed-beta-differential test-mixed-convert-differential \
	test-mixed-level-substitute-differential test-mixed-signature-differential \
	test-mixed-infer-differential \
	test-program-differential test-program-stack-differential \
	test-program-values-differential test-program-depth-differential \
	test-example-reference-differential test-add-reference-differential \
	test-abs-reference-differential test-factorial-reference-differential \
	test-gcd-reference-differential test-range-64-differential \
	test-memory-reference-differential test-memory-frame-differential

.PHONY: test test-differential check check-docs check-lean-sources smoke test-harness test-core \
	test-composition-fixture test-program test-symbolic-infer-draft \
	profile-existing profile-history $(DIFFERENTIAL_TARGETS)

# Gforth and Python 3 only; run on every CI host and before every commit.
test: check-docs check-lean-sources smoke test-harness test-core \
	test-composition-fixture test-program

# Fails on broken documentation links or missing docs/ paths.
check-docs:
	$(RUN) python3 scripts/check-doc-links.py

# Fails on sorry, admit, native_decide or unlisted axioms in Lean test files,
# or a Lean invocation without -DwarningAsError=true. Needs no Lean.
check-lean-sources:
	$(RUN) python3 scripts/check-lean-sources.py

# Requires pinned Lean 4.35.0 as well as Gforth and Python 3.
test-differential: $(DIFFERENTIAL_TARGETS)

check: test test-differential

smoke:
	$(RUN) $(GFORTH) tests/smoke/smoke.fs

reference:
	LEAN=$(LEAN) $(RUN) bash tests/reference/check.sh

reference-export:
	LEAN=$(LEAN) $(RUN) bash tests/reference/export-check.sh

test-harness:
	GFORTH=$(GFORTH) $(RUN) bash tests/harness/check.sh

test-core:
	$(RUN) $(GFORTH) tests/core/arena.fs
	$(RUN) $(GFORTH) tests/core/terms.fs
	$(RUN) $(GFORTH) tests/core/tagged-sort-boundary.fs
	$(RUN) $(GFORTH) tests/core/symbolic-session.fs
	$(RUN) $(GFORTH) tests/core/symbolic-session-extra.fs
	$(RUN) $(GFORTH) tests/core/generation-handles.fs
	$(RUN) $(GFORTH) tests/core/handle-reference-integrity.fs
	$(RUN) $(GFORTH) tests/core/raw-declaration-index.fs
	$(RUN) $(GFORTH) tests/core/raw-index-reset.fs
	$(RUN) $(GFORTH) tests/core/constant-references.fs
	$(RUN) $(GFORTH) tests/core/constant-term-boundary.fs
	$(RUN) $(GFORTH) tests/core/constant-term-scope.fs
	$(RUN) $(GFORTH) tests/core/mixed-shift.fs
	$(RUN) $(GFORTH) tests/core/mixed-instantiate.fs
	$(RUN) $(GFORTH) tests/core/mixed-beta.fs
	$(RUN) $(GFORTH) tests/core/mixed-compare.fs
	$(RUN) $(GFORTH) tests/core/mixed-convert.fs
	$(RUN) $(GFORTH) tests/core/mixed-level-substitute.fs
	$(RUN) $(GFORTH) tests/core/mixed-signature-probe.fs
	$(RUN) $(GFORTH) tests/core/mixed-signature-lifecycle.fs
	$(RUN) $(GFORTH) tests/core/mixed-signature-audit.fs
	$(RUN) $(GFORTH) tests/core/mixed-infer.fs
	$(RUN) $(GFORTH) tests/core/mixed-definition-probe.fs
	$(RUN) $(GFORTH) tests/core/constant-term-type-probe.fs
	$(RUN) $(GFORTH) tests/core/constant-application-oracle.fs
	$(RUN) $(GFORTH) tests/core/constant-application-probe.fs
	$(RUN) $(GFORTH) tests/core/constant-spine-probe.fs
	$(RUN) $(GFORTH) tests/core/context-constant-spine.fs
	$(RUN) $(GFORTH) tests/core/validated-context-spine.fs
	$(RUN) $(GFORTH) tests/core/constant-signature-probe.fs
	$(RUN) $(GFORTH) tests/core/raw-declaration-capacity.fs
	$(RUN) $(GFORTH) tests/core/raw-signature-specialize.fs
	$(RUN) $(GFORTH) tests/core/tagged-infer.fs
	$(RUN) $(GFORTH) tests/core/tagged-context-infer.fs
	$(RUN) $(GFORTH) tests/core/context-validation-probe.fs
	$(RUN) $(GFORTH) tests/core/tagged-shift.fs
	$(RUN) $(GFORTH) tests/core/tagged-instantiate.fs
	$(RUN) $(GFORTH) tests/core/tagged-compare.fs
	$(RUN) $(GFORTH) tests/core/tagged-application.fs
	$(RUN) $(GFORTH) tests/core/tagged-beta.fs
	$(RUN) $(GFORTH) tests/core/tagged-convert.fs
	$(RUN) $(GFORTH) tests/core/tagged-declaration-probe.fs
	$(RUN) $(GFORTH) tests/core/candidate-definition-probe.fs
	$(RUN) $(GFORTH) tests/core/tagged-integration.fs
	$(RUN) $(GFORTH) tests/core/names.fs
	$(RUN) $(GFORTH) tests/core/levels.fs
	$(RUN) $(GFORTH) tests/core/level-scope.fs
	$(RUN) $(GFORTH) tests/core/level-substitute.fs
	$(RUN) $(GFORTH) tests/core/term-level-substitute.fs
	$(RUN) $(GFORTH) tests/core/level-value.fs
	$(RUN) $(GFORTH) tests/core/level-compare.fs
	$(RUN) $(GFORTH) tests/core/load.fs
	$(RUN) $(GFORTH) tests/core/scope.fs
	$(RUN) $(GFORTH) tests/core/shift.fs
	$(RUN) $(GFORTH) tests/core/instantiate.fs
	$(RUN) $(GFORTH) tests/core/beta.fs
	$(RUN) $(GFORTH) tests/core/compare.fs
	$(RUN) $(GFORTH) tests/core/infer.fs
	$(RUN) $(GFORTH) tests/core/declaration-probe.fs
	$(RUN) $(GFORTH) tests/core/infer-composition-probe.fs

# Explicitly opt in to the unsafe draft; this target does not enable it for use.
test-symbolic-infer-draft:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/symbolic-infer-draft.sh

test-tagged-infer-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/tagged-infer-differential.sh

test-mixed-shift-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/mixed-shift-differential.sh

test-mixed-instantiate-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/mixed-instantiate-differential.sh

test-mixed-beta-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/mixed-beta-differential.sh

test-mixed-convert-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/mixed-convert-differential.sh

test-mixed-level-substitute-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/mixed-level-substitute-differential.sh

test-mixed-signature-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/mixed-signature-differential.sh

test-mixed-infer-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/mixed-infer-differential.sh

test-tagged-binder-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/tagged-binder-differential.sh

test-tagged-application-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/tagged-application-differential.sh

test-tagged-beta-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/tagged-beta-differential.sh

test-tagged-convert-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/tagged-convert-differential.sh

test-tagged-universe-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/tagged-universe-differential.sh

test-composition-fixture:
	$(RUN) python3 tests/core/test_composition_fixture.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_ndjson_preview.py
	$(RUN) python3 tests/core/test_preview_constants.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/constant-term-fixture-test.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/context-constant-fixture-test.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/declaration-chain-test.py
	$(RUN) python3 tests/core/test_preview_dependencies.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_named_levels.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_poly_specialization.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_tagged_poly_fixture.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/check_composition_fixture.py

test-name-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/name-differential.sh

test-scope-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/scope-differential.sh

test-shift-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/shift-differential.sh

test-instantiate-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/instantiate-differential.sh

test-beta-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/beta-differential.sh

test-compare-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/compare-differential.sh

test-infer-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/infer-differential.sh

test-declaration-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/declaration-differential.sh

test-level-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/core/level-differential.py

test-level-assignment-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/level-assignment-differential.sh

test-level-substitute-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/level-substitute-differential.sh

test-term-level-substitute-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/term-level-substitute-differential.sh

test-signature-fixture-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/core/signature-fixture-test.py

test-constant-signature-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/constant-signature-differential.sh

test-constant-term-type-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/constant-term-type-differential.sh

test-level-compare-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/level-compare-differential.sh

test-poly-specialization-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/poly-specialization-differential.sh

test-program:
	$(RUN) $(GFORTH) tests/program/clamp.fs
	$(RUN) $(GFORTH) tests/program/examples.fs
	$(RUN) $(GFORTH) tests/program/program-depth.fs

test-program-values-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/program-values-differential.sh

test-example-reference-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/example-reference-differential.sh

test-add-reference-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/add-reference-differential.sh

test-abs-reference-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/abs-reference-differential.sh

test-factorial-reference-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/factorial-reference-differential.sh

test-gcd-reference-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/gcd-reference-differential.sh

test-range-64-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/extra-program-range-differential.sh

test-memory-reference-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/memory-reference-differential.sh

test-memory-frame-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/memory-frame-differential.sh

profile-existing:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash scripts/profile-existing.sh

profile-history:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 scripts/profile-history.py

test-program-depth-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/program-depth-differential.sh

test-program-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/differential.sh

test-program-stack-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/stack-differential.sh

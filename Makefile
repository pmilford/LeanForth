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

# Every pinned-Lean oracle and differential comparison of current code.
# Excludes the unsafe test-symbolic-infer-draft and the profiling targets.
DIFFERENTIAL_TARGETS := \
	reference reference-export \
	test-name-differential \
	test-level-differential \
	test-level-assignment-differential test-level-compare-differential \
	test-level-substitute-differential \
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

# Pinned-Lean comparisons that use superseded code in src/legacy/. Their
# scripts and Lean tables are in tests/legacy/ and are retired with it
# (roadmap item Q9); `make check` still runs them through test-differential.
LEGACY_DIFFERENTIAL_TARGETS := \
	test-scope-differential test-shift-differential \
	test-instantiate-differential test-beta-differential \
	test-compare-differential test-infer-differential \
	test-declaration-differential test-term-level-substitute-differential \
	test-poly-specialization-differential test-signature-fixture-differential \
	test-constant-signature-differential test-constant-term-type-differential \
	test-tagged-infer-differential test-tagged-binder-differential \
	test-tagged-application-differential test-tagged-beta-differential \
	test-tagged-convert-differential test-tagged-universe-differential

.PHONY: test test-differential check check-docs check-lean-sources check-portable-forth smoke \
	test-harness test-lib test-core \
	test-composition-fixture test-program test-legacy test-legacy-differential \
	test-symbolic-infer-draft profile-existing profile-history forth-metrics \
	$(DIFFERENTIAL_TARGETS) $(LEGACY_DIFFERENTIAL_TARGETS)

# Gforth and Python 3 only; run on every CI host and before every commit.
test: check-docs check-lean-sources check-portable-forth smoke test-harness test-lib test-core \
	test-composition-fixture test-program test-legacy

# Fails on broken documentation links or missing docs/ paths.
check-docs:
	$(RUN) python3 scripts/check-doc-links.py

# Fails on sorry, admit, native_decide or unlisted axioms in Lean test files,
# or a Lean invocation without -DwarningAsError=true. Needs no Lean.
check-lean-sources:
	$(RUN) python3 scripts/check-lean-sources.py

# Fails if current Forth source could depend on byte order or cell size
# (docs/development/FORTH_STYLE.md, section 8).
check-portable-forth:
	$(RUN) python3 scripts/check-portable-forth.py

# Report-only Forth style metrics (word length, globals, locals, shuffling);
# see docs/development/FORTH_STYLE.md. Never fails on style.
forth-metrics:
	python3 scripts/forth-metrics.py --words 20 src

# Requires pinned Lean 4.35.0 as well as Gforth and Python 3.
test-differential: $(DIFFERENTIAL_TARGETS) test-legacy-differential

check: test test-differential

# src/main.fs must load silently: a "redefined" warning means two modules
# define the same word. Then one word from each loaded layer must run.
smoke:
	@out=$$($(RUN) $(GFORTH) src/main.fs -e bye 2>&1) || { printf '%s\n' "$$out" >&2; exit 1; }; \
	if [ -n "$$out" ]; then printf 'src/main.fs printed while loading:\n%s\n' "$$out" >&2; exit 1; fi
	$(RUN) $(GFORTH) tests/smoke/smoke.fs

reference:
	LEAN=$(LEAN) $(RUN) bash tests/reference/check.sh

reference-export:
	LEAN=$(LEAN) $(RUN) bash tests/reference/export-check.sh

test-harness:
	GFORTH=$(GFORTH) $(RUN) bash tests/harness/check.sh

# The general Forth library in src/lib. The task adapter is not loaded by
# src/main.fs, so it gets its own silent-load check; task.fs tests the
# host's tasks (threads on Gforth 1.0, cooperative on 0.7.3) and
# task-serial.fs the serial path. tests/lib/task-bench.fs is report-only.
test-lib:
	$(RUN) $(GFORTH) tests/lib/lib.fs
	$(RUN) $(GFORTH) tests/lib/lib-model.fs
	$(RUN) $(GFORTH) tests/lib/context.fs
	@out=$$($(RUN) $(GFORTH) src/lib/task.fs -e bye 2>&1) || { printf '%s\n' "$$out" >&2; exit 1; }; \
	if [ -n "$$out" ]; then printf 'src/lib/task.fs printed while loading:\n%s\n' "$$out" >&2; exit 1; fi
	$(RUN) $(GFORTH) tests/lib/task.fs
	$(RUN) $(GFORTH) tests/lib/task-serial.fs

test-core:
	$(RUN) $(GFORTH) tests/core/terms.fs
	$(RUN) $(GFORTH) tests/core/symbolic-session.fs
	$(RUN) $(GFORTH) tests/core/symbolic-session-extra.fs
	$(RUN) $(GFORTH) tests/core/generation-handles.fs
	$(RUN) $(GFORTH) tests/core/walker-interface.fs
	$(RUN) $(GFORTH) tests/core/handle-reference-integrity.fs
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
	$(RUN) $(GFORTH) tests/core/names.fs
	$(RUN) $(GFORTH) tests/core/levels.fs
	$(RUN) $(GFORTH) tests/core/level-scope.fs
	$(RUN) $(GFORTH) tests/core/level-substitute.fs
	$(RUN) $(GFORTH) tests/core/level-value.fs
	$(RUN) $(GFORTH) tests/core/level-compare.fs
	$(RUN) $(GFORTH) tests/core/level-deep.fs
	$(RUN) $(GFORTH) tests/core/infer-deep.fs
	$(RUN) $(GFORTH) tests/core/load.fs

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

test-composition-fixture:
	$(RUN) python3 tests/core/test_preview_constants.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/constant-term-fixture-test.py
	$(RUN) python3 tests/core/test_preview_dependencies.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_named_levels.py

test-name-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/name-differential.sh

test-level-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/core/level-differential.py

test-level-assignment-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/level-assignment-differential.sh

test-level-substitute-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/level-substitute-differential.sh

test-level-compare-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/level-compare-differential.sh

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

# Tests of superseded code in src/legacy/ live beside it in tests/legacy/ and
# are retired with it (roadmap item Q9). Some of them also exercise current
# modules through a legacy dependency; they must be rebased onto current code
# before tests/legacy/ is deleted.
test-legacy:
	$(RUN) $(GFORTH) tests/legacy/arena.fs
	$(RUN) $(GFORTH) tests/legacy/tagged-sort-boundary.fs
	$(RUN) $(GFORTH) tests/legacy/raw-declaration-index.fs
	$(RUN) $(GFORTH) tests/legacy/raw-index-reset.fs
	$(RUN) $(GFORTH) tests/legacy/constant-term-type-probe.fs
	$(RUN) $(GFORTH) tests/legacy/constant-application-oracle.fs
	$(RUN) $(GFORTH) tests/legacy/constant-application-probe.fs
	$(RUN) $(GFORTH) tests/legacy/constant-spine-probe.fs
	$(RUN) $(GFORTH) tests/legacy/context-constant-spine.fs
	$(RUN) $(GFORTH) tests/legacy/validated-context-spine.fs
	$(RUN) $(GFORTH) tests/legacy/constant-signature-probe.fs
	$(RUN) $(GFORTH) tests/legacy/raw-declaration-capacity.fs
	$(RUN) $(GFORTH) tests/legacy/raw-signature-specialize.fs
	$(RUN) $(GFORTH) tests/legacy/tagged-infer.fs
	$(RUN) $(GFORTH) tests/legacy/tagged-context-infer.fs
	$(RUN) $(GFORTH) tests/legacy/context-validation-probe.fs
	$(RUN) $(GFORTH) tests/legacy/tagged-shift.fs
	$(RUN) $(GFORTH) tests/legacy/tagged-instantiate.fs
	$(RUN) $(GFORTH) tests/legacy/tagged-compare.fs
	$(RUN) $(GFORTH) tests/legacy/tagged-application.fs
	$(RUN) $(GFORTH) tests/legacy/tagged-beta.fs
	$(RUN) $(GFORTH) tests/legacy/tagged-convert.fs
	$(RUN) $(GFORTH) tests/legacy/tagged-declaration-probe.fs
	$(RUN) $(GFORTH) tests/legacy/candidate-definition-probe.fs
	$(RUN) $(GFORTH) tests/legacy/tagged-integration.fs
	$(RUN) $(GFORTH) tests/legacy/term-level-substitute.fs
	$(RUN) $(GFORTH) tests/legacy/scope.fs
	$(RUN) $(GFORTH) tests/legacy/shift.fs
	$(RUN) $(GFORTH) tests/legacy/instantiate.fs
	$(RUN) $(GFORTH) tests/legacy/beta.fs
	$(RUN) $(GFORTH) tests/legacy/compare.fs
	$(RUN) $(GFORTH) tests/legacy/infer.fs
	$(RUN) $(GFORTH) tests/legacy/declaration-probe.fs
	$(RUN) $(GFORTH) tests/legacy/infer-composition-probe.fs
	$(RUN) python3 tests/legacy/test_composition_fixture.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/legacy/test_ndjson_preview.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/legacy/context-constant-fixture-test.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/legacy/declaration-chain-test.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/legacy/test_poly_specialization.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/legacy/test_tagged_poly_fixture.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/legacy/check_composition_fixture.py

test-legacy-differential: $(LEGACY_DIFFERENTIAL_TARGETS)

# Explicitly opt in to the unsafe draft; this target does not enable it for use.
test-symbolic-infer-draft:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/symbolic-infer-draft.sh

test-scope-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/scope-differential.sh

test-shift-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/shift-differential.sh

test-instantiate-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/instantiate-differential.sh

test-beta-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/beta-differential.sh

test-compare-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/compare-differential.sh

test-infer-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/infer-differential.sh

test-declaration-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/declaration-differential.sh

test-term-level-substitute-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/term-level-substitute-differential.sh

test-poly-specialization-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/poly-specialization-differential.sh

test-signature-fixture-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/legacy/signature-fixture-test.py

test-constant-signature-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/constant-signature-differential.sh

test-constant-term-type-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/constant-term-type-differential.sh

test-tagged-infer-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/tagged-infer-differential.sh

test-tagged-binder-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/tagged-binder-differential.sh

test-tagged-application-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/tagged-application-differential.sh

test-tagged-beta-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/tagged-beta-differential.sh

test-tagged-convert-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/tagged-convert-differential.sh

test-tagged-universe-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/legacy/tagged-universe-differential.sh

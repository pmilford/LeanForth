# Toolchains (TESTING_STRATEGY.md, "Toolchains"): GFORTH=... and LEAN=... win;
# else the pinned copies in this checkout's .tools/ (see
# docs/development/INSTALLATION_LOG.md); else those of the folder
# LEANFORTH_TOOLS names, laid out as .tools is (a worktree without .tools sets
# it to the main checkout's .tools, and never links one); else the PATH's.
# Every recipe and script gets them as absolute paths: LEANFORTH_GFORTH and
# LEANFORTH_LEAN (exported), GFORTH_FAST (gforth-fast beside that Gforth).
# LEAN names the pinned toolchain binary directly rather than the elan proxy,
# so no ELAN_HOME is needed and nothing is downloaded into ~/.elan.
TOOLS_DIRS := $(CURDIR)/.tools $(LEANFORTH_TOOLS)
find_tool = $(firstword $(wildcard $(addsuffix /$(1),$(TOOLS_DIRS))))
# A program's absolute path: a path made absolute, a bare name looked up on PATH.
tool_path = $(if $(findstring /,$(1)),$(abspath $(1)),$(or $(shell command -v $(1) 2>/dev/null),$(1)))
LOCAL_GFORTH := $(call find_tool,gforth/bin/gforth)
LOCAL_LEAN := $(call find_tool,elan/toolchains/leanprover--lean4---v4.35.0/bin/lean)
GFORTH ?= $(or $(LOCAL_GFORTH),gforth)
# Every Forth run goes through scripts/gforth-strict.sh, which fails when
# Gforth 1.0 exits 0 after an error whose report itself crashed (BASE 0).
# A GFORTH that already names a wrapper of scripts/ (a nested make, a test
# runner) is replaced by the real Gforth, or the wrapper would call itself.
ifneq ($(filter %/scripts/gforth-strict.sh %/scripts/gforth-fast,$(abspath $(GFORTH))),)
override GFORTH := $(or $(LEANFORTH_GFORTH),$(LOCAL_GFORTH),gforth)
endif
export LEANFORTH_GFORTH := $(call tool_path,$(GFORTH))
# The fast engine for the tests that run it by name (reference-cli).
GFORTH_FAST ?= $(firstword $(wildcard $(dir $(LEANFORTH_GFORTH))gforth-fast) \
	$(call find_tool,gforth/bin/gforth-fast) $(call tool_path,gforth-fast))
# make coverage sets GFORTH to scripts/coverage-gforth.sh, which runs the strict
# wrapper itself around its Gforth 1.0, so that name is kept as it is.
ifeq ($(filter %/scripts/coverage-gforth.sh,$(abspath $(GFORTH))),)
override GFORTH := $(CURDIR)/scripts/gforth-strict.sh
else
override GFORTH := $(abspath $(GFORTH))
endif
LEAN ?= $(or $(LOCAL_LEAN),lean)
LEAN_BINARY := $(call tool_path,$(LEAN))
override LEAN := $(LEAN_BINARY)
export LEANFORTH_LEAN := $(LEAN_BINARY)

# Parallel runs (docs/development/TESTING_STRATEGY.md, "Running the suites"):
# every target of make test and make check can run beside any other (each
# writes only its own temporary folders), so make runs JOBS jobs at once
# (default 8) unless -j is given, and prints each target's output in one
# piece. JOBS=1 (or -j1) runs one target at a time. A make started by a
# recipe ($(MAKE)) shares its parent's jobs.
JOBS ?= 8
ifeq ($(filter -j%,$(MAKEFLAGS))$(filter-out 0,$(MAKELEVEL)),)
MAKEFLAGS += -j$(JOBS)
endif
ifneq ($(filter output-sync,$(.FEATURES)),)
MAKEFLAGS += --output-sync=target
endif

# Pinned Lean's runs and its exporter's are cached (scripts/lean-cache.py):
# the recipes get LEAN and LEANEXPORT set to scripts that replay a stored
# run when every input of it is unchanged, and run the tool otherwise.
# LEAN_CACHE=0 runs them every time (CI does so; it is also the default when
# CI is set), LEAN_CACHE=verify runs them every time and fails when a stored
# run differs. The cache is shared by every worktree of the clone (in the
# main checkout's .claude/work/lean-cache, which git ignores). LEAN_BINARY
# is the real Lean.
LEAN_CACHE ?= $(if $(CI),0,1)
ifneq ($(LEAN_CACHE),0)
GIT_COMMON := $(shell git rev-parse --path-format=absolute --git-common-dir 2>/dev/null)
CHECKOUT := $(if $(filter %/.git,$(GIT_COMMON)),$(patsubst %/.git,%,$(GIT_COMMON)),$(CURDIR))
LEAN_CACHE_DIR ?= $(CHECKOUT)/.claude/work/lean-cache
export LEANFORTH_LEAN_CACHE := $(LEAN_CACHE)
export LEANFORTH_LEAN_CACHE_DIR := $(LEAN_CACHE_DIR)
export LEANEXPORT := $(CURDIR)/scripts/leanexport-cache.py
override LEAN := $(CURDIR)/scripts/lean-cache.py
endif

# Every test command is stopped after TEST_TIMEOUT seconds and then fails,
# so a looping test cannot stall a local run or CI. Uses GNU timeout(1).
TEST_TIMEOUT ?= 1800
# With LF_TIMING_LOG set (scripts/push.sh sets it), each command also appends
# "target seconds exit" to that file, so a normal CI run shows the slow tests.
RUN = $(if $(LF_TIMING_LOG),scripts/timed.sh $(or $@,unnamed) ,)timeout $(TEST_TIMEOUT)
# The tests' own subprocess limits (TEST_LIMIT in tests/*.py) follow it.
export TEST_TIMEOUT
# A Forth test that writes scratch files runs with a folder of its own
# (LF_TEST_SCRATCH, tests/support/scratch.fs; made and removed by the script),
# so the same test run at once by another worktree or make never shares them.
SCRATCH = scripts/with-scratch.sh

# Unit and end-to-end tests (owner, 2026-11-14; TESTING_STRATEGY.md, "Unit and
# end-to-end tests"): tests/test-classes.txt gives every test target of make
# check its class, the one list the Makefile and scripts/test-tier.py read
# (scripts/test-classes.py, make check-test-classes, fails on a target or test
# file in neither class). Unit tests run on Gforth 1.0 (instrumented, in make
# coverage-check), on gforth-fast and, at the push, on Gforth 0.7.3:
#   make test-unit GFORTH=.tools/gforth/bin/gforth-fast
# End-to-end tests run once, on Gforth 1.0: make test-e2e.
TEST_CLASSES := tests/test-classes.txt
test-class = $(shell awk '$$1 ~ /^[a-z][a-z0-9-]*$$/ && $$2 == "$(1)" { print $$1 }' $(TEST_CLASSES))
UNIT_TARGETS := $(call test-class,unit)
E2E_TARGETS := $(call test-class,e2e)
test-unit: $(UNIT_TARGETS)
test-e2e: $(E2E_TARGETS)
check-test-classes:
	$(RUN) python3 tests/scripts/test_test_classes.py
	$(RUN) python3 scripts/test-classes.py
.PHONY: test-unit test-e2e check-test-classes

# Every pinned-Lean oracle and differential comparison. Excludes the
# profiling targets.
DIFFERENTIAL_TARGETS := \
	test-doc-examples-lean \
	reference reference-export reference-first-checker reference-binder-domains \
	reference-definitional-equality test-definitional-equality-differential \
	reference-inductive \
	test-name-differential \
	test-level-differential \
	test-level-assignment-differential test-level-compare-differential \
	test-level-substitute-differential \
	test-mixed-shift-differential test-mixed-instantiate-differential \
	test-mixed-beta-differential test-mixed-convert-differential \
	test-mixed-level-substitute-differential test-mixed-signature-differential \
	test-mixed-infer-differential \
	test-constant-term-scope-differential test-mixed-shift-plain-differential \
	test-mixed-instantiate-plain-differential test-mixed-beta-plain-differential \
	test-mixed-convert-plain-differential test-mixed-infer-plain-differential \
	test-mixed-definition-differential test-mixed-level-substitute-plain-differential \
	test-mixed-infer-constant-differential test-export-signature-differential \
	test-export-specialization-differential test-first-checker-differential \
	test-binder-domains-differential test-universe-scope-differential \
	test-first-checker-large-differential test-binder-domains-large-differential \
	test-universe-scope-large-differential test-first-checker-fed-differential \
	test-binder-domains-fed-differential test-universe-scope-fed-differential \
	test-universe-many-differential test-universe-many-fed-differential \
	test-depth-differential test-depth-fed-differential reference-deep-recursion \
	test-dependencies-differential test-dependencies-fed-differential \
	test-program-differential test-program-stack-differential \
	test-program-values-differential test-program-depth-differential \
	test-example-reference-differential test-add-reference-differential \
	test-abs-reference-differential test-factorial-reference-differential \
	test-gcd-reference-differential test-range-64-differential \
	test-memory-reference-differential test-memory-frame-differential \
	test-printer-differential

.PHONY: test test-differential check check-docs check-doc-examples check-lean-sources check-forth-quality \
	check-portable-forth smoke \
	test-harness test-lib test-core \
	test-composition-fixture test-program test-present profile-existing profile-history \
	forth-metrics $(DIFFERENTIAL_TARGETS)

# Gforth and Python 3 only; run on every CI host and before every commit.
# The slowest targets first (see check below): the command line's parts take
# about 60-125 s each under make coverage-check (2026-11-14).
TEST_CLI_PARTS := test-cli-4 test-cli-1 test-cli-3 test-cli-2 test-cli-engines test-cli-forth
test: $(TEST_CLI_PARTS) test-elab-data-e2e test-author-e2e test-front-e2e
test: test-core test-composition-fixture test-bignum test-run-records test-environment
test: check-tools-untracked check-docs check-lean-sources check-portable-forth check-forth-quality smoke test-harness test-lib test-core \
	test-composition-fixture test-program test-present check-doc-examples check-test-classes

# Fails on broken documentation links or missing docs/ paths.
check-docs:
	$(RUN) python3 scripts/check-doc-links.py
	$(RUN) python3 tests/scripts/test_check_adr_status.py
	$(RUN) python3 scripts/check-adr-status.py
	$(RUN) python3 tests/scripts/test_check_agent_sync.py
	$(RUN) python3 scripts/check-agent-sync.py
	$(RUN) python3 tests/scripts/test_lib_index.py
	$(RUN) python3 scripts/lib-index.py

# Facts the pages restate (the progress page's Mathlib run, the manual's exit-code order,
# the receipt schema the AI guide names) against what they restate: kept apart from the
# slow tests, so that a page's edit re-runs only this under per-target reuse.
test-doc-facts:
	$(RUN) python3 tests/docs/test_doc_facts.py
.PHONY: test-doc-facts
test: test-doc-facts

# The Forth examples of the user pages print exactly the output shown.
DOC_EXAMPLE_PAGES := docs/user/CONCEPTS.md docs/user/TERM_PRINTER.md \
	docs/user/READING_A_LEAN_PROOF.md
# Its LeanForth examples run through the authoring words (src/author/).
DOC_EXAMPLE_PAGES += docs/user/LEANFORTH_SYNTAX.md
check-doc-examples:
	$(RUN) python3 scripts/check-doc-examples.py --gforth $(GFORTH) $(DOC_EXAMPLE_PAGES)

# The same pages' Lean examples, with pinned Lean: accepted or rejected as shown.
test-doc-examples-lean:
	$(RUN) python3 scripts/check-doc-examples.py --gforth $(GFORTH) --lean $(LEAN) \
	$(DOC_EXAMPLE_PAGES)

# Fails on sorry, admit, native_decide or unlisted axioms in Lean test files,
# or a Lean invocation without -DwarningAsError=true. Needs no Lean.
check-lean-sources:
	$(RUN) python3 scripts/check-lean-sources.py

# Fails if current Forth source could depend on byte order or cell size
# (docs/development/FORTH_STYLE.md, section 8).
# .tools holds the machine-local toolchains and Mathlib export (user data). It must never be tracked:
# checking out a commit that tracks a .tools symlink replaced the directory on 2026-11-13.
check-tools-untracked:
	@if git ls-files --error-unmatch .tools >/dev/null 2>&1; then \
	  echo "check-tools-untracked: .tools is tracked by git; run: git rm --cached .tools" >&2; exit 1; fi

check-portable-forth:
	$(RUN) python3 scripts/check-portable-forth.py

# Forth review log and style ratchet (docs/development/forth-reviews/LOG.md,
# tests/forth-quality-baseline.json): fails on main for an unreviewed Forth change; also the lib-caller and
# duplicate checks (plan 9.4.8f).
check-forth-quality:
	$(RUN) python3 tests/scripts/test_check_forth_quality.py
	$(RUN) python3 tests/scripts/test_check_progress.py
	$(RUN) python3 scripts/check-forth-quality.py
	$(RUN) python3 tests/scripts/test_check_lib_callers.py
	$(RUN) python3 scripts/check-lib-callers.py
	$(RUN) python3 tests/scripts/test_check_duplicates.py
	$(RUN) python3 scripts/check-duplicates.py

# Report-only Forth style metrics (word length, globals, locals, shuffling);
# see docs/development/FORTH_STYLE.md. Never fails on style.
forth-metrics:
	python3 scripts/forth-metrics.py --words 20 src

# Requires pinned Lean 4.35.0 as well as Gforth and Python 3.
test-differential: $(DIFFERENTIAL_TARGETS)

# With parallel jobs make starts targets in the order listed: the slowest
# first (each is also named again below), so that none of them starts last.
# Order of the measurement of 2026-11-11 (JOBS=1, no cache, seconds): reference-author 67,
# reference 61, test-cli 56, reference-compact-init 53, test-inductive-table 43 (it and
# reference-inductive share the 27 s Lean run of inductive-expected-output),
# reference-program-ir-run 33, reference-inductive 29, reference-cli 19, ...; since plan
# 5.5.1 (2026-11-12) program-clamp-record runs LeanForth once on the clamp proofs'
# 4,277-declaration export (about 100 s, 2 workers) for reference-program-ir-run and
# reference-program-mutants, which wait for it; since plan 8.4.1b (2026-11-13)
# reference-program-verify-clamp and -refuted each run leanforth verify's driver end
# to end (about 100 s, 2 workers).
CHECK_FIRST := program-clamp-record reference-program-verify-clamp \
	reference-program-verify-refuted reference-program-sha-export reference-demos \
	reference-program-ir-run reference-program-mutants reference-author reference $(TEST_CLI_PARTS) \
	reference-compact-init test-inductive-table reference-inductive reference-cli test-doc-examples-lean \
	test-depth-differential test-depth-fed-differential test-universe-many-differential \
	reference-bignum test-compact-faults
# make check is make test plus check-rest: everything make check runs that the
# instrumented make test of make coverage-check does not stand in for. That is
# every pinned-Lean comparison and other target of make check outside make
# test, and the targets of make test whose Gforth changes under coverage
# (COVERAGE_ENGINE_DIFFERS: test-cli-engines compares bin/leanforth's
# gforth-fast with its checking engine, and make coverage replaces gforth-fast
# by the counting Gforth 1.0). The full change tier (plan 9.4.6;
# scripts/test-tier.py) runs make coverage-check, make test-unit on
# gforth-fast and make check-rest, so make test runs once, instrumented, and
# every end-to-end test of make test (test-cli's parts among them) only
# there. tests/scripts/test_test_tier.py checks that check-rest holds no other
# target of make test.
COVERAGE_ENGINE_DIFFERS := test-cli-engines
check: $(CHECK_FIRST)
check: test check-rest
check-rest: $(filter-out $(TEST_CLI_PARTS),$(CHECK_FIRST)) $(COVERAGE_ENGINE_DIFFERS)
check-rest: test-differential mutants-check test-depth-deep-differential
.PHONY: check-rest

# src/main.fs must load silently: a "redefined" warning means two modules
# define the same word. Then one word from each loaded layer must run.
smoke:
	@out=$$($(RUN) $(GFORTH) src/main.fs -e bye 2>&1) || { printf '%s\n' "$$out" >&2; exit 1; }; \
	if [ -n "$$out" ]; then printf 'src/main.fs printed while loading:\n%s\n' "$$out" >&2; exit 1; fi
	$(RUN) $(GFORTH) tests/smoke/smoke.fs
	@for f in src/*/*.fs; do \
	  out=$$($(RUN) $(GFORTH) $$f -e bye </dev/null 2>&1) || { printf '%s\n' "$$out" >&2; exit 1; }; \
	  if [ -n "$$out" ]; then printf '%s printed while loading on its own:\n%s\n' "$$f" "$$out" >&2; exit 1; fi; \
	done; echo "Every source module loads on its own, silently."

reference:
	LEAN=$(LEAN) $(RUN) bash tests/reference/check.sh

# Lean's verdicts on the first checker's expected-results table (ADR 0011):
# 60 kernel cases and 27 broken source copies Lean must reject.
reference-first-checker:
	LEAN=$(LEAN) $(RUN) bash tests/reference/first-checker-check.sh

# Lean's answers when two binders' domains differ (ADR 0003, Amendment 1):
# 10 comparisons, each in both orders, and 12 declarations.
reference-binder-domains:
	LEAN=$(LEAN) $(RUN) bash tests/reference/binder-domains-check.sh

# Lean's definitional-equality procedure (ADR 0014): 55 cases with Lean's
# verdict and, when accepted, how often each constant was unfolded.
reference-definitional-equality:
	LEAN=$(LEAN) $(RUN) bash tests/reference/definitional-equality-check.sh

reference-export:
	LEAN=$(LEAN) $(RUN) bash tests/reference/export-check.sh

# Lean's verdicts for inductive types, reductions, the replay of exported
# blocks, primitive names and quotients (ADR 0015): 118 kernel cases; the
# exports of tests/reference/inductive/ reproduced byte for byte and staged
# by the Forth importer.
reference-inductive: inductive-expected-output
	INDUCTIVE_EXPECTED_OUT=$(INDUCTIVE_OUT) LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) \
	  bash tests/reference/inductive-check.sh

# Pinned Lean runs inductive-expected.lean once per make: this target (it
# always runs, as a test must) leaves the output where reference-inductive
# and test-inductive-table read it, instead of each running Lean (27 s) again.
# The two scripts run Lean themselves when INDUCTIVE_EXPECTED_OUT is not set.
INDUCTIVE_OUT := $(CURDIR)/build/inductive-expected.out
inductive-expected-output:
	mkdir -p build
	LEAN=$(LEAN) $(RUN) sh -c '"$$LEAN" -DwarningAsError=true \
	  tests/reference/inductive-expected.lean >$(INDUCTIVE_OUT) 2>&1' \
	  || { cat $(INDUCTIVE_OUT) >&2; echo 'Lean failed on inductive-expected.lean' >&2; exit 1; }
.PHONY: inductive-expected-output

# LeanForth against that table (plan task 5.2.1a; ADR 0015 §13, test plan
# 1): every case as the export Lean printed for it, staged, fed and checked;
# each row of task 5.2.1a gives the table's verdict (the pending ones, which
# need Nat or unfolding, the outcome named in the script, with the reason),
# every later task's row stays unsupported or unknown, or gives the table's
# verdict, never another. Also part of test-differential.
test-inductive-table: inductive-expected-output
	INDUCTIVE_EXPECTED_OUT=$(INDUCTIVE_OUT) LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) \
	  python3 tests/core/inductive-table.py
test-differential: test-inductive-table
.PHONY: test-inductive-table

test-harness:
	GFORTH=$(GFORTH) $(RUN) bash tests/harness/check.sh

# The general Forth library in src/lib. The job pool is not loaded by
# src/main.fs, so it gets its own silent-load check; task.fs tests the
# host's workers (threads on Gforth 1.0, cooperative on 0.7.3) and
# task-serial.fs the serial path (task-no-env.fs on a host that does not
# report its stack sizes); task-overflow.fs and its serial twin test
# stack overflows inside jobs. tests/lib/task-bench.fs is report-only.
# test_json_write.py checks the JSON writer against Python's json.dumps.
# runs.fs tests the runs library (sequences of cells that never change)
# against a model, outside the checker.
# sort.fs tests the sorting library against reference sorts (and the
# snapshot's insertion sorts, copied) on both Gforths. memo.fs and
# pqueue.fs test the keyed memo tables and the priority queues against
# models (pqueue.fs also against the scheduler's former heap, copied).
test-lib:
	$(RUN) $(GFORTH) tests/lib/sort.fs
	$(RUN) $(GFORTH) tests/lib/memo.fs
	$(RUN) $(GFORTH) tests/lib/pqueue.fs
	$(RUN) $(GFORTH) tests/lib/decimal.fs
	$(RUN) $(GFORTH) tests/lib/bits.fs
	$(RUN) $(GFORTH) tests/lib/texts.fs
	$(RUN) $(GFORTH) tests/lib/blocks.fs
	$(RUN) $(GFORTH) tests/lib/runs.fs
	$(RUN) $(GFORTH) tests/lib/lib.fs
	$(RUN) $(GFORTH) tests/lib/lib-model.fs
	$(RUN) $(GFORTH) tests/lib/context.fs
	@out=$$($(RUN) $(GFORTH) src/lib/task.fs -e bye 2>&1) || { printf '%s\n' "$$out" >&2; exit 1; }; \
	if [ -n "$$out" ]; then printf 'src/lib/task.fs printed while loading:\n%s\n' "$$out" >&2; exit 1; fi
	$(RUN) $(GFORTH) tests/lib/task.fs
	$(RUN) $(GFORTH) tests/lib/task-serial.fs
	$(RUN) $(GFORTH) tests/lib/task-no-env.fs
	$(RUN) $(GFORTH) tests/lib/bytes.fs
	$(RUN) $(GFORTH) tests/lib/text-rule.fs
	$(RUN) $(GFORTH) tests/lib/name-table.fs
	$(RUN) $(GFORTH) -e hex $(CURDIR)/src/lib/name-table.fs -e "base @ decimal 16 <> throw bye"
	$(RUN) $(GFORTH) tests/lib/json.fs
	$(RUN) $(GFORTH) tests/lib/json-write.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/lib/test_json_write.py
	$(RUN) $(GFORTH) tests/lib/task-overflow.fs
	$(RUN) $(GFORTH) tests/lib/task-overflow-serial.fs

test-core:
	$(RUN) $(GFORTH) tests/core/terms.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/infer_typed_trial.py
	$(RUN) $(GFORTH) tests/core/tagged-sort-boundary.fs
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
	$(RUN) $(GFORTH) tests/core/defeq.fs
	$(RUN) $(GFORTH) tests/core/whnf.fs
	$(RUN) $(GFORTH) tests/core/mixed-level-substitute.fs
	$(RUN) $(GFORTH) tests/core/mixed-level-substitute-crowded.fs
	$(RUN) $(GFORTH) tests/core/mixed-signature-probe.fs
	$(RUN) $(GFORTH) tests/core/mixed-signature-lifecycle.fs
	$(RUN) $(GFORTH) tests/core/mixed-signature-audit.fs
	$(RUN) $(GFORTH) tests/core/mixed-infer.fs
	$(RUN) $(GFORTH) tests/core/mixed-infer-coverage.fs
	$(RUN) $(GFORTH) tests/core/mixed-definition-probe.fs
	$(RUN) $(GFORTH) tests/core/definite-rejection.fs
	$(RUN) $(GFORTH) tests/core/names.fs
	$(RUN) $(GFORTH) tests/core/levels.fs
	$(RUN) $(GFORTH) tests/core/level-scope.fs
	$(RUN) $(GFORTH) tests/core/level-substitute.fs
	$(RUN) $(GFORTH) tests/core/level-value.fs
	$(RUN) $(GFORTH) tests/core/level-compare.fs
	$(RUN) $(GFORTH) tests/core/level-deep.fs
	$(RUN) $(GFORTH) tests/core/level-geq.fs
	$(RUN) $(GFORTH) tests/core/infer-deep.fs
	$(RUN) $(GFORTH) tests/core/contexts.fs
	$(RUN) $(GFORTH) tests/core/contexts-serial.fs
	$(RUN) $(GFORTH) tests/core/contexts-main.fs
	$(RUN) $(GFORTH) tests/core/store-growth.fs
	$(RUN) $(GFORTH) tests/core/diagnostics.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/check_diagnostics_catalogue.py
	$(RUN) $(GFORTH) tests/core/load.fs
	$(RUN) $(GFORTH) tests/core/ndjson.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_ndjson_reader.py

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

# Ports of the pinned-Lean comparisons of the legacy code (retired
# 2026-11-02) onto the current passes; tests/core/lean-differential.py
# documents each table.
LEAN_TABLE := LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/core/lean-differential.py

test-constant-term-scope-differential:
	$(LEAN_TABLE) scope

test-mixed-shift-plain-differential:
	$(LEAN_TABLE) shift

test-mixed-instantiate-plain-differential:
	$(LEAN_TABLE) instantiate

test-mixed-beta-plain-differential:
	$(LEAN_TABLE) beta

test-mixed-convert-plain-differential:
	$(LEAN_TABLE) convert

test-mixed-infer-plain-differential:
	$(LEAN_TABLE) infer

test-mixed-definition-differential:
	$(LEAN_TABLE) definition

test-mixed-level-substitute-plain-differential:
	$(LEAN_TABLE) level-substitute

test-mixed-infer-constant-differential:
	$(LEAN_TABLE) constant

test-export-signature-differential:
	$(LEAN_TABLE) signature-fixture

test-export-specialization-differential:
	$(LEAN_TABLE) poly-specialization

# The first checker end to end (ADR 0011, plan tasks 2.2.1 and 2.2.3):
# every case checked by check-declaration through the checked environment.
# The 62 table cases; the 22 binder-domain cases (ADR 0003 Amendment 1);
# the 50 universe-scope cases (ADR 0012 test-matrix row 4). Every rejection
# agrees with Lean's exception, every other row keeps the table's outcome,
# and every accepted row prints its label and gets a valid handle.
test-first-checker-differential:
	$(LEAN_TABLE) first-checker

test-binder-domains-differential:
	$(LEAN_TABLE) binder-domains

# Lean's definitional-equality procedure (ADR 0014; plan task 4.2.2c):
# the table's rows end to end; sort.*, pi.* and whnf.* give Lean's answer,
# no row contradicts Lean.
test-definitional-equality-differential:
	$(LEAN_TABLE) definitional-equality

test-universe-scope-differential:
	$(LEAN_TABLE) universe-scope

# The same three tables with every store's capacity raised (plan task
# 3.3.1; ADR 0016 C9 step 3): the same answers, and the three binder-domain
# rows that meet the 64-node store at the default capacity get the table's
# answer, so these tables have no known difference.
test-first-checker-large-differential:
	$(LEAN_TABLE) first-checker-large

test-binder-domains-large-differential:
	$(LEAN_TABLE) binder-domains-large

test-universe-scope-large-differential:
	$(LEAN_TABLE) universe-scope-large

# The same three tables through the path a real export takes (plan task
# 3.2.2): each case is written as a lean4export export, staged and fed to
# the checker (src/import/feed.fs), so the names stay in the stage's input
# tier and every store grows to the feed's capacities. The same answers,
# with no known difference.
test-first-checker-fed-differential:
	$(LEAN_TABLE) first-checker-fed

test-binder-domains-fed-differential:
	$(LEAN_TABLE) binder-domains-fed

test-universe-scope-fed-differential:
	$(LEAN_TABLE) universe-scope-fed

# No fixed limit on universe lists (plan task 6.2.0): declarations of 100,
# 300 and 1000 universe parameters and constants with as many arguments,
# accepted or refused for Lean's reason, by checker input and fed.
test-universe-many-differential:
	$(LEAN_TABLE) universe-many

test-universe-many-fed-differential:
	$(LEAN_TABLE) universe-many-fed

# No depth limit (plan task 6.2.0, part (b)): lambda, application and
# successor chains 2,000 deep, by checker input and fed; 10,000 deep, fed,
# in test-depth-deep-differential, part of make check since compact-store
# step S6 made the work linear in the depth (13 minutes before, about 6 s
# since 2026-11-11; plan task 6.5.5).
test-depth-differential:
	$(LEAN_TABLE) depth

test-depth-fed-differential:
	$(LEAN_TABLE) depth-fed

# Lean's deepRecursion is a counted depth, its maxRecDepth (BL-9 in
# docs/project/BEYOND_LEAN.md): pinned Lean's verdicts on application
# chains at the limits for three settings.
reference-deep-recursion:
	$(RUN) $(LEAN) -DwarningAsError=true tests/reference/deep-recursion.lean

.PHONY: test-depth-deep-differential
test-depth-deep-differential:
	$(LEAN_TABLE) depth-deep-fed

# No fixed limit on a check's dependencies or the dependency pool (plan
# task 6.2.0): a declaration using 41 and 1,001 earlier ones, accepted or
# refused for Lean's reason, by checker input and fed, and, fed, a pool
# brought to 66,066, past the old 65,536.
test-dependencies-differential:
	$(LEAN_TABLE) dependencies

test-dependencies-fed-differential:
	$(LEAN_TABLE) dependencies-fed

test-composition-fixture:
	$(RUN) python3 tests/core/test_preview_contract.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_ndjson_preview.py
	$(RUN) python3 tests/core/test_composition_fixture.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/check_composition_fixture.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_export_definitions.py
	$(RUN) python3 tests/core/test_preview_constants.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/constant-term-fixture-test.py
	$(RUN) python3 tests/core/test_preview_dependencies.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_named_levels.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/context-constant-fixture-test.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/declaration-chain-test.py

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

# The presentation layer in src/present: the term printer and its side
# table. Untrusted and not loaded by src/main.fs, so it gets its own
# silent-load check; print-sweep.fs reaches every failure exit of the
# printer, print-deep.fs prints terms and levels 2,000 and 10,000 deep in
# constant host-stack cells, check_golden.py compares the printed text
# with the golden files.
test-present:
	@out=$$($(RUN) $(GFORTH) src/present/term-printer.fs -e bye 2>&1) || { printf '%s\n' "$$out" >&2; exit 1; }; \
	if [ -n "$$out" ]; then printf 'src/present/term-printer.fs printed while loading:\n%s\n' "$$out" >&2; exit 1; fi
	$(RUN) $(GFORTH) tests/present/term-printer.fs
	$(RUN) $(GFORTH) tests/present/print-sweep.fs
	$(RUN) $(GFORTH) tests/present/print-deep.fs
	$(RUN) $(GFORTH) tests/present/notation.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/present/test_outline_block.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/present/check_golden.py

# The printer's Unicode output against pinned Lean's own printing, and its
# ASCII output read back by Lean.
test-printer-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/present/printer-differential.py

# The demos (plan task 8.6.6; docs/user/DEMOS.md): test-demos checks, without
# Lean, that the page is what tests/demos/demos.golden and the Lean sources
# make; reference-demos has pinned Lean prove and export the five theorems,
# LeanForth check and print them (and reject the wrong twins), and compares the
# live text with the golden file, the Lean forms with Lean's #check output.
test-demos:
	$(RUN) python3 tests/demos/build_page.py --check
reference-demos:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/demos/test_demos.py
.PHONY: test-demos reference-demos
test: test-demos
test-differential: reference-demos

profile-existing:
	LEAN=$(LEAN_BINARY) GFORTH=$(GFORTH) $(RUN) bash scripts/profile-existing.sh

profile-history:
	LEAN=$(LEAN_BINARY) GFORTH=$(GFORTH) $(RUN) python3 scripts/profile-history.py

test-program-depth-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/program-depth-differential.sh

test-program-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/differential.sh

test-program-stack-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/program/stack-differential.sh

# Program track, phase 2 (docs/programming/PROGRAM_IR.md and PROGRAM_RECEIPTS.md):
# the receipt schema and its examples, the IR reader, and the copies of the
# reference models in the IR's Lean model. Gforth and Python 3 only.
test-program-ir:
	$(RUN) python3 tests/program/test_receipts.py
	$(RUN) python3 tests/program/check_program_ir.py
	$(RUN) $(GFORTH) tests/program/ir-reader.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/program/ir_reader_files.py

# The IR's Lean model: its proofs, their axioms, and its IR text against the
# reader's golden output for src/program/clamp.fs and examples.fs.
reference-program-ir:
	LEAN=$(LEAN) $(RUN) python3 tests/program/check_program_ir.py --lean

.PHONY: test-program-ir reference-program-ir
test: test-program-ir
test-differential: reference-program-ir

# The program words in two modes (ADR 0019; docs/programming/PROGRAM_IR.md):
# their library, the mode shift and the separate vocabulary, their
# cross-check against today's reader, round trip and random programs.
# Gforth and Python 3 only.
test-program-verify:
	$(RUN) $(GFORTH) tests/lib/text-run.fs
	$(RUN) $(GFORTH) tests/program/verify.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/program/verify_check.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/program/verify_roundtrip.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/program/verify_ir02.py

.PHONY: test-program-verify
test: test-program-verify

# Program track, tasks 2.5.4 to 2.5.6 and 5.5.1 (docs/programming/PROGRAM_IR_RUN.md,
# PROGRAM_VC.md and PROGRAM_RECEIPTS.md): the IR interpreter against the host's
# own words, the verification-condition generator's golden output, the
# generated clamp receipt (schema 0.3), and the export mutation tool on a
# fixture. Gforth and Python 3 only.
test-program-ir-run:
	$(RUN) $(GFORTH) tests/program/ir-run.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/program/ir_run_differential.py
	$(RUN) python3 tests/program/vc_check.py
	$(RUN) python3 tests/program/receipt_check.py
	$(RUN) python3 tests/support/toolchain.py
	$(RUN) python3 scripts/lean_pin.py
	$(RUN) python3 tests/program/clamp_mutants.py --test

# The clamp receipt's evidence recorded afresh once per make (plan 5.5.1): Lean
# exports the clamp proofs with their closure (4,277 declarations), LeanForth
# checks the export with --jobs 2 and saves the checked environment as a
# snapshot, and Gforth runs the IR table; build/program-clamp keeps the
# evidence, the export and the snapshot (ignored by git). The two targets
# below read them instead of each checking the export again (about 100 s of
# two workers each); run alone, their scripts record for themselves.
# An earlier run's files are removed first, by name (the export and snapshot by
# program_receipt.py record --keep, which also fails when no snapshot was written).
PROGRAM_CLAMP := $(CURDIR)/build/program-clamp
program-clamp-record:
	mkdir -p $(PROGRAM_CLAMP)
	rm -f $(PROGRAM_CLAMP)/evidence.json $(PROGRAM_CLAMP)/manifest.json
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 scripts/program_receipt.py record \
	  --out $(PROGRAM_CLAMP)/evidence.json --manifest-out $(PROGRAM_CLAMP)/manifest.json \
	  --keep $(PROGRAM_CLAMP)
.PHONY: program-clamp-record

# The same against pinned Lean: the interpreter against Lean's evaluation of the
# model (tables and random programs), the obligations and contract theorems
# checked by Lean with planted faults, and the receipt's evidence recorded afresh
# (program-clamp-record) equal to the committed evidence.
reference-program-ir-run: program-clamp-record
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/program/ir_run_differential.py --lean
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/program/verify_ir02.py --lean
	LEAN=$(LEAN) $(RUN) python3 tests/program/vc_check.py --lean
	PROGRAM_CLAMP_RECORDED=$(PROGRAM_CLAMP) LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) \
	  python3 tests/program/receipt_check.py --record

# Plan 5.5.1: the clamp export with the program, the contract and the proof
# changed (tests/program/clamp_mutants.py copies) checked by LeanForth against
# the snapshot of the export's own check (program-clamp-record): the originals,
# every one accepted there, taken from it; every changed theorem rejected.
reference-program-mutants: program-clamp-record
	PROGRAM_CLAMP_RECORDED=$(PROGRAM_CLAMP) LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) \
	  python3 tests/program/clamp_mutants.py --test --lean

# The same pipeline for the SHA-256 helper words (stage SHA-2): Lean's proofs of
# sha-rotr, sha-ch, sha-maj and sha-big-sigma0 exported with their closure and
# checked by LeanForth; a changed word body and a changed proof rejected, checked
# against the snapshot of that check. No receipt yet (IR 0.2 programs need
# receipt schema 0.4, at the [format] gate).
reference-program-sha-export:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/program/sha_export_check.py

.PHONY: test-program-ir-run reference-program-ir-run reference-program-mutants \
	reference-program-sha-export
test: test-program-ir-run
test-differential: reference-program-ir-run reference-program-mutants reference-program-sha-export

# leanforth verify's driver v0 (plan 8.4.1b; docs/programming/PROGRAM_VERIFY.md):
# every outcome, exit status and problem code, malformed input, limits and
# state, with the real program words and generator and stand-ins for Lean, its
# exporter and LeanForth's checker; in two halves that run side by side.
# Gforth and Python 3 only.
VERIFY_DRIVER_TESTS := python3 tests/program/test_program_verify.py
test-program-verify-driver:
	GFORTH=$(GFORTH) $(RUN) $(VERIFY_DRIVER_TESTS) Discharged Refuted Unsupported Lean Limits
test-program-verify-driver-input:
	GFORTH=$(GFORTH) $(RUN) $(VERIFY_DRIVER_TESTS) Checker Malformed Workflow Shared
# The command (8.4.1c: bin/leanforth verify, --json, --write-ir) and replay (8.4.1d).
test-program-verify-command:
	GFORTH=$(GFORTH) $(RUN) $(VERIFY_DRIVER_TESTS) Report WriteIr Command Replay

# The driver end to end from the command line with pinned Lean and LeanForth's
# checker (--jobs 2, a final run): lf-clamp discharged and wrong-clamp-swapped
# refuted, each against its golden receipt (about 100 s of two workers each). The
# test switch LEANFORTH_VERIFY_TEST_TOOLS=1 lets the driver use LEAN and LEANEXPORT
# (here the Lean cache); without it the driver runs the checkout's pinned Lean.
reference-program-verify-clamp:
	LEANFORTH_VERIFY_TEST_TOOLS=1 LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) \
	  python3 tests/program/verify_lean_check.py lf-clamp
reference-program-verify-refuted:
	LEANFORTH_VERIFY_TEST_TOOLS=1 LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) \
	  python3 tests/program/verify_lean_check.py wrong-clamp-swapped
# All thirteen committed contracts, the plan's acceptance (about 13 minutes of
# two workers): run by hand, not part of make check.
reference-program-verify-all:
	LEANFORTH_VERIFY_TEST_TOOLS=1 LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) \
	  python3 tests/program/verify_lean_check.py --all

.PHONY: test-program-verify-driver test-program-verify-driver-input test-program-verify-command \
	reference-program-verify-clamp reference-program-verify-refuted reference-program-verify-all
test: test-program-verify-driver test-program-verify-driver-input test-program-verify-command
test-differential: reference-program-verify-clamp reference-program-verify-refuted

# Store marks (plan task 1.1.3) and the checked environment v0 (ADR 0012,
# plan task 2.2.2): unit and failure-path tests, and checks interleaved as
# jobs in two contexts (threads on Gforth 1.0, cooperative on 0.7.3, and
# the serial host). check-declaration (plan task 2.2.3): every outcome,
# Lean's order, dependencies, fuel sweeps, and the pinned NDJSON exports
# checked end to end. The failure-path suite (plan tasks 2.2.4, 1.4.6):
# every allocation of every check refused and thrown in turn, fuel swept,
# and the outcomes reached per check step; then nine planted faults, each
# in a temporary copy of the tree, must each make it fail. The lookup
# lists, the I2 assertion and the snapshot's round trip on every pinned
# export (tests/core/env-snapshot.fs, plan step SN3); the import pass of a
# dependent export, in the I2 build, and a layer (tests/core/env-import.fs,
# step SN4). Gforth and
# Python 3 only.
test-environment:
	$(RUN) $(GFORTH) tests/lib/store-mark.fs
	$(RUN) $(GFORTH) tests/core/environment.fs
	$(RUN) $(GFORTH) tests/core/environment-tasks.fs
	$(RUN) $(GFORTH) tests/core/environment-tasks-serial.fs
	$(RUN) $(SCRATCH) $(GFORTH) tests/core/env-snapshot.fs
	$(RUN) $(SCRATCH) $(GFORTH) tests/core/env-import.fs
	$(RUN) $(GFORTH) tests/core/check-declaration.fs
	$(RUN) $(GFORTH) tests/core/check-declaration-ndjson.fs
	$(RUN) $(GFORTH) tests/core/failure-paths.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/failure_path_faults.py

.PHONY: test-environment
test: test-environment
DOC_EXAMPLE_PAGES += docs/programming/CHECKED_ENVIRONMENT.md

# Inductive blocks (plan task 5.2.1a; ADR 0015): the block check end to
# end on cases of the inductive table, every outcome and rule with its
# diagnostic and step, Lean's replay of the Bool block mutated, blocks
# published together, the reference export tampered one field at a time,
# a fuel bisection and a full term store; the constructor capacity (512
# accepted, 513 and 1,600 full, a valid block after each still accepted).
# Gforth and Python 3.
test-check-block:
	$(RUN) $(GFORTH) tests/core/check-block.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_block_capacity.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_empty_block.py

.PHONY: test-check-block
test: test-check-block
DOC_EXAMPLE_PAGES += docs/user/FIRST_CHECK.md

# The kernel modules the review of 2026-11-12 found without a test file of
# their own (docs/development/forth-reviews/2026-11-12-backlog-kernel.md,
# section 3), on cases of check-block-cases/ (tests/support/case-sweeps.fs):
# the stack effects and outcomes of their words, run inside a check, and
# fuel, refused allocations and crowded stores inside each pass -- iota and
# projections, projection inference, quotients, Nat literals, the
# environment's answers to inference, Lean's generated recursor, heads and
# the rebuild helpers; then sampled sweeps of whole block checks for the
# block, recursor and nested passes. Gforth only; about 9 s on one core.
test-kernel-reduction:
	$(RUN) $(GFORTH) tests/core/iota.fs
	$(RUN) $(GFORTH) tests/core/reduce-nat.fs
	$(RUN) $(GFORTH) tests/core/quot.fs
	$(RUN) $(GFORTH) tests/core/infer-proj.fs
	$(RUN) $(GFORTH) tests/core/env-signature.fs
	$(RUN) $(GFORTH) tests/core/generated-recursor.fs
	$(RUN) $(GFORTH) tests/core/mixed-head.fs
	$(RUN) $(GFORTH) tests/core/mixed-rebuild.fs
	$(RUN) $(GFORTH) tests/core/no-data-terms.fs
test-kernel-blocks:
	$(RUN) $(GFORTH) tests/core/inductive-block.fs
	$(RUN) $(GFORTH) tests/core/inductive-recursor.fs
test-kernel-nested:
	$(RUN) $(GFORTH) tests/core/inductive-nested.fs
# The second coverage pass (COV2, 2026-11-12): terms without a data word
# (no-data-terms.fs, above), string literals' expansion under refused
# allocations, a crowded store and sampled fuel, and sampled fuel through
# definitional equality's eta, unit-like and lazy-delta steps. About 6 s.
test-kernel-passes:
	$(RUN) $(GFORTH) tests/core/string-literals.fs
	$(RUN) $(GFORTH) tests/core/defeq-sweeps.fs
	$(RUN) $(GFORTH) tests/core/check-forged.fs
	$(RUN) $(GFORTH) tests/core/heap-refusals.fs

.PHONY: test-kernel-reduction test-kernel-blocks test-kernel-nested test-kernel-passes
test: test-kernel-reduction test-kernel-blocks test-kernel-nested test-kernel-passes

# Run records and their replay (plan task 2.2.5; docs/programming/RUN_RECORDS.md):
# unit tests of src/import/run-record.fs and run-replay.fs (every fixture, each
# failure, replay findings), then records written to files for the five pinned
# exports and the four broken copies: both schemas, the golden records, two
# processes writing the same bytes, every record replayed, and tampered records
# refused with their codes. Gforth and Python 3 only; Python only drives Gforth
# and reads what it wrote. With a second Gforth (0.7.3, CI's other host):
#   GFORTH=... python3 tests/core/test_run_records.py --other-gforth GFORTH2
test-run-records:
	$(RUN) $(GFORTH) tests/core/run-record.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_run_records.py

# A run record of any lean4export file, and its replay, with Forth alone
# (tests/support/run-records.fs); the record names this tree's commit and
# whether tracked files differ from it. Exit status 0 only for a record
# written, or a record confirmed:
#   make run-record EXPORT=file.ndjson RECORD=file.json [FUEL=100000]
#   make replay EXPORT=file.ndjson RECORD=file.json [FUEL=100000]
FUEL ?= 100000
RR_COMMIT = $(shell git rev-parse HEAD 2>/dev/null)
RR_MODIFIED = $(shell git diff --quiet HEAD -- 2>/dev/null && echo false || echo true)
RR_SOURCE = $(if $(RR_COMMIT),-e 's" $(RR_COMMIT)" $(RR_MODIFIED) ni-source')
run-record:
	$(RUN) $(GFORTH) tests/support/run-records.fs $(RR_SOURCE) \
	-e 's" $(EXPORT)" $(FUEL) s" $(RECORD)" ni-record ni-exit' </dev/null
replay:
	$(RUN) $(GFORTH) tests/support/run-records.fs $(RR_SOURCE) \
	-e 's" $(EXPORT)" $(FUEL) s" $(RECORD)" ni-replay ni-exit' </dev/null

.PHONY: test-run-records run-record replay
test: test-run-records

# Big natural numbers for Lean's Nat literals (plan task 5.2.3, library
# part; docs/development/FORTH_LIBRARY.md): unit tests of every outcome,
# then about 37,500 cases against Python's integers and 20 planted faults
# that must each change a result. Gforth and Python 3 only.
# tests/lib/bignum_bench.py measures speed against Python (report only).
test-bignum:
	$(RUN) $(GFORTH) tests/lib/bignum.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/lib/bignum_differential.py

# A sample of those cases (986, every operation, some of over 3,000 digits)
# computed by pinned Lean's own kernel (decide +kernel), and each of them
# with its result changed rejected.
reference-bignum:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/lib/bignum_differential.py \
	--no-faults --lean

.PHONY: test-bignum reference-bignum
test: test-bignum
test-differential: reference-bignum

# Signed big integers with Lean's Int semantics (plan step FE1i-4;
# src/lib/bigint.fs, a standalone library over bignum.fs): unit tests of
# every word and outcome, every room from 0 cells up and no heap use; then
# 9,906 integer pairs (7,906 edge, 2,000 random), 13 operations each,
# against a model that follows Lean's definitions, and the header's example
# and interface from a folder outside the project. Gforth and Python 3 only.
test-bigint:
	$(RUN) $(GFORTH) tests/lib/bigint.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/lib/bigint_differential.py --pairs 2000

# 17,906 pairs (10,000 random) computed by pinned Lean's own Int, line for
# line, and 300 results decided by Lean's kernel (decide +kernel), each also
# rejected with its value changed.
reference-bigint:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/lib/bigint_differential.py --lean

.PHONY: test-bigint reference-bigint
test: test-bigint
test-differential: reference-bigint

# SHA-256 (src/lib/sha256.fs, a standalone library; docs/development/FORTH_LIBRARY.md):
# FIPS 180-4's vectors, every split of messages up to 200 bytes, the named
# functions against independent models and the fast round against the plain
# one, on both code paths; random messages against Python's hashlib; and the
# header's example run from a folder outside the project. Export manifests
# (plan task 3.2.6; src/import/manifest.fs, scripts/export_manifest.py): the
# writer against the committed manifests and the schema, and the Forth check's
# every failure. Gforth and Python 3 only. tests/lib/sha256-bench.fs measures
# speed (report only).
test-sha256:
	$(RUN) $(GFORTH) tests/lib/sha256.fs
	$(RUN) $(GFORTH) tests/lib/sha256-plain.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/lib/test_sha256.py

# Sectioned binary files (src/lib/sections.fs; plan step SN1): round trips, every
# planted fault with its outcome, then Python's independent reader, the block
# and field-by-field paths byte for byte, and the header's example outside
# the project (tests/lib/test_sections.py).
test-sections:
	$(RUN) $(SCRATCH) $(GFORTH) tests/lib/sections.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/lib/test_sections.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/scripts/test_with_scratch.py

test-manifest:
	$(RUN) $(GFORTH) tests/core/manifest.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_export_manifest.py

# The export step (scripts/export.sh) with pinned Lean reproduces the
# composition fixture and its manifest byte for byte, and the check refuses
# a changed copy.
reference-manifest:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/reference/manifest-check.sh

.PHONY: test-sha256 test-sections test-manifest reference-manifest
test: test-sha256 test-sections test-manifest
test-differential: reference-manifest

# The elaboration data (plan row FE1d; docs/programming/ELABORATION_DATA.md):
# the reader's unit tests and the check step's, then its finisher and every
# damaged file through leanforth check --elab-data. Gforth and Python 3 only.
test-elab-data:
	$(RUN) $(GFORTH) tests/front/elab-data.fs
	$(RUN) $(GFORTH) tests/front/elab-check-lf.fs
test-elab-data-e2e:
	GFORTH=$(GFORTH) $(RUN) python3 tests/front/test_elab_data.py
# With pinned Lean: scripts/export-elab.sh reproduces the init slice's data
# byte for byte, and for all of Init its records equal pinned Lean's own
# counts and LeanForth reads them against Init's export (about 60 s).
reference-elab-data: RUN := timeout 1500
reference-elab-data:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/front/elab-init.sh
.PHONY: test-elab-data test-elab-data-e2e reference-elab-data
test: test-elab-data test-elab-data-e2e
test-differential: reference-elab-data

# The instance table (plans FE1e2 and FE1e3; S1_INTERFACE.md §9): keys,
# isClass?, getUnify and getInstances over the Init slice, and instance
# search (FE1e5, tests/front/synth.fs), Gforth only; with pinned Lean,
# every Init instance's class and keys recomputed, getInstances and 30
# searches (answers and the candidates tried) compared with pinned Lean's
# #synth traces (a few minutes).
test-instances:
	$(RUN) $(GFORTH) tests/front/instances.fs
	$(RUN) $(GFORTH) tests/front/instances-bad.fs
	$(RUN) $(GFORTH) tests/front/instances-odd.fs
	$(RUN) $(GFORTH) tests/front/synth.fs
reference-synth: RUN := timeout 3000
reference-synth:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/front/synth-init.sh
.PHONY: test-instances reference-synth
test: test-instances
test-differential: reference-synth
DOC_EXAMPLE_PAGES += docs/programming/ELABORATION_DATA.md

# The LeanForth authoring words (plan task 8.1.2, ADR 0017; untrusted, not
# loaded by src/main.fs, so they get their own silent-load check): unit
# tests of every error code with its line and column, then the 22 example
# files against their golden report (with each declaration's terms) and a
# round trip each, the error catalogue against
# docs/programming/LEANFORTH_WORDS.md, the check that the checker never
# loads src/author, and round trips over the term printer's cases and the
# five Lean exports. Gforth and Python 3 only. The unit tests are
# host-sensitive (numbers): run them with Gforth 0.7.3 too when the runner
# changes.
test-author:
	@out=$$($(RUN) $(GFORTH) src/author/runner.fs -e bye 2>&1) || { printf '%s\n' "$$out" >&2; exit 1; }; \
	if [ -n "$$out" ]; then printf 'src/author/runner.fs printed while loading:\n%s\n' "$$out" >&2; exit 1; fi
	$(RUN) $(GFORTH) tests/author/author.fs
# The example files and round trips, also through bin/leanforth check and print.
test-author-e2e:
	GFORTH=$(GFORTH) $(RUN) python3 tests/author/check_author.py

# The example files' declarations against pinned Lean's, term for term
# (Lean's own, by a metaprogram, and the pinned exporter's) and as #print
# shows them, and 24 planted faults that must each be caught (five only by
# the comparison with Lean).
reference-author:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/author/check_author.py --lean
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/author/check_author.py --faults

.PHONY: test-author test-author-e2e reference-author
test: test-author test-author-e2e

# The front end's first steps (plan FE1a-c, FE1f, FE1g-2, FE6a, ADR 0021):
# the natural reader's syntax trees and refusals, the metavariable context,
# the Meta layer's level unification and instantiation, the hand-over of a
# finished declaration to the kernel, the generated definitions, and
# tactic proofs read (their records, golden, and every malformed shape,
# also through leanforth check) and run (FE1g-3: blocks, fuel, saved
# states, by-sorry through the kernel, with stand-in statements until
# FE1e; its output is long, so only its tail on a failure), and the first
# tactics (FE1g-4: by-intro:, by-exact, by-rfl, through the kernel too), and
# the elaborator (plan S1, FE1e6-7: tests/front/elab.fs with stand-ins for
# instance search; tests/front/check_elab.py against pinned Lean's golden
# terms through leanforth check). Its modules load alone, printing nothing.
# The modules whose silent load test-front checks are found from the files (tactic plug-in
# design, slice (a1); branch tactic-plugin-design): every front-end file, of src/front/ and of
# its tactics/ and meta-tactic/ folders, but those test-instances and test-elab-data load
# (FRONT_LOADED_ELSEWHERE), and the two core modules only the front end uses.
FRONT_LOADED_ELSEWHERE := src/front/discr-keys.fs src/front/elab-data.fs src/front/elab-keys.fs \
	src/front/instances.fs src/front/synth.fs
FRONT_MODULES := $(filter-out $(FRONT_LOADED_ELSEWHERE),$(sort $(wildcard src/front/*.fs \
	src/front/tactics/*.fs src/front/meta-tactic/*.fs))) src/core/mvar-leaves.fs src/core/reach.fs
test-front:
	@for m in $(FRONT_MODULES); do \
	  out=$$($(RUN) $(GFORTH) $$m -e bye 2>&1) || { printf '%s\n' "$$out" >&2; exit 1; }; \
	  if [ -n "$$out" ]; then printf '%s printed while loading:\n%s\n' "$$m" "$$out" >&2; exit 1; fi; \
	done
	$(RUN) $(GFORTH) tests/front/front.fs
	$(RUN) $(GFORTH) tests/front/meta.fs
	$(RUN) $(GFORTH) tests/front/meta-heap.fs
	$(RUN) $(GFORTH) tests/front/offset-walk.fs
	$(RUN) $(GFORTH) tests/front/constructions.fs
	@out=$$($(RUN) $(GFORTH) tests/front/handover.fs 2>&1) || \
	  { printf '%s\n' "$$out" | tail -20 >&2; exit 1; }; echo "handover.fs: all tests passed"
	$(RUN) $(GFORTH) tests/front/meta-env.fs
	$(RUN) $(GFORTH) tests/front/whnf.fs
	$(RUN) $(GFORTH) tests/front/infer.fs
	$(RUN) $(GFORTH) tests/front/defeq.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_defeq.py --golden
	GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_unfold.py --golden
	GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_whnf.py --golden
	$(RUN) $(GFORTH) tests/front/tactic-syntax.fs
	@out=$$($(RUN) $(GFORTH) tests/front/tactic-run.fs 2>&1) || \
	  { printf '%s\n' "$$out" | tail -20 >&2; exit 1; }; echo "tactic-run.fs: all tests passed"
	@out=$$($(RUN) $(GFORTH) tests/front/tactic-basic.fs 2>&1) || \
	  { printf '%s\n' "$$out" | tail -20 >&2; exit 1; }; echo "tactic-basic.fs: all tests passed"
	@out=$$($(RUN) $(GFORTH) tests/front/tactic-lib.fs 2>&1) || \
	  { printf '%s\n' "$$out" | tail -20 >&2; exit 1; }; echo "tactic-lib.fs: all tests passed"
	@out=$$($(RUN) $(GFORTH) tests/front/menv-run.fs 2>&1) || \
	  { printf '%s\n' "$$out" | tail -20 >&2; exit 1; }; echo "menv-run.fs: all tests passed"
	$(RUN) python3 tests/front/test_front_imports.py
	$(RUN) $(GFORTH) tests/front/goals.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_goals.py
	@out=$$($(RUN) $(GFORTH) tests/front/elab.fs 2>&1) || \
	  { printf '%s\n' "$$out" | tail -20 >&2; exit 1; }; echo "elab.fs: all tests passed"

# The front end end to end: LeanForth text (.lf) checked by bin/leanforth
# check against the tactic, S1 and S2 slices, golden (tactics, elaborator, S2).
test-front-e2e:
	GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_tactics.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_elab.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_s2.py

# The proof set's showcase (scripts/showcase-steps.sh) on S2's slice against its golden
# output (tests/front/showcase.golden), a stopped file and the formatter's refusals.
test-showcase:
	GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_showcase.py

# The natural reader's trees against pinned Lean's macro expansion of the
# same statements (tests/front/operators.lean); the Meta layer's answers
# against pinned Lean's (tests/front/check_meta.py: isLevelDefEqAux,
# instantiate1, abstract, headBeta, instantiateLevelParams;
# tests/front/check_unfold.py: reducibility, canUnfold, getUnfoldableConst?;
# tests/front/check_whnf.py: whnfCore, getStuckMVar?, inferType;
# tests/front/check_defeq.py: isDefEq); pinned
# Lean reproduces the tactic tests' export (tests/front/tactic-slice.ndjson).
reference-front:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_front.py
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_meta.py
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_unfold.py
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_whnf.py
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_defeq.py
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_tactics.py --lean
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_goals.py --lean
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_elab.py --lean
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/front/check_s2.py --lean

# Lean's generated definitions (casesOn, recOn, ctorIdx; plan FE6) built by
# src/front/constructions.fs and ctor-idx.fs for every inductive type of Init, against
# Lean's own in the same export, with pinned counts.
reference-constructions:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/front/constructions-init.sh

# Binder kinds of the Init export against pinned Lean's environment, every
# binder of every declaration's type (plan S1 §4): a measurement, not part
# of make check (it exports Init, 345 MB); fails when a declaration S1
# reads differs. INIT_EXPORT=FILE reuses a pinned export.
reference-binder-kinds:
	LEAN=$(LEAN) $(RUN) python3 tests/front/check_binder_kinds.py \
	  $(if $(INIT_EXPORT),--export $(INIT_EXPORT))

# A tactic's own tests (tactic plug-in design, slice (a1)): tests/front/tactics/NAME/test.fs is
# the unit target test-tactic-NAME and tests/front/tactics/NAME/check.py the end-to-end target
# test-tactic-NAME-e2e, both part of make test, found from the files, so a branch that adds a
# tactic edits no Makefile line (tests/test-classes.txt classes them by pattern).
TACTIC_UNIT_TARGETS := $(patsubst tests/front/tactics/%/test.fs,test-tactic-%,\
	$(sort $(wildcard tests/front/tactics/*/test.fs)))
TACTIC_E2E_TARGETS := $(patsubst tests/front/tactics/%/check.py,test-tactic-%-e2e,\
	$(sort $(wildcard tests/front/tactics/*/check.py)))
$(TACTIC_UNIT_TARGETS): test-tactic-%:
	$(RUN) $(GFORTH) tests/front/tactics/$*/test.fs
$(TACTIC_E2E_TARGETS): test-tactic-%-e2e:
	GFORTH=$(GFORTH) $(RUN) python3 tests/front/tactics/$*/check.py
.PHONY: $(TACTIC_UNIT_TARGETS) $(TACTIC_E2E_TARGETS)
test: $(TACTIC_UNIT_TARGETS) $(TACTIC_E2E_TARGETS)
test-unit: $(TACTIC_UNIT_TARGETS)
test-e2e: $(TACTIC_E2E_TARGETS)

.PHONY: test-front test-front-e2e test-showcase reference-front reference-constructions reference-binder-kinds
test: test-front test-front-e2e test-showcase
test-differential: reference-front
test-differential: reference-constructions
test-differential: reference-author

# Planted faults (plan task 1.4.2; docs/development/TESTING_STRATEGY.md,
# "Planted faults"): each fault of tests/mutants/faults.toml is written into
# a temporary copy of the tree, never this one, and the test it names must
# then fail. Not part of make test or make check. mutants-quick runs the
# faults marked quick, mutants-check only reports stale entries (old text
# no longer found once) and replacement texts changed by a commit that does
# not name the fault (plan 9.4.8j); test-mutants, part of make test, tests
# the runner and checks that history rule on the branch's commits.
# LEAN is the pinned binary itself (LEAN_BINARY), never the cache wrapper:
# the runner's controls include the Lean cache's own tests. FAULTS=ID,...
# runs only those faults (make tier; mutants.py --only); MUTANT_TEST_TIMEOUT is
# the seconds one test may take (a fault that times out counts as caught).
MUTANTS_TIMEOUT ?= 3600
MUTANT_TEST_TIMEOUT ?= 120
mutants:
	LEAN=$(LEAN_BINARY) timeout $(MUTANTS_TIMEOUT) python3 scripts/mutants.py --gforth $(GFORTH) \
	--timeout $(MUTANT_TEST_TIMEOUT) $(if $(FAULTS),--only $(FAULTS))

mutants-quick:
	LEAN=$(LEAN_BINARY) $(RUN) python3 scripts/mutants.py --gforth $(GFORTH) --quick

mutants-check:
	$(RUN) python3 scripts/mutants.py --check

test-mutants:
	$(RUN) python3 tests/mutants/test_mutants.py
	$(RUN) python3 scripts/mutants.py --history

# Block coverage of src/ over make test (plan task 1.4.1; TESTING_STRATEGY.md,
# "Block coverage"): every Gforth run of make test loads Gforth 1.0's
# coverage.fs first, and the blocks that ran are counted per folder. Needs
# Gforth 1.0 (LEANFORTH_GFORTH, the real one: GFORTH is the strict wrapper);
# fails when no counts, or fewer runs than the baseline's, are collected.
# coverage-check is the ratchet (tests/coverage-baseline.json): it fails when a
# file's never-run blocks grow; part of make check, not of make test. After a
# justified change: python3 scripts/coverage.py --update-baseline [--reason TEXT].
# test-coverage tests the tool itself (part of make test).
COVERAGE_GFORTH = $(or $(LEANFORTH_GFORTH),$(GFORTH))
coverage:
	$(RUN) python3 scripts/coverage.py --gforth $(COVERAGE_GFORTH) -- make test JOBS=$(JOBS)

coverage-check:
	$(RUN) python3 scripts/coverage.py --gforth $(COVERAGE_GFORTH) --check -- make test JOBS=$(JOBS)

test-coverage:
	GFORTH=$(GFORTH) $(RUN) python3 tests/support/test_coverage.py

# The ratchet for COVERAGE_FILES alone, over the targets COVERAGE_TARGETS only
# (the smaller change tiers of scripts/test-tier.py name every target of make
# test that loads the files, so their counts are those of the whole make test).
coverage-focus:
	$(if $(COVERAGE_FILES),,$(error coverage-focus needs COVERAGE_FILES and COVERAGE_TARGETS))
	$(RUN) python3 scripts/coverage.py --gforth $(COVERAGE_GFORTH) --check \
	$(addprefix --only ,$(COVERAGE_FILES)) -- make $(COVERAGE_TARGETS) JOBS=$(JOBS)

.PHONY: mutants mutants-quick mutants-check test-mutants coverage coverage-check test-coverage \
	coverage-focus
# The coverage ratchet runs in the full change tier (make tier, scripts/push.sh),
# not in make check: it runs the whole of make test, instrumented (about 6 min at
# JOBS=2), and stands in for make test there (check-rest above).
test: test-coverage
test: test-mutants

# The NDJSON re-exporter (plan task 3.2.4; docs/development/NDJSON_READER.md,
# "Re-export"): unit tests of every record kind, every failure and two
# planted faults; then every export under tests/ re-exported through files,
# byte for byte, and read back into the same dump, seeded sweeps of other
# spellings and of the reader's mutations, and the comparison tool. Gforth
# and Python 3 only.
test-reexport:
	$(RUN) $(GFORTH) tests/core/ndjson-emit.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_ndjson_emit.py

# Pinned Lean's export of every record kind is tests/core/reexport/kinds.ndjson,
# and its export of a string literal with every class of escape re-exports
# byte for byte.
reference-reexport:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/reexport/lean-check.sh

# Re-export any export and compare the copy with it, byte for byte, then
# read the copy back (not with COPY=-, which streams and keeps no copy):
#   make reexport EXPORT=file.ndjson COPY=copy.ndjson
# Uses the pinned gforth-fast; all of Mathlib takes several minutes.
REEXPORT_TIMEOUT ?= 7200
reexport:
	timeout $(REEXPORT_TIMEOUT) bash scripts/ndjson-reexport.sh \
	$(if $(filter -,$(COPY)),,--reimport) "$(EXPORT)" "$(COPY)"

.PHONY: test-reexport reference-reexport reexport
test: test-reexport
test-differential: reference-reexport
# The compact store (ADR 0016; plan tasks 1.1.5 and 6.2.0-6.2.2, library
# part): growable heap stores, hash tables, hashing and hash-consed sets in
# two tiers (src/lib/slab.fs, htab.fs, hash32.fs, cons.fs, pools.fs) and
# Lean's names, levels and expressions on them (src/core/compact*.fs). Unit
# tests with randomized models, then every pinned reference export loaded
# into the store by the importer stage, with its manifest, and re-emitted
# as the NDJSON reader dumps it. Gforth only.
test-compact:
	$(RUN) $(GFORTH) tests/lib/hash32.fs
	$(RUN) $(GFORTH) tests/lib/slab.fs
	$(RUN) $(GFORTH) tests/lib/store-columns.fs
	$(RUN) $(GFORTH) tests/lib/htab.fs
	$(RUN) $(GFORTH) tests/lib/cons.fs
	$(RUN) $(GFORTH) tests/core/compact.fs
	@for f in tests/reference/*.ndjson; do \
	  $(RUN) bash tests/core/compact-verify.sh $$f $(GFORTH) >/dev/null \
	  || { bash tests/core/compact-verify.sh $$f $(GFORTH); exit 1; }; \
	done; echo "The compact store re-emits every reference export as the reader dumps it."

# The importer stage (ADR 0016 C9 step 2, plan 3.2.1; src/import/stage.fs):
# unit tests (life cycle, declarations read back, lookups, resolutions,
# rollbacks, the memory limit, forged bad references, mdata marked, a
# scratch tier as a context member), the cases that need a changed export
# (unknown constants, duplicate names, truncated files, 32-bit limits), and
# every other fixture export of tests/, which have no manifest (loaded
# unchecked, explicitly), re-emitted as the reader dumps it, with every
# declaration found by name and every constant's resolution checked. The
# input tier saved and loaded (src/import/snapshot-tier.fs, plan step SN2):
# round trips record by record and byte for byte, the checker fed both ways,
# the planted file faults (tests/core/snapshot-tier.fs); saved and loaded in
# two processes, stage-continue (tests/core/test_stage.py; LF_OTHER_GFORTH
# names a second engine to load what the first wrote, and the reverse).
# Gforth and Python 3 only.
STAGE_FIXTURES := tests/core/check-declaration-cases/*.ndjson tests/core/ndjson-block.ndjson \
	tests/core/reexport/kinds.ndjson tests/core/stage-cases/*.ndjson
test-stage:
	$(RUN) $(GFORTH) tests/core/stage.fs
	$(RUN) $(SCRATCH) $(GFORTH) tests/core/snapshot-tier.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_stage.py
	@for f in $(STAGE_FIXTURES); do \
	  $(RUN) bash tests/core/compact-verify.sh --unchecked $$f $(GFORTH) >/dev/null \
	  || { bash tests/core/compact-verify.sh --unchecked $$f $(GFORTH); exit 1; }; \
	done; echo "The stage re-emits every other fixture export as the reader dumps it."

# Twenty-seven faults planted in a copy of the compact store, each caught by the
# checks of test-compact (about 25 s; part of make check).
test-compact-faults:
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/compact_faults.py

# Lean's Init, exported by the pinned leanexport with its manifest, staged
# into the compact store and re-emitted: all 6.4 million name, level,
# expression and declaration records equal the reader's dump (about 1.5
# minutes with gforth-fast).
# It exports and stages all of Init, about 1.5 minutes here but close to the
# 600 s test limit on CI's smaller runners with 8 jobs at once (CI runs
# 41900142434 and 41902902037 timed out), so it alone gets 1,500 s.
reference-compact-init: RUN := timeout 1500
reference-compact-init:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/compact-init.sh

.PHONY: test-compact test-stage test-compact-faults reference-compact-init
test: test-compact test-stage
check-rest: test-compact-faults
test-differential: reference-compact-init

# The derivation log (ADR 0013, plan task 2.4.1; docs/programming/DERIVATION_LOG.md)
# and the proof outline printed from it (plan task 2.4.4; docs/user/PROOF_OUTLINE.md):
# the log of every pinned export and broken copy off, on and full at every bound,
# with nothing changed; the checker trials with the log off, on, full and
# interleaved; the golden outlines; the rule catalogue against its documentation;
# the isolation rules. Gforth and Python 3 only.
test-log:
	$(RUN) $(GFORTH) tests/core/derivation-log.fs
	$(RUN) $(GFORTH) tests/core/log-trials.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/present/check_outline.py
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/check_log_catalogue.py
	$(RUN) python3 tests/core/check_log_isolation.py

# The proof outline of every declaration of a Lean export (or of the one
# named NAME), or with DETAIL=1 every step of its derivation log: bin/leanforth
# print, with its exit codes (docs/user/COMMAND_LINE.md):
#   make print EXPORT=tests/reference/composition.ndjson [DETAIL=1] [NAME=composition]
print:
	GFORTH=$(GFORTH) $(RUN) bin/leanforth print $(if $(DETAIL),--detail) \
	$(if $(NAME),--name $(NAME)) $(EXPORT)

# The evidence that the log changes nothing (ADR 0013, owner decision D5): all of
# make test and every pinned-Lean comparison of make test-differential with the
# log on in every context (tests/support/gforth-log.sh), then on and full after 5
# records, then make test with 2 term copies, 1 level copy and 3 open rules.
# About ten minutes; not part of make check. The chain is: the strict wrapper
# (GFORTH, always) runs LEANFORTH_GFORTH, which the inner make sets to the log
# wrapper (named by its absolute path, as tests run from other folders too),
# which runs LF_GFORTH, the real Gforth: never the strict wrapper, or the two
# would call each other (gforth-log.sh refuses a second level).
LOG_GFORTH = $(if $(findstring /,$(LEANFORTH_GFORTH)),$(abspath $(LEANFORTH_GFORTH)),$(shell command -v $(LEANFORTH_GFORTH)))
LOG_RUN = LF_GFORTH=$(LOG_GFORTH) LF_LOG_LEVEL=2
LOG_WRAPPER = GFORTH=$(CURDIR)/tests/support/gforth-log.sh
check-log-identity:
	$(LOG_RUN) $(MAKE) test test-differential $(LOG_WRAPPER)
	$(LOG_RUN) LF_LOG_RECORDS=5 $(MAKE) test test-differential $(LOG_WRAPPER)
	$(LOG_RUN) LF_LOG_TERMS=2 LF_LOG_LEVELS=1 LF_LOG_MARKS=3 $(MAKE) test $(LOG_WRAPPER)

.PHONY: test-log print check-log-identity
test: test-log
DOC_EXAMPLE_PAGES += docs/user/PROOF_OUTLINE.md

# The command line (plan tasks 3.4.1-3.4.2; docs/user/COMMAND_LINE.md): the
# Forth side's exit codes, their severity, the record hook and two injected
# internal faults; then bin/leanforth itself, every exit code 0-5 with its
# output, from other folders, against the counter and the re-exporter, and
# with a broken Gforth. The page's console examples run in check-doc-examples.
# Gforth and Python 3 only.
# The command-line tests run as four parts that make can run at once
# (tests/cli/run_group.py; 236 s on one core in one part, 2026-11-12), and the
# engine tests (the Engines class: gforth-fast against the checking engine) as
# a fifth, which make check-rest runs again without coverage (COVERAGE_ENGINE_DIFFERS).
# test-cli-forth is the Forth side's unit tests; the others are end to end.
test-cli: $(TEST_CLI_PARTS)
test-cli-forth:
	$(RUN) $(GFORTH) tests/cli/leanforth.fs
test-cli-1 test-cli-2 test-cli-3 test-cli-4 test-cli-engines:
	GFORTH=$(GFORTH) $(RUN) python3 tests/cli/run_group.py $(subst test-cli-,,$@)
.PHONY: test-cli-forth test-cli-1 test-cli-2 test-cli-3 test-cli-4 test-cli-engines

# Pinned Lean accepts the two Lean fixtures of the command line's tests and
# scripts/export.sh reproduces their exports and manifests byte for byte.
reference-cli:
	LEAN=$(LEAN) GFORTH=$(GFORTH_FAST) $(RUN) bash tests/cli/export-check.sh

# The default engine of bin/leanforth, gforth-fast, against Gforth's checking
# engine (--checked): all of Init (--jobs 8) and the arena tests, verdict lines
# and exit codes compared; exit 0 only if identical. About 15 minutes; needs
# the machine-local Init export and arena tests (scripts/engine-gate.sh). Not
# part of make check.
engine-gate: RUN := timeout 7200
engine-gate:
	$(RUN) bash scripts/engine-gate.sh $(ENGINE_GATE_INIT) $(ENGINE_GATE_ARENA)

.PHONY: engine-gate
.PHONY: test-cli reference-cli
# make test names test-cli's parts at its start (TEST_CLI_PARTS), the slowest first.
test-differential: reference-cli
DOC_EXAMPLE_PAGES += docs/user/COMMAND_LINE.md

# The Lean cache (scripts/lean-cache.py; TESTING_STRATEGY.md, "Running the
# suites"): with a fake toolchain, a repeated call replayed exactly, every
# input's change missing the cache, what is never cached, verify mode, and
# the Makefile's choice of the cache (never with LEAN_CACHE=0 or CI set).
# Python 3 and make only.
test-lean-cache:
	$(RUN) python3 tests/lean-cache/test_lean_cache.py

# The targets of make test (test-changed) or make check (check-changed) that
# use a file changed since the merge base with BASE (default main),
# uncommitted and new files included (scripts/changed-tests.py prints why
# with --why). For an agent's inner loop only: make test before each commit.
BASE ?= main
test-changed check-changed:
	@targets=$$(python3 scripts/changed-tests.py --why --base $(BASE) $(@:-changed=)) \
	|| exit 1; if [ -z "$$targets" ]; then echo "No target uses a changed file."; \
	else $(MAKE) --no-print-directory $$targets; fi

.PHONY: test-lean-cache test-changed check-changed check-tools-untracked
test: test-lean-cache

# Tested-tree records and change tiers (plan 9.4.6; TESTING_STRATEGY.md,
# "Running the suites"). make once GOALS="check" runs make GOALS and records
# the pass, unless a pass of them on this exact tree (git's tree hash; a
# worktree with uncommitted changes is refused) with the same Gforth, Lean
# and LEAN_CACHE is already recorded, in the main checkout's
# .claude/work/ci/tested/ (TESTED_DIR elsewhere): then it prints that record
# and runs nothing. make tier runs so every suite of the change tier of
# BASE...HEAD (scripts/test-tier.py), then the progress check; DRY_RUN=1
# prints what would run. Both name $(MAKE), so make prints their output as
# it comes (and runs them even under make -n, as test-changed). test-tiers
# tests the classifier, the records and push.sh's choices on throw-away
# repositories (Python 3, git and make only).
GOALS ?= test
once:
	@python3 scripts/tested-tree.py once -- $(MAKE) $(GOALS) JOBS=$(JOBS) \
	GFORTH=$(LEANFORTH_GFORTH) LEAN=$(LEAN_BINARY) LEAN_CACHE=$(LEAN_CACHE)
tier:
	@python3 scripts/tested-tree.py tier --make $(MAKE) --base $(BASE) --jobs $(JOBS) \
	--lean-cache $(LEAN_CACHE) --gforth $(LEANFORTH_GFORTH) --lean $(LEAN_BINARY) $(if $(DRY_RUN),--dry-run)
test-tiers:
	$(RUN) python3 tests/scripts/test_test_tier.py
	$(RUN) python3 tests/scripts/test_tested_tree.py
	$(RUN) python3 tests/scripts/test_check_tactic_plugins.py
# The daily full run (owner, 2026-11-17: its own command, once a night and before a tag;
# a push only reports its age): the full tier of HEAD with LEAN_CACHE=0 and Gforth 0.7.3,
# each suite recorded for this exact tree; DRY_RUN=1 prints what would run. make tag-check
# exits 0 only when this tree has a complete daily run (a tag requires one).
daily:
	@python3 scripts/tested-tree.py daily --make $(MAKE) --jobs $(JOBS) \
	--gforth $(LEANFORTH_GFORTH) --lean $(LEAN_BINARY) $(if $(DRY_RUN),--dry-run)
tag-check:
	@python3 scripts/tested-tree.py tag-check

.PHONY: once tier test-tiers daily tag-check
test: test-tiers

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

# Every pinned-Lean oracle and differential comparison. Excludes the
# profiling targets.
DIFFERENTIAL_TARGETS := \
	test-doc-examples-lean \
	reference reference-export reference-first-checker reference-binder-domains \
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
	test-program-differential test-program-stack-differential \
	test-program-values-differential test-program-depth-differential \
	test-example-reference-differential test-add-reference-differential \
	test-abs-reference-differential test-factorial-reference-differential \
	test-gcd-reference-differential test-range-64-differential \
	test-memory-reference-differential test-memory-frame-differential \
	test-printer-differential

.PHONY: test test-differential check check-docs check-doc-examples check-lean-sources \
	check-portable-forth smoke \
	test-harness test-lib test-core \
	test-composition-fixture test-program test-present profile-existing profile-history \
	forth-metrics $(DIFFERENTIAL_TARGETS)

# Gforth and Python 3 only; run on every CI host and before every commit.
test: check-docs check-lean-sources check-portable-forth smoke test-harness test-lib test-core \
	test-composition-fixture test-program test-present check-doc-examples

# Fails on broken documentation links or missing docs/ paths.
check-docs:
	$(RUN) python3 scripts/check-doc-links.py

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
check-portable-forth:
	$(RUN) python3 scripts/check-portable-forth.py

# Report-only Forth style metrics (word length, globals, locals, shuffling);
# see docs/development/FORTH_STYLE.md. Never fails on style.
forth-metrics:
	python3 scripts/forth-metrics.py --words 20 src

# Requires pinned Lean 4.35.0 as well as Gforth and Python 3.
test-differential: $(DIFFERENTIAL_TARGETS)

check: test test-differential mutants-check

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

reference-export:
	LEAN=$(LEAN) $(RUN) bash tests/reference/export-check.sh

test-harness:
	GFORTH=$(GFORTH) $(RUN) bash tests/harness/check.sh

# The general Forth library in src/lib. The job pool is not loaded by
# src/main.fs, so it gets its own silent-load check; task.fs tests the
# host's workers (threads on Gforth 1.0, cooperative on 0.7.3) and
# task-serial.fs the serial path (task-no-env.fs on a host that does not
# report its stack sizes); task-overflow.fs and its serial twin test
# stack overflows inside jobs. tests/lib/task-bench.fs is report-only.
# test_json_write.py checks the JSON writer against Python's json.dumps.
test-lib:
	$(RUN) $(GFORTH) tests/lib/lib.fs
	$(RUN) $(GFORTH) tests/lib/lib-model.fs
	$(RUN) $(GFORTH) tests/lib/context.fs
	@out=$$($(RUN) $(GFORTH) src/lib/task.fs -e bye 2>&1) || { printf '%s\n' "$$out" >&2; exit 1; }; \
	if [ -n "$$out" ]; then printf 'src/lib/task.fs printed while loading:\n%s\n' "$$out" >&2; exit 1; fi
	$(RUN) $(GFORTH) tests/lib/task.fs
	$(RUN) $(GFORTH) tests/lib/task-serial.fs
	$(RUN) $(GFORTH) tests/lib/task-no-env.fs
	$(RUN) $(GFORTH) tests/lib/bytes.fs
	$(RUN) $(GFORTH) tests/lib/json.fs
	$(RUN) $(GFORTH) tests/lib/json-write.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/lib/test_json_write.py
	$(RUN) $(GFORTH) tests/lib/task-overflow.fs
	$(RUN) $(GFORTH) tests/lib/task-overflow-serial.fs

test-core:
	$(RUN) $(GFORTH) tests/core/terms.fs
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
	$(RUN) $(GFORTH) tests/core/mixed-level-substitute.fs
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
	$(RUN) $(GFORTH) tests/core/infer-deep.fs
	$(RUN) $(GFORTH) tests/core/contexts.fs
	$(RUN) $(GFORTH) tests/core/contexts-serial.fs
	$(RUN) $(GFORTH) tests/core/contexts-main.fs
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
# the 49 universe-scope cases (ADR 0012 test-matrix row 4). Every rejection
# agrees with Lean's exception, every other row keeps the table's outcome,
# and every accepted row prints its label and gets a valid handle.
test-first-checker-differential:
	$(LEAN_TABLE) first-checker

test-binder-domains-differential:
	$(LEAN_TABLE) binder-domains

test-universe-scope-differential:
	$(LEAN_TABLE) universe-scope

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
# printer, check_golden.py compares the printed text with the golden files.
test-present:
	@out=$$($(RUN) $(GFORTH) src/present/term-printer.fs -e bye 2>&1) || { printf '%s\n' "$$out" >&2; exit 1; }; \
	if [ -n "$$out" ]; then printf 'src/present/term-printer.fs printed while loading:\n%s\n' "$$out" >&2; exit 1; fi
	$(RUN) $(GFORTH) tests/present/term-printer.fs
	$(RUN) $(GFORTH) tests/present/print-sweep.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/present/check_golden.py

# The printer's Unicode output against pinned Lean's own printing, and its
# ASCII output read back by Lean.
test-printer-differential:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/present/printer-differential.py

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

# Program track, phase 2, tasks 2.5.4 to 2.5.6 (docs/programming/PROGRAM_IR_RUN.md,
# PROGRAM_VC.md and PROGRAM_RECEIPTS.md): the IR interpreter against the host's
# own words, the verification-condition generator's golden output, and the
# generated clamp receipt. Gforth and Python 3 only.
test-program-ir-run:
	$(RUN) $(GFORTH) tests/program/ir-run.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/program/ir_run_differential.py
	$(RUN) python3 tests/program/vc_check.py
	$(RUN) python3 tests/program/receipt_check.py

# The same against pinned Lean: the interpreter against Lean's evaluation of the
# model (tables and random programs), the obligations and contract theorems
# checked by Lean with planted faults, and the receipt's evidence recorded afresh.
reference-program-ir-run:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/program/ir_run_differential.py --lean
	LEAN=$(LEAN) $(RUN) python3 tests/program/vc_check.py --lean
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/program/receipt_check.py --record

.PHONY: test-program-ir-run reference-program-ir-run
test: test-program-ir-run
test-differential: reference-program-ir-run

# Store marks (plan task 1.1.3) and the checked environment v0 (ADR 0012,
# plan task 2.2.2): unit and failure-path tests, and checks interleaved as
# jobs in two contexts (threads on Gforth 1.0, cooperative on 0.7.3, and
# the serial host). check-declaration (plan task 2.2.3): every outcome,
# Lean's order, dependencies, fuel sweeps, and the pinned NDJSON exports
# checked end to end. The failure-path suite (plan tasks 2.2.4, 1.4.6):
# every allocation of every check refused and thrown in turn, fuel swept,
# and the outcomes reached per check step; then nine planted faults, each
# in a temporary copy of the tree, must each make it fail. Gforth and
# Python 3 only.
test-environment:
	$(RUN) $(GFORTH) tests/lib/store-mark.fs
	$(RUN) $(GFORTH) tests/core/environment.fs
	$(RUN) $(GFORTH) tests/core/environment-tasks.fs
	$(RUN) $(GFORTH) tests/core/environment-tasks-serial.fs
	$(RUN) $(GFORTH) tests/core/check-declaration.fs
	$(RUN) $(GFORTH) tests/core/check-declaration-ndjson.fs
	$(RUN) $(GFORTH) tests/core/failure-paths.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/failure_path_faults.py

.PHONY: test-environment
test: test-environment
DOC_EXAMPLE_PAGES += docs/programming/CHECKED_ENVIRONMENT.md
DOC_EXAMPLE_PAGES += docs/user/FIRST_CHECK.md

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

test-manifest:
	$(RUN) $(GFORTH) tests/core/manifest.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/test_export_manifest.py

# The export step (scripts/export.sh) with pinned Lean reproduces the
# composition fixture and its manifest byte for byte, and the check refuses
# a changed copy.
reference-manifest:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/reference/manifest-check.sh

.PHONY: test-sha256 test-manifest reference-manifest
test: test-sha256 test-manifest
test-differential: reference-manifest

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
	GFORTH=$(GFORTH) $(RUN) python3 tests/author/check_author.py

# The example files' declarations against pinned Lean's, term for term
# (Lean's own, by a metaprogram, and the pinned exporter's) and as #print
# shows them, and 24 planted faults that must each be caught (five only by
# the comparison with Lean).
reference-author:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/author/check_author.py --lean
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/author/check_author.py --faults

.PHONY: test-author reference-author
test: test-author
test-differential: reference-author

# Planted faults (plan task 1.4.2; docs/development/TESTING_STRATEGY.md,
# "Planted faults"): each fault of tests/mutants/faults.toml is written into
# a temporary copy of the tree, never this one, and the test it names must
# then fail. Not part of make test or make check. mutants-quick runs the
# faults marked quick, mutants-check only reports stale entries (old text
# no longer found once); test-mutants, part of make test, tests the runner.
MUTANTS_TIMEOUT ?= 3600
mutants:
	timeout $(MUTANTS_TIMEOUT) python3 scripts/mutants.py --gforth $(GFORTH)

mutants-quick:
	$(RUN) python3 scripts/mutants.py --gforth $(GFORTH) --quick

mutants-check:
	$(RUN) python3 scripts/mutants.py --check

test-mutants:
	$(RUN) python3 tests/mutants/test_mutants.py

# Block coverage of src/ over make test (plan task 1.4.1; TESTING_STRATEGY.md,
# "Block coverage"): every Gforth run of make test loads Gforth 1.0's
# coverage.fs first, and the blocks that ran are counted per folder. Needs
# Gforth 1.0; not part of make test or make check.
coverage:
	$(RUN) python3 scripts/coverage.py --gforth $(GFORTH)

.PHONY: mutants mutants-quick mutants-check test-mutants coverage
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
# into the store and re-emitted as the NDJSON reader dumps it. Not loaded by
# src/main.fs yet; make smoke loads each module on its own. Gforth only.
test-compact:
	$(RUN) $(GFORTH) tests/lib/hash32.fs
	$(RUN) $(GFORTH) tests/lib/slab.fs
	$(RUN) $(GFORTH) tests/lib/htab.fs
	$(RUN) $(GFORTH) tests/lib/cons.fs
	$(RUN) $(GFORTH) tests/core/compact.fs
	@for f in tests/reference/*.ndjson; do \
	  $(RUN) bash tests/core/compact-verify.sh $$f $(GFORTH) >/dev/null \
	  || { bash tests/core/compact-verify.sh $$f $(GFORTH); exit 1; }; \
	done; echo "The compact store re-emits every reference export as the reader dumps it."

# Nineteen faults planted in a copy of the compact store, each caught by the
# checks of test-compact (about 25 s; part of make check).
test-compact-faults:
	GFORTH=$(GFORTH) $(RUN) python3 tests/core/compact_faults.py

# Lean's Init, exported by the pinned leanexport, loaded into the compact
# store and re-emitted: all 6.4 million name, level and expression records
# equal the reader's dump (about 1.5 minutes with gforth-fast).
reference-compact-init:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) bash tests/core/compact-init.sh

.PHONY: test-compact test-compact-faults reference-compact-init
test: test-compact
check: test-compact-faults
test-differential: reference-compact-init

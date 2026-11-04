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

check: test test-differential

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
# the 17 universe-scope cases (ADR 0012 test-matrix row 4). Every rejection
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
# checked end to end. Gforth only.
test-environment:
	$(RUN) $(GFORTH) tests/lib/store-mark.fs
	$(RUN) $(GFORTH) tests/core/environment.fs
	$(RUN) $(GFORTH) tests/core/environment-tasks.fs
	$(RUN) $(GFORTH) tests/core/environment-tasks-serial.fs
	$(RUN) $(GFORTH) tests/core/check-declaration.fs
	$(RUN) $(GFORTH) tests/core/check-declaration-ndjson.fs

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

# The LeanForth authoring words (plan task 8.1.2, ADR 0017; untrusted, not
# loaded by src/main.fs, so they get their own silent-load check): unit
# tests of every error code with its line and column, then the 19 example
# files against their golden report with a round trip each, the error
# catalogue against docs/programming/LEANFORTH_WORDS.md, the check that
# the checker never loads src/author, and round trips over the term
# printer's cases and the five Lean exports. Gforth and Python 3 only.
test-author:
	@out=$$($(RUN) $(GFORTH) src/author/runner.fs -e bye 2>&1) || { printf '%s\n' "$$out" >&2; exit 1; }; \
	if [ -n "$$out" ]; then printf 'src/author/runner.fs printed while loading:\n%s\n' "$$out" >&2; exit 1; fi
	$(RUN) $(GFORTH) tests/author/author.fs
	GFORTH=$(GFORTH) $(RUN) python3 tests/author/check_author.py

# The example files' theorems and definitions as pinned Lean's #print shows
# them, and seven planted faults that must each be caught (the spelling
# check disabled only by the comparison with Lean).
reference-author:
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/author/check_author.py --lean
	LEAN=$(LEAN) GFORTH=$(GFORTH) $(RUN) python3 tests/author/check_author.py --faults

.PHONY: test-author reference-author
test: test-author
test-differential: reference-author

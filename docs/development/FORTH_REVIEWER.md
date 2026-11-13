# Forth reviewer guide

Use this guide for a focused human or agent review of LeanForth Forth code. It
is a checklist, not an autonomous reviewer, a proof, or a replacement for the
project's required human reviews. Read `AGENTS.md` and the applicable contracts,
design decisions, module comments and tests first. Establish the exact change
and its callers; inspect dependencies where their stack effects, guarantees or
status codes matter. Review both the theorem and executable-program trust
boundaries when relevant.

## When reviews run, and the log (owner, 2026-11-12)

Every change to Forth source under `src/` is reviewed before it reaches `main`; correctness reviews of the checker
do not replace this review. The coordinator runs the reviewer on the branch's commit range (`BASE..HEAD`), saves
the report in [forth-reviews/](forth-reviews/LOG.md) and adds a row to its `LOG.md`; `make test`
(`scripts/check-forth-quality.py`) fails on `main` for any later commit changing `src/**/*.fs` outside a logged
range. Findings are fixed before the merge (the fix commits reviewed again, briefly) or recorded as plan tasks; the
row says how many remain open. The same script holds the style ratchet (`tests/forth-quality-baseline.json`); a
commit that raises it must say why in its review row. The reviewer also checks the tests of every changed word
against the coverage classes of [the coverage review](TEST_COVERAGE_REVIEW.md) and the planted faults in
`tests/mutants/faults.toml`, and reports missing ones as findings.

## Review procedure

1. Identify public words, internal helpers, state and ownership. Record the
   intended stack effects, inputs, outputs, failure modes and assumptions. Follow
   each public call through validation, mutation and result production.
2. Trace the data stack on every branch and exit, including variable-arity
   success/failure results. Trace return-stack use through loops, `EXIT`,
   `UNLOOP`, and calls; check loop bounds, empty ranges and nesting. Verify flags
   are consumed correctly and that callers use the actual returned convention.
3. Before judging factoring, look for existing words in the generated word index
   ([LIBRARY_WORDS.md](LIBRARY_WORDS.md)) and read the duplicate report
   (`python3 scripts/check-duplicates.py --report`; plan 9.4.8f): a new copy of an indexed word or a new
   duplicate group is a finding.
   Check idiom and factoring against [the Forth style guide](FORTH_STYLE.md),
   which is the project standard. Run
   `python3 scripts/forth-metrics.py --words 10 <files>` on the reviewed files
   and include its summary in the report. Raise a finding — with a concrete
   refactoring, not just a remark — for each of these:
   - a colon definition longer than five lines, unless a comment justifies it;
   - a `VARIABLE` (or `CREATE`d cell) used as a register to pass values between
     words, or across a few lines of one word, instead of the stack;
   - emulated locals: a global frame array addressed by magic slot numbers;
   - raw field offsets (`3 cells +`) in algorithm code instead of named
     accessors or `BEGIN-STRUCTURE` fields;
   - a long `IF` chain dispatching on a tag instead of `CASE` or an
     execution-token table;
   - a repeated phrase (such as the same error-exit sequence) that should be a
     named word;
   - a word that takes more than about three stack items or uses `PICK`/`ROLL`;
   - per-module status codes plus translation words where the shared outcome
     vocabulary would do, or a status consumed as a flag;
   - locals used where factoring would serve.
   Also suggest named helpers for distinct responsibilities, and check
   initialization and re-entrancy of any state that legitimately stays global.
   Do not shorten code by dropping validation, obscuring control flow,
   weakening resource bounds, or hiding a trust boundary; when a longer word is
   genuinely clearer, it must say why in a comment.
3a. **Reuse: look beyond the diff** (owner, 2026-11-13; AGENTS.md "Reuse
   first"). Mandatory in every review, whatever its size or report length; a
   review that skips it is incomplete. The reviewer must:
   - list each new or changed word that does something general: sorting,
     searching, tables, maps, heaps, stacks and frames for non-recursive
     walks, term or tree walks, memo caches, growable arrays, bounds and index
     checks, outcome chains and loops, number and text formatting, parsing,
     JSON;
   - for each, search for an existing word that already does it: the library
     words ([FORTH_LIBRARY.md](FORTH_LIBRARY.md), `src/README.md`'s `lib/`
     row, and the generated word index once plan 9.4.8f adds it), then
     `grep -rn` across all of `src/` by name and by shape (the same loop, the
     same push and pop, the same tag test), not only the changed files;
   - run `python3 scripts/check-duplicates.py` and
     `python3 scripts/check-lib-callers.py` (plan 9.4.8f, once on `main`) and
     quote their new entries; when the coordinator names branches in flight,
     compare their copies of the same operation too;
   - check the reverse: a general operation written inside a Lean module
     that belongs in `lib/` or a shared module, a module started as a copy of
     another (renamed prefixes), and a new library word with no caller.
   Each such case is a **blocking** finding that names the existing word to
   use, or the library or shared word to write and every copy it replaces. It
   is fixed before the merge, or the coordinator records a plan row in a named
   slice and the review cites it; "left as a note" is not an outcome.
4. Examine cell arithmetic, signed versus unsigned comparisons, overflow,
   alignment, address arithmetic, capacities, initialization and lifetime.
   Check array and arena bounds before access; identify caller-owned storage and
   aliasing assumptions. Check repeated calls, resets, stale handles and identity
   reuse, plus concurrent or nested calls if the contract permits them.
5. Follow every error path. Malformed input must fail closed, and exhaustion,
   invalid input, unknown results and success must stay distinct. Check stack
   cleanup, loop cleanup, rollback and what state may change on failure. Verify
   cross-module status mappings explicitly rather than assuming equal numbers.
6. Assess Forth-2012 portability word by word, including required word sets,
   environmental dependencies, cell width, numeric base, alignment, signed
   representation and implementation-defined behavior. Identify host extensions
   and their adapters. A source inspection is not a cross-host portability test;
   report exactly which hosts and versions were actually exercised.
7. Check comments on modules and public words against behavior: stack effects,
   ordering, types and units, ownership, side effects, failures, resource limits,
   assumptions and non-obvious algorithms. Check that each module `require`s
   exactly the files whose words it uses (never `include`), so it loads on
   its own, and that `main.fs` lists only the top modules. Keep internal
   helpers' preconditions visible. Comments must distinguish checked facts from
   unchecked inputs, structural validation and host/runtime assumptions.
8. Read the tests and identify missing meaningful cases: positive and negative
   behavior, each branch and stack shape, limits, malformed input, overflow,
   stale state, reentrancy assumptions and failure after partial mutation. Use
   sentinels or depth checks where useful for both stacks. For shared DAGs,
   test resource behavior and explicitly stated fuel semantics. Run relevant
   existing tests when the host is available; record commands, versions, results
   and any unavailable tools. Do not infer passing tests from their presence.
9. Trace authority: parsing, imported declarations, structural checks and
   generated explanations never establish theorem validity. Verify that only the
   trusted checker can do so and that axiom policy is explicit. For programs,
   separate source semantics and proof from host execution and compiler or FFI
   assumptions. Review changes to kernel semantics, imports, certificates,
   axioms, bypasses, compiler/FFI assumptions and mathematical parsing under
   the human review gates in `AGENTS.md`; an agent review cannot waive them.

## Findings and handoff

Report findings first, ordered by impact: correctness and trust risks, then
portability, maintainability and test gaps. Give a path and line, the concrete
trigger, consequence, and a practical remedy or test. Distinguish demonstrated
bugs from potential risks, documented limitations and style suggestions; do not
invent a failure. Note well-factored code when no improvement is justified.

Report reuse in its own section in every review, even when nothing is found:
what was searched (the index, the `grep` patterns, the duplicate and caller
checks) and each finding with the word to use or the library to write. A
one-line "Reuse: none" without the searches is not a review.

Report Forth style in its own section, not as an afterthought: the metrics
summary, then each style-guide finding with the proposed factoring, written
as Forth (new word names and stack comments). Style findings are not optional
cleanup; code that will become the trusted checker must be small, readable
words, because reviewers must be able to trace every one.
Include the review scope, commands and observed tool versions, tests actually
run, and limitations. For kernel-semantic changes, identify the required ADR,
positive/negative tests, pinned Lean comparison and human review. Never claim
that review or test execution proves correctness.

## Evaluation of the reviewer (2026-11-02)

The 18 AI reviews recorded in `docs/reviews/` from 2026-10-30 and 10-31
checked correctness and trust boundaries carefully but never raised
factoring, idiom or word length; global mutable state appeared only as a
listed limitation. Meanwhile 22% of words grew past ten lines and the code
accumulated 378 `VARIABLE`s. The style section of step 3, the
[style guide](FORTH_STYLE.md) and the metrics script were added in response.

A review of `src/kernel/mixed-infer.fs` with these in place found no
bugs, and it raised the 59-line walker, unnamed frame slots, nine repeated
error exits, raw slot offsets that bypass the module's own accessors,
variables used as registers, an internal word used as an undocumented
interface by another module, and the non-standard `>=`. Each came with a
Forth refactoring. That review ran while the style guide was still
uncommitted, so it is not a clean before-and-after comparison. Repeat such
an evaluation on another module after major guideline changes.

## Evaluation of the reviewer (2026-11-13): reuse

The [library audit](forth-reviews/2026-11-13-library-audit.md) found about 27 hand-written push and pop copies on
slabs, two term walkers sharing 37 identical words, 7 hand-written sorts beside an unused `lib/sort.fs`, and about 130
copies of one outcome loop, almost all merged after a logged Forth review. Why the reviews missed them: they read the
diff, and nothing told them to search `lib/` or the rest of `src/` for the same operation, so a hand-written sort
looked correct in isolation; there was no compact index of library words; the one reuse proposal (review fe1c-2, S2:
`slab-push` in `lib/slab.fs`, 2026-11-12) was a suggestion that the re-check accepted as "a plan note", and no plan
row followed; the coordinator asked for short one-round reviews to save tokens, which discouraged looking beyond the
change; and parallel branches were invisible to each review. Changes: step 3a and the reuse section of the report,
both mandatory and blocking; the generated word index, the duplicate detector and the library-caller check (plan
9.4.8f); a library proposal must cite a plan row before the review is logged. Repeat the evaluation with planted reuse
defects (plan 9.4.8h): a branch with a hand-written sort, a module started as a renamed copy of another and a new
library word with no caller; the reviewer must find all three.


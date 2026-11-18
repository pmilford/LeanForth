# Whole-code Forth review, fourth pass: src/present (rest) and the 14 small src/front files
**Range:** whole files at main `f90c71d9` (not a diff review; `f90c71d9..f90c71d9`).
**Findings: 19.** BLOCKS 3 (PB1-PB3). REUSE PASS 7 (R9-R15). Note 9 (N8-N16).
**What was run:** read-only, on a `git archive f90c71d9` scratch copy. 12 printer probes on Gforth 1.0.0 (tests/present/build.fs helpers). 9 planted faults in the scratch copy, each restored and checked with `cmp`. `forth-metrics.py`, `check-duplicates.py`, `check-lib-callers.py`. No suite, no Lean run: I compared the Lean ports by reading the pinned Lean source. This AI review does not replace the owner's human review.

## For the owner (plain language)
- **Universe levels match Lean.** I compared normalize, the max/imax simplifications, parameter substitution and Lean's name order with Lean's own source, line by line, and found no difference. My planted faults there were caught.
- **casesOn, recOn and ctorIdx are built as Lean builds them.** Shapes they do not handle are refused, not guessed. This code is not used by the product yet (R14).
- **Names print differently from Lean (PB1).** Lean writes a name part that is not a plain identifier between « and ». The term printer writes it bare, so `Foo.«a.b»` prints as `Foo.a.b`, which is a different name. The command line already has a correct speller (cli/name-text.fs); the printer should use it.
- **The step log's "accepted" test is weaker than the kernel's (PB2).** I could not trigger it, but the fix is one word.
- **`Nat.succ k` against `k.succ` (PB3):** this is Lean's "generalized field notation". The rule and what it would take are below; it is a planned gap (plan 8.6).
- **Reuse:** two name spellers, two LaTeX text escapers that disagree, two superscript tables, a hand-written decimal converter, two hand-written block growers.
- **Coverage:** 27 files read whole and 1 in part. What is still unread in src/ is listed at the end: four whole folders (kernel, core, lib, import) were outside all four passes.

## Findings (ranked)
**PB1 (BLOCKS: a difference from Lean; the printed name can denote another name).** present/print-names.fs:33-45 `lf-pp-name-to`, used through print-tokens.fs:72-77 (`lf-pp-name`, `lf-pp-constant`) and goal-print.fs:120-132, writes every component raw.
- **What Lean does:** Name.toString puts a non-identifier component between « » (Init/Data/ToString/Name.lean).
- **Probe e8:** the binder `a_b}` prints `fun a_b} ↦ a_b}`. Lean prints `«a_b}»`. A component holding a dot prints as two components.
- **Probe e9:** U+202E reaches the sink raw in Unicode mode. `print` escapes it later (test_print_crafted_binder_and_constant), but `.goals` and goal texts go to the printer's sink without that escape.
- **Fix:** move cli/name-text.fs's component rule (identifier test, « », \u{X} for banned characters) to present/ and call it from `lf-pp-part`, keeping `lf-tex-ident` for LaTeX. Pin `«a.b»`, `«a_b}»` and U+202E in tests/present, with a fault on the « » branch.

**PB2 (BLOCKS unless shown unreachable: a trust-boundary predicate).** cli/leanforth.fs:1070-1071 `cli-step-find` decides "accepted" by `lf-env-outcome ok?`. The kernel's own word is `lf-slot-accepted?` (environment.fs:553: final *and* ok). step-log.fs:5 promises a log "for the declarations the kernel accepted only". This is the same weaker test as pass 3's N1.
- **Fix:** `: cli-step-find ( c-addr u -- d true | false ) pr-newest 0= if false exit then dup lf-env-accepted nip ok? dup 0= if nip then ;`
- Plant a fault that restores `lf-env-outcome`.

**PB3 (BLOCKS: a difference from Lean, already listed in goal-print.fs:27-32 and owned by plan 8.6).** Goals print `Nat.succ k` where Lean prints `k.succ`.
- **Lean's rule:** PrettyPrinter/Delaborator/FieldNotation.lean `fieldNotationCandidate?` and `generalizedFieldInfo`, on by default (pp.fieldNotation.generalized). Field notation is used for `C.f a…` when:
  - the head is a constant `C.f` whose last component is a string; C is not `Function`; the head is not private-inaccessible and has no `pp_nodot` attribute; the head is not a proof;
  - the first binder whose type has head C (after reducible unfolding) is explicit, every binder before it is non-explicit, and no binder is named `motive`;
  - the argument's inferred type has head C;
  - the head is not written with `@` (needsExplicit).
  Structure projections take a separate path (`projInfo`): the object is argument numParams, and class projections are excluded unless they are parent projections. The result prints as `obj.f rest`, with obj at max precedence.
- **What it would take here:**
  1. a step in term-printer.fs before the application step, reading the head's declared type through `lf-pres-type@` (as print-analysis.fs:235 already does) for the binder kinds, the names and the head test;
  2. the argument's type: the goal printer can get it from the front end's `lf-infer` through a hook; the plain printer has no inference, so it keeps today's form;
  3. structure and projection information from the export;
  4. `pp_nodot`, which is not in exports: an explicit list (Real.sqrt and others) or the elaboration data.
- **Size:** about 40 words and a hook. Tests: the GAPS pair in tests/front/check_goals.py becomes a pass.

**R9 (REUSE PASS).** There are two name spellers, print-names.fs `lf-pp-name-to` and cli/name-text.fs `nt-name`. This is the cause of PB1; one speller, in present/, serves both.

**R10 (REUSE PASS, with an inconsistency).** LaTeX text-mode escaping is written twice:
- print-strings.fs:26-31 `lf-pq-tex-byte` writes `^` as `\textasciicircum{}`;
- statement-forms.fs:78-87 `lf-sf-tex-form` writes `^` as `\^{}`.
latex-text.fs:33-57 already has the mode record (`/lf-tex-mode`) meant to serve both. Fix: move `lf-sf-tex-mode` into latex-text.fs as `lf-tex-text-mode` and use it from print-strings.

**R11 (REUSE PASS).** There are two superscript-digit tables: goal-print.fs:79-85 (two CASE tables) and print-notation.fs:128-130. Add one `: lf-pp-super ( d -- c-addr u )` in print-tokens.fs, the string table form.

**R12 (REUSE PASS).** ctor-idx.fs:59 `digits` re-implements lib/decimal.fs `u>decimal`. Replace it: `u>decimal r@ aux-tier tier-texts text-intern`.

**R13 (REUSE PASS).** Two hand-written allocate/resize growers: constructions.fs:201-204 `aux-reserve` and cases-several.fs:51-57 `block-grow`. Use lib/slab.fs, as every other growable array does, or add one `block-grow ( u addr -- outcome )` in lib/blocks.fs.

**R14 (REUSE PASS: a module without a caller).** constructions.fs, cases-several.fs, ctor-idx.fs and expr-remap.fs (about 1,000 lines, 24 planted faults) are required by no file of src/, only by tests (plan FE6).
- They define unprefixed global words that will collide once main.fs loads them: `digits implicit arrow motive grow alt` (ctor-idx), `target cases moved pi? app? large? conclusion stripped type-name decl-of apply-var` (constructions), `anonymous plain-binder` (expr-remap).
- **Fix:** prefix them (`aux-`, `rmp-`) or hide them behind one wordlist; give FE6 a slice that adds the caller.

**R15 (REUSE PASS: double work).** level-map.fs:48-54 runs the image xt twice per universe argument: once in `lmap-moved?`, once in `lmap-fill`. Under level-params.fs that is a fresh dag-walk each time. Fill the pairs block once, then compare the levels against the old ones.

**N8 (note: cost, no fuel).** print-analysis.fs:258-272: `lf-pp-shown#` and `lf-pp-last` call `lf-pp-visible?` for each argument. Each call walks the spine (`lf-pp-head`) and the parameter chain (`lf-pp-avail`): O(n²) per application, and fuel is spent on none of it. Read the head and the kinds once per application, into the frame.

**N9 (note: an unbounded loop on malformed data).** elab-keys.fs:107 `elab-term-end` has no bound ("there must be one"). Stop it at `elab-keys#`, or assert `elab-one-term?` at every caller.

**N10 (note: differences from Lean that fail closed or are cosmetic).**
- constructions.fs:398-399: recOn's structure case refuses when casesOn is missing, where Lean falls back to the generic recOn (RecOn.lean:27-29).
- print-analysis.fs:276-286: `@` goes only before atom heads, where Lean's needsExplicit (Builtins.lean:276) takes any head. A head whose type unfolds to more Pis prints `@f a`, because getParamKinds reduces and this printer does not.
- print-notation.fs:34-35: an over-applied operator prints in kernel form, where Lean prints `(f + g) x`.

**N11 (note).** proof-outline.fs:503-519 prints "accepted; axioms: unlisted" with no NOT PROVED mark. Its own comment at :502 and the command line's reports say NOT PROVED. Add the mark.

**N12 (note).** print-forth.fs:336-341 `lf-pf-captured-in?` interns names (`lf-name-graft`) during a print. print-job.fs:12-16 forbids store changes during a print. Document this exception, or use a non-interning lookup.

**N13 (note).** print-forth.fs:311-312: a concrete Sort n prints words that build the symbolic Sort. The header's claim (:2-4) of "the identical term: the same nodes" is then false; state the exception.

**N14 (note).** step-log.fs:90-92, 131-136: after a refused axiom list, the header is written with `"axioms":null` and the run stops. A writer failure in mid-line leaves a last line without its line feed, and nothing marks the file as cut.

**N15 (note: fixed stores).** note-table.fs:20-21 holds 64 entries and 4,096 bytes (as the author pass's R5). log-view.fs:154-156 and log-check.fs:113-118 walk the premises once per premise: O(n²) per listed step.

**N16 (note: tests seen from the code).**
- **Surviving fault:** goal-print.fs:148 `gp-deeper` without the let rule (`1- 0 max`) survives both tests/front/check_goals.py and goals.fs. Add a tactic goal with a let value whose depth crosses 254 only through nested lets.
- **No planted fault:** print-tokens.fs (pass 3 noted this), syntax.fs. term-find.fs has only 1.
- **No test pins:** PB1's names, PB2's predicate, N11.

## Lean fidelity checked (no finding)
- **Levels:** level-normalize = Level.normalize, normLtAux, ctorToNat, getMaxArgsAux, skipExplicit, isExplicitSubsumed, mkMaxAux/accMax, mkIMaxAux (Level.lean:267-410). Flattening normal forms instead of raw maxes gives the same list; the imax offset is added outside, as Lean does. lf-meta-name-cmp = Name.cmp (the root-most differing pair wins; a number before a string).
- **Simplifications:** level-simp = mkLevelMaxCore and mkLevelIMaxCore (:519-552). level-params = substParams and updateMax!/updateIMax! with ptrEq (:564-621); node identity stands in for ptrEq.
- **Constructions:** isCasesOnViaProjs (CasesOn.lean:28-33) and mkCtorIdx (CtorIdx.lean:41-80, `x`, `Level.one`, raw literals).
- **Printer:** the notation table's precedences (Notation.lean:280-420, Core.lean:197); useAppExplicit; sanitizeNames numbering in goal-print.

## Probes run (Gforth 1.0.0; output as printed)
- **e1:** `∃ x x_1, x = x_1` (capture avoided). **e11:** `fun x ↦ ∃ x_1, x = x_1`.
- **e2/e3:** `1 = 2 ∧ ∃ x, x = x` and `(∃ x, x = x) ∧ 1 = 2`. **e4:** `¬∃ x, x = x`, mathtext `¬(∃ x, x = x)`.
- **e5:** `- -2` in all modes. **e6:** `2 · (0 + 1)`. **e7:** `1 = 2 ∈ s` (Lean parses it the same way). **e12:** `-(1 + 2)`.
- **e8/e9:** PB1, as above. **e10:** `\alpha_{1}`. LaTeX escapes `_ }` and writes U+202E as `\backslash{}u\{202E\}`.
- **Planted faults:**
  - caught: name-cmp num/str flipped, name-cmp shorter-first flipped, subsumes `<=`→`<`, updateMax! without simp (meta.fs exit 1, 1, 1, 139); inaccessible-shadow (check_goals 1); let depth `<=`→`<` (goals.fs 1);
  - survived: the let depth rule (N16).
- **Not run:** a goal print through the CLI, a cut step log, PB2's trigger, proof-outline's recognisers.

## Forth style (`forth-metrics.py --words 10`, 28 files)
- **Summary:** 1,751 words; 72% of 1-2 lines, 26% of 3-5, 20 of 6-10, none longer. 12 globals (9 CREATE tables, 3 xt-tables, all read-only), 23 context members, 1 "local" (a false positive: `{\ttfamily` in statement-forms.fs:120), 134 deep shuffles, 715 return-stack operations (print-job 39, print-notation 45: the frame protocol, which print-job.fs:143-147 justifies). check-duplicates: "284 baseline groups, none new or grown". check-lib-callers: OK.
- **Long words:** all are CASE tables (proof-outline.fs:537 `lf-ol-bound`, statement-forms.fs:78 `lf-sf-tex-form`, print-analysis.fs:69/149), which R10 and xt-tables would shorten. Split proof-outline.fs:259 `lf-ol-single`, :291 `lf-ol-discharge` and :582 `lf-ol-statement` into sentence and rule parts.
- **Shuffles:**
  - statement-forms.fs:168 `lf-sf-copy` (`2 pick 2 pick 2 pick`): pass decl alone and re-push the kind text inside each line word;
  - statement-forms.fs:131 `2 pick` inside `?do`: keep the address under `>r`;
  - note-table.fs:85 `2 pick`.
- **Good:** latex-text's mode record; print-forth's xt-tables by tag; level-simp's rule codes; expr-remap's frame steps; lctx-views' immutable locals.

## Reuse searched
- **Tools:** both scripts, as above.
- **Greps over src/:**
  - name spellers (`lf-pp-name-to`, `nt-name`, `«`);
  - LaTeX escapers (`textbackslash`, `textasciicircum`, `\^{}`);
  - superscript tables (⁰¹);
  - `<# #s #>` against lib/decimal.fs;
  - `allocate … resize` growers;
  - every generic name in R14 (`^: name`);
  - who requires constructions, cases-several and ctor-idx;
  - the step log's caller and `lf-slot-accepted?`;
  - `tests/mutants/faults.toml` counts per file.
- **New** next to the three earlier passes: PB1-PB3, R9-R15, N8-N16 (PB2 is the same predicate as pass 3's N1, at a new site).

## Files
- **Read whole (27):**
  - present (13): print-job, print-tokens, latex-text, print-strings, binder-table, print-analysis, print-notation, notation-table, note-table, statement-forms, print-forth, log-view, log-check;
  - front (14): level-map, level-normalize, level-params, level-simp, constructions, cases-several, ctor-idx, expr-remap, lctx-views, goal-print, step-log, term-find, syntax, elab-keys.
- **In part (1):** present/proof-outline.fs 1-260 and 494-698. Lines 261-493 (the recognisers and the walk) are not read.
- **Not read (stopped at about two thirds of context):** program/ir-reader.fs, ir-run.fs and verify-alias.fs beyond their headers; scripts/program_receipt.py beyond pass 3's lines 334-420.
- **Still unread in all of src/, by the four passes' lists:**
  - all of src/kernel (42 files, 16,571 lines), src/core (32, 7,338), src/lib (35, 8,139) and src/import (13, 6,436), and src/main.fs (outside these passes' scope; earlier reviews may cover them);
  - author/export.fs after line 120;
  - proof-outline.fs 261-493;
  - the program files above.
- **Uncertainties:**
  - PB2's trigger (an ok slot that is not final) was not built;
  - PB3's cost is an estimate;
  - Lean's printing of e6's `Nat.succ 0` (field notation on a literal) was not run.

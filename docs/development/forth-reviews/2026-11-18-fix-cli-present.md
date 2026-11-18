# Forth review: fix-cli-present, f8340f54..7a966b1a (7 commits)
**Findings: 15.** BLOCKS 2 (F1, F2). Should fix before merge 4 (F3-F6). REUSE PASS 2 (R1, R2). Note 7 (N1-N7).
**Verdict: blocking.** F1 (plain `print` outlines now print garbled names) and F2 ([format] gate: published schemas 0.4 and 0.5 edited in place). B1, N3, N5, N11, N14 and N16 are fixed as claimed.

## For the owner (plain language, gate statement)
- Fuel (B1) is fixed. With `--fuel 50/100/200` the text and the JSON both say 50/100/200, in the total and in "most fuel used". Nothing else in the resource report changed.
- New bug (F1): `print` without `--latex` mangles any name that needs « ». `Foo.«a.b»` prints as `Foo.«a.b\u{BB}`, and a name holding a hidden direction mark prints as a run of backslashes. Before this branch these printed readably. Two escaping steps share one buffer. No test covers it.
- F2: the JSON report schemas 0.4 and 0.5 were changed in place to allow `axiomBits: null`, for a case no run can reach. My recommendation is to undo that, not to approve it, and to treat the case as an internal fault.
- F3: `check` now writes Init's `inferInstanceAs` and `StateRefT` as `«inferInstanceAs»` in the text and the JSON. Lean's own name text writes them bare; only Lean's term printer adds « ». My recommendation: use « » for these names only in printed terms.
- Gates: [kernel], [import], [parser], [bypass]: none touched. [format]: F2 and F3.
- User-visible changes: (1) exhausted checks report their whole budget; (2) `print` outlines add "; NOT PROVED: depends on an axiom"; (3) `print --lf` with stubs exits 2 and adds a note on stderr; (4) a failed `--steps FILE` is cut back to its last whole line, and the error line says so; (5) `capabilities` makes no Mathlib claim; (6) names in terms, goals and `print` are spelled as Lean writes them (`Foo.«a.b»`, `«fun»`), and a hidden control is escaped; (7) `check` and JSON names whose first part is a word of Lean's syntax get « » (F3); (8) the schemas accept `axiomBits` null (F2). Item (6) is currently broken in plain `print` (F1).

## Findings
**F1 (BLOCKS: the user is told something wrong; input aliasing).**
- Where: src/cli/leanforth.fs:1427 installs `nt-text` as the plain outline's escape hook. src/present/log-view.fs:107-110 (`lf-lv-safe`) applies it to every piece of term text. src/present/print-names.fs:44 hands the sink `nt-part`'s text, which lives in nt-out. `nt-text` (name-text.fs:212) then runs `nt-start`, which clears that same slab, and rewrites it while reading it.
- Results: the closing » becomes `\u{BB}`. A backslash re-reads its own output, so `«a\u{202E}b»` comes out as `«a\\\\\\\\\\\\\\\\\\\\\\`. If the slab grows during that rewrite, the source it is reading has been freed.
- Repro: pinned Lean, export `theorem oddStmt : «a‮b» = «a‮b»` (built with `addDecl`), then `bin/leanforth print --no-manifest --name oddStmt X.ndjson`. Head prints "Statement in Lean: «a\\\\…"; the base printed `a\u{202E}b`. `--latex` is fine.
- Fix: term text already arrives escaped (names through nt-part, strings through print-strings), so pass 0 as the escape for printer output. If text still needs escaping, give `nt-text` its own slab and never call it on nt-out.
- Test: a `print` of an export holding `Foo.«a.b»`, `«a‮b»`, `Foo.«».x` and `Foo.a«b»c`, plus a planted fault that puts the hook back.

**F2 (BLOCKS: [format] gate).**
- What changed: schemas/check-report-0.4.schema.json:255-257 and 0.5:869-878 now take `anyOf [null, count]`, and the `notProved` if-clause gains `"type":"integer"` (0.4:286, 0.5:991).
- Why it matters: the state cannot occur today. lf-env-readable requires a final slot, and lf-env-axioms fails only when the declaration is not accepted (environment.fs:553, 638-640, 1247-1250). The PROJECT_PROGRESS [format] row records that earlier schema files are kept unchanged and that changes get new versions.
- Fix: revert both schema files. Make "accepted, axioms unreadable" an internal fault (code 5) in cj-bits and cli-axioms-of., or publish 0.6 with the owner's approval.

**F3 (should fix; [format]; a difference from Lean's Name.toString).**
- Where: name-text.fs:183-190 applies the token rule in `nt-name`, so the check text and the JSON `name` change for any first component among the 139 tokens.
- Pinned Lean: `Name.toString` gives `inferInstanceAs`; `ppExpr` gives `«inferInstanceAs»`. Lean also prints `fun` and `Prop` bare with toString and in « » with ppExpr.
- Fix: apply the rule only in `nt-part`, the term printer's path, which matches Lean's formatter. Keep `nt-name` as Name.toString, which is what COMMAND_LINE.md "Names" promises for reports.

**F4 (should fix: a protection lost its test).**
- latex-name-banned-unescaped is not equivalent. A string literal with U+E0041 or U+1D173 reaches latex-text.fs:60 unescaped: print-strings.fs:45 escapes only code points below $10000.
- I planted it: "Statement in Lean (ASCII)" then held the raw format characters. Unplanted it is `a\textbackslash{}u\{E0041\}b`.
- Fix: remove `equivalent` and add that export, run under `print --latex`, as the fault's test.

**F5 (should fix: the elan hazard is only partly closed).**
- Where: lean_pin.py:165-174. `version()` runs the candidate to ask its version, and that run is the hazard. I tested it with a fake `elan` that logs each run:
  - a wrapper script that execs the proxy: `proxy()` misses it, and `--version` runs it;
  - a copy of the proxy: the same;
  - a hard link without an `elan` file beside it: the same.
- lean-cache.py:499 checks an explicit path with `proxy()` only, so a wrapper given by path is run for real.
- scripts/export.sh:31 and export-elab.sh:26 run `$LEAN --version` themselves, without lean_pin.
- Fix: run `--version` with `ELAN_HOME` set to the checkout's `.tools/elan`, or refuse anything whose real path is not `…/toolchains/*/bin/lean` with `../lib/lean` beside it. Give lean_pin.py a `check PATH` command line and call it from both shell scripts.

**F6 (should fix: documentation).** FORTH_LIBRARY.md:53 and its "Name tables" section (+992-1017) describe an interface that does not exist and callers that do not use it.
- Interface described: `name-table: ( k "name" -- )`, `names,`, `name-table-end`, terminator rules, "two return-stack cells".
- Callers claimed: commands, options, statement forms, progress line.
- Fix: describe the actual linked-list interface (src/lib/name-table.fs:1-35). The only caller is name-text.fs.

**R1 (REUSE PASS).** name-table.fs adds a fourth table form. leanforth.fs `cli-entry`, print's `pr-form-names` and check-run's `ck-pline-parts` remain separate tables. Convert them in the scheduled reuse pass (the implementer's item 7); cite that plan row.

**R2 (REUSE PASS / wording).** print-forth.fs:182-190 (`lf-pf-put-part`) is still a second speller, for Forth mode, with LeanForth's own syntax. The header claim "the one name speller" (name-text.fs:1) should say "for Lean text".

**N1.** `decl-outcome`'s ok branch is a tautology, so `: decl-outcome ( d -- outcome ) lf-env-outcome ;` is equivalent and reads the slot once. The implementer is right that nothing user-visible changes. The `unfinal` test cannot tell the old reading from the new one (both give invalid); no test can.

**N2.** nt-state is a process-global slab. The term printer was designed context-local (print-job.fs:23, ADR 0009) and now writes into it. No job prints today. The token table sits inside nt-state; a standalone `name-table: nt-tokens` would count as a global. The header's "State" does not mention the table.

**N3.** The cut step log carries no mark in the file: only the error line (stdout) and exit 3 tell a reader. Three further points:
- The cut relies on the sink receiving `\n` as its own write (step-log.fs:70).
- The `flush-file` and `resize-file` results are dropped, yet the message says the file was cut.
- Suggest an end record in a complete log.

**N4.** `help` for `print --lf` does not mention exit 2. COMMAND_LINE.md:1574 does, and 2 (unsupported) fits its exit-code table.

**N5.** Already there before this branch:
- The LaTeX "Statement in mathematics" `\texttt{"…"}` keeps plane-1 and plane-14 format characters raw.
- README.md:7 and USER_GUIDE.md:8,62 still carry the Mathlib claim.

**N6.** Constants with macro scopes print as `x.«_@».Names._hyg.12` in terms; Lean writes `x✝`. This is documented for reports only.

**N7.** Test gaps:
- name-table: no test that a name over 255 bytes is refused, none of BASE restore, none from outside the project.
- `lf-pp-shown-to` takes 4 stack items.

## Forth style and reuse
- forth-metrics, 11 changed files: 1304 words; 65% are 1-2 lines and 0.2% over 10 lines. All long words predate the branch (`cli-check-usage.` 37 lines). name-table.fs: 9 words, all 1-2 lines, 0 globals.
- check-duplicates: none new or grown. check-lib-callers: every lib file has a caller.
- Baselines: coverage, forth-quality and duplicates show only the name-text.fs path renamed. No numbers were raised, no test was deleted or skipped, and no timeout was raised.
- Narrowed faults: cli-prints-accepted-itself (ExitCodes, 15.9 s), cli-fuel-given-up-counted (JsonReport Fuel, 18.9 s) and cli-name-raw (the Forth unit test, 0.3 s) are still caught. Their full-file tests still exist.
- Not run: check-forth-quality.py (it needs git; the archive has none).

## Probes run (Gforth 1.0.0 pinned; Lean 4.35.0 toolchain binary, never the proxy)
- `check [--json] [--resources] --fuel 50/100/200 tests/cli/chain.ndjson` on base and head. Also `--fuel 40` on a Lean export of 80 declarations: later block members keep 0, as documented.
- Lean files with 22 odd names, built with `lean -o` and `leanexport` (toolchain bin on PATH). Lean's `Name.toString` and `ppExpr` compared with head's `check` and `print`. The private golden `_private.tests.reference.«author-21-numeric-name».0.twice` equals Lean's toString.
- `print` and `print --latex` of `oddStmt` and of a string literal with U+E0041 and U+1D173 (`strTag`), on base and head.
- scripts/mutants.py --only 14 faults on the head copy: 13 caught, 1 listed as equivalent. That one, planted by hand, is caught by strTag (F4).
- lean_pin probes with a fake elan reached by symlink, wrapper, copy and hard link. tests/lib/name-table.fs passes. A token lookup takes 0.5-1.3 µs.
- Not run: any suite, make tier, pinned-Lean comparisons, Gforth 0.7.3. This AI review does not replace the owner's human review.

## Re-check: fix-cli-present-2, e3c5297a..8bb214e8 (20 commits, rebased; read as content)
**Verdict: mergeable.** Nothing blocks. F1-F6 are fixed. 3 should fix (S1-S3; S2 is a one-sentence fix to the manual), 4 notes.
- **Owner, plain language.**
  - The garbled names in `print` are gone.
  - The report formats are unchanged from main.
  - `check` names declarations as Lean's name text does; only printed formulas add « », as Lean's own printer does.
  - Gates:
    - [kernel], [import], [parser], [bypass]: none touched.
    - [format]: report schemas unchanged; the step log is unchanged at version 1.
    - Receipts: only the recorded hash of scripts/export.sh changed (see 6).
    - Open question for you: should the step log get an end record (format version 2)? I recommend yes.
- **Every user-visible change of the branch:**
  1. An exhausted check reports its whole budget, in text and JSON.
  2. `print` outlines mark NOT PROVED.
  3. `print --lf` with stubs exits 2 and adds a note; `help` says so.
  4. A failed `--steps FILE` is cut to its last whole line. If even the cut fails, the error says "it may end inside a line". Exit is 3 either way.
  5. `capabilities` makes no Mathlib claim; README and the user guide date their run.
  6. Printed terms, goals and LaTeX spell names as Lean's printer does (`Foo.«a.b»`, `«fun»`), with control and format characters escaped.
  7. A string literal's format characters above U+FFFF print as `\u{X}` in every mode. That is not Lean syntax (a documented difference).
  8. The step log's position line was re-wrapped.
  9. The export scripts and the Lean cache refuse a Lean that is not a toolchain's own binary.
- **1 (F1): fixed.**
  - log-view.fs `lf-lv-put` now writes printer text as it is. Only the input file name goes through `lf-lv-put-text`. statement-forms.fs:96 no longer escapes either.
  - oddStmt now prints `«a\u{202E}b» = «a\u{202E}b»`, plain and LaTeX. My 22 names: plain, LaTeX and math-text terms match pinned Lean's ppExpr, apart from 4 differences:
    - documented: `Foo.a«b»c`, macro-scope names and bidi controls;
    - known: the private name, as check_author pins it.
  - `nt-text` writes into its own slab (`nts-raw`). `nt-own?` refuses any address inside that slab; `slab-offset` is bounded, so nothing else is refused.
  - Note: the refusal surfaces as "full" in JSON (cj-shown) or as an internal fault in text (cli-unshown). No caller passes nt-text its own result today.
- **2 (F2): fixed.** Schemas show a zero-line diff against main.
  - decl-axioms throws -4135 only when `decl-accepted?` holds and `lf-env-axioms` fails. Both run the same test (environment.fs:1247-1250), so no real run reaches exit 5.
  - The JSON check exit codes over every tests/cli fixture equal main's.
- **3 (F3): fixed.**
  - `check` text and JSON names on my 80-declaration export are byte-identical to main (`fun`, `Prop` bare = Lean's Name.toString).
  - Printed terms and LaTeX titles use « » (= ppExpr), while plain titles say `Definition fun`. That is intentional; a note.
- **4 (F4): fixed.** I planted latex-name-banned-unescaped and str-print-wide-banned-raw; both were caught.
  - S1 (should fix): odd-string.ndjson is 590 KB because the real `String` drags in its dependencies. Not needed: a `prelude` file (`axiom String : Type`, `axiom P : String → Prop`, `theorem strUse (h : P "a<U+E0041>b<U+1D173>c") : P … := h`) exports to 1,223 bytes. On head it prints `\u{E0041}` in plain and LaTeX. Use that.
- **5 (F5): fixed for every realistic case.** My fake elan, reached by symlink, wrapper, copy or hard link, and copied into its own home's toolchain folder: all refused, none run.
  - Note: two contrived placements still run the candidate (`--version`, with ELAN_HOME confined to the fake home): an elan copy in a toolchain-shaped folder whose home has no bin/elan, and a wrapper script inside a toolchain folder. Tighten by also requiring an ELF header.
  - S3 (should fix or plan row): not every runner goes through the pin. These take `$LEAN` or `lean` from PATH unchecked: profile-existing.sh:7, tests/front/synth-init.sh:12-13, constructions-init.sh:22, check_meta.py:30, check_binder_kinds.py:137, check-doc-examples.py, program_receipt.py:616.
    - Covered with the cache on: recipes then get lean-cache, which checks LEANFORTH_LEAN.
    - Not covered: under `LEAN_CACHE=0` (the daily run), or when run by hand.
    - Fix: one Makefile guard, `python3 scripts/lean_pin.py check $(LEAN_BINARY)`, plus the pin in those scripts' defaults.
- **6 (receipts): the only change is the hash.**
  - Each of the 7 goldens, the generated clamp receipt and PROGRAM_RECEIPTS.md changes exactly one line: the `sha256` of `scripts/export.sh`.
  - Schemas, program_receipt.py, program_verify.py and receipt_check.py are unchanged.
  - Old receipts still `validate`. `verify` replays the receipt against the current files, so an old receipt is now refused. That is the field's documented meaning (program_receipt.py:44-46: "one whose files changed since, is rejected"): it pins the exact export tool. No format change. The owner should know old receipts must be regenerated.
- **7 (N3): mostly fixed.**
  - Step log schema unchanged. Write, flush, resize, position and close results are checked; any failure gives "it may end inside a line".
  - A line end is now found at the end of any write (`cli-line-end?`).
  - S2 (should fix, manual): the rule "a complete log is one in which each header's step count is followed by that many step lines" (COMMAND_LINE.md, leanforth.fs header) is not sufficient. A cut at a declaration boundary, the most likely place since the file is cut back to a whole line, leaves a log that passes the rule with later declarations missing.
    - Say: "the rule finds a cut inside a declaration; only the exit status shows a complete log".
    - Recommendation: the end record `{"tactic_steps_end":{"declarations":N}}` as format version 2, with a new schema, after the owner's [format] decision.
- **8 (new, style, reuse).**
  - Nothing new blocks. forth-metrics (7 files): no new long words; `cli-other-usage.` grew from 13 to 14 lines (help text).
  - check-duplicates: none new. check-lib-callers: OK. Baselines: path renames only.
  - Still for the reuse pass: R1 (3 tables onto name-table.fs), N6, and `lf-pp-shown-to`'s 4 items.
- **Probes:**
  - oddStmt and 80/22-name `print`/`print --latex`/`check [--json]`, on main and head.
  - The prelude string export, built with pinned Lean 4.35.0 (the toolchain binary).
  - 8 planted faults via scripts/mutants.py `--only` on the head copy, all caught.
  - lean_pin.refusal on 7 fake-elan placements.
  - JSON check exit codes over the tests/cli fixtures.
  - forth-metrics, check-duplicates, check-lib-callers.
  - No suite was run. This does not replace the owner's review.

# Whole-code Forth review: src/author, src/cli, src/program, src/present on s2-finish-2
**Range:** whole files at `s2-finish-2` = `3e5f95b4` (merge-base with main `3b8f8bf9`); not a diff review.
**Findings: 20.** BLOCKS 4 (B1-B4), REUSE PASS 8 (R1-R8), note 8 (N1-N8; N1 is high). Read-only. I worked in a `git archive` scratch copy and ran about 150 `bin/leanforth` probes on Gforth 1.0.0 (a few on gforth-fast), plus `forth-metrics.py`, `check-duplicates.py` and `check-lib-callers.py`. No suite was run and no fault was planted. This AI review does not replace the owner's required human review.

## For the owner (plain language)
- **The parser boundary held.** About 110 hostile `.lf` files (Forth word names such as `dup`, `bye`, `:`, `evaluate`, `include`, `lfa-group:`; every number form; raw bytes, control and bidi characters, NBSP; long lines and tokens; open comments; missing `end`; deep nesting; stack overflow) were all refused with a position. None was accepted wrongly, crashed, hung or exited with 5. Search order, BASE and the recognizer come back after every error.
- **Two ways to destroy an input file (B1, B2).** `--steps` can overwrite the `.lf` text or the library export and exit 0. `--record` or `--save-snapshot` can overwrite the export when `--jobs` or `--memory-per-check` comes first. All three are shown on copies.
- **Two differences from Lean, which are your three questions (B3, B4, N2).** A theorem from the same file used by name stops with error 73. The message, "depends on unfolding", is wrong: only library constants get an argument count. `open Nat` fails because library names never count as namespaces. `2 3 * #check` gives 119 or 120 because instance search tries an instance that the export lacks (slice) or that could not be checked (Init). It should name that instance.
- **One wrong exit class (N1).** A Forth fault inside the run, including one in the elaborator at `end`, is reported as "invalid text" (exit 4). Internal faults should exit 5, resource faults 3.
- **Reuse:** the authoring runner hand-copies `lib/text-run.fs`, which the program verifier already uses. Seven linear searches and three name tables should become library words.
- Read whole: 18 files. In part: 8. Not read: the rest of cli, most of program, all of present (list at the end).

## Findings (ranked)
**B1 (BLOCKS: an input destroyed).** bin/leanforth:132-150 guards against an output path that names the export, and the guard can be bypassed.
- Its loop counts as value-taking only `--fuel --snapshot --env --elab-data`. So `--jobs`, `--memory-per-check`, `--steps`, `--elab-fuel`, `--name`, `--statement` put their value in `files[0]`, and `-ef` compares the wrong file. The Forth side compares names only as text (leanforth.fs:938-939).
- Probes on a copy: `check --jobs 1 --no-manifest --record ./ex.ndjson ex.ndjson` gives exit 3, and ex.ndjson becomes a 766-byte run record. `check --memory-per-check 100 --no-manifest --save-snapshot ./ex.ndjson ex.ndjson` gives exit 0, and the export is overwritten.
- test_leanforth.py:1992 uses `--jobs` with a different record name, so it misses this.
- Fix: one list of value options for the wrapper, generated from `cli-option-table` or checked against it by a test. Add a test `--jobs 2 --record ./X X` → 4, and a fault that drops an option from the list.

**B2 (BLOCKS: an input destroyed, exit 0).** leanforth.fs:1081-1084 `cli-steps-file` runs `create-file` on whatever `--steps` names, after the check. Nothing refuses FILE.lf, `--env`, `--elab-data` or `--snapshot`.
- Probes: `check --env s1-slice.ndjson --elab-data s1-slice.elab.ndjson --steps victim.lf victim.lf` gives exit 0, and victim.lf now holds the step log. `--steps victim-env.ndjson` overwrites the library the same way.
- `--steps /nonexistent/dir/log` correctly exits 3, but no test pins that path (:1087-1090).
- Fix: in the wrapper, `-ef` the `--steps` target against every input before anything runs (exit 4, "STEPS must not be an input"). Add the tests and a fault.

**B3 (BLOCKS: a difference from Lean; fails closed as unsupported).** front/reader.fs:78-80 `lfn-library` gives `-1 true` for every declaration that is not a library one, so a same-file name used plainly stops with 73.
- Probes: `m self_eq` gives exit 2, error 73. `def two Nat := …` and then `two two =` also give 73, although `two` takes no argument. `' self_eq m $` is accepted (exit 0), so the type is known (handover.fs:142 `lf-menv-add`). Lean elaborates `self_eq m`.
- tests/front/front.fs:140 pins the wrong behaviour only with a stub finder.
- Fix: count arity from the declaration's type in the Meta env, with check-lf.fs:127-141's `lfc-telescope`/`lfc-unfolds?` rule, in one word for both kinds of declaration: `lf-menv-arity ( decl -- arity unfolds? )` (the front review's F1). Until then, give a separate unsupported code: "a declaration of this text used by name".

**B4 (BLOCKS: a difference from Lean; fails closed).** namespaces.fs:7-10 and 157-168: `open N` knows only the namespaces entered and the prefixes of the text's own names (`lfa-prefixes-known`, called only at declarations.fs:199).
- `open Nat` with the s1 or s2 slice gives exit 4, error 26. Lean's isNamespace counts every prefix of an environment name.
- Fix: `defer lfa-library-space? ( c-addr u -- flag )`, which check-lf sets to `lfa-intern lfc-name 0< 0=`, used by `lfa-scoped` and `lfa-opened-in`. Short names then still stop with 55 until the export records protected; say so in COMMAND_LINE.md:267.

**N1 (note, high: wrong exit class).** runner.fs:202-208 maps every THROW that is not an authoring error to error 41, which errors.fs:296 makes *invalid* (exit 4).
- The elaborator, synth and tactics run inside that CATCH at `end`, so an internal fault (-9, -4) is blamed on the user's text.
- Probe S_overflow (80,000 numbers in kernel form): exit 4, "error 41 … THROW code -3", where the contract says 3.
- Fix: map -3/-5/-8 to a full code, and any other code to a new "internal" outcome that tally.fs maps to exit 5.

**N2 (note; your third question).** `2 3 * #check` reaches synth.fs:452-455 `sy-candidate`. The candidates come in Lean's order, newest first, and the search tries one before the instance that would succeed: on a slice one the export left out (→ 119), on Init one whose recorded keys were not verified (→ 120). Lean prints `2 * 3 : Nat`. Refusing is fail-closed and right, but the message hides the cause. Fix: name the instance with `lfa-detail+` (for example "tried `instMulNat`, not in the export"), and pin both codes with that name. `2 3 + #check` works on both slices (exit 0).

**R1 (REUSE PASS).** author/runner.fs re-implements lib/text-run.fs, which verify-runner.fs uses: runner.fs:92-99 and :214-215 copy `run-settings-save`/`-restore`/`-depth`, :109-116 copy `text-line-end`/`text-cr-drop`, and `lfa-eol` is lib/bytes.fs's `lf-index`. Replace with `/run-settings +field lfa-run-settings` and `lfa-run lfa-run-settings run-settings-save 0= if lfa-order-full exit then`. runner.fs:243 also opens without `bin`, unlike verify-runner.fs:150.

**R2 (REUSE PASS). "Offset of first char" written 6 times:** source.fs:108 `lfa-dot`, :98 `lfa-word-end`, runner.fs:109, core/statement-match.fs:89 and :293, leanforth.fs:750. Add to lib/bytes.fs: `: byte-offset ( c-addr u char -- n ) >r tuck r> byte-scan nip - ;` (`lfa-word-end` needs a blank-predicate variant).

**R3 (REUSE PASS, and performance).** Linear `?do … unloop exit` searches at build.fs:48, :118, :158; constants.fs:42; groups.fs:121; namespaces.fs:78; runner.fs:256; print.fs:92-98. Use F4's `store-index ( x xt store -- i true | false )`. Performance: `lfa-find` scans the whole term store for every node made (O(n²) in the text's size); `pr-newest` runs once per step-log entry.

**R4 (REUSE PASS; old C1, still open).** Three counted-name tables: leanforth.fs:1520-1532 `cli-entry-find`, print.fs:127-141 `pr-form-bit`, check-run.fs:768-772 `ck-pline-parts`. Move them to `lib/name-table.fs` with `name-table-find ( c-addr u table -- entry | 0 )`, and split leanforth.fs (1,745 lines, up from 1,413).

**R5 (REUSE PASS: a fixed store where a growable one exists).** values.fs:24/45 and form.fs:35 hold 512 values per declaration and count every value made, not the ones live. A 256-arrow statement gives exit 3, error 64 at line 260: about 512 words per declaration, too few for printed Mathlib proofs. scopes.fs:30-34 already grows its binder store on the heap (`store-heap-init`, `store-limit!`); do the same here.

**R6 (REUSE PASS; old E2, still open).** build.fs:97-101 has twin bodies, and `lfa-copy` (:104-113) has a CASE with no default, so an unknown tag comes back unshared. Add a default arm: `lfa-e-malformed lfa-fail`.
**R7 (REUSE PASS).** words.fs:34-38 `lfa-kind-of`, a string IF chain → an R4 table.
**R8 (REUSE PASS; cause of B1).** The options are listed twice, in bin/leanforth and in leanforth.fs:1648-1674. Keep one list.

**N3 (note).** Repeated options win silently: `check --env x --env s1-slice.ndjson F` gives exit 0 and never opens `x`; `--steps a --steps b` behaves the same. Fix: refuse a single-value option given twice (exit 4).
**N4 (note).** A token longer than 240 characters gives exit 3 (error 62, at look-ahead, groups.fs:214) with `--env` and exit 4 (error 1) without. Fix: the look-ahead skips tokens too long for a group.
**N5 (note).** Only file lines are limited: 1,024 or more characters give exit 3, error 39 (runner.fs:120-125), while `lf-author-text` takes any length. This is documented; Lean has no limit.
**N6 (note).** build.fs:4 says sharing happens "while the term store holds 64 nodes"; `lfa-find` has no such bound.
**N7 (note; old portability item, still open).** `stdout`/`stderr` are used directly at check-run.fs:731, :777 and print-lf.fs:90.
**N8 (note).** errors.fs:551 `lfa-.n` is an alias left "until the front batch". Remove it.

## The 2026-11-12 review: status
- **Fixed:** C3, C5, D1, D2, D4, E3 (`check_catalogue`), F (the nested IF in ir-run.fs), L2/L3 (log-view).
- **Open:** C1 (R4); C2 (leanforth.fs:1364 still prints plan numbers); C4 (print.fs:81-83 `2 pick`/`2rot`); D3 (ck-state, 19 globals); E1 (`lfa-shift` still recursive, now bounded by R5's 512); E2 (R6); the portability item (N7); the library candidates (cli-entry, latex-text, progress).
- **Not re-verified:** B1, B2, B4-B7, T1-T6.

**Tests seen from the code.**
- No planted fault in author/scopes.fs, constants.fs or library.fs.
- No test or fault for B1, B2, the exit-3 `--steps` path, N1's exit class, or B3 with the real finder.
- tests/front/front.fs:123-140 pins 73 as correct.

## Forth style
**Metrics** (`--words 10`):
- author: 597 words; 70% of 1-2 lines; 3 of 6-10 lines.
- cli: 999 words; 64% of 1-2 lines; 16 of 6-10 lines and 4 longer.
- program: 844 words; 87% of 1-2 lines.
- present: 1,224 words; 66% of 1-2 lines; 24 of 6-10 lines.
- One local (present/statement-forms.fs).

**Long words.**
- `cli-check-usage.` (37 lines of help text): justified, but move it to cli/help.fs.
- `check-command` (leanforth.fs:1165, 11 lines) and `cli-snap-misuse` (:986, 12 lines) are outcome chains. Factoring:
```forth
: first-refusal ( table -- code true | false )
  begin dup @ while dup 2@ swap execute if nip execute true exit then drop 2 cells + repeat drop false ;
create check-refusals ' cli-misused? , ' cli-misuse-record , ' cli-jobs-misused? , ' cli-misuse-jobs , 0 ,
```
- **Shuffles:** print.fs:81-83 `pr-ends?` uses `2 pick … 2rot`. Use `ends-with? ( c u pa pu -- c u' flag )` built on R2, with tests first (part longer than the text, empty part).

## Probes run (exit codes)
- **Tokens:** Forth words → 4 (error 1); `]` → 2 (72); every number form (`$10 #10 %1 -1 +1 1. 1e 'a' &10 0x10 ${HOME} ->x 1,2`, 10 or 30 digits) → 4 (35); `0010` → 4 (20).
- **Structure:**
  - `( ) \ note"` → 0, or 4 (42, 37) when unclosed;
  - missing or wrong end → 4 (33, 22); nested declaration → 4 (14);
  - `theorem dup` and `theorem lfa-group:` → 0 (both are valid Lean names);
  - lines of 1,023 / 1,024 characters → 0 / 3;
  - 0xFF, overlong encoding, NUL, ^A, U+202E → 4 (46); NBSP → 4 (1); CR → 0;
  - deep arrows, binders, stack → 3 (64); S_overflow → 4 (41/-3), the same on gforth-fast.
- **With `--env`:** the same codes, except N4.
- **CLI:**
  - `--jobs 0/-1/2x/''/1e20` → 4; `--jobs 1000000` → 0;
  - `--fuel 0` → 3; fuel above the limit → 4; `--elab-fuel 0` → 3;
  - `--progress=` and a huge value → 4;
  - `--strict-axioms` on a text with an axiom → 6 (also with `--jobs 2`), without it → 0;
  - missing snapshot → 4.

## Reuse searched
- LIBRARY_WORDS by name.
- grep across src/ for `byte-scan`, `lf-index`, users of `text-run.fs`, `?do … lfa-dot-at?`, `chars + c@ … unloop`, counted tables, `run-settings`.
- `check-duplicates.py`: "284 baseline groups, none new or grown". In these folders it lists `lfa-rest`/`pv-rest`, `lfa-rest!`/`pv-rest!`/`pv-text!`, and log-view/ir-run twins.
- `check-lib-callers.py`: OK (`bigint.fs` allowed under FE1i-4).

## Files
- **Whole (18):** author runner, words, groups, source, values, scopes, form, build, constants, library, declarations, namespaces, errors; front/reader.fs (the natural reader); cli check-lf, tally, print; program/verify-runner.
- **In part (8):** author/export 1-120; cli/leanforth.fs 938-939, 1040-1189, 1364-1372, 1480-1745; check-run.fs 500-515, 768-776; program/verify.fs; front/synth.fs 440-460; instances.fs 40-60; lib/text-run.fs header; lib/bytes.fs 74-88.
- **Not read (stopped at about two thirds of context):** cli check-json, check-run (rest), name-text, print-lf (greps only); program ir-reader, ir-run, verify-semantics, verify-report, verify-alias, examples, clamp, program-depth, sha-words; all 17 files of present.
- **Uncertainties:** Gforth 0.7.3 was not run, so its number forms are reasoned only from the code (the check happens after conversion). Which instance N2 tries was not traced.

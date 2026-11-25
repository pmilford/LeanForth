FORTH REVIEW: tb2-patterns-e2a
Range reviewed: 84547d08..7e9a394b (4 commits, head 7e9a394b), worktree /home/peter/code/LeanForth/.claude/worktrees/agent-ac4af894086366c33.
Findings: 3 blocking (all about reuse), 5 not blocking (2 test gaps where my planted faults survived, 1 library hazard, 1 style, 1 ledger note). I found no text that LeanForth accepts and Lean rejects.
Verdict: merge after fixes (findings 1-3; finding 3 can instead cite a plan row).

## Findings

1. BLOCKING (reuse). The branch writes the check that an HEq has one type twice. `src/front/app-builder.fs` `abl-homogeneous`/`abl-heq-arg` re-reads the HEq's arguments with `4 lf-meta-nth-arg`, although `abl-args4` (used by `lf-match-heq?`) already does that. `src/front/meta-tactic/subst.fs:242` `mse-homogeneous?` is the same defeq test again. Fix: one word in app-builder.fs, used by both.
   ```forth
   : abl-heq-args? ( t -- α a β b true | false ) dup abl-heq-app? if abl-args4 true else drop false then ;
   : lf-heq-homogeneous? ( α a β b -- α a b flag ) >r >r over r> lf-defeq! r> swap ;
   : lf-mk-eq-of-heq ( h -- h' ) dup abl-infer-d abl-heq-args? 0= if abl-fail then
     lf-heq-homogeneous? 0= if abl-fail then s" eq_of_heq" abl-eq-app swap lf-mk-app ;
   ```
   Then `mse-heq-run` becomes `... lf-heq-homogeneous? if rot drop mse-to-eq else 2drop drop mse-kept then`, `mse-homogeneous?` goes, and `lf-match-heq?` reuses `abl-heq-args?`.
2. BLOCKING (reuse). The branch adds `lf-run2` (meta-must.fs:157) and replaces fvar-subst.fs's copy. It misses the copy at `src/front/rcases.fs:320` (`0 swap lf-run+ rcs-root rcs-name lf-run+`), in a file it touches. AGENTS.md requires every existing copy to be replaced in the same branch. Fix: `: rcs-target ( goal e -- goal' v ) dup lf-meta-fvar? if exit then rcs-root rcs-name lf-run2 lf-goal-generalize swap 0 run@ ;`. Optional: `: lf-run1 ( x -- run ) run-one lf-must ;` for rcases.fs:304, rcases.fs:320's first half and meta-induction.fs:228 (`0 swap lf-run+`).
3. BLOCKING unless a plan row is cited. `lf-tac-nothing.` (tactic-msg.fs:81) is the seventh word with the body `drop outcome-ok`. The other six:
   - lib-decode.fs:441 `lbd-anonymous`
   - core/scratch-marks.fs:163 `lf-scratch-kept`
   - import/snapshot-layer.fs:150 `ly-number`
   - import/run-record.fs:258 `rr-any`
   - import/checker-input.fs:128 `cin-pass-by`
   - kernel/mixed-rebuild.fs:26 `lf-rebuild-keep`

   One library word is the right fix, because each leaves the items below untouched. Put `: drop-ok ( x -- outcome ) drop outcome-ok ;` in `src/lib/outcome.fs` beside `ok-and`. In this branch, use it in place of `lf-tac-nothing.` (subst.fs:119, rewrite.fs, tactic-msg.fs). The six copies in lib, core, import and kernel move this branch to the full tier, so either do them here or record a plan row in a named slice. The note in `tests/small-copies-allowed.txt` ("a follow-up for the Forth review") is not a plan row.
4. Not blocking, test gap (planted fault F3 survived). Replacing substVar's check that the other side is free of x (`msv-free?`, subst.fs:281) with `drop true` passes batch-h test.fs and check.py. No test has an older equation that mentions x on both sides. Add to subst.lf and batch-h.lean: `theorem p08c (x y : Nat) (h1 : x = x) (h2 : y = x) : y = y := by subst x; exact h1`. Lean and LeanForth both accept it; with F3 it becomes error 476. Add a faults.d entry for it.
5. Not blocking, test gap (F2 survived). Making `lf-goal-intro1-as` (assert.fs:204) pass the plain name instead of `mat-own` (so a hidden hypothesis comes back named) passes all of batch-h. Inside subst the new hypothesis is cleared at once, so only error messages and future callers see it: heqToEq is a public word that E3-E5 will call. Add a unit test that asserts a hidden local through `lf-goal-intro1-as` and checks `lf-local-inaccessible` on the result, and an entry in faults.d. I did not run other suites (e.g. change at), which may catch it through `mat-change-run`.
6. Not blocking, library hazard. `lf-goal-revert-kept` (revert.fs:19-31, `mrv-seed`) does not make Lean's revertFailure check (an asked local that depends on one asked after it). The implementer says no caller can trigger it, and that is true today. subst asks `[a, h]` and a occurs in h's type, so a comes before h and cannot depend on it; induction asks one variable. But this is now a library word for E4's indices, and a wrong order would build a goal whose binder refers to a later binder. Fix now: in `mrv-seed`, for each i and each j < i, throw when asked j depends on asked i. Otherwise name it in E4's slice.
7. Not blocking, style. See the style section below.
8. Not blocking, ledger. "Subst of a have: 93" makes these texts unsupported where Lean accepts them:
   - `' k by-subst` on a have-bound equation (x_have);
   - any `by-subst`, `rfl` pattern or `by-subst-vars` whose revert would take a let or a have along;
   - `by-subst-vars`, which stops with 93 instead of trying the next local (test.fs:164);
   - `by-subst` of a let, which is 99 where Lean zeta-reduces it.

   All of this is in the ledger: docs/development/TACTIC_STATUS.md:86 ("a have, or a let or have among the reverted ... 93, Lean accepts", plan LC).

Not from this branch: `by-intro: h` and `by-rintro[ h ]` on `¬ a = b`, with `k : ¬ a = a` in context, give 93 where Lean accepts (p26, p26b, p26c). The same happens with plain intro, so it is intro's whnf path. `by-rintro[ n ]` on `¬¬(a = b)` introduced fine (p25).

## Probes (identical texts; Lean 4.35.0 pinned binary; LeanForth `bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data ...`)
| probe | text (Lean form) | Lean | LeanForth |
|---|---|---|---|
| p01 | h : a = b; subst h; exact Eq.refl a (b goes) | accept | accept |
| p02 | subst a (h : a = b); exact Eq.refl a | Unknown identifier a | 76 |
| p03 | h : succ a = b, k : b = b; subst h; exact k | accept | accept |
| p04 | h : succ a = succ a; subst h | not of the form (x = t) or (t = x) | 478, same text |
| p05 | h : a = succ a; subst h | 'a' occurs at | 476, same text and goal (`Nat.succ a` vs `a.succ`, printer) |
| q14 | h : a = a; subst h | occurs | 476 |
| p06 | revert h hb; intro h _; subst h; exact hb (hidden) | Unknown identifier hb | 76 |
| p07 | (h : a = b) (h : b = a); subst h; exact h (shadowing) | accept | accept |
| p08 / p08b | subst x with h1 : x = y, h2 : z = x / h1 : y = x, h2 : x = z | accept | accept |
| p08c | subst x with h1 : x = x, h2 : y = x | accept | accept |
| p09 | subst b, statement mentions b in k and goal | accept | accept |
| p10 | h : HEq a b; subst h | accept | accept |
| p11 / p11b | reduced: id n = succ m / n = id m with dependent k | accept | accept |
| p12 | subst h1 h2, h2 mentions the eliminated b | accept | accept |
| q05 | subst h1 h2, both a = b | occurs | 476 |
| q20 | subst h a (a gone) | did not find equation for 'a' | 479, same text |
| q04 | subst h; exact h | Unknown identifier h | 76 |
| p13 / p13b | subst_vars: variable before its equation; none usable | accept | accept |
| p14 | obtain ⟨rfl, -⟩, neither side a variable | 478 text | 478 |
| p17 | obtain ⟨rfl, -⟩ := (a = b ∧ True); exact Eq.refl b | Unknown identifier b | 76 |
| q01 / q02 | obtain ⟨rfl, rfl⟩ chain; rintro rfl rfl | accept | accept |
| q11 | rintro ⟨x, rfl⟩ on ∃ x, a = x | accept | accept |
| p18 / p19 | rintro x y; rintro ⟨x, y⟩ z | accept | accept |
| p21 / p22 | rintro -; rintro _, then exact h | Unknown identifier h | 76 / 76 |
| p23 | rintro x y, one binder | introN: no additional binders | 94, same text |
| q17 | rintro with no items | parse error | 481 |
| p26 | rintro rfl on ¬ a = b | accept | 93 (from intro, not this branch) |

I could not write `∃ x, x = a` (natural form has no lambda); the variable-on-the-left case is covered through `∧` (rf_left, p14, p17). The three worked theorems of LANGUAGE_REFERENCE D.9 (sb_right, rf_exists, ri_alts), extracted from the doc as written, are all accepted.

## Code (part B)
- I traced `lf-goal-subst-core` and every word under it by hand, and found the stacks right on every branch:
  - which side goes: a is the left side, or the right with symm;
  - the occurs check before the revert;
  - revert `[a, h]` with preserveOrder, then intro of the two;
  - skip only when nothing else was reverted and the goal mentions neither;
  - the Eq.rec / Eq.ndrec choice on whether the goal depends on h;
  - the motive, with `_h : b = a` and `_h.symm` when there is no symm;
  - the minor premise with refl, the major h or h.symm;
  - clearing h then a, re-intro of the rest;
  - the fs inserts in Lean's order.
- `mse-by-rhs`/`mse-by-lhs` match substEq/substReduced, including the throwing clear. `msb-run`/`msb-heq` match Lean's subst. `msv-tried` keeps the goal on the return stack across the CATCH and throws on any error that is not Lean's.
- The motive's level is right for the dependent motive. `abr-lam2` opens x and then `y : b = x'`, and infers the body, as Lean's inferType of a lambda does. The locals are dropped on every path, a THROW included, by `lf-with-local-decl`'s CATCH and `lf-lctx-drop`; the frames are cut by `lf-with-record`.
- No slab address is held across a claim. `mat-intro1` keeps an address from `lf-with-cells` across `lf-goal-intro-n`, but that word claims only goal.fs's slabs, never `mat-cells`.
- Every outcome is passed on (checked with grep). There is no `lf-menv-find` without `?`.
- New state: `msc-frames`, `mse-frames` and `abr-frames` are context slabs (ADR 0009). The constants `tac-k-subst`, `tac-k-subst-list`, `tac-k-subst-vars`, `tac-k-rintro`, `tac-shape-rintro` and `pat-seq` are all written while loading. There is no new VARIABLE or VALUE.
- The library has no rcases- or tactic-specific logic. The let refusal (99) sits in tactics/subst.fs.
- rcases.fs:245 marked unreachable: I agree. A pending target is a field declared after every equation whose pattern ran before it, and rintro's items are introduced fresh, so an rfl never turns a pending target into a term. Only a direct call of the private `rcs-fvar` could reach it.

## Reuse (searched)
- Searches: grep across all of src/ for each new word's name and body (`drop outcome-ok`, `0 rot lf-run+ swap lf-run+`, `run-one lf-must`, `0 swap lf-run+`, `s"  " lf-pp-emit lf-tac-quoted.`, the HEq argument and defeq phrases), the lib/runs.fs word list, and app-builder.fs's makers (`abl-eq-app`, `abl-fold`, `abl-args4`).
- `scripts/check-duplicates.py`: "186 baseline groups, none new or grown" (it looks only at bodies of 6 tokens or more, so it misses findings 1-3).
- `scripts/check-lib-callers.py`: clean.
- `lf-tac-ex-quoted` and `lf-tac-quoted-after.` correctly replace goal.fs's `mcl-refuse` and `mcl-fvar.`. `mrv-by` is private to revert.fs and not a copy. The three app-builder makers reuse `abl-eq-app` and `abl-fold`, apart from finding 1.

## Forth style
Metrics (`forth-metrics.py --words 10`, 10 files): 535 words, 83% of 1-2 lines, 16% of 3-5, none over 5 lines, no locals, no long lines. Deep shuffles 50, return-stack ops 144. subst.fs: 85 words, 8 deep shuffles, 24 return-stack ops. The baseline only adds the two new tactic files.

Style findings (not blocking):
- (a) Repeated phrases in subst.fs: `msc msc-hx @` 8 times, `msc msc-x @` 5, `msc msc-b @` 3, and the flag test twice. Name them:
  ```forth
  : msc-hx@ ( -- h ) msc msc-hx @ ;   : msc-x@ ( -- x ) msc msc-x @ ;   : msc-b@ ( -- b ) msc msc-b @ ;
  : msc-flag? ( mask -- flag ) msc msc-flags @ and 0<> ;
  ```
  Then `msc-symm?` is `lf-subst-symm msc-flag?`.
- (b) The bare `2` for "a and h" in `msc-again`, `msc-skip?`, `msc-old` and `msc-rest`. Name it: `2 constant msc-ah#`.
- (c) `rcs-introduced` (rcases.fs) reads the triple through bare slots (`2 run@`, `3 run-after`, `0 run-pair@`), as line 285 already does. Name them:
  ```forth
  : rcs-target@ ( pending -- e ) 2 run@ ;
  : rcs-after1 ( pending -- rest ) 3 run-after lf-must ;
  ```
- (d) `msc-framed` and `msb-framed` rely on fields being next to each other for `cell-pair!` (goal/h, fs/flags, a/b, x/y). Say so in the structure's comment, as /abr does.
- There is no PICK, ROLL or raw `cells +`, and the stack comments I checked are right.

## Planted faults (temporary copies under the scratch folder; batch-h test.fs about 2 minutes each, then check.py)
| fault | caught? |
|---|---|
| F1: wrong side eliminated (`msc-symm? 0= if swap`) | yes, by test.fs (substCore run count) |
| F2: hidden flag lost in `lf-goal-intro1-as` | no: test.fs and check.py both pass (finding 5) |
| F3: substVar's free-side check removed | no: both pass (finding 4) |
| F4: rintro's items cut to the first (`rcs-len 1 min`) | yes, by test.fs |
| F5: substVar left side checked before right | equivalent mutant: within one equation only one side can be x alone with the other free of x |

## Not looked at, or not run
- The tier and cover-changed (already passed on this head), gforth-fast, Gforth 0.7.3 and suites other than batch-h.
- Rollback of `by-subst[ h1 bad ]` inside a try.
- Error texts other than 476, 478, 479 and introN's.
- The step-log goldens.
- Documentation beyond D.9 and the TACTIC_STATUS rows.

Probe files are in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/review-e2a/ (Lean twins in probes.lean and q.lean there). This AI review does not replace the owner's required human review.

## Resolution

Fixed on branch `tb2-patterns-e2a` (2026-11-24), one commit an item:

1. `0617f481`: app-builder.fs's `abl-heq-args?` (Expr.heq?, `abl-heq-at` with no term left on a failure) and
   `lf-heq-homogeneous?` (the review's code), used by `lf-mk-eq-of-heq` and subst.fs's heqToEq; `lf-match-heq?`
   and `abl-heq-args?` share `abl-heq-at`; `abl-heq-arg`, `abl-homogeneous` and `mse-homogeneous?` removed; fault
   `heq-not-converted` moved to `lf-heq-homogeneous?`.
2. `84629dc9`: meta-must.fs's `lf-run1 ( x -- run )`, used by `lf-run2`, rcases.fs's `rcs-intro1` and `rcs-target`
   and meta-induction.fs's revert of the major (every `0 swap lf-run+` and `run-one lf-must` of src/); the batch-g
   and batch-h tests' own `run1` and `run2` replaced; fault `rintro-name-dropped` moved.
3. `49b9af30`: `drop-ok ( x -- outcome )` in `src/lib/outcome.fs` beside `ok-and` and `ok-with`, tested in
   tests/lib/lib.fs, fault `drop-ok-keeps-value`, listed in FORTH_LIBRARY.md and LIBRARY_WORDS.md. `lf-tac-nothing.`
   (tactic-msg.fs) and `lf-scratch-kept` (core/scratch-marks.fs) removed, their uses calling `drop-ok`;
   `lbd-anonymous`, `ly-number`, `rr-any`, `cin-pass-by` and `lf-rebuild-keep` keep their names (table entries or a
   role) with `drop-ok` as their body. Behaviour-preserving in the lib, core, import and kernel files: nothing else
   there changes. The small-copy allowance of `lf-tac-nothing.` removed.
4. `01273200`: theorem `sb_var_free` (the review's p08c) in subst.lf, batch-h.lean and both goldens; fault
   `subst-var-side-not-free` (the review's F3), caught by check.py (error 476).
5. `8ebb2404`: a unit test in batch-h's test.fs that intro1 as a hidden local (`lf-goal-intro1-as`) gives a hidden
   binder and as a named one its name; fault `intro-as-hidden-named` (the review's F2), caught by test.fs.
6. `dbb3e169` (reworked in `607d21f9`): revert.fs's `mrv-ordered` makes collectForwardDeps' revertFailure check in
   `mrv-seed` (a local asked that one asked before it depends on is refused), thrown invalid before anything is
   assigned; batch-g's test.fs asks h before b and finds it refused and the goal open; fault
   `revert-kept-order-unchecked`. Lean's own text ("failed to create binder due to failure when reverting variable
   dependencies", Meta/Basic.lean:1132) needs a new error code and no caller of E2a can reach it, so it is task
   **E4-revert-order** of slice E4 in docs/design/TACTIC_PATTERNS.md.
7. `607d21f9`: style points (a)-(d): `msc-hx@`, `msc-x@`, `msc-b@`, `msc-flag?` (`msc-symm?` over it) and
   `msc-ah#` in subst.fs; `rcs-node@`, `rcs-target@` and `rcs-after1` in rcases.fs (with `rcs-generalized`, to keep
   `rcs-target` under 90 characters); the paired fields of `/msc` and `/mse` named in their comments. Faults
   `dependent-not-reintroduced`, `subst-major-not-symm`, `try-skip-ignored`, `fsubst-not-applied` and
   `revert-kept-order-unchecked` moved and checked caught. app-builder.fs's return-stack baseline 38 to 42 for
   `lf-heq-homogeneous?` (its α lies four deep; every other form trades the four for deep shuffles, already at the
   file's baseline); `rcs-target@` excused as a small copy (a field reader, as `fsb-key`).
8. No change: the ledger already records it (TACTIC_STATUS.md, plan row LC).

The side note on intro (`by-intro: h` and `by-rintro[ h ]` on `¬a = b` with `k : ¬a = a` in context, 93 where
Lean accepts; older than the branch): a row of the intro entry in TACTIC_STATUS.md and a line of plan row 9.4.8t,
in the documentation commit that adds this report.

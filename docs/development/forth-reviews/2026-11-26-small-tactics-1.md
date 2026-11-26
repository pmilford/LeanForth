FORTH REVIEW: small-tactics-1
Range: 15b917a6..12334f6c (3 commits; head 12334f6cda24). Findings: 6 blocking, 2 medium, 5 low, plus 5 low style findings.
Verdict: **blocking.** Two blocking findings are cases where LeanForth's result differs from Lean's (1, 2). Four are reuse findings (3 to 6); each must be fixed or given a plan row before the merge.

Tools: Gforth 1.0.0 (`.tools/gforth/bin/gforth`) and the pinned Lean 4.35.0 binary called directly (commit eb6cafb7). No elan proxy, no make target, nothing above 4 jobs, no agents. The repository was not modified.

## Findings

**1. Blocking: a local instance is ignored, so terms differ from Lean's.**
- **What happens.** `by-infer-instance` with a class-typed hypothesis in the context builds the global instance where Lean uses the local one.
  - p17 (`[d : Decidable (a = b)]`, then `have e : Decidable (a = b) := by infer_instance`): LeanForth gives `inferInstance … (instDecidableEqNat a b)`, Lean gives `inferInstance … #1`.
  - p16 (an explicit hypothesis named `inferInstance`) and q4 (`(d : Decidable True)`) differ the same way. All three are accepted with terms that differ from Lean's node for node.
- **Root cause, which predates the branch.**
  - `src/front/elab-decl.fs:117` `edc-local` makes the header's locals with no class: `lf-local-instance` has no caller outside lctx-views.fs.
  - So the guard `src/front/instances.fs:418` `it-local-free` ("unsupported when the context has a local instance of the class") never fires.
- **It also lets main accept a text Lean refuses.** q3, `theorem q3 (d : Decidable True) : decide True = true := by rfl`, is accepted on main and on the branch, because its statement is elaborated with `instDecidableTrue`. Pinned Lean refuses it ("Tactic `rfl` failed"). That is outside this diff, but it is the same fix and needs its own plan row.
- **Fix.**
  - In `edc-local`, mark a parameter whose type is a class (instances.fs's `lf-class?`, Lean's isClass? under withLocalDecl) with `lf-local-instance`. The existing guard then answers unsupported until plan FE3.
  - Do the same where `by-intro` or `have` add a class-typed local.
  - Add `u-ii-local.lf` (the p17 shape, exit 2) and a q3-shaped exit-2 test.
  - Until then, `by-infer-instance` could answer 99 when any local's type is a class.

**2. Blocking: `iterate n` is accepted where Lean refuses.**
- **What happens.** The macro recurses, and pinned Lean fails `iterate 252 skip` at top level with "maximum recursion depth has been reached" (251 passes). LeanForth accepts `253 by-iterate by-skip by-end` and `600 …` (p20). It stops only at its step fuel (exit 3, error 91; 999999999 ends in about 1 s).
- **Where.** `src/front/tactics/iterate.fs:23-25` (`tit-num`, `tit-count`) has no bound. trivial.fs (`ttr-most`) and simp (`sm-depth-max`) already refuse past such a limit with unsupported.
- **Fix.** Add `tit-most` (for example 128, commented with the measured 252), so a count above it answers 99. Because nesting adds depth, bound the sum of the open iterate counts kept in the frames. Test at `tit-most` and `tit-most + 1`. The 1b test of a huge count (91) then becomes 99.

**3. Blocking (reuse): `trn-search` is a tactic-level withoutModifyingState written inside rename.fs** (`src/front/tactics/rename.fs:40-41`).
- It is general runner machinery, so it belongs in tactic-run.fs beside `lf-tac-try`.
- A refused put-back also goes through `lf-tac-must` (93 or 60) here. tactic-run.fs treats that as LeanForth's own fault (`lfr-sure`, internal error 41).
- Proposed:
```forth
\ withoutModifyingState: xt run and the whole tactic state put back
\ however it ends (a THROW thrown on after); a refused save or put-back
\ is LeanForth's fault (lfr-sure, as lf-tac-try's).
: lf-tac-without-modifying ( i*x xt -- j*x )
  lf-tac-save lfr-must >r catch r> lf-tac-restore lfr-sure throw ;
\ rename.fs:
: trn-search ( node -- fvar ) ['] trn-quiet lf-tac-without-modifying ;
```

**4. Blocking (reuse): `mgh-keep` and `mgh-filter` hand-write lib/runs.fs's `run-filter`** (Lean's filterM; `src/front/meta-tactic/generalize.fs:161-162`).
- In the scratch copy I replaced them with `: mgh-filter ( hyps -- ) ['] mgh-holds? run-filter lf-must mgh mgh-kept ! ;` and dropped `mgh-keep`.
- With that change, batch-small-1 test.fs passes (heap sweeps included), and the p53 and p05 terms still equal Lean's.

**5. Blocking (reuse): a copied name check.**
- `trn-name` (`rename.fs:44`) is have.fs:79's `thv-name` body with k fixed. `tgz-name?` (`generalize.fs:38`) is the same phrase with a drop.
- Fix: one shared word in tactic-core.fs, then `thv-name` → `lf-tac-name`, `trn-name` → `1 lf-tac-name`, `tgz-name?` → `lf-tac-name drop`.
```forth
\ Argument k of step i, a name; _ (0) not supported yet (99).
: lf-tac-name ( i k -- name ) lf-tac-arg dup 0= if lf-tac-unported then ;
```

**6. Blocking (reuse, small): `tfx-apply` and `tfx-tac` (`funext.fs:33-34`) re-make trivial.fs:53's `ttr-apply-tac`** (`['] lf-goal-apply-const lf-tac-with-synth`).
- Fix: make it one shared word, `lf-tac-apply-const ( goal c-addr u -- goals )` ("apply c written in a macro: evalApply's withSynthesize"), for example in tactics/apply.fs.
- Then `: tfx-tac ( goal -- goals ) s" funext" lf-tac-apply-const ;` and `ttr-and-tac`/`ttr-true-tac` call it.

**7. Medium: planted faults that survive the branch's tests.**
- F3 (at[ ] hypotheses reverted in reverse order) and F9 (only the first at[ ] name used) are caught only by my p53 term comparison and p04 (exit 4 where Lean accepts). Add p04, p05 and p53 with their Lean twins to generalize.lf and batch-small-1.lean, and these faults to batch-small-1.toml.
- F8 (rename without withNewMCtxDepth) cannot be reached from text (my p55 stops at `by-intro:` through `Ne`, 93). It needs a Forth-level test: a local of type `a = ?w`, ?w at the outer depth; `a a = by-rename: j` must answer 482, as Lean's e55 does.
- F17 (rename without withoutRecover) cannot be reached either: T's elaboration errors are coercions (131, p54). Record it as a known gap.

**8. Medium: test classes claimed but missing.**
- test.fs's header (lines 11, 21-22) claims a malformed-input test of an unclosed `by-funext[` and a state test of "a refused goal left unassigned". Neither exists: `open?` is only checked after successes (lines 87, 97, 110).
- The behaviour is correct (p57 and p58 give 458 and fail closed). Add:
  - `T{ hs s" by-funext[ x by-rfl" tactic-ran s" by-funext[" token? -> 458 true }T`
  - an `open?` check after the 380 at line 99.

**9. Low: stale comment.** `revert.fs:28` and `:103-104` say no caller asks for an argument that depends on a later one. `by-generalize: x at[ hv v ]` now does (p06): it is thrown invalid and the runner maps it to 93, exit 2. Lean refuses with "failed to create binder due to failure when reverting variable dependencies". Nothing is accepted, but update the comments, add a `u-` test and a reference note.

**10. Low: documentation code wrong, and the gap is wider than the text says.**
- `LANGUAGE_REFERENCE.md:3018` (D.11) says kabstract comparing `a + b` with another sum gives 93; it gives 99 (p51, p52, p01, p03).
- Nested sums are unsupported (`a + b + (a + b)`, `(a + b) + c`), and Lean accepts all four.

**11. Low: names resolved at read time.** `0 by-iterate ' nonexistent by-exact by-end` is refused with error 1, exit 4 (p21); Lean accepts, since iterate 0 expands to skip. `by-try` behaves the same on main (q2), so this predates the branch. Document it in D.11 and the iterate row.

**12. Low: portability.** `generalize.fs:41` uses `noop`, a Gforth word rather than Forth-2012. handover.fs and simp-data.fs already use it, and Gforth 0.7.3 has it.

**13. Low: message differences.** In p10 Lean prints `x.succ = x.succ` (field notation) and `@funext`; the `@funext` difference is documented, the field notation is not. p14 shows `@HAdd Nat Nat Bool` (the same kind as the documented IntCast case). p15 gives no detail.

## Probe table (my own files; terms compared node for node with the batch's `sx` dump)

| Probe | Shape | LeanForth | Lean | Result |
| --- | --- | --- | --- | --- |
| p02 | generalize under binders (revert c; generalize; intro c h) | accepted | accepted | same term |
| p04 | `at[ h2 h1 ]` | accepted | accepted | same term |
| p05 | `at[ v ]`, `hv : v = v` reverted with it (Fin) | accepted | accepted | same term |
| p53 | `at[ h2 h1 ]` of equal types, then rename `_ = c` | accepted | accepted | same term |
| p32 | `at[ h h ]` | accepted | accepted | same term |
| p18, p19, p26, p33, p39, p48 | shadowing x; generalize-eq of a variable; e only in h; eq form at h; `_ + b`; h and x one name | accepted | accepted | same terms |
| p01, p03, p51, p52 | e several times nested in sums; generalize-eq at h with e twice | 99, exit 2 | accepted | gap |
| p06 | `at[ hv v ]` | 93, exit 2 | refused | safe |
| p07 | rename `_ = a` with three candidates (newest fit j) | accepted | accepted | same term |
| p08, p09, p29, p36 | `rename _`; rename `Nat` (b); rename an inaccessible hypothesis; failing rename in try | accepted | accepted | same terms |
| p54 | try around a rename whose T does not elaborate | 131, exit 2 | accepted | gap |
| p10 | funext with more names than binders | 380 | 380 | same refusal |
| p42 | funext of `Nat.add a` | accepted | accepted | same term (Quot.sound) |
| p11, p44 | iterate 0 of a failing done; iterate failing inside first | accepted | accepted | same terms |
| p20 | iterate 253 / 600 skip | accepted | max recursion depth | **blocking** (finding 2) |
| p21 | iterate 0 of an unknown name | error 1, exit 4 | accepted | finding 11 |
| p12, p22 | done inside first; done with an assigned goal left | accepted | accepted | same terms |
| p13 | infer_instance, out-param `HAdd Nat Nat Nat` | accepted | accepted | same term |
| p14 | `HAdd Nat Nat Bool` | 125 | refused | same refusal |
| p15 | `Nat` (not a class) | 110 | 110 | same refusal |
| p16, p17, q4 | infer_instance with a local instance | accepted, global instance | accepted, local | **blocking** (finding 1) |
| q3 | `(d : Decidable True) : decide True = true := by rfl` | accepted (main too) | refused | **blocking** (finding 1, outside the diff) |
| p57, p58 | unclosed `by-funext[` | 458 | parse error | fails closed |

## Planted faults (scratch copy; batch-small-1 test.fs and check.py plus my probes)

| Fault | Branch tests | My probes |
| --- | --- | --- |
| F1 rename: no restore on the throw path | caught (test.fs, 482 test) | p36 exit 4 |
| F3 at[ ] order reversed | **survives** | p53 term differs |
| F6 funext: at most one pass | **survives** | equivalent today: a second pass is 93 |
| F8 rename without the new depth | **survives** | not reachable from text |
| F9 only the first at[ ] name | **survives** | p04 exit 4, p53 term differs |
| F17 rename with recover | **survives** | not reachable (131) |

## Trust and state
- Nothing bypasses the kernel: every "accepted" above comes from the kernel's check at `end`.
- `trn-search` restores the state on success (the test.fs probes) and on a throw (F1 is caught).
- Generalize's binder is opened by `lf-with-local-decl`, which drops the local however its word ends. Its frames are cut back on a throw by `lf-with-record`.
- A generalize that fails after its revert leaves the goal assigned at the Meta level, as Lean's MetaM does. At the tactic level only unsupported codes reach that point, and they stop the run.

## Re-entrancy (new globals)
- No new VARIABLE or VALUE in `src/`.
- `mgq-frames` and `mgh-frames` are context slabs.
- The 9 `lf-tactic:` rows are sealed by `lfr-open` (tactic-run.fs:304).
- `tit-mode` and `lfa-e-rename` are records allotted at load and never written again.
- Iterate's passes left live in the runner's frame.

## Reuse: what I searched
- Ran `check-duplicates.py` (no new or grown groups) and `check-lib-callers.py` (ok).
- Grepped `src/` by shape and by name for: tactic-state save/restore and withoutModifyingState, `lf-commit-when`, `run-filter`/`run-each`, name-or-`_` checks, `lf-meta-const-fresh` by name, `syn-k-const`/`syn-k-num` makers, the per-argument loop, `lf-with-location`, apply under synthesize, and `lf-goal-apply`.
- Results: findings 3 to 6. `lf-goal-apply-const` correctly replaces trivial's private copy; no other copy is left.

## Forth style
- **Metrics** (`forth-metrics.py --words 10`, 11 files): 146 words; 86% of one or two lines, none over 5; every word has a stack comment; no locals; 3 deep shuffles; 12 return-stack operations; no long lines; 8 globals (all `LF-TACTIC` rows).
- **S1** (`iterate.fs:28-29`): the passes left are stored in `tfr-at`, a field meant for a block's place. Name the use, for example a `tfr-passes` alias at the record.
- **S2:** `lf-goal-generalize-hyp ( goal args h hyps -- )` takes 4 items. Passing Lean's GeneralizeArg as a run of (e x h) triples gives `( goal args hyps -- fvars goal' )`, folds the `-eq` word in, and opens the way to several arguments.
- **S3:** `tgz-tac` and `tgz-eq-tac` are near copies (one uses `rot`). One `tgz-with ( i goal k h -- goal' )`, with `2>r swap dup tgz-names dup 2r> >r tgz-arg r> rot tgz-hyps tgz-gen`, serves both.
- **S4:** `mgq-closed` uses the address of the `mgq-x` field as a one-cell run. Say so in a comment.
- **S5:** the per-argument loop (`tfx-names`, `tgz-names`, and older copies in simp-only, subst, rewrite and exacts) could become one `lf-tac-args-each`. That can be a plan row.
- **Baseline entries.** Entries of exactly done 1, funext 2, generalize 2, infer-instance 1, skip 1 match the existing tactic files (exfalso 1, left 2, revert 2, obtain 2, …) and are justified: each "global" is a sealed registration row. One file per tactic is the plug-in design, so the files need no reshaping.
  - The metrics script does not count the rows in rename.fs and iterate.fs, because the shape word on the same line is taken as a name reader. That is a quirk of the script.

## What I ran
- `bin/leanforth check` and the dump (`decide-dump`) on my probes, with q1 to q3 also on main.
- Pinned Lean on the twins (`twins*.lean`, `e*.lean`).
- The batch's test.fs and check.py, both batches, in the scratch copy, as the baseline for planting faults.
- `forth-metrics.py`, `check-duplicates.py` and `check-lib-callers.py`.

## Not checked
- I did not run `make mutants` (the implementer's 21 faults), `cover-changed`, gforth-fast, Gforth 0.7.3, `check.py --lean` or `check-docs`.
- I did not test nested-iterate limits in Lean beyond `100 × 3`.
- funext's second pass cannot be tested today (a second pass is 93).

AI review does not replace the required human review.

The probe files (`p*.lf`, `q*.lf`, `twins*.lean`, `e*.lean`, `run.sh`, `cmp.py`, `faults.py`, `f3cmp.py`) are kept outside the repository, in the main checkout's untracked `.claude/work/small-tactics-1-probes/`; the probes the fix round turned into tests are named in the Resolution below.
## Resolution (fix round, 2026-11-26, branch `small-tactics-1-fix`)

All code fixes are in `5da9a111` (on `12334f6c`); the record is the commit after it.

- **Finding 1** (blocking, fidelity): fixed in `5da9a111`. A header's parameter (`elab-decl.fs`'s `edc-new-local`) and every local the tactic library pushes (`telescope.fs`'s `tl-classed`, through the deferred `lf-local-classed`, so `by-intro:`, `by-have-by:`, obtain/rintro and generalize's locals too) is a local instance when its type is a class: Lean's `withNewFVar` (Meta/Basic.lean:1819) and `withNewLocalInstances` (Basic.lean:1441; Intro.lean:25 and :59). The new `src/front/local-instances.fs` completes isClass? (Basic.lean:1576) past `lf-class?` with isClassExpensive? (:1554) and isClassApp? (:1544) at reducible transparency (`Ne` no class, `DecidableEq Nat` Decidable); a pi whose body needs whnf under binders is not supported yet. `instances.fs` and `data-index.fs` are unchanged: the existing guard (`it-local-free`) now answers 139. p16, p17, q4 (`u-ii-hygiene.lf`, `u-ii-local.lf`, `u-ii-explicit.lf`) and q3 (`u-ii-statement.lf`, no longer accepted) exit 2; `tests/front/tactics/local-instances/test.fs` (isClass? at each path, the header, a have's and intro's locals, sweeps); faults `sm1-local-instance-unmarked`, `-quick-only`, `-header-skipped`, `-tactic-skipped`, each caught. No other verdict moved: every `test-tactic-*-e2e`, `test-front-e2e`, `test-author-e2e`, `test-showcase` and `test-elab-data-e2e` pass unchanged. The guard asks the class only, so a local `Decidable True` also stops a search for `Decidable (a = b)` (tested, documented). Found on the way, in `instances.fs` (not edited): `it-class-name` leaves one cell fewer than its stack effect when `lf-menv-of-data` is refused: plan row 9.4.8z12 (e).
- **Finding 2** (blocking): fixed in `5da9a111`. Measured on pinned Lean: `iterate 251 skip` passes, 252 fails; two nested, counts summing to 250 pass, 251 fail; three, 248 pass, 249 fail; 101 nested `iterate 1` pass, 102 fail (about 2n + 3 levels per open iterate and 6, maxRecDepth 512). So the plain sum of counts is not safe (128 nested `iterate 1` would pass it); each open iterate weighs its count and 2 and an iterate that makes the open ones weigh more than `tit-most` (128) answers 99. Tests at 126 and 127, 62+62 and 62+63, two in a row, and the huge count (99, was 91); `u-it-deep.lf`; faults `sm1-iterate-unbounded`, `sm1-iterate-own-weight-only`.
- **Finding 3** (reuse): fixed in `5da9a111`: `tactic-run.fs`'s `lf-tac-without-modifying` (a refused save `lfr-must`, a refused put-back `lfr-sure`), rename's `trn-search` on it; tests in `tests/front/tactic-run.fs` (success and failure put back, a THROW passed on, a newer save left open, the save refused); faults `sm1-without-modifying-kept`, `sm1-without-modifying-unsure`. `tactic-run.fs`'s return-stack count kept at its baseline (`lfr-assemble` without `>r`).
- **Finding 4** (reuse): fixed in `5da9a111`: `mgh-filter` on `run-filter`, `mgh-keep` gone (FORTH_LIBRARY.md's runs profile names the caller).
- **Finding 5** (reuse): fixed in `5da9a111`: `tactic-core.fs`'s `lf-tac-name`; `thv-name`, `trn-name` and `tgz-name?` gone (`have.fs`, `by-cases.fs`, `rename.fs`, `generalize.fs`).
- **Finding 6** (reuse): fixed in `5da9a111`: `tactics/apply.fs`'s `lf-tac-apply-const`; `tfx-apply` and `ttr-apply-tac` gone.
- **Finding 7**: fixed in `5da9a111`: p04, p05, p53 as `gz_at_two`, `gz_at_dep`, `gz_at_order` in `generalize.lf` with their twins in `batch-small-1.lean` (golden rewritten by pinned Lean), F3 and F9 planted as `sm1-generalize-at-reversed` and `sm1-generalize-at-first-only` (caught by check.py), F8 as `sm1-rename-no-new-depth`, caught by test.fs's `by-probe-k` (k : a = ?w, then `a a = by-rename: j`: 482, as e55). F17 is a known gap: plan row 9.4.8z12 (h). F6 stays equivalent while a second funext pass is 93.
- **Finding 8**: fixed in `5da9a111`: the unclosed `by-funext[` (458 at its word) and `open?` after the 380.
- **Finding 9**: fixed in `5da9a111`: `revert.fs`'s two comments, `u-gen-dep.lf` (93, exit 2), D.11's note.
- **Finding 10**: fixed in `5da9a111` (D.11 says 99 and names the nested sums); the gap itself is plan row 9.4.8z12 (d).
- **Finding 11**: documented in `5da9a111` (D.11 and the `by-iterate` row); older than the branch (`by-try` alike).
- **Finding 12**: fixed for `generalize.fs` in `5da9a111` (`tgz-target`); `handover.fs` and `simp-data.fs` are plan row 9.4.8z12 (f).
- **Finding 13**: documented in `5da9a111` (D.11: field notation, `HAdd Nat Nat Bool`); plan row 9.4.8z12 (g).
- **S1**: fixed in `5da9a111` (`tfr-passes`, an alias of `tfr-at` at the record). **S2**: plan row 9.4.8z12 (a). **S3**: fixed in `5da9a111` (`tgz-with`). **S4**: fixed in `5da9a111` (comment). **S5**: plan row 9.4.8z12 (b).
- **Baseline entries**: made in `5da9a111` as the owner approved on 2026-11-26 (OWNER_DECISIONS.md, last section): done 1, funext 2, generalize 2, infer-instance 1, skip 1, by hand; no existing entry raised.

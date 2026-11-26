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

## Re-check (2026-11-26)

Range reviewed: 12334f6c..727d4c72. The code fix is 5da9a111 and the record is 727d4c72. Findings: 1 blocking, 1 medium, 3 low. Verdict: **blocking**, because of finding 1 (the iterate bound). The local-instance fix (point 1 of your brief) has no blocking finding.

### Findings

**1. Blocking: the `by-iterate` bound misses the other blocks, so LeanForth accepts proofs that pinned Lean refuses with "maximum recursion depth has been reached".**
- **Where:** `src/front/tactics/iterate.fs:40-48` (`tit-weight`, `tit-weights`, `tit-bounded`, `tit-open`).
  - Only iterate frames are weighed.
  - The weight is checked only when an iterate opens.
  - The comment at `:16-20` ("128 … leaves room for the blocks around") is false.
- **Probes** (LeanForth on the head gives exit 0; Lean refuses):
  - `i_try_36`: 36 nested `by-try` around `126 by-iterate by-skip by-end`. Lean accepts 35 and fails from 36.
  - `i_anyg_48`: 48 nested `by-any-goals` around the same iterate. Lean accepts 40 and fails at 48.
  - `i_haveby_20`: nested `by-have-by:` bodies around the same iterate. Lean accepts 17 and fails from 18.
  - `j_iter_out_try_36`: `126 by-iterate` whose body is 36 nested `by-try` around `by-skip`. Lean accepts 20 and fails at 36. Blocks opened inside an iterate are never checked at all.
- **Older than the branch, same cause (no iterate involved):**
  - `j_haveby0_40` and `j_haveby0_60`: Lean accepts 30 nested have-by and fails at 40.
  - `j_try0_80` and `j_try0_100`: Lean's one-line twin accepts 70 nested `try` and fails at 80 (at parse time).
  - LeanForth accepts all four.
- **Lean's cost per level, measured:**
  - iterate n: about 2n+3 levels
  - try: about 7
  - first, any_goals, all_goals: about 5.5
  - have-by: about 14
  - `{ }`: about 0 (60 nested pass)
  - repeat: a loop (`Elab/Tactic/Repeat.lean:17-26`), constant depth
  - the limit, maxRecDepth: 512
- **Fix:** one recursion budget in the runner, checked whenever any block opens. It replaces the iterate-only walk.

```forth
\ tactic-run.fs: Lean's maxRecDepth (512) over the open blocks, at every
\ block's open. Units of two levels (pinned Lean 4.35.0, 2026-11-26):
\ iterate n: n + 2 (2n + 3 levels); a have-by body: 8 (14); any other
\ block: 4 (try 7, first and any_goals about 6).
240 constant lfr-rec-most              \ 480 levels, 32 left for the rest
: lfr-weight ( frame -- w ) dup tfr-mode @ tbm-weight @ execute ;
: lfr-weights ( -- w ) 0 lfr-depth 0 ?do i lfr-frame lfr-weight + loop ;
: lfr-rec-check ( -- ) lfr-weights lfr-rec-most > if lf-tac-unported then ;
\ the weight set per mode after lf-block-mode (default ' lfr-block-weight, : lfr-block-weight ( frame -- w ) drop 4 ;)
\ iterate.fs: : tit-weight ( frame -- w ) tit-count 2 + ;   ' tit-weight tit-mode lf-mode-weight!
```

- **Tests to add** for each wrapper, on both sides of Lean's limit: try 35/36, any_goals 40/48, have-by 17/18 around iterate 126; iterate 126 around 20/36 tries; have-by 30/40 and try 70/80 with no iterate.
- **Docs:** update `LANGUAGE_REFERENCE.md:2014` and D.11 (around `:3010-3017`).
- If the no-iterate part is not fixed in this branch, give it a plan row.

**2. Medium: the local-instance tests do not cover the paths the Resolution claims.**
- The Resolution says obtain/rintro, generalize and let locals are covered, but `tests/front/tactics/local-instances/test.fs` tests only the header, have-by and revert-then-intro.
- My probes show that these paths work today, but nothing pins them:
  - `by-let:` (li10; Lean's term uses e)
  - `by-have:` with a term (li09)
  - `by-obtain[` (li11)
  - `by-generalize:` (li12, li18)
  - `by-intros` (li20)
  - rename keeping the mark (li13)
  - clear removing it (li14: accepted, term equal to Lean's)
- The transparency of isClassExpensive? is not pinned either: planted fault F1 (below) survives every branch test.
- **Fix:** add these as unit tests or as `u-`/accepted `.lf` files with Lean twins. Include `True Decidable id explicit: d` (li01/li01b): `id` is `implicit_reducible` (Prelude.lean:131), so Lean does not treat d as a local instance and the text must be accepted with the global instance.

**3. Low: coverage lost by the fix (documented, never accepting a wrong result).**
- (a) The guard asks only for the class (`instances.fs:418-422`). So `(d : Decidable True)` blocks `Decidable (a = b)` (139), where Lean tries d, fails to unify and takes the same global instance. Before the fix this was accepted with Lean's term. Name it under plan FE3 or 9.4.8z12.
- (b) A local whose type is a pi with a reducible-definition head under the binders now stops with error 93.
  - Probe r2, `' Nat.succ_ne_zero by-have`: exit 0 before the fix, exit 2 now (error 93); Lean accepts.
  - `LANGUAGE_REFERENCE.md:3043-3046` should name code 93 and the common way to reach it (`by-have` of a library lemma such as Nat.succ_ne_zero).
  - The port of whnf under binders is planned in 9.4.8z12 (e).

**4. Low: a fidelity detail of withNewLocalInstanceImp.**
- Lean skips implementation-detail locals (`Meta/Basic.lean:1417-1422`, `isImplementationDetail`); `li-classed` (`local-instances.fs:60-62`) does not.
- No word in `src/` makes such a local today, and the effect would only be more "not supported yet" answers.
- **Fix:** `dup lf-local-detail? if outcome-ok exit then` at the start of `li-classed`, or a comment saying why it is not needed.

**5. Low (reuse, mostly planned).** `lf-class-whnf?` is the complete isClass?, but the other isClass? callers keep the quick test, which answers unsupported where Lean goes on: `elab-pending.fs:261` (`lf-elab-class?`), `simp/rewrite.fs:89` (`sr-class?`), `synth.fs:714`, and the fun-info/congr-thms path. Plan row 9.4.8z12 (e) moves `lf-class-whnf?` beside `lf-class?`; add to that row that these callers switch to it, or say why they keep the quick test.

### Transparency and whnf of the port (point 1c)

The port follows Lean's lines:
- **isClassQuick?:** run at the ambient transparency (`getDefInfoTemp`, Basic.lean:1363-1371; `it-defn-temp?` reads the same rule).
- **isClassExpensive?** (Basic.lean:1554-1556): whnf under withReducible (`lf-with-reducible`, `lf-meta-whnf`).
- **isClassApp?** (Basic.lean:1544-1552): after whnf only a class constant at the head counts. Turning "undefined" into none through `li-none` is right because whnfR leaves no reducible head.

Where it differs, the difference is safe:
- Under binders a body that needs whnf is unsupported, where Lean opens the telescope.
- Failures are passed on as outcomes, where Lean's isClass? catches them and answers none.

It cannot loop: there is no recursion, and whnf has its own fuel (whnf.fs:74-81; running out gives an exhausted outcome). The deferred `lf-local-classed` is set only at load time (telescope.fs:127, local-instances.fs:63). No new VARIABLE, VALUE or table is written after loading.

### Probe table (LeanForth head 727d4c72 vs pinned Lean 4.35.0)

"Term equal" means LeanForth's terms equal Lean's node for node (`sx` dump). Every shape below that Lean refuses was **accepted before the fix** (12334f6c), and every class-typed local was accepted before with the global instance.

| Probe | Shape | LeanForth now | Lean | Result |
|---|---|---|---|---|
| li02 | `(d : outParam (Decidable True))`, then `decide` by rfl | 139, exit 2 | refused | fixed (accepted before) |
| li04, li05 | `{d}` and `⦃d⦄` : Decidable True, rfl | 139 | refused | fixed |
| li06, li20 | revert d, then `by-intro:` / `by-intros`, rfl | 139 | refused | fixed |
| li08 | `by-have-by:` e, then rfl of decide | 139 | refused | fixed |
| li09 | `by-have:` e := instDecidableTrue, rfl | 139 | refused | fixed |
| li11 | `by-obtain[` d from ∃ x, instDecidableTrue = x, rfl | 139 | refused | fixed |
| li12 | `by-generalize:` instDecidableTrue = d, rfl | 139 | refused | fixed |
| li26 | the 139 inside `by-try` | exit 2 (not swallowed) | refused | safe |
| li03, li23 | `(d : DecidableEq Nat)`, `outParam (DecidableEq Nat)`, infer `Decidable (a = b)` | 139 | accepted with d | safe |
| li07 | revert DecidableEq d, `by-intro[ e ]`, infer | 139 | accepted with e | safe |
| li10 | `by-let:` e, infer | 139 | accepted with e | safe |
| li13 | `by-rename:` of d, infer | 139 | accepted with e2 | safe |
| li18 | generalize, then infer | 139 | accepted with d | safe |
| li25 | `' Nat.decLe by-have` (∀ n m, Decidable (n ≤ m)), infer | 139 | accepted with this | safe |
| li01, li01b | `(d : id (Decidable True))`, infer / rfl | accepted | accepted (no local instance) | term equal |
| li14 | clear d, rfl | accepted | accepted | term equal |
| li15, li16, li17 | `a ≠ b`, `¬ a = b`, `Fin a`, infer | accepted | accepted | term equal |
| li27 | `by-cases:` a ≤ b | accepted | accepted | term equal |
| r1, r3, r4, r5, r7, r8, r9 | `by-have` of le_refl, lt_irrefl, add_zero, zero_le, not_lt_zero, le_succ; `(hl : a ≤ b)` | accepted | accepted | term equal |
| r2 | `' Nat.succ_ne_zero by-have` | 93, exit 2 (exit 0 before) | accepted | lost coverage (finding 3b) |
| r6 | `' instDecidableEqNat by-have` | 136 (also before) | accepted | older gap |
| li19 | natural-form `forall` in a statement | error 70 | n/a | statement binders cannot be written; kernel form runs no instance search |
| i_try_35 / i_try_36, 40, 60 | try×k around iterate 126 | accepted | 35 accepted / 36+ refused | **blocking** |
| i_anyg_40 / i_anyg_48 | any_goals×k around iterate 126 | accepted | 40 accepted / 48 refused | **blocking** |
| i_haveby_20 | have-by×20 around iterate 126 | accepted | refused (fails from 18) | **blocking** |
| j_iter_out_try_20 / 36 | iterate 126 around try×k | accepted | 20 accepted / 36 refused | **blocking** |
| i_focus_35, 40, 60 | `{ }`×k | accepted | accepted | same |
| i_rep_36 | repeat of a body that never fails | 91, exit 3 | heartbeat timeout | both refuse |
| i_first_40/48, i_haveby_30/40, i_rep_60 | — | error 39 (line too long) | — | not reached |
| j_haveby0_30 / 40, 60; j_try0_80, 100 | nesting with no iterate | accepted | 30 accepted / 40+ refused; try 70 accepted / 80 refused | older than the branch, same cause |

### Planted faults (scratch copy of the head)

| Fault | Branch tests | My probes |
|---|---|---|
| F1: `lf-class-whnf?` without `lf-with-reducible` (local-instances.fs:53), so isClassExpensive? runs at default | **survives** local-instances test.fs and batch-small-1 test.fs and check.py | li01 and li01b give 139 where Lean and the head accept |
| F2: `tit-weight` without the mode test (iterate.fs:42) | caught (batch-small-1b test.fs:92, 126 alone gives 99; caught only incidentally, through the root frame) | — |
| F3: `lf-let-decl-new` pushing its local unmarked (telescope.fs:136) | caught (local-instances test.fs, the have's local) | under the fault li08 is accepted where Lean refuses. The same fault limited to the dependent let would survive, because no test has a class-typed `by-let:` |

### Reuse and style
- **Reuse searched:**
  - `check-duplicates.py` in the worktree: 187 baseline groups, none new or grown.
  - `--new-words --base 12334f6c --head 727d4c72`: none.
  - `check-lib-callers.py`: ok.
  - Grepped `src/` for isClass?, isClassExpensive? and isClassApp? ports and callers of `lf-class?`. No copy found; finding 5 is the only reuse point.
  - Grepped every path that makes or pushes a local (`lf-local-new`, `lf-view-push`, `lf-local-decl-new`, `lf-let-decl-new`, `lf-view-refvar`, `lf-local-renamed`). Each one marks or keeps the mark as Lean does: defeq's binder locals are not marked, matching isDefEqBindingAux, and replaceLocalDeclDefEq keeps its local instances.
- **Metrics** (`forth-metrics.py --words 10` on local-instances.fs, iterate.fs, telescope.fs, elab-decl.fs): 141 words, 83% of one or two lines, none over 5 lines, every word has a stack comment, no globals, no locals, 6 deep shuffles (all in telescope.fs), 39 return-stack operations, no long lines.
- **Style:** no new style findings in the re-checked words.

### Not checked
- gforth-fast and Gforth 0.7.3.
- `make cover-changed`, `make mutants` on the implementer's faults, `check.py --lean`.
- Lean's depth for nested first and have-by past LeanForth's line limit; `<;>` and all_goals in LeanForth.
- Whnf fuel running out inside `lf-class-whnf?` (only the implementer's heap sweep covers refusals there).
- The cost of the extra whnf for each pushed local, and fed mode.
- li20-li27 on the pre-fix tree.

### What I ran
- `bin/leanforth check` on the decide slice, on scratch copies of 727d4c72 and 12334f6c (`git archive`).
- `tests/front/elab-dump.fs` for the term dumps; pinned Lean 4.35.0 called directly on my twins.
- The local-instances, batch-small-1 and batch-small-1b `test.fs` files and the batch-small-1 and batch-small-1b `check.py` files, in a scratch copy, for the faults.
- Everything under `ulimit -u 500`. No elan proxies, no make, no agents; no repository or worktree was modified.

Probes, twins and the harness were in the re-checker's scratch folder (`probes/`, with the runner `run.sh`); a copy of the probes and twins is kept in the main checkout's `.claude/work/small-tactics-1-recheck-probes/` (machine-local).

AI review does not replace the project's required human review.

### Resolution (second fix round, 2026-11-26, branch `small-tactics-1-fix2`)

The code fixes are `33e51e05`, `34dc834a` and `91ac4bb9` (on `727d4c72`); the record is the commit after them.

- **Finding 1** (blocking): fixed in `33e51e05`. One bound in the runner (`tactic-run.fs`'s `lfr-weighed`, in `lfr-block-as`, so every block that opens is checked before its mode's open): each mode has a weight ( frame -- w ), a new field of the mode record (`mode-weight`, `lf-mode-weight!`, set while the modules load; no module-level state), in units of two of Lean's levels, and a block that would make the open blocks weigh more than `lf-tac-depth-most` (240: 480 of Lean's 512 levels) is 99 at its step, its frame taken off and its goals put back (`lfr-unopen`), as an ordinary unsupported step leaves them; iterate's own walk (`tit-most`, `tit-weights`, `tit-bounded`) is gone and `tit-weight` (count, at most the bound, and 2) is iterate's mode weight. The weights, each at least one level's cost on pinned Lean 4.35.0 in its costliest one-line spelling (measured on both sides of the limit around `iterate 126 skip`, 255 levels): the proof's `by` 4 (Lean about 7 levels), a have-by body 8 (`(have z : a = b := by { X; exact h })`: 16 accepted, 17 refused, 15.6 levels at most), `iterate n` n + 2 (2n + 3: 251 accepted, 252 refused), `repeat` 5 (`repeat ((X); fail)`: 27/28, 9.3), first's alternatives 0 (first itself 4: `first | (X)` 41/42, 6.1), any other block 4 (`try (X)` 35/36, 7.2; any_goals, all_goals and focus 41/42, 6.1; `(· X)` 40/45, 6.3; `(next => X)` 35/40, 7.1; `skip <;> try (X)` 16/18 and `skip <;> { X }` 30/34, so the then-block about 7.4; `{ X }` 200/250, 1.3). Without iterate: `try (...)` 72/74 and have-by 32/34. Written in layout Lean goes deeper (try 60, have-by 22 around iterate 126), so the one-line twins are the stricter reference. LeanForth accepts up to: 27 try, any_goals, all_goals, first, focus or braces around 126 by-iterate (Lean 35 and 41), 13 have-by or `<;>` try (Lean 16), 21 repeat (Lean 27), 27 try inside it (Lean 35), 29 have-by and 59 try alone (Lean 32 and 72), iterate 234 alone (Lean 251). The re-check's probes are all 99 now: i_try_36, i_anyg_48, i_haveby_20, j_iter_out_try_36, j_haveby0_40 and 60, j_try0_80 and 100. Tests: `tests/front/tactics/rec-depth/` (test.fs on both sides of LeanForth's bound and past Lean's for each block listed, the weights of every mode, the refused frame and goals, the nine-digit count; check.py: `u-rd-try.lf` and `u-rd-have.lf` exit 2 with 99, and with `--lean` pinned Lean accepts rec-depth.lean's 13 theorems and refuses rec-depth-wrong.lean's 13 with the depth error). Faults `sm1-depth-weight-ignored`, `-check-skipped`, `-have-by-light`, `-repeat-light`, `-alternative-weighed`, `-refused-frame-kept`, `-refused-goals-kept`, `-bound-off-by-one`, and the re-pointed `sm1-iterate-zero-runs`, `-any-count`, `-unbounded`, `-own-weight-only`: each caught. Verdicts moved by the bound, all in LeanForth's own tests: `u-it-deep.lf` (200 now accepted: made 235), iterate's unit tests at 127 and 62 + 63 (now accepted: 235 and 116 + 117), and `tests/front/tactic-run.fs`'s 1,000 nested blocks (accepted before; Lean refuses that depth): it keeps its purpose (heap frames, no host recursion) in a test mode that weighs nothing, and pins the 99 at the 60th block otherwise. Docs: LANGUAGE_REFERENCE.md D.2 (the bound and its weights), the `by-iterate` row and D.11; iterate.fs's comment.
- **Finding 2** (medium): fixed in `34dc834a`. `tests/front/tactics/local-instances/test.fs` pins by-let:'s local (li10), by-have: with a term (li09), by-obtain[ (li11), by-generalize: (li12, li18), by-intros after revert (li20), by-rename: keeping the mark (li13) and by-clear removing it (li14, accepted), and `True Decidable id explicit: d` accepted with the global instance (li01, li01b). F1 is `sm1-local-instance-default-whnf` and F3 limited to the dependent let `sm1-local-instance-let-unmarked`, both caught by that file.
- **Finding 3**: (a) plan row 9.4.8z12 (e) in `91ac4bb9` (the guard compares the full type); (b) documented in `91ac4bb9` (LANGUAGE_REFERENCE.md D.11: error 93, `' Nat.succ_ne_zero by-have`), its port 9.4.8z12 (e).
- **Finding 4**: fixed in `91ac4bb9`: `li-classed` skips an implementation-detail local (`lf-local-detail?`), tested with such a local of a class's type; fault `sm1-local-instance-detail-classed`, caught.
- **Finding 5**: plan row 9.4.8z12 (e) in `91ac4bb9`: `lf-elab-class?`, `sr-class?`, `synth.fs:714` and the fun-info/congr-thms path switch to `lf-class-whnf?`.
- **Style**: `tactic-run.fs` stays at its baseline (3 deep shuffles, 21 return-stack operations, no long word); no baseline entry raised.

# Forth review: tactic batch 1, plan row TB1 (2026-11-19)

Branch tactic-batch-1, range **b80169d3..70c32327**: the batch's 9 first-parent commits eba4dfa2, 452144a8, d86687a3, 9c9b8389, bf92bef5, 1b972fcd, 82b35420, 0669d56f and c9265f0c. What came in from main is not reviewed. The worktree head 80b9d177 has no `src/` change after 70c32327. Reviewer: forth-reviewer (Opus), independent of the implementer.

Findings: 0 high, 2 medium, 8 low. Three are blocking (B1, B2, B3), and each is a few lines.

**Verdict: merge after B1-B3.**
- I found no Lean-fidelity failure in left, right, exfalso, intros or clear, or in the behaviour changes (intro-n's kinds, apply's "the term").
- No path reports success where Lean fails, or closes or leaves a goal Lean would not.
- The fidelity-review fixes are closed as stated.
- The two restructurings are behaviour-identical.

## Findings

**B1 (low, blocking: reuse). `mti-inner` and `lf-intros-size`'s loop re-implement `lf-meta-under`.**
- Location: meta-tactic/goal.fs:277-279.
- `lf-meta-under ( e tag -- e' true | e false )` (meta-spine.fs:131) already gives a let's body, or a pi's body. goal.fs requires meta-spine.fs since this batch. prop-quick.fs:105 walks the same way.
- Fix: delete `mti-inner` and write the following. This was run: intros/test.fs passes.
  ```forth
  \ getIntrosSize: the leading pis and lets (lf-meta-under, meta-spine.fs).
  : lf-intros-size ( type -- n )
    0 swap begin lf-tag-pi lf-meta-under while swap 1+ swap repeat drop ;
  ```

**B2 (low, blocking: reuse). The phrase "free variable of the current context's local k" is spelled out five times, and `lf-view-fvar` missed one copy.**
- The batch made `lf-view-fvar` public, but assign-check.fs:182 `ac-let-at?` still spells it out as `lf-view-local lf-local-fvar`.
- `lf-mctx-view swap lf-view-fvar` now appears at:
  - assumption.fs:51 (`mas-fvar`, private);
  - goal.fs:302 and :305 (`mcl-dep?` and `mcl-dependent`, new);
  - elab-term.fs:138;
  - and, spelled out, in `ac-let-at?`.
- Fix: one word in mvars.fs, beside `lf-mctx-view`. mvars.fs requires lctx-views.fs, and every user requires mvars.fs.
  ```forth
  : lf-mctx-fvar ( k -- fvar ) lf-mctx-view swap lf-view-fvar ;   \ local k's free variable
  : ac-let-at? ( i -- flag ) lf-mctx-fvar lf-fvar-let? ;
  ```
- Then delete `mas-fvar` (its callers use `lf-mctx-fvar`), and use the word at goal.fs:302 and :305 and at elab-term.fs:138.

**B3 (medium, blocking: a fault recorded as equivalent is caught by a test).**
- The fault `tb1-get-fvar-postponing` (faults.d/clear.toml:61) says no test can tell mayPostpone true from false. That is wrong for an application.
- `' id 0 $ by-clear`:
  - on the head: "Unexpected term `@id Nat 0`; expected single reference to variable" (default instance applied, as Lean's mayPostpone := false does);
  - under the fault: "`@id ?m.10 0`".
- Both runs were `bin/leanforth check` on the S2 slice.
- Fix: add the following to tests/front/tactics/clear/test.fs, then delete the fault's `equivalent` key.
  ```forth
  T{ s" ' id 0 $ by-clear" ran -> 389 }T
  T{ s" `@id Nat 0`" detail-has? -> true }T
  lf-tac-forget
  ```
- Run: it passes on the head and fails under the fault ("INCORRECT RESULT").
- Pinned Lean prints `id 0` here (see L4).

**M1 (medium, tests). `lf-goal-intros`'s instantiation is unpinned.**
- Location: goal.fs:283, `lf-goal-type lf-instantiate! lf-intros-size`.
- My fault r11 drops `lf-instantiate!`, and every test still passes.
- Lean's MVarId.intros counts the instantiated type (Intro.lean:202-203). apply's new goals hold assigned metavariables in their spine. For example, `a ≤ b → ?c` with ?c := `a ≤ b → a ≤ b`: Lean introduces 2, the fault 1.
- Add a unit test: a goal whose type is a metavariable assigned `three`'s pi, and one whose pi body is such a metavariable. Expect n = 3 and 2. Plant the fault as `tb1-intros-uninstantiated`.

**L1 (low, tests). checkNotAssigned is not distinguished in clear.**
- clear/test.fs:88 tests the assigned goal with `fb`, which no refusal reaches. goals.fs's own refusal gives the same -4201.
- So my fault r4, which drops `over lf-goal-not-assigned drop` at goal.fs:313, survives.
- Fix: use `fa` there. The head gives -4201; the fault gives 441.
- exfalso has the same gap: my r15 (no `lf-goal-not-assigned` in `lf-goal-exfalso`) survives. It is near-equivalent, because `mtg-assign` refuses the assigned goal with -4201 anyway.
  - Record it as equivalent, or check that no new metavariable was made.

**L2 (low, tests). exfalso's target instantiation is unpinned.**
- My fault r5 drops `lf-instantiate!` in `mtg-elim` (goal.fs:168), and it survives.
- The finished term is the same after instantiation, so this is near-equivalent.
- Either pin the raw assignment's argument on a goal whose type is an assigned metavariable, or record the fault as equivalent.

**L3 (low, tests class 5).** No exhaustion test covers `lf-goal-exfalso`, `lf-goal-intros` or `lf-goal-clear!`, that is, a store or heap refusing part-way, then the goal left unassigned and the context and slabs as before.
- Their refusals all go through `lf-must`, and no new branch is unrun. So this is the coverage class, not coverage debt.
- A heap or room sweep over one call of each would pin "fails closed".

**L4 (low, Lean difference in printing, existing).** Error 389's text prints implicit arguments with `@`. Lean hides them.
- LeanForth prints `@id (a ≤ a) h` and `@id Nat 0`; pinned Lean prints `id h`.
- This is the printer gap already known under plan 8.6 (the earlier review's `@Append Type`).
- The 389 twin uses a constant only, so it agrees. Note this in clear.fs's header; no new plan row is needed if 8.6 covers it.

**L5 (low, style). A frame field is used as a register.**
- `mti-k` (goal.fs:215) is written by `mti-kind!` (:246) and read by the next word, `mti-local` (:254), in the same step.
- It is re-entrant (frame on a context slab), but it is a register.
- Stack form (costs 2 return-stack ops):
  ```forth
  : mti-local ( pi kind -- fvar )
    >r dup mti-dom swap mti-named r> or lf-local-decl-new lf-mctx-view! ;
  : mti-step ( -- )
    mti-binder mti-unlet dup dup mti-kind mti-local dup mti-x! mti-body mti mti-type ! ;
  ```
- Then drop `mti-k` and `mti-kind!`. Optional, because of that cost.

**L6 (low, docs and robustness).**
- `lf-tac-ex`'s header (tactic-msg.fs:32-36) lists its users but omits clear's 440-442.
- `mnc-bounded` (constructor.fs:112) compares signed, so a record with a negative idx loads. Lean's idx is a Nat. Use `u<`:
  ```forth
  : mnc-bounded ( nth -- )
    dup nth-idx @ swap nth-expected @ u< 0= abort" lf-nth-constructor: idx >= expected" ;
  ```

## Lean fidelity
Lean 4.35.0 source was read. Pinned Lean was run on probes.lean (below) and LeanForth on the same inputs.

- **left and right.**
  - evalLeft and evalRight (BuiltinTactic.lean:660-664) are `liftMetaTactic (nthConstructor name idx (some 2))`; LeanForth uses `lf-lift-meta-tactic` with no synthesize.
  - nthConstructor (Apply.lean:300-314) runs: checkNotAssigned, then matchConstInduct of getType''s head, then the count test, then `goal.apply (mkConst ctor us)` with no term?, so apply's message says "the term". LeanForth follows the same order and texts.
  - `mco-type` is instantiate, then whnf, then instantiate, as before.
  - Probe: `left` on `a = a ↔ a = a` gives 386 in both, byte for byte.
- **apply's messages.**
  - by-apply now calls `lf-goal-apply-named`, so its 380 and its Note still print `` `e` `` (evalApply passes term? `` m!"`{e}`" ``, ElabTerm.lean:304). Users see no change.
  - constructor's own 380 cannot surface, because its final apply already succeeded under observing.
  - Fault `tb1-apply-tactic-unnamed` pins this, and my r7 (nth using named apply) is caught by left/test.fs.
- **exfalso.**
  - The macro is `refine False.elim ?_` (Init/Tactics.lean:276). refine elaborates it against the instantiated main target.
  - The level is the same: ?C := T gives `Sort ?u =?= inferType T`, which is getLevel's level, including through delta and `max`/`imax`.
  - The tag is the same: tagUntaggedGoals gives the single new goal the parent's tag.
  - So the term `@False.elim.{u} T ?g` equals MVarId.exfalso's (Apply.lean:286-293). The new goal is synthetic opaque of type False, in the main goal's context.
  - Probe: `exfalso; exact h` on goal False, where pinned Lean's `#print` gives `fun h => False.elim h`. LeanForth accepts it.
  - `lf-goal-exfalso` relies on the caller's context (documented). Lean's does its own withContext. This is a precondition for future callers (contradiction).
- **intros.**
  - evalIntros (BuiltinTactic.lean:396-400) is liftMetaTactic of MVarId.intros. getIntrosSize (Intro.lean:190-194) counts forallE and letE syntactically, has no letFun case, and skips mdata.
  - n = 0 returns the goal with no checkNotAssigned; LeanForth exits before any check, the same.
  - introNImp (:47-55) uses `mkLocalDecl … c`, so implicit and strict binders are introduced with their kind, now in LeanForth too. Pinned Lean on `∀ {n}, …` gives `fun h {n} => …`.
  - Lets and instance binders stay 99, which fails closed. tactic-alts' `tal-field` passes explicit kinds, so it is unaffected by the kinds-0 change.
- **clear.**
  - Clear.lean:20-41 has three refusals: unknown, the oldest dependent local (lctx.forM, itself skipped), then the target.
  - localDeclDependsOn has `generalizeNondepLet := true` by default, which is goals.fs's "let not hidden".
  - exprDependsOn counts an unassigned metavariable whose local context holds the variable; mvars.fs `mv-dep-hit?` does too.
  - Probes, identical texts and goals in both:
    - p2: `apply Nat.le_trans; clear h1` gives 442 "target depends on 'h1'", case a, `⊢ a ≤ ?m`;
    - p8: `clear a` gives 441 "variable 'h' depends on 'a'".
  - 440 is not reachable from by-clear, because getFVarId elaborates in the same context. It is unit-tested.
  - getFVarId (ElabTerm.lean:272-277): `withoutRecover`, `elabTermForApply (mayPostpone := false)`, then "Unexpected term `e`; expected single reference to variable". The ident path and the instantiation agree. See B3 for mayPostpone and L4 for the `@`.
  - `' _` and `' 0` are not LeanForth syntax (error 59), so the `?m` case of getFVarId cannot be reached.
- **`tb1-clear-self-dependent` is truly equivalent.**
  - A local's type, or a let's value, is built before the local, and `lf-depends-on?` instantiates first.
  - A metavariable reaching the local's own type with the local in its context would need a `checkAssignment` that LeanForth refuses.
- **`tb1-get-fvar-postponing` is not equivalent** (B3).

## Fidelity-review fixes (452144a8) and restructurings
- **B1 of that review.**
  - `lf-meta-app2?` and `lf-meta-args2` are in meta-spine.fs. The four copies are gone: `mrf-binary?` and `mrf-rel-sides`, `no-sides`, `et-type-args`, and `lf-eq?`'s inner phrase.
  - The `lf-eq?` rewrite gives the same (α a).
  - A grep of `first@ lf-term-second@ swap lf-term-second@` and `first@ lf-term-app?` over src/ finds only meta-spine.fs. (The kernel's whnf.fs:629 and front whnf.fs:553 are different shapes.)
- **M1, L1, L4-L8.** Closed as the Fixes section says. I checked L5's comment, L6's `require ./meta-config.fs` and L4's header in the diff, and the faults are in faults.d/tactic-fidelity.toml.
- **`wc-unfold-run` (0669d56f) is identical.** With `ok-then2? ( x1 x2 o -- x1 x2 true | o false )`, a delta failure leaves `o false`. The new `else false` keeps it. `0=` then gives `-1 o` through no-result in both versions, and the success path is unchanged.
- **`no-push-sides` (c9265f0c) is identical.**
  - It is reached only from `no-run`, through `no-step` right after `no-pop`. The first push reuses the cell just popped, within the slab's capacity, with no allocation, so it cannot fail.
  - Even if it could, `outcome-and` returns the same first failure. The only difference would be a stray cell on a failing path, and `lf-meta-eval-nat` clears it with `slab-clear` on the next call.
  - `wm-none?` and `lf-whnf-stuck` came from main (s2-debt), not from this batch.

## Trust boundary
- Every new path ends in a goal assignment that the kernel checks.
- Refusals fail closed: lets and instance binders give 99, getFVarId non-variables 389, and an assigned goal -4201.
- No refusal becomes an acceptance. In particular, B3's fault only changes a failure's text.

## Reuse (step 3a)
- **Searched:**
  - FORTH_LIBRARY.md and the slab.fs and runs.fs word lists;
  - meta-spine.fs, mvars.fs and lctx-views.fs;
  - `grep -rn` over src/ for each new short word's token sequence:
    - `0 swap run-push`;
    - `slab-claim lf-must swap|over slab-at`;
    - `lf-menv-find dup outcome-invalid`;
    - `lf-view-local lf-local-fvar`;
    - `lf-mctx-view swap lf-view-`;
    - `lf-level! 1 lf-mk-const-id`;
    - `lf-tac-goal-of. lf-tac-detail`;
    - `lf-let? if lf-let-body`;
    - `lf-term-pi? while`;
    - `lf-goal-type lf-instantiate! lf-whnf!`;
    - `lf-kind-inductive =`;
    - `slab-count 2>r`;
    - `tb tb-goal @ swap execute`;
    - `dup lf-meta-app? if lf-term-first@`;
    - `lf-depends-on? lf-must`.
- **check-duplicates.py:** "205 baseline groups, each with a reason, none new or grown".
- **check-lib-callers.py:** clean (bigint.fs is planned, FE1i-4).
- **Findings:** B1 (`lf-meta-under`) and B2 (`lf-mctx-fvar`, and `ac-let-at?`'s missed copy).
- **Considered and not raised:**
  - `0 swap run-push` appears twice (lf-goals1 and synth.fs:289). This 3-token "[x]" could become `run-1` in runs.fs; it is optional.
  - `lf-with-record` and `lf-with-cells` share their save, catch, cut and rethrow tail. Factoring it needs a third word that does the claim inside the guarded region, which is not clearer.
  - `mm-inductive` and `mm-declared` replace the old `mco-decl`, `mco-inductive?` and `mel-inductive` copies.
  - `mtg-at-level` is shared by Eq.mpr and False.elim.
- **Homes:**
  - `lf-match-const-induct` in meta-must.fs is right: meta-env.fs lies below and throws nothing.
  - `lf-view-fvar` in lctx-views.fs is right.
  - `lf-local-depends-on?` in goals.fs is acceptable (it uses `lf-fvar-let?` and `lf-fvar-value`).
  - `lf-tac-quoted.` in tactic-msg.fs is right.
- **Plug-ins:** each holds only its registration, codes, record and run word.

## Re-entrancy (step 4a)
- **New state:**
  - `mti-cells` is a `context-slab:`, one per checker context.
  - `mti-k` is a field of the per-call `mti` frame (context slab).
  - `ap-named` is a field of the existing `ap` context-record, written at each `lf-goal-apply*` entry. It is read when 380 is printed: `lf-tac-detail` prints at once, so a later apply cannot change it.
  - `tle-nth` and `tri-nth` are `lf-nth-constructor:` records written only while loading, by `create , , , ,`, and read-only afterwards.
  - `lf-tactic:` and `lfa-code:` registrations are written while loading.
  - No VARIABLE or VALUE is added in src/. The test helper's `tt-text` is test-only.
- **`lf-with-cells`'s rule** ("nothing else claims on that slab while xt runs") is kept.
  - The only claimant of `mti-cells` is `lf-goal-intros`.
  - Its xt reaches `lf-goal-intro-n`, which claims only on `mti-frames`.
  - Nothing under it calls `lf-goal-intros`.
- **Claim failure:** a failed claim (`lf-must` in `mm-cells`) throws before CATCH. The saved count on the return stack is discarded by THROW, and nothing was claimed.

## Kind numbers (registry)
- Kinds 1-11 (fixed) and 12-13 (apply, assumption) are unchanged.
- The registered kinds now sort as clear 14, constructor 15 (was 14), exfalso 16, intros 17, left 18, right 19.
- No saved format stores kind numbers:
  - schemas/tactic-steps-1.schema.json and every steps.golden store `tactic` and `word` names;
  - TACTIC_PLUGINS.md 3.1 says the structural checks read flags, not kind numbers;
  - the "kind 16-18" in other docs are snapshot section kinds.
- So the shift breaks no stored data.

## Forth style
`forth-metrics.py --words 10`:

| Measure | 11 existing files, base | Same files, head | + 5 plug-ins |
| --- | --- | --- | --- |
| Words | 642 | 686 | 8 |
| 1-2 lines | 70% | 72% | 100% |
| 3-5 lines | 29% | 27% | 0 |
| Over 5 lines | 0 | 0 | 0 |
| Globals | 0 | 0 | 7 |
| Locals | 0 | 0 | 0 |
| Deep shuffles | 20 | 22 | 0 |
| Return-stack ops | 85 | 84 | 0 |
| Long lines | 0 | 0 | 0 |

- The 7 plug-in globals are 5 `lf-tactic:` words and 2 `lf-nth-constructor:` records.
- **Baseline raises:**
  - **The plug-ins' globals 1-2 are accepted.** They are load-time registration words and constant records, never written after loading. tactics/constructor.fs already has 1.
  - **goal.fs shuffles 2 → 3 is accepted.** The new shuffle is `mti-intros`'s `2swap`. `0 0 rot dup mti-cells ['] lf-goal-intro-n lf-with-cells` inside `lf-goal-intros` would drop `mti-intros` but still needs one shuffle (`rot`). The return-stack form only moves the cost.
- **Style findings:** B1, B2 and L5 (factorings above).
- **The rest are well factored:**
  - every word is five lines or shorter, with accurate stack comments;
  - `lf-nth-constructor:` uses `begin-structure`, so there are no raw offsets;
  - `lf-tac-ex` names the repeated throwTacticEx exit and replaces 4 copies;
  - `lf-goals1` and `lf-lift-meta-tactic1` replace 3 hand-written `[g]`;
  - each module requires what it uses: meta-must.fs adds input, constant-term-boundary and meta-env; goal.fs adds find.fs and meta-spine.fs; tactic-core.fs adds meta-spine and meta-config.
- **Portability:** Forth-2012 only (begin-structure, field:, 2>r, abort", s\"). No new Gforth dependency.

## What I ran
On `git archive` copies of 70c32327 (and of b80169d3 for the metrics), with Gforth 1.0.0, `ulimit -u 500` and stdin `/dev/null`:

- **Unit tests on Gforth 1.0.0:** tests/front/tactics/{clear,exfalso,intros,left,right}/test.fs all pass, 0.6-0.7 s each.
- **17 planted faults** (`scratchpad/tb1-scripts/faults.py`, `faults2.py`), each run against the relevant unit tests:
  - **Caught (12):**
    - r1, intros-size not counting lets: intros;
    - r2, instance accepted: intros and tactic-basic;
    - r3, clear names the newest dependent: clear;
    - r6, count check `>=`: left and right;
    - r7, nth uses the named apply: left;
    - r9, `lf-with-cells` not cut: intros and tactic-lib;
    - r10, node kind always explicit: intros and tactic-basic;
    - r12, clear's target test before the locals: clear;
    - r13, matchConstInduct throws on an unknown name: tactic-lib;
    - r14, the bound check dropped: left;
    - r16, the quote not closed: clear and tactic-lib;
    - r17, a let's value ignored: clear and goals.
  - **Survived (5):**
    - r4 and r15 (L1);
    - r5 (L2);
    - r11 (M1);
    - r8 (= the implementer's `tb1-get-fvar-postponing`), which B3's test catches once added (run).
- **The B1 fix:** intros/test.fs passes with it.
- **`bin/leanforth check`** on the S2 slice (`--env tests/front/s2-slice.ndjson --elab-data tests/front/s2-slice.elab.ndjson`) with 12 probes:
  - p2 (442 with a metavariable), p3 (386), p4 (exfalso on False, accepted), p6, p7 (right then rfl, accepted), p8 (441), p9, p10, p16 (389 texts);
  - p1 and p5, refused at parse (59);
  - p15, which was mis-built and so tells nothing;
  - p9 and p15 were also run under r8 and r11.
- **Pinned Lean 4.35.0**, the binary run directly, on probes.lean: p2, p3, p4, p8-p14, with `#print` of p4, p13 and p14.
- **Scripts:** forth-metrics (head and base), check-duplicates and check-lib-callers.

Not run:
- the implementer's suites, any make target, `make cover-changed` and the tactic check.py runs;
- gforth-fast and Gforth 0.7.3;
- the `--lean` twins (the implementer's records 2-10);
- Init and Mathlib.

This AI review does not replace the human review AGENTS.md requires.

## Fixes
(To be filled in by the fixing commit.)

## Fixes (2026-11-19, commit 323a29e1)

- **B1: fixed.** `lf-intros-size` uses `lf-meta-under`; `mti-inner` deleted.
- **B2: fixed.** `lf-mctx-fvar ( k -- fvar )` in mvars.fs replaces the phrase in goal.fs (two places), elab-term.fs, assumption.fs (`mas-fvar` deleted) and assign-check.fs.
- **B3: fixed.** clear/test.fs prints `@id Nat 0`; the fault `tb1-get-fvar-postponing` is caught and no longer listed as equivalent.
- **L1: fixed** (the assigned-goal test uses the goal's own variable). **L6: fixed** for `mnc-bounded` (`u<`).
- **M1, L2, L3, L4, L5 and L6's comment: planned** as plan 9.4.8l (AN).
- Found by the tier: the older fault `lib-intro1-kinds-ignored` survived once intro-n read a node's own kind; tactic-basic.fs now tests a node whose own kind is explicit, and it is caught.

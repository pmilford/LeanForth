# Design review: simp (TACTIC_SIMP.md, first version), 2026-11-24

Independent reviewer (Opus, not the author), against DESIGN_STAGE_REVIEW.md, from Lean 4.35.0's source and five probes on pinned Lean (the probe files were in a scratch folder and are not kept). Every must-change and should-change item is applied in the second version of the design, [TACTIC_SIMP.md](../../design/TACTIC_SIMP.md) ("Changes after review"); the first slice there is the author's own count of 2,300 lines with a cut line at 1,600, where this review estimated about 1,400 to 2,000.

I reviewed this independently against DESIGN_STAGE_REVIEW.md; I am not the author. I read Lean 4.35.0's source and ran five probes on pinned Lean: /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/review-simp/r1.lean to r5.lean. I wrote nothing in the repository and ran no make, no tests and no agents.

**Verdict: approve with changes.** The layering, the order (simp only → default set → wrappers) and the proof-shape claims hold. But SL1a as written cannot match Lean. It is missing:
- the root-only keys that bracket terms and hypotheses use;
- `dsimp`;
- Lean's switchable whnfCore settings;
- the congruence-kind computation.

All four are needed by the first application simp visits. With them, SL1a grows to about 2,000 lines. Two more gaps (items 5 and 6) would make LeanForth accept a proof Lean rejects, or leave a different goal.

**Must change**
1. **Keys of bracket terms and hypotheses index only the head.**
   - Global constants get full keys (`noIndexAtArgs := false`, SimpTheorems.lean:470, :473). Hypotheses and non-constant terms get the head only (`:= true`, :502, :509; DiscrTree/Main.lean:258-265).
   - Probe r1 a1: `h : f 6 = 0`, `simp only [h]` proves `f (2 * 3) = 0` as `of_eq_true (Eq.trans (congrFun' (congrArg Eq h) 0) (eq_self 0))`. No simproc ran: r2 a1e shows the goal still `p (2 * 3)`.
   - The design never mentions this flag. Change: `lf-dt-path` takes the flag, and every origin uses Lean's choice. Add a wrong twin (a goal only head-only keys close) and a fault.
2. **dsimp is needed from SL1a, not SL4.**
   - simpAppUsingCongr, congrArgs and tryAutoCongrTheorem? call `dsimp` on every argument with forward dependencies, which includes every type argument (Types.lean:757-764, :668-677, :831).
   - Probe r4 o6: with `x : Fin (n+0)`, `simp only [Nat.add_zero]` turns `p (n + 0) x` into `p n x`, and the term is `id hp`.
   - Change: port dsimpImpl (Main.lean:469-530) and Meta.transform by SL1b. In SL1a, answer unsupported when such an argument holds a redex or a node a rfl lemma could rewrite; term-find.fs:61 `lf-term-holds-node?` can do the scan.
   - Reuse note: S3 built no transform (decide.fs:58-63 refuses lets). dag-walk.fs (176 lines; delta.fs's Core.transform) is a base, but it does not open binders as Meta.transform does.
3. **Lean's whnfCore settings are missing below simp.** Simp runs with three settings:
   - simpGlobalConfig for lemma keys: iota off, proj `.no`, zetaDelta off (SimpTheorems.lean:282);
   - mkIndexConfig for term keys: proj `.no` (Types.lean:141);
   - mkMetaConfig for unification: proj `.yesWithDelta`, zetaDelta from the config, off by default (:162).

   whnf.fs only runs Lean's defaults (whnf.fs:4-5), and meta-config.fs holds only the defeq flags and transparency (:7-30, :82-86). Change: add iota, proj kind, zeta, zetaDelta and beta to meta-config.fs, honour them in whnf.fs, defeq.fs and discr-keys.fs, and list it under "missing below simp" (about 200-350 lines). These are the most shared Meta files: SL1a must claim them.
4. **SL1a must compute the congruence kinds.** congrDefault tries the automatic congruence theorem first on every application (Main.lean:545-549). The plain builders are used only when getCongrSimpKinds gives fixed/eq everywhere (CongrTheorems.lean:178-212: result dependencies, Prop→cast, instance→subsingletonInst or fixed, class subobject mask, fixKindsForDependencies; plus isMatcher and the congrCache). Move `lf-congr-simp-kinds` from SL2b to SL1a. SL1a's refusal of `@[congr]` heads also needs SD's congruence records.
5. **A bracket hypothesis rewrites itself.**
   - Bracket terms get origin `.stx` (Elab/Tactic/Simp.lean:363, :370). simpGoal erases only `.fvar h` (Main.lean:884), which only `[*]` adds (:400-401).
   - Probe r5 x3: `simp only [h] at h h2; exact h` leaves `h : True`, and Lean refuses with a type mismatch. If LeanForth erased h, it would accept.
   - Change: port the origins exactly. Add wrong twin `w-at-self` and a fault.
6. **`lf-goal-change-local-decl` is not Lean's replaceLocalDeclDefEq.**
   - assert.fs:189-211 is changeLocalDecl: revert, defeq check, replaceTargetDefEq. That adds an `id` hint and a beta-redex to the term, and refuses a hypothesis others depend on.
   - Lean's replaceLocalDeclDefEq (Meta/Tactic/Replace.lean:110) changes the type in place after an `Expr.equal` test, works with dependents and leaves no node. simp's "no progress" check relies on that test returning the same goal (Main.lean:908).
   - Change: a new word in SL1b, with tests.
7. **State the helper-name rule exactly.** Names come from DeclNameGenerator.mkUniqueName (CoreM.lean:95-147):
   - A theorem's proof runs in an async child, giving `THM._simp_1_k`. A def gives `NAME._simp_k` (probe r3: `d2._simp_1`). An example keeps none. A name already taken is skipped.
   - Every bracket lemma that needs preprocessing gets its helper when the list is read, used or not. Probe r2 v1: `_simp_1_2` was made for the unused `Nat.add_eq_zero_iff`, so the used one is `_simp_1_3`. Nested `have` blocks share the counter and the cache (settled, r2 v1).
   - The helper's rfl flag follows `inferRfl := true` and `defeq := inv && tag` (SimpTheorems.lean:465-469).
   - Add fault `helper-only-when-used` and a def twin.
8. **On-demand constants Lean already has.**
   - `Decidable.decide.congr_simp` comes from Init.SimpLemmas (probe r3). Init's .olean files hold 256 `.congr_simp` and 7,537 `._simp_` constants, so Lean's user file declares none of these.
   - The design's "else build it and hand it to the kernel before the theorem under that name" would declare a constant Lean imports, and the helper-for-helper comparison would differ. SL2b's own acceptance example is this case.
   - Change: SD/EX list the realized constants of the library (name and statement). LeanForth builds and checks those as library constants, and declares only what Lean realizes in the user's file. The simp-slice export must cover them.
9. **The rfl flag of the user's own theorems.** Probe r5: `theorem myrfl … := rfl` used by simp leaves no proof step; `:= (rfl)` gives the step `myrfl2 n`. The flag is set at declaration time (inferDefEqAttr, DefEqAttrib.lean:159: the syntactic `:= rfl` plus a check at instances transparency). The design only says "`defeq` tag, data". Change: port the rule for the LeanForth spelling that matches Lean's `:= rfl`, else answer unsupported when simp uses a lemma from the user's own file.

**Should change**
- **Builder shortcuts.** Spell out AppBuilder's shortcuts for `lf-mk-of-eq-true`, `-eq-true` and `-eq-false` (AppBuilder.lean:630-660). Probe r5 x1: `simp only [h]` proving `p` from `h : p` is just `h`. Probe x2: `simp only []` on `True` closes with `True.intro`, with no "no progress" error. Test both.
- **Section 3, "Trying a lemma".** rewrite? calls tryTheoremWithExtraArgs? with the tree's extra-argument count (Rewrite.lean:178-185, :234). The retry belongs to tryTheorem? (:187-202), which other callers use. Also add resolveBinderNameHint (Rewrite.lean:152; Main.lean:600).
- **Limits.** The step check is a strict `>` before the increment, and a cache hit comes first (Main.lean:679-686; probe u3/u4 settle exact counting). Lean raises the depth twice per visit (:677, :714). Question 4 should say so.
- **Simp list items are not plain terms.** Items resolve through elabSimpArgs (Elab/Tactic/Simp.lean:336-370, :488): simprocs, simp sets and definitions to unfold. `Nat.reduceMul` is in Lean's package, not in an Init export, so `' Nat.reduceMul` as a plain term is error 1. This matters from SL3a on.
- **Sizes.**
  - The basis ratio of 1.6 is below rewrite.fs's measured 2.1.
  - With items 1-4, SL1a is about 2,000 lines and 2.0-2.4M tokens.
  - History (first slice under-estimated by 25%; slices opening a library layer ran over their ceiling twice) puts the total nearer 16-19M than 13-15.5M.
- **Value per token.** Init has only 17 `simp only` one-liners against 898 `simp`/`simp [..]`. Measure what those 898 need (binders, conditions, perm, congruence) and cut SL1b-SL2b to that, so SL3a comes earlier.
- **Small fixes.** `abm-deeper` is at app-builder.fs:309, not :224-226. Correct the 300-339 range written at SIMP_DATA.md:229.

**Owner's questions (6)**
- Mostly complete and plain. Missing: the shared Meta settings layer (item 3, a cross-cutting change worth telling the owner), and the def/theorem helper-name rule.
- `-'` is a tick-like word that takes the next name, like `'` and `by-have: h`. That is acceptable, and no Lean name can collide with it.
- `'*` is fine.
- `pre` is a valid Lean name. Once reserved, name lists refuse it (tactic-syntax.fs:331-338), so a hypothesis called `pre` could no longer appear in `at[ ]`, `by-intro[ ]` or `by-clear[ ]`. Propose a token no Lean name can be, for example `' foo !pre`. It stays postfix like `<-`.
- `' h by-simpa-using` and a trailing `config[ ]` follow the rules. Say that Lean writes options first.
- `by-simp[ ]` must use the rules shape, not `tac-shape-list+`, which refuses an empty list (460). Lean accepts `simp []`.
- Error codes 500-539 are free. No `N constant lfa-e-*` at 310 or above exists on main or the 25 most recent branches; errors.fs:56 says "310- free", and TACTIC_BLOCKS uses 468.

**Claims I verified**
- **No simprocs under `simp only`:** true (Elab/Tactic/Simp.lean:568; r2 a1e).
- **A rfl lemma leaves no proof step:** true for tagged lemmas (Rewrite.lean:109-123; r5 u1).
- **Rule order:**
  - The star branch is tried before the key, whatever the bracket order (r4 o1/o2 both use `gs`).
  - Lemmas at the same leaf are tried in bracket order (r1 n1-n4).
  - A stable priority sort follows (Rewrite.lean:220).
  - A hypothesis, with head-only keys, wins over a full-keyed global lemma (r4 o4).
- **Proof shapes:**
  - inside an argument: nested `congrArg`, then `congrFun'` (r1 a2);
  - under binders: `funext`, `implies_congr`, `forall_congr` (a3, a3b, a3c);
  - `at h`: `Eq.mp (congrFun' ..) h` (a4);
  - a hypothesis that becomes False: `False.elim (Eq.mp ..)` (a5);
  - `at *` on non-dependent Prop hypotheses (Elab/Tactic/Simp.lean:769; a6, the goal by `Eq.mpr (id (congr ..))`);
  - a hypothesis that becomes True is kept as `h : True` (o9);
  - no progress at h is an error (o7);
  - `ite_congr` is used with `fun a => h` (r2 c2).
- **Named words exist:** lf-meta-defeq, lf-meta-whnf-r, lf-meta-eqv (alpha-equivalence, binder names and info ignored, as Lean's `==`), lf-commit-when, lf-dtree-insert, lf-dt-path, lf-forall-meta-telescope-reducing, lf-mk-congr-arg (with Lean's fusion of nested congrArg), lf-goal-replace-target-eq, lf-with-location, lf-handover, tac-shape-rules (tactic-syntax.fs:357).
- **Proposed new words are new:** getMatch (discr-tree.fs has only getUnify), lf-mk-congr, -congr-fun, -of-eq-true, -prop-ext, -funext, a transform, and fun-info's dependency fields.
- **Files:** no unmerged local branch touches the files SL1a claims.
- **The `simp-data-tool` branch:** 847 commits behind main. Main has since changed export_elab.py (+192 lines) and export_elab.lean (+40). The tool writes keys, simprocs and congruence lemmas but no realized constants (item 8).

**Recommended first slice instead of SD → SL1a**
1. **SD-a** (about 350 lines): the reader for the congruence records and the defeq tags only.
2. **SL1a'** (about 1,400 lines): the Meta settings, head-only keys, getMatchWithExtra, the simp loop, the congruence kinds, the dsimp-unchanged guard, the target words, and `at[ h ]` with replaceLocalDeclDefEq. Command: `by-simp-only[ ' h ]` and `[ ' Nat.add_zero ]` on first-order goals and hypotheses, beside twins.
3. Run the rest of SD in parallel before SL3a.

A core of about 1,000 lines with congrArg/congrFun/congr only is not faithful once items 1-4 are counted.

**Not checked**
- Slices SL3-SL6: simprocs, arith, ground, `simp?`, simpa, simp_all, dsimp details.
- Mathlib and appendix counts.
- Which `_simp_`/`congr_simp` constants LeanForth's own export holds (I counted Init's .olean files only).
- The author's probes p1-p3, beyond re-deriving similar cases.
- `withLoopChecking`, `+locals`, appendix E's values.
- The token-history files.

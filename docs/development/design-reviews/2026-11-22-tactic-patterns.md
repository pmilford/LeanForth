# Design review: case patterns (TACTIC_PATTERNS.md, first version), 2026-11-22

Independent reviewer (Opus, not the author), against DESIGN_STAGE_REVIEW.md, from Lean's source and six probes on pinned Lean 4.35.0. Every must-change and should-change item is applied in the second version of the design, [TACTIC_PATTERNS.md](../../design/TACTIC_PATTERNS.md) ("Changes after review"), with one correction by the author: Lean's `(a | b) | c` is not `a | b | c`, and is written `<< a | b >> | c`. The probe files were in a scratch folder and are not kept.

I was the independent reviewer and not the author, and I used the DESIGN_STAGE_REVIEW.md checklist. I read Lean 4.35.0's source and ran six small probes on pinned Lean. The probes are in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/review-patterns/p1.lean to p6.lean. No make, no tests, and nothing written in the repository.

**Verdict: approve with changes.** The central claim holds: rcases/obtain cannot reuse by-induction's eliminator. Probe p6 shows the two terms differ. obtain gives `And.casesOn h fun hp hq => hq`. cases gives `And.casesOn (motive := fun t => h = t → q) h (fun hp hq h => hq) (Eq.refl h)`. Elab cases always adds target equations (Elab/Tactic/Induction.lean:1117, :1130). Four things must change before code: one tag rule, one name rule, one spelling clash and one grammar rule. Without them LeanForth would accept text that Lean rejects.

**Must change**
1. **Goal tags for one-constructor types.** Meta induction keeps the parent's tag when there is one minor premise (Meta/Tactic/Induction.lean:84). Section 3 says the tags include `intro`, which is wrong. Probe p1: `obtain ⟨hp, hq⟩ := h` then `case intro => …` gets Lean's "Case tag `intro` not found". With an `intro` tag, `by-case: intro =>` would be accepted where Lean rejects it. Fix the text and add a wrong twin. Probe p4 confirms nested tags: `inl.inl`, `inl.inr`, `inr.inl`, `inr.inr`.
2. **Hidden names must stay hidden after revert and re-intro.**
   - Lean keeps a reverted local's name exactly as it was, so an inaccessible one stays inaccessible. Probe p1: `intro x h _; subst h; exact hx` gets "Unknown identifier `hx`".
   - LeanForth keeps inaccessibility as a flag on the local (lctx-views.fs:87). A reverted binder stores only the name and binder kind (telescope.fs:201).
   - The planned `lf-goal-intro-np` ("names kept accessible", section 3; "five-line change", section 7) would therefore make `' hx by-exact` pass where Lean fails.
   - Change: carry the flag through revert for every re-intro that keeps names. That covers substCore's re-intro of the rest, Meta induction's re-intro of the major and extras, generalizeIndices, and heqToEq's and substReduced's assert-then-intro. Also, an anonymous binder still gets a fresh inaccessible `a` under introNP (Intro.lean:116). Add one wrong twin per path.
3. **`(` is a comment in the reader E2 plans to reuse.**
   - Batch 3c's `lfa-token-on` skips `( … )` "as Forth's own words do" (tb2-batch3c src/author/runner.fs:53, :208-215), and a Forth reader also sees a comment.
   - So `by-rcases[ ( a | b ) c ]` would silently drop the group. Grouping is needed on at least 1,899 Mathlib lines with parenthesized alternatives, plus 864 with typed patterns.
   - Change: the pattern reader takes `(` as a token, or another group spelling is chosen. Either way, put it to the owner in question 3; the "bar only inside parentheses" alternative has the same problem.
4. **rintro's grammar is not rcases's.**
   - In Lean, each rintro item is a single pattern with no bare bar, or a group `( p1 p2 … (: T)? )` (Init/RCases.lean:93-98, :194).
   - Probe p3: `rintro a | b` is a parse error ("unexpected token '|'"). Probe p4: `rintro (x y) -` is accepted.
   - The design's single grammar (section 2) accepts `by-rintro[ a | b c ]` and refuses `by-rintro[ ( x y ) ]`.
   - Change: two top levels. rcases, obtain and by-contra take alternatives; rintro takes items only, plus its group. Add a planted fault and a wrong twin.
5. **Two substitution paths are missing.**
   - `subst x` on a let variable succeeds in Lean: evalSubst unfolds the let (BuiltinTactic.lean:503-513). The let-declaration error at Subst.lean:148 is only reached through Meta substVar, and subst_vars catches it there.
   - Change: port the let branch or answer 99, and drop that error from appendix B. Today's revert.fs refuses lets, so 99 is the honest first answer.
   - substEq has a reduced-side path (Subst.lean:181-196). When whnf changes the side, Lean asserts the reduced equation, re-introduces it, clears the old one, then substitutes. That builds a different term. Add it, a test (e.g. `h : n = id m`) and a fault.
6. **Nat under rcases, and which export the tests use.**
   - `Nat.casesAuxOn` is a plain definition (Init/Data/Nat/Basic.lean:49), not a casesOn. Lean derives its recursor info from its type, taking the major premise as the motive's last argument (RecursorInfo.lean:105-110). The planned `lf-cases-on-info`, "from the inductive's data", does not cover it.
   - rcases picks casesAuxOn only when the environment has it (Cases.lean:270). s2-slice.ndjson lacks it; decide-slice has it.
   - Change: derive the info from the declaration's type, or from `lf-elim-info`'s positions.
   - Name the export each batch runs on. It must hold Nat.casesAuxOn, Nat.Internal.elimOffset, per-constructor `C.noConfusion`, `T.ctorIdx` and `noConfusion_of_Nat`. Probe p1 shows all are Init declarations; `Or.ctorIdx` does not exist.

**Should change**
- **Reconcile with the blocks design.** TACTIC_BLOCKS.md:111 says `lft-w-bar` asks an open pattern bracket; this design says the bar never reaches it. Write one rule in both. Tell the owner that inside a bracket a bar at a line's start is a pattern bar, an exception to the blocks rule.
- **Work in flight is understated.**
  - Batch 3c's list reader stops at reserved words (tb2-batch3c tactic-syntax.fs:319-321), so `|`, `-`, `<<` and `>>` must become items of the pattern list.
  - That change and the `tac-shape-new` export both edit tactic-syntax.fs, the file batch 3c and blocks slice 1 also change.
  - Batch 3c changes 19 source files (author/runner.fs, scopes.fs, elab-term.fs and others), not one.
- **Typed tuple elements.** `⟨k, hk : n = k + 1⟩` is valid Lean (probe p4). "Delete the commas" fails there because a postfix term has no end inside a tuple. Question 4 should say typed elements need a group bracket.
- **Say the reader needs no lookahead.** A bar sets a join flag, the next item joins the current element, and a closer with the flag set is an error. That keeps it a plain Forth loop.
- **Reuse words not named in the design:**
  - `lf-commit-when` (meta-must.fs:42), for observing?/commitWhen in unifyEq?, rule 6 and tryClear.
  - `lf-goal-exfalso` (goal.fs:195), which rule 6 calls first.
  - `lf-mk-app-m` (app-builder.fs:301).
  - `lf-meta-fun-info` (fun-info.fs:205), for processConstructor's getFunInfo.
  - `lf-meta-offset` and `lf-meta-ctor-if-lit` (nat-offset.fs:236, :256).
  - The level normalizer, for the motive's universe.
  - E4 also replaces whnf.fs:749 `wc-ctor-app?`, not only `mcd-ctor?`.
- **Wrong line references.** `lf-goal-intro-n` is at goal.fs:294 (not :48), `lf-goal-revert` at revert.fs:101 (not :7), `lf-mk-eq` and its neighbours at app-builder.fs:163-166 (not :13-16), and `mcd-ctors` at :123.
- **Consumers table is missing** (checklist item). Meta cases, subst and FVarSubst also serve contradiction rules 4 and 6, `intro ⟨a, b⟩` through match (FE7), `induction … generalizing`, `injections`, `subst_eqs` and `split`. Mathlib's `ext ⟨a, b⟩` takes rintro patterns.
- **subst_vars order.** It tries every local in context order: a variable through substVar's equation search (right side first), an equation through substEq (Subst.lean:282-292). Pin this with a test where the variable comes before its equation.
- **No-confusion must look only at Lean's declarations.** It should never see ctor-idx.fs's builder, which makes ctorIdx for twelve types Lean has none for. This reaches few texts.
- **Token estimates are too low.**
  - The figures should rest on measured batch totals: 1.13-1.53M each (implementer 600-940k, review 110-204k, fix round 290-400k, checks about 100k; .claude/work/COSTS.md rows 80-106).
  - Expect 1.2-1.6M per slice, about 5-6M for E1-E4, not 2.4M.

**Claims settled**
- **Meta induction's names and tags:** finalize reads Lean's `introN` with names and `useNamesForExplicitOnly := !explicit`, then `introNP` for the extras, after a try-clear of the major (Induction.lean:84-111). Tags are parent plus constructor name, or the parent alone with one minor premise.
- **RecursorInfo** is computed generically from the declaration's type (RecursorInfo.lean:186-226).
- **Declarations in Init:** Nat.casesAuxOn, Nat.ctorIdx, Nat.succ.noConfusion, noConfusion_of_Nat and Nat.Internal.elimOffset all exist (probe p1). Or has no ctorIdx because it is a Prop.
- **Generalize:** about 45 Lean lines (Generalize.lean:28-76). It uses instances transparency and ends in an `isTypeCorrect` check. A target that is already a free variable makes an empty generalize call, which leaves no trace in the term.
- **`rcases h with a b`** is a parse error (probe p2: "unexpected identifier").
- **introNP's names:** keeps binder names, but needs the flag (finding 2), so it is not a five-line change.
- **`throwNestedTacticEx` text:** "Tactic `cases` failed with a nested error:" followed by the inner message (Meta/Tactic/Util.lean:55-57).
- **Goal order is depth first** (probe p4).
- **Which side `rfl` eliminates:** the right-side variable (p4: `n = m` eliminates m).
- **unifyEq? order and mkNoConfusion's argument order** match the design.
- **Bar tighter than space is unambiguous** for names, `_`, `-`, `rfl`, tuples, nested alternatives and `@` as a one-item prefix. Each Lean alternative is a single item (Init/RCases.lean:68), so the rule is Lean's own grammar with commas as spaces. It breaks only for typed elements and rintro's top level, as above.

**Recommended first slice (different from the design's)**
- **E1:**
  - The Meta split on non-indexed types: FVarSubst, ordered revert, re-intro keeping names with the flag, recursor info, finalize.
  - `generalize`.
  - `by-obtain[ ]` and `by-rcases[ ]` with names, `_`, `-`, tuples, alternatives and Nat (shown as `0` and `n + 1`); `rfl` answers 99.
  - Contradiction rule 6 as a second caller.
- **E2:** subst and subst_vars, `rfl` patterns, rintro, `by-contra[ ]`.
- **Why:**
  - The Meta split lands with its real caller, as the owner's library-with-caller rule asks. The design's E1 gives it only rule 6.
  - The riskiest term shape is tested on the tactics with about 27,600 Mathlib lines rather than subst's 1,200.
  - The terms still equal Lean's node for node. The simple case (Cases.lean:290-293) adds no equations and no subst (probe p6, t1 and t3).
  - Indexed families look rare: the empty pattern `⟨⟩` appears in 256 of 30,365 obtain/rcases/rintro lines. That is a proxy only; the real share is not measured.
- **Size:** about 850 lines, so it needs a cut line (rule 6 moves to E2).

**Not checked**
- The size of the ported Meta split, and whether LeanForth's instantiateMVars beta-reduces `?r i m extras` to `T.casesOn … extras` as Lean's does.
- acyclic, and Quot under rcases.
- The indexed share of Mathlib uses.
- The step-log goldens.
- Gforth handling of `⟨` and `⟩` as tokens.
- The design's appendix A Mathlib counts, which I did not re-run.

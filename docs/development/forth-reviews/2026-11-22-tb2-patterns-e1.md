FORTH REVIEW: tb2-patterns-e1

Range: 87cb49a2..d27109fc (worktree /home/peter/code/LeanForth/.claude/worktrees/agent-a61d2f1f159794cd9). Findings: 13 (7 blocking, 6 non-blocking).

**Verdict: merge after fixes.** It cannot merge now, for three reasons:
- LeanForth accepts proofs that Lean rejects (finding 1).
- Valid Lean input crashes it (finding 2).
- `make cover-changed` fails (58 blocks) and `check-duplicates.py` fails.

AI review does not replace the owner's required human review.

## What I ran (Gforth 1.0.0 and pinned Lean 4.35.0, absolute paths, no `.tools` link)
- `make cover-changed BASE=87cb49a2` once (65 s): 58 never-run blocks, the same as the implementer's count.
- `scripts/forth-metrics.py --words 10` on the 9 new and changed files.
- `scripts/check-duplicates.py`: it fails on one new group.
- `scripts/check-lib-callers.py`: passes.
- 25 `.lf` probes with `bin/leanforth check` on decide-slice, and the same texts on pinned Lean (`probes*.lean` under `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/review-e1/`).
- 7 faults I planted, in a copy of src/tests: batch-g `test.fs` each time, `check.py` for one of them.
- `test.fs` and `check.py` unfaulted in the copy: both pass.

I did not run `make tier`, gforth-fast, Gforth 0.7.3 or `check.py --lean`.

## Findings

**1. BLOCKING. A cleared statement variable is accepted by `by-rcases[` and `by-obtain[`; Lean says "Unknown identifier".**
- Where: `src/front/rcases.fs:279-283` (`rcs-target`, `rcs-run`). The cause is older (a theorem binder `' h` resolves to its free variable even when the goal no longer holds it), but this branch makes clearing routine: every obtain clears its scrutinee.
- Reproduce: probe p01, `' h by-obtain[ << hab hba >> ]  ' h by-rcases[ x ]  ' hba by-exact`.
  - LeanForth: "p01: accepted".
  - Lean: `Unknown identifier h`.
- Probe p19 (`obtain _ := h; obtain x := h`) gives the same result.
- The documented "a cleared statement variable 98" holds only for tactics that check the assignment (exact). A name or `_` pattern does nothing, so nothing catches the stale variable. Pattern names are checked: p04 gives 76 and p14 gives 1.
- Fix:
  - Resolve a statement variable against the current goal's context: not present gives the unknown-name refusal, as pattern names already get.
  - At minimum, `rcs-target` refuses a free variable missing from `lf-mctx-view`.
  - Add wrong twin `w-stale-target.lf` (p01 and p19 bodies) and a planted fault that removes the check.
  - Correct the "each refused, never accepted" sentence in LANGUAGE_REFERENCE.md D.8 and the TACTIC_STATUS row.

**2. BLOCKING. Crash (THROW -9, invalid memory address) when a constructor has two or more fields more than the tuple has patterns.**
- Reproduce: probes p11 and p21, `' h by-obtain[ << >> ]` on `a = b ∧ b = a`. Lean accepts. LeanForth gives "internal fault ... THROW code -9".
- Cause, `rcases.fs:145`: `rcs-left` = len − hk goes to −1, because `rcs-take` moves the cursor past the end (Lean's `tailD []` stays empty).
  - `rcs-last` then makes a rest reference (node, 1) past the tuple's children.
  - `rcs-container`'s `0 1 ?do` (`:128`) wraps around and reads arbitrary memory.
- Fix:
  - `: rcs-left ( -- n ) rcs rcs-h @ rcs-len rcs rcs-hk @ - 0 max ;`
  - Bound the `?do` in `rcs-container` (start ≤ count).
  - Add p11 (`obtain ⟨⟩ := h; assumption`) to obtain.lf with its Lean twin, and a fault. This also covers block `:136`.

**3. BLOCKING. `make cover-changed` fails: 58 blocks.**
- Grouped list at the end of this report.
- test.fs:253 accepts 471 or 136. 471 is never reached there (coverage shows `rcs-not-inductive` never ran), and x-not-inductive.lf's comment "test.fs reaches 471" is false.
- Fix: replace that test with p25, `s" True" s" ' Nat by-rcases[ << x >> ] by-trivial" tactic-ran -> 471`. It prints Lean's exact message, "`x✝ : Type` is not an inductive datatype".

**4. BLOCKING. New duplicate group 59ff7dc0a595: `rcases.fs:236 rcs-sub@` and `:252 rcs-new@`.** `check-duplicates.py` fails, so `make test` fails. Fix with named subgoal accessors (finding 13a), or one word:
```forth
: rcs-quad@ ( addr i k -- x ) rot @ -rot lf-subgoal@ ;
\ callers: rcs rcs-subs i k rcs-quad@   /   rcs rcs-new t k rcs-quad@
```

**5. BLOCKING (reuse). The branch's new general words leave their copies in `src/`.** Replace each in this branch:
- `lf-run+` (`run-push lf-must`):
  - `meta-tactic/assert.fs:187`
  - `new-goals.fs:66`
  - `meta-tactic/revert.fs:127` (a file this branch touched)
  - `meta-tactic/apply.fs:209`
  - `meta-tactic/rewrite.fs:89`
- `lf-run+!`:
  - `revert.fs:89` `mrv-push` becomes `mrv mrv-out lf-run+!`.
  - `meta-tactic/repeat.fs:50` `mrp-onto` becomes `swap lf-run+!`.
  - Inside the branch, `rcases.fs` `rcs-field+`, `rcs-r+` and `rcs-task+` spell `X @ swap lf-run+ X !` out instead of `X lf-run+!`.
- `lf-tac-unported`: 17 copies of `lfa-e-tac-form lf-tac-fail` remain:
  - `elim.fs:193, 198, 230, 232` (touched here)
  - `tactic-core.fs:387, 416, 444`
  - `tactics/intro.fs:22`
  - `have.fs:79, 84`
  - `new-goals.fs:69, 82`
  - `tactic-alts.fs:151`
  - `by-cases.fs:33`
  - `trivial.fs:49`
  - `symm.fs:89`
  - `delta.fs:37, 57`
  - `apply.fs:198`
- `lf-tac-spaced.`: `tactic-core.fs:294` `tcr-inline.` still writes `s"  " lf-pp-emit lf-tac-inline. ['] tcr-blank. ok-and`; it should be `['] tcr-blank. lf-tac-spaced.`.
- Pair read: `rcs-pair@` (`rcases.fs:134`) and `mgz-arg` (`generalize.fs:59`) share `2* … 2dup run@ -rot 1+ run@`. Add to lib/runs.fs, with a test:
  `: run-pair@ ( run k -- x y ) 2* 2dup run@ -rot 1+ run@ ;`

**6. BLOCKING (reuse, design §4 "Copies replaced"). elim.fs's binder walk and casesOn lookup are not shared.**
- `mri-start` (`meta-induction.fs:168`) builds the same `[d n]` head and conclusion as `mel-head` (`elim.fs:209`).
- `mri-at` (`:135`) is `mel-at`'s index arithmetic.
- `mcs-cases-on` (`cases.fs:74`) is `mel-rec`'s casesOn lookup (`elim.fs:174`), with the better lookup word.
- Fix: export the shared words from elim.fs and call them from both files:
```forth
: lf-decl-telescope ( d -- info concl ) ...mel-head's body... ;
: lf-bvar-binder ( n bvar -- k ) lf-term-first@ - 1- ;
: lf-decl-suffix? ( d c-addr u -- d' true | false ) rot lf-menv-name -rot lfa-intern-part lf-menv-find? ;
\ mri-start: lf-decl-telescope mri mri-concl ! mri mri-out ! ; read d, n through lf-rinfo-decl, lf-rinfo-args
```
- mel-rec should use `lf-menv-find?` too, so a lookup that runs out of room is no longer read as "not found".

**7. BLOCKING (reuse, and a refusal read as a negative answer).**
- `contradiction.fs:116` (`lf-menv-find ok-then? 0= if 2drop false exit then`) reads any lookup failure, out of room included, as "not a constructor".
- Effect: rule 4 is skipped. The tactic can then end in Lean's "contradiction failed" (a rejection) where the honest outcome is full or unsupported.
- It cannot make LeanForth accept a false theorem: a skipped rule only removes a way to close the goal, and the kernel checks every term. But inside `by-try` or `by-first` it turns exhaustion into a Lean failure.
- Same pattern: `unfold.fs:137`, `tactics/rewrite.fs:61`, `meta-env.fs:407`.
- Fix: use `lf-menv-find?`, now public in meta-must.fs.

**8. Not blocking (test gap; the fault's "equivalent" reason is wrong).** Fault `fsubst-not-applied` is reachable on any export that holds a predicate which unfolds to an inductive type.
- Probe p27: `obtain ⟨_ | n, c, hc⟩ := h` with `h : Exists (Dvd.dvd 2)`.
  - Lean accepts.
  - LeanForth cannot state it on decide-slice: Dvd is missing, error 1.
- Natural form has no `fun` or `Prop` (error 70), so decide-slice texts cannot reach it, which is why the reason holds there.
- Fix: add Dvd and `Nat.instDvdNat` to the test export (the planned patterns-slice) with this theorem, and drop "equivalent".
- `align-no-skip` is truly equivalent in E1.

**9. Not blocking. `-` has no unit pin.** My fault F4 (`rcs-clear` ignores `-`) passed test.fs; check.py's step golden caught it.
- Fix: in test.fs, after `' h by-obtain[ << - hba >> ]`, check that the goal's view lacks the field. Both `se` texts today only check that the proof succeeds.

**10. Not blocking. No refusal sweep calls a library word directly; every sweep goes through text (test.fs:256-276).** Design §5 asks for one per library word.
- Add `heap-sweep` probes calling each directly: `lf-fsubst-insert`, `-append`, `-erase` and `-apply`; `lf-recursor-info`; `lf-goal-induction`; `lf-goal-cases`; `lf-goal-generalize`; `lf-goal-revert-kept`; `lf-goal-intro-kept` and `-names`.

**11. Not blocking (layering for E2-E5).**
- The Meta words in meta-induction.fs and cases.fs refuse through the tactic runner's `lf-tac-unported` (`lf-tac-fail`, an author-level throw), while revert.fs's `lf-goal-revert-kept` throws `outcome-unsupported lf-must`.
- `lf-commit-when` (`lfm-caught`) re-throws non-Meta codes, so E2's contradiction rule 6 could not observe a cases failure as Lean's `elimEmptyInductive` does.
- Fix: Meta library words throw `outcome-unsupported lf-must`, and the tactic layer maps it to 99.

**12. Not blocking (documentation).**
- LANGUAGE_REFERENCE.md D.8 "Narrower than Lean (each refused, never accepted)" and the TACTIC_STATUS row "a cleared statement variable 98" are false while finding 1 stands.
- x-not-inductive.lf's comment about test.fs is false.
- The code 76 refusal prints "malformed elaboration: a term that is no node…", which does not tell the user that the named hypothesis is not in this goal (Lean: Unknown identifier).
- The translation table, the `( a | b )`-is-a-comment statement and the three-forms examples are accurate.

**13. Not blocking (style; see the style section).**

## The 58 blocks: test it thus, or unreachable because

**cases.fs**
- `:70` mcs-has: test with a small export holding an inductive and its casesOn but no HEq. If tests/front has none, a crafted export is needed.
- `:71` mcs-data: probably unreachable, because `lf-match-const-induct` is true only for kind inductive, whose data is always decoded. Confirm in meta-env.fs, then record it as `unreachable:`.
- `:75-76` mcs-cases-on: test with a hypothesis of an inductive whose casesOn the slice lacks (list them with a script); expect 99.
- `:77` mcs-arity: unreachable. A free variable's type is a type, so through whnf it is I applied to all its parameters and indices.
- `:87` mcs-recursor fallback: test `lf-goal-cases` with nat-aux? true on s2-slice (no Nat.casesAuxOn); expect Nat.casesOn goals.

**generalize.fs**
- `:71-72`: with a : Nat and h : a = a, goal `@Eq (a = a) h (Eq.refl a)`, generalize `a`; expect `thrown-unsupported` (Lean: "result is not type correct").

**meta-induction.fs**
- `:140`: `s" False.elim" decl info-code -> 99` (conclusion a bare bound variable; `cast` or `id` would do too).
- `:144-145`: `s" Eq.ndrec" decl info-code -> 99` (the major's type is a bound variable).
- `:149`: `Nat.strongRecOn` if the slice has it (the major comes before the motive: 1 parameter, Nat has 0 arguments).
- `:146-147, :154, :156, :163-164`: Lean's "invalid user defined recursor" checks. Test with Init declarations of each shape: a parameter that is not I's leading argument; a motive into `Sort (u+1)`; a level parameter that is neither the motive's nor I's. Otherwise use a crafted export. They are not unreachable, because `lf-recursor-info` accepts any declaration.
- `:181-182`: `nat lf-target-arity -> 0`.
- `:215`: `lf-goal-induction` on a major of type `¬(a = b)` with And.casesOn; expect 99.
- `:216`: `gi ih s" Or.casesOn" decl 0` with ih : And; expect 99.
- `:217-218`: `ge qe s" Eq.casesOn" decl 0 ' lf-goal-induction code4 -> 99`.
- `:231`: a goal of type `Nat` (Sort 1), h : Exists (Eq a), Exists.casesOn; expect 99 (Lean: "can only eliminate into Prop").
- `:249`: unreachable. The parameters' and the motive's binders were counted from d's own type and stay pis after instantiation and whnfForall.
- `:269`: unreachable from Meta cases: each casesOn or casesAuxOn minor ends in the motive applied, so its arity is fields plus the goal's. Only a user recursor (E5) reaches it.
- `:292`: unreachable. The major's position is one of d's binders before `lf-rinfo-args`, and each is a pi.

**pattern-syntax.fs**
- `:117`: test a text that ends inside the bracket (`' h by-obtain[ x` at end of input); expect 458.

**rcases.fs**
- `:136`: the p11 test of finding 2.
- `:151`: needs a non-indexed constructor with an implicit field. None is known in decide-slice: find one or craft an export. It is not truly unreachable.
- `:190, :208-210, :224, :266`: unreachable in E1. The root is generalized to a free variable, fields are free variables, and E1's substitutions map them only to free variables. A split's major is never pending again, because each target takes one pattern. E2's `rfl` reaches them. Record each as `unreachable:` naming its line.
- `:211-217, :221-222`: the p25 test (finding 3).
- `:218-219` rcs-quot?: the false path is covered by p25. The true path (Quot, 99) stops today at 139 in the elaborator (probe p26), so record it as unreachable until the elaborator handles that term.
- `:234-235, :249-250`: unreachable in E1. Every constructor has one subgoal, in order, so align always finds the entry at the cursor (the same reason that makes `align-no-skip` equivalent). E4 reaches them.

## Probes (LeanForth on decide-slice vs pinned Lean 4.35.0)

| # | Lean text (abridged) | Lean | LeanForth |
|---|---|---|---|
| p01 | obtain ⟨hab,hba⟩ := h; rcases h with x; exact hba | Unknown identifier h | **accepted** (blocking) |
| p19 | obtain …; obtain _ := h; obtain x := h; exact hba | Unknown identifier h | **accepted** (blocking) |
| p02 | rcases h with -; obtain _ := h; sorry | Unknown identifier h | step accepted, NOT PROVED |
| p03 | obtain; then obtain ⟨x,y⟩ := h on the stale h | not run | 93 unsupported |
| p04 | pattern name hab cleared by -, then rcases hab | not run | 76 refused |
| p06 | rcases h with x \| y on (A∨B)∧C | accepts | accepts |
| p07 | rcases h with ⟨x⟩ on Or; case inr => assumption | assumption failed | 381 assumption failed |
| p08 | obtain ⟨⟨w,hw⟩,h2⟩ on ∃∧ | accepts | accepts |
| p09 | obtain ⟨⟩ := h, h : False | accepts | accepts |
| p10 | rcases h with _ \| k on a ≤ b | accepts (sorry) | 99 |
| p11 | obtain ⟨⟩ := h on ∧; assumption | accepts | **internal fault -9** (blocking) |
| p21 | obtain ⟨⟩ := h on ∧; sorry | not run | **internal fault -9** |
| p23 | rcases h with ⟨⟩ on Or | not run | 2 goals inl, inr (sorry) |
| p12 | obtain ⟨h, h2⟩ := h; exact h (shadows the scrutinee) | accepts | accepts |
| p13 | obtain ⟨x, x⟩ := h; exact x (same name twice) | accepts | accepts |
| p14 | obtain ⟨hab,_⟩ := h; exact right | Unknown identifier right | 1 unknown name |
| p15 | case intro after a one-constructor obtain | 210 "Case tag `intro` not found." | 210, same text |
| p16 | ⟨x\|y⟩\|z on (A∨B)∨C; cases inl.inl, inl.inr, inr | accepts | accepts |
| p17 | x\|y\|z on (A∨B)∨C; cases inl, inr | accepts | 99 (inr splits c = a, an Eq) |
| p18 | x\|y\|z on A∨B∨C; cases inl, inr.inl, inr.inr | accepts | accepts |
| p20 | rcases n with _ \| m; rfl; rfl | accepts | accepts |
| p25 | goal True; rcases Nat with ⟨x⟩ | 471 "`x✝ : Type` is not an inductive datatype" | 471, same text |
| p26 | rcases q with ⟨x⟩, q : Quot Nat.le | accepts | 139 unsupported |
| p27 | ⟨_ \| n, c, hc⟩ on Exists (Dvd.dvd 2) | accepts | 1 (Dvd not in decide-slice) |
| p05 | rcases h with -; rcases h with x; rfl on a = b | not run | 97 (my probe was wrong: the goal is not rfl) |

The implementer's two twins with their own codes are refused for the right reason in the sense that the name is not in the goal:
- w-order: 76, a pattern name checked against the context.
- w-clear-used: 98, only because exact checks the assignment. p01 shows tactics without that check accept.

I found no variant of a twin that is accepted, except the stale statement variable.

## Faults I planted (copy of src/tests)

| Fault | Caught? |
|---|---|
| F1: the tag never gets the constructor's name appended | test.fs |
| F2: intro-kept's step loses kinds and the hidden flag | test.fs |
| F3: align loop reversed (drops the one-constructor goal) | test.fs |
| F4: `-` ignored | **not** by test.fs; check.py's step golden |
| F5: a bar first in a list allowed | test.fs |
| F6: `lf-menv-find?` reads every failure as not found | test.fs's heap sweep |
| F7: Meta induction's substitution of the extras dropped | test.fs |

## Reuse (step 3a)
- Searched:
  - FORTH_LIBRARY.md's stacks, runs and outcomes sections, and lib/runs.fs's words.
  - `grep -rn` over `src/` by name and shape: `run-push lf-must`, `X @ swap … X !`, `lfa-e-tac-form lf-tac-fail`, `lf-menv-find ok-then?`, `lf-menv-find dup outcome-invalid`, `2dup run@ -rot 1+ run@`, `lf-term-first@ lf-meta-head-beta lf-must`, `over lf-meta-args# lf-meta-nth-arg`, `s"  " lf-pp-emit lf-tac-inline.`, `lfa-intern-part lf-menv-find`.
  - `check-duplicates.py` (one new group, finding 4) and `check-lib-callers.py` (clean).
- Findings 4 to 7 come from these searches.
- These are fine:
  - `run@0` (tested in tests/lib/runs.fs).
  - `lf-meta-app-arg`: replaced `dk-arg`, and no other copy remains.
  - `lf-binder-domain`: no other copy.
- The seven entries added to tests/small-copies-allowed.txt are genuine field accessors of different records: the `lf-rinfo-*` words and elim.fs's accessors read different runs, and `fsb-key`/`fsb-val` and `lf-tac-arg-span` are each their own record's reader. They become unnecessary once finding 6 shares the head.
- The design's "library stack for tasks" was not used: tasks are four-cell groups pushed on a run (finding 13b).

## Re-entrancy
- No new module-level mutable state.
- Each call's state lives in a frame of a context slab (`context-slab:`): `fsi-frames`, `frp-cells`, `mri-frames`, `mid-frames`, `mcs-frames`, `mgz-frames`, `mtk-frames`, `pat-frames` (cleared as each pattern begins, read time only) and `rcs-frames`.
- Written only while loading:
  - obtain.fs's two tactic constants;
  - `tac-shape-pattern` (dictionary space allotted at load);
  - the `pat-words` wordlist;
  - error codes 470-474.

## Forth style
**Metrics** (9 files): 411 words; 81% of 1-2 lines, 18% of 3-5, none longer. 2 globals (obtain.fs's tactic registrations), 0 locals, 29 deep shuffles, 78 return-stack operations. Longest word: `mcs-context`, 5 lines. rcases.fs alone has 12 deep shuffles and 44 return-stack operations.

**13a. Magic slot numbers for the subgoal and task records.**
- `0..3 lf-subgoal@`, `3 rcs-sub@` and `2 rcs-new@` use bare slot numbers.
- `4 *` and `4 /` appear six times (`mcs-each`, `rcs-split-in`, `rcs-pushed`, `rcs-task@`, `rcs-pop`, `lf-subgoal@`).
- The subgoal record is a public interface for E2-E5. Name it:
```forth
4 constant lf-subgoal-cells
: lf-subgoals# ( subs -- n ) run-count lf-subgoal-cells / ;
: lf-subgoal-goal ( subs i -- goal ) 0 lf-subgoal@ ;   \ -fields 1, -subst 2, -ctor 3
```
- Tasks: a BEGIN-STRUCTURE `/task` (task-goal, task-fs, task-clears, task-pending) on a context slab (`slab-claim-one`, `slab-last`, `slab-drop`, as pat-frames does) replaces `rcs-task+`, `rcs-task@`, `rcs-pop` and `rcs-again`.

**13b. `2 mri@` and `3 mri@` bypass the module's own accessors** (`mri-itype`, `mri-param`, `mri-params`, `mri-sort`). Use these:
```forth
: mri-info ( -- info ) mri mri-out @ ;
\ 3 mri@ -> mri-info lf-rinfo-major ; 2 mri@ -> mri-info lf-rinfo-params
```

**13c. `lf-goal-with4` takes five items and reaches the goal with `2over drop`.** The frames already hold the arguments. Check and enter the context inside the framed word, and delete `lf-goal-with4`:
```forth
: mid-framed ( goal major d names -- subgoals )
  mid mid-names ! mid mid-d ! mid mid-major0 ! lf-goal-not-assigned ['] mid-body lf-with-goal ;
```

**13d. The rcs frame has 24 fields, several of them registers.**
- `rcs-zps` and `rcs-zfs` are written by `rcs-zip` only for `rcs-zip+` to read.
- `rcs-h`, `rcs-hk`, `rcs-ns`, `rcs-ps`, `rcs-kinds` and `rcs-n` hold processConstructor's state; `rcs-alts`, `rcs-k`, `rcs-names` and `rcs-r` hold processConstructors'.
- Give processConstructor a frame of its own, or pass `( ps fields )` on the stack to a zip word: `: rcs-zip ( ps fields -- pending )` iterating `rcs-zip#` with both runs as arguments (`2dup … run-pair@`).
- `rcs-container` (`:127`) needs four shuffles. Split it into `rcs-head ( node s -- list )` and `rcs-kids+ ( list rev s -- list )`.

**13e. Line breaks that do not follow the code.** `mid-params`, `mid-prefix`, `mri-at`, `mri-major` and `mri-iconst` split a line mid-phrase (`loop` and `drop` alone on a line). Join them, or factor out e.g. `mid-param+ ( type k -- type )`.

**13f. Tests.** test.fs's `info.` uses `pick` and `roll`, and `sub@` copies `lf-subgoal@`. Use `lf-subgoal@` and separate `T{ }T` lines per field.

The layering of finding 11 also touches style: one outcome vocabulary in the Meta layer.

## Portability
- Forth-2012 words only in the new code: `?do`, `+loop`, BEGIN-STRUCTURE, `search-wordlist`, and a guarded `warnings`.
- UTF-8 word names (`⟨`, `⟩`) live in their own wordlist.
- Exercised on Gforth 1.0.0 only.

## What I did not look at
- I did not trace `lf-goal-intro-n`'s one-at-a-time chain against Lean's introN term for terms beyond check.py's 21.
- Gforth 0.7.3 and gforth-fast.
- `check.py --lean`.
- How 76 and 98 arise in other tactics: I checked whether the stale statement variable reaches other tactics only for exact.
- Lean's own text for p03, p04 and p21 (not run).
- The steps golden line by line.
- The docs outside D.8 and the TACTIC_STATUS row.

## Resolution

Fixed on branch `tb2-patterns-e1` (2026-11-22) unless a plan row is named.

| Finding | Resolution |
| --- | --- |
| 1 (blocking) | Fixed at the root in `1a2c6ec7`: elab-term.fs's `et-var` looks a statement variable up by its binder's name in the goal's context, as `et-hyp` does for a hypothesis, and refuses a name the context lacks (76); one check for every tactic. have.fs's own scope guard, which only the old fallback reached, is removed with its fault. Wrong twins `w-stale-target.lf` (p01) and `w-stale-blank.lf` (p19; the run stops at the first error, so two files) with Lean twins; fault `var-unscoped-slot`; test.fs pins both texts. No accepted text changed its answer; three refused ones changed code: `w-clear-used.lf` 98 to 76, batch-b's two cleared-name have texts 99 to 76. LANGUAGE_REFERENCE.md D.8 and the TACTIC_STATUS row corrected. |
| 2 (blocking) | Fixed in `87865975`: `rcs-left` stops at 0 and `rcs-container` bounds its start; `ob_empty` (p11) in obtain.lf with its Lean twin; fault `rcs-left-negative`. |
| 3 (blocking) | Fixed in `63df9aa8` (line numbers refreshed in `778a7b4a`): `make cover-changed` passes. The review's unit tests were written for every group it gave one; test.fs:253 replaced by p25 (471 with Lean's text); align's search is `find-index`, so its loop's blocks went; the blocks no input of the test exports reaches are in the coverage baseline's entries of cases.fs (4), meta-induction.fs (8) and rcases.fs (10), reasons starting "unreachable:" and naming each line. |
| 4 (blocking) | Fixed in `2cefe728`: the subgoal record's named words (`lf-subgoal-cells`, `lf-subgoals#`, `lf-subgoal-goal`, `-fields`, `-subst`, `-ctor`) and rcases' own `rcs-task-cells`; `check-duplicates.py` passes. |
| 5 (blocking) | Fixed in `778a7b4a`: `lf-run+`/`lf-run+!` at the seven sites and in rcases.fs; `lf-tac-unported` for all 22 copies (the review's 17 and contradiction.fs's 5); `lf-tac-spaced.` in `tcr-inline.`; `run-pair@` in lib/runs.fs (tested, documented) replaces `rcs-pair@` and `mgz-arg`'s copy. |
| 6 (blocking) | Fixed in `778a7b4a`: elim.fs exports `lf-decl-telescope`, `lf-bvar-binder` and `lf-decl-suffix`; `mri-start`, `mri-at`, `mcs-cases-on` and `mel-rec` call them (a missing recursor is now 99, not invalid; tactic-lib.fs pins it). |
| 7 (blocking) | Fixed in `778a7b4a`: contradiction.fs's `mcd-ctor-const` and tactics/rewrite.fs's `trw-definition?` use `lf-menv-find?`; unfold.fs's `uf-class-field` and meta-env.fs's `lf-menv-unfoldable` already pass the lookup's outcome on (and meta-env.fs loads before meta-must.fs). Test: s2-sweeps.fs's absorbed refusals drop from 2 to 1 (rw's lookup no longer swallows a refusal), pinned, with fault `trw-room-read-as-absent`. batch-g's heap sweep of contradiction's rule 4 makes no allocation in the lookup, so it does not tell the two apart. |
| 8 | Plan row 9.4.8t and slice E2's text (TACTIC_PATTERNS.md 5). |
| 9 | Fixed in `8573b9a3`: test.fs's ⟨-, hba⟩ leaves no `a = b` for assumption (381) while ⟨_, hba⟩ does; fault `clear-ignored`. |
| 10 | Plan row 9.4.8t and slice E2's text. |
| 11 | Plan row 9.4.8t and slice E2's text. |
| 12 | Fixed in `1a2c6ec7` (D.8, TACTIC_STATUS, what 76 means here) and `8573b9a3` (x-not-inductive.lf's note). |
| 13 | 13a, 13b, 13c (`lf-goal-with4` deleted; goal.fs's `lf-goal-within`), 13e and 13f fixed in `2cefe728`; 13d plan row 9.4.8t and slice E2's text. |

## Re-check of the fixes (2026-11-22)

The independent re-check of the fix commits (diffs read, stacks traced, 14 probes on LeanForth and pinned Lean)
verified the root fix of finding 1 (`et-var` resolves a statement variable through the goal's context: shadowing,
a hypothesis reverted and re-introduced, blocks, have-by and term-mode proofs all answer as Lean; removing have.fs's
guard was safe), finding 2, the replacements of findings 5 to 7 and the named subgoal accessors, and that every
fault's text occurs once. Two blocking items, fixed in `f8e58392`: B1, two copies of `lf-run+!` left (`rcs-finish`,
`mea-alt`); B2, the coverage reason for cases.fs:86 was false (the fallback to `Nat.casesOn` is reached on
s2-slice; `tests/front/tactic-lib.fs` now tests it and the baseline entry fell to 3). Four notes go to slice E2
with plan row 9.4.8t: N1, 76's message for an unknown variable should be Lean's "Unknown identifier"; N2,
`et-vars` stores free variables nothing reads; N3, a `run-quad@` for the task and subgoal copies; N4,
`lfa-has-word?` over `lfa-word-of`. Verdict: merge once B1 and B2 are fixed and the tier passes.

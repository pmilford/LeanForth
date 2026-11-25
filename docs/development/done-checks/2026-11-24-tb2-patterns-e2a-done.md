# Done check: plan row TB2, case patterns slice E2a (2026-11-24)

Independent done checker (Sonnet), on main da2dd131 (pushed by `scripts/push.sh`, origin/main 27ab87d4; Forth review
[2026-11-24-tb2-patterns-e2a.md](../forth-reviews/2026-11-24-tb2-patterns-e2a.md) logged with its re-check; full tier
passed on that head, the planted-faults suite with a 400 s limit per test because `batch-h/test.fs` takes 120 s:
slice E2b's first task). Its first verdict was NOT DONE for two gaps: one wrong variant it could not write from the
reference, and stale wording. The reference was corrected (how to write an application and an "and" hypothesis, a
tuple item in `by-rintro[ ]`, error 94, the status), and the checker then wrote and ran the two cases itself: DONE.
Both reports follow.

## First report

DONE CHECK: TB2 patterns E2a

**Verdict: NOT DONE** (11 of 12 checks pass; one is missing). Stage reached: works end to end on the real command, but two gaps keep it from "done". The scoped claim (subst, `rfl` in patterns, rintro) is met for the cases below. Gap 1: wrong variant 3, a subst on an equation with no variable side, was not exercised. Gap 2: the reference is stale at line 2332. The checked commit was `da2dd131 Log the re-check of slice E2a`, as expected. The checkout is `main`.

Command, run from the repository root with `nice -n 10`:
`bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson FILE.lf`

My files are in `/tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/donee2a/`.

| File | What it tests | Expected | Observed |
|---|---|---|---|
| `t1.lf` | `' h by-subst` on `h : a = b`, goal `b = a` | accept | exit 0, "t1: accepted; axioms: none" |
| `t2.lf` | subst where another hypothesis `k : b = b` mentions the variable | accept | exit 0, accepted |
| `t3.lf` | `by-subst[ h1 h2 ]` with `a = b` and `b = c` | accept | exit 0, accepted |
| `t4.lf` | `by-subst-vars` with `a = b` and `b = a` | accept | exit 0, accepted |
| `t5.lf` | `' h by-obtain[ << x rfl >> ]` on `∃ x, a = x` | accept | exit 0, accepted |
| `t6.lf` | `by-revert[ h k ]`, `by-rintro[ h1 \| h2 k ]`, one `{ }` per goal | accept | exit 0, accepted |
| `t6b.lf` | `by-obtain` on an "and" whose first part is `a = b` (tuple pattern, no `rfl`) | accept | exit 0, accepted |
| `t7.lf` | `by-revert[ h ]`, `by-rintro[ rfl ]` | accept | exit 0, accepted |

My own tuple-item test for `by-rintro` did not run. I replaced it with `by-obtain` in `t6b.lf`, so the tuple item `by-rintro[ << h1 h2 >> k ]` is **not** covered.

Wrong variants:

| File | Fault | Observed |
|---|---|---|
| `w1.lf` | naming the eliminated `b` after subst | exit 4, error 76 "malformed elaboration", at `by-exact` |
| `w2.lf` | naming `h` after `' h by-subst` | exit 4, error 76, same text |
| `w3.lf` | neither side of the equation is a variable (`succ a = succ b`) | **not tested**: my statement did not parse (error 18, exit 4). That is a refusal for a different reason. |
| `w4.lf` | `h : a = Nat.succ a` | exit 4, error 476 "Tactic `subst` failed: 'a' occurs at Nat.succ a", with the goal shown |
| `w5.lf` | `by-rintro[ h1 h2 ]` with only one binder after revert | exit 4, error 94 "Tactic `introN` failed: There are no additional binders ... to introduce" |

Observations:
- Output ends with "accepted: 1291; axioms: propext, Classical.choice, Quot.sound (allowlisted); none NOT PROVED". My theorem is listed as its own line (for example `t1: accepted; axioms: none`). That sits among the 1291 loaded environment declarations, and the summary line is easy to misread as covering only the environment. Piping the output through `head` gave exit 141 (SIGPIPE), which is my doing and not the tool's.
- Wrong variants 1 and 2 are refused with 76, which matches the reference at lines 2337-2338. The reference does not say what text a user sees. It says "Lean's Unknown identifier" while the message is "malformed elaboration".
- In `w1.lf` my first attempt, `' b by-rfl`, gave error 86 (wrong number of values). That was my mistake, not a refusal of subst.
- Every file starts with the same `Subtype ... accepted` lines for the environment, as expected.

Reference problems (`docs/user/LANGUAGE_REFERENCE.md`):
- **Line 2332** is stale: "tested on branch `tb2-patterns-e2a`, not merged". The slice is on `main`. Corrected wording: "Plan row TB2, piece E, slice E2a (merged; tests in `tests/front/tactics/batch-h/`)".
- **Lines 2362-2405 (the three examples)** are enough to copy a subst, an `rfl` pattern and an `∨` rintro. They are not enough to write a first proof of a different shape:
  - Nothing says how to write a binary operator or a nested application in a statement. `a b + =` failed. `' Eq ' Nat.succ a $ ' Nat.succ b $` failed. Only the `' f x $` form from the examples worked, and it was found by luck (`' Nat.succ a $` is used in `w4.lf`).
  - Nothing shows a hypothesis that is an "and" being written (`a b = a a = ∧`).
  - There is no example of a tuple item inside `by-rintro[ ]`, although the table at line 2347 lists one.
  - Line 2418-2419: "475 and 477 come from the goal operation alone, which the tactics never reach" is true as stated, but the user-visible code for subst on a missing equation (479) and for a bad `rintro` (94, `introN`) is not in the error list. Error 94 appeared for `w5.lf`, and 94 is not named in D.9.
- Line 2411 points to `tests/front/tactics/batch-h/`, which I did not read, as instructed.

Not checked:
- Wrong variant 3: a subst where neither side is a variable (error 478 expected). I could not write the statement.
- `by-rintro` with a tuple item.
- The `by-rintro[ ]` forms with `-` and a typed group.
- `by-subst[ ]` with a missing name (error 455).
- The `' x by-subst` form on a variable.
- `HEq`, let variables, `by-have:` hypotheses.
- Comparison with pinned Lean, the test suites and the git history. I ran no `make` target, as instructed.
- No non-trivial theorem where subst is needed for a goal that `by-rfl` cannot close.

## Follow-up

DONE CHECK (follow-up): TB2 patterns E2a. Verdict: DONE. Both gaps are closed. Command as before: bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson FILE.lf. My files: /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/donee2a/f1.lf and f2.lf.
1. Wrong variant 3 (f1.lf): h : ' Nat.succ a $ ' Nat.succ a $ = (succ a = succ a), then ' h by-subst. Exit 4, error 478 at by-subst: "Tactic `subst` failed: invalid equality proof, it is not of the form (x = t) or (t = x)", with the goal printed. Refused as the reference says. The "' f x $" statement form from the updated reference parsed on the first try.
2. Tuple item in by-rintro[ ] (f2.lf): h : a = b and b = a (as one "and"), goal b = a, by-revert[ h ], by-rintro[ << x y >> ], ' y by-exact. Exit 0, "f2: accepted; axioms: none".
3. docs/user/LANGUAGE_REFERENCE.md D.9 on disk (uncommitted): lines 2331-2334 no longer say "tested on branch ... not merged". They now say "on main, tests in tests/front/tactics/batch-h/" and link a done-check file, docs/development/done-checks/2026-11-24-tb2-patterns-e2a-done.md. I did not open that file. Error 94 ("Tactic `introN` failed: ...") is now listed at line 2426. Lines 2335-2336 add the statement-writing note (application is ' Nat.succ a $).
Still not checked: by-subst[ ] with a missing name (455), the "-" item and typed group, ' x by-subst on a variable, HEq/let/by-have: cases, comparison with pinned Lean, and the test suites (no make run). The coordinator's own c1.lf and c2.lf were ignored.

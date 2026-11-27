# Done check: small tactics 2 (2026-11-26)

Independent done checker (Sonnet), on main 8bd07450. Its report follows unchanged except for the scratch path.

**Coordinator's resolution (2026-11-26, 23:29):** verdict DONE on behaviour. The stale lines it lists are rewritten in the commit that adds this file: PROJECT_PROGRESS.md, plan row 9.4.8z15 for the group with row 9.4.8z12 keeping the leftovers, and the reference's pointer to D.13. Forth review: [2026-11-26-small-tactics-2.md](../forth-reviews/2026-11-26-small-tactics-2.md); the tier passed on 82f36982 (exit 0).

---

DONE CHECK: small tactics 2

**Verdict: DONE on behaviour (works end to end).** The user-facing check runs on my own `.lf` texts. The Lean twins and the Lean refusals agree with LeanForth. The only issue is one wrong-statement refusal, which is exit 2 rather than exit 4 (claim 3). The docs and records are stale, as listed below.

I wrote every proof from `docs/user/LANGUAGE_REFERENCE.md` D.13 (lines 3228-3315) and its table rows (2017-2020). The reference names the patterns slice for calc, so I used it. No test file was copied. All commands ran at the repo root under `ulimit -u 500` and `nice -n 10`, in the form `bin/leanforth check --env tests/front/patterns-slice.ndjson --elab-data tests/front/patterns-slice.elab.ndjson F.lf`. The files are in `the checker's scratch directory`. The Lean twins are `t.lean`, `u.lean` and `v.lean` in the same folder.

Claim sentences (each "A user can ..."):
1. Write `by-calc[ ... ]` chains and have `leanforth check` accept them.
2. Rely on a calc `?_` step putting its new goal ahead of the goals already open.
3. Get a refusal for wrong calc uses.
4. Use `by-with-reducible ... by-end` with the documented reducible-only unfolding.
5. See `rw`'s closing `rfl` run strictly at reducible transparency.

| # | File and what it tests | Exit | Decisive line |
|---|---|---|---|
| 1 | `ok1`: `=` chain of two steps from hypotheses | 0 | `ok1: accepted; axioms: none` |
| 1 | `ok2`: `= ≤ <` with `_` left sides | 0 | `ok2: accepted; axioms: none` |
| 1 | `ok3`: `≤ ≤` chain | 0 | `ok3: accepted` |
| 1 | `ok4`: `_ c = ?_` step, closed by the next tactic (`' h2 by-exact`) | 0 | `ok4: accepted` |
| 2 | `ord`: `by-constructor`, calc with `?_`, `' h2 by-exact`, `by-rfl` | 0 | `ord: accepted` |
| 2 | `ordtwin`: same, with `by-rfl` first | 4 | `error 97 ... Tactic rfl failed: ... b is not definitionally equal to ... c; case left` |
| 3 | `bad1`: step left side `c`, previous right side `b` | 4 | `error 513 ... invalid 'calc' step, left-hand side is c ... previous right-hand side is b` |
| 3 | `bad2`: chain gives `a ≤ c`, goal `a < c` | 4 | `error 89 unsolved goals; case calc.step ... ⊢ c < c` |
| 3 | `bad3`: step proofs swapped, so a proof of the wrong statement | 2 | `unsupported: error 131 ... a coercion (plan FE4)` |
| 4 | `wr1`: `by-with-reducible ' h1 by-exact by-end` | 0 | `wr1: accepted` |
| 4 | `wr2`: `h : Nat.pred (Nat.succ a) = b`, `exact h` inside `by-with-reducible` | 4 | `error 96 Type mismatch ... expected a = b` |
| 4 | `wr4`: the same `exact h` outside a block | 0 | `wr4: accepted` |
| 4 | `wr3`: the same inside `by-with-unfolding-all` | 0 | `wr3: accepted` |
| 4 | `wr5`: `by-try by-with-reducible ... by-end by-end`, then `exact` | 0 | `wr5: accepted` |
| 5 | `g`: the Lean text from the claim, written in LeanForth | 4 | `error 89 unsolved goals ... ⊢ Nat.pred (Nat.succ b) = b ↔ b = b` |
| 6 | Pinned Lean on `t.lean` (`ok1`, `ok2`, `ok3` and `ord` twins) | 0 | no output, all accepted |
| 6 | Pinned Lean on `u.lean` (goal-order twin) | 1 | `error: Tactic rfl failed ... b ... c; case left` |
| 6 | Pinned Lean on `v.lean` (claim 5's `rw [h]` theorem) | 1 | `error: unsolved goals ... ⊢ b.succ.pred = b ↔ b = b` |

Claim 3 detail: `bad3` is refused but not rejected as invalid. A wrong-statement step proof gives "not supported yet" (exit 2, error 131) where Lean says "type mismatch". D.13 (reference lines 3282-3283) documents this. The user sees a refusal, never an acceptance.

Claim 6 detail: I ran Lean twins for four calc theorems, the goal-order twin and the `rw` theorem. I compared accept/refuse only, not proof terms.

Claim 7, docs findings:
- `docs/project/PROJECT_PROGRESS.md:32` says small tactics 2 is "Forth-reviewed, its fix round on the branch, not merged, not done". That is stale if this head is the merged result.
- `docs/project/PROJECT_PROGRESS.md:33` says "Not yet: calc, ... with_reducible" for the small tactics 1 group. Those two are now in, so it needs a note that small tactics 2 added them.
- `docs/project/PLAN_DRAFT.md:851` marks row 9.4.8z12 "Not started (2026-11-26)" while its own text says calc and `with_reducible*` are in. Split it into a done part (small tactics 2, citing this report) and the leftovers.
- No plan row for small tactics 2 as a group cites a done-check report. The coordinator needs to add one.
- `docs/user/LANGUAGE_REFERENCE.md:2017` says "see D.12" but the section is D.13. Correct it to D.13.
- `docs/user/LANGUAGE_REFERENCE.md:3232-3234` says the examples are "copied whole" from `tests/front/tactics/batch-small-2/*.lf` and checked "node for node" against pinned Lean's twin. I did not verify that.
- The reference's cost line "300 steps check in 22 s" and the nesting limit of 118 blocks were not checked.

What I did not check:
- Node-for-node equality of terms with Lean, and `check.py`.
- `by-with-reducible-and-instances` (the 139 case).
- Chain extension with `calc.step` beyond `bad2`.
- The `ord` goal tags (`calc_1`, `calc_2`).
- A calc with a `?_` step whose proof is the only ordering test of more than two goals.
- Nesting depth and the 300-step timing.
- The Forth review log, coverage, CI and `make` targets.

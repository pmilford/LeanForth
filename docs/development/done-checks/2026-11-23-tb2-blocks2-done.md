# Done check: plan row TB2, blocks slice 2 (2026-11-23)

Independent done checker (Sonnet), on main 4aaf236a (pushed by `scripts/push.sh`, origin/main f5ab977e; Forth review
[2026-11-22-tb2-blocks2.md](../forth-reviews/2026-11-22-tb2-blocks2.md) logged with its re-check; full tier passed
on that head). The commit that added this report corrected the reference as its items 1 to 5 ask (status wording;
exit 4 for a refused text and where its error number is; how a four-part "and" is written; that goals a chain
leaves are closed by later steps).

DONE CHECK: TB2 blocks slice 2
Verdict: DONE for the claim as written, on stage "works end to end". I did not judge the "done" stage (review log, coverage, CI). The reference still calls the slice unfinished (stale, below). Checkout was `main` at 4aaf236a, the expected commit.

Command, from the repository root, once per file (files are in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/doneb2/, named g1..g6 and w1..w4, each `.lf`):
`nice -n 10 bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson FILE.lf`

Every file is my own LeanForth text, written from LANGUAGE_REFERENCE.md only. I did not read tests/front/tactics/blocks-2/. Hypotheses h : a = b and k : b = a, as in the reference.

| # | Goal and proof | Expected | Observed |
|---|---|---|---|
| g1 | (a=b ∧ a=b): `by-constructor <;> ' h by-exact` | accept | exit 0, "g1: accepted" |
| g2 | four-part "and": `by-constructor <;> by-constructor <;> ' h by-exact` (chain of three) | accept | exit 0 |
| g3 | `by-constructor <;> { ' h by-exact }` | accept | exit 0 |
| g4 | `by-constructor <;> by-constructor` leaves 4 goals, then `by-all-goals ' h by-exact by-end` | accept | exit 0 |
| g5 | `by-constructor`, then `by-all-goals ' h by-exact by-end` | accept | exit 0 |
| g6 | `by-constructor`, then `by-all-goals by-symm ' k by-exact by-end` (two-step block) | accept | exit 0 |
| w1 | goal a=b ∧ b=a, `by-constructor <;> ' h by-exact` (t2 fails on the second goal) | reject | exit 4, error 96 Type mismatch at 6:26, "has type a = b but is expected b = a" |
| w2 | `by-constructor <;> by-constructor` and nothing more (chain leaves goals open) | reject | exit 4, error 89 unsolved goals at `by` (5:4); lists the goal ⊢ a = b |
| w3 | `<;> ' h by-exact` as the first step of the proof | reject | exit 4, error 468 "<;> follows no tactic of its block" at 6:3 |
| w4 | goal a=b ∧ b=a, all-goals block `' h by-exact`, wrong for the second goal | reject | exit 4, error 96 Type mismatch at 7:20 |

Each accepted run ends with the library line "1291 declarations: 1291 accepted" and the theorem line "gN: accepted; axioms: none". Each of the 10 files was run once, so I did not check that the results are repeatable.

I did not see the "t2 closes one goal, the other is closed afterwards" case work with `<;>` alone. A `by-constructor` t2 fails on an equality goal. g4 covers the same idea with `by-all-goals`, closing goals that `<;>` left open.

What the reference got wrong or left out:
1. LANGUAGE_REFERENCE.md:1640-1642 is stale. It says "tested on branch `tb2-blocks2`, not merged, not done". The work is on `main` and now works end to end. The wording has to change once the plan row cites this report.
2. The task description says a rejection gives exit 1. All four wrong files exit 4, because they are refused as invalid LeanForth text (the output says "invalid: the LeanForth text was not checked"). The reference does not state the exit code for a refused proof, but it does give the error numbers (468, 89, 96 at 1677-1685), and these matched. Whoever writes the owner's report should say 4, not 1.
3. The reference never says how to read an "and" of four parts (`A B ∧ C D ∧ ∧`). It does give the three-part rule at lines 1549-1551, and I wrote g2 and g4 from that rule. The first example, at 1692-1700, shows enough of the layout (statement lines, `:= by`, `end NAME`) to start with.
4. The reference has no example of a chain where t2 leaves goals open that are closed later. `ag_left` at 1712-1723 comes closest, but it uses `by-all-goals` rather than `<;>`.
5. Nothing at 1640-1685 says that a plain `<;>` rejection exits 4, or where in the message to look for the error number. The number appears only in the "error NNN" text of the message.

Not checked:
- The comparison with pinned Lean (check.py), since I was not to run make targets or the suites.
- Nested uses, `at[ ]` after t2, and the "t1 leaves no goal" case.
- Anything on a different engine, or on the Mathlib or Init inputs.
- The error text for `<;>` before `by-end`, `}`, `|` or `end`.
- Lean-side agreement for my ten files; I only checked LeanForth's own verdict.

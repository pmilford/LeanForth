# Done check: plan row TB2, case patterns slice E1 (2026-11-22)

Independent done checker (Sonnet), on main 63f6324f (pushed by `scripts/push.sh`, origin/main 93edeac4; Forth review
[2026-11-22-tb2-patterns-e1.md](../forth-reviews/2026-11-22-tb2-patterns-e1.md) logged with its re-check; full tier
passed on that head). The commit that added this report corrected the reference as its gaps 1 to 5 ask (status
wording; one `{ }` per goal; what can and cannot be named after `-`; the exit codes of a refused text; which output
line is the theorem's verdict). The poor text of error 76 for "h is gone" is a task of slice E2 (plan row 9.4.8t).

DONE CHECK: TB2 patterns E1
Verdict: DONE for the claim as worded (a user can write `by-obtain[ ]` and `by-rcases[ ]` with these patterns, and `h` is gone afterwards). Stage: works end to end. I did not check the "done" criteria beyond that: CI, the Forth review log and coverage are out of scope here. Reference line 2101 is stale (below).
Main was at 63f6324f "Log the re-check of slice E1 and plan its four notes".

Claim as a user reads it: "A user can write `' h by-obtain[ pat ]` and `' h by-rcases[ pat ]` in a LeanForth file checked by `leanforth check`, with patterns made of a name, `_`, `-`, `<< >>` tuples and `a | b` alternatives, and after them `h` is gone."

Command, from /home/peter/code/LeanForth, run with `nice -n 10`:
`bin/leanforth check --env tests/front/decide-slice.ndjson --elab-data tests/front/decide-slice.elab.ndjson FILE.lf`
The files are in /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/donee1/ (g1..g8, w1..w5 .lf). I learned the syntax only from LANGUAGE_REFERENCE.md D.8 and the nearby tuple and `{ }` sections. I did not read batch-g.

Good theorems (a, b : Nat; all tuple patterns were written `<< >>`). All exit 0 with "gN: accepted; axioms: none":
| file | statement and pattern | expected | observed |
| g1 | h : a=b ∧ b=a ⊢ b=a; `<< hab hba >>`, `' hba by-exact` | accept | exit 0 |
| g2 | three-part ∧ ⊢ a=b; flat `<< x y z >>` | accept | exit 0 |
| g3 | same; nested `<< x << y z >> >>` | accept | exit 0 |
| g4 | h : a=b ∨ b=a ⊢ b=a ∨ a=b; `hp \| hq`, one `{ }` per goal | accept | exit 0 |
| g5 | h : (a=b ∨ b=a) ∧ a=b; `<< x \| y z >>`, two goals | accept | exit 0 |
| g6 | `-` drops a part: `<< x - >>` | accept | exit 0 |
| g7 | `_`: `<< _ y >>` | accept | exit 0 |
| g8 | n : Nat ⊢ n+0=n; `' n by-rcases[ _ \| m ]`, `{ by-rfl } { by-rfl }` | accept | exit 0 |

Wrong variants. None was accepted:
| file | variant | expected | observed |
| w1 | `' h by-exact` after `' h by-obtain[ << hab hba >> ]` | refuse | exit 4, error 76 at `by-exact` ("malformed elaboration…"). Lean says "Unknown identifier", and the reference (2203-2207) says the same. |
| w2 | use a name never given, after `<< hab - >>` | refuse | exit 4, error 1 "unknown name" at `hba`. See gap 3: this does not test a cleared name. |
| w3 | `hp \| hq` with only the first `{ }` | refuse | exit 4, error 89 "unsolved goals, case inr, hq : b = a" |
| w4 | `by-case: intro =>` after the one-constructor obtain | refuse | exit 4, error 210 "Case tag `intro` not found. Note: There are no cases to select." This is Lean's text. |
| w5 | tuple `<< hp hq >>` on an ∨ | refuse | exit 2, error 99 "not supported yet". Refused, but as "unsupported", not "invalid". |

Gaps and problems in the reference:
1. LANGUAGE_REFERENCE.md:2101 is stale. It says "tested on its branch, not merged", but the work is on main. It should say "slice E1 merged; checked with `bin/leanforth check` as below".
2. The reference worked the first time for g1..g8. One detail needed care: a `{ }` per goal is described only in the blocks-1 section (about line 1559), and D.8 does not mention it. The D.8 `rc_or` example uses no braces. Add one line to D.8: "with two goals, close each with `{ ... }` (see Tactic blocks)".
3. The `-` clearing is hard to test from the reference. Lines 2116 and 2203 say a cleared name is refused with 76. But `-` has no name to use afterwards, and `' h` afterwards is refused. A user cannot write a "use the dropped part" case. My w2 used a name that never existed (error 1, not 76). Lines 2116 and 2203 should say that only `h` itself, or a statement variable the split cleared, can be named afterwards.
4. Exit codes: refusals of bad proofs come out as exit 4 ("invalid"), not 1. The reference does not say how these codes relate to the claim's "refused". Line 2185 gives the command but no exit-code table. Error 76's text is misleading for "h is gone"; the reference admits it (plan NR). w5 exits 2, not 4.
5. Every run prints the whole environment ("1291 declarations: 1291 accepted … NOT PROVED"). That is the environment's check, not my theorem. A reader could mistake it for a verdict on the theorem; the line "gN: accepted" is the one that counts.

Not checked: the reference's `ob_exists` example and `⟨ ⟩` spelling in a file of my own (I used `<< >>`); errors 470-474, 458 and 72; `' foo ' a $` terms as the value; Nat.casesAuxOn goal names (`n + 1`); `rfl` patterns and indexed families (reference says 99); the hidden-name and revert behaviour; and CI or coverage state. The plan row and PROJECT_PROGRESS wording were not read.

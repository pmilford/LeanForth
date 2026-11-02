# First checker: review gate summary (draft)

**Status: draft, 2026-11-02. Nothing has been approved and no checker code
exists yet.** This is the plain-language summary the owner approves at the
[kernel] gate (`AGENTS.md`, owner decision 1). It is written now, before the
code, so the rules can be agreed first; it will be updated with the real
test results and the independent AI review before the final approval (plan
tasks 2.3.1–2.3.2). Technical detail: [ADR 0011](../adr/0011-definite-rejection.md)
and [the expected-results table](FIRST_CHECKER_EXPECTED.md).

## What the first checker will do

LeanForth will read a small Lean file's declarations (definitions and
theorems) one at a time, in order, and give each exactly one answer:

- **accepted** — the proof checks. Printed as *accepted — experimental, not
  independently audited; axioms: none*. Only accepted declarations are added
  to the library, and only they may be used by later declarations.
- **rejected** — the declaration is definitely wrong, *and Lean would reject
  it too*. LeanForth also names the kind of error Lean would report.
- **unsupported / unknown** — LeanForth could not decide. *Unsupported*
  means the declaration uses something not built yet (for example a `let`
  or a number). *Unknown* means the parts are supported but deciding needs a
  rule LeanForth does not have yet.

Malformed input (*invalid*) and running out of time or memory (*exhausted*,
*full*) are reported separately. None of these is ever counted or stored as
accepted.

It handles only the simplest kind of Lean declaration — functions, function
types and universe levels, plus references to earlier accepted
declarations — which is enough for the five pinned example files. Real Lean
library code needs data types such as numbers, which come in phase 5.

## Why "unknown" sometimes appears where Lean says "wrong"

Lean decides whether two expressions mean the same thing with several rules
the first checker leaves out on purpose (your decision 3, "cautious first"):
unfolding a definition into its body, treating any two proofs of the same
statement as equal, "eta" (`f` is the same function as `fun x => f x`), and
simplifying universe levels. Where one of these could matter, LeanForth must
say *unknown* — even if Lean would reject the declaration — because saying
*rejected* would be a guess. Example: the table's `needs-unfolding-wrong`
row claims something false about `fixtureId`; Lean rejects it after
unfolding `fixtureId`; LeanForth must answer *unknown*.

The reverse also happens: rows such as `proof-irrelevance-twin` are correct
proofs that Lean accepts but LeanForth cannot yet confirm, so it answers
*unknown*. Neither direction can make LeanForth accept a wrong proof.

## Evidence

| Evidence | Status |
| --- | --- |
| Rules follow Lean's own kernel: each rejection rule cites the Lean 4.35.0 source file and function that makes the rejection certain | done (ADR 0011) |
| Lean's answer for every test case, run with the pinned Lean: 60 cases (the 7 declarations of the 5 example files, 46 broken or near-identical copies, 7 out-of-scope cases) — 30 accepted, 30 rejected by Lean, all as recorded | done, 2026-11-02 |
| 27 of the broken copies also written as ordinary Lean source, in one file; Lean rejects every one for the expected reason | done, 2026-11-02 |
| The test script catches planted mistakes in its own tables (6 tried, 6 caught) | done, 2026-11-02 |
| LeanForth's answers agree with the table: 14 accepted, 28 rejected, 1 invalid, 9 unknown, 8 unsupported | **not started** — needs the checker (tasks 2.2.1–2.2.3) |
| Failure paths: every check reaches every outcome; nothing failing is stored as accepted; running out of fuel or memory at every step | **not started** (task 2.2.4) |
| Replay gives identical answers | **not started** (task 2.2.5) |
| Independent AI review of the exact code change, no unresolved findings | **not started** (task 2.3.1) |

## Risks

1. **A wrong rejection rule.** LeanForth would call a valid proof wrong. That
   cannot make a false theorem accepted, but it would mislead. Each rule is
   tied to Lean's source, and the table has pairs of almost identical cases
   where Lean accepts one and rejects the other, to catch a rule that
   reaches too far.
2. **A wrong acceptance** — the serious risk. The first checker accepts only
   when every comparison is exact (same structure after simple
   substitution), the narrowest rule there is. Results stay labelled *not
   independently audited* until an outside Lean expert reviews them.
3. **An assumption that LeanForth computes the same types as Lean.** The
   rules depend on it; the existing Lean comparisons and the planned ones
   test it, but tests are finite.
4. **A correction to earlier documents.** Lean's kernel does unfold
   theorems when comparing expressions; ADR 0006 proposes never unfolding
   them, and the plan describes Lean that way. This does not affect the
   first checker (it unfolds nothing) but must be settled before unfolding
   is built (phase 4).
5. **Toy inputs only.** These tests show the rules on small examples, not on
   real Lean libraries.
6. **Your time.** The gate needs your approval twice: of the rules now, and
   of the evidence once the code exists.

## Recommendation

Approve ADR 0011's rule list as the design for the first checker, with the
answers recommended below, so the code can be written against it. The rules
are the narrowest that still let LeanForth say "wrong" for the common
mistakes in the examples (wrong argument, wrong universe, wrong claimed
type, non-proposition theorem, missing or misused names), each is traced to
Lean's own source, and every case was checked against Lean. Final approval
of the checker itself comes later with LeanForth's own test results.

## Questions for you

**G1. Approve the rule list now, and the code later?**
LeanForth's first checker answers *rejected* only in the situations ADR 0011
lists, each traced to Lean's source, and *unknown* everywhere Lean might
still decide differently. *Recommendation: yes.* Agreeing the rules before
coding is cheaper than reworking code, and the code still needs your
separate approval with its test results.

**G2. Should *rejected* always mean "Lean would reject this too"?**
The alternative is to let LeanForth reject things for its own policy
reasons. *Recommendation: yes, keep "rejected" for Lean's verdict.* Then a
*rejected* answer is objective and testable against Lean, and policy
refusals have their own name (see G3).

**G3. What should LeanForth answer for a statement assumed without proof
(an axiom)?**
Lean accepts such a declaration; your decision 4 allows none in the first
checker. *Options:* (a) *unsupported* — not built yet; the allowlist
arrives with data types in phase 5; (b) *rejected* by policy.
*Recommendation: (a).* It is never accepted either way, and (a) keeps G2's
meaning of *rejected*. Anything that uses such a statement is also
unsupported, never accepted.

**G4. May LeanForth look inside expressions to reject a wrong variable?**
For example, claiming "P holds of y" from a proof that "P holds of x". Lean
rejects this when x and y are ordinary values but accepts it when they are
themselves proofs, because Lean treats any two proofs of the same statement
as equal. LeanForth can tell the two apart and the table tests both.
*Options:* (a) include this rule (D5) now; (b) leave such cases *unknown*
for now. *Recommendation: (a).* It catches a very common kind of mistake,
the risky twin is tested, and a mistake in it could only produce a wrong
*rejected*, never a wrong *accepted*.

**G5. Correct the earlier documents to say that Lean's kernel unfolds
theorems too?**
ADR 0006 and the checked-environment review propose that theorems never
unfold, and the plan describes Lean's method that way; Lean 4.35.0's kernel
source shows that Lean does unfold them (last, after definitions).
*Recommendation: yes, correct them when the unfolding ADR is written
(phase 4), and follow Lean there.* Your decision 1 says follow Lean's
published behaviour; the first checker is unaffected.

## Owner's answer

*Not yet given.* Record the date, the answer to each question and the
commit reviewed here.

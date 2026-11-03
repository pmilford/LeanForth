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

2026-11-02, reviewing commit `b30dc84`, in a Claude Code session; the owner
chose the recommended option on G1–G4:

- **G1:** the rule list is approved now; the code needs separate approval
  with its test results.
- **G2:** *rejected* always means Lean would reject it too.
- **G3:** a declaration assumed without proof is *unsupported* in the first
  checker, never accepted.
- **G4:** rule D5 (rejecting a wrong variable inside an argument) is in.
- **G5** was not asked: it follows owner decision 1 (follow Lean's published
  behaviour), so the earlier documents are corrected when the unfolding ADR
  is written in phase 4. The owner may still overrule it.

## Second set of questions

**Status: drafted 2026-11-02 (plan tasks 2.1.2 and 2.1.3); not yet
answered.** Two more decisions the first checker needs before its code is
written. Like G1–G4 they approve a rule and a design, not code: the code
still comes back to you with its test results. Technical detail:
[ADR 0003, Amendment 1](../adr/0003-conversion.md#amendment-1-proposed-comparing-under-binders-whose-domains-differ)
and [ADR 0012](../adr/0012-checked-environment.md). Answering "agree"
accepts all six recommendations.

### Decision A — functions whose argument types are written differently

**What it decides.** Checking a proof often means comparing two functions,
or two "for all" statements. Sometimes their argument types are written
differently but mean the same thing: `(fun T => T) A` is just `A` after one
simplification step. Today's rule then answers *unknown*. Your review of
2026-10-30 left open whether LeanForth may go further. The proposal: do what
Lean does — first check that the two argument types are equal; if they are,
compare the bodies, treating the argument as having the *expected* side's
type (the type the statement claims, or that the function asks for).

**Example.** "For every proposition A, (the identity applied to A) implies
A" — that is, A implies A. Lean accepts
`theorem bdStatement : ∀ (A : Prop), (fun T : Prop => T) A → A := fun (A : Prop) (h : A) => h`:
the statement's argument type is `(fun T => T) A`, the proof's is `A`.
Today LeanForth must answer *unknown*; with the change it answers
*accepted*, like Lean.

**Evidence.**

- Lean 4.35.0's own code does exactly this; the amendment cites the
  function (`is_def_eq_binding`) line by line, and Lean's published
  description of its type theory (Carneiro, 2019) states the same rule.
- A new Lean test file, run by `make reference-binder-domains` in
  `make check`: 22 cases (10 comparisons, 12 declarations). Lean gave the
  recorded answer in all 22. Every comparison gives the same answer with its
  two sides swapped — evidence that *which* side's argument type is used
  cannot change the result. 13 deliberately planted mistakes in the test
  files were each caught.
- 8 cases change from *unknown* to *accepted* (or equal); with G7, 5 more
  change from *unknown* to *rejected*; 9 stay as they are. None of the 60
  cases of [the first table](FIRST_CHECKER_EXPECTED.md) changes.
- LeanForth's existing (untrusted) comparison experiment already behaves
  this way; the written rule was stricter than the code.

**Risks.** LeanForth could wrongly accept only if it called two different
argument types equal — and that uses the same cautious comparison already
used everywhere else; this step adds no new kind of equality. The checker
must compare in Lean's order (found first, expected second); the tests pin
it. As before, this is evidence about Lean, not yet about LeanForth's code.

**Recommendation:** approve G6 and G7.

### Decision B — how the library of accepted declarations is kept

**What it decides.** Where accepted declarations are stored, and how checks
running at the same time are kept from seeing each other's unfinished work
(ADR 0012):

- Each declaration of the input has a numbered place in the library, in
  input order. The place is filled once, after the check ends, and never
  changes.
- Only accepted entries can be used, and only by later declarations.
- A check works in its own scratch space. If it fails for any reason —
  rejected, unknown, out of memory, a crash — that space is thrown away and
  the library is unchanged.
- One part of the program, the *publisher*, fills the places; checks only
  read.
- The proof that was checked is the proof stored; nothing is copied.
- Each entry lists the axioms it depends on, directly or indirectly. In the
  first checker the list is always empty, and is computed, not assumed.
- Saved results are reused only in development mode, and labelled.

**Evidence.** The design follows Lean's own kernel, cited in ADR 0012: Lean
never changes its library in place, adds a declaration only after every
check has passed, gives each declaration its own universe names, and
collects axiom lists the same way. It matches ADR 0006, ADR 0009 (which you
approved) and your earlier answers. It is a design only: there is no code
and no LeanForth test yet. ADR 0012 lists the ten groups of tests the code
must pass, including a failure injected at every memory allocation and
"parallel gives exactly the serial result".

**Risks.**

1. Scratch space and library must really stay apart. Tests compare
   fingerprints of the library before and after every failure.
2. The imported records must not change after loading (G10). Inside one
   Forth program this is a programming rule, not a hardware protection; a
   fingerprint test catches accidental changes. The checker already runs as
   its own program (your OQ-1 answer), so user code cannot reach it.
3. The parallel version (phase 7) relies on Gforth's threads, which Gforth
   marks experimental; the one-at-a-time path always works and is tested.

**Recommendation:** approve G8–G11.

### Questions for you

**G6. Should LeanForth compare functions whose argument types are written
differently, the way Lean does?**
*Options:* (a) yes, as Lean: argument types first; if equal, the bodies,
with the expected side's argument type; (b) keep today's rule, which
answers *unknown*. *Recommendation: (a).* It is Lean's own rule (your
decision 1), it turns *unknown* answers for correct proofs into *accepted*,
it cannot make a wrong proof accepted, and it settles the question left
open on 2026-10-30.

**G7. Should the same step also let LeanForth answer *rejected*?**
When the argument types are equal but the bodies certainly differ, Lean
rejects. Rule D4, approved under G1, looks at the bodies only when the
argument types are written identically. *Options:* (a) let D4 look at the
bodies whenever the argument types are equal; (b) keep D4 as approved, so
those 5 test cases stay *unknown*. *Recommendation: (a).* The reasons are
those of G4: it catches real mistakes, every case is checked against Lean,
and an error in it could only produce a wrong *rejected*, never a wrong
*accepted*. Choose (b) if you prefer to approve G6 on its own first.

**G8. Approve the library design of ADR 0012?**
Grow-only, each place written once after the check ends, scratch thrown
away on failure, one publisher, places numbered in input order.
*Recommendation: yes.* It is the simplest design that cannot leave a failed
or half-finished check in the library; it keeps the library the way Lean's
kernel does; and it already works for checks in parallel without changing
any rule.

**G9. May a check ever rely on an earlier declaration that has not been
accepted yet?**
The scale assessment suggested a faster parallel method: check declarations
before the ones they use are accepted, then accept them all together if
every one passed. *Options:* (a) no — a check uses only declarations already
accepted; (b) allow it later, after measurements. *Recommendation: (a) for
now.* With (b), *accepted* would rest on a second, separate bookkeeping
step — one more place where a mistake could produce a wrong *accepted* —
and no measurement yet shows that the speed is needed. Revisit in phase 7
with timings.

**G10. [import] May the library point at the imported records that were
checked, instead of copying them, if imported records never change after
loading?**
*Recommendation: yes, point rather than copy.* Then the stored statement is
exactly the checked one; a copy could differ through a copying mistake and
would need checking again. The risk is risk 2 above.

**G11. Is this how your "development mode" for saved results should work?**
A final run starts empty, refuses saved results and checks everything. A
development run may load saved results; each of them, and everything that
depends on one, is marked *not re-checked in this run* in every output.
Only a final run's results support a claim. *Recommendation: yes.* It is how
we read your answer to OQ-3; spreading the mark to everything that depends
on a saved result keeps a result from looking fully checked when part of
its foundation was not. Phase 2 builds only the final mode.

### Owner's answer (second set)

2026-11-02, reviewing commit `e3188de`, in a Claude Code session; the owner
chose the recommended option on all six:

- **G6:** compare under differing argument types as Lean does (ADR 0003,
  Amendment 1).
- **G7:** rule D4 rejects through *equal*, not only identical, argument
  types (ADR 0011 amended).
- **G8:** ADR 0012's library design is approved.
- **G9:** a check relies only on declarations already accepted; revisit
  speculative checking in phase 7 with timings.
- **G10:** the library points at the checked imported records, which never
  change after loading.
- **G11:** development mode as designed: saved results and everything that
  depends on them are labelled *not re-checked in this run*; only a final
  run supports a claim.

As before, these approve rules and a design; the checker code needs its
own approval with test results.

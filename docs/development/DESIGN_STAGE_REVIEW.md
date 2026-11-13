# Design stage review: too many sub-steps, no design review (2026-11-13)

The owner, 2026-11-13: "Also review the design stage for each task, seems like too many sub tasks and is the design
reviewed." This note counts what the recent designs produced, checks whether any was reviewed, lists the design
problems found later, and proposes changes; the owner decided them the same day (end of this note). Companion to [TEST_WORKFLOW_REVIEW.md](TEST_WORKFLOW_REVIEW.md); plan row
9.4.7.

## What the designs produced

| Design | Lines | Written | Sub-steps | Owner questions | Independent review before code |
| --- | --- | --- | --- | --- | --- |
| [FRONT_END.md](../design/FRONT_END.md), ADR 0021 | 1,012 | 11-12 16:52, then 44 commits | FE1-FE12, FE1a-FE1i (21) | D1-D3, D5, D7, Amendment 1 | none (ADR still "proposed") |
| [SNAPSHOT_COMPATIBILITY.md](../design/SNAPSHOT_COMPATIBILITY.md) | 656 | 11-12 21:52 | c1-c8 (8) | 4, answered | none |
| [FE1G_TACTICS.md](../design/FE1G_TACTICS.md) | 1,057 | 11-12 22:16 | FE1g-1 to 8 (8) | 3, answered | none |
| [FE1E_APPLICATIONS.md](../design/FE1E_APPLICATIONS.md) | 979 | 11-12 22:24 | FE1e0 to 8 (9) | 2, answered | none |
| [FE1I_AUTOMATION.md](../design/FE1I_AUTOMATION.md) | 854 | 11-12 23:15 | FE1i-1 to 9 (9) | 3, one answered | none |
| [PROOF_DEVELOPMENT.md](../design/PROOF_DEVELOPMENT.md) (research) | 764 | 11-12 23:17 | PD1-PD15 (15) | 3, open | none |
| [FE2_TERMS.md](../design/FE2_TERMS.md) | 922 | 11-12 23:37 | FE2a-FE2j (10) | 3, open | none |
| [VERIFY_COMMAND.md](../design/VERIFY_COMMAND.md) | 822 | 11-13 07:04 | 8.4.1a-n (14) | 6, open | none |
| **Total** | **7,066** | **about 14 hours** | **about 95** | | **none** |

About 16 of those sub-steps have code today: FE1a-FE1d, FE1f, FE6a, FE1g-1, FE1g-2, FE1e1, FE1i-4, c1-c5 and 8.4.1b.
Each design was written by one agent working alone.

**What did get checked:**
- The owner answered plain-language questions: product choices such as syntax, flags and wording, not whether the
  design is sound.
- The Forth reviewer reviewed each implementation, after the code was written.
- For kernel changes, AGENTS.md's gate (ADR, Lean differential, review, the owner's approval) applies at implementation
  time.

No one read a design for correctness, for fit with the other designs, or for its slicing before code started.

## Design problems found late

Each of these was found during or after the implementation, by a later design or an implementation review. A design
review could have found each one earlier.

1. **One growing local context (FE1b).**
   - FE1b's metavariables saw "every free variable made so far". Lean gives each metavariable its own local context.
   - The FE1g design found this. FE1g-1 then rewrote the API, and the term-unification branch (fe1c-3), being written
     at the same time, had to adapt mid-flight.
   - **Missing check:** fidelity to Lean's data model.
2. **Elaboration data format 1 lacked what its next consumer needed.**
   - FE1d shipped format 1 on 11-12 at 20:43. FE1e's design needed classes, instances, reducibility and the unfolding
     facts, so format 2 replaced it the next morning.
   - That cost a second [import][format] gate for the owner.
   - **Missing check:** what the next layers need from this data.
3. **Binder kinds lost through shared term nodes.**
   - The front end needs each binder's implicit or explicit kind, and the hash-consed store keeps one kind per node.
   - Found by the fe1c-3 review (M1, then R1).
   - **Missing check:** whether the data model serves the new consumer.
4. **The snapshot design missed a category.**
   - Changes in how an export is *read* were not in the reach table. That was review finding M2, and S-R was amended
     after the code.
   - Snapshot compatibility took four review rounds.
5. **Two plans changed the same kernel files at once.**
   - The snapshot design and the kernel refactor (FRK) were both planned on 11-12, and both rewrote `env-snapshot.fs`
     and `env-import.fs`.
   - The approved branch could not merge this morning and had to be reconciled by its author.
   - **Missing check:** work in flight on the same files.
6. **Sub-steps that give no usable result.**
   - FE1g-3 (the runner) needs FE1e, the statement elaboration, before any user can run it.
   - FE1i-4 (`lib/bigint.fs`) and `lib/sort.fs` landed with no caller.
   - The 8.4.1 design splits one command into 14 steps.
   - **Missing check:** slices sized by a user-visible result, the rule the owner set this morning.

## Why there are so many sub-steps

- **Designs follow Lean's source file by file:**
  - `discr-keys.fs`, `instances.fs`, `synth.fs`, `elab-pending.fs` and `elab-term.fs` are each a step in FE1e;
  - `omega-hash`, `omega-core`, `omega-proof` and `omega` are each a step in FE1i.
  - That is a good way to port and to read, but a poor unit of delivery: no single file is usable.
- **Each design ends with its own test and documentation step** (FE1e8, FE1g-8, FE1i-9, FE2j, 8.4.1n), so testing is
  scheduled after the code instead of with it.
- **Separate designs per sub-milestone** (FE1e, FE1g, FE1i, FE2), each written alone. Their shared parts were each
  designed in isolation: `mvars.fs`, the elaboration data, the `sorry` report.
- **The sizes were set before the 2026-11-13 rule on user-visible results,** and the plan was never re-cut afterwards.

## Proposals

**1. A design review before code.** An independent reviewer (Opus, not the author) reviews each design once, plus a
re-check if needed, against a short checklist:

- **Lean fidelity:** every ported function names its Lean file, and each data structure matches Lean's (the
  local-context case above).
- **Consumers:** what the next layers need from this data or API, written as a table. This is the format-2 and
  binder-kind case above.
- **Work in flight:** the files other branches or designs are changing, and how the two meet. This is the FRK case.
- **Slices:** each slice gives a result a user or the next layer can use, with its acceptance command; tests and docs
  belong to the slice that needs them, not to a final step.
- **Trust and gates:** the trust boundary, which owner gates apply, and when.
- **Reuse** (owner, 2026-11-13): the libraries and shared words the design uses, the new general-purpose words it
  needs (each a library or shared word, with the existing copies it replaces), and nothing general re-implemented.
- **Size:** a body of about 300 lines that the owner can read; Lean-source notes and long tables go in an appendix.
- **Questions:** the owner's questions extracted, each with a recommendation.

Then the owner approves a one-page summary: what a user can do after each slice, the gates, and the questions. Designs
touching the kernel keep AGENTS.md's ADR gate on top of this.

**2. Designs by milestone, not by sub-milestone.**
- One design document per milestone.
- When pieces are designed separately, they are reviewed together, so shared parts are designed once. For FE1 those
  are `mvars.fs`, the elaboration data and the error codes.

**3. Re-cut the existing plan into user-visible slices.** Proposed cut:

| Today's sub-steps | Proposed slices, each ending in a command a user can run |
| --- | --- |
| FE1e2-FE1e8, FE1g-3, FE1g-4, FE1d2, FE1c lazy delta | **S1, first native proof by `rfl`:** `leanforth check` accepts `theorem t : 0 + 0 = 0 := by-rfl` written in LeanForth, elaborated with Lean's instances, the term checked by the kernel |
| FE1g-5 to FE1g-8 | **S2, FE1 itself:** `0 + n = n` by `by-induction` and `by-rw`, with the step log; FE1's acceptance |
| FE1i-1 to FE1i-3 | **S3:** `by-decide` on the Init examples |
| FE1i-4 to FE1i-9 | **S4:** `by-omega`, Lean's omega by default, improvements behind a flag (owner, 2026-11-13); bigint.fs's first caller |
| FE2a-FE2e | **S5, natural statements:** binders, applications, `let`/`have`/`show`, literals |
| FE2f-FE2j | **S6:** structures and notation, declarations and commands, the natural printer and Init's round trip |
| 8.4.1b, c, d, n | **V1:** `leanforth verify WORD.fs --contract …` for IR 0.1 words with proofs written by Lean, its report, replay and tampering, the user guide |
| 8.4.1e-h | **V2:** the statement written by LeanForth, supplied proof exports, the contract reader and receipt writer in Forth |
| 8.4.1i-k | **V3:** `sorry` in program proofs, receipt 0.5, the SHA helper words |
| 8.4.1l, m | **V4** (after FE5/FE8): proofs by LeanForth tactics, the IR semantics in LeanForth |
| 6.2.5c c6-c8 | **one slice:** mixed versions and snapshot format 2 |
| PD1-PD15 | unchanged: long term, sliced when started |

That is 11 slices in place of about 50 sub-steps on these paths. Work already running keeps its branch and becomes
part of its slice: FE1g-3 and FE1g-4 on `fe1g3` go into S1, and 8.4.1b on `verify-b` into V1.

**4. Review the existing unreviewed designs once, together.**
- The front-end designs (FRONT_END, FE1E, FE1G, FE1I, FE2) get one combined review against the checklist, before S1
  continues past what is already being written.
- VERIFY_COMMAND gets a review before V1 is merged.
- SNAPSHOT_COMPATIBILITY's c6-c8 get one when that slice starts.

## Questions for the owner

1. Add a design review before code (an independent reviewer, the checklist above, and your approval of a one-page
   summary)? *Recommendation: yes.* It catches the six kinds of late problems above at the cheapest point.
2. Re-cut the plan into the proposed slices (11 slices instead of about 50 sub-steps)? *Recommendation: yes.*
   Running work is kept and folded in.
3. Limit a design's body to about 300 lines, with details in an appendix? *Recommendation: yes,* so you can read each
   one.
4. Review the existing front-end designs together now, and VERIFY_COMMAND before V1 merges? *Recommendation: yes.* One
   combined review, about the cost of one implementation review.

## Decisions (owner, 2026-11-13)

The owner chose the recommendation on all four questions: a design review before code with the owner's approval of a
one-page summary; the re-cut into 11 slices; a design body of about 300 lines with an appendix; and a review now of the
existing front-end designs together and of VERIFY_COMMAND before V1 merges. Recorded in
[OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md), "Design stage"; the rule is in AGENTS.md; the slices are in
[PLAN_DRAFT.md](../project/PLAN_DRAFT.md), "Slices".


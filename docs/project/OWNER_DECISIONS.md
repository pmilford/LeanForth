# Owner decisions in plain language

**Status: decided by the project owner on 2026-11-02; answers are recorded
at the end.** This document restates the open review
questions from [the kernel review packet](../reviews/KERNEL_REVIEW.md) and
[the checked environment review](../reviews/CHECKED_ENVIRONMENT_REVIEW.md) for a reader
who does not know Lean, theorem proving or program verification. Each
question gives the background, the options, a recommendation and the reasons.

## A few words first

- **Proof checker ("kernel").** A small program that reads a proof and says
  *accepted* or *not accepted*. Everything LeanForth promises rests on it: if
  it wrongly accepts a bad proof, every result built on it becomes worthless.
  That is why the project rules treat it so carefully.
- **Lean.** An existing, widely used proof system. **Mathlib** is Lean's huge
  shared library of mathematics (well over 100,000 results). LeanForth aims to
  check the same proofs Lean checks, independently, written in Forth.
- **Declaration.** One named item in the library: a *definition* (a named
  value or function) or a *theorem* (a statement plus its proof).
- **Axiom.** A statement accepted *without* proof. Each one is a trusted
  assumption, so the list of allowed axioms must be short and deliberate.
- **Differential test.** Give the same input to LeanForth and to Lean and
  check that they agree. Lean is the reference.

## Why these questions block progress

The project rules say a *human expert* must review the checker's rules before
they are trusted. The only human review so far (2026-10-30) said "continue",
but explicitly left one technical soundness question open. Since then Codex
kept building experiments *around* that gate instead of through it: 51
experimental modules exist, but no checker. Without these decisions the
project cannot reach its next step, the first independently checked
declaration.

## Decision 1 — How do we trust the checker without an in-house expert?

**Background.** The review gate assumes someone who can read typing rules and
judge whether they are correct. If nobody on the project can, the gate can
never be passed, and work stalls or drifts.

**Options.**

1. **Lean is the referee (recommended).** Copy Lean's own published checking
   rules as closely as possible rather than inventing new ones. Accept a
   checker change only when all of these hold:
   - it agrees with Lean on a large and growing set of tests, including
     deliberately broken proofs that must be rejected;
   - an independent AI review of that change finds no unresolved problem;
   - you approve a short plain-language summary of what changed.
   Until an outside Lean expert has audited the checker, every result is
   labelled *"experimental — not independently audited"*. Plan to find or pay
   such an expert before any public claim that LeanForth is trustworthy.
2. **Expert first.** Stop checker work until an outside expert has reviewed
   the rules. Safest, but could stall the project for months and costs money.
3. **AI review is enough.** Fastest, but AI reviewers can share blind spots
   and be confidently wrong. Not recommended for the one component everything
   depends on.

**Recommendation: option 1.** The project's goal is to agree with Lean, so
"agrees with Lean" is the right test of correctness. Test results are
objective; you can read pass and fail counts without understanding the
mathematics. It unblocks the work without pretending an expert has checked
it, and keeps the label honest until one has.

Under option 1, the purely technical designs still awaiting review — how
checked results are stored, how stale references are prevented, and the
internal representations in ADRs 0004, 0005 and 0007 — would be decided by
the same process. My recommendation for storage is the simplest safe design:
the library only ever grows, one check runs at a time, a new entry is added
only after it fully passes, and nothing saved to disk is trusted without being
checked again.

## Decision 2 — What should the first checker accept?

**Background.** Lean has many kinds of declarations: simple definitions,
theorems, recursive functions, data types, and more. The proposal starts
with only simple, non-recursive definitions and theorems. Everything else is
reported as not yet supported.

**Options.**

1. **Narrow start with three outcomes (recommended).** Accept only simple
   definitions and theorems at first. Every check ends in exactly one of:
   *accepted*; *rejected* (definitely wrong); or *unsupported / unknown*
   (could not decide). Only *accepted* ever counts.
2. **Include data types from the start.** More useful sooner, but a much
   bigger first step with more room for mistakes.

**Recommendation: option 1.** It is the smallest step that can be built and
tested properly. Keeping "could not decide" separate from "wrong" stops a
limitation from being mistaken for a disproof, or for success. Data types
should come soon after, because nearly all of Mathlib depends on them.

## Decision 3 — What happens when the checker cannot tell if two things are equal?

**Background.** Checking a proof often means deciding whether two
expressions mean the same thing — for example, a name and the definition it
stands for, or `2 + 2` and `4` after computing. Lean decides this by
"unfolding" definitions and computing. The proposed first checker handles
only the simplest cases and answers *unknown* otherwise. *Unknown* is never
treated as success. The technical question left open on 2026-10-30 concerns
exactly this comparison; the cautious version avoids it, but the next step
must answer it.

**Options.**

1. **Cautious first, unfolding next (recommended).** Ship the cautious
   version, then make unfolding definitions — following Lean's own method
   and tested against Lean — the very next step.
2. **Full Lean equality now.** Fewer *unknown* answers, but a much larger and
   riskier first version.

**Recommendation: option 1.** Being cautious can only make the checker fail
to accept some true proofs; it can never make it accept a false one. But
almost every real Lean proof needs unfolding, so it cannot be postponed long.

## Decision 4 — Which axioms are allowed?

**Background.** Lean and Mathlib rely on three standard axioms that nearly
all mathematicians accept:

- **Propositional extensionality** (`propext`): two statements that each imply
  the other are equal.
- **Choice** (`Classical.choice`): from any non-empty collection you can pick
  an element. Proof by contradiction relies on it.
- **Quotient soundness** (`Quot.sound`): needed to build things like
  fractions from pairs of numbers.

Mathlib cannot be used without them. Lean also has two "trust the compiler"
axioms (`Lean.ofReduceBool`, `Lean.trustCompiler`) that accept whatever
Lean's compiled code computes. They are not mathematical assumptions, and
Mathlib largely avoids them.

**Options.**

1. **None now; the standard three later; never compiler trust
   (recommended).** The first checker allows no axioms; it does not need
   any. When importing Lean's library starts, allow exactly the three
   standard axioms, each with its exact Lean statement. Never allow the
   compiler-trust axioms. Every accepted theorem lists the axioms it depends
   on, and you approve any future change to the list, recorded in a
   versioned file.
2. **No axioms ever.** Purer, but most of Mathlib could then never be
   accepted, which contradicts the project goal.
3. **Allow whatever Lean allows.** Simplest, but quietly trusts Lean's
   compiler, which LeanForth exists to check independently.

**Recommendation: option 1.** It matches what mathematicians and the Lean
community accept, keeps the full-Mathlib goal reachable, refuses the
non-mathematical shortcut, and keeps every assumption visible.

## Recorded answers

On 2026-11-02 the project owner, who states they are not an expert in Lean,
theorem proving or program correctness, answered these four questions in a
Claude Code session. The question text above had SHA-256
`c03d2d6eed88015d069dc4b1260577c0434deeaab9dd75c54411a2be2c743196` before
this section and the status line were filled in.

1. **Trust model: option 1, Lean is the referee.** A checker change requires
   agreement with pinned Lean on positive and negative tests, an independent
   AI review with no unresolved findings, and owner approval of a
   plain-language summary. Results are labelled *experimental — not
   independently audited* until an outside Lean expert audits the checker.
   Technical designs (storage of checked results, stale-reference handling,
   ADRs 0004, 0005, 0006 and 0007) are decided by this same process.
2. **First scope: option 1, narrow start with three outcomes**, with the
   owner's addition: *"should also test the failure paths. unknown/rejected"*.
   Every check therefore needs tests that reach each of *accepted*,
   *rejected* and *unsupported/unknown*, and tests showing that neither
   failure outcome is ever reported or stored as accepted.
3. **Equality: option 1, cautious first, unfolding next.** Unfolding
   definitions, following Lean's method and tested against Lean, is the next
   checker step after the first checked declaration. It must settle the
   conversion question left open on 2026-10-30.
4. **Axioms: option 1.** No axioms for the first checker. When library import
   begins, exactly `propext`, `Classical.choice` and `Quot.sound`, each with
   its exact Lean 4.35.0 statement, may be added to a versioned allowlist.
   `Lean.ofReduceBool` and `Lean.trustCompiler` are never allowed. Every
   accepted theorem reports the axioms it depends on, and the owner approves
   any change to the allowlist.

These answers are policy decisions. They do not approve any implementation,
and they are not an expert review of the checker's rules; that is why
decision 1 keeps the *not independently audited* label.

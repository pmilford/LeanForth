# Kernel review packet

Status: **draft; no kernel rule or implementation is approved by this file**.
An independent AI review found unresolved conversion soundness obligations;
this packet is ready for inspection and discussion, not for implementation
approval. Its findings are in `docs/reviews/2026-10-30-ai-kernel-review.md`.
This packet is for a human decision about the *first small fragment*, not
approval of full Lean or Mathlib compatibility. The detailed rules are in
`docs/adr/0002-core-rules.md` and `docs/adr/0003-conversion.md`.

## What we are proposing

1. Represent a small selection of Lean terms: universe sorts, bound variables,
   function types, functions and applications. A valid expression is not yet
   necessarily a valid proof.
2. Check that an expression has the stated type using the rules in ADR 0002.
   Allow no new axioms in this first fragment. Unsupported Lean features must be
   reported as unsupported, not silently assumed true.
3. Compare types using a conservative algorithm: it can establish equality for
   certain structural and beta-reduction cases, but reports `unknown` when it
   cannot establish equality. Unknown, invalid input, errors and exhausted
   resources never produce an accepted theorem.
4. Keep the checker independent from parsers, tactics, LLMs, importers and the
   Forth runtime used to execute programs. Checking source-level program
   properties does not by itself verify the compiled program or host runtime.

This is a starting point toward Lean/Mathlib support, not an importer or a
claim of compatibility. Lean's full equality rules, universe polymorphism,
definitions, inductives and other features remain outside this first proposal.

## Decisions for the human reviewer

- Are the expression forms, scope and initial lack of axioms acceptable for the
  first implementation, given the long-term requirement for Lean compatibility?
- Do the sort, dependent-function, lambda, application and context lookup rules
  in ADR 0002 agree with Lean on the stated fragment? Are binder shifting and
  capture-avoiding substitution correctly specified, including overflow and
  malformed inputs?
- Is every `equal` result in ADR 0003 sound for its stated preconditions? Can
  unsupported cases, context handling or budget exhaustion accidentally become
  theorem acceptance? Is the explicit incompleteness acceptable initially?
- Are the trusted boundary and proposed Forth memory and runtime assumptions
  clear enough? The mutable prototype is **not** approved as a trusted kernel.
- Which additional tests, implementation details or independent expert review
  are required before implementation and before merging kernel changes?

The reviewer can approve, request changes, or defer. Record the reviewer,
date, reviewed revision and specific scope of approval in a future decision
record. The owner's acknowledgement is recorded in
`docs/reviews/2026-10-30-human-review.md`; later changes need their own review.

## Evidence available now

- The pinned Lean oracle checks valid and invalid core expressions, universes,
  beta reduction, eta and proof irrelevance. The latter two show why the initial
  conversion proposal is incomplete.
- The untrusted Lean transformation model is compared with Lean's shift and
  instantiation operations on generated cases. This is finite test evidence,
  not a proof of soundness or a test of a Forth kernel.
- An untrusted Lean inference model compares its results with Lean's kernel on
  a small generated corpus and identity/composition terms. It uses Lean's own
  instantiation operation and is not a Forth implementation or a soundness proof.
- Forth tests cover experimental storage, scope traversal and incomplete type
  inference, including invalid nodes and budgets. A composition-shaped term's
  inferred type matches its manually constructed claim in the experiment; no
  current Forth component accepts or rejects theorems.
- A separate finite differential test compares seven inferred types and six
  rejected expressions with the pinned Lean kernel. This evidence does not
  resolve the mutable arena or conversion soundness obligations.
- The Lean NDJSON composition fixture reproduces byte-for-byte. Its expression
  records can be staged through a test-only decoder and exercised by an
  untrusted Forth declaration probe; the declaration has not been imported or
  checked by a trusted LeanForth kernel. The probe also exercises the Lean
  reference identity and selected invalid shapes without registering a theorem.

From the repository root, with this machine's pinned tools, run:

```sh
make smoke test-harness test-core test-composition-fixture test-program
ELAN_HOME="$PWD/.tools/elan" make reference reference-export LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make test-scope-differential test-program-differential LEAN="$PWD/.tools/elan/bin/lean"
ELAN_HOME="$PWD/.tools/elan" make test-infer-differential LEAN="$PWD/.tools/elan/bin/lean"
```

These commands require the tools and permissions described in the setup docs.
They must not be represented as a LeanForth kernel acceptance test. The two ADRs
and this packet must be reviewed at a specific revision; the owner's prior
acknowledgement does not approve subsequent implementation changes.

## Independent review

An independent AI subagent reviewed the draft and a subsequent revision.
Findings, follow-up changes and outstanding issues are recorded in
`docs/reviews/2026-10-30-ai-kernel-review.md` and
`docs/reviews/2026-10-30-ai-followup.md`. This is useful adversarial feedback
but does **not** satisfy the project's human-review gate.

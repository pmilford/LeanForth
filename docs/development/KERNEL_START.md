# Starting the kernel

The first kernel is feasible in small steps, but the current ADR is a proposal,
not a complete set of rules. A human has read the overview; a technical review
of the exact rules and trust boundary is still required before implementing
kernel semantics, as specified in `AGENTS.md`.

The first candidate rules are in `docs/adr/0002-core-rules.md`; a conservative
conversion algorithm is proposed in `docs/adr/0003-conversion.md`. Both remain
drafts, including their binder-manipulation algorithms, for human review.
The Lean reference tests do not establish compatibility of LeanForth itself.
The plain-language checklist and review scope are in `docs/reviews/KERNEL_REVIEW.md`.

## What must be decided

1. **What inputs mean.** Define the precise expression forms, variable binding,
   universe levels and well-formed contexts. Specify which Lean features are
   supported and reject everything else.
2. **What makes a proof valid.** Write explicit inference rules, substitution,
   equality/conversion and termination/resource limits. Decide how to represent
   assumptions and guarantee that no unapproved axioms enter a proof.
3. **What is trusted.** Specify the host Forth and memory assumptions, term
   validation, and how a checked result becomes a theorem handle. Decoders and
   tests cannot confer theorem validity.
4. **How to recognize mistakes.** Pair valid examples with wrong types,
   unbound variables, capture, malformed inputs and resource exhaustion.
   Compare supported examples with pinned Lean 4.35.0; Lean source tests alone
   are not yet differential tests of LeanForth.
5. **How to review it.** Have a human with type-theory/kernel expertise review
   the actual rules, acceptance criteria and trust boundary, not just this
   overview. Record decisions and unresolved items before implementation.

The next executable milestone can first demonstrate a representation and
validation of terms without claiming to check proofs. The first proof milestone
must accept a genuine identity or composition proof and reject an invalid one.
The separate program track continues with a contract and runtime semantics;
checking proof terms is not yet a verified executable Forth system.

## What the human review covers

You do not need to approve individual lines of Forth or understand all the
notation in the preliminary overview. The review concerns a concrete proposal
that does not yet exist: exact mathematical rules, how the implementation
enforces them, and evidence from positive and negative tests against Lean.
The reviewer needs to check that invalid terms cannot become accepted theorems,
that assumptions are visible, and that unsupported Lean features fail closed.
Review also covers whether the implementation really matches the stated rules,
and what is trusted about Gforth and memory. A reviewer experienced in Lean or
dependent type theory may be needed; an LLM review alone is not sufficient.

We can prepare the detailed proposal, tests and a readable summary autonomously.
Approval of the project direction or the preliminary ADR is not approval of
rules that have not yet been written. No human review is needed for routine
non-kernel work merely because it is part of the project.

# Kernel — the proof checker, under development

This folder holds the checker as it is developed: universe substitution,
value and comparison; candidate signatures; shift, instantiate, beta
reduction, definitional comparison, conversion and type inference; and the
definition probe that drives them.

**Nothing here is verified yet.** The code is in progress, and it becomes
trusted only when the owner declares it so, after the review gate in
`AGENTS.md`:

1. its rules follow Lean's published kernel behavior;
2. pinned-Lean differential tests agree and reach every outcome (accepted,
   rejected, unsupported/unknown), including deliberately invalid proofs;
3. an independent AI review of the exact change has no unresolved findings;
4. the owner approves a plain-language summary of the change.

Until an outside Lean expert has audited it, every accepted result is
labelled *experimental — not independently audited*. Axiom policy:
`docs/project/OWNER_DECISIONS.md`.

Kernel modules may use `lib/` and `core/`, never `import/`.

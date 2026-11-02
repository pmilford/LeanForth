# Trusted kernel (empty)

This folder is deliberately empty. It will hold the trusted proof checker and
nothing else. Code moves here from `core/` only after it passes the review
gate in `AGENTS.md`:

1. its rules follow Lean's published kernel behavior;
2. pinned-Lean differential tests agree and reach every outcome (accepted,
   rejected, unsupported/unknown), including deliberately invalid proofs;
3. an independent AI review of the exact change has no unresolved findings;
4. the owner approves a plain-language summary of the change.

Until an outside Lean expert has audited it, every accepted result is
labelled *experimental — not independently audited*. Axiom policy:
`docs/project/OWNER_DECISIONS.md`.

# Kernel — the proof checker, under development

This folder holds the checker as it is developed: universe substitution,
value and comparison; candidate signatures; shift, instantiate, beta
reduction, definitional comparison, conversion and type inference; the
definition and theorem probe that drives them; the checked environment and
its publisher; and the first checker, `check-declaration.fs` (plan task
2.2.3), which the publisher runs for each declaration: the audit (U1, U2,
V1), then the name, the universe parameters, inference in environment mode
(constants and universe arguments looked up in the environment in Lean's
order, `env-signature.fs`) and the final comparison. Inference and the
probe answer *rejected* by the rules of
[ADR 0011](../../docs/adr/0011-definite-rejection.md) (S1–S3, F1, D1–D5;
the head kinds those rules read are in `mixed-head.fs`, the level tests in
`level-value.fs`), the environment by N1, N2 and L1–L3, the declaration
audit *unsupported* by U1 and U2; every other failure stays *unknown*,
*invalid*, *exhausted* or *full*. Universe levels are built and compared
exactly as Lean's kernel does (ADR 0011, Amendment 1): `level-make.fs`
ports Lean's `mk_max`, `mk_imax` and structural level equality,
`level-normalize.fs` its `normalize`, name order and `is_equivalent`,
which `level-compare.fs` (conversion, rule D1) uses; `mixed-infer.fs`
types a Π with `mk_imax`, and `level-substitute.fs` specializes a
constant's type as Lean's `instantiate` does. A new place that builds a
level where Lean's kernel builds one must use the same ports.

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

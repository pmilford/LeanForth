# Independent AI review of kernel proposal

Reviewer: separate Codex subagent, 2026-10-30. This is an AI review, not the
human review required by `AGENTS.md`. It reviewed the then-current worktree,
not a committed revision. Its reviewed ADR SHA-256 hashes were:

- ADR 0002: `3382cca0ee17b1060edb87ab1af0d4fbd26363ba21e3b228a9afc11e5502478c`
- ADR 0003: `f428aa3f0366df3eab1a2e18963eed7a4d896e076110348a5f4a620fee2b9226`

The reviewer found no demonstrated unsound typing rule in the narrow fragment,
but did not recommend approving a kernel implementation yet. Its key findings
and follow-up status are:

1. **High: missing declaration acceptance contract.** The prior typing draft
   did not specify checking the declared type, value and final conversion, or
   distinguish theorems from definitions. A candidate contract and direct Lean
   kernel declaration cases have since been added to ADR 0002 and
   `tests/reference/declaration-oracle.lean`. The contract and its eventual
   implementation still need human review, including resource and unknown cases.
2. **High: conversion preconditions and binder contexts are underspecified.**
   The review identified an unresolved context-conversion and circularity
   question, not a demonstrated counterexample. ADR 0003 now states that
   well-typed inputs and a context-conversion argument are required and marks
   them unresolved. The Lean oracle now checks beta-equivalent binder domains
   and demonstrates that equality of an ill-typed term is not type checking.
3. **Medium: mutable prototype counts could permit out-of-bounds accesses.**
   `src/core/terms.fs` and `src/core/arena.fs` now validate allocation counts
   before public reads or allocation. Tests deliberately corrupt counts on both
   sides of the valid range. Raw address helpers and mutable storage remain
   untrusted and unsuitable as a protected theorem store.
4. **Medium: no LeanForth negative proof tests exist.** Correct: there is no
   LeanForth type checker yet. Lean oracle tests and Forth scope tests are not
   substitutes. A future checker needs valid/invalid declaration pairs and
   explicit unsupported, malformed and exhausted-budget tests.
5. **Medium: portability and CI coverage remain incomplete.** The prototypes
   require Forth word sets and file loading beyond an established core-only
   boundary. The updated local workflow has not run on GitHub and does not yet
   run the pinned Lean suites. Two Gforth versions on one architecture are not
   independent Forth implementations or cross-cell-width evidence.
6. **Low: stale handles and mutable internals.** Reset can reuse an index; the
   prototype has no protected immutable claim store. The eventual checked-handle
   interface needs lifetime, mutation, forgery and concurrency tests.

The subagent reported that its Gforth 1.0 `make test-core` run passed with a
temporary HOME, as did pinned Lean reference tests and the 64-case scope
differential. It did not run a second Forth implementation, GitHub CI, export
validation, or a LeanForth kernel differential test. Its initial Gforth run
with default HOME failed at startup. It made no changes.

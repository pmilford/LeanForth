# Forth reviewer guide

Use this guide for a focused human or agent review of LeanForth Forth code. It
is a checklist, not an autonomous reviewer, a proof, or a replacement for the
project's required human reviews. Read `AGENTS.md` and the applicable contracts,
design decisions, module comments and tests first. Establish the exact change
and its callers; inspect dependencies where their stack effects, guarantees or
status codes matter. Review both the theorem and executable-program trust
boundaries when relevant.

## Review procedure

1. Identify public words, internal helpers, state and ownership. Record the
   intended stack effects, inputs, outputs, failure modes and assumptions. Follow
   each public call through validation, mutation and result production.
2. Trace the data stack on every branch and exit, including variable-arity
   success/failure results. Trace return-stack use through loops, `EXIT`,
   `UNLOOP`, and calls; check loop bounds, empty ranges and nesting. Verify flags
   are consumed correctly and that callers use the actual returned convention.
3. Check idiom and factoring: words should have a clear purpose, useful names,
   and usually be short enough to trace. Suggest named helpers for repeated
   operations or distinct responsibilities when they clarify contracts and state
   flow. Avoid unnecessary stack juggling, hidden dependencies and global scratch;
   when scratch is intentional, check initialization and reentrancy. Do not
   shorten code by dropping validation, obscuring control flow, weakening resource
   bounds, or hiding a trust boundary. A longer explicit word can be preferable.
4. Examine cell arithmetic, signed versus unsigned comparisons, overflow,
   alignment, address arithmetic, capacities, initialization and lifetime.
   Check array and arena bounds before access; identify caller-owned storage and
   aliasing assumptions. Check repeated calls, resets, stale handles and identity
   reuse, plus concurrent or nested calls if the contract permits them.
5. Follow every error path. Malformed input must fail closed, and exhaustion,
   invalid input, unknown results and success must stay distinct. Check stack
   cleanup, loop cleanup, rollback and what state may change on failure. Verify
   cross-module status mappings explicitly rather than assuming equal numbers.
6. Assess Forth-2012 portability word by word, including required word sets,
   environmental dependencies, cell width, numeric base, alignment, signed
   representation and implementation-defined behavior. Identify host extensions
   and their adapters. A source inspection is not a cross-host portability test;
   report exactly which hosts and versions were actually exercised.
7. Check comments on modules and public words against behavior: stack effects,
   ordering, types and units, ownership, side effects, failures, resource limits,
   assumptions, loading dependencies and non-obvious algorithms. Keep internal
   helpers' preconditions visible. Comments must distinguish checked facts from
   unchecked inputs, structural validation and host/runtime assumptions.
8. Read the tests and identify missing meaningful cases: positive and negative
   behavior, each branch and stack shape, limits, malformed input, overflow,
   stale state, reentrancy assumptions and failure after partial mutation. Use
   sentinels or depth checks where useful for both stacks. For shared DAGs,
   test resource behavior and explicitly stated fuel semantics. Run relevant
   existing tests when the host is available; record commands, versions, results
   and any unavailable tools. Do not infer passing tests from their presence.
9. Trace authority: parsing, imported declarations, structural checks and
   generated explanations never establish theorem validity. Verify that only the
   trusted checker can do so and that axiom policy is explicit. For programs,
   separate source semantics and proof from host execution and compiler or FFI
   assumptions. Review changes to kernel semantics, imports, certificates,
   axioms, bypasses, compiler/FFI assumptions and mathematical parsing under
   the human review gates in `AGENTS.md`; an agent review cannot waive them.

## Findings and handoff

Report findings first, ordered by impact: correctness and trust risks, then
portability, maintainability and test gaps. Give a path and line, the concrete
trigger, consequence, and a practical remedy or test. Distinguish demonstrated
bugs from potential risks, documented limitations and style suggestions; do not
invent a failure. Note well-factored code when no improvement is justified.
Include the review scope, commands and observed tool versions, tests actually
run, and limitations. For kernel-semantic changes, identify the required ADR,
positive/negative tests, pinned Lean comparison and human review. Never claim
that review or test execution proves correctness.

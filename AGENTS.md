# Agent instructions — LeanForth

Read `docs/CODEX_HANDOFF.md`, `docs/IMPLEMENTATION_PLAN.md`, `docs/INTERFACE_CONTRACTS.md` and this file before making architecture changes. Treat this as a formal-methods and systems-programming project, not a normal code-generation project.

## Non-negotiable design decisions

- The goal is a finished, usable LeanForth product: a Lean- and Mathlib-compatible theorem prover and a checker for provably correct executable Forth programs. Experiments and prototypes are temporary development stages, not the intended deliverable; carry work forward toward production-quality implementations, documentation and tests.
- The canonical language is ordinary Forth tokens and words; mathematics is represented as typed AST/data. Mathematical brackets, subscripts and infix symbols belong to an external notation/editor/rendering layer, not the canonical Forth grammar.
- The project must develop **two equally visible product paths**: theorem proofs and verified executable Forth programs. Each early milestone should show both if technically feasible.
- Small **trusted kernel** checks all proof terms. Parsers, LLMs, tactics, proof explanations, MathJSON/LaTeX adapters, solvers, fast compilers, GPU backends and tensor libraries are **untrusted** and can never confer theorem validity.
- Never make an unchecked theorem true by asserting it as an axiom, treating a failed check as success, bypassing the kernel, or silently changing the specification. Preserve an explicit, audited axiom allowlist.
- Program correctness means correctness against **stated semantics and assumptions**. Compiled code and external numerical backends are not automatically verified by a proof of the source program. Report assumptions, trusted runtime boundaries, floating-point caveats and any incomplete backend validation.
- LLM-facing APIs must be versioned, deterministic where practical, documented with JSON Schema and structured error codes, scriptable and operable without chat/UI.
- Proof steps should carry source IDs and derivation/certificate references. Explanatory prose is not a substitute for checked derivations; tag reconstructed or LLM-generated explanations clearly.
- Tensor work must use explicitly typed shapes, strides, element types, ownership/lifetimes, memory placement and effect/aliasing contracts. CPU fallback is mandatory; never put a GPU in the trusted kernel.
- Prioritize portability: Forth-2012 core compatibility, Gforth 1.0 as a development host, Linux/WSL CI, and architecture-independent serialized terms.

## Work process

- After each meaningful milestone, update `docs/PROJECT_PROGRESS.md` and report both approximately ten-milestone tracks, their overlap, NDJSON support, code inventory, and relevant verification and limitations.
- Develop and maintain user manuals, installation, contributor, testing and interface documentation alongside each feature; distinguish implemented behavior from plans and state trust boundaries.
- Use scoped independent subagents when they materially improve parallel work or reviews, especially for Lean, Forth and kernel integrity. Measure usage where feasible; subagents do not necessarily save tokens and cannot replace required human review.
- Document Forth modules and public words with readable comments, including stack effects, behavior, error cases and relevant assumptions. Explain non-obvious implementation details where helpful.
- **First task: environment, repository foundation, specification, CI skeleton and honest smoke tests — not a fabricated theorem prover.** Follow `prompts/FIRST_CODEX_TASK.md`.
- Divide later work into narrowly scoped issues and test-first changes. Keep a running `docs/DECISIONS.md` with rationale and rejected alternatives.
- Before changing kernel semantics: propose an ADR; add positive/negative tests; compare with pinned Lean 4.35.0 on available cases; request human review. Do not merge kernel changes solely on LLM review.
- Do not claim a check/benchmark/platform test was run if it was not actually run. Document missing tools and blocked tests.
- User approval is required for GitHub authentication/remote creation/push, external service authorization, destructive actions, installing system packages with privilege, and adding new runtime/network dependencies.
- Record all commands used, observed versions, exact CI status and reproducibility hashes. Do not commit secrets, private keys or credentials.
- Use `scripts/check-env.sh` to collect a safe, read-only inventory of the development environment.

## Review gates

Kernel integrity, declaration import, proof certificate formats, new axioms, verifier bypasses, compiler/FFI assumptions and mathematical parser semantics require explicit human review. All malformed-input tests must fail closed. Maintain at least one acceptance test that constructs a valid proof and one that rejects an invalid proof, once the minimal kernel exists.

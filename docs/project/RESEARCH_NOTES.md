# Initial research outcomes, unresolved questions and source map

This is a brief carry-over of the completed first Deep Research report, not a substitute for it.

1. **Lean 4 is the current main language** (Lean 4.35.0 stable as of 2026-10-30; 4.36.0-rc2 announced). Lean's rich notation elaborates to a small core type system checked by a kernel. C remains a normal compiler backend; LLVM also exists. Lean 4.35 adds `vcgen` and independent checking infrastructure (`lake check --paranoid`).
2. **Lean NDJSON export** is a much better interoperability target than `.olean` or source parsing, because it includes elaborated declarations/proof objects. The format page currently describes version 3.1.0; pin metadata and test incompatible inputs.
3. **Gforth 1.0.0** (released 2026-10-25) is a practical open-source Forth host. Constrain trusted core words to portable Forth-2012 where feasible. Consider SwiftForth / VFX Forth as independent performance/portability tests in later phases.
4. **TensorForth** establishes Forth/GPU feasibility but is not a trustworthy or portable foundation for LeanForth. Arithmetic/tensor GPU work belongs behind an optional untrusted backend, after CPU and host Forth execution paths.
5. **Kernel acceleration**: sharing, compact representation, memory arenas, memoization and parallel independent checks are likely more promising initially than GPU. SIMD/BLAS/GPU are highly useful for large verified programs/tensors and selected proof-generation workloads.
6. **Caveat:** a formally checked source specification is not automatically an independently proven compiler, linked native library or floating-point GPU implementation.

## Questions for ADRs

- Is proof validity represented only as checked proof-term hashes, as opaque theorem handles issued by the kernel, or both?
- What is the exact Forth binder/quotation discipline (avoid stack capture and implicit syntactic modes)?
- Which expression DAG representation gives the best portability/speed/inspectability?
- How much of dependent Lean compatibility is needed for useful verified Forth before all of Mathlib works?
- How do theorem hash IDs, explanation step IDs and source maps survive independent import, print and edit cycles?
- Which numerical semantics are to be formally proved: exact arithmetic, fixed-width integers, IEEE-754 bounds, or assumption-based BLAS contracts?
- Should MathLive be optional web UI only, or also ship in a desktop extension?
- Licensing: original LeanForth own code, Gforth runtime interaction and bundled BLAS/ArrayFire dependencies must be audited before setting final license.

## Reference links

- https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/
- https://lean-lang.org/doc/reference/latest/The-Type-System/
- https://lean-lang.org/doc/reference/latest/releases/v4.35.0/
- https://lean-lang.org/fro/roadmap/y4-1/
- https://github.com/leanprover/lean4export/blob/master/format_ndjson.md
- https://gforth.org/
- https://forth-standard.org/
- https://github.com/chochain/tensorForth
- https://mathlive.io/mathfield/guides/interacting/
- https://mathlive.io/compute-engine/guides/latex-syntax/
- https://arrayfire.org/docs/unifiedbackend.htm
- https://docs.github.com/en/github-cli/github-cli/quickstart
- https://help.openai.com/en/articles/11369540-using-codex-with-your-chatgpt-plan

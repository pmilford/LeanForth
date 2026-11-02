# LeanForth — complete project brief and Codex handoff

**Prepared 2026-10-30.** This document is a requirements-and-architecture starting point, not an implemented language, proof checker or verified runtime. It incorporates three consecutive LeanForth discussions and the completed initial Deep Research report. The user is ready to start actual implementation with Codex.

## 0. Mission and first principles

Develop **LeanForth**, a clean and ergonomic Forth-native environment for:

1. authoring mathematical definitions, propositions and proofs, and **independently kernel-checking** the resulting proof terms;
2. specifying, checking, compiling and **efficiently executing verified Forth programs**;
3. importing already-elaborated Lean 4 declarations and Mathlib proofs through an official machine interchange format, aiming over time for faithful semantics and progressively broader corpus compatibility;
4. allowing humans, mathematical notation editors and **LLMs/coding agents** to author and inspect proofs/programs through well-documented interfaces;
5. expressing and running large matrix/tensor computations, efficiently on CPU immediately and with optional accelerator backends when beneficial;
6. producing **readable, step-by-step proofs**, mathematical pretty-printing and textual descriptions of why each step follows, while clearly distinguishing checked mathematical facts from explanatory prose.

### User's distinctive language rule

**Forth is the language, mathematics is its data.** The Forth lexer/parser has one unambiguous meaning for every token/delimiter. A bracket must never mean one thing in LeanForth source and something unrelated in embedded math grammar. Canonical forms use Forth words, literals and stack values to construct typed mathematical ASTs; readable math notation is handled by explicitly isolated editors/importers and by printers. Human-friendly structured Forth declaration words are allowed, provided they are still Forth words and do not create implicit competing punctuation grammars.

We are **not** recreating Lean's parser or adopting its mathematical notation in the canonical language.

### Trust philosophy

A small, reviewable, Forth-hosted kernel checks proof terms and declarations against a Lean-compatible dependent-type calculus. Parser, elaborator, tactics, rewriting engines, LLMs, external mathematical editors, proof explanations, compiler, JIT, numerical libraries, GPU and SMT solvers are **outside** the trusted mathematical proof kernel. They may propose proof objects or certificates; only the checker can authorize a theorem. Imported declarations are never treated as true solely because they came from Lean or were parsed successfully.

The **runtime assurance** story is separate. Proof-checking a program's *specification and source semantics* does NOT alone prove that an optimizing native/BLAS/GPU backend faithfully executes them. State that distinction in API status, docs and output. Initially, Forth/FFI/BLAS run under explicitly declared assumptions. Introduce backend equivalence proof or validated compiler passes when feasible.

## 1. Scientific and technical foundation

Lean 4 is the reference logical target. As of 2026-10-30, **Lean 4.35.0** is a stable version to pin; a Lean 4.36 release candidate is available but should not silently replace the baseline. Lean uses an elaborator to compile rich surface notation to small core expressions, checks those with a kernel and compiles executable code through compiler IR, with C as a normal backend and LLVM support present. Lean's 4.35 `vcgen` direction makes verified programming especially worth analyzing. The project must compare its approach with Rocq/Coq, Agda, Idris 2, Isabelle/HOL, HOL Light, ACL2, F*, Dafny, Why3, SPARK/Ada and Verus, but these comparisons must not distract from writing an independent checker.

**Major interoperability advantage discovered in research:** the official [Lean 4 NDJSON export format](https://github.com/leanprover/lean4export/blob/master/format_ndjson.md) (currently described as format v3.1.0) exports names, universes, expressions and declarations with proof values. Lean 4.35 adds `lake check`, `--from-export` and `--paranoid` for cross-checking with independent kernels. Pin the exact Lean version, export format and corpus revisions in version-controlled manifests. **Do not reverse-engineer `.olean` as the initial import path.**

Baseline implementation: **Gforth 1.0.0** on Ubuntu WSL2 for interactive development, backed by a deliberate Forth-2012-compatible subset in portable kernel modules. Consider SwiftForth and VFX Forth only after functionality exists and cross-runtime tests demonstrate portability. Compare a tiny C-hosted Forth as an audit/embedded port in later phases. Avoid introducing Gforth-only constructs into the logical core unless wrapped in platform adapters.

## 2. Architecture: two product paths, one logic

```text
                     Humans, Codex / LLM agents, APIs
                            |          |
                  MathLive/LaTeX     Forth source
                            |          |
                      notation adapter  |
                            \          /
                           semantic elaborator
                                  |
         Lean NDJSON --> versioned core IR / term DAG <-- proof tactics
                                  |
                         TRUSTED TYPE KERNEL
                          /              \
                 proof store          verified-program IR
                     |                  |         |
                proof steps        Forth runtime   C/BLAS/GPU
                explain/print       (CPU first)     optional

Trusted theorem boundary: checked AST and kernel only.
Execution trust: separately tracked for interpreter / compiler / native libraries.
```

Define independent modules/wordlists (`LF.CORE`, `LF.KERNEL`, `LF.ENV`, `LF.ELAB`, `LF.PROOF`, `LF.TACTIC`, `LF.PP`, `LF.EXPLAIN`, `LF.VERIFY`, `LF.EXEC`, `LF.TENSOR`, `LF.LEAN`, `LF.IO`, `LF.LLM`). Names are provisional, subject to an ADR and canonical stack-effect tests.

### Portable memory and performance

Represent expressions using compact, architecture-independent tagged DAG nodes and de Bruijn variable indices. Develop explicit name/level tables, hashing, sharing, memory arenas, cached weak-head normal forms, overflow detection, deterministic serialization, locality and per-module resource budgets. Never serialize host pointers. Profile before optimization. Host-specific memory, clock, concurrency, file I/O, FFI, SIMD, compiler and GPU words sit behind one small interface.

## 3. A CLEAN Forth vocabulary

The code below is **illustrative design notation**, not running implementation:

```forth
\ (source words) : AST constructors and checked registration
Nat const                  \ push Nat type AST
x variable                 \ allocate a binder descriptor
x ref                      \ construct variable reference
x lam                      \ lambda abstract term on stack
x pi                       \ dependent function AST
name type proof theorem!    \ checked registration; rejects invalid proof
```

Do **not** commit to specific words until stack effects, binder hygiene and source maps have been designed and covered by unit tests. Use explicit quotations only when their syntax has a single Forth-language role. If an external editor displays `∀ x : Nat, P x → Q x`, that notation is an external UI representation and *must not* be reinterpreted as a second implicit Forth grammar.

## 4. Priority A — explainable mathematical proofs and pretty-printing

Support structured, stable proof-step records independently of rendering. Each displayed step has:

- `step_id`, proof/declaration `id`, source span where available, target/conclusion AST identifiers and current hypotheses;
- `rule` / inference kind (`intro`, `refl`, `apply`, `rewrite`, `definitional_equal`, `induction`, etc.), precise premise step IDs, lemma/declaration references, substitution/binder mapping and certificate/proof-term hash;
- checker status (`accepted`, `rejected`, `unchecked`), axiom assumptions, warnings and resource use;
- a short *why this follows* explanation linked to the actual checked rule and referenced lemmas;
- explanation provenance (`structured-template`, `author-supplied`, `reconstructed-from-proof-term`, `llm-generated`) and confidence or limitations separate from validity.

Outputs required: compact pretty Forth; human mathematical format (Unicode/LaTeX/MathML); expandable line-by-line mathematical proof with plain-English explanations; machine JSON; Markdown/HTML export; source-to-step navigation later. Avoid fake reasoning: the explanation says "by reflexivity of equality" only when the checker can link to a valid reflexivity term. For tactic-generated or imported proofs, original human reasoning may be lost: reconstruct useful derivation slices from the term DAG, not assert that the original author used a specific step.

The printed claim must preserve the proposition's semantics. Test alpha-renaming, scope/binder escaping, operator precedence in display, universes, implicit arguments, notation ambiguities, Unicode escaping, and huge proof DAGs; support truncation/expansion, stable IDs, human-mode vs full-core-mode and re-parse tests where input format permits them.

**Acceptance demo:** given a constructed `∀ x : Nat, x = x` proof, the UI displays a theorem heading and numbered steps such as:

```text
Goal: For every natural number x, x = x.
1. Choose an arbitrary x : Nat.          [∀-introduction; accepted]
2. Conclude x = x.                       [equality reflexivity; accepted]
3. Since x was arbitrary, ∀ x : Nat, x=x. [∀-introduction; accepted]
```

The exact proof-term construction must be checked; the prose must map to proof objects and not just be generated from a vague goal description. The same proof should export structured JSON with lemma IDs and hypothesis references.

See `docs/programming/INTERFACE_CONTRACTS.md`.

## 5. Priority B — external mathematical notation input and interchange

**Recommended initial editor: [MathLive](https://mathlive.io/)** with [CortexJS Compute Engine](https://mathlive.io/compute-engine/guides/latex-syntax/). It supports editable mathematical input, LaTeX and MathJSON interchange, which are more suitable for a separate math frontend than inventing a second parser inside Forth. MathJSON captures expression structure but is **not** in general a fully typed theorem term, nor is LaTeX. Build a deterministic, inspectable adapter that resolves operations, variables, scoping and types against a LeanForth environment and fails when ambiguous.

Potential later inputs: MathML (presentation, and possibly content-oriented markup), direct LaTeX snippets, OpenMath-like semantic representations and Mathpix/MathType-style handwriting/editor import. Investigate license/API/data/privacy/format limitations before selecting dependencies. Reserve canonical logical AST serialization and explicit Forth words as the interchange of truth, never the math editor's appearance or heuristic parse.

Flows:

```text
MathLive UI -> LaTeX/MathJSON -> lexical/semantic mapping -> LeanForth AST
LeanForth AST -> pretty printer -> LaTeX/MathML/MathJSON + provenance
```

Roundtrip corpus: simple arithmetic, quantifiers and dependent binders, equality, natural-number induction, matrices/tensor indices, subsets and implicit multiplication; negative tests for ambiguous `xy`, `f(x)`, superscripts, binder collisions, overloaded `+` and ill-typed expressions. Initial MathLive integration can be a small browser demonstrator or design-only until the LLM/AST contracts stabilize. **No mathematical input format bypasses elaboration or kernel checking.**

## 6. Priority C — first-class LLM interaction and documentation

Assume Codex/LLMs will be major consumers of LeanForth. Provide a **stable, versioned, machine-first interface** instead of forcing the model to scrape unstructured REPL output. Start with a process-local, stateless-where-possible **JSON-RPC 2.0 over NDJSON stdin/stdout** CLI; no network listener by default. Eventually expose the exact same schemas as MCP tools and integrate with VS Code/LSP. Document:

- manifest/version negotiation and `capabilities`;
- `parse` / `elaborate` / `type.infer` / `goal.list` / `proof.propose` / `proof.check`;
- `proof.steps` / `proof.explain` / `proof.pretty`;
- `program.verify` / `program.compile` / `program.run` / `program.benchmark`;
- `tensor.describe` / `tensor.plan` / `tensor.execute` / `tensor.benchmark`;
- `lean.import.preview` / `lean.import.check` / `library.search`;
- diagnostics with code, location, expected/got types, source map, deterministic seed, available symbols, suggestions and failure category.

Every request returns version, request/correlation ID, status, machine-readable diagnostics and **the exact checked claim**, if any. Make `checked`, `under-assumptions`, `runtime-tested`, `unverified` distinct fields rather than a single misleading `success: true`. JSON Schema files and 10+ golden request/response pairs must live under `schemas/` and `examples/api/`; invalid/malformed requests must fail closed. Sessions are explicit IDs; transactions for mutable environments; deterministic replay logs and bounded resources. Never execute generated Forth code as part of parsing/checking an imported proof without a sandbox and explicit user action.

Provide short **LLM guide**, **proof-authoring cookbook**, **stack-effect reference**, **error-code catalog**, **tool/API reference**, **import guide** and **verified-program guide** with copyable examples. LLM-assisted proof construction uses propose -> elaborate -> checker -> counterexample/diagnostic feedback; agents cannot assert theorems or suppress failed checks.

## 7. Priority D — verified, efficiently executable Forth programs

This is **a parallel primary track from Sprint 1**, not a much-later optional add-on. Support an understandable distinction between ordinary Forth words, total verified computations, and explicitly trusted external effects. Design **effect/contract vocabulary** for stack effects, preconditions, postconditions, loop invariants, memory bounds, integer overflow, floating-point behavior and array/tensor shape checks. A small verification-condition (VC) generator can initially support a tiny pure, total subset; expand via weakest preconditions, refinement/dependent types and effect semantics. Examine Lean 4.35 `vcgen` and F*/Dafny/Verus for ideas.

Proposed three modes:

- `CHECK`: kernel checks definitions/proofs, never executes arbitrary code. Fail closed.
- `VERIFY`: type/contract checking plus VC generation; successful checks produce a durable proof artifact and a list of external assumptions.
- `RUN`: execute the verified definition with interpreter or compiled Forth, explicitly identifying whether the **compiled backend has been validated/proved**. Optionally enforce runtime assertions/bounds for external inputs.

Compiled programs should normally run at native speed for their kernels, not interpret individual mathematical AST nodes for every data element. Separate (1) pure verified semantic IR, (2) proof erasure/code generation to host Forth, (3) efficient native C/FFI backend and (4) optional future compiler-correctness or translation-validation proofs. Maintain benchmark parity with equivalent baseline Forth/C wherever possible and make measured regressions visible. Do not use floating-point approximations as proof of exact real-number equalities.

**Early acceptance goal:** a trivially typed identity or bounds-checked scalar function is (a) specified, (b) checked by real kernel/VC logic, (c) executed as Forth code on sample inputs, (d) yields an explanation and (e) produces a verifiable JSON receipt. Never call a test-only stub a "verified execution".

## 8. Priority E — efficient matrix and tensor computation at scale

The tensor system must be **designed in parallel** with verified-program execution. Forth handles pipeline/control and verification; optimized native libraries handle bulk numerical loops. The tensor contract includes: element dtype, rank, shape, stride, storage layout, axes, units/semantics where appropriate, mutability, ownership, aliasing, device, precision/rounding mode, and resources. For FFI avoid element-by-element callbacks into Forth; batch operations into BLAS/GEMM, batched GEMM, convolution, map, reductions, contractions, slicing, broadcasting and streaming blocks.

**Stage 1:** pure Forth reference implementation for tiny fixed-size arrays and a CPU native provider using CBLAS/OpenBLAS or BLIS, with documented FFI and golden tests against a high-precision or independent numerical oracle. Test float32/64, int32/64, overflow, NaNs, layout, zero dimensions and memory limits.

**Stage 2:** a vendor-neutral tensor provider interface supporting CPU first, then possibly [ArrayFire](https://arrayfire.org/docs/unifiedbackend.htm) (CPU/CUDA/OpenCL/oneAPI backends) after assessing its current license/quality/packaging; alternatively direct CUDA/HIP/OpenCL plug-ins, oneAPI or a portable CPU optimized C backend. GPUs are optional acceleration, not a correctness requirement.

**Stage 3:** formal shape/bounds/aliasing proofs, exact discrete operations where possible, special verified kernels and quantified numeric error bounds where feasible. Clearly mark BLAS/GPU arithmetic as **external runtime assumptions** until independently verified or translation-validated. Tensor shapes/indices may be verified even when floating-point numerical values rely on unverified external operations.

**Benchmark targets** should include 1k-10k vectors, 256²/1024²/4096² matrices when hardware permits, batched small GEMMs, transpose vs strided memory, streaming out-of-core datasets, speedup compared with scalar Gforth, CPU BLAS and, when available, GPU including host-device transfer overhead. Publish performance per hardware/BLAS version and allow reproducible workload seeds. Don't promise speedups before benchmarking.

## 9. Import pipeline and differential testing

Pin Lean 4.35.0, exact `lean4export` NDJSON schema, core tests and Mathlib commit separately. Initial implementation reads **Lean 4 NDJSON export**, reconstructs core AST DAG and independently checks each declaration. On supported subsets compare positive/negative acceptance with Lean `leanchecker`/`lake check --paranoid`, checksums, axiom lists, universe instantiations and declaration types; do not import a proposition as a trusted axiom merely to make tests green. Fuzz export streams: duplicates, invalid offsets, cyclic references, oversized literals, nested expressions, hash collisions and invalid recursor data. Stream large libraries, set resource ceilings and isolate untrusted inputs.

Source-level translation from `.lean` comes later. The primary objective is kernel parity on Lean core terms and imported proofs; it is not reproducing the entire Lean surface parser or Mathlib tactics.

## 10. Execution environment, repository and Codex

**Target environment:** Windows 11 host / WSL2 Ubuntu guest / Gforth 1.0.0 / Forth-2012 portable kernel subset / Lean 4.35.0 via elan / VS Code (Windows + WSL extension) / GitHub private repo / Codex CLI and/or IDE integration. All repositories live under Linux `$HOME`, for example `~/src/LeanForth`; no editing under `/mnt/c` for performance-sensitive builds.

First user-visible actions: install WSL if absent; install build tools, Git/GitHub CLI and Gforth; install current Node LTS and Codex in WSL; sign in interactively; create local Git repository; pin Lean; request permission for GitHub remote. Start with a **private** remote unless user approves publication. Set up GitHub Actions for Ubuntu first, then multi-OS/arch with actual support and no false-green jobs. Require human review for kernel/axiom/FFI-sensitive changes, and maintain architecture decision records.

A handoff that only says "build LeanForth" is insufficient. Codex must use the specific first-task prompt and issue-by-issue acceptance criteria in this package.

## 11. Non-goals and realistic staging

- No claim to reproduce all Lean 4/Mathlib features in one sprint. Dependent-type kernel correctness and parity are major long-term work.
- No arbitrary mathematical notation in canonical Forth source or overloaded brackets.
- No GPU in trusted theorem kernel, no blanket trust in tensorForth, no early dependency on CUDA.
- No unreviewed axiom additions, `sorry`, `admit`, magic proof acceptance, or fake green tests.
- No claim that checked source programs imply verified C/JIT/GPU artifacts without a separate argument or explicit assumption.
- No reliance on LLM-generated prose as mathematical proof.
- No automatic push, service authorization or privileged installation without the user's approval.

## 12. References used for the handoff (check versions and licenses again when installing)

- Lean reference: https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/ and https://lean-lang.org/doc/reference/latest/The-Type-System/
- Lean 4.35 release with `vcgen`, `lake check`, `--paranoid`: https://lean-lang.org/doc/reference/latest/releases/v4.35.0/
- Lean NDJSON v3.1.0: https://github.com/leanprover/lean4export/blob/master/format_ndjson.md
- Gforth v1.0: https://gforth.org/ and https://gforth.org/manual/1.0/
- Forth portability: https://forth-standard.org/
- MathLive: https://mathlive.io/mathfield/guides/interacting/ and https://mathlive.io/compute-engine/guides/latex-syntax/
- Tensor backend option: https://arrayfire.org/docs/unifiedbackend.htm
- WSL development: https://learn.microsoft.com/en-us/windows/wsl/setup/environment
- VS Code WSL: https://learn.microsoft.com/en-us/windows/wsl/tutorials/wsl-vscode
- GitHub CLI: https://docs.github.com/en/github-cli/github-cli/quickstart
- Codex getting started: https://help.openai.com/en/articles/11369540-using-codex-with-your-chatgpt-plan

**Immediate next action:** read `prompts/FIRST_CODEX_TASK.md` and implement only the approved environment/repo/bootstrap steps. The user remains the final decision maker on repo visibility, licenses, external dependencies, platform changes and kernel correctness choices.

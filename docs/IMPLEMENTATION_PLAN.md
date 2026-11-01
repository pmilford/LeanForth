# LeanForth implementation roadmap for Codex — staged and test-gated

**Plan status: proposal.** Dates are intentionally replaced by correctness/acceptance gates; time estimates on a new theorem checker are not reliable. Keep **theorem-checking and verified-program execution equally visible** at every design review.

The long-term target is to use Lean and Mathlib as a reusable, independently
checked theorem base and provide a Forth-native way to build and check proofs
and verified programs using Lean's logical approach. Early fragments are steps
toward that target, not a replacement with an incompatible toy logic. Full
Mathlib compatibility requires substantial staged work; report the exact
supported corpus and semantics rather than implying completeness.

The product target is **all of Mathlib**, not a handpicked useful subset.
LeanForth must ultimately make the entire library usable as a theorem and
rules base, including its transitive Lean/Std dependencies, with declarations
independently checked under an explicit, audited axiom policy. Compatibility
also requires the practical capacity and interfaces to find and apply those
results when developing proofs and verifying Forth programs. Pinned releases
define reproducible acceptance runs; they do not limit the product goal to one
snapshot. Some Mathlib results depend on standard axioms: report their actual
assumptions and obtain approval for the exact policy instead of silently
accepting axioms or claiming an axiom-free library.

The implementation sequence is: a minimal Lean-compatible kernel; a Lean
NDJSON importer; differential testing against pinned Lean checker cases and
eventually the official corpus; a Forth-native term-building vocabulary;
metavariables, unification and elaboration; then tactics and rewriting as
untrusted Forth. Implement verified-program execution and compilation with
explicit semantics and runtime boundaries; only investigate acceleration after
correctness and CPU behavior can be measured. Program-specification design and
reference experiments proceed alongside the kernel so that this remains a
first-class product path, without claiming verified execution prematurely.

These stages overlap where useful: importer fixtures and Lean oracle tests can
be prepared before the kernel exists. Compatibility is established only by
actual checker agreement over a specified, pinned corpus; early examples cannot
prove compatibility with all of Lean or Mathlib.

## Decision gates (before coding)

A. Confirm public project name and default private GitHub repository; license to be proposed after auditing Gforth and native library license interactions (Apache-2.0/MIT are candidates; don't guess compatibility).

B. Confirm working baseline environment WSL2 Linux, Gforth 1.0.0, portable Forth-2012 core, Lean 4.35.0, Lean export schema 3.1.0, CPU BLAS provider concept, MathLive optional external UI.

C. Record architecture ADRs: AST/binders/de Bruijn indices; trusted kernel boundary; Forth-specific platform adapter; serializations; non-theorem runtime trust; tensor FFI; explanation provenance; local JSON API.

## Phase 0 — actual environment and repository (first Codex session)

**Deliverables:** `README.md`, `AGENTS.md`, `docs/VERSIONS.md`, `docs/DECISIONS.md`, actual `Makefile`, a minimal `src/` Forth module, `tests/smoke/` that invokes Gforth, `scripts/check-env.sh`, scoped CI workflow and `docs/SETUP_WSL.md` updated with tested commands; local Git repo and private GitHub remote only after approval.

**Acceptance:** exact `gforth`, `lean`, `lake`, `gh`, `codex`, C compiler versions observed and recorded; `make smoke` invokes *real* Gforth and passes or exits nonzero on error; CI runs that exact command on supported Ubuntu. Any unavailable tool is explicitly shown as blocked, not silently skipped. User can clone (if remote approved) into WSL and repeat.

## Phase 1 — Forth kernel skeleton and typed terms (initial 1–2 weeks)

Build `src/core/names.fs`, `levels.fs`, `expr.fs`, `env.fs`, `arena.fs`, `serialize.fs`, plus unit tests. No proof-acceptance shortcut. Implement first small decidable fragment: sorts, variables, Pi/lambda/app and checking simple identity functions; exact rules to be reviewed in an ADR. A temporary standalone test harness is fine; avoid claiming full Lean compatibility.

**Acceptance:** canonical AST nodes and stable deterministic serializer; positive proof term is genuinely type checked; wrong term is rejected; undefined names, de Bruijn capture, malformed terms, type mismatch and corrupted serialization fail closed. `make test-core` and `make test-negative` are documented.

**Program track concurrently:** a minimal pure total function typed in the same core is executed through the Gforth host; the receipt explicitly separates *source typing* from *runtime correctness*. Define stack-effect documentation and contract AST tags in the first API schema.

## Phase 2 — Lean NDJSON importer and reference oracle (weeks 2–4, extend if necessary)

Build `src/import/lean_ndjson.fs` or a narrow untrusted decoder (consider Python parser initially if necessary, BUT semantics checked in Forth) and a fixture generator pinned to Lean 4.35.0/export v3.1.0. Begin with minimal names/levels/expressions. `lake check --paranoid` on a small oracle project when WSL sandbox works.

**Acceptance:** round-trip or stable reserialization of a curated subset; explicit unsupported-node diagnostics, hash/version metadata, malformed JSON negative tests, memory/depth limits, and demonstrated agreement for supported examples with pinned Lean checker. Incomplete inductives/quotients must be rejected as **unsupported**, not represented by axioms.

**Verified program track concurrently:** add spec/contract vocabulary design and a tiny VC proof of a pure scalar function. Document a sample `CHECK -> VERIFY -> RUN` workflow (real, not stubbed), returning distinct receipts. Test a runtime error and its diagnostic.

## Phase 3 — readable Forth source, proof steps and JSON interface

Create `LF.CORE`, `LF.KERNEL`, `LF.PROOF`, `LF.PP`, `LF.EXPLAIN`, `LF.API` vocabularies. Support a simple proof line by line with checked step objects and explanations; JSON-RPC local NDJSON interface validated against JSON schemas. Support Markdown/LaTeX/MathML export in the presentation layer without injecting the math grammar into Forth.

**Acceptance:** example universal reflexivity proof can be checked, displayed line-by-line with rule/lemma refs, turned into JSON, round-tripped where promised. An LLM can submit an invalid proof through JSON and receive a structured error without crashing or accepting it. Generate docs for every public word and API method.

## Phase 4 — real verified-Forth programming and tensor CPU baseline

Implement a small verification-condition generator and explicit specification language (stack types/effects, preconditions, postconditions, invariants). Interpret simple verified definitions on Gforth, then add a fast C/CBLAS CPU provider. Keep array metadata/checking in Forth and bulk numeric loops in native libraries.

**Acceptance:** nontrivial bounds-safe array operation verified against its stated semantics; executed on sample inputs with runtime check mode; tensor shape mismatch produces a deterministic error; BLAS matrix multiplication agrees with a tiny pure-Forth oracle on curated matrices. Benchmark with/without FFI overhead; publish assumptions and numerical tolerances.

## Phase 5 — compatible Lean kernel breadth / Mathlib / tactics

Extend universes, normalization, definitional equality, inductives, recursors, quotients and proof irrelevance to match Lean 4.35 semantics; progressively import Std/Mathlib slices; maintain allowlisted axioms and differential negative tests. Then add elaboration conveniences and tactics as untrusted proof generators.

**Acceptance:** progressively report objective pass fractions for a pinned
complete Mathlib release and its dependencies, not only selected examples;
completion requires the full corpus to be usable and independently checked
under the reviewed axiom policy. Require no false acceptance on negative
tests, recorded resource performance and diagnosis of every discrepancy.
Kernel remains small and human reviewed.

## Phase 6 — optimization, portable ports and external math UI

Profile term allocation, sharing, caching, parallel checking and efficient native compiled programs. Build external MathLive browser component; optional ArrayFire backend only after CPU+BLAS benchmarks show need. Test native Linux, macOS, Windows via supported Forth hosts and independent tiny Forth implementation; keep canonical source stable. Evaluate translation validation / compiler correctness for a narrow imperative subset and numeric verification caveats.

**Acceptance:** measured performance data with versioned test inputs, CPU fallback works when no GPU exists, and proof integrity is independent of chosen accelerator/compiler.

## Suggested first four weeks — reviewable tickets

| Ticket | Scope | Concrete observable acceptance |
|---|---|---|
| LF-001 | WSL/toolchain/Git/gh/Codex inventory | Commands/versions recorded; install blockers noted |
| LF-002 | Private GitHub repo + CI and smoke | User-authorized remote; `make smoke` actually runs in WSL and CI |
| LF-003 | Forth-2012 compatibility & host port | Mini host API; stack-effect table; test on target Gforth |
| LF-004 | Names/universes/expressions and serialization | Tagged nodes round-trip; malformed encodings rejected |
| LF-005 | Kernel core typing tests | Identity accepted; invalid application rejected |
| LF-006 | Proof-step structured data + printer design | Checked step map and text renderer goldens (can start unchecked) |
| LF-007 | JSON-RPC and schema design | Deterministic valid/invalid requests; no false `checked` state |
| LF-008 | Lean 4.35.0 export fixture and parser | Pin schema metadata; parse 1 positive/1 malformed fixture |
| LF-009 | Verified-program contract experiment | One real typed total executable Forth word, explicit trust receipt |
| LF-010 | Tensor shape/type API and CPU reference | Small 2D arrays; dimension mismatch correctly rejected |
| LF-011 | CBLAS selection/FFI feasibility | 1 native GEMM benchmark vs reference, provenance documented |
| LF-012 | MathLive adapter specification & 10 notation tests | 10 MathJSON/LaTeX semantic cases + ambiguity failures |

Tickets are suggestions, not claims of GitHub issues already created. Each issue should link to a test and clear acceptance result. Dependencies: LF-001/002 -> LF-003/004 -> LF-005/009; LF-006/007 can develop alongside kernel; LF-010/011 separate from mathematical proof checker; LF-012 frontend only.

## Test and review policy

- Positive proof tests, deliberately invalid proof tests and malformed importer tests are equally important. Every key proof behavior has a failure case.
- Every future assertion that a program is "verified" must include a check result from the actual kernel/VC tool and an explicit runtime assumption list.
- Differential Lean checks pin exact versions/corpus hashes and compare types/axioms/verdicts. Incomplete support is `unsupported`, not `accepted`.
- Tests belong in CI; benchmark changes require repeatable hardware and corpus metadata; no fake green placeholders.
- Kernel/axiom/compiler/FFI trust-boundary PRs must be human-reviewed, with an ADR and negative tests. Keep Codex-generated changes small enough to read.
- Do not grant Codex silent credential/network/system administrator access. User must approve private repo creation and any publication.

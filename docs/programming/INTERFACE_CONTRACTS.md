# Proposed external APIs and proof presentation (design contract, not implemented)

## Versioned JSON protocol

Use newline-delimited JSON-RPC 2.0 on standard input/output as a **local-only** machine interface initially. Use JSON Schema files later under `schemas/`; source code, prose and mathematical input are strings/structured objects, not special parser escape modes.

Example request (illustrative, may evolve):

```json
{"jsonrpc":"2.0","id":"req-1","method":"proof.check","params":{"schemaVersion":"0.1","theorem":"Nat.reflexivity","expressionRef":"sha256:...","proofTermRef":"sha256:...","axiomPolicy":"standard-only"}}
```

Example result (illustrative only — not a real checked theorem receipt):

```json
{"jsonrpc":"2.0","id":"req-1","result":{"schemaVersion":"0.1","status":"unchecked","checked":false,"verificationMode":"CHECK","diagnostics":[{"code":"LF_NOT_IMPLEMENTED","message":"Kernel not yet implemented"}],"theoremHash":null,"axioms":[]}}
```

Success is only true when a real checker has accepted the proof. Distinguish `parsed`, `elaborated`, `kernel-accepted`, `source-verified`, `runtime-validated`, `runtime-assumptions-present`, `rejected` and `unsupported`. No API silently upgrades one to another.

Required method families: `system.capabilities`, `source.parse`, `source.elaborate`, `type.infer`, `goal.list`, `proof.check`, `proof.steps`, `proof.explain`, `proof.pretty`, `program.verify`, `program.compile`, `program.run`, `tensor.describe`, `tensor.execute`, `lean.export.import`, `library.search`.

### Proof-step structure

```json
{
  "stepId":"s2",
  "conclusion":{"astRef":"sha256:...", "pretty":"x = x"},
  "premiseIds":[],
  "rule":"equality-reflexivity",
  "declarationRefs":["Eq.refl"],
  "termRef":"sha256:...",
  "kernelStatus":"unchecked",
  "axiomRefs":[],
  "explanation":{"text":"An expression is equal to itself by reflexivity of equality.","source":"structured-template","proofBased":true},
  "sourceSpan":null
}
```

`kernelStatus` must be a checker-derived field, never produced by a model. Explanation templates and LLM descriptions are untrusted metadata; a renderer must not invent premise IDs. Imported Lean proof terms normally lack author-level tactic narratives; reconstruct proof tree descriptions and tag them as reconstructed.

### Program verification receipt

The receipt format that exists is schema 0.3 (0.2, still read, without the check label), described in
[program receipts](PROGRAM_RECEIPTS.md); the sketch below predates it.

```json
{
  "programRef":"sha256:...",
  "specificationRef":"sha256:...",
  "sourceProofStatus":"unchecked",
  "runtimeBackend":"gforth",
  "runtimeValidation":"not-tested",
  "assumptions":[],
  "executionResult":null
}
```

Future source-proof status `kernel-accepted` and backend validation `runtime-tested` must remain separate even in success cases. For FFI/BLAS the assumptions list must identify exact external library builds and numerical semantics.

## LLM documentation requirements

Deliver (planned; none exists yet) an LLM guide, error-code catalogue and stack-effect reference as `LLM_GUIDE.md`, `ERROR_CODES.md` and `STACK_EFFECTS.md` in this directory, plus `schemas/*.json` and `examples/api/*.ndjson` at the repository root. All word docs include stack effects, semantics, trust boundary, one valid example and one invalid example. Error results should contain symbolic error code, source location, expected and inferred types, open goals, remaining assumptions and next machine-action suggestions. Tool invocations should be replayable without a GUI.

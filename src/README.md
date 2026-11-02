# Source layout

All Forth source lives here. Nothing in this tree is a trusted checker yet:
every module is untrusted development code, and any accepted result is
*experimental — not independently audited* (see `AGENTS.md`).

| Folder | Holds | Loaded by `main.fs` |
| --- | --- | --- |
| `main.fs` | One loader that includes every current module in dependency order; later the command-line entry point. Run `gforth src/main.fs`. | — |
| `lib/` | General Forth tools with no Lean knowledge: shared result codes, record fields, fixed-size stores, hashing, byte-stream reading, portability words. Created as the refactor extracts them. | yes |
| `core/` | Lean's data model and operations, the current path: terms, names, universe levels and their scope, value, comparison and substitution; sessions and stale-handle checks; constant references; and the `mixed-*` shift, instantiate, beta, compare, convert, signature and inference passes. | yes |
| `kernel/` | The trusted checker. Empty on purpose: code moves here only after it passes the review gate in `AGENTS.md`. | yes, once it exists |
| `import/` | Staging of decoded Lean exports into the term store (`load.fs`); later a shared NDJSON reader. | yes |
| `program/` | Verified-program track: the example words (clamp, checked add, abs, factorial, gcd, in-range) and the stack-depth analyzer. | yes |
| `legacy/` | Superseded earlier variants (plain and `tagged-*` passes, the `raw-*` signature index, `constant-*`/`context-*` probes, `arena.fs`, the unsafe `symbolic-infer.fs` draft). Kept only because tests and Lean comparisons still use them; retired under roadmap item Q9. Do not build on them. | no |

## Rules

- A module in `core/` may use `lib/` and other `core/` modules, never
  `legacy/`. `lib/` uses nothing outside `lib/`. `legacy/` may use `core/`.
- Every module states its load dependencies in its header comment. Add each
  new current module to `main.fs` in dependency order; `make smoke` fails if
  loading prints anything, such as a "redefined" warning.
- Tests load modules directly with `include`; they live in `tests/core/`
  (for `core/` and `legacy/` modules) and `tests/program/`.
- Style: [the Forth style guide](../docs/development/FORTH_STYLE.md);
  `make forth-metrics` reports per-folder totals.

## Where things moved (2026-11-02)

`src/experimental/` was split: the 22 modules that the current `mixed-*`
path uses went to `core/` (with `terms.fs`), `load.fs` to `import/`,
`program-depth.fs` to `program/`, and the remaining 27 modules plus
`core/arena.fs` to `legacy/`. File names were kept. `src/leanforth.fs` (a
one-word placeholder) was replaced by `main.fs`. Dated review records keep
the old paths.

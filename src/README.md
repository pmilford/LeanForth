# Source layout

All Forth source lives here. Nothing in this tree is verified yet: it is
code in progress, and the checker in `kernel/` becomes trusted only when the
owner declares it so after the review gate in `AGENTS.md`. Until an outside
audit, any accepted result is *experimental — not independently audited*.

| Folder | Holds | Loaded by `main.fs` |
| --- | --- | --- |
| `main.fs` | One loader that includes every current module in dependency order; later the command-line entry point. Run `gforth src/main.fs`. | — |
| `lib/` | General Forth tools with no Lean knowledge: the portability adapter, range checks, the `store:` bounded-store defining word, tagged node records, the shared outcome vocabulary and `walk:` re-entrant DAG walks so far; hashing and byte-stream reading are planned. `lib.fs` loads them in order. | yes, through `core/` |
| `core/` | Lean's data model: the term store, names, universe levels and their parameter scope, the Sort representation, sessions and stale-handle checks, constant references and their structural audits. | yes |
| `kernel/` | The proof checker, under development: universe substitution, value and comparison; candidate signatures; the `mixed-*` shift, instantiate, beta, compare, convert and inference passes; the definition probe. See [`kernel/README.md`](kernel/README.md). | yes |
| `import/` | Staging of decoded Lean exports into the term store (`load.fs`); later a shared NDJSON reader. | yes |
| `program/` | Verified-program track: the example words (clamp, checked add, abs, factorial, gcd, in-range) and the stack-depth analyzer. | yes |
| `legacy/` | Superseded earlier variants (plain and `tagged-*` passes, the `raw-*` signature index, `constant-*`/`context-*` probes, `arena.fs`, the unsafe `symbolic-infer.fs` draft). Kept only because tests and Lean comparisons still use them; retired under roadmap item Q9. Do not build on them. | no |

## Rules

- Dependencies point one way: `lib/` ← `core/` ← `kernel/`. `lib/` uses
  nothing outside `lib/`; `core/` never uses `kernel/`; neither uses
  `legacy/`, `import/` or `program/`. `legacy/` may use anything.
- Modules load the library with `require ../lib/lib.fs`, which compiles it
  once however many modules ask; other dependencies are still loaded by the
  caller in order. Every module states its load dependencies in its header comment. Add each
  new current module to `main.fs` in dependency order; `make smoke` fails if
  loading prints anything, such as a "redefined" warning.
- Tests load modules directly with `include`; they live in `tests/lib/`,
  `tests/core/` (for `core/`, `kernel/` and `legacy/` modules) and `tests/program/`.
- Style: [the Forth style guide](../docs/development/FORTH_STYLE.md);
  `make forth-metrics` reports per-folder totals.

## Where things moved (2026-11-02)

`src/experimental/` was split by computing which modules the current
`mixed-*` path actually uses: 9 data-model modules went to `core/` (joining
`terms.fs`), the 13 checking modules to `kernel/`, `load.fs` to `import/`,
`program-depth.fs` to `program/`, and the remaining 27 modules plus
`core/arena.fs` to `legacy/`. File names were kept. `src/leanforth.fs` (a
one-word placeholder) was replaced by `main.fs`. Dated review records keep
the old paths.

# Source layout

All Forth source lives here. Nothing in this tree is verified yet: it is
code in progress, and the checker in `kernel/` becomes trusted only when the
owner declares it so after the review gate in `AGENTS.md`. Until an outside
audit, any accepted result is *experimental — not independently audited*.

| Folder | Holds | Loaded by `main.fs` |
| --- | --- | --- |
| `main.fs` | One loader that includes every current module in dependency order; later the command-line entry point. Run `gforth src/main.fs`. | — |
| `lib/` | General Forth tools with no Lean knowledge: the portability adapter, range checks, the `store:` bounded-store defining word, tagged node records, the shared outcome vocabulary, `walk:` and paired `walk2:` re-entrant DAG walks, `frames:` records for bounded recursive passes, run-time versions of stores and walks (`store-init`, `walk-init`), and per-task checker contexts with owners (`context.fs`) so far; hashing and byte-stream reading are planned. `lib.fs` loads them in order. `task.fs`, the job pool for parallel checking (a fixed pool of worker tasks fed from a bounded queue), is loaded only by its users. | `lib.fs` yes, through `core/`; `task.fs` no |
| `core/` | Lean's data model: the term store, names, universe levels and their parameter scope, the Sort representation, sessions and stale-handle checks, constant references and their structural audits. | yes |
| `kernel/` | The proof checker, under development: universe substitution, value and comparison; candidate signatures; the `mixed-*` shift, instantiate, beta, compare, convert and inference passes; the definition probe. See [`kernel/README.md`](kernel/README.md). | yes |
| `import/` | Staging of decoded Lean exports into the term store (`load.fs`); later a shared NDJSON reader. | yes |
| `program/` | Verified-program track: the example words (clamp, checked add, abs, factorial, gcd, in-range) and the stack-depth analyzer. | yes |

## Rules

- Dependencies point one way: `lib/` ← `core/` ← `kernel/`. `lib/` uses
  nothing outside `lib/`; `core/` never uses `kernel/`; neither uses
  `import/` or `program/`.
- One variant per operation. The superseded variants that used to live in
  `legacy/` were retired on 2026-11-02 (see below); do not re-add them or
  keep a second version of a current module beside it.
- Each file loads exactly what it uses (owner rule, 2026-11-02): after its
  header comment a module `require`s its direct dependencies, with paths
  relative to itself (`./x.fs` in its own folder, `../core/x.fs` elsewhere)
  and the library as a whole as `../lib/lib.fs`. `REQUIRE` loads a file once
  however many modules ask; `INCLUDE` of a source module is refused by
  `make check-portable-forth`, because a second load would make a second copy
  of its stores. `main.fs` requires only the top modules, the ones no other
  module requires. `make smoke` loads every module on its own and fails if
  any of them, or `main.fs`, prints anything (a missing dependency or a
  "redefined" warning).
- Tests `require` the modules whose words they use; they live in `tests/lib/`,
  `tests/core/` (for `core/`, `kernel/` and `import/` modules) and
  `tests/program/`.
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

Later the same day `legacy/` (28 files) and its tests in `tests/legacy/`
(91 files) were deleted, with the owner's approval, once the current code
had at least the same test coverage; what replaced each capability is in
[the decisions record](../docs/project/DECISIONS.md) ("Legacy retired —
2026-11-02").

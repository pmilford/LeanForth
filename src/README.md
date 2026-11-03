# Source layout

All Forth source lives here. Nothing in this tree is verified yet: it is
code in progress, and the checker in `kernel/` becomes trusted only when the
owner declares it so after the review gate in `AGENTS.md`. Until an outside
audit, any accepted result is *experimental — not independently audited*.

| Folder | Holds | Loaded by `main.fs` |
| --- | --- | --- |
| `main.fs` | One loader that includes every current module in dependency order; later the command-line entry point. Run `gforth src/main.fs`. | — |
| `lib/` | General Forth tools with no Lean knowledge: the portability adapter, range checks, the `store:` bounded-store defining word, tagged node records, the shared outcome vocabulary, `walk:` and paired `walk2:` re-entrant DAG walks, `frames:` records for bounded recursive passes, run-time versions of stores and walks (`store-init`, `walk-init`), and per-task checker contexts with owners (`context.fs`, where every `core/` and `kernel/` module keeps its state), which `lib.fs` loads; and, loaded only by the modules that use them, the job pool for parallel checking (`task.fs`, a fixed pool of worker tasks fed from a bounded queue), the line reader with UTF-8 checks (`bytes.fs`), the JSON reader (`json.fs`) and the deterministic JSON writer (`json-write.fs`). Hashing is planned. | `lib.fs` yes, through `core/`; `task.fs` no |
| `core/` | Lean's data model: the term store, names, universe levels and their parameter scope, the Sort representation, sessions and stale-handle checks, constant references and their structural audits; and the checker's diagnostic record (`diagnostics.fs`, why a check failed; see [DIAGNOSTICS.md](../docs/programming/DIAGNOSTICS.md)); structural name equality (`name-equal.fs`) and the input of a checking run (`input.fs`: its declarations, marks and fingerprint). | yes (`input.fs`, `name-equal.fs` through the environment, once `main.fs` requires it) |
| `kernel/` | The proof checker, under development: universe substitution, value and comparison; candidate signatures; the `mixed-*` shift, instantiate, beta, compare, convert and inference passes, which reject by ADR 0011's rules (`mixed-head.fs`: the head kinds they read); the definition and theorem probe; the checked environment v0 and its publisher (`environment.fs`, `env-publish.fs`; see [CHECKED_ENVIRONMENT.md](../docs/programming/CHECKED_ENVIRONMENT.md)). See [`kernel/README.md`](kernel/README.md). | yes (the environment not yet) |
| `import/` | The reader of Lean's lean4export NDJSON files (`ndjson.fs`, see [NDJSON_READER.md](../docs/development/NDJSON_READER.md)) and its record-counting tool (`ndjson-count.fs`, not loaded by `main.fs`); staging of decoded expression records into the term store (`load.fs`). | yes |
| `program/` | Verified-program track: the example words (clamp, checked add, abs, factorial, gcd, in-range) and the stack-depth analyzer. | yes |
| `present/` | Presentation: untrusted output formatting that the checker never reads. The presentation side table (`binder-table.fs`: binder names and kinds, source record IDs, declared types) and the term printer (`term-printer.fs` and the `print-*.fs`, `latex-text.fs` modules it loads) in Lean's notation, ASCII and LaTeX. See [the user guide](../docs/user/TERM_PRINTER.md). Uses `lib/` and `core/`, never `kernel/`. | yes, `term-printer.fs`; the checker never uses it |

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
- Every mutable cell that a check writes lives in the checker context
  (`lib/context.fs`, ADR 0009), one copy per context: stores, walk,
  frames and module records are declared with `context-store:`,
  `context-walk:`, `context-walk2:`, `context-frames:` and
  `context-record:`, and what used to run while loading with
  `context-setup`; such modules define no `VARIABLE`, `store:`, `walk:` or
  `frames:`. Constants, tables filled while loading and deferred words set
  once while loading are shared and read-only. Shared and writable, besides
  the job pool's own records (`lib/task.fs`), are only the checked
  environment's registry (`lf-envs` in `kernel/environment.fs`; the
  environments themselves are on the heap), which only the task driving
  the checks writes, outside jobs, and the NDJSON counter's export record
  (below).
  `tests/core/contexts.fs` (the core and kernel modules) and
  `contexts-main.fs` (everything `main.fs` loads) check this without a
  list: the dictionary the modules lay down while loading must be
  unchanged, byte for byte, after real checker work in contexts, so a
  forgotten `VARIABLE` fails even when it is only a register within one
  call. Converted: all of `core/` and `kernel/`, `import/load.fs`,
  `import/ndjson-count.fs` (its tally; its export record owns heap
  buffers and stays shared, so one count runs at a time), `present/` and
  the program reader and interpreter (`program/ir-reader.fs`,
  `ir-run.fs`); `import/ndjson.fs` keeps no state of its own (every word
  takes an export record).
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

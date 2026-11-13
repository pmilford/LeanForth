# Source layout

All Forth source lives here. Nothing in this tree is verified yet: it is
code in progress, and the checker in `kernel/` becomes trusted only when the
owner declares it so after the review gate in `AGENTS.md`.

| Folder | Holds | Loaded by `main.fs` |
| --- | --- | --- |
| `main.fs` | One loader that requires every current module in dependency order, and the command-line entry point: `bin/leanforth` runs `gforth src/main.fs -e cli-main COMMAND ...`. Run `gforth src/main.fs` for a Forth session. | — |
| `lib/` | General Forth tools with no Lean knowledge: the portability adapter, range checks, the `store:` bounded-store defining word, tagged node records, the shared outcome vocabulary, `walk:` and paired `walk2:` re-entrant DAG walks, `frames:` records for bounded recursive passes, run-time versions of stores and walks (`store-init`, `walk-init`) and heap stores that grow up to a limit (`store-heap-init`, `store-grow`) and side columns that grow with them (`store-columns.fs`), and per-task checker contexts with owners (`context.fs`, where every `core/` and `kernel/` module keeps its state), which `lib.fs` loads; and, loaded only by the modules that use them, the job pool for parallel checking (`task.fs`, a fixed pool of worker tasks fed from a bounded queue), the line reader with UTF-8 checks (`bytes.fs`), the JSON reader (`json.fs`) and the deterministic JSON writer (`json-write.fs`), big natural numbers for Lean's `Nat` literals (`bignum.fs`, not yet used by the kernel), visible text (`text-rule.fs`: UTF-8 without control, format or separator characters, and not blank-looking; the run records' text rule), stable sorting of records in place (`sort.fs`, not yet used by any module; see [FORTH_LIBRARY.md](../docs/development/FORTH_LIBRARY.md#sorting)), sequences of cells that never change and share their cells (`runs.fs`, the front end's local contexts and goal lists); and the general part of the compact store ([ADR 0016](../docs/adr/0016-compact-store.md)): packed 32-bit fields (`u32.fs`), portable 32-bit hashing (`hash32.fs`), growable heap stores with marks (`slab.fs`), open-addressing hash tables (`htab.fs`), hash-consed sets in two tiers (`cons.fs`) with interned lists and texts (`pools.fs`), and the library's wordlists of [ADR 0010](../docs/adr/0010-wordlists.md) (`module.fs`). | `lib.fs` yes, through `core/`; `task.fs` no |
| `core/` | Lean's data model: the term store, names, universe levels and their parameter scope (heap stores whose capacities are per-context settings, with per-index side columns that grow with them, `lib/store-columns.fs`; names may be a sealed compact input tier's, attached with `lf-name-attach`), the Sort representation, sessions and stale-handle checks, constant references and their structural audits; free variables and the local context of a check (`local-context.fs`, ADR 0014 Q2), and the joint marks a check rolls its terms, levels, references and local context back to (`scratch-marks.fs`); a check's memory limit, which meters the records its scratch makes (`scratch-meter.fs`, `check --memory-per-check`); and the checker's diagnostic record (`diagnostics.fs`, why a check failed; see [DIAGNOSTICS.md](../docs/programming/DIAGNOSTICS.md)); structural name equality (`name-equal.fs`) and the input of a checking run (`input.fs`: its declarations, marks and fingerprint); and the leaves an importer stages for term forms the first checker does not support (`unsupported-forms.fs`); the axiom allowlist v1 (`axiom-allowlist.fs`, plan task 5.3.1) and the matcher of a term against a fixed statement text that it uses (`statement-match.fs`); the derivation log (`derivation-log.fs`, ADR 0013: the optional record of the rules the checker applies, written by the kernel and never read by it; see [DERIVATION_LOG.md](../docs/programming/DERIVATION_LOG.md)); and the compact store's Lean layer (`compact.fs` and the `compact-*.fs` it loads: names, levels, lists, literals and 16-byte expression records in a shared input tier and per-check scratch tiers, ADR 0016), whose names the checker reads through a name view. | yes (`input.fs`, `name-equal.fs` through the environment, once `main.fs` requires it; `compact*.fs` through `import/stage.fs`) |
| `kernel/` | The proof checker, under development: universe substitution, value and comparison; candidate signatures; the `mixed-*` shift, instantiate, beta, compare, convert and inference passes, which reject by ADR 0011's rules (`mixed-head.fs`: the head kinds they read), inference over free variables (`mixed-open.fs`: Lean's `instantiate_rev`, `abstract`, `mk_pi`; plan task 4.2.2a); Lean's weak head normal form with unfolding (`whnf.fs`) and definitional equality (`defeq.fs`, which conversion runs; plan tasks 4.2.2b-c, ADR 0014); the definition and theorem probe; the checked environment v0 and its publisher (`environment.fs`, `env-publish.fs`; see [CHECKED_ENVIRONMENT.md](../docs/programming/CHECKED_ENVIRONMENT.md)). See [`kernel/README.md`](kernel/README.md). | yes (the environment not yet) |
| `import/` | The reader of Lean's lean4export NDJSON files (`ndjson.fs`, see [NDJSON_READER.md](../docs/development/NDJSON_READER.md)), the check of its manifest (`manifest.fs`) and its record-counting tool (`ndjson-count.fs`); the re-exporter, which writes every record back in the exporter's exact bytes (`ndjson-emit.fs`; see [Re-export](../docs/development/NDJSON_READER.md#re-export)); staging of decoded expression records into the term store (`load.fs`); the importer stage (`stage.fs` and `stage-records.fs`, ADR 0016 C9 step 2): an export, checked against its manifest by default, staged into a compact input tier with 32-byte declaration records, the name-to-declaration array and constants resolved when sealed; the feed (`feed.fs`, plan task 3.2.2, ADR 0016 C9 step 3), which makes a sealed stage the current context's checker input in file order, its names and expressions read from the stage in place (lets and projections too; only an mdata expression and the terms above one copied) and its levels and declarations copied into the context's stores, any size; the checker's input read directly from an export (`checker-input.fs`, plan task 3.2.2 v0: the stores' default capacities, small exports only); run records, the evidence of one check of an export, and their replay (`run-record.fs`, `run-replay.fs`, whose texts follow `lib/text-rule.fs`; see [run records](../docs/programming/RUN_RECORDS.md)): the one place outside `kernel/` that runs checks and reads the checked environment, only through its public words. | yes (some through `cli/`) |
| `cli/` | The command line (`leanforth.fs`, plan tasks 3.4.1-3.4.2): `check` (with `--record`), `replay`, `print` (with `print.fs`: proof outlines from the derivation log), `count`, `reexport`, `version`, `capabilities`, the exit codes 0-5, and the Forth words behind them; see [the command line](../docs/user/COMMAND_LINE.md). Uses `lib/`, `core/`, `kernel/`, `import/` and `present/`; nothing but `main.fs` uses it. Untrusted: it prints a declaration's verdict as the checker published it. | yes |
| `program/` | Verified-program track: the example words (clamp, checked add, abs, factorial, gcd, in-range) and the stack-depth analyzer. | yes |
| `present/` | Presentation: untrusted output formatting that the checker never reads. The presentation side table (`binder-table.fs`: binder names and kinds, source record IDs, declared types) and the term printer (`term-printer.fs` and the `print-*.fs`, `latex-text.fs` modules it loads) in Lean's notation, ASCII and LaTeX; the labels and notes of proof steps (`note-table.fs`) and the printer's Forth mode (`print-forth.fs`, a declaration as the LeanForth words that build it); the proof outline printed from the derivation log (`proof-outline.fs` and `log-view.fs`, plan task 2.4.4, in plain text or as LaTeX, 8.6.1; its header shows the statement in Lean notation, mathematics and LeanForth words, `statement-forms.fs`, 8.6.2; the log's structural check, `log-check.fs`, which the outline applies before it prints; [PROOF_OUTLINE.md](../docs/user/PROOF_OUTLINE.md)). See [the user guide](../docs/user/TERM_PRINTER.md). Uses `lib/` and `core/`, never `kernel/`. | yes, `term-printer.fs` and `proof-outline.fs`; the checker never uses them; `note-table.fs` and `print-forth.fs` no |
| `front/` | The untrusted front end ([ADR 0021](../docs/adr/0021-front-end.md), proposed; plan FE1), started 2026-11-12: the natural reader (`reader.fs`, FE1a), which gives LeanForth's words their meaning in natural LeanForth, the default form (`author/form.fs`; the kernel form needs the word `kernel-form`), and builds Lean-shaped syntax trees with positions in the syntax store (`syntax.fs`), stopping as not supported yet where elaboration or a tactic would begin; and the metavariable context (`mvars.fs`, FE1b), after Lean's `MetavarContext`, whose metavariables are leaves of the term and level stores (`core/mvar-leaves.fs`) that the export writer refuses (ADR 0021 D2), with bottom-up walks on heap stacks (`dag-walk.fs`); and the first pieces of the Meta layer (FE1c, tested alone and compared with pinned Lean): level unification (`level-defeq.fs`), bound-variable instantiation, abstraction and head beta (`instantiate.fs`), level equality and Lean's cheap level simplifications (`level-simp.fs`), `Level.normalize` (`level-normalize.fs`), universe-parameter instantiation (`level-params.fs`), the rebuild of a Sort or constant over new levels it shares with `mvars.fs` (`level-map.fs`), the view of the environment (`meta-env.fs`: reducibility and unfolding under each transparency, from the input and the elaboration data), `whnfCore` (`whnf.fs`, with the spine and level-list words in `meta-spine.fs`), instantiation with beta (`beta-inst.fs`), the first cases of type inference (`infer.fs`) and term unification (`defeq.fs`, Lean's `isDefEq`, with Lean's `==` and eta shapes in `term-eqv.fs`, the quick proposition and proof tests in `prop-quick.fs`, `checkAssignment` and `mkLambdaFVars` in `assign-check.fs`, `Nat` values and offsets in `nat-offset.fs` and parameter facts in `fun-info.fs`); for the tactic framework (FE1g-1), Lean's local declarations and local contexts, one per metavariable (`lctx-views.fs`), goals, clear, rename and the goal list (`goals.fs`) and the goals' text as Lean's `trace_state` prints it (`goal-print.fs`); tactic proofs read into a record of steps (`tactic-syntax.fs`, FE1g-2) and run at `end NAME` (`tactic-run.fs`, FE1g-3: blocks as heap frames, focus and done, saved states, fuel, `by-sorry`, the closing over the binders and the hand-over; the statement from FE1e's hook) and the first tactics (`tactic-basic.fs`, FE1g-4: `by-intro:`, `by-exact`, `by-rfl`). Uses `lib/`, `core/`, `present/` and `author/`, never `kernel/`, and `import/` only for the stage's names (`meta-env.fs`, as `elab-data.fs`); the command line hands it a library constant's argument count (`cli/check-lf.fs`). | yes, `reader.fs` through `cli/check-lf.fs`, `mvars.fs` directly |
| `author/` | The untrusted authoring layer (plan task 8.1.2, ADR 0017): theorems and proofs written as LeanForth words and run by Forth's own interpreter, line by line (`runner.fs`, the top module), with case-sensitive names, namespaces, labels and notes and errors with line and column; a library's constants named through a finder (`library.fs`), and the declarations a run made written as export records (`export.fs`), which `leanforth check FILE.lf` reads into the importer stage (`cli/check-lf.fs`; plan tasks 8.2.1c-d, ADR 0017 Amendment 2). See [the reference](../docs/programming/LEANFORTH_WORDS.md). Uses `lib/`, `core/` and `present/`, never `kernel/` or `import/`; the kernel, the data model and the importer never load it (`tests/author/check_author.py` checks that). | yes, through `cli/check-lf.fs` |
| `front/` | The front end's modules (plan FE1-FE12, ADR 0021; untrusted, never loaded by the kernel): `elab-data.fs`, the reader of a library's elaboration data (plan row FE1d, [ELABORATION_DATA.md](../docs/programming/ELABORATION_DATA.md)), checked against the importer stage's names and kept in the checker context for the elaborator. Uses `lib/` and `import/`, never `kernel/`. | yes, through `cli/check-lf.fs` |

## Rules

- Dependencies point one way: `lib/` ← `core/` ← `kernel/`, and
  `lib/` ← `core/` ← `present/` ← `author/` ← `front/`; `cli/` loads
  `author/` and `front/` too (`leanforth check FILE.lf`). `lib/` uses
  nothing outside `lib/`; `core/` never uses `kernel/`; neither uses
  `import/` or `program/`. `cli/` sits on top: it uses `kernel/`,
  `import/` and `present/`, and only `main.fs` uses it.
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
  the checks writes, outside jobs; the parallel scheduler's record
  (`lf-sched` in `kernel/env-schedule.fs`), written only by that task
  outside jobs; the snapshot's (`kernel/env-snapshot.fs`): `snap-loading`
  (the record a load's check word reads), `snap-stale-allowed` (a flag
  set before loading), `snap-site-tables` and `snap-outers` (the
  writer's, one save at a time), and the import pass's `imp-current`
  (`kernel/env-import.fs`, one pass at a time); the NDJSON counter's export record
  (below), the re-exporter's module and export records
  (`import/ndjson-emit.fs`: they own heap buffers, so one re-export runs
  at a time), the checker input's export and manifest records
  (`import/checker-input.fs`, likewise), the run record's and the
  replay's records (`import/run-record.fs`, `run-replay.fs`: one run at a
  time) and the command line's manifest record for re-exports
  (`cli/leanforth.fs`).
  `tests/core/contexts.fs` (the core and kernel modules) and
  `contexts-main.fs` (everything `main.fs` loads) check this without a
  list: the dictionary the modules lay down while loading must be
  unchanged, byte for byte, after real checker work in contexts, so a
  forgotten `VARIABLE` fails even when it is only a register within one
  call. Converted: all of `core/` and `kernel/`, `import/load.fs`,
  `import/ndjson-count.fs` (its tally; its export record owns heap
  buffers and stays shared, so one count runs at a time),
  `import/checker-input.fs` (its tables), `cli/leanforth.fs` (its options and
  counts, set up with the defaults in every context), `present/` and
  the program reader and interpreter (`program/ir-reader.fs`,
  `ir-run.fs`); `import/ndjson.fs` and `import/stage.fs` keep no state
  of their own (every word takes an export or a stage record). `author/` keeps its state in context members
  too, but grows the dictionary while a proof runs (a word per name
  spelling): one more reason the kernel never loads it; `leanforth
  check FILE.lf` runs it once per process, within a dictionary reserve
  (ADR 0017 Amendment 1, A5 row 11).
- Tests `require` the modules whose words they use; they live in `tests/lib/`,
  `tests/core/` (for `core/`, `kernel/` and `import/` modules),
  `tests/present/`, `tests/author/`, `tests/program/` and `tests/cli/`.
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

# Running the checks today

What you can run are the test suites and the comparisons with Lean,
through `make`, a few Forth tools, and the command line `bin/leanforth`
(version 0, [its manual](COMMAND_LINE.md)), which checks small Lean exports
with the experimental first checker. This page says what each one runs,
what a pass shows, and — just as important — what it does not show.
Status 2026-11-02, commit `fc558cc`; the command line added 2026-11-03.

**Nothing below proves a theorem or verifies a program with LeanForth.**
A pass shows that untrusted, experimental code behaved as its tests and
the Lean comparisons expect on finite cases.

## Before you start

Install the pinned tools into `.tools/` as the
[project README](../../README.md#installing-the-pinned-tools-and-running-the-tests)
describes (Gforth 1.0.0 and Lean 4.35.0, each checked against a SHA-256).
The Makefile finds them there; override with `GFORTH=...` or `LEAN=...`.
Every command is stopped after `TEST_TIMEOUT` seconds (600 by default) and
then fails. Run everything from the repository root.

## The two suites

| Command | Needs | Time, measured 2026-11-03 (8 jobs, 10 cores) | Runs |
| --- | --- | --- | --- |
| `make test` | Gforth and Python 3 | about 8 s (36 s with `JOBS=1`) | Documentation, Lean-source and portability checks, the silent-load check of every module, the test harness's own tests, every Forth unit test, the NDJSON reader's file tests, the fixture bridge, the program examples, the term printer, the receipt schema and the IR reader |
| `make check` | also Lean 4.35.0 | about 45 s with the Lean cache filled, about 70 s with an empty one, about 75 s without it (`LEAN_CACHE=0`, as CI) | `make test`, then every comparison with pinned Lean |

Make runs 8 targets at a time (`JOBS=1` runs one at a time) and prints each
target's output in one piece. At the first failure it starts no more
targets, lets the running ones finish, names the failing target
(`make: *** [Makefile:LINE: TARGET] Error N`) and exits with a nonzero
status. Outside CI, `make check` replays pinned Lean's runs on unchanged
inputs from a cache shared by the clone's worktrees; `LEAN_CACHE=0` runs
Lean every time, and `LEAN_CACHE=verify` runs it and compares with the cache
([testing strategy](../development/TESTING_STRATEGY.md#running-the-suites-parallel-jobs-and-the-lean-cache)).
CI runs `make test` on Ubuntu's Gforth 0.7.3 and `make check LEAN_CACHE=0`
on the pinned tools for every push to `main`
([project progress](../project/PROJECT_PROGRESS.md) records the latest
runs), so CI never replays a cached run. Run `make test` before every
commit; while working, `make test-changed` runs only the targets that use a
file changed since `main`.

## What each part shows, and what it does not

| Target | A pass shows | It does not show |
| --- | --- | --- |
| `check-docs` | Every relative link in the documentation and every `docs/` path mentioned in sources resolves | That the text is right |
| `check-lean-sources` | No Lean test file contains `sorry`, `admit`, `native_decide` or an unlisted axiom, and every Lean call treats warnings as errors | Anything about LeanForth |
| `check-portable-forth` | The Forth source avoids the byte-order and cell-size dependencies the [style guide](../development/FORTH_STYLE.md) forbids, and loads modules with `require` | That it runs on another Forth |
| `smoke` | `src/main.fs` and every module, loaded on its own, load silently (no missing dependency, no redefinition) | Behaviour |
| `test-harness` | The test harness fails on a wrong value and on a wrong stack depth, as it must | — |
| `test-lib` | The library — stores, walks, frames, contexts, the job pool on threads, cooperative and serial hosts, the line reader, JSON — meets its unit tests, including stack overflows inside jobs and a randomized model of contexts | Speed (`tests/lib/task-bench.fs` is report-only) |
| `test-core` | The data model and the experimental checking passes meet their unit tests, including refused inputs, stale handles, fuel and room limits; checker trials give the same digests when every store is cut to its count before each check and every block moves at every allocation (`tests/core/store-growth.fs`); the NDJSON reader decodes the fixtures exactly as Python's `json` module does and fails at the expected line on 13 broken files and a seeded mutation sweep | That any inferred type is a checked result |
| `test-composition-fixture` | The test-only Python bridge stages the pinned fixtures into the Forth stores, and the definition probe reaches the expected diagnostics | Import or checking of real libraries |
| `test-program` | The six example words give the expected results on sample and small exhaustive inputs | That the words are correct for all inputs: testing is not proof |
| `test-program-ir` | The receipt schema accepts its valid examples and refuses each invalid one for its pinned reason; the reference models copied into the IR's Lean file are verbatim; the IR reader's output for the example words equals the golden IR | That the reader's translation is faithful |
| `test-lean-cache` | The Lean cache, on a fake toolchain, replays a repeated call exactly and misses on every changed input; it never caches IO inputs, and the Makefile uses it only without `LEAN_CACHE=0` and `CI` | That pinned Lean itself is deterministic (`make check LEAN_CACHE=verify` reruns every call and compares) |
| `test-present` | The term printer meets its unit tests, ends every print of 49 cases in three modes at every fuel level with a defined outcome, prints terms and levels 2,000 and 10,000 deep in the host-stack cells of shallow ones (and is full when the heap refuses room), and prints the golden text for those cases and the five fixtures | That the printed text is what Lean prints (that is `test-printer-differential`) |
| `reference`, `reference-export` | The Lean reference files check with pinned Lean and fail on `sorry`; re-exporting the fixtures gives byte-identical NDJSON | Anything about LeanForth |
| `reference-first-checker` | Lean's verdicts on the first checker's 60 expected-results cases and 27 broken source copies are as recorded ([expected results](../reviews/FIRST_CHECKER_EXPECTED.md)) | LeanForth's answers (that is `test-first-checker-differential`) |
| `reference-binder-domains` | Lean's answers on comparing binders whose argument types differ ([ADR 0003, Amendment 1](../adr/0003-conversion.md)) | LeanForth's answers (that is `test-binder-domains-differential`) |
| `test-first-checker-differential`, `test-binder-domains-differential`, `test-universe-scope-differential` | The first checker, run end to end through the checked environment, gives the expected outcome on the 69 table cases, the 22 binder-domain cases (three known capacity differences, each a failure) and 50 universe-scope cases; every rejection names Lean's reason; every accepted case prints its *experimental* label ([first check](FIRST_CHECK.md)) | That the checker is correct beyond these cases, or reviewed: it has not passed its gate |
| `test-first-checker-large-differential`, `test-binder-domains-large-differential`, `test-universe-scope-large-differential` | The same three tables with every store's capacity raised (4,096 terms, 1,024 levels, names and references, 256 declarations): the same answers, and the three binder-domain rows that meet the 64-node store get the table's answer, so no known difference remains | Inputs deeper than these small cases (the depth tables check 2,000 and 10,000) |
| `test-first-checker-fed-differential`, `test-binder-domains-fed-differential`, `test-universe-scope-fed-differential` | The same three tables through the path a real export takes: each case written as a lean4export export, staged and fed to the checker ([feeding the checker](../development/NDJSON_READER.md#feeding-the-checker)), so the names stay in the stage's input tier and every store grows to the feed's capacities. The same answers, with no known difference except three first-checker cases whose export the stage refuses as invalid, because they name a constant the export does not declare (a real export always does) | That every export is fed correctly: these are small cases, with few names and parameters |
| `test-depth-differential`, `test-depth-fed-differential` | Lambda, application and successor chains 2,000 deep (`tests/reference/depth-terms.lean`), each accepted or rejected for Lean's reason, by checker input and fed; `test-depth-deep-differential` (not part of `make check`; about 5 minutes) the same 10,000 deep, fed, with one known difference: the wrong lambda stays *unknown* | That LeanForth's passes have no depth limit of their own (plan task 6.2.0) | Speed at depth: the work grows with the square of the depth |
| `test-environment` | The checked environment and check-declaration meet their unit tests: every outcome, Lean's order, fuel sweeps, and the pinned NDJSON exports checked and accepted | The same |
| `test-check-block` | The check of inductive blocks ([developer notes](../programming/INDUCTIVE_BLOCKS.md)) gives every outcome on 72 exports Lean printed for the inductive table, each rejection with its rule; Lean's replay of a mutated `Bool` block, and blocks tampered one field at a time, are rejected with the field named | That it is right beyond these cases: it has not passed its gate |
| `test-inductive-table` | LeanForth, run on every case of `tests/reference/inductive-expected.lean` as the export Lean printed for it, gives Lean's verdict on the rows of task 5.2.1a (the pending ones named, with their reasons) and never another decided verdict on later rows | Anything about recursive, mutual or nested types, reductions, literals or quotients, all still unsupported |
| `test-cli` | `bin/leanforth` reaches every exit status 0–5 with its exact output (accepted, rejected, unsupported and unknown, out of fuel and out of room, malformed files and command lines, injected internal faults), from other folders, and agrees with the counter and the re-exporter | That a verdict is right beyond these cases: the checker has not passed its gate |
| `reference-cli` | Pinned Lean accepts the command line's two Lean fixtures, and `scripts/export.sh` reproduces their exports and manifests byte for byte | Anything about LeanForth |
| `reference-program-ir` | Lean proves the six words' IR equal to their reference models, using only `propext`, `Classical.choice` and `Quot.sound`, and the IR it prints equals the reader's | Anything checked by LeanForth, or the host's behaviour |
| `test-log` | The derivation log gives the same outcomes, diagnostics and fuel with the log off, on and full at every bound, on every pinned export and broken copy and on 8 random checker trials of 1,000 steps (also interleaved with a context that does not log); every log is a valid prefix; the proof outlines print the golden text; the rule catalogue matches its documentation; the kernel uses only the log's protocol ([derivation log](../programming/DERIVATION_LOG.md)) | That an outline's sentences are right: they are fixed templates, not checked reasoning |
| `check-log-identity` (not in `make check`, about ten minutes) | All of `make test` and the pinned-Lean comparisons pass unchanged with the log on in every context, and with it full after 5 records or with tiny copy pools | More than those tests cover |
| `test-printer-differential` | The printer's Unicode output equals Lean's own printing on 49 cases and the five fixtures' `#print` lines, and its ASCII output, read back by Lean, elaborates to the original declarations | That any printed statement was checked |
| `test-*-differential` | On finite tables, the experimental Forth passes (shift, instantiation, beta reduction, comparison, conversion, inference, level operations, names, the definition probe) and the program words agree with pinned Lean | General correctness: agreement on samples is evidence, not proof |

The individual targets can be run on their own, for example
`make test-core` or `make reference-first-checker`; `make check` runs every
one in the Makefile's `DIFFERENTIAL_TARGETS`. The
[testing strategy](../development/TESTING_STRATEGY.md) describes the layers
and the planted-fault checks behind them.

## Tools you can run on your own files

Check a small export with the experimental first checker, one verdict per
declaration and an exit status ([the command line](COMMAND_LINE.md)):
`bin/leanforth check FILE.ndjson`.

Count the records of any lean4export 3.1.0 file written by Lean 4.35.0
(`gforth-fast` is about three times faster than `gforth`). The file is
checked by default against the manifest that LeanForth's export step
(`scripts/export.sh`) wrote beside it, `FILE.manifest.json`: its SHA-256,
size, lines and records of each kind
([manifests](../development/NDJSON_READER.md#manifests)). A missing or
wrong manifest is an error; `count-export-unchecked` skips the check.

```sh
.tools/gforth/bin/gforth-fast src/import/ndjson-count.fs \
  -e 's" tests/reference/composition.ndjson" count-export bye'
```

```text
decl.thm                        1             67 B    67.0 B/rec
expr.app                        2             69 B    34.5 B/rec
expr.bvar                       5             92 B    18.4 B/rec
expr.forallE                    7            504 B    72.0 B/rec
expr.lam                        6            419 B    69.8 B/rec
expr.sort                       1             18 B    18.0 B/rec
meta                            1            173 B   173.0 B/rec
name                           12            445 B    37.1 B/rec
names 12 levels 0 exprs 21
total bytes 1787 name string bytes 37
max const universe args 0 max decl level params 0 lp histogram [(0, 1)]
inductive types 0 ctors 0 recursors 0
```

On the whole pinned Mathlib export (6.26 GB) it takes about 1 min 49 s in 17 MB
([reader guide](../development/NDJSON_READER.md)). Every record is decoded
and checked for shape and references; nothing is type-checked. A bad file
gives one line instead, for example `error: invalid: unexpected character
(line 1, byte 0)`, and exit status 1; a report ends with exit status 0.

Translate a Forth file into the program IR (from inside Gforth, after
`.tools/gforth/bin/gforth src/main.fs`):

```forth
: type-line ( c-addr u -- ) type cr ;
' type-line s" src/program/clamp.fs" lf-ir-read-file .
```

It prints the IR text shown in [program IR](../programming/PROGRAM_IR.md)
and then the outcome, 0. Any word outside IR 0.1 stops it with one
diagnostic line and *unsupported*, *invalid* or *full*.

Print the proof outline of every declaration of a Lean export (or of the
one named `NAME`), or with `DETAIL=1` every step of the checker's
derivation log ([proof outline](PROOF_OUTLINE.md)); this runs
`bin/leanforth print` ([command line](COMMAND_LINE.md#printing-a-readable-proof)),
with its exit status:

```sh
make print EXPORT=tests/reference/composition.ndjson
make print EXPORT=tests/reference/composition.ndjson DETAIL=1
make print EXPORT=tests/reference/constant-fixture.ndjson NAME=fixtureUse
```

Measure time and memory of an existing workload, without affecting any
result: `make profile-existing` ([profiling](../development/PROFILING.md)).
Report Forth style signals: `make forth-metrics`.

## Limits you will meet

- The term, level, name, reference and declaration stores grow up to a
  capacity that is a setting of each checker context (default 64, 64, 64,
  32 and 32 entries; `lf-term-capacity!` and the like, plan task 3.3.1);
  feeding a staged export (`src/import/feed.fs`) raises them to fit it, and
  all of `Init` (6.1 million expressions) fits in about 1.3 GB. Universe
  lists have no fixed length (Mathlib's longest has 30), and terms and
  levels no fixed depth: every checking pass keeps its pending work on
  explicit stacks in the heap (plan task 6.2.0; terms 2,000 and 10,000 deep
  are compared with Lean, `test-depth-differential` and
  `test-depth-deep-differential`). The work grows with the square of the
  depth there, so such terms need much more fuel than the default (a
  10,000-deep application chain about 150 million steps; table fuel
  10,000 million). `bin/leanforth check` still
  reads an export straight into the default capacities
  (`src/import/checker-input.fs`), so it ends *full*, exit status 3, on
  anything larger than a test fixture until it uses the feed.
- The checking passes run with explicit fuel; running out gives
  *exhausted*, running out of room *full*. Neither is ever accepted.
- Only the pinned exporter, format and Lean version are read; anything else
  is *unsupported*.

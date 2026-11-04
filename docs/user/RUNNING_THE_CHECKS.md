# Running the checks today

LeanForth has no `leanforth` command yet (plan task 3.4.1). What you can
run are the test suites and the comparisons with Lean, through `make`, and
a few Forth tools. This page says what each one runs, what a pass shows,
and — just as important — what it does not show. Status 2026-11-02, commit
`fc558cc`.

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

| Command | Needs | Time, measured 2026-11-02 | Runs |
| --- | --- | --- | --- |
| `make test` | Gforth and Python 3 | about 7 s | Documentation, Lean-source and portability checks, the silent-load check of every module, the test harness's own tests, every Forth unit test, the NDJSON reader's file tests, the fixture bridge, the program examples, the term printer, the receipt schema and the IR reader |
| `make check` | also Lean 4.35.0 | 90–100 s | `make test`, then every comparison with pinned Lean |

Both stop at the first failure and exit with a nonzero status. CI runs
`make test` on Ubuntu's Gforth 0.7.3 and `make check` on the pinned tools
for every push to `main` ([project progress](../project/PROJECT_PROGRESS.md)
records the latest runs). Run `make test` before every commit.

## What each part shows, and what it does not

| Target | A pass shows | It does not show |
| --- | --- | --- |
| `check-docs` | Every relative link in the documentation and every `docs/` path mentioned in sources resolves | That the text is right |
| `check-lean-sources` | No Lean test file contains `sorry`, `admit`, `native_decide` or an unlisted axiom, and every Lean call treats warnings as errors | Anything about LeanForth |
| `check-portable-forth` | The Forth source avoids the byte-order and cell-size dependencies the [style guide](../development/FORTH_STYLE.md) forbids, and loads modules with `require` | That it runs on another Forth |
| `smoke` | `src/main.fs` and every module, loaded on its own, load silently (no missing dependency, no redefinition) | Behaviour |
| `test-harness` | The test harness fails on a wrong value and on a wrong stack depth, as it must | — |
| `test-lib` | The library — stores, walks, frames, contexts, the job pool on threads, cooperative and serial hosts, the line reader, JSON — meets its unit tests, including stack overflows inside jobs and a randomized model of contexts | Speed (`tests/lib/task-bench.fs` is report-only) |
| `test-core` | The data model and the experimental checking passes meet their unit tests, including refused inputs, stale handles, fuel and room limits; the NDJSON reader decodes the fixtures exactly as Python's `json` module does and fails at the expected line on 13 broken files and a seeded mutation sweep | That any inferred type is a checked result |
| `test-composition-fixture` | The test-only Python bridge stages the pinned fixtures into the Forth stores, and the definition probe reaches the expected diagnostics | Import or checking of real libraries |
| `test-program` | The six example words give the expected results on sample and small exhaustive inputs | That the words are correct for all inputs: testing is not proof |
| `test-program-ir` | The receipt schema accepts its valid examples and refuses each invalid one for its pinned reason; the reference models copied into the IR's Lean file are verbatim; the IR reader's output for the example words equals the golden IR | That the reader's translation is faithful |
| `test-present` | The term printer meets its unit tests, ends every print of 49 cases in three modes at every fuel level with a defined outcome, and prints the golden text for those cases and the five fixtures | That the printed text is what Lean prints (that is `test-printer-differential`) |
| `reference`, `reference-export` | The Lean reference files check with pinned Lean and fail on `sorry`; re-exporting the fixtures gives byte-identical NDJSON | Anything about LeanForth |
| `reference-first-checker` | Lean's verdicts on the first checker's 60 expected-results cases and 27 broken source copies are as recorded ([expected results](../reviews/FIRST_CHECKER_EXPECTED.md)) | LeanForth's answers (that is `test-first-checker-differential`) |
| `reference-binder-domains` | Lean's answers on comparing binders whose argument types differ ([ADR 0003, Amendment 1](../adr/0003-conversion.md)) | LeanForth's answers (that is `test-binder-domains-differential`) |
| `test-first-checker-differential`, `test-binder-domains-differential`, `test-universe-scope-differential` | The first checker, run end to end through the checked environment, gives the expected outcome on the 62 table cases, the 22 binder-domain cases (three known capacity differences, each a failure) and 17 universe-scope cases; every rejection names Lean's reason; every accepted case prints its *experimental* label ([first check](FIRST_CHECK.md)) | That the checker is correct beyond these cases, or reviewed: it has not passed its gate |
| `test-environment` | The checked environment and check-declaration meet their unit tests: every outcome, Lean's order, fuel sweeps, and the pinned NDJSON exports checked and accepted | The same |
| `reference-program-ir` | Lean proves the six words' IR equal to their reference models, using only `propext`, `Classical.choice` and `Quot.sound`, and the IR it prints equals the reader's | Anything checked by LeanForth, or the host's behaviour |
| `test-printer-differential` | The printer's Unicode output equals Lean's own printing on 49 cases and the five fixtures' `#print` lines, and its ASCII output, read back by Lean, elaborates to the original declarations | That any printed statement was checked |
| `test-*-differential` | On finite tables, the experimental Forth passes (shift, instantiation, beta reduction, comparison, conversion, inference, level operations, names, the definition probe) and the program words agree with pinned Lean | General correctness: agreement on samples is evidence, not proof |

The individual targets can be run on their own, for example
`make test-core` or `make reference-first-checker`; `make check` runs every
one in the Makefile's `DIFFERENTIAL_TARGETS`. The
[testing strategy](../development/TESTING_STRATEGY.md) describes the layers
and the planted-fault checks behind them.

## Tools you can run on your own files

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

Measure time and memory of an existing workload, without affecting any
result: `make profile-existing` ([profiling](../development/PROFILING.md)).
Report Forth style signals: `make forth-metrics`.

## Limits you will meet

- The term, level, name, reference and declaration stores grow up to a
  capacity that is a setting of each checker context (default 64, 64, 64,
  32 and 32 entries; `lf-term-capacity!` and the like, plan task 3.3.1);
  feeding a staged export (`src/import/feed.fs`) raises them to fit it, and
  all of `Init` (6.1 million expressions) fits in about 1.3 GB. A constant
  reference takes at most 64 universe arguments (Mathlib's largest has 30).
  The checking passes nest at most 64 deep (`lf-depth-limit`): a deeper
  term gives *full* (plan task 6.2.0 lifts it).
- The checking passes run with explicit fuel; running out gives
  *exhausted*, running out of room *full*. Neither is ever accepted.
- Only the pinned exporter, format and Lean version are read; anything else
  is *unsupported*.

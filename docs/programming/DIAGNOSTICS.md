# Diagnostics: why a check failed

Status: implemented 2026-11-02 in `src/core/diagnostics.fs`, a first,
minimal form of [plan section 6.7](../project/PLAN_DRAFT.md#67-error-and-diagnostic-reporting).
Untrusted, like the rest of the checker: a diagnostic explains a failure,
it is never part of a verdict.

## What it is

Every check ends with an outcome ([ADR 0008](../adr/0008-outcome-vocabulary.md)):
ok, invalid, exhausted, unknown, rejected, unsupported or full. The outcome
says *what* happened; the diagnostic says *why*: when a check fails, the
place where it failed records

- a **reason code** from the catalogue below (for example 2, *term store
  full*),
- the **site**: the module and word that found the failure, as a counted
  string (for example `terms lf-term-add`),
- **two numbers** whose meaning the code defines (for example the store's
  count and capacity, 64 and 64).

Rules:

- **The first failure wins.** Once a diagnostic is recorded, later failures
  are ignored until the caller clears the record. A failure deep inside a
  check therefore keeps its own, more specific reason: a type inference
  that runs out of room because the term store is full reports *term store
  full at `terms lf-term-add`*, not the inference's own *full*.
- **Clear before, read after.** Call `lf-diag-clear` before a check and read
  the record only after a failed outcome. A record holds whatever failed
  first since it was last cleared, even in an earlier check.
- **It never changes an outcome, a result or fuel.** Recording only writes
  the record, and no check reads it. Evidence below.
- **One record per checker context** (`lib/context.fs`): each task, and
  each context, explains its own failures. A new context starts clear.

## Using it

| Word | Stack effect | Meaning |
| --- | --- | --- |
| `lf-diag-clear` | `( -- )` | Clear the record. |
| `lf-diag-clear?` | `( -- flag )` | True while nothing is recorded. |
| `lf-diag-code@` | `( -- code )` | The reason code, 0 while clear. |
| `lf-diag@` | `( -- n1 n2 site code )` | Everything recorded; `site` is a counted string (0 while clear). |
| `lf-diag.` | `( -- )` | Print it, or `no diagnostic`. |
| `lf-diag-name` | `( code -- c-addr u )` | The printed name of a code. |
| `lf-diag-note` | `( n1 n2 site code -- )` | Record, unless something is recorded already (for sites). |

A check whose result does not fit (Forth, after `require src/main.fs`;
`root` and `id` are the handle of a term whose type needs more nodes than
the term store has left):

```forth
lf-diag-clear
token root id 100000 lf-mixed-infer   \ gives -1 0 6: no type, full
lf-diag.                              \ term store full at terms lf-term-add: 64 64
```

Tests compare codes and numbers, never the printed wording.

## Catalogue

Numbers are stable. Unless the table says otherwise, the two numbers are
what was used and the limit.

| Code | Printed name | Outcome | First number | Second number | Recorded at |
| --- | --- | --- | --- | --- | --- |
| 0 | (no diagnostic) | — | 0 | 0 | — |
| 1 | fuel exhausted | exhausted | fuel left (0; negative if corrupted) | 0 | every walk and recursive pass (see *Sites*), `level-value`, `level-compare`, `mixed-infer`, `mixed-signature-audit` |
| 2 | term store full | full | count | capacity | `terms lf-term-add` |
| 3 | level store full | full | count, or the index a planned node would get | capacity | `levels lf-level-add`; `level-substitute lf-lsubst` when planning |
| 4 | name store full | full | count | capacity | `names lf-name-intern` |
| 5 | name bytes full | full | bytes needed | byte capacity | `names lf-name-intern` (a string component) |
| 6 | reference store full | full | count | capacity | `constant-references lf-cref-new` |
| 7 | signature index full | full | count | capacity | `mixed-signature-probe lf-msp-put` |
| 8 | identity serial spent | full | the store's serial | identities needed | the term, level, name and reference stores (1 needed); `level-substitute lf-lsubst` (the nodes it would add) |
| 9 | work stack full | full | cells pending | capacity | every walk |
| 10 | frame limit | full | frames in use | limit | `mixed-shift`, `mixed-instantiate`, `mixed-beta` (both numbers the limit: every frame was in use); `mixed-infer` |
| 11 | depth limit | full | depth | limit | `level-value`, `level-compare` |
| 12 | binder context full | full | binders | limit | `constant-term-scope` and `mixed-rebuild lf-rebuild-binary` (a binder depth at the largest cell, `max-n` twice); `mixed-infer` (binders, capacity) |
| 13 | value at cell maximum | full | the value | the amount to add | `level-value` (a successor of `max-n`: value, 1); `mixed-shift` (variable index, shift amount) |
| 14 | heap allocation failed | full | bytes | the `ALLOCATE` ior | reserved: no site in `core/` or `kernel/` allocates; see *Not yet covered* |
| 20 | invalid input: bad argument | invalid | the value | 0 | negative fuel: `mixed-infer`, `level-compare`, `mixed-signature-audit` |
| 21 | invalid input: stale handle | invalid | index | identity | `constant-term-boundary lf-cterm-check`, through which every kernel pass audits its roots |
| 22 | invalid input: malformed graph | invalid | the node being visited | 0 | every walk, when nothing more specific was recorded |
| 23 | invalid input: out of scope | invalid | variable index, or parameter ID | binders, or 0 for a parameter | `constant-term-scope` (an unbound variable), `level-scope` (a parameter outside the context) |
| 24 | invalid input: corrupted store | invalid | count | capacity | the four stores, when a store fails its own checks |
| 30 | undecided: terms or levels differ | unknown | left node or level | right node or level | `mixed-compare`, `mixed-convert` (the pair being compared), `level-compare` (its two roots) |
| 31 | undecided: function type not a Pi | unknown | the function's type node | 0 | `mixed-infer` |
| 32 | undecided: type not a Sort | unknown | the type node | 0 | `mixed-infer` |
| 33 | undecided: no candidate signature | unknown | the constant's name ID | 0 | `mixed-signature-probe lf-msp-specialize` |
| 34 | undecided: symbolic level | unknown | the level | 0 | `level-value` |
| 40 | unsupported construct | unknown today | the node's tag | 0 | `mixed-infer` (a constructor outside its subset; the outcome becomes *unsupported* with ADR 0008 step 3) |

Codes 1–14 explain *exhausted* (more fuel would help) and *full* (more
memory or a larger limit would help); 20–24 explain *invalid* input; 30–34
explain *unknown* (a stronger rule would help); 40 names a construct still
to be built.

### Sites

Walk sites (codes 1, 9 and 22, and 30 for paired comparisons) are
recorded after each walk, by `lf-diag-walk`, at: `level-scope
lf-lscope-check`, `constant-term-boundary lf-cterm-check`,
`constant-term-scope lf-constant-term-scope`, `generation-handles
lf-hterm-check`, `symbolic-session lf-ssession-check`,
`tagged-sort-boundary lf-repr-check`, `level-substitute lf-lsubst`,
`mixed-compare lf-mixed-compare` (term and level walks),
`mixed-convert lf-mixed-convert` and `mixed-level-substitute
lf-mixed-level-substitute`. Recursive-pass sites (codes 1 and 10) are
recorded after each pass, by `lf-diag-frames`, at `mixed-shift
lf-mixed-shift`, `mixed-instantiate lf-mixed-instantiate` and `mixed-beta
lf-mixed-beta`. A failure some check inside a walk or pass recorded first
is kept.

## Evidence (2026-11-02)

- `tests/core/diagnostics.fs` (in `make test`, Gforth 1.0 and 0.7.3): the
  record and its first-failure rule; every store's full, spent-serial and
  corrupted cases; a fuel sweep of every walk and pass that finds each
  site's own exhaustion and the fuel code on every exhausted run; the room
  limits a 64-node store cannot reach, white-box (a work stack of capacity
  1, frames limited to 1, the depth limits, the cell maximum, full binder
  contexts); the shift past the largest cell, the shift with no room for a
  binder, a substitution that fills the level store or spends its serial,
  a shift that fills the term store; and each invalid and undecided code.
- Over random checker work (`tests/support/checker-trial.fs`, 8 trials of
  1,000 steps, cleared before every check) every outcome is explained by
  its family: 9,953 checks, 0 unexplained; 4,567 ok with nothing recorded;
  all 1,923 exhausted and 44 full outcomes recorded (codes 1 and 2); 1,999
  of 1,999 unknown and 1,112 of 1,420 invalid outcomes recorded (codes 21,
  22, 23, 30–34).
- Outcomes, results and fuel are unchanged: the randomized differentials
  against the code before diagnostics and contexts (commit `f8aa35d`;
  group H's harnesses, seeds 1–150; group B's, seeds 1–300 of 3,000
  operations on Gforth 1.0 and seeds 1–60 on 0.7.3) show no difference,
  and the digests of 24 trials of 2,000 steps are identical with and
  without diagnostics.
- Planted faults are caught: a record that overwrites the first failure
  (by the unit test, and without it by the shift case, whose frame limit
  would hide the cell maximum), a site that forgets to record, and a wrong
  code.
- Cost: the fixed checker workload of the [library notes](../development/FORTH_LIBRARY.md#design-per-task-contexts-and-how-modules-convert)
  took about 1% longer.

## Not yet covered

The plan's full design adds what this first form lacks: a stage (read,
decode, check, print), a location in the input (file, NDJSON line, record,
declaration), the rule involved, the expected and found terms printed, a
hint, and text and JSON renderers. Also missing:

- **Invalid input is not always explained.** Many invalid paths, such as a
  negative fuel at most entry points or an argument out of range, record
  nothing yet (308 of 1,420 random invalid checks above).
- **Outside `core/` and `kernel/`.** The NDJSON reader (`src/import/`,
  `src/lib/bytes.fs`, `json.fs`) has its own error messages and would
  record code 14 for a failed `ALLOCATE` and its own invalid-input codes;
  `src/program/` and `src/present/` record nothing yet; `context-new` and
  the job pool report allocation failures as iors.
- **No record of recovered failures.** None is known in the checker, but a
  caller that tries one check and then another must clear between them.

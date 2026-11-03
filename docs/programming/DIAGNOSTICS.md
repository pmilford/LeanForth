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
  full at `terms lf-term-add`*, not the inference's own *full*. One
  exception: a rejection rule of ADR 0011 that decides an undecided step
  replaces that step's record with the rule's (codes 55–60), so that a
  *rejected* outcome is always explained by its rule.
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
| 7 | signature index full | full | count | capacity | `mixed-signature-probe lf-msp` (in `lf-msp-put`) |
| 8 | identity serial spent | full | the store's serial | identities needed | the term, level, name and reference stores (1 needed); `level-substitute lf-lsubst` (the nodes it would add) |
| 9 | work stack full | full | cells pending | capacity | every walk |
| 10 | frame limit | full | frames in use | limit | `mixed-shift`, `mixed-instantiate`, `mixed-beta` (both numbers the limit: every frame was in use); `mixed-infer` |
| 11 | depth limit | full | depth | limit | `level-value`, `level-compare` |
| 12 | binder context full | full | binders | limit | `constant-term-scope` and `mixed-rebuild lf-rebuild-binary` (a binder depth at the largest cell, `max-n` twice); `mixed-infer` (binders, capacity) |
| 13 | value at cell maximum | full | the value | the amount to add | `level-value` (a successor of `max-n`: value, 1); `mixed-shift` (variable index, shift amount) |
| 14 | heap allocation failed | full | bytes | the `ALLOCATE` ior | reserved: no site in `core/` or `kernel/` allocates; see *Not yet covered* |
| 15 | dependency list full | full | dependencies recorded | `lf-env-dep-capacity` | `environment lf-env-depend` (the check's candidate) |
| 16 | dependency pool full | full | dependencies needed (in the pool plus the candidate's) | the pool's capacity | `env-publish lf-env-append` |
| 20 | invalid input: bad argument | invalid | the value | 0 | negative fuel: `mixed-infer`, `level-compare`, `mixed-signature-audit` |
| 21 | invalid input: stale handle | invalid | index | identity | `constant-term-boundary lf-cterm-check`, through which every kernel pass audits its roots |
| 22 | invalid input: malformed graph | invalid | the node being visited (-1 when the walk ended before its first visit) | 0 | every walk, when nothing more specific was recorded |
| 23 | invalid input: out of scope | invalid | variable index, or parameter ID | binders, or 0 for a parameter | `constant-term-scope` (an unbound variable), `level-scope` (a parameter outside the context) |
| 24 | invalid input: corrupted store | invalid | count | capacity | the four stores, when a store fails its own checks |
| 25 | invalid: environment handle | invalid | the handle's (or snapshot's) environment identity | the slot | `environment lf-env-handle?`; `environment lf-env-accepted` (a dependency or parameter query on a slot the snapshot may not read, or not accepted) |
| 26 | invalid: check started too early | invalid | the same-named slot that is not final | the declaration checked | `environment lf-env-lookup` (also for N2 on the declaration's own name) |
| 27 | invalid: no snapshot | invalid | the context's snapshot identity (0 for none) | the current environment's identity, or 0 | `environment lf-env-snapshot` (no valid current environment for this context's input, or a snapshot of another one) |
| 28 | invalid: publisher re-check failed | invalid | the declaration | the part: 1 dependencies, 2 axiom set, 3 provenance, 4 name (N2, G-P5), 5 kind, safety, value or parameters | `env-publish lf-env-publish` (a fault in LeanForth) |
| 29 | invalid: internal fault | invalid | the declaration | the `THROW` code | `env-publish lf-env-step` (a check threw), `env-publish lf-env-hand-over` (the publisher threw) |
| 30 | undecided: terms or levels differ | unknown | left node or level | right node or level (0 after a walk that is not paired) | `mixed-compare`, `mixed-convert` (the pair being compared), `level-compare` (its two roots) |
| 31 | undecided: function type not a Pi | unknown | the function's type node | 0 | `mixed-infer` |
| 32 | undecided: type not a Sort | unknown | the type node | 0 | `mixed-infer` |
| 33 | undecided: no candidate signature | unknown | the constant's name ID | 0 | `mixed-signature-probe lf-msp` (in `lf-msp-specialize`) |
| 34 | undecided: symbolic level | unknown | the level | 0 | `level-value` |
| 35 | undecided: dependency undecided | unknown | the earlier slot (the first of that name) | its outcome | `environment lf-env-lookup` (K5; also for N2) |
| 40 | unsupported construct | unknown today | the node's tag | 0 | `mixed-infer` (a constructor outside its subset; the outcome becomes *unsupported* with ADR 0008 step 3) |
| 41 | unsupported: dependency unsupported | unsupported | the earlier slot | 0 | `environment lf-env-lookup` (K5; also for N2) |
| 50 | rejected: unknown constant | rejected | the name ID | the declaration checked | `environment lf-env-lookup` (N1: unknown, forward and self references) |
| 51 | rejected: name already declared | rejected | the name ID | the accepted slot | `environment lf-env-own-name` (N2) |
| 52 | rejected: wrong number of universe levels | rejected | levels given | the constant's parameters | `environment lf-env-arity?` (L1) |
| 53 | rejected: undeclared universe parameter | rejected | the name ID | 0 | `environment lf-env-param?` (L2) |
| 54 | rejected: duplicate universe parameter | rejected | the declaration | 0 | `environment lf-env-own-params` (L3) |
| 55 | rejected: type expected (S1) | rejected | the declared type's type, reduced (whnfβ) | 0 | `mixed-definition-probe lf-mixed-definition-probe` |
| 56 | rejected: binder domain not a type (S2) | rejected | the domain's type, reduced | 0 | `mixed-infer lf-mixed-infer` (a λ's or Π's domain) |
| 57 | rejected: theorem type not a proposition (S3) | rejected | the level of the statement's Sort | 0 | `mixed-definition-probe lf-mixed-definition-probe` (`lf-mixed-theorem-probe`) |
| 58 | rejected: function expected (F1) | rejected | the function's type, reduced | 0 | `mixed-infer lf-mixed-infer` (an application) |
| 59 | rejected: argument type mismatch (D1-D5) | rejected | the D rules used: 1 D1, 2 D2, 4 D3, 8 D4, 16 D5, added | 0 | `mixed-infer lf-mixed-infer` (an argument's type against the function's domain) |
| 60 | rejected: declared type mismatch (D1-D5) | rejected | the D rules used, as for 59 | 0 | `mixed-definition-probe lf-mixed-definition-probe` (the value's type against the claim) |

Codes 1–16 explain *exhausted* (more fuel would help) and *full* (more
memory or a larger limit would help); 20–29 explain *invalid* input or
state; 30–35 explain *unknown* (a stronger rule, or a decided dependency,
would help); 40–41 name a construct still to be built; 50–60 explain
*rejected*: 50–54 by the checked environment (ADR 0011's rules N1, N2,
L1–L3), 55–60 by comparison and inference (S1–S3, F1, D1–D5; plan task
2.2.1). A rejection by 55, 56, 58, 59 or 60 decides a step that was
undecided and had recorded why (codes 31, 32 or 30); the rejection
*replaces* that record, the one exception to "the first failure wins",
because the rule is the more specific reason for the same failure. When
the rule cannot decide, the undecided record stays. The D rules record the
rules used from the compared pair down to the pair that decided: in
`type-identity.wrong-argument` of the
[expected results](../reviews/FIRST_CHECKER_EXPECTED.md) the claim and
the proof's type are Πs (D4) whose bodies `P y` and `P x` apply the same
variable (D5) to different variables (D3), so the first number is
8 + 16 + 4 = 28.

Codes 15, 16, 25–29, 35, 41 and 50–54 are the checked environment's
([its page](CHECKED_ENVIRONMENT.md)), added 2026-11-02.
`lf-env-begin` clears the record before each check, and the serial driver
reads it per declaration.

Every code is a constant in `src/core/diagnostics.fs`, and its printed name
is an entry of one table there, `lf-diag-catalogue` (code order, ending
with the entry that names every other code "unknown code"), which
`lf-diag-name` searches. `tests/core/check_diagnostics_catalogue.py` (in
`make test`) checks that this page's table lists exactly the table's codes
and printed names, in the same order.

### Sites

Each module that records defines one site word, `lf-X-site ( -- site )`,
naming the module and its word (`mixed-signature-probe lf-msp` for both of
that module's failures, which differ by code). Walk sites (codes 1, 9 and 22, and 30 for paired comparisons) are
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
  22, 23, 30–34). Since the rejection rules (plan task 2.2.1), 248 of the
  1,999 unknown checks are rejected instead, each recorded with its rule
  (55: 34, 56: 1, 58: 50, 59: 39, 60: 124), and every other count is the
  same.
- Outcomes, results and fuel are unchanged: the randomized differentials
  against the code before diagnostics and contexts (commit `f8aa35d`;
  group H's harnesses, seeds 1–150; group B's, seeds 1–300 of 3,000
  operations on Gforth 1.0 and seeds 1–60 on 0.7.3) show no difference,
  and the digests of 24 trials of 2,000 steps are identical with and
  without diagnostics.
- The trial also folds each check's diagnostic (code and numbers, cleared
  before the check) into its digest, so `tests/core/contexts.fs` checks
  that every context records the same diagnostics interleaved, as jobs and
  alone (2026-11-02, review M3).
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

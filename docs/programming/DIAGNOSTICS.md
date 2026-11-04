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
| 1 | fuel exhausted | exhausted | fuel left (0; negative if corrupted) | 0 | every walk and recursive pass (see *Sites*), `level-value`, `level-normalize` (level comparison), `mixed-infer`, `mixed-signature-audit` |
| 2 | term store full | full | count | capacity | `terms lf-term-add` |
| 3 | level store full | full | count, or the index a new node would get | capacity | `levels lf-level-add`; `level-substitute lf-lsubst` before it adds a node |
| 4 | name store full | full | count | capacity | `names lf-name-intern` |
| 5 | name bytes full | full | bytes needed | byte capacity | `names lf-name-intern` (a string component) |
| 6 | reference store full | full | count | capacity | `constant-references lf-cref-new` |
| 7 | signature index full | full | count | capacity | `mixed-signature-probe lf-msp` (in `lf-msp-put`) |
| 8 | identity serial spent | full | the store's serial | identities needed | the term, level, name and reference stores (1 needed); `level-substitute lf-lsubst` (1, before it adds a node) |
| 9 | work stack full | full | cells pending | capacity | every walk; `level-normalize` (the arguments of a `max` being normalized) |
| 10 | frame limit | full | frames in use | limit | `mixed-shift`, `mixed-instantiate`, `mixed-beta`, `mixed-open` (both numbers the limit: every frame was in use); `mixed-infer` |
| 11 | depth limit | full | depth | limit | `level-value` |
| 12 | binder context full | full | binders | limit | `constant-term-scope` and `mixed-rebuild lf-rebuild-binary` (a binder depth at the largest cell, `max-n` twice); `mixed-infer` (the binders opened on its scope, the scope's capacity); `local-context lf-lctx-local` (the local context's entries, its capacity: plan task 4.2.2a) |
| 13 | value at cell maximum | full | the value | the amount to add | `level-value` (a successor of `max-n`: value, 1); `mixed-shift` (variable index, shift amount) |
| 14 | heap allocation failed | full | bytes | the `ALLOCATE` ior | reserved: no site in `core/` or `kernel/` allocates; see *Not yet covered* |
| 15 | dependency list full | full | dependencies recorded | `lf-env-dep-capacity` | `environment lf-env-depend` (the check's candidate) |
| 16 | dependency pool full | full | dependencies needed (in the pool plus the candidate's) | the pool's capacity | `env-publish lf-env-append` |
| 20 | invalid input: bad argument | invalid | the value | 0 | negative fuel: `mixed-infer`, `level-compare`, `mixed-signature-audit` |
| 21 | invalid input: stale handle | invalid | index | identity | `constant-term-boundary lf-cterm-check`, through which every kernel pass audits its roots |
| 22 | invalid input: malformed graph | invalid | the node being visited (-1 when the walk ended before its first visit) | 0 | every walk, when nothing more specific was recorded; `mixed-infer` (a free variable that the local context does not name) |
| 23 | invalid input: out of scope | invalid | variable index, or parameter ID | binders, or 0 for a parameter | `constant-term-scope` (an unbound variable), `level-scope` (a parameter outside the context), `mixed-infer` (a bound variable beyond the binders open on its scope, which preflight finds first in any input: its index, the binders open) |
| 24 | invalid input: corrupted store | invalid | count | capacity | the four stores, when a store fails its own checks |
| 25 | invalid: environment handle | invalid | the handle's (or snapshot's) environment identity | the slot | `environment lf-env-handle?`; `environment lf-env-accepted` (a dependency or parameter query on a slot the snapshot may not read, or not accepted) |
| 26 | invalid: check started too early | invalid | the same-named slot that is not final | the declaration checked | `environment lf-env-lookup` (also for N2 on the declaration's own name) |
| 27 | invalid: no snapshot | invalid | the context's snapshot identity (0 for none) | the current environment's identity, or 0 | `environment lf-env-snapshot` (no valid current environment for this context's input, or a snapshot of another one) |
| 28 | invalid: publisher re-check failed | invalid | the declaration | the part: 1 dependencies, 2 axiom set, 3 provenance, 4 name (N2, K5, G-P5: a same-named earlier slot not final or not rejected; or a corrupted name store), 5 kind, safety, value or parameters, 6 the snapshot (the check began another declaration) | `env-publish lf-env-hand-over` (parts 1–5), `env-publish lf-env-step` (part 6); a fault in LeanForth |
| 29 | invalid: internal fault | invalid | the declaration | the `THROW` code, or 0 | `env-publish lf-env-step` (a check threw, including -4096 `lf-env-unbalanced` for a check that changed the stack and -4110 `lf-env-refused` for one that called an internal word writing the environment; also `lf-env-thrown` and `lf-env-hand-over-job`, for a job that threw), `env-publish lf-env-hand-over` (the publisher threw; 0: a publication ended without a final slot), `environment lf-env-begin` (0: the context is spent, a check in it threw, G-P6) |
| 30 | undecided: terms or levels differ | unknown | left node or level | right node or level (0 after a walk that is not paired) | `mixed-compare`, `mixed-convert` (the pair being compared), `level-compare` (its two roots) |
| 31 | undecided: function type not a Pi | unknown | the function's type node | 0 | `mixed-infer` |
| 32 | undecided: type not a Sort | unknown | the type node | 0 | `mixed-infer` |
| 33 | undecided: no candidate signature | unknown | the constant's name ID | 0 | `mixed-signature-probe lf-msp` (in `lf-msp-specialize`) |
| 34 | undecided: symbolic level | unknown | the level | 0 | `level-value` |
| 35 | undecided: dependency undecided | unknown | the earlier slot (the first of that name) | its outcome | `environment lf-env-lookup` (K5; also for N2) |
| 36 | undecided: Lean's level depends on sharing (K6) | unknown | the `max` or `imax` node of the constant's type | 0 | `level-substitute lf-lsubst` (ADR 0011, Amendment 1: Lean keeps the node only when the universe arguments are the very objects in memory its type holds) |
| 40 | unsupported construct | unknown | the node's tag | 0 | `mixed-infer` (a constructor outside its subset; in a declaration's check the audit finds every unsupported form first, code 43, so inference never meets one there) |
| 41 | unsupported: dependency unsupported | unsupported | the earlier slot | 0 | `environment lf-env-lookup` (K5; also for N2) |
| 42 | unsupported: declaration kind (U1) | unsupported | the declaration's kind (`lf-kind-…`) | its safety (`lf-safety-…`) | `check-declaration lf-check-declaration` (anything but a safe definition or theorem: an axiom, an opaque declaration, an unsafe or partial definition, …) |
| 43 | unsupported: term form (U2) | unsupported | the form (`lf-form-…`: 1 let, 2 natural-number literal, 3 string literal, 4 metadata, 5 projection) | the node | `check-declaration lf-check-declaration` (the declaration audit, before any typing) |
| 50 | rejected: unknown constant | rejected | the name ID | the declaration checked | `environment lf-env-lookup` (N1: unknown, forward and self references) |
| 51 | rejected: name already declared | rejected | the name ID | the accepted slot | `environment lf-env-own-name` (N2) |
| 52 | rejected: wrong number of universe levels | rejected | levels given | the constant's parameters | `environment lf-env-arity?` (L1) |
| 53 | rejected: undeclared universe parameter | rejected | the name ID | 0 | `environment lf-env-param?` (L2) |
| 54 | rejected: duplicate universe parameter | rejected | the declaration | 0 | `environment lf-env-own-params` (L3) |
| 55 | rejected: type expected (S1) | rejected | the declared type's type, reduced (whnfβ) | 0 | `mixed-definition-probe lf-mixed-definition-probe`; `check-declaration lf-check-declaration` |
| 56 | rejected: binder domain not a type (S2) | rejected | the domain's type, reduced | 0 | `mixed-infer lf-mixed-infer` (a λ's or Π's domain) |
| 57 | rejected: theorem type not a proposition (S3) | rejected | the level of the statement's Sort | 0 | `mixed-definition-probe lf-mixed-definition-probe` (`lf-mixed-theorem-probe`); `check-declaration lf-check-declaration` |
| 58 | rejected: function expected (F1) | rejected | the function's type, reduced | 0 | `mixed-infer lf-mixed-infer` (an application) |
| 59 | rejected: argument type mismatch (D1-D5) | rejected | the D rules used: 1 D1, 2 D2, 4 D3, 8 D4, 16 D5, added | 0 | `mixed-infer lf-mixed-infer` (an argument's type against the function's domain) |
| 60 | rejected: declared type mismatch (D1-D5) | rejected | the D rules used, as for 59 | 0 | `mixed-definition-probe lf-mixed-definition-probe`, `check-declaration lf-check-declaration` (the value's type against the claim) |
| 61 | rejected: Pi body not a type (S4) | rejected | the body's type, reduced | 0 | `mixed-infer lf-mixed-infer` (a Π's body; ADR 0011, Amendment 2) |
| 62 | invalid input: inductive block shape (B0) | invalid | the block's first member | 0 | `inductive-block lf-ind-audit` (ADR 0015 B0: members, kinds, all and ctors lists, induct, recursors naming the block, distinct names, as lean4export writes them) |
| 63 | unsupported: inductive block outside task 5.2.1a | unsupported | the block's first member | 1 a mutual block (task 5.2.5), 2 a constructor type mentioning the type outside its result's head (recursive, 5.2.1b; in an index, 5.2.1c) | `inductive-block lf-ind-audit` |
| 64 | undecided: Lean may unfold a definition here (K1) | unknown | the node whose head is a constant | 0 | `check-block lf-block-check` (the type's telescope, where Lean's whnf may unfold) |
| 65 | rejected: reserved prefix _nested (T0) | rejected | the block's first member | 0 | `inductive-block lf-ind-audit` (`check_no_nested_aux`) |
| 66 | rejected: non-uniform occurrence of the type (C1) | rejected | the occurrence's node | its binder depth | `inductive-block lf-ind-audit` (`check_uniform_ind_occs`) |
| 67 | rejected: too few parameter binders (T1) | rejected | the type's binders | numParams | `inductive-block lf-ind-audit` (`get_params`) |
| 68 | rejected: inductive type not ending in a Sort (T2) | rejected | the type's result, reduced (whnfβ) | 0 | `check-block lf-block-check` (`check_inductive_types`: Lean's `typeExpected`) |
| 69 | rejected: constructor parameter mismatch (C2) | rejected | the D rules used, as for 59 | 0 | `check-block lf-block-check` (`check_constructors`) |
| 70 | rejected: constructor field universe too big (U1) | rejected | the constructor's member | the field's binder (from 0) | `check-block lf-block-check` (`check_constructors`, Lean's `is_geq`) |
| 71 | rejected: invalid constructor return type (C3) | rejected | the constructor's member | 0 | `check-block lf-block-check` (`is_valid_ind_app`) |
| 72 | rejected: duplicate constructor name (C4) | rejected | the constructor's member | 0 | `check-block lf-block-check` (`check_constructors`) |
| 73 | rejected: constructor differs from Lean's (B3) | rejected | the constructor's member | the field that differs (1 levelParams, 2 induct, 3 cidx, 4 numParams, 5 numFields) | `check-block lf-block-check` (Lean's replay: "Invalid constructor") |
| 74 | rejected: recursor differs from Lean's (B3) | rejected | the recursor's member | the field that differs (1 name, 2 levelParams, 3 type, 4 all, 5 numParams, 6 numIndices, 7 numMotives, 8 numMinors, 9 rules, 10 k) | `check-block lf-block-check` (Lean's replay: "Invalid recursor") |
| 75 | rejected: recursor Lean does not generate (B3) | rejected | the recursor's member | 0 | `check-block lf-block-check` (Lean's replay: "No such recursor") |
| 76 | inductive block: too many constructors | full | the block's constructors | the capacity, `lf-ind-ctor-capacity` (512) | `inductive-block lf-ind-audit` (review rvI21 B1: the whole block is *full*, before anything is written for its constructors) |
| 77 | undecided: a constant Lean's kernel holds, no slot accepted | unknown | the name | the slot that holds it | `environment lf-env-lookup`: a reference to `T.rec` that no slot holds, of a type `T` (accepted, or rejected only by B3) that left no recipe to build it again (ADR 0015 decision 12: a telescope only whnf shows). Lean's kernel holds the constant |

Codes 1–16 explain *exhausted* (more fuel would help) and *full* (more
memory or a larger limit would help); 20–29 explain *invalid* input or
state; 30–35 explain *unknown* (a stronger rule, or a decided dependency,
would help); 40–43 name a construct, a dependency, a declaration kind or
a term form still to be built; 50–60 explain
*rejected*: 50–54 by the checked environment (ADR 0011's rules N1, N2,
L1–L3), 55–60 by comparison and inference (S1–S3, F1, D1–D5; plan task
2.2.1). A rejection by 55, 56, 58, 59 or 60 decides a step that was
undecided and had recorded why (codes 31, 32 or 30); the rejection
*replaces* that record, the one exception to "the first failure wins",
because the rule is the more specific reason for the same failure. When
the rule cannot decide, the undecided record stays. The first number of
codes 55–58 may be a node (55, 56, 58: a reduced type) or a level (57)
that the check made, and the failed check's rollback frees those: the
number is a plain index for reading, not a live handle, and the store may
have reused that slot since. The D rules record the
rules used from the compared pair down to the pair that decided: in
`type-identity.wrong-argument` of the
[expected results](../reviews/FIRST_CHECKER_EXPECTED.md) the claim and
the proof's type are Πs (D4) whose bodies `P y` and `P x` apply the same
variable (D5) to different variables (D3), so the first number is
8 + 16 + 4 = 28.

Codes 15, 16, 25–29, 35, 41 and 50–54 are the checked environment's
([its page](CHECKED_ENVIRONMENT.md)), added 2026-11-02.
`lf-env-begin` clears the record before each check, and the serial driver
reads it per declaration. Codes 42 and 43 are check-declaration's
declaration audit (plan task 2.2.3, the same day). In a declaration's
check, inference meets constants and Sorts in Lean's order and asks the
environment there (`src/kernel/env-signature.fs`), so codes 35, 41 and
50–53 are recorded at the first constant or Sort, in that order, that
fails. While inference runs aside (test P2) a failed lookup may note a
code too, but only inside the rejection analysis, after the undecided
comparison recorded its own (code 30), which the first-failure rule
keeps.

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

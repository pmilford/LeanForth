# ADR 0018: exceptions — when to use `CATCH` and `THROW` — proposal

Status: **proposed**, 2026-11-02 (plan task 1.1.6, plan
[§6.10](../project/PLAN_DRAFT.md#610-the-catchthrow-decision)). A
code-structure decision for untrusted, in-progress modules, like
[ADR 0008](0008-outcome-vocabulary.md) and
[ADR 0009](0009-reentrant-state-and-parallel-checking.md): it changes no
typing or conversion rule. A kernel module that adopts it is still a
checker change and passes the [kernel] gate in `AGENTS.md` change by
change. Nothing here is implemented; the pilot below ran on a scratch
copy of the tree.

## Summary in plain words

Today every LeanForth word reports failure by returning an outcome (ok,
invalid, exhausted, full, unknown, rejected, unsupported), and every caller
checks it. That is explicit but repetitive: in the module piloted here, 33
of 58 words pass an outcome along, most only to hand a failure back up.
Forth has a second mechanism, `THROW`, which jumps straight back to the
nearest `CATCH`. This record proposes using it in one narrow way: inside
one operation, the three *exceptional* failures — malformed input
(invalid), out of fuel (exhausted) and out of room (full) — may be thrown;
the operation's entry word catches them, puts every store back as it was,
and returns the usual outcome. The three outcomes the owner cares about
(accepted, rejected, unsupported/unknown) are never thrown: callers always
see them as returned values. No thrown code can ever turn into *ok*.

## The current uses of `CATCH`, `THROW` and `ABORT"`

Surveyed in `src/` at `16bdc2f`. Every one fits the rules below.

| Site | What it does | Kind (decision 3) |
| --- | --- | --- |
| `lib/context.fs:217` `context-fill` | runs a new context's initialisers and set-up words, restores `lf-context`; `context-new` frees the block and gives the code as an ior | resource owner: release, then give an ior |
| `lib/task.fs:145` `job-run` | runs a job's word, restores the owner and context; the code becomes the job's ior | check boundary (parallel) |
| `lib/task.fs:302` `task-new` | host task creation, which can throw | host adapter: code to ior |
| `import/ndjson.fs:617` `busy-call` | calls a handler, ends the busy mark, re-throws (`0 … throw`) | resource owner: restore, re-throw |
| `import/ndjson.fs:805` `export-caught` | reads lines, closes the file, re-throws (806) | resource owner: release, re-throw |
| `import/ndjson-count.fs:172` `count-read` | the counting tool: any code is invalid ("a Forth exception") | tool top level |
| `kernel/env-publish.fs:204` `lf-env-guarded` | publishes under a pool mark; on a code rolls the pool back, clears the slot, invalid, the run stops | transaction boundary with a store mark |
| `kernel/env-publish.fs:222` `lf-env-run-check` | a check in the serial driver: invalid (diagnostic 29), the context is spent (ADR 0012, Amendment 1) | check boundary (serial) |
| `kernel/env-publish.fs:252` `lf-env-make` | the caller's context maker; restores `lf-context`; a code stops the run | caller-supplied word: code to ior |
| `program/ir-reader.fs:296` `ir-output` | the caller's output word; `ir-emit` (298) restores the reader and re-throws | caller-supplied word: restore, re-throw |
| `program/ir-reader.fs:644` `ir-read-open` | reads a file, closes it, re-throws | resource owner: release, re-throw |

`THROW` with a code of its own: `lib/task.fs:138` (`task-unbalanced`,
−4096, caught by `job-run`); `import/ndjson.fs:614–615` (−4, the standard
stack-underflow code, when a handler took more than its record);
`import/ndjson-count.fs:186` (−1, to end the tool where `(bye)` is
missing); `lib/context.fs:120` (`ALLOCATE`'s ior while loading). The others
re-throw what they caught.

`ABORT"` (code −2) after loading, for a caller that broke a contract or a
"cannot happen" state: `lib/context.fs:113–114, 213, 229–231`,
`lib/task.fs:342`, `lib/frame.fs:59` (`frame-init`, also called by the
printer), `kernel/env-publish.fs:155` (`lf-pool-put`, inside
`lf-env-guarded`'s `CATCH`), `import/ndjson.fs:597, 774`,
`program/ir-reader.fs:528, 586`, `program/ir-run.fs:519–520`. While
loading (a bad shape or table stops the load): `lib/store.fs:89`,
`lib/walk.fs:66`, `lib/context.fs:124, 132–133, 167, 169, 176, 178, 182,
189, 203`, `lib/bytes.fs:158`, `import/ndjson.fs:97`,
`import/ndjson-count.fs:36, 47`, `program/ir-reader.fs:87, 105`,
`program/ir-run.fs:73`, and the `[if] … abort [then]` checks in
`core/terms.fs:66`, `core/levels.fs:69`, `kernel/mixed-beta.fs:115`,
`kernel/mixed-infer.fs:301`, `kernel/mixed-instantiate.fs:25`,
`kernel/mixed-shift.fs:28`, `program/ir-reader.fs:178, 450, 495, 546` and
`program/ir-run.fs:135, 196`. Three modules document how to recover after
a host `THROW` out of a pass: `frame-reset` (`lib/frame.fs`),
`lf-mixed-rebuild-reset` (`kernel/mixed-beta.fs`) and `lf-print-reset`
(`present/print-job.fs`).

## Decision (proposed)

1. **What may be thrown.** Outcomes stay the interface (ADR 0008): every
   word another module or a test calls returns its outcome as today.
   *ok*, *rejected*, *unknown* and *unsupported* are always returned,
   never thrown, because callers branch on them (ADR 0012's K5 lookups,
   for example). Inside one transaction (decision 3), a module that
   adopts this ADR may throw *invalid*, *exhausted* and *full* instead of
   returning them, with the codes of decision 2. A walk or frames visitor
   (`lib/walk.fs`, `lib/frame.fs`) never throws: those libraries are
   outcome protocols, and a `THROW` out of a visit leaves the record busy.

2. **Codes.** Forth-2012 (section 9.3.1) reserves −1 to −255 for the
   standard and −4095 to −256 for the system; a program uses the rest.
   Measured on both CI hosts (2026-11-02), every code the hosts produce is
   in those ranges: the standard codes, Gforth's operating-system iors
   (−512 minus `errno`: −514, −524, −533 seen) and codes Gforth's
   `exception` hands out (from −2051 on 0.7.3, −2077 on 1.0, downwards).
   LeanForth reserves **−4096 to −4351**:

   | Code | Name | Meaning | Thrown? |
   | --- | --- | --- | --- |
   | −4096 | `task-unbalanced` | a job's word changed the stack depth (exists) | yes, caught by `job-run` |
   | −4097 to −4101 | `task-overflow`, `task-refused`, `task-queue-full`, `task-no-worker`, `task-stacks-small` | job pool refusals (exist) | no: returned as iors |
   | −4102 to −4111 | — | reserved for the job pool | — |
   | −4112 − *k* | — | outcome *k* thrown: −4113 invalid, −4114 exhausted, −4118 full | only these three |
   | −4112, −4115 to −4117 | — | ok, unknown, rejected, unsupported: never thrown; reserved so the mapping stays one rule | never |
   | −4119 to −4127 | — | reserved for outcomes added later | — |
   | −4128 | `throw-fault` | a fault in LeanForth: a broken internal invariant | yes; only a check boundary or a top level turns it into an outcome |
   | −4129 | `lf-author-throw` | an authoring error, recorded in the authoring program's error record (`src/author/errors.fs`; added with plan task 8.1.2) | yes; caught only by the authoring runner, a top level |
   | −4130 to −4351 | — | unassigned; assigned only by amending this table | — |

   Never `THROW` 0 (it does nothing), an outcome's own number, or a
   positive code (some hosts return positive iors). Run-time "cannot
   happen" `ABORT"` sites inside a check move to `throw-fault` when their
   module is next changed; load-time `ABORT"` and driver contract checks
   keep their messages.

3. **Who may `CATCH`.** Four kinds of word, and no others:
   - a **transaction boundary**: the entry word of one operation that
     allocates in stores (the pilot's `lf-mixed-level-substitute`). It
     marks every store the operation may allocate in *before* its `CATCH`,
     catches everything, rolls back to the marks, maps −4113, −4114 and
     −4118 to their outcomes, and throws every other code on after its
     rollback. Its callers see outcomes only. The publisher's
     `lf-env-guarded` is one too, with a stricter mapping: it runs outside
     every check, so any code there is a fault that stops the run (ADR
     0012, E4);
   - a **check boundary**: `lf-env-step` (through `lf-env-run-check`) and,
     in parallel runs, `job-run` with `lf-env-thrown`. Every code that
     reaches it — a host error, `throw-fault`, or a failure code that
     escaped its transaction (a missing boundary is a fault) — makes the
     declaration *invalid* (internal fault, diagnostic 29) and spends the
     context, which is replaced (ADR 0012, G-P6 and Amendment 1);
   - a **resource owner**: a word that holds a file, a heap buffer or a
     busy mark across a call that can throw, and catches only to release
     or restore it and throw the same code on (`export-caught`,
     `busy-call`, `ir-read-open`, `ir-emit`), or to free and give an ior
     (`context-fill`, `task-new`);
   - a **top level**: a tool's or the future command line's outermost
     word (`count-read`), which turns any code into a failure outcome or a
     nonzero exit status.

4. **Rollback.** Inside a check, a transaction boundary rolls back with
   store marks (`store-mark`, `store-rollback`, `src/lib/store.fs`), never
   by saving and restoring counts by hand. A mark is taken before anything
   can throw: a mark left over from an earlier call would roll back
   records other work allocated since, and `store-rollback` cannot always
   tell. A mark of an invalid store is refused, and nothing was allocated
   in such a store. A rollback refused for a mark that was taken
   successfully is a fault (`throw-fault`), because the store can no
   longer be shown to be back. At a check boundary, `lf-env-step` already
   rolls the scratch back to the input marks whatever the outcome; a code
   reaching it also spends the context, because records outside stores
   (frames still busy, walk stacks) may be inconsistent. Shared state is
   never written inside a check (ADR 0012, G-P1), so no `THROW` in a check
   can reach a slot; the publisher is its own transaction boundary
   (`lf-env-guarded`), and it marks the slot final last.

5. **A failure is never accepted.** The word that maps codes to outcomes
   gives *ok* only for 0 (nothing thrown) and never for a code; every
   unknown code is thrown on or, at a check boundary, becomes *invalid*.
   A declaration whose check threw is never published as accepted, and no
   caught code is stored or cached as success. Tests for every adopting
   module reach each mapped outcome and plant a mapping that would give
   *ok*, which they must catch.

6. **Resources.** Only resource owners and boundaries hold heap buffers
   or files across a call that can throw, and they release them on every
   path. Context members hold no `ALLOCATE`d memory (rule in
   [the library notes](../development/FORTH_LIBRARY.md#design-per-task-contexts-and-how-modules-convert)),
   so freeing a spent context frees all of a check's state. Failure
   injection (plan task 1.4.6) throws at every allocation site of an
   adopting module and checks that the stores and digests are unchanged.

7. **A host prerequisite: one backtrace string per worker.** Gforth 1.0's
   `THROW` records a backtrace in a heap string reached through the
   `USER` variable `stored-backtrace` (`backtrac.fs`), and a new thread
   copies its creator's user area, pointer included; `thread-init` does
   not reset it. When the main task has thrown before the job pool starts
   and jobs then throw, the workers resize and free the main task's
   string. Measured with the unchanged pool and plain `CATCH`/`THROW`: 12
   jobs of 2,000 caught throws each after 2,000 in the main task crash
   with heap corruption in 5 of 5 runs; giving each worker its own (zero)
   pointer when it starts makes 5 of 5 runs pass, and with that change the
   pilot below passes `tests/core/contexts.fs` (which crashed without it).
   Today's tests throw in only a few jobs and have not crashed, but the
   sharing is there. `src/lib/task.fs` must get this fix (one word called
   in `worker-start`, Gforth 1.0 only) before any module that throws runs
   in jobs.

8. **Adoption.** Opt-in per module, when the module is next refactored,
   allocation-heavy passes first (level substitution, the rebuild
   passes), with the randomized old-against-new differential that every
   refactor uses. Library support goes into `src/lib/outcome.fs` (or a
   small `src/lib/fail.fs` beside it): the code constants, `fail-invalid`
   and `fail-full`, `?fail ( outcome -- )` and `code>outcome ( code --
   outcome )`. Callers' stack effects do not change, so tests and the
   pinned-Lean tables do not change. Moving a boundary up (one boundary
   for several modules) is a later, separate decision per call path.

## The pilot: `mixed-level-substitute.fs`

Option (b) was applied to `src/kernel/mixed-level-substitute.fs` in a
scratch copy of `16bdc2f`, with `lf-mixed-level-substitute` as the
transaction boundary over the term, level and reference stores, and the
library words above in a new `src/lib/fail.fs`. The audit's walk visitors
were left on outcomes (decision 1). The boundary:

```forth
: lf-mls-caught ( 6*x code -- status ) lf-mls-rollback code>outcome >r 2drop 2drop 2drop r> ;
: lf-mixed-level-substitute
  ( index id formals actual-pairs count fuel -- index id 0 | status )
  lf-mls-snapshot ['] lf-mls-body catch ?dup if lf-mls-caught else outcome-ok then ;
```

and a typical pass word, before and after:

```forth
: lf-mls-sort ( node level -- index outcome )
  dup lf-mls-level ok-then? 0= if lf-mls-failed exit then
  tuck = if drop outcome-ok else nip lf-mls-new-sort then ;

: lf-mls-sort ( node level -- index )
  dup lf-mls-level tuck = if drop else nip lf-mls-new-sort then ;
```

| Measure (code lines, comments excluded) | Before | After |
| --- | --- | --- |
| Code lines / tokens | 151 / 835 | 129 / 714 |
| Colon definitions | 58 | 57 |
| Words that give an outcome | 33 | 10 |
| Status plumbing (`ok?`, `ok-then?`, `outcome-*`, `flag>outcome`) | 45 | 6 |
| Exception words (`?fail`, `fail-*`, `CATCH`, `code>outcome`) | 0 | 18 |
| `IF … EXIT THEN` failure exits | 14 | 6 |
| Words of one or two lines | 62% | 80% |
| Hand-written count saving and restoring | 3 stores | none (3 store marks) |

`lf-mls-failed` went away, and `lf-mls-apply`, `lf-mls-run` and
`lf-mls-build-node` folded into their callers. The pilot drops the
outcome of each `store-rollback`: its only refusals are marks of stores
that were already invalid when the call began, where nothing can have
been allocated; decision 4's fault for any other refusal is not yet in
it. The library cost is `fail.fs`: 4 constants and 5 words, 15 code
lines. For scale, `core/` and `kernel/` hold 1,004 colon definitions, 389
of which give an outcome, with 379 plumbing tokens and 176 failure exits;
this module is allocation-heavy, and modules made mostly of walk visitors
would gain less.

Evidence, all on the scratch copy:

- every target of `make test` except the two that need a git checkout
  (`check-docs`, `check-lean-sources`) passes on Gforth 1.0 and 0.7.3,
  with the job-pool fix of decision 7, and the five pinned-Lean
  comparisons that use level substitution agree (27, 48, 27, 4 and 8
  observations);
- a randomized differential against the unchanged code (the earlier
  `ops2` harness: every `lf-mixed-*` pass on random and corrupted stores,
  plus a substitution after a quarter of the operations; 400 seeds of
  3,000 operations, 1.54 million output lines, 330,308 substitutions:
  323,173 invalid, 3,944 exhausted, 6 full, 3,185 ok) gives byte-identical
  output, every module's fuel and the full store state included;
- a planted fault, the boundary without its rollback, changes 3,974 lines
  of that output and fails the module's unit test (`fuel-sweep`);
- time (Gforth 1.0, 100,000 calls, three runs each): successful calls
  2,877–3,049 ms before and 2,807–2,990 ms after; calls that run out of
  fuel 1,078–1,128 ms before and 1,135–1,198 ms after, about 6% more,
  the cost of one `THROW`.

## Rejected alternatives

- **(a) Outcomes everywhere, as today.** Explicit, but in the pilot module
  more than half the words exist partly to pass failures up, and a
  hand-written rollback in every failing branch is where a mistake would
  leave a store half-built. Kept as the interface rule.
- **(c) `THROW` for every outcome that is not ok.** Callers branch on
  *rejected*, *unknown* and *unsupported* (K5's "unknown first", the
  checker's own decisions); throwing them would hide the owner's three
  outcomes in control flow and need a `CATCH` at every branching caller.
- **Throwing outcome numbers** (`outcome throw`). `0 throw` does nothing,
  small positive codes can collide with host iors, and a stray `1 throw`
  from any library would read as *invalid*.
- **Gforth's `exception` word for the codes.** Its numbers depend on the
  host and on load order (−2051 on 0.7.3, −2077 on 1.0) and lie in the
  system's range.
- **Catching at every module boundary, host errors included.** An inner
  boundary that swallows a host error (a bad address, a stack overflow)
  would go on in a context whose records may be busy or half-written;
  such codes must reach the check boundary, which spends the context.
- **Converting every module now.** Most of `core/` is walk visitors, which
  keep outcomes; a module-by-module adoption keeps each change small and
  checkable against the code it replaces.

## What the owner must decide

1. **Adopt the rule** — exceptional failures (invalid, out of fuel, out of
   room) may be thrown inside one operation and are always turned back
   into the usual outcome at its entry; accepted, rejected and
   unsupported/unknown are never thrown. *Recommendation: yes.* In the
   pilot it removed most of the failure-passing code (outcomes in 10
   words instead of 33) and replaced hand-written rollback with store
   marks, with identical results on 330,308 random calls and one more
   `THROW`'s cost only on failure.
2. **Fix the job pool first** — give each Gforth 1.0 worker its own
   exception-backtrace string. *Recommendation: yes, now and on its own.*
   It is a latent crash in today's pool (shown reproducibly), small and
   independent of this rule.
3. **Pace of adoption** — module by module when each is next refactored,
   allocation-heavy passes first, rather than all at once.
   *Recommendation: module by module*, each with the usual randomized
   comparison against the code it replaces.

## Reproduction

Gforth 1.0.0 and 0.7.3 (the CI hosts), 2026-11-02. The host codes came
from small probes that `CATCH` each failure (`ALLOCATE` of half the
address space, `OPEN-FILE` of a missing file, `READ-FILE` of a directory,
`@` of address 0, stack underflow and overflow, `ABORT`, `ABORT"`, an
undefined word, `exception`). The backtrace crash: load `src/lib/task.fs`,
run 2,000 caught throws in the main task, then submit 12 jobs that each
run 2,000 caught throws; the fix sets `stored-backtrace` to 0 in
`worker-start` after `thread-init`. The pilot's metrics count code tokens
with comments removed; `python3 scripts/forth-metrics.py` gives the word
lengths.

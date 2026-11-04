# The derivation log

The **derivation log** is an optional notebook in which LeanForth's checker
writes one numbered record for each rule it applies while it checks a
declaration: which rule, what it was applied to, what came out, how many
binders deep, and which earlier records it used. Nothing in the checker
ever reads it. The [proof outline](../user/PROOF_OUTLINE.md) is printed
from it. This page is the programming reference: the record format, the
rule catalogue, the Forth interface, and the evidence that the log changes
no answer.

**Status.** Implemented (plan task 2.4.1, [ADR 0013](../adr/0013-derivation-log.md),
accepted by the owner with decisions D1–D5). The log is called from the
checker's own words, so it is [kernel] code with the *no-behaviour-change*
review of ADR 0013 (D5): until that review is complete it is experimental,
like the checker itself. The log is not a certificate: nothing decides
acceptance by reading it.

**Owner decisions (ADR 0013).** D1: off unless asked for. D2: when it runs
out of room it stops, says "log incomplete at step N", the verdict stands,
and no outline is printed from it. D3: it keeps copies of the intermediate
formulas (level `terms`); level `steps` keeps records without formulas.
D4: the outline is short by default, every step with `--detail`. D5: the
checker's usual gate, with "nothing changed" as the evidence.

## Where it lives

| File | What |
| --- | --- |
| [`src/core/derivation-log.fs`](../../src/core/derivation-log.fs) | the log: options, per-context state, the open and close protocol, the copier, the rule catalogue |
| `src/kernel/*.fs` | one guarded call per site (below): `lf-log? if` logged path `else` plain path `then`, both running the same kernel word |
| [`src/present/log-view.fs`](../../src/present/log-view.fs) | reading a log for printing: formulas in each step's scope, the step list |
| [`src/present/log-check.fs`](../../src/present/log-check.fs) | the structural check of a log (`lf-log-flaw`): the printer prints nothing from a log that fails it, and the tests check every log they make with it |
| [`src/present/proof-outline.fs`](../../src/present/proof-outline.fs) | the proof outline (plan task 2.4.4) |
| [`src/cli/print.fs`](../../src/cli/print.fs) | `bin/leanforth print` ([command line](../user/COMMAND_LINE.md#printing-a-readable-proof)) and `make print`: binder names from the export, each declaration checked with the log on and printed right after its check, and when no outline may be printed |
| [`tests/support/print-outline.fs`](../../tests/support/print-outline.fs) | the same words for tests and the user page, without the command line's manifest check and exit codes |
| [`tests/support/gforth-log.sh`](../../tests/support/gforth-log.sh) | run any test with the log on, or on and full (the test preset) |

## Records

Step *s* is record *s*, counting from 1. A rule *opens* before its work and
*closes* after it; its record is written when it closes, after the records
of everything it used (post-order). Each record is seven cells:

| Field | Contents |
| --- | --- |
| `logrec-rule` | the rule's code (catalogue below) |
| `logrec-outcome` | the rule's outcome ([ADR 0008](../adr/0008-outcome-vocabulary.md)): ok, or the failure it ended with |
| `logrec-start` | how many records existed when the rule opened: its sub-derivation is steps `start+1` … `s−1` |
| `logrec-depth` | how many binders surround its subject (an inference step: the binder context's depth; any other step: the innermost open rule's) |
| `logrec-a`, `logrec-b` | its inputs, references of the kinds the catalogue gives |
| `logrec-out` | its result when the outcome is ok, else none |

**Premises from `start` alone.** A step's premises are the top-level records
of its sub-derivation: the record just before it (`s−1`), then the record
just before that premise's own sub-derivation (its `start`), and so on
while the step is above the rule's `start` (`lf-log-premise`). For
`composition`, application step s36 opened when 31 records existed; its
premises are s35 (start 34), s34 (start 33), s33 (start 32) and s32 (start
31, which ends the chain): the instantiation, the comparison, the
argument's type and the function's type. A step that failed may have more: the
steps of its failure's analysis (for a rejected application, the
inference steps the rejection's diagnosis ran) appear among its premises
too, since they were written while the rule was open.

**References.** A term or level reference `n ≥ 0` is input object `n`, an
index below the input marks of [`src/core/input.fs`](../../src/core/input.fs),
which never change during a check; `−1 − k` is copy `k` in the log's own
pool; `lf-log-none` (the most negative cell) is no object, and
`lf-log-unkept` (one more) a scratch object at level `steps`, which keeps
no copies. A *number* is stored as it is: a name ID, a slot, a count.

**Copies.** At level `terms` every scratch term or level a record mentions
is copied into the log's pools when the record is written, after its
identity is checked against the one recorded when the rule opened. A copy
is a node (`tag first second`, as in the term and level stores) whose
children are input objects or earlier copies, so input subterms are
shared and each copy refers only backwards. A copy is made in a
*context*, the number of binders around the node: the record's depth for
its inputs and result, one more for the body of an `instantiate` or
`beta` step, `amount` fewer for the term of a `shift` (as the step list
below reads them), and one more under each lambda or Π binder within the
copied term. A free variable of the local context (plan task 4.2.2a;
[`src/core/local-context.fs`](../../src/core/local-context.fs)) is copied
as the bound variable it stands for there: `c − 1 − d` in context `c`,
for the depth `d` at which inference opened its binder (recorded in its
entry), so a copy, like an input object, holds bound variables only; a
free variable not live, or opened outside its context, is unreadable. A
memo (1,024 entries per store, direct-mapped by index and checked by
identity and context) copies a live scratch node once per context; a
collision only costs a second copy. Symbolic Sorts
refer to level references. A constant keeps its reference when that lies
below the input marks; any other reference is copied too
(`lf-log-cref-slot`: its name, name generation, number of universe
arguments, and where their level references start in the argument pool,
`lf-log-arg-ref`), however many arguments it has.

The copier walks a node post-order with two stacks of its own (tasks and
values, 512 cells each), so it never recurses and does not depend on the
term and level stores' capacities, which are per-context settings of the
heap stores (ADR 0016). One copy may run 4,096 tasks.

**Truncation.** The first bound reached wins: no room for a record, for an
open rule, in the term, level or reference pools, a formula that needs
more stack or work than one copy may use (`lf-bound-work`), a node the
copier cannot read (not live, or not the node the rule opened with; a
child index below 0 counts as one), a check that ended with rules still
open (`lf-bound-interrupted`: a THROW in the check, ADR 0013 L6's
*interrupted* state), or no memory for the pools when the log started
(`lf-bound-memory`). The log then records the step it could not write and
the bound (`lf-log-cut ( -- step bound )`), stops recording, and is a
consistent prefix: steps 1 … N−1 complete, nothing after. The check goes
on exactly as before. An interrupted log has no publish step.

**Memory** (measured on Gforth 1.0 and 0.7.3, 64-bit, 2026-11-03). The
log's state in each context is a 224-byte header. Its pools — records,
open rules, the term, level and reference copies, the copier's memos and
stacks — are one heap block of 223,264 bytes, allocated when a log starts
in a context that has none and freed when a check begins with the log off
(`lf-log-stop`) and by the context's teardown. So a context with the log
off pays 224 bytes, and one with the log on about 218 KiB more, once. The
printers' state is heap-held only while an outline prints (39,480 bytes
for `log-view.fs`, 25,144 for `proof-outline.fs`; a THROW while printing
leaves them held until the next outline, which zeroes and reuses them, or
the context's teardown). The log's own share of every context is
therefore 224 bytes, plus 40 for the printers (the input's name and line,
two pointer cells) and 528 for `print.fs`'s line table; the context as a
whole is larger and grows with other modules. At the first review the
log's share was 288,088 bytes. The ADR's estimate approved in D3 ("about
150 KB per worker while it is on") is low: the measured cost while on is
218 KiB.

**Heap with the log on and off.** Since the pools exist only while the
log is on, a run with the log on uses about 218 KiB more heap per context
than one with it off. On a host where that much memory decides whether a
heap store can grow, a check could end *full* with the log on and *ok*
with it off; nowhere else can the two differ. (Allocating the pools for
every context, log on or off, would remove the difference and cost every
context the 218 KiB again.)

**Header.** Besides the counts and limits, the header keeps the input's
fingerprint when the log started (`lf-log-input`), and the slot and
outcome the check published (`lf-log-published ( -- slot outcome )`, slot
−1 until a check publishes; `lf-log-start`, which starts a log of no
check, sets it back to −1), also when the log is off or truncated. The
outline printer compares them with the verdict it is given.

**Inductive blocks.** The check of an inductive block (ADR 0015, plan
task 5.2.1a; `lf-check-block`) is one `inductive-block` step (44) at its
first member's slot, closed with the block's outcome; the publish step
follows it, so a block's log passes the structural check like a
declaration's. The steps inside it are those its logged sites write
(inference of the types, universe instantiation); positivity, the
universe rules, the recursor's construction and the B3 comparison are not
yet steps of their own. That is enough for the log's guarantees (a
consistent, nested prefix that changes no answer); detailed block steps
come with the block's own outline templates.

## Rule catalogue

Stable codes, like the diagnostic codes. Kinds: `term` and `level` are
references, `number` a plain cell, `none` unused.
`tests/core/check_log_catalogue.py` (part of `make test`) keeps this table
equal to the code's.

| Code | Rule | a | b | out | Written by | Premises |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `sort` | term | none | term | inference of a Sort | the universe-parameter checks of its level |
| 2 | `variable` | term | none | term | inference of a variable: its type is its local-context entry's (plan task 4.2.2a; before, the `shift` of its binder's domain was a premise) | — |
| 3 | `constant` | term | none | term | inference of a constant | `resolve`, `universe-arity`, `universe-parameter`, `instantiate-levels` |
| 4 | `application` | term | none | term | inference of an application | function's type, argument's type, `defeq`, `instantiate` |
| 5 | `lambda` | term | none | term | inference of a λ: its type, a Π | the domain's type, the body's type |
| 6 | `pi` | term | none | term | inference of a Π: its Sort | the domain's type, the body's type |
| 7 | `form` | term | none | term | inference of a node inference does not handle | — |
| 10 | `whnf` | term | none | term | a reduction that changed the term (one that changed nothing writes no record) | its `beta` steps |
| 11 | `beta` | term | term | term | one contraction: λ body, argument, contractum | its `instantiate` |
| 12 | `defeq` | term | term | none | a comparison of two terms | its `whnf` and `level-eq` steps |
| 13 | `level-eq` | level | level | none | a comparison of two levels | — |
| 20 | `instantiate` | term | term | term | putting an argument for a bound variable | — |
| 21 | `shift` | term | number | term | shifting a term's free variables by an amount | — |
| 22 | `instantiate-levels` | term | number | term | a constant's type at its universe arguments (b: their number) | — |
| 30 | `resolve` | number | none | number | finding a constant's name (a) in the environment: its slot | — |
| 31 | `fresh-name` | number | none | none | N2 for declaration a | — |
| 32 | `universe-arity` | number | number | none | L1: a universe arguments for slot b | — |
| 33 | `universe-parameter` | number | none | none | L2: name a is a parameter of the declaration | — |
| 34 | `distinct-parameters` | number | none | none | L3 for declaration a | — |
| 40 | `proposition` | term | none | level | a theorem's statement is a proposition (S1, S3): its Sort's level | the statement's type |
| 41 | `declaration` | term | term | none | the whole check of a declaration (type, value) | name and parameter rules, type formation, the value's type, `defeq` |
| 42 | `publish` | number | number | none | the published outcome: slot a with b dependencies | the `declaration` or `inductive-block` |
| 43 | `type` | term | none | level | a definition's declared type is a type (S1) | the type's type |
| 44 | `inductive-block` | number | none | none | the whole check of an inductive block (ADR 0015), at the slot a of its first member; its inner steps are not yet logged in detail | the steps its logged sites wrote (inference, universe instantiation) |

**Room to grow.** Codes 10–19 are conversion and reduction. Phase 4
(definitional equality with unfolding) adds, in this range, `unfold` (14:
a named constant replaced by its value, Lean's δ), `eta` (15),
`proof-irrelevance` (16) and `let` (17, ζ), each a premise of the `whnf` or
`defeq` that used it, with the same record shape: `unfold` takes the
constant (a) and gives its value at the levels used (out), with the
`resolve` and `instantiate-levels` it needed as premises. Recursor rules,
literals, projections and quotients get codes when the checker has them.

Not logged, because they are not rules of the derivation: the audits and
preflights, the shift inside an instantiation, level evaluation inside a
comparison, the environment's scans and the publisher's re-check. Their
failures stay explained by the [diagnostic](DIAGNOSTICS.md).

## Where each rule records

| Rule | Site |
| --- | --- |
| `sort` … `form` | `lf-minfer-in-frame` in [`src/kernel/mixed-infer.fs`](../../src/kernel/mixed-infer.fs), after its fuel and frame check |
| `whnf` | `lf-mixed-beta` in [`mixed-beta.fs`](../../src/kernel/mixed-beta.fs) |
| `beta` | `lf-mbeta-step`, around the instantiation of each contraction |
| `defeq` | `lf-mconvert-checked` in [`mixed-convert.fs`](../../src/kernel/mixed-convert.fs) |
| `level-eq` | `lf-level-compare-run` in [`level-compare.fs`](../../src/kernel/level-compare.fs) |
| `instantiate` | `lf-mixed-instantiate` in [`mixed-instantiate.fs`](../../src/kernel/mixed-instantiate.fs) |
| `shift` | `lf-mixed-shift` in [`mixed-shift.fs`](../../src/kernel/mixed-shift.fs) |
| `instantiate-levels` | `lf-mixed-level-substitute` in [`mixed-level-substitute.fs`](../../src/kernel/mixed-level-substitute.fs) |
| `resolve`, `fresh-name`, `universe-arity`, `universe-parameter`, `distinct-parameters` | `lf-env-lookup`, `lf-env-own-name`, `lf-env-arity?`, `lf-env-param?`, `lf-env-own-params` in [`environment.fs`](../../src/kernel/environment.fs) |
| `proposition`, `type`, `declaration` | `lf-check-type` (opens), `lf-check-prop` (closes), `lf-check-run` in [`check-declaration.fs`](../../src/kernel/check-declaration.fs) |
| `inductive-block` | `lf-check-block` in `check-declaration.fs`, around check-block.fs's `lf-block-check`: one step for the whole block check, closed with its outcome (positivity, universes, the recursor and the B3 comparison are not yet steps of their own) |
| `publish` | `lf-env-step` in [`env-publish.fs`](../../src/kernel/env-publish.fs), after the hand-over |
| (begin) | `lf-env-begin` in `environment.fs` |

## Forth interface

Options, shared and read-only during a run (set outside jobs; inside one
these words do nothing):

| Word | Stack effect | Does |
| --- | --- | --- |
| `lf-log-set` | `( level -- )` | the level of every later check: `lf-log-off` (0), `lf-log-steps` (1), `lf-log-terms` (2) |
| `lf-log-limits` | `( records marks terms levels -- )` | limits for records, open rules, term and level copies, each clamped to its capacity |
| `lf-log-capacities` | `( -- records marks terms levels )` | the capacities: 1,024; 256; 2,048; 512 |

Per context (the current one):

| Word | Stack effect | Does |
| --- | --- | --- |
| `lf-log?` | `( -- flag )` | nonzero while this context's log records (the kernel's only test) |
| `lf-log-start`, `lf-log-stop` | `( level -- )`, `( -- )` | start a log for work outside the checked environment; stop and clear it |
| `lf-log-count`, `lf-log-level`, `lf-log-decl` | `( -- n )` | records, level, the declaration a check's log is of |
| `lf-log-cut`, `lf-log-complete?` | `( -- step bound )`, `( -- flag )` | the step that could not be written and its bound (`lf-bound-records`, `-marks`, `-terms`, `-levels`, `-unreadable`, `-work`, `-refs`, `-interrupted`, `-memory`), 0 0 while complete |
| `lf-log-input`, `lf-log-published` | `( -- h )`, `( -- slot outcome )` | the input's fingerprint when the log started; the slot and outcome the check published (−1 before) |
| `lf-log-record` | `( step -- rec )` | record of a step (unchecked), fields `logrec-*` |
| `lf-log-premise` | `( p -- p' )` | the next premise (see *Premises*) |
| `lf-log-term-copies`, `lf-log-term-slot` | `( -- n )`, `( k -- addr )` | the term pool: copy `k`'s node (`node@` gives `tag first second`) |
| `lf-log-level-copies`, `lf-log-level-slot` | same | the level pool |
| `lf-log-copy?`, `lf-log-copy-index` | `( ref -- flag )`, `( ref -- k )` | whether a reference is a copy, and which |
| `lf-log-rule-name`, `lf-log-kind` | `( code -- c-addr u )`, `( rule shift -- kind )` | the catalogue: name, and the kind of a (shift 0), b (2) or out (4) |
| `lf-log-written`, `lf-log-restarts` | `( -- n )` | statistics: records written in this context, preset logs restarted |

The kernel's protocol (only `src/kernel/` calls these, always after
`lf-log?` was true, and each returns its arguments unchanged):
`lf-log-open ( a b rule -- )`, `lf-log-infer ( node depth -- node )`,
`lf-log-close ( result outcome -- result outcome )`, `lf-log-decided`,
`lf-log-close-handle`, `lf-log-close-maybe`, `lf-log-close-whnf`,
`lf-log-close-all`, and, unconditionally, `lf-log-begin ( i -- )` at the
start of a check and `lf-log-publish ( slot deps outcome -- )` after its
hand-over.

The printers and the structural check read the log only through value
words: `lf-log-rule@`, `lf-log-outcome@`, `lf-log-depth@`, `lf-log-a@`,
`lf-log-b@`, `lf-log-out@` and `lf-log-premise ( s -- x )` for a record's
fields, `lf-log-term-node@` and `lf-log-level-node@ ( k -- tag first
second )` for a copy, `lf-log-cref@ ( k -- name generation count args )`
and `lf-log-arg-ref` for a copied constant reference; no word they may use
gives an address of the log's records, pools or header.

**The isolation check.** `tests/core/check_log_isolation.py` (in `make
test`) checks allow-lists on the source text. Comments, strings and the
exact load-time assertion `[if] .( … ) cr abort [then]` are removed;
every other token is checked, also inside `[if] … [then]` and after `'`
or `[']`. A kernel file may name only the protocol above and the rule
codes, and loads nothing from `src/present/` or `src/cli/`. A printer
(`src/present/`) may name only the log's reading words (all of which give
values), loads only from `./`, `../lib/` and `../core/`, and uses no word
that looks a name up or runs text (`EVALUATE`, `FIND` and the like). The
command line (`src/cli/`, which turns the log on for `leanforth print`)
may name only the switches `lf-log-set`, `lf-log-limits`,
`lf-log-capacities`, the levels and the read-only `lf-log-level` and
`lf-log-complete?`; any other source file no log word. No file outside the
log module may store into a field of a record, mark, copied reference,
the header, the pools or the options. The log module may name only its
own words, standard Forth words, the context words and the stores'
value-giving read accessors (`lf-term-read`, `lf-term-identity`,
`lf-level-read`, `lf-level-identity`, `lf-cref-read`, `lf-cref-level`,
`lf-input-mark-count`, `lf-input-intact?`, `lf-input-fingerprint`): no
diagnostic, printing, store allocation or rollback, walk, fuel or
name-lookup word, and no address of another module's state. It loads only
from `./` and `../lib/`. `ALLOCATE` appears only in the word that makes
its pools, `FREE` only in the one that gives them back, `THROW` only in
its context teardown, `ABORT"` only in the catalogue's load-time index,
`ALLOT`, `HERE`, `,` and `ALIGN` only at load time, and `CREATE` and
`CONSTANT` only at top level. The ten evasions planted by the second
review are flagged (planted faults `iso-*` in `make mutants`).

What it cannot see: an address computed by arithmetic from an allowed
one (the log module's own state plus an offset); an execution token
taken elsewhere and passed in; and what the words it allows do in turn
(their list is reviewed by hand). It does not check the compiled code's
word references: Gforth's threaded code has no portable reader, and 0.7.3
and 1.0 differ. The behavioural tests are the evidence for those.

**Lifetime.** `lf-env-begin` starts a fresh log for the check at the
options' level, or, when that is off, frees the pools and clears it.
After the hand-over the published slot and outcome go into the header,
the publish step is written (unless the check ended with rules open) and
the log stops recording; it stays readable until the next check begins
in that context, which is when the proof outline is printed. The
kernel's two reads of `lf-log?` around the formation step (steps 4–6 of
a check) agree because a check's log never restarts while it runs; a
log truncated between them leaves the formation step counted as open,
and `lf-log-close-all` closes it.

**Stack use.** ADR 0013 L5 item 5 asked for the stack needs to be
measured again with the log on. Stack painting of `infer-deep`'s deepest
case (25 applications, a 59-level normalisation; the review of
2026-11-03): 597 return and 222 data cells before the log; 599 and 222
with it off; 601 and 222 at level `terms` or `steps` (158 records); 599
and 222 truncated by three term copies; the fuel the same in every run.
The stated need is 1,728 return and 1,280 data cells. The printers' own
walks over a formula (rebuilding copies, naming them, looking for a bound
variable) nest at most 128 deep, about 4 return cells a level, well
inside Gforth 0.7.3's 1,920 return cells (1.0: 3,968) and above the 64
levels any check reaches; deeper, the formula prints as `?`
(`tests/core/derivation-log.fs` rebuilds a 120-deep copy and refuses a
450-deep one on both hosts; at the earlier limit of 512, 451 levels
overflowed 0.7.3's return stack).

**Test preset.** A word `lf-log-preset-level` defined before
`src/core/derivation-log.fs` loads (`gforth -e "2 constant lf-log-preset-level" …`)
sets that level and makes every context log every checker call, restarting
a truncated log when its outermost rule ends; `lf-log-preset-records`,
`-marks`, `-terms` and `-levels` set the limits. `tests/support/gforth-log.sh`
defines them from `LF_LOG_LEVEL`, `LF_LOG_RECORDS`, `LF_LOG_MARKS`,
`LF_LOG_TERMS` and `LF_LOG_LEVELS`, so any test runs with the log on or
full:

```text
LF_GFORTH=$PWD/.tools/gforth/bin/gforth LF_LOG_LEVEL=2 LF_LOG_RECORDS=5 \
  make test GFORTH=tests/support/gforth-log.sh
```

## The step list (`--detail`)

Each step is one line: its number, rule, depth, the formulas it relates
(printed by the term printer in the scope of the binders around it: an
inference step as `subject : type`, a reduction `term ⟶ reduct`, an
instantiation or contraction as the redex `(fun x ↦ body) argument ⟶
result`, a shift `term shifted by n ⟶ result` in the scope the term came
from, a comparison `left ≡ right`), the premises after `←`, and the outcome
in brackets unless ok. For `composition`:

```text
  s35    instantiate         depth 6   (fun x ↦ B) value ⟶ B
  s36    application         depth 6   f value : B  ← s32, s33, s34, s35
```

The complete list is in [`tests/present/outlines.golden`](../../tests/present/outlines.golden),
which `make test` compares byte for byte.

## Evidence that nothing changed

All run with Gforth 1.0 on 2026-11-03 (branch of agent RB); the unit tests
also on Gforth 0.7.3.

- `tests/core/derivation-log.fs` (`make test`): off by default, in new
  contexts too; composition's log is 51 steps with the ADR's rules, depths
  and premises (65 before plan task 4.2.2a: its 14 `shift` steps, each a
  variable step's premise, are gone); the nine fixture and broken exports give the same
  published outcomes, check steps, diagnostics (code and numbers) and fuel
  with the log off, at level steps and at level terms, and with the log
  full at every record limit from 0 to 139, every open-rule limit from 0
  to 23, every term-copy limit from 0 to 39 and every level-copy limit
  from 0 to 11 (2,272 truncated logs), every log passing the structural
  check of `src/present/log-check.fs` (numbering, nesting, references,
  copies, the prefix, a publish step whose premise is the declaration or
  inductive-block step, and each ok step's premise kinds, a step's later
  parts checked only when its earlier ones passed and premises followed
  only while strictly earlier, so a damaged start fails part 2 at once
  instead of looping: an application at least two
  inference premises, one defeq and one instantiate; a lambda and a Pi
  two inference premises; a variable only shifts; a Sort only
  universe-parameter steps; a proposition or type step one inference
  premise; a declaration one fresh-name, one formation and one defeq step.
  A failed step is not checked this way: its premises include the steps
  of its failure's analysis); an unreadable input; a check that throws
  with rules open (its log truncated as interrupted, not complete); a
  validator that refuses a publish step after another step and an ok
  declaration step without its premises; a damaged start (part 2, no
  loop); a test log that forgets the last check's slot; a 120-deep copy
  rebuilt and a 450-deep one refused by the printer on both hosts; and
  nine inductive-block exports (Bool, Nat, Eq, And, Or, Exists, a mutual
  block, two rejected blocks) with the same outcomes with the log off and
  on, every log valid and every block's publish step after its
  inductive-block step.
- `tests/core/log-trials.fs` (`make test`): the checker trials of
  `tests/support/checker-trial.fs`, 8 seeds of 1,000 random steps
  (inference, conversion, comparison, beta, shift, instantiation, the level
  passes, universe substitution, the signature index, the definition probe
  and the pinned fixtures), each with the log off, at levels terms and
  steps, at three sets of random limits, and interleaved step by step with
  one context logging and one not: every digest of outcomes, results, fuel,
  store counts and serials, and diagnostics equals the log-off digest
  (about 100,000 checker calls; 84,920 records written; 18,510 logs
  truncated and restarted). On the heap stores of ADR 0016 step 3, also a
  copied constant reference rebuilt for printing, and chains of 200
  applications (copied whole, 201 copies) and 300 (too large to copy: the
  log truncated, the answer unchanged) in a store of 1,000 terms.
- The whole of `make test` with the log on (`LF_LOG_LEVEL=2`), full after 5
  records, and with 2 term copies, 1 level copy and 3 open rules; and the
  pinned-Lean differentials of `make test-differential` with the log on and
  full: every test passes unchanged (`make check-log-identity`).
- Planted faults in `make mutants` (`tests/mutants/faults.toml`, ids
  `log-*`): a logged path that changes a comparison's verdict, a truncated
  log that changes an outcome, a step saved one step late (a premise
  pointing at a missing step), a log that keeps recording after a bound,
  an outline printed from a truncated log, a printer that trusts the
  caller's verdict, a thrown check's log reported complete, a validator
  that accepts any publish premise, the log module rolling the stores
  back or allocating outside its pools word, a printer storing into a
  record, and `print` leaving the log on after a THROW; each is caught.
- The outline printer refuses a log the verdict does not belong to (M1
  of the review of 2026-11-03): two golden sections in
  `tests/present/outlines.golden` (a rejected declaration's log given as
  accepted; composition's log after identity's input is loaded).

**Cost.** Off, the checker pays one fetch and branch per logged site. On
the workload of checking the five pinned exports 2,000 times each
(`gforth-fast` 1.0, seven interleaved runs against `main` at `6aabd81`):
median 833 ms on `main`, 828 ms on this branch with the log off (paired
median difference −2 ms: within the noise); with the log on, about 1.9
times as long at level terms and 1.5 times at level steps.

## Not yet

- ADR 0013 L2's header copy is partial: `lf-log-publish` keeps the
  published slot and outcome, not the diagnostic (the printers read it from
  the context, as the checker left it).
- The NDJSON writer of ADR 0013 L6 and the observer called after each
  declaration (a parallel run needs it); the outline is printed from the
  in-memory log, between checks, by the caller.
- The parallel scheduler's hand-over (`lf-env-hand-over-job`) writes no
  publish step; phase 2 runs serially.
- The log's own capacities are constants; settings like the stores' (plan
  task 3.3.1) come when a large proof needs them.
- The checker reads the heap stores of ADR 0016 step 3; when it moves onto
  the compact store's expression records, the copier's read words change
  with it (its walk does not).

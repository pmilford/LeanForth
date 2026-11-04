# ADR 0013: the derivation log and the proof outline

Status: **accepted** by the owner on 2026-11-03, with D1–D5 as recommended
([OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md#gate-answers-and-working-guidelines-2026-11-03)).
Previously: **proposed**, 2026-11-02 (plan tasks 2.4.1 and 2.4.4; design only,
nothing here is implemented). The log is called from the checker's own
words, so it is a [kernel] change with the *no-behaviour-change* review the
plan gives task 2.4.1: it passes the review gate in `AGENTS.md` only with
the evidence below and the owner's approval of the plain summary. The
proof-outline printer (2.4.4) is untrusted presentation code with no gate
of its own. Builds on [ADR 0008](0008-outcome-vocabulary.md) (outcomes),
[ADR 0009](0009-reentrant-state-and-parallel-checking.md) (one context per
worker) and [ADR 0012](0012-checked-environment.md) (whose E1 and E7
already place "the derivation log" in the check's context), and reuses the
patterns of the [diagnostics](../programming/DIAGNOSTICS.md).

## Implementation (2026-11-03)

Implemented on a branch of agent RB (plan tasks 2.4.1 and 2.4.4): the log
in `src/core/derivation-log.fs`, one guarded call per kernel site, the
proof outline in `src/present/proof-outline.fs` and `log-view.fs`,
`make print`, and since then `bin/leanforth print`
([command line](../user/COMMAND_LINE.md#printing-a-readable-proof),
`src/cli/print.fs`); reference in
[DERIVATION_LOG.md](../programming/DERIVATION_LOG.md), user page in
[PROOF_OUTLINE.md](../user/PROOF_OUTLINE.md). The gate's evidence (D5) is
listed there; the owner's approval of the summary is still to come. Where
the implementation differs from the decision text below:

- **Copies when the record is written**, not when the rule opens: inputs
  are still live then (no kernel pass rolls back its caller's nodes), and
  the identity recorded at the open is checked first; a `whnf` that
  changed nothing then costs no copy.
- **The copier's walk** uses two bounded stacks of its own (tasks and
  values) instead of a `context-walk:` record, and a work bound per copy;
  it does not depend on the heap stores' capacities (ADR 0016 step 3).
  Constant references above the input marks are copied with their
  universe arguments (a reference pool and an argument pool).
- **Printing without a view.** The term printer reads the stores directly
  in dozens of places; instead of a view, `log-view.fs` rebuilds a copy as
  scratch above the input marks, prints it, and rolls back with
  `lf-input-rollback`, between checks. The input is never written; the
  scratch advances identity serials as a check does. Copied binders take
  their names from the λ whose type they are, or from the node a shift,
  instantiation or universe instantiation rebuilt.
- **Rules added:** `form` (7: inference of a node it does not handle) and
  `type` (43: a definition's type is a type; `proposition` is a theorem's).
  `fresh-name` and `distinct-parameters` record the declaration's number,
  `resolve` is written by `lf-env-lookup` (the path the constant rule
  takes), and `publish`'s `start` is that of the step it uses, so
  sub-derivations stay nested.
- **Memory differs from D3's estimate** (owner to confirm): the pools are
  223,264 bytes (about 218 KiB) per context while the log is on, not
  "about 150 KB"; they are one heap block that exists only while a log is
  on (freed when a check begins with the log off, and by the context's
  teardown, ADR 0009 amendment), so a context with the log off holds a
  224-byte header. The printers' state (64,624 bytes) is heap-held only
  while an outline prints. The pools allocate when a log starts, before
  the check's first rule; no memory truncates the log (bound `memory`).
- **Heap with the log on and off** (L5): the pools' 218 KiB are taken
  only while the log is on, so on a host where that much memory decides
  whether a heap store can grow, a check could end *full* with the log on
  and *ok* with it off; nowhere else can the two differ.
- **Inductive blocks** (rule 44, `inductive-block`, added for ADR 0015's
  block check): one step for the whole block check, which its publish
  step follows; the block's own rules are not yet steps of their own.
  The outline printer prints nothing from a log that fails the
  structural check (`src/present/log-check.fs`).
- **Interrupted** (L6) is a truncation bound: a check that ends with rules
  open writes no publish step, and the log says `truncated at step N (the
  check stopped with rules open)`.
- **The header copy at publish (L2)** keeps the published slot and outcome
  (and the input's fingerprint from the log's start), which the outline
  printer compares with the verdict it is given; it does not copy the
  diagnostic, which the printer reads from the context.
- **The isolation check** (L5 item 6) is an allow-list per layer and for
  the log module itself (`tests/core/check_log_isolation.py`).
- **The stack re-measurement** (L5 item 5) was done by the review of
  2026-11-03 (two return cells more with the log off, four with it on,
  against a need of 1,728); the numbers are in DERIVATION_LOG.md.
- **Not yet:** the NDJSON writer and the observer (L6), the publish step of
  the parallel hand-over, the outline's Markdown and JSON forms and the
  statement "in words".

## Summary in plain words

When LeanForth checks a proof it applies small rules one after another:
"this variable has that type", "applying `f` to `value` gives a proof of
`B`", "these two types are the same". Today it keeps none of that; it only
says *accepted* or why not. The **derivation log** is an optional notebook
in which the checker writes one numbered line per rule it applies: which
rule, what it was applied to, what came out, how many binders deep it was,
which earlier lines it used, and where in the input file the pieces came
from. The **proof outline** is a separate printer that reads the notebook
and prints a short, readable proof — "Assume f : A → B. … Then f value : B,
because f turns any proof of A into a proof of B." — in which every line
points to the notebook lines the checker actually wrote.

Three promises. First, the notebook never changes a verdict: the same input
gives exactly the same answers with the log off, on, or out of room; nothing
in the checker ever reads it. Second, when the notebook runs out of room it
stops and says so ("log incomplete at step N"); the verdict is unaffected,
and no outline is printed from an incomplete log. Third, the English
sentences are fixed templates and are labelled as such; only the rules,
formulas and step numbers come from the checker.

The log is off unless asked for. Measured cost while it is off: one test of
a flag, about 1.7 ns on `gforth-fast` and 6 ns on `gforth`, 404 times per
round of the fixed checker workload — below the run-to-run noise (*Cost*).

## Problem

AGENTS.md requires proof steps with source IDs and derivation references,
and says explanatory prose is no substitute for checked derivations. The
plan (§7, tasks 2.4.1–2.4.4) wants readable proofs early, starting with
`composition` in phase 2, with "every printed line points to a step the
checker actually performed". The term printer (2.4.2–2.4.3,
[printing terms](../user/TERM_PRINTER.md)) prints a declaration's statement
and proof term, but not the reasoning between them: the checker records
none. The diagnostic record keeps only the *first failure*; a derivation
needs *every success*, in order, with its premises.

Constraints:

- **No behaviour change** (plan 2.4.1's acceptance): verdicts identical
  with the log off, on and full.
- **Parallel contexts** (ADR 0009): checks run in separate contexts on
  separate tasks; each needs its own bounded log, reached through the
  context, with no locks and no shared mutable state.
- **Scratch is short-lived.** The types and reducts the checker builds lie
  above the input marks and are rolled back inside the check
  (`lf-mconvert-run`, `lf-minfer-rollback`, the definition probe's
  rewind, `lf-input-rollback`). A log that only pointed at them would point
  at nodes that are later reused for other terms.
- **The kernel never loads presentation code** (TERM_PRINTER.md: "the
  checker never loads it"), and nothing may print or pause inside a job or
  the publisher (ADR 0012, G-P2).
- **Determinism** (plan 2.2.5): the same input checked twice gives the same
  bytes.

## Decision (proposed)

### L1 One record per rule application

A record is seven cells, `/lf-logrec`, in the log's buffer. Its step number
is its position (step 1 is the first record of a check), so it is not
stored.

| Field | Contents |
| --- | --- |
| `logrec-rule` | the rule's code, from the catalogue below |
| `logrec-outcome` | the rule's outcome (ADR 0008): ok, or the failure with which the rule ended |
| `logrec-start` | how many records existed when the rule began; its own sub-derivation is steps `start+1` … `step−1` |
| `logrec-depth` | how many binders surround the subject in the check's context when the rule began |
| `logrec-a`, `logrec-b` | the rule's inputs, as its catalogue entry says: a reference or a number |
| `logrec-out` | its result: a reference, a number, or none |

**Premises without a list.** Records are written in *post-order*: a rule's
record is written when the rule ends, after the records of everything it
used. Its premises are then exactly the top-level records of its
sub-derivation, found from `start` alone: the last record before it is a
premise; the record just before that premise's own sub-derivation is the
next premise; and so on while the step is above `start`. For example
`application` at step 50 began with 43 records written; its premises are
s49 (whose `start` is 48), s48 (`start` 47), s47 (`start` 45) and s45
(`start` 43, which ends the chain). One cell encodes the whole tree, and no
premise numbers are carried on the host stacks.

**References.** A reference is one cell: `n ≥ 0` is input object `n`
(below the input marks of [`src/core/input.fs`](../../src/core/input.fs),
which never change once loading ends), of the kind the catalogue entry
says: term, level, name or environment slot; `−1 − k` is copy `k` in the
log's own term or level pool; two sentinels at the most negative cell
values mean *none* and *not kept* (a scratch object at level `steps`, which
keeps no copies).

**Copies.** At level `terms` the log copies every scratch object a record
mentions into its own pools, at the moment it is alive: inputs when the
rule begins, the result when it ends. A copied node keeps its tag and its
children as references, so input subterms are shared, never copied. A
direct-mapped memo of 1,024 entries, keyed by node index and checked
against the node's identity stamp, copies a scratch node once even when
several records mention it; a collision only costs a second copy. The
copier walks with its own walk record (`context-walk:`, never another
module's), so it cannot overflow the host stacks, and it reads only through
the read-only accessors `lf-term-read`, `lf-term-identity`,
`lf-level-read`, `lf-level-identity` and the constant-reference readers.
Constant references are copied as their name and level references.

**Rule catalogue** (stable numbers, like the diagnostic codes; JSON names
in the second column). Every term or level in it is a reference: an input
object or a copy.

| Code | Rule | Inputs a, b | Result | Premises |
| --- | --- | --- | --- | --- |
| 1 | `sort` | the Sort term | its type | — |
| 2 | `variable` | the bound variable | its type | the shift of its binder's domain |
| 3 | `constant` | the constant | its type | its resolution and level instantiation |
| 4 | `application` | the application | its type | function's type, argument's type, `defeq`, `instantiate` |
| 5 | `lambda` | the λ | its type, a Π | the domain's type, the body's type |
| 6 | `pi` | the Π | its Sort | the domain's type, the body's type |
| 10 | `whnf` | the term | its weak head normal form | its `beta` steps |
| 11 | `beta` | λ body, argument | the contractum | its `instantiate` |
| 12 | `defeq` | left, right | — | the `whnf` and `level-eq` steps of the comparison |
| 13 | `level-eq` | left level, right level | — | — |
| 20 | `instantiate` | body, argument | the instantiated body | — |
| 21 | `shift` | term, amount (number) | the shifted term | — |
| 22 | `instantiate-levels` | type, level count (number) | the type with the levels put in | — |
| 30 | `resolve` | name | slot (the dependency recorded) | — |
| 31 | `fresh-name` | the declaration's name | — | — (N2) |
| 32 | `universe-arity` | levels given (number), slot | — | — (L1) |
| 33 | `universe-parameter` | name | — | — (L2) |
| 34 | `distinct-parameters` | parameter count (number) | — | — (L3) |
| 40 | `proposition` | the statement | its Sort's level | the statement's type formation (S3) |
| 41 | `declaration` | statement, value | — | name and parameter rules, type formation, value's type, `defeq` |
| 42 | `publish` | slot, dependency count (number) | — | the declaration; the outcome field is the published outcome |

The rule names follow plan §7.5's fixed list; `let`, unfolding, recursor
rules, eta, proof irrelevance, literals, projections and quotients get
codes when the checker has them. A Python check, like
`tests/core/check_diagnostics_catalogue.py`, keeps this table and the
code's table equal.

### L2 Storage: a bounded log in every context

- **State per context.** One context record, `lf-log-state`
  (`context-record:`, ADR 0009), holds the header, the record buffer, the
  stack of open rules (*marks*: start, a, b, rule, depth — five cells
  each), the term and level copy pools and the memo. Each worker has its
  own; nothing is shared or locked. A new context starts with the log
  inactive.
- **Options shared and read-only during a run.** `lf-log-options` (level,
  record and copy limits at or below the capacities, and an observer
  word) is set outside jobs before a run, like the run mode and capacities
  of ADR 0012 E7. `lf-env-begin` copies the level into the context's
  `log-active` cell, so a replacement context made after a `THROW` logs
  like the one it replaces. Levels: `off` (0), `steps` (1: records, no
  copies), `terms` (2: records and copies; the outline needs this).
- **The hot test** is `lf-log? ( -- flag )`: `log-active` of the current
  context, nonzero only while this check logs and the log is not
  truncated. Kernel words call the open and close words (L4) only after
  it is true.
- **Lifetime, as for diagnostics.** `lf-env-begin` clears the log and
  records the declaration; `lf-env-finish` copies the check's outcome and
  the diagnostic (code, site text, numbers) into the header; the log then
  stays readable until the next `lf-env-begin` in that context. Checks run
  outside the environment (unit tests calling `lf-mixed-infer` directly)
  never activate it, so they run exactly as today; a test that wants their
  log calls `lf-log-start`.
- **Capacities** are constants fixed when the context layout is sealed
  (phase 2: 1,024 records, 256 marks, 2,048 copied terms, 512 copied
  levels, a 1,024-entry memo: about 150 KB per context); configurable
  capacities come with plan task 3.3.1.

### L3 When the log is full

The first bound reached wins, as the first failure wins in diagnostics: a
record with no room, a mark with no room, a copy with no room in its pool,
a copy that would need more walking than the pool has room left, or a
node the copier cannot read. The log then records the step number it could
not write and which bound stopped it, sets `log-active` to 0 and records
nothing more for this check (the end of the check is still copied into the
header). So a truncated log is always a consistent *prefix*: steps 1 … N−1
are complete, with every premise present; nothing after them exists.

Only the log becomes incomplete. The check goes on and ends with the same
outcome, result and fuel; the NDJSON end line says `"complete":false` and
`"truncated":{"atStep":"sN","bound":"records"}`; the outline printer prints
the verdict and "proof outline not available: the checker's log was
truncated at step N (records); the verdict is unaffected", and no outline.
The word *full* stays reserved for the outcome `full`; the log is
*truncated* or *incomplete*.

### L4 Where each rule records

**Protocol.** A rule *opens* (`lf-log-open ( a b rule -- a b )`, or for
inference `lf-log-infer ( node depth -- node )`, which takes the rule from
the node's tag) and *closes* exactly once (`lf-log-close ( r outcome -- r
outcome )`, or `lf-log-decided ( outcome -- outcome )` for rules without a
term result). Open pushes a mark and copies scratch inputs; close pops it,
copies the result and writes the record with the outcome it is given —
also a failure, so a failed check's log ends with the chain of rules that
failed. The one exception: `whnf` that changed nothing applied no rule and
writes no record. Closes return their arguments unchanged. The current
depth is inherited from the innermost open mark, so passes called from
inference record the inference depth; a comparison's own descent under
binders is not tracked (its pairs have their own records).

**Map onto today's kernel** (K1 is editing these files now; the
implementation follows the names it leaves, and this table is updated):

| Rule | File | Word | Opens with | Closes with |
| --- | --- | --- | --- | --- |
| `sort`, `variable`, `constant`, `application`, `lambda`, `pi` | [`src/kernel/mixed-infer.fs`](../../src/kernel/mixed-infer.fs) | `lf-minfer-in-frame`, the single recursion point (after its fuel and frame check) | the node, `lf-minfer-context-depth` | type, outcome |
| `whnf` | [`src/kernel/mixed-beta.fs`](../../src/kernel/mixed-beta.fs) | `lf-mixed-beta` (reached from `lf-mconvert-whnf`) | the term | reduct, outcome |
| `beta` | `mixed-beta.fs` | `lf-mbeta-contract`, around `lf-mbeta-instantiate` (before `frame-call`) | λ body, argument | contractum, outcome |
| `defeq` | [`src/kernel/mixed-convert.fs`](../../src/kernel/mixed-convert.fs) | `lf-mixed-convert` (from `lf-minfer-convert`, and the declaration check) | left, right | outcome |
| `level-eq` | [`src/kernel/level-compare.fs`](../../src/kernel/level-compare.fs) | `lf-level-compare` (from `lf-mconvert-levels`) | left, right | outcome |
| `instantiate` | [`src/kernel/mixed-instantiate.fs`](../../src/kernel/mixed-instantiate.fs) | `lf-mixed-instantiate` (from `lf-minfer-substitute`, `lf-mbeta-instantiate`) | body, argument | result, outcome |
| `shift` | [`src/kernel/mixed-shift.fs`](../../src/kernel/mixed-shift.fs) | `lf-mixed-shift` (from `lf-minfer-shift`) | term, amount | result, outcome |
| `instantiate-levels` | [`src/kernel/mixed-level-substitute.fs`](../../src/kernel/mixed-level-substitute.fs) | `lf-mixed-level-substitute` (from the signature probe today, the constant rule with 2.2.3) | type, count | result, outcome |
| `resolve` | [`src/kernel/environment.fs`](../../src/kernel/environment.fs) | `lf-env-resolve` | name | slot, outcome |
| `fresh-name`, `universe-arity`, `universe-parameter`, `distinct-parameters` | `environment.fs` | `lf-env-own-name`, `lf-env-arity?`, `lf-env-param?`, `lf-env-own-params` | as the catalogue says | outcome |
| `proposition`, `declaration` | the declaration check (task 2.2.3, not written yet) | its entry word, open at its start | statement, value | outcome |
| `publish` | [`src/kernel/env-publish.fs`](../../src/kernel/env-publish.fs) | `lf-env-step`, right after `lf-env-hand-over-at`, outside the publisher's `CATCH`; its premise is the check's last record | slot, dependency count | the published outcome |
| (begin, finish) | `environment.fs` | `lf-env-begin`, `lf-env-finish` | — | — |
| (observer) | `env-publish.fs` | `lf-env-step`, last, under `CATCH` (L6) | — | — |

Not logged, because they are not rules of the derivation: the audits and
preflights (`lf-cterm-check`, `lf-constant-term-scope`,
`lf-mixed-signature-audit`, `lf-rebuild-audit`, the level-scope audits),
the shift inside instantiation (`lf-mshift-inside`), level evaluation
inside comparison (`lf-level-value`), the environment's scans and the
publisher's re-check (its result is the `publish` record's outcome). Their
failures stay explained by the diagnostic.

**The inference site**, as it would read. The visit runs from the same
word on both paths, so a level of inference holds the same host-stack
cells with the log on and off:

```forth
: lf-minfer-logged ( node -- node ) lf-minfer-context-depth @ lf-log-infer ;
: lf-minfer-in-frame ( node -- type status )
  lf-minfer-room ok-then? 0= if no-result exit then
  lf-minfer-enter
  lf-log? if lf-minfer-logged lf-minfer-visit lf-log-close
  else lf-minfer-visit then -1 lf-minfer-depth +! ;
```

Each pass's public word does the same around its body: `lf-log? if`
open, run, close `else` run `then`.

### L5 Why no verdict can change

1. The log writes only its own context record. It never writes a store,
   a walk or frames record of another module, fuel, the diagnostic, the
   environment or anything shared.
2. It reads checker state only through the read-only accessors of L1,
   and copies a node only after finding it live with the identity the
   record expects.
3. It never `THROW`s or `ABORT`s, never `ALLOCATE`s (its record is sized
   when the layout seals), never prints or pauses. Every bound is checked
   before it is used; a bound reached truncates the log (L3).
4. No checker word reads anything the log writes except `lf-log?`, which
   chooses between two paths that run the same kernel word with the same
   stack effect; open and close return their arguments unchanged.
5. Host stacks: the logged path adds no cells per level of recursion
   (subjects wait on the log's mark stack, not the host's); the open,
   close and copy words add a constant at the deepest point. The stated
   needs (`lf-minfer-rs-level`, `lf-mbeta-rs-level` and the slack,
   `context-need`) are re-measured by stack painting with the log at
   `terms`; loading refuses hosts whose stacks are smaller, so the log
   cannot turn a result into a stack-overflow `THROW`.
6. **Isolation check** (in `make test`, like the diagnostics catalogue
   check): a script fails if a file under `src/` other than the log module
   names a log word other than `lf-log?` and the open, close, begin,
   finish, published and observe words; if the log module calls a word
   outside its allowlist (the read-only accessors, `walk.fs`, `store.fs`
   readers); or if the log module mentions `lf-diag-note`, `throw`,
   `abort`, `allocate`, `type` or `emit`.

### L6 Getting the log out: NDJSON from a deterministic writer

After each declaration, `lf-env-step` calls the run's **observer** (an xt
in the options; none by default) under `CATCH`, after the slot is final
and the scratch is rolled back. A `THROW` in the observer is recorded as
"log output failed" and reported after the run; the slot is already
final, so no verdict can change. The observer runs outside jobs: a
parallel scheduler (phase 7) calls it from the driving task after each
hand-over, in slot order.

The writer, `src/present/derivation-ndjson.fs` (untrusted presentation
code, never loaded by the checker), writes one group of lines per
declaration. Plan task 3.1.3's `lib/json-write.fs` (fixed key order,
escaping), being written now, is the intended way to emit them; this
design fixes the bytes, not that module's words, so the writer can follow
whatever 3.1.3 provides or emit these few shapes itself:

| Line | Keys, in this order |
| --- | --- |
| begin | `log` ("begin"), `schema` ("leanforth.derivation-log"), `version` ("0.1"), `decl`, `name`, `kind`, `source` {`file`, `sha256`, `line`}, `level`, `limits` {`records`, `copies`} |
| level copy | `log` ("level"), `id`, then one of `succ`, `max` [a, b], `imax` [a, b], `param` |
| term copy | `log` ("term"), `id`, then one of `bvar`, `sort`, `const` {`name`, `us`}, `app` {`fn`, `arg`}, `lam` {`type`, `body`}, `forallE` {`type`, `body`} |
| step | `log` ("step"), `step`, `rule`, `outcome`, `depth`, `a`, `b`, `out`, `from`, `premises` |
| end | `log` ("end"), `decl`, `outcome`, `published`, `fault`, `steps`, `complete`, `truncated`, `interrupted`, `diagnostic` {`code`, `name`, `site`, `first`, `second`}, `axioms`, `label` |

- **References as strings.** Input objects by their numbers in Lean's
  export format, as the fixture files use them: `ie12` (expression),
  `il0` (level), `in5` (name); copies `le7`, `ll2`; slots `d0`; steps
  `s50`. A run whose input did not come from an export file (terms built by
  tests) prints store indices with the prefixes `te`, `tl`, `tn` instead,
  and its begin line says so. The store-to-export mapping comes from the
  presentation side table (`lf-pres-source@`, task 2.4.2) and the
  decoder's index tables (task 3.2.1); the kernel record holds only store
  indices.
- **Copies first.** Copy lines come right after the begin line, in the
  order they were made; a copy refers only to input objects and earlier
  copies. Steps then follow in step order. `from` is the first step of the
  step's sub-derivation (`start + 1`, or the step itself), and `premises`
  is the list L1 derives, ascending.
- **Bytes.** One line per record, ending in a line feed; no spaces; keys in
  the order above; integers in decimal whatever `BASE` is; strings with
  `"` and `\` escaped by a backslash, U+0000–U+001F as `\u00XX` (lower
  case) and everything else, UTF-8 included, as is; `null` for none and
  not kept. Never written: addresses, identity stamps, store serials,
  context or job handles, worker numbers, times. A diagnostic number that
  is an identity or a serial (codes 8, 21, 25, 27) is written as `null`.
  If 3.1.3 settles on another escaping rule, this design follows it and
  the golden files are regenerated once.

### L7 The proof outline (task 2.4.4)

`src/present/proof-outline.fs` turns one declaration's log into a readable
proof, in text (Unicode), Markdown (with LaTeX math) or JSON (the
proof-step schema of [INTERFACE_CONTRACTS.md](../programming/INTERFACE_CONTRACTS.md)).
It runs in the observer, after the check, from the in-memory log (later
also from a saved NDJSON log, `leanforth print`, plan 3.4). It prints
formulas with the term printer, which gains two things in 2.4.4: printing
an open term under a list of binder names, and reading nodes through a
*view*, so that the log view reads input objects from the stores
(read-only) and copies from the log's pools — the printer never writes the
checker's stores. Binder names come from the side table of the λ and Π
records around each step; a copied binder takes the name of the λ whose
type it is, otherwise `x`, as the printer does today.

**Recognisers** (untrusted) for the λ/application fragment; anything else
prints as a numbered list of raw steps:

| Pattern in the log | Line | Rule shown |
| --- | --- | --- |
| the `proposition` record and its type formation | in the header: the statement is a proposition | (type formation) |
| a run of `lambda` records whose domains are types of propositions or types (`Prop`, `Sort u`) | "Let A, B, C be propositions." / "Let α be a type." | ∀-introduction |
| a `lambda` record whose domain is a proposition | "Assume f : A → B." | assumption |
| an `application` whose function's type is a non-dependent arrow between propositions | "Then f value : B, because f turns any proof of A into a proof of B." | →-elimination |
| an `application` with a dependent function type | "Then h a : P a, because h holds for every x, in particular for a." | ∀-elimination |
| the `lambda` records that close the binders | "Discharging 4, 3, 2 and 1 gives …" | →/∀-introduction |
| the declaration's `defeq` between the proof's type and the statement | "This is the statement." (with "after computation, sN" when it needed `whnf`) | definitional equality |

**Folding.** `variable` steps point to the line that introduced their
binder; `shift`, `instantiate`, `whnf`, `beta`, `level-eq` and the
argument's `defeq` fold into the line of the rule that used them; the
`lambda` records closing one `fun` chain fold into one discharge line. A
line's premises (`← 2, 4`) are the lines its folded steps' premises map
to; none is invented. `--detail` prints every step instead.

**What is checked and what is only explanation.**

- *Checked* (comes from records the checker wrote, with outcome ok, in a
  declaration published as accepted): each line's formula — exactly the
  term the checker computed and the log copied, printed by the term
  printer; the rule codes; the premise structure; the final match with the
  statement; the verdict, the label *experimental — not independently
  audited* and the axiom list, read from the environment.
- *Explanation only* (untrusted, tagged `structured-template`): every
  English sentence ("Let", "Assume", "because …", "Discharging", the
  statement in words), the grouping and folding, the line numbers, the
  choice of names and notation. Each template has an identifier and a
  version (`implies-elim/v0`); golden files pin them. A wrong template
  misleads a reader but changes no verdict. Imported Lean proofs carry no
  author's reasoning, so for them the whole outline is a reconstruction
  from the proof term, and it says so (`"reconstructed": true`, plan §7).
- An outline is printed only for a declaration published as *accepted*
  with a complete log; otherwise the verdict, the diagnostic and, with
  `--detail`, the steps up to the failure.

### L8 Replay (plan task 2.2.5)

The log is deterministic by construction: step numbers count rules in the
check's own order, copies are numbered per check in the order made, input
objects print as export numbers, and nothing timing-, address- or
serial-dependent is written (L6). The check's own work is deterministic
given its input and the slots its snapshot reads (ADR 0012, G-P4). So:

- The run record of 2.2.5 lists the log's options and limits and, when a
  log was written, its SHA-256. Replay with the same options must give a
  byte-identical log; with the log off, identical verdicts.
- Logs are compared across: two runs; the serial driver against jobs and
  interleaved contexts (phase 7: groups are written in slot order, so the
  bytes match the serial run); Gforth 1.0 against 0.7.3. A difference is a
  test failure; the replay tool names the first differing line, which
  locates nondeterminism to one rule.
- The log is not a certificate: nothing reads it to decide acceptance. A
  certificate format checked by a second checker would be its own
  [format] and [kernel] decision.

## Golden example: `composition`

The pinned fixture `tests/reference/composition.lean`,

    theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
      fun value => g (f value)

exported as `tests/reference/composition.ndjson` (35 lines, SHA-256
`7778d2ef5da2f0935fb0180c953afa9371843f4ceec2660122f8c792b9ca2fec`):
statement `ie10` (line 23), proof `ie20` (line 34), theorem record line
35. Its binders `A`, `B`, `C`, `f`, `g`, `value` are the λs `ie20` … `ie15`
(lines 34 … 29). The log below follows today's inference word by word; for
the declaration check (2.2.3, not written yet) it assumes the order of the
definition probe and ADR 0011: N2, L3, the statement's type, the value's
type, their comparison. If 2.2.3 orders its steps differently, the golden
files of 2.4.1 and 2.4.4 pin what it does and this example is updated.

### The log (level `terms`): 65 steps

*Note (plan task 4.2.2a, free variables, ADR 0014 Q2):* a variable's type
is now its local-context entry's, as in Lean's `infer_fvar`, so a
`variable` step has no `shift` premise. The log is this table without its
14 `shift` steps: 51 steps, renumbered, with the same rules, depths,
formulas and other premises; `tests/present/outlines.golden` holds it.

Depth is the number of binders around the subject; formulas are shown as
the term printer would print them in that context. "(copy)" marks a
scratch result the log copied.

| Step | Rule | Depth | a | b | Result | Premises |
| --- | --- | --- | --- | --- | --- | --- |
| s1 | `fresh-name` | 0 | `in1` composition | | | |
| s2 | `distinct-parameters` | 0 | 0 | | | |
| s3 | `sort` | 0 | `ie0` Prop | | Type (copy) | |
| s4 | `sort` | 1 | `ie0` | | Type (copy) | |
| s5 | `sort` | 2 | `ie0` | | Type (copy) | |
| s6 | `shift` | 3 | `ie0` | 3 | `ie0` Prop | |
| s7 | `variable` | 3 | `ie1` A | | Prop | s6 |
| s8 | `shift` | 4 | `ie0` | 3 | `ie0` | |
| s9 | `variable` | 4 | `ie1` B | | Prop | s8 |
| s10 | `pi` | 3 | `ie2` A → B | | Prop (copy) | s7, s9 |
| s11 | `shift` | 4 | `ie0` | 3 | `ie0` | |
| s12 | `variable` | 4 | `ie1` B | | Prop | s11 |
| s13 | `shift` | 5 | `ie0` | 3 | `ie0` | |
| s14 | `variable` | 5 | `ie1` C | | Prop | s13 |
| s15 | `pi` | 4 | `ie2` B → C | | Prop (copy) | s12, s14 |
| s16 | `shift` | 5 | `ie0` | 5 | `ie0` | |
| s17 | `variable` | 5 | `ie3` A | | Prop | s16 |
| s18 | `shift` | 6 | `ie0` | 4 | `ie0` | |
| s19 | `variable` | 6 | `ie4` C | | Prop | s18 |
| s20 | `pi` | 5 | `ie5` A → C | | Prop (copy) | s17, s19 |
| s21 | `pi` | 4 | `ie6` (B → C) → A → C | | Prop (copy) | s15, s20 |
| s22 | `pi` | 3 | `ie7` (A → B) → (B → C) → A → C | | Prop (copy) | s10, s21 |
| s23 | `pi` | 2 | `ie8` ∀ {C : Prop}, … | | Prop (copy) | s5, s22 |
| s24 | `pi` | 1 | `ie9` ∀ {B C : Prop}, … | | Prop (copy) | s4, s23 |
| s25 | `pi` | 0 | `ie10` the statement | | Prop (copy) | s3, s24 |
| s26 | `proposition` | 0 | `ie10` | | `il0` | s25 |
| s27 | `sort` | 0 | `ie0` | | Type (copy) | |
| s28 | `sort` | 1 | `ie0` | | Type (copy) | |
| s29 | `sort` | 2 | `ie0` | | Type (copy) | |
| s30 | `shift` | 3 | `ie0` | 3 | `ie0` | |
| s31 | `variable` | 3 | `ie1` A | | Prop | s30 |
| s32 | `shift` | 4 | `ie0` | 3 | `ie0` | |
| s33 | `variable` | 4 | `ie1` B | | Prop | s32 |
| s34 | `pi` | 3 | `ie2` A → B | | Prop (copy) | s31, s33 |
| s35 | `shift` | 4 | `ie0` | 3 | `ie0` | |
| s36 | `variable` | 4 | `ie1` B | | Prop | s35 |
| s37 | `shift` | 5 | `ie0` | 3 | `ie0` | |
| s38 | `variable` | 5 | `ie1` C | | Prop | s37 |
| s39 | `pi` | 4 | `ie2` B → C | | Prop (copy) | s36, s38 |
| s40 | `shift` | 5 | `ie0` | 5 | `ie0` | |
| s41 | `variable` | 5 | `ie3` A | | Prop | s40 |
| s42 | `shift` | 6 | `ie2` | 2 | B → C (copy) | |
| s43 | `variable` | 6 | `ie11` g | | B → C | s42 |
| s44 | `shift` | 6 | `ie2` | 3 | A → B (copy) | |
| s45 | `variable` | 6 | `ie1` f | | A → B | s44 |
| s46 | `shift` | 6 | `ie3` | 1 | A (copy) | |
| s47 | `variable` | 6 | `ie12` value | | A | s46 |
| s48 | `defeq` | 6 | A (f's domain) | A (value's type) | | |
| s49 | `instantiate` | 6 | B (body of f's type) | `ie12` value | B (copy) | |
| s50 | `application` | 6 | `ie13` f value | | B | s45, s47, s48, s49 |
| s51 | `defeq` | 6 | B (g's domain) | B (s50's result) | | |
| s52 | `instantiate` | 6 | C (body of g's type) | `ie13` f value | C (copy) | |
| s53 | `application` | 6 | `ie14` g (f value) | | C | s43, s50, s51, s52 |
| s54 | `lambda` | 5 | `ie15` fun value ↦ … | | A → C (copy) | s41, s53 |
| s55 | `lambda` | 4 | `ie16` | | (B → C) → A → C (copy) | s39, s54 |
| s56 | `lambda` | 3 | `ie17` | | (A → B) → (B → C) → A → C (copy) | s34, s55 |
| s57 | `lambda` | 2 | `ie18` | | ∀ {C : Prop}, … (copy) | s29, s56 |
| s58 | `lambda` | 1 | `ie19` | | ∀ {B C : Prop}, … (copy) | s28, s57 |
| s59 | `lambda` | 0 | `ie20` the proof | | ∀ {A B C : Prop}, (A → B) → (B → C) → A → C (copy) | s27, s58 |
| s60 | `level-eq` | 0 | `il0` | `il0` | | |
| s61 | `level-eq` | 0 | `il0` | `il0` | | |
| s62 | `level-eq` | 0 | `il0` | `il0` | | |
| s63 | `defeq` | 0 | s59's result | `ie10` | | s60, s61, s62 |
| s64 | `declaration` | 0 | `ie10` | `ie20` | | s1, s2, s26, s59, s63 |
| s65 | `publish` | 0 | `d0` | 0 | (published ok) | s64 |

The three `level-eq` steps are the comparison meeting `Prop` against
`Prop` at the binders A, B and C; no `whnf` step appears because nothing
reduced. Every `defeq` here is between syntactically equal terms.

### NDJSON, an excerpt

Copy identifiers depend on how the passes share nodes; these are
illustrative, and the golden file of 2.4.1 pins the real ones.

```text
{"log":"begin","schema":"leanforth.derivation-log","version":"0.1","decl":0,"name":"composition","kind":"theorem","source":{"file":"tests/reference/composition.ndjson","sha256":"7778d2ef5da2f0935fb0180c953afa9371843f4ceec2660122f8c792b9ca2fec","line":35},"level":"terms","limits":{"records":1024,"copies":2048}}
{"log":"level","id":"ll0","succ":"il0"}
{"log":"term","id":"le0","sort":"ll0"}
{"log":"step","step":"s3","rule":"sort","outcome":"ok","depth":0,"a":"ie0","b":null,"out":"le0","from":"s3","premises":[]}
{"log":"step","step":"s48","rule":"defeq","outcome":"ok","depth":6,"a":"le19","b":"le22","out":null,"from":"s48","premises":[]}
{"log":"step","step":"s49","rule":"instantiate","outcome":"ok","depth":6,"a":"le20","b":"ie12","out":"le23","from":"s49","premises":[]}
{"log":"step","step":"s50","rule":"application","outcome":"ok","depth":6,"a":"ie13","b":null,"out":"le23","from":"s44","premises":["s45","s47","s48","s49"]}
{"log":"step","step":"s65","rule":"publish","outcome":"ok","depth":0,"a":"d0","b":0,"out":null,"from":"s64","premises":["s64"]}
{"log":"end","decl":0,"outcome":"ok","published":"ok","fault":false,"steps":65,"complete":true,"truncated":null,"interrupted":false,"diagnostic":null,"axioms":[],"label":"experimental — not independently audited"}
```

### Text

```text
Theorem composition
  accepted — experimental, not independently audited; axioms: none
  Statement: ∀ {A B C : Prop}, (A → B) → (B → C) → A → C
  In words:  for all propositions A, B, C: if A implies B, and B implies C, then A implies C.
  Input:     tests/reference/composition.ndjson line 35
             sha256 7778d2ef5da2f0935fb0180c953afa9371843f4ceec2660122f8c792b9ca2fec
  Checker log: 65 steps, complete. The statement is a proposition: s26 (from s3).

Proof (reconstructed from the proof term).
  1  Let A, B, C be propositions.                  [∀-introduction]                   s27–s29
  2  Assume f : A → B.                             [assumption]                       s34
  3  Assume g : B → C.                             [assumption]                       s39
  4  Assume value : A.                             [assumption]                       s41
  5    Then f value : B,                           [→-elimination ← 2, 4]             s50
       because f turns any proof of A into a proof of B.
  6    Then g (f value) : C,                       [→-elimination ← 3, 5]             s53
       because g turns any proof of B into a proof of C.
  7  Discharging 4, 3, 2 and 1 gives               [→/∀-introduction ← 1, 2, 3, 4, 6] s54–s59
       ∀ {A B C : Prop}, (A → B) → (B → C) → A → C.
  8  This is the statement.                        [definitional equality ← 7]        s63
∎
Rules and step numbers come from the checker's log. The sentences are fixed
templates (structured-template), not checked reasoning.
```

### Markdown

```markdown
### Theorem `composition`

**accepted — experimental, not independently audited; axioms: none** ·
input `tests/reference/composition.ndjson` line 35, sha256
`7778d2ef5da2f0935fb0180c953afa9371843f4ceec2660122f8c792b9ca2fec` ·
checker log: 65 steps, complete

**Statement.** $\forall \{A\ B\ C : \mathrm{Prop}\},\ (A \to B) \to (B \to C) \to A \to C$,
a proposition (step s26, from s3). *In words (structured-template):* for all
propositions A, B, C: if A implies B, and B implies C, then A implies C.

**Proof** (reconstructed from the proof term).

| # | Line | Rule | Uses | Checker steps |
| ---: | --- | --- | --- | --- |
| 1 | Let $A, B, C$ be propositions. | ∀-introduction | | s27–s29 |
| 2 | Assume $f : A \to B$. | assumption | | s34 |
| 3 | Assume $g : B \to C$. | assumption | | s39 |
| 4 | Assume $\mathit{value} : A$. | assumption | | s41 |
| 5 | Then $f\ \mathit{value} : B$, because $f$ turns any proof of $A$ into a proof of $B$. | →-elimination | 2, 4 | s50 |
| 6 | Then $g\ (f\ \mathit{value}) : C$, because $g$ turns any proof of $B$ into a proof of $C$. | →-elimination | 3, 5 | s53 |
| 7 | Discharging 4, 3, 2 and 1 gives $\forall \{A\ B\ C : \mathrm{Prop}\},\ (A \to B) \to (B \to C) \to A \to C$. | →/∀-introduction | 1, 2, 3, 4, 6 | s54–s59 |
| 8 | This is the statement. | definitional equality | 7 | s63 |

∎ *Rules and step numbers come from the checker's log; the sentences are
fixed templates (`structured-template`), not checked reasoning.*
```

### JSON

Shown indented for reading; the golden file holds the same value on one
line, without spaces, keys in the order shown. `astRef` names an input
expression (`ie10`) or the result of a log step (`s50/out`), never a
scratch node. `context` lists the names in scope, outermost first.

```json
{
  "schemaVersion": "0.1",
  "kind": "proof-outline",
  "reconstructed": true,
  "declaration": {"name": "composition", "kind": "theorem", "slot": 0,
    "source": {"file": "tests/reference/composition.ndjson",
      "sha256": "7778d2ef5da2f0935fb0180c953afa9371843f4ceec2660122f8c792b9ca2fec", "line": 35}},
  "verdict": {"kernelStatus": "kernel-accepted",
    "label": "experimental — not independently audited", "axioms": []},
  "statement": {
    "conclusion": {"astRef": "ie10", "pretty": "∀ {A B C : Prop}, (A → B) → (B → C) → A → C"},
    "explanation": {"text": "For all propositions A, B, C: if A implies B, and B implies C, then A implies C.",
      "source": "structured-template", "template": "statement-in-words/v0", "proofBased": true},
    "derivation": {"steps": ["s26"], "from": "s3"}},
  "log": {"steps": 65, "complete": true},
  "steps": [
    {"stepId": "p1", "context": [],
     "conclusion": {"astRef": "ie0", "pretty": "Prop"}, "termRef": "ie20", "termPretty": "A, B, C",
     "premiseIds": [], "rule": "forall-introduction", "declarationRefs": [],
     "kernelStatus": "kernel-accepted", "axiomRefs": [],
     "explanation": {"text": "Let A, B, C be propositions.", "source": "structured-template",
       "template": "let/v0", "proofBased": true},
     "sourceSpan": {"file": "tests/reference/composition.ndjson",
       "refs": [{"expr": "ie20", "line": 34}, {"expr": "ie19", "line": 33}, {"expr": "ie18", "line": 32}]},
     "derivation": {"steps": ["s27", "s28", "s29"], "closedBy": ["s59", "s58", "s57"]}},
    {"stepId": "p2", "context": ["A", "B", "C"],
     "conclusion": {"astRef": "ie2", "pretty": "A → B"}, "termRef": "ie17", "termPretty": "f",
     "premiseIds": [], "rule": "assumption", "declarationRefs": [],
     "kernelStatus": "kernel-accepted", "axiomRefs": [],
     "explanation": {"text": "Assume f : A → B.", "source": "structured-template",
       "template": "assume/v0", "proofBased": true},
     "sourceSpan": {"file": "tests/reference/composition.ndjson", "refs": [{"expr": "ie17", "line": 31}]},
     "derivation": {"steps": ["s34"], "closedBy": ["s56"]}},
    {"stepId": "p3", "context": ["A", "B", "C", "f"],
     "conclusion": {"astRef": "ie2", "pretty": "B → C"}, "termRef": "ie16", "termPretty": "g",
     "premiseIds": [], "rule": "assumption", "declarationRefs": [],
     "kernelStatus": "kernel-accepted", "axiomRefs": [],
     "explanation": {"text": "Assume g : B → C.", "source": "structured-template",
       "template": "assume/v0", "proofBased": true},
     "sourceSpan": {"file": "tests/reference/composition.ndjson", "refs": [{"expr": "ie16", "line": 30}]},
     "derivation": {"steps": ["s39"], "closedBy": ["s55"]}},
    {"stepId": "p4", "context": ["A", "B", "C", "f", "g"],
     "conclusion": {"astRef": "ie3", "pretty": "A"}, "termRef": "ie15", "termPretty": "value",
     "premiseIds": [], "rule": "assumption", "declarationRefs": [],
     "kernelStatus": "kernel-accepted", "axiomRefs": [],
     "explanation": {"text": "Assume value : A.", "source": "structured-template",
       "template": "assume/v0", "proofBased": true},
     "sourceSpan": {"file": "tests/reference/composition.ndjson", "refs": [{"expr": "ie15", "line": 29}]},
     "derivation": {"steps": ["s41"], "closedBy": ["s54"]}},
    {"stepId": "p5", "context": ["A", "B", "C", "f", "g", "value"],
     "conclusion": {"astRef": "s50/out", "pretty": "B"}, "termRef": "ie13", "termPretty": "f value",
     "premiseIds": ["p2", "p4"], "rule": "implication-elimination", "declarationRefs": [],
     "kernelStatus": "kernel-accepted", "axiomRefs": [],
     "explanation": {"text": "Then f value : B, because f turns any proof of A into a proof of B.",
       "source": "structured-template", "template": "implies-elim/v0", "proofBased": true},
     "sourceSpan": {"file": "tests/reference/composition.ndjson", "refs": [{"expr": "ie13", "line": 27}]},
     "derivation": {"steps": ["s50"], "premises": ["s45", "s47", "s48", "s49"]}},
    {"stepId": "p6", "context": ["A", "B", "C", "f", "g", "value"],
     "conclusion": {"astRef": "s53/out", "pretty": "C"}, "termRef": "ie14", "termPretty": "g (f value)",
     "premiseIds": ["p3", "p5"], "rule": "implication-elimination", "declarationRefs": [],
     "kernelStatus": "kernel-accepted", "axiomRefs": [],
     "explanation": {"text": "Then g (f value) : C, because g turns any proof of B into a proof of C.",
       "source": "structured-template", "template": "implies-elim/v0", "proofBased": true},
     "sourceSpan": {"file": "tests/reference/composition.ndjson", "refs": [{"expr": "ie14", "line": 28}]},
     "derivation": {"steps": ["s53"], "premises": ["s43", "s50", "s51", "s52"]}},
    {"stepId": "p7", "context": [],
     "conclusion": {"astRef": "s59/out", "pretty": "∀ {A B C : Prop}, (A → B) → (B → C) → A → C"},
     "termRef": "ie20", "termPretty": "fun {A B C} f g value ↦ g (f value)",
     "premiseIds": ["p1", "p2", "p3", "p4", "p6"], "rule": "discharge", "declarationRefs": [],
     "kernelStatus": "kernel-accepted", "axiomRefs": [],
     "explanation": {"text": "Discharging 4, 3, 2 and 1 gives ∀ {A B C : Prop}, (A → B) → (B → C) → A → C.",
       "source": "structured-template", "template": "discharge/v0", "proofBased": true},
     "sourceSpan": {"file": "tests/reference/composition.ndjson",
       "refs": [{"expr": "ie15", "line": 29}, {"expr": "ie16", "line": 30}, {"expr": "ie17", "line": 31},
         {"expr": "ie18", "line": 32}, {"expr": "ie19", "line": 33}, {"expr": "ie20", "line": 34}]},
     "derivation": {"steps": ["s54", "s55", "s56", "s57", "s58", "s59"]}},
    {"stepId": "p8", "context": [],
     "conclusion": {"astRef": "ie10", "pretty": "∀ {A B C : Prop}, (A → B) → (B → C) → A → C"},
     "termRef": "ie20", "termPretty": "fun {A B C} f g value ↦ g (f value)",
     "premiseIds": ["p7"], "rule": "statement-match", "declarationRefs": [],
     "kernelStatus": "kernel-accepted", "axiomRefs": [],
     "explanation": {"text": "This is the statement.", "source": "structured-template",
       "template": "statement/v0", "proofBased": true},
     "sourceSpan": {"file": "tests/reference/composition.ndjson",
       "refs": [{"expr": "ie10", "line": 23}, {"decl": "composition", "line": 35}]},
     "derivation": {"steps": ["s63"], "premises": ["s60", "s61", "s62"]}}
  ],
  "conclusion": {"steps": ["s64", "s65"], "published": {"slot": "d0", "outcome": "accepted"}}
}
```

`kernelStatus` is derived from the log and the environment (records with
outcome ok, declaration published accepted), never from a template or a
model. The golden files of 2.4.4 cover `composition`, `fixtureUse` (whose
`resolve` and `instantiate-levels` steps give `declarationRefs`
`["fixtureId"]`) and `identity`.

## Test plan

**1. Verdict identity, the acceptance test of 2.4.1.** Every randomized and
table-driven harness runs three ways — log `off`, log `terms` with ample
limits, and log `terms` with its limits swept from 0 up to what each case
needs, so that truncation happens at every possible step and at every
bound — and the results must be identical: outcome, result (type, reduct,
term indices), fuel left, the diagnostic's code and numbers, the
environment digests (slots, dependency lists, input region) and the store
counts and serials. Harnesses: `tests/support/checker-trial.fs` (8 trials
of 1,000 steps, whose `before-check` hook sets the mode), the interleaving
and jobs tests of `tests/core/contexts.fs`, `contexts-serial.fs` and
`environment-tasks.fs` (one context logging, one not, interleaved: the
strongest form), `tests/core/environment.fs`, the pinned-Lean
differentials (`mixed-infer`, `mixed-convert`, `mixed-beta`,
`mixed-instantiate`, `mixed-shift`, the level tables) and the first
checker's 60-row table once 2.2.3 exists. On Gforth 1.0 (threads), 0.7.3
(cooperative) and the serial host. A digest of the context's bytes
outside the log's own members, before and after each check, must match
between the off and on runs.

**2. The log itself.** A validator (Python, in `make test`) reads every log
the tests write and checks: steps numbered from 1; every `from` at or
below its step and sub-derivations nested; each rule's premises of the
kinds its catalogue entry says (an `application` has a function step, an
argument step, a `defeq` and an `instantiate`); every reference defined
(input numbers in range, copies before use); the end line consistent with
the steps (`complete` exactly when nothing was truncated). Golden logs and
outlines for `composition`, `identity` and `fixtureUse`. Unit tests reach
each bound (records, marks, both pools, copy work, an unreadable node)
and the observer's `THROW`.

**3. Cost while off** (measured below for one flag test; repeated on the
implementation with the full workload).

**4. Planted faults**, each of which the tests above must catch: a close
that drops or adds a stack cell; a close that returns another result; the
copier spending the checker's fuel; the copier allocating in the term
store instead of its pool; the log recording a diagnostic; a `lf-log?`
guard that skips the kernel word while logging or once truncated; a kernel
word that reads `log-active` to decide anything; `start` saved one step
late (premises shifted); a truncation not labelled; a log that keeps
recording after a bound (a gap in the premises); the writer printing an
identity stamp (caught by comparing serial, interleaved and job logs); the
copier walking on another module's walk record; the observer called inside
the publisher's `CATCH`.

**5. Replay** (L8): byte-identical logs for two runs, for serial against
interleaved and job runs, and for Gforth 1.0 against 0.7.3.

## Cost

**Measured while off**, 2026-11-02, this machine (12 logical cores, WSL2,
shared with other work: load average 4.6–5.8), in scratch copies of the
tree at `16bdc2f`; nothing in `src/` was changed. A context record with the
level cell (`context-record:`) and `lf-log? ( -- flag )`, which fetches it
through `lf-context`.

| Measurement | `gforth-fast` 1.0 | `gforth` 1.0 | `gforth` 0.7.3 |
| --- | --- | --- | --- |
| One `lf-log? if … then`, 10⁸ times, minus an empty loop (medians of 5) | 1.7 ns | 5.9 ns | 6.1 ns |
| The same test of a plain global variable | 0.26 ns | 2.2 ns | 2.4 ns |

On the fixed checker workload of the
[library notes](../development/FORTH_LIBRARY.md#design-per-task-contexts-and-how-modules-convert)
(composition, deep beta, deep inference, a level chain, the plain cases;
1,000 rounds), one test in `lf-minfer-in-frame` runs 139 times per round,
and tests at every site of L4 (inference visits and pass entries) 404
times: 404,000 tests, predicted at 0.7 ms on `gforth-fast` (0.1% of about
610 ms) and 2.4 ms on `gforth` (0.13% of about 1,800 ms). Seven interleaved
runs of each tree:

| Tree | `gforth-fast` median (range), ms | `gforth` median (range), ms |
| --- | --- | --- |
| unchanged | 608 (573–637) | 1,842 (1,701–1,885) |
| one test per inference visit | 615 (569–654) | 1,775 (1,684–1,848) |
| tests at every L4 site | 607 (587–710) | 1,815 (1,732–1,880) |

The differences are within the run-to-run noise; every run gave the same
result digest. A shared global flag would be about four times cheaper per
test, but both are negligible, and a per-context flag lets the
verdict-identity test run a logging and a non-logging context side by side.

**While on** (estimated, not measured): each record costs an open and a
close (a few dozen cell operations) plus copying the scratch it mentions,
which is at most proportional to the scratch the check built anyway. To be
measured on the implementation; the plan's profiling task (W3) records it.

## Consequences

- New: `src/core/derivation-log.fs` (state, protocol, copier, catalogue;
  [kernel] path, no-behaviour-change review),
  `src/present/derivation-ndjson.fs` (writer) and
  `src/present/proof-outline.fs` (2.4.4), the term printer's view and
  open-term printing, the catalogue and isolation checks, the validator,
  and a programming page for the log and its line formats.
- Kernel files gain one guarded branch per site (L4). The stack needs are
  re-measured with the log on.
- The declaration check of 2.2.3 opens its `declaration` record at its
  start and emits `proposition`; its golden log is the table above.
- Diagnostics are unchanged and stay the explanation of failures; the end
  line carries a copy.
- Plan §7.5 item 2 is met by L1 and L6; items 1 (side table) and 4–6
  (notation table, summariser, recognisers beyond λ/application) stay
  with tasks 2.4.2, 4.4.3 and 5.6.1.

## Rejected alternatives

- **An always-on log.** Every check would pay memory and time for a
  record few runs read. Off by default, chosen per run.
- **Extending the diagnostic record.** It keeps the first failure, by
  design; a derivation needs every success with its premises. The log
  reuses its patterns instead: one record per context, cleared at begin,
  never read by a check, a catalogue with stable numbers and a check that
  the docs match the code.
- **Carrying step numbers or a log handle on the data stack.** It changes
  every kernel word's stack effect and the per-level stack needs. The
  log's own mark stack holds them.
- **Numbering at the start of a rule (pre-order).** Conclusions would come
  before their premises, the reverse of how proofs read; post-order plus
  one `start` cell encodes the same tree.
- **An explicit premise list per record.** More memory and one more pool
  that can fill; `start` gives the list exactly.
- **References to scratch terms by index and identity only.** Scratch is
  rolled back and reused inside the check, so such references can only be
  detected as stale, never printed. Kept as level `steps`, which needs no
  copies, for audits that do not print formulas.
- **Postponing rollbacks while logging.** Scratch would stay alive, but
  the stores would fill sooner and a check could end *full* with the log
  on and *ok* with it off: a behaviour change.
- **Printing formulas as text inside the check.** The kernel would load
  presentation code, and printing switches tasks on the cooperative
  tasker (G-P2).
- **Rebuilding the formulas in the outline printer** by redoing shifts and
  substitutions. A second, untrusted implementation of kernel operations
  could print a formula the checker never computed; the copy is the one it
  did compute.
- **Recording after a bound by dropping only what does not fit.** Later
  records would name premises that are missing. Stopping at the first
  bound keeps a consistent prefix.
- **Writing the log to a file from inside the check.** Input and output in
  the check's path, failures that could reach a verdict, and task
  switches. The observer writes after the slot is final.
- **Comparing the log with Lean.** Lean's kernel writes out no
  derivation of the rules it applies, so there is no Lean log to compare
  with; the evidence is verdict identity, structural validation and
  golden files.

## Questions for the owner

Plain language, each with a recommendation; "agree" is enough.

- **D1. Off unless asked.** The notebook is off for an ordinary check and
  is switched on when you ask for a readable proof or an audit trail
  (`leanforth check --log`, `leanforth print`). *Recommendation: agree.*
  Ordinary checks stay as fast and small as they are; the measured cost of
  having the switch at all is too small to see.
- **D2. When the notebook runs out of room.** It stops, says "log
  incomplete at step N", the verdict stands, and no readable proof is
  printed for that declaration (it can be rerun with a larger log).
  *Recommendation: agree.* The other choices — abandoning the check, or
  growing memory without limit — would let the notebook change a verdict
  or exhaust the machine.
- **D3. Keep the intermediate formulas.** To print "Then f value : B" the
  notebook must keep a copy of each formula the checker builds, because
  the checker throws its working space away as it goes. That makes the
  notebook larger (about 150 KB of memory per worker while it is on, more
  for big proofs). *Recommendation: agree,* for readable proofs; a smaller
  "steps only" mode without formulas remains for audits.
- **D4. Short or detailed by default.** The printed proof of `composition`
  is 8 lines; the notebook has 65 steps. *Recommendation: print the short
  form by default, with every line naming the steps it covers, and show all
  steps with `--detail`.*
- **D5. Which review.** The notebook is written from inside the checker,
  but must not change any answer. *Recommendation: the checker's usual gate
  (AGENTS.md), with "nothing changed" as the evidence:* the verdict-identity
  tests above with the log off, on and full, the existing pinned-Lean
  comparisons rerun with the log on, an independent AI review of the exact
  change, and your approval of a short summary. Lean has no such notebook,
  so there is no Lean answer to compare it with.

## Reproduction

The cost measurement used three scratch copies of `git archive 16bdc2f
src tests/support`: one unchanged; one with the flag test in
`lf-minfer-in-frame` exactly as in L4 (the logged branch only counted a
hit); one that also wrapped `lf-mixed-beta`, `lf-mixed-instantiate`,
`lf-mixed-shift`, `lf-mixed-convert` and `lf-level-compare` as `lf-log? if
… else … then` around the renamed pass. Each loaded this module after
`src/lib/lib.fs`:

```forth
begin-structure /lf-log
  field: lf-log-level      \ 0 off; nonzero on
end-structure
/lf-log context-record: lf-log-state
: lf-log? ( -- flag ) lf-log-state lf-log-level @ ;
```

The loop timed 10⁸ iterations of `0 ?do loop`, of `0 ?do lf-log? if …
then loop` and of the same test on a global variable, with `utime`. The
workload is the `bench` file written for the library notes' measurement
(not in the repository; 1,000 rounds, run as `gforth src/main.fs
tests/support/plain-terms.fs tests/support/plain-cases.fs bench.fs` with
`1000 bench bye`), seven runs per tree interleaved, on `gforth` and
`gforth-fast` 1.0.0 from `.tools/gforth/bin`; the loop also on the
extracted Gforth 0.7.3. Switching the flag on in the main context and
counting hits gave the 139 and 404 tests per round. The Lean examples of
the user sketch were checked with the pinned `lean` 4.35.0 and
`-DwarningAsError=true`, and with `scripts/check-doc-examples.py --lean`.

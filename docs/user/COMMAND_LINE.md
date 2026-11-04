# The command line: `leanforth`

**Status, 2026-11-04: version 0, experimental** (plan tasks 3.4.1 to
3.4.3, and the command line's part of 6.5.2). `bin/leanforth` checks a
Lean export with LeanForth's first checker, which has not passed its
review gate (`AGENTS.md`) and has not been audited by an outside Lean
expert: every result it accepts is printed *accepted (experimental, not
independently audited)* with the axioms it depends on. Until the owner
approves the checker, Lean's own kernel is the referee. `check` takes
exports of any size: it stages the export with the importer stage and
feeds it to the checker, whose stores grow to fit, so a whole library is
checked from the command line — all of Lean's `Init`, 59,349
declarations, in [about ten minutes, four to five with `gforth-fast`](#a-whole-library-leans-init). Most
of a real library still ends *unsupported* or *unknown*, because
unfolding definitions (plan task 4.2.2), recursive data types and
literals (phase 5) are not built yet. Two commands keep the first,
small path —
`check --record` and `replay` hold 64 names, 64 levels, 64 term
nodes and 32 declarations per export ([small exports](#small-exports-check---record-and-replay)).

Every example on this page is run by `make test` (the shell and Forth
examples) and `make check` (the Lean ones), and must print exactly what is
shown; the `text` blocks are measured runs, shown as they were printed.

## Checking a Lean export

From the repository root:

```console
$ bin/leanforth check tests/reference/composition.ndjson
composition: accepted (experimental, not independently audited); axioms: none
1 declaration: 1 accepted
accepted: 1 (experimental, not independently audited); axioms: none
```

`check` reads the export with LeanForth's own reader, written in Forth;
no Python or Lean runs. It checks the export against its *manifest*,
`tests/reference/composition.ndjson.manifest.json`, which LeanForth's
export step wrote beside it (see [Manifests](#manifests)), while it
stages it into the importer's compact store
([staging](../development/NDJSON_READER.md#staging-into-the-compact-store)),
and hands the staged declarations to the checker in file order
([feeding the checker](../development/NDJSON_READER.md#feeding-the-checker)).
Then it checks every declaration in file order, each with the same
checker and rules as [the first check](FIRST_CHECK.md) — and an inductive
type's declarations together, as [one block](../programming/INDUCTIVE_BLOCKS.md)
— and prints one line per declaration with its verdict, then a summary.

## The example in three forms

**Mathematics.** For all propositions *A*, *B*, *C*: if *A* implies *B*
and *B* implies *C*, then *A* implies *C*,

$$\forall A\, B\, C : \mathrm{Prop},\ (A \to B) \to (B \to C) \to A \to C,$$

proved by $\lambda f\, g\, a.\ g\,(f\,a)$. It uses no axiom.

**LeanForth Forth.** The command line is a thin wrapper: `bin/leanforth`
runs `src/main.fs` and its word `cli-main`. The same check from a Forth
session is one word, `cli-check ( c-addr u -- code )`, which prints what
the command prints and leaves the exit code. `cli-options` restores the
defaults (manifest checked, fuel 100,000 per declaration):

```forth
cli-options
```

```forth
s" tests/reference/composition.ndjson" cli-check .
```

```text
composition: accepted (experimental, not independently audited); axioms: none
1 declaration: 1 accepted
accepted: 1 (experimental, not independently audited); axioms: none
0
```

**Lean.** Lean 4.35.0 accepts the same theorem and lists its axioms:

```lean
theorem composition {A B C : Prop} (f : A → B) (g : B → C) : A → C :=
  fun value => g (f value)
#print axioms composition
```

```text
'composition' does not depend on any axioms
```

## Commands

| Command | What it does |
| --- | --- |
| `check [--no-manifest] [--fuel N] [--resources] [--json] EXPORT` | Check every declaration of a Lean export of any size, in file order; with `--resources`, also print the [resource report](#the-resource-report); with `--json`, print [one JSON report](#json-output) instead of text |
| `check [--no-manifest] [--fuel N] --record RECORD EXPORT` | Check a small export (as `print` reads it) and also write its [run record](#run-records-and-replay) |
| `replay [--no-manifest] [--fuel N] EXPORT RECORD` | Check the export again and compare the new run record with RECORD; print the replay report |
| `print [--no-manifest] [--fuel N] [--detail] [--name NAME] [--latex] [--statement FORMS] EXPORT` | Check the export and print each accepted declaration's [readable proof](#printing-a-readable-proof), or with `--detail` every step of the checker's log; `--name` prints one declaration |
| `count [--no-manifest] EXPORT` | Count the export's records by kind ([the reader's counter](../development/NDJSON_READER.md#using-it)), for exports of any size |
| `reexport [--no-manifest] EXPORT COPY` | Write the export again into COPY, byte for byte as Lean's exporter writes it ([re-export](../development/NDJSON_READER.md#re-export)); after an error COPY is incomplete and must be discarded |
| `version` (or `--version`) | Versions of LeanForth, its Forth host, the export format it reads, and the git commit |
| `capabilities` | What this build supports, what it does not, and its limits |
| `help` (or `--help`, `-h`) | The usage text |

Options:

- `--no-manifest` reads the export without checking its manifest. It is
  an explicit choice, and `check`, `count` and `reexport` say so in their
  first line.
- `--fuel N` gives each declaration's check N steps (default 100,000). A
  check that runs out ends *exhausted*. N is decimal digits, at most
  2^53 − 1 = 9,007,199,254,740,991, the largest integer every JSON reader
  holds exactly, so that reports and run records hold it; a larger N is a
  command-line mistake (status 4).
- `--record RECORD` writes the run record of the check to RECORD
  ([run records and replay](#run-records-and-replay)); RECORD must not be
  the export. Run records 0.1 hold at most 32 declarations, so `check
  --record` reads the export straight into the checker's default
  sizes ([small exports](#small-exports-check---record-and-replay)).
- `--resources` (`check` only) adds the [resource report](#the-resource-report)
  after the summary: time, memory, the input's size and fuel.
- `--json` (`check` only) prints the whole result as one
  [JSON report](#json-output) instead of text. Neither goes with
  `--record` (status 4).
- `--detail` (`print` only) prints every step of the checker's log
  instead of the outline; `--name NAME` (`print` only) prints only the
  declaration named NAME.

`EXPORT` and `COPY` are file names relative to the current folder; the
tool works from any folder, and gives the same bytes on every run:

```console
$ cd tests && ../bin/leanforth check reference/composition.ndjson
composition: accepted (experimental, not independently audited); axioms: none
1 declaration: 1 accepted
accepted: 1 (experimental, not independently audited); axioms: none
```

## What `check` prints

One line per declaration: its name, a colon and its verdict, read from
the declaration's published slot in the checked environment. An accepted
declaration always reads `accepted (experimental, not independently
audited); axioms: …`, with the axioms its slot records (always `none`
today: the first checker accepts no axiom). Any other verdict is one of
the [outcomes](CONCEPTS.md#outcomes): *rejected*, *unknown*,
*unsupported*, *invalid*, *exhausted* or *full*, followed by an indented
line with the first reason the checker recorded: the reason's name, its
[diagnostic code](../programming/DIAGNOSTICS.md), the place in the checker
and two numbers that the catalogue explains. Then the summary: a line
that counts the verdicts, and, when anything was accepted, one that
repeats the label and the axioms of the accepted declarations; then notes
explain a limit that was reached.

**Names.** A declaration's name is shown as Lean's `Name.toString` shows
it (`src/cli/name-text.fs`): its components joined by dots, numeric ones
in decimal, a component that is not an identifier between `«` and `»`
(`ReexportKinds.«with space»`; an empty component is `«»`), and the
anonymous name as `[anonymous]`; names of any depth. Two changes make the
line show exactly what the name holds, so that no name, however crafted,
can start a line of its own, move the cursor or reorder the text after
it: inside a component that is not an identifier, a backslash is shown
as `\\`, and every character the [text rule of run
records](../programming/RUN_RECORDS.md) bans — control characters (C0
and C1, line feed and carriage return among them), format characters
such as the bidirectional controls, and the line and paragraph separators
— as `\u{X}`, its code point in hexadecimal; a byte that does not start
UTF-8 as `\x{X}`. A theorem named `composition: rejected` + line feed +
`forged: accepted …` is one line,
`«composition: rejected\u{A}forged: accepted …»: accepted …`. As in Lean,
no `«»` is added to a component that holds `»`, or to a name with macro
scopes (`x._@._hyg`), an inaccessible name or pseudo-syntax; the escapes
are made all the same. The JSON report holds the same text, and its
`export` member shows the export's file name with the same escapes.

**Axioms and NOT PROVED.** The axioms are read from each accepted
declaration's slot: the axiom set the checker joined from everything the
declaration uses. The first checker refuses every axiom (*unsupported*,
rule U1), and with it everything that uses one, so today the set is
always empty and the summary says `axioms: none`. Under the owner's rule,
an accepted declaration that depends on an axiom other than `propext`,
`Classical.choice` and `Quot.sound` gets Lean's verdict and is marked
`NOT PROVED` on its line and counted apart in the summary (`axioms: N NOT
PROVED`), never as proved; until axioms are supported (plan tasks 5.3.1
and 5.3.2, which also bring the axioms' names) any axiom counts, and none
can appear yet. When every declaration is accepted but some are NOT
PROVED, the exit status is 6, not 0 ([exit status](#exit-status); proposed,
pending the owner's confirmation).

A broken copy of `composition`, whose proof applies `g` to `value`
instead of to `f value`, is rejected for the reason Lean's kernel gives
(rule D3 of [ADR 0011](../adr/0011-definite-rejection.md): the argument
has type `A`, `g` needs a `B`). The copy has no manifest, so it is read
with `--no-manifest`:

```console
$ bin/leanforth check --no-manifest tests/core/check-declaration-cases/composition-wrong-argument.ndjson; echo "exit status $?"
note: the export's manifest is not checked (--no-manifest)
composition: rejected
  rejected: argument type mismatch (D1-D5); diagnostic 59 at mixed-infer lf-mixed-infer: 4 0
1 declaration: 1 rejected
exit status 1
```

A file whose declarations end differently counts each verdict:

```console
$ bin/leanforth check tests/cli/unfold.ndjson; echo "exit status $?"
Implies: accepted (experimental, not independently audited); axioms: none
impliesSelf: unknown
  undecided: terms or levels differ; diagnostic 30 at mixed-convert lf-mixed-convert: 17 10
2 declarations: 1 accepted, 1 unknown
accepted: 1 (experimental, not independently audited); axioms: none
exit status 2
```

Here *unknown* is honest, not a rejection, and it is a gap, not a
difference from Lean: the proof is correct, and Lean accepts it, but
checking it needs the definition of `Implies` unfolded, which the first
checker does not do yet (plan task 4.2.2 closes it):

```lean
def Implies (A B : Prop) : Prop := A → B

theorem impliesSelf {A : Prop} : Implies A A := fun a => a

#print axioms impliesSelf
```

```text
'impliesSelf' does not depend on any axioms
```

### An inductive type

An inductive type is a block of declarations — the type, its
constructors and its recursor — checked together by the first member's
check, as Lean's kernel adds them together ([inductive blocks](../programming/INDUCTIVE_BLOCKS.md),
plan task 5.2.1a: blocks that are not recursive, indexed or mutual). Each
member gets the block's verdict. `tests/cli/inductive.lean` declares a
type with two values, proves a theorem with its recursor and defines a
function with it:

```lean
inductive Two where
  | first
  | second

theorem Two.cases (motive : Two → Prop) (a : motive Two.first) (b : motive Two.second)
    (t : Two) : motive t :=
  Two.rec a b t

noncomputable def Two.swap (t : Two) : Two :=
  Two.rec (motive := fun _ => Two) Two.second Two.first t

#print axioms Two.cases
```

```text
'Two.cases' does not depend on any axioms
```

```console
$ bin/leanforth check tests/cli/inductive.ndjson; echo "exit status $?"
Two: accepted (experimental, not independently audited); axioms: none
Two.first: accepted (experimental, not independently audited); axioms: none
Two.second: accepted (experimental, not independently audited); axioms: none
Two.rec: accepted (experimental, not independently audited); axioms: none
Two.cases: accepted (experimental, not independently audited); axioms: none
Two.swap: accepted (experimental, not independently audited); axioms: none
6 declarations: 6 accepted
accepted: 6 (experimental, not independently audited); axioms: none
exit status 0
```

In mathematics: a set *T* = {first, second} and, for every property *P*
of its elements, *P*(first) ∧ *P*(second) → ∀ *t* ∈ *T*, *P*(*t*), proved
by cases; and the map swap: *T* → *T* that exchanges the two values,
defined by cases (`noncomputable` because Lean's compiler does not compile
a recursor; Lean's kernel checks it all the same). In LeanForth's Forth,
the same check is
`s" tests/cli/inductive.ndjson" cli-check`, which prints the lines above
and leaves 0. An export that uses every kind of record Lean writes,
`tests/core/reexport/kinds.ndjson`, shows the mix a real library gives
today: blocks such as `Prod`, `Eq` and `Iff`, and recursive types such
as `Nat` and `List` (plan task 5.2.1b), are accepted; mutual and nested
types, literals, projections, axioms, opaque declarations, quotients and
what uses them are not yet:

```console
$ bin/leanforth check --no-manifest tests/core/reexport/kinds.ndjson | tail -n 2; echo "exit status ${PIPESTATUS[0]}"
106 declarations: 58 accepted, 5 unknown, 43 unsupported
accepted: 58 (experimental, not independently audited); axioms: none
exit status 2
```

### A whole library: Lean's `Init`

`check` holds an export of any size: the importer stage reads it once,
with its manifest, into a compact store, and the checker's stores grow to
take the staged declarations. Lean's own `Init` library, exported with
`scripts/export.sh` (345.7 MB, 59,349 declarations), checked on
2026-11-04 with the default fuel:

```text
$ GFORTH=.tools/gforth/bin/gforth-fast bin/leanforth check --resources init.ndjson | tail -n 28
59349 declarations: 1618 accepted, 3748 unknown, 53800 unsupported, 179 exhausted, 4 full
accepted: 1618 (experimental, not independently audited); axioms: none
note: a check ran out of room; its diagnostic names the limit: memory, or
note: 16 dependencies per declaration, 65536 per export, 512 constructors per
note: inductive block (plan task 6.2.0)
note: a check ran out of fuel (100000 steps each); --fuel N gives each more
resources:
  time (s)     wall      cpu
  stage      18.869   18.869
  feed       18.717   18.426
  check     220.083  220.045
  total     258.063  257.733
  memory: peak resident 1218.1 MB; the stage's heap blocks 179.4 MB
  input: 59349 declarations, 6099054 term nodes, 578 levels, 56957 constant references, 295432 names
  fuel: 26769240 steps in all, at most 100000 per declaration
  fuel not known for 30023 declarations: a failed inference gives its
    counter up (their checks are not in the fuel above)
  most fuel used:
    100000 Lean.Omega.Constraint.add_sat (exhausted)
    100000 ByteArray.utf8Decode?.go._unary.eq_def (exhausted)
    100000 String.Slice.Pos.copy_eq_append_get (exhausted)
    100000 Array.map_attach_eq_pmap (exhausted)
    100000 Std.IterM.step_filterMapM (exhausted)
    100000 Std.IterM.toList_filterMapM_map (exhausted)
    100000 Std.Iter.forIn'_eq_match_step (exhausted)
    100000 Std.IterM.step_filterMap (exhausted)
    100000 Std.IterM.toList_filterMap (exhausted)
    100000 Std.IterM.forIn_filterMapWithPostcondition (exhausted)
```

Nothing was rejected and nothing was invalid. The 1,618 accepted
declarations include `id`, `Function.comp` and whole inductive blocks
such as `Bool`, `Option`, `Prod`, `Sum`, `And`, `Or`, `Exists`, `Eq`,
`HEq` and `Decidable`. Almost everything else is *unsupported* or
*unknown* because it needs features not built yet — each a gap to close,
not an answer that differs from Lean's, which accepts all of `Init`:
recursive and indexed inductive types such as `Nat` and `List` (plan
tasks 5.2.1b, 5.2.1c; 266 declarations), literals, projections and other
term forms (5.2.3, 5.2.2, 4.2.3; 25,703 declarations), axioms, opaque,
unsafe and partial declarations and quotients (5.3.1, 4.2.6, 5.2.4; 252),
comparisons that need definitions unfolded (4.2.2; 749 *unknown*, codes
30–32), and everything that uses
one of those (27,579 *unsupported* and 2,999 *unknown* only for that).
*full* means a declaration with more than 16 dependencies (4, such as
`Sum.isRight_iff`; plan task 6.2.0), and *exhausted* a check that needed
more than 100,000 steps (179; `--fuel N` gives more). No term is too
deep any more: since the depth work of plan task 6.2.0 (part (b)) the
55 declarations that ended *full* at a walk's 64 levels in the first run
of 2026-11-04 get other verdicts (33 *unsupported*, 17 *exhausted*, 4
*unknown*, 1 accepted), and two that use one of them moved from
*unknown* to *unsupported*. 183 names, most of them notations such as
`«term_+_»`, are shown with `«»`, as Lean shows them.

The run above used the `gforth-fast` engine
(`GFORTH=.tools/gforth/bin/gforth-fast`) on a 10-core WSL2 machine that
other agents' test runs shared. The default `gforth` engine gives the
same output, byte for byte but for the times, in about two and a half
times as long (9 min 59 s for an earlier build on 2026-11-04). Freeing
the stage's export-index maps once it is staged gives back 35.7 MB of
its 215.1 MB; on three runs of this build, the same verdicts, fuel and
diagnostics for every declaration, the peak was 1,263 MB without it and
1,218 MB with it (peaks vary by about 20 MB from run to run). The ten
declarations that used the most fuel all ran out of it; among the
accepted ones the most was 48,291 steps (a `match` auxiliary of
`Sum.exists`). Half the declarations' fuel is not known: their check
failed inside inference, which gives its counter up, so neither the
total nor the list counts them ([fuel](#the-resource-report)); a later
step of plan task 6.5.2 can keep it, with a change to the checker.

### The resource report

`--resources` adds a report after the summary (plan task 6.5.2, the
command line's part): the wall and CPU time of each phase — staging,
feeding, checking — and of the whole run so far, in seconds; the
process's peak resident memory (`VmHWM` in `/proc/self/status`; on a host
without it, `not measured on this host`) and the bytes of heap blocks the
stage holds while the checks run (its export-index maps, which only
loading needs, are freed once it is staged: `stage-unmap`); the size of the input as fed (declarations, term nodes,
levels, constant references, names); the fuel all checks used; and the
ten declarations that used the most, most first, those of equal fuel in
file order. Times and memory differ from run to run; everything else is
the same on every run, as in this example, where the time and memory
lines are left out:

```console
$ bin/leanforth check --resources tests/cli/inductive.ndjson | grep -v -E "^  (stage|feed|check|total) |^  memory: "
Two: accepted (experimental, not independently audited); axioms: none
Two.first: accepted (experimental, not independently audited); axioms: none
Two.second: accepted (experimental, not independently audited); axioms: none
Two.rec: accepted (experimental, not independently audited); axioms: none
Two.cases: accepted (experimental, not independently audited); axioms: none
Two.swap: accepted (experimental, not independently audited); axioms: none
6 declarations: 6 accepted
accepted: 6 (experimental, not independently audited); axioms: none
resources:
  time (s)     wall      cpu
  input: 6 declarations, 46 term nodes, 3 levels, 5 constant references, 31 names
  fuel: 1520 steps in all, at most 100000 per declaration
  most fuel used:
       832 Two.cases (accepted)
       349 Two.swap (accepted)
       339 Two (accepted)
```

**Fuel**, a check's unit of work, is read from the checker's own counters
after each check. For an accepted declaration it is exact: with a budget
of exactly that much (`--fuel N`) it is accepted, with one less it is not
(`make test` checks this on the fixtures). An exhausted check used the
whole budget. The block's fuel is counted on its first member (`Two`
above); its other members show none of their own. A check that failed
inside inference gives its counter up (the checker sets it to zero), so
its fuel is *not known*: the report counts those declarations apart and
leaves them out of the total and the list. The report reads the counters
only; nothing it prints is fed back into a check.

### JSON output

`--json` prints the whole result as one JSON text, then a line feed, in
the format `leanforth-check-report`, version 0.1
([`schemas/check-report-0.1.schema.json`](../../schemas/check-report-0.1.schema.json),
JSON Schema draft 2020-12 within the subset of
[`tests/support/schema_subset.py`](../../tests/support/schema_subset.py)).
It holds what the text holds and the resource report, with the times and
memory apart in `measured`; every other member is the same on every run
of the same export with the same options and build. Here the `measured`
member is cut off:

```console
$ bin/leanforth check --json tests/cli/unfold.ndjson | sed "s/,\"measured\":.*/}/"; echo "exit status ${PIPESTATUS[0]}"
{"schema":"leanforth-check-report","schemaVersion":"0.1","export":"tests/cli/unfold.ndjson","manifest":"checked","label":"experimental, not independently audited","settings":{"fuel":100000,"dependencyPool":65536},"read":{"outcome":"ok","phase":null,"line":null,"field":null,"reason":null,"at":null},"run":"ok","stopped":false,"declarations":[{"index":0,"name":"Implies","verdict":"accepted","label":"experimental, not independently audited","axiomBits":0,"notProved":false,"fuel":137},{"index":1,"name":"impliesSelf","verdict":"unknown","diagnostic":{"code":30,"reason":"undecided: terms or levels differ","site":"mixed-convert lf-mixed-convert","numbers":[17,10],"step":8},"fuel":281}],"counts":{"declarations":2,"accepted":1,"rejected":0,"unknown":1,"unsupported":0,"invalid":0,"exhausted":0,"full":0,"notChecked":0,"notProved":0},"fuel":{"perDeclaration":100000,"total":418,"unknown":0,"top":[{"index":1,"name":"impliesSelf","fuel":281,"verdict":"unknown"},{"index":0,"name":"Implies","fuel":137,"verdict":"accepted"}]},"input":{"declarations":2,"terms":14,"levels":1,"references":1,"names":10},"exitStatus":2}
exit status 2
```

| Member | Contents |
| --- | --- |
| `schema`, `schemaVersion` | `leanforth-check-report`, `0.1` |
| `export`, `manifest` | the file name given, with the escapes of [names](#what-check-prints); `checked`, or `not-checked` with `--no-manifest` |
| `label` | `experimental, not independently audited` |
| `settings` | the fuel per check and `dependencyPool`, the room the environment's dependency pool starts with (it grows: not a limit since plan task 6.2.0) |
| `read` | the read's outcome and, for a failure, its `phase` (`open`, `stage`, `feed`), `line`, `field`, `reason`, and for the feed the number `at` which it stopped |
| `run` | the run's outcome: `ok` when every slot ended final and the run did not stop, `invalid` when it stopped, `not-run` when the export was not read |
| `stopped` | true when the run stopped on an internal fault (a check threw, or publishing failed), as the text's `internal fault: the run stopped` line says; the run is then `invalid` and the status 5 |
| `declarations` | each declaration in file order: `index`, `name` (as the text shows it), `verdict` (`accepted`, an outcome, or `not-checked`), `fuel` (null when not known); an accepted one's `label`, `axiomBits` (0: none) and `notProved`; any other's `diagnostic` (code, reason, site, two numbers, step) |
| `counts` | the declarations by verdict, `notChecked` and `notProved`; null when no verdict could be read |
| `fuel` | `perDeclaration`, `total` (of the known), `unknown` (how many are not known) and `top` (the ten that used the most) |
| `input` | declarations, term nodes, levels and constant references fed, and the stage's names; null when nothing was fed |
| `exitStatus` | the command's [exit status](#exit-status), 0 to 6 |
| `measured` | `microseconds` (wall and CPU of `stage`, `feed`, `check` and `total`; null on a host without clocks), `peakResidentBytes` and `stageBytes` (null when not known) |

The parts of a report agree, and the schema states what its keywords
can: status 0 only for a run that ended `ok`, did not stop and listed at
least one declaration, every one accepted and proved, with every other
count 0 and every fuel known; status 6 only when every declaration was
accepted and at least one is NOT PROVED; a rejected or invalid
declaration, or one not checked, never leaves the status 0. What it
cannot state, `make test` checks on every report it makes (the schema's
`$comment` lists it): `counts.declarations` is the number of
`declarations` and the sum of the eight verdict counts, each count the
number of declarations with that verdict, `notProved` the number marked
so, and `input.declarations` the same number; `fuel.unknown` is the
number of declarations whose fuel is null and `fuel.total` the sum of
the others'; `fuel.top` is in order of fuel, most first, each entry the
name, fuel and verdict of the declaration at its index.

The report is written out as it is made, one declaration after another
(`Init`'s is 13.8 MB, and the schema accepts it). The exit status is the
same as without `--json`. A report is untrusted
output, not a [run record](#run-records-and-replay): it names no commit
and no SHA-256, and nothing reads it back into a check. A command-line
mistake is still reported as text (status 4), and an internal fault
(status 5) can leave a report cut short: read the report only when the
status is 0 to 4 or 6. The format has not passed the owner's [format] gate.

## Printing a readable proof

`print` checks the export as `check` does (staged and fed to the checker,
so any size: it prints a chosen theorem of Lean's `Init` as well as a
fixture), one declaration at a
time with the checker's [derivation log](../programming/DERIVATION_LOG.md)
on, and prints each declaration right after its check: the verdict with
its label and axioms, the statement, and a short readable proof (the
[proof outline](PROOF_OUTLINE.md)) whose every line names the checker
steps it covers. The formulas and step numbers come from the checker's
log; the English sentences are fixed templates, labelled
`structured-template` at the end:

```console
$ bin/leanforth print tests/reference/composition.ndjson; echo "exit status $?"
Theorem composition
  accepted (experimental, not independently audited); axioms: none
  Statement in Lean:        ∀ {A B C : Prop}, (A → B) → (B → C) → A → C
  Statement in mathematics: $\forall \{A\ B\ C : \mathrm{Prop}\},\ (A \to B) \to (B \to C) \to A \to C$
  Statement in LeanForth (the statement only, written as an axiom; nothing is assumed):
    axiom composition
      Prop implicit: A
      Prop implicit: B
      Prop implicit: C
      A B -> explicit: f
      B C -> explicit: g
      A C ->
    end composition
  Input:     tests/reference/composition.ndjson line 35
  Checker log: 51 steps, complete. The statement is a proposition: s20 (from s3).

Proof (reconstructed from the proof term).
  1  Let A, B, C be propositions.                  [∀-introduction]                   s21–s23
  2  Assume f : A → B.                             [assumption]                       s26
  3  Assume g : B → C.                             [assumption]                       s29
  4  Assume value : A.                             [assumption]                       s30
  5    Then f value : B,                           [→-elimination ← 2, 4]             s36
         because f turns any proof of A into a proof of B.
  6    Then g (f value) : C,                       [→-elimination ← 3, 5]             s39
         because g turns any proof of B into a proof of C.
  7  Discharging 4, 3, 2 and 1 gives               [→/∀-introduction ← 1, 2, 3, 4, 6] s40–s45
       ∀ {A B C : Prop}, (A → B) → (B → C) → A → C.
  8  This is the statement.                        [definitional equality ← 7]        s49
∎
Rules, formulas and step numbers come from the checker's log; the sentences are
fixed templates (structured-template), not checked reasoning.
Templates: let-props/v0, assume/v0, implies-elim/v0, discharge/v0, statement/v0.

exit status 0
```

The header shows the statement in three forms (plan task 8.6.2): in
Lean's notation, in mathematics (LaTeX between `$` and `$`) and in
LeanForth words. The LeanForth block states the type as the `axiom` of
the same name does, because that is the one form of the words that states
a type with no proof; it assumes nothing: nobody checked such an axiom,
and the verdict printed above it is the checker's. The words run through
the [authoring words](../programming/LEANFORTH_WORDS.md) to the identical
statement (checked by `tests/present/check_outline.py` for every pinned
example). The statement is printed whether or not the declaration was
accepted. A block can be run only after the declarations it mentions: the
constants of an earlier declaration are defined by running that
declaration first (an `import-stub` line stands for one of Lean's).

`--statement FORMS` chooses the forms: `lean`, `mathematics` and
`leanforth`, joined by commas (`--statement lean,leanforth`), or `all`
(the default). `--latex` prints the outlines as LaTeX fragments instead
(see [the proof outline](PROOF_OUTLINE.md#latex)); with `--detail` the
step list is always plain text.

`--name NAME` prints only the declaration named NAME (the declarations
before it are checked too, since it may use them; the ones after it are
not); `--detail` prints every step of the log instead of the outline.
No outline is ever printed for a declaration that was not accepted, nor
from a log that ran out of room; the printer says why, and the exit status
says what happened:

```console
$ bin/leanforth print --no-manifest tests/core/check-declaration-cases/composition-wrong-argument.ndjson; echo "exit status $?"
note: the export's manifest is not checked (--no-manifest)
Theorem composition
  rejected
  Diagnostic: rejected: argument type mismatch (D1-D5) (4, 0)
  Statement in Lean:        ∀ {A B C : Prop}, (A → B) → (B → C) → A → C
  Statement in mathematics: $\forall \{A\ B\ C : \mathrm{Prop}\},\ (A \to B) \to (B \to C) \to A \to C$
  Statement in LeanForth (the statement only, written as an axiom; nothing is assumed):
    axiom composition
      Prop implicit: A
      Prop implicit: B
      Prop implicit: C
      A B -> explicit: f
      B C -> explicit: g
      A C ->
    end composition
  Input:     tests/core/check-declaration-cases/composition-wrong-argument.ndjson line 35
  Checker log: 51 steps, complete. The statement is a proposition: s20 (from s3).

No proof outline: the declaration was not accepted.

exit status 1
$ bin/leanforth print --name fixtureUse tests/reference/constant-fixture.ndjson | head -3
Theorem fixtureUse
  accepted (experimental, not independently audited); axioms: none
  Statement in Lean:        ∀ {P : Prop}, P → P
$ bin/leanforth print --name noSuch tests/reference/constant-fixture.ndjson; echo "exit status $?"
error: no declaration named noSuch
exit status 4
```

Exit status of `print`: the status `check` gives, from the
[verdicts](#exit-status) of the declarations printed — 0 when every one is
accepted, whether or not its outline could be printed (an accepted
declaration whose log ran out of room says `No proof outline: the
declaration is accepted, but the checker's log was truncated at step N
(...)`; no status is free to tell that apart, so the text does) — 4 for a
name no declaration has, and 5 when the run stopped (a check threw,
publishing failed, or the printer itself threw; the log is switched off
and the checked environment freed all the same). The outline is
untrusted presentation: the verdict comes from the checked environment,
as `check`'s does, and nothing `print` writes can make a declaration
accepted.

Two things can differ from `check`. A diagnostic's two numbers that are
identities or serials (codes 8, 21, 25 and 27) can differ for a later
declaration, because printing an outline builds and discards scratch
terms between checks and so advances the serials; the verdicts do not
change. And with `--no-manifest` the export is read twice (once to check,
once for binder names), so if the file changes in between, binder names
(only names) can come from the newer bytes; with the manifest checked,
both reads check it.

## Exit status

| Status | Meaning | Comes from |
| --- | --- | --- |
| 0 | Every declaration accepted (or, for the other commands, done) | every verdict *ok* |
| 1 | Something rejected: Lean's kernel rejects it too | *rejected* |
| 2 | Unsupported or unknown: LeanForth cannot decide it yet | *unsupported*, *unknown* |
| 3 | A resource limit: out of fuel or out of room | *exhausted*, *full* |
| 4 | Malformed input: a broken export, a missing or wrong manifest, a file that cannot be opened or created, or a malformed command line | *invalid* |
| 5 | An internal fault: a Forth exception, a check that threw, a failed publication, or Gforth ending in an unexpected way | — |
| 6 | Every declaration accepted, but some NOT PROVED: they depend on an axiom (proposed; see below) | *ok* with an axiom |

When the declarations end differently, the most severe status wins, in
the order 5, 4, 1, 3, 2, 6, 0: an internal fault or a malformed export puts
every verdict in doubt; a rejection is Lean's definite "no"; a limit or a
missing feature leaves a declaration undecided; a NOT PROVED declaration
is Lean's "yes" resting on an axiom. Only status 0 means every
declaration was accepted and proved. Status 6 follows the owner's rule
that NOT PROVED "has its own exit code and never counts as proved"
([owner decisions](../project/OWNER_DECISIONS.md)); its number and its
place in the order are proposed, pending the owner's confirmation at the
check report's [format] gate. No declaration can be NOT PROVED yet (the
first checker accepts no axiom), so `make test` reaches status 6 by
planting an axiom in an accepted slot. One example of each status other
than 0 and 6:

```console
$ bin/leanforth check --no-manifest tests/core/check-declaration-cases/composition-postulate.ndjson; echo "exit status $?"
note: the export's manifest is not checked (--no-manifest)
composition: unsupported
  unsupported: declaration kind (U1); diagnostic 42 at check-declaration lf-check-declaration: 3 0
1 declaration: 1 unsupported
exit status 2
$ bin/leanforth check --fuel 30 tests/reference/composition.ndjson; echo "exit status $?"
composition: exhausted
  fuel exhausted; diagnostic 1 at check-declaration lf-check-declaration: 0 0
1 declaration: 1 exhausted
note: a check ran out of fuel (30 steps each); --fuel N gives each more
exit status 3
$ bin/leanforth check --no-manifest tests/core/check-declaration-cases/composition-loose.ndjson; echo "exit status $?"
note: the export's manifest is not checked (--no-manifest)
composition: invalid
  invalid input: out of scope; diagnostic 23 at constant-term-scope lf-constant-term-scope: 7 6
1 declaration: 1 invalid
exit status 4
$ bin/leanforth check --fule 30 tests/reference/composition.ndjson; echo "exit status $?"
error: an unknown option: --fule
try: leanforth help
exit status 4
$ GFORTH=false bin/leanforth check tests/reference/composition.ndjson; echo "exit status $?"
leanforth: internal fault: Gforth ended with status 1
exit status 5
```

The Forth entry point leaves Gforth with status 100 plus the code, and
`bin/leanforth` turns that back into the code. Any other status — Gforth
failing on its own, as `false` does above, or a crash — is an internal
fault, never a verdict. A Forth exception inside the tool is caught and
reported the same way (`internal fault: a Forth exception (THROW n)`);
`make test` injects one while an export is fed to the checker and one
inside a check, and checks that the stage is freed either way.

A check that throws *spends* its checker context for good
([ADR 0012](../adr/0012-checked-environment.md), G-P6): the run stops,
its declaration is *invalid* (diagnostic 29) and the ones after it are
`not checked`, and every later check in that context also ends *invalid*
with diagnostic 29. `bin/leanforth` runs one command per process, so this
matters only in a Forth session, which runs its next command in a new
context (`context-new`, `context-use`). It fails closed: nothing is ever
accepted in a spent context.

## Small exports: `check --record` and `replay`

Run records 0.1 hold at most 32 declarations, so these two commands
keep the first path: the export read straight into the checker's stores
at their default sizes, 64 names, 64 levels and 64 term nodes — the
export's own and each check's working terms together — and 32
declarations, with inductive types refused while reading. The fixtures
fit. `tests/cli/chain.lean` chains twelve implications (Lean accepts it,
without axioms); its export has 81 expression records, so `check` accepts
it and `check --record` does not hold it:

```console
$ bin/leanforth check tests/cli/chain.ndjson; echo "exit status $?"
chain: accepted (experimental, not independently audited); axioms: none
1 declaration: 1 accepted
accepted: 1 (experimental, not independently audited); axioms: none
exit status 0
$ bin/leanforth check --record /dev/null tests/cli/chain.ndjson; echo "exit status $?"
error: full: too many expression nodes or constant references for the check's stores (line 97)
note: check --record and replay hold at most 64 names, 64 levels,
note: 64 term nodes and 32 declarations per export; check without --record holds any size
exit status 3
$ bin/leanforth check --no-manifest --record /dev/null tests/core/reexport/kinds.ndjson; echo "exit status $?"
note: the export's manifest is not checked (--no-manifest)
error: unsupported: an inductive type (not supported yet) (line 51)
exit status 2
```

Nothing is checked then: the export did not fit, so no verdict is given.
`count` and `reexport` have no such limit; they read all of Mathlib.
`capabilities` lists every limit and every unsupported feature, each with
the plan task that lifts it:

```console
$ bin/leanforth capabilities
leanforth 0.1.0-dev: what this build can do
supported:
  check: Lean 4.35.0 exports (lean4export 3.1.0 NDJSON) of any size, such as
    all of Lean's Init, staged and fed in Forth; the manifest checked unless
    --no-manifest; a summary, --resources (time, memory, fuel), --json
  check: definitions and theorems built from Sort, variables, application, fun,
    forall and earlier accepted declarations (the first checker, ADR 0011),
    and inductive blocks that are not recursive, indexed or mutual (5.2.1a);
    an accepted one is labelled experimental, not independently audited
  check --record, replay: run records 0.1 and their replay (plan task 2.2.5)
  print: a readable proof outline of each accepted declaration, from the
    checker's derivation log (plan tasks 2.4.1, 2.4.4; untrusted presentation)
  count, reexport: exports of any size, up to all of Mathlib
not yet supported (check answers unsupported or unknown, exit 2):
  axioms (5.3.1), opaque declarations (4.2.6), unsafe and partial definitions;
  let (4.2.3), literals (5.2.3), projections (5.2.2) and metadata (4.1.3) in a term;
  recursive and indexed inductive types (5.2.1b, 5.2.1c), quotients (5.2.4),
  mutual and nested blocks (5.2.5); unfolding definitions (4.2.2), so some
  correct proofs end unknown; check --record and replay refuse
  inductive types while reading
limits (check answers full or exhausted, exit 3):
  check: stores, walks and lists that grow with the export (memory), any
    depth and number of dependencies or constructors (plan task 6.2.0);
    each check's scratch above the input: 1048576 term nodes, 65536 levels,
    262144 constant references (plan task 6.2.2)
  check --record, replay: 64 names, 64 levels, 64 term nodes,
    32 declarations per export
  universe parameters per declaration and universe arguments per constant:
    no fixed limit (memory)
  fuel 100000 steps per declaration (--fuel N, at most 9007199254740991)
planned, not built: program, serve and --record on any size,
  the axiom names of each accepted declaration (plan task 5.3.2)
```

## Manifests

Lean's export carries no checksum, so a file cut off between two lines
would read as a shorter, valid library. LeanForth's export step,
`scripts/export.sh OUT.ndjson MODULE... [-- DECLARATION...]`, therefore
writes `OUT.ndjson.manifest.json` beside each export: its SHA-256, its
line and byte counts, its record counts and the Lean version
([manifests](../development/NDJSON_READER.md#manifests)). `check`,
`count` and `reexport` compare the export with it while reading, by
default, and refuse a missing or different manifest as malformed input.
`check` reads the export once, while it stages it, and compares what it
read with the manifest at the end, before anything is checked; a change
anywhere in the file, a line cut off or a line added is refused as invalid
(`make test` checks each). `check --record`, `replay` and `print` read the
export in two passes (names first, then terms and declarations) and
compare each with the manifest. With the manifest or without it
(`--no-manifest`), the two passes must also have read the same bytes,
else the export is refused as invalid with "the export changed between
the two passes" (line 0), so a file replaced while they read it cannot
pair the names of one file with the terms of another:

```console
$ bin/leanforth check tests/core/check-declaration-cases/composition-loose.ndjson; echo "exit status $?"
error: invalid: manifest missing, unreadable or too large (line 0)
note: the export is checked against EXPORT.manifest.json, which scripts/export.sh writes;
note: --no-manifest skips that check
exit status 4
```

## Run records and replay

`check --record RECORD` also writes the *run record* of the check
([run records](../programming/RUN_RECORDS.md), format 0.1, plan task
2.2.5): which file was checked (its SHA-256, size, lines, whether its
manifest matched, and whether the check enforced it: true by default,
false with `--no-manifest`), which Lean and exporter wrote it, which LeanForth
commit and Forth system checked it (the commit `bin/leanforth` finds with
git, or null), with which fuel and limits, and each declaration's verdict,
read from its published slot. The printed verdicts and the exit status are
those of the check alone; a record that cannot be written is reported and
the status is then at least 4. A record holds at most 32 declarations, so
`check --record` reads the export into the checker's default sizes
([above](#small-exports-check---record-and-replay)); what a record
version 0.2 for exports of any size would need is written down in
[run records](../programming/RUN_RECORDS.md#version-02-records-of-any-size),
and needs the owner's [format] gate. A record costs reads: with
`--record` (and in `replay`) the export is read before the check for its
SHA-256, its metadata and its manifest, and once more after the check to
see that it did not change, besides the checker's own two passes.
Without `--record`, `check` reads the export once, as the importer stage
needs it, so a plain check of a large export pays nothing for records
(`tests/cli/leanforth.fs` checks that no record read happens then).
`replay EXPORT RECORD` checks the export again as `check --record` does
and compares the new record with RECORD, field by field; its output is
the replay report, one JSON line:

```console
$ bin/leanforth check --no-manifest --record /dev/null tests/core/check-declaration-cases/composition-wrong-argument.ndjson; echo "exit status $?"
note: the export's manifest is not checked (--no-manifest)
composition: rejected
  rejected: argument type mismatch (D1-D5); diagnostic 59 at mixed-infer lf-mixed-infer: 4 0
1 declaration: 1 rejected
exit status 1
$ bin/leanforth replay tests/reference/composition.ndjson tests/cli/no-such-record.json; echo "exit status $?"
{"schema":"leanforth-replay-report","schemaVersion":"0.1","result":"refused","findings":[{"code":"unreadable","path":"$"}],"findingsTotal":1}
exit status 4
```

Replay exits 0 when the record is confirmed (`"result":"confirmed"`), 1
when anything differs (each difference a finding with its code and JSON
path, such as `accepted-not-established` for a record that claims
*accepted* where the new run did not accept), and 4 when the record cannot
be compared or the export cannot be checked again. A record names the
commit, so after a new commit replay finds `tool-differs`. Give replay the
same `--fuel` and `--no-manifest` as the check; `make run-record` writes
records without the manifest check, so replay those with `--no-manifest`.

## What a verdict does and does not tell you

- *accepted* is printed only by the checker's own report of a
  declaration's published slot, and status 0 only when every slot says
  *accepted*. Reading the file, the command line and the printing are
  untrusted; they could hand the checker a wrong claim or misreport a
  failure, never make a declaration accepted. The checked statement is not
  yet printed for you to compare with your source (plan task 2.4.4).
- *rejected* means Lean's kernel rejects the declaration too, by one of
  the rules of [ADR 0011](../adr/0011-definite-rejection.md); *unknown*
  and *unsupported* mean LeanForth cannot decide it yet, not that it is
  wrong. Where Lean accepts such a declaration, that is a gap the plan
  closes (the plan tasks are in `capabilities`), never a difference
  LeanForth keeps.
- A declaration that uses one that was not accepted is never accepted:
  it ends *unknown* or *unsupported*.
- An accepted declaration that depends on an axiom outside `propext`,
  `Classical.choice` and `Quot.sound` would be marked NOT PROVED; none can
  be yet ([axioms](#what-check-prints)).
- The results are experimental, not independently audited, as long as
  the first checker has not passed its review gate.
- The resource report and the JSON report are untrusted output, like the
  text; fuel, time and memory never change a verdict.

## Gforth

`bin/leanforth` runs the Gforth named by the `GFORTH` environment
variable; otherwise the pinned one in `.tools/gforth` of its checkout
(`scripts/install-gforth.sh`), otherwise `gforth` on the `PATH`. `count`
and `reexport` prefer `gforth-fast`, about 3.3 times faster on large
exports; `check` uses the `gforth` engine, whose stack and memory checks
turn a fault in the checker into an internal fault where it happens.
`GFORTH=.tools/gforth/bin/gforth-fast` checks `Init` more than twice as
fast, with the same verdicts byte for byte. Standard input is closed.
`bin/leanforth version` adds the checkout's git commit to the versions:

```console
$ bin/leanforth version | sed -n '1p;3p'
leanforth 0.1.0-dev (development version; experimental, not independently audited)
reads: lean4export 3.1.0, format 3.1.0, Lean 4.35.0 (eb6cafb7290e8bd5f2937522d8d804f58f02bafc)
```

## Not built yet

`program` (a program receipt), `serve` (the JSON-RPC interface for AI
tools, plan section 3.5), receipts that carry each theorem's statement
(task 3.4.3 beyond the check report), `--record` on exports of any size,
the names of the axioms each accepted declaration uses (task 5.3.2), the
resource report in run records and in `print` (task 6.5.2), and Markdown
and JSON forms of `print`'s outline (task 2.4.4).

## Tests

`make test-cli` runs `tests/cli/leanforth.fs` (the Forth side: every
outcome's code, the order of severity, NOT PROVED, the record hook, the
fuel each check used, the stage freed and the stores' sizes given back
after every check, two injected internal faults, `print`'s codes, and a
THROW at each of `print`'s store allocations, after which the log is off
and no environment is left) and `tests/cli/test_leanforth.py` (the tool
itself: every exit status with its exact output, from other folders,
tampered and cut exports, every JSON report against its schema and
against the text, the resource report, exact fuel, against the counter and
the re-exporter, with a broken Gforth, and `print`'s outlines against the
outline printer's golden file). `make reference-cli`, part of `make
check`, has pinned Lean accept `tests/cli/chain.lean`, `unfold.lean` and
`inductive.lean` and has `scripts/export.sh` reproduce their committed
exports and manifests byte for byte. The examples on this page run in
`make test` and `make check`.

## See also

- [First check](FIRST_CHECK.md): the same check from the inside, step by
  step.
- [For AI tools](AI_TOOLS.md): the command line among the other
  interfaces, and the rules for reporting its results.
- [Diagnostics](../programming/DIAGNOSTICS.md): every reason code.

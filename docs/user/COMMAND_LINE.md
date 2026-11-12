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
declarations, in [about twelve minutes](#a-whole-library-leans-init). Most
of a real library may still end *unsupported* or *unknown*: nested
inductive types, metadata and some projection steps are not built yet
(`capabilities` lists them); unsafe and partial declarations are
*skipped*, as Lean's own checker skips them (below). The
counts of Init below are a snapshot of 2026-11-04, before `let`,
literals, projections, quotients and mutual blocks were merged; no
Mathlib declaration has been checked (0 of 729,263). Two commands keep the first,
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
defaults (manifest checked, fuel 100,000,000 per declaration):

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
| `check [--no-manifest] [--fuel N] [--resources] [--json] [--checked] [--strict-axioms] [--any-lean-version] [--jobs N] [--progress[=SECONDS]] [--memory-per-check MB] [--save-snapshot FILE] EXPORT` | Check every declaration of a Lean export of any size, in file order; with `--resources`, also print the [resource report](#the-resource-report); with `--json`, print [one JSON report](#json-output) instead of text; with `--jobs N`, check with [N workers at once](#parallel-checking---jobs); with `--memory-per-check MB`, give each check [at most MB megabytes of scratch](#memory-per-check---memory-per-check); with `--progress`, write [a status line](#progress-and-partial-results---progress) to standard error every minute; with `--save-snapshot FILE`, also write the checked environment to FILE ([snapshots](#snapshots---save-snapshot-and---snapshot)) |
| `check --snapshot FILE [--snapshot LAYER ...] [--fuel N] [--resources] [--json] [--checked] [--strict-axioms] [--any-lean-version] [--no-manifest] [--jobs N] [--save-snapshot LAYER] [--snapshot-stale-ok] [EXPORT]` | Report the verdicts a [snapshot](#snapshots---save-snapshot-and---snapshot) and its layers hold, each labelled as taken from it and not re-checked; with EXPORT, check it against them, taking what they vouch for and checking the rest, and with `--save-snapshot`, write what was checked as a layer: for development and research only |
| `check [--no-manifest] [--fuel N] [--checked] [--strict-axioms] --record RECORD EXPORT` | Check a small export (read straight into the checker's stores) and also write its [run record](#run-records-and-replay) |
| `replay [--no-manifest] [--fuel N] [--checked] EXPORT RECORD` | Check the export again and compare the new run record with RECORD; print the replay report |
| `print [--no-manifest] [--fuel N] [--checked] [--detail] [--name NAME] [--latex] [--statement FORMS] [--any-lean-version] EXPORT`, or `print --lf [--no-manifest] [--fuel N] [--checked] [--any-lean-version] EXPORT` | Check the export and print each accepted declaration's [readable proof](#printing-a-readable-proof), or with `--detail` every step of the checker's log; `--name` prints one declaration; `--lf` writes the whole export as one [LeanForth text](#writing-an-export-as-leanforth-text) |
| `count [--no-manifest] EXPORT` | Count the export's records by kind ([the reader's counter](../development/NDJSON_READER.md#using-it)), for exports of any size |
| `reexport [--no-manifest] EXPORT COPY` | Write the export again into COPY, byte for byte as Lean's exporter writes it ([re-export](../development/NDJSON_READER.md#re-export)); after an error COPY is incomplete and must be discarded |
| `version` (or `--version`) | Versions of LeanForth, its Forth host, the export format it reads, and the git commit |
| `capabilities` | What this build supports, what it does not, and its limits |
| `help` (or `--help`, `-h`) | The usage text |

Options:

- `--no-manifest` reads the export without checking its manifest. It is
  an explicit choice, and `check`, `count` and `reexport` say so in their
  first line.
- `--fuel N` gives each declaration's check N steps (default 100,000,000 since 2026-11-11, when the Lean Kernel Arena's Θ(n²) perf tests needed it: Lean's own kernel takes 20-91 million of the same steps on them; 20,000,000 earlier that day, when all of `Init` needed it; 2,000,000 from 2026-11-10; 100,000 before). A
  check that runs out ends *exhausted*. N is decimal digits, at most
  2^53 − 1 = 9,007,199,254,740,991, the largest integer every JSON reader
  holds exactly, so that reports and run records hold it; a larger N is a
  command-line mistake (status 4).
- `--record RECORD` writes the run record of the check to RECORD
  ([run records and replay](#run-records-and-replay)); RECORD must not be
  the export. Run records 0.2 hold at most 32 declarations, so `check
  --record` reads the export straight into the checker's default
  sizes ([small exports](#small-exports-check---record-and-replay)).
- `--resources` (`check` only) adds the [resource report](#the-resource-report)
  after the summary: time, memory, the input's size and fuel.
- `--json` (`check` only) prints the whole result as one
  [JSON report](#json-output) instead of text. Neither goes with
  `--record` (status 4).
- `--strict-axioms` (`check` only) makes a run whose declarations are all
  accepted, some of them NOT PROVED, exit with status 6 instead of Lean's
  0 ([axioms and NOT PROVED](#what-check-prints)).
- `--any-lean-version` (`check` and `print`, not with `--record`) reads an
  export whose metadata names another exporter or Lean version, as long as
  its format version is 3.1.0, the format LeanForth reads; by default only
  lean4export 3.1.0's exports of Lean 4.35.0 (githash `eb6cafb…`) are read,
  anything else is *unsupported* (status 2). The verdicts are still those
  of Lean 4.35.0's kernel rules, which another Lean version's kernel may not
  share, so a note says what the export named:

  ```text
  note: export made by Lean 4.29.1 (githash 2fcce7258eeb6e324366bc25f9058293b04b7547), written by handcrafted 0.1.0; verdicts are Lean 4.35.0's
  ```

  The texts are escaped as names are, so a crafted version cannot forge a
  line. With a manifest, its `exporter`, `exporter_version`, `lean_version`
  and `lean_githash` then need only be strings (they are labels: they are not
  compared with the export's own header, and the SHA-256 binds the manifest
  to the file); `export_format` must still be 3.1.0. The [JSON report](#json-output) adds `settings.anyLeanVersion`
  and, when the metadata named other versions, `exportMeta`.
- `--checked` (`check`, `replay`, `print`) runs on Gforth's checking engine,
  `gforth`, instead of the default `gforth-fast` ([the engine](#the-engine)).
  `--fast` is still accepted and changes nothing (it cannot be combined with
  `--checked`).
- `--jobs N` (`check` only, not with `--record`) checks with N workers at
  once ([parallel checking](#parallel-checking---jobs)); N is at least 1,
  and 1, the default, checks one declaration at a time. The output is the
  same whatever N is. N is cut to the number of cores (and to the job
  pool's queue of 1024): more workers could not run at once. The workers
  share one copy of the input; each adds only its own scratch and caches
  (the resource report says how many were made). On a host that is not x86-64
  (threads without memory barriers) or where the thread pool cannot start,
  the check runs one declaration at a time and the resource report says why.
- `--memory-per-check MB` (`check` only, not with `--record`) gives each
  declaration's check at most MB megabytes (of 2^20 bytes) of scratch; a
  check that would pass it is *full* ([memory per check](#memory-per-check---memory-per-check)).
  MB is at least 1; without the option there is no limit but the heap's.
- `--progress[=SECONDS]` (`check` only, not with `--record`) writes a status
  line to standard error every SECONDS (60 without a value; 0: after every
  report) and one at the end ([progress](#progress-and-partial-results---progress)).
  It changes nothing on standard output or in the exit status.
- `--save-snapshot FILE` (`check` only, not with `--record`) writes the
  run's checked environment to FILE after a run in which every declaration
  was decided; FILE must not be the export. `--snapshot FILE` (`check`
  only, not with `--record`) reports a snapshot's verdicts, a further
  one loads a layer on it, and with an export checks the export against
  them; `--save-snapshot` with one `--snapshot` and an export writes a
  layer ([snapshots](#snapshots---save-snapshot-and---snapshot)).
  `--snapshot-stale-ok` (with `--snapshot`, not with `--save-snapshot`)
  loads a snapshot of an older verdict version, its results labelled
  stale ([stale snapshots](#stale-snapshots---snapshot-stale-ok)).
- `--detail` (`print` only) prints every step of the checker's log
  instead of the outline; `--name NAME` (`print` only) prints only the
  declaration named NAME.

### The engine

`check`, `replay` and `print` run on `gforth-fast` by default (owner's
decision of 2026-11-11, replacing that of 2026-11-04), which leaves out
Gforth's stack and memory checks and is about 2.4 times quicker than the
checking engine, `gforth`. `--checked` runs them on `gforth`, which stops
at a stack or memory fault where it happens, so a fault in LeanForth's
own Forth is reported as an internal fault at its source; use it to
investigate a surprising result. `make test` and `make check` run on the
checking engine, and `make engine-gate` compares both engines on all of
`Init` and the arena tests. For reference, all of Lean's `Init` took all of Lean's `Init` in 4 minutes 5 seconds instead of 9
minutes 59 seconds, on the checking engine and 4 minutes 5 seconds on `gforth-fast`, for one build of 2026-11-04
([below](#a-whole-library-leans-init)). Both engines give the same
verdicts in every test (`make test` compares the text and the JSON
reports of the command-line fixtures on both), and the JSON report is
the same but for `measured`, which names the engine. `count` and
`reexport`, which check no proof, use `gforth-fast` (about 3.3 times
faster on large exports). The engine is the one `GFORTH` names when it
is set, used as it is (with `--fast`, the `gforth-fast` in the same
folder, on `PATH` when `GFORTH` names no folder) — else the pinned one
in `.tools/gforth`, else one on `PATH`. When no `gforth-fast` is found,
the run uses `gforth` and says so on standard error:

```text
leanforth: note: no /opt/forth/gforth-fast found; checking with /opt/forth/myforth
```

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
anonymous name as `[anonymous]`; names of any depth. Three differences
from Lean's text make the line show exactly what the name holds, so that
no name, however crafted, can start a line of its own, look like the
start of another declaration's line, move the cursor or reorder the
text after it:

1. A component that is not an identifier is always between `«` and `»`.
   Lean leaves them out for a component that holds `»`, and for a whole
   name with macro scopes (`x._@._hyg`), an inaccessible name (one holding
   `✝`) or pseudo-syntax (`_`, or a root that starts with `#` or `?`); its
   spaces and colons would then pass through, and a line could begin
   `fake: accepted (…)`. Here `x._@._hyg` is `x.«_@»._hyg`.
2. Inside `«»`, every character the [text rule of run
   records](../programming/RUN_RECORDS.md) bans — control characters (C0
   and C1, line feed and carriage return among them), format characters
   such as the bidirectional controls, and the line and paragraph
   separators — and `»` itself are shown as `\u{X}`, the code point in
   hexadecimal, so a component ends at its first `»`; a byte that does
   not start UTF-8 is shown as `\x{X}`.
3. A backslash is shown as `\\`, so that the text of an escape in a name
   is never read as an escape.

A theorem named `composition: rejected` + line feed + `forged: accepted …`
is one line, `«composition: rejected\u{A}forged: accepted …»: accepted …`,
and one named `fake: accepted …✝` is `«fake: accepted …✝»: …`. Identifiers
are as Lean's `isIdFirst` and `isIdRest` have them, subscript digits and
letters (`x₁`, `xₐ`) included and subscript signs not (`«x₊»`). The JSON
report's `name` holds the same text, and its `export` member the export's
file name with the escapes of 2 and 3; both are display text, not the
name's bytes, and a declaration is identified by its `index`, its place
in the export.

**Axioms and NOT PROVED.** The axioms are read from each accepted
declaration's slot: the axiom set the checker joined from everything the
declaration uses (plan task 5.3.1). An axiom gets Lean's verdict: Lean's
kernel accepts any axiom whose type is well formed, and so does
LeanForth. Only `propext`, `Classical.choice` and `Quot.sound`, each with
exactly Lean 4.35.0's statement (the versioned allowlist,
`src/core/axiom-allowlist.fs`, version 1), count as proved, and only
when the constants their statements name are Lean's own: `Quot` and
`Quot.mk` the quotient constants, and `Eq`, `Iff` and `Nonempty` the
inductive types exactly as Lean's `Init` declares them (universe
parameters, type, parameters, a block of their own, one constructor of
Lean's name and type, accepted without a warning). `propext` with
Lean's exact statement about an `Iff` the file declares otherwise is
therefore unlisted. The allowlisted names follow `axioms:` on the line,
in the order `#print axioms` sorts them, and `unlisted` stands for any
other axiom. Under the owner's rule,
an accepted declaration that depends on an unlisted axiom -- `sorryAx`,
an axiom the file declares, or `propext` with another statement -- is
marked `NOT PROVED: depends on` with those axioms named (in file order)
and counted apart in the summary, never as proved. The summary names
the allowlisted axioms the accepted declarations use, then the count:
`axioms: none` when they use no axiom, else for example `axioms:
propext, Classical.choice, Quot.sound (allowlisted); none NOT PROVED`
or `axioms: 2 NOT PROVED (they depend on an axiom)`. The mark is
presentation, never a different verdict. So, by the
owner's decision of 2026-11-04, a
run whose declarations are all accepted, some of them NOT PROVED, keeps
Lean's exit status, 0, and says so in a note after the summary:

```text
note: NOT PROVED declarations keep Lean's exit status; --strict-axioms
note: makes it 6
```

With `--strict-axioms` the same run exits with status 6, below every real
failure ([exit status](#exit-status)), and the JSON report's
`settings.strictAxioms` is true. `make test` reaches both with an
export's own axiom and by planting an axiom in an accepted slot.

**Unsafe and partial declarations: skipped.** Lean's own checker for
exports, its replay (`Lean/Replay.lean` 180–183), never checks an
unsafe constant (a definition marked `unsafe`, or an axiom, opaque
constant, inductive type, constructor or recursor with `isUnsafe`) or a
`partial` definition: it skips them, so a file that holds one is still
accepted, and a later declaration that uses one meets an unknown
constant. LeanForth does the same (plan task 5.2.7): such a declaration
is *skipped*, nothing of it checked, with Lean's exit status 0; it is
never labelled accepted, nothing can use it (a use is *rejected*, as
Lean's checker rejects it), and its name stays taken. Here `composition`
is declared as an unsafe definition:

```console
$ bin/leanforth check --no-manifest tests/core/check-declaration-cases/composition-unsafe.ndjson; echo "exit status $?"
note: the export's manifest is not checked (--no-manifest)
composition: skipped
  skipped: unsafe or partial, as Lean's replay skips it; diagnostic 97 at environment lf-env-skip: 1 1
1 declaration: 1 skipped
exit status 0
```

An inductive block whose members are all unsafe is skipped the same way;
one with both safe and unsafe members, which Lean never writes, is still
*unsupported* (task 5.2.7, part b). `print` shows a skipped declaration's
slot as *rejected*, with diagnostic 97.

A broken copy of `composition`, whose proof applies `g` to `value`
instead of to `f value`, is rejected for the reason Lean's kernel gives
(Lean's definitional equality says no: the argument has type `A`, `g`
needs a `B`). The copy has no manifest, so it is read
with `--no-manifest`:

```console
$ bin/leanforth check --no-manifest tests/core/check-declaration-cases/composition-wrong-argument.ndjson; echo "exit status $?"
note: the export's manifest is not checked (--no-manifest)
composition: rejected
  rejected: argument type mismatch (D1-D5); diagnostic 59 at mixed-infer lf-mixed-infer: 0 0
1 declaration: 1 rejected
exit status 1
```

A file whose check needs a definition unfolded:

```console
$ bin/leanforth check tests/cli/unfold.ndjson; echo "exit status $?"
Implies: accepted (experimental, not independently audited); axioms: none
impliesSelf: accepted (experimental, not independently audited); axioms: none
2 declarations: 2 accepted
accepted: 2 (experimental, not independently audited); axioms: none
exit status 0
```

Checking `impliesSelf` needs the definition of `Implies` unfolded by
Lean's lazy delta reduction, which the checker does since plan task
4.2.2d (before, it was *unknown*); Lean accepts it too:

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
today: blocks such as `Prod`, `Eq` and `Iff`, recursive types such as
`Nat` and `List` (plan task 5.2.1b), projections (plan task 5.2.2) and
natural-number literals (plan task 5.2.3), axioms (5.3.1), opaque
declarations (4.2.6), quotients (5.2.4) and nested types (5.2.5b) are
accepted; the unsafe definition `risky` is skipped, as Lean's replay skips it
(below); string literals and what uses them are not yet:

```console
$ bin/leanforth check --no-manifest tests/core/reexport/kinds.ndjson | tail -n 2; echo "exit status ${PIPESTATUS[0]}"
106 declarations: 94 accepted, 1 skipped, 11 unsupported
accepted: 94 (experimental, not independently audited); axioms: propext (allowlisted); none NOT PROVED
exit status 2
```

### A whole library: Lean's `Init`

`check` holds an export of any size: the importer stage reads it once,
with its manifest, into a compact store (a loading stage only: the
checker does not read it in place, it copies the staged names, levels,
terms and declarations into its own stores, which grow to take them). Lean's own `Init` library, exported with
`scripts/export.sh` (345.7 MB, 59,349 declarations), checked on
2026-11-04 with the default fuel (a snapshot; later merges changed some verdicts and the
numbers were not re-measured since):

```text
$ bin/leanforth check --fast --resources init.ndjson | tail -n 29
59349 declarations: 2503 accepted, 5056 unknown, 51579 unsupported, 180 exhausted, 31 full
accepted: 2503 (experimental, not independently audited); axioms: none
note: a check ran out of room; its diagnostic names the limit: memory, or
note: 16 dependencies per declaration, 65536 per export, 512 constructors per
note: inductive block (plan task 6.2.0)
note: a check ran out of fuel (100000 steps each); --fuel N gives each more
resources:
  time (s)     wall      cpu
  stage      30.902   29.019
  feed       17.062   17.062
  check     676.073  658.932
  total     724.465  705.442
  memory: peak resident 1237.9 MB; the stage's heap blocks 179.7 MB
  engine: gforth-fast
  input: 59349 declarations, 6099054 term nodes, 578 levels, 56957 constant references, 295432 names
  fuel: 31876309 steps in all, at most 100000 per declaration
  fuel not known for 29203 declarations: a failed inference gives its
    counter up (their checks are not in the fuel above)
  most fuel used:
    100000 Lean.Omega.Constraint.add_sat (exhausted)
    100000 ByteArray.utf8Decode?.go._unary.eq_def (exhausted)
    100000 String.Slice.Pos.copy_eq_append_get (exhausted)
    100000 _private.Init.Grind.Config.0.Lean.Grind.instBEqConfig.beq.match_1 (exhausted)
    100000 Array.map_attach_eq_pmap (exhausted)
    100000 Std.IterM.step_filterMapM (exhausted)
    100000 Std.IterM.toList_filterMapM_map (exhausted)
    100000 Std.Iter.forIn'_eq_match_step (exhausted)
    100000 Std.IterM.step_filterMap (exhausted)
    100000 Std.IterM.toList_filterMap (exhausted)
```

Nothing was rejected and nothing was invalid. The 2,503 accepted
declarations include `id`, `Function.comp`, whole inductive blocks such
as `Bool`, `Option`, `Prod`, `Sum`, `And`, `Or`, `Exists`, `Eq`, `HEq`
and `Decidable`, and since task 5.2.1b the recursive types `Nat`, `List`
and `Array` with their recursors. Almost everything else is
*unsupported* or *unknown* because it needs features not built yet —
each a gap to close, not an answer that differs from Lean's, which
accepts all of `Init`: literals, projections and other term forms
(5.2.3, 5.2.2, 4.2.3; 25,703 declarations), axioms, opaque, unsafe and
partial declarations and quotients (252; axioms, opaque declarations
and quotients since 5.3.1, 4.2.6 and 5.2.4; unsafe and partial ones
were unsupported in that run and are skipped, as Lean's replay skips
them, since plan task 5.2.7), mutual
and nested inductive blocks (5.2.5; 8), comparisons that need
definitions unfolded (4.2.2; 951 *unknown*, codes 30–32), and
everything that uses one of those (25,616 *unsupported* and 4,105
*unknown* only for that). *full* meant a declaration with more than 16
dependencies (31, such as `Lean.Grind.CommRing.Expr.toPoly.match_4.congr_eq_1`),
a limit gone since plan task 6.2.0 (below), and *exhausted* a check that
needed more than 100,000 steps (180; `--fuel N` gives more). No term is too deep any more: since
the depth work of plan task 6.2.0 (part (b)) the 55 declarations that
ended *full* at a walk's 64 levels in the first run of 2026-11-04 get
other verdicts. 183 names, most of them notations such as `«term_+_»`,
are shown with `«»`, as Lean shows them.

Since part (c) of plan task 6.2.0 (2026-11-04) nothing in a check has a
fixed number any more: a declaration's dependencies, the environment's
dependency pool and an inductive block's constructors grow with the heap,
like its terms and its depth. A check is *full* only when the heap
refuses, or when it needs more than its scratch above the input, as the
note after the summary then says. That scratch grows since step S5 of the
compact-store plan (2026-11-11; plan task 6.2.2), up to about 2^31 term
nodes, levels and constant references each, or the limit a context sets
with the Forth word `lf-input-room!` (`src/core/input.fs`); before, it
was fixed at 1,048,576 term nodes, 65,536 levels and 262,144 constant
references. The same build with
part (c), checked with `--resources --json` and `gforth-fast`, gave
2,503 accepted, 5,083 *unknown*, 51,583 *unsupported*, 180 *exhausted*
and none *full*: of the 31 declarations above that ended *full*, 27 are
now *unknown* (a comparison that needs a definition unfolded, plan task
4.2.2) and 4 *unsupported* (a dependency unsupported, such as
`Sum.isRight_iff`), and every other declaration kept its verdict and
diagnostic.

The run above used the `gforth-fast` engine
([the engine](#the-engine)), on a 10-core WSL2 machine that other agents'
test runs shared; its checks took 11 minutes, against under 4 for the
build of the morning, which accepted 1,618 declarations and checked
fewer that far. The checking engine (`--checked`) gives the
same output, byte for byte but for the times, memory and engine lines,
in about 2.4 times as long (9 min 59 s against 4 min 5 s for the
morning's build; not yet measured on this one). Freeing the stage's
export-index maps once it is staged gives back 35.7 MB of its 215.1 MB;
on three runs of the morning's build, the same verdicts, fuel and
diagnostics for every declaration, the peak was 1,263 MB without it and
1,218 MB with it (peaks vary by about 20 MB from run to run). The ten
declarations that used the most fuel all ran out of it. Half the declarations' fuel is not known: their check
failed inside inference, which gives its counter up, so neither the
total nor the list counts them ([fuel](#the-resource-report)); a later
step of plan task 6.5.2 can keep it, with a change to the checker.

### Parallel checking (`--jobs`)

`check --jobs N` checks with N workers at once (plan tasks 6.5.4 and
7.3.1, 2026-11-11; its [kernel] review is pending). The output is the
same as with `--jobs 1`, the default, byte for byte but for the resource
report's times, memory and workers line, and the JSON report but for
`measured`: every verdict, diagnostic and fuel count, the counts and the
exit status. How:

- each worker is a context of its own that reads one shared input in
  place, the one the run fed (the staged export, its declarations, the
  tables of its leaves and binders, its constant references; nothing a
  check does writes them), keeps only its own scratch, caches, memos and
  marks (and its levels, a few thousand), and checks one declaration at a
  time as a thread of Gforth 1.0 (cooperative tasks on Gforth 0.7.3, which
  gives the same output, no faster);
- a declaration is handed to a worker only when every earlier declaration
  its check may look up by name is published, and results are published
  by one task, in the order checks end, into the checked environment's
  slots, from which the report is printed afterwards in file order;
- a check that still finds an earlier declaration it needs unpublished
  (a name met only after unfolding a definition) is thrown away and run
  again later, never published; each check starts from the input alone,
  with empty caches, so its fuel does not depend on the other checks its
  worker ran.

All of `Init` (59,349 declarations, all accepted), `check --fast --json
--jobs N`, on this 10-core WSL2 machine, which other agents' runs shared,
2026-11-11, every report the same as the serial one but for `measured`.
With the shared input (wall and CPU seconds of the whole run, peak
resident memory, the load average; the wall times are noisy at such
loads, the CPU times and memory much less so):

| workers | wall | CPU | peak memory | load |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 1,354 | 1,249 | 658 MB | 12-18 |
| 4 | 511 | 1,439 | 957 MB | 18 |
| 8 | 263-346 | 1,428-1,477 | 1,166-1,175 MB | 17-21 |
| 10 | 244-481 | 1,421-1,479 | 1,221-1,280 MB | 15-23 |

More workers than the cores are not made (`--jobs 12` here runs 10): in a
copy of LeanForth whose pool was forced to 12 threads, `Init` took
233-326 s, 1,429-1,461 s CPU and 1,314-1,356 MB, no gain over 10 beyond
the noise. Mathlib's first sixth (119,472 declarations) at 8 workers took
2,773 s at load 15-22 and 4,688 MB (7,710 MB when each worker held its
own copy of the input, the same run otherwise); for all of Mathlib, 8
workers are expected to hold about 13 GB (ADR 0016, Amendment 2).

Before the input was shared (each worker fed its own copy; load average
10-13; wall, the check phase's wall time, its speed-up, CPU, peak memory):

| workers | wall | check wall | speed-up (check) | CPU | peak memory |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 1,157 | 1,136 | 1.0 | 1,146 | 543 MB |
| 2 | 557 | 536 | 2.1 | 1,088 | 1,030 MB |
| 4 | 367 | 334 | 3.4 | 1,307 | 1,478 MB |
| 6 | 407 | 374 | 3.0 | 1,481 | 1,809 MB |
| 8 | 215 | 183 | 6.2 | 1,400 | 2,219 MB |
| 10 | 249 | 209 | 5.4 | 1,512 | 2,564 MB |

The run with 6 workers met the heaviest load from other runs; the times
vary by that much from run to run on a shared machine. Each worker then
cost about 210 MB and its feeding about 2.5 seconds, one worker after
another (the "feed" phase: 25 seconds for 10 workers); sharing the input
brings a worker of `Init` down to about 64 MB (its scratch, caches and
marks) and its feeding to a fraction of a second (the "feed" phase at 8
workers: 2.3 seconds, against 16.3). When no worker can be
made (no memory; or, from a Forth session, a context that ran checks
before, whose input then has another fingerprint than a new worker's),
the run checks one declaration at a time, and the resource report says
so. With `--resources` the
report adds a line naming the workers and how many checks were handed
out, run again, refused by readiness or forced (the last two are 0 unless
LeanForth's plan of which declaration needs which is wrong).

### Memory per check (`--memory-per-check`)

`check --memory-per-check MB` limits the scratch of each declaration's
check to MB megabytes (MB × 2^20 bytes): the term nodes, levels and
constant references it makes above the input, its local context and its
result caches, all of which it gives back when it ends. A check that
would pass the limit stops and is *full*, exit status 3, as when memory
runs out; it is never accepted, and declarations that depend on it are
unknown, as after any other *full*. Its diagnostic is code 101, "memory
limit per check", with the bytes the check asked for and the limit, and a
note follows the summary. With `--json` the settings hold
`"memoryPerCheck": MB`. The limit applies to every worker of `--jobs N`
alike, so a check gets the same verdict serially and in parallel, and the
bytes are counted per record made, not read from the heap, so the same
check under the same limit is full in every run.

Like fuel, the limit is LeanForth's own resource bound, never a Lean
verdict: Lean's kernel has neither. Its use is a long parallel run such
as all of Mathlib with a large `--fuel`: the workers of `--jobs` share
one process's memory, so without a limit one huge check could take the
memory the others need and make their checks *full* too. Each record a
check makes counts a fixed number of bytes, an upper bound on a 64-bit
host of what the record itself takes (96 per term node, 176 per level,
64 per reference and 16 per universe argument, 64 per cache entry, 48
per local-context entry). The heap holds more than the count: stores
and tables grow by doubling, and a worker keeps what its largest check
grew; the walks' stacks and memos, the input, the stage and the checked
environment are not counted. Measured on the doubling export (`gen.py
double 14` and `double 16`, 2026-11-11), a check that needed 11 and 44
MB by the count grew the process by 14 and 59 MB: about 1.3-1.4 times.
So give each check at most about half of the memory the run has left
after the input, divided by the workers. A snapshot written with a limit holds such checks as *full*;
an export checked against it checks them again (*full* is never taken
from a snapshot).

```
$ python3 tests/cli/jobs/gen.py double 12 > /tmp/double12.ndjson
$ bin/leanforth check --no-manifest --memory-per-check 1 /tmp/double12.ndjson
...
big: full
  memory limit per check; diagnostic 101 at check-declaration lf-check-declaration: 1048640 1048576
...
18 declarations: 17 accepted, 1 full
accepted: 17 (experimental, not independently audited); axioms: none
note: a check ran out of room; its diagnostic names the limit: memory, or
note: each check's scratch above the input grows, up to 2147483647
note: term nodes, levels and constant references each (plan task 6.2.2)
note: a check passed its memory limit (1 MB each); --memory-per-check MB gives each more
```

With `--memory-per-check 4` (or none) `big` is accepted: Lean accepts it
after unfolding 2^12 - 1 definitions.

### Progress and partial results (`--progress`)

A check of a library takes hours (all of Mathlib is a run of a day or
more), and the report used to appear only at the end. Two changes let you
watch a run and keep what it found (2026-11-11, untrusted reporting; no
verdict, fuel count, exit status or byte of a finished run's standard
output changes):

- **The text report's lines are written as the run goes.** A declaration's
  line is written once it and every declaration before it are final (the
  serial run: when its check ends; `--jobs`: when the scheduler's frontier
  passes it), in file order, so a run that is stopped (killed, timed out,
  the machine going down) leaves the lines of the declarations before the
  stop, a correct prefix of the report. Standard output is flushed every
  2000 lines or ten seconds (the progress interval, if it is shorter), so
  a stop loses at most that much: `timeout 600 leanforth check EXPORT >
  lines.txt` keeps the prefix. The summary, the notes and the resource
  report come at the end, so a stopped run has no summary: count the
  lines (`grep -c ': accepted'`). `--json` is one text, written at the
  end, and is not affected. With `--jobs` the lines written are always a prefix of the
  serial run's: nothing at or after a declaration whose check threw is written
  while the run goes (the run then ends with the internal-fault message and code 5).
  Gforth does not flush its output when it is killed by SIGTERM (`timeout`): the
  lines since the last flush are lost, at most 2000 lines or ten seconds' worth.
  Measured: `timeout 60` on all of Init left 3354 lines, a byte-for-byte prefix
  of the full output, ending at a line end.
- **`--progress[=SECONDS]`** writes one line to standard error each time
  SECONDS seconds (default 60) have passed when a declaration becomes final
  (a single check longer than the interval delays its line), and one when
  the run ends:

```text
progress: 754 s elapsed; 120000/729263 declarations final (16%); 119990 accepted, 10 other; 159 declarations/s; eta 3830 s; resident 8123 MB
```

  the seconds since the check began, the declarations final of the total
  (all below that number, in file order) and their share, how many were
  accepted and how many were anything else, the average rate so far, a
  rough estimate of the seconds to go at that rate (declarations differ
  very much in cost, so it can be far off; `unknown` before the first), and
  the process's resident memory (`? MB` where the host has no
  `/proc/self/status`). `--progress=0` writes a line after every
  report, for tests. The lines go only to standard error, in text and
  `--json` mode alike; `--progress` does not go with `--record` (status 4)
  and `replay` and `print` do not take it.

### The resource report

`--resources` adds a report after the summary (plan task 6.5.2, the
command line's part): the wall and CPU time of each phase — staging,
feeding, checking — and of the whole run so far, in seconds; the
process's peak resident memory (`VmHWM` in `/proc/self/status`; on a host
without it, `not measured on this host`) and the bytes of heap blocks the
stage holds while the checks run (its export-index maps, which only
loading needs, are freed once it is staged: `stage-unmap`); the engine
that ran ([the engine](#the-engine): the file name of the Gforth
program, such as `gforth` or `gforth-fast`, or `not known` outside
`bin/leanforth`); the size of the input as fed (declarations, term
nodes, levels, constant references, names); the fuel all checks used;
and the ten declarations that used the most, most first, those of equal
fuel in file order. Times and memory differ from run to run, and the
engine with how the tool is run; everything else is the same on every
run, as in this example, where the time, memory and engine lines are
left out:

```console
$ bin/leanforth check --resources tests/cli/inductive.ndjson | grep -v -E "^  (stage|feed|check|total) |^  (memory|engine): "
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
  input: 6 declarations, 92 term nodes, 3 levels, 5 constant references, 31 names
  fuel: 415 steps in all, at most 100000000 per declaration
  most fuel used:
          244 Two.cases (accepted)
          113 Two.swap (accepted)
           58 Two (accepted)
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
the format `leanforth-check-report`, version 0.2
([`schemas/check-report-0.2.schema.json`](../../schemas/check-report-0.2.schema.json),
JSON Schema draft 2020-12 within the subset of
[`tests/support/schema_subset.py`](../../tests/support/schema_subset.py)).
It holds what the text holds and the resource report, with the times and
memory apart in `measured`; every other member is the same on every run
of the same export with the same options and build. Here the `measured`
member is cut off:

```console
$ bin/leanforth check --json tests/cli/unfold.ndjson | sed "s/,\"measured\":.*/}/"; echo "exit status ${PIPESTATUS[0]}"
{"schema":"leanforth-check-report","schemaVersion":"0.2","export":"tests/cli/unfold.ndjson","manifest":"checked","label":"experimental, not independently audited","settings":{"fuel":100000000,"dependencyPool":65536,"strictAxioms":false},"read":{"outcome":"ok","phase":null,"line":null,"field":null,"reason":null,"at":null},"run":"ok","stopped":false,"declarations":[{"index":0,"name":"Implies","verdict":"accepted","label":"experimental, not independently audited","axiomBits":0,"notProved":false,"fuel":34},{"index":1,"name":"impliesSelf","verdict":"accepted","label":"experimental, not independently audited","axiomBits":0,"notProved":false,"fuel":65}],"counts":{"declarations":2,"accepted":2,"skipped":0,"rejected":0,"unknown":0,"unsupported":0,"invalid":0,"exhausted":0,"full":0,"notChecked":0,"notProved":0},"fuel":{"perDeclaration":100000000,"total":99,"unknown":0,"top":[{"index":1,"name":"impliesSelf","fuel":65,"verdict":"accepted"},{"index":0,"name":"Implies","fuel":34,"verdict":"accepted"}]},"input":{"declarations":2,"terms":28,"levels":1,"references":1,"names":10},"exitStatus":0}
exit status 0
```

| Member | Contents |
| --- | --- |
| `schema`, `schemaVersion` | `leanforth-check-report`, `0.2` (since the verdict *skipped*, 2026-11-11; [`0.1`](../../schemas/check-report-0.1.schema.json), kept unchanged for earlier reports, has no *skipped*) |
| `export`, `manifest` | the file name given, as escaped display text (the escapes of [names](#what-check-prints)); `checked`, or `not-checked` with `--no-manifest` |
| `label` | `experimental, not independently audited` |
| `settings` | the fuel per check, `dependencyPool`, the room the environment's dependency pool starts with (it grows: not a limit since plan task 6.2.0), and `strictAxioms` (true with `--strict-axioms`); `anyLeanVersion`, true, only with `--any-lean-version` |
| `read` | the read's outcome and, for a failure, its `phase` (`open`, `stage`, `feed`), `line`, `field`, `reason`, and for the feed the number `at` which it stopped |
| `exportMeta` | only when the export's metadata named another exporter or Lean version (with `--any-lean-version`) and it was staged: `exporter` (`name`, `version`), `format` (`version`) and `lean` (`githash`, `version`), as the export's own metadata record has them, each as escaped display text. Optional members added within version 0.1 (2026-11-10): a report without the option is as before |
| `run` | the run's outcome: `ok` when every slot ended final and the run did not stop, `invalid` when it stopped, `not-run` when the export was not read |
| `stopped` | true when the run stopped on an internal fault (a check threw, or publishing failed), as the text's `internal fault: the run stopped` line says; the run is then `invalid` and the status 5 |
| `declarations` | each declaration in file order: `index` (its place in the export, which identifies it), `name` (escaped display text, as the text shows it), `verdict` (`accepted`, `skipped`, an outcome, or `not-checked`), `fuel` (null when not known); an accepted one's `label`, `axiomBits` (0: none; 1 `propext`, 2 `Classical.choice`, 4 `Quot.sound`, each with Lean's statement, 8 any other axiom) and `notProved` (bit 8 set), with `notProvedBy`, the unlisted axioms' names, when it is true; any other's `diagnostic` (code, reason, site, two numbers, step) |
| `counts` | the declarations by verdict (`skipped` among them since version 0.2), `notChecked` and `notProved`; null when no verdict could be read |
| `fuel` | `perDeclaration`, `total` (of the known), `unknown` (how many are not known) and `top` (the ten that used the most) |
| `input` | declarations, term numbers (two per expression record read in place: the record and the lambda or leaf a let or projection carries; then the store's own nodes), levels and constant references fed, and the stage's names; null when nothing was fed |
| `exitStatus` | the command's [exit status](#exit-status), 0 to 6 |
| `measured` | `microseconds` (wall and CPU of `stage`, `feed`, `check` and `total`; null on a host without clocks), `peakResidentBytes` and `stageBytes` (null when not known), and `engine`, the file name of the Gforth program that ran ([the engine](#the-engine); null outside `bin/leanforth`) |

The engine is in `measured`, not in `settings`: it says how the run was
made, not what it found, and keeping it apart makes the report of a
check on either engine the same but for `measured`.

The parts of a report agree, and the schema states what its keywords
can: status 0 only for a run that ended `ok`, did not stop and listed at
least one declaration, every one accepted or skipped, with every other count 0 and
every fuel known, and under `--strict-axioms` none NOT PROVED; status 6
only under `--strict-axioms`, when every declaration was accepted and at
least one is NOT PROVED; a rejected or invalid declaration, or one not
checked, never leaves the status 0. What it
cannot state, `make test` checks on every report it makes (the schema's
`$comment` lists it): `counts.declarations` is the number of
`declarations` and the sum of the nine verdict counts, each count the
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

### Snapshots (`--save-snapshot` and `--snapshot`)

*Plan task 6.2.5, step SN3 (ADR 0020); a [kernel] and [format] decision
for the owner, not yet through its gate.* Checking all of Lean's `Init`
takes minutes and all of Mathlib hours; a **snapshot** saves a run's
result in one binary file: every name, level, expression and declaration
of the export as the importer stored them, and each declaration's
verdict with what the checked environment keeps for it (its
dependencies, its axioms, the names its check looked up and what each
lookup answered), its fuel and its diagnostic.

```text
leanforth check --save-snapshot two.lfsnap tests/cli/inductive.ndjson
leanforth check --snapshot two.lfsnap
```

The first is an ordinary, final check that also writes `two.lfsnap`
(written as `init.lfsnap.partial`, then renamed, so a failure never
leaves a file that looks complete): the text ends with `snapshot: written
to two.lfsnap`, or `error: the snapshot was not written: …` with that
outcome's exit status when the run did not decide every declaration or
the file could not be written. `--jobs 1` and `--jobs 4` write the same
bytes, and so do two runs of one build.

The second reads no export: it loads the snapshot (every section's
SHA-256 and every record checked; the publisher re-checks every saved
verdict's dependencies, axiom set and names as it publishes it again)
and reports its verdicts, each labelled:

```text
Two: accepted (experimental, not independently audited; from snapshot, not re-checked in this run); axioms: none
Two.first: accepted (experimental, not independently audited; from snapshot, not re-checked in this run); axioms: none
...
6 declarations: 6 accepted
accepted: 6 (experimental, not independently audited); axioms: none
snapshot: two.lfsnap (sha256 9aa54473…), export sha256 5c14b3b4…, verdict version 7, written by LeanForth 03c68bd2…: 6 results taken from it, not re-checked in this run
note: development and research mode: a final run re-checks everything from the
note: export and reads no snapshot; only its results support a claim
```

A declaration not accepted reads, for example, `rejected (from snapshot,
not re-checked in this run)`. The snapshot's SHA-256 is its header's,
which holds every section's: a
user can record it to recognise the file again. A saved verdict is
never a claim: only a final run, which re-checks everything from the
export and reads no snapshot, supports one (the owner's answer to
OQ-3). The exit status follows the verdicts as in a final run. A
snapshot is refused (nothing reported as checked) when it is damaged,
altered or cut short (status 4, `error: invalid: the snapshot was
refused: …` naming the section, and the record when there is one), when
it was written by another verdict version (stale: check the export again,
or see [stale snapshots](#stale-snapshots---snapshot-stale-ok))
or format version or is a layer given without its base (status 2), or for other
settings: `--fuel N` other than the snapshot's (by default its own
fuel is used) or another axiom allowlist (status 4). A snapshot of an
export read with `--any-lean-version` needs that option again. Measured on
all of `Init` (59,349 declarations, `gforth-fast`, a loaded machine): the
file is 132.9 MB, writing it adds about 3 s to the run, and `check
--snapshot` takes 10 s (4.9 s to read and check the file, 1.8 s to feed
the tier to the checker, 2.1 s to publish and compare every slot) at a
peak of 0.69 GB, against 6 minutes to check it with four workers.

With `--json`, a run of a snapshot prints report version 0.3
([`schemas/check-report-0.3.schema.json`](../../schemas/check-report-0.3.schema.json)):
version 0.2's members, `export` null (the export's name when one is
checked against the snapshot), `mode` `development`, a `snapshot`
member (the file, its `sha256`, `formatVersion`, its `verdictVersion`,
`stale` (null, or [for a stale one](#stale-snapshots---snapshot-stale-ok)
this build's verdict version and how many results are stale), the
`export` it was written from with its SHA-256, bytes and lines, the
`manifestSha256`, `base` null, `layers` (each layer loaded on it: its
`file`, `sha256`, `exportSha256`, `base` and `verdictVersion`), the
`information` text of the build that wrote it, and `import`: null, or
with an export the counts `taken`, `checked` (the declarations whose
verdict this run gave) and `otherContent`; null too when the snapshot
was refused), and on each declaration its `provenance`: `snapshot`
(taken from it), `uses-snapshot` (checked in this run but resting on its
results), `checked`, or with a stale snapshot `stale-snapshot` and
`uses-stale-snapshot`. A refused snapshot is a read that failed with
`phase` `snapshot` and lists no declaration. Final runs keep writing
version 0.2, unchanged.

#### A dependent export checked against a snapshot

*Plan step SN4 (ADR 0020 D5); a [kernel] and [import] decision for the
owner, not yet through its gate.* A library built on another -- a
project on Mathlib, say -- is exported with every declaration it uses,
its base's among them. Given a snapshot of the base, `check --snapshot
FILE EXPORT` checks only what the snapshot cannot vouch for:

```text
leanforth check --save-snapshot two.lfsnap tests/cli/inductive.ndjson
leanforth check --snapshot two.lfsnap tests/cli/dependent.ndjson
```

The export is read on into the snapshot's records, so that a record equal
to one of the snapshot is the same number; then, before any check, each
declaration is **taken** from the snapshot when one of the snapshot's
declarations of its name has exactly its content (an inductive block
only whole), a verdict that does not depend on memory or fuel (not
*full*, *invalid* or *exhausted*), and gives the same answer to every
lookup its check made, each asked again here by the checker's own code
over what was taken so far (a lookup that meets a declaration not taken
is no match). Every other declaration is checked as in a final run (with
`--jobs N` too), and labelled as resting on the snapshot when it uses a
taken one. On the test exports the verdicts and counts are those of a
final check of the export (the tests compare both, field by field, and so
did all of `Init` against its own snapshot); only the labels differ.

**Fuel too** (since 2026-11-11, review rvSN4 B1, ADR 0014 Amendment 7):
the fuel a check uses depends only on its declaration and what it reads,
not on what else the run's tier holds (before, it could, through binders
equal up to their names and through terms a check made that matched
other declarations' records), so a taken declaration's fuel, the
snapshot run's, is a final check's, and so is a verdict near the fuel
budget (`tests/cli/cross_snapshot.py` checks nine fixtures, each fresh
and against the others' snapshots; on Mathlib's first million lines
against `Init`'s snapshot all 13,023 declarations used the final check's
fuel). An exhausted verdict is still never taken:

```text
Two: accepted (experimental, not independently audited; from snapshot, not re-checked in this run); axioms: none
...
Eq: accepted (experimental, not independently audited); axioms: none
Two.swap_swap: accepted (experimental, not independently audited; checked in this run, uses results from the snapshot); axioms: none
...
13 declarations: 13 accepted; 6 from the snapshot, 7 checked in this run
...
import: 7 checked in this run; 0 with the name of a declaration of the snapshot, not its content
```

A declaration whose check made names of its own beyond the export (the
auxiliary types `_nested.Array_1` of a nested inductive block) is taken
too since plan step SN5: the snapshot holds those names, written after
the export's, and their lookups are asked again as any other (verdict
version 2; a snapshot of version 1 kept such declarations, and everything
whose lookups reach them, to be checked again). A snapshot refused before
the export is read is reported as above; the export's own failures are
reported as a final run reports them.

Measured (`gforth-fast`, `--jobs 3`, a loaded 10-core machine): all of
`Init` against its own snapshot takes every one of its 59,349
declarations, with every verdict, count and fuel as the fresh check's,
in 49 s against 749 s fresh (most of the 49 s reads the export again:
an exact check always reads it whole). Mathlib's first million lines
against `Init`'s snapshot take 1,108 declarations, 69 s wall against 89 s
fresh but 164 s of CPU against 139 s: loading `Init`'s records and
feeding them cost more than the few checks saved, so a snapshot pays off
for an export that shares much of it.

#### Layered snapshots

*ADR 0020 amendment 1, the owner's decision F5.* With `--snapshot BASE`,
`--save-snapshot LAYER EXPORT` writes a **layer**: only what the run
added to BASE -- the records the export added and the declarations
checked in the run -- numbered on from BASE's, with BASE's identity (its
header's SHA-256) in its header. Further `--snapshot` options load layers
on the first, in order, with or without an export:

```text
leanforth check --snapshot two.lfsnap --save-snapshot dep.lfsnap tests/cli/dependent.ndjson
leanforth check --snapshot two.lfsnap --save-snapshot sib.lfsnap tests/cli/sibling.ndjson
leanforth check --snapshot two.lfsnap --snapshot dep.lfsnap --snapshot sib.lfsnap
```

Base and layer report what the run that wrote the layer reported, and
two layers written on one base load together: a declaration both hold
(here `Eq` and `rfl`) is loaded once when its content and verdicts agree.
The report names each layer loaded, after the snapshot's line (and in
JSON in `snapshot.layers`):

```text
snapshot: two.lfsnap (sha256 9aa54473…), export sha256 5c14b3b4…, verdict version 7, written by LeanForth 03c68bd2…: 13 results taken from it and its layers, not re-checked in this run
layer: dep.lfsnap (sha256 2e727cd4…), export sha256 0a286479…, verdict version 7, on the snapshot above
```

Refused (status 4, nothing listed): a layer written on another base
(`base snapshot of the layer`), a declaration two loaded snapshots hold
with other verdicts, a name two of them declare with other content
(`a name of two snapshots with other content`; any member of an
inductive block counts, a constructor too), as Lean refuses an import
that declares a name twice, and a layer that holds one of its records
twice; a layer given first is refused as `layer`
(status 2). A layer is written on one snapshot only (`--save-snapshot`
with several `--snapshot` options is refused, status 4), and FILE must not
be the snapshot read.

#### Stale snapshots (`--snapshot-stale-ok`)

*A development flag the owner approved (2026-11-11; ADR 0020 amendment
3).* A snapshot written under an older verdict version (the checker's
rules changed since) is refused by default. With `--snapshot-stale-ok`
it loads, and every result taken from it is labelled stale, never as
this build's verdict: `from a stale snapshot (an older verdict version),
not this build's verdict` in the text, with `stale:` lines that count
them, and `stale-snapshot` (or `uses-stale-snapshot` for one checked here
but resting on them) in JSON, where `snapshot.stale` gives the count. A
snapshot of a newer verdict version than this build's is refused still,
the flag needs `--snapshot`, and it does not go with `--save-snapshot`
(a stale verdict is never written into another snapshot). Use it to look
at an old run's results while a new snapshot is being made; only a final
run supports a claim.

#### The snapshot workflow

1. **Save the base once.** A final run of a library writes its snapshot
   (`check --jobs N --save-snapshot mathlib.lfsnap mathlib.ndjson`; every
   full Mathlib run saves one, owner 2026-11-11). The snapshot is valid
   for every LeanForth build of the same verdict version; a bump of the
   verdict version needs it written again (or `--snapshot-stale-ok` for a
   look in the meantime).
2. **Check a dependent library or a slice against it.**
   `check --snapshot mathlib.lfsnap physlib.ndjson` reads the dependent
   export (which holds every Mathlib declaration it uses) on into the
   snapshot's records and checks only what the snapshot cannot vouch for:
   new declarations, edited ones and everything whose lookups reach them.
   A slice of Mathlib itself (an edited file's export) is checked the same
   way.
3. **Keep the dependent result as a layer.** Add `--save-snapshot
   physlib.lfsnap`: the layer holds only what the run added, and
   `--snapshot mathlib.lfsnap --snapshot physlib.lfsnap` loads both; two
   layers on one base load together.
4. **Claims come from final runs only.** A run with `--snapshot` is a
   development and research run; the results it reports, taken or
   checked, are labelled, and fuel and verdicts near the fuel budget are
   not yet guaranteed equal to a final check's (see above).

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
  Statement in LeanForth (as an axiom declaration; the checker did not assume it, running it would):
    axiom composition
      Prop implicit: A
      Prop implicit: B
      Prop implicit: C
      A B -> explicit: f
      B C -> explicit: g
      A C ->
    end composition
  Input:     tests/reference/composition.ndjson line 35
  Checker log: 48 steps, complete. The statement is a proposition: s20 (from s3).

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
  8  This is the statement.                        [definitional equality ← 7]        s46
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
a type with no proof. Printing it assumes nothing, and the verdict printed
above it is the checker's (also for an `Axiom` declaration and for a
rejected one, whose block is printed all the same); running the words would
make an axiom in the authoring program, never in the checker. The words run through
the [authoring words](../programming/LEANFORTH_WORDS.md) to the identical
statement (checked by `tests/present/check_outline.py` for the five pinned
examples; the `Init` example below was not run back). The statement is printed whether or not the declaration was
accepted. A block can be run only after the declarations it mentions: the
constants of an earlier declaration are defined by running that
declaration first (an `import-stub` line stands for one of Lean's).

`--statement FORMS` chooses the forms: `lean`, `mathematics` and
`leanforth`, joined by commas (`--statement lean,leanforth`), or `all`
(the default). `--latex` prints the outlines as LaTeX fragments instead
(see [the proof outline](PROOF_OUTLINE.md#latex)); with `--detail` the
step list is always plain text.

NAME is matched against the name as the term printer spells it, components
joined by dots without « »: `a.b` selects a declaration whose name is the
two components `a` and `b` and also the one-component name `«a.b»`, and a
numeric component matches the same digits as a string component. The name
is shown escaped in the output (so a name holding a line end or a
bidirectional control cannot be written as an argument).

### Writing an export as LeanForth text

`print --lf EXPORT` writes every declaration of the export, in file order,
as one LeanForth text on the standard output: each theorem, definition and
axiom with its statement and value (the proof), as the
[authoring words](../programming/LEANFORTH_WORDS.md) read it back to the
identical terms (checked node for node for the pinned examples, for
`Nat.add_zero` and for a slice of `Init`; see [the proof of
`Nat.add_zero` in LeanForth](PROOF_OUTLINE.md#natadd_zero-in-leanforth)).
The export is not checked and the text is no evidence of anything: it is
untrusted presentation. `--lf` takes `--no-manifest`, `--fuel` and `--fast`,
not `--detail`, `--name`, `--latex` or `--statement` (exit 4).

What the words cannot write yet is never dropped silently and never written
wrongly. Such a declaration becomes a comment line
`\ not written: NAME (reason)` and, so that later declarations that use the
constant still read back, an `import-stub` of the same name, universe
parameters and, when it prints, type (the stub the authoring words use for a
constant of Lean's library: an assumption, not a proof). Each one is also
listed on the standard error with its reason, followed by the counts. The
reasons today (the gaps are follow-ups of plan task 8.6.3):

| Reason | Why |
|---|---|
| an inductive type, constructor, recursor, quotient constant, block header | no inductive declarations in the words yet (ADR 0017, section 14); the stub stands in |
| an opaque constant, an unsafe or partial declaration | the words make safe, regular definitions only |
| more than 8 universe parameters | `lf-decl-universe-capacity` |
| a name, literal or term form the words cannot write | a numeric part in the name of a declaration (Lean's `_private.Init.Prelude.0.x`), a part with a dot, a literal beyond one cell, a string literal (no authoring word for one yet, a follow-up of plan task 5.2.3), a name the text rule bans |
| a term the input does not hold | `let` and metadata, which the checker's input does not store yet (the checker says unsupported) |
| the printer ran out of fuel or room | try a larger `--fuel` |

A declaration that uses a constant with neither text nor stub (a private
name) is itself listed as not written. A constant that no declaration of the
export defines (an invalid export) gets no stub: reading the text back
reports it. A definition's reducibility hint and safety are not in the text
(the words make a regular, safe, unprotected definition).

A limit still to lift: the LeanForth block takes at most 8 universe
parameters (print-forth's `lf-decl-universe-capacity`); a declaration with
more prints "(not complete: unsupported)" instead of the block.

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
  Diagnostic: rejected: argument type mismatch (D1-D5) (0, 0)
  Statement in Lean:        ∀ {A B C : Prop}, (A → B) → (B → C) → A → C
  Statement in mathematics: $\forall \{A\ B\ C : \mathrm{Prop}\},\ (A \to B) \to (B \to C) \to A \to C$
  Statement in LeanForth (as an axiom declaration; the checker did not assume it, running it would):
    axiom composition
      Prop implicit: A
      Prop implicit: B
      Prop implicit: C
      A B -> explicit: f
      B C -> explicit: g
      A C ->
    end composition
  Input:     tests/core/check-declaration-cases/composition-wrong-argument.ndjson line 35
  Checker log: 42 steps, complete. The statement is a proposition: s20 (from s3).

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
| 0 | Every declaration accepted or skipped (or, for the other commands, done); NOT PROVED ones too, as Lean, unless `--strict-axioms` | every verdict *ok* or *skipped* |
| 1 | Something rejected: Lean's kernel rejects it too | *rejected* |
| 2 | Unsupported or unknown: LeanForth cannot decide it yet | *unsupported*, *unknown* |
| 3 | A resource limit: out of fuel or out of room | *exhausted*, *full* |
| 4 | Malformed input: a broken export, a missing or wrong manifest, a file that cannot be opened or created, or a malformed command line | *invalid* |
| 5 | An internal fault: a Forth exception, a check that threw, a failed publication, or Gforth ending in an unexpected way | — |
| 6 | Only with `--strict-axioms`: every declaration accepted, but some NOT PROVED (they depend on an axiom) | *ok* with an axiom |

When the declarations end differently, the most severe status wins, in
the order 5, 4, 1, 3, 2, 6, 0: an internal fault or a malformed export puts
every verdict in doubt; a rejection is Lean's definite "no"; a limit or a
missing feature leaves a declaration undecided; a NOT PROVED declaration
is Lean's "yes" resting on an axiom. By the owner's decision of
2026-11-04 ([owner decisions](../project/OWNER_DECISIONS.md), "0 like
Lean, flag for 6"), a NOT PROVED declaration keeps Lean's status — 0
when everything is accepted — and is marked on its line, in the summary,
in a note and in the JSON report; `--strict-axioms` gives such a run
status 6, so that a script can refuse anything resting on an axiom. Here
`composition` is declared as an axiom, so it rests on itself; then
examples of other statuses, the first a proof that is the string literal
`"3"`, which Lean's kernel rejects too (the file declares no `String`):

```console
$ bin/leanforth check --no-manifest --strict-axioms tests/core/check-declaration-cases/composition-postulate.ndjson; echo "exit status $?"
note: the export's manifest is not checked (--no-manifest)
composition: accepted (experimental, not independently audited); axioms: unlisted; NOT PROVED: depends on composition
1 declaration: 1 accepted
accepted: 1 (experimental, not independently audited); axioms: 1 NOT PROVED (they depend on an axiom)
exit status 6
$ bin/leanforth check --no-manifest tests/core/check-declaration-cases/composition-literal.ndjson; echo "exit status $?"
note: the export's manifest is not checked (--no-manifest)
composition: rejected
  rejected: unknown constant; diagnostic 50 at environment lf-env-lookup: 13 0
1 declaration: 1 rejected
exit status 1
$ bin/leanforth check --fuel 30 tests/reference/composition.ndjson; echo "exit status $?"
composition: exhausted
  fuel exhausted; diagnostic 1 at mixed-infer lf-mixed-infer: 0 0
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
`not checked (not reached: the run stopped)` (verdict *not checked*,
never to be read as *skipped*), and every later check in that context also ends *invalid*
with diagnostic 29. `bin/leanforth` runs one command per process, so this
matters only in a Forth session, which runs its next command in a new
context (`context-new`, `context-use`). It fails closed: nothing is ever
accepted in a spent context.

## Small exports: `check --record` and `replay`

Run records 0.2 hold at most 32 declarations, so these two commands
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
    --no-manifest; a summary, --resources (time, memory, fuel), --json;
    gforth-fast, or Gforth's checking engine with --checked; --jobs N checks
    with N workers (threads on Gforth 1.0), the same output as one
  check: Lean's kernel rules as built so far, each result labelled
    experimental, not independently audited: definitions, theorems, opaque
    declarations and axioms (an axiom outside Lean's standard three is NOT
    PROVED, as Lean's exit status 0); fun, forall, application, let,
    number and string literals, projections, unfolding of definitions;
    proof irrelevance and eta; quotients; inductive types, recursive,
    indexed and mutual ones, with their recursors; unsafe and partial
    declarations skipped, as Lean's replay skips them (5.2.7); several of
    these are merged but their review gates are open
    (docs/project/PROJECT_PROGRESS.md)
  check --record, replay: run records 0.2 and their replay (plan task 2.2.5)
  print: a readable proof outline of each accepted declaration, from the
    checker's derivation log (plan tasks 2.4.1, 2.4.4; untrusted presentation)
  count, reexport: exports of any size, up to all of Mathlib
not yet supported (check answers unsupported or unknown, exit 2):
  nested inductive types (5.2.5b), a block with both safe and unsafe
  members (5.2.7 part b), metadata (mdata) in a term (4.1.3);
  recursor reductions on a variable (a follow-up of 5.2.2),
  so a correct proof can still end unknown;
  check --record and replay (the old reader) refuse inductive types, and
  answer unsupported for let, literals, projections and metadata;
  the checker has not yet checked a Mathlib declaration
  (0 of 729,263)
limits (check answers full or exhausted, exit 3):
  check: stores, walks and lists that grow with the export (memory), any
    depth and number of dependencies or constructors (plan task 6.2.0);
    each check's scratch above the input grows, up to 2147483647
    term nodes, levels and constant references each (plan task 6.2.2)
  check --record, replay: 64 names, 64 levels, 64 term nodes,
    32 declarations per export
  universe parameters per declaration and universe arguments per constant:
    no fixed limit (memory)
  fuel 100000000 steps per declaration (--fuel N, at most 9007199254740991)
  memory per check: none but the heap's (--memory-per-check MB)
planned, not built: program, serve and --record on any size,
  every axiom name of each accepted declaration, as #print axioms
    (plan task 5.3.2; today: the allowlist's names and NOT PROVED's)
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
([run records](../programming/RUN_RECORDS.md), format 0.2, plan task
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
version 0.3 for exports of any size would need is written down in
[run records](../programming/RUN_RECORDS.md#version-03-records-of-any-size),
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
  rejected: argument type mismatch (D1-D5); diagnostic 59 at mixed-infer lf-mixed-infer: 0 0
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
  `Classical.choice` and `Quot.sound` with Lean's statements is marked
  NOT PROVED ([axioms](#what-check-prints)).
- The results are experimental, not independently audited, as long as
  the first checker has not passed its review gate.
- The resource report and the JSON report are untrusted output, like the
  text; fuel, time and memory never change a verdict.

## Gforth

`bin/leanforth` runs the Gforth named by the `GFORTH` environment
variable; otherwise the pinned one in `.tools/gforth` of its checkout
(`scripts/install-gforth.sh`), otherwise `gforth` on the `PATH`. `count`
and `reexport` prefer `gforth-fast`, about 3.3 times faster on large
exports; `check`, `replay` and `print` use `gforth-fast` too, and `--checked` runs
them on Gforth's checking engine, whose stack and memory checks turn a
fault in the checker into an internal fault where it happens
([the engine](#the-engine)). Standard input is closed.
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
outcome's code, the order of severity, NOT PROVED with Lean's status and
with `--strict-axioms`, the record hook, the
fuel each check used, the stage freed and the stores' sizes given back
after every check, two injected internal faults, `print`'s codes, and a
THROW at each of `print`'s store allocations, after which the log is off
and no environment is left) and `tests/cli/test_leanforth.py` (the tool
itself: every exit status with its exact output, from other folders,
tampered and cut exports, every JSON report against its schema and
against the text, the resource report, exact fuel, against the counter and
the re-exporter, with a broken Gforth, the same text and reports on both
engines (`--fast`), and `print`'s outlines against the outline printer's
golden file). `make reference-cli`, part of `make
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

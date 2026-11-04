# The command line: `leanforth`

**Status, 2026-11-03: version 0, experimental** (plan tasks 3.4.1 and
3.4.2). `bin/leanforth` checks a Lean export with LeanForth's first
checker, which has not passed its review gate (`AGENTS.md`) and has not
been audited by an outside Lean expert: every result it accepts is printed
*accepted (experimental, not independently audited)* with the axioms it
depends on. Until the owner approves the checker, Lean's own kernel is the
referee. **Today's check holds small exports only** — 64 names, 64 levels,
64 term nodes and 32 declarations per export — so it works on test
fixtures such as the ones below, and any larger export ends *full*
(exit status 3). The stores themselves now grow (plan task 3.3.1), and
the Forth words that stage an export and feed it to the checker take any
size (all of `Init`; see [NDJSON_READER.md](../development/NDJSON_READER.md#feeding-the-checker)),
but `check` still reads the export with the first reader and keeps its run
record in tables sized for these defaults; moving `check` onto the feed is
the next step.

Every example on this page is run by `make test` (the shell and Forth
examples) and `make check` (the Lean ones), and must print exactly what is
shown.

## Checking a Lean export

From the repository root:

```console
$ bin/leanforth check tests/reference/composition.ndjson
composition: accepted (experimental, not independently audited); axioms: none
1 declaration: 1 accepted
```

`check` reads the export with LeanForth's own reader, written in Forth;
no Python or Lean runs. It first checks the export against its
*manifest*, `tests/reference/composition.ndjson.manifest.json`, which
LeanForth's export step wrote beside it (see [Manifests](#manifests)).
Then it checks every declaration in file order, each with the same
checker and rules as [the first check](FIRST_CHECK.md), and prints one
line per declaration with its verdict, then a summary.

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
| `check [--no-manifest] [--fuel N] [--record RECORD] EXPORT` | Check every declaration of a Lean export, in file order; with `--record`, also write the [run record](#run-records-and-replay) |
| `replay [--no-manifest] [--fuel N] EXPORT RECORD` | Check the export again and compare the new run record with RECORD; print the replay report |
| `print [--no-manifest] [--fuel N] [--detail] [--name NAME] EXPORT` | Check the export and print each accepted declaration's [readable proof](#printing-a-readable-proof), or with `--detail` every step of the checker's log; `--name` prints one declaration |
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
  check that runs out ends *exhausted*.
- `--record RECORD` writes the run record of the check to RECORD
  ([run records and replay](#run-records-and-replay)); RECORD must not be
  the export.
- `--detail` (`print` only) prints every step of the checker's log
  instead of the outline; `--name NAME` (`print` only) prints only the
  declaration named NAME.

`EXPORT` and `COPY` are file names relative to the current folder; the
tool works from any folder, and gives the same bytes on every run:

```console
$ cd tests && ../bin/leanforth check reference/composition.ndjson
composition: accepted (experimental, not independently audited); axioms: none
1 declaration: 1 accepted
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
and two numbers that the catalogue explains. Then a summary line counts
the verdicts, and notes explain a limit that was reached.

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
  undecided: terms or levels differ; diagnostic 30 at mixed-convert lf-mixed-convert: 16 10
2 declarations: 1 accepted, 1 unknown
exit status 2
```

Here *unknown* is honest, not a rejection: the proof is correct, and Lean
accepts it, but checking it needs the definition of `Implies` unfolded,
which the first checker does not do yet (plan phase 4):

```lean
def Implies (A B : Prop) : Prop := A → B

theorem impliesSelf {A : Prop} : Implies A A := fun a => a

#print axioms impliesSelf
```

```text
'impliesSelf' does not depend on any axioms
```

## Printing a readable proof

`print` checks the export exactly as `check` does, one declaration at a
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
  Statement: ∀ {A B C : Prop}, (A → B) → (B → C) → A → C
  Input:     tests/reference/composition.ndjson line 35
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
Rules, formulas and step numbers come from the checker's log; the sentences are
fixed templates (structured-template), not checked reasoning.
Templates: let-props/v0, assume/v0, implies-elim/v0, discharge/v0, statement/v0.

exit status 0
```

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
  Statement: ∀ {A B C : Prop}, (A → B) → (B → C) → A → C
  Input:     tests/core/check-declaration-cases/composition-wrong-argument.ndjson line 35
  Checker log: 67 steps, complete. The statement is a proposition: s26 (from s3).

No proof outline: the declaration was not accepted.

exit status 1
$ bin/leanforth print --name fixtureUse tests/reference/constant-fixture.ndjson | head -3
Theorem fixtureUse
  accepted (experimental, not independently audited); axioms: none
  Statement: ∀ {P : Prop}, P → P
$ bin/leanforth print --name noSuch tests/reference/constant-fixture.ndjson; echo "exit status $?"
error: no declaration named noSuch
exit status 4
```

Exit status of `print`: 0 when every declaration printed has its outline
(or, with no template for its proof, its steps); otherwise the status of
the [outcomes](#exit-status) of the declarations that were refused, 3
for a log that ran out of room, 4 for a name no declaration has, 5 when
the run stopped. The outline is untrusted presentation: the verdict comes
from the checked environment, as `check`'s does, and nothing `print`
writes can make a declaration accepted.

## Exit status

| Status | Meaning | Comes from |
| --- | --- | --- |
| 0 | Every declaration accepted (or, for the other commands, done) | every verdict *ok* |
| 1 | Something rejected: Lean's kernel rejects it too | *rejected* |
| 2 | Unsupported or unknown: LeanForth cannot decide it yet | *unsupported*, *unknown* |
| 3 | A resource limit: out of fuel or out of room | *exhausted*, *full* |
| 4 | Malformed input: a broken export, a missing or wrong manifest, a file that cannot be opened or created, or a malformed command line | *invalid* |
| 5 | An internal fault: a Forth exception, a check that threw, a failed publication, or Gforth ending in an unexpected way | — |

When the declarations end differently, the most severe status wins, in
the order 5, 4, 1, 3, 2, 0: an internal fault or a malformed export puts
every verdict in doubt; a rejection is Lean's definite "no"; a limit or a
missing feature leaves a declaration undecided. Only status 0 means every
declaration was accepted. One example of each status other than 0:

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
`make test` injects one while an export is read and one inside a check.

## Small exports only

The stores the first checker uses hold 64 names, 64 levels and 64 term
nodes — the export's own and each check's working terms together — and 32
declarations. The fixtures fit. A correct theorem only a little longer
does not: `tests/cli/chain.lean` chains twelve implications (Lean accepts
it, without axioms), and its export has 81 expression records:

```console
$ bin/leanforth check tests/cli/chain.ndjson; echo "exit status $?"
error: full: too many expression nodes or constant references for the check's stores (line 97)
note: today's check holds at most 64 names, 64 levels, 64 term nodes and 32 declarations per export,
note: so only small exports, such as the test fixtures, fit; larger ones end full
exit status 3
```

Nothing is checked then: the export did not fit, so no verdict is given.
`count` and `reexport` have no such limit; they read all of Mathlib.
`capabilities` lists every limit and every unsupported feature:

```console
$ bin/leanforth capabilities
leanforth 0.1.0-dev: what this build can do
supported:
  check: Lean 4.35.0 exports (lean4export 3.1.0 NDJSON), read in Forth;
    the manifest checked unless --no-manifest
  check: definitions and theorems built from Sort, variables, application, fun,
    forall and earlier accepted declarations (the first checker, ADR 0011);
    an accepted one is labelled experimental, not independently audited
  check --record, replay: run records 0.1 and their replay (plan task 2.2.5)
  print: a readable proof outline of each accepted declaration, from the
    checker's derivation log (plan tasks 2.4.1, 2.4.4; untrusted presentation)
  count, reexport: exports of any size, up to all of Mathlib
unsupported (check answers unsupported, exit 2):
  axioms, opaque declarations, unsafe and partial definitions;
  let, literals, projections and metadata in a term;
  inductive types, quotients and mutual blocks (refused while reading)
  unfolding definitions: some correct proofs end unknown (exit 2)
limits (check answers full, exit 3; small exports only):
  64 names (2048 bytes), 64 levels, 64 term nodes, 32 declarations per export
  64 universe parameters per declaration, 64 universe arguments per constant
  16 dependencies per declaration, 64 per export
  fuel 100000 steps per declaration (--fuel N)
planned, not built: program, serve, --json receipts,
  larger stores (plan task 3.3.1)
```

An export that uses something unsupported while being read, such as an
inductive type, stops there:

```console
$ bin/leanforth check --no-manifest tests/core/reexport/kinds.ndjson; echo "exit status $?"
note: the export's manifest is not checked (--no-manifest)
error: unsupported: an inductive type (not supported yet) (line 51)
exit status 2
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
`check` reads the export in two passes (names first, then terms and
declarations) and compares each with the manifest; the two passes must
also have read the same bytes, else the export is refused as invalid with
"the export changed between the two passes", so a file replaced while
`check` reads it cannot pair the names of one file with the terms of
another:

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
those of `check` alone; a record that cannot be written is reported and
the status is then at least 4. A record costs reads: with `--record` (and
in `replay`) the export is read before the check for its SHA-256, its
metadata and its manifest, and once more after the check to see that it
did not change, besides the checker's own read. Without `--record`,
`check` reads the export only as the checker needs it (the importer's two
passes, with the manifest checked unless `--no-manifest`), so a plain check of a large
export pays nothing for records (`tests/cli/leanforth.fs` checks that no
record read happens then). `replay EXPORT RECORD` checks the export
again in the same way and compares the new record with RECORD, field by
field; its output is the replay report, one JSON line:

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
  wrong.
- A declaration that uses one that was not accepted is never accepted:
  it ends *unknown* or *unsupported*.
- The results are experimental, not independently audited, as long as
  the first checker has not passed its review gate.

## Gforth

`bin/leanforth` runs the Gforth named by the `GFORTH` environment
variable; otherwise the pinned one in `.tools/gforth` of its checkout
(`scripts/install-gforth.sh`), otherwise `gforth` on the `PATH`. `count`
and `reexport` prefer `gforth-fast`, about 3.3 times faster on large
exports; `check` uses the `gforth` engine. Standard input is closed.
`bin/leanforth version` adds the checkout's git commit to the versions:

```console
$ bin/leanforth version | sed -n '1p;3p'
leanforth 0.1.0-dev (development version; experimental, not independently audited)
reads: lean4export 3.1.0, format 3.1.0, Lean 4.35.0 (eb6cafb7290e8bd5f2937522d8d804f58f02bafc)
```

## Not built yet

`program` (a program receipt), `serve` (the JSON-RPC interface for AI
tools, plan section 3.5), `--json` receipts (task 3.4.3), Markdown, LaTeX
and JSON forms of `print`'s outline (tasks 2.4.4 and 8.6.1) and larger
stores (task 3.3.1).

## Tests

`make test-cli` runs `tests/cli/leanforth.fs` (the Forth side: every
outcome's code, the order of severity, the record hook, two injected
internal faults, and `print`'s codes and refusals, a truncated log
included) and `tests/cli/test_leanforth.py` (the tool itself: every exit
status with its exact output, from other folders, against the counter and
the re-exporter, with a broken Gforth, and `print`'s outlines against the
outline printer's golden file). `make
reference-cli`, part of `make check`, has pinned Lean accept
`tests/cli/chain.lean` and `unfold.lean` and has `scripts/export.sh`
reproduce their committed exports and manifests byte for byte. The
examples on this page run in `make test` and `make check`.

## See also

- [First check](FIRST_CHECK.md): the same check from the inside, step by
  step.
- [For AI tools](AI_TOOLS.md): the command line among the other
  interfaces, and the rules for reporting its results.
- [Diagnostics](../programming/DIAGNOSTICS.md): every reason code.

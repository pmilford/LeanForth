# Verifying one Forth word: `leanforth verify` (V1)

**Status (2026-11-13): plan steps 8.4.1b (the driver), 8.4.1c (the
command and its report) and 8.4.1d (replay and tampering) written and
tested alone; this page is 8.4.1n's user guide.** Nothing here is called
done: the done checker's run (the list [below](#the-done-check)) and the
owner's gates ([bypass] for b and d, [format] for c, [parser] for the
contract translation) come first. `leanforth capabilities` and `leanforth
help` do not list `verify` yet: that is a change to the Forth command
line (`src/cli/leanforth.fs`) with its own Forth review. The design is
[VERIFY_COMMAND.md](../design/VERIFY_COMMAND.md); the owner's answers of
2026-11-13 are in [OWNER_DECISIONS.md](../project/OWNER_DECISIONS.md).

**Who proves what.** Lean 4.35.0 writes every proof, from the tactic
scripts of the untrusted generator (`scripts/program_vc.py`); Lean's
exporter writes the proofs with every declaration they use; LeanForth's
checker (`bin/leanforth check`, a final run) re-checks that export and is
the only judge. LeanForth writes no proof. A receipt is about the word's
IR, under the assumptions it lists, and never about the compiled code or
the Forth system that runs it. V1 needs Python 3 and the pinned Lean
4.35.0 (the owner allowed both for V1 only); V2 checks proofs a user
supplies with Forth alone.

## One example in three forms

**Mathematics.** For integers v, l, u that fit in a cell: if l > u,
`lf-clamp` leaves *false*; if l ≤ u it leaves r = min(max(v, l), u) and
*true*, so l ≤ r ≤ u. The cells below its inputs are kept, for every cell
width.

**Forth** ([`src/program/clamp.fs`](../../src/program/clamp.fs)), with its
contract [`tests/program/contracts/lf-clamp.contract`](../../tests/program/contracts/lf-clamp.contract)
in contract language 0.1 ([PROGRAM_VC.md](PROGRAM_VC.md#the-contract-language-version-01)):

```forth
: lf-clamp ( value lower upper -- result true | false )
  2dup > if 2drop drop false exit then
  >r max r> min true ;
```

**Lean**, the contract theorem as pinned Lean printed it in the run below
(`--detail` shows it, with `post`; stacks are top first, `-1` is Forth's
*true*):

```lean
THEOREM
```

## A first run, step by step

1. Write the contract next to the word, with an `ir` line naming a file
   inside the checkout, for example `ir tests/program/ir/clamp.ir`.
2. `bin/leanforth verify src/program/clamp.fs --contract C --write-ir`
   writes the IR the program words write for the source to that file and
   does nothing else. Read it: it is what the proofs are about.
3. `bin/leanforth verify src/program/clamp.fs --contract C` runs every
   step and writes the receipt to `verify-out/lf-clamp/` (or `--out DIR`).
4. `bin/leanforth verify --replay verify-out/lf-clamp/lf-clamp.receipt.json`
   later checks that the receipt is still what its files and evidence
   give; `--rerun` runs every step again.

```sh
bin/leanforth verify SOURCE.fs --contract CONTRACT [--out DIR] [--json] [--detail]
    [--fuel N] [--jobs N] [--memory-per-check MB] [--checked]
    [--lean-time-limit SECONDS] [--keep-export] [--paths-limit N] [--search-limit N]
bin/leanforth verify SOURCE.fs --contract CONTRACT --write-ir
bin/leanforth verify --replay RECEIPT [--rerun] [--json]
```

`python3 scripts/program_verify.py` with the same arguments is the same
command. SOURCE.fs, CONTRACT, `--out` and RECEIPT must lie inside the
LeanForth checkout (receipt 0.3 names files relative to it).

| Option | Meaning |
| --- | --- |
| `--contract FILE` | the contract (`lf-contract 0.1`); it names the word, which SOURCE.fs must define |
| `--out DIR` | where the files go; default `verify-out/WORD` in the current folder (ignored by git) |
| `--json` | print one JSON report ([below](#the-json-report)) instead of the text |
| `--detail` | also print the theorem and `post` as Lean printed them in this run: what is proved, to compare with the contract's lines |
| `--write-ir` | write the IR of SOURCE.fs to the file the contract's `ir` line names, and stop |
| `--replay RECEIPT`, `--rerun` | [replay](#replay-and-tampering) a receipt; with `--rerun` run every step again and compare |
| `--fuel N`, `--jobs N`, `--memory-per-check MB`, `--checked` | passed to LeanForth's check as for `bin/leanforth check` (`--jobs` default 2) |
| `--lean-time-limit S` | Lean's time limit for its compile and for its export, each (default 1800 s) |
| `--keep-export` | keep the export (about 23 MB); by default it is removed, by name, and the manifest kept |
| `--paths-limit N`, `--search-limit N` | the generator's limits: at most N paths (default 256; paths double with each IF), at most N candidate inputs tried (default 250,000; 12 values per input, 12³ = 1,728 for clamp) |

No option weakens what is checked: there is no way to skip a step, the
manifest check or the axiom comparison. Gforth is `GFORTH`, else the
checkout's, else on the PATH; Lean and its `leanexport` are always the
checkout's pinned toolchain (`scripts/install-lean.sh`): `LEAN` and
`LEANEXPORT` are ignored except under `LEANFORTH_VERIFY_TEST_TOOLS=1`,
which only the test suites set (stand-ins, the Lean cache), and the
evidence record says which tools ran, with their SHA-256.

## What it prints

Run on 2026-11-13 by `tests/program/verify_lean_check.py --all` (each Lean
run about 100 s on two workers with other agents running, nearly all of
it LeanForth's check of the IR semantics' closure; what it printed is
kept in `build/verify-lean/NAME/verify.out`):

```text
$ bin/leanforth verify src/program/clamp.fs --contract tests/program/contracts/lf-clamp.contract --out build/verify-lean/lf-clamp; echo "exit status $?"
CLAMP
exit status 0
```

A wrong contract (MAX and MIN exchanged), refuted: LeanForth's checker
accepted Lean's proof that the contract is false.

```text
$ bin/leanforth verify src/program/clamp.fs --contract tests/program/contracts/wrong-clamp-swapped.contract --out build/verify-lean/wrong-clamp-swapped; echo "exit status $?"
SWAPPED
exit status 1
```

When no obligation is settled, the summary says `NOT VERIFIED: open` and
lists each open obligation in plain words; exit status 2 (or 3, 5 by the
cause). A success says `discharged`, never a bare "verified".

## The JSON report

`--json` prints one JSON text, `leanforth-verify-report` version 0.1
([`schemas/verify-report-0.1.schema.json`](../../schemas/verify-report-0.1.schema.json),
within the subset of `tests/support/schema_subset.py`; a draft for the
[format] gate). Every member but `measured` is the same on every run with
the same inputs and tools. A command-line mistake is still reported as
text (`error: usage: ...`, status 4).

| Member | Contents |
| --- | --- |
| `schema`, `schemaVersion` | `leanforth-verify-report`, `0.1` |
| `mode` | `lean` (a run), `replay`, `rerun` |
| `word` | `name`, `stackEffect`, `source` (`path`, `line`, `sha256`), `ir` (`version`, `sha256`); null without a receipt |
| `contract` | `id`, `path`, `sha256`, `lean` (the contract theorem's name), `theorem` and `post` as Lean printed them in this run (null when Lean did not run) |
| `steps` | each step run, in order: `step` and `outcome` (`ok` or the first problem's code) |
| `obligations` | each: `id`, `statement`, `status`, `theorem`, LeanForth's `verdict` and `axioms` |
| `searchNotes` | the counterexample search's notes |
| `check`, `verify`, `run` | the receipt's three statuses (null without a receipt) |
| `receipt` | `path`, `schemaVersion`, `sha256` of the receipt written, or null |
| `problems` | each problem: `code`, `step`, `message`, in the order found |
| `exitStatus` | 0 to 6, the command's |
| `measured` | `millisecondsPerStep` |

The report repeats the receipt's statuses and names it by its hash: the
receipt is the record of the claim.

## The steps

| Step | What the driver does | Trusted? |
| --- | --- | --- |
| command-line | The options; the paths must lie inside the checkout | untrusted driver |
| read-word | The program words (`src/program/verify.fs`, ADR 0019) write the IR of the whole source file, or refuse a token with its diagnostic; the file is hashed before and after | `trusted-reader` (tested, not proved) |
| read-contract | The contract read (its refusals are in [PROGRAM_VC.md](PROGRAM_VC.md#the-contract-language-version-01)), its word found in the IR, the files an earlier run wrote in `--out` removed by name, and the contract's `ir` file required to be the IR just written, byte for byte | untrusted |
| generate | An IR 0.2 word refused (receipt 0.4 awaits the owner); the generator, for this contract alone and within its limits, writes the obligations, the contract theorem and their tactic scripts, or the theorem `refuted` | `untrusted-generator` |
| prove | Pinned Lean compiles the file (warnings are errors, `autoImplicit` off) inside `--out`, so the module name its private names carry is `obligations` whatever the folder; it prints the program back (it must equal the IR), the theorem with its `pre` hypotheses and `post` as it elaborated them (recorded with their SHA-256), and `#print axioms`; `scripts/export.sh` exports the theorems with their closure and the manifest | `trusted-lean` |
| check | `bin/leanforth check --json`, a final run: its report must be check report 0.4 with no snapshot; the export and manifest hashed before and after; the export's `ProgramVC` declarations exactly the generator's, with only Lean's `_proof_N`/`_simp_N` lemmas under them. The check status from every declaration's verdict, each kind a problem of its own; a rejection is the two checkers disagreeing; each accepted theorem's axioms must equal Lean's | `trusted-leanforth`, the only judge |
| write | The receipt built and read by the strict reader, then the evidence record and the receipt each written to a `.partial` file renamed when complete; the export removed unless `--keep-export` | untrusted; the reader checks it |

## The receipt

Schema 0.3 ([PROGRAM_RECEIPTS.md](PROGRAM_RECEIPTS.md)), statuses set only
from LeanForth's report and the generator's summary:

| Situation | check | verify | Exit status | Receipt |
| --- | --- | --- | --- | --- |
| LeanForth accepted every declaration, the contract theorem and every obligation's theorem among them, each with allowlisted axioms equal to Lean's | `accepted-by-leanforth` | `discharged` | 0 | yes |
| A counterexample, and LeanForth accepted the theorem `refuted` | `accepted-by-leanforth` | `refuted` | 1 | yes |
| A declaration rejected: Lean accepted it, so the checkers disagree | `rejected` | `open` | 5 | yes |
| A declaration unknown or unsupported | `unsupported` | `open` | 2 | yes |
| The check did not finish: out of fuel or room (3); invalid, not checked, a stopped run, no report (5) | `failed` | `open` | 3 or 5 | yes |
| Lean failed on the generated file, or ran out of time | `not-checked` | `open` | 2 or 3 | yes |
| The generator cannot make obligations (loops, recursion, literals outside −1…1) | `not-checked` | `unsupported` | 2 | yes |
| An IR 0.2 word (the SHA helper words) | — | — | 2 | no: needs receipt 0.4 |
| A theorem NOT PROVED (an axiom outside the allowlist) | — | — | 6 | no: 0.3 has no status for it |
| LeanForth's axioms not Lean's; the program printed back not the IR; the export's `ProgramVC` declarations not the generator's; a report not a final run's 0.4 | — | — | 5 | no |
| The source, the contract, the IR file or a tool refused; a limit of the generator | — | — | 2, 3 or 4 | no |

RUN is `not-run`, label *not run*, until plan 8.4.2. A receipt lists every
theorem with its own axioms, the assumptions that apply (`trusted-lean`
only when Lean elaborated the file, `trusted-leanforth` only when
LeanForth accepted; the generator's assumption says the contract's
translation into `post` is not checked and names `post`'s SHA-256), the
tools, and the hashes of the source, the IR, the contract, the generated
Lean file, `scripts/program_vc.py`, `scripts/export.sh`, the export's
manifest and the evidence record. It never has a `verified` field and
never says LeanForth proved anything. Beside it, `WORD.evidence.json`
records what the run found: Lean's version, its prints of the theorem and
of `post` with their SHA-256, its axiom reports, the export's hash,
LeanForth's version, counts and verdicts, the generator's summary with
its search notes, the options that can change a result, and each tool by
path and SHA-256. The receipt names the record with its SHA-256 in its
provenance note, and in `check.evidence` when something was checked.

**Files in `--out`:** `obligations.lean`, `WORD.ndjson` (removed after the
check unless `--keep-export`), `WORD.ndjson.manifest.json`,
`WORD.evidence.json`, `WORD.receipt.json`, WORD with characters outside
letters, digits, `_ . -` written `_`. As soon as the contract names the
word, the driver removes these names (and their `.partial` files) left by
an earlier run, and nothing else; a run that stops leaves no receipt.

## Replay and tampering

`--replay RECEIPT` reads the receipt strictly, checks the evidence record
it names by its SHA-256, runs the generator again (no Lean, no LeanForth)
and requires its summary and the generated Lean file to be the recorded
ones, requires the manifest to be the recorded export's, and rebuilds the
receipt from the files it names as they are now and that record: every
field that differs is a problem `replay`, exit 1. `--rerun` also runs
every step again into a scratch folder of `build/` and compares the new
receipt and the new evidence record with the old ones.

| What changed after the receipt | Caught by | Exit |
| --- | --- | --- |
| The source, the contract, the contract's IR file | `--replay`: the rebuilt receipt's hashes, or the generator no longer running | 1 |
| The generated Lean file | `--replay`: not the file the generator writes | 1 |
| The manifest | `--replay`: its hash, or not the recorded export's | 1 |
| The evidence record | `--replay`: its SHA-256 in the receipt | 1 |
| A theorem's axioms, an assumption, a count in the receipt | `--replay`: the rebuilt receipt | 1 |
| A status, an added `verified` field, a duplicate id, a path outside the checkout, an unknown or superseded version, a duplicate key, a missing file | the strict reader, its schema and rules | 4 |
| A receipt that `leanforth verify` did not write | `--replay` | 1 |
| The receipt and its evidence record changed together, consistently | only `--replay --rerun` | 1 |

## Exit statuses and problem codes

The CLI's statuses, the most severe first when several apply: 5, 4, 1,
3, 2, 6, 0 (verdicts of several kinds give one problem each). Each problem
prints `error: CODE: MESSAGE`; a run that writes no receipt ends with
`WORD: NOT VERIFIED: CODE; no receipt written`. Any status of the Python
interpreter outside 0 to 6 (Python missing, a crash) is 5 at
`bin/leanforth verify`, and an exception the driver does not catch is 5,
never 1. `tests/program/test_program_verify.py` reaches every code and
checks that each is listed here.

| Code | Status | Step | Meaning |
| --- | --- | --- | --- |
| `usage` | 4 | command-line | a command-line mistake |
| `outside-folder` | 4 | command-line | a path outside the checkout, or one receipt 0.3 cannot name |
| `gforth-not-found` | 4 | read-word | Gforth cannot be started |
| `source-unreadable` | 4 | read-word | the source file cannot be read |
| `source-refused` | 2, 4 or 3 | read-word | the program words refused the source: unsupported (2), invalid (4), full, for example a path of about 90 characters or more (3) |
| `source-changed` | 4 | read-word | the source changed while the program words read it |
| `contract-unreadable` | 4 | read-contract | the contract cannot be read, or is not UTF-8 |
| `contract-malformed` | 4 | read-contract | the contract reader refused it, or its `ir` line names no file inside the checkout |
| `word-not-found` | 4 | read-contract | the source defines no word the contract names |
| `contract-ir-differs` | 4 | read-contract | the contract's `ir` file is missing or is not the IR the program words write (`--write-ir` writes it) |
| `ir-needs-receipt-0.4` | 2 | generate | an IR 0.2 word |
| `generator-unsupported` | 2 | generate | the generator cannot make obligations (a receipt says `unsupported`) |
| `paths-limit` | 3 | generate | more paths than `--paths-limit` |
| `search-limit` | 3 | generate | more candidate inputs than `--search-limit` |
| `lean-not-found` | 4 | prove | no pinned Lean, or not Lean 4.35.0 |
| `lean-failed` | 2 | prove | Lean failed on the generated file: nothing checked, every obligation open |
| `lean-time-limit` | 3 | prove | Lean's compile or export ran over `--lean-time-limit` |
| `program-print-back-differs` | 5 | prove | the program Lean printed back is not the IR |
| `export-failed` | 5 | prove | `scripts/export.sh` failed or wrote no manifest |
| `file-changed` | 4 | prove, check | the generated file changed while Lean read it, or the export or manifest while LeanForth checked it |
| `export-invalid` | 4 | check | LeanForth refused to read the export |
| `export-differs` | 5 | check | the export's `ProgramVC` declarations are not exactly the generator's |
| `checkers-disagree` | 5 | check | LeanForth rejected a declaration Lean had accepted |
| `proof-undecided` | 2 | check | a declaration unknown or unsupported |
| `proof-exhausted` | 3 | check | a declaration out of fuel or room |
| `not-proved` | 6 | check | a theorem accepted but resting on an axiom outside the allowlist |
| `axioms-differ` | 5 | check | LeanForth's axioms for a theorem are not Lean's `#print axioms` |
| `internal` | 5 | any | a fault: a tool ending unexpectedly, no check report or one not a final run's 0.4, a stopped or unfinished check, a missing print, the driver's own fault |
| `receipt-not-written` | 4 | write | the `--out` folder or a file in it cannot be written |
| `unreadable`, `not-strict-json`, `superseded-version`, `unknown-version`, `schema`, `rule` | 4 | replay | the receipt reader's codes ([PROGRAM_RECEIPTS.md](PROGRAM_RECEIPTS.md#reading-a-receipt)) |
| `replay` | 1 | replay | a field, file or record differs from what the receipt says |

`expect` in a contract is a test annotation: when the outcome differs the
driver prints `note: the contract expects X; verify found Y`. The search
prints `note: search: no candidate meets pre` when no candidate input
satisfies the `pre` lines and `note: search: inputs no case covers: …`
when some meet no case's guard; neither changes the outcome.

## Differences from the design

What V1 does otherwise than [VERIFY_COMMAND.md](../design/VERIFY_COMMAND.md)
says (review L1, 2026-11-13), for the [format] gate:

| Design | V1 |
| --- | --- |
| §4: a theorem rejected is `proof-rejected`, exit 1 | `checkers-disagree`, exit 5 (owner, 2026-11-13); `proof-rejected` returns with supplied proofs (V2) |
| §4, §6.3 codes | added: `search-limit`, `file-changed`, `export-differs`, `checkers-disagree`; removed: `proof-rejected` |
| §2 options | added: `--paths-limit`, `--search-limit`, `--write-ir` (review M6); `--detail` prints Lean's own theorem and `post` |
| §6.1 text | no `(if @13:10 taken)` path positions on obligations (the generator keeps no IR locations) |
| §6.4 JSON report | `contract.theorem` added; `measured` is milliseconds per step; `mode` also `replay`, `rerun`; `searchNotes` added |
| §6.5 receipt | a refuted contract's receipt has one obligation `O1`, `refuted`, naming the theorem `refuted` (schema 0.3 needs a settled obligation); the evidence record named by hash |
| §8 files | as listed above; Lean runs inside `--out` |
| §3.2 contract | the reader refuses more than contract 0.1's text says (hidden lines, repeated lines and inputs, no case, unbound names; review B1 and its probe); the statement never enters the Lean file |
| §5 tools | `LEAN` and `LEANEXPORT` only under the test switch; each tool's SHA-256 in the evidence |
| §2 `capabilities`, `help` | not yet: a Forth change to `src/cli/leanforth.fs` with its own review |

## Limits and resources

- The generator: its two limits; loops, recursion, literals outside −1…1
  and stack effects deeper than the declared inputs are unsupported.
- Time: about 100 s per word with Lean, 10 s of it Lean's compile and
  export, the rest LeanForth's check of the 4,277 to 4,295 declarations;
  under a second without Lean (unsupported, refused).
- Disk: the export is about 23.6 MB, removed after the check.
- The program words: lines under 128 characters, source paths under about
  90 characters.
- A time limit or a signal stops the tool that runs and everything it
  started.

## Results (the plan's acceptance, 2026-11-13)

`python3 tests/program/verify_lean_check.py --all` ran every committed
contract through `bin/leanforth verify` with pinned Lean and LeanForth
(`--jobs 2`):

| Contract | Word | Outcome | Exit status |
| --- | --- | --- | --- |
| `lf-clamp`, `lf-checked-add`, `lf-checked-abs`, `lf-in-range` | the four words | `accepted-by-leanforth`, `discharged` | 0 |
| `wrong-clamp-swapped`, `wrong-checked-add-total`, `wrong-in-range-exclusive` | clamp, checked add, in-range | `accepted-by-leanforth`, `refuted` | 1 |
| `lf-gcd`, `lf-factorial` | the loop words | `not-checked`, `unsupported` | 2 |
| `sha-rotr`, `sha-ch`, `sha-maj`, `sha-big-sigma0` | the SHA helper words | refused, `ir-needs-receipt-0.4`, no receipt | 2 |

Every receipt is read by the strict reader and equals its golden copy in
[`tests/program/verify/golden/`](../../tests/program/verify/golden/) but for
its date, `--out` folder and evidence hash.

## Tests

- `make test` (`test-program-verify-driver`, `-driver-input`, `test-program-verify-command`):
  [`tests/program/test_program_verify.py`](../../tests/program/test_program_verify.py)
  with the real program words and generator and
  [`tests/program/verify/fake_lean.py`](../../tests/program/verify/fake_lean.py)
  standing in for Lean, its exporter and LeanForth's checker (the checker
  only inside the test's own process). Every outcome, status and code;
  malformed command lines, sources, contracts and IR files; the limits;
  tools missing or of another version; files changed during the run; the
  report against its schema; `--write-ir`; `bin/leanforth verify`; replay
  and every tampering of the table above; two runs giving the same bytes.
  `tests/program/vc_check.py` holds the contract reader's hostile corpus.
- `make check` (`reference-program-verify-clamp`, `reference-program-verify-refuted`):
  `lf-clamp` and `wrong-clamp-swapped` end to end through `bin/leanforth
  verify` against their golden receipts.
- `make reference-program-verify-all`: all thirteen contracts (about 13
  minutes; not part of `make check`).
- Planted faults in `tests/mutants/faults.toml` (`verify-…`, `vc-…`,
  `leanforth-verify-…`), each caught by a named test or listed as
  equivalent with its reason.

## The done check

What the done checker runs for V1 (plan 8.4.1n), each with its expected
end:

| Command | Expected |
| --- | --- |
| `bin/leanforth verify src/program/clamp.fs --contract tests/program/contracts/lf-clamp.contract --out build/done/clamp` | `discharged`, exit 0, a receipt the strict reader accepts |
| the same with `--json` | one report valid against `schemas/verify-report-0.1.schema.json`, `exitStatus` 0 |
| `bin/leanforth verify src/program/clamp.fs --contract tests/program/contracts/wrong-clamp-swapped.contract --out build/done/wrong` | `NOT VERIFIED: refuted`, exit 1 |
| `bin/leanforth verify src/program/examples.fs --contract tests/program/contracts/lf-gcd.contract --out build/done/gcd` | `NOT VERIFIED: unsupported`, exit 2 |
| `bin/leanforth verify src/program/clamp.fs --contract tests/program/verify/hostile-statement.contract` | `contract-malformed`, exit 4, nothing written (the hostile contract of review B1) |
| `bin/leanforth verify --replay build/done/clamp/lf-clamp.receipt.json` | exit 0; then, after a byte appended to the evidence record, exit 1 with `replay` |

## What it does not do yet

`capabilities` and `help` entries (a Forth change); the statement fixed by
LeanForth and supplied proofs (8.4.1e–f); contracts read in Forth
(8.4.1g); the receipt written in Forth (8.4.1h); `sorry` (8.4.1i, 0.5);
files outside the checkout (8.4.1j); IR 0.2 words (8.4.1k); proofs by
LeanForth's tactics (8.4.1l–m); RUN (8.4.2). Loop words need invariants
(plan 4.4.1) or proofs supplied by hand (V2).

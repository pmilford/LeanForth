# Verifying one Forth word: the driver of `leanforth verify`, v0

**Status (2026-11-13): written and tested alone (plan 8.4.1b).** The driver
`scripts/program_verify.py` runs the whole pipeline of plan 5.5.1 for one
Forth word and one contract, any word of an IR 0.1 file inside the
LeanForth checkout, and writes a receipt (schema 0.3). It is not yet a
`bin/leanforth` command: `leanforth verify`, its options, text and JSON
report are plan 8.4.1c, after the owner's questions 3 and 5 of the
[design](../design/VERIFY_COMMAND.md#13-questions-for-the-owner); replay
and tampering of these receipts are 8.4.1d. The design of every step is
[VERIFY_COMMAND.md](../design/VERIFY_COMMAND.md); this page says what the
driver does today.

**Who proves what.** Lean 4.35.0 writes every proof, from the tactic
scripts of the untrusted generator (`scripts/program_vc.py`); Lean's
exporter writes the proofs with every declaration they use; LeanForth's
checker (`bin/leanforth check`, a final run) re-checks that export and is
the only judge. LeanForth writes no proof. A receipt is about the word's
IR, under the assumptions it lists, and never about the compiled code or
the Forth system that runs it.

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

**Lean** (what the generator writes into `OUT/obligations.lean` and Lean
proves; stacks top first, `-1` is Forth's *true*):

```lean
theorem contract (c : Cells) (fuel : Nat) (value lower upper : Int) (tail rs : List Int)
    (f1 : c.Fits value) (f2 : c.Fits lower) (f3 : c.Fits upper) :
    ∃ out, callWord c program (fuel + 1) "lf-clamp"
      ⟨upper :: lower :: value :: tail, rs⟩ = .next ⟨out ++ tail, rs⟩ ∧
      post c value lower upper out
```

## Running it

```sh
python3 scripts/program_verify.py SOURCE.fs --contract CONTRACT [--out DIR]
    [--fuel N] [--jobs N] [--memory-per-check MB] [--checked]
    [--lean-time-limit SECONDS] [--keep-export] [--paths-limit N] [--search-limit N]
```

| Option | Meaning |
| --- | --- |
| `--contract FILE` | the contract (`lf-contract 0.1`); it names the word, which SOURCE.fs must define |
| `--out DIR` | where the files go; default `verify-out/WORD` in the current folder (ignored by git in the checkout) |
| `--fuel N`, `--jobs N`, `--memory-per-check MB`, `--checked` | passed to LeanForth's check as for `bin/leanforth check` (`--jobs` default 2, the owner's CPU rule) |
| `--lean-time-limit S` | Lean's time limit, for its compile and for its export, each (default 1800 s) |
| `--keep-export` | keep the export (about 23 MB) after the check; by default it is removed, by name, and the manifest kept |
| `--paths-limit N` | the generator stops when the word has more than N paths (default 256; paths double with each IF) |
| `--search-limit N` | the counterexample search may try at most N input combinations (default 250,000; it tries 12 values per input, 12³ = 1,728 for clamp) |

No option weakens what is checked: there is no way to skip a step, the
manifest check or the axiom comparison. Python 3 (standard library only),
Gforth, pinned Lean 4.35.0 (`scripts/install-lean.sh`; `LEAN` may name it
or the Makefile's cache) and LeanForth's checker are needed; the generator
stops before Lean for an unsupported word. SOURCE.fs, CONTRACT and `--out`
must lie inside the LeanForth checkout, since receipt 0.3 names files
relative to it (plan 8.4.1j makes receipts for other folders).

Run on 2026-11-13 (each run about 100 s on two workers, nearly all of it
LeanForth's check of the IR semantics' closure; standard input closed):

```text
$ python3 scripts/program_verify.py src/program/clamp.fs --contract tests/program/contracts/lf-clamp.contract --out build/ver1/lf-clamp; echo "exit status $?"
word: lf-clamp ( value lower upper -- result true | false ), src/program/clamp.fs:12, sha256 e4444161…
IR: 0.1, sha256 65187502…, equal to tests/program/ir/clamp.ir
contract: lf-clamp/0, tests/program/contracts/lf-clamp.contract, sha256 841a7163…
obligations: 2, from the untrusted generator program_vc.py 0.1
  O1: If lower > upper: the word leaves false (bottom first), and the postcondition holds.
  O2: If lower ≤ upper: the word leaves min(max(value, lower), upper), true (bottom first), and the postcondition holds.
proofs: written by Lean 4.35.0 from the generator's tactic scripts; Lean printed the program back equal to the IR
export: build/ver1/lf-clamp/lf-clamp.ndjson and its manifest (23,600,297 bytes)
ProgramVC.LfClamp0.contract: accepted; axioms: propext, Classical.choice, Quot.sound
ProgramVC.LfClamp0.O1: accepted; axioms: propext, Quot.sound
ProgramVC.LfClamp0.O2: accepted; axioms: propext, Classical.choice, Quot.sound
check: accepted-by-leanforth: LeanForth's checker re-checked the export and accepted all 4277 declarations; each theorem's axioms equal Lean's #print axioms
verify: discharged, settled by accepted-by-leanforth
run: not-run (plan 8.4.2)
lf-clamp: contract lf-clamp/0 discharged (2 of 2 obligations; Lean wrote the proofs, LeanForth's checker accepted them); about the IR, under the receipt's 8 assumptions; compiled code is not covered
receipt: build/ver1/lf-clamp/lf-clamp.receipt.json (schema 0.3)
exit status 0
```

A wrong contract (MAX and MIN exchanged), refuted: LeanForth's checker
accepted Lean's proof that the contract is false.

```text
$ python3 scripts/program_verify.py src/program/clamp.fs --contract tests/program/contracts/wrong-clamp-swapped.contract --out build/ver1/wrong-clamp-swapped; echo "exit status $?"
...
obligations: none: the untrusted generator program_vc.py 0.1 found inputs that break the contract
  refutation: on 64-bit cells with value = -3, lower = -3, upper = -2, the word leaves -3, -1 (true) (bottom first); the postcondition fails
proofs: written by Lean 4.35.0 from the generator's tactic scripts; Lean printed the program back equal to the IR
export: build/ver1/wrong-clamp-swapped/lf-clamp.ndjson and its manifest (23,388,200 bytes)
ProgramVC.LfClampWrongSwapped.refuted: accepted; axioms: propext, Classical.choice, Quot.sound
check: accepted-by-leanforth: LeanForth's checker re-checked the export and accepted all 4295 declarations; each theorem's axioms equal Lean's #print axioms
verify: refuted, settled by accepted-by-leanforth
run: not-run (plan 8.4.2)
lf-clamp: contract lf-clamp/wrong-swapped NOT VERIFIED: refuted: on 64-bit cells with value = -3, lower = -3, upper = -2, the word leaves -3, -1 (true) (bottom first); the postcondition fails
receipt: build/ver1/wrong-clamp-swapped/lf-clamp.receipt.json (schema 0.3)
exit status 1
```

The text is v0's: its exact form, `--json` and the report schema are plan
8.4.1c's [format] gate.

## The steps

| Step | What the driver does | Trusted? |
| --- | --- | --- |
| 0 | Reads the command line; the three paths must lie inside the checkout | untrusted driver |
| 1 | Runs the program words (`src/program/verify.fs`, ADR 0019) on the whole source file: they write its IR, or refuse a token with its diagnostic; the file is hashed before and after | `trusted-reader` (tested, not proved) |
| 2 | Reads the contract, finds its word in the IR, removes by name the files an earlier run wrote in `--out`, and requires the contract's `ir` file to be the IR just written, byte for byte | untrusted |
| 3 | Refuses an IR 0.2 word (receipt schema 0.4 awaits the owner); runs the generator for this contract alone, within the path and search limits: the obligations, the contract theorem and their tactic scripts, or the theorem `refuted` | `untrusted-generator` |
| 4 | Pinned Lean compiles the generated file (warnings are errors, so `sorry` fails): it writes the proofs, prints the program back, which must equal the IR, and reports `#print axioms`; `scripts/export.sh` writes the theorems with every declaration they use and the manifest | `trusted-lean` |
| 6 | `bin/leanforth check --json` checks the export, a final run (no snapshot); export and manifest hashed before and after | `trusted-leanforth`, the only judge |
| 7 | The check status from LeanForth's verdicts on every declaration; each accepted theorem's axioms must equal Lean's | untrusted, from the report |
| 8 | Builds the receipt, has the strict reader check it, and writes the evidence record and the receipt, each to a `.partial` file renamed when complete; removes the export unless `--keep-export` | untrusted; the reader checks it |

(Step 5, the statement fixed by LeanForth itself, is plan 8.4.1e–f.)

## The receipt

Schema 0.3 ([PROGRAM_RECEIPTS.md](PROGRAM_RECEIPTS.md)), statuses set only
from LeanForth's report and the generator's summary:

| Situation | check | verify | Exit status | Receipt |
| --- | --- | --- | --- | --- |
| LeanForth accepted every declaration of the export, the contract theorem and every obligation's theorem among them, each with allowlisted axioms equal to Lean's | `accepted-by-leanforth` | `discharged` | 0 | yes |
| A counterexample, and LeanForth accepted the theorem `refuted` | `accepted-by-leanforth` | `refuted` | 1 | yes |
| A declaration rejected | `rejected` | `open`, nothing settled | 1 | yes |
| A declaration unknown or unsupported | `unsupported` | `open` | 2 | yes |
| The check did not finish: out of fuel or room (3); invalid, not checked, a theorem missing from the report, a stopped run, no report (5) | `failed` | `open` | 3 or 5 | yes |
| Lean failed on the generated file, or ran out of time | `not-checked` | `open` | 2 or 3 | yes |
| The generator cannot make obligations (loops, recursion, literals outside −1…1) | `not-checked` | `unsupported` | 2 | yes |
| An IR 0.2 word (the SHA helper words) | — | — | 2 | no: needs receipt 0.4 |
| A theorem NOT PROVED (an axiom outside the allowlist) | — | — | 6 | no: 0.3 has no status for it |
| LeanForth's axioms not Lean's; Lean's printed program not the IR | — | — | 5 | no |
| The source, the contract, the IR file or a tool refused; a limit of the generator | — | — | 2, 3 or 4 | no |

RUN is always `not-run`, label *not run*, until plan 8.4.2. A receipt
lists every theorem with its own axioms, the assumptions that apply
(`trusted-lean` only when Lean elaborated the file, `trusted-leanforth`
only when LeanForth accepted), the tools, and the hashes of the source,
the IR, the contract, the generated Lean file, `scripts/program_vc.py`,
`scripts/export.sh` and the export's manifest. It never has a `verified`
field and never says LeanForth proved anything. Beside it,
`WORD.evidence.json` records what the run found (Lean's version and
axiom reports, the export's hash, LeanForth's version, counts and
verdicts, the generator's summary, the options that can change a result),
for the replay of plan 8.4.1d.

**Files in `--out`:** `obligations.lean`, `WORD.ndjson` (removed after the
check unless `--keep-export`), `WORD.ndjson.manifest.json`,
`WORD.evidence.json`, `WORD.receipt.json`, WORD with characters outside
letters, digits, `_ . -` written `_`. As soon as the contract names the
word, the driver removes these names (and their `.partial` files) left by
an earlier run, and nothing else, so no earlier result is ever read as
this run's; a run that stops leaves no receipt.

## Exit statuses and problem codes

The CLI's statuses, the most severe first when several apply: 5, 4, 1,
3, 2, 6, 0. Each problem prints one line `error: CODE: MESSAGE`; a run
that writes no receipt ends with `WORD: NOT VERIFIED: CODE; no receipt
written`. `tests/program/test_program_verify.py` reaches every code and
checks that each is listed here.

| Code | Status | Step | Meaning |
| --- | --- | --- | --- |
| `usage` | 4 | 0 | a command-line mistake |
| `outside-folder` | 4 | 0 | a path outside the checkout, or one receipt 0.3 cannot name (a segment starting with a dot) |
| `gforth-not-found` | 4 | 1 | Gforth (`GFORTH`, the checkout's, or on the PATH) cannot be started |
| `source-unreadable` | 4 | 1 | the source file cannot be read |
| `source-refused` | 2, 4 or 3 | 1 | the program words refused the source: unsupported (2), invalid (4), full, for example a path of about 90 characters or more (3) |
| `source-changed` | 4 | 1 | the source changed while the program words read it |
| `contract-unreadable` | 4 | 2 | the contract cannot be read, or is not UTF-8 |
| `contract-malformed` | 4 | 2 | a contract parse error, or an `ir` line naming no file inside the checkout |
| `word-not-found` | 4 | 2 | the source defines no word the contract names (a constant is not a word) |
| `contract-ir-differs` | 4 | 2 | the contract's `ir` file is missing or is not the IR the program words write |
| `ir-needs-receipt-0.4` | 2 | 3 | an IR 0.2 word: its receipt needs schema 0.4 (plan 8.4.1k) |
| `generator-unsupported` | 2 | 3 | the generator cannot make obligations (a receipt says `unsupported`) |
| `paths-limit` | 3 | 3 | more paths than `--paths-limit` |
| `search-limit` | 3 | 3 | more input combinations than `--search-limit` |
| `lean-not-found` | 4 | 4 | no Lean, or not Lean 4.35.0 |
| `lean-failed` | 2 | 4 | Lean failed on the generated file: nothing checked, every obligation open |
| `lean-time-limit` | 3 | 4 | Lean's compile or export ran over `--lean-time-limit` |
| `program-print-back-differs` | 5 | 4 | the program Lean printed back is not the IR |
| `export-failed` | 5 | 4 | `scripts/export.sh` failed or wrote no manifest |
| `file-changed` | 4 | 4, 6 | the generated file changed while Lean read it, or the export or manifest while LeanForth checked it |
| `export-invalid` | 4 | 6 | LeanForth refused to read the export (its manifest, its format) |
| `proof-rejected` | 1 | 6 | a declaration rejected |
| `proof-undecided` | 2 | 6 | a declaration unknown or unsupported |
| `proof-exhausted` | 3 | 6 | a declaration out of fuel or room |
| `not-proved` | 6 | 6 | a theorem accepted but resting on an axiom outside the allowlist |
| `axioms-differ` | 5 | 7 | LeanForth's axioms for a theorem are not Lean's `#print axioms` |
| `internal` | 5 | any | a fault: a tool ending unexpectedly, no check report, a stopped or unfinished check, a missing axiom report, the driver's own fault |
| `receipt-not-written` | 4 | 8 | the `--out` folder or a file in it cannot be written |

`search-limit` and `file-changed` are v0's additions to the design's
catalogue; the catalogue is fixed at 8.4.1c's [format] gate (plan 3.5.4).
`expect` in a contract is a test annotation: when the outcome differs
the driver prints `note: the contract expects X; verify found Y` and
changes nothing else.

## Limits and resources

- The generator: `--paths-limit` and `--search-limit` above; loops,
  recursion, literals outside −1…1 and stack effects deeper than the
  declared inputs are unsupported (PROGRAM_VC.md).
- Time on clamp (2026-11-13, two workers, other agents running): about
  100 s in all, Lean's compile and export about 10 s, LeanForth's check of
  the 4,277 declarations the rest; the wrong contract's 4,295 the same.
- Disk: the export is about 23.6 MB, removed after the check; the
  generated file is 27 KB, the receipt 8 KB.
- The program words: lines under 128 characters, source paths under about
  90 characters (else `source-refused`, full).
- A time limit or a signal stops the tool that runs and everything it
  started (each runs in a process group of its own).

## Results (the plan's acceptance, 2026-11-13)

`python3 tests/program/verify_lean_check.py --all` ran every committed
contract end to end with pinned Lean and LeanForth (`--jobs 2`):

| Contract | Word | Outcome | Exit status |
| --- | --- | --- | --- |
| `lf-clamp` | `lf-clamp` | `accepted-by-leanforth`, `discharged` | 0 |
| `lf-checked-add` | `lf-checked-add` | `accepted-by-leanforth`, `discharged` | 0 |
| `lf-checked-abs` | `lf-checked-abs` | `accepted-by-leanforth`, `discharged` | 0 |
| `lf-in-range` | `lf-in-range` | `accepted-by-leanforth`, `discharged` | 0 |
| `wrong-clamp-swapped` | `lf-clamp` | `accepted-by-leanforth`, `refuted` | 1 |
| `wrong-checked-add-total` | `lf-checked-add` | `accepted-by-leanforth`, `refuted` | 1 |
| `wrong-in-range-exclusive` | `lf-in-range` | `accepted-by-leanforth`, `refuted` | 1 |
| `lf-gcd` | `lf-gcd` | `not-checked`, `unsupported` (a loop) | 2 |
| `lf-factorial` | `lf-factorial` | `not-checked`, `unsupported` (a loop) | 2 |
| `sha-rotr`, `sha-ch`, `sha-maj`, `sha-big-sigma0` | the SHA helper words | refused: `ir-needs-receipt-0.4`, no receipt | 2 |

Every receipt written is read by `python3 scripts/program_receipt.py
validate` and equals its golden copy in
[`tests/program/verify/golden/`](../../tests/program/verify/golden/) but for
its date and `--out` folder.

## Tests

- `make test` (`test-program-verify-driver`):
  [`tests/program/test_program_verify.py`](../../tests/program/test_program_verify.py)
  runs the driver with the real program words and generator and with
  [`tests/program/verify/fake_lean.py`](../../tests/program/verify/fake_lean.py)
  standing in for Lean, its exporter and LeanForth's checker (the checker
  only inside the test's own process: the driver has no option or variable
  that changes its checker). Every outcome, exit status and code above;
  malformed command lines, sources, contracts and IR files; the limits;
  tools missing or of another version; files changed during the run; the
  default `--out`; an earlier run's files removed by name and nothing else;
  a failed write leaving no receipt and no partial file; two runs giving the
  same bytes; the golden receipts of gcd and factorial.
- `make check` (`reference-program-verify-clamp`, `reference-program-verify-refuted`):
  [`tests/program/verify_lean_check.py`](../../tests/program/verify_lean_check.py)
  runs `lf-clamp` and `wrong-clamp-swapped` end to end from the command
  line with pinned Lean (cached when the Makefile's Lean cache is on) and
  LeanForth, against their golden receipts.
- `make reference-program-verify-all`: all thirteen contracts (about 12
  minutes; not part of `make check`).
- Planted faults in `tests/mutants/faults.toml` (ids `verify-…`), each
  caught by a named test.

## What it does not do yet

`bin/leanforth verify`, `--json` and the report schema (8.4.1c);
`--replay` and the tampering suite (8.4.1d); the statement fixed by
LeanForth and supplied proofs (8.4.1e–f); contracts read in Forth (8.4.1g);
the receipt written in Forth (8.4.1h); `sorry` and NOT PROVED receipts
(8.4.1i, 0.5); files outside the checkout (8.4.1j); IR 0.2 words (8.4.1k);
proofs by LeanForth's tactics (8.4.1l–m); RUN (8.4.2). Loop words need
invariants (plan 4.4.1) or proofs supplied by hand (8.4.1f).

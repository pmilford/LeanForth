# Verification conditions and the clamp receipt

**Status: implemented, version 0 (2026-11-02, tasks 2.5.5 and 2.5.6 of
the [plan draft](../project/PLAN_DRAFT.md)); the clamp proofs re-checked by
LeanForth since 2026-11-12 (task 5.5.1).** The generator is untrusted
Python; Lean 4.35.0 proves everything it produces, from the tactic scripts
it writes. For the clamp contract, Lean's exporter then writes the
contract theorem and its two obligations with every declaration they use,
and LeanForth's checker (`bin/leanforth check`) checks that export again:
the clamp receipt ([schema 0.3](PROGRAM_RECEIPTS.md)) states LeanForth's
verdict. Lean wrote the proofs and LeanForth re-checked them; LeanForth
has no tactics yet. The other contracts below are checked by Lean only.

```text
Forth source ─reader─▶ IR ─┐
                           ├─ scripts/program_vc.py ─▶ obligations + contract theorem ─▶ Lean
contract (text) ───────────┘        (untrusted)              (Lean file)       (writes the proofs)
                                                                                         │
                                       export with the closure (scripts/export.sh) ◀─────┘
                                                                                         │
runtime comparison (PROGRAM_IR_RUN.md) ───────────┐       LeanForth's checker ◀──────────┘
                                                  │       (bin/leanforth check)
                     scripts/program_receipt.py ◀─┴──── evidence ◀─┘
                                  │
                                  ▼
             receipt (JSON, schema 0.3) and its printed form
```

## One example in three forms

**Mathematics.** For integers v, l, u in the cell range: if l > u,
`lf-clamp` returns *false*; if l ≤ u it returns r and *true* with
r = min(max(v, l), u), l ≤ r ≤ u, r = v when l ≤ v ≤ u, r = l when v < l,
r = u when v > u. Cells below its inputs are kept.

**Forth.** The word, and its contract as the generator reads it
([`tests/program/contracts/lf-clamp.contract`](../../tests/program/contracts/lf-clamp.contract)):

```forth
: lf-clamp ( value lower upper -- result true | false )
  2dup > if 2drop drop false exit then
  >r max r> min true ;
```

```text
lf-contract 0.1
id lf-clamp/0
word lf-clamp
ir tests/program/ir/clamp.ir
stack ( value lower upper -- result true | false )
inputs value lower upper
statement For integers v, l, u in the cell range: ...
case lower > upper
  out false
case lower <= upper
  out r true
  ensure r = min(max(value, lower), upper)
  ensure lower <= r && r <= upper
  ensure lower <= value && value <= upper -> r = value
  ensure value < lower -> r = lower
  ensure value > upper -> r = upper
expect discharged
```

**Lean** (generated, in
[`tests/program/vc/obligations.lean`](../../tests/program/vc/obligations.lean),
namespace `ProgramVC.LfClamp0`; stacks are top first):

```lean
def post (c : Cells) (value lower upper : Int) (out : List Int) : Prop :=
  (lower > upper → out = [0]) ∧
    (lower ≤ upper → ∃ r : Int, out = [(-1), r] ∧ (r = (min (max value lower) upper)) ∧ ...)

theorem O1 ... (p1 : lower > upper) : post c value lower upper [0]
theorem O2 ... (p1 : ¬(lower > upper)) : post c value lower upper [(-1), min (max value lower) upper]

theorem contract (c : Cells) (fuel : Nat) (value lower upper : Int) (tail rs : List Int)
    (f1 : c.Fits value) (f2 : c.Fits lower) (f3 : c.Fits upper) :
    ∃ out, callWord c program (fuel + 1) "lf-clamp"
      ⟨upper :: lower :: value :: tail, rs⟩ = .next ⟨out ++ tail, rs⟩ ∧
      post c value lower upper out
```

## The contract language, version 0.1

A contract names the word, its IR file, its inputs (bottom first) and its
stack effect, a plain-language statement, optional preconditions
(`pre`), and cases. Each case has a guard, the output it leaves above the
untouched cells (`out`, bottom first: `true`, `false`, numbers, inputs, or
new names for results) and conditions on those results (`ensure`). Every
input is assumed to fit in a cell. Expressions use `-> || && !`, `= <> <
<= > >=`, `+ - *` (mathematical integers), `min(a, b)`, `max(a, b)`,
`abs(a)`, `flag(condition)` (−1 or 0), `fits(a)` and `cell.max`,
`cell.min`. `expect` says what the test requires: `discharged`, `refuted`
or `unsupported`.

The contract theorem says: for every cell width, every fuel of at least
the word's call depth, all inputs that fit and satisfy `pre`, and every
stack below them, the word returns normally, keeps the cells below, and
leaves an output that satisfies every case whose guard holds.

## What the generator does

[`scripts/program_vc.py`](../../scripts/program_vc.py) executes the
word's IR symbolically: each IF on a condition splits the path (constant
conditions do not), calls are followed with the callee's own return stack,
constants are evaluated (`-1 1 RSHIFT` is the largest cell, its `INVERT`
the smallest), arithmetic is kept as the model's `c.wrap`, and a division
or shift outside the model becomes a failing path. For each path it writes
an obligation: under the path's conditions the output satisfies `post`, or
for a failing path, the path cannot be taken. Each comes with a proof
script (unfold, rewrite each `c.wrap` that provably fits, give the
witnesses, `omega`). It then states `contract` against the IR semantics
and proves it by splitting on the same conditions, running the IR in Lean
on each path (`vc_run`) and using the obligations.

Before writing proofs it searches for a counterexample (each input from
−3…3, 10 and the cell edges, on 64-bit cells). If it finds one, it writes
instead a theorem `refuted`: the negation of the contract statement,
proved by running the IR in Lean on those inputs.

**Why this is safe though the generator is untrusted.** `contract` and
`refuted` are statements about `ProgramIR.callWord` itself (copied
verbatim from [`tests/reference/program-ir.lean`](../../tests/reference/program-ir.lean)),
not about the generator's symbolic results. A wrong symbolic step makes a
proof fail, never a false theorem. The generator's translation of the IR
text into Lean terms is checked too: Lean prints each generated program
back in the text form and `make check` compares it with the IR file.
`make check` also plants two faults that Lean must reject: a postcondition
changed without its proofs, and the program's MAX and MIN exchanged.

## Results (2026-11-02)

| Word | Contract | Paths (obligations) | Status |
| --- | --- | --- | --- |
| `lf-clamp` | `lf-clamp/0` (above) | 2: l > u; l ≤ u | discharged |
| `lf-checked-add` | returns a + b and true when a + b fits, else false | 5: b > 0 with or without overflow; b < 0 with or without; b = 0 | discharged |
| `lf-checked-abs` | false for the smallest cell, else \|n\| and true, \|n\| ≤ max | 2 | discharged |
| `lf-in-range` | false for l > u, else flag(l ≤ v ≤ u) and true | 2 | discharged |
| `lf-gcd` | false for a negative input, else g ≥ 0 and true | — | unsupported: its loop (in `lf-euclid`) needs an invariant (stated and proved by hand in Lean, below) |
| `lf-factorial` | false for n < 0, else f ≥ 1 and true | — | unsupported: its loop (in `lf-factorial-from`) needs an invariant (stated and proved by hand in Lean, below) |

Version 0 also accepts only the literals −1, 0 and 1, which fit every cell
width (`Cells.fits_*` in the model); a larger literal may not fit a small
cell, where the model makes it *unmodeled*, so such a word is reported
unsupported rather than given a cell-width precondition.

Loops are executed by IR 0.1 but reasoning about them needs invariants,
which the plan puts in IR and VC version 1 (tasks 4.4.1 and 4.4.2). The two
loop words are already proved correct by induction directly on the
semantics (`gcd_correct`, `factorial_correct` in
[program IR](PROGRAM_IR.md)); the generator does not claim them.

Since 2026-11-03 (plan task 1.5.3) the Lean side of loop obligations
exists: Part 5 of `program-ir.lean` defines `LoopInvariant`, the three
obligations of a `BEGIN test WHILE body REPEAT rest` loop (the test leaves
a flag; on zero, `rest` reaches the goal; otherwise the body restores the
invariant with a smaller measure, or stops with a result that meets the
goal), proves the loop rule that combines them, states the invariants of
`lf-euclid` and `lf-factorial-from`, and proves the formal contracts of
`lf-gcd` and `lf-factorial` through them
([contracts of the five other words](PROGRAM_IR.md#contracts-of-the-five-other-words)).
Those proofs are written by hand. What the generator still lacks, so that
it could produce them:

- contract syntax for a loop's invariant and measure (one pair per
  `BEGIN`), since an invariant cannot be guessed;
- symbolic execution that stops at a loop: assume the invariant for an
  arbitrary state, check the test and body once, and continue after the
  loop from the invariant and a zero flag;
- writing the three obligations of `LoopInvariant` for each loop, with
  proof scripts, and a contract theorem that applies `loop_rule`;
- calls into a word with a loop, as `lf-gcd` calls `lf-euclid`: the
  loop's obligations generated inside the callee, or the callee's own
  contract used at the call.

The `ensure` lines of `lf-gcd.contract` and `lf-factorial.contract` are
also weaker than the formal contracts: the contract language has no
divisibility and no factorial.

Three deliberately wrong contracts are refuted by Lean:

| Contract | Claim | Counterexample (64-bit cells) |
| --- | --- | --- |
| `lf-clamp/wrong-swapped` | r = max(min(v, l), u) | v = −3, l = −3, u = −2: the word gives −3, the claim −2 |
| `lf-checked-add/wrong-total` | every sum returns with true | a = −3, b = smallest cell: the word returns false |
| `lf-in-range/wrong-exclusive` | flag is l < v < u | v = l = u = −3: the word says inside |

All 18 theorems use only `propext`, `Classical.choice` and `Quot.sound`.
`make test` checks, without Lean, that the generator writes exactly the
committed Lean file and summary, that each contract comes out as it
expects, and that mutating the clamp contract (MIN and MAX exchanged, or
an off-by-one bound) makes it refuted, a loop word unsupported, and an
input named `c` malformed.

## The clamp receipt

[`scripts/program_receipt.py`](../../scripts/program_receipt.py) writes
the receipt ([JSON](../../tests/program/receipts/generated/lf-clamp.json),
[printed form](../../tests/program/receipts/generated/lf-clamp.md)) from
the repository files at their current hashes — the source and the line of
its colon, the IR, the contract, the generated obligations and their
summary, the export step and the pinned export's manifest, the runtime
comparison's files — and from an evidence record
([`lf-clamp-evidence.json`](../../tests/program/receipts/generated/lf-clamp-evidence.json))
that `record` makes by running Lean (version, commit, its own axiom report
for each theorem), Lean's exporter (the export's hash and size, which must
be the ones [`lf-clamp.ndjson.manifest.json`](../../tests/program/vc/lf-clamp.ndjson.manifest.json)
pins), LeanForth (`bin/leanforth check --json --jobs 2`: its version and
verdict version, the declarations it accepted, and each theorem's verdict
and axioms) and Gforth (the clamp cases of the three-way comparison, and
Lean's agreement on them).

It keeps the three answers apart:

| Part | Clamp receipt says |
| --- | --- |
| CHECK | `accepted-by-leanforth`: Lean 4.35.0 wrote the proofs of `ProgramVC.LfClamp0.contract`, `O1` and `O2`; its exporter wrote them with every declaration they use, 4,277, to the pinned export; LeanForth's checker re-checked the export and accepted all 4,277. Each theorem with its axioms as LeanForth reports them (`O1` propext and Quot.sound, the others also Classical.choice), equal to Lean's `#print axioms` |
| VERIFY | `discharged`, `settledBy` `accepted-by-leanforth`: two obligations from the untrusted generator, each discharged by its theorem, which Lean proved and LeanForth's checker accepted |
| RUN | `passed`, label *runtime-tested; testing is not proof*: Gforth 1.0.0, Linux x86-64, 64-bit cells, 986 cases, 0 failures; Lean's model agreed on all 991 clamp cases |

and lists eight assumptions: host cells, two's complement, the trusted
reader (which finds names ignoring letter case, as Gforth does), the trusted runtime
(Gforth executes 2DUP, >, … as the IR semantics says), stack capacity,
the trusted Lean (it elaborated the obligations file and its exporter
wrote the export faithfully; its own check of the proofs is not relied
on), the untrusted generator made safe by stating the contract against
the IR semantics (kind `untrusted-generator`), and LeanForth's checker
(kind `trusted-leanforth`).

`scripts/program_receipt.py verify RECEIPT.json` reads the receipt
strictly, checks its schema and the rules beyond JSON Schema, then
rebuilds it and reports every field that differs, so a hand-edited
receipt, or one whose files changed since, is rejected
([reading a receipt](PROGRAM_RECEIPTS.md#reading-a-receipt)). `make test`
([`tests/program/receipt_check.py`](../../tests/program/receipt_check.py))
checks the golden output, strict reading, schema 0.3 and its rules
([`tests/support/schema_subset.py`](../../tests/support/schema_subset.py)),
that the receipt is accepted by LeanForth with every obligation
discharged by a named theorem and every path inside the repository,
verification, that tampered receipts (changed hashes, statuses, a label
put back, counts, theorems, axioms, assumptions, an added `verified`
field, a path outside the repository) are refused by the layer named with
each, and tampered texts (duplicate keys, fractions, a lone surrogate,
deep nesting) by the strict reader; and that evidence in which LeanForth
rejected a theorem, did not decide it or did not finish gives a receipt
that says so and discharges nothing, while evidence with a NOT PROVED
theorem, LeanForth's axioms other than Lean's or another export gives
none. `make check` records the evidence again (Lean, the export, LeanForth,
Gforth) and requires it to equal the committed record, and the fresh
export's manifest to equal the pinned one byte for byte.

A receipt that verifies is consistent with the repository and the
evidence. It is not an approval: the receipt format, the reader and the
generator are all under the review gates of `AGENTS.md`.

### LeanForth re-checks the clamp proofs (plan 5.5.1)

What LeanForth checks is Lean's export, not LeanForth text: Lean wrote the
proofs (from the generator's tactic scripts) and LeanForth's checker
checked them again, with every definition, inductive type and lemma they
use, from the pinned Lean's own `Init` up. LeanForth has no tactics yet.
The IR's Lean model uses a nested inductive type (`Instr`, whose `ifElse`
and `loop` hold lists of instructions) and well-founded recursion (`run`),
which LeanForth checks since plan task 5.2.5.

Run on 2026-11-12 (the export takes about 10 s, each check about 45 s on
two workers; the folder is any scratch folder):

```text
$ python3 scripts/program_receipt.py export /tmp/clamp/lf-clamp.ndjson
wrote /tmp/clamp/lf-clamp.ndjson and its manifest: ProgramVC.LfClamp0.O1, ProgramVC.LfClamp0.O2, ProgramVC.LfClamp0.contract with every declaration they use; check it with bin/leanforth check
$ bin/leanforth check --jobs 2 /tmp/clamp/lf-clamp.ndjson | tail -3      # exit status 0
ProgramVC.LfClamp0.contract: accepted; axioms: propext, Classical.choice, Quot.sound
4277 declarations: 4277 accepted
accepted: 4277; axioms: propext, Classical.choice, Quot.sound (allowlisted); none NOT PROVED
$ python3 tests/program/clamp_mutants.py program /tmp/clamp/lf-clamp.ndjson /tmp/clamp/program-mutant.ndjson
/tmp/clamp/program-mutant.ndjson: program, 11 new expressions
$ bin/leanforth check --jobs 2 /tmp/clamp/program-mutant.ndjson | grep -v ': accepted'   # exit status 1
ProgramVC.LfClamp0.contract: rejected
  rejected: argument type mismatch (D1-D5); diagnostic 59 at mixed-infer lf-mixed-infer: 0 0
4277 declarations: 4276 accepted, 1 rejected
accepted: 4276; axioms: propext, Classical.choice, Quot.sound (allowlisted); none NOT PROVED
```

`python3 scripts/program_receipt.py record` runs the same export and check
(with `--json`) for the receipt's evidence, and `write` then writes the
receipt; `make check` does both and compares them with the committed ones.

An export whose program IR term, postcondition or proof term was changed after Lean proved it is rejected by LeanForth's checker.
[`tests/program/clamp_mutants.py`](../../tests/program/clamp_mutants.py)
(untrusted test tool) changes one declaration of the export and leaves
everything else as it was, writing a fresh manifest so that the rejection
is the kernel's and not the manifest check's:

| Mutant | Change | LeanForth | Lean's official checker |
| --- | --- | --- | --- |
| `program` | MAX and MIN exchanged in `ProgramVC.LfClamp0.program` | `contract` rejected, exit 1 | rejected, exit 1 |
| `contract` | min and max exchanged in the postcondition `post` (the refuted contract `wrong-clamp-swapped`) | `O1` and `O2` rejected, so `contract` (it uses them), exit 1 | rejected, exit 1 |
| `proof` | the lemma `ir_max` replaced by `ir_min` in `contract`'s proof term | `contract` rejected, exit 1 | rejected, exit 1 |

The official checker's column cannot be reproduced from the repository: it is
one manual run on 2026-11-12 of Lean's kernel on the same files (the arena
build of lean4export v4.35.0's checker, kept outside the repository), not
repeated by the done check; it also accepted the unchanged export. `make
check` (`reference-program-mutants`) puts all three changes into one
export, each changed declaration added under its own name next to the
originals, and requires LeanForth to accept the originals and reject the
five changed theorems, in one run instead of three; `make test` checks the
tool itself on a small fixture (its changes are well formed and accepted
where they keep the proof). `make check` also has pinned Lean reject the
same program and postcondition changes in the Lean source
(`vc_check.py --lean`).

**The SHA-256 helper words** (stage SHA-2 of the flagship target) go
through the same pipeline: pinned Lean compiles
`tests/reference/program-ir.lean`, its exporter writes `shaRotr_correct`,
`shaCh_correct`, `shaMaj_correct` and `shaBigSigma0_correct` (each word of
`src/program/sha-words.fs` computes FIPS 180-4's function for every 32-bit
input) with every declaration they use, 2,890 in all, and LeanForth's
checker accepts every one, each theorem with the axioms Lean's
`#print axioms` reports. `sha-ch`'s body with AND and XOR exchanged, under
its old proof, and `shaCh_correct`'s proof with the lemmas of `sha-ch` and
`sha-maj` exchanged are rejected
([`tests/program/sha_export_check.py`](../../tests/program/sha_export_check.py),
`make check` target `reference-program-sha-export`, 2026-11-12). There is
no receipt for them yet: they are IR 0.2 programs, and their receipts need
schema 0.4, at the owner's [format] gate
([receipts](PROGRAM_RECEIPTS.md#schema-04-what-ir-02-receipts-need)).

## Running

```sh
python3 scripts/program_vc.py --out FILE.lean --summary FILE.json CONTRACT...
python3 tests/program/vc_check.py --write          # regenerate the committed obligations
python3 scripts/program_receipt.py write           # regenerate the receipt from the evidence
python3 scripts/program_receipt.py verify tests/program/receipts/generated/lf-clamp.json
GFORTH=... LEAN=... python3 scripts/program_receipt.py record --out EVIDENCE.json \
    [--manifest-out tests/program/vc/lf-clamp.ndjson.manifest.json]   # to pin a new export
python3 scripts/program_receipt.py export OUT.ndjson   # pinned Lean: the clamp proofs' export
bin/leanforth check --jobs 2 OUT.ndjson                # LeanForth's verdict on it
python3 tests/program/clamp_mutants.py program|contract|proof OUT.ndjson MUTANT.ndjson
make test-program-ir-run reference-program-ir-run reference-program-mutants
```

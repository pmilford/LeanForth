# Verification conditions and the clamp receipt

**Status: implemented, version 0 (2026-11-02, tasks 2.5.5 and 2.5.6 of
the [plan draft](../project/PLAN_DRAFT.md)).** The generator is untrusted
Python; everything it produces is checked by Lean 4.35.0 — *checked by the
Lean reference, not by LeanForth*, whose checker cannot check programs
before data types arrive (phase 5). The receipt format is schema 0.1,
which is under review; nothing here has passed a review gate.

```text
Forth source ─reader─▶ IR ─┐
                           ├─ scripts/program_vc.py ─▶ obligations + contract theorem ─▶ Lean
contract (text) ───────────┘        (untrusted)              (Lean file)                 │
runtime comparison (PROGRAM_IR_RUN.md) ─────────────────────────────────┐               │
                                     scripts/program_receipt.py ◀───────┴── evidence ◀──┘
                                                  │
                                                  ▼
                          receipt (JSON, schema 0.1) and its printed form
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
| `lf-gcd` | false for a negative input, else g ≥ 0 and true | — | unsupported: its loop (in `lf-euclid`) needs an invariant |
| `lf-factorial` | false for n < 0, else f ≥ 1 and true | — | unsupported: its loop (in `lf-factorial-from`) needs an invariant |

Loops are executed by IR 0.1 but reasoning about them needs invariants,
which the plan puts in IR and VC version 1 (tasks 4.4.1 and 4.4.2). The two
loop words are already proved correct by induction directly on the
semantics (`gcd_correct`, `factorial_correct` in
[program IR](PROGRAM_IR.md)); the generator does not claim them.

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
summary, the runtime comparison's files — and from an evidence record
([`lf-clamp-evidence.json`](../../tests/program/receipts/generated/lf-clamp-evidence.json))
that `record` makes by running Lean (version, commit, each theorem's
axioms) and Gforth (the clamp cases of the three-way comparison, and
Lean's agreement on them).

It keeps the three answers apart:

| Part | Clamp receipt says |
| --- | --- |
| CHECK | `checked-by-lean-reference`, label *checked by the Lean reference, not by LeanForth*: Lean 4.35.0 proved `ProgramVC.LfClamp0.contract`, `O1` and `O2`; axioms propext, Classical.choice, Quot.sound |
| VERIFY | `discharged`: two obligations from the untrusted generator, each with its theorem |
| RUN | `passed`, label *runtime-tested; testing is not proof*: Gforth 1.0.0, Linux x86-64, 64-bit cells, 986 cases, 0 failures; Lean's model agreed on all 991 clamp cases |

and lists seven assumptions: host cells, two's complement, the trusted
reader (including the known case-sensitivity gap), the trusted runtime
(Gforth executes 2DUP, >, … as the IR semantics says), stack capacity, the
trusted Lean, and the untrusted generator made safe by stating the
contract against the IR semantics.

`scripts/program_receipt.py verify RECEIPT.json` rebuilds the receipt and
reports every field that differs, so a hand-edited receipt, or one whose
files changed since, is rejected. `make test`
([`tests/program/receipt_check.py`](../../tests/program/receipt_check.py))
checks the golden output, schema 0.1
([`tests/support/schema_subset.py`](../../tests/support/schema_subset.py)),
the stricter rules the schema review asks for (every discharged
obligation names its theorem, `program.ir` is an object with a
*trusted-reader* assumption, only allowlisted axioms, every path inside
the repository), verification, and that 17 tampered receipts are rejected
(changed hashes, statuses, labels, counts, theorems, axioms, assumptions,
an added `verified` field, a path outside the repository). `make check`
records the evidence again and requires it to equal the committed record.

A receipt that verifies is consistent with the repository and the
evidence. It is not an approval: the receipt format, the reader and the
generator are all under the review gates of `AGENTS.md`, and the receipt
must be validated again against the schema version the review settles on.

## Running

```sh
python3 scripts/program_vc.py --out FILE.lean --summary FILE.json CONTRACT...
python3 tests/program/vc_check.py --write          # regenerate the committed obligations
python3 scripts/program_receipt.py write           # regenerate the receipt from the evidence
python3 scripts/program_receipt.py verify tests/program/receipts/generated/lf-clamp.json
GFORTH=... LEAN=... python3 scripts/program_receipt.py record --out EVIDENCE.json
make test-program-ir-run reference-program-ir-run
```

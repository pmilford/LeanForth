# The program IR interpreter and the three-way comparison

**Status: implemented and untrusted (2026-11-02, task 2.5.4 of the
[plan draft](../project/PLAN_DRAFT.md)); IR 0.2 added 2026-11-04.** The interpreter is ordinary
Forth; it proves nothing. What it adds is evidence that three independent
executions of the same word agree: the host running the Forth source, the
Forth interpreter running the reader's IR, and Lean running the IR model.

**IR 0.2** ([program IR](PROGRAM_IR.md#ir-02)): the interpreter reads
`lf-ir 0.2` as well, with `prim lshift` (unmodeled for a count outside the
cell, as `rshift`), `prim -rot` and `out` lines, and refuses those under
an `lf-ir 0.1` version line; names may be 36 characters long (a version
name, `x'31`). An out line takes its cells and sends what it prints to the
context's output sink (`irx-output-to ( xt -- )`, xt `( c-addr u -- )`;
a new context discards it): the bytes of Lean's `Event.render`, and `.S`
as both Gforths print it. The random comparison with Lean
(`ir_run_differential.py --lean`) adds 150 IR 0.2 programs (seed + 1) and
two planted faults (`-rot` as `rot`, `lshift` as `rshift`);
`tests/program/verify_ir02.py` compares the interpreter's stacks and
printed bytes with plain Gforth running the source.

Until now nothing tied `lf-clamp` as Gforth runs it to the IR terms the
Lean theorems are about ([program IR](PROGRAM_IR.md), "What is proved").
The comparison closes that gap for the IR route as far as testing can:

```text
                       ┌──▶ Gforth runs the word itself ─────────────┐
src/program/clamp.fs ──┤                                             ├─ same stack, or fail
  (reader)             └──▶ IR text ──▶ src/program/ir-run.fs runs it ┤
                                  └──▶ Lean runs ProgramIR.callWord ──┘   (make check)
```

## One example in three forms

**Mathematics.** For v = 5, l = 0 and u = 3, clamp gives min(max(5, 0), 3)
= 3 and *true*; a sentinel cell 12345 below the inputs is kept. With one
unit of fuel the call succeeds; with none it fails *out of fuel*.

**Forth** (the interpreter on the reader's live output, then the host):

```forth
irx-load-start ' irx-load-line s" src/program/clamp.fs" lf-ir-read-file drop
irx-load-finish drop                                      \ outcome-ok
irx-clear 12345 irx-push drop 5 irx-push drop 0 irx-push drop 3 irx-push drop
1 s" lf-clamp" irx-run                                    \ outcome-ok
\ irx-depth is 3 and items 0..2 are 12345 3 -1, as on the host:
12345 5 0 3 lf-clamp                                      \ 12345 3 -1
```

**Lean** (`tests/reference/program-ir-run.lean`, which copies the model
verbatim; stacks are top first):

```lean
callWord cells64 clampProgram 1 "lf-clamp" ⟨[3, 0, 5, 12345], []⟩
  = .next ⟨[-1, 3, 12345], []⟩
```

All three print the line `clamp lf-clamp 1 12345 5 0 3 -> ok 12345 3 -1`.

## The interpreter

[`src/program/ir-run.fs`](../../src/program/ir-run.fs), words prefixed
`irx-` (the reader's are `ir-`). It loads the IR text form and runs a word
exactly as `ProgramIR.run` does:

| Rule | As in the model |
| --- | --- |
| Cells | host cells; `+ - negate 1+ 1-` wrap (two's complement), `*` keeps the low cell (`UM* DROP`), `abs` of the smallest cell is itself |
| Partial words | `/` and `MOD` only for dividend ≥ 0 and divisor > 0, `RSHIFT` only for a count below the cell width; anything else is *unmodeled*, never a host result |
| Literals | read as the model's parser reads them (`String.toInt?`): an optional `-` and decimal digits, where leading zeros change nothing (`-0007` is −7); a literal outside the cell is *unmodeled* when it runs; it still loads (the reader writes only literals of at most 10 digits, which fit 64-bit cells). Whether it fits is decided from its digits without the leading zeros, compared with the digits of `max-n 1+`, so the rule is exact for every cell width of 16 bits or more |
| Calls | a word runs on its caller's data stack with a return stack of its own and must leave it empty (*unbalanced*); a constant runs on empty stacks and must leave one value and not EXIT (*bad constant*); an undefined name fails only when called (*unknown word*), after the fuel check |
| Fuel | a call gives its callee one unit less; each loop iteration costs one unit of the block's fuel, and what the body spent is gone for the rest of the block; an IF part's own spending is not |
| Failures | *underflow*, *unmodeled*, *unbalanced*, *unknownWord*, *badConstant*, *outOfFuel*, each an explicit result |

Public words:

| Word | Effect |
| --- | --- |
| `irx-load-start` `irx-load-line ( c-addr u -- )` `irx-load-finish ( -- outcome )` | load IR text a line at a time; `irx-load-line` suits the reader's output word, so `' irx-load-line` can be given to `lf-ir-read-file`. `irx-load-finish` closes the load: a program runs only after a finish that gave *ok*, and a line or a second finish after it is *invalid* and leaves no program to run, so a word left half-loaded never runs |
| `irx-load-file ( c-addr u -- outcome )` | load an IR text file |
| `irx-clear` `irx-push ( x -- outcome )` `irx-depth ( -- n )` `irx-item ( i -- x true \| false )` | the data stack, bottom first; `irx-item` gives *false* outside `0 ≤ i < irx-depth` |
| `irx-run ( fuel c-addr u -- outcome )` | the model's `callWord`: run a word |
| `irx-result ( -- result )` `irx-result-text ( result -- c-addr u )` `irx-last ( -- line column )` | which model result ended the run, its Lean name, and where |

Outcomes ([`src/lib/outcome.fs`](../../src/lib/outcome.fs)):

| Outcome | Loading | Running |
| --- | --- | --- |
| ok | well-formed IR 0.1 text | the word returned normally |
| invalid | anything else, including a name defined twice, a line of 128 characters or more (fed by `irx-load-line` or read from a file, as the reader refuses it), and any line or second `irx-load-finish` after a finished load | underflow, unbalanced, unknown word, bad constant; no program; negative fuel |
| unsupported | — | the model's *unmodeled*, including a literal outside the cell |
| exhausted | — | out of fuel |
| full | more than 512 instructions, 64 names, 16 open IF/BEGIN, a name over 31 characters | the data stack (128 cells), return stack (32) or frames (64) are full — the model has no limits, so this is never a model result |

Every run starts from an empty return stack, as `callWord` does, even
when a failed run left items on it. A failed load reports through
`irx-load-lines` the line that stopped it.

Its state is one context record (`context-record:`,
[ADR 0009](../adr/0009-reentrant-state-and-parallel-checking.md)), so a
program loaded in one context is invisible in another; a test checks it.
It reads text without byte access: tokens are split with `SEARCH` and
`COMPARE`, and lines fed by the reader are never `EVALUATE`d again.

## The comparison

[`tests/program/ir-run-table.fs`](../../tests/program/ir-run-table.fs)
loads `clamp.fs` and `examples.fs` through the reader into the
interpreter, runs every case on the interpreter and, where the host can
run it, on the host word, requiring the same data stack item for item. It
prints each case for Lean.
[`tests/program/ir_run_differential.py`](../../tests/program/ir_run_differential.py)
checks the result and, under `make check`, gives the lines to
[`tests/reference/program-ir-run.lean`](../../tests/reference/program-ir-run.lean),
which must print exactly the same lines.

| Cases | Number (seed 20261102) |
| --- | --- |
| The input sets of the existing tables, below a sentinel: clamp 686, in-range 686 + 343, checked add 410, checked abs 263, factorial 152, gcd 150 | 2,690 |
| Seeded random inputs (xorshift64): the six words and their helpers (`lf-within-closed?`, `lf-add-overflow?`, `lf-add-above?`, `lf-add-below?`, `lf-euclid`, `lf-factorial-from`, `lf-product-over?`) and the two constants | 2,402 |
| Model only: too few inputs, fuel sweeps (0 up to enough), division outside the model, an unknown word | 60 |
| **Total** (5,092 also run on the host) | **5,152** |

Measured 2026-11-02 on Gforth 1.0.0 and 0.7.3: 0 mismatches between the
interpreter and the host; Lean printed all 5,152 lines identically (5,112
*ok*, 27 *outOfFuel*, 7 *underflow*, 4 *unmodeled*, 2 *unknownWord*).

The six words use only some primitives, so `make check` also generates 300
random IR programs (every primitive, IF, loops, also inside loops, calls
forward and back, EXIT, constants, unknown names, literals at and beyond
the cell edges, some written with leading zeros) with 4 runs
each at fuel 0 to 6, runs them on the interpreter
([`tests/program/ir-run-cases.fs`](../../tests/program/ir-run-cases.fs))
and in Lean, which reads the same IR text back, and requires identical
results: 1,200 cases, every failure kind reached (444 *ok*, 319
*underflow*, 258 *outOfFuel*, 71 *unmodeled*, 52 *badConstant*, 43
*unknownWord*, 13 *unbalanced*); the programs hold 77 literals with
leading zeros and 20 loops inside loops. Other seeds with 1,500 programs
each also agreed: seeds 1 to 4 before the model's literal rule, 1 and 2
after it, and seeds 1 to 3 with loops inside loops and leading zeros
(54,000 cases in all). Lean's parser of the text is more lenient than the
interpreter's loader (it ignores indentation and blank lines, and reads
`1_000` as 1000); text only Lean accepts stops the Forth run, so it can
never count as agreement, and the generator writes none.

### Planted faults

| Fault | Caught by |
| --- | --- |
| `MAX` and `MIN` exchanged; `*` computed as `+` | the host comparison (281 and 239 differing cases), in `make test` |
| `XOR` as `OR`, `0>` as `0<`, `NIP` as `DROP` | the random programs against Lean (4, 11 and 11 cases with the default seed), in `make check` |
| loops spend no fuel; a callee keeps its caller's fuel; a constant may EXIT; `/` defined for negative operands; a word sees its caller's return stack | the unit tests (`tests/program/ir-run.fs`, `make test`); the first four also by the Lean comparison (`make check`). The host comparison alone misses all five: the host has no fuel, and the tables never divide negative numbers or misuse the return stack |
| leading zeros counted as digits, so `lit 0…05` is *unmodeled* | the unit tests, and the random programs against Lean (11 cases with the default seed) |
| lines still loaded after `irx-load-finish`, so a half-loaded word runs; a run that does not start from an empty return stack | the unit tests |

## What this does and does not establish

It shows, on 5,092 host cases, that Gforth 1.0.0 and 0.7.3 on x86-64 run
the six words as the reader's IR says, and on 6,352 cases that the
interpreter computes what the Lean model computes. It does not prove
either: the host is trusted (*trusted-runtime* in receipts), the reader is
trusted (*trusted-reader*), and other hosts, cell sizes and inputs are
untested. The reader finds names ignoring the case of A–Z, as Gforth does,
and refuses a redefinition under any spelling, so a source file cannot
make `true` mean one thing on the host and another in the IR
([program IR](PROGRAM_IR.md), "Names").

## Running

```sh
make test-program-ir-run        # unit tests, interpreter against host, VC and receipt goldens
make reference-program-ir-run   # the same against pinned Lean (about 154 s with `JOBS=2 LEAN_CACHE=0`, 2026-11-12, since it also records the clamp receipt's evidence)
gforth -e '7 constant ir-run-seed' tests/program/ir-run-table.fs      # another seed
GFORTH=gforth LEAN=... python3 tests/program/ir_run_differential.py --lean --seed 3 --programs 1500
```

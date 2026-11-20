# Forth review: nat-ops refuses a non-literal Nat operand, plan 9.4.8l AW, the owner's gate of 2026-11-20 (2026-11-20)

Branch `nat-ops-fail-closed`, range **8b6272c1..fbe5de3e** (2 commits: c98d91d2, fbe5de3e). Reviewed: `git diff
8b6272c1...fbe5de3e -- src tests` and the documentation diff. Source change: src/core/nat-ops.fs, src/kernel/reduce-nat.fs,
src/front/reduce-nat.fs. Work was done on `git archive fbe5de3e` and `git archive 8b6272c1`, extracted into a scratch
folder. No worktree was edited. This is a kernel-gate change. The owner approved it in principle on 2026-11-20
(OWNER_DECISIONS.md, "Two answers of 2026-11-20, morning"). This report is the independent review the gate requires.

Inputs:
- pinned Lean's kernel source, `type_checker.cpp` 300-313 (`get_count_arg`) and 604-703 (`is_nat_lit_ext`,
  `get_nat_val`, `reduce_bin_nat_op`, `reduce_pow`, `reduce_shiftLeft`, `reduce_bin_nat_pred`, `reduce_nat`), read
  from the saved copy in `.claude/work/lean-src/`, since the toolchain ships only the Lean sources;
- Meta/WHNF.lean 976-1035 (`withNatValue`, `reducePow`, `reduceNat?`) from the toolchain;
- kernel/whnf.fs 555-615, kernel/defeq.fs 480-495 and 960-1001, kernel/iota.fs 280-284 and front/whnf.fs 764-799.

**Findings: 0 high, 2 medium, 2 low. Two are blocking: B1 (tests) and B2 (reuse).** No input the checker can reach gets a
different answer. Every literal case is byte-identical between the old and new trees. The non-literal path is
unreachable: a tripwire never fired on real inputs. The new order (literal test, then count) matches Lean's.

**Verdict: merge after fixes (B1, B2). L1 and L2 should be fixed or given a plan row.**

For the owner: no input the checker can reach gets a different verdict (yes). Every caller already checks that both
numbers are literals before it calls these words, and Lean's own kernel does the same. On 10,000 literal cases the
old and new code gave identical answers. On four Lean export slices and four `decide` files the verdicts were
identical, and a tripwire showed the new refusal never fired.

## Findings

**B1 (medium, blocking: tests). The new order is pinned only for a non-literal *second* operand.**
- The branch claims that an operand that is no literal is invalid before the count or threshold is read
  (kernel/reduce-nat.fs:58-63, front/reduce-nat.fs:26-28). The tests check only the case where the count or
  threshold is read on the second operand: pow and shl by an application, tests/core/reduce-nat.fs:172-173 and
  tests/front/reduce-nat.fs:110-111.
- A non-literal *first* operand with a count Lean refuses, or with an exponent above 256, is never tested. The
  first-operand cases use exponent 3, which passes the policy, so the inner test refuses them whatever the order.
- Two faults of mine survive all four test files (nat-ops, kernel reduce-nat, front reduce-nat, defeq). Both test
  only the second operand before the policy:
  - R5, in kernel/reduce-nat.fs:63: `over lf-lit-leaf? if lf-rn-binary exit then ['] lf-rn-binary lf-nat-lits-by`.
    With it, `pow (Nat) 2^32` and `shiftLeft (Nat.succ 4) 2^32` answer rejected 92. They must answer invalid.
  - R6, in front/reduce-nat.fs:84: `over lf-lit-leaf? if rn-fold-op exit then ['] rn-fold-op lf-nat-lits-by`.
    With it, `Nat.pow Nat 257` and `Nat.pow (Nat.succ fk) 257` answer unsupported. They must answer invalid.
  - A probe (`probe/first.fs`) confirmed both answers.
- Fix (checked: passes on fbe5de3e, catches R5 and R6 respectively):
  ```forth
  \ tests/core/reduce-nat.fs, after the AW section: the first operand no literal and a count Lean refuses
  T{ k-nat 4294967296 nat 3 kernel-refused? k-app big 3 kernel-refused? k-app 4294967296 nat 12 kernel-refused?
     -> true true true }T
  \ tests/front/reduce-nat.fs, after the AW section: the first operand no literal and an exponent above 256
  T{ nat 257 nat-lit 3 fold-refused? sfk two64 3 fold-refused? -> true true }T
  ```
  Also add R5 and R6 to tests/mutants/faults.d/nat-ops-aw.toml (old/new texts above; tests
  `$GFORTH tests/core/reduce-nat.fs` and `$GFORTH tests/front/reduce-nat.fs`).

**B2 (medium, blocking: reuse). `lf-nat-lits-by` and `lf-nat-lit-succ` hand-write an outcome chain that lib/outcome.fs
already provides.**
- The new shape is "test, then the step, else -1 invalid with the step not run" (nat-ops.fs:168-170, 175-176). That is
  `flag>outcome` (lib/outcome.fs:44) followed by `ok-apply3` or `ok-apply` (lib/outcome.fs:103, 96).
- The private failure word `nop-not-lit ( x -- -1 outcome )` (nat-ops.fs:168) is a copy of front/infer.fs:108's
  `if-bad ( x -- -1 outcome )`. The same phrase `drop-invalid no-result` is also written inline at front/unfold.fs:86
  and present/binder-table.fs:105 and 127.
- `check-duplicates.py --new-words` cannot see this: the bodies are under its size threshold. The same class blocked
  ops-c1 (B1) and s3a-decide (B1).
- Fix (checked in a copy: all four test files pass; the k3 and kgrid probes are byte-identical to fbe5de3e's; one word
  fewer; deep shuffles unchanged at 5):
  ```forth
  \ The operands' test before any is read: both literal leaves, or invalid.
  : nop-lits? ( a b -- flag ) lf-lit-leaf? swap lf-lit-leaf? and ;
  : lf-nat-lits-by ( a b i xt -- node outcome )
    2over nop-lits? flag>outcome swap ok-apply3 ;
  ...
  : lf-nat-lit-succ ( a -- node outcome )
    dup lf-lit-leaf? flag>outcome ['] nop-succ ok-apply ;
  ```
  `nop-not-lit` then goes away. Faults `aw-nat-ops-invalid-as-ok` and `aw-nat-ops-refusal-keeps-a-cell` need new
  old/new texts, for example `flag>outcome` → `drop outcome-ok`, and `swap ok-apply3` → `swap ok-apply2`. The other
  copies (`if-bad` and the three inline phrases) may become a lib word `invalid-result ( x -- -1 outcome )` in this
  branch, or a 9.4.8l row like AX.

**L1 (low; unreachable). `lf-reduce-nat-pred` and `lf-reduce-nat-constructor` are now half fail-closed, and the change
is not documented or tested (kernel/reduce-nat.fs:67-76).**
- Both are public kernel words. On a non-literal they read its fields as a literal before any test:
  - pred: `lf-lit-small?`, then `lf-lit-cell`;
  - ctor: `lf-term-second@ 0=`.
- So their answer now depends on the node's second field. Probe `probe/pred.fs`, old → new:

  | Call | Old | New |
  |---|---|---|
  | pred of the constant Nat | ok, made-up literal 2^64-1 | unchanged |
  | pred of Nat.succ 4 | ok, made-up 5-limb literal read from wrong slab cells | invalid (through `lf-nat-lit-op`) |
  | pred of literal 0 (precondition "above 0") | ok, 2^64-1 | unchanged |
  | ctor of Nat | ok, Nat.zero | unchanged |
  | ctor of Nat.succ 4 | ok, an application | invalid |

- Both callers test first, so none of this is reachable:
  - defeq.fs:495, with `lf-dq-pred?` at 1001 before `lf-lz-offset`'s calls at 970-971;
  - iota.fs:283.
- nat-ops.fs:26-29 says "both callers" of `lf-nat-lit-op` test for literals. It omits this third path, pred (through
  defeq.fs and iota.fs).
- Fix, in this branch (same gate spirit, two words), or record a plan row:
  ```forth
  : lf-rn-pred ( a -- node outcome )   \ the old body of lf-reduce-nat-pred
    dup lf-lit-small? if lf-lit-cell 1- lf-reduce-nat-literal exit then
    1 lf-reduce-nat-literal ok-then? 0= if nip no-result exit then 1 lf-nat-lit-op ;
  : lf-rn-positive? ( a -- flag ) dup lf-lit-leaf? if lf-term-second@ 0<> else drop false then ;
  : lf-reduce-nat-pred ( a -- node outcome ) dup lf-rn-positive? flag>outcome ['] lf-rn-pred ok-apply ;
  : lf-rn-constructor ( a -- node outcome )   \ the old body of lf-reduce-nat-constructor
    dup lf-term-second@ 0= if drop lf-rn-zero exit then lf-reduce-nat-pred ['] lf-rn-succ-of ok-apply ;
  : lf-reduce-nat-constructor ( a -- node outcome )
    dup lf-lit-leaf? flag>outcome ['] lf-rn-constructor ok-apply ;
  ```
  Each word needs a test (k-nat, k-app and literal 0 for pred) and a fault.

**L2 (low; pre-existing, not introduced). The guarantee holds only for a valid node and an index in 0..13.**
- `lf-lit-leaf?` is `lf-term-tag@`, which is unchecked (core/terms.fs:460-464). An index outside the store, such as -1,
  is read, not refused.
- `nop-run` (nat-ops.fs:171) executes `cells nop-ops + @` for any i.
- All callers pass valid nodes and an i from `lf-nat-op` or `lf-whnf-op`, after their -1 test.
- Fix: say "a and b valid term nodes; i 0..13 (not checked)" in the header at nat-ops.fs:18-33. Optionally make the
  guard test i too: `: nop-args? ( a b i -- flag ) 14 u< >r nop-lits? r> and ;` with `2over 2over drop` or
  equivalent. Or record a plan row.

## The questions of the brief, with evidence

**1a. Literal cases identical (outcome, result, diagnostic, depth, sentinel).**
- I re-generated the implementer's probes (gen_kgrid.py, gen_k2.py, gen_k3.py) on my two trees and ran them on
  Gforth 1.0.0.
- kgrid: 8,749 `lf-reduce-nat-binary` cases (14 operations × 25 values from 0 to 2^200, the operands' limb hash
  printed), plus succ, pred and constructor on all 25. Old and new outputs are **byte-identical** (`cmp`). They are
  also identical to the implementer's saved output.
- k2: crowded term and constant stores, and every allocation refused in turn for 6 operand pairs × 14 operations:
  661 lines identical. The 84 differing lines are all non-literal cases.
- k3: `lf-nat-lit-op`, `lf-reduce-nat-binary` and `lf-meta-nat-fold` on 5×5 literals and 4 non-literals, plus
  succ: 1,047 lines identical.
  - All 852 differing lines are non-literal. Each now answers invalid with node -1, diagnostic 0 and depth change 0,
    and the 7777 sentinel is kept. No line shows `S!`, `THROW` or `SHORT`.
  - Old answers on those lines: 710 ok with a made-up literal, 120 ok with a Bool constant, 9 full 93,
    6 rejected 92, 7 unsupported.

**1b. Callers, each testing for literals first:**
- kernel/whnf.fs:605 `lf-nat-second` → `lf-reduce-nat-binary`. Both operands come from `lf-nat-ext` (598-600):
  the node itself if `lf-lit-leaf?`, else `0 lf-reduce-nat-literal` for Nat.zero, else `lf-whnf-none`. None and
  failures leave at 603-604 and 607-608 before the call.
- kernel/whnf.fs:609 → `lf-reduce-nat-succ`, after the same test.
- kernel/reduce-nat.fs:69 `lf-reduce-nat-pred` → `lf-nat-lit-op`. It is called only from defeq.fs:495 and
  iota.fs:283, both behind `lf-lit-leaf?`.
- front/whnf.fs:786 and 792 → `lf-meta-nat-fold` with values from `lf-meta-nat-value?` (front/reduce-nat.fs:73-75:
  a literal leaf or `0 lf-nat-lit`), after its flag test at 788 and 791. The first value travels as the frame's aux.
- No other caller exists in src/ (`grep` of all five names).

Tripwire evidence: in a third copy of fbe5de3e, `nop-not-lit` writes `AWTRIP` to stderr.
- All 146 test files under tests/ that load kernel, front or nat-ops code ran on it. 137 exit 0. The other 9 are
  fragments other tests include, which stop on an undefined word at load.
- `AWTRIP` appears only in the three changed test files: 92, 48 and 47 times. These are exactly the counts of their
  new non-literal calls.
- `bin/leanforth check` ran on tests/front/{decide,s1,s2,whnf}-slice.ndjson. The decide slice has 1,263
  declarations, all accepted. Outputs are identical to the old tree and there were 0 trips.
- A second instrumented run counted the operations actually reached: 258 `lf-nat-lits-by` calls and 74 succs (decide
  slice); 34 and 24 (whnf slice).
- `bin/leanforth check --env decide-slice.ndjson --elab-data ...` ran on the decide tactic's dc-arith, dc-logic,
  dc-ops and w-dc-add .lf files, which use the front-end fold. Verdicts are identical to the old tree, there were
  0 trips. `lf-nat-lits-by` calls reached (kernel and front end together) were 298, 290 and 394.

Before the change, a non-literal would have got **ok with a made-up literal** (710 of k3's lines): a soundness hazard
had any path existed. **No such path existed**, before or after, on any caller above.

**1c. What callers do with invalid.**
- Kernel: `lf-whnf-nat-back` (whnf.fs:563-565) passes any non-ok outcome to `lf-whnf-failed`, so whnf, and with it
  the declaration's check, fails with that outcome. Invalid maps to exit 4 and is never accepted.
- The only verdict that moved on a non-literal is pow and shiftLeft by an application with a count read from its
  fields: from rejected (92) to invalid. It is unreachable (1b).
- Front: `wc-folded` (front/whnf.fs:779-780) turns a failure into whnf's failure. The front end is untrusted, so no
  front-end answer can make a declaration accepted.
- `check-outcome-steps.py` reports 122 sites, 122 right.

**2. Lean fidelity.**
- Lean tests `is_nat_lit_ext` on the first argument's whnf, then on the second's. It does this before reading any
  value (type_checker.cpp:614-619, 630-634, 648-651, 663-666, 678) and before `get_count_arg` (637, 656).
- In LeanForth that test is kernel/whnf.fs's `lf-nat-ext`, which answers none and lets delta run, as Lean's
  `none_expr()` does.
- The words reviewed here correspond to `get_nat_val`, which in Lean begins with `lean_assert(is_nat_lit_ext(e))`. A
  non-literal there is a broken internal invariant, not Lean's "none".
- So **invalid (fail closed) is right**. Answering none would silently send a caller's bug on to delta.
  - The vocabulary has no "internal" outcome; invalid is the closest and matches nat-ops' other caller-error answers
    (`nop-literal`).
  - Note: `-1 ok` would be read by whnf.fs as `lf-whnf-none` (-1). That is why the fault `aw-nat-ops-invalid-as-ok`
    matters.
- **The new order (test, then count) matches Lean's. The old order (count, then test) did not.** Neither is reachable.
- Meta's `withNatValue` (WHNF.lean:976-986) is mirrored by `lf-meta-nat-value?`. `reducePow` checks the exponent
  only after both values (995-1000); the new fold order matches.

**3. Refusal keeps the caller's cells; stack comments.**
- Every refusal ends ( -1 outcome ) with the sentinel kept: tests (111), probes (7777, depth change 0) and the fault
  `aw-nat-ops-refusal-keeps-a-cell` (caught).
- Stack comments traced on every branch:
  - `lf-nat-lits-by` (true branch: `execute`; false branch: `2drop drop nop-not-lit`);
  - `nop-run`, `lf-nat-lit-succ`, `lf-rn-binary` (pow / shl / other), `rn-fold-op` (over threshold / other);
  - `lf-meta-nat-fold`: succ is tested first, so v2 (0) is never given to the literal test.
- All are true. `check-outcome-steps.py`: 0 wrong.

**4. Cost.**
- `probe/bench2.fs`: 100,000 calls each, the least of 9 rounds interleaved old/new. The machine was loaded (load
  8-10 on 10 cores).

  | | Gforth 1.0, old → new (ms) | gforth-fast, old → new (ms) |
  |---|---|---|
  | `lf-nat-lit-op` mul | 224 → 236 | 88 → 94 |
  | kernel mul | 237 → 264 | 91 → 87 |
  | kernel ble | 519 → 553 | 199 → 214 |
  | fold mul | 224 → 252 | 81 → 92 |
  | a pair of `lf-lit-leaf?` tests alone | 6 | 2 |

- The extra cost is 0.03-0.3 µs per operation, against about 2.3 µs (Gforth 1.0) per operation, mostly the scratch
  arena's allocate and free. `leanforth check` runs on gforth-fast, where the kernel products are within noise. The
  decide slice reaches 258 operations per check, so the cost is under 0.1 ms.
- Can one test go? The fault R1b removes the kernel's outer test for every operation except pow and shiftLeft. It
  survives because it is **equivalent**: the inner test refuses those 12 operations. The outer test is needed only for
  pow and shiftLeft's order (R1, outer test removed for them, is caught: rejected 92).
- Dropping the inner test needs an unchecked runner that the policies call. That reopens review s3a-decide M1 for any
  future caller.
- **Recommendation: keep both tests.** Do not add an unchecked entry. The cost does not justify it.
- FORTH_LIBRARY.md's recorded figures (236 → 273, 90 → 96) are consistent with these.

**5. Faults.**
- The implementer's 7 faults (faults.d/nat-ops-aw.toml) are each caught by the test named in the fault.
- Mine:

| Fault | Where | Caught by |
|---|---|---|
| R1 kernel: pow/shl read the count before the test | kernel/reduce-nat.fs:63 | tests/core/reduce-nat.fs only |
| R4 kernel: `lf-reduce-nat-succ` unchecked (`1 lf-nat-lit ['] nop-add ok-apply2`) | kernel/reduce-nat.fs:65 | tests/core/reduce-nat.fs only |
| R2 front: threshold before the test (old body) | front/reduce-nat.fs:84 | tests/front/reduce-nat.fs only |
| R2b front: Nat.succ unchecked | front/reduce-nat.fs:83 | tests/front/reduce-nat.fs only |
| R3 invalid mapped to ok, a made-up literal 0 (`2drop 2drop 0 lf-nat-lit`) | core/nat-ops.fs:170 | tests/core/nat-ops.fs (also both reduce-nat files) |
| R3b succ's refusal mapped to ok 0 | core/nat-ops.fs:176 | tests/core/nat-ops.fs (also both reduce-nat files) |
| R5 kernel tests only the second operand before the count | kernel/reduce-nat.fs:63 | **survives** (B1) |
| R6 front tests only the second operand before the threshold | front/reduce-nat.fs:84 | **survives** (B1) |
| R1b kernel's outer test only for pow/shl | kernel/reduce-nat.fs:63 | survives: equivalent (see 4) |

**Coverage classes (TEST_COVERAGE_REVIEW.md)** for the changed words: `lf-nat-lits-by`, `lf-nat-lit-op`,
`lf-nat-lit-succ`, `lf-reduce-nat-binary`, `lf-reduce-nat-succ`, `lf-meta-nat-fold`.
1. Every outcome is reached: ok, invalid, rejected 92, full 93 and unsupported. Exhausted is reached by the existing
   sweeps.
2. Malformed input: the first, the second or both operands no literal; the gap is B1.
3. Stack and sentinel: tests and probes.
4. Workflows: unchanged on literals (the tripwire runs); refusal is unreachable end to end.
5. Resources: a refusal makes no node (`lf-term-count`, nat-ops tests only) and sets no diagnostic (kernel tests);
   the existing allocation sweeps are unchanged.
6. State: none.
7. Regression pins: the old rejected-92 and made-up-literal answers are pinned as invalid. The pred and ctor change
   is not pinned (L1).
8. Lean: the literal paths are byte-identical, so the existing pinned-Lean comparisons stand. Not re-run.

## Reuse (step 3a)

Searched:
- `lib/outcome.fs` and LIBRARY_WORDS.md for guard and outcome-chain words. Found `flag>outcome`, `ok-apply`,
  `ok-apply2`, `ok-apply3`, `ok-and`, `drop-invalid`, `no-result`.
- `grep -rn` over src/ by name and by shape:
  - `drop-invalid no-result`: 3 inline sites and `nop-not-lit`;
  - `( x -- -1 outcome )` definitions: `if-bad` in front/infer.fs:108;
  - `drop -1 outcome-invalid`: 67 inline sites, outside this branch;
  - `lf-lit-leaf? swap lf-lit-leaf?`: only nop-lits?;
  - `if execute else`: no library guard-by-flag combinator other than `flag>outcome` with `ok-applyN`.

Tools:
- `scripts/check-duplicates.py`: 187 baseline groups, none new or grown. The `--report` lines for nat-ops and
  reduce-nat are the same before and after.
- `check-duplicates.py --new-words --base 8b6272c1 --head fbe5de3e`: no new small copies.
- `scripts/check-lib-callers.py`: every lib file has a caller or a plan row (bigint.fs: plan FE1i-4).

Findings:
- B2 (blocking): use `flag>outcome` with `ok-apply3` / `ok-apply`.
- No module copied from another, and no general operation is buried in a module. `lf-nat-lits-by` is Nat-specific
  and belongs in core/nat-ops.fs.

## Re-entrancy (step 4a)

- No new module-level state: no VARIABLE, VALUE or CREATEd table.
- `nop-ops` is the existing constant xt table, written while loading.
- `lf-nat-lits-by` holds nothing between calls.
- The words run inside a context's term store, as before.

## Forth style

`python3 scripts/forth-metrics.py --words 10` on the three files (new tree):
- core/nat-ops.fs: 53 words (old 48), 86% of words 1-2 lines and 13% 3-5, none longer; deep shuffles 5 (old 4,
  the new `2over`); return-stack ops 22.
- front/reduce-nat.fs: 14 words (13), 50% / 50%, 0 shuffles.
- kernel/reduce-nat.fs: 15 words (14), 66% / 33%, 1 shuffle.
- Total: 82 words, none over 5 lines, no globals, no locals, every word with a stack comment, no line over 90.
- Longest words: `nop-pow` and `nop-shl`, 5 lines each, unchanged.

Style findings:
- `lf-nat-lits-by` takes four items (a b i xt). That is acceptable: it is the `ok-apply3` combinator shape, and B2
  makes it literally that.
- `lf-rn-binary` (kernel/reduce-nat.fs:54-56) lost its comment to the public word below it. A two-arm IF chain on
  pow and shl is fine (two arms, no CASE needed). One line would help:
  `\ Lean's policies on literals: pow's count, shiftLeft's 0 and count, else the table.`
- The other new words are one-liners with honest names.
- The deep-shuffle ratchet (`check-forth-quality.py`) was **not run**: it needs git, and the extracted tree has none.
  The `2over` adds one to core/nat-ops.fs, which has no explicit baseline entry. The implementer's `pre-tier` decides
  whether that passes.

## Commands, versions, limits

Commands and tools:
- Gforth 1.0.0 (`.tools/gforth/bin/gforth`, `gforth-fast`) and Gforth 0.7.3 (`.claude/work/A/gforth073.sh`), Python
  3.13; `ulimit -u 500`, stdin from /dev/null.
- Probes and scripts are in the scratch folder `aw-review/`: kgrid, k2 and k3 from the implementer's generators, plus
  my bench2, pred, first, the tripwire tree, and the mutant helper `mut-tools/mut.py`.

Tests run:
- tests/core/nat-ops.fs, tests/core/reduce-nat.fs, tests/front/reduce-nat.fs and tests/core/defeq.fs on Gforth 1.0
  and gforth-fast: all exit 0.
- The first three on Gforth 0.7.3: exit 0.
- 146 kernel and front test files on the tripwire tree, 4 export slices, and 4 .lf files, on old and tripwire trees.

Not run: make, any suite, `make cover-changed`, `check-forth-quality.py`, pinned Lean. Lean was not needed: the
literal paths are byte-identical, and Lean cannot express a non-literal at this point.

Uncertainty:
- The front end's first value is carried as the frame's aux (front/whnf.fs:785, 792). I read this, but did not trace
  it through every frame operation. The tripwire runs (0 trips over 982 `lf-nat-lits-by` calls in the .lf runs) and the existing fold tests support it.
- This AI review does not replace the owner's approval of the gate summary (AGENTS.md "Review gates", item 4).

## Fixes (2026-11-20, branch `nat-ops-fail-closed`, commit `9f1b95d4`)

All four findings are fixed in one commit, `9f1b95d4`. Every fault named below is in
`tests/mutants/faults.d/nat-ops-aw.toml`, and each is caught by the test it names.

| Finding | Commit | Test or fault |
| --- | --- | --- |
| B1 | `9f1b95d4` | The review's lines were added as written. In tests/core/reduce-nat.fs, these answer invalid with no diagnostic (`kernel-refused?`): the constant Nat raised to 2^32, Nat.succ 4 raised to 2^64, and Nat.succ 4 shifted left by 2^32. In tests/front/reduce-nat.fs, these answer invalid (`fold-refused?`): Nat raised to 257, and Nat.succ fk raised to 2^64. R5 is planted as `aw-kernel-second-only` (tests/core/reduce-nat.fs) and R6 as `aw-front-second-only` (tests/front/reduce-nat.fs). Both are caught. |
| B2 | `9f1b95d4` | `lf-nat-lits-by` is now `2over nop-lits? flag>outcome swap ok-apply3`, and `nop-not-lit` is deleted. The one-operand form is a new public word, `lf-nat-lit-by ( a xt -- node outcome )` (`over lf-lit-leaf? flag>outcome swap ok-apply`), in core/nat-ops.fs. A word was needed because the review's `dup lf-lit-leaf? flag>outcome ['] X ok-apply`, written in both `lf-nat-lit-succ` and L1's `lf-reduce-nat-constructor`, formed a new duplicate group (`check-duplicates.py`: 9400797d5142). With the word, no new or grown group. It is tested in tests/core/nat-ops.fs: a step on a literal runs, and a constant or an application gives -1 invalid, with the sentinel kept each time. Faults re-pointed to the new text: `aw-nat-ops-invalid-as-ok` (the refusal's invalid turned into ok with node -1, the meaning the fault had), `aw-nat-ops-refusal-keeps-a-cell` (`ok-apply3` → `ok-apply2`) and `aw-nat-ops-succ-unchecked` (`lf-nat-lit-succ` calls `nop-succ` directly). New fault: `aw-nat-lit-by-unchecked`. All are caught by tests/core/nat-ops.fs. `front/infer.fs`'s `if-bad` and the three inline `drop-invalid no-result` copies (front/unfold.fs:86, present/binder-table.fs:105 and 127) are outside this branch's files. They were not touched here and are planned as 9.4.8l (AZ). Deep shuffles of nat-ops.fs: 5, within its allowance of 7 (no baseline entry: 0.15 a word); `check-forth-quality.py` ratchet holds. |
| L1 | `9f1b95d4` | Lean computes a predecessor only for a literal that is not 0 (`is_nat_succ`, type_checker.cpp:1029-1035), and `nat_lit_to_constructor` asserts a literal (inductive.cpp:1359-1366). So now `lf-reduce-nat-pred` is `dup lf-rn-positive? flag>outcome ['] lf-rn-pred ok-apply`, with `lf-rn-positive?` defined as `dup lf-lit-leaf? swap lf-term-second@ 0<> and` (no IF; it reads only the tag and the limb count). `lf-reduce-nat-constructor` is `['] lf-rn-constructor lf-nat-lit-by`. The old bodies are `lf-rn-pred` and `lf-rn-constructor`. tests/core/reduce-nat.fs: the predecessor of the constant Nat, of Nat.succ 4 and of the literal 0, and the constructor form of Nat and of Nat.succ 4, each answer -1 invalid with the 111 under it kept, no diagnostic and no node made. The predecessor of 1 is still 0, and the constructor form of 1 is still Nat.succ 0. The callers' checks are pinned in tests/core/defeq.fs: <br>- `lf-dq-pred?` is false on the literal 0 and on Nat.zero, and true on 5 and on Nat.succ 4; <br>- `lf-dq-pred` of Nat.succ 4 is its argument 4, and of 5 is 4; <br>- `lf-iota-lit` keeps Nat.zero and Nat.succ 4, turns 3 into Nat.succ 2 and turns 0 into a constant. <br>Faults: `aw-kernel-pred-unchecked`, `aw-kernel-pred-of-zero` and `aw-kernel-constructor-unchecked` (tests/core/reduce-nat.fs); `aw-defeq-pred-caller-unchecked`, `aw-defeq-pred-test-zero` and `aw-iota-literal-caller-unchecked` (tests/core/defeq.fs). All caught. nat-ops.fs's header now says "every caller" and names the predecessor's path. |
| L2 | `9f1b95d4` | nat-ops.fs's header now says that the refusal assumes valid term nodes and an operation index 0-13, and that neither is checked. Checking them is plan 9.4.8l (AY). |
| Style | `9f1b95d4` | `lf-rn-binary` has its one-line comment back. |

**No reachable verdict changed** (probes `gen_kgrid.py`, `gen_k2.py`, `gen_k3.py` and `compare.py`, Gforth 1.0.0, against main
`8b6272c1` and against `fbe5de3e`):
- kgrid: 8,823 lines, byte-identical to main's. These include the predecessor on every literal above 0 and the
  constructor form on every literal.
- k2: 661 lines identical to main's, 84 differ.
- k3: 1,047 lines identical to main's, 852 differ.
- Every differing line is a non-literal case that now answers invalid with the sentinel kept (`compare.py` exit 0),
  the same counts as the review's.
- All three outputs are byte-identical to `fbe5de3e`'s.
- No line shows `THROW`, `S!` or `SHORT`.

**Commands, all exit 0**, with `ulimit -u 500` and stdin from /dev/null:
- tests/core/nat-ops.fs, tests/core/reduce-nat.fs, tests/core/defeq.fs, tests/front/reduce-nat.fs and
  tests/front/tactics/decide/test.fs, on Gforth 1.0.0 and on gforth-fast.
- `make test-kernel-reduction JOBS=3`.
- `python3 tests/front/tactics/decide/check.py`: 3 files accepted, node for node pinned Lean's; 13 wrong twins
  refused.
- `make cover-changed BASE=main JOBS=3`: every block on a changed line ran.
- `scripts/mutants.py --check`: 3,156 entries, 0 stale.
- `scripts/mutants.py --only`: the 41 faults on core/nat-ops.fs, kernel/reduce-nat.fs and front/reduce-nat.fs plus
  the `aw-` faults on defeq.fs and iota.fs. All 41 caught.
- `check-forth-quality.py`, `check-duplicates.py` (no new or grown group) and `check-progress.py`.

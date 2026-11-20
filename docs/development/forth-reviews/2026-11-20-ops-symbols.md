# Forth review: Lean's symbols as notation words, their ASCII spellings, and `^` as `rightact%` (slice S3a-ops C2-C4, plan S3; parser gate approved by the owner 2026-11-20) (2026-11-20)

Branch `ops-symbols`, range **8b6272c1..eab85b83** (6 commits: 8d449f1c, 97dd3dd7, a08c068b, b86b1763, 1e48754a, eab85b83).

**Findings: 0 high, 3 medium (all blocking), 5 low.**

**Verdict: merge after fixes.**
- B1, B2 and the cheap in-tier part of B3 (a, b) are fixed before the merge.
- B3 (c) gets a plan row.
- L1 to L5 are fixed or get plan rows.

**No difference from pinned Lean was found.** I compared 73 statements of my own with pinned Lean, type and value node for node: 146 terms, all identical. I also ran 38 slice runs: 76 terms, all identical.

For the owner: every symbol word builds exactly the term Lean builds for the same statement. That includes the argument order of `- / % < > ≥ ^ ∣`, `>` built as Lean's `GT.gt a b`, and `^` choosing the number type as Lean does. Every misuse I tried stops with a clear error, and nothing wrong was accepted. Two gaps remain:
- the tests that guard this in the regular runs are thinner than the checks the implementer ran once by hand;
- one load-time table can still be written after the checker starts.
Both are small fixes.

Scope and method:
- Reviewed `git diff 8b6272c1...eab85b83 -- src tests scripts Makefile`, plus the documentation diff. Golden data was only sampled.
- Work was done on `git archive eab85b83` (and `8b6272c1`) extracted into the scratchpad. No worktree was edited.
- Tools: Gforth 1.0.0 (`gforth`, `gforth-fast`) from `.tools`, pinned Lean 4.35.0's `lean` binary, `ulimit -u 500`, stdin `/dev/null`.
- Probes used the branch's own term dump: `gforth-fast src/main.fs tests/front/elab-dump.fs -e "cli-dump (bye)" check --snapshot init-1.lfsn --elab-data init.elab.ndjson --steps - FILE.lf`.
- Lean twins used the S-expression printer of tests/front/tactics/goal-layer.lean.
- Proofs were `by-exfalso by-assumption` from a hypothesis `False`, so any statement, true or false, with variables could be compared.
- Not run: make, any suite or tier, `make cover-changed`, `scripts/mutants.py`, `check.py` as a whole, Gforth 0.7.3.

## Findings

**B1 (medium, blocking: re-entrancy, FORTH_REVIEWER 4a). The new table `lfn-notations` can be written after `context-new`.**
- Where: src/front/reader.fs:164 (the table), :183-185 (`lfn-entry,`), :192-195 (`lfn-meaning`).
- The table is new module-level state, shared read-only by every context. Its writer never checks `context-sealed?`.
- It also lays the entry down before the row check, so a failed registration leaves its entry behind.
- Reproduction (scratch `seal.fs`):
  1. Load `src/load/checker.fs` and `src/load/front.fs`.
  2. Count the entries: 22.
  3. Run `context-new throw context-use`: `context-sealed?` is -1.
  4. Evaluate `s" Membership.mem" syn-k-binrel lfn-operator: ∈`. It aborts (-2), but only in `lfa-natural!`.
  5. The table now has 23 entries, and `s" ∈" lfn-notations name-table-find` is non-zero.
- The unit tests front.fs:129-134 also write the table after loading (entries `zz`, `$`, `<<` and `!` stay in it).
- The reader.fs header's "State:" line (:37-38) does not mention the table.
- Fix: do as tactic-run.fs:289-290 does, and name the table in the header.
  ```forth
  : lfn-open ( -- ) context-sealed? abort" reader.fs: a notation word after context-new" ;
  ```
  Call `lfn-open` first in `lfn-entry,`.
- Add a front.fs test: after `context-new`, a registration aborts and the entry count is unchanged.
- Add a fault `rd-notation-after-context` that drops the check.

**B2 (medium, blocking: tests and faults). "No homogeneous instance is asked of `rightact%`" (Extra.lean:420) is not pinned by any test.**
- My fault F7, in src/front/elab-term.fs:400:
  - old: `dup et-act? if drop outcome-ok exit then`
  - new: `dup et-act? over et-leaf? and if …`
  - Effect: the `^` operator node gets `et-coe-op`.
- F7 survives tests/front/front.fs, tests/author/author.fs and tests/lib/text-run.fs.
- It also survives the `check.py --init` comparison: dc-symbols.lf gives 14 accepted and 28 terms equal to the golden under the fault. Every `^` there is all numerals, so analyze finds no max type and applyCoe never runs.
- Under F7, `i n ^ i =` (i : Int, n : Nat) stops with 139: my probe file stops at p20. Lean builds `i ^ n = i`.
- The implementer's `et-coe-exponent` removes both skips at once and is caught only through the exponent leaf.
- Fix (verified):
  - Add after front.fs:864: `T{ s" Bool explicit: b Nat explicit: n b n ^ b =" ran -> 119 }T`. Head gives 119; F7 gives 139 and is caught.
  - Add a fault:
  ```toml
  [[fault]]
  id = "et-coe-rightact-op"
  file = "src/front/elab-term.fs"
  old = '''  dup et-act? if drop outcome-ok exit then'''
  new = '''  dup et-act? over et-leaf? and if drop outcome-ok exit then'''
  test = "$GFORTH tests/front/front.fs"
  reason = "S3a-ops C4: rightact% asked for a homogeneous instance (Lean's applyCoe never asks, Extra.lean:420): b ^ n with b : Bool answers 139, not the instance search's 119"
  ```

**B3 (medium, blocking for (a) and (b); a plan row for (c)). No symbol theorem that is accepted is compared node for node with Lean in any recorded run.**
- `check.py --init` is the only place where the symbol files are compared with pinned Lean (check.py:46-48, `SYMBOLS, ASCII` only in `INIT_FILES`). No make target runs it.
- What the tier does run:
  - check_front.py (reference-front) compares syntax trees with pinned Lean, but not ∨ ∣ ¬ ↔ <->, because init-slice lacks those constants.
  - The plain-mode wrong twins (`< ≠ >= \/ <-> ¬`) check only the rejected outcome.
  - front.fs has four Bool error codes.
- The `rightact%` max-type rules (exponent outside the max type, no homogeneous instance, base coerced with no operator above) have no positive comparison anywhere, `--init` included.
- Measured cheap fixes:
  - (a) The 16 theorems of dc-symbols.lf and dc-ascii.lf that avoid `- / ^ Nat.gcd` are accepted on the decide slice:
    - sy_ and as_: mul, pythag, gauss, compare, leap, not, or, iff;
    - 32 of 32 terms equal to goal-layer.golden's existing lines;
    - they cover `* + = > ≥ >= ≠ Ne % ∧ /\ ¬ Not ∨ \/ ↔ <-> < ≤ <=`.
    - Split them into plain-mode `FILES`. No new golden is needed.
  - (b) Add a variables file proved by `by-exfalso by-assumption`, with its Lean twins in goal-layer.lean:
    - my probes p01-p09, p11-p14, p19, p31, p36-p40, p48, p50 (22 theorems);
    - every word including `- / % ^` with a variable exponent;
    - each runs on the decide slice in about 0.5 s;
    - 44 of 44 terms equal pinned Lean's.
    - Not on the slice: numeral bases or exponents of `^` (139, Init's first candidates), `∣` (no Dvd.dvd, 38), and Int (119/139).
  - (c) A daily target, for example `reference-decide-init`:
    - runs `check.py --init` plus an Int-variable file (p20-p24, p29-p30, p32, p34, p41, p44-p47, r1-r8: all identical today);
    - uses Init's snapshot;
    - exits 3 "SKIPPED, NOT A PASS" when the snapshot is missing, as reference-mathlib-slice does.
- B2's unit line covers the most likely C4 regression in the tier already.

**L1 (low, style and reuse). The registration words take too many items, re-implement library and file words, and reach into a library's private layout.**
- `lfn-entry,` (reader.fs:183) takes 5 items.
- `lfn-meaning` (:192) takes 4 items and juggles `>in` through the return stack. That re-implements `lfn-peek` (:127) in the same file.
- `lfn-notations cell+ @` (:185) reads name-table.fs's private `ntab-last` by a raw offset.
- `align here 0 , 0 , constant lfn-notations` (:164) re-implements `name-table:`. A side effect: forth-metrics counts the table as a constant, not a global (reader.fs: "globals 0, constants 1").
- `lfn-entry` (:168) answers 0 if the token were not in the table; that is unreachable today and would be a null dereference.
- Factoring:
  ```forth
  name-table: lfn-notations
  : lfn-new-word ( "word" -- c-addr u )   \ peeked; a word twice aborts
    lfn-peek 2dup lfn-notations name-table-find abort" reader.fs: a notation word twice" ;
  : lfn-entry, ( c-addr u kind "word" -- entry )
    lfn-open lfn-new-word align here >r lfn-notations name-entry , counted, r> ;
  : lfn-meaning ( entry xt "word" -- )
    swap lfn-spelt? 0= abort" reader.fs: a notation word its constant's row lacks" lfa-natural! ;
  : lfn-operator: ( c-addr u kind "word" -- ) lfn-entry, ['] lfn-w-operator lfn-meaning ;
  : lfn-notation-name: ( c-addr u "word" -- ) 0 lfn-entry, ['] lfn-w-named lfn-meaning ;
  ```
- Optional: `lfn-const-at` (:176-177) repeats the shape of `lfn-ident`'s constant branch (:99-104). One word `lfn-const-node ( decl pos -- node n )` would serve both.

**L2 (low, tests). Operand order is pinned in front.fs only for `-` (front.fs:90).**
- A fault that swaps only `>` (F1) or only `≥` (F1c) survives all three unit files.
- check_front.py catches each (`n > m`: reader `GT.gt m n`).
- For `<` (F1b), the plain decide check also catches it. Under that fault the kernel *accepted* `w_sy_lt` as `10 < 20`: a reader slip yields an accepted theorem whose statement is not the text's.
- Fix (verified: head passes; F1 and F1c are caught), after front.fs:98:
  `T{ s" n m >" op-read lf-front-statement dup syn-b@ syn-a@ swap syn-c@ syn-a@ -> 71 0 1 }T`, and the same for `≥`.
- The registration refusals at front.fs:129-137 check only that something aborted (-2), not which check fired. The `zz` line says "no syntax word" but aborts at the row check first. Check the abort message instead.

**L3 (low, tests). Some words never run in the tier, and nothing checks that every listed word got a meaning.**
- `∨` and `∣` never run in any tier test: front.fs has them only in comments, and w-sy-or uses `\/`.
- Nothing checks that every word of `lfa-natural-words` (words.fs:194) got a reader meaning. A word left out of reader.fs would give error 70 at use, undetected.
- Add a front.fs loop asserting `lfn-notations name-table-find 0<>` for each of the 22 spellings.
- B3 (a) brings `∨` into the tier.

**L4 (low, docs). The "How to type each symbol" sentence overclaims for `Ne`.**
- LANGUAGE_REFERENCE.md:268-271 says each typed spelling "means the same thing and builds the same term node for node".
- That is exact for `<= >= /\ \/ <->`, which are the same macro, and for `Not` and `Dvd.dvd`, which are what Lean's notation expands to.
- `Ne` applied is not `≠` (`binrel%`). Pinned Lean elaborates `fun (n : Nat) (i : Int) => n ≠ i` as `@Ne Int (@Nat.cast Int instNatCastInt n) i` and refuses `Ne n i` ("Application type mismatch").
- Typed `Not` inside a namespace with its own `Not` resolves there, while `¬` is the root constant.
- LeanForth refuses the coercion cases today (131), so no wrong term arises. On 8 pairs without coercion the name and symbol forms were identical in Lean and in LeanForth.
- Fix: qualify the sentence.

**L5 (low, test helper). tests/front/tactic-dump.fs:36-44 has no `syn-k-rightact` case.**
- A `^` in a tactic argument would print `?` into tactics.golden and hide a wrong tree.
- Add `syn-k-rightact of ." [ rightact% " .op ."  ]" endof`.

## Lean fidelity

I checked:
- the macros: Notation.lean:280, 285-311 (`rightact% HPow.hPow`), 370-392, 404-406; Core.lean:196-197, 880-882;
- Extra.lean: `toTree.processBinOp` (rightact's rhs goes through `processLeaf`, lhs before rhs), `analyze` (`.binop _ .rightact _ lhs _ => go lhs`), `applyCoe` (rightact: lhs with `none false false`, no `hasHomogeneousInstance`), `toExprCore`, `toExpr`, `elabBinRelCore`.

The code follows each of them:
- `et-act-op!` marks the operator.
- `et-op-lhs` passes the leaf flag, so `et-go` takes the right operand as a leaf, elaborated with no expected type.
- `et-up!` gives the base no operator above (f? none).
- `et-counted?` and `et-coe-at` skip the exponent and the operator.
- A nested `rightact%` exponent (`2 3 2 ^ ^`) is elaborated by its own elabOp; its nodes are cut back before the leaf is made.

`>` builds `GT.gt a b` and `≥` builds `GE.ge a b`, never a flipped `<`. A notation name resolves to the exact root constant (`lfa-const-named`), as Lean's hygienic `And✝` does.

Pinned-Lean comparison, type and value node for node. Binders: n m : Nat, i j : Int, h : False. Proof: exfalso, assumption.

| id | LeanForth | Lean | result |
|---|---|---|---|
| p01 | `n m - m =` | `n - m = m` | same |
| p02 | `n m / m =` | `n / m = m` | same |
| p03 | `n m % m =` | `n % m = m` | same |
| p04 | `n m <` | `n < m` | same |
| p05 | `n m >` | `n > m` (both `GT.gt Nat instLTNat n m`) | same |
| p06 | `n m ≥` | `n ≥ m` | same |
| p07 | `n m ≤` | `n ≤ m` | same |
| p08 | `n m ≠` | `n ≠ m` | same |
| p09 | `n m ^ m =` | `n ^ m = m` | same |
| p10 | `n m ∣` | `n ∣ m` (both `Dvd.dvd Nat Nat.instDvd n m`) | same |
| p11 | `n m <  m n <  ∧` | `n < m ∧ m < n` | same |
| p12 | `n m <  m n <  ∨` | `n < m ∨ m < n` | same |
| p13 | `n m <  m n ≤  ↔` | `n < m ↔ m ≤ n` | same |
| p14 | `n m < ¬` | `¬ (n < m)` | same |
| p15 | `2 3 ^ 4 * 5 +  n =` | `2 ^ 3 * 4 + 5 = n` | same |
| p16 | `2 3 ^ n <` | `2 ^ 3 < n` | same |
| p17 | `2 3 2 ^ ^  n =` | `2 ^ 3 ^ 2 = n` | same |
| p18 | `2 3 ^ 2 ^  n =` | `(2 ^ 3) ^ 2 = n` | same |
| p19 | `n m - 2 / m +  n =` | `(n - m) / 2 + m = n` | same |
| p20 | `i n ^ i =` | `i ^ n = i` | same |
| p21 | `i n ^ j *  i =` | `i ^ n * j = i` | same |
| p22 | `i 2 ^ i =` | `i ^ 2 = i` (exponent stays Nat: `instHPow Int Nat (instPowNat Int Int.instNatPow)`) | same |
| p23 | `i n ^ n ^  i =` | `(i ^ n) ^ n = i` | same |
| p24 | `2 n ^ i =` | `2 ^ n = i` (base `OfNat.ofNat Int 2`) | same |
| p25 | `n 2 ^  n n * =` | `n ^ 2 = n * n` | same |
| p26 | `i j -  j i -  <` | `i - j < j - i` | same |
| p27 | `i 0 >=` | `i >= 0` | same |
| p28 | `n 2 3 + ^  n =` | `n ^ (2 + 3) = n` | same |
| p29 | `i n m + ^  i =` | `i ^ (n + m) = i` | same |
| p30 | `i n ^  j i -  <` | `i ^ n < j - i` | same |
| p31 | `n m ^  m n ^  ≠` | `n ^ m ≠ m ^ n` | same |
| p32 | `i n ^ 2 ^  i =` | `(i ^ n) ^ 2 = i` | same |
| p34 | `i i * n ^  i =` | `(i * i) ^ n = i` | same |
| p35 | `n m ∣  m n ∣  ∧ ¬` | `¬ (n ∣ m ∧ m ∣ n)` | same |
| p36 | `n m <=` | `n <= m` | same |
| p37 | `n m >=` | `n >= m` | same |
| p38 | `n m <  m n <  /\` | `n < m /\ m < n` | same |
| p39 | `n m <  m n <  \/` | `n < m \/ m < n` | same |
| p40 | `n m <  m n ≤  <->` | `n < m <-> m ≤ n` | same |
| p41 | `i 2 ^ j 3 ^ +  i =` | `i ^ 2 + j ^ 3 = i` | same |
| p42 | `i j ∣` | `i ∣ j` | same |
| p43 | `i 0 ≠` | `i ≠ 0` | same |
| p44 | `i 2 ^ 1 -  0 ≥` | `i ^ 2 - 1 ≥ 0` | same |
| p45 | `i 2 ^ 2 ^  0 >` | `(i ^ 2) ^ 2 > 0` | same |
| p46 | `2 2 n ^ ^  i =` | `2 ^ 2 ^ n = i` | same |
| p47 | `i n ^  i n ^  =` | `i ^ n = i ^ n` | same |
| p48 | `n m / m n % <` | `n / m < m % n` | same |
| p49 | `i j / j i % ≤` | `i / j ≤ j % i` | same |
| p50 | `n m ≠ ¬  n m =  ↔` | `¬ (n ≠ m) ↔ n = m` | same |
| r1 | `n 2 ^ Nat.succ m =` | `Nat.succ (n ^ 2) = m` | same |
| r2 | `2 n ^ Int.natAbs m =` | `Int.natAbs (2 ^ n) = m` (expected Int makes the base Int) | same |
| r3 | `i n ^ Int.natAbs m =` | `Int.natAbs (i ^ n) = m` | same |
| r4 | `2 n ^ Int.natAbs  2 n ^  =` | `Int.natAbs (2 ^ n) = 2 ^ n` | same |
| r5 | `n m ^ Int.ofNat i =` | `Int.ofNat (n ^ m) = i` | same |
| r6 | `2 n ^ Int.ofNat  i =` | `Int.ofNat (2 ^ n) = i` | same |
| r7 | `i 2 n ^ ^ i =` | `i ^ 2 ^ n = i` | same |
| r8 | `2 i n ^ * i =` | `2 * i ^ n = i` | same |
| q01-q08 | `2 n ≠`, `2 3 + i ≠`, `i n ^ i ≠`, `n m ∣`, `n m < ¬`, `i 2 3 + ≠`, `2 2 ≠`, `0 i 1 + ≠`, and the same with `Ne`, `Dvd.dvd`, `Not` | the Lean twins of both forms | same (16 of 16; in Lean too the two forms are equal on these) |

Also:
- On the decide slice: the 16 non-`- / ^` theorems of dc-symbols.lf and dc-ascii.lf, 32 of 32 equal to the golden; 22 Nat-variable probes, 44 of 44 equal to pinned Lean.
- Syntax: check_front's 18 cases plus 11 of mine (`n m - m =`, `2 3 ^ 4 * 5 + n =`, `(2 ^ 3) ^ 2`, `(n - m) / 2 + m`, `n ^ (2 + 3)`, …), 29 of 29 equal to pinned Lean's `#expand`.
- Unary minus: `5 -` and `- 5` both stop with error 3 (too few values) at the word. The docs say binary minus only.

## Typed spellings

- `<= >= /\ \/ <->` are registered against the same constant's ASCII row; a neighbour mapping aborts at load (F3, F3b).
- They build the same nodes (front.fs:97-98, 102), and in my probes p36-p40 terms identical to Lean's ASCII statements.
- Search order: `lfa-order!` (groups.fs:52) is `lf-consts lf-locals lf-words 3 set-order`. LF-WORDS is searched first, and Forth's wordlists are absent during a run. Outside a run LF-WORDS is not in the order (front.fs:121-123: `7 3 -` etc. are Forth's).
- `\/` and `/\` are tokens of their own: 58 in kernel form (author.fs) and 38 or a word in natural form, never the comment `\`.
- `<->` is a separate token from `->` (70 today), so it will not clash when FE2 adds `->`.
- Glued or look-alike tokens are refused at the token, never misread:

  | input | error |
  |---|---|
  | `3<4`, `2^3` | 35 |
  | `n<m`, `m<=`, `=<`, `/\/`, `∧∧`, `＜` (U+FF1C), `−` (U+2212) | 1 |
  | `|` | 81 |

- Kernel form: `>=`, `<->`, `%`, `∣` (mine) and `/\`, `-`, `≠`, `<=`, `\/`, `∧` (the implementer's) are 58. `^` keeps the universe meaning.

## Failure behaviour

Reader, on init-slice:

| input | error | meaning |
|---|---|---|
| `5 -` / `- 5` / `n m - -` / `n m ^ ^` | 3 | too few values |
| `n n = m m = m ∧` | 18 | one term before `:=` |
| `' +`, `' ∧`, `' <=` | 59 | tick |
| universe operand of `+ ∧ ^` | 7 | a universe where a term is needed |
| `∣ ¬ <-> \/` without their constant | 38 | unknown constant |

On s2-slice, `>` and `≠` without GT.gt or Ne give 38 at elaboration.

Elaboration, on Init:

| input | result | Lean |
|---|---|---|
| `n m ∧` (Nat operands) | 131, exit 2 | type error |
| `n m ¬` | 18, exit 4 | — |
| `n i ^ n =` | 125 "failed to synthesize", exit 4 | failed to synthesize `HPow Nat Int ?` |
| `n i <` | 131 | inserts `↑n` |
| `n m ∣ m ∣` | 131 | — |

No crash and no wrong acceptance. The kernel checks every built term, but B2 and L2 show a fidelity slip can yield an accepted theorem whose statement differs from the text (F1b accepted `w_sy_lt`). That is why the in-tier comparisons of B3 matter.

## Reuse

What was searched:
- LIBRARY_WORDS.md and FORTH_LIBRARY.md (name-table.fs, text-run.fs);
- grep over src for `trim|strip|-trailing|skip-blanks`, for `parse-name dup while`, for `>in @ … >in !` peeks, and for `syn-kind@`, `syn-k-binop`, `syn-k-binrel` walkers;
- `python3 scripts/check-duplicates.py .`: 187 baseline groups, none new or grown;
- `--new-words --base 8b6272c1 --head eab85b83` (main checkout, read-only): none;
- `scripts/check-lib-callers.py`: every lib file has a caller (bigint planned).

Results:
- `text-trim` (text-run.fs:127) is new. There was no trim before: `lfa-skip-blanks` is leading-only over `lfa-blank?`, bytes.fs's `reader-trim` trims a reader's bounds, and `lf-tex-trailing` counts by an xt. It is built from `text-from` and standard `-TRAILING`, with its caller reader.fs. Good.
- The registry reuses lib/name-table.fs, but with the defining word re-implemented, a private offset and `lfn-peek` re-implemented (L1).
- The four old operators moved onto the registry; `lfn-op-*`, `lfn-w-add/mul/eq/le`, `lfn-inner`, the old `lfn-spelt?`, the `lfn-notation` lines, words.fs:187-190 and print-forth's `+ = * ≤` are all gone, so no copy is left.
- The two-file split is justified: the syntax words and their kernel-form refusal (58) must exist in kernel-form runs without the front end. A mismatch aborts at load one way (`lfa-natural!`) and is untested the other way (L3).
- `lfa-natural-words`' loop is the third `begin parse-name dup while … repeat` line (print-forth.fs:92, program/verify.fs:69). It is an idiom, and I found no library word worth writing.
- No other src walker misses `syn-k-rightact`; the test helper tactic-dump.fs does (L5).

## Tests

My planted faults (unit files run on Gforth 1.0 in hard-linked scratch copies):

| fault | change | front.fs | author.fs | text-run.fs | caught by |
|---|---|---|---|---|---|
| F1 | `>` operands swapped | survives | survives | survives | check_front.py |
| F1b | `<` operands swapped | survives | survives | survives | check_front.py; decide check.py plain (kernel accepted w_sy_lt) |
| F1c | `≥` operands swapped | survives | survives | survives | check_front.py |
| F2 | `et-acting!` no-op (exponent counted and coerced) | caught | | | front.fs |
| F2b | `et-act-op!` no-op | caught | | | front.fs |
| F2c | base gets `tn-up` = HPow | survives | survives | survives | equivalent: HPow has one default instance; my 49 probes are unchanged |
| F3 | `<=` mapped to LT.lt | load abort | | | front.fs (any file loading reader.fs) |
| F3b | `/\` mapped to Or | load abort | | | front.fs |
| F4 | notation name resolved in the declaration's namespace first | caught | | | front.fs (the namespace Foo `And` test) |
| F7 | `^` operator asked for a homogeneous instance | survives | survives | survives | not caught, `--init` included (B2) |

The four faults asked for, and the single test file that catches each:
- binrel argument order: tests/front/check_front.py;
- exponent counted in the max type: tests/front/front.fs;
- ASCII spelling mapped to a neighbour: tests/front/front.fs (load abort);
- `¬` resolved through the namespace: tests/front/front.fs.

Coverage classes:
- Pass: missing in the tier (B3).
- Fail and malformed input: good.
- Interfaces: good.
- Workflow: `--init` only.
- Resources: shared, unchanged paths.
- State: B1.
- Regression pins: goldens present.
- Lean compatibility in the tier: syntax yes, elaboration of an accepted theorem no (B3).

The structural concern: the slice-level testing in the tier catches reader-level slips and refusal paths. It does not catch elaboration fidelity of an accepted theorem, nor the C4 max-type rules. The cheapest way to put the comparison into a recorded run is B3 (a) and (b), plus B2's line; then (c) as a daily target.

## Forth style

`python3 scripts/forth-metrics.py --words 10` on the six changed files:

| file | words | 1-2 lines | 3-5 lines | longer | other |
|---|---|---|---|---|---|
| reader.fs | 67 (base 64) | 83% | 16% | none | globals 0, constants 1 (the table; L1), return-stack ops 16 (18) |
| elab-term.fs | 150 (145) | 59% | 40% | none | — |
| words.fs | 53 | 81% | 18% | none | — |
| text-run.fs | 26 | 84% | 15% | none | — |
| syntax.fs | 19 | | | none | — |
| print-forth.fs | 158 | | | 2 of 6 lines (unchanged words) | — |

- Every new word has a stack comment; there are no locals, no `PICK` or `ROLL`, and no new `VARIABLE`.
- The elab-term.fs changes are small, well-factored words. `tn-act` carries two documented meanings (operator and its exponent) that every consumer treats alike.
- Style findings: L1 (`lfn-entry,` takes 5 items and `lfn-meaning` 4 with `>r` juggling; a private-layout raw offset; `name-table:` and `lfn-peek` re-implemented), with the factoring written out above.
- New globals:
  - `lfn-notations`: written by `lfn-operator:` and `lfn-notation-name:` while reader.fs loads, read by the reader in runs; unsealed (B1).
  - 17 new `lf-pf-more` records and 17 LF-WORDS syntax words with `lfa-natural!` meanings: load-time, through pre-existing unsealed mechanisms.
  - `tn-act`: a field of the context slab `et-tree`, one per context.

## Commands and limits

- Run: the unit files (front.fs, author.fs, text-run.fs) on Gforth 1.0 for the head and ten fault copies; probe files with gforth-fast and `cli-dump` against Init's snapshot (all about 13 s); pinned Lean on the twin files; check_front's tree comparison via a wrapper that skips its export self-test.
- Not run: suites, make targets, coverage, mutants.py, Gforth 0.7.3, gforth-fast unit runs.
- The Lean twins `import Lean`, as goal-layer.lean does.
- An AI review does not replace the owner's gate approval, which is already recorded.

Scratch artifacts:
- probe files: /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/probes/probe.lf, …/probes/probe.lean, …/probes/probe2.lf, …/probes/probe3.lf;
- slice runs: /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/probes/slice/;
- fault copies: /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/faults/;
- tools: /tmp/claude-1000/-home-peter-code-LeanForth/69a89404-3a7f-48aa-b333-1f7651c5eb48/scratchpad/tools/ (plant.py, units.sh, probe.sh, cmp.py, trees.py, gen*.py).

## Fixes

Made on branch `ops-symbols` after the review, in two commits: `ccbe966a` (B1, B2, L1, L2, L3, L5)
and `26761ac1` (B3, L4). Each fault named below is in `tests/mutants/faults.d/s3a-ops.toml` or
`tests/mutants/faults.d/decide-init.toml` and was caught (`python3 scripts/mutants.py --only ...`,
2026-11-20: 9 run, 9 caught).

| Finding | Resolution |
| --- | --- |
| B1 | `ccbe966a`: reader.fs's `lfn-open` refuses a registration once `context-sealed?` (as tactic-run.fs does); the row check, the syntax-word check and the twice check all peek the word and run before the entry is laid down and the meaning given; the header's "State:" line names the table. front.fs: after `context-new` a registration aborts with its message and the entry count is unchanged; the test entries `zz`, `$`, `<<`, `!` are refused before they are written. Faults `rd-notation-after-context`, `rd-notation-no-syntax-check`. Fixed. |
| B2 | `ccbe966a`: front.fs `b n ^ b =` with `b : Bool` answers 119 (139 under the fault). Fault `et-coe-rightact-op`. Fixed. On Init the positive cases (`i n ^ i =` and the other max-type rules) are now compared node for node with pinned Lean every night (B3 (c): `si_p20`-`si_p24`, `si_p29`, `si_p30`, `si_p32`, `si_p34`, `si_r1`-`si_r8`). |
| B3 (a) | `26761ac1`: the nine talk theorems the decide slice elaborates (mul, pythag, gauss, gcd, compare, leap, not, or, iff; gcd too, which the slice also accepts), with symbol words in `dc-symbols.lf` and in ASCII in `dc-ascii.lf`, are in `tests/front/tactics/decide/check.py`'s plain-mode `FILES`: 18 theorems, each term node for node `goal-layer.golden`'s existing lines. The five whose `- / ^` need Init moved to `dc-symbols-init.lf` and `dc-ascii-init.lf` (`check.py --init`). Fixed. |
| B3 (b) | `26761ac1`: `tests/front/tactics/decide/sy-vars.lf`, the review's 22 slice-runnable probes (p01-p09, p11-p14, p19, p31, p36-p40, p48, p50; binders `n m : Nat`, `h : False`; proof `by-exfalso by-assumption`), as `sv_ID`, their Lean twins in `goal-layer.lean`; pinned Lean regenerated the golden (114 new lines, none changed, all equal to the review's own Lean dumps). In plain-mode `FILES`. Plain mode now compares 62 theorems node for node with pinned Lean (22 before); its run went from about 32 s to about 45-55 s. Fixed. |
| B3 (c) | `26761ac1`: `make reference-decide-init` runs `check.py --init $(INIT_SNAPSHOT) $(INIT_ELAB)` (defaults: the main checkout's `.claude/work/parallel-init/init-1.lfsn` and `.claude/work/IM/init.elab.ndjson`, found by their own `git rev-parse --git-common-dir`), with `sy-vars-init.lf`: the review's 35 Init-only probes (p10, p15-p18, p20-p30, p32, p34, p35, p41-p47, p49, r1-r8) as `si_ID`. 116 theorems of 11 files accepted, each term node for node pinned Lean's, in 165 s through make (strict engine; 78 s with plain Gforth). Without the snapshot a user's run prints `check decide --init: SKIPPED, NOT RUN: no Init snapshot (INIT_SNAPSHOT=...)` and exits 0; a recorded run (`REQUIRE_INIT_SNAPSHOT=1`, set by `scripts/tested-tree.py` as `REQUIRE_MATHLIB`) fails; a snapshot not of this build's verdict version fails with "STALE SNAPSHOT, NOT A PASS". Part of `make daily` after `make parallel-init` (`DAILY_SUITES`, `daily_needs`), never of a tier; `scripts/test-classes.py` has a `daily` class checked against `DAILY_SUITES`. Unit tests: `tests/scripts/test_mathlib_slice.py` `NoInitSnapshot`, `tests/scripts/test_test_classes.py` `test_daily_rows`, `tests/scripts/test_tested_tree.py`. Faults `decide-init-recorded-run-skips`, `decide-init-stale-unseen`, `test-classes-daily-unchecked`. Fixed (done now, not a plan row). |
| L1 | `ccbe966a`: `name-table: lfn-notations`, `lfn-new-word` and `lfn-checked` peek through `lfn-peek`, `lfn-entry,` lays down the entry from `name-entry` with no private offset; `lfn-entry`'s comment states every word that runs it has an entry (L3's test checks all 22). Fault `rd-op-skips-row-check` re-pointed. The optional `lfn-const-node` is not done. **Open, the owner's decision:** with `name-table:` the table is now counted as reader.fs's one global, so `python3 scripts/check-forth-quality.py` fails with `src/front/reader.fs: globals 1 > 0`; the baseline (`tests/forth-quality-baseline.json`) is not raised here, the owner is being asked. |
| L2 | `ccbe966a`: front.fs pins the operand order of `>`, `≥`, `<`, `/`, `%` and `^` (which operand is the node's first and which its second); each registration refusal checks its abort message. Faults `rd-gt-operands-swapped`, `rd-ge-operands-swapped`. Fixed. |
| L3 | `ccbe966a`: front.fs asserts each of the 22 spellings of `lfa-natural-words` is in `lfn-notations`, and runs `∨` and `∣`; `26761ac1` brings `∨` into the tier's decide comparison too (`sy_or`, `sv_p12`). Fixed. |
| L4 | `26761ac1`: LANGUAGE_REFERENCE's "How to type each symbol" says the ASCII notation `<= >= /\ \/ <->` builds the same term, and that a typed constant name differs from the notation in two cases, as in Lean: `Ne` with sides of different number types (Lean converts for `≠`, refuses `Ne`; LeanForth refuses both, 131) and `Not` inside a namespace with its own `Not`. Fixed. |
| L5 | `ccbe966a`: tests/front/tactic-dump.fs prints `[ rightact% ... ]`. Fixed. |

Checks after the fixes (2026-11-20, `26761ac1`): `python3 tests/front/tactics/decide/check.py` and
`--lean` exit 0; `make reference-decide-init` exit 0; `make cover-changed BASE=main JOBS=3` exit 0 (every
block on a changed line ran); `python3 scripts/mutants.py --check` exit 0; `make check-test-classes
check-docs` exit 0. `scripts/pre-tier.sh` fails on one line only, "forth quality + review log", for the
open L1 baseline point above.

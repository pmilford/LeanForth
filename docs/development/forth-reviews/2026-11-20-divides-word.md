# Forth review: the word divides for Lean's Dvd.dvd (2026-11-20)

Branch `divides-word`, range **085536f2..8c49d364** (1 commit). Reviewed: `git show 8c49d364 -- src tests`
(src/front/reader.fs +11/-3, src/author/words.fs one word, tests/front/front.fs, three faults in
tests/mutants/faults.d/s3a-ops.toml); the user documentation of the commit was read for accuracy only. Worked on
`git archive 8c49d364` and `git archive 8c49d364^` extracted into a scratch folder; no worktree was edited.

**Findings: 0 high, 1 medium, 2 low. Blocking: M1 (validation) and L1 (tests).**
Terms agree: `a b divides`, `a b ∣` and `a b Dvd.dvd` elaborate to the identical term on Init, Nat and Int.

**Verdict: merge after fixes (M1, L1).**

## Findings

**M1 (medium, blocking: validation lost). `lfn-own-name:` will give any syntax word that is not in the table
the meaning "Dvd.dvd", silently replacing the meaning it already had (reader.fs:213-214).**
- Before this commit, every registration passed `lfn-spelt`. The row check meant that only a spelling from
  Lean's notation table could be registered, and those words have no other natural meaning. The tests record
  that guarantee as "`$` keeps its own".
- `lfn-own-name:` drops the row check. It still checks the seal, that the word is a syntax word, and that the
  word is not in the table yet. Nothing checks that the word has no natural meaning yet.
- Probe, after loading `src/load/checker.fs src/load/front.fs` on Gforth 1.0, showing the throw code and the
  table size:
  - `s" Dvd.dvd" lfn-own-name: $` gives 0 and 24: accepted, and `$` now means Dvd.dvd.
  - `... lfn-own-name: theorem` gives 0 and 25.
  - `... lfn-own-name: by-rfl` gives 0 and 26.
  - `... lfn-own-name: Nat` gives -2 and 26 (refused: not a syntax word).
- Only one line calls it, at load time, so no user input reaches it today. But it is the registration word meant
  for future words of LeanForth's own, and the guarantee it drops was one an earlier review asked for.
- Fix: refuse a word that already has a natural meaning. Put one word in author/groups.fs, which owns the
  syntax-word layout, and call it from reader.fs:

```forth
\ groups.fs: whether syntax word c-addr u has no natural meaning yet.
: lfa-natural-later? ( c-addr u -- flag )
  lf-words search-wordlist 0= abort" lfa-natural-later?: no such syntax word"
  >body cell+ @ ['] lfa-natural-later = ;
\ reader.fs
: lfn-unmeant ( "word" -- )
  lfn-peek lfa-natural-later? 0= abort" reader.fs: a word with a meaning of its own" ;
: lfn-own-name: ( c-addr u "word" -- )
  lfn-open lfn-syntax-word lfn-unmeant lfn-new-word 0 lfn-lay ['] lfn-w-named lfa-natural! ;
```

- Test:
  `T{ s\" s\" Dvd.dvd\" lfn-own-name: $" reg s" reader.fs: a word with a meaning of its own" says? entries -> -2 true 23 }T`.
- Fault `rd-own-name-meant`: drop `lfn-unmeant`.
- Optionally use the same check in `lfn-checked`, so the rule is stated rather than implied by the row check.

**L1 (low, blocking under the coverage classes: tests 3, 4, 7 and 8). No end-to-end or pinned-Lean test of
`divides`, and no kernel-form test.**
- The unit test environment of front.fs has no `Dvd.dvd`. So `n n n divides` gives error 38 there (unknown
  constant, errors.fs:94). That only shows the word looks up a constant by name. It is not "the same answers as
  ∣" in any sense that shows the term.
- The two table tests (constant `Dvd.dvd`, kind 0) do pin the entry.
- That the term is identical to ∣ and to Lean was shown only by this review's probe (below).
- Fix 1: add twins of `si_p10` (`n m divides`) and `si_p42` (`i j divides`) to
  tests/front/tactics/decide/sy-vars-init.lf, checked by `check.py --init` against the same Lean statements as
  the ∣ ones.
- Fix 2: add a kernel-form pin to front.fs:
  `T{ s" kernel-form theorem t Prop explicit: p p p divides := p end t" nfails -> 58 1 44 }T`.
  The probe gives exactly `58 1 44`.

**L2 (low, style). `lfn-lay` takes the word as two cells, which the callers get from `lfn-new-word`, even though
the word is still waiting in the input. This adds a `>r`/`r>` pair: return-stack operations in reader.fs go from
14 to 16 (the baseline is 18, so the ratchet passes).**
- Better: let `lfn-lay` peek the word itself, and let `lfn-new-word` only check. The word in the input then stays
  the single source, and no `>r` is needed in `lfn-lay`:

```forth
: lfn-new-word ( "word" -- )
  lfn-peek lfn-notations name-table-find abort" reader.fs: a notation word twice" ;
: lfn-checked ( c-addr u "word" -- c-addr u ) lfn-spelt lfn-syntax-word lfn-new-word ;
: lfn-lay ( c-addr u kind "word" -- ) lfn-peek lfn-notations name-entry , counted, ;
: lfn-entry, ( c-addr u kind "word" -- ) lfn-open >r lfn-checked r> lfn-lay ;
```

- With this change, the `new` text of fault `rd-own-name-twice` would become a removal of `lfn-new-word`.
- Not blocking.

## Checks asked for, with evidence

1. **Same term as ∣, as Dvd.dvd, and as Lean.** I ran the term dump on gforth-fast with Init's snapshot
   init-1.lfsn and init.elab.ndjson, over 12 statements. Each statement had binders `Nat n m`, `Int i j` and
   `False h`, and was proved by `by-exfalso by-assumption`. Exit code 0.
   - These pairs are identical, compared on each dumped type line:
     - `n m divides`, `n m ∣` and `n m Dvd.dvd`;
     - `i j divides`, `i j ∣` and `i j Dvd.dvd`;
     - `¬ (n divides m ∧ m ∣ n)` and the same with ∣ in both places;
     - `3 12 divides` and `3 12 ∣`;
     - `n 2 + m divides` and `n 2 + m ∣`.
   - Operand order: `(app (app (app (app Dvd.dvd.{0} Nat) Nat.instDvd) #4) #3)` for `n m`, so `a b divides` is
     `Dvd.dvd a b`. With Int it is `Int.instDvd ... #2 #1`.
   - The ∣ forms are already compared with pinned Lean (`si_p10`, `si_p42`), so `divides` matches Lean by
     equality with them. I did not run pinned Lean myself.
2. **`lfn-lay` and `lfn-entry,`.**
   - The stack effects are right: `name-entry ( c-addr u table -- )` lays the word, then `,` lays the kind, then
     `counted,` lays the constant.
   - I dumped the table (word, kind, constant) through `name-table-each` in the parent tree and in this one. The
     22 older entries are identical and in the same order. Only `divides 0 Dvd.dvd` is added.
3. **`lfn-own-name:`.**
   - It is sealed: the test at front.fs:940 passes, and fault `rd-own-name-unsealed` is caught.
   - A word that is no syntax word (`zz`) and a second registration (`divides`) are refused with their own
     messages. The table keeps 23 entries, and `lfa-natural!` is never reached, so a refusal leaves nothing behind.
   - Skipping the row check is sound for the constant, which the tests and fault pin to `Dvd.dvd`. It loses the
     guarantee that the word had no other meaning (M1).
   - Printer: the Forth-form printer (print-forth.fs, statement-forms.fs) writes constants by their full names
     and never uses notation words. So `Dvd.dvd` prints as `Dvd.dvd` with its arguments, and the round trip is
     unchanged.
   - `divides` is now reserved, through `lfa-natural-words` and `lf-pf-reserve-more`. A bare constant named
     `divides` prints with `root:`, a variable named `divides` prints as `var#`, and a declaration named bare
     `divides` prints the reason line.
   - Lean-form goals print `∣`, as Lean does (seen in the dump: `⊢ n + 2 ∣ m`).
   - Init has no bare `divides` name. A grep of IM/init.ndjson finds only `cdiv_eq_div_of_divides`. In
     IM/mathlib.ndjson, `"divides"` occurs only as the last part of dotted names, which this does not affect.
   - No test or .lf file outside front.fs uses `divides`.
   - A binder named `divides` is accepted, and each use then runs the word. Probe: `Nat explicit: divides divides
     divides ∣` gives 38 at the second `divides`. `∣` behaves exactly the same, so this is not new. The message
     at the use does not mention the binder.
4. **Kernel form.** `p p p divides` gives `58 1 44`, the same as `∣` (probe). There is no test for it (L1).
   Also, the bar key `n 3 12 |` gives `81 1 32`, as LANGUAGE_REFERENCE.md says.
5. **Faults.** I planted each fault in the scratch tree and ran Gforth 1.0 on tests/front/front.fs. Each one fails
   on an `INCORRECT RESULT` assertion:
   - `rd-divides-other-constant`: caught by the `lfn-entry-const` test.
   - `rd-own-name-unsealed`: caught by the sealed `zzz` test.
   - `rd-own-name-twice`: caught by the twice test.
   - Mine, all caught:
     - no syntax-word check (caught by the `zz` test);
     - `lfn-w-operator` in place of `lfn-w-named` (caught by `n n n divides`);
     - kind 6 in place of 0 (caught by the kind test);
     - `lfn-entry,` without the row check (caught by the `Foo.bar` test);
     - `divides` dropped from `lfa-natural-words` (the load aborts, "not a syntax word").
   - A swap of the operands for `divides` alone cannot happen. `divides` has no code of its own: its entry holds
     only a kind and a constant name, and it applies its arguments through `lfn-w-named`, shared with ∣, ¬, ∧, ∨
     and ↔. Operand order is covered by the ∣ comparisons on Init and by probe 1.
6. **Reuse and re-entrancy.** See the sections below.

## Reuse

- The new words use the existing library words: `name-table` and `name-entry` (lib/name-table.fs), `counted,`
  (lib/bytes.fs:245), `lfa-has-word?` (author/runner.fs:140) and `lfa-natural!` (author/groups.fs:183).
- `lfn-lay` is specific to this module: it writes the notation table. `lfn-own-name:` is a registration variant
  that shares every check word with `lfn-entry,`.
- The fix for M1 puts its question in groups.fs, which owns the syntax-word body. reader.fs should not read the
  layout with `>body cell+` itself.
- I grepped src/ for the names and shapes of `lfn-lay`, `lfn-own-name:`, `counted,` and `lfa-has-word?`. No copy
  was found.
- `scripts/check-duplicates.py`: "187 baseline groups, each with a reason, none new or grown".
- `scripts/check-lib-callers.py`: "every src/lib/ file is used outside lib/ or listed with a plan row" (bigint.fs
  is allowed by plan FE1i-4).

## Re-entrancy

- No new global.
- The one write, of `lfn-notations` and the natural meaning of `divides`, happens at load time.
- `lfn-own-name:` calls `lfn-open` first, which aborts once `context-sealed?` is true. Runs and workers read the
  table in place.

## Forth style

`python3 scripts/forth-metrics.py --words 10 src/front/reader.fs`, at the commit:

- 72 words. 63 (87%) are one or two lines long, 9 (12%) are three to five lines, and none is longer.
- Every word has a stack comment.
- 1 global (the table, NAME-TABLE) and 1 context member. No locals.
- 4 deep shuffles, 16 return-stack operations, no line over 90 characters.

At the parent there were 70 words and 14 return-stack operations. The baseline for reader.fs is rstack 18,
shuffles 6, globals 1, long words 0, so the ratchet holds.

The two new words are one line each. Their stack comments are right, and a comment says why the row check is
skipped. The style point is L2. The kind `0` ("a notation name") is a literal in both `lfn-notation-name:` and
`lfn-own-name:`. That predates this commit, and a named constant would read better.

## What was run and what was not

What was run:
- Gforth 1.0.0, tests/front/front.fs on the commit's tree: "all tests passed".
- My probes: the table dump of both trees, `lfn-own-name:` on `$`, `theorem`, `by-rfl` and `Nat`, kernel form,
  binder names, the bar key, and `'`.
- 3 + 5 planted faults.
- gforth-fast with Init's snapshot for the term dump.
- forth-metrics, check-duplicates and check-lib-callers.

What was not run:
- make, any suite, gforth-fast on front.fs, and Gforth 0.7.3.
- Pinned Lean and check.py. Lean agreement is inferred from the identity with the ∣ forms that are already compared.
- A binder named `divides` on Init.

AI review does not replace the human review the project requires. This change touches front-end reading
(parser semantics: what a word of theorem text means), and the owner decided it on 2026-11-20.

## Fixes (2026-11-20, commit ede27b68)

| Finding | Fix | Test / fault |
| --- | --- | --- |
| M1 | `lfa-natural-later?` (`src/author/groups.fs`) and `lfn-unmeant` (`src/front/reader.fs`): `lfn-own-name:` refuses a syntax word that already has a natural meaning, before anything is written | `tests/front/front.fs`: `lfn-own-name: $` aborts with "a word with a meaning of its own", the table keeps 23 entries and `$` its meaning; fault `rd-own-name-meant` |
| L1 | `si_d10` (`n m divides`) and `si_d42` (`i j divides`) in `tests/front/tactics/decide/sy-vars-init.lf` with their Lean twins in `tests/front/tactics/goal-layer.lean`: `check.py --init` (the daily target `reference-decide-init`) compares them node for node with pinned Lean's terms, 118 theorems in all; the kernel-form test (58) in `tests/front/front.fs` | the golden's four new lines are pinned Lean's |
| L2 | not changed (style; the ratchet holds): plan 9.4.8l (BE) | - |

`rd-own-name-twice` became `rd-own-name-meant`: a word already in the table always has its meaning, so the twice
check of `lfn-own-name:` is now reached only behind the meaning check. All three faults of the word are caught by
assertions of `tests/front/front.fs`.


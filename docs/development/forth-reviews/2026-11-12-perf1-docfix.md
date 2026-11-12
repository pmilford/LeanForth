# Forth review of the performance pass and the docs fixes (2026-11-12)

Reviewer: forth-reviewer (Opus), read-only. Ranges: (1) `c19a2f5..bf5cb68` (perf1, merged in 3ac0558): 1 medium,
8 low, 1 info; (2) `41c6d8e..66da748` (docfix): 1 medium, 1 low. The correctness findings of review rvPF1 are left
to branch pf1-fix. Runs: forth-metrics; mutants with the reviewer's own fault lists on exported trees of bf5cb68 and
pf1-fix; the proposed tests in a scratch copy; the SYNONYM snippet on Gforth 0.7.3 and 1.0.0. Saved by the
coordinator, condensed.

## perf1
1. MEDIUM test gap (class 5, no fault): level-scope.fs:110, the path where `lf-lscope-pass` is refused heap room never
   runs; fault `ok? 0= if drop exit then` -> `drop` (copy written past its block) survives. Proposed test: a 1-cell
   `lf-lscope-audited` slab, two context entries, valid with `passed` 0; then restore the slab.
2. LOW test gap (class 7): binder-table.fs, the slab grows only in `lf-pres-claim`, never on a read: not pinned
   (fault `over lf-pres-hold drop` in `lf-pres-current` survives); proposed capacity assertions.
3. LOW faults not planted (caught by existing tests): `lf-check-reached?` memo-off `drop false`; failed audit kept /
   copy never refreshed (level-scope.fs:111, 115); `lf-term-same` ignoring the key (terms.fs:538); a
   `u32-native ... [if]` -> `false [if]` fault marked "performance only".
4. LOW docs: constant-term-boundary.fs:368-372 leftover comment for removed `lf-audit-reached?`; :358 wrong about
   `lf-audit-held?`; check-declaration.fs:312 names the removed word.
5. LOW factoring: check-declaration.fs:322-334 level and reference hooks still ask `lf-audit-on?` twice; one shape as
   for terms.
6. LOW style: level-scope.fs:103-112 repeats `lf-lscope-state lf-lsctx-passed`; `lf-lscope-pass` does four jobs and
   exits mid-word: `lf-lscope-passed`, `lf-lscope-keep`.
7. LOW portability: the SYNONYM fallback in u32.fs:78-87 belongs in portability.fs
   (`[undefined] synonym [if] : synonym ( "new" "old" -- ) : ' compile, postpone ; ; [then]`, ordinary words only).
8. LOW style: terms.fs:535-538 mid-word exit and `>r`/`r>` round trip (`lf-term-equal?`, `lf-term-given?`);
   binder-table.fs:66 `slab-at` instead of `column-at`; 89-95 repeated guard -> `lf-pres-held`.
9. INFO: level-scope.fs:107 COMPAREs cell bytes; harmless (only `0=` used); say so.
Metrics: 6 files, 518 words (+10, all new words 5 lines or fewer); globals, deep shuffles, return-stack operations and
long lines unchanged.

## docfix
10. MEDIUM trust labelling: leanforth.fs:1082-1084 `cli-mathlib.` prints an unqualified "accepted": add
    "experimental and not independently audited", the one NOT PROVED (sorryAx, as in Lean) and the build.
11. LOW test: tests/cli/test_leanforth.py:964-976 should also assert the label, NOT PROVED and the settings.
Metrics: leanforth.fs 347 -> 348 words; long lines unchanged (11).

\ Test driver: an export checked both ways at the tier level (plan step
\ SN2, ADR 0020): as staged, and as loaded from its saved input tier
\ (src/import/snapshot-tier.fs), each run printing one line per
\ declaration, "d <number> <outcome> <fuel used>", for a diff; and the
\ saved tier loaded, sealed and saved again, timed. Used once on all of
\ Lean's Init with gforth-fast (too slow for make check; the unit tests
\ in tests/core/snapshot-tier.fs do the same on the small exports).
\ Test-only; nothing here accepts a theorem. Usage, from the project root:
\   gforth-fast tests/support/tier-both-ways.fs -e \
\     's" init.tier" s" init.ndjson" 3 tbw-fresh bye'    > fresh.out
\   gforth-fast tests/support/tier-both-ways.fs -e \
\     's" init.tier" s" again.tier" tbw-resave bye'        (load, seal, save)
\   gforth-fast tests/support/tier-both-ways.fs -e \
\     's" init.tier" 3 tbw-loaded bye'                   > loaded.out
\ The number is the jobs of the check (cli/check-run.fs ck-jobs!); the
\ fuel is the CLI's default. The export is read with its manifest.

require ../../src/load/checker.fs
require ../../src/cli/check-run.fs
decimal

create tbw-tf /tier-file allot  tbw-tf tier-file-init
create tbw-stage /stage allot  tbw-stage /stage erase
100000000 constant tbw-fuel
: tbw-now ( -- us ) utime drop ;
: tbw-ms ( us -- ) 500 + 1000 / 0 .r ." ms" cr ;
\ Stop with the step's name when an outcome is not ok.
: tbw-must ( outcome c-addr u -- )
  rot dup ok? if drop 2drop exit then ." error: " -rot type space . cr
  tbw-tf tier-file-error ." at " . ." in " type cr 1 (bye) ;
: tbw-results ( -- )
  ck-verdicts? 0= abort" no verdicts" lf-input-count 0 ?do
    ." d " i 0 .r space i lf-env-outcome 0 .r space i ck-fuel-of 0 .r cr
  loop ;
\ The checker's stage loaded from a tier file and sealed, then fed, as
\ ck-load stages and feeds an export.
: tbw-staged ( c-addr u -- outcome )
  12 ck-stage stage-init s" init" tbw-must ck-stage tbw-tf tier-load
  dup ok? if drop ck-stage stage-seal then ;
: tbw-load ( c-addr u -- outcome )
  tbw-staged dup ok? if drop ck-stage-facts ck-feed-phase dup ok? if ck-input-facts then then
  dup ck-state ck-loaded ! ;
\ The export staged and fed, its tier saved to the file t (timed), then
\ every declaration checked.
: tbw-fresh ( t-addr t-u e-addr e-u jobs -- )
  tbw-fuel ck-start ck-jobs! true ck-load s" stage and feed" tbw-must
  tbw-now >r ck-stage tbw-tf tier-save s" save" tbw-must
  ." tier saved in " tbw-now r> - tbw-ms ck-check tbw-results ck-release ;
\ The tier file t loaded into the checker's stage, then every declaration
\ checked.
: tbw-loaded ( t-addr t-u jobs -- )
  tbw-fuel ck-start ck-jobs! tbw-load s" load and feed" tbw-must
  ck-check tbw-results ck-release ;
\ The tier file t1 loaded, sealed and saved as t2, each step timed.
: tbw-into ( t1-addr t1-u -- outcome ) tbw-stage tbw-tf tier-load ;
: tbw-seal ( -- outcome ) tbw-stage stage-seal ;
: tbw-resave ( t1-addr t1-u t2-addr t2-u -- )
  16 tbw-stage stage-init s" init" tbw-must 2swap
  tbw-now >r tbw-into s" load" tbw-must ." loaded in " tbw-now r> - tbw-ms
  tbw-now >r tbw-seal s" seal" tbw-must ." sealed in " tbw-now r> - tbw-ms
  tbw-now >r tbw-stage tbw-tf tier-save s" save" tbw-must
  ." saved in " tbw-now r> - tbw-ms tbw-stage stage-free ;

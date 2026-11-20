\ Test driver for the feed path of the first checker's Lean differentials
\ (the *-fed tables of tests/core/lean-differential.py; plan task 3.2.2).
\ Test-only.
\
\ Each case comes as a lean4export export written by
\ tests/support/case_export.py from the same case text that
\ first-checker-driver.fs reads. A line
\   fd-case <id> <path>
\ stages the export (src/import/stage.fs), unchecked as it has no
\ manifest, and feeds it to this context in file order
\ (src/import/feed.fs): the names stay in the stage's input tier, the
\ stores grow to the feed's capacities, and the level context is every
\ parameter the export's levels name. Then it checks every declaration
\ with check-declaration through the checked environment's serial
\ publisher, prints the case's ROW and VERDICT lines and checks every slot
\ exactly as first-checker-driver.fs does (its words are used here), and
\ detaches the names and frees the stage.
\
\ The stage refuses an export that names a constant no declaration of it
\ has (a real export is closed): such a case prints
\   REFUSED <id> <the stage's reason>
\ and the row of an invalid check, which the harness allows only for the
\ cases it lists. Nothing here accepts a theorem; it observes the kernel
\ code under test.

require ./first-checker-driver.fs
require ../../src/load/import.fs   \ the stage and the feed

create fd-stage /stage allot
create fd-feed /feed allot
: fd-checked ( -- )
  fd-stage fd-feed lf-feed ok? must 64 lf-env-new ok? must dup lf-env-use ok? must
  fc-check-all fc-report lf-env-free ok? must lf-name-detach ;
: fd-refused ( -- )
  ." REFUSED " fc-.id fd-stage stage-error type 2drop drop cr
  ." ROW " fc-.id ." invalid 0 0 0 0" cr ." VERDICT " fc-.id ." invalid" cr ;
: fd-case ( "id" "path" -- )
  fc-token dup fc-id# ! fc-id swap move 16 fd-stage stage-init ok? must
  fc-token fd-stage stage-load-unchecked ok? if fd-checked else fd-refused then
  fd-stage stage-free ;

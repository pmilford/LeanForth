\ The proof outline on inductive blocks fed from an export (plan task
\ 5.2.1a; review rvI21 R4-5, R4-6), which the command line cannot reach
\ yet (its reader refuses inductive types), so a test reaches it here:
\ - an empty block's declaration (lf-kind-block, ADR 0016 amendment 1) has
\   no type: the outline's statement line reads none and prints "none";
\ - a use of the recursor a block generated (ADR 0015 decision 12): the
\   log's resolve step for IE.B.rec names no slot (never IE.B's), and the
\   outline says the kernel generated it.
\ Each outline is printed, and the run must not throw. Test-only.
include ../support/tester.fs
include ../support/checks.fs
require ../../src/cli/print.fs
require ../../src/import/feed.fs

create stg /stage allot
create fdd /feed allot
variable env
: must ( flag -- ) 0= abort" outline-block: refused" ;
: staged ( c-addr u -- )
  16 stg stage-init ok? must stg stage-load-unchecked ok? must stg fdd lf-feed ok? must ;
: unstage ( -- ) lf-name-viewed? if lf-name-detach then stg stage-free ;
: fresh ( -- )
  1000000 lf-check-budget 64 lf-env-new ok? must dup env ! lf-env-use ok? must ;
: finish ( -- ) env @ lf-env-free ok? must unstage ;
: checked ( d -- outcome )
  ['] lf-check-declaration swap lf-env-step drop lf-env-view drop ;
pr-log-on

\ The empty block: rejected, and its outline prints without reading a type.
s" tests/core/check-block-cases/names.empty-block.ndjson" staged fresh
T{ 0 checked 0 lf-env-outcome -> outcome-rejected outcome-rejected }T
T{ outcome-rejected 0 false ' lf-outline catch -> 0 }T
finish

\ IE.B.useRec := @IE.B.rec.{u}, IE.B.rec left out: every resolve step
\ that names a slot names a declaration of the name it resolved, and one
\ resolves IE.B.rec to no slot (the generated recursor).
s" tests/core/check-block-cases/after.recursor-left-out-then-use-rec.ndjson" staged fresh
T{ 0 checked 3 checked -> outcome-ok outcome-ok }T
: resolve? ( s -- flag ) lf-log-rule@ lf-rule-resolve = ;
: named-right? ( s -- flag )
  dup lf-log-out@ dup 0< if 2drop true exit then lf-input-name swap lf-log-a@ lf-name-same? ;
: generated? ( s -- flag ) dup lf-log-out@ 0< swap lf-log-outcome@ ok? and ;
: resolves ( -- right? generated? )
  true false lf-log-count 1+ 1 ?do i resolve? if
    i named-right? rot and swap i generated? or then
  loop ;
T{ resolves -> true true }T
T{ outcome-ok 0 false ' lf-outline catch -> 0 }T
finish

cases-done
bye

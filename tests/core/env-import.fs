\ Tests of the import pass and of layers at the Forth level (plan task
\ 6.2.5, step SN4; kernel/env-import.fs, kernel/env-layers.fs,
\ kernel/environment.fs lf-env-replay). Built with the I2 assertion
\ (lf-env-i2-checks, defined before loading):
\ - lf-env-replay asks nothing for a key no import replays: names beyond
\   the input, another module's test;
\ - the dependent fixture (tests/cli/dependent.ndjson) checked against a
\   snapshot of its base (inductive.ndjson): the base's six declarations
\   taken, every outcome and fuel as its fresh check's, and no check (the
\   taken slots' publications included) reads a slot that no recorded
\   query answered (lf-i2-misses 0);
\ - the same against the base and the dependent export's layer: all
\   taken, the same outcomes;
\ - dep-sort sorts little-endian slot numbers.
\ The command line's tests (tests/cli/test_leanforth.py, Imports and
\ Layers) cover both ways on every fixture, the refusals and the planted
\ faults. Test-only.

create lf-env-i2-checks   \ compiles the I2 assertion into environment.fs
require ../../src/main.fs
include ../support/tester.fs
decimal

: base-file ( -- c-addr u ) s" /tmp/leanforth-env-import-base.lfsnap" ;
: layer-file ( -- c-addr u ) s" /tmp/leanforth-env-import-layer.lfsnap" ;
: dependent ( -- c-addr u ) s" tests/cli/dependent.ndjson" ;
variable failures  0 failures !
: must ( flag c-addr u -- ) rot if 2drop else ." failed: " type cr 1 failures +! then ;

\ Keys no import replays.
T{ lf-look-outside lf-env-replay -> false }T
T{ 5 lf-look-other lf-look-key lf-env-replay -> false }T

\ The fresh check's outcomes and fuel, then the same export's through the
\ base's snapshot.
create fresh-outcomes 64 cells allot
create fresh-fuel 64 cells allot
: keep-fresh ( -- )
  lf-input-count 0 ?do
    i lf-env-outcome fresh-outcomes i cells + ! i ck-fuel-of fresh-fuel i cells + !
  loop ;
: same-as-fresh? ( -- flag )
  true lf-input-count 0 ?do
    i lf-env-outcome fresh-outcomes i cells + @ = and
    i ck-fuel-of fresh-fuel i cells + @ = and
  loop ;
: taken# ( -- n ) 0 lf-input-count 0 ?do i lf-env-origin lf-origin-saved = - loop ;

20000000 ck-start s" tests/cli/inductive.ndjson" true ck-load ok? s" base load" must ck-check
base-file s" {}" ck-snapshot-save ok? s" base save" must ck-release
20000000 ck-start dependent true ck-load ok? s" fresh load" must ck-check
ck-verdicts? s" fresh verdicts" must keep-fresh lf-input-count 13 = s" thirteen" must
ck-release

20000000 ck-start 0 0 ck-layers! base-file -1 ck-snapshot-import ok? s" import" must
0 lf-i2-misses ! dependent true ck-load ok? s" import load" must ck-check
T{ ck-outcome ck-taken# taken# ck-other# -> outcome-ok 6 6 0 }T
T{ ck-verdicts? same-as-fresh? lf-i2-misses @ -> true true 0 }T
layer-file s" {}" ck-snapshot-save ok? s" layer save" must ck-release

\ Base and layer: everything taken, as fresh.
create layers 2 cells allot  layer-file layers 2!
20000000 ck-start layers 1 ck-layers! base-file -1 ck-snapshot-import ok? s" layered" must
dependent true ck-load ok? s" layered load" must ck-check
T{ ck-outcome ck-taken# ck-layers# -> outcome-ok 13 1 }T
T{ ck-verdicts? same-as-fresh? -> true true }T
ck-release

\ Sorting slot numbers.
create nums 16 allot
: num! ( u k -- ) 4 * nums + u32-le! ;
: num@ ( k -- u ) 4 * nums + u32-le@ ;
9 0 num! 3 1 num! 7 2 num! 1 3 num!
nums 4 dep-sort
T{ 0 num@ 1 num@ 2 num@ 3 num@ -> 1 3 7 9 }T
nums 0 dep-sort

base-file delete-file drop  layer-file delete-file drop
T{ failures @ -> 0 }T
failures @ 0= [if] ." The import pass, its I2 build and layers hold." cr [then]
bye

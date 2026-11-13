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
\ - dep-sort sorts little-endian slot numbers;
\ - a taken slot whose saved lookups cannot all be asked again is
\   published invalid, never with the saved outcome (review FRK F3);
\ - out of room while a layer is entered is full, never invalid (review
\   FRI F1; heap refusals from tests/support/heap-watch.fs, loaded first).
\ The command line's tests (tests/cli/test_leanforth.py, Imports and
\ Layers) cover both ways on every fixture, the refusals and the planted
\ faults. Test-only.

include ../support/scratch.fs
include ../support/heap-watch.fs
create lf-env-i2-checks   \ compiles the I2 assertion into environment.fs
require ../../src/main.fs
include ../support/tester.fs
decimal

s" leanforth-env-import-base.lfsnap" scratch-file 2constant base-file
s" leanforth-env-import-layer.lfsnap" scratch-file 2constant layer-file
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

\ A taken slot whose saved lookups cannot all be asked again (review FRK
\ F3): imp-fill publishes it invalid and take refuses it, never with the
\ saved outcome. The base's first slot, its first saved lookup's key
\ forged to one no import replays (lf-env-replay false), then taken by
\ hand in the environment the import pass would run in.
: first-look ( -- addr ) ss-looks ck-snap snap-block 0 start@ nip 8 * + ;
20000000 ck-start 0 0 ck-layers! base-file -1 ck-snapshot-import ok? s" forge import" must
dependent true ck-load ok? s" forge load" must ck-facts drop ck-env drop
T{ first-look u32-le@ lf-env-replay -> true }T
lf-look-outside first-look u32-le!
: published ( d -- outcome ) lf-env lf-env-slot lf-slot-outcome @ ;
T{ 0 0 ck-import take 0 published -> outcome-invalid outcome-invalid }T
ck-release

\ Sorting slot numbers.
create nums 16 allot
: num! ( u k -- ) 4 * nums + u32-le! ;
: num@ ( k -- u ) 4 * nums + u32-le@ ;
9 0 num! 3 1 num! 7 2 num! 1 3 num!
nums 4 dep-sort
T{ 0 num@ 1 num@ 2 num@ 3 num@ -> 1 3 7 9 }T
nums 0 dep-sort

\ ---- Out of room while a layer is entered (review FRI F1): the layer of
\ inductive.ndjson (two blocks with their recursors, constants with
\ universe arguments) written over a snapshot of identity.ndjson. Every
\ heap allocation the layered import makes, refused in turn, gives full;
\ and with the stage's tuples trimmed and their next growth refused, a
\ constant's universe arguments, a recursor's rules, the expressions and
\ the recursor's declaration are full (they were invalid).
s" leanforth-env-import-base2.lfsnap" scratch-file 2constant base2-file
s" leanforth-env-import-layer2.lfsnap" scratch-file 2constant layer2-file
20000000 ck-start s" tests/reference/identity.ndjson" true ck-load ok? s" base2 load" must
ck-check base2-file s" {}" ck-snapshot-save ok? s" base2 save" must ck-release
20000000 ck-start 0 0 ck-layers! base2-file -1 ck-snapshot-import ok? s" import2" must
s" tests/cli/inductive.ndjson" true ck-load ok? s" import2 load" must ck-check
T{ ck-outcome ck-taken# -> outcome-ok 0 }T
layer2-file s" {}" ck-snapshot-save ok? s" layer2 save" must ck-release
create layers2 2 cells allot  layer2-file layers2 2!
: layered2 ( -- outcome ) 20000000 ck-start layers2 1 ck-layers! base2-file -1 ck-snapshot-import ;
T{ layered2 ck-release -> outcome-ok }T
\ The allocations a layered import makes (a refusal never reached), and
\ the k-th refused: its outcome, and whether the refusal was reached.
: allocations ( -- n )
  max-n heap-refusals ! layered2 drop max-n heap-refusals @ - 0 heap-refusals ! ck-release ;
: refusing ( k -- outcome reached? )
  heap-refusals ! layered2 heap-refusals @ 0= 0 heap-refusals ! ck-release ;
: all-full? ( -- flag )
  true allocations 1+ 1 ?do i refusing swap outcome-full = and and loop ;
T{ allocations 50 > all-full? -> true true }T
\ The base and the layer's sections read by hand, as ck-snapshot-import
\ and env-layers.fs lay-open and ly-load do, up to the expressions.
: ly ( -- ly ) ck-lay lay-ly ;
: base2-read ( -- )
  20000000 ck-start base2-file -1 ck-snap snap-open drop ck-snap-read drop ck-firsts!
  ck-stage-slots ck-snap snap-read drop ;
: layer2-open ( -- )
  ck-stage ck-snap ck-snap snap-n @ ck-stage stage-tier tier-names cons-numbers ck-firsts
  ck-lay lay-init layer2-file ck-snap snap-fuel ck-lay lay-base @ snap-sum
  ck-lay lay-firsts @ ck-lay lay-snap snap-layer-open drop
  ck-lay lay-snap snap-tf tf-start drop ck-lay lay-ly-start ly ly-sections drop ;
: ly-early ( -- )
  lp-names ['] ly-name-step ly ly-family drop lp-levels ['] ly-level-step ly ly-family drop
  lp-texts ['] ly-text-step ly ly-family drop ly ly-starts drop ;
: layer2-ready ( -- ) base2-read layer2-open ly-early ;
: layer2-done ( -- ) ck-lay lay-free ck-release ;
\ The tuples' slab at its count, its next growth refused.
: tuples-refused ( -- ) ly ly-tier tier-tuples cons-records slab-trim drop 1 heap-refusals ! ;
: own-list? ( t -- flag ) lp-lists ly ly-first u< 0= ;
: expr@ ( j -- addr ) lp-exprs ly ly-rec ;
: own-const? ( j -- flag )
  expr@ dup ly-head drop tag-const = if quad-b u32@ own-list? else drop false then ;
: first-const ( -- j|-1 )
  lp-exprs ly ly-units 0 ?do i own-const? if i unloop exit then loop -1 ;
: const-operands ( j -- a b ) expr@ dup quad-a u32@ swap quad-b u32@ ;
: recursor ( -- i|-1 )
  ly ly-decls# 0 ?do i ly ly-decl ly-kind kind-recursor = if i unloop exit then loop -1 ;
: rules-of ( i -- t ) ly ly-decl staged-more u32@ 5 swap ly ly-at drop ;
layer2-ready
T{ first-const 0< recursor 0< -> false false }T
T{ first-const const-operands tuples-refused ly ly-const nip nip -> outcome-full }T
T{ first-const const-operands ly ly-const nip nip -> outcome-ok }T
T{ ly ly-exprs -> outcome-ok }T
T{ recursor rules-of own-list? -> true }T
T{ recursor rules-of tuples-refused ly ly-rules -> -1 outcome-full }T
T{ recursor rules-of ly ly-rules nip -> outcome-ok }T
T{ recursor ly ly-decl tuples-refused ly ly-xlate-decl -> outcome-full }T
layer2-done
layer2-ready
T{ tuples-refused ly ly-exprs -> outcome-full }T
layer2-done
T{ heap-refusals @ -> 0 }T
T{ depth -> 0 }T
base2-file delete-file drop  layer2-file delete-file drop

base-file delete-file drop  layer-file delete-file drop
T{ failures @ -> 0 }T
failures @ 0= [if] ." The import pass, its I2 build and layers hold." cr [then]
bye

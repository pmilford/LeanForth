\ Unit tests of src/lib/bigint.fs (plan step FE1i-4), outside the checker:
\ the representation and its check, every word on signs and zero, Lean's
\ documented examples of /, % and bmod (Init/Data/Int/DivMod/Basic.lean),
\ carries across limbs at 2^64, huge values, the most negative cell,
\ decimal text and every kind of malformed text; malformed, released and
\ straddling operands and a corrupted arena (invalid, nothing made); the
\ arena's bit limit; every room from 0 cells up between guard cells (each
\ result right, or full with nothing made and nothing written outside);
\ no heap use at all (tests/support/heap-watch.fs refuses allocations);
\ both stacks balanced; operands unchanged by every operation. Random pairs
\ against a model of Lean's definitions and against pinned Lean are in
\ tests/lib/bigint_differential.py. Expected values are decimal text, so
\ they hold whatever the cell size. Loaded under HEX: the library must not
\ depend on BASE.
include ../support/tester.fs
include ../support/checks.fs
include ../support/heap-watch.fs
hex require ../../src/lib/bigint.fs base @ decimal constant base-after-load

T{ base-after-load -> 16 }T

\ A 4 MiB arena for most tests: the only heap block the test holds.
create ar /big-arena allot
4194304 constant ar-bytes
ar-bytes allocate throw ar-bytes ar big-arena-init
T{ live-blocks @ -> 1 }T

: top ( -- addr ) ar big-mark ;
: int ( c-addr u -- i ) ar decimal>bigint outcome-ok <> abort" test integer" ;
: nat ( c-addr u -- big ) ar decimal>big outcome-ok <> abort" test number" ;
: text ( i -- c-addr u ) ar bigint>decimal outcome-ok <> abort" test print" ;
: nat-text ( big -- c-addr u ) ar big>decimal outcome-ok <> abort" test print" ;
\ Whether an operation gave ok and the well-formed integer (natural
\ number) whose text is c-addr u.
: gives? ( i outcome c-addr u -- flag )
  2swap outcome-ok = if dup bigint-valid? >r text compare 0= r> and else drop 2drop false then ;
: nat-gives? ( big outcome c-addr u -- flag )
  2swap outcome-ok = if dup big-valid? >r nat-text compare 0= r> and else drop 2drop false then ;
\ "A B R": the operation xt ( a b arena -- c outcome ) on the integers A
\ and B gives R.
: space-index ( c-addr u -- n )
  tuck 0 ?do dup i + c@ bl = if 2drop i unloop exit then loop drop ;
: token ( c-addr u -- rest-addr rest-u tok-addr tok-u )
  2dup space-index >r over r@ 2swap r> /string dup if 1 /string then 2swap ;
: row? ( c-addr u xt -- flag ) >r token int >r token int r> swap ar r> execute 2swap gives? ;
: nat-row? ( c-addr u xt -- flag )
  >r token int >r token int r> swap ar r> execute 2swap nat-gives? ;
\ bmod and ^ with B's magnitude as the natural number m or e.
: bmod-by ( x b arena -- c outcome ) >r bigint-magnitude r> bigint-bmod ;
: pow-by ( a b arena -- c outcome ) >r bigint-magnitude r> bigint-pow ;
\ The operation on two integers, then its result against a text.
: op-gives? ( a b xt c-addr u -- flag ) 2>r >r ar r> execute 2r> gives? ;

\ ---- Representation ----

\ A sign cell, -1, 0 or 1, then a bignum: 0 is sign 0 and no limbs.
T{ s" 0" int dup bigint-sign swap bigint-magnitude @ -> 0 0 }T
T{ s" -5" int dup @ over cell+ @ rot 2 cells + @ -> -1 1 5 }T
T{ s" 5" int dup bigint-sign swap bigint-magnitude dup @ swap big-limbs @ -> 1 1 5 }T
T{ s" -0" int bigint-sign s" -000" int bigint-sign s" 000" int bigint-sign -> 0 0 0 }T
T{ s" -7" int bigint-sign s" 0" int bigint-sign s" 7" int bigint-sign -> -1 0 1 }T
\ A result is made at the arena's top, with nothing left above it.
: at-top? ( a b xt -- flag )
  top >r >r ar r> execute drop dup r> = swap bigint-magnitude big-end top = and ;
T{ s" -7" int s" 3" int ' bigint-ediv at-top? -> true }T
T{ s" -7" int s" 3" int ' bigint-emod at-top? -> true }T
T{ s" -12" int s" 7" int ' bmod-by at-top? -> true }T
T{ s" -340282366920938463463374607431768211457" int s" 18446744073709551616" int
   ' bigint* at-top? -> true }T
\ Natural-number results too take the build's place.
: nat-at-top? ( a b xt -- flag ) top >r >r ar r> execute drop dup r> = swap big-end top = and ;
T{ s" -12" int s" 18" int ' bigint-gcd nat-at-top? -> true }T

\ ---- Well-formedness ----

create bad-sign 2 , 1 , 5 ,          \ sign 2
create unsigned-five 0 , 1 , 5 ,     \ sign 0, magnitude 5
create signed-zero 1 , 0 ,           \ sign 1, magnitude 0
create zero-limb 1 , 2 , 5 , 0 ,     \ a zero top limb
create minus-count -1 , -1 ,         \ a negative count
create five 1 , 1 , 5 ,              \ +5, in the dictionary: well formed, and live
T{ bad-sign bigint-valid? unsigned-five bigint-valid? signed-zero bigint-valid? -> false false false }T
T{ zero-limb bigint-valid? minus-count bigint-valid? five bigint-valid? -> false false true }T
T{ five five ar bigint+ s" 10" gives? five ar bigint-negate s" -5" gives? -> true true }T

\ Every operation refuses a malformed operand in either place: -1, invalid,
\ and the arena's top where it was.
: refused? ( i*x xt -- flag ) top >r >r ar r> execute -1 outcome-invalid d= top r> = and ;
\ The first n of these operations; bmod-by and pow-by read only b's
\ magnitude, so they count for a malformed a only.
create int-ops ' bigint+ , ' bigint- , ' bigint* , ' bigint-ediv , ' bigint-emod , ' bigint-gcd ,
  ' bmod-by , ' pow-by ,
: all-refused? ( a b n -- flag )
  >r true -rot r> 0 ?do 2dup int-ops i cells + @ refused? >r rot r> and -rot loop 2drop ;
: one-refused? ( i -- flag )
  dup ['] bigint-negate refused? over ['] bigint-natAbs refused? and
  swap ['] bigint-toNat refused? and ;
\ one is a good operand made before i, so that making it cannot overwrite
\ a released i.
: bad-int? ( one i -- flag )
  2dup 6 all-refused? >r 2dup swap 8 all-refused? >r nip one-refused? r> r> and and ;
: one ( -- i ) s" 1" int ;
T{ one bad-sign bad-int? one unsigned-five bad-int? one signed-zero bad-int? -> true true true }T
T{ one zero-limb bad-int? one minus-count bad-int? -> true true }T
T{ bad-sign ar bigint>decimal -> 0 0 outcome-invalid }T
\ Malformed natural numbers for bmod, ^ and nat>bigint.
create nat-zero-limb 2 , 5 , 0 ,
create nat-minus -1 ,
: bad-nat? ( big -- flag )
  s" 7" int over ['] bigint-bmod refused? s" 7" int 2 pick ['] bigint-pow refused? and
  swap ['] nat>bigint refused? and ;
T{ nat-zero-limb bad-nat? nat-minus bad-nat? -> true true }T

\ Released operands: wholly (stale) or in part (straddling the top). They
\ are well formed but reach into the arena's free part, which the result
\ would overwrite.
: big-text ( -- c-addr u ) s" -340282366920938463463374607431768211455" ;
: stale ( -- i ) top big-text int swap ar big-release drop ;
: straddling ( -- i ) top big-text int nip dup 3 cells + ar big-release drop ;
T{ stale dup bigint-valid? swap bigint-magnitude ar big-live? -> true false }T
T{ one stale bad-int? one straddling bad-int? -> true true }T
: stale-printed? ( i -- flag )
  top >r ar bigint>decimal outcome-invalid = -rot 0 0 d= and top r> = and ;
T{ stale stale-printed? straddling stale-printed? -> true true }T

\ A corrupted arena record: its top beyond its end. Every word refuses it.
create ar2 /big-arena allot
: corrupt ( x field -- ) ar ar2 /big-arena move ar2 + ! ;
ar arena-end @ cell+ 0 arena-top corrupt
T{ s" 1" int s" 2" int ar2 bigint+ -> -1 outcome-invalid }T
T{ s" -1" int s" 2" int ar2 bigint-ediv -> -1 outcome-invalid }T
T{ s" -1" int s" 2" nat ar2 bigint-bmod -> -1 outcome-invalid }T
T{ s" -1" int ar2 bigint-negate s" -1" int ar2 bigint-natAbs -> -1 outcome-invalid -1 outcome-invalid }T
T{ 5 ar2 n>bigint s" 5" ar2 decimal>bigint -> -1 outcome-invalid -1 outcome-invalid }T
T{ s" 5" nat ar2 nat>bigint s" -5" int ar2 bigint>decimal -> -1 outcome-invalid 0 0 outcome-invalid }T

\ ---- Signs and zero ----

\ A zero result has sign 0 (gives? checks bigint-valid?, which refuses a
\ signed zero).
T{ s" 0 0 0" ' bigint+ row? s" 5 -5 0" ' bigint+ row? s" -5 5 0" ' bigint+ row? -> true true true }T
T{ s" 5 5 0" ' bigint- row? s" -5 -5 0" ' bigint- row? s" 0 0 0" ' bigint- row? -> true true true }T
T{ s" 0 -7 0" ' bigint* row? s" -7 0 0" ' bigint* row? s" -3 -4 12" ' bigint* row? -> true true true }T
T{ s" 3 -4 -12" ' bigint* row? s" -3 4 -12" ' bigint* row? -> true true }T
T{ s" 0 -5 0" ' bigint-ediv row? s" -7 7 -1" ' bigint-ediv row? s" -7 7 0" ' bigint-emod row? -> true true true }T
T{ s" 0 7 -7" ' bigint- row? s" -3 5 2" ' bigint+ row? s" 3 -5 -2" ' bigint+ row? -> true true true }T
T{ s" -3 -5 -8" ' bigint+ row? s" -3 5 -8" ' bigint- row? s" 3 -5 8" ' bigint- row? -> true true true }T
T{ s" -5 -3 -2" ' bigint- row? s" -3 -5 2" ' bigint- row? s" 0 -7 7" ' bigint- row? -> true true true }T
T{ s" -3 7 -1" ' bigint-ediv row? s" -3 7 4" ' bigint-emod row? s" 3 -7 0" ' bigint-ediv row? -> true true true }T
T{ s" 0 0 0" ' bigint-ediv row? s" 0 0 0" ' bigint-emod row? s" -9 0 -9" ' bigint-emod row? -> true true true }T

\ ---- Lean's documented examples (DivMod/Basic.lean) ----

\ Int.ediv, lines 61-70.
T{ s" 7 0 0" ' bigint-ediv row? s" 0 7 0" ' bigint-ediv row? s" 12 6 2" ' bigint-ediv row? -> true true true }T
T{ s" 12 -6 -2" ' bigint-ediv row? s" -12 6 -2" ' bigint-ediv row? s" -12 -6 2" ' bigint-ediv row? -> true true true }T
T{ s" 12 7 1" ' bigint-ediv row? s" 12 -7 -1" ' bigint-ediv row? -> true true }T
T{ s" -12 7 -2" ' bigint-ediv row? s" -12 -7 2" ' bigint-ediv row? -> true true }T
\ Int.emod, lines 91-100.
T{ s" 7 0 7" ' bigint-emod row? s" 0 7 0" ' bigint-emod row? s" 12 6 0" ' bigint-emod row? -> true true true }T
T{ s" 12 -6 0" ' bigint-emod row? s" -12 6 0" ' bigint-emod row? s" -12 -6 0" ' bigint-emod row? -> true true true }T
T{ s" 12 7 5" ' bigint-emod row? s" 12 -7 5" ' bigint-emod row? -> true true }T
T{ s" -12 7 2" ' bigint-emod row? s" -12 -7 2" ' bigint-emod row? -> true true }T
\ Int.bmod, lines 306-315 (the modulus is a natural number).
T{ s" 7 0 7" ' bmod-by row? s" 0 7 0" ' bmod-by row? s" 12 6 0" ' bmod-by row? -> true true true }T
T{ s" 12 7 -2" ' bmod-by row? s" 12 8 -4" ' bmod-by row? s" 12 9 3" ' bmod-by row? -> true true true }T
T{ s" -12 6 0" ' bmod-by row? s" -12 7 2" ' bmod-by row? -> true true }T
T{ s" -12 8 -4" ' bmod-by row? s" -12 9 -3" ' bmod-by row? -> true true }T
\ bmod's boundary, 2r = m - 1, m, m + 1, and the moduli 1 and 2.
T{ s" 2 5 2" ' bmod-by row? s" 3 5 -2" ' bmod-by row? s" 4 8 -4" ' bmod-by row? s" 3 8 3" ' bmod-by row? -> true true true true }T
T{ s" -9 1 0" ' bmod-by row? s" 1 2 -1" ' bmod-by row? s" -1 2 -1" ' bmod-by row? s" -12 0 -12" ' bmod-by row? -> true true true true }T

\ ---- Carries across limbs, 2^64 boundaries ----

T{ s" 18446744073709551615 1 18446744073709551616" ' bigint+ row? -> true }T
T{ s" -18446744073709551616 1 -18446744073709551615" ' bigint+ row? -> true }T
T{ s" -18446744073709551615 1 -18446744073709551616" ' bigint- row? -> true }T
T{ s" 18446744073709551616 18446744073709551617 -1" ' bigint- row? -> true }T
T{ s" -340282366920938463463374607431768211456 340282366920938463463374607431768211455 -1"
   ' bigint+ row? -> true }T
T{ s" 18446744073709551616 -18446744073709551616 -340282366920938463463374607431768211456"
   ' bigint* row? -> true }T
\ -(2^128 - 1) and -(2^128 + 1) over +-2^64: quotients that round away
\ from zero, and their remainders.
: 2^128-1 ( -- c-addr u ) s" -340282366920938463463374607431768211455" ;
: 2^128+1 ( -- c-addr u ) s" -340282366920938463463374607431768211457" ;
: 2^64 ( -- i ) s" 18446744073709551616" int ;
T{ 2^128-1 int 2^64 ' bigint-ediv s" -18446744073709551616" op-gives? -> true }T
T{ 2^128-1 int 2^64 ' bigint-emod s" 1" op-gives? -> true }T
T{ 2^128-1 int s" -18446744073709551616" int ' bigint-ediv s" 18446744073709551616" op-gives? -> true }T
T{ 2^128+1 int 2^64 ' bigint-ediv s" -18446744073709551617" op-gives? -> true }T
T{ 2^128+1 int 2^64 ' bigint-emod s" 18446744073709551615" op-gives? -> true }T
T{ 2^128+1 int 2^64 ' bmod-by s" -1" op-gives? -> true }T

\ ---- Huge values ----

: 2^300 ( -- c-addr u )
  s" 2037035976334486086268445688409378161051468393665936250636140449354381299763336706183397376" ;
: 2^200+1 ( -- i ) s" 1606938044258990275541962092341162602522202993782792835301377" int ;
: -2^300 ( -- i ) 2^300 int ar bigint-negate drop ;
T{ 2^300 int -2^300 ' bigint* s" -4149515568880992958512407863691161151012446232242436899995657329690652811412908146399707048947103794288197886611300789182395151075411775307886874834113963687061181803401509523685376" op-gives? -> true }T
T{ -2^300 2^200+1 ' bigint-ediv s" -1267650600228229401496703205376" op-gives? -> true }T
T{ -2^300 2^200+1 ' bigint-emod s" 1267650600228229401496703205376" op-gives? -> true }T
T{ 2^300 int 2^200+1 ' bmod-by s" -1267650600228229401496703205376" op-gives? -> true }T
T{ -2^300 2^200+1 ' bmod-by s" 1267650600228229401496703205376" op-gives? -> true }T
T{ -2^300 s" -9641628265553941653251772554046975615133217962696757011808256" int ar bigint-gcd
   s" 3213876088517980551083924184682325205044405987565585670602752" nat-gives? -> true }T
T{ -2^300 2^300 int ' bigint+ s" 0" op-gives? -2^300 -2^300 ' bigint- s" 0" op-gives? -> true true }T

\ ---- Powers, gcd, natAbs, toNat ----

T{ s" -3 7 -2187" ' pow-by row? s" -3 0 1" ' pow-by row? s" 0 0 1" ' pow-by row? s" 0 5 0" ' pow-by row? -> true true true true }T
T{ s" -2 201 -3213876088517980551083924184682325205044405987565585670602752" ' pow-by row? -> true }T
T{ s" -2 200 1606938044258990275541962092341162602522202993782792835301376" ' pow-by row? -> true }T
T{ s" -18446744073709551616 3 -6277101735386680763835789423207666416102355444464034512896" ' pow-by row? -> true }T
\ An exponent of two limbs: (-1)^(2^64 + 1) = -1 and (-1)^(2^64) = 1; for
\ a base above 1 such a power is full (bignum.fs).
T{ s" -1 18446744073709551617 -1" ' pow-by row? s" -1 18446744073709551616 1" ' pow-by row? -> true true }T
T{ s" -2" int s" 18446744073709551616" nat ar bigint-pow -> -1 outcome-full }T
T{ s" 0 0 0" ' bigint-gcd nat-row? s" -12 0 12" ' bigint-gcd nat-row? s" 0 -12 12" ' bigint-gcd nat-row? -> true true true }T
T{ s" -12 -18 6" ' bigint-gcd nat-row? s" 12 -18 6" ' bigint-gcd nat-row? -> true true }T
T{ s" -18446744073709551616" int ar bigint-natAbs s" 18446744073709551616" nat-gives? -> true }T
T{ s" 0" int ar bigint-natAbs s" 0" nat-gives? s" 7" int ar bigint-natAbs s" 7" nat-gives? -> true true }T
T{ s" -5" int ar bigint-toNat s" 0" nat-gives? s" 5" int ar bigint-toNat s" 5" nat-gives? -> true true }T
T{ s" 0" int ar bigint-toNat s" 0" nat-gives? -> true }T
T{ s" -77" int bigint-magnitude s" 77" nat big= -> true }T
T{ s" 0" int ar bigint-negate s" 0" gives? s" -18446744073709551616" int ar bigint-negate
   s" 18446744073709551616" gives? -> true true }T

\ ---- Comparison ----

T{ s" -5" int s" 3" int bigint-compare s" 3" int s" -5" int bigint-compare -> -1 1 }T
T{ s" -5" int s" -3" int bigint-compare s" -3" int s" -5" int bigint-compare -> -1 1 }T
T{ s" -5" int s" -5" int bigint-compare s" 0" int s" -0" int bigint-compare -> 0 0 }T
T{ s" 0" int s" -1" int bigint-compare s" 0" int s" 1" int bigint-compare -> 1 -1 }T
T{ 2^64 s" 18446744073709551615" int bigint-compare -> 1 }T
T{ s" -18446744073709551616" int s" -18446744073709551615" int bigint-compare -> -1 }T

\ ---- Cells and natural numbers ----

: min-n ( -- n ) max-n negate 1- ;
T{ 0 ar n>bigint s" 0" gives? -1 ar n>bigint s" -1" gives? 42 ar n>bigint s" 42" gives? -> true true true }T
T{ max-n ar n>bigint drop bigint>n min-n ar n>bigint drop bigint>n -> max-n true min-n true }T
\ The most negative cell: magnitude max-n + 1, read unsigned.
T{ min-n ar n>bigint drop dup bigint-sign swap bigint-magnitude big>u -> -1 max-n 1+ true }T
T{ min-n ar n>bigint drop max-n ar n>bigint drop ar bigint+ s" -1" gives? -> true }T
\ bigint>n refuses max-n + 1, -(max-n + 2) and two limbs.
T{ max-n ar n>bigint drop s" 1" int ar bigint+ drop bigint>n -> false }T
T{ min-n ar n>bigint drop s" -1" int ar bigint+ drop bigint>n -> false }T
T{ s" 0" int bigint>n s" -42" int bigint>n -> 0 true -42 true }T
T{ s" -340282366920938463463374607431768211456" int bigint>n -> false }T
T{ s" 18446744073709551616" nat ar nat>bigint s" 18446744073709551616" gives? -> true }T
T{ s" 0" nat ar nat>bigint s" 0" gives? -> true }T

\ ---- Decimal text ----

: refused-text? ( c-addr u -- flag )
  top >r ar decimal>bigint outcome-invalid = swap -1 = and top r> = and ;
T{ s" " refused-text? s" -" refused-text? s" --1" refused-text? s" +1" refused-text? -> true true true true }T
T{ s"  1" refused-text? s" 1 " refused-text? s" 1-" refused-text? s" 12x4" refused-text? -> true true true true }T
T{ s" -x" refused-text? s" - 1" refused-text? s" -+1" refused-text? s" 1.0" refused-text? -> true true true true }T
T{ s" -007" int text s" -7" compare s" 000" int text s" 0" compare -> 0 0 }T
T{ s" -18446744073709551616" int text s" -18446744073709551616" compare -> 0 }T
T{ 2^300 int text 2^300 compare -> 0 }T
\ Printing twice gives the same text: printing leaves the integer as it was.
: twice? ( c-addr u -- flag ) 2dup int dup text 2drop text compare 0= ;
T{ s" -1" twice? s" -10000000000000000000" twice? s" -18446744073709551615" twice? -> true true true }T
T{ s" -340282366920938463463374607431768211455" twice? s" 123456789" twice? -> true true }T

\ ---- Operands are never changed ----

2variable a-text  2variable b-text
: kept? ( a b xt -- flag )
  >r over text a-text 2! dup text b-text 2! 2dup ar r> execute 2drop
  text b-text 2@ compare 0= swap text a-text 2@ compare 0= and ;
: -2^64 ( -- i ) s" -18446744073709551616" int ;
T{ 2^128+1 int -2^64 ' bigint-ediv kept? 2^128+1 int -2^64 ' bigint-emod kept? -> true true }T
T{ 2^128+1 int s" 18446744073709551617" int ' bmod-by kept? -> true }T
T{ s" -3" int s" 5" int ' pow-by kept? s" -3" int s" 5" int ' bigint- kept? -> true true }T
T{ s" -3" int s" 5" int ' bigint-gcd kept? s" -3" int s" 5" int ' bigint* kept? -> true true }T

\ ---- Stack effects: both stacks balanced ----

T{ s" -9" int s" 4" int ar ' bigint-ediv rs-checked s" -3" gives? -> true }T
T{ s" -9" int s" 4" int ar ' bigint-emod rs-checked s" 3" gives? -> true }T
T{ s" -9" int s" 4" int ar ' bigint+ rs-checked s" -5" gives? -> true }T
T{ s" -9" int s" 4" int ar ' bigint- rs-checked s" -13" gives? -> true }T
T{ s" -9" int s" 4" int ar ' bigint* rs-checked s" -36" gives? -> true }T
T{ s" -9" int s" 6" int ar ' bigint-gcd rs-checked s" 3" nat-gives? -> true }T
T{ s" -9" int s" 4" nat ar ' bigint-bmod rs-checked s" -1" gives? -> true }T
T{ s" -9" int s" 3" nat ar ' bigint-pow rs-checked s" -729" gives? -> true }T
T{ s" -9" int ar ' bigint-negate rs-checked s" 9" gives? -> true }T
T{ s" -9" int ar ' bigint-natAbs rs-checked s" 9" nat-gives? -> true }T
T{ s" -9" int ar ' bigint-toNat rs-checked s" 0" nat-gives? -> true }T
T{ s" 9" nat ar ' nat>bigint rs-checked s" 9" gives? -> true }T
T{ -9 ar ' n>bigint rs-checked s" -9" gives? -> true }T
T{ s" -9" ar ' decimal>bigint rs-checked s" -9" gives? -> true }T
T{ s" -9" int ar ' bigint>decimal rs-checked >r s" -9" compare r> -> 0 outcome-ok }T
T{ s" -9" int ' bigint>n rs-checked s" -9" int ' bigint-sign rs-checked -> -9 true -1 }T
T{ s" -9" int s" 4" int ' bigint-compare rs-checked s" -9" int ' bigint-valid? rs-checked -> -1 true }T
T{ s" -9" int ' bigint-magnitude rs-checked s" 9" nat big= -> true }T

\ ---- The bit limit ----

\ At a limit of 64 bits: results of 65 bits are full, with nothing made;
\ results of 64 bits are made. No value on the way is longer than the
\ result or an operand.
: full? ( x outcome mark -- flag ) top = -rot -1 outcome-full d= and ;
: limited? ( a b xt -- flag ) top >r >r ar r> execute r> full? ;
: 2^64-1 ( -- c-addr u ) s" 18446744073709551615" ;
: -2^64+1 ( -- c-addr u ) s" -18446744073709551615" ;
T{ 64 ar big-limit! -> }T
T{ 2^64-1 int s" 1" int ' bigint+ limited? -2^64+1 int s" 1" int ' bigint- limited? -> true true }T
T{ 2^64-1 int s" -1" int ' bigint- limited? s" 4294967296" int dup ' bigint* limited? -> true true }T
T{ s" -2" int s" 64" int ' pow-by limited? -> true }T
T{ top s" -18446744073709551616" ar decimal>bigint rot full? -> true }T
T{ -2^64+1 int s" 1" int ' bigint+ s" -18446744073709551614" op-gives? -> true }T
T{ -2^64+1 int s" 1" int ' bigint-ediv s" -18446744073709551615" op-gives? -> true }T
T{ -2^64+1 int 2^64-1 int ' bigint-emod s" 0" op-gives? -> true }T
T{ -2^64+1 int 2^64-1 int ' bmod-by s" 0" op-gives? -> true }T
T{ s" -2 63 -9223372036854775808" ' pow-by row? -> true }T
T{ big-lean-bits ar big-limit! -> }T

\ ---- No room: every room from 0 cells up ----

\ An arena of room cells between guard cells. In every room an operation
\ gives the right result, or is full with nothing made, and writes nothing
\ outside the arena. Operands and reference results live in ar (outside
\ gar, so live). first-ok is the first room in which the operation worked.
1515870810 constant pattern
64 constant guard-cells
240 constant most-room
most-room guard-cells 2* + constant guarded-cells
create guarded guarded-cells cells allot
create gar /big-arena allot
: guard-fill ( -- ) guarded guarded-cells cells over + swap ?do pattern i ! cell +loop ;
: gar-init ( room -- ) guard-fill guarded guard-cells cells + swap cells gar big-arena-init ;
: guarded? ( addr n -- flag ) true -rot cells over + swap ?do i @ pattern = and cell +loop ;
: above-guards ( room -- addr n ) guard-cells + dup cells guarded + guarded-cells rot - ;
: guards? ( room -- flag ) guarded guard-cells guarded? swap above-guards guarded? and ;
: gar-empty? ( -- flag ) gar big-mark gar arena-start @ = ;

variable sweep-a  variable sweep-b  variable sweep-xt  variable sweep-show
2variable sweep-ref  variable first-ok
: sweep-op ( arena -- x outcome ) >r sweep-a @ sweep-b @ r> sweep-xt @ execute ;
: shown ( x -- c-addr u ) sweep-show @ execute ;
\ Whether x prints as the reference result (printed in ar, then given back).
: same? ( x -- flag ) top >r shown sweep-ref 2@ compare 0= r> ar big-release drop ;
: gar-sound? ( x outcome -- flag )
  dup ok? if drop same? exit then -1 outcome-full d= gar-empty? and ;
: note-ok ( room -- room ) gar-empty? 0= first-ok @ 0< and if dup first-ok ! then ;
: sweep-room ( room -- flag ) dup gar-init gar sweep-op gar-sound? swap note-ok guards? and ;
\ a b xt in every room below most-room, printed by show ( x -- c-addr u ).
: swept? ( a b xt show -- flag )
  sweep-show ! sweep-xt ! sweep-b ! sweep-a !
  ar sweep-op drop shown sweep-ref 2! -1 first-ok !
  true most-room 0 ?do i sweep-room and loop first-ok @ 0 most-room within and ;
\ Operations of two arguments for the sweep.
: negate-by ( a b arena -- c outcome ) nip bigint-negate ;
: natabs-by ( a b arena -- big outcome ) nip bigint-natAbs ;
: tonat-by ( a b arena -- big outcome ) nip bigint-toNat ;
: cell-by ( n b arena -- i outcome ) nip n>bigint ;
: nat-by ( big b arena -- i outcome ) nip nat>bigint ;
: -2^128+1 ( -- i ) 2^128-1 int ;
: 2^64+3 ( -- i ) s" 18446744073709551619" int ;
T{ -2^128+1 2^64+3 ' bigint+ ' text swept? -2^128+1 2^64+3 ' bigint- ' text swept? -> true true }T
T{ -2^128+1 2^64+3 ' bigint* ' text swept? -> true }T
T{ -2^128+1 2^64+3 ' bigint-ediv ' text swept? -2^128+1 2^64+3 ' bigint-emod ' text swept? -> true true }T
T{ -2^128+1 2^64+3 ' bmod-by ' text swept? -2^128+1 s" 3" int ' pow-by ' text swept? -> true true }T
T{ -2^128+1 2^64+3 ' bigint-gcd ' nat-text swept? -2^128+1 0 ' negate-by ' text swept? -> true true }T
T{ -2^128+1 0 ' natabs-by ' nat-text swept? 2^64+3 0 ' tonat-by ' nat-text swept? -> true true }T
T{ min-n 0 ' cell-by ' text swept? s" 340282366920938463463374607431768211457" nat 0 ' nat-by ' text swept?
   -> true true }T
: neg-text ( -- c-addr u ) s" -340282366920938463463374607431768211457" ;
T{ neg-text ' decimal>bigint ' text swept? -> true }T

\ Printing in every room: the reference integer (in ar) printed in gar,
\ right or 0 0 full with gar left empty, the guards kept.
variable print-int
: print-sound? ( c-addr u outcome -- flag )
  dup ok? if drop sweep-ref 2@ compare 0= exit then
  outcome-full = -rot 0 0 d= and gar-empty? and ;
: printed? ( room -- flag )
  dup gar-init print-int @ gar bigint>decimal print-sound? swap note-ok guards? and ;
: print-swept? ( c-addr u -- flag )
  2dup sweep-ref 2! int print-int ! -1 first-ok !
  true 80 0 ?do i printed? and loop first-ok @ 0 80 within and ;
T{ s" -1" print-swept? s" -340282366920938463463374607431768211457" print-swept? -> true true }T
T{ s" 0" print-swept? s" 18446744073709551616" print-swept? -> true true }T

\ ---- No heap ----

\ The library never allocates: no block more is held, and with the next
\ allocation refused, every kind of operation still works and the refusal
\ is still pending.
T{ live-blocks @ -> 1 }T
1 heap-refusals !
T{ -2^128+1 2^64+3 ' bigint-ediv s" -18446744073709551614" op-gives? -> true }T
T{ -2^128+1 2^64+3 ' bmod-by s" -8" op-gives? -> true }T
T{ -2^128+1 ar bigint>decimal nip nip -9 ar n>bigint nip -> outcome-ok outcome-ok }T
T{ heap-refusals @ live-blocks @ -> 1 1 }T
0 heap-refusals !

cases-done
bye

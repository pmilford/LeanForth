\ Unit tests of src/lib/bignum.fs: limb geometry, arenas and marks, the
\ conversions, every operation's edge cases (0, 1, limb boundaries, max-u
\ plus and minus one, equal operands, subtraction below 0, division by 0,
\ huge shifts and exponents), and every failure: invalid numbers, text and
\ arenas, no room, and the bit limit; a failure leaves the arena's top
\ where it was. Random cases against Python's integers, planted faults and
\ the Lean comparison are in tests/lib/bignum_differential.py. Expected
\ values are decimal text, so they hold whatever the cell size; on a 64-bit
\ host they cross limb boundaries. The module is loaded under HEX: its
\ numbers must not depend on BASE.
include ../support/tester.fs
include ../support/checks.fs
hex require ../../src/lib/bignum.fs base @ decimal constant base-after-load

T{ base-after-load -> 16 }T

\ Limb geometry, checked independently: the top bit of a cell, and the
\ decimal chunk, whose next power of ten no longer fits a limb.
T{ 1 limb-bits 1- lshift 0<> -> true }T
T{ 1 limb-bits 1- lshift 2* -> 0 }T
: ten^ ( k -- u ) 1 swap 0 ?do 10 * loop ;
T{ chunk-digits ten^ chunk-base = -> true }T
T{ chunk-base 10 um* nip 0<> -> true }T
T{ 0 bit-length 1 bit-length -1 bit-length limb-bits = -> 0 1 true }T
\ bit-length of 2^i and 2^i - 1 for every bit i of a cell.
: bit-lengths? ( -- flag )
  true limb-bits 0 do
    1 i lshift bit-length i 1+ = and 1 i lshift 1- bit-length i = and loop ;
T{ bit-lengths? -> true }T

\ A 4 MiB arena for most tests.
create ar /big-arena allot
4194304 constant ar-bytes
ar-bytes allocate throw ar-bytes ar big-arena-init
T{ ar arena-valid? ar arena-limit @ -> true big-lean-bits }T

: num ( c-addr u -- big ) ar decimal>big outcome-ok <> abort" test number" ;
\ Whether an operation gave ok and the number with these digits, read
\ again after printing: printing must leave the number as it was.
: gives? ( big outcome c-addr u -- flag )
  2swap outcome-ok <> if drop 2drop false exit then
  >r 2dup r@ ar big>decimal drop compare 0= -rot num r> big= and ;
: top ( -- addr ) ar big-mark ;
: max-u ( -- big ) -1 ar u>big drop ;
: max-u+1 ( -- big ) max-u s" 1" num ar big+ drop ;
\ An operation on two numbers given as text.
: op-case ( a-addr a-u b-addr b-u xt -- big outcome )
  >r 2swap num -rot num ar r> execute ;

\ Arenas: alignment, size, marks.
create ar3 /big-arena allot
create odd 10 cells allot
T{ odd 1+ 5 cells ar3 big-arena-init ar3 arena-room ar3 arena-start @ odd cell+ =
   -> 4 true }T
T{ odd -8 ar3 big-arena-init ar3 arena-room ar3 arena-valid? -> 0 true }T
T{ 7 ar3 u>big -> -1 outcome-full }T

\ Conversions.
T{ 0 ar u>big drop dup @ swap big>u -> 0 0 true }T
T{ -1 ar u>big drop big>u -> -1 true }T
T{ max-u+1 big>u -> false }T
T{ s" 000" num big>u s" 00042" num big>u -> 0 true 42 true }T
: digits-of ( big -- addr u ) ar big>decimal outcome-ok <> abort" test print" ;
T{ max-u digits-of -1 0 <# #s #> compare -> 0 }T
T{ s" 0" num ar big>decimal -> top 1 cells - 1 outcome-ok }T
T{ s" 0" num big-bits s" 1" num big-bits s" 1024" num big-bits -> 0 1 11 }T
T{ max-u big-bits max-u+1 big-bits -> limb-bits limb-bits 1+ }T
T{ s" 123456789012345678901234567890" num digits-of
   s" 123456789012345678901234567890" compare -> 0 }T
\ The result is the arena's newest number; its digits follow it.
T{ s" 7" s" 8" ' big* op-case drop big-end top = -> true }T
T{ s" 56" num ar big>decimal drop + top <= -> true }T
\ Printing leaves the number unchanged: printed twice, the same digits.
\ (The top chunk is written whole, leading zeros too; they once went
\ below the text's room, into the number just printed.)
: twice? ( c-addr u -- flag ) 2dup num dup digits-of 2drop digits-of compare 0= ;
T{ s" 1" twice? s" 10000000000000000000" twice? s" 18446744073709551615" twice?
   -> true true true }T
T{ s" 340282366920938463463374607431768211455" twice? s" 123456789" twice? -> true true }T

\ Text that is not a number: invalid, nothing made.
: refused-text ( c-addr u -- flag )
  top >r ar decimal>big outcome-invalid = swap -1 = and top r> = and ;
T{ s" " refused-text s" 12x4" refused-text s" -1" refused-text -> true true true }T
T{ s"  1" refused-text s" 1 " refused-text s" +5" refused-text -> true true true }T

\ Each operation on its edge cases.
T{ s" 0" s" 0" ' big+ op-case s" 0" gives? -> true }T
T{ s" 18446744073709551615" s" 1" ' big+ op-case
   s" 18446744073709551616" gives? -> true }T
T{ s" 18446744073709551615" s" 18446744073709551615" ' big+ op-case
   s" 36893488147419103230" gives? -> true }T
T{ max-u s" 1" num ar big+ drop s" 1" num ar big- drop max-u big= -> true }T
T{ s" 5" s" 7" ' big- op-case s" 0" gives? -> true }T
T{ s" 7" s" 7" ' big- op-case s" 0" gives? -> true }T
T{ s" 340282366920938463463374607431768211456" s" 1" ' big- op-case
   s" 340282366920938463463374607431768211455" gives? -> true }T
T{ s" 0" s" 123" ' big* op-case s" 0" gives? -> true }T
T{ s" 18446744073709551615" s" 18446744073709551615" ' big* op-case
   s" 340282366920938463426481119284349108225" gives? -> true }T
T{ s" 17" s" 0" ' big/ op-case s" 0" gives? -> true }T
T{ s" 17" s" 0" ' big-mod op-case s" 17" gives? -> true }T
T{ s" 0" s" 0" ' big/ op-case s" 0" gives? -> true }T
T{ s" 0" s" 0" ' big-mod op-case s" 0" gives? -> true }T
T{ s" 17" s" 17" ' big/ op-case s" 1" gives? -> true }T
T{ s" 16" s" 17" ' big/ op-case s" 0" gives? -> true }T
T{ s" 16" s" 17" ' big-mod op-case s" 16" gives? -> true }T
T{ s" 340282366920938463463374607431768211455" s" 18446744073709551617" ' big/ op-case
   s" 18446744073709551615" gives? -> true }T
T{ s" 340282366920938463463374607431768211455" s" 18446744073709551617" ' big-mod op-case
   s" 0" gives? -> true }T
T{ s" 1000000000000000000000000000000000000000000000000001" s" 7" ' big-mod op-case
   s" 0" gives? -> true }T
T{ s" 0" s" 0" ' big-gcd op-case s" 0" gives? -> true }T
T{ s" 0" s" 12" ' big-gcd op-case s" 12" gives? -> true }T
T{ s" 12" s" 0" ' big-gcd op-case s" 12" gives? -> true }T
T{ s" 12" s" 18" ' big-gcd op-case s" 6" gives? -> true }T
T{ s" 354224848179261915075" s" 218922995834555169026" ' big-gcd op-case
   s" 1" gives? -> true }T
T{ s" 1" s" 340282366920938463463374607431768211455" ' big-gcd op-case
   s" 1" gives? -> true }T
T{ s" 12" s" 10" ' big-and op-case s" 8" gives? -> true }T
T{ s" 12" s" 10" ' big-or op-case s" 14" gives? -> true }T
T{ s" 12" s" 10" ' big-xor op-case s" 6" gives? -> true }T
T{ s" 340282366920938463463374607431768211455" s" 1" ' big-and op-case
   s" 1" gives? -> true }T
T{ s" 18446744073709551616" s" 18446744073709551616" ' big-xor op-case
   s" 0" gives? -> true }T
T{ s" 3" s" 0" ' big-lshift op-case s" 3" gives? -> true }T
T{ s" 1" s" 64" ' big-lshift op-case s" 18446744073709551616" gives? -> true }T
T{ s" 0" s" 18446744073709551616" ' big-lshift op-case s" 0" gives? -> true }T
T{ s" 1" s" 18446744073709551616" ' big-lshift op-case -> -1 outcome-full }T
T{ s" 18446744073709551616" s" 64" ' big-rshift op-case s" 1" gives? -> true }T
T{ s" 18446744073709551615" s" 64" ' big-rshift op-case s" 0" gives? -> true }T
T{ s" 5" s" 100000000000000000000000" ' big-rshift op-case s" 0" gives? -> true }T
T{ s" 0" s" 0" ' big-pow op-case s" 1" gives? -> true }T
T{ s" 0" s" 5" ' big-pow op-case s" 0" gives? -> true }T
T{ s" 1" s" 100000000000000000000000" ' big-pow op-case s" 1" gives? -> true }T
T{ s" 0" s" 100000000000000000000000" ' big-pow op-case s" 0" gives? -> true }T
T{ s" 2" s" 100000000000000000000000" ' big-pow op-case -> -1 outcome-full }T
T{ s" 2" s" 64" ' big-pow op-case s" 18446744073709551616" gives? -> true }T
T{ s" 10" s" 30" ' big-pow op-case s" 1000000000000000000000000000000" gives? -> true }T
\ Every operation leaves both stacks balanced.
T{ s" 9" num s" 4" num ar ' big-gcd rs-checked s" 1" gives? -> true }T

\ Comparisons (Nat.beq, Nat.ble).
T{ s" 5" num s" 5" num big-compare s" 5" num s" 6" num big-compare
   s" 6" num s" 5" num big-compare -> 0 -1 1 }T
T{ max-u max-u+1 big<= max-u+1 max-u big<= max-u max-u big= -> true false true }T
T{ s" 18446744073709551617" num s" 18446744073709551616" num big-compare -> 1 }T
T{ s" 0" num s" 0" num big= s" 0" num s" 1" num big<= -> true true }T

\ Malformed numbers: a negative count, or a zero top limb.
create bad1 2 cells allot  -1 bad1 !
create bad2 3 cells allot  2 bad2 !  5 bad2 cell+ !  0 bad2 2 cells + !
T{ bad1 big-valid? bad2 big-valid? s" 9" num big-valid? -> false false true }T
create binary-ops ' big+ , ' big- , ' big* , ' big/ , ' big-mod , ' big-gcd , ' big-and ,
  ' big-or , ' big-xor , ' big-lshift , ' big-rshift , ' big-pow ,
: refused ( a b xt -- flag ) top >r >r ar r> execute -1 outcome-invalid d= top r> = and ;
: refused-all ( a b -- flag )
  true -rot 12 0 do 2dup binary-ops i cells + @ refused >r rot r> and -rot loop 2drop ;
T{ bad1 s" 1" num refused-all s" 1" num bad2 refused-all -> true true }T
T{ bad2 ar big>decimal -> 0 0 outcome-invalid }T

\ A released (stale) number in the arena's free part is invalid too, as
\ an operand or printed: the result would overwrite it. It is still well
\ formed; big-live? finds it from addresses. Made after the live operand.
: max-2^128 ( -- c-addr u ) s" 340282366920938463463374607431768211455" ;
: stale ( -- big ) top max-2^128 num drop dup ar big-release drop ;
\ Released in part: the top is moved back into its limbs.
: straddling ( -- big ) top max-2^128 num drop dup 2 cells + ar big-release drop ;
T{ stale dup big-valid? swap ar big-live? -> true false }T
T{ s" 7" num stale refused-all s" 7" num stale swap refused-all -> true true }T
T{ s" 7" num straddling refused-all s" 7" num straddling swap refused-all -> true true }T
T{ stale stale refused-all -> true }T
\ Printing big: its result, and whether the top stayed where it was.
: print-kept ( big -- addr u outcome flag ) top >r ar big>decimal top r> = ;
T{ stale print-kept -> 0 0 outcome-invalid true }T
T{ straddling print-kept -> 0 0 outcome-invalid true }T
\ The newest number is live, and so is one outside the arena.
create dict-one 1 , 1 ,   \ the number 1, in the dictionary
T{ max-2^128 num ar big-live? dict-one ar big-live? -> true true }T
T{ dict-one dict-one ar big+ s" 2" gives? -> true }T

\ A corrupted arena record: top beyond end, or a limit out of range.
create ar2 /big-arena allot
\ A copy of ar with x stored in the field at offset field.
: corrupt ( x field -- ) ar ar2 /big-arena move ar2 + ! ;
T{ ar arena-end @ cell+ 0 arena-top corrupt ar2 arena-valid? -> false }T
T{ s" 1" num s" 1" num ar2 big+ -> -1 outcome-invalid }T
T{ 7 ar2 u>big -> -1 outcome-invalid }T
T{ s" 7" ar2 decimal>big -> -1 outcome-invalid }T
T{ -1 0 arena-limit corrupt ar2 arena-valid? -> false }T
T{ s" 1" num ar2 big>decimal -> 0 0 outcome-invalid }T

\ Limits: big-limit! keeps the limit in range; past it, full, top unchanged.
T{ -5 ar big-limit! ar arena-limit @ -> 0 }T
T{ max-n ar big-limit! ar arena-limit @ -> big-max-limit }T
T{ 10 ar big-limit! -> }T
: full? ( big outcome mark -- flag ) top = -rot -1 outcome-full d= and ;
\ Whether the operation is full and leaves the arena's top where it was.
: refused-full ( a b xt -- flag ) top >r >r ar r> execute r> full? ;
T{ s" 1023" ar decimal>big nip -> outcome-ok }T
T{ top s" 1024" ar decimal>big rot full? -> true }T
T{ s" 1023" num s" 1" num ' big+ refused-full -> true }T
T{ s" 512" num s" 2" num ' big* refused-full -> true }T
T{ s" 32" num s" 31" num ar big* s" 992" gives? -> true }T
T{ s" 1" num s" 10" num ' big-lshift refused-full -> true }T
T{ s" 1" num s" 9" num ar big-lshift s" 512" gives? -> true }T
T{ s" 2" num s" 10" num ' big-pow refused-full -> true }T
T{ s" 3" num s" 6" num ar big-pow s" 729" gives? -> true }T
T{ s" 3" num s" 7" num ' big-pow refused-full -> true }T
T{ 0 ar big-limit! s" 0" ar decimal>big nip s" 1" ar decimal>big
   -> outcome-ok -1 outcome-full }T
\ A power over the limit is refused before its last product is made: at
\ a limit of 4,096 bits, 3^4095 (6,491 bits: 3^2047 squared cannot fit)
\ writes no higher above the top than the valid 3^2047 (3,245 bits). The
\ free part is filled with a pattern first; the highest changed cell is
\ the high-water mark.
1515870810 constant pattern
2048 constant watched
: pattern-fill ( -- ) top watched cells over + swap ?do pattern i ! cell +loop ;
: high-water ( -- cells )
  watched begin dup 0> while 1- dup cells top + @ pattern <> if 1+ exit then repeat ;
: pow-written ( c-addr u -- cells )
  s" 3" num -rot num pattern-fill top >r ar big-pow 2drop r> ar big-release drop
  high-water ;
T{ 4096 ar big-limit! s" 3" num s" 4095" num ' big-pow refused-full -> true }T
T{ s" 4095" pow-written s" 2047" pow-written > s" 2047" pow-written 0> -> false true }T
T{ big-lean-bits ar big-limit! -> }T

\ No room: an arena of 64 cells, where a number of k limbs takes k + 1.
create small /big-arena allot
create small-mem 64 cells allot
small-mem 64 cells small big-arena-init
T{ small big-mark small-mem = small arena-room -> true 64 }T
T{ 64 small arena-claim 63 small arena-claim nip -> false true }T
T{ small-mem small big-release -> outcome-ok }T
T{ small-mem cell+ small big-release -> outcome-invalid }T
T{ small-mem cell - small big-release -> outcome-invalid }T
T{ 5 small u>big 2drop small-mem 1+ small big-release small big-mark
   -> outcome-invalid small-mem 2 cells + }T
T{ small-mem small big-release -> outcome-ok }T
\ Whether an operation in the small arena is full and leaves its top.
: small-full? ( c outcome mark -- flag ) small big-mark = -rot -1 outcome-full d= and ;
: small-refused ( a b xt -- flag ) small big-mark >r >r small r> execute r> small-full? ;
create text 2000 chars allot  text 2000 chars char 7 fill
T{ small big-mark text 2000 small decimal>big rot small-full? -> true }T
\ 900 digits (2,990 bits) take 48 of the 64 cells: no room for 900 digits
\ more, nor for their sum, product, text, a remainder or the scratch of a gcd.
T{ text 900 small decimal>big nip -> outcome-ok }T
small-mem constant nines
T{ nines big-bits small big-mark nines - cell / -> 2990 48 }T
T{ small big-mark text 900 small decimal>big rot small-full? -> true }T
T{ nines nines ' big* small-refused nines nines ' big+ small-refused -> true true }T
T{ nines nines ' big-gcd small-refused nines s" 2" num ' big-mod small-refused
   -> true true }T
T{ small big-mark nines small big>decimal nip nip swap small big-mark =
   -> outcome-full true }T
T{ s" 7" num s" 8" num small big+ s" 15" gives? -> true }T

\ ---- Guarded arenas: every room from 0 cells up ----
\ An arena of room cells between guard cells (the pattern above). In
\ every room each operation gives the right value, or is full with
\ nothing made, and writes nothing outside the arena; printing gives the
\ digits, or 0 0 full, and leaves the number printed as it was, also
\ when it is the arena's newest. Operands and reference values live in
\ ar. A room too small for Karatsuba's scratch would stop the run
\ (kara-child's ABORT"), so the sweep also shows mul-cells is enough.
64 constant guard-cells
1200 constant most-room
most-room guard-cells 2* + constant guarded-cells
create guarded guarded-cells cells allot
create gar /big-arena allot
: guard-fill ( -- ) guarded guarded-cells cells over + swap ?do pattern i ! cell +loop ;
: gar-init ( room -- )
  guard-fill guarded guard-cells cells + swap cells gar big-arena-init ;
\ Whether the n cells from addr still hold the pattern: those below the
\ arena, and all of those above it.
: guarded? ( addr n -- flag )
  true -rot cells over + swap ?do i @ pattern = and cell +loop ;
: below-guards ( -- addr n ) guarded guard-cells ;
: above-guards ( room -- addr n ) guard-cells + dup cells guarded + guarded-cells rot - ;
: guards? ( room -- flag ) below-guards guarded? swap above-guards guarded? and ;
: gar-empty? ( -- flag ) gar big-mark gar arena-start @ = ;

\ One operation in every room below rooms; first-ok is the first room in
\ which it worked, or -1. Test-only variables.
variable sweep-a  variable sweep-b  variable sweep-xt  variable sweep-ref
variable first-ok
: gar-sound? ( c outcome -- flag )
  dup ok? if drop sweep-ref @ big= exit then -1 outcome-full d= gar-empty? and ;
: note-ok ( room -- room ) gar-empty? 0= first-ok @ 0< and if dup first-ok ! then ;
: sweep-op ( -- c outcome ) sweep-a @ sweep-b @ gar sweep-xt @ execute ;
: sweep-room ( room -- flag ) dup gar-init sweep-op gar-sound? swap note-ok guards? and ;
\ a op b in every room below rooms, against its value computed in ar.
: swept? ( a b xt rooms -- flag )
  >r sweep-xt ! sweep-b ! sweep-a ! sweep-a @ sweep-b @ ar sweep-xt @ execute drop
  sweep-ref ! -1 first-ok ! true r> 0 ?do i sweep-room and loop ;
\ All twelve operations; worked counts those that worked in some room.
variable pair-a  variable pair-b  variable pair-rooms  variable worked
: op-swept? ( i -- flag )
  >r pair-a @ pair-b @ binary-ops r> cells + @ pair-rooms @ swept?
  first-ok @ 0< 0= if 1 worked +! then ;
: all-swept? ( a b rooms -- flag )
  pair-rooms ! pair-b ! pair-a ! 0 worked ! true 12 0 do i op-swept? and loop ;
\ 2^(n limb-bits) - 1: n limbs of ones.
: ones ( n -- big )
  limb-bits * >r s" 1" num r> ar u>big drop ar big-lshift drop s" 1" num ar big- drop ;
T{ s" 6277101735386680763835789423207666416102355444464034512895" num s" 1" num
   80 all-swept? worked @ -> true 12 }T
T{ s" 3" num s" 100" num 80 all-swept? worked @ -> true 12 }T
\ The power and the left shift are full in every room.
T{ 5 ones 2 ones 120 all-swept? worked @ -> true 10 }T
\ The room a product needs, exactly: by rows, the result and a frame; by
\ Karatsuba, the result, the job with T (2 nb limbs) and the Karatsuba
\ scratch, but no padded copy of a short last chunk (160 by 100 limbs: a
\ tail of 60; 233 by 144: tails of 89, 55 and 34).
: rows-room ( na nb -- cells ) + 1+ kara-cells + 1+ ;
: kara-room ( na nb -- cells ) tuck + 1+ over 2* chunks-cells + 1+ + swap kara-scratch + ;
T{ 100 ones 47 ones ' big* 300 swept? first-ok @ -> true 100 47 rows-room }T
T{ 160 ones 100 ones ' big* 850 swept? first-ok @ -> true 160 100 kara-room }T
T{ 233 ones 144 ones ' big* most-room swept? first-ok @ -> true 233 144 kara-room }T

\ Printing: the reference number (in ar) printed in gar; and its digits
\ read into gar and printed there, the number unchanged after.
2variable ref-text  variable ref-big
\ Whether addr u outcome is the reference text, or 0 0 full with gar's
\ top still at mark.
: print-sound? ( addr u outcome mark -- flag )
  >r dup ok? if drop ref-text 2@ compare 0= r> drop exit then
  outcome-full = -rot 0 0 d= and gar big-mark r> = and ;
: printed? ( room -- flag )
  dup gar-init ref-big @ gar big>decimal gar arena-start @ print-sound?
  swap guards? and ;
: print-kept? ( x -- flag )
  gar big-mark >r dup gar big>decimal r> print-sound? swap ref-big @ big= and ;
: reprinted? ( room -- flag )
  dup gar-init ref-text 2@ gar decimal>big ok? if print-kept? else drop true then
  swap guards? and ;
: print-swept? ( c-addr u rooms -- flag )
  >r 2dup ref-text 2! num ref-big ! true r> 0 ?do i printed? and i reprinted? and loop ;
T{ s" 1" 40 print-swept? s" 123456789" 40 print-swept? s" 0" 10 print-swept?
   -> true true true }T
T{ s" 18446744073709551615" 40 print-swept? max-2^128 60 print-swept? -> true true }T
T{ s" 10000000000000000000000000000000000000000" 60 print-swept? -> true }T
cases-done
bye

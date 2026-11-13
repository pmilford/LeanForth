\ Run src/lib/bigint.fs on a file of integer pairs, "A B" in decimal, one
\ per line, and print for each pair the line that pinned Lean's program of
\ tests/lib/bigint_differential.py prints for it:
\   a b a+b a-b a*b a/b a%b (Int.bmod a b.natAbs) (Int.gcd a b) a.natAbs
\   a.toNat (-a) a.sign (compare a b) a^(b.natAbs % 8)
\ (compare as -1, 0 or 1). A result is decimal text, or the name of the
\ outcome of a step that failed. Every number is read with decimal>bigint
\ and printed with bigint>decimal (natural numbers with big>decimal), and
\ b's magnitude is taken in place (bigint-magnitude) for bmod and the
\ exponent. Usage, from the repository root:
\   gforth tests/lib/bigint-cases.fs -e 's" CASES" run-cases bye'
\ Test-only; global state is fine.
require ../../src/lib/bigint.fs
decimal

\ One arena of 64 MiB for all pairs; each line gives its numbers back.
create arena /big-arena allot
64 1024 * 1024 * constant arena-bytes
arena-bytes allocate throw arena-bytes arena big-arena-init
1024 1024 * constant line-max
line-max 2 + allocate throw constant line

\ Split off the first space-separated token.
: space-index ( addr u -- n )
  tuck 0 ?do dup i + c@ bl = if 2drop i unloop exit then loop drop ;
: token ( addr u -- rest-addr rest-u tok-addr tok-u )
  2dup space-index >r over r@ 2swap r> /string dup if 1 /string then 2swap ;

\ Printing results, each followed by a space.
: .failed ( x outcome -- ) nip outcome-text type space ;
: .int ( i outcome -- )
  dup ok? if drop arena bigint>decimal drop type space else .failed then ;
: .nat ( big outcome -- )
  dup ok? if drop arena big>decimal drop type space else .failed then ;
: .n ( n -- ) 0 .r space ;

variable first   variable second   \ the pair's integers
: ab ( -- a b ) first @ second @ ;
\ b.natAbs % 8 as a natural number: its lowest limb's low bits.
: exponent ( -- big )
  second @ bigint-magnitude dup @ if big-limbs @ 7 and else drop 0 then arena u>big drop ;
: ops ( -- )
  first @ outcome-ok .int  second @ outcome-ok .int
  ab arena bigint+ .int  ab arena bigint- .int  ab arena bigint* .int
  ab arena bigint-ediv .int  ab arena bigint-emod .int
  ab bigint-magnitude arena bigint-bmod .int  ab arena bigint-gcd .nat
  first @ arena bigint-natAbs .nat  first @ arena bigint-toNat .nat
  first @ arena bigint-negate .int  first @ bigint-sign .n  ab bigint-compare .n
  first @ exponent arena bigint-pow .int ;

\ The next operand; false when it is not an integer (its outcome printed).
: operand ( addr u -- rest-addr rest-u i true | false )
  token arena decimal>bigint dup ok? if drop true exit then
  >r drop 2drop r> outcome-text type false ;
: pair ( addr u -- )
  operand 0= if exit then first ! operand 0= if exit then second ! 2drop ops ;

\ Each line is sent at once, so that a run with a planted fault can be
\ stopped at its first wrong line.
[defined] outfile-id [if]
: flush-line ( -- ) outfile-id flush-file drop ;
[else]
: flush-line ( -- ) ;
[then]
: run-line ( addr u -- ) arena big-mark >r pair cr flush-line r> arena big-release drop ;
: run-cases ( c-addr u -- )
  r/o open-file throw >r
  begin line line-max r@ read-line throw while line swap run-line repeat drop
  r> close-file throw ;

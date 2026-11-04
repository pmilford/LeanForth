\ Every addition of IR 0.2 (ADR 0019 Amendment 1) at least once, for the
\ golden IR tests/program/ir/ir-0.2.ir, which the program words write and
\ tests/reference/program-ir.lean prints: the primitives LSHIFT and -ROT,
\ every output word, Forth-2012's number prefixes and 32-bit literals, and
\ a word defined again, whose second version calls its first. It loads in
\ plain Forth too (on a Forth without -ROT, after src/lib/portability.fs).
$10000 dup * 1- constant mask32   \ 2^32 - 1 on cells of 33 bits or more
: rotl1 ( x -- x' ) dup 1 lshift swap 31 rshift or mask32 and ;
: shuffle ( a b c -- c a b ) -rot ;
: literals ( -- a b c d e f ) #10 $-10 %101 'a' 4294967295 -2147483648 ;
: show ( n -- n ) dup . dup u. cr dup emit space 2 spaces .s ." text" ;
: show ( n -- n ) s" <" type show ."   >" ;

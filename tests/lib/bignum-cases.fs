\ Run src/lib/bignum.fs on a file of cases, one per line, and print one
\ result line per case, for tests/lib/bignum_differential.py, which
\ compares them with Python's integers and a sample with pinned Lean:
\   OP A B    OP one of add sub mul div mod gcd and or xor shl shr pow
\             beq ble cmp; A and B in decimal
\   dec A     A read and printed again
\   limit N   the arena's limit becomes N bits; prints "limit"
\ A result is decimal digits, true or false (beq, ble), -1, 0 or 1 (cmp),
\ or the name of the outcome (full, invalid) of the first step that failed.
\ Usage, from the repository root:
\   gforth tests/lib/bignum-cases.fs -e 's" CASES" run-cases bye'
\ A planted fault: the Python script loads a changed copy of the library
\ first (gforth COPY/bignum.fs tests/lib/bignum-cases.fs ...), which this
\ file then uses instead of the original. Test-only; global state is fine.
[undefined] big+ [if] require ../../src/lib/bignum.fs [then]
decimal

\ One arena of 64 MiB for all cases; each case gives its numbers back.
create arena /big-arena allot
64 1024 * 1024 * constant arena-bytes
arena-bytes allocate throw arena-bytes arena big-arena-init
4 1024 * 1024 * constant line-max
line-max 2 + allocate throw constant line

\ Split off the first space-separated token.
: space-index ( addr u -- n )
  tuck 0 ?do dup i + c@ bl = if 2drop i unloop exit then loop drop ;
: token ( addr u -- rest-addr rest-u tok-addr tok-u )
  2dup space-index >r over r@ 2swap r> /string dup if 1 /string then 2swap ;

\ Printing results.
: .big ( big -- ) arena big>decimal ok? if type else 2drop ." print-failed" then ;
: show ( big outcome -- ) dup ok? if drop .big else nip outcome-text type then ;
: .flag ( flag -- ) if ." true" else ." false" then ;

\ The next operand; on failure its outcome is printed.
: operand ( addr u -- rest-addr rest-u big true | false )
  token arena decimal>big dup ok? if drop true exit then
  >r drop 2drop r> outcome-text type false ;
: operands ( addr u -- a b true | false )
  operand 0= if false exit then
  >r operand if nip nip r> swap true else r> drop false then ;
: binary-case ( addr u xt -- ) >r operands if arena r> execute show else r> drop then ;

\ The operations, by name, in a word list of their own.
wordlist constant case-ops
get-current case-ops set-current
: add ( addr u -- ) ['] big+ binary-case ;
: sub ( addr u -- ) ['] big- binary-case ;
: mul ( addr u -- ) ['] big* binary-case ;
: div ( addr u -- ) ['] big/ binary-case ;
: mod ( addr u -- ) ['] big-mod binary-case ;
: gcd ( addr u -- ) ['] big-gcd binary-case ;
: and ( addr u -- ) ['] big-and binary-case ;
: or ( addr u -- ) ['] big-or binary-case ;
: xor ( addr u -- ) ['] big-xor binary-case ;
: shl ( addr u -- ) ['] big-lshift binary-case ;
: shr ( addr u -- ) ['] big-rshift binary-case ;
: pow ( addr u -- ) ['] big-pow binary-case ;
: beq ( addr u -- ) operands if big= .flag then ;
: ble ( addr u -- ) operands if big<= .flag then ;
: cmp ( addr u -- ) operands if big-compare 0 .r then ;
: dec ( addr u -- ) operand if nip nip .big then ;
: limit ( addr u -- )
  token 2swap 2drop 0 0 2swap >number 2drop drop arena big-limit! ." limit" ;
set-current

\ Each line is sent at once, so that the Python script can stop a run with
\ a planted fault at its first wrong line (a broken library may then loop).
[defined] outfile-id [if]
: flush-line ( -- ) outfile-id flush-file drop ;
[else]
: flush-line ( -- ) ;
[then]
: run-line ( addr u -- )
  arena big-mark >r token case-ops search-wordlist 0= abort" unknown operation"
  execute cr flush-line r> arena big-release drop ;
: run-cases ( c-addr u -- )
  r/o open-file throw >r
  begin line line-max r@ read-line throw while line swap run-line repeat drop
  r> close-file throw ;

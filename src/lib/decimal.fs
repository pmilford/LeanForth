\ Decimal numbers as text, and decimal text as numbers, whatever BASE is.
\ A general tool with no Lean knowledge; untrusted. Written for the dozen
\ modules that each saved BASE, switched to decimal, formatted or read a
\ number and restored BASE by hand, most of them losing BASE when a THROW
\ came out in between (library audit 2026-11-13, action 7; plan 9.4.8d),
\ and for json.fs's digit reader, moved here.
\
\ The method. in-base runs a word with BASE set under CATCH and restores
\ BASE on both paths, passing a THROW on; in-decimal is in-base with ten.
\ The text words build pictured numeric output (<# #s #>) inside in-base,
\ so their text is the host's transient pictured-output buffer: valid
\ until the next pictured output (another number formatted, by these
\ words or by . or .r); copy it to keep it. u>hex writes hexadecimal
\ digits as the host's # does (upper case on Gforth). Reading is by hand,
\ digit by digit, never by >NUMBER, so BASE does not matter to it:
\ digits>u gives the value of a run of decimal digits when it fits in a
\ nonnegative cell, leading zeros skipped, decimal>u the value modulo the
\ cell size (unchecked: digits only); skip-zeros drops leading zeros.
\ decimal-digit? tests one character; hex-char is one lower-case digit
\ of a number from 0 to 15 and hex-byte! the two of a byte, for
\ fixed-width hexadecimal (JSON escapes, digests), with no pictured output.
\ type-right pads text to a column's width, for tables.
\
\ Genericity. Any cell or double cell, signed or unsigned; any word under
\ in-decimal.
\ Cost: linear in the digits; nothing allocated; no state.
\
\ Example:
\   hex ff u>decimal type  -10 n>decimal type  decimal   \ 255-16
\   255 u>hex type  s" 007" skip-zeros type               \ FF7
\   s" 00000000000000000000042" digits>u . .            \ -1 42
\   s" 1234" digits>u . .                              \ -1 1234
\   s" 99999999999999999999999" digits>u .             \ 0: too large
\   : dot ( n -- ) 0 .r ;   hex 100 ' dot in-decimal   \ 256, BASE still hex
\   s" 42x" decimal>number type d.  s" 042" decimal-digits?   \ x42 -1
\
\ Interface: in-base in-decimal u>decimal n>decimal ud>decimal d>decimal
\ .decimal type-right u>hex decimal>number decimal-digits?
\ decimal-digit? hex-char hex-byte! skip-zeros digits>u decimal>u
\ cell-digits. State:
\ none. Requires portability.fs and module.fs; helpers private in
\ lf-lib-private (ADR 0010). Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./module.fs

lf-lib-private module-open

lf-lib set-current
\ Run xt with BASE base, or decimal, then give BASE back as it was, also
\ when xt throws (the THROW is then passed on). Precondition: base is 2 to
\ 36, as BASE must be for the standard's number conversion (with base 1
\ #s never ends; base 0 divides by zero).
: in-base ( i*x xt base -- j*x ) base @ >r base ! catch r> base ! throw ;
: in-decimal ( i*x xt -- j*x ) 10 in-base ;
lf-lib-private set-current
: ud>text ( ud -- c-addr u ) <# #s #> ;
: d>text ( d -- c-addr u ) dup >r dabs <# #s r> sign #> ;

lf-lib set-current
\ Decimal digits, with a leading minus sign for a negative signed number,
\ in the pictured-output buffer (see the header).
: ud>decimal ( ud -- c-addr u ) ['] ud>text in-decimal ;
: u>decimal ( u -- c-addr u ) 0 ud>decimal ;
: d>decimal ( d -- c-addr u ) ['] d>text in-decimal ;
: n>decimal ( n -- c-addr u ) s>d d>decimal ;
\ Print n in decimal, with no space after it.
: .decimal ( n -- ) n>decimal type ;
\ Columns: text right-aligned in width characters (text longer than
\ width is printed whole), for tables of numbers.
: type-right ( c-addr u width -- ) over - 0 max spaces type ;
\ Hexadecimal digits of an unsigned cell, in the pictured-output buffer.
: u>hex ( u -- c-addr u ) 0 ['] ud>text 16 in-base ;
\ >NUMBER from zero in decimal: the digits' value (modulo a double cell)
\ and the text after them.
: decimal>number ( c-addr u -- ud c-addr' u' ) 0 0 2swap ['] >number in-decimal ;
\ Whether c-addr u is one or more decimal digits and nothing else.
: decimal-digits? ( c-addr u -- flag ) dup 0> >r decimal>number nip nip nip 0= r> and ;
\ Whether the character c is a decimal digit, 0 to 9.
: decimal-digit? ( c -- flag ) [char] 0 - 10 u< ;
\ The lower-case hexadecimal digit of n, 0 to 15 (unchecked: other n give
\ other characters).
: hex-char ( n -- c ) dup 10 < if [char] 0 else [char] a 10 - then + ;
\ The two lower-case hexadecimal digits of a byte (0 to 255), high first,
\ stored at c-addr and c-addr+1.
: hex-byte! ( byte c-addr -- )
  over 4 rshift hex-char over c! swap 15 and hex-char swap char+ c! ;
lf-lib-private set-current

\ Decimal digits of a nonnegative number.
: decimal-width ( u -- n ) 0 swap begin swap 1+ swap 10 / dup 0= until drop ;
lf-lib set-current
\ Decimal digits of the largest cell, computed once.
max-n decimal-width constant cell-digits
\ The text after its leading zeros: empty for zeros only.
: skip-zeros ( addr u -- addr' u' )
  begin dup if over c@ [char] 0 = else false then while 1 /string repeat ;
\ The value of decimal digits modulo the cell size: exact whenever it fits
\ in an unsigned cell, which is always so for fewer digits than max-n has.
\ Unchecked: addr u holds only decimal digits.
: decimal>u ( addr u -- u ) 0 swap 0 ?do 10 * over i + c@ [char] 0 - + loop nip ;
lf-lib-private set-current
\ Ten times u plus the digit c, when that fits in a nonnegative cell.
: digit+ ( u c -- u' true | false )
  [char] 0 - 2dup max-n swap - 10 / > if 2drop false exit then swap 10 * + true ;
\ The value of digits without leading zeros, when it fits.
: unpadded>u ( addr u -- u true | false )
  dup cell-digits < if decimal>u true exit then dup cell-digits > if 2drop false exit then
  1- 2dup decimal>u -rot + c@ digit+ ;
lf-lib set-current
\ The value of decimal digits that fit in a nonnegative cell, however
\ many leading zeros come first; false when larger. Fewer digits than
\ cell-digits are read at once. Unchecked: addr u holds only decimal
\ digits (none reads as 0).
: digits>u ( addr u -- u true | false )
  dup cell-digits < if decimal>u true exit then skip-zeros unpadded>u ;

module-close
base !   \ the BASE this file was loaded with

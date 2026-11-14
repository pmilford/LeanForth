\ Decimal numbers as text, and decimal text as numbers, whatever BASE is.
\ A general tool with no Lean knowledge; untrusted. Written for the dozen
\ modules that each saved BASE, switched to decimal, formatted or read a
\ number and restored BASE by hand, most of them losing BASE when a THROW
\ came out in between (library audit 2026-11-13, action 7; plan 9.4.8d),
\ and for json.fs's digit reader, moved here.
\
\ The method. in-decimal runs a word with BASE decimal under CATCH and
\ restores BASE on both paths, passing a THROW on. The text words build
\ pictured numeric output (<# #s #>) inside in-decimal, so their text is
\ the host's transient pictured-output buffer: valid until the next
\ pictured output (another number formatted, by these words or by . or
\ .r); copy it to keep it. Reading is by hand, digit by digit, never by
\ >NUMBER, so BASE does not matter to it: digits>u gives the value of a
\ run of decimal digits when it fits in a nonnegative cell, decimal>u the
\ value modulo the cell size (unchecked: digits only).
\
\ Genericity. Any cell or double cell, signed or unsigned; any word under
\ in-decimal.
\ Cost: linear in the digits; nothing allocated; no state.
\
\ Example:
\   hex ff u>decimal type  -10 n>decimal type  decimal   \ 255-16
\   s" 1234" digits>u . .                              \ -1 1234
\   s" 99999999999999999999999" digits>u .             \ 0: too large
\   : dot ( n -- ) 0 .r ;   hex 100 ' dot in-decimal   \ 256, BASE still hex
\   s" 42x" decimal>number type d.  s" 042" decimal-digits?   \ x42 -1
\
\ Interface: in-decimal u>decimal n>decimal ud>decimal d>decimal .decimal
\ decimal>number decimal-digits? digits>u decimal>u cell-digits. State:
\ none. Requires portability.fs and module.fs; helpers private in
\ lf-lib-private (ADR 0010). Loads in decimal whatever BASE is, then
\ restores it.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ./portability.fs
require ./module.fs

lf-lib-private module-open

lf-lib set-current
\ Run xt with BASE decimal, then give BASE back as it was, also when xt
\ throws (the THROW is then passed on).
: in-decimal ( i*x xt -- j*x ) base @ >r decimal catch r> base ! throw ;
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
\ >NUMBER from zero in decimal: the digits' value (modulo a double cell)
\ and the text after them.
: decimal>number ( c-addr u -- ud c-addr' u' ) 0 0 2swap ['] >number in-decimal ;
\ Whether c-addr u is one or more decimal digits and nothing else.
: decimal-digits? ( c-addr u -- flag ) dup 0> >r decimal>number nip nip nip 0= r> and ;
lf-lib-private set-current

\ Decimal digits of a nonnegative number.
: decimal-width ( u -- n ) 0 swap begin swap 1+ swap 10 / dup 0= until drop ;
lf-lib set-current
\ Decimal digits of the largest cell, computed once.
max-n decimal-width constant cell-digits
\ The value of decimal digits modulo the cell size: exact whenever it fits
\ in an unsigned cell, which is always so for fewer digits than max-n has.
\ Unchecked: addr u holds only decimal digits.
: decimal>u ( addr u -- u ) 0 swap 0 ?do 10 * over i + c@ [char] 0 - + loop nip ;
lf-lib-private set-current
\ Ten times u plus the digit c, when that fits in a nonnegative cell.
: digit+ ( u c -- u' true | false )
  [char] 0 - 2dup max-n swap - 10 / > if 2drop false exit then swap 10 * + true ;
lf-lib set-current
\ The value of decimal digits that fit in a nonnegative cell; false when
\ larger. Unchecked: addr u holds only decimal digits.
: digits>u ( addr u -- u true | false )
  dup cell-digits < if decimal>u true exit then dup cell-digits > if 2drop false exit then
  1- 2dup decimal>u -rot + c@ digit+ ;

module-close
base !   \ the BASE this file was loaded with

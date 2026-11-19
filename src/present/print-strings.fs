\ String literals in the printer (plan task 5.2.3, strings): a string
\ literal leaf (core/string-literals.fs) prints as Lean 4.35.0 prints it,
\ with String.quote (Init/Data/Repr.lean; Char.quoteCore, inString):
\ between double quotes, the line feed, tab, backslash and double quote as
\ \n, \t, \\ and \", every other character below 32 and DEL as \x and two
\ lowercase hexadecimal digits (a carriage return as \x0d), every other
\ character as itself. One addition: a character that lib/text-rule.fs
\ bans (a control or format character, such as a bidirectional one, a
\ line or paragraph separator), which Lean writes as itself, is written as
\ \u and four hexadecimal digits when it is below U+10000 (every
\ bidirectional control is), Lean's own escape for the same character, and
\ above it (tag characters, musical format characters) as \u{X}, which
\ Lean's syntax lacks, so that a literal cannot end a
\ line or reorder the text it is printed in, in any mode.
\ In LaTeX the quoted text is the argument of \texttt, its characters that
\ are special in text mode escaped. Bytes that are no UTF-8 character
\ (only a corrupted leaf holds them) are invalid. Untrusted presentation
\ code. Requires print-job.fs and latex-text.fs. No state.

require ./print-job.fs
require ./latex-text.fs
require ../lib/bytes.fs
require ../lib/decimal.fs
require ../lib/text-rule.fs
require ../core/string-literals.fs

\ Text in the current mode: in LaTeX a byte at a time, as latex-text.fs's
\ lf-tex-text-form writes it; else as it is.
: lf-pq-tex-byte ( c-addr -- )
  dup c@ lf-tex-text-form if lf-pp-emit drop else 1 lf-pp-emit then ;
: lf-pq-out ( c-addr u -- )
  lf-pp-latex? 0= if lf-pp-emit exit then
  over + swap ?do i lf-pq-tex-byte loop ;

\ Escapes: a backslash and letters; n lowercase hexadecimal digits of u.
: lf-pq-letter ( c-addr u -- ) s" \" lf-pq-out lf-pq-out ;
: lf-pq-digit ( u -- c-addr 1 ) $f and s" 0123456789abcdef" drop + 1 ;
: lf-pq-hex ( u n -- )
  begin dup while 1- 2dup 4 * rshift lf-pq-digit lf-pq-out repeat 2drop ;
: lf-pq-coded ( code c-addr u n -- ) >r lf-pq-letter r> lf-pq-hex ;

\ One character, its bytes c-addr n and its code point.
: lf-pq-control? ( code -- flag ) dup 32 < swap 127 = or ;
\ A banned character: \u and four digits below U+10000; above, where
\ Lean's string syntax has no escape (\u takes four digits, and a
\ surrogate pair reads as two NULs), \u{X} as names write it (X in
\ capital hexadecimal), which Lean refuses to read rather than reads as
\ another string (review F4).
: lf-pq-wide ( code -- ) s" u{" lf-pq-letter u>hex lf-pq-out s" }" lf-pq-out ;
: lf-pq-banned ( code -- ) dup $10000 < if s" u" 4 lf-pq-coded else lf-pq-wide then ;
: lf-pq-other ( c-addr n code -- code )
  dup lf-pq-control? if >r 2drop r@ s" x" 2 lf-pq-coded r> exit then
  dup tr-banned? if >r 2drop r@ lf-pq-banned r> exit then
  >r lf-pq-out r> ;
: lf-pq-char ( c-addr n code -- )
  case 10 of 2drop s" n" lf-pq-letter endof
    9 of 2drop s" t" lf-pq-letter endof
    92 of lf-pq-letter endof
    34 of lf-pq-letter endof
    lf-pq-other endcase ;
\ The characters of the text; false at bytes that are no UTF-8 character.
: lf-pq-chars ( c-addr u -- flag )
  begin dup while
    2dup utf8-length ?dup 0= if 2drop false exit then
    >r over r@ 2dup utf8-decode lf-pq-char r> /string
  repeat 2drop true ;

: lf-pq-quote ( -- ) s\" \"" lf-pq-out ;
\ The literal leaf, quoted: ok, or invalid (the sink has had part of it).
: lf-pp-string ( leaf -- outcome )
  lf-pp-latex? if s" \texttt{" lf-pp-emit then
  lf-pq-quote lf-str-text lf-pq-chars lf-pq-quote
  lf-pp-latex? if s" }" lf-pp-emit then
  flag>outcome ;

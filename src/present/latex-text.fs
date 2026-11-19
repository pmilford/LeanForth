\ LaTeX spelling of identifiers for the printer's LaTeX mode. A variable
\ prints in math italic: one letter as itself, a Greek letter as its
\ command (α as \alpha), a longer name as \mathit{...}; a trailing _2 or ₂
\ becomes the subscript _{2}, trailing primes stay primes. A constant
\ prints upright as \mathsf{...}. The characters _ # % & { } $ ^ ~ \
\ are escaped. A Greek letter or a subscript digit counts only as a whole
\ UTF-8 character; other valid characters are written as they are. A
\ character that lib/text-rule.fs bans (controls, format characters such as
\ bidirectional ones, line and paragraph separators) is written as
\ \backslash{}u\{X\} (its code point in hexadecimal) and a byte that starts no
\ UTF-8 character as \backslash{}x\{X\}, so that a name can never put a line end
\ or a reordering into the LaTeX (or into the plain text it is part of). Text
\ is examined a character at a time, with COMPARE and SEARCH for the symbol
\ tables. The escaping serves two modes: math mode here (the printer's
\ lf-pp-emit, \backslash{}) and text mode in statement-forms.fs (its own
\ sink and bytes, \textbackslash{}); a mode is a read-only record of its
\ sink, byte step and backslash. Untrusted presentation code. Requires
\ print-job.fs. No state.

require ./print-job.fs
require ../lib/bytes.fs
require ../lib/decimal.fs
require ../lib/text-rule.fs

\ Escaping, one byte at a time.
: lf-tex-in? ( c-addr hay u -- c-addr flag ) 2>r dup 1 2r> 2swap search nip nip ;
: lf-tex-is? ( c-addr c-addr2 u2 -- c-addr flag ) 2>r dup 1 2r> compare 0= ;
: lf-tex-byte ( c-addr -- )
  s" _#%&{}$" lf-tex-in? if s" \" lf-pp-emit 1 lf-pp-emit exit then
  s" ^" lf-tex-is? if drop s" \hat{}" lf-pp-emit exit then
  s" ~" lf-tex-is? if drop s" \sim{}" lf-pp-emit exit then
  s" \" lf-tex-is? if drop s" \backslash{}" lf-pp-emit exit then 1 lf-pp-emit ;
\ lf-tex-text-form ( char -- c-addr u true | false ): one ASCII character
\ in LaTeX's text mode (string literals, print-strings.fs; the statement
\ forms, statement-forms.fs; review R10): _ # % & { } $ after a backslash,
\ \ ^ ~ by name; false for any other character.
\ The slashed characters, and their forms last first: the character that
\ byte-scan finds with u bytes left of the table has its form at 2(u-1).
: lf-tex-plain ( -- c-addr u ) s" _#%&{}$" ;
: lf-tex-slashed ( u -- c-addr 2 ) 1- 2* s" \$\}\{\&\%\#\_" drop + 2 ;
: lf-tex-left ( char c-addr u -- u' ) rot byte-scan nip ;
: lf-tex-named ( char -- c-addr u true | false )
  dup [char] \ = if drop s" \textbackslash{}" true exit then
  dup [char] ^ = if drop s" \textasciicircum{}" true exit then
  [char] ~ = if s" \textasciitilde{}" true else false then ;
: lf-tex-text-form ( char -- c-addr u true | false )
  dup lf-tex-plain lf-tex-left ?dup if nip lf-tex-slashed true exit then lf-tex-named ;
\ The same for the byte at c-addr.
: lf-tex-text-byte ( c-addr -- c-addr' u true | false ) c@ lf-tex-text-form ;
\ A mode: its sink ( c-addr u -- ), its step for a one-byte character
\ ( c-addr -- ) and its backslash ( -- c-addr u ).
begin-structure /lf-tex-mode
  field: lf-tex-sink
  field: lf-tex-one
  field: lf-tex-slash
end-structure
: lf-tex-out ( c-addr u mode -- ) lf-tex-sink @ execute ;
\ A code in hexadecimal after the mode's backslash and the letter text
\ c-addr u2 (u\{ or x\{), closed by \}.
: lf-tex-code ( u c-addr u2 mode -- )
  >r r@ lf-tex-slash @ execute r@ lf-tex-out r@ lf-tex-out u>hex r@ lf-tex-out
  s" \}" r> lf-tex-out ;
: lf-tex-bad ( c-addr mode -- ) >r c@ s" x\{" r> lf-tex-code ;
\ « and », which name-text.fs puts around a name part that is no
\ identifier, as math symbols in either mode: LaTeX's default font
\ encoding (OT1) has no guillemets.
: lf-tex-angle? ( code -- flag ) dup $ab = swap $bb = or ;
: lf-tex-angle ( code -- c-addr u )
  $ab = if s" \ensuremath{\ll}" else s" \ensuremath{\gg}" then ;
\ A character of n > 1 bytes at c-addr: the bytes it takes and its text.
: lf-tex-wide ( c-addr n code -- n c-addr' u' )
  dup lf-tex-angle? if nip nip 2 swap lf-tex-angle else drop tuck then ;
\ The character at c-addr, u bytes left, written in the mode; the bytes it
\ took.
: lf-tex-step ( c-addr u mode -- n )
  >r 2dup utf8-length dup 0= if 2drop r> lf-tex-bad 1 exit then nip
  2dup utf8-decode dup tr-banned? if s" u\{" r> lf-tex-code nip exit then
  over 1 = if 2drop r> lf-tex-one @ execute 1 exit then
  lf-tex-wide r> lf-tex-out ;
: lf-tex-text ( c-addr u mode -- )
  >r begin dup while 2dup r@ lf-tex-step /string repeat 2drop r> drop ;
: lf-tex-backslash ( -- c-addr u ) s" \backslash{}" ;
create lf-tex-math ' lf-pp-emit , ' lf-tex-byte , ' lf-tex-backslash ,
: lf-tex-escaped ( c-addr u -- ) lf-tex-math lf-tex-text ;

\ Greek letters: a name that is exactly one of them prints as its command.
: lf-tex-greek-letters ( -- c-addr u ) s" αβγδεζηθικλμνξπρστυφχψω" ;
\ Their command names, in the same order, each followed by one space.
: lf-tex-greek-low ( -- c-addr u )
  s" alpha beta gamma delta epsilon zeta eta theta iota kappa " ;
: lf-tex-greek-high ( -- c-addr u )
  s" lambda mu nu xi pi rho sigma tau upsilon phi chi psi omega " ;
: lf-tex-skip ( c-addr u -- c-addr' u' ) s"  " search drop 1 /string ;
: lf-tex-word ( c-addr u i -- c-addr' u' )
  0 ?do lf-tex-skip loop 2dup s"  " search drop nip - ;
: lf-tex-greek-name ( i -- c-addr u )
  dup 10 < if lf-tex-greek-low else 10 - lf-tex-greek-high then rot lf-tex-word ;
\ A match that SEARCH found u-left bytes before the end of a table of
\ u-table bytes, whose characters are width bytes each: the index of the
\ character, when the match starts at a character boundary. The first
\ byte of a whole UTF-8 character occurs in such a table only at a
\ boundary, so a first match elsewhere (invalid UTF-8 such as the bytes
\ B1 CE, the end of α and the start of β) is no character of the table.
: lf-tex-index ( u-table u-left width -- i true | false )
  >r - r> /mod swap if drop false else true then ;
\ Each letter is two bytes.
: lf-tex-letter-at ( u-left -- i true | false )
  lf-tex-greek-letters nip swap 2 lf-tex-index ;
: lf-tex-greek ( c-addr u -- i true | false )
  dup 2 <> if 2drop false exit then 2>r lf-tex-greek-letters 2r> search
  if nip lf-tex-letter-at else 2drop false then ;
: lf-tex-greek-out ( i -- ) s" \" lf-pp-emit lf-tex-greek-name lf-pp-emit ;

\ The tail of a text: does it end with a prime, with an ASCII digit, with
\ a subscript digit (three bytes each, giving its value)?
\ Unchecked: n <= u.
: lf-tex-tail ( c-addr u n -- c-addr' n ) >r + r@ - r> ;
: lf-tex-prime-end? ( c-addr u -- flag ) 1 lf-tex-tail s" '" compare 0= ;
: lf-tex-digit-end? ( c-addr u -- flag )
  dup 0> if 1 lf-tex-tail drop s" 0123456789" lf-tex-in? nip else 2drop false then ;
: lf-tex-subscripts ( -- c-addr u ) s" ₀₁₂₃₄₅₆₇₈₉" ;
: lf-tex-sub-at ( u-left -- d true | false ) lf-tex-subscripts nip swap 3 lf-tex-index ;
: lf-tex-sub-end ( c-addr u -- d true | false )
  dup 3 < if 2drop false exit then 3 lf-tex-tail 2>r lf-tex-subscripts 2r> search
  if nip lf-tex-sub-at else 2drop false then ;
: lf-tex-sub? ( c-addr u -- flag ) lf-tex-sub-end dup if nip then ;

\ Counting trailing primes, ASCII digits and subscript digits; each count
\ leaves at least one byte of base.
\ The trailing characters for which xt ( c-addr u -- flag ) holds at the
\ end, cut off while more than one character is left, and their number.
: lf-tex-trailing ( c-addr u xt -- c-addr u' n )
  over >r >r begin dup 1 > while 2dup r@ execute while 1- repeat then
  r> drop r> over - ;
: lf-tex-primes ( c-addr u -- c-addr u' n ) ['] lf-tex-prime-end? lf-tex-trailing ;
: lf-tex-digits ( c-addr u -- c-addr u' k ) ['] lf-tex-digit-end? lf-tex-trailing ;
: lf-tex-subs ( c-addr u -- c-addr u' k )
  0 >r begin dup 3 > while 2dup lf-tex-sub? while 3 - r> 1+ >r repeat then r> ;

\ The base of a variable name.
: lf-tex-base ( c-addr u -- )
  2dup lf-tex-greek if nip nip lf-tex-greek-out exit then
  dup 1 = if lf-tex-escaped exit then
  s" \mathit{" lf-pp-emit lf-tex-escaped s" }" lf-pp-emit ;
: lf-tex-open-sub ( -- ) s" _{" lf-pp-emit ;
: lf-tex-close ( -- ) s" }" lf-pp-emit ;
\ name_12: base, then the digits as a subscript.
: lf-tex-underscored? ( c-addr u k -- flag )
  dup 0> >r over swap - 1- dup 0> r> and
  if nip + s" _" lf-tex-is? nip else 2drop drop false then ;
: lf-tex-ascii-sub ( c-addr u k -- )
  >r 2dup + r@ - r@ 2swap r> - 1- lf-tex-base lf-tex-open-sub lf-pp-emit lf-tex-close ;
\ name₁₂: base, then the subscript digits' values.
: lf-tex-unisub-out ( c-addr k -- )
  lf-tex-open-sub 0 ?do dup i 3 * + 3 lf-tex-sub-end drop lf-pp-number loop drop
  lf-tex-close ;
: lf-tex-uni-sub ( c-addr u k -- ) >r 2dup lf-tex-base + r> lf-tex-unisub-out ;
: lf-tex-stem ( c-addr u -- )
  2dup lf-tex-digits nip nip >r 2dup r@ lf-tex-underscored? r> swap
  if lf-tex-ascii-sub exit then drop
  2dup lf-tex-subs ?dup if 2>r 2drop 2r> lf-tex-uni-sub else 2drop lf-tex-base then ;

\ A bound variable's or universe parameter's display name.
: lf-tex-ident ( c-addr u -- )
  lf-tex-primes >r lf-tex-stem r> 0 ?do s" '" lf-pp-emit loop ;
\ A constant's name, already spelled out with its dots.
: lf-tex-constant ( c-addr u -- ) s" \mathsf{" lf-pp-emit lf-tex-escaped lf-tex-close ;

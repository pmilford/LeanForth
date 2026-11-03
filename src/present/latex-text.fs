\ LaTeX spelling of identifiers for the printer's LaTeX mode. A variable
\ prints in math italic: one letter as itself, a Greek letter as its
\ command (α as \alpha), a longer name as \mathit{...}; a trailing _2 or ₂
\ becomes the subscript _{2}, trailing primes stay primes. A constant
\ prints upright as \mathsf{...}. The characters _ # % & { } $ ^ ~ \
\ are escaped. Text is examined as one-byte slices with COMPARE and
\ SEARCH, never byte by byte. Untrusted presentation code. Requires
\ print-job.fs. No state.

require ./print-job.fs

\ Escaping, one byte at a time.
: lf-tex-in? ( c-addr hay u -- c-addr flag ) 2>r dup 1 2r> 2swap search nip nip ;
: lf-tex-is? ( c-addr c-addr2 u2 -- c-addr flag ) 2>r dup 1 2r> compare 0= ;
: lf-tex-byte ( c-addr -- )
  s" _#%&{}$" lf-tex-in? if s" \" lf-pp-emit 1 lf-pp-emit exit then
  s" ^" lf-tex-is? if drop s" \hat{}" lf-pp-emit exit then
  s" ~" lf-tex-is? if drop s" \sim{}" lf-pp-emit exit then
  s" \" lf-tex-is? if drop s" \backslash{}" lf-pp-emit exit then 1 lf-pp-emit ;
: lf-tex-escaped ( c-addr u -- ) 0 ?do dup i + lf-tex-byte loop drop ;

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
\ Each letter is two bytes, and a match can only start on a letter.
: lf-tex-letter-at ( c-addr u -- i ) nip lf-tex-greek-letters nip swap - 2/ ;
: lf-tex-greek ( c-addr u -- i true | false )
  dup 2 <> if 2drop false exit then 2>r lf-tex-greek-letters 2r> search
  if lf-tex-letter-at true else 2drop false then ;
: lf-tex-greek-out ( i -- ) s" \" lf-pp-emit lf-tex-greek-name lf-pp-emit ;

\ The tail of a text: does it end with a string, with an ASCII digit, with
\ a subscript digit (three bytes each, giving its value)?
: lf-tex-ends? ( c-addr u c-addr2 u2 -- flag )
  2swap 2 pick over > if 2drop 2drop false exit then + over - over compare 0= ;
: lf-tex-digit-end? ( c-addr u -- flag )
  dup 0> if + 1- s" 0123456789" lf-tex-in? nip else 2drop false then ;
: lf-tex-subscripts ( -- c-addr u ) s" ₀₁₂₃₄₅₆₇₈₉" ;
: lf-tex-sub-end ( c-addr u -- d true | false )
  dup 3 < if 2drop false exit then + 3 - 3 2>r lf-tex-subscripts 2r> search
  if nip lf-tex-subscripts nip swap - 3 / true else 2drop false then ;
: lf-tex-sub? ( c-addr u -- flag ) lf-tex-sub-end dup if nip then ;

\ Counting trailing primes, ASCII digits and subscript digits; each count
\ leaves at least one byte of base.
: lf-tex-primes ( c-addr u -- c-addr u' n )
  0 >r begin dup 1 > while 2dup s" '" lf-tex-ends? while 1- r> 1+ >r repeat then r> ;
: lf-tex-digits ( c-addr u -- c-addr u' k )
  0 >r begin dup 1 > while 2dup lf-tex-digit-end? while 1- r> 1+ >r repeat then r> ;
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

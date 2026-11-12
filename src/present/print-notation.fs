\ Mathematical notation for the term printer (plan task 4.4.3): when
\ lf-print-notation! is on, an application of a constant in the notation
\ table (notation-table.fs) prints as the table says -- a + b, a = b, ¬p,
\ ∃ x y, p, 3, n + 1, ℕ -- in Lean's own precedences and parentheses, in the
\ printer's four modes (Lean's Unicode, ASCII, LaTeX, mathematical text).
\ An application that does not fit its row (another number of arguments, a
\ numeral that is no literal, a mode the row has no spelling for) prints as
\ the kernel's term does, so turning notation on never fails a print that
\ would succeed. The arguments in the row's operand places are the only ones
\ shown: implicit and instance arguments of the notation's constant are
\ hidden, as Lean's delaborator hides them. Two minus signs in a row are
\ written apart, - -a, as Lean writes them (--a would start a comment).
\ Untrusted presentation code: the checker never loads it, a spelling is no
\ evidence of anything, and the kernel form stays available (notation off).
\ Requires term-printer.fs, which calls the two words installed at the end.
\ State: none of its own; the flag is the printer record's (print-job.fs).
\ Depth (plan task 6.2.0): an operand is a visit of the print's frames, a
\ part of a visit that waits for it keeps its cells on the frames' stack.

require ./term-printer.fs
require ./notation-table.fs

\ ---- Which row, if any ---------------------------------------------------
\ The row for a constant node, or 0: its name spelled in the name pool,
\ taken back at once (the mark waits on the data stack; a THROW out of a
\ print resets the pool, lf-print-reset), and looked up in the table.
: lf-pn-spell ( id -- row | 0 )
  lf-pp-used @ swap ['] lf-pp-put lf-pp-name-to dup lf-pp-pending lf-nt-find
  swap lf-pp-used ! ;
: lf-pn-head-row ( head -- row | 0 )
  dup lf-tag-constant lf-pp-is? 0= if drop 0 exit then
  lf-pp-const-name if lf-pn-spell else 0 then ;
\ The row if the application has as many arguments as the row says.
: lf-pn-sized ( row n -- row | 0 )
  over 0= if drop exit then over lf-nt-arity @ <> if drop 0 then ;
\ The row of an application's head, sized to it.
: lf-pn-sized-row ( term -- row | 0 ) lf-pp-head >r lf-pn-head-row r> lf-pn-sized ;
: lf-pn-mode-sym ( row -- c-addr u ) lf-pp-mode lf-nt-sym ;
: lf-pn-spelt? ( row -- flag ) lf-pn-mode-sym nip 0<> ;
\ The operands: the arguments in the row's places a and b.
: lf-pn-a ( term row -- arg ) lf-nt-a @ lf-pp-arg-at ;
: lf-pn-b ( term row -- arg ) lf-nt-b @ lf-pp-arg-at ;
\ A numeral's argument is a literal that fits a cell; ∃ needs a lambda.
: lf-pn-small? ( term -- flag )
  dup lf-tag-lit lf-pp-is? if lf-lit-small? else drop false then ;
: lf-pn-literal-arg ( term row -- n true | false )
  lf-pn-a dup lf-pn-small? if lf-lit-cell true else drop false then ;
: lf-pn-literal? ( term row -- flag ) lf-pn-literal-arg dup if nip then ;
: lf-pn-lambda? ( term row -- flag ) lf-pn-a lf-tag-lam lf-pp-is? ;
: lf-pn-shape ( term row -- flag )
  dup lf-nt-kind @ case
    lf-nt-numeral of lf-pn-literal? endof
    lf-nt-exists of lf-pn-lambda? endof
    >r 2drop true r> endcase ;
\ Does the row apply to the application in this mode?
: lf-pn-applies? ( term row -- flag )
  dup lf-nt-kind @ lf-nt-numeral <> over lf-pn-spelt? 0= and
  if 2drop false exit then lf-pn-shape ;
: lf-pn-fitting ( term row -- row | 0 ) dup if tuck lf-pn-applies? and else nip then ;
: lf-pn-notation ( term -- row | 0 )
  lf-print-notation? if dup lf-pn-sized-row lf-pn-fitting else drop 0 then ;
\ A numeral OfNat.ofNat _ n _: an application of the numeral row's constant
\ with the row's number of arguments; with n a literal that fits a cell,
\ its value.
: lf-pn-ofnat? ( term -- row | 0 )
  dup lf-pp-applied? if lf-pn-sized-row else drop 0 then
  dup if dup lf-nt-kind @ lf-nt-numeral = and then ;
: lf-pn-numeral? ( term -- n true | false )
  dup lf-pn-ofnat? ?dup if lf-pn-literal-arg else drop false then ;

\ ---- Positions and symbols ----------------------------------------------
\ The position of an operand: its least precedence, whether text follows
\ it, and whether the row's operands are propositions.
: lf-pn-pos ( row prec followed -- pos )
  lf-pos swap lf-nt-props @ if lf-pos-prop or then ;
: lf-pn-open? ( row pos -- flag ) swap lf-nt-prec @ false lf-pp-parens? ;
: lf-pn-op ( row -- ) lf-pn-mode-sym lf-pp-emit ;
\ The operand of a prefix notation: tight in the mathematical modes.
: lf-pn-tight? ( row -- flag )
  lf-nt-mprec @ 0<> lf-pp-mode lf-print-latex lf-print-mathtext between? and ;
: lf-pn-rprec ( row -- prec ) dup lf-pn-tight? if lf-nt-mprec else lf-nt-rprec then @ ;
\ Does text follow what the notation prints, outside a parenthesis it opened?
: lf-pn-rest-followed ( pos paren -- flag ) 0= swap lf-pos-followed? and ;
\ The operands with their positions: a OP's left one, followed by the
\ symbol; OP b's right one and OP a's, followed when rf says so.
: lf-pn-left ( term row -- arg pos ) tuck lf-pn-a swap dup lf-nt-lprec @ true lf-pn-pos ;
: lf-pn-right ( term row rf -- arg pos )
  >r tuck lf-pn-b swap dup lf-nt-rprec @ r> lf-pn-pos ;
: lf-pn-prefixed ( term row rf -- arg pos )
  >r tuck lf-pn-a swap dup lf-pn-rprec r> lf-pn-pos ;
\ Open the notation's parenthesis when its position needs one, the flag
\ waiting on the frames for lf-pp-wrapped, which closes it: rf is whether
\ text follows the notation outside it.
: lf-pn-opened ( row pos frames -- row rf frames )
  >r 2dup lf-pn-open? lf-pp-open-if dup r@ frame-save lf-pn-rest-followed r> ;

\ ---- One step per kind: ( term row pos frames -- ... frames next ) ----------
: lf-pn-invalid ( term row pos frames -- outcome frames 0 )
  >r 2drop drop outcome-invalid r> 0 ;
: lf-pn-atom ( term row pos frames -- outcome frames 0 )
  >r drop nip lf-pn-op outcome-ok r> 0 ;
: lf-pn-numeral ( term row pos frames -- outcome frames 0 )
  >r drop lf-pn-a lf-lit-cell lf-pp-number outcome-ok r> 0 ;

\ a OP b, a ^ b and n + 1 have the left operand in common. While it
\ prints, the notation's step record waits on the frames: term, row and rf
\ (whether text follows the notation outside any parenthesis it opened),
\ term on top. The rest of the notation, a part ( frames -- ... frames
\ next ) chosen by the row's kind, reads the record in place and takes it
\ back before it ends.
: lf-pn-keep ( term row rf frames -- frames ) dup >r lf-pp-save3 r> ;
: lf-pn-kept-term ( frames -- term ) 0 swap frame-pick ;
: lf-pn-kept-row ( frames -- row ) 1 swap frame-pick ;
: lf-pn-kept ( frames -- term row ) dup lf-pn-kept-term swap lf-pn-kept-row ;
: lf-pn-taken ( frames -- term row rf frames ) dup >r lf-pp-restore3 r> ;
: lf-pn-forget ( frames -- frames ) 3 over frame-drop ;
: lf-pn-done ( frames -- outcome frames 0 ) lf-pn-forget outcome-ok swap 0 ;
: lf-pn-infix ( frames -- ... frames next )
  dup lf-pn-kept-row lf-pn-op lf-pn-taken >r lf-pn-right r> ['] frame-return
  lf-pp-term-call ;
: lf-pn-suffix ( frames -- outcome frames 0 ) dup lf-pn-kept-row lf-pn-op lf-pn-done ;
\ a ^ b: b raised in mathematical text when it is a digit, in braces in
\ LaTeX, whatever b's type (Lean writes x ^ y for every HPow). The
\ superscript digits ⁰ to ⁹ lie three bytes apart in the string below: ⁰
\ (U+2070) and ⁴ to ⁹ (U+2074 to U+2079) take three bytes of UTF-8, ¹ ² ³
\ (U+00B9, U+00B2, U+00B3) two and a blank. Unchecked: d is a digit
\ (lf-pn-digit).
: lf-pn-sup-width ( d -- u ) 1 4 within if 2 else 3 then ;
: lf-pn-sups ( -- c-addr ) s" ⁰¹ ² ³ ⁴⁵⁶⁷⁸⁹" drop ;
: lf-pn-sup-digit ( d -- c-addr u ) dup 3 * lf-pn-sups + swap lf-pn-sup-width ;
: lf-pn-digit ( term row -- d true | false )
  lf-pp-mode lf-print-mathtext <> if 2drop false exit then
  lf-pn-b lf-pn-numeral? 0= if false exit then
  dup 10 u< if true else drop false then ;
: lf-pn-close ( outcome frames -- outcome frames 0 ) >r s" }" lf-pp-emit r> 0 ;
: lf-pn-exponent ( frames -- b frames ) lf-pn-taken >r drop lf-pn-b r> ;
: lf-pn-braced ( frames -- ... frames next )
  s" ^{" lf-pp-emit lf-pn-exponent 0 false lf-pos swap ['] lf-pn-close lf-pp-term-call ;
: lf-pn-raised ( frames -- ... frames next )
  s" ^" lf-pp-emit lf-pn-exponent lf-prec-arg false lf-pos swap ['] frame-return
  lf-pp-term-call ;
: lf-pn-power-text ( -- xt )
  lf-pp-mode case lf-print-latex of ['] lf-pn-braced endof
    lf-print-mathtext of ['] lf-pn-raised endof ['] lf-pn-infix swap endcase ;
: lf-pn-power ( frames -- ... frames next )
  dup lf-pn-kept lf-pn-digit if lf-pn-sup-digit lf-pp-emit lf-pn-done exit then
  lf-pn-power-text execute ;
: lf-pn-rest-xt ( kind -- xt )
  case lf-nt-suffix of ['] lf-pn-suffix endof lf-nt-power of ['] lf-pn-power endof
    ['] lf-pn-infix swap endcase ;
: lf-pn-binary-back ( outcome frames -- ... frames next )
  3 lf-pp-failed? if 0 exit then dup lf-pn-kept-row lf-nt-kind @ lf-pn-rest-xt execute ;
: lf-pn-binary-body ( term row rf frames cont -- ... frames next )
  over frame-save lf-pn-keep dup >r lf-pn-kept lf-pn-left r> ['] lf-pn-binary-back
  lf-pp-term-call ;
: lf-pn-binary ( term row pos frames -- ... frames next )
  lf-pn-opened ['] lf-pp-wrapped lf-pn-binary-body ;

\ OP a: the operand follows the symbol, after a blank when both are minus
\ signs: the symbol ends with one and the operand, unparenthesized, prints
\ by a prefix row whose symbol starts with one (Lean's - -a).
: lf-pn-minus-end? ( row -- flag ) lf-pn-mode-sym + 1- 1 s" -" compare 0= ;
: lf-pn-minus-start? ( row -- flag ) lf-pn-mode-sym drop 1 s" -" compare 0= ;
: lf-pn-prefix-row ( arg -- row | 0 )
  dup lf-pp-applied? if lf-pn-notation else drop 0 then
  dup if dup lf-nt-kind @ lf-nt-prefix = and then ;
: lf-pn-minus-first? ( arg pos -- flag )
  swap lf-pn-prefix-row ?dup 0= if drop false exit then
  dup lf-pn-minus-start? if swap lf-pn-open? 0= else 2drop false then ;
: lf-pn-gap ( arg pos row -- arg pos )
  lf-pn-minus-end? if 2dup lf-pn-minus-first? if s"  " lf-pp-emit then then ;
: lf-pn-prefix ( term row pos frames -- ... frames next )
  lf-pn-opened >r over lf-pn-op over >r lf-pn-prefixed r> lf-pn-gap
  r> ['] lf-pp-wrapped lf-pp-term-call ;

\ ∃ x y, p: Exists applied to a lambda; an Exists in its body merges into
\ the same binder list. The binders are brought into scope, as a fun's are,
\ and left when the body is printed: the flag of the parenthesis and the
\ depth before the binders wait.
: lf-pn-exists-app? ( term -- flag )
  dup lf-pp-applied? 0= if drop false exit then
  lf-pn-notation ?dup 0= if false exit then lf-nt-kind @ lf-nt-exists = ;
: lf-pn-lambda-of ( app -- lam ) 1 lf-pp-arg-at ;
\ One binder of the list: the lambda's, shown and brought into scope, and
\ the lambda's body.
: lf-pn-bind-next ( app from -- body from outcome )
  over lf-pn-lambda-of over lf-pp-show-bind >r
  swap lf-pn-lambda-of lf-term-second@ swap r> ;
: lf-pn-binders ( app from -- body outcome )
  begin lf-pn-bind-next ok-then2? 0= if 0 swap exit then
    over lf-pn-exists-app? while lf-pp-space repeat drop outcome-ok ;
: lf-pn-exists-end ( outcome frames -- outcome frames 0 )
  >r r@ frame-restore lf-pp-leave r> lf-pp-wrapped ;
: lf-pn-exists ( term row pos frames -- ... frames next )
  >r lf-prec-lead true lf-pp-parens? lf-pp-open-if dup r@ frame-save drop
  lf-pp-depth r@ frame-save lf-pn-op lf-pp-depth lf-pn-binders
  ok-then? 0= if r> lf-pn-exists-end exit then
  lf-pp-comma 0 false lf-pos lf-pos-prop or r> ['] lf-pn-exists-end lf-pp-term-call ;

\ ---- Dispatch ------------------------------------------------------------
: lf-pn-step ( kind -- xt )
  case lf-nt-atom of ['] lf-pn-atom endof lf-nt-numeral of ['] lf-pn-numeral endof
    lf-nt-infix of ['] lf-pn-binary endof lf-nt-power of ['] lf-pn-binary endof
    lf-nt-suffix of ['] lf-pn-binary endof lf-nt-prefix of ['] lf-pn-prefix endof
    lf-nt-exists of ['] lf-pn-exists endof ['] lf-pn-invalid swap endcase ;
: lf-pn-notated ( term row pos frames -- ... frames next )
  >r over lf-nt-kind @ lf-pn-step r> swap execute ;
' lf-pn-notation is lf-pp-notation
' lf-pn-notated is lf-pp-notated

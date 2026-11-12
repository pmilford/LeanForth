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
\ hidden, as Lean's delaborator hides them.
\ Untrusted presentation code: the checker never loads it, a spelling is no
\ evidence of anything, and the kernel form stays available (notation off).
\ Requires term-printer.fs, which calls the two words installed at the end.
\ State: none of its own; the flag is the printer record's (print-job.fs).
\ Depth (plan task 6.2.0): an operand is a visit of the print's frames, a
\ part of a visit that waits for it keeps its cells on the frames' stack.

require ./term-printer.fs
require ./notation-table.fs

\ ---- Which row, if any ---------------------------------------------------
\ The row for a constant node, or 0: its name spelled in the name pool
\ (taken back at once) and looked up in the table.
: lf-pn-spell ( id -- row | 0 )
  lf-pp-used @ >r ['] lf-pp-put lf-pp-name-to
  r@ lf-pp-pending lf-nt-find r> lf-pp-used ! ;
: lf-pn-head-row ( head -- row | 0 )
  dup lf-tag-constant lf-pp-is? 0= if drop 0 exit then
  lf-pp-const-name if lf-pn-spell else 0 then ;
\ The row if the application has as many arguments as the row says.
: lf-pn-sized ( row n -- row | 0 )
  over 0= if drop exit then over lf-nt-arity @ <> if drop 0 then ;
: lf-pn-mode-sym ( row -- c-addr u ) lf-pp-mode lf-nt-sym ;
: lf-pn-spelt? ( row -- flag ) lf-pn-mode-sym nip 0<> ;
\ A numeral's argument is a literal that fits a cell; ∃ needs a lambda.
: lf-pn-literal? ( term row -- flag )
  lf-nt-a @ lf-pp-arg-at dup lf-tag-lit lf-pp-is? if lf-lit-small? else drop false then ;
: lf-pn-lambda? ( term row -- flag ) lf-nt-a @ lf-pp-arg-at lf-tag-lam lf-pp-is? ;
: lf-pn-shape ( term row -- flag )
  dup lf-nt-kind @ case
    lf-nt-numeral of lf-pn-literal? endof
    lf-nt-exists of lf-pn-lambda? endof
    >r 2drop true r> endcase ;
\ Does the row apply to the application in this mode?
: lf-pn-applies? ( term row -- flag )
  dup lf-nt-kind @ lf-nt-numeral <> over lf-pn-spelt? 0= and
  if 2drop false exit then lf-pn-shape ;
: lf-pn-notation ( term -- row | 0 )
  lf-print-notation? 0= if drop 0 exit then
  dup lf-pp-head >r lf-pn-head-row r> lf-pn-sized
  dup 0= if nip exit then 2dup lf-pn-applies? 0= if 2drop 0 exit then nip ;

\ ---- Positions and symbols ----------------------------------------------
\ The position of an operand: its least precedence, whether text follows
\ it, and whether the row's operands are propositions.
: lf-pn-pos ( prec followed row -- pos )
  lf-nt-props @ >r lf-pos r> if lf-pos-prop or then ;
: lf-pn-open? ( row pos -- flag ) swap lf-nt-prec @ false lf-pp-parens? ;
: lf-pn-op ( row -- ) lf-pn-mode-sym lf-pp-emit ;
\ The operand of a prefix notation: tight in the mathematical modes.
: lf-pn-tight? ( row -- flag )
  lf-nt-mprec @ 0<> lf-pp-mode lf-print-latex lf-print-mathtext between? and ;
: lf-pn-rprec ( row -- prec ) dup lf-pn-tight? if lf-nt-mprec else lf-nt-rprec then @ ;
\ Does text follow what the notation prints, outside a parenthesis it opened?
: lf-pn-rest-followed ( pos paren -- flag ) 0= swap lf-pos-followed? and ;

\ ---- One step per kind: ( term row pos frames -- ... frames next ) ----------
: lf-pn-invalid ( term row pos frames -- outcome frames 0 )
  >r 2drop drop outcome-invalid r> 0 ;
: lf-pn-atom ( term row pos frames -- outcome frames 0 )
  >r drop nip lf-pn-op outcome-ok r> 0 ;
: lf-pn-numeral ( term row pos frames -- outcome frames 0 )
  >r drop lf-nt-a @ lf-pp-arg-at lf-lit-cell lf-pp-number outcome-ok r> 0 ;

\ a OP b, a ^ b and n + 1 have the left operand in common. After it, a part
\ with ( term row rf frames ) finishes the notation, rf being whether text
\ follows it outside any parenthesis the notation opened.
: lf-pn-infix ( term row rf frames -- ... frames next )
  >r over lf-pn-op >r tuck lf-nt-b @ lf-pp-arg-at
  swap dup lf-nt-rprec @ r> rot lf-pn-pos r> ['] frame-return lf-pp-term-call ;
: lf-pn-suffix ( term row rf frames -- outcome frames 0 )
  >r drop lf-pn-op drop outcome-ok r> 0 ;
\ a ^ b: b raised in mathematical text when it is a digit, in braces in LaTeX.
: lf-pn-sup-digit ( d -- c-addr u )
  case 0 of s" ⁰" endof 1 of s" ¹" endof 2 of s" ²" endof 3 of s" ³" endof
    4 of s" ⁴" endof 5 of s" ⁵" endof 6 of s" ⁶" endof 7 of s" ⁷" endof
    8 of s" ⁸" endof s" ⁹" rot endcase ;
\ A numeral OfNat.ofNat _ n _ with n a literal that fits a cell: its value.
: lf-pn-numeral? ( term -- n true | false )
  dup lf-pp-applied? 0= if drop false exit then
  dup lf-pp-head nip 3 <> if drop false exit then
  dup lf-pp-head drop lf-pn-head-row dup 0= if 2drop false exit then
  lf-nt-kind @ lf-nt-numeral <> if drop false exit then
  1 lf-pp-arg-at dup lf-tag-lit lf-pp-is? 0= if drop false exit then
  dup lf-lit-small? if lf-lit-cell true else drop false then ;
: lf-pn-digit ( term row -- d true | false )
  lf-pp-mode lf-print-mathtext <> if 2drop false exit then
  lf-nt-b @ lf-pp-arg-at lf-pn-numeral? 0= if false exit then
  dup 10 u< if true else drop false then ;
: lf-pn-close ( outcome frames -- outcome frames 0 ) >r s" }" lf-pp-emit r> 0 ;
: lf-pn-braced ( term row rf frames -- ... frames next )
  >r drop s" ^{" lf-pp-emit lf-nt-b @ lf-pp-arg-at 0 false lf-pos
  r> ['] lf-pn-close lf-pp-term-call ;
: lf-pn-raised ( term row rf frames -- ... frames next )
  >r drop s" ^" lf-pp-emit lf-nt-b @ lf-pp-arg-at lf-prec-arg false lf-pos
  r> ['] frame-return lf-pp-term-call ;
: lf-pn-power-other ( term row rf frames -- ... frames next )
  lf-pp-mode case lf-print-latex of lf-pn-braced endof
    lf-print-mathtext of lf-pn-raised endof
    >r lf-pn-infix r> endcase ;
: lf-pn-power ( term row rf frames -- ... frames next )
  >r 2 pick 2 pick lf-pn-digit
  if lf-pn-sup-digit lf-pp-emit 2drop drop outcome-ok r> 0 exit then
  r> lf-pn-power-other ;
: lf-pn-rest-xt ( kind -- xt )
  case lf-nt-suffix of ['] lf-pn-suffix endof lf-nt-power of ['] lf-pn-power endof
    ['] lf-pn-infix swap endcase ;
: lf-pn-binary-back ( outcome frames -- ... frames next )
  3 lf-pp-failed? if 0 exit then
  >r r@ lf-pp-restore3 r> 2 pick lf-nt-kind @ lf-pn-rest-xt execute ;
: lf-pn-binary-body ( term row rf frames cont -- ... frames next )
  over frame-save >r 2 pick 2 pick 2 pick r@ lf-pp-save3 drop
  tuck lf-nt-a @ lf-pp-arg-at swap dup lf-nt-lprec @ true rot lf-pn-pos
  r> ['] lf-pn-binary-back lf-pp-term-call ;
: lf-pn-binary ( term row pos frames -- ... frames next )
  >r 2dup lf-pn-open? lf-pp-open-if dup r@ frame-save
  lf-pn-rest-followed r> ['] lf-pp-wrapped lf-pn-binary-body ;

\ OP a: the operand follows the symbol.
: lf-pn-prefix ( term row pos frames -- ... frames next )
  >r 2dup lf-pn-open? lf-pp-open-if dup r@ frame-save lf-pn-rest-followed
  over lf-pn-op >r tuck lf-nt-a @ lf-pp-arg-at
  swap dup lf-pn-rprec r> rot lf-pn-pos r> ['] lf-pp-wrapped lf-pp-term-call ;

\ ∃ x y, p: Exists applied to a lambda; an Exists in its body merges into
\ the same binder list. The binders are brought into scope, as a fun's are,
\ and left when the body is printed: the flag of the parenthesis and the
\ depth before the binders wait.
: lf-pn-exists-app? ( term -- flag )
  dup lf-pp-applied? 0= if drop false exit then
  lf-pn-notation ?dup 0= if false exit then lf-nt-kind @ lf-nt-exists = ;
: lf-pn-lambda-of ( app -- lam ) 1 lf-pp-arg-at ;
: lf-pn-binders ( app from -- body outcome )
  begin
    over lf-pn-lambda-of over lf-pp-show-bind
    dup ok? 0= if nip nip 0 swap exit then drop
    swap lf-pn-lambda-of lf-term-second@ swap
    over lf-pn-exists-app? while lf-pp-space repeat
  drop outcome-ok ;
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
    lf-nt-exists of ['] lf-pn-exists endof
    ['] lf-pn-invalid swap endcase ;
: lf-pn-notated ( term row pos frames -- ... frames next )
  >r over lf-nt-kind @ lf-pn-step r> swap execute ;
' lf-pn-notation is lf-pp-notation
' lf-pn-notated is lf-pp-notated

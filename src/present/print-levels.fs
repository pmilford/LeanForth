\ Universe levels and Sorts, printed as Lean prints them: Prop, Type,
\ Type u for Sort (u + 1), Sort u otherwise; levels with max and imax
\ flattened to the right, successors as u + k, numerals for closed
\ successors of zero (Lean's Level.PP). Untrusted presentation code.
\ Requires print-tokens.fs.
\ State: one walk record in the context, lf-pp-level-walk, for the scans.

require ./print-tokens.fs

lf-level-depth-limit context-walk: lf-pp-level-walk

\ Level scans with the print's fuel. Always zero (Lean's isAlwaysZero):
\ no successor or parameter is reachable through max operands or imax's
\ second operand. Decrementable (Lean's Level.dec succeeds): every path
\ through max and imax ends in a successor. A scan stops at the first
\ witness against, reported internally as rejected: an answer that
\ lf-pp-hit? (print-names.fs) turns into a flag, never a verdict.
\ Each dispatch is a CASE with one arm per level tag (six lines, read as
\ a table); a leaf ends its path with an outcome.
: lf-pp-leaf ( first second walk outcome -- outcome ) nip nip nip ;
: lf-pp-zero-dispatch ( first second walk tag -- outcome )
  case lf-level-tag-zero of outcome-ok lf-pp-leaf endof
    lf-level-tag-max of walk-children endof
    lf-level-tag-imax of rot drop walk-child endof
    lf-level-tag-succ of outcome-rejected lf-pp-leaf endof
    lf-level-tag-param of outcome-rejected lf-pp-leaf endof
    walk-bad-tag endcase ;
: lf-pp-dec-dispatch ( first second walk tag -- outcome )
  case lf-level-tag-succ of outcome-ok lf-pp-leaf endof
    lf-level-tag-max of walk-children endof
    lf-level-tag-imax of walk-children endof
    lf-level-tag-zero of outcome-rejected lf-pp-leaf endof
    lf-level-tag-param of outcome-rejected lf-pp-leaf endof
    walk-bad-tag endcase ;
: lf-pp-zero-visit ( walk -- outcome ) lf-levels ['] lf-pp-zero-dispatch walk-visit ;
: lf-pp-dec-visit ( walk -- outcome ) lf-levels ['] lf-pp-dec-dispatch walk-visit ;
: lf-pp-level-scan ( level xt -- flag outcome )
  lf-pp-level-walk dup lf-pp-lend walk-run lf-pp-level-walk lf-pp-repay lf-pp-hit? >r 0=
  r> ;
: lf-pp-always-zero? ( level -- flag outcome ) ['] lf-pp-zero-visit lf-pp-level-scan ;
: lf-pp-can-dec? ( level -- flag outcome ) ['] lf-pp-dec-visit lf-pp-level-scan ;

\ Views. A view is a level index times two, plus one when the level is to
\ be printed decremented (the u of Type u). A view reads as a node whose
\ operands are views again; a parameter's operand is its name ID. The
\ decrement of succ u is u; of max a b and imax a b it is max of the
\ decremented operands; zero and parameters have none (invalid). An
\ index that is no level of the store becomes the view -1, which reads as
\ no node, so doubling a bad index can never wrap round to a good one.
: lf-pp-view-of ( level -- view ) dup lf-level-valid? if 2* else drop -1 then ;
: lf-pp-dec-view-of ( level -- view ) lf-pp-view-of 1 or ;
: lf-pp-views ( a b -- view-a view-b ) lf-pp-view-of swap lf-pp-view-of swap ;
: lf-pp-plain ( tag first second -- tag a b )
  rot dup >r lf-level-tag-param <> if lf-pp-views then r> -rot ;
: lf-pp-dec-max ( first second -- tag a b )
  lf-pp-dec-view-of swap lf-pp-dec-view-of swap lf-level-tag-max -rot ;
: lf-pp-dec-succ ( first second -- tag a b true | false )
  drop lf-level-read if lf-pp-plain true else false then ;
: lf-pp-dec ( tag first second -- tag a b true | false )
  rot case lf-level-tag-succ of lf-pp-dec-succ endof
    lf-level-tag-max of lf-pp-dec-max true endof
    lf-level-tag-imax of lf-pp-dec-max true endof
    >r 2drop false r> endcase ;
: lf-pp-view ( view -- tag a b true | false )
  dup 1 and >r 2/ lf-level-read 0= if r> drop false exit then
  r> if lf-pp-dec else lf-pp-plain true then ;
: lf-pp-view-tag ( view -- tag true | false ) lf-pp-view if 2drop true else false then ;

\ Printing a view. In an argument (arg? true) a compound level is put in
\ parentheses, as Lean's Result.quote does above precedence 0.
defer lf-pp-level-print ( view arg? -- outcome )
: lf-pp-level-call ( view arg? -- outcome ) ['] lf-pp-level-print lf-pp-call ;
: lf-pp-param-name ( id -- outcome )
  dup 0> over lf-name-valid? and if lf-pp-name outcome-ok else drop-invalid then ;
: lf-pp-level-param ( view -- outcome )
  lf-pp-view if drop nip lf-pp-param-name else outcome-invalid then ;

\ Successors: count them down to the base; a closed level is a numeral,
\ any other is base + k.
: lf-pp-succ-step ( view k -- view' k' true | view k false )
  over lf-pp-view 0= if false exit then
  drop swap lf-level-tag-succ = if rot drop swap 1+ true else drop false then ;
: lf-pp-succs ( view -- base k outcome )
  0 begin lf-pp-spend 0= if outcome-exhausted exit then lf-pp-succ-step 0= until
  outcome-ok ;
: lf-pp-zero-view? ( view -- flag )
  lf-pp-view-tag if lf-level-tag-zero = else false then ;
: lf-pp-offset ( arg? base k -- outcome )
  rot dup >r if s" (" lf-pp-emit then swap true lf-pp-level-call
  ok-then? if lf-pp-plus lf-pp-number outcome-ok then r> lf-pp-wrap ;
: lf-pp-level-succ ( view arg? -- outcome )
  swap lf-pp-succs dup ok? 0= if nip nip nip exit then drop
  over lf-pp-zero-view? if nip nip lf-pp-number outcome-ok else lf-pp-offset then ;

\ max a b c and imax a b c: operands in argument position.
: lf-pp-keyword ( tag -- ) lf-level-tag-max = if lf-pp-max else lf-pp-imax then ;
: lf-pp-item ( view -- outcome ) lf-pp-space true lf-pp-level-call ;
\ Unchecked: the view was read successfully.
: lf-pp-operands ( view -- a b ) lf-pp-view drop rot drop ;
: lf-pp-same-tag? ( view tag -- flag ) swap lf-pp-view-tag if = else drop false then ;
: lf-pp-items ( view tag -- outcome )
  begin
    >r lf-pp-operands swap lf-pp-item ok-then? 0= if r> drop exit then
    dup r@ lf-pp-same-tag? 0= r> swap
  until drop lf-pp-item ;
: lf-pp-level-list ( view arg? tag -- outcome )
  swap dup >r if s" (" lf-pp-emit then dup lf-pp-keyword lf-pp-items r> lf-pp-wrap ;

\ A CASE with one arm per level tag (eight lines, read as a table).
: lf-pp-level-impl ( view arg? -- outcome )
  over lf-pp-view-tag 0= if 2drop outcome-invalid exit then
  case lf-level-tag-zero of 2drop s" 0" lf-pp-emit outcome-ok endof
    lf-level-tag-param of drop lf-pp-level-param endof
    lf-level-tag-succ of lf-pp-level-succ endof
    lf-level-tag-max of lf-level-tag-max lf-pp-level-list endof
    lf-level-tag-imax of lf-level-tag-imax lf-pp-level-list endof
    >r 2drop outcome-invalid r> endcase ;
' lf-pp-level-impl is lf-pp-level-print

\ A level by index, in argument position or not.
: lf-pp-level ( level arg? -- outcome ) swap lf-pp-view-of swap lf-pp-level-call ;

\ Sorts. Sort 0 is Prop, Sort 1 is Type, Sort (u + 1) is Type u, any
\ other Sort u stays Sort u; Prop and Type are atoms, Type u and Sort u
\ are not.
: lf-pp-level-tag ( level -- tag true | false )
  lf-level-read if 2drop true else false then ;
: lf-pp-zero-level? ( level -- flag )
  lf-pp-level-tag if lf-level-tag-zero = else false then ;
: lf-pp-type-level? ( level -- flag )
  lf-level-read 0= if false exit then
  drop swap lf-level-tag-succ = if lf-pp-zero-level? else drop false then ;
: lf-pp-level-atom? ( level -- flag ) dup lf-pp-zero-level? swap lf-pp-type-level? or ;
\ Type and the level's decrement when it has one, else Sort and the level.
: lf-pp-sort-word ( level dec? -- view )
  if lf-pp-type lf-pp-dec-view-of else lf-pp-sort lf-pp-view-of then lf-pp-space ;
: lf-pp-sort-body ( level -- outcome )
  dup lf-pp-can-dec? ok-keep? 0= if nip exit then lf-pp-sort-word true lf-pp-level-call ;
: lf-pp-sort-level ( level -- outcome )
  dup lf-pp-zero-level? if drop lf-pp-prop outcome-ok exit then
  dup lf-pp-type-level? if drop lf-pp-type outcome-ok exit then lf-pp-sort-body ;
\ A concrete Sort n of the term store, n >= 0.
: lf-pp-sort-number ( n -- )
  dup 0= if drop lf-pp-prop exit then dup 1 = if drop lf-pp-type exit then
  lf-pp-type lf-pp-space 1- lf-pp-number ;

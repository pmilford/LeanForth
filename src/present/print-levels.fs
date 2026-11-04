\ Universe levels and Sorts, printed as Lean prints them: Prop, Type,
\ Type u for Sort (u + 1), Sort u otherwise; levels with max and imax
\ flattened to the right, successors as u + k, numerals for closed
\ successors of zero (Lean's Level.PP). Untrusted presentation code.
\ Requires print-tokens.fs.
\ State: one walk record in the context, lf-pp-level-walk, for the scans;
\ a level's print is a visit of the print's frames (print-job.fs).

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

\ Printing a view: a visit of the print's frames (print-job.fs), whose
\ steps keep on the frames' stack what they need while an operand prints,
\ so no depth of a level is tied to the host's stacks. In an argument
\ (arg? true) a compound level is put in parentheses, as Lean's
\ Result.quote does above precedence 0.
defer lf-pp-level-step ( view arg? frames -- ... frames next )
: lf-pp-level-call ( view arg? frames cont -- ... frames next )
  ['] lf-pp-level-step lf-pp-call ;
: lf-pp-param-name ( id -- outcome )
  dup 0> over lf-name-valid? and if lf-pp-name outcome-ok else drop-invalid then ;
: lf-pp-level-param ( view -- outcome )
  lf-pp-view if drop nip lf-pp-param-name else outcome-invalid then ;

\ Successors: count them down to the base; a closed level is a numeral,
\ any other is base + k, arg? and k waiting while the base prints.
: lf-pp-succ-step ( view k -- view' k' true | view k false )
  over lf-pp-view 0= if false exit then
  drop swap lf-level-tag-succ = if rot drop swap 1+ true else drop false then ;
: lf-pp-succs ( view -- base k outcome )
  0 begin lf-pp-spend 0= if outcome-exhausted exit then lf-pp-succ-step 0= until
  outcome-ok ;
: lf-pp-zero-view? ( view -- flag )
  lf-pp-view-tag if lf-level-tag-zero = else false then ;
: lf-pp-offset-back ( outcome frames -- outcome frames 0 )
  >r r@ frame-restore swap ok-then? if lf-pp-plus lf-pp-number outcome-ok then
  r@ frame-restore lf-pp-wrap r> 0 ;
: lf-pp-offset ( arg? base k frames -- ... frames next )
  >r rot dup r@ frame-save if s" (" lf-pp-emit then
  r@ frame-save true r> ['] lf-pp-offset-back lf-pp-level-call ;
: lf-pp-level-succ ( view arg? frames -- ... frames next )
  >r swap lf-pp-succs dup ok? 0= if nip nip nip r> 0 exit then drop
  over lf-pp-zero-view?
  if nip nip lf-pp-number outcome-ok r> 0 else r> lf-pp-offset then ;

\ max a b c and imax a b c: operands in argument position, a right operand
\ of the same tag going on with the list; the right operand and the tag
\ wait while the left one prints, the parenthesis flag below them.
: lf-pp-keyword ( tag -- ) lf-level-tag-max = if lf-pp-max else lf-pp-imax then ;
: lf-pp-item ( view frames cont -- ... frames next )
  2>r lf-pp-space true 2r> lf-pp-level-call ;
\ Unchecked: the view was read successfully.
: lf-pp-operands ( view -- a b ) lf-pp-view drop rot drop ;
: lf-pp-same-tag? ( view tag -- flag ) swap lf-pp-view-tag if = else drop false then ;
defer lf-pp-items ( view tag frames -- ... frames next )
: lf-pp-items-back ( outcome frames -- ... frames next )
  over ok? 0= if 2 over frame-drop 0 exit then nip
  >r r@ frame-restore r@ frame-restore 2dup swap lf-pp-same-tag?
  if swap r> lf-pp-items exit then nip r> ['] frame-return lf-pp-item ;
: lf-pp-items-next ( view tag frames -- ... frames next )
  >r swap lf-pp-operands r@ frame-save swap r@ frame-save
  r> ['] lf-pp-items-back lf-pp-item ;
' lf-pp-items-next is lf-pp-items
: lf-pp-level-list ( view arg? tag frames -- ... frames next )
  >r swap dup r@ frame-save ['] lf-pp-wrapped r@ frame-save if s" (" lf-pp-emit then
  dup lf-pp-keyword r> lf-pp-items ;

\ The step for a view's tag: a CASE with one arm per level tag (read as
\ a table).
: lf-pp-level-zero ( view arg? frames -- outcome frames 0 )
  >r 2drop s" 0" lf-pp-emit outcome-ok r> 0 ;
: lf-pp-level-name ( view arg? frames -- outcome frames 0 )
  >r drop lf-pp-level-param r> 0 ;
: lf-pp-level-max ( view arg? frames -- ... frames next )
  lf-level-tag-max swap lf-pp-level-list ;
: lf-pp-level-imax ( view arg? frames -- ... frames next )
  lf-level-tag-imax swap lf-pp-level-list ;
: lf-pp-level-bad ( view arg? frames -- outcome frames 0 ) >r 2drop outcome-invalid r> 0 ;
: lf-pp-level-by ( tag -- xt )
  case lf-level-tag-zero of ['] lf-pp-level-zero endof
    lf-level-tag-param of ['] lf-pp-level-name endof
    lf-level-tag-succ of ['] lf-pp-level-succ endof
    lf-level-tag-max of ['] lf-pp-level-max endof
    lf-level-tag-imax of ['] lf-pp-level-imax endof
    ['] lf-pp-level-bad swap endcase ;
: lf-pp-level-impl ( view arg? frames -- ... frames next )
  2 pick lf-pp-view-tag if lf-pp-level-by else ['] lf-pp-level-bad then execute ;
' lf-pp-level-impl is lf-pp-level-step

\ A level by index, in argument position or not: as a print's root, and
\ as a part of a visit, continuing with cont.
: lf-pp-level ( level arg? -- outcome )
  swap lf-pp-view-of swap ['] lf-pp-level-step lf-pp-run ;
: lf-pp-level-part ( level arg? frames cont -- ... frames next )
  2>r swap lf-pp-view-of swap 2r> lf-pp-level-call ;

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
\ An atom prints as Prop or Type. Any other Sort as Type and the level's
\ decrement when it has one, else Sort and the level, in argument
\ position: a part of the Sort's visit.
: lf-pp-sort-atom ( level -- outcome )
  lf-pp-zero-level? if lf-pp-prop else lf-pp-type then outcome-ok ;
: lf-pp-sort-word ( level dec? -- view )
  if lf-pp-type lf-pp-dec-view-of else lf-pp-sort lf-pp-view-of then lf-pp-space ;
: lf-pp-sort-body ( level frames cont -- ... frames next )
  2>r dup lf-pp-can-dec? ok-keep? 0= if nip 2r> exit then
  lf-pp-sort-word true 2r> lf-pp-level-call ;
\ A concrete Sort n of the term store, n >= 0.
: lf-pp-sort-number ( n -- )
  dup 0= if drop lf-pp-prop exit then dup 1 = if drop lf-pp-type exit then
  lf-pp-type lf-pp-space 1- lf-pp-number ;

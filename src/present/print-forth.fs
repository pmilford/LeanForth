\ The term printer's Forth mode (ADR 0017 §13, plan task 8.1.2): prints a
\ term, or a whole declaration, as the LeanForth words that build it, so
\ that running the printed words (src/author/) gives the identical term:
\ the same nodes, levels, constants and universe arguments, binder names
\ and kinds, labels and notes. Constants are written by their full names,
\ with root: where a variable or universe parameter has the same spelling
\ or the name is a syntax word; a variable by its name, or as n var# when
\ an inner binder hides the name, it has none, or the name could be read
\ as something else (a syntax word, a number). A Pi prints as A B -> when
\ its binder is explicit, unused and anonymous or hygienic (Lean's
\ a._@._hyg.0); running -> gives the anonymous name, the one stated
\ exception to the round trip. A declaration prints as its declaration
\ word and full name, a line per universe parameter, a line per
\ parameter (the leading binders its type and value share: the same
\ domain node, name and kind; for an axiom or import stub, the leading
\ binders of the type that do not print as ->), the type, := and the
\ value, and end NAME. Lines wrap at 90 columns between words, never
\ between a word and the name it reads; a note ends its line.
\ Untrusted presentation code: the checker never loads it, and no output
\ is evidence of anything. Uses the term printer's job record
\ (print-job.fs: sink, fuel, nested visits, binders in scope and the name
\ pool); a binder in scope holds the name its variables can be written
\ by (empty when none) and, in its domain cell, -1 for the binder of an
\ arrow, which the printed words do not count.
\ State: one context record, lf-pforth (ADR 0009), besides the printer's.
\
\ Public words (outcomes from lib/outcome.fs):
\   lf-print-forth-term ( term fuel -- outcome )  a closed term
\   lf-print-forth-decl ( decl fuel -- outcome )  a declaration (/lf-fdecl)
\ ok: printed. invalid: malformed input, as for lf-print-term, or a
\ variable bound by an arrow. unsupported: a name the words cannot spell
\ (a part with a dot, a space or only digits; a universe parameter named
\ like a syntax word). exhausted and full: as for lf-print-term.

require ./term-printer.fs
require ./note-table.fs

\ Declarations, as the authoring program records them.
0 constant lf-decl-theorem
1 constant lf-decl-def
2 constant lf-decl-axiom
3 constant lf-decl-stub
8 constant lf-decl-universe-capacity
begin-structure /lf-fdecl
  field: lf-fdecl-kind          \ lf-decl-theorem, -def, -axiom or -stub
  field: lf-fdecl-name          \ name ID of the full name
  field: lf-fdecl-type          \ term, or -1 for none (an import stub)
  field: lf-fdecl-value         \ term, or -1 for none (an axiom or import stub)
  field: lf-fdecl-universes     \ number of universe parameters
  lf-decl-universe-capacity cells +field lf-fdecl-universe   \ their name IDs
end-structure

90 constant lf-pf-width
begin-structure /lf-pforth
  field: lf-pforth-column      \ characters on the current line
  field: lf-pforth-start       \ column where the line's words begin
  field: lf-pforth-indent      \ indentation of a wrapped line
  field: lf-pforth-decl        \ the declaration being printed, or 0
end-structure
/lf-pforth context-record: lf-pforth

\ The syntax words (src/author/words.fs checks its words against this
\ list when it loads). A name equal to one of them is written with root:
\ or var#.
: lf-pf-word, ( c-addr u -- ) dup c, here swap dup chars allot move ;
: lf-pf-reserve ( "names<eol>" -- ) begin parse-name dup while lf-pf-word, repeat 2drop ;
create lf-pf-reserved
lf-pf-reserve \ ( theorem def axiom import-stub universe := end namespace open
lf-pf-reserve explicit: implicit: strict-implicit: instance: fun forall -> $ ^
lf-pf-reserve Prop Type Sort level+ level-max level-imax var# root:
lf-pf-reserve label: note" ai-note" _ let: let have field-at by s" import
0 c, align
: lf-pf-next ( c-addr -- c-addr' ) count chars + ;
: lf-pf-reserved? ( c-addr u -- flag )
  lf-pf-reserved begin dup c@ while >r 2dup r@ count compare 0= if r> drop 2drop true exit
  then r> lf-pf-next repeat drop 2drop false ;

\ Names. A part is spelt plainly when it is not empty, has no dot, space or
\ control character, is not all digits and is not [anonymous]: then its
\ text reads back as the same part. A name can be referred to when, in
\ addition, it is no syntax word and cannot start a Forth number.
: lf-pf-digit? ( char -- flag ) [char] 0 [char] 9 1+ within ;
: lf-pf-digits? ( c-addr u -- flag )
  dup 0= if 2drop false exit then
  true -rot chars over + swap ?do i c@ lf-pf-digit? and loop ;
: lf-pf-odd-char? ( char -- flag ) dup bl 1+ < swap [char] . = or ;
: lf-pf-odd? ( c-addr u -- flag )
  false -rot chars over + swap ?do i c@ lf-pf-odd-char? or loop ;
: lf-pf-anonymous ( -- c-addr u ) s" [anonymous]" ;
: lf-pf-plain? ( c-addr u -- flag )
  dup 0= if 2drop false exit then 2dup lf-pf-odd? if 2drop false exit then
  2dup lf-pf-digits? if 2drop false exit then lf-pf-anonymous compare 0<> ;
: lf-pf-part? ( id -- flag )
  dup lf-name-tag@ lf-name-tag-str = if lf-name-text lf-pf-plain? else drop true then ;
: lf-pf-writable? ( id -- flag )
  dup 0= if drop false exit then
  begin dup while dup lf-pf-part? 0= if drop false exit then lf-name-prefix@ repeat
  drop true ;
: lf-pf-among? ( c-addr u char -- flag )
  false 2swap chars over + swap ?do over i c@ = or loop nip ;
: lf-pf-number-start? ( char -- flag )
  dup lf-pf-digit? swap s\" -+$#%&'\"." rot lf-pf-among? or ;
: lf-pf-token? ( c-addr u -- flag )
  dup 0= if 2drop false exit then
  over c@ lf-pf-number-start? if 2drop false exit then lf-pf-reserved? 0= ;

\ Output: words separated by one space, a line wrapped before a word that
\ would pass the width. A unit is text that must stay on one line.
create lf-pf-eol 10 c,
: lf-pf-column ( -- addr ) lf-pforth lf-pforth-column ;
: lf-pf-spaces ( n -- ) s"                 " rot min lf-pp-emit ;
: lf-pf-line-at ( indent -- )
  lf-pf-column @ if lf-pf-eol 1 lf-pp-emit then
  dup lf-pf-spaces dup lf-pf-column ! lf-pforth lf-pforth-start ! ;
\ A new line at indent; wrapped lines go two columns further in.
: lf-pf-open ( indent -- ) dup 2 + lf-pforth lf-pforth-indent ! lf-pf-line-at ;
: lf-pf-wrap ( -- ) lf-pforth lf-pforth-indent @ lf-pf-line-at ;
: lf-pf-fits? ( u -- flag ) lf-pf-column @ + 1+ lf-pf-width > 0= ;
: lf-pf-gap ( u -- )
  lf-pf-column @ lf-pforth lf-pforth-start @ > 0= if drop exit then
  lf-pf-fits? if s"  " lf-pp-emit 1 lf-pf-column +! else lf-pf-wrap then ;
: lf-pf-text ( c-addr u -- ) dup lf-pf-gap dup lf-pf-column +! lf-pp-emit ;
\ The text put in the pool since mark, as one unit; the pool is given back.
: lf-pf-unit ( mark -- ) dup lf-pp-pending lf-pf-text lf-pp-used ! ;
\ The next word starts a new line.
: lf-pf-end-line ( -- ) lf-pf-width lf-pf-column ! ;
: lf-pf-mark ( -- mark ) lf-pp-used @ ;
: lf-pf-put-name ( id -- ) ['] lf-pp-put lf-pp-name-to ;
: lf-pf-put-number ( u -- ) ['] lf-pp-put lf-pp-number-to ;

\ Labels and notes after their term.
: lf-pf-note-word ( kind -- c-addr u )
  case lf-note-person of s\" note\" " endof lf-note-ai of s\" ai-note\" " endof
  s" label: " rot endcase ;
: lf-pf-note ( i -- )
  lf-pf-mark over lf-note-kind@ dup >r lf-pf-note-word lf-pp-put over lf-note-text@
    lf-pp-put
  r@ lf-note-label <> if s\" \"" lf-pp-put then lf-pf-unit drop
  r> lf-note-label <> if lf-pf-end-line then ;
: lf-pf-notes ( term -- )
  lf-note-count 0 ?do dup i lf-note-on? if i lf-pf-note then loop drop ;

\ Binders in scope: a variable's name, or n var#.
: lf-pf-visible? ( j -- flag ) lf-pp-entry lf-pbind-domain @ 0< 0= ;
: lf-pf-inner# ( j -- n ) 0 swap 0 ?do i lf-pf-visible? if 1+ then loop ;
: lf-pf-shown ( j -- c-addr u ) lf-pp-entry lf-pp-text ;
: lf-pf-hides? ( c-addr u k -- c-addr u flag )
  dup lf-pf-visible? if lf-pf-shown 2over compare 0= else drop false then ;
: lf-pf-hidden? ( j -- flag )
  dup lf-pf-shown dup 0= if 2drop drop true exit then
  rot 0 ?do i lf-pf-hides? if 2drop true unloop exit then loop 2drop false ;
: lf-pf-var# ( n -- ) lf-pf-mark swap lf-pf-put-number s"  var#" lf-pp-put lf-pf-unit ;
: lf-pf-var ( i -- outcome )
  dup 0 lf-pp-depth within 0= if drop-invalid exit then
  dup lf-pf-visible? 0= if drop-invalid exit then
  dup lf-pf-hidden? if lf-pf-inner# lf-pf-var# else lf-pf-shown lf-pf-text then
    outcome-ok ;

\ A word, as a step that cannot fail; a word after a step, only when the
\ step succeeded.
: lf-pf-say ( c-addr u -- outcome ) lf-pf-text outcome-ok ;
: lf-pf-then-word ( outcome c-addr u -- outcome ) rot dup ok? if drop lf-pf-say else nip
  nip then ;
: lf-pf-number ( u -- ) lf-pf-mark swap lf-pf-put-number lf-pf-unit ;

\ Universe levels, postfix: 0, 2, u, u 1 level+, a b level-max, a b level-imax.
\ A parameter is written by its name, which must be a usable token.
defer lf-pf-level-visit ( level x -- outcome )
: lf-pf-level ( level -- outcome ) 0 ['] lf-pf-level-visit lf-pp-call ;
: lf-pf-param ( id -- outcome )
  dup lf-pf-writable? 0= if drop outcome-unsupported exit then
  lf-pf-mark swap lf-pf-put-name dup lf-pp-pending lf-pf-token?
  if lf-pf-unit outcome-ok else lf-pp-used ! outcome-unsupported then ;
\ Unchecked: level is valid; successors point to earlier levels.
: lf-pf-succs ( level -- base n )
  0 begin over lf-level-tag@ lf-level-tag-succ = while swap lf-level-first@ swap 1+
    repeat ;
: lf-pf-zero? ( level -- flag ) lf-level-tag@ lf-level-tag-zero = ;
: lf-pf-offset ( base n -- outcome )
  swap lf-pf-level dup ok? if drop lf-pf-number s" level+" lf-pf-say else nip then ;
: lf-pf-succ-level ( level -- outcome )
  lf-pf-succs over lf-pf-zero? if nip lf-pf-number outcome-ok else lf-pf-offset then ;
: lf-pf-operands ( level -- outcome )
  dup lf-level-first@ lf-pf-level ok-then? if lf-level-second@ lf-pf-level then ;
: lf-pf-binary ( level c-addr u -- outcome ) 2>r lf-pf-operands 2r> lf-pf-then-word ;
\ A CASE with one arm per level tag, read as a table.
: lf-pf-level-node ( level x -- outcome )
  drop dup lf-level-valid? 0= if drop-invalid exit then
  dup lf-level-tag@ case
    lf-level-tag-zero of drop s" 0" lf-pf-say endof
    lf-level-tag-succ of lf-pf-succ-level endof
    lf-level-tag-max of s" level-max" lf-pf-binary endof
    lf-level-tag-imax of s" level-imax" lf-pf-binary endof
    lf-level-tag-param of lf-level-first@ lf-pf-param endof
    >r drop-invalid r> endcase ;
' lf-pf-level-node is lf-pf-level-visit

\ Sorts: Prop, l Type for Sort (l + 1), l Sort otherwise. A concrete Sort
\ n prints the same words (they build the symbolic Sort).
: lf-pf-sort-word ( level c-addr u -- outcome ) 2>r lf-pf-level 2r> lf-pf-then-word ;
: lf-pf-symbolic ( level -- outcome )
  dup lf-level-valid? 0= if drop-invalid exit then
  dup lf-pf-zero? if drop s" Prop" lf-pf-say exit then
  dup lf-level-tag@ lf-level-tag-succ =
  if lf-level-first@ s" Type" else s" Sort" then lf-pf-sort-word ;
: lf-pf-concrete ( n -- outcome )
  ?dup 0= if s" Prop" lf-pf-say exit then 1- lf-pf-number s" Type" lf-pf-say ;

\ Constants: the full name, with root: when the words would find something
\ else under it (a variable or universe parameter, a syntax word, a
\ number), then each universe argument and ^.
: lf-pf-universe-ids ( -- addr n )
  lf-pforth lf-pforth-decl @ ?dup 0= if 0 0 exit then
  dup lf-fdecl-universe swap lf-fdecl-universes @ 0 max lf-decl-universe-capacity min ;
: lf-pf-decl-universe? ( id -- flag )
  lf-pf-universe-ids 0 ?do 2dup i cells + @ = if 2drop true unloop exit then loop
  2drop false ;
: lf-pf-root? ( id -- flag )
  dup lf-pf-decl-universe? if drop true exit then
  lf-pf-mark swap lf-pf-put-name dup lf-pp-pending 2dup lf-pf-token? 0= -rot 0 lf-pp-any?
    or
  swap lf-pp-used ! ;
: lf-pf-const-name ( id -- outcome )
  dup lf-pf-writable? 0= if drop outcome-unsupported exit then
  lf-pf-mark over lf-pf-root? if s" root: " lf-pp-put then swap lf-pf-put-name lf-pf-unit
  outcome-ok ;
: lf-pf-universe-args ( term -- outcome )
  lf-pp-const-levels 0= if outcome-invalid exit then
  0 ?do dup i lf-pp-level-at lf-pf-level dup ok? 0= if nip unloop exit then drop
    s" ^" lf-pf-text loop drop outcome-ok ;
: lf-pf-const ( term -- outcome )
  dup lf-pp-const-name 0= if drop-invalid exit then
  lf-pf-const-name ok-then? if lf-pf-universe-args then ;

\ Binders: the domain, then kind: NAME, then the body with the binder in
\ scope, then fun or forall; or A B -> for an arrow. A binder with no
\ entry in the side table is explicit and anonymous.
defer lf-pf-term-visit ( term x -- outcome )
: lf-pf-term ( term -- outcome ) 0 ['] lf-pf-term-visit lf-pp-call ;
: lf-pf-binder-name ( node -- name kind ) lf-pres-binder@ 0= if 0 lf-binder-default then ;
: lf-pf-kind-word ( kind -- c-addr u )
  case lf-binder-implicit of s" implicit:" endof lf-binder-strict of s" strict-implicit:"
    endof
    lf-binder-instance of s" instance:" endof s" explicit:" rot endcase ;
: lf-pf-spellable? ( id -- flag ) dup 0= swap lf-pf-writable? or ;
: lf-pf-name-text ( id -- ) ?dup if lf-pf-put-name else lf-pf-anonymous lf-pp-put then ;
: lf-pf-opener ( node -- outcome )
  lf-pf-binder-name over lf-pf-spellable? 0= if 2drop outcome-unsupported exit then
  lf-pf-mark swap lf-pf-kind-word lf-pp-put s"  " lf-pp-put swap lf-pf-name-text
    lf-pf-unit
  outcome-ok ;
\ The name its variables are written by, put in the pool, if they can be.
: lf-pf-referable ( id -- )
  dup lf-pf-writable? 0= if drop exit then
  lf-pf-mark swap lf-pf-put-name dup lf-pp-pending lf-pf-token? if drop else lf-pp-used !
    then ;
: lf-pf-bind-visible ( node -- outcome )
  lf-pf-mark swap lf-pf-binder-name drop lf-pf-referable 0 swap lf-pp-bind ;
: lf-pf-bind-arrow ( -- outcome ) -1 lf-pf-mark lf-pp-bind ;
: lf-pf-head ( node -- outcome )
  dup lf-term-first@ lf-pf-term dup ok? 0= if nip exit then drop
  dup lf-pf-opener dup ok? 0= if nip exit then drop lf-pf-bind-visible ;
: lf-pf-binder ( node c-addr u -- outcome )
  2>r dup lf-pf-head dup ok?
  if drop lf-term-second@ lf-pf-term 1 lf-pp-unbind 2r> lf-pf-then-word exit then
  nip 2r> 2drop ;
: lf-pf-loose-name? ( id -- flag ) dup 0= if drop true else lf-pp-hygienic? then ;
: lf-pf-arrow? ( pi -- flag outcome )
  dup lf-pp-kind lf-binder-default <> if drop false outcome-ok exit then
  dup lf-pf-binder-name drop lf-pf-loose-name? 0= if drop false outcome-ok exit then
  lf-term-second@ 0 lf-pp-loose? >r 0= r> ;
: lf-pf-arrow ( pi -- outcome )
  dup lf-term-first@ lf-pf-term dup ok? 0= if nip exit then drop
  lf-pf-bind-arrow dup ok? 0= if nip exit then drop
  lf-term-second@ lf-pf-term 1 lf-pp-unbind s" ->" lf-pf-then-word ;
: lf-pf-pi ( pi -- outcome )
  dup lf-pf-arrow? dup ok? 0= if nip nip exit then drop
  if lf-pf-arrow else s" forall" lf-pf-binder then ;
: lf-pf-app ( app -- outcome )
  dup lf-term-first@ lf-pf-term ok-then? if lf-term-second@ lf-pf-term s" $"
    lf-pf-then-word then ;

\ A CASE with one arm per term tag, read as a table; then the node's
\ labels and notes.
: lf-pf-node ( term -- outcome )
  dup lf-pp-tag 0= if drop-invalid exit then
  case lf-tag-bvar of lf-term-first@ lf-pf-var endof
    lf-tag-sort of lf-term-first@ lf-pf-concrete endof
    lf-tag-symbolic-sort of lf-term-first@ lf-pf-symbolic endof
    lf-tag-app of lf-pf-app endof
    lf-tag-lam of s" fun" lf-pf-binder endof
    lf-tag-pi of lf-pf-pi endof
    lf-tag-constant of lf-pf-const endof
    >r drop-invalid r> endcase ;
: lf-pf-noted ( term x -- outcome )
  drop dup lf-pf-node dup ok? if over lf-pf-notes then nip ;
' lf-pf-noted is lf-pf-term-visit

\ Declarations.
: lf-pf-keyword ( kind -- c-addr u )
  case lf-decl-theorem of s" theorem" endof lf-decl-def of s" def" endof
    lf-decl-axiom of s" axiom" endof s" import-stub" rot endcase ;
: lf-pf-kind? ( decl -- flag ) lf-fdecl-kind @ lf-decl-theorem lf-decl-stub between? ;
: lf-pf-header ( decl -- outcome )
  dup lf-pf-kind? 0= if drop-invalid exit then
  dup lf-fdecl-name @ dup lf-pf-writable? 0= if 2drop outcome-unsupported exit then
  0 lf-pf-open lf-pf-mark rot lf-fdecl-kind @ lf-pf-keyword lf-pp-put s"  " lf-pp-put
  swap lf-pf-put-name lf-pf-unit outcome-ok ;
: lf-pf-universe ( id -- outcome )
  dup lf-pf-writable? 0= if drop outcome-unsupported exit then
  2 lf-pf-open lf-pf-mark s" universe " lf-pp-put swap lf-pf-put-name lf-pf-unit
    outcome-ok ;
: lf-pf-universes ( -- outcome )
  lf-pf-universe-ids 0 ?do dup i cells + @ lf-pf-universe dup ok? 0= if nip unloop exit
    then
    drop loop drop outcome-ok ;
\ A parameter: its own line, then its binder stays in scope.
: lf-pf-param-line ( binder -- outcome ) 2 lf-pf-open lf-pf-head ;
: lf-pf-same-binder? ( pi lam -- flag )
  lf-pf-binder-name rot lf-pf-binder-name rot = >r = r> and ;
: lf-pf-shares? ( type value -- flag )
  over lf-tag-pi lf-pp-is? over lf-tag-lam lf-pp-is? and 0= if 2drop false exit then
  2dup lf-term-first@ swap lf-term-first@ <> if 2drop false exit then lf-pf-same-binder? ;
: lf-pf-bodies ( type value -- type' value' ) lf-term-second@ swap lf-term-second@ swap ;
: lf-pf-def-params ( type value -- type' value' outcome )
  begin 2dup lf-pf-shares? while
    over lf-pf-param-line dup ok? 0= if exit then drop lf-pf-bodies
  repeat outcome-ok ;
: lf-pf-type-params ( type -- type' outcome )
  begin dup lf-tag-pi lf-pp-is? while
    dup lf-pf-arrow? dup ok? 0= if nip exit then drop if outcome-ok exit then
    dup lf-pf-param-line dup ok? 0= if exit then drop lf-term-second@
  repeat outcome-ok ;
: lf-pf-body ( term -- outcome ) 2 lf-pf-open lf-pf-term ;
: lf-pf-definition ( decl -- outcome )
  dup lf-fdecl-type @ swap lf-fdecl-value @ lf-pf-def-params dup ok? 0= if nip nip exit
    then
  drop swap lf-pf-body dup ok? 0= if nip exit then drop
  0 lf-pf-open s" :=" lf-pf-text lf-pf-body ;
: lf-pf-statement ( decl -- outcome )
  lf-fdecl-type @ dup 0< if drop outcome-ok exit then
  lf-pf-type-params dup ok? 0= if nip exit then drop lf-pf-body ;
: lf-pf-parts ( decl -- outcome )
  dup lf-fdecl-kind @ lf-decl-def > if lf-pf-statement else lf-pf-definition then ;
: lf-pf-end ( decl -- outcome )
  0 lf-pf-open lf-pf-mark s" end " lf-pp-put swap lf-fdecl-name @ lf-pf-put-name
    lf-pf-unit
  lf-pf-eol 1 lf-pp-emit 0 lf-pf-column ! outcome-ok ;
: lf-pf-declaration ( decl x -- outcome )
  drop dup lf-pf-header dup ok? 0= if nip exit then drop
  lf-pf-universes dup ok? 0= if nip exit then drop
  dup lf-pf-parts dup ok? 0= if nip exit then drop lf-pf-end ;

\ Public words; see the header.
: lf-pf-start ( decl -- ) lf-pforth /lf-pforth erase lf-pforth lf-pforth-decl ! ;
: lf-print-forth-term ( term fuel -- outcome )
  lf-print-ready? 0= if drop-invalid exit then 0 lf-pf-start lf-pf-term lf-pp-finish ;
: lf-print-forth-decl ( decl fuel -- outcome )
  lf-print-ready? 0= if drop-invalid exit then
  dup lf-pf-start 0 ['] lf-pf-declaration lf-pp-call lf-pp-finish 0 lf-pf-start ;

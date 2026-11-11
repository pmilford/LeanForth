\ The term printer's Forth mode (ADR 0017 §13, plan task 8.1.2): prints a
\ term, or a whole declaration, as the LeanForth words that build it, so
\ that running the printed words (src/author/) gives the identical term:
\ the same nodes, levels, constants and universe arguments, binder names
\ and kinds, labels and notes. Constants are written by their full names,
\ with root: where a namespace around a dotted declaration holds a constant
\ the reader would find first (it looks names up there first), and where a
\ variable or universe parameter has the same spelling or the name is a
\ syntax word; a variable by its name, or as n var# when
\ an inner binder hides the name, it has none, or the name could be read
\ as something else (a syntax word, a number). A Pi prints as A B -> when
\ its binder is explicit, unused and anonymous or hygienic (Lean's
\ a._@._hyg.0); running -> gives the anonymous name, the one stated
\ exception to the round trip. A declaration prints as its declaration
\ word (after protected, for a protected one) and full name, a line per
\ universe parameter, a line per
\ parameter (the leading binders its type and value share: the same
\ domain node, name and kind; for an axiom or import stub, the leading
\ binders of the type that do not print as ->), the type, := and the
\ value, and end NAME. Lines wrap at 90 columns between words, never
\ between a word and the name it reads; a note ends its line.
\ Untrusted presentation code: the checker never loads it, and no output
\ is evidence of anything. Uses the term printer's job record
\ (print-job.fs: sink, fuel, the frames its visits run on, binders in
\ scope and the name pool); a binder in scope holds the name its variables
\ can be written by (empty when none) and, in its domain cell, -1 for the
\ binder of an arrow, which the printed words do not count. As in the
\ term printer, every term, level and the declaration is a visit of the
\ print's frames, whose steps keep what they need on the frames' stack,
\ so no depth is tied to the host's stacks (plan task 6.2.0).
\ State: one context record, lf-pforth (ADR 0009), besides the printer's.
\
\ Public words (outcomes from lib/outcome.fs):
\   lf-print-forth-term ( term fuel -- outcome )  a closed term
\   lf-print-forth-decl ( decl fuel -- outcome )  a declaration (/lf-fdecl)
\ ok: printed. invalid: malformed input, as for lf-print-term, or a
\ variable bound by an arrow. unsupported: a name the words cannot spell
\ (a part with a dot, a space, only digits or between guillemets; a universe parameter named
\ like a syntax word), or a label or note that would not read back as
\ itself (from lf-note-add, not the words), which is never printed as
\ live words. exhausted and full: as for lf-print-term. On a failure the
\ text sent to the sink so far is incomplete.

require ./term-printer.fs
require ./note-table.fs
require ../lib/text-rule.fs
require ../core/input.fs

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
  field: lf-fdecl-protected     \ true for a protected declaration (Lean's protected)
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
lf-pf-reserve protected export lit# proj#
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
: lf-pf-open-quote ( -- c-addr u ) s\" \xC2\xAB" ;
: lf-pf-close-quote ( -- c-addr u ) s\" \xC2\xBB" ;
\ A part of 5 or more bytes between guillemets: the reader takes it as «digits»
\ (src/author/declarations.fs, lfa-quoted?), so as text it would read back as
\ another part or stop the file; such a part is not written (plan task 8.6.3).
: lf-pf-guillemets? ( c-addr u -- flag )
  dup 4 > 0= if 2drop false exit then
  2dup 2 min lf-pf-open-quote compare 0= -rot + 2 - 2 lf-pf-close-quote compare 0= and ;
: lf-pf-plain? ( c-addr u -- flag )
  dup 0= if 2drop false exit then 2dup lf-pf-odd? if 2drop false exit then
  2dup lf-pf-guillemets? if 2drop false exit then
  2dup tr-rule? 0= if 2drop false exit then
  2dup lf-pf-digits? if 2drop false exit then lf-pf-anonymous compare 0<> ;
\ A numeric part is writable up to the digits a cell holds exactly, which
\ the authoring words read (src/author/declarations.fs): 18 on a 64-bit
\ host, 9 on a 32-bit one. Lean's macro scopes have long ones
\ (x._@.Init.Prelude.1910291827._hygCtx._hyg.5).
1 cells 8 < [if] 9 [else] 18 [then] constant lf-name-digits-max
: lf-pf-part-bound ( -- u ) 1 lf-name-digits-max 0 ?do 10 * loop ;
: lf-pf-part? ( id -- flag )
  dup lf-name-tag@ lf-name-tag-str =
  if lf-name-text 2dup lf-pf-digits? if 2drop true else lf-pf-plain? then exit then
  lf-name-payload lf-pf-part-bound u< ;
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

\ A name the authoring words can declare or refer to by a word (the name of
\ a declaration, a universe parameter, a structure): every part writable and
\ the first one a string part that cannot start a Forth number, so the whole
\ dotted token is no number. A later numeric part is no problem: no word is
\ made for a part, only for the whole name (src/author/namespaces.fs). A
\ string part of digits is written between guillemets.
: lf-pf-root ( id -- id' ) begin dup lf-name-prefix@ ?dup while nip repeat ;
: lf-pf-root-ok? ( id -- flag )
  lf-pf-root dup lf-name-tag@ lf-name-tag-str = 0= if drop false exit then
  lf-name-text drop c@ lf-pf-number-start? 0= ;
: lf-pf-declarable? ( id -- flag )
  dup lf-pf-writable? if lf-pf-root-ok? else drop false then ;

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
\ A part: a string part of digits between guillemets (it stays a string
\ when read back), a numeric part as its digits.
: lf-pf-put-part ( id -- )
  dup lf-name-tag@ lf-name-tag-str <>
  if lf-name-payload ['] lf-pp-put lf-pp-number-to exit then
  lf-name-text 2dup lf-pf-digits? 0= if lf-pp-put exit then
  lf-pf-open-quote lf-pp-put lf-pp-put lf-pf-close-quote lf-pp-put ;
\ The parts from the root (component 0) on, joined by dots.
: lf-pf-put-parts ( id n -- )
  dup 0 ?do i if s" ." lf-pp-put then 2dup i - 1- lf-pp-ancestor lf-pf-put-part loop 2drop ;
\ A name as text, as lf-pp-name-to: too long a name marks the pool full.
: lf-pf-put-name ( id -- )
  dup lf-pp-name-depth dup lf-name-default >
  if ['] lf-pp-put lf-pp-too-deep else lf-pf-put-parts then ;
: lf-pf-put-number ( u -- ) ['] lf-pp-put lf-pp-number-to ;

\ Labels and notes after their term. A label reads back as one token, so
\ it is not empty and has no blank or control character; a note's text
\ has no " and no line end, which would end it early. Both pass the text
\ rule (lib/text-rule.fs), as the reader applies it to a line. Any other text
\ would print as live words: unsupported.
: lf-pf-blank-in? ( c-addr u -- flag )
  false -rot chars over + swap ?do i c@ bl 1+ < or loop ;
: lf-pf-label? ( c-addr u -- flag )
  dup 0= if 2drop false exit then 2dup tr-rule? 0= if 2drop false exit then
  lf-pf-blank-in? 0= ;
: lf-pf-note-end? ( char -- flag ) dup [char] " = over 10 = or swap 13 = or ;
: lf-pf-note? ( c-addr u -- flag )
  2dup tr-rule? invert if 2drop false exit then
  true -rot chars over + swap ?do i c@ lf-pf-note-end? 0= and loop ;
: lf-pf-spellable-note? ( i -- flag )
  dup lf-note-text@ rot lf-note-kind@ lf-note-label =
  if lf-pf-label? else lf-pf-note? then ;
: lf-pf-note-word ( kind -- c-addr u )
  case lf-note-person of s\" note\" " endof lf-note-ai of s\" ai-note\" " endof
  s" label: " rot endcase ;
: lf-pf-note ( i -- outcome )
  dup lf-pf-spellable-note? 0= if drop outcome-unsupported exit then
  lf-pf-mark over lf-note-kind@ dup >r lf-pf-note-word lf-pp-put over lf-note-text@
    lf-pp-put
  r@ lf-note-label <> if s\" \"" lf-pp-put then lf-pf-unit drop
  r> lf-note-label <> if lf-pf-end-line then outcome-ok ;
: lf-pf-notes ( term -- outcome )
  lf-note-count 0 ?do dup i lf-note-on?
    if i lf-pf-note ok-then? 0= if unloop exit then then loop drop outcome-ok ;

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
\ A parameter is written by its name, which must be a usable token. A
\ level is a visit; lf-pf-level asks for one, continuing with cont.
defer lf-pf-level-step ( level x frames -- ... frames next )
: lf-pf-level ( level frames cont -- ... frames next )
  rot 0 2swap ['] lf-pf-level-step lf-pp-call ;
: lf-pf-param ( id -- outcome )
  dup lf-pf-declarable? 0= if drop outcome-unsupported exit then
  lf-pf-mark swap lf-pf-put-name dup lf-pp-pending lf-pf-token?
  if lf-pf-unit outcome-ok else lf-pp-used ! outcome-unsupported then ;
\ Unchecked: level is valid; successors point to earlier levels.
: lf-pf-succs ( level -- base n )
  0 begin over lf-level-tag@ lf-level-tag-succ = while swap lf-level-first@ swap 1+
    repeat ;
: lf-pf-zero? ( level -- flag ) lf-level-tag@ lf-level-tag-zero = ;
\ base n level+: n waits while base prints.
: lf-pf-offset-back ( outcome frames -- outcome frames 0 )
  >r r@ frame-restore swap dup ok? if drop lf-pf-number s" level+" lf-pf-say else nip then
  r> 0 ;
: lf-pf-offset ( base n frames -- ... frames next )
  tuck frame-save ['] lf-pf-offset-back lf-pf-level ;
: lf-pf-succ-level ( level frames -- ... frames next )
  >r lf-pf-succs over lf-pf-zero?
  if nip lf-pf-number outcome-ok r> 0 else r> lf-pf-offset then ;
\ a b level-max and a b level-imax: the tag and the level wait while a
\ prints, the tag while b does.
: lf-pf-binary-word ( tag -- c-addr u )
  lf-level-tag-max = if s" level-max" else s" level-imax" then ;
: lf-pf-binary-end ( outcome frames -- outcome frames 0 )
  >r r@ frame-restore lf-pf-binary-word lf-pf-then-word r> 0 ;
: lf-pf-binary-second ( outcome frames -- ... frames next )
  >r r@ frame-restore swap ok-then?
  if lf-level-second@ r> ['] lf-pf-binary-end lf-pf-level else r> lf-pf-binary-end then ;
: lf-pf-binary ( level frames -- ... frames next )
  >r dup lf-level-tag@ r@ frame-save dup r@ frame-save lf-level-first@
  r> ['] lf-pf-binary-second lf-pf-level ;
\ The step for a level's tag: a CASE with one arm per tag, read as a table.
: lf-pf-level-zero ( level frames -- outcome frames 0 ) >r drop s" 0" lf-pf-say r> 0 ;
: lf-pf-level-param ( level frames -- outcome frames 0 )
  >r lf-level-first@ lf-pf-param r> 0 ;
\ The step of a visit that cannot print its node (a level or a term): invalid.
: lf-pf-invalid-step ( x frames -- outcome frames 0 ) >r drop-invalid r> 0 ;
: lf-pf-level-by ( tag -- xt )
  case lf-level-tag-zero of ['] lf-pf-level-zero endof
    lf-level-tag-succ of ['] lf-pf-succ-level endof
    lf-level-tag-max of ['] lf-pf-binary endof
    lf-level-tag-imax of ['] lf-pf-binary endof
    lf-level-tag-param of ['] lf-pf-level-param endof
    ['] lf-pf-invalid-step swap endcase ;
: lf-pf-level-node ( level x frames -- ... frames next )
  nip over lf-level-valid?
  if over lf-level-tag@ lf-pf-level-by else ['] lf-pf-invalid-step then execute ;
' lf-pf-level-node is lf-pf-level-step

\ Sorts: Prop, l Type for Sort (l + 1), l Sort otherwise. A concrete Sort
\ n prints the same words (they build the symbolic Sort).
: lf-pf-type-end ( outcome frames -- outcome frames 0 ) >r s" Type" lf-pf-then-word r> 0 ;
: lf-pf-sort-end ( outcome frames -- outcome frames 0 ) >r s" Sort" lf-pf-then-word r> 0 ;
: lf-pf-symbolic ( level frames -- ... frames next )
  >r dup lf-level-valid? 0= if drop-invalid r> 0 exit then
  dup lf-pf-zero? if drop s" Prop" lf-pf-say r> 0 exit then
  dup lf-level-tag@ lf-level-tag-succ =
  if lf-level-first@ r> ['] lf-pf-type-end else r> ['] lf-pf-sort-end then lf-pf-level ;
: lf-pf-concrete ( n -- outcome )
  ?dup 0= if s" Prop" lf-pf-say exit then 1- lf-pf-number s" Type" lf-pf-say ;

\ Constants: the full name, with root: when the words would find something
\ else under it (a variable or universe parameter, a syntax word, a
\ number) or, in a declaration with a dotted name, when a namespace around it
\ holds a constant of the same relative name: the reader looks a name up in
\ the namespaces around the declaration first (Lean's rule), so A.t would
\ find A.c for c; root: is an exact full-name lookup. Then each universe argument and ^.
: lf-pf-universe-ids ( -- addr n )
  lf-pforth lf-pforth-decl @ ?dup 0= if 0 0 exit then
  dup lf-fdecl-universe swap lf-fdecl-universes @ 0 max lf-decl-universe-capacity min ;
: lf-pf-decl-universe? ( id -- flag )
  lf-pf-universe-ids 0 ?do 2dup i cells + @ = if 2drop true unloop exit then loop
  2drop false ;
: lf-pf-dotted-decl? ( -- flag )
  lf-pforth lf-pforth-decl @ ?dup 0= if false exit then
  lf-fdecl-name @ ?dup 0= if false exit then lf-name-prefix@ 0<> ;
\ Whether a constant is named: the input's (print --lf, the outline); the
\ authoring words set their own (src/author/runner.fs).
defer lf-pf-const-exists? ( name -- flag )
: lf-pf-input-const? ( name -- flag ) lf-input-newest 0< 0= ;
' lf-pf-input-const? is lf-pf-const-exists?
\ The name id with base put in front of its components (base.c for c); false
\ when the name store refuses it (the caller then assumes the worst).
: lf-pf-graft-part ( base id -- id' flag )
  dup lf-name-tag@ lf-name-tag-str =
  if swap >r lf-name-text r> -rot lf-name-str
  else swap >r lf-name-payload r> swap lf-name-num then ;
: lf-pf-graft ( base id -- id' flag )
  dup 0= if drop true exit then
  dup >r lf-name-prefix@ recurse 0= if r> drop 0 false exit then r> lf-pf-graft-part ;
\ Whether namespace P around the declaration holds a constant P.c, which the
\ reader would find first for c.
: lf-pf-captured-in? ( id P -- flag )
  swap lf-pf-graft if lf-pf-const-exists? else drop true then ;
: lf-pf-captured? ( id -- flag )
  lf-pforth lf-pforth-decl @ lf-fdecl-name @ lf-name-prefix@
  begin dup while 2dup lf-pf-captured-in? if 2drop true exit then lf-name-prefix@ repeat
  2drop false ;
: lf-pf-capturable? ( id -- flag ) lf-pf-dotted-decl? if lf-pf-captured? else drop false then ;
: lf-pf-root? ( id -- flag )
  dup lf-pf-capturable? if drop true exit then
  dup lf-pf-decl-universe? if drop true exit then
  lf-pf-mark swap lf-pf-put-name dup lf-pp-pending 2dup lf-pf-token? 0= -rot 0 lf-pp-any?
    or
  swap lf-pp-used ! ;
: lf-pf-const-name ( id -- outcome )
  dup lf-pf-declarable? 0= if drop outcome-unsupported exit then
  lf-pf-mark over lf-pf-root? if s" root: " lf-pp-put then swap lf-pf-put-name lf-pf-unit
  outcome-ok ;
\ Each universe argument from index i on, then ^: the levels (addr), their
\ number and the next index wait while one prints.
defer lf-pf-args ( addr n i frames -- ... frames next )
: lf-pf-args-back ( outcome frames -- ... frames next )
  3 lf-pp-failed? if 0 exit then s" ^" lf-pf-text dup >r lf-pp-restore3 r> lf-pf-args ;
: lf-pf-args-next ( addr n i frames -- ... frames next )
  >r 2dup > 0= if 2drop drop outcome-ok r> 0 exit then
  r@ lf-pp-keep-next nip lf-pp-level-at r> ['] lf-pf-args-back lf-pf-level ;
' lf-pf-args-next is lf-pf-args
: lf-pf-universe-args ( term frames -- ... frames next )
  >r lf-pp-const-levels 0= if outcome-invalid r> 0 exit then 0 r> lf-pf-args ;
: lf-pf-const ( term frames -- ... frames next )
  >r dup lf-pp-const-name 0= if drop-invalid r> 0 exit then
  lf-pf-const-name ok-then? if r> lf-pf-universe-args else r> 0 then ;

\ Binders: the domain, then kind: NAME, then the body with the binder in
\ scope, then fun or forall; or A B -> for an arrow. A binder with no
\ entry in the side table is explicit and anonymous. A term is a visit;
\ lf-pf-term asks for one, continuing with cont.
defer lf-pf-term-step ( term x frames -- ... frames next )
: lf-pf-term ( term frames cont -- ... frames next )
  rot 0 2swap ['] lf-pf-term-step lf-pp-call ;
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
\ A binder's domain, then kind: NAME and the binder in scope, a part of a
\ visit: node waits while the domain prints.
: lf-pf-head-back ( outcome frames -- ... frames next )
  >r r@ frame-restore swap ok-then? 0= if r> 0 exit then
  dup lf-pf-opener ok-then? if lf-pf-bind-visible then r> 0 ;
: lf-pf-head ( node frames cont -- ... frames next )
  over frame-save >r dup r@ frame-save lf-term-first@ r> ['] lf-pf-head-back lf-pf-term ;
\ Then the body, fun or forall (lam? says which): lam? waits under the
\ head, node while the head prints.
: lf-pf-binder-word ( lam? -- c-addr u ) if s" fun" else s" forall" then ;
: lf-pf-binder-end ( outcome frames -- outcome frames 0 )
  >r 1 lf-pp-unbind r@ frame-restore lf-pf-binder-word lf-pf-then-word r> 0 ;
: lf-pf-binder-body ( outcome frames -- ... frames next )
  >r r@ frame-restore swap ok-then? 0= if r@ frame-restore drop r> 0 exit then
  lf-term-second@ r> ['] lf-pf-binder-end lf-pf-term ;
: lf-pf-binder ( node lam? frames -- ... frames next )
  >r r@ frame-save dup r@ frame-save r> ['] lf-pf-binder-body lf-pf-head ;
: lf-pf-loose-name? ( id -- flag ) dup 0= if drop true else lf-pp-hygienic? then ;
: lf-pf-arrow? ( pi -- flag outcome )
  dup lf-pp-kind lf-binder-default <> if drop false outcome-ok exit then
  dup lf-pf-binder-name drop lf-pf-loose-name? 0= if drop false outcome-ok exit then
  lf-term-second@ 0 lf-pp-loose? >r 0= r> ;
\ A B ->: pi waits while A prints.
: lf-pf-arrow-end ( outcome frames -- outcome frames 0 )
  >r 1 lf-pp-unbind s" ->" lf-pf-then-word r> 0 ;
: lf-pf-arrow-body ( outcome frames -- ... frames next )
  >r r@ frame-restore swap ok-then? 0= if r> 0 exit then
  lf-pf-bind-arrow ok-then? 0= if r> 0 exit then
  lf-term-second@ r> ['] lf-pf-arrow-end lf-pf-term ;
: lf-pf-arrow ( pi frames -- ... frames next )
  >r dup r@ frame-save lf-term-first@ r> ['] lf-pf-arrow-body lf-pf-term ;
: lf-pf-pi ( pi frames -- ... frames next )
  >r dup lf-pf-arrow? ok-then2? 0= if r> 0 exit then
  if r> lf-pf-arrow else false r> lf-pf-binder then ;
\ f a $: app waits while f prints.
: lf-pf-app-end ( outcome frames -- outcome frames 0 ) >r s" $" lf-pf-then-word r> 0 ;
: lf-pf-app-arg ( outcome frames -- ... frames next )
  >r r@ frame-restore swap ok-then?
  if lf-term-second@ r> ['] lf-pf-app-end lf-pf-term else r> 0 then ;
: lf-pf-app ( app frames -- ... frames next )
  >r dup r@ frame-save lf-term-first@ r> ['] lf-pf-app-arg lf-pf-term ;

\ A term's visit: its node, then its labels and notes, the term waiting
\ meanwhile. The step for the node's tag: a CASE with one arm per tag,
\ read as a table.
: lf-pf-var-step ( term frames -- outcome frames 0 ) >r lf-term-first@ lf-pf-var r> 0 ;
: lf-pf-sort-step ( term frames -- outcome frames 0 )
  >r lf-term-first@ lf-pf-concrete r> 0 ;
: lf-pf-symbolic-step ( term frames -- ... frames next )
  >r lf-term-first@ r> lf-pf-symbolic ;
\ A number literal leaf: n lit# (one cell; a longer one is unsupported). A
\ projection leaf: i proj# NAME, the full name of the structure. Both are
\ applied with $, as Lean's Expr.lit and Expr.proj are (the projection
\ to its term).
: lf-pf-lit-step ( leaf frames -- outcome frames 0 )
  >r dup lf-lit-small? over lf-lit-cell 0< 0= and
  if lf-lit-cell lf-pf-number s" lit#" lf-pf-say else drop outcome-unsupported then r> 0 ;
\ A string literal: unsupported, as the authoring words have no word for
\ one yet (a follow-up of plan task 5.2.3, strings: str#), so its
\ declaration is not written.
: lf-pf-str-step ( leaf frames -- outcome frames 0 ) nip outcome-unsupported swap 0 ;
: lf-pf-proj-step ( leaf frames -- outcome frames 0 )
  >r dup lf-proj-name lf-pf-declarable? 0= if drop outcome-unsupported r> 0 exit then
  dup lf-proj-idx lf-pf-number
  lf-pf-mark s" proj# " lf-pp-put swap lf-proj-name lf-pf-put-name lf-pf-unit
  outcome-ok r> 0 ;
: lf-pf-lam ( lam frames -- ... frames next ) true swap lf-pf-binder ;
: lf-pf-node-by ( tag -- xt )
  case lf-tag-bvar of ['] lf-pf-var-step endof
    lf-tag-sort of ['] lf-pf-sort-step endof
    lf-tag-symbolic-sort of ['] lf-pf-symbolic-step endof
    lf-tag-app of ['] lf-pf-app endof
    lf-tag-lam of ['] lf-pf-lam endof
    lf-tag-pi of ['] lf-pf-pi endof
    lf-tag-constant of ['] lf-pf-const endof
    lf-tag-lit of ['] lf-pf-lit-step endof
    lf-tag-str of ['] lf-pf-str-step endof
    lf-tag-proj of ['] lf-pf-proj-step endof
    ['] lf-pf-invalid-step swap endcase ;
: lf-pf-noted-end ( outcome frames -- outcome frames 0 )
  >r r@ frame-restore swap ok-then? if lf-pf-notes then r> 0 ;
: lf-pf-noted ( term x frames -- ... frames next )
  nip 2dup frame-save ['] lf-pf-noted-end over frame-save
  over lf-pp-tag if lf-pf-node-by else ['] lf-pf-invalid-step then execute ;
' lf-pf-noted is lf-pf-term-step

\ Declarations.
: lf-pf-keyword ( kind -- c-addr u )
  case lf-decl-theorem of s" theorem" endof lf-decl-def of s" def" endof
    lf-decl-axiom of s" axiom" endof s" import-stub" rot endcase ;
: lf-pf-kind? ( decl -- flag ) lf-fdecl-kind @ lf-decl-theorem lf-decl-stub between? ;
: lf-pf-modifier ( decl -- ) lf-fdecl-protected @ if s" protected " lf-pp-put then ;
: lf-pf-header ( decl -- outcome )
  dup lf-pf-kind? 0= if drop-invalid exit then
  dup lf-fdecl-name @ dup lf-pf-declarable? 0= if 2drop outcome-unsupported exit then
  0 lf-pf-open lf-pf-mark rot dup lf-pf-modifier lf-fdecl-kind @ lf-pf-keyword lf-pp-put
  s"  " lf-pp-put swap lf-pf-put-name lf-pf-unit outcome-ok ;
: lf-pf-universe ( id -- outcome )
  dup lf-pf-declarable? 0= if drop outcome-unsupported exit then
  2 lf-pf-open lf-pf-mark s" universe " lf-pp-put swap lf-pf-put-name lf-pf-unit
    outcome-ok ;
: lf-pf-universes ( -- outcome )
  lf-pf-universe-ids 0 ?do dup i cells + @ lf-pf-universe ok-then? 0= if unloop exit then
    loop drop outcome-ok ;
\ A parameter: its own line, then its binder stays in scope; a part of
\ the declaration's visit, as is a body on its own line.
: lf-pf-param-line ( binder frames cont -- ... frames next ) 2 lf-pf-open lf-pf-head ;
: lf-pf-same-binder? ( pi lam -- flag )
  lf-pf-binder-name rot lf-pf-binder-name rot = >r = r> and ;
: lf-pf-shares? ( type value -- flag )
  over lf-tag-pi lf-pp-is? over lf-tag-lam lf-pp-is? and 0= if 2drop false exit then
  2dup lf-term-first@ swap lf-term-first@ <> if 2drop false exit then lf-pf-same-binder? ;
: lf-pf-bodies ( type value -- type' value' ) lf-term-second@ swap lf-term-second@ swap ;
: lf-pf-body ( term frames cont -- ... frames next ) 2 lf-pf-open lf-pf-term ;
\ A definition: its parameters while type and value share them (both
\ wait while one prints), then the type (the value waits), := and the
\ value.
defer lf-pf-def-params ( type value frames -- ... frames next )
: lf-pf-def-next ( outcome frames -- ... frames next )
  >r r@ lf-pp-restore2 rot ok-then2? if lf-pf-bodies r> lf-pf-def-params else r> 0 then ;
: lf-pf-def-value ( outcome frames -- ... frames next )
  >r r@ frame-restore swap ok-then? 0= if r> 0 exit then
  0 lf-pf-open s" :=" lf-pf-text r> ['] frame-return lf-pf-body ;
: lf-pf-def-from ( type value frames -- ... frames next )
  >r 2dup lf-pf-shares?
  if 2dup r@ lf-pp-save2 drop r> ['] lf-pf-def-next lf-pf-param-line exit then
  r@ frame-save r> ['] lf-pf-def-value lf-pf-body ;
' lf-pf-def-from is lf-pf-def-params
: lf-pf-definition ( decl frames -- ... frames next )
  >r dup lf-fdecl-type @ swap lf-fdecl-value @ r> lf-pf-def-params ;
\ A statement: the leading Pi binders that do not print as ->, a line
\ each (the type waits while one prints), then the type.
defer lf-pf-type-params ( type frames -- ... frames next )
: lf-pf-type-next ( outcome frames -- ... frames next )
  >r r@ frame-restore swap ok-then?
  if lf-term-second@ r> lf-pf-type-params else r> 0 then ;
: lf-pf-type-from ( type frames -- ... frames next )
  >r dup lf-tag-pi lf-pp-is? 0= if r> ['] frame-return lf-pf-body exit then
  dup lf-pf-arrow? dup ok? 0= if nip nip r> 0 exit then drop
  if r> ['] frame-return lf-pf-body exit then
  dup r@ frame-save r> ['] lf-pf-type-next lf-pf-param-line ;
' lf-pf-type-from is lf-pf-type-params
: lf-pf-statement ( decl frames -- ... frames next )
  >r lf-fdecl-type @ dup 0< if drop outcome-ok r> 0 exit then r> lf-pf-type-params ;
: lf-pf-parts ( decl frames -- ... frames next )
  over lf-fdecl-kind @ lf-decl-def > if lf-pf-statement else lf-pf-definition then ;
: lf-pf-end ( decl -- outcome )
  0 lf-pf-open lf-pf-mark s" end " lf-pp-put swap lf-fdecl-name @ lf-pf-put-name
    lf-pf-unit
  lf-pf-eol 1 lf-pp-emit 0 lf-pf-column ! outcome-ok ;
\ The declaration's visit: header and universes at once, then its parts,
\ the declaration waiting for its end line.
: lf-pf-decl-end ( outcome frames -- outcome frames 0 )
  >r r@ frame-restore swap ok-then? if lf-pf-end then r> 0 ;
: lf-pf-declaration ( decl x frames -- ... frames next )
  >r drop dup lf-pf-header ok-then? 0= if r> 0 exit then
  lf-pf-universes ok-then? 0= if r> 0 exit then
  dup r@ frame-save ['] lf-pf-decl-end r@ frame-save r> lf-pf-parts ;

\ Public words; see the header.
: lf-pf-start ( decl -- ) lf-pforth /lf-pforth erase lf-pforth lf-pforth-decl ! ;
: lf-print-forth-term ( term fuel -- outcome )
  lf-print-ready? 0= if drop-invalid exit then
  0 lf-pf-start 0 ['] lf-pf-term-step lf-pp-run lf-pp-finish ;
: lf-print-forth-decl ( decl fuel -- outcome )
  lf-print-ready? 0= if drop-invalid exit then
  dup lf-pf-start 0 ['] lf-pf-declaration lf-pp-run lf-pp-finish 0 lf-pf-start ;

\ The LeanForth syntax words (ADR 0017 §6-§11), the fixed vocabulary of
\ proof files: LF-WORDS. Each is one of Lean's keywords or contains a
\ character no unquoted Lean identifier has (rule R1), so no name an
\ author can write in Lean is a syntax word, and it is checked against the
\ term printer's list of the words it writes (print-forth.fs) when it
\ loads. Stack effects are on LeanForth values (values.fs): t a term, l a
\ universe level (or a number), c a constant, n a number. Forms the term
\ store cannot hold yet (literals, let, have, projections, strings,
\ tactic blocks, holes, import) stop with "not supported yet". Untrusted
\ authoring code. No state of its own.

require ../lib/lib.fs
require ./declarations.fs

\ Comments, with Forth's meanings, on one line: a ( comment must end on
\ its line, or the text after it would silently become comment.
: lfa-w-backslash ( -- ) source nip >in ! lfa-read! ;
: lfa-closed? ( c-addr u -- flag ) chars + source chars + <> ;
: lfa-w-paren ( -- ) [char] ) parse lfa-closed? lfa-e-comment-end lfa-must lfa-read! ;

\ Declarations: theorem NAME, def NAME, axiom NAME, import-stub NAME;
\ end NAME closes a declaration or a namespace.
: lfa-w-theorem ( -- ) lf-decl-theorem lfa-declare ;
: lfa-w-def ( -- ) lf-decl-def lfa-declare ;
: lfa-w-axiom ( -- ) lf-decl-axiom lfa-declare ;
: lfa-w-import-stub ( -- ) lf-decl-stub lfa-declare ;
\ Errors of end point at end itself, so its name is not made current.
: lfa-w-end ( -- )
  lfa-above parse-name dup 0<> lfa-e-no-name lfa-must lfa-read!
  lfa-inside? if lfa-end-declaration else rot drop lfa-end-namespace then ;

\ Binders: t explicit: NAME and the other kinds; fun and forall close.
: lfa-w-explicit ( t -- ) 1 lfa-args lf-binder-default lfa-binder-word ;
: lfa-w-implicit ( t -- ) 1 lfa-args lf-binder-implicit lfa-binder-word ;
: lfa-w-strict ( t -- ) 1 lfa-args lf-binder-strict lfa-binder-word ;
: lfa-w-instance ( t -- ) 1 lfa-args lf-binder-instance lfa-binder-word ;
: lfa-w-fun ( t -- t' ) lfa-closing lf-tag-lam lfa-close ;
: lfa-w-forall ( t -- t' ) lfa-closing lf-tag-pi lfa-close ;
: lfa-two-terms ( a b -- ta tb ) swap lfa>term swap lfa>term ;
: lfa-w-arrow ( a b -- t ) 2 lfa-args lfa-two-terms lfa-here lfa-arrow true
  lfa-term-value ;

\ Terms: f a $, c l ^, Prop, l Type, l Sort, n var#, root: NAME.
: lfa-w-app ( f a -- t ) 2 lfa-args lfa-two-terms lfa-here lfa-app lfa-term-value ;
: lfa-w-univ ( c l -- c' )
  2 lfa-args lfa>level over lfa>constant lfa-chain# lf-cref-argument-capacity <
  lfa-e-many-levels lfa-must lfa-more-levels ;
: lfa-sort-value ( level -- t ) lfa-here lfa-sort lfa-term-value ;
: lfa-w-prop ( -- t ) 0 lfa-args 0 lfa-sort-value ;
: lfa-w-type ( l -- t ) 1 lfa-args lfa>level lfa-succ lfa-sort-value ;
: lfa-w-sort ( l -- t ) 1 lfa-args lfa>level lfa-sort-value ;
: lfa-w-var ( n -- t )
  1 lfa-args lfa>count dup lfa-depth < lfa-e-var-index lfa-must lfa-here lfa-bvar
  lfa-term-value ;
: lfa-w-root ( "name" -- c )
  0 lfa-args lfa-name-token lfa-const-named 0= if lfa-e-unknown-constant lfa-fail then
  lfa-const-value ;

\ Levels: l n level+, a b level-max, a b level-imax.
: lfa-w-level+ ( l n -- l' )
  2 lfa-args lfa>count dup lf-level-capacity < lfa-e-levels-full lfa-must
  swap lfa>level swap lfa-succs lfa-level-value ;
: lfa-two-levels ( a b -- la lb ) swap lfa>level swap lfa>level ;
: lfa-w-max ( a b -- l ) 2 lfa-args lfa-two-levels lfa-max lfa-level-value ;
: lfa-w-imax ( a b -- l ) 2 lfa-args lfa-two-levels lfa-imax lfa-level-value ;

\ Labels and notes on the term on top: label: NAME, note" text",
\ ai-note" text". The term gets a node of its own (build.fs) and a new
\ value; the note records the position of the word that made it.
: lfa-step ( t -- t' term ) lfa>term+ lfa-own dup true lfa-term-value swap ;
: lfa-note! ( term c-addr u kind -- i )
  2>r swap 2r> rot lf-note-add ok? lfa-e-notes-full lfa-must ;
: lfa-annotate ( t c-addr u kind -- t' i ) 2>r >r lfa-step r> 2r> lfa-note! ;
: lfa-label-free ( c-addr u -- c-addr u )
  2dup lfa-this lfa-decl-notes @ lf-note-label? 0= lfa-e-label-twice lfa-must ;
: lfa-w-label ( t -- t' )
  1 lfa-args lfa-here >r lfa-name-token lfa-label-free lf-note-label lfa-annotate
  r> lf-note-source! ;
: lfa-note-text ( -- c-addr u )
  [char] " parse 2dup lfa-closed? lfa-e-note-end lfa-must lfa-read! ;
: lfa-w-note ( t -- t' )
  1 lfa-args lfa-here >r lfa-note-text lf-note-person lfa-annotate r> lf-note-source! ;
: lfa-w-ai-note ( t -- t' )
  1 lfa-args lfa-here >r lfa-note-text lf-note-ai lfa-annotate r> lf-note-source! ;

\ Forms the term store cannot hold yet.
: lfa-w-sketch ( -- ) lfa-e-sketch lfa-fail ;
: lfa-w-hole ( -- ) lfa-e-hole lfa-fail ;

\ The vocabulary. Each word must be in the printer's list.
: lfa-word ( xt "name" -- )
  >in @ parse-name lf-pf-reserved? 0= abort" words.fs: a word missing in print-forth.fs"
  >in ! lfa-syntax ;
' lfa-w-backslash lfa-word \
' lfa-w-paren lfa-word (
' lfa-w-theorem lfa-word theorem
' lfa-w-def lfa-word def
' lfa-w-axiom lfa-word axiom
' lfa-w-import-stub lfa-word import-stub
' lfa-universe-word lfa-word universe
' lfa-define lfa-word :=
' lfa-w-end lfa-word end
' lfa-namespace-word lfa-word namespace
' lfa-open-word lfa-word open
' lfa-w-explicit lfa-word explicit:
' lfa-w-implicit lfa-word implicit:
' lfa-w-strict lfa-word strict-implicit:
' lfa-w-instance lfa-word instance:
' lfa-w-fun lfa-word fun
' lfa-w-forall lfa-word forall
' lfa-w-arrow lfa-word ->
' lfa-w-app lfa-word $
' lfa-w-univ lfa-word ^
' lfa-w-prop lfa-word Prop
' lfa-w-type lfa-word Type
' lfa-w-sort lfa-word Sort
' lfa-w-level+ lfa-word level+
' lfa-w-max lfa-word level-max
' lfa-w-imax lfa-word level-imax
' lfa-w-var lfa-word var#
' lfa-w-root lfa-word root:
' lfa-w-label lfa-word label:
' lfa-w-note lfa-word note"
' lfa-w-ai-note lfa-word ai-note"
\ Gforth 1.0 warns that _ could be read as a number; LF-WORDS is searched
\ before any number conversion, so _ is this word.
[defined] warnings [if] warnings @ warnings off [then]
' lfa-w-hole lfa-word _
[defined] warnings [if] warnings ! [then]
' lfa-w-sketch lfa-word let:
' lfa-w-sketch lfa-word let
' lfa-w-sketch lfa-word have
' lfa-w-sketch lfa-word field-at
' lfa-w-sketch lfa-word by
' lfa-w-sketch lfa-word s"
' lfa-w-sketch lfa-word import

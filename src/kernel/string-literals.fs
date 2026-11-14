\ String literals in the kernel (plan task 5.2.3, its string part; ADR
\ 0015 L2, L4; Lean 4.35.0 at eb6cafb7): a literal's type (infer_lit,
\ type_checker.cpp 315-321: the constant String), Lean's
\ string_lit_to_constructor (inductive.cpp 1368-1380) and its three
\ callers: reduce_proj_core (type_checker.cpp 420-422) and
\ inductive_reduce_rec (inductive.h 94-97), both through iota.fs, and
\ try_string_lit_expansion (type_checker.cpp 1104-1117), step 13 of
\ is_def_eq_core (1200-1201), which this file sets as defeq.fs's hook
\ lf-dq-string-step. [kernel] code: not through the review gate
\ (AGENTS.md).
\
\ string_lit_to_constructor turns the literal s (core/string-literals.fs)
\ into
\   String.ofList (List.cons.{0} Char (Char.ofNat c1) (List.cons.{0} Char
\     ... (List.cons.{0} Char (Char.ofNat cn) (List.nil.{0} Char))))
\ over s's code points c1 .. cn (utf8_decode), each a natural-number
\ literal (core/literals.fs), the list built from the last character to
\ the first, as Lean builds it. The constants are Lean's by name only
\ (L5), whatever the environment declares under those names; List.cons
\ and List.nil take the universe level zero. The term is made where a rule
\ needs it, new each time (as Lean's), never kept: four new nodes and one
\ unit of the frames' fuel per character, so a long literal costs fuel and
\ room, and running out of either is exhausted or full, never a verdict.
\ Bytes that are no UTF-8 character are invalid (the leaf's fields passed
\ the audit, and lf-str-new took valid UTF-8 only, so only corruption).
\
\ The callers, each as Lean's. lf-str-whnf-call puts the constructor form
\ in whnf (whnf.fs, a child visit); in iota.fs the result takes the
\ literal's place as the projected term or the recursor's major premise.
\ Step 13 of a comparison: when t is a string literal and s an application
\ of the constant String.ofList without universe arguments to one argument
\ (app_fn(s) == String.ofList), the answer is is_def_eq_core of t's
\ constructor form in whnf and s, yes or no; tried with tn and sn, then
\ with sn and tn; when neither applies, the comparison goes on to step 14
\ (defeq.fs, lf-dq-unit-step).
\
\ State: the expansion's constants, its literal and its frames in one
\ module record, and two growable arrays, the literal's code points and the
\ one universe argument, all members of the checker context
\ (lib/context.fs), filled and used within one step (lf-str-expand calls
\ no pass).

require ../lib/lib.fs
require ../lib/bytes.fs
require ../lib/slab.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/diagnostics.fs
require ../core/generation-handles.fs
require ../core/literals.fs
require ../core/names.fs
require ../core/string-literals.fs
require ../core/terms.fs
require ./defeq.fs
require ./whnf.fs

begin-structure /lf-sx
  field: lf-sx-cons      \ List.cons.{0} Char
  field: lf-sx-ofnat     \ Char.ofNat
  field: lf-sx-leaf      \ the literal being expanded
  field: lf-sx-frames    \ whose fuel pays for it
  field: lf-sx-count     \ its code points decoded so far
end-structure
/lf-sx context-record: lf-sx
2 cells context-slab: lf-sx-pairs   \ the universe argument zero, one pair
1 cells context-slab: lf-sx-codes   \ the literal's code points, in order

: lf-sx-site ( -- site ) c" string-literals lf-str-expand" ;

\ ---------------------------------------------------------------------------
\ Constants by name (L5): an interned name prefix.part, the constant of
\ that name at the first n universe arguments of the pair array, and an
\ application; full without room.
: lf-sx-name ( prefix c-addr u -- id outcome )
  lf-name-str room-result ;
: lf-sx-dotted ( c-addr u prefix-addr prefix-u -- id outcome )
  0 -rot lf-sx-name ok-then? 0= if >r 2drop r> no-result exit then -rot lf-sx-name ;
: lf-sx-const ( id n -- node outcome )
  >r lf-name-generation @ 0 lf-sx-pairs slab-at r> lf-cref-new
  0= if -1 outcome-full exit then
  lf-cterm-new if drop outcome-ok else -1 outcome-full then ;
: lf-sx-app ( f a -- node outcome ) lf-term-app room-result ;
\ prefix.part without universe arguments.
: lf-sx-plain ( c-addr u prefix-addr prefix-u -- node outcome )
  lf-sx-dotted ok-then? if 0 lf-sx-const else no-result then ;
\ The level zero as the one universe argument (Lean's level()).
: lf-sx-zero! ( -- outcome )
  1 lf-sx-pairs slab-hold dup ok? 0= if exit then drop
  lf-hlevel-zero 0= if outcome-full exit then
  swap 0 lf-sx-pairs slab-at 2! outcome-ok ;
: lf-sx-at-zero ( id outcome -- node outcome )
  ok-then? 0= if no-result exit then
  lf-sx-zero! ok-then? if 1 lf-sx-const else no-result then ;
: lf-sx-char ( -- node outcome )
  0 s" Char" lf-sx-name ok-then? if 0 lf-sx-const else no-result then ;
\ List.cons.{0} Char or List.nil.{0} Char, for c-addr u cons or nil.
: lf-sx-list ( c-addr u -- node outcome )
  s" List" lf-sx-dotted lf-sx-at-zero ok-then? 0= if no-result exit then
  lf-sx-char ok-then? 0= if nip no-result exit then lf-sx-app ;

\ A literal's type (infer_lit): the constant String.
: lf-str-type ( -- node outcome )
  0 s" String" lf-sx-name ok-then? if 0 lf-sx-const else no-result then ;

\ ---------------------------------------------------------------------------
\ string_lit_to_constructor. One unit of the frames' fuel per character.
: lf-sx-pay ( -- outcome )
  lf-sx lf-sx-frames @ dup frame-fuel @ 0> if -1 swap frame-fuel +! outcome-ok exit then
  lf-sx-site lf-diag-frames-fuel outcome-exhausted ;
\ utf8_decode: the literal's code points, in order, into lf-sx-codes and
\ their number into lf-sx-count; invalid at bytes that are no UTF-8
\ character, full without room. The character at the start of a text:
\ its code point and its bytes, 0 bytes for none.
: lf-sx-first ( c-addr u -- code n )
  over swap utf8-length dup if tuck utf8-decode swap else nip 0 swap then ;
: lf-sx-keep ( code i -- outcome )
  dup 1+ lf-sx-codes slab-hold dup ok? 0= if nip nip exit then drop
  lf-sx-codes slab-at ! outcome-ok ;
: lf-sx-decode-step ( c-addr u -- c-addr' u' outcome )
  2dup lf-sx-first dup 0= if 2drop outcome-invalid exit then
  >r lf-sx lf-sx-count @ lf-sx-keep dup ok? 0= if r> drop exit then drop
  1 lf-sx lf-sx-count +! r> /string outcome-ok ;
: lf-sx-decode ( leaf -- outcome )
  0 lf-sx lf-sx-count ! lf-str-text
  begin dup while lf-sx-decode-step dup ok? 0= if nip nip exit then drop repeat
  2drop outcome-ok ;
\ List.cons.{0} Char (Char.ofNat code) applied to the list r.
: lf-sx-cell ( code r -- r' outcome )
  >r lf-hterm-cell 0= if r> drop -1 outcome-full exit then drop
  lf-sx lf-sx-ofnat @ swap lf-sx-app ok-then? 0= if r> drop no-result exit then
  lf-sx lf-sx-cons @ swap lf-sx-app ok-then? 0= if r> drop no-result exit then
  r> lf-sx-app ;
\ Code point i - 1, the last not yet in the list r.
: lf-sx-step ( r i -- r' i' outcome )
  lf-sx-pay dup ok? 0= if nip nip -1 0 rot exit then drop
  1- tuck lf-sx-codes slab-at @ swap lf-sx-cell >r swap r> ;
: lf-sx-list-of ( nil n -- list outcome )
  begin dup while lf-sx-step dup ok? 0= if nip exit then drop repeat
  drop outcome-ok ;
: lf-sx-ready ( leaf frames -- outcome )
  lf-sx lf-sx-frames ! dup lf-sx lf-sx-leaf ! lf-sx-decode dup ok? 0= if exit then drop
  s" cons" lf-sx-list ok-then? 0= if exit then lf-sx lf-sx-cons !
  s" ofNat" s" Char" lf-sx-plain ok-then? 0= if exit then lf-sx lf-sx-ofnat !
  outcome-ok ;
\ The constructor form of the string literal leaf, on frames' fuel.
: lf-str-expand ( leaf frames -- node outcome )
  lf-sx-ready dup ok? 0= if no-result exit then drop
  s" nil" lf-sx-list ok-then? 0= if no-result exit then
  lf-sx lf-sx-count @ lf-sx-list-of ok-then? 0= if no-result exit then
  s" ofList" s" String" lf-sx-plain ok-then? 0= if nip no-result exit then
  swap lf-sx-app ;

\ The constructor form of leaf put in whnf, a child visit on frames that
\ continues with cont ( node outcome frames -- ... frames next ); a failed
\ expansion goes on to cont at once with ( -1 outcome ).
: lf-str-whnf-call ( leaf frames cont -- ... frames next )
  >r tuck lf-str-expand ok-then? 0= if no-result rot r> exit then
  swap r> lf-whnf-call ;

\ ---------------------------------------------------------------------------
\ Step 13 (try_string_lit_expansion). app_fn(s) == String.ofList: s an
\ application whose function is the constant String.ofList, named by its
\ components, without universe arguments.
: lf-sx-of-list? ( name -- flag )
  dup s" ofList" lf-whnf-part? 0= if drop false exit then
  lf-name-prefix@ dup s" String" lf-whnf-part?
  if lf-name-prefix@ lf-whnf-anon? else drop false then ;
: lf-sx-string-app? ( s -- flag )
  dup lf-term-tag@ lf-tag-app <> if drop false exit then
  lf-term-first@ dup lf-whnf-const? 0= if drop false exit then
  lf-whnf-cref dup lf-crec-arity @ if drop false exit then lf-crec-name @ lf-sx-of-list? ;
\ try_string_lit_expansion_core(t, s) applies.
: lf-sx-applies? ( t s -- flag ) lf-sx-string-app? swap lf-str-leaf? and ;
: lf-sx-compared ( flag outcome frames -- ... frames next )
  >r ok-then? if r> lf-dq-end else r> lf-dq-end-failed then ;
\ After t's constructor form is in whnf: is_def_eq_core of it and s,
\ saved across the visit.
: lf-sx-whnfed ( t' outcome frames -- ... frames next )
  >r r@ frame-restore -rot ok-then? 0= if nip r> lf-dq-end-failed exit then
  swap r> ['] lf-sx-compared lf-dq-call ;
: lf-sx-expand-try ( t s frames -- ... frames next )
  tuck frame-save ['] lf-sx-whnfed lf-str-whnf-call ;
:noname ( frames -- ... frames next )
  dup lf-dq-sides 2dup lf-sx-applies? if rot lf-sx-expand-try exit then
  swap 2dup lf-sx-applies? if rot lf-sx-expand-try exit then
  2drop lf-dq-unit-step ; is lf-dq-string-step

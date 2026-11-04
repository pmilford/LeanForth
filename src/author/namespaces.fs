\ Namespaces and the resolution of constant names (ADR 0017 §9), as pinned
\ Lean 4.35 does them (src/lean/Lean/ResolveName.lean, Elab/Open.lean,
\ Elab/BuiltinCommand.lean, Elab/Declaration.lean of the toolchain):
\ - namespace A.B enters one scope per part (A, then A.B); end NAME
\   leaves one scope per part of NAME, each part naming its scope, last
\   part innermost, and with them every namespace opened inside them.
\ - A namespace is known once it is entered or is a prefix of a declared
\   name (Lean's isNamespace). open N opens N inside the current
\   namespace or the nearest one around it that has it (or N itself),
\   and O.N for every namespace O open now: all of them; none is an error.
\ - The current namespace is the innermost one entered; while a
\   declaration is made it is that declaration's own prefix (Lean reads
\   def N.f as namespace N def f end N).
\ - A constant's name T (resolveGlobalName): the first of P.T, for the
\   current namespace P and each namespace around it, innermost first,
\   that is a constant; otherwise T at the root and O.T for each open
\   namespace O, which must all be the same constant. Through a namespace
\   (P.T or O.T) a T of one part never finds a protected constant. Lean
\   then tries each candidate against the expected type; the authoring
\   words have no types, so two candidates stop the run as ambiguous.
\   Lean's aliases (export) and private names would add candidates; the
\   words make neither (export stops as not supported yet), so here there
\   are none.
\ Names here are texts of parts joined by dots. Untrusted authoring code.
\ State: two records and one store in the checker context: lfa-knowns
\ (the namespaces known, by name, and a scratch text), lfa-spaces (the
\ scopes entered and the namespaces opened in them, oldest first).

require ../lib/lib.fs
require ./groups.fs

\ The name after a word, made the current token; a word with no name after
\ it on its line stops with the error at the word.
: lfa-name-token ( -- c-addr u ) parse-name dup 0<> lfa-e-no-name lfa-must 2dup
  lfa-token! ;

\ Name texts (the dots in them: source.fs).
: lfa-last-part ( c-addr u -- c-addr' u' ) 2dup lfa-cut dup if 1+ then nip /string ;
\ Every part of a name a word is made for: not empty, not number-like.
: lfa-part-ok? ( c-addr u -- flag ) dup 0<> >r lfa-number-like? 0= r> and ;
: lfa-parts-ok? ( c-addr u -- flag )
  begin 2dup lfa-dot >r over r@ lfa-part-ok? 0= if r> drop 2drop false exit then
    r> 1+ over min /string dup 0= until 2drop true ;
: lfa-word-name ( c-addr u -- c-addr u )
  2dup lfa-empty-part? 0= lfa-e-bad-name lfa-must
  2dup lfa-parts-ok? lfa-e-bad-name lfa-must ;

\ Texts of up to 256 characters in a record.
256 constant lfa-text-capacity
begin-structure /lfa-text
  field: lfa-text-length
  lfa-text-capacity +field lfa-text-chars
end-structure
: lfa-text ( text -- c-addr u ) dup lfa-text-chars swap lfa-text-length @ ;
: lfa-text-clear ( text -- ) 0 swap lfa-text-length ! ;
: lfa-text+ ( c-addr u text -- )
  2dup lfa-text-length @ + lfa-text-capacity > 0= lfa-e-names-full lfa-must
  dup lfa-text + >r 2dup lfa-text-length +! drop r> swap move ;
: lfa-text-dotted ( c-addr u text -- )
  dup lfa-text-length @ if s" ." 2 pick lfa-text+ then lfa-text+ ;

\ Namespaces known: their full names.
32 constant lfa-known-capacity
1024 constant lfa-known-bytes
begin-structure /lfa-known
  field: lfa-known-offset
  field: lfa-known-length
end-structure
begin-structure /lfa-knowns
  field: lfa-knowns-count
  field: lfa-knowns-used
  lfa-known-capacity /lfa-known * +field lfa-knowns-table
  lfa-known-bytes +field lfa-knowns-bytes
  /lfa-text +field lfa-knowns-scratch     \ a name being joined
end-structure
/lfa-knowns context-record: lfa-knowns
: lfa-known ( i -- known ) /lfa-known * lfa-knowns lfa-knowns-table + ;
: lfa-known# ( -- n ) lfa-knowns lfa-knowns-count @ ;
: lfa-known-name ( i -- c-addr u )
  lfa-known dup lfa-known-offset @ lfa-knowns lfa-knowns-bytes + swap lfa-known-length @ ;
: lfa-known-find ( c-addr u -- i true | false )
  lfa-known# 0 ?do 2dup i lfa-known-name compare 0=
    if 2drop i true unloop exit then loop 2drop false ;
: lfa-known-room? ( u -- flag )
  lfa-known-bytes lfa-knowns lfa-knowns-used @ - upto? lfa-known# lfa-known-capacity <
    and ;
: lfa-known-text! ( c-addr u known -- )
  2dup lfa-known-length ! lfa-knowns lfa-knowns-used @ swap lfa-known-offset !
  tuck lfa-knowns lfa-knowns-bytes lfa-knowns lfa-knowns-used @ + swap move
  lfa-knowns lfa-knowns-used +! ;
: lfa-known-add ( c-addr u -- i )
  dup lfa-known-room? lfa-e-entries-full lfa-must
  lfa-known# dup >r lfa-known lfa-known-text! 1 lfa-knowns lfa-knowns-count +! r> ;
\ The namespace named c-addr u, made known when it is new.
: lfa-known-of ( c-addr u -- i ) 2dup lfa-known-find if nip nip else lfa-known-add then ;
\ Every prefix of a declared name is a namespace.
: lfa-prefixes-known ( c-addr u -- )
  dup 0 ?do over i lfa-dot-at? if over i lfa-known-of drop then loop 2drop ;

\ The namespace prefix p-addr p-u joined to the name x-addr x-u, in the
\ scratch text.
: lfa-scratch ( -- text ) lfa-knowns lfa-knowns-scratch ;
: lfa-joined ( x-addr x-u p-addr p-u -- c-addr u )
  lfa-scratch dup lfa-text-clear lfa-text+ lfa-scratch lfa-text-dotted lfa-scratch
    lfa-text ;

\ Scopes entered and namespaces opened, oldest first.
0 constant lfa-space-entered
1 constant lfa-space-opened
16 constant lfa-space-capacity
begin-structure /lfa-space
  field: lfa-space-known      \ the namespace
  field: lfa-space-kind
end-structure
lfa-space-capacity /lfa-space 0 context-store: lfa-spaces
: lfa-space ( i -- space ) lfa-spaces store-slot ;
: lfa-space# ( -- n ) lfa-spaces store-count @ ;
: lfa-space-name ( space -- c-addr u ) lfa-space-known @ lfa-known-name ;
: lfa-entered? ( space -- flag ) lfa-space-kind @ lfa-space-entered = ;
: lfa-space-push ( known kind -- )
  lfa-spaces store-new-slot lfa-e-namespaces lfa-must drop
  tuck lfa-space-kind ! lfa-space-known ! ;
: lfa-namespaces-reset ( -- ) lfa-spaces store-clear lfa-knowns /lfa-knowns erase ;

\ The current namespace: the innermost one entered, or none (empty).
: lfa-innermost-space ( -- space true | false )
  lfa-space# begin dup while 1- dup lfa-space dup lfa-entered?
    if nip true exit then drop repeat drop false ;
: lfa-current-space ( -- c-addr u )
  lfa-innermost-space if lfa-space-name else 0 0 then ;

\ namespace NAME: a scope for each part, inside the current namespace.
: lfa-outside ( -- ) lfa-inside? 0= lfa-e-namespace-here lfa-must ;
: lfa-enter-part ( c-addr u -- )
  lfa-current-space lfa-joined lfa-known-of lfa-space-entered lfa-space-push ;
: lfa-namespace-word ( -- )
  lfa-outside lfa-name-token lfa-word-name
  begin 2dup lfa-dot >r over r@ lfa-enter-part r> 1+ over min /string dup 0= until
    2drop ;

\ end NAME of a namespace: NAME's parts, last first, name the innermost
\ scopes entered; they go, and every namespace opened in them.
: lfa-entered-below ( i -- j )
  begin 1- dup 0< if exit then dup lfa-space lfa-entered? until ;
: lfa-end-part ( i c-addr u -- j )
  rot lfa-entered-below dup 0< if lfa-e-no-namespace lfa-fail then
  dup >r lfa-space lfa-space-name lfa-last-part compare 0= lfa-e-end-name lfa-must r> ;
: lfa-split-last ( c-addr u -- rest-addr rest-u part-addr part-u )
  2dup lfa-cut 2swap lfa-last-part ;
: lfa-end-namespace ( c-addr u -- )
  2dup lfa-empty-part? 0= lfa-e-end-name lfa-must
  lfa-space# -rot begin dup while lfa-split-last 2>r rot 2r> lfa-end-part -rot repeat
  2drop lfa-spaces store-count ! ;

\ open NAME: the namespaces NAME can mean, each opened.
\ First: P.NAME for the current namespace P or the nearest one around it,
\ else NAME itself (written _root_.NAME or not).
: lfa-unrooted ( c-addr u -- c-addr' u' )
  2dup 7 min s" _root_." compare 0= if 7 /string then ;
: lfa-scoped ( c-addr u -- i true | false )
  lfa-current-space begin dup while 2over 2over lfa-joined lfa-known-find
    if nip nip nip nip true exit then lfa-cut repeat 2drop lfa-unrooted lfa-known-find ;
\ Then: O.NAME for every namespace O open before this open.
: lfa-open-one ( i -- ) lfa-space-opened lfa-space-push ;
: lfa-opened-in ( c-addr u space -- )
  dup lfa-entered? if drop 2drop exit then
  lfa-space-name lfa-joined lfa-known-find if lfa-open-one then ;
: lfa-open-word ( -- )
  lfa-outside lfa-name-token lfa-space# >r 2dup lfa-scoped if lfa-open-one then
  r@ 0 ?do 2dup i lfa-space lfa-opened-in loop 2drop
  lfa-space# r> > lfa-e-unknown-space lfa-must ;

\ A constant's name, the current token, in the namespace p-addr p-u:
\ first the namespaces around, innermost first; then the root and the
\ namespaces open, which must agree. Through a namespace, a name of one
\ part never finds a protected constant (Lean's resolveQualifiedName).
: lfa-one-part? ( c-addr u -- flag ) tuck lfa-dot = ;
: lfa-hidden? ( decl -- flag ) lfa-decl lf-fdecl-protected @ lfa-token lfa-one-part? and ;
: lfa-const-in-space ( p-addr p-u -- decl true | false )
  lfa-token 2swap lfa-joined lfa-const-named 0= if false exit then
  dup lfa-hidden? if drop false else true then ;
: lfa-const-around ( p-addr p-u -- decl true | false )
  begin dup while 2dup lfa-const-in-space if nip nip true exit then lfa-cut repeat
  2drop false ;
: lfa-agree ( found decl -- found' )
  over 0< if nip exit then over = lfa-e-ambiguous lfa-must ;
: lfa-agree-open ( found space -- found' )
  dup lfa-entered? if drop exit then lfa-space-name lfa-const-in-space if lfa-agree then ;
: lfa-const-open ( -- found | -1 )
  -1 lfa-token lfa-const-named if lfa-agree then
  lfa-space# 0 ?do i lfa-space lfa-agree-open loop ;
: lfa-resolve ( p-addr p-u -- decl true | false )
  lfa-const-around if true exit then lfa-const-open dup 0< if drop false else true then ;

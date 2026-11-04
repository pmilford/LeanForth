\ Declarations, universe parameters, binders and namespaces (ADR 0017 §7-§9):
\ the words that open and close scopes. theorem, def, axiom and
\ import-stub NAME start a declaration on an empty stack; universe NAME
\ adds a universe parameter; a binder word takes a domain and reads the
\ variable's name; fun and forall close the innermost binder around the
\ one value above it; := takes the statement, and the binders still open
\ are the parameters; end NAME closes them around the statement (Pi) and
\ the proof (lambda), records the declaration and defines the words of
\ the constant: its full name in LF-CONST and, in each enclosing
\ namespace's wordlist, the rest of the name. namespace NAME and open
\ NAME put a namespace's wordlist in the search order until the
\ enclosing namespace ends. Names are Lean names, read from tokens: parts
\ between dots, a part of digits being a number. Untrusted authoring code:
\ these words build terms; only the checker can accept them.
\ State: three records in the checker context: lfa-current (the
\ declaration being made), lfa-spaces (namespaces in the search order)
\ and lfa-knowns (namespaces met, with their wordlists).

require ../lib/lib.fs
require ./groups.fs

\ Names from tokens.
: lfa-dot ( c-addr u -- n )
  dup >r 0 ?do dup i chars + c@ [char] . = if drop i unloop r> drop exit then loop
  drop r> ;
: lfa-numeric ( prefix c-addr u -- name )
  dup 10 < lfa-e-bad-name lfa-must 0 0 2swap >number 2drop drop lf-name-num
  lfa-e-names-full lfa-must ;
: lfa-intern-part ( prefix c-addr u -- name )
  dup 0<> lfa-e-bad-name lfa-must 2dup lf-pf-digits?
  if lfa-numeric else lf-name-str lfa-e-names-full lfa-must then ;
: lfa-intern-step ( prefix c-addr u -- prefix' c-addr' u' )
  2dup lfa-dot >r rot 2 pick r@ lfa-intern-part -rot r> 1+ over min /string ;
: lfa-last-char ( c-addr u -- char ) + 1- c@ ;
\ The name a token spells: no part may be empty.
: lfa-intern ( c-addr u -- name )
  dup 0<> lfa-e-bad-name lfa-must 2dup lfa-last-char [char] . <> lfa-e-bad-name lfa-must
  0 -rot begin dup while lfa-intern-step repeat 2drop ;
: lfa-anonymous? ( c-addr u -- flag ) lf-pf-anonymous compare 0= ;
\ A binder's name: [anonymous] is the anonymous name.
: lfa-binder-name-of ( c-addr u -- name ) 2dup lfa-anonymous? if 2drop 0 else lfa-intern
  then ;
\ The name after a word, made the current token; a word with no name after
\ it on its line stops with the error at the word.
: lfa-name-token ( -- c-addr u ) parse-name dup 0<> lfa-e-no-name lfa-must 2dup
  lfa-token! ;

\ Texts of up to 256 characters in a record: the declaration's token and
\ full name, a namespace name being made.
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

\ The declaration being made.
begin-structure /lfa-current
  field: lfa-current-decl        \ its index in lfa-decls
  field: lfa-current-entries     \ names defined before it
  /lfa-text +field lfa-current-token
  /lfa-text +field lfa-current-full
end-structure
/lfa-current context-record: lfa-current
: lfa-this ( -- decl ) lfa-current lfa-current-decl @ lfa-decl ;
: lfa-this-kind ( -- kind ) lfa-this lf-fdecl-kind @ ;
: lfa-full ( -- c-addr u ) lfa-current lfa-current-full lfa-text ;

\ Namespaces met: their full names and wordlists.
32 constant lfa-known-capacity
1024 constant lfa-known-bytes
begin-structure /lfa-known
  field: lfa-known-wid
  field: lfa-known-offset
  field: lfa-known-length
end-structure
begin-structure /lfa-knowns
  field: lfa-knowns-count
  field: lfa-knowns-used
  lfa-known-capacity /lfa-known * +field lfa-knowns-table
  lfa-known-bytes +field lfa-knowns-bytes
  /lfa-text +field lfa-knowns-scratch     \ a candidate name for open
end-structure
/lfa-knowns context-record: lfa-knowns
: lfa-known ( i -- known ) /lfa-known * lfa-knowns lfa-knowns-table + ;
: lfa-known# ( -- n ) lfa-knowns lfa-knowns-count @ ;
: lfa-known-name ( known -- c-addr u )
  dup lfa-known-offset @ lfa-knowns lfa-knowns-bytes + swap lfa-known-length @ ;
: lfa-known-find ( c-addr u -- i true | false )
  lfa-known# 0 ?do 2dup i lfa-known lfa-known-name compare 0=
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
  lfa-known# dup >r lfa-known lfa-known-text! wordlist r@ lfa-known lfa-known-wid !
  1 lfa-knowns lfa-knowns-count +! r> ;
\ The namespace named c-addr u, made when it is new.
: lfa-known-of ( c-addr u -- i ) 2dup lfa-known-find if nip nip else lfa-known-add then ;
: lfa-namespace ( c-addr u -- wid ) lfa-known-of lfa-known lfa-known-wid @ ;

\ Namespaces in the search order, oldest first: entered with namespace
\ (the last part of the name the command gave, or an outer part of it)
\ or opened with open.
0 constant lfa-space-entered
1 constant lfa-space-outer
2 constant lfa-space-opened
s" WORDLISTS" environment? 0= [if] 8 [then] 16 min 3 - constant lfa-space-capacity
begin-structure /lfa-space
  field: lfa-space-known      \ the namespace
  field: lfa-space-kind
  field: lfa-space-from       \ entered: where the command's name starts in it
end-structure
lfa-space-capacity /lfa-space 0 context-store: lfa-spaces
: lfa-space ( i -- space ) lfa-spaces store-slot ;
: lfa-space# ( -- n ) lfa-spaces store-count @ ;
: lfa-space-wid ( space -- wid ) lfa-space-known @ lfa-known lfa-known-wid @ ;

\ The search order while a proof runs.
: lfa-order! ( -- )
  lf-consts lfa-space# 0 ?do i lfa-space lfa-space-wid loop
  lf-locals lf-words lfa-space# 3 + set-order ;

: lfa-declarations-reset ( -- )
  lfa-decls store-clear lfa-spaces store-clear lfa-knowns /lfa-knowns erase ;

\ The current namespace: the innermost one entered, or none.
: lfa-entered? ( space -- flag ) lfa-space-kind @ lfa-space-opened <> ;
: lfa-innermost-space ( -- space true | false )
  lfa-space# begin dup while 1- dup lfa-space dup lfa-entered?
    if nip true exit then drop repeat drop false ;
: lfa-current-space ( -- c-addr u )
  lfa-innermost-space if lfa-space-known @ lfa-known lfa-known-name else 0 0 then ;

\ Declarations: kind NAME starts one.
: lfa-root-name? ( c-addr u -- flag )
  2dup s" _root_" compare 0= >r 7 min s" _root_." compare 0= r> or ;
: lfa-end-token! ( c-addr u -- ) lfa-current lfa-current-token dup lfa-text-clear
  lfa-text+ ;
: lfa-full! ( c-addr u -- )
  lfa-current lfa-current-full dup lfa-text-clear lfa-current-space rot lfa-text+
  lfa-current lfa-current-full lfa-text-dotted ;
: lfa-declared? ( c-addr u -- flag )
  2dup lf-consts search-wordlist 0= if 2drop false exit then
  >body lfa-entry-constant lfa-key! lfa-entry-find dup if nip then ;
: lfa-new-decl ( kind name pos -- )
  lfa-decl-new dup lfa-current lfa-current-decl ! lfa-decl
  tuck lfa-decl-at ! tuck lf-fdecl-name ! tuck lf-fdecl-kind !
  -1 over lf-fdecl-type ! -1 over lf-fdecl-value ! lf-note-count swap lfa-decl-notes ! ;
: lfa-open-scope ( depth -- )
  lfa-scope lfa-scope-base ! -1 lfa-params! lfa-items-reset
  lfa-entry# lfa-current lfa-current-entries ! ;
: lfa-declare ( kind -- )
  lfa-inside? 0= lfa-e-nested lfa-must depth 1- lfa-floor = lfa-e-not-empty lfa-must
  lfa-here >r lfa-name-token 2dup lfa-root-name? 0= lfa-e-root-name lfa-must
  2dup lfa-end-token! lfa-full! lfa-full lfa-declared? 0= lfa-e-declared lfa-must
  lfa-full lfa-intern r> lfa-new-decl depth lfa-open-scope ;

\ universe NAME, right after the declaration's name: a level parameter.
: lfa-universes ( -- addr n ) lfa-this dup lf-fdecl-universe swap lf-fdecl-universes @ ;
: lfa-has-universe? ( name -- flag )
  lfa-universes 0 ?do 2dup i cells + @ = if 2drop true unloop exit then loop 2drop false ;
: lfa-universe-add ( name -- )
  lfa-universes nip lf-decl-universe-capacity < lfa-e-many-levels lfa-must
  lfa-universes cells + ! 1 lfa-this lf-fdecl-universes +! ;
: lfa-universe-early? ( -- flag )
  depth lfa-base = lfa-inside? and lfa-depth 0= and lfa-params 0< and ;
: lfa-universe-word ( -- )
  lfa-universe-early? lfa-e-universe-late lfa-must lfa-name-token 2dup lfa-intern
  dup lfa-has-universe? 0= lfa-e-declared lfa-must dup lfa-universe-add
  lfa-param >r lf-locals lfa-entry-new lfa-entry-universe r> rot lfa-entry-set ;

\ Binders. A binder word takes the domain, reads the variable's name and
\ opens a scope; fun or forall closes the innermost one.
: lfa-open ( domain kind pos -- binder )
  lfa-binder-push >r r@ lfa-binder-at ! r@ lfa-binder-kind ! r@ lfa-binder-domain !
  lfa-entry# r@ lfa-binder-entries ! r> ;
: lfa-local! ( c-addr u slot -- )
  >r lf-locals lfa-entry-new lfa-entry-variable r> rot lfa-entry-set ;
: lfa-name-binder ( binder -- )
  >r lfa-name-token 2dup lfa-binder-name-of dup r> lfa-binder-name !
  if lfa-depth 1- lfa-local! else 2drop then ;
\ value kind: the binder word; its frame starts below the domain.
: lfa-binder-word ( value kind -- )
  depth 2 - >r >r lfa>term r> lfa-here lfa-open r> over lfa-binder-mark !
    lfa-name-binder ;
\ The node of a binder around body, with its name, kind and position.
: lfa-named-node ( binder body tag -- term )
  >r over lfa-binder-domain @ swap r> lfa-binder-node swap >r
  r@ lfa-binder-name @ r@ lfa-binder-kind @ lfa-name! r> lfa-binder-at @ lfa-span ;
: lfa-binder-drop ( -- ) lfa-innermost lfa-binder-entries @ lfa-entries-cut
  lfa-binder-pop ;
\ Before fun or forall: a binder that may close, and one value above it.
: lfa-closing ( -- )
  lfa-closable 0> lfa-e-no-binder lfa-must
  depth lfa-frame - 1 = if exit then lfa-innermost lfa-binder-at @ lfa-e-body
    lfa-fail-see ;
: lfa-close ( value tag -- value' )
  >r lfa>term lfa-innermost swap r> lfa-named-node lfa-binder-drop true lfa-term-value ;

\ := takes the statement; the binders open now are the parameters.
: lfa-definable? ( -- flag ) lfa-inside? if lfa-this-kind lf-decl-def > 0= lfa-params 0<
  and
  else false then ;
: lfa-define ( -- )
  lfa-definable? lfa-e-define-here lfa-must 1 lfa-e-statement lfa-exactly
  lfa>term lfa-this lf-fdecl-type ! lfa-depth lfa-params! ;

\ end NAME of a declaration: the proof (or, for an axiom or import stub,
\ the statement) is the one value above the parameters; an import stub
\ may have none, and then has no statement.
: lfa-above ( -- n ) depth lfa-frame - ;
: lfa-same-binders ( -- )
  lfa-depth lfa-params = if exit then lfa-innermost lfa-binder-at @ lfa-e-open-binder
  lfa-fail-see ;
: lfa-proof-end ( above -- value )
  lfa-params 0< 0= lfa-e-no-define lfa-must lfa-same-binders
  1 = lfa-e-proof lfa-must lfa>term ;
: lfa-no-statement? ( above -- flag ) 0= lfa-depth 0= and lfa-this-kind lf-decl-stub =
  and ;
: lfa-statement-end ( above -- )
  dup lfa-no-statement? if drop exit then
  1 = lfa-e-statement lfa-must lfa>term lfa-this lf-fdecl-type ! lfa-depth lfa-params! ;
: lfa-around ( value binder -- value' )
  over 0< if drop exit then swap lf-tag-lam lfa-named-node ;
: lfa-close-param ( type value -- type' value' )
  lfa-innermost tuck lfa-around >r swap lf-tag-pi lfa-named-node r> lfa-binder-drop ;
: lfa-close-params ( type value -- type' value' ) begin lfa-depth while lfa-close-param
  repeat ;
\ The constant's words: the full name, and the rest of it in the wordlist
\ of each namespace its name is inside.
: lfa-constant! ( c-addr u wid -- )
  lfa-entry-new lfa-entry-constant lfa-current lfa-current-decl @ rot lfa-entry-set ;
: lfa-at-dot ( c-addr u i -- ) >r over r@ lfa-namespace -rot r> 1+ /string rot
  lfa-constant! ;
: lfa-register ( -- )
  lfa-full 2dup lf-consts lfa-constant!
  dup 0 ?do over i chars + c@ [char] . = if 2dup i lfa-at-dot then loop 2drop ;
: lfa-record-decl ( type value -- )
  lfa-close-params lfa-this tuck lf-fdecl-value ! tuck lf-fdecl-type !
  lf-note-count swap lfa-decl-notes-end ! ;
: lfa-publish ( -- )
  lfa-this dup lf-fdecl-type @ dup 0< if 2drop exit then
  swap lf-fdecl-name @ swap lf-pres-declare ok? lfa-e-entries-full lfa-must ;
: lfa-finish ( type value -- )
  lfa-record-decl lfa-publish lfa-current lfa-current-entries @ lfa-entries-cut
    lfa-register
  lfa-scope-close lfa-items-reset ;
: lfa-end-check ( c-addr u -- )
  lfa-current lfa-current-token lfa-text compare 0= lfa-e-end-name lfa-must ;
: lfa-end-declaration ( above c-addr u -- )
  lfa-end-check lfa-this-kind lf-decl-def > if lfa-statement-end -1 else lfa-proof-end
    then
  lfa-this lf-fdecl-type @ swap lfa-finish ;

\ namespace NAME and end NAME outside declarations; open NAME.
: lfa-space-push ( known kind -- space )
  lfa-spaces store-new-slot lfa-e-namespaces lfa-must drop
  tuck lfa-space-kind ! tuck lfa-space-known ! 0 over lfa-space-from ! ;
: lfa-outside ( -- ) lfa-inside? 0= lfa-e-namespace-here lfa-must ;
\ Enter the namespace text (whose own name starts at from), and before
\ it, as outer parts, the namespaces at each dot of its own name.
: lfa-outer-parts ( c-addr u from -- )
  over swap ?do over i chars + c@ [char] . =
    if over i lfa-known-of lfa-space-outer lfa-space-push drop then loop 2drop ;
: lfa-enter ( c-addr u from -- )
  >r 2dup r@ lfa-outer-parts lfa-known-of lfa-space-entered lfa-space-push r> swap
  lfa-space-from ! lfa-order! ;
\ A name's text has no empty part: no dot first, last or twice in a row.
: lfa-empty-part? ( c-addr u -- flag )
  dup 0= if 2drop true exit then
  over c@ [char] . = >r 2dup lfa-last-char [char] . = r> or if 2drop true exit then
  s" .." search nip nip ;
: lfa-scratch ( -- text ) lfa-knowns lfa-knowns-scratch ;
\ The namespace prefix p-addr p-u joined to the name x-addr x-u, in the
\ scratch text.
: lfa-joined ( x-addr x-u p-addr p-u -- c-addr u )
  lfa-scratch dup lfa-text-clear lfa-text+ lfa-scratch lfa-text-dotted lfa-scratch
    lfa-text ;
: lfa-from ( -- n ) lfa-current-space nip dup if 1+ then ;
: lfa-namespace-word ( -- )
  lfa-outside lfa-name-token 2dup lfa-empty-part? 0= lfa-e-bad-name lfa-must
  lfa-from >r lfa-current-space lfa-joined r> lfa-enter ;

\ end NAME of a namespace: the innermost one entered must have been
\ entered with that name; it goes, with its outer parts and every
\ namespace opened inside it.
: lfa-entered-name ( space -- c-addr u )
  dup lfa-space-known @ lfa-known lfa-known-name rot lfa-space-from @ /string ;
: lfa-closing-space ( -- i )
  lfa-space# begin dup while 1- dup lfa-space lfa-space-kind @ lfa-space-entered =
    if exit then repeat
  drop lfa-e-no-namespace lfa-fail ;
: lfa-outer? ( i -- flag )
  dup if 1- lfa-space lfa-space-kind @ lfa-space-outer = else drop false then ;
: lfa-end-namespace ( c-addr u -- )
  lfa-closing-space >r r@ lfa-space lfa-entered-name compare 0= lfa-e-end-name lfa-must
  r> begin dup lfa-outer? while 1- repeat lfa-spaces store-count ! lfa-order! ;

\ open NAME: the namespace NAME inside the current namespace or one
\ around it, innermost first, as Lean resolves it; it must be known (a
\ namespace entered, or the namespace of a constant).
: lfa-cut ( c-addr u -- c-addr u' ) begin dup while 1- 2dup chars + c@ [char] . = until
  then ;
: lfa-try ( x-addr x-u p-addr p-u -- i true | false ) lfa-joined lfa-known-find ;
: lfa-resolve ( c-addr u -- i )
  lfa-current-space begin 2over 2over lfa-try if nip nip nip nip exit then
    dup while lfa-cut repeat 2drop 2drop lfa-e-unknown-space lfa-fail ;
: lfa-open-word ( -- )
  lfa-outside lfa-name-token lfa-resolve lfa-space-opened lfa-space-push drop lfa-order! ;

\ Declarations, universe parameters and binders (ADR 0017 §7-§9): the
\ words that open and close scopes. theorem, def, axiom and import-stub
\ NAME start a declaration on an empty stack; universe NAME adds a
\ universe parameter; a binder word takes a domain and reads the
\ variable's name; fun and forall close the innermost binder around the
\ one value above it; := takes the statement, and the binders still open
\ are the parameters, with no value left between them; end NAME closes
\ them around the statement (Pi) and the proof (lambda), records the
\ declaration and defines the words of the constant (groups.fs). Inside a
\ declaration a constant's name is resolved in the declaration's own
\ namespace, as Lean does (namespaces.fs). Names are Lean names, read
\ from tokens: parts between dots, a part of digits being a number with
\ no leading zero. The name of a declaration, universe or namespace has
\ no number-like part, so no word ever shadows a number; a binder may
\ have any name, and gets no word for a number-like one (n var# refers to
\ it). Declarations are told apart by their name IDs. Untrusted
\ authoring code: these words build terms; only the checker can accept
\ them.
\ State: one record in the checker context, lfa-current (the declaration
\ being made).

require ../lib/lib.fs
require ./namespaces.fs

\ Names from tokens.
: lfa-leading-zero? ( c-addr u -- flag ) 1 > swap c@ [char] 0 = and ;
: lfa-numeric ( prefix c-addr u -- name )
  2dup lfa-leading-zero? 0= lfa-e-bad-name lfa-must
  dup 10 < lfa-e-bad-name lfa-must 0 0 2swap >number 2drop drop lf-name-num
  lfa-e-names-full lfa-must ;
: lfa-intern-part ( prefix c-addr u -- name )
  dup 0<> lfa-e-bad-name lfa-must 2dup lfa-digits?
  if lfa-numeric else lf-name-str lfa-e-names-full lfa-must then ;
: lfa-intern-step ( prefix c-addr u -- prefix' c-addr' u' )
  2dup lfa-dot >r rot 2 pick r@ lfa-intern-part -rot r> 1+ over min /string ;
\ The name a token spells: no part may be empty.
: lfa-intern ( c-addr u -- name )
  dup 0<> lfa-e-bad-name lfa-must 2dup lfa-last-char [char] . <> lfa-e-bad-name lfa-must
  0 -rot begin dup while lfa-intern-step repeat 2drop ;
: lfa-anonymous? ( c-addr u -- flag ) lf-pf-anonymous compare 0= ;
\ A binder's name: [anonymous] is the anonymous name.
: lfa-binder-name-of ( c-addr u -- name ) 2dup lfa-anonymous? if 2drop 0 else lfa-intern
  then ;

\ The declaration being made: its index, the names defined before it, its
\ token and its full name.
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

: lfa-declarations-reset ( -- ) lfa-decls store-clear lfa-namespaces-reset ;

\ Declarations: kind NAME starts one.
: lfa-root-name? ( c-addr u -- flag )
  2dup s" _root_" compare 0= >r 7 min s" _root_." compare 0= r> or ;
: lfa-end-token! ( c-addr u -- ) lfa-current lfa-current-token dup lfa-text-clear
  lfa-text+ ;
: lfa-full! ( c-addr u -- )
  lfa-current lfa-current-full dup lfa-text-clear lfa-current-space rot lfa-text+
  lfa-current lfa-current-full lfa-text-dotted ;
: lfa-declared? ( name -- flag )
  lfa-decl-count 0 ?do dup i lfa-decl-name = if drop true unloop exit then loop drop
  false ;
: lfa-new-decl ( kind name pos -- )
  lfa-decl-new dup lfa-current lfa-current-decl ! lfa-decl
  tuck lfa-decl-at ! tuck lf-fdecl-name ! tuck lf-fdecl-kind !
  -1 over lf-fdecl-type ! -1 over lf-fdecl-value ! lf-note-count swap lfa-decl-notes ! ;
: lfa-open-scope ( depth -- )
  lfa-scope lfa-scope-base ! -1 lfa-params! lfa-items-reset
  lfa-entry# lfa-current lfa-current-entries ! ;
: lfa-decl-name! ( c-addr u -- name )
  2dup lfa-root-name? 0= lfa-e-root-name lfa-must lfa-word-name
  2dup lfa-end-token! lfa-full! lfa-full lfa-intern dup lfa-declared? 0= lfa-e-declared
    lfa-must ;
: lfa-declare ( kind -- )
  lfa-inside? 0= lfa-e-nested lfa-must depth 1- lfa-floor = lfa-e-not-empty lfa-must
  lfa-here >r lfa-name-token lfa-decl-name! r> lfa-new-decl depth lfa-open-scope ;

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
  lfa-universe-early? lfa-e-universe-late lfa-must lfa-name-token lfa-word-name 2dup
  lfa-intern dup lfa-has-universe? 0= lfa-e-declared lfa-must dup lfa-universe-add
  lfa-param >r lf-locals lfa-entry-new lfa-entry-universe r> rot lfa-entry-set ;

\ Binders. A binder word takes the domain, reads the variable's name and
\ opens a scope; fun or forall closes the innermost one.
: lfa-open ( domain kind pos -- binder )
  lfa-binder-push >r r@ lfa-binder-at ! r@ lfa-binder-kind ! r@ lfa-binder-domain !
  lfa-entry# r@ lfa-binder-entries ! r> ;
: lfa-local! ( c-addr u slot -- )
  >r lf-locals lfa-entry-new lfa-entry-variable r> rot lfa-entry-set ;
\ A variable gets a word unless it is anonymous or its name is number-like.
: lfa-named? ( c-addr u name -- flag ) 0<> -rot lfa-number-like? 0= and ;
: lfa-name-binder ( binder -- )
  >r lfa-name-token 2dup lfa-binder-name-of dup r> lfa-binder-name ! >r 2dup r> lfa-named?
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

\ The binders open at := (or at the end of an axiom or import stub) are
\ the parameters: each frame starts where the declaration's does, so no
\ value is left between them, where it could never reach the term.
: lfa-no-gap ( slot -- )
  lfa-binder dup lfa-binder-mark @ lfa-base = if drop exit then
  lfa-binder-at @ lfa-e-statement lfa-fail-see ;
: lfa-params-tight ( -- ) lfa-depth 0 ?do i lfa-no-gap loop ;

\ := takes the statement; the binders open now are the parameters.
: lfa-definable? ( -- flag ) lfa-inside? if lfa-this-kind lf-decl-def > 0= lfa-params 0<
  and
  else false then ;
: lfa-define ( -- )
  lfa-definable? lfa-e-define-here lfa-must 1 lfa-e-statement lfa-exactly
  lfa-params-tight lfa>term lfa-this lf-fdecl-type ! lfa-depth lfa-params! ;

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
  1 = lfa-e-statement lfa-must lfa-params-tight lfa>term lfa-this lf-fdecl-type !
  lfa-depth lfa-params! ;
: lfa-around ( value binder -- value' )
  over 0< if drop exit then swap lf-tag-lam lfa-named-node ;
: lfa-close-param ( type value -- type' value' )
  lfa-innermost tuck lfa-around >r swap lf-tag-pi lfa-named-node r> lfa-binder-drop ;
: lfa-close-params ( type value -- type' value' ) begin lfa-depth while lfa-close-param
  repeat ;
\ The constant's words: an entry under its full name; a word with no entry
\ for each shorter name it can be written by; its prefixes are namespaces.
: lfa-constant! ( c-addr u wid -- )
  lfa-entry-new lfa-entry-constant lfa-current lfa-current-decl @ rot lfa-entry-set ;
: lfa-short-word ( c-addr u i -- ) 1+ /string lf-consts lfa-group drop ;
: lfa-register ( -- )
  lfa-full 2dup lf-consts lfa-constant! 2dup lfa-prefixes-known
  dup 0 ?do over i chars + c@ [char] . = if 2dup i lfa-short-word then loop 2drop ;
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

\ A constant's name, run: resolved in the declaration's namespace (its
\ own name's prefix), or outside declarations in the current namespace.
: lfa-name-space ( -- c-addr u ) lfa-inside? if lfa-full lfa-cut else lfa-current-space
  then ;
: lfa-resolved-run ( body -- )
  drop lfa-name-space lfa-resolve 0= if lfa-e-unknown lfa-fail then lfa-const-value ;
' lfa-resolved-run is lfa-const-run

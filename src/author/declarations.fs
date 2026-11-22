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
require ../present/print-forth.fs
require ./namespaces.fs

\ Names from tokens.
: lfa-leading-zero? ( c-addr u -- flag ) 1 > swap c@ [char] 0 = and ;
: lfa-numeric ( prefix c-addr u -- name )
  2dup lfa-leading-zero? 0= lfa-e-bad-name lfa-must
  dup lf-name-digits-max 1+ < lfa-e-bad-name lfa-must 0 0 2swap >number 2drop drop lf-name-num
  lfa-e-names-full lfa-must ;
\ «digits»: a string part of digits (bare digits are a numeric part), in
\ the guillemets print-forth.fs writes and tests (lf-pf-guillemets?).
: lfa-unquote ( c-addr u -- c-addr' u' ) 4 - swap 2 + swap ;
: lfa-quoted-part ( prefix c-addr u -- name )
  lfa-unquote 2dup decimal-digits? lfa-e-bad-name lfa-must lf-name-str
  lfa-e-names-full lfa-must ;
: lfa-intern-part ( prefix c-addr u -- name )
  dup 0<> lfa-e-bad-name lfa-must 2dup lf-pf-guillemets? if lfa-quoted-part exit then
  2dup decimal-digits? if lfa-numeric else lf-name-str lfa-e-names-full lfa-must then ;
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
: lfa-declared? ( name -- flag ) lfa-decl-find dup if nip then ;
\ No declaration takes the name of a library constant (library.fs).
: lfa-library-free ( c-addr u -- )
  lfa-library-named if drop lfa-e-declared lfa-fail then ;
: lfa-new-decl ( kind name pos -- )
  lfa-decl-new dup lfa-current lfa-current-decl ! lfa-decl
  tuck lfa-decl-at ! tuck lf-fdecl-name ! tuck lf-fdecl-kind !
  -1 over lf-fdecl-type ! -1 over lf-fdecl-value ! lf-note-count swap lfa-decl-notes ! ;
: lfa-open-scope ( depth -- )
  lfa-scope lfa-scope-base ! -1 lfa-params! lfa-items-reset
  lfa-entry# lfa-current lfa-current-entries ! lfa-declaration-fresh ;
: lfa-decl-name! ( c-addr u -- name )
  2dup lfa-root-name? 0= lfa-e-root-name lfa-must lfa-word-name
  2dup lfa-end-token! lfa-full! lfa-full lfa-library-free
  lfa-full lfa-intern dup lfa-declared? 0= lfa-e-declared lfa-must ;
: lfa-declare ( kind -- )
  lfa-inside? 0= lfa-e-nested lfa-must depth 1- lfa-floor = lfa-e-not-empty lfa-must
  lfa-here >r lfa-name-token lfa-decl-name! r> lfa-new-decl depth lfa-open-scope ;
\ protected KIND NAME: the declaration being made is protected, which
\ needs a namespace (Lean: "protected declarations must be in a
\ namespace"); the error points at the name.
: lfa-protect ( -- )
  lfa-full lfa-cut nip 0<> lfa-e-protected-root lfa-must
  true lfa-this lf-fdecl-protected ! ;

\ universe NAME, right after the declaration's name: a level parameter.
: lfa-universes ( -- addr n ) lfa-this lf-fdecl-universe-names ;
: lfa-has-universe? ( name -- flag ) lfa-universes cells-has? ;
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
\ A binder's name is no syntax word, whose word its variable would hide
\ (78); _ stays a name, as Lean's own _ binders (a match's Unit argument)
\ are written and read back.
: lfa-reserved-binder? ( c-addr u -- flag )
  2dup s" _" compare if lf-pf-reserved? else 2drop false then ;
: lfa-binder-token ( -- c-addr u )
  lfa-name-token 2dup lfa-reserved-binder? 0= lfa-e-reserved-name lfa-must ;
: lfa-name-binder ( binder -- )
  >r lfa-binder-token 2dup lfa-binder-name-of dup r> lfa-binder-name !
  2dup-under lfa-named? if lfa-depth 1- lfa-local! else 2drop then ;
\ value kind: the binder word; its frame starts below the domain, which
\ is a term in the kernel form and a syntax node in natural form
\ (src/front/reader.fs gives the word that makes it).
: lfa-binder-open ( domain kind -- )
  depth 2 - >r lfa-here lfa-open r> over lfa-binder-mark ! lfa-name-binder ;
: lfa-binder-of ( value kind xt -- ) swap >r execute r> lfa-binder-open ;
: lfa-binder-word ( value kind -- ) ['] lfa>term lfa-binder-of ;
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

\ An axiom or import stub: a statement and no value, no := (review fe1f L7).
: lfa-statement-only? ( -- flag ) lfa-this-kind lf-decl-def > ;
\ := takes the statement; the binders open now are the parameters.
: lfa-definable? ( -- flag )
  lfa-inside? if lfa-statement-only? 0= lfa-params 0< and else false then ;
\ lfa-define-check, first thing, with the statement on top; then the
\ statement taken (a term here, a syntax node in src/front/reader.fs);
\ then lfa-define-done.
: lfa-define-check ( -- )
  lfa-definable? lfa-e-define-here lfa-must 1 lfa-e-statement lfa-exactly
  lfa-params-tight ;
: lfa-define-done ( -- ) lfa-depth lfa-params! ;
: lfa-define ( -- ) lfa-define-check lfa>term lfa-this lf-fdecl-type ! lfa-define-done ;

\ end NAME of a declaration: the proof (or, for an axiom or import stub,
\ the statement) is the one value above the parameters; an import stub
\ may have none, and then has no statement.
: lfa-above ( -- n ) depth lfa-frame - ;
: lfa-same-binders ( -- )
  lfa-depth lfa-params = if exit then lfa-innermost lfa-binder-at @ lfa-e-open-binder
  lfa-fail-see ;
\ Before a declaration's proof is taken: := was there, and no binder of
\ the proof is still open (shared with src/front/reader.fs).
: lfa-proof-ready ( -- ) lfa-params 0< 0= lfa-e-no-define lfa-must lfa-same-binders ;
: lfa-proof-end ( above -- value ) lfa-proof-ready 1 = lfa-e-proof lfa-must lfa>term ;
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
\ A shorter name that is number-like (N.0.f as 0.f) gets no word.
: lfa-short-word ( c-addr u i -- )
  1+ /string 2dup lfa-number-like? if 2drop else lf-consts lfa-group drop then ;
: lfa-register ( -- )
  lfa-full 2dup lf-consts lfa-constant! 2dup lfa-prefixes-known
  dup 0 ?do over i lfa-dot-at? if 2dup i lfa-short-word then loop 2drop ;
: lfa-record-decl ( type value -- )
  lfa-close-params lfa-this tuck lf-fdecl-value ! lf-fdecl-type ! ;
: lfa-publish ( -- )
  lfa-this dup lf-fdecl-type @ dup 0< if 2drop exit then
  swap lf-fdecl-name @ swap lf-pres-declare ok? lfa-e-entries-full lfa-must ;
: lfa-notes-end ( -- ) lf-note-count lfa-this lfa-decl-notes-end ! ;
\ The declaration made, its type and value recorded (by lfa-record-decl
\ here, by the front end's hand-over in natural text, front/handover.fs):
\ the end of its notes, its words, and its scope closed.
: lfa-declared ( -- )
  lfa-notes-end lfa-publish lfa-current lfa-current-entries @ lfa-entries-cut
  lfa-register lfa-scope-close lfa-items-reset ;
: lfa-finish ( type value -- ) lfa-record-decl lfa-declared ;
: lfa-end-check ( c-addr u -- )
  lfa-current lfa-current-token lfa-text compare 0= lfa-e-end-name lfa-must ;
: lfa-end-declaration ( above c-addr u -- )
  lfa-end-check lfa-statement-only? if lfa-statement-end -1 else lfa-proof-end then
  lfa-this lf-fdecl-type @ swap lfa-finish ;

\ A constant's name, run: resolved in the declaration's namespace (its
\ own name's prefix), or outside declarations in the current namespace.
: lfa-name-space ( -- c-addr u ) lfa-inside? if lfa-full lfa-cut else lfa-current-space
  then ;
: lfa-resolved-run ( body -- )
  drop lfa-name-space lfa-resolve 0= if lfa-e-unknown lfa-fail then lfa-const-value
  lfa-named-natural ;
' lfa-resolved-run is lfa-const-run

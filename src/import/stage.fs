\ Staging a Lean export into the checker's input (plan task 3.2.2, v0):
\ a lean4export NDJSON file read with the Forth reader (ndjson.fs) into
\ this context's name, level, term and constant-reference stores, and each
\ declaration into the input (core/input.fs), which loading then seals.
\ Moved here from the test-only transport tests/support/ndjson-input.fs,
\ unchanged in what it stages; the command line (src/cli/leanforth.fs) and
\ the tests use it. It decides nothing about types: check-declaration does.
\
\ Two passes over the file. The first interns every name and adds every
\ universe parameter that a level names to the session's level context,
\ which must be complete before the symbolic session begins; the second
\ stages levels, expressions (Sorts as symbolic Sorts, constants through
\ their reference boundary; a let, literal, metadata or projection as the
\ leaf of its form, core/unsupported-forms.fs) and the theorems,
\ definitions, opaque declarations and axioms, each with its universe
\ parameters, type, value, hint and safety. Binder names and annotations
\ are dropped, as Lean's kernel ignores them. A declaration of a mutual
\ block (whose `all` list is not its own name alone), a quotient or an
\ inductive block stops reading as unsupported: the input cannot hold it.
\ Equal nodes are not shared beyond what the export shares.
\
\ stage-read ( c-addr u -- outcome ) reads the export file c-addr u into
\ this context's input, replacing what was there, and ends loading;
\ stage-read-checked does the same with the export's manifest checked on
\ both passes (manifest.fs: "<file>.manifest.json"; any failure about it
\ is invalid), the default of the command line. Outcomes: ok; the
\ reader's or the manifest check's (invalid malformed, unsupported for
\ other versions); a handler's: full when a store or table of this phase
\ has no room (64 names, levels and term nodes, 32 declarations and
\ constant references, 8 universe parameters per declaration and 8
\ universe arguments per constant: only small exports fit) or a numeric
\ name part is larger than max-n (never wrapped into another), unsupported
\ for the kinds above, invalid for a declaration the input refuses; or
\ lf-input-end's. After a failure the input is not sealed and nothing can
\ be checked. stage-error gives the line, field and reason of a failure,
\ a handler's own reason in place of the reader's. A THROW from the
\ reader passes on, the file closed.
\
\ Untrusted [import] code: it can hand the checker a wrong claim, never
\ make one accepted. Limits are the stores' (above): a larger file stops
\ with full (plan task 3.3.1 makes them configurable).
\ State: one record in the checker context, stage-state (the tables from
\ export indices to LeanForth's names, levels and expressions, a
\ constant's universe arguments, the declaration being built and the
\ reason of a refusal), and one export record and one manifest record,
\ stage-export and stage-manifest, which stay shared because they own
\ heap buffers (a context member may not: context-free has no release
\ hook), like ndjson-count.fs's; so one staging runs at a time, in any
\ context, and its input lands in the context current while it runs.

base @ decimal   \ the numbers below are decimal; the BASE kept here returns at the end
require ../lib/lib.fs
require ../core/names.fs
require ../core/levels.fs
require ../core/level-scope.fs
require ../core/terms.fs
require ../core/symbolic-session.fs
require ../core/generation-handles.fs
require ../core/constant-references.fs
require ../core/constant-term-boundary.fs
require ../core/unsupported-forms.fs
require ../core/input.fs
require ./ndjson.fs
require ./manifest.fs

begin-structure /staging
  lf-name-capacity cells +field staging-names        \ export name -> name ID
  lf-level-capacity cells +field staging-levels      \ export level -> level index
  lf-term-capacity 2* cells +field staging-exprs     \ export expression -> handle
  lf-cref-argument-capacity 2* cells +field staging-pairs   \ a constant's levels
  /lf-idecl +field staging-decl                      \ the declaration being built
  field: staging-why                                 \ counted string, or 0
end-structure
/staging context-record: stage-state
export: stage-export
manifest: stage-manifest

: stage-names ( -- addr ) stage-state staging-names ;
: stage-levels ( -- addr ) stage-state staging-levels ;
: stage-exprs ( -- addr ) stage-state staging-exprs ;
: stage-pairs ( -- addr ) stage-state staging-pairs ;
: stage-decl ( -- decl ) stage-state staging-decl ;
: stage-why ( -- addr ) stage-state staging-why ;

\ A handler's refusal, with its reason kept for stage-error.
: stage-stop ( outcome why -- outcome ) stage-why ! ;
: stage-no-room ( why -- outcome ) outcome-full swap stage-stop ;
: names-full ( -- outcome ) c" too many names for the check's name store" stage-no-room ;
: levels-full ( -- outcome )
  c" too many levels for the check's level store" stage-no-room ;
: exprs-full ( -- outcome )
  c" too many expression nodes or constant references for the check's stores"
  stage-no-room ;

\ Table cells, refused (false) for an index past the table.
: stage-cell ( i table capacity -- addr true | false )
  rot tuck u> if cells + true else 2drop false then ;
: stage-name ( i -- id ) cells stage-names + @ ;
: stage-level@ ( i -- level ) cells stage-levels + @ ;
: stage-expr@ ( i -- index identity ) 2* cells stage-exprs + 2@ ;
: stage-root ( i -- term ) stage-expr@ drop ;
: stage-pass-by ( record -- outcome ) drop outcome-ok ;
\ Store x in cell i of a table: true, or false past its capacity.
: stage-store ( x i table capacity -- flag )
  stage-cell if ! true else drop false then ;

\ Names (both passes see them; the first interns them).
: stage-name! ( id record -- outcome )
  record-index @ stage-names lf-name-capacity stage-store
  if outcome-ok else names-full then ;
: stage-prefix ( record -- prefix ) name-prefix @ stage-name ;
: stage-interned ( id true | false record -- outcome )
  swap if stage-name! else drop names-full then ;
: stage-str ( record -- outcome )
  dup >r stage-prefix r@ name-part 2@ lf-name-str r> stage-interned ;
\ A numeric part's decimal digits (the reader allows any number of them)
\ as a cell: (n true), or false beyond max-n, which a name entry cannot
\ hold. Reading them into one cell regardless would wrap a large number
\ into another, smaller one: a different name, so a different claim.
: stage-small? ( ud -- n flag ) 0= over 0< 0= and ;
: stage-digits ( c-addr u -- n true | false )
  0 0 2swap >number nip if 2drop false exit then stage-small? dup 0= if nip then ;
: too-large-part ( record -- outcome )
  drop outcome-full c" a numeric name part larger than the check holds" stage-stop ;
: stage-num ( record -- outcome )
  dup name-part 2@ stage-digits 0= if too-large-part exit then
  over >r swap stage-prefix swap lf-name-num r> stage-interned ;
\ The first pass also puts every universe parameter in the level context.
: stage-context ( id -- outcome )
  dup lf-lscope-member? if drop outcome-ok exit then
  lf-lscope-context-add if outcome-ok else levels-full then ;
: stage-param-name ( record -- outcome ) param-name @ stage-name stage-context ;

\ Levels (second pass).
: stage-level-keep ( index true | false record -- outcome )
  swap 0= if drop levels-full exit then
  record-index @ stage-levels lf-level-capacity stage-store
  if outcome-ok else levels-full then ;
: stage-two ( record -- l r ) dup max-left @ stage-level@ swap max-right @ stage-level@ ;
: stage-succ ( record -- outcome )
  dup >r succ-of @ stage-level@ lf-level-succ r> stage-level-keep ;
: stage-max ( record -- outcome ) dup >r stage-two lf-level-max r> stage-level-keep ;
: stage-imax ( record -- outcome ) dup >r stage-two lf-level-imax r> stage-level-keep ;
: stage-param ( record -- outcome )
  dup >r param-name @ stage-name lf-level-param r> stage-level-keep ;
: stage-level-handle ( i -- index identity )
  stage-level@ dup lf-level-identity 0= if 0 then ;

\ Expressions (second pass), kept as handles.
: stage-expr-keep ( index identity true | false record -- outcome )
  swap 0= if drop exprs-full exit then
  record-index @ dup lf-term-capacity u< 0= if drop 2drop exprs-full exit then
  2* cells stage-exprs + 2! outcome-ok ;
: stage-bvar ( record -- outcome ) dup >r bvar-index @ lf-hterm-bvar r> stage-expr-keep ;
: stage-sort ( record -- outcome )
  dup >r sort-level @ stage-level-handle lf-hterm-sort r> stage-expr-keep ;
: stage-arg! ( i k -- ) >r stage-level-handle swap r> 2* cells stage-pairs + 2! ;
: stage-arg ( record k -- record )
  2dup swap dup const-levels @ swap list-item swap stage-arg! ;
: stage-arity ( record -- n ) dup const-levels @ swap list-count ;
: stage-reference ( record n -- cref identity true | false )
  >r r@ 0 ?do i stage-arg loop const-name @ stage-name lf-name-generation @ stage-pairs r>
  lf-cref-new ;
: stage-constant ( record n -- index identity true | false )
  stage-reference if lf-cterm-new else false then ;
: too-many-args ( record n -- outcome )
  2drop outcome-full c" a constant with more universe arguments than the check holds"
  stage-stop ;
: stage-const ( record -- outcome )
  dup stage-arity dup lf-cref-argument-capacity > if too-many-args exit then
  over >r stage-constant r> stage-expr-keep ;
\ Two children, at the field offsets first and second, as handles.
: stage-child ( record offset -- index identity ) + @ stage-expr@ ;
: stage-children ( record first second -- l lid r rid )
  >r over swap stage-child rot r> stage-child ;
: stage-app ( record -- outcome )
  dup >r 0 app-fn 0 app-arg stage-children lf-hterm-app r> stage-expr-keep ;
: stage-binder ( record -- d did b bid ) 0 binder-type 0 binder-body stage-children ;
: stage-lam ( record -- outcome ) dup >r stage-binder lf-hterm-lam r> stage-expr-keep ;
: stage-forall ( record -- outcome ) dup >r stage-binder lf-hterm-pi r> stage-expr-keep ;
: stage-form ( record form -- outcome ) swap >r lf-hterm-unsupported r> stage-expr-keep ;
: stage-let ( record -- outcome ) lf-form-let stage-form ;
: stage-proj ( record -- outcome ) lf-form-proj stage-form ;
: stage-natval ( record -- outcome ) lf-form-nat stage-form ;
: stage-strval ( record -- outcome ) lf-form-string stage-form ;
: stage-mdata ( record -- outcome ) lf-form-mdata stage-form ;

\ Declarations (second pass).
\ A declaration of kind, with no value, opaque, until set otherwise.
: stage-clear ( kind -- )
  stage-decl /lf-idecl erase stage-decl lf-idecl-kind !
  lf-hint-opaque stage-decl lf-idecl-hint ! -1 stage-decl lf-idecl-value ! ;
: stage-start ( record kind -- record )
  stage-clear dup decl-name @ stage-name stage-decl lf-idecl-name !
  dup decl-type @ stage-root stage-decl lf-idecl-type ! ;
: stage-value ( record -- record )
  dup decl-value @ stage-root stage-decl lf-idecl-value ! ;
: stage-safety ( safety -- ) stage-decl lf-idecl-safety ! ;
: stage-unsafe ( record -- record )
  dup decl-unsafe @ if lf-safety-unsafe else lf-safety-safe then stage-safety ;
: stage-hint ( record -- record )
  dup decl-hints @ dup stage-decl lf-idecl-hint ! lf-hint-regular =
  if dup decl-height @ stage-decl lf-idecl-height ! then ;
: stage-param-id ( record k -- id ) swap dup decl-params @ swap list-item stage-name ;
: stage-decl-param ( record k -- record )
  2dup stage-param-id swap cells stage-decl lf-idecl-params + ! ;
: too-many-params ( record n -- record outcome )
  drop outcome-full c" a declaration with more universe parameters than the check holds"
  stage-stop ;
: stage-params ( record -- record outcome )
  dup decl-params @ over list-count dup lf-param-capacity > if too-many-params exit then
  dup stage-decl lf-idecl-arity ! 0 ?do i stage-decl-param loop outcome-ok ;
\ The input's answer: full when it holds no more declarations, invalid
\ when it refuses the record.
: stage-added ( i outcome -- outcome )
  nip dup outcome-full =
  if c" too many declarations for the check's input" stage-stop then
  dup outcome-invalid = if c" a declaration the input refuses" stage-stop then ;
: stage-add ( record -- outcome )
  stage-params ok-then? 0= if exit then drop stage-decl lf-input-add stage-added ;
: stage-first-of-all ( record -- u ) 0 over decl-all @ rot list-item ;
: stage-alone? ( record -- flag )
  dup decl-all @ over list-count 1 = over stage-first-of-all rot decl-name @ = and ;
: stage-mutual ( record -- outcome )
  drop outcome-unsupported c" a declaration of a mutual block (not supported yet)"
  stage-stop ;
: stage-thm ( record -- outcome )
  dup stage-alone? 0= if stage-mutual exit then
  lf-kind-theorem stage-start stage-value lf-safety-safe stage-safety stage-add ;
: stage-def ( record -- outcome )
  dup stage-alone? 0= if stage-mutual exit then
  lf-kind-definition stage-start stage-value stage-hint dup decl-safety @ stage-safety
  stage-add ;
: stage-opaque ( record -- outcome )
  dup stage-alone? 0= if stage-mutual exit then
  lf-kind-opaque stage-start stage-value stage-unsafe stage-add ;
: stage-axiom ( record -- outcome ) lf-kind-axiom stage-start stage-unsafe stage-add ;
\ Kinds the input cannot hold, refused on the first pass.
: stage-quot ( record -- outcome )
  drop outcome-unsupported c" a quotient declaration (not supported yet)" stage-stop ;
: stage-inductive ( record -- outcome )
  drop outcome-unsupported c" an inductive type (not supported yet)" stage-stop ;

\ The two passes' handlers, in the reader's kind order (ndjson.fs); 0 is
\ no handler, which the reader refuses as unsupported (the elements of an
\ inductive block, never reached after its block). Each table must end at
\ HERE with one cell per kind, otherwise the load stops.
: stage-table-check ( table -- )
  here swap - kind-count cells <> abort" stage.fs: one handler per record kind" ;
create stage-first
  ' stage-pass-by , ' stage-str , ' stage-num , ' stage-pass-by , ' stage-pass-by ,
  ' stage-pass-by , ' stage-param-name , ' stage-pass-by , ' stage-pass-by ,
  ' stage-pass-by , ' stage-pass-by , ' stage-pass-by , ' stage-pass-by ,
  ' stage-pass-by , ' stage-pass-by , ' stage-pass-by , ' stage-pass-by ,
  ' stage-pass-by , ' stage-pass-by , ' stage-pass-by , ' stage-pass-by ,
  ' stage-pass-by , ' stage-quot , ' stage-inductive , 0 , 0 , 0 ,
stage-first stage-table-check
create stage-second
  ' stage-pass-by , ' stage-pass-by , ' stage-pass-by , ' stage-succ , ' stage-max ,
  ' stage-imax , ' stage-param , ' stage-bvar , ' stage-sort , ' stage-const ,
  ' stage-app , ' stage-lam , ' stage-forall , ' stage-let , ' stage-proj ,
  ' stage-natval , ' stage-strval , ' stage-mdata , ' stage-axiom , ' stage-def ,
  ' stage-thm , ' stage-opaque , ' stage-quot , ' stage-inductive , 0 , 0 , 0 ,
stage-second stage-table-check
: stage-handler! ( xt|0 kind -- )
  over 0= if 2drop exit then stage-export export-handler ! ;
: stage-handlers ( table -- )
  stage-export export-handlers-clear
  kind-count 0 do dup i cells + @ i stage-handler! loop drop ;

\ Reading the file once, by xt ( c-addr u -- outcome ): the reader alone,
\ or with the manifest checked.
: stage-plain ( c-addr u -- outcome ) stage-export export-read ;
: stage-checked ( c-addr u -- outcome ) stage-manifest manifest-read ;
: stage-pass ( c-addr u xt table -- outcome ) stage-handlers execute ;
\ A fresh input in this context.
: stage-fresh ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  lf-input-reset stage-state /staging erase ;
: stage-session ( -- outcome )
  lf-ssession-begin if outcome-ok exit then
  outcome-invalid c" the symbolic session could not begin" stage-stop ;
: stage-both ( c-addr u xt -- outcome )
  >r 2dup r@ stage-first stage-pass dup ok? 0= if nip nip r> drop exit then drop
  stage-session dup ok? 0= if nip nip r> drop exit then drop
  r> stage-second stage-pass dup ok? if drop lf-input-end then ;
\ Both records ready (full when the heap has no room), the input fresh,
\ both passes, then the records' memory released, on a failed start too.
: stage-init ( -- outcome )
  stage-export export-init
  dup ok? if drop stage-export stage-manifest manifest-init then ;
: stage-done ( -- ) stage-manifest manifest-free stage-export export-free ;
: stage-file ( c-addr u xt -- outcome )
  0 stage-why ! stage-init dup ok? 0= if nip nip nip stage-done exit then drop
  stage-fresh stage-both stage-done ;
: stage-read ( c-addr u -- outcome ) ['] stage-plain stage-file ;
: stage-read-checked ( c-addr u -- outcome ) ['] stage-checked stage-file ;

\ After a failure: the line, the field (empty if none) and the reason, a
\ handler's own in place of the reader's "handler refused the record".
: stage-error ( -- line key-addr key-u why-addr why-u )
  stage-export export-error stage-why @ ?dup if >r 2drop r> count then ;

base !   \ the BASE this file was loaded with

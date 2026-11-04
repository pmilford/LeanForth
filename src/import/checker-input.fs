\ The checker's input from a Lean export (plan task 3.2.2, v0): a
\ lean4export NDJSON file read with the Forth reader (ndjson.fs) into
\ this context's name, level, term and constant-reference stores, and each
\ declaration into the input (core/input.fs), which loading then seals.
\ Unlike import/stage.fs, which stages an export into the compact store
\ (ADR 0016), this fills the 64-entry stores today's checker reads; it is
\ retired when the checker moves onto the compact store (C9 step 3).
\ Moved here from the test-only transport tests/support/ndjson-input.fs;
\ the command line (src/cli/leanforth.fs), the run records' driver
\ (tests/support/run-records.fs) and the tests use it. It decides
\ nothing about types: check-declaration does.
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
\ cin-read ( c-addr u -- outcome ) reads the export file c-addr u into
\ this context's input, replacing what was there, and ends loading;
\ cin-read-checked does the same with the export's manifest checked on
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
\ be checked. cin-error gives the line, field and reason of a failure,
\ a handler's own reason in place of the reader's. A THROW from the
\ reader passes on, the file closed.
\
\ Untrusted [import] code: it can hand the checker a wrong claim, never
\ make one accepted. Limits are the stores' (above): a larger file stops
\ with full (plan task 3.3.1 makes them configurable).
\ State: one record in the checker context, cin-state (the tables from
\ export indices to LeanForth's names, levels and expressions, a
\ constant's universe arguments, the declaration being built and the
\ reason of a refusal), and one export record and one manifest record,
\ cin-export and cin-manifest, which stay shared because they own
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

begin-structure /import-map
  lf-name-capacity cells +field map-names        \ export name -> name ID
  lf-level-capacity cells +field map-levels      \ export level -> level index
  lf-term-capacity 2* cells +field map-exprs     \ export expression -> handle
  lf-cref-argument-capacity 2* cells +field map-pairs   \ a constant's levels
  /lf-idecl +field map-decl                      \ the declaration being built
  field: map-why                                 \ counted string, or 0
end-structure
/import-map context-record: cin-state
export: cin-export
manifest: cin-manifest

: cin-names ( -- addr ) cin-state map-names ;
: cin-levels ( -- addr ) cin-state map-levels ;
: cin-exprs ( -- addr ) cin-state map-exprs ;
: cin-pairs ( -- addr ) cin-state map-pairs ;
: cin-decl ( -- decl ) cin-state map-decl ;
: cin-why ( -- addr ) cin-state map-why ;

\ A handler's refusal, with its reason kept for cin-error.
: cin-stop ( outcome why -- outcome ) cin-why ! ;
: cin-no-room ( why -- outcome ) outcome-full swap cin-stop ;
: cin-names-full ( -- outcome )
  c" too many names for the check's name store" cin-no-room ;
: cin-levels-full ( -- outcome )
  c" too many levels for the check's level store" cin-no-room ;
: cin-exprs-full ( -- outcome )
  c" too many expression nodes or constant references for the check's stores"
  cin-no-room ;

\ Table cells, refused (false) for an index past the table.
: cin-cell ( i table capacity -- addr true | false )
  rot tuck u> if cells + true else 2drop false then ;
: cin-name ( i -- id ) cells cin-names + @ ;
: cin-level@ ( i -- level ) cells cin-levels + @ ;
: cin-expr@ ( i -- index identity ) 2* cells cin-exprs + 2@ ;
: cin-root ( i -- term ) cin-expr@ drop ;
: cin-pass-by ( record -- outcome ) drop outcome-ok ;
\ Store x in cell i of a table: true, or false past its capacity.
: cin-store ( x i table capacity -- flag )
  cin-cell if ! true else drop false then ;

\ Names (both passes see them; the first interns them).
: cin-name! ( id record -- outcome )
  record-index @ cin-names lf-name-capacity cin-store
  if outcome-ok else cin-names-full then ;
: cin-prefix ( record -- prefix ) name-prefix @ cin-name ;
: cin-interned ( id true | false record -- outcome )
  swap if cin-name! else drop cin-names-full then ;
: cin-str ( record -- outcome )
  dup >r cin-prefix r@ name-part 2@ lf-name-str r> cin-interned ;
\ A numeric part's decimal digits (the reader allows any number of them)
\ as a cell: (n true), or false beyond max-n, which a name entry cannot
\ hold. Reading them into one cell regardless would wrap a large number
\ into another, smaller one: a different name, so a different claim.
: cin-small? ( ud -- n flag ) 0= over 0< 0= and ;
: cin-digits ( c-addr u -- n true | false )
  0 0 2swap >number nip if 2drop false exit then cin-small? dup 0= if nip then ;
: cin-large-part ( record -- outcome )
  drop outcome-full c" a numeric name part larger than the check holds" cin-stop ;
: cin-num ( record -- outcome )
  dup name-part 2@ cin-digits 0= if cin-large-part exit then
  over >r swap cin-prefix swap lf-name-num r> cin-interned ;
\ The first pass also puts every universe parameter in the level context.
: cin-context ( id -- outcome )
  dup lf-lscope-member? if drop outcome-ok exit then
  lf-lscope-context-add if outcome-ok else cin-levels-full then ;
: cin-param-name ( record -- outcome ) param-name @ cin-name cin-context ;

\ Levels (second pass).
: cin-level-keep ( index true | false record -- outcome )
  swap 0= if drop cin-levels-full exit then
  record-index @ cin-levels lf-level-capacity cin-store
  if outcome-ok else cin-levels-full then ;
: cin-two ( record -- l r ) dup max-left @ cin-level@ swap max-right @ cin-level@ ;
: cin-succ ( record -- outcome )
  dup >r succ-of @ cin-level@ lf-level-succ r> cin-level-keep ;
: cin-max ( record -- outcome ) dup >r cin-two lf-level-max r> cin-level-keep ;
: cin-imax ( record -- outcome ) dup >r cin-two lf-level-imax r> cin-level-keep ;
: cin-param ( record -- outcome )
  dup >r param-name @ cin-name lf-level-param r> cin-level-keep ;
: cin-level-handle ( i -- index identity )
  cin-level@ dup lf-level-identity 0= if 0 then ;

\ Expressions (second pass), kept as handles.
: cin-expr-keep ( index identity true | false record -- outcome )
  swap 0= if drop cin-exprs-full exit then
  record-index @ dup lf-term-capacity u< 0= if drop 2drop cin-exprs-full exit then
  2* cells cin-exprs + 2! outcome-ok ;
: cin-bvar ( record -- outcome ) dup >r bvar-index @ lf-hterm-bvar r> cin-expr-keep ;
: cin-sort ( record -- outcome )
  dup >r sort-level @ cin-level-handle lf-hterm-sort r> cin-expr-keep ;
: cin-arg! ( i k -- ) >r cin-level-handle swap r> 2* cells cin-pairs + 2! ;
: cin-arg ( record k -- record )
  2dup swap dup const-levels @ swap list-item swap cin-arg! ;
: cin-arity ( record -- n ) dup const-levels @ swap list-count ;
: cin-reference ( record n -- cref identity true | false )
  >r r@ 0 ?do i cin-arg loop const-name @ cin-name lf-name-generation @ cin-pairs r>
  lf-cref-new ;
: cin-constant ( record n -- index identity true | false )
  cin-reference if lf-cterm-new else false then ;
: cin-many-args ( record n -- outcome )
  2drop outcome-full c" a constant with more universe arguments than the check holds"
  cin-stop ;
: cin-const ( record -- outcome )
  dup cin-arity dup lf-cref-argument-capacity > if cin-many-args exit then
  over >r cin-constant r> cin-expr-keep ;
\ Two children, at the field offsets first and second, as handles.
: cin-child ( record offset -- index identity ) + @ cin-expr@ ;
: cin-children ( record first second -- l lid r rid )
  >r over swap cin-child rot r> cin-child ;
: cin-app ( record -- outcome )
  dup >r 0 app-fn 0 app-arg cin-children lf-hterm-app r> cin-expr-keep ;
: cin-binder ( record -- d did b bid ) 0 binder-type 0 binder-body cin-children ;
: cin-lam ( record -- outcome ) dup >r cin-binder lf-hterm-lam r> cin-expr-keep ;
: cin-forall ( record -- outcome ) dup >r cin-binder lf-hterm-pi r> cin-expr-keep ;
: cin-form ( record form -- outcome ) swap >r lf-hterm-unsupported r> cin-expr-keep ;
: cin-let ( record -- outcome ) lf-form-let cin-form ;
: cin-proj ( record -- outcome ) lf-form-proj cin-form ;
: cin-natval ( record -- outcome ) lf-form-nat cin-form ;
: cin-strval ( record -- outcome ) lf-form-string cin-form ;
: cin-mdata ( record -- outcome ) lf-form-mdata cin-form ;

\ Declarations (second pass).
\ A declaration of kind, with no value, opaque, until set otherwise.
: cin-clear ( kind -- )
  cin-decl /lf-idecl erase cin-decl lf-idecl-kind !
  lf-hint-opaque cin-decl lf-idecl-hint ! -1 cin-decl lf-idecl-value ! ;
: cin-start ( record kind -- record )
  cin-clear dup decl-name @ cin-name cin-decl lf-idecl-name !
  dup decl-type @ cin-root cin-decl lf-idecl-type ! ;
: cin-value ( record -- record )
  dup decl-value @ cin-root cin-decl lf-idecl-value ! ;
: cin-safety ( safety -- ) cin-decl lf-idecl-safety ! ;
: cin-unsafe ( record -- record )
  dup decl-unsafe @ if lf-safety-unsafe else lf-safety-safe then cin-safety ;
: cin-hint ( record -- record )
  dup decl-hints @ dup cin-decl lf-idecl-hint ! lf-hint-regular =
  if dup decl-height @ cin-decl lf-idecl-height ! then ;
: cin-param-id ( record k -- id ) swap dup decl-params @ swap list-item cin-name ;
: cin-decl-param ( record k -- record )
  2dup cin-param-id swap cells cin-decl lf-idecl-params + ! ;
: cin-many-params ( record n -- record outcome )
  drop outcome-full c" a declaration with more universe parameters than the check holds"
  cin-stop ;
: cin-params ( record -- record outcome )
  dup decl-params @ over list-count dup lf-param-capacity > if cin-many-params exit then
  dup cin-decl lf-idecl-arity ! 0 ?do i cin-decl-param loop outcome-ok ;
\ The input's answer: full when it holds no more declarations, invalid
\ when it refuses the record.
: cin-added ( i outcome -- outcome )
  nip dup outcome-full =
  if c" too many declarations for the check's input" cin-stop then
  dup outcome-invalid = if c" a declaration the input refuses" cin-stop then ;
: cin-add ( record -- outcome )
  cin-params ok-then? 0= if exit then drop cin-decl lf-input-add cin-added ;
: cin-first-of-all ( record -- u ) 0 over decl-all @ rot list-item ;
: cin-alone? ( record -- flag )
  dup decl-all @ over list-count 1 = over cin-first-of-all rot decl-name @ = and ;
: cin-mutual ( record -- outcome )
  drop outcome-unsupported c" a declaration of a mutual block (not supported yet)"
  cin-stop ;
: cin-thm ( record -- outcome )
  dup cin-alone? 0= if cin-mutual exit then
  lf-kind-theorem cin-start cin-value lf-safety-safe cin-safety cin-add ;
: cin-def ( record -- outcome )
  dup cin-alone? 0= if cin-mutual exit then
  lf-kind-definition cin-start cin-value cin-hint dup decl-safety @ cin-safety
  cin-add ;
: cin-opaque ( record -- outcome )
  dup cin-alone? 0= if cin-mutual exit then
  lf-kind-opaque cin-start cin-value cin-unsafe cin-add ;
: cin-axiom ( record -- outcome ) lf-kind-axiom cin-start cin-unsafe cin-add ;
\ Kinds the input cannot hold, refused on the first pass.
: cin-quot ( record -- outcome )
  drop outcome-unsupported c" a quotient declaration (not supported yet)" cin-stop ;
: cin-inductive ( record -- outcome )
  drop outcome-unsupported c" an inductive type (not supported yet)" cin-stop ;

\ The two passes' handlers, in the reader's kind order (ndjson.fs); 0 is
\ no handler, which the reader refuses as unsupported (the elements of an
\ inductive block, never reached after its block). Each table must end at
\ HERE with one cell per kind, otherwise the load stops.
: cin-table-check ( table -- )
  here swap - kind-count cells <> abort" checker-input.fs: one handler per record kind" ;
create cin-first
  ' cin-pass-by , ' cin-str , ' cin-num , ' cin-pass-by , ' cin-pass-by ,
  ' cin-pass-by , ' cin-param-name , ' cin-pass-by , ' cin-pass-by ,
  ' cin-pass-by , ' cin-pass-by , ' cin-pass-by , ' cin-pass-by ,
  ' cin-pass-by , ' cin-pass-by , ' cin-pass-by , ' cin-pass-by ,
  ' cin-pass-by , ' cin-pass-by , ' cin-pass-by , ' cin-pass-by ,
  ' cin-pass-by , ' cin-quot , ' cin-inductive , 0 , 0 , 0 ,
cin-first cin-table-check
create cin-second
  ' cin-pass-by , ' cin-pass-by , ' cin-pass-by , ' cin-succ , ' cin-max ,
  ' cin-imax , ' cin-param , ' cin-bvar , ' cin-sort , ' cin-const ,
  ' cin-app , ' cin-lam , ' cin-forall , ' cin-let , ' cin-proj ,
  ' cin-natval , ' cin-strval , ' cin-mdata , ' cin-axiom , ' cin-def ,
  ' cin-thm , ' cin-opaque , ' cin-quot , ' cin-inductive , 0 , 0 , 0 ,
cin-second cin-table-check
: cin-handler! ( xt|0 kind -- )
  over 0= if 2drop exit then cin-export export-handler ! ;
: cin-handlers ( table -- )
  cin-export export-handlers-clear
  kind-count 0 do dup i cells + @ i cin-handler! loop drop ;

\ Reading the file once, by xt ( c-addr u -- outcome ): the reader alone,
\ or with the manifest checked.
: cin-plain ( c-addr u -- outcome ) cin-export export-read ;
: cin-checked ( c-addr u -- outcome ) cin-manifest manifest-read ;
: cin-pass ( c-addr u xt table -- outcome ) cin-handlers execute ;
\ A fresh input in this context.
: cin-fresh ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  lf-input-reset cin-state /import-map erase ;
: cin-session ( -- outcome )
  lf-ssession-begin if outcome-ok exit then
  outcome-invalid c" the symbolic session could not begin" cin-stop ;
: cin-both ( c-addr u xt -- outcome )
  >r 2dup r@ cin-first cin-pass dup ok? 0= if nip nip r> drop exit then drop
  cin-session dup ok? 0= if nip nip r> drop exit then drop
  r> cin-second cin-pass dup ok? if drop lf-input-end then ;
\ Both records ready (full when the heap has no room), the input fresh,
\ both passes, then the records' memory released, on a failed start too.
: cin-init ( -- outcome )
  cin-export export-init
  dup ok? if drop cin-export cin-manifest manifest-init then ;
: cin-done ( -- ) cin-manifest manifest-free cin-export export-free ;
: cin-file ( c-addr u xt -- outcome )
  0 cin-why ! cin-init dup ok? 0= if nip nip nip cin-done exit then drop
  cin-fresh cin-both cin-done ;
: cin-read ( c-addr u -- outcome ) ['] cin-plain cin-file ;
: cin-read-checked ( c-addr u -- outcome ) ['] cin-checked cin-file ;

\ After a failure: the line, the field (empty if none) and the reason, a
\ handler's own in place of the reader's "handler refused the record".
: cin-error ( -- line key-addr key-u why-addr why-u )
  cin-export export-error cin-why @ ?dup if >r 2drop r> count then ;

base !   \ the BASE this file was loaded with

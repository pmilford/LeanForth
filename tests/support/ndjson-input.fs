\ Test-only transport from a lean4export NDJSON file to LeanForth's input
\ (src/core/input.fs), then the first checker. The examples and tests of
\ check-declaration (plan task 2.2.3) read the pinned fixtures' exports
\ with it. It uses the project's NDJSON reader (src/import/ndjson.fs),
\ which checks every record's form and references, and stages names,
\ levels and expressions into this context's stores and each declaration
\ into the input. It decides nothing about types: check-declaration does.
\
\ Two passes over the file. The first interns every name and adds every
\ universe parameter that a level names to the session's level context,
\ which must be complete before the symbolic session begins; the second
\ stages levels, expressions (Sorts as symbolic Sorts, constants through
\ their reference boundary; a let, literal, metadata or projection as the
\ leaf of its form, src/core/unsupported-forms.fs) and the theorems,
\ definitions, opaque declarations and axioms, each with its universe
\ parameters, type, value, hint and safety. Binder names and annotations
\ are dropped, as Lean's kernel ignores them. A declaration of a mutual
\ block (whose `all` list is not its own name alone), a quotient or an
\ inductive block stops reading as unsupported: the input cannot hold it.
\ Equal nodes are not shared beyond what the export shares.
\
\ Untrusted [import] code, test-only: src/import/feed.fs (plan task 3.2.2)
\ replaces it. Limits are the stores' default capacities (64 names, levels
\ and terms; 32 declarations), which its tables hold whatever the
\ context's settings are: a larger file stops with full.
\ State: the export ni-export and four tables from export indices to
\ LeanForth's (names, levels, expressions) and one declaration buffer, all
\ global and test-only; single-threaded.

require ../../src/main.fs

export: ni-export
create ni-names lf-name-default cells allot          \ export name -> name ID
create ni-levels lf-level-default cells allot        \ export level -> level index
create ni-exprs lf-term-default 2* cells allot       \ export expression -> handle
create ni-pairs lf-cref-argument-capacity 2* cells allot
create ni-decl /lf-idecl allot

\ Table cells, refused (false) for an index past the table.
: ni-cell ( i table capacity -- addr true | false )
  rot tuck u> if cells + true else 2drop false then ;
: ni-name ( i -- id ) cells ni-names + @ ;
: ni-level@ ( i -- level ) cells ni-levels + @ ;
: ni-expr@ ( i -- index identity ) 2* cells ni-exprs + 2@ ;
: ni-root ( i -- term ) ni-expr@ drop ;
: ok-handler ( record -- outcome ) drop outcome-ok ;
\ Store x in cell i of a table: ok, or full past its capacity.
: ni-store ( x i table capacity -- outcome )
  ni-cell if ! outcome-ok else drop outcome-full then ;

\ Names (both passes see them; the first interns them).
: ni-name! ( id record -- outcome ) record-index @ ni-names lf-name-default ni-store ;
: ni-prefix ( record -- prefix ) name-prefix @ ni-name ;
: ni-digits ( c-addr u -- n ) 0 0 2swap >number 2drop drop ;
: ni-interned ( id true | false record -- outcome )
  swap if ni-name! else drop outcome-full then ;
: on-str ( record -- outcome )
  dup >r ni-prefix r@ name-part 2@ lf-name-str r> ni-interned ;
: on-num ( record -- outcome )
  dup >r ni-prefix r@ name-part 2@ ni-digits lf-name-num r> ni-interned ;
\ The first pass also puts every universe parameter in the level context.
: ni-context ( id -- outcome )
  dup lf-lscope-member? if drop outcome-ok exit then
  lf-lscope-context-add if outcome-ok else outcome-full then ;
: on-param-name ( record -- outcome ) param-name @ ni-name ni-context ;

\ Levels (second pass).
: ni-level-keep ( index true | false record -- outcome )
  swap 0= if drop outcome-full exit then
  record-index @ ni-levels lf-level-default ni-store ;
: ni-two ( record -- l r ) dup max-left @ ni-level@ swap max-right @ ni-level@ ;
: on-succ ( record -- outcome )
  dup >r succ-of @ ni-level@ lf-level-succ r> ni-level-keep ;
: on-max ( record -- outcome ) dup >r ni-two lf-level-max r> ni-level-keep ;
: on-imax ( record -- outcome ) dup >r ni-two lf-level-imax r> ni-level-keep ;
: on-param ( record -- outcome )
  dup >r param-name @ ni-name lf-level-param r> ni-level-keep ;
: ni-level-handle ( i -- index identity ) ni-level@ dup lf-level-identity 0= if 0 then ;

\ Expressions (second pass), kept as handles.
: ni-expr-keep ( index identity true | false record -- outcome )
  swap 0= if drop outcome-full exit then
  record-index @ dup lf-term-default u< 0= if drop 2drop outcome-full exit then
  2* cells ni-exprs + 2! outcome-ok ;
: on-bvar ( record -- outcome ) dup >r bvar-index @ lf-hterm-bvar r> ni-expr-keep ;
: on-sort ( record -- outcome )
  dup >r sort-level @ ni-level-handle lf-hterm-sort r> ni-expr-keep ;
: ni-arg! ( i k -- ) >r ni-level-handle swap r> 2* cells ni-pairs + 2! ;
: ni-arg ( record k -- record ) 2dup swap dup const-levels @ swap list-item swap ni-arg! ;
: ni-arity ( record -- n ) dup const-levels @ swap list-count ;
: ni-reference ( record n -- cref identity true | false )
  >r r@ 0 ?do i ni-arg loop const-name @ ni-name lf-name-generation @ ni-pairs r>
  lf-cref-new ;
: ni-constant ( record n -- index identity true | false )
  ni-reference if lf-cterm-new else false then ;
: on-const ( record -- outcome )
  dup ni-arity dup lf-cref-argument-capacity > if 2drop outcome-full exit then
  over >r ni-constant r> ni-expr-keep ;
\ Two children, at the field offsets first and second, as handles.
: ni-child ( record offset -- index identity ) + @ ni-expr@ ;
: ni-children ( record first second -- l lid r rid )
  >r over swap ni-child rot r> ni-child ;
: on-app ( record -- outcome )
  dup >r 0 app-fn 0 app-arg ni-children lf-hterm-app r> ni-expr-keep ;
: ni-binder ( record -- d did b bid ) 0 binder-type 0 binder-body ni-children ;
: on-lam ( record -- outcome ) dup >r ni-binder lf-hterm-lam r> ni-expr-keep ;
: on-forall ( record -- outcome ) dup >r ni-binder lf-hterm-pi r> ni-expr-keep ;
: ni-form ( record form -- outcome ) swap >r lf-hterm-unsupported r> ni-expr-keep ;
: on-let ( record -- outcome ) lf-form-let ni-form ;
: on-proj ( record -- outcome ) lf-form-proj ni-form ;
: on-natval ( record -- outcome ) lf-form-nat ni-form ;
: on-strval ( record -- outcome ) lf-form-string ni-form ;
: on-mdata ( record -- outcome ) lf-form-mdata ni-form ;

\ Declarations (second pass).
: ni-start ( record kind -- record )
  ni-decl /lf-idecl erase ni-decl lf-idecl-kind ! lf-hint-opaque ni-decl lf-idecl-hint !
  -1 ni-decl lf-idecl-value ! dup decl-name @ ni-name ni-decl lf-idecl-name !
  dup decl-type @ ni-root ni-decl lf-idecl-type ! ;
: ni-value ( record -- record ) dup decl-value @ ni-root ni-decl lf-idecl-value ! ;
: ni-safety ( safety -- ) ni-decl lf-idecl-safety ! ;
: ni-unsafe ( record -- record )
  dup decl-unsafe @ if lf-safety-unsafe else lf-safety-safe then ni-safety ;
: ni-hint ( record -- record )
  dup decl-hints @ dup ni-decl lf-idecl-hint ! lf-hint-regular =
  if dup decl-height @ ni-decl lf-idecl-height ! then ;
: ni-param-name ( record k -- id ) swap dup decl-params @ swap list-item ni-name ;
: ni-param ( record k -- record )
  2dup ni-param-name swap cells ni-decl lf-idecl-params + ! ;
: ni-params ( record -- record outcome )
  dup decl-params @ over list-count dup lf-param-capacity > if drop outcome-full exit then
  dup ni-decl lf-idecl-arity ! 0 ?do i ni-param loop outcome-ok ;
: ni-add ( record -- outcome )
  ni-params ok-then? 0= if exit then drop ni-decl lf-input-add nip ;
: ni-first-of-all ( record -- u ) 0 over decl-all @ rot list-item ;
: ni-alone? ( record -- flag )
  dup decl-all @ over list-count 1 = over ni-first-of-all rot decl-name @ = and ;
: ni-block? ( record -- record flag ) dup ni-alone? 0= ;
: on-thm ( record -- outcome )
  ni-block? if drop outcome-unsupported exit then
  lf-kind-theorem ni-start ni-value lf-safety-safe ni-safety ni-add ;
: on-def ( record -- outcome )
  ni-block? if drop outcome-unsupported exit then
  lf-kind-definition ni-start ni-value ni-hint dup decl-safety @ ni-safety ni-add ;
: on-opaque ( record -- outcome )
  ni-block? if drop outcome-unsupported exit then
  lf-kind-opaque ni-start ni-value ni-unsafe ni-add ;
: on-axiom ( record -- outcome ) lf-kind-axiom ni-start ni-unsafe ni-add ;

\ The two passes' handlers, in the reader's kind order; 0 is no handler
\ (reading stops as unsupported).
create ni-first
  ' ok-handler , ' on-str , ' on-num , ' ok-handler , ' ok-handler , ' ok-handler ,
  ' on-param-name , ' ok-handler , ' ok-handler , ' ok-handler , ' ok-handler ,
  ' ok-handler , ' ok-handler , ' ok-handler , ' ok-handler , ' ok-handler ,
  ' ok-handler , ' ok-handler , ' ok-handler , ' ok-handler , ' ok-handler ,
  ' ok-handler , 0 , 0 , 0 , 0 , 0 ,
create ni-second
  ' ok-handler , ' ok-handler , ' ok-handler , ' on-succ , ' on-max , ' on-imax ,
  ' on-param , ' on-bvar , ' on-sort , ' on-const , ' on-app , ' on-lam , ' on-forall ,
  ' on-let , ' on-proj , ' on-natval , ' on-strval , ' on-mdata , ' on-axiom , ' on-def ,
  ' on-thm , ' on-opaque , 0 , 0 , 0 , 0 , 0 ,
: ni-handler! ( xt|0 kind -- )
  over 0= if 2drop exit then ni-export export-handler ! ;
: ni-handlers ( table -- )
  ni-export export-handlers-clear
  kind-count 0 do dup i cells + @ i ni-handler! loop drop ;
: ni-pass ( c-addr u table -- outcome ) ni-handlers ni-export export-read ;

\ A fresh input in this context.
: ni-fresh ( -- )
  lf-name-reset lf-level-reset lf-term-reset lf-lscope-context-reset lf-cref-reset
  lf-input-reset ni-names lf-name-default cells erase
  ni-levels lf-level-default cells erase ;
: ni-passes ( c-addr u -- outcome )
  2dup ni-first ni-pass dup ok? 0= if nip nip exit then drop
  lf-ssession-begin 0= if 2drop outcome-invalid exit then
  ni-second ni-pass dup ok? if drop lf-input-end then ;
\ Read the export file c-addr u into this context's input, replacing what
\ was there, and end loading: ok, or the reader's, a handler's or
\ lf-input-end's outcome.
: ni-read ( c-addr u -- outcome )
  ni-export export-init dup ok? 0= if nip nip exit then drop
  ni-fresh ni-passes ni-export export-free ;

\ Check what ni-read loaded with check-declaration, each declaration with
\ fuel, and print each one's name and verdict; the environment is freed.
: ni-name. ( d -- ) lf-input-name ['] type lf-pp-name-to ;
: ni-verdict ( d -- ) dup ni-name. ." : " lf-check-verdict. cr ;
: ni-report ( -- ) lf-env-view drop lf-input-count 0 ?do i ni-verdict loop ;
: ni-checked ( env outcome -- )
  ok? 0= abort" ndjson-input: the run stopped" ni-report lf-env-free drop ;
: ni-check ( c-addr u fuel -- )
  >r ni-read ok? 0= abort" ndjson-input: not read" r> 64 lf-check-input ni-checked ;

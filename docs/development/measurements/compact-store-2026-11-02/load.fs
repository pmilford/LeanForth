\ Prototype (ADR 0016, measurement code): NDJSON reader handlers that fill
\ the compact store. Export indices are mapped to store ids through emap,
\ nmap and lmap (load-time arrays). Not a module of src/.
require ../../../../src/import/ndjson.fs
require ../../../../src/lib/u32.fs
require ./arena.fs
require ./compact.fs

arena: emap  arena: nmap  arena: lmap
: maps-init ( -- )
  1 20 lshift emap arena-init 1 16 lshift nmap arena-init 1 12 lshift lmap arena-init
  0 nmap arena-push 0 lmap arena-push ;
: >nid ( export -- id ) nmap arena@ ;
: >level ( export -- id ) lmap arena@ ;
: >expr ( export -- id ) emap arena@ ;
: ok ( -- outcome ) outcome-ok ;
: 3dup ( a b c -- a b c a b c ) 2 pick 2 pick 2 pick ;

\ Names.
: digits>u32 ( addr u -- n true | false )
  0 0 2swap >number nip if 2drop false exit then
  if drop false exit then dup u32-mask u> if drop false else true then ;
: on-str ( record -- outcome )
  dup name-prefix @ >nid swap name-part 2@ nkey-str name-intern nmap arena-push ok ;
: on-num ( record -- outcome )
  dup name-prefix @ >nid swap name-part 2@ digits>u32 0= if drop outcome-full exit then
  nkey-num name-intern nmap arena-push ok ;

\ Levels.
: lp ( level -- bit ) l-data@ lp-bit and ;
: on-succ ( record -- outcome )
  succ-of @ >level lv-succ swap 0 over lp level-intern lmap arena-push ok ;
: lv-pair ( record tag -- id )
  >r dup max-left @ >level swap max-right @ >level r> -rot 2dup lp swap lp or level-intern ;
: on-max ( record -- outcome ) lv-max lv-pair lmap arena-push ok ;
: on-imax ( record -- outcome ) lv-imax lv-pair lmap arena-push ok ;
: on-param ( record -- outcome )
  param-name @ >nid 4 lshift lv-param or 0 0 lp-bit level-intern lmap arena-push ok ;

\ Expressions.
1 27 lshift constant payload-limit
: >ehead ( tag payload -- head ) 5 lshift or ;
: e! ( id -- outcome ) emap arena-push ok ;
: on-bvar ( record -- outcome )
  bvar-index @ dup range-max u< 0= if drop outcome-full exit then
  t-bvar over 0 0 4 roll 1+ 0 0 >data expr-intern e! ;
: on-sort ( record -- outcome )
  sort-level @ >level t-sort over 0 0 4 roll lp 0 swap 0 >data expr-intern e! ;
: levels-list ( list record -- id lp )
  lists-start 0 -rot 2dup list-count 0 ?do
    i 2 pick 2 pick list-item >level dup lp 4 roll or >r li! r> -rot loop
  2drop list-intern swap ;
: on-const ( record -- outcome )
  dup const-name @ >nid swap dup const-levels @ swap levels-list
  >r t-const -rot 0 0 r> 0 >data expr-intern e! ;
: on-app ( record -- outcome )
  dup app-fn @ >expr swap app-arg @ >expr
  t-app -rot 0 2 pick e-data@ 2 pick e-data@ false data2 expr-intern e! ;
: binder-head ( record tag -- head )
  over binder-info @ + swap binder-name @ >nid >ehead ;
: binder ( record tag -- outcome )
  over swap binder-head swap dup binder-type @ >expr swap binder-body @ >expr
  0 2 pick e-data@ 2 pick e-data@ true data2 expr-intern e! ;
: on-lam ( record -- outcome ) t-lam binder ;
: on-forall ( record -- outcome ) t-forall binder ;
: let-data ( type value body -- d )
  e-data@ swap e-data@ rot e-data@ 2dup or 3 pick or d-flags >r
  over d-range over d-range max 3 pick d-range lower max >r
  d-depth swap d-depth max swap d-depth max 1+ r> r> rot >data ;
: on-let ( record -- outcome )
  dup let-nondep @ if t-let-nondep else t-let then over let-name @ >nid >ehead
  swap dup let-type @ >expr over let-value @ >expr rot let-body @ >expr
  3dup let-data expr-intern e! ;
: on-proj ( record -- outcome )
  dup proj-idx @ dup u32-mask u> if 2drop outcome-full exit then
  over proj-type-name @ >nid t-proj swap >ehead rot proj-struct @ >expr rot
  0 2 pick e-data@ dup d-range over d-flags rot d-depth 1+ >data expr-intern e! ;
: on-natval ( record -- outcome ) t-natlit swap literal-text 2@ lit-intern 0 0 0 expr-intern e! ;
: on-strval ( record -- outcome ) t-strlit swap literal-text 2@ lit-intern 0 0 0 expr-intern e! ;
: on-mdata ( record -- outcome ) drop outcome-unsupported ;

\ Declarations.
: names-list ( list record -- id )
  lists-start 2dup list-count 0 ?do i 2 pick 2 pick list-item >nid li! loop
  2drop list-intern ;
: decl-head ( record kind -- record id )
  over decl-name @ >nid 2 pick dup decl-params @ swap names-list
  3 pick decl-type @ >expr decl-new ;
: decl-value! ( record id -- ) swap decl-value @ >expr swap decl 4 quad + u32! ;
: valued ( record kind -- outcome ) decl-head decl-value! ok ;
: plain ( record kind -- outcome ) decl-head 2drop ok ;
: on-thm ( record -- outcome ) k-thm valued ;
: on-def ( record -- outcome ) k-def valued ;
: on-opaque ( record -- outcome ) k-opaque valued ;
: on-axiom ( record -- outcome ) k-axiom plain ;
: on-quot ( record -- outcome ) k-quot plain ;
variable blocks
: on-inductive ( record -- outcome ) drop 1 blocks +! ok ;
: on-type ( record -- outcome ) k-induct plain ;
: on-ctor ( record -- outcome ) k-ctor plain ;
: rules-list ( record -- id )
  lists-start dup recursor-rules @ over list-count 0 ?do
    i over recursor-rule rule-rhs @ >expr li! loop drop list-new ;
: on-recursor ( record -- outcome )
  k-rec decl-head swap rules-list swap decl 6 quad + u32! ok ;

create handlers
  ' drop , ' on-str , ' on-num , ' on-succ , ' on-max , ' on-imax , ' on-param ,
  ' on-bvar , ' on-sort , ' on-const , ' on-app , ' on-lam , ' on-forall , ' on-let ,
  ' on-proj , ' on-natval , ' on-strval , ' on-mdata , ' on-axiom , ' on-def , ' on-thm ,
  ' on-opaque , ' on-quot , ' on-inductive , ' on-type , ' on-ctor , ' on-recursor ,
: on-meta ( record -- outcome ) drop ok ;
' on-meta handlers !
export: library
: load-start ( -- )
  library export-init outcome-ok <> abort" export-init"
  kind-count 0 do handlers i cells + @ i library export-handler ! loop
  compact-init maps-init 0 blocks ! ;
: .load-error ( -- )
  library export-error ." line " rot . ." field " type ."  why " type cr ;
: load-file ( c-addr u -- outcome )
  load-start library export-read dup outcome-ok <> if ." load failed: " dup . .load-error then ;

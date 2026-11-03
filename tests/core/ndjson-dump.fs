\ Test driver: print every record the Forth NDJSON reader decodes, one
\ line per record, in the canonical text form that
\ tests/support/ndjson_dump.py prints from Python's json module, so that
\ the two can be compared field by field. Strings are printed as the hex
\ of their UTF-8 bytes; flags as 1 or 0; enumerations as their codes;
\ lists as [a,b,...]. Usage:
\   gforth tests/core/ndjson-dump.fs -e 's" FILE" dump-export bye'
\ On failure the last line is "error: OUTCOME LINE", the outcome a number.
require ../../src/import/ndjson.fs

export: dumped

: .int ( n -- ) space 0 .r ;
: .flag ( flag -- ) 0<> 1 and .int ;
: .hex-byte ( c -- ) base @ >r hex 0 <# # # #> type r> base ! ;
: .hex ( addr u -- )
  space dup 0= if 2drop ." -" exit then over + swap ?do i c@ .hex-byte loop ;
: .text ( text-addr -- ) 2@ .hex ;
: .digits ( text-addr -- ) space 2@ type ;
: .item ( list record i -- ) dup if ." ," then -rot list-item 0 .r ;
: .list ( list record -- )
  space ." [" 2dup list-count 0 ?do 2dup i .item loop 2drop ." ]" ;
: .head ( record c-addr u -- ) type record-index @ .int ;
: ended ( record -- outcome ) drop cr outcome-ok ;

: on-meta ( record -- outcome )
  dup s" meta" .head dup meta-exporter .text dup meta-exporter-version .text
  dup meta-lean-githash .text dup meta-lean-version .text
  dup meta-format-version .text ended ;
: on-str ( record -- outcome )
  dup s" name.str" .head dup name-prefix @ .int dup name-part .text ended ;
: on-num ( record -- outcome )
  dup s" name.num" .head dup name-prefix @ .int dup name-part .digits ended ;
: on-succ ( record -- outcome ) dup s" level.succ" .head dup succ-of @ .int ended ;
: .pair ( record -- ) dup max-left @ .int max-right @ .int ;
: on-max ( record -- outcome ) dup s" level.max" .head dup .pair ended ;
: on-imax ( record -- outcome ) dup s" level.imax" .head dup .pair ended ;
: on-param ( record -- outcome ) dup s" level.param" .head dup param-name @ .int ended ;
: on-bvar ( record -- outcome ) dup s" expr.bvar" .head dup bvar-index @ .int ended ;
: on-sort ( record -- outcome ) dup s" expr.sort" .head dup sort-level @ .int ended ;
: on-const ( record -- outcome )
  dup s" expr.const" .head dup const-name @ .int dup const-levels @ over .list ended ;
: on-app ( record -- outcome )
  dup s" expr.app" .head dup app-fn @ .int dup app-arg @ .int ended ;
: .binder ( record -- )
  dup binder-name @ .int dup binder-type @ .int dup binder-body @ .int binder-info @ .int ;
: on-lam ( record -- outcome ) dup s" expr.lam" .head dup .binder ended ;
: on-forall ( record -- outcome ) dup s" expr.forallE" .head dup .binder ended ;
: on-let ( record -- outcome )
  dup s" expr.letE" .head dup let-name @ .int dup let-type @ .int dup let-value @ .int
  dup let-body @ .int dup let-nondep @ .flag ended ;
: on-proj ( record -- outcome )
  dup s" expr.proj" .head dup proj-type-name @ .int dup proj-idx @ .int
  dup proj-struct @ .int ended ;
: on-natval ( record -- outcome )
  dup s" expr.natVal" .head dup literal-text .digits ended ;
: on-strval ( record -- outcome ) dup s" expr.strVal" .head dup literal-text .text ended ;
: on-mdata ( record -- outcome ) dup s" expr.mdata" .head dup mdata-expr @ .int ended ;
: .decl ( record -- ) dup decl-name @ .int dup decl-params @ over .list decl-type @ .int ;
: on-axiom ( record -- outcome )
  dup s" decl.axiom" .head dup .decl dup decl-unsafe @ .flag ended ;
: on-def ( record -- outcome )
  dup s" decl.def" .head dup .decl dup decl-value @ .int dup decl-hints @ .int
  dup decl-hints @ 2 = if dup decl-height @ else 0 then .int
  dup decl-safety @ .int dup decl-all @ over .list ended ;
: on-thm ( record -- outcome )
  dup s" decl.thm" .head dup .decl dup decl-value @ .int dup decl-all @ over .list ended ;
: on-opaque ( record -- outcome )
  dup s" decl.opaque" .head dup .decl dup decl-value @ .int dup decl-unsafe @ .flag
  dup decl-all @ over .list ended ;
: on-quot ( record -- outcome )
  dup s" decl.quot" .head dup .decl dup decl-quot-kind @ .int ended ;
: on-inductive ( record -- outcome )
  dup s" decl.inductive" .head dup block-types @ over list-count .int
  dup block-ctors @ over list-count .int dup block-recursors @ over list-count .int ended ;
: on-type ( record -- outcome )
  dup s" ind.type" .head dup .decl dup type-num-params @ .int dup type-num-indices @ .int
  dup type-all @ over .list dup type-ctors @ over .list dup type-num-nested @ .int
  dup type-rec @ .flag dup type-unsafe @ .flag dup type-reflexive @ .flag ended ;
: on-ctor ( record -- outcome )
  dup s" ind.ctor" .head dup .decl dup ctor-induct @ .int dup ctor-cidx @ .int
  dup ctor-num-params @ .int dup ctor-num-fields @ .int dup ctor-unsafe @ .flag ended ;
: .rule ( i record -- )
  recursor-rule dup rule-ctor @ 0 .r ." :" dup rule-fields @ 0 .r ." :" rule-rhs @ 0 .r ;
: .rule-item ( record i -- record ) dup if ." ," then over .rule ;
: .rules ( record -- )
  space ." [" dup recursor-rules @ over list-count 0 ?do i .rule-item loop drop ." ]" ;
: on-recursor ( record -- outcome )
  dup s" ind.rec" .head dup .decl dup recursor-all @ over .list
  dup recursor-num-params @ .int dup recursor-num-indices @ .int
  dup recursor-num-motives @ .int dup recursor-num-minors @ .int
  dup recursor-k @ .flag dup recursor-unsafe @ .flag dup .rules ended ;

create dump-handlers
  ' on-meta , ' on-str , ' on-num , ' on-succ , ' on-max , ' on-imax , ' on-param ,
  ' on-bvar , ' on-sort , ' on-const , ' on-app , ' on-lam , ' on-forall , ' on-let ,
  ' on-proj , ' on-natval , ' on-strval , ' on-mdata , ' on-axiom , ' on-def , ' on-thm ,
  ' on-opaque , ' on-quot , ' on-inductive , ' on-type , ' on-ctor , ' on-recursor ,
: dump-start ( -- outcome )
  dumped export-init kind-count 0 do dump-handlers i cells + @ i dumped export-handler ! loop ;
\ Print every record of the export named c-addr u, then "ok", or an error line.
: dump-export ( c-addr u -- )
  dump-start drop dumped export-read dup ok?
  if drop ." ok" cr else ." error:" .int dumped export-error 2drop 2drop .int cr then ;

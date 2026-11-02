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

: .n ( n -- ) space 0 .r ;
: .flag ( flag -- ) 0<> 1 and .n ;
: .hex-byte ( c -- ) base @ >r hex 0 <# # # #> type r> base ! ;
: .hex ( addr u -- )
  space dup 0= if 2drop ." -" exit then bounds ?do i c@ .hex-byte loop ;
: .text ( text-addr -- ) 2@ .hex ;
: .digits ( text-addr -- ) space 2@ type ;
: .item ( list record i -- ) dup if ." ," then -rot list-item 0 .r ;
: .list ( list record -- )
  space ." [" 2dup list-count 0 ?do 2dup i .item loop 2drop ." ]" ;
: .head ( record c-addr u -- ) type record-index @ .n ;
: ended ( record -- outcome ) drop cr outcome-ok ;

: on-meta ( record -- outcome )
  dup s" meta" .head dup meta-exporter .text dup meta-exporter-version .text
  dup meta-lean-githash .text dup meta-lean-version .text
  dup meta-format-version .text ended ;
: on-str ( record -- outcome )
  dup s" name.str" .head dup name-prefix @ .n dup name-part .text ended ;
: on-num ( record -- outcome )
  dup s" name.num" .head dup name-prefix @ .n dup name-part .digits ended ;
: on-succ ( record -- outcome ) dup s" level.succ" .head dup succ-of @ .n ended ;
: .pair ( record -- ) dup max-left @ .n max-right @ .n ;
: on-max ( record -- outcome ) dup s" level.max" .head dup .pair ended ;
: on-imax ( record -- outcome ) dup s" level.imax" .head dup .pair ended ;
: on-param ( record -- outcome ) dup s" level.param" .head dup param-name @ .n ended ;
: on-bvar ( record -- outcome ) dup s" expr.bvar" .head dup bvar-index @ .n ended ;
: on-sort ( record -- outcome ) dup s" expr.sort" .head dup sort-level @ .n ended ;
: on-const ( record -- outcome )
  dup s" expr.const" .head dup const-name @ .n dup const-levels @ over .list ended ;
: on-app ( record -- outcome )
  dup s" expr.app" .head dup app-fn @ .n dup app-arg @ .n ended ;
: .binder ( record -- )
  dup binder-name @ .n dup binder-type @ .n dup binder-body @ .n binder-info @ .n ;
: on-lam ( record -- outcome ) dup s" expr.lam" .head dup .binder ended ;
: on-forall ( record -- outcome ) dup s" expr.forallE" .head dup .binder ended ;
: on-let ( record -- outcome )
  dup s" expr.letE" .head dup let-name @ .n dup let-type @ .n dup let-value @ .n
  dup let-body @ .n dup let-nondep @ .flag ended ;
: on-proj ( record -- outcome )
  dup s" expr.proj" .head dup proj-type-name @ .n dup proj-idx @ .n
  dup proj-struct @ .n ended ;
: on-natval ( record -- outcome )
  dup s" expr.natVal" .head dup literal-text .digits ended ;
: on-strval ( record -- outcome ) dup s" expr.strVal" .head dup literal-text .text ended ;
: on-mdata ( record -- outcome ) dup s" expr.mdata" .head dup mdata-expr @ .n ended ;
: .decl ( record -- ) dup decl-name @ .n dup decl-params @ over .list decl-type @ .n ;
: on-axiom ( record -- outcome )
  dup s" decl.axiom" .head dup .decl dup decl-unsafe @ .flag ended ;
: on-def ( record -- outcome )
  dup s" decl.def" .head dup .decl dup decl-value @ .n dup decl-hints @ .n
  dup decl-hints @ 2 = if dup decl-height @ else 0 then .n
  dup decl-safety @ .n dup decl-all @ over .list ended ;
: on-thm ( record -- outcome )
  dup s" decl.thm" .head dup .decl dup decl-value @ .n dup decl-all @ over .list ended ;
: on-opaque ( record -- outcome )
  dup s" decl.opaque" .head dup .decl dup decl-value @ .n dup decl-unsafe @ .flag
  dup decl-all @ over .list ended ;
: on-quot ( record -- outcome )
  dup s" decl.quot" .head dup .decl dup decl-quot-kind @ .n ended ;
: on-inductive ( record -- outcome )
  dup s" decl.inductive" .head dup block-types @ over list-count .n
  dup block-ctors @ over list-count .n dup block-recursors @ over list-count .n ended ;
: on-type ( record -- outcome )
  dup s" ind.type" .head dup .decl dup type-num-params @ .n dup type-num-indices @ .n
  dup type-all @ over .list dup type-ctors @ over .list dup type-num-nested @ .n
  dup type-rec @ .flag dup type-unsafe @ .flag dup type-reflexive @ .flag ended ;
: on-ctor ( record -- outcome )
  dup s" ind.ctor" .head dup .decl dup ctor-induct @ .n dup ctor-cidx @ .n
  dup ctor-num-params @ .n dup ctor-num-fields @ .n dup ctor-unsafe @ .flag ended ;
: .rule ( i record -- )
  recursor-rule dup rule-ctor @ 0 .r ." :" dup rule-fields @ 0 .r ." :" rule-rhs @ 0 .r ;
: .rule-item ( record i -- record ) dup if ." ," then over .rule ;
: .rules ( record -- )
  space ." [" dup recursor-rules @ over list-count 0 ?do i .rule-item loop drop ." ]" ;
: on-recursor ( record -- outcome )
  dup s" ind.rec" .head dup .decl dup recursor-all @ over .list
  dup recursor-num-params @ .n dup recursor-num-indices @ .n
  dup recursor-num-motives @ .n dup recursor-num-minors @ .n
  dup recursor-k @ .flag dup recursor-unsafe @ .flag dup .rules ended ;

create dump-handlers
  ' on-meta , ' on-str , ' on-num , ' on-succ , ' on-max , ' on-imax , ' on-param ,
  ' on-bvar , ' on-sort , ' on-const , ' on-app , ' on-lam , ' on-forall , ' on-let ,
  ' on-proj , ' on-natval , ' on-strval , ' on-mdata , ' on-axiom , ' on-def , ' on-thm ,
  ' on-opaque , ' on-quot , ' on-inductive , ' on-type , ' on-ctor , ' on-recursor ,
: dump-start ( -- outcome )
  dumped export-free dumped export-init
  kind-count 0 do dump-handlers i cells + @ i dumped export-handler ! loop ;
\ Print every record of the export named c-addr u, then "ok", or an error line.
: dump-export ( c-addr u -- )
  dump-start drop dumped export-read dup ok?
  if drop ." ok" cr else ." error:" .n dumped export-error 2drop 2drop .n cr then ;

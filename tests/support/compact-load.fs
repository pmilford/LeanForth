\ Test support: load a Lean export through the NDJSON reader
\ (src/import/ndjson.fs) into a compact input tier (src/core/compact.fs),
\ then re-emit every name, level and expression record in the reader's
\ dump format (tests/core/ndjson-dump.fs), and measure the load: ADR 0016's
\ prototype, made with the library. Not a module of src/: the importer
\ stage (ADR 0016 C9 step 2) will turn these handlers into src/import/
\ code. One load at a time: the state is one record, compact-loaded.
\
\ Export indices map to store numbers through slabs of 32-bit fields
\ (names, levels, expressions), kept for the re-emission, which prints each
\ record from the store with its references turned back into export
\ indices through inverse maps (the first export index of each store
\ number). So a merge of two different records by hash-consing, or any
\ field read back wrong, shows as a changed line.
\
\ Entry words: compact-load ( c-addr u log2 -- outcome ) loads and seals,
\ the expression table pre-sized to 2^log2 slots; compact-emit ( -- )
\ prints the dump lines; compact-stats ( -- ) prints sizes and table
\ statistics; compact-lookups ( -- ) looks every declaration's name up by
\ its text through a scratch tier and checks the number; compact-free
\ ( -- ); and the two drivers compact-dump ( c-addr u -- ), used by
\ tests/core/compact-verify.sh, and compact-measure ( c-addr u log2 -- ).
\ Uses Gforth's utime for timings. Usage, for example:
\   gforth-fast tests/support/compact-load.fs -e 's" init.ndjson" 24 compact-measure bye'

require ../../src/import/ndjson.fs
require ../../src/core/compact.fs

create compact-tier /tier allot
create compact-scratch /tier allot
begin-structure /compact-load
  /slab +field name-map
  /slab +field level-map
  /slab +field expr-map
  /slab +field decl-map       \ per declaration record: its name number
  /slab +field name-inverse   \ store number -> first export index
  /slab +field level-inverse
  /slab +field expr-inverse
  /slab +field comp-stack     \ components of a name being looked up
  field: load-blocks          \ inductive blocks
end-structure
create compact-loaded /compact-load allot
export: compact-export

\ The maps: slabs of 32-bit fields.
: map-init ( map -- outcome ) 1 u32s cons-numbers-max rot slab-init ;
: map@ ( i map -- u ) slab-at u32@ ;
: map-push ( u map -- outcome )
  1 over slab-claim dup ok? if drop swap slab-at u32! outcome-ok else >r 2drop drop r> then ;
\ Keep a builder's result as the next export index's.
: kept ( n outcome map -- outcome ) swap dup ok? if drop map-push else nip nip then ;
: export>name ( export -- n ) compact-loaded name-map map@ ;
: export>level ( export -- l ) compact-loaded level-map map@ ;
: export>expr ( export -- e ) compact-loaded expr-map map@ ;
: names-kept ( n outcome -- outcome ) compact-loaded name-map kept ;
: levels-kept ( l outcome -- outcome ) compact-loaded level-map kept ;
: exprs-kept ( e outcome -- outcome ) compact-loaded expr-map kept ;

\ Names.
: on-str ( record -- outcome )
  dup name-prefix @ export>name swap name-part 2@ compact-tier name-str names-kept ;
: digits>u32 ( addr u -- u true | false )
  digits>u if dup u32-mask u> if drop false else true then else false then ;
: on-num ( record -- outcome )
  dup name-prefix @ export>name swap name-part 2@ digits>u32 0= if drop outcome-full exit then
  compact-tier name-num names-kept ;

\ Levels.
: on-succ ( record -- outcome ) succ-of @ export>level compact-tier level-succ levels-kept ;
: level-pair ( record -- l1 l2 ) dup max-left @ export>level swap max-right @ export>level ;
: on-max ( record -- outcome ) level-pair compact-tier level-max levels-kept ;
: on-imax ( record -- outcome ) level-pair compact-tier level-imax levels-kept ;
: on-param ( record -- outcome ) param-name @ export>name compact-tier level-param levels-kept ;

\ Lists of the reader's record as tuples of the tier, each item mapped by
\ xt ( export -- n ).
: tuple-item, ( list record xt i -- list record xt outcome )
  >r 2 pick 2 pick r> -rot list-item over execute compact-tier tier-tuples tuple-add ;
: list-items, ( list record xt -- outcome )
  2 pick 2 pick list-count 0 ?do
    i tuple-item, dup ok? 0= if nip nip nip unloop exit then drop
  loop drop 2drop outcome-ok ;
: list>tuple ( list record xt -- t outcome )
  compact-tier tier-tuples tuple-start dup ok? 0= if nip nip nip no-result exit then drop
  list-items, dup ok? 0= if no-result exit then drop compact-tier tier-tuples tuple-end ;

\ Expressions.
: on-bvar ( record -- outcome ) bvar-index @ compact-tier expr-bvar exprs-kept ;
: on-sort ( record -- outcome ) sort-level @ export>level compact-tier expr-sort exprs-kept ;
: on-const ( record -- outcome )
  dup const-name @ export>name swap dup const-levels @ swap ['] export>level list>tuple
  dup ok? 0= if nip nip exit then drop compact-tier expr-const exprs-kept ;
: on-app ( record -- outcome )
  dup app-fn @ export>expr swap app-arg @ export>expr compact-tier expr-app exprs-kept ;
: binder-parts ( record -- name info type body )
  dup binder-name @ export>name over binder-info @ 2 pick binder-type @ export>expr
  3 roll binder-body @ export>expr ;
: on-lam ( record -- outcome )
  binder-parts >r >r lam-head r> r> compact-tier expr-make exprs-kept ;
: on-forall ( record -- outcome )
  binder-parts >r >r pi-head r> r> compact-tier expr-make exprs-kept ;
: on-let ( record -- outcome )
  dup let-name @ export>name over let-nondep @ let-head over let-type @ export>expr
  2 pick let-value @ export>expr 3 roll let-body @ export>expr compact-tier expr-let exprs-kept ;
: on-proj ( record -- outcome )
  dup proj-idx @ u32-mask u> if drop outcome-full exit then
  dup proj-type-name @ export>name proj-head over proj-struct @ export>expr rot proj-idx @
  compact-tier expr-make exprs-kept ;
: record-literal ( record -- t outcome ) literal-text 2@ compact-tier tier-texts text-intern ;
: on-natval ( record -- outcome )
  record-literal dup ok? if drop compact-tier expr-nat else nip no-result then exprs-kept ;
: on-strval ( record -- outcome )
  record-literal dup ok? if drop compact-tier expr-str else nip no-result then exprs-kept ;
: on-mdata ( record -- outcome ) drop outcome-unsupported ;

\ Declarations: only their names are kept (for the lookups), and their
\ parameter lists become tuples of names.
: on-decl ( record -- outcome )
  dup decl-params @ over ['] export>name list>tuple nip dup ok? 0= if nip exit then drop
  decl-name @ export>name compact-loaded decl-map map-push ;
: on-block ( record -- outcome ) drop 1 compact-loaded load-blocks +! outcome-ok ;
: on-meta ( record -- outcome ) drop outcome-ok ;

create compact-handlers
  ' on-meta , ' on-str , ' on-num , ' on-succ , ' on-max , ' on-imax , ' on-param ,
  ' on-bvar , ' on-sort , ' on-const , ' on-app , ' on-lam , ' on-forall , ' on-let ,
  ' on-proj , ' on-natval , ' on-strval , ' on-mdata , ' on-decl , ' on-decl , ' on-decl ,
  ' on-decl , ' on-decl , ' on-block , ' on-decl , ' on-decl , ' on-decl ,

create compact-maps ' name-map , ' level-map , ' expr-map , ' decl-map , ' name-inverse ,
  ' level-inverse , ' expr-inverse , ' comp-stack ,
8 constant #compact-maps
: compact-map ( i -- map ) cells compact-maps + @ compact-loaded swap execute ;
: maps-init ( -- outcome )
  compact-loaded /compact-load erase
  #compact-maps 0 do i compact-map map-init dup ok? 0= if unloop exit then drop loop
  outcome-ok ;
\ The anonymous name and level zero are export index 0 of their families.
: maps-start ( -- outcome )
  0 compact-loaded name-map map-push 0 compact-loaded level-map map-push or 0= flag>outcome ;
: handlers-set ( -- )
  kind-count 0 do compact-handlers i cells + @ i compact-export export-handler ! loop ;
: load-start ( log2 -- outcome )
  12 compact-tier tier-init dup ok? 0= if nip exit then drop
  compact-tier tier-exprs cons-table htab-presize dup ok? 0= if exit then drop
  compact-export export-init dup ok? 0= if exit then drop handlers-set
  maps-init dup ok? 0= if exit then drop maps-start ;
: .load-error ( -- )
  compact-export export-error 2>r 2>r ." line " . ." field " 2r> type ."  why " 2r> type cr ;
\ Load and seal the export named c-addr u, its expression table starting at 2^log2
\ slots: ok, or the failing outcome after printing where.
: compact-load ( c-addr u log2 -- outcome )
  load-start dup ok? 0= if nip nip exit then drop
  compact-export export-read dup ok? 0= if ." load failed: " dup . .load-error exit then
  drop compact-tier tier-seal ;
: compact-free ( -- )
  compact-tier tier-free compact-export export-free
  #compact-maps 0 do i compact-map slab-free loop ;

\ ---- Re-emission in tests/core/ndjson-dump.fs's format.
: inverse-init ( count map -- outcome )
  dup slab-clear 2dup slab-claim nip dup ok? 0= if nip nip exit then drop
  swap 0 ?do u32-mask i 2 pick slab-at u32! loop drop outcome-ok ;
: inverse-note ( n i inverse -- )
  rot over slab-at dup u32@ u32-mask = if nip u32! else 2drop drop then ;
\ Fill inverse from map: the first export index of each of count numbers.
: inverse-build ( map count inverse -- outcome )
  tuck inverse-init dup ok? 0= if nip nip exit then drop
  over slab-count 0 ?do i 2 pick map@ i 2 pick inverse-note loop 2drop outcome-ok ;
: inverses ( -- outcome )
  compact-loaded name-map compact-tier tier-names cons-numbers compact-loaded name-inverse
  inverse-build compact-loaded level-map compact-tier tier-levels cons-numbers
  compact-loaded level-inverse inverse-build or compact-loaded expr-map
  compact-tier tier-exprs cons-numbers compact-loaded expr-inverse inverse-build or
  0= flag>outcome ;
: name-index ( n -- i ) compact-loaded name-inverse map@ ;
: level-index ( l -- i ) compact-loaded level-inverse map@ ;
: expr-index ( e -- i ) compact-loaded expr-inverse map@ ;

: .int ( n -- ) space 0 .r ;
: .hex-byte ( c -- ) base @ >r hex 0 <# # # #> type r> base ! ;
: .hex ( addr u -- ) space dup 0= if 2drop ." -" exit then over + swap ?do i c@ .hex-byte loop ;
: .head ( i c-addr u -- ) type .int ;

: emit-name ( i -- )
  dup export>name dup compact-tier name-tag@ tag-name-str =
  if swap s" name.str" .head dup compact-tier name-prefix@ name-index .int
    compact-tier name-text@ .hex
  else swap s" name.num" .head dup compact-tier name-prefix@ name-index .int
    compact-tier name-number@ .int then cr ;
: .level-a ( l -- ) compact-tier level-a@ level-index .int ;
: .level-b ( l -- ) compact-tier level-b@ level-index .int ;
: emit-level ( i -- )
  dup export>level dup compact-tier level-tag@ case
    tag-level-succ of swap s" level.succ" .head .level-a endof
    tag-level-max of swap s" level.max" .head dup .level-a .level-b endof
    tag-level-imax of swap s" level.imax" .head dup .level-a .level-b endof
    tag-level-param of swap s" level.param" .head compact-tier level-name@ name-index .int endof
    nip ." level.?" swap .int endcase cr ;
: .e ( e -- ) expr-index .int ;
: .list ( t -- )
  space ." [" compact-tier tier-tuples 2dup tuple-length 0 ?do
    i if ." ," then i 2 pick 2 pick tuple-item level-index 0 .r loop 2drop ." ]" ;
: .payload-name ( e -- ) compact-tier expr-payload@ name-index .int ;
: emit-binder ( i e -- )
  dup compact-tier expr-tag@ tag-pi < if ." expr.lam" else ." expr.forallE" then
  swap .int dup .payload-name dup compact-tier expr-a@ .e dup compact-tier expr-b@ .e
  compact-tier expr-tag@ tag-lam - 3 and .int ;
: emit-let ( i e -- )
  ." expr.letE" swap .int dup .payload-name dup compact-tier expr-a@ .e
  dup compact-tier expr-b@ .e dup compact-tier expr-body@ .e
  compact-tier expr-tag@ tag-let-nondep = 1 and .int ;
: emit-proj ( i e -- )
  ." expr.proj" swap .int dup .payload-name dup compact-tier expr-b@ .int compact-tier expr-a@ .e ;
: .text ( e -- addr u ) compact-tier expr-a@ compact-tier tier-texts text@ ;
: emit-other ( i e tag -- )
  case
    tag-bvar of ." expr.bvar" swap .int compact-tier expr-a@ .int endof
    tag-sort of ." expr.sort" swap .int compact-tier expr-a@ level-index .int endof
    tag-const of ." expr.const" swap .int dup compact-tier expr-a@ name-index .int
      compact-tier expr-b@ .list endof
    tag-app of ." expr.app" swap .int dup compact-tier expr-a@ .e compact-tier expr-b@ .e endof
    tag-nat of ." expr.natVal" swap .int .text space type endof
    tag-str of ." expr.strVal" swap .int .text .hex endof
    ." expr.?" >r 2drop r>
  endcase ;
: emit-expr ( i e -- )
  dup compact-tier expr-tag@ dup binder-tag? if drop emit-binder else
  dup let-tag? if drop emit-let else dup tag-proj = if drop emit-proj else emit-other
  then then then cr ;

: emit-names ( -- )
  compact-loaded name-map slab-count 1 ?do i emit-name loop ;
: emit-levels ( -- )
  compact-loaded level-map slab-count 1 ?do i emit-level loop ;
: emit-exprs ( -- )
  compact-loaded expr-map slab-count 0 ?do i dup export>expr emit-expr loop ;
\ Print every name, level and expression record, in export order.
: compact-emit ( -- )
  inverses ok? 0= abort" compact-emit: no room for the inverse maps"
  emit-names emit-levels emit-exprs ;

\ ---- Timing and statistics.
: now ( -- us ) utime drop ;
: .ms ( us -- ) 500 + 1000 / 0 .r ." ms" ;
: .kv ( n c-addr u -- ) space type ." =" 0 .r ;
: .table ( cons c-addr u -- )
  type cons-table >r r@ htab-count s" entries" .kv r@ htab-slots s" slots" .kv
  r@ htab-stats rot s" finds" .kv swap s" compared" .kv s" grows" .kv
  ."  load%=" r@ htab-count 100 * r> htab-slots / 0 .r cr ;
: .family ( cons c-addr u -- )
  2dup type ." :" 2 pick cons-numbers s" numbers" .kv
  2 pick cons-records slab-used-bytes s" record-bytes" .kv
  2 pick cons-bytes slab-count s" text-bytes" .kv
  2 pick cons-table htab-slots u32s s" table-bytes" .kv cr ." table " .table ;
: compact-stats ( -- )
  compact-tier tier-names s" names" .family compact-tier tier-levels s" levels" .family
  compact-tier tier-tuples s" tuples" .family compact-tier tier-texts s" texts" .family
  compact-tier tier-exprs s" exprs" .family
  ." input tier: bytes used=" compact-tier tier-used 0 .r
  ."  allocated=" compact-tier tier-allocated 0 .r cr
  ." export: names=" compact-loaded name-map slab-count 0 .r
  ."  levels=" compact-loaded level-map slab-count 0 .r
  ."  exprs=" compact-loaded expr-map slab-count 0 .r
  ."  declarations=" compact-loaded decl-map slab-count 0 .r
  ."  blocks=" compact-loaded load-blocks @ 0 .r cr ;

\ ---- Name lookups by text: each declaration's name, component by
\ component, through a scratch tier over the sealed input (no insertion).
: comps ( -- stack ) compact-loaded comp-stack ;
: chain ( n -- ) comps slab-clear begin dup while dup comps map-push drop
  compact-tier name-prefix@ repeat drop ;
: comp-step ( id comp -- id' true | false )
  dup compact-tier name-tag@ tag-name-str =
  if compact-tier name-text@ compact-scratch name-find-str
  else compact-tier name-number@ compact-scratch name-find-num then ;
: comp@ ( k -- comp ) comps slab-count 1- swap - comps map@ ;
: resolve ( n -- n' true | false )
  chain name-anonymous comps slab-count 0 ?do
    i comp@ comp-step 0= if false unloop exit then
  loop true ;
: lookups ( -- found ) 0 compact-loaded decl-map slab-count 0 ?do
    i compact-loaded decl-map map@ dup resolve if = if 1+ then else drop then loop ;
\ Look every declaration's name up by its text; print how many were found
\ as themselves, and the time.
: compact-lookups ( -- )
  compact-tier compact-scratch tier-extend ok? 0= abort" compact-lookups: no scratch tier"
  now lookups now rot - swap
  ." name lookups by text: declarations=" compact-loaded decl-map slab-count 0 .r
  ."  found=" 0 .r space .ms cr compact-scratch tier-free ;

\ ---- Entry words.
\ Load the export named c-addr u and print its dump lines.
: compact-dump ( c-addr u -- )
  16 compact-load dup ok? 0= if ." error: " . cr exit then drop compact-emit compact-free ;
\ Load with tables starting at 2^log2 slots, and report time, sizes,
\ tables and lookups.
: compact-measure ( c-addr u log2 -- )
  now >r compact-load now r> - swap dup ok? 0= if ." error: " . drop cr exit then drop
  ." load and seal: " .ms cr compact-stats compact-lookups compact-free ;
